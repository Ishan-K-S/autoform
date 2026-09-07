#!/usr/bin/env python3
"""Render the language-neutral JSON AST as a Lean 4 `Autoform.Core.Program`.

Deterministic printer. The only judgement it makes is name sanitisation; everything
else is a direct structural mapping, so the output is diffable and reviewable.

Two invariants this file exists to protect:

* **Every expression and statement is fully parenthesised.** A previous version emitted
  `.ret .name "a"`, which Lean parses as `Stmt.ret` applied to three arguments. Anything
  that is not a nullary constructor gets wrapped, always.
* **The printer is a function of the JSON alone.** No dict/set iteration order, no
  timestamps, no paths beyond what the AST records — the same input must give a
  byte-identical file.

Usage: render_lean.py ast.json Out.lean [ModuleName]
"""
import json
import threading, sys, re, os

# Break a term across lines once its flat form would push past this column. Purely
# cosmetic: the layout below is whitespace-insensitive because every term is
# parenthesised or bracketed, so wrapping can never change what Lean parses.
WIDTH = 100
INDENT = 2
# Indentation stops growing past this column. Without a cap, a right-nested `seq` chain
# of n statements indents 2n spaces at its deepest line, so the OUTPUT is O(n^2)
# characters -- 2000 statements produced a 20 MB module, and the cost is in the file, not
# the algorithm. Real code nests: V8 has functions with thousands of statements in a
# single body. Past ~20 levels the staircase has stopped conveying structure anyway, and
# this is generated code that says "do not edit" at the top. Capping makes the output
# linear; it changes only where the continuation lines sit, never the term.
MAX_INDENT = 40

# ---------------------------------------------------------------------------
# Lean literals
# ---------------------------------------------------------------------------

# Lean 4 string escapes are a short list: \\ \" \' \n \t \r \x?? \u????. Anything
# outside it is either passed through as UTF-8 (Lean source is UTF-8) or hex-escaped.
_SIMPLE_ESCAPES = {
    '\\': '\\\\',
    '"':  '\\"',
    '\n': '\\n',
    '\t': '\\t',
    '\r': '\\r',
}

def lean_str(s) -> str:
    """Escape a Python string as a Lean 4 string literal.

    Control characters (including DEL and the C1 block) become `\\x..`/`\\u....`; printable
    non-ASCII is emitted verbatim, since Lean reads UTF-8 source. Lone surrogates cannot
    appear in a Lean string at all, so they are hex-escaped too — which keeps the file
    writable even when the source contained mojibake.
    """
    if not isinstance(s, str):
        s = str(s)
    out = []
    for ch in s:
        if ch in _SIMPLE_ESCAPES:
            out.append(_SIMPLE_ESCAPES[ch])
            continue
        o = ord(ch)
        if o < 0x20 or o == 0x7F:
            out.append('\\x%02x' % o)
        elif 0x80 <= o <= 0x9F or 0xD800 <= o <= 0xDFFF or o in (0xFEFF, 0x2028, 0x2029):
            # C1 controls, surrogates, BOM and line/paragraph separators: invisible or
            # illegal in source, so never emit them raw.
            out.append('\\u%04x' % o)
        else:
            out.append(ch)
    return '"' + ''.join(out) + '"'

def lean_int(i) -> str:
    i = int(i)
    return f"({i})" if i < 0 else str(i)

def lean_float_bits(v) -> int:
    """The IEEE-754 binary64 bit pattern of a decimal float literal.

    `Autoform/Lang/Core/Float.lean` models floats by bit pattern and its docstring names
    exactly this conversion: `struct.unpack('<Q', struct.pack('<d', x))[0]`. Emitting BITS
    rather than decimal text is the point -- `Format.ofDecimal` can round a decimal
    correctly on the way in, but going back out to decimal is not modelled, so bits are the
    only spelling that round-trips through the differential harness.

    Python's float() is correctly rounded, so this is the same value a C or Python compiler
    would produce for the same source text. A literal that does not parse is an error here
    rather than a silent 0.0: 854 lines of verified IEEE-754 are not improved by feeding
    them a guess.
    """
    import struct
    x = float(str(v).rstrip("fFlL"))
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def lean_bool(b) -> str:
    return "true" if b else "false"

# ---------------------------------------------------------------------------
# Structure: each node becomes a head token plus a list of children.
#
# A child is one of:
#   ("atom", text)          already-rendered leaf (string/int/bool literal)
#   ("e", node)             sub-expression
#   ("s", node)             sub-statement
#   ("es", [node, ...])     list of sub-expressions  -> [a, b, c]
#   ("ps", [[k, v], ...])   list of expression pairs -> [(k, v), ...]
# ---------------------------------------------------------------------------

def _field(n, key, kind):
    if key not in n:
        raise ValueError(f"{kind} node {n.get('k')!r} is missing required field {key!r}")
    return n[key]

def expr_shape(n):
    if not isinstance(n, dict):
        raise ValueError(f"expression node is not an object: {n!r}")
    k = n.get("k")
    f = lambda key: _field(n, key, "expr")
    if k == "int":    return ".lit", [("atom", f"(.int {lean_int(f('v'))})")]
    if k == "str":    return ".lit", [("atom", f"(.str {lean_str(f('v'))})")]
    if k == "bool":   return ".lit", [("atom", f"(.bool {lean_bool(f('v'))})")]
    if k == "unit":   return ".lit", [("atom", ".unit")]
    if k == "float":  return ".lit", [("atom", f"(.float (Fl.ofBits {lean_float_bits(f('v'))}))")]
    if k == "name":   return ".name", [("atom", lean_str(f('v')))]
    if k == "binop":  return ".binop", [("atom", lean_str(f('op'))), ("e", f('a')), ("e", f('b'))]
    if k == "unop":   return ".unop", [("atom", lean_str(f('op'))), ("e", f('a'))]
    if k == "index":  return ".index", [("e", f('a')), ("e", f('b'))]
    if k == "call":   return ".call", [("atom", lean_str(f('f'))), ("es", f('args'))]
    if k == "hole":   return ".hole", [("atom", lean_str(f('label')))]
    # `003-box-address-taken-locals`: unconditional, constructor-free box allocation.
    # See `data-model.md` for the on-disk shape and `Expr.boxNew` (`Syntax.lean`) for
    # its semantics.
    if k == "boxNew": return ".boxNew", [("e", f('e'))]
    # `006-reduce-remaining-holes`, Story 5: `boxNew` generalised to N fields. The
    # wire format keeps plain string keys (`data-model.md`'s `[["<key>", <expr>],
    # ...]`); each key is wrapped as an ordinary `{"k":"str",...}` expr node here so
    # the existing `("ps", ...)` pair-list machinery (already used by `dictE`)
    # renders it with no further changes -- `Expr.boxFields`'s own Lean signature is
    # `List (Expr × Expr)` for exactly this reason (reusing `evalPairs`, already
    # proven fuel-monotone, rather than a second list-evaluator).
    if k == "boxFields":
        pairs = [[{"k": "str", "v": key}, val] for key, val in f('fields')]
        return ".boxFields", [("ps", pairs)]
    # `010-reach-90pct-hole-free` US1/US5: a plain, unit-filled numeric-range
    # box (`export_ast.sc`'s own `boxRangeExpr` -- see its doc comment for the
    # full argument and the live experiment that motivated this) -- rendered
    # as a COMPUTED Lean list (`List.range n |>.map ...`) instead of unrolling
    # `n` literal pairs the way `"boxFields"` above does. Evaluates to exactly
    # the same `List (Expr × Expr)` value a literal `[("0", .unit), ("1",
    # .unit), ...]` of length `n` would, so `Expr.boxFields`'s own semantics
    # (`evalPairs`) are completely unaffected -- only the SOURCE TEXT spelling
    # the argument differs, and it differs at CONSTANT size regardless of `n`,
    # avoiding the elaboration-recursion-depth wall a literal list of this
    # shape hits at real buffer sizes (confirmed: `ArrayRepExperiment.lean`).
    if k == "boxFieldsRange":
        n = f('n')
        if not isinstance(n, int) or n < 0:
            raise ValueError(f"boxFieldsRange node has invalid n: {n!r}")
        atom = (f"((List.range {n}).map (fun i => "
                f"(Expr.lit (Lit.str s!\"{{i}}\"), Expr.lit Lit.unit)))")
        return ".boxFields", [("atom", atom)]
    # `010-reach-90pct-hole-free`: `boxFieldsRange` above needs `n` known at EXPORT
    # time (it bakes the literal into the generated source text) -- no help for a
    # `malloc(len)`-shaped C allocation, whose size the exporter can never know
    # until the program runs. `Expr.boxArray` (`Syntax.lean`) takes a LENGTH
    # EXPRESSION instead of a literal count, evaluated once at runtime; this is
    # the ordinary `("e", ...)` single-sub-expression shape every other
    # one-argument constructor here already uses (`boxNew`, `derefIref`, ...), not
    # a new rendering pattern.
    if k == "boxArray": return ".boxArray", [("e", f('n'))]
    if k == "irefIndex": return ".irefIndex", [("e", f('a')), ("e", f('i'))]
    if k == "irefField": return ".irefField", [("e", f('a')), ("atom", lean_str(f('f')))]
    if k == "derefIref": return ".derefIref", [("e", f('p'))]
    # `009-reduce-remaining-holes-4`: `*p`/`p[i]` on a `char*` byte-cursor -- read
    # the byte at offset `b` of the base string `a`. See `Syntax.lean`'s own
    # `Expr.strByte` doc comment for why this is a separate constructor from
    # `.index` rather than a new case on it.
    if k == "strByte": return ".strByte", [("e", f('a')), ("e", f('b'))]
    # `009-reduce-remaining-holes-4`: the substring of `a` from offset `b`
    # onward -- a byte cursor (`strByte`, above) handed WHOLE to another
    # function partway through being walked. See `Syntax.lean`'s own
    # `Expr.strFrom` doc comment. Missed on the first pass (found live: a real
    # Colab run of the full, unbounded corpus hit `unknown expr node kind
    # 'strFrom'` on `jim_strstr`, autosetup/jimsh0.c, the first real-corpus
    # function to actually reach this shape) -- `strByte` alone was added here
    # and verified via local fixtures, but `strFrom` was verified only via
    # `lake env lean` fixtures and the exporter's own JSON output, never
    # actually run through this renderer until a real corpus function used it.
    if k == "strFrom": return ".strFrom", [("e", f('a')), ("e", f('b'))]
    # --- objects, containers, control ---
    if k == "field":  return ".field", [("e", f('a')), ("atom", lean_str(f('f')))]
    if k == "mcall":  return ".mcall", [("e", f('recv')), ("atom", lean_str(f('m'))), ("es", f('args'))]
    if k == "alloc":  return ".alloc", [("atom", lean_str(f('cls'))), ("es", f('args'))]
    if k == "fnref":  return ".fnref", [("atom", lean_str(f('v')))]
    # A function value that reads variables of an enclosing function. `fnref` is the
    # cheaper form and is used wherever the exporter proved there is nothing to capture.
    if k == "closure": return ".closure", [("atom", lean_str(f('f')))]
    # A *class* that captures its defining scope: instances carry the captured frame, so
    # their methods can read the enclosing function's variables. `closure` names a
    # function and cannot stand in for this.
    if k == "classClosure": return ".classClosure", [("atom", lean_str(f('c')))]
    if k == "listE":  return ".listE", [("es", f('items'))]
    if k == "tupleE": return ".tupleE", [("es", f('items'))]
    if k == "dictE":  return ".dictE", [("ps", f('pairs'))]
    if k == "cond":   return ".cond", [("e", f('c')), ("e", f('t')), ("e", f('e'))]
    if k == "isOp":   return ".isOp", [("atom", lean_bool(f('neg'))), ("e", f('a')), ("e", f('b'))]
    if k == "inOp":   return ".inOp", [("atom", lean_bool(f('neg'))), ("e", f('a')), ("e", f('b'))]
    # --- the calling convention: `f(*xs, k=v, **d)` ---
    # Only meaningful directly inside a call's argument list; `Semantics.evalList` is the
    # only consumer, and anywhere else the interpreter holes rather than inventing a value.
    if k == "starred":  return ".starred", [("e", f('a'))]
    if k == "kwargE":   return ".kwargE", [("atom", lean_str(f('n'))), ("e", f('a'))]
    if k == "dstarred": return ".dstarred", [("e", f('a'))]
    raise ValueError(f"unknown expr node kind {k!r} (node: {json.dumps(n)[:200]})")

def stmt_shape(n):
    if not isinstance(n, dict):
        raise ValueError(f"statement node is not an object: {n!r}")
    k = n.get("k")
    f = lambda key: _field(n, key, "stmt")
    if k == "skip":     return ".skip", []
    if k == "brk":      return ".brk", []
    if k == "cont":     return ".cont", []
    if k == "holeS":    return ".hole", [("atom", lean_str(f('label')))]
    if k == "exprS":    return ".expr", [("e", f('e'))]
    if k == "assign":   return ".assign", [("atom", lean_str(f('x'))), ("e", f('e'))]
    if k == "ret":      return ".ret", [("e", f('e'))]
    if k == "seq":      return ".seq", [("s", f('a')), ("s", f('b'))]
    if k == "ifte":     return ".ifte", [("e", f('c')), ("s", f('t')), ("s", f('e'))]
    if k == "loop":     return ".loop", [("e", f('c')), ("s", f('body'))]
    # `007-reduce-remaining-holes-2` US4: absorbs a `break` from `body` without also
    # absorbing a `continue` (unlike `.loop`, which catches both) -- `switch` lowers to
    # this wrapping its `ifte`-chain dispatch, so `break` inside a case ends only the
    # switch, never an enclosing loop.
    if k == "breakBlock": return ".breakBlock", [("s", f('body'))]
    # --- objects, iteration, exceptions ---
    if k == "setField": return ".setField", [("e", f('r')), ("atom", lean_str(f('f'))), ("e", f('v'))]
    if k == "setIndex": return ".setIndex", [("e", f('r')), ("e", f('i')), ("e", f('v'))]
    if k == "setDerefIref": return ".setDerefIref", [("e", f('p')), ("e", f('v'))]
    if k == "forIn":    return ".forIn", [("atom", lean_str(f('x'))), ("e", f('e')), ("s", f('body'))]
    if k == "tryCatch": return ".tryCatch", [("s", f('body')), ("atom", lean_str(f('x'))), ("s", f('handler'))]
    # `try: body finally: fin`. Distinct from `tryCatch` because it intercepts *every* way
    # control leaves the body — return/break/continue as well as exceptions — and then
    # re-raises that outcome unless the finalizer itself leaves abnormally.
    if k == "tryFinally": return ".tryFinally", [("s", f('body')), ("s", f('fin'))]
    if k == "raise":    return ".raise", [("e", f('e'))]
    if k == "del":      return ".del", [("atom", lean_str(f('x')))]
    # --- module-level scope ---
    if k == "setGlobal":  return ".setGlobal", [("atom", lean_str(f('x'))), ("e", f('e'))]
    if k == "declGlobal": return ".declGlobal", [("atom", lean_str(f('x')))]
    raise ValueError(f"unknown stmt node kind {k!r} (node: {json.dumps(n)[:200]})")

SHAPE = {"e": expr_shape, "s": stmt_shape}

# ---------------------------------------------------------------------------
# Printing
# ---------------------------------------------------------------------------

def flat(node, kind) -> str:
    """Single-line rendering. Always fully parenthesised (except nullary constructors)."""
    head, children = SHAPE[kind](node)
    if not children:
        return head
    return "(" + head + " " + " ".join(flat_child(c) for c in children) + ")"

class _RawNewline(Exception):
    """An atom contained a literal newline — fall back to the uncapped path.

    `render` returns the flat form unconditionally when it contains a newline, so the
    capped variant must not silently disagree. JSON escapes newlines, so this should be
    unreachable; it exists so that "should be" is not load-bearing."""


def flat_capped(node, kind, cap):
    """`flat(node, kind)` if it is at most `cap` characters, else `None`.

    Why this exists: `render` computed `flat()` over the WHOLE subtree at every level
    just to ask whether it fit in `WIDTH` columns, then threw the string away when it did
    not. On a chain of n nested statements that is O(n^2) characters built and discarded,
    and measured it was worse than that -- 250 statements rendered in 0.33 s, 2000 in
    42 s, and 5000 did not finish. V8 has functions far deeper than 2000.

    Since a flat form is only ever *used* when it fits in `WIDTH` (100) columns, anything
    longer need never be constructed. This short-circuits as soon as the budget is blown,
    so each node costs O(cap) instead of O(subtree), and the whole render is linear.
    """
    if cap < 0:
        return None
    head, children = SHAPE[kind](node)
    if not children:
        return head if len(head) <= cap else None
    # "(" + head + " " + ... + ")"
    budget = cap - (len(head) + 3)
    if budget < 0:
        return None
    parts = []
    for c in children:
        piece = flat_child_capped(c, budget)
        if piece is None:
            return None
        budget -= len(piece) + 1          # the separating space
        if budget < -1:
            return None
        parts.append(piece)
    out = "(" + head + " " + " ".join(parts) + ")"
    return out if len(out) <= cap else None


def flat_child_capped(c, cap):
    tag, val = c
    if tag == "atom":
        if "\n" in val:
            raise _RawNewline
        return val if len(val) <= cap else None
    if tag in ("e", "s"):
        return flat_capped(val, tag, cap)
    if tag in ("es", "ps"):
        items = _seq(val)
        budget = cap - 2                  # the brackets
        if budget < 0:
            return None
        parts = []
        for x in items:
            piece = (flat_capped(x, "e", budget) if tag == "es"
                     else _flat_pair_capped(x, budget))
            if piece is None:
                return None
            budget -= len(piece) + 2      # ", "
            if budget < -2:
                return None
            parts.append(piece)
        out = "[" + ", ".join(parts) + "]"
        return out if len(out) <= cap else None
    raise AssertionError(tag)


def _flat_pair_capped(p, cap):
    if not (isinstance(p, list) and len(p) == 2):
        raise ValueError(f"dictE pair must be a 2-element array, got {p!r}")
    a = flat_capped(p[0], "e", cap - 4)
    if a is None:
        return None
    b = flat_capped(p[1], "e", cap - 4 - len(a))
    if b is None:
        return None
    out = "(" + a + ", " + b + ")"
    return out if len(out) <= cap else None


def flat_child(c) -> str:
    tag, val = c
    if tag == "atom":
        return val
    if tag in ("e", "s"):
        return flat(val, tag)
    if tag == "es":
        return "[" + ", ".join(flat(x, "e") for x in _seq(val)) + "]"
    if tag == "ps":
        return "[" + ", ".join(_flat_pair(p) for p in _seq(val)) + "]"
    raise AssertionError(tag)

def _seq(val):
    if val is None:
        return []
    if not isinstance(val, list):
        raise ValueError(f"expected a JSON array, got {val!r}")
    return val

def _flat_pair(p):
    if not (isinstance(p, list) and len(p) == 2):
        raise ValueError(f"dictE pair must be a 2-element array, got {p!r}")
    return "(" + flat(p[0], "e") + ", " + flat(p[1], "e") + ")"

def _render_seq_chain(node, col) -> str:
    """Render a `Stmt.seq` whose flat form already failed to fit at `col`, without one
    Python stack frame per statement.

    `.seq(a, b)` is right-associated, so a function with N consecutive top-level
    statements is a chain N deep. The fully-recursive walk (`render` -> `render_child` ->
    `render` for `b`, all the way down) turns that into N nested Python calls, which is
    exactly the wall `docs/scale.md` measured at 247 statements (independent of total
    repo size — `sqlparse` at 8.8k lines failed, `requests` at 12k lines did not, because
    the trigger is one file's statement count). Raising `sys.setrecursionlimit` and the
    thread stack size (`main`, below) moved that cliff without removing it; this removes
    it, by walking the spine with an explicit `while` loop instead of the call stack.

    Reproduces `render()`'s output byte-for-byte: at every link in the spine, the same
    flat-then-structural decision `render()` itself makes is made here too, so a
    sub-chain short enough to fit on one line still renders flat, exactly as it would
    have under full recursion. Real nesting (if/loop bodies) is not the measured problem
    and is not touched — each individual statement in the chain still renders through the
    ordinary recursive `render`, only as deep as that one statement's own structure.
    """
    heads = []              # (statement node, its column), outermost first
    cur, cur_col = node, col
    while True:
        if not (isinstance(cur, dict) and cur.get("k") == "seq"):
            tail_text = render(cur, "s", cur_col)
            break
        try:
            one = flat_capped(cur, "s", WIDTH - cur_col)
            if one is not None:
                tail_text = one
                break
        except _RawNewline:
            one = flat(cur, "s")
            if cur_col + len(one) <= WIDTH or "\n" in one:
                tail_text = one
                break
        inner = min(cur_col + INDENT, MAX_INDENT)
        heads.append((cur["a"], inner))
        cur_col = inner
        cur = cur["b"]
    acc = tail_text
    for head_node, head_col in reversed(heads):
        pad = " " * head_col
        head_text = render(head_node, "s", head_col)
        acc = "(.seq\n" + pad + head_text + "\n" + pad + acc + ")"
    return acc

def render(node, kind, col) -> str:
    """Render `node` starting at column `col`, wrapping if the flat form is too wide.

    The returned string's first line is *not* indented (the caller has already placed the
    cursor at `col`); continuation lines carry their own indentation.
    """
    try:
        one = flat_capped(node, kind, WIDTH - col)
        if one is not None:
            return one
    except _RawNewline:
        one = flat(node, kind)
        if col + len(one) <= WIDTH or "\n" in one:
            return one
    if kind == "s" and isinstance(node, dict) and node.get("k") == "seq":
        return _render_seq_chain(node, col)
    head, children = SHAPE[kind](node)
    if not children:
        # A nullary constructor's flat form IS its head. The capped flatten returns None
        # when the head alone overruns the column budget, and returning that None here
        # was a real regression: it propagated into a string join several frames up and
        # surfaced as a TypeError, not as a wrong render. Caught by check_render.
        return head
    inner = min(col + INDENT, MAX_INDENT)
    pad = " " * inner
    parts = [render_child(c, inner) for c in children]
    return "(" + head + "\n" + "\n".join(pad + p for p in parts) + ")"

def render_child(c, col) -> str:
    tag, val = c
    if tag == "atom":
        return val
    if tag in ("e", "s"):
        return render(val, tag, col)
    if tag in ("es", "ps"):
        items = _seq(val)
        if not items:
            return "[]"
        one = flat_child(c)
        if col + len(one) <= WIDTH:
            return one
        # Leading-comma layout: every element starts at the same column, so the block
        # stays readable and each line is independently diffable.
        pad = " " * col
        deeper = min(col + INDENT, MAX_INDENT)
        rendered = ([render(x, "e", deeper) for x in items] if tag == "es"
                    else [render_pair(p, deeper) for p in items])
        body = ("\n" + pad + ", ").join(rendered)
        return "[ " + body + " ]"
    raise AssertionError(tag)

def render_pair(p, col) -> str:
    one = _flat_pair(p)
    if col + len(one) <= WIDTH:
        return one
    inner = min(col + INDENT, MAX_INDENT)
    return ("(" + render(p[0], "e", inner) + ",\n" + " " * inner
            + render(p[1], "e", inner) + ")")

# Kept as the public entry points other tooling may import.
def expr(n) -> str:
    return flat(n, "e")

def stmt(n) -> str:
    return flat(n, "s")

# ---------------------------------------------------------------------------

def ident(name: str) -> str:
    s = re.sub(r'[^A-Za-z0-9_]', '_', name)
    return ("f_" + s)[:120]

# Integer division/modulo convention by source language. Getting this wrong is silent
# mistranslation, so it is recorded per program rather than assumed.
# `.cc`/`.cxx`/`.hh`/`.hpp` are C++ exactly as `.cpp` is. Their absence was not
# hypothetical: V8's `src/base` is 104 `.cc` files against 53 `.h`, so its dialect was
# being decided by the *headers* alone, and a corpus of `.cc` files with no header
# aborted the render outright. Found by tests/test_render_lean.py, which recorded it as
# a strict xfail before it had a fix.
#
# `.js`/`.ts`/`.tsx`/`.jsx`/`.mjs`/`.cjs` map to `.javascript`, not `.cLike`. Mapping them
# to `.cLike` was itself a measured, confirmed wrong answer (docs/languages.md): `&&`/`||`
# returned a coerced boolean instead of an operand, and arithmetic wrapped at 32 bits
# instead of matching Node's IEEE-double `Number` (`2147483647 + 1` gave `-2147483648`
# instead of Node's `2147483648`). `Autoform.Core.Dialect.javascript`
# (`Autoform/Lang/Core/Syntax.lean`) is the real fix; this table just has to point at it.
DIALECT = {".py": ".python", ".c": ".cLike", ".h": ".cLike", ".cpp": ".cLike",
           ".cc": ".cLike", ".cxx": ".cLike", ".hh": ".cLike", ".hpp": ".cLike",
           ".java": ".cLike", ".kt": ".cLike", ".go": ".cLike",
           ".js": ".javascript", ".ts": ".javascript", ".tsx": ".javascript",
           ".jsx": ".javascript", ".mjs": ".javascript", ".cjs": ".javascript"}

def infer_dialect(funcs) -> str:
    """Pick the arithmetic/string dialect from file extensions.

    Refuses rather than defaulting. Defaulting to `.python` when no extension
    voted meant a `.tsx` file was translated with Python's floored division and
    modulo: measured, `-7 % 3` gave 2 where TypeScript gives -1, and `-7/2` gave
    -4 where TypeScript gives -3.5. That is the original modulo bug re-entering
    through the extension table, which is exactly the class of silent
    mistranslation the dialect parameter exists to prevent — so an unrecognized
    extension is an error, not an assumption.
    """
    exts = [os.path.splitext(f.get("file", ""))[1] for f in funcs]
    votes = [DIALECT[e] for e in exts if e in DIALECT]
    if not votes:
        seen = sorted({e for e in exts if e})
        raise SystemExit(
            "render_lean: cannot infer dialect — no known extension among %s.\n"
            "  Known: %s\n"
            "  Add the extension to DIALECT (with its real integer-division and\n"
            "  string semantics) rather than letting it default." % (seen or "[]",
                                                                    sorted(DIALECT)))
    return max(set(votes), key=votes.count)

def render_func(f, nm) -> list:
    params = ", ".join(lean_str(p) for p in f.get("params", []))
    body = render(f["body"], "s", 10)  # "  , body := " is 12 wide; 10 keeps a margin
    # `vararg`/`kwarg` are emitted only when the AST records them, so a corpus with no
    # variadic parameters renders byte-identically to the way it did before the calling
    # convention existed. Both fields default to `none` in `Core.Func`.
    variadic = []
    if f.get("vararg") is not None:
        variadic.append(f"  , vararg := some {lean_str(f['vararg'])}")
    if f.get("kwarg") is not None:
        variadic.append(f"  , kwarg := some {lean_str(f['kwarg'])}")
    return [
        f"/-- `{f['name']}`  (from `{f.get('file','?')}`) -/",
        f"def {nm} : Func :=",
        f"  {{ name := {lean_str(f['name'])}",
        f"  , params := [{params}]",
        *variadic,
        f"  , body := {body} }}",
        "",
    ]

def _run_main():
    src, dst = sys.argv[1], sys.argv[2]
    module = sys.argv[3] if len(sys.argv) > 3 else "Translated"
    with open(src) as fh:
        funcs = json.load(fh)
    dialect = infer_dialect(funcs)

    out = [
        "import Autoform.Lang.Core.Semantics",
        "",
        "-- Lean's default `maxRecDepth` (512) is a guard against runaway elaboration, not",
        "-- a statement about reasonable programs. A deep-embedded function body is one",
        "-- term, so the elaborator's recursion depth tracks the *source's* nesting depth:",
        "-- Linux `lib/` hit the limit at two declarations and the whole module failed to",
        "-- type-check. Raising it costs nothing for shallow modules and is the difference",
        "-- between compiling a real codebase and not.",
        "--",
        "-- 8000 was not enough either. The binding constraint is not the nesting depth of",
        "-- any one body (Ansible's deepest is 297) but the `funcs := [...]` list literal,",
        "-- which elaborates as nested cons cells -- one frame or more per function, and",
        "-- Ansible has 5,546. So the limit has to scale with the module's function count,",
        "-- not with how deep its code happens to be.",
        f"set_option maxRecDepth {max(8000, 8 * len(funcs) + 8000)}",
        "",
        "-- Lean's default `maxHeartbeats` (200000) budgets ONE declaration's own",
        "-- elaboration cost, separately from `maxRecDepth` above (which bounds nesting",
        "-- depth, not total work). A single source file whose top-level declarations",
        "-- carry a large static table -- SQLite's `test_vdbecov.c`, whose `<global>`",
        "-- initializer alone is ~5.3M characters of generated Lean -- blows through the",
        "-- default budget on that ONE declaration and fails with a `(deterministic)",
        "-- timeout at isDefEq` error, unrelated to whether the translation is correct.",
        "-- Unlike `maxRecDepth`, this does not scale with function COUNT (Ansible-style",
        "-- corpora with thousands of small functions never hit it); it is one",
        "-- pathologically large declaration, which no per-function-count formula would",
        "-- predict, so this disables the budget outright rather than guessing a bigger",
        "-- number that the next large static table would just exceed again. Scoped to",
        "-- THIS generated file only (`set_option` here does not touch hand-written proof",
        "-- files elsewhere in the project, which keep the default as a real safety net",
        "-- against a genuine runaway elaboration bug while someone is editing them).",
        "set_option maxHeartbeats 0",
        "",
        "/-!",
        f"# {module} — machine-generated",
        "",
        "Emitted by `cartographer/render_lean.py` from a Joern code property graph.",
        "Do not edit: regenerate. Every `Stmt.hole` / `Expr.hole` marks a construct the",
        "transpiler did not translate, tagged with the CPG node label responsible.",
        "-/",
        "",
        # Each corpus gets its OWN namespace, `Autoform.Generated.<Module>`, so that
        # `program` becomes `Autoform.Generated.<Module>.program` and two rendered
        # corpora can live in one import graph. When every module declared
        # `namespace Autoform.Generated`, importing a second one failed outright with
        # "environment already contains 'Autoform.Generated.program'", which is why the
        # proof modules for cachetools and for V8 could never share a build -- and hence
        # why they sat outside the root import graph, unchecked by `leanchecker --fresh`.
        f"namespace Autoform.Generated.{module}",
        "open Autoform.Core",
        "",
    ]
    names = []
    seen = set()
    for f in funcs:
        nm = ident(f["name"])
        while nm in seen:
            nm += "'"
        seen.add(nm)
        names.append(nm)
        try:
            out.extend(render_func(f, nm))
        except ValueError as e:
            raise SystemExit(f"render_lean: in function {f.get('name')!r} "
                             f"(from {f.get('file','?')}): {e}")

    # Module-level bindings are exported as zero-argument *initializer* functions, one
    # per source file, whose bodies are runs of `Stmt.setGlobal`. Running them is what
    # makes module-level constants, classes and `def`s resolvable, so the entry points
    # that need them have to know which functions they are.
    inits = [n for f, n in zip(funcs, names)
             if f["name"].endswith(":<module>") or f["name"].endswith(":<global>")]
    out.append("/-- Module-level initializers: run these to populate the globals frame")
    out.append("before calling any entry point. -/")
    out.append("def moduleInits : List Func := [" + ", ".join(inits) + "]")
    out.append("")
    # Classes whose single base is a builtin type (`class X(tuple)`), as recorded by
    # `cartographer/export_ast.sc` on the module initializer of the file that declares
    # them. Collected across all entries, deduplicated, and *dropped* on conflict: two
    # same-named classes with different bases cannot be told apart by `Expr.alloc`, which
    # carries only the short name, so the honest answer is to record neither and leave
    # both as opaque references -- exactly the pre-existing behaviour.
    bases = {}
    conflicts = set()
    for f in funcs:
        for cls, base in sorted((f.get("classBases") or {}).items()):
            if cls in bases and bases[cls] != base:
                conflicts.add(cls)
            bases[cls] = base
    for c in conflicts:
        bases.pop(c, None)
    base_ctor = {"tuple": ".tuple", "list": ".list", "dict": ".dict", "str": ".str"}
    unknown = sorted(set(b for b in bases.values() if b not in base_ctor))
    if unknown:
        raise SystemExit("render_lean: unmodelled builtin base(s) {}; "
                         "Core.BuiltinBase has no constructor for them".format(unknown))
    bb = ", ".join("({}, {})".format(lean_str(c), base_ctor[bases[c]])
                   for c in sorted(bases))

    if bb:
        out.append(f"/-- Source dialect: `{dialect}` (integer division/modulo convention).")
        out.append("")
        out.append("`builtinBases` lists the classes whose base is a builtin type, so that")
        out.append("`Expr.alloc` builds a `Val.bobj` and not an opaque `Val.ref`. -/")
        out.append("def program : Program := { dialect := " + dialect
                   + ", builtinBases := [" + bb + "], funcs := [")
    else:
        out.append(f"/-- Source dialect: `{dialect}` (integer division/modulo convention). -/")
        out.append("def program : Program := { dialect := " + dialect + ", funcs := [")
    out.append(",\n".join("  " + n for n in names))
    out.append("] }")
    out.append("")
    out.append(f"end Autoform.Generated.{module}")
    with open(dst, "w") as fh:
        fh.write("\n".join(out))
    print(f"rendered {len(funcs)} functions -> {dst}")

def main():
    """Render on a thread with a large stack.

    The emitters are mutually recursive over the AST, so depth is the source's nesting
    depth, not a constant. Python's default limit is 1000 frames and this file never
    raised it -- `scripts/lang_matrix.py` set it to 100000 before calling in, but
    `autoform.sh` invokes this script directly, so the default applied to every real run.
    It failed at 247 consecutive top-level statements.

    Raising `setrecursionlimit` alone is not enough and is actively dangerous: the limit
    is a guard against overrunning the *C* stack, and lifting it without a bigger stack
    turns a clean RecursionError into a segfault. A thread with an explicit stack size is
    the portable way to get both.
    """
    sys.setrecursionlimit(300_000)
    try:
        threading.stack_size(512 * 1024 * 1024)
    except (ValueError, RuntimeError):
        try:
            threading.stack_size(64 * 1024 * 1024)   # some platforms cap this
        except (ValueError, RuntimeError):
            pass
    box = {}

    def go():
        try:
            _run_main()
        except BaseException as e:        # noqa: BLE001 - re-raised on the main thread
            box["e"] = e

    t = threading.Thread(target=go)
    t.start()
    t.join()
    if "e" in box:
        raise box["e"]


if __name__ == "__main__":
    main()
