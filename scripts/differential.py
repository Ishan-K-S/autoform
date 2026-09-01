#!/usr/bin/env python3
"""Differential harness: Lean semantics vs. the real runtime.

This is the conformance oracle from STRATEGY.md §2/§5. It is not optional
infrastructure: a proof about a semantics that does not match the real runtime is
theater. Here we test the *transpiler + semantics* jointly, which is exactly the
composite the ledger claims.

Two sources of test cases, in value order:

1. **The repository's own test suite** (STRATEGY.md §3: "every repo ships its own
   conformance suite"). We run the project's pytest/unittest suite under a
   `sys.settrace` hook that records `(function, receiver, args, outcome)` for every call
   that lands in a function we translated, then replay exactly those tuples against the
   Lean `Autoform.Core` interpreter. This gives *realistic* arguments — including
   strings, lists, dicts and live objects — and reaches code random ints never can.
2. **Random integers** for module-level functions, as a fallback / supplement.

Class methods are testable because the recorded receiver is snapshotted into a Lean
`Heap` literal and passed as `self`; the generated scratch file calls `applyFunc`
directly rather than `runFunc`, which always starts from an empty heap.

Outcomes are three-valued, never two: agreement, divergence, and INCONCLUSIVE
(`hole`, `outOfFuel`, or a value the harness cannot faithfully encode). A case that was
not actually compared is never reported as passing — that is the cardinal sin here.

Usage: differential.py <ast.json> <source-dir> <lean-module> [n-cases] [--tests DIR]
"""
import os, sys
import json, subprocess, random, importlib.util, re, glob, io
import contextlib, inspect, functools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import wasm_backend

random.seed(20260819)   # deterministic: workflows/proofs must be reproducible


def _corpus_commit(src_root):
    """The corpus checkout's commit, or why it could not be determined. Never raises:
    provenance that fails the run is worse than provenance that reports its own absence."""
    import subprocess
    try:
        out = subprocess.run(["git", "-C", src_root, "rev-parse", "HEAD"],
                             capture_output=True, text=True, timeout=10)
        if out.returncode == 0:
            return out.stdout.strip()
        return "not-a-git-checkout"
    except Exception as e:                                          # noqa: BLE001
        return "unavailable: %s" % type(e).__name__

# Every scratch artefact lives under one private directory. A fixed `/tmp` path is a
# phantom-result generator: several agents run this harness at once, and a shared
# `/tmp/autoform_diff.lean` means one run can report conformance computed from another
# run's program. Nothing here may be a constant path.
import atexit as _atexit
import tempfile as _tempfile
WORK = _tempfile.mkdtemp(prefix="autoform_diff_%d_" % os.getpid())
_atexit.register(lambda: __import__("shutil").rmtree(WORK, ignore_errors=True))

# Test-suite-derived cases must be reproducible too. Set-iteration and dict-key hashing
# feed which calls the suite makes and in which order, so an unseeded interpreter gives
# a different sample of cases (and a different set of divergences) on every run.
if os.environ.get("PYTHONHASHSEED") != "0" and not os.environ.get("AUTOFORM_NO_REEXEC"):
    os.execve(sys.executable, [sys.executable] + sys.argv,
              dict(os.environ, PYTHONHASHSEED="0"))

FUEL = 5000
MAX_TOTAL_CASES = 600      # keep the generated Lean file compile-bounded
MAX_DEPTH = 8              # value-encoding depth limit
MAX_ELEMS = 512            # value-encoding breadth limit (a resource
                           # bound, not a fidelity one: containers are
                           # encoded whole or refused, never truncated)


# --------------------------------------------------------------------------- AST

def has_hole(n):
    """Tolerant of unknown node kinds: we only look for the hole markers.

    Iterative on purpose. The recursive version blew Python's 1000-frame default on
    Linux `lib/` and raised RecursionError *before any backend ran*, so the largest C
    corpus could not be measured at all — and the failure looked like "the harness broke"
    rather than "this function is deeply nested". Raising the recursion limit is not the
    fix: the limit guards the C stack, and lifting it without a bigger stack turns a clean
    exception into a segfault. An explicit stack has no such ceiling.

    This is the same defect `cartographer/render_lean.py` had (it never set a limit at all
    and died at 247 consecutive statements). Any AST walker here should be assumed to meet
    a 20,000-deep term eventually, because real code nests.
    """
    stack = [n]
    while stack:
        x = stack.pop()
        if isinstance(x, dict):
            if x.get("k") in ("hole", "holeS"):
                return True
            stack.extend(x.values())
        elif isinstance(x, list):
            stack.extend(x)
    return False


PY_NAME = re.compile(r'(?P<file>.+?):<module>\.(?P<qual>.+)')


def classify(f):
    """(relfile, qualname, is_method) for a Python AST entry, or None."""
    m = PY_NAME.fullmatch(f["name"])
    if not m: return None
    qual = m.group("qual")
    if "<" in qual: return None          # <lambda>N, <redefined>N: no stable call site
    return m.group("file"), qual, ("." in qual)


# ------------------------------------------------------------------ value encoding
#
# Python value -> Lean `Val`, allocating plain objects into a `Heap` (a list of `Obj`).
# Returns None when the value has no faithful Core representation; the caller then
# skips the case rather than comparing something it made up.

class Unencodable(Exception):
    pass


class Encoder:
    """Python value -> Core `Val`, with one encoding per value in *every* position.

    Invariants, all of them load-bearing for the oracle's honesty:

    * A given Python object encodes to the same `Val.ref` whether it appears as the
      receiver, inside a receiver's field, as an argument, or in the result — the memo
      is keyed on `id` and shared across the whole case.
    * `tuple`/`list`/`dict` *subclasses* (e.g. cachetools' `_HashedTuple`) encode
      structurally, by value, in every position — never sometimes-value/sometimes-ref.
    * Nothing is dropped. If any value, however deeply nested inside a receiver, has
      no faithful Core representation, the encoder raises and the *whole case* is
      abandoned. A partially-encoded receiver reads back as `unit` in Core and would
      surface as a confident divergence the harness itself manufactured.
    """

    def __init__(self):
        self.heap = []          # list of (cls, [(field, Val)])
        self.byid = {}          # id(obj) -> ref index
        self.objs = {}          # ref index -> the live object (keeps ids alive)
        self.pin = set()        # ids present before the result was encoded

    def enc(self, v, depth=0, in_key=False):
        if depth > MAX_DEPTH: raise Unencodable("depth")
        if v is None: return ("unit",)
        if isinstance(v, bool): return ("bool", v)
        if isinstance(v, int): return ("int", v)
        if isinstance(v, str): return ("str", v)
        if isinstance(v, (list, tuple)):
            # Subclasses (`_HashedTuple`, `OrderedDict`) encode structurally: that is
            # faithful for every operation Core can perform on data it was *handed*
            # (index, len, membership, iteration order). Where Core instead *allocates*
            # such a value itself it produces a `Val.ref`, and that shape disagreement
            # is ruled INCONCLUSIVE at comparison time rather than refused here — see
            # `compare_outcome`.
            if len(v) > MAX_ELEMS: raise Unencodable("wide")
            k = "tuple" if isinstance(v, tuple) else "list"
            return (k, [self.enc(x, depth + 1, in_key) for x in v])
        if isinstance(v, dict):
            if len(v) > MAX_ELEMS: raise Unencodable("wide")
            # Keys are the subtle case: CPython looks them up by `__hash__`/`__eq__`,
            # which user classes override (cachetools' own tests define a
            # `RecursiveEquals` whose *distinct* instances compare equal), while Core
            # compares `Val`s structurally with `.ref` identity. Any object inside a
            # key therefore makes the lookup unfaithful in either direction, so the
            # case is refused rather than compared.
            return ("dict", [(self.enc(k, depth + 1, True),
                              self.enc(x, depth + 1, in_key)) for k, x in v.items()])
        if isinstance(v, type) or inspect.isroutine(v) or isinstance(v, (
                staticmethod, classmethod, property, functools.partial)):
            # `METHOD_REF`/`TYPE_REF` values: Core models them by name only.
            n = getattr(v, "__qualname__", None) or getattr(v, "__name__", None)
            if n: return ("fn", n)
            raise Unencodable("callable")
        # a callable *instance* is still an object with fields — encode it as one
        if isinstance(v, (float, complex, bytes, frozenset, set)):
            raise Unencodable(type(v).__name__)
        if in_key:
            raise Unencodable("object-as-dict-key")
        return ("ref", self.alloc(v, depth))

    def alloc(self, obj, depth):
        """Snapshot a plain Python object into the heap. Cycles resolve to the same
        ref, which is exactly the identity semantics `Val.ref` has."""
        if id(obj) in self.byid: return self.byid[id(obj)]
        if isinstance(obj, type) or inspect.isroutine(obj):
            raise Unencodable("callable")
        fields = {}
        if hasattr(obj, "__dict__"):
            fields.update(vars(obj))
        for cls in type(obj).__mro__:
            for s in getattr(cls, "__slots__", ()) or ():
                if hasattr(obj, s): fields[s] = getattr(obj, s)
        slotted = any(getattr(c, "__slots__", None) is not None
                      for c in type(obj).__mro__)
        if not fields and not hasattr(obj, "__dict__") and not slotted:
            raise Unencodable("opaque")     # C-level object with no inspectable state
        if len(fields) > MAX_ELEMS: raise Unencodable("wide-object")
        idx = len(self.heap)
        self.heap.append(None)                  # reserve the slot before recursing
        self.byid[id(obj)] = idx
        self.objs[idx] = obj
        out = [(str(k), self.enc(val, depth + 1)) for k, val in fields.items()]
        self.heap[idx] = (type(obj).__name__, out)
        return idx

    def freeze(self):
        """Mark the objects that existed before the call returned."""
        self.pin = set(self.byid)

    def enc_result(self, v):
        """Encode a returned value in the *same* namespace as the arguments.

        An object the callee freshly allocated has no counterpart in the heap Core was
        given, so its `Val.ref` would be a number with no shared meaning — refuse it
        instead of comparing addresses across two different allocators."""
        r = self.enc(v)
        if any(i not in self.pin for i in self.byid):
            raise Unencodable("result-allocates-fresh-object")
        return r


def lean_val(v):
    t = v[0]
    if t == "unit": return "Val.unit"
    if t == "bool": return "Val.bool " + ("true" if v[1] else "false")
    if t == "int":  return "Val.int (%d)" % v[1]
    if t == "str":  return "Val.str " + json.dumps(v[1])
    if t == "ref":  return "Val.ref (base + %d)" % v[1]
    if t == "fn":   return "Val.fn " + json.dumps(v[1])
    if t in ("list", "tuple"):
        return "Val.%s [%s]" % (t, ", ".join(lean_val(x) for x in v[1]))
    if t == "dict":
        return "Val.dict [%s]" % ", ".join("(%s, %s)" % (lean_val(a), lean_val(b))
                                           for a, b in v[1])
    raise Unencodable(t)


def lean_heap(heap):
    # named fields, not `⟨…⟩`: `Obj` has grown a field before (`captured`) and
    # anonymous-constructor literals fail the whole run when it happens again
    return "[%s]" % ", ".join(
        "{ cls := %s, fields := [%s] }"
        % (json.dumps(cls), ", ".join("(%s, %s)" % (json.dumps(k), lean_val(val))
                                      for k, val in fields))
        for cls, fields in heap)


# ------------------------------------------------------------------- repr parsing
#
# We cannot edit the Lean sources, so we parse Lean's derived `Repr` output. It is
# emitted on one line (`Format.pretty` at a huge width) and fully parenthesised.

TOKEN = re.compile(r'\s*("(?:[^"\\]|\\.)*"|[A-Za-z_][A-Za-z0-9_.!?]*|-?\d+|[()\[\],])')


def tokenize(s):
    out, i = [], 0
    while i < len(s):
        m = TOKEN.match(s, i)
        if not m: break
        out.append(m.group(1)); i = m.end()
    return out


class P:
    def __init__(self, toks): self.t, self.i = toks, 0
    def peek(self): return self.t[self.i] if self.i < len(self.t) else None
    def next(self):
        v = self.peek(); self.i += 1; return v
    def expect(self, c):
        if self.next() != c: raise ValueError("expected " + c)

    def atom(self):
        tok = self.peek()
        if tok is None: raise ValueError("eof")
        if tok == "(":
            self.next()
            items = [self.atom()]
            while self.peek() == ",":
                self.next(); items.append(self.atom())
            self.expect(")")
            return items[0] if len(items) == 1 else ("pair", items)
        if tok == "[":
            self.next(); items = []
            if self.peek() != "]":
                items.append(self.atom())
                while self.peek() == ",":
                    self.next(); items.append(self.atom())
            self.expect("]")
            return ("seq", items)
        if re.fullmatch(r'-?\d+', tok):
            self.next(); return ("int", int(tok))
        if tok.startswith('"'):
            self.next(); return ("str", json.loads(tok))
        self.next()
        name = tok.split(".")[-1]
        qual = ".".join(tok.split(".")[-2:])
        if qual in ("Val.unit",):            return ("unit",)
        if qual in ("EResult.outOfFuel",):   return ("outOfFuel",)
        if name in ("true", "false"):        return ("bool", name == "true")
        # `Val.bobj cls payload` takes TWO arguments -- the only Val constructor that
        # does. Parsed as a one-argument constructor it consumed the class name and left
        # the payload dangling, so every `_HashedTuple` result came back "unparsable" and
        # was counted INCONCLUSIVE. Core produced the right value; the oracle could not
        # read it.
        if qual == "Val.bobj":
            cls = self.atom()
            payload = self.atom()
            return ("bobj", cls[1] if cls[0] == "str" else "?", payload)
        # `Val.clos name captured` also takes two arguments. Unboxing a function object
        # (Core section 47) exposes these, because a decorator's `wrapper` is a CLOSURE --
        # so the six `_cached.py` functions went from a shape clash straight to
        # "unparsable" and stayed INCONCLUSIVE. A closure IS a function value for the
        # purpose of comparing return values; the captured environment is not something
        # CPython hands the oracle, so it is parsed and dropped rather than compared.
        if qual == "Val.clos":
            nm = self.atom()
            _cap = self.atom()
            return ("fn", nm[1] if nm[0] == "str" else "?")
        arg = self.atom()
        if qual == "Val.int":   return ("int", arg[1])
        if qual == "Val.str":   return ("str", arg[1])
        if qual == "Val.bool":  return ("bool", arg[1])
        if qual == "Val.ref":   return ("ref", arg[1])
        if qual == "Val.fn":    return ("fn", arg[1])
        if qual == "Val.list":  return ("list", arg[1])
        if qual == "Val.tuple": return ("tuple", arg[1])
        if qual == "Val.dict":
            return ("dict", [(p[1][0], p[1][1]) for p in arg[1]])
        if qual in ("EResult.val", "EResult.exn", "EResult.hole"):
            return (name, arg)
        raise ValueError("unknown ctor " + tok)


def parse_result(line):
    """-> ('val', Val) | ('exn', Val) | ('hole', str) | ('outOfFuel',)"""
    p = P(tokenize(line))
    r = p.atom()
    if r[0] == "hole":
        return ("hole", r[1][1] if r[1][0] == "str" else "?")
    if r[0] in ("val", "exn"): return (r[0], r[1])
    if r[0] == "outOfFuel": return ("outOfFuel",)
    raise ValueError("not an EResult: " + line[:80])


# ---------------------------------------------------------------------- comparison

def unwrap_bobj(v):
    """A `Val.bobj cls payload` compares as its payload.

    `class _HashedTuple(tuple)` translates to `Val.bobj "_HashedTuple" (tuple …)`, and
    Core's `Val.beq` compares such a value BY CONTENTS, ignoring the class — which is
    CPython's answer for a builtin subclass that does not override `__eq__`
    (`hashkey(0) == (0,)` is `True`). CPython hands the oracle a plain tuple, so comparing
    the payload is the same relation the semantics implements, not a convenience.

    Before this the harness had no `bobj` case at all: `hashkey` and `methodkey` came back
    `representation:value-vs-object` and were counted INCONCLUSIVE — the oracle refusing to
    look at a value Core had been fixed to produce correctly."""
    while isinstance(v, tuple) and len(v) == 3 and v[0] == "bobj":
        v = v[2]
    return v


def same(py, ln, base):
    """Compare an encoded Python value against a parsed Lean value.

    Dicts compare order-insensitively: Core's `Val.dict` is an association list whose
    order is observable, but Python's insertion order is not part of the contract we
    are checking here, and pretending otherwise would manufacture divergences."""
    ln = unwrap_bobj(ln)
    if py[0] != ln[0]:
        # Core has no separate tuple/list distinction at some call sites; still, do not
        # paper over it — report as a mismatch.
        return False
    t = py[0]
    if t in ("unit",): return True
    if t in ("int", "bool", "str"): return py[1] == ln[1]
    if t == "fn":
        # `Val.fn` names are spelled differently on the two sides: CPython reports a
        # `__qualname__` (`TTLCache._Link`), Joern a fully-qualified one
        # (`pkg/mod.py:<module>.TTLCache._Link`). Core's own `Ctx.resolve` matches
        # callables by dotted suffix, so accept exactly that and nothing looser.
        # The two sides spell nesting differently: CPython's `__qualname__` inserts
        # `<locals>` for a function defined inside a function (`_locked_info.<locals>.
        # wrapper`), Joern's fully-qualified name inserts `<module>` for file scope
        # (`cachetools/_cached.py:<module>._locked_info.wrapper`). Neither segment names
        # anything a program can refer to, so drop both before matching by dotted suffix.
        def _qual(x):
            x = x.split(":")[-1]
            return ".".join(p for p in x.split(".") if p not in ("<locals>", "<module>"))
        a, b = _qual(py[1]), _qual(ln[1])
        return a == b or a.endswith("." + b) or b.endswith("." + a)
    if t == "ref": return py[1] + base == ln[1]
    if t in ("list", "tuple"):
        return len(py[1]) == len(ln[1]) and all(same(a, b, base)
                                                for a, b in zip(py[1], ln[1]))
    if t == "dict":
        if len(py[1]) != len(ln[1]): return False
        rest = list(ln[1])
        for k, v in py[1]:
            for j, (k2, v2) in enumerate(rest):
                if same(k, k2, base) and same(v, v2, base):
                    rest.pop(j); break
            else:
                return False
        return True
    return False


def shape_clash(py, ln):
    """True when the two sides disagree about value-vs-object representation."""
    ln = unwrap_bobj(ln)
    containers = ("list", "tuple", "dict")
    if py[0] == "ref" and ln[0] in containers: return True
    if ln[0] == "ref" and py[0] in containers: return True
    if py[0] in containers and ln[0] in containers and py[0] != ln[0]: return False
    if py[0] in ("list", "tuple") and ln[0] in ("list", "tuple"):
        return any(shape_clash(a, b) for a, b in zip(py[1], ln[1]))
    return False


def show(v):
    t = v[0]
    if t == "unit": return "unit"
    if t in ("int", "bool", "str", "fn", "ref"): return "%s %r" % (t, v[1])
    if t in ("list", "tuple"): return "%s[%s]" % (t, ", ".join(show(x) for x in v[1]))
    if t == "dict": return "{%s}" % ", ".join("%s: %s" % (show(a), show(b))
                                              for a, b in v[1])
    return str(v)


# ------------------------------------------------------------------- test tracing

def find_tests(src_root):
    """Locate the repository's own test suite."""
    roots, cur = [], os.path.abspath(src_root)
    for _ in range(3):
        roots.append(cur); cur = os.path.dirname(cur)
    seen = []
    for r in roots:
        for name in ("tests", "test"):
            d = os.path.join(r, name)
            if os.path.isdir(d) and glob.glob(os.path.join(d, "**", "test_*.py"),
                                              recursive=True):
                seen.append(d)
        if glob.glob(os.path.join(r, "test_*.py")): seen.append(r)
    out = []
    for d in seen:
        if d not in out: out.append(d)
    return out


def resolve_src_root(src_root, rel_files):
    """Find the directory the AST's relative paths are actually rooted at.

    Joern's paths are relative to whatever directory was parsed, which for the modern
    `src/` layout is `<repo>/src` while the tests live at `<repo>/tests`. Pointing the
    harness at the repo root is the natural thing to do and used to silently yield zero
    test-derived cases, so correct it here instead."""
    rels = [r for r in rel_files if r]
    if not rels: return src_root

    def hits(root):
        return sum(1 for r in rels if os.path.exists(os.path.join(root, r)))
    best, n = os.path.abspath(src_root), hits(src_root)
    if n == len(rels): return best
    cands = [os.path.join(src_root, d) for d in ("src", "lib", "python")]
    try:
        cands += [os.path.join(src_root, d.name) for d in os.scandir(src_root)
                  if d.is_dir() and not d.name.startswith(".")]
    except OSError:
        pass
    for c in cands:
        if not os.path.isdir(c): continue
        m = hits(c)
        if m > n: best, n = os.path.abspath(c), m
    if os.path.abspath(best) != os.path.abspath(src_root):
        print("source root corrected: %s -> %s (%d/%d AST paths resolve there)"
              % (src_root, best, n, len(rels)))
    return best


def build_lineno_index(src_root, wanted_files):
    """(abs source file, first line of def) -> qualified AST name.

    Python 3.9 has no `co_qualname`, so we recover the qualified name from the source
    with the `ast` module and key on the code object's `co_firstlineno`."""
    import ast as pyast

    def mangle(name, cls):
        """CPython private name mangling: inside `class C`, `__x` becomes `_C__x`.

        The transpiler applies this rule, so the qualnames recovered here must too —
        otherwise a traced call to `LFUCache.__touch` never matches the translated
        `LFUCache._LFUCache__touch` and the function is silently dropped from the oracle's
        reach. Two or more leading underscores, at most one trailing."""
        if cls is None: return name
        if not name.startswith("__"): return name
        if name.endswith("__"): return name
        return "_" + cls.lstrip("_") + name

    idx = {}
    for rel in wanted_files:
        path = os.path.join(src_root, rel)
        # `isfile`, not `exists`: an AST entry with an empty `file` (a module-level
        # initialiser) joins to the source ROOT, which exists and is a directory. Opening
        # it raised IsADirectoryError and killed the run before any case was compared.
        if not os.path.isfile(path): continue
        try:
            tree = pyast.parse(open(path, encoding="utf-8").read(), path)
        except (SyntaxError, OSError, UnicodeDecodeError):
            continue
        stack = []

        def walk(node, prefix, cls):
            for ch in pyast.iter_child_nodes(node):
                if isinstance(ch, (pyast.FunctionDef, pyast.AsyncFunctionDef)):
                    qual = prefix + mangle(ch.name, cls)
                    # decorators shift co_firstlineno to the first decorator line
                    lines = [ch.lineno] + [d.lineno for d in ch.decorator_list]
                    for ln in lines:
                        idx.setdefault((os.path.abspath(path), ln), (rel, qual))
                    # a nested def does not change the mangling class
                    walk(ch, qual + ".", cls)
                elif isinstance(ch, pyast.ClassDef):
                    walk(ch, prefix + ch.name + ".", ch.name)
                else:
                    walk(ch, prefix, cls)
        walk(tree, "", None)
    return idx


VARARGS, VARKW = 0x04, 0x08


def frame_param_order(code):
    """Parameter names in *source* order, plus how each one binds.

    `co_varnames` lists positional names, then keyword-only names, then `*args`, then
    `**kwargs` — which is not the order they were written in, and not the order the
    transpiler recorded. Rebuild the source order so it can be checked against the AST.
    """
    n, k = code.co_argcount, code.co_kwonlyargcount
    pos = list(code.co_varnames[:n])
    kwonly = list(code.co_varnames[n:n + k])
    i = n + k
    star = None
    if code.co_flags & VARARGS:
        star = code.co_varnames[i]; i += 1
    dstar = code.co_varnames[i] if code.co_flags & VARKW else None
    order = [(p, "pos") for p in pos]
    if star is not None: order.append((star, "star"))
    order += [(p, "kwonly") for p in kwonly]
    if dstar is not None: order.append((dstar, "dstar"))
    return order


def bind_args(order, loc, enc, ast_params, self_name):
    """Encode one call's arguments in the order Core will bind them.

    Core binds by position: `applyFunc` zips `Func.params` with the argument list. That
    is faithful to CPython only if the transpiler's parameter list is name-for-name the
    source parameter list, so require exactly that and refuse otherwise — a silent
    off-by-one in parameter binding would be indistinguishable from a semantics bug.

    `*args` binds to a tuple and `**kwargs` to a dict, which is what the *callee* sees
    and what the translated body reads (`cachetools.keys.hashkey` does `args + _kwmark`
    on it). Refusing these cost ~13k calls for no fidelity reason.
    """
    names = [n for n, _ in order]
    if self_name is not None: names = names[1:]
    if ast_params is not None and names != list(ast_params):
        raise ParamMismatch("%s vs %s" % (names, list(ast_params)))
    slf, args = None, []
    for i, (n, kind) in enumerate(order):
        if i == 0 and n == self_name:
            slf = enc.enc(loc[n])
            continue
        v = loc[n]
        if kind == "star":
            # SPREAD, do not pass the packed tuple.
            #
            # A frame's `*args` local is already the packed tuple. Passing it as one
            # positional argument was right while Core had no calling convention -- it
            # simply bound to the first parameter. Now `bindParams` packs the surplus
            # positionals itself, so passing the packed value packs it AGAIN:
            # `hashkey(0)` came out as `((0,), {})` against CPython's `(0,)`, and was
            # reported as a divergence in the semantics. The bug was here.
            for elem in v:
                args.append(enc.enc(elem))
            continue
        if kind == "dstar":
            # The harness has no keyword channel (it calls `applyFunc … args []`), so a
            # non-empty `**kwargs` cannot be represented and must be refused rather than
            # flattened into positionals, which would bind to the wrong parameters.
            if v:
                raise ParamMismatch("non-empty **%s cannot be passed positionally" % n)
            continue
        args.append(enc.enc(v))
    return slf, args


class ParamMismatch(Exception):
    pass


def trace_tests(src_root, test_dirs, index, wanted, limit_per_fn, stats,
                params_by_name=None, live=None, pool=None):
    """Run the project's test suite under `sys.settrace`, recording calls into `wanted`.

    Each record is a fully-encoded snapshot taken *at call time*, so later mutation of
    the arguments cannot corrupt it."""
    records = []
    counts = {}
    live_files = set(p for (p, _) in index)

    params_by_name = params_by_name if params_by_name is not None else {}
    live = live if live is not None else {}        # class name -> live instances
    pool = pool if pool is not None else {}        # parameter name -> live values

    def snapshot(frame, qual, key):
        code = frame.f_code
        order = frame_param_order(code)
        loc = frame.f_locals
        self_name = order[0][0] if order and order[0][0] == "self" else None
        enc = Encoder()
        try:
            slf, args = bind_args(order, loc, enc, params_by_name.get(key), self_name)
        except ParamMismatch as e:
            stats["skip_param_mismatch"] = stats.get("skip_param_mismatch", 0) + 1
            r = stats.setdefault("param_mismatch_detail", {})
            r[qual] = e.args[0]
            return None
        except (Unencodable, KeyError) as e:
            stats["skip_unencodable_args"] += 1
            r = stats.setdefault("unencodable_reasons", {})
            k = "%s: %s" % (qual, e.args[0] if e.args else type(e).__name__)
            r[k] = r.get(k, 0) + 1
            return None
        if self_name is not None:
            if slf is None or slf[0] != "ref":
                # e.g. a `tuple` subclass: the receiver is a value, not an object with
                # fields, and Core has no such receiver.
                stats["skip_self_not_object"] = \
                    stats.get("skip_self_not_object", 0) + 1
                return None
            # keep the live receiver: it is the only way to exercise sibling methods
            # the suite never calls (see `constructed_cases`)
            inst = loc[self_name]
            bucket = live.setdefault(type(inst).__name__, [])
            if len(bucket) < 4 and not any(o is inst for o in bucket):
                bucket.append(inst)
        for (n, kind) in order:
            if n == self_name: continue
            b = pool.setdefault(n, [])
            if len(b) < 6:
                try:
                    if not any(o is loc[n] for o in b): b.append(loc[n])
                except KeyError:
                    pass
        return enc, slf, args

    # frames have no user-writable slot, so carry per-call state keyed by frame id
    state_by_frame = {}

    def local2(frame, event, arg):
        st = state_by_frame.get(id(frame))
        if st is None: return None
        if event == "exception":
            st["exn"] = arg[0].__name__
        elif event == "return":
            rec = st["rec"]
            if arg is None and st.get("exn"):
                rec["outcome"] = ("exn", st["exn"])
            else:
                try:
                    rec["outcome"] = ("val", st["enc"].enc_result(arg))
                except Unencodable as e:
                    stats["skip_unencodable_ret"] += 1
                    r = stats.setdefault("unencodable_reasons", {})
                    k = "%s: result %s" % (rec["name"].split(".")[-1],
                                           e.args[0] if e.args else "?")
                    r[k] = r.get(k, 0) + 1
                    rec = None
            state_by_frame.pop(id(frame), None)
            if rec is not None: records.append(rec)
        return local2

    def tracer2(frame, event, arg):
        if event != "call": return None
        code = frame.f_code
        hit = index.get((os.path.abspath(code.co_filename), code.co_firstlineno))
        if hit is None: return None
        rel, qual = hit
        key = "%s:<module>.%s" % (rel, qual)
        if key not in wanted or counts.get(key, 0) >= limit_per_fn: return None
        snap = snapshot(frame, qual, key)
        if snap is None: return None
        enc, slf, args = snap
        counts[key] = counts.get(key, 0) + 1
        enc.freeze()
        state_by_frame[id(frame)] = {
            "rec": {"name": key, "heap": enc.heap, "self": slf, "args": args,
                    "outcome": None},
            "enc": enc, "exn": None}
        return local2

    old_path = list(sys.path)
    sys.path.insert(0, os.path.abspath(src_root))
    for d in test_dirs:
        sys.path.insert(0, os.path.dirname(os.path.abspath(d)))
    ran = []
    buf = io.StringIO()
    try:
        sys.settrace(tracer2)
        for d in test_dirs:
            try:
                with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
                    rc = run_suite(d)
                ran.append({"dir": d, "rc": rc})
            except Exception as e:                       # noqa: BLE001
                ran.append({"dir": d, "error": repr(e)[:200]})
    finally:
        sys.settrace(None)
        sys.path[:] = old_path
    stats["test_runs"] = ran
    return records


def _raw_attr(cls, name):
    """The *descriptor* for `name`, not the value binding it would produce."""
    for c in cls.__mro__:
        if name in c.__dict__: return c.__dict__[name]
    return None


def find_module(rel):
    """The imported module for a corpus-relative source path, or None.

    Falling back to an explicit import matters more than it looks. `import cachetools`
    pulls in `cachetools.keys` and nothing else -- `_cached` and `_cachedmethod` are
    imported lazily inside functions -- so tracing the suite never put them in
    `sys.modules`, `find_class` returned None for every class they define, and 48
    functions were reported as blocked. The cause recorded against them was
    "constructor rejected ()/(1)/(2,1)", which was false: no constructor was ever
    reached, because the module holding the class had never been loaded.

    Importing a submodule of a package the suite already imported is not fabricating
    state -- it is loading code the corpus ships and the AST was exported from."""
    mod = rel[:-3].replace("/", ".").replace("\\", ".")
    if mod.endswith(".__init__"): mod = mod[:-9]
    m = sys.modules.get(mod)
    if m is not None:
        return m
    try:
        import importlib
        return importlib.import_module(mod)
    except Exception:                                       # noqa: BLE001
        return None


def find_class(rel, clsname):
    """Locate a class the test suite already imported, by module path and name."""
    m = find_module(rel)
    if m is None: return None
    obj = m
    for part in clsname.split("."):
        obj = getattr(obj, part, None)
        if obj is None: return None
    return obj if isinstance(obj, type) else None


class Timeout(Exception):
    pass


@contextlib.contextmanager
def time_limit(seconds):
    """Guard against a synthesized call that blocks (locks, sleeps, IO)."""
    import signal
    try:
        def handler(sig, frm): raise Timeout()
        old = signal.signal(signal.SIGALRM, handler)
        signal.setitimer(signal.ITIMER_REAL, seconds)
    except (ValueError, AttributeError):
        yield; return            # not the main thread, or no SIGALRM: run unguarded
    try:
        yield
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, old)


def _ctor_attempts(cls, pool):
    """Argument tuples to try for `cls(...)`, best first.

    The old search was three hardcoded shapes -- `()`, `(1,)`, `(2, 1)` -- and it was the
    single largest blocker in the whole report: 54 functions, more than were being compared,
    failed as "no live instance". They are not blocked by the semantics. `_WrapperBase`
    takes four arguments and `cachedmethod`'s decorator takes a callable, so no tuple of
    small integers was ever going to construct one.

    So drive the search from the constructor's own parameter names, using the SAME observed
    -value pool the method-argument synthesis already uses, and fall back by name only for
    the shapes a cache library obviously needs. Anything constructed here still goes through
    the identical encode/refuse/compare path as a traced call, so this widens what the oracle
    can reach without widening what it will accept."""
    attempts = [(), (1,), (2, 1)]
    try:
        order = frame_param_order(cls.__init__.__code__)
    except Exception:                                       # noqa: BLE001
        return attempts
    if any(k in ("star", "dstar", "kwonly") for _, k in order):
        return attempts
    names = [n for n, _ in order][1:]
    if not names:
        return attempts
    synth = []
    for n in names:
        cand = pool.get(n) or []
        if cand:
            synth.append(cand[0]); continue
        synth.append(_ctor_fallback(n))
    attempts.insert(0, tuple(synth))
    # ... and the same shape with the trailing optional parameters dropped, since a
    # constructor that rejects a fabricated `lock` may still accept a shorter call.
    for k in range(len(synth) - 1, 0, -1):
        attempts.append(tuple(synth[:k]))
    return attempts


def _ctor_fallback(n):
    """A plausible value for a constructor parameter no run ever observed. By NAME only --
    guessing from a type annotation would be guessing about a contract the code may not
    keep, and a wrong instance is worse than no instance."""
    low = n.lower()
    if low in ("func", "method", "fn", "callable", "user_function"):
        return lambda *a, **k: None
    if low in ("key", "getsizeof", "timer", "ttu"):
        return lambda *a, **k: 1
    if low in ("lock", "cond", "condition"):
        import threading
        return threading.RLock() if low == "lock" else threading.Condition()
    if low in ("maxsize", "ttl", "size", "n", "count"):
        return 1
    if low in ("cache",):
        return {}
    if low in ("info",):
        return False
    return 1


def _direct_cases(fn, f, pool, ncases, out):
    """Call a plain callable with synthesized arguments and append the cases it yields."""
    try:
        order = frame_param_order(fn.__code__)
    except Exception:                                       # noqa: BLE001
        return 0
    if any(k in ("star", "dstar", "kwonly") for _, k in order):
        return 0
    names = [n for n, _ in order]
    if names != list(f["params"]):
        return 0
    made = 0
    for attempt in range(ncases * 3):
        if made >= ncases:
            break
        argv = []
        for n in names:
            cand = pool.get(n) or []
            argv.append(cand[attempt % len(cand)] if cand else random.randint(-8, 8))
        enc = Encoder()
        try:
            eargs = [enc.enc(a) for a in argv]
        except Unencodable:
            return made
        enc.freeze()
        try:
            with time_limit(2.0):
                got = fn(*argv)
            outcome = ("val", enc.enc_result(got))
        except Timeout:
            return made
        except Unencodable:
            continue
        except Exception as e:                              # noqa: BLE001
            outcome = ("exn", type(e).__name__)
        out.append({"name": f["name"], "heap": enc.heap, "self": None,
                    "args": eargs, "outcome": outcome, "origin": "constructed"})
        made += 1
    return made


def _factory_args(fn, pool):
    """Arguments for calling a factory, drawn from observed values then by name."""
    try:
        order = frame_param_order(fn.__code__)
    except Exception:                                       # noqa: BLE001
        return []
    if any(k in ("star", "dstar", "kwonly") for _, k in order):
        return []
    out = []
    for n, _ in order:
        cand = pool.get(n) or []
        out.append(cand[0] if cand else _ctor_fallback(n))
    return out


def resolve_via_factory(mod, clsname, attr, pool):
    """The callable named `clsname.attr`, reached by CALLING the factory that defines it.

    A decorator's `wrapper` and the `Descriptor.Wrapper` classes cachetools builds inside
    `_condition`/`_locked`/`_unlocked` do not exist until their factory runs -- they are
    closures, not module attributes. Splitting the qualified name on the last dot had
    classified them as `Class.method`, so the report said "class not found", which is true
    and useless: nothing is wrong with the class, it simply has not been created yet.

    Returns a routine to call directly, a class to construct, or None. Never raises: a
    factory that rejects fabricated arguments is a missing case, not a failure."""
    segs = clsname.split(".")
    root = getattr(mod, segs[0], None)
    if root is None or not inspect.isroutine(root):
        return None
    try:
        with time_limit(2.0):
            obj = root(*_factory_args(root, pool))
    except Exception:                                       # noqa: BLE001
        return None
    for sname in segs[1:]:
        obj = getattr(obj, sname, None)
        if obj is None:
            return None
    target = getattr(obj, attr, None)
    if target is not None and (inspect.isroutine(target) or isinstance(target, type)):
        return target
    # the factory's RESULT may itself be the thing named `attr` (`_locked` returns
    # `wrapper`), in which case there is no attribute to look up
    if inspect.isroutine(obj) and getattr(obj, "__qualname__", "").split(".")[-1] == attr:
        return obj
    if isinstance(obj, type):
        return obj
    return None


def constructed_cases(methods, reached, live, pool, stats, ncases):
    """Exercise hole-free methods the test suite never called.

    The suite is the source of *realistic* state, so rather than fabricating an object
    we reuse a real instance it built for a sibling method (falling back to calling the
    class's own constructor), and draw arguments from values observed at parameters of
    the same name. Everything else — encoding, refusal, comparison — is the same path
    as a traced call, so a constructed case is no more lenient than a recorded one; it
    is only differently sourced, and is tagged `constructed` in the report.
    """
    out = []
    why = stats.setdefault("no_instance_detail", {})
    for f, rel, qual in methods:
        if f["name"] in reached: continue
        if "." not in qual:
            why[qual] = "not a method"; continue
        clsname, attr = qual.rsplit(".", 1)
        insts = list(live.get(clsname.split(".")[-1], ()))
        cls = find_class(rel, clsname)
        if not insts and cls is not None:
            tried = _ctor_attempts(cls, pool)
            for mk in tried:
                try:
                    with time_limit(2.0):
                        insts = [cls(*mk)]
                    break
                except Exception:                       # noqa: BLE001
                    continue
        if not insts:
            # Say WHICH of these it is. The old message was "no live instance and
            # constructor rejected ()/(1)/(2,1)" for all 54 functions in this bucket --
            # the largest single category in the report, larger than COMPARED -- and for
            # 50 of them it was FALSE: there is no class and no constructor was ever
            # tried. `_condition.wrapper` and `_locked_info.cache_info` are nested
            # FUNCTIONS, closures returned by a factory, which the caller-side split on
            # the last dot had classified as `Class.method`. A wrong cause is worse than
            # a coarse one: it sends the next person to widen a constructor search that
            # was never reached.
            if cls is None:
                # `rel` is a corpus-relative PATH, not a module -- resolve it before
                # asking what the parent name is, or every lookup silently returns None
                # and every cause comes out "class not found".
                m = find_module(rel)
                parent = clsname.rsplit(".", 1)[-1]
                pobj = getattr(m, parent, None) if m is not None else None
                if m is None:
                    why[qual] = "module for %s not imported by the suite" % rel
                    continue
                if pobj is not None and inspect.isroutine(pobj):
                    tgt = resolve_via_factory(m, clsname, attr, pool)
                    if tgt is not None and inspect.isroutine(tgt):
                        made = _direct_cases(tgt, f, pool, ncases, out)
                        if made:
                            why.pop(qual, None)
                            continue
                        why[qual] = ("reached through %s(...), but no case survived "
                                     "encoding" % parent)
                        continue
                    why[qual] = ("nested function, not a method: needs %s(...) called and "
                                 "its result captured" % parent)
                else:
                    why[qual] = "class %s not found in the module" % clsname
            else:
                why[qual] = ("no live instance; constructor rejected %d argument shapes"
                             % len(tried))
            continue
        raw = _raw_attr(type(insts[0]), attr) if not cls else \
            (_raw_attr(cls, attr) or _raw_attr(type(insts[0]), attr))
        if isinstance(raw, property): raw = raw.fget
        if isinstance(raw, (staticmethod, classmethod)): raw = raw.__func__
        if not inspect.isroutine(raw):
            why[qual] = "no callable attribute %r on the class" % attr; continue
        try:
            order = frame_param_order(raw.__code__)
        except AttributeError:
            why[qual] = "builtin, no bytecode"; continue
        names = [n for n, _ in order]
        self_name = names[0] if names and names[0] == "self" else None
        if self_name is None:
            why[qual] = "no self parameter"; continue
        if any(k in ("star", "dstar", "kwonly") for _, k in order):
            why[qual] = "varargs/keyword-only: cannot synthesize a faithful call"
            continue
        if [n for n, _ in order][1:] != list(f["params"]):
            why[qual] = "parameter list disagrees with the AST"; continue
        made = 0
        for attempt in range(ncases * 4):
            if made >= ncases: break
            inst = insts[attempt % len(insts)]
            argv = []
            for n, _ in order[1:]:
                cand = pool.get(n) or []
                argv.append(cand[attempt % len(cand)] if cand
                            else random.randint(-8, 8))
            enc = Encoder()
            try:
                slf = enc.enc(inst)
                if slf[0] != "ref": raise Unencodable("self-not-object")
                eargs = [enc.enc(a) for a in argv]
            except Unencodable as e:
                why[qual] = "unencodable receiver/arguments: %s" % (e.args[0],)
                break
            enc.freeze()
            try:
                with time_limit(2.0):
                    got = raw(inst, *argv)
                outcome = ("val", enc.enc_result(got))
            except Timeout:
                why[qual] = "call did not terminate within 2s"; break
            except Unencodable as e:
                why[qual] = "unencodable result: %s" % (e.args[0],); break
            except Exception as e:                       # noqa: BLE001
                outcome = ("exn", type(e).__name__)
            out.append({"name": f["name"], "heap": enc.heap, "self": slf,
                        "args": eargs, "outcome": outcome, "origin": "constructed"})
            made += 1
        if made: why.pop(qual, None)
    return out


def run_suite(test_dir):
    """Run one test directory with whatever runner the project uses."""
    try:
        import pytest
    except ImportError:
        pytest = None
    if pytest is not None:
        return int(pytest.main([test_dir, "-q", "-p", "no:cacheprovider",
                                "--no-header"]))
    import unittest
    loader = unittest.TestLoader()
    suite = loader.discover(test_dir, top_level_dir=os.path.dirname(test_dir))
    return 0 if unittest.TextTestRunner(verbosity=0).run(suite).wasSuccessful() else 1


# ----------------------------------------------------------------------- C runtime

def c_runtime(src_root):
    """Compile the C sources to a shared library and expose them via ctypes.

    Same oracle, different runtime: the point of the Core language is that one semantics
    is checked against whichever real implementation produced the code."""
    import ctypes
    srcs = glob.glob(os.path.join(src_root, "**", "*.c"), recursive=True)
    if not srcs: return None
    lib = os.path.join(WORK, "libautoform_diff_c" +
                       (".dylib" if sys.platform == "darwin" else ".so"))
    r = subprocess.run(["cc", "-shared", "-fPIC", "-O0", "-o", lib] + srcs,
                       capture_output=True, text=True)
    if r.returncode != 0:
        print("cc failed:", r.stderr[:300]); return None
    dll = ctypes.CDLL(lib)

    def get(name, nargs):
        try: fn = getattr(dll, name)
        except AttributeError: return None
        fn.restype = ctypes.c_int
        fn.argtypes = [ctypes.c_int] * nargs
        return fn
    return get


def call_in_child(fn, args):
    """Run one native call in a forked child; None if it crashed or hung."""
    r, w = os.pipe()
    pid = os.fork()
    if pid == 0:                                    # child
        try:
            os.close(r)
            v = fn(*args)
            os.write(w, ("%d" % v).encode())
            os.close(w)
        except BaseException:                       # noqa: BLE001
            pass
        os._exit(0)
    os.close(w)
    out = b""
    try:
        while True:
            chunk = os.read(r, 64)
            if not chunk: break
            out += chunk
    finally:
        os.close(r)
        _, status = os.waitpid(pid, 0)
    if not os.WIFEXITED(status) or not out:
        return None
    try:
        return int(out)
    except ValueError:
        return None


def call_in_child_twice(fn, args):
    """Call the same function twice with the same arguments in one forked child.

    Returns (v1, v2), either of which is None if the child died.

    This is the allocation-dependence discriminator for the wasm UB oracle. A function
    that returns a freshly `malloc`ed pointer (`sdsempty`, `sds_malloc`) hands back a
    different value on the second call; a pure integer function hands back the same one.
    Without this test, every pointer-returning function looks like a native/wasm
    disagreement -- native reports a 64-bit heap address, wasm reports a 32-bit linear
    memory offset -- and the UB count fills up with results that are nothing but two
    different address spaces. That would be a self-flattering metric pointed the other
    way: an impressive-sounding pile of "UB found" that is entirely an artifact.
    """
    r, w = os.pipe()
    pid = os.fork()
    if pid == 0:                                    # child
        try:
            os.close(r)
            v1 = fn(*args); v2 = fn(*args)
            os.write(w, ("%d,%d" % (v1, v2)).encode())
            os.close(w)
        except BaseException:                       # noqa: BLE001
            pass
        os._exit(0)
    os.close(w)
    out = b""
    try:
        while True:
            chunk = os.read(r, 64)
            if not chunk: break
            out += chunk
    finally:
        os.close(r)
        _, status = os.waitpid(pid, 0)
    if not os.WIFEXITED(status) or b"," not in out:
        return None, None
    try:
        a, b = out.split(b",", 1)
        return int(a), int(b)
    except ValueError:
        return None, None


def load_module(path, root):
    """The module for a source file.

    Ask for it BY PACKAGE NAME first. Loading a file by path gives it a synthetic top-level
    name (`cachetools__init___py`), which makes every RELATIVE import inside it fail --
    `from . import keys` has no package to be relative to. That is not an edge case: it is
    every package `__init__.py`, and here it silently cost `cached`, `cachedmethod` and
    `_cache` their cases, which then reported as "hole-free, no case built" as though the
    functions were unreachable rather than the loader broken.

    The path loader stays as the fallback, for a corpus that is not an importable package."""
    rel = os.path.relpath(path, root)
    m = find_module(rel)
    if m is not None:
        return m
    name = re.sub(r'[^A-Za-z0-9_]', '_', rel)
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec)
    sys.path.insert(0, root)
    try:
        spec.loader.exec_module(m)
        return m
    except Exception:
        return None


# ------------------------------------------------------------------ language dispatch
#
# The corpus decides which real runtime the oracle must talk to. Getting this wrong is
# not a missing feature but a *false* result: `cartographer/render_lean.py`'s
# `infer_dialect` used to default an unrecognised language to Python, and the oracle
# then cheerfully reported agreement. So the mapping is explicit, and an extension that
# is not in it is REFUSED rather than defaulted.

LANG_BY_EXT = {".py": "python", ".pyi": "python",
               ".c": "c", ".h": "c",
               ".java": "java", ".go": "go",
               ".js": "js", ".mjs": "js", ".cjs": "js",
               ".ts": "ts", ".tsx": "ts", ".mts": "ts",
               ".kt": "kotlin", ".kts": "kotlin"}

# The Core dialect each language *should* have. Java, Go and Kotlin have no constructor
# of their own yet, so they necessarily run under an approximation (`.cLike`). JS/TS now
# have their own `Autoform.Core.Dialect.javascript` (fixes the measured `&&`/`||` and
# 32-bit-overflow bugs, `docs/languages.md`), so they are no longer flagged inexact for
# those — but `.javascript`'s bitwise/shift operators still truncate wrong (real JS
# converts them to Int32; `.javascript`'s one `NumConfig` does not model that
# separately), so a divergence traceable to `&`/`|`/`^`/`<<`/`>>`/`>>>` is still a named
# dialect gap, not a transpiler bug — see `Dialect`'s doc comment in `Syntax.lean`.
DIALECT_FOR = {"python": ("python", True), "c": ("cLike", True),
               "java": ("cLike", False),      # java64 NumConfig exists but is unused
               "go": ("cLike", False),        # go64 likewise
               "js": ("javascript", True),    # bitwise/shift ops remain an approximation
               "ts": ("javascript", True),    # (see comment above); everything else fixed
               "kotlin": ("cLike", False)}

TOOLCHAIN = {"python": [], "c": ["cc"], "java": ["javac", "java"], "go": ["go"],
             "js": ["node"], "ts": ["node"], "kotlin": ["kotlinc"]}


def detect_language(funcs):
    """(language, extension histogram). Returns None rather than guessing."""
    exts = {}
    for f in funcs:
        ext = os.path.splitext(f.get("file", ""))[1].lower()
        if ext:
            exts[ext] = exts.get(ext, 0) + 1
    if not exts:
        return None, exts
    langs = {}
    for e, n in exts.items():
        k = LANG_BY_EXT.get(e)
        langs[k] = langs.get(k, 0) + n
    if None in langs and langs[None] > sum(v for k, v in langs.items() if k):
        return None, exts
    langs.pop(None, None)
    if not langs:
        return None, exts
    return max(langs, key=lambda k: langs[k]), exts


def have(cmd):
    for d in os.environ.get("PATH", "").split(":"):
        p = os.path.join(d, cmd)
        if os.path.isfile(p) and os.access(p, os.X_OK):
            return p
    return None


def missing_tools(lang):
    return [c for c in TOOLCHAIN.get(lang, []) if not have(c)]


# ------------------------------------------------------------------------ JVM backend

JAVA_PRIM = ("int", "long", "short", "byte", "boolean", "java.lang.String")
STRING_POOL = ["", "0", "11", "1.8.0_281", "17.0.1", "java.lang.String",
               "android.os.Bundle", "com.example.Foo"]
JAVA_SIG = re.compile(r'^(?P<cls>[\w.$]+)\.(?P<meth>[\w$<>]+):(?P<ret>[\w.$\[\]]+)'
                      r'\((?P<args>.*)\)$')

JAVA_DRIVER = r"""import java.lang.reflect.*;
import java.util.*;

public class AutoformDriver {
  static String enc(Object o) {
    if (o == null) return "null|";
    if (o instanceof String)
      return "str|" + Base64.getEncoder().encodeToString(((String) o).getBytes());
    if (o instanceof Boolean) return "bool|" + o;
    if (o instanceof Character) return "int|" + (int) (Character) o;
    return "int|" + o;
  }
  public static void main(String[] a) throws Exception {
    Scanner sc = new Scanner(System.in);
    while (sc.hasNextLine()) {
      String line = sc.nextLine();
      if (line.isEmpty()) continue;
      String[] p = line.split("\\|", -1);
      String idx = p[0], cn = p[1], mn = p[2];
      int n = Integer.parseInt(p[3]);
      Class<?>[] ts = new Class<?>[n];
      Object[] vs = new Object[n];
      for (int i = 0; i < n; i++) {
        String t = p[4 + 2 * i], v = p[5 + 2 * i];
        if (t.equals("int"))          { ts[i] = int.class;     vs[i] = Integer.parseInt(v); }
        else if (t.equals("long"))    { ts[i] = long.class;    vs[i] = Long.parseLong(v); }
        else if (t.equals("short"))   { ts[i] = short.class;   vs[i] = Short.parseShort(v); }
        else if (t.equals("byte"))    { ts[i] = byte.class;    vs[i] = Byte.parseByte(v); }
        else if (t.equals("boolean")) { ts[i] = boolean.class; vs[i] = Boolean.parseBoolean(v); }
        else { ts[i] = String.class; vs[i] = new String(Base64.getDecoder().decode(v)); }
      }
      try {
        Method m = Class.forName(cn).getDeclaredMethod(mn, ts);
        m.setAccessible(true);
        Object r = m.invoke(null, vs);
        System.out.println(idx + "|OK|" + enc(r));
      } catch (InvocationTargetException e) {
        System.out.println(idx + "|EXN|" + e.getCause().getClass().getSimpleName());
      } catch (Throwable t) {
        System.out.println(idx + "|ERR|" + t.getClass().getSimpleName());
      }
    }
  }
}
"""


def java_backend(src_root, holefree, ncases):
    """Compile each candidate's own file, then call it reflectively.

    The corpus (a gson subset) does not compile as a whole — most of gson is absent —
    so compilation is per file, and a file that will not build becomes a *reported*
    skip rather than a silent one. Only `static` methods whose whole signature is
    primitive-or-String are callable without building a receiver."""
    import base64
    work = os.path.join(WORK, "java")
    classes = os.path.join(work, "classes")
    os.makedirs(classes, exist_ok=True)
    info, skipped, cands = {}, {}, []
    for f in holefree:
        m = JAVA_SIG.match(f["name"])
        if not m:
            continue
        if "this" in f["params"]:
            skipped[f["name"]] = "instance method: needs a receiver"
            continue
        args = [a for a in m.group("args").split(",") if a]
        if len(args) != len(f["params"]):
            skipped[f["name"]] = "signature/parameter count disagree"
            continue
        if any(a not in JAVA_PRIM for a in args) or m.group("ret") not in JAVA_PRIM:
            skipped[f["name"]] = "non-primitive signature"
            continue
        src = os.path.join(src_root, f.get("file", ""))
        if not os.path.exists(src):
            skipped[f["name"]] = "source file not found under the corpus root"
            continue
        cands.append((f, m, args, src))
    info["primitive_static_candidates"] = len(cands)
    if not cands:
        return [], info, skipped
    compiled = set()
    for src in sorted({c[3] for c in cands}):
        r = subprocess.run(["javac", "-nowarn", "-d", classes, src],
                           capture_output=True, text=True)
        if r.returncode == 0:
            compiled.add(src)
        else:
            last = (r.stderr.strip().splitlines() or ["?"])[-1]
            for f, _, _, s2 in cands:
                if s2 == src:
                    skipped[f["name"]] = "javac failed: " + last[:70]
    info["files_compiled"] = len(compiled)
    cands = [c for c in cands if c[3] in compiled]
    if not cands:
        return [], info, skipped
    open(os.path.join(work, "AutoformDriver.java"), "w").write(JAVA_DRIVER)
    r = subprocess.run(["javac", "-nowarn", "-d", classes,
                        os.path.join(work, "AutoformDriver.java")],
                       capture_output=True, text=True)
    if r.returncode != 0:
        info["driver"] = "failed to compile: " + r.stderr[:200]
        return [], info, skipped
    calls, plan = [], []
    for f, m, argtypes, _ in cands:
        for _ in range(ncases):
            vals, enc = [], []
            for t in argtypes:
                if t == "java.lang.String":
                    v = random.choice(STRING_POOL)
                    vals.append(("str", v))
                    enc += [t, base64.b64encode(v.encode()).decode()]
                elif t == "boolean":
                    v = random.choice([True, False])
                    vals.append(("bool", v))
                    enc += [t, "true" if v else "false"]
                else:
                    v = random.randint(-20, 20)
                    vals.append(("int", v))
                    enc += [t, str(v)]
            calls.append("|".join([str(len(calls)), m.group("cls"), m.group("meth"),
                                   str(len(argtypes))] + enc))
            plan.append((f["name"], vals))
    out = subprocess.run(["java", "-cp", classes, "AutoformDriver"],
                         input="\n".join(calls) + "\n",
                         capture_output=True, text=True, timeout=300)
    got = {}
    for line in out.stdout.splitlines():
        p = line.split("|")
        if len(p) >= 2 and p[0].isdigit():
            got[int(p[0])] = p[1:]
    cases, unusable = [], {}
    for i, (name, vals) in enumerate(plan):
        r = got.get(i)
        if r is None:
            unusable[name] = "no answer from the JVM driver"
            continue
        if r[0] == "OK":
            kind = r[1]
            payload = r[2] if len(r) > 2 else ""
            if kind == "str":
                outcome = ("val", ("str", base64.b64decode(payload).decode()))
            elif kind == "bool":
                outcome = ("val", ("bool", payload == "true"))
            elif kind == "int":
                outcome = ("val", ("int", int(payload)))
            else:
                unusable[name] = "returned null: no faithful Core counterpart"
                continue
        elif r[0] == "EXN":
            outcome = ("exn", r[1])
        else:
            unusable[name] = "JVM driver error: " + (r[1] if len(r) > 1 else "?")
            continue
        cases.append({"name": name, "heap": [], "self": None,
                      "args": list(vals), "outcome": outcome, "origin": "random"})
    skipped.update(unusable)
    info["cases_built"] = len(cases)
    return cases, info, skipped


# ------------------------------------------------------------------------- Go backend

GO_FUNC = re.compile(r'^func\s+(?P<name>[A-Za-z_]\w*)\s*\((?P<args>[^)]*)\)\s*'
                     r'(?P<ret>[\w]*)\s*\{')

GO_MAIN = """package %s

import (
\t"encoding/json"
\t"fmt"
\t"os"
)

func AutoformDriverMain() {
\tvar calls [][]interface{}
\tjson.NewDecoder(os.Stdin).Decode(&calls)
\tout := [][]interface{}{}
%s
\tb, _ := json.Marshal(out)
\tfmt.Println(string(b))
}
"""


def go_backend(src_root, holefree, ncases):
    """Package-level int→int functions, executed from a generated file placed in a copy
    of the package so that unexported functions are reachable."""
    by_short = {}
    for f in holefree:
        by_short.setdefault(f["name"].split(".")[-1], f)
    cands = []
    for path in sorted(glob.glob(os.path.join(src_root, "*.go"))):
        if path.endswith("_test.go"):
            continue
        for line in open(path, encoding="utf-8", errors="replace"):
            m = GO_FUNC.match(line)
            if not m:
                continue
            args = [a.strip() for a in m.group("args").split(",") if a.strip()]
            if not args or not all(a.split()[-1] == "int" for a in args):
                continue
            if m.group("ret") != "int":
                continue
            f = by_short.get(m.group("name"))
            if f is not None:
                cands.append((f, m.group("name"), len(args)))
    info = {"int_to_int_package_functions": len(cands)}
    if not cands:
        info["note"] = ("no package-level int→int function in this corpus: every "
                        "exported entry point takes a struct, an interface or a "
                        "reflect.Value, none of which Core models")
    return [], info, {}


# ----------------------------------------------------------------------- Node backend

NODE_DRIVER = """const path = process.argv[2];
const calls = JSON.parse(process.argv[3]);
const out = [];
const mod = await import(path);
for (const c of calls) {
  const [i, name, args] = c;
  let fn = mod[name];
  if (typeof fn !== 'function' && typeof mod.default === 'function'
      && (name === 'default' || mod.default.name === name)) fn = mod.default;
  if (typeof fn !== 'function') { out.push([i, 'MISSING']); continue; }
  try {
    const r = fn(...args);
    if (r && typeof r.then === 'function') { out.push([i, 'ASYNC']); continue; }
    out.push([i, 'OK', r === undefined ? null : r, typeof r]);
  } catch (e) { out.push([i, 'EXN', e && e.constructor ? e.constructor.name : 'Error']); }
}
console.log('@@RESULT@@' + JSON.stringify(out));
"""


def node_backend(src_root, holefree, ncases, lang):
    """JS/TS through node. TypeScript runs via `--experimental-strip-types`, which
    handles type annotations only; anything needing real transpilation is refused
    rather than approximated."""
    work = os.path.join(WORK, "node")
    os.makedirs(work, exist_ok=True)
    cands, skipped = [], {}
    for f in holefree:
        tail = f["name"].split(":")[-1]
        params = [p for p in f["params"] if p != "this"]
        if "<" in tail or "#" in tail:
            skipped[f["name"]] = "closure or private member: not reachable from outside"
            continue
        if "this" in f["params"]:
            skipped[f["name"]] = "method: needs a receiver"
            continue
        if not params:
            skipped[f["name"]] = "no parameters: nothing to vary"
            continue
        cands.append((f, tail, params))
    info = {"exported_candidates": len(cands)}
    if not cands:
        info["note"] = ("no top-level exported function with parameters: this corpus is "
                        "classes, closures and async entry points")
        return [], info, skipped
    calls, plan = [], []
    for f, tail, params in cands:
        rel = f.get("file", "")
        for _ in range(ncases):
            args = [random.randint(-20, 20) for _ in params]
            calls.append([len(calls), tail, args])
            plan.append((f["name"], rel, args))
    by_file = {}
    for i, (_, rel, _) in enumerate(plan):
        by_file.setdefault(rel, []).append(i)
    drv = os.path.join(work, "driver.mjs")
    open(drv, "w").write(NODE_DRIVER)
    cases = []
    for rel, idxs in by_file.items():
        target = os.path.abspath(os.path.join(src_root, rel))
        if not os.path.exists(target):
            for i in idxs:
                skipped[plan[i][0]] = "source file not found under the corpus root"
            continue
        cmd = [have("node")]
        if lang == "ts":
            cmd.append("--experimental-strip-types")
        cmd += [drv, target, json.dumps([calls[i] for i in idxs])]
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
        line = [l for l in r.stdout.splitlines() if l.startswith("@@RESULT@@")]
        if not line:
            for i in idxs:
                skipped[plan[i][0]] = ("node could not load the module: "
                                       + r.stderr.strip().splitlines()[-1][:80]
                                       if r.stderr.strip() else "node produced no result")
            continue
        for rec in json.loads(line[0][len("@@RESULT@@"):]):
            i, kind = rec[0], rec[1]
            name, _, args = plan[i]
            if kind == "OK":
                v, t = rec[2], rec[3]
                if t == "number" and isinstance(v, int):
                    outcome = ("val", ("int", v))
                elif t == "boolean":
                    outcome = ("val", ("bool", v))
                elif t == "string":
                    outcome = ("val", ("str", v))
                else:
                    skipped[name] = "returned %s: no faithful Core counterpart" % t
                    continue
            elif kind == "EXN":
                outcome = ("exn", rec[2])
            else:
                skipped[name] = {"MISSING": "not exported at module scope",
                                 "ASYNC": "async: Core has no promises"}.get(kind, kind)
                continue
            cases.append({"name": name, "heap": [], "self": None,
                          "args": [("int", a) for a in args],
                          "outcome": outcome, "origin": "random"})
    info["cases_built"] = len(cases)
    return cases, info, skipped


# ---------------------------------------------------------------------------- main

def main():
    argv = [a for a in sys.argv[1:]]
    tests_override = None
    if "--tests" in argv:
        i = argv.index("--tests"); tests_override = argv[i + 1]; del argv[i:i + 2]
    # `--wasm` turns on the sandboxed second C implementation. It is OPT-IN, and
    # deliberately so: it changes which cases are attempted and which are withheld from
    # the Lean comparison, so it changes the denominator. A flag that silently altered
    # the basis would make new rates look comparable to old ones when they are not.
    wasm_mode = "--wasm" in argv
    if wasm_mode: argv.remove("--wasm")
    ast_path, src_root, lean_mod = argv[0], argv[1], argv[2]
    ncases = int(argv[3]) if len(argv) > 3 else 5
    funcs = json.load(open(ast_path))
    module_tag = lean_mod

    # ---- which real runtime does this corpus need?
    lang, exts = detect_language(funcs)
    RUNTIME = {"python": "cpython", "c": "cc", "java": "jvm", "go": "go",
               "js": "node", "ts": "node", "kotlin": "kotlin"}
    if lang is None:
        print("REFUSING to run: cannot identify the corpus language from its file "
              "extensions %s. Defaulting to CPython would report agreement between the "
              "Lean semantics and a runtime that never ran this code." % sorted(exts))
        json.dump({"module": module_tag, "ast": os.path.abspath(ast_path),
                   "status": "REFUSED: unknown source language",
                   "extensions": exts, "agree": 0, "total": 0, "divergences": 0,
                   "inconclusive": 0, "rate": "n/a",
                   "coverage": {"population": len(funcs), "compared": 0,
                                "covered_metric": "compared",
                                "compared_fraction": 0.0}},
                  open("conformance.json", "w"), indent=1)
        return 2
    runtime = RUNTIME[lang]
    is_c = (lang == "c")
    want_dialect, exact = DIALECT_FOR[lang]
    missing = missing_tools(lang)
    print("language: %s (%s) -> runtime %s%s"
          % (lang, ", ".join("%s x%d" % (e, n) for e, n in sorted(exts.items())),
             runtime, "" if not missing else "  [MISSING: %s]" % ", ".join(missing)))
    if not exact:
        print("  dialect note: Core has no %s-specific dialect yet (only .python, "
              ".cLike, .javascript exist), so %s runs under an approximation "
              "(java64/go64 NumConfigs exist but are unwired)." % (lang, lang))

    holefree = [f for f in funcs if not has_hole(f["body"])]
    # NOTE ON MEASUREMENT BASIS. `skip_varargs` used to exist here and was removed
    # deliberately: a `*args`/`**kwargs` callee binds a tuple and a dict, which Core
    # models exactly, so those calls are now *attempted* (bound positionally against
    # the AST's own parameter list) instead of skipped. That attempts far more and
    # lands more cases INCONCLUSIVE, so the conclusive denominator is not the same
    # denominator as before. Rates across the two bases are NOT comparable, and the
    # output says which basis produced it rather than leaving a reader to assume.
    stats = {"skip_unencodable_args": 0, "skip_unencodable_ret": 0,
             "skip_no_instance": 0, "test_runs": []}
    BASIS = "varargs-attempted-v2"
    BASIS_NOTE = ("Basis %s: `*args`/`**kwargs` callees are bound (tuple/dict) and "
                  "attempted rather than skipped; container subclasses and object dict "
                  "keys are refused; only adjudicated cases count in the denominator. "
                  "Rates from the earlier `varargs-skipped-v1` basis (e.g. 104/104) are "
                  "a different measurement and must not be compared." % "v2")

    if wasm_mode and is_c:
        # The denominator moves under `--wasm`: calls where native and wasm-clang
        # disagree are withheld from the Lean comparison and counted as `ub-suspected`
        # instead. That is a DIFFERENT measurement from the native-only C basis, and it
        # says so rather than letting a reader assume the rates line up.
        BASIS = "c-dual-oracle-v3"
        BASIS_NOTE = (
            "Basis c-dual-oracle-v3: C is executed under BOTH native `cc` and a "
            "freestanding wasm32 build, on identical inputs. Calls where the two "
            "conforming implementations return different values are recorded as "
            "`ub-suspected` and WITHHELD from the Lean comparison -- Core maps UB to "
            "`Expr.hole` (`NumResult.ub`), so scoring those against Lean would penalise "
            "the semantics for being correct. The conclusive denominator therefore "
            "excludes them and is NOT comparable to the native-only C basis. Arguments "
            "are additionally drawn from a boundary-biased pool (INT_MIN/INT_MAX, shift "
            "counts >= 32) rather than only randint(-20, 20), so the inputs differ from "
            "the native-only basis as well. Two separate categories are reported and "
            "NOT counted as UB: `width-sensitive` (functions using `long`/`size_t`, "
            "which are 32-bit on wasm32 and 64-bit natively) and `excluded_from_ub` "
            "(pointer returns and results unstable across two identical native calls).")

    # cases: dict(name, heap, self, args, outcome, origin)
    cases = []
    C_WASM_REPORT = []      # filled by the C backend below; surfaced in conformance.json

    backend_info, backend_skipped, backend_status = {}, {}, "available"
    if missing:
        backend_status = "UNSUPPORTED: toolchain absent (%s)" % ", ".join(missing)
        print("  backend UNSUPPORTED: %s not on PATH — this language has NO runtime "
              "check, which is a gap in the evidence, not a pass." % ", ".join(missing))
    elif lang in ("java", "go", "js", "ts"):
        if lang == "java":
            cases, backend_info, backend_skipped = java_backend(src_root, holefree,
                                                                ncases)
        elif lang == "go":
            cases, backend_info, backend_skipped = go_backend(src_root, holefree,
                                                              ncases)
        else:
            cases, backend_info, backend_skipped = node_backend(src_root, holefree,
                                                                ncases, lang)
        if not cases:
            backend_status = ("UNSUPPORTED: no testable surface — "
                              + str(backend_info.get("note", backend_info)))
        print("  backend %s: %s; %d cases built"
              % (runtime, json.dumps(backend_info)[:160], len(cases)))
    elif lang == "kotlin":
        backend_status = "UNSUPPORTED: no kotlinc"
    elif is_c:
        cget = c_runtime(src_root)
        cands = [f for f in holefree
                 if f["params"] and re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', f["name"])]
        # Fix the argument vectors up front so the native and wasm runs see EXACTLY the
        # same inputs. Generating them twice from the same seeded RNG would drift the
        # moment either side skips a function, and a cross-implementation comparison on
        # mismatched inputs is worse than none: it manufactures disagreements.
        # Under `--wasm` the arguments are drawn from a boundary-biased pool as well as
        # the small range. `randint(-20, 20)` can never trigger the behaviour this
        # oracle exists to find: signed overflow needs operands near INT_MAX, and
        # shift-past-width needs a count >= 32. Searching for UB with inputs that cannot
        # produce it and reporting "none found" would be an empty result dressed as a
        # clean one. This widens what is attempted, which is part of why the basis
        # changes.
        UB_POOL = [0, 1, -1, 2, 3, 7, 8, 16, 31, 32, 33, 63, 64, 65,
                   255, 256, 65535, 65536, 1 << 20,
                   (1 << 31) - 1, -(1 << 31), (1 << 31) - 2, -(1 << 31) + 1,
                   (1 << 30), -(1 << 30), 0x55555555 - (1 << 32), 0x7ffffffe]

        def c_arg():
            if wasm_mode and random.random() < 0.55:
                return random.choice(UB_POOL)
            return random.randint(-20, 20)

        plan = []
        for f in cands:
            for _ in range(ncases):
                plan.append((f, [c_arg() for _ in f["params"]]))

        # ---- native leg (the existing `cc` backend)
        native, native2 = {}, {}
        for k, (f, args) in enumerate(plan):
            fn = cget(f["name"], len(f["params"])) if cget else None
            if fn is None: continue
            # The AST carries no C types, so an `int` we pass may be a pointer
            # parameter. On a real corpus (`sds`) that segfaults and takes the whole
            # harness with it, so each call runs in a forked child: a crash costs
            # one case, not the run.
            if wasm_mode:
                # Two invocations, so the UB oracle can tell an allocation-dependent
                # result (a fresh pointer each call) from a stable computed value.
                native[k], native2[k] = call_in_child_twice(fn, args)
            else:
                native[k] = call_in_child(fn, args)

        # ---- wasm leg (sandbox + second implementation)
        wres, wasm_report = {}, None
        if wasm_mode:
            tc = wasm_backend.toolchain()
            if not tc["ok"]:
                # LOUD. A missing toolchain is a gap in the evidence; it must never be
                # allowed to look like a clean run with nothing to report.
                wasm_report = {"status": "UNSUPPORTED: no wasm toolchain",
                               "reason": tc["reason"]}
                print("  wasm UNSUPPORTED: %s — the sandbox and the UB oracle did NOT "
                      "run. This is a missing check, not a pass." % tc["reason"])
            else:
                wdir = os.path.join(WORK, "wasm"); os.makedirs(wdir, exist_ok=True)
                srcs = glob.glob(os.path.join(src_root, "**", "*.c"), recursive=True)
                wpath, winfo = wasm_backend.compile_wasm(srcs, wdir, tc)
                if wpath is None:
                    wasm_report = {"status": "UNSUPPORTED: wasm build failed",
                                   "reason": winfo.get("error"), "build": winfo}
                    print("  wasm UNSUPPORTED: %s" % winfo.get("error"))
                else:
                    caller = wasm_backend.WasmCaller(wpath, tc, wdir)
                    wres = caller.run([{"id": k, "name": f["name"], "args": a}
                                       for k, (f, a) in enumerate(plan)])
                    wasm_report = {"status": "ran", "toolchain": tc, "build": winfo}

        # ---- adjudicate the two C implementations against each other
        wtally, ub_findings, trap_detail, excluded = {}, [], {}, []
        width_findings = []
        width_fns = (wasm_backend.width_sensitive_functions(src_root)
                     if wasm_mode and wres else set())
        for k, (f, args) in enumerate(plan):
            nat = native.get(k)
            if wasm_mode and wres:
                kind, det = wasm_backend.adjudicate(nat, wres.get(k),
                                                    native2.get(k))
                wtally[kind] = wtally.get(kind, 0) + 1
                if kind in ("address-valued", "nondeterministic"):
                    # Recorded, not hidden: these differ for a reason the harness can
                    # point at (two address spaces / an unstable native result), so
                    # they are neither UB evidence nor a fair Lean comparison.
                    if len(excluded) < 40:
                        excluded.append(dict(function=f["name"], args=args,
                                             why=kind, **det))
                    continue
                if kind == "trap":
                    tk = "%s: %s" % (f["name"], det.get("kind"))
                    trap_detail[tk] = trap_detail.get(tk, 0) + 1
                if kind == "ub-suspected":
                    ws = f["name"] in width_fns
                    if ws:
                        # Fully defined on both targets, just computed at different
                        # widths. Retallied so the UB headline stays honest.
                        wtally["ub-suspected"] -= 1
                        wtally["width-sensitive"] = wtally.get("width-sensitive", 0) + 1
                    (width_findings if ws else ub_findings).append({
                        "function": f["name"], "args": args,
                        "native": det["native"], "wasm": det["wasm"],
                        "width_sensitive": ws,
                        "reading": wasm_backend.classify_ub(f["name"], args,
                                                            det["native"], det["wasm"]),
                        "reading_is_a_hint": True})
                    # NOT a conformance divergence. Core maps UB to `Expr.hole`
                    # (`NumResult.ub`), so where two conforming C implementations
                    # disagree the hole is the CORRECT answer -- scoring this against
                    # Lean would penalise the semantics for being right. The case is
                    # withheld from the Lean comparison and counted in its own
                    # category, which is why the measurement basis changes below.
                    continue
            if nat is None:
                stats["skip_c_crash"] = stats.get("skip_c_crash", 0) + 1
                continue
            cases.append({"name": f["name"], "heap": [], "self": None,
                          "args": [("int", a) for a in args],
                          "outcome": ("val", ("int", nat)), "origin": "random",
                          "objs": {}})
        if wasm_report is not None:
            wasm_report.update(calls_planned=len(plan), tally=wtally,
                               trap_detail=dict(sorted(trap_detail.items(),
                                                       key=lambda kv: -kv[1])[:30]),
                               ub_suspected=len(ub_findings),
                               ub_findings=ub_findings[:60],
                               width_sensitive=len(width_findings),
                               width_findings=width_findings[:40],
                               width_note=(
                                   "Native/wasm disagreements in functions that use a "
                                   "pointer-width type (`long`, `size_t`, ...). wasm32 "
                                   "makes those 32-bit and the native build 64-bit, so "
                                   "these differ WITHOUT undefined behaviour -- it is "
                                   "the NumConfig width axis `Core/Numeric.lean` "
                                   "models. Kept out of `ub_suspected` so that number "
                                   "means what it says."),
                               excluded_from_ub=excluded,
                               excluded_note=(
                                   "Native/wasm value differences the harness can "
                                   "attribute to something other than the program's "
                                   "semantics: a pointer return (two address spaces) "
                                   "or a native result that is not stable across two "
                                   "identical calls. Counted here rather than in "
                                   "`ub_suspected`, and withheld from the Lean "
                                   "comparison, because neither number answers the "
                                   "same question."))
            if wasm_report["status"] == "ran" and not wtally:
                wasm_report["status"] = ("SKIPPED: wasm built but zero calls were "
                                         "comparable — nothing was checked")
            print("  wasm: %s; %d calls, tally %s, %d ub-suspected"
                  % (wasm_report["status"], len(plan), json.dumps(wtally),
                     len(ub_findings)))
            C_WASM_REPORT.append(wasm_report)
    elif lang == "python":
        wanted, methods, modlevel = set(), [], []
        for f in holefree:
            c = classify(f)
            if not c: continue
            rel, qual, is_meth = c
            wanted.add(f["name"])
            (methods if is_meth else modlevel).append((f, rel, qual))

        # (1) the repository's own test suite — the highest-value source of arguments
        rel_files = sorted(set(f.get("file", "") for f in funcs))
        src_root = resolve_src_root(src_root, rel_files)
        test_dirs = [tests_override] if tests_override else find_tests(src_root)
        index = build_lineno_index(src_root, rel_files)
        traced = []
        params_by_name = {f["name"]: f["params"] for f in holefree}
        live, pool = {}, {}
        if test_dirs and index:
            print("test suite: %s" % ", ".join(test_dirs))
            traced = trace_tests(src_root, test_dirs, index, wanted, ncases, stats,
                                 params_by_name, live, pool)
        elif not test_dirs:
            print("test suite: none discovered under %s (pass --tests DIR)" % src_root)
        else:
            print("test suite: %s found, but none of the AST's source files resolve "
                  "under %s — nothing to instrument" % (", ".join(test_dirs), src_root))
        for r in traced:
            r["origin"] = "test-suite"
            cases.append(r)
        print("cases recorded from the test suite: %d" % len(traced))
        if test_dirs and not traced:
            print("  (the suite produced no usable calls — if it failed to even "
                  "collect, try re-running this harness under the interpreter the "
                  "project supports, e.g. `python3.11 scripts/differential.py ...`)")

        # (2) random integers for module-level functions (supplement, not substitute)
        for f, rel, qual in modlevel:
            mod = load_module(os.path.join(src_root, rel), src_root)
            if mod is None or not hasattr(mod, qual): continue
            fn = getattr(mod, qual)
            for _ in range(ncases):
                args = [random.randint(-20, 20) for _ in f["params"]]
                enc = Encoder()
                enc.freeze()
                try:
                    got = fn(*args)
                    out = ("val", enc.enc_result(got))
                except Unencodable:
                    stats["skip_unencodable_ret"] += 1; continue
                except Exception as e:                      # noqa: BLE001
                    out = ("exn", type(e).__name__)
                cases.append({"name": f["name"], "heap": enc.heap, "self": None,
                              "args": [("int", a) for a in args], "outcome": out,
                              "origin": "random"})

        # (3) methods the suite never called: reuse an instance it built for a
        # sibling method, or build one, and synthesize arguments from observed values
        reached = set(c["name"] for c in cases)
        built = constructed_cases(methods, reached, live, pool, stats, ncases)
        cases += built
        print("cases constructed for methods the suite never called: %d (%d functions)"
              % (len(built), len(set(c["name"] for c in built))))
        reached = set(c["name"] for c in cases)
        stats["skip_no_instance"] = sum(1 for f, _, _ in methods
                                        if f["name"] not in reached)

    if len(cases) > MAX_TOTAL_CASES:
        random.shuffle(cases)
        cases = cases[:MAX_TOTAL_CASES]

    result = {"module": module_tag, "source_root": os.path.abspath(src_root),
              "ast": os.path.abspath(ast_path), "runtime": runtime,
              "runtime_version": sys.version.split()[0],
              "measurement_basis": BASIS, "measurement_basis_note": BASIS_NOTE,
              "language": lang, "extensions": exts,
              "backend": runtime, "backend_status": backend_status,
              "backend_info": backend_info,
              "backend_skipped": dict(list(backend_skipped.items())[:40]),
              "backend_skipped_total": len(backend_skipped),
              # The wasm leg is a SEPARATE ORACLE, reported alongside the Lean
              # comparison rather than folded into it. `ub_suspected` counts programs
              # two conforming C compilers disagree about; those are evidence about the
              # program under test, not about our semantics.
              "wasm_c_oracle": (C_WASM_REPORT[0] if C_WASM_REPORT else
                                ({"status": "not requested (pass --wasm)"} if is_c
                                 else {"status": "n/a: not a C corpus"})),
              "dialect_expected": want_dialect,
              "dialect_is_exact": exact,
              "dialect_note": (None if exact else
                               "Core has only .python and .cLike; %s is run under an "
                               "approximation. A divergence may be a dialect gap rather "
                               "than a transpiler fault." % lang),
              # PROVENANCE. `functions_covered` is built from tracing the corpus's own
              # test suite, so it moves when the CHECKOUT moves -- and a coverage number
              # that silently tracks an unpinned `--depth 1` clone is the same trap as a
              # metric computed from the artifact it describes. Two runs of this harness
              # reported 107 and 82 covered functions with identical harness code, an
              # identical AST and an identical seed; the only free variable was the
              # checkout. Record it, so the next such gap is a diff and not an argument.
              "corpus_commit": _corpus_commit(src_root),
              "functions_total": len(funcs), "functions_hole_free": len(holefree),
              "functions_covered": len(set(c["name"] for c in cases)),
              "cases": len(cases), "agree": 0, "total": 0, "divergences": 0,
              "inconclusive": 0, "rate": "n/a", "by_origin": {},
              "skipped": {k: v for k, v in stats.items() if k.startswith("skip")},
              "skipped_note": "call-event counts, not function counts: a function whose "
                              "case quota is already full still logs skips for every "
                              "further call. Bound coverage with `coverage`, never with "
                              "these.",
              "test_runs": stats["test_runs"], "divergence_detail": [],
              "unencodable_reasons": stats.get("unencodable_reasons", {}),
              "no_instance_detail": stats.get("no_instance_detail", {}),
              "param_mismatch_detail": stats.get("param_mismatch_detail", {}),
              "coverage": {
                  # `covered_metric` names the field a coverage-bounded claim should
                  # read. `compared` is the strong one: functions with at least one
                  # case the oracle actually adjudicated. `exercised` merely means a
                  # case was built, which an inconclusive outcome does not vindicate.
                  "population": len(funcs),
                  "population_kind": "functions in %s" % os.path.basename(ast_path),
                  "hole_free": len(holefree),
                  "exercised": len(set(c["name"] for c in cases)),
                  "compared": 0,
                  "covered_metric": "compared",
                  "compared_fraction": 0.0,
                  "exercised_fraction": (len(set(c["name"] for c in cases))
                                         / len(funcs)) if funcs else 0.0,
                  "compared_fraction_of_hole_free": 0.0,
                  "by_status": {}, "status_counts": {}}}

    if not cases:
        print("module %s (%s, %s): NO COMPARABLE CASES — %s"
              % (module_tag, lang, runtime, backend_status))
        print("functions: %d total, %d hole-free, 0 exercised, 0 COMPARED (0%%). This "
              "language has no positive runtime evidence." % (len(funcs), len(holefree)))
        json.dump(result, open("conformance.json", "w"), indent=1)
        return 0

    # ---- ask Lean for its answer on exactly those cases
    #
    # Evaluated in chunks with bisection on failure: a single case can bring the whole
    # Lean interpreter down (a stale generated module, an unimplemented constructor),
    # and losing an entire run to one bad case would be a false negative. Cases we
    # cannot get an answer for are INCONCLUSIVE, never agreement.
    env = dict(os.environ,
               PATH=os.path.expanduser("~/.elan/bin") + ":" + os.environ["PATH"])
    repo = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    # A stale `.olean` silently answers with the *previous* semantics — which shows up
    # as fictitious divergences. Rebuild the module before trusting anything it says.
    b = subprocess.run(["lake", "build", "Autoform.Generated.%s" % lean_mod],
                       capture_output=True, text=True, env=env, cwd=repo)
    if b.returncode != 0:
        print("WARNING: `lake build Autoform.Generated.%s` failed; results below are "
              "against a possibly stale build:\n%s" % (lean_mod, b.stderr[:300]))
    gen = os.path.join(repo, "Autoform", "Generated", lean_mod + ".lean")
    # `scripts/mutate.py` edits the generated module in place and keeps the pristine
    # copy beside it. If that backup exists, the module under test is currently a
    # MUTANT: its divergences are injected faults, not evidence about the semantics.
    mutating = os.path.exists(gen + ".mutate-backup")
    result["mutation_in_progress"] = mutating
    if mutating:
        print("WARNING: %s.mutate-backup exists — a mutation run owns this module right "
              "now, so it is a MUTANT. Any divergence below is an injected fault; this "
              "run is not conformance evidence." % os.path.basename(gen))
    has_inits = (os.path.exists(gen)
                 and "def moduleInits" in open(gen, encoding="utf-8").read())
    inits = "moduleInits" if has_inits else "([] : List Func)"

    # Module-level bindings (`Stmt.setGlobal` / `Expr.closure`) only exist after the
    # module initializers have run, so we start from `initGlobals` rather than the empty
    # heap. The globals frame occupies ref 0, so every receiver object the harness
    # materialises must be allocated at `base = h0.length` and upward; all `Val.ref`
    # literals below are emitted relative to `base`. `drun` re-checks that arithmetic
    # against the class name Python recorded — an off-by-one that aliased the globals
    # frame would otherwise be silently wrong rather than loudly wrong.
    # Isolate the run from the rest of the project: copy the compiled `Autoform`
    # artifacts to a private directory and resolve imports from there first. Other
    # agents build — and `scripts/mutate.py` deliberately *mutates* — the same generated
    # module while this runs, and evaluating against a moving target produced phantom
    # divergences that reproduced nowhere (`Cache.__contains__` inverted,
    # `_DefaultSize.pop` returning 0: both were live mutants).
    snap_dir = os.path.join(WORK, "lean-snapshot")
    lean_env = dict(env)
    try:
        import shutil
        shutil.rmtree(snap_dir, ignore_errors=True)
        os.makedirs(snap_dir, exist_ok=True)
        blib = os.path.join(repo, ".lake/build/lib/lean")
        shutil.copytree(os.path.join(blib, "Autoform/Lang"),
                        os.path.join(snap_dir, "Autoform/Lang"))
        os.makedirs(os.path.join(snap_dir, "Autoform/Generated"), exist_ok=True)
        for ext in (".olean", ".ilean"):
            src_f = os.path.join(blib, "Autoform/Generated", lean_mod + ext)
            if os.path.exists(src_f):
                shutil.copy(src_f, os.path.join(snap_dir, "Autoform/Generated"))
        base = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"],
                              capture_output=True, text=True, env=env, cwd=repo)
        lean_env["LEAN_PATH"] = snap_dir + ":" + base.stdout.strip()
        isolated = True
    except (OSError, shutil.Error) as e:                    # noqa: BLE001
        print("could not isolate the build (%s); evaluating against the live tree" % e)
        isolated = False

    header = ["import Autoform.Generated.%s" % lean_mod,
              # Each corpus owns its namespace (`Autoform.Generated.Cachetools.program`,
              # ...) so that proofs about two codebases can share an import graph. Opening
              # the parent only was silently fatal here: `program` did not resolve, the
              # generated harness failed to compile, and EVERY case came back
              # `lean-no-answer` -- 534 of 534 on cachetools, reported as INCONCLUSIVE
              # rather than as a broken harness. Conformance is not in CI, so nothing
              # caught it.
              "open Autoform.Core Autoform.Generated Autoform.Generated.%s" % lean_mod, "",
              "private def gp : Heap × Ref := initGlobals program %d %s" % (FUEL, inits),
              "private def h0 : Heap := gp.1",
              "private def gref : Ref := gp.2",
              "private def base : Nat := h0.length",
              # `builtinBases` must be carried, or `Expr.alloc` cannot know that
              # `class _HashedTuple(tuple)` has a builtin base and produces a plain
              # `Val.ref` instead of a `Val.bobj`. The oracle then reports
              # `representation:value-vs-object` and counts the case INCONCLUSIVE -- the
              # harness refusing to look at a value Core was fixed to produce correctly,
              # because the harness dropped the field on the way in.
              "private def dctx : Ctx := "
              "{ dialect := program.dialect, table := program.table, globals := gref, "
              "builtinBases := program.builtinBases }",
              "",
              "private structure DCase where",
              "  idx  : Nat",
              "  objs : List Obj",
              "  fn   : String",
              "  slf  : Option Val",
              "  args : List Val",
              "  chk  : List (Nat × String)", "",
              # A boxed function object (Core section 47) is REPORTED AS THE FUNCTION IT
              # CARRIES. `wrapper.cache_clear = f` makes `wrapper` a heap object, and Core
              # returns a `Val.ref` to it where CPython returns the function -- a shape
              # clash, not a disagreement. This is the same move `unwrap_bobj` makes on the
              # Python side, and it hides the same thing: object identity and the attributes
              # written to it. Neither side's test compares those here; if one ever does,
              # this has to compare them rather than unbox.
              "private def unboxRes (h : Heap) (r : EResult) : EResult :=",
              "  match r with",
              "  | .val (.ref a) => match unboxFn h a with",
              "                     | some fv => .val fv",
              "                     | none    => r",
              "  | _ => r", "",
              "private def drun (c : DCase) : EResult :=",
              "  let h := h0 ++ c.objs",
              "  -- the globals frame must survive, and each receiver must land where",
              "  -- the harness said it would",
              "  if (h.get gref).map (·.cls) != some \"<globals>\" then",
              "    .hole \"harness:globals-frame-clobbered\"",
              "  else if c.chk.any (fun p => (h.get (base + p.1)).map (·.cls) "
              "!= some p.2) then",
              "    .hole \"harness:receiver-alias\"",
              "  else",
              "    match dctx.resolve c.fn with",
              '    | none    => .hole s!"entry:{c.fn}"',
              # `applyFunc` gained a `kws` parameter when Python's calling convention was
              # modelled. This call site kept five arguments, so `drun` failed to elaborate
              # -- but the `@@meta@@` line above it only mentions `base`/`gref` and still
              # printed, so the harness saw a live Lean process and reported every case as
              # `lean-no-answer`. An arity change silently disabled the only oracle that
              # compares the semantics to a real runtime.
              "    | some fn => let r := applyFunc dctx %d h fn c.slf c.args []" % FUEL,
              "                 unboxRes r.1 r.2", ""]
    footer = ["]", "",
              '#eval IO.println ("@@meta@@" ++ toString base ++ " " ++ toString gref)',
              '#eval cases.forM (fun c => IO.println ("@@" ++ toString c.idx ++ "@@" '
              '++ (repr (drun c)).pretty (width := 1000000)))']

    def case_lit(i, c):
        slf = "none" if c["self"] is None else "(some (%s))" % lean_val(c["self"])
        chk = ", ".join('(%d, %s)' % (k, json.dumps(cls))
                        for k, (cls, _) in enumerate(c["heap"]))
        return ("  { idx := %d, objs := %s, fn := %s, slf := %s, args := [%s], "
                "chk := [%s] }"
                % (i, lean_heap(c["heap"]), json.dumps(c["name"]), slf,
                   ", ".join(lean_val(a) for a in c["args"]), chk))

    meta = {"base": 0, "gref": 0}
    # per-process scratch file: two harness runs (or two agents) sharing /tmp would
    # otherwise clobber each other's generated file mid-bisection
    scratch = os.path.join(WORK, "harness.lean")

    def lean_eval(idxs, depth=0, retried=False):
        """idxs -> {idx: repr line}. Missing keys are cases Lean could not answer."""
        if not idxs: return {}
        src = header + ["private def cases : List DCase := ["] \
            + [",\n".join(case_lit(i, cases[i]) for i in idxs)] + footer
        open(scratch, "w").write("\n".join(src) + "\n")
        if isolated:
            out = subprocess.run([os.path.expanduser("~/.elan/bin/lean"), scratch],
                                 capture_output=True, text=True, env=lean_env, cwd=repo)
        else:
            out = subprocess.run(["lake", "env", "lean", scratch],
                                 capture_output=True, text=True, env=env, cwd=repo)
        got = {}
        saw_meta = False
        for l in out.stdout.splitlines():
            m = re.match(r'@@meta@@(\d+) (\d+)', l)
            if m:
                meta["base"], meta["gref"] = int(m.group(1)), int(m.group(2))
                saw_meta = True
                continue
            m = re.match(r'@@(\d+)@@(.*)', l)
            if m and int(m.group(1)) in idxs: got[int(m.group(1))] = m.group(2)
        if not saw_meta:
            # PRINT THE REASON. Without this the whole oracle fails as "534 INCONCLUSIVE
            # (lean-no-answer)", which is indistinguishable from "the semantics could not
            # decide" -- an oracle that cannot run looks exactly like an oracle that ran
            # and abstained. That is how a namespace change disabled conformance entirely
            # while every other gate stayed green.
            first = (out.stderr or out.stdout or "").strip().splitlines()
            if first:
                print("  lean did not reach the first case (rc=%s): %s"
                      % (out.returncode, first[0][:200]))
        if not saw_meta and not retried:
            # No `@@meta@@` line: the file never reached the first case, so this is a
            # compile or environment failure, not a bad case. That happens for real —
            # another process rebuilding `Semantics.olean` removes it mid-run — so
            # rebuild and try once more before giving up on the whole chunk.
            subprocess.run(["lake", "build", "Autoform.Generated.%s" % lean_mod],
                           capture_output=True, text=True, env=env, cwd=repo)
            if isolated:
                import shutil
                blib = os.path.join(repo, ".lake/build/lib/lean")
                shutil.rmtree(os.path.join(snap_dir, "Autoform"), ignore_errors=True)
                shutil.copytree(os.path.join(blib, "Autoform/Lang"),
                                os.path.join(snap_dir, "Autoform/Lang"))
                os.makedirs(os.path.join(snap_dir, "Autoform/Generated"),
                            exist_ok=True)
                for ext in (".olean", ".ilean"):
                    f2 = os.path.join(blib, "Autoform/Generated", lean_mod + ext)
                    if os.path.exists(f2):
                        shutil.copy(f2, os.path.join(snap_dir, "Autoform/Generated"))
            return lean_eval(idxs, depth, retried=True)
        if not saw_meta:
            # Bisecting an environment failure costs one lake invocation per case and
            # answers nothing.
            if depth == 0 or not meta.get("env_reported"):
                meta["env_reported"] = True
                print("lean environment failure, not bisecting:",
                      (out.stdout[:200] + " " + out.stderr[:300]).replace("\n", " ")[:300])
            return got
        if len(got) < len(idxs) and len(idxs) == 1 and os.environ.get(
                "AUTOFORM_DIFF_KEEP"):
            # debugging aid: keep the exact file the interpreter choked on
            import shutil
            keep = os.environ["AUTOFORM_DIFF_KEEP"]
            os.makedirs(keep, exist_ok=True)
            shutil.copy(scratch, os.path.join(keep, "fail_%d.lean" % idxs[0]))
        if len(got) < len(idxs) and len(idxs) > 1:
            mid = len(idxs) // 2
            got.update(lean_eval(idxs[:mid], depth + 1))
            got.update(lean_eval(idxs[mid:], depth + 1))
        elif len(got) < len(idxs) and depth == 0:
            print("lean could not evaluate any case:",
                  (out.stdout[:200] + out.stderr[:400]).replace("\n", " ")[:400])
        return got

    def olean_fingerprint():
        """Identify the compiled artifacts the answers actually came from.

        STRATEGY.md §19: a stale `.olean` answers with the *previous* semantics. That
        can also happen *during* a run — another process rebuilding `Semantics` while
        the chunks are being evaluated — and it produced a phantom divergence
        (`_DefaultSize.pop` returning 0 instead of 1) that reproduced nowhere
        afterwards. So fingerprint the artifacts and re-run if they moved."""
        import hashlib
        h = hashlib.sha256()
        root = snap_dir if isolated else os.path.join(repo, ".lake/build/lib/lean")
        for p in (os.path.join(root, "Autoform/Lang/Core/Semantics.olean"),
                  os.path.join(root, "Autoform/Generated", lean_mod + ".olean")):
            try:
                h.update(open(p, "rb").read())
            except OSError:
                h.update(b"<missing>")
        return h.hexdigest()

    CHUNK = 20
    order = list(range(len(cases)))
    got, stable = {}, False
    for attempt in range(3):
        before = olean_fingerprint()
        got = {}
        for i in range(0, len(order), CHUNK):
            got.update(lean_eval(order[i:i + CHUNK]))
        if olean_fingerprint() == before:
            stable = True; break
        print("WARNING: the compiled Lean artifacts changed while the cases were being "
              "evaluated (a concurrent build). Discarding and re-running.")
    result["build_stable"] = stable and not mutating
    if not stable or mutating:
        print("WARNING: results below were produced against a moving or mutated build "
              "and must not be treated as conformance evidence (build_stable=false).")
    if len(got) < len(cases):
        print("lean answered %d/%d cases; the rest are INCONCLUSIVE"
              % (len(got), len(cases)))

    agree = diverge = incon = 0
    compared_fns = set()          # functions the oracle actually adjudicated
    incon_detail: dict = {}
    per_origin = {}
    for i, c in enumerate(cases):
        origin = c.get("origin", "?")
        bucket = per_origin.setdefault(origin, {"agree": 0, "diverge": 0, "incon": 0})
        line = got.get(i)
        if line is None:
            incon += 1; bucket["incon"] += 1
            k = "%s: lean-no-answer (interpreter failed on this case)" % c["name"]
            incon_detail[k] = incon_detail.get(k, 0) + 1
            continue
        try:
            lr = parse_result(line)
        except Exception:                                  # noqa: BLE001
            incon += 1; bucket["incon"] += 1
            print("  unparsable %s: %s" % (c["name"], line[:80]))
            continue
        py = c["outcome"]
        argstr = "(%s)" % ", ".join(show(a) for a in c["args"])
        if lr[0] in ("hole", "outOfFuel"):
            # ignorance is never agreement
            incon += 1; bucket["incon"] += 1
            label = lr[1] if lr[0] == "hole" else "outOfFuel"
            k = "%s: %s" % (c["name"], label)
            incon_detail[k] = incon_detail.get(k, 0) + 1
            continue
        ok = False
        undecidable = None
        if py[0] == "val" and lr[0] == "val":
            # A value/object shape disagreement is not adjudicable: the transpiler
            # allocates a heap object for any constructed class (including subclasses
            # of tuple/dict), while the runtime hands us a container. The harness
            # cannot tell its own representation choice from a real disagreement, so
            # it declines to call it either way.
            if shape_clash(py[1], lr[1]):
                undecidable = "representation:value-vs-object"
            else:
                ok = same(py[1], lr[1], meta["base"])
            desc = "%s=%s lean=%s" % (runtime, show(py[1]), show(lr[1]))
        elif py[0] == "exn" and lr[0] == "exn":
            lname = lr[1][1] if lr[1][0] == "str" else show(lr[1])
            ok = (lname == py[1])
            if not ok and lr[1][0] != "str":
                # Core raised at the same point but carries no name for the class
                # (`raise NotImplementedError` evaluates a builtin it has no model of).
                # Control flow agrees; the payload is unmodelled, not wrong.
                undecidable = "exception-payload-unmodelled"
            desc = "%s raised %s, lean raised %s" % (runtime, py[1], lname)
        elif py[0] == "exn":
            desc = "%s raised %s, lean returned %s" % (runtime, py[1], show(lr[1]))
        else:
            lname = lr[1][1] if lr[1][0] == "str" else show(lr[1])
            desc = "%s=%s, lean raised %s" % (runtime, show(py[1]), lname)
        if undecidable is not None:
            incon += 1; bucket["incon"] += 1
            k = "%s: %s" % (c["name"], undecidable)
            incon_detail[k] = incon_detail.get(k, 0) + 1
            continue
        compared_fns.add(c["name"])
        if ok:
            agree += 1; bucket["agree"] += 1
        else:
            diverge += 1; bucket["diverge"] += 1
            msg = "  DIVERGENCE %s%s: %s [%s]" % (c["name"], argstr, desc, origin)
            print(msg[:300])
            result["divergence_detail"].append(
                {"function": c["name"], "args": argstr[:200], "detail": desc[:200],
                 "origin": origin,
                 # the exact inputs, so a divergence is a reproducible artifact rather
                 # than a line of prose
                 "case": {"self": c["self"], "args": c["args"],
                          "heap": json.loads(json.dumps(c["heap"]))[:6]},
                 "lean_repr": line[:400]})

    total = agree + diverge
    rate = "%d%%" % (100 * agree // total) if total else "n/a"
    # ---- coverage, as a first-class output: which functions the oracle actually
    # adjudicated, which it merely touched, and why the rest were out of reach.
    status = {}
    for f in funcs:
        status[f["name"]] = ("not-translated-fully (holes): untestable until translated"
                             if has_hole(f["body"]) else "hole-free, no case built")
    for c in cases:
        status[c["name"]] = "cases built, all inconclusive"
    for n in compared_fns:
        status[n] = "compared"
    for n, why in stats.get("no_instance_detail", {}).items():
        for f in funcs:
            if f["name"].endswith("." + n) and status.get(f["name"], "").startswith(
                    "hole-free"):
                status[f["name"]] = "hole-free, no case built: " + why
    # why each un-compared function is un-compared, split into the two categories that
    # matter for a coverage-bounded claim: gaps the project intends to close, and gaps
    # in the oracle's own value model that no amount of semantics work removes.
    VALUE_MODEL = ("float", "set", "opaque", "complex", "bytes", "frozenset",
                   "container-subclass", "object-as-dict-key", "wide",
                   "self-not-object", "representation")
    labels = {}
    for k, v in incon_detail.items():
        fn, lab = k.split(": ", 1)
        labels.setdefault(fn, set()).add(lab.split(":")[0])
    for f in funcs:
        n = f["name"]
        if n in compared_fns or has_hole(f["body"]): continue
        labs = labels.get(n, set())
        if labs and labs <= {"representation", "exception-payload-unmodelled"}:
            status[n] = "blocked (value model): " + ", ".join(sorted(labs))
        elif labs:
            status[n] = "blocked (semantics/transpiler): runtime holes " + \
                        ", ".join(sorted(labs))
        else:
            why = status.get(n, "")
            hit = [w for w in VALUE_MODEL if w in why]
            status[n] = ("blocked (value model): " + hit[0] if hit
                         else "blocked (unexercised): " + why.split(": ", 1)[-1])
    counts = {}
    for v in status.values():
        k = v.split(":")[0]
        counts[k] = counts.get(k, 0) + 1
    cov = result["coverage"]
    cov["compared"] = len(compared_fns)
    cov["compared_fraction"] = len(compared_fns) / len(funcs) if funcs else 0.0
    cov["compared_fraction_of_hole_free"] = (len(compared_fns) / len(holefree)
                                             if holefree else 0.0)
    cov["by_status"] = status
    cov["status_counts"] = counts
    perm = sum(v for k, v in counts.items() if k.startswith("blocked (value model)"))
    cov["ceiling"] = {
        "compared_now": len(compared_fns),
        "blocked_by_value_model": perm,
        "reachable_in_principle": len(funcs) - perm,
        "reachable_fraction": (len(funcs) - perm) / len(funcs) if funcs else 0.0,
        "note": "Blocked-by-value-model functions need a Core value the interpreter "
                "does not have (floats, sets, opaque C objects) — no transpiler work "
                "reaches them. Everything else is blocked by holes, either in the AST "
                "or hit at runtime, and becomes reachable as those close."}
    result["inconclusive_detail"] = incon_detail
    result.update(agree=agree, total=total, divergences=diverge, inconclusive=incon,
                  rate=rate, by_origin=per_origin)
    print("\nmodule %s (%s, %s)" % (module_tag, os.path.abspath(src_root), runtime))
    print("measurement basis: %s" % BASIS)
    print("functions: %d total, %d hole-free, %d exercised, %d COMPARED (%.0f%% of "
          "all, %.0f%% of hole-free)"
          % (len(funcs), len(holefree), result["functions_covered"],
             len(compared_fns), 100 * result["coverage"]["compared_fraction"],
             100 * result["coverage"]["compared_fraction_of_hole_free"]))
    print("conformance: %d/%d agree (%s) vs %s, %d divergences, %d INCONCLUSIVE "
          "(hole / outOfFuel / unrepresentable)" % (agree, total, rate, runtime,
                                                    diverge, incon))
    for k, v in sorted(incon_detail.items(), key=lambda kv: -kv[1])[:10]:
        print("  INCONCLUSIVE x%-3d %s" % (v, k))
    for o, b in sorted(per_origin.items()):
        print("  by origin %-11s agree %d, diverge %d, inconclusive %d"
              % (o, b["agree"], b["diverge"], b["incon"]))
    if stats["skip_no_instance"]:
        print("  skipped %d hole-free methods: no instance reached by the test suite"
              % stats["skip_no_instance"])
    for k, v in result["skipped"].items():
        if v: print("  skipped %s: %d" % (k, v))
    json.dump(result, open("conformance.json", "w"), indent=1)
    if isolated:
        import shutil
        shutil.rmtree(snap_dir, ignore_errors=True)
    return 1 if diverge else 0


def _run_on_a_big_stack(fn):
    """Run `fn` on a thread with a large stack and a raised recursion limit.

    `json.load` is recursive, and the neutral AST nests as deeply as the source does.
    Ansible's AST blew Python's 1000-frame default *while decoding*, so conformance could
    not run on the largest Python corpus at all -- and the traceback pointed at the JSON
    decoder, which reads as "the file is corrupt" rather than "this program is deeply
    nested".

    This is the third instance of the same defect in this repository: `render_lean.py`
    never set a limit and died at 247 consecutive statements, `has_hole` was recursive and
    raised before any backend ran, and now the decoder itself. Raising the limit alone is
    not enough -- the limit guards the C stack, so lifting it without a bigger stack turns
    a clean exception into a segfault.
    """
    import threading
    sys.setrecursionlimit(300_000)
    try:
        threading.stack_size(512 * 1024 * 1024)
    except (ValueError, RuntimeError):
        try:
            threading.stack_size(64 * 1024 * 1024)
        except (ValueError, RuntimeError):
            pass
    box = {}

    def go():
        try:
            box["rc"] = fn()
        except BaseException as e:          # noqa: BLE001 - re-raised on the caller
            box["exc"] = e

    t = threading.Thread(target=go)
    t.start()
    t.join()
    if "exc" in box:
        raise box["exc"]
    return box.get("rc", 0)


if __name__ == "__main__":
    sys.exit(_run_on_a_big_stack(main))
