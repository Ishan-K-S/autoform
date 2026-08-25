#!/usr/bin/env python3
"""Layer 4 — automatic specification synthesis (STRATEGY.md §4).

Every specification about translated code in this repository is hand-written today, which
does not scale past a demo. This script generates them, working *down* §4's list of
sources by descending trustworthiness rather than jumping to invention:

  1. **Existing artifacts** — docstrings carried through the AST, `assert`/`raise` guards,
     doctests, and above all the repository's own test suite, whose executions are
     recorded by `scripts/differential.py`'s trace hook. §15 measured that a repo's own
     property-based tests are the highest-yield source; here the suite plays that role,
     and the outcome CPython produced for each recorded call is a fact this system did
     not manufacture.
  2. **Structural / safety specs, free for all code** — for a function in the call-closed
     core, "on this domain the interpreter returns a value, never `.hole` and never
     `.outOfFuel`" is a real, provable, non-trivial property: `Refine.lean`'s `Outcome`
     has no constructor for either.
  3. **Algebraic laws mined from behaviour** — constancy, projection, identity,
     idempotence, involutivity, commutativity, range bounds, heap purity. Mined from
     observed executions, then *pruned by a refutation pass* over a fuzzed domain before
     anything is emitted.
  4. **Cross-implementation equivalence** — the conformance family: the Lean interpreter
     reproduces what CPython did, stated as a kernel-checked theorem rather than a test
     report.

## The non-negotiable part

§15 measured that **41% of FVSpec's 9,415 LLM-transpiled specs are vacuous** under static
screening, dominated by determinism properties (`f(x) == f(x)`) that become `rfl` in a
pure setting. This generator is built so that it can be measured the same way and report
the number honestly:

* every candidate is **refuted before it is emitted** — mined laws are evaluated over a
  fuzzed domain in the Lean semantics, and a single counterexample drops the candidate;
* every survivor passes a **vacuity screen** with the same check names §15 used
  (`reflexive_conclusion`, `trivial_conclusion`, `empty_quantification`,
  `dependency_vacuity`, `opaque_subject`), and the flagged fraction is reported as *this
  generator's own vacuity rate*;
* a `Deterministic` family is mined deliberately and then rejected in full, so the number
  §15 found dominant is measured here rather than assumed absent;
* nothing is admitted. Statements that cannot be proved are emitted as `Prop`-valued
  `def`s plus `OpenObligation` records. There is no `sorry` anywhere — `scripts/audit_all.py`
  audits for it.

Both anti-vacuity gates run on the output: the emitted module ends with `#audit_depends`
for every theorem (so a statement that never mentions the generated implementation fails
the *build*), and the module is a valid target for
`scripts/mutate.py Autoform/Generated/<M>.lean Autoform.Generated.<M>
 --spec-file Autoform/SpecsGen/<M>.lean --spec-module Autoform.SpecsGen.<M>`.

Usage:
    synth_specs.py <ast.json> <source-dir> <Module> [--tests DIR] [--cases N]
                   [--no-mine] [--json PATH]
"""
from __future__ import annotations

import argparse
import json
import os
import random
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(REPO, "cartographer"))

import differential as D                                  # noqa: E402  (trace + encoder)
import mutate as M                                        # noqa: E402  (decl parser)
from render_lean import ident as lean_ident               # noqa: E402  (name mangling)

random.seed(20260819)

FUEL = 400             # fuel budget the emitted theorems are stated at
INIT_FUEL = 5000       # fuel for `initGlobals`, matching scripts/differential.py
MAX_DOMAIN = 8         # cases per mined law: the kernel has to evaluate every one
MIN_LAW_DOMAIN = 3     # below this a "law" is an anecdote, not a law
OUTDIR = os.path.join(REPO, "Autoform", "SpecsGen")
SCRATCH = os.environ.get("AUTOFORM_SCRATCH", "/tmp")
GLOBALS = ("[]", "0")   # filled in by `globals_literal` once the module is known
ENV = dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + ":" + os.environ["PATH"])


# ---------------------------------------------------------------------------
# 0. Lean plumbing
# ---------------------------------------------------------------------------

def lean_run(src: str, tag: str, timeout: int = 900):
    """Elaborate a Lean source string; return (rc, stdout, stderr)."""
    path = os.path.join(SCRATCH, "autoform_synth_%s.lean" % tag)
    with open(path, "w", encoding="utf-8") as f:
        f.write(src)
    try:
        r = subprocess.run(["lake", "env", "lean", path], capture_output=True, text=True,
                           env=ENV, cwd=REPO, timeout=timeout)
    except subprocess.TimeoutExpired:
        # The `timeout` argument was accepted and then not passed to `subprocess.run`,
        # so a chunk that diverged hung the whole generator with no output at all. A
        # timeout is a *result* — "this could not be evaluated in %d s" — and the caller
        # records it as `not_checked`, never as a pass.
        return 124, "", "lake env lean exceeded %d s on %s" % (timeout, path), path
    return r.returncode, r.stdout, r.stderr, path


def core_names(module: str):
    """The call-closed core, straight from `Program.callClosed` — the Lean definition is
    the authority on which functions are analysable, so it is asked rather than
    re-implemented here."""
    # Per-corpus namespaces (`Autoform.Generated.<M>`) landed in the generated modules but
    # never here, so every reference below was to `Autoform.Generated.program`, which has
    # not existed since. The generator could not query ANY corpus -- and because
    # `check_specs_fresh` demands regeneration rather than re-recording, that silently made
    # every AST change unlandable.
    src = ("import Autoform.Ledger\nimport Autoform.Generated.{m}\n"
           "open Autoform.Core in\n#eval do\n"
           "  let p : Program := Autoform.Generated.{m}.program\n"
           "  IO.println (String.intercalate \"\\n\" "
           "(p.callClosed.map (fun f : Func => f.name)))\n").format(m=module)
    rc, out, err, _ = lean_run(src, "core")
    if rc != 0:
        print("could not query the call-closed core:\n%s" % (err or out)[:400])
        return None
    return [l for l in out.splitlines() if l.strip()]


def globals_literal(module: str):
    """The module-initialiser heap, as a Lean *source* literal.

    Module-level bindings (`Stmt.setGlobal`, `Expr.closure`) only exist after the
    initialisers have run, so every case has to run against that frame — the same frame
    `scripts/differential.py` builds. Writing `initGlobals P 5000 moduleInits` into the
    generated module would be simpler, but the kernel has no sharing: every `by rfl` proof
    would re-run every initialiser once per case. Evaluating it once here and emitting the
    resulting heap as a literal keeps the proofs affordable, and the literal is Lean's own
    `Repr` output for the value, not a reconstruction of it."""
    src = ("import Autoform.Generated.{m}\n"
           "open Autoform.Core Autoform.Generated.{m}\n"
           "#eval do\n"
           "  let gp := initGlobals Autoform.Generated.{m}.program {f} "
           "Autoform.Generated.{m}.moduleInits\n"
           "  IO.println (\"@@\" ++ ((repr gp.1).pretty (width := 100000000)))\n"
           "  IO.println (\"##\" ++ toString gp.2)\n").format(m=module, f=INIT_FUEL)
    rc, out, err, _ = lean_run(src, "globals")
    heap = gref = None
    for line in out.splitlines():
        if line.startswith("@@"):
            heap = line[2:]
        elif line.startswith("##"):
            gref = line[2:]
    if heap is None:
        print("   could not materialise the globals frame; falling back to an empty "
              "heap (functions that read module-level names will hole and be dropped)")
        return "[]", "0"
    return heap, gref


# ---------------------------------------------------------------------------
# 1. Source artifacts (§4 source 1)
# ---------------------------------------------------------------------------

def strip_doc(body):
    """A leading docstring is an `exprS` of a string literal; peel it off.

    It is peeled rather than ignored because the *shape* underneath is what decides
    whether a universally quantified specification can be generated and proved."""
    doc = None
    while body.get("k") == "seq" and body["a"].get("k") == "exprS" \
            and body["a"]["e"].get("k") == "str":
        doc = body["a"]["e"]["v"]
        body = body["b"]
    return doc, body


DOCTEST = re.compile(r'^\s*>>> ', re.M)


def mine_artifacts(funcs, src_root):
    """Count what §4 source 1 actually offers on this corpus, without guessing.

    Docstrings and guards come from the AST (so they are exactly what was translated);
    doctests and property-based tests are counted from the source tree, because a PBT is
    evidence about the *repository*, not about any one translated function."""
    art = {"docstrings": 0, "doctests": 0, "asserts": 0, "raises": 0,
           "pbt_files": 0, "pbt_properties": 0, "test_files": 0}
    for f in funcs:
        doc, _ = strip_doc(f["body"])
        if doc:
            art["docstrings"] += 1
            if DOCTEST.search(doc):
                art["doctests"] += 1
        blob = json.dumps(f["body"])
        art["raises"] += blob.count('"k": "raise"') + blob.count('"k":"raise"')
    for root, _dirs, files in os.walk(src_root):
        if ".git" in root:
            continue
        for fn in files:
            if not fn.endswith((".py", ".c", ".cc", ".cpp", ".h", ".hpp")):
                continue
            p = os.path.join(root, fn)
            try:
                txt = open(p, encoding="utf-8", errors="replace").read()
            except OSError:
                continue
            if os.path.basename(p).startswith("test") or "/tests" in p:
                art["test_files"] += 1
            art["asserts"] += len(re.findall(r'^\s*assert\b', txt, re.M))
            if "hypothesis" in txt:
                art["pbt_files"] += 1
                art["pbt_properties"] += len(re.findall(r'^\s*@given\b', txt, re.M))
            art["doctests"] += 0
    return art


# ---------------------------------------------------------------------------
# 2. Observations (§4 source 1 + 4): the repository's own test suite
# ---------------------------------------------------------------------------

def observe(ast_path, src_root, tests_override, per_fn):
    """Drive the repo's suite under `differential.py`'s trace hook.

    Reused wholesale rather than rebuilt: the encoder there already refuses every value
    it cannot represent faithfully, which is precisely the property a specification
    generator needs from its input."""
    funcs = json.load(open(ast_path))
    holefree = [f for f in funcs if not D.has_hole(f["body"])]
    wanted = set(f["name"] for f in holefree if D.classify(f))
    # The exporter emits one synthetic `<module-objects>:<module>` entry with an empty
    # `file`, which is not a source path. Passed through, `root + ""` is the source root
    # itself and `build_lineno_index` dies with IsADirectoryError -- a crash, at least,
    # rather than a silent miss, but it stops the whole run. Drop empty paths here and
    # SAY how many, so a corpus that is mostly empty paths cannot look like a clean run.
    allrels = sorted(set(f.get("file", "") for f in funcs))
    rels = [r for r in allrels if r and not r.endswith("/")]
    if len(rels) != len(allrels):
        print("   %d AST entr%s carry no source path (synthetic module entries); "
              "excluded from the line-number index, %d real path(s) remain"
              % (len(allrels) - len(rels), "y" if len(allrels)-len(rels)==1 else "ies",
                 len(rels)))
    if not rels:
        raise SystemExit("ABORT: not one AST entry names a source file. Nothing can be "
                         "traced, and a run that reports 0 observations here would read "
                         "as 'the tests exercise nothing'.")
    root = D.resolve_src_root(src_root, rels)
    tests = [tests_override] if tests_override else D.find_tests(root)
    index = D.build_lineno_index(root, rels)
    stats = {"skip_varargs": 0, "skip_unencodable_args": 0, "skip_unencodable_ret": 0,
             "test_runs": []}
    recs = D.trace_tests(root, tests, index, wanted, per_fn, stats) if tests else []
    return funcs, recs, stats, root, tests


# ---------------------------------------------------------------------------
# 3. Fuzzing: candidate domains
# ---------------------------------------------------------------------------

# Value generation is Hypothesis's job, not ours. The hand-rolled version drew ints from
# a seven-element list (`[0, 1, -1, 2, 7, -7, 1000000]`) and strings from three shapes
# (`""`, `"x"`, `v + "!"`). Hypothesis's `integers()` already knows to probe 0, +/-1, and
# the machine-word and 64-bit boundaries -- the exact edges `Numeric.lean` models and the
# exact edges a hand-written list forgets -- and `text()` probes empty, whitespace and
# non-ASCII. `derandomize=True` keeps a run reproducible, which the refutation record
# depends on: a counterexample nobody can regenerate is not evidence.
#
# Hypothesis's shrinking is deliberately NOT used. Shrinking needs a per-example verdict,
# and the verdict here comes from a batched Lean elaboration of 120 candidates at a time
# (`refute`, below); asking Lean once per shrink step would cost hours. So Hypothesis is
# used as a generator and the batch oracle is kept. Counterexamples are therefore not
# minimal, and that is a real limitation of this script, not a solved problem.

from hypothesis import HealthCheck, Phase, given, settings
from hypothesis import strategies as st

# Bare `st.integers()` is the wrong strategy here, and measuring said so: drawn 600 times
# it hit exactly one of the boundaries this project models (0) and wandered out to 10^31.
# Python ints really are unbounded, so those draws are legitimate and are kept -- but the
# edges that `Numeric.lean` gives distinct behaviour to (word boundaries, INT_MIN, where
# `-INT_MIN` is unrepresentable) have to be sampled deliberately or they never appear.
_EDGES = [0, 1, -1, 2, -2, 7, -7, 10 ** 6,
          2 ** 31 - 1, -2 ** 31, 2 ** 31, 2 ** 32,
          2 ** 63 - 1, -2 ** 63, 2 ** 63, 10 ** 18]
_INTS = st.one_of(
    st.sampled_from(_EDGES),                                       # the modelled edges
    st.integers(min_value=-2 ** 63, max_value=2 ** 63),            # machine-word range
    st.integers())                                                 # genuine bignums

# Codepoints Lean's string literals and the JSON round-trip both survive: no surrogates.
_TEXT = st.text(
    alphabet=st.characters(exclude_categories=("Cs",), max_codepoint=0x2FFF),
    max_size=8)


def _pool(strategy, n):
    """Draw `n` values from a Hypothesis strategy as a plain list.

    Hypothesis's execution model is one adaptive test function; this is the supported way
    to borrow only its generators. `derandomize` makes the pool a pure function of the
    strategy, so two runs of this script fuzz identically."""
    out = []

    @settings(max_examples=n, database=None, derandomize=True, deadline=None,
              phases=[Phase.generate], suppress_health_check=list(HealthCheck))
    @given(strategy)
    def collect(v):
        out.append(v)

    collect()
    return out


_POOL_N = 200
_INT_POOL = None
_STR_POOL = None


def _pools():
    global _INT_POOL, _STR_POOL
    if _INT_POOL is None:
        _INT_POOL = _pool(_INTS, _POOL_N)
        _STR_POOL = _pool(_TEXT, _POOL_N)
    return _INT_POOL, _STR_POOL


def perturb(v, rng):
    """One structural mutation of an encoded value. Used to build the refutation domain:
    a law that only ever saw the test suite's arguments has not been tested."""
    ints, strs = _pools()
    t = v[0]
    if t == "int":
        return ("int", rng.choice(ints))
    if t == "bool":
        return ("bool", not v[1])
    if t == "str":
        return ("str", rng.choice(strs))
    if t in ("list", "tuple"):
        if v[1] and rng.random() < 0.5:
            i = rng.randrange(len(v[1]))
            return (t, [perturb(x, rng) if j == i else x for j, x in enumerate(v[1])])
        return (t, [])
    if t == "dict":
        return (t, []) if rng.random() < 0.5 else v
    if t == "unit":
        return ("int", 0)
    return v


def fuzz_cases(rec, rng, n):
    """Fuzz a recorded call: perturb arguments, and perturb the receiver's fields.

    The receiver matters more than the arguments here — most of the call-closed core of a
    cache library is accessors, and a law about an accessor is only tested by varying the
    object it reads."""
    out = []
    for _ in range(n):
        args = [perturb(a, rng) if rng.random() < 0.7 else a for a in rec["args"]]
        heap = [list(o) for o in rec["heap"]]
        for o in heap:
            o[1] = [(k, perturb(x, rng) if rng.random() < 0.4 else x) for k, x in o[1]]
        out.append({"heap": [(c, fs) for c, fs in heap], "self": rec["self"],
                    "args": args})
    return out


# ---------------------------------------------------------------------------
# 3b. Synthetic domains — the corpora with no CPython to trace
# ---------------------------------------------------------------------------
#
# Everything above this point takes its domain from `differential.py`'s trace hook, which
# means it takes its domain from *CPython*. That is the right source when the corpus is
# Python and it is the only source the generator has ever had — which is exactly why
# every theorem in this repository is about one Python library. V8 and Linux have no
# CPython to trace: there is no interpreter of ours that can run `bits.cc`, and a
# recorded call for a C++ function is not something this repository can honestly produce.
#
# So the domain is *synthesized* instead: arguments drawn from the same Hypothesis pools
# the fuzzer already uses, typed by the C/C++ signature carried in the function's name.
# What this buys and what it costs, stated plainly:
#
#   * `conform_*` is impossible here and is NOT generated. A cross-runtime theorem needs
#     the other runtime. Emitting one against outcomes this system computed itself would
#     be the interpreter agreeing with itself — the precise failure the family exists to
#     avoid. The synthetic families are structural (§4.2) and algebraic (§4.3) only.
#   * `const_*`, `raises_*` and `projects_*` are also not generated: all three are *mined
#     from observed outcomes*, and there are none.
#   * Everything else is unchanged, including every anti-vacuity gate: a law is still
#     refuted against its domain before emission, still dropped if any case holes, still
#     screened, and still has to survive the `≠ outOfFuel` guard to be lifted off `FUEL`.
#
# One gate is *added* for this mode. With a recorded domain, a law about an argument was
# at least about an argument some caller really passed. With a synthesized one, a
# function that ignores its parameters satisfies `commutes` and `idempotent` trivially,
# so the screen below requires the subject to actually mention the parameter the law is
# about (`argument_insensitive`).

_SIG_ARGS = re.compile(r'\(([^()]*)\)\s*$')


def param_types(fname, params):
    """Guess each parameter's type from the C/C++ signature carried in the function name.

    `render_lean.py` keeps Joern's full signature (`…SignedMulHigh32:int32_t(int32_t,
    int32_t)`), so the types are right there. When the parse fails — Python names carry
    no signature, C++ templates nest parentheses — every parameter falls back to "any",
    which draws from every pool. A wrong guess costs a refuted candidate, never a wrong
    theorem: the refutation pass runs the real semantics either way."""
    m = _SIG_ARGS.search(fname or "")
    raw = [t.strip() for t in m.group(1).split(",")] if m and m.group(1).strip() else []
    if len(raw) != len(params):
        return ["any"] * len(params)
    out = []
    for t in raw:
        low = t.lower()
        if "*" in t or "char" in low and "*" in t:
            out.append("any")
        elif "bool" in low:
            out.append("bool")
        elif any(k in low for k in ("int", "long", "short", "size_t", "unsigned",
                                    "uint", "byte", "word")):
            out.append("int")
        elif "string" in low:
            out.append("str")
        elif "double" in low or "float" in low:
            out.append("float")          # not modelled; forces a fallback draw
        else:
            out.append("any")
    return out


def synth_args(types, rng):
    ints, strs = _pools()
    out = []
    for t in types:
        if t == "int":
            out.append(("int", rng.choice(ints)))
        elif t == "bool":
            out.append(("bool", rng.random() < 0.5))
        elif t == "str":
            out.append(("str", rng.choice(strs)))
        else:
            r = rng.random()
            if r < 0.55:
                out.append(("int", rng.choice(ints)))
            elif r < 0.8:
                out.append(("str", rng.choice(strs)))
            elif r < 0.9:
                out.append(("bool", rng.random() < 0.5))
            else:
                out.append(("list", [("int", rng.choice(ints))]))
    return out


def synth_cases(f, rng, n):
    """`n` synthetic calls of `f`: empty local heap, no receiver, fuzzed arguments.

    The heap is empty because these corpora have no objects to record — a C translation
    unit's state lives in the globals frame, which the generated module already carries as
    `h0`, and `case_lit` prepends it."""
    types = param_types(f.get("name", ""), f.get("params", []))
    seen, out = set(), []
    for _ in range(n * 4):
        if len(out) >= n:
            break
        c = {"heap": [], "self": None, "args": synth_args(types, rng)}
        k = json.dumps(c, sort_keys=True)
        if k in seen:
            continue
        seen.add(k)
        out.append(c)
    return out


# ---------------------------------------------------------------------------
# 4. Lean rendering of cases
# ---------------------------------------------------------------------------

def lean_str(s):
    """A Lean 4 string literal.

    `json.dumps` is *almost* right and was used here until it was measured: it emits
    `\\b` and `\\f` for U+0008 and U+000C, which Lean 4's lexer rejects
    ("invalid escape sequence"), and 213 candidates of a V8 run came back `not_checked`
    for that reason alone — a whole chunk of the population silently unevaluated because
    one fuzzed string held a backspace. Everything outside the printable ASCII range is
    written as `\\uXXXX`, which Lean does accept."""
    out = ['"']
    for ch in s:
        o = ord(ch)
        if ch == '"':
            out.append('\\"')
        elif ch == "\\":
            out.append("\\\\")
        elif ch == "\n":
            out.append("\\n")
        elif ch == "\t":
            out.append("\\t")
        elif ch == "\r":
            out.append("\\r")
        elif 0x20 <= o < 0x7F:
            out.append(ch)
        elif o <= 0xFFFF:
            out.append("\\u%04x" % o)
        else:                       # outside the BMP: Lean has no \U escape
            out.append("\\u%04x\\u%04x"
                       % (0xD800 + ((o - 0x10000) >> 10),
                          0xDC00 + ((o - 0x10000) & 0x3FF)))
    out.append('"')
    return "".join(out)


def val_lit(v):
    """`differential.lean_val`, with string literals written by `lean_str`."""
    t = v[0]
    if t == "str":
        return "Val.str " + lean_str(v[1])
    if t in ("list", "tuple"):
        return "Val.%s [%s]" % (t, ", ".join(val_lit(x) for x in v[1]))
    if t == "dict":
        return "Val.dict [%s]" % ", ".join("(%s, %s)" % (val_lit(a), val_lit(b))
                                           for a, b in v[1])
    return D.lean_val(v)


def heap_lit(heap):
    """Heap literal, written with named fields.

    `differential.py`'s `lean_heap` uses the anonymous constructor, which no longer
    accepts `Obj` now that it carries a third (defaulted) `captured` field — named fields
    are the form that survives a structure gaining one."""
    return "[%s]" % ", ".join(
        "{ cls := %s, fields := [%s] }"
        % (lean_str(cls), ", ".join("(%s, %s)" % (lean_str(k), val_lit(v))
                                    for k, v in fields))
        for cls, fields in heap)


def case_lit(c):
    slf = "none" if c["self"] is None else "(some (%s))" % val_lit(c["self"])
    return ("{ heap := h0 ++ %s, self := %s, args := [%s] }"
            % (heap_lit(c["heap"]), slf,
               ", ".join(val_lit(a) for a in c["args"])))


def eresult_lit(outcome):
    """The outcome CPython produced, as a Core `EResult`.

    Only `val` and `exn` occur: `hole` and `outOfFuel` are statements about *our*
    ignorance and the real runtime never makes them."""
    kind, payload = outcome
    if kind == "val":
        return "EResult.val (%s)" % val_lit(payload)
    return "EResult.exn (Val.str %s)" % lean_str(payload)


def obs_lit(rec):
    return "{ case := %s, expected := %s }" % (case_lit(rec), eresult_lit(rec["outcome"]))


# ---------------------------------------------------------------------------
# 5. Candidate generation
# ---------------------------------------------------------------------------

class Cand:
    """One candidate specification, before anything is known about whether it is true."""

    def __init__(self, cid, family, source, subject, fdef, law, dom, kind="law",
                 dom_kind="case", note="", extra=None):
        self.id, self.family, self.source = cid, family, source
        self.subject, self.fdef = subject, fdef
        self.law = law                 # Lean text: partially applied law
        self.dom = dom                 # list of Lean case/obs literals
        self.kind = kind               # "law" | "universal"
        self.dom_kind = dom_kind       # "case" | "obs"
        self.note = note
        self.extra = extra or {}
        self.status = "candidate"
        self.reason = ""
        self.proved = False
        self.checked = None            # refutation verdict

    def as_json(self):
        return {"id": self.id, "family": self.family, "source": self.source,
                "subject": self.subject, "kind": self.kind, "domain": len(self.dom),
                "status": self.status, "reason": self.reason, "proved": self.proved,
                "checked": self.checked, "note": self.note}


GUARD = {"conform": "gRunObs", "charact": "gRunObs", "runs": "gRun", "returns": "gRun",
         "heappure": "gRun", "const": "gRun", "projects": "gRun",
         "identity": "gRun", "nonneg": "gRun", "raises": "gRun",
         "idempotent": "gIdem", "involutive": "gInvol", "commutes": "gComm"}

MONO = {"conform": "lawConform_fuel_mono", "charact": "lawConform_fuel_mono",
        "runs": "lawRuns_fuel_mono",
        "returns": "lawReturns_fuel_mono", "heappure": "lawHeapPreserved_fuel_mono",
        "const": "lawConst_fuel_mono", "projects": "lawProjects_fuel_mono",
        "identity": "lawIdentity_fuel_mono", "nonneg": "lawNonneg_fuel_mono",
        "raises": "lawRaises_fuel_mono", "idempotent": "lawIdempotent_fuel_mono",
        "involutive": "lawInvolutive_fuel_mono", "commutes": "lawCommutes_fuel_mono"}


def has_try_finally(body):
    """`Stmt.tryFinally` is the one construct fuel monotonicity excludes, and the
    exclusion is real: `FuelMono.tryFinally_breaks_fuel_mono` exhibits a program that
    answers 1 at fuel 4 and 2 at fuel 5. A law about such a subject stays an open
    obligation."""
    return '"tryFinally"' in json.dumps(body)


def writes_heap(body):
    blob = json.dumps(body)
    return any(k in blob for k in ('"setField"', '"setIndex"', '"alloc"'))


def can_hole_or_loop(body):
    """Does this function have any construct that could hole at runtime or fail to
    terminate? Mirrors `Ledger.lean`'s `Analysis.eRisk`: `field`, `index`, `mcall`,
    `call`, `inOp`, arithmetic, and every looping form."""
    blob = json.dumps(body)
    return any('"%s"' % k in blob for k in
               ("field", "index", "mcall", "call", "alloc", "inOp", "binop",
                "loop", "forIn", "setIndex"))


def gen_candidates(core, byname, recs, rng, synthetic=False):
    """Mine candidates for every call-closed function the suite actually exercised.

    With `synthetic=True` there is no suite and no recorded call: the domain is fuzzed
    from the signature instead, and the three families that are mined *from observations*
    (`conform`, `const`, `raises`, `projects`) are not generated at all. See §3b."""
    cands = []
    by_fn = {}
    for r in recs:
        by_fn.setdefault(r["name"], []).append(r)

    for name in core:
        f = byname.get(name)
        if f is None:
            continue
        fdef = lean_ident(name)
        obs = by_fn.get(name, [])
        sid = re.sub(r'[^A-Za-z0-9]', '_', name)[-70:].strip("_")
        doc, core_body = strip_doc(f["body"])
        tf = has_try_finally(f["body"])

        # ---- §4 source 4: cross-implementation equivalence, one theorem per function.
        if obs and not synthetic:
            seen, uniq = set(), []
            for r in obs:
                k = json.dumps([r["heap"], r["self"], r["args"]], sort_keys=True)
                if k in seen:
                    continue
                seen.add(k)
                uniq.append(r)
            cf = Cand("conform_" + sid, "conform", "cross-runtime (§4.4)", name,
                      fdef, "lawConform C FUEL %s" % fdef,
                      [obs_lit(r) for r in uniq[:MAX_DOMAIN]], dom_kind="obs",
                      note="expected outcomes recorded from CPython by "
                           "scripts/differential.py")
            cf.extra["try_finally"] = has_try_finally(f["body"])
            cands.append(cf)

        # ---- the fuzz domain every behavioural law is refuted against
        base = []
        if synthetic:
            base = synth_cases(f, rng, MAX_DOMAIN)
        for r in obs[:4]:
            base.append({"heap": r["heap"], "self": r["self"], "args": r["args"]})
            base.extend(fuzz_cases(r, rng, 3))
        seen, dom = set(), []
        for c in base:
            k = json.dumps(c, sort_keys=True)
            if k in seen:
                continue
            seen.add(k)
            dom.append(c)
        dom = dom[:MAX_DOMAIN]
        if not dom:
            continue
        lits = [case_lit(c) for c in dom]
        triv_hole = not can_hole_or_loop(core_body)
        triv_heap = not writes_heap(core_body)

        def add(fam, source, law, note="", trivial=False, extra=None, tag=""):
            c = Cand("%s%s_%s" % (fam, tag, sid), fam, source, name, fdef, law, lits,
                     note=note, extra=extra)
            c.extra["try_finally"] = tf
            if trivial:
                c.extra["structurally_trivial"] = True
            cands.append(c)

        # ---- §4 source 2: structural / safety, free for all code
        add("runs", "structural (§4.2)", "lawRuns C FUEL %s" % fdef,
            note="no .hole and no .outOfFuel within the stated fuel budget",
            trivial=triv_hole)
        add("returns", "structural (§4.2)", "lawReturns C FUEL %s" % fdef,
            note="returns a value; does not even raise", trivial=triv_hole)

        # ---- §4 source 3: algebraic laws mined from behaviour
        add("heappure", "algebraic (§4.3)", "lawHeapPreserved C FUEL %s" % fdef,
            note="the call leaves the heap structurally unchanged", trivial=triv_heap)
        add("nonneg", "algebraic (§4.3)", "lawNonneg C FUEL %s" % fdef,
            note="integer result is non-negative", trivial=triv_hole)
        # Does the body actually *read* the parameter a law is about? On a synthesized
        # domain a function that ignores its arguments satisfies `commutes` and
        # `idempotent` for a reason that has nothing to do with the law.
        pnames = f.get("params", []) or []
        blob = json.dumps(core_body)
        reads = [('"v": %s' % json.dumps(p)) in blob for p in pnames]
        if any(len(c["args"]) >= 1 for c in dom):
            ins1 = synthetic and not (reads[:1] or [False])[0]
            add("identity", "algebraic (§4.3)", "lawIdentity C FUEL %s" % fdef,
                note="returns its first argument unchanged",
                extra={"argument_insensitive": ins1})
            add("idempotent", "algebraic (§4.3)", "lawIdempotent C FUEL %s" % fdef,
                note="f (f x) = f x",
                extra={"argument_insensitive": ins1})
            add("involutive", "algebraic (§4.3)", "lawInvolutive C FUEL %s" % fdef,
                note="f (f x) = x",
                extra={"argument_insensitive": ins1})
        if any(len(c["args"]) >= 2 for c in dom):
            ins2 = synthetic and not all(reads[:2] or [False, False])
            add("commutes", "algebraic (§4.3)", "lawCommutes C FUEL %s" % fdef,
                note="symmetric in its first two arguments",
                extra={"argument_insensitive": ins2})

        # constants and projections are mined from what was observed, then refuted
        vals = [r["outcome"] for r in obs if r["outcome"][0] == "val"]
        if vals and all(json.dumps(v) == json.dumps(vals[0]) for v in vals):
            add("const", "algebraic (§4.3)",
                "lawConst C FUEL %s (%s)" % (fdef, val_lit(vals[0][1])),
                note="constant output")
        exns = [r["outcome"] for r in obs if r["outcome"][0] == "exn"]
        if exns and not vals and all(e[1] == exns[0][1] for e in exns):
            add("raises", "artifact (§4.1)",
                "lawRaises C FUEL %s (Val.str %s)" % (fdef, lean_str(exns[0][1])),
                note="always raises %s — the postcondition of a guard the suite "
                     "exercised" % exns[0][1])
        flds = set()
        for r in obs:
            if r["self"] and r["self"][0] == "ref":
                idx = r["self"][1]
                if idx < len(r["heap"]):
                    flds.update(k for k, _ in r["heap"][idx][1])
        for fld in sorted(flds)[:6]:
            add("projects", "algebraic (§4.3)",
                "lawProjects C FUEL %s %s" % (fdef, lean_str(fld)),
                note="the accessor reads field %s" % fld,
                tag="_" + re.sub(r'[^A-Za-z0-9]', '_', fld))

        # ---- deliberately mined, and never emitted: the §15 pattern
        cands.append(Cand("determ_" + sid, "determinism", "algebraic (§4.3)", name, fdef,
                          "", lits, kind="determinism",
                          note="f(x) = f(x): the property §15 found dominates FVSpec's "
                               "vacuous 41%"))

        # ---- universally quantified families, with generated proofs
        if core_body.get("k") == "ret" and core_body["e"].get("k") in (
                "int", "str", "bool"):
            e = core_body["e"]
            lit = {"int": "Val.int (%s)" % e.get("v"), "bool": "Val.bool %s" %
                   ("true" if e.get("v") else "false"),
                   "str": "Val.str %s" % json.dumps(str(e.get("v")))}[e["k"]]
            cands.append(Cand("uconst_" + sid, "u_const", "structural (§4.2)", name, fdef,
                              "", [], kind="universal",
                              note="constant on every input, at every fuel budget ≥ 8",
                              extra={"shape": "const", "lit": lit}))
        if core_body.get("k") == "ret" and core_body["e"].get("k") == "field" \
                and core_body["e"]["a"].get("k") == "name" \
                and core_body["e"]["a"].get("v") == "self" and not f["params"]:
            cands.append(Cand("uproj_" + sid, "u_projection", "algebraic (§4.3)", name,
                              fdef, "", [], kind="universal",
                              note="accessor: returns receiver field %s on every heap"
                                   % core_body["e"]["f"],
                              extra={"shape": "projection",
                                     "field": core_body["e"]["f"],
                                     "documented": doc is not None}))
    # Lean names must be unique; a collision would silently drop a candidate.
    seen = {}
    for c in cands:
        if c.id in seen:
            seen[c.id] += 1
            c.id = "%s_%d" % (c.id, seen[c.id])
        else:
            seen[c.id] = 0
    return cands


# ---------------------------------------------------------------------------
# 6. Refutation
# ---------------------------------------------------------------------------

HEADER = """import Autoform.SpecsGen.Basis
import Autoform.Harness.Audit
import Autoform.Generated.%s

/-! Generated by `scripts/synth_specs.py`. Do not edit by hand. -/
namespace Autoform.SpecsGen.%s

open Autoform.Core Autoform.Refine Autoform.SpecsGen

-- The proofs below are by computation on concrete inputs: the kernel walks the
-- interpreter, and deeply nested calls need more than the default budgets.
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

abbrev P : Program := Autoform.Generated.%s.program

/-- The module-initialiser heap, evaluated once by `initGlobals P %d moduleInits` and
frozen into this literal so that the kernel does not re-run the initialisers for every
case of every proof. -/
def h0 : Heap := %s

/-- Address of the globals frame. -/
def gref : Ref := %s
def base : Nat := h0.length
def C : Ctx := { dialect := P.dialect, table := P.table, globals := gref }
def FUEL : Nat := %d
open Autoform.Generated.%s

/-- Every function body reachable in this program is `tryFinally`-free, so
`Autoform/FuelMono.lean`'s monotonicity theorems apply to this context. Checked by
computation over the whole function table, not assumed. `Stmt.tryFinally` is the single
construct that breaks fuel monotonicity (`FuelMono.tryFinally_breaks_fuel_mono` exhibits a
program answering 1 at fuel 4 and 2 at fuel 5), so this is the hypothesis that decides
whether a law checked at one budget holds at every larger one. -/
theorem C_tfFree : TFFreeCtx C := by
  refine tfFree_of_table ?_
  have h : (C.table.all fun p => tfFreeS p.2.body) = true := by rfl
  exact fun p hp => (List.all_eq_true.mp h) p hp
"""


def domain_defs(c):
    ty = "Obs" if c.dom_kind == "obs" else "Case"
    body = ",\n   ".join(c.dom)
    return "def dom_%s : List %s :=\n  [%s]\n" % (c.id, ty, body)


def refute(cands, module, chunk=120):
    """Evaluate every candidate over its domain, in the Lean semantics, before anything
    is emitted. A single counterexample drops the candidate.

    The check is `#eval`, not a proof: refutation is cheap and must not be allowed to
    fail merely because the kernel is slow. What survives is *then* asked to be proved."""
    live = [c for c in cands if c.kind == "law"]
    for i in range(0, len(live), chunk):
        part = live[i:i + chunk]
        src = [HEADER % (module, module, module, INIT_FUEL, GLOBALS[0], GLOBALS[1],
                         FUEL, module)]
        for c in part:
            src.append(domain_defs(c))
            src.append('#eval IO.println ("@@%s@@" ++ toString '
                       '((dom_%s).all (%s)) ++ " " ++ toString (dom_%s).length ++ " " '
                       '++ toString ((dom_%s).countP (fun x => %s)))\n'
                       % (c.id, c.id, c.law, c.id, c.id,
                          "isHole (runCase C FUEL %s x.case).2" % c.fdef
                          if c.dom_kind == "obs" else
                          "isHole (runCase C FUEL %s x).2" % c.fdef))
        src.append("end Autoform.SpecsGen.%s\n" % module)
        # A concurrently rebuilt `.olean` makes `lake env lean` fail for reasons that
        # have nothing to do with the candidates; retry once before recording a chunk as
        # unevaluated, since "not checked" silently shrinks the population.
        got = {}
        for attempt in range(2):
            rc, out, err, path = lean_run("\n".join(src), "refute%d" % i)
            for line in out.splitlines():
                m = re.match(r'@@([A-Za-z0-9_]+)@@(true|false) (\d+) (\d+)', line)
                if m:
                    got[m.group(1)] = (m.group(2) == "true", int(m.group(3)),
                                       int(m.group(4)))
            if got:
                break
            subprocess.run(["lake", "build", "Autoform.Generated.%s" % module,
                            "Autoform.SpecsGen.Basis"], capture_output=True, env=ENV,
                           cwd=REPO)
        for c in part:
            if c.id not in got:
                c.status, c.reason = "not_checked", "lean could not evaluate the domain"
                c.checked = {"error": (err or out)[-300:]}
                continue
            holds, n, holes = got[c.id]
            c.checked = {"holds": holds, "domain": n, "holes": holes}
            if holes:
                c.status = "refuted"
                c.reason = ("interpreter reached an untranslated construct on %d/%d "
                            "cases — the law is inconclusive, not true" % (holes, n))
            elif not holds:
                c.status, c.reason = "refuted", "counterexample in the fuzzed domain"
        if rc != 0 and not got:
            print("  refutation chunk %d: lean failed (%s)" % (i, path))
    return cands


def guard_pass(cands, module, chunk=120):
    """Evaluate the `≠ outOfFuel` guard of each surviving law over its own domain.

    This is what decides whether a law checked at one fuel budget can be lifted to every
    larger one. It is *evaluated*, never assumed: `lawCommutes` compares two results with
    `EResult.beq`, and `beq .outOfFuel .outOfFuel` is `true`, so a "commuting" function
    that simply never ran would sail through the law and fail here — which is the whole
    point of checking. The pass also counts, per candidate, how many cases actually hit
    `outOfFuel`, so the answer to "did the guard ever matter?" is a measurement.
    """
    live = [c for c in cands if c.kind == "law" and c.status == "candidate"]
    for c in live:
        if c.extra.get("try_finally"):
            c.extra["fuel_mono"] = False
            c.extra["fuel_mono_reason"] = (
                "subject reaches Stmt.tryFinally, which FuelMono excludes by "
                "counterexample (1 at fuel 4, 2 at fuel 5)")
    todo = [c for c in live if "fuel_mono" not in c.extra]
    for i in range(0, len(todo), chunk):
        part = todo[i:i + chunk]
        src = [HEADER % (module, module, module, INIT_FUEL, GLOBALS[0], GLOBALS[1],
                         FUEL, module)]
        for c in part:
            g = GUARD[c.family]
            arg = "x.case" if c.dom_kind == "obs" else "x"
            oof = ("(fun x => !(defined (runCase C FUEL %s %s).2))" % (c.fdef, arg))
            swapped = ("(fun x => match x.args with"
                       " | a :: b :: rest =>"
                       " !(defined (runCase C FUEL %s"
                       " { x with args := b :: a :: rest }).2)"
                       " | _ => false)" % c.fdef)
            src.append(domain_defs(c))
            src.append('#eval IO.println ("@@%s@@" ++ toString '
                       '((dom_%s).all (%s C FUEL %s)) ++ " " ++ toString '
                       '((dom_%s).countP %s) ++ " " ++ toString '
                       '((dom_%s).countP %s))\n'
                       % (c.id, c.id, g, c.fdef, c.id, oof, c.id,
                          swapped if c.family == "commutes" else oof))
        src.append("end Autoform.SpecsGen.%s\n" % module)
        got = {}
        for _ in range(2):
            rc, out, err, path = lean_run("\n".join(src), "guard%d" % i)
            for line in out.splitlines():
                m = re.match(r'@@([A-Za-z0-9_]+)@@(true|false) (\d+) (\d+)', line)
                if m:
                    got[m.group(1)] = (m.group(2) == "true", int(m.group(3)),
                                       int(m.group(4)))
            if got:
                break
        for c in part:
            if c.id not in got:
                c.extra["fuel_mono"] = False
                c.extra["fuel_mono_reason"] = "guard could not be evaluated"
                continue
            ok, n_oof, n_second = got[c.id]
            c.extra["fuel_mono"] = ok
            c.extra["outOfFuel_cases"] = n_oof
            c.extra["outOfFuel_second_run"] = n_second
            if not ok:
                c.extra["fuel_mono_reason"] = (
                    "guard false: %d of %d cases reach outOfFuel at FUEL, so the law's "
                    "truth at FUEL does not transport" % (n_oof, len(c.dom)))
    return cands


# ---------------------------------------------------------------------------
# 6b. Characterization: what the translated function actually computes
# ---------------------------------------------------------------------------
#
# Measured, not assumed: the mutation gate (`scripts/mutate.py`, the *sufficient* half of
# the anti-vacuity check) rated the structural families WEAK on Linux. `lawRuns` and
# `lawReturns` forbid only `.hole` and `.outOfFuel`, and most mutations of a body preserve
# both — `radix_tree_tagged` with its two arguments swapped still returns a value, so the
# theorem still proves and the mutant survives. On cachetools the family with teeth was
# `conform_*`, which pins the exact outcome; C and C++ corpora have no runtime this
# repository can drive, so that family does not exist for them.
#
# This is the honest replacement, and its name is chosen so that it can never be mistaken
# for the other one:
#
#   * `conform_*` says *CPython produced this*. It is cross-implementation evidence.
#   * `charact_*` says *this translation computes this*. It is a **characterization**
#     (regression) theorem. The right-hand side is this system's own output, so it is
#     emphatically NOT evidence that the translation is faithful to C, and the report
#     records it under a separate key for exactly that reason.
#
# What it is good for is the thing the structural families are bad at: it pins every bit
# of the result, so any mutation of the subject that changes what it computes breaks the
# proof. A specification that cannot be broken by breaking the code is worthless, and this
# is how the C corpora get one at all.
#
# Anti-vacuity, unchanged: a case whose result is `.hole` or `.outOfFuel` is dropped
# (`EResult.beq .outOfFuel .outOfFuel` is `true`, which is the vacuity this whole file is
# organised against), a subject with nothing left is dropped, and the `≠ outOfFuel` guard
# still has to pass before the theorem is lifted off `FUEL`.

def characterize(cands, module, chunk=60):
    """Emit one `charact_*` candidate per subject that already has a surviving law."""
    subjects = {}
    for c in cands:
        if c.kind == "law" and c.status == "candidate" and c.dom_kind == "case":
            subjects.setdefault(c.subject, c)
    todo = list(subjects.values())
    out = []
    for i in range(0, len(todo), chunk):
        part = todo[i:i + chunk]
        src = [HEADER % (module, module, module, INIT_FUEL, GLOBALS[0], GLOBALS[1],
                         FUEL, module)]
        for c in part:
            src.append(domain_defs(c))
            src.append('#eval IO.println ("@@%s@@" ++ String.intercalate "@|@" '
                       '((dom_%s).map (fun x => ((repr (runCase C FUEL %s x).2).pretty '
                       '(width := 100000000)))))\n' % (c.id, c.id, c.fdef))
        src.append("end Autoform.SpecsGen.%s\n" % module)
        rc, sout, err, path = lean_run("\n".join(src), "charact%d" % i, timeout=1800)
        got = {}
        for line in sout.splitlines():
            m = re.match(r'@@([A-Za-z0-9_]+)@@(.*)$', line)
            if m:
                got[m.group(1)] = m.group(2).split("@|@")
        for c in part:
            res = got.get(c.id)
            if res is None:
                continue
            keep = [(case, r) for case, r in zip(c.dom, res)
                    if not (r.startswith("Autoform.Core.EResult.hole")
                            or r.startswith("Autoform.Core.EResult.outOfFuel"))]
            if len(keep) < MIN_LAW_DOMAIN:
                continue
            dom = ["{ case := %s, expected := %s }" % (case, r) for case, r in keep]
            n = Cand("charact_" + c.id.split("_", 1)[1], "charact",
                     "characterization (§4.2, NOT cross-runtime)", c.subject, c.fdef,
                     "lawConform C FUEL %s" % c.fdef, dom, dom_kind="obs",
                     note="the translated function computes exactly these results on "
                          "these inputs. Right-hand sides are THIS interpreter's own "
                          "output, recorded at FUEL: a regression/characterization "
                          "theorem, not cross-implementation evidence")
            n.extra["try_finally"] = c.extra.get("try_finally", False)
            n.extra["self_recorded"] = True
            out.append(n)
    cands.extend(out)
    return out


# ---------------------------------------------------------------------------
# 7. The vacuity screen — the same check names §15 applied to FVSpec
# ---------------------------------------------------------------------------

def screen(cands):
    for c in cands:
        if c.status not in ("candidate",):
            continue
        if c.kind == "determinism":
            c.status = "vacuous"
            c.reason = ("reflexive_conclusion: f(x) = f(x) is closed by `rfl` in a pure "
                        "setting — see SpecsGen.Basis.deterministic_vacuous")
            continue
        if c.kind == "universal":
            continue                                   # screened by construction below
        if not c.dom:
            c.status, c.reason = "vacuous", "empty_quantification: no domain"
            continue
        if c.extra.get("argument_insensitive"):
            c.status = "vacuous"
            c.reason = ("argument_insensitive: on a synthesized domain this law would "
                        "hold because the body never reads the parameter it is about, "
                        "not because the function has the property")
            continue
        if c.extra.get("structurally_trivial"):
            c.status = "vacuous"
            c.reason = ("trivial_conclusion: the AST contains no construct that could "
                        "falsify this, so the statement is true by shape, not by "
                        "behaviour")
            continue
        if c.fdef not in c.law:
            c.status = "vacuous"
            c.reason = "dependency_vacuity: statement never mentions the implementation"
            continue
        if c.dom_kind == "case" and len(c.dom) < MIN_LAW_DOMAIN:
            c.status = "vacuous"
            c.reason = ("empty_quantification: %d-case domain is an anecdote, not a "
                        "quantifier" % len(c.dom))
            continue
    return cands


# ---------------------------------------------------------------------------
# 8. Emission
# ---------------------------------------------------------------------------

PROOF_CONST = """theorem %(id)s :
    Refines P %(name)s 8 (fun _ => True) (fun _ => .ret (%(lit)s)) := by
  intro args _
  refine forall_ge_of_forall_add (N := 8) ?_
  intro k
  rw [runFunc_of_resolve _ _ _ _ %(fdef)s rfl]
  simp [applyFunc, execStmt, evalExpr, Env.set, %(fdef)s, ctxOf, P]
"""

PROOF_PROJ = """theorem %(id)s :
    MRefines P %(name)s 4
      (fun h self args => args = [] ∧ ∃ r, self = .ref r ∧
        ∀ o, h.get r = some o → o.cls.startsWith "<module>" = false)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (fieldOf h r %(field)s)
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨rfl, r, rfl, hmod⟩
  refine forall_ge_of_forall_add (N := 4) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ _ %(fdef)s rfl]
  simpa [Nat.add_comm, Nat.add_left_comm] using
    applyFunc_ret_field_self (ctxOf P) k h %(fdef)s %(field)s rfl rfl rfl rfl r [] rfl
      hmod
"""

PROOF_PROJ_DOC = """theorem %(id)s :
    MRefines P %(name)s 5
      (fun h self args => args = [] ∧ ∃ r, self = .ref r ∧
        ∀ o, h.get r = some o → o.cls.startsWith "<module>" = false)
      (fun h self _ => (h, match self with
                           | .ref r => .ret (fieldOf h r %(field)s)
                           | _      => .ret .unit)) := by
  rintro h _ args ⟨rfl, r, rfl, hmod⟩
  refine forall_ge_of_forall_add (N := 5) ?_
  intro k
  rw [runMethod_of_resolve _ _ _ _ _ _ %(fdef)s rfl]
  simpa [Nat.add_comm, Nat.add_left_comm] using
    applyFunc_doc_ret_field_self (ctxOf P) k h %(fdef)s %(field)s _ rfl rfl rfl rfl r
      [] rfl hmod
"""

FUEL_THM = """/-- Holds at **every** fuel budget at or above `FUEL`.

Checked at `FUEL` by computation, then transported by `FuelMono.applyFunc_fuel_mono`.
The `%(guard)s` conjunct is the `≠ outOfFuel` side condition, evaluated over the same
domain rather than assumed: without it a law could hold at `FUEL` for the reason that
nothing ran. -/
theorem %(id)s : ∀ fuel, FUEL ≤ fuel → ((dom_%(id)s).all (%(lawfuel)s)) = true := by
  intro fuel hf
  exact all_transfer _ (%(guard)s C FUEL %(fdef)s) (%(law)s) (%(lawfuel)s)
    (fun c hgc hlc =>
      %(mono)s (hctx := C_tfFree) (hfn := (by rfl : tfFreeS %(fdef)s.body = true))
        (hk := hf) (hg := hgc) (h := hlc))
    (by rfl) (by rfl)
"""

DOC = '''
/-!
# Synthesized specifications — `%(module)s`

**Generated by `scripts/synth_specs.py`. Do not edit by hand.**

Every statement below is about `Autoform/Generated/%(module)s.lean` *by import*, so a
mutation of the generated module is a mutation of the subject of these theorems
(`scripts/mutate.py --spec-file`). The `#audit_depends` block at the end fails the build
for any theorem that does not mention the implementation it claims to constrain.

What each family claims, in the order of `STRATEGY.md` §4:

* `conform_*` (§4.4, cross-implementation) — the interpreter reproduces, case by case,
  the outcome **CPython** produced when the repository's own test suite called this
  function. The right-hand sides were recorded by `scripts/differential.py`'s trace hook;
  they are not this system's own output, which is what keeps the family from being an
  elaborate `rfl`.
* `runs_*` / `returns_*` (§4.2, structural) — on this domain the interpreter neither
  reaches an untranslated construct nor exhausts its fuel. `EResult` distinguishes
  `.hole` and `.outOfFuel` from behaviour, so this is a real property, and it is stated
  only for functions whose AST *could* violate it.
* `heappure_*`, `const_*`, `projects_*`, `identity_*`, `idempotent_*`, `involutive_*`,
  `commutes_*`, `nonneg_*` (§4.3, algebraic) — laws mined from observed executions and
  **refuted against a fuzzed domain before emission**. Survivors only.
* `uconst_*`, `uproj_*` — universally quantified refinements, proved for every input and
  every fuel budget above a stated bound.

Domains are finite and explicit, and the theorems about them are proved by computation.
That is deliberate: a kernel-checked test is a test whose axiom basis is auditable and
whose subject a mutation gate can attack.

**Fuel.** A law checked at one budget is a weaker claim than it looks, so each law here is
stated as `∀ fuel, FUEL ≤ fuel → …` wherever that could be *proved*: checked at `FUEL` by
computation and transported by `Autoform/FuelMono.lean`'s `applyFunc_fuel_mono`. That
transport needs two side conditions, both discharged rather than assumed — the context is
`tryFinally`-free (`C_tfFree`, by computation over the function table) and the run did not
end in `outOfFuel` (the `g…` guard, evaluated over the same domain as the law). Where
either fails, the theorem stays at `FUEL` and its generalization is recorded in
`obligations` below as a `Prop`-valued `def` — a statement, not an admission.

There is no `sorry` in this file.

Counts for this run are in `Autoform/SpecsGen/report.json`.
-/
'''


def emit(cands, module, obligations_extra, ns=None):
    """`ns` overrides the namespace, for the mutation-gate sample module: two files that
    share a namespace also share declaration names, and importing both would clash."""
    ns = ns or module
    survivors = [c for c in cands if c.status in ("candidate", "proved")]
    out = [HEADER % (module, ns, module, INIT_FUEL, GLOBALS[0], GLOBALS[1],
                     FUEL, module)]
    out.insert(1, DOC % {"module": module})
    obs = []
    thms = []
    for c in survivors:
        if c.kind == "law":
            out.append(domain_defs(c))
            lawfuel = c.law.replace("C FUEL", "C fuel")
            if c.extra.get("fuel_mono"):
                # the general statement, proved: FuelMono transports it off FUEL
                out.append(FUEL_THM % {"id": c.id, "law": c.law, "lawfuel": lawfuel,
                                       "guard": GUARD[c.family], "fdef": c.fdef,
                                       "mono": MONO[c.family]})
            else:
                out.append("theorem %s : ((dom_%s).all (%s)) = true := by rfl\n"
                           % (c.id, c.id, c.law))
                # the honest generalization: stated, and not proved
                out.append("/-- Open: the same statement at **every** fuel budget ≥ "
                           "`FUEL`. Proved only at `FUEL`; %s -/\ndef ob_%s : Prop :=\n"
                           "  ∀ fuel, FUEL ≤ fuel → ((dom_%s).all (%s)) = true\n"
                           % (c.extra.get("fuel_mono_reason", "not transportable"),
                              c.id, c.id, lawfuel))
                obs.append((("ob_" + c.id), c.source, c.subject,
                            "proved at FUEL only; fuel-independence unproved (%s)"
                            % c.extra.get("fuel_mono_reason", "unknown")))
            thms.append((c.id, c.fdef))
        elif c.kind == "universal":
            d = {"id": c.id, "name": json.dumps(c.subject), "fdef": c.fdef,
                 "lit": c.extra.get("lit", ""),
                 "field": json.dumps(c.extra.get("field", ""))}
            if c.extra["shape"] == "const":
                out.append(PROOF_CONST % d)
            elif c.extra.get("documented"):
                out.append(PROOF_PROJ_DOC % d)
            else:
                out.append(PROOF_PROJ % d)
            thms.append((c.id, c.fdef))
    for name, source, subject, reason in obligations_extra:
        obs.append((name, source, subject, reason))
    out.append("/-- Everything this module states but does not prove. A `Prop`-valued "
               "`def` asserts nothing, so nothing here is admitted. -/\n"
               "def obligations : List OpenObligation :=\n  [%s]\n"
               % ",\n   ".join('{ name := %s, source := %s, subject := %s, reason := %s }'
                               % (json.dumps(n), json.dumps(s), json.dumps(sub),
                                  json.dumps(r)) for n, s, sub, r in obs))
    out.append("#eval IO.println (renderObligations %s obligations)\n"
               % json.dumps(ns))
    out.append("/-! ## Anti-vacuity gate\n\n`#audit_depends` fails the build if a "
               "theorem's proof term never mentions the generated definition it claims "
               "to be about — the necessary half of the gate. The sufficient half is "
               "`scripts/mutate.py`, run against this file. -/\n")
    for tid, fdef in thms:
        out.append("#audit_depends %s on %s" % (tid, fdef))
    out.append("\n/-! ## Axiom basis\n\n`#audit_axioms` fails the build on `sorryAx`, "
               "`ofReduceBool` or `ofReduceNat`, so \"no admitted step, no "
               "`native_decide`\" is checked here rather than asserted in prose. -/\n")
    for tid, _fdef in thms:
        out.append("#audit_axioms %s" % tid)
    out.append("\nend Autoform.SpecsGen.%s\n" % ns)
    return "\n".join(out), thms, obs


def compile_repair(cands, module, path, rounds=6, timeout=5400, ns=None):
    """Emit, compile, and demote whatever will not prove to an open obligation.

    A generator that cannot prove a statement has exactly two honest options: state it
    without proof, or drop it. `sorry` is neither."""
    demoted = []
    for _ in range(rounds):
        src, thms, _obs = emit(cands, module, demoted, ns=ns)
        with open(path, "w", encoding="utf-8") as f:
            f.write(src)
        try:
            r = subprocess.run(["lake", "env", "lean", path], capture_output=True,
                               text=True, env=ENV, cwd=REPO, timeout=timeout)
        except subprocess.TimeoutExpired:
            # Kernel evaluation of a whole module of by-computation proofs is expensive
            # and *can* diverge. A round that never returns is not a round that passed:
            # stop, and say which file to look at.
            print("  emission round exceeded %d s; the module is left on disk at %s but "
                  "is NOT proved. Reduce --max-subjects or --domain and re-run."
                  % (timeout, path))
            return False, demoted, "compile timeout after %d s" % timeout
        if r.returncode == 0:
            for c in cands:
                if c.status == "candidate":
                    c.status, c.proved = "proved", True
            return True, demoted, r.stdout
        lines = src.splitlines(keepends=True)
        decls = M.parse_decls(lines)
        bad = set()
        for m in re.finditer(r'^%s:(\d+):\d+: error' % re.escape(path),
                             r.stdout + r.stderr, re.M):
            ln = int(m.group(1))
            for d in decls:
                if d.start <= ln <= d.end and d.kind in ("theorem", "lemma"):
                    bad.add(d.name)
        if not bad:
            print("  build failed with no attributable theorem:\n%s"
                  % (r.stdout + r.stderr)[:600])
            return False, demoted, r.stdout + r.stderr
        for c in cands:
            if c.id in bad and c.status == "candidate":
                c.status = "unproved"
                c.reason = "no proof found by the generated portfolio"
                demoted.append(("stmt_" + c.id, c.source, c.subject,
                                "statement survived refutation; the generated proof "
                                "portfolio could not close it"))
        print("  demoted to open obligations: %s" % ", ".join(sorted(bad)))
    return False, demoted, "gave up after %d repair rounds" % rounds


# ---------------------------------------------------------------------------
# 9. main
# ---------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser(description="Layer 4: automatic specification synthesis")
    ap.add_argument("ast")
    ap.add_argument("src_root")
    ap.add_argument("module")
    ap.add_argument("--tests", default=None)
    ap.add_argument("--cases", type=int, default=10,
                    help="traced calls to keep per function")
    ap.add_argument("--allow-dirty-subject", action="store_true",
                    help="run even if Autoform/Generated/<M>.lean looks mutated. Only "
                         "for debugging: the resulting theorems are about a mutant")
    ap.add_argument("--refute-cache", default=None,
                    help="cache the refutation verdicts here, keyed by candidate id. "
                         "Refuting 500 candidates means elaborating half a megabyte of "
                         "Lean; when only the emission changed, replay instead")
    ap.add_argument("--obs-cache", default=None,
                    help="cache the traced calls here; the repository's suite takes "
                         "minutes to run under `sys.settrace` and the recording is "
                         "deterministic, so re-running it on every iteration is waste")
    ap.add_argument("--synthetic", action="store_true",
                    help="there is no runtime of ours that can execute this corpus (C, "
                         "C++): skip the trace step and fuzz the domain from the "
                         "signature instead. Drops the conform/const/raises/projects "
                         "families, which are mined from observations, and adds the "
                         "`argument_insensitive` screen. See §3b")
    ap.add_argument("--no-characterize", dest="characterize", action="store_false",
                    help="skip the `charact_*` family (characterization theorems that "
                         "pin what the translation computes). They are the only family "
                         "the mutation gate can bite on when a corpus has no runtime to "
                         "trace, so skipping them makes the output weaker, not purer")
    ap.add_argument("--out", default=None,
                    help="write the emitted module here instead of "
                         "Autoform/SpecsGen/<Module>.lean. A targeted run "
                         "(--only-subjects) must use it, or it would silently replace "
                         "the full corpus module with a two-function one")
    ap.add_argument("--only-subjects", default=None,
                    help="`;`-separated function names (a C++ signature contains commas: mine candidates for exactly "
                         "these call-closed functions and no others. Used to build a "
                         "small module quickly (the mutation-gate target); a run made "
                         "with it is recorded in the report as a targeted run, never as "
                         "a census of the corpus")
    ap.add_argument("--sample-subjects", type=int, default=4,
                    help="also emit `<Module>Sample.lean`: the proved theorems about "
                         "this many subjects, in their own namespace, as a mutation-gate "
                         "target that rebuilds in minutes rather than an hour. 0 to skip")
    ap.add_argument("--domain", type=int, default=8,
                    help="cases per mined law (default %d). The kernel evaluates every "
                         "one of them in every proof, so this is the main lever on how "
                         "long emission takes" % 8)
    ap.add_argument("--max-subjects", type=int, default=0,
                    help="cap the number of call-closed functions candidates are mined "
                         "for (0 = no cap). The cap is recorded in the report: a corpus "
                         "with 1,000 analysable functions is not a corpus with as many "
                         "as this run looked at")
    ap.add_argument("--json", dest="json_path",
                    default=os.path.join(OUTDIR, "report.json"))
    args = ap.parse_args()

    globals()["MAX_DOMAIN"] = args.domain
    os.makedirs(OUTDIR, exist_ok=True)
    rng = random.Random(20260819)

    print("== 0. the analysable core")
    gen_path = os.path.join(REPO, "Autoform", "Generated", "%s.lean" % args.module)
    if not args.allow_dirty_subject:
        # §19's trap in a new costume: another agent may be running `scripts/mutate.py`
        # over the very module these theorems are about. A proof against a mutant is
        # worse than no proof, and the mutation gate's own backup file is the reliable
        # in-flight marker.
        blockers = []
        if os.path.exists(gen_path + ".mutate-backup"):
            blockers.append("a mutation run is in flight (%s.mutate-backup exists)"
                            % os.path.basename(gen_path))
        try:
            if "__mutated" in open(gen_path, encoding="utf-8").read():
                blockers.append("the module contains mutation markers (`__mutated`)")
        except OSError as e:
            blockers.append("could not read the subject: %r" % e)
        # The marker check is necessary but not sufficient: `scripts/mutate.py` also
        # mutates *values* (`.int 0` -> `.int 1`), which leave no marker, and it removes
        # its `.mutate-backup` between mutants. For a tracked module the reliable test is
        # that it matches the commit — observed in practice: a gate was mid-cycle with no
        # backup file present and a live one-line numeric mutation in the tree.
        r = subprocess.run(["git", "diff", "--quiet", "--", gen_path],
                           capture_output=True, cwd=REPO)
        if r.returncode == 1:
            blockers.append("the subject differs from its committed version (a mutation "
                            "may be live, or the module was regenerated and not "
                            "committed)")
        if blockers:
            print("REFUSING TO RUN: the subject is not pristine — %s. Every theorem "
                  "below would be about a mutant. Re-run when the gate finishes, or "
                  "pass --allow-dirty-subject if you know what you are doing."
                  % "; ".join(blockers))
            return 3
    b = subprocess.run(["lake", "build", "Autoform.Generated.%s" % args.module,
                        "Autoform.SpecsGen.Basis"],
                       capture_output=True, text=True, env=ENV, cwd=REPO)
    if b.returncode != 0:
        # README: "a stale `.olean` made the oracle lie ... an oracle reading a stale
        # cache is worse than no oracle". The same applies here, and worse: a red
        # baseline makes *every* generated proof fail, and the repair loop would then
        # demote every real theorem to an open obligation and overwrite a good module
        # with a wrong one. Refuse instead, and leave the previous output alone.
        print("REFUSING TO RUN: the baseline does not build, so no proof attempt below "
              "would mean anything, and the previous output would be overwritten with "
              "an artefact of the broken build:\n%s"
              % (b.stderr or b.stdout)[-600:])
        return 2
    global GLOBALS
    GLOBALS = globals_literal(args.module)
    core = core_names(args.module)
    if core is None:
        return 2
    funcs = json.load(open(args.ast))
    byname = {f["name"]: f for f in funcs}
    print("   %d functions translated, %d call-closed" % (len(funcs), len(core)))

    print("== 1. existing artifacts (§4 source 1)")
    art = mine_artifacts(funcs, args.src_root)
    print("   docstrings %d, doctests %d, `raise` guards %d, asserts %d, "
          "hypothesis PBT files %d (%d @given properties)"
          % (art["docstrings"], art["doctests"], art["raises"], art["asserts"],
             art["pbt_files"], art["pbt_properties"]))

    print("== 2. observations from the repository's own test suite")
    if args.synthetic:
        # LOUD, not silent: this run has no cross-runtime evidence at all, and the
        # report has to say so where a reader will trip over it rather than in a
        # footnote. A quiet zero here would look exactly like a suite that ran and
        # found nothing.
        print("   SYNTHETIC MODE: this corpus has no runtime this repository can "
              "trace, so NO observations are recorded and NO conformance theorem is "
              "generated. The domains below are fuzzed from the signatures; the "
              "families that are mined from observed outcomes (conform, const, "
              "raises, projects) are absent by construction, not by accident.")
        recs, stats, tests = [], {"skip_varargs": 0, "skip_unencodable_args": 0,
                                  "skip_unencodable_ret": 0}, []
    elif args.obs_cache and os.path.exists(args.obs_cache):
        blob = json.load(open(args.obs_cache))
        funcs, recs, stats, tests = (json.load(open(args.ast)), blob["recs"],
                                     blob["stats"], blob["tests"])
        print("   (replayed from %s)" % args.obs_cache)
    else:
        funcs, recs, stats, root, tests = observe(args.ast, args.src_root, args.tests,
                                                  args.cases)
        if args.obs_cache:
            json.dump({"recs": recs, "stats": stats, "tests": tests},
                      open(args.obs_cache, "w"))
    incore = [r for r in recs if r["name"] in set(core)]
    if not args.synthetic and not recs:
        print("REFUSING TO RUN: the trace step recorded zero calls, so every mined law "
              "would be about a domain nobody supplied. That is silence, not a result. "
              "Point --tests at a suite, or pass --synthetic if this corpus genuinely "
              "has no runtime to trace.")
        return 4
    print("   %d calls recorded over %d functions; %d of them in the call-closed core"
          % (len(recs), len(set(r["name"] for r in recs)), len(incore)))

    print("== 3. candidate generation")
    subjects = core
    if args.only_subjects:
        want = [n.strip() for n in args.only_subjects.split(";") if n.strip()]
        subjects = [n for n in core if n in want]
        missing = [n for n in want if n not in subjects]
        if missing:
            # Asking for a function that is not in the call-closed core and getting a
            # quietly smaller run is exactly the silence this repository keeps paying
            # for. Name them.
            print("   !! not in the call-closed core, so NOT mined: %s"
                  % ", ".join(missing))
        if not subjects:
            print("REFUSING TO RUN: --only-subjects matched nothing in the call-closed "
                  "core.")
            return 5
        print("   targeted run: %d of %d call-closed functions named on the command line"
              % (len(subjects), len(core)))
    elif args.max_subjects and len(core) > args.max_subjects:
        # Deterministic and stated, so the report is not silently a sample presented as
        # a census: sorted by name, first N.
        subjects = sorted(core)[:args.max_subjects]
        print("   capped at %d of %d call-closed functions (--max-subjects); the "
              "report records the cap" % (len(subjects), len(core)))
    cands = gen_candidates(subjects, byname, incore, rng, synthetic=args.synthetic)
    print("   %d candidates" % len(cands))

    print("== 4. refutation (fuzz every candidate before emitting anything)")
    cache = {}
    if args.refute_cache and os.path.exists(args.refute_cache):
        cache = json.load(open(args.refute_cache))
    hit = [c for c in cands if c.id in cache]
    for c in hit:
        v = cache[c.id]
        c.status, c.reason, c.checked = v["status"], v["reason"], v["checked"]
    miss = [c for c in cands if c.id not in cache]
    if hit:
        print("   (%d verdicts replayed from %s, %d to check)"
              % (len(hit), args.refute_cache, len(miss)))
    refute(miss, args.module)
    if args.refute_cache:
        for c in cands:
            if c.kind == "law" and c.checked is not None:
                cache[c.id] = {"status": c.status, "reason": c.reason,
                               "checked": c.checked}
        json.dump(cache, open(args.refute_cache, "w"))
    refuted = [c for c in cands if c.status == "refuted"]
    nochk = [c for c in cands if c.status == "not_checked"]
    if nochk:
        # A candidate nobody could evaluate is not a candidate that passed. Say so where
        # it cannot be mistaken for a verdict, and say why.
        why = {}
        for c in nochk:
            e = (c.checked or {}).get("error", "")[-120:]
            why[e] = why.get(e, 0) + 1
        print("   !! %d candidates could NOT be evaluated at all — these are NOT "
              "passes and are not emitted. Distinct Lean errors:" % len(nochk))
        for e, n in sorted(why.items(), key=lambda kv: -kv[1])[:5]:
            print("      %4d x %s" % (n, e.replace("\n", " ")))
    print("   %d refuted, %d not checkable, %d survive"
          % (len(refuted), len(nochk),
             len([c for c in cands if c.status == "candidate"])))

    print("== 5. vacuity screen (the checks §15 ran over FVSpec, run over ourselves)")
    screen(cands)
    vac = [c for c in cands if c.status == "vacuous"]
    kinds = {}
    for c in vac:
        kinds[c.reason.split(":")[0]] = kinds.get(c.reason.split(":")[0], 0) + 1
    for k, v in sorted(kinds.items(), key=lambda kv: -kv[1]):
        print("   %-24s %d" % (k, v))
    survivors = [c for c in cands if c.status == "candidate"]
    print("   %d flagged vacuous, %d emitted" % (len(vac), len(survivors)))

    print("== 5a. characterization (what the translation computes; NOT cross-runtime)")
    if args.characterize:
        made = characterize(cands, args.module)
        print("   %d characterization theorems staged over %d subjects. These pin the "
              "exact result and are what the mutation gate can bite on; they are NOT "
              "evidence about the original C/C++/Python runtime and are reported "
              "separately." % (len(made), len(set(c.subject for c in made))))
    else:
        print("   skipped (--no-characterize)")

    print("== 5b. fuel-independence guards (FuelMono side condition, evaluated)")
    guard_pass(cands, args.module)
    live = [c for c in cands if c.kind == "law" and c.status == "candidate"]
    liftable = [c for c in live if c.extra.get("fuel_mono")]
    tf = [c for c in live if c.extra.get("try_finally")]
    oof = [c for c in live if c.extra.get("outOfFuel_cases")]
    print("   %d of %d laws transportable to all fuel ≥ FUEL; %d blocked by "
          "tryFinally; %d have a case that reaches outOfFuel at FUEL"
          % (len(liftable), len(live), len(tf), len(oof)))
    for c in oof:
        print("      outOfFuel at FUEL: %s (%d/%d cases, %d on the second run)"
              % (c.id, c.extra["outOfFuel_cases"], len(c.dom),
                 c.extra.get("outOfFuel_second_run", 0)))

    print("== 6. emission + proof")
    path = args.out or os.path.join(OUTDIR, "%s.lean" % args.module)
    if args.only_subjects and not args.out:
        print("REFUSING TO RUN: a targeted --only-subjects run would overwrite the "
              "corpus-wide module at %s with a handful of functions. Pass --out."
              % path)
        return 6
    ns_override = (os.path.splitext(os.path.basename(path))[0]
                   if args.out else args.module)
    ok, demoted, log = compile_repair(cands, args.module, path, ns=ns_override)
    proved = [c for c in cands if c.proved]
    unproved = [c for c in cands if c.status == "unproved"]
    print("   %s: %d theorems proved, %d statements left open"
          % ("clean" if ok else "BUILD FAILED", len(proved), len(unproved)))

    # ---- the mutation-gate target
    #
    # `#audit_depends` is the *necessary* half of the anti-vacuity gate; `scripts/mutate.py`
    # is the sufficient half, and it has to rebuild the spec module once per mutant. The
    # full module takes tens of minutes of kernel evaluation to check, so mutating against
    # it is not something anyone will actually run. This emits a small, separately
    # namespaced module carved from the same generated theorems -- same families, same
    # proofs, a handful of subjects -- so the sufficient half can be run at all. It is a
    # SAMPLE and the report says so: a kill rate measured on it is evidence about these
    # families, not a statement about every emitted theorem.
    sample_info = None
    if ok and args.sample_subjects:
        subs, chosen = [], []
        for c in [c for c in cands if c.proved]:
            if c.subject not in subs:
                if len(subs) >= args.sample_subjects:
                    continue
                subs.append(c.subject)
            chosen.append(c)
        if chosen:
            spath = os.path.join(OUTDIR, "%sSample.lean" % args.module)
            src, sthms, _ = emit(chosen, args.module, [], ns=args.module + "Sample")
            with open(spath, "w", encoding="utf-8") as f:
                f.write(src)
            rs = subprocess.run(["lake", "env", "lean", spath], capture_output=True,
                                text=True, env=ENV, cwd=REPO, timeout=3600)
            sample_info = {"file": spath, "theorems": len(sthms), "subjects": subs,
                           "build_clean": rs.returncode == 0,
                           "purpose": "fast target for scripts/mutate.py --spec-file; a "
                                      "sample of the emitted families, not all of them"}
            if rs.returncode != 0:
                print("  sample module did not build; that is a failure, not a pass:\n%s"
                      % (rs.stdout + rs.stderr)[-400:])
            else:
                print("   mutation-gate sample: %d theorems over %d subjects -> %s"
                      % (len(sthms), len(subs), spath))

    considered = [c for c in cands if c.status != "not_checked"]
    vac_rate = (100.0 * len(vac) / len(considered)) if considered else 0.0
    report = {
        "module": args.module,
        "corpus": os.path.abspath(args.src_root),
        "mode": "synthetic" if args.synthetic else "traced",
        "cross_runtime_evidence": (not args.synthetic),
        "self_recorded_families": ["charact"],
        "self_recorded_note": ("`charact_*` right-hand sides are this interpreter's own "
                               "output. They are characterization/regression theorems "
                               "and are NOT cross-implementation evidence; only "
                               "`conform_*` is, and it needs a runtime this repository "
                               "can drive."),
        "families_unavailable": (["conform", "const", "raises", "projects"]
                                 if args.synthetic else []),
        "subjects_considered": len(subjects),
        "max_subjects": args.max_subjects or None,
        "only_subjects": args.only_subjects,
        "functions": len(funcs),
        "call_closed": len(core),
        "artifacts": art,
        "observations": {"calls": len(recs), "in_core": len(incore),
                         "tests": tests, "skipped": {k: v for k, v in stats.items()
                                                     if k != "test_runs"}},
        "candidates": len(cands),
        "refuted": len(refuted),
        "not_checked": len(nochk),
        "vacuous": len(vac),
        "vacuity_checks": kinds,
        "vacuity_rate_pct": round(vac_rate, 1),
        "emitted": len(survivors),
        "proved": len(proved),
        "open_obligations": len(unproved) + len([c for c in cands
                                                 if c.proved and c.kind == "law"
                                                 and not c.extra.get("fuel_mono")]),
        "build_clean": ok,
        "mutation_sample": sample_info,
        "fuel_independent": len([c for c in cands
                                 if c.proved and c.extra.get("fuel_mono")]),
        "fuel_obligations_remaining": len([c for c in cands
                                           if c.proved
                                           and not c.extra.get("fuel_mono")
                                           and c.kind == "law"]),
        "fuel_blocked_reasons": {c.id: c.extra.get("fuel_mono_reason")
                                 for c in cands
                                 if c.kind == "law" and c.status in ("candidate",
                                                                     "proved")
                                 and not c.extra.get("fuel_mono")},
        "outOfFuel_cases": {c.id: c.extra["outOfFuel_cases"] for c in cands
                            if c.extra.get("outOfFuel_cases")},
        "by_family": {},
        "specs": [c.as_json() for c in cands],
        "not_checked_gates": [
            "scripts/mutate.py — run separately; a surviving mutant means the spec is "
            "vacuous in the sufficient sense",
            "scripts/audit_all.py — axiom basis of the emitted theorems"],
    }
    for c in cands:
        b = report["by_family"].setdefault(c.family, {"candidates": 0, "refuted": 0,
                                                      "vacuous": 0, "proved": 0})
        b["candidates"] += 1
        b["refuted"] += c.status == "refuted"
        b["vacuous"] += c.status == "vacuous"
        b["proved"] += c.proved
    json.dump(report, open(args.json_path, "w"), indent=1)

    print("\n== summary")
    print("   candidates generated : %d" % len(cands))
    print("   refuted by fuzzing   : %d" % len(refuted))
    print("   flagged vacuous      : %d  (%.1f%% of %d screened — FVSpec's rate was "
          "41.0%%)" % (len(vac), vac_rate, len(considered)))
    print("   emitted + proved     : %d" % len(proved))
    print("   open obligations     : %d" % report["open_obligations"])
    print("   fuel-independent     : %d proved for ALL fuel ≥ FUEL (%d still FUEL-only)"
          % (report["fuel_independent"], report["fuel_obligations_remaining"]))
    print("   report               : %s" % args.json_path)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
