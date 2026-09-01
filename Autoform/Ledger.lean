import Lean
import Autoform.Lang.Core.Semantics

/-!
# Trust ledger

The deliverable is never "your codebase is verified". It is a precise statement of what
was translated, what was assumed, and what remains — so a reader can locate the trust
boundary in seconds.

Evidence types here are the domain-specific part (§10 of `STRATEGY.md`); the argument
structure they feed is SACM's, not ours.
-/

namespace Autoform.Core

open Std

/-!
## Static hole-freedom is an upper bound, not a guarantee

`Func.total` (no `Expr.hole`/`Stmt.hole` in the AST) was being reported as "the verifiable
core". Testing showed that claim is too strong: the *interpreter* can introduce holes at
runtime that static counting cannot see.

    def sneaky  := .ret (.field (.name "x") "attr")   -- Func.total = true
    run sneaky 3  ==>  hole "field:attr:non-object"
    run sneaky2 3 ==>  hole "call:not_translated"     -- unresolved call, statically invisible
    run sneaky3 3 ==>  hole "index:unsupported"

The worst of the three is `call:` — a call to a function that was never translated looks
identical, in the AST, to a call to one that was. So the headline coverage number
overstated the verifiable core, and this refines it.

Three tiers are now reported, weakest claim first:

* **hole-free** — no static holes. An upper bound on what could be verified.
* **call-closed** — hole-free *and* every call/method target resolves inside the program.
  Removes the invisible-`call:` failure mode.
* **dynamic-hole risk** — constructs (`field`, `index`, `mcall`, arithmetic that can hit
  `ub`) that can still produce a hole on some input. Reported as a count, not subtracted,
  because whether they *do* is input-dependent and belongs to the conformance oracle.
-/

namespace Analysis

mutual
/-- Names called by an expression, via `call` or `mcall`. -/
def eCalls : Expr → List (Bool × String)
  | .call f as    => (false, f) :: eCallsL as
  | .mcall r m as => (true, m) :: eCalls r ++ eCallsL as
  | .binop _ a b  => eCalls a ++ eCalls b
  | .unop _ a     => eCalls a
  | .index a b    => eCalls a ++ eCalls b
  | .field a _    => eCalls a
  | .alloc _ as   => eCallsL as
  | .listE as     => eCallsL as
  | .tupleE as    => eCallsL as
  | .dictE kvs    => eCallsP kvs
  | .cond c a b   => eCalls c ++ eCalls a ++ eCalls b
  | .isOp _ a b   => eCalls a ++ eCalls b
  | .inOp _ a b   => eCalls a ++ eCalls b
  | _             => []
/-- Names called across a list of expressions. -/
def eCallsL : List Expr → List (Bool × String)
  | []      => []
  | e :: es => eCalls e ++ eCallsL es
/-- Names called across key/value pairs. -/
def eCallsP : List (Expr × Expr) → List (Bool × String)
  | []           => []
  | (k, v) :: ps => eCalls k ++ eCalls v ++ eCallsP ps
end

mutual
/-- Constructs that can produce a hole at runtime even when the AST has none. -/
def eRisk : Expr → Nat
  | .field a _    => 1 + eRisk a
  | .index a b    => 1 + eRisk a + eRisk b
  | .mcall r _ as => 1 + eRisk r + eRiskL as
  | .binop _ a b  => 1 + eRisk a + eRisk b   -- may hit `ub:` under a fixed-width dialect
  | .call _ as    => 1 + eRiskL as           -- may fail to resolve
  | .unop _ a     => eRisk a
  | .alloc _ as   => 1 + eRiskL as
  | .listE as     => eRiskL as
  | .tupleE as    => eRiskL as
  | .dictE kvs    => eRiskP kvs
  | .cond c a b   => eRisk c + eRisk a + eRisk b
  | .isOp _ a b   => eRisk a + eRisk b
  | .inOp _ a b   => 1 + eRisk a + eRisk b
  | _             => 0
/-- Risk across a list of expressions. -/
def eRiskL : List Expr → Nat
  | []      => 0
  | e :: es => eRisk e + eRiskL es
/-- Risk across key/value pairs. -/
def eRiskP : List (Expr × Expr) → Nat
  | []           => 0
  | (k, v) :: ps => eRisk k + eRisk v + eRiskP ps
end

/-- Names called by a statement. -/
def sCalls : Stmt → List (Bool × String)
  | .expr e         => eCalls e
  | .assign _ e     => eCalls e
  | .setField r _ v => eCalls r ++ eCalls v
  | .setIndex r i v => eCalls r ++ eCalls i ++ eCalls v
  | .seq a b        => sCalls a ++ sCalls b
  | .ifte c a b     => eCalls c ++ sCalls a ++ sCalls b
  | .loop c a       => eCalls c ++ sCalls a
  | .forIn _ e b    => eCalls e ++ sCalls b
  | .ret e          => eCalls e
  | .tryCatch b _ h => sCalls b ++ sCalls h
  | .raise e        => eCalls e
  | _               => []

/-- Runtime-hole risk of a statement. -/
def sRisk : Stmt → Nat
  | .expr e         => eRisk e
  | .assign _ e     => eRisk e
  | .setField r _ v => 1 + eRisk r + eRisk v
  | .setIndex _ _ _ => 1
  | .seq a b        => sRisk a + sRisk b
  | .ifte c a b     => eRisk c + sRisk a + sRisk b
  | .loop c a       => eRisk c + sRisk a
  | .forIn _ e b    => 1 + eRisk e + sRisk b
  | .ret e          => eRisk e
  | .tryCatch b _ h => sRisk b + sRisk h
  | .raise e        => eRisk e
  | _               => 0

end Analysis

/-- Calls in this function, each tagged with the dispatch path the interpreter will
take: `true` for a method call (`mcall`, resolved by `Ctx.resolveMethod`), `false` for a
free call (`call`, resolved by `Ctx.resolve`). The tag is the whole point — the two paths
have *different* resolution rules, and a flat `List String` cannot say which applies. -/
def Func.calls (f : Func) : List (Bool × String) := Analysis.sCalls f.body

/-- How many constructs in this function could hole at runtime. -/
def Func.risk (f : Func) : Nat := Analysis.sRisk f.body

/-- Can the interpreter resolve this callee, on the path it will actually take?

Must mirror what `evalExpr` actually does — neither stricter nor looser. The two call
paths do not agree, and collapsing them is how this went wrong twice in opposite
directions:

* **Too strict.** `Ctx.resolve` requires a *unique* suffix match, and applying that rule
  to method calls reported `clear` (9 candidate methods), `__init__` (22) and `pop` (3)
  as unresolvable while the interpreter dispatches them fine — understating the core by
  14 functions. A ledger stricter than the artifact it describes is wrong in the *safe*
  direction, which makes it easy to leave unnoticed, but it still hides the real gap.

* **Too loose.** The fix for that applied `resolveMethod`'s first-match rule to *free*
  calls as well, and `scripts/core_oracle.py` refuted it by execution: `_wrapper` and
  `cache_clear` have several definitions, so the ledger called them resolvable while
  `Ctx.resolve` — which the `call` path really uses — returns `none` on the ambiguity and
  the interpreter holes. That loosening is most of why the claimed core jumped 45 → 74.

So the predicate now takes the dispatch tag from `Func.calls` and answers per path. -/
def Ctx.resolvable (isMethod : Bool) (ctx : Ctx) (n : String) : Bool :=
  if isMethod then
    -- Mirrors `Ctx.resolveMethod`, which takes the *first* match. Still an upper bound:
    -- it asks only whether some class defines the name, not whether *this* receiver's
    -- class does — a static ledger has no receiver.
    ctx.table.any (fun q => q.1.endsWith ("." ++ n))
  else
    -- Mirrors `Ctx.resolve` exactly, ambiguity and all: two suffix matches resolve to
    -- nothing, so two matches must not count as resolvable.
    (ctx.resolve n).isSome
    -- Modelled builtins are resolvable too. `knowsFree` is exact at the name level and is
    -- the *guard* in front of `builtin`, so an unlisted case is dead code rather than a
    -- ledger overstatement — the drift direction that matters cannot rot.
    --
    -- `knowsMethod` is deliberately NOT consulted. It is only an upper bound: methods are
    -- modelled per receiver shape (`pop` is answered on a dict, refused on a str), and a
    -- static ledger has no receiver. Its author measured the pure methods as worth +1
    -- function, so excluding them costs almost nothing and buys an honest number.
    || Stdlib.knowsFree ctx.dialect n

/-! ## Making call closure linear instead of quadratic

`Ctx.resolvable` calls `Ctx.resolve`, which scans the whole function table on every miss.
The ledger asks it once per call site, so computing call closure is O(callsites × table)
— 363 s on a 10k-function corpus.

The obvious fix, a `HashMap` field on `Ctx`, is **not available**: the proofs in
`Autoform/Contracts.lean`, `Autoform/Refine.lean` and `Autoform/CallingConvention.lean`
`simp` through `Ctx.resolve.go` on the association list, so the list shape is load-bearing
for the kernel. So the index lives *here*, is built once per program, and `Ctx.resolve`
itself is untouched — a `git diff` of `Semantics.lean` shows no change to it.

An index is only a speedup if it computes the same answer. It would be very easy for this
one to quietly disagree with `Ctx.resolvable` and inflate the verifiable core, which is
the exact §17/§30 failure this project keeps catching, so:

* the equivalence argument is written out below, in terms of `String.endsWith`;
* `Program.callClosureAgrees` re-derives the answer *both* ways and compares, and
  `#guard`s at the bottom of this file run it on real corpora at elaboration time. A
  disagreement is a build failure, not a silent number.

**The equivalence.** `Ctx.resolve n` looks for an exact key, then for a *unique* key with
`k.endsWith ("." ++ n)`. For a key `k` split on `"."` into `p₀ … pₘ`, the strings `k` ends
with after a dot are exactly the rejoined tails `p₁…pₘ`, `p₂…pₘ`, …, `pₘ` — one per dot,
all of different lengths, so a single key contributes each candidate `n` at most once.
Therefore `suffixCount[n]` counts *keys*, and:

* `(ctx.resolve n).isSome  ↔  exact.contains n ∨ suffixCount[n] = 1`
* `ctx.table.any (·.1.endsWith ("." ++ n))  ↔  suffixCount[n] ≥ 1`

which is what `ResolveIndex.resolvable` evaluates. -/
structure ResolveIndex where
  /-- Keys present verbatim in the table — the exact-match arm of `Ctx.resolve`. -/
  exact : Std.HashSet String
  /-- For each name that some key ends with after a dot, how many keys do. `1` means
  `Ctx.resolve`'s uniqueness condition holds; `≥ 2` means it resolves to `none`. -/
  suffixCount : Std.HashMap String Nat
  deriving Inhabited

/-- Every string `k` ends with immediately after a `'.'`, longest first. `"a.b.c"` gives
`["b.c", "c"]` — and notably *not* `"a.b.c"` itself, matching `endsWith ("." ++ n)`, which
requires a dot to be present. -/
private def nonEmptySuffixes : List String → List (List String)
  | []      => []
  | p :: ps => (p :: ps) :: nonEmptySuffixes ps

def dottedTails (k : String) : List String :=
  match k.splitOn "." with
  | []      => []
  | _ :: ps => (nonEmptySuffixes ps).map (fun t => ".".intercalate t)

def ResolveIndex.build (t : FuncTable) : ResolveIndex :=
  t.foldl (fun idx (k, _) =>
    { exact := idx.exact.insert k
    , suffixCount := (dottedTails k).foldl
        (fun m n => m.insert n ((m.getD n 0) + 1)) idx.suffixCount })
    { exact := ∅, suffixCount := ∅ }

/-- The index's answer to `Ctx.resolvable`. Mirrors it arm for arm, including the
`Stdlib.knowsFree` fallback and the deliberate omission of `knowsMethod`. -/
def ResolveIndex.resolvable (idx : ResolveIndex) (dialect : Dialect)
    (isMethod : Bool) (n : String) : Bool :=
  if isMethod then idx.suffixCount.getD n 0 ≥ 1
  else idx.exact.contains n || idx.suffixCount.getD n 0 == 1
       || Stdlib.knowsFree dialect n

/-- Hole-free **and** every call target resolves inside the program.

The reference definition: `Ctx.resolvable` per call site, quadratic. Kept because it is
the one that obviously mirrors the interpreter, and because it is the thing
`Program.callClosureAgrees` checks the index against. -/
def Program.callClosedRef (p : Program) : List Func :=
  let ctx : Ctx := { dialect := p.dialect, table := p.table }
  p.verifiableCore.filter (fun f => f.calls.all (fun c => ctx.resolvable c.1 c.2))

/-- Hole-free **and** every call target resolves inside the program, via the index. This
is what the ledger reports. -/
def Program.callClosed (p : Program) : List Func :=
  let idx := ResolveIndex.build p.table
  p.verifiableCore.filter (fun f =>
    f.calls.all (fun c => idx.resolvable p.dialect c.1 c.2))

/-- Do the two agree, function for function? Compares the *names*, not just the counts:
two lists of equal length can still be different lists, and it is the membership that the
ledger's claim rests on. -/
def Program.callClosureAgrees (p : Program) : Bool :=
  p.callClosed.map (·.name) == p.callClosedRef.map (·.name)

/-- Per-program translation evidence. -/
structure Coverage where
  funcs      : Nat
  nodes      : Nat
  holes      : Nat
  totalFuncs : Nat
  /-- Hole-free *and* call-closed: the honest verifiable core. -/
  closedFuncs : Nat
  /-- Constructs that can still hole at runtime, across the whole program. -/
  riskNodes  : Nat
  byLabel    : List (String × Nat)
  deriving Repr

/-- Group hole labels by frequency, most common first. -/
def tally (ls : List String) : List (String × Nat) :=
  let m := ls.foldl (fun (m : Std.HashMap String Nat) l =>
    m.insert l ((m.getD l 0) + 1)) ∅
  (m.toList).mergeSort (fun a b => a.2 ≥ b.2)

/-- Compute coverage for a translated program. -/
def Program.coverage (p : Program) : Coverage :=
  let hs    := p.holes
  let nf    := p.funcs.length
  let nodes := p.size
  let core  := p.verifiableCore.length
  let closed := p.callClosed.length
  let risk   := (p.funcs.map Func.risk).sum
  { funcs      := nf
  , nodes      := nodes
  , holes      := hs.length
  , totalFuncs := core
  , closedFuncs := closed
  , riskNodes  := risk
  , byLabel    := tally hs }

/-- Render the ledger. Percentages are of AST nodes, and the verifiable core is the set
of functions with **no** holes — the only ones that can be verified unconditionally. -/
def Program.ledger (p : Program) (name : String) : String :=
  let c := p.coverage
  let pct (a b : Nat) : String :=
    if b == 0 then "n/a" else s!"{(a * 100) / b}%"
  let hdr := s!"
╭─ autoform trust ledger ─ {name}
│ functions translated : {c.funcs}
│ AST nodes            : {c.nodes}
│ holes                : {c.holes}  ({pct c.holes c.nodes} of nodes)
│ hole-free (upper bd) : {c.totalFuncs} / {c.funcs} functions  ({pct c.totalFuncs c.funcs})
│ VERIFIABLE CORE      : {c.closedFuncs} / {c.funcs} functions  ({pct c.closedFuncs c.funcs}) — hole-free AND call-closed
│ dynamic-hole risk    : {c.riskNodes} constructs may hole at runtime (input-dependent)
│ semantics            : Autoform.Core (fuel-indexed, total, no sorry)
│ transpiler           : Joern CPG → Core, deterministic
│ NOT PROVED           : transpiler faithfulness — see conformance.json
├─ holes by cause ─────────────────────────────────────────────"
  let rows := c.byLabel.take 12 |>.map (fun (l, n) => s!"\n│ {n}  {l}")
  let more := if c.byLabel.length > 12 then s!"\n│         … {c.byLabel.length - 12} more labels" else ""
  hdr ++ String.join rows ++ more ++ "\n╰───────────────────────────────────────────────────────────────"

/-- Human-readable dialect name, for the ledger and for provenance in the assurance case. -/
def Dialect.name : Dialect -> String
  | .python     => "python"
  | .cLike      => "c-like"
  | .javascript => "javascript"

/-- Machine-readable ledger, for `scripts/sacm.py` to consume as evidence.

Built with `Lean.Json` rather than string concatenation, and tagged with the module and
dialect explicitly. The SACM pass caught exactly this class of defect in
`conformance.json`: evidence that cannot be attributed to a subject cannot support a
claim about that subject, and was correctly capped at WEAK. -/
def Program.ledgerJson (p : Program) (name : String) : Lean.Json :=
  let c := p.coverage
  Lean.Json.mkObj
    [ ("module",         .str name)
    , ("dialect",        .str p.dialect.name)
    , ("functions",      .num c.funcs)
    , ("nodes",          .num c.nodes)
    , ("holes",          .num c.holes)
    , ("holeFree",       .num c.totalFuncs)
    , ("verifiableCore", .num c.closedFuncs)
    , ("dynamicHoleRisk", .num c.riskNodes)
    , ("holesByLabel",   .arr (c.byLabel.map (fun (l, n) =>
        Lean.Json.mkObj [("label", .str l), ("count", .num n)])).toArray) ]

/-! ## The index, checked against the definition it replaces

A synthetic table covering every arm, including the two that a wrong index would get
wrong in the *flattering* direction: an ambiguous suffix must be unresolvable on the free
path, and a name that is only a *substring* of a key must not match at all. Real corpora
are checked too — `scripts/ledger.lean.tmpl` fails loudly if `callClosureAgrees` is false
for the module being reported. -/
section IndexCheck

private def tbl : FuncTable :=
  [ ("m.py:<module>.helper",      { name := "m.py:<module>.helper",   params := [], body := .skip })
  , ("m.py:<module>.A.clear",     { name := "m.py:<module>.A.clear",  params := [], body := .skip })
  , ("m.py:<module>.B.clear",     { name := "m.py:<module>.B.clear",  params := [], body := .skip })
  , ("plain",                     { name := "plain",                  params := [], body := .skip }) ]

private def ix : ResolveIndex := ResolveIndex.build tbl
private def cx : Ctx := { dialect := .python, table := tbl }

-- Unique suffix: resolvable as a free call, and agrees with `Ctx.resolvable`.
#guard ix.resolvable .python false "helper" == cx.resolvable false "helper"
#guard ix.resolvable .python false "helper" == true
-- Ambiguous suffix (`A.clear` and `B.clear`): `Ctx.resolve` returns `none`, so the free
-- path must say `false`. An index that counted "at least one" would say `true` here and
-- inflate the verifiable core — this is the case that makes the check non-vacuous.
#guard ix.resolvable .python false "clear" == cx.resolvable false "clear"
#guard ix.resolvable .python false "clear" == false
-- The same name on the *method* path is resolvable, because `resolveMethod` takes the
-- first match. The two paths must disagree here; an index collapsing them fails.
#guard ix.resolvable .python true "clear" == cx.resolvable true "clear"
#guard ix.resolvable .python true "clear" == true
-- Exact key with no dot at all.
#guard ix.resolvable .python false "plain" == cx.resolvable false "plain"
#guard ix.resolvable .python false "plain" == true
-- A substring that is not a dotted tail: `"lper"` must not match `".helper"`.
#guard ix.resolvable .python false "lper" == cx.resolvable false "lper"
#guard ix.resolvable .python false "lper" == false
#guard ix.resolvable .python true "lper" == cx.resolvable true "lper"
-- A modelled builtin is resolvable on the free path even though it is not in the table.
#guard ix.resolvable .python false "len" == cx.resolvable false "len"
-- The tail decomposition itself.
#guard dottedTails "m.py:<module>.A.clear" == ["py:<module>.A.clear", "A.clear", "clear"]
#guard dottedTails "plain" == []

end IndexCheck

/-- The names of functions that can be verified unconditionally. -/
def Program.coreNames (p : Program) : List String :=
  p.callClosed.map (·.name)

end Autoform.Core
