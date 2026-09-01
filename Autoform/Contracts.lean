import Lean
import Autoform.Refine
import Autoform.Generated.Cachetools

/-!
# Contracts at holes

`STRATEGY.md` §5: *"Proof burden grows superlinearly with program size. Hence: verified
core + contracts, never whole-repo."* `Refine.lean` built the verified-core half. This
file builds the contracts half.

## The problem

`Expr.hole l` evaluates to `EResult.hole l`, `Stmt.hole l` to `Ctl.hole l`, and
`Refine.Outcome` deliberately has no `hole` constructor — so `refines_not_hole` says a
refined function provably never reaches an untranslated construct. That is the right
default and it is not being weakened here. Its cost is that **one** hole anywhere in a
function puts the entire function outside anything we can state: on `cachetools`, 165 of
238 functions are hole-free and 74 are call-closed, so roughly 70% of the code is
currently unspeakable.

## The mechanism

A contract is an *opt-in assumption about one hole*. Given a hole labelled
`op:starredUnpack`, a contract says: "every implementation of this construct, run with at
least `fuel` budget, satisfies `post`". Then

    RefinesUnder Γ p name N dom spec

says: **for every** way of filling the contracted holes that satisfies Γ, the resulting
program refines `spec`. It is a universally quantified statement over implementations,
not a re-definition of the semantics. Three consequences follow, and each is a theorem
below rather than a comment:

* With `Γ = []` there is nothing to fill, and `RefinesUnder` is *literally* `Refines`
  (`refinesUnder_nil_iff`). The two are therefore not confusable: a contract-relative
  theorem carries its `Γ` in its statement.
* If Γ is **unsatisfiable** — no implementation at all meets it — then `RefinesUnder Γ`
  holds for *every* spec (`refinesUnder_of_unsatisfiable`). This is the failure mode of
  every contract system stated as a theorem: an inconsistent assumption set is a machine
  for assuming your conclusion. Hence `Satisfiable` is a proof obligation, not a comment.
* If Γ **is** satisfiable, contracts still cannot prove two different things
  (`refinesUnder_unique`), which is the `refines_unique` guarantee recovered relative to Γ.

And the honest default has teeth: a contract that assumes *nothing* about a hole
(`topContract`) proves nothing at all — `methodkey_not_refinable_under_top` shows a real
`cachetools` function is provably unrefinable under it, because leaving the hole in place
is itself a legal implementation.

## What a contract-relative theorem is worth

Exactly the truth of its contracts. Nothing here discharges them; `ContractEnv.assumptions`
exists to hand them to `scripts/sacm.py` as named `Assumption` nodes **of that theorem**.
See `docs/contracts.md` for what a reader must check.
-/

namespace Autoform.Contracts

open Autoform.Core Autoform.Refine

/-! ## 1. Contracts -/

/-- A contract on one hole label.

* `post` is the load-bearing part: a predicate on the pre-heap, the environment at the
  hole site, and the pair the interpreter is assumed to produce. It ranges over the whole
  `Heap × EResult`, so an implementation is free to mutate the heap, raise, or return —
  and an *unconstrained* hole is exactly `post := fun _ _ _ => True`, which is the honest
  default and provably useless (`methodkey_not_refinable_under_top`).
* `fuel` is the budget the implementation is assumed to need. Without it the fuel bound
  `N` of a `RefinesUnder` theorem would be a lie: the cost of the untranslated construct
  has to appear somewhere, so it appears here.
* `stmt` is **unchecked prose** for the assurance case. It is never used in any proof;
  a wrong `stmt` misleads a human reader and cannot mislead the kernel. `docs/contracts.md`
  lists checking `stmt` against `post` as a reader obligation.
-/
structure Contract where
  /-- The CPG hole label this contract is about, e.g. `op:starredUnpack`. -/
  label : String
  /-- Human-readable rendering of `post`, for SACM. Unchecked. -/
  stmt  : String
  /-- Fuel budget the hole's implementation is assumed to need. -/
  fuel  : Nat
  /-- The assumed behaviour: `post h ρ (h', r)` for the hole evaluated in heap `h`,
  environment `ρ`, yielding heap `h'` and result `r`. -/
  post  : Heap → Env → Heap × EResult → Prop

/-- A contract environment: the assumptions a theorem is relative to. -/
abbrev ContractEnv := List Contract

/-- The hole labels a contract environment speaks about. -/
def ContractEnv.labels (Γ : ContractEnv) : List String := Γ.map (·.label)

/-! ## 2. Implementations

A contract constrains; an *implementation* is a witness. Filling a hole means replacing
`Expr.hole l` by an ordinary `Expr`, so implementations stay inside the language and the
semantics is untouched — there is no second interpreter to trust. -/

/-- A way of filling holes: hole label ↦ replacement expression. -/
abbrev Impl := List (String × Expr)

/-- The labels an implementation fills. -/
def Impl.labels (σ : Impl) : List String := σ.map (·.1)

mutual
/-- Substitute implementations for holes in an expression. -/
def substE (σ : Impl) : Expr → Expr
  | .hole l        => match σ.lookup l with
                      | some e => e
                      | none   => .hole l
  | .binop o a b   => .binop o (substE σ a) (substE σ b)
  | .unop o a      => .unop o (substE σ a)
  | .index a b     => .index (substE σ a) (substE σ b)
  | .field a f     => .field (substE σ a) f
  | .call f as     => .call f (substEL σ as)
  | .mcall r m as  => .mcall (substE σ r) m (substEL σ as)
  | .alloc c as    => .alloc c (substEL σ as)
  | .listE as      => .listE (substEL σ as)
  | .tupleE as     => .tupleE (substEL σ as)
  | .dictE kvs     => .dictE (substEP σ kvs)
  | .cond c a b    => .cond (substE σ c) (substE σ a) (substE σ b)
  | .isOp n a b    => .isOp n (substE σ a) (substE σ b)
  | .inOp n a b    => .inOp n (substE σ a) (substE σ b)
  | .starred a     => .starred (substE σ a)
  | .kwargE k a    => .kwargE k (substE σ a)
  | .dstarred a    => .dstarred (substE σ a)
  | .boxNew a      => .boxNew (substE σ a)
  | .boxFields kvs => .boxFields (substEP σ kvs)
  | .irefIndex a i => .irefIndex (substE σ a) (substE σ i)
  | .irefField a f => .irefField (substE σ a) f
  | .derefIref a   => .derefIref (substE σ a)
  | .lit l         => .lit l
  | .name x        => .name x
  | .fnref f       => .fnref f
  | .closure f     => .closure f
  | .classClosure c => .classClosure c

/-- Substitution across a list of expressions. -/
def substEL (σ : Impl) : List Expr → List Expr
  | []      => []
  | e :: es => substE σ e :: substEL σ es

/-- Substitution across key/value expression pairs. -/
def substEP (σ : Impl) : List (Expr × Expr) → List (Expr × Expr)
  | []           => []
  | (k, v) :: ps => (substE σ k, substE σ v) :: substEP σ ps
end

/-- Substitute implementations for holes in a statement.

`Stmt.hole` is **not** filled: a statement-level hole is an untranslated *effect*, and
filling it with an expression would be a category error. Statement holes therefore remain
outside the mechanism, which is the conservative direction — see `docs/contracts.md`. -/
def substS (σ : Impl) : Stmt → Stmt
  | .expr e          => .expr (substE σ e)
  | .assign x e      => .assign x (substE σ e)
  | .setField r f v  => .setField (substE σ r) f (substE σ v)
  | .setIndex r i v  => .setIndex (substE σ r) (substE σ i) (substE σ v)
  | .setDerefIref p v => .setDerefIref (substE σ p) (substE σ v)
  | .seq a b         => .seq (substS σ a) (substS σ b)
  | .ifte c a b      => .ifte (substE σ c) (substS σ a) (substS σ b)
  | .loop c a        => .loop (substE σ c) (substS σ a)
  | .forIn x e b     => .forIn x (substE σ e) (substS σ b)
  | .ret e           => .ret (substE σ e)
  | .tryCatch b x hd => .tryCatch (substS σ b) x (substS σ hd)
  | .tryFinally b f  => .tryFinally (substS σ b) (substS σ f)
  | .raise e         => .raise (substE σ e)
  | .setGlobal x e   => .setGlobal x (substE σ e)
  | .skip            => .skip
  | .brk             => .brk
  | .cont            => .cont
  | .del x           => .del x
  | .declGlobal x    => .declGlobal x
  | .hole l          => .hole l

/-- Apply an implementation to a function. Name and parameters are untouched, so name
resolution in the instantiated program is the same as in the original. -/
def Impl.onFunc (σ : Impl) (f : Func) : Func := { f with body := substS σ f.body }

/-- Apply an implementation to a whole program. -/
def Impl.onProgram (σ : Impl) (p : Program) : Program :=
  { p with funcs := p.funcs.map σ.onFunc }

/-! ### The empty implementation changes nothing

Needed for `refinesUnder_nil_iff`, and worth having independently: it says substitution
is not quietly rewriting the program. -/

mutual
theorem substE_nil : ∀ e : Expr, substE [] e = e
  | .hole _        => rfl
  | .lit _         => rfl
  | .name _        => rfl
  | .fnref _       => rfl
  | .closure _     => rfl
  | .classClosure _ => rfl
  | .binop o a b   => by rw [substE, substE_nil a, substE_nil b]
  | .unop o a      => by rw [substE, substE_nil a]
  | .index a b     => by rw [substE, substE_nil a, substE_nil b]
  | .field a f     => by rw [substE, substE_nil a]
  | .call f as     => by rw [substE, substEL_nil as]
  | .mcall r m as  => by rw [substE, substE_nil r, substEL_nil as]
  | .alloc c as    => by rw [substE, substEL_nil as]
  | .listE as      => by rw [substE, substEL_nil as]
  | .tupleE as     => by rw [substE, substEL_nil as]
  | .dictE kvs     => by rw [substE, substEP_nil kvs]
  | .cond c a b    => by rw [substE, substE_nil c, substE_nil a, substE_nil b]
  | .starred a     => by rw [substE, substE_nil a]
  | .kwargE k a    => by rw [substE, substE_nil a]
  | .dstarred a    => by rw [substE, substE_nil a]
  | .isOp n a b    => by rw [substE, substE_nil a, substE_nil b]
  | .inOp n a b    => by rw [substE, substE_nil a, substE_nil b]
  | .boxNew a      => by rw [substE, substE_nil a]
  | .boxFields kvs => by rw [substE, substEP_nil kvs]
  | .irefIndex a i => by rw [substE, substE_nil a, substE_nil i]
  | .irefField a f => by rw [substE, substE_nil a]
  | .derefIref a   => by rw [substE, substE_nil a]

theorem substEL_nil : ∀ es : List Expr, substEL [] es = es
  | []      => rfl
  | e :: es => by rw [substEL, substE_nil e, substEL_nil es]

theorem substEP_nil : ∀ ps : List (Expr × Expr), substEP [] ps = ps
  | []           => rfl
  | (k, v) :: ps => by rw [substEP, substE_nil k, substE_nil v, substEP_nil ps]
end

theorem substS_nil : ∀ s : Stmt, substS [] s = s
  | .skip | .brk | .cont | .del _ | .declGlobal _ | .hole _ => rfl
  | .expr e          => by rw [substS, substE_nil e]
  | .assign x e      => by rw [substS, substE_nil e]
  | .setField r f v  => by rw [substS, substE_nil r, substE_nil v]
  | .setIndex r i v  => by rw [substS, substE_nil r, substE_nil i, substE_nil v]
  | .setDerefIref p v => by rw [substS, substE_nil p, substE_nil v]
  | .seq a b         => by rw [substS, substS_nil a, substS_nil b]
  | .ifte c a b      => by rw [substS, substE_nil c, substS_nil a, substS_nil b]
  | .loop c a        => by rw [substS, substE_nil c, substS_nil a]
  | .forIn x e b     => by rw [substS, substE_nil e, substS_nil b]
  | .ret e           => by rw [substS, substE_nil e]
  | .tryCatch b x hd => by rw [substS, substS_nil b, substS_nil hd]
  | .tryFinally b f  => by rw [substS, substS_nil b, substS_nil f]
  | .raise e         => by rw [substS, substE_nil e]
  | .setGlobal x e   => by rw [substS, substE_nil e]

@[simp] theorem onFunc_nil (f : Func) : Impl.onFunc [] f = f := by
  simp [Impl.onFunc, substS_nil]

@[simp] theorem onProgram_nil (p : Program) : Impl.onProgram [] p = p := by
  simp [Impl.onProgram, List.map_id'']

/-! ## 3. Consistency, satisfiability, and `RefinesUnder` -/

/-- `Consistent Γ p σ`: the implementation `σ` is a legal witness for the contracts `Γ`
in program `p`.

Two clauses, both load-bearing:

* **`σ` may only fill labels `Γ` speaks about.** Without this clause a "contract-relative"
  theorem could silently repair holes nobody declared, and `refinesUnder_nil_iff` would be
  false. The contract environment is therefore an exact inventory of what was assumed.
* **Every filled hole really behaves as its contract says**, at every fuel budget at or
  above the contract's declared `fuel`, in every heap and every environment. Universal
  quantification over `h` and `ρ` is what makes a contract a statement about the
  *construct* rather than about one call site.
* **Every replacement is an ordinary expression**, i.e. not one of the three argument
  *forms* `starred` / `kwargE` / `dstarred`. Those are not expressions that produce a
  value: `f(*xs)` passes several arguments and `f(**d)` passes none positionally, so
  substituting one into an argument list changes the call's **arity**, which no `post` —
  a predicate on `evalExpr`'s single `Heap × EResult` — can describe. Admitting them
  would make `Consistent` claim to constrain something it does not.

  This is a genuine narrowing of `RefinesUnder`: it now quantifies over strictly fewer
  implementations than before argument forms existed, so a contract-relative theorem
  says slightly less. It is recorded here rather than hidden because the alternative —
  quantifying over implementations whose behaviour the contract cannot state — would be
  unsound, not merely imprecise. Every witness in this file (`.hole l`, `.lit`, `.binop`)
  is plain, so nothing below is weakened in practice. -/
def Consistent (Γ : ContractEnv) (p : Program) (σ : Impl) : Prop :=
  (∀ l ∈ σ.labels, l ∈ Γ.labels) ∧
  (∀ c ∈ Γ, ∀ e, σ.lookup c.label = some e →
     ∀ k, c.fuel ≤ k → ∀ h ρ, c.post h ρ (evalExpr (ctxOf (σ.onProgram p)) k h ρ e)) ∧
  (∀ l e, σ.lookup l = some e → e.plainArg = true)

/-- `σ` fills every hole `Γ` speaks about. A partial witness would leave a contracted
hole in place and the "refinement" would be about a program that still holes. -/
def Total (Γ : ContractEnv) (σ : Impl) : Prop :=
  ∀ c ∈ Γ, (σ.lookup c.label).isSome

/-- **The contracts are satisfiable**: some implementation actually meets them.

This is the anti-vacuity obligation, and it is not decorative — see
`refinesUnder_of_unsatisfiable`. §4's discipline is that a specification must be shown to
constrain something; for an assumption the corresponding obligation is that it can be
met. -/
def Satisfiable (Γ : ContractEnv) (p : Program) : Prop :=
  ∃ σ, Consistent Γ p σ ∧ Total Γ σ

/-- **Refinement relative to a contract environment.**

`RefinesUnder Γ p name N dom spec`: for *every* implementation of the contracted holes
that satisfies `Γ`, the instantiated program refines `spec` in the ordinary
`Refine.Refines` sense — same `Outcome` type with no `hole` and no `outOfFuel`, same
universally quantified fuel above the concrete bound `N`, same explicit domain.

Nothing about `Refines` is weakened. What is weakened is *which program* the claim is
about: not `p`, but every instantiation of `p` consistent with `Γ`. That is strictly less
than a claim about `p` itself, and the difference is exactly `Γ`. -/
def RefinesUnder (Γ : ContractEnv) (p : Program) (name : String) (N : Nat)
    (dom : List Val → Prop) (spec : List Val → Outcome) : Prop :=
  ∀ σ, Consistent Γ p σ → Total Γ σ → Refines (σ.onProgram p) name N dom spec

/-! ### Relationship to `Refines` -/

/-- **No contracts, no difference.** With an empty contract environment `RefinesUnder`
*is* `Refines`, in both directions.

The `←` direction is the one that needs the "only contracted labels" clause of
`Consistent`: it forces `σ = []`, so the instantiated program is `p` itself. Together
with the fact that `Γ` appears in the statement of every contract-relative theorem, this
is what keeps the two claims unconfusable — a theorem is unconditional iff its `Γ` is
literally `[]`. -/
theorem refinesUnder_nil_iff (p : Program) (name : String) (N : Nat)
    (dom : List Val → Prop) (spec : List Val → Outcome) :
    RefinesUnder [] p name N dom spec ↔ Refines p name N dom spec := by
  constructor
  · intro h
    have hcons : Consistent [] p [] := by
      refine ⟨?_, ?_, ?_⟩
      · intro l hl; cases hl
      · intro c hc; cases hc
      · intro l e hl; cases hl
    have htot : Total [] [] := by intro c hc; cases hc
    simpa using h [] hcons htot
  · intro h σ hc _
    have hσ : σ = [] := by
      cases σ with
      | nil => rfl
      | cons a as =>
        exact absurd (hc.1 a.1 (by simp [Impl.labels])) (by simp [ContractEnv.labels])
    subst hσ; simpa using h

/-- A contract-relative theorem becomes an ordinary one exactly when the contracts are
**discharged**: exhibit an implementation, prove it consistent, and the refinement holds
of the instantiated program. This is the only route from `RefinesUnder` to `Refines`, and
it terminates in `Refines (σ.onProgram p)` — a claim about the *repaired* program, never
silently about `p`. -/
theorem RefinesUnder.discharge {Γ p name N dom spec} (h : RefinesUnder Γ p name N dom spec)
    {σ : Impl} (hc : Consistent Γ p σ) (ht : Total Γ σ) :
    Refines (σ.onProgram p) name N dom spec := h σ hc ht

/-- Under contracts, the instantiated program still never reaches an untranslated hole
and still terminates. `Refine`'s non-vacuity theorems survive relativisation — what a
contract buys is a *different program*, not a laxer notion of refinement. -/
theorem refinesUnder_not_hole {Γ p name N dom spec} (h : RefinesUnder Γ p name N dom spec)
    {σ : Impl} (hc : Consistent Γ p σ) (ht : Total Γ σ)
    (args : List Val) (hd : dom args) (fuel : Nat) (hf : N ≤ fuel) (l : String) :
    runFunc (σ.onProgram p) fuel name args ≠ .hole l :=
  refines_not_hole (h σ hc ht) args hd fuel hf l

/-! ### The failure mode, stated as theorems

A contract mechanism is a machine for assuming your conclusion. The two theorems below
are what make that visible rather than latent. -/

/-- **An unsatisfiable contract environment proves everything.**

If no implementation meets `Γ`, then `RefinesUnder Γ` holds for every entry point, every
fuel bound, every domain and every specification — including contradictory ones. This is
not a defect to be patched; it is the definition of assuming a falsehood, and the useful
thing is to have it in the open. Its immediate corollary is the reader obligation in
`docs/contracts.md`: **a contract-relative theorem is worthless until `Satisfiable Γ p`
is proved.** -/
theorem refinesUnder_of_unsatisfiable {Γ p} (h : ¬ Satisfiable Γ p)
    (name : String) (N : Nat) (dom : List Val → Prop) (spec : List Val → Outcome) :
    RefinesUnder Γ p name N dom spec := by
  intro σ hc ht
  exact absurd ⟨σ, hc, ht⟩ h

/-- Contradiction is *detectable*: a contract whose `post` is unsatisfiable makes the
whole environment unsatisfiable, in any program. Nothing about the hole's implementation
is needed — the contract cannot be met by anything, which is precisely why it would
otherwise prove anything. -/
theorem unsatisfiable_of_false_post {Γ : ContractEnv} {p : Program} {c : Contract}
    (hmem : c ∈ Γ) (hfalse : ∀ h ρ st, ¬ c.post h ρ st) : ¬ Satisfiable Γ p := by
  rintro ⟨σ, hc, ht⟩
  have hs := ht c hmem
  match hlk : σ.lookup c.label with
  | none   => rw [hlk] at hs; exact absurd hs (by simp)
  | some e =>
    exact hfalse [] [] _ (hc.2.1 c hmem e hlk c.fuel (Nat.le_refl _) [] [])

/-- **Satisfiable contracts still cannot prove two different things.**

`Refine.refines_unique` says a program determines its shallow model. The relative form:
if `Γ` can be met at all, then two specs proved under the *same* `Γ` agree on the domain.
So a satisfiable contract environment is not a licence to conclude anything — it is
exactly as constraining as the program plus `Γ`.

Note what this does **not** say: two specs proved under *different* contract environments
need not agree, and must not be expected to. `methodkey_refinesUnder_value` and
`methodkey_refinesUnder_raise` below are a concrete pair. -/
theorem refinesUnder_unique {Γ p name N₁ N₂ dom s₁ s₂}
    (hsat : Satisfiable Γ p)
    (h₁ : RefinesUnder Γ p name N₁ dom s₁) (h₂ : RefinesUnder Γ p name N₂ dom s₂)
    (args : List Val) (hd : dom args) : (s₁ args).toEResult = (s₂ args).toEResult := by
  obtain ⟨σ, hc, ht⟩ := hsat
  exact refines_unique (h₁ σ hc ht) (h₂ σ hc ht) args hd

/-- Contracts compose in the safe direction: assuming *more* labels can only weaken the
claim, never strengthen it. Formally, an environment that constrains a superset of labels
admits at least the implementations of the smaller one, so a theorem proved under `Γ`
survives under any `Γ'` whose consistent, total implementations are among `Γ`'s. -/
theorem refinesUnder_weaken {Γ Γ' p name N dom spec}
    (hsub : ∀ σ, Consistent Γ' p σ → Total Γ' σ → Consistent Γ p σ ∧ Total Γ σ)
    (h : RefinesUnder Γ p name N dom spec) : RefinesUnder Γ' p name N dom spec := by
  intro σ hc ht
  obtain ⟨hc', ht'⟩ := hsub σ hc ht
  exact h σ hc' ht'

/-! ## 4. Standard contracts

Three, spanning the useful range. `topContract` is the honest default for a hole nobody
has looked at; the other two are what a human asserts after looking. -/

/-- **Assume nothing.** The hole may do anything at all: mutate the heap, raise, return,
or remain a hole. Always satisfiable, and provably useless — see
`methodkey_not_refinable_under_top`. This is what an undeclared hole *means*, made
explicit. -/
def topContract (l : String) : Contract :=
  { label := l, fuel := 0
  , stmt  := s!"the construct `{l}` may do anything (no assumption)"
  , post  := fun _ _ _ => True }

/-- **Assume the hole is a pure value producer**: it terminates, returns some value, does
not raise, and does not touch the heap. This is the weakest contract that lets a proof
walk *through* a hole, and it is a real assumption: `op:starredUnpack` in CPython can
raise `TypeError` on a non-iterable, so a theorem using this contract is conditional on
the unpacked argument being iterable. -/
def pureValueContract (l : String) : Contract :=
  { label := l, fuel := 1
  , stmt  := s!"`{l}` terminates, returns a value, raises nothing, and does not mutate the heap"
  , post  := fun h _ st => st.1 = h ∧ ∃ v, st.2 = .val v }

/-- **Assume the hole raises**, with a named payload and no heap effect. Exceptions are
behaviour, not ignorance (`Refine`'s `Outcome.raise`), so this is a genuine specification
of a hole rather than a way of hiding it. -/
def raisesContract (l : String) (payload : Val) : Contract :=
  { label := l, fuel := 2
  , stmt  := s!"`{l}` raises, with no heap effect"
  , post  := fun h _ st => st = (h, .exn payload) }

/-- Any contract whose `post` is `True` is met by leaving the hole exactly where it is:
the identity implementation. So `topContract` environments are always satisfiable — which
is the point. They are consistent *and* worthless, the two properties that together show
satisfiability is necessary but not sufficient. -/
theorem satisfiable_top (l : String) (p : Program) :
    Satisfiable [topContract l] p :=
  ⟨[(l, .hole l)],
   ⟨by intro l' hl'; simp [Impl.labels] at hl'; simp [ContractEnv.labels, topContract, hl'],
    by intro c hc e _ k _ h ρ; simp at hc; subst hc; trivial,
    by intro l' e he
       simp only [List.lookup] at he
       split at he
       · cases he; rfl
       · simp_all⟩,
   by intro c hc; simp at hc; subst hc; simp [topContract]⟩

/-! ## 5. Extracting the assumptions

`Ledger.lean` and `scripts/sacm.py` turn every hole label into a named SACM `Assumption`
node of the *module*. A contract-relative theorem needs finer granularity: these are
assumptions of **that theorem**, and the assurance case should say so, because discharging
them is a different piece of work from discharging the module's other holes. -/

/-- One SACM `Assumption` node, derived from one contract. -/
structure Assumption where
  /-- The CPG hole label. Matches the labels `Ledger.tally` already counts. -/
  label : String
  /-- Unchecked prose from `Contract.stmt`. -/
  statement : String
  /-- The fuel budget assumed for the construct. -/
  fuelBound : Nat
  deriving Repr, DecidableEq

/-- The assumptions a contract environment represents. -/
def ContractEnv.assumptions (Γ : ContractEnv) : List Assumption :=
  Γ.map fun c => { label := c.label, statement := c.stmt, fuelBound := c.fuel }

/-- Machine-readable assumption record for one contract-relative theorem.

`theoremName` is the Lean declaration the assumptions belong to; `satisfiable` records
whether a `Satisfiable Γ p` proof exists and names it. A `false` there is not a warning,
it is a disqualification: by `refinesUnder_of_unsatisfiable` the theorem carries no
information until it is `true`. `scripts/sacm.py` should cap any claim supported by such
a theorem at the same level it caps unattributed evidence. -/
def assumptionsJson (theoremName : String) (Γ : ContractEnv)
    (satisfiabilityProof : Option String) : Lean.Json :=
  Lean.Json.mkObj
    [ ("theorem", .str theoremName)
    , ("relativeTo", .arr (Γ.assumptions.map (fun a =>
        Lean.Json.mkObj
          [ ("label", .str a.label)
          , ("statement", .str a.statement)
          , ("fuelBound", .num a.fuelBound) ])).toArray)
    , ("satisfiable", .bool satisfiabilityProof.isSome)
    , ("satisfiabilityProof",
        match satisfiabilityProof with | some n => .str n | none => .null) ]


/-! ## 6. A real function, proved under a contract

`cachetools/keys.py:methodkey` is

```python
def methodkey(self, *args, **kwargs):
    return hashkey(*args, **kwargs)
```

and until the calling convention was modelled the transpiler emitted it with exactly one
hole:

```lean
body := .seq (.expr (.lit (.str "…docstring…")))
          (.seq .skip (.ret (.call "hashkey" [(.hole "op:starredUnpack")])))
```

`op:starredUnpack` was the most common hole label in the corpus (36 occurrences on the
committed AST), and this single node was the entire reason `methodkey` sat outside the
verifiable core.

**It no longer does.** `Core.Expr` now has `starred`/`kwargE`/`dstarred`, `Core.Func` has
`vararg`/`kwarg`, and the exporter emits them, so the generated body is

```lean
.ret (.call "cachetools/keys.py:<module>.hashkey"
        [(.starred (.name "args")), (.dstarred (.name "kwargs"))])
```

with no hole at all. `methodkey_refines` below is therefore **unconditional** — the same
conclusion the contract-relative theorem reached, now with an empty `Γ`.

That would leave this section with nothing to demonstrate contracts *on*, so the
contract-relative theorems are kept and re-pointed at `keysProgramHoled`: `methodkey`
**exactly as the transpiler used to emit it**, with the starred call replaced by
`Expr.hole "op:starredUnpack"`. Nothing about the mechanism changed; what changed is that
the worked example is now a historical program rather than the current one, and this
paragraph is the only thing standing between a reader and mistaking one for the other.

The `Func` values below are **the generated ones, imported unedited** from
`Autoform/Generated/Cachetools.lean`.

**Scope, stated rather than glossed.** The theorems are about a two-function program, not
about all of `cachetools`. That matters for exactly one thing — name resolution: `.call
"hashkey"` is resolved by `Ctx.resolve`'s unique-suffix rule, which could in principle
answer differently in a 238-function table. The `#eval`s at the end of this section check
that the full program agrees; they are evidence, not proof, and `docs/contracts.md` lists
this as a reader obligation. -/

namespace Demo

open Autoform.Generated.Cachetools

set_option maxRecDepth 40000

/-- `methodkey` together with the `hashkey` it calls, verbatim from the generated module. -/
def keysProgram : Program := { dialect := .python, funcs :=
  [ f_cachetools_keys_py__module__hashkey
  , f_cachetools_keys_py__module__methodkey ] }

/-- `keys.py` records no class with a builtin base, so `Expr.alloc "_HashedTuple"` takes
the ordinary heap-allocation branch. Stated as a lemma so the evaluation `simp`s below can
step past `Ctx.builtinBase` without unfolding the program. -/
@[simp] theorem builtinBase_keysProgram (cls : String) :
    (ctxOf keysProgram).builtinBase cls = none := rfl

/-! ### The instantiated program, and its name resolution

`Ctx.resolve` falls back to a *unique suffix* match over the function table, and
`Ctx.resolveMethod` to a class-qualified one. Those are the only places where a
two-function slice could behave differently from the whole corpus, so they are discharged
here as four named lemmas rather than buried inside an evaluation proof. -/

/-- `methodkey` with its single hole implemented by `e`. -/
def methodkeyWith (e : Expr) : Func :=
  { name   := "cachetools/keys.py:<module>.methodkey"
  , params := ["args", "kwargs"]
  , vararg := some "args"
  , kwarg  := some "kwargs"
  , body := (.seq (.expr (.lit (.str "\"\"Return a cache key for use with cached methods.\"\"")))
              (.seq .skip (.ret (.call "hashkey" [e])))) }

/-- The instantiated program. -/
def keysProgramWith (e : Expr) : Program := { dialect := .python, funcs :=
  [ f_cachetools_keys_py__module__hashkey, methodkeyWith e ] }

/-- The `keys.py` fragment records no class with a builtin base, so `Expr.alloc
"_HashedTuple"` takes the ordinary heap-allocation branch. Stated as a lemma so the
evaluation `simp`s below can step past `Ctx.builtinBase` without unfolding the whole
program. -/
@[simp] theorem builtinBase_keysProgramWith (e : Expr) (cls : String) :
    (ctxOf (keysProgramWith e)).builtinBase cls = none := rfl

/-- `methodkey` **as the transpiler used to emit it**: the starred call replaced by the
hole it produced before `Expr.starred`/`Expr.dstarred` existed. This is the subject of the
contract-relative theorems below; `keysProgram` above is the current program. -/
def keysProgramHoled : Program := keysProgramWith (.hole "op:starredUnpack")

/-- Any implementation of the one contracted label turns `keysProgramHoled` into
`keysProgramWith`. Note that names and parameters are untouched — which is why the
resolution lemmas below are about the instantiated program and still describe the
original. -/
theorem onProgram_keysProgramHoled {σ : Impl} {e : Expr}
    (he : σ.lookup "op:starredUnpack" = some e) :
    σ.onProgram keysProgramHoled = keysProgramWith e := by
  simp [Impl.onProgram, Impl.onFunc, keysProgramHoled, keysProgramWith, methodkeyWith, keysProgramWith, methodkeyWith,
    substS, substE, substEL, he, f_cachetools_keys_py__module__hashkey]

theorem table_keysProgramWith (e : Expr) : (keysProgramWith e).table =
    [ ("cachetools/keys.py:<module>.hashkey", f_cachetools_keys_py__module__hashkey)
    , ("cachetools/keys.py:<module>.methodkey", methodkeyWith e) ] := by
  simp [Program.table, keysProgramWith, methodkeyWith,
    f_cachetools_keys_py__module__hashkey, f_cachetools_keys_py__module__methodkey]

/-- The entry point resolves, by exact match on the fully qualified CPG name. -/
theorem resolve_methodkey (e : Expr) :
    (ctxOf (keysProgramWith e)).resolve "cachetools/keys.py:<module>.methodkey"
      = some (methodkeyWith e) := by
  simp +decide [Ctx.resolve, ctxOf, table_keysProgramWith, methodkeyWith,
    f_cachetools_keys_py__module__methodkey]

/-- The call `hashkey(...)` resolves, and *uniquely* — the suffix rule finds exactly one
candidate. This is the fact the `#eval` cross-checks below re-run on the full program. -/
theorem resolve_hashkey (e : Expr) :
    (ctxOf (keysProgramWith e)).resolve "hashkey"
      = some f_cachetools_keys_py__module__hashkey := by
  simp only [Ctx.resolve, ctxOf, table_keysProgramWith, methodkeyWith,
    f_cachetools_keys_py__module__methodkey, f_cachetools_keys_py__module__hashkey]
  rw [show ("." ++ "hashkey") = ".hashkey" from by rfl]
  simp +decide [Ctx.resolve.go, String.endsWith]

/-- `kwargs` is not a function. `hashkey`'s `if kwargs:` reads its own `**kwargs`
parameter, which the call `hashkey(e)` leaves as the empty `dict` — falsy — so the
`**kwargs` branch is not taken. (Before the calling convention existed the name was
unbound and read as `unit`, also falsy; the branch taken is the same either way.) -/
theorem resolve_kwargs (e : Expr) : (ctxOf (keysProgramWith e)).resolve "kwargs" = none := by
  simp only [Ctx.resolve, ctxOf, table_keysProgramWith, methodkeyWith,
    f_cachetools_keys_py__module__methodkey, f_cachetools_keys_py__module__hashkey]
  rw [show ("." ++ "kwargs") = ".kwargs" from by rfl]
  simp +decide [Ctx.resolve.go, String.endsWith]

/-- `_HashedTuple` has no translated `__init__`, so `Expr.alloc` returns the fresh
reference without running one — and the unpacked arguments are therefore not observable in
`methodkey`'s result. -/
theorem resolveMethod_hashedTuple_init (e : Expr) :
    (ctxOf (keysProgramWith e)).resolveMethod "_HashedTuple" "__init__" = none := by
  simp only [Ctx.resolveMethod, ctxOf, table_keysProgramWith, methodkeyWith,
    f_cachetools_keys_py__module__methodkey, f_cachetools_keys_py__module__hashkey]
  rw [show ("." ++ "_HashedTuple" ++ "." ++ "__init__") = "._HashedTuple.__init__" from by rfl]
  simp +decide [List.filter_cons, String.endsWith]
  simp only [Ctx.resolve, ctxOf, table_keysProgramWith]
  rw [show ("." ++ "__init__") = ".__init__" from by rfl]
  simp +decide [Ctx.resolve.go, String.endsWith, methodkeyWith,
    f_cachetools_keys_py__module__methodkey, f_cachetools_keys_py__module__hashkey]

/-- `runFunc` builds its context inline; folding it back to `ctxOf` is what lets the
resolution lemmas above apply. -/
private theorem ctx_fold (p : Program) :
    ({ dialect := p.dialect, table := p.table, builtinBases := p.builtinBases } : Ctx) = ctxOf p := rfl

/-! ### Satisfiability first

By `refinesUnder_of_unsatisfiable`, a contract-relative theorem says nothing until its
contracts are known to be meetable. So the satisfiability proofs come first, and they are
constructive: each exhibits an implementation. -/

/-- `pureValueContract` is satisfiable here: an integer literal is a hole implementation
that terminates, returns, raises nothing and leaves the heap alone. -/
theorem satisfiable_pureValue :
    Satisfiable [pureValueContract "op:starredUnpack"] keysProgramHoled := by
  refine ⟨[("op:starredUnpack", .lit (.int 0))], ⟨?_, ?_, ?_⟩, ?_⟩
  · intro l hl
    simp [Impl.labels] at hl
    simp [ContractEnv.labels, pureValueContract, hl]
  · intro c hc e' he' k hk h ρ
    simp [pureValueContract] at hc
    subst hc
    simp only [pureValueContract] at he' hk ⊢
    simp at he'
    subst he'
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    exact ⟨rfl, ⟨.int 0, rfl⟩⟩
  · intro l e he
    simp only [List.lookup] at he
    split at he
    · cases he; rfl
    · simp_all
  · intro c hc
    simp at hc; subst hc
    simp [pureValueContract]

/-- `raisesContract` is satisfiable **only for payloads Core can actually raise.** Division
by zero is one: `1 / 0` is a legal `Expr` whose meaning is `.exn (.str "ZeroDivisionError")`.

This is a real limitation and it is the mechanism working: an assumption that the hole
raises `MyCustomError` is not automatically meetable, and the obligation surfaces here
rather than being smuggled in. -/
theorem satisfiable_raises_zeroDiv :
    Satisfiable [raisesContract "op:starredUnpack" (.str "ZeroDivisionError")] keysProgramHoled := by
  refine ⟨[("op:starredUnpack", .binop "/" (.lit (.int 1)) (.lit (.int 0)))],
    ⟨?_, ?_, ?_⟩, ?_⟩
  · intro l hl
    simp [Impl.labels] at hl
    simp [ContractEnv.labels, raisesContract, hl]
  · intro c hc e' he' k hk h ρ
    simp [raisesContract] at hc
    subst hc
    simp only [raisesContract] at he' hk ⊢
    simp at he'
    subst he'
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    rfl
  · intro l e he
    simp only [List.lookup] at he
    split at he
    · cases he; rfl
    · simp_all
  · intro c hc
    simp at hc; subst hc
    simp [raisesContract]

/-! ### The theorems

Both are `RefinesUnder`, at the concrete fuel bound 14, on the unrestricted domain. -/

set_option maxHeartbeats 2000000 in
/-- **`methodkey` refines a total Lean specification, under one contract.**

Assuming only that the starred-unpack construct returns *some* value without touching the
heap, `methodkey` provably terminates, provably never raises, provably never reaches any
other hole, and returns a freshly allocated `_HashedTuple` at address 0 — for every
argument list and every fuel budget from 14 up.

Note what is *not* assumed: nothing about which value the hole produces. The conclusion is
uniform over all implementations meeting the contract, which is the strongest form this
mechanism can deliver — and here it happens to be available, because `_HashedTuple` has no
`__init__` in the translated program, so the unpacked arguments are not observable in the
result. That is a fact about `cachetools`'s translation, discovered by the proof. -/
theorem methodkey_refinesUnder_value :
    RefinesUnder [pureValueContract "op:starredUnpack"] keysProgramHoled "cachetools/keys.py:<module>.methodkey" 14
      (fun _ => True) (fun _ => .ret (.ref 0)) := by
  intro σ hc ht
  have hmem : pureValueContract "op:starredUnpack" ∈ [pureValueContract "op:starredUnpack"] := by
    simp
  obtain ⟨e, he⟩ : ∃ e, σ.lookup "op:starredUnpack" = some e := by
    have h1 : (σ.lookup "op:starredUnpack").isSome := ht _ hmem
    exact Option.isSome_iff_exists.mp h1
  have hpost := hc.2.1 _ hmem e he
  simp only [pureValueContract] at hpost
  -- The contract fixes the *shape* of the hole's outcome, not its value; that is enough
  -- to rewrite past it.
  obtain ⟨vf, hvf⟩ : ∃ vf : Nat → Heap → Env → Val, ∀ k h ρ, 1 ≤ k →
      evalExpr (ctxOf (σ.onProgram keysProgramHoled)) k h ρ e = (h, .val (vf k h ρ)) := by
    refine ⟨fun k h ρ => match (evalExpr (ctxOf (σ.onProgram keysProgramHoled)) k h ρ e).2 with
                         | .val v => v | _ => .unit, ?_⟩
    intro k h ρ hk
    obtain ⟨h1, v, h2⟩ := hpost k hk h ρ
    simp only []
    rw [h2]
    exact Prod.ext h1 h2
  rw [onProgram_keysProgramHoled he] at hvf
  have hplain : e.plainArg = true := hc.2.2 _ _ he
  intro args _
  apply forall_ge_of_forall_add
  intro k
  rw [onProgram_keysProgramHoled he]
  -- `evalList` dispatches on the *syntax* of an argument before evaluating it, so the
  -- contract's statement about `evalExpr e` is not on its own enough to say what the
  -- argument list does. `Consistent`'s plainness clause supplies the missing half.
  have hvl : ∀ (h : Heap) (ρ : Env),
      evalList (ctxOf (keysProgramWith e)) (k+9) h ρ [e]
        = (h, .inr ([vf (k+8) h ρ], [])) := by
    intro h ρ
    rw [show k+9 = (k+7)+2 from rfl, evalList_singleton _ _ _ _ hplain,
        show (k+7)+1 = k+8 from rfl, hvf (k+8) h ρ (by omega)]
  -- Everything from here is evaluation of the interpreter on a concrete AST. The only
  -- non-mechanical step is `hvf`, which is exactly where the contract is used.
  simp +decide [runFunc, bindParams, Func.posParams, kwargsRejected, posRejected, builtinBase_keysProgramWith, ctx_fold, resolve_methodkey, resolve_hashkey, resolve_kwargs,
    resolveMethod_hashedTuple_init, methodkeyWith,
    f_cachetools_keys_py__module__hashkey, applyFunc, execStmt, evalExpr, evalList,
    Env.set, Env.get, Val.truthy, Heap.get, Heap.alloc, hvl, hvf]

set_option maxHeartbeats 2000000 in
/-- **A different contract proves a different theorem.**

Under the assumption that the same hole *raises*, `methodkey` refines `raise payload`
instead. The contract is therefore load-bearing: it is not a formality that lets an
otherwise-fixed conclusion through, it determines the conclusion.

Taken with `methodkey_refinesUnder_value` this is also the sharpest illustration of what
`refinesUnder_unique` does and does not say. Both theorems are true; they do not conflict,
because they are relative to different `Γ`s. Reading either one without its `Γ` is reading
it wrong. -/
theorem methodkey_refinesUnder_raise (payload : Val) :
    RefinesUnder [raisesContract "op:starredUnpack" payload] keysProgramHoled "cachetools/keys.py:<module>.methodkey" 14
      (fun _ => True) (fun _ => .raise payload) := by
  intro σ hc ht
  have hmem : raisesContract "op:starredUnpack" payload ∈
      [raisesContract "op:starredUnpack" payload] := by simp
  obtain ⟨e, he⟩ : ∃ e, σ.lookup "op:starredUnpack" = some e := by
    have h1 : (σ.lookup "op:starredUnpack").isSome := ht _ hmem
    exact Option.isSome_iff_exists.mp h1
  have hpost := hc.2.1 _ hmem e he
  simp only [raisesContract] at hpost
  simp only [ctxOf, Impl.onProgram, Impl.onFunc, keysProgramHoled, keysProgramWith, methodkeyWith, substS, substE, substEL,
    he, f_cachetools_keys_py__module__hashkey,
    f_cachetools_keys_py__module__methodkey, List.map, Program.table] at hpost
  have hplain : e.plainArg = true := hc.2.2 _ _ he
  intro args _
  apply forall_ge_of_forall_add
  intro k
  -- As in the value theorem: the plainness clause of `Consistent` is what lets a fact
  -- about `evalExpr e` become a fact about the argument list `[e]`.
  simp +decide [runFunc, bindParams, Func.posParams, kwargsRejected, posRejected, builtinBase_keysProgramWith, evalList_singleton _ _ _ _ hplain, Impl.onProgram, Impl.onFunc, keysProgramHoled, keysProgramWith, methodkeyWith,
    f_cachetools_keys_py__module__hashkey, f_cachetools_keys_py__module__methodkey,
    substS, substE, substEL, he, Ctx.resolve, Ctx.resolve.go, String.endsWith, Program.table,
    applyFunc, execStmt, evalExpr, evalList, ctxOf, Env.set, hpost]

/-- The contract-relative theorem plus its satisfiability proof, which is the pair a
reader is entitled to demand. Stated as one declaration so the two cannot drift apart. -/
theorem methodkey_value_result :
    Satisfiable [pureValueContract "op:starredUnpack"] keysProgramHoled ∧
    RefinesUnder [pureValueContract "op:starredUnpack"] keysProgramHoled "cachetools/keys.py:<module>.methodkey" 14
      (fun _ => True) (fun _ => .ret (.ref 0)) :=
  ⟨satisfiable_pureValue, methodkey_refinesUnder_value⟩

/-- The raising contract, paired with the payload for which satisfiability is proved.
The general `methodkey_refinesUnder_raise` holds for *any* payload; only this instance
comes with a witness that the assumption can be met. -/
theorem methodkey_raise_result :
    Satisfiable [raisesContract "op:starredUnpack" (.str "ZeroDivisionError")] keysProgramHoled ∧
    RefinesUnder [raisesContract "op:starredUnpack" (.str "ZeroDivisionError")] keysProgramHoled
      "cachetools/keys.py:<module>.methodkey" 14 (fun _ => True)
      (fun _ => .raise (.str "ZeroDivisionError")) :=
  ⟨satisfiable_raises_zeroDiv, methodkey_refinesUnder_raise _⟩

/-- The same resolution facts, for the *current* program rather than the holed one.
`_HashedTuple` has no translated `__init__` here either. -/
theorem table_keysProgram : keysProgram.table =
    [ ("cachetools/keys.py:<module>.hashkey", f_cachetools_keys_py__module__hashkey)
    , ("cachetools/keys.py:<module>.methodkey", f_cachetools_keys_py__module__methodkey) ] := by
  simp [Program.table, keysProgram, f_cachetools_keys_py__module__hashkey,
    f_cachetools_keys_py__module__methodkey]

theorem resolve_methodkey' :
    (ctxOf keysProgram).resolve "cachetools/keys.py:<module>.methodkey"
      = some f_cachetools_keys_py__module__methodkey := by
  simp +decide [Ctx.resolve, ctxOf, table_keysProgram,
    f_cachetools_keys_py__module__methodkey]

/-- The generated `methodkey` calls `hashkey` by its **fully qualified** name (§31), so
this resolution is an exact table hit rather than the unique-suffix fallback. -/
theorem resolve_hashkey' :
    (ctxOf keysProgram).resolve "cachetools/keys.py:<module>.hashkey"
      = some f_cachetools_keys_py__module__hashkey := by
  simp +decide [Ctx.resolve, ctxOf, table_keysProgram,
    f_cachetools_keys_py__module__hashkey]

theorem resolveMethod_hashedTuple_init' :
    (ctxOf keysProgram).resolveMethod "_HashedTuple" "__init__" = none := by
  simp only [Ctx.resolveMethod, ctxOf, table_keysProgram,
    f_cachetools_keys_py__module__methodkey, f_cachetools_keys_py__module__hashkey]
  rw [show ("." ++ "_HashedTuple" ++ "." ++ "__init__") = "._HashedTuple.__init__" from by rfl]
  simp +decide [List.filter_cons, String.endsWith]
  simp only [Ctx.resolve, ctxOf, table_keysProgram]
  rw [show ("." ++ "__init__") = ".__init__" from by rfl]
  simp +decide [Ctx.resolve.go, String.endsWith,
    f_cachetools_keys_py__module__methodkey, f_cachetools_keys_py__module__hashkey]

/-! ### The unconditional theorem

The point of the whole section: with the calling convention modelled, the contract is no
longer needed. -/

set_option maxHeartbeats 4000000 in
/-- **`methodkey` refines a total Lean specification, unconditionally.**

Same entry point, same fuel bound, same domain and same conclusion as
`methodkey_refinesUnder_value` — with `Γ = []`. By `refinesUnder_nil_iff` a theorem is
unconditional exactly when its contract environment is literally empty, and this one has
no contract environment at all: it is an ordinary `Refine.Refines`.

What closed it was language modelling, not proof automation: `Expr.starred`/`Expr.dstarred`
and `Func.vararg`/`Func.kwarg`, plus an exporter that emits them. The hole
`op:starredUnpack` no longer occurs anywhere in the corpus.

The conclusion is still `_HashedTuple` at address 0 and still does not depend on the
unpacked arguments, for the reason the contract-relative proof already found: the
translated `_HashedTuple` has no `__init__`. That is the builtin-base-class gap
STRATEGY.md §31/§34 records, and it is unchanged by this theorem. -/
theorem methodkey_refines :
    Refines keysProgram "cachetools/keys.py:<module>.methodkey" 14
      (fun _ => True) (fun _ => .ret (.ref 0)) := by
  intro args _
  apply forall_ge_of_forall_add
  intro k
  simp +decide [runFunc, bindParams, Func.posParams, kwargsRejected, posRejected, builtinBase_keysProgram, ctx_fold,
    resolve_methodkey', resolve_hashkey', resolveMethod_hashedTuple_init',
    f_cachetools_keys_py__module__hashkey, f_cachetools_keys_py__module__methodkey,
    applyFunc, execStmt, evalExpr, evalList, Env.set, Env.get, Val.truthy,
    Val.iterable, strKeyed, Heap.get, Heap.alloc]

/-- The unconditional theorem needs no satisfiability obligation — there is nothing to
satisfy. Recorded as a declaration so the contrast with `methodkey_value_result` is
mechanical rather than a matter of reading the prose. -/
theorem methodkey_unconditional : RefinesUnder [] keysProgram
    "cachetools/keys.py:<module>.methodkey" 14 (fun _ => True) (fun _ => .ret (.ref 0)) :=
  (refinesUnder_nil_iff _ _ _ _ _).mpr methodkey_refines

/-! ### The negative result

Without it the section above would be advocacy. -/

/-- Leaving the hole in place is a legal implementation of `topContract`. -/
def idImpl : Impl := [("op:starredUnpack", .hole "op:starredUnpack")]

theorem idImpl_onProgram : idImpl.onProgram keysProgramHoled = keysProgramHoled := by
  simp [idImpl, Impl.onProgram, Impl.onFunc, keysProgramHoled, keysProgramWith, methodkeyWith, substS, substE, substEL,
    f_cachetools_keys_py__module__hashkey, f_cachetools_keys_py__module__methodkey]

set_option maxHeartbeats 1000000 in
/-- Untouched, `methodkey` reports the hole, at any adequate fuel — the situation this
whole file exists to improve on. -/
theorem methodkey_holes (k : Nat) (args : List Val) :
    runFunc keysProgramHoled (k + 14) "cachetools/keys.py:<module>.methodkey" args = .hole "op:starredUnpack" := by
  simp +decide [runFunc, bindParams, Func.posParams, kwargsRejected, posRejected, keysProgramHoled, keysProgramWith, methodkeyWith,
    f_cachetools_keys_py__module__hashkey,
    f_cachetools_keys_py__module__methodkey, Ctx.resolve, Ctx.resolve.go, String.endsWith,
    Program.table,
    applyFunc, execStmt, evalExpr, evalList, ctxOf, Env.set, Env.get, Val.truthy,
    Heap.get, Heap.alloc]

/-- **An unconstrained contract proves nothing.**

Under `topContract` — satisfiable, by `satisfiable_top`, and therefore not excluded by the
anti-vacuity check — *no* specification refines `methodkey`, at any fuel bound, on any
non-empty domain. The reason is exactly right: "the hole may do anything" includes
"the hole may still be a hole", and `Refine.refines_not_hole` then bites.

So satisfiability is necessary and not sufficient, and the useful contracts are the ones
that say something. A `Γ` full of `topContract`s is detectably worthless rather than
quietly worthless. -/
theorem methodkey_not_refinable_under_top (N : Nat) (dom : List Val → Prop)
    (spec : List Val → Outcome) (args : List Val) (hd : dom args) :
    ¬ RefinesUnder [topContract "op:starredUnpack"] keysProgramHoled "cachetools/keys.py:<module>.methodkey" N dom spec := by
  intro h
  have hcons : Consistent [topContract "op:starredUnpack"] keysProgramHoled idImpl := by
    refine ⟨?_, ?_, ?_⟩
    · intro l hl
      simp [idImpl, Impl.labels] at hl
      simp [ContractEnv.labels, topContract, hl]
    · intro c hc e' _ k _ h' ρ
      simp at hc; subst hc; trivial
    · intro l e he
      simp only [idImpl, List.lookup] at he
      split at he
      · cases he; rfl
      · simp_all
  have htot : Total [topContract "op:starredUnpack"] idImpl := by
    intro c hc; simp at hc; subst hc; simp [topContract, idImpl]
  have hR := h idImpl hcons htot
  rw [idImpl_onProgram] at hR
  exact refines_not_hole hR args hd (N + 14) (Nat.le_add_right _ _) "op:starredUnpack"
    (methodkey_holes N args)

/-! ### Cross-checks against the full program

`keysProgram` is a two-function slice. These evaluate the *whole* translated `cachetools`
(208 functions) and confirm the slice did not change the answer — the same
oracle-not-sharing-the-artifact's-assumptions discipline as §17. They are `#eval`, so they
are evidence for a reader, not part of any proof. -/

-- The full program agrees with `methodkey_refines`: `_HashedTuple` at address 0, with no
-- hole and no contract. This is the line that used to print `hole "op:starredUnpack"`.
#eval reprStr (runFunc Autoform.Generated.Cachetools.program 40 "cachetools/keys.py:<module>.methodkey" [.int 1])

-- Re-holing the starred call reproduces the old behaviour on the full program, which is
-- what `keysProgramHoled` is a slice of.
def reholed : Program :=
  { Autoform.Generated.Cachetools.program with
    funcs := Autoform.Generated.Cachetools.program.funcs.map fun f =>
      if f.name == "cachetools/keys.py:<module>.methodkey" then
        methodkeyWith (.hole "op:starredUnpack") else f }

#eval reprStr (runFunc reholed 40 "cachetools/keys.py:<module>.methodkey" [.int 1])

-- `hashkey` on the full program, showing the `**kwargs` branch is reachable: passing a
-- keyword argument takes the `if kwargs:` branch that the empty call does not.
#eval reprStr (runFunc Autoform.Generated.Cachetools.program 40 "cachetools/keys.py:<module>.hashkey" [.int 1])

/-! ### Axiom audit

The headline of this section is now the unconditional theorem, so it is the one whose
axiom base a reader should check. -/

#print axioms methodkey_refines
#print axioms methodkey_unconditional
#print axioms methodkey_refinesUnder_value
#print axioms methodkey_refinesUnder_raise
#print axioms methodkey_not_refinable_under_top

/-! ### The assumption record this theorem exports -/

-- What `scripts/sacm.py` should turn into `Assumption` nodes attached to
-- `methodkey_refinesUnder_value` — not to the module.
#eval (assumptionsJson
  "Autoform.Contracts.Demo.methodkey_refinesUnder_value"
  [pureValueContract "op:starredUnpack"]
  (some "Autoform.Contracts.Demo.satisfiable_pureValue")).pretty

/-! ### The registry `scripts/sacm.py` consumes

One record per contract-relative theorem in this module. Keeping it beside the theorems
is deliberate: a registry maintained anywhere else drifts, and a contract-relative
theorem that is *missing* from the assurance case reads exactly like an unconditional
one. `scripts/emit_contracts.py` renders this to `contracts-<Module>.json`. -/

def contractRecords : List Lean.Json :=
  [ assumptionsJson
      "Autoform.Contracts.Demo.methodkey_refinesUnder_value"
      [pureValueContract "op:starredUnpack"]
      (some "Autoform.Contracts.Demo.satisfiable_pureValue")
  , assumptionsJson
      "Autoform.Contracts.Demo.methodkey_refinesUnder_raise"
      [raisesContract "op:starredUnpack" (.int 0)]
      (some "Autoform.Contracts.Demo.satisfiable_raises_zeroDiv")
  ]
-- `methodkey_not_refinable_under_top` is deliberately NOT in this list. It is a
-- *negative* result -- `topContract` is satisfiable (`satisfiable_top`) and still proves
-- nothing -- so listing it beside the positive records would file a refutation as
-- support. What it establishes belongs in the consumer's justification instead:
-- `satisfiable: true` is necessary for a contract-relative theorem to carry
-- information, and it is not sufficient. See `scripts/sacm.py`.

/-- Rendered registry, for the emitter. -/
def contractRecordsJson (module : String) : Lean.Json :=
  Lean.Json.mkObj [("module", .str module), ("theorems", .arr contractRecords.toArray)]

end Demo

end Autoform.Contracts
