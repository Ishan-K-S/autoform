import Autoform.Lang.Core.Semantics

/-!
# General fuel monotonicity for the Core interpreter

Open obligation #1 of `Autoform/Refine.lean` §5, closed here up to one honest exclusion.

**What is proved.** For all seven mutually recursive interpreter functions of
`Autoform/Lang/Core/Semantics.lean` — `evalExpr`, `applyFunc`, `applyClosure`, `evalList`,
`evalPairs`, `execStmt`, `execFor` — raising the fuel budget cannot change a result that
did not itself run out of fuel:

    evalExpr ctx k h ρ e = (h', r) → r ≠ .outOfFuel → evalExpr ctx (k+1) h ρ e = (h', r)

and, by induction on the gap, the same for any `k ≤ k'`. The "out of fuel" side condition
is spelled per return type: `EResult.outOfFuel` for `evalExpr`/`applyFunc`/`applyClosure`,
`Sum.inl EResult.outOfFuel` for `evalList`/`evalPairs` (which return
`Heap × Sum EResult _`), and `Ctl.outOfFuel` — a constructor of `Ctl`, not of `EResult` —
for `execStmt`/`execFor`.

The proof is a single induction on the fuel `k`, over the seven-way conjunction
`FuelStep`; every recursive call in the interpreter is at `k`, so one induction hypothesis
serves all seven functions.

**What is excluded, and why it must be.** `Stmt.tryFinally`, and nothing else. It is the
only construct in the interpreter that does not propagate an out-of-fuel sub-result: when
the body runs out of fuel and the finalizer exits abnormally, Python's rule makes the
finalizer's outcome *discard* the body's, so the statement returns an ordinary result
computed from a partially-mutated heap — and a larger budget mutates that heap further.
`tryFinally_breaks_fuel_mono` at the bottom of this file exhibits a four-line program
whose result is `return 1` at fuel 4 and `return 2` at fuel 5, neither of them
`outOfFuel`. So the theorems carry `tfFreeS` side conditions (`fuelMonoExclusions` lists
the exclusion as a value), and `tfFree_of_table` discharges them for any program whose
function table contains no `tryFinally`.
-/

namespace Autoform.Core

/-- `tryFinally`-freedom, the one syntactic exclusion this file needs.

`Stmt.tryFinally` is the *only* interpreter construct whose result does not propagate an
out-of-fuel sub-result: when the body runs out of fuel and the finalizer exits abnormally,
the finalizer's outcome *discards* the body's, so the whole statement can return a
perfectly ordinary result computed from a partially-mutated heap. Raising the budget lets
the body get further, changing that heap — so fuel monotonicity is *false* in the presence
of `tryFinally` (see `tryFinally_breaks_fuel_mono` at the bottom of this file for a
machine-checked counterexample). Every other construct propagates `outOfFuel`, which is
exactly what makes the induction go through. -/
def tfFreeS : Stmt → Bool
  | .tryFinally _ _  => false
  | .seq a b         => tfFreeS a && tfFreeS b
  | .ifte _ t e      => tfFreeS t && tfFreeS e
  | .loop _ b        => tfFreeS b
  | .forIn _ _ b     => tfFreeS b
  | .tryCatch b _ hd => tfFreeS b && tfFreeS hd
  | _                => true

/-- A context every one of whose *reachable* function bodies is `tryFinally`-free.

Stated in terms of the two resolution functions rather than of `ctx.table` because those
are exactly the two ways the interpreter can reach a function body; `tfFree_of_table`
below derives it from the simpler table-wide condition. -/
def TFFreeCtx (ctx : Ctx) : Prop :=
  (∀ n fn, ctx.resolve n = some fn → tfFreeS fn.body = true) ∧
  (∀ c m fn, ctx.resolveMethod c m = some fn → tfFreeS fn.body = true)

/-- The seven-way simultaneous statement, at a fixed fuel `k`. -/
private def FuelStep (k : Nat) : Prop :=
  (∀ (ctx : Ctx), TFFreeCtx ctx → ∀ (h : Heap) (ρ : Env) (e : Expr) (h' : Heap)
        (r : EResult),
      evalExpr ctx k h ρ e = (h', r) → r ≠ .outOfFuel →
      evalExpr ctx (k+1) h ρ e = (h', r))
  ∧ (∀ (ctx : Ctx), TFFreeCtx ctx → ∀ (h : Heap) (fn : Func), tfFreeS fn.body = true →
        ∀ (s : Option Val) (vs : List Val) (kws : List (String × Val))
          (h' : Heap) (r : EResult),
      applyFunc ctx k h fn s vs kws = (h', r) → r ≠ .outOfFuel →
      applyFunc ctx (k+1) h fn s vs kws = (h', r))
  ∧ (∀ (ctx : Ctx), TFFreeCtx ctx → ∀ (h : Heap) (fn : Func), tfFreeS fn.body = true →
        ∀ (cap : List (String × Val)) (vs : List Val) (kws : List (String × Val))
          (h' : Heap) (r : EResult),
      applyClosure ctx k h fn cap vs kws = (h', r) → r ≠ .outOfFuel →
      applyClosure ctx (k+1) h fn cap vs kws = (h', r))
  ∧ (∀ (ctx : Ctx), TFFreeCtx ctx → ∀ (h : Heap) (ρ : Env) (es : List Expr) (h' : Heap)
        (r : Sum EResult (List Val × List (String × Val))),
      evalList ctx k h ρ es = (h', r) → r ≠ .inl .outOfFuel →
      evalList ctx (k+1) h ρ es = (h', r))
  ∧ (∀ (ctx : Ctx), TFFreeCtx ctx → ∀ (h : Heap) (ρ : Env) (ps : List (Expr × Expr))
        (h' : Heap) (r : Sum EResult (List (Val × Val))),
      evalPairs ctx k h ρ ps = (h', r) → r ≠ .inl .outOfFuel →
      evalPairs ctx (k+1) h ρ ps = (h', r))
  ∧ (∀ (ctx : Ctx), TFFreeCtx ctx → ∀ (h : Heap) (ρ : Env) (s : Stmt),
        tfFreeS s = true → ∀ (h' : Heap) (c : Ctl),
      execStmt ctx k h ρ s = (h', c) → c ≠ .outOfFuel →
      execStmt ctx (k+1) h ρ s = (h', c))
  ∧ (∀ (ctx : Ctx), TFFreeCtx ctx → ∀ (h : Heap) (ρ : Env) (x : String) (vs : List Val)
        (body : Stmt), tfFreeS body = true → ∀ (h' : Heap) (c : Ctl),
      execFor ctx k h ρ x vs body = (h', c) → c ≠ .outOfFuel →
      execFor ctx (k+1) h ρ x vs body = (h', c))

private theorem fuelStep : ∀ k, FuelStep k := by
  intro k
  induction k with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
        (rename_i hy hne
         simp only [evalExpr, applyFunc, applyClosure, evalList, evalPairs, execStmt,
           execFor] at hy
         cases hy
         exact absurd rfl hne)
  | succ k ih =>
      obtain ⟨ihE, ihF, ihC, ihL, ihP, ihS, ihR⟩ := ih
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro ctx hctx h ρ e h' r hy hne
        cases e with
        | lit l => cases l <;> exact hy
        | name x => exact hy
        | fnref f => exact hy
        | closure f => exact hy
        | classClosure c => exact hy
        | hole l => exact hy
        | starred a => exact hy
        | kwargE k a => exact hy
        | dstarred a => exact hy
        | unop op a =>
            simp only [evalExpr] at hy ⊢
            rcases hA : evalExpr ctx k h ρ a with ⟨h₁, r₁⟩
            rw [hA] at hy
            cases r₁ <;> first
              | (cases hy; exact absurd rfl hne)
              | (rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy)
        -- `003-box-address-taken-locals`: same shape as `unop` -- one recursive
        -- `evalExpr` call, then a fuel-free follow-up (`Heap.alloc` here, `applyUnop`
        -- there) with no further recursion to induct on.
        | boxNew a =>
            simp only [evalExpr] at hy ⊢
            rcases hA : evalExpr ctx k h ρ a with ⟨h₁, r₁⟩
            rw [hA] at hy
            cases r₁ <;> first
              | (cases hy; exact absurd rfl hne)
              | (rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy)
        -- `006-reduce-remaining-holes`, Story 5: `Expr.boxFields` reuses `evalPairs`
        -- verbatim (each key an `Expr`, always a string literal at every site the
        -- exporter emits) -- same shape as `dictE` exactly, `ihP` already proves it.
        -- The key-extraction fold after `evalPairs` returns is fuel-free, so once
        -- `ihP` shows the SAME `(h₁, pairs)` at fuel `k+1`, the rest is identical on
        -- both sides and `exact hy` (already unified by the rewrite) closes it.
        | boxFields kvs =>
            simp only [evalExpr] at hy ⊢
            rcases hA : evalPairs ctx k h ρ kvs with ⟨h₁, s⟩
            rw [hA] at hy
            cases s with
            | inr pairs => rw [ihP _ hctx _ _ _ _ _ hA (by simp)]; exact hy
            | inl r₁ =>
                cases r₁ <;> first
                  | (cases hy; exact absurd rfl hne)
                  | (rw [ihP _ hctx _ _ _ _ _ hA (by simp)]; exact hy)
        -- `006-reduce-remaining-holes`, Story 5: `&a[i]` -- same shape as `index`,
        -- two sequential `evalExpr` calls with no further recursion afterwards.
        | irefIndex a i =>
            simp only [evalExpr] at hy ⊢
            rcases hA : evalExpr ctx k h ρ a with ⟨h₁, r₁⟩
            rw [hA] at hy
            cases r₁ with
            | exn v => rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy
            | hole l => rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy
            | outOfFuel => cases hy; exact absurd rfl hne
            | val x =>
                rw [ihE _ hctx _ _ _ _ _ hA (by simp)]
                -- Unlike `index`, this match discriminates on `x`'s OWN shape (only
                -- `.ref` recurses further) before recursing again, so `x` needs its
                -- own case split first.
                cases x
                case ref r =>
                    dsimp only at hy ⊢
                    rcases hB : evalExpr ctx k h₁ ρ i with ⟨h₂, r₂⟩
                    rw [hB] at hy
                    cases r₂ <;> first
                      | (cases hy; exact absurd rfl hne)
                      | (rw [ihE _ hctx _ _ _ _ _ hB (by simp)]; exact hy)
                all_goals (dsimp only at hy ⊢; exact hy)
        -- `006-reduce-remaining-holes`, Story 5: `&s.f` -- same shape as `field`/
        -- `boxNew`, one recursive `evalExpr` call with no further recursion.
        | irefField a f =>
            simp only [evalExpr] at hy ⊢
            rcases hA : evalExpr ctx k h ρ a with ⟨h₁, r₁⟩
            rw [hA] at hy
            cases r₁ <;> first
              | (cases hy; exact absurd rfl hne)
              | (rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy)
        -- `006-reduce-remaining-holes`, Story 5: `*p` -- same shape as `field`.
        | derefIref a =>
            simp only [evalExpr] at hy ⊢
            rcases hA : evalExpr ctx k h ρ a with ⟨h₁, r₁⟩
            rw [hA] at hy
            cases r₁ <;> first
              | (cases hy; exact absurd rfl hne)
              | (rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy)
        | binop op a b =>
            simp only [evalExpr] at hy ⊢
            rcases hA : evalExpr ctx k h ρ a with ⟨h₁, r₁⟩
            rw [hA] at hy
            cases r₁ with
            | exn v => rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy
            | hole l => rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy
            | outOfFuel => cases hy; exact absurd rfl hne
            | val x =>
                rw [ihE _ hctx _ _ _ _ _ hA (by simp)]
                dsimp only at hy ⊢
                by_cases hc1 : (op == "&&" && !x.truthy) = true
                · rw [if_pos hc1] at hy ⊢; exact hy
                · rw [if_neg hc1] at hy ⊢
                  by_cases hc2 : (op == "||" && x.truthy) = true
                  · rw [if_pos hc2] at hy ⊢; exact hy
                  · rw [if_neg hc2] at hy ⊢
                    rcases hB : evalExpr ctx k h₁ ρ b with ⟨h₂, r₂⟩
                    rw [hB] at hy
                    cases r₂ <;> first
                      | (cases hy; exact absurd rfl hne)
                      | (rw [ihE _ hctx _ _ _ _ _ hB (by simp)]; exact hy)
        | cond c t el =>
            simp only [evalExpr] at hy ⊢
            rcases hA : evalExpr ctx k h ρ c with ⟨h₁, r₁⟩
            rw [hA] at hy
            cases r₁ with
            | exn v => rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy
            | hole l => rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy
            | outOfFuel => cases hy; exact absurd rfl hne
            | val v =>
                rw [ihE _ hctx _ _ _ _ _ hA (by simp)]
                dsimp only at hy ⊢
                by_cases hv : v.truthy = true
                · rw [if_pos hv] at hy ⊢; exact ihE _ hctx _ _ _ _ _ hy hne
                · rw [if_neg hv] at hy ⊢; exact ihE _ hctx _ _ _ _ _ hy hne
        | isOp neg a b =>
            simp only [evalExpr] at hy ⊢
            rcases hA : evalExpr ctx k h ρ a with ⟨h₁, r₁⟩
            rw [hA] at hy
            cases r₁ with
            | exn v => rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy
            | hole l => rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy
            | outOfFuel => cases hy; exact absurd rfl hne
            | val x =>
                rw [ihE _ hctx _ _ _ _ _ hA (by simp)]
                dsimp only at hy ⊢
                rcases hB : evalExpr ctx k h₁ ρ b with ⟨h₂, r₂⟩
                rw [hB] at hy
                cases r₂ <;> first
                  | (cases hy; exact absurd rfl hne)
                  | (rw [ihE _ hctx _ _ _ _ _ hB (by simp)]; exact hy)
        | inOp neg a b =>
            simp only [evalExpr] at hy ⊢
            rcases hA : evalExpr ctx k h ρ a with ⟨h₁, r₁⟩
            rw [hA] at hy
            cases r₁ with
            | exn v => rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy
            | hole l => rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy
            | outOfFuel => cases hy; exact absurd rfl hne
            | val x =>
                rw [ihE _ hctx _ _ _ _ _ hA (by simp)]
                dsimp only at hy ⊢
                rcases hB : evalExpr ctx k h₁ ρ b with ⟨h₂, r₂⟩
                rw [hB] at hy
                cases r₂ <;> first
                  | (cases hy; exact absurd rfl hne)
                  | (rw [ihE _ hctx _ _ _ _ _ hB (by simp)]; exact hy)
        | index a b =>
            simp only [evalExpr] at hy ⊢
            rcases hA : evalExpr ctx k h ρ a with ⟨h₁, r₁⟩
            rw [hA] at hy
            cases r₁ with
            | exn v => rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy
            | hole l => rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy
            | outOfFuel => cases hy; exact absurd rfl hne
            | val x =>
                rw [ihE _ hctx _ _ _ _ _ hA (by simp)]
                dsimp only at hy ⊢
                rcases hB : evalExpr ctx k h₁ ρ b with ⟨h₂, r₂⟩
                rw [hB] at hy
                cases r₂ <;> first
                  | (cases hy; exact absurd rfl hne)
                  | (rw [ihE _ hctx _ _ _ _ _ hB (by simp)]; exact hy)
        | field a f =>
            simp only [evalExpr] at hy ⊢
            rcases hA : evalExpr ctx k h ρ a with ⟨h₁, r₁⟩
            rw [hA] at hy
            cases r₁ <;> first
              | (cases hy; exact absurd rfl hne)
              | (rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy)
        | listE es =>
            simp only [evalExpr] at hy ⊢
            rcases hA : evalList ctx k h ρ es with ⟨h₁, s⟩
            rw [hA] at hy
            cases s with
            | inr vs => rw [ihL _ hctx _ _ _ _ _ hA (by simp)]; exact hy
            | inl r₁ =>
                cases r₁ <;> first
                  | (cases hy; exact absurd rfl hne)
                  | (rw [ihL _ hctx _ _ _ _ _ hA (by simp)]; exact hy)
        | tupleE es =>
            simp only [evalExpr] at hy ⊢
            rcases hA : evalList ctx k h ρ es with ⟨h₁, s⟩
            rw [hA] at hy
            cases s with
            | inr vs => rw [ihL _ hctx _ _ _ _ _ hA (by simp)]; exact hy
            | inl r₁ =>
                cases r₁ <;> first
                  | (cases hy; exact absurd rfl hne)
                  | (rw [ihL _ hctx _ _ _ _ _ hA (by simp)]; exact hy)
        | dictE kvs =>
            simp only [evalExpr] at hy ⊢
            rcases hA : evalPairs ctx k h ρ kvs with ⟨h₁, s⟩
            rw [hA] at hy
            cases s with
            | inr ps => rw [ihP _ hctx _ _ _ _ _ hA (by simp)]; exact hy
            | inl r₁ =>
                cases r₁ <;> first
                  | (cases hy; exact absurd rfl hne)
                  | (rw [ihP _ hctx _ _ _ _ _ hA (by simp)]; exact hy)
        | call f args =>
            simp only [evalExpr] at hy ⊢
            rcases hA : evalList ctx k h ρ args with ⟨h₁, s⟩
            rw [hA] at hy
            cases s with
            | inl r₁ =>
                cases r₁ <;> first
                  | (cases hy; exact absurd rfl hne)
                  | (rw [ihL _ hctx _ _ _ _ _ hA (by simp)]; exact hy)
            | inr vs =>
                rw [ihL _ hctx _ _ _ _ _ hA (by simp)]
                dsimp only at hy ⊢
                cases hres : Ctx.resolve ctx f with
                | some fn => rw [hres] at hy; exact ihF _ hctx _ _ (hctx.1 _ _ hres) _ _ _ _ _ hy hne
                | none =>
                    rw [hres] at hy
                    dsimp only at hy ⊢
                    cases hg : Env.get ρ f
                    case fn g =>
                        rw [hg] at hy
                        dsimp only at hy ⊢
                        cases hres2 : Ctx.resolve ctx g with
                        | some fn2 =>
                            -- Two `applyFunc` calls now, not one: the unbound-method rule
                            -- splits the receiver off the positionals. Fuel monotonicity is
                            -- indifferent to WHICH arguments are passed, so `ihF` discharges
                            -- both branches -- but the branch has to be taken, or the goal
                            -- and the hypothesis are shaped differently.
                            rw [hres2] at hy
                            dsimp only at hy ⊢
                            split at hy
                            · next hc =>
                                simp only [hc, if_true]
                                exact ihF _ hctx _ _ (hctx.1 _ _ hres2) _ _ _ _ _ hy hne
                            · next hc =>
                                simp only [hc, if_false, Bool.false_eq_true]
                                exact ihF _ hctx _ _ (hctx.1 _ _ hres2) _ _ _ _ _ hy hne
                        | none => rw [hres2] at hy; exact hy
                    case clos g cap =>
                        rw [hg] at hy
                        dsimp only at hy ⊢
                        cases hres2 : Ctx.resolve ctx g with
                        | some fn2 => rw [hres2] at hy; exact ihC _ hctx _ _ (hctx.1 _ _ hres2) _ _ _ _ _ hy hne
                        | none => rw [hres2] at hy; exact hy
                    case ref addr =>
                        -- A boxed function object (section 47) dispatches to what it
                        -- carries, so this case now recurses where it used to be inert.
                        rw [hg] at hy
                        dsimp only at hy ⊢
                        cases hub : unboxFn h₁ addr with
                        | none => rw [hub] at hy; exact hy
                        | some fv =>
                            rw [hub] at hy
                            cases fv
                            case fn g2 =>
                                dsimp only at hy ⊢
                                cases hr3 : Ctx.resolve ctx g2 with
                                | some fn3 =>
                                    rw [hr3] at hy
                                    exact ihF _ hctx _ _ (hctx.1 _ _ hr3) _ _ _ _ _ hy hne
                                | none => rw [hr3] at hy; exact hy
                            case clos g2 cap2 =>
                                dsimp only at hy ⊢
                                cases hr3 : Ctx.resolve ctx g2 with
                                | some fn3 =>
                                    rw [hr3] at hy
                                    exact ihC _ hctx _ _ (hctx.1 _ _ hr3) _ _ _ _ _ hy hne
                                | none => rw [hr3] at hy; exact hy
                            all_goals (dsimp only at hy ⊢; exact hy)
                    all_goals (rw [hg] at hy; exact hy)
        | mcall recv m args =>
            simp only [evalExpr] at hy ⊢
            rcases hA : evalExpr ctx k h ρ recv with ⟨h₁, r₁⟩
            rw [hA] at hy
            cases r₁ with
            | exn v => rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy
            | hole l => rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy
            | outOfFuel => cases hy; exact absurd rfl hne
            | val v =>
                rw [ihE _ hctx _ _ _ _ _ hA (by simp)]
                cases v
                case fn g =>
                    -- A CLASS value receiver (`Cache.__init__(self, ...)`) now dispatches
                    -- to the class's method with the first positional split off as the
                    -- receiver, so this case recurses where it used to be inert.
                    dsimp only at hy ⊢
                    rcases hB : evalList ctx k h₁ ρ args with ⟨h₂, s⟩
                    rw [hB] at hy
                    cases s with
                    | inl e' =>
                        cases e' <;> first
                          | (cases hy; exact absurd rfl hne)
                          | (rw [ihL _ hctx _ _ _ _ _ hB (by simp)]; exact hy)
                    | inr vs =>
                        rw [ihL _ hctx _ _ _ _ _ hB (by simp)]
                        dsimp only at hy ⊢
                        -- three nested branches now: the `classDefines` guard, the
                        -- method lookup, and splitting the receiver off the positionals.
                        cases hcd : Ctx.classDefines ctx (classNameOfValue g) m with
                        | false => simp only [hcd, Bool.false_eq_true, if_false] at hy ⊢; exact hy
                        | true =>
                            simp only [hcd, if_true] at hy ⊢
                            cases hrm : Ctx.resolveMethod ctx (classNameOfValue g) m with
                            | none => simp only [hrm] at hy ⊢; exact hy
                            | some fn2 =>
                                simp only [hrm] at hy ⊢
                                cases hvs : vs.1 with
                                | nil => simp only [hvs] at hy ⊢; exact hy
                                | cons recv rest =>
                                    simp only [hvs] at hy ⊢
                                    exact ihF _ hctx _ _ (hctx.2 _ _ _ hrm) _ _ _ _ _ hy hne
                case ref rr =>
                    dsimp only at hy ⊢
                    rcases hB : evalList ctx k h₁ ρ args with ⟨h₂, s⟩
                    rw [hB] at hy
                    cases s with
                    | inl e' =>
                        cases e' <;> first
                          | (cases hy; exact absurd rfl hne)
                          | (rw [ihL _ hctx _ _ _ _ _ hB (by simp)]; exact hy)
                    | inr vs =>
                        rw [ihL _ hctx _ _ _ _ _ hB (by simp)]
                        dsimp only at hy ⊢
                        cases hget : Heap.get h₂ rr with
                        | none => rw [hget] at hy; exact hy
                        | some o =>
                            rw [hget] at hy
                            dsimp only at hy ⊢
                            cases hrm : Ctx.resolveMethod ctx o.cls m with
                            -- No method of that name. For a **module object** this is not
                            -- the end: the name may be a *field* holding a function value,
                            -- which is then applied with no receiver (`Semantics`, `.mcall`).
                            -- That is a recursive call, so this branch — which used to be a
                            -- bare hole — now needs the same induction hypotheses the
                            -- resolved case does. Softening the statement instead was the
                            -- alternative and is not one.
                            | none =>
                                rw [hrm] at hy
                                dsimp only at hy ⊢
                                by_cases hmod : String.startsWith o.cls "<module>" = true
                                · rw [if_pos hmod] at hy ⊢
                                  cases hf : List.find? (fun x => x.1 == m) o.fields with
                                  | none => rw [hf] at hy; exact hy
                                  | some p =>
                                      obtain ⟨_, mv⟩ := p
                                      rw [hf] at hy
                                      cases mv with
                                      | fn g =>
                                          dsimp only at hy ⊢
                                          cases hres2 : Ctx.resolve ctx g with
                                          | some fn2 =>
                                              rw [hres2] at hy
                                              exact ihF _ hctx _ _ (hctx.1 _ _ hres2) _ _ _ _ _ hy hne
                                          | none => rw [hres2] at hy; exact hy
                                      | clos g cap =>
                                          dsimp only at hy ⊢
                                          cases hres2 : Ctx.resolve ctx g with
                                          | some fn2 =>
                                              rw [hres2] at hy
                                              exact ihC _ hctx _ _ (hctx.1 _ _ hres2) _ _ _ _ _ hy hne
                                          | none => rw [hres2] at hy; exact hy
                                      | int _ => exact hy
                                      | str _ => exact hy
                                      | bool _ => exact hy
                                      | float _ => exact hy
                                      | unit => exact hy
                                      | list _ => exact hy
                                      | tuple _ => exact hy
                                      | dict _ => exact hy
                                      | ref _ => exact hy
                                      | clsClos _ _ => exact hy
                                      | bobj _ _ => exact hy
                                      | iref _ _ => exact hy
                                · rw [if_neg hmod] at hy ⊢
                                  exact hy
                            | some fn =>
                                rw [hrm] at hy
                                dsimp only at hy ⊢
                                by_cases hcap : o.captured.isEmpty = true
                                · rw [if_pos hcap] at hy ⊢
                                  exact ihF _ hctx _ _ (hctx.2 _ _ _ hrm) _ _ _ _ _ hy hne
                                · rw [if_neg hcap] at hy ⊢
                                  exact ihC _ hctx _ _ (hctx.2 _ _ _ hrm) _ _ _ _ _ hy hne
                -- An instance of a class with a builtin base (`Val.bobj`) dispatches to
                -- the class's own method when it has one, and otherwise to `Stdlib`.
                -- Only the first branch is a recursive call, so only it needs an IH.
                case bobj bcls pay =>
                    dsimp only at hy ⊢
                    rcases hB : evalList ctx k h₁ ρ args with ⟨h₂, s⟩
                    rw [hB] at hy
                    cases s with
                    | inl e' =>
                        cases e' <;> first
                          | (cases hy; exact absurd rfl hne)
                          | (rw [ihL _ hctx _ _ _ _ _ hB (by simp)]; exact hy)
                    | inr vs =>
                        rw [ihL _ hctx _ _ _ _ _ hB (by simp)]
                        dsimp only at hy ⊢
                        by_cases hcd : Ctx.classDefines ctx bcls m = true
                        · rw [if_pos hcd] at hy ⊢
                          cases hrm : Ctx.resolveMethod ctx bcls m with
                          | none => rw [hrm] at hy; exact hy
                          | some fn =>
                              rw [hrm] at hy
                              dsimp only at hy ⊢
                              exact ihF _ hctx _ _ (hctx.2 _ _ _ hrm) _ _ _ _ _ hy hne
                        · rw [if_neg hcd] at hy ⊢
                          exact hy
                all_goals
                  (dsimp only at hy ⊢
                   rcases hB : evalList ctx k h₁ ρ args with ⟨h₂, s⟩
                   rw [hB] at hy
                   cases s with
                   | inl e' =>
                       cases e' <;> first
                         | (cases hy; exact absurd rfl hne)
                         | (rw [ihL _ hctx _ _ _ _ _ hB (by simp)]; exact hy)
                   | inr vs =>
                       rw [ihL _ hctx _ _ _ _ _ hB (by simp)]; exact hy)
        | alloc cls args =>
            simp only [evalExpr, Heap.alloc] at hy ⊢
            rcases hA : evalList ctx k h ρ args with ⟨h₁, s⟩
            rw [hA] at hy
            cases s with
            | inl r₁ =>
                cases r₁ <;> first
                  | (cases hy; exact absurd rfl hne)
                  | (rw [ihL _ hctx _ _ _ _ _ hA (by simp)]; exact hy)
            | inr vs =>
                rw [ihL _ hctx _ _ _ _ _ hA (by simp)]
                dsimp only at hy ⊢
                -- A class with a builtin base allocates a `Val.bobj` by a fuel-free
                -- computation (`allocBuiltin`), so that branch has nothing to induct on.
                cases hbb : Ctx.builtinBase ctx cls with
                | some bb => rw [hbb] at hy; exact hy
                | none =>
                rw [hbb] at hy
                dsimp only at hy ⊢
                cases hcap : Env.get ρ cls
                case clsClos cname cvs =>
                    rw [hcap] at hy
                    dsimp only at hy ⊢
                    cases hrm : Ctx.resolveMethod ctx cls "__init__" with
                    | none => rw [hrm] at hy; exact hy
                    | some fn =>
                        rw [hrm] at hy
                        dsimp only at hy ⊢
                        rcases hC : applyFunc ctx k
                            (h₁ ++ [{ cls := cls, fields := [], captured := cvs }]) fn
                            (some (Val.ref h₁.length)) vs.1 vs.2 with ⟨h₃, r₃⟩
                        rw [hC] at hy
                        cases r₃ <;> first
                          | (cases hy; exact absurd rfl hne)
                          | (rw [ihF _ hctx _ _ (hctx.2 _ _ _ hrm) _ _ _ _ _ hC (by simp)]; exact hy)
                all_goals
                  (rw [hcap] at hy
                   dsimp only at hy ⊢
                   cases hrm : Ctx.resolveMethod ctx cls "__init__" with
                   | none => rw [hrm] at hy; exact hy
                   | some fn =>
                       rw [hrm] at hy
                       dsimp only at hy ⊢
                       rcases hC : applyFunc ctx k
                           (h₁ ++ [{ cls := cls, fields := [], captured := [] }]) fn
                           (some (Val.ref h₁.length)) vs.1 vs.2 with ⟨h₃, r₃⟩
                       rw [hC] at hy
                       cases r₃ <;> first
                         | (cases hy; exact absurd rfl hne)
                         | (rw [ihF _ hctx _ _ (hctx.2 _ _ _ hrm) _ _ _ _ _ hC (by simp)]; exact hy))
      · intro ctx hctx h fn hfree self? vs kws h' r hy hne
        simp only [applyFunc] at hy ⊢
        by_cases hk : (kwargsRejected fn kws || posRejected fn vs) = true
        · rw [if_pos hk] at hy ⊢; exact hy
        rw [if_neg hk] at hy ⊢
        split at hy <;> first
          | (cases hy; exact absurd rfl hne)
          | (rw [ihS _ hctx _ _ _ hfree _ _ (by assumption)
                (by first | assumption | simp | (cases hy; exact hne))]
             first | exact hy | (split <;> first | exact hy | simp_all))
      · intro ctx hctx h fn hfree cap vs kws h' r hy hne
        simp only [applyClosure] at hy ⊢
        by_cases hk : (kwargsRejected fn kws || posRejected fn vs) = true
        · rw [if_pos hk] at hy ⊢; exact hy
        rw [if_neg hk] at hy ⊢
        split at hy <;> first
          | (cases hy; exact absurd rfl hne)
          | (rw [ihS _ hctx _ _ _ hfree _ _ (by assumption)
                (by first | assumption | simp | (cases hy; exact hne))]
             first | exact hy | (split <;> first | exact hy | simp_all))
      · intro ctx hctx h ρ es h' r hy hne
        cases es with
        | nil => exact hy
        | cons a as =>
            -- The three starred argument forms are dispatched on syntactically, before
            -- `evalExpr` runs, so each needs its own step; the operand is still evaluated
            -- by `evalExpr` and the tail by `evalList`, so the induction hypotheses are
            -- the same two.
            cases a
            case starred e =>
                simp only [evalList] at hy ⊢
                rcases hA : evalExpr ctx k h ρ e with ⟨h₁, r₁⟩
                rw [hA] at hy
                cases r₁ with
                | exn v => rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy
                | hole l => rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy
                | outOfFuel => cases hy; exact absurd rfl hne
                | val v =>
                    rw [ihE _ hctx _ _ _ _ _ hA (by simp)]
                    dsimp only at hy ⊢
                    cases hit : Val.iterable v with
                    | none => rw [hit] at hy; exact hy
                    | some xs =>
                        rw [hit] at hy
                        dsimp only at hy ⊢
                        rcases hB : evalList ctx k h₁ ρ as with ⟨h₂, s⟩
                        rw [hB] at hy
                        cases s with
                        | inr vs => rw [ihL _ hctx _ _ _ _ _ hB (by simp)]; exact hy
                        | inl r₂ =>
                            cases r₂ <;> first
                              | (cases hy; exact absurd rfl hne)
                              | (rw [ihL _ hctx _ _ _ _ _ hB (by simp)]; exact hy)
            case dstarred e =>
                simp only [evalList] at hy ⊢
                rcases hA : evalExpr ctx k h ρ e with ⟨h₁, r₁⟩
                rw [hA] at hy
                cases r₁ with
                | exn v => rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy
                | hole l => rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy
                | outOfFuel => cases hy; exact absurd rfl hne
                | val v =>
                    rw [ihE _ hctx _ _ _ _ _ hA (by simp)]
                    dsimp only at hy ⊢
                    cases hit : strKeyed v with
                    | none => rw [hit] at hy; exact hy
                    | some ks =>
                        rw [hit] at hy
                        dsimp only at hy ⊢
                        rcases hB : evalList ctx k h₁ ρ as with ⟨h₂, s⟩
                        rw [hB] at hy
                        cases s with
                        | inr vs => rw [ihL _ hctx _ _ _ _ _ hB (by simp)]; exact hy
                        | inl r₂ =>
                            cases r₂ <;> first
                              | (cases hy; exact absurd rfl hne)
                              | (rw [ihL _ hctx _ _ _ _ _ hB (by simp)]; exact hy)
            case kwargE kk e =>
                simp only [evalList] at hy ⊢
                rcases hA : evalExpr ctx k h ρ e with ⟨h₁, r₁⟩
                rw [hA] at hy
                cases r₁ with
                | exn v => rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy
                | hole l => rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy
                | outOfFuel => cases hy; exact absurd rfl hne
                | val v =>
                    rw [ihE _ hctx _ _ _ _ _ hA (by simp)]
                    dsimp only at hy ⊢
                    rcases hB : evalList ctx k h₁ ρ as with ⟨h₂, s⟩
                    rw [hB] at hy
                    cases s with
                    | inr vs => rw [ihL _ hctx _ _ _ _ _ hB (by simp)]; exact hy
                    | inl r₂ =>
                        cases r₂ <;> first
                          | (cases hy; exact absurd rfl hne)
                          | (rw [ihL _ hctx _ _ _ _ _ hB (by simp)]; exact hy)
            all_goals
              (simp only [evalList] at hy ⊢
               rcases hA : evalExpr ctx k h ρ _ with ⟨h₁, r₁⟩
               rw [hA] at hy
               cases r₁ with
               | exn v => rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy
               | hole l => rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy
               | outOfFuel => cases hy; exact absurd rfl hne
               | val v =>
                   rw [ihE _ hctx _ _ _ _ _ hA (by simp)]
                   dsimp only at hy ⊢
                   rcases hB : evalList ctx k h₁ ρ as with ⟨h₂, s⟩
                   rw [hB] at hy
                   cases s with
                   | inr vs => rw [ihL _ hctx _ _ _ _ _ hB (by simp)]; exact hy
                   | inl r₂ =>
                       cases r₂ <;> first
                         | (cases hy; exact absurd rfl hne)
                         | (rw [ihL _ hctx _ _ _ _ _ hB (by simp)]; exact hy))
      · intro ctx hctx h ρ ps h' r hy hne
        cases ps with
        | nil => exact hy
        | cons kv ps =>
            obtain ⟨ke, ve⟩ := kv
            simp only [evalPairs] at hy ⊢
            rcases hA : evalExpr ctx k h ρ ke with ⟨h₁, r₁⟩
            rw [hA] at hy
            cases r₁ with
            | exn v => rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy
            | hole l => rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy
            | outOfFuel => cases hy; exact absurd rfl hne
            | val kvv =>
                rw [ihE _ hctx _ _ _ _ _ hA (by simp)]
                dsimp only at hy ⊢
                rcases hB : evalExpr ctx k h₁ ρ ve with ⟨h₂, r₂⟩
                rw [hB] at hy
                cases r₂ with
                | exn v => rw [ihE _ hctx _ _ _ _ _ hB (by simp)]; exact hy
                | hole l => rw [ihE _ hctx _ _ _ _ _ hB (by simp)]; exact hy
                | outOfFuel => cases hy; exact absurd rfl hne
                | val vvv =>
                    rw [ihE _ hctx _ _ _ _ _ hB (by simp)]
                    dsimp only at hy ⊢
                    rcases hC : evalPairs ctx k h₂ ρ ps with ⟨h₃, s⟩
                    rw [hC] at hy
                    cases s with
                    | inr rest => rw [ihP _ hctx _ _ _ _ _ hC (by simp)]; exact hy
                    | inl r₃ =>
                        cases r₃ <;> first
                          | (cases hy; exact absurd rfl hne)
                          | (rw [ihP _ hctx _ _ _ _ _ hC (by simp)]; exact hy)
      · intro ctx hctx h ρ st hfree h' c hy hne
        cases st with
        | skip => exact hy
        | brk => exact hy
        | cont => exact hy
        | hole l => exact hy
        | del x => exact hy
        | declGlobal x => exact hy
        | setIndex a b c => exact hy
        -- `006-reduce-remaining-holes`, Story 5: `*p = v` -- same shape as
        -- `setField`'s `ref`/non-object split, one constructor case instead of three.
        | setDerefIref p v =>
            simp only [execStmt] at hy ⊢
            rcases hA : evalExpr ctx k h ρ p with ⟨h₁, r₁⟩
            rw [hA] at hy
            cases r₁ with
            | exn e => rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy
            | hole l => rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy
            | outOfFuel => cases hy; exact absurd rfl hne
            | val pv =>
                rw [ihE _ hctx _ _ _ _ _ hA (by simp)]
                cases pv
                case iref r sel =>
                    dsimp only at hy ⊢
                    rcases hB : evalExpr ctx k h₁ ρ v with ⟨h₂, r₂⟩
                    rw [hB] at hy
                    cases r₂ <;> first
                      | (cases hy; exact absurd rfl hne)
                      | (rw [ihE _ hctx _ _ _ _ _ hB (by simp)]; exact hy)
                all_goals (dsimp only at hy ⊢; exact hy)
        | tryFinally a b => simp [tfFreeS] at hfree
        | expr e =>
            simp only [execStmt] at hy ⊢
            rcases hA : evalExpr ctx k h ρ e with ⟨h₁, r₁⟩
            rw [hA] at hy
            cases r₁ <;> first
              | (cases hy; exact absurd rfl hne)
              | (rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy)
        | assign x e =>
            simp only [execStmt] at hy ⊢
            rcases hA : evalExpr ctx k h ρ e with ⟨h₁, r₁⟩
            rw [hA] at hy
            cases r₁ <;> first
              | (cases hy; exact absurd rfl hne)
              | (rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy)
        | setGlobal x e =>
            simp only [execStmt] at hy ⊢
            rcases hA : evalExpr ctx k h ρ e with ⟨h₁, r₁⟩
            rw [hA] at hy
            cases r₁ <;> first
              | (cases hy; exact absurd rfl hne)
              | (rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy)
        | ret e =>
            simp only [execStmt] at hy ⊢
            rcases hA : evalExpr ctx k h ρ e with ⟨h₁, r₁⟩
            rw [hA] at hy
            cases r₁ <;> first
              | (cases hy; exact absurd rfl hne)
              | (rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy)
        | raise e =>
            simp only [execStmt] at hy ⊢
            rcases hA : evalExpr ctx k h ρ e with ⟨h₁, r₁⟩
            rw [hA] at hy
            cases r₁ <;> first
              | (cases hy; exact absurd rfl hne)
              | (rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy)
        | setField re f ve =>
            simp only [execStmt] at hy ⊢
            rcases hA : evalExpr ctx k h ρ re with ⟨h₁, r₁⟩
            rw [hA] at hy
            cases r₁ with
            | exn v => rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy
            | hole l => rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy
            | outOfFuel => cases hy; exact absurd rfl hne
            | val v =>
                rw [ihE _ hctx _ _ _ _ _ hA (by simp)]
                cases v
                case ref addr =>
                    dsimp only at hy ⊢
                    rcases hB : evalExpr ctx k h₁ ρ ve with ⟨h₂, r₂⟩
                    rw [hB] at hy
                    cases r₂ <;> first
                      | (cases hy; exact absurd rfl hne)
                      | (rw [ihE _ hctx _ _ _ _ _ hB (by simp)]; exact hy)
                case fn g =>
                    -- Boxing evaluates the right-hand side IN THE POST-ALLOCATION HEAP,
                    -- so the recursion is at `(boxFn h₁ _).1`, not at `h₁`.
                    cases re <;> dsimp only [isFnVal] at hy ⊢ <;>
                      first
                        | exact hy
                        | (generalize hbx : boxFn h₁ (Val.fn g) = bx at hy ⊢
                           obtain ⟨hb, addr⟩ := bx
                           rcases hB : evalExpr ctx k hb ρ ve with ⟨h₂, r₂⟩
                           rw [hB] at hy
                           cases r₂ <;> first
                             | (cases hy; exact absurd rfl hne)
                             | (rw [ihE _ hctx _ _ _ _ _ hB (by simp)]; exact hy))
                case clos g cap =>
                    -- Boxing evaluates the right-hand side IN THE POST-ALLOCATION HEAP,
                    -- so the recursion is at `(boxFn h₁ _).1`, not at `h₁`.
                    cases re <;> dsimp only [isFnVal] at hy ⊢ <;>
                      first
                        | exact hy
                        | (generalize hbx : boxFn h₁ (Val.clos g cap) = bx at hy ⊢
                           obtain ⟨hb, addr⟩ := bx
                           rcases hB : evalExpr ctx k hb ρ ve with ⟨h₂, r₂⟩
                           rw [hB] at hy
                           cases r₂ <;> first
                             | (cases hy; exact absurd rfl hne)
                             | (rw [ihE _ hctx _ _ _ _ _ hB (by simp)]; exact hy))
                all_goals (dsimp only at hy ⊢; exact hy)
        | seq a b =>
            simp only [tfFreeS, Bool.and_eq_true] at hfree
            simp only [execStmt] at hy ⊢
            rcases hA : execStmt ctx k h ρ a with ⟨h₁, c₁⟩
            rw [hA] at hy
            cases c₁ <;> first
              | (cases hy; exact absurd rfl hne)
              | (rw [ihS _ hctx _ _ _ hfree.1 _ _ hA (by simp)]
                 first
                   | exact hy
                   | exact ihS _ hctx _ _ _ hfree.2 _ _ hy hne)
        | tryCatch a x hd =>
            simp only [tfFreeS, Bool.and_eq_true] at hfree
            simp only [execStmt] at hy ⊢
            rcases hA : execStmt ctx k h ρ a with ⟨h₁, c₁⟩
            rw [hA] at hy
            cases c₁ <;> first
              | (cases hy; exact absurd rfl hne)
              | (rw [ihS _ hctx _ _ _ hfree.1 _ _ hA (by simp)]
                 first
                   | exact hy
                   | exact ihS _ hctx _ _ _ hfree.2 _ _ hy hne)
        | ifte cnd t el =>
            simp only [tfFreeS, Bool.and_eq_true] at hfree
            simp only [execStmt] at hy ⊢
            rcases hA : evalExpr ctx k h ρ cnd with ⟨h₁, r₁⟩
            rw [hA] at hy
            cases r₁ with
            | exn v => rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy
            | hole l => rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy
            | outOfFuel => cases hy; exact absurd rfl hne
            | val v =>
                rw [ihE _ hctx _ _ _ _ _ hA (by simp)]
                dsimp only at hy ⊢
                by_cases hv : v.truthy = true
                · rw [if_pos hv] at hy ⊢
                  exact ihS _ hctx _ _ _ hfree.1 _ _ hy hne
                · rw [if_neg hv] at hy ⊢
                  exact ihS _ hctx _ _ _ hfree.2 _ _ hy hne
        | loop cnd bdy =>
            have hb : tfFreeS bdy = true := by simpa [tfFreeS] using hfree
            simp only [execStmt] at hy ⊢
            rcases hA : evalExpr ctx k h ρ cnd with ⟨h₁, r₁⟩
            rw [hA] at hy
            cases r₁ with
            | exn v => rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy
            | hole l => rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy
            | outOfFuel => cases hy; exact absurd rfl hne
            | val v =>
                rw [ihE _ hctx _ _ _ _ _ hA (by simp)]
                dsimp only at hy ⊢
                by_cases hv : v.truthy = true
                · rw [if_pos hv] at hy ⊢
                  rcases hB : execStmt ctx k h₁ ρ bdy with ⟨h₂, c₂⟩
                  rw [hB] at hy
                  cases c₂ <;> first
                    | (cases hy; exact absurd rfl hne)
                    | (rw [ihS _ hctx _ _ _ hb _ _ hB (by simp)]
                       first
                         | exact hy
                         | exact ihS _ hctx _ _ _ hfree _ _ hy hne)
                · rw [if_neg hv] at hy ⊢; exact hy
        | forIn x e bdy =>
            have hb : tfFreeS bdy = true := by simpa [tfFreeS] using hfree
            simp only [execStmt] at hy ⊢
            rcases hA : evalExpr ctx k h ρ e with ⟨h₁, r₁⟩
            rw [hA] at hy
            cases r₁ with
            | exn v => rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy
            | hole l => rw [ihE _ hctx _ _ _ _ _ hA (by simp)]; exact hy
            | outOfFuel => cases hy; exact absurd rfl hne
            | val v =>
                rw [ihE _ hctx _ _ _ _ _ hA (by simp)]
                dsimp only at hy ⊢
                cases hit : Val.iterable v with
                | none => rw [hit] at hy; exact hy
                | some vs =>
                    rw [hit] at hy
                    exact ihR _ hctx _ _ _ _ _ hb _ _ hy hne
      · intro ctx hctx h ρ x vs bdy hfree h' c hy hne
        cases vs with
        | nil => exact hy
        | cons v vs =>
            simp only [execFor] at hy ⊢
            rcases hA : execStmt ctx k h (ρ.set x v) bdy with ⟨h₁, c₁⟩
            rw [hA] at hy
            cases c₁ <;> first
              | (cases hy; exact absurd rfl hne)
              | (rw [ihS _ hctx _ _ _ hfree _ _ hA (by simp)]
                 first
                   | exact hy
                   | exact ihR _ hctx _ _ _ _ _ hfree _ _ hy hne)


/-- The suffix scanner in `Ctx.resolve` only ever returns a function drawn from the list it
scanned, or the accumulator it started with. -/
private theorem resolve_go_mem (sfx : String) :
    ∀ (ps : FuncTable) (acc : Option Func) (f : Func),
      Ctx.resolve.go sfx ps acc = some f → (∃ p ∈ ps, p.2 = f) ∨ acc = some f := by
  intro ps
  induction ps with
  | nil => intro acc f hg; right; simpa [Ctx.resolve.go] using hg
  | cons p ps ih =>
      obtain ⟨kk, ff⟩ := p
      intro acc f hg
      cases acc with
      | none =>
          simp only [Ctx.resolve.go] at hg
          split at hg
          · rcases ih _ _ hg with ⟨q, hq, hq2⟩ | hacc
            · exact Or.inl ⟨q, List.mem_cons_of_mem _ hq, hq2⟩
            · exact Or.inl ⟨(kk, ff), List.mem_cons_self, by simpa using hacc⟩
          · rcases ih _ _ hg with ⟨q, hq, hq2⟩ | hacc
            · exact Or.inl ⟨q, List.mem_cons_of_mem _ hq, hq2⟩
            · simp at hacc
      | some g =>
          simp only [Ctx.resolve.go] at hg
          split at hg
          · simp at hg
          · rcases ih _ _ hg with ⟨q, hq, hq2⟩ | hacc
            · exact Or.inl ⟨q, List.mem_cons_of_mem _ hq, hq2⟩
            · exact Or.inr hacc

/-- The table-wide condition implies the resolution-wide one: if no function in the table
uses `tryFinally`, then neither does anything the interpreter can reach. -/
theorem tfFree_of_table {ctx : Ctx}
    (hT : ∀ p ∈ ctx.table, tfFreeS p.2.body = true) : TFFreeCtx ctx := by
  have hres : ∀ n fn, ctx.resolve n = some fn → tfFreeS fn.body = true := by
    intro n fn hr
    rw [Ctx.resolve] at hr
    split at hr
    · rename_i a f hfind
      have hmem := List.mem_of_find?_eq_some hfind
      have : f = fn := by simpa using hr
      exact this ▸ hT (a, f) hmem
    · rcases resolve_go_mem _ _ _ _ hr with ⟨q, hq, hq2⟩ | hacc
      · exact hq2 ▸ hT q hq
      · simp at hacc
  refine ⟨hres, ?_⟩
  intro c m fn hr
  rw [Ctx.resolveMethod] at hr
  split at hr
  · rename_i a f rest hfilt
    have hmem : (a, f) ∈ ctx.table.filter
        (fun p => p.1.endsWith ("." ++ c ++ "." ++ m)) := by
      rw [hfilt]; exact List.mem_cons_self
    have : f = fn := by simpa using hr
    exact this ▸ hT (a, f) (List.mem_filter.mp hmem).1
  · exact hres m fn hr

/-! ## Public statements

Each of the seven interpreter functions, at `k` and at `k+1`, and then the `k ≤ k'`
corollary. All carry `TFFreeCtx` (no reachable function body uses `tryFinally`) and, where
the function takes a statement, that the statement is `tryFinally`-free. See `tfFreeS` and
`tryFinally_breaks_fuel_mono` for why that exclusion is necessary rather than an artefact
of the proof. -/

/-- Raising the budget by one cannot change an expression result that did not run out of
fuel. -/
theorem evalExpr_fuel_succ {ctx : Ctx} (hctx : TFFreeCtx ctx) {k : Nat} {h h' : Heap}
    {ρ : Env} {e : Expr} {r : EResult}
    (he : evalExpr ctx k h ρ e = (h', r)) (hne : r ≠ .outOfFuel) :
    evalExpr ctx (k+1) h ρ e = (h', r) :=
  (fuelStep k).1 ctx hctx h ρ e h' r he hne

/-- `applyFunc` version. -/
theorem applyFunc_fuel_succ {ctx : Ctx} (hctx : TFFreeCtx ctx) {k : Nat} {h h' : Heap}
    {fn : Func} (hfn : tfFreeS fn.body = true) {self? : Option Val} {vs : List Val}
    {kws : List (String × Val)}
    {r : EResult} (he : applyFunc ctx k h fn self? vs kws = (h', r))
    (hne : r ≠ .outOfFuel) :
    applyFunc ctx (k+1) h fn self? vs kws = (h', r) :=
  (fuelStep k).2.1 ctx hctx h fn hfn self? vs kws h' r he hne

/-- `applyClosure` version. -/
theorem applyClosure_fuel_succ {ctx : Ctx} (hctx : TFFreeCtx ctx) {k : Nat} {h h' : Heap}
    {fn : Func} (hfn : tfFreeS fn.body = true) {cap : List (String × Val)}
    {vs : List Val} {kws : List (String × Val)} {r : EResult}
    (he : applyClosure ctx k h fn cap vs kws = (h', r)) (hne : r ≠ .outOfFuel) :
    applyClosure ctx (k+1) h fn cap vs kws = (h', r) :=
  (fuelStep k).2.2.1 ctx hctx h fn hfn cap vs kws h' r he hne

/-- `evalList` version. Its "out of fuel" is spelled `Sum.inl EResult.outOfFuel`, since the
function returns `Sum EResult (List Val × List (String × Val))`. -/
theorem evalList_fuel_succ {ctx : Ctx} (hctx : TFFreeCtx ctx) {k : Nat} {h h' : Heap}
    {ρ : Env} {es : List Expr} {r : Sum EResult (List Val × List (String × Val))}
    (he : evalList ctx k h ρ es = (h', r)) (hne : r ≠ .inl .outOfFuel) :
    evalList ctx (k+1) h ρ es = (h', r) :=
  (fuelStep k).2.2.2.1 ctx hctx h ρ es h' r he hne

/-- `evalPairs` version, same `Sum.inl EResult.outOfFuel` spelling. -/
theorem evalPairs_fuel_succ {ctx : Ctx} (hctx : TFFreeCtx ctx) {k : Nat} {h h' : Heap}
    {ρ : Env} {ps : List (Expr × Expr)} {r : Sum EResult (List (Val × Val))}
    (he : evalPairs ctx k h ρ ps = (h', r)) (hne : r ≠ .inl .outOfFuel) :
    evalPairs ctx (k+1) h ρ ps = (h', r) :=
  (fuelStep k).2.2.2.2.1 ctx hctx h ρ ps h' r he hne

/-- `execStmt` version. Its "out of fuel" is `Ctl.outOfFuel`, a constructor of `Ctl`
rather than of `EResult`. -/
theorem execStmt_fuel_succ {ctx : Ctx} (hctx : TFFreeCtx ctx) {k : Nat} {h h' : Heap}
    {ρ : Env} {st : Stmt} (hst : tfFreeS st = true) {c : Ctl}
    (he : execStmt ctx k h ρ st = (h', c)) (hne : c ≠ .outOfFuel) :
    execStmt ctx (k+1) h ρ st = (h', c) :=
  (fuelStep k).2.2.2.2.2.1 ctx hctx h ρ st hst h' c he hne

/-- `execFor` version, also with `Ctl.outOfFuel`. -/
theorem execFor_fuel_succ {ctx : Ctx} (hctx : TFFreeCtx ctx) {k : Nat} {h h' : Heap}
    {ρ : Env} {x : String} {vs : List Val} {body : Stmt} (hb : tfFreeS body = true)
    {c : Ctl} (he : execFor ctx k h ρ x vs body = (h', c)) (hne : c ≠ .outOfFuel) :
    execFor ctx (k+1) h ρ x vs body = (h', c) :=
  (fuelStep k).2.2.2.2.2.2 ctx hctx h ρ x vs body hb h' c he hne

/-- **Fuel monotonicity for expressions**: any larger budget gives the same heap and the
same result. -/
theorem evalExpr_fuel_mono {ctx : Ctx} (hctx : TFFreeCtx ctx) {k k' : Nat} {h h' : Heap}
    {ρ : Env} {e : Expr} {r : EResult} (hk : k ≤ k')
    (he : evalExpr ctx k h ρ e = (h', r)) (hne : r ≠ .outOfFuel) :
    evalExpr ctx k' h ρ e = (h', r) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction d with
  | zero => exact he
  | succ n ih => exact evalExpr_fuel_succ hctx ih hne

/-- `applyFunc`, any larger budget. -/
theorem applyFunc_fuel_mono {ctx : Ctx} (hctx : TFFreeCtx ctx) {k k' : Nat} {h h' : Heap}
    {fn : Func} (hfn : tfFreeS fn.body = true) {self? : Option Val} {vs : List Val}
    {kws : List (String × Val)}
    {r : EResult} (hk : k ≤ k') (he : applyFunc ctx k h fn self? vs kws = (h', r))
    (hne : r ≠ .outOfFuel) : applyFunc ctx k' h fn self? vs kws = (h', r) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction d with
  | zero => exact he
  | succ n ih => exact applyFunc_fuel_succ hctx hfn ih hne

/-- `applyClosure`, any larger budget. -/
theorem applyClosure_fuel_mono {ctx : Ctx} (hctx : TFFreeCtx ctx) {k k' : Nat}
    {h h' : Heap} {fn : Func} (hfn : tfFreeS fn.body = true)
    {cap : List (String × Val)} {vs : List Val} {kws : List (String × Val)}
    {r : EResult} (hk : k ≤ k')
    (he : applyClosure ctx k h fn cap vs kws = (h', r)) (hne : r ≠ .outOfFuel) :
    applyClosure ctx k' h fn cap vs kws = (h', r) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction d with
  | zero => exact he
  | succ n ih => exact applyClosure_fuel_succ hctx hfn ih hne

/-- `evalList`, any larger budget. -/
theorem evalList_fuel_mono {ctx : Ctx} (hctx : TFFreeCtx ctx) {k k' : Nat} {h h' : Heap}
    {ρ : Env} {es : List Expr} {r : Sum EResult (List Val × List (String × Val))} (hk : k ≤ k')
    (he : evalList ctx k h ρ es = (h', r)) (hne : r ≠ .inl .outOfFuel) :
    evalList ctx k' h ρ es = (h', r) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction d with
  | zero => exact he
  | succ n ih => exact evalList_fuel_succ hctx ih hne

/-- `evalPairs`, any larger budget. -/
theorem evalPairs_fuel_mono {ctx : Ctx} (hctx : TFFreeCtx ctx) {k k' : Nat} {h h' : Heap}
    {ρ : Env} {ps : List (Expr × Expr)} {r : Sum EResult (List (Val × Val))} (hk : k ≤ k')
    (he : evalPairs ctx k h ρ ps = (h', r)) (hne : r ≠ .inl .outOfFuel) :
    evalPairs ctx k' h ρ ps = (h', r) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction d with
  | zero => exact he
  | succ n ih => exact evalPairs_fuel_succ hctx ih hne

/-- **Fuel monotonicity for statements**, any larger budget. -/
theorem execStmt_fuel_mono {ctx : Ctx} (hctx : TFFreeCtx ctx) {k k' : Nat} {h h' : Heap}
    {ρ : Env} {st : Stmt} (hst : tfFreeS st = true) {c : Ctl} (hk : k ≤ k')
    (he : execStmt ctx k h ρ st = (h', c)) (hne : c ≠ .outOfFuel) :
    execStmt ctx k' h ρ st = (h', c) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction d with
  | zero => exact he
  | succ n ih => exact execStmt_fuel_succ hctx hst ih hne

/-- `execFor`, any larger budget. -/
theorem execFor_fuel_mono {ctx : Ctx} (hctx : TFFreeCtx ctx) {k k' : Nat} {h h' : Heap}
    {ρ : Env} {x : String} {vs : List Val} {body : Stmt} (hb : tfFreeS body = true)
    {c : Ctl} (hk : k ≤ k') (he : execFor ctx k h ρ x vs body = (h', c))
    (hne : c ≠ .outOfFuel) : execFor ctx k' h ρ x vs body = (h', c) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction d with
  | zero => exact he
  | succ n ih => exact execFor_fuel_succ hctx hb ih hne

/-! ## The excluded case, exhibited

Not an artefact of the proof: `tryFinally` really does break fuel monotonicity. -/

/-- A context with no functions at all — the exclusion has nothing to do with calls. -/
def cexCtx : Ctx := { dialect := .python, table := [], globals := 0 }

/-- A heap holding just the module-globals frame. -/
def cexHeap : Heap := [{ cls := "<module>", fields := [], captured := [] }]

/-- `try: x = 1; x = 2 finally: return x`.

With 4 units of fuel the body runs out after the first assignment; the finalizer exits
abnormally, which *discards* the body's pending `outOfFuel` and returns `x = 1`. With 5
units the body completes and the finalizer sees `x = 2`. Both results are ordinary — no
`outOfFuel` anywhere — and they differ. -/
def cexStmt : Stmt :=
  .tryFinally
    (.seq (.setGlobal "x" (.lit (.int 1)))
      (.seq (.setGlobal "x" (.lit (.int 2))) .skip))
    (.ret (.name "x"))

/-- **The side condition is necessary.** A `tryFinally` statement whose result at fuel 4 is
`return 1` and at fuel 5 is `return 2`, neither of them `outOfFuel`. So the unrestricted
form of the theorem — `execStmt ctx k h ρ s = (h', c) → c ≠ .outOfFuel →
execStmt ctx (k+1) h ρ s = (h', c)` — is false, and `tfFreeS` is not a proof artefact. -/
theorem tryFinally_breaks_fuel_mono :
    (execStmt cexCtx 4 cexHeap [] cexStmt).2 = .ret (.int 1) ∧
    (execStmt cexCtx 5 cexHeap [] cexStmt).2 = .ret (.int 2) ∧
    tfFreeS cexStmt = false :=
  ⟨rfl, rfl, rfl⟩

/-- The complete list of interpreter constructors excluded from fuel monotonicity, as a
machine-checkable value. Exactly one: `Stmt.tryFinally`, for the reason exhibited by
`tryFinally_breaks_fuel_mono`. Every other `Expr` and `Stmt` constructor, and all seven
mutually recursive interpreter functions, are covered. -/
def fuelMonoExclusions : List String := ["Stmt.tryFinally"]

-- Axiom audit: these must list only `propext`, `Classical.choice`, `Quot.sound`.
#print axioms evalExpr_fuel_mono
#print axioms applyFunc_fuel_mono
#print axioms applyClosure_fuel_mono
#print axioms evalList_fuel_mono
#print axioms evalPairs_fuel_mono
#print axioms execStmt_fuel_mono
#print axioms execFor_fuel_mono
#print axioms tfFree_of_table
#print axioms tryFinally_breaks_fuel_mono

end Autoform.Core
