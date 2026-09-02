import Autoform.Lang.Core.Syntax
import Autoform.Lang.Core.Numeric
import Autoform.Lang.Core.Stdlib

/-!
# Core — semantics

A fuel-indexed definitional interpreter for the universal core language. This is the
formal interpreter that an arbitrary codebase is mapped onto.

Design commitments, each of which exists to keep the trust story honest:

* **Total.** Structurally recursive on fuel, so evaluation always terminates and Lean
  accepts it without `partial`. No `sorry`, no `unsafe`.
* **Holes are observable.** Reaching a hole yields a distinguished outcome — not an
  error, not a value. A theorem about a program can therefore never accidentally
  quantify over behaviour we failed to translate.
* **Ignorance is distinguishable from behaviour.** `outOfFuel` (we did not run long
  enough), `hole` (we did not translate this), a raised exception, and a genuine result
  are four different outcomes, because they mean four different things.
* **The heap is explicit.** Objects are boxed and mutable; the heap is threaded through
  evaluation rather than hidden in a monad, so the recursion stays visibly structural.
-/

namespace Autoform.Core

/-- Variable environment. -/
abbrev Env := List (String × Val)

namespace Env

/-- Look up a variable; unbound reads are `unit`. -/
def get (ρ : Env) (x : String) : Val :=
  match ρ.find? (·.1 == x) with
  | some (_, v) => v
  | none        => .unit

/-- Bind a variable, shadowing any previous binding. -/
def set (ρ : Env) (x : String) (v : Val) : Env := (x, v) :: ρ

/-- Remove every binding of a variable (`del x`). -/
def del (ρ : Env) (x : String) : Env := ρ.filter (·.1 != x)

end Env




/-!
## Dialect-sensitive arithmetic

Integer division and modulo are **not** universal: Python floors, C and Java truncate
toward zero. Hardcoding one convention silently mistranslates every other language, so
the dialect is carried explicitly and recorded by the transpiler.

This was not designed in. It was found by `scripts/differential.py`, which caught
`fmod(6, -9)` returning `6` in Lean against CPython's `-3`, and the same error
propagating into `gcdish`. That is what the conformance oracle is for.
-/

/-- Integer division under a dialect.

Unused by `applyBinop` (superseded by `NumConfig.quot`, per this section's own intro);
kept, and kept exhaustive, because `Numeric.lean` cites it as the pattern's first
instance. `.javascript` mirrors `.python`'s arm: `Dialect.toNumConfig .javascript` is
`NumConfig.python`, whose `divRound` is `.floor`. -/
def Dialect.idiv : Dialect → Int → Int → Int
  | .python,     a, b => Int.fdiv a b
  | .cLike,      a, b => Int.tdiv a b
  | .javascript, a, b => Int.fdiv a b

/-- Integer remainder under a dialect. See `idiv` — unused, kept exhaustive and
consistent with it. -/
def Dialect.imod : Dialect → Int → Int → Int
  | .python,     a, b => Int.fmod a b
  | .cLike,      a, b => Int.tmod a b
  | .javascript, a, b => Int.fmod a b


/-- Result of executing a statement: how control left it. -/
inductive Ctl where
  | normal    : Env → Ctl
  | ret       : Val → Ctl
  | brk       : Env → Ctl
  | cont      : Env → Ctl
  | exn       : Val → Ctl
  | hole      : String → Ctl
  | outOfFuel : Ctl
  deriving Repr, Inhabited

/-- Lift a machine-integer outcome into an evaluation outcome.

`ub` becomes a **hole**, not a number. A program that relies on undefined behaviour has
no defined meaning at that point, so the honest translation is "we cannot say" — the same
discipline applied to untranslated constructs. Returning some plausible number here would
be the same class of error as the original modulo bug, only harder to detect. -/
def numToE : NumResult → EResult
  | .ok v      => .val (.int v)
  | .divZero   => .exn (.str "ZeroDivisionError")
  | .trap r    => .exn (.str r)
  | .ub r      => .hole s!"ub:{r}"

/-! ### Floating point

`Autoform/Lang/Core/Float.lean` supplies the value domain and the arithmetic; this section
is only the wiring. Three decisions are recorded here because they are the ones that can
be silently wrong.

**Promotion.** In mixed `int`/`float` *arithmetic* both Python and C convert the integer
to a double and compute in binary64, so `flOfVal` promotes. Python raises `OverflowError`
if the integer is too large to convert (reachable only under `.python`, since `.cLike`
integers are 32-bit and always convertible), and `FConfig.ofInt` reproduces that.

**Comparison does *not* promote — under Python.** CPython compares an `int` and a `float`
*exactly*: `10**23 == 1e23` is `False`, because `1e23` is really
`99999999999999991611392`. C has no bignums and its `==` promotes, so the two dialects
genuinely differ here and `flCmp` splits on the dialect. Promoting under `.python` would
be a silent wrong answer of the `floorDiv` family.

**`/` on two integers is still floor division, and that is now a known wrong answer for
Python.** CPython's `/` is *true* division (`7 / 2 == 3.5`) and `//` floors. The
transpiler currently maps Python's `//` onto the `"/"` operator string (see the note above
`applyBinop_py_div` and `Refine.lean`'s discussion of `op:floorDiv`), so `"/"` on two
`.int`s is left exactly as it was — changing it would silently break every `//` in the
corpora. `"//"` is now a distinct operator with the floor semantics, so the fix is in
`cartographer/render_lean.py`: emit `"//"` for floor division and `"/"` for true division,
after which `"/"` on two `.int`s under `.python` must become `flBinop`. Until then this is
a recorded silent mistranslation, not an accident.

**NaN is unordered.** `flCmp` returns `none`, and `ordToE` turns that into `false` for
`<`, `<=`, `>`, `>=` and `==`, and `true` for `!=`. That is CPython's behaviour and it is
not expressible by an `Ordering` alone. -/

/-- Lift a float outcome into an evaluation outcome. `ub` and `unmodelled` both become
holes — the first because the language does not define the result, the second because we
have not modelled it — and they keep distinct labels so the ledger can tell them apart. -/
def fresToE : FResult → EResult
  | .ok v         => .val (.float v)
  | .exn r        => .exn (.str r)
  | .ub r         => .hole s!"ub:{r}"
  | .unmodelled r => .hole r

/-- Promote a numeric value to the dialect's float format, as mixed arithmetic requires.
`none` means "not a number", not "failed". -/
def flOfVal (d : Dialect) : Val → Option FResult
  | .float f => some (if f.fmt == (d.toFConfig).fmt then .ok f
                      else .unmodelled "float:format-mismatch")
  | .int n   => some ((d.toFConfig).ofInt n)
  | _        => none

/-- Compare two numeric values, at least one a float. `none` is *unordered* (NaN, or a
non-numeric operand), which is not the same as "equal" or "less". -/
def flCmp (d : Dialect) : Val → Val → Option Ordering
  | .float x, .float y => Fl.cmpv x y
  | .int n,   .float y =>
      match d with
      | .python => Fl.cmpIntv n y                     -- exact, no conversion
      -- `comparesIntFloatExactly d = false` for both: JS has no separate int type to be
      -- exact about, so it promotes like C.
      | .cLike | .javascript =>
          match (d.toFConfig).ofInt n with
          | .ok x => Fl.cmpv x y
          | _     => none
  | .float x, .int n   =>
      (match d with
       | .python => Fl.cmpIntv n x
       | .cLike | .javascript =>
           match (d.toFConfig).ofInt n with
           | .ok y => Fl.cmpv y x
           | _     => none).map Ordering.swap
  | _,        _        => none

/-- Turn a comparison outcome into the answer for a relational operator. Unordered is
`false` everywhere except `!=`. -/
def ordToE (op : String) (o : Option Ordering) : EResult :=
  match op with
  | "<"  => .val (.bool (o == some .lt))
  | "<=" => .val (.bool (o == some .lt || o == some .eq))
  | ">"  => .val (.bool (o == some .gt))
  | ">=" => .val (.bool (o == some .gt || o == some .eq))
  | "==" => .val (.bool (o == some .eq))
  | "!=" => .val (.bool (!(o == some .eq)))
  | _    => .hole s!"binop:{op}"

/-- Binary operators where at least one operand is a float. -/
def flBinop (d : Dialect) (op : String) (a b : Val) : EResult :=
  match op with
  | "&&" => .val (.bool (a.truthy && b.truthy))
  | "||" => .val (.bool (a.truthy || b.truthy))
  | "<" | "<=" | ">" | ">=" | "==" | "!=" => ordToE op (flCmp d a b)
  | "+" | "-" | "*" | "/" | "%" =>
      match flOfVal d a, flOfVal d b with
      | some (.ok x), some (.ok y) =>
          let fc := d.toFConfig
          fresToE (match op with
                   | "+" => fc.add x y
                   | "-" => fc.sub x y
                   | "*" => fc.mul x y
                   | "/" => fc.div x y
                   | _   => fc.pyMod x y)
        -- a failed promotion (Python's `OverflowError` on a huge int) is the answer
      | some r, some (.ok _) => fresToE r
      | some (.ok _), some r => fresToE r
      | some r, some _       => fresToE r
      | _, _                 => .hole s!"binop:{op}:non-numeric"
  -- CPython's `float.__floordiv__` is a multi-step rounding sequence (`fmod`, then a
  -- rounded subtraction, then `floor`, then a half-ulp correction). Modelling it
  -- approximately would produce divergences on the boundary cases it exists to get
  -- right, so it is a hole until it is modelled properly.
  | "//" => .hole "binop://:float-floordiv"
  -- `x ** y` on floats is `pow`, which IEEE does define, but which this model does not
  -- implement. See `Float.lean`'s "what is deliberately NOT modelled".
  | "**" => .hole "float:pow"
  | _    => .hole s!"binop:{op}"

/-- Whether `==`/`!=` on these operands has to consult the heap.

Only a REFERENCE forces it: two distinct objects with equal contents are `==` in Python, and
no structural compare of two refs can see that. Everything else stays on `applyBinop`, which
is heap-free and reducible -- the property `Refine.lean` is built on. Named rather than
inlined so proofs can discharge it by `simp` on concrete operands. -/
def binopNeedsHeap (op : String) (x y : Val) : Bool :=
  (op == "==" || op == "!=") && (x.kind == 8 || y.kind == 8)

@[simp] theorem binopNeedsHeap_int_left (op : String) (i : Int) (y : Val) :
    binopNeedsHeap op (.int i) y = ((op == "==" || op == "!=") && y.kind == 8) := by
  simp [binopNeedsHeap, Val.kind]

@[simp] theorem binopNeedsHeap_arith (x y : Val) (op : String)
    (h : op ≠ "==") (h2 : op ≠ "!=") : binopNeedsHeap op x y = false := by
  simp [binopNeedsHeap, beq_iff_eq, h, h2]

/-- Built-in binary operators. Unknown operators are holes, not guesses.

Integer arithmetic goes through `NumConfig`, so width and overflow policy follow the
source dialect: Python gets bignums, C-like gets 32-bit two's-complement. -/
def applyBinop (d : Dialect) (op : String) (a b : Val) : EResult :=
  let nc := d.toNumConfig
  match op, a, b with
  | "+",  .int x,   .int y   => numToE (nc.add x y)
  -- Item 6: a C `char*` is not a Python `str`. In C, `+` on pointers is POINTER
  -- ARITHMETIC and `<`/`>`/`==` compare ADDRESSES, not contents. Core has one `Val.str`
  -- for both, so applying Python's string semantics under `.cLike` would be a silent
  -- wrong answer of exactly the kind §12 is about. Under `.cLike` these are holes.
  | "+",  .str _,   .str _   =>
      if d.stringsAreValues then
        .val (.str (match a, b with | .str x, .str y => x ++ y | _, _ => ""))
      else .hole "str:pointer-arithmetic-not-modelled"
  | "+",  .list x,  .list y  => .val (.list (x ++ y))
  | "+",  .tuple x, .tuple y => .val (.tuple (x ++ y))
  | "-",  .int x, .int y => numToE (nc.sub x y)
  | "*",  .int x, .int y => numToE (nc.mul x y)
  | "/",  .int x, .int y => numToE (nc.div x y)
  | "%",  .int x, .int y => numToE (nc.mod x y)
  -- ### Bitwise operators
  --
  -- These are `&`, `|`, `^`, `<<`, `>>` and `>>>` — the **bitwise** operations, not the
  -- logical ones. `<operator>.and` / `<operator>.or` in a CPG are these, and the exporter
  -- used to map them onto `"&&"` / `"||"`, which returned a boolean where C returns a
  -- number: `(flags & MASK) == MASK` became `true == MASK`. That silent wrong answer is
  -- why they were unmapped for so long, and it is why they get their **own** operator
  -- strings here rather than sharing the logical ones.
  --
  -- The arithmetic is `NumConfig`'s, so the width and overflow policy are the dialect's:
  -- under `.cLike` every integer is 32-bit two's-complement, so `1 << 31` is `INT_MIN`
  -- (the wrapping config the oracle measures) and `-1 & 255` is `255`.
  --
  -- `>>` and `>>>` are **two different operators** and the difference is only visible on
  -- a negative left operand: C's `>>` on a signed value is arithmetic (sign-extending) and
  -- on an unsigned value it is logical (zero-filling). Core cannot recover the operand's
  -- signedness at run time — a `Val.int` carries no type — so the *exporter* decides,
  -- from the CPG's static type, which of the two it emits, and holes when the type is
  -- unknown. Collapsing them here would reintroduce exactly the `<operator>.and` mistake
  -- in a place where it is much harder to see.
  | "&",  .int x, .int y => numToE (nc.band x y)
  | "|",  .int x, .int y => numToE (nc.bor x y)
  | "^",  .int x, .int y => numToE (nc.bxor x y)
  | "<<", .int x, .int y => numToE (nc.shl x y)
  | ">>", .int x, .int y => numToE (nc.shr x y)
  | ">>>", .int x, .int y => numToE ({ nc with negRightShift := .logical }.shr x y)
  | "<",  .int x, .int y => .val (.bool (x < y))
  | "<=", .int x, .int y => .val (.bool (x ≤ y))
  | ">",  .int x, .int y => .val (.bool (x > y))
  | ">=", .int x, .int y => .val (.bool (x ≥ y))
  | "<",  .str x, .str y =>
      if d.stringsAreValues then .val (.bool (x < y))
      else .hole "str:pointer-compare-not-modelled"
  | ">",  .str x, .str y =>
      if d.stringsAreValues then .val (.bool (x > y))
      else .hole "str:pointer-compare-not-modelled"
  -- `==` on strings compares contents in Python and addresses in C. `Val.beq` is
  -- structural, so it is right for Python and wrong for C.
  | "==", .str _, .str _ =>
      if d.stringsAreValues then .val (.bool (Val.beq a b))
      else .hole "str:pointer-equality-not-modelled"
  | "!=", .str _, .str _ =>
      if d.stringsAreValues then .val (.bool (!Val.beq a b))
      else .hole "str:pointer-equality-not-modelled"
  -- Floats, including mixed `int`/`float`. Placed before the generic `==`/`!=` so that
  -- the dialect split on comparison (see `flCmp`) is not bypassed by `Val.beq`.
  | op, .float _, .float _ => flBinop d op a b
  | op, .float _, .int _   => flBinop d op a b
  | op, .int _,   .float _ => flBinop d op a b
  -- Floor division. Distinct from `/` on purpose: Python's `/` is *true* division and
  -- `//` floors. The transpiler currently maps `//` onto `"/"` (see the note on
  -- `applyBinop_py_div`), so `"//"` is unreachable from the present corpora and exists so
  -- that the transpiler can start emitting the two separately.
  | "//", .int x, .int y => numToE (nc.div x y)
  -- `006-reduce-remaining-holes`, Story 5: interior-pointer arithmetic and
  -- comparison. Placed BEFORE the generic `"==",x,y`/`"!=",x,y` catch-all just
  -- below, deliberately: those would otherwise route an `.iref`/`.iref` pair
  -- through `Val.beq`, whose own wildcard (`Syntax.lean`) answers `false`
  -- unconditionally, silently wrong for FR-013's own "cross-object `==` is
  -- well-defined, not a hole" requirement.
  --
  -- Same-object arithmetic/subtraction/ordering succeed (an array's elements
  -- only -- a struct FIELD's address has no `+`/`-`/ordering in standard C, so a
  -- `.fld` selector on either side of one of those three stays a hole, `Sel`'s own
  -- doc comment's reasoning). Cross-object arithmetic, subtraction and ordering
  -- (undefined behaviour in C itself) become a DYNAMIC hole -- evaluation-time, not
  -- export-time, mirroring the already-shipped `.str`/`.str` `.cLike`
  -- "pointer-arithmetic/-compare-not-modelled" precedent just above. Equality and
  -- inequality are NOT gated on same-object: comparing addresses for equality
  -- across two different objects is well-defined in C (it is only ordering and
  -- subtraction across objects that are UB), so `==`/`!=` answer directly from
  -- `(ref, selector)` structural equality regardless of which object each side
  -- names.
  | "+", .iref r sel, .int n =>
      match sel with
      | .idx i => .val (.iref r (.idx (i + n)))
      | .fld _ => .hole "iref:arith-on-field"
  | "+", .int n, .iref r sel =>
      match sel with
      | .idx i => .val (.iref r (.idx (i + n)))
      | .fld _ => .hole "iref:arith-on-field"
  | "-", .iref r sel, .int n =>
      match sel with
      | .idx i => .val (.iref r (.idx (i - n)))
      | .fld _ => .hole "iref:arith-on-field"
  | "-", .iref r1 s1, .iref r2 s2 =>
      if r1 != r2 then .hole "iref:cross-object"
      else match s1, s2 with
           | .idx i, .idx j => numToE (nc.sub i j)
           | _,      _      => .hole "iref:sub-non-index"
  | "<",  .iref r1 s1, .iref r2 s2 =>
      if r1 != r2 then .hole "iref:cross-object"
      else match s1, s2 with
           | .idx i, .idx j => .val (.bool (i < j))
           | _,      _      => .hole "iref:cmp-non-index"
  | "<=", .iref r1 s1, .iref r2 s2 =>
      if r1 != r2 then .hole "iref:cross-object"
      else match s1, s2 with
           | .idx i, .idx j => .val (.bool (i ≤ j))
           | _,      _      => .hole "iref:cmp-non-index"
  | ">",  .iref r1 s1, .iref r2 s2 =>
      if r1 != r2 then .hole "iref:cross-object"
      else match s1, s2 with
           | .idx i, .idx j => .val (.bool (i > j))
           | _,      _      => .hole "iref:cmp-non-index"
  | ">=", .iref r1 s1, .iref r2 s2 =>
      if r1 != r2 then .hole "iref:cross-object"
      else match s1, s2 with
           | .idx i, .idx j => .val (.bool (i ≥ j))
           | _,      _      => .hole "iref:cmp-non-index"
  | "==", .iref r1 s1, .iref r2 s2 => .val (.bool (r1 == r2 && s1 == s2))
  | "!=", .iref r1 s1, .iref r2 s2 => .val (.bool !(r1 == r2 && s1 == s2))
  | "==", x, y           => .val (.bool (Val.beq x y))
  | "!=", x, y           => .val (.bool (!Val.beq x y))
  -- Reached only when the left operand did not decide the result, so the value
  -- of the expression is the RIGHT operand under value semantics.
  | "&&", _, y           => .val (if d.boolOpsAreValues then y else .bool y.truthy)
  | "||", _, y           => .val (if d.boolOpsAreValues then y else .bool y.truthy)
  | _, _, _              => .hole s!"binop:{op}"

/-!
### Operator equations

Refinement proofs need `applyBinop` to reduce cleanly. For the unbounded (Python) config
these are definitional; for fixed-width configs they are *conditional on
representability*, which is the whole point — a C function only agrees with its
mathematical model where nothing overflows.
-/

@[simp] theorem applyBinop_py_add (x y : Int) :
    applyBinop .python "+" (.int x) (.int y) = .val (.int (x + y)) := rfl
@[simp] theorem applyBinop_py_sub (x y : Int) :
    applyBinop .python "-" (.int x) (.int y) = .val (.int (x - y)) := rfl
@[simp] theorem applyBinop_py_mul (x y : Int) :
    applyBinop .python "*" (.int x) (.int y) = .val (.int (x * y)) := rfl
@[simp] theorem applyBinop_py_div (x y : Int) (h : y ≠ 0) :
    applyBinop .python "/" (.int x) (.int y) = .val (.int (Int.fdiv x y)) := by
  simp [applyBinop, numToE, Dialect.toNumConfig, NumConfig.div, NumConfig.quot,
        NumConfig.finish, NumConfig.python, IntType.inRange, IntType.wrap_unbounded, h]
@[simp] theorem applyBinop_py_mod (x y : Int) (h : y ≠ 0) :
    applyBinop .python "%" (.int x) (.int y) = .val (.int (Int.fmod x y)) := by
  simp [applyBinop, numToE, Dialect.toNumConfig, NumConfig.mod, NumConfig.quot,
        NumConfig.rem, NumConfig.finish, NumConfig.python, IntType.inRange, IntType.wrap_unbounded, h]
@[simp] theorem applyBinop_py_divZero (x : Int) :
    applyBinop .python "/" (.int x) (.int 0) = .exn (.str "ZeroDivisionError") := rfl
@[simp] theorem applyBinop_py_modZero (x : Int) :
    applyBinop .python "%" (.int x) (.int 0) = .exn (.str "ZeroDivisionError") := rfl

/-! ### The two measured JS bugs (research.md / docs/languages.md), checked here rather
than only in a real corpus, whose export shape may or may not exercise them. -/

/-- Node: `0 || 5` is `5`. Under the OLD `.cLike`-routed dialect this returned a coerced
`Val.bool`, a confirmed wrong answer. `Val`/`EResult` have no `DecidableEq` (`Syntax.lean`
derives only `Repr, Inhabited` for both), so this is `rfl`, not `decide` — matching how
`applyBinop_py_add` etc. above are proved. -/
example : applyBinop .javascript "||" (.int 0) (.int 5) = .val (.int 5) := rfl
#eval applyBinop .javascript "||" (.int 0) (.int 5)   -- val (int 5), matches Node

/-- Node: `1 && 0` is `0` (the second operand, since the first is truthy). -/
example : applyBinop .javascript "&&" (.int 1) (.int 0) = .val (.int 0) := rfl
#eval applyBinop .javascript "&&" (.int 1) (.int 0)   -- val (int 0), matches Node

/-- Node: `2147483647 + 1 === 2147483648`. Under the OLD `.cLike`-routed dialect this
wrapped to `-2147483648`, the same confirmed-wrong answer `applyBinop_c_add` above would
give (32-bit wraparound). -/
example : applyBinop .javascript "+" (.int 2147483647) (.int 1) = .val (.int 2147483648) := rfl
#eval applyBinop .javascript "+" (.int 2147483647) (.int 1)  -- val (int 2147483648)

/-! ### Float equations, and the two that must not regress

`Val.beq` on floats is the place where a plausible-looking implementation is wrong. Both
directions are pinned here, so that replacing `Fl.eqv` with structural bit equality — or
with `DecidableEq Fl`, which is derived and therefore always in scope — fails the build
rather than the oracle. This is the executable form of `Float.lean`'s
`float_beq_is_not_bit_equality`. -/

/-- **NaN is not equal to itself**, even though the two bit patterns are identical. -/
@[simp] theorem beq_float_nan_self :
    Val.beq (.float (Fl.nan Format.binary64)) (.float (Fl.nan Format.binary64)) = false := by
  decide

/-- **`-0.0` equals `+0.0`**, even though the two bit patterns differ. -/
@[simp] theorem beq_float_negzero :
    Val.beq (.float (Fl.zero Format.binary64 true))
            (.float (Fl.zero Format.binary64 false)) = true := by
  decide

/-- ...and they really are different bit patterns, so the theorem above has content. -/
theorem float_negzero_bits_differ :
    (Fl.zero Format.binary64 true).bits ≠ (Fl.zero Format.binary64 false).bits := by
  decide

/-- `-0.0` is false, like `0.0`. -/
@[simp] theorem truthy_float_negzero :
    Val.truthy (.float (Fl.zero Format.binary64 true)) = false := by decide

/-- Representability under the 32-bit signed C configuration. -/
abbrev Fits32 (x : Int) : Prop := IntType.inRange (.signed .w32) x = true

@[simp] theorem applyBinop_c_add {x y : Int} (h : Fits32 (x + y)) :
    applyBinop .cLike "+" (.int x) (.int y) = .val (.int (x + y)) := by
  simp [applyBinop, numToE, Dialect.toNumConfig, NumConfig.add, NumConfig.finish,
        NumConfig.c32Wrapv, NumConfig.c32, h]
@[simp] theorem applyBinop_c_sub {x y : Int} (h : Fits32 (x - y)) :
    applyBinop .cLike "-" (.int x) (.int y) = .val (.int (x - y)) := by
  simp [applyBinop, numToE, Dialect.toNumConfig, NumConfig.sub, NumConfig.finish,
        NumConfig.c32Wrapv, NumConfig.c32, h]
@[simp] theorem applyBinop_c_mul {x y : Int} (h : Fits32 (x * y)) :
    applyBinop .cLike "*" (.int x) (.int y) = .val (.int (x * y)) := by
  simp [applyBinop, numToE, Dialect.toNumConfig, NumConfig.mul, NumConfig.finish,
        NumConfig.c32Wrapv, NumConfig.c32, h]
@[simp] theorem applyBinop_c_div {x y : Int} (hy : y ≠ 0) (h : Fits32 (Int.tdiv x y)) :
    applyBinop .cLike "/" (.int x) (.int y) = .val (.int (Int.tdiv x y)) := by
  simp [applyBinop, numToE, Dialect.toNumConfig, NumConfig.div, NumConfig.quot,
        NumConfig.finish, NumConfig.c32Wrapv, NumConfig.c32, hy, h]
@[simp] theorem applyBinop_c_divZero (x : Int) :
    applyBinop .cLike "/" (.int x) (.int 0) = .exn (.str "ZeroDivisionError") := rfl

/-- Built-in unary operators. -/
def applyUnop (d : Dialect) (op : String) (a : Val) : EResult :=
  match op, a with
  -- Negation goes through `NumConfig` for the same reason the binary operators do:
  -- `-INT_MIN` is not representable, so under a fixed-width dialect it must wrap, trap,
  -- or become a hole — never the unrepresentable number. This path was left unchecked
  -- when `Numeric` was first wired in, and `Autoform/Refine.lean` caught it.
  | "-", .int x => numToE ((d.toNumConfig).neg x)
  -- Float negation is a sign-bit flip: exact, no rounding, and correct on `-0.0` and NaN
  -- where "subtract from zero" would not be (`0.0 - 0.0 = 0.0`, but `-(0.0) = -0.0`).
  | "-", .float f => .val (.float f.neg)
  | "!", x      => .val (.bool (!x.truthy))
  -- `~x` — **bitwise** complement, which is not `!x`. Joern spells the two
  -- `<operator>.not` and `<operator>.logicalNot`; this exporter previously mapped *both*
  -- onto `"!"`, so `~0` translated to `false`. `bnot` is `-x-1` wrapped to the dialect's
  -- width, which is two's complement at every width and never overflows.
  | "~", .int x => numToE ((d.toNumConfig).bnot x)
  -- **Width conversions.** `static_cast<uint8_t>(e)` in C++ is a unary operator whose
  -- meaning is completely determined: since C++20, conversion to any integer type is
  -- two's-complement reduction modulo `2^width`, which is exactly `IntType.wrap`. So it
  -- gets an operator here rather than a constructor in `Syntax.lean` — a cast *is* a
  -- unary operator, and spelling it as one means `Expr.hole`-freedom, fuel monotonicity,
  -- rendering and the ledger all keep working without a single new case anywhere.
  --
  -- What is deliberately **not** here:
  --
  -- * a cast to `char`, whose signedness is implementation-defined, so
  --   `static_cast<char>(200)` has no standard-mandated value;
  -- * a cast to `double`, which rounds rather than truncates and belongs to `Fl`;
  -- * a cast between *pointer* types, which reinterprets an address — and Core has no
  --   addresses. The exporter keeps that one as an `op:cast:pointer` hole. Collapsing the
  --   two would be the `<operator>.and` mistake again: same syntax, different operation.
  --
  -- A non-integer operand falls through to the hole below, labelled `unop:cast:u8` and
  -- so on, which is the honest answer for `static_cast<int>(someDouble)`.
  | "cast:i8",  .int x => .val (.int (IntType.wrap (.signed .w8) x))
  | "cast:u8",  .int x => .val (.int (IntType.wrap (.unsigned .w8) x))
  | "cast:i16", .int x => .val (.int (IntType.wrap (.signed .w16) x))
  | "cast:u16", .int x => .val (.int (IntType.wrap (.unsigned .w16) x))
  | "cast:i32", .int x => .val (.int (IntType.wrap (.signed .w32) x))
  | "cast:u32", .int x => .val (.int (IntType.wrap (.unsigned .w32) x))
  | "cast:i64", .int x => .val (.int (IntType.wrap (.signed .w64) x))
  | "cast:u64", .int x => .val (.int (IntType.wrap (.unsigned .w64) x))
  -- A `bool` converts to 1/0 at any width, in every dialect.
  | "cast:i8",  .bool b => .val (.int (if b then 1 else 0))
  | "cast:u8",  .bool b => .val (.int (if b then 1 else 0))
  | "cast:i16", .bool b => .val (.int (if b then 1 else 0))
  | "cast:u16", .bool b => .val (.int (if b then 1 else 0))
  | "cast:i32", .bool b => .val (.int (if b then 1 else 0))
  | "cast:u32", .bool b => .val (.int (if b then 1 else 0))
  | "cast:i64", .bool b => .val (.int (if b then 1 else 0))
  | "cast:u64", .bool b => .val (.int (if b then 1 else 0))
  | _, _        => .hole s!"unop:{op}"

/-- `static_cast<uint8_t>` is reduction mod 256, stated against `IntType.wrap` rather
than against `applyUnop`'s own definition. -/
@[simp] theorem applyUnop_cast_u8 (d : Dialect) (x : Int) :
    applyUnop d "cast:u8" (.int x) = .val (.int (x % 256)) := by
  cases d <;> rfl

/-- The narrowing is real: `static_cast<uint8_t>(300)` is `44`, not `300`. A cast that
returned its argument — or a hole — would make every downstream theorem about a
converting program vacuously true, so this is checked by evaluation. -/
example : applyUnop .cLike "cast:u8" (.int 300) = .val (.int 44) := by rfl

/-- And it is not the identity on the signed side either: `static_cast<int8_t>(200)` is
`-56`. -/
example : applyUnop .cLike "cast:i8" (.int 200) = .val (.int (-56)) := by rfl

/-- A cast of something that is not a number is a hole, not a guess. -/
example : applyUnop .cLike "cast:u8" (.str "x") = .hole "unop:cast:u8" := by rfl

/-- Negation is definitional under the unbounded (Python) config. -/
@[simp] theorem applyUnop_py_neg (x : Int) :
    applyUnop .python "-" (.int x) = .val (.int (-x)) := rfl

/-- Under a fixed-width dialect negation only equals mathematical negation where the
result is representable. `-INT_MIN` is precisely where it does not. -/
@[simp] theorem applyUnop_c_neg {x : Int} (h : Fits32 (-x)) :
    applyUnop .cLike "-" (.int x) = .val (.int (-x)) := by
  simp [applyUnop, numToE, Dialect.toNumConfig, NumConfig.neg, NumConfig.finish,
        NumConfig.c32Wrapv, NumConfig.c32, h]

/-- Unary minus on a float is a sign flip, in every dialect — no rounding, and correct on
`-0.0` and NaN, where "subtract from zero" would not be. -/
@[simp] theorem applyUnop_float_neg (d : Dialect) (f : Fl) :
    applyUnop d "-" (.float f) = .val (.float f.neg) := by cases d <;> rfl


/-- Membership test. -/
def valIn (x c : Val) : EResult :=
  -- An instance of a class with a builtin base is a container: `0 in A((0,))` is `True`
  -- in CPython for `class A(tuple)`. `unbuiltin` is non-recursive, which keeps this
  -- function non-recursive too.
  match c.unbuiltin with
  | .list vs  => .val (.bool (vs.any (Val.beq x)))
  | .tuple vs => .val (.bool (vs.any (Val.beq x)))
  | .dict kvs => .val (.bool (kvs.any (fun kv => Val.beq x kv.1)))
  | .str s    => match x with
                 | .str t => .val (.bool ((s.splitOn t).length > 1))
                 | _      => .hole "in:non-str-in-str"
  | _         => .hole "in:non-container"

/-- Function table, keyed by name. -/
abbrev FuncTable := List (String × Func)

/-- Everything the interpreter needs: the callable functions and the source dialect. -/
structure Ctx where
  dialect : Dialect
  table   : FuncTable
  /-- Classes whose base is a builtin type — see `Program.builtinBases`. -/
  builtinBases : List (String × BuiltinBase) := []
  /-- Heap address of the module-level bindings frame. Globals must be mutable and must
  outlive any single call, so they live on the heap rather than in `Env`. -/
  globals : Ref := 0

/-- Build a function table from a program. -/
def Program.table (p : Program) : FuncTable := p.funcs.map (fun f => (f.name, f))

/-- Resolve a callable by exact name, else by suffix.

Joern emits fully-qualified names like `pkg/mod.py:<module>.Cls.meth`, while call sites
carry only the short name. Suffix matching is a *heuristic*, and an ambiguous or missing
resolution becomes a hole rather than a guess. -/
def Ctx.resolve (ctx : Ctx) (n : String) : Option Func :=
  match ctx.table.find? (·.1 == n) with
  | some (_, f) => some f
  | none        =>
    -- Scan for a *unique* suffix match, stopping as soon as a second one is seen.
    -- The previous form built the full match list with `filter`, so every miss
    -- allocated across the whole table — on Django's 10,623 functions that made the
    -- ledger run 363s, 55x the cost of a corpus 5x smaller. This is still linear per
    -- lookup (the asymptotic fix is an index on `Ctx`, recorded as an open item), but
    -- it no longer allocates and it exits early on the ambiguous case.
    let suffix := "." ++ n
    let rec go : FuncTable → Option Func → Option Func
      | [],           acc      => acc
      | (k, f) :: ps, none     => if k.endsWith suffix then go ps (some f) else go ps none
      | (k, _) :: ps, some f   => if k.endsWith suffix then none else go ps (some f)
    go ctx.table none

/-! ## The calling convention

`f(*xs, k=v, **d)` and `def f(a, *args, **kwargs)` are one mechanism, split across two
places: `evalList` turns an argument list into a **positional list plus a keyword list**,
and `bindParams` turns those two lists plus a `Func`'s parameter description into an
environment.

Both halves are ordinary total functions — `bindParams` is not even recursive on fuel —
so the interpreter's seven-way mutual recursion is unchanged in shape and
`Autoform/FuelMono.lean` still covers exactly the same functions. -/

/-- View a value as keyword bindings, for `**e`. Only a `dict` whose keys are *all*
strings qualifies: CPython raises `TypeError: keywords must be strings` otherwise, and
`argument after ** must be a mapping` for a non-`dict`, so `none` here means "raise",
never "ignore". -/
def strKeyed : Val → Option (List (String × Val))
  | .dict kvs =>
      kvs.foldr (fun kv acc =>
        match kv.1, acc with
        | .str k, some rest => some ((k, kv.2) :: rest)
        | _,      _         => none) (some [])
  | _ => none

/-- The parameters that receive positional arguments: every parameter except the
variadic ones. -/
def Func.posParams (fn : Func) : List String :=
  fn.params.filter fun p => fn.vararg != some p && fn.kwarg != some p

/-- Bind a call's arguments into the callee's environment.

The rule is CPython's, minus default values (which Core does not model):

* positional arguments fill `posParams` left to right;
* leftovers go to `vararg` as a `tuple` — an empty one when there are none, which is
  why `def f(*a)` called with no arguments binds `a` to `()` rather than to `unit`;
* a keyword argument naming a positional parameter binds that parameter;
* every other keyword argument goes to `kwarg` as a `dict` with `str` keys.

Two deliberate departures, both recorded rather than hidden:

* **Surplus positional arguments are dropped when there is no `*args`.** CPython raises
  `TypeError`. This is the behaviour `applyFunc` already had (`params.zip vs` truncates),
  and it is left alone here so that this change is about starred arguments only.
* **A keyword argument matching no parameter is dropped here** when there is no
  `**kwargs`. `bindParams` is only the binding half; `kwargsRejected` below detects that
  case and `applyFunc` turns it into CPython's `TypeError` before the body ever runs, so
  the drop is never observable. Nothing previously produced keyword arguments, so this
  cannot change any existing behaviour. -/
def bindParams (fn : Func) (base : Env) (vs : List Val)
    (kws : List (String × Val)) : Env :=
  let ps    := fn.posParams
  let ρ₀    := (ps.zip vs).foldl (fun (e : Env) (x, v) => Env.set e x v) base
  let rest  := vs.drop ps.length
  let ρ₁    := match fn.vararg with
               | some a => Env.set ρ₀ a (.tuple rest)
               | none   => ρ₀
  let named := kws.filter (fun kv => ps.contains kv.1)
  let extra := kws.filter (fun kv => !ps.contains kv.1)
  let ρ₂    := named.foldl (fun (e : Env) (x, v) => Env.set e x v) ρ₁
  match fn.kwarg with
  | some k => Env.set ρ₂ k (.dict (extra.map fun kv => (.str kv.1, kv.2)))
  | none   => ρ₂

/-- Does this call pass **more positional arguments than the callee can accept**?

CPython: `def f(a, b)` called as `f(1, 2, 3)` is
`TypeError: f() takes 2 positional arguments but 3 were given` (3.9.6). Core used to
truncate — `params.zip vs` drops the surplus — and the disagreement was recorded as the
theorem `surplusPositional_is_a_known_divergence`, now
`CallingConvention.surplusPositional_now_agrees_with_cpython`. Truncation is the dangerous
direction: a call the real program rejects loudly runs to completion in Core and every
theorem about it is a theorem about a program CPython never executes.

Only a *surplus* is rejected. Too few arguments is still not an error here, because Core
does not model default values: `def k(a=None)` renders as `params := ["a"]`, so raising
on an under-supplied call would reject calls CPython accepts. That asymmetry is
deliberate and is the reason this is not simply an arity equality test.

A `*args` parameter absorbs any surplus, so a callee with `vararg` is never rejected. -/
def posRejected (fn : Func) (vs : List Val) : Bool :=
  fn.vararg.isNone && fn.posParams.length < vs.length

/-- A call passing no more arguments than the callee has positional parameters is never
rejected — in particular the zero-argument call, which is what most callers in a rendered
corpus are. -/
@[simp] theorem posRejected_nil (fn : Func) : posRejected fn [] = false := by
  simp [posRejected]

/-- `posRejected` on the shape a rendered corpus actually presents: a `Func` literal with
both variadic fields at their `none` defaults. The companion of `bindParams_mk`, and
needed for the same reason — a proof about a literal `Func` cannot fire a hypothesis-form
lemma without first deciding which `fn` it is about. -/
@[simp] theorem posRejected_mk (name : String) (params : List String) (body : Stmt)
    (vs : List Val) :
    posRejected ⟨name, params, body, none, none⟩ vs
      = decide (params.length < vs.length) := by
  have : (List.filter (fun p => none != some p) params) = params := by
    simp [List.filter_eq_self]
  simp [posRejected, Func.posParams, this]

/-- Does this call pass a keyword argument the callee cannot accept? CPython raises
`TypeError: f() got an unexpected keyword argument 'k'`; `bindParams` alone would silently
drop it, which is the silently-wrong shape this project keeps catching, so the check is
separate and `applyFunc` turns it into the exception. -/
def kwargsRejected (fn : Func) (kws : List (String × Val)) : Bool :=
  fn.kwarg.isNone && kws.any (fun kv => !fn.posParams.contains kv.1)

/-- A call with no keyword arguments can never be rejected. -/
@[simp] theorem kwargsRejected_nil (fn : Func) : kwargsRejected fn [] = false := by
  simp [kwargsRejected]

/-- A function with no variadic parameters, called with no keyword arguments, binds
exactly what `applyFunc` bound before the calling convention existed. This is the
compatibility equation: every corpus rendered before starred arguments were modelled has
`vararg = none` and `kwarg = none`, so nothing about it changed. -/
theorem bindParams_plain {fn : Func} (base : Env) (vs : List Val)
    (h1 : fn.vararg = none) (h2 : fn.kwarg = none) :
    bindParams fn base vs [] =
      (fn.params.zip vs).foldl (fun (e : Env) (x, v) => Env.set e x v) base := by
  have : (List.filter (fun p => none != some p) fn.params) = fn.params := by
    simp [List.filter_eq_self]
  simp [bindParams, Func.posParams, h1, h2, this]

/-- The same equation in the shape a rendered corpus actually presents: a `Func` literal
with both variadic fields at their `none` defaults. Stated separately because the
hypothesis form of `bindParams_plain` cannot fire on a literal without first deciding
which `fn` it is about. -/
@[simp] theorem bindParams_mk (name : String) (params : List String) (body : Stmt)
    (base : Env) (vs : List Val) :
    bindParams ⟨name, params, body, none, none⟩ base vs [] =
      (params.zip vs).foldl (fun (e : Env) (x, v) => Env.set e x v) base :=
  bindParams_plain base vs rfl rfl

/-- The short class name behind a class VALUE.

The exporter marks a class value by suffixing `<meta>` to the qualified name, and
`resolveMethod`/`classDefines` want the short name -- the last dotted segment. This cannot
split the whole name, because the FILE part contains dots
(`cachetools/__init__.py:<module>.Cache<meta>`). Named rather than inlined so that proofs
about the `mcall` case have a term to talk about. -/
def classNameOfValue (g : String) : String :=
  let base := if g.endsWith "<meta>" then g.dropRight 6 else g
  (base.splitOn ".").getLastD base

/-- Resolve a method on a class: prefer `Cls.meth`, else any `.meth`. -/
def Ctx.resolveMethod (ctx : Ctx) (cls meth : String) : Option Func :=
  match ctx.table.filter (fun p => p.1.endsWith ("." ++ cls ++ "." ++ meth)) with
  | (_, f) :: _ => some f
  | []          => ctx.resolve meth

/-- Does this class define this method *itself*? Unlike `resolveMethod` there is no
free-function fallback, so a global `__eq__` cannot be mistaken for a class's own. -/
def Ctx.classDefines (ctx : Ctx) (cls meth : String) : Bool :=
  ctx.table.any (fun p => p.1.endsWith ("." ++ cls ++ "." ++ meth))

/-- The builtin base of a class, if the exporter recorded one. -/
def Ctx.builtinBase (ctx : Ctx) (cls : String) : Option BuiltinBase :=
  match ctx.builtinBases.find? (·.1 == cls) with
  | some (_, b) => some b
  | none        => none

/-! ### Function objects

A Python function is a heap object with a `__dict__`, which is why `wrapper.cache_clear = f`
is an ordinary attribute write and not a special form. `Val.fn` is a bare name with no
identity, so that write used to hole as `setField:<f>:non-object` -- the largest single block
of INCONCLUSIVE cases in the conformance run. `Val.ref` already carries the identity `is`
compares, so the heap needs nothing new: a function that has been written to becomes an
object of the reserved class below, carrying the function it was. -/

/-- Reserved class of a boxed function object. Not a name any source language can produce. -/
def funcObjCls : String := "<function>"

/-- Reserved field holding the boxed function. -/
def funcObjField : String := "__fn__"

/-- Whether a value is callable-as-a-function, and so may be boxed on attribute write. -/
def isFnVal : Val → Bool
  | .fn _     => true
  | .clos _ _ => true
  | _         => false

/-- Box a function value into a heap object so it can carry attributes. -/
def boxFn (h : Heap) (fv : Val) : Heap × Ref :=
  h.alloc { cls := funcObjCls, fields := [(funcObjField, fv)] }

/-- The function a boxed function object carries, if it is one. -/
def unboxFn (h : Heap) (addr : Ref) : Option Val :=
  match h.get addr with
  | some o => if o.cls == funcObjCls then o.fields.lookup funcObjField else none
  | none   => none

/-- Construct an instance of a class whose base is a builtin type: `X(iterable)` for
`class X(tuple)` / `class X(list)`, `X(d)` for `class X(dict)`, `X(s)` for
`class X(str)`, and `X()` for the empty instance.

Deliberately **refuses** two shapes rather than approximating them:

* a class that defines its own `__init__` — Core would have to run it against a value
  that has no mutable attributes, so whatever it did would be lost;
* a class that defines its own `__eq__` — `Val.beq` compares `bobj`s by contents and
  has no dunder dispatch, so an overridden `__eq__` would be silently ignored. That is
  precisely the silent-wrong outcome this representation is supposed to avoid, so it is
  a hole instead.

Both refusals are *holes*, i.e. counted ignorance, not wrong answers. -/
def allocBuiltin (ctx : Ctx) (cls : String) (b : BuiltinBase) (vs : List Val) : EResult :=
  if ctx.classDefines cls "__init__" then .hole s!"alloc:builtin-base:{cls}:own-__init__"
  else if ctx.classDefines cls "__eq__" then .hole s!"alloc:builtin-base:{cls}:own-__eq__"
  else
    match vs with
    | []  => .val (.bobj cls b.empty)
    | [v] =>
        match b, v.unbuiltin with
        | .tuple, w =>
            match Stdlib.elems w with
            | some es => .val (.bobj cls (.tuple es))
            | none    => .hole s!"alloc:builtin-base:{cls}:non-iterable"
        | .list,  w =>
            match Stdlib.elems w with
            | some es => .val (.bobj cls (.list es))
            | none    => .hole s!"alloc:builtin-base:{cls}:non-iterable"
        -- `dict(pairs)` and `str(x)` on a non-string need `repr`/pair-unpacking that
        -- Core does not model, so only the identity coercions are accepted.
        | .dict,  .dict kvs => .val (.bobj cls (.dict kvs))
        | .dict,  _         => .hole s!"alloc:builtin-base:{cls}:dict-from-non-dict"
        | .str,   .str t    => .val (.bobj cls (.str t))
        | .str,   _         => .hole s!"alloc:builtin-base:{cls}:str-of-non-str"
    | _ => .hole s!"alloc:builtin-base:{cls}:multiple-args"

mutual

/-- Evaluate an expression, threading the heap. -/
def evalExpr (ctx : Ctx) : Nat → Heap → Env → Expr → Heap × EResult
  | 0,   h, _, _ => (h, .outOfFuel)
  | _+1, h, _, .lit (.int i)  => (h, .val (.int i))
  | _+1, h, _, .lit (.str s)  => (h, .val (.str s))
  | _+1, h, _, .lit (.bool b) => (h, .val (.bool b))
  | _+1, h, _, .lit (.float f) => (h, .val (.float f))
  | _+1, h, _, .lit .unit     => (h, .val .unit)
  | _+1, h, ρ, .name x        =>
      match ρ.find? (·.1 == x) with
      | some (_, v) => (h, .val v)
      | none        =>
        -- Item 5: a bare name that is not a local may still be a module-level function.
        -- Resolving it to a function value is what lets higher-order code (decorators,
        -- callbacks) be translated instead of holed.
        match h.get ctx.globals with
        | some g =>
          match g.fields.find? (·.1 == x) with
          | some (_, v) => (h, .val v)
          | none        => match ctx.resolve x with
                           | some _ => (h, .val (.fn x))
                           | none   => (h, .val .unit)
        | none => match ctx.resolve x with
                  | some _ => (h, .val (.fn x))
                  | none   => (h, .val .unit)
  | _+1, h, _, .fnref f       => (h, .val (.fn f))
  | _+1, h, ρ, .closure f     => (h, .val (.clos f ρ))
  | _+1, h, ρ, .classClosure c => (h, .val (.clsClos c ρ))
  | _+1, h, _, .hole l        => (h, .hole l)
  -- The three argument forms are only meaningful inside a call's argument list, where
  -- `evalList` intercepts them before `evalExpr` is ever reached. Anywhere else they have
  -- no value, and saying so is the honest answer.
  | _+1, h, _, .starred _     => (h, .hole "op:starred-outside-call")
  | _+1, h, _, .kwargE _ _    => (h, .hole "op:starred-outside-call")
  | _+1, h, _, .dstarred _    => (h, .hole "op:starred-outside-call")
  | n+1, h, ρ, .unop op a =>
      match evalExpr ctx n h ρ a with
      | (h₁, .val v) => (h₁, applyUnop ctx.dialect op v)
      | (h₁, r)      => (h₁, r)
  | n+1, h, ρ, .binop op a b =>
      match evalExpr ctx n h ρ a with
      | (h₁, .val x) =>
        -- `&&` and `||` must NOT evaluate their right operand when the left already
        -- decides the answer. Eager evaluation was a genuine soundness bug, not a
        -- conservative approximation: `scripts/differential.py` caught
        -- `safemod(-11, 0)` returning 0 in CPython while Core raised ZeroDivisionError,
        -- because `b != 0 and a % b == 0` evaluated the division anyway.
        -- `and`/`or` are VALUE operators in Python and JavaScript: `a and b` is `a`
        -- when `a` is falsy and `b` otherwise, so `pick(0, 5)` is `5`, not `True`.
        -- Returning a bool was wrong for every Python program that uses them in
        -- value position; it survived because cachetools only uses them in
        -- conditions, where truthiness makes the two indistinguishable.
        -- C is the opposite: `&&`/`||` genuinely yield 0/1.
        if op == "&&" && !x.truthy then
          (h₁, .val (if ctx.dialect.boolOpsAreValues then x else .bool false))
        else if op == "||" && x.truthy then
          (h₁, .val (if ctx.dialect.boolOpsAreValues then x else .bool true))
        else
          match evalExpr ctx n h₁ ρ b with
          | (h₂, .val y) =>
            -- `==`/`!=` on a REFERENCE has to go through the heap: two distinct objects
            -- with equal contents are `==` in Python, and no structural compare of two
            -- refs can see that. Everything else keeps the heap-free path, which is the
            -- one `Refine.lean` needs reducible -- diverting here costs one call site
            -- instead of re-typing `applyBinop` and its 155 references.
            if binopNeedsHeap op x y then
              match Val.eqPy h₂ (Val.eqFuel h₂) x y with
              | some r => (h₂, .val (.bool (if op == "==" then r else !r)))
              | none   => (h₂, .outOfFuel)
            else (h₂, applyBinop ctx.dialect op x y)
          | (h₂, r)      => (h₂, r)
      | (h₁, r) => (h₁, r)
  | n+1, h, ρ, .cond c t e =>
      match evalExpr ctx n h ρ c with
      | (h₁, .val v) => if v.truthy then evalExpr ctx n h₁ ρ t else evalExpr ctx n h₁ ρ e
      | (h₁, r)      => (h₁, r)
  | n+1, h, ρ, .isOp neg a b =>
      match evalExpr ctx n h ρ a with
      | (h₁, .val x) =>
        match evalExpr ctx n h₁ ρ b with
        | (h₂, .val y) =>
            -- `is` is reference identity. It used to fall back to a STRUCTURAL compare
            -- for immediates, which is a guess about interning: right for CPython's small
            -- ints, wrong for `[1] is [1]` (two allocations, `False`) and for large ints.
            -- `Val.identical` answers only where Core actually knows, and the rest becomes
            -- a hole rather than a plausible-looking wrong answer.
            match Val.identical x y with
            | some same => (h₂, .val (.bool (if neg then !same else same)))
            | none      => (h₂, .hole "is:unboxed-value-identity")
        | (h₂, r) => (h₂, r)
      | (h₁, r) => (h₁, r)
  | n+1, h, ρ, .inOp neg a b =>
      match evalExpr ctx n h ρ a with
      | (h₁, .val x) =>
        match evalExpr ctx n h₁ ρ b with
        | (h₂, .val c) =>
            match valIn x c with
            | .val (.bool r) => (h₂, .val (.bool (if neg then !r else r)))
            | r              => (h₂, r)
        | (h₂, r) => (h₂, r)
      | (h₁, r) => (h₁, r)
  | n+1, h, ρ, .index a b =>
      match evalExpr ctx n h ρ a with
      | (h₁, .val c) =>
        match evalExpr ctx n h₁ ρ b with
        | (h₂, .val k) =>
          -- `A((0,))[0]` is `0` in CPython for `class A(tuple)`.
          match c.unbuiltin, k with
          | .list vs, .int i =>
              if hh : i.toNat < vs.length then (h₂, .val (vs[i.toNat]))
              else (h₂, .exn (.str "IndexError"))
          | .tuple vs, .int i =>
              if hh : i.toNat < vs.length then (h₂, .val (vs[i.toNat]))
              else (h₂, .exn (.str "IndexError"))
          | .dict kvs, key =>
              match kvs.find? (fun kv => Val.beq kv.1 key) with
              | some (_, v) => (h₂, .val v)
              | none        => (h₂, .exn (.str "KeyError"))
          | _, _ => (h₂, .hole "index:unsupported")
        | (h₂, r) => (h₂, r)
      | (h₁, r) => (h₁, r)
  | n+1, h, ρ, .field a f =>
      match evalExpr ctx n h ρ a with
      | (h₁, .val (.ref r)) =>
        match h₁.get r with
        | some o =>
          match o.fields.find? (·.1 == f) with
          | some (_, v) => (h₁, .val v)
          | none        => match o.captured.find? (·.1 == f) with
                           | some (_, v) => (h₁, .val v)
                           -- A **module object** — the exporter's representation of an
                           -- imported module, marked by a class name beginning `<module>`
                           -- that no `class` statement in any language can spell — carries
                           -- exactly its top-level functions, classes and submodules. Its
                           -- module-level *data* is not a field, because Core's single
                           -- globals frame is not per-module and the value would have to
                           -- be captured before the module body computed it. Answering
                           -- `unit` for such an attribute is the silent wrong answer;
                           -- naming the miss is the honest one. Ordinary objects keep the
                           -- documented `unit` behaviour, so no existing corpus changes.
                           | none        =>
                             if o.cls.startsWith "<module>" then
                               (h₁, .hole s!"module-attr:{f}")
                             else (h₁, .val .unit)
        | none => (h₁, .val .unit)
      -- A C aggregate initializer is a `Val.dict` keyed by field name (see
      -- `Dialect.fieldsOnDicts`), so `alg.cra_priority` is a lookup in it. A *missing*
      -- key is a hole rather than `unit`: in C every field of a struct exists, so a name
      -- the initializer does not mention means the exporter and the semantics disagree
      -- about the shape, and inventing `unit` would hide that.
      | (h₁, .val (.dict kvs)) =>
          if ctx.dialect.fieldsOnDicts then
            match kvs.find? (fun kv => Val.beq kv.1 (.str f)) with
            | some (_, v) => (h₁, .val v)
            | none        => (h₁, .hole s!"field:{f}:absent-from-aggregate")
          else (h₁, .hole s!"field:{f}:non-object")
      | (h₁, .val _)        => (h₁, .hole s!"field:{f}:non-object")
      | (h₁, r)             => (h₁, r)
  -- `[*a, b]` and `(*a, b)` splice, exactly as in a call. `{**d}` has no display form
  -- here (a dict display is `dictE`), so a keyword group in a list/tuple literal is a
  -- shape we do not model and it says so.
  | n+1, h, ρ, .listE es =>
      match evalList ctx n h ρ es with
      | (h₁, .inr (vs, []))  => (h₁, .val (.list vs))
      | (h₁, .inr (_,  _))   => (h₁, .hole "op:keyword-in-literal")
      | (h₁, .inl r)         => (h₁, r)
  | n+1, h, ρ, .tupleE es =>
      match evalList ctx n h ρ es with
      | (h₁, .inr (vs, []))  => (h₁, .val (.tuple vs))
      | (h₁, .inr (_,  _))   => (h₁, .hole "op:keyword-in-literal")
      | (h₁, .inl r)         => (h₁, r)
  | n+1, h, ρ, .dictE kvs =>
      match evalPairs ctx n h ρ kvs with
      | (h₁, .inr ps) => (h₁, .val (.dict ps))
      | (h₁, .inl r)  => (h₁, r)
  | n+1, h, ρ, .call f args =>
      match evalList ctx n h ρ args with
      | (h₁, .inl r)  => (h₁, r)
      | (h₁, .inr (vs, kws)) =>
        match ctx.resolve f with
        | some fn => applyFunc ctx n h₁ fn none vs kws
        | none    =>
          -- Not a statically known function: it may be a function value or closure held
          -- in a variable (`f = g; f(x)`, decorators, callbacks).
          match ρ.get f with
          | .fn g      => match ctx.resolve g with
                          | some fn =>
                            -- An unbound method reached through a VARIABLE -- a decorator's
                            -- wrapped function, a callback, `cache_getitem = Cache.__getitem__`
                            -- -- receives its receiver as the first POSITIONAL argument. That
                            -- is what `self` is in Python; the receiver is only implicit at a
                            -- `.`-call. `applyFunc` binds the receiver separately, so the head
                            -- has to be split off here, or it lands on `self`'s successor and
                            -- the call reports a spurious arity `TypeError`.
                            if fn.isMethod && fn.vararg.isNone
                               && vs.length == fn.params.length + 1 then
                              applyFunc ctx n h₁ fn (some (vs.headD .unit)) vs.tail kws
                            else applyFunc ctx n h₁ fn none vs kws
                          | none    => (h₁, .hole s!"call:{g}")
          | .clos g cap => match ctx.resolve g with
                          | some fn => applyClosure ctx n h₁ fn cap vs kws
                          | none    => (h₁, .hole s!"call:{g}")
          | .ref addr  =>
            -- A function that has had an attribute written to it is now a boxed function
            -- object. Calling it calls what it carries; anything else on the heap is not
            -- callable and says so rather than guessing.
            match unboxFn h₁ addr with
            | some (.fn g)      => match ctx.resolve g with
                                   | some fn => applyFunc ctx n h₁ fn none vs kws
                                   | none    => (h₁, .hole s!"call:{g}")
            | some (.clos g cap) => match ctx.resolve g with
                                    | some fn => applyClosure ctx n h₁ fn cap vs kws
                                    | none    => (h₁, .hole s!"call:{g}")
            | _ => (h₁, .hole s!"call:{f}:not-callable")
          | _          =>
            -- Modelled stdlib is consulted LAST, so a user function of the same name
            -- always wins. `builtin` returns `none` for anything it cannot model
            -- faithfully, which falls through to a visible hole.
            -- `Stdlib.builtin` takes positional arguments only: a keyword argument to a
            -- builtin is *not* passed silently, it is a named hole.
            if kws.isEmpty then
              match Stdlib.builtin ctx.dialect h₁ f vs with
              | some (h₂, r) => (h₂, r)
              | none         => (h₁, .hole s!"call:{f}")
            else (h₁, .hole s!"call:{f}:keyword-to-builtin")
  | n+1, h, ρ, .mcall recv m args =>
      match evalExpr ctx n h ρ recv with
      | (h₁, .val (.ref r)) =>
        match evalList ctx n h₁ ρ args with
        | (h₂, .inl e)  => (h₂, e)
        | (h₂, .inr (vs, kws)) =>
          match h₂.get r with
          | none   => (h₂, .hole "mcall:dangling-ref")
          | some o =>
            match ctx.resolveMethod o.cls m with
            | none    =>
              -- `keys.hashkey(x)` on a **module object**. A module has no methods, so
              -- `resolveMethod` finds nothing; what it has is a *field* holding a
              -- function value, and a module-level function takes no receiver. Calling
              -- it with `self` bound would shift every argument by one, so the receiver
              -- is dropped — which is exactly what CPython does for an attribute that is
              -- a plain function rather than a class attribute.
              --
              -- Restricted to module objects on purpose. The same rule is *also* correct
              -- for an ordinary instance attribute holding a function (`self.cb(x)` does
              -- not pass `self` in CPython), and today that is the hole `mcall:C.cb`. But
              -- that is a claim about every class in every corpus, and it is not what
              -- this change is about; it stays a hole until it is measured on its own.
              if o.cls.startsWith "<module>" then
                match o.fields.find? (·.1 == m) with
                | some (_, .fn g)      =>
                    match ctx.resolve g with
                    | some fn => applyFunc ctx n h₂ fn none vs kws
                    | none    => (h₂, .hole s!"call:{g}")
                | some (_, .clos g cap) =>
                    match ctx.resolve g with
                    | some fn => applyClosure ctx n h₂ fn cap vs kws
                    | none    => (h₂, .hole s!"call:{g}")
                | some _  => (h₂, .hole s!"module-call:{m}:not-a-function")
                | none    => (h₂, .hole s!"module-attr:{m}")
              else (h₂, .hole s!"mcall:{o.cls}.{m}")
            | some fn =>
              if o.captured.isEmpty then applyFunc ctx n h₂ fn (some (.ref r)) vs kws
              else applyClosure ctx n h₂ fn (("self", .ref r) :: o.captured) vs kws
      | (h₁, .val (.fn g)) =>
        match evalList ctx n h₁ ρ args with
        | (h₂, .inl e)  => (h₂, e)
        | (h₂, .inr (vs, kws)) =>
          -- `Cache.__init__(self, maxsize, getsizeof)`: an UNBOUND method reached through
          -- the CLASS, which is how every subclass in cachetools calls its base
          -- constructor. Python passes the receiver as an ordinary first positional here;
          -- `applyFunc` binds receivers separately, so it has to be split off. Same rule
          -- as the `.fn` case in `Expr.call`, and it was worth six functions -- every
          -- `__init__` in the corpus was `mcall:__init__:non-object`.
          --
          -- The class value's name is the exporter's `<meta>` marker on the qualified
          -- name; `resolveMethod` wants the short class name, which is its last dotted
          -- segment (the FILE part contains dots, so this cannot split on the whole name).
          let short := classNameOfValue g
          -- `classDefines`, NOT `resolveMethod`: the latter falls back to any free
          -- function of that name, which for an opaque external module (`time.monotonic`)
          -- would invent a method out of an unrelated global. A hole is the right answer
          -- there; a plausible wrong one is not.
          if ctx.classDefines short m then
            match ctx.resolveMethod short m with
            | some fn =>
                match vs with
                | recv :: rest => applyFunc ctx n h₂ fn (some recv) rest kws
                | []           => (h₂, .hole s!"mcall:{short}.{m}:no-receiver")
            | none => (h₂, .hole s!"mcall:{m}:non-object")
          else (h₂, .hole s!"mcall:{short}.{m}:not-a-class-method")
      | (h₁, .val (.bobj bcls pay)) =>
        match evalList ctx n h₁ ρ args with
        | (h₂, .inl e)  => (h₂, e)
        | (h₂, .inr (vs, kws)) =>
          -- Method dispatch on a builtin-based instance: the class's own methods first
          -- (`self` is bound to the whole instance, so `self` still compares as the
          -- builtin), then the builtin's own methods on the payload.
          if ctx.classDefines bcls m then
            match ctx.resolveMethod bcls m with
            | some fn => applyFunc ctx n h₂ fn (some (.bobj bcls pay)) vs kws
            | none    => (h₂, .hole s!"mcall:{bcls}.{m}")
          else if kws.isEmpty then
            match Stdlib.method ctx.dialect h₂ pay m vs with
            | some (h₃, .pure r)       => (h₃, r)
            | some (h₃, .mutating _ _) => (h₃, .hole s!"mcall:{m}:unboxed-container")
            | none                     => (h₂, .hole s!"mcall:{bcls}.{m}")
          -- `Stdlib.method` has no keyword-argument calling convention, so a keyword
          -- call on a builtin payload is refused rather than silently dropped — the
          -- silent-drop of nine keyword arguments is what the varargs work just fixed.
          else (h₂, .hole s!"mcall:{m}:keyword-to-builtin")
      | (h₁, .val recv) =>
        match evalList ctx n h₁ ρ args with
        | (h₂, .inl e)  => (h₂, e)
        | (h₂, .inr (_, _ :: _)) => (h₂, .hole s!"mcall:{m}:keyword-to-builtin")
        | (h₂, .inr (vs, [])) =>
          match Stdlib.method ctx.dialect h₂ recv m vs with
          | some (h₃, .pure r)       => (h₃, r)
          -- A mutating container method cannot be honoured while containers are values:
          -- writing back through the receiver *expression* updates a temporary, because
          -- the CPG has already desugared `self.d.pop(k)` into `t = self.d; t.pop(k)`.
          -- An honest hole until containers are boxed (see docs/boxed-containers.md).
          | some (h₃, .mutating _ _) => (h₃, .hole s!"mcall:{m}:unboxed-container")
          | none                     => (h₂, .hole s!"mcall:{m}:non-object")
      | (h₁, r)      => (h₁, r)
  -- `003-box-address-taken-locals`: unconditional, constructor-free allocation of a
  -- fresh single-field box. Evaluate the argument, allocate `{cls := "<local>",
  -- fields := [("v", value)]}`, and yield the resulting `Val.ref` -- no class lookup,
  -- no `__init__`, unlike `.alloc` just below.
  | n+1, h, ρ, .boxNew e =>
      match evalExpr ctx n h ρ e with
      | (h₁, .val v) =>
        let (h₂, r) := h₁.alloc { cls := "<local>", fields := [("v", v)] }
        (h₂, .val (.ref r))
      | (h₁, r) => (h₁, r)
  -- `006-reduce-remaining-holes`, Story 5: `Expr.boxNew` generalised to N fields --
  -- evaluate every (key, value) pair left-to-right, allocate one fresh `Obj` from the
  -- whole list, and yield `Val.ref`. The producer is the unconditional per-function
  -- allocation prologue for every array/struct local the exporter's own scope
  -- boundary admits (research.md §5.3-§5.4); this is what closes the pre-existing
  -- §5.1 gap (a plain struct local that looked hole-free but silently depended on a
  -- `setField` special case that did not cover it) for every struct this admits.
  --
  -- Reuses `evalPairs` verbatim (each key an `Expr`, always a string literal at
  -- every site the exporter emits) rather than a parallel `String`-keyed evaluator:
  -- `evalPairs` is already proven fuel-monotone as part of `dictE`'s own machinery
  -- (`Autoform/FuelMono.lean`), so `boxFields` needs no separate proof obligation of
  -- its own -- only the fuel-free key-extraction step below is new.
  | n+1, h, ρ, .boxFields kvs =>
      match evalPairs ctx n h ρ kvs with
      | (h₁, .inr pairs) =>
        match pairs.foldr (fun kv acc => match kv.1, acc with
                | .str k, some rest => some ((k, kv.2) :: rest)
                | _,      _         => none) (some []) with
        | some fields =>
          let (h₂, r) := h₁.alloc { cls := "<local>", fields := fields }
          (h₂, .val (.ref r))
        | none => (h₁, .hole "boxFields:non-string-key")
      | (h₁, .inl res) => (h₁, res)
  -- `006-reduce-remaining-holes`, Story 5: `&a[i]` once `a` is a boxed array --
  -- evaluate the receiver to `Val.ref r`, evaluate the index, produce
  -- `Val.iref r (.idx i)`. Anything else is a shape the exporter's own scope
  -- boundary should never have emitted this node for; named as a hole rather than
  -- risking a wrong answer, per this project's own discipline.
  | n+1, h, ρ, .irefIndex a i =>
      match evalExpr ctx n h ρ a with
      | (h₁, .val (.ref r)) =>
        match evalExpr ctx n h₁ ρ i with
        | (h₂, .val (.int k)) => (h₂, .val (.iref r (.idx k)))
        | (h₂, .val _)        => (h₂, .hole "irefIndex:non-int-index")
        | (h₂, res)           => (h₂, res)
      | (h₁, .val _) => (h₁, .hole "irefIndex:non-object")
      | (h₁, res)    => (h₁, res)
  -- `006-reduce-remaining-holes`, Story 5: `&s.f` once `s` is a boxed struct --
  -- evaluate the receiver to `Val.ref r`, produce `Val.iref r (.fld f)`.
  | n+1, h, ρ, .irefField a f =>
      match evalExpr ctx n h ρ a with
      | (h₁, .val (.ref r)) => (h₁, .val (.iref r (.fld f)))
      | (h₁, .val _)        => (h₁, .hole "irefField:non-object")
      | (h₁, res)           => (h₁, res)
  -- `006-reduce-remaining-holes`, Story 5: `*p`, `p` an interior-pointer VALUE --
  -- requires the operand to evaluate to `Val.iref r sel` and delegates,
  -- unconditionally, to the unchanged `Heap.getField` -- no `Heap`-level change.
  | n+1, h, ρ, .derefIref a =>
      match evalExpr ctx n h ρ a with
      | (h₁, .val (.iref r sel)) => (h₁, .val (h₁.getField r sel.key))
      | (h₁, .val _)             => (h₁, .hole "derefIref:non-iref")
      | (h₁, res)                => (h₁, res)
  | n+1, h, ρ, .alloc cls args =>
      match evalList ctx n h ρ args with
      | (h₁, .inl r)  => (h₁, r)
      | (h₁, .inr (vs, kws)) =>
        match ctx.builtinBase cls with
        -- `class X(tuple)` and friends: the instance IS the builtin, not an opaque
        -- reference. See `Val.bobj`.
        | some b => (h₁, allocBuiltin ctx cls b vs)
        | none =>
        -- A class defined inside a function is a *value*; instances carry the bindings it
        -- captured, so its methods can read the enclosing scope.
        let cap := match ρ.get cls with
                   | .clsClos _ c => c
                   | _            => []
        let (h₂, r) := h₁.alloc { cls := cls, fields := [], captured := cap }
        match ctx.resolveMethod cls "__init__" with
        | none    => (h₂, .val (.ref r))
        | some fn =>
          match applyFunc ctx n h₂ fn (some (.ref r)) vs kws with
          | (h₃, .val _)  => (h₃, .val (.ref r))
          | (h₃, .hole l) => (h₃, .hole l)
          | (h₃, e)       => (h₃, e)

/-- Apply a resolved function, optionally with a receiver bound to `self`.

`kws` carries the keyword arguments — `[]` for every call that has none, which is every
call this interpreter could express before starred arguments existed. -/
def applyFunc (ctx : Ctx) : Nat → Heap → Func → Option Val → List Val →
    List (String × Val) → Heap × EResult
  | 0,   h, _,  _,     _,  _   => (h, .outOfFuel)
  | n+1, h, fn, self?, vs, kws =>
      let base : Env := match self? with
                        | some s => [("self", s)]
                        | none   => []
      let ρ := bindParams fn base vs kws
      if kwargsRejected fn kws || posRejected fn vs then (h, .exn (.str "TypeError")) else
      match execStmt ctx n h ρ fn.body with
      | (h₁, .ret v)    => (h₁, .val v)
      | (h₁, .normal _) => (h₁, .val .unit)
      | (h₁, .exn v)    => (h₁, .exn v)
      | (h₁, .hole l)   => (h₁, .hole l)
      | (h₁, .outOfFuel)=> (h₁, .outOfFuel)
      | (h₁, _)         => (h₁, .hole "call:stray-control-flow")

/-- Apply a closure: the captured bindings form the base environment, then parameters
shadow them.

Capture is by value. Reads of enclosing variables therefore work, which covers decorators
and factory functions; a `nonlocal` **write** would need the binding to be a shared
mutable cell, so the transpiler keeps it as an explicit hole rather than pretending. -/
def applyClosure (ctx : Ctx) : Nat → Heap → Func → List (String × Val) → List Val →
    List (String × Val) → Heap × EResult
  | 0,   h, _,  _,   _,  _   => (h, .outOfFuel)
  | n+1, h, fn, cap, vs, kws =>
      let base : Env := cap
      let ρ : Env := bindParams fn base vs kws
      if kwargsRejected fn kws || posRejected fn vs then (h, .exn (.str "TypeError")) else
      match execStmt ctx n h ρ fn.body with
      | (h₁, .ret v)     => (h₁, .val v)
      | (h₁, .normal _)  => (h₁, .val .unit)
      | (h₁, .exn v)     => (h₁, .exn v)
      | (h₁, .hole l)    => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
      | (h₁, _)          => (h₁, .hole "call:stray-control-flow")

/-- Evaluate an argument list left to right, short-circuiting on the first non-value, and
return the **positional** values together with the **keyword** bindings.

This is the one place the three argument forms of `Expr` mean anything:

* `*e` splices `e`'s elements into the positional list. A non-iterable `e` raises
  `TypeError`, as in CPython (`f(*1)`).
* `k = e` appends one keyword binding.
* `**e` splices a `dict` into the keyword bindings. A non-`dict`, or a `dict` with a
  non-string key, raises `TypeError`, as in CPython.

Every other expression contributes exactly one positional value, so the `kws` component is
`[]` for every argument list that predates this change and the whole of the previous
behaviour is recovered by projecting on the first component. -/
def evalList (ctx : Ctx) : Nat → Heap → Env → List Expr →
    Heap × Sum EResult (List Val × List (String × Val))
  | 0,   h, _, _       => (h, .inl .outOfFuel)
  | _+1, h, _, []      => (h, .inr ([], []))
  | n+1, h, ρ, .starred e :: as =>
      match evalExpr ctx n h ρ e with
      | (h₁, .val v) =>
        match v.iterable with
        | none    => (h₁, .inl (.exn (.str "TypeError")))
        | some xs =>
          match evalList ctx n h₁ ρ as with
          | (h₂, .inr (vs, kws)) => (h₂, .inr (xs ++ vs, kws))
          | (h₂, .inl r)         => (h₂, .inl r)
      | (h₁, r) => (h₁, .inl r)
  | n+1, h, ρ, .kwargE k e :: as =>
      match evalExpr ctx n h ρ e with
      | (h₁, .val v) =>
        match evalList ctx n h₁ ρ as with
        | (h₂, .inr (vs, kws)) => (h₂, .inr (vs, (k, v) :: kws))
        | (h₂, .inl r)         => (h₂, .inl r)
      | (h₁, r) => (h₁, .inl r)
  | n+1, h, ρ, .dstarred e :: as =>
      match evalExpr ctx n h ρ e with
      | (h₁, .val v) =>
        match strKeyed v with
        | none    => (h₁, .inl (.exn (.str "TypeError")))
        | some ks =>
          match evalList ctx n h₁ ρ as with
          | (h₂, .inr (vs, kws)) => (h₂, .inr (vs, ks ++ kws))
          | (h₂, .inl r)         => (h₂, .inl r)
      | (h₁, r) => (h₁, .inl r)
  | n+1, h, ρ, a :: as =>
      match evalExpr ctx n h ρ a with
      | (h₁, .val v) =>
        match evalList ctx n h₁ ρ as with
        | (h₂, .inr (vs, kws)) => (h₂, .inr (v :: vs, kws))
        | (h₂, .inl r)         => (h₂, .inl r)
      | (h₁, r) => (h₁, .inl r)

/-- Evaluate a list of key/value expression pairs. -/
def evalPairs (ctx : Ctx) : Nat → Heap → Env → List (Expr × Expr) →
    Heap × Sum EResult (List (Val × Val))
  | 0,   h, _, _            => (h, .inl .outOfFuel)
  | _+1, h, _, []           => (h, .inr [])
  | n+1, h, ρ, (k, v) :: ps =>
      match evalExpr ctx n h ρ k with
      | (h₁, .val kv) =>
        match evalExpr ctx n h₁ ρ v with
        | (h₂, .val vv) =>
          match evalPairs ctx n h₂ ρ ps with
          | (h₃, .inr rest) => (h₃, .inr ((kv, vv) :: rest))
          | (h₃, .inl r)    => (h₃, .inl r)
        | (h₂, r) => (h₂, .inl r)
      | (h₁, r) => (h₁, .inl r)

/-- Execute a statement, threading the heap. -/
def execStmt (ctx : Ctx) : Nat → Heap → Env → Stmt → Heap × Ctl
  | 0,   h, _, _ => (h, .outOfFuel)
  | _+1, h, ρ, .skip   => (h, .normal ρ)
  | _+1, h, ρ, .brk    => (h, .brk ρ)
  | _+1, h, ρ, .cont   => (h, .cont ρ)
  | _+1, h, _, .hole l => (h, .hole l)
  | _+1, h, ρ, .del x  => (h, .normal (ρ.del x))
  -- `global x` records a marker; `assign` consults it so that `global x; x = 1` writes
  -- module scope rather than silently creating a local and losing the update.
  | _+1, h, ρ, .declGlobal x => (h, .normal (ρ.set ("<glob>" ++ x) (.bool true)))
  | n+1, h, ρ, .expr e =>
      match evalExpr ctx n h ρ e with
      | (h₁, .val _)     => (h₁, .normal ρ)
      | (h₁, .exn v)     => (h₁, .exn v)
      | (h₁, .hole l)    => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
  | n+1, h, ρ, .setGlobal x e =>
      match evalExpr ctx n h ρ e with
      | (h₁, .val v)     => (h₁.setField ctx.globals x v, .normal ρ)
      | (h₁, .exn v)     => (h₁, .exn v)
      | (h₁, .hole l)    => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
  | n+1, h, ρ, .assign x e =>
      match evalExpr ctx n h ρ e with
      | (h₁, .val v)     =>
          if (ρ.get ("<glob>" ++ x)).truthy then (h₁.setField ctx.globals x v, .normal ρ)
          else (h₁, .normal (ρ.set x v))
      | (h₁, .exn v)     => (h₁, .exn v)
      | (h₁, .hole l)    => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
  | n+1, h, ρ, .ret e =>
      match evalExpr ctx n h ρ e with
      | (h₁, .val v)     => (h₁, .ret v)
      | (h₁, .exn v)     => (h₁, .exn v)
      | (h₁, .hole l)    => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
  | n+1, h, ρ, .raise e =>
      match evalExpr ctx n h ρ e with
      | (h₁, .val v)     => (h₁, .exn v)
      | (h₁, .exn v)     => (h₁, .exn v)
      | (h₁, .hole l)    => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
  | n+1, h, ρ, .setField r f v =>
      match evalExpr ctx n h ρ r with
      | (h₁, .val (.ref addr)) =>
        match evalExpr ctx n h₁ ρ v with
        | (h₂, .val vv)    => (h₂.setField addr f vv, .normal ρ)
        | (h₂, .exn e)     => (h₂, .exn e)
        | (h₂, .hole l)    => (h₂, .hole l)
        | (h₂, .outOfFuel) => (h₂, .outOfFuel)
      | (h₁, .val fv) =>
        -- A function is a heap object in Python, so an attribute write to one is legal.
        -- It is only expressible here when the receiver is a NAME: boxing rebinds that
        -- name to the new object, and a function value reached any other way has nowhere
        -- to rebind, so it keeps holing. That is correct rather than convenient -- the
        -- alternative silently drops the mutation.
        match r with
        | .name x =>
          if isFnVal fv then
            let (h₂, addr) := boxFn h₁ fv
            match evalExpr ctx n h₂ ρ v with
            | (h₃, .val vv)    => (h₃.setField addr f vv, .normal (Env.set ρ x (.ref addr)))
            | (h₃, .exn e)     => (h₃, .exn e)
            | (h₃, .hole l)    => (h₃, .hole l)
            | (h₃, .outOfFuel) => (h₃, .outOfFuel)
          else (h₁, .hole s!"setField:{f}:non-object")
        | _ => (h₁, .hole s!"setField:{f}:non-object")
      | (h₁, .exn e) => (h₁, .exn e)
      | (h₁, .hole l) => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
  | n+1, h, ρ, .setIndex _ _ _ =>
      -- Container mutation needs boxed containers, which Core does not have yet.
      (h, .hole "setIndex:immutable-containers")
  -- `006-reduce-remaining-holes`, Story 5: `*p = v`, `p` an interior-pointer VALUE --
  -- requires the pointer operand to evaluate to `Val.iref r sel` and delegates,
  -- unconditionally, to the unchanged `Heap.setField`.
  | n+1, h, ρ, .setDerefIref p v =>
      match evalExpr ctx n h ρ p with
      | (h₁, .val (.iref r sel)) =>
        match evalExpr ctx n h₁ ρ v with
        | (h₂, .val vv)    => (h₂.setField r sel.key vv, .normal ρ)
        | (h₂, .exn e)     => (h₂, .exn e)
        | (h₂, .hole l)    => (h₂, .hole l)
        | (h₂, .outOfFuel) => (h₂, .outOfFuel)
      | (h₁, .val _)      => (h₁, .hole "setDerefIref:non-iref")
      | (h₁, .exn e)      => (h₁, .exn e)
      | (h₁, .hole l)     => (h₁, .hole l)
      | (h₁, .outOfFuel)  => (h₁, .outOfFuel)
  | n+1, h, ρ, .seq a b =>
      match execStmt ctx n h ρ a with
      | (h₁, .normal ρ') => execStmt ctx n h₁ ρ' b
      | (h₁, r)          => (h₁, r)
  | n+1, h, ρ, .ifte c t e =>
      match evalExpr ctx n h ρ c with
      | (h₁, .val v)     => if v.truthy then execStmt ctx n h₁ ρ t
                            else execStmt ctx n h₁ ρ e
      | (h₁, .exn v)     => (h₁, .exn v)
      | (h₁, .hole l)    => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
  | n+1, h, ρ, .tryFinally body fin =>
      match execStmt ctx n h ρ body with
      | (h₁, .normal ρ') => execStmt ctx n h₁ ρ' fin
      | (h₁, r) =>
          -- The finalizer runs on every path. If it exits abnormally it *discards* the
          -- body's pending outcome: `try: return 1 finally: return 2` returns 2.
          let ρ' := match r with
                    | .normal e | .brk e | .cont e => e
                    | _                            => ρ
          match execStmt ctx n h₁ ρ' fin with
          | (h₂, .normal _) => (h₂, r)
          | (h₂, r')        => (h₂, r')
  | n+1, h, ρ, .tryCatch body x handler =>
      match execStmt ctx n h ρ body with
      | (h₁, .exn v) => execStmt ctx n h₁ (ρ.set x v) handler
      | (h₁, r)      => (h₁, r)
  | n+1, h, ρ, .loop c body =>
      match evalExpr ctx n h ρ c with
      | (h₁, .val v) =>
          if v.truthy then
            match execStmt ctx n h₁ ρ body with
            | (h₂, .normal ρ') => execStmt ctx n h₂ ρ' (.loop c body)
            | (h₂, .cont ρ')   => execStmt ctx n h₂ ρ' (.loop c body)
            | (h₂, .brk ρ')    => (h₂, .normal ρ')
            | (h₂, r)          => (h₂, r)
          else (h₁, .normal ρ)
      | (h₁, .exn v)     => (h₁, .exn v)
      | (h₁, .hole l)    => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)
  -- `007-reduce-remaining-holes-2` US4: catches a `.brk` from its inner statement and
  -- converts it to `.normal`, exactly once (no re-execution, unlike `.loop`) --
  -- deliberately does NOT catch `.cont`, so a `continue` written directly in a
  -- `switch` case body keeps propagating to whatever REAL loop encloses the switch,
  -- unchanged. This is the one thing `.loop`/`.forIn` do not provide on their own.
  | n+1, h, ρ, .breakBlock body =>
      match execStmt ctx n h ρ body with
      | (h₁, .brk ρ') => (h₁, .normal ρ')
      | (h₁, r)       => (h₁, r)
  | n+1, h, ρ, .forIn x e body =>
      match evalExpr ctx n h ρ e with
      | (h₁, .val v) =>
        match v.iterable with
        | some vs => execFor ctx n h₁ ρ x vs body
        | none    => (h₁, .hole "forIn:non-iterable")
      | (h₁, .exn v)     => (h₁, .exn v)
      | (h₁, .hole l)    => (h₁, .hole l)
      | (h₁, .outOfFuel) => (h₁, .outOfFuel)

/-- Run a loop body once per element of an already-computed sequence. -/
def execFor (ctx : Ctx) : Nat → Heap → Env → String → List Val → Stmt → Heap × Ctl
  | 0,   h, ρ, _, _,       _    => (h, .outOfFuel)
  | _+1, h, ρ, _, [],      _    => (h, .normal ρ)
  | n+1, h, ρ, x, v :: vs, body =>
      match execStmt ctx n h (ρ.set x v) body with
      | (h₁, .normal ρ') => execFor ctx n h₁ ρ' x vs body
      | (h₁, .cont ρ')   => execFor ctx n h₁ ρ' x vs body
      | (h₁, .brk ρ')    => (h₁, .normal ρ')
      | (h₁, r)          => (h₁, r)

end

/-- A one-element argument list, when that argument is an ordinary one. Stated because a
*symbolic* expression cannot be dispatched on: `evalList` looks at the argument's syntax
before evaluating it, so knowing what `evalExpr` does to `e` is not by itself enough to
know what `evalList` does to `[e]`. -/
theorem evalList_singleton (ctx : Ctx) (n : Nat) (h : Heap) (ρ : Env) {e : Expr}
    (hp : e.plainArg = true) :
    evalList ctx (n+2) h ρ [e] =
      (match evalExpr ctx (n+1) h ρ e with
       | (h₁, .val v) => (h₁, .inr ([v], []))
       | (h₁, r)      => (h₁, .inl r)) := by
  cases e
  case starred _ => exact absurd hp (by simp [Expr.plainArg])
  case kwargE _ _ => exact absurd hp (by simp [Expr.plainArg])
  case dstarred _ => exact absurd hp (by simp [Expr.plainArg])
  all_goals rfl

/-- Run a named entry point against argument values, with **no** module-level state.

Deliberately unchanged: it starts from the empty heap, so `Heap.get ctx.globals` finds
nothing and a free name falls through to the function table. This is the right entry point
for a self-contained function, and keeping it stable keeps the refinement layer's
theorems meaningful. Use `runMain` when module-level bindings matter. -/
def runFunc (p : Program) (fuel : Nat) (name : String) (args : List Val) : EResult :=
  let ctx : Ctx := { dialect := p.dialect, table := p.table,
                     builtinBases := p.builtinBases }
  match ctx.resolve name with
  | none    => .hole s!"entry:{name}"
  | some fn => (applyFunc ctx fuel [] fn none args []).2

/-- Run the module initializers and return the resulting heap plus the globals address.

Exposed separately from `runMain` so that a harness which builds its own heap (e.g. the
differential oracle, which materialises receiver objects) can start from an initialised
globals frame instead of the empty heap. Fresh objects must be allocated at indices from
`heap.length` onward. -/
def initGlobals (p : Program) (fuel : Nat) (inits : List Func) : Heap × Ref :=
  let (h₀, g) := Heap.alloc ([] : Heap) { cls := "<globals>", fields := [] }
  let ctx : Ctx := { dialect := p.dialect, table := p.table, globals := g,
                     builtinBases := p.builtinBases }
  let rec go : Nat → Heap → List Func → Heap
    | 0,   h, _       => h
    | _+1, h, []      => h
    | n+1, h, f :: fs => go n (applyFunc ctx fuel h f none [] []).1 fs
  (go (inits.length + 1) h₀ inits, g)

/-- Run module initializers into a shared globals frame, then call an entry point.

Module-level bindings are mutable and outlive any single call, so they live in a heap
object rather than in `Env`. The transpiler emits one zero-argument `Func` per source
module (`moduleInits`); running them in order is what makes module constants, classes and
functions resolvable.

Initializer order is the caller's responsibility: the transpiler cannot recover a
cross-file dependency order from the CPG, so a module that reads another module's globals
must be listed after it. That is a real limitation, not a detail — it is recorded as an
open item rather than papered over with a guessed ordering. -/
def runMain (p : Program) (fuel : Nat) (inits : List Func) (name : String)
    (args : List Val) : EResult :=
  let (h₀, g) := Heap.alloc ([] : Heap) { cls := "<globals>", fields := [] }
  let ctx : Ctx := { dialect := p.dialect, table := p.table, globals := g,
                     builtinBases := p.builtinBases }
  let rec runInits : Nat → Heap → List Func → Heap × Option String
    | 0,   h, _       => (h, some "initializers:outOfFuel")
    | _+1, h, []      => (h, none)
    | n+1, h, f :: fs =>
        match applyFunc ctx fuel h f none [] [] with
        | (h₁, .val _)     => runInits n h₁ fs
        | (h₁, .hole l)    => (h₁, some l)
        | (h₁, .exn _)     => runInits n h₁ fs   -- an initializer that raises still bound
                                                  -- whatever it bound before raising
        | (h₁, .outOfFuel) => (h₁, some "initializers:outOfFuel")
  match runInits (inits.length + 1) h₀ inits with
  | (_,  some l) => .hole l
  | (h₁, none)   =>
    match ctx.resolve name with
    | none    => .hole s!"entry:{name}"
    | some fn => (applyFunc ctx fuel h₁ fn none args []).2

/-! ## C and C++ pointers, end to end

The exporter now maps `p->f` to `Expr.field`, `p[i]` to `Expr.index`, C++ stack
construction to `Expr.alloc`, and `&x` on an aggregate to `x` itself. Each of those is a
*mapping* decision, and a mapping decision is exactly the kind that can be wrong while
every downstream theorem still passes: an `Expr.field` that resolved to nothing would
return `unit`, a program full of them would type-check, and the ledger would count it as
translated. So the mappings are checked here by running them.

`boxProg` is what the exporter emits for

    struct Box { int v; Box(int x) { this->v = x; } };
    static int bump(Box *p) { p->v = p->v + 1; return p->v; }
    int run() { Box b(41); return bump(&b); }

with every one of the new decisions visible in the term: the constructor is named
`__init__` (so `Expr.alloc` runs it), its body writes through `self` (not `this`),
`bump` reads and writes `p->v` as `Expr.field` / `Stmt.setField`, and `&b` is just `b`. -/
private def boxProg : Program :=
  { dialect := .cLike
  , funcs :=
    [ { name   := "ns.Box.__init__"
      , params := ["x"]
      , body   := .setField (.name "self") "v" (.name "x") }
    , { name   := "ns.bump"
      , params := ["p"]
      , body   := .seq (.setField (.name "p") "v"
                          (.binop "+" (.field (.name "p") "v") (.lit (.int 1))))
                       (.ret (.field (.name "p") "v")) }
    , { name   := "ns.run"
      , params := []
      , body   := .seq (.assign "b" (.alloc "Box" [.lit (.int 41)]))
                       (.ret (.call "ns.bump" [.name "b"])) }
      -- `static_cast<uint8_t>(300 + 44)` — a real narrowing, in a real program.
    , { name   := "ns.narrow"
      , params := []
      , body   := .ret (.unop "cast:u8" (.binop "+" (.lit (.int 300)) (.lit (.int 44)))) }
      -- `int a[3] = {7,8,9}; return a[1];` as Core spells an indexable value.
    , { name   := "ns.pick"
      , params := []
      , body   := .ret (.index (.listE [.lit (.int 7), .lit (.int 8), .lit (.int 9)])
                               (.lit (.int 1))) }
      -- The negative control: an object whose field was never written.
    , { name   := "ns.unset"
      , params := []
      , body   := .ret (.field (.alloc "Empty" []) "v") } ] }

/-! The whole chain works: `Box b(41)` allocates and runs the constructor, `&b` is `b`,
`p->v = p->v + 1` mutates *that* object, and the caller sees `42`.

`42` is the load-bearing number. `41` would mean the constructor ran but the write
through the pointer did not reach the same object; `unit` would mean the field read
missed; a hole would mean one of the four mappings is unreachable. Only a correct
pointer round-trip produces `42`.

These are pinned with `#guard_msgs`, not `rfl`: `runFunc` on a heap-allocating program
does not reduce by `whnf` (the `.alloc` case threads a heap through `applyFunc`), so
`rfl` cannot see the answer even though the evaluator computes it immediately.
`#guard_msgs` checks the evaluated result at build time and fails the build if it
changes, which is the property wanted here — and unlike `native_decide` it introduces no
axiom. -/
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 42) -/
#guard_msgs in #eval runFunc boxProg 200 "ns.run" []

/-- The cast narrows: `static_cast<uint8_t>(344)` is `88`, matching `cc`. This one does
reduce, so it is stated as a theorem as well. -/
example : runFunc boxProg 200 "ns.narrow" [] = .val (.int 88) := by rfl

/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 88) -/
#guard_msgs in #eval runFunc boxProg 200 "ns.narrow" []

/-- Subscripting reads the element, not the container. -/
example : runFunc boxProg 200 "ns.pick" [] = .val (.int 8) := by rfl

/-! **The known hazard, stated rather than hidden.** `Expr.field` on an object that has
no such field returns `unit`, not a hole — see the `.field` case above. So a C++ class
whose constructor the exporter could not find translates to an object every one of whose
fields reads `unit`, and nothing downstream will say so.

That is why `emit` renames C++ constructors to `__init__` instead of leaving `Expr.alloc`
to allocate an empty object, and why `alloc:builtin-base:*` refuses construction it cannot
model. This check exists so the behaviour is a recorded fact with a test attached, and so
that changing it is a deliberate act rather than an accident. -/
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.unit) -/
#guard_msgs in #eval runFunc boxProg 200 "ns.unset" []


/-! ## Bitwise operators, `for`, and `goto`, checked against `cc`

Every number below was produced by compiling the same fragment with `cc -O0 -fwrapv` on
x86-64 and running it. They are pinned with `#guard_msgs`, which fails the build if the
semantics changes and — unlike `native_decide` — introduces no axiom.

These exist because "the label disappeared from the ledger" is not evidence. An `xor`
that returned `0`, an array initializer that evaluated to `unit`, or a `for` that ran zero
times would each remove a hole and prove nothing; only a checked *value* does. Where a
translation could plausibly have been done a wrong-but-plausible way, the wrong way is
included as a negative control and shown to disagree.
-/

section CEvidence

/-- The C constructs the exporter now translates, spelled in Core exactly as it spells
them.

`ns.forSum` is the interesting one. It is the translation of

    int i, s = 0;
    for (i = 0; i < 10; i++) { if (i % 3 == 0) continue; s += i; }
    return s * 100 + i;

under the rule that a `for`'s `continue` must run the **step**: each `continue` in the
body is emitted as `step; continue`. `cc` prints `s=27 i=10`, so the answer is `2710`.

`ns.forNaive` is the same loop under the *textbook* desugaring — `init; while (c) { body;
step }` with the `continue` left alone. It is the negative control, and it does not
terminate: the `continue` jumps back to the test without incrementing `i`. -/
private def cBits : Program :=
  { dialect := .cLike
  , funcs :=
    [ { name := "ns.xor",   params := [],
        body := .ret (.binop "^" (.lit (.int 0x5A)) (.lit (.int 0x3C))) }
    , { name := "ns.and",   params := [],
        body := .ret (.binop "&" (.lit (.int (-1))) (.lit (.int 255))) }
    , { name := "ns.or",    params := [],
        body := .ret (.binop "|" (.lit (.int 0xF0)) (.lit (.int 0x0F))) }
    , { name := "ns.bnot",  params := [],
        body := .ret (.unop "~" (.lit (.int 0x5A))) }
    , { name := "ns.shl",   params := [],
        body := .ret (.binop "<<" (.lit (.int 1)) (.lit (.int 31))) }
    , { name := "ns.sar",   params := [],
        body := .ret (.binop ">>" (.lit (.int (-8))) (.lit (.int 1))) }
    , { name := "ns.sarNeg", params := [],
        body := .ret (.binop ">>" (.lit (.int (-1))) (.lit (.int 4))) }
      -- `unsigned u = 0x80000000u; u >> 31` — the *logical* shift, which the exporter
      -- emits as `>>>` because the left operand's static type is unsigned.
    , { name := "ns.shrU",  params := [],
        body := .ret (.binop ">>>" (.lit (.int 0x80000000)) (.lit (.int 31))) }
      -- The same bits arrived at by wrapping arithmetic, which is how the value actually
      -- shows up when it is computed rather than written down.
    , { name := "ns.shrUw", params := [],
        body := .ret (.binop ">>>" (.binop "<<" (.lit (.int 1)) (.lit (.int 31)))
                                   (.lit (.int 31))) }
    , { name := "ns.shrU4", params := [],
        body := .ret (.binop ">>>" (.lit (.int 0xF0000000)) (.lit (.int 4))) }
      -- The negative control for the `>>` / `>>>` split. It has to be written with the
      -- value in its *wrapped* form: an integer literal is not normalised to the
      -- dialect's width on the way in, so `0xF0000000` is the positive `4026531840` in
      -- Core, and on a non-negative value the two shifts agree by definition. `1 << 31`
      -- is `INT_MIN`, and there the two disagree, which is the point.
      --   `int x = 1 << 31; x >> 4`       cc: -134217728
      --   `unsigned u = 1u << 31; u >> 4` cc:  134217728
    , { name := "ns.sarMin", params := [],
        body := .ret (.binop ">>" (.binop "<<" (.lit (.int 1)) (.lit (.int 31)))
                                  (.lit (.int 4))) }
    , { name := "ns.shrMin", params := [],
        body := .ret (.binop ">>>" (.binop "<<" (.lit (.int 1)) (.lit (.int 31)))
                                   (.lit (.int 4))) }
      -- `int a[] = {7,8,9}; return a[1] ^ a[2];`
    , { name := "ns.tbl",   params := [],
        body := .ret (.binop "^" (.index (.listE [.lit (.int 7), .lit (.int 8),
                                                  .lit (.int 9)]) (.lit (.int 1)))
                                 (.index (.listE [.lit (.int 7), .lit (.int 8),
                                                  .lit (.int 9)]) (.lit (.int 2)))) }
      -- `struct crypto_alg alg = { .cra_priority = 100, .cra_name = "842" };
      --  return alg.cra_priority;`
    , { name := "ns.desig", params := [],
        body := .seq (.assign "alg" (.dictE [(.lit (.str "cra_priority"), .lit (.int 100)),
                                             (.lit (.str "cra_name"), .lit (.str "842"))]))
                     (.ret (.field (.name "alg") "cra_priority")) }
      -- A field the initializer does not mention is a hole, not `unit`.
    , { name := "ns.desigMissing", params := [],
        body := .seq (.assign "alg" (.dictE [(.lit (.str "cra_priority"),
                                              .lit (.int 100))]))
                     (.ret (.field (.name "alg") "cra_flags")) }
    , { name := "ns.forSum", params := []
      , body :=
          .seq (.assign "s" (.lit (.int 0)))
          (.seq (.assign "i" (.lit (.int 0)))
          (.seq (.loop (.binop "<" (.name "i") (.lit (.int 10)))
                  (.seq
                    -- the body, with `step; continue` in place of each `continue`
                    (.seq (.ifte (.binop "=="
                                    (.binop "%" (.name "i") (.lit (.int 3)))
                                    (.lit (.int 0)))
                            (.seq (.assign "i" (.binop "+" (.name "i") (.lit (.int 1))))
                                  .cont)
                            .skip)
                          (.assign "s" (.binop "+" (.name "s") (.name "i"))))
                    -- the step
                    (.assign "i" (.binop "+" (.name "i") (.lit (.int 1))))))
                (.ret (.binop "+" (.binop "*" (.name "s") (.lit (.int 100)))
                                  (.name "i"))))) }
    , { name := "ns.forNaive", params := []
      , body :=
          .seq (.assign "s" (.lit (.int 0)))
          (.seq (.assign "i" (.lit (.int 0)))
          (.seq (.loop (.binop "<" (.name "i") (.lit (.int 10)))
                  (.seq
                    (.seq (.ifte (.binop "=="
                                    (.binop "%" (.name "i") (.lit (.int 3)))
                                    (.lit (.int 0)))
                            .cont
                            .skip)
                          (.assign "s" (.binop "+" (.name "s") (.name "i"))))
                    (.assign "i" (.binop "+" (.name "i") (.lit (.int 1))))))
                (.ret (.binop "+" (.binop "*" (.name "s") (.lit (.int 100)))
                                  (.name "i"))))) }
      -- `for (j = 0; j < 10; j++) { if (j == 4) break; t += j; }` — `break` must *not*
      -- run the step, so `j` is left at 4. `cc` prints `t=6 j=4`.
    , { name := "ns.forBrk", params := []
      , body :=
          .seq (.assign "t" (.lit (.int 0)))
          (.seq (.assign "j" (.lit (.int 0)))
          (.seq (.loop (.binop "<" (.name "j") (.lit (.int 10)))
                  (.seq
                    (.seq (.ifte (.binop "==" (.name "j") (.lit (.int 4))) .brk .skip)
                          (.assign "t" (.binop "+" (.name "t") (.name "j"))))
                    (.assign "j" (.binop "+" (.name "j") (.lit (.int 1))))))
                (.ret (.binop "+" (.binop "*" (.name "t") (.lit (.int 100)))
                                  (.name "j"))))) }
      -- The kernel error-handling shape:
      --
      --     err = 0; err = 7; if (err) goto out; err = 100; out: err = err + 1;
      --     return err;
      --
      -- as `methodBody` encodes it: `while (true) { prefix; break } suffix`. The jump
      -- must skip `err = 100` and still run `err = err + 1`, so the answer is 8. `100`
      -- would mean the jump did not happen and `7` that the tail did not run.
    , { name := "ns.gotoOut", params := []
      , body :=
          .seq (.loop (.lit (.bool true))
                 (.seq (.seq (.assign "err" (.lit (.int 7)))
                        (.seq (.ifte (.name "err") .brk .skip)
                              (.assign "err" (.lit (.int 100)))))
                       .brk))
               (.seq (.assign "err" (.binop "+" (.name "err") (.lit (.int 1))))
                     (.ret (.name "err"))) }
      -- The same shape with the jump not taken: the wrapper must be transparent.
    , { name := "ns.gotoFall", params := []
      , body :=
          .seq (.loop (.lit (.bool true))
                 (.seq (.seq (.assign "err" (.lit (.int 0)))
                        (.seq (.ifte (.name "err") .brk .skip)
                              (.assign "err" (.lit (.int 100)))))
                       .brk))
               (.seq (.assign "err" (.binop "+" (.name "err") (.lit (.int 1))))
                     (.ret (.name "err"))) }
      -- And a `return` from inside the wrapper, which must leave the *function*, not the
      -- synthetic loop: `cc` returns 5, never reaching the tail.
    , { name := "ns.gotoRet", params := []
      , body :=
          .seq (.loop (.lit (.bool true))
                 (.seq (.seq (.assign "err" (.lit (.int 5)))
                             (.ret (.name "err")))
                       .brk))
               (.seq (.assign "err" (.lit (.int 99))) (.ret (.name "err"))) } ] }

/-- The same designated-initializer program under `.python`, where `d.f` on a dict is an
`AttributeError` and must stay a hole. `Dialect.fieldsOnDicts` is the switch. -/
private def pyDesig : Program := { cBits with dialect := .python }

-- `0x5A ^ 0x3C` — cc: 102
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 102) -/
#guard_msgs in #eval runFunc cBits 200 "ns.xor" []
-- `-1 & 255` — cc: 255.  Not `-1`, and not a boolean.
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 255) -/
#guard_msgs in #eval runFunc cBits 200 "ns.and" []
-- `0xF0 | 0x0F` — cc: 255
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 255) -/
#guard_msgs in #eval runFunc cBits 200 "ns.or" []
-- `~0x5A` — cc: -91.  Under the old `<operator>.not -> "!"` mapping this was `false`.
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int (-91)) -/
#guard_msgs in #eval runFunc cBits 200 "ns.bnot" []
-- `1 << 31` — cc -fwrapv: -2147483648
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int (-2147483648)) -/
#guard_msgs in #eval runFunc cBits 200 "ns.shl" []
-- `-8 >> 1` — cc: -4 (arithmetic, sign-extending)
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int (-4)) -/
#guard_msgs in #eval runFunc cBits 200 "ns.sar" []
-- `-1 >> 4` — cc: -1
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int (-1)) -/
#guard_msgs in #eval runFunc cBits 200 "ns.sarNeg" []
-- `0x80000000u >> 31` — cc: 1 (logical, zero-filling)
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 1) -/
#guard_msgs in #eval runFunc cBits 200 "ns.shrU" []
-- ... and the same bits reached by `1 << 31`, which Core stores as a negative number.
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 1) -/
#guard_msgs in #eval runFunc cBits 200 "ns.shrUw" []
-- `0xF0000000u >> 4` — cc: 251658240
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 251658240) -/
#guard_msgs in #eval runFunc cBits 200 "ns.shrU4" []
-- The negative control: on `INT_MIN` the arithmetic shift keeps the sign bits and the
-- logical one does not. `>>` and `>>>` are two operators, and this is the difference.
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int (-134217728)) -/
#guard_msgs in #eval runFunc cBits 200 "ns.sarMin" []
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 134217728) -/
#guard_msgs in #eval runFunc cBits 200 "ns.shrMin" []
-- `int a[] = {7,8,9}; a[1] ^ a[2]` — cc: 1
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 1) -/
#guard_msgs in #eval runFunc cBits 200 "ns.tbl" []
-- A designated initializer read back by field name: 100, not `unit` and not a hole.
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 100) -/
#guard_msgs in #eval runFunc cBits 200 "ns.desig" []
-- A field the aggregate does not carry: a hole naming it, never an invented `unit`.
/-- info: Autoform.Core.EResult.hole "field:cra_flags:absent-from-aggregate" -/
#guard_msgs in #eval runFunc cBits 200 "ns.desigMissing" []
-- The dialect split. `{'cra_priority': 100}.cra_priority` is an `AttributeError` in
-- Python, so under `.python` the same term is the hole it has always been.
/-- info: Autoform.Core.EResult.hole "field:cra_priority:non-object" -/
#guard_msgs in #eval runFunc pyDesig 200 "ns.desig" []
-- The `for` with `continue`: `s = 27`, `i = 10` — cc: `forcont s=27 i=10`.
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 2710) -/
#guard_msgs in #eval runFunc cBits 4000 "ns.forSum" []
-- The negative control. The textbook desugaring skips the step on `continue` and spins
-- forever; four thousand steps of fuel are not enough because no number of them is.
/-- info: Autoform.Core.EResult.outOfFuel -/
#guard_msgs in #eval runFunc cBits 4000 "ns.forNaive" []
-- The `for` with `break`: `t = 6`, `j = 4` — cc: `forbrk t=6 j=4`. `break` leaves
-- without running the step, which is why `j` is 4 and not 5.
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 604) -/
#guard_msgs in #eval runFunc cBits 4000 "ns.forBrk" []
-- `goto out` taken: skips the middle, runs the tail. cc: 8.
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 8) -/
#guard_msgs in #eval runFunc cBits 400 "ns.gotoOut" []
-- ... not taken: falls through the whole prefix, then the tail. cc: 101.
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 101) -/
#guard_msgs in #eval runFunc cBits 400 "ns.gotoFall" []
-- ... and a `return` inside the wrapper leaves the function, not the synthetic loop.
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 5) -/
#guard_msgs in #eval runFunc cBits 400 "ns.gotoRet" []

end CEvidence

/-! ## Modules as objects, end to end

The exporter represents an imported module as a **heap object** whose class name begins
`<module>` and whose fields are the module's top-level functions, classes and submodules,
allocated once by a synthetic initializer that `render_lean.py` places first in
`moduleInits`. Nothing was added to `Core` for it: `Expr.alloc`, `Stmt.setField` and
`Expr.field` already do the work.

The program below is the translation of a two-file package, in the exact shape
`cartographer/export_ast.sc` emits:

```python
# pkg/util.py
def double(n):
    return n * 2

# main
import pkg.util
pkg.util.double(21)      # 42
pkg.util.double          # <function double at ...>
pkg.util.VERSION         # AttributeError
```

Measured with CPython 3.9.6:

```
42
<function double at 0x109796af0>
AttributeError: module 'pkg.util' has no attribute 'VERSION'
```

The three checks below are the non-vacuity evidence. A module object with no fields, or
one whose fields never resolved, would answer `unit` to all three while every downstream
theorem still passed. -/
def modProg : Program :=
  { dialect := .python
  , funcs :=
    [ { name := "pkg/util.py:<module>.double", params := ["n"]
      , body := .ret (.binop "*" (.name "n") (.lit (.int 2))) }
      -- `pkg.util.double(21)`: a field read through the package object into the submodule
      -- object, then a call of the function that submodule's field holds.
    , { name := "main.run", params := []
      , body := .ret (.mcall (.field (.name "<module>pkg/__init__.py") "util")
                             "double" [.lit (.int 21)]) }
      -- `pkg.util.double` as a *value*: nesting resolves without calling anything.
    , { name := "main.ref", params := []
      , body := .ret (.field (.field (.name "<module>pkg/__init__.py") "util") "double") }
      -- `pkg.util.VERSION`: a module-level name the module object deliberately does not
      -- carry. CPython raises `AttributeError`; Core refuses. Refusing is not the same
      -- claim as raising, so it is a hole and not an `exn`.
    , { name := "main.attr", params := []
      , body := .ret (.field (.field (.name "<module>pkg/__init__.py") "util") "VERSION") } ] }

/-- The synthetic `<module-objects>` initializer: **all** allocations first, then the
field writes, so a package and a module that import each other both exist before either
is populated. -/
def modInit : Func :=
  { name := "<module-objects>:<module>", params := []
  , body :=
      .seq (.setGlobal "<module>pkg/__init__.py" (.alloc "<module>pkg/__init__.py" []))
      (.seq (.setGlobal "<module>pkg/util.py" (.alloc "<module>pkg/util.py" []))
      (.seq (.setField (.name "<module>pkg/__init__.py") "util"
                       (.name "<module>pkg/util.py"))
            (.setField (.name "<module>pkg/util.py") "double"
                       (.fnref "pkg/util.py:<module>.double")))) }

/-! `pkg.util.double(21)` is `42`, as CPython prints. `unit` would mean a field read
missed; a hole would mean the module object never reached the call. -/
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 42) -/
#guard_msgs in #eval runMain modProg 200 [modInit] "main.run" []

/-! Nesting: the package's `util` field holds the submodule object, whose `double` field
holds the function value. -/
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.fn "pkg/util.py:<module>.double") -/
#guard_msgs in #eval runMain modProg 200 [modInit] "main.ref" []

/-! The honesty check, and the reason a module object carries a marker class at all. An
ordinary object answers `unit` for a field it does not have (`ns.unset`, above); a module
object names the miss. Module-level *data* is absent from a module object on purpose —
Core has one globals frame for the whole program, so a module-level constant is not
module-scoped and its value would have to be captured before the module body computed it
— and this is what stops that decision from becoming a silent `unit`. -/
/-- info: Autoform.Core.EResult.hole "module-attr:VERSION" -/
#guard_msgs in #eval runMain modProg 200 [modInit] "main.attr" []

/-! ## f-strings

`f'v{n}!'` is `"v" + str(n) + "!"` — that is the language definition for a field with no
conversion and no format spec, so the exporter emits exactly that. What it meets is a
Core limitation that predates it: `Stdlib.builtin`'s `str` answers on `.int` and `.bool`
and **declines on `.str`**, because Core represents an exception as a bare `Val.str` and
cannot tell one from an ordinary string.

So the f-string hole *moves* rather than vanishing, and both halves are pinned here.
Measured with CPython 3.9.6: `greet(3)` is `'v3!'` and `greet('x')` is `'vx!'`. -/
def fstrProg : Program :=
  { dialect := .python
  , funcs :=
    [ { name := "greet", params := ["n"]
      , body := .ret (.binop "+" (.binop "+" (.lit (.str "v")) (.call "str" [.name "n"]))
                                 (.lit (.str "!"))) } ] }

/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.str "v3!") -/
#guard_msgs in #eval runFunc fstrProg 200 "greet" [.int 3]

/-! The residue, named for what actually blocks it. CPython answers `'vx!'`; Core answers
a hole at `str` rather than a wrong string, and the label points at `Stdlib`'s `str`, not
at the f-string. -/
/-- info: Autoform.Core.EResult.hole "call:str" -/
#guard_msgs in #eval runFunc fstrProg 200 "greet" [.str "x"]

end Autoform.Core
