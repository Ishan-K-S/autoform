import Autoform.Lang.Core.Syntax

/-!
# Core — fixed-width machine integers

`Core` originally modelled every integer as a mathematical `Int`. That is exactly right
for Python and exactly wrong for C, C++, Java and Go. The conformance oracle measured
the divergence:

```
mulbig(100000, 100000)   cc: 1410065408      Core: 10000000000
```

`1410065408` is `10^10` reduced mod `2^32` and reinterpreted as a signed 32-bit value.
This is the worst class of defect in the project's taxonomy: it silently returns a
*wrong number* rather than a visible hole.

Following §12 ("the dialect lesson"), the fix is structural rather than a patch to one
operator. Integer width, signedness, overflow behaviour, shift behaviour and division
rounding are **dialect parameters** of the universal core, bundled here as `NumConfig`.
`Dialect.idiv`/`Dialect.imod` in `Semantics.lean` were the first instance of this
pattern; this file generalises it.

## What is modelled

* `IntType` — `unbounded` (Python `int`, Java `BigInteger`, Go `big.Int`) plus signed
  and unsigned 8/16/32/64-bit machine words.
* `IntType.wrap` — two's-complement normalisation into range.
* `NumConfig` — the width *plus* the policy choices below.
* `NumResult` — `ok`, `divZero`, `trap`, and crucially `ub`.

## Undefined behaviour is represented, not guessed

Where real languages genuinely disagree or leave a case undefined, this module refuses
to silently pick an answer. `NumResult.ub reason` says "this program's result depends on
behaviour the source language does not define". A ledger can count those; a theorem
cannot accidentally quantify over them. The cases, and who does what:

| Case | C / C++ | Java | Go | Python |
|---|---|---|---|---|
| signed overflow | **UB** | wraps | wraps | n/a (bignum) |
| unsigned overflow | wraps | n/a | wraps | n/a |
| `INT_MIN / -1` | **UB** | yields `INT_MIN` | **panics** | n/a |
| `INT_MIN % -1` | **UB** | yields `0` | panics | n/a |
| shift count ≥ width | **UB** | count taken mod width | **panics**¹ | n/a |
| negative shift count | **UB** | (mod width, so no) | panics | `ValueError` |
| `>>` of a negative | arithmetic | `>>` arithmetic, `>>>` logical | arithmetic | arithmetic |
| `/` rounding | toward zero | toward zero | toward zero | toward −∞ |

¹ Go shifts by an over-large *count* yield 0 rather than panicking; Go panics only on a
negative count. `Policy.wrap` here means "reduce the count mod width" (the x86/Java
behaviour), so Go is modelled with `.undefined` unless the caller knows better. This
imprecision is recorded rather than hidden.

Note the deliberate asymmetry: `NumConfig.c32` uses `Policy.undefined` for signed
overflow, because that is what the *standard* says, and a program relying on it is a
latent bug. `NumConfig.c32Wrapv` uses `Policy.wrap`, which is what mainstream compilers
at `-O0`/`-fwrapv` actually do and therefore what the differential oracle observes.
`Dialect.toNumConfig .cLike` picks the wrapping variant so the interpreter agrees with
the measured runtime; switch it to `c32` to *find* UB reliance instead of matching it.

## Discipline

Total functions only: no `partial`, no `sorry`, no `unsafe`, no `native_decide`.
-/

namespace Autoform.Core

/-! ## Widths -/

/-- Machine word widths the core models. -/
inductive Width where
  | w8 | w16 | w32 | w64
  deriving Repr, Inhabited, DecidableEq

namespace Width

/-- Width in bits. -/
def bits : Width → Nat
  | .w8 => 8 | .w16 => 16 | .w32 => 32 | .w64 => 64

theorem bits_pos (w : Width) : 0 < w.bits := by cases w <;> decide

/-- `2 ^ bits = 2 * 2 ^ (bits - 1)`; proved without evaluating `2 ^ 64`. -/
theorem two_pow_bits (w : Width) : (2 : Nat) ^ w.bits = 2 * 2 ^ (w.bits - 1) := by
  obtain ⟨k, hk⟩ : ∃ k, w.bits = k + 1 := ⟨w.bits - 1, by have := w.bits_pos; omega⟩
  simp [hk, Nat.pow_succ, Nat.mul_comm]

end Width

/-! ## Integer types -/

/-- An integer type: mathematically unbounded, or a fixed-width machine word. -/
inductive IntType where
  /-- Python `int`, Java `BigInteger`, Lean `Int`: no overflow, ever. -/
  | unbounded : IntType
  /-- Two's-complement signed word. -/
  | signed    : Width → IntType
  /-- Unsigned word. -/
  | unsigned  : Width → IntType
  deriving Repr, Inhabited, DecidableEq

namespace IntType

/-- Width in bits; `0` for `unbounded` (which has no width). -/
def bits : IntType → Nat
  | .unbounded  => 0
  | .signed w   => w.bits
  | .unsigned w => w.bits

/-- `2 ^ bits`: the modulus of the wrap-around. Meaningless for `unbounded`. -/
def modulus (t : IntType) : Nat := 2 ^ t.bits

/-- Half the modulus: the magnitude of the most negative signed value. -/
def half (t : IntType) : Nat := 2 ^ (t.bits - 1)

def isFixed : IntType → Bool
  | .unbounded => false | _ => true

def isSigned : IntType → Bool
  | .unbounded => true | .signed _ => true | .unsigned _ => false

/-- Smallest representable value (`none` for `unbounded`). -/
def lo : IntType → Option Int
  | .unbounded  => none
  | .signed w   => some (-((2:Int) ^ (w.bits - 1)))
  | .unsigned _ => some 0

/-- Largest representable value, inclusive (`none` for `unbounded`). -/
def hi : IntType → Option Int
  | .unbounded  => none
  | .signed w   => some (((2:Int) ^ (w.bits - 1)) - 1)
  | .unsigned w => some (((2:Int) ^ w.bits) - 1)

/-- Is `x` representable in `t`? -/
def inRange : IntType → Int → Bool
  | .unbounded,  _ => true
  | .signed w,   x => (-((2:Int) ^ (w.bits - 1)) ≤ x) && (x < ((2:Int) ^ (w.bits - 1)))
  | .unsigned w, x => (0 ≤ x) && (x < ((2:Int) ^ w.bits))

/-- Two's-complement normalisation: the unique representable value congruent to `x`
modulo `2 ^ bits`. The identity on `unbounded`. -/
def wrap : IntType → Int → Int
  | .unbounded,  x => x
  | .unsigned w, x => x % ((2:Int) ^ w.bits)
  | .signed w,   x =>
      let m : Int := ((2:Int) ^ w.bits)
      let h : Int := ((2:Int) ^ (w.bits - 1))
      let r := x % m
      if r < h then r else r - m

/-- The unsigned bit pattern of `x` at this type's width, as a `Nat`. For `unbounded`
this is not meaningful and returns `x.natAbs`. -/
def bitsOf : IntType → Int → Nat
  | .unbounded, x => x.natAbs
  | t,          x => (x % ((2:Int) ^ t.bits)).toNat

end IntType

/-! ## Policies -/

/-- What to do when an operation leaves the representable range, or is handed an
out-of-range shift count. -/
inductive Policy where
  /-- Two's-complement wrap-around (Java, Go, C `-fwrapv`, all unsigned C). For shift
  counts, "wrap" means reduce the count modulo the width. -/
  | wrap
  /-- The source language leaves this undefined. Produce `NumResult.ub`. -/
  | undefined
  /-- The source language defines this as a runtime fault (Go integer divide panic,
  Java `ArithmeticException`, Rust debug overflow). Produce `NumResult.trap`. -/
  | trap
  deriving Repr, Inhabited, DecidableEq

/-- Right-shift of a negative value. -/
inductive ShiftSemantics where
  /-- Sign-extending: `-8 >> 1 = -4`. C (in practice), Java `>>`, Go, Python. -/
  | arithmetic
  /-- Zero-filling on the type's width: Java `>>>`, C on unsigned. -/
  | logical
  /-- Implementation-defined in C89/C99 for negative left operands. -/
  | undefined
  deriving Repr, Inhabited, DecidableEq

/-- Rounding direction of integer division (the §12 dialect bug, in this file's terms). -/
inductive DivRound where
  /-- Toward zero: C, C++, Java, Go, Rust. -/
  | trunc
  /-- Toward −∞: Python. -/
  | floor
  deriving Repr, Inhabited, DecidableEq

/-- The full numeric dialect: everything about integer behaviour that differs across the
languages the core unifies. -/
structure NumConfig where
  type             : IntType       := .unbounded
  /-- Signed overflow. Unsigned overflow always wraps — every language that has
  unsigned integers defines it that way. -/
  onSignedOverflow : Policy        := .wrap
  /-- Shift count negative, or ≥ width. -/
  onShiftCount     : Policy        := .undefined
  /-- `>>` applied to a negative value. -/
  negRightShift    : ShiftSemantics := .arithmetic
  divRound         : DivRound      := .trunc
  deriving Repr, Inhabited, DecidableEq

namespace NumConfig

/-- Python: bignums, floor division, negative shift counts raise `ValueError`. -/
def python : NumConfig :=
  { type := .unbounded, onShiftCount := .trap, divRound := .floor }

/-- C `int` as the standard defines it: signed overflow, `INT_MIN / -1` and over-wide
shifts are **undefined**, and this config says so out loud. -/
def c32 : NumConfig :=
  { type := .signed .w32, onSignedOverflow := .undefined, onShiftCount := .undefined,
    negRightShift := .arithmetic, divRound := .trunc }

/-- C `int` as mainstream compilers actually behave (`-fwrapv`, or `-O0` in practice).
This is the config that reproduces the measured `cc` output. -/
def c32Wrapv : NumConfig := { c32 with onSignedOverflow := .wrap }

/-- C `long` / `int64_t`, wrapping variant. -/
def c64Wrapv : NumConfig := { c32Wrapv with type := .signed .w64 }

/-- C `unsigned int`. Wrapping is *defined* here, by the standard. -/
def u32 : NumConfig := { type := .unsigned .w32, onShiftCount := .undefined }

/-- Java `int`: overflow wraps, shift counts are masked to 5 bits, `/` truncates,
`Integer.MIN_VALUE / -1` is `Integer.MIN_VALUE`. -/
def java32 : NumConfig :=
  { type := .signed .w32, onSignedOverflow := .wrap, onShiftCount := .wrap,
    negRightShift := .arithmetic, divRound := .trunc }

/-- Java `long`. -/
def java64 : NumConfig := { java32 with type := .signed .w64 }

/-- Go `int` (64-bit on mainstream platforms): overflow wraps, division by zero and
`MinInt / -1` panic. -/
def go64 : NumConfig :=
  { type := .signed .w64, onSignedOverflow := .trap, onShiftCount := .undefined,
    negRightShift := .arithmetic, divRound := .trunc }

end NumConfig

/-- Numeric config implied by a `Core.Dialect`. `cLike` gets the *wrapping* 32-bit
signed config, so the interpreter agrees with the compiler the oracle measures; use
`NumConfig.c32` explicitly to surface UB reliance instead. `javascript` gets `python`
(unbounded): this is the specific, measured fix for `2147483647 + 1` (Node:
`2147483648`; the old `.cLike`-routed answer: `-2147483648`) and is exact for every
value up to `Number.MAX_SAFE_INTEGER`. It is still a *named* approximation past that
bound, and for the bitwise/shift operators, which real JS truncates to Int32 and this
config does not — see `Dialect`'s doc comment in `Syntax.lean`. -/
def Dialect.toNumConfig : Dialect → NumConfig
  | .python     => NumConfig.python
  | .cLike      => NumConfig.c32Wrapv
  | .javascript => NumConfig.python

/-! ## Results -/

/-- The outcome of a machine-integer operation. Four distinct outcomes, because they
mean four different things — the same discipline `EResult` applies to evaluation. -/
inductive NumResult where
  | ok      : Int → NumResult
  /-- Division or remainder by zero. -/
  | divZero : NumResult
  /-- The source language does not define this. The program's meaning depends on the
  compiler, so no number is the right answer. -/
  | ub      : String → NumResult
  /-- The source language defines this as a runtime fault. -/
  | trap    : String → NumResult
  deriving Repr, Inhabited, DecidableEq

namespace NumResult

def isOk : NumResult → Bool | .ok _ => true | _ => false
def toOption : NumResult → Option Int | .ok v => some v | _ => none

end NumResult

/-! ## Range lemmas -/

namespace IntType

theorem inRange_unbounded (x : Int) : inRange .unbounded x = true := rfl

theorem wrap_unbounded (x : Int) : wrap .unbounded x = x := rfl

private theorem two_pow_pos (n : Nat) : (0 : Int) < 2 ^ n := by
  induction n with
  | zero => decide
  | succ k ih => rw [Int.pow_succ]; exact Int.mul_pos ih (by decide)

private theorem modulus_pos (w : Width) : (0 : Int) < (2:Int) ^ w.bits := two_pow_pos _

private theorem half_pos (w : Width) : (0 : Int) < (2:Int) ^ (w.bits - 1) := two_pow_pos _

private theorem mod_eq_two_half (w : Width) :
    (2:Int) ^ w.bits = 2 * (2:Int) ^ (w.bits - 1) := by
  obtain ⟨k, hk⟩ : ∃ k, w.bits = k + 1 := ⟨w.bits - 1, by have := w.bits_pos; omega⟩
  rw [hk]
  simp [Int.pow_succ, Int.mul_comm]

/-- **Wrapping lands in range.** Every fixed-width operation in this file goes through
`wrap`, so every fixed-width result is representable. -/
theorem wrap_inRange (t : IntType) (x : Int) : t.inRange (t.wrap x) = true := by
  cases t with
  | unbounded => rfl
  | unsigned w =>
      have hm := modulus_pos w
      have h0 : 0 ≤ x % ((2:Int) ^ w.bits) := Int.emod_nonneg x (by omega)
      have h1 : x % ((2:Int) ^ w.bits) < ((2:Int) ^ w.bits) :=
        Int.emod_lt_of_pos x hm
      simp [wrap, inRange, h0, h1]
  | signed w =>
      have hm := modulus_pos w
      have hh := half_pos w
      have hmh := mod_eq_two_half w
      have h0 : 0 ≤ x % ((2:Int) ^ w.bits) := Int.emod_nonneg x (by omega)
      have h1 : x % ((2:Int) ^ w.bits) < ((2:Int) ^ w.bits) :=
        Int.emod_lt_of_pos x hm
      by_cases hlt : x % ((2:Int) ^ w.bits) < ((2:Int) ^ (w.bits - 1)) <;>
        simp [wrap, inRange, hlt] <;> omega

/-- Wrapping is the identity on values already in range. -/
theorem wrap_of_inRange {t : IntType} {x : Int} (h : t.inRange x = true) : t.wrap x = x := by
  cases t with
  | unbounded => rfl
  | unsigned w =>
      simp only [inRange, Bool.and_eq_true, decide_eq_true_eq] at h
      simp [wrap, Int.emod_eq_of_lt h.1 h.2]
  | signed w =>
      have hmh := mod_eq_two_half w
      have hh := half_pos w
      simp only [inRange, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨h1, h2⟩ := h
      by_cases hx : 0 ≤ x
      · have hm : x % ((2:Int) ^ w.bits) = x := Int.emod_eq_of_lt hx (by omega)
        simp only [wrap, hm]
        split <;> omega
      · have hx' : 0 ≤ x + ((2:Int) ^ w.bits) := by omega
        have h3 : (x + ((2:Int) ^ w.bits)) % ((2:Int) ^ w.bits) = x % ((2:Int) ^ w.bits) := by
          have := Int.add_mul_emod_self_left (a := x) (b := ((2:Int) ^ w.bits)) (c := 1)
          simpa using this
        have h4 : (x + ((2:Int) ^ w.bits)) % ((2:Int) ^ w.bits) = x + ((2:Int) ^ w.bits) :=
          Int.emod_eq_of_lt hx' (by omega)
        have h5 : x % ((2:Int) ^ w.bits) = x + ((2:Int) ^ w.bits) := by rw [← h3, h4]
        simp only [wrap, h5]
        split <;> omega

/-- Wrapping is idempotent — a corollary of the two lemmas above. -/
theorem wrap_wrap (t : IntType) (x : Int) : t.wrap (t.wrap x) = t.wrap x :=
  wrap_of_inRange (wrap_inRange t x)

end IntType

/-! ## Arithmetic -/

namespace NumConfig

/-- Take an exact mathematical result to a machine result: in range, it is itself;
out of range, the type's overflow policy decides. Unsigned overflow always wraps —
that is defined behaviour in every language that has unsigned integers. -/
def finish (c : NumConfig) (exact : Int) : NumResult :=
  if c.type.inRange exact then .ok exact
  else
    match c.type with
    | .unbounded  => .ok exact                       -- unreachable: always in range
    | .unsigned _ => .ok (c.type.wrap exact)
    | .signed _   =>
      match c.onSignedOverflow with
      | .wrap      => .ok (c.type.wrap exact)
      | .undefined => .ub "signed integer overflow"
      | .trap      => .trap "signed integer overflow"

def add (c : NumConfig) (a b : Int) : NumResult := c.finish (a + b)
def sub (c : NumConfig) (a b : Int) : NumResult := c.finish (a - b)
def mul (c : NumConfig) (a b : Int) : NumResult := c.finish (a * b)

/-- Negation. `-INT_MIN` is not representable, so it goes through the overflow policy. -/
def neg (c : NumConfig) (a : Int) : NumResult := c.finish (-a)

/-- Exact quotient under the configured rounding. -/
def quot (c : NumConfig) (a b : Int) : Int :=
  match c.divRound with
  | .trunc => Int.tdiv a b
  | .floor => Int.fdiv a b

/-- Exact remainder under the configured rounding. Matches `quot`: `a = b * q + r`. -/
def rem (c : NumConfig) (a b : Int) : Int :=
  match c.divRound with
  | .trunc => Int.tmod a b
  | .floor => Int.fmod a b

/-- Division. Two failure modes beyond overflow: division by zero, and `INT_MIN / -1`,
whose mathematical quotient `2^(n-1)` is one past the top of the signed range. -/
def div (c : NumConfig) (a b : Int) : NumResult :=
  if b == 0 then .divZero else c.finish (c.quot a b)

/-- Remainder. `INT_MIN % -1` is mathematically `0` — in range — yet C makes it
undefined and Go panics, because the *quotient* overflows. So the overflow check is on
the quotient, and the wrapping answer is the true remainder `0`. -/
def mod (c : NumConfig) (a b : Int) : NumResult :=
  if b == 0 then .divZero
  else
    let q := c.quot a b
    if c.type.inRange q then .ok (c.type.wrap (c.rem a b))
    else
      match c.type with
      | .unbounded  => .ok (c.rem a b)
      | .unsigned _ => .ok (c.type.wrap (c.rem a b))
      | .signed _   =>
        match c.onSignedOverflow with
        | .wrap      => .ok (c.type.wrap (c.rem a b))
        | .undefined => .ub "remainder with overflowing quotient (INT_MIN % -1)"
        | .trap      => .trap "remainder with overflowing quotient (INT_MIN % -1)"

/-! ### Shifts -/

/-- Normalise a shift count, or report why it cannot be. Returns the count to use. -/
def shiftCount (c : NumConfig) (k : Int) : NumResult :=
  match c.type with
  | .unbounded =>
      if k < 0 then
        match c.onShiftCount with
        | .wrap      => .ok 0
        | .undefined => .ub "negative shift count"
        | .trap      => .trap "negative shift count"
      else .ok k
  | t =>
      let n : Int := (t.bits : Int)
      if 0 ≤ k && k < n then .ok k
      else
        match c.onShiftCount with
        | .wrap      => .ok (k % n)                 -- Java / x86: mask to log2(width) bits
        | .undefined => .ub "shift count out of range"
        | .trap      => .trap "shift count out of range"

/-- `a << k`. The count is normalised first, then the value is shifted exactly and put
through the overflow policy — C makes a signed left shift that loses bits undefined,
Java and Go define it to wrap. -/
def shl (c : NumConfig) (a k : Int) : NumResult :=
  match c.shiftCount k with
  | .ok k' => c.finish (a * 2 ^ k'.toNat)
  | r      => r

/-- `a >> k`. Arithmetic (sign-extending) or logical (zero-filling) on negatives,
per `negRightShift`. Both agree on non-negative values. -/
def shr (c : NumConfig) (a k : Int) : NumResult :=
  match c.shiftCount k with
  | .ok k' =>
      let n := k'.toNat
      if 0 ≤ a then .ok (c.type.wrap (Int.fdiv a (2 ^ n)))
      else
        match c.negRightShift with
        | .arithmetic => .ok (c.type.wrap (Int.fdiv a (2 ^ n)))
        | .logical =>
            match c.type with
            | .unbounded =>
                -- A negative bignum has infinitely many leading sign bits; there is no
                -- logical shift. Java's `>>>` only exists on fixed widths.
                .ub "logical right shift of an unbounded negative value"
            | t => .ok (t.wrap (((t.bitsOf a) / 2 ^ n : Nat) : Int))
        | .undefined => .ub "right shift of a negative value"
  | r      => r

/-! ### Bitwise -/

/-- Width, in bits, large enough to hold both operands as two's-complement signed
values. Used only for `unbounded`, where the bit pattern is conceptually infinite but
`and`/`or`/`xor` are still determined by any sufficiently wide window. -/
def dynWidth (a b : Int) : Nat := Nat.max a.natAbs.log2 b.natAbs.log2 + 2

/-- Bitwise operation lifted to two's complement. For fixed widths the operands are
reduced to their bit patterns and the result reinterpreted; for `unbounded` a window
wide enough for both operands is used, which is exact for `and`/`or`/`xor`. -/
def bitwise (c : NumConfig) (f : Nat → Nat → Nat) (a b : Int) : NumResult :=
  match c.type with
  | .unbounded =>
      let n := dynWidth a b
      let m : Int := ((2:Int) ^ n)
      let h : Int := ((2:Int) ^ (n - 1))
      let r : Int := ((f (a % m).toNat (b % m).toNat : Nat) : Int)
      .ok (if r < h then r else r - m)
  | t =>
      .ok (t.wrap ((f (t.bitsOf a) (t.bitsOf b) : Nat) : Int))

def band (c : NumConfig) (a b : Int) : NumResult := c.bitwise Nat.land a b
def bor  (c : NumConfig) (a b : Int) : NumResult := c.bitwise Nat.lor  a b
def bxor (c : NumConfig) (a b : Int) : NumResult := c.bitwise Nat.xor  a b

/-- Bitwise complement. `~x = -x - 1` in two's complement, at every width, and it never
overflows: the complement of a representable value is representable. -/
def bnot (c : NumConfig) (a : Int) : NumResult := .ok (c.type.wrap (-a - 1))

/-! ### Comparison and conversion -/

/-- Reinterpret/convert a value into this config's type (a C cast). Narrowing and
signed⇄unsigned conversions are *defined* to wrap in C for unsigned destinations, and
implementation-defined (universally wrapping in practice) for signed ones — so this is
always `wrap`, and never a `ub`. -/
def cast (c : NumConfig) (a : Int) : Int := c.type.wrap a

/-- Comparison is width-independent once both sides are in range. -/
def lt (c : NumConfig) (a b : Int) : Bool := c.cast a < c.cast b
def le (c : NumConfig) (a b : Int) : Bool := c.cast a ≤ c.cast b
def eq (c : NumConfig) (a b : Int) : Bool := c.cast a == c.cast b

end NumConfig

/-! ## Lemmas about the operations

What is proved here is deliberately modest and load-bearing: results are representable,
and the `unbounded` configuration is exactly `Int`. See the open obligations below for
what is stated but not proved.
-/

namespace NumConfig

/-- **`finish` never leaves the range.** Every `ok` result of an arithmetic operation is
representable in the configured type. -/
theorem finish_inRange (c : NumConfig) (x v : Int) (h : c.finish x = .ok v) :
    c.type.inRange v = true := by
  unfold finish at h
  split at h
  · rename_i hr; cases h; exact hr
  · rename_i hr
    cases hty : c.type with
    | unbounded =>
        rw [hty] at hr; simp [IntType.inRange] at hr
    | unsigned w =>
        rw [hty] at h; cases h; exact IntType.wrap_inRange _ x
    | signed w =>
        rw [hty] at h
        cases hp : c.onSignedOverflow <;> rw [hp] at h <;> cases h
        exact IntType.wrap_inRange _ x

/-! ### The unbounded configuration is plain `Int` -/

private theorem unbounded_finish (c : NumConfig) (h : c.type = .unbounded) (x : Int) :
    c.finish x = .ok x := by
  simp [finish, h, IntType.inRange]

theorem python_add (a b : Int) : NumConfig.python.add a b = .ok (a + b) :=
  unbounded_finish _ rfl _

theorem python_sub (a b : Int) : NumConfig.python.sub a b = .ok (a - b) :=
  unbounded_finish _ rfl _

theorem python_mul (a b : Int) : NumConfig.python.mul a b = .ok (a * b) :=
  unbounded_finish _ rfl _

theorem python_neg (a : Int) : NumConfig.python.neg a = .ok (-a) :=
  unbounded_finish _ rfl _

/-- Python division floors — the §12 bug, now a theorem rather than an assumption. -/
theorem python_div (a b : Int) (h : b ≠ 0) :
    NumConfig.python.div a b = .ok (Int.fdiv a b) := by
  simp [div, NumConfig.python, quot, finish, IntType.inRange, h]

theorem python_mod (a b : Int) (h : b ≠ 0) :
    NumConfig.python.mod a b = .ok (Int.fmod a b) := by
  simp [mod, NumConfig.python, quot, rem, h, IntType.inRange, IntType.wrap]


/-- `bnot` is `-x-1` on unbounded integers, i.e. Python's `~`. -/
theorem python_bnot (a : Int) : NumConfig.python.bnot a = .ok (-a - 1) := rfl

/-! ### Open obligations

Stated here, deliberately *not* proved with `sorry`. Each is true and each needs the
congruence lemma `wrap x = wrap y ↔ x ≡ y [ZMOD 2^n]`, which is where the work is.

1. `wrap_hom_add : t.wrap (t.wrap a + t.wrap b) = t.wrap (a + b)` — and the same for
   `sub` and `mul`. i.e. wrapping arithmetic is a ring homomorphism `ℤ → ℤ/2^n`. This
   is the lemma that justifies "you may normalise operands eagerly or lazily".
2. `wrap_emod : (t.wrap x) % (t.modulus : Int) = x % (t.modulus : Int)` — the residue is
   preserved. (1) follows from this plus `Int.add_emod`/`Int.mul_emod`.
3. `shl_eq_mul : c.shl a k = c.mul a (2 ^ k)` when the count is in range.
4. `band_self : c.band a a = .ok (c.cast a)`, and the de Morgan laws relating
   `band`/`bor`/`bnot`.
5. `cast_bitsOf : t.wrap ((t.bitsOf x : Nat) : Int) = t.wrap x` — the round trip between
   the signed value and its bit pattern.

None of these are needed for the interpreter to be *correct*; they are needed for proofs
*about* programs to be tractable. They should be closed with `bv_decide` after a
`BitVec` refinement of `IntType.wrap`, which is the natural next step: Lean core's
`BitVec` already carries these lemmas, and `wrap` is definitionally
`(BitVec.ofInt n x).toInt` / `.toNat`.
-/

end NumConfig

/-! ## The confirmed bug, executable

`scripts/differential.py` measured `mulbig(100000, 100000)` as `1410065408` under `cc`
and `10000000000` under the old Core semantics. Both numbers now appear, each from the
configuration that actually produces it.
-/

section Evidence

open NumConfig

/-- C, as compilers behave: 32-bit signed wraparound. **This is the measured `cc`
answer.** -/
example : NumConfig.c32Wrapv.mul 100000 100000 = .ok 1410065408 := by decide
#eval NumConfig.c32Wrapv.mul 100000 100000        -- Autoform.Core.NumResult.ok 1410065408

-- C, as the standard defines it: the program relies on undefined behaviour, and the semantics says so instead of inventing a number.
#eval NumConfig.c32.mul 100000 100000             -- ub "signed integer overflow"

-- Java `int`: defined to wrap, same bits.
#eval NumConfig.java32.mul 100000 100000          -- ok 1410065408

-- Python: unbounded, the old answer, and still the right one *for Python*.
#eval NumConfig.python.mul 100000 100000          -- ok 10000000000

-- 64-bit C: no overflow at this magnitude.
#eval NumConfig.c64Wrapv.mul 100000 100000        -- ok 10000000000

-- Unsigned 32-bit: the same bits, read as unsigned.
#eval NumConfig.u32.mul 100000 100000             -- ok 1410065408

-- Overflow at the boundary.
#eval NumConfig.java32.add 2147483647 1           -- ok (-2147483648)
#eval NumConfig.c32.add 2147483647 1              -- ub "signed integer overflow"
#eval NumConfig.u32.add 4294967295 1              -- ok 0
#eval NumConfig.java32.neg (-2147483648)          -- ok (-2147483648)

-- The measured JS bug (research.md / docs/languages.md), now fixed and checked at build
-- time rather than only in a fixture whose export shape may or may not exercise it:
-- Node reports `2147483647 + 1 === 2147483648`. Under the OLD `.cLike`-routed dialect
-- this wrapped to -2147483648, same as `NumConfig.c32Wrapv` above -- a confirmed wrong
-- answer. `Dialect.javascript.toNumConfig` is `NumConfig.python` (unbounded), so it now
-- agrees with Node exactly, up to `Number.MAX_SAFE_INTEGER`.
#eval Dialect.javascript.toNumConfig.add 2147483647 1   -- ok 2147483648  (matches Node)
#eval Dialect.javascript.toNumConfig.mul 100000 100000  -- ok 10000000000 (matches Node)

-- INT_MIN / -1.
#eval NumConfig.c32.div (-2147483648) (-1)        -- ub "signed integer overflow"
#eval NumConfig.java32.div (-2147483648) (-1)     -- ok (-2147483648)
#eval NumConfig.go64.div (-9223372036854775808) (-1)  -- trap
#eval NumConfig.c32.div 1 0                       -- divZero
#eval NumConfig.c32.mod (-2147483648) (-1)        -- ub
#eval NumConfig.java32.mod (-2147483648) (-1)     -- ok 0

-- Division rounding: the §12 dialect bug.
#eval NumConfig.python.div 6 (-9)                 -- ok (-1)
#eval NumConfig.c32.div 6 (-9)                    -- ok 0
#eval NumConfig.python.mod 6 (-9)                 -- ok (-3)   (matches CPython)
#eval NumConfig.c32.mod 6 (-9)                    -- ok 6      (matches cc)

-- Shifts.
#eval NumConfig.java32.shl 1 31                   -- ok (-2147483648)
#eval NumConfig.c32.shl 1 31                      -- ub (loses the sign bit)
#eval NumConfig.c32.shl 1 32                      -- ub "shift count out of range"
#eval NumConfig.java32.shl 1 32                   -- ok 1 (count masked to 0)
#eval NumConfig.python.shl 1 40                   -- ok 1099511627776
#eval NumConfig.python.shl 1 (-1)                 -- trap "negative shift count"
#eval NumConfig.java32.shr (-8) 1                 -- ok (-4)   arithmetic
#eval ({ NumConfig.java32 with negRightShift := .logical } : NumConfig).shr (-8) 1
                                                  -- ok 2147483644  (Java >>>)

-- Bitwise, including negatives.
#eval NumConfig.python.band (-1) 12               -- ok 12
#eval NumConfig.python.bxor (-1) 0                -- ok (-1)
#eval NumConfig.python.bor (-8) 3                 -- ok (-5)
#eval NumConfig.c32.band (-1) 255                 -- ok 255
#eval NumConfig.u32.bnot 0                        -- ok 4294967295
#eval NumConfig.c32.bnot 0                        -- ok (-1)

-- Casts.
#eval NumConfig.c32.cast 4294967296               -- 0
#eval ({ type := .signed .w8 } : NumConfig).cast 200   -- -56
#eval ({ type := .unsigned .w8 } : NumConfig).cast (-1) -- 255

end Evidence


/-! ## Languages, and the approximation each one is currently under

`Dialect` originally had two constructors, and §29 recorded that two were not enough:
Java, Go and JavaScript were all run as `.cLike`, which is right about `and`/`or` for
Java and Go and **wrong** for JavaScript, where `0 || 5` is `5`. Collapsing them was
invisible because nothing in the build ever named a language.

`Lang` names it. `javascript`/`typescript` now route to the real `Dialect.javascript`
(see `Syntax.lean`) instead of `.cLike`, which fixes the measured `&&`/`||` and integer-
overflow bugs; `Lang.approximated` still marks them `true` because the bitwise/shift-op
gap documented on `Dialect` itself remains open. Java and Go stay on `.cLike`, which is
still the correct call for their boolean operators.

Why constructor-per-language for the *other* under-provisioned languages (Java, Go) is
still additive rather than done: about 110 sites still `match` on `Dialect` directly, so
adding a constructor makes every one of them non-exhaustive at once — which is exactly
what happened, and was worked through, when `javascript` was added. `java`/`go`
constructors are the same shape of work, not yet done. -/
inductive Lang where
  | python | c | java | go | javascript | typescript | kotlin
  deriving Repr, Inhabited, DecidableEq

namespace Lang

/-- File extensions Joern's front ends produce for each language. `render_lean.py`'s
`infer_dialect` refuses on an unknown extension rather than defaulting to Python; this is
the table it should be refusing against. -/
def extensions : Lang → List String
  | .python     => [".py"]
  | .c          => [".c", ".h", ".cpp", ".hpp", ".cc"]
  | .java       => [".java"]
  | .go         => [".go"]
  | .javascript => [".js", ".mjs", ".cjs"]
  | .typescript => [".ts", ".tsx"]
  | .kotlin     => [".kt", ".kts"]

/-- The dialect this language is evaluated under **today**. Several of these are
approximations; `approximated` says which. -/
def dialect : Lang → Dialect
  | .python     => .python
  -- Correct for `and`/`or`: Java and Go really do yield a bool. No constructor of their
  -- own yet (see the module doc comment above), so they stay on `.cLike`.
  | .java | .go | .c => .cLike
  -- `.javascript` is a real constructor now (Syntax.lean): `&&`/`||` yield an operand
  -- and arithmetic no longer wraps at 32 bits. TypeScript shares it — type erasure means
  -- TS's runtime numeric/boolean/string behaviour is JS's.
  | .javascript | .typescript => .javascript
  -- Kotlin's `&&`/`||` are bool-valued, like Java's.
  | .kotlin     => .cLike

/-- Does this language's real behaviour disagree with the dialect it is run under, in a
way the semantics can currently express? Each `true` is a known-wrong answer, not an
unknown one. JS/TS's `&&`/`||`/overflow bugs are fixed by `.javascript`; `true` here now
tracks the *narrower*, still-open gap: real JS truncates bitwise/shift operands to
Int32, and `.javascript`'s one `NumConfig` (unbounded, chosen to fix arithmetic) does not
model that separately — see `Dialect`'s doc comment in `Syntax.lean`. -/
def approximated : Lang → Bool
  | .javascript | .typescript => true   -- bitwise/shift ops still truncate wrong
  | _ => false

/-- The integer model. `java64` and `go64` were written months ago and never wired to
anything, because nothing named a language. -/
def numConfig : Lang → NumConfig
  | .python                   => NumConfig.python
  | .c                        => NumConfig.c32
  | .java | .kotlin           => NumConfig.java64
  | .go                       => NumConfig.go64
  -- JS/TS numbers are IEEE doubles, not integers at all; `.javascript`'s `NumConfig` is
  -- `NumConfig.python` (unbounded) — exact up to `Number.MAX_SAFE_INTEGER`, a named
  -- approximation beyond it and for bitwise/shift ops. See `Dialect.toNumConfig`.
  | .javascript | .typescript => Dialect.javascript.toNumConfig

/-- Languages whose semantics are currently known to be wrong. -/
def known_wrong : List Lang :=
  [.python, .c, .java, .go, .javascript, .typescript, .kotlin].filter approximated

end Lang

end Autoform.Core
