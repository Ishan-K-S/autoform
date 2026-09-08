import Specimen
import Autoform.Lang.Core.Float

/-!
# Core — a universal deep-embedded imperative language

`Imp` proved the harness works. `Core` is the real target: it is deliberately shaped to
match **Joern's code property graph node vocabulary**, which already normalizes
C/C++/Java/JavaScript/Python/Kotlin/binaries into a single AST schema.

That is the trick for "arbitrary codebase". We do not write one transpiler per language;
we write one semantics for the CPG core and one CPG→Lean exporter, and every
Joern-supported front end comes along for free.

The price is honesty about coverage, which is why holes are first class:

* `Expr.hole` — an unmapped expression, tagged with the CPG node label that produced it.
* `Stmt.hole` — an unmapped statement, likewise.

Nothing is ever silently dropped. The ledger counts holes, and a program with holes
cannot be proved to do anything at the hole. That is the point, not a limitation.
-/

namespace Autoform.Core

/-- Source-language dialect.

**Two constructors were not enough** and this was known (STRATEGY.md §29): six languages
have been run through the pipeline and they disagree on integer width, string semantics,
boolean-operator semantics, and equality. `cLike` used to mean "32-bit truncating C" and
was applied to Java, Go, JavaScript and TypeScript, which are none of those things.
`javascript` is the first constructor added past the original two — for JS/TS
specifically, not for Java/Go, which really do agree with `cLike` on `&&`/`||`
(`Lang.dialect` still routes them there).

**What `javascript` fixes, because it was measured wrong (`docs/languages.md`):**
`&&`/`||` now yield an **operand**, not a coerced boolean (`0 || 5` is `5`, not `true`) —
`boolOpsAreValues := true`, like Python. Arithmetic now uses unbounded integers instead
of 32-bit two's-complement wraparound — `toNumConfig .javascript = NumConfig.python` —
which is the specific fix for the measured bug `2147483647 + 1`: Node reports
`2147483648`, the old `.cLike`-routed Core reported `-2147483648` (wrapped), and unbounded
arithmetic now agrees with Node up to `Number.MAX_SAFE_INTEGER` (2^53 - 1).

**What `javascript` does NOT fix, named rather than hidden:** real JS numbers are IEEE
doubles, and this project's `Val` has no single "JS number" representation that is
sometimes-int-sometimes-float the way `Number` is — `NumConfig.python`'s *unbounded*
integers are themselves a known-wrong approximation past 2^53 (Numeric.lean already
recorded this before this dialect existed). Bitwise/shift operators (`&`, `|`, `^`, `<<`,
`>>`, `>>>`) go through the same `NumConfig`, but real JS converts their operands to
Int32 first (ECMA `ToInt32`) — a genuinely different width policy from JS's own
arithmetic operators. Modelling that correctly needs a *second* numeric config per
dialect (one for arithmetic, one for bitwise), which `Dialect.toNumConfig`'s
one-config-per-dialect shape does not support yet; until it does, `<<`/`>>`/bitwise ops
on `.javascript` inherit the unbounded config and are a known, recorded gap, not a
claimed fix. `Lang.approximated` still marks JavaScript/TypeScript `true` for this
reason. -/
inductive Dialect where
  | python
  | cLike
  | javascript
  deriving Repr, Inhabited, DecidableEq

namespace Dialect

/-- Do `and`/`or` evaluate to one of their **operands** (Python, JavaScript) rather than
to a boolean (C, Java, Go)? `0 and 5` is `0` in Python and `1` in C. -/
def boolOpsAreValues : Dialect → Bool
  | .python     => true
  | .cLike      => false
  | .javascript => true

/-- Are strings **values** with content equality and concatenation (Python, Java, Go,
JavaScript), or pointers with address semantics (C)? Under pointer semantics `+`, `<`,
`>` and `==` on strings are holes rather than the content operations. -/
def stringsAreValues : Dialect → Bool
  | .python     => true
  | .cLike      => false
  | .javascript => true

/-- Is `e.f` on a **dict** value a member selection?

A C aggregate initializer — `static struct crypto_alg alg = { .cra_name = "842", .
cra_priority = 100 }` — is a finite map from field names to values, which is exactly
`Val.dict` with string keys, and C struct assignment copies, so value semantics is the
right semantics for it. Under a C-family dialect `alg.cra_priority` therefore reads the
key `"cra_priority"` out of that map.

Under Python it must **not**: `{'a': 1}.a` is an `AttributeError`, not `1`, and answering
`1` would be a silent wrong answer of the §12 kind. So `.python` says `false` and the
access stays the `field:a:non-object` hole it has always been.

JavaScript agrees with the C-family answer here, for a different reason: a JS object
literal's fields genuinely are accessible by dot notation (`({a: 1}).a === 1`), so
`.javascript` says `true`, like `.cLike`.

Note what this does *not* buy: a `dict` is not on the heap, so `e.f = v` on one is still
`setField:non-object`. A struct whose fields are written after initialization is a hole,
not a wrong answer. -/
def fieldsOnDicts : Dialect → Bool
  | .python     => false
  | .cLike      => true
  | .javascript => true

/-- Does comparing an integer against a float compare **exactly** (Python: `10**23 ==
1e23` is `False`), or promote the integer to a double first (C)? JavaScript has no
separate integer type at runtime — every `Number` is already a double — so there is no
"exact bignum vs. float" comparison to have; `.javascript` says `false`, matching the
promote-and-compare behaviour that is the closer model for a language with one numeric
type. -/
def comparesIntFloatExactly : Dialect → Bool
  | .python     => true
  | .cLike      => false
  | .javascript => false

end Dialect

/-- Float configuration implied by a `Core.Dialect`. `cLike` gets `cDouble`, matching what
the oracle measures on x86-64 (SSE2, `FLT_EVAL_METHOD = 0`); switch it to
`FConfig.cDoubleExcess` to *surface* excess-precision dependence instead of assuming it
away. As with `NumConfig`, the ledger must record which one a result was obtained under —
`1.0 / 0.0` is `ZeroDivisionError` under one and `inf` under the other. `javascript` also
gets `cDouble`: JS's `Number` *is* an IEEE binary64, the same format C's `double` uses on
this architecture. -/
def Dialect.toFConfig : Dialect → FConfig
  | .python     => FConfig.python
  | .cLike      => FConfig.cDouble
  | .javascript => FConfig.cDouble

/-- A heap address. Objects are boxed and mutable; everything else is a value. -/
abbrev Ref := Nat

/-- `006-reduce-remaining-holes`, Story 5: a position WITHIN a heap-boxed array or
struct -- an element index, or a field name. Two constructors rather than one unified
key type because pointer arithmetic (`applyBinop` below) is only ever defined, in
standard C, for the array/`.idx` case: a struct field's address has no `+`/`-` outside
an array-typed field, which stays a hole under `"iref:arith-on-field"` rather than
inventing a meaning C itself does not give. -/
inductive Sel where
  | idx : Int → Sel
  | fld : String → Sel
  deriving Repr, Inhabited, DecidableEq

namespace Sel

/-- The one bridge to `Heap.getField`/`setField`'s existing `String`-keyed lookup: an
array's elements are `Obj.fields` entries keyed by their decimal-string index, reusing
the exact association list `003`'s scalar boxes already use -- no `Heap`-level change
at all. -/
def key : Sel → String
  | .idx n => toString n
  | .fld f => f

end Sel

/-- Runtime values. A small universal core; anything richer becomes a hole. -/
inductive Val where
  | int   : Int → Val
  | str   : String → Val
  | bool  : Bool → Val
  /-- An IEEE 754 float, as a bit pattern plus its format (`Autoform/Lang/Core/Float.lean`).

  **`Val.beq` must not compare these structurally.** `Fl` derives `DecidableEq`, so
  `.float a == .float b` on the bit patterns is available and is *wrong* in both
  directions: NaN would equal itself and `-0.0` would differ from `+0.0`. Both are proved
  in `Float.lean` (`float_beq_is_not_bit_equality`, `float_bit_equality_is_not_beq`), and
  `Val.beq` below routes floats through `Fl.eqv` for exactly this reason. -/
  | float : Fl → Val
  | unit  : Val
  | list  : List Val → Val
  | tuple : List Val → Val
  /-- Association list, not a hash map: key order is observable and we do not want to
  silently impose one language's iteration order on another's. -/
  | dict  : List (Val × Val) → Val
  /-- A reference to a heap object. Reference identity is what `is` compares. -/
  | ref   : Ref → Val
  /-- `006-reduce-remaining-holes`, Story 5: an INTERIOR pointer -- a reference to a
  heap-boxed array/struct PLUS a position within it. The one genuinely new
  representational concept this project's whole history has needed: `Val.ref` alone
  can name an object, but cannot express "partway into" one. Not derived from `Val.ref`
  because a bare object reference and a positioned interior pointer must stay
  distinguishable to `applyBinop` below (only the latter has pointer arithmetic). -/
  | iref  : Ref → Sel → Val
  /-- A function or method used as a value (`METHOD_REF`), or a class (`TYPE_REF`). -/
  | fn    : String → Val
  /-- A class together with the bindings it captured, for classes defined inside a
  function whose methods read the enclosing scope. -/
  | clsClos : String → List (String × Val) → Val
  /-- A closure: a function together with the bindings it captured. Capture is **by
  value**, which is why `nonlocal` *writes* remain a hole — see `Semantics.lean`. -/
  | clos  : String → List (String × Val) → Val
  /-- An instance of a class whose base is a **builtin type**: `class X(tuple)`,
  `class X(list)`, `class X(dict)`, `class X(str)`. Carries the class name and the
  underlying builtin value.

  ## Why this shape, and not a payload on `Obj`

  The obvious cheaper alternative is `Obj.builtin : Option Val`, leaving the value a
  `Val.ref`. It does not work, and the reason is structural rather than a matter of
  taste: **`Val.beq`, `applyBinop`, `valIn` and `Val.truthy` do not take the heap.**
  They are pure functions of values, and they are exactly the functions that have to
  agree with the builtin. Making the `Obj` payload visible to them means threading a
  `Heap` through `Val.beq` — which is also the `BEq Val` instance, is used inside
  `Val.beqL`/`beqP`, inside `Stdlib`'s association-list helpers, and inside dozens of
  `Refine.lean` theorems. That is a far larger and more dangerous edit than adding a
  constructor, and it leaves `Val.beq` able to *fail* to consult the heap on any path —
  the silent-wrong failure mode this project keeps finding.

  So the payload lives in the value. There is exactly one copy of an instance's builtin
  state and no way for a value and a heap object to disagree about it.

  ## What this costs, stated plainly

  A `bobj` has **no mutable instance attributes**: it is not on the heap, so `e.f` on one
  is `field:f:non-object` and `e.f = v` is `setField:f:non-object` — holes, not wrong
  answers. `_HashedTuple.__hash__`'s memo field is therefore a hole. Classes with a
  builtin base that define `__init__` or `__eq__` are refused at construction
  (`alloc:builtin-base:...`) rather than silently ignoring them.

  ## What could still silently go wrong

  1. `Val.beq` now compares two `bobj`s, and a `bobj` against a plain builtin, by
     **contents, ignoring the class**. That is CPython's behaviour for `tuple`/`list`/
     `dict`/`str` subclasses that do not override `__eq__` (measured: `A((0,)) ==
     B((0,))` is `True`), and the `__eq__` check at construction is what keeps it true.
     If a future exporter records a builtin base for a class whose `__eq__` it could not
     see, equality would be wrong and nothing here would catch it.
  2. Mutation of a `list`/`dict` base is value-semantics, exactly as Core's own
     containers already are (`setIndex` is `setIndex:immutable-containers`). A `bobj`
     inherits that known unsoundness rather than adding a new one — see
     `docs/boxed-containers.md`.
  3. Any `match` on `Val` with a catch-all that predates this constructor will treat a
     `bobj` as "some other value". Every such site in `Semantics.lean` and `Stdlib.lean`
     was audited; a site added later will not be. -/
  | bobj  : String → Val → Val
  deriving Repr, Inhabited

/-- The builtin types a user class may inherit from and still be modelled.

Deliberately not `Exception` (Core represents exceptions as bare `Val.str` class names,
so an exception subclass has nowhere to put its payload), not `object` (that is an
ordinary class and already works), and not multiple bases. -/
inductive BuiltinBase where
  | tuple
  | list
  | dict
  | str
  deriving Repr, Inhabited, DecidableEq

namespace BuiltinBase

/-- The empty instance of the base, used when the constructor is called with no
argument: `tuple()` is `()`, `str()` is `""`. -/
def empty : BuiltinBase → Val
  | .tuple => .tuple []
  | .list  => .list []
  | .dict  => .dict []
  | .str   => .str ""

/-- The builtin type name, for `isinstance`. -/
def typeName : BuiltinBase → String
  | .tuple => "tuple"
  | .list  => "list"
  | .dict  => "dict"
  | .str   => "str"

end BuiltinBase

/-- The mutable container payload an object carries, if any.

**Step 1 of `docs/boxed-containers.md`, and deliberately inert.** Nothing constructs a
payload other than `.none` yet, so no behaviour changes and no corpus needs regeneration.
The point of landing it separately is that the oracle numbers move at step 3, and a number
that moves two steps after the field appeared cannot be attributed to the field. -/
inductive Payload where
  /-- An ordinary instance: no builtin container behind it. -/
  | none  : Payload
  | list  : List Val → Payload
  | dict  : List (Val × Val) → Payload
  /-- `tuple` SUBCLASS instances only -- plain tuples stay values, see the doc's section 1. -/
  | tuple : List Val → Payload
  deriving Repr, Inhabited

/-- A heap object: its class and its mutable fields. -/
structure Obj where
  cls    : String
  fields : List (String × Val)
  /-- Bindings captured by the class that produced this object, if it was defined inside
  a function. Resolved after the object's own fields and before globals. -/
  captured : List (String × Val) := []
  /-- The builtin container this object IS, if it is one. `.none` for every object Core
  currently builds. -/
  payload  : Payload := .none
  /-- Bumped by every mutation. Iterators record it, so that a change during iteration can
  become CPython's `RuntimeError` rather than a silently different answer. Inert until
  step 4. -/
  version  : Nat := 0
  deriving Repr, Inhabited

/-- The heap. Index into the list is the `Ref`; allocation appends. -/
abbrev Heap := List Obj

namespace Heap

/-- Dereference. -/
def get (h : Heap) (r : Ref) : Option Obj := h[r]?

/-- Allocate, returning the new heap and the fresh reference. -/
def alloc (h : Heap) (o : Obj) : Heap × Ref := (h ++ [o], h.length)

/-- Read a field, `unit` if absent. -/
def getField (h : Heap) (r : Ref) (f : String) : Val :=
  match h.get r with
  | none   => .unit
  | some o => match o.fields.find? (·.1 == f) with
              | some (_, v) => v
              | none        => .unit

/-- Write a field, shadowing any previous binding. -/
def setField (h : Heap) (r : Ref) (f : String) (v : Val) : Heap :=
  h.mapIdx fun i o => if i == r then { o with fields := (f, v) :: o.fields } else o

/-- Read an object's container payload. `.none` for a dangling reference, which is the same
answer as for an ordinary instance -- the caller must already have established the
reference is live, exactly as `getField` requires. -/
def payload (h : Heap) (r : Ref) : Payload :=
  match h.get r with
  | none   => .none
  | some o => o.payload

/-- Replace an object's container payload and BUMP ITS VERSION. The two always move
together: a payload write that left the version alone would be invisible to an iterator,
which is the silent-wrong failure this field exists to prevent. -/
def setPayload (h : Heap) (r : Ref) (p : Payload) : Heap :=
  h.mapIdx fun i o =>
    if i == r then { o with payload := p, version := o.version + 1 } else o

end Heap

/-- Literals as they appear in source. -/
inductive Lit where
  | int   : Int → Lit
  | str   : String → Lit
  | bool  : Bool → Lit
  /-- A float literal. The transpiler should emit the *bit pattern*
  (`Fl.ofBits 4591870180066957722` for `0.1`), not decimal text: `Format.ofDecimal` can
  correctly round a decimal literal, but going back out to decimal is not modelled, so
  bits are the only spelling that round-trips through the differential harness. -/
  | float : Fl → Lit
  | unit  : Lit
  deriving Repr, Inhabited, DecidableEq

/-- Expressions. `call` is by name: the CPG gives us resolved callee names. -/
inductive Expr where
  | lit    : Lit → Expr
  | name   : String → Expr
  | binop  : String → Expr → Expr → Expr
  | unop   : String → Expr → Expr
  | call   : String → List Expr → Expr
  | index  : Expr → Expr → Expr
  /-- Attribute access: `e.f`. -/
  | field  : Expr → String → Expr
  /-- Method call on a receiver: `e.m(args)`. Dispatch is on the receiver's class. -/
  | mcall  : Expr → String → List Expr → Expr
  /-- Object construction: `Cls(args)`, running `Cls.__init__` if one is known. -/
  | alloc  : String → List Expr → Expr
  /-- A function, method or class used as a value (`METHOD_REF` / `TYPE_REF`). -/
  | fnref  : String → Expr
  /-- A function value that captures the enclosing scope: decorators, factories, and
  nested functions that read outer variables. -/
  | closure : String → Expr
  /-- A *class* value that captures the enclosing scope. Distinct from `closure` because
  a class is not a function: its methods, not it, read the captured bindings. -/
  | classClosure : String → Expr
  | listE  : List Expr → Expr
  | tupleE : List Expr → Expr
  | dictE  : List (Expr × Expr) → Expr
  /-- Conditional expression `t if c else e`. -/
  | cond   : Expr → Expr → Expr → Expr
  /-- Reference identity. `true` means negated (`is not`). -/
  | isOp   : Bool → Expr → Expr → Expr
  /-- Membership. `true` means negated (`not in`). -/
  | inOp   : Bool → Expr → Expr → Expr
  -- ### Argument forms
  --
  -- Python's calling convention needs three argument *shapes* that a fixed positional
  -- list cannot express. They are added as `Expr` constructors rather than by changing
  -- `call`'s argument type, because replacing `List Expr` with a new `Arg` type makes
  -- every one of the ~110 existing `Expr` matches non-exhaustive at once, while three new
  -- leaf constructors only disturb the handful of matches that are exhaustive.
  --
  -- They are only meaningful directly inside a call's argument list. `evalList` -- the
  -- one place an argument list is evaluated -- dispatches on them; `evalExpr` reached on
  -- one of them anywhere else yields the hole `op:starred-outside-call`, which is an
  -- honest admission rather than a silently wrong value.
  /-- `*e` in an argument list: splice the elements of an iterable into the positional
  arguments. A non-iterable operand raises `TypeError`, as in CPython. -/
  | starred : Expr → Expr
  /-- `k = e` in an argument list: one keyword argument. Before this existed the exporter
  dropped such arguments **silently** — `_wrapper(..., info = make_info)` translated to a
  call that simply did not pass `info`. -/
  | kwargE  : String → Expr → Expr
  /-- `**e` in an argument list: splice a `dict` into the keyword arguments. Non-`dict`
  operands, and `dict`s with non-string keys, raise `TypeError`, as in CPython. -/
  | dstarred : Expr → Expr
  /-- Unmapped expression, tagged with the originating CPG node label. -/
  | hole   : String → Expr
  /-- Unconditional heap allocation of a fresh single-field `Obj` -- `{cls :=
  "<local>", fields := [("v", value)]}` -- holding the evaluated argument, returning
  the resulting `Val.ref`. This is the ONE new primitive `003-box-address-taken-locals`
  needs (`research.md` item 2): boxing an address-taken local reuses `Expr.field`/
  `Stmt.setField` as-is for reads/writes of the box, but allocation has no existing
  counterpart. `Expr.alloc` is the wrong tool for it -- `Expr.alloc`'s documented
  semantics is "run `Cls.__init__` if one is known" for a NAMED class, which is either
  undefined behaviour or an accidental fallback for a synthetic box that has no class
  and no constructor. `Expr.boxNew` is unconditional and constructor-free: it always
  allocates, exactly once, with exactly one field. -/
  | boxNew : Expr → Expr
  /-- `006-reduce-remaining-holes`, Story 5: `Expr.boxNew` generalised from exactly one
  field (`"v"`) to N -- allocates a fresh, multi-field `Obj` from a list of (key,
  initial-value) pairs, evaluated left-to-right, returning the resulting `Val.ref`. The
  producer is the unconditional per-function allocation prologue for every array/struct
  local Story 5's own scope boundary admits: an array's elements become fields keyed by
  their decimal-string index (`"0"`, `"1"`, ...), a struct's members become fields keyed
  by their real member names.

  The key of each pair is an `Expr` (always a string LITERAL, in every site this project
  emits), not a bare `String`, DELIBERATELY: it lets evaluation reuse `evalPairs` --
  already proven fuel-monotone as part of `Expr.dictE`'s own machinery -- verbatim,
  rather than a second, parallel list-evaluator needing its own proof. Any key that does
  not evaluate to a `Val.str` is a hole, never reached by anything the exporter emits. -/
  | boxFields : List (Expr × Expr) → Expr
  /-- `010-reach-90pct-hole-free`: allocation of a fresh `Obj` whose FIELD COUNT is a
  RUNTIME value, not a list of `(key, value)` pairs the exporter writes out one at a
  time. `Expr.boxFields`' own list is a SYNTACTIC term embedded in the generated Lean
  source -- its length is fixed at EXPORT time, which is exactly why a large
  compile-time-sized array (SQLite's own I/O buffers run 512-8,192 elements) blows
  the elaborator's recursion depth or exhausts memory (`research.md` §3, spec 010's
  own Day-1 finding): the SOURCE FILE itself contains one nested list cell per
  element.

  `Expr.boxArray` sidesteps this by construction: it takes a single length
  EXPRESSION, evaluates it ONCE at runtime to a `Val.int`, and the resulting `Obj`'s
  fields (`"0" ↦ .unit, "1" ↦ .unit, ..., "n-1" ↦ .unit`, `List.range` under the
  hood) are built by an ordinary, already-compiled Lean function operating on
  whatever `Nat` the interpreter computes THEN -- no per-element syntax, so no
  elaboration-time cost that scales with the array's size at all, compile-time-known
  or not. This is what makes it usable for `malloc(len)`-shaped C allocations, whose
  size the exporter can never know until the program runs: `zOut = malloc(n);` seeds
  `zOut` as `Val.ref` to a fresh `n`-field `Obj`, `Val.iref` (`Sel.idx`, already
  generic over the position) then walks and reads/writes it exactly like any other
  boxed array -- `irefIndex`/`derefIref`/`setDerefIref`/pointer arithmetic on
  `Val.iref` need no change at all, only a new way to OBTAIN a valid ref to something
  shaped like one. Every field starts `.unit`, matching every other uninitialized
  boxed local/array's own convention -- sound because the only real corpus idiom this
  targets (`malloc` a buffer, walk it with a pointer, write every byte before ever
  reading one back) never observes a field's `.unit` starting value at all. -/
  | boxArray : Expr → Expr
  /-- `006-reduce-remaining-holes`, Story 5: `&a[i]` once `a` is a boxed array --
  evaluates the receiver to `Val.ref r`, evaluates the index, and produces
  `Val.iref r (.idx i)`. Takes a full sub-`Expr` for the index (not a literal), since
  most real `&a[i]` sites have a runtime-valued `i`. The address-of counterpart to
  `Expr.index` (a whole-VALUE read); does not replace it. -/
  | irefIndex : Expr → Expr → Expr
  /-- `006-reduce-remaining-holes`, Story 5: `&s.f` once `s` is a boxed struct --
  evaluates the receiver to `Val.ref r`, produces `Val.iref r (.fld f)`. The
  address-of counterpart to `Expr.field` (a whole-VALUE read); does not replace it. -/
  | irefField : Expr → String → Expr
  /-- `006-reduce-remaining-holes`, Story 5: `*p` where `p` is an interior-pointer
  VALUE (as opposed to `Expr.field`, which takes an explicit field name for a NAMED
  receiver). Requires its operand to evaluate to `Val.iref r sel` and delegates,
  unconditionally, to the unchanged `Heap.getField h r sel.key` -- no `Heap`-level
  change at all. -/
  | derefIref : Expr → Expr
  /-- `009-reduce-remaining-holes-4`: read the byte at position `b` of the string `a`,
  as an integer -- C's `*p`/`p[i]` on a `char*` walked as a byte cursor, which is
  fundamentally NOT `Expr.index`'s existing meaning. `Expr.index` on a `.str` receiver
  has no case in `evalExpr` at all today (confirmed by reading it directly): Python's
  own `s[i]` returns a length-1 `Val.str` (matching CPython), but C's `*p` needs an
  INTEGER byte value comparable via arithmetic (`*z == '"'`, `*z - '0'`) -- the two
  languages want different return types from the identical `a[b]` syntax, so one
  semantics cannot honestly serve both. Giving `Expr.index` a `.str` case that returns
  an integer would silently mistranslate the (currently unsupported, so not yet relied
  on by anything) Python shape; a separate constructor, emitted ONLY by the C-family
  exporter path, keeps that choice explicit rather than baked into a single shared
  node's semantics.

  `Val.beq`/`applyBinop`/every existing `Val` match are untouched: the OPERAND and
  RESULT are ordinary `Val.str`/`Val.int` values already known throughout Core, this
  only adds one more way to produce an `Int` from a `Val.str`'s own content. Reads at
  the string's own length (one past its last real character) yield `0`, matching C's
  own implicit null terminator that a `Val.str` does not literally store; any other
  out-of-range index is a hole, not a guessed value, since indexing past a C string's
  terminator is undefined behaviour with no single well-defined answer to encode.
  Indexes by Lean `String` codepoint, not raw UTF-8 byte -- identical for the ASCII
  content this project's own string literals are built from, and stated here rather
  than silently assumed. -/
  | strByte : Expr → Expr → Expr
  /-- `009-reduce-remaining-holes-4`: the substring of `a` starting at position `b`,
  through its end -- Python's own `s[i:]`, and the value a C byte-cursor `char *z`
  (`Expr.strByte`, just above) has to produce when it is passed WHOLE to another
  function partway through being walked (`parseHhMmSs(zDate, p)` after `zDate` has
  already advanced past the date portion -- SQLite's own dominant real shape for a
  walked cursor, confirmed live: the great majority of `const char *` cursor
  parameters are passed onward to a sub-parser at least once). Clamped like Lean's
  own `List.drop`: a negative start is a hole (the exporter never has a genuine
  reason to produce one -- a cursor only ever advances forward), but a start past
  the string's own length is simply the empty string, exactly as `"abc"[10:]` is
  `""` in Python and `s.drop 999` is `[]` in Lean -- no undefined behaviour to
  guard against on that side, unlike `strByte`'s own out-of-range READ. -/
  | strFrom : Expr → Expr → Expr
  deriving Repr, Inhabited

/-- Statements. -/
inductive Stmt where
  | skip     : Stmt
  | expr     : Expr → Stmt
  | assign   : String → Expr → Stmt
  /-- `e.f = v` -/
  | setField : Expr → String → Expr → Stmt
  /-- `e[i] = v` -/
  | setIndex : Expr → Expr → Expr → Stmt
  /-- `006-reduce-remaining-holes`, Story 5: `*p = v` where `p` is an interior-pointer
  VALUE (as opposed to `Stmt.setField`, which takes an explicit field name for a NAMED
  receiver). Requires its pointer operand to evaluate to `Val.iref r sel` and
  delegates, unconditionally, to the unchanged `Heap.setField h r sel.key v`. -/
  | setDerefIref : Expr → Expr → Stmt
  | seq      : Stmt → Stmt → Stmt
  | ifte     : Expr → Stmt → Stmt → Stmt
  | loop     : Expr → Stmt → Stmt
  /-- `007-reduce-remaining-holes-2` US4: absorbs a `break` from its inner statement
  without absorbing a `continue` -- the one thing `Stmt.loop`/`Stmt.forIn` do NOT
  provide on their own, since both of those catch `.cont` too (re-entering the loop),
  which is correct for a loop but wrong for a `switch`: a `continue` written directly
  in a `switch` case body (no loop of its own between it and an enclosing loop) must
  keep propagating past the switch to that enclosing loop, unchanged. `switch` lowers
  to a `Stmt.ifte` dispatch chain wrapped in this constructor, so a `break` inside a
  case body ends only the switch's own dispatch, never an enclosing loop. See
  `execStmt`'s case for the exact semantics. -/
  | breakBlock : Stmt → Stmt
  /-- `for x in e: body` -/
  | forIn    : String → Expr → Stmt → Stmt
  | ret      : Expr → Stmt
  | brk      : Stmt
  | cont     : Stmt
  /-- `try: body except as x: handler`. Catches exceptions only — `ret`/`brk`/`cont`
  pass straight through, or every `try/except` containing a `return` would break. -/
  | tryCatch : Stmt → String → Stmt → Stmt
  /-- `try: body finally: fin`. The finalizer runs on **every** exit path, and an
  abnormal exit from the finalizer discards the pending outcome of the body — Python's
  rule, so `try: return 1 finally: return 2` returns 2. -/
  | tryFinally : Stmt → Stmt → Stmt
  | raise    : Expr → Stmt
  /-- `del x` -/
  | del      : String → Stmt
  /-- Write a module-level binding: `x = e` at module scope, or under `global x`. -/
  | setGlobal   : String → Expr → Stmt
  /-- `global x` — subsequent assignments to `x` in this function target module scope. -/
  | declGlobal  : String → Stmt
  /-- Unmapped statement, tagged with the originating CPG node label. -/
  | hole     : String → Stmt
  deriving Repr, Inhabited

/-- A function: name, parameters, body.

`params` lists **every** parameter name in source order, including the variadic ones.
`vararg` and `kwarg` say which of those names — if any — are `*args` and `**kwargs`; they
are `Option`al fields with `none` defaults, so every existing `Func` literal and every
already-rendered corpus keeps its meaning unchanged. See `bindParams` in `Semantics.lean`
for the binding rule. -/
structure Func where
  name   : String
  params : List String
  body   : Stmt
  /-- The `*args` parameter's name, if the function has one. -/
  vararg : Option String := none
  /-- The `**kwargs` parameter's name, if the function has one. -/
  kwarg  : Option String := none
  deriving Repr, Inhabited

/-- Whether this `Func` is a method, by the exporter's naming convention: the segment after
`<module>.` is `Class.method` rather than a bare function name. Used to recover Python's
unbound-method rule, where a method reached as a plain value takes its receiver as the
first positional argument. -/
def Func.isMethod (fn : Func) : Bool :=
  match fn.name.splitOn "<module>." with
  | [_, rest] => rest.any (· == '.')
  | _         => false

/-- A whole translated codebase, tagged with the dialect it came from. -/
structure Program where
  funcs   : List Func
  dialect : Dialect := .python
  /-- Classes whose (single) base is a builtin type, by the **short** class name that
  `Expr.alloc` uses. Empty by default, so a program translated before the exporter
  learned to record bases behaves exactly as it did: opaque `Val.ref` instances.

  Keyed by short name because that is what the CPG gives the allocation site. A corpus
  with two same-named classes in different modules and *different* bases cannot be
  represented; the exporter drops such a name entirely rather than guessing, which
  degrades to the pre-existing opaque-reference behaviour. -/
  builtinBases : List (String × BuiltinBase) := []
  deriving Repr, Inhabited

namespace Expr

/-- Is this an ordinary argument — one that contributes exactly one positional value —
rather than one of the three starred forms? Used as the side condition on the reasoning
lemmas about argument lists. -/
def plainArg : Expr → Bool
  | .starred _  => false
  | .kwargE _ _ => false
  | .dstarred _ => false
  | _           => true

/-!
Nested inductives (`List Expr`, `List (Expr × Expr)`) need explicit list helpers for
Lean to see the recursion as structural — `List.flatMap` hides it.
-/
mutual
/-- Holes in an expression, by label. -/
def holes : Expr → List String
  | .hole l       => [l]
  | .binop _ a b  => holes a ++ holes b
  | .unop _ a     => holes a
  | .index a b    => holes a ++ holes b
  | .field a _    => holes a
  | .call _ as    => holesL as
  | .mcall r _ as => holes r ++ holesL as
  | .alloc _ as   => holesL as
  | .listE as     => holesL as
  | .tupleE as    => holesL as
  | .dictE kvs    => holesP kvs
  | .cond c a b   => holes c ++ holes a ++ holes b
  | .isOp _ a b   => holes a ++ holes b
  | .inOp _ a b   => holes a ++ holes b
  | .starred a    => holes a
  | .kwargE _ a   => holes a
  | .dstarred a   => holes a
  | .boxNew a     => holes a
  | .boxFields kvs => holesP kvs
  | .boxArray n    => holes n
  | .irefIndex a i => holes a ++ holes i
  | .irefField a _ => holes a
  | .derefIref a   => holes a
  | _             => []

/-- Holes across a list of expressions. -/
def holesL : List Expr → List String
  | []      => []
  | e :: es => holes e ++ holesL es

/-- Holes across a list of key/value expression pairs. -/
def holesP : List (Expr × Expr) → List String
  | []           => []
  | (k, v) :: ps => holes k ++ holes v ++ holesP ps
end

mutual
/-- Total node count, for coverage arithmetic. -/
def size : Expr → Nat
  | .binop _ a b  => 1 + size a + size b
  | .unop _ a     => 1 + size a
  | .index a b    => 1 + size a + size b
  | .field a _    => 1 + size a
  | .call _ as    => 1 + sizeL as
  | .mcall r _ as => 1 + size r + sizeL as
  | .alloc _ as   => 1 + sizeL as
  | .listE as     => 1 + sizeL as
  | .tupleE as    => 1 + sizeL as
  | .dictE kvs    => 1 + sizeP kvs
  | .cond c a b   => 1 + size c + size a + size b
  | .isOp _ a b   => 1 + size a + size b
  | .inOp _ a b   => 1 + size a + size b
  | .starred a    => 1 + size a
  | .kwargE _ a   => 1 + size a
  | .dstarred a   => 1 + size a
  | .boxNew a     => 1 + size a
  | .boxFields kvs => 1 + sizeP kvs
  | .boxArray n    => 1 + size n
  | .irefIndex a i => 1 + size a + size i
  | .irefField a _ => 1 + size a
  | .derefIref a   => 1 + size a
  | _             => 1

/-- Node count across a list of expressions. -/
def sizeL : List Expr → Nat
  | []      => 0
  | e :: es => size e + sizeL es

/-- Node count across a list of key/value expression pairs. -/
def sizeP : List (Expr × Expr) → Nat
  | []           => 0
  | (k, v) :: ps => size k + size v + sizeP ps
end

end Expr

namespace Stmt

/-- Holes in a statement, by label. -/
def holes : Stmt → List String
  | .hole l          => [l]
  | .expr e          => e.holes
  | .assign _ e      => e.holes
  | .setField r _ v  => r.holes ++ v.holes
  | .setIndex r i v  => r.holes ++ i.holes ++ v.holes
  | .setDerefIref p v => p.holes ++ v.holes
  | .seq a b         => a.holes ++ b.holes
  | .ifte c a b      => c.holes ++ a.holes ++ b.holes
  | .loop c a        => c.holes ++ a.holes
  | .breakBlock a    => a.holes
  | .forIn _ e b     => e.holes ++ b.holes
  | .ret e           => e.holes
  | .tryCatch b _ h  => b.holes ++ h.holes
  | .tryFinally b f  => b.holes ++ f.holes
  | .raise e         => e.holes
  | .setGlobal _ e   => e.holes
  | _                => []

/-- Total node count. -/
def size : Stmt → Nat
  | .expr e          => 1 + e.size
  | .assign _ e      => 1 + e.size
  | .setField r _ v  => 1 + r.size + v.size
  | .setIndex r i v  => 1 + r.size + i.size + v.size
  | .setDerefIref p v => 1 + p.size + v.size
  | .seq a b         => a.size + b.size
  | .ifte c a b      => 1 + c.size + a.size + b.size
  | .loop c a        => 1 + c.size + a.size
  | .breakBlock a    => 1 + a.size
  | .forIn _ e b     => 1 + e.size + b.size
  | .ret e           => 1 + e.size
  | .tryCatch b _ h  => 1 + b.size + h.size
  | .tryFinally b f  => 1 + b.size + f.size
  | .raise e         => 1 + e.size
  | .setGlobal _ e   => 1 + e.size
  | _                => 1

end Stmt

namespace Func
/-- Holes in a function. -/
def holes (f : Func) : List String := f.body.holes
/-- Node count of a function. -/
def size (f : Func) : Nat := f.body.size
/-- A function is *fully translated* when it contains no holes. Only these are
candidates for unconditional verification. -/
def total (f : Func) : Bool := f.holes.isEmpty
end Func

namespace Program
/-- Every hole in the program. -/
def holes (p : Program) : List String := p.funcs.flatMap Func.holes
/-- Total node count. -/
def size (p : Program) : Nat := (p.funcs.map Func.size).sum
/-- Functions with no holes — the verifiable core. -/
def verifiableCore (p : Program) : List Func := p.funcs.filter Func.total
end Program

/-!
Structural equality on values is written by hand: the nested `List`/`Prod` occurrences
block `deriving DecidableEq`.
-/
/-- Which CONSTRUCTOR a value is. Two values of different kinds are never the same object,
which is what makes most of `Val.identical` decidable. -/
def Val.kind : Val → Nat
  | .int _       => 0
  | .str _       => 1
  | .bool _      => 2
  | .float _     => 3
  | .unit        => 4
  | .list _      => 5
  | .tuple _     => 6
  | .dict _      => 7
  | .ref _       => 8
  | .fn _        => 9
  | .clos _ _    => 10
  | .clsClos _ _ => 11
  | .bobj _ _    => 12
  | .iref _ _    => 13

/-- Python `is` -- reference identity, as a PARTIAL function.

`none` means "Core cannot answer this", not "false". Two unboxed containers have no identity
to compare: `[1] is [1]` is `False` in CPython because two allocations happened, and `True`
under a structural comparison, and Core cannot tell which it is looking at until containers
are boxed (`docs/boxed-containers.md` step 3). `1 is 1` is `True` only because CPython
interns small integers -- a fact about the runtime, not the language.

Answering `none` makes those a hole, `is:unboxed-value-identity`. That REDUCES what Core
answers, and the project prefers it: the previous structural fallback was right for interned
ints and wrong for everything else, and being quietly wrong is the failure mode this codebase
keeps finding. -/
def Val.identical : Val → Val → Option Bool
  | .ref a, .ref b => some (a == b)
  | .unit,  .unit  => some true
  -- A NAMED function denotes one function object, so `f is g` is decidable on names.
  -- `Cache.__init__` needs exactly this: `self.getsizeof is not Cache.getsizeof` is how
  -- cachetools detects an overridden sizer, and `none` there would turn a working
  -- constructor into a hole.
  | .fn a,  .fn b  => some (a == b)
  -- `True`/`False`/`None` are singletons in CPython, so identity follows value.
  | .bool a, .bool b => some (a == b)
  -- Closures are NOT decidable the same way: two calls to one factory make two distinct
  -- objects sharing a name. Different names are still definitely different.
  | .clos a _,    .clos b _    => if a == b then none else some false
  | .clsClos a _, .clsClos b _ => if a == b then none else some false
  -- Different KINDS are never the same object. Same kind and not covered above -- two ints,
  -- two strings, two unboxed containers -- stays `none`, because the answer depends on
  -- interning and on allocation, neither of which Core can see until step 3.
  | x, y => if x.kind == y.kind then none else some false

/-! `Val.identical` is `rfl`-checkable, so these pin it cheaply. They are not vacuous: each
one dies under the corresponding mutation, which is what stops the relation drifting back
towards the structural guess it replaced. -/
section IdentityCharacterization

/-- The case `Cache.__init__` depends on: the same named function is the same object. -/
theorem identical_fn_same : Val.identical (.fn "f") (.fn "f") = some true := rfl
/-- ...and two different names are two different objects. -/
theorem identical_fn_diff : Val.identical (.fn "f") (.fn "g") = some false := rfl
/-- `None is None`. -/
theorem identical_unit : Val.identical .unit .unit = some true := rfl
/-- References compare by address, which is the whole point of the relation. -/
theorem identical_ref_same : Val.identical (.ref 3) (.ref 3) = some true := rfl
theorem identical_ref_diff : Val.identical (.ref 3) (.ref 4) = some false := rfl
/-- **Interning is not modelled**: `1 is 1` is not answered, rather than answered `true`.
This is the equation that distinguishes the new relation from the old fallback. -/
theorem identical_int_unknown : Val.identical (.int 1) (.int 1) = none := rfl
/-- Two unboxed containers likewise: CPython says `False` (two allocations), a structural
compare says `True`, and Core does not yet know which it is looking at. -/
theorem identical_list_unknown :
    Val.identical (.list [.int 1]) (.list [.int 1]) = none := rfl
/-- Different kinds are decidable even when neither kind is. -/
theorem identical_cross_kind : Val.identical (.int 1) (.fn "f") = some false := rfl
/-- `1 is True` is `False` in CPython. -/
theorem identical_int_bool : Val.identical (.int 1) (.bool true) = some false := rfl

end IdentityCharacterization


mutual
/-- Structural equality on values. -/
def Val.beq : Val → Val → Bool
  | .int a,   .int b   => a == b
  | .str a,   .str b   => a == b
  | .bool a,  .bool b  => a == b
  -- Floats compare by *value*, never by bit pattern: `nan != nan`, `+0.0 == -0.0`.
  | .float a, .float b => Fl.eqv a b
  -- Python's numeric tower: `1 == 1.0`, and `{1: 'a'}[1.0]` succeeds because the two also
  -- hash equal. The comparison is *exact* — `10**23 == 1e23` is `False` in CPython —
  -- which is why it goes through `Fl.cmpIntv` rather than converting either side.
  | .int a,   .float b => Fl.cmpIntv a b == some .eq
  | .float a, .int b   => Fl.cmpIntv b a == some .eq
  | .unit,    .unit    => true
  | .ref a,   .ref b   => a == b
  | .fn a,    .fn b    => a == b
  | .clos a _, .clos b _ => a == b
  | .clsClos a _, .clsClos b _ => a == b
  | .list a,  .list b  => Val.beqL a b
  | .tuple a, .tuple b => Val.beqL a b
  | .dict a,  .dict b  => Val.beqP a b
  -- Instances of builtin-based classes compare by **contents, ignoring the class**, and
  -- compare equal to the plain builtin. Measured against CPython 3.9.6:
  --   `A((0,)) == (0,)`  True      `A((0,)) == B((0,))`  True   (A, B both `(tuple)`)
  --   `A((0,)) == (1,)`  False     `A((0,)) == [0]`      False
  -- The twelve cases are written out rather than routed through an unwrapping helper so
  -- that every recursive call is on a *subterm of the first argument*: that is what keeps
  -- `Val.beq` structurally recursive, and hence reducible by `rfl`/`decide`, which the
  -- float equations below and much of `Refine.lean` depend on.
  | .bobj _ (.tuple a), .bobj _ (.tuple b) => Val.beqL a b
  | .bobj _ (.list a),  .bobj _ (.list b)  => Val.beqL a b
  | .bobj _ (.dict a),  .bobj _ (.dict b)  => Val.beqP a b
  | .bobj _ (.str a),   .bobj _ (.str b)   => a == b
  | .bobj _ (.tuple a), .tuple b => Val.beqL a b
  | .bobj _ (.list a),  .list b  => Val.beqL a b
  | .bobj _ (.dict a),  .dict b  => Val.beqP a b
  | .bobj _ (.str a),   .str b   => a == b
  | .tuple a, .bobj _ (.tuple b) => Val.beqL a b
  | .list a,  .bobj _ (.list b)  => Val.beqL a b
  | .dict a,  .bobj _ (.dict b)  => Val.beqP a b
  | .str a,   .bobj _ (.str b)   => a == b
  | _,        _        => false
/-- Structural equality on value lists. -/
def Val.beqL : List Val → List Val → Bool
  | [],      []      => true
  | a :: as, b :: bs => Val.beq a b && Val.beqL as bs
  | _,       _       => false
/-- Structural equality on key/value lists. -/
def Val.beqP : List (Val × Val) → List (Val × Val) → Bool
  | [],           []           => true
  | (a,b) :: as, (c,d) :: bs   => Val.beq a c && Val.beq b d && Val.beqP as bs
  | _,           _             => false
end

/-! ### `==` through the heap

`Val.beq` is structural and heap-free, which is right for scalars and is what makes the
scalar path reducible by `rfl`/`decide` -- `Refine.lean` depends on that. It is NOT right
for containers once they live on the heap: two list objects with equal contents have
different refs, so a structural compare answers `False` where Python answers `True`.

`Val.eqPy` is the heap-aware relation. It is `Option`-valued because it is fuel-indexed:
containers can be cyclic (`a = []; a.append(a)`), and running out of fuel is IGNORANCE, so
it must be `none` and become `outOfFuel`, never `false` -- a `false` there would be a
manufactured divergence on deeply nested values.

**At this step it agrees with `Val.beq` everywhere**, because every payload is `.none`, so
two distinct refs are two distinct plain objects and compare `false` exactly as before. The
ref case is written out now so that step 3 of `docs/boxed-containers.md` -- container
literals allocating -- needs no change here.

Note this does NOT re-type `applyBinop`. The design note proposed threading a heap through
it, which is 155 call sites and every reducible scalar lemma in `Refine.lean`. Diverting at
the one call site where a ref can appear costs nothing and leaves that path intact. -/
/-- Fuel for `==`, derived from the HEAP and never from the evaluator's fuel.

This is not a detail. Threading `evalExpr`'s fuel into the comparison makes the value of a
`binop` depend on how much fuel the evaluator had, which breaks `evalExpr_pure_fuel_indep`
outright -- the pure fragment includes `binop`. Deriving it from the heap keeps the
comparison fuel equal across two runs that differ only in evaluator fuel, because the pure
fragment is heap-inert.

`h.length` bounds how far reference-chasing can go before repeating an object; the constant
covers nesting inside VALUE containers, which the heap does not bound. Exceeding it yields
`none`, hence `outOfFuel` -- ignorance, never `false`. -/
def Val.eqFuel (h : Heap) : Nat := h.length + 64

mutual

def Val.eqPy (h : Heap) : Nat → Val → Val → Option Bool
  | 0,   _, _ => none
  | n+1, x, y =>
    match x, y with
    -- Reference identity short-circuits FIRST. That is CPython's fast path, and it is what
    -- makes `a == a` terminate for a cyclic container.
    | .ref a, .ref b =>
        if a == b then some true
        else
          match h.payload a, h.payload b with
          | .list u,  .list v  => Val.eqPyL h n u v
          | .tuple u, .tuple v => Val.eqPyL h n u v
          | .dict u,  .dict v  => Val.eqPyP h n u v
          | _, _ => some false
    | .list u,  .list v  => Val.eqPyL h n u v
    | .tuple u, .tuple v => Val.eqPyL h n u v
    | .dict u,  .dict v  => Val.eqPyP h n u v
    | .bobj _ (.tuple u), .bobj _ (.tuple v) => Val.eqPyL h n u v
    | .bobj _ (.list u),  .bobj _ (.list v)  => Val.eqPyL h n u v
    | .bobj _ (.dict u),  .bobj _ (.dict v)  => Val.eqPyP h n u v
    | .bobj _ (.tuple u), .tuple v => Val.eqPyL h n u v
    | .bobj _ (.list u),  .list v  => Val.eqPyL h n u v
    | .bobj _ (.dict u),  .dict v  => Val.eqPyP h n u v
    | .tuple u, .bobj _ (.tuple v) => Val.eqPyL h n u v
    | .list u,  .bobj _ (.list v)  => Val.eqPyL h n u v
    | .dict u,  .bobj _ (.dict v)  => Val.eqPyP h n u v
    -- Scalars, functions, and mismatched shapes: `Val.beq` is already correct and needs
    -- no heap, so there is one definition of scalar equality rather than two that can drift.
    | a, b => some (Val.beq a b)

def Val.eqPyL (h : Heap) : Nat → List Val → List Val → Option Bool
  | _,   [],      []      => some true
  | 0,   _,       _       => none
  | n+1, a :: as, b :: bs =>
      match Val.eqPy h n a b with
      | some true  => Val.eqPyL h n as bs
      | some false => some false
      | none       => none
  | _,   _,       _       => some false

def Val.eqPyP (h : Heap) : Nat → List (Val × Val) → List (Val × Val) → Option Bool
  | _,   [],      []      => some true
  | 0,   _,       _       => none
  | n+1, a :: as, b :: bs =>
      match Val.eqPy h n a.1 b.1 with
      | some true  =>
          match Val.eqPy h n a.2 b.2 with
          | some true  => Val.eqPyP h n as bs
          | some false => some false
          | none       => none
      | some false => some false
      | none       => none
  | _,   _,       _       => some false

end

/-- At this step every payload is `.none`, so the heap-aware relation and the structural one
agree on everything Core can currently build. Stated as a theorem so that step 3 has to
break it deliberately rather than silently: when container literals start allocating, this
becomes false for two equal lists, and that is the intended change. -/
theorem eqPy_agrees_with_beq_on_scalars (h : Heap) (n : Nat) (a b : Val)
    (ha : a.kind ≠ 5 ∧ a.kind ≠ 6 ∧ a.kind ≠ 7 ∧ a.kind ≠ 8 ∧ a.kind ≠ 12)
    (hb : b.kind ≠ 5 ∧ b.kind ≠ 6 ∧ b.kind ≠ 7 ∧ b.kind ≠ 8 ∧ b.kind ≠ 12) :
    Val.eqPy h (n+1) a b = some (Val.beq a b) := by
  cases a <;> cases b <;> simp_all [Val.eqPy, Val.kind]


instance : BEq Val := ⟨Val.beq⟩

/-- Strip one layer of builtin-base wrapping: the underlying `tuple`/`list`/`dict`/`str`
of an instance of a class with a builtin base, or the value unchanged.

Only one layer is ever needed: `Expr.alloc` never builds a `bobj` whose payload is itself
a `bobj` (the payload is coerced to the declared base first).

Deliberately **non-recursive**. Every consumer below unwraps with this rather than
recursing on `Val`, which keeps `Val.truthy`, `Val.iterable` and `Stdlib.elems`
non-recursive matchers: making them recursive compiles them through `brecOn`, and the
`unfold`/`whnf`-based proof of `Stdlib.builtin_heap_unchanged` does not survive that. -/
def Val.unbuiltin : Val → Val
  | .bobj _ v => v
  | v         => v

/-- Truthiness, in the permissive sense shared by most dynamic languages. -/
def Val.truthy : Val → Bool
  | .bool b   => b
  | .int i    => i != 0
  | .str s    => s != ""
  -- `bool(0.0) == bool(-0.0) == False`; `bool(nan)` is `True`.
  | .float f  => Fl.truthy f
  | .unit     => false
  | .list vs  => !vs.isEmpty
  | .tuple vs => !vs.isEmpty
  | .dict kvs => !kvs.isEmpty
  | .ref _    => true
  -- An interior pointer is an address, exactly like `.ref` -- never falsy.
  | .iref _ _ => true
  | .fn _     => true
  | .clos _ _ => true
  | .clsClos _ _ => true
  -- An instance of a class with a builtin base is truthy exactly as its base is:
  -- `bool(A(()))` is `False` for `class A(tuple)`. Written out per base rather than
  -- recursing, so this stays a plain matcher that reduces by `rfl`.
  | .bobj _ (.list vs)  => !vs.isEmpty
  | .bobj _ (.tuple vs) => !vs.isEmpty
  | .bobj _ (.dict kvs) => !kvs.isEmpty
  | .bobj _ (.str t)    => t != ""
  | .bobj _ _           => true

/-- What a value iterates over, if anything.

A `str` iterates over its characters as **one-character strings**, as CPython does:
`list("ab") == ['a', 'b']` and `g(*"ab") == ('a', 'b')` under CPython 3.9.6. Core had no
`str` case at all, which made `g(*"ab")` a `TypeError` and `for c in "ab"` a hole — a
measured divergence on extremely common code, recorded as a theorem until this change
and now recorded as agreement (`CallingConvention.str_is_iterable`).

The encoding is character-for-character the one `Stdlib.elems` already used for `str`,
which is what made the omission here a plain inconsistency rather than a design choice:
`list("ab")` worked while `for c in "ab"` did not. `String.toList` is the codepoint
decomposition, so this iterates `Char`s as CPython 3 iterates a `str`, not bytes.

Note the base case: the empty string iterates to `[]`, so `g(*"")` is `()` — matching
CPython — rather than an error, and a `str` case that returned `some []` for *every*
string would satisfy that pin while being useless, which is why the non-empty case is
pinned separately. -/
def Val.iterable : Val → Option (List Val)
  | .list vs  => some vs
  | .tuple vs => some vs
  | .dict kvs => some (kvs.map (·.1))
  | .str s    => some (s.toList.map (fun c => .str c.toString))
  | .bobj _ (.list vs)  => some vs
  | .bobj _ (.tuple vs) => some vs
  | .bobj _ (.dict kvs) => some (kvs.map (·.1))
  | .bobj _ (.str s)    => some (s.toList.map (fun c => .str c.toString))
  | _         => none

/-- Result of evaluating an expression. -/
inductive EResult where
  | val       : Val → EResult
  /-- A raised exception carrying its payload. -/
  | exn       : Val → EResult
  | hole      : String → EResult
  | outOfFuel : EResult
  deriving Repr, Inhabited

end Autoform.Core
