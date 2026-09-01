import Autoform.Lang.Core.Syntax

/-!
# Core — a modelled standard library

## Why this file exists

The `cachetools` ledger reads

    hole-free (upper bound) : 149 / 238 functions
    verifiable core         :  45 / 238 functions   (hole-free AND call-closed)

The 104-function difference is functions that contain no holes of their own but call
something that does not exist inside the translated program. Counting the unresolved
callee names over `ast-Cachetools.json` says what they are: Python builtins (`len`,
`sorted`, `tuple`, `callable`, `getattr`), exception constructors (`KeyError`,
`ValueError`, ...), and container methods (`get`, `items`, `append`, `pop`, `update`).

A function is only as analysable as its callees, so this is the largest single lever on
the verifiable core. This file supplies the callees.

## The rule this file is written under

**Model behaviour faithfully or return `none`.**

`none` means "not a modelled builtin", and the caller falls through to the existing
`call:<name>` / `mcall:<name>` hole — a *visible* gap, which the ledger counts and the
SACM case declares. A wrong model is the opposite: a silent wrong answer, which is the
failure mode `STRATEGY.md` §12, §19 and §26 exist to prevent, and which this project has
already been bitten by four times (floored `%`, bitwise `and`/`or`, C string `+`, private
name mangling). Every builtin below therefore returns `none` on argument shapes whose
Python behaviour Core cannot represent, rather than picking a plausible answer.

## Dialect

Everything here is **Python**. Under `.cLike` every entry point returns `none`
(`builtin_cLike_none`, `method_cLike_none` below): C has no `len`, and C's library
(`strlen`, `malloc`, `abs` on `INT_MIN`) has different semantics that would need their
own modelling pass. Answering a C program with Python's builtins is exactly the class of
error that made the semantics dialect-parameterized in the first place.

## What is deliberately NOT modelled, and why

* `super()` — needs an MRO. Core has one class *name* per object and no inheritance
  graph, so there is nothing to compute a proxy from.
* `hash()` — CPython's `hash` is implementation-defined and, for `str`/`bytes`,
  randomized per process by PYTHONHASHSEED. Any concrete value would diverge from the
  conformance oracle by construction.
* `set()` / `frozenset()` — Core has no unordered-collection value. Returning `Val.list`
  would make ordering and `==` observable where Python makes them not, and would make
  `set([1,2]) == set([2,1])` false.
* `iter()` / `next()` — an iterator is *stateful*. A `Val.list` snapshot makes repeated
  `next(it)` on the same variable return the same element forever, which is a wrong
  answer, not a missing one. Needs an iterator value in `Syntax.lean`.
* `type()` — Core has no type objects. `Val.fn` names live in the function-table
  namespace, not the builtin-type namespace, so `type(x) == int` would silently answer
  `False`. (`isinstance` is modelled only for the cases where the answer is certain.)
* `id()` — CPython interns small ints and some strings; identity of non-objects is not
  something Core can commit to.
* `range()`, `enumerate()`, `zip()`, `map()`, `filter()`, `reversed()` — lazy views.
  Same objection as `iter`, plus `range(3) == [0,1,2]` is `False` in Python.
* `str()` / `repr()` on strings and containers — see `Exceptions are strings` below.
* `float`, `bytes`, `complex` — no corresponding `Val`.
* `getattr`/`hasattr` on an *absent* attribute — Python consults the class, the MRO and
  `__getattr__`; Core's heap only has instance fields, so absence is unknown, not `False`.

## Two assumptions this file makes, stated so a reviewer can find them

1. **Exceptions are strings.** `Semantics.lean` already raises `.exn (.str "KeyError")`
   from `numToE` and from `index`, so exception *constructors* here produce
   `.val (.str "KeyError")` for consistency — which **drops the payload**. `KeyError(k)`
   and `KeyError(j)` are therefore indistinguishable, and `e.args` / `str(e)` are not
   faithful. Because an exception value and an ordinary string are the same `Val`, `str`
   and `repr` are modelled *only* on `.int` and `.bool`, so that this file never claims
   `str(e) = "KeyError"`.
2. **Mutating methods assume the receiver is not aliased.** Core containers are values,
   not boxed objects, so `xs.append(v)` cannot write through a reference. Those methods
   are returned under a **separate constructor**, `MethodResult.mutating`, carrying the
   updated receiver for the caller to store back. See the warning on `method` before
   wiring them.
-/

namespace Autoform.Core
namespace Stdlib

/-! ## Association-list helpers, shared with `Val.dict`

`Val.dict` is an association list in **insertion order** (CPython 3.7+ guarantees that
order, and `Semantics.evalExpr` resolves `index` by first match). Writing a key must
therefore *replace in place* when the key is present and *append* when it is not —
appending unconditionally would shadow correctly but change `len`, `keys` and iteration
order. -/

/-- Look up a key by structural equality, first match — the same discipline
`evalExpr` uses for `Expr.index`. -/
def dictGet : List (Val × Val) → Val → Option Val
  | [],           _ => none
  | (k, v) :: ps, x => if Val.beq k x then some v else dictGet ps x

/-- Is this key present? -/
def dictHas (ps : List (Val × Val)) (k : Val) : Bool := (dictGet ps k).isSome

/-- Write a key: replace in place if present, else append at the end. This is exactly
CPython's insertion-order rule. -/
def dictSet : List (Val × Val) → Val → Val → List (Val × Val)
  | [],           k, v => [(k, v)]
  | (k', v') :: ps, k, v =>
      if Val.beq k' k then (k, v) :: ps else (k', v') :: dictSet ps k v

/-- Delete every binding of a key. Keys are unique in a well-formed dict, so this
removes at most one. -/
def dictDel : List (Val × Val) → Val → List (Val × Val)
  | [],           _ => []
  | (k, v) :: ps, x => if Val.beq k x then dictDel ps x else (k, v) :: dictDel ps x

/-- Remove the first structural occurrence of a value from a list (`list.remove`). -/
def listRemove : List Val → Val → Option (List Val)
  | [],      _ => none
  | v :: vs, x => if Val.beq v x then some vs else (listRemove vs x).map (v :: ·)

/-- Index of the first structural occurrence (`list.index`). -/
def listIndex : List Val → Val → Option Nat
  | [],      _ => none
  | v :: vs, x => if Val.beq v x then some 0 else (listIndex vs x).map (· + 1)

/-- Occurrences of a value (`list.count`). -/
def listCount (vs : List Val) (x : Val) : Nat := (vs.filter (Val.beq x)).length

/-- Insert at a Python index: negative counts from the end, out-of-range clamps —
`list.insert` never raises. -/
def listInsert (vs : List Val) (i : Int) (x : Val) : List Val :=
  let n : Int := vs.length
  let j : Int := if i < 0 then max 0 (n + i) else min i n
  let k : Nat := j.toNat
  vs.take k ++ [x] ++ vs.drop k

/-- Resolve a Python sequence index: negative counts from the end, out of range is
`none` (the caller raises `IndexError`). -/
def seqIndex (n : Nat) (i : Int) : Option Nat :=
  let j : Int := if i < 0 then (n : Int) + i else i
  if 0 ≤ j ∧ j < (n : Int) then some j.toNat else none

/-- Remove the element at a resolved position. -/
def dropAt (vs : List Val) (k : Nat) : List Val := vs.take k ++ vs.drop (k + 1)

/-! ## Iteration and ordering -/

/-- What a value yields when iterated. Extends `Val.iterable` with the string case
(Python iterates a `str` as one-character strings). Anything else is `none`. -/
def elems : Val → Option (List Val)
  | .list vs  => some vs
  | .tuple vs => some vs
  | .dict kvs => some (kvs.map (·.1))
  | .str s    => some (s.toList.map (fun c => .str c.toString))
  -- An instance of a class with a builtin base iterates as its base does. Written out
  -- per base rather than recursing: making `elems` recursive compiles it through
  -- `brecOn`, which defeats the `whnf`-based proof of `builtin_heap_unchanged`.
  | .bobj _ (.list vs)  => some vs
  | .bobj _ (.tuple vs) => some vs
  | .bobj _ (.dict kvs) => some (kvs.map (·.1))
  | .bobj _ (.str s)    => some (s.toList.map (fun c => .str c.toString))
  | _         => none

/-- All-integers view of a value list; `none` if any element is not an `int`. -/
def allInts : List Val → Option (List Int)
  | []            => some []
  | .int i :: vs  => (allInts vs).map (i :: ·)
  | _ :: _        => none

/-- All-strings view of a value list. -/
def allStrs : List Val → Option (List String)
  | []            => some []
  | .str s :: vs  => (allStrs vs).map (s :: ·)
  | _ :: _        => none

/-- Sort a value list, if it is homogeneously ordered.

Only all-`int` and all-`str` lists are sorted. Python's `sorted` is defined by `<` on the
elements: on mixed or non-scalar element types it either raises `TypeError` or compares
by an order Core does not have, so those return `none`. `List.mergeSort` is stable, which
matches CPython. `Char` order is by code point in both languages, so lexicographic
`String` order agrees. -/
def sortVals (vs : List Val) : Option (List Val) :=
  match allInts vs with
  | some is => some ((is.mergeSort (fun a b => decide (a ≤ b))).map Val.int)
  | none    =>
    match allStrs vs with
    | some ss => some ((ss.mergeSort (fun a b => decide (a ≤ b))).map Val.str)
    | none    => none

/-! ## Exceptions

`Semantics.numToE` raises `.exn (.str "ZeroDivisionError")` and `evalExpr` raises
`.exn (.str "KeyError")`, so an exception in Core *is* the string naming its class.
Constructors follow that convention — see assumption 1 in the module docstring. -/

/-- The exception classes Core can name. Anything outside this list is `none`: a
user-defined exception is an ordinary class and goes through `Expr.alloc`. -/
def excNames : List String :=
  [ "Exception", "BaseException", "ArithmeticError", "AssertionError", "AttributeError"
  , "EOFError", "FloatingPointError", "ImportError", "IndentationError", "IndexError"
  , "KeyError", "KeyboardInterrupt", "LookupError", "MemoryError", "NameError"
  , "NotImplementedError", "OverflowError", "RecursionError", "ReferenceError"
  , "RuntimeError", "StopIteration", "StopAsyncIteration", "SyntaxError", "SystemError"
  , "SystemExit", "TypeError", "UnboundLocalError", "ValueError", "ZeroDivisionError" ]

/-- Raise a named exception. -/
private def raiseE (n : String) : EResult := .exn (.str n)

/-! ## Free builtins -/

/-- Builtin *type* names `isinstance` can decide against. -/
private def instOf : Val → Option String
  | .bool _  => some "bool"
  | .int _   => some "int"
  | .str _   => some "str"
  | .list _  => some "list"
  | .tuple _ => some "tuple"
  | .dict _  => some "dict"
  | .unit    => some "NoneType"
  -- `isinstance(A((0,)), tuple)` is `True` in CPython for `class A(tuple)`. The *class's
  -- own* name stays undecidable here (it is not a builtin type name), so `isInstance`
  -- answers `none` for it — a hole, not a wrong `False`.
  | .bobj _ (.bool _)  => some "bool"
  | .bobj _ (.int _)   => some "int"
  | .bobj _ (.str _)   => some "str"
  | .bobj _ (.list _)  => some "list"
  | .bobj _ (.tuple _) => some "tuple"
  | .bobj _ (.dict _)  => some "dict"
  | _        => none

/-- `isinstance` for the cases where the answer is certain.

Certain means: the value is a non-object primitive *and* the named type is a builtin
type. `bool` is a subclass of `int`, which is why `isinstance(True, int)` is `True`.
A `Val.ref` receiver, or a type name that is not a builtin, is `none` — deciding it
needs the class hierarchy Core does not carry. -/
def isInstance (v : Val) (tyName : String) : Option Bool :=
  if excNames.contains tyName then none
  else match instOf v with
  | none    => none
  | some t =>
    if tyName == "object" then some true
    else if !(["bool","int","str","list","tuple","dict","NoneType"].contains tyName) then none
    else if t == "bool" && tyName == "int" then some true
    else some (t == tyName)

/-- Read an instance attribute, distinguishing *absent* from `unit`.

`Heap.getField` answers `unit` for a missing field, which conflates "the attribute is
`None`" with "there is no such attribute". `getattr` must not: absence in Python consults
the class and `__getattr__`, which Core cannot see, so absence yields `none` here and the
caller holes. -/
def getAttr (h : Heap) (r : Ref) (f : String) : Option Val :=
  match h.get r with
  | none   => none
  | some o => (o.fields.find? (·.1 == f)).map (·.2)

/-! ### The name predicate, and why it is a *guard* rather than a list

The ledger needs to know which callee names this file answers, so that `Ctx.resolvable`
counts a modelled builtin as resolved. The obvious implementation is a hand-written list
of names beside the implementation — and a hand-written list beside an implementation is
exactly how a coverage metric starts lying, which is §17's whole subject.

So the list is not *beside* the implementation, it is *in front of* it: `builtin` is
`builtinCore` guarded by `knowsFree`, and every name `knowsFree` rejects is `none` **by
construction**, not by a theorem that could rot. Adding a case to `builtinCore` without
adding its name to `freeNames` makes that case dead code rather than making the ledger
overstate. `builtin_none_of_not_knowsFree` below is then true by `rfl`.

The other direction — every name in `freeNames` really is answered — *can* rot, so it is
proved by evaluation against a witness argument list (`knowsFree_complete`). -/

/-- Every free name this file answers under `.python`: the exception constructors plus
the modelled builtins. -/
def freeNames : List String :=
  excNames ++
  [ "len", "abs", "sum", "min", "max", "sorted", "bool", "str", "repr", "int"
  , "ord", "chr", "callable", "isinstance", "getattr", "hasattr"
  , "list", "tuple", "dict" ]

/-- Does `builtin` model this free-function name under this dialect?

**Exact**, not an upper bound: `knowsFree d n = true` iff `builtin d _ n _` answers for
*some* arguments (`knowsFree_complete` / `builtin_none_of_not_knowsFree`). It is still
only an upper bound on whether a *particular* call is answered, since `str` is modelled
on `.int` but not on `.str` — that residue is `dynamic-hole risk`, exactly like the
`field`/`index` cases the ledger already counts there. -/
def knowsFree (d : Dialect) (name : String) : Bool :=
  match d with
  | .cLike | .javascript => false
  | .python => freeNames.contains name

/-- The builtin bodies. Call `builtin`, not this: only `builtin` carries the `knowsFree`
guard that keeps the ledger honest. -/
def builtinCore (d : Dialect) (h : Heap) (name : String) (args : List Val) :
    Option (Heap × EResult) :=
  match d with
  | .cLike | .javascript => none
  | .python =>
    let ok (r : EResult) : Option (Heap × EResult) := some (h, r)
    let v (x : Val) : Option (Heap × EResult) := ok (.val x)
    if excNames.contains name then
      -- `KeyError(k)` — payload dropped, matching the interpreter's own representation.
      v (.str name)
    else
    match name, args with
    -- len: code points for `str`, exactly like CPython.
    | "len", [.list vs]  => v (.int vs.length)
    | "len", [.tuple vs] => v (.int vs.length)
    | "len", [.dict kvs] => v (.int kvs.length)
    | "len", [.str s]    => v (.int s.length)
    -- **Excluded, deliberately.** `len(A((0,)))` is `1` in CPython for `class A(tuple)`,
    -- but adding a `.bobj` case here defeats the branch enumeration in
    -- `builtin_heap_unchanged` below (a `whnf` timeout that raising the heartbeat budget
    -- does not fix). `len` of a builtin-based instance is therefore a `call:len` hole —
    -- counted ignorance, not a wrong number. `list`, `tuple`, `sorted`, `sum`, `min` and
    -- `max` all go through `elems` and *do* see through the base.
    -- abs: Python integers are unbounded, so this cannot overflow.
    | "abs", [.int i] => v (.int i.natAbs)
    -- bool / truthiness. Core's `Val.truthy` is the shared dynamic-language notion.
    | "bool", []       => v (.bool false)
    | "bool", [x]      => v (.bool x.truthy)
    -- str / repr: `.int` and `.bool` only. On a `.str` we cannot tell an ordinary
    -- string from an exception value, so we decline (module docstring, assumption 1).
    | "str",  [.int i]  => v (.str (toString i))
    | "str",  [.bool b] => v (.str (if b then "True" else "False"))
    | "repr", [.int i]  => v (.str (toString i))
    | "repr", [.bool b] => v (.str (if b then "True" else "False"))
    -- int: no string parsing (Python accepts underscores, signs, surrounding
    -- whitespace and arbitrary bases; getting that subtly wrong is not worth it).
    | "int", []         => v (.int 0)
    | "int", [.int i]   => v (.int i)
    | "int", [.bool b]  => v (.int (if b then 1 else 0))
    -- ord / chr.
    | "ord", [.str s] =>
        match s.toList with
        | [c] => v (.int c.toNat)
        | _   => ok (raiseE "TypeError")
    | "chr", [.int i] =>
        -- `Char.ofNat` answers `'A'` for a code point Lean rejects (surrogates, which
        -- CPython *does* allow), so the round trip is the guard: no round trip, no answer.
        if i ≥ 0 && i < 1114112 && (Char.ofNat i.toNat).toNat == i.toNat then
          v (.str (Char.ofNat i.toNat).toString)
        else none
    -- callable. A `.ref` is `none`: it depends on `__call__` on its class.
    | "callable", [.fn _]    => v (.bool true)
    | "callable", [.clos _ _]=> v (.bool true)
    | "callable", [.int _]   => v (.bool false)
    | "callable", [.str _]   => v (.bool false)
    | "callable", [.bool _]  => v (.bool false)
    | "callable", [.unit]    => v (.bool false)
    | "callable", [.list _]  => v (.bool false)
    | "callable", [.tuple _] => v (.bool false)
    | "callable", [.dict _]  => v (.bool false)
    -- isinstance, only where the answer is certain.
    | "isinstance", [x, .fn t] => (isInstance x t).map (fun b => (h, .val (.bool b)))
    -- getattr / hasattr: present attributes only.
    | "getattr", [.ref r, .str f]     => (getAttr h r f).map (fun x => (h, .val x))
    | "getattr", [.ref r, .str f, dv] => v ((getAttr h r f).getD dv)
    | "hasattr", [.ref r, .str f]     => (getAttr h r f).map (fun _ => (h, .val (.bool true)))
    -- Container constructors.
    | "list",  []  => v (.list [])
    | "list",  [x] => (elems x).map (fun es => (h, .val (.list es)))
    | "tuple", []  => v (.tuple [])
    | "tuple", [x] => (elems x).map (fun es => (h, .val (.tuple es)))
    | "dict",  []  => v (.dict [])
    | "dict",  [.dict kvs] => v (.dict kvs)
    | "dict",  [.list ps]  => (pairsOf [] ps).map (fun kvs => (h, .val (.dict kvs)))
    | "dict",  [.tuple ps] => (pairsOf [] ps).map (fun kvs => (h, .val (.dict kvs)))
    -- sorted.
    | "sorted", [x] =>
        match elems x with
        | none    => none
        | some es => (sortVals es).map (fun s => (h, .val (.list s)))
    -- sum / min / max over integers.
    | "sum", [x] =>
        match (elems x).bind allInts with
        | some is => v (.int is.sum)
        | none    => none
    | "sum", [x, .int s] =>
        match (elems x).bind allInts with
        | some is => v (.int (s + is.sum))
        | none    => none
    | "min", [x] => minMax x true
    | "max", [x] => minMax x false
    | "min", args@(_ :: _ :: _) => minMax (.list args) true
    | "max", args@(_ :: _ :: _) => minMax (.list args) false
    | _, _ => none
where
  /-- Build dict entries from a list of two-element pairs, **left to right**, so a
  repeated key keeps its first position and its last value — CPython's rule. -/
  pairsOf (acc : List (Val × Val)) : List Val → Option (List (Val × Val))
    | []                      => some acc
    | .tuple [k, x] :: rest   => pairsOf (dictSet acc k x) rest
    | .list  [k, x] :: rest   => pairsOf (dictSet acc k x) rest
    | _ :: _                  => none
  /-- `min`/`max` over an all-integer iterable; empty raises `ValueError`. -/
  minMax (x : Val) (isMin : Bool) : Option (Heap × EResult) :=
    match (elems x).bind allInts with
    | none    => none
    | some [] => some (h, .exn (.str "ValueError"))
    | some (i :: is) =>
        some (h, .val (.int (is.foldl (fun a b => if isMin then min a b else max a b) i)))

/-- The Python builtins, for `Expr.call`.

`none` means "not modelled" — the caller must fall through to its `call:<name>` hole.
Returns the heap so the caller can thread it uniformly; every entry here leaves it
unchanged (only `getattr` even reads it), which `builtin_heap_unchanged` proves.

Under `.cLike` this is `none` for every name (`builtin_cLike_none`), and for any name
`knowsFree` rejects it is `none` by construction. -/
def builtin (d : Dialect) (h : Heap) (name : String) (args : List Val) :
    Option (Heap × EResult) :=
  if knowsFree d name then builtinCore d h name args else none

/-! ## Container methods

`Expr.mcall` currently holes with `mcall:<m>:non-object` whenever the receiver is not a
`Val.ref` — which is every list, tuple, dict and string. This is the other half of the
gap.

### Read the warning before wiring the mutating half

Python containers are boxed and shared; Core's are values. `MethodResult.mutating`
therefore hands the caller the *new receiver value* rather than performing a write, and
it is only faithful when the receiver is not aliased:

    a = []; b = a; b.append(1)      -- Python: `a` is [1].  Value writeback: `a` is [].

Worse, on this corpus the CPG has already desugared `self.__data.pop(k)` into
`tmp0 = self.__data; tmp0.pop(k)`, so writing back to the receiver *expression* updates a
temporary and the object is untouched. **The honest wiring is to treat `.mutating` as a
hole (`mcall:<m>:unboxed-container`) until `Syntax.lean` grows a boxed container**, and to
use the `.pure` half now. The mutating cases are implemented here so that the boxed
version is a change of plumbing rather than of semantics — not because they are ready.
-/

/-- Outcome of a method call. `pure` is safe to use directly; `mutating` additionally
carries the updated receiver and inherits the aliasing caveat above. -/
inductive MethodResult where
  | pure     : EResult → MethodResult
  /-- result, then the receiver's new value. -/
  | mutating : EResult → Val → MethodResult
  deriving Repr, Inhabited

/-- Methods on non-object receivers (`list`, `tuple`, `dict`).

`none` means "not modelled": the caller keeps its `mcall:` hole. Note that this must be
consulted **only after** the interpreter's own class dispatch fails, so a user class with
a `get` or `pop` method always wins — those names are ambiguous by design.

String methods are not modelled at all: an exception value and a string are the same
`Val`, so `"KeyError".startswith(...)` and `e.startswith(...)` are indistinguishable. -/
def methodCore (d : Dialect) (h : Heap) (recv : Val) (name : String) (args : List Val) :
    Option (Heap × MethodResult) :=
  match d with
  | .cLike | .javascript => none
  | .python =>
    let p (r : EResult) : Option (Heap × MethodResult) := some (h, .pure r)
    let pv (x : Val) : Option (Heap × MethodResult) := p (.val x)
    let m (r : EResult) (nv : Val) : Option (Heap × MethodResult) := some (h, .mutating r nv)
    match recv, name, args with
    -- ── dict, read-only ────────────────────────────────────────────────────────
    | .dict kvs, "get", [k]     => pv ((dictGet kvs k).getD .unit)
    | .dict kvs, "get", [k, dv] => pv ((dictGet kvs k).getD dv)
    -- `keys`/`values`/`items` return *views* in Python 3. They are modelled as lists,
    -- which is faithful for iteration, `len` and `in`, and NOT faithful for `==`
    -- against a set, or for observing later mutation of the dict through the view.
    | .dict kvs, "keys",   [] => pv (.list (kvs.map (·.1)))
    | .dict kvs, "values", [] => pv (.list (kvs.map (·.2)))
    | .dict kvs, "items",  [] => pv (.list (kvs.map (fun kv => .tuple [kv.1, kv.2])))
    | .dict kvs, "copy",   [] => pv (.dict kvs)
    -- ── dict, mutating ─────────────────────────────────────────────────────────
    | .dict kvs, "pop", [k] =>
        match dictGet kvs k with
        | some x => m (.val x) (.dict (dictDel kvs k))
        | none   => p (raiseE "KeyError")
    | .dict kvs, "pop", [k, dv] =>
        match dictGet kvs k with
        | some x => m (.val x) (.dict (dictDel kvs k))
        | none   => p (.val dv)
    -- CPython 3.7+ `popitem` is LIFO: the *last* inserted pair.
    | .dict kvs, "popitem", [] =>
        match kvs.getLast? with
        | some (k, x) => m (.val (.tuple [k, x])) (.dict (kvs.dropLast))
        | none        => p (raiseE "KeyError")
    | .dict kvs, "setdefault", [k] =>
        match dictGet kvs k with
        | some x => p (.val x)
        | none   => m (.val .unit) (.dict (dictSet kvs k .unit))
    | .dict kvs, "setdefault", [k, dv] =>
        match dictGet kvs k with
        | some x => p (.val x)
        | none   => m (.val dv) (.dict (dictSet kvs k dv))
    | .dict _,   "clear", []             => m (.val .unit) (.dict [])
    | .dict kvs, "update", [.dict other] =>
        m (.val .unit) (.dict (other.foldl (fun acc kv => dictSet acc kv.1 kv.2) kvs))
    -- ── list / tuple, read-only ────────────────────────────────────────────────
    | .list vs,  "count", [x] => pv (.int (listCount vs x))
    | .tuple vs, "count", [x] => pv (.int (listCount vs x))
    | .list vs,  "copy",  []  => pv (.list vs)
    | .list vs,  "index", [x] =>
        match listIndex vs x with
        | some i => p (.val (.int i))
        | none   => p (raiseE "ValueError")
    | .tuple vs, "index", [x] =>
        match listIndex vs x with
        | some i => p (.val (.int i))
        | none   => p (raiseE "ValueError")
    -- ── list, mutating ─────────────────────────────────────────────────────────
    | .list vs, "append", [x] => m (.val .unit) (.list (vs ++ [x]))
    | .list vs, "insert", [.int i, x] => m (.val .unit) (.list (listInsert vs i x))
    | .list vs, "extend", [y] =>
        match elems y with
        | some es => m (.val .unit) (.list (vs ++ es))
        | none    => none
    | .list _,  "clear", [] => m (.val .unit) (.list [])
    | .list vs, "remove", [x] =>
        match listRemove vs x with
        | some vs' => m (.val .unit) (.list vs')
        | none     => p (raiseE "ValueError")
    | .list vs, "pop", [] =>
        match vs.getLast? with
        | some x => m (.val x) (.list vs.dropLast)
        | none   => p (raiseE "IndexError")
    | .list vs, "pop", [.int i] =>
        match seqIndex vs.length i with
        | none   => p (raiseE "IndexError")
        | some k => match vs[k]? with
                    | some x => m (.val x) (.list (dropAt vs k))
                    | none   => p (raiseE "IndexError")
    | _, _, _ => none

/-- Every method name this file answers under `.python`. -/
def methodNames : List String :=
  [ "get", "keys", "values", "items", "copy", "count", "index"
  , "append", "insert", "extend", "clear", "remove", "pop", "popitem"
  , "setdefault", "update" ]

/-- Does `method` model this method name under this dialect?

**This one is an upper bound, and you should treat it as one.** Unlike `knowsFree` it
cannot be exact, because a method is modelled per *receiver shape*, and the ledger is a
static analysis that does not know receivers: `pop` is answered on a `.list` and a
`.dict` and refused on a `.str`, `.tuple` or `.ref`. A bare name predicate necessarily
says `true` for all three.

That is the same kind of claim `Ctx.resolve` already makes for user functions — a name
that resolves statically can still hole at runtime — so using this in `Ctx.resolvable`
does not introduce a *new* category of overstatement. But it does add to it, and the
residue belongs in `dynamic-hole risk`, which is the number §17 built for exactly this.

If you want a predicate with no slack at all, use `answersMethod` below: it is decided by
the real function against the real receiver, so it cannot overstate and cannot drift. It
is only usable where the receiver value is in hand — the interpreter, or the conformance
harness, not the static ledger. -/
def knowsMethod (d : Dialect) (name : String) : Bool :=
  match d with
  | .cLike | .javascript => false
  | .python => methodNames.contains name

/-- Methods on non-object receivers, for `Expr.mcall`. Guarded by `knowsMethod` for the
same reason `builtin` is guarded by `knowsFree`. -/
def method (d : Dialect) (h : Heap) (recv : Val) (name : String) (args : List Val) :
    Option (Heap × MethodResult) :=
  if knowsMethod d name then methodCore d h recv name args else none

/-- The exact, receiver-aware version of `knowsMethod`: decided by `method` itself, so it
is sound and complete by definition and cannot drift. -/
def answersMethod (d : Dialect) (h : Heap) (recv : Val) (name : String)
    (args : List Val) : Bool := (method d h recv name args).isSome

/-! ## Properties

Only what closes cheaply and independently. Each is stated in terms other than the
definition it checks wherever that was possible — a lemma that restates its subject is
the vacuity `STRATEGY.md` §14 and the mutation gate exist to catch. -/

/-- The whole table is Python-only: no C program can be answered by a Python builtin. -/
@[simp] theorem builtin_cLike_none (h : Heap) (n : String) (as : List Val) :
    builtin .cLike h n as = none := rfl

/-- Likewise for JavaScript: no stdlib modelling exists for it either yet. -/
@[simp] theorem builtin_javascript_none (h : Heap) (n : String) (as : List Val) :
    builtin .javascript h n as = none := rfl

/-- Likewise for methods. -/
@[simp] theorem method_cLike_none (h : Heap) (r : Val) (n : String) (as : List Val) :
    method .cLike h r n as = none := rfl

/-- Likewise for methods, under JavaScript. -/
@[simp] theorem method_javascript_none (h : Heap) (r : Val) (n : String) (as : List Val) :
    method .javascript h r n as = none := rfl


/-! ### The name predicates the ledger consumes

`Ctx.resolvable` must count a modelled builtin as a resolved callee, or the verifiable
core is understated. These are the predicates for that. The soundness direction — the one
that stops the ledger *overstating* — holds by construction, because `builtin` and
`method` are the guarded wrappers, not the implementations. -/

/-- No C program is answered by a Python builtin, at the predicate level too. -/
@[simp] theorem knowsFree_cLike (n : String) : knowsFree .cLike n = false := rfl

/-- Likewise at the predicate level for JavaScript. -/
@[simp] theorem knowsFree_javascript (n : String) : knowsFree .javascript n = false := rfl

/-- Likewise for methods. -/
@[simp] theorem knowsMethod_cLike (n : String) : knowsMethod .cLike n = false := rfl

/-- Likewise for methods, under JavaScript. -/
@[simp] theorem knowsMethod_javascript (n : String) : knowsMethod .javascript n = false := rfl

/-- **The direction that matters.** A name the predicate rejects is never answered, so a
ledger built on `knowsFree` can only understate, never overstate. True by `rfl` under the
hypothesis: `builtin` *is* `builtinCore` behind this guard. -/
theorem builtin_none_of_not_knowsFree {d : Dialect} {h : Heap} {n : String}
    {as : List Val} (hk : knowsFree d n = false) : builtin d h n as = none := by
  simp [builtin, hk]

/-- Same for methods. -/
theorem method_none_of_not_knowsMethod {d : Dialect} {h : Heap} {r : Val} {n : String}
    {as : List Val} (hk : knowsMethod d n = false) : method d h r n as = none := by
  simp [method, hk]

/-- Contrapositive, in the form a caller wants: if the call was answered, the predicate
said so. -/
theorem knowsFree_of_builtin_isSome {d : Dialect} {h : Heap} {n : String} {as : List Val}
    (hs : (builtin d h n as).isSome) : knowsFree d n = true := by
  by_cases hk : knowsFree d n
  · exact hk
  · simp [builtin_none_of_not_knowsFree (Bool.not_eq_true _ ▸ hk)] at hs

/-- And for methods — which also bounds the exact receiver-aware predicate: anything
`answersMethod` accepts, `knowsMethod` accepts. -/
theorem knowsMethod_of_answersMethod {d : Dialect} {h : Heap} {r : Val} {n : String}
    {as : List Val} (hs : answersMethod d h r n as = true) : knowsMethod d n = true := by
  by_cases hk : knowsMethod d n
  · exact hk
  · simp [answersMethod, method_none_of_not_knowsMethod (Bool.not_eq_true _ ▸ hk)] at hs

/-! The completeness direction — every listed name really is answered — is the one that
can rot as the implementation changes, so it is not asserted, it is *evaluated*. Each
name is applied to a witness argument list and the whole table is checked by the kernel.
Delete a case from `builtinCore` and leave its name in `freeNames`, and this fails. -/

/-- A heap with one object carrying one field, so `getattr`/`hasattr` have something to
find. -/
private def wHeap : Heap := [{ cls := "C", fields := [("f", .unit)] }]

/-- Arguments on which each free name is answered. Exception constructors accept
anything, so they fall through to `[]`. -/
private def freeWitness : String → List Val
  | "len"        => [.list []]
  | "abs"        => [.int 0]
  | "sum"        => [.list []]
  | "min"        => [.list [.int 1]]
  | "max"        => [.list [.int 1]]
  | "sorted"     => [.list []]
  | "bool"       => []
  | "str"        => [.int 0]
  | "repr"       => [.int 0]
  | "int"        => []
  | "ord"        => [.str "a"]
  | "chr"        => [.int 65]
  | "callable"   => [.int 0]
  | "isinstance" => [.int 0, .fn "int"]
  | "getattr"    => [.ref 0, .str "f"]
  | "hasattr"    => [.ref 0, .str "f"]
  | "list"       => []
  | "tuple"      => []
  | "dict"       => []
  | _            => []

/-- Receiver and arguments on which each method name is answered. -/
private def methodWitness : String → Val × List Val
  | "get"        => (.dict [], [.unit])
  | "keys"       => (.dict [], [])
  | "values"     => (.dict [], [])
  | "items"      => (.dict [], [])
  | "copy"       => (.dict [], [])
  | "count"      => (.list [], [.unit])
  | "index"      => (.list [], [.unit])
  | "append"     => (.list [], [.unit])
  | "insert"     => (.list [], [.int 0, .unit])
  | "extend"     => (.list [], [.list []])
  | "clear"      => (.list [], [])
  | "remove"     => (.list [], [.unit])
  | "pop"        => (.list [], [])
  | "popitem"    => (.dict [], [])
  | "setdefault" => (.dict [], [.unit])
  | "update"     => (.dict [], [.dict []])
  | _            => (.unit, [])

/-- Every name `knowsFree` accepts is genuinely answered by `builtin`. With
`builtin_none_of_not_knowsFree`, `knowsFree` is exactly the set of answered names. -/
theorem knowsFree_complete :
    freeNames.all (fun n => (builtin .python wHeap n (freeWitness n)).isSome) = true := by
  decide

/-- Every name `knowsMethod` accepts is genuinely answered by `method` on some
receiver. -/
theorem knowsMethod_complete :
    methodNames.all (fun n =>
      (method .python wHeap (methodWitness n).1 n (methodWitness n).2).isSome) = true := by
  decide

/-- `len` of a list is its length — stated against `List.length`, not against `builtin`. -/
@[simp] theorem builtin_len_list (h : Heap) (vs : List Val) :
    builtin .python h "len" [.list vs] = some (h, .val (.int vs.length)) := rfl

/-- `len` of a dict counts its entries. -/
@[simp] theorem builtin_len_dict (h : Heap) (kvs : List (Val × Val)) :
    builtin .python h "len" [.dict kvs] = some (h, .val (.int kvs.length)) := rfl

/-- Builtins never allocate or mutate: the heap comes back unchanged. -/
theorem builtin_heap_unchanged {d : Dialect} {h h' : Heap} {n : String} {as : List Val}
    {r : EResult} (hb : builtin d h n as = some (h', r)) : h' = h := by
  cases d with
  | cLike => simp at hb
  | javascript => simp at hb
  | python =>
    -- Every branch either returns `(h, _)` or is `none`; `split` enumerates them and
    -- `simp_all` discharges each by injectivity of `some`/`Prod.mk`.
    unfold builtin builtinCore at hb
    split at hb
    case isFalse => cases hb
    simp only at hb
    split at hb
    · simp_all
    · split at hb <;> simp_all [Option.map_eq_some_iff, builtinCore.minMax] <;>
        (try split at hb) <;> (try simp_all) <;>
        (try (obtain ⟨_, h1, _⟩ := hb; exact h1.symm)) <;>
        (try (obtain ⟨_, _, h1, _⟩ := hb; exact h1.symm)) <;>
        (try (rcases hb with ⟨_, h1, _⟩ | ⟨_, h1, _⟩ <;> exact h1.symm)) <;>
        (try (rename_i hx; exact hx.2.1.symm))

/-- Reading back a key just written returns what was written. -/
@[simp] theorem dictGet_dictSet_self (ps : List (Val × Val)) (k v : Val)
    (hk : Val.beq k k = true) : dictGet (dictSet ps k v) k = some v := by
  induction ps with
  | nil => simp [dictSet, dictGet, hk]
  | cons p ps ih =>
    obtain ⟨k', v'⟩ := p
    by_cases hc : Val.beq k' k = true
    · simp [dictSet, dictGet, hc, hk]
    · simp [dictSet, dictGet, hc, ih]

/-- Writing a key never shrinks or grows a dict by more than one entry, and never
reorders it: the length is the old length, or one more. -/
theorem dictSet_length (ps : List (Val × Val)) (k v : Val) :
    (dictSet ps k v).length = ps.length ∨ (dictSet ps k v).length = ps.length + 1 := by
  induction ps with
  | nil => simp [dictSet]
  | cons p ps ih =>
    obtain ⟨k', v'⟩ := p
    by_cases hc : Val.beq k' k = true
    · simp [dictSet, hc]
    · simp only [dictSet, hc, List.length_cons]
      rcases ih with h | h <;> simp [h]

/-- `dict.get` on a present key returns that key's value — stated via `dictGet`, which
`dictGet_dictSet_self` independently pins down. -/
theorem method_dict_get_present (h : Heap) (kvs : List (Val × Val)) (k v : Val)
    (hk : dictGet kvs k = some v) :
    method .python h (.dict kvs) "get" [k] = some (h, .pure (.val v)) := by
  simp [method, methodCore, knowsMethod, methodNames, hk]

/-- `dict.get` with a default falls back to it when the key is absent. -/
theorem method_dict_get_absent (h : Heap) (kvs : List (Val × Val)) (k dv : Val)
    (hk : dictGet kvs k = none) :
    method .python h (.dict kvs) "get" [k, dv] = some (h, .pure (.val dv)) := by
  simp [method, methodCore, knowsMethod, methodNames, hk]

/-- `append` extends the receiver by exactly one element. -/
theorem method_append (h : Heap) (vs : List Val) (x : Val) :
    method .python h (.list vs) "append" [x]
      = some (h, .mutating (.val .unit) (.list (vs ++ [x]))) := rfl

/-- `list.count` agrees with `List.countP` on structural equality. -/
theorem listCount_eq (vs : List Val) (x : Val) :
    listCount vs x = (vs.countP (Val.beq x)) := by
  simp [listCount, List.countP_eq_length_filter]

/-- Sorting preserves multiset content, so `len(sorted(xs)) = len(xs)`. -/
theorem allInts_length : ∀ {vs : List Val} {is : List Int},
    allInts vs = some is → is.length = vs.length
  | [],      _, h => by simp [allInts] at h; simp [← h]
  | v :: vs, is, h => by
      cases v <;> simp [allInts, Option.map_eq_some_iff] at h
      obtain ⟨as, ha, hb⟩ := h
      simp [← hb, allInts_length ha]

theorem allStrs_length : ∀ {vs : List Val} {ss : List String},
    allStrs vs = some ss → ss.length = vs.length
  | [],      _, h => by simp [allStrs] at h; simp [← h]
  | v :: vs, ss, h => by
      cases v <;> simp [allStrs, Option.map_eq_some_iff] at h
      obtain ⟨as, ha, hb⟩ := h
      simp [← hb, allStrs_length ha]

/-- Sorting is a permutation, so `len(sorted(xs)) = len(xs)`. -/
theorem sortVals_length {vs sorted : List Val} (hs : sortVals vs = some sorted) :
    sorted.length = vs.length := by
  unfold sortVals at hs
  split at hs
  · rename_i is hi
    injection hs with hs
    simp [← hs, List.length_mergeSort, allInts_length hi]
  · split at hs
    · rename_i ss hi
      injection hs with hs
      simp [← hs, List.length_mergeSort, allStrs_length hi]
    · cases hs

/-! ## Examples

Each modelled builtin, evaluated. These are the executable half of the documentation:
they are what a reviewer reads to see the claimed behaviour without reading the code. -/

section Examples

private def H : Heap := []

/-- Show only the result, dropping the (always unchanged) heap. -/
private def R (o : Option (Heap × EResult)) : Option EResult := o.map (·.2)
private def M (o : Option (Heap × MethodResult)) : Option MethodResult := o.map (·.2)
private def B (n : String) (as : List Val) : Option EResult := R (builtin .python H n as)
private def Mth (r : Val) (n : String) (as : List Val) : Option MethodResult :=
  M (method .python H r n as)

-- len
#eval B "len" [.list [.int 1, .int 2, .int 3]]      -- val (int 3)
#eval B "len" [.dict [(.str "a", .int 1)]]          -- val (int 1)
#eval B "len" [.str "héllo"]                        -- val (int 5)   (code points)
-- numeric
#eval B "abs" [.int (-7)]                           -- val (int 7)
#eval B "sum" [.list [.int 1, .int 2, .int 4]]      -- val (int 7)
#eval B "sum" [.list [.int 1], .int 10]             -- val (int 11)
#eval B "min" [.list [.int 3, .int 1, .int 2]]      -- val (int 1)
#eval B "max" [.int 3, .int 9]                      -- val (int 9)
#eval B "min" [.list []]                            -- exn ValueError
#eval B "min" [.list [.str "a"]]                    -- none  (not modelled on str)
-- conversions
#eval B "bool" [.list []]                           -- val (bool false)
#eval B "str"  [.int (-5)]                          -- val (str "-5")
#eval B "str"  [.bool true]                         -- val (str "True")
#eval B "repr" [.int 12]                            -- val (str "12")
#eval B "str"  [.str "x"]                           -- none  (exception ambiguity)
#eval B "int"  [.bool true]                         -- val (int 1)
#eval B "ord"  [.str "A"]                           -- val (int 65)
#eval B "chr"  [.int 65]                            -- val (str "A")
-- containers
#eval B "list"   [.str "ab"]                        -- val (list ["a","b"])
#eval B "tuple"  [.list [.int 1, .int 2]]           -- val (tuple [1,2])
#eval B "tuple"  [.dict [(.str "k", .int 1)]]       -- val (tuple ["k"])  (keys)
#eval B "dict"   [.list [.tuple [.str "a", .int 1], .tuple [.str "a", .int 2]]]
                                                    -- val (dict [("a",2)])  (last wins)
#eval B "sorted" [.list [.int 3, .int 1, .int 2]]   -- val (list [1,2,3])
#eval B "sorted" [.list [.str "b", .str "a"]]       -- val (list ["a","b"])
#eval B "sorted" [.list [.int 1, .str "a"]]         -- none  (heterogeneous)
-- predicates
#eval B "callable" [.fn "f"]                        -- val (bool true)
#eval B "callable" [.int 1]                         -- val (bool false)
#eval B "callable" [.ref 0]                         -- none  (needs __call__)
#eval B "isinstance" [.int 1, .fn "int"]            -- val (bool true)
#eval B "isinstance" [.bool true, .fn "int"]        -- val (bool true)  (bool <: int)
#eval B "isinstance" [.str "x", .fn "int"]          -- val (bool false)
#eval B "isinstance" [.ref 0, .fn "Cache"]          -- none  (no class hierarchy)
-- exceptions
#eval B "KeyError" [.str "k"]                       -- val (str "KeyError")
#eval B "ValueError" []                             -- val (str "ValueError")
#eval B "MyError" []                                -- none  (user class)
-- attributes
#eval R (builtin .python [{ cls := "C", fields := [("x", .int 4)] }]
          "getattr" [.ref 0, .str "x"])             -- val (int 4)
#eval R (builtin .python [{ cls := "C", fields := [] }]
          "getattr" [.ref 0, .str "x"])             -- none  (absence is unknown)
#eval R (builtin .python [{ cls := "C", fields := [] }]
          "getattr" [.ref 0, .str "x", .int 9])     -- val (int 9)
-- not modelled
#eval B "super" []                                  -- none
#eval B "hash"  [.int 1]                            -- none
#eval B "set"   []                                  -- none
#eval B "iter"  [.list []]                          -- none
#eval B "type"  [.int 1]                            -- none
-- dialect
#eval R (builtin .cLike H "len" [.list []])         -- none

-- methods, pure
#eval Mth (.dict [(.str "a", .int 1)]) "get" [.str "a"]        -- pure (val 1)
#eval Mth (.dict [(.str "a", .int 1)]) "get" [.str "z"]        -- pure (val unit)
#eval Mth (.dict [(.str "a", .int 1)]) "get" [.str "z", .int 0]-- pure (val 0)
#eval Mth (.dict [(.str "a", .int 1)]) "keys" []               -- pure (val ["a"])
#eval Mth (.dict [(.str "a", .int 1)]) "values" []             -- pure (val [1])
#eval Mth (.dict [(.str "a", .int 1)]) "items" []              -- pure (val [("a",1)])
#eval Mth (.list [.int 1, .int 2, .int 1]) "count" [.int 1]    -- pure (val 2)
#eval Mth (.list [.int 1, .int 2]) "index" [.int 2]            -- pure (val 1)
#eval Mth (.list [.int 1]) "index" [.int 9]                    -- pure (exn ValueError)
-- methods, mutating (note the separate constructor)
#eval Mth (.list [.int 1]) "append" [.int 2]                   -- mutating unit [1,2]
#eval Mth (.list [.int 1, .int 2]) "pop" []                    -- mutating 2 [1]
#eval Mth (.list [.int 1, .int 2]) "pop" [.int 0]              -- mutating 1 [2]
#eval Mth (.list [.int 1]) "pop" [.int 5]                      -- pure (exn IndexError)
#eval Mth (.list [.int 1, .int 2]) "remove" [.int 1]           -- mutating unit [2]
#eval Mth (.list [.int 1]) "insert" [.int 0, .int 9]           -- mutating unit [9,1]
#eval Mth (.list [.int 1]) "extend" [.list [.int 2]]           -- mutating unit [1,2]
#eval Mth (.list [.int 1]) "clear" []                          -- mutating unit []
#eval Mth (.dict [(.str "a", .int 1)]) "pop" [.str "a"]        -- mutating 1 {}
#eval Mth (.dict []) "pop" [.str "a"]                          -- pure (exn KeyError)
#eval Mth (.dict [(.str "a", .int 1), (.str "b", .int 2)]) "popitem" []
                                                               -- mutating ("b",2) {a:1}  (LIFO)
#eval Mth (.dict [(.str "a", .int 1)]) "setdefault" [.str "a", .int 9]
                                                               -- pure (val 1)  (present: no write)
#eval Mth (.dict []) "setdefault" [.str "a", .int 9]            -- mutating 9 {a:9}
#eval Mth (.dict [(.str "a", .int 1)]) "update" [.dict [(.str "a", .int 5), (.str "b", .int 6)]]
                                                               -- mutating unit {a:5, b:6}  (order kept)
-- not modelled
#eval Mth (.str "ab") "startswith" [.str "a"]                  -- none
#eval Mth (.list []) "sort" []                                 -- none

-- the ledger's name predicates
#eval knowsFree .python "len"          -- true
#eval knowsFree .python "KeyError"     -- true
#eval knowsFree .python "super"        -- false
#eval knowsFree .python "hash"         -- false
#eval knowsFree .cLike  "len"          -- false
#eval knowsMethod .python "pop"        -- true
#eval knowsMethod .python "sort"       -- false
#eval knowsMethod .cLike  "pop"        -- false
-- and the slack `knowsMethod` necessarily carries, made visible:
#eval knowsMethod .python "pop"                              -- true  (name level)
#eval answersMethod .python H (.dict []) "pop" [.str "k"]    -- true  (dict: modelled)
#eval answersMethod .python H (.str "s") "pop" [.str "k"]    -- false (str: not modelled)
#eval answersMethod .python H (.tuple []) "pop" []           -- false (tuple: immutable)

end Examples

end Stdlib
end Autoform.Core
