import Autoform.Lang.Core.Semantics

/-!
# A C `...` is not a Python `*args`

`cartographer/export_ast.sc` gates its Python-specific parameter analysis on the file
extension, but did not gate the *variadic* flag, which the C and C++ frontends also set for
`...`. A signature such as

```c
void V8_Fatal(const char *fmt, ...);
```

therefore carried a vararg marker, and `bindParams` binds surplus positional arguments to a
tuple under that marker. C's `...` is read through `va_arg`, which the pipeline does not
translate at all, so the marker did not merely mislabel the signature: it gave every
printf-style call in the corpus an answer computed under Python's calling convention.

The two functions below differ in exactly one field. `withMarker` is what the exporter
emitted, and it silently binds a 2-tuple for a three-argument call. `withoutMarker` is the
same signature with the marker removed, and the same call is refused. Neither models
`va_arg`, and that is the point of this case rather than an omission: the defect converted a
call the pipeline would have **declined** into one it **answered wrongly**, which is the
distinction the surrounding paper is about, and no hole is emitted on either side.

`withMarker` is retained as a negative control for the same reason the other fixtures retain
theirs: nothing in the coverage ledger moved when this was repaired, so nothing in the ledger
would notice a regression to it.
-/

namespace Autoform.VariadicSpec

open Autoform.Core

private def C : Ctx := { dialect := .cLike, table := [], globals := 0 }

/-- The body reads the vararg name, which is what a Python `*args` function would do and
what no C function can do. -/
private def body : Stmt := .ret (.name "args")

/-- What the exporter emitted for `void V8_Fatal(const char *fmt, ...)`: a Python vararg
marker on a C signature. Retained as a negative control. -/
private def withMarker : Func :=
  { name := "V8_Fatal", params := ["fmt"], vararg := some "args", body := body }

/-- The same signature with the marker not emitted, which is what the fix does for
non-Python sources. -/
private def withoutMarker : Func :=
  { name := "V8_Fatal", params := ["fmt"], body := body }

private def run (f : Func) (vs : List Val) : EResult :=
  (applyFunc C 200 [] f none vs []).2

-- `V8_Fatal("%s", 1, 2)` under the marker: the two surplus arguments are silently
-- packed into a tuple and handed to the body, under Python's convention.
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.tuple [Autoform.Core.Val.int 1, Autoform.Core.Val.int 2]) -/
#guard_msgs in #eval run withMarker [.str "%s", .int 1, .int 2]

-- The same call with the marker removed is refused rather than answered.
/-- info: Autoform.Core.EResult.exn (Autoform.Core.Val.str "TypeError") -/
#guard_msgs in #eval run withoutMarker [.str "%s", .int 1, .int 2]

/-- One field changes a refusal into an answer. This is the decoupling in miniature: the
artifact's behaviour differs on every variadic call, and no hole is emitted either way, so
no hole count distinguishes the two. -/
theorem marker_turns_a_refusal_into_an_answer :
    run withMarker [.str "%s", .int 1, .int 2] = .val (.tuple [.int 1, .int 2])
  ∧ run withoutMarker [.str "%s", .int 1, .int 2] = .exn (.str "TypeError") :=
  ⟨rfl, rfl⟩

/-! The synthetic body above reads the vararg name, which a real C body cannot do; it is the
shortest way to make the binding observable. The defect in the corpus was the binding itself,
not any use of it: `bindParams` packs the surplus arguments whenever the marker is present,
whatever the body does with them. -/

end Autoform.VariadicSpec
