import Autoform.Lang.Core.Semantics

/-!
# A character literal is a number, not a string

`cartographer/export_ast.sc`'s literal dispatch had no case for a bare single-quoted
literal. It fell through to a generic "starts with a quote" branch and rendered `'x'`
identically to `"x"`. In C a single-quoted literal is a *number*, the character's own
codepoint. `Expr.strByte` already correctly yields that byte as an `Int`, so `*p == 'x'`
became an integer-versus-string comparison, which is never equal. The loop below therefore
compiled with **zero holes** and returned 0 for every input.

Measured with `cc -O0`:

```c
static int count_x(const char *s, int n) {
    int c = 0;
    for (const char *p = s; p < s + n; p++) if (*p == 'x') c = c + 1;
    return c;
}
count_x("axxbxcdef", 9) == 3
count_x("axxbxcdef", 3) == 2
count_x("axxbxcdef", 1) == 0
```

The two Core programs below differ in exactly one leaf: the literal compared against the
byte. `asNumber` is what the exporter now emits and reproduces all three values.
`asString` is what it emitted before and returns 0 for every input, and it is kept as a
negative control for the same reason `DoWhileSpec` keeps its `while` shape: this defect
never appeared as a hole, so nothing in the coverage ledger would notice a regression to
it. `#guard_msgs` fails the build if either value changes, and unlike `native_decide` it
introduces no axiom.
-/

namespace Autoform.CharLiteralSpec

open Autoform.Core

private def C : Ctx := { dialect := .cLike, table := [], globals := 0 }

/-- The subject string, `"axxbxcdef"`. Bytes 1, 2 and 4 are `'x'`. -/
private def subject : Expr := .lit (.str "axxbxcdef")

/-- `int c = 0; int i = 0; while (i < n) { if (strByte(s,i) == X) c = c+1; i = i+1 } return c;`
parameterised on the literal `X` the byte is compared against. -/
private def countWith (X : Expr) : Func :=
  { name := "count_x", params := ["n"]
  , body :=
      .seq (.assign "c" (.lit (.int 0)))
      (.seq (.assign "i" (.lit (.int 0)))
      (.seq (.loop (.binop "<" (.name "i") (.name "n"))
              (.seq (.ifte (.binop "==" (.strByte subject (.name "i")) X)
                      (.assign "c" (.binop "+" (.name "c") (.lit (.int 1))))
                      .skip)
                    (.assign "i" (.binop "+" (.name "i") (.lit (.int 1))))))
            (.ret (.name "c")))) }

/-- What the exporter emits now: `'x'` as its codepoint, 120. -/
private def asNumber : Func := countWith (.lit (.int 120))

/-- What the exporter emitted before: `'x'` as the string `"x"`. Retained as a negative
control. It is hole-free, well-typed, and wrong for every input. -/
private def asString : Func := countWith (.lit (.str "x"))

private def run (f : Func) (n : Int) : EResult :=
  (applyFunc C 4000 [] f none [.int n] []).2

/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 3) -/
#guard_msgs in #eval run asNumber 9
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 2) -/
#guard_msgs in #eval run asNumber 3
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 0) -/
#guard_msgs in #eval run asNumber 1

-- The defective shape: 0 for every input, including the two where `cc` prints 3 and 2.
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 0) -/
#guard_msgs in #eval run asString 9
/-- info: Autoform.Core.EResult.val (Autoform.Core.Val.int 0) -/
#guard_msgs in #eval run asString 3

/-- The fixed shape agrees with `cc` on all three inputs. -/
theorem asNumber_matches_cc :
    run asNumber 9 = .val (.int 3)
  ∧ run asNumber 3 = .val (.int 2)
  ∧ run asNumber 1 = .val (.int 0) :=
  ⟨rfl, rfl, rfl⟩

/-- The defect was not a hole and not a type error but a wrong answer: on the same input
the two shapes return 3 and 0, so the fix is not cosmetic. -/
theorem asNumber_differs_from_asString :
    run asNumber 9 = .val (.int 3) ∧ run asString 9 = .val (.int 0) :=
  ⟨rfl, rfl⟩

end Autoform.CharLiteralSpec
