# autoform

Turn an arbitrary codebase into autoformalized Lean 4 by mapping it onto a formal
interpreter written in Lean. See `STRATEGY.md` for the design and the build/buy audit.

**Approach:** formalize the *language* rather than the program. The program becomes data,
and every property is a theorem about `eval` applied to it.

**Generalization:** Joern's code property graph is a universal AST. C, C++, Java,
JavaScript, Python, Kotlin and binaries normalize to one node vocabulary, so one semantics
and one exporter cover all of them. There is no per-language transpiler.

## Use

```sh
./autoform.sh <source-dir> [ModuleName]   # translate + type-check + conformance + ledger
./assure.sh   <source-dir> <ModuleName>   # the above, plus audit, mutation gate, SACM case
```

```
source ──Joern──▶ CPG ──▶ neutral JSON AST ──▶ Lean Core program ──▶ trust ledger
                   │                                   │
                   └─▶ formalization graph             └─▶ differential vs real runtime
```

> **Numbers in this file go stale.** A dozen artifacts describe the same metrics and they
> drift apart. Regenerate rather than trust:
> `./autoform.sh <src> <Name>` prints the ledger; `python3 scripts/sacm.py --module <Name>`
> prints the assurance case. `docs/` explains what each number means.

## Verified end to end

| Corpus | Language | Functions | Verifiable core | Conformance vs real runtime |
|---|---|---|---|---|
| `cachetools` (real repo) | Python | see below | see below | see below |
| stress corpus | Python | 6 | 6 (100%) | **30/30 (100%)** vs CPython |
| sample | Python | 5 | 2 (40%) | **10/10 (100%)** vs CPython |
| ctest | C | 5 | 5 (100%) | **25/25 (100%)** vs `cc` |
| shortcircuit | Python | 1 | 1 (100%) | **6/6 (100%)** vs CPython |

All generated Lean type-checks. The "verifiable core" is the set of **hole-free**
functions — the only ones that can be verified unconditionally.

Three figures are reported, because one number would mislead (`STRATEGY.md` §17):
**hole-free** (no static holes) is an upper bound; **call-closed** additionally requires
every callee to resolve inside the program, and is the verifiable core;
**dynamic-hole risk** counts constructs that can still hole on some input.
Static hole-freedom does not imply the interpreter never holes — an untranslated callee
is invisible in the AST.

## The oracle

Each item below was found by the tooling, not designed in. On its first run the
differential harness found a bug:

```
DIVERGENCE fmod(6, -9): cpython=-3 lean=6
DIVERGENCE gcdish(16, -20): cpython=-4 lean=4
```

Python floors integer division and modulo; C and Java truncate toward zero. The
semantics had assumed one convention. The fix was not to patch an operator but to make
the semantics **dialect-parameterized** (`Core.Dialect`), with the transpiler recording
the source language. Mislabelling C as Python reproduces 7 divergences, so the harness
discriminates.

This is the failure mode `STRATEGY.md` §5 describes — a proof about a semantics that does
not match the runtime — caught automatically rather than by inspection.

## Layout

| Path | Layer | Role |
|---|---|---|
| `Autoform/Lang/Core/Syntax.lean` | 3 | Universal deep embedding: objects, heap, exceptions, containers, iteration. `Expr.hole`/`Stmt.hole` are the effect boundary. |
| `Autoform/Lang/Core/Semantics.lean` | 2 | Fuel-indexed total interpreter with an explicit heap, method dispatch, exceptions. Dialect-parameterized. No `sorry`, no `partial`. |
| `Autoform/Ledger.lean` | 6 | Coverage, holes-by-cause, verifiable core; JSON evidence for the assurance case. |
| `Autoform/Tactics/Portfolio.lean` | 5 | Tiered proof portfolio; records open obligations instead of admitting them. |
| `scripts/audit_all.py` | 6 | Axiom sweep over every declaration + source sweep for escape hatches. |
| `scripts/mutate.py` | 4 | Source-level mutation gate — the *sufficient* anti-vacuity test. |
| `scripts/sacm.py` | 6 | SACM assurance case + in-toto attestation. |
| `scripts/fvspec.py` | 4 | Vacuity screen over the FVSpec benchmark. |
| `Autoform/Harness/Audit.lean` | 6 | `#audit_axioms`, `#audit_depends`, `#audit_ledger` — Lean metaprogramming. |
| `Autoform/Harness/Conformance.lean` | 4 | Specimen-derived generators; the refutation gate. |
| `Autoform/Lang/Imp/*` | — | Minimal worked example with a proved `evalStmt_sound`. |
| `cartographer/formalization_graph.sc` | 1 | Joern query: call graph, effects, formalizability score. |
| `cartographer/export_ast.sc` | 3 | CPG → neutral AST. Deterministic; no LLM on this path. |
| `cartographer/render_lean.py` | 3 | Neutral AST → Lean. Infers dialect from file extension. |
| `scripts/differential.py` | 2 | Conformance oracle vs CPython / `cc`. |
| `Demo.lean` | — | Refutation gate, axiom audit, vacuity detection, ledger. |

## Design commitments

- **Nothing is silently dropped.** Untranslated constructs become holes tagged with the
  CPG node label that produced them, and the ledger counts them by cause.
- **Ignorance ≠ behaviour.** `outOfFuel` (didn't run long enough), `hole` (didn't
  translate), and a real value are three distinct outcomes.
- **The gate never manufactures its own evidence.** It uses `Testable.check`, never the
  `plausible` tactic, which closes goals with `sorry` — the thing the audit exists to
  catch.
- **Total semantics.** Structurally recursive on fuel; no `partial`, no `sorry`.

## Findings the tooling produced (not designed in)

- **Dialect arithmetic.** The differential harness caught Python's floored `%` against
  Lean's `Int`, which had mistranslated every C and Java program. Fix: the Core language
  is now parameterized by dialect.
- **Vacuity the dependency check cannot see.** The mutation gate scored `evalStmt_sound`
  at 25% (WEAK) — all six survivors were `evalBExpr` mutations, because `BigStep`'s side
  conditions are stated in terms of `evalBExpr` itself, so a mutation changes both sides
  of the equation. Adding independent characterization lemmas raised the reported score
  to 100%. That figure is **not attributable**: it was produced by the same
  `scripts/mutate.py` whose `error_lines` regex never matched this toolchain's
  diagnostics, so every "kill" came from the coarse build-failure fallback rather than
  from any individual theorem (see the trust chain below). The vacuity the lemmas were
  added to fix is real and was found by mutation; the 100% is not evidence that they
  fixed it. Re-running the gate on `Autoform/Lang/Imp/*` would settle it and has not been
  done.
- **41% of the FVSpec benchmark is vacuous under static screening.** 3,833 of 9,352
  analyzed problems. The dominant pattern: Python determinism tests (`f(x) == f(x)`)
  transliterated into Lean, where purity makes them `rfl`. Spec *translation* is not spec
  *preservation*.
- **Short-circuit evaluation returned a wrong answer.** `safemod(-11, 0)` returned `0` in
  CPython and raised `ZeroDivisionError` in Lean, because `b != 0 and a % b == 0` divided
  anyway. It had been conservative until exceptions were added — fidelity work makes other
  fidelity bugs findable, so the gaps are not independent.
- **A stale `.olean` made the oracle lie.** It answered with the previous semantics and
  produced 10 fictitious divergences before being caught. An oracle reading a stale cache
  is worse than no oracle: it is specifically wrong. Oracles must now establish they are
  reading the current artifact before reporting.
- **`<operator>.and`/`.or` are bitwise, not logical.** They had been mapped to `&&`/`||`,
  computing wrong answers. Now holes.
- **Static hole-freedom does not imply the program runs.** An untranslated callee is
  invisible in the AST, so the ledger reports hole-free, call-closed, and dynamic-hole
  risk as three separate numbers.

## Trust chain

Every link is mechanically checked, and each check is a different kind of oracle:

| link | oracle | status |
|---|---|---|
| semantics matches the real runtime | differential testing vs CPython / `cc` | **0 divergences**, but over **30 of 208** `cachetools` functions — coverage, not agreement, is the limit |
| specifications constrain behaviour | source-level mutation gate | **78/88 (88.6%)** on the translated module; 10 survivors, all analysed |
| proofs depend on no unsound axiom | axiom sweep over every declaration | clean, 1,696 decls |
| `.olean`s match a kernel replay | `leanchecker --fresh` | VERIFIED |
| untranslated code is declared | hole counting + SACM assumptions | 26 holes, all named |

The second row used to read "100%, HAS TEETH". That number was an artifact of the gate,
not a property of the specifications: `scripts/mutate.py`'s `error_lines` regex matched
the *older* Lean diagnostic format, so on this toolchain it never matched anything and
every "kill" came from the coarse "the build failed, credit all theorems" fallback. There
was no per-theorem attribution behind it. The on-subject score against
`Autoform/Generated/Cachetools.lean` is 78/88, with all 10 survivors analysed — 4 are
docstring deletions, 1 is an observably identical `.ret unit` → `.expr unit`, 2 are
operand swaps under a self-comparison witness, 2 sit behind a `Stmt.hole`. G4 is recorded
UNSUPPORTED rather than suppressing the equivalent mutants to turn it green.

The first row used to read "100% on all corpora", which was wrong in both directions.

It was wrong to say 100%, because the denominator is small: only 30 of 208 `cachetools`
functions are compared. Everything else is INCONCLUSIVE — a value the harness cannot
encode, a receiver it cannot build, or a hole. **The limit is reach, not agreement.** A
conformance rate quoted without its coverage is the self-flattering metric this project
keeps finding.

It was then briefly wrong in the other direction: an intermediate run reported 5
divergences, and this file attributed them to `class _HashedTuple(tuple)`. That
attribution was false. All five were an artifact of a **concurrent mutation run** holding
`Autoform/Generated/Cachetools.lean` — `_DefaultSize.pop` was a live mutant returning 0
instead of 1, and it is in that run's `decls` list. The harness now detects the
`.mutate-backup` sentinel, sets `build_stable: false`, and refuses to let a mutated module
be read as a divergence. See STRATEGY.md §33.

The `_HashedTuple` gap is real but separate: Core has no inheritance from builtin types,
so instances are opaque `Val.ref`s while CPython's instance *is* a tuple. It surfaces as
a counted `representation:value-vs-object` INCONCLUSIVE, not as a divergence, because the
oracle cannot compare the two encodings.

`leanchecker` ships with the Lean toolchain (v4.28.0+) — `lean4checker` is deprecated and
there is no Homebrew formula. **Use `--fresh`**: without it the checker can silently pass
a root module that has only imports, which is `Autoform.lean`'s shape.

## Not yet built

Boxed mutable containers (`Stmt.setIndex` is still a hole — design in
`docs/boxed-containers.md`); cross-scope *writes* (`nonlocal`; reads and closures work);
contracts at holes, so partially-translated functions can be reasoned about under stated
assumptions; `Val.float` (an IEEE-754 model exists in `Autoform/Lang/Core/Float.lean` and
is **not yet wired into the semantics**, so floats still hole). `op:starredUnpack` is
**closed** (STRATEGY.md §35) — Core now has a variadic calling convention; what is left of
it is default parameter values, keyword-only parameters, and starred *destructuring*.

## Dependencies

Lean 4.30.0-rc1 · [Specimen](https://github.com/strata-org/specimen) ·
[Plausible](https://github.com/leanprover-community/plausible) ·
[Joern](https://github.com/joernio/joern) 4.0.606 · Python 3 · a C compiler (for C conformance)
