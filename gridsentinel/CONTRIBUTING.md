# Contributing to GridSentinel

Read `docs/PROOF.md` §8 ("what is NOT proved") and `docs/THREATMODEL.md` §4
before you change anything in the trusted plane. This repository's value is
that its claims are calibrated; a change that improves the numbers and
degrades the honesty of the write-up is a regression.

---

## 0. The environment gotcha — read this first

**On macOS, always invoke the interpreter as:**

```sh
arch -arm64 .venv/bin/python ...
```

**and never wrap it in `timeout`.**

Why: `.venv/bin/python` is a *universal* binary. It selects its architecture
slice from the parent process. This machine's `timeout` (and `gtimeout`) are
x86_64, so `timeout 60 .venv/bin/python ...` starts CPython in its x86_64
slice — whereupon:

* **z3 fails outright.** `libz3.dylib` is arm64-only; the import dies.
* **pandapower crawls.** Everything runs under Rosetta, and the load-flow-per-
  millisecond harnesses become unusable.

The failure looks like a z3 import error or a mysteriously slow run, and
several people have lost an afternoon to it. It is encoded in the `Makefile`
(`ARCH := arch -arm64` on Darwin/arm64), so **prefer `make` over calling the
interpreter directly** and the problem cannot recur.

If you need a time limit, do not use `timeout`. Bound the work instead
(`--n-per-family`, `--horizon`), or run the command in the background and stop
it yourself.

This is macOS-local. CI runs on linux x86_64 runners where `arch -arm64` does
not exist and is not needed; the Makefile detects `uname` and leaves the
prefix empty there.

---

## 1. Getting set up

```sh
make install        # venv (if absent) + editable install + dev extras
make                # the target list
```

| Command | What it does | Runtime |
|---|---|---|
| `make test` | pytest over `tests/` (75 tests) | ~2.5 min |
| `make verify` | the Z3 proof suite; non-zero exit on a proof regression | ~1 min |
| `make experiment` | `run.py` → `out/results.json` + figures | minutes |
| `make attacks` | `run_v2.py` → `out/results_v2.json` + figures | minutes |
| `make figures` | re-render from existing JSON, no re-run | seconds |
| `make lint` | ruff if installed, else pyflakes, else a syntax check | seconds |
| `make all` | install, test, verify, both harnesses | |
| `make clean` | caches and build artefacts (keeps `out/`, `models/`) | |

`SEED`, `N_PER_FAMILY` and `HORIZON` are overridable: `make experiment SEED=7`.

Console scripts, installed by `make install`, are equivalent and are what CI
uses: `gridsentinel-experiment`, `gridsentinel-attacks`, `gridsentinel-verify`,
`gridsentinel-report`. They live in `gs/__main__.py` and exist because
`run.py` and `gs.verify.main()` return result dictionaries rather than exit
statuses — `gridsentinel-verify` adds the pass/fail gate that makes a proof
regression fail a build.

Python 3.9 is the floor and what everything is developed against.

---

## 2. File ownership

Do not edit a file you do not own without talking to its owner. Signatures in
`INTERFACES.md` are frozen.

| Path | Owner / role |
|---|---|
| `gs/power.py` | power-system model (pandapower load flow) |
| `gs/measure.py`, `gs/scenarios.py`, `gs/relay.py` | telemetry, scenarios, conventional protection |
| `gs/ai.py`, `models/` | the untrusted plane |
| **`gs/shield.py`** | **frozen spec artifact.** v1 shield. See §4. |
| **`gs/monitor.py`** | **frozen spec artifact.** v2 reference monitor. See §4. |
| `gs/plant_drive.py` | the VFD/rotor plant, and the authority for every commissioning constant the monitor imports |
| `gs/attacks.py` | the adversary catalogue |
| `gs/verify.py` | the Z3 proofs |
| `spark/` | the SPARK Ada mirror of the shield |
| `run.py`, `run_v2.py`, `tests/`, `gs/report*.py` | harnesses, tests, reporting |
| `docs/PROOF.md` | what is and is not proved |
| `docs/THREATMODEL.md` | adversary model and residual risk |
| `docs/OPERATIONS.md` | the deployment-facing manual |
| `pyproject.toml`, `Makefile`, `.github/`, `CONTRIBUTING.md` | packaging, build, CI |

`INTERFACES.md` is the contract between all of them. Changing a signature in
it is a cross-cutting change and needs every downstream owner's agreement.

---

## 3. Layering rules that are not negotiable

* **The trusted plane never imports the untrusted plane.** `gs/shield.py` and
  `gs/monitor.py` do not import `gs/ai.py`, and never will.
* **`gs/plant_drive.py` must never import `gs/monitor.py`.** The monitor
  imports the plant for *commissioning data only* (qualified band, slew limit,
  critical bands) — no plant state, no plant model. There is deliberately no
  local fallback copy of those numbers: a fallback is drift, spelled
  differently.
* **Conventional protection is OR-ed at the output and never mediated (I6).**
  If a change makes it possible for the shield to inhibit the baseline relay,
  the change is wrong, however good the test results look.
* **`decide` stays pure.** No I/O, no allocation, no unbounded loops,
  integers and booleans only; all state updates live in `commit`. This split
  is *why* the logic can be enumerated exhaustively and k-induction closes.
  Move one line of state mutation into `decide` and the proof method breaks.

---

## 4. The rule for `gs/shield.py` and `gs/monitor.py`

> **Any change to `gs/shield.py` or `gs/monitor.py` requires `make verify`
> (i.e. `gs/verify.py`) to pass on the same commit, before merge.**

Not afterwards, and not "it's only a comment" — a comment in these files is
frequently the argument for a constant.

A shield change is complete when all of the following are true:

1. `make verify` passes all four gates.
2. Any theorem whose constants moved has been **re-derived**, not merely
   re-run. A theorem that still passes because it was restated around the new
   value proves nothing.
3. `make test` passes.
4. `docs/PROOF.md` is updated, including "what is NOT proved".
5. The `spark/` mirror is updated so the two artifacts do not diverge — and
   the note that it carries no `gnatprove` evidence stays.
6. Both harnesses have been re-run and the results diffed.

Defect history lives in `docs/PROOF.md` §7 and in `prove_v1_regressions()`.
Every historic defect is a permanent regression theorem. **Never delete one**
— if it becomes inconvenient, that is the strongest possible reason to keep
it.

---

## 5. Adding a scenario

Scenarios are benign/fault episodes for the v1 line experiment; attacks are
adversary episodes for the v2 catalogue. They live in different files.

**A benign or fault scenario** (`gs/scenarios.py`, owner A2):

1. Add it to `catalogue()` with a `family` name. Families are the unit of
   reporting — a scenario in a new family changes every table.
2. Set `internal_truth` honestly. It is the ground truth every false-trip
   count is computed against; getting it wrong flatters or damns an arm for
   no reason.
3. Confirm `gs/measure.py` can materialise it. Power-swing scenarios can walk
   past the steady-state stability limit and fail to converge — such episodes
   are **counted and reported, never silently dropped**, because dropping
   them quietly shrinks the family and flatters every arm.
4. `make experiment` and check the family appears with a sane episode count.

**An attack** (`gs/attacks.py`):

1. Add it to `catalogue()` with the expected verdict.
2. State which invariant is supposed to stop it, and be prepared for the
   answer to be "none of them". A `judge`d attack that is granted is a
   finding, not a bug to be hidden — the false-data-injection result got into
   the headline exactly this way.
3. Do **not** credit an invariant with a block it did not perform. E3 was
   once credited with six blocks that were really I1's directional element.
   Run the probe and read the veto reason.
4. `make attacks` and check the new row.

---

## 6. Adding an invariant

1. **State it in English first**, in the module docstring of the artifact that
   enforces it, next to the kill-chain step it addresses. If it cannot be
   stated in a sentence, it cannot be proved either.
2. **Give it its own veto reason**, a distinct named constant. The veto
   spectrum is a detection signal (`docs/OPERATIONS.md` §1.1); reusing an
   existing reason destroys it. Add the new reason to the tables in
   `docs/OPERATIONS.md` §2.
3. **Put the numeric part in the reduction layer** and let `decide` see one
   boolean. This is what keeps layer 2 finite-state.
4. **Encode it in `gs/verify.py`.** Assert the negation and require `unsat`;
   attack it with BMC first, then close with k-induction and report the
   smallest k.
5. **Report bounded results as bounded.** Anything that only survives BMC to
   depth N is "bounded-to-N", never "proved". This is the house honesty rule
   and it is not optional.
6. **Add a property test** in `tests/` — hypothesis for the numeric layer,
   exhaustive enumeration for the state machine where the space allows it.
7. **Write down what it does *not* cover** in `docs/PROOF.md` §8. Every
   invariant in this repository has a limit; an invariant presented without
   one is under-specified.

---

## 7. Style and tone

* Line length 79, `target-version = py39`. Lint is **advisory**: `ruff` must
  never be a reason to reformat `gs/shield.py` or `gs/monitor.py`, which are
  written to be read by a reviewer rather than by a style bot.
* Comments in the trusted plane explain *why a constant has that value* and
  *what defect the code exists to prevent*. Historic-defect comments are
  load-bearing documentation — do not tidy them away.
* **Do not overstate results anywhere.** No document in this repository may
  read like marketing. Specifically, and permanently:
  * the headline safety claim **is falsified** under a local merging-unit key
    compromise, and the FDI grants still appear in `run.py` output;
  * `gnatprove` was never available, so the SPARK artifact carries **no
    machine evidence**;
  * the Z3 proofs are over the **reals** apart from a small layer-0 IEEE-754
    fragment, and a proof over the reals is not a proof about the arithmetic
    the appliance executes;
  * detection is **containment, not prevention**, and every DETECT verdict is
    conditional on a human acting in time.
  If your change makes one of those statements less true, change the
  statement in the same commit — in both directions.

---

## 8. Before you open a pull request

```sh
make lint
make test
make verify        # mandatory if you touched gs/shield.py or gs/monitor.py
make experiment
make attacks
```

CI runs the same four (tests, proofs, both harnesses on seed 0) on linux, and
fails on a test failure or a proof regression. It deliberately does **not**
fail on the known FDI grants: those are expected output recorded in
`docs/PROOF.md` §8.7, and asserting on them belongs in `tests/`, not in CI.
