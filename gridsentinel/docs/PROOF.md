# GridSentinel — verification report for the trusted shield

**Artifact under verification:** `gs/shield.py` **v6** (frozen; unmodified by this work)
**Prover:** Z3 5.1.0 via `z3-solver`, driven by `gs/verify.py`
**Shipping mirror:** `spark/shield.ads` / `spark/shield.adb` (SPARK 2014, **not** compiled or proved here — §8.6)
**Reproduce:** `arch -arm64 ./.venv/bin/python gs/verify.py`
(the venv interpreter is a universal binary; a wrapper such as the x86_64 `timeout` forces
the child into x86_64 and the arm64 `libz3.dylib` then fails to load — never run it under `timeout`)

The tool no longer prints a hand-written version number for the artifact. It prints a
**derived fingerprint** — `sha256` of the frozen source, plus the constants that
characterise its behaviour, all read from the module at run time:

```
Artifact under verification: gs/shield.py  [frozen; sha256:21e508978fae]
  characterising constants read from the artifact: MAX_GRANTS=2 WINDOW_MS=1000 DWELL_MS=2
  VETO_LIMIT=24 EXCURSION_LIMIT=24 MAX_CLOCK_STEP_MS=100 REQUIRE_LOCAL_PROVENANCE=True
```

A version number in that banner would have been the same failure mode as the stale A8C
row: asserted rather than checked, silently wrong after the next patch, and trusted by a
reader. **Everything the suite announces about the artifact is now derived from the
artifact.** §7.6.

---

> ## READ THIS FIRST — assumption A8 is now SPLIT: one half proved, one half not
>
> `i_diff = |I_local + I_remote|` is a **sum**. Every theorem that concludes
> anything from `diff_ok` is only as good as the provenance of **both** addends.
> Until v5 that was a single assumption, it was violated, and — the reason this
> banner has been rewritten rather than deleted — it **conflated two adversaries
> who behave nothing alike**.
>
> **A8-LINUX — the adversary owns the inference plane but holds no merging-unit
> signing key. → DISCHARGED. Now theorem A8L.**
> `decide` requires `local_ok` alongside `remote_ok`. Such an adversary cannot
> present a sample the shield will read at all, whatever numbers it contains.
> A8L: with local provenance unauthenticated, **zero grants over any trace**,
> with `i_diff`, `i_restraint` and both requested settings free at every step.
> This is the half that was actually being exploited — 25 of 25 tuned episodes.
>
> **A8-MU — the adversary *holds* the local merging unit's own signing key.
> → STILL AN ASSUMPTION.**
> Their forgeries verify. `local_ok` is true for them *by construction*, so
> authentication is blind to them and **DW5 stands exactly as it did**: a
> constant forged differential of 0.1133 pu, held steadily on an honest clock,
> obtains a grant for any run length. **No value of `DWELL_MS` closes it.** The
> residual is bounded only by non-exportable HSM key custody and attestation —
> **neither of which is modelled, tested or proved anywhere in this report.**
>
> **v5 did not solve false data injection. It cut it in two and solved the
> larger half.** Read any "PROVED" below as scoped to A8-MU holding.

---

The safety claim being defended is *not* "the neural network is good". It is:
**whatever the network proposes — including a fully hostile network proposing
an accelerated trip every millisecond with arbitrary, negative, infinite or NaN
parameters, on a clock it can spoof in either direction — the shield's output
is safe**, *given A8*. Everything below is about the shield.

> **Six defects have been found and fixed.** They are recorded in §7 with their
> counterexamples and re-run on every invocation as regressions R1–R6 plus the
> live A8C gate. Two of the six (D3, D6) were raised by *this report* against a
> previous version of itself rather than by the solver — a solver only refutes
> the theorems you write down.

---

## 1. Version history

| | v1 | v2 | v3 | v4 | v5 | **v6** |
|---|---|---|---|---|---|---|
| Rate limiter | one scalar, **jumping** window | `grant_times`, **sliding** window | — | — | — | — |
| Clock | monotonicity **assumed** (A5) | one-sided **watermark** | two-sided **plausibility window** | — | — | — |
| `RESTRICTED` | provably decorative | `effective_cert` | — | — | — | — |
| Non-finite input | accidental | explicit, both directions | — | — | — | — |
| Counters | one, shared | — | — | **split** `vetoes` / `excursions` | — | — |
| Recovery | impossible | — | — | **authenticated `reinstate`** | — | — |
| Corroboration | **one sample** | — | — | **`DWELL_MS = 2`** | — | — |
| Provenance | remote addend only | — | — | — | **both addends** (`local_ok`, `R_LOCAL`) | — |
| **I2 status** | **disproved** without A5 | proved, free clock | proved | proved | **still proved, free clock** | **still proved** |
| **DoS status** | n/a | watermark **poisonable** | proved immune | proved immune | proved immune | proved immune |
| **A8 status** | violated | violated | violated | violated | **A8-LINUX discharged; A8-MU still assumed** | unchanged |
| Compat. defaults | — | — | — | — | **fail OPEN** (A8C) | **fail CLOSED**, one rule, live gate |

The result that must survive every future patch, and did: **I2 holds with no
assumption about the clock whatsoever.**

---

## 2. Assumptions

| # | Assumption | Where it enters | If violated |
|---|---|---|---|
| **A1** | CT / MU magnitude error ≤ **12 %** of through-current | T1, T3 | The floor loses its margin; §4.3 |
| **A2** | Charging residual ≤ **0.02 pu** after compensation | T1, T3 | Same |
| **A3** | The remote **and local** merging-unit channels are **authenticated and fresh**, and the operator channel carrying `reclose_auth` and `reinstate` is likewise authenticated | I1, I1-local, S6 | An attacker who forges it supplies one corroboration free, and can rearm a disowned shield |
| **A4** | The shield runs on **isolated hardware**; the model's only channel is the `Proposal` record | all of Layer 2, S7 | Every invariant is void |
| **A6** | Real arithmetic in Layers 1–2 | T1–T5, I5, I5b | Partly mitigated by Layer 0; §8.2 |
| **FPM** | `fl(x·y) ≥ fl(K_MIN·y)` for `x ≥ K_MIN, y ≥ 0` | N3 only | **Z3 does not close it in 45 s; ASSUMED** |
| **A7** | `MAX_CLOCK_STEP_MS = 100` exceeds any legitimate inter-sample gap | TRANSPARENCY, P4, P5 | Honest samples vetoed as jumps. An **availability** parameter: too small costs service, never safety |
| ~~**A8**~~ | ~~both terms of `i_diff` come from merging units whose keys the adversary does not hold~~ | — | **SPLIT IN v5.** The single form conflated two adversaries; see the two rows below |
| **A8-LINUX** | the adversary owns the inference plane but holds **no merging-unit key** | — | **DISCHARGED — no longer an assumption.** It is now theorem **A8L**, with **I1-local** and **I1-both** as the invariants. Moved from this table into the proved column |
| **A8-MU** | **the adversary does not hold the local merging unit's own signing key** | **the entire I1 family, I5, I5b, T2, T3, DW1–DW4** | **STILL AN ASSUMPTION.** Their forgeries verify, so authentication cannot see them and **DW5 stands unchanged**. The shield's logic remains correct and its conclusions become worthless, because it is reasoning about a number the attacker chose. §8.7 |

### ~~A5 — the sample clock is monotone~~ **RETIRED IN v2, still retired**

`gs/verify.py` runs with `clock="free"`: `now_ms` is an unconstrained integer
at every step. Regression R3 is the theorem that this is sound.

---

## 3. Method

Three layers. **Layer 0**: IEEE-754 `Float64`, genuine NaN and ±∞. **Layer 1**:
real arithmetic, each theorem discharged by refuting its negation — a proof over
the continuum, replacing `lemma_sensitivity_floor`'s 200 001 samples. **Layer 2**:
`decide` + `commit` + `Shield.step` as a symbolic transition relation over
`(mode, latched, grant_times[0..2], vetoes, excursions, diff_run, last_seen_ms)`
plus ghosts (`g1..g4`, `ng` for the rate limit; `dprev1..3` for the dwell;
`vmax` for the trust tier). Ghosts appear in no guard, so adding them is sound.

Every input is a free variable re-chosen each step — the proposal, the four
finiteness flags, `cert_ok`, the booleans, `reclose_auth`, `baseline_trip`,
`reinstate`, **and `now_ms`**. `diff_ok` is *not* free: it is derived from the
numeric layer through `effective_cert`, so the layers are chained.

Per property: **BMC first**, then **k-induction** from k = 1, retrying each k
with the simple-path restriction. Anything that survives BMC but never closes is
reported `BOUNDED-ONLY`, never proved.

---

## 4. Layers 0 and 1

### 4.1 Layer 0 — non-finite handling

| | Verdict | ms |
|---|---|---|
| **N1** non-finite measurement fails closed | **PROVED** | 0.3 |
| **N2** non-finite request cannot deny service | **PROVED** | 0.2 |
| **N4** finite negative `i_restraint` clamps to zero | **PROVED** | 0.2 |
| **FPM** `fl(x·y) ≥ fl(K_MIN·y)` | **ASSUMED — `unknown` at 45 s** | 45 100 |
| **N3** clamp theorem in binary64, **modulo FPM** | **PROVED** | 45 |

N2 is proved with an *uninterpreted* multiplication — stronger than for `fpMul`,
since the equivalence then holds for any multiplication at all. N3 abstracts both
products to fresh FP variables related only by FPM, so it checks the clamp logic
over FP *comparison* semantics with no multiplication in it; direct attempts
(bounded and unbounded) returned `unknown` at 45–60 s.

### 4.2 Layer 1 — real arithmetic

T1, T1b, **T2** (clamp non-defeat, adversarial and non-finite requests), T4, **T3**
(A1/A2 noise never admitted), T5 (request monotonicity) — **all PROVED**, 0.2–4 ms.

### 4.3 Worst-case safety margin (Z3 `Optimize`)

    inf over ir >= 0 of  max(P0_MIN, K_MIN*ir) - (A1*ir + A2)
      =  1/50 pu = 0.0200 pu exactly,  attained at ir = 1/2 pu

Slope headroom `K_MIN − A1 = 0.08`. **If CT error ever reaches 20 %, T1 becomes
false for all large `ir`** — the spurious differential then grows at least as
fast as the threshold, with no saturation term to rescue it.

---

## 5. Layer 2 — the logic invariants

**Clock assumption: none.**

### 5.1 Core invariants

| Property | Verdict | k | time |
|---|---|---|---|
| **W** well-formedness | **PROVED** | **1** | 1 029 ms |
| **I1** no-trip-without-physics | **PROVED** | **1** | 39 ms |
| **I1-local** *(v5)* both addends authenticated and fresh | **PROVED** | **1** | 38 ms |
| **I1-both** *(v5)* I1 ∧ I1-local composed — **A8-LINUX as a theorem** | **PROVED** | **1** | 38 ms |
| **I3** latch until `reclose_auth` | **PROVED** | **1** | 36 ms |
| **I4** `grant ⟹ time_quality_ok` | **PROVED** | **1** | 35 ms |
| **I4b** no grant on an implausible timestamp | **PROVED** | **1** | 36 ms |
| **P1** `grant ⟹ ls ≤ now ≤ ls + 100` | **PROVED** | **1** | 39 ms |
| **P4** a plausible timestamp is never time-vetoed | **PROVED** | **1** | 37 ms |
| **P6** clock-advance bound | **PROVED** | **1** | 38 ms |
| **I5** certified region | **PROVED** | **1** | 167 ms |
| **I5b** hard floor unconditional | **PROVED** | **1** | 254 ms |
| **I6** baseline pass-through | **PROVED** | **1** | 39 ms |
| **I8** non-finite measurement never grants | **PROVED** | **1** | 40 ms |
| **DWELL** *(v4)* grant ⟹ sustained corroboration | **PROVED** | **1** | 41 ms |
| **S5** *(v4)* either counter alone disowns | **PROVED** | **1** | 44 ms |
| **TRANSPARENCY** (restated, §5.2) | **PROVED** | **1** | 47 ms |
| **I2** rate limit, *bare* | **BOUNDED-ONLY (depth 12)** | — | 935 ms |
| **I2** rate limit, strengthened with **W** | **PROVED** | **1** | 1 338 ms |
| **I2** rate limit, **order-agnostic, FREE CLOCK** | **PROVED** | **1** | 1 973 ms |
| **I7a** mode monotone **absent a reinstate** | **PROVED** | 1 | 1.9 ms |
| **I7b** `BASELINE_ONLY` absorbing **absent a reinstate** | **PROVED** | 1 | 0.4 ms |
| **I7c** no grant in `BASELINE_ONLY` | **PROVED** | 1 | 0.04 ms |
| **I7d** requests cannot lower the veto count | **PROVED** | 1 | 0.7 ms |
| **I7e** vetoes cleared only by a grant or a reinstate | **PROVED** | 1 | 1.3 ms |
| **I7g** *(v4)* an excursion advances the **excursion** counter | **PROVED** | 1 | 0.8 ms |
| **I7f/decide** NORMAL ≡ RESTRICTED *at decide level* | **PROVED** | 1 | 0.7 ms |
| **I7f/step** RESTRICTED observably weaker *at step level* | **WITNESS** (intended) | — | 1.5 ms |
| **I7f/band** withdrawn band is exactly `[nominal, floor)` | **PROVED** | 1 | 1.3 ms |
| **P2a** an excursion never moves the watermark | **PROVED** | 1 | 0.4 ms |
| **P2b/P2c** watermark monotone; only takes an **accepted** timestamp | **PROVED** | 1 | 1.8 ms |
| **P3** a burst of N spoofs leaves it fixed | **PROVED** (N=1..6; unbounded by induction from P2a) | — | 7 ms |
| **P5** a spoof burst cannot deny service to the honest **run** after | **PROVED** (N=1..6) | — | 14 ms |
| **P7** 24 excursions still disown, via the **separate** counter | **PROVED** | — | 16 ms |

### 5.2 TRANSPARENCY, restated for v4 — say the new form out loud

The v3 property was *"corroboration now ⟹ grant now"*. **That is no longer the
property, and pretending otherwise would be the easiest way to overstate this
report.** v4 requires the corroboration to have been sustained. Both halves are
stated and both are proved:

**TRANSPARENCY (one-step, restated).** For all states and inputs:

    want_trip and mode = NORMAL and not latched and rate budget available
      and not clock_excursion
      and time_ok and remote_ok and forward and diff_ok
      and diff_run + 1 >= DWELL_MS          <-- NEW, and stated as a
                                                PRECONDITION, not hidden
    =>  grant

The dwell appears as an explicit hypothesis. A reader who only saw this would
rightly ask whether the shield can now refuse forever, which is why the second
half exists:

**DW4 / TRANSPARENCY_SUSTAINED (multi-step).** From a clean state, `DWELL_MS`
consecutive fully-corroborated in-window proposals **contain a grant**. Proved
by unrolling exactly `DWELL_MS` steps — which is the whole of the property's
lookback, so this is a proof, not a bounded approximation.

Together: **the dwell is a delay of `DWELL_MS` samples (~2 ms), not a veto.**
The shield still never gratuitously refuses a good model; it now insists the
model be right twice running, as the 87L element beside it insists on six.

### 5.3 The dwell theorems (new in v4)

| | Verdict | ms |
|---|---|---|
| **DW1** grant ⟹ 2 consecutive corroborated samples (**ghost-free**) | **PROVED** | 0.5 |
| **DW2** an isolated single-sample spike can never produce a grant | **PROVED** | 0.5 |
| **DW3** every sample of the run cleared the hard floor, not just the last | **PROVED** | 13 |
| **DW4** `DWELL_MS` good samples **do** produce a grant | **PROVED** | 0.6 |
| **DW5** **a steady forgery defeats any dwell — *MU-key adversary*** | **SHOWN (`sat`, as expected)** | 5 |
| **A8L** *(v5)* **the Linux-plane adversary obtains no grant** | **PROVED** | 1.5 |
| **A8C** *(v6)* the compatibility paths **fail closed** — live gate | **CLOSED** | — |

`DWELL` in the main table is stated over the ghost history and closes at k = 1.
**DW1 re-derives the same claim without mentioning a ghost**, by unrolling
`DWELL_MS` steps — an exact unrolling, since the property's entire lookback is
`DWELL_MS` samples.

**DW5 is a negative result and the most important row in this section. v5 did
not change it — v5 changed its scope.** `sat` is still the expected outcome: a
constant `i_diff = 0.1133 pu`, parked just above `P0_MIN` and held for
`DWELL_MS + 4` consecutive samples on a perfectly honest clock, obtains a grant.
The construction is uniform in the run length, so **no value of `DWELL_MS`
rejects it.**

What changed is one assertion in its encoding: `fs[i].local_ok` is now
explicitly **true**, and that single line *is* the difference between the two
threat models. Holding the local merging unit's key is exactly the capability
that makes `local_ok` true for an adversary, so DW5 is now, precisely, the
**A8-MU** result and nothing wider.

**A8L is its complement, and is the v5 discharge.** An adversary owning the
inference plane but holding no merging-unit key is given everything else —
arbitrary `i_diff` and `i_restraint` at every step, arbitrary `req_p0`/`req_k`,
a perfect clock, perfect remote provenance, perfect direction and time quality,
a trip request every millisecond — and obtains **zero grants** over the whole
trace. `unsat`. The one thing they lack is a valid local signature, and it is
sufficient.

Together the two rows say the useful thing: *the shield is now immune to the
adversary that was actually beating it, and remains defenceless against an
adversary who has stolen a key from the instrument it trusts.* Those are very
different engineering problems, and conflating them — as the single A8 did — was
hiding the second behind the first.

**A8C was an observation I raised against v5; it is now CLOSED, and the row is
a live gate rather than a comment.** Both backward-compatibility paths used to
substitute a permissive `local_ok`:

* `decide` accepted a five-element input tuple and substituted `local_ok = True`;
* `Shield.step` read provenance via `getattr(sample, "local_authentic", True)`.

An un-updated caller therefore kept running, kept granting, and got **no
indication that A8-LINUX was no longer discharged for it**. A deployment that
missed a single call site silently got D5 back.

**The fix (v6):** one module constant, `REQUIRE_LOCAL_PROVENANCE = True`, governing
**both** paths — `decide`'s legacy form now sets `local_ok = not
REQUIRE_LOCAL_PROVENANCE`, and `Shield.step` reads
`getattr(sample, "local_authentic", _absent)` with `_absent = not
REQUIRE_LOCAL_PROVENANCE`. That there is exactly *one* rule matters as much as
its polarity: leaving the second path permissive is precisely how the hazard
arose the first time. **A default is not an authentication.**

Three things about how this row is now written, because the row itself was the
last piece of drift in this suite:

1. **Its name, verdict and statement are all derived from the probe**, never
   static strings. It reads `CLOSED` while both paths refuse and reverts to
   `A8C compatibility paths FAIL OPEN -- DEPLOYMENT HAZARD` the moment either
   goes permissive. A static "FAIL OPEN" headline sitting above a detail line
   reading `defaults open = False` is documentation drift *inside the proof
   suite* — a reader scanning verdicts would see a live hazard that no longer
   exists, which is exactly how a stale line becomes a false finding.
2. **It probes behaviourally, by calling the shield, not by grepping its
   source.** The v5 detector string-matched `'local_ok = True'`; a refactor
   that reintroduced the hazard with different wording would have slipped past
   it — the very failure mode the row exists to catch. It now calls `decide`
   with a five-element tuple (with `diff_run` primed so the dwell is already
   satisfied, making the local guard the *only* thing that can refuse) and runs
   `Shield.step` on a sample object carrying no provenance attributes at all.
3. **It carries a negative control, so it cannot pass vacuously.** The detector
   flips `REQUIRE_LOCAL_PROVENANCE` to `False`, confirms both probes go
   permissive again, and restores it. If the control does not fire the row
   reports `DETECTOR INERT` regardless of what the main probe returned.

`proved` for this row is now the gate value, not a recorded fact, and it feeds
the Layer-2 aggregate. Verified by simulation: with `REQUIRE_LOCAL_PROVENANCE`
forced `False`, the row flips to `HAZARD OPEN` **and
`prove_shield_invariants()['proved']` goes `False`** — the whole layer goes red,
not just one line.

The SPARK mirror still cannot express this hazard at all: `Local_Ok` is a field
of `Inputs_T` and `Local_Authentic`/`Local_Fresh` are fields of `Sample_T`, so a
stream lacking them does not typecheck. That remains one concrete place the Ada
artifact is structurally stronger than the Python. §7.6.

---

## 6. RESTRICTED, at two levels

**At `decide` level: NORMAL and RESTRICTED remain indistinguishable** (proved) —
`decide` reads `mode` only as `== BASELINE_ONLY`, by design, which is what keeps
its `Contract_Cases` complete. **At `Shield.step` level: RESTRICTED is observably
weaker** (witness), via `effective_cert`. **And the difference is exactly the
right size**: `I7f/band` proves every distinguishing input lies strictly between
the hard floor and the nominal threshold. Quoting the wrong level misleads in
opposite directions.

---

## 7. Defect history

All re-run every invocation as R1–R5.

### 7.1 D1 — rate limiter defeatable by a backwards clock jump *(v1 → v2)*

v1 used a single `last_grant_ms` and a **jumping** window; nothing required
`sample.t` to be monotone. Z3 counterexample, BMC depth 7:

```
grants at t = {0, 998, 999, 1000} ms
the subset {0, 998, 999} spans 999 ms < WINDOW_MS = 1000
=> THREE accelerated trips inside one 1000 ms window, against MAX_GRANTS = 2
```

The grant at `t = 1000` looked old relative to `last = 0`, so `commit` reset the
budget; the clock then stepped back and the fresh budget was spent inside the
original window. **Detecting it required four grant timestamps of history, not
three** — the violating triple is not the most recent three grants, so a
three-deep encoding would have declared v1 safe.

| regression | v1 | v2/v3 | **v4** |
|---|---|---|---|
| **R1** the exact attack timestamps, maximised | 3 grants | 2 | **1** (dwell tightens it further) |
| **R2** strictly decreasing clock, 10 steps | 3 obtainable | 1 | **0** (the first sample can never grant) |
| **R3** I2 under a **free clock** | **DISPROVED** | PROVED, k=1 | **PROVED, k=1** |

### 7.2 D2 — the RESTRICTED tier was decorative *(v1 → v2)*

Proved, not conjectured: two states differing only in `mode ∈ {NORMAL,
RESTRICTED}` decided identically for all inputs. **R4: FIXED.**

### 7.3 D3 — the watermark was one-sided and poisonable *(v2 → v3)*

Raised in §8.4 of the v2 edition of this report, **not** by BMC — the v2 encoding
did not model it because the property had not been written down. *A solver only
refutes the theorems you give it.* A single sample dated far in the future set
`last_seen_ms` to that value and every honest sample afterwards was vetoed as
backwards.

**R5**, replaying the concrete case symbolically — honest 1 ms samples at
`t = 1,2,3,4`, one injected at `t = 999999`, honest samples resume:

| | v2 | **v4** |
|---|---|---|
| watermark after injection | 999999 | **4** |
| injected sample classified | accepted | **excursion (`time-jump`)** |
| honest tail | vetoed | **granted** |

R5 asserts the negation of all three and obtains `unsat`, so this holds for every
model. The honest tail is now `DWELL_MS` samples long, because that is what the
shield requires.

### 7.4 D4 — one counter for two unrelated failure modes *(v3 → v4)*

Raised in §8.4 of the v3 edition. `vetoes` was advanced both by a model proposing
unjustified trips and by a clock producing implausible timestamps, under a single
limit. Three consequences, all provable from the table:

* a perfectly-behaved model was disowned by a merging-unit fault it did not control;
* worse, 12 clock glitches reached RESTRICTED, which by I5 and I7f/band
  **withdraws the model's adaptive sensitivity** — a proved degradation for a
  reason having nothing to do with the model;
* **`vetoes` clears only on a grant (I7e), and a calm grid produces no grants**,
  so on a quiet system the count was effectively a **lifetime total**. 24 is not
  many lifetime PTP events. This was the decisive argument: it converts "24
  injected timestamps" from an attack into a reliability question.

**Fixed by S1–S7.** Cost: one field. Proof strength lost: none — I7a, I7b and I7g
restate over two counters unchanged.

A second half of that objection was also accepted: *"requires a human" need not
mean "requires a truck".* `reinstate` travels the same authenticated channel as
`reclose_auth` (A3), is unreachable from `Proposal` (S7, A4), and **permanence is
preserved** — S6b proves nothing the model or the clock does can rearm the shield.
I7a and I7b are now correctly stated as *"absent a reinstate"*, because stating
them without the qualifier would be false.

### 7.5 D5 — only the *remote* addend of the differential was authenticated *(v4 → v5)*

**The defect.** `i_diff = |I_local + I_remote|` is a **sum**, and only the
remote term was authenticated. Authenticating one half of a sum leaves the sum
forgeable: anyone on the local wire chooses one addend and therefore chooses
`i_diff`. They can hold it **steadily just above the sensitivity floor and below
the nominal pickup** — high enough for the shield to grant, low enough to be
invisible to the conventional 87L element beside it. **Measured: 25 of 25 tuned
episodes defeated the shield.**

**Counterexample record.** The counterexample is **DW5**, unchanged from the v4
report and still in the table: a constant `i_diff = 0.1133 pu`, held for
`DWELL_MS + 4` consecutive samples on a perfectly honest clock, obtains a grant.
DW5 was written to show that *no dwell length closes this* — and it is the
counterexample for D5 for the same reason it was the limit of dwell: the two are
the same fact seen from either end. Dwell removes the noise-crossing case;
authentication removes the unprivileged forger; **neither removes a forger
holding the key.**

**The fix.** A new veto reason `R_LOCAL`, a six-element decision input tuple, and
a `local_ok` guard placed **immediately after** the remote guard so the two ends
stay distinguishable in the veto spectrum — which is exactly the information an
engineer needs first when a trip is refused.

**R6, the regression, reports both adversaries separately**, because the point of
the fix is that they now diverge:

| the measured FDI shape, replayed against v5 | outcome |
|---|---|
| **vs. Linux-plane adversary** (no merging-unit key) | **no grant possible** |
| **vs. MU-key adversary** (holds the local key) | **GRANTED** |

R6 is marked FIXED **iff exactly one of the two closes** — a fix that closed
both would mean the encoding was wrong, and a fix that closed neither would mean
the change did nothing. The asymmetry is the result.

**What this cost, and what it did not.** Nothing regressed: every theorem proved
in v1–v4 is still proved, and I2 order-agnostic under a free clock still closes
at k = 1. The new invariants **I1-local** and **I1-both** are deliberately kept
as *separate lines* from I1 rather than folded into it, so the proof obligation
that v5 introduced stays visible on its own instead of silently widening an
existing theorem.

### 7.6 D6 — the compatibility paths failed open *(v5 → v6)*

**Origin.** Like D3, this was raised by *this report against a previous version
of itself* — it appeared in the v5 edition as observation **A8C**, not as a
solver counterexample. Worth recording for the same reason D3 was: the v5
encoding could not have refuted it, because the property had not been written
down. **A solver only refutes the theorems you give it.**

**The defect.** v5 authenticated both addends of the differential and discharged
A8-LINUX — but both backward-compatibility paths substituted a *permissive*
default:

```python
# v5, decide():
if len(mode_ok_inputs) == 5:
    ...
    local_ok = True                                    # <-- fail-open

# v5, Shield.step():
local_ok = (getattr(sample, "local_authentic", True)   # <-- fail-open
            and getattr(sample, "local_fresh", True))
```

So an un-updated caller kept running, kept granting, and got **no indication
that A8-LINUX was no longer discharged for it**. The theorems in §5 were all
still true; they simply stopped applying to that caller. A deployment that
missed a single call site silently got **D5** back — with a proof suite
reporting `PROVED` throughout, which is the worst property a proof suite can
have.

**Counterexample record.** The counterexample is D5's, replayed against a caller
on either compatibility path: the steady forged differential of **DW5** at
0.1133 pu, which under a permissive default is admitted from an adversary with
no merging-unit key at all — i.e. **A8L's `unsat` silently becomes `sat`** for
that caller. The measurement is D5's: **25 of 25 tuned episodes**.

**The fix.** One module constant, `REQUIRE_LOCAL_PROVENANCE = True`, governing
**both** paths — `decide`'s legacy form sets `local_ok = not
REQUIRE_LOCAL_PROVENANCE`, and `Shield.step` reads
`getattr(sample, "local_authentic", _absent)` with `_absent = not
REQUIRE_LOCAL_PROVENANCE`. **That there is exactly one rule matters as much as
its polarity**: leaving the second path permissive is precisely how the hazard
arose. *A default is not an authentication.*

**A sweep for siblings.** Having fixed one stale line I checked the rest of the
suite's own output for the same failure mode, on the principle that a single
instance is rarely alone. Five more were found and fixed, all by the same
method — derive, do not assert:

| stale output | now |
|---|---|
| `Artifact under verification: gs/shield.py [v5, repaired]` | `[frozen; sha256:…]` plus the characterising constants, read from the module |
| `REGRESSION — … replayed against v5` | `… replayed against the CURRENT artifact` |
| `R1 … replayed against v4` | `R1 D1 rate-limit counterexample, replayed` |
| `R3 … (v1: DISPROVED; v2, v3: ?)` | `R3 … (v1: DISPROVED — and now?)`, with the verdict printed beneath |
| result keys `v4_max_grants_obtainable`, `v2_distinguishable` | `max_grants_obtainable_now`, `distinguishable_now` |

Version tags that record *history* — `I8 … (v2)`, `DWELL … (v4)`, the
`v1_result` / `v2_result` / `v4_result` keys — are left alone. Those are facts
about the past and do not go stale; the ones fixed above were claims about the
present.

**Regression.** The A8C row of the proof table is now a **live behavioural
gate**, described in full in §5.3: it calls the shield rather than grepping it,
derives its name and verdict from what it observes, and carries a negative
control so it cannot pass vacuously. Verified by simulation — forcing
`REQUIRE_LOCAL_PROVENANCE = False` flips the row to `HAZARD OPEN` **and turns
`prove_shield_invariants()['proved']` to `False`**, so the whole layer goes red.

Three tests in `tests/test_properties.py` cover the same ground from the
outside, and all three pass:

| test | covers |
|---|---|
| `test_a_sample_without_local_provenance_is_refused` | the `Shield.step` path; also asserts the *same* differential IS granted once provenance is supplied, so the refusal is about provenance and not the measurement |
| `test_a_forged_or_stale_local_channel_is_refused` | all three failure combinations of `(local_authentic, local_fresh)` |
| `test_the_legacy_five_element_decide_form_also_fails_closed` | the `decide` five-element path — the one my detector watches |

**The last one is the important one**, and I would keep it even though the
detector covers the same path: the detector lives in the proof suite and could
itself be deleted or made inert, whereas a test failing is a louder and more
ordinary signal. Two independent watchers on the path that produced the hazard
is proportionate.

**A note on scope, so this fix is not over-read.** D6 restores A8-LINUX for
callers that were not updated. It does nothing whatever for **A8-MU** — an
adversary holding the local merging unit's key still supplies `local_authentic`
and `local_fresh` that verify, and **DW5 is unchanged**. §8.7.

### 7.7 Carried forward

* **`grant_times` and `diff_run` are unbounded in Python, saturating in the
  SPARK.** Refinements, not divergences — `decide` only ever compares against a
  bound — but the artifacts are not structurally identical. `gs/verify.py` models
  the unbounded Python form, which is the stronger of the two.
* **`Shield.step` discards the shield's reason on a baseline trip.**
  Safety-neutral; the SPARK body keeps it.
* ~~The v5 compatibility defaults fail open (A8C).~~ **CLOSED in v6** — promoted
  out of this list and into the defect history as **D6**, §7.6.

---

## 8. What is **NOT** proved

### 8.1 The neural network
Nothing. The proofs assume it is maximally hostile and show the shield holds
anyway — which leaves them silent on whether the AI is *useful*. A shield that
vetoes everything satisfies every invariant here. DW4 is the only counterweight.

### 8.2 Floating point is only partly closed
FPM is assumed. Layers 1–2 reason over ℝ with finiteness as a *predicate*. The
SPARK mirror adds saturations the Python has no need of — all conservative with
respect to granting, all unverified.

### 8.3 The plant model
A1 and A2 are assumed, not derived. Whether a real 345 kV line under CT
saturation, DC offset, inrush and subharmonics stays inside `A1·ir + A2` is a
power-systems question no solver here touches.

### 8.4 Permanent disownment — an accepted trade, now a *better* one
`EXCURSION_LIMIT` excursions still force `BASELINE_ONLY` with no trip ever
requested (P7, unavoidable), and one **repeated** implausible timestamp still
suffices, because the watermark is frozen on excursion — the D3 fix made the
disownment surface cheaper, and that is still true. What changed is that it lands
in its own counter (S1–S4b), so the model is no longer accused and RESTRICTED is
never reached this way; and recovery is now possible (S6) without ceasing to be
permanent against the attacker (S6b). **I agreed with the permanence and still
do**: it is what makes the I7 family close at k = 1, and an auto-rearming shield
is one an attacker can groom into rearming just before a fault.

**Clamp-and-continue remains rejected**, for a machine-checkable reason: per P6
the rate limiter measures elapsed time in raw sample timestamps, so clamping a
forward jump to `ls + 100` and accepting it would advance the effective clock
100 ms per 1 ms sample — a 100× speed-up of the rate window, i.e. D1 in a new
costume. (That comparison is an argument about a design not taken; not
machine-checked.)

### 8.5 Everything outside the state machine
Side channels and fault injection; the isolation boundary (A4, assumed outright);
the remote and operator channels (A3, no protocol/replay/key-management
analysis — and `reinstate` now rides that channel, so A3 carries more weight in
v4 than in v3); the baseline relay's own correctness; compilation, object code
and WCET; general liveness; the unbounded form of P5 (a two-lemma hand argument
from P2a + TRANSPARENCY_SUSTAINED, not a machine-checked composition);
`MAX_CLOCK_STEP_MS = 100` validated against a real merging unit.

### 8.6 The SPARK artifact has still not been proved
Hand-written to be well-formed and faithful, contracts encoding the invariants at
type level, but **gnatprove is not installed here and has never been run on
them**. §9 is an expectation. If the two artifacts drift, only the Python has
evidence behind it — and the one that would ship is the one without it.

### 8.7 **False data injection — what v5 closed, and what it did not**

Stated once more, plainly, because it remains the most important limitation in
this document and the split makes it *easier*, not harder, to overstate.

`i_diff = |I_local + I_remote|`. **v5 authenticates both addends.** That is a
real fix and it closes the attack that was actually being run: the Linux-plane
adversary, who owns the inference plane and can propose anything but cannot sign
as a merging unit, now obtains **zero grants over any trace** (A8L, `unsat`),
however they choose `i_diff`, `i_restraint` or the requested settings. Twenty-five
of twenty-five tuned episodes become zero. **A8-LINUX has moved out of the
assumptions table and into the theorems.**

**It does not close the MU-key adversary, and no amount of authentication can.**
An adversary holding the local merging unit's own signing key produces samples
that *verify*. `local_ok` is true for them by construction — that is what holding
the key means. For them the shield is in exactly the position it was in before
v5: it correctly evaluates an inequality about a number the attacker picked.
**DW5 is unchanged and still `sat`.**

Dwell does not help either, and never could: raising `DWELL_MS` only costs
latency and reach — the value was swept, and `DWELL ≥ 3` destroys the benefit
entirely (0/8 high-impedance reach) while still not closing this.

**What actually bounds the residual is key custody, and none of it is in this
report.** Non-exportable keys in an HSM or a TPM-backed secure element; device
attestation; key rotation and revocation; physical security of the merging unit
cabinet; detection of a key used from two places at once. **None of these is
modelled, tested, or proved anywhere in `gs/verify.py` or `spark/`.** They are
the entire remaining defence and they are outside the verification boundary.

A reviewer's summary of this document should therefore be: *the shield's logic is
verified; its inputs are now authenticated; and its trust in the instruments
holding those keys is unexamined.* That last clause is where the next defect will
be found.

---

## 9. The SPARK mirror — what gnatprove would be expected to discharge

| Aspect | Obligation |
|---|---|
| `SPARK_Mode => On` | no allocation, recursion, exceptions, tasking or secondary stack; the only loops have static bounds |
| AoRTE | no overflow in timestamp differences (`Ms` is 64-bit); indices guarded by `N_Grants`; `Veto_Count`, `Excursion_Count`, `Dwell_Count`, `Grant_Count` all saturate; **no `Constraint_Error` from a NaN or infinite sample**, because `Differential_Ok` takes `Raw_Pu` and rejects before converting |
| `Is_Finite` | the only bridge `Raw_Pu → Pu`; deliberately redundant (`'Valid` plus two range tests) so it is correct whatever a runtime makes of `'Valid` on a float |
| `Differential_Ok'Contract_Cases` | **N1**, as a *case*, not an emergent IEEE-754 property |
| `Differential_Ok'Post` | **T2**, **I5**, **I8**. One `pragma Assert`, `K * Ir >= K_Min * Ir`, **is FPM** — in SPARK a proof obligation rather than an assumption, one way the Ada artifact is stronger than the Z3 one |
| `Clock_Plausible'Post` | **P4**, as a contract on the definition |
| `Dwell_Met` | **DWELL**, as a function `Decide` reads and `Commit` maintains |
| `Decide'Contract_Cases` | **I1, I1-local, I3, I4, I4b, P1, DWELL** and **TRANSPARENCY**; thirteen cases, pairwise disjoint and complete — itself a checked VC. `R_Time_Jump`, `R_Dwell` and **`R_Local`** are cases, not fall-throughs |
| `Inputs_T.Local_Ok`, `Sample_T.Local_Authentic/Local_Fresh` | **A8-LINUX by typing.** Python reaches provenance through `getattr` and a five-element fallback, which had to be made fail-closed by hand and is now watched by a live gate (D6, §7.6); Ada has record fields, so a stream that does not carry local provenance **does not compile**. The Python needed a constant and a regression detector to reach where the Ada type system starts |
| `Step'Post` | also **I1-both**: `Trip ∧ ¬Baseline_Trip ⟹` both `Remote_*` **and** `Local_*` were authentic and fresh |
| `Commit'Pre` | `Granted ⟹ ¬Clock_Excursion ∧ ¬Rate_Blocked ∧ Dwell_Met` |
| `Commit'Post` | **P2a** (one line, the D3 fix), **P2b/P2c**, **S1, S2, S3, S5, S6**, **I7** *absent a reinstate*, **I7g** into the excursion counter, `Window_Ascending`, and the dwell-run coherence |
| `Step'Post` | **I6** unconditionally, **I5** against the pre-state mode, **DWELL** against the pre-state run; and `Reinstate => False` at the only call site the model can reach (**S7**) |
| `Global => null`, `Depends` | the shield reads nothing but its formals and touches no package or heap state |
| **Not needed any more** | v1 listed I2 as "holds only under A5". **I2 is now a property of the code.** |

Much of Z3's `W` disappears in SPARK because `Mode_T`, `Grant_Count`,
`Veto_Count`, `Excursion_Count`, `Dwell_Count` and `Grant_Window` are *types*.
That is the argument for the SPARK artifact being the one that ships — undercut
entirely by §8.6 until gnatprove is run.

---

## 10. Summary

* **Layer 0: 3/4 proved outright, N3 modulo FPM.** **Layer 1: 6/6 proved**,
  margin **0.02 pu exactly** at `i_restraint = 0.5 pu`.
* **Layer 2: everything proved at k = 1** with fully unconstrained hostile
  inputs including a free clock. **I2 order-agnostic under a FREE CLOCK still
  holds, k = 1 — the centrepiece survived the v5 change.** I2's bare form is
  still `BOUNDED-ONLY` to depth 12 and reported as such.
* **New in v5 and proved: I1-local and I1-both** — a grant implies *both*
  addends of the differential were authenticated and fresh. Kept as separate
  lines from I1 so the new obligation is visible rather than folded into an
  existing theorem. **A8L** turns the Linux-plane half of A8 into a theorem:
  zero grants over any trace, with every measurement and setting free.
* **A8 restated, not quietly resolved.** It is now two assumptions with two
  different fates: **A8-LINUX is DISCHARGED** and has moved into the proved
  column; **A8-MU remains an ASSUMPTION** with the same prominence it had —
  the opening banner, the assumptions table, §5.3, §7.5, §7.6, §8.7, and a block the
  tool prints after every run. **DW5 is unchanged**, still `sat`, still the
  most important line in the document; it now carries a precisely stated scope
  (`local_ok` asserted true — the defining capability of an adversary holding
  the key).
* **All six historic defects fixed and regression-tested.** R1 yields **1**
  grant where v1 yielded 3; R2 yields **0**; R5 proved for all models; **R6
  reports the two adversaries separately and is marked FIXED only because
  exactly one of them closes.**
* **Nothing regressed.** Every theorem proved in v1–v5 is still proved, and
  all 84 tests pass. One
  invariant *clause* was dropped back in v4 (`ls ≥ g1`, §5.5) because
  `reinstate` legitimately resyncs the clock; it was never needed by I2.
* **A8C is CLOSED (D6), and the row that reports it is now a live gate.** Both
  compatibility paths — `decide`'s five-element form and `Shield.step`'s
  absent-attribute read — now fail **closed** under one rule,
  `REQUIRE_LOCAL_PROVENANCE`. The proof table's A8C row derives its name and
  verdict from a **behavioural probe** rather than a static string or a source
  grep, and carries a negative control so it cannot pass vacuously: force the
  constant `False` and the row flips to `HAZARD OPEN` while
  `prove_shield_invariants()['proved']` goes `False`. It stays a regression
  detector instead of decaying into a comment.
* **Two of the six defects (D3, D6) were raised by this report against a
  previous version of itself**, not by the solver. Both times the encoding
  *could not* have refuted them, because the property had not been written
  down. That is the honest limit of the method and it is worth stating next to
  the `PROVED` column: a solver only refutes the theorems you give it.
* **The residual, and it is not small:** an adversary holding the local merging
  unit's signing key defeats the shield exactly as before. What bounds that is
  non-exportable key custody, attestation, rotation and revocation — **none of
  which is modelled, tested or proved anywhere here.** §8.7.
* The shipping SPARK artifact remains unproved (§8.6), and nothing here says
  anything about the neural network, the plant model, or the physical isolation
  the whole argument rests on (§8).
