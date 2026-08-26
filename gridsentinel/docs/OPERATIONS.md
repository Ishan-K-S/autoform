# GridSentinel — operations manual

**Audience:** the protection engineer commissioning the appliance, and the
operator or SOC analyst who has to act on what it prints.

**Companion documents.** `docs/PROOF.md` says what has been proved and, more
importantly, what has not. `docs/THREATMODEL.md` says what the design does not
prevent. This document says what to *do*. Where the three disagree, PROOF.md
and THREATMODEL.md win; this file is derived from them.

---

## 0. Status, before anything else

Read this section before quoting anything from the rest of the document.

* **This is a study, not a qualified product.** Nothing here has been through
  a type test, a protection-scheme design review, or IEC 61508 / 61511 / 62443
  assessment. Do not put it on a live bay.
* **The headline safety claim was falsified.** Not by a hostile model — the
  three adversarial policies are contained with zero grants — but by
  false-data injection. `i_diff = |I_local + I_remote|`; whoever controls one
  addend controls the sum. The shield now requires **both** addends to be
  authenticated and fresh, which closes the adversary who sits on the Linux
  plane. It does **not** close an adversary holding the *local merging unit's
  own signing key*: that residual is bounded only by non-exportable key
  custody in an HSM plus attestation, neither of which this repository
  implements or tests. `run.py --seed 0` still grants on
  `attack/fdi_tuned` episodes and prints the falsification. Z3 theorem DW5
  shows no value of `DWELL_MS` closes it.
* **The SPARK mirror has no machine evidence.** `spark/shield.ads` /
  `spark/shield.adb` have never been compiled or run through `gnatprove` —
  the tool was not available. Treat the Ada as a design document.
* **The Z3 proofs are over the reals**, except a small layer-0 fragment that
  uses the IEEE-754 binary64 theory for NaN/±inf handling. A proof over the
  reals is not a proof about the arithmetic the appliance will execute.
* **The proofs are about the *logic*, not about whether the measurements are
  true.** That gap is authentication, and it is larger than every defect the
  verification has found put together.

---

## 1. What an operator actually sees

The appliance emits three things, continuously:

1. **A trip decision and its source.** `Shield.step` returns
   `(trip, source, reason)`; `source` is either the conventional relay
   (baseline) or the shield's grant. A trip that reads `baseline` was taken by
   conventional protection and would have happened with the appliance switched
   off.
2. **A mode.** `NORMAL` → `RESTRICTED` → `BASELINE_ONLY`, monotone downwards
   and never upwards except by an authenticated operator action (§4).
3. **A veto stream.** Every refused request is logged with a distinct named
   reason.

### 1.1 The veto spectrum is the detection signal

Every veto reason is a separate named constant on purpose. Collapsing two
causes into one reason destroys the signal. **A single veto tells you very
little; the *distribution* over reasons is diagnostic**, because different
attacks produce characteristically different distributions. Alarm on the shape
of the histogram, not on individual lines.

Two properties of the stream matter operationally:

* **A veto is a record; a grant is not.** Only refusals are logged today. An
  attack that *succeeds* leaves no entry. This is a real gap (see
  `docs/THREATMODEL.md` §6.2) and the first thing an integrator should fix.
* **Silence is not safety.** The most dangerous observed state is *no vetoes*,
  all-benign traffic, and a rising process residual — commands consistent with
  the reports while the physics disagrees with both. Trend the residual
  separately from the veto count.

---

## 2. Veto reasons: what each means, and what to do

The vocabulary below is taken from the code, not invented: `gs/shield.py`
(v1, one line, differential protection) and `gs/monitor.py` (v2, the
generalised reference monitor over a fleet of actuators). The v2 names carry
the invariant that produced them.

### 2.1 `gs/shield.py` — the line-protection shield

| Reason | Meaning | Operator action |
|---|---|---|
| `grant` | Accelerated trip authorised. | None. Expect a latch; reclose needs authorisation (§4.1). |
| `no-request` | The model asked for nothing. The overwhelmingly common case. | None. |
| `veto:mode-disowned-model` | The model is in `BASELINE_ONLY`. Every request is refused. | The plant is running on conventional protection. Decide whether to investigate or reinstate (§4). |
| `veto:latched-awaiting-reclose-auth` | A grant already fired; no further grant until reclose is authorised. | Normal after a trip. **Repeated** occurrences mean either open/close cycling or a reclose authorisation that is not arriving. Ambiguous — needs a human. |
| `veto:rate-limit` | More than `MAX_GRANTS` accelerated trips inside `WINDOW_MS`. | Containment working. Bursts of this are a probe of the budget. Investigate. |
| `veto:time-went-backwards` | The sample clock stepped backwards. | **Security event, not a glitch.** This is the precondition of the historic rate-limiter defeat (defect D1). Check PTP/GPS. Repeated occurrences: treat as deliberate clock manipulation. |
| `veto:time-jumped-forward` | A forward step larger than `MAX_CLOCK_STEP_MS` (100 ms). | Same as above. The plausibility window exists so one future-dated sample cannot poison the watermark and deny service forever (defect D3). |
| `veto:time-source-integrity` | The sample's own time-quality flag is bad. | Instrument/PTP fault. Counted as an *excursion*, not against the model. |
| `veto:remote-channel-unauthenticated` | The remote merging unit is unauthenticated or stale. | Comms or key problem — or a forgery attempt. Check the remote MU link. |
| `veto:local-channel-unauthenticated` | The local merging unit is unauthenticated or stale — **or the sample stream carries no local provenance at all**, which fails closed. | If seen at commissioning, the sample source has not been upgraded to carry local provenance; fix the source, do **not** set `REQUIRE_LOCAL_PROVENANCE = False` (§6.2). If seen in service, this is the false-data-injection path being exercised. |
| `veto:directional-reverse` | The directional element says the disturbance is behind the relay. | External fault. Correct refusal; an attacker using a real through-fault as cover looks exactly like this. |
| `veto:no-physics-corroboration` | The differential does not clear the clamped threshold. | The model wanted a trip the physics does not support. Sustained: see disownment. |
| `veto:physics-not-sustained` | Corroboration did not hold for `DWELL_MS` consecutive samples. | A single-sample noise excursion. Common and benign in isolation; a rising rate means a noisy CT or a forger probing the floor. |

### 2.2 `gs/monitor.py` — the generalised reference monitor

| Reason | Meaning | Operator action |
|---|---|---|
| `veto:E7-unrecognised-or-unauthenticated-source` | Command from a source the monitor does not recognise or cannot authenticate. | Usually a misconfigured device. Under this threat model, the *least* interesting alarm: an adversary with stolen credentials does not trip it. |
| `veto:E7-baseline-must-not-be-mediated` | Something tried to route conventional protection through the monitor. | Configuration defect. Conventional protection is OR-ed at the output and must never be mediated (I6). Fix immediately. |
| `veto:E6-clock-stepped-backwards` | Monotone-time violation. **Three of these force `BASELINE_ONLY`.** | Security event. Check time distribution before reinstating anything. |
| `veto:I4-time-source-integrity` | Time quality flag bad. | Instrument fault. |
| `veto:E5-stale-sequence-counter`, `veto:E5-nonce-reuse`, `veto:E5-replayed-process-report` | A correctly *signed* frame carrying stale or replayed data. | **Replay in progress.** A valid signature over stale data is not a sender bug. This is the Stuxnet 21-second process-value replay, precisely. Escalate. |
| `veto:I7-mode-disowned-source` | The source has been disowned. | See §4. |
| `veto:I3-latched-awaiting-reclose-auth` | Per-target latch after a protective trip. | As §2.1. |
| `veto:I2-E2-cross-source-rate-limit` | The global budget — across every source *and* every target — is spent. | **This is the primary control on the Industroyer path.** Bursts across several different sources in one window mean a mass-open sweep or source hopping. Escalate. |
| `veto:I1-remote-channel-unauthenticated`, `veto:I1-local-channel-unauthenticated` | As §2.1, per addend. | As §2.1. |
| `veto:I1-directional-reverse` | Disturbance behind the element. | Correct refusal. |
| `veto:I1-no-physics-corroboration` | An authenticated TRIP with no fault behind it. | **Industroyer-shaped**, especially sustained, from SCADA/HMI, with valid signatures and no baseline activity. Escalate. |
| `veto:E1-setpoint-outside-absolute-band` | Setpoint outside the machine's qualified band. | **Stuxnet-shaped.** The 1410 Hz / 2 Hz payload lands here. |
| `veto:E1-setpoint-rate-of-change` | Ramp faster than the torque-limited slew. | As above; the ramp *between* the payload values. |
| `veto:E1-setpoint-in-or-through-critical-band` | The setpoint sits in, or sweeps through, a rotor-critical band. | As above — caught even at legal absolute values. Long gaps between occurrences are the tell, not a mitigation. |
| `veto:I1p-observation-channel-unauthenticated` | The independent observation channel (motor current, casing vibration) is unauthenticated or stale. | The residual is the only thing that contradicts a replay. Without it the monitor is blind in the process domain. Treat as loss of a safety function. |
| `veto:I1p-no-process-corroboration-residual` | The independent residual contradicts the reported process value by more than `RESIDUAL_MAX_SIGMA` (6σ). | **The attacker owns the reporting channel and is being caught by physics.** Highest-value alarm in the drive domain. |
| `veto:E3-remaining-system-not-survivable` | The post-open island is short of generation, violates reclose dead time, or erodes N-1. | Refused regardless of who asked. If an operator legitimately needs this, the answer is a system study, not a bypass. |
| `veto:E4-privileged-op-in-restricted-mode` | Privileged operation attempted while the source is distrusted. | Investigate the vetoes that caused `RESTRICTED` first. |
| `veto:E4-dual-signature-absent`, `veto:E4-attestation-invalid` | Logic download / settings change without both signatures or with failed attestation. | Escalate. |
| `veto:E4-physical-keyswitch-not-engaged`, `veto:E4-outside-maintenance-window` | The credentials were all present; the *physical* factor or the time window was not. | **The most alarming single line the log can produce.** With valid dual signatures and valid attestation, this means the adversary has the credentials and the certificates and is missing only the key switch. Treat as confirmed compromise of the engineering plane. |
| `veto:E4-operational-switching-custody` | Dual custody required for an operational switch and not supplied. | Off by default; see `require_switch_custody`. |
| `veto:unrecognised-command-kind` | Malformed or unknown command kind. | Configuration or protocol defect. |

### 2.3 Reading the histogram

| Shape | Most likely cause |
|---|---|
| Sustained `I1-no-physics-corroboration` on TRIPs from SCADA/HMI, valid signatures, no baseline activity | Industroyer-shaped: authenticated commands with no fault behind them |
| `I2-E2-cross-source-rate-limit` bursts across several sources in one window | Mass-open sweep or source hopping |
| `E1-*` on SETPOINTs from engineering, weeks apart | Stuxnet-shaped |
| `E5-*` with valid signatures | Replay in progress |
| `E6-clock-stepped-backwards`, more than once | Deliberate clock manipulation |
| `E4-physical-keyswitch-not-engaged` with valid dual signature and attestation | Engineering plane compromised |
| Rising `physics-not-sustained` with no other change | Noisy CT — or a forger probing the sensitivity floor |
| **No vetoes at all, rising process residual** | The worst case that is still visible |

---

## 3. What happens when the appliance fails

**Fail-operational for the grid; fail-safe for the appliance.**

The conventional relay (`gs/relay.py` — memory-polarised mho distance zones
1/2/3, 87L at nominal settings, directional supervision, power-swing blocking)
runs **unconditionally**. `baseline_trip` is OR-ed at the output and is never
routed through `decide`. This is invariant **I6**, and it is structural rather
than configured: there is no shield state, no mode, and no proposal that can
inhibit conventional protection.

Consequences:

| Failure | Effect on the grid |
|---|---|
| ML plane crashes, hangs, or is compromised | Conventional protection unaffected. Lose the accelerated trip and the high-impedance reach; lose nothing you had before the appliance was fitted. |
| Safety island crashes or is powered down | Same. The appliance's *only* output is a permissive; losing it removes a capability, not a protection. |
| Merging-unit authentication fails | Every grant is vetoed (`*-channel-unauthenticated`). Degrades to conventional protection. |
| Model disowned (`BASELINE_ONLY`) | Degrades to conventional protection, and stays there until a human acts. |

So the honest framing of an appliance outage is: **you are back to the
protection you had before, which is safe and less capable**. Somebody still
has to decide how long that is acceptable — that decision cannot be
automated.

---

## 4. Disownment and reinstatement

### 4.1 How disownment happens

Two counters, deliberately kept apart, because conflating them let a
merging-unit or PTP fault disown a blameless model:

* `State.vetoes` — sustained *unjustified requests*. At `VETO_LIMIT` (24) the
  mode becomes `BASELINE_ONLY`. At `VETO_LIMIT // 2` (12) it becomes
  `RESTRICTED`, in which the model can no longer buy adaptive sensitivity.
  Cleared by a grant.
* `State.excursions` — *clock and instrument* faults. At `EXCURSION_LIMIT`
  (24), also `BASELINE_ONLY`. Blameless model, blamed plant.

In `gs/monitor.py` there is additionally a hard rule: **three** backwards
clock steps (`clock_faults >= 3`) force `BASELINE_ONLY` outright.

### 4.2 `BASELINE_ONLY` is absorbing

The mode transition is monotone and one-way. Nothing in the model's influence
— no proposal, no confidence, no quiet period, no timeout — returns it to
`NORMAL`. **A model can never rearm itself.** That is deliberate: an
automatic recovery is exactly the thing an attacker waits out.

### 4.3 Reinstatement

`shield.commit(..., reinstate=True)` is the **only** path back, and it is an
**authenticated operator action on the same channel as `reclose_auth`** — the
same out-of-band path, structurally unreachable from a `Proposal` (`Proposal`
has no `reinstate` field; Z3 checks this).

Reinstatement performs three things atomically:

1. `mode → NORMAL`
2. `vetoes → 0`, `excursions → 0`
3. **`last_seen_ms → None`** — the clock watermark is resynchronised.
   Without this, a stale frozen watermark makes the very next honest sample
   read as an excursion and the operator's action achieves nothing.

**Procedure.**

1. **Do not reinstate first.** Pull the veto log and read the *distribution*
   (§2.3). Reinstating clears the counters and destroys the evidence of rate.
2. Classify: model misbehaviour (`vetoes` drove it) or plant fault
   (`excursions` drove it)? The two counters are separate precisely so this
   question has an answer.
3. If plant fault: fix the clock or the instrument, confirm the fix on live
   telemetry with the appliance still disowned, then reinstate.
4. If model misbehaviour: **do not reinstate the same model.** Go to §5.
5. If neither is clear, keep it disowned. Running on conventional protection
   is the safe state, and §3 says what it costs.
6. Record the reinstatement: who, when, why, and what changed. This is the
   one action that undoes an automatic safety response.

> **Open item for the owners of `gs/monitor.py`:** the v2 monitor has no
> `reinstate` path at all — `commit()` sets `BASELINE_ONLY` and there is no
> way out short of restarting the process, which also discards the replay
> memory and the latch table. v1 has the authenticated path; v2 does not.
> This is a reliability trap and needs closing before any deployment.

---

## 5. Model updates and re-proof: two lanes

The model and the shield are updated on **different lanes at different
speeds**, and this is the central operational discipline of the design.

| | Fast lane — the model | Slow lane — the shield |
|---|---|---|
| Artifact | `gs/ai.py`, `models/*.joblib` | `gs/shield.py`, `gs/monitor.py` |
| Plane | Untrusted (Linux, Python, sklearn) | Trusted (safety island) |
| Change cadence | As often as retraining is useful | Rarely, and never casually |
| Evidence required | The experiment harness: benefit did not regress | Z3 re-proof, plus review of the SPARK mirror |
| Blast radius of a bad change | **Bounded by the shield**: a hostile model gets zero grants | **Unbounded**: the shield is the thing that bounds everything else |

**Why the asymmetry is the point.** The shield's entire value is that you do
not have to trust the model. A model update therefore does not need a safety
argument — it needs an *efficacy* argument, because the safety argument is
carried by an artifact that did not change. The moment you change the shield,
that inheritance stops and every claim must be re-established.

### 5.1 Fast lane — updating the model

1. Retrain: `make experiment SEED=<n>` with `--retrain`, or refit offline and
   drop the joblib into `models/`.
2. Run the experiment across seeds. Compare arm C against arm A: latency,
   high-impedance reach, false trips.
3. **Check the veto spectrum, not just the score.** A model whose benefit is
   unchanged but whose veto rate has doubled is heading for disownment in
   service.
4. No re-proof is required. The shield did not change.

### 5.2 Slow lane — changing the shield or the monitor

**Rule: any change to `gs/shield.py` or `gs/monitor.py` requires
`make verify` to pass, on the same commit, before merge.** Not afterwards.

1. Change the artifact.
2. `make verify` — the Z3 suite. Layers 0/1/2 and every historic-defect
   regression must pass; `gridsentinel-verify` exits non-zero if any layer
   regresses.
3. If a constant that appears in a theorem changed, the theorem must be
   *re-derived*, not merely re-run: a theorem that still passes because it was
   restated around the new value proves nothing.
4. `make test` — the property tests.
5. Update `docs/PROOF.md`, including the "what is NOT proved" section.
6. Update the SPARK mirror in `spark/` so the two artifacts do not diverge,
   and record honestly that it still carries no `gnatprove` evidence.
7. Re-run both harnesses and diff the results.

---

## 6. Constants: what an integrator may retune, and what is frozen

### 6.1 Retunable, with judgement

| Constant | Where | Notes |
|---|---|---|
| `P0_NOM`, `K_NOM` | `shield.py` | Nominal 87L settings, applied when no certificate is asserted. Site settings; retune with the rest of the protection scheme. They must remain **above** the floor. |
| `MAX_GRANTS`, `WINDOW_MS` | both | The rate budget. Lowering is always safe; raising weakens the primary control on the Industroyer path. Any change must be re-proved (I2). |
| `VETO_LIMIT`, `EXCURSION_LIMIT` | `shield.py` | Disownment sensitivity. Tuning these trades nuisance disownment against how long a misbehaving model runs. Keep them **separate** — merging them was defect D4. |
| `MAX_CLOCK_STEP_MS` | `shield.py` | Clock plausibility window. Set from the real time distribution: grandmaster failover, BMCA re-election and a smeared leap second all produce steps. |
| `RESIDUAL_MAX_SIGMA` | `monitor.py` | Process-corroboration threshold. Measured separation is ~8× on medians; 6σ sits inside that gap. Raising it blinds I1′. |
| `ISLAND_MARGIN`, the `feasibility` oracle | `monitor.py` | Site-specific and expected to be replaced by a certified oracle. The default is deliberately conservative. |
| `maint_window`, `require_switch_custody` | `monitor.py` | Site policy. |

### 6.2 Frozen — changing these invalidates the proof

| Constant | Why |
|---|---|
| **`P0_MIN` = 0.10, `K_MIN` = 0.20** | **The sensitivity floor is a proven bound, not a setting.** The lemma is `A1·Ir + A2 < max(P0_MIN, K_MIN·Ir)` for all through-currents: the worst-case spurious differential admitted by instrument error is strictly below the most sensitive threshold the shield will ever grant. Lower either value and the lemma is false — instrument error alone can then trip the line. Changing them **invalidates the Z3 lemma and requires re-proof**, including re-derivation of the worst-case margin. There is no "just a bit more sensitive". |
| `A1_CT_ERROR` = 0.12, `A2_CHARGING` = 0.02 | These are not settings either: they are the *premises* the floor is proved under, and `gs/measure.py` hard-clamps the simulator to them. If the real CTs are worse, the lemma does not hold for your site — the answer is different CTs or a different floor with a fresh proof, not a bigger number here. |
| `REQUIRE_LOCAL_PROVENANCE` = `True` | A default is not an authentication. Setting this `False` restores the falsification: absent local provenance is then silently trusted. Permitted only for replaying historical sample streams, never in a deployment. |
| `DWELL_MS` = 2 | Swept empirically: 1 leaves the noise-crossing break open; ≥3 closes it *and* destroys the benefit entirely. 2 is the only value that buys anything. It does **not** close false-data injection and no value of it does (theorem DW5). |
| The E1 envelope (`SP_ABS_MIN/MAX`, `SP_MAX_RATE`, `RESONANCES`) | Imported from `gs/plant_drive.py`, which stands in for the machine's commissioning report. Never re-declare them locally — three files once carried three different answers. They change when the *machine* changes, via commissioning data. |
| I6 baseline pass-through | Structural. Not a constant, and not negotiable: if the monitor can inhibit conventional protection, a compromised monitor becomes the attack. |

---

## 7. Commissioning checks

Run in order. Each one has failed for somebody.

1. **Environment.** `make` prints the interpreter. On macOS it must read
   `arch -arm64 .venv/bin/python`, and nothing may wrap it in `timeout`
   (see CONTRIBUTING.md).
2. **`make verify`.** All four gates PASS. Read the A8 note it prints at the
   end; do not skip it because the gates are green.
3. **`make test`.** 75 tests, ~2.5 minutes, all passing.
4. **`make experiment`** and **`make attacks`** on the site seed. Expect the
   `attack/fdi_tuned` falsification to be printed. **If it is *not* printed,
   something has been weakened** — check `REQUIRE_LOCAL_PROVENANCE` and the
   scenario catalogue before concluding you fixed it.
5. **Power-system model.** `gs.power.self_check()` — every entry True.
6. **Provenance end to end.** Confirm the live sample stream carries
   `local_authentic` / `local_fresh` / `remote_authentic` / `remote_fresh`
   and that they are real signature checks, not defaults. Deliberately drop
   each one and confirm the matching `*-channel-unauthenticated` veto.
7. **Key custody.** The local merging unit's key must be non-exportable and
   attested. This is the residual that the falsification lives in, and it is
   the one control the software cannot check for you.
8. **Time distribution.** Force a grandmaster failover. Confirm you get
   `veto:time-jumped-forward` / excursion counting and **not** disownment of
   a blameless model, and that the watermark recovers.
9. **Baseline independence (I6).** Power down the safety island entirely and
   confirm conventional protection still trips on an internal fault. This is
   the single most important commissioning test in this list.
10. **Latch and reclose.** Confirm a granted trip latches and that only the
    out-of-band `reclose_auth` clears it.
11. **Disownment and reinstatement.** Drive the model to `BASELINE_ONLY`
    deliberately. Confirm it cannot rearm itself, that the authenticated
    `reinstate` works, and that an honest sample immediately after
    reinstatement is **not** judged an excursion (the watermark resync).
12. **Rate limit.** Attempt three accelerated trips inside one second, and a
    source-hopping sweep against the v2 monitor. Confirm the third is
    refused with the rate-limit reason.
13. **Process residual (drive domain).** Confirm the observation channel is
    wired and authenticated, and that a replayed process report with a valid
    signature is refused. `gs/monitor.py` does not wire the residual to a SOC
    by itself — a deployment must.
14. **Logging.** Confirm vetoes reach the historian. Note the known gap:
    grants are not logged, and the log carries no issuing identity or command
    parameters. Close this before service.
