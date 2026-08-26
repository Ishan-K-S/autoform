# GridSentinel — threat model

> ## READ THIS FIRST — the design was falsified, and the fix covers one of two adversaries
>
> An earlier cut of this design authenticated only the **remote** addend of the
> line differential. Since `i_diff = |I_local + I_remote|`, an adversary owning
> the local channel controlled the sum, and could hold a forged differential
> steadily **above the sensitivity floor and below the nominal 87L pickup** —
> corroborated to this monitor, invisible to conventional protection. That
> falsified the project's headline safety claim: **a tuned, paced forger won 25
> of 25 episodes.** Z3 theorem **DW5** proves the general case — *no* dwell
> length rejects a steadily-held forged differential, so "wait longer" is not a
> fix.
>
> Both ends are now authenticated (`R_LOCAL`), and the same reasoning was
> applied to the process domain's observation channel (`R_OBSERVATION`). The
> result splits cleanly in two, and the split is the most important thing in
> this document:
>
> | Adversary | Status | Evidence |
> |---|---|---|
> | **A8-LINUX** — owns the inference plane, the OS, the model and the command path, but holds **no merging-unit signing key** | **DISCHARGED.** Now theorem **A8L**: zero grants over any trace (`unsat`). | 25/25 → **0/25** measured |
> | **A8-MU** — **holds the local merging unit's own signing key** | **STILL AN ASSUMPTION,** at the same prominence it always had. Their forgeries verify, so authentication is blind to them. **DW5 stands exactly as it did.** | 25/25 stays **25/25** |
>
> The catalogue's `unblockable/local_mu_key_holder` is **byte-identical** to the
> positive control `control/local_addend_authentic`. That identity *is* the
> finding: every check in this design asks whether **a** valid key signed, never
> whether the **right party** held it. A8-MU is bounded only by key custody,
> attestation, rotation and revocation — none of which is modelled, exercised or
> verified anywhere in this repository. The verification agent expects the next
> defect to be there, and so do I.

**Scope of this document.** What the GridSentinel actuation reference monitor
(`gs/monitor.py`, with the v1 line-protection shield `gs/shield.py` as its
special case) is being asked to defend against, what it actually stops, and —
at greater length — what it does not. The threat model was widened from "a
wrong or hostile ML model" to include two historical attacks that arrive through
the *legitimate* control path with correct credentials and well-formed protocol:
Stuxnet (2010) and Industroyer / Industroyer2 (2016, 2022) together with the
2015 Ukraine attack.

**The claim this document defends is deliberately weak.** It is
*containment and bounded impact*, not prevention. Section 4 says so without
hedging and Section 5 lists the places the argument is thinnest. Where I am not
sure whether a mechanism blocks a step, it is marked UNCERTAIN and I state what
evidence would settle it.

**Artifacts referenced, as they exist on this machine:**

| Artifact | Role | Verification status |
|---|---|---|
| `gs/shield.py` | v1 line-protection shield; single AI channel | Z3-proved (`docs/PROOF.md`) |
| `gs/monitor.py` | v2 generalised actuation reference monitor: I1, I1p, I2–I7 + E1–E7 | **Partially.** The I1 family — I1-local, I1-both, A8L, DW1–DW5 — is machine-checked. The E1–E7 envelope layer, the provenance prologue, the per-target latch, the per-association replay table and operator reinstatement are **not**. |
| `gs/plant_drive.py` | VFD/rotor plant model (Stuxnet domain) | self-check passes; a model, not a plant |
| `gs/attacks.py` | monitor-aware adversary catalogue, incl. an `unblockable` family and matched positive controls | data, not evidence |
| `spark/shield.ads/.adb` | the artifact that would ship | **never run through gnatprove** |

---

## 1. Assets and consequences

### 1.1 What is being protected

The asset is not data and it is not availability of a control system. It is
**the physical plant's remaining margin to destruction, and the load it serves.**
Everything below is measured in physical consequence, not in alerts.

| Domain | Asset | Actuator under mediation | Sensors the monitor trusts |
|---|---|---|---|
| Line protection | A 345 kV transmission line, the breakers at each end, and the load downstream of the resulting island | breaker TRIP (protective) / SWITCH (operational) / CLOSE | **both** merging units — `i_diff = \|I_local + I_remote\|`, and both addends must now carry provenance |
| VFD / rotor process | A high-speed rotor (1064 Hz nominal, qualified band ~1000–1100 Hz) and its accumulated fatigue life | drive SETPOINT, PLC SETTINGS_CHANGE / LOGIC_DOWNLOAD | the tach / motor-current / casing-vibration observation channel, which must now carry provenance before its residual is consulted |

### 1.2 What harm looks like

**Line protection domain.**

| Failure | Mechanism | Consequence |
|---|---|---|
| Spurious trip | accelerated trip granted with no real fault | one line lost; if the remaining island is short of generation, cascading under-frequency load shedding |
| **Manufactured trip** | **a forged differential held in the band between the sensitivity floor and the nominal pickup** | **the falsification above: a trip that this monitor corroborates and conventional protection never sees. Closed for A8-LINUX, open for A8-MU.** |
| Mass trip | many breakers opened in sequence, each individually plausible | the 2015 Ukraine outcome: ~225 000 customers de-energised, restoration by hand at the substation |
| Repeated re-open | operator restores, attacker re-opens | restoration is denied; the outage duration, not the trip, is the damage |
| Failure to trip | protection desensitised by a settings change, or inhibited | a real fault is not cleared — equipment damage, arc-flash, fire. **This is the worse of the two directions** and is why baseline protection is structurally un-inhibitable (I6). |

**VFD / rotor domain.** Damage here is an *integral*, not an event. From
`gs/plant_drive.py`'s calibration: a single 25 s dwell at 1410 Hz costs ~0.097 of
rotor life — survivable. The full slow-cycle payload accumulates 1.00 (failure)
in ~3.7 bursts. Sustained dwell in a critical-speed band is the more efficient
destroyer than overspeed. So:

* No single command in the Stuxnet payload is individually fatal.
* An alerting system that scores "did we raise a flag" scores the wrong thing.
* The consequence of interest is **time-to-destruction**, and the monitor's job
  is to make that time infinite, not to make it longer.

### 1.3 Consequence of the monitor failing the other way

A monitor that vetoes everything satisfies every invariant in this document.
Denial of service by veto is a real failure mode with real physical
consequence (a fault that should have been cleared, was not). Its counterweights
are weak: v1's TRANSPARENCY is a **one-step** property, and DW4 (`DWELL_MS` good
samples do produce a grant) is the only multi-step counterweight. Neither is a
liveness guarantee.

---

## 2. Adversary model

### 2.1 Granted to the adversary

These are assumed true, not argued against. An objection of the form "but the
attacker would need X" is not available for any X below.

| # | Granted capability | Grounding |
|---|---|---|
| **G1** | **Full compromise of the Linux/inference plane.** Root, arbitrary code, the model weights, the feature pipeline, and unlimited proposals at line rate with arbitrary parameters. | v1's original assumption; `docs/PROOF.md` proves the invariants against a maximally hostile proposer. |
| **G2** | **Valid credentials on SCADA / HMI / the engineering workstation.** Sessions indistinguishable from an operator's. | The 2015 Ukraine attack was executed through the operators' own HMI. |
| **G3** | **A validly stolen code-signing certificate.** Signatures produced with it verify. | Stuxnet was signed with genuine Realtek and JMicron keys. Every signature check in `gs/monitor.py` establishes that *a* recognised key signed, never that the *right* party intended it. |
| **G4** | **Ability to author correctly formed, correctly authenticated protocol traffic** — IEC-101/104, IEC 61850 MMS/GOOSE, S7 — at any rate, in any order. | Industroyer's payload modules spoke the protocols correctly by design. Nothing malformed was needed. |
| **G5** | **Ownership of the process-reporting path.** The adversary can freeze, bias, or replay recorded genuine telemetry — Stuxnet's ~21 s loop — so operators and the plant's own shutdown logic see a healthy machine. | Historical. `plant_drive.SensorAttack` models all three. |
| **G6** | **Full knowledge of this design.** The adversary has read `gs/monitor.py`, this document, and `docs/PROOF.md`, and knows every invariant, threshold, window and band. | `gs/attacks.py` is written to this stance: strawmen are deliberately excluded. |
| **G7** | **Patience.** Months of dwell time; payloads whose bursts are weeks apart. | Both intrusions were resident for months before acting. |
| **G8** | **Ability to author and download malicious PLC logic**, and to hijack a comms library on the engineering workstation (Stuxnet's `s7otbxdx.dll` interposition, which made the workstation itself lie about the PLC's contents). | Historical. |
| **G9** | **Control of the raw local measurement path, and the ability to pace a forgery.** Not merely to spike a value, but to hold one steadily inside a chosen band for as long as the attacker likes. | This is the capability that produced the 25/25 falsification. Whether it also yields a *verifying signature* is the A8-LINUX / A8-MU dividing line below. |

### 2.2 Assumed out of reach — and how credible that is

Each is load-bearing. Two of the four are weak, and one has just moved from
"assumed" to "proved".

| # | Assumption | Credibility |
|---|---|---|
| **O1** | **The safety island's own key material and code are not attacker-controlled.** The AI plane cannot write monitor state; its whole channel is the `Command` record. | `docs/PROOF.md`'s A4, and it is **assumed outright — no proof, no review of the actual inter-processor mailbox, no side-channel or fault-injection analysis.** Credible only if the island is a physically separate device with a one-directional interface. If it is a process on the same SoC as the inference plane, this is not credible and most of Section 3 collapses. |
| **O2a** | ~~**A8-LINUX** — an adversary owning the inference plane cannot manufacture corroboration.~~ | **NO LONGER AN ASSUMPTION.** Discharged as theorem **A8L**: with local provenance unauthenticated, such an adversary obtains **zero grants over any trace** (`unsat`), and measured 25/25 → 0/25. It moved into the proved column. It got there by *requiring provenance on both addends*, not by tuning a threshold or a dwell — DW5 proves no threshold or dwell would have worked. |
| **O2b** | **A8-MU** — the adversary does **not** hold the local merging unit's own signing key. | **STILL AN ASSUMPTION, and the thinnest point in the design.** Their forgeries verify, so every check in `gs/monitor.py` passes and the monitor reasons correctly about a number the attacker chose. `unblockable/local_mu_key_holder` and the positive control `control/local_addend_authentic` are byte-identical — the monitor cannot tell them apart, by construction. **This sits in direct tension with G3, which grants the adversary a stolen signing certificate.** The distinction the design relies on is that *command*-signing keys may be stolen while *sensor*-signing keys are not. That distinction is a key-custody claim (non-exportable keys in an HSM at the merging unit, present on no workstation) and **nothing in this repository enforces, exercises or checks it.** |
| **O2c** | The process-domain **observation channel** (tach / current / vibration) is likewise held by a key the adversary does not have. | Same structure, same status: `R_OBSERVATION` requires provenance before the residual's *value* is consulted, which closes the Linux-plane adversary and does nothing about a key holder. An adversary owning that channel holds the residual under the 6.0 σ gate while the rotor does anything. |
| **O3** | **Physical access to the E4 key switch is controlled.** Privileged operations (SETTINGS_CHANGE / LOGIC_DOWNLOAD) require a physical key input the compromised workstation does not have. | Credible against a remote adversary. **Not credible against an insider or anyone standing at the panel** — `LOCAL_PANEL` is a source like any other and physical presence is authority the design does not attempt to revoke. Also defeated if the switch is left engaged during a maintenance window the attacker can wait for (G7). |

### 2.3 Explicitly not modelled

No timing, power, EM or glitch analysis. No compiler-correctness or object-code
argument. No WCET measurement on real silicon. No analysis of the attestation
root's own trustworthiness. **No key lifecycle at all** — see §4.1 item 5.

---

## 3. Kill-chain mapping

**Reading the verdicts.** These four words mean four different things and are
not interchangeable:

* **BLOCK** — the actuation does not reach the plant. A named guard in
  `monitor.decide` returns `False` for this input class.
* **BOUND** — some actuations succeed; the invariant caps how many, how fast,
  or how far. Damage is limited, not zero. **This is not blocking.**
* **DETECT** — the actuation may proceed; the design produces a distinguishable
  signal (a veto reason, a residual, a log entry) that a human must act on.
  **Detection with no human response is worth nothing.**
* **NOT ADDRESSED** — the design has nothing to say. It happens elsewhere, or
  it is indistinguishable from legitimate operation.

Every BLOCK below is additionally **scoped to A8-MU and O2c holding**. Against
a merging-unit key holder, the entire I1 / I1p family degrades to
NOT ADDRESSED, and that is not a hedge — it is DW5, `sat`.

Invariant names are those actually implemented in `gs/monitor.py` (guards in
`decide`, and the veto reason constants `R_*`).

### 3.0 One structural change that moves several verdicts: the TRIP / SWITCH split

`monitor.effective_kind` reclassifies a breaker-open **by its authenticated
source**, never by a params flag (a flag like `"maintenance": true` is
attacker-supplied and would be forged immediately):

* **PROTECTIVE TRIP** — from the automatic plane (`PROTECTIVE_SOURCES = (AI,
  BASELINE)`). Must be corroborated by physics (I1: remote, **local**,
  directional, differential) and latches its own target (I3, per-target).
* **OPERATIONAL SWITCH** — from SCADA, HMI, engineering or the local panel.
  A human-authorised topology change with no fault present. **It faces no
  physics test, because there is deliberately none to demand.**

The first cut demanded fault corroboration for every open, which meant routine
maintenance switching could not be performed through the monitor at all — it
would have been removed from service in week one. The split fixes that and
**deliberately widens the attack surface**, which changes the headline
Industroyer verdict below. It is recorded here rather than buried because I
previously credited I1 with blocking Industroyer's commands, and that is no
longer true.

### 3.1 Stuxnet (2010)

| # | Kill-chain step | Verdict | Mechanism / invariant |
|---|---|---|---|
| 1 | USB/LNK zero-day delivery to an air-gapped network | **NOT ADDRESSED** | Happens on Windows hosts the monitor never sees. |
| 2 | Propagation via Step7 project files and network shares | **NOT ADDRESSED** | Same. |
| 3 | Driver signed with stolen Realtek / JMicron certificates | **NOT ADDRESSED** | G3. `authenticated = sig_valid and identity != ""` checks that a recognised key signed. It cannot distinguish a stolen key from a legitimate one. Nothing here is a defence against certificate theft. |
| 4 | Hijack of `s7otbxdx.dll`, so the workstation misreports the PLC's contents | **NOT ADDRESSED as an intrusion; BOUNDED in effect** | The lie lives on the workstation. The countermeasure is structural, not detective: the monitor does not read the workstation's view of the PLC. Its effect on the *next* step is bounded by E4. |
| 5 | Download of malicious ladder/STL logic to S7-315/417 | **BLOCK, conditional** | **E4** (`R_PRIV_DUAL_SIG`, `R_PRIV_ATTEST`, `R_PRIV_KEYSWITCH`, `R_PRIV_WINDOW`). `LOGIC_DOWNLOAD` requires dual independent signature **and** issuer attestation **and** a physical key switch **and** a maintenance window; the default `maint_window` predicate is `lambda _ms: False`, so an unconfigured monitor denies all privileged operations. Conditional on O3 and on the two signing keys not living on the same compromised host. If they do (G3), E4 reduces to the key switch alone. |
| 5b | Same download, in `RESTRICTED` mode | **BLOCK** | `R_PRIV_RESTRICTED` — a degraded-trust source loses privilege before it loses protection. (The fix to `docs/PROOF.md` §5.1, where v1's `RESTRICTED` was proved decorative.) |
| 6 | Setpoint driven to 1410 Hz against 1064 Hz nominal | **BLOCK** | **E1a** `setpoint_abs_ok` → `R_ENVELOPE_ABS`, against the plant's own commissioning constants imported from `gs/plant_drive.py`. Checked on the **commanded end-state**, never on the reported process value. |
| 7 | Setpoint driven to 2 Hz | **BLOCK** | **E1a**, and independently **E1c** `setpoint_band_clear` → `R_ENVELOPE_RESONANCE`: the descent from 1064 Hz transits a rotor-critical band, and the check covers the whole interval `[min(current,target), max(current,target)]`, not the target alone. Transit matters as much as dwell. |
| 8 | Slow ramp between setpoints, engineered to stay under any rate limiter | **BLOCK** | **E1a** is memoryless in the end-state, so ramp shape is irrelevant to it. **E1b** `setpoint_rate_ok` additionally bounds the torque-limited slew and fails closed on `dt_ms <= 0` (a zero-time step is an unbounded ramp). |
| 9 | Long quiet intervals (~27 days) between bursts, to defeat anomaly detection | **BLOCK, by irrelevance** | No guard in `decide` is a statistical detector, so there is nothing for dwell time to evade. E1 has no memory to poison. |
| 10 | Replay of ~21 s of recorded genuine process values to authorise action | **BLOCK** | **E5** `report_fresh`: accepted only if `sig_valid` **and** `seq` strictly increases for that **association** — `(source, target)`, not source alone, since a counter belongs to a protocol association. A replayed frame's signature verifies and it is still rejected → `R_REPORT_STALE`. |
| 10b | Same replay, deceiving the operators' displays | **NOT ADDRESSED** | The monitor is not the HMI. Operators watching a spoofed display still see a healthy machine; the monitor refuses to let the spoof *authorise* anything. |
| 10c | Same replay, contradicted by independent physics | **BLOCK — now in the enforcement path** | **I1′/I1p**: `process_corroborated` gates the tach/current/vibration residual at `RESIDUAL_MAX_SIGMA = 6.0` → `R_PROCESS_RESIDUAL`, with `R_OBSERVATION` checked **first** — provenance before value, the drive-side twin of `R_LOCAL`. Non-finite and `None` residuals fail closed. Measured separation: benign p99/max 2.65 / 3.50 σ against hidden-step p50 28.0 σ, 97.1 % of hidden steps above the worst benign value. **This corrects my previous pass, which said the residual was modelled but not wired in. It is wired in.** Scoped to O2c: an adversary holding the observation channel's key holds the residual under 6.0 σ at will. |
| 11 | Cumulative fatigue from individually survivable excursions | **BOUND, not blocked** | If steps 6–8 hold, no excursion occurs and the integral stays at zero. If any single excursion slips through inside the envelope, **nothing in the design integrates damage over time.** There is no cumulative-damage invariant. See `attacks.py::unblockable/uncharacterised_resonance`. |
| 12 | Rootkit concealment of the payload on the PLC | **NOT ADDRESSED** | The monitor does not read back or attest PLC program memory. E4 gates *writing* logic; it verifies nothing about what is already there. |

### 3.2 Industroyer / Industroyer2, and the 2015 Ukraine attack

| # | Kill-chain step | Verdict | Mechanism / invariant |
|---|---|---|---|
| 1 | Spear-phish, macro-laden documents, initial foothold | **NOT ADDRESSED** | Upstream. |
| 2 | Months of reconnaissance; theft of HMI/VPN credentials | **NOT ADDRESSED** | G2. |
| 3 | Mapping the substation, enumerating IEC-101/104 IOAs and 61850 logical nodes | **NOT ADDRESSED** | The monitor sees no reconnaissance traffic; it mediates actuation only. |
| 4 | **A single, correctly formed, correctly authenticated breaker OPEN from SCADA or a stolen HMI session, no fault present** | **NOT ADDRESSED — corrected from my previous pass** | Per §3.0, an open from an operator console is reclassified `SWITCH` and **faces no physics test at all.** I previously credited `R_PHYSICS` with blocking exactly this, and that was wrong. What it faces is `R_SWITCH_CUSTODY` (an E4-lite dual-custody gate, **off by default** — `require_switch_custody=False`), then E3 feasibility, with E5/E6/E7 upstream. A single authorised open of a redundant element is **permitted**, because it is indistinguishable from maintenance. |
| 4b | A **protective** trip proposed by the automatic plane with no corroborating fault | **BLOCK** | **I1** — `R_REMOTE`, `R_LOCAL`, `R_DIRECTION`, `R_PHYSICS`. This is where physics is demanded, and it is the AI-proposer path, not Industroyer's path. Scoped to A8-MU. |
| 4c | Same command during a genuine coincident external fault, aimed at the wrong element | **BLOCK on the protective path; BOUND on the operational path** | On the protective path it is **I1's directional discrimination** that rejects it, **not E3** — the pluggable oracle is a generation/load balance check with no notion of which element is which, and `gs/monitor.py` now says so explicitly. On the operational path, E3's `corroboration_on_target` is the only target-awareness in the file. **Do not credit E3 with the protective-path block** — I did, in my previous pass, and it was a misattribution. |
| 5 | **Mass open**: sequential OPEN of every enumerated breaker | **BOUND, not blocked** | **I2/E2** `rate_ok` — a true sliding window over the last `MAX_GRANTS` grant timestamps within `WINDOW_MS`, counted **in aggregate across every source AND every target**. Since the operational path is not asked for physics, **E2 is now the PRIMARY control on the Industroyer path, not a backstop.** Say it precisely: **breakers still open.** A sweep of six to ten spends the budget at the third. |
| 5b | Industroyer2's one-command-per-device variant, designed to defeat per-device counters | **BOUND** | Caught only because the budget is global across targets as well as sources. A per-device counter would see nothing. |
| 5c | Source hopping (AI → SCADA → HMI) to buy fresh rate budget | **BLOCK** | One window, not one per channel. |
| 6 | **Open/close cycling** (Industroyer2) and re-opening after operator restoration (2015) | **BLOCK of the repeat on the protective path, not of the first open** | **I3** `R_LATCHED` — **per-target**, since v2 mediates a fleet of breakers. A global latch meant a latch on breaker A silently supplied the security for breaker B and made the E2 budget unreachable for breaker traffic entirely. CLOSE is not the inverse of TRIP: it needs `reclose_auth` **and** E3 feasibility including reclose dead time and anti-pump. |
| 7 | Protection-relay DoS component (Industroyer's SIPROTEC exploit) | **UNCERTAIN — partially addressed, structurally** | **I6** baseline pass-through: conventional protection is OR-ed at the output and never routed through `decide`, so a compromised or vetoing monitor cannot inhibit it. That is a defence against the monitor *becoming* the DoS. It is **not** a defence against crashing a different, real relay over the network; nothing here hardens or supervises third-party IEDs. Evidence that would settle it: a defined supervision channel for peer relay health, which does not exist. |
| 8 | Wiper component (destroys SCADA/HMI hosts, denies restoration) | **NOT ADDRESSED** | It destroys hosts on the untrusted plane. The monitor survives it (O1) but restores nothing. The design *worsens* recovery in one respect: with the HMIs wiped, the out-of-band `reclose_auth` needed to clear an I3 latch — and the operator `reinstate` needed to leave `BASELINE_ONLY` — are harder to deliver, so breakers stay open. A real operational cost, and it is deliberate: `reinstate` has no timer, because auto-recovery on a timer is groomable. |
| 9 | Settings-group change to desensitise or disable protection | **BLOCK, same conditions as Stuxnet step 5** | **E4** (`SETTINGS_CHANGE` is `PRIVILEGED`). Additionally **I5/T2**: the AI's `req_p0` / `req_k` are clamped *upward* to the floors — a hostile request can only ever make the relay *less* sensitive, and `differential_ok` is proved (T2, T4) to imply `i_diff > max(P0_MIN, K_MIN·i_restraint)` for every real-valued request. |
| 10 | Replay of a previously captured, validly signed measurement to manufacture corroboration | **BLOCK** | **E5** `seq_fresh` / `nonce_fresh` / `report_fresh`, per association. Checked *after* and *independently of* the signature: "authentication answers who said it; it never answers is it true now." |
| 11 | Clock manipulation (PTP/GPS step) to widen the rate window or make a stale frame look fresh | **BLOCK, and counted** | Two mechanisms, deliberately distinct. The window clock is **monotone by construction** (`max(now, last)`), so a rewound timestamp can never widen it — structural, no tolerance parameter; this is the actual fix for `docs/PROOF.md` §5.2 (grants at t = 998, 0, 1000, 999, three inside one window against `MAX_GRANTS = 2`). Separately, a backwards step larger than `CLOCK_SKEW_MS = 10` is refused as a security event (`R_TIME_REGRESSION`); three send the source to `BASELINE_ONLY`. The tolerance exists because Industroyer2's near-simultaneous cross-substation opens genuinely arrive a few ms out of order, and refusing those as clock attacks would mask the real control (E2). |
| 12 | Sustained attempts after repeated vetoes | **DETECT / disown** | **I7** — `vetoes >= VETO_LIMIT/2` → `RESTRICTED` (loses privileged ops and adaptive sensitivity); `>= VETO_LIMIT` → `BASELINE_ONLY`, absorbing absent an authenticated operator `reinstate`. **Two counters, not one:** `vetoes` counts MODEL misbehaviour, `clock_faults` counts INSTRUMENT and CLOCK faults, so a PTP grandmaster failover cannot disown a blameless model or silently withdraw its adaptive sensitivity. |
| 13 | Unauthenticated or unrecognised source attempting actuation | **BLOCK** | **E7** `R_PROVENANCE` — before everything else, at any privilege level. The weakest kind of block: it only stops an adversary who is *not* using G2/G3, i.e. not this one. |

### 3.3 The falsification itself, as a kill chain

| # | Step | Verdict | Mechanism |
|---|---|---|---|
| F1 | Own the local measurement path and pace a forged differential into the band between the sensitivity floor and the nominal 87L pickup | **BLOCK for A8-LINUX; NOT ADDRESSED for A8-MU** | `R_LOCAL`. The forger without a merging-unit key cannot make `local_ok` true: theorem **A8L**, zero grants over any trace, 25/25 → 0/25. The forger *with* the key signs a false local current, `local_ok` is true, and **DW5** stands: 25/25 remains 25/25. |
| F2 | Hold it steadily rather than spiking, to survive any dwell requirement | **NOT ADDRESSED by dwell, at any value** | **DW5** is a proof that this is unfixable by dwell — no `DWELL_MS` rejects a steadily-held forgery. DW1–DW3 bound the *noisy* variant only. This is why the fix was provenance and not a threshold. |
| F3 | Same capability against the process observation channel, holding the residual under 6.0 σ | **BLOCK for the Linux-plane adversary; NOT ADDRESSED for the channel's key holder** | `R_OBSERVATION`, checked before `R_PROCESS_RESIDUAL` — provenance before value. |
| F4 | Reach a call site that never supplied the provenance fields, so the absent default is read as trust | **BLOCK — now fails closed** | Observation **A8C**: the defaults previously resolved to `True`, so an un-updated caller kept granting with no indication that A8-LINUX no longer held for it, and **one missed call site silently restored the 25/25 forgery.** `local_authentic`, `local_fresh`, `residual_authentic`, `residual_fresh` now default to `PROVENANCE_ABSENT`, and absence resolves to **refusal**. A default is not an authentication. |
| F5 | Use the legacy compatibility flag to restore the permissive behaviour | **BOUND and marked, not blocked** | `Monitor(legacy_unauthenticated_channels=True)` is one auditable decision per deployment — deliberately a constructor flag, not a per-`Report` default, since a per-field opt-in rebuilds the hole one call site at a time. Grants issued under it carry the distinct reason `R_GRANT_UNVERIFIED` and a `LogEntry` with `provenance_assumed` and `unverified_channels`, so they are never afterwards mistaken for grants backed by a real check. **It is still a switch that turns the fix off**, and §6.4 makes it a deployment audit question. |

### 3.4 Aggregate

Across the three chains: 17 steps BLOCK (all conditional on A8-MU / O2c, several
also on O1 and O3), 4 BOUND, 1 DETECT, 1 UNCERTAIN, and **11 NOT ADDRESSED** —
enumerated in §4.1. The most consequential change since the previous pass is
that **Industroyer's own commands moved from BLOCK to NOT ADDRESSED** (§3.2 step
4), bounded now only by E2 and E3.

---

## 4. What this design does not prevent

This section is not a caveat appended to a stronger claim. It is the claim.

**GridSentinel is a containment mechanism, not a prevention mechanism.** In
operational terms: prevention would mean the attack does not occur. Containment
means the attack occurs, the adversary is inside, some of what they command
happens, and the design's contribution is that the *physical outcome* is
survivable and the *attempt* is visible. An operator whose substation is under
Industroyer with this monitor in front of the breakers will still lose a breaker
or two, will still restore by hand, and will still have a compromised control
network to rebuild. What they will not have is a de-energised region or a
destroyed rotor — **provided the adversary does not hold a merging-unit key.**
That is the entire value proposition and it should not be described as anything
larger.

### 4.1 Kill-chain steps this design does not address, in full

1. **Initial access** — spear-phishing, malicious documents, VPN credential
   theft, the infected USB, a compromised vendor laptop.
2. **The LNK / removable-media zero-day** and any other host exploitation.
3. **Propagation** — Step7 project files, network shares, lateral movement.
4. **Stolen or fraudulently issued signing certificates as such.** Every check
   verifies that *a* recognised key signed, never that the right party intended
   it. Stuxnet's Realtek/JMicron keys would pass.
5. **The entire key lifecycle — custody, attestation, rotation, revocation.**
   This is now the single largest unaddressed dependency and it deserves its own
   paragraph. The A8-LINUX discharge is worth exactly as much as the claim that
   merging-unit and observation-channel private keys are non-exportable, live in
   an HSM at the sensor, are never present on any workstation, are attested to a
   root the monitor can check, are rotated on a schedule, and can be revoked
   fast enough to matter after a compromise. **Nothing in this repository
   models, exercises or verifies any of that.** There is no key store, no
   attestation verification, no rotation schedule, no revocation list, and no
   test that a revoked key stops being accepted. The monitor *consumes* a
   provenance verdict; it does not *perform* the verification. A `True` in
   `local_authentic` is assumed to reflect a signature and counter check that
   actually ran. **This is where the next defect should be looked for.**
6. **Supply-chain compromise of the toolchain** — the compiler, the build, the
   merging-unit firmware, the sensor firmware, or the attestation root. E5
   assumes the sensor's counter is generated by the sensor. If it is not, every
   physics-corroboration argument in §3 is void.
7. **Hijack of the engineering workstation's comms library** (`s7otbxdx.dll`)
   as an intrusion, and PLC-resident rootkit concealment. The monitor gates
   writes; it never reads back or attests what is already in the PLC.
8. **Insider action, and anyone with physical access to the panel.** The E4 key
   switch is defeated by presence. `LOCAL_PANEL` is deliberately a source like
   any other. An insider holding both dual-control factors defeats E4 entirely.
9. **Any command whose end-state is genuinely survivable.** A single
   authenticated breaker-open, at a feasible operating point, within the rate
   budget, is granted — because that is exactly what a real operator does, and
   after §3.0 it does not even face a physics test. The same holds for a
   setpoint inside the certified band that is simply not what the operator
   wanted, and for margin erosion where every checkpoint is safe
   (`unblockable/slow_low_redundant`: two opens six hours apart, both leaving
   the system N-1 secure, cumulative effect real, invisible to E1 and E2 alike).
   A reference monitor enforces **safety, not intent** — a limit of the concept.
10. **Hazards outside the modelled envelope** — an uncharacterised torsional
    resonance inside the certified band; cumulative fatigue at legal operating
    points. E1 excludes only bands it was told about at commissioning, and
    nothing integrates damage over time.
11. **Physical-layer attacks upstream of the sensors** — a shunt across a CT
    secondary, a shorted VT, a tampered accelerometer, a substituted merging
    unit, GPS spoofing at the antenna. The monitor reasons about signed
    measurements. It cannot reason about a lie told **before** the signature,
    and A8-MU is the sharpest instance of exactly that.
12. **Wiper / destructive payloads on the untrusted plane**, and the loss of
    restoration capability that follows — worsened by the deliberate absence of
    any timer-based recovery from `BASELINE_ONLY`.
13. **Denial of service by veto.** A monitor that refuses everything satisfies
    every invariant here. TRANSPARENCY is one-step; DW4 is the only multi-step
    counterweight, and neither is liveness.

### 4.2 The safety island is now the target

A reference monitor does not remove the high-value target; it **relocates** it.
Before, an attacker needed the engineering workstation. Now they need the safety
island — or, per §3.3, a merging unit's signing key, which is smaller, cheaper
and more numerous. The argument that this is a net improvement rests on the
island being small enough to verify and isolated enough to be unreachable
(assumption O1, asserted, not proved) **and** on the sensor keys being harder to
steal than the workstation credentials the attacker already has. The second half
is an empirical claim about key custody that this project has not tested.

---

## 5. Residual risk and assumptions that could fail

Ordered by how much of the argument dies if the assumption is wrong.

| # | Assumption | Where it is load-bearing | If it fails |
|---|---|---|---|
| **R1** | **O2b / O2c — A8-MU: the adversary does not hold a merging unit's or the observation channel's own signing key.** | The entire I1 and I1p family, I5, I5b, T2, T3, DW1–DW4 — i.e. every physics-corroboration verdict in §3. | Their forgeries verify. The shield's logic remains correct and its conclusions become worthless, because it is reasoning about a number the attacker chose. **DW5 stands unchanged, `sat`, 25/25.** `unblockable/local_mu_key_holder` is byte-identical to the positive control precisely to make this undeniable. Mitigation lives entirely outside this repository — see §4.1 item 5 — and is **unverified, unexercised and unmodelled here.** This is the thinnest point in the design and the tension with G3 is real, not rhetorical. |
| **R2** | **O1 — the isolation boundary.** | Every invariant in Layer 2. | The attacker writes monitor state directly and the document is void. `docs/PROOF.md` states plainly: no proof, no threat model, no review of the mailbox. |
| **R3** | **The v2 monitor's envelope invariants hold.** | All E1–E7 verdicts in §3. | The I1 family is now machine-checked (I1-local, I1-both, A8L, DW1–DW5). **The E1–E7 layer is not.** The provenance prologue, the five/six command kinds, the per-association replay memory, the per-target latch table, operator reinstatement and the effective-kind reclassification have not been through k-induction. Those §3 verdicts rest on **reading the guards.** Evidence that would settle it: re-target `gs/verify.py` at `monitor.decide`/`commit` over the full input space. |
| **R4** | **A6 — reals ≈ IEEE-754.** | T1–T4 and every numeric guard in Layer 1. | The proved margin is 0.02 pu, ~10¹⁴ ULPs at these magnitudes, so rounding cannot plausibly close it — **but that is an argument, not a proof.** No FPA-logic re-proof exists. `process_corroborated` does reject non-finite residuals explicitly rather than relying on the IEEE comparison accident; confirm the same for `differential_ok` before relying on NaN behaviour, since that reasoning does not survive translation to SPARK. |
| **R5** | **The SPARK artifact is correct.** | Everything that would actually ship. | `spark/shield.ads` / `shield.adb` **have never been run through gnatprove — the tool is not installed on this machine.** The artifact with evidence behind it is the Python mirror; the artifact that would go near a substation is the one without. There is **no SPARK mirror of `gs/monitor.py` at all.** Noted in `docs/PROOF.md`: the Ada typing would have made A8C impossible — a stream that does not carry local provenance would not compile — which is one concrete place the unproved artifact is *stronger* than the proved one. |
| **R6** | **Plant-model fidelity.** | A1 (CT error ≤ 12 %), A2 (charging ≤ 0.02 pu), the E1 bands, the 6.0 σ residual gate, the rotor damage integrals. | A1/A2 are assumed, not derived. The slope headroom is `K_MIN − A1 = 0.08`; **if CT error reaches 20 %, T1 is false for all large through-current.** The 6.0 σ gate sits between a measured benign max of 3.50 σ and a hidden-step p50 of 28.0 σ — a defensible placement on *this* model, and the false-positive cost at ramp corners (an estimator artefact `gs/plant_drive.py` flags itself) has not been characterised on real hardware. Resonance bands come off a spin pit, not off this file. The quiet interval between payload bursts is compressed from ~27 days to 120 s: damage per burst is honest, wall-clock spacing is not. |
| **R7** | **The feasibility oracle E3 is certified and correct.** | Industroyer steps 4c and 5, and every CLOSE — and since §3.0, E3 carries more weight than it used to, because the operational path has no physics test behind it. | The default `island_feasible` is a generation-vs-load margin check; `feasibility_unknown` fails closed. Neither is an N-1 contingency analysis. `gs/monitor.py` now states the limit itself: do not credit E3 with the protective-path block. E3's verdicts are only as good as an oracle that does not yet exist. |
| **R8** | **`gs/attacks.py`'s expectations match `gs/monitor.py`'s behaviour.** | The evidence base for §3. | The catalogue is data. It now carries matched positive controls, which is the right structure — a blocked attack next to a byte-identical permitted control is far stronger evidence than either alone. Until a harness is shown running it end-to-end against the monitor, `expected_blocked` remains a claim rather than a measurement. |
| **R9** | **A reference monitor is the right shape of answer.** | The premise. | It relocates the target (§4.2), introduces a denial-of-service surface (§4.1 item 13), and makes restoration harder under a wiper (item 12). Real costs charged against the containment benefit. |

---

## 6. Detection and response

### 6.1 The veto spectrum as a signal

Every veto reason in `gs/monitor.py` is a distinct named constant on purpose:
collapsing two causes into one destroys the signal. Different attacks produce
characteristically different *distributions* over reasons, and the distribution
is more diagnostic than any single veto.

| Observed distribution | Most likely cause |
|---|---|
| **`R_LOCAL`, sustained** | **The falsification's signature.** Something is presenting a local differential addend without provenance. Under A8-LINUX this is the forger being refused; it is also what a genuinely un-updated call site looks like. Both need investigating, and the log's `unverified_channels` field distinguishes them. |
| **`R_OBSERVATION`, sustained** | The same, in the process domain. |
| `R_PROCESS_RESIDUAL` with valid provenance | The reported speed and the independent current/vibration do not describe the same rotor — **replay, freeze or bias in progress**, at ≥ 6.0 σ. |
| `R_PHYSICS` / `R_DIRECTION` on **protective** trips from the AI plane | A hostile or broken proposer. Note this is no longer Industroyer's shape. |
| Bursts of `R_RATE` across several sources or several targets in one window | **Mass-open sweep, or source hopping.** After §3.0 this is the primary Industroyer indicator, since those commands face no physics test. |
| `R_SWITCH_CUSTODY` | Operational switching attempted without dual custody — only visible if `require_switch_custody=True` was configured. |
| `R_LATCHED` on one target, repeatedly | Open/close cycling on that target, or reclose authorisation not arriving. Ambiguous — needs a human. |
| `R_ENVELOPE_ABS` / `R_ENVELOPE_RESONANCE` on SETPOINTs from ENGINEERING, weeks apart | **Stuxnet-shaped.** Long gaps are the tell, not a mitigation. |
| `R_PRIV_KEYSWITCH` / `R_PRIV_WINDOW` on LOGIC_DOWNLOAD **with valid dual signatures and valid attestation** | **The most alarming single line in the log.** The adversary has the credentials and the certificates and is missing only the physical factor. Treat as confirmed compromise of the engineering plane. |
| `R_REPLAY_SEQ` / `R_REPLAY_NONCE` / `R_REPORT_STALE` with valid signatures | Replay in progress. A valid signature over stale data is not a bug in the sender. |
| `R_TIME_REGRESSION`, especially more than once | Deliberate clock manipulation beyond the 10 ms jitter tolerance; three force `BASELINE_ONLY`. Distinguish from `vetoes` — clock faults never touch the model's counter. |
| `R_PROVENANCE` | Comparatively benign — a misconfigured device, or an adversary *without* stolen credentials. Under this threat model, the least interesting alarm. |
| **`R_GRANT_UNVERIFIED` anywhere at all** | A grant that rested on **assumed**, not verified, channel provenance. See §6.4. |
| No vetoes, all traffic in-envelope, and a rising residual below 6.0 σ | The worst case that is still visible: an adversary pacing under the gate. If they hold the observation key, not visible at all (R1). |

### 6.2 What is logged

**`Monitor.submit` appends a `LogEntry` for every mediated command — granted and
vetoed alike.** Logging only vetoes is backwards: a veto record is a record of an
attack that *failed*, and a grant record is the only evidence of one that did
not. Each entry carries:

`t`, `source`, `kind` (post-reclassification), `target`, `granted`, `reason`,
`identity`, `params`, `seq`, `nonce`, `report_seq`, `residual_sigma`, `mode`,
`baseline_trip`, **`provenance_assumed`** and **`unverified_channels`**.

It is a record, not a positionally-decoded tuple. `submit` also preserves the
monitor's own reason when a baseline trip fires — `"baseline-protection|<reason>"`.

*(Correction: a previous revision of this document stated that only vetoes were
logged and that grant logging was a gap. That was true when written and is no
longer true. It should not be quoted, and the deployment-blocker derived from it
should be withdrawn.)*

### 6.3 What a SOC would see, and what a human must decide

A SOC sees the full mediated-command stream with provenance, the mode
transitions (`NORMAL` → `RESTRICTED` → `BASELINE_ONLY`, monotone), and the
drive-domain residual in σ on every entry.

Five decisions cannot be automated and must be taken by a person:

1. **Reclose authorisation.** I3 latches the affected target and only an
   out-of-band `reclose_auth` clears it. Nothing re-energises by itself.
2. **Reinstatement out of `BASELINE_ONLY`.** There is **no timer**, deliberately:
   auto-recovery on a timer is groomable. A reinstate arrives on the same
   authenticated channel as reclose authorisation, resyncs the clock watermark,
   and preserves the replay table, the latch table and the rate window —
   recovery restores authority, not amnesia.
3. **Whether a `BASELINE_ONLY` transition is an attack or a broken sensor.**
   The two counters help: `clock_faults` points at instrumentation, `vetoes` at
   the model.
4. **Whether to run degraded.** Once disowned, the plant runs on conventional
   protection alone — safe, less capable. Someone must decide how long that is
   acceptable.
5. **Whether an in-envelope but unexpected command was authorised.** The monitor
   cannot answer this and will not try (§4.1 item 9).

**Detection without response is worth nothing.** Every DETECT verdict in §3 is
conditional on a human acting within the time the physics allows — bursts, not
seconds, for a rotor accumulating fatigue; minutes for a de-energised feeder.

### 6.4 A deployment audit question, and it is a short one

> **Was this monitor constructed with `legacy_unauthenticated_channels=True`,
> and does the log contain any `R_GRANT_UNVERIFIED` entry?**

That flag makes absent channel provenance resolve to *trust* instead of refusal.
It is only ever correct for replaying historical streams that predate the
provenance fields. Under it, **the A8-LINUX discharge does not hold** — the
25/25 forgery is available again to an adversary with no key at all. It is a
constructor flag rather than a per-`Report` default so that it is one auditable
decision per deployment instead of a hole rebuilt one call site at a time, and
grants taken under it are marked in two independent places (`R_GRANT_UNVERIFIED`
in the reason spectrum, `provenance_assumed` + `unverified_channels` in the log)
so they stay distinguishable after an incident. Any production deployment
answering "yes" to either half of the question above should be treated as
running the falsified design.

---

## 7. Standards mapping

Brief and concrete. This is where the design's claims land, not a conformance
statement; nothing here has been assessed by a certification body.

| Standard | Clause / concept | How this design maps | Gap |
|---|---|---|---|
| **IEC 62443-3-3** | Zones and conduits | Three zones: untrusted inference plane, control plane (SCADA/HMI/engineering), safety island. The **only** conduit into the island is the `Command` record; E7 is conduit enforcement — every path is a `Command`, no privileged channel. | The conduit's physical realisation (the mailbox) is unspecified and unreviewed — O1. |
| | SR 1.1/1.2 identification & authentication | `authenticated = sig_valid ∧ identity ≠ ""` per source; `local_ok` / `remote_ok` / `observation_ok` per **measurement channel**. | Authenticates the key, not the party (G3) — which is precisely A8-MU. |
| | SR 1.5 authenticator management (keys, rotation, revocation) | **Nothing.** | The largest single gap; §4.1 item 5. |
| | SR 2.1 authorisation enforcement; SR 2.8 auditable events | E4 privileged mediation, `R_SWITCH_CUSTODY` for operational switching; and a `LogEntry` for **every** mediated command, granted or vetoed, with identity, params, counters, residual, mode and provenance status. | SR 2.8's retention, integrity protection and export are unaddressed — the log is an in-process Python list. |
| | SR 3.1 communication integrity; SR 4.3 use of cryptography | Signature and counter checks on commands, reports and both differential addends. | The monitor *consumes* verdicts; it does not perform verification, and no key management exists. |
| | SR 6.2 continuous monitoring | The veto spectrum (§6.1). | No export format or SIEM integration. |
| | **SL** | The island targets **SL 3**. **SL 4 is explicitly not claimed** — G3, G6, the insider case and A8-MU are all inside SL 4's adversary and outside what this design blocks. | Claiming SL 3 for the island says nothing about the surrounding zones, which are assumed fully compromised. |
| **NERC CIP-005** | Electronic Security Perimeter; interactive remote access | The island is its own ESP with one conduit. | The design assumes the outer ESPs are already breached (G1, G2) — a compensating control *inside* a failed perimeter, not an ESP control. |
| **NERC CIP-007** | Ports & services; security event monitoring; patch management | Minimal attack surface: no allocation, no unbounded loops, no tasking, no network stack in the island. Event monitoring per §6, now covering grants as well as vetoes. | Patch management for a formally verified island is unaddressed: every patch invalidates the proof. |
| **NERC CIP-010** | Configuration change management; baseline configuration | E4 is a change-control gate at the machine boundary: dual signature + attestation + physical key + maintenance window for `SETTINGS_CHANGE` / `LOGIC_DOWNLOAD`. | CIP-010 also requires *verification* of the baseline. The monitor gates writes and never reads back or attests PLC contents (§4.1 item 7). |
| **IEC 61850-90-5** | Authenticated, session-protected transport of synchrophasor / sampled-value data | The standard the merging-unit channels must implement for O2b/O2c to be credible: authenticated frames with monotone sequence numbers per association, which is exactly what E5 and the `local_ok`/`remote_ok` provenance bits consume. **The both-ends fix is, in standards terms, the requirement that 90-5 be applied at both ends rather than one.** | Nothing here implements or tests 90-5, and 90-5 says nothing about key custody either — which is where A8-MU lives. |
| | 61850-8-1 / 60870-5-104 control | The protocols the adversary is granted (G4). | Protocol authentication is necessary and, per §3.2, not sufficient — and after §3.0 it is the *only* thing operational switching faces besides E2/E3. |
| **IEC 61508** | SIL for the safety island | Shaped for a **SIL 3** claim: a small, allocation-free, loop-free, exception-free, single-threaded decision function with formal contracts; I6 makes it structurally non-interfering with conventional protection, so a monitor failure cannot inhibit a real trip. | **No SIL is claimed.** SIL 3 requires the whole lifecycle — hazard analysis, systematic capability, tool qualification, hardware fault tolerance, PFD figures. This project has machine-checked proofs of one component's I1 family, an unproved SPARK mirror of an earlier version, and no SPARK artifact for `gs/monitor.py` at all. |

---

## 8. Summary

* The design's honest claim is **containment and bounded impact**, and it now
  has a sharp boundary: **A8-LINUX is closed, A8-MU is open.**
* **The falsification is the most important fact in this document.** Only the
  remote differential addend was authenticated; a paced forger owning the local
  channel won **25 of 25** episodes, invisible to conventional protection. The
  fix — provenance on both addends (`R_LOCAL`), and the same for the process
  observation channel (`R_OBSERVATION`) — takes that to **0 of 25** and is
  proved for one adversary (**A8L**, `unsat`). For the adversary holding the
  merging unit's own key it remains **25 of 25** (**DW5**, `sat`), and
  `unblockable/local_mu_key_holder` is byte-identical to the positive control to
  make that impossible to overlook.
* **The fix could not have been a threshold or a dwell.** DW5 proves no dwell
  length rejects a steadily-held forgery. That generalises: against a forged
  input, tuning the consumer is never the answer.
* Provenance now **fails closed** — absent means refused, with `PROVENANCE_ABSENT`
  distinguishing silence from a failed check. The one escape hatch is an
  auditable constructor flag whose grants are marked `R_GRANT_UNVERIFIED` (§6.4).
* Against **Industroyer**, the load-bearing controls are now **E2** (the global
  aggregate budget) and **E3** — *not* I1, because operational switching from an
  operator console faces no physics test by design (§3.0). This corrects the
  previous revision of this document.
* Against **Stuxnet**, they are **E1** (the commanded end-state is checked, never
  the reported one), **E4** (a physical key switch the workstation lacks), **E5**
  (the 21 s replay authorises nothing) and **I1p** (the independent residual, now
  in the enforcement path at 6.0 σ).
* **11 kill-chain steps are not addressed at all** (§4.1). One is UNCERTAIN.
* The three sharpest gaps between claim and evidence: **key custody, attestation,
  rotation and revocation are entirely unmodelled** (§4.1 item 5 — the next defect
  is expected here), the **E1–E7 envelope layer is unverified** (R3), and the
  SPARK artifact has **never been through gnatprove** (R5).
