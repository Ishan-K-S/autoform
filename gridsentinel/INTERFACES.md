# GridSentinel — module contracts (frozen; do not change signatures)

Python: `./.venv/bin/python` (z3-solver, scikit-learn, hypothesis, pandapower, matplotlib).
Per-unit base: 100 MVA, 345 kV. Always pass `numba=False` to pandapower to silence warnings.

## Architecture
Untrusted plane (AI, Linux) proposes; trusted plane (shield, safety island) disposes.
Baseline protection runs unconditionally and can never be inhibited.

## gs/power.py  [owner: agent A1]
    ZL : complex                      # protected line series impedance, pu
    class Solution: V_s, I_s, I_r, V_r  (complex, pu; I_* flow INTO protected line)
        .z_app        -> complex      # V_s / I_s
        .i_diff       -> float        # |I_s + I_r|, charging-compensated
        .i_through    -> float        # 0.5*(|I_s|+|I_r|)
    solve(delta_deg=8.0, fault_node=None, rf=0.0, m=0.5, a=0.5) -> Solution
        fault_node in {None,"F","G","B"}  F=internal, G=external-forward, B=external-reverse
        rf in per-unit
    prefault(delta_deg=8.0) -> Solution
    self_check() -> list[(str, bool)]

## gs/measure.py  [owner: agent A2]
    CYCLE_MS=20.0  EVENT_MS=20  HORIZON_MS=400  NOMINAL_DELTA=8.0
    A1_CT_ERROR=0.12  A2_CHARGING=0.02        # proof assumptions, hard-clamped
    class Sample: t,i_diff,i_restraint,z_app,v_mag,di_fast,harmonic,
                  remote_fresh,remote_authentic,time_quality_ok,forward
    class Scenario: name,family,internal_truth, + injection flags
    run_scenario(sc, seed=0) -> iterator[Sample]

## gs/scenarios.py  [owner: agent A2]
    catalogue(n_per_family=..., seed=...) -> list[Scenario]

## gs/relay.py  [owner: agent A2]
    class BaselineRelay: .step(sample)->bool ; .trip_t ; .trip_element

## gs/shield.py  [FROZEN - spec artifact, do not edit]
    thresholds(cert_ok) ; differential_ok(i_diff,i_restraint,cert_ok,req_p0,req_k)
    decide(st, now_ms, want_trip, (time_ok,remote_ok,forward,diff_ok,reclose_auth)) -> (grant,reason)
    commit(st, now_ms, granted, want_trip, reclose_auth)
    class Shield: .step(sample, proposal, baseline_trip, cert_ok, reclose_auth) -> (trip,source,reason)
    Constants: P0_NOM=.30 K_NOM=.35 P0_MIN=.10 K_MIN=.20 A1_CT_ERROR=.12 A2_CHARGING=.02
               MAX_GRANTS=2 WINDOW_MS=1000 VETO_LIMIT=24
               NORMAL=0 RESTRICTED=1 BASELINE_ONLY=2

## gs/ai.py  [owner: agent A4]
    features(buffer) -> list[float]           # causal, from Samples seen so far
    class Policy: .propose(buffer) -> shield.Proposal ; .cert_ok(buffer) -> bool
    HonestPolicy / AlwaysTripPolicy / MaxSensitivityPolicy / StealthyPolicy
    train(seed=...) -> HonestPolicy ; save/load to models/

## gs/verify.py  [owner: agent A3]
    Z3 proofs. prove_sensitivity_floor() ; prove_shield_invariants() -> dict of results

## tests/, run.py, gs/report.py  [owner: agent A5]
