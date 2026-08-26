#!/usr/bin/env python
"""GridSentinel experiment runner.

Drives the whole scenario catalogue through three arms and writes a
machine-readable comparison to out/results.json.

    A  baseline       conventional protection alone (gs.relay.BaselineRelay)
    B  ai_unshielded  the AI's proposal wired STRAIGHT to the trip coil
    C  ai_shielded    AI proposes, gs.shield gates, baseline OR-ed at output

Each arm is run with the honest policy and with every adversarial policy in
gs.ai.  Arm B is the ablation: it is what the appliance would do if you
believed the model.  Arm C is the design.  Arm A is the incumbent.

Usage:
    ./.venv/bin/python run.py --seed 0
"""

import argparse
import json
import os
import statistics
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from gs import ai, measure, relay, shield  # noqa: E402

ARMS = ("baseline", "ai_unshielded", "ai_shielded")
OUT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "out")


# --- one episode ------------------------------------------------------------

def replay_samples(sc, seed):
    """Materialise one episode's telemetry.

    A power-swing scenario ramps the load angle every millisecond and can walk
    past the steady-state stability limit, at which point pandapower's
    Newton-Raphson does not converge and gs/power.py raises.  Such an episode
    is NOT silently dropped -- dropping it would quietly shrink the swing
    family and flatter every arm.  It is counted and reported.
    """
    try:
        return list(measure.run_scenario(sc, seed=seed)), None
    except Exception as exc:
        return None, "%s: %s" % (type(exc).__name__, exc)


def baseline_trip_times(samples):
    """Per-millisecond baseline trip flags + (first trip t, element)."""
    r = relay.BaselineRelay()
    flags = []
    for s in samples:
        flags.append(bool(r.step(s)))
    return flags, r.trip_t, r.trip_element


def policy_trace(policy, samples):
    """Precompute the AI's proposals for one episode.

    The AI sees only the telemetry, which is identical in every arm, so its
    proposal stream can be computed once and replayed into all three arms.
    That is not a shortcut: the AI has no feedback path from the trip coil.
    """
    if hasattr(policy, "reset"):
        policy.reset()
    buf = []
    out = []
    for s in samples:
        buf.append(s)
        p = policy.propose(buf)
        out.append((bool(p.want_trip), p.req_p0, p.req_k,
                    float(p.confidence) if p.confidence == p.confidence else 0.0,
                    bool(policy.cert_ok(buf))))
    return out


def run_arm_baseline(samples, base_flags, base_t, base_elem):
    return {"trip": base_t is not None, "trip_t": base_t,
            "source": "baseline" if base_t is not None else None,
            "element": base_elem, "vetoes": {}, "mode": "NORMAL",
            "grants": 0, "shield_grant_t": None}


def run_arm_unshielded(samples, proposals):
    """No shield, no baseline: the model's word is the trip command."""
    for s, (want, _p0, _k, _c, _cert) in zip(samples, proposals):
        if want:
            return {"trip": True, "trip_t": s.t, "source": "ai",
                    "element": None, "vetoes": {}, "mode": "NONE",
                    "grants": 1, "shield_grant_t": None}
    return {"trip": False, "trip_t": None, "source": None, "element": None,
            "vetoes": {}, "mode": "NONE", "grants": 0, "shield_grant_t": None}


def run_arm_shielded(samples, proposals, base_flags, base_elem):
    """Arm C, run over the WHOLE horizon -- deliberately without stopping at
    the first trip.

    Stopping at the first output trip would make the safety claim unfalsifiable
    in exactly the case that matters: if the baseline mis-operates at t=21 and
    the shield would have granted an accelerated trip on the same healthy line
    at t=25, an early break hides the grant and the report says "the shield
    granted nothing".  The breaker is not modelled anyway, so continuing to the
    horizon is simply "what the shield does with this telemetry".

    `trip_t` is still the FIRST trip (that is the operational answer);
    `shield_grant_t` is the first time the shield granted in its own right,
    whether or not the baseline had already fired.
    """
    sh = shield.Shield()
    vetoes = {}
    trip_t = None
    source = None
    element = None
    grant_t = None
    n_grants = 0
    for s, (want, p0, k, c, cert), base in zip(samples, proposals, base_flags):
        prop = shield.Proposal(want_trip=want, req_p0=p0, req_k=k, confidence=c)
        latched_before = sh.st.latched
        trip, src, reason = sh.step(s, prop, base, cert, reclose_auth=False)

        # `Shield.step` returns reason="baseline-protection" whenever the
        # baseline is tripping, which MASKS the decide() result underneath --
        # including a grant.  Read the grant off the shield's own state
        # instead: `commit` appends to grant_times (and sets latched) on, and
        # only on, a grant.  Without this the strict safety test would report
        # zero grants purely because the baseline happened to fire first.
        gt = getattr(sh.st, "grant_times", None)
        granted = (gt[-1] == s.t if gt else
                   (sh.st.latched and not latched_before))
        if granted:
            n_grants += 1
            if grant_t is None:
                grant_t = s.t
        elif want and reason.startswith("veto:"):
            vetoes[reason] = vetoes.get(reason, 0) + 1

        if trip and trip_t is None:
            trip_t = s.t
            source = src
            element = base_elem if src == "baseline" else None
    return {"trip": trip_t is not None, "trip_t": trip_t, "source": source,
            "element": element, "vetoes": vetoes, "shield_grant_t": grant_t,
            "mode": shield.MODE_NAMES[sh.st.mode], "grants": n_grants}


# --- experiment -------------------------------------------------------------

def build_policies(seed, retrain=False, verbose=True):
    """Load the honest policy, refitting it if the cached model is stale.

    models/ is a build artefact of gs/ai.py, which is owned by another agent
    and evolves (the feature vector has changed width at least once).  A model
    that no longer matches `ai.features()` must be refitted, not worked
    around, or the experiment silently measures the wrong classifier.
    """
    honest = ai.get_policy(retrain=retrain)
    if not retrain:
        try:
            probe = list(measure.run_scenario(
                measure.Scenario("probe", "probe", fault_node="F", rf=0.1),
                seed=0))[:measure.EVENT_MS + 5]
            honest.propose(probe)
            honest.cert_ok(probe)
        except Exception as exc:
            if verbose:
                print("cached model is stale (%s); refitting" % exc)
            honest = ai.get_policy(retrain=True)
        honest.reset()
    return [honest, ai.AlwaysTripPolicy(), ai.MaxSensitivityPolicy(),
            ai.StealthyPolicy()]


def experiment(seed=0, n_per_family=8, retrain=False, verbose=True):
    t0 = time.time()
    cat = ai.catalogue(n_per_family=n_per_family, seed=seed)
    policies = build_policies(seed, retrain=retrain, verbose=verbose)
    if verbose:
        print("scenarios: %d  policies: %s"
              % (len(cat), [p.name for p in policies]))

    episodes = []
    nonconvergent = []
    for i, sc in enumerate(cat):
        samples, err = replay_samples(sc, seed=seed * 7919 + i * 977 + 13)
        if samples is None:
            nonconvergent.append({"scenario": sc.name, "family": sc.family,
                                  "internal_truth": bool(sc.internal_truth),
                                  "error": err})
            if verbose:
                print("  NON-CONVERGENT episode dropped: %s (%s) -- %s"
                      % (sc.name, sc.family, err))
            continue
        base_flags, base_t, base_elem = baseline_trip_times(samples)
        for pol in policies:
            props = policy_trace(pol, samples)
            rows = {
                "baseline": run_arm_baseline(samples, base_flags, base_t,
                                             base_elem),
                "ai_unshielded": run_arm_unshielded(samples, props),
                "ai_shielded": run_arm_shielded(samples, props, base_flags,
                                                base_elem),
            }
            for arm, r in rows.items():
                r = dict(r)
                r.update({"scenario": sc.name, "family": sc.family,
                          "internal_truth": bool(sc.internal_truth),
                          "policy": pol.name, "arm": arm,
                          "latency_ms": (None if r["trip_t"] is None
                                         else r["trip_t"] - measure.EVENT_MS)})
                episodes.append(r)
        if verbose and (i + 1) % 10 == 0:
            print("  %d/%d scenarios (%.1fs)"
                  % (i + 1, len(cat), time.time() - t0))
    return cat, policies, episodes, nonconvergent


# --- aggregation ------------------------------------------------------------

def _pct(vals, q):
    if not vals:
        return None
    vals = sorted(vals)
    if len(vals) == 1:
        return float(vals[0])
    pos = q * (len(vals) - 1)
    lo = int(pos)
    hi = min(lo + 1, len(vals) - 1)
    return float(vals[lo] + (vals[hi] - vals[lo]) * (pos - lo))


def summarise(episodes):
    """Aggregate by (policy, arm) and by (policy, arm, family)."""
    by_arm = {}
    by_family = {}
    for e in episodes:
        for key, table in (((e["policy"], e["arm"]), by_arm),
                           ((e["policy"], e["arm"], e["family"]), by_family)):
            k = "|".join(key)
            d = table.setdefault(k, {
                "policy": e["policy"], "arm": e["arm"],
                "family": key[2] if len(key) > 2 else None,
                "n": 0, "n_benign": 0, "n_internal": 0,
                "false_trips": 0, "missed": 0, "correct_trips": 0,
                "latencies": [], "vetoes": {},
                "baseline_only_episodes": 0, "grants": 0,
                "false_trip_scenarios": [],
                "pre_inception_trips": 0,
                "shield_grants_on_benign": 0,
                "shield_grant_on_benign_scenarios": [],
            })
            d["n"] += 1
            d["grants"] += e["grants"]
            # Integrity check: a trip before EVENT_MS is a trip on the healthy
            # pre-fault load point.  It is never protection, whatever the
            # scenario's ground truth, and it silently flatters both the
            # dependability and the latency columns if left uncounted.
            if e["trip_t"] is not None and e["trip_t"] < measure.EVENT_MS:
                d["pre_inception_trips"] += 1
            if e["mode"] == "BASELINE_ONLY":
                d["baseline_only_episodes"] += 1
            for r, c in e["vetoes"].items():
                d["vetoes"][r] = d["vetoes"].get(r, 0) + c
            if e["internal_truth"]:
                d["n_internal"] += 1
                if e["trip"]:
                    d["correct_trips"] += 1
                    d["latencies"].append(e["latency_ms"])
                else:
                    d["missed"] += 1
            else:
                d["n_benign"] += 1
                if e.get("shield_grant_t") is not None:
                    d["shield_grants_on_benign"] += 1
                    d["shield_grant_on_benign_scenarios"].append(
                        {"scenario": e["scenario"], "family": e["family"],
                         "t": e["shield_grant_t"]})
                if e["trip"]:
                    d["false_trips"] += 1
                    d["false_trip_scenarios"].append(
                        {"scenario": e["scenario"], "family": e["family"],
                         "t": e["trip_t"], "source": e["source"],
                         "element": e["element"]})

    for table in (by_arm, by_family):
        for d in table.values():
            lat = d["latencies"]
            d["median_latency_ms"] = (float(statistics.median(lat))
                                      if lat else None)
            d["p95_latency_ms"] = _pct(lat, 0.95)
            d["dependability"] = (d["correct_trips"] / d["n_internal"]
                                  if d["n_internal"] else None)
            d["security"] = (1.0 - d["false_trips"] / d["n_benign"]
                             if d["n_benign"] else None)
    return by_arm, by_family


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--n-per-family", type=int, default=8)
    ap.add_argument("--retrain", action="store_true",
                    help="refit the honest policy instead of loading models/")
    ap.add_argument("--out", default=os.path.join(OUT_DIR, "results.json"))
    ap.add_argument("--no-report", action="store_true")
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args(argv)

    cat, policies, episodes, nonconvergent = experiment(
        seed=args.seed, n_per_family=args.n_per_family,
        retrain=args.retrain, verbose=not args.quiet)
    by_arm, by_family = summarise(episodes)

    results = {
        "seed": args.seed,
        "n_per_family": args.n_per_family,
        "n_scenarios": len(cat),
        "n_scenarios_simulated": len(cat) - len(nonconvergent),
        "nonconvergent_episodes": nonconvergent,
        "families": sorted({sc.family for sc in cat}),
        "policies": [p.name for p in policies],
        "arms": list(ARMS),
        "constants": {
            "P0_NOM": shield.P0_NOM, "K_NOM": shield.K_NOM,
            "P0_MIN": shield.P0_MIN, "K_MIN": shield.K_MIN,
            "MAX_GRANTS": shield.MAX_GRANTS, "WINDOW_MS": shield.WINDOW_MS,
            "VETO_LIMIT": shield.VETO_LIMIT, "EVENT_MS": measure.EVENT_MS,
            "HORIZON_MS": measure.HORIZON_MS,
        },
        "lemma": shield.lemma_sensitivity_floor(samples=20001),
        "by_arm": by_arm,
        "by_family": by_family,
        "episodes": episodes,
    }

    if not os.path.isdir(os.path.dirname(args.out)):
        os.makedirs(os.path.dirname(args.out))
    with open(args.out, "w") as fh:
        json.dump(results, fh, indent=1, sort_keys=True)
    if not args.quiet:
        print("wrote", args.out)

    if not args.no_report:
        from gs import report
        report.render(results, out_dir=os.path.dirname(args.out))
    return results


if __name__ == "__main__":
    main()
