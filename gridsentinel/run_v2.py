"""GridSentinel v2 experiment: run the adversary catalogue through the
generalised actuation reference monitor, and run the Stuxnet payload through
the drive plant in three mitigation arms.

The claim under test is that gs/monitor.py blocks the ACTUATION of both
Stuxnet-class and Industroyer-class attacks.  Nothing in the repository
previously ran one against the other, so the claim was unfalsifiable.  This
file makes it falsifiable, and scores three things SEPARATELY because they
fail in different ways:

  (a) BLOCK RATE on scenarios the catalogue claims are blocked.
  (b) NEGATIVE CONTROLS: the `unblockable` family must NOT be blocked.  A
      block there is over-blocking (the monitor would break legitimate
      operations) or a mis-classification in gs/attacks.py.
  (c) RIGHT-REASON RATE: of the blocked scenarios, how many were blocked by
      the invariant that was EXPECTED to block them.  A scenario blocked by
      the wrong invariant is a latent fragility: the invariant we believe is
      load-bearing is not the one doing the work.

----------------------------------------------------------------------------
THE JUDGING HARNESS, AND EVERY MODELLING CHOICE IN IT
----------------------------------------------------------------------------
gs/attacks.py is deliberately data: it names sources and kinds as strings and
carries domain params ("target_hz", "breaker", "corroboration") that the
monitor's vocabulary ("target", "dt_ms", Report.i_diff) does not share.  A
harness has to bridge that, and every bridging choice can flatter or damn the
design, so all of them are listed here and implemented in `_world` below.

  * PHYSICS.  gs/monitor.py grants a TRIP only on an independently-keyed
    Report showing a real differential.  The attacks are, by construction,
    against HEALTHY plant, so the honest Report is i_diff = 0.01 pu on
    i_restraint = 1.0 pu.  That is the truthful world for a mass-open of
    healthy feeders -- and it means I1 (`no-physics-corroboration`) usually
    speaks before E2 ever gets to count.  That is a real result, not a
    harness artefact, and it is reported as a right-reason mismatch.
  * The ONE exception is adaptive/fault_coincident_malicious_trip, whose
    params describe a genuine EXTERNAL through-fault: high through current,
    charging-level differential, directional REVERSE.
  * REPLAYED CORROBORATION.  adaptive/stale_signed_measurement_replay carries
    a corroborating frame with sequence 41 and fresh=False.  The monitor's
    replay memory only bites if it has already seen something later, so the
    harness starts every scenario's report counter at REPORT_SEQ0 = 1000,
    modelling a monitor that has been receiving live sensor frames all along.
    Without that the replayed frame would be the FIRST frame the monitor ever
    saw and E5 could not fire -- which would be a harness artefact.
  * FEASIBILITY (E3).  Default TRUE: the attacker picks feasible operating
    points, and a permissive default is the honest one because a conservative
    default would manufacture blocks.  It is FALSE only where the scenario's
    own params say so: the 4th open of grid/slow_and_low_topology
    ("erodes to N-1 violation on 4th open") and any CLOSE whose dead_time_ms
    is under ANTI_PUMP_MS (grid/rapid_open_close_cycling's 40 ms).
  * PRIVILEGED FACTORS (E4).  maint_window is TRUE for every scenario: an
    attacker inside for months picks his moment, and leaving it False would
    let R_PRIV_WINDOW block E4 scenarios for a reason the catalogue is not
    claiming.  Dual signature / attestation / key switch are FALSE except
    where the scenario says the adversary holds them
    (unblockable/insider_dual_control: "BOTH dual-control factors held",
    "every authorisation factor genuinely satisfied").
  * SETPOINT dt.  The catalogue gives command times but no dt; the harness
    uses the gap to the previous command in the same scenario, and 1000 ms
    for the first one.  A zero gap fails closed inside the monitor, which is
    correct behaviour but would be a harness-chosen block, so it is avoided
    for the first command only.
  * PROCESS VALUE.  The monitor's `current` for the E1 rate/band checks is
    the last GRANTED setpoint, starting at 1064 Hz nominal -- i.e. the plant
    follows only what the monitor permitted.

TWO PASSES, and why the second one exists.  Guard order in `decide` means one
invariant can permanently shadow another: if I1 refuses every trip for want of
physics, E2 never counts and we learn nothing about whether the rate limit
works.  So every scenario is also run ATTACKER-FAVOURABLE: full physics
corroboration, feasible, strictly-increasing per-source sequence and nonce,
reclose authorisation granted.  Everything the expected invariant does not
cover is handed to the attacker.  If the expected invariant still fires, it is
load-bearing and merely shadowed; if it does not, the attribution in
gs/attacks.py is wrong.  Both passes are reported.

----------------------------------------------------------------------------
THE DRIVE EXPERIMENT (Task 3)
----------------------------------------------------------------------------
Arm A  unmitigated: the payload drives the rotor directly.
Arm B  the monitor mediates every SETPOINT, and the Report it reasons from
       carries the COMPROMISED speed channel -- the one the attacker is
       replaying.  This is the "trust the reported process state" arm.
Arm C  identical, except the Report carries the independently-keyed
       tachometer instead of the replayed channel.  Nothing else changes.

The two arms differ in EXACTLY ONE variable, which is the whole point: both
present the monitor with the same commands and the same (replayed) reported
process value, and the reported value is what the E1 rate and critical-band
checks are computed against.  Arm B leaves the independent observation
channel unwired -- `Report.residual_sigma = 0.0`, which is what "trusting the
reported process state" means numerically: the report is assumed consistent
with itself.  Arm C wires it: `Report.residual_sigma =
plant_drive.residual(reported speed, its rate, motor current, casing
vibration)`, which the patched gs/monitor.py consumes through
`process_corroborated` (veto R_PROCESS_RESIDUAL, I1'). Nothing else changes.

A NOTE ON WHAT ARM B ALREADY GETS FOR FREE.  Since the envelope constants
were bound to the plant's commissioning data, E1a is the qualified band
[1000, 1100] Hz -- and E1a does NOT consult the reported process value at
all.  It is therefore immune to the replay by construction, and no replayed
report can buy a setpoint outside it.  Whether the residual is load-bearing
for DAMAGE in this payload is exactly the question arm B vs arm C answers,
and the answer is reported as measured, not as hoped.
"""

from __future__ import print_function

import argparse
import json
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from gs import attacks, monitor as M, plant_drive as P  # noqa: E402

OUT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "out")

REPORT_SEQ0 = 1000          # live sensor frames already seen (see header)
ANTI_PUMP_MS = 300          # minimum reclose dead time (E3)
NOMINAL_HZ = 1064.0

# THE HARNESS'S OWN DEFAULT, named rather than implicit.
#
# gs/monitor.py closed its fail-open provenance default: an absent annotation
# is PROVENANCE_ABSENT and is refused.  The same pattern existed one layer up
# in this file -- a scenario that said nothing about its channels silently
# became an assertion that they were honest -- and an unnamed `= True` in a
# judging harness is exactly as unauditable there as it was in the monitor.
#
# It is still True, and here is the justification, which is a real one and not
# a shrug: the catalogue's premise is that these attacks arrive through the
# LEGITIMATE control path with genuine credentials against healthy plant, so
# the sensor infrastructure a scenario does not mention is honest BY
# CONSTRUCTION.  Setting PROVENANCE_ABSENT instead would veto all 27 scenarios
# at I1 and measure nothing.
#
# What is NOT acceptable is for that assumption to be invisible, so every
# command that relies on it is counted and the total is reported: see
# `harness_provenance_assumptions` in the results.  A reader can then see
# exactly how much of the block rate rests on a harness assumption rather than
# on something a scenario actually asserted.
HARNESS_ASSUMES_HONEST_CHANNEL = True

SOURCE_OF = {n: v for v, n in M.SOURCE_NAMES.items()}
KIND_OF = {n: v for v, n in M.KIND_NAMES.items()}

# Which monitor veto reason belongs to which catalogue invariant.  Derived
# from the reason strings themselves (they are named E#/I# on purpose), never
# guessed: `R_RATE` is "veto:I2-E2-cross-source-rate-limit", so it maps to E2.
REASON_INVARIANT = {
    M.R_PROVENANCE: "E7",
    M.R_BASELINE_MEDIATED: "E7",
    M.R_TIME_REGRESSION: "E6",
    M.R_TIME: "E6",
    M.R_REPLAY_SEQ: "E5",
    M.R_REPLAY_NONCE: "E5",
    M.R_REPORT_STALE: "E5",
    M.R_MODE: "I7",
    M.R_LATCHED: "I3",
    M.R_RATE: "E2",
    M.R_REMOTE: "I1",
    M.R_DIRECTION: "I1",
    M.R_PHYSICS: "I1",
    M.R_ENVELOPE_ABS: "E1",
    M.R_ENVELOPE_RATE: "E1",
    M.R_ENVELOPE_RESONANCE: "E1",
    M.R_INFEASIBLE: "E3",
    M.R_PRIV_RESTRICTED: "E4",
    M.R_PRIV_DUAL_SIG: "E4",
    M.R_PRIV_ATTEST: "E4",
    M.R_PRIV_KEYSWITCH: "E4",
    M.R_PRIV_WINDOW: "E4",
    M.R_UNKNOWN_KIND: "E7",
    M.R_PROCESS_RESIDUAL: "I1p",
    # Added when the both-ends fix landed.  Without these two the right-reason
    # metric would return None for the very guards it exists to police, which
    # would be the exact misattribution failure the metric was built to catch.
    M.R_LOCAL: "I1",            # the differential's LOCAL addend
    M.R_OBSERVATION: "I1p",     # the process observation channel
    M.R_SWITCH_CUSTODY: "E4",   # E4-lite on operational switching
}

# A veto reason with no invariant silently corrupts the right-reason rate, so
# the mapping is checked for completeness at import rather than trusted.
_UNMAPPED = sorted(
    v for k, v in vars(M).items()
    if k.startswith("R_") and isinstance(v, str)
    and v.startswith("veto:") and v not in REASON_INVARIANT)
if _UNMAPPED:                                            # pragma: no cover
    raise RuntimeError("run_v2.REASON_INVARIANT is missing an entry for the "
                       "veto reason(s) %r -- the right-reason metric would "
                       "report None for them" % (_UNMAPPED,))


# ==========================================================================
# TASK 2 -- the catalogue against the monitor
# ==========================================================================

GRANT_REASONS = (M.R_GRANT, M.R_GRANT_UNVERIFIED)


def _is_grant(reason):
    """`R_GRANT_UNVERIFIED` is a GRANT whose channel provenance was ASSUMED
    under `Monitor(legacy_unauthenticated_channels=True)`, not a veto.  Scoring
    it as a block would report a legacy deployment -- the one still exposed to
    the paced forger -- as if it were the safest configuration in the run,
    which is precisely backwards.  The import-time completeness check below
    only polices `veto:` reasons, so this one has to be handled by hand."""
    return reason in GRANT_REASONS


def _identity(cmd):
    p = cmd.params
    for k in ("operator", "cert_subject", "plc", "relay", "drive", "breaker"):
        if k in p:
            return str(p[k])
    return cmd.source.lower() + "-session"


def _has(cmd, needle):
    return any(needle in str(v).lower() for v in cmd.params.values())


def _world(sc, cmd, i, prev_t, sp_current, favourable, keep=None):
    """Map one catalogue Cmd onto (monitor.Command, monitor.Report, maint,
    reclose_auth).  Every choice here is justified in the module header."""
    src = SOURCE_OF[cmd.source]
    kind = KIND_OF[cmd.kind]
    p = dict(cmd.params)

    corro = p.get("corroboration")
    insider = _has(cmd, "both dual-control") or _has(cmd, "genuinely satisfied")
    # The attacker-favourable pass hands the attacker everything EXCEPT the
    # inputs of the invariant that is expected to block: handing those over
    # too would remove the very thing under test and prove nothing.
    keep_e5 = (keep == "E5")
    fav_phys = favourable and keep not in ("E3",)

    # ---- the honest physical world the monitor's own sensors report -------
    if corro is not None and not fav_phys:
        i_diff, i_restraint, forward = float(corro.get("i_diff_pu", 0.0)), 1.0, True
    elif "through_current_pu" in p and not fav_phys:
        thr = float(p["through_current_pu"])
        i_diff, i_restraint = P_CHARGING * thr, thr      # external through-fault
        forward = "reverse" not in str(p.get("directional", "")).lower()
    elif fav_phys:
        i_diff, i_restraint, forward = 50.0, 0.0, True   # full corroboration
    elif favourable:
        # E3 scenario: corroborate the physics but preserve the direction /
        # target-specificity the scenario describes, since that is what E3 is
        # being asked to catch.
        i_diff, i_restraint = 50.0, 0.0
        forward = "reverse" not in str(p.get("directional", "")).lower()
    else:
        i_diff, i_restraint, forward = 0.01, 1.0, True   # HEALTHY plant

    # ---- I1 / I1' CHANNEL PROVENANCE -------------------------------------
    # `i_diff = |I_local + I_remote|`: authenticating only the remote addend
    # leaves the sum under an adversary who owns the local channel, which is
    # how a paced forger won 25/25.  These four fields default to True inside
    # gs/monitor.py so that pre-existing report streams keep working -- but a
    # default is not an authentication, and a harness that leaves them
    # defaulted is not testing the guard at all.  So every Report this file
    # builds sets all four EXPLICITLY, derived from what the scenario models.
    #
    # What the catalogue actually models: the corroboration annotations
    # (`sig_valid`, `fresh`) describe the merging-unit frame, so they drive
    # the local addend's provenance.  For the process domain, gs/plant_drive
    # is explicit that the attacker owns the speed-REPORTING path and not the
    # separately-keyed tach / current / vibration channel -- that asymmetry is
    # the stated premise of `residual()` -- so `sensor_channel: "replayed"`
    # compromises the reported value, NOT the observation channel, and
    # residual provenance stays authentic and fresh.  Forging the observation
    # channel is a threat the catalogue does not contain; it is covered by
    # the harness-owned probes in `provenance_probes()` instead of by
    # inventing a catalogue entry in a file this agent does not own.
    if corro is not None:
        local_authentic = bool(corro.get("sig_valid", True))
        local_fresh = bool(corro.get("fresh", True))
    else:
        local_authentic = local_fresh = HARNESS_ASSUMES_HONEST_CHANNEL

    # The process-domain twin, wired the same way and for the same reason.
    # Earlier revisions of this file hardcoded these two True and read no
    # observation annotation, so `provenance/observation_channel_forged` was
    # GRANTED by the harness even though gs/monitor.py would have vetoed it.
    # The catalogue author measured that gap and left the row red rather than
    # relabelling the scenario to make the number green; `observation` is
    # shaped like `corroboration` on purpose so this is the same mapping.
    obs = p.get("observation")
    if obs is not None:
        residual_authentic = bool(obs.get("sig_valid", True))
        residual_fresh = bool(obs.get("fresh", True))
    else:
        residual_authentic = residual_fresh = HARNESS_ASSUMES_HONEST_CHANNEL

    # ---- E5 report freshness ---------------------------------------------
    if corro is not None and not corro.get("fresh", True) \
            and (keep_e5 or not favourable):
        rseq = int(corro.get("sequence", 0))             # the replayed frame
    else:
        rseq = REPORT_SEQ0 + i + 1

    # ---- E1 setpoint mapping ---------------------------------------------
    # dt for the rate bound: the real gap to the previous command in this
    # scenario.  For the FIRST command there is no previous one, and picking
    # a small dt would manufacture an E1b veto that the harness, not the
    # attack, is responsible for.  So the first command is given exactly the
    # time the drive would need at its torque limit -- the most generous
    # honest choice, which lets E1a/E1c decide instead of the harness.
    residual_sigma = 1.0
    if kind == M.SETPOINT:
        p["target"] = float(p.get("target_hz", float("nan")))
        if i > 0:
            p["dt_ms"] = float(cmd.t_ms - prev_t)
        else:
            need = abs(p["target"] - sp_current) if \
                math.isfinite(p["target"]) else 0.0
            p["dt_ms"] = max(1000.0, 1000.0 * need / M.SP_MAX_RATE)
        # I1' VALUE.  A scenario that models the observation channel states
        # its own residual; otherwise, at the moment each command is issued
        # the machine is running consistently with what it reports -- the
        # replay hides the CONSEQUENCE of a command, and no out-of-band
        # command is ever granted, so nothing is being hidden yet.  A benign
        # 1.0 sigma keeps E1 (the invariant the catalogue names) as the thing
        # under test rather than letting I1' pre-empt it.
        if obs is not None and "residual_sigma" in obs:
            residual_sigma = float(obs["residual_sigma"])
        else:
            residual_sigma = 1.0

    # ---- E5 command counters ---------------------------------------------
    seq, nonce = cmd.sequence, cmd.nonce
    if favourable and not keep_e5:
        seq, nonce = REPORT_SEQ0 + i + 1, ("fav", i)

    mcmd = M.Command(
        source=src, kind=kind, params=p,
        sig_valid=bool(cmd.sig_valid),
        sig2_valid=insider, attested=insider, keyswitch=insider,
        identity=_identity(cmd), nonce=nonce, seq=seq)
    rep = M.Report(t=cmd.t_ms, seq=rseq, sig_valid=True,
                   i_diff=i_diff, i_restraint=i_restraint,
                   remote_ok=True, forward=forward, time_quality_ok=True,
                   process_value=sp_current, residual_sigma=residual_sigma,
                   local_authentic=local_authentic, local_fresh=local_fresh,
                   residual_authentic=residual_authentic,
                   residual_fresh=residual_fresh)
    assumed = {"local": corro is None, "observation": obs is None}
    return mcmd, rep, assumed


P_CHARGING = M.A2_CHARGING      # an external through-fault leaves only charging


def _feasibility(sc, favourable):
    """E3 oracle for one scenario, read off the scenario's own params."""
    def oracle(p):
        if favourable and sc.expected_invariant != "E3":
            return True
        if "N-1 violation on 4th open" in str(p.get("cumulative_topology", "")):
            return not p.get("_is_fourth", False)
        if "dead_time_ms" in p and float(p["dead_time_ms"]) < ANTI_PUMP_MS:
            return False
        return True
    return oracle


def judge(sc, favourable=False):
    """Run one scenario through a fresh Monitor.  Returns a result dict."""
    keep = sc.expected_invariant if favourable else None
    mon = M.Monitor(feasibility=_feasibility(sc, favourable),
                    maint_window=lambda _ms: True)
    mon.st.last_report_seq = REPORT_SEQ0
    sp_current = NOMINAL_HZ
    prev_t = 0
    per_cmd = []
    n_assumed_local = n_assumed_obs = 0
    for i, cmd in enumerate(sc.commands):
        if "cumulative_topology" in cmd.params:
            cmd.params["_is_fourth"] = (i >= 3)
        mcmd, rep, assumed = _world(sc, cmd, i, prev_t, sp_current,
                                    favourable, keep)
        if assumed["local"]:
            n_assumed_local += 1
        if assumed["observation"]:
            n_assumed_obs += 1
        actuate, _src, reason = mon.submit(
            mcmd, rep, baseline_trip=False, cert_ok=False,
            reclose_auth=bool(favourable))
        granted = _is_grant(reason)
        if granted and mcmd.kind == M.SETPOINT:
            sp_current = mcmd.params["target"]
        per_cmd.append({"i": i, "t_ms": cmd.t_ms, "source": cmd.source,
                        "kind": cmd.kind,
                        "effective_kind": M.KIND_NAMES.get(
                            M.effective_kind(mcmd.source, mcmd.kind), "?"),
                        "granted": granted,
                        "reason": reason,
                        "invariant": REASON_INVARIANT.get(reason)})
        prev_t = cmd.t_ms

    # gs/monitor.py tags any grant whose channel provenance was ASSUMED
    # rather than verified.  This harness never constructs a Monitor with
    # `legacy_unauthenticated_channels=True`, so this must be zero -- and
    # checking it is what turns "we tested the shipped default" from a claim
    # into a measurement.
    n_assumed_grants = sum(1 for e in mon.log
                           if getattr(e, "provenance_assumed", False))

    n = len(per_cmd)
    n_granted = sum(1 for c in per_cmd if c["granted"])
    blocked_cmds = [c for c in per_cmd if not c["granted"]]
    blocked = n_granted < n
    first_inv = blocked_cmds[0]["invariant"] if blocked_cmds else None
    invs = []
    for c in blocked_cmds:
        if c["invariant"] not in invs:
            invs.append(c["invariant"])
    return {
        "name": sc.name, "family": sc.family, "domain": sc.domain,
        "expected_blocked": sc.expected_blocked,
        "expected_invariant": sc.expected_invariant,
        "ground_truth_permit": sc.ground_truth_permit,
        "n_commands": n, "n_granted": n_granted,
        "blocked": blocked,
        "first_block_invariant": first_inv,
        "first_block_reason": blocked_cmds[0]["reason"] if blocked_cmds else None,
        "invariants_fired": invs,
        # How much of this verdict rests on a harness assumption rather than
        # on something the scenario asserted.
        "grants_under_assumed_provenance": n_assumed_grants,
        "provenance_assumed_local": n_assumed_local,
        "provenance_assumed_observation": n_assumed_obs,
        "commands": per_cmd,
    }


def score(results):
    """(a) block rate, (b) negative controls, (c) right-reason rate."""
    pos = [r for r in results if r["expected_blocked"]]
    neg = [r for r in results if not r["expected_blocked"]]
    misses = [r for r in pos if not r["blocked"]]
    overblocked = [r for r in neg if r["blocked"]]

    blocked_pos = [r for r in pos if r["blocked"]]
    strict = [r for r in blocked_pos
              if r["first_block_invariant"] == r["expected_invariant"]]
    lenient = [r for r in blocked_pos
               if r["expected_invariant"] in r["invariants_fired"]]
    mismatches = [{"name": r["name"],
                   "expected": r["expected_invariant"],
                   "actual_first": r["first_block_invariant"],
                   "actual_reason": r["first_block_reason"],
                   "all_fired": r["invariants_fired"],
                   "expected_fired_somewhere":
                       r["expected_invariant"] in r["invariants_fired"]}
                  for r in blocked_pos
                  if r["first_block_invariant"] != r["expected_invariant"]]

    by_family = {}
    for fam in attacks.FAMILIES:
        f_pos = [r for r in pos if r["family"] == fam]
        f_blocked = [r for r in f_pos if r["blocked"]]
        f_right = [r for r in f_blocked
                   if r["first_block_invariant"] == r["expected_invariant"]]
        f_neg = [r for r in neg if r["family"] == fam]
        by_family[fam] = {
            "n_positive": len(f_pos), "n_blocked": len(f_blocked),
            "n_right_reason": len(f_right),
            "block_rate": (len(f_blocked) / float(len(f_pos))) if f_pos else None,
            "right_reason_rate": (len(f_right) / float(len(f_blocked)))
                                 if f_blocked else None,
            "n_negative": len(f_neg),
            "n_negative_overblocked": len([r for r in f_neg if r["blocked"]]),
        }

    # Negative controls are not one population.  The `control` family is a
    # POSITIVE control: ground_truth_permit=True, an action that SHOULD be
    # permitted, and blocking one is an availability failure -- the monitor
    # would be unusable.  The `unblockable` family is malicious
    # (ground_truth_permit=False) but beyond what a reference monitor can see,
    # and blocking one is over-blocking of a different kind.  Reporting them
    # as a single number would hide which of the two just broke.
    pos_ctrl = [r for r in neg if r["family"] == "control"]
    unblockable = [r for r in neg if r["family"] != "control"]

    return {
        "n_scenarios": len(results),
        "n_positive": len(pos), "n_blocked": len(blocked_pos),
        "block_rate": (len(blocked_pos) / float(len(pos))) if pos else None,
        "misses": [{"name": r["name"],
                    "expected_invariant": r["expected_invariant"],
                    "n_granted": r["n_granted"], "n_commands": r["n_commands"],
                    "why": "every command granted; "
                           "invariants fired: %s" % (r["invariants_fired"],)}
                   for r in misses],
        "n_negative": len(neg),
        "n_negative_overblocked": len(overblocked),
        "positive_controls": {
            "n": len(pos_ctrl),
            "n_permitted": len([r for r in pos_ctrl if not r["blocked"]]),
            "blocked": [r["name"] for r in pos_ctrl if r["blocked"]]},
        "unblockable_controls": {
            "n": len(unblockable),
            "n_permitted": len([r for r in unblockable if not r["blocked"]]),
            "blocked": [r["name"] for r in unblockable if r["blocked"]]},
        "negative_controls": [
            {"name": r["name"], "blocked": r["blocked"],
             "n_granted": r["n_granted"], "n_commands": r["n_commands"],
             "first_block_reason": r["first_block_reason"],
             "first_block_invariant": r["first_block_invariant"]}
            for r in neg],
        "right_reason_rate": (len(strict) / float(len(blocked_pos)))
                             if blocked_pos else None,
        "right_reason_rate_lenient": (len(lenient) / float(len(blocked_pos)))
                                     if blocked_pos else None,
        "n_right_reason": len(strict),
        "n_right_reason_lenient": len(lenient),
        "mismatches": mismatches,
        "by_family": by_family,
        "harness_provenance_assumptions": {
            "policy": ("absent channel annotation is treated as honest "
                       "(HARNESS_ASSUMES_HONEST_CHANNEL=%r)"
                       % (HARNESS_ASSUMES_HONEST_CHANNEL,)),
            "commands_total": sum(r["n_commands"] for r in results),
            "commands_local_assumed":
                sum(r["provenance_assumed_local"] for r in results),
            "commands_observation_assumed":
                sum(r["provenance_assumed_observation"] for r in results),
            # Must be 0: every verdict above was decided on the SHIPPED
            # fail-closed default, never under the legacy opt-in.
            "grants_under_assumed_provenance":
                sum(r["grants_under_assumed_provenance"] for r in results),
            "scenarios_asserting_local_provenance":
                sorted(r["name"] for r in results
                       if r["provenance_assumed_local"] < r["n_commands"]),
            "scenarios_asserting_observation_provenance":
                sorted(r["name"] for r in results
                       if r["provenance_assumed_observation"]
                       < r["n_commands"]),
        },
    }


# ==========================================================================
# TASK 3 -- the physical-consequence experiment
# ==========================================================================

def run_arm(arm, seed=0, horizon_s=6000.0, dt=P.DT, cmd_period_s=1.0,
            quiet_s=P.QUIET_S):
    """One mitigation arm of the slow-cycle payload.

    arm "A": unmitigated -- the payload's commanded frequency goes straight
             to the drive.
    arm "B": the monitor mediates every SETPOINT, reasoning from the
             COMPROMISED (replayed) process value, with the independent
             observation channel UNWIRED (residual_sigma = 0.0, i.e. "the
             report is assumed consistent with itself").
    arm "C": identical in every respect except that residual_sigma carries
             plant_drive.residual() computed from the independently-keyed
             tachometer-rate, motor current and casing vibration.
    """
    import random
    rng = random.Random(seed)
    rotor = P.Rotor(P.F_NOM)
    period = P.payload_period(quiet_s=quiet_s)
    n_per = int(math.ceil(horizon_s / period)) + 1
    windows = [(k * period + quiet_s - 1.0, (k + 1) * period)
               for k in range(n_per)]
    atk = P.SensorAttack(mode="replay", record_until=quiet_s - 2.0,
                         active_windows=windows, dt=dt)

    b_i, b_v = rng.gauss(0.0, 0.008), rng.gauss(0.0, 0.015)
    mon = None
    if arm in ("B", "C", "D"):
        mon = M.Monitor(feasibility=lambda p: True,
                        maint_window=lambda _ms: False)

    applied = P.F_NOM
    sp_seq = 0
    rate_lag = max(1, int(round(P.RATE_WIN_S / dt)))
    rep_hist = []
    ts, dmg, spd_true, spd_rep, res_series, cmd_series = [], [], [], [], [], []
    lie_flags = []
    decisions = []
    n = int(round(horizon_s / dt))
    every = max(1, int(round(cmd_period_s / dt)))
    attack_start = None          # true speed leaves the qualified band
    lie_start = None             # the reported speed becomes materially wrong
    disowned_t = None           # I7 puts the source in BASELINE_ONLY
    destroyed_t = None

    for k in range(n):
        t = k * dt
        rotor.step(applied, dt=dt, t=t)
        tach = rotor.f + rng.gauss(0.0, P.TACH_SIGMA)
        i_meas = (P.true_current(rotor.f, rotor.dfdt) + b_i
                  + rng.gauss(0.0, P.I_SIGMA))
        v_meas = P.true_vibration(rotor.f) + b_v + rng.gauss(0.0, P.V_SIGMA)
        honest = rotor.f + rng.gauss(0.0, P.TACH_SIGMA)
        rep, faked = atk.report(t, honest)
        rep_hist.append(rep)
        if len(rep_hist) > rate_lag + 1:
            rep_hist.pop(0)
        d_rep = ((rep_hist[-1] - rep_hist[0]) / ((len(rep_hist) - 1) * dt)
                 if len(rep_hist) > 1 else 0.0)
        r = P.residual(rep, d_rep, i_meas, v_meas)

        # "the attack is hiding something" == the true speed is outside the
        # qualified band while the reported speed says it is not.  This is
        # the instant detection latency is measured from.
        hidden = (faked and not (P.F_BAND_LO <= rotor.f <= P.F_BAND_HI))
        if hidden and attack_start is None:
            attack_start = t
        # "materially wrong" = the replayed value is further from the truth
        # than five sigma of tachometer noise, i.e. the lie has begun to bite.
        lying = bool(faked and abs(rep - rotor.f) > 5 * P.TACH_SIGMA)
        lie_flags.append(lying)
        if lying and lie_start is None:
            lie_start = t

        target = P.payload_cycle(t, quiet_s=quiet_s)
        if arm == "A":
            applied = target
        elif k % every == 0:
            sp_seq += 1
            # Provenance is set EXPLICITLY on every arm.  Arm B models the
            # pre-fix deployment: the observation channel exists and is
            # assumed honest, but its VALUE is never consulted (a 0.0 sigma
            # residual is "the report is consistent with itself").  Arm D
            # models the adversary who owns that channel outright and feeds a
            # clean 1.0 sigma residual while the rotor does as it pleases --
            # the process-domain twin of the paced forger.
            report = M.Report(
                t=int(round(t * 1000)), seq=sp_seq,
                sig_valid=True, remote_ok=True, forward=True,
                time_quality_ok=True, process_value=rep,
                residual_sigma=(0.0 if arm == "B"
                                else 1.0 if arm == "D" else r),
                local_authentic=True, local_fresh=True,
                residual_authentic=(arm != "D"), residual_fresh=True)
            cmd = M.Command(M.ENGINEERING, M.SETPOINT,
                            {"target": target,
                             "dt_ms": cmd_period_s * 1000.0},
                            sig_valid=True, identity="eng-ws",
                            nonce=("sp", sp_seq), seq=sp_seq)
            actuate, _s, reason = mon.submit(cmd, report)
            decisions.append((t, target, bool(actuate), reason, r, hidden))
            if actuate:
                applied = target
            if mon.st.mode == M.BASELINE_ONLY and disowned_t is None:
                disowned_t = t

        if rotor.destroyed and destroyed_t is None:
            destroyed_t = t
        ts.append(t); dmg.append(rotor.damage); spd_true.append(rotor.f)
        spd_rep.append(rep); res_series.append(r); cmd_series.append(applied)

    stride = max(1, len(ts) // 1500)
    return {
        "arm": arm,
        "horizon_s": horizon_s,
        "final_damage": rotor.damage,
        "destroyed": rotor.destroyed,
        "destroyed_t": destroyed_t,
        "destroyed_bursts": (destroyed_t / period) if destroyed_t else None,
        "payload_period_s": period,
        "max_true_hz": max(spd_true), "min_true_hz": min(spd_true),
        "overspeed_s": rotor.overspeed_s,
        "resonance_dwell_s": rotor.resonance_dwell_s,
        "attack_start_s": attack_start,
        "lie_start_s": lie_start,
        "disowned_t_s": disowned_t,
        "n_commands": len(decisions),
        "n_granted": sum(1 for d in decisions if d[2]),
        "veto_reasons": _tally([d[3] for d in decisions if not d[2]]),
        "t": ts[::stride], "damage": dmg[::stride],
        "speed_true": spd_true[::stride], "speed_reported": spd_rep[::stride],
        "residual": res_series[::stride],
        "_decisions": decisions,
        "_res_full": res_series, "_t_full": ts, "_lie_full": lie_flags,
    }


# ==========================================================================
# PROVENANCE PROBES -- harness-owned, scored SEPARATELY
# ==========================================================================
#
# gs/attacks.py contains no scenario that forges the differential's LOCAL
# addend or the process OBSERVATION channel, so nothing in the catalogue
# exercises R_LOCAL or R_OBSERVATION and a 100% catalogue block rate says
# nothing whatever about the both-ends fix.  These probes close that gap.
# They live here, and are reported and scored SEPARATELY from the catalogue,
# for two reasons: this agent does not own gs/attacks.py, and folding
# harness-authored attacks into the catalogue block rate would be exactly the
# kind of number-flattering the experiment exists to prevent.
#
# Each probe is a MATCHED PAIR: the attack, and the identical command with
# only the provenance flag flipped.  A guard that refuses both proves
# nothing (a monitor that refuses everything satisfies every invariant); the
# pair shows the flag is the only difference between refused and granted.

def _probe_monitor():
    return M.Monitor(feasibility=lambda p: True)


def provenance_probes():
    """Does each new guard actually bite, and only when it should?"""
    probes = []

    def trip(local_authentic=True, local_fresh=True, i_diff=0.15,
             i_restraint=0.1):
        mon = _probe_monitor()
        rep = M.Report(t=100, seq=1, i_diff=i_diff, i_restraint=i_restraint,
                       remote_ok=True, forward=True, time_quality_ok=True,
                       local_authentic=local_authentic,
                       local_fresh=local_fresh,
                       residual_authentic=True, residual_fresh=True)
        # AI-sourced: PROTECTIVE_SOURCES, so this stays a TRIP and faces I1
        # rather than being reclassified to operational SWITCH.
        cmd = M.Command(M.AI, M.TRIP, {"breaker": "SS1-01", "gen_pu": 0.95,
                                       "load_pu": 1.0},
                        sig_valid=True, identity="ai-plane", nonce="n", seq=1)
        return mon.submit(cmd, rep, cert_ok=True)

    def setpoint(residual_authentic=True, residual_fresh=True, sigma=1.0):
        mon = _probe_monitor()
        rep = M.Report(t=100, seq=1, process_value=1064.0,
                       remote_ok=True, forward=True, time_quality_ok=True,
                       residual_sigma=sigma,
                       local_authentic=True, local_fresh=True,
                       residual_authentic=residual_authentic,
                       residual_fresh=residual_fresh)
        cmd = M.Command(M.SCADA, M.SETPOINT,
                        {"drive": "VFD-A21", "target": 1070.0,
                         "dt_ms": 1000.0},
                        sig_valid=True, identity="op", nonce="n", seq=1)
        return mon.submit(cmd, rep)

    def add(name, kill_chain, res, expect_granted, expect_reason):
        actuate, _src, reason = res
        granted = _is_grant(reason)
        probes.append({
            "name": name, "kill_chain": kill_chain,
            "granted": granted, "reason": reason,
            "invariant": REASON_INVARIANT.get(reason),
            "expect_granted": expect_granted,
            "expect_reason": expect_reason,
            "pass": (granted == expect_granted
                     and (expect_reason is None or reason == expect_reason))})

    add("local_addend_forged",
        "paced forger owns the local merging-unit channel and holds i_diff "
        "steadily above the sensitivity floor and below nominal 87L pickup",
        trip(local_authentic=False), False, M.R_LOCAL)
    add("local_addend_stale",
        "same forger replays a genuine local frame instead of signing one",
        trip(local_fresh=False), False, M.R_LOCAL)
    add("local_addend_authentic_CONTROL",
        "byte-identical trip, local addend authenticated: must be GRANTED, "
        "or the guard is indistinguishable from refusing everything",
        trip(), True, M.R_GRANT)
    add("observation_channel_forged",
        "adversary owns the tach/current/vibration stream and feeds a clean "
        "1.0 sigma residual while the rotor does as it pleases",
        setpoint(residual_authentic=False), False, M.R_OBSERVATION)
    add("observation_channel_stale",
        "same adversary replays genuine observation frames",
        setpoint(residual_fresh=False), False, M.R_OBSERVATION)
    add("observation_channel_authentic_CONTROL",
        "byte-identical setpoint, observation channel authenticated: must be "
        "GRANTED", setpoint(), True, M.R_GRANT)
    # The legacy escape hatch is itself a security-relevant configuration,
    # so it gets probed rather than assumed.  Two things must hold: it grants
    # what the fail-closed default refuses (otherwise it is not an escape
    # hatch), and the grant is TAGGED, so an investigator can tell a grant
    # backed by verification from one backed by an assumption.
    mon_legacy = M.Monitor(feasibility=lambda p: True,
                           legacy_unauthenticated_channels=True)
    legacy_rep = M.Report(t=100, seq=1, i_diff=0.15, i_restraint=0.1,
                          remote_ok=True, forward=True, time_quality_ok=True)
    legacy_cmd = M.Command(M.AI, M.TRIP, {"breaker": "SS1-01"},
                           sig_valid=True, identity="ai-plane", nonce="n",
                           seq=1)
    add("legacy_optin_grants_the_paced_forger_BUT_TAGS_IT",
        "a deployment that has not wired channel provenance opts out; the "
        "paced forger is granted again, and the grant must be marked so it "
        "is distinguishable after the fact",
        mon_legacy.submit(legacy_cmd, legacy_rep, cert_ok=True),
        True, M.R_GRANT_UNVERIFIED)
    add("absent_provenance_fails_closed_by_default",
        "the same stream against a default Monitor: silence about the "
        "channel is not an authentication",
        _probe_monitor().submit(legacy_cmd, M.Report(
            t=100, seq=1, i_diff=0.15, i_restraint=0.1, remote_ok=True,
            forward=True, time_quality_ok=True), cert_ok=True),
        False, M.R_LOCAL)

    add("observation_authentic_but_residual_high",
        "authentic observation channel reporting a real inconsistency: I1' "
        "must still veto, on VALUE not provenance",
        setpoint(sigma=28.0), False, M.R_PROCESS_RESIDUAL)

    return {"probes": probes,
            "n": len(probes),
            "n_pass": sum(1 for x in probes if x["pass"]),
            "all_pass": all(x["pass"] for x in probes)}


def provenance_coverage(seed=0):
    """Does the CATALOGUE exercise the new guards at all?

    Re-judges every scenario with all four provenance fields forced to True
    -- the fail-OPEN behaviour the monitor used to have by default and now
    only offers via `Monitor(legacy_unauthenticated_channels=True)` -- and
    diffs the outcomes against the real annotations.  If nothing changes, the
    catalogue never touches R_LOCAL or R_OBSERVATION and a 100% block rate
    says nothing about the both-ends fix.  That is a fact about the
    catalogue's coverage, and it belongs in the results file rather than in a
    sentence somebody has to take on trust.
    """
    def outcomes():
        return {r["name"]: (r["first_block_invariant"], r["first_block_reason"],
                            r["n_granted"])
                for r in (judge(sc) for sc in attacks.catalogue(seed=seed))}

    base = outcomes()
    real = M.Report

    class _Defaulted(real):
        def __init__(self, *a, **kw):
            for k in ("local_authentic", "local_fresh",
                      "residual_authentic", "residual_fresh"):
                kw[k] = True
            real.__init__(self, *a, **kw)

    M.Report = _Defaulted
    try:
        alt = outcomes()
    finally:
        M.Report = real
    changed = sorted(k for k in base if base[k] != alt[k])
    return {"scenarios_changed_by_real_provenance": changed,
            "catalogue_exercises_new_guards": bool(changed),
            "note": "empty list == gs/attacks.py contains no scenario that "
                    "forges the differential's local addend or the process "
                    "observation channel, and coverage would come only from "
                    "provenance_probes(); a non-empty list names the "
                    "scenarios whose verdict genuinely turns on channel "
                    "provenance"}


def e2_reachability_probe():
    """Can E2 fire AT ALL for breaker traffic?

    The catalogue attributes six scenarios to E2, but `decide` checks I3
    (latched) before `rate_ok`, and `commit` clears the latch BEFORE it sets
    it, so a granted TRIP re-latches in the same step: without an external
    reclose authorisation arriving in a LATER step, a monitor instance grants
    at most one TRIP ever and the MAX_GRANTS=2 budget is unreachable.  This
    probe separates "E2 is broken" from "E2 is unreachable behind I3", by
    re-running the source-hopping attack with the latch cleared between
    commands exactly as gs/monitor.py's own demo 7 does."""
    out = {}
    for label, clear in (("as_written", False), ("latch_cleared", True)):
        mon = M.Monitor(feasibility=lambda p: True)
        reasons, granted = [], 0
        for i, src in enumerate([M.AI, M.SCADA, M.HMI, M.AI, M.SCADA, M.HMI]):
            # Explicitly authenticated: this probe is about the E2 budget,
            # and since the provenance defaults went fail-closed an absent
            # annotation would veto at I1 before the budget is ever consulted.
            rep = M.Report(t=100 + i * 50, seq=i + 1, i_diff=2.5,
                           i_restraint=1.0, local_authentic=True,
                           local_fresh=True, residual_authentic=True,
                           residual_fresh=True)
            cmd = M.Command(src, M.TRIP, {}, sig_valid=True, identity="x",
                            nonce=i, seq=i + 1)
            ok, _s, why = mon.submit(cmd, rep)
            granted += 1 if ok else 0
            reasons.append(why)
            if clear:
                mon.st.latched = False
        out[label] = {"granted": granted, "reasons": reasons,
                      "e2_fired": M.R_RATE in reasons}
    return out


def _tally(xs):
    d = {}
    for x in xs:
        d[x] = d.get(x, 0) + 1
    return d


def residual_diagnostic(arm_res, seed=0, persist=3, thr=None):
    """DETECTION LATENCY of the residual channel: how long after the payload
    starts hiding an excursion does the residual first cross the monitor's
    own gate (RESIDUAL_MAX_SIGMA) and stay across it for `persist` steps.

    Measured on every arm.  Arm A is the informative one: it is the only arm
    in which an excursion actually happens, because in arms B and C the
    envelope refuses the command before the rotor can leave the band, so
    there is nothing for the residual to detect.  That is a result about the
    payload, not a defect in the measurement."""
    if thr is None:
        thr = M.RESIDUAL_MAX_SIGMA
    t_full, res = arm_res["_t_full"], arm_res["_res_full"]
    run = 0
    t_det = None
    for i, r in enumerate(res):
        run = run + 1 if r > thr else 0
        if run >= persist:
            t_det = t_full[i]
            break
    benign = max(P.episode_stats(P.sc_normal(), seed=seed)["res_max"],
                 P.episode_stats(P.sc_operator_setpoint(), seed=seed)["res_max"])
    lie = arm_res["lie_start_s"]
    hid = arm_res["attack_start_s"]
    return {"threshold_sigma": thr, "worst_benign_sigma": benign,
            "persist_steps": persist, "t_detect_s": t_det,
            "lie_start_s": lie, "attack_start_s": hid,
            # PRIMARY: from the report first becoming materially wrong to the
            # residual crossing the gate.  That is detection latency.
            "latency_s": (t_det - lie) if (t_det is not None
                                           and lie is not None) else None,
            # SECONDARY, and it may be NEGATIVE-as-good: the inertia term in
            # motor current makes a ramp visible while the speed itself is
            # still legal, so the residual can cross the gate BEFORE the rotor
            # leaves the qualified band.
            "margin_before_excursion_s": ((hid - t_det)
                                          if (t_det is not None
                                              and hid is not None) else None)}


def per_burst_latency(arm_res, thr=None, persist=3):
    """Detection latency for EVERY burst, not just the first.

    The plant's author flags the weak point precisely: the residual has a real
    low tail wherever the payload ramp passes through 1064 Hz, because at that
    instant the replayed value and the truth genuinely agree and there is no
    inconsistency to see.  So the interesting numbers are the WORST per-burst
    latency and the fraction of lying steps on which the detector is silent.
    """
    if thr is None:
        thr = M.RESIDUAL_MAX_SIGMA
    t, res, lie = arm_res["_t_full"], arm_res["_res_full"], arm_res["_lie_full"]
    bursts, cur = [], None
    for i, l in enumerate(lie):
        if l and cur is None:
            cur = i
        elif not l and cur is not None:
            bursts.append((cur, i))
            cur = None
    if cur is not None:
        bursts.append((cur, len(lie)))
    lats = []
    for a, b in bursts:
        run, det = 0, None
        for i in range(a, b):
            run = run + 1 if res[i] > thr else 0
            if run >= persist:
                det = t[i]
                break
        lats.append(None if det is None else det - t[a])
    n_lie = sum(1 for x in lie if x)
    n_above = sum(1 for i, x in enumerate(lie) if x and res[i] > thr)
    got = [x for x in lats if x is not None]
    return {"n_bursts": len(bursts), "latencies_s": lats,
            "worst_latency_s": max(got) if got else None,
            "median_latency_s": sorted(got)[len(got) // 2] if got else None,
            "n_bursts_undetected": len([x for x in lats if x is None]),
            "lying_steps": n_lie,
            "frac_lying_steps_above_gate": (n_above / float(n_lie))
                                           if n_lie else None}


def monitor_detection_latency(arm_b, arm_c):
    """Latency of the mechanism the monitor ACTUALLY has in arm C: the first
    moment the independently-keyed Report makes it refuse a setpoint that the
    compromised-channel arm granted."""
    start = arm_c["attack_start_s"] or arm_b["attack_start_s"]
    b = {round(d[0], 3): d[2] for d in arm_b["_decisions"]}
    for t, _tg, granted, reason, _r, _h in arm_c["_decisions"]:
        bg = b.get(round(t, 3))
        if (not granted) and bg is True:
            return {"t_first_divergence_s": t, "reason": reason,
                    "attack_start_s": start,
                    "latency_s": (t - start) if start is not None else None}
    return {"t_first_divergence_s": None, "reason": None,
            "attack_start_s": start, "latency_s": None}


def residual_separation(seed=0):
    """The numbers behind the separation figure."""
    st_n = P.episode_stats(P.sc_normal(), seed=seed)
    st_op = P.episode_stats(P.sc_operator_setpoint(), seed=seed)
    st_p = P.episode_stats(P.sc_payload(horizon_s=3 * P.payload_period()),
                           seed=seed)
    st_r = P.episode_stats(P.sc_replay_only(), seed=seed)
    benign_max = max(st_n["res_max"], st_op["res_max"])
    return {
        "normal_p50": st_n["res_p50"], "normal_p99": st_n["res_p99"],
        "normal_max": st_n["res_max"],
        "operator_max": st_op["res_max"],
        "benign_max": benign_max,
        "hidden_p05": st_p["res_hidden_p05"],
        "hidden_p50": st_p["res_hidden_p50"],
        "hidden_steps": st_p["hidden_steps"],
        "separation_x": st_p["res_hidden_p50"] / max(benign_max, 1e-9),
        "hidden_frac_above_benign_max": st_p["hidden_frac_above"](benign_max),
        "replay_only_faked_max": st_r["res_faked_max"],
        "replay_only_damage": st_r["damage"],
    }


# ==========================================================================
# main
# ==========================================================================

def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--horizon", type=float, default=6000.0,
                    help="drive-arm horizon, seconds")
    ap.add_argument("--no-figures", action="store_true")
    args = ap.parse_args(argv)

    if not os.path.isdir(OUT_DIR):
        os.makedirs(OUT_DIR)

    cat = attacks.catalogue(seed=args.seed)
    as_written = [judge(sc, favourable=False) for sc in cat]
    favourable = [judge(sc, favourable=True)
                  for sc in attacks.catalogue(seed=args.seed)]

    results = {
        "seed": args.seed,
        "monitor_constants": {
            "MAX_GRANTS": M.MAX_GRANTS, "WINDOW_MS": M.WINDOW_MS,
            "VETO_LIMIT": M.VETO_LIMIT,
            "SP_ABS_MIN": M.SP_ABS_MIN, "SP_ABS_MAX": M.SP_ABS_MAX,
            "SP_MAX_RATE": M.SP_MAX_RATE,
            "RESONANCES": [list(r) for r in M.RESONANCES],
            "RESIDUAL_MAX_SIGMA": M.RESIDUAL_MAX_SIGMA,
        },
        "plant_constants": {
            "F_NOM": P.F_NOM, "F_BURST": P.F_BURST, "DAMAGE_FAIL": P.DAMAGE_FAIL,
            "RESONANCES": [list(r) for r in P.RESONANCES],
            "attacks_DRIVE_RESONANCE_HZ": list(attacks.DRIVE_RESONANCE_HZ),
        },
        "catalogue": {"as_written": as_written, "favourable": favourable},
        "score": {"as_written": score(as_written),
                  "favourable": score(favourable)},
    }

    arms = {}
    for arm in ("A", "B", "C", "D"):
        arms[arm] = run_arm(arm, seed=args.seed, horizon_s=args.horizon)
    results["drive"] = {
        "arms": {a: {k: v for k, v in arms[a].items()
                     if not k.startswith("_")} for a in arms},
        "monitor_latency_arm_c": monitor_detection_latency(arms["B"], arms["C"]),
        "residual_diagnostic": {
            a: residual_diagnostic(arms[a], seed=args.seed) for a in arms},
        "unmitigated_reference": {
            "plant_author_time_to_destruction_s": 1129.8,
            "plant_author_bursts": 3.69,
        },
        "separation": residual_separation(seed=args.seed),
        "e2_reachability": e2_reachability_probe(),
        "provenance_probes": provenance_probes(),
        "provenance_coverage": provenance_coverage(seed=args.seed),
        "per_burst_latency": {a: per_burst_latency(arms[a]) for a in arms},
    }

    path = os.path.join(OUT_DIR, "results_v2.json")
    with open(path, "w") as fh:
        json.dump(results, fh, indent=1, sort_keys=True)

    from gs import report_v2
    report_v2.terminal(results)
    if not args.no_figures:
        made = report_v2.figures(results, OUT_DIR)
        print("\nfigures: " + ", ".join(made))
    print("results:  %s" % path)
    return 0


if __name__ == "__main__":
    sys.exit(main())
