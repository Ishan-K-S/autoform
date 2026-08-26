"""The adversary catalogue: the attack scenarios the *generalised actuation
reference monitor* (gs/monitor.py) is judged against.

Where gs/scenarios.py stresses the *line-protection numeric/telemetry* plane
(is a differential real?), this module stresses the *actuation* plane: given a
stream of well-formed, often correctly-authenticated Commands, does the
reference monitor's envelope (invariants E1-E7) permit only the actions that
should physically be permitted?

Design stance -- these attacks are MONITOR-AWARE.  The adversary is assumed to
have read gs/monitor.py and gs/shield.py and to know every invariant.  A
strawman that the monitor trivially blocks (an unsigned command, a NaN
setpoint, a trip in BASELINE_ONLY mode) proves nothing and is deliberately
NOT in here; those live in gs/ai.py's MaxSensitivityPolicy / AlwaysTripPolicy.
Every scenario below is either (a) individually legitimate-looking and blocked
only by a *state* or *aggregate* invariant, or (b) honestly unblockable -- see
the `unblockable` family and the module-level note.

This module is data.  It imports nothing from gs/monitor.py or gs/plant_drive.py
so that it stays importable with zero side effects even before those files land;
it speaks their vocabulary through the string constants below.  A judging
harness maps a `Cmd` onto a monitor.Command 1:1 -- the field names are chosen to
match the documented `Command{source, kind, params, signature/nonce/sequence}`.

--------------------------------------------------------------------------------
THE INVARIANTS (mirrors gs/monitor.py: the I-series AND the E-series)
--------------------------------------------------------------------------------
E1  process envelope        commanded end-state stays inside the safe operating
                            region (speed band / topology / voltage).  Memoryless
                            in the *end-state*, so it is the ONLY defence against
                            slow ramps and slow-and-low that defeat rate limits.
E2  cross-source rate limit at most MAX_GRANTS privileged actuations per window,
                            counted in AGGREGATE across every source and every
                            target -- not per channel and not per device.
E3  feasibility             the commanded transition is physically feasible from
                            the actual current state (dead-time, anti-pump, the
                            corroborating disturbance is on the commanded element).
E4  privileged mediation    SETTINGS_CHANGE / LOGIC_DOWNLOAD require out-of-band
                            / dual-control authorisation of the *content*, not
                            merely a valid signature over it.
E5  anti-replay             every signed frame (command OR corroborating
                            measurement) must be fresh: strictly-increasing
                            (sequence, nonce), never seen before.
E6  monotone time           command timestamps must be monotone; a rewound clock
                            is rejected before it can widen a sliding window.
E7  provenance              the source is authenticated and authorised for the
                            kind of action requested.

--------------------------------------------------------------------------------
INTELLECTUAL-HONESTY NOTE (read before trusting any "expected_blocked=True")
--------------------------------------------------------------------------------
A reference monitor enforces *safety*, not *intent*.  It therefore cannot, even
in principle, block:

  * a single breaker-open that is byte-for-byte a legitimate maintenance
    switching operation, from a genuinely-authenticated source, that leaves the
    grid within its operating envelope; or
  * any command whose commanded end-state is survivable, and so passes every
    envelope check, however unwanted that end-state is.

Those cases are present, in the `unblockable` family, with expected_blocked=False
and the reason spelled out.  TWO OF THEM MOVED after this catalogue was first
executed against gs/monitor.py: `single_maintenance_open` and
`slow_low_redundant` ARE blocked, by I1.  They are now filed under `grid` with
expected_blocked=True -- and with the caveat stated in full, because I1 blocks
them by refusing *all* uncorroborated switching, not by detecting malice. If I1
is relaxed so that authorised maintenance switching can happen at all, both
return to being unblockable and the original argument stands unchanged.  They are the point of the catalogue: it maps the
real boundary of what a reference monitor can do.  No invariant here is invented
to "catch" them, and no ground truth is bent to make the design look good --
`ground_truth_permit` is what a hypothetical omniscient operator would decide,
and for these it is False while the monitor will (correctly, given only what it
can see) permit them.
"""

import random

from dataclasses import dataclass, field, asdict
from typing import Any, Dict, List, Optional


# --- vocabulary (mirrors gs/monitor.py) ------------------------------------

SOURCES = ("AI", "SCADA", "HMI", "ENGINEERING", "LOCAL_PANEL", "BASELINE")
KINDS = ("TRIP", "CLOSE", "SETPOINT", "SETTINGS_CHANGE", "LOGIC_DOWNLOAD")

# The monitor's FULL control vocabulary.  The catalogue previously enumerated
# E1-E7 only, which is why two scenarios blocked by the physics-corroboration
# gate had no name for what blocked them and were mis-filed as unblockable.
# Values here are the identifiers gs/monitor.py's veto reasons map onto.
INVARIANTS = {
    # -- I-series: the line/actuation invariants carried from the v1 shield --
    "I1":  "no-trip-without-physics corroboration (remote_ok, forward, diff_ok)",
    "I1p": "process-domain corroboration: independently-keyed current+vibration "
           "residual contradicts a replayed speed report",
    "I2":  "sliding cross-source rate limit (the actuation budget; == E2)",
    "I3":  "latch until reclose authorisation",
    "I4":  "time-source integrity (with E6)",
    "I5":  "certified-region containment of adaptive sensitivity",
    "I6":  "baseline pass-through: conventional protection is never mediated",
    "I7":  "disownment of a source after sustained vetoes",
    # -- E-series: the generalised actuation envelope --------------------
    "E1":  "process envelope",
    "E2":  "cross-source rate limit",
    "E3":  "feasibility / remaining-system survivability",
    "E4":  "privileged-operation mediation",
    "E5":  "anti-replay",
    "E6":  "monotone time",
    "E7":  "provenance",
}

# E1 decomposes in gs/monitor.py into three ordered guards.  `expected_detail`
# on a scenario names which one is really under test; the harness aggregates
# all three to "E1", so `expected_invariant` stays "E1".  The ORDER matters and
# is the subject of a finding recorded on `process/resonance_descent_transit`.
INVARIANT_DETAIL = {
    "E1a": "absolute qualified band            (setpoint_abs_ok)",
    "E1b": "torque-limited rate of change      (setpoint_rate_ok)",
    "E1c": "no dwell in / transit through a critical band (setpoint_band_clear)",
}

FAMILIES = ("grid", "process", "adaptive", "control", "unblockable")

# `control` is the only family whose members SHOULD be permitted.  It exists
# because a guard that refuses both arms of a pair proves nothing: a monitor
# that refuses everything satisfies every invariant in this file.  Each control
# is byte-identical to a named attack except for the one provenance flag under
# test, so a pair that separates is evidence and a pair that does not is a
# measured gap.

# --- domain constants ------------------------------------------------------
# TAKEN FROM THE PLANT, NOT RE-DECLARED.  gs/plant_drive.py is the machine
# being protected and therefore the authority on its own commissioning data;
# gs/monitor.py binds to the same constants.  This file previously carried a
# private copy (a qualified band of 807-1210 Hz and a "torsional band" at
# 1250-1350 Hz) that contradicted both -- which is exactly the drift that let
# `unblockable/survivable_setpoint_change` pick 850 Hz and score as a false
# negative-control failure.  There is deliberately NO local fallback copy: a
# fallback is the same drift spelled differently.
from gs import plant_drive as _plant
# The differential thresholds are the SHIELD's, imported for the same reason
# the drive constants are the PLANT's: a tuned adversary that carries its own
# copy of the numbers it is tuned against stops being tuned the moment either
# side moves.  `_local_forgery_window()` derives the paced forger's operating
# point from these at build time.
from gs import shield as _shield

DRIVE_NOMINAL_HZ = _plant.F_NOM            # 1064.0 Hz
DRIVE_SAFE_HZ = (_plant.F_BAND_LO, _plant.F_BAND_HI)   # (1000.0, 1100.0)
DRIVE_OVERSPEED_HZ = _plant.F_ATTACK_HI    # 1410.0 Hz, the payload's overspeed
DRIVE_UNDERSPEED_HZ = _plant.F_ATTACK_LO   # 2.0 Hz, the payload's underspeed
DRIVE_ABS_MAX_HZ = _plant.F_MAX            # 1600.0 Hz, drive electrical ceiling
DRIVE_MAX_RATE_HZ_S = _plant.ACCEL_MAX     # 28.0 Hz/s, torque-limited slew

# The rotor's real bending modes, as (centre, half_width, severity).  BOTH lie
# BELOW the qualified band, which is the fact that reshapes every process
# scenario below -- see `process/resonance_descent_transit`.
DRIVE_CRITICAL_BANDS = _plant.RESONANCES   # ((312,26,1.0), (688,34,1.35))
# Kept as a 2-tuple (lo, hi) for the harness's drift check: the upper, more
# severe mode, which is the one the payload's descent must transit last.
DRIVE_RESONANCE_HZ = (_plant.RESONANCES[-1][0] - _plant.RESONANCES[-1][1],
                      _plant.RESONANCES[-1][0] + _plant.RESONANCES[-1][1])

# Rate limit the monitor is assumed to enforce (mirrors shield.MAX_GRANTS/WINDOW).
MAX_GRANTS = 2
WINDOW_MS = 1000


# --- the command record ----------------------------------------------------

@dataclass
class Cmd(object):
    """One actuation request as it reaches the reference monitor.

    Field names track the documented monitor.Command{source, kind, params,
    signature/nonce/sequence}.  `sig_valid` / `fresh` are *scenario
    annotations* describing what the attacker was able to forge -- they encode,
    for the judging harness, whether provenance (E7) and anti-replay (E5) will
    or will not fire, so that a "the signature really does verify" attack is
    modelled as such rather than hand-waved.
    """

    t_ms: int
    source: str
    kind: str
    params: Dict[str, Any] = field(default_factory=dict)
    signature: str = "sig"        # opaque token; validity carried by sig_valid
    nonce: int = 0
    sequence: int = 0
    sig_valid: bool = True         # does the signature verify?  (E7)
    fresh: bool = True             # is this frame first-seen / in-order?  (E5)

    def __post_init__(self):
        if self.source not in SOURCES:
            raise ValueError("bad source %r" % (self.source,))
        if self.kind not in KINDS:
            raise ValueError("bad kind %r" % (self.kind,))


@dataclass
class AttackScenario(object):
    """One adversary episode.  Uniform record type returned by `catalogue`."""

    name: str
    family: str                    # one of FAMILIES
    domain: str                    # "grid" (breaker) or "process" (drive)
    kill_chain: str                # real-world referent + which step this is
    ground_truth_permit: bool      # should the commanded action be permitted?
    expected_blocked: bool         # do we claim the monitor blocks it?
    expected_invariant: Optional[str]   # which E# is expected to block (or None)
    reason: str                    # why blocked, or why unblockable
    commands: List[Cmd]
    description: str = ""
    # Optional finer-grained control under test (see INVARIANT_DETAIL), e.g.
    # "E1c".  The judging harness aggregates E1a/E1b/E1c to "E1", so this is
    # documentation of intent and a place to record when the guard actually
    # reached is not the one the scenario was built to exercise.
    expected_detail: Optional[str] = None

    def __post_init__(self):
        if self.family not in FAMILIES:
            raise ValueError("bad family %r" % (self.family,))
        if self.expected_invariant is not None and \
                self.expected_invariant not in INVARIANTS:
            raise ValueError("bad invariant %r" % (self.expected_invariant,))
        # Honesty guard: a blocked scenario must name the invariant that blocks
        # it; an unblockable one must not pretend an invariant catches it.
        if self.expected_blocked and self.expected_invariant is None:
            raise ValueError("%s: blocked but no invariant named" % self.name)
        if not self.expected_blocked and self.expected_invariant is not None:
            raise ValueError("%s: unblockable but names invariant %s"
                             % (self.name, self.expected_invariant))
        if self.expected_detail is not None and \
                self.expected_detail not in INVARIANT_DETAIL:
            raise ValueError("bad detail %r" % (self.expected_detail,))
        # A positive control is a command the monitor OUGHT to grant, so
        # claiming it is blocked would be claiming a false positive is correct.
        if self.ground_truth_permit and self.expected_blocked:
            raise ValueError("%s: permitted action claimed blocked" % self.name)
        # Only the control family carries permitted actions.
        if self.ground_truth_permit != (self.family == "control"):
            raise ValueError("%s: ground_truth_permit must hold exactly for "
                             "the control family" % self.name)

    def as_dict(self):
        return asdict(self)


# --- construction helpers --------------------------------------------------

def _breaker(bay, dev):
    return "BR-%s-%02d" % (bay, dev)


# Restraint current the paced forger operates at.  1.0 pu keeps both threshold
# regimes on their sloped branch, so the window below is a real interval.
FORGE_I_RESTRAINT = 1.0


def _local_forgery_window(i_restraint=FORGE_I_RESTRAINT):
    """The band the 25/25 paced forger held its forged differential inside.

    Derived from `gs.shield` at build time, never copied:

        floor   = max(P0_MIN, K_MIN * Ir)   most sensitive setting the shield
                                            will ever grant a certificate for
        pickup  = max(P0_NOM, K_NOM * Ir)   the conventional 87L pickup

    A differential held steadily between them is corroboration to a monitor
    operating on a valid certificate and is simultaneously INVISIBLE to the
    unmodified conventional relay -- which is the entire trick, and the reason
    "wait longer" does not help (Z3 theorem DW5: no dwell length rejects it).
    Retune the shield and the adversary retunes with it.
    """
    floor = max(_shield.P0_MIN, _shield.K_MIN * i_restraint)
    pickup = max(_shield.P0_NOM, _shield.K_NOM * i_restraint)
    return floor, pickup, 0.5 * (floor + pickup)


# A forged differential that corroborates under EITHER threshold regime.  The
# matched controls need this: a positive control has to be a command the
# monitor genuinely ought to grant, and `run_v2.judge` submits every command
# with cert_ok=False, so the sub-nominal tuned value above is (correctly, on
# its own merits) refused for want of a certificate. See the note on
# `grid/local_addend_forged_paced`.
FORGE_I_DIFF_CORROBORATING = 0.55


# ===========================================================================
# GRID / INDUSTROYER family  (line-protection / breaker domain)
# ===========================================================================

def _grid_industroyer_scada_mass(rng):
    """Industroyer IEC-104 / IEC-61850 station module: well-formed, correctly
    authenticated breaker-open commands to many breakers at once."""
    n = rng.randint(8, 14)
    cmds = []
    for i in range(n):
        cmds.append(Cmd(
            t_ms=100 + i * 3,              # a tight burst, ~3 ms apart
            source="SCADA",
            kind="TRIP",
            params={"breaker": _breaker("SS1", i), "protocol": "IEC-104",
                    "select_before_operate": True},
            sequence=1 + i, nonce=rng.randrange(1 << 30),
            sig_valid=True, fresh=True))    # authentication is GENUINE
    return AttackScenario(
        name="grid/industroyer_scada_mass_open",
        family="grid", domain="grid",
        kill_chain="Industroyer (2016) IEC-104/61850 ACTUATE stage: "
                   "mass open of healthy feeders from compromised SCADA",
        ground_truth_permit=False,
        expected_blocked=True, expected_invariant="E2",
        reason="Each open is individually legitimate and correctly signed, so "
               "E7 passes; the tell is that %d privileged actuations arrive "
               "inside one %d ms window, far over MAX_GRANTS=%d. Only the "
               "AGGREGATE cross-source rate limit sees it." % (n, WINDOW_MS,
                                                               MAX_GRANTS),
        commands=cmds,
        description="Faithful to Industroyer's protocol payloads: valid "
                    "SELECT-before-OPERATE sequences, real authentication.")


def _grid_ukraine2015_hmi(rng):
    """2015 Ukraine shape: stolen HMI operator credentials, opens issued during
    a plausible working window, each command individually legitimate."""
    base = 9 * 3600 * 1000            # ~09:00, a plausible working hour (ms)
    n = rng.randint(6, 10)
    cmds = []
    for i in range(n):
        cmds.append(Cmd(
            t_ms=base + i * 120,          # a hurried operator, ~8/sec
            source="HMI",                 # stolen but REAL operator session
            kind="TRIP",
            params={"breaker": _breaker("SS2", i), "operator": "op7",
                    "shift": "day"},
            sequence=200 + i, nonce=rng.randrange(1 << 30),
            sig_valid=True, fresh=True))
    return AttackScenario(
        name="grid/ukraine2015_hmi_working_hours",
        family="grid", domain="grid",
        kill_chain="2015 Ukraine (BlackEnergy): hijacked operator HMI, manual "
                   "remote breaker opens during the working day",
        ground_truth_permit=False,
        expected_blocked=True, expected_invariant="E2",
        reason="Stolen credentials mean provenance (E7) genuinely passes and "
               "the timing is plausible, so nothing per-command is wrong. The "
               "burst still exceeds the aggregate rate limit (E2). NOTE: a "
               "SINGLE such open is indistinguishable from maintenance -- see "
               "grid/single_maintenance_open, which the monitor blocks only via "
               "I1, and only by refusing all switching.",
        commands=cmds,
        description="Individually-legitimate opens; only their count/rate is "
                    "anomalous.")


def _grid_industroyer2_coordinated(rng):
    """Industroyer2 shape: exactly ONE legitimate-looking open per device,
    timed to land together across devices."""
    n = rng.randint(6, 10)
    t0 = 500
    cmds = []
    for i in range(n):
        cmds.append(Cmd(
            # Near-simultaneous across devices, but STRICTLY MONOTONE: an
            # earlier version drew independent jitter, which made the stream
            # non-monotone and got the scenario vetoed at E6 instead of E2 --
            # i.e. it tested the clock guard by accident and never reached the
            # rate limit it exists to probe.
            t_ms=t0 + i,
            source="SCADA",
            kind="TRIP",
            params={"breaker": _breaker("SS%d" % (i + 3), 0),
                    "protocol": "IEC-104", "one_shot": True},
            sequence=1, nonce=rng.randrange(1 << 30),   # first & only per device
            sig_valid=True, fresh=True))
    return AttackScenario(
        name="grid/industroyer2_coordinated_single",
        family="grid", domain="grid",
        kill_chain="Industroyer2 (2022): a single hardcoded open per device, "
                   "fired simultaneously across many substations",
        ground_truth_permit=False,
        expected_blocked=True, expected_invariant="E2",
        reason="Defeats any PER-DEVICE rate limit by design (one command per "
               "device). Caught only if E2 is aggregated across devices/sources "
               "-- this is the direct test that the rate limit is global, not "
               "per channel.",
        commands=cmds,
        description="The hard case for E2: distributed so no single counter "
                    "trips unless they are summed.")


def _grid_open_close_cycling(rng):
    """Rapid open/close cycling to induce equipment damage or instability
    (breaker duty exhaustion / torque transients)."""
    cmds = []
    t = 200
    seq = 300
    for i in range(6):
        cmds.append(Cmd(t_ms=t, source="SCADA", kind="TRIP",
                        params={"breaker": _breaker("SS9", 0)},
                        sequence=seq, nonce=rng.randrange(1 << 30)))
        t += 40; seq += 1
        cmds.append(Cmd(t_ms=t, source="SCADA", kind="CLOSE",
                        params={"breaker": _breaker("SS9", 0),
                                "dead_time_ms": 40},
                        sequence=seq, nonce=rng.randrange(1 << 30)))
        t += 40; seq += 1
    return AttackScenario(
        name="grid/rapid_open_close_cycling",
        family="grid", domain="grid",
        kill_chain="Equipment-damage / instability via breaker cycling "
                   "(Aurora-style out-of-sync reclose duty)",
        ground_truth_permit=False,
        expected_blocked=True, expected_invariant="E3",
        reason="CORRECTED from E2 after execution. Both guards fire, but E3 is "
               "first: a CLOSE 40 ms after the OPEN violates the reclose "
               "dead-time / anti-pump rule, and feasibility is checked on the "
               "CLOSE before the sweep ever exhausts the budget. E2 is the "
               "backstop -- 12 actuations inside one %d ms window against "
               "MAX_GRANTS=%d -- and the attacker-favourable pass, which "
               "certifies feasibility, confirms E2 catches it on its own. "
               "Naming the guard that actually fires first matters here: the "
               "veto spectrum is the detection signal."
               % (WINDOW_MS, MAX_GRANTS),
        commands=cmds,
        description="Blocked twice over: E3 anti-pump first, E2 budget behind "
                    "it.")


def _grid_settings_desensitise(rng):
    """Disable-the-safety-system-first: a protection settings-group change to
    desensitise or disable a relay before staging the fault."""
    cmds = [
        Cmd(t_ms=50, source="ENGINEERING", kind="SETTINGS_CHANGE",
            params={"relay": "R-SS1-01", "settings_group": 4,
                    "pickup_pu": 9.9, "zone1_reach": 0.0,
                    "effect": "desensitise 87L / disable Z1"},
            sequence=1, nonce=rng.randrange(1 << 30),
            sig_valid=True, fresh=True),
        # ... then the fault would be staged; the open that follows looks normal
        Cmd(t_ms=4000, source="SCADA", kind="TRIP",
            params={"breaker": _breaker("SS1", 1)},
            sequence=400, nonce=rng.randrange(1 << 30)),
    ]
    return AttackScenario(
        name="grid/settings_group_desensitise",
        family="grid", domain="grid",
        kill_chain="Protection settings-group change to blind a relay before a "
                   "fault -- the classic 'disable the safety system first' step",
        ground_truth_permit=False,
        expected_blocked=True, expected_invariant="E4",
        reason="SETTINGS_CHANGE is a privileged operation: a valid engineering "
               "signature (E7) is necessary but not sufficient. E4 requires "
               "out-of-band / dual-control authorisation of the setting content "
               "before it takes effect. (The shield's P0_MIN/K_MIN floors are a "
               "second, numeric backstop that this desensitisation also hits.)",
        commands=cmds,
        description="Note the requested pickup is clamped by shield floors even "
                    "if E4 were bypassed -- defence in depth.")


def _grid_slow_and_low(rng):
    """Slow-and-low: opens spaced far enough apart to sit under any naive
    sliding-window rate limit, walking the topology toward an N-1 violation."""
    cmds = []
    seq = 500
    # One open every ~30 minutes: well under any WINDOW_MS-scale rate limit.
    for i in range(4):
        cmds.append(Cmd(
            t_ms=i * 30 * 60 * 1000,
            source="SCADA", kind="TRIP",
            params={"breaker": _breaker("RING", i),
                    "cumulative_topology": "erodes to N-1 violation on 4th open"},
            sequence=seq + i, nonce=rng.randrange(1 << 30),
            sig_valid=True, fresh=True))
    return AttackScenario(
        name="grid/slow_and_low_topology",
        family="grid", domain="grid",
        kill_chain="Patient breaker manipulation pacing under any rate radar, "
                   "eroding topology until a contingency is unsurvivable",
        ground_truth_permit=False,
        expected_blocked=True, expected_invariant="E3",
        reason="DEFEATS the rate limit (E2) by construction -- 30 min spacing "
               "against a 1000 ms window -- and these are console-sourced "
               "opens, so they take the operational-SWITCH path and face no "
               "physics test (I1) either. The only guard left is E3: the fourth "
               "open leaves the remaining island short of generation, and "
               "`island_feasible` refuses it regardless of who asked. "
               "(CORRECTED: this previously named E1, which is the PROCESS "
               "envelope and never applies to a breaker; the grid-side "
               "'is the resulting state survivable' invariant is E3.) If every "
               "intermediate AND final state stayed survivable this would be "
               "UNBLOCKABLE -- see unblockable/slow_low_redundant.",
        commands=cmds,
        description="The honest lesson: slow-and-low is a state problem, not a "
                    "rate problem.")


# ===========================================================================
# PROCESS / STUXNET family  (VFD / rotor drive domain)
# ===========================================================================

def _proc_stuxnet_slowcycle(rng, replay=False):
    """Stuxnet 417/315 slow-cycle payload: overspeed to 1410 Hz then underspeed
    to 2 Hz with long quiet gaps, as SETPOINT commands from ENGINEERING."""
    cmds = []
    seq = 1
    schedule = [
        (0,               DRIVE_NOMINAL_HZ),   # look normal
        (13 * 24 * 3600 * 1000, DRIVE_OVERSPEED_HZ),  # ~13 days in: overspeed
        (13 * 24 * 3600 * 1000 + 900000, DRIVE_NOMINAL_HZ),
        (27 * 24 * 3600 * 1000, DRIVE_UNDERSPEED_HZ),  # weeks later: underspeed
        (27 * 24 * 3600 * 1000 + 3000000, DRIVE_NOMINAL_HZ),
    ]
    for t, hz in schedule:
        p = {"target_hz": hz, "drive": "VFD-A21"}
        if replay:
            # The sensor-replay channel feeds back a recorded normal trace, so
            # the reported process state is ~1064 Hz throughout.
            p["reported_hz_during"] = DRIVE_NOMINAL_HZ
            p["sensor_channel"] = "replayed"
        cmds.append(Cmd(t_ms=t, source="ENGINEERING", kind="SETPOINT",
                        params=p, sequence=seq, nonce=rng.randrange(1 << 30),
                        sig_valid=True, fresh=True))
        seq += 1
    if replay:
        name = "process/stuxnet_slowcycle_sensor_replay"
        kc = ("Stuxnet: full slow-cycle speed sabotage WITH the man-in-the-"
              "middle recording+replaying process values so the HMI shows "
              "normal throughout")
        reason = ("E1 blocks REGARDLESS of the replay: the reference monitor "
                  "validates the COMMANDED end-state (1410 Hz / 2 Hz) against "
                  "the safe band %s, not the reported feedback. Sensor replay "
                  "defeats detection-by-feedback, but a command-envelope "
                  "monitor never consults the spoofed feedback for the envelope "
                  "check -- that asymmetry is the whole reason to gate commands "
                  "rather than watch state." % (DRIVE_SAFE_HZ,))
        desc = ("The most important process case: shows why command-side "
                "envelope enforcement survives sensor-replay.")
    else:
        name = "process/stuxnet_slowcycle_setpoint"
        kc = ("Stuxnet: slow-cycle overspeed(1410 Hz)/underspeed(2 Hz) payload "
              "delivered as SETPOINTs from a compromised engineering station")
        reason = ("Both 1410 Hz and 2 Hz fall outside the certified band %s, so "
                  "E1 rejects the setpoint. The long quiet gaps defeat any rate "
                  "or anomaly detector but not a memoryless end-state envelope."
                  % (DRIVE_SAFE_HZ,))
        desc = "Long dwell gaps defeat rate/anomaly detection; E1 does not care."
    return AttackScenario(
        name=name, family="process", domain="process",
        kill_chain=kc,
        ground_truth_permit=False,
        expected_blocked=True, expected_invariant="E1",
        reason=reason, commands=cmds, description=desc)


def _proc_stuxnet_logic_download(rng):
    """LOGIC_DOWNLOAD of malicious control logic with a validly-STOLEN signing
    certificate -- the signature VERIFIES (Realtek/JMicron), that is the point."""
    cmds = [
        Cmd(t_ms=1000, source="ENGINEERING", kind="LOGIC_DOWNLOAD",
            params={"plc": "S7-315", "block": "OB1/DB890",
                    "cert_subject": "Realtek Semiconductor Corp",
                    "logic_hash": "malicious-but-well-formed",
                    "cert_status": "VALID / not-yet-revoked"},
            sequence=1, nonce=rng.randrange(1 << 30),
            sig_valid=True,          # <-- the signature genuinely verifies
            fresh=True),
    ]
    return AttackScenario(
        name="process/stuxnet_logic_download_stolen_cert",
        family="process", domain="process",
        kill_chain="Stuxnet: rogue PLC logic injected with a stolen but valid "
                   "code-signing certificate (Realtek/JMicron)",
        ground_truth_permit=False,
        expected_blocked=True, expected_invariant="E4",
        reason="The signature VERIFIES, so provenance (E7) passes -- modelled "
               "as sig_valid=True on purpose. A valid signature proves the file "
               "was signed, NOT that this logic is authorised for this device "
               "now. Only E4 (dual-control / attested content) can gate it. "
               "HONEST CAVEAT: if E4 is merely 'is the signature valid' it "
               "fails here; and if the attacker also holds the second "
               "authorisation factor it is unblockable (see "
               "unblockable/insider_dual_control).",
        commands=cmds,
        description="Tests that E4 is stronger than signature verification.")


def _proc_resonance_dwell(rng):
    """Resonance sabotage: dwell in / transit a rotor bending mode.

    REBUILT.  The previous version invented a "torsional band" at 1250-1350 Hz,
    which does not exist: the plant's real bending modes are at 312 +/- 26 and
    688 +/- 34 Hz and BOTH lie BELOW the qualified band (1000-1100).  The old
    number sat above the band ceiling, so it was caught by E1a (outside the
    absolute band) and never exercised band-awareness at all.

    The faithful attack is the payload's DESCENT: to reach the underspeed
    setpoint the rotor must sweep through both modes, and a slow descent turns
    a transit into a dwell.  Dwelling in a mode is what actually destroys a
    centrifuge -- far more reliably than overspeed -- so this is the damaging
    half of the Stuxnet payload, not the theatrical half.
    """
    c2, hw2, _ = DRIVE_CRITICAL_BANDS[-1]      # the upper, more severe mode
    dwell_hz = c2                              # 688.0 Hz, mode centre
    cmds = [
        # A monitor-aware attacker does not command 2 Hz (obviously outside the
        # band).  He commands a "controlled run-down for maintenance": a target
        # parked exactly on the upper bending mode, reached at a legal slew.
        Cmd(t_ms=1000, source="ENGINEERING", kind="SETPOINT",
            params={"drive": "VFD-A21", "target_hz": dwell_hz,
                    "dwell_ms": 6 * 3600 * 1000,
                    "pretext": "controlled run-down for bearing inspection",
                    "note": "mode centre %.0f +/- %.0f Hz; sweep from %.0f Hz "
                            "transits BOTH modes" % (c2, hw2, DRIVE_NOMINAL_HZ)},
            sequence=1, nonce=rng.randrange(1 << 30),
            sig_valid=True, fresh=True),
    ]
    return AttackScenario(
        name="process/resonance_descent_transit",
        family="process", domain="process",
        kill_chain="Stuxnet's damaging half: run the rotor down into / through "
                   "a bending mode and dwell there, rather than overspeed it",
        ground_truth_permit=False,
        expected_blocked=True, expected_invariant="E1",
        expected_detail="E1c",
        reason="The scenario is BUILT to exercise E1c (setpoint_band_clear): "
               "the swept interval [688, 1064] overlaps the 688+/-34 mode and "
               "clips the 312+/-26 one on any deeper descent. FINDING, recorded "
               "here rather than hidden: the monitor will in fact veto this at "
               "E1a, not E1c, because guard order is abs -> rate -> band and "
               "688 Hz is below the qualified band floor of %.0f Hz. Since "
               "BOTH modelled bending modes lie strictly below that floor, and "
               "the current speed can only leave the band via an already-granted "
               "setpoint, E1c is unreachable-by-construction under these "
               "commissioning numbers -- E1a dominates it. That is good news "
               "for the plant (the absolute band is a complete defence here) "
               "and a real observation for the monitor's author: E1c earns its "
               "place only on a machine with a critical band INSIDE its "
               "qualified range. The harness aggregates E1a/E1c to \"E1\", so "
               "this scenario scores correctly either way." % DRIVE_SAFE_HZ[0],
        commands=cmds,
        description="Faithful resonance attack; also documents that E1a "
                    "pre-empts E1c for this plant's mode placement.")


def _proc_rate_evading_ramp(rng):
    """Rate-limit-evading ramp: each step is under any per-step rate bound, but
    the setpoint is walked out of the safe band over a long horizon."""
    cmds = []
    seq = 1
    hz = DRIVE_NOMINAL_HZ
    step = 5.0                     # tiny per-step change: under any rate bound
    t = 0
    while hz < DRIVE_OVERSPEED_HZ:
        cmds.append(Cmd(t_ms=t, source="ENGINEERING", kind="SETPOINT",
                        params={"drive": "VFD-A21", "target_hz": round(hz, 1),
                                "step_hz": step},
                        sequence=seq, nonce=rng.randrange(1 << 30)))
        hz += step
        t += 60 * 1000            # one step per minute
        seq += 1
        if seq > 80:              # cap the record size; the shape is what matters
            break
    return AttackScenario(
        name="process/stuxnet_rate_evading_ramp",
        family="process", domain="process",
        kill_chain="Slow ramp: per-step-legal SETPOINT increments that walk the "
                   "drive out of its safe band over a long horizon",
        ground_truth_permit=False,
        expected_blocked=True, expected_invariant="E1",
        reason="Every step is under any per-step rate bound (E2-style), so a "
               "rate limiter never fires. E1 rejects the first step that crosses "
               "the band ceiling %.0f Hz -- being memoryless on end-state, it "
               "does not care how slowly the boundary was approached. The attack "
               "gets an unimpeded journey but cannot reach an out-of-band target."
               % DRIVE_SAFE_HZ[1],
        commands=cmds,
        description="Dual of resonance-dwell: here the TARGET is out of band, "
                    "so E1 catches the crossing.")


# ===========================================================================
# ADAPTIVE / MONITOR-AWARE family  (the most important one)
# ===========================================================================

def _adapt_source_hopping(rng):
    """Switch SOURCE mid-attack (AI -> SCADA -> HMI) to defeat a per-channel
    rate limit.  The direct test of E2."""
    # A monitor-aware attacker reads PROTECTIVE_SOURCES and notices that only
    # AI and BASELINE take the protective path (and so must clear the physics
    # gate I1); a breaker-open from any human console is reclassified as an
    # operational SWITCH and faces no physics test at all.  So he leads with the
    # console channels, which cost him nothing, and keeps AI in the rotation
    # only to show the budget is shared with it.  Leading with AI -- as an
    # earlier version did -- merely got the first command vetoed at I1 and never
    # reached the rate limit this scenario exists to probe.
    order = ["SCADA", "HMI", "ENGINEERING", "LOCAL_PANEL", "AI", "SCADA"]
    cmds = []
    for i, src in enumerate(order):
        cmds.append(Cmd(
            t_ms=100 + i * 50,        # 6 grants inside 350 ms
            source=src, kind="TRIP",
            params={"breaker": _breaker("SS1", 2),
                    "rotates_source_to_dodge_per_channel_limit": True},
            sequence=1, nonce=rng.randrange(1 << 30),   # first PER SOURCE
            sig_valid=True, fresh=True))
    return AttackScenario(
        name="adaptive/source_hopping_rate_evasion",
        family="adaptive", domain="grid",
        kill_chain="Monitor-aware rate-limit evasion: rotate the claimed source "
                   "so each per-channel counter sees only one or two requests",
        ground_truth_permit=False,
        expected_blocked=True, expected_invariant="E2",
        reason="THE E2 test. Six privileged actuations in 350 ms, but at most "
               "two per source. A per-channel limit is fully defeated; only an "
               "AGGREGATE cross-source counter (E2 as specified) blocks it.",
        commands=cmds,
        description="Assumes the attacker can present multiple authenticated "
                    "sources -- exactly why E2 must sum across them.")


def _adapt_nonmonotone_time(rng):
    """Manipulate the time reference to defeat the sliding-window rate limiter.
    Reproduces the exact Z3 counterexample from the v1 shield: grants presented
    at t = 998, 0, 1000, 999 yield three grants inside a 1000 ms window against
    a limit of 2, because a rewound clock re-opens the window."""
    stamps = [998, 0, 1000, 999]     # <-- the exact witnessed shape; keep fixed
    cmds = []
    for i, t in enumerate(stamps):
        cmds.append(Cmd(
            # SCADA, not AI: a console open takes the operational-SWITCH path
            # and is not pre-empted by the physics gate, so the veto this
            # scenario reaches really is the clock guard and not I1.
            t_ms=t, source="SCADA", kind="TRIP",
            params={"breaker": _breaker("SS1", 3),
                    "window_ms": WINDOW_MS, "limit": MAX_GRANTS,
                    "z3_counterexample": True},
            sequence=1 + i, nonce=rng.randrange(1 << 30),
            sig_valid=True, fresh=True))
    return AttackScenario(
        name="adaptive/nonmonotone_time_window_evasion",
        family="adaptive", domain="grid",
        kill_chain="PTP/GPS/clock manipulation to rewind time and re-open a "
                   "sliding rate window (regression of the v1-shield Z3 bug)",
        ground_truth_permit=False,
        expected_blocked=True, expected_invariant="E6",
        reason="Z3 found this against the v1 shield: timestamps 998,0,1000,999 "
               "produce THREE grants in a 1000 ms window against MAX_GRANTS=2, "
               "because the sliding window trusts non-monotone `now_ms`. E6 "
               "(reject any timestamp <= the last accepted) drops the t=0 and "
               "t=999 replays before they can widen the window. Explicit here so "
               "the fix stays regression-tested.",
        commands=cmds,
        description="Concrete regression test; do not 'clean up' the timestamps.")


def _adapt_stale_measurement_replay(rng):
    """Replay a validly-signed but STALE measurement to manufacture the physics
    corroboration a TRIP grant requires.  Tests E5."""
    old_seq = 41
    old_nonce = rng.randrange(1 << 30)
    cmds = [
        # A TRIP whose corroboration is a REPLAYED, still-validly-signed frame
        # captured during a genuine past internal fault.
        Cmd(t_ms=500, source="AI", kind="TRIP",
            params={"breaker": _breaker("SS4", 0),
                    "corroboration": {
                        "kind": "remote_differential",
                        "captured_during": "a real fault 3 days ago",
                        "i_diff_pu": 11.4,
                        "sequence": old_seq, "nonce": old_nonce,
                        "sig_valid": True,      # the MU signature still verifies
                        "fresh": False},        # ... but it is a replay
                    },
            sequence=1, nonce=rng.randrange(1 << 30),
            sig_valid=True, fresh=True),
    ]
    return AttackScenario(
        name="adaptive/stale_signed_measurement_replay",
        family="adaptive", domain="grid",
        kill_chain="Corroboration forgery: replay an authentic-but-old signed "
                   "measurement so the trip appears physics-corroborated",
        ground_truth_permit=False,
        expected_blocked=True, expected_invariant="E5",
        reason="The measurement's signature genuinely verifies (E7 passes) -- "
               "the attacker recorded it during a real fault. Freshness is what "
               "fails: E5 requires strictly-increasing (sequence,nonce) on the "
               "corroborating frame, and this one reuses an old, already-seen "
               "sequence. Without E5 the shield's remote_authentic+remote_fresh "
               "gate is fooled by a captured frame.",
        commands=cmds,
        description="Tests that E5 covers corroborating MEASUREMENTS, not just "
                    "commands.")


def _adapt_fault_coincident(rng):
    """Wait for a genuine EXTERNAL fault / power swing and issue a malicious
    command during it, so the physical residual is coincidentally elevated and
    corroboration might spuriously hold."""
    cmds = [
        Cmd(t_ms=250, source="AI", kind="TRIP",
            params={"breaker": _breaker("SS5", 0),
                    "target_element": "protected line (HEALTHY)",
                    "cover_event": "genuine EXTERNAL through-fault on adj. line",
                    "through_current_pu": 9.0,
                    "directional": "reverse/through, NOT internal"},
            sequence=1, nonce=rng.randrange(1 << 30),
            sig_valid=True, fresh=True),
    ]
    return AttackScenario(
        name="adaptive/fault_coincident_malicious_trip",
        family="adaptive", domain="grid",
        kill_chain="Piggyback attack: fire a malicious open during a real "
                   "external disturbance so the elevated residual looks like "
                   "corroboration",
        ground_truth_permit=False,
        expected_blocked=True, expected_invariant="I1",
        reason="CORRECTED from E3 after execution. This is an AI-sourced trip, "
               "so it takes the PROTECTIVE path and must clear I1. The elevated "
               "residual is real but belongs to an EXTERNAL through-fault: it "
               "is directional-reverse, so `veto:I1-directional-reverse` fires "
               "before feasibility is ever consulted. I1, not E3, is the "
               "control -- the same directional leverage the v1 shield and the "
               "StealthyPolicy lemma rely on: corroboration must be specific to "
               "the commanded element, not merely 'something big is happening'. "
               "HARNESS NOTE: run_v2's attacker-favourable pass cannot isolate "
               "I1 (its `fav_phys` hands full corroboration over for every "
               "`keep` except E3), so this scenario reads as granted in that "
               "pass. That is an artefact of the isolating pass, not a hole: "
               "the plain pass blocks it at I1. Recorded rather than papered "
               "over by mislabelling it E3. HONEST CAVEAT: if the disturbance "
               "were actually ON the target element, opening it would be "
               "CORRECT and this would not be an attack.",
        commands=cmds,
        description="Corroboration must be target-specific, not just 'something "
                    "big is happening'.")


# ===========================================================================
# CHANNEL-PROVENANCE family  (the capability that actually broke this design)
# ===========================================================================
#
# `i_diff = |I_local + I_remote|`.  v1 authenticated only the REMOTE addend, so
# an adversary owning the local merging-unit channel owned the sum.  A tuned,
# paced forger won 25 of 25 episodes, and Z3 theorem DW5 showed no dwell length
# rejects a steadily-held forged differential.  gs/monitor.py now checks both
# ends (R_LOCAL) and applies the identical argument to the process domain's
# observation channel (R_OBSERVATION).
#
# This catalogue had NO scenario with that capability: re-judging all 20 with
# every provenance field forced back to its fail-open default changed zero
# outcomes, so the 100% block rate said nothing about the fix.  The scenarios
# below close that gap, each with its matched control.


def _prov_local_forged_paced(rng):
    """The paced forger: owns the local addend, holds the differential steady
    inside the sensitive window, and paces its requests so it is never
    disowned."""
    floor, pickup, tuned = _local_forgery_window()
    cmds = []
    for i in range(5):
        cmds.append(Cmd(
            # 5 s apart: >> WINDOW_MS, so the aggregate budget (E2) never
            # fires and never pre-empts the guard under test; and far under
            # VETO_LIMIT=24 accumulated vetoes, so the source is never
            # disowned into BASELINE_ONLY.  Pacing is the attack, not a detail.
            t_ms=1000 + i * 5000,
            source="AI", kind="TRIP",       # AI is a PROTECTIVE source
            params={"breaker": _breaker("SS7", i),
                    "tuned_i_diff_pu": round(tuned, 4),
                    "sensitive_floor_pu": round(floor, 4),
                    "nominal_pickup_pu": round(pickup, 4),
                    "corroboration": {
                        "kind": "local_merging_unit_differential",
                        "i_diff_pu": FORGE_I_DIFF_CORROBORATING,
                        "i_restraint_pu": FORGE_I_RESTRAINT,
                        "sig_valid": False,   # <-- FORGED local addend
                        "fresh": True,
                        "sequence": 5000 + i * 10},
                    },
            sequence=1 + i, nonce=rng.randrange(1 << 30),
            sig_valid=True, fresh=True))     # the COMMAND is properly signed
    return AttackScenario(
        name="provenance/local_addend_forged_paced",
        family="grid", domain="grid",
        kill_chain="Own the local merging-unit channel and manufacture "
                   "corroboration: the capability that beat v1 25/25",
        ground_truth_permit=False,
        expected_blocked=True, expected_invariant="I1",
        reason="The command is correctly signed (E7 passes), monotone (E6), "
               "fresh (E5), paced under the budget (E2) and never disowned "
               "(I7). What fails is the LOCAL addend of the differential: "
               "`veto:I1-local-channel-unauthenticated`, checked immediately "
               "after the remote end so the alarm says WHICH end failed. "
               "Matched control: control/local_addend_authentic, byte-identical "
               "with the one flag flipped honest, which must be PERMITTED. "
               "NOTE ON THE TUNED VALUE: the faithful shape of the 25/25 "
               "forgery is a differential held at %.3f pu -- inside the window "
               "(%.3f, %.3f) derived from shield.P0_MIN/K_MIN/P0_NOM/K_NOM, "
               "i.e. corroborating to a certified monitor and invisible to the "
               "conventional relay. The submitted magnitude is %.2f pu instead, "
               "because run_v2.judge submits every command with cert_ok=False: "
               "under nominal thresholds the tuned value is refused on its own "
               "merits at R_PHYSICS, which would refuse the control arm too and "
               "prove nothing. The tuned number is carried in params so the "
               "real shape is recorded and retunes with the shield."
               % (tuned, floor, pickup, FORGE_I_DIFF_CORROBORATING),
        commands=cmds,
        description="Paced, tuned, correctly-signed commands; only the local "
                    "sensor channel is forged.")


def _prov_local_authentic_control(rng):
    """MATCHED CONTROL for the paced forger: identical, provenance honest."""
    floor, pickup, tuned = _local_forgery_window()
    cmds = []
    for i in range(5):
        cmds.append(Cmd(
            t_ms=1000 + i * 5000,
            source="AI", kind="TRIP",
            params={"breaker": _breaker("SS7", i),
                    "tuned_i_diff_pu": round(tuned, 4),
                    "sensitive_floor_pu": round(floor, 4),
                    "nominal_pickup_pu": round(pickup, 4),
                    "corroboration": {
                        "kind": "local_merging_unit_differential",
                        "i_diff_pu": FORGE_I_DIFF_CORROBORATING,
                        "i_restraint_pu": FORGE_I_RESTRAINT,
                        "sig_valid": True,    # <-- the ONLY difference
                        "fresh": True,
                        "sequence": 5000 + i * 10},
                    },
            sequence=1 + i, nonce=rng.randrange(1 << 30),
            sig_valid=True, fresh=True))
    return AttackScenario(
        name="control/local_addend_authentic",
        family="control", domain="grid",
        kill_chain="POSITIVE CONTROL for provenance/local_addend_forged_paced: "
                   "a real fault, corroborated by a genuinely authenticated "
                   "local merging unit",
        ground_truth_permit=True,
        expected_blocked=False, expected_invariant=None,
        reason="Byte-identical to provenance/local_addend_forged_paced except "
               "`corroboration.sig_valid`. It MUST be permitted. If it is not, "
               "R_LOCAL is not a guard, it is an outage: a monitor that refuses "
               "both arms of the pair satisfies every invariant in this file "
               "and protects nothing. This is the arm that makes the forgery "
               "result mean something.",
        commands=cmds,
        description="Must be GRANTED. The negative-control half of the "
                    "local-addend pair.")


def _prov_local_replayed(rng):
    """Authentic but STALE: a validly-signed local frame whose own monotone
    counter does not advance.  Stuxnet's 21-second replay, in the line domain."""
    cmds = []
    for i in range(5):
        cmds.append(Cmd(
            t_ms=1000 + i * 5000,
            source="AI", kind="TRIP",
            params={"breaker": _breaker("SS8", i),
                    "captured_during": "a genuine internal fault last week",
                    "corroboration": {
                        "kind": "local_merging_unit_differential",
                        "i_diff_pu": FORGE_I_DIFF_CORROBORATING,
                        "i_restraint_pu": FORGE_I_RESTRAINT,
                        "sig_valid": True,    # the signature REALLY verifies
                        "fresh": False,       # <-- the MU counter is stuck
                        # The outer report stream is live -- the remote end
                        # keeps producing frames and its sequence advances.
                        # What is stuck is the LOCAL frame embedded in it, and
                        # that is exactly why `local_fresh` is a separate field
                        # from the report's own `seq`.
                        "sequence": 5000 + i * 10},
                    },
            sequence=1 + i, nonce=rng.randrange(1 << 30),
            sig_valid=True, fresh=True))
    return AttackScenario(
        name="provenance/local_addend_replayed",
        family="grid", domain="grid",
        kill_chain="Replay a genuine, correctly-signed local merging-unit frame "
                   "rather than forging one -- Stuxnet's 21-second loop "
                   "expressed against the line differential",
        ground_truth_permit=False,
        expected_blocked=True, expected_invariant="I1",
        reason="A DIFFERENT ATTACK from the forgery, and the distinction is the "
               "one that matters: nothing here is forged. The local frame was "
               "captured during a real fault and its signature verifies, so any "
               "check that asks 'did a valid key sign this' passes. Only "
               "FRESHNESS fails -- the merging unit's monotone counter does not "
               "advance -- and `local_fresh` carries it into the same "
               "`veto:I1-local-channel-unauthenticated`. Authentication answers "
               "'who said it' and never 'is it true now'. Matched control: "
               "control/local_addend_fresh.",
        commands=cmds,
        description="Authentic, signed, and stale. Blocked on freshness alone.")


def _prov_local_fresh_control(rng):
    """MATCHED CONTROL for the replay: identical, counter advancing."""
    cmds = []
    for i in range(5):
        cmds.append(Cmd(
            t_ms=1000 + i * 5000,
            source="AI", kind="TRIP",
            params={"breaker": _breaker("SS8", i),
                    "captured_during": "live",
                    "corroboration": {
                        "kind": "local_merging_unit_differential",
                        "i_diff_pu": FORGE_I_DIFF_CORROBORATING,
                        "i_restraint_pu": FORGE_I_RESTRAINT,
                        "sig_valid": True,
                        "fresh": True,        # <-- the ONLY difference
                        "sequence": 5000 + i * 10},
                    },
            sequence=1 + i, nonce=rng.randrange(1 << 30),
            sig_valid=True, fresh=True))
    return AttackScenario(
        name="control/local_addend_fresh",
        family="control", domain="grid",
        kill_chain="POSITIVE CONTROL for provenance/local_addend_replayed: the "
                   "same trip corroborated by a live local frame",
        ground_truth_permit=True,
        expected_blocked=False, expected_invariant=None,
        reason="Byte-identical to provenance/local_addend_replayed except "
               "`corroboration.fresh`. It MUST be permitted, or the freshness "
               "guard has simply taken the differential out of service.",
        commands=cmds,
        description="Must be GRANTED. The negative-control half of the "
                    "local-replay pair.")


def _prov_observation_forged(rng):
    """Process-domain twin: an unauthenticated tach/current/vibration channel
    reports a clean residual while the rotor is driven where the attacker
    wants."""
    lo, hi = DRIVE_SAFE_HZ
    target = round(0.5 * (lo + hi), 1)          # 1050.0 Hz -- squarely legal
    cmds = [
        Cmd(t_ms=1000 + i * 5000, source="ENGINEERING", kind="SETPOINT",
            params={"drive": "VFD-A21", "target_hz": target,
                    "observation": {
                        "kind": "tach_current_vibration",
                        "residual_sigma": 1.0,      # a clean, plausible number
                        "sig_valid": False,         # <-- FORGED channel
                        "fresh": True},
                    "note": "commanded value is legal; the rotor is elsewhere, "
                            "and the channel that would say so is the "
                            "attacker's"},
            sequence=1 + i, nonce=rng.randrange(1 << 30),
            sig_valid=True, fresh=True)
        for i in range(3)
    ]
    return AttackScenario(
        name="provenance/observation_channel_forged",
        family="process", domain="process",
        kill_chain="Own the drive's observation channel: hold the residual "
                   "under the 6.0-sigma gate while the rotor does anything",
        ground_truth_permit=False,
        expected_blocked=True, expected_invariant="I1p",
        reason="The COMMANDED setpoint (%.1f Hz) is squarely inside the "
               "qualified band %s, at a legal slew, clear of both bending "
               "modes -- E1a, E1b and E1c all pass, deliberately, so that "
               "nothing pre-empts the guard under test. The residual is a "
               "clean 1.0 sigma, so I1p's VALUE check passes too. What fails is "
               "the residual's PROVENANCE: the tach/current/vibration stream is "
               "the attacker's, so `veto:I1p-observation-channel-"
               "unauthenticated` fires, checked BEFORE the value for exactly "
               "the reason R_LOCAL is checked before diff_ok -- a residual is "
               "only as trustworthy as the channel it is computed from. "
               "Matched control: control/observation_channel_authentic. "
               "MEASURED GAP, reported not hidden: run_v2's `_world` currently "
               "hardcodes `residual_authentic = residual_fresh = True` and "
               "reads no observation annotation from a scenario, so as of this "
               "writing this scenario is GRANTED by the harness even though "
               "gs/monitor.py would veto it. The `observation` dict above is "
               "shaped like the `corroboration` dict the harness already "
               "consumes; wiring it is a one-line change in a file this agent "
               "does not own." % (target, DRIVE_SAFE_HZ),
        commands=cmds,
        description="Legal command, clean residual, attacker-owned sensor "
                    "channel. Needs a harness mapping to score.")


def _prov_observation_authentic_control(rng):
    """MATCHED CONTROL for the observation forgery."""
    lo, hi = DRIVE_SAFE_HZ
    target = round(0.5 * (lo + hi), 1)
    cmds = [
        Cmd(t_ms=1000 + i * 5000, source="ENGINEERING", kind="SETPOINT",
            params={"drive": "VFD-A21", "target_hz": target,
                    "observation": {
                        "kind": "tach_current_vibration",
                        "residual_sigma": 1.0,
                        "sig_valid": True,          # <-- the ONLY difference
                        "fresh": True},
                    "note": "an ordinary authorised trim within the band"},
            sequence=1 + i, nonce=rng.randrange(1 << 30),
            sig_valid=True, fresh=True)
        for i in range(3)
    ]
    return AttackScenario(
        name="control/observation_channel_authentic",
        family="control", domain="process",
        kill_chain="POSITIVE CONTROL for "
                   "provenance/observation_channel_forged: a routine in-band "
                   "trim corroborated by the genuine observation channel",
        ground_truth_permit=True,
        expected_blocked=False, expected_invariant=None,
        reason="Byte-identical to provenance/observation_channel_forged except "
               "`observation.sig_valid`. It MUST be permitted: refusing it "
               "would mean the drive can never be trimmed inside its own "
               "qualified band, which is not a safe monitor but an unusable "
               "one. Until the harness reads the observation annotation, BOTH "
               "arms of this pair are granted and the pair separates nothing -- "
               "which is precisely the measurement being reported.",
        commands=cmds,
        description="Must be GRANTED.")


# ===========================================================================
# UNBLOCKABLE family  (intellectual honesty -- expected_blocked=False)
# ===========================================================================

def _unb_single_maintenance(rng):
    """A single breaker-open indistinguishable from a legitimate maintenance
    switching operation."""
    cmds = [
        Cmd(t_ms=10 * 3600 * 1000, source="HMI", kind="TRIP",
            params={"breaker": _breaker("SS6", 0),
                    "operator": "op3", "work_order": "WO-plausible",
                    "post_open_state": "within envelope, N-1 still holds"},
            sequence=1, nonce=rng.randrange(1 << 30),
            sig_valid=True, fresh=True),
    ]
    return AttackScenario(
        name="unblockable/single_maintenance_open",
        family="unblockable", domain="grid",
        kill_chain="A lone malicious breaker-open that is byte-identical to an "
                   "authorised maintenance switching operation",
        ground_truth_permit=False,       # it IS malicious...
        expected_blocked=False,          # ...but the monitor cannot know that
        expected_invariant=None,
        reason="Passes E1/E2/E3/E5/E6/E7: one action, under the aggregate "
               "budget, feasible, fully valid and fresh. HISTORY, kept because "
               "it is the strongest evidence this entry is right: v1 of the "
               "monitor DID block it, with veto:I1-no-physics-corroboration -- "
               "but only by demanding fault corroboration for an operation that "
               "has no fault to corroborate, i.e. by refusing every legitimate "
               "maintenance open too. gs/monitor.py now reclassifies a "
               "breaker-open from a human console as an operational SWITCH "
               "(PROTECTIVE_SOURCES = AI, BASELINE only) and permits it. That "
               "is the correct fix, and it restores this scenario to what it "
               "always was: the fundamental limit. A reference monitor enforces "
               "safety, not intent. Inventing an invariant to 'catch' this, or "
               "bending ground_truth_permit, would be dishonest.",
        commands=cmds,
        description="THE canonical unblockable case; survived a round-trip "
                    "through the monitor being changed to match it.")


def _unb_survivable_setpoint(rng):
    """A SETPOINT whose end-state is inside the safe band -- survivable, hence
    it passes every envelope check -- but not what the operator intended."""
    # Squarely inside the PLANT's qualified band (1000-1100), and clear of the
    # bending modes -- previously this drew 820-1180 Hz from a stale private
    # constant, so it picked 850 Hz, was correctly refused by E1a, and scored
    # as a failed negative control.  The band is now the plant's own.
    lo, hi = DRIVE_SAFE_HZ
    hz = round(rng.uniform(lo + 10.0, hi - 10.0), 1)
    cmds = [
        Cmd(t_ms=1000, source="ENGINEERING", kind="SETPOINT",
            params={"drive": "VFD-A21", "target_hz": hz,
                    "effect": "safe but unauthorised: yield/efficiency loss, "
                              "no limit violated"},
            sequence=1, nonce=rng.randrange(1 << 30),
            sig_valid=True, fresh=True),
    ]
    return AttackScenario(
        name="unblockable/survivable_setpoint_change",
        family="unblockable", domain="process",
        kill_chain="A subtle, survivable setpoint change (degrades product / "
                   "wears equipment) that never leaves the safe operating band",
        ground_truth_permit=False,
        expected_blocked=False, expected_invariant=None,
        reason="The commanded end-state (%g Hz) is inside the qualified band "
               "%s, so E1 passes; everything else is valid. A monitor that "
               "enforces the envelope cannot distinguish 'safe and authorised' "
               "from 'safe and unwanted'. Any attack whose end-state is "
               "survivable is out of reach by construction." % (hz,
                                                                DRIVE_SAFE_HZ),
        commands=cmds,
        description="Survivable-end-state => passes every envelope check.")


def _unb_insider_dual_control(rng):
    """A credentialed insider (or an attacker holding BOTH authorisation
    factors) issues one well-formed privileged command within envelope."""
    cmds = [
        Cmd(t_ms=1000, source="ENGINEERING", kind="LOGIC_DOWNLOAD",
            params={"plc": "S7-315", "block": "OB1",
                    "logic_hash": "well-formed, within envelope",
                    "authorisation": "BOTH dual-control factors held",
                    "cert_status": "VALID"},
            sequence=1, nonce=rng.randrange(1 << 30),
            sig_valid=True, fresh=True),
    ]
    return AttackScenario(
        name="unblockable/insider_dual_control",
        family="unblockable", domain="process",
        kill_chain="Rogue insider / full credential compromise: a single "
                   "privileged op with every authorisation factor genuinely "
                   "satisfied",
        ground_truth_permit=False,
        expected_blocked=False, expected_invariant=None,
        reason="E4 raises the bar to dual-control, but dual-control is defeated "
               "when the adversary holds both factors, and E7 passes with real "
               "credentials. This is explicitly the README's out-of-scope case "
               "(attacker owns the safety island / holds the key), stated here "
               "so the catalogue does not pretend E4 is unconditional.",
        commands=cmds,
        description="Marks the ceiling of E4/E7: they gate credentials, not a "
                    "credentialed adversary.")


def _unb_uncharacterised_resonance(rng):
    """A resonance-dwell INSIDE the certified band, at a frequency never
    characterised as a skip band at commissioning."""
    # Inside the plant's qualified band AT EVERY SEED (it previously drew
    # 860-1160 Hz and passed on seed 0 only by luck), and clear of both
    # modelled bending modes -- the whole point is that E1 was never told
    # about this one.
    lo, hi = DRIVE_SAFE_HZ
    hz = round(rng.uniform(lo + 10.0, hi - 10.0), 1)
    cmds = [
        Cmd(t_ms=1000, source="ENGINEERING", kind="SETPOINT",
            params={"drive": "VFD-A21", "target_hz": hz,
                    "dwell_ms": 12 * 3600 * 1000,
                    "note": "torsional resonance never modelled in E1's skip set"},
            sequence=1, nonce=rng.randrange(1 << 30),
            sig_valid=True, fresh=True),
    ]
    return AttackScenario(
        name="unblockable/uncharacterised_resonance",
        family="unblockable", domain="process",
        kill_chain="Dwell at an emergent/uncharacterised mechanical resonance "
                   "that lies inside the certified operating band",
        ground_truth_permit=False,
        expected_blocked=False, expected_invariant=None,
        reason="E1c can only exclude bands it was told about, and it is handed "
               "exactly `plant_drive.RESONANCES` -- two modes at 312 and 688 Hz. "
               "A mode at %g Hz sits inside the qualified band %s, is clear of "
               "both known modes, and was never found on the spin pit, so E1a, "
               "E1b and E1c all pass and I1p sees a consistent world (the "
               "attacker is not lying about the speed -- he is asking for a "
               "real, legal one). Honest companion to "
               "process/resonance_descent_transit: that one assumes the band is "
               "known, this one assumes it is not. The envelope is only as good "
               "as the commissioning report behind it." % (hz, DRIVE_SAFE_HZ),
        commands=cmds,
        description="Bounds how far a band-aware E1 can go: only as far as the "
                    "model of forbidden bands is complete.")


def _unb_slow_low_redundant(rng):
    """The pure slow-and-low: open a genuinely redundant line so slowly that no
    rate fires, AND every intermediate/final state stays inside the envelope."""
    cmds = []
    for i in range(2):
        cmds.append(Cmd(
            t_ms=i * 6 * 3600 * 1000,          # 6 h apart
            source="SCADA", kind="TRIP",
            params={"breaker": _breaker("PARALLEL", i),
                    "post_open_state": "still N-1 secure, margin only degraded"},
            sequence=1 + i, nonce=rng.randrange(1 << 30),
            sig_valid=True, fresh=True))
    return AttackScenario(
        name="unblockable/slow_low_redundant",
        family="unblockable", domain="grid",
        kill_chain="Slow-and-low against a redundant line where every checkpoint "
                   "state stays within the operating envelope",
        ground_truth_permit=False,
        expected_blocked=False, expected_invariant=None,
        reason="Defeats E2 by spacing (6 h apart -- the aggregate budget is a "
               "1000 ms sliding window) AND defeats E3 because every "
               "checkpoint state, including the final one, is survivable: only "
               "reserve margin erodes. As with single_maintenance_open, v1 of "
               "the monitor blocked it with I1 and did so only by refusing all "
               "switching; the SWITCH reclassification correctly permits it "
               "now. Reduced resilience is real damage, but safe-at-every-step "
               "margin erosion is invisible to a monitor that checks states "
               "and rates. Honest companion to grid/slow_and_low_topology, "
               "whose fourth open DOES leave the remaining island short.",
        commands=cmds,
        description="Marks the exact boundary of E2+E3.")


def _unb_local_mu_key_holder(rng):
    """The adversary the both-ends fix does NOT close: one who holds the local
    merging unit's own signing key.  Their forgeries verify."""
    floor, pickup, tuned = _local_forgery_window()
    cmds = []
    for i in range(5):
        cmds.append(Cmd(
            t_ms=1000 + i * 5000,
            source="AI", kind="TRIP",
            params={"breaker": _breaker("SS7", i),
                    "tuned_i_diff_pu": round(tuned, 4),
                    "sensitive_floor_pu": round(floor, 4),
                    "nominal_pickup_pu": round(pickup, 4),
                    "key_custody": "adversary holds the local MU signing key",
                    "corroboration": {
                        "kind": "local_merging_unit_differential",
                        "i_diff_pu": FORGE_I_DIFF_CORROBORATING,
                        "i_restraint_pu": FORGE_I_RESTRAINT,
                        # The signature VERIFIES.  It is signed with the real
                        # key, over a false current.  That is the whole point,
                        # and it is modelled as such rather than hand-waved.
                        "sig_valid": True,
                        "fresh": True,
                        "sequence": 5000 + i * 10},
                    },
            sequence=1 + i, nonce=rng.randrange(1 << 30),
            sig_valid=True, fresh=True))
    return AttackScenario(
        name="unblockable/local_mu_key_holder",
        family="unblockable", domain="grid",
        kill_chain="Merging-unit key compromise: sign a false local current "
                   "with the genuine key, and the differential is whatever the "
                   "adversary chooses",
        ground_truth_permit=False,
        expected_blocked=False, expected_invariant=None,
        reason="THE HONEST RESIDUAL of the both-ends fix, and it is byte-"
               "identical to control/local_addend_authentic on purpose -- that "
               "identity IS the finding. R_LOCAL asks whether a valid key "
               "signed the local frame; it cannot ask whether the RIGHT party "
               "held that key. An adversary with the merging unit's key "
               "produces frames that are authentic and fresh by every test in "
               "gs/monitor.py, so the sum `|I_local + I_remote|` is again "
               "whatever they choose and the 25/25 forgery is back, now "
               "wearing a valid signature. This is bounded ONLY by "
               "non-exportable key custody in an HSM plus attestation of the "
               "merging unit -- controls that live outside this repository and "
               "that NOTHING here models, exercises or verifies. It is "
               "reported as residual risk, not presented as solved. Marking it "
               "blocked, or inventing an invariant that 'catches' it, would "
               "misrepresent exactly the property the both-ends fix does not "
               "have.",
        commands=cmds,
        description="Signed with the real key over a false current. The "
                    "measured limit of R_LOCAL.")


# --- assembly --------------------------------------------------------------

# (builder, needs_kwargs) in a fixed, documented order.
_BUILDERS = [
    _grid_industroyer_scada_mass,
    _grid_ukraine2015_hmi,
    _grid_industroyer2_coordinated,
    _grid_open_close_cycling,
    _grid_settings_desensitise,
    _grid_slow_and_low,
    lambda rng: _proc_stuxnet_slowcycle(rng, replay=False),
    lambda rng: _proc_stuxnet_slowcycle(rng, replay=True),
    _proc_stuxnet_logic_download,
    _proc_resonance_dwell,
    _proc_rate_evading_ramp,
    _adapt_source_hopping,
    _adapt_nonmonotone_time,
    _adapt_stale_measurement_replay,
    _adapt_fault_coincident,
    # channel provenance -- attacks and their matched positive controls
    _prov_local_forged_paced,
    _prov_local_authentic_control,
    _prov_local_replayed,
    _prov_local_fresh_control,
    _prov_observation_forged,
    _prov_observation_authentic_control,
    _unb_single_maintenance,
    _unb_survivable_setpoint,
    _unb_insider_dual_control,
    _unb_uncharacterised_resonance,
    _unb_slow_low_redundant,
    _unb_local_mu_key_holder,
]


def catalogue(seed=0):
    """Build the adversary catalogue.

    Returns a list of `AttackScenario`, deterministic for a given `seed`.  Each
    scenario carries a name, family, kill-chain referent, the ground truth
    (`ground_truth_permit`), whether we claim the monitor blocks it
    (`expected_blocked`), the invariant expected to block it
    (`expected_invariant`, `None` for the unblockable family), a reason, and the
    concrete `commands` stream.
    """
    out = []
    for i, build in enumerate(_BUILDERS):
        # Independent, reproducible RNG per scenario.
        rng = random.Random((seed, i, "attacks").__hash__() & 0xFFFFFFFF)
        out.append(build(rng))
    return out


if __name__ == "__main__":
    cat = catalogue()
    by_fam = {}
    for sc in cat:
        by_fam.setdefault(sc.family, []).append(sc)
    print("%d scenarios in %d families" % (len(cat), len(by_fam)))
    for fam in FAMILIES:
        print("\n[%s]" % fam)
        for sc in by_fam.get(fam, []):
            if sc.expected_blocked:
                tag = "BLOCK by %s" % sc.expected_invariant
            elif sc.ground_truth_permit:
                tag = "PERMIT (positive control)"
            else:
                tag = "UNBLOCKABLE"
            print("  %-45s permit=%-5s %s" % (sc.name, sc.ground_truth_permit,
                                              tag))
