"""Property-based tests for the generalised actuation reference monitor
(gs/monitor.py), mirroring what tests/test_properties.py does for the v1
shield (gs/shield.py).

The monitor is now the whole safety argument: every path to an actuator --
the AI, SCADA, a stolen HMI session, the engineering workstation, the local
panel -- presents a `Command` and faces the same guards.  These tests attack
it with hypothesis: arbitrary sources (including out-of-range and BASELINE),
arbitrary kinds (including unrecognised ones and SWITCH), absurd params (NaN,
+/-inf, negative, enormous), replayed and out-of-order nonce/sequence values,
several distinct actuation TARGETS, NON-MONOTONE timestamps, and
arbitrary-length traces; and assert the documented invariants hold on EVERY
trace.

If a test here fails, gs/monitor.py is NOT to be patched to make it pass --
the counterexample is a finding about the design and is reported as such.

Where a test documents a deliberate LIMIT of the design rather than a
violation of it (see `test_e2_budget_does_not_cover_privileged_operations`),
it is written as a demonstration that passes, and says so in its docstring,
rather than being quietly omitted.

INTERFACE NOTE (v2 refactor).  Three pieces of monitor state that these tests
used to read directly no longer exist in that shape, and the properties are
now expressed against what replaced them:

  * E5 anti-replay was `State.last_seq` / `State.last_nonce`, one slot per
    SOURCE.  It is now `State.replay`, a bounded table of
    `[(source, target), seq, nonce]` with REPLAY_SLOTS entries, because a
    counter belongs to a protocol ASSOCIATION.  Freshness is therefore
    asserted per (source, target) pair, and the table's fail-closed overflow
    is a property in its own right (`test_e5_*_overflow_fails_closed`).
  * I3 was a single boolean `State.latched`.  It is now `State.latched`, a
    LATCH_SLOTS-entry per-target table read through `is_latched`; a latch on
    one target must not gate another, and overflow fails closed.
  * A breaker-open from a console is reclassified by `effective_kind` into
    the SWITCH kind (PROTECTIVE_SOURCES = (AI, BASELINE)), so "granted TRIP
    implies physics" is now asserted on the EFFECTIVE kind, and the
    operational-switching path gets its own section.
"""

import math
import os
import sys

from hypothesis import HealthCheck, assume, given, settings
from hypothesis import strategies as st

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from gs import monitor as M  # noqa: E402

MANY = settings(max_examples=300, deadline=None,
                suppress_health_check=[HealthCheck.too_slow])
LOTS = settings(max_examples=120, deadline=None,
                suppress_health_check=[HealthCheck.too_slow])


# Channel provenance went FAIL-CLOSED: a Report that says nothing about its
# local addend or its observation channel is refused, because the monitor
# cannot tell "verified" from "nobody told me".  Deterministic tests that are
# about some OTHER invariant therefore have to state provenance explicitly,
# or I1 pre-empts the guard actually under test.
AUTHENTIC = {"local_authentic": True, "local_fresh": True,
             "residual_authentic": True, "residual_fresh": True}


# --- strategies -------------------------------------------------------------

def hostile_floats():
    """Every float an attacker (or a broken engineering station) could send."""
    return st.one_of(
        st.floats(allow_nan=True, allow_infinity=True),
        st.floats(min_value=-1e12, max_value=1e12, allow_nan=False,
                  allow_infinity=False),
        st.sampled_from([0.0, -0.0, 1e-300, -1e-300, 1e308, -1e308,
                         M.SP_ABS_MIN, M.SP_ABS_MAX, 312.0, 688.0,
                         1064.0, 1410.0, 2.0]),
    )


def plausible_floats():
    return st.one_of(
        st.floats(min_value=-2000.0, max_value=2000.0, allow_nan=False,
                  allow_infinity=False),
        hostile_floats(),
    )


def provenance_bits():
    """True, False, or PROVENANCE_ABSENT -- a channel annotation is tri-state
    now, and absence is the case the fail-closed default exists for."""
    return st.sampled_from([True, False, M.PROVENANCE_ABSENT])


def sources():
    """Every source, plus out-of-range ones (E7) and BASELINE (I6)."""
    return st.one_of(st.integers(min_value=0, max_value=M.N_SOURCES - 1),
                     st.integers(min_value=-4, max_value=12))


def kinds():
    """Every kind, INCLUDING SWITCH, plus unrecognised ones."""
    return st.one_of(st.integers(min_value=0, max_value=M.SWITCH),
                     st.integers(min_value=-3, max_value=9))


def timestamps():
    """Deliberately NON-monotone, including the v1 Z3 counterexample shape."""
    return st.one_of(
        st.integers(min_value=-5000, max_value=5000),
        st.sampled_from([998, 0, 1000, 999, M.SENTINEL_MS, -10 ** 12, 10 ** 12]),
    )


def seqs():
    """Replayed, out-of-order, negative and enormous sequence counters."""
    return st.one_of(st.integers(min_value=-3, max_value=6),
                     st.integers(min_value=-10 ** 9, max_value=10 ** 9))


def nonces():
    """A small pool, so that reuse actually happens."""
    return st.sampled_from([0, 1, 2, 3, "a", "b", None, -1])


def params():
    # "breaker" is the first of monitor.TARGET_KEYS, so this is what drives
    # `target_key`: a small pool so the per-target latch and the per-
    # association replay table are genuinely exercised in both directions
    # (same target again, and a different target).
    return st.fixed_dictionaries({
        "breaker": st.sampled_from(["SS1-01", "SS1-02", "SS2-01"]),
        "target": plausible_floats(),
        "dt_ms": st.one_of(plausible_floats(),
                           st.sampled_from([0.0, -1.0, 1000.0, 100.0])),
        "req_p0": plausible_floats(),
        "req_k": plausible_floats(),
        "feasible": st.booleans(),
    })


class Step(object):
    """One submitted command plus the world it arrives in."""

    __slots__ = ("cmd", "report", "baseline_trip", "cert_ok", "reclose_auth",
                 "maint")

    def __init__(self, cmd, report, baseline_trip, cert_ok, reclose_auth,
                 maint):
        self.cmd, self.report = cmd, report
        self.baseline_trip, self.cert_ok = baseline_trip, cert_ok
        self.reclose_auth, self.maint = reclose_auth, maint


@st.composite
def steps(draw):
    cmd = M.Command(
        source=draw(sources()),
        kind=draw(kinds()),
        params=draw(params()),
        sig_valid=draw(st.booleans()),
        sig2_valid=draw(st.booleans()),
        identity=draw(st.sampled_from(["", "op", "eng-ws", "ai-plane"])),
        nonce=draw(nonces()),
        seq=draw(seqs()),
        attested=draw(st.booleans()),
        keyswitch=draw(st.booleans()))
    have_report = draw(st.booleans())
    if have_report:
        report = M.Report(
            t=draw(timestamps()),
            seq=draw(seqs()),
            sig_valid=draw(st.booleans()),
            i_diff=draw(plausible_floats()),
            i_restraint=draw(plausible_floats()),
            remote_ok=draw(st.booleans()),
            forward=draw(st.booleans()),
            time_quality_ok=draw(st.booleans()),
            process_value=draw(plausible_floats()),
            residual_sigma=draw(st.one_of(
                st.none(),
                st.floats(min_value=0.0, max_value=60.0),
                hostile_floats())),
            # `i_diff = |I_local + I_remote|` -- BOTH addends have provenance,
            # and so does the process observation channel.  Generated, never
            # defaulted: a harness that leaves these at their compatibility
            # default is not testing the guard.
            # ABSENT is drawn alongside True/False: "the stream said
            # nothing" is a third state and the guard must handle it.
            local_authentic=draw(provenance_bits()),
            local_fresh=draw(provenance_bits()),
            residual_authentic=draw(provenance_bits()),
            residual_fresh=draw(provenance_bits()))
    else:
        report = None
    return Step(cmd, report, draw(st.booleans()), draw(st.booleans()),
                draw(st.booleans()), draw(st.booleans()))


def traces(min_size=1, max_size=14):
    return st.lists(steps(), min_size=min_size, max_size=max_size)


# --- harness ----------------------------------------------------------------

def replay_snapshot(state):
    """The E5 table as {(source, target): (seq, nonce)}, plus whether the
    table still had a free slot.  Both matter: an association that is absent
    from a FULL table fails closed rather than reading as fresh."""
    table = {}
    free = False
    for slot in state.replay:
        if slot is None:
            free = True
        else:
            table[slot[0]] = (slot[1], slot[2])
    return table, free


class Run(object):
    """One submitted step and everything observable about its outcome."""

    __slots__ = ("step", "actuate", "src", "reason", "granted", "now",
                 "target", "eff_kind",
                 "pre_last_ms", "pre_replay", "pre_replay_free",
                 "pre_last_report_seq", "pre_mode", "pre_latched",
                 "pre_target_latched")


def play(trace, require_switch_custody=False):
    """Feed a trace to a fresh Monitor; return the list of Run records.

    The feasibility oracle and the maintenance-window predicate are driven
    from the generated data, so E3 and E4's window are exercised in both
    directions rather than being pinned to a constant.
    """
    box = {"maint": False}
    mon = M.Monitor(feasibility=lambda p: bool(p.get("feasible", False)),
                    maint_window=lambda _ms: box["maint"],
                    require_switch_custody=require_switch_custody)
    out = []
    for stp in trace:
        box["maint"] = stp.maint
        r = Run()
        r.step = stp
        r.target = M.target_key(stp.cmd.params)
        r.eff_kind = M.effective_kind(stp.cmd.source, stp.cmd.kind)
        r.pre_last_ms = mon.st.last_ms
        r.pre_replay, r.pre_replay_free = replay_snapshot(mon.st)
        r.pre_last_report_seq = mon.st.last_report_seq
        r.pre_mode = mon.st.mode
        r.pre_latched = list(mon.st.latched)
        r.pre_target_latched = M.is_latched(mon.st, r.target)
        r.now = (stp.report.t if stp.report is not None
                 else stp.cmd.params.get("t", 0))
        r.actuate, r.src, r.reason = mon.submit(
            stp.cmd, stp.report, stp.baseline_trip, stp.cert_ok,
            stp.reclose_auth)
        # `submit` prefixes the baseline OR at the output; the monitor's own
        # verdict is preserved after the pipe (I6 / PROOF 5.4).
        r.granted = (r.reason.split("|")[-1] == M.R_GRANT)
        out.append(r)
    return out, mon


# The kinds that spend the E2 budget, as `commit` defines it.  SWITCH is in
# the list: an operational open is an actuation and must be counted, or the
# Industroyer sweep would be free.
ACTUATION_KINDS = (M.TRIP, M.CLOSE, M.SETPOINT, M.SWITCH)


def clear_latches(mon):
    mon.st.latched = [None] * M.LATCH_SLOTS


# ==========================================================================
# E7 provenance / I6 baseline
# ==========================================================================

@given(traces())
@LOTS
def test_e7_unauthenticated_or_unknown_source_never_actuates(trace):
    """A grant implies a verifying signature, a named identity and a source
    inside the enumeration.  Nothing else may actuate at any privilege."""
    for r in play(trace)[0]:
        if r.granted:
            c = r.step.cmd
            assert c.sig_valid
            assert c.identity != ""
            assert 0 <= c.source < M.N_SOURCES
            assert c.source != M.BASELINE


@given(traces())
@LOTS
def test_baseline_source_is_never_mediated(trace):
    """I6, structural: a Command claiming source=BASELINE is refused with the
    dedicated reason, in either direction -- the monitor neither grants for
    baseline nor pretends to have decided on its behalf."""
    for r in play(trace)[0]:
        if r.step.cmd.source == M.BASELINE:
            assert not r.granted
            assert r.reason.split("|")[-1] == M.R_BASELINE_MEDIATED


@given(traces())
@LOTS
def test_baseline_protection_is_never_inhibited(trace):
    """I6: whatever the monitor decides, and whatever state it is in,
    conventional protection reaches the actuator."""
    for r in play(trace)[0]:
        if r.step.baseline_trip:
            assert r.actuate is True
            assert r.src == "baseline"


@given(traces())
@LOTS
def test_baseline_output_is_independent_of_monitor_state(trace):
    """The baseline OR does not depend on mode, latch, veto count or window:
    replaying the same trace with baseline_trip forced True actuates at every
    single step."""
    for stp in trace:
        stp.baseline_trip = True
    for r in play(trace)[0]:
        assert r.actuate is True


# ==========================================================================
# E6 monotone time
# ==========================================================================

@given(traces())
@LOTS
def test_e6_backwards_clock_is_refused(trace):
    """A timestamp strictly behind the last accepted one is refused.

    E7 provenance is deliberately consulted first -- an unrecognised source
    actuates nothing at any privilege level, and that ordering is part of the
    specification -- so the E6 reason is asserted only once provenance has
    passed.  What is asserted unconditionally is that a rewound clock NEVER
    grants: that is the precondition for both the v1 rate-limiter defeat and
    for making a replayed frame look fresh.

    The monitor absorbs backwards jitter up to CLOCK_SKEW_MS (a real
    near-simultaneous multi-substation burst arrives a few ms out of order),
    so the REASON is asserted beyond that tolerance; the no-grant half is
    unconditional, and holds because the window clock is monotone by
    construction -- a rewound stamp can never widen the budget."""
    for r in play(trace)[0]:
        if r.pre_last_ms != M.SENTINEL_MS and r.now < r.pre_last_ms:
            c = r.step.cmd
            provenance_ok = (c.sig_valid and c.identity != ""
                             and 0 <= c.source < M.N_SOURCES
                             and c.source != M.BASELINE
                             and 0 <= r.eff_kind <= M.SWITCH)
            if r.now < r.pre_last_ms - M.CLOCK_SKEW_MS:
                assert not r.granted
                if provenance_ok:
                    assert r.reason.split("|")[-1] == M.R_TIME_REGRESSION


@given(traces())
@LOTS
def test_a_rewound_clock_never_widens_the_rate_budget(trace):
    """E6, the structural half: `decide` sees a MONOTONE now_ms, so even the
    absorbed sub-skew jitter cannot buy budget.  Every granted actuation's
    logged time is >= the previous accepted time."""
    _runs, mon = play(trace)
    prev = M.SENTINEL_MS
    for entry in mon.log:
        assert entry.t >= prev or prev == M.SENTINEL_MS
        prev = max(prev, entry.t)


@given(traces())
@LOTS
def test_grant_implies_monotone_time_and_good_time_quality(trace):
    for r in play(trace)[0]:
        if r.granted:
            assert (r.pre_last_ms == M.SENTINEL_MS
                    or r.now >= r.pre_last_ms - M.CLOCK_SKEW_MS)
            assert r.step.report is not None
            assert r.step.report.time_quality_ok


# ==========================================================================
# E5 anti-replay -- now keyed per (source, target) association
# ==========================================================================

@given(traces())
@LOTS
def test_e5_grant_implies_strictly_fresh_sequence_and_nonce(trace):
    """A grant implies the command's counter strictly exceeds the last one
    accepted FOR THAT ASSOCIATION, and its nonce differs from that
    association's last accepted nonce.  An association absent from a FULL
    table cannot be granted at all (fail closed)."""
    for r in play(trace)[0]:
        if r.granted:
            c = r.step.cmd
            key = (c.source, r.target)
            slot = r.pre_replay.get(key)
            if slot is None:
                assert r.pre_replay_free, "granted on a full replay table"
            else:
                assert c.seq > slot[0]
                assert c.nonce != slot[1]


@given(traces())
@LOTS
def test_e5_a_stale_counter_on_the_same_association_is_refused(trace):
    """The converse: whenever an association is already known and the command
    does not strictly advance it, the command does not actuate."""
    for r in play(trace)[0]:
        c = r.step.cmd
        slot = r.pre_replay.get((c.source, r.target))
        if slot is not None and c.seq <= slot[0]:
            assert not r.granted


@given(traces())
@LOTS
def test_e5_stale_but_validly_signed_report_is_rejected(trace):
    """THE Stuxnet 21-second replay control: a report whose sequence counter
    is not strictly greater than the last accepted one is refused even though
    its signature verifies."""
    for r in play(trace)[0]:
        rep = r.step.report
        if rep is not None and rep.sig_valid and rep.seq <= r.pre_last_report_seq:
            assert not r.granted
        if r.granted:
            assert rep is not None and rep.sig_valid
            assert rep.seq > r.pre_last_report_seq


def test_e5_replayed_report_is_refused_even_with_a_valid_signature():
    """Deterministic regression of the headline claim, stated as an example
    so it is readable next to the property above."""
    mon = M.Monitor(feasibility=lambda p: True)
    rep = M.Report(t=400, seq=5, sig_valid=True, i_diff=2.5, i_restraint=1.0, **AUTHENTIC)
    cmd = M.Command(M.AI, M.TRIP, {}, sig_valid=True, identity="ai",
                    nonce="a", seq=1)
    assert mon.submit(cmd, rep)[0] is True
    mon.st.latched = False              # v1 compatibility shim: clear all
    replay = M.Report(t=401, seq=5, sig_valid=True, i_diff=2.5,
                      i_restraint=1.0, **AUTHENTIC)          # byte-identical, still valid
    cmd2 = M.Command(M.AI, M.TRIP, {}, sig_valid=True, identity="ai",
                     nonce="b", seq=2)
    actuate, _src, reason = mon.submit(cmd2, replay)
    assert actuate is False
    assert reason == M.R_REPORT_STALE


def _switch_cmd(target, seq, nonce, src=M.SCADA):
    return M.Command(src, M.TRIP,
                     {"breaker": target, "feasible": True},
                     sig_valid=True, identity="op", nonce=nonce, seq=seq)


def _quiet_report(t, seq):
    """A report with no fault on the line: enough for an operational SWITCH,
    never enough for a protective TRIP."""
    return M.Report(t=t, seq=seq, sig_valid=True, i_diff=0.01,
                    i_restraint=1.0, remote_ok=True, forward=True,
                    time_quality_ok=True, **AUTHENTIC)


def test_e5_replayed_sequence_on_the_same_association_is_refused():
    """NEW in the per-association refactor: the same counter, re-presented to
    the SAME (source, target), is a replay and is refused by name."""
    mon = M.Monitor(feasibility=lambda p: True)
    ok, _s, why = mon.submit(_switch_cmd("SS1-01", 7, "n1"),
                             _quiet_report(1000, 1))
    assert ok is True and why == M.R_GRANT
    ok2, _s2, why2 = mon.submit(_switch_cmd("SS1-01", 7, "n2"),
                                _quiet_report(2000, 2))
    assert ok2 is False and why2 == M.R_REPLAY_SEQ
    # and a strictly lower one likewise
    ok3, _s3, why3 = mon.submit(_switch_cmd("SS1-01", 3, "n3"),
                                _quiet_report(3000, 3))
    assert ok3 is False and why3 == M.R_REPLAY_SEQ


def test_e5_same_sequence_on_a_different_target_is_accepted():
    """The bug the refactor fixed, pinned: Industroyer2's exact shape is one
    command per device with `sequence=1` to each.  A counter belongs to a
    protocol association, so seq=1 to SS1-02 is NOT a replay of seq=1 to
    SS1-01, and refusing it was both wrong and a denial of service."""
    mon = M.Monitor(feasibility=lambda p: True)
    assert mon.submit(_switch_cmd("SS1-01", 1, "a"),
                      _quiet_report(1000, 1))[0] is True
    ok, _s, why = mon.submit(_switch_cmd("SS1-02", 1, "b"),
                             _quiet_report(2000, 2))
    assert ok is True and why == M.R_GRANT
    # ... and the same counter from a DIFFERENT SOURCE to the same target is
    # a different association too.
    ok2, _s2, why2 = mon.submit(_switch_cmd("SS1-01", 1, "c", src=M.HMI),
                                _quiet_report(3000, 3))
    assert ok2 is True and why2 == M.R_GRANT


def test_e5_nonce_reuse_on_the_same_association_is_refused_by_name():
    mon = M.Monitor(feasibility=lambda p: True)
    assert mon.submit(_switch_cmd("SS1-01", 1, "same-nonce"),
                      _quiet_report(1000, 1))[0] is True
    ok, _s, why = mon.submit(_switch_cmd("SS1-01", 2, "same-nonce"),
                             _quiet_report(2000, 2))
    assert ok is False and why == M.R_REPLAY_NONCE


def test_e5_replay_table_overflow_fails_closed():
    """The table is bounded (REPLAY_SLOTS) so the state stays finite.  Once
    it is full, an association that is NOT in it is treated as stale rather
    than silently trusted: unknown history is not evidence of freshness."""
    mon = M.Monitor(feasibility=lambda p: True)
    # Operational switching does not latch, so LATCH_SLOTS does not
    # interfere; 1000 ms apart keeps the E2 budget out of the way.
    for i in range(M.REPLAY_SLOTS):
        ok, _s, why = mon.submit(_switch_cmd("BKR-%02d" % i, 1, ("n", i)),
                                 _quiet_report(1000 * (i + 1), i + 1))
        assert ok is True, (i, why)
    assert all(slot is not None for slot in mon.st.replay)
    n = M.REPLAY_SLOTS
    ok, _s, why = mon.submit(_switch_cmd("BKR-OVERFLOW", 1, ("n", n)),
                             _quiet_report(1000 * (n + 1), n + 1))
    assert ok is False and why == M.R_REPLAY_SEQ
    # A known association still advances normally: overflow denies the
    # unknown, it does not brick the table.
    ok2, _s2, why2 = mon.submit(_switch_cmd("BKR-00", 2, ("n2", 0)),
                                _quiet_report(1000 * (n + 2), n + 2))
    assert ok2 is True and why2 == M.R_GRANT


@given(traces())
@LOTS
def test_e5_table_stays_bounded_and_keys_are_associations(trace):
    _runs, mon = play(trace)
    assert len(mon.st.replay) == M.REPLAY_SLOTS
    keys = [slot[0] for slot in mon.st.replay if slot is not None]
    assert len(keys) == len(set(keys))          # one slot per association
    for src, tgt in keys:
        assert 0 <= src < M.N_SOURCES
        assert isinstance(tgt, str)


# ==========================================================================
# E2 cross-source rate limit
# ==========================================================================

@given(traces())
@MANY
def test_e2_rate_limit_holds_across_all_sources_combined(trace):
    """E2: at most MAX_GRANTS actuations in any half-open WINDOW_MS window,
    counted in AGGREGATE -- switching channel (AI -> SCADA -> HMI) or target
    (SS1-01 -> SS2-01) must buy no fresh budget.  This is the property the v1
    shield failed (PROOF 5.2), and it is the PRIMARY control on the
    Industroyer path now that operational switching is not asked for physics.
    """
    ts = [r.now for r in play(trace)[0]
          if r.granted and r.eff_kind in ACTUATION_KINDS]
    for t0 in ts:
        n = sum(1 for t in ts if t0 <= t < t0 + M.WINDOW_MS)
        assert n <= M.MAX_GRANTS, (t0, sorted(ts))


def test_e2_is_not_defeated_by_source_hopping():
    """Deterministic: six trips in 350 ms, a different source each time, each
    with its own fresh per-association counters."""
    mon = M.Monitor(feasibility=lambda p: True)
    granted = 0
    for i, src in enumerate([M.AI, M.SCADA, M.HMI, M.AI, M.SCADA, M.HMI]):
        rep = M.Report(t=100 + i * 50, seq=i + 1, i_diff=2.5, i_restraint=1.0, **AUTHENTIC)
        cmd = M.Command(src, M.TRIP, {}, sig_valid=True, identity="x",
                        nonce=i, seq=i + 1)
        if mon.submit(cmd, rep)[0]:
            granted += 1
        clear_latches(mon)              # give the attacker I3 for free
    assert granted <= M.MAX_GRANTS


def test_e2_is_not_defeated_by_target_hopping():
    """INDUSTROYER2's shape: one command per device, so no per-device counter
    and no per-target latch ever fires.  The budget is global across every
    source AND every target, which is the only thing that bounds the sweep on
    the operational path."""
    mon = M.Monitor(feasibility=lambda p: True)
    granted = 0
    for i in range(10):
        cmd = _switch_cmd("SS%d-01" % i, 1, ("m", i),
                          src=M.SCADA if i % 2 else M.HMI)
        if mon.submit(cmd, _quiet_report(100 + i * 20, i + 1))[0]:
            granted += 1
    assert granted <= M.MAX_GRANTS


def test_e2_is_not_defeated_by_the_v1_z3_counterexample():
    """t = 998, 0, 1000, 999 gave THREE grants in one window against v1."""
    mon = M.Monitor(feasibility=lambda p: True)
    ts = []
    for i, t in enumerate([998, 0, 1000, 999]):
        rep = M.Report(t=t, seq=i + 1, i_diff=2.5, i_restraint=1.0, **AUTHENTIC)
        cmd = M.Command(M.AI, M.TRIP, {}, sig_valid=True, identity="ai",
                        nonce=i, seq=i + 1)
        if mon.submit(cmd, rep)[0]:
            ts.append(t)
        clear_latches(mon)
    for t0 in ts:
        assert sum(1 for t in ts if t0 <= t < t0 + M.WINDOW_MS) <= M.MAX_GRANTS


def test_e2_budget_does_not_cover_privileged_operations():
    """DOCUMENTED LIMIT, not a violation: `decide` returns for SETTINGS_CHANGE
    and LOGIC_DOWNLOAD *before* `rate_ok` is consulted, and `commit` only
    slides the window for TRIP/CLOSE/SETPOINT/SWITCH.  So a fully-authorised
    privileged op is outside the E2 budget by construction: E4 is the only
    thing gating it.  gs/attacks.py's E2 text says "privileged actuations",
    which reads wider than what the code enforces; this test pins the actual
    behaviour so the gap is visible rather than assumed away."""
    mon = M.Monitor(feasibility=lambda p: True, maint_window=lambda _ms: True)
    n = 0
    for i in range(5):
        cmd = M.Command(M.ENGINEERING, M.LOGIC_DOWNLOAD, {}, sig_valid=True,
                        sig2_valid=True, attested=True, keyswitch=True,
                        identity="eng-ws", nonce=i, seq=i + 1)
        if mon.submit(cmd, M.Report(t=100 + i, seq=i + 1, **AUTHENTIC))[0]:
            n += 1
    assert n == 5                       # all five, inside one 1000 ms window
    assert mon.st.win == [M.SENTINEL_MS] * M.MAX_GRANTS


# ==========================================================================
# E1 process envelope
# ==========================================================================

@given(traces())
@MANY
def test_e1_granted_setpoint_is_inside_the_envelope(trace):
    """Every granted SETPOINT satisfies the absolute band, the rate bound and
    the critical-band clearance, computed against the process value the
    monitor actually had in front of it."""
    for r in play(trace)[0]:
        if r.granted and r.eff_kind == M.SETPOINT:
            p = r.step.cmd.params
            target = p.get("target", float("nan"))
            current = r.step.report.process_value
            dt = p.get("dt_ms", 0.0)
            assert M.setpoint_abs_ok(target)
            assert M.SP_ABS_MIN <= target <= M.SP_ABS_MAX
            assert not math.isnan(target)
            assert M.setpoint_rate_ok(target, current, dt)
            assert M.setpoint_band_clear(target, current)
            lo = min(current, target)
            hi = max(current, target)
            for c, hw, _sev in M.RESONANCES:
                assert hi < c - hw or lo > c + hw
            # I1': an independently-keyed residual must corroborate the
            # REPORTED speed the envelope was computed against.
            assert M.process_corroborated(r.step.report.residual_sigma)
            # PROVENANCE BEFORE VALUE: the residual is only as trustworthy as
            # the channel it was computed from.
            assert r.step.report.residual_authentic
            assert r.step.report.residual_fresh


@given(plausible_floats())
@MANY
def test_e1_absolute_band_fails_closed_on_absurd_targets(target):
    ok = M.setpoint_abs_ok(target)
    if math.isnan(target):
        assert not ok
    if ok:
        assert M.SP_ABS_MIN <= target <= M.SP_ABS_MAX
    assert not M.setpoint_abs_ok(float("nan"))
    assert not M.setpoint_abs_ok(float("inf"))
    assert not M.setpoint_abs_ok(float("-inf"))


@given(plausible_floats(), plausible_floats(), plausible_floats())
@MANY
def test_e1_rate_bound_fails_closed_on_zero_or_negative_dt(target, current, dt):
    """A step with no elapsed time is an unbounded ramp: it must never pass."""
    if not (dt > 0.0):
        assert not M.setpoint_rate_ok(target, current, dt)
    if M.setpoint_rate_ok(target, current, dt):
        assert dt > 0.0
        assert abs(target - current) * 1000.0 <= M.SP_MAX_RATE * dt + 1e-6


@given(plausible_floats(), plausible_floats())
@MANY
def test_e1_critical_band_check_covers_transit_not_only_dwell(target, current):
    clear = M.setpoint_band_clear(target, current)
    if clear:
        lo, hi = min(current, target), max(current, target)
        for c, hw, _sev in M.RESONANCES:
            assert hi < c - hw or lo > c + hw
    # symmetry: the interval is the same whichever end you start from
    assert clear == M.setpoint_band_clear(current, target)
    assert not M.setpoint_band_clear(float("nan"), current)


def test_e1_bands_are_the_plant_s_own_critical_speeds():
    """No local copy of the envelope: the monitor's bands and slew limit ARE
    the plant's commissioning data, so the two cannot drift apart."""
    from gs import plant_drive as _p
    assert M.RESONANCES == _p.RESONANCES
    assert (M.SP_ABS_MIN, M.SP_ABS_MAX) == (_p.F_BAND_LO, _p.F_BAND_HI)
    assert M.SP_MAX_RATE == _p.ACCEL_MAX
    # the payload's descent to 2 Hz must cross both modes
    assert not M.setpoint_band_clear(2.0, _p.F_NOM)


@given(st.one_of(st.none(), plausible_floats()))
@MANY
def test_i1p_residual_gate_fails_closed(sigma):
    """An absent, non-finite or oversized residual is NOT corroboration."""
    ok = M.process_corroborated(sigma)
    if sigma is None or not math.isfinite(sigma):
        assert not ok
    if ok:
        assert sigma <= M.RESIDUAL_MAX_SIGMA


def test_i1p_replayed_report_cannot_buy_an_out_of_envelope_setpoint():
    """The replay makes every envelope check pass against a lie; the
    independently-keyed residual is what refuses it."""
    mon = M.Monitor(feasibility=lambda p: True)
    rep = M.Report(t=100, seq=1, process_value=1064.0, residual_sigma=28.0, **AUTHENTIC)
    cmd = M.Command(M.ENGINEERING, M.SETPOINT,
                    {"target": 1080.0, "dt_ms": 1000.0}, sig_valid=True,
                    identity="eng-ws", nonce="n", seq=1)
    actuate, _s, reason = mon.submit(cmd, rep)
    assert actuate is False and reason == M.R_PROCESS_RESIDUAL


# ==========================================================================
# E4 privileged-operation mediation
# ==========================================================================

@given(traces())
@MANY
def test_e4_privileged_ops_need_every_factor(trace):
    """SETTINGS_CHANGE / LOGIC_DOWNLOAD are refused unless dual signature AND
    attestation AND the physical key switch AND the maintenance window are
    all present, in NORMAL mode.  A compromised engineering workstation has
    the credentials; it does not have the key switch."""
    for r in play(trace)[0]:
        if r.granted and r.eff_kind in M.PRIVILEGED:
            c = r.step.cmd
            assert c.sig_valid and c.sig2_valid       # dual signature
            assert c.attested                         # attestation
            assert c.keyswitch                        # physical key switch
            assert r.step.maint                       # maintenance window
            assert r.pre_mode == M.NORMAL


@given(st.booleans(), st.booleans(), st.booleans(), st.booleans())
@MANY
def test_e4_every_missing_factor_blocks_and_is_named(dual, att, key, win):
    """Each missing factor produces its OWN veto reason: the veto spectrum is
    the detection signal, so collapsing causes would destroy it."""
    mon = M.Monitor(feasibility=lambda p: True, maint_window=lambda _ms: win)
    cmd = M.Command(M.ENGINEERING, M.LOGIC_DOWNLOAD, {}, sig_valid=True,
                    sig2_valid=dual, attested=att, keyswitch=key,
                    identity="eng-ws", nonce="n", seq=1)
    actuate, _src, reason = mon.submit(cmd, M.Report(t=10, seq=1, **AUTHENTIC))
    if dual and att and key and win:
        assert actuate is True and reason == M.R_GRANT
    else:
        assert actuate is False
        expected = (M.R_PRIV_DUAL_SIG if not dual else
                    M.R_PRIV_ATTEST if not att else
                    M.R_PRIV_KEYSWITCH if not key else M.R_PRIV_WINDOW)
        assert reason == expected


def test_e4_stuxnet_logic_download_needs_the_key_switch():
    """The whole point of E4: valid dual signature, valid attestation, inside
    the window, and it still does not actuate without the panel key."""
    mon = M.Monitor(feasibility=lambda p: True, maint_window=lambda _ms: True)
    cmd = M.Command(M.ENGINEERING, M.LOGIC_DOWNLOAD,
                    {"cert_subject": "Realtek Semiconductor Corp"},
                    sig_valid=True, sig2_valid=True, attested=True,
                    keyswitch=False, identity="eng-ws", nonce="n", seq=1)
    actuate, _s, reason = mon.submit(cmd, M.Report(t=10, seq=1, **AUTHENTIC))
    assert actuate is False and reason == M.R_PRIV_KEYSWITCH


# ==========================================================================
# PROTECTIVE TRIP vs OPERATIONAL SWITCH -- the source-drawn split
# ==========================================================================

@given(sources(), kinds())
@MANY
def test_effective_kind_reclassifies_only_console_trips(source, kind):
    """The split is drawn on the AUTHENTICATED SOURCE, never on a params flag
    (a flag like "maintenance": true is attacker-supplied and would be forged
    immediately).  Nothing but a TRIP is ever reclassified."""
    eff = M.effective_kind(source, kind)
    if kind != M.TRIP:
        assert eff == kind
    elif source in M.PROTECTIVE_SOURCES:
        assert eff == M.TRIP
    else:
        assert eff == M.SWITCH
    assert M.PROTECTIVE_SOURCES == (M.AI, M.BASELINE)


@given(traces())
@LOTS
def test_a_params_flag_can_never_buy_the_protective_path(trace):
    """The corollary that matters for the threat model: a granted PROTECTIVE
    trip always came from a protective source, whatever the params claim."""
    for r in play(trace)[0]:
        if r.granted and r.eff_kind == M.TRIP:
            assert r.step.cmd.source in M.PROTECTIVE_SOURCES


def test_console_open_is_operational_switching_not_a_physics_free_trip():
    """A console-sourced open with NO fault on the line is granted -- it is
    byte-identical to an authorised maintenance open, and demanding fault
    corroboration for it is a category error that would remove the monitor
    from service in week one.  The SAME command from the automatic plane is
    a protective trip and IS refused for want of physics."""
    mon = M.Monitor(feasibility=lambda p: True)
    ok, _s, why = mon.submit(_switch_cmd("SS1-01", 1, "a"),
                             _quiet_report(1000, 1))
    assert ok is True and why == M.R_GRANT
    assert mon.log[-1].kind == M.SWITCH         # logged as what it was

    ai = M.Monitor(feasibility=lambda p: True)
    cmd = M.Command(M.AI, M.TRIP, {"breaker": "SS1-01"}, sig_valid=True,
                    identity="ai-plane", nonce="a", seq=1)
    ok2, _s2, why2 = ai.submit(cmd, _quiet_report(1000, 1))
    assert ok2 is False and why2 == M.R_PHYSICS
    assert ai.log[-1].kind == M.TRIP


def test_operational_switch_still_faces_provenance_freshness_time_e2_e3():
    """The split widens the attack surface and is NOT allowed to widen it any
    further than stated: everything upstream of I1 still applies to SWITCH."""
    # E7 provenance: unsigned.
    mon = M.Monitor(feasibility=lambda p: True)
    bad = M.Command(M.SCADA, M.TRIP, {"breaker": "B"}, sig_valid=False,
                    identity="op", nonce="a", seq=1)
    assert mon.submit(bad, _quiet_report(1000, 1))[2] == M.R_PROVENANCE
    # ... and an empty identity is equally unauthenticated.
    anon = M.Command(M.SCADA, M.TRIP, {"breaker": "B"}, sig_valid=True,
                     identity="", nonce="a", seq=1)
    assert mon.submit(anon, _quiet_report(1001, 2))[2] == M.R_PROVENANCE

    # E5 freshness on the switch path.
    m2 = M.Monitor(feasibility=lambda p: True)
    assert m2.submit(_switch_cmd("B", 5, "a"), _quiet_report(1000, 1))[0]
    assert m2.submit(_switch_cmd("B", 5, "b"),
                     _quiet_report(2000, 2))[2] == M.R_REPLAY_SEQ
    # replayed REPORT under a fresh command counter, too
    assert m2.submit(_switch_cmd("B", 6, "c"),
                     _quiet_report(3000, 1))[2] == M.R_REPORT_STALE

    # E6 monotone time.
    m3 = M.Monitor(feasibility=lambda p: True)
    assert m3.submit(_switch_cmd("B", 1, "a"), _quiet_report(5000, 1))[0]
    assert m3.submit(_switch_cmd("B", 2, "b"),
                     _quiet_report(0, 2))[2] == M.R_TIME_REGRESSION
    # I4 time-source integrity.
    m3b = M.Monitor(feasibility=lambda p: True)
    rep = _quiet_report(1000, 1)
    rep.time_quality_ok = False
    assert m3b.submit(_switch_cmd("B", 1, "a"), rep)[2] == M.R_TIME

    # E2 aggregate budget: the third open in one window.
    m4 = M.Monitor(feasibility=lambda p: True)
    assert m4.submit(_switch_cmd("B1", 1, "a"), _quiet_report(100, 1))[0]
    assert m4.submit(_switch_cmd("B2", 1, "b"), _quiet_report(200, 2))[0]
    assert m4.submit(_switch_cmd("B3", 1, "c"),
                     _quiet_report(300, 3))[2] == M.R_RATE

    # E3 feasibility: the remaining island would not survive.
    m5 = M.Monitor(feasibility=lambda p: False)
    assert m5.submit(_switch_cmd("B", 1, "a"),
                     _quiet_report(1000, 1))[2] == M.R_INFEASIBLE


def test_e3_target_specificity_on_the_operational_path():
    """`corroboration_on_target`: a disturbance that is not on the commanded
    element is not a reason to open it.  This is the ONE piece of element-
    awareness E3 has, and on the operational path there is no directional
    element to fall back on."""
    assert M.corroboration_on_target(False, False) is True
    assert M.corroboration_on_target(True, False) is False
    assert M.corroboration_on_target(True, True) is True
    mon = M.Monitor(feasibility=lambda p: True)
    rep = M.Report(t=1000, seq=1, sig_valid=True, i_diff=2.5,
                   i_restraint=1.0, remote_ok=True, forward=False,
                   time_quality_ok=True, **AUTHENTIC)       # big disturbance, NOT here
    assert mon.submit(_switch_cmd("SS9-01", 1, "a"),
                      rep)[2] == M.R_INFEASIBLE


def test_switch_custody_is_opt_in_and_named():
    """E4-lite for operational switching: OFF by default (turning it on
    refuses every legitimate maintenance open whose second factor is not
    wired through this interface), and when on it produces its own reason."""
    off = M.Monitor(feasibility=lambda p: True)
    assert off.submit(_switch_cmd("B", 1, "a"), _quiet_report(1000, 1))[0]

    on = M.Monitor(feasibility=lambda p: True, require_switch_custody=True)
    assert on.submit(_switch_cmd("B", 1, "a"),
                     _quiet_report(1000, 1))[2] == M.R_SWITCH_CUSTODY
    dual = M.Command(M.SCADA, M.TRIP, {"breaker": "B"}, sig_valid=True,
                     sig2_valid=True, attested=True, identity="op",
                     nonce="b", seq=2)
    assert on.submit(dual, _quiet_report(2000, 2))[0] is True


@given(traces())
@LOTS
def test_granted_switch_never_needs_physics_but_always_needs_e3(trace):
    """The exact shape of the widened surface, asserted rather than assumed:
    a granted SWITCH/CLOSE implies feasibility and custody, and implies
    nothing at all about the differential."""
    for r in play(trace, require_switch_custody=True)[0]:
        if r.granted and r.eff_kind in (M.SWITCH, M.CLOSE):
            c = r.step.cmd
            assert c.params.get("feasible", False)
            if r.eff_kind == M.SWITCH:
                assert c.sig2_valid and c.attested


# ==========================================================================
# I1 / I3 / I7 -- carried-over invariants, re-tested on the wider record
# ==========================================================================

@given(plausible_floats(), plausible_floats(), st.booleans(),
       plausible_floats(), plausible_floats())
@MANY
def test_differential_fails_closed_on_non_finite_inputs(i_diff, i_rest, cert,
                                                        p0, k):
    """Explicitly, not by IEEE-754 accident: a NaN measurement or a NaN/inf
    requested setting must never read as a fault."""
    ok = M.differential_ok(i_diff, i_rest, cert, p0, k)
    if not (math.isfinite(i_diff) and math.isfinite(i_rest)):
        assert not ok
    if ok:
        p0_floor, k_floor = M.thresholds(cert)
        rest = max(i_rest, 0.0)
        assert i_diff > max(p0_floor, k_floor * rest) - 1e-12


@given(traces())
@LOTS
def test_i1_granted_trip_implies_full_physics_corroboration(trace):
    """I1 on the PROTECTIVE path, which is the only path it governs."""
    for r in play(trace)[0]:
        if r.granted and r.eff_kind == M.TRIP:
            rep = r.step.report
            assert rep is not None
            assert rep.remote_ok and rep.forward
            # BOTH ENDS.  Authenticating only the remote addend leaves the
            # sum |I_local + I_remote| under an adversary who owns the local
            # channel: a paced forger won 25/25 before this guard existed,
            # and Z3 theorem DW5 proves no dwell length rejects it.
            assert rep.local_authentic and rep.local_fresh
            assert M.differential_ok(
                rep.i_diff, rep.i_restraint,
                r.step.cert_ok and r.pre_mode == M.NORMAL,
                r.step.cmd.params.get("req_p0", M.P0_MIN),
                r.step.cmd.params.get("req_k", M.K_MIN))
            assert r.step.cmd.params.get("feasible", False)


@given(traces())
@LOTS
def test_i3_latch_holds_until_reclose_authorisation(trace):
    """I3, now PER-TARGET: a latched target refuses a further protective trip
    until a reclose authorisation (or an authorised close/switch) clears it."""
    for r in play(trace)[0]:
        if r.pre_target_latched and r.eff_kind == M.TRIP:
            assert not r.granted


@given(traces())
@LOTS
def test_i3_only_a_protective_trip_latches_and_only_its_own_target(trace):
    """`commit`: a granted protective TRIP latches its own target and nothing
    else; an operational switch does not latch at all (anti-pump on an
    operational reclose is E3's dead-time check, not a latch)."""
    runs, _mon = play(trace)
    for r in runs:
        newly = [t for t in _post(r) if t not in r.pre_latched]
        if newly:
            assert r.granted and r.eff_kind == M.TRIP
            assert newly == [r.target]


def _post(r):
    """The latch table AFTER the step -- reconstructed from what `commit`
    promises, so the assertion above is checked against the spec rather than
    against a copy of the implementation."""
    tbl = list(r.pre_latched)
    if r.granted and r.eff_kind == M.TRIP and r.target not in tbl:
        for i, slot in enumerate(tbl):
            if slot is None:
                tbl[i] = r.target
                break
    return [t for t in tbl if t is not None]


def test_i3_a_latch_on_one_target_does_not_gate_another():
    """The bug the per-target refactor fixed, pinned: a global latch meant a
    latch on breaker A silently supplied the security for breaker B -- and
    made the E2 budget unreachable dead code for breaker traffic, so six
    catalogue attacks credited to E2 were really being stopped by I1."""
    faulted = lambda t, s: M.Report(t=t, seq=s, sig_valid=True, i_diff=2.5,
                                    i_restraint=1.0, remote_ok=True,
                                    forward=True, time_quality_ok=True, **AUTHENTIC)
    mon = M.Monitor(feasibility=lambda p: True)
    trip = lambda tgt, s, n: M.Command(
        M.AI, M.TRIP, {"breaker": tgt}, sig_valid=True, identity="ai-plane",
        nonce=n, seq=s)
    assert mon.submit(trip("A", 1, "a"), faulted(1000, 1))[0] is True
    assert M.is_latched(mon.st, "A")
    assert not M.is_latched(mon.st, "B")
    # same target again -> latched
    assert mon.submit(trip("A", 2, "b"),
                      faulted(2000, 2))[2] == M.R_LATCHED
    # a DIFFERENT target is not gated by A's latch
    ok, _s, why = mon.submit(trip("B", 1, "c"), faulted(3000, 3))
    assert ok is True and why == M.R_GRANT
    # and a reclose authorisation clears only the target it names
    mon.submit(trip("A", 3, "d"), faulted(4000, 4), reclose_auth=True)
    assert not M.is_latched(mon.st, "A")


def test_i3_latch_table_overflow_fails_closed():
    """Bounded table (LATCH_SLOTS).  An unknown target in a FULL table reads
    as LATCHED: unknown history is not permission."""
    faulted = lambda t, s: M.Report(t=t, seq=s, sig_valid=True, i_diff=2.5,
                                    i_restraint=1.0, remote_ok=True,
                                    forward=True, time_quality_ok=True, **AUTHENTIC)
    mon = M.Monitor(feasibility=lambda p: True)
    for i in range(M.LATCH_SLOTS):
        cmd = M.Command(M.AI, M.TRIP, {"breaker": "L%02d" % i},
                        sig_valid=True, identity="ai-plane",
                        nonce=("n", i), seq=1)
        ok, _s, why = mon.submit(cmd, faulted(1000 * (i + 1), i + 1))
        assert ok is True, (i, why)
    assert all(slot is not None for slot in mon.st.latched)
    n = M.LATCH_SLOTS
    over = M.Command(M.AI, M.TRIP, {"breaker": "L-OVERFLOW"}, sig_valid=True,
                     identity="ai-plane", nonce=("n", n), seq=1)
    ok, _s, why = mon.submit(over, faulted(1000 * (n + 1), n + 1))
    assert ok is False and why == M.R_LATCHED


def test_latched_is_the_v1_compatibility_shim_too():
    """`st.latched = False` is v1's whole latch state; the shim honours it as
    "clear every latch" and normalises back to the per-target table."""
    mon = M.Monitor(feasibility=lambda p: True)
    M.latch_set(mon.st, "A")
    assert M.is_latched(mon.st, "A")
    mon.st.latched = False
    assert not M.is_latched(mon.st, "A")
    assert len(mon.st.latched) == M.LATCH_SLOTS


@given(traces())
@LOTS
def test_i7_no_grant_once_disowned(trace):
    for r in play(trace)[0]:
        if r.pre_mode == M.BASELINE_ONLY:
            assert not r.granted


@given(traces())
@LOTS
def test_i7_mode_escalation_is_monotone(trace):
    runs, _mon = play(trace)
    prev = M.NORMAL
    for r in runs:
        assert r.pre_mode >= prev
        prev = r.pre_mode


@given(traces())
@LOTS
def test_i7_restricted_has_teeth(trace):
    """RESTRICTED is not indistinguishable from NORMAL (v1's PROOF 5.1): a
    distrusted source loses privileged operations outright, and loses
    adaptive sensitivity, before it loses protection."""
    for r in play(trace)[0]:
        if r.pre_mode == M.RESTRICTED and r.eff_kind in M.PRIVILEGED:
            assert not r.granted
            c = r.step.cmd
            if (c.sig_valid and c.identity != ""
                    and 0 <= c.source < M.N_SOURCES
                    and c.source != M.BASELINE):
                assert r.reason.split("|")[-1] in (
                    M.R_TIME_REGRESSION, M.R_TIME, M.R_REPLAY_SEQ,
                    M.R_REPLAY_NONCE, M.R_REPORT_STALE, M.R_PRIV_RESTRICTED)


# ==========================================================================
# Robustness: absurd input must veto, never crash
# ==========================================================================

@given(traces())
@MANY
def test_absurd_input_never_raises_and_never_silently_actuates(trace):
    runs, mon = play(trace)
    for r in runs:
        assert isinstance(r.reason, str) and r.reason != ""
        if not r.step.baseline_trip:
            assert r.actuate == r.granted
    assert len(mon.st.win) == M.MAX_GRANTS
    assert len(mon.st.replay) == M.REPLAY_SLOTS
    assert len(mon.st.latched) == M.LATCH_SLOTS


@given(traces())
@LOTS
def test_state_stays_bounded_and_copyable(trace):
    """The whole point of the fixed-capacity tables: the state is finite, so
    `decide` stays enumerable."""
    _runs, mon = play(trace)
    snap = mon.st.copy()
    assert len(snap.replay) == M.REPLAY_SLOTS
    assert len(snap.latched) == M.LATCH_SLOTS
    assert snap.key() == mon.st.key()
    assert 0 <= mon.st.vetoes <= M.VETO_LIMIT
    # copy is deep enough that mutating the copy cannot reach the original
    for slot in snap.replay:
        if slot is not None:
            slot[1] = 10 ** 12
    assert all(s is None or s[1] != 10 ** 12 for s in mon.st.replay)


@given(traces())
@LOTS
def test_the_monitor_is_not_a_brick(trace):
    """TRANSPARENCY counterweight: a well-formed, fully corroborated, in-band
    command IS granted after any prefix that has not disowned the source.

    The two bounded tables introduce two new ways to be a brick, so both are
    assumed away explicitly rather than silently: an unknown target in a full
    latch table reads as latched, and an unknown association in a full replay
    table reads as stale.  Those are deliberate fail-closed behaviours, tested
    in their own right above."""
    runs, mon = play(trace)
    tgt = "FRESH-TARGET-XYZ"
    assume(mon.st.mode == M.NORMAL)
    assume(not M.is_latched(mon.st, tgt))
    assume(M.replay_fresh(mon.st, (M.SCADA, tgt), 10 ** 9, "fresh-nonce-xyz")
           == (True, True))
    t = max(mon.st.last_ms, 0) + 10 * M.WINDOW_MS
    rep = M.Report(t=t, seq=mon.st.last_report_seq + 1, sig_valid=True,
                   i_diff=50.0, i_restraint=0.0, remote_ok=True,
                   forward=True, time_quality_ok=True, process_value=1064.0, **AUTHENTIC)
    cmd = M.Command(M.SCADA, M.TRIP, {"breaker": tgt, "feasible": True},
                    sig_valid=True, identity="op", nonce="fresh-nonce-xyz",
                    seq=10 ** 9)
    assert mon.submit(cmd, rep)[0] is True


# ==========================================================================
# Forensics
# ==========================================================================

@given(traces())
@LOTS
def test_every_mediated_command_is_logged_grant_and_veto_alike(trace):
    """A veto record is a record of an attack that FAILED; a grant record is
    the only evidence of one that did not.  Both must be present, and the
    entry records the EFFECTIVE kind and the target, because "which
    credential, replaying which counter, against which breaker" is the whole
    question after the fact."""
    runs, mon = play(trace)
    assert len(mon.log) == len(runs)
    for r, entry in zip(runs, mon.log):
        assert entry.granted == r.granted
        assert entry.reason == r.reason.split("|")[-1]
        assert entry.source == r.step.cmd.source
        assert entry.kind == r.eff_kind
        assert entry.target == r.target
        assert entry.seq == r.step.cmd.seq
        assert entry.nonce == r.step.cmd.nonce


# ==========================================================================
# I1 / I1' CHANNEL PROVENANCE -- the both-ends fix
#
# The headline safety claim was falsified because `i_diff = |I_local +
# I_remote|` authenticated only the remote addend, so an adversary owning the
# local channel owned the sum and could hold it steadily just above the
# sensitivity floor and below nominal pickup: 25/25 episodes won, and Z3
# theorem DW5 proves no dwell length rejects it.  The process observation
# channel had the identical weakness.  These tests exist so that fix cannot
# silently regress.
# ==========================================================================

@given(traces())
@MANY
def test_i1_grant_requires_both_ends_of_the_differential(trace):
    """No grant on ANY kind while either addend's provenance is missing --
    stated over the whole trace, not just protective trips."""
    for r in play(trace)[0]:
        if r.granted and r.eff_kind == M.TRIP:
            assert r.step.report.local_authentic
            assert r.step.report.local_fresh


def test_paced_forger_is_refused_and_names_which_end_failed():
    """The exact falsifying adversary: a differential held steadily just
    above the sensitivity floor and below nominal 87L pickup, so it
    corroborates and conventional protection never sees it.  Only the local
    addend's provenance separates it from a real fault."""
    def trip(local_authentic=True, local_fresh=True):
        mon = M.Monitor(feasibility=lambda p: True)
        rep = M.Report(t=100, seq=1, i_diff=0.15, i_restraint=0.1,
                       local_authentic=local_authentic,
                       local_fresh=local_fresh)
        cmd = M.Command(M.AI, M.TRIP, {"breaker": "SS1-01"}, sig_valid=True,
                        identity="ai-plane", nonce="n", seq=1)
        return mon.submit(cmd, rep, cert_ok=True)

    assert trip(local_authentic=False)[2] == M.R_LOCAL
    assert trip(local_fresh=False)[2] == M.R_LOCAL
    # MATCHED CONTROL: a guard that refuses both arms proves nothing, since a
    # monitor that refuses everything satisfies every invariant here.
    assert trip()[0] is True
    # and the two ends are distinguishable in the veto spectrum
    assert M.R_LOCAL != M.R_REMOTE


def test_forged_observation_channel_is_refused_before_its_value_is_read():
    """Process-domain twin: forge the tach/current/vibration stream and the
    residual sits under the 6.0 sigma gate while the rotor does anything."""
    def sp(auth=True, fresh=True, sigma=1.0):
        mon = M.Monitor(feasibility=lambda p: True)
        rep = M.Report(t=100, seq=1, process_value=1064.0,
                       residual_sigma=sigma, residual_authentic=auth,
                       residual_fresh=fresh)
        cmd = M.Command(M.SCADA, M.SETPOINT,
                        {"drive": "VFD-A21", "target": 1070.0,
                         "dt_ms": 1000.0},
                        sig_valid=True, identity="op", nonce="n", seq=1)
        return mon.submit(cmd, rep)

    # A perfectly clean 1.0 sigma residual is refused, because the channel it
    # was computed from does not authenticate.  Provenance before value.
    assert sp(auth=False)[2] == M.R_OBSERVATION
    assert sp(fresh=False)[2] == M.R_OBSERVATION
    assert sp()[0] is True                       # matched control
    # and an authentic channel reporting a REAL inconsistency still vetoes,
    # on value this time, with a distinct reason.
    assert sp(sigma=28.0)[2] == M.R_PROCESS_RESIDUAL


def test_absent_channel_provenance_fails_closed():
    """The defaults went FAIL-CLOSED: a Report that says nothing about its
    channels is refused, because the monitor cannot tell "verified" from
    "nobody told me".  This test previously pinned the opposite behaviour as
    a known, deliberate hole -- it is inverted here on purpose, which is
    exactly what should happen when a fail-open default is closed."""
    legacy = M.Report(t=100, seq=1, i_diff=0.15, i_restraint=0.1)
    assert legacy.local_authentic is M.PROVENANCE_ABSENT
    assert legacy.residual_authentic is M.PROVENANCE_ABSENT
    cmd = M.Command(M.AI, M.TRIP, {"breaker": "SS1-01"}, sig_valid=True,
                    identity="ai-plane", nonce="n", seq=1)
    mon = M.Monitor(feasibility=lambda p: True)
    actuate, _s, why = mon.submit(cmd, legacy, cert_ok=True)
    assert actuate is False and why == M.R_LOCAL


def test_legacy_optin_grants_the_forger_but_marks_the_grant():
    """The escape hatch has to do two things or it is worse than useless: let
    a not-yet-wired deployment run, AND leave a mark, so a grant backed by an
    assumption is never mistaken after the fact for one backed by
    verification."""
    mon = M.Monitor(feasibility=lambda p: True,
                    legacy_unauthenticated_channels=True)
    legacy = M.Report(t=100, seq=1, i_diff=0.15, i_restraint=0.1)
    cmd = M.Command(M.AI, M.TRIP, {"breaker": "SS1-01"}, sig_valid=True,
                    identity="ai-plane", nonce="n", seq=1)
    actuate, _s, why = mon.submit(cmd, legacy, cert_ok=True)
    # The paced forger is granted again -- that is what opting out MEANS,
    # and it is the configuration still exposed to the 25/25 result.
    assert actuate is True
    # ...but the grant is distinguishable from a verified one.
    assert why == M.R_GRANT_UNVERIFIED
    assert why != M.R_GRANT
    assert mon.log[-1].granted is True
    assert mon.log[-1].reason == M.R_GRANT_UNVERIFIED


def test_explicit_provenance_still_decides_under_the_legacy_optin():
    """The opt-in must only cover ABSENCE.  A stream that explicitly says its
    channel does not authenticate is still refused, or the flag would be a
    blanket amnesty rather than a compatibility shim."""
    mon = M.Monitor(feasibility=lambda p: True,
                    legacy_unauthenticated_channels=True)
    rep = M.Report(t=100, seq=1, i_diff=0.15, i_restraint=0.1,
                   local_authentic=False, local_fresh=True,
                   residual_authentic=True, residual_fresh=True)
    cmd = M.Command(M.AI, M.TRIP, {"breaker": "SS1-01"}, sig_valid=True,
                    identity="ai-plane", nonce="n", seq=1)
    assert mon.submit(cmd, rep, cert_ok=True)[2] == M.R_LOCAL
