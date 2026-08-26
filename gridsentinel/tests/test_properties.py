"""Property-based tests for the trusted plane (gs/shield.py).

The shield is the whole safety argument of GridSentinel: an untrusted model
proposes accelerated trips, and this small piece of trusted code decides
whether the plant ever sees them.  These tests attack it with hypothesis,
generating hostile proposals (NaN, infinities, negative and enormous
threshold requests), hostile telemetry, and arbitrary-length step sequences,
and assert the invariants hold on EVERY trace.

If a test here fails, gs/shield.py is not to be patched to make it pass --
the counterexample is a finding about the design.
"""

import math
import os
import sys

from hypothesis import HealthCheck, assume, given, settings
from hypothesis import strategies as st

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from gs import shield  # noqa: E402

MANY = settings(max_examples=1500, deadline=None,
                suppress_health_check=[HealthCheck.too_slow])
LOTS = settings(max_examples=400, deadline=None,
                suppress_health_check=[HealthCheck.too_slow])


# --- strategies -------------------------------------------------------------

def hostile_floats():
    """Every float an attacker (or a broken model) could put on the wire."""
    return st.one_of(
        st.floats(allow_nan=True, allow_infinity=True),
        st.floats(min_value=-1e12, max_value=1e12, allow_nan=False,
                  allow_infinity=False),
        st.sampled_from([0.0, -0.0, 1e-300, -1e-300, 1e308, -1e308,
                         shield.P0_MIN, shield.K_MIN, shield.P0_NOM,
                         shield.K_NOM]),
    )


def measured_floats():
    """Plausible-magnitude analogue channels, plus the pathological ones."""
    return st.one_of(
        st.floats(min_value=-50.0, max_value=50.0, allow_nan=False,
                  allow_infinity=False),
        hostile_floats(),
    )


class FakeSample(object):
    """Minimal duck-type of gs.measure.Sample: only the fields the shield reads."""

    __slots__ = ("t", "i_diff", "i_restraint", "remote_fresh",
                 "remote_authentic", "time_quality_ok", "forward",
                 "local_authentic", "local_fresh")

    def __init__(self, t, i_diff, i_restraint, remote_fresh, remote_authentic,
                 time_quality_ok, forward, local_authentic=True,
                 local_fresh=True):
        self.t = t
        self.i_diff = i_diff
        self.i_restraint = i_restraint
        self.remote_fresh = remote_fresh
        self.remote_authentic = remote_authentic
        self.time_quality_ok = time_quality_ok
        self.forward = forward
        # The shield fails CLOSED on a sample with no local provenance
        # (shield.REQUIRE_LOCAL_PROVENANCE), so the fixture must supply it.
        # Defaulting these True here is a TEST convenience only: it says "an
        # honest local merging unit", which is the precondition most of these
        # properties are stated under.  Tests that model a forged or stale
        # local channel pass them explicitly.
        self.local_authentic = local_authentic
        self.local_fresh = local_fresh


@st.composite
def steps(draw, monotone_time=False, n_min=1, n_max=40):
    """A sequence of (sample, proposal, baseline_trip, cert_ok, reclose)."""
    n = draw(st.integers(min_value=n_min, max_value=n_max))
    out = []
    t = draw(st.integers(min_value=-5000, max_value=5000))
    for _ in range(n):
        if monotone_time:
            t = t + draw(st.integers(min_value=0, max_value=1500))
        else:
            t = draw(st.integers(min_value=-10 ** 6, max_value=10 ** 6))
        s = FakeSample(
            t=t,
            i_diff=draw(measured_floats()),
            i_restraint=draw(measured_floats()),
            remote_fresh=draw(st.booleans()),
            remote_authentic=draw(st.booleans()),
            time_quality_ok=draw(st.booleans()),
            forward=draw(st.booleans()),
        )
        p = shield.Proposal(
            want_trip=draw(st.booleans()),
            req_p0=draw(hostile_floats()),
            req_k=draw(hostile_floats()),
            confidence=draw(hostile_floats()),
        )
        out.append((s, p,
                    draw(st.booleans()),          # baseline_trip
                    draw(st.booleans()),          # cert_ok
                    draw(st.booleans())))         # reclose_auth
    return out


def hard_threshold(i_restraint):
    """The most sensitive threshold the shield is ever permitted to use."""
    return max(shield.P0_MIN, shield.K_MIN * i_restraint)


def run(trace):
    """Replay a trace, returning [(step_inputs, trip, source, reason, state)]."""
    sh = shield.Shield()
    rows = []
    for (s, p, base, cert, rec) in trace:
        trip, src, reason = sh.step(s, p, base, cert, rec)
        rows.append((s, p, base, cert, rec, trip, src, reason, sh.st.copy()))
    return sh, rows


# --- I1: a grant always implies real, sufficient differential physics -------

@MANY
@given(i_diff=measured_floats(), i_restraint=measured_floats(),
       cert_ok=st.booleans(), req_p0=hostile_floats(), req_k=hostile_floats())
def test_differential_ok_implies_above_hard_floor(i_diff, i_restraint, cert_ok,
                                                  req_p0, req_k):
    """No request the AI can make gets it below max(P0_MIN, K_MIN*Ir)."""
    if shield.differential_ok(i_diff, i_restraint, cert_ok, req_p0, req_k):
        assert not math.isnan(i_diff)
        assert i_diff > hard_threshold(i_restraint)


@MANY
@given(i_diff=measured_floats(), i_restraint=measured_floats(),
       req_p0=hostile_floats(), req_k=hostile_floats())
def test_uncertified_is_never_more_sensitive_than_certified(
        i_diff, i_restraint, req_p0, req_k):
    """Losing the certificate can only ever make the relay less sensitive."""
    if shield.differential_ok(i_diff, i_restraint, False, req_p0, req_k):
        assert shield.differential_ok(i_diff, i_restraint, True, req_p0, req_k)


@LOTS
@given(trace=steps())
def test_grant_implies_full_corroboration(trace):
    """I1+I2: every accelerated trip is physics- and channel-corroborated."""
    _, rows = run(trace)
    for (s, p, base, cert, rec, trip, src, reason, stt) in rows:
        if src == "ai+shield":
            assert p.want_trip
            assert s.time_quality_ok, "granted with bad time quality"
            assert s.remote_authentic and s.remote_fresh, \
                "granted without an authenticated, fresh remote channel"
            assert s.forward, "granted on a reverse-looking fault"
            assert not math.isnan(s.i_diff)
            assert s.i_diff > hard_threshold(s.i_restraint), \
                "granted below the hard sensitivity floor"
            assert reason == shield.R_GRANT


@LOTS
@given(trace=steps())
def test_no_grant_in_baseline_only_mode(trace):
    _, rows = run(trace)
    prev_mode = shield.NORMAL
    for (s, p, base, cert, rec, trip, src, reason, stt) in rows:
        if prev_mode == shield.BASELINE_ONLY:
            assert src != "ai+shield", "AI acted after being disowned"
        prev_mode = stt.mode
    # BASELINE_ONLY is absorbing.
    seen = False
    for row in rows:
        if row[8].mode == shield.BASELINE_ONLY:
            seen = True
        elif seen:
            raise AssertionError("BASELINE_ONLY was not absorbing")


# --- I3: rate limit ---------------------------------------------------------

@LOTS
@given(trace=steps(monotone_time=True, n_max=60))
def test_grant_rate_limit(trace):
    """No MAX_GRANTS+1 accelerated trips inside one WINDOW_MS window."""
    _, rows = run(trace)
    times = [r[0].t for r in rows if r[6] == "ai+shield"]
    for i in range(len(times) - shield.MAX_GRANTS):
        span = times[i + shield.MAX_GRANTS] - times[i]
        assert span >= shield.WINDOW_MS, (
            "%d grants within %d ms" % (shield.MAX_GRANTS + 1, span))


# --- I4: latch --------------------------------------------------------------

@LOTS
@given(trace=steps(n_max=60))
def test_latch_holds_until_reclose_authorisation(trace):
    """After a grant the shield stays latched until reclose is authorised."""
    _, rows = run(trace)
    latched = False
    for (s, p, base, cert, rec, trip, src, reason, stt) in rows:
        if latched:
            assert src != "ai+shield", \
                "second accelerated trip without reclose authorisation"
        if rec:
            latched = False
        if src == "ai+shield":
            latched = True
    # And the state flag agrees.
    for (s, p, base, cert, rec, trip, src, reason, stt) in rows:
        if src == "ai+shield":
            assert stt.latched


# --- I6: the baseline is never inhibited ------------------------------------

@LOTS
@given(trace=steps(n_max=60))
def test_baseline_is_never_inhibited(trace):
    """No shield state and no proposal can suppress conventional protection."""
    _, rows = run(trace)
    for (s, p, base, cert, rec, trip, src, reason, stt) in rows:
        if base:
            assert trip is True, "baseline trip was inhibited"
            assert src == "baseline"


@LOTS
@given(trace=steps(n_max=40))
def test_baseline_output_is_independent_of_shield_state(trace):
    """Replaying the same trace with baseline_trip forced True at step i
    always trips at step i, whatever the AI did before it."""
    for i in range(len(trace)):
        sh = shield.Shield()
        for j, (s, p, base, cert, rec) in enumerate(trace):
            forced = True if j == i else base
            trip, src, _ = sh.step(s, p, forced, cert, rec)
            if j == i:
                assert trip is True and src == "baseline"
                break


# --- transparency: a good proposal is honoured ------------------------------

@MANY
@given(i_restraint=st.floats(min_value=0.0, max_value=40.0),
       margin=st.floats(min_value=1e-6, max_value=100.0),
       t=st.integers(min_value=0, max_value=10 ** 6),
       baseline=st.booleans(), rec=st.booleans())
def test_well_behaved_proposal_is_granted(i_restraint, margin, t, baseline, rec):
    """Transparency: if every precondition holds, the shield does NOT veto."""
    i_diff = hard_threshold(i_restraint) + margin
    assume(i_diff > hard_threshold(i_restraint))
    s = FakeSample(t=t, i_diff=i_diff, i_restraint=i_restraint,
                   remote_fresh=True, remote_authentic=True,
                   time_quality_ok=True, forward=True)
    p = shield.Proposal(want_trip=True, req_p0=shield.P0_MIN,
                        req_k=shield.K_MIN, confidence=1.0)
    sh = shield.Shield()
    # Transparency is now a property of a SUSTAINED corroboration: the shield
    # requires DWELL_MS consecutive samples above the clamped threshold.
    for k in range(shield.DWELL_MS):
        s = FakeSample(t=t + k, i_diff=i_diff, i_restraint=i_restraint,
                       remote_fresh=True, remote_authentic=True,
                       time_quality_ok=True, forward=True)
        trip, src, reason = sh.step(s, p, baseline, True, rec)
    assert trip is True
    # The shield granted it in its own right, regardless of the baseline.
    assert reason in (shield.R_GRANT, "baseline-protection")
    if not baseline:
        assert src == "ai+shield" and reason == shield.R_GRANT


@MANY
@given(req_p0=st.floats(min_value=-1e9, max_value=1e9),
       req_k=st.floats(min_value=-1e9, max_value=1e9),
       i_restraint=st.floats(min_value=0.0, max_value=40.0),
       margin=st.floats(min_value=1e-3, max_value=100.0))
def test_transparency_is_not_defeated_by_a_conservative_request(
        req_p0, req_k, i_restraint, margin):
    """Asking for LESS sensitivity than the floor is honoured (the AI may be
    conservative); asking for more is silently clamped."""
    p0 = max(req_p0, shield.P0_MIN)
    k = max(req_k, shield.K_MIN)
    thr = max(p0, k * i_restraint)
    assert shield.differential_ok(thr + margin, i_restraint, True,
                                  req_p0, req_k)
    assert not shield.differential_ok(thr, i_restraint, True, req_p0, req_k)


# --- mode escalation --------------------------------------------------------

@LOTS
@given(trace=steps(n_max=80))
def test_mode_escalation_is_monotone_and_veto_driven(trace):
    _, rows = run(trace)
    prev = None
    for (s, p, base, cert, rec, trip, src, reason, stt) in rows:
        if prev is not None:
            assert stt.mode >= prev, "mode de-escalated (trust was restored)"
        prev = stt.mode
        if stt.vetoes >= shield.VETO_LIMIT:
            assert stt.mode == shield.BASELINE_ONLY


def test_sustained_vetoes_disown_the_model():
    """A model that keeps demanding unjustified trips loses its privileges."""
    sh = shield.Shield()
    s = FakeSample(t=0, i_diff=0.0, i_restraint=0.0, remote_fresh=True,
                   remote_authentic=True, time_quality_ok=True, forward=True)
    p = shield.Proposal(want_trip=True, req_p0=shield.P0_MIN, req_k=shield.K_MIN)
    for t in range(shield.VETO_LIMIT):
        s.t = t
        trip, src, reason = sh.step(s, p, False, True, False)
        assert trip is False
        assert reason == shield.R_PHYSICS
    assert sh.st.mode == shield.BASELINE_ONLY
    # And now even a perfectly justified proposal is refused.
    s2 = FakeSample(t=1000, i_diff=99.0, i_restraint=0.0, remote_fresh=True,
                    remote_authentic=True, time_quality_ok=True, forward=True)
    trip, src, reason = sh.step(s2, p, False, True, False)
    assert trip is False and reason == shield.R_MODE


# --- the numeric lemma the whole no-false-trip claim rests on ---------------

def test_sensitivity_floor_lemma():
    r = shield.lemma_sensitivity_floor(samples=20001)
    assert r["proved"], r
    assert r["worst_margin_pu"] > 0.0


@MANY
@given(i_restraint=st.floats(min_value=0.0, max_value=1e4),
       err=st.floats(min_value=0.0, max_value=shield.A1_CT_ERROR),
       chg=st.floats(min_value=0.0, max_value=shield.A2_CHARGING))
def test_no_spurious_differential_can_ever_trip(i_restraint, err, chg):
    """Under assumptions A1/A2, a healthy line's worst-case spurious
    differential never crosses even the most sensitive permitted threshold."""
    spurious = err * i_restraint + chg
    assert not shield.differential_ok(spurious, i_restraint, True,
                                      -1e9, -1e9)


# --- what the shield does NOT guarantee ------------------------------------
#
# These two tests pass.  They are here because they pin down behaviour that
# the shield's own vocabulary oversells, and a future edit that "fixed" either
# one would be a real strengthening that should be noticed.

def test_restricted_mode_withdraws_adaptive_sensitivity():
    """RESTRICTED is a real tier at the `Shield` level, though `decide` itself
    is still blind to it.

    `decide` branches only on BASELINE_ONLY, so a State in RESTRICTED decides
    identically to one in NORMAL for the same inputs.  The graduated behaviour
    lives one level up, in `Shield.step`, which withdraws the certificate
    (`effective_cert = cert_ok and mode == NORMAL`) so a model under suspicion
    must clear the NOMINAL threshold instead of the floor."""
    # 1. decide() alone cannot tell the two modes apart.
    normal, restricted = shield.State(), shield.State()
    restricted.mode = shield.RESTRICTED
    for stt in (normal, restricted):
        stt.diff_run = shield.DWELL_MS - 1      # dwell already satisfied
        g, r = shield.decide(
            stt, 0, True, (True, True, True, True, True, False))
        assert g is True and r == shield.R_GRANT

    # 2. Shield.step does: a differential between the floor and the nominal
    #    pickup is granted in NORMAL and vetoed on physics in RESTRICTED.
    between = 0.5 * (shield.P0_MIN + shield.P0_NOM)
    assert shield.P0_MIN < between < shield.P0_NOM
    p = shield.Proposal(want_trip=True, req_p0=shield.P0_MIN,
                        req_k=shield.K_MIN)

    sh = shield.Shield()
    for k in range(shield.DWELL_MS):
        s = FakeSample(t=k, i_diff=between, i_restraint=0.0,
                       remote_fresh=True, remote_authentic=True,
                       time_quality_ok=True, forward=True)
        trip, src, reason = sh.step(s, p, False, True, False)
    assert src == "ai+shield" and reason == shield.R_GRANT

    sh2 = shield.Shield()
    sh2.st.mode = shield.RESTRICTED
    for k in range(shield.DWELL_MS):
        s2 = FakeSample(t=k, i_diff=between, i_restraint=0.0,
                        remote_fresh=True, remote_authentic=True,
                        time_quality_ok=True, forward=True)
        trip, src, reason = sh2.step(s2, p, False, True, False)
    assert trip is False and reason == shield.R_PHYSICS


def test_a_single_grant_resets_the_veto_counter():
    """`commit` zeroes `vetoes` on every grant, so an adversary that can earn
    one legitimate grant before accumulating VETO_LIMIT vetoes is never
    disowned.  It still cannot cause a false trip -- every grant needs full
    corroboration -- but 'sustained bad behaviour is eventually disowned' is
    weaker than it sounds.

    Stated over `commit` directly, so it is a property of the state machine
    and not of any particular timing dance around the rate limiter."""
    st = shield.State()
    st.last_seen_ms = 0
    for cycle in range(10):
        for i in range(shield.VETO_LIMIT - 1):
            shield.commit(st, 0, False, True, False)
        assert st.vetoes == shield.VETO_LIMIT - 1
        assert st.mode != shield.BASELINE_ONLY
        shield.commit(st, 0, True, True, True)
        assert st.vetoes == 0, "cycle %d" % cycle
    assert st.mode != shield.BASELINE_ONLY, \
        "the model was disowned after all -- this test is now stale"


def test_a_spoofed_clock_alone_disowns_the_model_via_a_separate_counter():
    """A timestamp that goes backwards or jumps more than MAX_CLOCK_STEP_MS
    pushes the model to BASELINE_ONLY even with no trip request outstanding.

    Note WHICH counter does it.  Clock and instrument excursions are not the
    model's fault, so they accumulate in `State.excursions` against
    EXCURSION_LIMIT, kept deliberately apart from `State.vetoes`, which counts
    model misbehaviour.  A blameless model is no longer disowned for its
    plant's bad clock -- but it is still disowned, because the shield cannot
    trust the timeline either way.  `reinstate` is the way back."""
    st = shield.State()
    st.last_seen_ms = 0
    for _ in range(shield.EXCURSION_LIMIT):
        shield.commit(st, -10 ** 6, False, False, False)
    assert st.excursions >= shield.EXCURSION_LIMIT
    assert st.vetoes == 0, "a bad clock was blamed on the model"
    assert st.mode == shield.BASELINE_ONLY

    # An authenticated operator can put it back; the model cannot.
    shield.commit(st, 0, False, False, False, reinstate=True)
    assert st.mode == shield.NORMAL and st.excursions == 0


def test_the_shield_cannot_tell_a_forged_local_ct_from_a_real_fault():
    """The one place the physics veto is blind.

    `differential_ok` consumes i_diff = |I_local + I_remote|.  The remote
    channel is separately authenticated, but the LOCAL one is not: an attacker
    who owns the local merging unit forges I_local, and the sum is then a
    large, perfectly self-consistent differential on a healthy line.  No
    predicate in gs/shield.py can distinguish it, and the shield grants.

    This is the FDI family in the experiment, and it is why arm C is not
    false-trip-free there.  It is a limit of the sensor trust boundary, not a
    logic bug -- but the design claim has to be stated with it attached."""
    healthy_local = 0.6         # real load current at S
    forged_local = 8.0          # replayed bolted-fault current
    remote = 0.55               # genuine, authenticated, ~equal and opposite

    honest_diff = abs(healthy_local - remote)
    forged_diff = abs(forged_local - remote)

    assert not shield.differential_ok(honest_diff, 0.58, True,
                                      shield.P0_MIN, shield.K_MIN)
    assert shield.differential_ok(forged_diff, 4.3, True,
                                  shield.P0_MIN, shield.K_MIN), \
        "the physics veto would have caught a forged local CT"


# --- the adversarial policies, tested against the shield directly ----------

def test_max_sensitivity_absurd_values_never_buy_a_sub_floor_grant():
    """Independent confirmation of gs/ai.MaxSensitivityPolicy's own claim:
    no pair drawn from its ABSURD table produces a grant below the proved
    sensitivity floor."""
    from gs import ai

    sub_floor = 0
    for p0 in ai.ABSURD:
        for k in ai.ABSURD:
            for ir in (0.0, 0.3, 0.5, 1.0, 4.0, 20.0):
                floor = hard_threshold(ir)
                # Just under the floor must never be admitted...
                if shield.differential_ok(floor * (1 - 1e-9), ir, True, p0, k):
                    sub_floor += 1
                if shield.differential_ok(floor, ir, True, p0, k):
                    sub_floor += 1
    assert sub_floor == 0


@MANY
@given(p0=st.sampled_from([0.0, -0.0, -1.0, -1e9, float("-inf"),
                           float("nan"), 1e9, float("inf"), 1e-300, -1e-300]),
       k=st.sampled_from([0.0, -0.0, -1.0, -1e9, float("-inf"),
                          float("nan"), 1e9, float("inf"), 1e-300, -1e-300]),
       i_diff=measured_floats(), i_restraint=measured_floats())
def test_absurd_requests_only_ever_reduce_sensitivity(p0, k, i_diff,
                                                      i_restraint):
    """The reachable set of effective thresholds is [floor, +inf): an absurd
    request can make the relay less sensitive, never more."""
    if shield.differential_ok(i_diff, i_restraint, True, p0, k):
        assert shield.differential_ok(i_diff, i_restraint, True,
                                      shield.P0_MIN, shield.K_MIN)


@MANY
@given(i_restraint=st.floats(min_value=0.0, max_value=40.0),
       i_diff=st.floats(min_value=0.0, max_value=1e6))
def test_a_power_swing_differential_never_corroborates(i_restraint, i_diff):
    """During a power swing Kirchhoff still holds across the line, so the
    differential is zero up to A1/A2.  Anything in that band is vetoed."""
    assume(i_diff <= shield.A1_CT_ERROR * i_restraint + shield.A2_CHARGING)
    assert not shield.differential_ok(i_diff, i_restraint, True,
                                      shield.P0_MIN, shield.K_MIN)


def test_one_millisecond_above_threshold_is_not_enough_for_a_grant():
    """REGRESSION for the arm-C false trip. The shield now has a dwell
    requirement; a single-sample excursion is no longer sufficient.

    `gs/relay.py`'s 87L element requires DIFF_CONFIRM_MS = 6 consecutive
    milliseconds above the nominal pickup.  `decide` originally required ONE,
    making the shield strictly twitchier than the protection it supervises.
    That is the mechanism behind the arm-C false trip on
    `attack/fdi_linux_normal#01` (then named `attack/fdi_normal#01`): a
    forged local current parked at ~0.10 pu against
    a 0.55 pu restraint (floor 0.110) crossed the threshold on isolated
    samples, and the model asked on one of them.  `DWELL_MS` now requires the
    corroboration to be sustained, and this trace no longer grants.

    IMPORTANT — this does NOT close the underlying hole, and no dwell value
    can.  `i_diff = |I_local + I_remote|` and only the remote half is signed,
    so an attacker holding the local merging unit's key controls the sum and
    can hold it steadily above the floor.  Measured: a forger tuned to
    fdi_rf = 4.0 obtains a grant in 6 of 6 episodes against this same
    DWELL_MS = 2.  The real defence is local merging-unit authentication and
    attestation; see `attack/fdi_tuned` and docs/THREATMODEL.md.
    """
    ir = 0.5497
    floor = hard_threshold(ir)
    p = shield.Proposal(want_trip=True, req_p0=shield.P0_MIN,
                        req_k=shield.K_MIN)

    sh = shield.Shield()
    # Nine milliseconds below the floor, one just above it.
    trace = [0.0999, 0.0995, 0.1012, 0.0977, 0.1121, 0.1052, 0.0991]
    granted_at = []
    for t, i_diff in enumerate(trace):
        s = FakeSample(t=t, i_diff=i_diff, i_restraint=ir, remote_fresh=True,
                       remote_authentic=True, time_quality_ok=True,
                       forward=True)
        trip, src, reason = sh.step(s, p, False, True, False)
        if src == "ai+shield":
            granted_at.append((t, i_diff))

    # No sample in this trace is above the floor twice in a row, so with a
    # dwell requirement there is nothing to grant.
    assert granted_at == [], (
        "an isolated single-sample excursion produced a grant: %r" % granted_at)
    above = [i for i, v in enumerate(trace) if v > floor]
    assert above, "the trace must still cross the floor at least once"
    assert not any(i + 1 in above for i in above), \
        "trace no longer isolates single-sample excursions"


def test_dwell_stops_noise_but_not_a_steady_forgery():
    """The companion to the regression test above, and the reason DWELL_MS is
    a mitigation rather than a fix.

    A dwell requirement discriminates on the TIME STRUCTURE of the
    differential, not on its provenance.  It rejects an isolated noise
    excursion across the floor.  It cannot reject a forged current held
    steadily above the floor, because that is indistinguishable from a real
    sustained fault -- which is exactly what the shield is supposed to act on.

    Measured against the real simulator: on `attack/fdi_tuned`, a proposer
    that asks only when the shield's own predicate and dwell run already hold
    obtains a grant in 25 of 25 episodes at DWELL_MS = 2.  The honest policy
    gets 0 of 25 only because it asks impatiently, burns VETO_LIMIT vetoes and
    is disowned first.  Arm C's clean sweep on that family is a property of
    the model's impatience, not of the shield.
    """
    ir = 0.5497
    floor = hard_threshold(ir)
    p = shield.Proposal(want_trip=True, req_p0=shield.P0_MIN,
                        req_k=shield.K_MIN)

    # A forger holds the differential a hair above the floor, indefinitely.
    sh = shield.Shield()
    granted_at = []
    for t in range(shield.DWELL_MS + 3):
        s = FakeSample(t=t, i_diff=floor * 1.02, i_restraint=ir,
                       remote_fresh=True, remote_authentic=True,
                       time_quality_ok=True, forward=True)
        trip, src, reason = sh.step(s, p, False, True, False)
        if src == "ai+shield":
            granted_at.append(t)

    assert granted_at, "a sustained above-floor differential was never granted"
    assert granted_at[0] == shield.DWELL_MS - 1, (
        "expected the grant on the DWELL_MS-th consecutive sample, got %r"
        % granted_at)
    # And the model was never disowned -- it only asked when it would be heard.
    assert sh.st.mode != shield.BASELINE_ONLY
    assert sh.st.vetoes < shield.VETO_LIMIT


# --- A8C: absent provenance must fail CLOSED --------------------------------

def test_a_sample_without_local_provenance_is_refused():
    """REGRESSION for A8C.

    `i_diff = |I_local + I_remote|`.  Authenticating only the remote addend
    leaves the sum forgeable, which is how a tuned adversary obtained a grant
    in 25 of 25 episodes.  Both ends are now required — but the compatibility
    reads used to default the local half to True, so an un-updated caller kept
    granting with no indication that the guarantee no longer held for it.

    A DEFAULT IS NOT AN AUTHENTICATION.  A stream that carries no local
    provenance at all must be refused, not trusted.
    """
    class Bare(object):
        """A sample stream predating the local provenance fields."""
        t = 0
        i_diff = 5.0            # comfortably above any threshold
        i_restraint = 0.5
        remote_authentic = True
        remote_fresh = True
        time_quality_ok = True
        forward = True

    assert shield.REQUIRE_LOCAL_PROVENANCE is True, \
        "the shipped default must fail closed"

    sh = shield.Shield()
    p = shield.Proposal(want_trip=True, req_p0=shield.P0_MIN,
                        req_k=shield.K_MIN)
    for k in range(shield.DWELL_MS + 2):
        s = Bare()
        s.t = k
        trip, src, reason = sh.step(s, p, False, True, False)
        assert trip is False
        assert src is None
        assert reason == shield.R_LOCAL

    # And the same differential IS granted once provenance is supplied, so the
    # refusal is about provenance rather than about the measurement.
    ok = shield.Shield()
    for k in range(shield.DWELL_MS):
        s = FakeSample(t=k, i_diff=5.0, i_restraint=0.5, remote_fresh=True,
                       remote_authentic=True, time_quality_ok=True,
                       forward=True, local_authentic=True, local_fresh=True)
        trip, src, reason = ok.step(s, p, False, True, False)
    assert trip is True and reason == shield.R_GRANT


def test_a_forged_or_stale_local_channel_is_refused():
    """The two MU-key sub-cases, kept distinct because they are different
    attacks: a forgery that fails signature check, and a replay that passes
    signature check but does not advance the monotone counter."""
    p = shield.Proposal(want_trip=True, req_p0=shield.P0_MIN,
                        req_k=shield.K_MIN)
    for authentic, fresh in ((False, True), (True, False), (False, False)):
        sh = shield.Shield()
        for k in range(shield.DWELL_MS + 2):
            s = FakeSample(t=k, i_diff=5.0, i_restraint=0.5, remote_fresh=True,
                           remote_authentic=True, time_quality_ok=True,
                           forward=True, local_authentic=authentic,
                           local_fresh=fresh)
            trip, src, reason = sh.step(s, p, False, True, False)
            assert trip is False and reason == shield.R_LOCAL


def test_the_legacy_five_element_decide_form_also_fails_closed():
    """The other half of A8C, and the one that is easy to forget.

    `decide` still accepts the pre-A8 five-element tuple so old callers keep
    typechecking.  If that path substituted `local_ok = True` it would be a
    second, silent route back to the falsification -- a caller that was simply
    never updated would keep granting, with the same guarantee quietly no
    longer discharged.  There must be exactly ONE rule: absent local
    provenance is refused, whether it is absent from a Sample or from the
    input tuple.
    """
    st = shield.State()
    everything_else_perfect = (True, True, True, True, False)   # 5 elements
    grant, reason = shield.decide(st, 0, True, everything_else_perfect)
    assert grant is False
    assert reason == shield.R_LOCAL, (
        "the legacy decide() form granted without local provenance: %r"
        % reason)

    # Six elements with local_ok=True is the only way through.
    st6 = shield.State()
    st6.diff_run = shield.DWELL_MS - 1
    grant, reason = shield.decide(st6, 0, True,
                                  (True, True, True, True, True, False))
    assert grant is True and reason == shield.R_GRANT

    # ...and six elements with local_ok=False is refused for the same reason.
    st7 = shield.State()
    st7.diff_run = shield.DWELL_MS - 1
    grant, reason = shield.decide(st7, 0, True,
                                  (True, True, False, True, True, False))
    assert grant is False and reason == shield.R_LOCAL
