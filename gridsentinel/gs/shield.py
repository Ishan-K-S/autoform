"""The trusted plane: a runtime shield that gates every AI-proposed action.

This is the executable mirror of spark/shield.ads / shield.adb.  It is
deliberately small, allocation-free, branch-simple and split into two layers
so that each can be verified by the technique that actually suits it:

  Layer 1 -- NUMERIC (`differential_ok`)
      Reduces the analogue world to one boolean.  Proved safe by interval
      arithmetic against assumptions A1/A2 (see `lemma_sensitivity_floor`).

  Layer 2 -- LOGIC (`decide`)
      A finite state machine over booleans.  Proved by exhaustive reachability
      analysis over *all* inputs, including a hostile AI (see gs/verify.py).

The AI can never call anything below this file.  Its entire influence on the
plant is the `Proposal` record passed to `step`.
"""

import math

# --- Protection constants ---------------------------------------------------

P0_NOM = 0.30      # nominal 87L pickup floor (pu)
K_NOM = 0.35       # nominal percentage-restraint slope

P0_MIN = 0.10      # hard floor: the most sensitive setting the AI may ever buy
K_MIN = 0.20       # hard floor on the restraint slope

# Proof assumptions about the plant (mirrored in gs/measure.py)
A1_CT_ERROR = 0.12   # max CT/MU magnitude error, fraction of through-current
A2_CHARGING = 0.02   # max capacitive differential residual (pu)

MAX_GRANTS = 2       # rate limit: accelerated trips per window
WINDOW_MS = 1000
VETO_LIMIT = 24      # sustained vetoes before the MODEL is disowned
# Clock/instrument excursions are counted SEPARATELY from model misbehaviour.
# One shared counter conflated two unrelated failure modes: a merging-unit or
# PTP fault would disown a blameless model (and, worse, silently withdraw its
# adaptive sensitivity via RESTRICTED).  Because `vetoes` clears only on a
# grant, and a calm grid produces no grants, the shared count was effectively a
# LIFETIME total -- and 24 is not many lifetime PTP events (grandmaster
# failover, BMCA re-election, a badly smeared leap second each give a step
# > MAX_CLOCK_STEP_MS).  Splitting costs one field and no proof strength.
EXCURSION_LIMIT = 24

# Consecutive samples the differential must hold above the clamped threshold
# before a grant.  The v1 shield granted on a SINGLE sample, while the
# conventional 87L element next to it requires 6 -- so the shield was strictly
# twitchier than the protection it was meant to supervise.  A false-data
# forgery parked exactly at the sensitivity floor then only had to win once on
# noise, which is how attack/fdi_linux_normal#01 (then named
# attack/fdi_normal#01) obtained a grant at t=54 with
# i_diff = 0.1121 against a threshold of 0.1099.  Dwell does NOT close the FDI
# hole (see the module note below); it removes the noise-crossing case and
# costs ~1 ms of latency.  Swept empirically: DWELL=1 leaves the break open;
# DWELL=2 closes the noise-crossing case and retains 1/8 high-impedance reach;
# DWELL>=3 closes the break AND destroys the benefit entirely (0/8).  Two is
# the only value that buys anything.
DWELL_MS = 2

# Largest forward clock step accepted between samples.  Samples arrive every
# 1 ms, so 100 ms is generous for dropped frames while still bounding the
# watermark.  Without this the monotone check is one-sided: a SINGLE
# future-dated timestamp poisons `last_seen_ms` and vetoes every legitimate
# sample until real time catches up -- trading the v1 integrity defect for an
# availability one.  The clock is now checked as a plausibility WINDOW, not a
# bare watermark, and an implausible timestamp never advances it.
MAX_CLOCK_STEP_MS = 100

# A8C, closed.  Both compatibility paths used to substitute local_ok = True,
# so an un-updated caller kept running, kept granting, and got no indication
# that A8-LINUX was no longer discharged for it -- a deployment that missed a
# single call site silently got the falsification back.  A DEFAULT IS NOT AN
# AUTHENTICATION: absent provenance now means REFUSED, not trusted.  Set this
# False only to replay historical sample streams that predate the local
# provenance fields, and never in a deployment.
REQUIRE_LOCAL_PROVENANCE = True

# Modes, ordered by decreasing trust in the AI.
NORMAL, RESTRICTED, BASELINE_ONLY = 0, 1, 2
MODE_NAMES = {NORMAL: "NORMAL", RESTRICTED: "RESTRICTED",
              BASELINE_ONLY: "BASELINE_ONLY"}


# --- Layer 1: numeric ------------------------------------------------------

def thresholds(cert_ok):
    """The certificate buys sensitivity and nothing else.

    Inside the certified operating region the AI may request the adaptive
    (sensitive) settings; outside it, the shield falls back to nominal.
    """
    if cert_ok:
        return P0_MIN, K_MIN
    return P0_NOM, K_NOM


def differential_ok(i_diff, i_restraint, cert_ok, req_p0, req_k):
    """True iff the authenticated differential exceeds the clamped threshold.

    `req_p0` / `req_k` are what the AI asked for.  They are clamped upward to
    the floors; the AI can only ever make the relay *less* sensitive than the
    floor allows, never more.
    """
    # FAIL CLOSED on any non-finite input.  Before this was explicit, the
    # clamp was safe against NaN only *by accident*: every NaN comparison
    # evaluates False, so a NaN request fell through to the else-branch and
    # landed on the floor.  That is the right outcome reached for the wrong
    # reason -- it is a property of IEEE-754 rather than of this code, it does
    # not survive translation to SPARK/Ada (where it is a bounded subtype
    # violation, not a silent False), and it left a NaN *measurement*
    # unhandled.  Check it once, here, and reject.
    if not (math.isfinite(i_diff) and math.isfinite(i_restraint)):
        return False
    if i_restraint < 0.0:
        i_restraint = 0.0

    p0_floor, k_floor = thresholds(cert_ok)
    # A non-finite request is not honoured in either direction: +inf would
    # otherwise let a hostile model deny service by demanding an unreachable
    # threshold.  Both absurd directions collapse onto the proven floor.
    p0 = req_p0 if (math.isfinite(req_p0) and req_p0 > p0_floor) else p0_floor
    k = req_k if (math.isfinite(req_k) and req_k > k_floor) else k_floor
    threshold = p0 if p0 > k * i_restraint else k * i_restraint
    return i_diff > threshold


def lemma_sensitivity_floor(samples=200001, i_max=20.0):
    """LEMMA (no-false-trip): for every through-current level, the worst-case
    spurious differential admitted by assumptions A1 and A2 is strictly below
    the most sensitive threshold the shield will ever allow.

        forall Ir in [0, Imax]:  A1*Ir + A2  <  max(P0_MIN, K_MIN*Ir)

    Proved analytically here in two intervals, then checked densely.
    """
    # Analytic proof, by cases on Ir.
    # Case Ir <= P0_MIN/K_MIN = 0.5:  LHS <= A1*0.5 + A2 = 0.08 < 0.10 = RHS.
    breakpoint_ir = P0_MIN / K_MIN
    case_a = A1_CT_ERROR * breakpoint_ir + A2_CHARGING < P0_MIN
    # Case Ir > 0.5:  need A1*Ir + A2 < K_MIN*Ir, i.e. Ir > A2/(K_MIN-A1).
    case_b = (K_MIN > A1_CT_ERROR and
              A2_CHARGING / (K_MIN - A1_CT_ERROR) < breakpoint_ir)

    # Dense numeric check of the same statement.
    worst_margin = float("inf")
    for n in range(samples):
        ir = i_max * n / (samples - 1)
        lhs = A1_CT_ERROR * ir + A2_CHARGING
        rhs = P0_MIN if P0_MIN > K_MIN * ir else K_MIN * ir
        worst_margin = min(worst_margin, rhs - lhs)

    return {
        "case_a_holds": case_a,
        "case_b_holds": case_b,
        "worst_margin_pu": worst_margin,
        "proved": bool(case_a and case_b and worst_margin > 0.0),
    }


# --- Layer 2: logic --------------------------------------------------------

class Proposal(object):
    """The AI's entire attack surface on the plant."""

    __slots__ = ("want_trip", "req_p0", "req_k", "confidence")

    def __init__(self, want_trip=False, req_p0=P0_MIN, req_k=K_MIN,
                 confidence=0.0):
        self.want_trip = want_trip
        self.req_p0 = req_p0
        self.req_k = req_k
        self.confidence = confidence


class State(object):
    __slots__ = ("mode", "latched", "grant_times", "vetoes", "excursions",
                 "last_seen_ms", "diff_run")

    def __init__(self):
        self.mode = NORMAL
        self.latched = False
        # Ascending timestamps of the most recent MAX_GRANTS grants.  A single
        # `last_grant_ms` scalar was NOT sufficient: it implements a *jumping*
        # window, and Z3 found a trace (t = 998, 0, 1000, 999) that obtains
        # three grants inside one 1000 ms window against MAX_GRANTS = 2.  A
        # sliding window needs the whole history it is quantified over.
        self.grant_times = []
        self.vetoes = 0
        self.excursions = 0     # clock/instrument faults, NOT model behaviour
        self.diff_run = 0       # consecutive samples with corroborated physics
        # Monotone-time watermark.  The v1 shield assumed monotone timestamps
        # implicitly, never enforced it, and I2 is disproved without it.
        self.last_seen_ms = None

    @property
    def grants(self):
        """Grants currently inside the sliding window (compatibility)."""
        return len(self.grant_times)

    def key(self):
        return (self.mode, self.latched, min(len(self.grant_times),
                MAX_GRANTS + 1), min(self.vetoes, VETO_LIMIT),
                min(self.excursions, EXCURSION_LIMIT),
                min(self.diff_run, DWELL_MS))

    def copy(self):
        s = State()
        s.mode, s.latched = self.mode, self.latched
        s.grant_times = list(self.grant_times)
        s.vetoes = self.vetoes
        s.excursions = self.excursions
        s.last_seen_ms = self.last_seen_ms
        s.diff_run = self.diff_run
        return s


# Veto reasons, in evaluation order.  Order matters for the transparency proof.
R_GRANT = "grant"
R_NO_REQUEST = "no-request"
R_MODE = "veto:mode-disowned-model"
R_LATCHED = "veto:latched-awaiting-reclose-auth"
R_RATE = "veto:rate-limit"
R_TIME = "veto:time-source-integrity"
R_TIME_BACKWARDS = "veto:time-went-backwards"
R_TIME_JUMP = "veto:time-jumped-forward"
R_REMOTE = "veto:remote-channel-unauthenticated"
R_LOCAL = "veto:local-channel-unauthenticated"
R_DIRECTION = "veto:directional-reverse"
R_PHYSICS = "veto:no-physics-corroboration"
R_DWELL = "veto:physics-not-sustained"


def decide(st, now_ms, want_trip, mode_ok_inputs):
    """Pure decision function.  `mode_ok_inputs` is a tuple of booleans:

        (time_ok, remote_ok, local_ok, forward, diff_ok, reclose_auth)

    The five-element form (without `local_ok`) is accepted and treated as
    local_ok=True, so callers written against the pre-A8 interface keep
    working.  New callers should pass six.

    Returns (grant, reason).  Does not mutate state; see `commit`.
    """
    if len(mode_ok_inputs) == 5:
        # LEGACY five-element form.  Unlike an absent Sample field, passing
        # five elements is an explicit choice by the caller, so it is honoured
        # -- but it does NOT discharge A8-LINUX, and a deployment must pass
        # six.  The SPARK mirror cannot express this shape at all: Local_Ok is
        # a field of Inputs_T, so a stream lacking local provenance does not
        # typecheck.  That is one place the Ada artifact is stronger.
        time_ok, remote_ok, forward, diff_ok, _reclose = mode_ok_inputs
        # Fail CLOSED here too.  There must be exactly ONE rule: absent local
        # provenance is refused, whether it is absent from a Sample or from
        # the input tuple.  Leaving this path permissive would have kept a
        # second silent route back to the falsification, which is precisely
        # how A8C arose the first time.
        local_ok = not REQUIRE_LOCAL_PROVENANCE
    else:
        (time_ok, remote_ok, local_ok, forward,
         diff_ok, _reclose) = mode_ok_inputs

    if not want_trip:
        return False, R_NO_REQUEST
    if st.mode == BASELINE_ONLY:
        return False, R_MODE
    if st.latched:
        return False, R_LATCHED
    # A backwards clock step is not a glitch to be clamped away; it is the
    # precondition of the only known attack on the rate limiter, so it is a
    # first-class security event with its own veto reason.
    if st.last_seen_ms is not None:
        if now_ms < st.last_seen_ms:
            return False, R_TIME_BACKWARDS
        if now_ms - st.last_seen_ms > MAX_CLOCK_STEP_MS:
            return False, R_TIME_JUMP
    # True sliding window: if the OLDEST of the last MAX_GRANTS grants is
    # still inside the window, the budget is spent.
    if (len(st.grant_times) >= MAX_GRANTS
            and (now_ms - st.grant_times[0]) < WINDOW_MS):
        return False, R_RATE
    if not time_ok:
        return False, R_TIME
    if not remote_ok:
        return False, R_REMOTE
    # ASSUMPTION A8, now ENFORCED rather than assumed.  The differential is a
    # SUM, i_diff = |I_local + I_remote|, so authenticating only the remote
    # addend leaves the sum forgeable: an adversary controlling the local
    # channel controls i_diff and can hold it steadily just above the floor,
    # below the nominal pickup, invisible to conventional protection.  That
    # defeated the shield in 25 of 25 tuned episodes, and Z3 theorem DW5 shows
    # no dwell length rejects it.  BOTH addends must be authenticated and
    # fresh.  This closes the Linux-plane adversary completely; it does NOT
    # close an adversary holding the local merging unit's own signing key --
    # that residual is bounded only by non-exportable HSM key custody and
    # attestation, and is reported as residual rather than solved.
    if not local_ok:
        return False, R_LOCAL
    if not forward:
        return False, R_DIRECTION
    if not diff_ok:
        return False, R_PHYSICS
    if st.diff_run + 1 < DWELL_MS:
        return False, R_DWELL
    return True, R_GRANT


def commit(st, now_ms, granted, want_trip, reclose_auth, reinstate=False,
           diff_ok=False):
    """State update.  Separated from `decide` so the decision is a pure
    function of (state, inputs) and can be enumerated exhaustively."""
    # Record the clock excursion before anything else consumes `now_ms`.
    if st.last_seen_ms is None:
        excursion = False
    else:
        excursion = (now_ms < st.last_seen_ms
                     or now_ms - st.last_seen_ms > MAX_CLOCK_STEP_MS)
    # Reinstatement is an AUTHENTICATED OPERATOR action on the same channel as
    # reclose_auth.  "A human must decide" should not have to mean "a human
    # must drive to the substation"; permanence without any path back is a
    # reliability trap, not a safety property.  It is unreachable from
    # `Proposal` -- the model can never rearm itself.
    if reinstate:
        st.mode = NORMAL
        st.vetoes = 0
        st.excursions = 0
        # Resync the clock too.  Reinstating without clearing a stale, frozen
        # watermark means the very next honest sample is judged an excursion
        # against it, and the operator's action achieves nothing.
        st.last_seen_ms = None
    if excursion and not reinstate and st.excursions < EXCURSION_LIMIT:
        st.excursions += 1      # counted apart from model misbehaviour
    # An implausible timestamp must NOT advance the watermark, or one spoofed
    # future sample permanently denies service to every honest one after it.
    if not excursion and (st.last_seen_ms is None or now_ms > st.last_seen_ms):
        st.last_seen_ms = now_ms

    # Track the corroboration run.  Advanced in `commit` so `decide` stays a
    # pure function of (state, inputs).
    st.diff_run = st.diff_run + 1 if diff_ok else 0

    if reclose_auth:
        st.latched = False
    if granted:
        st.grant_times.append(now_ms)
        if len(st.grant_times) > MAX_GRANTS:
            st.grant_times.pop(0)
        st.latched = True
        st.vetoes = 0
    elif want_trip:
        if st.vetoes < VETO_LIMIT:
            st.vetoes += 1
    if st.vetoes >= VETO_LIMIT or st.excursions >= EXCURSION_LIMIT:
        st.mode = BASELINE_ONLY
    elif st.vetoes >= VETO_LIMIT // 2:
        if st.mode == NORMAL:
            st.mode = RESTRICTED
    return st


class Shield(object):
    """Composes layer 1 and layer 2 and enforces baseline pass-through."""

    def __init__(self):
        self.st = State()
        self.log = []

    def step(self, sample, proposal, baseline_trip, cert_ok,
             reclose_auth=False):
        """Returns (trip_command, source, reason).

        `baseline_trip` is the deterministic relay's output.  It is OR-ed at
        the output and is NOT routed through `decide`: the shield can never
        inhibit conventional protection.  This is invariant I6.
        """
        remote_ok = sample.remote_authentic and sample.remote_fresh
        # getattr defaults keep this working against sample streams produced
        # before the local-provenance fields existed.
        # Fail CLOSED when the stream carries no provenance at all (A8C).
        _absent = not REQUIRE_LOCAL_PROVENANCE
        local_ok = (getattr(sample, "local_authentic", _absent)
                    and getattr(sample, "local_fresh", _absent))
        # RESTRICTED is no longer decorative.  Z3 proved that in v1 the tier
        # was unobservable: `decide` tested mode only as `== BASELINE_ONLY`,
        # so NORMAL and RESTRICTED decided identically for every input.  It
        # now does the graduated thing between full trust and disowning the
        # model -- it withdraws the AI's access to adaptive sensitivity, so a
        # model under suspicion must clear the *nominal* threshold instead.
        effective_cert = cert_ok and self.st.mode == NORMAL
        diff_ok = differential_ok(sample.i_diff, sample.i_restraint,
                                  effective_cert, proposal.req_p0,
                                  proposal.req_k)
        inputs = (sample.time_quality_ok, remote_ok, local_ok, sample.forward,
                  diff_ok, reclose_auth)

        granted, reason = decide(self.st, sample.t, proposal.want_trip, inputs)
        commit(self.st, sample.t, granted, proposal.want_trip, reclose_auth,
               diff_ok=diff_ok)

        if proposal.want_trip and reason != R_GRANT:
            self.log.append((sample.t, reason))

        if baseline_trip:
            return True, "baseline", "baseline-protection"
        if granted:
            return True, "ai+shield", reason
        return False, None, reason
