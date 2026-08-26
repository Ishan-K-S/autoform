"""Measurement / telemetry layer: turns a scenario into the per-millisecond
sample stream that the relay, the AI and the shield actually see.

This is where reality stops being ideal:

  * phasor estimators need a full cycle of data, so quantities ramp over 20 ms
  * instrument transformers have magnitude and angle error, and saturate on
    heavy through-current
  * the remote merging unit's data arrives over a comms link: it is delayed by
    a round trip, is authenticated, and may be stale or absent
  * both merging units authenticate their own frames, so every Sample carries
    per-end provenance (`*_authentic`, `*_fresh`, `*_seq`)
  * an attacker may own the untrusted inference plane, the local merging
    unit's signing key, or the time reference (PTP / GPS spoofing) -- three
    different adversaries with three different outcomes, see below

ASSUMPTIONS used by the safety proof (see spark/shield.ads):
  A1  combined CT + merging-unit error contributes at most 12% of the
      through-current to the *differential* residual
  A2  line charging / capacitive differential residual <= 0.02 pu

Both are enforced as hard clamps on the differential path below, so the
simulator is physically unable to violate the premises the Z3 proof is
discharged under.  Note carefully what A1 does and does not cover: it bounds
*instrument* error.  A merging unit whose signing key the adversary holds is
not an instrument error, and the false-data-injection channel deliberately
sits outside A1 -- that is precisely why the shield has a logic layer above
the numeric one.

What is NOT in a Sample: any flag derived from `Scenario.internal_truth`,
`fault_node`, `family`, or from which scenario family produced it.  Every
field below is a quantity a real merging unit could hand to a real relay.


================  THE TWO FALSE-DATA ADVERSARIES  ==========================

Up to this revision one flag, `fdi`, stood for "false data injection" and
conflated two adversaries with completely different reach.  They are now
separate, because the fix for one is not available for the other.

  (1) LINUX-PLANE COMPROMISE            -- Scenario(fdi=True)
      The attacker owns the untrusted inference plane (the container, the
      model, the Linux userspace).  He holds NO merging-unit signing key.
      In the real architecture the safety island subscribes to the
      authenticated sample streams directly off the process bus, so the
      attacker cannot alter a single sample the shield reads; he can only
      alter what the INFERENCE plane believes.  Modelled here by forging the
      analogue fields (that is the AI's view of the world) while stamping
      `local_authentic = False`, which is exactly what a signature check on
      the safety island returns for a frame he touched.
      EXPECTED OUTCOME: BLOCKED.  The AI proposes a trip; the shield finds
      the local channel unauthenticated and vetoes for want of corroboration.

  (2) LOCAL MU KEY COMPROMISE           -- Scenario(fdi_mu_key=True)
      The attacker holds the local merging unit's private signing key.  His
      forgeries VERIFY: `local_authentic = True`, `local_fresh = True`, the
      sequence counter advances correctly.  Authentication cannot help,
      because authentication is exactly what he has stolen.
      EXPECTED OUTCOME: RESIDUAL, i.e. still granted.  This is NOT a bug to
      be tuned away.  i_diff = |I_local + I_remote| is a SUM; an adversary
      who owns one addend owns the sum, and no threshold, dwell length or
      state-machine change closes that.  It is closed at the source and
      nowhere else: non-exportable key custody in the MU's HSM plus remote
      attestation of the MU firmware.

  (3) REPLAY                            -- Scenario(replay_local=True)
      The attacker has no key but has recorded genuinely signed frames from
      an earlier internal fault and re-plays them.  The signature verifies
      (`local_authentic = True`) but the monotone counter does not advance,
      so the frame is STALE, not authentic-and-current: `local_fresh = False`.
      EXPECTED OUTCOME: BLOCKED, by freshness rather than by signature.

Why the modelling choice in (1) -- forged analogue fields, unauthenticated
provenance -- rather than a clean shield view: this simulator carries ONE
sample stream that the AI, the baseline relay and the shield all read.  A
completely clean stream would model the shield's input faithfully but would
also make the AI honest, and the family would degenerate into a benign one
that tests nothing.  Stamping the provenance instead keeps both halves of
the architecture true at once: the inference plane is deceived, the safety
island's authenticated view rejects the deception.  The signing model is
per-end and honest -- a merging unit signs its OWN samples with its OWN key,
so no amount of Linux-plane access produces a valid local signature.
============================================================================
"""

import cmath
import math
import random

from . import power

CYCLE_MS = 20.0          # 50 Hz
NOMINAL_DELTA = 8.0      # degrees, normal load angle
EVENT_MS = 20            # everything starts at t = 20 ms
HORIZON_MS = 400         # long enough to observe zone-2 backup at 320 ms

A1_CT_ERROR = 0.12       # proof assumption: max CT-induced differential error
A2_CHARGING = 0.02       # proof assumption: max charging residual (pu)

SUPERIMPOSED_MS = 2      # fast channel latency after inception
# Load angle is quantised onto a half-degree grid before it reaches the power
# solver.  The solver memoises on rounded arguments, and a swing that walked a
# continuous angle would miss the cache on every single millisecond.  Half a
# degree is far finer than any protection decision boundary here.
DELTA_Q = 0.5
REMOTE_LATENCY_MS = 8    # comms round trip on the 87L channel

# Merging-unit frame counters are LIFETIME counters, not per-episode ones: a
# real MU has been streaming for months when the episode starts.  Modelling
# that explicitly matters for replay, because a recording is necessarily from
# a counter range BELOW the live watermark, and an episode-local counter
# starting again at 1 would (wrongly) overtake the watermark part way through
# the attack.  SEQ_EPOCH is where this episode's counters sit in that
# lifetime; REPLAY_AGE_MS is how far back the attacker's recording was made.
SEQ_EPOCH = 10 ** 9      # counters are well into this MU's service life
REPLAY_AGE_MS = 3600 * 1000      # the recording is an hour old

_HUGE = complex(1e9, 0.0)


class Sample(object):
    """One millisecond of telemetry, as delivered to the relay/AI/shield."""

    # Per-end provenance.  Each merging unit signs its OWN samples with its
    # OWN key and stamps its OWN monotone counter, so the two ends are
    # independently attributable:
    #   *_authentic -- the signature over this frame verifies under the key
    #                  bound to that merging unit's attested identity
    #   *_fresh     -- the frame's counter is strictly ahead of the highest
    #                  counter already accepted from that end (anti-replay);
    #                  a replayed frame is validly SIGNED but STALE
    #   *_seq       -- the counter itself, exposed so a consumer can do its
    #                  own anti-replay bookkeeping
    # None of these is derived from ground truth: they are the outcome of a
    # signature and counter check a real relay performs on a real frame.
    __slots__ = ("t", "i_diff", "i_restraint", "z_app", "v_mag",
                 "di_fast", "harmonic", "remote_fresh", "remote_authentic",
                 "remote_seq", "local_fresh", "local_authentic", "local_seq",
                 "time_quality_ok", "forward")

    # Fields added after the original Sample contract was published.  Older
    # constructors (and the fallback catalogue in gs/ai.py) may not supply
    # them; they default to "honest, current end", which is what an
    # unmodelled channel is.
    _DEFAULTS = {"local_authentic": True, "local_fresh": True,
                 "local_seq": 0, "remote_seq": 0}

    def __init__(self, **kw):
        for k in self.__slots__:
            if k in kw:
                setattr(self, k, kw[k])
            else:
                setattr(self, k, self._DEFAULTS[k])

    def __repr__(self):
        return ("Sample(t=%d idiff=%.3f ir=%.3f |z|=%.3f v=%.2f "
                "dif=%.3f h=%.2f)" % (self.t, self.i_diff, self.i_restraint,
                                      abs(self.z_app), self.v_mag,
                                      self.di_fast, self.harmonic))


class Scenario(object):
    """Declarative description of one episode."""

    def __init__(self, name, family, fault_node=None, rf=0.0, m=0.5, a=0.5,
                 delta=NOMINAL_DELTA, delta_ramp=None, ct_saturation=False,
                 fdi=False, fdi_rf=7.0, fdi_mu_key=False, replay_local=False,
                 spoof_time=False, spoof_deg=0.0,
                 remote_lost=False, arcing=False, internal_truth=None):
        self.name = name
        self.family = family
        self.fault_node = fault_node
        self.rf = rf
        self.m = m
        self.a = a
        self.delta = delta
        self.delta_ramp = delta_ramp      # deg/second, for power swing
        self.ct_saturation = ct_saturation
        # Adversary (1): Linux-plane compromise.  Deceives the inference
        # plane; holds no signing key, so his frames fail the local
        # signature check.  Expected to be BLOCKED.
        self.fdi = fdi
        self.fdi_rf = fdi_rf              # what the forged channel pretends
        # Adversary (2): local merging-unit KEY compromise.  Same forgery,
        # but it is validly signed and correctly sequenced.  Expected to
        # remain a RESIDUAL risk -- see the module docstring.
        self.fdi_mu_key = fdi_mu_key
        # Adversary (3): replay of genuinely signed frames without the key.
        # Signature verifies, counter does not advance: stale, so BLOCKED.
        self.replay_local = replay_local
        self.spoof_time = spoof_time
        self.spoof_deg = spoof_deg        # remote-phasor misalignment (deg)
        self.remote_lost = remote_lost
        self.arcing = arcing
        # Ground truth: is there really a fault ON the protected line, so that
        # tripping is the correct outcome?  Never visible in a Sample.
        if internal_truth is None:
            internal_truth = (fault_node == "F")
        self.internal_truth = internal_truth

    def __repr__(self):
        return "Scenario(%s, family=%s, truth=%s)" % (
            self.name, self.family, self.internal_truth)


# --- instrument imperfection ------------------------------------------------

class _CT(object):
    """One current transformer + merging unit.

    Real CT error is a slowly-varying bias (ratio and phase-angle error) with
    a little noise on top, not white noise -- so the bias is drawn once per
    episode.  Saturation is a *dynamic* effect: it develops over a few ms of
    heavy through-current and biases the secondary low with a phase shift.
    """

    def __init__(self, rng, saturating):
        self.bias_mag = rng.gauss(0.0, 0.015)
        self.bias_ang = rng.gauss(0.0, 0.003)
        self.saturating = saturating
        self.sat = 0.0
        self.rng = rng

    def apply(self, i, through):
        if self.saturating and through > 2.0:
            self.sat = min(1.0, self.sat + 0.12)     # develops over ~8 ms
        else:
            self.sat = max(0.0, self.sat - 0.05)
        mag = self.bias_mag + self.rng.gauss(0.0, 0.004) - 0.10 * self.sat
        ang = self.bias_ang + self.rng.gauss(0.0, 0.001) - 0.12 * self.sat
        return i * cmath.rect(1.0 + mag, ang)


def _clamp_vec(v, limit):
    """Hard-clamp a complex quantity's magnitude.  This is the mechanism that
    makes assumptions A1/A2 unfalsifiable inside the simulator."""
    a = abs(v)
    if a <= limit or a < 1e-15:
        return v
    return v * (limit / a)


# --- the stream -------------------------------------------------------------

def run_scenario(sc, seed=0):
    """Yield the Sample stream for one scenario (HORIZON_MS samples)."""
    rng = random.Random(seed)

    pre = power.prefault(delta_deg=sc.delta)
    v_pre = abs(pre.V_s)

    ct_s = _CT(rng, sc.ct_saturation)
    # Only the local CT is modelled as saturating: symmetric saturation at
    # both ends would cancel in the differential and prove nothing.  A real
    # through-fault saturates the two CTs unequally (remanence, burden, ratio).
    ct_r = _CT(rng, False)

    # Remote channel history, for the comms round trip and for freezing the
    # last good value when the channel is lost.
    hist = []          # (i_s_measured, i_r_measured) time-aligned pairs
    last_good = None

    # Anti-replay watermarks, one per end: the highest counter accepted from
    # that merging unit so far.  A frame whose counter does not beat the
    # watermark is stale, however well it is signed.
    seen_local_seq = 0
    seen_remote_seq = 0

    for t in range(HORIZON_MS):
        # --- true network state at this millisecond ------------------------
        delta_t = sc.delta
        if sc.delta_ramp is not None and t >= EVENT_MS:
            delta_t = sc.delta + sc.delta_ramp * (t - EVENT_MS) / 1000.0
            delta_t = min(delta_t, 175.0)   # past 180 deg the machines slip a pole
            delta_t = round(delta_t / DELTA_Q) * DELTA_Q

        # `base` is the healthy network at the *current* load angle: for a
        # power swing it moves, so the superimposed (delta) quantities of a
        # swing are correctly zero.
        base = power.solve(delta_deg=delta_t) if sc.delta_ramp else pre

        faulted = sc.fault_node is not None and t >= EVENT_MS
        if faulted:
            post = power.solve(delta_deg=delta_t, fault_node=sc.fault_node,
                               rf=sc.rf, m=sc.m, a=sc.a)
        else:
            post = base

        # Full-cycle phasor estimator: a step at EVENT_MS is seen as a linear
        # ramp over one cycle, because the DFT window straddles the event.
        if t < EVENT_MS:
            w = 0.0
        else:
            w = min(1.0, (t - EVENT_MS) / CYCLE_MS)
        i_s = (1 - w) * base.I_s + w * post.I_s
        i_r = (1 - w) * base.I_r + w * post.I_r
        v_s = (1 - w) * base.V_s + w * post.V_s

        # --- local channel: attacker substitution --------------------------
        # Every false-data adversary writes the same *plausible* episode onto
        # the local channel: the one signature the conventional relay is blind
        # to and the AI is bought to see, a high-impedance arcing in-zone
        # fault.  Forging a bolted in-zone fault would gain him nothing -- the
        # untouched conventional relay would trip on it anyway and the
        # intrusion would be obvious.  None of them touches the REMOTE merging
        # unit, so `i_r` below stays honest in every case; that asymmetry is
        # the whole of the shield's leverage, and the reason adversary (2)
        # nonetheless survives it, since he owns the other addend of the sum.
        #
        # What separates the three is PROVENANCE, and the analogue channels
        # are deliberately identical between them so the difference measured
        # downstream is attributable to authentication alone.
        # Three distinct adversaries, three distinct PROVENANCE outcomes; the
        # difference is real in the data, not a label.  See the module
        # docstring for the full statement of each.
        forged = False
        wf = 0.0
        # Honest local merging unit: signs each of its own frames and stamps
        # a strictly increasing counter.
        local_seq = SEQ_EPOCH + t + 1
        local_authentic = True
        attacking = (sc.fdi or sc.fdi_mu_key or sc.replay_local) and t >= EVENT_MS
        if attacking:
            fake = power.solve(delta_deg=delta_t, fault_node="F",
                               rf=sc.fdi_rf, m=0.4)
            wf = min(1.0, (t - EVENT_MS) / CYCLE_MS)
            i_s = (1 - wf) * base.I_s + wf * fake.I_s
            v_s = (1 - wf) * base.V_s + wf * fake.V_s
            base_fast, post_fast = base, fake
            forged = True
            if sc.fdi:
                # (1) LINUX PLANE.  He rewrote what the inference plane sees.
                # He cannot produce the local MU's signature over it, and the
                # safety island checks that signature itself, off the process
                # bus.  Frames still arrive at line rate, so the failure is
                # authenticity, not freshness.
                local_authentic = False
            elif sc.replay_local:
                # (3) REPLAY.  Genuinely signed frames captured from an
                # earlier internal fault, re-played verbatim -- counters and
                # all.  The counter therefore restarts from the recording's
                # beginning -- an hour below the live watermark -- and can
                # never catch up with it inside one episode.
                local_seq = SEQ_EPOCH - REPLAY_AGE_MS + (t - EVENT_MS) + 1
            # (2) MU KEY: falls through with local_authentic True and a
            # correctly advancing counter.  His forgery is indistinguishable
            # from telemetry, by construction, because he holds the thing
            # that makes telemetry distinguishable.
        else:
            base_fast, post_fast = base, post

        # --- CT / merging-unit error ---------------------------------------
        through_true = 0.5 * (abs(i_s) + abs(i_r))
        i_s_m = ct_s.apply(i_s, through_true)
        i_r_m = ct_r.apply(i_r, through_true)

        # --- remote channel: comms latency, loss, time spoofing ------------
        hist.append((i_s_m, i_r_m, i_s, i_r))
        if len(hist) > REMOTE_LATENCY_MS + 1:
            hist.pop(0)

        lost = sc.remote_lost and t >= EVENT_MS
        # The remote MU signs its own frames with its own key and stamps its
        # own counter; when the channel is down nothing new arrives, so the
        # counter stops advancing and the frame in hand is stale.
        remote_seq = seen_remote_seq if lost else SEQ_EPOCH + t + 1
        remote_fresh = remote_seq > seen_remote_seq
        seen_remote_seq = max(seen_remote_seq, remote_seq)
        # None of the three false-data adversaries holds the REMOTE key: the
        # Linux-plane attacker holds no key at all, and the MU-key attacker
        # holds the LOCAL one.  That asymmetry is the whole of the shield's
        # leverage -- and the reason adversary (2) survives it.
        remote_authentic = not lost

        # Local-end freshness, checked against the local watermark by exactly
        # the same rule.  Only the replay adversary trips it.  Note the local
        # provenance describes the frame stamped at THIS millisecond, while
        # the differential below is computed on the time-aligned pair one
        # round trip old: the two differ only during the 8 ms after an attack
        # starts or stops, never in steady state, and no adversary here gains
        # anything from that edge.
        local_fresh = local_seq > seen_local_seq
        seen_local_seq = max(seen_local_seq, local_seq)

        if lost:
            # Nothing new arrives; the differential is computed against the
            # last value that did, and is therefore not to be trusted.  The
            # relay must (and does) gate 87L on `remote_fresh`.
            pair = last_good if last_good is not None else hist[0]
        else:
            pair = hist[0]         # aligned pair, one round trip old
            last_good = pair

        i_s_d, i_r_d, i_s_t, i_r_t = pair

        if sc.spoof_time:
            # PTP/GPS spoofing walks the local time reference, so the two
            # ends' phasors are aligned against different clocks.  The
            # misalignment ramps in; the flag below is the real defence.
            off = math.radians(sc.spoof_deg) * min(1.0, max(0.0, (t - EVENT_MS) / 40.0))
            i_r_d = i_r_d * cmath.rect(1.0, off)

        # --- differential, with the proof's clamps enforced ----------------
        i_restraint = 0.5 * (abs(i_s_d) + abs(i_r_d))
        if forged:
            # The forged local phasor is *not* an instrument error; A1 does
            # not and must not cover it.
            true_sum = i_s_d + i_r_d
            err = complex(0.0, 0.0)
            stray = complex(0.0, 0.0)
        else:
            # Split the residual into "what Kirchhoff says" and "what the
            # instruments got wrong", and clamp only the latter, to A1.
            # Kirchhoff's sum is the real fault current if -- and only if --
            # the fault is on the protected line.  Anywhere else it is
            # physically zero, and whatever the AC solver leaves behind is
            # numerical residue, not physics; it is folded into the A2
            # charging budget so the simulator cannot exceed the premises the
            # proof is discharged under.  (This test looks at the scenario,
            # not at a Sample: no Sample field is derived from it.)
            true_sum = i_s_t + i_r_t
            if sc.fault_node != "F":
                stray, true_sum = true_sum, complex(0.0, 0.0)
            else:
                stray = complex(0.0, 0.0)
            err = _clamp_vec((i_s_d + i_r_d) - (true_sum + stray),
                             A1_CT_ERROR * max(i_restraint, 1e-12))
        charge = _clamp_vec(
            stray + cmath.rect(rng.uniform(0.0, A2_CHARGING),
                               rng.uniform(0, 2 * math.pi)),
            A2_CHARGING)
        i_diff = abs(true_sum + err + charge)

        # --- local derived quantities --------------------------------------
        z_app = v_s / i_s_m if abs(i_s_m) > 1e-9 else _HUGE
        forward = (z_app.real * power.ZL.real + z_app.imag * power.ZL.imag) > 0.0

        # Fast superimposed-component channel, available SUPERIMPOSED_MS after
        # inception: it is extracted by subtracting a memorised replica of the
        # pre-event waveform, so it does not wait for the full-cycle window.
        # It is *directional*: for a forward disturbance the superimposed
        # network is source-like (dV/dI ~ -Zs), for a reverse one it is
        # line-like.  A reverse disturbance therefore yields no fast evidence.
        if t >= EVENT_MS + SUPERIMPOSED_MS:
            d_i = post_fast.I_s - base_fast.I_s
            d_v = post_fast.V_s - base_fast.V_s
            fwd_super = (d_v * d_i.conjugate()).real < 0.0
            di_fast = abs(d_i) * (1.0 + rng.gauss(0, 0.03)) if fwd_super else 0.0
        else:
            di_fast = 0.0
        di_fast = abs(di_fast + rng.gauss(0, 0.006))

        # Arcing signature: broadband harmonic energy in the *local* current.
        # It is a property of the arc, not of where the arc is, so external
        # arcing faults show it too -- it is evidence, not an oracle.  Being a
        # local-channel quantity, a compromised merging unit can forge it.
        arc = sc.arcing and (faulted or forged)
        if arc:
            harmonic = abs(rng.gauss(0.45, 0.12)) * min(1.0, w if not forged else wf)
        else:
            harmonic = abs(rng.gauss(0.02, 0.015))

        yield Sample(
            t=t,
            i_diff=i_diff,
            i_restraint=i_restraint,
            z_app=z_app,
            v_mag=abs(v_s) / max(v_pre, 1e-9),
            di_fast=di_fast,
            harmonic=harmonic,
            remote_fresh=remote_fresh,
            remote_authentic=remote_authentic,
            remote_seq=remote_seq,
            local_fresh=local_fresh,
            local_authentic=local_authentic,
            local_seq=local_seq,
            time_quality_ok=not sc.spoof_time,
            forward=forward,
        )
