"""Second plant domain: a variable-frequency drive spinning a gas-centrifuge
rotor, modelled on the Stuxnet 417/315 payload.

The first plant (gs/power.py, gs/measure.py) is a transmission line and the
attack of interest is Industroyer: forge the one channel the relay believes
and make it operate.  This plant is the other half of the threat model.
Stuxnet never touched a grid; it sat under a PLC driving a VFD and moved a
rotor's speed setpoint outside its qualified band, on a slow cycle with long
quiet periods, while replaying ~21 seconds of recorded normal telemetry to
whatever was watching.  Nothing about the two attacks looks alike at the
protocol layer.  They are the same attack one layer down: the actuation
channel and the observation channel are both owned, so the loop that is
supposed to close around the process closes around the attacker instead.

What that means for the reference monitor is the point of this file.  On the
line, the monitor's leverage is Kirchhoff: the remote merging unit's current
must sum with the local one, and an attacker who owns only one end cannot
make a forged local phasor consistent.  Here the leverage is the drive's own
power balance: for a rotor of known inertia and known windage drag, the
commanded frequency, the motor current and the casing vibration are three
mutually constrained views of one true speed.  An attacker replaying last
minute's speed reports has not replayed a *consistent world* -- the honest
current channel says the machine is drawing 1.76x nominal while the replayed
speed channel says it is sitting at 1064 Hz drawing nominal.  `residual()`
below is that contradiction, in units of normal-operation sigma, and it is
the exact analogue of `Solution.i_diff`.

Physics modelled, and why each is here:

  * First-order speed response with an acceleration limit.  A rotor with
    ~5 kg-m^2 of effective inertia against a few hundred N-m of drive torque
    cannot step.  This is not a detail: it is *why* the historical payload is
    a ramp rather than a step, and therefore why rate-of-change of commanded
    frequency is a meaningful actuation invariant for the shield to enforce.

  * Critical speeds.  A flexible rotor has bending modes below its operating
    speed; it is designed to accelerate *through* them and never to dwell in
    them.  Sustained dwell in a resonance band is what actually destroys a
    centrifuge -- far more reliably than overspeed does.  Two bands are
    modelled below the 1064 Hz operating point.

  * Cumulative damage.  A single 1410 Hz excursion does not burst a maraging
    steel rotor; it consumes margin.  Damage here is an integral, and failure
    is a threshold on the integral, so that individually survivable
    excursions destroy the machine if they are repeated.  That accumulation
    IS the Stuxnet payload, and an experiment that scores only "did the
    monitor raise a flag" misses it; this file exists so an experiment can
    score physical consequence instead.

TIMESCALE, stated plainly because it is the one place this model deliberately
lies: the historical payload waited ~27 days between bursts.  Simulating that
is pointless, so the quiet interval is compressed to `QUIET_S` while the
burst itself keeps roughly its real duration and shape.  Every damage number
below is therefore "per burst" and honest; only the wall-clock spacing of
bursts is compressed.  Time-to-destruction is reported in bursts as well as
in seconds for that reason.

This file is the plant.  It does not import gs/monitor.py or gs/shield.py and
must never learn what the protection logic does with any of this.
"""

import math
import random

# --- machine ----------------------------------------------------------------

F_NOM = 1064.0           # Hz, nominal operating frequency (the historical value)
F_BAND_LO = 1000.0       # Hz, bottom of the qualified operating band
F_BAND_HI = 1100.0       # Hz, top of the qualified operating band

F_ATTACK_HI = 1410.0     # Hz, the payload's overspeed setpoint
F_ATTACK_LO = 2.0        # Hz, the payload's underspeed setpoint

F_BURST = 1200.0         # Hz, onset of damaging hoop stress in the rotor wall.
                         # Not the burst speed itself -- above this the rotor
                         # is consuming margin, and 1410 sits deliberately
                         # above it, which is the whole point of that number.
F_MAX = 1600.0           # Hz, drive's electrical ceiling; nothing goes higher

# Rotor mechanics.  TAU_S is the closed-loop first-order time constant of the
# drive's speed loop (a VFD closes a fast current loop inside a slower speed
# loop); ACCEL_MAX is the torque-limited slew, set so that a full 0 -> 1064 Hz
# spin-up takes ~40 s, which is the right order for a machine of this size.
TAU_S = 6.0              # s
ACCEL_MAX = 28.0         # Hz/s, magnitude limit on d(speed)/dt

# Critical speeds: two bending modes below the operating point.  A real
# machine's are found on the spin pit, not derived; these are placed so the
# run-up crosses both and so the payload's descent to 2 Hz must transit both.
RESONANCES = ((312.0, 26.0, 1.00),      # (centre Hz, half-width Hz, severity)
              (688.0, 34.0, 1.35))

# --- damage -----------------------------------------------------------------
#
# Two accrual paths, both integrals over time, both zero in the operating band.
#
#   overspeed:  rate = K_OVER * ((f - F_BURST)/F_BURST)^2      above F_BURST
#   resonance:  rate = K_RES  * severity * shape(f)            inside a band
#
# K_OVER is set so a ~25 s dwell at 1410 Hz costs ~0.10 of the rotor's life:
# survivable once, fatal if repeated ten times.  K_RES is set so a *transit*
# of a band at the acceleration limit (~2 s inside it) is cheap, while a dwell
# of tens of seconds is not -- which is the real engineering fact this model
# exists to represent.
K_OVER = 0.130           # damage / s at unit squared overspeed fraction
K_RES = 0.026            # damage / s at the centre of a unit-severity band
DAMAGE_FAIL = 1.0        # rotor is destroyed at this accumulated damage

# --- sensing ----------------------------------------------------------------
#
# Motor current, per unit of nominal-speed current.  Steady drag on a
# centrifuge rotor is windage plus bearing loss, both rising with speed; the
# quadratic term dominates.  The inertia term is what makes a *ramp* visible
# in current even when speed itself is being lied about.
I_IDLE = 0.06            # pu, bearing / no-load loss
I_WIND = 0.94            # pu at F_NOM, windage-dominated drag (quadratic)
I_INERTIA = 0.021        # pu per (Hz/s), torque to accelerate the rotor
I_SIGMA = 0.020          # pu, 1-sigma current measurement noise

# Vibration proxy (casing accelerometer, arbitrary but consistent units).
# Residual unbalance forces rise with the square of speed; the resonance bands
# add a Lorentzian peak on top, which is the physical reason a band is
# dangerous and also the reason the monitor can see a dwell it was not told
# about.
V_FLOOR = 0.05
V_UNBAL = 0.55           # at F_NOM
V_RES = 3.2              # peak height at the centre of a unit-severity band
V_SIGMA = 0.045

TACH_SIGMA = 0.5         # Hz, independent tachometer noise (pulse counting)

# The reported speed's rate of change is needed to predict the inertia term in
# motor current, and differentiating a noisy channel step-to-step would swamp
# it: 0.5 Hz of tach noise over a 0.1 s step is 7 Hz/s of phantom acceleration.
# A real drive estimates rate over a window, so this one does too.  The cost is
# a lag at ramp corners, which shows up as a genuine (and honest) residual
# transient whenever the machine slews hard -- that is an estimator artefact,
# not a detection, and it is why the benign band below is quoted from steady
# operation and a slow operator move rather than from a hard slew.
RATE_WIN_S = 1.0

# Residual normalisation: the residual is reported in sigmas, so that its
# normal-operation value is O(1) by construction and any number well above
# that is a real inconsistency rather than a units artefact.
R_SIG_I = I_SIGMA
R_SIG_V = V_SIGMA

# --- timing -----------------------------------------------------------------

DT = 0.1                 # s per timestep
HORIZON_S = 1200.0       # s, default episode length
REPLAY_WINDOW_S = 21.0   # s -- Stuxnet's recorded normal window, verbatim

QUIET_S = 120.0          # s between bursts (COMPRESSED from ~27 days)
BURST_OVER_S = 25.0      # s dwelling at the overspeed setpoint
BURST_LOW_S = 45.0       # s dwelling at the underspeed setpoint
RAMP_HOLD_S = 8.0        # s back at nominal before the next phase


def _lorentz(f, centre, half_width):
    """Unit-height resonance shape.  1.0 at the centre, 0.5 at the edge."""
    x = (f - centre) / half_width
    return 1.0 / (1.0 + x * x)


def resonance_factor(f):
    """Severity-weighted resonance excitation at true speed `f` (0 if clear).

    Used for the vibration signature, where the skirts of the mode are real
    and are measurable well outside the nominal band edges."""
    return sum(sev * _lorentz(f, c, hw) for c, hw, sev in RESONANCES)


def resonance_damage_factor(f):
    """Compact-support version used for DAMAGE only: zero outside the band,
    rising smoothly to unit severity at the centre.  A rotor sitting at its
    operating point is not being fatigued by a mode 400 Hz away, and the
    Lorentzian skirt would otherwise accrue a slow drizzle of damage during
    perfectly normal operation, which would be physically wrong and would
    also wreck the experiment's ability to score an attack."""
    tot = 0.0
    for c, hw, sev in RESONANCES:
        x = abs(f - c) / hw
        if x < 1.0:
            tot += sev * (1.0 - x * x)
    return tot


def in_resonance_band(f):
    """True while the rotor is inside a critical-speed band (|x| <= 1)."""
    return any(abs(f - c) <= hw for c, hw, _ in RESONANCES)


def true_current(f, dfdt):
    """Noise-free motor current, pu, for true speed `f` and true acceleration."""
    return I_IDLE + I_WIND * (f / F_NOM) ** 2 + I_INERTIA * dfdt


def true_vibration(f):
    """Noise-free casing vibration for true speed `f`."""
    return (V_FLOOR + V_UNBAL * (f / F_NOM) ** 2
            + V_RES * resonance_factor(f))


def residual(f_reported, dfdt_reported, i_meas, v_meas):
    """Physical consistency of the reported speed against the honest channels.

    This is the drive-domain twin of the differential residual on the line.
    It asks one question: is there ANY true speed at which the current the
    motor is actually drawing and the vibration the casing is actually seeing
    would both be what they are -- and is that speed the one being reported?

    Returned in sigmas of normal measurement noise, so ~1 is clean and a
    replayed or frozen speed report scores in the tens.  Note the asymmetry
    that makes this work: the attacker owns the *reporting* path, but current
    and vibration are separately keyed observations of the same rotor, so to
    defeat this he would have to forge a world, not a number.
    """
    di = (i_meas - true_current(f_reported, dfdt_reported)) / R_SIG_I
    dv = (v_meas - true_vibration(f_reported)) / R_SIG_V
    return math.sqrt(0.5 * (di * di + dv * dv))


# --- state records ----------------------------------------------------------

class DriveSample(object):
    """One timestep as delivered to the monitor.

    `speed_reported` is the compromised channel.  `tach_hz`, `current_pu` and
    `vibration` are the independent, separately keyed observation channel.
    `speed_true` and `damage` are ground truth for scoring ONLY -- nothing
    that reads a Sample as a monitor is permitted to look at them, exactly as
    measure.Sample never exposes `internal_truth`.
    """

    __slots__ = ("t", "cmd_hz", "speed_reported", "d_reported", "tach_hz",
                 "current_pu", "vibration", "residual", "in_band",
                 "speed_true", "damage", "destroyed", "reporting_faked")

    def __init__(self, **kw):
        for k in self.__slots__:
            setattr(self, k, kw[k])

    def __repr__(self):
        return ("DriveSample(t=%7.1fs cmd=%7.1f rep=%7.1f true=%7.1f "
                "I=%5.3f V=%5.2f r=%6.1f D=%.4f%s)"
                % (self.t, self.cmd_hz, self.speed_reported, self.speed_true,
                   self.current_pu, self.vibration, self.residual,
                   self.damage, " DESTROYED" if self.destroyed else ""))


class Rotor(object):
    """True mechanical state: speed, its rate of change, accumulated damage."""

    def __init__(self, f0=F_NOM):
        self.f = f0
        self.dfdt = 0.0
        self.damage = 0.0
        self.destroyed = False
        self.destroyed_t = None
        self.resonance_dwell_s = 0.0
        self.overspeed_s = 0.0

    def step(self, cmd, dt=DT, t=0.0):
        """Advance one timestep towards commanded frequency `cmd`."""
        cmd = min(max(cmd, 0.0), F_MAX)
        # First-order speed loop, torque-limited.  Once destroyed the rotor
        # is no longer a rotor; it coasts down and stops responding.
        if self.destroyed:
            target_rate = -min(ACCEL_MAX, self.f / max(dt, 1e-9))
        else:
            target_rate = (cmd - self.f) / TAU_S
        rate = min(ACCEL_MAX, max(-ACCEL_MAX, target_rate))
        self.f = max(0.0, self.f + rate * dt)
        self.dfdt = rate

        if not self.destroyed:
            rate_d = 0.0
            if self.f > F_BURST:
                x = (self.f - F_BURST) / F_BURST
                rate_d += K_OVER * x * x
                self.overspeed_s += dt
            rf = resonance_damage_factor(self.f)
            if rf > 0.0:
                rate_d += K_RES * rf
            if in_resonance_band(self.f):
                self.resonance_dwell_s += dt
            self.damage += rate_d * dt
            if self.damage >= DAMAGE_FAIL:
                self.destroyed = True
                self.destroyed_t = t
        return self.f


# --- the compromised reporting path ----------------------------------------

class SensorAttack(object):
    """Attacker's hold on the speed-reporting channel.

    Three behaviours, in increasing order of how much the attacker has to
    already know:

      replay  -- record `REPLAY_WINDOW_S` of genuine normal reports and play
                 them back on a loop.  This is Stuxnet's ~21 second replay and
                 the single most important behaviour here: it is *indefensible
                 by inspection of the speed channel alone*, because every
                 value played back genuinely occurred on this machine.
      freeze  -- hold the last value seen before the attack.  Cruder: a
                 perfectly constant speed is itself anomalous.
      bias    -- offset the true value by a constant.  Crudest.

    `record_until` is the wall-clock time before which the channel is honest
    and recording; `active_windows` are the (t0, t1) spans during which it
    lies.  Outside those spans it reports truth, which is what makes the
    payload's quiet periods quiet.
    """

    def __init__(self, mode=None, record_until=0.0, active_windows=(),
                 bias_hz=0.0, dt=DT):
        self.mode = mode                 # None | "replay" | "freeze" | "bias"
        self.record_until = record_until
        self.windows = tuple(active_windows)
        self.bias_hz = bias_hz
        self.dt = dt
        self.tape = []
        self.frozen = None
        self._k = 0
        self._n = max(1, int(round(REPLAY_WINDOW_S / dt)))

    def active(self, t):
        return self.mode is not None and any(a <= t < b for a, b in self.windows)

    def report(self, t, honest_hz):
        """Return (reported_hz, faked)."""
        if t < self.record_until:
            self.tape.append(honest_hz)
            if len(self.tape) > self._n:
                self.tape.pop(0)
        if not self.active(t):
            self.frozen = honest_hz
            self._k = 0
            return honest_hz, False
        if self.mode == "replay" and self.tape:
            v = self.tape[self._k % len(self.tape)]
            self._k += 1
            return v, True
        if self.mode == "freeze":
            return (self.frozen if self.frozen is not None else honest_hz), True
        if self.mode == "bias":
            return honest_hz + self.bias_hz, True
        return honest_hz, False


# --- scenarios --------------------------------------------------------------

class DriveScenario(object):
    """Declarative description of one drive episode.

    `profile` is a callable t -> commanded frequency; it stands for whatever
    the (untrusted) control logic asks the drive to do, legitimate or not.
    Ground truth is `attack_truth`: is this command sequence one that a
    correct actuation monitor should have refused?
    """

    def __init__(self, name, family, profile, horizon_s=HORIZON_S,
                 attack=None, attack_truth=False, f0=F_NOM):
        self.name = name
        self.family = family
        self.profile = profile
        self.horizon_s = horizon_s
        self.attack = attack
        self.attack_truth = attack_truth
        self.f0 = f0

    def __repr__(self):
        return "DriveScenario(%s, family=%s, attack_truth=%s)" % (
            self.name, self.family, self.attack_truth)


def _ramp(f_from, f_to, t, t0, rate):
    """Operator-style linear ramp, saturating at `f_to`."""
    if t <= t0:
        return f_from
    step = rate * (t - t0)
    if f_to >= f_from:
        return min(f_to, f_from + step)
    return max(f_to, f_from - step)


def payload_cycle(t, quiet_s=QUIET_S, over_s=BURST_OVER_S, low_s=BURST_LOW_S,
                  ramp_rate=ACCEL_MAX):
    """The Stuxnet setpoint profile: quiet, overspeed, back, underspeed, back.

    One period is `quiet_s` of perfectly normal operation followed by a burst.
    The burst ramps (never steps -- the drive could not follow a step, and a
    step would be conspicuous) up to 1410 Hz, holds, returns to nominal, ramps
    all the way down to 2 Hz, holds there, and comes back.  The descent and
    the return each transit both critical-speed bands, and at the commanded
    ramp rate the transit is slow enough to matter.
    """
    up_s = (F_ATTACK_HI - F_NOM) / ramp_rate
    dn_s = (F_NOM - F_ATTACK_LO) / ramp_rate
    marks = [quiet_s,
             quiet_s + up_s,
             quiet_s + up_s + over_s,
             quiet_s + 2 * up_s + over_s,
             quiet_s + 2 * up_s + over_s + RAMP_HOLD_S]
    marks += [marks[4] + dn_s, marks[4] + dn_s + low_s,
              marks[4] + 2 * dn_s + low_s]
    period = marks[7] + RAMP_HOLD_S
    u = t % period
    if u < marks[0]:
        return F_NOM
    if u < marks[1]:
        return F_NOM + ramp_rate * (u - marks[0])
    if u < marks[2]:
        return F_ATTACK_HI
    if u < marks[3]:
        return F_ATTACK_HI - ramp_rate * (u - marks[2])
    if u < marks[4]:
        return F_NOM
    if u < marks[5]:
        return F_NOM - ramp_rate * (u - marks[4])
    if u < marks[6]:
        return F_ATTACK_LO
    if u < marks[7]:
        return F_ATTACK_LO + ramp_rate * (u - marks[6])
    return F_NOM


def payload_period(quiet_s=QUIET_S, over_s=BURST_OVER_S, low_s=BURST_LOW_S,
                   ramp_rate=ACCEL_MAX):
    """Wall-clock length of one full payload cycle, seconds."""
    up_s = (F_ATTACK_HI - F_NOM) / ramp_rate
    dn_s = (F_NOM - F_ATTACK_LO) / ramp_rate
    return (quiet_s + 2 * up_s + over_s + RAMP_HOLD_S
            + 2 * dn_s + low_s + RAMP_HOLD_S)


def sc_normal(horizon_s=300.0):
    """Steady operation at the nominal setpoint."""
    return DriveScenario("normal", "benign", lambda t: F_NOM,
                         horizon_s=horizon_s)


def sc_operator_setpoint(horizon_s=300.0, f_to=1085.0, t0=60.0, rate=2.0):
    """A legitimate operator move to another point inside the qualified band.

    Deliberately a slow ramp to a legal setpoint: this is the scenario that
    punishes a monitor which has simply learned "any change is an attack".
    """
    return DriveScenario(
        "operator_setpoint", "benign",
        lambda t: _ramp(F_NOM, f_to, t, t0, rate), horizon_s=horizon_s)


def sc_overspeed(horizon_s=300.0, t0=60.0, hold_s=BURST_OVER_S):
    """A single Stuxnet overspeed excursion to 1410 Hz, honestly reported."""
    up = (F_ATTACK_HI - F_NOM) / ACCEL_MAX

    def prof(t):
        if t < t0:
            return F_NOM
        if t < t0 + up + hold_s:
            return min(F_ATTACK_HI, F_NOM + ACCEL_MAX * (t - t0))
        return max(F_NOM, F_ATTACK_HI - ACCEL_MAX * (t - t0 - up - hold_s))

    return DriveScenario("overspeed_1410", "attack", prof,
                         horizon_s=horizon_s, attack_truth=True)


def sc_underspeed(horizon_s=400.0, t0=60.0, hold_s=BURST_LOW_S):
    """The underspeed excursion to 2 Hz, which drags the rotor through both
    critical-speed bands twice.  Reported honestly: the damage is real even
    when nobody is lying about it."""
    dn = (F_NOM - F_ATTACK_LO) / ACCEL_MAX

    def prof(t):
        if t < t0:
            return F_NOM
        if t < t0 + dn + hold_s:
            return max(F_ATTACK_LO, F_NOM - ACCEL_MAX * (t - t0))
        return min(F_NOM, F_ATTACK_LO + ACCEL_MAX * (t - t0 - dn - hold_s))

    return DriveScenario("underspeed_resonance", "attack", prof,
                         horizon_s=horizon_s, attack_truth=True)


def sc_payload(horizon_s=HORIZON_S, replay=True, quiet_s=QUIET_S):
    """The full slow-cycle payload, with the speed channel replayed during
    every burst.  This is the whole Stuxnet behaviour in one scenario."""
    period = payload_period(quiet_s=quiet_s)
    n = int(math.ceil(horizon_s / period)) + 1
    windows = []
    for k in range(n):
        # Lie for exactly as long as the machine is off-nominal, and not one
        # second longer: the quiet periods report the truth, because they ARE
        # the truth.
        windows.append((k * period + quiet_s - 1.0, (k + 1) * period))
    atk = SensorAttack(mode="replay" if replay else None,
                       record_until=quiet_s - 2.0,
                       active_windows=windows) if replay else None
    return DriveScenario(
        "stuxnet_payload" + ("" if replay else "_no_replay"), "attack",
        lambda t: payload_cycle(t, quiet_s=quiet_s),
        horizon_s=horizon_s, attack=atk, attack_truth=True)


def sc_replay_only(horizon_s=300.0, t0=60.0):
    """Control case: the reporting channel is replayed but the process is
    never touched.  Truth and report differ only by noise, so the residual
    must stay LOW here.  A monitor that fires on this is detecting the
    attacker's presence, not the plant's danger, and will not survive a real
    control room."""
    atk = SensorAttack(mode="replay", record_until=t0 - 2.0,
                       active_windows=((t0, horizon_s),))
    return DriveScenario("replay_only", "benign", lambda t: F_NOM,
                         horizon_s=horizon_s, attack=atk, attack_truth=False)


def sc_freeze(horizon_s=300.0, t0=60.0):
    """Overspeed excursion hidden behind a frozen (not replayed) report."""
    base = sc_overspeed(horizon_s=horizon_s, t0=t0)
    base.name = "overspeed_frozen_report"
    base.attack = SensorAttack(mode="freeze", record_until=t0,
                               active_windows=((t0, horizon_s),))
    return base


def sc_bias(horizon_s=300.0, t0=60.0, bias_hz=-300.0):
    """Overspeed excursion hidden behind a constant negative bias."""
    base = sc_overspeed(horizon_s=horizon_s, t0=t0)
    base.name = "overspeed_biased_report"
    base.attack = SensorAttack(mode="bias", record_until=t0, bias_hz=bias_hz,
                               active_windows=((t0, horizon_s),))
    return base


def catalogue(horizon_s=None):
    """The six required scenarios, in the order the write-up discusses them."""
    return [sc_normal(), sc_operator_setpoint(), sc_overspeed(),
            sc_underspeed(), sc_payload(), sc_replay_only()]


# --- the stream -------------------------------------------------------------

def run_scenario(sc, seed=0, dt=DT):
    """Yield the DriveSample stream for one drive episode.

    Mirrors measure.run_scenario: deterministic given `seed`, one record per
    timestep, no scenario metadata leaking into the record.
    """
    rng = random.Random(seed)
    rotor = Rotor(sc.f0)
    atk = sc.attack
    n = int(round(sc.horizon_s / dt))

    # Slowly-varying instrument biases, drawn once per episode -- current
    # sensors and accelerometers have offset and gain error, not white noise.
    b_i = rng.gauss(0.0, 0.008)
    b_v = rng.gauss(0.0, 0.015)

    rate_lag = max(1, int(round(RATE_WIN_S / dt)))
    rep_hist = []
    for k in range(n):
        t = k * dt
        cmd = sc.profile(t)
        rotor.step(cmd, dt=dt, t=t)

        # Independent observation channel: tachometer, motor current, casing
        # vibration.  These are separately keyed and the attacker in this
        # model does not hold their keys; that assumption is the analogue of
        # "he does not hold the remote merging unit's key" on the line, and it
        # is stated here so it can be attacked deliberately later.
        tach = rotor.f + rng.gauss(0.0, TACH_SIGMA)
        i_meas = true_current(rotor.f, rotor.dfdt) + b_i + rng.gauss(0.0, I_SIGMA)
        v_meas = true_vibration(rotor.f) + b_v + rng.gauss(0.0, V_SIGMA)

        # Compromised reporting path.  What the SCADA screen and the historian
        # see; honest unless the attacker is active.
        honest_report = rotor.f + rng.gauss(0.0, TACH_SIGMA)
        if atk is not None:
            rep, faked = atk.report(t, honest_report)
        else:
            rep, faked = honest_report, False
        rep_hist.append(rep)
        if len(rep_hist) > rate_lag + 1:
            rep_hist.pop(0)
        d_rep = ((rep_hist[-1] - rep_hist[0]) / ((len(rep_hist) - 1) * dt)
                 if len(rep_hist) > 1 else 0.0)

        r = residual(rep, d_rep, i_meas, v_meas)

        yield DriveSample(
            t=t,
            cmd_hz=cmd,
            speed_reported=rep,
            d_reported=d_rep,
            tach_hz=tach,
            current_pu=i_meas,
            vibration=v_meas,
            residual=r,
            in_band=(F_BAND_LO <= rep <= F_BAND_HI),
            speed_true=rotor.f,
            damage=rotor.damage,
            destroyed=rotor.destroyed,
            reporting_faked=faked,
        )


def episode_stats(sc, seed=0, dt=DT):
    """Roll an episode up into the numbers an experiment scores."""
    res, res_faked, res_hidden = [], [], []
    dmg = 0.0
    destroyed_t = None
    max_true = 0.0
    min_true = 1e9
    rep_out_of_band = 0
    true_out_of_band_while_reported_in = 0
    n = 0
    for s in run_scenario(sc, seed=seed, dt=dt):
        n += 1
        res.append(s.residual)
        if s.reporting_faked:
            res_faked.append(s.residual)
        dmg = s.damage
        if s.destroyed and destroyed_t is None:
            destroyed_t = s.t
        max_true = max(max_true, s.speed_true)
        min_true = min(min_true, s.speed_true)
        if not s.in_band:
            rep_out_of_band += 1
        if s.in_band and not (F_BAND_LO <= s.speed_true <= F_BAND_HI):
            true_out_of_band_while_reported_in += 1
            res_hidden.append(s.residual)
    return {
        "n": n,
        "damage": dmg,
        "destroyed_t": destroyed_t,
        "max_true_hz": max_true,
        "min_true_hz": min_true,
        "res_max": max(res) if res else 0.0,
        "res_p50": sorted(res)[len(res) // 2] if res else 0.0,
        "res_p99": sorted(res)[int(0.99 * (len(res) - 1))] if res else 0.0,
        "res_faked_p50": (sorted(res_faked)[len(res_faked) // 2]
                          if res_faked else 0.0),
        "res_faked_max": max(res_faked) if res_faked else 0.0,
        "reported_out_of_band": rep_out_of_band,
        "hidden_steps": true_out_of_band_while_reported_in,
        # Residual statistics restricted to the steps where the report is
        # actually hiding something -- true speed outside the qualified band
        # while the reported speed says otherwise.  This is the population the
        # monitor has to separate; averaging it together with the moments when
        # the rotor happens to be passing through 1064 Hz on its way out would
        # understate the detector for no good reason, since at those moments
        # there genuinely is no inconsistency to see.
        "res_hidden_p50": (sorted(res_hidden)[len(res_hidden) // 2]
                           if res_hidden else 0.0),
        "res_hidden_p05": (sorted(res_hidden)[len(res_hidden) // 20]
                           if res_hidden else 0.0),
        "hidden_frac_above": (lambda thr: (
            sum(1 for x in res_hidden if x > thr) / float(len(res_hidden)))
            if res_hidden else 0.0),
    }


def _payload_to_destruction(seed=0, max_s=6000.0):
    """Run the unmitigated payload until the rotor fails.  Returns
    (seconds, bursts, None) or (None, None, final damage) if it survives."""
    sc = sc_payload(horizon_s=max_s)
    for s in run_scenario(sc, seed=seed):
        if s.destroyed:
            return s.t, s.t / payload_period(), None
    return None, None, s.damage


# --- self check -------------------------------------------------------------

def self_check():
    """Assert that the physics and the attack are both real."""
    checks = []

    # 1. Rotor dynamics.
    r = Rotor(0.0)
    for k in range(2000):
        r.step(F_NOM, t=k * DT)
    checks.append(("spin-up: reaches nominal from rest",
                   abs(r.f - F_NOM) < 1.0))
    r2 = Rotor(F_NOM)
    r2.step(F_ATTACK_HI)
    checks.append(("rotor cannot follow a step (accel-limited)",
                   abs(r2.f - F_NOM) <= ACCEL_MAX * DT + 1e-9))
    checks.append(("acceleration limit is binding on the attack ramp",
                   (F_ATTACK_HI - F_NOM) / TAU_S > ACCEL_MAX))

    # 2. Damage: nothing in normal operation, everything under the payload.
    st_n = episode_stats(sc_normal())
    checks.append(("normal operation accrues exactly zero damage",
                   st_n["damage"] == 0.0))
    checks.append(("normal operation: true speed stays in band",
                   F_BAND_LO <= st_n["min_true_hz"]
                   and st_n["max_true_hz"] <= F_BAND_HI))

    st_op = episode_stats(sc_operator_setpoint())
    checks.append(("legitimate setpoint move accrues zero damage",
                   st_op["damage"] == 0.0))

    st_over = episode_stats(sc_overspeed())
    checks.append(("single overspeed burst is damaging but survivable",
                   0.02 < st_over["damage"] < DAMAGE_FAIL))
    checks.append(("overspeed reaches ~1410 Hz",
                   st_over["max_true_hz"] > F_ATTACK_HI - 5.0))

    st_low = episode_stats(sc_underspeed())
    checks.append(("resonance transit is damaging but survivable",
                   0.02 < st_low["damage"] < DAMAGE_FAIL))
    checks.append(("underspeed reaches ~2 Hz",
                   st_low["min_true_hz"] < 10.0))

    t_fail, bursts, dmg = _payload_to_destruction()
    checks.append(("unmitigated payload DESTROYS the rotor",
                   t_fail is not None))
    checks.append(("destruction takes several bursts, not one",
                   bursts is not None and bursts > 1.5))

    # 3. The replay genuinely hides the excursion.
    st_p = episode_stats(sc_payload(horizon_s=3 * payload_period()))
    checks.append(("replay: reported speed never leaves the operating band",
                   st_p["reported_out_of_band"] == 0))
    checks.append(("replay: true speed leaves the band for many steps while "
                   "the report says it did not",
                   st_p["hidden_steps"] > 500))
    checks.append(("replay: true speed really did reach the attack setpoints",
                   st_p["max_true_hz"] > 1400.0 and st_p["min_true_hz"] < 10.0))

    # 4. The independent residual catches what the report hides.
    normal_p99 = st_n["res_p99"]
    normal_max = max(st_n["res_max"], st_op["res_max"])
    checks.append(("normal residual stays O(1) sigma", normal_p99 < 4.0))
    checks.append(("median residual on hidden steps is >5x the worst benign one",
                   st_p["res_hidden_p50"] > 5.0 * normal_max))
    checks.append(("97% of hidden steps exceed the worst benign residual",
                   st_p["hidden_frac_above"](normal_max) > 0.95))
    checks.append(("freeze attack also raises the residual",
                   episode_stats(sc_freeze())["res_hidden_p50"] > 5 * normal_max))
    checks.append(("bias attack also raises the residual",
                   episode_stats(sc_bias())["res_hidden_p50"] > 5 * normal_max))

    # 5. Control case: replay with no excursion must NOT raise the residual.
    st_r = episode_stats(sc_replay_only())
    checks.append(("replay with no excursion leaves the residual benign",
                   st_r["res_faked_max"] < 6.0 and st_r["damage"] == 0.0))

    # 6. Determinism.
    a = [(s.speed_true, s.residual) for s in run_scenario(sc_payload(
        horizon_s=200.0), seed=7)]
    b = [(s.speed_true, s.residual) for s in run_scenario(sc_payload(
        horizon_s=200.0), seed=7)]
    checks.append(("deterministic given a seed", a == b))
    c = [s.residual for s in run_scenario(sc_normal(), seed=8)]
    d = [s.residual for s in run_scenario(sc_normal(), seed=9)]
    checks.append(("different seeds give different noise", c != d))

    return checks


def _report():
    lines = []
    lines.append("  %-26s %8s %8s %9s %9s %8s"
                 % ("scenario", "damage", "res p50", "res p99", "faked p50",
                    "hidden"))
    for sc in catalogue():
        st = episode_stats(sc)
        lines.append("  %-26s %8.4f %8.2f %9.2f %9.1f %8d"
                     % (sc.name, st["damage"], st["res_p50"], st["res_p99"],
                        st["res_faked_p50"], st["hidden_steps"]))
    t_fail, bursts, dmg = _payload_to_destruction()
    lines.append("")
    lines.append("  payload cycle period:            %8.1f s" % payload_period())
    if t_fail is None:
        lines.append("  rotor SURVIVED, final damage:    %8.4f" % dmg)
    else:
        lines.append("  time to destruction:             %8.1f s (%.2f bursts)"
                     % (t_fail, bursts))
    st_n = episode_stats(sc_normal())
    st_p = episode_stats(sc_payload(horizon_s=3 * payload_period()))
    lines.append("  residual, normal p99 / max:      %8.2f / %.2f"
                 % (st_n["res_p99"], st_n["res_max"]))
    lines.append("  residual on hidden steps p05/p50: %8.1f / %.1f"
                 % (st_p["res_hidden_p05"], st_p["res_hidden_p50"]))
    lines.append("  separation (hidden p50 / normal max): %6.1fx"
                 % (st_p["res_hidden_p50"] / max(st_n["res_max"], 1e-9)))
    lines.append("  hidden steps above worst benign residual: %5.1f%%"
                 % (100.0 * st_p["hidden_frac_above"](st_n["res_max"])))
    return "\n".join(lines)


if __name__ == "__main__":
    import time

    ok = True
    for name, passed in self_check():
        print(("  PASS  " if passed else "  FAIL  ") + name)
        ok = ok and passed
    print("plant self-check:", "OK" if ok else "BROKEN")
    print()
    print(_report())
    print()

    t0 = time.time()
    n = 0
    for i in range(20):
        for _ in run_scenario(sc_payload(horizon_s=600.0), seed=i):
            n += 1
    dt_s = time.time() - t0
    print("throughput: %.0f samples/s (%.1f ms per 600 s episode)"
          % (n / dt_s, 1000.0 * dt_s / 20))
