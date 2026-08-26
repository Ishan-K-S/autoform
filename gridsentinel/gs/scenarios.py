"""The scenario catalogue: the stress set every plane is scored on.

Seventeen families in three groups.

  benign   -- nothing on the protected line is faulted.  Tripping is wrong.
  genuine  -- the protected line is faulted.  Tripping is right, and the
              faster the better.
  attack   -- an adversary is manipulating the telemetry.  Tripping on the
              adversary's say-so is wrong.

FALSE DATA INJECTION IS SPLIT ACROSS TWO ADVERSARIES.  They look alike in
the analogue channels and are completely different in provenance, so they
are separate families and are held to opposite expectations:

  attack/fdi_linux_*   LINUX-PLANE compromise.  The attacker owns the
                       untrusted inference plane but no merging-unit signing
                       key.  He deceives the model; the safety island reads
                       authenticated streams straight off the process bus, so
                       his frames fail the local signature check.
                       EXPECTED: BLOCKED (zero shield grants).
  attack/fdi_replay    No key either, but a recording of genuinely signed
                       frames.  Signatures verify; the monotone counter does
                       not advance, so the frames are stale.
                       EXPECTED: BLOCKED (zero shield grants).
  attack/fdi_tuned     LOCAL MERGING-UNIT KEY compromise.  His forgeries are
                       validly signed and correctly sequenced, because he
                       holds the key.  i_diff = |I_local + I_remote| is a sum
                       and he owns one addend.
                       EXPECTED: STILL GRANTED.  This is the honest RESIDUAL
                       risk.  It is closed by non-exportable key custody in
                       the MU's HSM plus firmware attestation -- NOT by any
                       threshold, dwell length or logic change, and a patch
                       that drives it to zero has almost certainly weakened
                       the adversary rather than the exposure.

`internal_truth` is set from the physics, not from the group name: it is True
exactly when the protected line carries a fault and opening the breaker is
the correct action.  There is one place where that rule and the shorthand
"attacks are never trips" disagree, and physics wins:

    attack/remote_loss_fault -- the adversary (or a backhoe) takes out the
    87L communications channel *during a real internal fault*.  A fault is
    genuinely there, so internal_truth is True; the point of the family is
    that losing the differential channel must not lose the line.  Labelling
    it False would score a correct, necessary trip as a false trip.

Every family carries a `family` tag of the form "group/name" so results can
be aggregated, and every instance carries a `seed` for a reproducible
measurement stream.
"""

import random

from . import power
from . import shield as sh
from .measure import Scenario, NOMINAL_DELTA, HORIZON_MS, EVENT_MS


GROUPS = {"benign": [], "genuine": [], "attack": []}


# The power solver memoises on ROUNDED arguments and an uncached AC solve is
# ~5 ms, so every randomised parameter below is drawn onto a coarse grid.  The
# variety the experiment needs is in the spread, not in the seventh decimal.
M_GRID = [0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9]
A_GRID = [0.1, 0.3, 0.5, 0.7, 0.9]
RF_BOLTED_MIN = 0.02      # the solver's Newton-Raphson floor; electrically
                          # bolted (11.4 pu differential) at this value


def _u(rng, lo, hi, q=0.5):
    """Uniform on [lo, hi], snapped to a grid of size `q`."""
    return round(rng.uniform(lo, hi) / q) * q


def _swing_ramp(rng, d0):
    """Angular velocity (deg/s) that walks the machine angle from `d0` to a
    given peak by the end of the observation horizon.  Peaks are kept below
    180 deg: past that the machines have slipped a pole and the correct
    response is out-of-step *tripping*, a different element and a different
    study."""
    peak = _u(rng, 130.0, 165.0, 5.0)
    span_s = (HORIZON_MS - EVENT_MS) / 1000.0
    return (peak - d0) / span_s


# --- the monitor-aware forger ----------------------------------------------

FDI_RF_GRID = [round(1.0 + 0.25 * i, 2) for i in range(45)]   # 1.00 .. 12.00
FDI_M = 0.4               # where the forgery pretends the fault is


def _fdi_band(delta, rf):
    """What a forgery at `rf` would actually put on the two channels.

    The local channel is the attacker's to write; the remote channel is not,
    so the differential he manufactures is `|I_local_forged + I_remote_true|`
    and the restraint is the mean of the two magnitudes.  Everything the
    shield and the 87L element decide on follows from those two numbers.
    """
    base = power.prefault(delta_deg=delta)
    fake = power.solve(delta_deg=delta, fault_node="F", rf=rf, m=FDI_M)
    i_diff = abs(fake.I_s + base.I_r)
    i_rest = 0.5 * (abs(fake.I_s) + abs(base.I_r))
    floor = max(sh.P0_MIN, sh.K_MIN * i_rest)       # most sensitive setting
    nominal = max(sh.P0_NOM, sh.K_NOM * i_rest)     # conventional 87L pickup
    return i_diff, i_rest, floor, nominal


# How far above the shield's floor the forger aims.  Measured, not guessed:
# swept against the live shield and the trained honest policy, the grant rate
# peaks when the fabricated differential only just clears the floor.  Aiming
# higher is counter-productive for the attacker -- a larger forgery makes the
# AI ask for a trip sooner and more insistently, and those early requests are
# vetoed while the forgery is still ramping in, spending the model's VETO_LIMIT
# trust budget before the differential becomes credible.  Restraint, in both
# senses, is what gets him through.
FDI_TARGET_MARGIN = 1.06


def _restraint_breakpoint_delta():
    """Load angle at which through-current reaches P0_MIN/K_MIN.

    Below it the shield's floor is the flat P0_MIN pedestal; above it the floor
    is K_MIN * Ir and climbs with load.  The forger's best moment is right at
    the knee: as much cover as the pedestal allows, with a plausible
    high-impedance forgery still able to clear it.  Derived from the shield
    constants so it tracks any retune.
    """
    target = sh.P0_MIN / sh.K_MIN
    best = None
    for i in range(30):
        d = round(3.0 + 0.5 * i, 1)
        err = abs(abs(power.prefault(delta_deg=d).I_r) - target)
        if best is None or err < best[0]:
            best = (err, d)
    return best[1]


def _tune_fdi_rf(delta):
    """Pick the forgery amplitude that best exploits the shield.

    The attacker wants his fabricated differential to land in the band

        max(P0_MIN, K_MIN*Ir)  <  i_diff  <  max(P0_NOM, K_NOM*Ir)

    -- above the most sensitive threshold the shield will ever allow, so the
    AI's proposal survives `differential_ok`, and below the nominal pickup, so
    the conventional 87L element beside it stays silent and never exposes the
    intrusion.  Within that band he aims LOW, at FDI_TARGET_MARGIN times the
    floor; see that constant for why the bottom of the band beats the middle.

    Both bounds are read from gs.shield at build time, so if P0_MIN/K_MIN or
    P0_NOM/K_NOM are ever retuned the adversary retunes with them -- which is
    the point: no choice of threshold closes this, because the attacker can
    see the threshold too.

    Returns None if no grid point lands in the band, which in this network
    does not happen -- see `_fdi_tuned` for why the band cannot be closed by
    choosing thresholds.
    """
    best = None
    for rf in FDI_RF_GRID:
        i_diff, _i_rest, floor, nominal = _fdi_band(delta, rf)
        if not (floor < i_diff < nominal):
            continue
        err = abs(i_diff / floor - FDI_TARGET_MARGIN)
        if best is None or err < best[0]:
            best = (err, rf)
    return best[1] if best is not None else None


# --- family builders --------------------------------------------------------
# Each takes (rng, index) and returns the kwargs for one Scenario instance.

def _normal_load(rng, i):
    return dict(delta=_u(rng, 4.0, 12.0))


def _stressed_load(rng, i):
    # Heavy import: the load impedance walks in towards the zone-3 circle.
    # This is the classic load-encroachment case a distance relay must ride.
    return dict(delta=_u(rng, 45.0, 75.0))


def _power_swing(rng, i):
    # Post-disturbance angular swing.  The angle ramps far enough to walk the
    # apparent impedance through the outer characteristic and into zone 2,
    # which is exactly what 68 exists to block.
    d0 = _u(rng, 15.0, 30.0)
    return dict(delta=d0, delta_ramp=_swing_ramp(rng, d0))


def _external_fwd(rng, i):
    return dict(fault_node="G", rf=_u(rng, RF_BOLTED_MIN, 0.3, 0.01), a=rng.choice(A_GRID),
                delta=_u(rng, 5.0, 15.0), arcing=rng.random() < 0.35)


def _external_fwd_ctsat(rng, i):
    # Bolted-ish through fault: heavy through-current, unequal CT saturation.
    # The spurious differential this produces is the worst case assumption A1
    # is allowed to admit, and it must stay under the nominal restraint line.
    return dict(fault_node="G", rf=_u(rng, RF_BOLTED_MIN, 0.05, 0.01), a=rng.choice(A_GRID),
                delta=_u(rng, 5.0, 15.0), ct_saturation=True)


def _external_rev(rng, i):
    return dict(fault_node="B", rf=_u(rng, RF_BOLTED_MIN, 0.3, 0.01), delta=_u(rng, 5.0, 15.0),
                arcing=rng.random() < 0.35)


def _internal_bolted(rng, i):
    # rf spans the whole [0, 0.2] pu band the brief asks for, skewed towards
    # the bolted end: 0.2 pu is 240 primary ohms, which is a low-impedance
    # fault by differential standards but far outside any mho's resistive
    # reach, so a flat draw would report the family as an 87L family.
    u = rng.random()
    return dict(fault_node="F", rf=round(RF_BOLTED_MIN + 0.18 * u * u, 2),
                m=rng.choice(M_GRID), delta=_u(rng, 5.0, 15.0))


def _internal_medium(rng, i):
    return dict(fault_node="F", rf=_u(rng, 0.5, 2.0, 0.05), m=rng.choice(M_GRID),
                delta=_u(rng, 5.0, 15.0), arcing=rng.random() < 0.5)


def _internal_hif_arcing(rng, i):
    # The reason the AI exists.  Downed conductor / tree contact: the fault
    # current is of the order of load current, the apparent impedance is ten
    # line-lengths out, and the only distinguishing evidence is a small but
    # *authenticated* differential plus the arc's harmonic signature.
    return dict(fault_node="F", rf=_u(rng, 3.0, 12.0, 0.25), m=rng.choice(M_GRID),
                delta=_u(rng, 5.0, 15.0), arcing=True)


def _fdi_linux_normal(rng, i):
    """LINUX-PLANE compromise under normal load.  EXPECTED TO BE BLOCKED.

    The attacker owns the untrusted inference plane and no signing key.  He
    rewrites what the MODEL sees; the safety island reads the authenticated
    stream off the process bus and finds the local channel unsigned.  See
    measure.py for why the forgery imitates a high-impedance arcing fault
    rather than a bolted one, and for the modelling choice.
    """
    return dict(delta=_u(rng, 5.0, 15.0), fdi=True, fdi_rf=_u(rng, 5.0, 10.0, 0.5),
                arcing=True)


def _fdi_linux_swing(rng, i):
    """Same Linux-plane forgery under cover of a power swing, when the
    impedance is already inside the characteristics and operators are busy.
    EXPECTED TO BE BLOCKED, for the same reason."""
    d0 = _u(rng, 15.0, 30.0)
    return dict(delta=d0, delta_ramp=_swing_ramp(rng, d0),
                fdi=True, fdi_rf=_u(rng, 5.0, 10.0, 0.5), arcing=True)


def _fdi_linux_tuned(rng, i):
    """The tuned forgery of `_fdi_tuned`, launched from the LINUX PLANE.

    Deliberately the SAME analogue numbers as the residual family below --
    same tuning machinery, same target band, same moment -- differing only in
    provenance: these frames carry no valid local signature.  It is the
    controlled comparison that shows the block is due to authentication and
    not to some accident of amplitude.  EXPECTED TO BE BLOCKED.
    """
    kw = _fdi_tuned(rng, i)
    kw.pop("fdi_mu_key", None)
    kw["fdi"] = True
    return kw


def _fdi_replay(rng, i):
    """REPLAY of genuinely signed local frames.  EXPECTED TO BE BLOCKED.

    The attacker has no key; he has a recording of an earlier internal fault,
    signed by the real merging unit, and re-plays it.  Every signature
    verifies.  What does not verify is the monotone counter: the replayed
    frames never get ahead of the live watermark, so they are stale.  This is
    the family that distinguishes "authenticated" from "fresh" -- a signature
    alone would pass this attack straight through.
    """
    return dict(delta=_u(rng, 5.0, 15.0), replay_local=True,
                fdi_rf=_u(rng, 5.0, 10.0, 0.5), arcing=True)


def _fdi_tuned(rng, i):
    """FDI by a forger who has READ THE SHIELD *and holds the local merging
    unit's private signing key*.

    ==================  EXPECTED TO DEFEAT THE SHIELD  ======================
    RESIDUAL RISK, BY CONSTRUCTION.  This family is not a regression test and
    a non-zero grant rate here is NOT a bug to be tuned away.  Its forged
    frames carry a VALID local signature and a correctly advancing sequence
    counter, because the adversary holds the key that makes signatures valid.
    Authenticating both ends -- which the shield now does, and which blocks
    every `attack/fdi_linux_*` and `attack/fdi_replay` episode -- cannot touch
    it.  It exists to measure a real, structural exposure:

        the differential is a SUM, i_diff = |I_local + I_remote|.  An
        adversary holding the local merging unit's key owns one addend and
        therefore owns the sum.  Authenticating only the remote half does not
        protect it.  The A1/A2 sensitivity-floor lemma does not apply, because
        a forged current is not an instrument error -- it violates the very
        premise the lemma is discharged under.

    No threshold and no dwell length closes this.  Raising the floor only
    tells the attacker where to aim (he reads the same constants); the dwell
    only requires him to hold the forgery steady for another millisecond,
    which costs him nothing.  The defence is at the source and nowhere else:
    non-exportable custody of the LOCAL merging unit's key (generated in and
    never leaving the MU's HSM) plus remote attestation of the MU firmware,
    so that holding the key requires physically defeating the MU.  Local
    authentication closed the attacker who never had the key; only key
    custody closes the one who does.  No threshold, no dwell length and no
    change to the shield's logic will move this number, and any future patch
    that appears to move it should be suspected of having weakened the
    adversary rather than the exposure.
    =========================================================================

    He tunes his MOMENT as well as his amplitude.  The forged apparent
    impedance stays 5 to 15 line-lengths out across the whole usable rf range,
    so the distance elements never see him either way -- a forgery big enough
    for 21 to notice would be big enough for the nominal 87L to notice too.
    What does bind him is the floor's shape: it is
    max(P0_MIN, K_MIN*Ir), so he strikes at the knee, where through-current is
    near P0_MIN/K_MIN.  Much below it and the AI is unconvinced; much above it
    and the floor climbs with load until only an implausibly large forgery
    could clear it.
    """
    delta = _restraint_breakpoint_delta() + _u(rng, -1.0, 0.5, 0.5)
    rf = _tune_fdi_rf(delta)
    if rf is None:                            # band empty: best effort
        rf = 3.0
    # Modest jitter, so the family is not 25 copies of one number -- but a
    # careful attacker checks his jitter before he uses it, and backs off any
    # value that would push the forgery out of the band and expose him to the
    # conventional 87L element.
    jittered = max(FDI_RF_GRID[0], rf + _u(rng, -0.5, 0.5, 0.25))
    i_diff, _ir, floor, nominal = _fdi_band(delta, jittered)
    if floor < i_diff < nominal:
        rf = jittered
    return dict(delta=delta, fdi_mu_key=True, fdi_rf=rf, arcing=True)


def _spoof_time(rng, i):
    return dict(delta=_u(rng, 5.0, 15.0), spoof_time=True,
                spoof_deg=_u(rng, 4.0, 14.0, 1.0) * rng.choice([-1.0, 1.0]))


def _remote_loss(rng, i):
    return dict(delta=_u(rng, 5.0, 15.0), remote_lost=True)


def _remote_loss_fault(rng, i):
    # Channel gone AND a real internal fault.  Baseline distance must carry
    # the line on its own, so this family is deliberately the case distance
    # protection can actually carry: a close-in, near-bolted fault inside the
    # zone-1 reach.  (An arcing fault at 90% of the line with the differential
    # channel down is simply not clearable by conventional means -- that is
    # the same gap the high-impedance family measures, not a separate one.)
    return dict(fault_node="F", rf=_u(rng, RF_BOLTED_MIN, 0.03, 0.01),
                m=rng.choice(M_GRID[:5]),
                delta=_u(rng, 5.0, 15.0), remote_lost=True)


# (group, name, builder, internal_truth)
FAMILIES = [
    ("benign",  "normal_load",        _normal_load,        False),
    ("benign",  "stressed_load",      _stressed_load,      False),
    ("benign",  "power_swing",        _power_swing,        False),
    ("benign",  "external_fwd",       _external_fwd,       False),
    ("benign",  "external_fwd_ctsat", _external_fwd_ctsat, False),
    ("benign",  "external_rev",       _external_rev,       False),
    ("genuine", "internal_bolted",    _internal_bolted,    True),
    ("genuine", "internal_medium",    _internal_medium,    True),
    ("genuine", "internal_hif_arcing", _internal_hif_arcing, True),
    # --- false data injection: TWO adversaries, kept apart on purpose -----
    # Linux-plane (no signing key): EXPECTED BLOCKED by both-ends
    # authentication.  Replay (no key, stolen frames): EXPECTED BLOCKED by
    # the monotone counter.  MU-key: RESIDUAL, closed only by key custody in
    # the MU's HSM plus attestation -- never by a threshold or dwell change.
    ("attack",  "fdi_linux_normal",   _fdi_linux_normal,   False),
    ("attack",  "fdi_linux_swing",    _fdi_linux_swing,    False),
    ("attack",  "fdi_linux_tuned",    _fdi_linux_tuned,    False),
    ("attack",  "fdi_replay",         _fdi_replay,         False),
    ("attack",  "fdi_tuned",          _fdi_tuned,          False),
    ("attack",  "spoof_time",         _spoof_time,         False),
    ("attack",  "remote_loss",        _remote_loss,        False),
    # physics overrides the shorthand here -- see module docstring
    ("attack",  "remote_loss_fault",  _remote_loss_fault,  True),
]

FAMILY_NAMES = ["%s/%s" % (g, n) for g, n, _b, _t in FAMILIES]


def catalogue(n_per_family=25, seed=0):
    """Build the full stress set: `n_per_family` randomised instances of each
    of the 17 families, in a deterministic order for a given seed."""
    out = []
    for fi, (group, name, build, truth) in enumerate(FAMILIES):
        family = "%s/%s" % (group, name)
        for i in range(n_per_family):
            # Per-instance stream: independent of n_per_family and of the
            # order families are listed in.
            rng = random.Random((seed, fi, i).__hash__() & 0xFFFFFFFF)
            kw = build(rng, i)
            kw.setdefault("delta", NOMINAL_DELTA)
            sc = Scenario(name="%s#%02d" % (family, i), family=family,
                          internal_truth=truth, **kw)
            sc.group = group
            sc.seed = rng.randrange(1 << 30)
            out.append(sc)
    return out


if __name__ == "__main__":
    cat = catalogue()
    print("%d scenarios, %d families" % (len(cat), len(FAMILIES)))
    for f in FAMILY_NAMES:
        n = sum(1 for s in cat if s.family == f)
        t = sum(1 for s in cat if s.family == f and s.internal_truth)
        print("  %-28s n=%3d internal_truth=%d" % (f, n, t))
