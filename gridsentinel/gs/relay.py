"""Baseline (conventional, deterministic, non-ML) protection.

This is what protects the line today and what the appliance must never make
worse.  It runs unconditionally, on the safety island, and its trip output is
OR-ed downstream of the shield -- no AI or shield state can inhibit it.

Elements:
  * 21  distance, mho characteristic, zones 1/2/3
  * 87L line differential with percentage restraint (NOMINAL settings only)
  * 67  directional supervision
  * 68  power-swing blocking
  * 21LB load-encroachment blinder on the distance elements

DELIBERATE BEHAVIOUR -- DO NOT "FIX"
-----------------------------------
This relay CAN be made to trip by a compromised local merging unit or a
spoofed time reference, and that is the correct, intended result.  A
conventional distance relay believes its own VT and CT: fed a forged local
voltage and current that describe an in-zone fault, it trips, and there is
nothing in a conventional relay that could know better.  Demonstrating that
is the entire reason this project exists.  The defence is architectural, not
local -- the remote merging unit is separately authenticated, and the shield
refuses to act on an AI proposal that the remote channel does not corroborate
(gs/shield.py: R_REMOTE, R_TIME, R_PHYSICS).

So: a trip in attack/fdi_* or attack/spoof_time is a true positive for this
file and a finding for the report, not a defect to be tuned away.  What must
never happen is a trip on benign/external_*, benign/power_swing or
benign/stressed_load -- those are honest telemetry, and tripping on them is a
real relay defect.

Nothing in this file reads, imports or is parameterised by anything on the
untrusted plane.  It consumes only `Sample` and the frozen constants in
`gs.shield`, and its output is a pure function of the sample stream.

Design notes that matter for the headline result
------------------------------------------------
The mho elements are *memory polarised*: the polarising quantity is the
remembered pre-fault voltage, which expands the characteristic backwards to
-Zs and buys real resistive coverage.  This is deliberately the *generous*
conventional choice -- the high-impedance gap reported downstream is measured
against the best conventional practice, not against a strawman.

Even so, the resistive reach of a mho at zone-2 setting is a few tenths of a
per-unit ohm, while an arcing fault with rf >= 3 pu puts the apparent
impedance ten line-lengths away.  No distance element sees it, and the
nominal percentage restraint (P0_NOM=0.30, K_NOM=0.35) sits above the fault
current it produces.  That gap is physics, not tuning.
"""

import cmath
import math

from . import power
from . import shield as sh

# Local source impedance behind the relay, used as the memory-polarisation
# expansion.  A distance relay derives this from settings, not from the AI.
ZS_LOCAL = power.ZS

Z1_REACH = 0.8 * power.ZL
Z2_REACH = 1.25 * power.ZL
Z3_REACH = 2.0 * power.ZL
ZOUT_REACH = 3.0 * power.ZL       # 68 outer (starter) characteristic

Z1_CONFIRM_MS = 2
Z2_DELAY_MS = 300
Z3_DELAY_MS = 800
DIFF_CONFIRM_MS = 6      # confirmation window for 87L, on top of comms delay

# 68 power-swing blocking: a swing walks the impedance from the outer
# characteristic into zone 3 over tens of milliseconds; a fault jumps in
# within the phasor estimator's one-cycle window.  Anything slower than this
# transit time is declared a swing.
SWING_TRANSIT_MS = 18

# 21LB load-encroachment blinder.  A fault sits close to the line angle
# (arg(ZL) = 84 deg) and close in; heavy load sits close to the real axis and
# far out.  A distance relay on a heavily loaded line has one of these
# precisely so that the load impedance cannot walk into the characteristic.
# Both conditions must hold before the zones are blocked, because the model's
# apparent fault angle is dragged well below the line angle by load flow: a
# close-in bolted fault here can show arg(z) = 17 deg, so an angle test on its
# own would blind zone 1 to real faults.  Adding the resistive-reach test
# separates them -- every impedance that reaches inside zone 1 has
# Re(z) <= 0.066 pu, while load encroachment carries Re(z) >= 0.10 pu.
BLINDER_R = 0.08                 # pu; ~0.8 x |ZL|
BLINDER_ANGLE_DEG = 30.0         # +/- about the real axis
# ... and any real differential current instantly proves it is not a swing
# (a swing is a balanced through-condition; Kirchhoff holds across the line).
# The unblock test has to be restraint-percentage, not a fixed pickup: a deep
# swing carries 6 pu of through-current, and assumption A1 alone then admits
# 0.7 pu of spurious differential.  Using the shield's *sensitivity floor*
# (P0_MIN / K_MIN) makes the unblock provably unreachable by CT error and
# charging current -- that is exactly what lemma_sensitivity_floor states.
# These are frozen protection constants, not anything the AI can move.
#
# With the differential channel down there is no remote quantity to appeal to,
# so 68 falls back on the local superimposed-component detector: a fault is a
# step, a swing is a ramp.  The threshold is set well above the step a
# high-impedance fault (or a forgery imitating one) produces, so a compromised
# local merging unit cannot talk its way past the block.
SWING_UNBLOCK_DIFAST = 0.5
# Both unblock paths are confirmed over a few milliseconds, like every other
# element here: a single anomalous sample must not be able to lift the block.
UNBLOCK_CONFIRM_MS = 4


def in_mho(z_app, z_set, z_pol=None):
    """Memory-polarised mho: the operate region is the circle whose diameter
    runs from -z_pol to z_set (self-polarised when z_pol is 0)."""
    if z_pol is None:
        z_pol = ZS_LOCAL
    a = z_set - z_app
    b = z_app + z_pol
    return (a.real * b.real + a.imag * b.imag) > 0.0


def in_load_region(z_app):
    """21LB: True when the apparent impedance is load, not fault."""
    if z_app.real <= BLINDER_R:
        return False
    ang = abs(math.degrees(cmath.phase(z_app)))
    return ang < BLINDER_ANGLE_DEG


class BaselineRelay(object):
    """Deterministic protection.  `step(sample) -> bool`, latching."""

    def __init__(self):
        self.z1_count = 0
        self.z2_since = None
        self.z3_since = None
        self.diff_count = 0
        self.out_since = None       # when the impedance entered ZOUT
        self.swing_blocked = False
        self.load_blocked = False
        self.unblock_count = 0
        self.trip = False
        self.trip_t = None
        self.trip_element = None

    # -- 68 ----------------------------------------------------------------
    def _swing(self, s):
        z = s.z_app
        in_out = s.forward and in_mho(z, ZOUT_REACH)
        in3 = s.forward and in_mho(z, Z3_REACH)

        if not in_out:
            self.out_since = None
            self.swing_blocked = False
            return in3

        if self.out_since is None:
            self.out_since = s.t

        if in3 and not self.swing_blocked:
            # Declare a swing only if the transit from the outer
            # characteristic into zone 3 took longer than a fault ever could.
            if s.t - self.out_since >= SWING_TRANSIT_MS:
                self.swing_blocked = True

        # A differential residual is proof of a fault, not a swing.
        floor = max(sh.P0_MIN, sh.K_MIN * s.i_restraint)
        fault_evidence = (
            (s.remote_fresh and s.remote_authentic and s.i_diff > floor)
            or s.di_fast > SWING_UNBLOCK_DIFAST)
        self.unblock_count = self.unblock_count + 1 if fault_evidence else 0
        if self.unblock_count >= UNBLOCK_CONFIRM_MS:
            self.swing_blocked = False
            self.out_since = None

        return in3

    # -- main --------------------------------------------------------------
    def step(self, s):
        if self.trip:
            return True

        z = s.z_app
        in3 = self._swing(s)

        # 67 directional supervision, 68 swing blocking and the 21LB load
        # blinder all gate the distance zones.  87L is deliberately NOT gated
        # by any of them: Kirchhoff does not care about load angle, and a
        # differential element has no reason to be blinded.
        self.load_blocked = in_load_region(z)
        distance_enabled = (s.forward and not self.swing_blocked
                            and not self.load_blocked)

        # Zone 1 -- instantaneous (short confirmation count)
        if distance_enabled and in_mho(z, Z1_REACH):
            self.z1_count += 1
        else:
            self.z1_count = 0
        if self.z1_count >= Z1_CONFIRM_MS:
            return self._fire(s, "21-Z1")

        # Zone 2 / Zone 3 -- time delayed backup
        if distance_enabled and in_mho(z, Z2_REACH):
            if self.z2_since is None:
                self.z2_since = s.t
            elif s.t - self.z2_since >= Z2_DELAY_MS:
                return self._fire(s, "21-Z2")
        else:
            self.z2_since = None

        if distance_enabled and in3:
            if self.z3_since is None:
                self.z3_since = s.t
            elif s.t - self.z3_since >= Z3_DELAY_MS:
                return self._fire(s, "21-Z3")
        else:
            self.z3_since = None

        # 87L at nominal (insensitive) settings only.  Requires authenticated,
        # fresh remote data: with the channel down the element is out of
        # service and the line falls back on distance, as it does in practice.
        nominal_threshold = max(sh.P0_NOM, sh.K_NOM * s.i_restraint)
        if (s.remote_authentic and s.remote_fresh
                and s.i_diff > nominal_threshold):
            self.diff_count += 1
        else:
            self.diff_count = 0
        if self.diff_count >= DIFF_CONFIRM_MS:
            return self._fire(s, "87L")

        return False

    def _fire(self, s, element):
        self.trip = True
        self.trip_t = s.t
        self.trip_element = element
        return True


def run(samples):
    """Convenience: drive a relay over a sample stream, return the relay."""
    r = BaselineRelay()
    for s in samples:
        if r.step(s):
            break
    return r
