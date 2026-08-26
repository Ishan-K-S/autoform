"""Positive-sequence phasor model for the protected line, built with pandapower.

Topology (all impedances in per-unit on a 100 MVA / 345 kV base):

    Es --(Zs/2)-- B --(Zs/2)-- S ==(m*ZL)== F ==((1-m)*ZL)== R --(a*ZL2)-- G --((1-a)*ZL2)-- T --(Zt)-- Et
       ^                                                     |
    (ext_grid behind an                                     Zr
     explicit source impedance)                              |
                                                            Er   (remote infeed at bus R)

    `==` is the protected line.  The relay under study sits at bus S looking
    forward (into the line).  A second, independently authenticated merging
    unit sits at bus R.  Faults are applied as a shunt conductance at exactly
    one node:

        F  -> internal fault (in-zone, at fraction m of the line)
        G  -> external forward fault (adjacent line, through-current)
        B  -> external reverse fault (behind the relay)
        None -> healthy network (load flow only)

Everything downstream -- apparent impedance, differential residual, distance
element behaviour -- is derived from one network solution, so the numbers are
mutually consistent instead of being asserted scenario by scenario.


WHY THIS IS A DIRECT SOLVE AND NOT `runpp`
------------------------------------------
pandapower builds the network and its admittance matrix; that is what it is
used for here.  The *solution* is then obtained by solving Y*V = I directly
rather than by Newton-Raphson, because this network is entirely linear: every
source is a constant-voltage slack behind a finite impedance, the fault is a
constant-admittance shunt, and there are no constant-power loads at all.

Running Newton-Raphson on it was an active correctness hazard.  Buses B, S, F,
R and G carry zero power injection, so V = 0 satisfies their mismatch
equations exactly -- the power-flow equations have a spurious all-zero fixed
point alongside the physical one.  `runpp` would converge onto that degenerate
branch (reporting converged=True with bus voltages of 1e-58) whenever it was
started near it, which happened both at large source angles and, far more
insidiously, whenever a previous high-angle solve had left the net warm-started.
That made solve() a function of its call history: solve(175) followed by
solve(22) returned |I_s| = 0.000152 where solve(22) alone returns 1.279576, an
8394x error that then got memoised under the correct cache key.  The degenerate
|z_app| of 0.05 sits at the line angle inside zone 1, so it read as a bolted
internal fault and tripped the distance element on healthy networks.

A linear solve has no iteration, no start point, no tolerance and no second
branch, so identical arguments give bit-identical results no matter what was
solved before.  `self_check` cross-validates it against `pp.runpp` on the
well-conditioned part of the operating range, so pandapower remains the
authority on what the network model *is*.

Note that a plausibility floor on bus voltage would NOT have been a correct
gate: at delta = 175 degrees the electrical centre of the swing genuinely falls
inside the protected line and V_F legitimately drops to 0.04 pu.  The gate used
here is the linear-system residual, which is exact.


THREE MODELLING POINTS THE NUMBERS DEPEND ON
--------------------------------------------
1.  Every source sits on its own bus behind an explicit series impedance
    branch.  An ideal ext_grid bolted straight onto B/R/T would swallow an
    external fault whole and leave the protected line's currents untouched,
    making external faults invisible to the relay.

2.  The source EMF magnitudes and angles are calibrated so that the healthy
    load current sits near 0.54 pu and the high-impedance internal fault
    current band straddles the shield's 0.10 pu sensitivity floor.

3.  The line is modelled with its distributed capacitance, so the raw
    |I_s + I_r| carries a standing charging current.  `Solution.i_diff`
    subtracts the computed charging current the way a real 87L relay does.
    The compensation susceptance is read back out of the assembled network
    rather than assumed, so it cannot drift from the model: pandapower's
    default system frequency is 50 Hz, and an earlier version of this file
    sized c_nf_per_km at 60 Hz and then compensated at 60 Hz against a line
    that was actually built at 50 Hz, leaving a standing error of 0.013 pu.
"""

import cmath
import logging
import math
import random
import warnings

import numpy as np

# pandapower is chatty on import; nothing it says is actionable here.
warnings.filterwarnings("ignore")
for _name in ("pandapower", "pandapower.auxiliary", "pandapower.run",
              "pandapower.powerflow", "numba"):
    logging.getLogger(_name).setLevel(logging.CRITICAL)

import pandapower as pp  # noqa: E402

# --- bases -----------------------------------------------------------------

VN_KV = 345.0
S_BASE_MVA = 100.0
F_HZ = 60.0
Z_BASE = VN_KV * VN_KV / S_BASE_MVA     # 1190.25 ohm
OMEGA = 2.0 * math.pi * F_HZ

NODES = ["B", "S", "F", "R", "G", "T"]
FAULT_NODES = ("F", "G", "B")
_BUS_NAMES = ("ES", "B", "S", "F", "R", "G", "T", "ER", "ET")

# --- network constants (per unit) ------------------------------------------

ZL = complex(0.010, 0.100)    # protected line, total series impedance
ZL2 = complex(0.012, 0.120)   # adjacent line, total series impedance
ZS = complex(0.005, 0.050)    # local source, behind bus B
ZR = complex(0.008, 0.080)    # remote infeed at bus R
ZT = complex(0.006, 0.060)    # far source, behind bus T

# Total shunt susceptance of each line, pu.  A 345 kV line with x = 0.10 pu on
# a 100 MVA base is ~350 km long and would carry ~1.9 pu of raw charging; these
# values represent the line as heavily shunt-reactor compensated, which is what
# an EHV line of that length actually is.
B_LINE = 0.08                 # protected line
B_LINE2 = 0.10                # adjacent line

# Source EMFs.  Magnitudes are calibrated (see module docstring); the small
# spread across the three sources makes the healthy flow lagging so the
# directional element sees it as forward.
E_MAG = 0.65
E_S = E_MAG * 1.03
E_R = E_MAG * 0.97
E_T = E_MAG * 0.96
DELTA_R_DEG = 0.0             # remote infeed reference angle
DELTA_T_DEG = -4.0            # far source angle

# A "bolted" fault is a shunt of this per-unit resistance (1.2 ohm primary).
RF_MIN = 1e-3

# Residual tolerance for the linear solve; a correct solve lands near 1e-16.
RESIDUAL_TOL = 1e-9

# Collapse detector: the largest bus voltage anywhere in the network. The true
# solution never drops this below 0.51 pu anywhere in the operating envelope;
# the spurious zero-voltage branch puts it at ~1e-6.
V_COLLAPSE_FLOOR = 0.05

HUGE = complex(1e9, 0.0)

_TOPO_CACHE = {}
_SOLVE_CACHE = {}
_SOLVE_CACHE_MAX = 200000


class PowerFlowError(RuntimeError):
    """Raised when a solution fails validation.  Never cached, never returned."""


class Solution(object):
    """Result of one phasor solve, from the relay's point of view."""

    __slots__ = ("V_s", "I_s", "I_r", "V_r")

    def __init__(self, V_s, I_s, I_r, V_r):
        self.V_s = V_s      # bus S voltage phasor
        self.I_s = I_s      # current at S flowing INTO the protected line
        self.I_r = I_r      # current at R flowing INTO the protected line
        self.V_r = V_r      # bus R voltage phasor

    @property
    def z_app(self):
        """Apparent impedance seen by the distance element at S."""
        if abs(self.I_s) < 1e-9:
            return HUGE
        return self.V_s / self.I_s

    @property
    def i_diff(self):
        """Line differential (87L) residual in per unit, charging-compensated.

        Kirchhoff: for any fault *outside* the protected line the sum of the
        two terminal currents is exactly the line's own capacitive charging
        current.  A real 87L relay subtracts an estimate of that current
        (j*B/2 applied to each terminal voltage) before comparing against the
        pickup, otherwise a long EHV line stands permanently picked up.  What
        is left is zero up to instrument-transformer error; for an internal
        fault it equals the total fault current.  This is the physics channel
        the shield trusts.
        """
        charging = 1j * B_HALF * (self.V_s + self.V_r)
        return abs(self.I_s + self.I_r - charging)

    @property
    def i_through(self):
        """Restraint quantity: through-current magnitude."""
        return 0.5 * (abs(self.I_s) + abs(self.I_r))


# --- network construction ---------------------------------------------------

def _add_line(net, f_bus, t_bus, z_pu, b_pu, name):
    """Add a 1 km equivalent line whose pi-parameters are the given pu values."""
    c_nf = b_pu / (OMEGA * Z_BASE) * 1e9
    return pp.create_line_from_parameters(
        net, f_bus, t_bus, length_km=1.0,
        r_ohm_per_km=z_pu.real * Z_BASE,
        x_ohm_per_km=z_pu.imag * Z_BASE,
        c_nf_per_km=c_nf, max_i_ka=100.0, name=name)


def _build_net(m, a):
    """Build the pandapower network for one fault-position topology."""
    net = pp.create_empty_network(sn_mva=S_BASE_MVA, f_hz=F_HZ)
    bus = {}
    for name in _BUS_NAMES:
        bus[name] = pp.create_bus(net, vn_kv=VN_KV, name=name)

    # Source branches.  Every EMF is behind a real impedance, so a fault at B
    # or G depresses the network and the protected line's currents move.
    pp.create_impedance(net, bus["ES"], bus["B"],
                        0.5 * ZS.real, 0.5 * ZS.imag, S_BASE_MVA)
    pp.create_impedance(net, bus["B"], bus["S"],
                        0.5 * ZS.real, 0.5 * ZS.imag, S_BASE_MVA)
    pp.create_impedance(net, bus["ER"], bus["R"],
                        ZR.real, ZR.imag, S_BASE_MVA)
    pp.create_impedance(net, bus["ET"], bus["T"],
                        ZT.real, ZT.imag, S_BASE_MVA)

    li_sf = _add_line(net, bus["S"], bus["F"], m * ZL, m * B_LINE, "S-F")
    li_fr = _add_line(net, bus["F"], bus["R"], (1.0 - m) * ZL,
                      (1.0 - m) * B_LINE, "F-R")
    _add_line(net, bus["R"], bus["G"], a * ZL2, a * B_LINE2, "R-G")
    _add_line(net, bus["G"], bus["T"], (1.0 - a) * ZL2,
              (1.0 - a) * B_LINE2, "G-T")

    eg_s = pp.create_ext_grid(net, bus["ES"], vm_pu=E_S, va_degree=0.0)
    pp.create_ext_grid(net, bus["ER"], vm_pu=E_R, va_degree=DELTA_R_DEG)
    pp.create_ext_grid(net, bus["ET"], vm_pu=E_T, va_degree=DELTA_T_DEG)

    return net, bus, eg_s, li_sf, li_fr


def _build_topology(m, a):
    """Assemble the constant parts of one (m, a) topology, once.

    Returns everything the per-solve linear solve needs.  No pandapower object
    is mutated after this point, which is what makes solve() history-free.
    """
    net, bus, eg_s, li_sf, li_fr = _build_net(m, a)

    # Let pandapower assemble the admittance matrix and branch model for us.
    # This is the only runpp call in the module's steady-state path; it runs
    # once per topology at 8 degrees purely to populate net._ppc.  Its
    # *result* is never read -- Ybus and the branch table are built from the
    # network data before the iteration starts -- so a convergence failure
    # here is harmless and is deliberately swallowed.
    net.ext_grid.at[eg_s, "va_degree"] = 8.0
    try:
        pp.runpp(net, numba=False, init="dc", max_iteration=50)
    except Exception:
        pass
    if getattr(net, "_ppc", None) is None:
        raise PowerFlowError("pandapower failed to assemble the network "
                             "for m=%r a=%r" % (m, a))

    ppc = net._ppc
    y_full = np.asarray(ppc["internal"]["Ybus"].todense(), dtype=complex)
    lookup = net._pd2ppc_lookups["bus"]
    p = {name: int(lookup[bus[name]]) for name in _BUS_NAMES}

    slack = [p["ES"], p["ER"], p["ET"]]
    rest = [i for i in range(y_full.shape[0]) if i not in slack]
    rest_pos = {ppc_i: k for k, ppc_i in enumerate(rest)}

    # Exact branch model of the two protected-line segments, read back out of
    # the ppc so the currents are pandapower's model, not a re-derivation.
    br = ppc["branch"]
    br_lookup = net._pd2ppc_lookups["branch"]["line"][0]

    def branch_of(line_idx):
        row = br[br_lookup + line_idx]
        z = complex(row[2].real, row[3].real)
        return 1.0 / z, 0.5 * row[4].real       # y_series, b_half

    y_sf, b_sf_half = branch_of(li_sf)
    y_fr, b_fr_half = branch_of(li_fr)

    # Independent check that the assembled Ybus really is this network: for a
    # passive network whose only shunts are the line charging, every row of
    # Ybus must sum to exactly that bus's shunt susceptance.  This catches a
    # mis-assembled or mis-indexed matrix before it can produce a plausible
    # but wrong answer.
    row_sums = np.asarray(y_full.sum(axis=1)).ravel()
    if np.max(np.abs(row_sums.real)) > 1e-9:
        raise PowerFlowError("assembled Ybus has non-zero conductance row "
                             "sums; network model is not passive")

    return {
        "net": net, "bus": bus, "p": p,
        "y_rr": y_full[np.ix_(rest, rest)].copy(),
        "y_rs": y_full[np.ix_(rest, slack)].copy(),
        "rest_pos": rest_pos,
        "i_s": rest_pos[p["S"]], "i_f": rest_pos[p["F"]],
        "i_r": rest_pos[p["R"]],
        "y_sf": y_sf, "b_sf_half": b_sf_half,
        "y_fr": y_fr, "b_fr_half": b_fr_half,
        # Total charging susceptance of the protected line, as actually built.
        "b_line": 2.0 * (b_sf_half + b_fr_half),
        "eg_s": eg_s, "li_sf": li_sf, "li_fr": li_fr,
    }


def _get_topology(m, a):
    key = (m, a)
    topo = _TOPO_CACHE.get(key)
    if topo is None:
        topo = _build_topology(m, a)
        _TOPO_CACHE[key] = topo
    return topo


# The 87L charging compensation constant, taken from the as-built network so it
# can never disagree with the line model.  Identical for every topology: the
# two segments always sum to the whole line.
B_HALF = 0.5 * _get_topology(0.5, 0.5)["b_line"]


# --- solving ----------------------------------------------------------------

def _slack_vector(delta_deg):
    return np.array([
        cmath.rect(E_S, math.radians(delta_deg)),
        cmath.rect(E_R, math.radians(DELTA_R_DEG)),
        cmath.rect(E_T, math.radians(DELTA_T_DEG)),
    ], dtype=complex)


def _run(topo, delta_deg, fault_node, rf):
    """Solve Y*V = I exactly for one operating point.

    Pure: reads only immutable cached topology data plus its arguments.
    """
    y_rr = topo["y_rr"].copy()
    if fault_node is not None:
        k = topo["rest_pos"][topo["p"][fault_node]]
        y_rr[k, k] += 1.0 / max(float(rf), RF_MIN)   # fault conductance, pu

    v_slack = _slack_vector(delta_deg)
    rhs = -(topo["y_rs"] @ v_slack)

    try:
        v_rest = np.linalg.solve(y_rr, rhs)
    except np.linalg.LinAlgError as exc:
        raise PowerFlowError("singular admittance matrix: %s" % exc)

    # --- validation gate.  Nothing past here may be cached unvalidated. ---
    if not np.all(np.isfinite(v_rest)):
        raise PowerFlowError(
            "non-finite bus voltages (delta=%r node=%r rf=%r)"
            % (delta_deg, fault_node, rf))
    residual = np.max(np.abs(y_rr @ v_rest - rhs))
    if not residual < RESIDUAL_TOL:
        raise PowerFlowError(
            "linear residual %.3e exceeds %.1e (delta=%r node=%r rf=%r)"
            % (residual, RESIDUAL_TOL, delta_deg, fault_node, rf))

    # Physical plausibility, aimed squarely at the degenerate all-zero branch
    # that Newton-Raphson used to fall into: it collapsed *every* bus at once
    # (1e-58, 3e-6, 5e-22 ...) while the slacks stayed put.  Note the gate is
    # on the network MAXIMUM, not on each bus: at delta = 175 degrees the
    # electrical centre of the swing genuinely sits inside the protected line
    # and V_F legitimately falls to 0.04 pu, so a per-bus floor would reject
    # correct answers.  Every bus is fed from a fixed EMF behind a finite
    # impedance, so at least one must stay high; the true minimum of this
    # quantity over the whole operating envelope is 0.51 pu, giving 10x margin.
    v_max = float(np.max(np.abs(v_rest)))
    if not v_max > V_COLLAPSE_FLOOR:
        raise PowerFlowError(
            "degenerate solution: max bus voltage %.3e pu (delta=%r node=%r "
            "rf=%r)" % (v_max, delta_deg, fault_node, rf))

    v_s = complex(v_rest[topo["i_s"]])
    v_f = complex(v_rest[topo["i_f"]])
    v_r = complex(v_rest[topo["i_r"]])

    i_s = (v_s - v_f) * topo["y_sf"] + 1j * topo["b_sf_half"] * v_s
    i_r = (v_r - v_f) * topo["y_fr"] + 1j * topo["b_fr_half"] * v_r

    return Solution(v_s, i_s, i_r, v_r)


def solve(delta_deg=8.0, fault_node=None, rf=0.0, m=0.5, a=0.5):
    """Solve the network for one operating point.

    delta_deg   : angle of the local source EMF (drives load flow / stress)
    fault_node  : "F" | "G" | "B" | None
    rf          : fault resistance in per unit (0 = bolted)
    m, a        : fault position along the protected / adjacent line

    A pure function of its arguments: identical arguments give bit-identical
    results regardless of call history.  Memoised on rounded arguments; only
    validated solutions are ever cached.
    """
    if fault_node is not None and fault_node not in FAULT_NODES:
        raise ValueError("fault_node must be one of None, 'F', 'G', 'B'")

    # Guard against degenerate fault positions collapsing a branch to zero.
    m = min(max(m, 0.02), 0.98)
    a = min(max(a, 0.02), 0.98)

    if fault_node is None:
        rf = 0.0
    key = (round(float(delta_deg), 2), fault_node, round(float(rf), 4),
           round(m, 3), round(a, 3))
    hit = _SOLVE_CACHE.get(key)
    if hit is not None:
        return hit

    topo = _get_topology(key[3], key[4])
    sol = _run(topo, key[0], fault_node, key[2])   # raises on failure

    if len(_SOLVE_CACHE) >= _SOLVE_CACHE_MAX:
        _SOLVE_CACHE.clear()
    _SOLVE_CACHE[key] = sol
    return sol


def prefault(delta_deg=8.0):
    return solve(delta_deg=delta_deg, fault_node=None)


# --- cross-validation against pandapower's own Newton-Raphson ---------------

def _runpp_solution(m, a, delta_deg, fault_node, rf):
    """Solve the same point with pp.runpp, for cross-validation only.

    Not used by solve(): Newton-Raphson admits the spurious zero-voltage branch
    described in the module docstring.  Used by self_check to confirm the
    linear solve agrees with pandapower over the well-conditioned range.
    """
    topo = _build_topology(m, a)          # a private net, never shared
    net, bus = topo["net"], topo["bus"]
    net.ext_grid.at[topo["eg_s"], "va_degree"] = delta_deg
    if fault_node is not None:
        pp.create_shunt(net, bus[fault_node], q_mvar=0.0,
                        p_mw=VN_KV * VN_KV / (max(float(rf), RF_MIN) * Z_BASE))
    pp.runpp(net, numba=False, init="dc", max_iteration=100)

    def volts(name):
        i = bus[name]
        return cmath.rect(net.res_bus.vm_pu.at[i],
                          math.radians(net.res_bus.va_degree.at[i]))

    v_s, v_r = volts("S"), volts("R")

    def current_into(line_idx, end, v):
        p = net.res_line["p_%s_mw" % end].at[line_idx]
        q = net.res_line["q_%s_mvar" % end].at[line_idx]
        return (complex(p, q) / S_BASE_MVA / v).conjugate()

    return Solution(v_s, current_into(topo["li_sf"], "from", v_s),
                    current_into(topo["li_fr"], "to", v_r), v_r)


# --- sanity properties the model must satisfy -------------------------------

HIF_RF = (2.0, 4.0, 6.0, 8.0, 12.0)

# The operating range the swing scenarios actually reach.
DELTA_MAX_DEG = 175.0

# Poisoning began somewhere between 60 and 70 degrees, so `benign/stressed_load`
# (which reaches delta = 75) was enough to corrupt the process on its own.  A
# low-angle-only fuzz reports success on a broken solver, so these cases
# deliberately straddle the trigger.
_PURITY_CASES = [
    dict(delta_deg=22.0),
    dict(delta_deg=8.0),
    dict(delta_deg=0.0),
    dict(delta_deg=60.0),
    dict(delta_deg=70.0),
    dict(delta_deg=75.0),
    dict(delta_deg=164.5),
    dict(delta_deg=175.0),
    dict(delta_deg=90.0, fault_node="F", rf=6.0),
    dict(delta_deg=8.0, fault_node="F", rf=0.0),
    dict(delta_deg=45.0, fault_node="G", rf=0.0, m=0.2, a=0.8),
    dict(delta_deg=120.0, fault_node="B", rf=2.0, m=0.9),
    dict(delta_deg=30.0, fault_node="F", rf=12.0, m=0.05, a=0.05),
]


def _tup(s):
    return (s.V_s, s.I_s, s.I_r, s.V_r)


def _purity_check():
    """Would solve() ever return a different answer for the same arguments?

    Computes a reference for a spread of cases from a cold cache, then re-runs
    them in several randomised orders -- and in the specific order that broke
    it (a 175-degree solve interleaved before a 22-degree one) -- asserting
    bit-identical phasors every time.
    """
    _SOLVE_CACHE.clear()
    ref = {}
    for case in _PURITY_CASES:
        key = tuple(sorted(case.items()))
        ref[key] = _tup(solve(**case))

    problems = []

    # (1) The exact reported regression: 175 poisons 22.
    _SOLVE_CACHE.clear()
    solve(delta_deg=175.0)
    got = _tup(solve(delta_deg=22.0))
    want = ref[tuple(sorted(dict(delta_deg=22.0).items()))]
    if got != want:
        problems.append("175-then-22: |I_s| %.6f != %.6f"
                        % (abs(got[1]), abs(want[1])))

    # (1b) Threshold scan: no high-angle first solve may perturb a later
    # low-angle one.  This is the generalised form of the reported bug, and it
    # sweeps straight through the 60-70 degree region where poisoning started.
    for poison in [50.0, 60.0, 65.0, 70.0, 75.0, 90.0, 120.0, 150.0,
                   164.5, 175.0]:
        for victim in (8.0, 22.0):
            _SOLVE_CACHE.clear()
            solve(delta_deg=poison)
            got_v = _tup(solve(delta_deg=victim))
            _SOLVE_CACHE.clear()
            want_v = _tup(solve(delta_deg=victim))
            if got_v != want_v:
                problems.append(
                    "solve(%.1f) poisons solve(%.1f): |I_s| %.6f != %.6f"
                    % (poison, victim, abs(got_v[1]), abs(want_v[1])))

    # (1c) The degenerate answer had z_app == ZS exactly (84.29 deg, the line
    # angle), which is why it read as an in-zone fault.  Assert we are nowhere
    # near it for the healthy cases the relay sees most often.
    for d in (8.0, 22.0, 75.0):
        z = solve(delta_deg=d).z_app
        if abs(z - ZS) < 1e-3:
            problems.append("delta=%.1f returned the degenerate z_app == ZS" % d)

    # (2) Randomised call orders, cold cache each time.
    rng = random.Random(20240617)
    order = list(_PURITY_CASES)
    for _ in range(12):
        rng.shuffle(order)
        _SOLVE_CACHE.clear()
        for case in order:
            key = tuple(sorted(case.items()))
            if _tup(solve(**case)) != ref[key]:
                problems.append("order-dependent: %r" % (case,))

    # (3) Warm cache must agree with cold cache.
    for case in _PURITY_CASES:
        key = tuple(sorted(case.items()))
        if _tup(solve(**case)) != ref[key]:
            problems.append("cache disagrees with cold solve: %r" % (case,))

    # (4) Descending sweep across the full range must match an ascending one.
    _SOLVE_CACHE.clear()
    up = [_tup(solve(delta_deg=d * 2.5)) for d in range(71)]
    _SOLVE_CACHE.clear()
    down = [_tup(solve(delta_deg=d * 2.5)) for d in range(70, -1, -1)][::-1]
    if up != down:
        problems.append("ascending and descending delta sweeps disagree")

    return problems


def self_check():
    """Assert the Kirchhoff facts the whole safety argument rests on."""
    checks = []

    pre = prefault()
    checks.append(("healthy: charging-compensated differential < 0.02 pu",
                   pre.i_diff < 0.02))
    checks.append(("healthy: load current in [0.4, 1.0] pu",
                   0.4 <= abs(pre.I_s) <= 1.0))
    checks.append(("healthy: load current rises with delta",
                   abs(solve(delta_deg=20.0).I_s) > abs(pre.I_s)))

    internal = solve(fault_node="F", rf=0.0)
    checks.append(("internal bolted: differential > 3.0 pu",
                   internal.i_diff > 3.0))

    hifs = [solve(fault_node="F", rf=rf) for rf in HIF_RF]
    diffs = [s.i_diff for s in hifs]
    checks.append(("high-Z internal: differential strictly decreasing in rf",
                   all(diffs[i] > diffs[i + 1] for i in range(len(diffs) - 1))))
    checks.append(("high-Z internal: band spans ~0.30 pu down to ~0.05 pu",
                   0.25 <= diffs[0] <= 0.40 and 0.04 <= diffs[-1] <= 0.07))
    checks.append(("high-Z internal: band straddles the 0.10 pu shield floor",
                   diffs[0] > 0.10 > diffs[-1]))
    checks.append(("high-Z internal: distance element under-reaches",
                   all(abs(s.z_app) > abs(0.8 * ZL) for s in hifs)))

    through = solve(fault_node="G", rf=0.0)
    checks.append(("external fwd: differential < 0.03 pu",
                   through.i_diff < 0.03))
    checks.append(("external fwd: through-current > 2.0 pu",
                   through.i_through > 2.0))

    reverse = solve(fault_node="B", rf=0.0)
    checks.append(("external rev: differential < 0.03 pu",
                   reverse.i_diff < 0.03))
    z = reverse.z_app
    checks.append(("external rev: apparent impedance is reverse",
                   (z * ZL.conjugate()).real < 0.0))

    # --- purity: the regression that corrupted two experiment runs ---------
    problems = _purity_check()
    checks.append(("PURITY: solve() is order-independent (175-then-22 + "
                   "12 shuffled orders + sweep)", not problems))
    for p in problems[:5]:
        checks.append(("  purity detail: " + p, False))

    # --- full operating range 0..175 degrees -------------------------------
    bad = []
    for i in range(int(DELTA_MAX_DEG) + 1):
        for node, rf in ((None, 0.0), ("F", 0.0), ("F", 6.0),
                         ("G", 0.0), ("B", 0.0)):
            try:
                s = solve(delta_deg=float(i), fault_node=node, rf=rf)
            except PowerFlowError as exc:
                bad.append((i, node, rf, str(exc)))
                continue
            if not (abs(s.V_s) < 5.0 and abs(s.I_s) < 1e4):
                bad.append((i, node, rf, "implausible magnitudes"))
    checks.append(("full range 0-175 deg x 5 fault cases: all solve cleanly",
                   not bad))

    # Healthy voltage must stay physical across the whole swing range.
    v_min = min(abs(solve(delta_deg=float(i)).V_s)
                for i in range(int(DELTA_MAX_DEG) + 1))
    checks.append(("healthy sweep: |V_s| stays above 0.15 pu", v_min > 0.15))

    # --- cross-validation against pandapower's Newton-Raphson --------------
    # Restricted to the well-conditioned range where NR is trustworthy; the
    # linear solve is the authority outside it.
    worst = 0.0
    for delta in (0.0, 8.0, 22.0, 45.0):
        for node, rf in ((None, 0.0), ("F", 6.0), ("G", 2.0), ("B", 2.0)):
            mine = solve(delta_deg=delta, fault_node=node, rf=rf)
            theirs = _runpp_solution(0.5, 0.5, delta, node, rf)
            worst = max(worst, abs(mine.I_s - theirs.I_s),
                        abs(mine.V_s - theirs.V_s))
    checks.append(("cross-validates against pp.runpp (max phasor error "
                   "%.2e)" % worst, worst < 1e-6))

    # --- the validation gate itself must actually bite ---------------------
    gate_works = False
    try:
        topo = _get_topology(0.5, 0.5)
        saved = topo["y_rr"]
        topo["y_rr"] = np.full_like(saved, np.nan)
        try:
            _run(topo, 8.0, None, 0.0)
        except PowerFlowError:
            gate_works = True
        finally:
            topo["y_rr"] = saved
    except Exception:
        gate_works = False
    checks.append(("validation gate rejects a corrupt solve", gate_works))

    return checks


def _table():
    """Calibration table printed by `python -m gs.power`."""
    lines = []
    pre = prefault()
    lines.append("healthy: |I_s| = %.4f pu   i_diff = %.3e pu   |V_s| = %.4f pu"
                 % (abs(pre.I_s), pre.i_diff, abs(pre.V_s)))
    lines.append("charging compensation B/2 = %.6f pu (read from the "
                 "as-built network)" % B_HALF)
    lines.append("")
    lines.append("  %-10s %12s %10s %12s" %
                 ("case", "i_diff", "i_through", "|z_app|/|0.8ZL|"))
    ref = abs(0.8 * ZL)
    rows = [("bolted F", solve(fault_node="F", rf=0.0))]
    rows += [("rf=%-5.1f" % rf, solve(fault_node="F", rf=rf)) for rf in HIF_RF]
    rows += [("ext fwd G", solve(fault_node="G", rf=0.0)),
             ("ext rev B", solve(fault_node="B", rf=0.0)),
             ("healthy", pre)]
    for name, s in rows:
        lines.append("  %-10s %12.5f %10.4f %12.3f"
                     % (name, s.i_diff, s.i_through, abs(s.z_app) / ref))
    return "\n".join(lines)


if __name__ == "__main__":
    import time

    ok = True
    for name, passed in self_check():
        print(("  PASS  " if passed else "  FAIL  ") + name)
        ok = ok and passed
    print("model self-check:", "OK" if ok else "BROKEN")
    print()
    print(_table())
    print()

    def episode():
        for i in range(400):
            d = 8.0 + 60.0 * i / 1000.0
            solve(delta_deg=d, fault_node="F" if i >= 20 else None,
                  rf=3.0, m=0.4, a=0.5)
            solve(delta_deg=d)
        return 800

    _SOLVE_CACHE.clear()
    t0 = time.time()
    n = episode()
    print("solve() throughput, cold cache: %8.0f calls/s"
          % (n / (time.time() - t0)))
    t0 = time.time()
    n = sum(episode() for _ in range(20))
    print("solve() throughput, warm cache: %8.0f calls/s"
          % (n / (time.time() - t0)))
