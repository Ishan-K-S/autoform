"""Machine-checked verification of gs/shield.py with Z3.

VERSION 3 -- re-encoded against the repaired shield.  Three defects have been
found and fixed so far; the encoding tracks the artifact, and the defects and
the counterexamples that exposed them are kept as regression theorems in
`prove_v1_regressions()`, where they must now come back `unsat`:

  D1  the rate limiter was a JUMPING window keyed off `State.last_grant_ms`,
      and a backwards clock step bought a third grant inside one window;
  D2  the RESTRICTED trust tier was provably unobservable;
  D3  the v2 fix for D1 was ONE-SIDED: it rejected backwards timestamps but
      accepted arbitrarily large forward ones, so a single sample dated far in
      the future poisoned the watermark and denied service to every honest
      sample after it.

v3 replaces the bare watermark with a clock PLAUSIBILITY WINDOW that an
implausible timestamp cannot move at all (theorem P2a), which is what makes
denial-of-service resistance provable rather than hoped for.

Three layers, three techniques, all unbounded in the input domain:

  Layer 0 -- FLOATING POINT.  The new non-finite handling cannot be stated in
      the reals at all, so it is proved twice: once over Z3's IEEE-754
      Float64 theory (genuine NaN and +/-inf), and once over an abstraction
      of reals-plus-finiteness-flags that is cheap enough to compose with the
      rest of the proof.

  Layer 1 -- NUMERIC.  Real arithmetic.  Every theorem is discharged by
      asserting its NEGATION and obtaining `unsat`, which is a proof over the
      full uncountable domain -- unlike `shield.lemma_sensitivity_floor`,
      which samples 200001 points and therefore proves nothing about the
      remaining continuum.

  Layer 2 -- LOGIC.  `decide` / `commit` / `Shield.step` become a symbolic
      transition relation with FULLY UNCONSTRAINED inputs at every step (the
      AI is maximally hostile: it may request a trip every millisecond with
      arbitrary parameters).  Invariants are attacked first by bounded model
      checking, then closed by k-induction, reporting the smallest k.

      NOTE THE HEADLINE CHANGE: the transition relation no longer assumes
      anything whatsoever about the clock.  `now_ms` is a free integer at
      every step, free to jump backwards, and I2 is proved anyway, because
      the shield now enforces the watermark itself.

Honesty policy: anything that only survives BMC to depth N is reported as
"bounded-to-N", never as "proved".  Counterexamples are reported verbatim.

Entry points (see INTERFACES.md):  prove_sensitivity_floor(),
prove_shield_invariants().
"""

import time

from z3 import (And, Bool, BoolVal, Function, If, Implies, Int, IntVal, Not,
                Or, Real,
                Solver, Optimize, sat, unsat, unknown,
                FPSort, FP, FPVal, RNE, fpGT, fpLT, fpMul, fpIsNaN, fpIsInf)

try:                                    # works as `python -m gs.verify`
    from gs import shield as S
except ImportError:                     # and as `python gs/verify.py`
    import importlib.util as _ilu
    import os as _os
    _p = _os.path.join(_os.path.dirname(_os.path.abspath(__file__)),
                       "shield.py")
    _spec = _ilu.spec_from_file_location("gs_shield", _p)
    S = _ilu.module_from_spec(_spec)
    _spec.loader.exec_module(S)

# --- constants, taken from the artifact, never re-typed here ---------------
P0_NOM, K_NOM = S.P0_NOM, S.K_NOM
P0_MIN, K_MIN = S.P0_MIN, S.K_MIN
A1, A2 = S.A1_CT_ERROR, S.A2_CHARGING
MAX_GRANTS, WINDOW_MS, VETO_LIMIT = S.MAX_GRANTS, S.WINDOW_MS, S.VETO_LIMIT
MAX_CLOCK_STEP = S.MAX_CLOCK_STEP_MS
EXCURSION_LIMIT = S.EXCURSION_LIMIT
DWELL_MS = S.DWELL_MS
NORMAL, RESTRICTED, BASELINE_ONLY = S.NORMAL, S.RESTRICTED, S.BASELINE_ONLY

NEG_INF = -10 ** 9          # ghost-history sentinel (verifier-local only)


def zmax(a, b):
    return If(a > b, a, b)


def _check(name, negation, statement, extra=None, timeout_ms=0):
    """Discharge `statement` by refuting `negation`.  Returns a result dict."""
    s = Solver()
    if timeout_ms:
        s.set("timeout", timeout_ms)
    s.add(negation)
    t0 = time.perf_counter()
    r = s.check()
    dt = time.perf_counter() - t0
    out = {"name": name, "statement": statement, "ms": round(dt * 1000, 2),
           "proved": r == unsat, "status": str(r), "counterexample": None}
    if r == sat:
        m = s.model()
        out["counterexample"] = {str(d): str(m[d]) for d in m.decls()}
    if extra:
        out.update(extra)
    return out


def _witness(name, formula, statement, extra=None):
    """The dual of _check: EXPECT `sat`, and report the witness.  Used where
    the desired outcome is that two things are distinguishable."""
    s = Solver()
    s.add(formula)
    t0 = time.perf_counter()
    r = s.check()
    dt = time.perf_counter() - t0
    out = {"name": name, "statement": statement, "ms": round(dt * 1000, 2),
           "found": r == sat, "status": str(r), "witness": None}
    if r == sat:
        m = s.model()
        out["witness"] = {str(d): str(m[d]) for d in m.decls()}
    if extra:
        out.update(extra)
    return out


# ===========================================================================
# LAYER 0 -- non-finite handling
# ===========================================================================
#
# gs/shield.py:71-83 now reads, in essence:
#
#     if not (isfinite(i_diff) and isfinite(i_restraint)): return False
#     if i_restraint < 0.0: i_restraint = 0.0
#     p0_floor, k_floor = thresholds(cert_ok)
#     p0 = req_p0 if (isfinite(req_p0) and req_p0 > p0_floor) else p0_floor
#     k  = req_k  if (isfinite(req_k)  and req_k  > k_floor)  else k_floor
#     threshold = p0 if p0 > k * i_restraint else k * i_restraint
#     return i_diff > threshold
#
# Two encodings follow.  The FP one is the honest one (real NaN, real inf);
# the abstract one is the one cheap enough to compose with Layer 2.

F64 = FPSort(11, 53)


def _fp_finite(x):
    return Not(Or(fpIsNaN(x), fpIsInf(x)))


def fp_differential_ok(i_diff, i_restraint, cert_ok, req_p0, req_k,
                       mul=None):
    """`differential_ok` over genuine IEEE-754 binary64, NaN and inf included.

    `mul` defaults to correctly-rounded binary64 multiplication.  Passing an
    uninterpreted function instead yields a STRONGER theorem: one that holds
    for any multiplication at all."""
    if mul is None:
        def mul(a, b):
            return fpMul(RNE(), a, b)
    zero = FPVal(0.0, F64)
    p0_floor = If(cert_ok, FPVal(P0_MIN, F64), FPVal(P0_NOM, F64))
    k_floor = If(cert_ok, FPVal(K_MIN, F64), FPVal(K_NOM, F64))

    ir = If(fpLT(i_restraint, zero), zero, i_restraint)        # shield.py:73-74
    p0 = If(And(_fp_finite(req_p0), fpGT(req_p0, p0_floor)),   # shield.py:80
             req_p0, p0_floor)
    k = If(And(_fp_finite(req_k), fpGT(req_k, k_floor)),       # shield.py:81
            req_k, k_floor)
    kir = mul(k, ir)
    threshold = If(fpGT(p0, kir), p0, kir)                     # shield.py:82
    inputs_finite = And(_fp_finite(i_diff), _fp_finite(i_restraint))
    return And(inputs_finite, fpGT(i_diff, threshold))         # shield.py:71,83


def prove_nonfinite_handling(timeout_ms=60000, fpm_timeout_ms=45000):
    """Layer 0.  The obligations that only exist because of the v2 change.

    Two of these need care, and the care is worth spelling out because it is
    the only place in this report where a theorem is discharged modulo a side
    condition the solver could not close.

      * N2 is proved with an UNINTERPRETED multiplication.  That is strictly
        stronger than proving it for `fpMul`: the equivalence holds whatever
        the multiply does, so it depends on the clamp structure alone.
      * N3 is proved modulo one axiom, FPM (below), which Z3's bit-blaster
        cannot discharge within 45 s.  FPM is a standard monotonicity fact
        about correctly-rounded IEEE-754 multiplication, not a claim about
        this code -- but it is ASSUMED here, and is listed as such in
        docs/PROOF.md.
    """
    out = []
    idf, irr = FP("i_diff", F64), FP("i_restraint", F64)
    rp0, rk = FP("req_p0", F64), FP("req_k", F64)
    cert = Bool("cert_ok")
    zero = FPVal(0.0, F64)
    res = fp_differential_ok(idf, irr, cert, rp0, rk)

    # N1 -- fail closed on a non-finite MEASUREMENT.
    out.append(_check(
        "N1 non-finite measurement fails closed (FP64)",
        And(Not(And(_fp_finite(idf), _fp_finite(irr))), res),
        "forall FP inputs . (i_diff or i_restraint non-finite) "
        "=> not differential_ok(..)", timeout_ms=timeout_ms))

    # N2 -- a non-finite REQUEST cannot deny service.  This is the direction
    # the IEEE-754 accident did NOT cover in v1: req_p0 = +inf made
    # `req_p0 > p0_floor` true and became the threshold, so a hostile model
    # could demand an unreachable pickup and veto every real fault.
    # Proved with an uninterpreted multiply => holds for ANY multiplication.
    mul_u = Function("mul_abstract", F64, F64, F64)
    res_u = fp_differential_ok(idf, irr, cert, rp0, rk,
                               mul=lambda a, b: mul_u(a, b))
    res_floor_u = fp_differential_ok(
        idf, irr, cert,
        If(cert, FPVal(P0_MIN, F64), FPVal(P0_NOM, F64)),
        If(cert, FPVal(K_MIN, F64), FPVal(K_NOM, F64)),
        mul=lambda a, b: mul_u(a, b))
    out.append(_check(
        "N2 non-finite request cannot deny service (FP64, any multiply)",
        And(Not(_fp_finite(rp0)), Not(_fp_finite(rk)), res_u != res_floor_u),
        "forall FP inputs . req_p0, req_k non-finite => differential_ok(..) "
        "= differential_ok(.. at the floors).  Multiplication left "
        "uninterpreted, so the result does not depend on FP arithmetic.",
        timeout_ms=timeout_ms))

    # N4 -- a FINITE negative restraint is clamped, not exploited.  (The
    # non-finite case is N1: shield.py:71 rejects before shield.py:73 clamps.)
    out.append(_check(
        "N4 finite negative i_restraint clamps to zero (FP64)",
        And(_fp_finite(irr), fpLT(irr, zero),
            res != fp_differential_ok(idf, zero, cert, rp0, rk)),
        "forall FP inputs . finite i_restraint < 0 => differential_ok(..) = "
        "differential_ok(.. with i_restraint = 0)", timeout_ms=timeout_ms))

    # FPM -- the side condition.  Correctly-rounded binary64 multiplication is
    # monotone in its first argument for a non-negative second argument.
    # Attempted honestly; Z3 does not close it.
    x, y = FP("fpm_x", F64), FP("fpm_y", F64)
    fpm = _check(
        "FPM fpMul monotone in arg1 for arg2 >= 0 (side condition)",
        And(_fp_finite(x), _fp_finite(y), Not(fpLT(y, zero)),
            Not(fpLT(x, FPVal(K_MIN, F64))),
            fpLT(fpMul(RNE(), x, y), fpMul(RNE(), FPVal(K_MIN, F64), y))),
        "forall finite x >= K_MIN, finite y >= 0 . "
        "fl(x*y) >= fl(K_MIN*y)   [standard IEEE-754 fact, NOT a claim about "
        "this code -- assumed, not proved]",
        timeout_ms=fpm_timeout_ms)
    out.append(fpm)

    # N3 -- the clamp theorem in floating point, modulo FPM.  The two products
    # are abstracted to fresh variables related only by FPM, so this checks
    # the CLAMP LOGIC over FP comparison semantics with no multiplication.
    m_k, m_min = FP("m_k", F64), FP("m_min", F64)
    p0_floor = If(cert, FPVal(P0_MIN, F64), FPVal(P0_NOM, F64))
    p0 = If(And(_fp_finite(rp0), fpGT(rp0, p0_floor)), rp0, p0_floor)
    thr_a = If(fpGT(p0, m_k), p0, m_k)
    floor_a = If(fpGT(FPVal(P0_MIN, F64), m_min), FPVal(P0_MIN, F64), m_min)
    res_a = And(_fp_finite(idf), _fp_finite(irr), fpGT(idf, thr_a))
    fpm_axiom = And(_fp_finite(m_k), _fp_finite(m_min), Not(fpLT(m_k, m_min)))
    n3 = _check(
        "N3 clamp theorem in IEEE-754 binary64, modulo FPM (T2 in FP)",
        And(fpm_axiom, res_a, Not(fpGT(idf, floor_a))),
        "forall FP inputs incl. NaN/inf . differential_ok(..) => "
        "i_diff > max(P0_MIN, K_MIN * max(i_restraint,0)) in binary64, "
        "GIVEN FPM", timeout_ms=timeout_ms)
    n3["modulo"] = "FPM (unproved side condition, see above)"
    out.append(n3)
    return out


# --- the abstract (reals + finiteness flags) encoding used by layers 1 & 2 --

def z_thresholds(cert_ok):
    return (If(cert_ok, P0_MIN, P0_NOM), If(cert_ok, K_MIN, K_NOM))


def z_differential_ok(i_diff, i_restraint, cert_ok, req_p0, req_k,
                      fin_diff=None, fin_restraint=None,
                      fin_p0=None, fin_k=None):
    """`differential_ok` over the reals, with explicit finiteness predicates.

    A non-finite input is modelled as a Boolean flag rather than an FP value:
    when the flag is false the real variable is unconstrained and IGNORED, so
    the abstraction is sound (it admits every FP behaviour and more).  Passing
    all four flags as None recovers the all-finite case.
    """
    if fin_diff is None:
        fin_diff = BoolVal(True)
    if fin_restraint is None:
        fin_restraint = BoolVal(True)
    if fin_p0 is None:
        fin_p0 = BoolVal(True)
    if fin_k is None:
        fin_k = BoolVal(True)

    p0_floor, k_floor = z_thresholds(cert_ok)
    ir = If(i_restraint < 0, 0, i_restraint)                   # shield.py:73-74
    p0 = If(And(fin_p0, req_p0 > p0_floor), req_p0, p0_floor)  # shield.py:80
    k = If(And(fin_k, req_k > k_floor), req_k, k_floor)        # shield.py:81
    threshold = If(p0 > k * ir, p0, k * ir)                    # shield.py:82
    return And(fin_diff, fin_restraint, i_diff > threshold)    # shield.py:71,83


# ===========================================================================
# LAYER 1 -- the numeric layer
# ===========================================================================

def prove_sensitivity_floor():
    """Unbounded Z3 proofs replacing `shield.lemma_sensitivity_floor`."""
    results = []

    # --- T1 -----------------------------------------------------------------
    ir = Real("i_restraint")
    lhs = A1 * ir + A2
    rhs = zmax(P0_MIN, K_MIN * ir)
    results.append(_check(
        "T1 no-false-trip floor (ir >= 0, unbounded above)",
        And(ir >= 0, Not(lhs < rhs)),
        "forall i_restraint >= 0 . A1*ir + A2 < max(P0_MIN, K_MIN*ir)"))

    results.append(_check(
        "T1b same statement for ir < 0 (non-physical domain)",
        And(ir < 0, Not(lhs < rhs)),
        "forall i_restraint < 0 . A1*ir + A2 < max(P0_MIN, K_MIN*ir)"))

    # --- T2: the clamp cannot be defeated by any adversarial proposal -------
    idf, irr = Real("i_diff"), Real("i_restraint2")
    rp0, rk = Real("req_p0"), Real("req_k")
    cert = Bool("cert_ok")
    fp0, fk = Bool("fin_p0"), Bool("fin_k")
    fd, fr = Bool("fin_diff"), Bool("fin_restraint")
    dok = z_differential_ok(idf, irr, cert, rp0, rk, fd, fr, fp0, fk)
    ir_c = If(irr < 0, 0, irr)
    results.append(_check(
        "T2 clamp non-defeat (adversarial req_p0, req_k in R u {non-finite})",
        And(dok, Not(idf > zmax(P0_MIN, K_MIN * ir_c))),
        "forall req_p0,req_k,i_diff,i_restraint,cert_ok, finite or not . "
        "differential_ok(..) => i_diff > max(P0_MIN, K_MIN*max(i_restraint,0))"))

    # --- T4: outside the certified region, nominal thresholds apply ---------
    results.append(_check(
        "T4 certified-region containment (numeric half of I5)",
        And(z_differential_ok(idf, irr, False, rp0, rk, fd, fr, fp0, fk),
            Not(idf > zmax(P0_NOM, K_NOM * ir_c))),
        "forall .. . differential_ok(..,cert_ok=False,..) "
        "=> i_diff > max(P0_NOM, K_NOM*max(i_restraint,0))"))

    # --- T3: composition -- A1/A2 noise can never be granted ----------------
    results.append(_check(
        "T3 composition: A1/A2 noise is never admitted by differential_ok",
        And(irr >= 0, idf >= 0, idf <= A1 * irr + A2,
            z_differential_ok(idf, irr, cert, rp0, rk, fd, fr, fp0, fk)),
        "forall .. . 0 <= i_diff <= A1*i_restraint + A2 and i_restraint >= 0 "
        "=> not differential_ok(..)"))

    # --- T5: monotonicity of the threshold in the AI's request --------------
    # The AI can only ever make the relay LESS sensitive.  Stated directly:
    # raising a request can never turn a veto into a grant.
    rp0b, rkb = Real("req_p0_b"), Real("req_k_b")
    results.append(_check(
        "T5 request monotonicity (a larger request never buys a grant)",
        And(rp0b >= rp0, rkb >= rk, irr >= 0,
            z_differential_ok(idf, irr, cert, rp0b, rkb),
            Not(z_differential_ok(idf, irr, cert, rp0, rk))),
        "forall .. . req' >= req => differential_ok(req') "
        "=> differential_ok(req)"))

    # --- worst-case margin, exactly, by optimisation ------------------------
    opt = Optimize()
    m_ir = Real("m_ir")
    margin = Real("margin")
    opt.add(m_ir >= 0)
    opt.add(margin == zmax(P0_MIN, K_MIN * m_ir) - (A1 * m_ir + A2))
    h = opt.minimize(margin)
    t0 = time.perf_counter()
    opt.check()
    opt_ms = round((time.perf_counter() - t0) * 1000, 2)
    lower = opt.lower(h)
    mdl = opt.model()
    margin_info = {
        "infimum_pu": str(lower),
        "infimum_float": float(lower.as_fraction()) if hasattr(
            lower, "as_fraction") else None,
        "attained_at_i_restraint": str(mdl[m_ir]) if mdl[m_ir] is not None
        else None,
        "ms": opt_ms,
        "threshold_breakpoint_ir": P0_MIN / K_MIN,
        "slope_headroom": K_MIN - A1,
    }

    proved = all(r["proved"] for r in results)
    return {
        "layer": "numeric",
        "method": "Z3 QF_NRA, negation refuted (unsat) -- unbounded",
        "theorems": results,
        "worst_case_margin": margin_info,
        "proved": proved and margin_info["slope_headroom"] > 0,
        "replaces": "shield.lemma_sensitivity_floor (dense sampling, not a "
                    "proof: 200001 points of an uncountable domain)",
    }


# ===========================================================================
# LAYER 2 -- the logic layer
# ===========================================================================

class Step(object):
    """Symbolic state s_i, the hostile inputs at step i, and s_{i+1}.

    State mirrors `shield.State` v4 exactly:
        mode, latched, grant_times (a 2-slot ascending window), vetoes,
        excursions, diff_run, last_seen_ms (None-able: a value plus `seen`).

    Ghost variables are write-only observers used only to STATE properties;
    they appear in no guard, so adding them is sound:
        g1..g4, ng   -- the four most recent grant timestamps and the total
        dprev1..3    -- diff_ok as it was at the 1st/2nd/3rd previous steps
    """

    def __init__(self, i):
        self.i = i
        # --- concrete state ------------------------------------------------
        self.mode = Int("mode_%d" % i)
        self.latched = Bool("latched_%d" % i)
        self.vetoes = Int("vetoes_%d" % i)
        self.excursions = Int("excursions_%d" % i)   # v4: separate counter
        self.diff_run = Int("diff_run_%d" % i)       # v4: corroboration run
        # grant_times, ascending, oldest first.  MAX_GRANTS == 2, so:
        self.n_gt = Int("n_gt_%d" % i)          # len(st.grant_times), 0..2
        self.gt0 = Int("gt0_%d" % i)            # st.grant_times[0], oldest
        self.gt1 = Int("gt1_%d" % i)            # st.grant_times[1], newest
        # last_seen_ms: None is modelled as `seen == False`.
        self.seen = Bool("seen_%d" % i)
        self.ls = Int("last_seen_ms_%d" % i)
        # --- ghosts --------------------------------------------------------
        self.g1 = Int("g1_%d" % i)
        self.g2 = Int("g2_%d" % i)
        self.g3 = Int("g3_%d" % i)
        self.g4 = Int("g4_%d" % i)
        self.ng = Int("ng_%d" % i)
        self.dprev1 = Bool("dprev1_%d" % i)
        self.dprev2 = Bool("dprev2_%d" % i)
        self.dprev3 = Bool("dprev3_%d" % i)
        self.vmax = Int("vmax_%d" % i)   # high-water mark of `vetoes`
        # --- hostile inputs at step i (utterly unconstrained) --------------
        self.now = Int("now_%d" % i)            # NO monotonicity assumption
        self.want = Bool("want_trip_%d" % i)
        self.time_ok = Bool("time_ok_%d" % i)
        self.remote_ok = Bool("remote_ok_%d" % i)
        # v5: the LOCAL addend's provenance.  i_diff = |I_local + I_remote| is
        # a SUM; authenticating only the remote half leaves the sum forgeable.
        self.local_ok = Bool("local_ok_%d" % i)
        self.forward = Bool("forward_%d" % i)
        self.reclose = Bool("reclose_auth_%d" % i)
        self.cert = Bool("cert_ok_%d" % i)
        self.baseline = Bool("baseline_trip_%d" % i)
        self.i_diff = Real("i_diff_%d" % i)
        self.i_restraint = Real("i_restraint_%d" % i)
        self.req_p0 = Real("req_p0_%d" % i)
        self.req_k = Real("req_k_%d" % i)
        self.fin_diff = Bool("fin_diff_%d" % i)
        self.fin_restraint = Bool("fin_restraint_%d" % i)
        self.fin_p0 = Bool("fin_p0_%d" % i)
        self.fin_k = Bool("fin_k_%d" % i)
        # --- the AUTHENTICATED OPERATOR channel (v4) -----------------------
        # `reinstate` is NOT part of the Proposal record and Shield.step never
        # passes it; it reaches `commit` only from the same authenticated
        # channel as reclose_auth.  Left free here so the transition relation
        # covers the operator's action as well as the model's.
        self.reinstate = Bool("reinstate_%d" % i)

        # --- Shield.step, shield.py:332-344 --------------------------------
        self.effective_cert = And(self.cert, self.mode == NORMAL)
        self.diff_ok = z_differential_ok(
            self.i_diff, self.i_restraint, self.effective_cert,
            self.req_p0, self.req_k, self.fin_diff, self.fin_restraint,
            self.fin_p0, self.fin_k)

        # --- decide(), shield.py:222-258 -----------------------------------
        self.backwards = And(self.seen, self.now < self.ls)
        self.jumped = And(self.seen, self.now - self.ls > MAX_CLOCK_STEP)
        self.excursion = Or(self.backwards, self.jumped)
        self.rate_blocked = And(self.n_gt >= MAX_GRANTS,
                                self.now - self.gt0 < WINDOW_MS)
        # v4 DWELL: the corroboration must have been SUSTAINED.
        self.dwell_met = self.diff_run + 1 >= DWELL_MS
        self.grant = And(self.want,
                         self.mode != BASELINE_ONLY,
                         Not(self.latched),
                         Not(self.excursion),
                         Not(self.rate_blocked),
                         self.time_ok,
                         self.remote_ok,                        # :263
                         self.local_ok,                         # :276 (v5)
                         self.forward,
                         self.diff_ok,
                         self.dwell_met)
        self.trip_out = Or(self.baseline, self.grant)

    def state_vars(self):
        return [self.mode, self.latched, self.vetoes, self.excursions,
                self.diff_run, self.n_gt, self.gt0, self.gt1, self.seen,
                self.ls, self.g1, self.g2, self.g3, self.g4, self.ng,
                self.dprev1, self.dprev2, self.dprev3, self.vmax]


def init(s):
    return And(s.mode == NORMAL, Not(s.latched), s.vetoes == 0,
               s.excursions == 0, s.diff_run == 0,
               s.n_gt == 0, s.gt0 == NEG_INF, s.gt1 == NEG_INF,
               Not(s.seen), s.ls == NEG_INF,
               s.g1 == NEG_INF, s.g2 == NEG_INF, s.g3 == NEG_INF,
               s.g4 == NEG_INF, s.ng == 0,
               Not(s.dprev1), Not(s.dprev2), Not(s.dprev3),
               s.vmax == 0)


def trans(a, b, clock="free"):
    """b == commit(a, now, decide(...), ..., reinstate=, diff_ok=), exactly as
    shield.commit v4 does it, in the same order.

    `clock` selects the time model:
        "free"      -- now_ms is a completely unconstrained integer at every
                       step.  NO assumption at all.  The default.
        "monotone"  -- now >= previous now (the retired v1 assumption A5),
                       kept only so the regressions can compare.
    """
    cs = []
    if clock == "monotone":
        cs += [Or(Not(a.seen), a.now >= a.ls), a.now >= 0]

    excursion = a.excursion                                  # shield.py:264-269

    # shield.py:275-283  REINSTATE: an authenticated operator action.  Clears
    # the mode and BOTH counters, and resyncs the watermark -- omitting the
    # resync leaves a stale frozen watermark, so the next honest sample is
    # judged an excursion again and the operator's action achieves nothing.
    mode_r = If(a.reinstate, NORMAL, a.mode)
    vet_r = If(a.reinstate, 0, a.vetoes)
    exc_r = If(a.reinstate, 0, a.excursions)
    seen_r = And(a.seen, Not(a.reinstate))
    ls_r = a.ls                     # meaningless when seen_r is False

    # shield.py:284-285  the excursion is counted APART from model behaviour
    exc_1 = If(And(excursion, Not(a.reinstate), exc_r < EXCURSION_LIMIT),
               exc_r + 1, exc_r)

    # shield.py:288-289  an implausible timestamp never advances the watermark
    advance = And(Not(excursion), Or(Not(seen_r), a.now > ls_r))
    cs.append(b.seen == If(advance, True, seen_r))
    cs.append(b.ls == If(advance, a.now, ls_r))

    # shield.py:293  the corroboration run, advanced in commit so that decide
    # stays a pure function of (state, inputs)
    cs.append(b.diff_run == If(a.diff_ok, a.diff_run + 1, 0))

    # shield.py:295-296  if reclose_auth: st.latched = False
    latched_a = If(a.reclose, False, a.latched)

    # shield.py:297-305  append the grant, then drop the oldest past MAX_GRANTS
    n_after = If(a.n_gt < MAX_GRANTS, a.n_gt + 1, MAX_GRANTS)
    gt0_after = If(a.n_gt == 0, a.now, If(a.n_gt == 1, a.gt0, a.gt1))
    gt1_after = If(a.n_gt == 0, NEG_INF, a.now)
    cs.append(b.n_gt == If(a.grant, n_after, a.n_gt))
    cs.append(b.gt0 == If(a.grant, gt0_after, a.gt0))
    cs.append(b.gt1 == If(a.grant, gt1_after, a.gt1))
    cs.append(b.latched == If(a.grant, True, latched_a))

    # shield.py:305-308  vetoes: MODEL misbehaviour only.  A clock excursion
    # no longer touches this counter -- that is the v4 split.
    vet_2 = If(a.grant, 0,
               If(a.want, If(vet_r < VETO_LIMIT, vet_r + 1, vet_r), vet_r))
    cs.append(b.vetoes == vet_2)
    cs.append(b.excursions == exc_1)

    # shield.py:309-313  disowning.  EITHER counter alone reaches BASELINE_ONLY;
    # only the MODEL's counter can produce RESTRICTED.
    cs.append(b.mode == If(Or(vet_2 >= VETO_LIMIT, exc_1 >= EXCURSION_LIMIT),
                           BASELINE_ONLY,
                           If(vet_2 >= VETO_LIMIT // 2,
                              If(mode_r == NORMAL, RESTRICTED, mode_r),
                              mode_r)))

    # ghost shift registers
    cs.append(b.g1 == If(a.grant, a.now, a.g1))
    cs.append(b.g2 == If(a.grant, a.g1, a.g2))
    cs.append(b.g3 == If(a.grant, a.g2, a.g3))
    cs.append(b.g4 == If(a.grant, a.g3, a.g4))
    cs.append(b.ng == If(a.grant, a.ng + 1, a.ng))
    cs.append(b.dprev1 == a.diff_ok)
    cs.append(b.dprev2 == a.dprev1)
    cs.append(b.dprev3 == a.dprev2)
    cs.append(b.vmax == If(a.reinstate, vet_2, If(vet_2 > a.vmax, vet_2,
                                                 a.vmax)))
    return And(*cs)


# --- the invariants --------------------------------------------------------

def W(s):
    """Well-formedness: the SPARK subtypes plus ghost/state coherence.
    Proved inductive, never assumed."""
    return And(
        s.mode >= NORMAL, s.mode <= BASELINE_ONLY,              # Mode_T
        s.vetoes >= 0, s.vetoes <= VETO_LIMIT,                  # Veto_Count
        s.excursions >= 0, s.excursions <= EXCURSION_LIMIT,     # Excursion_Count
        s.diff_run >= 0,                                        # Dwell_Count
        s.n_gt >= 0, s.n_gt <= MAX_GRANTS,
        s.ng >= 0,
        s.n_gt == If(s.ng < MAX_GRANTS, s.ng, MAX_GRANTS),
        Implies(s.ng == 0, And(s.g1 == NEG_INF, s.gt0 == NEG_INF,
                               s.gt1 == NEG_INF)),
        Implies(s.ng == 1, And(s.gt0 == s.g1, s.gt1 == NEG_INF)),
        Implies(s.ng >= 2, And(s.gt0 == s.g2, s.gt1 == s.g1)),
        # NOTE: v1-v3 carried `ng >= 1 => ls >= g1` here ("the watermark
        # dominates every grant").  v4 CANNOT: `reinstate` deliberately
        # resyncs the clock, so the watermark legitimately drops below an
        # earlier grant's timestamp.  I2 does not need it -- the sliding
        # window is anchored on grant_times[0], not on the watermark -- and
        # dropping it is what keeps I2 provable across a reinstate.
        # either counter at its limit means the model is disowned
        Implies(Or(s.vetoes >= VETO_LIMIT, s.excursions >= EXCURSION_LIMIT),
                s.mode == BASELINE_ONLY),
        # v4 dwell coherence: the run counter is backed by the ghost history
        Implies(s.diff_run >= 1, s.dprev1),
        Implies(s.diff_run >= 2, s.dprev2),
        Implies(s.diff_run >= 3, s.dprev3),
        s.vmax >= s.vetoes, s.vmax >= 0, s.vmax <= VETO_LIMIT,
        # RESTRICTED is reachable only from MODEL misbehaviour (S4)
        Implies(s.mode == RESTRICTED, s.vmax >= VETO_LIMIT // 2),
    )


def I1(s):      # no trip without physics
    return Implies(s.grant, And(s.diff_ok, s.forward, s.remote_ok, s.time_ok))


def I1_local(s):
    """v5.  BOTH addends of the differential were authenticated and fresh.

    Stated as the delta over I1 rather than as a restatement of it: I1 already
    gives `remote_ok`, so this adds `local_ok` and the two compose to
    I1_both.  Keeping them separate is deliberate -- it makes the proof
    obligation that the v5 change introduced visible on its own line, instead
    of silently widening an existing theorem."""
    return Implies(s.grant, s.local_ok)


def I1_both(s):
    """I1 and I1_local composed: a grant implies every term the shield reasons
    about came from an authenticated, fresh channel.  This is assumption A8
    (Linux-plane half) turned into a theorem."""
    return Implies(s.grant, And(s.remote_ok, s.local_ok))


def I2(s):      # rate limit, insertion-order form
    return Implies(s.ng >= MAX_GRANTS + 1, s.g1 - s.g3 >= WINDOW_MS)


def I2_span4(s):
    """I2 with NO assumption about the ORDER of timestamps: among the four
    most recent grants, no three may share a WINDOW_MS window.  This is the
    form that caught the v1 defect (the violating triple was not the most
    recent three), and it is the form used under the free clock."""
    g = [s.g1, s.g2, s.g3, s.g4]
    bad = []
    for a_ in range(4):
        for b_ in range(a_ + 1, 4):
            for c_ in range(b_ + 1, 4):
                t = [g[a_], g[b_], g[c_]]
                hi = zmax(zmax(t[0], t[1]), t[2])
                lo = If(t[0] < t[1], If(t[0] < t[2], t[0], t[2]),
                        If(t[1] < t[2], t[1], t[2]))
                bad.append(hi - lo < WINDOW_MS)
    return Implies(s.ng >= MAX_GRANTS + 2, Not(Or(*bad)))


def I2_strong(s):
    return And(I2(s), W(s))


def I2_span4_strong(s):
    return And(I2_span4(s), I2(s), W(s))


def I3(s):      # latch: no grant while awaiting reclose authorisation
    return Implies(s.latched, Not(s.grant))


def I4(s):      # time integrity
    return Implies(s.grant, s.time_ok)


def I4b(s):
    """v2: no grant on a backwards clock step.  v3: no grant on ANY
    implausible timestamp, in either direction."""
    return Implies(s.grant, Not(s.excursion))


def P1(s):
    """v3 WATERMARK INTEGRITY, single-state half: a grant can only happen on a
    timestamp inside the plausibility window of the current watermark."""
    return Implies(s.grant,
                   Or(Not(s.seen),
                      And(s.now >= s.ls, s.now - s.ls <= MAX_CLOCK_STEP)))


def P4(s):
    """v3 SERVICE GUARANTEE (the definitional half of DoS-freedom): a sample
    whose timestamp is plausible relative to the watermark is never vetoed for
    any time-integrity reason."""
    return Implies(And(s.seen, s.now >= s.ls,
                       s.now - s.ls <= MAX_CLOCK_STEP),
                   Not(s.excursion))


def P6(s):
    """v3 CLOCK-ADVANCE BOUND: the timestamp of any granted trip is at most
    MAX_CLOCK_STEP_MS beyond the watermark.  Together with P2 (the watermark
    only ever takes the value of a sample that PASSED the plausibility test)
    this is what stops a hostile clock from inflating the rate-limiter's sense
    of elapsed time and thereby refilling the grant budget early."""
    return Implies(And(s.grant, s.seen), s.now <= s.ls + MAX_CLOCK_STEP)


def I5(s):
    """Certified region.  Adaptive sensitivity requires BOTH the certificate
    and full trust; anything else is gated by the nominal thresholds.  Stated
    at Shield.step level, which is where `effective_cert` is computed."""
    return Implies(And(s.grant, Not(And(s.cert, s.mode == NORMAL))),
                   s.i_diff > zmax(P0_NOM, K_NOM * If(s.i_restraint < 0, 0,
                                                      s.i_restraint)))


def I5b(s):
    """The unconditional half: every grant clears the hard floor, whatever
    the mode and whatever the certificate says."""
    return Implies(s.grant,
                   s.i_diff > zmax(P0_MIN, K_MIN * If(s.i_restraint < 0, 0,
                                                      s.i_restraint)))


def I6(s):      # baseline pass-through is never inhibited
    return Implies(s.baseline, s.trip_out)


def I8(s):      # NEW in v2: a non-finite measurement can never yield a grant
    return Implies(s.grant, And(s.fin_diff, s.fin_restraint))


def TRANSPARENCY(s):
    """Liveness-as-safety, RESTATED FOR v4.  The old form said "corroboration
    now => grant now".  That is no longer the property: v4 requires the
    corroboration to have been SUSTAINED for DWELL_MS consecutive samples, so
    the honest statement adds `dwell_met` as an explicit precondition rather
    than quietly weakening the conclusion.  The multi-step form -- that
    DWELL_MS consecutive good samples DO produce a grant, so the dwell is a
    delay and not a veto -- is TRANSPARENCY_SUSTAINED below, which is proved
    by unrolling exactly DWELL_MS steps."""
    budget = Or(s.n_gt < MAX_GRANTS, s.now - s.gt0 >= WINDOW_MS)
    return Implies(And(s.want, s.mode == NORMAL, Not(s.latched), budget,
                       Not(s.excursion),
                       s.time_ok, s.remote_ok, s.local_ok, s.forward,
                       s.diff_ok,
                       s.diff_run + 1 >= DWELL_MS),
                   s.grant)


# --- v4: the dwell requirement ---------------------------------------------

def DWELL(s):
    """A grant implies the physics was corroborated on DWELL_MS CONSECUTIVE
    samples: this one and the DWELL_MS-1 before it.  No isolated single-sample
    excursion can ever produce a grant.

    Stated over the ghost history (dprev1..3), so it is a single-state
    property and closes at k = 1.  The ghost-free form -- which is the same
    claim without trusting the ghosts -- is checked separately by unrolling
    DWELL_MS steps in prove_dwell()."""
    hist = [s.dprev1, s.dprev2, s.dprev3][:max(0, DWELL_MS - 1)]
    return Implies(s.grant, And(s.diff_ok, *hist)) if hist else \
        Implies(s.grant, s.diff_ok)


def DWELL_floor(s):
    """The dwell composes with the numeric layer: every one of the DWELL_MS
    corroborated samples cleared the hard floor, not merely the last."""
    return Implies(s.grant,
                   And(s.diff_ok,
                       s.i_diff > zmax(P0_MIN,
                                       K_MIN * If(s.i_restraint < 0, 0,
                                                  s.i_restraint)),
                       s.diff_run + 1 >= DWELL_MS))


# --- v4: the split counters ------------------------------------------------

def S1(s):
    """A clock excursion never touches the MODEL's veto counter.  This is the
    invariant that stops a merging-unit fault being laundered into a verdict
    about the AI."""
    return BoolVal(True)      # 2-state; see prove_split_counters()


def S4(s):
    """RESTRICTED is reachable only from MODEL misbehaviour.  Excursions alone
    can never withdraw the AI's adaptive sensitivity (I5, I7f/band).

    Stated over `vmax`, the high-water mark of the MODEL's veto counter since
    the last reinstate.  The naive form `mode = RESTRICTED => vetoes >=
    VETO_LIMIT/2` is FALSE, and instructively so: a grant clears `vetoes` to 0
    while I7a keeps the mode at RESTRICTED."""
    return Implies(s.mode == RESTRICTED, s.vmax >= VETO_LIMIT // 2)


def S5(s):
    """Either counter alone at its limit disowns the model."""
    return Implies(Or(s.vetoes >= VETO_LIMIT,
                      s.excursions >= EXCURSION_LIMIT),
                   s.mode == BASELINE_ONLY)


# --- BMC and k-induction engines ------------------------------------------

def bmc(prop, depth, clock="free"):
    """Look for a counterexample within `depth` transitions from init."""
    steps = [Step(i) for i in range(depth + 1)]
    s = Solver()
    s.add(init(steps[0]))
    t0 = time.perf_counter()
    for i in range(depth + 1):
        s.push()
        s.add(Not(prop(steps[i])))
        if s.check() == sat:
            m = s.model()
            ce = {str(d): str(m[d]) for d in m.decls()}
            s.pop()
            return ({"depth": i, "model": ce},
                    round((time.perf_counter() - t0) * 1000, 2))
        s.pop()
        if i < depth:
            s.add(trans(steps[i], steps[i + 1], clock))
    return None, round((time.perf_counter() - t0) * 1000, 2)


def k_induction(prop, k, clock="free", simple_path=False):
    """base: init and the first k states satisfy prop.
       step: prop at k consecutive states + transitions => prop at the next."""
    t0 = time.perf_counter()
    b = [Step(i) for i in range(k)]
    sb = Solver()
    sb.add(init(b[0]))
    for i in range(k - 1):
        sb.add(trans(b[i], b[i + 1], clock))
    sb.add(Or(*[Not(prop(b[i])) for i in range(k)]))
    base_ok = sb.check() == unsat
    base_ce = None
    if not base_ok:
        m = sb.model()
        base_ce = {str(d): str(m[d]) for d in m.decls()}

    st = [Step(100 + i) for i in range(k + 1)]
    ss = Solver()
    for i in range(k):
        ss.add(trans(st[i], st[i + 1], clock))
        ss.add(prop(st[i]))
    if simple_path and k > 1:
        for i in range(k + 1):
            for j in range(i + 1, k + 1):
                ss.add(Or(*[a != bb for a, bb in
                            zip(st[i].state_vars(), st[j].state_vars())]))
    ss.add(Not(prop(st[k])))
    step_ok = ss.check() == unsat
    return base_ok, step_ok, base_ce, round((time.perf_counter() - t0) * 1000,
                                            2)


def prove_by_kinduction(name, prop, kmax=8, bmc_depth=12, clock="free",
                        note=""):
    ce, bmc_ms = bmc(prop, bmc_depth, clock)
    rec = {"name": name, "bmc_depth": bmc_depth, "bmc_ms": bmc_ms,
           "note": note, "clock": clock, "counterexample": None, "k": None,
           "verdict": None, "kind_ms": 0.0}
    if ce is not None:
        rec["counterexample"] = ce
        rec["verdict"] = "DISPROVED"
        return rec
    for k in range(1, kmax + 1):
        base_ok, step_ok, base_ce, ms = k_induction(prop, k, clock)
        rec["kind_ms"] = round(rec["kind_ms"] + ms, 2)
        if not base_ok:
            rec["counterexample"] = {"depth": "<%d (base case)" % k,
                                     "model": base_ce}
            rec["verdict"] = "DISPROVED"
            return rec
        if step_ok:
            rec["k"] = k
            rec["verdict"] = "PROVED"
            return rec
        base_ok, step_ok, _, ms2 = k_induction(prop, k, clock,
                                               simple_path=True)
        rec["kind_ms"] = round(rec["kind_ms"] + ms2, 2)
        if step_ok:
            rec["k"] = k
            rec["verdict"] = "PROVED"
            rec["simple_path"] = True
            return rec
    rec["verdict"] = "BOUNDED-ONLY"
    return rec


def prove_disowning():
    """I7, the two-state properties.  Checked over an ARBITRARY well-formed
    pre-state, which is strictly stronger than over reachable pre-states.

    RESTATED FOR v4.  Monotonicity and absorption now hold *absent a
    reinstate*.  That is the whole point of the authenticated operator
    channel, and saying "mode is monotone" without the qualifier would be
    false, so every clause below carries it explicitly.
    """
    a, b = Step(0), Step(1)
    out = []
    out.append(_check(
        "I7a mode is monotone non-decreasing ABSENT a reinstate",
        And(W(a), trans(a, b), Not(a.reinstate), b.mode < a.mode),
        "forall s,s' . W(s) and trans(s,s') and not reinstate "
        "=> s'.mode >= s.mode"))
    out.append(_check(
        "I7b BASELINE_ONLY is absorbing ABSENT a reinstate",
        And(W(a), trans(a, b), Not(a.reinstate), a.mode == BASELINE_ONLY,
            b.mode != BASELINE_ONLY),
        "BASELINE_ONLY is a sink of the mode lattice unless an authenticated "
        "operator reinstates"))
    out.append(_check("I7c in BASELINE_ONLY no grant is ever possible",
                      And(W(a), a.mode == BASELINE_ONLY, a.grant),
                      "forall s . s.mode = BASELINE_ONLY => not grant(s)"))
    out.append(_check(
        "I7d under disownment a request cannot lower the veto count",
        And(W(a), trans(a, b), Not(a.reinstate), a.mode == BASELINE_ONLY,
            a.want, a.vetoes < VETO_LIMIT, b.vetoes <= a.vetoes),
        "sustained requests under disownment cannot lower the veto count"))
    out.append(_check(
        "I7e the veto counter is cleared only by a grant or a reinstate",
        And(W(a), trans(a, b), b.vetoes < a.vetoes, Not(a.grant),
            Not(a.reinstate)),
        "forall s,s' . trans(s,s') and not grant(s) and not reinstate "
        "=> s'.vetoes >= s.vetoes"))
    out.append(_check(
        "I7g a clock excursion alone advances the EXCURSION counter (v4)",
        And(W(a), trans(a, b), a.excursion, Not(a.reinstate),
            a.excursions < EXCURSION_LIMIT, b.excursions <= a.excursions),
        "a clock excursion in either direction advances disowning on its own, "
        "via the SEPARATE excursion counter"))
    return out


def prove_watermark(max_burst=6):
    """v3.  The theorems the plausibility-window patch exists to establish.

    The defect this replaces (D3, see docs/PROOF.md) was one I raised against
    v2 myself: the watermark was ONE-SIDED.  It rejected backwards timestamps
    but accepted arbitrarily large forward ones, so a single sample dated far
    in the future poisoned `last_seen_ms` and vetoed every honest sample after
    it until real time caught up.  v2 traded an integrity defect for an
    availability one.

    The fix is that an implausible timestamp does not move the watermark AT
    ALL.  That is P2a below, and everything else follows from it.
    """
    out = []
    a, b = Step(0), Step(1)

    # P2a -- THE theorem.  An implausible timestamp never advances the
    # watermark.  This is the whole patch, in one verification condition.
    out.append(_check(
        "P2a watermark integrity: an excursion never moves the watermark",
        And(W(a), trans(a, b), a.excursion, Not(a.reinstate),
            Or(b.ls != a.ls, b.seen != a.seen)),
        "forall s,s' . trans(s,s') and excursion(s) and not reinstate => "
        "the watermark is unchanged.  The `not reinstate` is new in v4 and is "
        "the point of the split: the AUTHENTICATED OPERATOR may resync the "
        "clock, the attacker may not."))

    # P2b -- the watermark is monotone and only ever takes a PRESENTED value.
    out.append(_check(
        "P2b watermark is monotone and only takes a presented timestamp",
        And(W(a), trans(a, b), a.seen, Not(a.reinstate),
            Or(b.ls < a.ls, And(b.ls != a.ls, b.ls != a.now))),
        "forall s,s' . trans(s,s') and s.seen => "
        "s'.last_seen_ms >= s.last_seen_ms and "
        "s'.last_seen_ms in {s.last_seen_ms, now_ms}"))

    # P2c -- the watermark only ever takes a value that PASSED the test.
    # This is what makes the watermark an honest clock rather than an
    # attacker-controlled one, and it is the premise of P6.
    out.append(_check(
        "P2c the watermark only ever takes an ACCEPTED timestamp",
        And(W(a), trans(a, b), Not(a.reinstate), b.ls != a.ls,
            Or(a.excursion, b.ls != a.now)),
        "forall s,s' . trans(s,s') and the watermark moved => "
        "not excursion(s) and s'.last_seen_ms = now_ms"))

    # P3 -- a BURST of spoofed timestamps leaves the watermark untouched.
    # P2a is the induction step, so the unbounded statement follows by
    # induction on the burst length; the finite checks below are a sanity
    # check on that reasoning, not a substitute for it.
    burst = []
    for n in range(1, max_burst + 1):
        st = [Step(500 + 10 * n + i) for i in range(n + 1)]
        sv = Solver()
        sv.add(W(st[0]))
        for i in range(n):
            sv.add(trans(st[i], st[i + 1]))
            sv.add(st[i].excursion, Not(st[i].reinstate))   # spoofed
        sv.add(st[n].ls != st[0].ls)
        t0 = time.perf_counter()
        ok = sv.check() == unsat
        burst.append({"n": n, "ok": ok,
                      "ms": round((time.perf_counter() - t0) * 1000, 2)})
    out.append({
        "name": "P3 a burst of N spoofed timestamps leaves the watermark fixed",
        "statement": "forall N, forall traces of N consecutive excursions . "
                     "last_seen_ms is unchanged.  Unbounded N follows from "
                     "P2a by induction; N = 1..%d checked directly." % max_burst,
        "proved": all(x["ok"] for x in burst),
        "ms": round(sum(x["ms"] for x in burst), 2),
        "per_n": burst, "counterexample": None,
    })

    # P5 -- the composite service guarantee, which is what a reviewer actually
    # cares about: spoofed samples cannot deny service to the honest ones that
    # follow.  RESTATED FOR v4: the honest tail must now be DWELL_MS
    # consecutive corroborated samples, not one, because that is what the
    # shield requires.  Checked directly for bursts up to max_burst.
    comp = []
    for n in range(1, max_burst + 1):
        st = [Step(700 + 40 * n + i) for i in range(n + DWELL_MS + 2)]
        sv = Solver()
        sv.add(init(st[0]))
        for i in range(len(st) - 1):
            sv.add(trans(st[i], st[i + 1]))
        # step 0 is an honest sample establishing the watermark;
        # steps 1..n are spoofed timestamps with NO trip requested;
        # steps n+1 .. n+DWELL_MS are honest, in-window, fully corroborated.
        sv.add(Not(st[0].want), Not(st[0].reinstate))
        for i in range(1, n + 1):
            sv.add(st[i].excursion, Not(st[i].want), Not(st[i].reclose),
                   Not(st[i].reinstate))
        for j in range(n + 1, n + 1 + DWELL_MS):
            h = st[j]
            sv.add(h.want, h.time_ok, h.remote_ok, h.local_ok, h.forward,
                   h.diff_ok,
                   h.seen, h.now >= h.ls, h.now - h.ls <= MAX_CLOCK_STEP,
                   Not(h.reinstate), Not(h.reclose))
        # Service is denied iff NONE of the honest run is granted.  (Asking
        # specifically for the LAST one would be wrong: if the run started
        # with dwell credit already banked, the grant lands earlier and the
        # latch then correctly vetoes the rest.)
        sv.add(And(*[Not(st[j].grant)
                     for j in range(n + 1, n + 1 + DWELL_MS)]))
        t0 = time.perf_counter()
        ok = sv.check() == unsat
        comp.append({"n": n, "ok": ok,
                     "ms": round((time.perf_counter() - t0) * 1000, 2)})
    out.append({
        "name": "P5 spoof burst cannot deny service to the honest RUN after",
        "statement": "for N = 1..%d spoofed timestamps, the following run of "
                     "%d consecutive in-window corroborated honest samples "
                     "contains a GRANT.  Unbounded N follows from P2a + "
                     "TRANSPARENCY_SUSTAINED; the composition of those two "
                     "lemmas is a hand argument, not a machine-checked one."
                     % (max_burst, DWELL_MS),
        "proved": all(x["ok"] for x in comp),
        "ms": round(sum(x["ms"] for x in comp), 2),
        "per_n": comp, "counterexample": None,
    })

    # P7 -- OBSERVATION, and the price of the D3 fix.  Because the watermark
    # is now FROZEN on an excursion, the same implausible timestamp stays
    # implausible forever, so ONE repeated constant accumulates the whole
    # disowning budget.  In v2 a forward jump moved the watermark, so the
    # attacker needed a fresh timestamp each time; v3 made the disownment
    # surface strictly cheaper while closing the availability defect.  This is
    # a design trade, not a soundness bug -- see docs/PROOF.md section 8.4.
    n = EXCURSION_LIMIT + 1
    st = [Step(900 + i) for i in range(n + 1)]
    sv = Solver()
    sv.add(init(st[0]))
    for i in range(n):
        sv.add(trans(st[i], st[i + 1]))
        sv.add(Not(st[i].want), Not(st[i].reinstate))   # no trip, no operator
        if i > 0:
            sv.add(st[i].excursion)      # every later sample is an excursion
    t0 = time.perf_counter()
    sv.push()
    sv.add(st[n].mode != BASELINE_ONLY)
    forced = sv.check() == unsat
    sv.pop()
    sv.push()
    sv.add(*[st[i].now == st[1].now for i in range(2, n)])   # one constant
    sv.add(st[n].vetoes == 0)     # and the MODEL's counter is untouched
    one_value = sv.check() == sat
    sv.pop()
    out.append({
        "name": "P7 %d excursions still disown, but via the SEPARATE counter"
                % EXCURSION_LIMIT,
        "statement": "%d clock excursions and zero trip requests still FORCE "
                     "mode = BASELINE_ONLY (unavoidable), and one repeated "
                     "implausible timestamp suffices because the watermark is "
                     "frozen on excursion.  v4 changes WHERE this lands: the "
                     "excursion counter, not the model's veto counter, so a "
                     "blameless model is no longer accused and RESTRICTED is "
                     "never reached this way (S4).  Recovery is now possible "
                     "via an authenticated reinstate (S6)."
                     % EXCURSION_LIMIT,
        "proved": forced,
        "one_repeated_timestamp_suffices": one_value,
        "ms": round((time.perf_counter() - t0) * 1000, 2),
        "counterexample": None,
    })
    return out


def prove_dwell():
    """v4.  The dwell requirement, proved WITHOUT the ghosts.

    `DWELL` in the invariant table is a single-state property stated over the
    ghost history, so it closes at k = 1.  The theorems here re-derive the
    same claim by unrolling the transition relation DWELL_MS steps and never
    mentioning a ghost.  That unrolling is EXACT, not a bounded approximation:
    the property's entire lookback is DWELL_MS samples, so a trace of that
    length is the whole of it.
    """
    out = []
    n = DWELL_MS
    st = [Step(1100 + i) for i in range(n + 1)]
    base = [init(st[0])] if False else []
    tr = [trans(st[i], st[i + 1]) for i in range(n)]

    # DW1 -- a grant implies DWELL_MS consecutive corroborated samples.
    out.append(_check(
        "DW1 grant implies %d CONSECUTIVE corroborated samples (ghost-free)"
        % DWELL_MS,
        And(W(st[0]), *tr, st[n - 1].grant,
            Or(*[Not(st[i].diff_ok) for i in range(n)])),
        "forall traces of %d steps . grant at the last => diff_ok at every "
        "one of them.  Unrolled to exactly the property's lookback, so this "
        "is a proof, not a bound." % DWELL_MS))

    # DW2 -- no isolated single-sample excursion can ever produce a grant.
    out.append(_check(
        "DW2 an isolated single-sample spike can never produce a grant",
        And(W(st[0]), *tr, Not(st[n - 2].diff_ok), st[n - 1].diff_ok,
            st[n - 1].grant),
        "forall traces . corroboration false at the previous sample and true "
        "at this one => no grant.  This is the noise-crossing case, and it is "
        "ALL that dwell closes -- see assumption A8 in docs/PROOF.md."))

    # DW3 -- every one of the sustained samples cleared the hard floor, not
    # merely the last.  The dwell composes with the numeric layer.
    floor = lambda x: x.i_diff > zmax(P0_MIN,
                                      K_MIN * If(x.i_restraint < 0, 0,
                                                 x.i_restraint))
    out.append(_check(
        "DW3 every sample of the run cleared the hard floor, not just the last",
        And(W(st[0]), *tr, st[n - 1].grant,
            Or(*[Not(floor(st[i])) for i in range(n)])),
        "forall traces . grant => i_diff > max(P0_MIN, K_MIN*i_restraint) at "
        "each of the %d samples" % DWELL_MS))

    # DW4 / TRANSPARENCY_SUSTAINED -- the dwell is a DELAY, not a veto.
    sv = Solver()
    tr2 = [trans(st[i], st[i + 1]) for i in range(n)]
    sv.add(W(st[0]), st[0].mode == NORMAL, Not(st[0].latched),
           st[0].n_gt == 0, st[0].diff_run == 0, Not(st[0].seen),
           st[0].vetoes == 0, st[0].excursions == 0, st[0].ng == 0)
    for i in range(n):
        sv.add(tr2[i]) if i < n else None
        sv.add(st[i].want, st[i].time_ok, st[i].remote_ok, st[i].local_ok,
               st[i].forward,
               st[i].diff_ok, Not(st[i].reinstate), Not(st[i].reclose),
               Not(st[i].excursion))
    sv.add(And(*[Not(st[i].grant) for i in range(n)]))
    t0 = time.perf_counter()
    ok = sv.check() == unsat
    out.append({
        "name": "DW4 TRANSPARENCY_SUSTAINED: %d good samples DO produce a grant"
                % DWELL_MS,
        "statement": "from a clean state, %d consecutive fully-corroborated "
                     "in-window proposals contain a GRANT.  This is what "
                     "makes the dwell a DELAY of ~%d ms rather than a veto, "
                     "and it is the half of TRANSPARENCY that the v4 change "
                     "would otherwise have quietly removed."
                     % (DWELL_MS, DWELL_MS),
        "proved": ok, "ms": round((time.perf_counter() - t0) * 1000, 2),
        "counterexample": None,
    })
    # DW5 -- THE LIMIT OF DWELL, and the most important line in this function.
    # UNCHANGED by v5, but its SCOPE is now stated precisely.
    #
    # Note `fs[i].local_ok` below.  v5 authenticates the local addend, which
    # blocks any adversary who cannot sign as the local merging unit.  It does
    # NOT block an adversary who HOLDS that merging unit's key: their samples
    # verify, so local_ok is true for them by construction, and that single
    # assertion is the whole of what distinguishes the two threat models.
    #
    # Against that adversary, dwell still removes the NOISE-CROSSING case only.
    # They control one addend of i_diff = |I_local + I_remote| and therefore
    # the sum, so they hold the differential STEADILY above the floor rather
    # than crossing it on noise.  A steady forgery satisfies any dwell length,
    # so NO value of DWELL_MS closes this.  Demonstrated rather than asserted:
    # a run of length DWELL_MS + 4 that grants, uniform in the length.
    m = DWELL_MS + 4
    fs = [Step(1500 + i) for i in range(m + 1)]
    forged = Solver()
    forged.add(init(fs[0]))
    for i in range(m):
        forged.add(trans(fs[i], fs[i + 1]))
        # a STEADY forged differential: the same value every sample, parked
        # just above the most sensitive threshold the shield will ever allow
        forged.add(fs[i].i_diff == fs[0].i_diff, fs[i].fin_diff,
                   fs[i].i_restraint == 0, fs[i].fin_restraint,
                   fs[i].fin_p0, fs[i].fin_k,
                   fs[i].want, fs[i].time_ok, fs[i].remote_ok,
                   # THE DEFINING CAPABILITY of the MU-key adversary: their
                   # forgeries carry a valid local signature.
                   fs[i].local_ok,
                   fs[i].forward,
                   fs[i].cert, Not(fs[i].reinstate),
                   fs[i].now == i)              # a perfectly honest clock
    forged.add(fs[0].i_diff > P0_MIN, fs[0].i_diff < P0_MIN + 0.02)
    forged.add(Or(*[fs[i].grant for i in range(m)]))
    t0 = time.perf_counter()
    got = forged.check() == sat
    val = None
    if got:
        v = forged.model().eval(fs[0].i_diff)
        val = round(float(v.as_fraction()), 6) if hasattr(v, "as_fraction") \
            else str(v)
    out.append({
        "name": "DW5 LIMIT: a STEADY forgery defeats any dwell (MU-KEY adv.)",
        "statement": "a constant i_diff parked just above P0_MIN, held for "
                     "%d consecutive samples on an honest clock BY AN "
                     "ADVERSARY WHOSE LOCAL SIGNATURES VERIFY, obtains a "
                     "GRANT.  Dwell removes only the noise-crossing case and "
                     "no dwell length closes this.  v5 does NOT change this "
                     "result -- it changes its SCOPE: assumption A8-MU "
                     "(the adversary does not hold the local merging unit's "
                     "signing key) remains an ASSUMPTION and is the residual "
                     "risk.  See docs/PROOF.md sections 2 and 8.7." % m,
        "proved": got,            # `sat` IS the expected outcome here
        "is_negative_result": True,
        "forged_i_diff_pu": val,
        "ms": round((time.perf_counter() - t0) * 1000, 2),
        "counterexample": None,
    })
    # A8L -- THE v5 DISCHARGE.  An adversary who owns the inference plane but
    # holds NO merging-unit key cannot produce an authenticated local sample.
    # Give them everything else: arbitrary i_diff and i_restraint at every
    # step, arbitrary req_p0/req_k, a perfect clock, perfect remote
    # provenance, perfect direction and time quality, a trip request every
    # millisecond -- and no number of steps yields a single grant.
    ln = DWELL_MS + 6
    ls_ = [Step(1700 + i) for i in range(ln + 1)]
    lin = Solver()
    lin.add(init(ls_[0]))
    for i in range(ln):
        lin.add(trans(ls_[i], ls_[i + 1]))
        lin.add(Not(ls_[i].local_ok),          # the ONE thing they lack
                ls_[i].want, ls_[i].time_ok, ls_[i].remote_ok,
                ls_[i].forward, ls_[i].cert, ls_[i].fin_diff,
                ls_[i].fin_restraint, ls_[i].fin_p0, ls_[i].fin_k,
                Not(ls_[i].reinstate), ls_[i].now == i)
    lin.add(Or(*[ls_[i].grant for i in range(ln)]))
    t0 = time.perf_counter()
    blocked = lin.check() == unsat
    out.append({
        "name": "A8L DISCHARGED: the Linux-plane adversary obtains no grant",
        "statement": "an adversary owning the inference plane but holding no "
                     "merging-unit key -- free to choose i_diff, i_restraint "
                     "and both requested settings at every one of %d steps, "
                     "with a perfect clock and perfect remote provenance -- "
                     "obtains ZERO grants.  This is the Linux-plane half of "
                     "assumption A8, now a THEOREM rather than an "
                     "assumption.  It says nothing about the MU-key "
                     "adversary; that is DW5." % ln,
        "proved": blocked,
        "ms": round((time.perf_counter() - t0) * 1000, 2),
        "counterexample": None,
    })
    return out


def prove_split_counters():
    """v4.  The two counters are independent, and the operator channel works.

    This is the group that exists because of the dissent in the v3 report:
    one counter for two unrelated failure modes meant a merging-unit or PTP
    fault disowned a blameless model, and -- worse -- silently withdrew its
    adaptive sensitivity by way of RESTRICTED.
    """
    a, b = Step(0), Step(1)
    out = []

    out.append(_check(
        "S1 a clock excursion never touches the MODEL's veto counter",
        And(W(a), trans(a, b), Not(a.want), Not(a.reinstate),
            b.vetoes != a.vetoes),
        "forall s,s' . trans(s,s') and no trip requested and no reinstate "
        "=> s'.vetoes = s.vetoes, whatever the clock did"))

    out.append(_check(
        "S2 model misbehaviour never touches the EXCURSION counter",
        And(W(a), trans(a, b), Not(a.excursion), Not(a.reinstate),
            b.excursions != a.excursions),
        "forall s,s' . trans(s,s') and no clock excursion and no reinstate "
        "=> s'.excursions = s.excursions, whatever the model proposed"))

    out.append(_check(
        "S3 a grant clears vetoes and leaves excursions untouched",
        And(W(a), trans(a, b), a.grant, Not(a.reinstate),
            Or(b.vetoes != 0, b.excursions != a.excursions)),
        "neither counter can be cleared by the other's clearing event"))

    # S4 -- stated over a ghost high-water mark of the MODEL's veto counter,
    # because the plain two-state form is FALSE and instructively so: a grant
    # clears `vetoes` to 0 while I7a keeps the mode at RESTRICTED, so a state
    # with mode = RESTRICTED and vetoes = 0 is perfectly reachable.  What is
    # true, and what the split was made to guarantee, is that the mode got
    # there because of the MODEL.
    out.append(prove_by_kinduction(
        "S4 RESTRICTED is reachable only from MODEL misbehaviour",
        S4, 8, 12,
        note="mode = RESTRICTED => vetoes reached VETO_LIMIT/2 at some point; "
             "excursions alone can NEVER withdraw adaptive sensitivity"))

    # S4b -- the concrete version: a run of nothing but clock excursions, with
    # no trip ever proposed, never passes through RESTRICTED.
    n = EXCURSION_LIMIT + 1
    st = [Step(1300 + i) for i in range(n + 1)]
    sv = Solver()
    sv.add(init(st[0]))
    for i in range(n):
        sv.add(trans(st[i], st[i + 1]))
        sv.add(Not(st[i].want), Not(st[i].reinstate))
        if i > 0:
            sv.add(st[i].excursion)
    sv.add(Or(*[st[i].mode == RESTRICTED for i in range(n + 1)]))
    t0 = time.perf_counter()
    out.append({
        "name": "S4b an excursions-only run never passes through RESTRICTED",
        "statement": "%d clock excursions with no trip ever proposed: the mode "
                     "goes NORMAL -> BASELINE_ONLY and never visits "
                     "RESTRICTED, so a merging-unit fault cannot silently "
                     "withdraw the model's adaptive sensitivity"
                     % EXCURSION_LIMIT,
        "proved": sv.check() == unsat,
        "ms": round((time.perf_counter() - t0) * 1000, 2),
        "counterexample": None,
    })

    out.append(_check(
        "S5 either counter alone at its limit disowns the model",
        And(W(a), trans(a, b),
            Or(b.vetoes >= VETO_LIMIT, b.excursions >= EXCURSION_LIMIT),
            b.mode != BASELINE_ONLY),
        "forall s' . vetoes >= VETO_LIMIT or excursions >= EXCURSION_LIMIT "
        "=> mode = BASELINE_ONLY"))

    out.append(_check(
        "S6 reinstate restores NORMAL, zeroes both counters, resyncs the clock",
        And(W(a), trans(a, b), a.reinstate,
            Or(b.mode != NORMAL, b.excursions != 0, b.vetoes > 1,
               And(b.seen, b.ls != a.now))),
        "forall s,s' . trans(s,s') and reinstate => s'.mode = NORMAL and "
        "s'.excursions = 0 and s'.vetoes <= 1 (the same step may re-count one "
        "veto if a trip was requested and refused) and the watermark is "
        "either cleared or resynced to the current sample -- never left stale"))

    out.append(_check(
        "S6b reinstate is the ONLY way out of BASELINE_ONLY",
        And(W(a), trans(a, b), a.mode == BASELINE_ONLY,
            b.mode != BASELINE_ONLY, Not(a.reinstate)),
        "permanence is preserved: nothing the model or the clock does can "
        "rearm the shield"))

    # S7 -- unreachability from the Proposal record.  This is a SYNTACTIC
    # check on the frozen source, not a Z3 theorem, and is reported as such.
    import inspect
    src_step = inspect.getsource(S.Shield.step)
    src_commit = inspect.getsource(S.commit)
    out.append({
        "name": "S7 reinstate is unreachable from Proposal (SYNTACTIC check)",
        "statement": "`reinstate` is not a field of Proposal, and Shield.step "
                     "never passes it to commit -- so the model has no path "
                     "to it.  Checked by source inspection, NOT by Z3: the "
                     "transition relation deliberately leaves `reinstate` a "
                     "free input, which is the more adversarial model.",
        "proved": ("reinstate" not in S.Proposal.__slots__
                   and "reinstate" not in src_step
                   and "reinstate" in src_commit),
        "proposal_slots": list(S.Proposal.__slots__),
        "step_mentions_reinstate": "reinstate" in src_step,
        "ms": 0.0, "counterexample": None,
    })
    # A8C -- the compatibility paths.  Reported dynamically, and probed
    # BEHAVIOURALLY rather than by grepping the source.
    #
    # This row exists because I raised the hazard in the v5 report: both
    # backward-compatibility paths substituted local_ok = True, so an
    # un-updated caller kept running, kept granting, and got no indication
    # that A8-LINUX was no longer discharged for it.  It has since been
    # closed (REQUIRE_LOCAL_PROVENANCE).
    #
    # The row must therefore say what is true TODAY, not what was true when
    # it was written.  A static "FAIL OPEN" headline over a detail line
    # reading "defaults open = False" is documentation drift inside the proof
    # suite itself -- a reader scanning verdicts sees a live hazard that no
    # longer exists, and that is exactly how a stale line becomes a false
    # finding.  So: the name, the verdict and the statement are all derived
    # from the probe, and the row reverts to a hazard the moment either path
    # goes permissive again.
    #
    # Probed by CALLING the shield, not by string-matching it: a refactor
    # that reintroduced the hazard with different wording would slip past a
    # grep, which is the failure mode this row is supposed to catch.
    def _probe_compat_paths():
        """Returns (five_tuple_grants, absent_provenance_grants)."""
        # Path 1: the legacy five-element `decide` input tuple.  diff_run is
        # primed so the dwell is already satisfied -- then the ONLY thing that
        # can stand between this call and a grant is the local guard, so
        # `True` here means fail-open and nothing else.
        st = S.State()
        st.diff_run = DWELL_MS
        five_grants, _reason = S.decide(st, 0, True,
                                        (True, True, True, True, False))

        # Path 2: a sample object carrying NO local-provenance attributes at
        # all, everything else perfect, run for DWELL_MS + 1 samples so the
        # dwell cannot be what refuses it.
        class _BareSample(object):
            __slots__ = ("t", "i_diff", "i_restraint", "remote_authentic",
                         "remote_fresh", "time_quality_ok", "forward")

            def __init__(self, t):
                self.t = t
                self.i_diff = 0.5           # comfortably over the floor
                self.i_restraint = 0.0
                self.remote_authentic = True
                self.remote_fresh = True
                self.time_quality_ok = True
                self.forward = True

        sh = S.Shield()
        prop = S.Proposal(want_trip=True, req_p0=P0_MIN, req_k=K_MIN)
        step_grants = any(
            sh.step(_BareSample(t), prop, False, True)[0]
            for t in range(DWELL_MS + 1))
        return bool(five_grants), bool(step_grants)

    t0 = time.perf_counter()
    five_open, step_open = _probe_compat_paths()

    # And a NEGATIVE CONTROL, so this row cannot pass vacuously: flip the
    # constant that closes the hazard and confirm both probes go permissive
    # again.  If the control does not fire, the detector has stopped
    # detecting and says so, whatever the main probe returned.
    _saved = getattr(S, "REQUIRE_LOCAL_PROVENANCE", None)
    try:
        S.REQUIRE_LOCAL_PROVENANCE = False
        ctl_five, ctl_step = _probe_compat_paths()
    finally:
        if _saved is None:
            del S.REQUIRE_LOCAL_PROVENANCE
        else:
            S.REQUIRE_LOCAL_PROVENANCE = _saved
    control_fires = ctl_five and ctl_step

    hazard = five_open or step_open
    closed = (not hazard) and control_fires
    out.append({
        "name": ("A8C compatibility paths FAIL OPEN -- DEPLOYMENT HAZARD"
                 if hazard else
                 ("A8C compatibility paths fail CLOSED (hazard closed)"
                  if control_fires else
                  "A8C DETECTOR INERT -- negative control did not fire")),
        "statement": (
            ("decide()'s five-element form and Shield.step's absent-attribute "
             "path substitute a permissive local_ok, so an un-updated caller "
             "silently runs the pre-A8 shield with A8-LINUX no longer "
             "discharged."
             if hazard else
             "decide()'s five-element form and Shield.step's absent-attribute "
             "path both REFUSE.  A default is not an authentication: absent "
             "provenance is now refused rather than trusted, by one rule "
             "(REQUIRE_LOCAL_PROVENANCE) covering both paths.")
            + "  Probed by calling the shield, not by matching its source, so "
              "a refactor that reintroduced the hazard with different wording "
              "would still be caught.  This row is a live gate: if either "
              "path goes permissive, `proved` goes False and the whole suite "
              "goes red."),
        # A real gate now, not a recorded fact: it feeds the aggregate.
        "proved": closed,
        "is_observation": True,
        "hazard_open": hazard,
        "five_element_form_fails_open": five_open,
        "step_absent_attr_fails_open": step_open,
        "require_local_provenance": getattr(S, "REQUIRE_LOCAL_PROVENANCE",
                                            None),
        "negative_control_fires": control_fires,
        "ms": round((time.perf_counter() - t0) * 1000, 2),
        "counterexample": None,
    })
    return out


def prove_restricted_has_teeth():
    """I7f, re-checked at BOTH levels.  In v1 this came back PROVED, which was
    the finding: the tier was unobservable.  In v2 it must split."""
    out = []

    # Level 1: `decide` alone.  Still true, and still fine: decide is pure
    # over booleans and tests mode only as `== BASELINE_ONLY`.
    c, d = Step(2), Step(3)
    shared = [(c.latched, d.latched), (c.n_gt, d.n_gt), (c.gt0, d.gt0),
              (c.gt1, d.gt1), (c.seen, d.seen), (c.ls, d.ls),
              (c.now, d.now), (c.want, d.want), (c.time_ok, d.time_ok),
              (c.remote_ok, d.remote_ok), (c.local_ok, d.local_ok),
              (c.forward, d.forward)]
    # decide's diff_ok is an INPUT boolean at this level, so force it equal.
    dok = Bool("shared_diff_ok")

    def decide_only(s, mode_val):
        backwards = And(s.seen, s.now < s.ls)
        rate = And(s.n_gt >= MAX_GRANTS, s.now - s.gt0 < WINDOW_MS)
        return And(s.want, mode_val != BASELINE_ONLY, Not(s.latched),
                   Not(backwards), Not(rate), s.time_ok, s.remote_ok,
                   s.local_ok,
                   s.forward, dok)

    out.append(_check(
        "I7f/decide  NORMAL and RESTRICTED decide identically (still true)",
        And(And(*[x == y for x, y in shared]),
            decide_only(c, IntVal(NORMAL)) != decide_only(d,
                                                          IntVal(RESTRICTED))),
        "decide() reads mode only via (mode == BASELINE_ONLY), so the tier is "
        "invisible AT THIS LEVEL -- which is why it must be checked one "
        "level up"))

    # Level 2: Shield.step, where `effective_cert` lives.  Here the tiers must
    # be DISTINGUISHABLE, so we look for a witness rather than a refutation.
    e, f = Step(4), Step(5)
    same_inputs = And(
        [e.mode == NORMAL, f.mode == RESTRICTED] +
        [x == y for x, y in
         [(e.latched, f.latched), (e.n_gt, f.n_gt), (e.gt0, f.gt0),
          (e.gt1, f.gt1), (e.seen, f.seen), (e.ls, f.ls), (e.now, f.now),
          (e.want, f.want), (e.time_ok, f.time_ok),
          (e.remote_ok, f.remote_ok), (e.local_ok, f.local_ok),
          (e.forward, f.forward),
          (e.cert, f.cert), (e.i_diff, f.i_diff),
          (e.i_restraint, f.i_restraint), (e.req_p0, f.req_p0),
          (e.req_k, f.req_k), (e.fin_diff, f.fin_diff),
          (e.fin_restraint, f.fin_restraint), (e.fin_p0, f.fin_p0),
          (e.fin_k, f.fin_k),
          # v4 state, equated so the ONLY difference is the trust tier
          (e.diff_run, f.diff_run), (e.excursions, f.excursions),
          (e.vetoes, f.vetoes), (e.vmax, f.vmax)]])
    out.append(_witness(
        "I7f/step   RESTRICTED is observably weaker than NORMAL (v2 fix)",
        And(same_inputs, e.grant, Not(f.grant)),
        "exists inputs . step grants in NORMAL and vetoes in RESTRICTED "
        "-- i.e. the tier is no longer decorative",
        extra={"want": "sat"}))

    # And quantify the difference: exactly the sensitivity band it withdraws.
    out.append(_check(
        "I7f/band   the withdrawn band is exactly [nominal, floor)",
        And(same_inputs, e.cert, e.grant, Not(f.grant),
            Not(And(e.i_diff > zmax(P0_MIN,
                                    K_MIN * If(e.i_restraint < 0, 0,
                                               e.i_restraint)),
                    Not(e.i_diff > zmax(P0_NOM,
                                        K_NOM * If(e.i_restraint < 0, 0,
                                                   e.i_restraint)))))),
        "every input distinguishing NORMAL from RESTRICTED lies strictly "
        "between the hard floor and the nominal threshold"))
    return out


def prove_v1_regressions():
    """Every historic defect, kept as a regression theorem.

    DEFECT 1 (rate limiter).  v1 used a single `last_grant_ms` scalar and a
    JUMPING window: `commit` reset the grant counter whenever the most recent
    grant looked older than WINDOW_MS.  With a clock that could step
    backwards, Z3 found grants at t = 998, 0, 1000, 999; the subset
    {0, 998, 999} spans 999 ms < WINDOW_MS = 1000, i.e. THREE accelerated
    trips inside one 1000 ms window against MAX_GRANTS = 2.

    DEFECT 2 (decorative tier).  v1's RESTRICTED mode was provably
    unobservable: `decide` read mode only as `== BASELINE_ONLY`, so NORMAL and
    RESTRICTED produced identical decisions for every input.

    Both are re-run here against v2.  Defect 1 must now be unsat under a FREE
    clock -- not merely under the monotone assumption, since removing the need
    for that assumption is the entire point of the fix.
    """
    out = []

    # R1 -- the v1 counterexample trace, replayed concretely against v2.
    # Drive the machine with the exact timestamps Z3 found for v1, give the
    # attacker EVERY advantage (perfect physics corroboration and reclose
    # authorisation at every step, so the latch never binds), and ask for the
    # maximum number of grants obtainable.
    v1_times = [998, 0, 0, 0, 1000, 0, 999, 999]
    steps = [Step(200 + i) for i in range(len(v1_times))]
    s = Solver()
    s.add(init(steps[0]))
    for i in range(len(v1_times) - 1):
        s.add(trans(steps[i], steps[i + 1], "free"))
    for i, t in enumerate(v1_times):
        s.add(steps[i].now == t)
        s.add(steps[i].want, steps[i].time_ok, steps[i].remote_ok,
              steps[i].local_ok,
              steps[i].forward, steps[i].diff_ok, steps[i].reclose,
              Not(steps[i].reinstate))   # the attacker has no operator channel
    t0 = time.perf_counter()
    best = 0
    for target in range(1, len(v1_times) + 1):
        s.push()
        s.add(steps[-1].ng >= target)
        ok = s.check() == sat
        s.pop()
        if not ok:
            break
        best = target
    out.append({
        "name": "R1 D1 rate-limit counterexample, replayed",
        "statement": "v2 driven with the exact v1 attack timestamps "
                     "t = [998,0,0,0,1000,0,999,999], every step requesting a "
                     "trip with perfect corroboration and reclose auth",
        "v1_result": "3 grants, of which {0,998,999} span 999 ms < WINDOW_MS",
        "max_grants_obtainable_now": best,
        "ms": round((time.perf_counter() - t0) * 1000, 2),
        "fixed": best <= MAX_GRANTS,
    })

    # R2 -- a monotonically DECREASING clock, the pure form of the attack.
    steps = [Step(300 + i) for i in range(10)]
    s = Solver()
    s.add(init(steps[0]))
    for i in range(9):
        s.add(trans(steps[i], steps[i + 1], "free"))
    for i in range(10):
        s.add(steps[i].want)
        s.add(steps[i].time_ok)
        s.add(steps[i].remote_ok)
        s.add(steps[i].local_ok)
        s.add(steps[i].forward)
        s.add(steps[i].diff_ok)
        s.add(steps[i].reclose)          # maximally helpful to the attacker
        s.add(Not(steps[i].reinstate))   # attacker has no operator channel
        if i > 0:
            s.add(steps[i].now < steps[i - 1].now)
    t0 = time.perf_counter()
    r = s.check()
    ng_dec = None
    if r == sat:
        ng_dec = int(str(s.model().eval(steps[9].ng)))
    # and the MAXIMUM obtainable, by asking for more
    s.push()
    s.add(steps[9].ng >= 2)
    more = s.check() == sat
    s.pop()
    out.append({
        "name": "R2 strictly decreasing clock, 10 steps, all preconditions met",
        "statement": "every step requests a trip with perfect corroboration "
                     "and reclose authorisation, on a clock that only ever "
                     "goes backwards",
        "grants_obtained": ng_dec,
        "can_obtain_2_or_more": more,
        "ms": round((time.perf_counter() - t0) * 1000, 2),
        "v1_result": "3 grants obtainable; v2/v3: 1; v4 adds DWELL so the "
                     "first sample can never grant either",
        "fixed": ng_dec is not None and ng_dec <= 1 and not more,
    })

    # R3 -- the v1 defect stated as a theorem: is I2 true with NO clock
    # assumption at all?  This is the load-bearing regression.
    r3 = prove_by_kinduction(
        "R3 I2 under a FREE clock (v1: DISPROVED -- and now?)",
        I2_span4_strong, kmax=8, bmc_depth=12, clock="free",
        note="no monotonicity assumption whatsoever; now_ms free at each step")
    out.append({
        "name": r3["name"],
        "statement": "forall traces with arbitrary integer timestamps . "
                     "no three of the four most recent grants share a "
                     "WINDOW_MS window",
        "verdict": r3["verdict"], "k": r3["k"],
        "ms": round(r3["bmc_ms"] + r3["kind_ms"], 2),
        "counterexample": r3["counterexample"],
        "fixed": r3["verdict"] == "PROVED",
    })

    # R5 -- defect 3 (the v2 availability defect I raised in my own report):
    # replay the coordinator's concrete regression symbolically.  Honest 1 ms
    # samples, ONE sample dated t = 999999 injected between them, then honest
    # samples resume.  Under v2 the watermark would have jumped to 999999 and
    # every subsequent honest sample would have been vetoed as backwards.
    times = [1, 2, 3, 4, 999999, 5, 6]
    st = [Step(600 + i) for i in range(len(times) + 1)]
    sv = Solver()
    sv.add(init(st[0]))
    for i in range(len(times)):
        sv.add(trans(st[i], st[i + 1]))
        sv.add(st[i].now == times[i], Not(st[i].reinstate))
    # The leading honest samples merely establish the watermark; they request
    # nothing.  The injected sample requests nothing either.  The honest tail
    # (t = 5, 6) requests a trip with full corroboration -- two samples,
    # because v4 requires the corroboration to be SUSTAINED for DWELL_MS.
    for i, t in enumerate(times):
        if i >= 5:
            sv.add(st[i].want, st[i].time_ok, st[i].remote_ok,
                   st[i].local_ok, st[i].forward, st[i].diff_ok)
        else:
            sv.add(Not(st[i].want))
    t0 = time.perf_counter()
    r5 = {"name": "R5 D3 watermark-poisoning defect: one spoofed future sample",
          "statement": "honest 1 ms samples with a single t = 999999 injected; "
                       "under v2 the watermark jumped and every later honest "
                       "sample was vetoed.  The honest tail is now %d samples "
                       "long because of DWELL_MS." % DWELL_MS,
          "v2_result": "watermark poisoned to 999999; total denial of service",
          "ms": 0.0}
    if sv.check() == sat:
        m = sv.model()
        r5["watermark_after_injection"] = str(m.eval(st[5].ls))
        r5["injected_sample_was_excursion"] = str(m.eval(st[4].excursion))
        r5["honest_tail_granted"] = str(m.eval(Or(st[5].grant, st[6].grant)))
        # and prove it, rather than merely exhibiting one model
        sv.push()
        sv.add(Or(st[5].ls != 4, Not(st[4].excursion),
                  And(Not(st[5].grant), Not(st[6].grant))))
        r5["proved_for_all_models"] = sv.check() == unsat
        sv.pop()
    r5["ms"] = round((time.perf_counter() - t0) * 1000, 2)
    r5["fixed"] = r5.get("proved_for_all_models", False)
    out.append(r5)

    # R6 -- defect 5 (the unauthenticated local addend).  Replay the exact
    # FDI shape -- a steady forged differential parked just above the floor --
    # against v5, for BOTH adversaries, and report them separately.  The whole
    # point of the v5 change is that these two now diverge.
    mm = DWELL_MS + 4
    res6 = {}
    for label, local_key in (("linux_plane_adversary", False),
                             ("mu_key_adversary", True)):
        fz = [Step(1900 + (0 if local_key else 100) + i) for i in range(mm + 1)]
        sv = Solver()
        sv.add(init(fz[0]))
        for i in range(mm):
            sv.add(trans(fz[i], fz[i + 1]))
            sv.add(fz[i].i_diff == fz[0].i_diff, fz[i].fin_diff,
                   fz[i].i_restraint == 0, fz[i].fin_restraint,
                   fz[i].fin_p0, fz[i].fin_k,
                   fz[i].want, fz[i].time_ok, fz[i].remote_ok,
                   fz[i].local_ok if local_key else Not(fz[i].local_ok),
                   fz[i].forward, fz[i].cert, Not(fz[i].reinstate),
                   fz[i].now == i)
        sv.add(fz[0].i_diff > P0_MIN, fz[0].i_diff < P0_MIN + 0.02)
        sv.add(Or(*[fz[i].grant for i in range(mm)]))
        res6[label] = "GRANTED" if sv.check() == sat else "no grant possible"
    out.append({
        "name": "R6 D5 unauthenticated local addend: the A8 split",
        "statement": "the measured FDI shape -- a steady forged differential "
                     "parked just above P0_MIN, held for %d samples on an "
                     "honest clock -- replayed against v5 for each adversary "
                     "separately" % mm,
        "v4_result": "25 of 25 tuned episodes defeated the shield; only the "
                     "remote addend was authenticated, so the SUM was "
                     "forgeable by anyone on the local wire",
        "vs_linux_plane_adversary": res6["linux_plane_adversary"],
        "vs_mu_key_adversary": res6["mu_key_adversary"],
        "ms": 0.0,
        # The fix is what it claims to be iff exactly one of the two closes.
        "fixed": (res6["linux_plane_adversary"] == "no grant possible"
                  and res6["mu_key_adversary"] == "GRANTED"),
    })

    # R4 -- defect 2: RESTRICTED must no longer be unobservable at step level.
    e, f = Step(400), Step(401)
    same = And(
        [e.mode == NORMAL, f.mode == RESTRICTED] +
        [x == y for x, y in
         [(e.latched, f.latched), (e.n_gt, f.n_gt), (e.gt0, f.gt0),
          (e.gt1, f.gt1), (e.seen, f.seen), (e.ls, f.ls), (e.now, f.now),
          (e.want, f.want), (e.time_ok, f.time_ok),
          (e.remote_ok, f.remote_ok), (e.local_ok, f.local_ok),
          (e.forward, f.forward),
          (e.cert, f.cert), (e.i_diff, f.i_diff),
          (e.i_restraint, f.i_restraint), (e.req_p0, f.req_p0),
          (e.req_k, f.req_k), (e.fin_diff, f.fin_diff),
          (e.fin_restraint, f.fin_restraint), (e.fin_p0, f.fin_p0),
          (e.fin_k, f.fin_k),
          (e.diff_run, f.diff_run), (e.excursions, f.excursions),
          (e.vetoes, f.vetoes), (e.vmax, f.vmax)]])
    sw = Solver()
    sw.add(And(same, e.grant, Not(f.grant)))
    t0 = time.perf_counter()
    found = sw.check() == sat
    out.append({
        "name": "R4 D2 decorative-tier defect: RESTRICTED now observable",
        "statement": "exists inputs distinguishing NORMAL from RESTRICTED at "
                     "Shield.step level",
        "v1_result": "no such input existed (tier was provably decorative)",
        "distinguishable_now": found,
        "ms": round((time.perf_counter() - t0) * 1000, 2),
        "fixed": found,
    })
    return out


def prove_shield_invariants(kmax=8, bmc_depth=12):
    """Encode decide/commit/Shield.step as a transition system and discharge
    I1..I8 and the transparency property.  Inputs, INCLUDING THE CLOCK, are
    unconstrained at every step."""
    props = []
    P = props.append

    P(prove_by_kinduction(
        "W  state well-formedness (SPARK subtypes are inductive)", W,
        kmax, bmc_depth, note="mode in 0..2, vetoes in 0..24, window/ghost "
                              "coherence, watermark dominates every grant"))
    P(prove_by_kinduction(
        "I1 no-trip-without-physics", I1, kmax, bmc_depth,
        note="grant => diff_ok and forward and remote_ok and time_ok"))
    P(prove_by_kinduction(
        "I1-local BOTH addends authenticated and fresh (v5)", I1_local,
        kmax, bmc_depth,
        note="grant => local_ok; the delta over I1, kept on its own line"))
    P(prove_by_kinduction(
        "I1-both  I1 and I1-local composed (A8 Linux-plane half)", I1_both,
        kmax, bmc_depth,
        note="grant => remote_ok and local_ok: every term the shield reasons "
             "about came from an authenticated, fresh channel"))
    P(prove_by_kinduction(
        "I3 latch until reclose_auth", I3, kmax, bmc_depth,
        note="latched => no grant; latched cleared only by reclose_auth"))
    P(prove_by_kinduction(
        "I4 time integrity", I4, kmax, bmc_depth,
        note="grant => time_quality_ok"))
    P(prove_by_kinduction(
        "I4b no grant on an implausible timestamp (v2/v3)", I4b, kmax,
        bmc_depth,
        note="grant => the timestamp is inside the plausibility window"))
    P(prove_by_kinduction(
        "P1 grant implies timestamp within the plausibility window (v3)", P1,
        kmax, bmc_depth,
        note="grant => ls <= now <= ls + MAX_CLOCK_STEP_MS"))
    P(prove_by_kinduction(
        "P4 a plausible timestamp is never vetoed for time (v3)", P4,
        kmax, bmc_depth,
        note="the service half of DoS-freedom"))
    P(prove_by_kinduction(
        "P6 clock-advance bound: the AI cannot inflate elapsed time (v3)", P6,
        kmax, bmc_depth,
        note="grant => now <= last_seen_ms + MAX_CLOCK_STEP_MS"))
    P(prove_by_kinduction(
        "I5 certified region (RESTRICTED withdraws sensitivity)", I5,
        kmax, bmc_depth,
        note="grant without (cert_ok and mode=NORMAL) => nominal threshold"))
    P(prove_by_kinduction(
        "I5b hard floor holds unconditionally", I5b, kmax, bmc_depth,
        note="every grant clears max(P0_MIN, K_MIN*i_restraint)"))
    P(prove_by_kinduction(
        "I6 baseline pass-through", I6, kmax, bmc_depth,
        note="baseline_trip => trip_out, for every state and proposal"))
    P(prove_by_kinduction(
        "I8 non-finite measurement never grants (v2)", I8, kmax, bmc_depth,
        note="grant => i_diff and i_restraint both finite"))
    P(prove_by_kinduction(
        "DWELL grant implies sustained corroboration (v4)", DWELL, kmax,
        bmc_depth,
        note="grant => diff_ok on this and the previous %d sample(s)"
             % (DWELL_MS - 1)))
    P(prove_by_kinduction(
        "S5 either counter alone disowns the model (v4)", S5, kmax, bmc_depth,
        note="vetoes >= VETO_LIMIT or excursions >= EXCURSION_LIMIT "
             "=> BASELINE_ONLY"))
    P(prove_by_kinduction(
        "TRANSPARENCY (no gratuitous veto, dwell-aware)", TRANSPARENCY, kmax,
        bmc_depth,
        note="good AI in NORMAL, unlatched, in budget, clock sane, physics "
             "ok => granted"))

    # I2: the bare property first (honest), then strengthened, then the
    # order-agnostic form, ALL under a free clock.
    P(prove_by_kinduction("I2 rate limit (bare, plain k-induction)", I2,
                          kmax, bmc_depth,
                          note="never MAX_GRANTS+1 grants inside WINDOW_MS"))
    P(prove_by_kinduction(
        "I2 rate limit (strengthened with W)", I2_strong, kmax, bmc_depth,
        note="I2 conjoined with the well-formedness invariant"))
    P(prove_by_kinduction(
        "I2 rate limit, ORDER-AGNOSTIC, FREE CLOCK", I2_span4_strong,
        kmax, bmc_depth, clock="free",
        note="no clock assumption at all; the v1 form of this was DISPROVED"))

    dis = prove_disowning()
    teeth = prove_restricted_has_teeth()
    water = prove_watermark()
    dwell = prove_dwell()
    split = prove_split_counters()

    core = [p for p in props if "bare, plain" not in p["name"]]
    return {
        "layer": "logic",
        "method": "symbolic transition relation + BMC + k-induction (Z3)",
        "state_space": "(mode, latched, grant_times[0..2], vetoes, "
                       "last_seen_ms) + 4 ghost grant timestamps + ng",
        "clock_assumption": "NONE -- now_ms is a free integer at every step",
        "inputs": "fully unconstrained at every step (hostile AI)",
        "invariants": props,
        "i7_disowning": dis,
        "i7f_restricted": teeth,
        "watermark": water,
        "dwell": dwell,
        "split_counters": split,
        "proved": (all(p["verdict"] == "PROVED" for p in core)
                   and all(m["proved"] for m in dis)
                   and teeth[0]["proved"] and teeth[1]["found"]
                   and teeth[2]["proved"]
                   and all(w["proved"] for w in water)
                   and all(w["proved"] for w in dwell)
                   and all(w.get("proved", w.get("verdict") == "PROVED")
                           for w in split)),
    }


# ===========================================================================
# Reporting
# ===========================================================================

def _rule(w=100):
    return "-" * w


def main():
    print("=" * 100)
    print("GridSentinel -- machine-checked shield verification (Z3)")
    # DERIVED, never asserted.  A hand-written version number in this banner
    # is the same failure mode as the A8C row was: it goes stale silently and
    # a reader trusts it.  Print what can be checked instead -- a content hash
    # of the frozen artifact and the constants that characterise its
    # behaviour, all read from the module at run time.
    import hashlib
    import inspect as _insp
    _digest = hashlib.sha256(
        _insp.getsource(S).encode("utf-8")).hexdigest()[:12]
    print("Artifact under verification: gs/shield.py  [frozen; sha256:%s]"
          % _digest)
    print("  characterising constants read from the artifact: "
          "MAX_GRANTS=%d WINDOW_MS=%d DWELL_MS=%d" %
          (MAX_GRANTS, WINDOW_MS, DWELL_MS))
    print("  VETO_LIMIT=%d EXCURSION_LIMIT=%d MAX_CLOCK_STEP_MS=%d "
          "REQUIRE_LOCAL_PROVENANCE=%s" %
          (VETO_LIMIT, EXCURSION_LIMIT, MAX_CLOCK_STEP,
           getattr(S, "REQUIRE_LOCAL_PROVENANCE", None)))
    print("=" * 100)

    nf = prove_nonfinite_handling()
    print("\nLAYER 0 -- NON-FINITE HANDLING (IEEE-754 binary64, real NaN/inf)")
    print(_rule())
    print("%-62s %-10s %9s" % ("THEOREM", "VERDICT", "TIME(ms)"))
    print(_rule())
    for t in nf:
        if t["name"].startswith("FPM"):
            v = "PROVED" if t["proved"] else "ASSUMED"
        elif t["proved"]:
            v = "PROVED"
        elif t["status"] == "unknown":
            v = "UNKNOWN"
        else:
            v = "SAT!"
        print("%-62s %-10s %9s" % (t["name"][:62], v, t["ms"]))
        if t.get("modulo"):
            print("      discharged modulo: %s" % t["modulo"])
        if t["counterexample"]:
            print("      COUNTEREXAMPLE: %s" % t["counterexample"])

    num = prove_sensitivity_floor()
    print("\nLAYER 1 -- NUMERIC (real arithmetic, unbounded)")
    print(_rule())
    print("%-62s %-10s %9s" % ("THEOREM", "VERDICT", "TIME(ms)"))
    print(_rule())
    for t in num["theorems"]:
        print("%-62s %-10s %9s" % (t["name"][:62],
                                   "PROVED" if t["proved"] else "SAT!",
                                   t["ms"]))
        if t["counterexample"]:
            print("      COUNTEREXAMPLE: %s" % t["counterexample"])
    wm = num["worst_case_margin"]
    print(_rule())
    print("  worst-case safety margin (infimum over i_restraint >= 0): "
          "%s pu  (= %.6f)" % (wm["infimum_pu"], wm["infimum_float"]))
    print("  attained at i_restraint = %s pu (threshold breakpoint "
          "P0_MIN/K_MIN = %.4f)" % (wm["attained_at_i_restraint"],
                                    wm["threshold_breakpoint_ir"]))
    print("  slope headroom K_MIN - A1_CT_ERROR = %.4f  (must be > 0 as "
          "ir -> inf)" % wm["slope_headroom"])

    log = prove_shield_invariants()
    print("\nLAYER 2 -- LOGIC (transition relation, hostile unconstrained "
          "inputs)")
    print("  clock assumption: %s" % log["clock_assumption"])
    print(_rule())
    print("%-58s %-14s %4s %9s" % ("PROPERTY", "VERDICT", "k", "TIME(ms)"))
    print(_rule())
    for p in log["invariants"]:
        print("%-58s %-14s %4s %9s" % (
            p["name"][:58], p["verdict"],
            p["k"] if p["k"] is not None else "-",
            round(p["bmc_ms"] + p["kind_ms"], 2)))
        if p["counterexample"]:
            print("      CE at depth %s" % p["counterexample"]["depth"])
    print(_rule())
    for m in log["i7_disowning"]:
        print("%-58s %-14s %4s %9s" % (
            m["name"][:58], "PROVED" if m["proved"] else "DISPROVED", "1",
            m["ms"]))
        if m["counterexample"]:
            print("      COUNTEREXAMPLE: %s" % m["counterexample"])
    print(_rule())
    for m in log["i7f_restricted"]:
        if "found" in m:
            print("%-58s %-14s %4s %9s" % (
                m["name"][:58],
                "WITNESS FOUND" if m["found"] else "NO WITNESS!", "-",
                m["ms"]))
        else:
            print("%-58s %-14s %4s %9s" % (
                m["name"][:58], "PROVED" if m["proved"] else "DISPROVED", "1",
                m["ms"]))

    print(_rule())
    for m in log["dwell"] + log["split_counters"]:
        ok = m.get("proved", m.get("verdict") == "PROVED")
        k = m.get("k", 1)
        if m.get("is_observation"):
            # Verdict derived from the probe, never a static string: this row
            # must read as closed when it is closed and as a hazard the moment
            # it is not.  A stale headline here would be the proof suite doing
            # to a reader what documentation drift does.
            verdict = ("HAZARD OPEN" if m.get("hazard_open")
                       else ("CLOSED" if m.get("negative_control_fires")
                             else "DETECTOR INERT"))
            k = "-"
        elif m.get("is_negative_result"):
            verdict = "SHOWN (sat)" if ok else "NOT SHOWN"
            k = "-"
        else:
            verdict = "PROVED" if ok else "DISPROVED"
        print("%-58s %-14s %4s %9s" % (
            m["name"][:58], verdict,
            k if k is not None else "-",
            m.get("ms", round(m.get("bmc_ms", 0) + m.get("kind_ms", 0), 2))))
        if m.get("counterexample"):
            print("      COUNTEREXAMPLE: %s" % m["counterexample"])
        if m.get("is_observation"):
            print("        5-element decide() grants without provenance = %s"
                  " ; sample lacking provenance grants = %s"
                  % (m["five_element_form_fails_open"],
                     m["step_absent_attr_fails_open"]))
            print("        REQUIRE_LOCAL_PROVENANCE = %s ; negative control "
                  "fires = %s   (behavioural probe, not a source grep)"
                  % (m["require_local_provenance"],
                     m["negative_control_fires"]))
        if m.get("is_negative_result"):
            print("        NEGATIVE RESULT (sat is expected): forged "
                  "i_diff = %s pu obtains a grant" % m.get("forged_i_diff_pu"))
        if m.get("proposal_slots"):
            print("        Proposal fields: %s   (no `reinstate`); "
                  "Shield.step passes reinstate: %s"
                  % (m["proposal_slots"], m["step_mentions_reinstate"]))
    print(_rule())
    for m in log["watermark"]:
        print("%-58s %-14s %4s %9s" % (
            m["name"][:58], "PROVED" if m["proved"] else "DISPROVED",
            "1" if "per_n" not in m else "-", m["ms"]))
        if m.get("one_repeated_timestamp_suffices"):
            print("        and a SINGLE repeated implausible timestamp "
                  "suffices (watermark is frozen on excursion)")
        if m.get("per_n"):
            print("        burst lengths N = %s : %s"
                  % ([x["n"] for x in m["per_n"]],
                     "all unsat" if all(x["ok"] for x in m["per_n"])
                     else [x["ok"] for x in m["per_n"]]))
        if m["counterexample"]:
            print("      COUNTEREXAMPLE: %s" % m["counterexample"])

    reg = prove_v1_regressions()
    print("\nREGRESSION -- every historic defect, replayed against "
          "the CURRENT artifact")
    print(_rule())
    for r in reg:
        print("%-58s %-14s %9s" % (r["name"][:58],
                                   "FIXED" if r["fixed"] else "STILL BROKEN",
                                   r["ms"]))
        for key in ("v1_result", "v2_result", "max_grants_obtainable_now",
                    "grants_obtained", "can_obtain_2_or_more",
                    "distinguishable_now", "v4_result",
                    "vs_linux_plane_adversary", "vs_mu_key_adversary",
                    "watermark_after_injection",
                    "injected_sample_was_excursion",
                    "honest_tail_granted", "proved_for_all_models",
                    "verdict", "k"):
            if key in r and r[key] is not None:
                print("        %-24s %s" % (key + ":", r[key]))

    print("\n" + _rule())
    print("SUMMARY")
    print(_rule())
    nf_core = [t for t in nf if not t["name"].startswith("FPM")]
    print("  layer 0 (non-finite) : %s"
          % ("ALL PROVED (N3 modulo the FPM side condition, which Z3 could "
             "not close)" if all(t["proved"] for t in nf_core)
             else "SEE ABOVE"))
    print("  layer 1 (numeric)    : %s"
          % ("ALL PROVED" if num["proved"] else "NOT PROVED"))
    print("  layer 2 (logic)      : %s"
          % ("ALL PROVED, WITH NO CLOCK ASSUMPTION" if log["proved"]
             else "NOT PROVED"))
    print("  defect regressions   : %s"
          % ("ALL FIXED" if all(r["fixed"] for r in reg) else "SEE ABOVE"))
    print(_rule())
    print("  ASSUMPTION A8 IS NOW SPLIT.  ONE HALF IS DISCHARGED; ONE HALF "
          "IS NOT.")
    print("    i_diff = |I_local + I_remote| is a SUM.  The shield "
          "authenticates BOTH addends (I1-local,")
    print("    I1-both), not just the remote one.")
    print("")
    print("    A8-LINUX  the adversary owns the inference plane but holds no "
          "merging-unit key.")
    print("              DISCHARGED -- now theorem A8L: with local provenance "
          "unauthenticated they")
    print("              obtain ZERO grants, however they choose i_diff, "
          "i_restraint or the settings.")
    print("")
    print("    A8-MU     the adversary HOLDS the local merging unit's signing "
          "key.  STILL AN")
    print("              ASSUMPTION.  Their forgeries verify, so "
          "authentication cannot see them and")
    print("              DW5 stands unchanged: a steady forged differential "
          "defeats ANY dwell length.")
    print("              Bounded only by non-exportable HSM key custody and "
          "attestation -- neither of")
    print("              which is modelled, tested or proved anywhere in this "
          "report.")
    print("")
    print("    Authenticating the local addend did not solve the FDI "
          "problem; it cut it in two and")
    print("    solved the larger half.")
    print("    See docs/PROOF.md sections 2 (A8-LINUX / A8-MU) and 8.7.")
    print(_rule())
    print("  see docs/PROOF.md for assumptions, k values and what is NOT "
          "proved.")
    return {"nonfinite": nf, "numeric": num, "logic": log, "regression": reg}


if __name__ == "__main__":
    main()
