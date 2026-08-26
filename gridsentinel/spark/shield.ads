------------------------------------------------------------------------------
--  GridSentinel  --  trusted plane, safety-island shield  (SPARK 2014)
--
--  VERSION 5.  Mirrors gs/shield.py after the repair of five defects, all
--  found by machine-checked analysis (see docs/PROOF.md, "Defect history"):
--     D1  the rate limiter was a JUMPING window keyed off a single
--         Last_Grant_Ms scalar, and a backwards clock step bought a third
--         accelerated trip inside one window;
--     D2  the RESTRICTED trust tier was provably unobservable;
--     D3  the v2 fix for D1 was ONE-SIDED -- it rejected backwards timestamps
--         but accepted arbitrarily large forward ones, so a single sample
--         dated far in the future poisoned the watermark and denied service
--         to every honest sample after it.  v2 traded an integrity defect for
--         an availability one;
--     D4  one counter and one limit were shared between two unrelated failure
--         modes -- a misbehaving model and a misbehaving clock -- so a
--         merging-unit or PTP fault disowned a blameless model and silently
--         withdrew its adaptive sensitivity via Restricted.  Because the veto
--         count clears only on a grant, and a calm grid produces no grants,
--         the shared count was effectively a LIFETIME total;
--     D5  only the REMOTE addend of the differential was authenticated.
--         I_Diff = |I_Local + I_Remote| is a SUM, so authenticating one half
--         leaves the sum forgeable: anyone on the local wire could hold the
--         differential steadily just above the floor and below the nominal
--         pickup, invisible to conventional protection.  That defeated the
--         shield in 25 of 25 tuned episodes.
--  All five are fixed below: a true sliding window held in a fixed-size
--  array; a clock PLAUSIBILITY WINDOW (not a bare watermark) that an
--  implausible timestamp cannot move at all; and Effective_Cert in Step so
--  that RESTRICTED withdraws adaptive sensitivity; SEPARATE Veto_Count and
--  Excursion_Count with independent limits, plus an authenticated operator
--  Reinstate that is unreachable from Proposal_T; and a DWELL requirement so
--  the shield is no longer twitchier than the 87L element it supervises.
--
--  NOT COMPILED OR PROVED IN THIS REPOSITORY.  gnatprove and gnat are not
--  installed on the machine where this was written (`which gnatprove` finds
--  nothing), so nothing below has been run through the toolchain: it is
--  source-level evidence of the shipping artifact, hand-checked for
--  well-formedness, and it is the mirror of gs/shield.py procedure for
--  procedure.  Treat every claim in this header as "expected", not
--  "discharged".  The properties that HAVE been machine-checked were checked
--  on the Python mirror with Z3; see gs/verify.py and docs/PROOF.md.
--
--  What gnatprove would be expected to discharge, at level 2
--  (--level=2 --prover=cvc5,z3,altergo):
--
--    (a) Absence of run-time errors (AoRTE) for the whole package:
--        no overflow in Now_Ms - St.Grant_Times (Ms is 64-bit); every index
--        into Grant_Window is guarded by N_Grants; Grant_Count and Veto_Count
--        saturate before assignment; no division, no uninitialised reads.
--    (b) Every Post and Contract_Cases below, in particular:
--          Differential_Ok'Post   -- T2, I5, and the non-finite obligations
--                                    N1/N2/N4 that in Python are guarded by
--                                    an explicit math.isfinite check
--          Decide'Contract_Cases  -- I1, I3, I4, I4b and TRANSPARENCY
--          Commit'Post            -- I7 (mode monotonicity), the watermark
--          Step'Post              -- I6 (baseline pass-through), I5
--    (c) The Global => null and Depends aspects, i.e. flow analysis proving
--        the shield reads nothing but its formals and touches no package or
--        heap state.
--    (d) SPARK_Mode => On over the whole body with no dynamic allocation, no
--        secondary stack (no unconstrained function results), no unbounded
--        loops (the only loop is over Grant_Index, whose bounds are static),
--        no exceptions, no tasking and no recursion -- so worst-case
--        execution time is a straight-line bound suitable for the
--        Cortex-R5F safety island.
--
--  THE NON-FINITE OBLIGATION.  gs/shield.py rejects NaN and +/-inf with an
--  explicit `math.isfinite` test rather than relying on IEEE-754 comparison
--  semantics, precisely so that the property survives translation to Ada,
--  where a NaN is not a silent False but a bounded-subtype violation.  Here
--  that becomes a TYPE distinction: Raw_Pu (what the merging unit hands over,
--  possibly garbage) versus Current and Setting (validated).  Is_Finite is
--  the only bridge between them, and it is a precondition of nothing --
--  Differential_Ok takes Raw_Pu and fails closed, exactly as the Python does,
--  so a bad sample can never raise Constraint_Error on the safety island.
--
--  ACCEPTED TRADE, NOT AN OVERSIGHT.  Excursion_Limit clock excursions still
--  drive the shield to Baseline_Only with no trip ever requested (I7g, P7),
--  and I7b proves Baseline_Only is absorbing absent a Reinstate.  Permanence
--  is deliberate and load-bearing: it is what makes the I7 family close at
--  k = 1, and automatic re-arming would be an attacker-groomable surface.
--  What v4 changes is that the excursion lands in its OWN counter (S1, S2,
--  S4, S4b), so a clock fault can no longer be laundered into a verdict about
--  the model, and that recovery is possible through an AUTHENTICATED OPERATOR
--  action (S6) rather than requiring a truck.  docs/PROOF.md section 8.4.
--
--  ASSUMPTION A8, WHICH v5 SPLITS IN TWO.  I_Diff = |I_Local + I_Remote| is
--  a SUM, so a contract concluding anything from Diff_Ok is only as good as
--  the provenance of BOTH addends.  Until v5 that was one assumption; it was
--  violated; and it conflated two adversaries who behave nothing alike.
--
--    A8-LINUX -- the adversary owns the inference plane but holds no
--      merging-unit signing key.  DISCHARGED.  Decide now requires Local_Ok
--      as well as Remote_Ok (R_Local below), so such an adversary cannot
--      present a sample the shield will read at all, whatever numbers it
--      contains.  Theorem A8L in gs/verify.py: zero grants over any trace,
--      with I_Diff, I_Restraint and both requested settings free at every
--      step.  This is the half that was actually being exploited.
--
--    A8-MU -- the adversary HOLDS the local merging unit's own signing key.
--      STILL AN ASSUMPTION, and it must keep the prominence it had.  Their
--      forgeries verify, so Local_Ok is true for them by construction and
--      authentication is blind to them.  Theorem DW5 is unchanged by v5: a
--      STEADY forged differential defeats any Dwell_Ms whatsoever.  The
--      residual is bounded only by non-exportable HSM key custody and
--      attestation, neither of which is modelled, tested or proved anywhere.
--
--  v5 did not solve false data injection.  It cut it in two and solved the
--  larger half.  See docs/PROOF.md sections 2 and 8.7.
--
--  WHAT IS STILL ASSUMED.  I2 no longer needs a monotone-clock assumption --
--  the watermark makes it a theorem, and Z3 proves it with `now_ms` a free
--  integer at every step.  One IEEE-754 side condition (FPM: correctly-
--  rounded multiplication is monotone in its first argument for a
--  non-negative second argument) is assumed rather than proved; Z3's
--  bit-blaster does not close it within 45 s.  See docs/PROOF.md.
------------------------------------------------------------------------------

package Shield with SPARK_Mode => On is

   ---------------------------------------------------------------------------
   --  Types
   ---------------------------------------------------------------------------

   --  Raw, UNVALIDATED input from the merging unit.  May be NaN or infinite.
   subtype Raw_Pu is Long_Float;

   --  Validated per-unit quantities.  The bounds are what make the single
   --  multiplication in Differential_Ok free of an overflow VC.
   type Pu is digits 15 range -1.0E9 .. 1.0E9;
   subtype Current is Pu range 0.0 .. 1.0E3;    --  measured currents, pu
   subtype Setting is Pu range -1.0E3 .. 1.0E3;
   --  Setting is deliberately WIDER than any sane relay setting and admits
   --  negative values: the AI is hostile and may propose absurdities.  The
   --  clamp, not the type, is what makes that safe.

   --  Milliseconds.  64-bit, so no difference of two timestamps can overflow.
   type Ms is range -2 ** 62 .. 2 ** 62 - 1;
   subtype Time_Ms is Ms range 0 .. 2 ** 40;

   type Mode_T is (Normal, Restricted, Baseline_Only);
   --  Ordered by DECREASING trust in the AI.  Mode_T'Pos matches the Python
   --  constants NORMAL = 0, RESTRICTED = 1, BASELINE_ONLY = 2.

   Max_Grants : constant := 2;
   Window_Ms  : constant Ms := 1_000;
   Veto_Limit      : constant := 24;   --  MODEL misbehaviour
   Excursion_Limit : constant := 24;   --  clock/instrument faults (v4)

   --  Consecutive samples the differential must hold above the clamped
   --  threshold before a grant.  Before this the shield granted on ONE
   --  sample while the conventional 87L element beside it requires six, so it
   --  was strictly twitchier than the protection it supervises.
   Dwell_Ms : constant := 2;

   --  Largest forward clock step accepted between samples.  Samples arrive
   --  every 1 ms, so 100 ms is generous for dropped frames while still
   --  bounding the watermark.  Without this the monotone check is one-sided
   --  and defect D3 reappears.
   Max_Clock_Step_Ms : constant Ms := 100;

   subtype Grant_Index is Positive range 1 .. Max_Grants;
   subtype Grant_Count is Natural  range 0 .. Max_Grants;
   --  v4: SEPARATE counters.  Veto_Count is advanced only by a model that
   --  keeps proposing unjustified trips; Excursion_Count only by a clock that
   --  keeps producing implausible timestamps.  Sharing one counter meant a
   --  merging-unit fault was laundered into a verdict about the AI -- and,
   --  worse, twelve clock glitches reached Restricted, which by I5 withdraws
   --  the model's adaptive sensitivity for a reason that has nothing to do
   --  with the model.  S1, S2, S3, S4 and S4b in gs/verify.py are the proofs
   --  that the two are now independent.
   subtype Veto_Count      is Natural range 0 .. Veto_Limit;
   subtype Excursion_Count is Natural range 0 .. Excursion_Limit;
   --  Saturating run length; only the comparison with Dwell_Ms is observable.
   subtype Dwell_Count     is Natural range 0 .. Dwell_Ms;

   --  The sliding window.  A FIXED-SIZE array, ascending, oldest at index 1,
   --  with N_Grants valid entries.  This is the direct analogue of the Python
   --  list `State.grant_times`, minus the allocation: a single Last_Grant_Ms
   --  scalar was NOT sufficient (defect D1) because it implements a jumping
   --  window, and a sliding window needs the whole history it quantifies over.
   type Grant_Window is array (Grant_Index) of Ms;

   --  Protection constants (identical to gs/shield.py).
   P0_Nom : constant Pu := 0.30;   --  nominal 87L pickup floor
   K_Nom  : constant Pu := 0.35;   --  nominal percentage-restraint slope
   P0_Min : constant Pu := 0.10;   --  hard floor: most sensitive setting ever
   K_Min  : constant Pu := 0.20;   --  hard floor on the restraint slope

   --  Proof assumptions about the plant (mirrored in gs/measure.py).
   A1_Ct_Error : constant Pu := 0.12;  --  max CT/MU error, frac. of through-I
   A2_Charging : constant Pu := 0.02;  --  max capacitive differential, pu

   type Reason_T is
     (R_Grant,
      R_No_Request,
      R_Mode,            --  veto: disowned model
      R_Latched,         --  veto: awaiting reclose authorisation
      R_Time_Backwards,  --  veto: the sample clock went backwards      (v2)
      R_Time_Jump,       --  veto: the sample clock jumped implausibly  (v3)
      R_Rate,            --  veto: rate limit
      R_Time,            --  veto: time-source integrity
      R_Remote,          --  veto: remote channel unauthenticated
      R_Local,           --  veto: local channel unauthenticated      (v5)
      R_Direction,       --  veto: directional, reverse
      R_Physics,         --  veto: no physics corroboration
      R_Dwell);          --  veto: physics not sustained for Dwell_Ms  (v4)

   --  The AI's entire attack surface on the plant.
   type Proposal_T is record
      Want_Trip  : Boolean := False;
      Req_P0     : Raw_Pu  := Raw_Pu (P0_Min);
      Req_K      : Raw_Pu  := Raw_Pu (K_Min);
      Confidence : Raw_Pu  := 0.0;
   end record;

   --  The corroborating boolean evidence handed to Decide.
   type Inputs_T is record
      Time_Ok      : Boolean;
      Remote_Ok    : Boolean;
      --  v5.  The two ends are SEPARATE fields with SEPARATE veto reasons,
      --  so the veto spectrum distinguishes which end failed.  Folding them
      --  into one "channels_ok" would have made the two indistinguishable in
      --  the sequence-of-events record, which is exactly the information an
      --  engineer needs first.
      Local_Ok     : Boolean;
      Forward      : Boolean;
      Diff_Ok      : Boolean;
      Reclose_Auth : Boolean;
   end record;

   type State_T is record
      Mode         : Mode_T       := Normal;
      Latched      : Boolean      := False;
      Grant_Times  : Grant_Window := (others => 0);
      N_Grants     : Grant_Count  := 0;
      Vetoes       : Veto_Count      := 0;   --  MODEL misbehaviour only
      Excursions   : Excursion_Count := 0;   --  clock faults only     (v4)
      Diff_Run     : Dwell_Count     := 0;   --  corroboration run     (v4)
      --  Clock plausibility watermark.  Python's None becomes an explicit
      --  flag; v1 assumed monotone timestamps implicitly, never enforced it,
      --  and I2 was disproved without that assumption (defect D1).  v3 makes
      --  the check two-sided (defect D3).
      Seen         : Boolean      := False;
      Last_Seen_Ms : Ms           := 0;
   end record;

   ---------------------------------------------------------------------------
   --  Ghost machinery: the state invariant (invariant W of gs/verify.py)
   ---------------------------------------------------------------------------

   function Window_Ascending (St : State_T) return Boolean is
     (St.N_Grants < 2 or else St.Grant_Times (1) <= St.Grant_Times (2))
   with Ghost;

   function Valid_State (St : State_T) return Boolean is
     (Window_Ascending (St)
      --  NOTE: v1-v3 also carried "the watermark dominates every grant".
      --  v4 CANNOT: Reinstate deliberately resyncs the clock, so the
      --  watermark legitimately drops below an earlier grant's timestamp.
      --  I2 never needed it -- the sliding window is anchored on
      --  Grant_Times (1), not on the watermark.
      and then (if St.Vetoes >= Veto_Limit
                   or else St.Excursions >= Excursion_Limit
                then St.Mode = Baseline_Only))
   with Ghost;
   --  The subtypes Mode_T / Grant_Count / Veto_Count carry the rest of the
   --  well-formedness that gs/verify.py has to state explicitly, because Z3
   --  has no types.  That is the argument for the shipping artifact being the
   --  SPARK one: half of invariant W becomes a type, not a proof obligation.

   ---------------------------------------------------------------------------
   --  Layer 0 -- validation of raw input
   ---------------------------------------------------------------------------

   --  The ONLY bridge from Raw_Pu to Pu.  Note the redundancy: 'Valid rejects
   --  invalid representations, and the two range tests independently reject
   --  NaN (every comparison with NaN is False) and both infinities.  The
   --  conjunction is therefore correct whatever a particular runtime makes of
   --  'Valid on a floating-point object.
   function Is_Finite (X : Raw_Pu) return Boolean is
     (X'Valid
      and then X >= Raw_Pu (Pu'First)
      and then X <= Raw_Pu (Pu'Last));

   function Sanitised_Restraint (X : Raw_Pu) return Current is
     (if not Is_Finite (X) then 0.0
      elsif X < 0.0 then 0.0                       --  shield.py:73-74
      elsif X > Raw_Pu (Current'Last) then Current'Last
      else Current (X))
   with Ghost;

   ---------------------------------------------------------------------------
   --  Layer 1 -- NUMERIC
   ---------------------------------------------------------------------------

   --  The certificate buys sensitivity and NOTHING else.
   procedure Thresholds
     (Cert_Ok :     Boolean;
      P0      : out Pu;
      K       : out Pu)
   with
     Global  => null,
     Depends => (P0 => Cert_Ok, K => Cert_Ok),
     Post    => (if Cert_Ok then P0 = P0_Min and K = K_Min
                            else P0 = P0_Nom and K = K_Nom)
                and then P0 >= P0_Min and then K >= K_Min;

   --  True iff the authenticated differential exceeds the CLAMPED threshold.
   --  Req_P0 / Req_K are what the AI asked for; they are clamped upward to
   --  the floors, so the AI can only ever make the relay LESS sensitive.
   --
   --  Takes Raw_Pu and FAILS CLOSED on anything that is not finite.  This is
   --  a total function on garbage input: it cannot raise Constraint_Error,
   --  which is what makes it safe to call on an unvalidated merging-unit
   --  sample on the safety island.
   function Differential_Ok
     (I_Diff      : Raw_Pu;
      I_Restraint : Raw_Pu;
      Cert_Ok     : Boolean;
      Req_P0      : Raw_Pu;
      Req_K       : Raw_Pu) return Boolean
   with
     Global => null,
     Contract_Cases =>
       --  N1: a non-finite MEASUREMENT fails closed.  (shield.py:71-72)
       (not (Is_Finite (I_Diff) and Is_Finite (I_Restraint)) =>
          Differential_Ok'Result = False,
        others => True),
     Post   =>
       --  T2, the clamp theorem: whatever the AI proposes -- finite,
       --  infinite, NaN, negative, absurd -- a true result implies the
       --  differential cleared the hard floor.
       (if Differential_Ok'Result then
          Is_Finite (I_Diff) and then Is_Finite (I_Restraint)   --  I8
          and then Raw_Pu (I_Diff) >
            Raw_Pu (Pu'Max (P0_Min,
                            K_Min * Sanitised_Restraint (I_Restraint))))
       --  I5, the certified-region theorem: without the certificate the
       --  NOMINAL thresholds gate the decision.  Combined with Step's
       --  Effective_Cert, this is what gives RESTRICTED its teeth (defect D2).
       and then (if Differential_Ok'Result and then not Cert_Ok then
                   Raw_Pu (I_Diff) >
                     Raw_Pu (Pu'Max (P0_Nom,
                                     K_Nom *
                                       Sanitised_Restraint (I_Restraint))));

   --  LEMMA (no-false-trip floor).  In gs/shield.py this is
   --  lemma_sensitivity_floor, which merely SAMPLES 200001 points.  Here it
   --  is a contract: gnatprove would have to discharge it over the whole
   --  interval, as Z3 does over the whole of the reals.
   function Sensitivity_Floor_Holds (I_Restraint : Current) return Boolean is
     (A1_Ct_Error * I_Restraint + A2_Charging
        < Pu'Max (P0_Min, K_Min * I_Restraint))
   with Ghost;

   ---------------------------------------------------------------------------
   --  Layer 2 -- LOGIC
   ---------------------------------------------------------------------------

   --  A backwards clock step is not a glitch to be clamped away; it was the
   --  precondition of the only known attack on the rate limiter (defect D1),
   --  so it is a first-class security event with its own veto reason.
   function Time_Went_Backwards (St : State_T; Now_Ms : Time_Ms)
                                 return Boolean is
     (St.Seen and then Now_Ms < St.Last_Seen_Ms);

   --  v3.  The other half of the window.  A forward jump is just as much a
   --  clock-integrity event as a backwards one, and admitting it unbounded is
   --  what made v2 vulnerable to a single poisoned timestamp.
   function Clock_Jumped (St : State_T; Now_Ms : Time_Ms) return Boolean is
     (St.Seen and then Now_Ms - St.Last_Seen_Ms > Max_Clock_Step_Ms);

   function Clock_Excursion (St : State_T; Now_Ms : Time_Ms) return Boolean is
     (Time_Went_Backwards (St, Now_Ms) or else Clock_Jumped (St, Now_Ms));

   --  The service guarantee, stated as a function so it can appear in
   --  contracts: a timestamp inside the plausibility window is never rejected
   --  for a clock reason.  (Theorem P4 in gs/verify.py.)
   function Clock_Plausible (St : State_T; Now_Ms : Time_Ms) return Boolean is
     (not St.Seen
        or else (Now_Ms >= St.Last_Seen_Ms
                 and then Now_Ms - St.Last_Seen_Ms <= Max_Clock_Step_Ms))
   with Post => Clock_Plausible'Result = not Clock_Excursion (St, Now_Ms);

   --  TRUE SLIDING WINDOW: if the OLDEST of the last Max_Grants grants is
   --  still inside the window, the budget is spent.  Contrast v1, which
   --  compared against the NEWEST grant and reset the counter -- a jumping
   --  window, and the defect.
   function Rate_Blocked (St : State_T; Now_Ms : Time_Ms) return Boolean is
     (St.N_Grants >= Max_Grants
        and then Now_Ms - St.Grant_Times (1) < Window_Ms)
   with Pre => Valid_State (St);

   --  v4.  The corroboration run is advanced in Commit, so Decide stays a
   --  pure function of (state, inputs) and its Contract_Cases stay enumerable.
   function Dwell_Met (St : State_T) return Boolean is
     (St.Diff_Run + 1 >= Dwell_Ms);

   --  Pure decision function.  Does not mutate state; see Commit.
   --  The Contract_Cases below are the veto cascade of gs/shield.py in
   --  evaluation order.  They are pairwise disjoint and complete, which is
   --  itself a verification condition gnatprove checks.
   procedure Decide
     (St      :     State_T;
      Now_Ms  :     Time_Ms;
      Inp     :     Inputs_T;
      Want    :     Boolean;
      Grant   : out Boolean;
      Reason  : out Reason_T)
   with
     Global  => null,
     Depends => ((Grant, Reason) => (St, Now_Ms, Inp, Want)),
     Pre     => Valid_State (St),
     Contract_Cases =>
       (not Want                                                  =>
          not Grant and Reason = R_No_Request,
        Want and St.Mode = Baseline_Only                          =>
          not Grant and Reason = R_Mode,
        Want and St.Mode /= Baseline_Only and St.Latched           =>
          not Grant and Reason = R_Latched,
        Want and St.Mode /= Baseline_Only and not St.Latched
             and Time_Went_Backwards (St, Now_Ms)                 =>
          not Grant and Reason = R_Time_Backwards,
        Want and St.Mode /= Baseline_Only and not St.Latched
             and not Time_Went_Backwards (St, Now_Ms)
             and Clock_Jumped (St, Now_Ms)                        =>
          not Grant and Reason = R_Time_Jump,
        Want and St.Mode /= Baseline_Only and not St.Latched
             and not Clock_Excursion (St, Now_Ms)
             and Rate_Blocked (St, Now_Ms)                        =>
          not Grant and Reason = R_Rate,
        Want and St.Mode /= Baseline_Only and not St.Latched
             and not Clock_Excursion (St, Now_Ms)
             and not Rate_Blocked (St, Now_Ms)
             and not Inp.Time_Ok                                  =>
          not Grant and Reason = R_Time,
        Want and St.Mode /= Baseline_Only and not St.Latched
             and not Clock_Excursion (St, Now_Ms)
             and not Rate_Blocked (St, Now_Ms)
             and Inp.Time_Ok and not Inp.Remote_Ok                =>
          not Grant and Reason = R_Remote,
        --  v5.  The local addend is checked immediately after the remote one,
        --  so the two ends stay distinguishable in the veto spectrum.
        Want and St.Mode /= Baseline_Only and not St.Latched
             and not Clock_Excursion (St, Now_Ms)
             and not Rate_Blocked (St, Now_Ms)
             and Inp.Time_Ok and Inp.Remote_Ok and not Inp.Local_Ok  =>
          not Grant and Reason = R_Local,
        Want and St.Mode /= Baseline_Only and not St.Latched
             and not Clock_Excursion (St, Now_Ms)
             and not Rate_Blocked (St, Now_Ms)
             and Inp.Time_Ok and Inp.Remote_Ok and Inp.Local_Ok
             and not Inp.Forward                                  =>
          not Grant and Reason = R_Direction,
        Want and St.Mode /= Baseline_Only and not St.Latched
             and not Clock_Excursion (St, Now_Ms)
             and not Rate_Blocked (St, Now_Ms)
             and Inp.Time_Ok and Inp.Remote_Ok and Inp.Local_Ok
             and Inp.Forward and not Inp.Diff_Ok                  =>
          not Grant and Reason = R_Physics,
        --  v4 DWELL: the corroboration must have been SUSTAINED.
        Want and St.Mode /= Baseline_Only and not St.Latched
             and not Clock_Excursion (St, Now_Ms)
             and not Rate_Blocked (St, Now_Ms)
             and Inp.Time_Ok and Inp.Remote_Ok and Inp.Forward
             and Inp.Local_Ok
             and Inp.Diff_Ok and not Dwell_Met (St)               =>
          not Grant and Reason = R_Dwell,
        --  TRANSPARENCY: everything in order => the trip IS granted.  The
        --  shield never gratuitously vetoes a good AI.
        others                                                    =>
          Grant and Reason = R_Grant),
     --  I1 / I3 / I4 / I4b restated as a plain Post, visible to callers.
     Post    => (if Grant then
                   Want
                   and Inp.Diff_Ok and Inp.Forward                --  I1
                   and Inp.Remote_Ok and Inp.Time_Ok              --  I1, I4
                   and Inp.Local_Ok                               --  I1-local
                   and St.Mode /= Baseline_Only                   --  I7c
                   and not St.Latched                             --  I3
                   and not Clock_Excursion (St, Now_Ms)           --  I4b
                   and Clock_Plausible (St, Now_Ms)               --  P1
                   and Dwell_Met (St)                             --  DWELL
                   and not Rate_Blocked (St, Now_Ms));            --  I2

   --  State update.  Separated from Decide so that the decision is a pure
   --  function of (state, inputs) and can be enumerated exhaustively.
   procedure Commit
     (St           : in out State_T;
      Now_Ms       :        Time_Ms;
      Granted      :        Boolean;
      Want_Trip    :        Boolean;
      Reclose_Auth :        Boolean;
      Reinstate    :        Boolean := False;
      Diff_Ok      :        Boolean := False)
   with
     Global  => null,
     Depends => (St =>+ (Now_Ms, Granted, Want_Trip, Reclose_Auth,
                         Reinstate, Diff_Ok)),
     Pre     => Valid_State (St)
                --  Granted can only have come from Decide, which refuses on
                --  any clock excursion; carrying that as a Pre is what lets
                --  the window stay ascending without a sort.
                and then (if Granted then
                            not Clock_Excursion (St, Now_Ms)
                            and then not Rate_Blocked (St, Now_Ms)
                            and then Dwell_Met (St)),
     Post    => Valid_State (St)
                --  the watermark only ever advances                (v2)
                and then (if not Reinstate then
                            St.Seen
                            and then St.Last_Seen_Ms >= St'Old.Last_Seen_Ms)
                --  P2a, THE v3 THEOREM: an implausible timestamp does not
                --  move the watermark AT ALL.  This one line is the whole of
                --  the D3 fix, and everything else about denial-of-service
                --  resistance follows from it by induction on the burst
                --  length.
                and then (if Clock_Excursion (St'Old, Now_Ms)
                             and then not Reinstate
                          then St.Last_Seen_Ms = St'Old.Last_Seen_Ms
                               and then St.Seen = St'Old.Seen)
                --  P2b/P2c: the watermark only ever takes the value of a
                --  sample that PASSED the plausibility test.
                and then (if St.Last_Seen_Ms /= St'Old.Last_Seen_Ms
                             and then not Reinstate
                          then not Clock_Excursion (St'Old, Now_Ms)
                               and then St.Last_Seen_Ms = Now_Ms)
                and then (if not Clock_Excursion (St'Old, Now_Ms)
                             and then not Reinstate
                          then St.Last_Seen_Ms >= Now_Ms)
                --  I7: the mode never recovers on its own.  ABSENT a
                --  Reinstate -- the authenticated operator may rearm, and
                --  nothing else can (S6b).
                and then (if not Reinstate then
                            St.Mode >= St'Old.Mode
                            and then (if St'Old.Mode = Baseline_Only then
                                        St.Mode = Baseline_Only))
                --  S6: Reinstate restores Normal, zeroes BOTH counters, and
                --  resyncs the clock.  Omitting the resync would leave a
                --  stale frozen watermark, so the very next honest sample is
                --  judged an excursion and the operator achieves nothing.
                and then (if Reinstate then
                            St.Mode = Normal
                            and then St.Excursions = 0
                            and then St.Vetoes <= 1)
                --  S1: a clock excursion NEVER touches the model's counter.
                and then (if not Want_Trip and not Reinstate then
                            St.Vetoes = St'Old.Vetoes)
                --  S2: model misbehaviour NEVER touches the excursion counter.
                and then (if not Clock_Excursion (St'Old, Now_Ms)
                             and not Reinstate
                          then St.Excursions = St'Old.Excursions)
                --  S3: neither counter is cleared by the other's event.
                and then (if Granted and not Reinstate then
                            St.Vetoes = 0
                            and then St.Excursions = St'Old.Excursions)
                --  S5: either counter alone disowns the model.
                and then (if St.Vetoes >= Veto_Limit
                             or else St.Excursions >= Excursion_Limit
                          then St.Mode = Baseline_Only)
                --  DWELL: the run counter tracks the corroboration exactly.
                and then (if Diff_Ok then St.Diff_Run > 0
                                     else St.Diff_Run = 0)
                --  I7e: the veto counter is cleared only by a real grant.
                and then (if not Granted then St.Vetoes >= St'Old.Vetoes)
                --  I7g: a clock excursion in EITHER direction advances
                --  disowning on its own.                       (v2, v3)
                and then (if Clock_Excursion (St'Old, Now_Ms)
                             and then not Reinstate
                             and then St'Old.Excursions < Excursion_Limit
                          then St.Excursions > St'Old.Excursions)
                --  I3: a grant always arms the latch and records its time.
                and then (if Granted then
                            St.Latched
                            and then St.N_Grants >= 1
                            and then St.Grant_Times (St.N_Grants) = Now_Ms
                            and then St.Vetoes = 0)
                --  the latch is cleared by nothing but reclose authorisation.
                and then (if St'Old.Latched and not Reclose_Auth then
                            St.Latched)
                and then (if St.Vetoes >= Veto_Limit then
                            St.Mode = Baseline_Only);

   ---------------------------------------------------------------------------
   --  Composition:  Layer 1 + Layer 2 + unconditional baseline pass-through
   ---------------------------------------------------------------------------

   type Sample_T is record
      T                : Time_Ms;
      I_Diff           : Raw_Pu;      --  unvalidated: may be NaN or infinite
      I_Restraint      : Raw_Pu;
      Remote_Fresh     : Boolean;
      Remote_Authentic : Boolean;
      Local_Fresh      : Boolean;      --  v5
      Local_Authentic  : Boolean;      --  v5
      Time_Quality_Ok  : Boolean;
      Forward          : Boolean;
   end record;

   type Source_T is (Src_None, Src_Baseline, Src_Ai_Shield);

   --  RESTRICTED is no longer decorative (defect D2).  Z3 proved that in v1
   --  the tier was unobservable: Decide tests Mode only as = Baseline_Only,
   --  so Normal and Restricted decided identically for every input.  This
   --  function is the graduated step between full trust and disowning the
   --  model: it withdraws the AI's access to adaptive sensitivity, so a model
   --  under suspicion must clear the NOMINAL threshold instead of the floor.
   --  It deliberately lives in Step, not in Decide -- Decide stays pure over
   --  booleans, which is what makes its Contract_Cases enumerable.
   function Effective_Cert (St : State_T; Cert_Ok : Boolean) return Boolean is
     (Cert_Ok and then St.Mode = Normal);

   procedure Step
     (St            : in out State_T;
      Sample        :        Sample_T;
      Proposal      :        Proposal_T;
      Baseline_Trip :        Boolean;
      Cert_Ok       :        Boolean;
      Reclose_Auth  :        Boolean;
      Trip          :    out Boolean;
      Source        :    out Source_T;
      Reason        :    out Reason_T)
   with
     Global  => null,
     Depends => (St     =>+ (Sample, Proposal, Cert_Ok, Reclose_Auth),
                 (Trip, Source, Reason) =>
                   (St, Sample, Proposal, Baseline_Trip, Cert_Ok,
                    Reclose_Auth)),
     Pre     => Valid_State (St),
     Post    => Valid_State (St)
                --  I6, BASELINE PASS-THROUGH.  The single most important line
                --  in the package: conventional protection is OR-ed at the
                --  output and is never routed through Decide, so no shield
                --  state and no proposal can inhibit it.
                and then (if Baseline_Trip then
                            Trip and Source = Src_Baseline)
                --  the shield can only ever ADD a trip, never remove one.
                and then (if not Baseline_Trip and Trip then
                            Source = Src_Ai_Shield and Reason = R_Grant
                            and Proposal.Want_Trip
                            and Sample.Time_Quality_Ok            --  I4
                            and Sample.Forward
                            --  I1-both: EVERY term the shield reasons about
                            --  came from an authenticated, fresh channel.
                            --  This is assumption A8-LINUX, discharged.
                            and (Sample.Remote_Authentic
                                 and Sample.Remote_Fresh)         --  I1
                            and (Sample.Local_Authentic
                                 and Sample.Local_Fresh)          --  I1-local
                            and Is_Finite (Sample.I_Diff)         --  I8
                            and Is_Finite (Sample.I_Restraint)
                            and Raw_Pu (Sample.I_Diff) >
                                  Raw_Pu (Pu'Max
                                    (P0_Min,
                                     K_Min * Sanitised_Restraint
                                               (Sample.I_Restraint)))
                            --  DWELL: and it was not the first such sample.
                            --  CONDITIONAL ON A8: this says the differential
                            --  cleared the floor, not that the differential
                            --  is TRUE.  See the header.
                            and Dwell_Met (St'Old)
                            --  I5: outside NORMAL, the nominal threshold.
                            and (if St'Old.Mode /= Normal or else not Cert_Ok
                                 then Raw_Pu (Sample.I_Diff) >
                                   Raw_Pu (Pu'Max
                                     (P0_Nom,
                                      K_Nom * Sanitised_Restraint
                                                (Sample.I_Restraint)))))
                and then St.Mode >= St'Old.Mode;                  --  I7

end Shield;
