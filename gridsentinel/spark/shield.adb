------------------------------------------------------------------------------
--  GridSentinel  --  trusted plane, safety-island shield  (SPARK 2014, body)
--
--  VERSION 5.  NOT COMPILED OR PROVED HERE: gnatprove and gnat are not
--  installed on this machine.  See the header of shield.ads for what the
--  toolchain would be expected to discharge.  This body is straight-line,
--  allocation-free, exception-free and secondary-stack-free by construction;
--  its one loop runs over Grant_Index, whose bounds are static.
--
--  Correspondence with gs/shield.py v5 is one-to-one; the Python line each
--  statement mirrors is cited in a comment.
------------------------------------------------------------------------------

package body Shield with SPARK_Mode => On is

   ---------------------------------------------------------------------------
   --  Layer 1 -- NUMERIC
   ---------------------------------------------------------------------------

   procedure Thresholds
     (Cert_Ok :     Boolean;
      P0      : out Pu;
      K       : out Pu)
   is
   begin
      if Cert_Ok then          --  shield.py:51  if cert_ok:
         P0 := P0_Min;         --  shield.py:52      return P0_MIN, K_MIN
         K  := K_Min;
      else
         P0 := P0_Nom;         --  shield.py:53  return P0_NOM, K_NOM
         K  := K_Nom;
      end if;
   end Thresholds;

   function Differential_Ok
     (I_Diff      : Raw_Pu;
      I_Restraint : Raw_Pu;
      Cert_Ok     : Boolean;
      Req_P0      : Raw_Pu;
      Req_K       : Raw_Pu) return Boolean
   is
      P0_Floor  : Pu;
      K_Floor   : Pu;
      P0        : Pu;
      K         : Pu;
      Ir        : Current;
      Threshold : Pu;
      Diff      : Pu;
   begin
      --  shield.py:71-72  FAIL CLOSED on any non-finite MEASUREMENT.
      --  In Python this replaced an accidental reliance on IEEE-754
      --  comparison semantics; in Ada it is load-bearing for a different
      --  reason -- without it the conversions below could raise
      --  Constraint_Error on the safety island, which is not an option.
      if not Is_Finite (I_Diff) or else not Is_Finite (I_Restraint) then
         return False;
      end if;

      --  shield.py:73-74  if i_restraint < 0.0: i_restraint = 0.0
      if I_Restraint < 0.0 then
         Ir := 0.0;
      elsif I_Restraint > Raw_Pu (Current'Last) then
         Ir := Current'Last;   --  saturate rather than trap; see note below
      else
         Ir := Current (I_Restraint);
      end if;

      if I_Diff > Raw_Pu (Pu'Last) then
         Diff := Pu'Last;
      elsif I_Diff < Raw_Pu (Pu'First) then
         Diff := Pu'First;
      else
         Diff := Pu (I_Diff);
      end if;
      --  NOTE.  These two saturations have no counterpart in gs/shield.py,
      --  which has no bounded float type to overflow.  They are a REFINEMENT,
      --  not a divergence: saturating I_Restraint upward can only RAISE the
      --  threshold, and saturating I_Diff downward can only LOWER the
      --  measured differential, so both directions are conservative with
      --  respect to granting a trip.  Every theorem in docs/PROOF.md that
      --  concludes "grant => i_diff exceeded the floor" survives.

      Thresholds (Cert_Ok, P0_Floor, K_Floor);   --  shield.py:76

      --  shield.py:80  A non-finite request is not honoured in EITHER
      --  direction: +inf would otherwise let a hostile model deny service by
      --  demanding an unreachable threshold.  Both absurd directions collapse
      --  onto the proven floor.
      if Is_Finite (Req_P0)
        and then Req_P0 > Raw_Pu (P0_Floor)
        and then Req_P0 <= Raw_Pu (Setting'Last)
      then
         P0 := Pu (Req_P0);
      elsif Is_Finite (Req_P0) and then Req_P0 > Raw_Pu (Setting'Last) then
         P0 := Setting'Last;                --  an absurd but finite request
      else
         P0 := P0_Floor;
      end if;

      --  shield.py:81  same, for the restraint slope
      if Is_Finite (Req_K)
        and then Req_K > Raw_Pu (K_Floor)
        and then Req_K <= Raw_Pu (Setting'Last)
      then
         K := Pu (Req_K);
      elsif Is_Finite (Req_K) and then Req_K > Raw_Pu (Setting'Last) then
         K := Setting'Last;
      else
         K := K_Floor;
      end if;

      --  shield.py:82  threshold = p0 if p0 > k*i_restraint else k*i_restraint
      if P0 > K * Ir then
         Threshold := P0;
      else
         Threshold := K * Ir;
      end if;

      --  Proof hints for gnatprove.  Each is a consequence of the clamps
      --  above plus Ir >= 0 (guaranteed by subtype Current); the same facts
      --  are what Z3 uses to close theorems T2 and N3 in gs/verify.py.
      pragma Assert (P0 >= P0_Floor and then P0_Floor >= P0_Min);
      pragma Assert (K >= K_Floor and then K_Floor >= K_Min);
      pragma Assert (Ir >= 0.0);
      pragma Assert (K * Ir >= K_Min * Ir);        --  the FPM side condition
      pragma Assert (Threshold >= Pu'Max (P0_Min, K_Min * Ir));
      pragma Assert (if not Cert_Ok then
                       Threshold >= Pu'Max (P0_Nom, K_Nom * Ir));

      return Diff > Threshold;                     --  shield.py:83
   end Differential_Ok;

   ---------------------------------------------------------------------------
   --  Layer 2 -- LOGIC
   ---------------------------------------------------------------------------

   procedure Decide
     (St      :     State_T;
      Now_Ms  :     Time_Ms;
      Inp     :     Inputs_T;
      Want    :     Boolean;
      Grant   : out Boolean;
      Reason  : out Reason_T)
   is
   begin
      --  The veto cascade, in evaluation order.  Order matters for the
      --  transparency contract: the FIRST failing precondition is reported,
      --  so the operator always learns the binding constraint.
      if not Want then                                     --  shield.py:191
         Grant  := False;
         Reason := R_No_Request;
      elsif St.Mode = Baseline_Only then                   --  shield.py:193
         Grant  := False;
         Reason := R_Mode;
      elsif St.Latched then                                --  shield.py:195
         Grant  := False;
         Reason := R_Latched;
      elsif Time_Went_Backwards (St, Now_Ms) then          --  shield.py:211
         Grant  := False;
         Reason := R_Time_Backwards;
      elsif Clock_Jumped (St, Now_Ms) then                 --  shield.py:213
         --  v3.  A forward jump is as much a clock-integrity event as a
         --  backwards one; admitting it unbounded is what let a single
         --  poisoned timestamp deny service in v2 (defect D3).
         Grant  := False;
         Reason := R_Time_Jump;
      elsif Rate_Blocked (St, Now_Ms) then                 --  shield.py:216
         Grant  := False;
         Reason := R_Rate;
      elsif not Inp.Time_Ok then                           --  shield.py:207
         Grant  := False;
         Reason := R_Time;
      elsif not Inp.Remote_Ok then                         --  shield.py:263
         Grant  := False;
         Reason := R_Remote;
      elsif not Inp.Local_Ok then                          --  shield.py:276
         --  v5.  ASSUMPTION A8, now ENFORCED rather than assumed for the
         --  Linux-plane adversary.  I_Diff = |I_Local + I_Remote| is a SUM;
         --  authenticating only the remote addend left the sum forgeable, and
         --  that defeated the shield in 25 of 25 tuned episodes.  Checked
         --  immediately after Remote_Ok so the two ends remain
         --  distinguishable in the veto spectrum.  This does NOT close an
         --  adversary holding the local unit's own key -- see A8-MU in the
         --  spec header.
         Grant  := False;
         Reason := R_Local;
      elsif not Inp.Forward then                           --  shield.py:211
         Grant  := False;
         Reason := R_Direction;
      elsif not Inp.Diff_Ok then                           --  shield.py:255
         Grant  := False;
         Reason := R_Physics;
      elsif not Dwell_Met (St) then                        --  shield.py:257
         --  v4.  The corroboration must have been SUSTAINED.  Without this
         --  the shield granted on ONE sample while the 87L element beside it
         --  requires six -- strictly twitchier than the protection it
         --  supervises.  It removes the noise-crossing case ONLY; see the
         --  A8 note in shield.ads.
         Grant  := False;
         Reason := R_Dwell;
      else                                                 --  shield.py:215
         Grant  := True;
         Reason := R_Grant;
      end if;
   end Decide;

   procedure Commit
     (St           : in out State_T;
      Now_Ms       :        Time_Ms;
      Granted      :        Boolean;
      Want_Trip    :        Boolean;
      Reclose_Auth :        Boolean;
      Reinstate    :        Boolean := False;
      Diff_Ok      :        Boolean := False)
   is
      --  shield.py:234-239  record the clock excursion before anything else
      --  consumes Now_Ms.  ONE flag covering both directions.
      Excursion     : constant Boolean := Clock_Excursion (St, Now_Ms);
      Old_Watermark : constant Ms      := St.Last_Seen_Ms with Ghost;
   begin
      --  shield.py:240-241  the excursion counts toward disowning even when
      --  no trip was requested.
      --  shield.py:275-283  REINSTATE: an authenticated operator action on
      --  the same channel as Reclose_Auth.  "A human must decide" should not
      --  have to mean "a human must drive to the substation"; permanence with
      --  no path back is a reliability trap, not a safety property.  It is
      --  unreachable from Proposal_T -- Step never passes it -- so the model
      --  can never rearm itself.
      if Reinstate then
         St.Mode       := Normal;
         St.Vetoes     := 0;
         St.Excursions := 0;
         --  Resync the clock too.  Reinstating without clearing a stale,
         --  frozen watermark means the very next honest sample is judged an
         --  excursion against it and the operator achieves nothing.
         St.Seen := False;
      end if;

      --  shield.py:284-285  counted APART from model misbehaviour (v4).
      if Excursion and then not Reinstate
        and then St.Excursions < Excursion_Limit
      then
         St.Excursions := St.Excursions + 1;
      end if;

      --  shield.py:244-245  THE v3 FIX, and the whole of it.  An implausible
      --  timestamp must NOT advance the watermark, or one spoofed future
      --  sample permanently denies service to every honest one after it.
      --  Note the guard is `not Excursion` FIRST: without it this is the v2
      --  code, and defect D3 is back.
      if not Excursion
        and then (not St.Seen or else Now_Ms > St.Last_Seen_Ms)
      then
         St.Last_Seen_Ms := Now_Ms;
         St.Seen         := True;
      end if;

      --  shield.py:293  the corroboration run.  Advanced HERE, not in Decide,
      --  so that Decide stays a pure function of (state, inputs).
      --  Saturating at Dwell_Ms, unlike Python's unbounded int.  A
      --  REFINEMENT, not a divergence: Decide only ever evaluates
      --  Diff_Run + 1 >= Dwell_Ms, so any value at or above Dwell_Ms - 1 is
      --  observationally identical, and saturation is what makes Dwell_Count
      --  a fixed-width type with no overflow VC.  gs/verify.py models the
      --  unbounded Python form, which is the stronger of the two.
      if Diff_Ok then
         if St.Diff_Run < Dwell_Ms then
            St.Diff_Run := St.Diff_Run + 1;
         end if;
      else
         St.Diff_Run := 0;
      end if;
      pragma Assert (if Excursion then St.Last_Seen_Ms = Old_Watermark);
      --  P2a, discharged locally so the prover does not have to rediscover it
      --  from the whole of Commit's postcondition.

      if Reclose_Auth then                                 --  shield.py:228
         St.Latched := False;
      end if;

      if Granted then                                      --  shield.py:230
         --  shield.py:231-233
         --      st.grant_times.append(now_ms)
         --      if len(st.grant_times) > MAX_GRANTS: st.grant_times.pop(0)
         --  The Python list becomes a fixed-size shift register: no
         --  allocation, no unbounded growth, statically bounded loop.
         if St.N_Grants < Max_Grants then
            St.N_Grants := St.N_Grants + 1;
            St.Grant_Times (St.N_Grants) := Now_Ms;
         else
            for I in Grant_Index range 1 .. Max_Grants - 1 loop
               St.Grant_Times (I) := St.Grant_Times (I + 1);
               pragma Loop_Invariant
                 (for all J in 1 .. I =>
                    St.Grant_Times (J) = St.Grant_Times'Loop_Entry (J + 1));
            end loop;
            St.Grant_Times (Max_Grants) := Now_Ms;
         end if;
         --  Ascending order is preserved because Decide refuses a grant on any
         --  clock excursion (Commit's Pre carries this), so Now_Ms is at least
         --  the watermark, which by Valid_State dominates every stored grant.
         pragma Assert (Window_Ascending (St));

         St.Latched := True;                               --  shield.py:234
         St.Vetoes  := 0;                                  --  shield.py:235

      elsif Want_Trip then                                 --  shield.py:236
         if St.Vetoes < Veto_Limit then                    --  shield.py:237
            St.Vetoes := St.Vetoes + 1;                    --  shield.py:238
         end if;
      end if;

      --  Disowning.  Monotone by construction: Mode is only ever assigned a
      --  value at or above its current one, which is invariant I7.
      --  v4: EITHER counter alone disowns the model, but only the MODEL's
      --  counter can produce Restricted -- a clock fault must never withdraw
      --  the AI's adaptive sensitivity (S4, S4b).
      if St.Vetoes >= Veto_Limit
        or else St.Excursions >= Excursion_Limit                --  shield:309
      then
         St.Mode := Baseline_Only;
      elsif St.Vetoes >= Veto_Limit / 2 then               --  shield.py:311
         if St.Mode = Normal then                          --  shield.py:242
            St.Mode := Restricted;                         --  shield.py:243
         end if;
      end if;
   end Commit;

   ---------------------------------------------------------------------------
   --  Composition
   ---------------------------------------------------------------------------

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
   is
      Remote_Ok : constant Boolean :=
        Sample.Remote_Authentic and then Sample.Remote_Fresh;  --  shield:284
      --  shield.py:280  effective_cert = cert_ok and self.st.mode == NORMAL
      --  Evaluated against the PRE-state, before Commit runs.
      Eff_Cert  : constant Boolean := Effective_Cert (St, Cert_Ok);
      Diff_Ok   : constant Boolean :=
        Differential_Ok (Sample.I_Diff, Sample.I_Restraint,    --  shield:281
                         Eff_Cert, Proposal.Req_P0, Proposal.Req_K);
      Inp       : constant Inputs_T :=
        (Time_Ok      => Sample.Time_Quality_Ok,               --  shield:370
         Remote_Ok    => Remote_Ok,
         Local_Ok     => Local_Ok,
         Forward      => Sample.Forward,
         Diff_Ok      => Diff_Ok,
         Reclose_Auth => Reclose_Auth);
      Granted   : Boolean;
      Why       : Reason_T;
   begin
      Decide (St, Sample.T, Inp, Proposal.Want_Trip, Granted, Why);  --  :287
      --  Note what is NOT passed: Reinstate.  Step is the model's only path
      --  into the shield, so the model has no way to rearm it (S7).
      Commit (St, Sample.T, Granted, Proposal.Want_Trip, Reclose_Auth,
              Reinstate => False, Diff_Ok => Diff_Ok);              --  :288

      --  shield.py:293-297.  The baseline output is OR-ed at the very end and
      --  was never routed through Decide, so nothing above can inhibit it.
      if Baseline_Trip then
         Trip   := True;
         Source := Src_Baseline;
         Reason := Why;
         --  NOTE: gs/shield.py returns the literal string
         --  "baseline-protection" here and discards the shield's own reason.
         --  Keeping Why is a strict improvement for the sequence-of-events
         --  recorder and changes no trip decision; it is the ONE place where
         --  this body is not textually identical to the Python mirror.
      elsif Granted then
         Trip   := True;
         Source := Src_Ai_Shield;
         Reason := Why;
      else
         Trip   := False;
         Source := Src_None;
         Reason := Why;
      end if;
   end Step;

end Shield;
