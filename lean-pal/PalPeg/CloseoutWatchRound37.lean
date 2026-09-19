import PalPeg.CloseoutWatchRound33
import PalPeg.CloseoutWatchRound34
import PalPeg.CloseoutWatchRound31

/-!
# Closeout watch round 37 — feeding the landing-dependent data to the tail

Round 33 corrected `ShiftRoundData` to `ShiftRoundDataL` (pre-compare `w`,
post-compare `w'`, `Internal w w'`, `h := periodLength w'`) and derived its
producer `shiftRoundAtCL_of_tick` from pieces 3–6.  This round connects it to
the consumer `CloseoutWatchPhase2.ShiftTailC` and re-runs Round 34's two
producers for the `L` pieces.

**Field-by-field check of the consumer (the one obstruction).**  `ShiftTailC`
binds ONE `w` with `s1.chain = .watch w`, `zero w.lag = true`,
`beginShiftVM h w (afterMismatch …)` (which says `vs.chain = .watch w`) and
`ChainShiftRun … (immediate w) …`; `roundsRouteLP_of_tail` hands exactly that
`w` to `GalilFoundLandingL.foundRouteMC_shift_Inv`, and `Rounds.next`
(`GalilScaffoldTopRounds`) has the same single-`w` shape.  So the `L` data
feeds the tail **only when `w' = w`**, i.e. when the compare's chain tick is
`Internal.idle`.  In the `take` case (`w' = caught w`, positive pre-compare
lag) no `ShiftTailC` witness exists, and this is not a weakness of the proof
below: the downstream `Rounds` layer itself cannot represent that compare.
Hence `shiftRoundData_of_dataL` converts under the lag-zero premise at the
landing, and the route theorem takes it as the NAMED hypothesis
`MismatchLandingLagZeroC` (Round 32's `ShiftLagZeroC`, restricted to the
live clock-`1` mismatch-shift landings; Round 33's refutation of the global
form does not apply to this restriction, but the model does not exclude such
landings either — see Round 33's header).

**Round 34's producers, ported.**  `ShiftRoundInvCL` / `ShiftOriginRestCL`
restate `ShiftRoundInvC` / `ShiftOriginRestC` at the post-compare `w'` with
`h := periodLength w'`; `ShiftBreakOracleC` / `ShiftBreakFitC` are reused
for every `h` (the shift amount is chosen at the landing).

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace PalPeg.CloseoutWatchRound37

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.CloseoutContracts
open PalPeg.GalilRunSkeleton PalPeg.GalilInvPlus PalPeg.GalilInvPlus2
open PalPeg.GalilFoundStage PalPeg.GalilTraceCost
open PalPeg.GalilInvPlus3 (InvLPS)
open PalPeg.CloseoutWatchRun (LiveScanWatch roundFuel watchSeg_append)
open PalPeg.CloseoutWatchPhase2 (ShiftTailC)
open PalPeg.CloseoutWatchRound2 (FoundCompareCtxC)
open PalPeg.CloseoutWatchRound3 (DistanceNonnegC)
open PalPeg.CloseoutWatchRound5 (PrepLandingLiveC)
open PalPeg.CloseoutWatchRound6 (RightCanC RightSaneC StartLeC LedgerOriginC PeriodMatchC)
open PalPeg.CloseoutWatchRound4 (ZeroLagAtMatchC)
open PalPeg.CloseoutWatchRound7 (PrepLandingWatchC ShiftReachC ShiftRoundAtC BreakTermData
  ShiftRoundData)
open PalPeg.CloseoutWatchRound10 (FoundDpAtC)
open PalPeg.CloseoutPrepInputs2 (MismatchExitG)
open PalPeg.CloseoutPrepInputs3 (PrepInputsG3)
open PalPeg.CloseoutWatchRound23 (MismatchGuardFails TerminalRunMismatchShiftC)
open PalPeg.CloseoutWatchRound25 (MismatchShiftRouteC)
open PalPeg.CloseoutWatchRound27 (guard_of_mismatchShift)
open PalPeg.CloseoutWatchRound30 (ShiftCopyIdleC MismatchClassifierTieC not_matched_of_compare)

open PalPeg.CloseoutWatchRound2 (TerminalC' terminalC'_of_align)
open PalPeg.CloseoutWatchRound18 (ExitSplit3C)
open PalPeg.CloseoutWatchRound23 (ExitSplit4C exitSplit4C_of_tick terminalRunFallbackC_of_G)
open PalPeg.CloseoutWatchRound20 (watchPrefixC_of_unique)
open PalPeg.CloseoutPrepInputs3 (foundExit_of_compare3)
open PalPeg.CloseoutWatchRound31 (FoundExitLPS FallbackReachS foundExit_compare_final9S')
open PalPeg.CloseoutWatchRound33 (ShiftRoundDataL ShiftRoundAtCL' ShiftRunCL ShiftOriginCL
  ShiftBreakRunCL shiftRoundAtCL_of_tick)
open PalPeg.CloseoutWatchRound34 (postShift ShiftBreakOracleC ShiftBreakFitC
  rounds_construct_break refresh_frame_exists' read_center_of_roundInv roundInv_postShift_watch)

/-! ## 1. The data, back to the single-`w` form under lag zero -/

/-- **`ShiftRoundDataL` collapses to `ShiftRoundData` when the pre-compare lag
is zero**: the `Internal` step is then `idle`, so `w' = w`. -/
theorem shiftRoundData_of_dataL (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h lower : ℕ) (sF : GalilVM) (vq : SearchVM)
    (c1 : Control) (s1 : GalilVM)
    (hz0 : ∀ w : GalilScaffoldChainWatch.State, s1.chain = ChainVM.watch w → zero w.lag = true)
    (hd : ShiftRoundDataL centre place entry qq first raw m h lower sF vq c1 s1) :
    ShiftRoundData centre place entry qq first raw m h lower sF vq c1 s1 := by
  obtain ⟨w, w', vs, vq', s2', t', v, cycle, o, org, mm, c', s', n, c3, s3, w3, vs3, vq3, o3, w3',
    hm1, hr1, hc1, hw, hint', hvs, hz, hav, hcmp, hmis, hq', hg, hb, hs2', hi2, hchain, ho, hint,
    he, hoc, ha, hpos11, hlow, hrounds, hseg3, hm3, hr3, hc3, hs3, hav3, hcmp3, hmt3, hq3, ho3,
    hbroken, hmargin, hlast, hlag3, hbound⟩ := hd
  have hzw : zero w.lag = true := hz0 w hw
  cases hint' with
  | idle _ =>
    exact ⟨w, vs, vq', s2', t', v, cycle, o, org, mm, c', s', n, c3, s3, w3, vs3, vq3, o3, w3',
      hm1, hr1, hc1, hw, hzw, hav, hcmp, hmis, hq', hg, hb, hs2', hi2, hchain, ho, hint, he, hoc,
      ha, hpos11, hlow, hrounds, hseg3, hm3, hr3, hc3, hs3, hav3, hcmp3, hmt3, hq3, ho3, hbroken,
      hmargin, hlast, hlag3, hbound⟩
  | take hp _ =>
    rw [positive_of_zero hzw] at hp
    exact Bool.noConfusion hp

/-- **NAMED (open) — lag zero at the mismatch-shift landing.**  At a live
clock-`1` landing with an available outer mismatch and a passing classifier,
the watching chain's lag is zero.  This is `CloseoutWatchRound32.ShiftLagZeroC`
restricted to those landings; the restriction is exactly what the single-`w`
consumer (`ShiftTailC`, `Rounds.next`) forces. -/
def MismatchLandingLagZeroC : Prop :=
  ∀ (c1 : Control) (s1 : GalilVM) (w : GalilScaffoldChainWatch.State),
    LiveScanWatch c1 s1 → c1.clock = 1 → canRight s1.right →
    read (left s1.left) ≠ read (right s1.right) → ¬ MismatchGuardFails s1 →
    s1.chain = ChainVM.watch w → zero w.lag = true

/-! ## 2. The tail from the landing-dependent route -/

/-- The landing-dependent route: `MismatchShiftRouteC` with `h` chosen at the
landing and the conclusion `ShiftRoundDataL`. -/
def MismatchShiftRouteL (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m lower : ℕ) : Prop :=
  ∀ (sF : GalilVM) (vq : SearchVM) (c1 : Control) (s1 : GalilVM),
    LiveScanWatch c1 s1 → c1.clock = 1 → canRight s1.right →
    read (left s1.left) ≠ read (right s1.right) → ¬ MismatchGuardFails s1 →
      ∃ h : ℕ, ShiftRoundDataL centre place entry qq first raw m h lower sF vq c1 s1

/-- **Derived — `MismatchShiftRouteL` from `ShiftRoundAtCL'` and the
classifier bridge** (`CloseoutWatchRound30.mismatchShiftRouteC'_of_shiftRoundAtC'`
with the landing-chosen `h`). -/
theorem mismatchShiftRouteL_of_shiftRoundAtCL' (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m lower : ℕ)
    (hat : ShiftRoundAtCL' centre place entry qq first raw m lower)
    (htie : MismatchClassifierTieC (PofC centre place entry raw) qq first) :
    MismatchShiftRouteL centre place entry qq first raw m lower := by
  intro sF vq c1 s1 hlive hclk hav hne hnG
  obtain ⟨⟨vs, hcmp⟩, hnGC⟩ := htie c1 s1 hlive hclk hav hne hnG
  have hmis := not_matched_of_compare hcmp hne
  have hgt := guard_of_mismatchShift hnGC hcmp hne
  exact hat sF vq c1 s1 vs hlive hclk hav hcmp hmis (fun vq' => (hgt vq').1)

/-- **`ShiftTailC` from the landing-dependent data**
(`CloseoutWatchRound25.mismatchShift_to_shiftRoute` with `MismatchShiftRouteC`
replaced by `MismatchShiftRouteL` + `MismatchLandingLagZeroC`).  The tail's
existential `h` is the landing's; its single `w` is the pre-compare watch,
legitimate by `shiftRoundData_of_dataL`. -/
theorem shiftTailC_of_dataL (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h lower span : ℕ) {c0 cP : Control} {r sP : GalilVM}
    (hdp : PalPeg.CloseoutWatchRound5.FoundDpShiftC centre place entry qq first raw lower span
      c0 r)
    (hroute : MismatchShiftRouteL centre place entry qq first raw m lower)
    (hlag0 : MismatchLandingLagZeroC)
    (hctx : FoundCompareCtxC centre place entry qq first raw c0 r cP sP)
    (hrun : TerminalRunMismatchShiftC (PofC centre place entry raw) qq first h cP sP) :
    ShiftTailC centre place entry qq first raw m c0 r cP sP := by
  obtain ⟨es0, cF, sF, vq, ch, oF, a, ls, rs, qw, gap, hraw, hseg0, hmF, hrF, hcF, havF,
    hidle, hCen, hq, hfound, hmt, hch, hchne, hoF, hcPeq, hsPeq⟩ := hctx
  obtain ⟨hres, hpc⟩ := hdp a ls rs qw gap es0 cF sF vq hseg0 hCen hq hfound
  refine ⟨a, ls, rs, qw, gap, es0, cF, sF, vq, ch, oF, lower, span, hraw, hseg0, hmF, hrF, hcF,
    havF, hidle, hCen, hq, hfound, hmt, hch, hchne, hoF, hcPeq, hsPeq, hres, hpc, ?_⟩
  intro es c2 s2 hseg hwLanding
  obtain ⟨hmL, hrL, hcL⟩ := watchSegE_live_control (delay := 2048) (by omega) hseg
    (by rw [hcPeq]; exact hmF) (by rw [hcPeq]) (by simp [hcPeq])
  obtain ⟨cT, sT, hsegT, hLT, c1, s1, hseg1, hclk, hlive1, hav1, hne1, hnG⟩ :=
    hrun es c2 s2 hseg ⟨hmL, hrL, hcL, hwLanding⟩
  obtain ⟨h1, hdL⟩ := hroute sF vq c1 s1 hlive1 hclk hav1 hne1 hnG
  have hd := shiftRoundData_of_dataL centre place entry qq first raw m h1 lower sF vq c1 s1
    (fun w hw => hlag0 c1 s1 w hlive1 hclk hav1 hne1 hnG hw) hdL
  obtain ⟨w, vs, vq', s2', t', v, cycle, o, org, mm, c', s', n, c3, s3, w3, vs3, vq3, o3, w3',
    hm1, hr1, hc1, hs1, hz, hav, hcmp, hmis, hq', hg, hb, hs2', hi2, hchain, ho, hint, he,
    hoc, ha, hpos11, hlow, hrounds, hseg3, hm3, hr3, hc3, hs3, hav3, hcmp3, hmt3, hq3, ho3,
    hbroken, hmargin, hlast, hlag, hbound⟩ := hd
  exact ⟨c1, s1, h1, w, vs, vq', s2', t', v, cycle, o, org, mm, c', s', n, c3, s3, w3, vs3, vq3,
    o3, w3', watchSeg_append hsegT hseg1, hm1, hr1, hc1, hs1, hz, hav, hcmp, hmis, hq', hg, hb,
    hs2', hi2, hchain, ho, hint, he, hoc, ha, hpos11, hlow, hrounds, hseg3, hm3, hr3, hc3, hs3,
    hav3, hcmp3, hmt3, hq3, ho3, hbroken, hmargin, hlast, hlag, hbound⟩

/-! ## 3. Round 34's producers for the `L` pieces -/

/-- **NAMED (open) — `ShiftRoundInvC` at the post-compare watch**, with
`h := periodLength w'`. -/
def ShiftRoundInvCL (raw : List (Fin 2)) : Prop :=
  ∀ (c1 : Control) (s1 : GalilVM) (vs : ScanVM) (vq' : SearchVM)
    (w w' : GalilScaffoldChainWatch.State) (s2' : GalilVM) (t' : ShiftState)
    (v : GalilScaffoldChainWatch.State) (cycle : Counter) (o : Bool),
    LiveScanWatch c1 s1 → c1.clock = 1 → s1.chain = ChainVM.watch w →
    GalilScaffoldChainWatch.Internal w w' →
    beginShiftVM (periodLength w') w' (afterMismatch s1 vs vq') s2' →
    ChainShiftRun ⟨s1.center, left s1.left, ofNat (periodLength w'), inc s1.radius,
        inc (inc s1.length)⟩
      (GalilScaffoldChainWatch.immediate w') reset (periodLength w') t' v cycle →
    RoundInv (periodLength w') raw {c1 with mode := .scan, clock := 2048, output := o}
      (postShift s2' t' v cycle)

/-- **NAMED (open) — `ShiftOriginRestC` at the post-compare watch**, with
`h := periodLength w'`. -/
def ShiftOriginRestCL (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (lower : ℕ) : Prop :=
  ∀ (sF : GalilVM) (vq : SearchVM) (c1 : Control) (s1 : GalilVM) (vs : ScanVM)
    (vq' : SearchVM) (w w' : GalilScaffoldChainWatch.State) (s2' : GalilVM)
    (t' : ShiftState) (v : GalilScaffoldChainWatch.State) (cycle : Counter)
    (org : ReadOrigin raw),
    LiveScanWatch c1 s1 → c1.clock = 1 → s1.chain = ChainVM.watch w →
    GalilScaffoldChainWatch.Internal w w' →
    beginShiftVM (periodLength w') w' (afterMismatch s1 vs vq') s2' →
    ChainShiftRun ⟨s1.center, left s1.left, ofNat (periodLength w'), inc s1.radius,
        inc (inc s1.length)⟩
      (GalilScaffoldChainWatch.immediate w') reset (periodLength w') t' v cycle →
    org.interior.length + 1 = periodLength w' →
    Entry raw org (toOnly (postShift s2' t' v cycle) v) →
      org.center = position sF.center ∧
      PalPeg.GalilRadiusConsumed.Aligned org ∧
      (GalilScaffoldProgram.denote vq.dp.config).pos 11 = periodLength w' ∧
      (∀ δ, 0 < δ → δ ≤ lower → ¬ HasPeriod (Span raw org.center org.radius) (2*δ))

/-- **Derived — `ShiftBreakRunCL`** (`CloseoutWatchRound34.shiftBreakRunC_of_tail`
at `w'`, `h := periodLength w'`; oracle and fit for every `h`). -/
theorem shiftBreakRunCL_of_tail (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ) (μ : ℕ → Control → GalilVM → ℕ)
    (hinv : ShiftRoundInvCL raw)
    (horacle : ∀ h, ShiftBreakOracleC centre place entry qq first raw h (μ h))
    (hfit : ∀ h, ShiftBreakFitC centre place entry qq first raw m h) :
    ShiftBreakRunCL centre place entry qq first raw m := by
  intro c1 s1 vs vq' w w' s2' t' v cycle o hL hclk hw hint' hs2' hchain ho
  have hI := hinv c1 s1 vs vq' w w' s2' t' v cycle o hL hclk hw hint' hs2' hchain
  obtain ⟨org, hint, hzv, he⟩ := roundInv_postShift_watch hI
  have horacle' : ∀ c s, RoundInv (periodLength w') raw c s →
      BreakEnd (PofC centre place entry raw) qq first 2048 c s ∨
      ∃ (c' : Control) (s' : GalilVM),
        Rounds (PofC centre place entry raw) qq first 2048 (periodLength w') 1 c s c' s' ∧
        RoundInv (periodLength w') raw c' s' ∧ μ (periodLength w') c' s' < μ (periodLength w') c s := by
    intro c0 s0 h0
    rcases horacle (periodLength w') c0 s0 h0 with hend | ⟨c', s', hstep, hlt⟩
    · exact Or.inl hend
    · exact Or.inr ⟨c', s', hstep,
        roundInv_preserved (PofC centre place entry raw) qq first 2048 (periodLength w') raw
          hstep h0, hlt⟩
  obtain ⟨mm, c', s', hrounds, hI', hend⟩ :=
    rounds_construct_break (PofC centre place entry raw) qq first 2048 (periodLength w')
      (RoundInv (periodLength w') raw) (μ (periodLength w')) horacle' _ _ hI
  obtain ⟨n, c3, s3, hseg3, hm3, hr3, hc3, w3, hs3, hav3, vs3, vq3, hcmp3, hmt3, hq3, hsp3,
    w3', hbr3⟩ := hend
  obtain ⟨o3, ho3⟩ := refresh_frame_exists' (PofC centre place entry raw) qq first
    (afterCompare s3 vs3 vq3) c3.output
  have hp0 : (postShift s2' t' v cycle).periodOnly = true := by
    show s2'.periodOnly = true
    rw [hs2'.2]
  have hs0 : (postShift s2' t' v cycle).chain = ChainVM.watch v := rfl
  obtain ⟨-, -, hbroken, hres⟩ :=
    rounds_break (PofC centre place entry raw) qq first 2048 (periodLength w') hrounds v hp0 hs0
      hzv hseg3 hm3 hr3 hc3 w3 hs3 hav3 vs3 vq3 hcmp3 hmt3 hq3 hsp3 w3' hbr3 o3 ho3
  have hall := hres raw org hint he (read_center_of_roundInv hI')
  obtain ⟨-, -, hmargin, hlast, hlag, -, -, -, -, -⟩ := hall
  have hbound := hfit (periodLength w') _ _ mm c' s' n c3 s3 vs3 vq3 hI hrounds hseg3 hav3
    hcmp3 hmt3
  exact ⟨mm, c', s', n, c3, s3, w3, vs3, vq3, o3, w3', hrounds, hseg3, hm3, hr3, hc3, hs3, hav3,
    hcmp3, hmt3, hq3, ho3, hbroken, hmargin, hlast, hlag, hbound⟩

/-- **Derived — `ShiftOriginCL`** (`CloseoutWatchRound34.shiftOriginC_of_ctx`
at `w'`). -/
theorem shiftOriginCL_of_ctx (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (lower : ℕ)
    (hinv : ShiftRoundInvCL raw)
    (hrest : ShiftOriginRestCL centre place entry qq first raw lower) :
    ShiftOriginCL centre place entry qq first raw lower := by
  intro sF vq c1 s1 vs vq' w w' s2' t' v cycle hL hclk hw hint' hs2' hchain
  have hI := hinv c1 s1 vs vq' w w' s2' t' v cycle c1.output hL hclk hw hint' hs2' hchain
  obtain ⟨org, hint, -, he⟩ := roundInv_postShift_watch hI
  obtain ⟨hoc, ha, hpos11, hlow⟩ :=
    hrest sF vq c1 s1 vs vq' w w' s2' t' v cycle org hL hclk hw hint' hs2' hchain hint he
  exact ⟨org, hint, he, hoc, ha, hpos11, hlow⟩

/-! ## 4. The route from the tick, and `foundExit_compare_final15` -/

/-- **Derived — the landing-dependent route from the tick and the `L` pieces.** -/
theorem mismatchShiftRouteL_of_tick (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m lower : ℕ) (μ : ℕ → Control → GalilVM → ℕ)
    (h3 : ShiftCopyIdleC) (h4 : ShiftRunCL)
    (hinv : ShiftRoundInvCL raw)
    (horacle : ∀ h, ShiftBreakOracleC centre place entry qq first raw h (μ h))
    (hfit : ∀ h, ShiftBreakFitC centre place entry qq first raw m h)
    (hrest : ShiftOriginRestCL centre place entry qq first raw lower)
    (htie : MismatchClassifierTieC (PofC centre place entry raw) qq first) :
    MismatchShiftRouteL centre place entry qq first raw m lower :=
  mismatchShiftRouteL_of_shiftRoundAtCL' centre place entry qq first raw m lower
    (shiftRoundAtCL_of_tick centre place entry qq first raw m lower h3 h4
      (shiftOriginCL_of_ctx centre place entry qq first raw lower hinv hrest)
      (shiftBreakRunCL_of_tail centre place entry qq first raw m μ hinv horacle hfit))
    htie

/-- **`foundExit_compare_final14` with `MismatchShiftRouteC` replaced by the
`L` pieces' hypotheses**: `ShiftCopyIdleC`, `ShiftRunCL`, `ShiftRoundInvCL`,
`ShiftBreakOracleC` (every `h`), `ShiftBreakFitC` (every `h`),
`ShiftOriginRestCL`, `MismatchClassifierTieC`, and the landing lag
`MismatchLandingLagZeroC`.  Family 4 goes through `shiftTailC_of_dataL`. -/
theorem foundExit_compare_final15 (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (m h lower span : ℕ) (μ : ℕ → Control → GalilVM → ℕ)
    (hP : Decodes (PofC centre place entry w))
    (hex : ∀ s, (PofC centre place entry w).replayExhausted s = zero s.replay)
    (hready : PalPeg.GalilReplayChainSeg.ChainTickable)
    (hcan : RightCanC) (hsane : RightSaneC) (hstart : StartLeC)
    (hor : LedgerOriginC centre place entry q first 2048 w)
    (hzl : ZeroLagAtMatchC) (hnn : DistanceNonnegC) (hpm : PeriodMatchC)
    {c c' cP : Control} {r t sP : GalilVM}
    (hE : StageEntryC (PofC centre place entry w) q first w c r)
    (hsW : SegReachedW centre place entry q first w c r c' t)
    (a : Fin 2) (ls rs qw : List (Fin 2)) (gap : Bool)
    (hprep : PrepInputsG3 (PofC centre place entry w) q first ⟨a :: ls, gap⟩ lower span cP sP)
    (hmis : MismatchExitG (PofC centre place entry w) q first w m c r cP sP)
    (hctx : FoundCompareCtxC centre place entry q first w c r cP sP)
    (hfbS : FallbackReachS (PofC centre place entry w) q first w m c r cP sP)
    (hstage : ReplayStage w (PofC centre place entry w) q first c r)
    (hmP : cP.mode = .scan) (hrP : cP.replaying = false) (hcP : 1 ≤ cP.clock)
    (hreachWatch : ∃ (es : List Bool) (c2 : Control) (s2 : GalilVM),
      WatchSegE (PofC centre place entry w) q first 2048 es cP sP c2 s2 ∧
        PalPeg.CloseoutWatchRun.LiveScanWatch c2 s2)
    (hat : FoundDpAtC centre place entry q first w lower span h c r)
    (hreach : ShiftReachC centre place entry q first w h)
    (hround : ShiftRoundAtC centre place entry q first w m h lower)
    (h3 : ShiftCopyIdleC) (h4 : ShiftRunCL)
    (hinv : ShiftRoundInvCL w)
    (horacle : ∀ h', ShiftBreakOracleC centre place entry q first w h' (μ h'))
    (hfit : ∀ h', ShiftBreakFitC centre place entry q first w m h')
    (hrest : ShiftOriginRestCL centre place entry q first w lower)
    (htie : MismatchClassifierTieC (PofC centre place entry w) q first)
    (hlag0 : MismatchLandingLagZeroC)
    (hland : ∀ sF : GalilVM,
      PalPeg.CloseoutWatchRound5.BreakLandingC centre place entry q first w h sF cP sP)
    (hstepBreak : ∀ (c0 : Control) (s0 : GalilVM), LiveScanWatch c0 s0 →
      PalPeg.CloseoutWatchRun.RoundStepC (PofC centre place entry w) q first (roundFuel h)
        (BreakTermData centre place entry q first w m h) c0 s0) :
    FoundExitLPS (PofC centre place entry w) q first w m c r := by
  classical
  have hrouteL := mismatchShiftRouteL_of_tick centre place entry q first w m lower μ h3 h4 hinv
    horacle hfit hrest htie
  have hsplit4 : ExitSplit4C centre place entry q first w h cP sP :=
    exitSplit4C_of_tick centre place entry q first w h cP sP
      (PalPeg.CloseoutWatchRound2.chain_ne_idle_of_foundCompareCtx hctx)
      (watchPrefixC_of_unique _ _ _ _ _)
  have hstp := PalPeg.CloseoutWatchRound6.lagStepC_of_parts hcan hsane hstart
  have hre := PalPeg.CloseoutWatchRound6.ledgerReachC_of_origin centre place entry q first 2048 w
    hstp hor
  have hled := PalPeg.CloseoutWatchRound4.watchLedgerC_of_reach hstp hre
  have hcaught := PalPeg.CloseoutWatchRound4.caughtAtMatchC_of_zeroLag hled hzl
  have hpred := PalPeg.CloseoutWatchRound6.predictC_of_match hled hzl hpm
  have havail := PalPeg.CloseoutWatchRound6.landingCanRightC_of_reach hstp hre
  have hT : TerminalC' centre place entry q first w h c r cP sP :=
    terminalC'_of_align centre place entry q first w h hready
      (PalPeg.CloseoutWatchRound3.matchTickC_of_parts hled hcaught hpred)
      (PalPeg.CloseoutWatchRound3.landingReadyC_of_parts hled havail hnn) hctx
  have via3 : ∀ (hs3 : ExitSplit3C centre place entry q first w h cP sP),
      FoundExitLPS (PofC centre place entry w) q first w m c r := fun hs3 =>
    foundExit_compare_final9S' (h := h) (fun hsplit =>
      PalPeg.CloseoutWatchRound15.foundExit_compare_final8 centre place entry q first w m h
        lower span hP hex hready hcan hsane hstart hor hzl hnn hpm hE hsW a ls rs qw gap hprep
        hmis hctx hsplit hstage hmP hrP hcP hat hreach hround hland hstepBreak)
      hT.2 hs3 hfbS (PalPeg.CloseoutWatchRound2.chain_ne_idle_of_foundCompareCtx hctx)
      hreachWatch
  rcases hsplit4 hT.2 with hs | hb | hf | hm
  · exact via3 (fun _ => Or.inl hs)
  · exact via3 (fun _ => Or.inr (Or.inl hb))
  · exact via3 (fun _ => Or.inr (Or.inr (terminalRunFallbackC_of_G hf)))
  · have htail : ShiftTailC centre place entry q first w m c r cP sP :=
      shiftTailC_of_dataL centre place entry q first w m h lower span
        (PalPeg.CloseoutWatchRound10.foundDpShiftC_of_at centre place entry q first w hP
          lower span h hstage hat)
        hrouteL hlag0 hctx hm
    have hroute := PalPeg.CloseoutWatchRound15.roundsRouteLP_of_tail centre place entry q first
      w m hex hE htail
    exact .exit (foundExit_of_compare3 centre place entry q first w m hP hE hsW a ls rs qw gap
      hprep hmis (Or.inl (PalPeg.CloseoutWatchPhase.roundsExit_of_LP hroute)))

end PalPeg.CloseoutWatchRound37

#print axioms PalPeg.CloseoutWatchRound37.shiftRoundData_of_dataL
#print axioms PalPeg.CloseoutWatchRound37.mismatchShiftRouteL_of_shiftRoundAtCL'
#print axioms PalPeg.CloseoutWatchRound37.shiftTailC_of_dataL
#print axioms PalPeg.CloseoutWatchRound37.shiftBreakRunCL_of_tail
#print axioms PalPeg.CloseoutWatchRound37.shiftOriginCL_of_ctx
#print axioms PalPeg.CloseoutWatchRound37.mismatchShiftRouteL_of_tick
#print axioms PalPeg.CloseoutWatchRound37.foundExit_compare_final15
