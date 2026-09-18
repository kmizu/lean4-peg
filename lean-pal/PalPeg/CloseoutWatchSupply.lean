import PalPeg.CloseoutChainPack
import PalPeg.CloseoutShiftS2
import PalPeg.CloseoutTrailS2

/-!
# `WatchShiftS` with no `ConsumeAvail`

`CloseoutPackRun41.watchShiftS_of_chainPosInv2` uses its `ConsumeAvail`
hypothesis at exactly one place — `chainPos_step P.chainPos hav hstep` — and
`CloseoutPackRun48.chainPos_step_of_supply` is precisely that step with the
`ConsumeAvail` replaced by the four local supply facts (`Represents` and
presence of the right head, the verifier pair, `LagCan`), all of which are
`ChainPack` fields.

So `hav` never has to be assumed: it is the same data as `ChainPack`.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchSupply

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilFrontMono PalPeg.GalilChainCoupling
open PalPeg.CloseoutLPack5 PalPeg.CloseoutPackRun6 PalPeg.CloseoutPackRun10
open PalPeg.CloseoutRadPack2 PalPeg.CloseoutRadPack4
open PalPeg.CloseoutPackRun26 PalPeg.CloseoutPackRun30 PalPeg.CloseoutPackRun32
open PalPeg.CloseoutPackRun34 PalPeg.CloseoutPackRun38 PalPeg.CloseoutPackRun40
open PalPeg.GalilBranchInvariants
open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilFrontMono PalPeg.GalilChainCoupling
open PalPeg.CloseoutLPack5 PalPeg.CloseoutPackRun6 PalPeg.CloseoutPackRun10
open PalPeg.CloseoutRadPack2 PalPeg.CloseoutRadPack4
open PalPeg.CloseoutPackRun26 PalPeg.CloseoutPackRun30 PalPeg.CloseoutPackRun32
open PalPeg.CloseoutPackRun26 PalPeg.CloseoutPackRun34 PalPeg.CloseoutFrontExtra
open PalPeg.CloseoutLPack PalPeg.CloseoutPackRun10 PalPeg.CloseoutPackRun30
open PalPeg.CloseoutLPack5 PalPeg.CloseoutLPack6 PalPeg.CloseoutPackRun12
open PalPeg.GalilTrailSane PalPeg.GalilChainCoupling PalPeg.GalilBranchInvariants
open PalPeg.CloseoutPackRun11 PalPeg.CloseoutPackRun9 PalPeg.CloseoutPackRun8
open PalPeg.GalilTrailChain PalPeg.GalilFinalAssembly PalPeg.GalilThrottledRun
open PalPeg.CloseoutRadPack PalPeg.CloseoutRadPack2 PalPeg.CloseoutRadPack3 PalPeg.CloseoutRadPack4
open PalPeg.GalilTrailRad PalPeg.GalilTrailProof PalPeg.GalilTrailAssembly
open PalPeg.GalilTrailScan PalPeg.GalilTrailBudget PalPeg.GalilTrailFront
open PalPeg.CloseoutPackRun41 PalPeg.CloseoutPackRun44 PalPeg.CloseoutPackRun47
open PalPeg.CloseoutPackRun48 PalPeg.CloseoutChainPack PalPeg.CloseoutVerRep
open PalPeg.CloseoutShiftS2 PalPeg.CloseoutTrailS2 PalPeg.CloseoutOracleW
open PalPeg.CloseoutShiftS PalPeg.CloseoutCheckW PalPeg.GalilLookRefined

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

theorem watchShiftS_of_supply {w : List (Fin 2)} {x : State GalilVM}
    (h : ChainPositionInvariantWithShiftPhase w x.ctl x.vm)
    (hrepR : GalilScaffoldInputTrace.Represents x.vm.right.head w)
    (hfocR : x.vm.right.head.focus ≠ none)
    (hrepV : ∀ wch : GalilScaffoldChainWatch.State, x.vm.chain = .watch wch →
      GalilScaffoldInputTrace.Represents wch.machine.verifier.head w ∧
        wch.machine.verifier.head.focus ≠ none)
    (hL : PalPeg.CloseoutPackRun48.LagCan x.vm.chain) :
    WatchShiftS centre place entry q first w x := by
  intro hs hni s'' hcmp hmt hg wch hch
  have hs' : ScanNR ⟨x.ctl, x.vm⟩ := hs
  have P := h.payload hs' hni
  -- the chain of the (unmatched) target is one plain `ChainStep` away
  have hstep : ChainStep x.vm.chain s''.chain := by
    obtain ⟨vs, vq, a, -, -, hiff, -, hchn, hteq⟩ :
      compareFound (PofC centre place entry w) q first x.vm s'' := hcmp
    have ha : a = false := by
      cases a with
      | false => rfl
      | true =>
        rw [if_pos rfl] at hteq
        subst hteq
        refine absurd ?_ hmt
        show GalilScaffoldInputHead.read (afterBirth _ (afterCompare x.vm vs vq)).left
          = GalilScaffoldInputHead.read (afterBirth _ (afterCompare x.vm vs vq)).right
        rw [afterBirth_left, afterBirth_right]
        exact hiff.1 rfl
    subst ha
    have hcn : s''.chain = vs.chain := by rw [hteq, afterBirth_chain]; rfl
    rw [hcn]
    rcases hchn with ⟨-, ht⟩ | ⟨hi, -⟩ | ⟨hi, -⟩
    · obtain ⟨y, hst, ho⟩ := ht
      simp only [Bool.false_eq_true, ↓reduceIte] at ho
      rw [ho]
      exact hst
    · exact absurd hi hni
    · exact absurd hi hni
  have hver := (PalPeg.CloseoutPackRun48.chainPos_step_of_supply hrepR hfocR P.canR
    hrepV hL P.chainPos hstep).watch wch hch
  -- the two numeric halves, exactly as in Run40
  obtain ⟨-, -, -, -, hmis⟩ :=
    compare'_inv (onLetterVM w) leftFirstVM centre place entry q first h.coupled hs.1 hcmp
  obtain ⟨-, -, hsum, hwk⟩ := hmis hmt
  have hg' := hg
  obtain ⟨w1, hw1, hz, hph, hbr, -, -⟩ := hg'
  have hch' := hch
  rw [hw1] at hch'
  injection hch' with hwe
  rw [hwe] at hw1 hz hph hbr
  rw [hw1] at hsum hwk
  have hd : value wch.machine.control.distance + value wch.lag = value x.vm.radius := hsum hbr
  rw [value_zero_of_zero hz] at hd
  refine ⟨P.canR, ?_, ?_, hver.1, hver.2.1⟩
  · rcases hwk wch rfl hbr with ⟨-, hf⟩ | hO
    · exact four_of_freshC hph hf
    · exact four_of_other' centre place entry q first h.coupled hs hcmp hmt hg hch hO
  · intro rad hsc
    have := P.radLe rad hsc
    omega


/-- **`ShiftLocalS` from `ChainPack` alone.**  No `ConsumeAvail`. -/
theorem shiftLocalS_of_chainPack {w : List (Fin 2)} {x : State GalilVM}
    (hp : ChainPack q first w x.ctl x.vm) :
    PalPeg.CloseoutPackRun34.ShiftLocalS centre place entry q first w x := by
  by_cases hi : x.vm.chain = ChainVM.idle
  · exact PalPeg.CloseoutPackRun34.shiftLocalS_of_chainIdle centre place entry q first hi
  · refine
      { move := fun hs => ?_, guard := fun hs => ?_, coupled := fun hs => ?_,
        ver := fun hs => ?_ } <;>
    · obtain ⟨hrr, hfr⟩ := hp.repR hs.1
      exact (PalPeg.CloseoutPackRun34.shiftLocalS_of_watchShiftS centre place entry q first hi
        (watchShiftS_of_supply centre place entry q first hp.inv hrr hfr
          (hp.repV hs.1) (hp.lagCan hs.1)) |> fun H => by
        first
          | exact H.move hs | exact H.guard hs | exact H.coupled hs | exact H.ver hs)

theorem shiftLocalS_of_run3 {w : List (Fin 2)}
    (hbg : H_BackgroundLandingChainLedger centre place entry q first w) (hmatch : H_MatchLandingChainLedger centre place entry q first w)
    (hentry : H_ShiftEntryChainLedger centre place entry q first w)
    (hsd : H_ShiftExitRadiusLedger centre place entry q first w)
    {n : ℕ} {x y : State GalilVM} (hx : ChainPositionInvariantWithShiftPhase w x.ctl x.vm)
    (h : Steps (galilFrameS (PofC centre place entry w) q first) 2048 n x y)
    (hp : ∀ (c : Control) (s : GalilVM), ChainPositionInvariantWithShiftPhase w c s → ChainPack q first w c s) :
    ShiftLocalS centre place entry q first w y :=
  PalPeg.CloseoutWatchSupply.shiftLocalS_of_chainPack centre place entry q first
    (hp y.ctl y.vm
      (chainPosInv2_steps centre place entry q first hbg hmatch hentry hsd hx h))


theorem radPack_ptS3 {w : List (Fin 2)} (hw : 0 < w.length) {st : ℕ → State GalilVM}
    {Tc : ℕ → ℕ} (hP : PreTrace centre place entry q first w st Tc)
    (hbg : H_BackgroundLandingChainLedger centre place entry q first w) (hmatch : H_MatchLandingChainLedger centre place entry q first w)
    (hentry : H_ShiftEntryChainLedger centre place entry q first w)
    (hsd : H_ShiftExitRadiusLedger centre place entry q first w)
    (hpos0 : ChainPositionInvariantWithShiftPhase w (st 0).ctl (st 0).vm)
    (hreach : ∀ i, i ≤ Tc w.length →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 i (st 0) (st i))
    (hLP : ∀ i, i ≤ Tc w.length → PalPeg.CloseoutPackRun10.LPackM w (st i).ctl (st i).vm)
    (hll : ∀ i, i ≤ Tc w.length → PalPeg.GalilTrailSane.LeftLive (st i).ctl (st i).vm)
    (hpk : ∀ (c : Control) (s : GalilVM), ChainPositionInvariantWithShiftPhase w c s → ChainPack q first w c s) :
    ∀ i, i ≤ Tc w.length → RadPack (st i).ctl (st i).vm := by
  have hsh : ∀ i, i ≤ Tc w.length → ShiftLocalS centre place entry q first w (st i) := fun i hi =>
    PalPeg.CloseoutWatchSupply.shiftLocalS_of_run3 centre place entry q first hbg hmatch hentry hsd hpos0 (hreach i hi) hpk
  have hen : ∀ i, i ≤ Tc w.length → ScanNR (st i) → ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
      ¬ (galilFrameS (PofC centre place entry w) q first).matched s'' →
      shiftGuardVM s'' → beginShiftVM' s'' t'' → ShiftBud t'' := by
    intro i hi hs s'' t'' hcmp hmt hg hb
    obtain ⟨rad, hscan, hcan, hh⟩ :=
      halfBound_of_shiftLocalS centre place entry q first (hLP i hi) (hsh i hi) hs hcmp hmt hg hb
    exact shiftBud_of_scanInv (onLetterVM w) leftFirstVM centre place entry q first
      hscan hcan hcmp hb hh
  have hsv : ∀ i, i ≤ Tc w.length → ScanNR (st i) → ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
      ¬ (galilFrameS (PofC centre place entry w) q first).matched s'' →
      shiftGuardVM s'' → beginShiftVM' s'' t'' → SaneVer t''.chain := fun i hi hs s'' t'' =>
    saneVer_of_shiftLocalS centre place entry q first (hsh i hi) hs
  have hL := radLedger_pt centre place entry q first hw hP hll
  have hS := shiftOrd_ptS centre place entry q first hw hP hll hen
  have hV := verSane_ptS centre place entry q first hw hP hll hsv
  exact fun i hi => radPack_of_parts (hL i hi) (hS i hi) (hll i hi) (hV i hi)


theorem trailF_ptS3 {w : List (Fin 2)} (hw : 0 < w.length) {st : ℕ → State GalilVM}
    {Tc : ℕ → ℕ} (hP : PreTrace centre place entry q first w st Tc)
    (hbg : H_BackgroundLandingChainLedger centre place entry q first w) (hmatch : H_MatchLandingChainLedger centre place entry q first w)
    (hentry : H_ShiftEntryChainLedger centre place entry q first w)
    (hsd : H_ShiftExitRadiusLedger centre place entry q first w)
    (hpos0 : ChainPositionInvariantWithShiftPhase w (st 0).ctl (st 0).vm)
    (hreach : ∀ i, i ≤ Tc w.length →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 i (st 0) (st i))
    (hLP : ∀ i, i ≤ Tc w.length → PalPeg.CloseoutPackRun10.LPackM w (st i).ctl (st i).vm)
    (hll : ∀ i, i ≤ Tc w.length → PalPeg.GalilTrailSane.LeftLive (st i).ctl (st i).vm)
    (hpk : ∀ (c : Control) (s : GalilVM), ChainPositionInvariantWithShiftPhase w c s → ChainPack q first w c s)
    {m : ℕ} (hm : m < w.length) :
    ∀ i, i ≤ Tc (m+1) → TrailF w m (st i) := by
  have hsane := sanePack_pt centre place entry q first hw hP hll
  have hrad := radPack_ptS3 centre place entry q first hw hP hbg hmatch hentry hsd hpos0
    hreach hLP hll hpk
  have hscan := scanT_pt centre place entry q first hw hP hrad hsane hm
  have hB := chainBudget_pt centre place entry q first hw hP hrad hsane hm
  have hV := verF_trace centre place entry q first hP hm hscan hB
  exact fun i hi => trailF_of_scanT (hscan i hi) (hV i hi).ver (hV i hi).lagPos


theorem needIMW'_le_W3 {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : PalPeg.CloseoutCheckW.PreTraceIMW centre place entry q first w st Tc)
    (hbg : H_BackgroundLandingChainLedger centre place entry q first w) (hmatch : H_MatchLandingChainLedger centre place entry q first w)
    (hentry : H_ShiftEntryChainLedger centre place entry q first w)
    (hsd : H_ShiftExitRadiusLedger centre place entry q first w)
    (hpos0 : ChainPositionInvariantWithShiftPhase w (st 0).ctl (st 0).vm)
    (hpk : ∀ (c : Control) (s : GalilVM), ChainPositionInvariantWithShiftPhase w c s → ChainPack q first w c s) :
    ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) →
      PalPeg.GalilLookRefined.needL' w st i ≤ m + 1 := by
  have hbase := hP.base.pre
  have hreach : ∀ i, i ≤ Tc w.length →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 i (st 0) (st i) := by
    intro i hi
    exact PalPeg.CloseoutPackRun2.steps_of_trace hbase.trace i hi
  have hLP : ∀ i, i ≤ Tc w.length →
      PalPeg.CloseoutPackRun10.LPackM w (st i).ctl (st i).vm :=
    fun i hi => (hP.packs i hi).pack
  have hll : ∀ i, i ≤ Tc w.length →
      PalPeg.GalilTrailSane.LeftLive (st i).ctl (st i).vm :=
    fun i hi => leftLive_of_lpackM (hLP i hi)
  intro m hm i hi
  exact needL'_le_of_trailF w st m i
    (trailF_ptS3 centre place entry q first hw hbase hbg hmatch hentry hsd hpos0
      hreach hLP hll hpk hm i hi)



#print axioms radPack_ptS3
#print axioms trailF_ptS3
#print axioms needIMW'_le_W3
#print axioms shiftLocalS_of_run3
#print axioms watchShiftS_of_supply
#print axioms shiftLocalS_of_chainPack

end

end PalPeg.CloseoutWatchSupply
