import PalPeg.CloseoutFinalBranch
import PalPeg.LocalShadowConcrete
import PalPeg.LocalBlankState
import PalPeg.CloseoutRightBounds
import PalPeg.CanonicalLocalRealizes
import PalPeg.LocalInitStep
import PalPeg.ChainLookBehindRight
import PalPeg.TickUsedLetters
import PalPeg.ReplayStartGhost
import PalPeg.ReportPhase
import PalPeg.GhostSection
import PalPeg.CountersCanonicalTrace
import PalPeg.ParkedRight
import PalPeg.ScanEntrySigns

/-!
# The final theorem from the local system and a physical machine, the trace side discharged

`LocalShadowConcrete.pal_in_peg_of_shadowed_sysC` takes a pre-loaded trace with nine facts about
it.  Here the trace is the canonical pre-loaded trace of `CloseoutFinalBranch`
(`canonicalPreTrace_exists`), and the nine facts are theorems about it.  What remains is stated
over canonical pre-loaded traces: the per-mode obligation of the abstract local system, its
starvation test, its report test, and the specification of the physical machine.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000

namespace PalPeg.ShadowedLocalFinal

variable {spare : ℕ}

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilRunSkeleton (PofC PofC_onLetter PofC_leftFirst)
open PalPeg.GalilFinalAssembly (boot)
open PalPeg.GalilFinalAssembly2 (centreC placeC centrePlaceC sufVM_boot)
open PalPeg.GalilFinalBaseNeed (base_of_preTraceB)
open PalPeg.GalilTruncTick (sharedC_trunc_vm sharedC_suf sufVM_trace)
open PalPeg.GalilLookRefined (needL' needT' needL'_boot needLe_of_pointwise')
open PalPeg.GalilThrottledRun (truncS usedVM)
open PalPeg.CloseoutCheckW (PreTraceIMW CanonTrace)
open PalPeg.BranchSupply (ScanLandingObligationsAlongTrace)
open PalPeg.CloseoutFinalBranch (canonicalPreTrace_exists needBound_alongPreTrace)
open PalPeg.Local (LocalStep)
open PalPeg.LocalTrackingLatch
open PalPeg.LocalReplayParked (absState'' Mirrored1 MirInv1)
open PalPeg.LocalSysConcrete (Steps stepOf tickC sysC sysM absSC feedC Starved Needy TickNeed InvC PhysWF
  Realizes x0C)
open PalPeg.LocalShadowConcrete (pal_in_peg_of_shadowed_sysC OnRun TickSucc)
open PalPeg.LocalBlankState (tapeCount blankVML absState''_blank inv_blank twin_blank wf_blankView
  walkerProper_blank)

/-- The trace held at its last tick: the states of `st` up to `lastTick`, then `st lastTick`
for ever.  A pre-loaded trace says nothing about its states after the last report point; the
local layer reads the trace through an index that is not bounded by its invariant, so it is
given a trace that says something at every index. -/
def heldAfter (lastTick : ℕ) (st : ℕ → State GalilVM) : ℕ → State GalilVM :=
  fun k => st (min k lastTick)

theorem heldAfter_of_le {lastTick k : ℕ} (st : ℕ → State GalilVM) (hk : k ≤ lastTick) :
    heldAfter lastTick st k = st k := by
  unfold heldAfter
  rw [Nat.min_eq_left hk]

theorem heldAfter_afterLast {lastTick k : ℕ} (st : ℕ → State GalilVM) (hk : lastTick ≤ k) :
    heldAfter lastTick st k = heldAfter lastTick st lastTick := by
  unfold heldAfter
  rw [Nat.min_eq_right hk, Nat.min_self]

theorem needL'_heldAfter (w : List (Fin 2)) {lastTick i : ℕ} (st : ℕ → State GalilVM)
    (hi : i ≤ lastTick) : needL' w (heldAfter lastTick st) i = needL' w st i := by
  unfold needL' PalPeg.GalilThrottledRun.needS
  rw [heldAfter_of_le st hi]

/-- **The chain position invariant along a packed pre-trace**, from the scan landing obligations:
the assembly `BranchSupply.needBound_of_scanLandingObligations` makes on its way to the need
bound.  In scan mode with a chain at work it gives `position verifier + lag = position right`. -/
theorem chainPosInv2_alongPreTrace (entry q : ℕ) (first : Fin 9) {w : List (Fin 2)}
    (hw : 0 < w.length) {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hpreTrace : PreTraceIMW centreC placeC entry q first w st Tc)
    (hres : ScanLandingObligationsAlongTrace centreC placeC entry q first w st Tc) :
    ∀ i, i ≤ Tc w.length →
      PalPeg.CloseoutPackRun41.ChainPositionInvariantWithShiftPhase w (st i).ctl (st i).vm := by
  have hleftLive : ∀ i, i ≤ Tc w.length →
      PalPeg.GalilTrailSane.LeftLive (st i).ctl (st i).vm :=
    fun i hi => PalPeg.CloseoutPackRun10.leftLive_of_lpackM (hpreTrace.packs i hi).pack
  have hradLedger := PalPeg.CloseoutLPack6.radLedger_pt centreC placeC entry q first hw
    hpreTrace.base.pre hleftLive
  have hshiftCanRight := PalPeg.BranchSupply.shiftRightHeadCanRight_alongTrace centreC placeC
    entry q first hw hpreTrace.base.pre (fun j hj => (hpreTrace.packs j hj).m2)
  exact PalPeg.BranchSupply.chainPosInv2_alongTrace centreC placeC entry q first
    hpreTrace.base.pre
    (fun i hi => PalPeg.BranchSupply.landingObligationsAt_of_sansRadiusLedger centreC placeC
      entry q first (hradLedger i hi)
      ⟨(hres i hi).bg, (hres i hi).matchLand, (hres i hi).entryLand,
        fun hmode _ => hshiftCanRight i hi hmode⟩)
    (PalPeg.BranchSupply.canRightAtScanOrShift_alongTrace centreC placeC entry q first hw
      hpreTrace)
    (by rw [hpreTrace.base.pre.start]
        exact PalPeg.CloseoutPackRun41.chainPosInv2_of_idle
          (PalPeg.CloseoutShiftFinal.boot_chain_idle w))

#print axioms chainPosInv2_alongPreTrace

/-- **The verifier of a chain walking back represents the word, and its lag is not negative**,
at every point of a pre-loaded trace: the `.back` fields of the verifier and lag invariants of
`BranchSupply`, which hold along the trace without a guard on the mode. -/
theorem backVerifier_alongPreTrace (entry q : ℕ) (first : Fin 9) (hfirst : first ≠ 4)
    {w : List (Fin 2)} (hw : 0 < w.length) {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hpreTrace : PreTraceIMW centreC placeC entry q first w st Tc) :
    ∀ i, i ≤ Tc w.length → (st i).ctl.mode = .scan →
      ∀ (v : GalilScaffoldChainPeriod.Tape) (h lag margin : GalilScaffoldCounter.Counter)
        (ver : GalilScaffoldInputHead.PlaceHead), (st i).vm.chain = .back v h lag margin ver →
        GalilScaffoldInputTrace.Represents ver.head w ∧ 0 ≤ GalilScaffoldCounter.value lag := by
  intro i hile _ v h lag margin ver hchain
  have hverifier := PalPeg.BranchSupply.chainVerifierRepresents_alongTrace centreC placeC entry q
    first hw hpreTrace
    (PalPeg.BranchSupply.marksInv_alongTrace_ofPreTrace centreC placeC entry q first hfirst
      hpreTrace.base.pre)
    (hpreTrace.base.tc1 ▸ hpreTrace.base.pre.mono 1 w.length hw le_rfl) i hile
  have hlag := PalPeg.BranchSupply.chainLagCanonical_alongTrace centreC placeC entry q first hw
    hpreTrace i hile
  exact ⟨(hverifier.backVer v h lag margin ver hchain).1,
    (hlag.backLagField v h lag margin ver hchain).2⟩

#print axioms backVerifier_alongPreTrace

/-- **The lookahead of the chain verifier of a tracked, non-starved scan state has arrived.**
On the held canonical trace below the last report point: the verifier supply gives `VerRep` and
`LagCan`, `chainPosInv2_alongPreTrace` the position ledger, the scan geometry of the pack the
representation of the right head, the front pack its sanity, and the starvation test the
lookahead of the right head.  For a chain walking back the representation of its verifier and the
sign of its lag are not in these invariants; `hbackRep` is `backVerifier_alongPreTrace`. -/
theorem chainLook_heldAfter (entry q : ℕ) (first : Fin 9)
    {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hpreTrace : PreTraceIMW centreC placeC entry q first w st Tc)
    (hres : ScanLandingObligationsAlongTrace centreC placeC entry q first w st Tc)
    (hsupply : PalPeg.BranchSupply.ChainVerifierSupplyAlongTrace w st Tc)
    (hbackRep : ∀ i, i ≤ Tc w.length → (st i).ctl.mode = .scan →
      ∀ (v : GalilScaffoldChainPeriod.Tape) (h lag margin : GalilScaffoldCounter.Counter)
        (ver : GalilScaffoldInputHead.PlaceHead), (st i).vm.chain = .back v h lag margin ver →
        GalilScaffoldInputTrace.Represents ver.head w ∧ 0 ≤ GalilScaffoldCounter.value lag)
    (m : Mirrored1 (tapeCount spare)) (k j : ℕ)
    (hnotStarved : ¬ Starved m.vm)
    (hneedy : Needy w (heldAfter (Tc w.length) st) k j m.vm) (hbefore : k < Tc w.length)
    (hused : usedVM w (heldAfter (Tc w.length) st k).vm ≤ j)
    (hscan : (heldAfter (Tc w.length) st k).ctl.mode = .scan) :
    PalPeg.GalilLookRefined.lookChain' w.length (heldAfter (Tc w.length) st k).vm.chain ≤ j := by
  have hheld : heldAfter (Tc w.length) st k = st k := heldAfter_of_le st hbefore.le
  have hsuffix : PalPeg.GalilThrottledRun.SufVM w (heldAfter (Tc w.length) st k).vm := by
    rw [hheld]
    exact sufVM_trace w st (Tc w.length) (sharedC_suf w _ _ centreC placeC entry) q first 2048
      hpreTrace.base.pre.trace.tick (by rw [hpreTrace.base.pre.start]; exact sufVM_boot w) k
      hbefore.le
  have hlookRight := PalPeg.LocalStarvedRight.usedPH_right_le_of_notStarved hneedy hnotStarved
    hsuffix hused (Or.inr hscan)
  rw [hheld] at hused hscan hlookRight ⊢
  have hpositive : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hzero | hpos
    · rw [hzero, hpreTrace.base.pre.start] at hscan
      cases hscan
    · exact hpos
  have hsane := (PalPeg.BranchSupply.frontPack_alongTrace centreC placeC entry q first hw
    hpreTrace.base.pre k hpositive hbefore.le).sane
  have hrightRep : GalilScaffoldInputTrace.Represents (st k).vm.right.head w := by
    cases hreplaying : (st k).ctl.replaying with
    | false =>
      obtain ⟨radius, hgeometry⟩ :=
        (hpreTrace.packs k hbefore.le).m2.packM.scanGeom hscan hreplaying
      exact hgeometry.rightRep
    | true =>
      obtain ⟨radius, hgeometry⟩ := (hpreTrace.packs k hbefore.le).m2.scanGeomR hscan hreplaying
      exact hgeometry.rightRep
  obtain ⟨hverRep, hlagCan⟩ := hsupply k hbefore.le hscan
  by_cases hidle : (st k).vm.chain = ChainVM.idle
  · rw [hidle]
    exact Nat.zero_le _
  · have hledger := ((chainPosInv2_alongPreTrace entry q first hw hpreTrace hres k
      hbefore.le).payload hscan hidle).chainPos
    have husedChain : PalPeg.GalilThrottledRun.usedChain w.length (st k).vm.chain ≤ j :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hused
    exact PalPeg.ChainLookBehindRight.lookChain'_le w j (st k).vm.chain (st k).vm.right hverRep
      hledger hlagCan (hbackRep k hbefore.le hscan) hrightRep hsane husedChain hlookRight

#print axioms chainLook_heldAfter

/-- **A tracked state whose need has arrived is not starved.**  The starvation test reads, by the
mode, the cursors the tick moves; the need bounds the letters used by the target of the tick and
the lookahead of the right head, so each cursor the test reads can move after truncation
(`canRight_truncPH`).  `init` occurs at the boot state only, whose right head has the word
pending. -/
theorem notStarved_of_need_heldAfter (entry q : ℕ) (first : Fin 9) {w : List (Fin 2)}
    (hw : 0 < w.length) {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hpreTrace : PreTraceIMW centreC placeC entry q first w st Tc)
    (m : Mirrored1 (tapeCount spare)) (k j : ℕ)
    (hneedy : Needy w (heldAfter (Tc w.length) st) k j m.vm) (hbefore : k < Tc w.length)
    (hneed : needT' w (heldAfter (Tc w.length) st) k ≤ j) : ¬ Starved m.vm := by
  obtain ⟨-, hnextUsed, hlook⟩ := PalPeg.LocalSysConcrete.used_le_of_need hneed
  have hheld := heldAfter_of_le st hbefore.le
  rw [heldAfter_of_le st (Nat.succ_le_of_lt hbefore)] at hnextUsed
  rw [hheld] at hlook
  have hstate := hneedy.2
  rw [hheld] at hstate
  have hvm : PalPeg.LocalReplayParked.abs'' m.vm
      = PalPeg.GalilThrottledRun.truncVM (w.length - j) (st k).vm := congrArg State.vm hstate
  have hctl : m.vm.ctl = (st k).ctl := congrArg State.ctl hstate
  have htick := hpreTrace.base.pre.trace.tick k hbefore
  refine Classical.not_not.mpr ⟨fun hmode => ?_, fun hshift hmoves => ?_⟩
  · rw [hvm]
    rw [hctl] at hmode
    rcases hmode with hinit | hscan
    · have hzero : k = 0 := by
        rcases Nat.eq_zero_or_pos k with hzero | hpos
        · exact hzero
        · exact absurd hinit (PalPeg.BranchSupply.mode_ne_init_alongTrace_afterFirstStep centreC
            placeC entry q first hpreTrace.base.pre k hpos hbefore.le)
      obtain ⟨t, hinitVM, hnext⟩ := PalPeg.GalilTickFair.tick_init_cases (c := (st k).ctl)
        (s := (st k).vm) hinit htick
      have hright : t.right = GalilScaffoldChainVerifier.right (st k).vm.right := hinitVM.1
      have hlookRight : PalPeg.GalilThrottledRun.usedPH w.length
          (GalilScaffoldChainVerifier.right (st k).vm.right) ≤ j := by
        rw [← hright]
        rw [hnext] at hnextUsed
        exact (PalPeg.GalilTruncTick.usedVM_right w t).trans hnextUsed
      refine PalPeg.GalilTruncTick.canRight_truncPH w.length j _ ?_ hlookRight
      rw [hzero, hpreTrace.base.pre.start]
      exact initialHead_canRight w (by
        intro hnil
        rw [hnil] at hw
        exact Nat.lt_irrefl 0 hw)
    · exact PalPeg.GalilTruncTick.canRight_truncPH w.length j _
        (PalPeg.BranchSupply.canRightAtScanOrShift_alongTrace centreC placeC entry q first hw
          hpreTrace k hbefore.le (Or.inl hscan))
        (le_trans (PalPeg.GalilLookRefined.look'_scan w hscan).1 hlook)
  · rw [hctl] at hshift
    rw [hvm] at hmoves ⊢
    have hmoves' : (galilFrameS (PofC centreC placeC entry w) q first).remainingPos (st k).vm :=
      hmoves
    obtain ⟨hcanCenter, hcanLeft, hcanLeftTwice, hcenterNext, hleftNext⟩ :=
      PalPeg.TickUsedLetters.shiftMove_of_tick htick hshift hmoves'
    have hlookCenter : PalPeg.GalilThrottledRun.usedPH w.length
        (GalilScaffoldChainVerifier.right (st k).vm.center) ≤ j := by
      rw [← hcenterNext]
      exact (PalPeg.GalilTruncTick.usedVM_center w _).trans hnextUsed
    have hlookLeftTwice : PalPeg.GalilThrottledRun.usedPH w.length
        (GalilScaffoldChainVerifier.right (GalilScaffoldChainVerifier.right (st k).vm.left))
          ≤ j := by
      rw [← hleftNext]
      exact (PalPeg.GalilTruncTick.usedVM_left w _).trans hnextUsed
    have hlookLeft := le_trans (PalPeg.GalilTruncTick.usedPH_right_mono w.length _) hlookLeftTwice
    refine ⟨PalPeg.GalilTruncTick.canRight_truncPH w.length j _ hcanCenter hlookCenter,
      PalPeg.GalilTruncTick.canRight_truncPH w.length j _ hcanLeft hlookLeft, ?_⟩
    show GalilScaffoldChainVerifier.canRight (GalilScaffoldChainVerifier.right
      (PalPeg.GalilThrottledRun.truncPH (w.length - j) (st k).vm.left))
    rw [PalPeg.GalilTruncTick.truncPH_right w.length j _ hlookLeft]
    exact PalPeg.GalilTruncTick.canRight_truncPH w.length j _ hcanLeftTwice hlookLeftTwice

#print axioms notStarved_of_need_heldAfter

/-- **The letters used by the target of a tick have arrived**, for an `init` tick, a
`replayStart` tick, and a `scan` tick that does not enter `shift`.  `init` puts the three heads on
the place right of the right head, whose lookahead the starvation test gives; `replayStart` puts
them on the centre head; a `scan` tick other than the shift entry uses the letters of the source,
the lookahead of the right head and that of the chain verifier
(`TickUsedLetters.usedVM_scanTick_le`, `chainLook_heldAfter`); a tick of any other mode uses the
letters of the source, or is the moving tick of a shift, which moves the centre head one place
and the left head two, as the starvation test reads in that mode
(`TickUsedLetters.usedVM_phaseTick_le`,
`LocalStarvedRight.usedPH_shiftHeads_le_of_notStarved`).  At the shift entry the chain verifier
moves once more; the position ledger of the target (in `shift` mode) puts the moved verifier not
right of the right head, which has arrived (`HeadBehindRight.usedPH_right_le_of_next_position_le`). -/
theorem nextUsed_heldAfter (entry q : ℕ) (first : Fin 9) (hfirst : first ≠ 4)
    {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hpreTrace : PreTraceIMW centreC placeC entry q first w st Tc)
    (hres : ScanLandingObligationsAlongTrace centreC placeC entry q first w st Tc)
    (hsupply : PalPeg.BranchSupply.ChainVerifierSupplyAlongTrace w st Tc)
    (m : Mirrored1 (tapeCount spare)) (k j : ℕ) (hnotStarved : ¬ Starved m.vm)
    (hneedy : Needy w (heldAfter (Tc w.length) st) k j m.vm) (hbefore : k < Tc w.length)
    (hused : usedVM w (heldAfter (Tc w.length) st k).vm ≤ j) :
    usedVM w (heldAfter (Tc w.length) st (k+1)).vm ≤ j := by
  have hbackRep := backVerifier_alongPreTrace entry q first hfirst hw hpreTrace
  have hsuffix : PalPeg.GalilThrottledRun.SufVM w (heldAfter (Tc w.length) st k).vm := by
    rw [heldAfter_of_le st hbefore.le]
    exact sufVM_trace w st (Tc w.length) (sharedC_suf w _ _ centreC placeC entry) q first 2048
      hpreTrace.base.pre.trace.tick (by rw [hpreTrace.base.pre.start]; exact sufVM_boot w) k
      hbefore.le
  have htick := hpreTrace.base.pre.trace.tick k hbefore
  by_cases hinitMode : (heldAfter (Tc w.length) st k).ctl.mode = .init
  · have hlookRight := PalPeg.LocalStarvedRight.usedPH_right_le_of_notStarved hneedy hnotStarved
      hsuffix hused (Or.inl hinitMode)
    rw [heldAfter_of_le st hbefore.le] at hinitMode hlookRight
    rw [heldAfter_of_le st (Nat.succ_le_of_lt hbefore)]
    obtain ⟨t, hinit, hnext⟩ := PalPeg.GalilTickFair.tick_init_cases (c := (st k).ctl)
      (s := (st k).vm) hinitMode htick
    rw [hnext]
    exact (PalPeg.TickUsedLetters.usedVM_init_le w hinit).trans hlookRight
  · by_cases hreplayMode : (heldAfter (Tc w.length) st k).ctl.mode = .replayStart
    · rw [heldAfter_of_le st hbefore.le] at hreplayMode hused
      rw [heldAfter_of_le st (Nat.succ_le_of_lt hbefore)]
      obtain ⟨t, o, hreplayStart, -, -, hnext⟩ := PalPeg.GalilTickFair.tick_replayStart_cases
        (c := (st k).ctl) (s := (st k).vm) hreplayMode htick
      rw [hnext]
      exact (PalPeg.TickUsedLetters.usedVM_replayStart_le w hreplayStart).trans hused
    · by_cases hscanMode : (heldAfter (Tc w.length) st k).ctl.mode = .scan
      · have hlookRight := PalPeg.LocalStarvedRight.usedPH_right_le_of_notStarved hneedy
          hnotStarved hsuffix hused (Or.inr hscanMode)
        have hlookChain := chainLook_heldAfter entry q first hw hpreTrace hres hsupply hbackRep
          m k j hnotStarved hneedy hbefore hused hscanMode
        have hnextLe : k + 1 ≤ Tc w.length := Nat.succ_le_of_lt hbefore
        rw [heldAfter_of_le st hbefore.le] at hscanMode hused hlookRight hlookChain
        rw [heldAfter_of_le st hnextLe]
        by_cases hshiftNext : (st (k+1)).ctl.mode = .shift
        · obtain ⟨compared, watching, hcompare, hcomparedChain, htargetChain, htargetRight,
            hbound⟩ := PalPeg.TickUsedLetters.usedVM_shiftEntry_le w htick hscanMode hshiftNext
          have hcomparedUsed : usedVM w compared ≤ j :=
            (PalPeg.TickUsedLetters.usedVM_compare_le w _ q first hcompare).trans
              (max_le (max_le hused hlookRight) hlookChain)
          have hpositive : 1 ≤ k := by
            rcases Nat.eq_zero_or_pos k with hzero | hpos
            · rw [hzero, hpreTrace.base.pre.start] at hscanMode
              cases hscanMode
            · exact hpos
          have hmarks := PalPeg.BranchSupply.marksInv_alongTrace_ofPreTrace centreC placeC entry q
            first hfirst hpreTrace.base.pre
          have hTcPos : 1 ≤ Tc w.length :=
            hpreTrace.base.tc1 ▸ hpreTrace.base.pre.mono 1 w.length hw le_rfl
          have hheads := PalPeg.BranchSupply.headsRepresent_alongTrace centreC placeC entry q first
            hw hpreTrace hmarks hTcPos
          have hverifierRep := PalPeg.BranchSupply.chainVerifierRepresents_alongTrace centreC placeC
            entry q first hw hpreTrace hmarks hTcPos k hbefore.le
          have hcomparedRep := PalPeg.BranchSupply.chainVerifierRepresents_compare centreC placeC
            entry q first hcompare hverifierRep (hheads k hpositive hbefore.le).centre.1
            (hheads k hpositive hbefore.le).centre.2
          obtain ⟨-, -, hsum⟩ := ((chainPosInv2_alongPreTrace entry q first hw hpreTrace hres (k+1)
            hnextLe).shiftPay hshiftNext).watch _ htargetChain
          have hlagNonneg := ((PalPeg.BranchSupply.chainLagCanonical_alongTrace centreC placeC entry
            q first hw hpreTrace (k+1) hnextLe).watchLag _ htargetChain).2
          have hsumMoved : (position (GalilScaffoldChainVerifier.right watching.machine.verifier) : ℤ)
              + GalilScaffoldCounter.value watching.lag = position (st (k+1)).vm.right := hsum
          have hlagNonneg' : 0 ≤ GalilScaffoldCounter.value watching.lag := hlagNonneg
          have husedVerifier : PalPeg.GalilThrottledRun.usedPH w.length watching.machine.verifier
              ≤ j := by
            have hchainUsed : PalPeg.GalilThrottledRun.usedChain w.length compared.chain ≤ j :=
              le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hcomparedUsed
            rw [hcomparedChain] at hchainUsed
            exact hchainUsed
          have husedRight : PalPeg.GalilThrottledRun.usedPH w.length (st (k+1)).vm.right ≤ j := by
            rw [htargetRight]
            exact (PalPeg.GalilTruncTick.usedVM_right w compared).trans hcomparedUsed
          have hverifierNext := PalPeg.HeadBehindRight.usedPH_right_le_of_next_position_le w j
            watching.machine.verifier (st (k+1)).vm.right
            (hcomparedRep.watchVer watching hcomparedChain).1
            (hheads (k+1) (by omega) hnextLe).right.1
            (PalPeg.BranchSupply.frontPack_alongTrace centreC placeC entry q first hw
              hpreTrace.base.pre (k+1) (by omega) hnextLe).sane
            (by omega) husedVerifier husedRight
          exact hbound.trans (max_le hcomparedUsed hverifierNext)
        · exact (PalPeg.TickUsedLetters.usedVM_scanTick_le w (c := (st k).ctl) (s := (st k).vm)
            hscanMode htick hshiftNext).trans (max_le (max_le hused hlookRight) hlookChain)
      · have hheld := heldAfter_of_le st hbefore.le
        rw [heldAfter_of_le st (Nat.succ_le_of_lt hbefore)]
        rcases PalPeg.TickUsedLetters.usedVM_phaseTick_le w htick (hheld ▸ hinitMode)
          (hheld ▸ hscanMode) (hheld ▸ hreplayMode) with hkeeps | ⟨hshiftMode, hmoves, hmoved⟩
        · exact hkeeps.trans (hheld ▸ hused)
        · obtain ⟨hlookCenter, hlookLeftTwice⟩ :=
            PalPeg.LocalStarvedRight.usedPH_shiftHeads_le_of_notStarved hneedy hnotStarved
              hsuffix hused (hheld.symm ▸ hshiftMode) (hheld.symm ▸ hmoves)
          rw [hheld] at hused hlookCenter hlookLeftTwice
          exact hmoved.trans (max_le hused (max_le hlookCenter hlookLeftTwice))

#print axioms nextUsed_heldAfter

/-- **A trace state whose right head stands on the last letter has used the whole word.** -/
theorem usedOfLastLetter_heldAfter (entry q : ℕ) (first : Fin 9) (hfirst : first ≠ 4)
    {w : List (Fin 2)} (hw : 0 < w.length) {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hpreTrace : PreTraceIMW centreC placeC entry q first w st Tc) :
    ∀ k, k ≤ Tc w.length →
      position (heldAfter (Tc w.length) st k).vm.right = 2 * w.length - 1 →
      w.length ≤ usedVM w (heldAfter (Tc w.length) st k).vm := by
  intro k hk hpos
  rw [heldAfter_of_le st hk] at hpos ⊢
  rcases Nat.eq_zero_or_pos k with hzero | hkpos
  · exfalso
    rw [hzero, hpreTrace.base.pre.start] at hpos
    have hbootPos : position (initialHead w) = 0 := by simp [position, initialHead]
    have hpos' : position (initialHead w) = 2 * w.length - 1 := hpos
    omega
  · have hTcPos : 1 ≤ Tc w.length :=
      hpreTrace.base.tc1 ▸ hpreTrace.base.pre.mono 1 w.length hw le_rfl
    have hrep := (PalPeg.BranchSupply.headsRepresent_alongTrace centreC placeC entry q first hw
      hpreTrace
      (PalPeg.BranchSupply.marksInv_alongTrace_ofPreTrace centreC placeC entry q first hfirst
        hpreTrace.base.pre) hTcPos k hkpos hk).right.1
    have hsane := (PalPeg.BranchSupply.frontPack_alongTrace centreC placeC entry q first hw
      hpreTrace.base.pre k hkpos hk).sane
    have htwice := PalPeg.GalilNeedBound.two_usedPH_of_rep w _ hrep hsane
    have hright := PalPeg.GalilTruncTick.usedVM_right w (st k).vm
    split_ifs at htwice <;> omega

#print axioms usedOfLastLetter_heldAfter

/-- **`PAL ∈ PEG` from the local system and a physical machine.**  The first three hypotheses
are those of `CloseoutFinalBranch.given_scanLandingObligations` other than the realization; the
rest replaces the realization. -/
theorem given_shadowedLocalSystem (entry q : ℕ) (first : Fin 9) (hfirst : first ≠ 4)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      PalPeg.CloseoutCheckW.CycleOracleOn centreC placeC entry q first
        (PalPeg.CloseoutCheckW.ScanOnPackedRunFromInvLPS centreC placeC entry q first)
        (PalPeg.ShapedRun.OracleTick entry)
      (fun _ y => y.ctl.mode = PalPeg.GalilScaffoldController.Mode.scan) w)
    (hres : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc →
      ScanLandingObligationsAlongTrace centreC placeC entry q first w st Tc)
    (hChainVerifierSupply : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      0 < w.length → PreTraceIMW centreC placeC entry q first w st Tc →
      PalPeg.BranchSupply.ChainVerifierSupplyAlongTrace w st Tc)
    -- the abstract local system
    {Q Γ : Type} {t K : ℕ} [Fintype Q] [DecidableEq Q] [Fintype Γ] [DecidableEq Γ]
    (M : List (Fin 2) → Steps (tapeCount spare)) (repM : List (Fin 2) → Mirrored1 (tapeCount spare) → Bool)
    -- the invariants the abstract local system carries along the run
    (Good : Mirrored1 (tapeCount spare) → Prop) (hgoodInit : Good (x0C (blankVML spare) 2048).core)
    (hgoodTick : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ m : Mirrored1 (tapeCount spare), InvC Good w (heldAfter (Tc w.length) st) m → Good (tickC (M w) m))
    (hgoodFeed : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ (letter : Fin 2) (m : Mirrored1 (tapeCount spare)),
        InvC Good w (heldAfter (Tc w.length) st) m → Good (feedC letter m))
    (hrealizes : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ mode : Mode, Realizes Good w (heldAfter (Tc w.length) st) (Tc w.length) (stepOf (M w) mode) mode)
    -- after the last report point the trace says nothing: the local ticks are still ticks
    (Post : List (Fin 2) → Mirrored1 (tapeCount spare) → Prop)
    (frozen : List (Fin 2) → Mirrored1 (tapeCount spare) → Prop)
    (hnotFrozenTracked : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      0 < w.length → PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ m : Mirrored1 (tapeCount spare), InvC Good w (heldAfter (Tc w.length) st) m →
        ¬ frozen w m)
    (hpostOfLastReport : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      0 < w.length → PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      (∀ index, 1 ≤ index → index ≤ w.length → (st (Tc index)).ctl.mode = Mode.scan) →
      ∀ (m : Mirrored1 (tapeCount spare)), InvC Good w (heldAfter (Tc w.length) st) m →
        Needy w (heldAfter (Tc w.length) st) (Tc w.length) w.length m.vm → Post w m)
    (hpostTick : ∀ (w : List (Fin 2)) (m : Mirrored1 (tapeCount spare)), 0 < w.length →
      Post w m → PhysWF m.vm → MirInv1 m → Good m → ¬ Starved m.vm →
      TickSucc (PofC centreC placeC entry w) q first 2048
          (PalPeg.GalilTickFair.Canonical entry 2048) (frozen w m) (absSC m)
          (absSC (tickC (M w) m)) ∧
        Post w (tickC (M w) m) ∧ PhysWF (tickC (M w) m).vm ∧ MirInv1 (tickC (M w) m) ∧
        Good (tickC (M w) m))
    (rep_sound : ∀ (w : List (Fin 2)) (s : ℕ), 0 < w.length → (w.length - 1) * nLocalL < s →
      repM w (micro (sysM (M w) (repM w)) w (x0C (blankVML spare) 2048) s).core = true →
      ReportPoint w (stAbs (sysM (M w) (repM w)) absSC w (x0C (blankVML spare) 2048) s) ∧
        Refreshed (PofC centreC placeC entry w) q first
          (stAbs (sysM (M w) (repM w)) absSC w (x0C (blankVML spare) 2048) s))
    (rep_complete : ∀ (w : List (Fin 2)) (s : ℕ), 0 < w.length →
      ReportPoint w (stAbs (sysM (M w) (repM w)) absSC w (x0C (blankVML spare) 2048) s) →
      Refreshed (PofC centreC placeC entry w) q first
        (stAbs (sysM (M w) (repM w)) absSC w (x0C (blankVML spare) 2048) s) →
      repM w (micro (sysM (M w) (repM w)) w (x0C (blankVML spare) 2048) s).core = true)
    -- the physical machine and its specification
    (L0 : LocalStep (Fin 2) Q Γ t K) (blankSymbol : Γ) (q0 : Q) (repQ outQ : Q → Bool)
    (htape : 0 < t) (Rep : List (Fin 2) → Mirrored1 (tapeCount spare) → Q × (Fin t → STape Γ) → Prop)
    (hrepInit : ∀ w, Rep w (x0C (blankVML spare) 2048).core
      (q0, fun _ => STape.blankTape blankSymbol))
    (hsimTick : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ m p, OnRun Good Post w (heldAfter (Tc w.length) st) m →
        OnRun Good Post w (heldAfter (Tc w.length) st) (tickC (M w) m) →
        TickSucc (PofC centreC placeC entry w) q first 2048
          (PalPeg.GalilTickFair.Canonical entry 2048) (Starved m.vm ∨ frozen w m) (absSC m)
          (absSC (tickC (M w) m)) →
        Rep w m p → Rep w (tickC (M w) m) (L0.apply blankSymbol p none))
    (hsimFeed : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ letter m p, InvC Good w (heldAfter (Tc w.length) st) m →
        OnRun Good Post w (heldAfter (Tc w.length) st) (feedC letter m) → Rep w m p →
        Rep w (feedC letter m) (L0.apply blankSymbol p (some letter)))
    (hreadRep : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ m p, OnRun Good Post w (heldAfter (Tc w.length) st) m → Rep w m p → repM w m = repQ p.1)
    (hreadOut : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ m p, OnRun Good Post w (heldAfter (Tc w.length) st) m → Rep w m p →
        ReportPoint w (absSC m) → m.vm.ctl.output = outQ p.1) :
    RecognizedByTotalPEG PAL := by
  classical
  have hexists : ∀ w : List (Fin 2), ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      0 < w.length → PreTraceIMW centreC placeC entry q first w st Tc ∧
        CanonTrace entry w st Tc ∧
        ∀ m, 1 ≤ m → m ≤ w.length → (st (Tc m)).ctl.mode = Mode.scan := by
    intro w
    by_cases hw : 0 < w.length
    · obtain ⟨st, Tc, h⟩ := canonicalPreTrace_exists entry q first hor w hw
      exact ⟨st, Tc, fun _ => h⟩
    · exact ⟨fun _ => boot w, fun _ => 0, fun h => absurd h hw⟩
  choose stOf TcOf htraceOf using hexists
  have hstart : ∀ w, 0 < w.length → stOf w 0 = boot w :=
    fun w hw => (htraceOf w hw).1.base.pre.start
  have hneedBound := fun w (hw : 0 < w.length) =>
    needBound_alongPreTrace entry q first hres hChainVerifierSupply hw (htraceOf w hw).1
  exact pal_in_peg_of_shadowed_sysC M repM (blankVML spare) 2048 (PofC centreC placeC entry) (fun _ => q)
    (fun _ => first) (fun w => PofC_onLetter centreC placeC entry w)
    (fun w => PofC_leftFirst centreC placeC entry w) (inv_blank spare) (walkerProper_blank spare) (twin_blank spare) wf_blankView
    (fun w => heldAfter (TcOf w w.length) (stOf w)) TcOf
    (fun w j => sharedC_trunc_vm w j centreC placeC entry (fun s => (centrePlaceC w j s).1)
      (fun s => (centrePlaceC w j s).2))
    (fun w hw k hk => by
      rw [heldAfter_of_le (stOf w) hk.le, heldAfter_of_le (stOf w) (Nat.succ_le_of_lt hk)]
      exact (htraceOf w hw).1.base.pre.trace.tick k hk)
    (fun _ => PalPeg.GalilTickFair.Canonical entry 2048)
    (fun w hw k j hk _ => by
      rw [heldAfter_of_le (stOf w) hk.le, heldAfter_of_le (stOf w) (Nat.succ_le_of_lt hk)]
      exact PalPeg.CanonicalLocalRealizes.canonical_trunc ((htraceOf w hw).2.1 k hk) _)
    (fun w hw k hk => by
      rw [heldAfter_of_le (stOf w) hk]
      exact sufVM_trace w (stOf w) (TcOf w w.length)
        (sharedC_suf w _ _ centreC placeC entry) q first 2048
        (htraceOf w hw).1.base.pre.trace.tick (by rw [hstart w hw]; exact sufVM_boot w) k hk)
    (fun w hw => by
      rw [heldAfter_of_le (stOf w) (Nat.zero_le _), hstart w hw]
      exact absState''_blank spare w)
    (fun w hw => by
      have hneed := needL'_boot w (stOf w) (hstart w hw)
      have hused : usedVM w (stOf w 0).vm ≤ needL' w (stOf w) 0 := le_max_left _ _
      rw [heldAfter_of_le (stOf w) (Nat.zero_le _)]
      omega)
    (fun w hw => ⟨(htraceOf w hw).1.base.pre.tc0,
      fun m hm => (htraceOf w hw).1.base.pre.mono m (m+1) (by omega) hm,
      by rw [needL'_heldAfter w (stOf w) (Nat.zero_le _)]
         exact needL'_boot w (stOf w) (hstart w hw),
      needLe_of_pointwise' w _ (TcOf w) (fun m hm i hi => by
        rw [needL'_heldAfter w (stOf w)
          (hi.trans ((htraceOf w hw).1.base.pre.mono (m+1) w.length hm le_rfl))]
        exact hneedBound w hw m hm i hi)⟩)
    (fun w hw => base_of_preTraceB (htraceOf w hw).1.base)
    (fun w hw => (htraceOf w hw).1.base.pre.cost)
    (fun w hw => by
      rw [heldAfter_of_le (stOf w) le_rfl]
      exact (htraceOf w hw).1.base.pre.report w.length hw le_rfl)
    (fun w hw => usedOfLastLetter_heldAfter entry q first hfirst hw (htraceOf w hw).1)
    Good hgoodInit
    (fun w m hw hinv => hgoodTick w _ _ (htraceOf w hw).1 (htraceOf w hw).2.1 m hinv)
    (fun w letter m hw hinv => hgoodFeed w _ _ (htraceOf w hw).1 (htraceOf w hw).2.1 letter m hinv)
    (fun w hw => hrealizes w _ _ (htraceOf w hw).1 (htraceOf w hw).2.1)
    (fun w m k j hw hinv hstarved hneedy hbefore hused =>
      nextUsed_heldAfter entry q first hfirst hw (htraceOf w hw).1 (hres w _ _ (htraceOf w hw).1)
        (hChainVerifierSupply w _ _ hw (htraceOf w hw).1) m k j hstarved hneedy hbefore hused)
    (fun w m k j hw _ hstarved hneedy hbefore hused hscan =>
      chainLook_heldAfter entry q first hw (htraceOf w hw).1 (hres w _ _ (htraceOf w hw).1)
        (hChainVerifierSupply w _ _ hw (htraceOf w hw).1)
        (backVerifier_alongPreTrace entry q first hfirst hw (htraceOf w hw).1) m k j hstarved hneedy
        hbefore hused
        hscan)
    (fun w m k j hw _ hneedy hbefore hneed =>
      notStarved_of_need_heldAfter entry q first hw (htraceOf w hw).1 m k j hneedy hbefore hneed)
    Post frozen
    (fun w m hw hinv => hnotFrozenTracked w _ _ hw (htraceOf w hw).1 (htraceOf w hw).2.1 m hinv)
    (fun w m hw hinv hneedy =>
      hpostOfLastReport w _ _ hw (htraceOf w hw).1 (htraceOf w hw).2.1 (htraceOf w hw).2.2 m hinv
        hneedy)
    hpostTick
    rep_sound rep_complete L0 blankSymbol q0 repQ outQ htape Rep hrepInit
    (fun w m p hw honRun honRunNext hsucc hrep =>
      hsimTick w _ _ (htraceOf w hw).1 (htraceOf w hw).2.1 m p honRun honRunNext hsucc hrep)
    (fun w letter m p hw hinv honRunNext hrep =>
      hsimFeed w _ _ (htraceOf w hw).1 (htraceOf w hw).2.1 letter m p hinv honRunNext hrep)
    (fun w m p hw honRun hrep =>
      hreadRep w _ _ (htraceOf w hw).1 (htraceOf w hw).2.1 m p honRun hrep)
    (fun w m p hw honRun hrep hpoint =>
      hreadOut w _ _ (htraceOf w hw).1 (htraceOf w hw).2.1 m p honRun hrep hpoint)

#print axioms given_shadowedLocalSystem

/-- The steps of the abstract local system: the seven phase modes of the word-free
`CloseoutCoreAgree.SL`, and the three modes `SL` leaves open. -/
noncomputable def localSteps (q : ℕ) (first : Fin 9)
    (initStep scanStep replayStartStep : Mirrored1 (tapeCount spare) → Mirrored1 (tapeCount spare)) :
    Steps (tapeCount spare) :=
  { PalPeg.CloseoutCoreAgree.SL q first with
    init := initStep, scan := scanStep, replayStart := replayStartStep }

/-- The right head of the held canonical trace never stands past the end of the input. -/
theorem traceRightLe_heldAfter (entry q : ℕ) (first : Fin 9) {w : List (Fin 2)}
    (hw : 0 < w.length) {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hpreTrace : PreTraceIMW centreC placeC entry q first w st Tc) :
    PalPeg.CloseoutRightBounds.TraceRightLe w (heldAfter (Tc w.length) st) := by
  intro k
  have hlastPos : 1 ≤ Tc w.length :=
    hpreTrace.base.tc1 ▸ hpreTrace.base.pre.mono 1 w.length hw le_rfl
  show position (st (min k (Tc w.length))).vm.right ≤ 2 * w.length
  rcases Nat.eq_zero_or_pos (min k (Tc w.length)) with hzero | hpos
  · rw [hzero, hpreTrace.base.pre.start]
    show position (initialHead w) ≤ 2 * w.length
    simp [position, initialHead]
  · have hbound := PalPeg.BranchSupply.rightHeadPos_le_alongTrace centreC placeC entry q first hw
      hpreTrace.base.pre
      (PalPeg.BranchSupply.frontPack_alongTrace centreC placeC entry q first hw
        hpreTrace.base.pre)
      hlastPos (min k (Tc w.length)) hpos (Nat.min_le_right _ _)
    omega

/-- **The `init` mode of the abstract local system.**  A tracked state in `init` mode stands on
the boot state of the held canonical trace (the trace leaves `init` with its first tick), so its
counters are zero and its cursors coincide; if it is not starved the next cell is there, and
`LocalInitStep.initStep` is a canonical `init` tick of the abstraction. -/
theorem initLocal_heldAfter (entry q : ℕ) (first : Fin 9) {Good : Mirrored1 (tapeCount spare) → Prop}
    {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hpreTrace : PreTraceIMW centreC placeC entry q first w st Tc)
    (m : Mirrored1 (tapeCount spare)) (target : State GalilVM)
    (hinv : InvC Good w (heldAfter (Tc w.length) st) m) (hmode : m.vm.ctl.mode = .init)
    (hnotStarved : ¬ Starved m.vm)
    (_htick : Tick (galilFrameS (PofC centreC placeC entry w) q first) 2048
      (absState'' m.vm) target) :
    Tick (galilFrameS (PofC centreC placeC entry w) q first) 2048
        (absState'' m.vm) (absState'' (PalPeg.LocalInitStep.initStep entry m).vm) ∧
      PalPeg.GalilTickFair.Canonical entry 2048 (absState'' m.vm)
        (absState'' (PalPeg.LocalInitStep.initStep entry m).vm) ∧
      PhysWF (PalPeg.LocalInitStep.initStep entry m).vm ∧
      MirInv1 (PalPeg.LocalInitStep.initStep entry m) := by
  obtain ⟨k, j, _, hneedy⟩ := hinv.track
  have hindex : min k (Tc w.length) = 0 := by
    rcases Nat.eq_zero_or_pos (min k (Tc w.length)) with hzero | hpos
    · exact hzero
    · have hne := PalPeg.BranchSupply.mode_ne_init_alongTrace_afterFirstStep centreC placeC entry q
        first hpreTrace.base.pre (min k (Tc w.length)) hpos (Nat.min_le_right _ _)
      have hctl : m.vm.ctl = (st (min k (Tc w.length))).ctl := congrArg State.ctl hneedy
      exact absurd (hctl ▸ hmode) hne
  have hstate : absState'' m.vm = truncS (w.length - j) (boot w) := by
    rw [hneedy]
    show truncS _ (st (min k (Tc w.length))) = _
    rw [hindex, hpreTrace.base.pre.start]
  have hreplaying : m.vm.ctl.replaying = false := by
    have hctl : m.vm.ctl = (boot w).ctl := congrArg State.ctl hstate
    rw [hctl]
    rfl
  obtain ⟨hzero, hdp, hleft, hcenter⟩ :=
    PalPeg.LocalInitStep.premises_of_truncated_boot (w := w) (d := w.length - j) hreplaying
      (congrArg State.vm hstate)
  have hcanRight : GalilScaffoldChainVerifier.canRight
      (PalPeg.LocalArrival.absHead' m.vm.right m.vm.pending) := by
    have hright := (Classical.not_not.mp hnotStarved).1 (Or.inl hmode)
    rw [PalPeg.LocalReplayParked.abs''_eq_abs' hreplaying] at hright
    exact hright
  obtain ⟨htick, hcanonical⟩ := PalPeg.LocalInitStep.tick_initStep
    (Pw := PofC centreC placeC entry w) q first 2048 entry rfl hmode
    hreplaying hinv.phys.inv.roles hinv.phys.inv.views hinv.phys.pend hleft hcenter hcanRight
    hzero hdp
  exact ⟨htick, hcanonical, PalPeg.LocalInitStep.physWF_initStep entry hinv.phys hinv.mir hreplaying⟩

#print axioms initLocal_heldAfter

open Classical in
/-- **The report test of the abstract local layer, by its meaning**: the abstract state is a
refreshed report point of the word.  The abstract layer is a ghost and knows the word; the
physical machine has to keep a bit that agrees with this test on the run (`hencRep`). -/
noncomputable def reportTest (entry q : ℕ) (first : Fin 9) (w : List (Fin 2))
    (x : State GalilVM) : Bool :=
  decide (ReportPoint w x ∧ Refreshed (PofC centreC placeC entry w) q first x)

open Classical in
theorem reportTest_iff (entry q : ℕ) (first : Fin 9) (w : List (Fin 2)) (x : State GalilVM) :
    reportTest entry q first w x = true ↔
      ReportPoint w x ∧ Refreshed (PofC centreC placeC entry w) q first x := by
  unfold reportTest
  exact decide_eq_true_iff

/-- **A local successor**: its abstraction is a canonical tick of the frame of the word from the
abstraction of the source, and it keeps the invariants of the local layer (and the phase after
the last report point, if the source is in it). -/
def NextOK (entry q : ℕ) (first : Fin 9) (Good : Mirrored1 (tapeCount spare) → Prop)
    (w : List (Fin 2))
    (m next : Mirrored1 (tapeCount spare)) : Prop :=
  Tick (galilFrameS (PofC centreC placeC entry w) q first) 2048 (absState'' m.vm)
      (absState'' next.vm) ∧
    PalPeg.GalilTickFair.Canonical entry 2048 (absState'' m.vm) (absState'' next.vm) ∧
    PhysWF next.vm ∧ MirInv1 next ∧ Good next

open Classical in
/-- **The step of the two open modes, by choice.**  The abstract local layer is a ghost of the
proof, so its step need not be computed: it is some local successor when there is one.  It knows
the word, because the frame reads `onLetterVM w`; the physical machine does not
(`hforwardTick` asks it for any local state with a successor abstraction). -/
noncomputable def chosenStep (entry q : ℕ) (first : Fin 9)
    (Good : Mirrored1 (tapeCount spare) → Prop) (w : List (Fin 2))
    (m : Mirrored1 (tapeCount spare)) : Mirrored1 (tapeCount spare) :=
  if h : ∃ next, NextOK entry q first Good w m next then Classical.choose h else m

theorem chosenStep_spec {entry q : ℕ} {first : Fin 9} {Good : Mirrored1 (tapeCount spare) → Prop}
    {w : List (Fin 2)}
    {m : Mirrored1 (tapeCount spare)} (h : ∃ next, NextOK entry q first Good w m next) :
    NextOK entry q first Good w m (chosenStep entry q first Good w m) := by
  unfold chosenStep
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- **The abstract layer is frozen** once its right head has left the last letter of the word:
no report point lies beyond, so the abstract layer (a ghost that knows the word) stops there, and
the machine is only asked to keep its report bit off (not to follow an abstract run for which
the trace gives no invariant). -/
def frozenAt (w : List (Fin 2)) (m : Mirrored1 (tapeCount spare)) : Prop :=
  0 < w.length ∧ 2 * w.length ≤ position (absSC m).vm.right

open Classical in
/-- The steps that do nothing on frozen states. -/
noncomputable def freezeSteps (isFrozen : Mirrored1 (tapeCount spare) → Prop)
    (M : Steps (tapeCount spare)) : Steps (tapeCount spare) where
  init := fun m => if isFrozen m then m else M.init m
  scan := fun m => if isFrozen m then m else M.scan m
  shift := fun m => if isFrozen m then m else M.shift m
  copy := fun m => if isFrozen m then m else M.copy m
  home := fun m => if isFrozen m then m else M.home m
  fpp := fun m => if isFrozen m then m else M.fpp m
  markEnd := fun m => if isFrozen m then m else M.markEnd m
  choose := fun m => if isFrozen m then m else M.choose m
  rewind := fun m => if isFrozen m then m else M.rewind m
  replayStart := fun m => if isFrozen m then m else M.replayStart m

open Classical in
theorem stepOf_freezeSteps (isFrozen : Mirrored1 (tapeCount spare) → Prop)
    (M : Steps (tapeCount spare)) (mode : Mode) (m : Mirrored1 (tapeCount spare)) :
    stepOf (freezeSteps isFrozen M) mode m = if isFrozen m then m else stepOf M mode m := by
  cases mode <;> rfl

/-- Freezing does not change what the steps realize: tracked states are not frozen. -/
theorem realizes_freeze {Good : Mirrored1 (tapeCount spare) → Prop} {w : List (Fin 2)}
    {stOf : ℕ → State GalilVM} {lastTick : ℕ} {isFrozen : Mirrored1 (tapeCount spare) → Prop}
    {M : Steps (tapeCount spare)} {mode : Mode}
    (hnotFrozen : ∀ m, InvC Good w stOf m → ¬ isFrozen m)
    (hrealizes : Realizes Good w stOf lastTick (stepOf M mode) mode) :
    Realizes Good w stOf lastTick (stepOf (freezeSteps isFrozen M) mode) mode := by
  intro m k j hinv hmode hnotStarved hneedy hneed hbefore
  rw [stepOf_freezeSteps, if_neg (hnotFrozen m hinv)]
  exact hrealizes m k j hinv hmode hnotStarved hneedy hneed hbefore

/-- **A tracked state is not frozen**: on the trace the right head stays on or before the last
letter (`BranchSupply.rightHeadPos_le_alongTrace`), and truncation keeps positions. -/
theorem notFrozen_of_invC (entry q : ℕ) (first : Fin 9) {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hpreTrace : PreTraceIMW centreC placeC entry q first w st Tc)
    {Good : Mirrored1 (tapeCount spare) → Prop} (m : Mirrored1 (tapeCount spare))
    (hinv : InvC Good w (heldAfter (Tc w.length) st) m) : ¬ frozenAt w m := by
  intro hfrozen
  obtain ⟨_, _, ⟨k, j, hneedy⟩, _⟩ := hinv
  have hpos : position (absSC m).vm.right
      = position (st (min k (Tc w.length))).vm.right := by
    show position (absState'' m.vm).vm.right = _
    rw [hneedy.2]
    rfl
  have hfrozen := hfrozen.2
  rw [hpos] at hfrozen
  have hTcPos : 1 ≤ Tc w.length :=
    hpreTrace.base.tc1 ▸ hpreTrace.base.pre.mono 1 w.length hw le_rfl
  rcases Nat.eq_zero_or_pos (min k (Tc w.length)) with hzero | hindexPos
  · rw [hzero, hpreTrace.base.pre.start] at hfrozen
    have hbootPos : position (initialHead w) = 0 := by simp [position, initialHead]
    have hfrozen' : 2 * w.length ≤ position (initialHead w) := hfrozen
    omega
  · have hbound := PalPeg.BranchSupply.rightHeadPos_le_alongTrace centreC placeC entry q first hw
      hpreTrace.base.pre
      (PalPeg.BranchSupply.frontPack_alongTrace centreC placeC entry q first hw
        hpreTrace.base.pre)
      hTcPos (min k (Tc w.length)) hindexPos (Nat.min_le_right _ _)
    omega

#print axioms notFrozen_of_invC

/-- The abstraction decides whether a state is frozen. -/
theorem frozenAt_of_absSC_eq {w : List (Fin 2)} {encoded m : Mirrored1 (tapeCount spare)}
    (habs : absSC encoded = absSC m) : frozenAt w encoded ↔ frozenAt w m := by
  unfold frozenAt
  rw [habs]

/-- **The invariant the abstract local layer carries along the run**: the polarity bundle
`LocalWF.PolWF`, outside `scan`.  The readers of a polarity are the seven phase steps and the
replay commit, none of them in `scan`; a successor of a scan state is a state with the right
abstraction, and it need not keep a polarity.  The counter magnitudes a shift or copy unit needs
are read off the trace, where the abstraction of a tracked state lives
(`LocalWF.shiftMagnitudes_of_trace`, `LocalWF.copyRemaining_of_trace`). -/
def localGood (m : Mirrored1 (tapeCount spare)) : Prop :=
  m.vm.ctl.mode ≠ .scan → PalPeg.LocalWF.PolWF m.vm

/-- **The steps that are functions keep the polarity bundle.**  The seven phase steps of
`CloseoutCoreAgree.SL` do not touch the polarity of any tape, and the `init` step lands in
`scan`. -/
theorem localGood_stepOf_localSteps (entry q : ℕ) (first : Fin 9)
    (scanStep replayStartStep : Mirrored1 (tapeCount spare) → Mirrored1 (tapeCount spare))
    {m : Mirrored1 (tapeCount spare)} (hgood : localGood m)
    (hnotScan : m.vm.ctl.mode ≠ .scan) (hnotReplayStart : m.vm.ctl.mode ≠ .replayStart) :
    localGood (stepOf (localSteps (spare := spare) q first (PalPeg.LocalInitStep.initStep entry)
      scanStep replayStartStep) m.vm.ctl.mode m) := by
  have hbundle := hgood hnotScan
  cases hmode : m.vm.ctl.mode with
  | init =>
      -- the landing is a scan state
      exact fun hnotScanNext => absurd rfl hnotScanNext
  | scan => exact absurd hmode hnotScan
  | replayStart => exact absurd hmode hnotReplayStart
  | shift =>
      refine fun _ => PalPeg.LocalWF.polWF_congr hbundle ?_ (fun {M} hentry hland => ?_)
      · show (PalPeg.CloseoutCoreAgree.shiftStepW m).vm.pol = m.vm.pol
        classical
        unfold PalPeg.CloseoutCoreAgree.shiftStepW
        split
        · unfold PalPeg.LocalRealizesPhase.shiftPick; split <;> rfl
        · rfl
      · -- a shift step lands in `shift` or in `scan`
        rcases hentry with rfl | rfl
        · exact hmode
        · exfalso
          classical
          have hland : (PalPeg.CloseoutCoreAgree.shiftStepW m).vm.ctl.mode = Mode.copy := hland
          unfold PalPeg.CloseoutCoreAgree.shiftStepW at hland
          split at hland
          · unfold PalPeg.LocalRealizesPhase.shiftPick at hland
            split at hland <;> exact Mode.noConfusion (hmode.symm.trans hland)
          · exact Mode.noConfusion hland
  | copy =>
      exact fun _ => PalPeg.LocalWF.polWF_congr hbundle (PalPeg.LocalWF.pol_copyStepL m)
        PalPeg.LocalWF.entryMode_of_copyStepL
  | home =>
      exact fun _ => PalPeg.LocalWF.polWF_congr hbundle (PalPeg.LocalWF.pol_homeStepL m)
        PalPeg.LocalWF.entryMode_of_homeStepL
  | fpp =>
      exact fun _ => PalPeg.LocalWF.polWF_congr hbundle
        (PalPeg.LocalWF.pol_ffpp PalPeg.CloseoutCoreAgree.dumS q first m)
        (PalPeg.LocalWF.entryMode_of_ffpp PalPeg.CloseoutCoreAgree.dumS q first)
  | markEnd =>
      exact fun _ => PalPeg.LocalWF.polWF_congr hbundle (PalPeg.LocalWF.pol_markEndStepL m)
        PalPeg.LocalWF.entryMode_of_markEndStepL
  | choose =>
      exact fun _ => PalPeg.LocalWF.polWF_congr hbundle
        (PalPeg.LocalWF.pol_chooseStepC PalPeg.CloseoutCoreAgree.dumS q first m)
        (PalPeg.LocalWF.entryMode_of_chooseStepC PalPeg.CloseoutCoreAgree.dumS q first)
  | rewind =>
      exact fun _ => PalPeg.LocalWF.polWF_congr hbundle
        (PalPeg.LocalWF.pol_rewindStepC PalPeg.CloseoutCoreAgree.dumS q first m)
        (PalPeg.LocalWF.entryMode_of_rewindStepC PalPeg.CloseoutCoreAgree.dumS q first)

/-- **The phase after the last report point**: the abstract state is still a refreshed report
point of the word in scan mode (the plateau: the right head stands on the last letter), or it is
frozen. -/
def postPhase (entry q : ℕ) (first : Fin 9) (w : List (Fin 2))
    (m : Mirrored1 (tapeCount spare)) : Prop :=
  (ReportPoint w (absSC m) ∧ Refreshed (PofC centreC placeC entry w) q first (absSC m) ∧
      (absSC m).ctl.mode = Mode.scan) ∨
    frozenAt w m

/-- The step by choice keeps the run invariant: a local successor has it (`NextOK`), and without
a local successor the step does nothing. -/
theorem good_chosenStep {entry q : ℕ} {first : Fin 9} {Good : Mirrored1 (tapeCount spare) → Prop}
    {w : List (Fin 2)}
    {m : Mirrored1 (tapeCount spare)} (hgood : Good m) :
    Good (chosenStep entry q first Good w m) := by
  by_cases hnext : ∃ next, NextOK entry q first Good w m next
  · exact (chosenStep_spec hnext).2.2.2.2
  · unfold chosenStep
    rw [dif_neg hnext]
    exact hgood

/-- The steps of the abstract local layer for the word `w`: `LocalInitStep.initStep`, the seven
phase steps of `CloseoutCoreAgree.SL`, and `chosenStep` for `scan` and `replayStart`. -/
noncomputable def ghostSteps (entry q : ℕ) (first : Fin 9)
    (Good : Mirrored1 (tapeCount spare) → Prop) (w : List (Fin 2)) :
    Steps (tapeCount spare) :=
  freezeSteps (frozenAt w)
    (localSteps q first (PalPeg.LocalInitStep.initStep entry)
      (chosenStep entry q first Good w) (chosenStep entry q first Good w))

/-- The starvation test reads the abstraction only (the mode and the abstract heads). -/
theorem starved_of_absSC_eq {encoded m : Mirrored1 (tapeCount spare)}
    (habs : absSC encoded = absSC m) : Starved encoded.vm ↔ Starved m.vm := by
  have hctl : encoded.vm.ctl = m.vm.ctl := congrArg State.ctl habs
  have hvm : PalPeg.LocalReplayParked.abs'' encoded.vm = PalPeg.LocalReplayParked.abs'' m.vm :=
    congrArg State.vm habs
  unfold Starved
  rw [hctl, hvm]

/-- **The abstract successor of a local tick is unique**: a canonical tick of the frame has one
target (`GalilTickFair.tick_canonical_unique`), and a starved state stays. -/
theorem tickSucc_unique (entry q : ℕ) (first : Fin 9) (w : List (Fin 2)) {starved₁ starved₂ : Prop}
    (hiff : starved₁ ↔ starved₂) {x y₁ y₂ : State GalilVM}
    (h₁ : TickSucc (PofC centreC placeC entry w) q first 2048
      (PalPeg.GalilTickFair.Canonical entry 2048) starved₁ x y₁)
    (h₂ : TickSucc (PofC centreC placeC entry w) q first 2048
      (PalPeg.GalilTickFair.Canonical entry 2048) starved₂ x y₂) : y₁ = y₂ := by
  rcases h₁ with ⟨hstarved₁, hy₁⟩ | ⟨hnot₁, htick₁, hcanon₁⟩
  · rcases h₂ with ⟨_, hy₂⟩ | ⟨hnot₂, _, _⟩
    · rw [hy₁, hy₂]
    · exact absurd (hiff.mp hstarved₁) hnot₂
  · rcases h₂ with ⟨hstarved₂, _⟩ | ⟨_, htick₂, hcanon₂⟩
    · exact absurd (hiff.mpr hstarved₂) hnot₁
    · exact PalPeg.GalilTickFair.tick_canonical_unique htick₁ hcanon₁ htick₂ hcanon₂

#print axioms tickSucc_unique

open PalPeg.ReplayStartGhost
open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (ofNat)
open PalPeg.LocalReplayParked (abs'')
open PalPeg.LocalArrival (abs')

/-- **A tracked `replayStart` state has a local successor.**  The successor is the ghost commit
`ReplayStartGhost.replayCommitVm`: its abstraction is the unique `replayStartVM` landing, so it is
the target of the tick.  The facts the commit needs are read off the trace: in `replayStart` the
centre head is the right head moved left by the radius, the radius is at most the position of the
right head, and the state is not replaying. -/
theorem replayStartNext (entry q : ℕ) (first : Fin 9) {w : List (Fin 2)}
    (hw : 0 < w.length) {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hpreTrace : PreTraceIMW centreC placeC entry q first w st Tc)
    (m : Mirrored1 (tapeCount spare)) (target : State GalilVM)
    (hinv : InvC (localGood (spare := spare)) w (heldAfter (Tc w.length) st) m)
    (hmode : m.vm.ctl.mode = .replayStart)
    (htarget : Tick (galilFrameS (PofC centreC placeC entry w) q first) 2048
      (absState'' m.vm) target) :
    ∃ next, NextOK entry q first (localGood (spare := spare)) w m
      next := by
  obtain ⟨k, j, hneedy⟩ := hinv.track
  have hbundle := hinv.good (by rw [hmode]; decide)
  have hctl : m.vm.ctl = (heldAfter (Tc w.length) st k).ctl := PalPeg.LocalWF.ctl_of_needy hneedy
  have hvm : abs'' m.vm
      = PalPeg.GalilThrottledRun.truncVM (w.length - j) (heldAfter (Tc w.length) st k).vm :=
    congrArg State.vm hneedy.2
  unfold heldAfter at hctl hvm
  have hindexLe : min k (Tc w.length) ≤ Tc w.length := Nat.min_le_right _ _
  have hmodeTrace : (st (min k (Tc w.length))).ctl.mode = .replayStart := by
    rw [← hctl]; exact hmode
  obtain ⟨r, hradiusTrace, hcentreTrace⟩ :=
    rewindCentre_trace centreC placeC entry q first hpreTrace.base.pre _ hindexLe
      (Or.inr hmodeTrace)
  have hradLedger := PalPeg.CloseoutLPack6.radLedger_pt centreC placeC entry q first hw
    hpreTrace.base.pre
    (fun i hi => PalPeg.CloseoutPackRun10.leftLive_of_lpackM (hpreTrace.packs i hi).pack)
    _ hindexLe
  have hnotReplaying : m.vm.ctl.replaying = false := by
    have hnoReplay : ∀ i, PalPeg.LocalWF.NoReplay (heldAfter (Tc w.length) st i) :=
      PalPeg.LocalWF.noReplay_run (lastTick := Tc w.length)
        (F := galilFrameS (PofC centreC placeC entry w) q first) (delay := 2048)
        (fun i hi => by
          rw [heldAfter_of_le st hi.le, heldAfter_of_le st (Nat.succ_le_of_lt hi)]
          exact hpreTrace.base.pre.trace.tick i hi)
        (fun i hi => heldAfter_afterLast st hi)
        (PalPeg.LocalWF.noReplay_zero_of_init (by
          rw [heldAfter_of_le st (Nat.zero_le _), hpreTrace.base.pre.start]
          rfl))
    rcases Nat.eq_zero_or_pos (min k (Tc w.length)) with hindexZero | hindexPos
    · rw [hindexZero, hpreTrace.base.pre.start] at hmodeTrace
      exact Mode.noConfusion hmodeTrace
    · obtain ⟨previous, hprevious⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hindexPos)
      have hpreviousLt : previous < Tc w.length := by omega
      have hsource := hnoReplay previous
      rw [heldAfter_of_le st hpreviousLt.le] at hsource
      have htick := hpreTrace.base.pre.trace.tick previous hpreviousLt
      rw [hctl, hprevious]
      exact notReplaying_of_tick_into_replayStart hsource htick
        (by rw [← hprevious]; exact hmodeTrace)
  rw [PalPeg.LocalReplayParked.abs''_eq_abs' hnotReplaying] at hvm
  have hradiusEq : (abs' m.vm).radius = ofNat r :=
    ((congrArg GalilVM.radius hvm).trans rfl).trans hradiusTrace
  have hrightEq : (abs' m.vm).right
      = PalPeg.GalilThrottledRun.truncPH (w.length - j) (st (min k (Tc w.length))).vm.right :=
    (congrArg GalilVM.right hvm).trans rfl
  have hcentreEq : (abs' m.vm).center
      = PalPeg.GalilThrottledRun.truncPH (w.length - j) (st (min k (Tc w.length))).vm.center :=
    (congrArg GalilVM.center hvm).trans rfl
  have hradiusVal : LocalCounter.val (m.vm.phys (m.vm.roles .radius)) = r := by
    have hvalue := PalPeg.LocalWF.value_absCtr_of_positivePolarity
      (m.vm.phys (m.vm.roles .radius))
    have hradiusAbs : (abs' m.vm).radius
        = PalPeg.LocalCounter.absCtr (m.vm.phys (m.vm.roles .radius)) true := by
      rw [← hbundle.2.1]; rfl
    rw [← hradiusAbs, hradiusEq] at hvalue
    have hofNat : PalPeg.GalilScaffoldCounter.value (ofNat r) = (r : ℤ) := by
      simp [PalPeg.GalilScaffoldCounter.value, ofNat]
    omega
  have hland : GalilScaffoldInputHead.left^[LocalCounter.val (m.vm.phys (m.vm.roles .radius))]
      (abs' m.vm).right = (abs' m.vm).center := by
    rw [hradiusVal, hrightEq, hcentreEq, truncPH_left_iterate, ← hcentreTrace]
  have hradiusLe : LocalCounter.val (m.vm.phys (m.vm.roles .radius))
      ≤ position (abs' m.vm).right := by
    rw [hradiusVal, hrightEq]
    have hle := hradLedger.le
    rw [hradiusTrace] at hle
    have hofNat : PalPeg.GalilScaffoldCounter.value (ofNat r) = (r : ℤ) := by
      simp [PalPeg.GalilScaffoldCounter.value, ofNat]
    show r ≤ position (st (min k (Tc w.length))).vm.right
    omega
  obtain ⟨landing, o, hlanding, -, -, htargetEq⟩ :=
    PalPeg.GalilTickFair.tick_replayStart_cases (c := m.vm.ctl) (s := abs'' m.vm) hmode htarget
  have hlandingVM : replayStartVM entry (abs'' m.vm) landing := hlanding
  obtain ⟨landingReplaying, hlandingReplaying⟩ : ∃ flag : Bool,
      flag = (galilFrameS (PofC centreC placeC entry w) q first).replayPos landing := ⟨_, rfl⟩
  rw [← hlandingReplaying] at htargetEq
  have hflag : landingReplaying = true ∨
      LocalCounter.val (m.vm.phys (m.vm.roles .radius)) = 0 := by
    cases r with
    | zero => exact Or.inr hradiusVal
    | succ r' =>
      left
      rw [hlandingReplaying]
      show PalPeg.GalilScaffoldCounter.positive landing.replay = true
      rw [hlandingVM.1, show (abs'' m.vm).radius = (abs' m.vm).radius from rfl, hradiusEq]
      rfl
  have hnextLanding := replayStartVM_replayCommitVm (x := m.vm) entry
    { m.vm.ctl with mode := Mode.scan, clock := 2048, output := o, replaying := landingReplaying }
    hinv.phys.inv.roles hnotReplaying hflag hland
  have hnextVm := replayStartVM_unique hnextLanding hlandingVM
  refine ⟨⟨replayCommitVm entry
    { m.vm.ctl with mode := Mode.scan, clock := 2048, output := o, replaying := landingReplaying }
    m.vm, m.vm.center⟩, ?_, ?_, ?_, ?_, ?_⟩
  · -- the tick
    suffices htickTo : ∀ landed : State GalilVM, landed = target →
        Tick (galilFrameS (PofC centreC placeC entry w) q first) 2048 (absState'' m.vm) landed from
      htickTo _ (by rw [htargetEq]; exact congrArg (State.mk _) hnextVm)
    intro landed hlanded
    rw [hlanded]
    exact htarget
  · -- canonical: only the search cursor clause applies
    refine ⟨fun hscan => ?_, fun hscan => ?_, fun _ => ?_⟩
    · exact absurd (hmode.symm.trans hscan) (by decide)
    · exact absurd (hmode.symm.trans hscan) (by decide)
    · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hperiodOnly, hwalker⟩ := hnextLanding
      exact ⟨hperiodOnly, hwalker⟩
  · -- the physical pack
    exact ⟨inv_replayCommitVm entry _ hinv.phys.inv,
      parkedOK_replayCommitVm entry _ hinv.phys.inv.roles hradiusLe,
      hinv.phys.pend, hinv.phys.walkerProper⟩
  · -- the mirror of the centre
    exact ⟨PalPeg.LocalReplaySwap.Twin.refl _, hinv.phys.inv.views.2.1⟩
  · -- the landing is a scan state: no polarity is asked for
    exact fun hnotScanNext => absurd rfl hnotScanNext

section ScanSuccessor

open PalPeg.GalilScaffoldChainInputSupply GalilScaffoldInputHead
open PalPeg.GalilScaffoldCounter (Canonical value ofNat)
open PalPeg.GhostSection (ghostOf countersOf absState''_ghostOf physWF_ghostOf polOf_of_nonneg)
open PalPeg.ScanEntrySigns (entrySigns_of_scanTick)

/-- **The successor by the section.**  A tick target with canonical counters, a parked right
head and the signs of the entry counters has a local successor. -/
theorem nextOK_ghostOf (entry q : ℕ) (first : Fin 9) {w : List (Fin 2)}
    {m : Mirrored1 (tapeCount spare)} {target : State GalilVM} {parked : PlaceHead} {r : ℕ}
    (hinj : Function.Injective m.vm.roles)
    (htick : Tick (galilFrameS (PofC centreC placeC entry w) q first) 2048
      (absState'' m.vm) target)
    (hcanonicalTick : PalPeg.GalilTickFair.Canonical entry 2048 (absState'' m.vm) target)
    (hcanonical : ∀ role, Canonical (countersOf target.vm role))
    (hreplay : target.vm.replay = ofNat r)
    (hright : target.vm.right = GalilScaffoldInputHead.left^[r] parked)
    (hparkedLe : r ≤ position parked)
    (hrest : target.ctl.replaying = false → r = 0)
    (hsigns : target.ctl.mode ≠ Mode.scan →
      0 ≤ value target.vm.radius ∧ 0 ≤ value target.vm.length ∧
        (target.ctl.mode = Mode.shift →
          0 ≤ value target.vm.remaining ∧ 0 ≤ value target.vm.cycle) ∧
        (target.ctl.mode = Mode.copy → 0 ≤ value target.vm.fpp.work)) :
    ∃ next, NextOK entry q first (localGood (spare := spare)) w m next := by
  refine ⟨ghostOf m.vm.roles m.vm.phys target.ctl target.vm parked, ?_⟩
  have habs : absState'' (ghostOf m.vm.roles m.vm.phys target.ctl target.vm parked).vm = target :=
    absState''_ghostOf hinj m.vm.phys target.ctl hcanonical hreplay hright hrest
  obtain ⟨hphys, hmir⟩ := physWF_ghostOf hinj m.vm.phys target.ctl hreplay hparkedLe
  refine ⟨by rw [habs]; exact htick, by rw [habs]; exact hcanonicalTick, hphys, hmir, ?_⟩
  intro hnotScan
  obtain ⟨hradius, hlength, hshift, hcopy⟩ := hsigns hnotScan
  exact ⟨fun hmode => polOf_of_nonneg (hcanonical .remaining) (hshift hmode).1,
    polOf_of_nonneg (hcanonical .radius) hradius,
    polOf_of_nonneg (hcanonical .length) hlength,
    fun hmode => polOf_of_nonneg (hcanonical .cycle) (hshift hmode).2,
    fun hmode => polOf_of_nonneg (hcanonical .fppWork) (hcopy hmode)⟩

/-- **The open mode `scan`.**  A tracked scan state whose tick target is the next state of the
trace, truncated to the letters that have arrived, has a local successor: the section of that
target (`GhostSection.ghostOf`).  The counters of a trace state are canonical
(`CountersCanonicalTrace.countersCanonical_trace`), its right head is parked
(`ParkedRight.parkedRight_trace`), and truncation touches neither. -/
theorem scanNext (entry q : ℕ) (first : Fin 9) {w : List (Fin 2)}
    (hw : 0 < w.length) {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hpreTrace : PreTraceIMW centreC placeC entry q first w st Tc)
    (m : Mirrored1 (tapeCount spare)) (target : State GalilVM)
    (hinv : InvC (localGood (spare := spare)) w (heldAfter (Tc w.length) st) m)
    (hmode : m.vm.ctl.mode = .scan)
    (htarget : Tick (galilFrameS (PofC centreC placeC entry w) q first) 2048
      (absState'' m.vm) target)
    (honTrace : ∃ k j, Needy w (heldAfter (Tc w.length) st) k j m.vm ∧ k < Tc w.length ∧
      target = truncS (w.length - j) (heldAfter (Tc w.length) st (k+1)))
    (hcanonicalTick : PalPeg.GalilTickFair.Canonical entry 2048 (absState'' m.vm) target) :
    ∃ next, NextOK entry q first (localGood (spare := spare)) w m next := by
  obtain ⟨k, j, hneedy, hbefore, htargetEq⟩ := honTrace
  have hpre := hpreTrace.base.pre
  rw [heldAfter_of_le st (Nat.succ_le_of_lt hbefore)] at htargetEq
  have hsource : absState'' m.vm = truncS (w.length - j) (st k) := by
    rw [hneedy.2, heldAfter_of_le st hbefore.le]
  -- the counters of the target
  have hall := (PalPeg.CountersCanonicalTrace.countersCanonical_trace centreC placeC entry q first
    hpre (k+1) (Nat.succ_le_of_lt hbefore)).1
  have hcanonical : ∀ role, Canonical (countersOf target.vm role) := by
    intro role
    rw [htargetEq]
    cases role
    · exact hall.cycle
    · exact hall.remaining
    · exact hall.radius
    · exact hall.length
    · exact hall.replay
    · exact hall.lower
    · exact hall.span
    · exact hall.work
    · exact hall.debt
    · exact hall.fppWork
  -- the parked right head of the target
  obtain ⟨r, parked, hreplay, hright, hparkedLe⟩ :=
    PalPeg.ParkedRight.parkedRight_trace centreC placeC entry q first hw hpre (k+1)
      (Nat.succ_le_of_lt hbefore)
  have hpack := PalPeg.BranchSupply.frontPack_alongTrace centreC placeC entry q first hw hpre
    (k+1) (Nat.succ_le_succ (Nat.zero_le k)) (Nat.succ_le_of_lt hbefore)
  -- the signs at an entry, from the source
  have hspanSource := PalPeg.BranchSupply.spanRepOnScanAndShift_alongTrace centreC placeC entry q
    first hpre k hbefore.le
  have hradLedger := PalPeg.CloseoutLPack6.radLedger_pt centreC placeC entry q first hw hpre
    (fun i hi => PalPeg.CloseoutPackRun10.leftLive_of_lpackM (hpreTrace.packs i hi).pack)
    k hbefore.le
  have hscanTrace : (st k).ctl.mode = Mode.scan := by
    have hctl : m.vm.ctl = (truncS (w.length - j) (st k)).ctl := congrArg State.ctl hsource
    rw [← hmode, hctl]; rfl
  have hsigns := entrySigns_of_scanTick _ _ centreC placeC entry q first 2048
    (c := (st k).ctl) (s := PalPeg.GalilThrottledRun.truncVM (w.length - j) (st k).vm)
    (c' := target.ctl) (t := target.vm) hscanTrace
    (hspanSource (Or.inl hscanTrace)) hradLedger.nonneg
    (by have htickSource := htarget; rw [hsource] at htickSource; exact htickSource)
  refine nextOK_ghostOf entry q first hinv.phys.inv.roles htarget hcanonicalTick hcanonical
    (r := r) (parked := PalPeg.GalilThrottledRun.truncPH (w.length - j) parked) ?_ ?_ ?_ ?_ hsigns
  · rw [htargetEq]; exact hreplay
  · rw [htargetEq]
    show PalPeg.GalilThrottledRun.truncPH (w.length - j) (st (k+1)).vm.right = _
    rw [hright, PalPeg.ReplayStartGhost.truncPH_left_iterate]
  · exact hparkedLe
  · intro hnotReplaying
    rw [htargetEq] at hnotReplaying
    exact ofNat_eq_reset (hreplay.symm.trans (hpack.rest (Or.inl hnotReplaying)))

#print axioms scanNext

end ScanSuccessor

/-- **`PAL ∈ PEG` from the plateau step and a physical machine.**  The `init` mode is
`LocalInitStep.initStep` (`initLocal_heldAfter`), `scan` and `replayStart` have a local successor
on the trace (`scanNext`, `replayStartNext`); what is still asked of the abstract local layer is a
successor on the plateau after the last report point (`hplateauNext`).  The seven phase modes of
the abstract local system are `CloseoutCoreAgree.realizes_seven_SL`; its side conditions are
facts about the held canonical trace.  The physical machine is asked for a forward simulation up
to the abstraction (`hforwardTick`, `hforwardFeed`): it may compute any local state whose
abstraction is an abstract successor, because that successor is unique (`tickSucc_unique`). -/
theorem given_openModesAndPhysicalMachine (entry q : ℕ) (first : Fin 9) (hfirst : first ≠ 4)
    (hq : q ≤ 64)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      PalPeg.CloseoutCheckW.CycleOracleOn centreC placeC entry q first
        (PalPeg.CloseoutCheckW.ScanOnPackedRunFromInvLPS centreC placeC entry q first)
        (PalPeg.ShapedRun.OracleTick entry)
      (fun _ y => y.ctl.mode = PalPeg.GalilScaffoldController.Mode.scan) w)
    (hres : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc →
      ScanLandingObligationsAlongTrace centreC placeC entry q first w st Tc)
    (hChainVerifierSupply : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      0 < w.length → PreTraceIMW centreC placeC entry q first w st Tc →
      PalPeg.BranchSupply.ChainVerifierSupplyAlongTrace w st Tc)
    {Q Γ : Type} {t K : ℕ} [Fintype Q] [DecidableEq Q] [Fintype Γ] [DecidableEq Γ]
    -- on the plateau after the last report point the local ticks are still ticks
    (hplateauNext : ∀ (w : List (Fin 2)) (m : Mirrored1 (tapeCount spare)), 0 < w.length →
      ReportPoint w (absSC m) → Refreshed (PofC centreC placeC entry w) q first (absSC m) →
      (absSC m).ctl.mode = Mode.scan → ¬ frozenAt w m → PhysWF m.vm → MirInv1 m → (localGood (spare := spare)) m →
      ¬ Starved m.vm → ∃ next, NextOK entry q first (localGood (spare := spare)) w m next)
    (L0 : LocalStep (Fin 2) Q Γ t K) (blankSymbol : Γ) (q0 : Q) (repQ outQ : Q → Bool)
    (htape : 0 < t) (Enc : Mirrored1 (tapeCount spare) → Q × (Fin t → STape Γ) → Prop)
    (hencInit : Enc (x0C (blankVML spare) 2048).core (q0, fun _ => STape.blankTape blankSymbol))
    -- the machine simulates the local layer forwards, up to the abstraction: from a configuration
    -- encoding some local state with the abstraction of a state of the run, one step reaches a
    -- configuration encoding a local state whose abstraction is an abstract successor
    (hforwardTick : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ m encoded p, OnRun (localGood (spare := spare)) (postPhase entry q first) w (heldAfter (Tc w.length) st) m → ¬ frozenAt w m →
        absSC encoded = absSC m → Enc encoded p →
        ∃ next, Enc next (L0.apply blankSymbol p none) ∧
          TickSucc (PofC centreC placeC entry w) q first 2048
            (PalPeg.GalilTickFair.Canonical entry 2048) (Starved encoded.vm) (absSC encoded)
            (absSC next))
    (hforwardFeed : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ letter m encoded p, InvC (localGood (spare := spare)) w (heldAfter (Tc w.length) st) m →
        absSC encoded = absSC m → Enc encoded p →
        ∃ next, Enc next (L0.apply blankSymbol p (some letter)) ∧
          absSC next = absSC (feedC letter m))
    -- once the abstract layer is frozen the machine is not followed any more: it keeps an
    -- invariant of its own, under which its report bit is off
    (PhysFrozen : List (Fin 2) → Q × (Fin t → STape Γ) → Prop)
    (hfrozenEnter : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ m encoded p, OnRun (localGood (spare := spare)) (postPhase entry q first) w (heldAfter (Tc w.length) st) m → frozenAt w m →
        absSC encoded = absSC m → Enc encoded p → PhysFrozen w p)
    (hfrozenKeep : ∀ (w : List (Fin 2)) p, PhysFrozen w p →
      PhysFrozen w (L0.apply blankSymbol p none))
    (hfrozenQuiet : ∀ (w : List (Fin 2)) p, PhysFrozen w p → repQ p.1 = false)
    (hencRep : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ m encoded p, OnRun (localGood (spare := spare)) (postPhase entry q first) w (heldAfter (Tc w.length) st) m →
        absSC encoded = absSC m → Enc encoded p → reportTest entry q first w (absSC encoded) = repQ p.1)
    (hencOut : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ m encoded p, OnRun (localGood (spare := spare)) (postPhase entry q first) w (heldAfter (Tc w.length) st) m →
        absSC encoded = absSC m → Enc encoded p → ReportPoint w (absSC m) →
        encoded.vm.ctl.output = outQ p.1) :
    RecognizedByTotalPEG PAL := by
  refine given_shadowedLocalSystem entry q first hfirst hor hres hChainVerifierSupply
    (fun w => ghostSteps entry q first (localGood (spare := spare)) w)
    (fun w m => reportTest entry q first w (absSC m))
    (localGood (spare := spare))
    (fun _ => PalPeg.LocalWF.polWF_x0C ⟨fun _ => rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩ 2048)
    (fun w st Tc hpreTrace hcanonical m hinv => by
      by_cases hstarved : Starved m.vm
      · rw [PalPeg.LocalSysConcrete.tickC_starved _ hstarved]
        exact hinv.good
      · rw [PalPeg.LocalSysConcrete.tickC_step _ hstarved]
        show localGood (stepOf (freezeSteps (frozenAt w) _) m.vm.ctl.mode m)
        rw [stepOf_freezeSteps]
        split
        · exact hinv.good
        · by_cases hscan : m.vm.ctl.mode = .scan
          · rw [hscan]
            exact good_chosenStep hinv.good
          · by_cases hreplayStart : m.vm.ctl.mode = .replayStart
            · rw [hreplayStart]
              exact good_chosenStep hinv.good
            · exact localGood_stepOf_localSteps entry q first _ _ hinv.good hscan hreplayStart)
    (fun w st Tc hpreTrace hcanonical letter m hinv =>
      fun hnotScan => PalPeg.LocalWF.polWF_congr
        (hinv.good (by rwa [PalPeg.LocalWF.ctl_feedC hinv.phys.pend letter] at hnotScan))
        (PalPeg.LocalWF.pol_feedC hinv.phys.pend letter)
        (fun _ hland => by rwa [PalPeg.LocalWF.ctl_feedC hinv.phys.pend letter] at hland))
    ?_ (postPhase entry q first) frozenAt
    (fun w st Tc hw hpreTrace _ m hinv => notFrozen_of_invC entry q first hw hpreTrace m hinv)
    (fun w st Tc hw hpreTrace _ hscanAtReport m _ hneedy => by
      refine Or.inl ?_
      have hstate := hneedy.2
      rw [Nat.sub_self, PalPeg.GalilThrottledRun.truncS_zero, heldAfter_of_le st le_rfl]
        at hstate
      show ReportPoint w (absState'' m.vm) ∧ Refreshed _ q first (absState'' m.vm) ∧
        (absState'' m.vm).ctl.mode = Mode.scan
      rw [hstate]
      have hreport := PalPeg.GalilLedgerAssembly.reportPoint_of_at_length hw
        (hpreTrace.base.pre.report w.length hw le_rfl)
      exact ⟨hreport.1, hreport.2, hscanAtReport w.length hw le_rfl⟩)
    (fun w m hw hpost hphys hmir hgood hnotStarved => by
      by_cases hfrozen : frozenAt w m
      · have hstay : tickC (ghostSteps entry q first (localGood (spare := spare)) w) m = m := by
          rw [PalPeg.LocalSysConcrete.tickC_step _ hnotStarved]
          show stepOf (freezeSteps (frozenAt w) _) m.vm.ctl.mode m = m
          rw [stepOf_freezeSteps, if_pos hfrozen]
        rw [hstay]
        exact ⟨Or.inl ⟨hfrozen, rfl⟩, Or.inr hfrozen, hphys, hmir, hgood⟩
      · rcases hpost with ⟨hpoint, hrefreshed, hscan⟩ | hfrozen'
        · have hspec := chosenStep_spec
            (hplateauNext w m hw hpoint hrefreshed hscan hfrozen hphys hmir hgood hnotStarved)
          have hstep : tickC (ghostSteps entry q first (localGood (spare := spare)) w) m
              = chosenStep entry q first (localGood (spare := spare)) w m := by
            rw [PalPeg.LocalSysConcrete.tickC_step _ hnotStarved]
            show stepOf (freezeSteps (frozenAt w) _) m.vm.ctl.mode m = _
            rw [stepOf_freezeSteps, if_neg hfrozen, show m.vm.ctl.mode = Mode.scan from hscan]
            rfl
          rw [hstep]
          have hphase : postPhase entry q first w
              (chosenStep entry q first (localGood (spare := spare)) w m) := by
            rcases PalPeg.ReportPhase.reportPhase_tick centreC placeC entry q first 2048
                hpoint hrefreshed hscan hspec.1 with hkept | hleft
            · exact Or.inl hkept
            · exact Or.inr ⟨hw, hleft⟩
          exact ⟨Or.inr ⟨hfrozen, hspec.1, hspec.2.1⟩, hphase, hspec.2.2.1, hspec.2.2.2.1,
            hspec.2.2.2.2⟩
        · exact absurd hfrozen' hfrozen)
    (fun w s _ _ hreport => (reportTest_iff entry q first w _).mp hreport)
    (fun w s _ hpoint hrefreshed => (reportTest_iff entry q first w _).mpr ⟨hpoint, hrefreshed⟩)
    L0
    blankSymbol q0 repQ outQ htape
    (fun w m p => (¬ frozenAt w m ∧ ∃ encoded, Enc encoded p ∧ absSC encoded = absSC m) ∨
      (frozenAt w m ∧ PhysFrozen w p))
    (fun w => Or.inl ⟨fun hfrozen => by
        have hbound := hfrozen.2
        have hpos : position (absSC (x0C (blankVML spare) 2048).core).vm.right = 0 := by
          show position (absState'' (x0C (blankVML spare) 2048).core.vm).vm.right = 0
          rw [absState''_blank spare w]
          show position (initialHead w) = 0
          simp [position, initialHead]
        have := hfrozen.1
        omega, _, hencInit, rfl⟩)
    (fun w st Tc hpreTrace hcanonical m p honRun honRunNext hsucc hrep => by
      rcases hrep with ⟨hnotFrozen, encoded, henc, habs⟩ | ⟨hfrozen, hphys⟩
      · obtain ⟨next, hencNext, hsuccEncoded⟩ :=
          hforwardTick w st Tc hpreTrace hcanonical m encoded p honRun hnotFrozen habs henc
        rw [habs] at hsuccEncoded
        have hnextAbs := tickSucc_unique entry q first w
          (⟨fun h => Or.inl ((starved_of_absSC_eq habs).mp h),
            fun h => h.elim (starved_of_absSC_eq habs).mpr (fun hf => absurd hf hnotFrozen)⟩)
          hsuccEncoded hsucc
        by_cases hfrozenNext : frozenAt w (tickC (ghostSteps entry q first (localGood (spare := spare)) w) m)
        · exact Or.inr ⟨hfrozenNext, hfrozenEnter w st Tc hpreTrace hcanonical _ next _
            honRunNext hfrozenNext hnextAbs hencNext⟩
        · exact Or.inl ⟨hfrozenNext, next, hencNext, hnextAbs⟩
      · have hstay : absSC (tickC (ghostSteps entry q first (localGood (spare := spare)) w) m) = absSC m := by
          rcases hsucc with ⟨_, hstay⟩ | ⟨hmoves, _⟩
          · exact hstay
          · exact absurd (Or.inr hfrozen) hmoves
        exact Or.inr ⟨(frozenAt_of_absSC_eq hstay).mpr hfrozen, hfrozenKeep w p hphys⟩)
    (fun w st Tc hpreTrace hcanonical letter m p hinv honRunNext hrep => by
      rcases hrep with ⟨_, encoded, henc, habs⟩ | ⟨hfrozen, _⟩
      · obtain ⟨next, hencNext, hnextAbs⟩ :=
          hforwardFeed w st Tc hpreTrace hcanonical letter m encoded p hinv habs henc
        by_cases hfrozenNext : frozenAt w (feedC letter m)
        · exact Or.inr ⟨hfrozenNext, hfrozenEnter w st Tc hpreTrace hcanonical _ next _
            honRunNext hfrozenNext hnextAbs hencNext⟩
        · exact Or.inl ⟨hfrozenNext, next, hencNext, hnextAbs⟩
      · exact absurd hfrozen (notFrozen_of_invC entry q first hfrozen.1 hpreTrace m hinv))
    (fun w st Tc hpreTrace hcanonical m p honRun hrep => by
      show reportTest entry q first w (absSC m) = repQ p.1
      rcases hrep with ⟨_, encoded, henc, habs⟩ | ⟨hfrozen, hphys⟩
      · rw [← habs]
        exact hencRep w st Tc hpreTrace hcanonical m encoded p honRun habs henc
      · rw [hfrozenQuiet w p hphys]
        cases htest : reportTest entry q first w (absSC m) with
        | false => rfl
        | true =>
          have hlast := ((reportTest_iff entry q first w _).mp htest).1.atLast
          have := hfrozen.1
          have := hfrozen.2
          omega)
    (fun w st Tc hpreTrace hcanonical m p honRun hrep hpoint => by
      rcases hrep with ⟨_, encoded, henc, habs⟩ | ⟨hfrozen, _⟩
      · rw [← show encoded.vm.ctl = m.vm.ctl from congrArg State.ctl habs]
        exact hencOut w st Tc hpreTrace hcanonical m encoded p honRun habs henc hpoint
      · have hlast := hpoint.atLast
        have := hfrozen.1
        have := hfrozen.2
        omega)
  intro w st Tc hpreTrace hcanonical mode
  rcases Nat.eq_zero_or_pos w.length with hempty | hw
  · intro m k j _ _ _ _ _ hbefore
    rw [hempty, hpreTrace.base.pre.tc0] at hbefore
    exact absurd hbefore (Nat.not_lt_zero _)
  have hshared := fun j => sharedC_trunc_vm w j centreC placeC entry
    (fun s => (centrePlaceC w j s).1) (fun s => (centrePlaceC w j s).2)
  have htick : ∀ k, k < Tc w.length →
      Tick (galilFrameS (PofC centreC placeC entry w) q first) 2048
        (heldAfter (Tc w.length) st k) (heldAfter (Tc w.length) st (k+1)) := fun k hk => by
    rw [heldAfter_of_le st hk.le, heldAfter_of_le st (Nat.succ_le_of_lt hk)]
    exact hpreTrace.base.pre.trace.tick k hk
  have hcanonicalTick : ∀ k, k < Tc w.length →
      PalPeg.GalilTickFair.Canonical entry 2048
        (heldAfter (Tc w.length) st k) (heldAfter (Tc w.length) st (k+1)) := fun k hk => by
    rw [heldAfter_of_le st hk.le, heldAfter_of_le st (Nat.succ_le_of_lt hk)]
    exact hcanonical k hk
  have hshiftIdleInCopy : ∀ k, (heldAfter (Tc w.length) st k).ctl.mode = .copy →
      ¬ PalPeg.GalilTickFun3.ShiftRemaining (heldAfter (Tc w.length) st k).vm := by
    intro k hmode hshift
    have hTcPos : 1 ≤ Tc w.length :=
      hpreTrace.base.tc1 ▸ hpreTrace.base.pre.mono 1 w.length hw le_rfl
    unfold heldAfter at hmode hshift
    have hindexLe : min k (Tc w.length) ≤ Tc w.length := Nat.min_le_right _ _
    rcases Nat.eq_zero_or_pos (min k (Tc w.length)) with hindexZero | hindexPos
    · rw [hindexZero, hpreTrace.base.pre.start] at hmode
      exact Mode.noConfusion hmode
    · have hcpack := PalPeg.BranchSupply.cpack_alongTrace centreC placeC entry q first hw
        hpreTrace.base.pre hTcPos _ hindexPos hindexLe
      have hidle := hcpack.idle (by rw [hmode]; decide)
      rw [PalPeg.GalilScaffoldChainInputSupply.shiftIdle_iff] at hidle
      unfold PalPeg.GalilTickFun3.ShiftRemaining at hshift
      rw [hidle] at hshift
      exact absurd hshift (by decide)
  have hshiftLedgerOnTrace : ∀ k, (heldAfter (Tc w.length) st k).ctl.mode = .shift →
      CopyIdle (heldAfter (Tc w.length) st k).vm ∧
        GalilScaffoldCounter.value (heldAfter (Tc w.length) st k).vm.remaining
          ≤ GalilScaffoldCounter.value (heldAfter (Tc w.length) st k).vm.radius ∧
        SpanRep (heldAfter (Tc w.length) st k).vm := by
    intro k hmode
    unfold heldAfter at hmode ⊢
    have hindexLe : min k (Tc w.length) ≤ Tc w.length := Nat.min_le_right _ _
    have hradLedger := PalPeg.CloseoutLPack6.radLedger_pt centreC placeC entry q first hw
      hpreTrace.base.pre
      (fun j hj => PalPeg.CloseoutPackRun10.leftLive_of_lpackM (hpreTrace.packs j hj).pack)
    exact ⟨PalPeg.CloseoutRadPack3.copyIdle_trace centreC placeC entry q first
        hpreTrace.base.pre _ hindexLe hmode,
      (hradLedger _ hindexLe).shiftBud hmode,
      PalPeg.BranchSupply.spanRepOnScanAndShift_alongTrace centreC placeC entry q first
        hpreTrace.base.pre _ hindexLe (Or.inr hmode)⟩
  have hseven := PalPeg.CloseoutCoreAgree.realizes_seven_SL (P := (tapeCount spare)) (Good := localGood (spare := spare))
    (raw := w) (stOf := heldAfter (Tc w.length) st) (lastTick := Tc w.length)
    (Pw := PofC centreC placeC entry w) (qq := q) (first := first) (delay := 2048)
    (fun j => sharedC_trunc_vm w j centreC placeC entry (fun s => (centrePlaceC w j s).1)
      (fun s => (centrePlaceC w j s).2))
    (fun k hk => by
      rw [heldAfter_of_le st hk.le, heldAfter_of_le st (Nat.succ_le_of_lt hk)]
      exact hpreTrace.base.pre.trace.tick k hk)
    (fun k hk => heldAfter_afterLast st hk)
    (PalPeg.LocalWF.noReplay_zero_of_init (by
      rw [heldAfter_of_le st (Nat.zero_le _), hpreTrace.base.pre.start]
      rfl))
    hq (fun m hinv hnotScan => ⟨hinv.good hnotScan⟩)
    hshiftIdleInCopy hshiftLedgerOnTrace
    (PofC_onLetter centreC placeC entry w) (PofC_leftFirst centreC placeC entry w)
    (PalPeg.CloseoutRightBounds.rightInBounds
      (PalPeg.LocalWF.phaseNoReplay_of_trace
        (PalPeg.LocalWF.noReplay_run (lastTick := Tc w.length)
          (F := galilFrameS (PofC centreC placeC entry w) q first) (delay := 2048)
          (fun k hk => by
            rw [heldAfter_of_le st hk.le, heldAfter_of_le st (Nat.succ_le_of_lt hk)]
            exact hpreTrace.base.pre.trace.tick k hk)
          (fun k hk => heldAfter_afterLast st hk)
          (PalPeg.LocalWF.noReplay_zero_of_init (by
            rw [heldAfter_of_le st (Nat.zero_le _), hpreTrace.base.pre.start]
            rfl))))
      (traceRightLe_heldAfter entry q first hw hpreTrace))
  obtain ⟨hshift, hcopy, hhome, hfpp, hmarkEnd, hchoose, hrewind⟩ := hseven
  refine realizes_freeze (fun m hinv => notFrozen_of_invC entry q first hw hpreTrace m hinv) ?_
  cases mode with
  | init =>
    exact PalPeg.CanonicalLocalRealizes.realizes_canonical hshared htick hcanonicalTick
      (fun m target hinv hmode hnotStarved htarget _ _ =>
        initLocal_heldAfter entry q first hpreTrace m target hinv hmode hnotStarved htarget)
  | scan =>
    exact PalPeg.CanonicalLocalRealizes.realizes_canonical hshared htick hcanonicalTick
      (fun m target hinv hmode hnotStarved htarget honTrace htargetCanonical => by
        have hspec := chosenStep_spec
          (scanNext entry q first hw hpreTrace m target hinv hmode htarget honTrace
            htargetCanonical)
        exact ⟨hspec.1, hspec.2.1, hspec.2.2.1, hspec.2.2.2.1⟩)
  | shift => exact hshift
  | copy => exact hcopy
  | home => exact hhome
  | fpp => exact hfpp
  | markEnd => exact hmarkEnd
  | choose => exact hchoose
  | rewind => exact hrewind
  | replayStart =>
    exact PalPeg.CanonicalLocalRealizes.realizes_canonical hshared htick hcanonicalTick
      (fun m target hinv hmode hnotStarved htarget _ _ => by
        have hspec := chosenStep_spec
          (replayStartNext entry q first hw hpreTrace m target hinv hmode htarget)
        exact ⟨hspec.1, hspec.2.1, hspec.2.2.1, hspec.2.2.2.1⟩)

#print axioms given_openModesAndPhysicalMachine

end PalPeg.ShadowedLocalFinal
