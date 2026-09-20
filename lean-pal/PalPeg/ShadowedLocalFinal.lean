import PalPeg.CloseoutFinalBranch
import PalPeg.LocalShadowConcrete
import PalPeg.LocalBlankState
import PalPeg.CloseoutRightBounds
import PalPeg.CanonicalLocalRealizes
import PalPeg.LocalInitStep
import PalPeg.ChainLookBehindRight
import PalPeg.TickUsedLetters

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
open PalPeg.LocalSysConcrete (Steps stepOf tickC sysC absSC feedC Starved Needy TickNeed InvC PhysWF
  Realizes x0C)
open PalPeg.LocalShadowConcrete (pal_in_peg_of_shadowed_sysC OnRun TickSucc)
open PalPeg.LocalBlankState (tapeCount blankVML absState''_blank inv_blank twin_blank wf_blankView)

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

/-- **`PAL ∈ PEG` from the local system and a physical machine.**  The first three hypotheses
are those of `CloseoutFinalBranch.given_scanLandingObligations` other than the realization; the
rest replaces the realization. -/
theorem given_shadowedLocalSystem (entry q : ℕ) (first : Fin 9) (hfirst : first ≠ 4)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      PalPeg.CloseoutCheckW.CycleOracleOn centreC placeC entry q first
        (PalPeg.CloseoutCheckW.ScanOnPackedRunFromInvLPS centreC placeC entry q first)
        (PalPeg.ShapedRun.OracleTick entry) w)
    (hres : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc →
      ScanLandingObligationsAlongTrace centreC placeC entry q first w st Tc)
    (hChainVerifierSupply : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      0 < w.length → PreTraceIMW centreC placeC entry q first w st Tc →
      PalPeg.BranchSupply.ChainVerifierSupplyAlongTrace w st Tc)
    -- the abstract local system
    {Q Γ : Type} {t K : ℕ} [Fintype Q] [DecidableEq Q] [Fintype Γ] [DecidableEq Γ]
    (M : Steps (tapeCount spare)) (repC : Control → Bool)
    -- the invariants the abstract local system carries along the run
    (Good : Mirrored1 (tapeCount spare) → Prop) (hgoodInit : Good (x0C (blankVML spare) 2048).core)
    (hgoodTick : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ m : Mirrored1 (tapeCount spare), InvC Good w (heldAfter (Tc w.length) st) m → Good (tickC M m))
    (hgoodFeed : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ (letter : Fin 2) (m : Mirrored1 (tapeCount spare)),
        InvC Good w (heldAfter (Tc w.length) st) m → Good (feedC letter m))
    (hrealizes : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ mode : Mode, Realizes Good w (heldAfter (Tc w.length) st) (Tc w.length) (stepOf M mode) mode)
    -- after the last report point the trace says nothing: the local ticks are still ticks
    (Post : List (Fin 2) → Mirrored1 (tapeCount spare) → Prop)
    (hpostOfLastReport : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ (m : Mirrored1 (tapeCount spare)) (j : ℕ), InvC Good w (heldAfter (Tc w.length) st) m →
        Needy w (heldAfter (Tc w.length) st) (Tc w.length) j m.vm → Post w m)
    (hpostTick : ∀ (w : List (Fin 2)) (m : Mirrored1 (tapeCount spare)), 0 < w.length →
      Post w m → PhysWF m.vm → MirInv1 m → Good m → ¬ Starved m.vm →
      (Tick (galilFrameS (PofC centreC placeC entry w) q first) 2048 (absSC m)
          (absSC (tickC M m)) ∧
        PalPeg.GalilTickFair.Canonical entry 2048 (absSC m) (absSC (tickC M m))) ∧
        Post w (tickC M m) ∧ PhysWF (tickC M m).vm ∧ MirInv1 (tickC M m) ∧
        Good (tickC M m))
    (rep_sound : ∀ (w : List (Fin 2)) (s : ℕ), 0 < w.length → (w.length - 1) * nLocalL < s →
      repC (micro (sysC M repC) w (x0C (blankVML spare) 2048) s).core.vm.ctl = true →
      ReportPoint w (stAbs (sysC M repC) absSC w (x0C (blankVML spare) 2048) s) ∧
        Refreshed (PofC centreC placeC entry w) q first
          (stAbs (sysC M repC) absSC w (x0C (blankVML spare) 2048) s))
    (rep_complete : ∀ (w : List (Fin 2)) (s : ℕ), 0 < w.length →
      ReportPoint w (stAbs (sysC M repC) absSC w (x0C (blankVML spare) 2048) s) →
      Refreshed (PofC centreC placeC entry w) q first
        (stAbs (sysC M repC) absSC w (x0C (blankVML spare) 2048) s) →
      ∃ s', s' ≤ s ∧ (w.length - 1) * nLocalL + 1 < s' ∧
        repC (micro (sysC M repC) w (x0C (blankVML spare) 2048) s').core.vm.ctl = true)
    -- the physical machine and its specification
    (L0 : LocalStep (Fin 2) Q Γ t K) (blankSymbol : Γ) (q0 : Q) (repQ outQ : Q → Bool)
    (htape : 0 < t) (Rep : Mirrored1 (tapeCount spare) → Q × (Fin t → STape Γ) → Prop)
    (hrepInit : Rep (x0C (blankVML spare) 2048).core (q0, fun _ => STape.blankTape blankSymbol))
    (hsimTick : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ m p, OnRun Good Post w (heldAfter (Tc w.length) st) m →
        TickSucc (PofC centreC placeC entry w) q first 2048
          (PalPeg.GalilTickFair.Canonical entry 2048) (Starved m.vm) (absSC m)
          (absSC (tickC M m)) →
        Rep m p → Rep (tickC M m) (L0.apply blankSymbol p none))
    (hsimFeed : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ letter m p, OnRun Good Post w (heldAfter (Tc w.length) st) m → Rep m p →
        Rep (feedC letter m) (L0.apply blankSymbol p (some letter)))
    (hreadRep : ∀ m p, Rep m p → repC m.vm.ctl = repQ p.1)
    (hreadOut : ∀ m p, Rep m p → m.vm.ctl.output = outQ p.1) :
    RecognizedByTotalPEG PAL := by
  classical
  have hexists : ∀ w : List (Fin 2), ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      0 < w.length → PreTraceIMW centreC placeC entry q first w st Tc ∧
        CanonTrace entry w st Tc := by
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
  exact pal_in_peg_of_shadowed_sysC M repC (blankVML spare) 2048 (PofC centreC placeC entry) (fun _ => q)
    (fun _ => first) (fun w => PofC_onLetter centreC placeC entry w)
    (fun w => PofC_leftFirst centreC placeC entry w) (inv_blank spare) (twin_blank spare) wf_blankView
    (fun w => heldAfter (TcOf w w.length) (stOf w)) TcOf
    (fun w j => sharedC_trunc_vm w j centreC placeC entry (fun s => (centrePlaceC w j s).1)
      (fun s => (centrePlaceC w j s).2))
    (fun w hw k hk => by
      rw [heldAfter_of_le (stOf w) hk.le, heldAfter_of_le (stOf w) (Nat.succ_le_of_lt hk)]
      exact (htraceOf w hw).1.base.pre.trace.tick k hk)
    (fun _ => PalPeg.GalilTickFair.Canonical entry 2048)
    (fun w hw k j hk _ => by
      rw [heldAfter_of_le (stOf w) hk.le, heldAfter_of_le (stOf w) (Nat.succ_le_of_lt hk)]
      exact PalPeg.CanonicalLocalRealizes.canonical_trunc ((htraceOf w hw).2 k hk) _)
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
    Good hgoodInit
    (fun w m hw hinv => hgoodTick w _ _ (htraceOf w hw).1 (htraceOf w hw).2 m hinv)
    (fun w letter m hw hinv => hgoodFeed w _ _ (htraceOf w hw).1 (htraceOf w hw).2 letter m hinv)
    (fun w hw => hrealizes w _ _ (htraceOf w hw).1 (htraceOf w hw).2)
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
    Post
    (fun w m j hw hinv hneedy =>
      hpostOfLastReport w _ _ (htraceOf w hw).1 (htraceOf w hw).2 m j hinv hneedy)
    hpostTick
    rep_sound rep_complete L0 blankSymbol q0 repQ outQ htape Rep hrepInit
    (fun w m p hw honRun hsucc hrep =>
      hsimTick w _ _ (htraceOf w hw).1 (htraceOf w hw).2 m p honRun hsucc hrep)
    (fun w letter m p hw honRun hrep =>
      hsimFeed w _ _ (htraceOf w hw).1 (htraceOf w hw).2 letter m p honRun hrep)
    hreadRep hreadOut

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

/-- **`PAL ∈ PEG` from the two open modes and a physical machine.**  The `init` mode is
`LocalInitStep.initStep` (`initLocal_heldAfter`).  The seven phase modes of
the abstract local system are `CloseoutCoreAgree.realizes_seven_SL`; its side conditions are
facts about the held canonical trace.  The physical machine is asked for a forward simulation up
to the abstraction (`hforwardTick`, `hforwardFeed`): it may compute any local state whose
abstraction is an abstract successor, because that successor is unique (`tickSucc_unique`). -/
theorem given_openModesAndPhysicalMachine (entry q : ℕ) (first : Fin 9) (hfirst : first ≠ 4)
    (hq : q ≤ 64)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      PalPeg.CloseoutCheckW.CycleOracleOn centreC placeC entry q first
        (PalPeg.CloseoutCheckW.ScanOnPackedRunFromInvLPS centreC placeC entry q first)
        (PalPeg.ShapedRun.OracleTick entry) w)
    (hres : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc →
      ScanLandingObligationsAlongTrace centreC placeC entry q first w st Tc)
    (hChainVerifierSupply : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      0 < w.length → PreTraceIMW centreC placeC entry q first w st Tc →
      PalPeg.BranchSupply.ChainVerifierSupplyAlongTrace w st Tc)
    {Q Γ : Type} {t K : ℕ} [Fintype Q] [DecidableEq Q] [Fintype Γ] [DecidableEq Γ]
    (scanStep replayStartStep : Mirrored1 (tapeCount spare) → Mirrored1 (tapeCount spare))
    (repC : Control → Bool)
    (Good : Mirrored1 (tapeCount spare) → Prop)
    (hgoodWF : ∀ m : Mirrored1 (tapeCount spare), Good m → PalPeg.LocalWF.LocalWF m.vm)
    (hgoodInit : Good (x0C (blankVML spare) 2048).core)
    (hgoodTick : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ m : Mirrored1 (tapeCount spare), InvC Good w (heldAfter (Tc w.length) st) m →
        Good (tickC (localSteps q first (PalPeg.LocalInitStep.initStep entry) scanStep replayStartStep) m))
    (hgoodFeed : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ (letter : Fin 2) (m : Mirrored1 (tapeCount spare)),
        InvC Good w (heldAfter (Tc w.length) st) m → Good (feedC letter m))
    (hscanLocal : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ (m : Mirrored1 (tapeCount spare)) (target : State GalilVM),
        InvC Good w (heldAfter (Tc w.length) st) m → m.vm.ctl.mode = .scan → ¬ Starved m.vm →
        Tick (galilFrameS (PofC centreC placeC entry w) q first) 2048 (absState'' m.vm) target →
        Tick (galilFrameS (PofC centreC placeC entry w) q first) 2048
            (absState'' m.vm) (absState'' (scanStep m).vm) ∧
          PalPeg.GalilTickFair.Canonical entry 2048 (absState'' m.vm)
            (absState'' (scanStep m).vm) ∧
          PhysWF (scanStep m).vm ∧ MirInv1 (scanStep m))
    (hreplayStartLocal : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ (m : Mirrored1 (tapeCount spare)) (target : State GalilVM),
        InvC Good w (heldAfter (Tc w.length) st) m → m.vm.ctl.mode = .replayStart → ¬ Starved m.vm →
        Tick (galilFrameS (PofC centreC placeC entry w) q first) 2048 (absState'' m.vm) target →
        Tick (galilFrameS (PofC centreC placeC entry w) q first) 2048
            (absState'' m.vm) (absState'' (replayStartStep m).vm) ∧
          PalPeg.GalilTickFair.Canonical entry 2048 (absState'' m.vm)
            (absState'' (replayStartStep m).vm) ∧
          PhysWF (replayStartStep m).vm ∧ MirInv1 (replayStartStep m))
    -- after the last report point the trace says nothing: the local ticks are still ticks
    (Post : List (Fin 2) → Mirrored1 (tapeCount spare) → Prop)
    (hpostOfLastReport : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ (m : Mirrored1 (tapeCount spare)) (j : ℕ), InvC Good w (heldAfter (Tc w.length) st) m →
        Needy w (heldAfter (Tc w.length) st) (Tc w.length) j m.vm → Post w m)
    (hpostTick : ∀ (w : List (Fin 2)) (m : Mirrored1 (tapeCount spare)), 0 < w.length →
      Post w m → PhysWF m.vm → MirInv1 m → Good m → ¬ Starved m.vm →
      (Tick (galilFrameS (PofC centreC placeC entry w) q first) 2048 (absSC m)
          (absSC (tickC (localSteps q first (PalPeg.LocalInitStep.initStep entry) scanStep replayStartStep) m)) ∧
        PalPeg.GalilTickFair.Canonical entry 2048 (absSC m) (absSC (tickC (localSteps q first (PalPeg.LocalInitStep.initStep entry) scanStep replayStartStep) m))) ∧
        Post w (tickC (localSteps q first (PalPeg.LocalInitStep.initStep entry) scanStep replayStartStep) m) ∧ PhysWF (tickC (localSteps q first (PalPeg.LocalInitStep.initStep entry) scanStep replayStartStep) m).vm ∧ MirInv1 (tickC (localSteps q first (PalPeg.LocalInitStep.initStep entry) scanStep replayStartStep) m) ∧
        Good (tickC (localSteps q first (PalPeg.LocalInitStep.initStep entry) scanStep replayStartStep) m))
    (rep_sound : ∀ (w : List (Fin 2)) (s : ℕ), 0 < w.length → (w.length - 1) * nLocalL < s →
      repC (micro (sysC (localSteps q first (PalPeg.LocalInitStep.initStep entry) scanStep replayStartStep) repC) w
        (x0C (blankVML spare) 2048) s).core.vm.ctl = true →
      ReportPoint w (stAbs (sysC (localSteps q first (PalPeg.LocalInitStep.initStep entry) scanStep replayStartStep) repC)
          absSC w (x0C (blankVML spare) 2048) s) ∧
        Refreshed (PofC centreC placeC entry w) q first
          (stAbs (sysC (localSteps q first (PalPeg.LocalInitStep.initStep entry) scanStep replayStartStep) repC) absSC w
            (x0C (blankVML spare) 2048) s))
    (rep_complete : ∀ (w : List (Fin 2)) (s : ℕ), 0 < w.length →
      ReportPoint w (stAbs (sysC (localSteps q first (PalPeg.LocalInitStep.initStep entry) scanStep replayStartStep) repC)
        absSC w (x0C (blankVML spare) 2048) s) →
      Refreshed (PofC centreC placeC entry w) q first
        (stAbs (sysC (localSteps q first (PalPeg.LocalInitStep.initStep entry) scanStep replayStartStep) repC) absSC w
          (x0C (blankVML spare) 2048) s) →
      ∃ s', s' ≤ s ∧ (w.length - 1) * nLocalL + 1 < s' ∧
        repC (micro (sysC (localSteps q first (PalPeg.LocalInitStep.initStep entry) scanStep replayStartStep) repC) w
          (x0C (blankVML spare) 2048) s').core.vm.ctl = true)
    (L0 : LocalStep (Fin 2) Q Γ t K) (blankSymbol : Γ) (q0 : Q) (repQ outQ : Q → Bool)
    (htape : 0 < t) (Enc : Mirrored1 (tapeCount spare) → Q × (Fin t → STape Γ) → Prop)
    (hencInit : Enc (x0C (blankVML spare) 2048).core (q0, fun _ => STape.blankTape blankSymbol))
    -- the machine simulates the local layer forwards, up to the abstraction: from a configuration
    -- encoding some local state with the abstraction of a state of the run, one step reaches a
    -- configuration encoding a local state whose abstraction is an abstract successor
    (hforwardTick : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ m encoded p, OnRun Good Post w (heldAfter (Tc w.length) st) m →
        absSC encoded = absSC m → Enc encoded p →
        ∃ next, Enc next (L0.apply blankSymbol p none) ∧
          TickSucc (PofC centreC placeC entry w) q first 2048
            (PalPeg.GalilTickFair.Canonical entry 2048) (Starved encoded.vm) (absSC encoded)
            (absSC next))
    (hforwardFeed : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ letter m encoded p, OnRun Good Post w (heldAfter (Tc w.length) st) m →
        absSC encoded = absSC m → Enc encoded p →
        ∃ next, Enc next (L0.apply blankSymbol p (some letter)) ∧
          absSC next = absSC (feedC letter m))
    (hencRep : ∀ encoded p, Enc encoded p → repC encoded.vm.ctl = repQ p.1)
    (hencOut : ∀ encoded p, Enc encoded p → encoded.vm.ctl.output = outQ p.1) :
    RecognizedByTotalPEG PAL := by
  refine given_shadowedLocalSystem entry q first hfirst hor hres hChainVerifierSupply
    (localSteps q first (PalPeg.LocalInitStep.initStep entry) scanStep replayStartStep) repC Good hgoodInit hgoodTick hgoodFeed
    ?_ Post hpostOfLastReport hpostTick rep_sound rep_complete L0
    blankSymbol q0 repQ outQ htape (fun m p => ∃ encoded, Enc encoded p ∧ absSC encoded = absSC m)
    ⟨_, hencInit, rfl⟩
    (fun w st Tc hpreTrace hcanonical m p honRun hsucc ⟨encoded, henc, habs⟩ => by
      obtain ⟨next, hencNext, hsuccEncoded⟩ :=
        hforwardTick w st Tc hpreTrace hcanonical m encoded p honRun habs henc
      rw [habs] at hsuccEncoded
      exact ⟨next, hencNext,
        tickSucc_unique entry q first w (starved_of_absSC_eq habs) hsuccEncoded hsucc⟩)
    (fun w st Tc hpreTrace hcanonical letter m p honRun ⟨encoded, henc, habs⟩ =>
      hforwardFeed w st Tc hpreTrace hcanonical letter m encoded p honRun habs henc)
    (fun m p ⟨encoded, henc, habs⟩ => by
      rw [← show encoded.vm.ctl = m.vm.ctl from congrArg State.ctl habs]
      exact hencRep encoded p henc)
    (fun m p ⟨encoded, henc, habs⟩ => by
      rw [← show encoded.vm.ctl = m.vm.ctl from congrArg State.ctl habs]
      exact hencOut encoded p henc)
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
  have hseven := PalPeg.CloseoutCoreAgree.realizes_seven_SL (P := (tapeCount spare)) (Good := Good)
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
    hq hgoodWF (PofC_onLetter centreC placeC entry w) (PofC_leftFirst centreC placeC entry w)
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
  cases mode with
  | init =>
    exact PalPeg.CanonicalLocalRealizes.realizes_canonical hshared htick hcanonicalTick
      (fun m target => initLocal_heldAfter entry q first hpreTrace m target)
  | scan =>
    exact PalPeg.CanonicalLocalRealizes.realizes_canonical hshared htick hcanonicalTick
      (hscanLocal w st Tc hpreTrace hcanonical)
  | shift => exact hshift
  | copy => exact hcopy
  | home => exact hhome
  | fpp => exact hfpp
  | markEnd => exact hmarkEnd
  | choose => exact hchoose
  | rewind => exact hrewind
  | replayStart =>
    exact PalPeg.CanonicalLocalRealizes.realizes_canonical hshared htick hcanonicalTick
      (hreplayStartLocal w st Tc hpreTrace hcanonical)

#print axioms given_openModesAndPhysicalMachine

end PalPeg.ShadowedLocalFinal
