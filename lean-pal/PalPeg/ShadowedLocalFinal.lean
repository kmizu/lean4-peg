import PalPeg.CloseoutFinalBranch
import PalPeg.LocalShadowConcrete
import PalPeg.LocalBlankState
import PalPeg.CloseoutRightBounds

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
open PalPeg.LocalSysConcrete (Steps stepOf tickC sysC absSC feedC Starved Needy InvC PhysWF
  Realizes x0C)
open PalPeg.LocalShadowConcrete (pal_in_peg_of_shadowed_sysC)
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

/-- **`PAL ∈ PEG` from the local system and a physical machine.**  The first three hypotheses
are those of `CloseoutFinalBranch.given_scanLandingObligations` other than the realization; the
rest replaces the realization. -/
theorem given_shadowedLocalSystem (entry q : ℕ) (first : Fin 9)
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
    (M : Steps tapeCount) (repC : Control → Bool)
    -- the invariants the abstract local system carries along the run
    (Good : Mirrored1 tapeCount → Prop) (hgoodInit : Good (x0C blankVML 2048).core)
    (hgoodTick : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ m : Mirrored1 tapeCount, InvC Good w (heldAfter (Tc w.length) st) m → Good (tickC M m))
    (hgoodFeed : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ (letter : Fin 2) (m : Mirrored1 tapeCount),
        InvC Good w (heldAfter (Tc w.length) st) m → Good (feedC letter m))
    (hrealizes : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ mode : Mode, Realizes Good w (heldAfter (Tc w.length) st) (Tc w.length) (stepOf M mode) mode)
    (hneedOfNotStarved : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ (m : Mirrored1 tapeCount) (k j : ℕ), InvC Good w (heldAfter (Tc w.length) st) m → ¬ Starved m.vm →
        Needy w (heldAfter (Tc w.length) st) k j m.vm →
        needT' w (heldAfter (Tc w.length) st) k ≤ j)
    (hnotStarvedOfNeed : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ (m : Mirrored1 tapeCount) (k j : ℕ), InvC Good w (heldAfter (Tc w.length) st) m →
        Needy w (heldAfter (Tc w.length) st) k j m.vm → k < Tc w.length →
        needT' w (heldAfter (Tc w.length) st) k ≤ j → ¬ Starved m.vm)
    (hstarvedAtLastReport : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ (m : Mirrored1 tapeCount) (j : ℕ), InvC Good w (heldAfter (Tc w.length) st) m →
        Needy w (heldAfter (Tc w.length) st) (Tc w.length) j m.vm → Starved m.vm)
    (rep_sound : ∀ (w : List (Fin 2)) (s : ℕ), 0 < w.length → (w.length - 1) * nLocalL < s →
      repC (micro (sysC M repC) w (x0C blankVML 2048) s).core.vm.ctl = true →
      ReportPoint w (stAbs (sysC M repC) absSC w (x0C blankVML 2048) s) ∧
        Refreshed (PofC centreC placeC entry w) q first
          (stAbs (sysC M repC) absSC w (x0C blankVML 2048) s))
    (rep_complete : ∀ (w : List (Fin 2)) (s : ℕ), 0 < w.length →
      ReportPoint w (stAbs (sysC M repC) absSC w (x0C blankVML 2048) s) →
      Refreshed (PofC centreC placeC entry w) q first
        (stAbs (sysC M repC) absSC w (x0C blankVML 2048) s) →
      ∃ s', s' ≤ s ∧ (w.length - 1) * nLocalL + 1 < s' ∧
        repC (micro (sysC M repC) w (x0C blankVML 2048) s').core.vm.ctl = true)
    -- the physical machine and its specification
    (L0 : LocalStep (Fin 2) Q Γ t K) (blankSymbol : Γ) (q0 : Q) (repQ outQ : Q → Bool)
    (htape : 0 < t) (Rep : Mirrored1 tapeCount → Q × (Fin t → STape Γ) → Prop)
    (hrepInit : Rep (x0C blankVML 2048).core (q0, fun _ => STape.blankTape blankSymbol))
    (hsimTick : ∀ m p, PhysWF m.vm → MirInv1 m → Rep m p →
      Rep (tickC M m) (L0.apply blankSymbol p none))
    (hsimFeed : ∀ letter m p, PhysWF m.vm → MirInv1 m → Rep m p →
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
  exact pal_in_peg_of_shadowed_sysC M repC blankVML 2048 (PofC centreC placeC entry) (fun _ => q)
    (fun _ => first) (fun w => PofC_onLetter centreC placeC entry w)
    (fun w => PofC_leftFirst centreC placeC entry w) inv_blank twin_blank wf_blankView
    (fun w => heldAfter (TcOf w w.length) (stOf w)) TcOf
    (fun w j => sharedC_trunc_vm w j centreC placeC entry (fun s => (centrePlaceC w j s).1)
      (fun s => (centrePlaceC w j s).2))
    (fun w hw k hk => by
      rw [heldAfter_of_le (stOf w) hk.le, heldAfter_of_le (stOf w) (Nat.succ_le_of_lt hk)]
      exact (htraceOf w hw).1.base.pre.trace.tick k hk)
    (fun w hw k hk => by
      rw [heldAfter_of_le (stOf w) hk]
      exact sufVM_trace w (stOf w) (TcOf w w.length)
        (sharedC_suf w _ _ centreC placeC entry) q first 2048
        (htraceOf w hw).1.base.pre.trace.tick (by rw [hstart w hw]; exact sufVM_boot w) k hk)
    (fun w hw => by
      rw [heldAfter_of_le (stOf w) (Nat.zero_le _), hstart w hw]
      exact absState''_blank w)
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
    (fun w m k j hw hinv hstarved hneedy =>
      hneedOfNotStarved w _ _ (htraceOf w hw).1 (htraceOf w hw).2 m k j hinv hstarved hneedy)
    (fun w m k j hw hinv hneedy hbefore hneed =>
      hnotStarvedOfNeed w _ _ (htraceOf w hw).1 (htraceOf w hw).2 m k j hinv hneedy hbefore
        hneed)
    (fun w m j hw hinv hneedy =>
      hstarvedAtLastReport w _ _ (htraceOf w hw).1 (htraceOf w hw).2 m j hinv hneedy)
    rep_sound rep_complete L0 blankSymbol q0 repQ outQ htape Rep hrepInit hsimTick hsimFeed
    hreadRep hreadOut

#print axioms given_shadowedLocalSystem

/-- The steps of the abstract local system: the seven phase modes of the word-free
`CloseoutCoreAgree.SL`, and the three modes `SL` leaves open. -/
noncomputable def localSteps (q : ℕ) (first : Fin 9)
    (initStep scanStep replayStartStep : Mirrored1 tapeCount → Mirrored1 tapeCount) :
    Steps tapeCount :=
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

/-- **`PAL ∈ PEG` from the three open modes and a physical machine.**  The seven phase modes of
the abstract local system are `CloseoutCoreAgree.realizes_seven_SL`; its side conditions are
facts about the held canonical trace. -/
theorem given_openModesAndPhysicalMachine (entry q : ℕ) (first : Fin 9) (hq : q ≤ 64)
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
    (initStep scanStep replayStartStep : Mirrored1 tapeCount → Mirrored1 tapeCount)
    (repC : Control → Bool)
    (Good : Mirrored1 tapeCount → Prop)
    (hgoodWF : ∀ m : Mirrored1 tapeCount, Good m → PalPeg.LocalWF.LocalWF m.vm)
    (hgoodInit : Good (x0C blankVML 2048).core)
    (hgoodTick : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ m : Mirrored1 tapeCount, InvC Good w (heldAfter (Tc w.length) st) m →
        Good (tickC (localSteps q first initStep scanStep replayStartStep) m))
    (hgoodFeed : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ (letter : Fin 2) (m : Mirrored1 tapeCount),
        InvC Good w (heldAfter (Tc w.length) st) m → Good (feedC letter m))
    (hinitMode : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      Realizes Good w (heldAfter (Tc w.length) st) (Tc w.length) initStep .init)
    (hscanMode : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      Realizes Good w (heldAfter (Tc w.length) st) (Tc w.length) scanStep .scan)
    (hreplayStartMode : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      Realizes Good w (heldAfter (Tc w.length) st) (Tc w.length) replayStartStep .replayStart)
    (hneedOfNotStarved : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ (m : Mirrored1 tapeCount) (k j : ℕ), InvC Good w (heldAfter (Tc w.length) st) m →
        ¬ Starved m.vm → Needy w (heldAfter (Tc w.length) st) k j m.vm →
        needT' w (heldAfter (Tc w.length) st) k ≤ j)
    (hnotStarvedOfNeed : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ (m : Mirrored1 tapeCount) (k j : ℕ), InvC Good w (heldAfter (Tc w.length) st) m →
        Needy w (heldAfter (Tc w.length) st) k j m.vm → k < Tc w.length →
        needT' w (heldAfter (Tc w.length) st) k ≤ j → ¬ Starved m.vm)
    (hstarvedAtLastReport : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ (m : Mirrored1 tapeCount) (j : ℕ), InvC Good w (heldAfter (Tc w.length) st) m →
        Needy w (heldAfter (Tc w.length) st) (Tc w.length) j m.vm → Starved m.vm)
    (rep_sound : ∀ (w : List (Fin 2)) (s : ℕ), 0 < w.length → (w.length - 1) * nLocalL < s →
      repC (micro (sysC (localSteps q first initStep scanStep replayStartStep) repC) w
        (x0C blankVML 2048) s).core.vm.ctl = true →
      ReportPoint w (stAbs (sysC (localSteps q first initStep scanStep replayStartStep) repC)
          absSC w (x0C blankVML 2048) s) ∧
        Refreshed (PofC centreC placeC entry w) q first
          (stAbs (sysC (localSteps q first initStep scanStep replayStartStep) repC) absSC w
            (x0C blankVML 2048) s))
    (rep_complete : ∀ (w : List (Fin 2)) (s : ℕ), 0 < w.length →
      ReportPoint w (stAbs (sysC (localSteps q first initStep scanStep replayStartStep) repC)
        absSC w (x0C blankVML 2048) s) →
      Refreshed (PofC centreC placeC entry w) q first
        (stAbs (sysC (localSteps q first initStep scanStep replayStartStep) repC) absSC w
          (x0C blankVML 2048) s) →
      ∃ s', s' ≤ s ∧ (w.length - 1) * nLocalL + 1 < s' ∧
        repC (micro (sysC (localSteps q first initStep scanStep replayStartStep) repC) w
          (x0C blankVML 2048) s').core.vm.ctl = true)
    (L0 : LocalStep (Fin 2) Q Γ t K) (blankSymbol : Γ) (q0 : Q) (repQ outQ : Q → Bool)
    (htape : 0 < t) (Rep : Mirrored1 tapeCount → Q × (Fin t → STape Γ) → Prop)
    (hrepInit : Rep (x0C blankVML 2048).core (q0, fun _ => STape.blankTape blankSymbol))
    (hsimTick : ∀ m p, PhysWF m.vm → MirInv1 m → Rep m p →
      Rep (tickC (localSteps q first initStep scanStep replayStartStep) m)
        (L0.apply blankSymbol p none))
    (hsimFeed : ∀ letter m p, PhysWF m.vm → MirInv1 m → Rep m p →
      Rep (feedC letter m) (L0.apply blankSymbol p (some letter)))
    (hreadRep : ∀ m p, Rep m p → repC m.vm.ctl = repQ p.1)
    (hreadOut : ∀ m p, Rep m p → m.vm.ctl.output = outQ p.1) :
    RecognizedByTotalPEG PAL := by
  refine given_shadowedLocalSystem entry q first hor hres hChainVerifierSupply
    (localSteps q first initStep scanStep replayStartStep) repC Good hgoodInit hgoodTick hgoodFeed
    ?_ hneedOfNotStarved hnotStarvedOfNeed hstarvedAtLastReport rep_sound rep_complete L0
    blankSymbol q0 repQ outQ htape Rep hrepInit hsimTick hsimFeed hreadRep hreadOut
  intro w st Tc hpreTrace hcanonical mode
  rcases Nat.eq_zero_or_pos w.length with hempty | hw
  · intro m k j _ _ _ _ _ hbefore
    rw [hempty, hpreTrace.base.pre.tc0] at hbefore
    exact absurd hbefore (Nat.not_lt_zero _)
  have hseven := PalPeg.CloseoutCoreAgree.realizes_seven_SL (P := tapeCount) (Good := Good)
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
  | init => exact hinitMode w st Tc hpreTrace hcanonical
  | scan => exact hscanMode w st Tc hpreTrace hcanonical
  | shift => exact hshift
  | copy => exact hcopy
  | home => exact hhome
  | fpp => exact hfpp
  | markEnd => exact hmarkEnd
  | choose => exact hchoose
  | rewind => exact hrewind
  | replayStart => exact hreplayStartMode w st Tc hpreTrace hcanonical

#print axioms given_openModesAndPhysicalMachine

end PalPeg.ShadowedLocalFinal
