import PalPeg.CloseoutFinalBranch
import PalPeg.LocalShadowConcrete
import PalPeg.LocalBlankState
import PalPeg.CloseoutRightBounds
import PalPeg.CanonicalLocalRealizes
import PalPeg.LocalInitStep

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
    (hneedOfNotStarved : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ (m : Mirrored1 (tapeCount spare)) (k j : ℕ), InvC Good w (heldAfter (Tc w.length) st) m → ¬ Starved m.vm →
        Needy w (heldAfter (Tc w.length) st) k j m.vm →
        TickNeed w (heldAfter (Tc w.length) st) k j)
    (hnotStarvedOfNeed : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ (m : Mirrored1 (tapeCount spare)) (k j : ℕ), InvC Good w (heldAfter (Tc w.length) st) m →
        Needy w (heldAfter (Tc w.length) st) k j m.vm → k < Tc w.length →
        needT' w (heldAfter (Tc w.length) st) k ≤ j → ¬ Starved m.vm)
    -- after the last report point the trace says nothing: the local ticks are still ticks
    (Post : List (Fin 2) → Mirrored1 (tapeCount spare) → Prop)
    (hpostOfLastReport : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ (m : Mirrored1 (tapeCount spare)) (j : ℕ), InvC Good w (heldAfter (Tc w.length) st) m →
        Needy w (heldAfter (Tc w.length) st) (Tc w.length) j m.vm → Post w m)
    (hpostTick : ∀ (w : List (Fin 2)) (m : Mirrored1 (tapeCount spare)), 0 < w.length →
      Post w m → PhysWF m.vm → MirInv1 m → Good m → ¬ Starved m.vm →
      Tick (galilFrameS (PofC centreC placeC entry w) q first) 2048 (absSC m)
          (absSC (tickC M m)) ∧
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
  exact pal_in_peg_of_shadowed_sysC M repC (blankVML spare) 2048 (PofC centreC placeC entry) (fun _ => q)
    (fun _ => first) (fun w => PofC_onLetter centreC placeC entry w)
    (fun w => PofC_leftFirst centreC placeC entry w) (inv_blank spare) (twin_blank spare) wf_blankView
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
    (fun w m k j hw hinv hstarved hneedy =>
      hneedOfNotStarved w _ _ (htraceOf w hw).1 (htraceOf w hw).2 m k j hinv hstarved hneedy)
    (fun w m k j hw hinv hneedy hbefore hneed =>
      hnotStarvedOfNeed w _ _ (htraceOf w hw).1 (htraceOf w hw).2 m k j hinv hneedy hbefore
        hneed)
    Post
    (fun w m j hw hinv hneedy =>
      hpostOfLastReport w _ _ (htraceOf w hw).1 (htraceOf w hw).2 m j hinv hneedy)
    hpostTick
    rep_sound rep_complete L0 blankSymbol q0 repQ outQ htape Rep hrepInit hsimTick hsimFeed
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
    have hall := Classical.not_not.mp hnotStarved
    have hright := hall.2.2.1
    rw [PalPeg.LocalReplayParked.abs''_eq_abs' hreplaying] at hright
    exact hright
  obtain ⟨htick, hcanonical⟩ := PalPeg.LocalInitStep.tick_initStep
    (Pw := PofC centreC placeC entry w) q first 2048 entry rfl hmode
    hreplaying hinv.phys.inv.roles hinv.phys.inv.views hinv.phys.pend hleft hcenter hcanRight
    hzero hdp
  exact ⟨htick, hcanonical, PalPeg.LocalInitStep.physWF_initStep entry hinv.phys hinv.mir hreplaying⟩

#print axioms initLocal_heldAfter

/-- **`PAL ∈ PEG` from the two open modes and a physical machine.**  The `init` mode is
`LocalInitStep.initStep` (`initLocal_heldAfter`).  The seven phase modes of
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
    (hneedOfNotStarved : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ (m : Mirrored1 (tapeCount spare)) (k j : ℕ), InvC Good w (heldAfter (Tc w.length) st) m →
        ¬ Starved m.vm → Needy w (heldAfter (Tc w.length) st) k j m.vm →
        TickNeed w (heldAfter (Tc w.length) st) k j)
    (hnotStarvedOfNeed : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ (m : Mirrored1 (tapeCount spare)) (k j : ℕ), InvC Good w (heldAfter (Tc w.length) st) m →
        Needy w (heldAfter (Tc w.length) st) k j m.vm → k < Tc w.length →
        needT' w (heldAfter (Tc w.length) st) k ≤ j → ¬ Starved m.vm)
    -- after the last report point the trace says nothing: the local ticks are still ticks
    (Post : List (Fin 2) → Mirrored1 (tapeCount spare) → Prop)
    (hpostOfLastReport : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC entry q first w st Tc → CanonTrace entry w st Tc →
      ∀ (m : Mirrored1 (tapeCount spare)) (j : ℕ), InvC Good w (heldAfter (Tc w.length) st) m →
        Needy w (heldAfter (Tc w.length) st) (Tc w.length) j m.vm → Post w m)
    (hpostTick : ∀ (w : List (Fin 2)) (m : Mirrored1 (tapeCount spare)), 0 < w.length →
      Post w m → PhysWF m.vm → MirInv1 m → Good m → ¬ Starved m.vm →
      Tick (galilFrameS (PofC centreC placeC entry w) q first) 2048 (absSC m)
          (absSC (tickC (localSteps q first (PalPeg.LocalInitStep.initStep entry) scanStep replayStartStep) m)) ∧
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
    (htape : 0 < t) (Rep : Mirrored1 (tapeCount spare) → Q × (Fin t → STape Γ) → Prop)
    (hrepInit : Rep (x0C (blankVML spare) 2048).core (q0, fun _ => STape.blankTape blankSymbol))
    (hsimTick : ∀ m p, PhysWF m.vm → MirInv1 m → Rep m p →
      Rep (tickC (localSteps q first (PalPeg.LocalInitStep.initStep entry) scanStep replayStartStep) m)
        (L0.apply blankSymbol p none))
    (hsimFeed : ∀ letter m p, PhysWF m.vm → MirInv1 m → Rep m p →
      Rep (feedC letter m) (L0.apply blankSymbol p (some letter)))
    (hreadRep : ∀ m p, Rep m p → repC m.vm.ctl = repQ p.1)
    (hreadOut : ∀ m p, Rep m p → m.vm.ctl.output = outQ p.1) :
    RecognizedByTotalPEG PAL := by
  refine given_shadowedLocalSystem entry q first hor hres hChainVerifierSupply
    (localSteps q first (PalPeg.LocalInitStep.initStep entry) scanStep replayStartStep) repC Good hgoodInit hgoodTick hgoodFeed
    ?_ hneedOfNotStarved hnotStarvedOfNeed Post hpostOfLastReport hpostTick rep_sound rep_complete L0
    blankSymbol q0 repQ outQ htape Rep hrepInit hsimTick hsimFeed hreadRep hreadOut
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
