import PalPeg.PhysicalShiftLanding
import PalPeg.PhysicalChainShape

/-!
# The arrived input and head ledger needed at shift entry

The physical tick consumes only the represented word and the verifier/lag
alignment. The full periodic-window invariant is stronger than this interface.
The tracked case retains the already proved consumption bound from TrackedAt.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalShiftSource
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldInputHead (PlaceHead layout)
open PalPeg.GalilScaffoldChainVerifier (right canRight)
open PalPeg.GalilThrottledRun
open PalPeg.GalilReplayGeneral2 (LagAt)
open PalPeg.GalilFinalAssembly2 (centreC placeC)
open PalPeg.LocalSysConcrete (absSC)

/-- Truncation to arrived letters preserves exactly their prefix when the
source has consumed no later letter. -/
theorem represents_trunc (raw : List (Fin 2)) (j : ℕ) (head : PlaceHead)
    (hrep : PalPeg.GalilScaffoldInputTrace.Represents head.head raw)
    (hused : usedPH raw.length head ≤ j) (hj : j ≤ raw.length) :
    PalPeg.GalilScaffoldInputTrace.Represents (truncPH (raw.length-j) head).head (raw.take j) := by
  obtain ⟨xs, rs, queue, hh, hw⟩ := hrep
  have hprefix : xs.length + rs.length ≤ j := by
    rw [usedPH, hh, hw] at hused
    cases xs <;> simp [layout] at hused ⊢ <;> omega
  have hcut : queue.length - (raw.length-j) = j - (xs.length + rs.length) := by
    rw [hw] at hj ⊢
    simp only [List.length_append, List.length_reverse] at hj ⊢
    omega
  rw [hw] at hcut
  simp only [List.length_append, List.length_reverse] at hcut
  refine ⟨xs, rs, dropN (raw.length-j) queue, ?_, ?_⟩
  · cases xs <;> simp [truncPH, hh, layout]
  · rw [hw, List.take_append, List.take_append]
    simp only [List.length_append, List.length_reverse]
    rw [List.take_of_length_le (by simpa using (show xs.length ≤ j by omega)),
      List.take_of_length_le (by omega : rs.length ≤ j-xs.length)]
    simp only [dropN, hcut]

/-- Only the two heads and the nonnegative lag ledger are needed to justify
the immediate comparison quantum. -/
structure Heads (raw : List (Fin 2)) (s : GalilVM) : Prop where
  rightRep : PalPeg.GalilScaffoldInputTrace.Represents s.right.head raw
  rightPresent : s.right.head.focus ≠ none
  watch : ∀ wm, s.chain = .watch wm →
    PalPeg.GalilScaffoldInputTrace.Represents wm.machine.verifier.head raw ∧
      wm.machine.verifier.head.focus ≠ none ∧ LagAt wm.lag wm.machine.verifier (position s.right)

theorem heads_of_pack (raw : List (Fin 2)) (x : State GalilVM)
    (hp : PalPeg.CloseoutPackW.IPackMW centreC placeC 0 1 0 raw x)
    (hm : x.ctl.mode = .scan) : Heads raw x.vm := by
  obtain ⟨hr, hf⟩ := PalPeg.WindowPack.rightHead_of_packs hp.pack hp.m2 hm
  refine ⟨hr, hf, ?_⟩
  intro wm hw
  obtain ⟨cen, cc, _, hinv, _⟩ := (hp.win (PalPeg.GalilFinalAssembly2.decodesC 0 raw)).window
  rw [hw] at hinv
  obtain ⟨b, xs, hlag, _, hc⟩ := hinv
  exact ⟨hc.2.1, hc.2.2.1, hlag⟩

theorem heads_trunc (raw : List (Fin 2)) (j : ℕ) (s : GalilVM)
    (hs : Heads raw s) (hu : usedVM raw s ≤ j) (hj : j ≤ raw.length) :
    Heads (raw.take j) (truncVM (raw.length-j) s) := by
  refine ⟨represents_trunc raw j s.right hs.rightRep
    ((PalPeg.GalilTruncTick.usedVM_right raw s).trans hu) hj, hs.rightPresent, ?_⟩
  intro wm hw
  cases hc : s.chain <;> simp only [truncVM, truncChain, hc] at hw
  all_goals try cases hw
  case watch old =>
    obtain ⟨hr, hf, hl⟩ := hs.watch old hc
    have huv : usedPH raw.length old.machine.verifier ≤ j := by
      simp only [usedVM, hc, usedChain, verOf] at hu
      omega
    exact ⟨represents_trunc raw j old.machine.verifier hr huv hj, hf, hl⟩

/-- The tracked prefix and the post-report packed run supply the same head
interface. No arrival bound is postulated at the physical call site. -/
theorem heads_onRun (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ)
    (hpre : PalPeg.CloseoutCheckW.PreTraceIMW centreC placeC 0 1 0 w st Tc)
    (m : PalPeg.LocalReplayParked.Mirrored1 (PalPeg.LocalBlankState.tapeCount 0))
    (hon : PalPeg.LocalShadowConcrete.ArrivedOnRun (PalPeg.ShadowedLocalFinal.localGood (spare := 0))
      (PalPeg.ShadowedLocalFinal.postPhase 0 1 0) w
      (PalPeg.ShadowedLocalFinal.heldAfter (Tc w.length) st) m)
    (hnf : ¬ PalPeg.ShadowedLocalFinal.frozenAt w m)
    (hm : (absSC m).ctl.mode = .scan) :
    ∃ arrived : List (Fin 2), arrived.length ≤ w.length ∧ Heads arrived (absSC m).vm := by
  rcases hon with ⟨_, k, j, ⟨hj, hsource⟩, hused⟩ | ⟨hpost, _, _, _⟩
  · have hm' : (st (min k (Tc w.length))).ctl.mode = .scan :=
      (congrArg (fun z : State GalilVM => z.ctl.mode) hsource).symm.trans hm
    have hp := heads_of_pack w (st (min k (Tc w.length)))
      (hpre.packs _ (Nat.min_le_right _ _)) hm'
    refine ⟨w.take j, by simp, ?_⟩
    change Heads (w.take j) (PalPeg.LocalReplayParked.absState'' m.vm).vm
    rw [hsource]
    exact heads_trunc w j _ hp hused hj
  · rcases hpost with hplateau | hfrozen
    · obtain ⟨c, s, k, kS, _, hrun, _⟩ := hplateau.onRun
      exact ⟨w, le_rfl, heads_of_pack w (absSC m)
        (PalPeg.CloseoutCheckW.ipackMW_last_of_stepsIMWC centreC placeC 0 1 0 hrun) hm⟩
    · exact (hnf hfrozen).elim

/-- The first successful quantum preserves word representation and its lag
ledger, so the second quantum can use the same arrived prefix. -/
theorem watch_internal (raw : List (Fin 2)) (R : ℕ)
    (wm mid : PalPeg.GalilScaffoldChainWatch.State)
    (hr : PalPeg.GalilScaffoldInputTrace.Represents wm.machine.verifier.head raw)
    (hp : wm.machine.verifier.head.focus ≠ none) (hl : LagAt wm.lag wm.machine.verifier R)
    (hi : PalPeg.GalilScaffoldChainWatch.Internal wm mid) :
    PalPeg.GalilScaffoldInputTrace.Represents mid.machine.verifier.head raw ∧
      mid.machine.verifier.head.focus ≠ none ∧ LagAt mid.lag mid.machine.verifier R := by
  cases hi with
  | idle _ => exact ⟨hr, hp, hl⟩
  | take hpos hg =>
    refine ⟨right_word _ raw hr hg.1, right_present _ raw hr hp hg.1, ?_⟩
    have hm := right_position _ hg.1 (represented_position _ raw hr hp).1
    change (PalPeg.GalilScaffoldCounter.dec wm.lag).neg = [] ∧
      position (right wm.machine.verifier) + (PalPeg.GalilScaffoldCounter.dec wm.lag).pos.length = R
    cases hc : wm.lag.pos with
    | nil => simp [PalPeg.GalilScaffoldCounter.positive, hc] at hpos
    | cons a rest =>
      have hsum := hl.2
      rw [hc] at hsum
      simp only [PalPeg.GalilScaffoldCounter.dec, hc, List.length_cons] at hsum ⊢
      exact ⟨hl.1, by omega⟩

/-- At zero lag the two represented cursors stand at the same position. The
outer cursor's available next letter supplies both availability and the actual
symbol for the immediate verifier step. -/
theorem good_at_right (raw : List (Fin 2)) (outer : PlaceHead)
    (wm : PalPeg.GalilScaffoldChainWatch.State)
    (hr : PalPeg.GalilScaffoldInputTrace.Represents wm.machine.verifier.head raw)
    (hp : wm.machine.verifier.head.focus ≠ none)
    (hl : LagAt wm.lag wm.machine.verifier (position outer))
    (hz : PalPeg.GalilScaffoldCounter.zero wm.lag = true)
    (hor : PalPeg.GalilScaffoldInputTrace.Represents outer.head raw)
    (hop : outer.head.focus ≠ none) (hcan : canRight outer)
    (hsym : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus =
      PalPeg.GalilScaffoldInputHead.read (right outer)) :
    PalPeg.GalilScaffoldChainWatch.Good wm := by
  have hnil : wm.lag.pos = [] := by
    cases h : wm.lag.pos <;> simp_all [PalPeg.GalilScaffoldCounter.zero]
  have hv : position wm.machine.verifier = position outer := by
    have h := hl.2
    simpa only [hnil, List.length_nil, Nat.add_zero] using h
  have hrNext := right_word outer raw hor hcan
  have hpNext := right_present outer raw hor hop hcan
  have hpos := right_position outer hcan (represented_position _ raw hor hop).1
  have hread := represented_read (right outer) raw hrNext hpNext
  have hne : PalPeg.GalilScaffoldInputHead.read (right outer) ≠ none :=
    fun h => hpNext (Option.map_eq_none_iff.1 h)
  have hlt : position outer + 1 < (encoded raw).length := by
    rw [hpos] at hread
    by_contra hn
    exact hne (hread.trans (List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt hn)))
  have hc : canRight wm.machine.verifier := canRight_of_bound _ raw hr hp (by omega)
  have hrv := represented_read (right wm.machine.verifier) raw (right_word _ raw hr hc)
    (right_present _ raw hr hp hc)
  rw [right_position _ hc (represented_position _ raw hr hp).1, hv] at hrv
  rw [hpos] at hread
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hne
  exact ⟨hc, a, hsym.trans ha, hrv.trans (hread.symm.trans ha)⟩

theorem immediate_good (raw : List (Fin 2)) (x : State GalilVM) (hh : Heads raw x.vm)
    (hcan : canRight x.vm.right) {P : Shared} {q : ℕ} {first : Fin 9} {t : GalilVM}
    (hcmp : compareFound P q first x.vm t)
    (hmis : ¬ (galilFrameS P q first).matched t) (hg : shiftGuardVM t)
    (mid : PalPeg.GalilScaffoldChainWatch.State) (hmid : t.chain = .watch mid) :
    PalPeg.GalilScaffoldChainWatch.Good mid := by
  obtain ⟨wm, hw, hi⟩ := PalPeg.WindowPack.source_watch_of_guard hcmp hmis hg
  obtain ⟨hr, hp, hl⟩ := hh.watch wm hw
  obtain ⟨hrm, hpm, hlm⟩ := watch_internal raw _ wm mid hr hp hl (hi mid hmid)
  obtain ⟨other, ho, hz, _, _, _, hsym⟩ := hg
  have heq : other = mid := ChainVM.watch.inj (ho.symm.trans hmid)
  subst other
  have hright : t.right = right x.vm.right :=
    (congrArg GalilVM.right (compare_eq_compareFun hcmp)).trans (PalPeg.PhysicalEncoding.compareFun_cursors P x.vm).2
  rw [hright] at hsym
  exact good_at_right raw x.vm.right mid hrm hpm hlm hz hh.rightRep hh.rightPresent hcan hsym

/-- The final consumer's source run supplies every read/availability premise
of the complete shift-entry step. Only selection of this step in the common
finite dispatcher remains outside this theorem. -/
theorem running_onRun (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ)
    (hpre : PalPeg.CloseoutCheckW.PreTraceIMW centreC placeC 0 1 0 w st Tc)
    (m : PalPeg.LocalReplayParked.Mirrored1 (PalPeg.LocalBlankState.tapeCount 0))
    (p : PalPeg.LocalRoleRouting.Config PalPeg.PhysicalContract.CoreControl
      PalPeg.PhysicalEncoding.Γm PalPeg.PhysicalEncoding.tapeCountM)
    (hon : PalPeg.LocalShadowConcrete.ArrivedOnRun (PalPeg.ShadowedLocalFinal.localGood (spare := 0))
      (PalPeg.ShadowedLocalFinal.postPhase 0 1 0) w
      (PalPeg.ShadowedLocalFinal.heldAfter (Tc w.length) st) m)
    (hnf : ¬ PalPeg.ShadowedLocalFinal.frozenAt w m)
    (he : PalPeg.PhysicalCacheInvariant.Running w (absSC m) (PalPeg.LocalRoleRouting.decode p))
    (hm : (absSC m).ctl.mode = .scan) (hclock : (absSC m).ctl.clock = 1)
    (hs : PalPeg.FrameFunction.starvedTest (absSC m) = false) (t : GalilVM)
    (hcmp : compareFound (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0 (absSC m).vm t)
    (hmis : ¬ (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0).matched t)
    (hg : shiftGuardVM t) :
    ∃ wm : PalPeg.GalilScaffoldChainWatch.State, (absSC m).vm.chain = .watch wm ∧
      PalPeg.PhysicalCacheInvariant.Running w
        (tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
          (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 (absSC m))
        (PalPeg.LocalRoleRouting.decode
          ((PalPeg.PhysicalShiftTick.step (PalPeg.GalilScaffoldCounter.positive wm.lag)).apply
            PalPeg.PhysicalEncoding.blankM p none)) := by
  have hcan : canRight (absSC m).vm.right := by
    apply (canRightTest_iff _).mpr
    simpa [PalPeg.FrameFunction.starvedTest, PalPeg.FrameFunction.starvedOf, hm] using hs
  obtain ⟨arrived, hlen, hh⟩ := heads_onRun w st Tc hpre m hon hnf hm
  obtain ⟨wm, hw, hfirst, hmid⟩ := PalPeg.PhysicalShiftStart.source_of_guard hcmp hmis hg
  have hgood := immediate_good arrived (absSC m) hh hcan hcmp hmis hg _ hmid
  have hblock := (PalPeg.PhysicalChainShape.period_onRun w st Tc hpre m hon.onRun hnf).1
  obtain ⟨old, hold, hinternal⟩ := PalPeg.WindowPack.source_watch_of_guard hcmp hmis hg
  have holdEq : old = wm := ChainVM.watch.inj (hold.symm.trans hw)
  subst old
  have hb := PalPeg.GalilBranchInvariants.blockInv_step
    (ChainStep.watchStep wm _ (hinternal _ hmid)) (hw ▸ hblock)
  obtain ⟨u, hu⟩ := beginShift_exists t hg
  have hout := PalPeg.PhysicalShiftTick.running (PalPeg.GalilScaffoldCounter.positive wm.lag)
    w arrived (absSC m) p he hm wm hw hfirst hgood hcan hh.rightRep hlen
  rw [PalPeg.PhysicalShiftLanding.moved_eq_entry (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w)
    1 0 (absSC m) wm hw t u hcmp hmis hmid hb hu,
    ← PalPeg.PhysicalShiftLanding.tick_eq_entry centreC placeC 0 1 0 w (absSC m) t u
      hm hclock ⟨wm, hw⟩ hcan hcmp hmis hg hu] at hout
  exact ⟨wm, hw, hout⟩

/-- info: 'PalPeg.PhysicalShiftSource.heads_onRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms heads_onRun

/-- info: 'PalPeg.PhysicalShiftSource.running_onRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running_onRun

end PalPeg.PhysicalShiftSource
