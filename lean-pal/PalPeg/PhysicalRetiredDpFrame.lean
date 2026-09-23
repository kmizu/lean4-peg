import PalPeg.PhysicalLoanInvariant
import PalPeg.PhysicalProgramErase

/-! Retired DP tapes can be changed without changing the current abstract
state. This frame fact covers the actual shared encoding, including cache,
restart snapshots and the borrowed radius mirror. -/
set_option autoImplicit false
namespace PalPeg.PhysicalRetiredDpFrame
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.PhysicalCacheInvariant (CoreInv Running)
open PalPeg.PhysicalDebtMirror (RebuildingCore Rebuilding repaired repair)
open PalPeg.PhysicalShiftDispatch (RoutedCore RoutedState liftConfig)
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.Program PalPeg.Local PalPeg.CloseoutCoreEnc12

def Retired (q : CoreControl) (j : Fin tapeCountM) : Prop :=
  ∃ i : Fin 12, j = slotIndex (dpSlotOf (!q.dpLive) i)

theorem retired_iff (q : CoreControl) (slot : Slot) :
    Retired q (slotIndex slot) ↔ ∃ i, slot = dpSlotOf (!q.dpLive) i := by
  simp [Retired]

theorem not_retired_counter (q : CoreControl) (c : Fin 16) : ¬ Retired q (slotIndex (counterSlot c)) := by
  simp only [retired_iff, not_exists]
  intro i
  cases q.dpLive <;> simp [dpSlotOf,counterSlot]

theorem not_retired_mirror (q : CoreControl) (m : Fin 7) : ¬ Retired q (slotIndex (mirrorSlot m)) := by
  simp only [retired_iff, not_exists]
  intro i
  cases q.dpLive <;> simp [dpSlotOf,mirrorSlot]

def Kept (q : CoreControl) (T U : Fin tapeCountM → STape Γm) : Prop :=
  ∀ j, ¬ Retired q j → U j = T j

def Outside (q : CoreControl) (T U : Fin tapeCountM → STape Γm) : Prop :=
  ∀ j, ¬ Retired q j → TEqG blankM (T j) (U j)

def Margin (U : Fin tapeCountM → STape Γm) : Prop := ∀ j, margin ≤ pos (U j)

theorem core (w : List (Fin 2)) (x : State GalilVM) (q : CoreControl)
    (T U : Fin tapeCountM → STape Γm) (he : CoreInv w x (q,T))
    (hk : Kept q T U) (hm : Margin U) : CoreInv w x (q,U) := by
  refine ⟨⟨⟨⟨he.1.1.1.1, ?_⟩, he.1.1.2⟩, ?_⟩, ?_⟩
  · apply PalPeg.PhysicalProgramErase.encTapes_retired_dp he.1.1.1.2
    · intro slot hs
      apply hk
      rintro ⟨i,hi⟩
      have hh : slot = dpSlotOf (!q.dpLive) i := slotIndex.injective hi
      rw [hh, PalPeg.PhysicalProgramErase.carrier_at] at hs
      contradiction
    · intro slot; exact hm (slotIndex slot)
  · intro c
    change ∃ seg, U (slotIndex (counterSlot c)) = padLeft margin (mapTape encSeg seg)
    rw [hk _ (not_retired_counter q c)]
    exact he.1.2 c
  · have hsp := hk _ (not_retired_counter q 10)
    have hmir := hk _ (not_retired_mirror q 5)
    simpa only [PalPeg.PhysicalSpare.spareIndex,PalPeg.PhysicalPeriodMirror.mirrorIndex,hsp,hmir] using he.2

theorem repair_kept (q : CoreControl) (T U : Fin tapeCountM → STape Γm) (hk : Kept q T U) :
    Kept q (repaired T) (repaired U) := by
  intro j hj
  unfold repaired repair
  split
  · exact hk _ (not_retired_mirror q 0)
  · exact hk _ (by simpa only [Equiv.apply_symm_apply] using hj)

theorem repair_margin (U : Fin tapeCountM → STape Γm) (hm : Margin U) : Margin (repaired U) := by
  intro j
  unfold repaired repair
  split <;> apply hm

theorem rebuilding_core (w : List (Fin 2)) (x : State GalilVM) (q : CoreControl)
    (T U : Fin tapeCountM → STape Γm) (he : RebuildingCore w x (q,T))
    (hk : Kept q T U) (hm : Margin U) : RebuildingCore w x (q,U) := by
  refine ⟨core w x q (repaired T) (repaired U) he.1 (repair_kept q T U hk) (repair_margin U hm), ?_⟩
  obtain ⟨seg,ha,ht⟩ := he.2
  exact ⟨seg,ha,(hk _ (not_retired_mirror q 2)).trans ht⟩

noncomputable def patch (q : CoreControl) (T U : Fin tapeCountM → STape Γm) (j : Fin tapeCountM) : STape Γm := by
  classical
  exact if Retired q j then U j else T j

theorem patch_kept (q : CoreControl) (T U : Fin tapeCountM → STape Γm) : Kept q T (patch q T U) := by
  intro j hj; simp [patch,hj]

theorem closure (E : State GalilVM → CoreState → Prop)
    (hframe : ∀ x q T U, E x (q,T) → Kept q T U → Margin U → E x (q,U))
    (hmargin : ∀ x q T, E x (q,T) → Margin T)
    (x : State GalilVM) (q : CoreControl) (T U : Fin tapeCountM → STape Γm)
    (he : PalPeg.MachineStep.sweepClosure blankM E x (q,T))
    (hk : Outside q T U) (hm : ∀ j, Retired q j → margin ≤ pos (U j)) :
    PalPeg.MachineStep.sweepClosure blankM E x (q,U) := by
  obtain ⟨V,hV,hv⟩ := he
  refine ⟨patch q V U,hframe x q V _ hV (patch_kept q V U) ?_,?_⟩
  · intro j
    by_cases hj : Retired q j
    · simpa only [patch,if_pos hj] using hm j hj
    · simpa only [patch,if_neg hj] using hmargin x q V hV j
  · intro j
    by_cases hj : Retired q j
    · simp only [patch,if_pos hj]
      exact ⟨rfl,fun _ => rfl⟩
    · simp only [patch,if_neg hj]
      exact PalPeg.MachineStep.teqG_trans (hv j) (hk j hj)

theorem running (w : List (Fin 2)) (x : State GalilVM) (q : CoreControl)
    (T U : Fin tapeCountM → STape Γm) (he : Running w x (q,T))
    (hk : Outside q T U) (hm : ∀ j, Retired q j → margin ≤ pos (U j)) : Running w x (q,U) := by
  apply closure (CoreInv w) (core w) ?_ x q T U he hk hm
  intro y c V hV j
  have h := hV.1.1.1.2.margins (slotIndex.symm j)
  simpa only [Equiv.apply_symm_apply] using h

theorem rebuilding (w : List (Fin 2)) (x : State GalilVM) (q : CoreControl)
    (T U : Fin tapeCountM → STape Γm) (he : Rebuilding w x (q,T))
    (hk : Outside q T U) (hm : ∀ j, Retired q j → margin ≤ pos (U j)) : Rebuilding w x (q,U) := by
  exact closure (RebuildingCore w) (rebuilding_core w)
    (fun y c V hV => PalPeg.PhysicalDebtRebuild.core_margin w y (c,V) hV) x q T U he hk hm

theorem old_routed (w : List (Fin 2)) (x : State GalilVM) (p : RoutedCore)
    (U : Fin tapeCountM → STape Γm)
    (he : PalPeg.PhysicalSnapshotInvariant.OldEnc w x (liftConfig p))
    (hk : Outside p.1.2 (fun j => p.2 (p.1.1 j)) (fun j => U (p.1.1 j)))
    (hm : ∀ j, Retired p.1.2 j → margin ≤ pos (U (p.1.1 j))) :
    PalPeg.PhysicalSnapshotInvariant.OldEnc w x (liftConfig (p.1,U)) :=
  running w x p.1.2 _ _ he hk hm

/-- The unchanged common Loan encoding accepts the concurrent cleanup's
result whenever only its retired DP tapes change and their margin is kept. -/
theorem loan (w : List (Fin 2)) (x : State GalilVM) (p : RoutedCore)
    (U : Fin tapeCountM → STape Γm)
    (he : PalPeg.PhysicalLoanInvariant.Enc w x (liftConfig p))
    (hk : Outside p.1.2 (fun j => p.2 (p.1.1 j)) (fun j => U (p.1.1 j)))
    (hm : ∀ j, Retired p.1.2 j → margin ≤ pos (U (p.1.1 j))) :
    PalPeg.PhysicalLoanInvariant.Enc w x (liftConfig (p.1,U)) := by
  by_cases hn : PalPeg.PhysicalLoanInvariant.NeedsLoan x
  · obtain ⟨hb,hr⟩ := (PalPeg.PhysicalLoanInvariant.enc_partial w x _ hn).mp he
    apply (PalPeg.PhysicalLoanInvariant.enc_partial w x _ hn).mpr
    exact ⟨hb,rebuilding w x p.1.2 _ _ hr hk hm⟩
  · have hs := (PalPeg.PhysicalLoanInvariant.enc_full w x _ hn).mp he
    apply (PalPeg.PhysicalLoanInvariant.enc_full w x _ hn).mpr
    exact PalPeg.PhysicalSnapshotInvariant.preserve w x _ _ hs
      (fun y _ hy => old_routed w y p U hy hk hm)

/-- info: 'PalPeg.PhysicalRetiredDpFrame.running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running

/-- info: 'PalPeg.PhysicalRetiredDpFrame.loan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms loan

end PalPeg.PhysicalRetiredDpFrame
