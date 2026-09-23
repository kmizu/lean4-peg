import PalPeg.PhysicalProgramErase

/-! A fixed number of eraser actions fits inside a single existing-radius
sweep. Only the four phases are runtime data; the elapsed count below is a
proof witness. A completed phase is sound even when reached before the bound. -/
set_option autoImplicit false
namespace PalPeg.PhysicalEraseBatch
open PalPeg.PhysicalProgramErase PalPeg.PhysicalEncoding
open PalPeg.Program PalPeg.Local PalPeg.CloseoutCoreEnc12 PalPeg.LocalStepFusion

/-- The eraser started on a dense program tape and has made some progress. -/
def Good (r : Raw) : Prop := ∃ t k, Dense t ∧ r = run k (.rewind,t)

theorem good_start (t : STape (Fin 9)) (hd : Dense t) : Good (.rewind,t) := ⟨t,0,hd,rfl⟩

theorem good_run (r : Raw) (h : Good r) (n : ℕ) : Good (run n r) := by
  obtain ⟨t,k,hd,rfl⟩ := h
  exact ⟨t,k+n,hd,(run_add k n _).symm⟩

theorem good_blank : Good (.done,STape.blankTape 6) := by
  refine ⟨STape.blankTape 6,3,?_,rfl⟩
  exact ⟨[],1,by simp, rfl⟩

/-- Reading done is sufficient: the tape is blank at its floor. -/
theorem done_clean (r : Raw) (h : Good r) (hdone : r.1 = .done) :
    STape.BlankEq 6 r.2 (STape.blankTape 6) := by
  obtain ⟨t,k,hd,hr⟩ := h
  let bound := 3*(t.left.length+t.right.length)+5
  have hfinal := reusable t hd (k+bound) (by omega)
  rw [run_add, ← hr, show r = (.done,r.2) from Prod.ext hdone rfl, done_run] at hfinal
  exact hfinal.2

variable {fb db : ℕ}

noncomputable def step (n : ℕ) : LocalStep (Fin 2) (Control fb db) Γm tapeCountM n := by
  have h : iterRadius 1 n = n := by rw [iterRadius_eq, Nat.mul_one]
  exact h ▸ compStep (iterRule bankRule n)

theorem cast_apply {K N : ℕ} (h : K = N)
    (L : LocalStep (Fin 2) (Control fb db) Γm tapeCountM K)
    (p : Control fb db × (Fin tapeCountM → STape Γm)) :
    (h ▸ L).apply blankM p none = L.apply blankM p none := by
  cases h
  rfl

theorem step_spec (n : ℕ) (p : Control fb db × (Fin tapeCountM → STape Γm))
    (hm : ∀ j, n ≤ pos (p.2 j)) :
    ((step n).apply blankM p none).1 = (idealRun bankRule blankM p none n).1 ∧
      ∀ j, TEqG blankM ((idealRun bankRule blankM p none n).2 j)
        (((step n).apply blankM p none).2 j) := by
  have hi : iterRadius 1 n = n := by rw [iterRadius_eq, Nat.mul_one]
  have hs := compStep_iterRule blankM bankRule n p none (fun j => hi.symm ▸ hm j)
  rw [idealIter_eq_idealRun] at hs
  unfold step
  rw [cast_apply]
  exact hs

theorem run_control (n : ℕ) (p : Control fb db × (Fin tapeCountM → STape Γm)) :
    (idealRun bankRule blankM p none n).1.1 = p.1.1 := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => rw [idealRun_succ]; exact ih _

theorem run_kept (n : ℕ) (p : Control fb db × (Fin tapeCountM → STape Γm))
    (j : Fin tapeCountM) (hj : ∀ i, j ≠ slotIndex (dpSlotOf (!p.1.1.dpLive) i)) :
    (idealRun bankRule blankM p none n).2 j = p.2 j := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    rw [idealRun_succ, ih (idealStep bankRule blankM p none) hj]
    have h := bank_kept p (slotIndex.symm j) (by
      intro i hi; apply hj i; rw [← hi, Equiv.apply_symm_apply])
    simpa only [Equiv.apply_symm_apply] using h

theorem run_margin (n m : ℕ) (raw : Fin 12 → Raw)
    (p : Control fb db × (Fin tapeCountM → STape Γm))
    (he : BankRep m raw p) (hm : ∀ j, 1 ≤ pos (p.2 j)) :
    ∀ j, 1 ≤ pos ((idealRun bankRule blankM p none n).2 j) := by
  induction n generalizing raw p with
  | zero => exact hm
  | succ n ih =>
    rw [idealRun_succ]
    exact ih _ _ (bank_ideal m raw p he) (bank_margin m raw p he hm)

/-- The source can be an actual swept representation. The batch runs on its
source windows; it does not assume canonical literal equality. -/
theorem stored (m n : ℕ) (raw : Fin 12 → Raw)
    (p : Control fb db × (Fin tapeCountM → STape Γm)) (he : Stored m raw p)
    (hm : ∀ j, n ≤ pos (p.2 j)) :
    Stored m (fun i => run n (raw i)) ((step n).apply blankM p none) := by
  obtain ⟨T,hT,hpos,ht⟩ := he
  have hTm : ∀ j, iterRadius 1 n ≤ pos (T j) := by
    intro j
    rw [iterRadius_eq, Nat.mul_one, (ht j).1]
    exact hm j
  obtain ⟨hc, hacts⟩ := idealStep_congr_teqG (iterRule bankRule n) blankM p.1 T p.2 ht none
  rw [iterRule_ideal blankM bankRule n (p.1,T) none hTm, idealIter_eq_idealRun,
    iterRule_ideal blankM bankRule n p none (by simpa only [iterRadius_eq,Nat.mul_one] using hm),
    idealIter_eq_idealRun] at hc hacts
  obtain ⟨hq, hs⟩ := step_spec n p hm
  have hb := bank_ideal_run m n raw (p.1,T) hT
  have hp := run_margin n m raw (p.1,T) hT hpos
  refine ⟨(idealRun bankRule blankM (p.1,T) none n).2, ?_, hp,
    fun j => PalPeg.MachineStep.teqG_trans (hacts j) (hs j)⟩
  rw [hq, ← hc]
  exact hb

/-- A fixed batch neither changes the main control nor its chosen live bank. -/
theorem control (n : ℕ) (p : Control fb db × (Fin tapeCountM → STape Γm))
    (hm : ∀ j, n ≤ pos (p.2 j)) : ((step n).apply blankM p none).1.1 = p.1.1 :=
  (congrArg Prod.fst (step_spec n p hm).1).trans (run_control n p)

/- Keep concrete fixed batches opaque to elaboration; their checked step
specification is the public interface. -/
attribute [irreducible] step

/-- info: 'PalPeg.PhysicalEraseBatch.done_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms done_clean

/-- info: 'PalPeg.PhysicalEraseBatch.stored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stored

end PalPeg.PhysicalEraseBatch
