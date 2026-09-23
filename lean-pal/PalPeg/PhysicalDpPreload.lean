import PalPeg.PhysicalDpDensity
import PalPeg.GalilScaffoldPrepareControl

/-! The DP bank may be retired before preload finishes. Every prefix of the
actual lower/source preparation keeps all twelve tapes dense. The loading
heads are at the first blank; no completed preload is assumed. -/
set_option autoImplicit false
namespace PalPeg.PhysicalDpPreload
open PalPeg.GalilScaffoldTape
open PalPeg.GalilScaffoldPrepareControl
open PalPeg.GalilFppFrontier (Shape)
open PalPeg.PhysicalEncoding (encTape)
open PalPeg.PhysicalProgramErase (Dense)

def Solid (t : Tape) : Prop := ∃ n, Shape (denote t) n
def Frontier (t : Tape) : Prop := Shape (denote t) (head t)

theorem reset_frontier : Frontier reset := by
  rw [Frontier,reset_head,reset_blank]
  exact ⟨by omega,by simp⟩

theorem reset_solid : Solid reset := ⟨0,reset_frontier⟩

theorem write_solid (t : Tape) (s : Fin 9) (ht : Frontier t) (hs : s ≠ 6) :
    Solid (write t s) := by
  refine ⟨head t+1,?_⟩
  rw [write_denote]
  simpa only [if_true] using PalPeg.GalilFppFrontier.write_shape
    (denote t) (head t) (head t) s ht (Nat.le_refl _) hs

theorem append_frontier (t : Tape) (s : Fin 9) (ht : Frontier t) (hs : s ≠ 6) :
    Frontier (moveRight (write t s)) := by
  rw [Frontier,right_denote,right_head,write_head,write_denote]
  simpa only [if_true] using PalPeg.GalilFppFrontier.write_shape
    (denote t) (head t) (head t) s ht (Nat.le_refl _) hs

theorem left_solid (t : Tape) (ht : Solid t) : Solid (moveLeft t) := by
  simpa only [Solid,left_denote] using ht

structure Inv (x : State) : Prop where
  solid : ∀ i, Solid (x.program.config.tapes i)
  lower : x.mode = .lower → Frontier (x.program.config.tapes 10)
  untouched : x.mode = .lower ∨ x.mode = .lowerHome → x.program.config.tapes 7 = reset
  source : x.mode = .copy → Frontier (x.program.config.tapes 7)

theorem tape_solid (x : State) (i : Fin 12) (f : Tape → Tape)
    (hx : ∀ j, Solid (x.program.config.tapes j)) (hf : Solid (f (x.program.config.tapes i))) :
    ∀ j, Solid ((tape x i f).config.tapes j) := by
  intro j
  by_cases hj : j = i
  · simpa [tape,GalilScaffoldLoading.put,hj] using hf
  · simpa [tape,GalilScaffoldLoading.put,hj] using hx j

theorem tick_inv {x y : State} {b : Bool} (ht : Tick b x y) (hx : Inv x) : Inv y := by
  cases ht with
  | idle => exact hx
  | lowerBit x hm hp =>
    have hf := append_frontier _ 8 (hx.lower hm) (by decide)
    refine ⟨tape_solid x 10 _ hx.solid ⟨_,hf⟩,?_,?_,?_⟩
    · intro _; simpa [tape,GalilScaffoldLoading.put] using hf
    · intro _; simpa [tape,GalilScaffoldLoading.put] using hx.untouched (Or.inl hm)
    · simp [hm]
  | lowerEnd x hm hp =>
    refine ⟨tape_solid x 10 _ hx.solid (write_solid _ 5 (hx.lower hm) (by decide)),?_,?_,?_⟩
    · simp
    · intro _; simpa [tape,GalilScaffoldLoading.put] using hx.untouched (Or.inl hm)
    · simp
  | lowerLeft x hm hf hl =>
    refine ⟨tape_solid x 10 _ hx.solid (left_solid _ (hx.solid 10)),?_,?_,?_⟩
    · simp [hm]
    · intro _; simpa [tape,GalilScaffoldLoading.put] using hx.untouched (Or.inr hm)
    · simp [hm]
  | beginCopy x hm hf =>
    have h7 := hx.untouched (Or.inr hm)
    have hs := append_frontier _ 4 reset_frontier (by decide)
    refine ⟨tape_solid x 7 _ hx.solid ?_,?_,?_,?_⟩
    · rw [h7]; exact ⟨_,hs⟩
    · simp
    · simp
    · intro _; simpa [tape,GalilScaffoldLoading.put,h7] using hs
  | copyBit x a hm ha hw =>
    have hf := append_frontier _ (PalPeg.GalilFppPreparation.symbol a) (hx.source hm)
      ((by decide : ∀ a : Fin 3, PalPeg.GalilFppPreparation.symbol a ≠ 6) a)
    refine ⟨tape_solid x 7 _ hx.solid ⟨_,hf⟩,?_,?_,?_⟩
    · simp [hm]
    · simp [hm]
    · intro _; simpa [tape,GalilScaffoldLoading.put] using hf
  | copyEnd x hm he =>
    refine ⟨tape_solid x 7 _ hx.solid (write_solid _ 5 (hx.source hm) (by decide)),?_,?_,?_⟩ <;> simp
  | sourceLeft x hm hf hl =>
    refine ⟨tape_solid x 7 _ hx.solid (left_solid _ (hx.solid 7)),?_,?_,?_⟩ <;> simp [hm]
  | startRun x hm hf =>
    refine ⟨hx.solid,?_,?_,?_⟩ <;> simp

theorem prepare_inv (x : State) (lower : PalPeg.GalilScaffoldCounter.Counter)
    (center : PalPeg.GalilScaffoldPlace.Place) : Inv (prepare x lower center) := by
  have hf := append_frontier reset 4 reset_frontier (by decide)
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    by_cases hi : i = 10
    · simpa [prepare,GalilScaffoldLoading.put,hi] using (show Solid _ from ⟨_,hf⟩)
    · simpa [prepare,GalilScaffoldLoading.put,GalilScaffoldControl.reset,hi] using reset_solid
  · intro _; simpa [prepare,GalilScaffoldLoading.put] using hf
  · intro _; simp [prepare,GalilScaffoldLoading.put,GalilScaffoldControl.reset]
  · simp [prepare]

theorem run_inv {x y : State} {bs : List Bool} (hr : Run x bs y) (hx : Inv x) : Inv y := by
  induction hr with
  | nil => exact hx
  | cons x y z b bs ht hr ih => exact ih (tick_inv ht hx)

/-- Includes disabled ticks and cancellation during any of the four loading
phases; the caller need not provide a final preload or a density premise. -/
theorem dense_onRun (x : State) (lower : PalPeg.GalilScaffoldCounter.Counter)
    (center : PalPeg.GalilScaffoldPlace.Place) {y : State} {bs : List Bool}
    (hr : Run (prepare x lower center) bs y) :
    ∀ i, Dense (encTape (y.program.config.tapes i)) := by
  have hh := run_inv hr (prepare_inv x lower center)
  intro i
  obtain ⟨n,hn⟩ := hh.solid i
  exact PalPeg.PhysicalDpDensity.dense_of_shape _ n hn

open PalPeg.PhysicalDpDensity (size)

theorem tape_size (x : State) (i : Fin 12) (f : Tape → Tape)
    (hf : size (f (x.program.config.tapes i)) ≤ size (x.program.config.tapes i)+1) :
    ∀ j, size ((tape x i f).config.tapes j) ≤ size (x.program.config.tapes j)+1 := by
  intro j
  by_cases hj : j = i
  · simpa [tape,GalilScaffoldLoading.put,hj] using hf
  · simp [tape,GalilScaffoldLoading.put,hj]

theorem tick_size {x y : State} {b : Bool} (ht : Tick b x y) (i : Fin 12) :
    size (y.program.config.tapes i) ≤ size (x.program.config.tapes i)+(if b then 1 else 0) := by
  cases ht with
  | idle => simp
  | lowerBit x _ _ | beginCopy x _ _ | copyBit x _ _ _ _ =>
    apply tape_size x _ _ ?_ i
    simpa only [size,write] using PalPeg.PhysicalDpDensity.size_right (write _ _)
  | lowerEnd x _ _ | copyEnd x _ _ => exact tape_size x _ _ (by simp [size,write]) i
  | lowerLeft x _ _ _ | sourceLeft x _ _ _ =>
    exact tape_size x _ _ (PalPeg.PhysicalDpDensity.size_left _) i
  | startRun => simp [GalilScaffoldControl.start]

theorem run_size {x y : State} {bs : List Bool} (hr : Run x bs y) (i : Fin 12) :
    size (y.program.config.tapes i) ≤ size (x.program.config.tapes i)+bs.count true := by
  induction hr with
  | nil => simp
  | cons x y z b bs ht hr ih =>
    have hh := tick_size ht i
    cases b <;> simp at * <;> omega

/-- A partial preload needs no whole-stage cost estimate: each enabled
preparation row grows each tape by at most one cell. -/
theorem prepare_run_size (x : State) (lower : PalPeg.GalilScaffoldCounter.Counter)
    (center : PalPeg.GalilScaffoldPlace.Place) {y : State} {bs : List Bool}
    (hr : Run (prepare x lower center) bs y) (i : Fin 12) :
    size (y.program.config.tapes i) ≤ 1+bs.count true := by
  have hh := run_size hr i
  have hi : size ((prepare x lower center).program.config.tapes i) ≤ 1 := by
    by_cases hi : i = 10 <;>
      simp [prepare,GalilScaffoldLoading.put,GalilScaffoldControl.reset,hi,size,reset,moveRight,write]
  omega

/-- info: 'PalPeg.PhysicalDpPreload.dense_onRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dense_onRun

/-- info: 'PalPeg.PhysicalDpPreload.prepare_run_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prepare_run_size

end PalPeg.PhysicalDpPreload
