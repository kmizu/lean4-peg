import PalPeg.GalilScaffoldTopFallback

/-!
# Fpp-mode instantiation of the controller frame

`stepFpp` runs up to `quantum` instructions of the FPP program per tick and,
at the halt, marks the new place (`marks.move(1); marks.write(FIRST);
marks.move(1)`) and switches to `MarkEnd`. This module instantiates
`fppSlice`/`fppDone` with `GalilScaffoldControl.Run` of the marked FPP code
over `quantum` enabled ticks (idle after the halt), proves determinism and
splitting of control runs, and lifts the scheduled FPP run of
`fpp_scheduled` to a run of controller ticks from `fpp` to `markEnd`.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController

set_option maxRecDepth 100000 in
theorem marked_wellFormed : ∀ i ∈ GalilFppMarkedCode.code, GalilScaffoldNextPc.WellFormed i := by
  decide

theorem control_run_unique {n : ℕ} {code : List (GalilFppWide.Instruction n)}
    (hw : ∀ i ∈ code, GalilScaffoldNextPc.WellFormed i) :
    ∀ {bs : List Bool} {x y y' : GalilScaffoldControl.Machine n},
      GalilScaffoldControl.Run code x bs y → GalilScaffoldControl.Run code x bs y' → y = y' := by
  intro bs
  induction bs with
  | nil =>
    intro x y y' h1 h2
    cases h1; cases h2; rfl
  | cons b bs ih =>
    intro x y y' h1 h2
    cases h1 with
    | cons _ m _ _ _ ht hr =>
      cases h2 with
      | cons _ m' _ _ _ ht' hr' =>
        have := control_tick_unique hw ht ht'
        subst this
        exact ih hr hr'

theorem control_run_split {n : ℕ} {code : List (GalilFppWide.Instruction n)} :
    ∀ {as : List Bool} {bs : List Bool} {x z : GalilScaffoldControl.Machine n},
      GalilScaffoldControl.Run code x (as ++ bs) z →
      ∃ y, GalilScaffoldControl.Run code x as y ∧ GalilScaffoldControl.Run code y bs z := by
  intro as
  induction as with
  | nil => intro bs x z h; exact ⟨x, .nil x, h⟩
  | cons a as ih =>
    intro bs x z h
    rw [List.cons_append] at h
    cases h with
    | cons _ m _ _ _ ht hr =>
      obtain ⟨y, h1, h2⟩ := ih hr
      exact ⟨y, .cons _ _ _ _ _ ht h1, h2⟩

/-- `marks.move(1); marks.write(FIRST); marks.move(1)` on the halted program. -/
def markNew (p : GalilScaffoldControl.Machine 9) (first : Fin 9) : GalilScaffoldControl.Machine 9 :=
  {p with config := GalilScaffoldLoading.put p.config 8 (GalilScaffoldTape.moveRight (GalilScaffoldTape.write (GalilScaffoldTape.moveRight (p.config.tapes 8)) first))}

def fppFrame (q : ℕ) (first : Fin 9) (onLetter leftFirst : FppControl.State → Prop) :
    Frame FppControl.State where
  init := fun _ _ => False
  available := fun _ => False
  background := fun _ _ => False
  compare := fun _ _ => False
  matched := fun _ => False
  shiftGuard := fun _ => False
  matchedPlace := fun _ _ _ => False
  replayExhausted := fun _ => false
  onLetter := onLetter
  leftFirst := leftFirst
  beginShift := fun _ _ => False
  beginFallback := fun _ _ => False
  remainingPos := fun _ => False
  shiftOne := fun _ _ => False
  copyOne := fun _ _ => False
  copyEnd := fun _ _ => False
  atLeft := fun _ => False
  fppStart := fun _ _ => False
  homeStep := fun _ _ => False
  fppSlice := fun x y => x.mode = .run ∧
    GalilScaffoldControl.Run GalilFppMarkedCode.code x.program (List.replicate q true) y.program ∧
    y.program.done = false ∧ y = {x with program := y.program}
  fppDone := fun x y => x.mode = .run ∧ ∃ p : GalilScaffoldControl.Machine 9,
    GalilScaffoldControl.Run GalilFppMarkedCode.code x.program (List.replicate q true) p ∧
    p.done = true ∧ y = {x with program := markNew p first}
  atEnd := fun _ => False
  markBack := fun _ _ => False
  markForward := fun _ _ => False
  markSet := fun _ => False
  choose := fun _ _ => False
  atFirst := fun _ => False
  fppReset := fun _ _ => False
  rewindOne := fun _ _ => False
  rewindPair := fun _ _ => False
  replayStart := fun _ _ => False
  replayPos := fun _ => false
  restart := fun _ _ => False

/-- The controller-visible outcome of the fpp phase: a halted program `p`
reached by `(n+1)·q` enabled ticks, marked, in `markEnd` mode; walker, work
and stage flag untouched. -/
def FppOutcome (q : ℕ) (first : Fin 9) (onLetter leftFirst : FppControl.State → Prop) (delay : ℕ)
    (c : Control) (x : FppControl.State) : Prop :=
  ∃ (n : ℕ) (p : GalilScaffoldControl.Machine 9) (y : FppControl.State),
    Steps (fppFrame q first onLetter leftFirst) delay (n+1) ⟨c, x⟩ ⟨{c with mode := .markEnd}, y⟩ ∧
    y.program = markNew p first ∧ y.mode = .run ∧ y.walker = x.walker ∧ y.work = x.work ∧
    y.finalStage = x.finalStage ∧ p.done = true ∧
    GalilScaffoldControl.Run GalilFppMarkedCode.code x.program (List.replicate ((n+1)*q) true) p

theorem count_true_replicate (k : ℕ) : (List.replicate k true).count true = k := by
  simp

/-- Slicing invariant: after `m` slices either the program is still running
(and the controller has taken `m` `fpp_slice` ticks) or the phase has ended. -/
theorem fpp_slices (q : ℕ) (first : Fin 9) (onLetter leftFirst : FppControl.State → Prop)
    (delay : ℕ) (c : Control) (hm : c.mode = .fpp) (x : FppControl.State) (hx : x.mode = .run)
    (M : ℕ) (v : GalilScaffoldProgram.Config 9)
    (hbig : GalilScaffoldControl.Run GalilFppMarkedCode.code x.program (List.replicate (M*q) true) ⟨v,true⟩) :
    ∀ m, m ≤ M →
      (∃ y : FppControl.State, Steps (fppFrame q first onLetter leftFirst) delay m ⟨c, x⟩ ⟨c, y⟩ ∧
        y.mode = .run ∧ y.walker = x.walker ∧ y.work = x.work ∧ y.finalStage = x.finalStage ∧
        GalilScaffoldControl.Run GalilFppMarkedCode.code x.program (List.replicate (m*q) true) y.program ∧
        y.program.done = false) ∨
      FppOutcome q first onLetter leftFirst delay c x := by
  intro m
  induction m with
  | zero =>
    intro _
    by_cases hd : x.program.done = true
    · -- already halted: the first slice is idle and ends the phase
      right
      obtain ⟨y1, h1, _⟩ := control_run_split (as := List.replicate 0 true)
        (bs := List.replicate (M*q) true) (by simpa using hbig)
      -- an all-idle run of `q` ticks from a halted program
      have hidle : ∀ k, GalilScaffoldControl.Run GalilFppMarkedCode.code x.program
          (List.replicate k true) x.program := by
        intro k
        induction k with
        | zero => exact .nil _
        | succ k ih =>
          rw [List.replicate_succ]
          exact .cons _ _ _ _ _ (.idle _ _ (Or.inr hd)) ih
      refine ⟨0, x.program, {x with program := markNew x.program first}, ?_, rfl, hx, rfl, rfl, rfl, hd, ?_⟩
      · refine .succ (GalilScaffoldTop.Tick.fpp_done c x _ hm ⟨hx, x.program, hidle q, hd, rfl⟩) (.zero _)
      · simpa using hidle q
    · left
      refine ⟨x, .zero _, hx, rfl, rfl, rfl, by simpa using GalilScaffoldControl.Run.nil x.program, ?_⟩
      cases h : x.program.done
      · rfl
      · exact absurd h hd
  | succ m ih =>
    intro hle
    rcases ih (Nat.le_of_succ_le hle) with ⟨y, hs, hym, hyw, hyk, hyf, hyr, hyd⟩ | hout
    · -- split the scheduled run at `m*q` and `(m+1)*q`
      have hsplit : List.replicate (M*q) true =
          List.replicate (m*q) true ++ (List.replicate q true ++ List.replicate ((M-(m+1))*q) true) := by
        rw [← List.replicate_add, ← List.replicate_add]
        congr 1
        have : M*q = m*q + q + (M-(m+1))*q := by
          rw [← Nat.succ_mul, ← Nat.add_mul]
          congr 1
          omega
        omega
      rw [hsplit] at hbig
      obtain ⟨y1, h1, h2⟩ := control_run_split hbig
      obtain ⟨y2, h21, _⟩ := control_run_split h2
      have hy1 : y1 = y.program := control_run_unique marked_wellFormed h1 hyr
      subst hy1
      have hrun : GalilScaffoldControl.Run GalilFppMarkedCode.code x.program
          (List.replicate ((m+1)*q) true) y2 := by
        rw [Nat.succ_mul, List.replicate_add]
        exact control_run_append hyr h21
      by_cases hd : y2.done = true
      · right
        refine ⟨m, y2, {y with program := markNew y2 first}, ?_, rfl, hym, hyw, hyk, hyf, hd, hrun⟩
        exact steps_trans hs (.succ (GalilScaffoldTop.Tick.fpp_done c y _ hm ⟨hym, y2, h21, hd, rfl⟩) (.zero _))
      · left
        have hd' : y2.done = false := by
          cases h : y2.done
          · rfl
          · exact absurd h hd
        refine ⟨{y with program := y2}, ?_, hym, hyw, hyk, hyf, hrun, hd'⟩
        exact steps_trans hs (.succ (GalilScaffoldTop.Tick.fpp_slice c y _ hm ⟨hym, h21, hd', rfl⟩) (.zero _))
    · exact Or.inr hout

/-- The fpp phase: from a running program that the scheduled run halts within
`M·q` ticks, the controller reaches `markEnd` with the marked halted program. -/
theorem fpp_phase_lift (q : ℕ) (first : Fin 9) (onLetter leftFirst : FppControl.State → Prop)
    (delay : ℕ) (c : Control) (hm : c.mode = .fpp) (x : FppControl.State) (hx : x.mode = .run)
    (M : ℕ) (v : GalilScaffoldProgram.Config 9)
    (hbig : GalilScaffoldControl.Run GalilFppMarkedCode.code x.program (List.replicate (M*q) true) ⟨v,true⟩) :
    FppOutcome q first onLetter leftFirst delay c x := by
  rcases fpp_slices q first onLetter leftFirst delay c hm x hx M v hbig M (le_refl _) with
    ⟨y, _, _, _, _, _, hyr, hyd⟩ | hout
  · exfalso
    have := control_run_unique marked_wellFormed hyr hbig
    rw [this] at hyd
    cases hyd
  · exact hout

/-- Instance on the prepared FPP program of `fpp_scheduled`: the phase halts
within `⌈(1584·|w|+830)/q⌉` slices. -/
theorem fpp_phase_scheduled (q : ℕ) (hq : 0 < q) (first : Fin 9)
    (onLetter leftFirst : FppControl.State → Prop) (delay : ℕ) (c : Control) (hm : c.mode = .fpp)
    (x : FppControl.State) (hx : x.mode = .run) (w : List (Fin 3))
    (hp : x.program = ⟨fppInitial w, false⟩) :
    FppOutcome q first onLetter leftFirst delay c x := by
  obtain ⟨v, _, _, _, _, hrun⟩ := fpp_scheduled w
  have hM : 1584*w.length+830 ≤ ((1584*w.length+830)/q + 1) * q := by
    have := Nat.lt_div_mul_add (a := 1584*w.length+830) hq
    rw [Nat.add_mul, Nat.one_mul]
    omega
  apply fpp_phase_lift q first onLetter leftFirst delay c hm x hx ((1584*w.length+830)/q + 1) v
  rw [hp]
  apply hrun
  rw [count_true_replicate]
  exact hM

#print axioms fpp_phase_lift
#print axioms fpp_phase_scheduled

end PalPeg.GalilScaffoldChainInputSupply
