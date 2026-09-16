import PalPeg.ProgramFrame

set_option autoImplicit false
set_option maxRecDepth 2048
namespace PalPeg.Program.WarmStart
open PegSeparation.RealTimeTM PalPeg.ProgLangPersist2
variable {Terminal Q Γ : Type} [Fintype Terminal] [DecidableEq Terminal]
  [Fintype Q] [DecidableEq Q] [Fintype Γ] [DecidableEq Γ] {t : ℕ}

abbrev Core (Terminal Q : Type) := Bool × Option Terminal × Q
variable (M : StructuredMachine Terminal Q Γ t 33)

def pack (b : Bool) (p : Option Terminal) (x : SConfig Q Γ t) :
    SConfig (Core Terminal Q) Γ t := ⟨(b, p, x.state), x.tape⟩

def hold : StructuredMachine Terminal (Core Terminal Q) Γ t 33 where
  tapeCount_pos := M.tapeCount_pos
  blank := M.blank
  initial := (true, none, M.initial)
  accepting := fun q => M.accepting q.2.2
  micro := fun q a σ =>
    let d := M.micro q.2.2 a σ
    ((q.1, q.2.1, d.1), d.2)

def initTapes (act : (Fin t → Γ) → Fin t → Γ × Move) (T : Fin t → STape Γ) :=
  fun j => (T j).applyAction M.blank (act (fun i => (T i).focus) j)

/-- Cache each arrival in finite control. On the first arrival only, make
the initial tape moves before forwarding that same arrival to the worker. -/
def body (act : (Fin t → Γ) → Fin t → Γ × Move) :
    PhaseBody Terminal (Core Terminal Q) Γ t 34 := fun q a ph σ =>
  if ph.val = 0 then
    ((false, a, q.2.2), if q.1 then act σ else fun j => (σ j, .stay))
  else (hold M).micro q (if ph.val = 1 then q.2.1 else none) σ

def machine (act : (Fin t → Γ) → Fin t → Γ × Move) :
    StructuredMachine Terminal (Core Terminal Q × Fin 34) Γ t 34 :=
  ofPhases M.tapeCount_pos (by decide) M.blank (true, none, M.initial)
    (fun q => M.accepting q.2.2) (body M act)

def strip (x : SConfig (Core Terminal Q × Fin 34) Γ t) : SConfig (Core Terminal Q) Γ t :=
  ⟨x.state.1, x.tape⟩

def view (x : SConfig (Core Terminal Q × Fin 34) Γ t) : SConfig Q Γ t :=
  ⟨x.state.1.2.2, x.tape⟩

theorem hold_step (b : Bool) (p a : Option Terminal) (x : SConfig Q Γ t) :
    (hold M).sMicroStep (pack b p x) a = pack b p (M.sMicroStep x a) := rfl

theorem hold_steps (b : Bool) (p : Option Terminal) (ops : List (Option Terminal)) (x : SConfig Q Γ t) :
    ops.foldl (hold M).sMicroStep (pack b p x) = pack b p (ops.foldl M.sMicroStep x) := by
  induction ops generalizing x with
  | nil => rfl
  | cons a ops ih => rw [List.foldl_cons, hold_step, ih, List.foldl_cons]

theorem phase_step (act : (Fin t → Γ) → Fin t → Γ × Move)
    (x : SConfig (Core Terminal Q × Fin 34) Γ t) (a : Option Terminal) :
    ((machine M act).sMicroStep x a).state.2 = nextPhase x.state.2 := rfl

theorem inner_step (act : (Fin t → Γ) → Fin t → Γ × Move)
    (x : SConfig (Core Terminal Q × Fin 34) Γ t) (h : x.state.2.val ≠ 0)
    (a : Option Terminal) :
    strip ((machine M act).sMicroStep x a) =
      (hold M).sMicroStep (strip x) (if x.state.2.val = 1 then x.state.1.2.1 else none) := by
  simp only [strip, StructuredMachine.sMicroStep, machine, ofPhases, body, h, ↓reduceIte]
  rfl

theorem tail_steps (act : (Fin t → Γ) → Fin t → Γ × Move) (n : ℕ)
    (x : SConfig (Core Terminal Q × Fin 34) Γ t)
    (hpos : 2 ≤ x.state.2.val) (hlen : x.state.2.val + n ≤ 34) :
    strip ((List.replicate n none).foldl (machine M act).sMicroStep x) =
      (List.replicate n none).foldl (hold M).sMicroStep (strip x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have hs : strip ((machine M act).sMicroStep x none) = (hold M).sMicroStep (strip x) none := by
      rw [inner_step M act x (by omega)]
      simp only [show x.state.2.val ≠ 1 by omega, ↓reduceIte]
    cases n with
    | zero => exact hs
    | succ n =>
      have hnext : x.state.2.val + 1 < 34 := by omega
      have hv : ((machine M act).sMicroStep x none).state.2.val = x.state.2.val + 1 := by
        rw [phase_step]
        simp only [nextPhase, dif_pos hnext]
      rw [List.replicate_succ, List.foldl_cons, ih _ (by rw [hv]; omega) (by rw [hv]; omega), hs]
      rfl

theorem round (act : (Fin t → Γ) → Fin t → Γ × Move)
    (b : Bool) (p : Option Terminal) (q : Q) (T : Fin t → STape Γ) (a : Terminal) :
    strip ((machine M act).sRound ⟨((b, p, q), 0), T⟩ a) =
      pack false (some a) (M.sRound ⟨q, if b then initTapes M act T else T⟩ a) := by
  let x : SConfig (Core Terminal Q × Fin 34) Γ t := ⟨((b, p, q), 0), T⟩
  let x1 := (machine M act).sMicroStep x (some a)
  let x2 := (machine M act).sMicroStep x1 none
  have h1 : x1.state.2.val = 1 := rfl
  have h2 : x2.state.2.val = 2 := rfl
  have hp : x1.state.1.2.1 = some a := rfl
  have hs : strip x1 = pack false (some a) ⟨q, if b then initTapes M act T else T⟩ := by
    cases b <;> rfl
  have ht : strip x2 = pack false (some a)
      (M.sMicroStep ⟨q, if b then initTapes M act T else T⟩ (some a)) := by
    rw [show strip x2 = (hold M).sMicroStep (strip x1)
      (if x1.state.2.val = 1 then x1.state.1.2.1 else none) from inner_step M act x1 (by omega) none,
      h1, hp, if_pos rfl, hs, hold_step]
  rw [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    show List.replicate (34 - 1) (none : Option Terminal) = none :: List.replicate 32 none from rfl,
    List.foldl_cons, List.foldl_cons]
  have hh := tail_steps M act 32 x2 (by omega) (by omega)
  rw [ht, hold_steps] at hh
  exact hh

theorem round_phase (act : (Fin t → Γ) → Fin t → Γ × Move)
    (x : SConfig (Core Terminal Q × Fin 34) Γ t) (hx : x.state.2 = 0) (a : Terminal) :
    ((machine M act).sRound x a).state.2 = 0 := by
  have he : x = ⟨(x.state.1, 0), x.tape⟩ := by rw [← hx]
  rw [he]
  have hh := ofPhases_round M.tapeCount_pos (by decide : 0 < 34) M.blank
    (true, none, M.initial) (fun q : Core Terminal Q => M.accepting q.2.2)
    (body M act) x.state.1 x.tape a
  simpa only [machine, Fin.zero_eta] using congrArg (fun y => y.state.2) hh

theorem round_result (act : (Fin t → Γ) → Fin t → Γ × Move)
    (x : SConfig (Core Terminal Q × Fin 34) Γ t) (hx : x.state.2 = 0) (a : Terminal) :
    let y := (machine M act).sRound x a
    y.state.1.1 = false ∧ y.state.2 = 0 ∧
      view y = M.sRound ⟨x.state.1.2.2, if x.state.1.1 then initTapes M act x.tape else x.tape⟩ a := by
  have he : x = ⟨((x.state.1.1, x.state.1.2.1, x.state.1.2.2), 0), x.tape⟩ := by rw [← hx]
  have hr := round M act x.state.1.1 x.state.1.2.1 x.state.1.2.2 x.tape a
  rw [← he] at hr
  have hphase := round_phase M act x hx a
  generalize hy : (machine M act).sRound x a = y at hr hphase ⊢
  refine ⟨congrArg (fun z => z.state.1) hr, hphase, ?_⟩
  exact congrArg (fun z : SConfig (Core Terminal Q) Γ t =>
    (⟨z.state.2.2, z.tape⟩ : SConfig Q Γ t)) hr

theorem run_ready (act : (Fin t → Γ) → Fin t → Γ × Move) (w : List Terminal)
    (x : SConfig (Core Terminal Q × Fin 34) Γ t)
    (hb : x.state.1.1 = false) (hp : x.state.2 = 0) :
    let y := w.foldl (machine M act).sRound x
    y.state.1.1 = false ∧ y.state.2 = 0 ∧ view y = w.foldl M.sRound (view x) := by
  induction w generalizing x with
  | nil => exact ⟨hb, hp, rfl⟩
  | cons a w ih =>
    have hr := round_result M act x hp a
    simp only [List.foldl_cons]
    generalize hz : (machine M act).sRound x a = z at hr ⊢
    have hs := ih z hr.1 hr.2.1
    simp only [hb, Bool.false_eq_true, ↓reduceIte] at hr
    refine ⟨hs.1, hs.2.1, ?_⟩
    rw [hs.2.2, hr.2.2]
    rfl

/-- Every symbol, including the first, is forwarded exactly once. The only
difference from the inner run is the one-time initial tape action. -/
theorem from_blank (act : (Fin t → Γ) → Fin t → Γ × Move) (a : Terminal) (w : List Terminal) :
    view ((machine M act).srun (a :: w)) =
      (a :: w).foldl M.sRound ⟨M.initial, initTapes M act M.sInit.tape⟩ := by
  have hr := round_result M act (machine M act).sInit rfl a
  rw [StructuredMachine.srun, List.foldl_cons]
  generalize hz : (machine M act).sRound (machine M act).sInit a = z at hr ⊢
  have hs := run_ready M act w z hr.1 hr.2.1
  rw [hs.2.2, hr.2.2]
  rfl

/-- info: 'PalPeg.Program.WarmStart.from_blank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms from_blank

end PalPeg.Program.WarmStart
