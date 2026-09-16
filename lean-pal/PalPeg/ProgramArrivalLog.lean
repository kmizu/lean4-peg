import PalPeg.ProgramFrame

set_option autoImplicit false
namespace PalPeg.Program.ArrivalLog
open PegSeparation.RealTimeTM PalPeg.ProgLangPersist2
variable {Q Γ Terminal : Type} [Fintype Q] [DecidableEq Q]
  [Fintype Γ] [DecidableEq Γ] {t : ℕ}

def addr (j : Fin t) : Fin (t + 1) := ⟨j.val, by omega⟩
def logAddr : Fin (t + 1) := ⟨t, by omega⟩

/-- A unit-input worker plus a disjoint, append-only arrival log. Each
worker tick executes one original round; it cannot touch the log tape. -/
def worker (M : StructuredMachine Unit Q Γ t 1) :
    StructuredMachine Terminal Q Γ (t + 1) 1 where
  tapeCount_pos := by omega
  blank := M.blank
  initial := M.initial
  accepting := M.accepting
  micro := fun q _ σ =>
    let d := M.micro q (some ()) (fun j => σ (addr j))
    (d.1, fun j => if h : j.val < t then d.2 ⟨j.val, h⟩ else (σ j, .stay))

def capture (enc : Terminal → Γ) : ArriveAct Terminal Γ (t + 1) :=
  fun a σ j => match a with
    | none => (σ j, .stay)
    | some a => if j = logAddr then (enc a, .right) else (σ j, .stay)

def machine (M : StructuredMachine Unit Q Γ t 1) (enc : Terminal → Γ) (C : ℕ) :=
  frameMachine (worker M) (capture enc) C

def project (x : SConfig Q Γ (t + 1)) : SConfig Q Γ t :=
  ⟨x.state, fun j => x.tape (addr j)⟩

def view {C : ℕ} (x : SConfig (Q × Fin (C + 1)) Γ (t + 1)) : SConfig Q Γ t :=
  project ⟨x.state.1, x.tape⟩

def ticks (M : StructuredMachine Unit Q Γ t 1) (n : ℕ) (x : SConfig Q Γ t) :=
  (List.replicate n ()).foldl M.sRound x

theorem ticks_add (M : StructuredMachine Unit Q Γ t 1) (n m : ℕ) (x : SConfig Q Γ t) :
    ticks M (n + m) x = ticks M m (ticks M n x) := by
  simp only [ticks, List.replicate_add, List.foldl_append]

theorem worker_project (M : StructuredMachine Unit Q Γ t 1)
    (x : SConfig Q Γ (t + 1)) (a : Option Terminal) :
    project ((worker M).sMicroStep x a) = M.sRound (project x) () := by
  simp only [project, StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
    StructuredMachine.sMicroStep, worker, addr, Fin.isLt, ↓reduceDIte]

theorem steps_project (M : StructuredMachine Unit Q Γ t 1)
    (ops : List (Option Terminal)) (x : SConfig Q Γ (t + 1)) :
    project (ops.foldl (worker M).sMicroStep x) = ticks M ops.length (project x) := by
  induction ops generalizing x with
  | nil => rfl
  | cons a ops ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, worker_project]
    rfl

theorem worker_log (M : StructuredMachine Unit Q Γ t 1)
    (x : SConfig Q Γ (t + 1)) (a : Option Terminal) :
    ((worker M).sMicroStep x a).tape logAddr = x.tape logAddr := by
  simp only [StructuredMachine.sMicroStep, worker, logAddr, Nat.lt_irrefl, ↓reduceDIte]
  rfl

theorem steps_log (M : StructuredMachine Unit Q Γ t 1)
    (ops : List (Option Terminal)) (x : SConfig Q Γ (t + 1)) :
    (ops.foldl (worker M).sMicroStep x).tape logAddr = x.tape logAddr := by
  induction ops generalizing x with
  | nil => rfl
  | cons a ops ih => exact (ih _).trans (worker_log M x a)

theorem capture_project (M : StructuredMachine Unit Q Γ t 1) (enc : Terminal → Γ)
    (q : Q) (T : Fin (t + 1) → STape Γ) (a : Terminal) :
    project ⟨q, arriveA M.blank (capture enc) (some a) T⟩ = project ⟨q, T⟩ := by
  have hn (j : Fin t) : addr j ≠ logAddr := by
    intro h
    have he := congrArg Fin.val h
    change j.val = t at he
    omega
  simp only [project, arriveA, capture, hn, ↓reduceIte]
  rfl

theorem round (M : StructuredMachine Unit Q Γ t 1) (enc : Terminal → Γ) (C : ℕ)
    (q : Q) (T : Fin (t + 1) → STape Γ) (a : Terminal)
    (out : List Γ) (h : T logAddr = ⟨out, M.blank, []⟩) :
    let y := (machine M enc C).sRound ⟨(q, 0), T⟩ a
    y.state.2 = 0 ∧ view y = ticks M C (project ⟨q, T⟩) ∧
      y.tape logAddr = ⟨enc a :: out, M.blank, []⟩ := by
  have hr := frameMachine_round (worker M) (capture enc) C a q T
  simp only [Fin.zero_eta] at hr
  simp only [machine, hr]
  refine ⟨trivial, ?_, ?_⟩
  · change project ((List.replicate C none).foldl (worker M).sMicroStep _) = _
    rw [steps_project, List.length_replicate]
    congr 1
    exact capture_project M enc q T a
  · rw [steps_log]
    simp only [arriveA, capture, ↓reduceIte, show (worker (Terminal := Terminal) M).blank = M.blank from rfl, h]
    rfl

/-- Every real arrival is logged once, while the independent worker receives
exactly C rounds per arrival. This includes worker phase changes and stops. -/
theorem rounds (M : StructuredMachine Unit Q Γ t 1) (enc : Terminal → Γ) (C : ℕ)
    (w : List Terminal) (q : Q) (T : Fin (t + 1) → STape Γ)
    (out : List Γ) (h : T logAddr = ⟨out, M.blank, []⟩) :
    let y := w.foldl (machine M enc C).sRound ⟨(q, 0), T⟩
    y.state.2 = 0 ∧ view y = ticks M (w.length * C) (project ⟨q, T⟩) ∧
      y.tape logAddr = ⟨(w.map enc).reverse ++ out, M.blank, []⟩ := by
  induction w generalizing q T out with
  | nil => simpa [view, project, ticks] using h
  | cons a w ih =>
    let z := (machine M enc C).sRound ⟨(q, 0), T⟩ a
    have hh := round M enc C q T a out h
    have hz : z.state.2 = 0 := hh.1
    have he : z = ⟨(z.state.1, 0), z.tape⟩ := by rw [← hz]
    have hi := ih z.state.1 z.tape (enc a :: out) hh.2.2
    have hr : (a :: w).foldl (machine M enc C).sRound ⟨(q, 0), T⟩ =
        w.foldl (machine M enc C).sRound ⟨(z.state.1, 0), z.tape⟩ := by
      change w.foldl (machine M enc C).sRound z = _
      rw [he]
    simp only [hr]
    refine ⟨hi.1, ?_, ?_⟩
    · rw [hi.2.1]
      change ticks M (w.length * C) (view z) = _
      rw [hh.2.1, List.length_cons, Nat.succ_mul, Nat.add_comm (w.length * C) C, ticks_add]
    · simpa only [List.map_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append] using hi.2.2

end PalPeg.Program.ArrivalLog
