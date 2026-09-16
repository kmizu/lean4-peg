import PalPeg.HistoryConcat
import PalPeg.ProgramFrame

set_option autoImplicit false
namespace PalPeg.HistoryArrival
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLangPersist2
variable {k : ℕ} {Terminal : Type}

def addr (j : Fin 3) : Fin 4 := ⟨j.val, by omega⟩

/-- The fourth tape is reserved for arrivals while the first three merge
the previous history. The worker never changes the arrival tape. -/
def worker (blank : Fin k) : StructuredMachine Terminal (Fin 3) (Fin k) 4 1 where
  tapeCount_pos := by decide
  blank := blank
  initial := 0
  accepting := fun q => decide (q = 2)
  micro := fun q _ σ =>
    let d := (HistoryConcat.machine blank).micro q none (fun j => σ (addr j))
    (d.1, fun j => if h : j.val < 3 then d.2 ⟨j.val, h⟩ else (σ j, .stay))

def capture (enc : Terminal → Fin k) : ArriveAct Terminal (Fin k) 4 :=
  fun a σ j => match a with
    | none => (σ j, .stay)
    | some a => if j = 3 then (enc a, .right) else (σ j, .stay)

def machine (blank : Fin k) (enc : Terminal → Fin k) (C : ℕ) :=
  frameMachine (worker (Terminal := Terminal) blank) (capture enc) C

def project (x : SConfig (Fin 3) (Fin k) 4) : SConfig (Fin 3) (Fin k) 3 :=
  ⟨x.state, fun j => x.tape (addr j)⟩

theorem worker_project (blank : Fin k) (x : SConfig (Fin 3) (Fin k) 4)
    (a : Option Terminal) :
    project ((worker blank).sMicroStep x a) =
      (HistoryConcat.machine blank).sMicroStep (project x) none := by
  simp only [project, StructuredMachine.sMicroStep, worker, addr, Fin.isLt, ↓reduceDIte]
  rfl

theorem steps_project (blank : Fin k) (ops : List (Option Terminal))
    (x : SConfig (Fin 3) (Fin k) 4) :
    project (ops.foldl (worker blank).sMicroStep x) =
      (List.replicate ops.length none).foldl
        (HistoryConcat.machine blank).sMicroStep (project x) := by
  induction ops generalizing x with
  | nil => rfl
  | cons a ops ih =>
    simp only [List.foldl_cons, List.length_cons, List.replicate_succ]
    rw [ih, worker_project]

theorem worker_log (blank : Fin k) (x : SConfig (Fin 3) (Fin k) 4)
    (a : Option Terminal) :
    ((worker blank).sMicroStep x a).tape 3 = x.tape 3 := by
  rfl

theorem steps_log (blank : Fin k) (ops : List (Option Terminal))
    (x : SConfig (Fin 3) (Fin k) 4) :
    (ops.foldl (worker blank).sMicroStep x).tape 3 = x.tape 3 := by
  induction ops generalizing x with
  | nil => rfl
  | cons a ops ih => exact (ih _).trans (worker_log blank x a)

/-- Exactly one new symbol is appended per external input round, irrespective
of the copy controller's state or the fixed amount of copying work. -/
theorem round_log (blank : Fin k) (enc : Terminal → Fin k) (C : ℕ)
    (q : Fin 3) (T : Fin 4 → STape (Fin k)) (a : Terminal)
    (out : List (Fin k)) (h : T 3 = ⟨out, blank, []⟩) :
    ((machine blank enc C).sRound ⟨(q, 0), T⟩ a).tape 3 =
      ⟨enc a :: out, blank, []⟩ := by
  have hr := frameMachine_round (worker blank) (capture enc) C a q T
  simp only [Fin.zero_eta] at hr
  rw [machine, hr]
  rw [steps_log]
  simp only [arriveA, capture, ↓reduceIte, h]
  rfl

def copyView {C : ℕ} (x : SConfig (Fin 3 × Fin (C + 1)) (Fin k) 4) :
    SConfig (Fin 3) (Fin k) 3 := ⟨x.state.1, fun j => x.tape (addr j)⟩

theorem round_phase (blank : Fin k) (enc : Terminal → Fin k) (C : ℕ)
    (q : Fin 3) (T : Fin 4 → STape (Fin k)) (a : Terminal) :
    ((machine blank enc C).sRound ⟨(q, 0), T⟩ a).state.2 = 0 := by
  have hr := frameMachine_round (worker blank) (capture enc) C a q T
  simpa only [machine, Fin.zero_eta] using congrArg (fun x => x.state.2) hr

theorem capture_project (blank : Fin k) (enc : Terminal → Fin k)
    (q : Fin 3) (T : Fin 4 → STape (Fin k)) (a : Terminal) :
    project ⟨q, arriveA blank (capture enc) (some a) T⟩ = project ⟨q, T⟩ := by
  have hn (j : Fin 3) : addr j ≠ 3 := by
    intro h
    have := congrArg Fin.val h
    change j.val = 3 at this
    omega
  simp only [project, arriveA, capture, hn, ↓reduceIte]
  rfl

theorem copy_ticks (blank : Fin k) (n : ℕ) (x : SConfig (Fin 3) (Fin k) 3) :
    (List.replicate n none).foldl (HistoryConcat.machine blank).sMicroStep x =
      HistoryConcat.run blank n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, List.foldl_cons]
    rw [ih]
    rfl

theorem round_copy (blank : Fin k) (enc : Terminal → Fin k) (C : ℕ)
    (q : Fin 3) (T : Fin 4 → STape (Fin k)) (a : Terminal) :
    copyView ((machine blank enc C).sRound ⟨(q, 0), T⟩ a) =
      HistoryConcat.run blank C (project ⟨q, T⟩) := by
  have hr := frameMachine_round (worker blank) (capture enc) C a q T
  simp only [Fin.zero_eta] at hr
  rw [machine, hr]
  change project ((List.replicate C none).foldl (worker blank).sMicroStep _) = _
  rw [steps_project, List.length_replicate, copy_ticks]
  congr 1
  exact capture_project blank enc q T a

theorem rounds (blank : Fin k) (enc : Terminal → Fin k) (C : ℕ)
    (w : List Terminal) (q : Fin 3) (T : Fin 4 → STape (Fin k))
    (out : List (Fin k)) (h : T 3 = ⟨out, blank, []⟩) :
    let y := w.foldl (machine blank enc C).sRound ⟨(q, 0), T⟩
    y.state.2 = 0 ∧ copyView y = HistoryConcat.run blank (w.length * C) (project ⟨q, T⟩) ∧
      y.tape 3 = ⟨(w.map enc).reverse ++ out, blank, []⟩ := by
  induction w generalizing q T out with
  | nil => simpa [copyView, project, HistoryConcat.run] using h
  | cons a w ih =>
    let z := (machine blank enc C).sRound ⟨(q, 0), T⟩ a
    have hz : z.state.2 = 0 := round_phase blank enc C q T a
    have he : z = ⟨(z.state.1, 0), z.tape⟩ := by rw [← hz]
    have hl : z.tape 3 = ⟨enc a :: out, blank, []⟩ := round_log blank enc C q T a out h
    have hc := round_copy blank enc C q T a
    change copyView z = _ at hc
    have hh := ih z.state.1 z.tape (enc a :: out) hl
    have hr : (a :: w).foldl (machine blank enc C).sRound ⟨(q, 0), T⟩ =
        w.foldl (machine blank enc C).sRound ⟨(z.state.1, 0), z.tape⟩ := by
      change w.foldl (machine blank enc C).sRound z = _
      rw [he]
    simp only [hr]
    refine ⟨hh.1, ?_, ?_⟩
    · rw [hh.2.1]
      change HistoryConcat.run blank (w.length * C) (copyView z) = _
      rw [hc, List.length_cons, Nat.succ_mul, Nat.add_comm (w.length * C) C,
        HistoryConcat.run_add]
    · simpa only [List.map_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append] using hh.2.2

/-- Once the fixed per-arrival copy budget covers both old segments, the
merged prefix and every new arrival coexist on separate physical tapes.
Extra copy ticks after completion do not corrupt either history. -/
theorem completed (blank : Fin k) (enc : Terminal → Fin k) (C : ℕ)
    (w : List Terminal) (u v : List (Fin k)) (hu : blank ∉ u) (hv : blank ∉ v)
    (left right out log : List (Fin k)) (T : Fin 4 → STape (Fin k))
    (h0 : T 0 = HistoryConcat.source blank u left)
    (h1 : T 1 = HistoryConcat.source blank v right)
    (h2 : T 2 = ⟨out, blank, []⟩) (h3 : T 3 = ⟨log, blank, []⟩)
    (budget : u.length + v.length + 2 ≤ w.length * C) :
    let y := w.foldl (machine blank enc C).sRound ⟨(0, 0), T⟩
    y.state = (2, 0) ∧ y.tape 2 = ⟨(u ++ v).reverse ++ out, blank, []⟩ ∧
      y.tape 3 = ⟨(w.map enc).reverse ++ log, blank, []⟩ := by
  have hh := rounds blank enc C w 0 T log h3
  have hc := HistoryConcat.concat blank u v hu hv left right out
    (fun j => T (addr j)) h0 h1 h2
  let x := HistoryConcat.run blank (u.length + v.length + 2) (project ⟨0, T⟩)
  have hx : x.state = 2 := hc.1
  have hb : w.length * C = (u.length + v.length + 2) +
      (w.length * C - (u.length + v.length + 2)) := by omega
  have hr : copyView (w.foldl (machine blank enc C).sRound ⟨(0, 0), T⟩) = x := by
    rw [hh.2.1, hb, HistoryConcat.run_add]
    exact HistoryConcat.stable_done blank x hx _
  have hs := congrArg SConfig.state hr
  have ht := congrArg (fun z => z.tape 2) hr
  refine ⟨?_, ?_, hh.2.2⟩
  · exact Prod.ext (hs.trans hx) hh.1
  · exact ht.trans hc.2.1

/-- info: 'PalPeg.HistoryArrival.completed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms completed

/-- info: 'PalPeg.HistoryArrival.round_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms round_log

/-- info: 'PalPeg.HistoryArrival.steps_project' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms steps_project

end PalPeg.HistoryArrival
