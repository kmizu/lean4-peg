import PalPeg.ReplayBufferTurn
import PalPeg.ProgramReplayArrival
import PalPeg.ProgramFrame

set_option autoImplicit false
namespace PalPeg.ReplayLoop
open PegSeparation.RealTimeTM PalPeg.Program
variable {Terminal Q : Type} [Fintype Q] [DecidableEq Q] {k t B : ℕ}

/-- New consumed/source/log roles are old source/log/free, respectively.
Buffer 1 remains the spare reclaim lane. No tape contents are moved. -/
def rotate : Fin 4 ≃ Fin 4 where
  toFun := ![2, 1, 3, 0]
  invFun := ![3, 1, 0, 2]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

abbrev Control (Q : Type) (B : ℕ) := Q × (Fin 4 ≃ Fin 4) × ((Fin 3 → Fin 3) ⊕ Fin B)
def buf (i : Fin 4) : Fin (4 + t) := finSumFinEquiv (.inl i : Fin 4 ⊕ Fin t)
def dataAddr (i : Fin t) : Fin (4 + t) := finSumFinEquiv (.inr i : Fin 4 ⊕ Fin t)

/-- Finite autonomous batch loop. Recovery completion starts replay;
replay's blank terminator rotates buffers and starts the next recovery.
The matcher state is never reset by either handoff. -/
def worker (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (decode : Fin k → Terminal) : StructuredMachine Terminal (Control Q B) (Fin k) (4 + t) 1 where
  tapeCount_pos := by omega
  blank := M.blank
  initial := (M.initial, Equiv.refl _, .inl (fun _ => 0))
  accepting := fun q => M.accepting q.1
  micro := fun q _ σ =>
    let idle := fun j => (σ j, Move.stay)
    match q.2.2 with
    | .inl p =>
      if ∀ i, p i = 2 then ((q.1, q.2.1, .inr ⟨0, hB⟩), idle) else
      let d := (HistoryRecover.machine M.blank).micro p (some ())
        (fun i => σ (buf (q.2.1 ⟨i.val, by omega⟩)))
      ((q.1, q.2.1, .inl d.1), fun j =>
        match (finSumFinEquiv.symm j : Fin 4 ⊕ Fin t) with
        | .inl i =>
          let r := q.2.1.symm i
          if h : r.val < 3 then d.2 ⟨r.val, h⟩ else idle j
        | .inr _ => idle j)
    | .inr p =>
      if p.val = 0 ∧ σ (buf (q.2.1 2)) = M.blank then
        ((q.1, rotate.trans q.2.1, .inl (fun _ => 0)), idle) else
      let d := (TapeReplay.machine M hB decode).micro (q.1, p) (some ())
        (fun j => match (finSumFinEquiv.symm j : Fin 1 ⊕ Fin t) with
          | .inl _ => σ (buf (q.2.1 2))
          | .inr i => σ (dataAddr i))
      ((d.1.1, q.2.1, .inr d.1.2), fun j =>
        match (finSumFinEquiv.symm j : Fin 4 ⊕ Fin t) with
        | .inl i => if i = q.2.1 2 then d.2 TapeReplay.sourceAddr else idle j
        | .inr i => d.2 (TapeReplay.targetAddr i))

/-- Capture precedes the fixed worker budget. A role exchange later in
that frame therefore cannot duplicate or discard the arrival. -/
def body (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal) (C : ℕ) :
    PhaseBody Terminal (Control Q B) (Fin k) (4 + t) (C + 1) := fun q a ph σ =>
  if ph.val = 0 then
    (q, fun j => match a with
      | none => (σ j, .stay)
      | some a => if j = buf (q.2.1 3) then (enc a, .right) else (σ j, .stay))
  else (worker M hB decode).micro q none σ

def machine (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal) (C : ℕ) :=
  ofPhases (by omega : 0 < 4 + t) (by omega : 0 < C + 1) M.blank
    (worker M hB decode).initial (fun q => M.accepting q.1) (body M hB enc decode C)

theorem worker_preserves_matcher_during_recovery
    (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (decode : Fin k → Terminal) (q : Q) (roles : Fin 4 ≃ Fin 4)
    (p : Fin 3 → Fin 3) (σ : Fin (4 + t) → Fin k) :
    ((worker M hB decode).micro (q, roles, .inl p) none σ).1.1 = q ∧
    ∀ i, ((worker M hB decode).micro (q, roles, .inl p) none σ).2 (dataAddr i) =
      (σ (dataAddr i), .stay) := by
  simp only [worker, dataAddr, Equiv.symm_apply_apply]
  split
  · exact ⟨rfl, fun _ => rfl⟩
  · refine ⟨rfl, ?_⟩
    intro i
    simp only [Equiv.symm_apply_apply]

theorem replay_handoff (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (decode : Fin k → Terminal) (q : Q) (roles : Fin 4 ≃ Fin 4)
    (σ : Fin (4 + t) → Fin k) (h : σ (buf (roles 2)) = M.blank) :
    (worker M hB decode).micro (q, roles, .inr ⟨0, hB⟩) none σ =
      ((q, rotate.trans roles, .inl (fun _ => 0)), fun j => (σ j, .stay)) := by
  simp only [worker, h, and_self, ↓reduceIte]

theorem worker_preserves_current_log
    (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (decode : Fin k → Terminal) (q : Control Q B) (σ : Fin (4 + t) → Fin k) :
    ((worker M hB decode).micro q none σ).2 (buf (q.2.1 3)) =
      (σ (buf (q.2.1 3)), .stay) := by
  rcases q with ⟨s, roles, p⟩
  cases p with
  | inl p =>
    simp only [worker]
    split
    · rfl
    · simp only [buf, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
        show ¬ (3 : Fin 4).val < 3 by decide, ↓reduceDIte]
  | inr p =>
    simp only [worker]
    split
    · rfl
    · have hn : roles 3 ≠ roles 2 := fun h => (by decide : (3 : Fin 4) ≠ 2) (roles.injective h)
      simp only [buf, Equiv.symm_apply_apply, hn, ↓reduceIte]

theorem capture_arrival (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal) (C : ℕ)
    (q : Control Q B) (a : Terminal) (σ : Fin (4 + t) → Fin k) :
    body M hB enc decode C q (some a) ⟨0, by omega⟩ σ =
      (q, fun j => if j = buf (q.2.1 3) then (enc a, .right) else (σ j, .stay)) := rfl

/-- info: 'PalPeg.ReplayLoop.worker_preserves_current_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms worker_preserves_current_log

end PalPeg.ReplayLoop
