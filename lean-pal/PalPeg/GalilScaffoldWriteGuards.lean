import PalPeg.GalilScaffoldMoveGuards

set_option autoImplicit false
namespace PalPeg.GalilScaffoldWriteGuards
open GalilFppWide (Instruction)
open GalilScaffoldMoveGuards (dispatch dispatch_once)

def WriteEvent {n : ℕ} (code : List (Instruction n)) (pc : ℕ) (active : Bool)
    (t : Fin n) (v : Fin 9) : Prop :=
  ∃ i next, active = true ∧ pc = i ∧ code[i]? = some (.write t v next)

theorem event_iff {n : ℕ} (code : List (Instruction n)) (pc : ℕ) (active : Bool)
    (t : Fin n) (v : Fin 9) : WriteEvent code pc active t v ↔
      active = true ∧ ∃ next, code[pc]? = some (.write t v next) := by
  constructor
  · rintro ⟨i,next,ha,he,hi⟩; subst i; exact ⟨ha,next,hi⟩
  · rintro ⟨ha,next,hi⟩; exact ⟨pc,next,ha,rfl,hi⟩

theorem selected_write {n : ℕ} {code : List (Instruction n)} {pc next : ℕ}
    {t : Fin n} {v : Fin 9} (hi : code[pc]? = some (.write t v next))
    (u : Fin n) (w : Fin 9) : WriteEvent code pc true u w ↔ u = t ∧ w = v := by
  constructor
  · intro hu
    obtain ⟨_,q,hq⟩ := (event_iff _ _ _ _ _).mp hu
    rw [hi] at hq
    cases hq
    exact ⟨rfl,rfl⟩
  · rintro ⟨rfl,rfl⟩
    exact (event_iff _ _ _ _ _).mpr ⟨rfl,next,hi⟩

theorem dispatch_fold {κ σ : Type} [DecidableEq κ] (chosen : κ) (step : κ → σ → σ)
    (ks : List κ) (x : σ) :
    ks.foldl (fun y k => if k = chosen then step k y else y) x = dispatch chosen step ks x := by
  induction ks generalizing x with
  | nil => rfl
  | cons k ks ih => exact ih _

/-- Decoded write groups, after selected_write reduces the symbol guards.
The instruction-entry PC is fixed throughout the tape loop. -/
def writeLoop {n : ℕ} {σ : Type} (code : List (Instruction n)) (pc : ℕ) (active : Bool)
    (step : Fin n → Fin 9 → σ → σ) (x : σ) : σ :=
  (List.finRange n).foldl (fun y k => match code[pc]? with
    | some (.write t v _) => if active then (if k = t then step k v y else y) else y
    | _ => y) x

theorem loop_write {n : ℕ} {σ : Type} {code : List (Instruction n)} {pc next : ℕ}
    {t : Fin n} {v : Fin 9} (hi : code[pc]? = some (.write t v next))
    (step : Fin n → Fin 9 → σ → σ) (x : σ) :
    writeLoop code pc true step x = step t v x := by
  simp only [writeLoop,hi,ite_true]
  rw [dispatch_fold]
  exact dispatch_once t (fun k => step k v) _ (List.nodup_finRange n) (List.mem_finRange t) x

theorem loop_heap_write {n slots : ℕ} {code : List (Instruction n)} {pc next : ℕ}
    {t : Fin n} {v : Fin 9} (hi : code[pc]? = some (.write t v next))
    (x : GalilScaffoldHeapProgram.Config n slots) :
    writeLoop code pc true (fun k s y => GalilScaffoldHeapProgram.written y k s x.pc) x =
      GalilScaffoldHeapProgram.written x t v x.pc := loop_write hi _ x

theorem loop_inactive {n : ℕ} {σ : Type} (code : List (Instruction n)) (pc : ℕ)
    (step : Fin n → Fin 9 → σ → σ) (x : σ) : writeLoop code pc false step x = x := by
  cases he : code[pc]? with
  | none => simp [writeLoop,he]
  | some i => cases i <;> simp [writeLoop,he]

theorem loop_nonwrite {n : ℕ} {σ : Type} {code : List (Instruction n)} {pc : ℕ}
    {i : Instruction n} (hi : code[pc]? = some i)
    (hn : ∀ t v next, i ≠ .write t v next) (active : Bool)
    (step : Fin n → Fin 9 → σ → σ) (x : σ) : writeLoop code pc active step x = x := by
  cases i <;> simp_all [writeLoop]

#print axioms loop_inactive
#print axioms loop_nonwrite
#print axioms selected_write
#print axioms loop_heap_write
end PalPeg.GalilScaffoldWriteGuards
