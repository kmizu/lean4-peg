import PalPeg.GalilFppExecution

set_option autoImplicit false
namespace PalPeg.GalilFppInputScan
open GalilFppInstruction GalilFppCode

def preservesB : Instruction → Bool
  | .write t _ _ => t != 1
  | .move t false _ => t != 1
  | _ => true

/-- Check every instruction of the actual exported Scala kernel. -/
theorem code_preservesB : code.all preservesB = true := by decide

def advanceB : Instruction → ℕ
  | .move t true _ => if t = 1 then 1 else 0
  | _ => 0

theorem step_B {i : Instruction} {x y : Config} (h : Execute i x y)
    (hi : preservesB i = true) :
    y.tape 1 = x.tape 1 ∧ y.pos 1 = x.pos 1 + advanceB i := by
  cases h with
  | emit => simp [advanceB]
  | read => simp [advanceB]
  | right x t n =>
    by_cases ht : t = 1
    · subst t; simp [advanceB]
    · simp [advanceB, ht, Ne.symm ht]
  | left x t n hp =>
    have ht : t ≠ 1 := by simpa [preservesB] using hi
    simp [advanceB, ht, Ne.symm ht]
  | write x t s n =>
    have ht : t ≠ 1 := by simpa [preservesB] using hi
    simp [advanceB, ht, Ne.symm ht]

def movesB (qs : List ℕ) : ℕ :=
  (qs.map fun q => (code[q]?.map advanceB).getD 0).sum

/-- Exact resource accounting for any terminating tape execution:
B is immutable, and each counted B move advances its head exactly once. -/
theorem completed_B {x z : Config} {qs : List ℕ} (h : Completed code x qs z) :
    z.tape 1 = x.tape 1 ∧ z.pos 1 = x.pos 1 + movesB qs := by
  induction h with
  | halt x hi => simp [movesB, hi, advanceB]
  | step x y z i qs hi hs rest ih =>
    have hm : i ∈ code := List.mem_of_getElem? hi
    have hp := List.all_eq_true.mp code_preservesB i hm
    have hb := step_B hs hp
    refine ⟨ih.1.trans hb.1, ?_⟩
    simp only [movesB, List.map_cons, List.sum_cons, hi, Option.map_some, Option.getD_some]
    change z.pos 1 = x.pos 1 + (advanceB i + movesB qs)
    omega

/-- The remaining B-resource obligation is to keep the head at or before
the end marker. No total instruction bound is assumed in this reduction. -/
theorem movesB_le {x z : Config} {qs : List ℕ} (h : Completed code x qs z)
    (N : ℕ) (hx : x.pos 1 = 1) (hz : z.pos 1 ≤ N + 1) : movesB qs ≤ N := by
  have hb := (completed_B h).2
  omega

/-- PCs reachable while B is on its end marker, including initial and
next-input dispatch. The kernel's only B move is outside this region. -/
def endSafe (q : ℕ) : Bool := decide (q ≤ 37 ∨ q = 227)

def endGuard (q : ℕ) : Instruction → Bool
  | .move t true n => if t = 1 then !endSafe q && endSafe n else !endSafe q || endSafe n
  | .read t choices => if t = 1 then !endSafe q || choices.all (fun p => p.1 != 5 || endSafe p.2)
      else !endSafe q || (choices.map Prod.snd).all endSafe
  | i => !endSafe q || (successors i).all endSafe

theorem code_endGuard : (code.zipIdx).all (fun p => endGuard p.2 p.1) = true := by decide

theorem guard_effect {i : Instruction} {x y : Config} (h : Execute i x y)
    (hg : endGuard x.pc i = true) :
    (advanceB i = 1 → endSafe x.pc = false ∧ endSafe y.pc = true) ∧
    (advanceB i = 0 → x.tape 1 (x.pos 1) = 5 → endSafe x.pc = true → endSafe y.pc = true) := by
  cases h with
  | right x t n =>
    by_cases ht : t = 1
    · subst t
      simpa [endGuard, advanceB, Bool.and_eq_true] using hg
    · simp only [endGuard, ht, ↓reduceIte, successors, List.all_cons, List.all_nil,
        Bool.and_true, Bool.or_eq_true, Bool.not_eq_true] at hg
      simp only [advanceB, ht, ↓reduceIte]
      constructor
      · omega
      · intro _ _ hx
        rcases hg with h | h
        · simp [hx] at h
        · exact h
  | read x t choices n he =>
    by_cases ht : t = 1
    · subst t
      constructor
      · simp [advanceB]
      · intro _ heof hx
        simp only [endGuard, hx, Bool.not_true, Bool.false_or] at hg
        have hh := List.all_eq_true.mp hg (x.tape 1 (x.pos 1), n) he
        simpa [heof] using hh
    · constructor
      · simp [advanceB]
      · intro _ _ hx
        simp only [endGuard, ht, ↓reduceIte, hx, Bool.not_true, Bool.false_or] at hg
        exact List.all_eq_true.mp hg n (List.mem_map.mpr ⟨_, he, rfl⟩)
  | emit x n =>
    constructor
    · simp [advanceB]
    · intro _ _ hx
      simpa [endGuard, hx, successors] using hg
  | left x t n hp =>
    constructor
    · simp [advanceB]
    · intro _ _ hx
      simpa [endGuard, hx, successors] using hg
  | write x t s n =>
    constructor
    · simp [advanceB]
    · intro _ _ hx
      simpa [endGuard, hx, successors] using hg

theorem lookup_guard {q : ℕ} {i : Instruction} (hi : code[q]? = some i) : endGuard q i = true := by
  obtain ⟨hq, he⟩ := List.getElem?_eq_some_iff.mp hi
  have hh := List.forall_mem_zipIdx'.mp (List.all_eq_true.mp code_endGuard) q hq
  simpa only [he] using hh

def Bounded (x : Config) (limit : ℕ) : Prop :=
  x.tape 1 limit = 5 ∧ x.pos 1 ≤ limit ∧
    (x.tape 1 (x.pos 1) = 5 → endSafe x.pc = true)

theorem step_bounded {i : Instruction} {x y : Config} (h : Execute i x y)
    (hi : code[x.pc]? = some i) (limit : ℕ) (hx : Bounded x limit) : Bounded y limit := by
  have hp := List.all_eq_true.mp code_preservesB i (List.mem_of_getElem? hi)
  have hb := step_B h hp
  have hg := guard_effect h (lookup_guard hi)
  have ha : advanceB i ≤ 1 := by
    cases h <;> simp [advanceB]
    split <;> omega
  refine ⟨by rw [hb.1]; exact hx.1, ?_, ?_⟩
  · by_cases hz : advanceB i = 0
    · have hh := hx.2.1
      omega
    · have hone : advanceB i = 1 := by omega
      have hnot : x.pos 1 ≠ limit := by
        intro he
        have heof : x.tape 1 (x.pos 1) = 5 := he ▸ hx.1
        have hs := hx.2.2 heof
        have hf := (hg.1 hone).1
        simp [hs] at hf
      have hh := hx.2.1
      omega
  · intro hy
    by_cases hz : advanceB i = 0
    · have he : y.pos 1 = x.pos 1 := by omega
      rw [hb.1, he] at hy
      exact hg.2 hz hy (hx.2.2 hy)
    · exact (hg.1 (by omega)).2

theorem completed_bounded {x z : Config} {qs : List ℕ} (h : Completed code x qs z)
    (limit : ℕ) (hx : Bounded x limit) : Bounded z limit := by
  induction h with
  | halt => exact hx
  | step x y z i qs hi hs rest ih => exact ih (step_bounded hs hi limit hx)

/-- B's linear resource bound from the actual start PC, head position and
end marker. No bound on the final head is supplied by the caller. -/
theorem input_moves_le {x z : Config} {qs : List ℕ} (h : Completed code x qs z)
    (N : ℕ) (hpc : x.pc = start) (hpos : x.pos 1 = 1) (hend : x.tape 1 (N + 1) = 5) :
    movesB qs ≤ N := by
  have hx : Bounded x (N + 1) := by
    refine ⟨hend, by omega, ?_⟩
    intro _
    rw [hpc]
    decide
  exact movesB_le h N hpos (completed_bounded h (N + 1) hx).2.1

#print axioms input_moves_le
#print axioms completed_B
end PalPeg.GalilFppInputScan
