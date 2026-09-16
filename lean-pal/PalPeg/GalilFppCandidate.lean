import PalPeg.GalilFppInputScan

set_option autoImplicit false
set_option maxRecDepth 100000
namespace PalPeg.GalilFppCandidate
open GalilFppInstruction GalilFppCode

/-- Change of A position minus B position in one local instruction. -/
def displacement : Instruction → ℤ
  | .move t right _ => if t = 0 then (if right then 1 else -1)
      else if t = 1 then (if right then -1 else 1) else 0
  | _ => 0

def credit (q : ℕ) : ℤ := potential[q]!

/-- The exporter supplies a candidate potential; Lean checks every edge. -/
theorem code_credit : (code.zipIdx).all (fun p => (successors p.1).all
    (fun n => decide (displacement p.1 + credit n ≤ credit p.2))) = true := by decide

theorem start_credit : credit start = 0 := by decide

theorem execute_displacement {i : Instruction} {x y : Config} (h : Execute i x y) :
    (y.pos 0 : ℤ) - y.pos 1 = (x.pos 0 : ℤ) - x.pos 1 + displacement i := by
  cases h with
  | emit => simp [displacement]
  | read => simp [displacement]
  | write => simp [displacement]
  | right x t n => fin_cases t <;> simp [displacement, Function.update_apply] <;> omega
  | left x t n hp => fin_cases t <;> simp [displacement] at * <;> omega

theorem step_credit {i : Instruction} {x y : Config} (hi : code[x.pc]? = some i)
    (h : Execute i x y) :
    (y.pos 0 : ℤ) - y.pos 1 + credit y.pc ≤ (x.pos 0 : ℤ) - x.pos 1 + credit x.pc := by
  obtain ⟨hq, he⟩ := List.getElem?_eq_some_iff.mp hi
  have hg := List.forall_mem_zipIdx'.mp (List.all_eq_true.mp code_credit) x.pc hq
  simp only [he] at hg
  have hb := of_decide_eq_true (List.all_eq_true.mp hg y.pc (execute_successor h))
  rw [execute_displacement h]
  omega

theorem completed_credit {x z : Config} {qs : List ℕ} (h : Completed code x qs z) :
    (z.pos 0 : ℤ) - z.pos 1 + credit z.pc ≤ (x.pos 0 : ℤ) - x.pos 1 + credit x.pc := by
  induction h with
  | halt => exact le_refl _
  | step x y z i qs hi hs rest ih => exact ih.trans (step_credit hi hs)

/-- A never catches or passes B when started at the actual kernel entry.
This includes speculative comparisons and all fallback branches. -/
theorem candidate_before_scan {x z : Config} {qs : List ℕ} (h : Completed code x qs z)
    (hpc : x.pc = start) (ha : x.pos 0 = 0) (hb : x.pos 1 = 1) : z.pos 0 < z.pos 1 := by
  have hh := completed_credit h
  have hn : 0 ≤ credit z.pc := Int.natCast_nonneg _
  rw [hpc, start_credit, ha, hb] at hh
  omega

/-- Combine the A/B separation with the proved B end-marker invariant. -/
theorem candidate_le_input {x z : Config} {qs : List ℕ} (h : Completed code x qs z)
    (N : ℕ) (hpc : x.pc = start) (ha : x.pos 0 = 0) (hb : x.pos 1 = 1)
    (hend : x.tape 1 (N + 1) = 5) : z.pos 0 ≤ N := by
  have hi : GalilFppInputScan.Bounded x (N + 1) := by
    refine ⟨hend, by omega, ?_⟩
    intro _
    rw [hpc]
    decide
  have hbound := (GalilFppInputScan.completed_bounded h (N + 1) hi).2.1
  have hsep := candidate_before_scan h hpc ha hb
  omega

#print axioms candidate_le_input
end PalPeg.GalilFppCandidate
