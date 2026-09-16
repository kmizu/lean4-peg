import PalPeg.GalilFppCandidate

set_option autoImplicit false
namespace PalPeg.GalilFppPrefix
open GalilFppInstruction GalilFppCode GalilFppInputScan GalilFppCandidate

/-- Resource invariants of every finite execution prefix, including a
prefix of a hypothetical nonterminating execution. -/
theorem invariants {x z : Config} {qs : List ℕ} (h : Steps code x qs z)
    (limit : ℕ) (hx : Bounded x limit) :
    Bounded z limit ∧ z.tape 1 = x.tape 1 ∧ z.pos 1 = x.pos 1 + movesB qs ∧
      (z.pos 0 : ℤ) - z.pos 1 + credit z.pc ≤ (x.pos 0 : ℤ) - x.pos 1 + credit x.pc := by
  induction h with
  | nil => exact ⟨hx, rfl, by simp [movesB], le_refl _⟩
  | step x y z i qs hi hs rest ih =>
    obtain ⟨hbound, htape, hpos, hcredit⟩ := ih (step_bounded hs hi limit hx)
    have hp := List.all_eq_true.mp code_preservesB i (List.mem_of_getElem? hi)
    have hb := step_B hs hp
    refine ⟨hbound, htape.trans hb.1, ?_, hcredit.trans (step_credit hi hs)⟩
    simp only [movesB, List.map_cons, List.sum_cons, hi, Option.map_some, Option.getD_some]
    change z.pos 1 = x.pos 1 + (advanceB i + movesB qs)
    omega

/-- Initial tape conditions suffice for the bounds at every intermediate
state. This theorem does not assume termination or a total instruction bound. -/
theorem initial_bounds {x z : Config} {qs : List ℕ} (h : Steps code x qs z)
    (N : ℕ) (hpc : x.pc = start) (ha : x.pos 0 = 0) (hb : x.pos 1 = 1)
    (hend : x.tape 1 (N + 1) = 5) :
    z.pos 0 < z.pos 1 ∧ z.pos 1 ≤ N + 1 ∧ movesB qs ≤ N ∧ z.tape 1 = x.tape 1 := by
  have hx : Bounded x (N + 1) := by
    refine ⟨hend, by omega, ?_⟩
    intro _
    rw [hpc]
    decide
  obtain ⟨hbound, htape, hpos, hcredit⟩ := invariants h (N + 1) hx
  have hn : 0 ≤ credit z.pc := Int.natCast_nonneg _
  rw [hpc, start_credit, ha, hb] at hcredit
  refine ⟨by omega, hbound.2.1, ?_, htape⟩
  have hz := hbound.2.1
  omega

open GalilFppTrace

theorem step_rank {i : Instruction} {x y : Config} (hi : code[x.pc]? = some i)
    (h : Execute i x y) :
    1 + rank y.pc ≤ rank x.pc + 4 * (if GalilFppTrace.charged x.pc then 1 else 0) := by
  obtain ⟨hq, hp⟩ := GalilFppExecution.lookup_projection hi
  have he : y.pc ∈ GalilFppTrace.successors x.pc := by
    rw [← show successors i = GalilFppTrace.successors x.pc from congrArg Prod.snd hp]
    exact execute_successor h
  have hm : GalilFppGraph.graph[x.pc]! ∈ GalilFppGraph.graph := by
    rw [getElem!_pos GalilFppGraph.graph x.pc hq]
    exact List.getElem_mem hq
  have hc := List.all_eq_true.mp GalilFppGraph.certified _ hm
  simp only [Bool.and_eq_true] at hc
  have hy := of_decide_eq_true (List.all_eq_true.mp hc.1.2 y.pc he)
  have hx := row_facts x.pc hq
  have hr := row_facts y.pc hy
  cases hh : GalilFppTrace.charged x.pc with
  | false =>
    have hd := hx.2.2.2 hh y.pc he
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega
  | true =>
    have hd := hx.2.2.1 hh
    simp only [↓reduceIte]
    omega

/-- The graph accounting also holds before halt. The final rank pays for
the unfinished charged block rather than assuming that block terminates. -/
theorem instruction_budget {x z : Config} {qs : List ℕ} (h : Steps code x qs z) :
    qs.length + rank z.pc ≤ rank x.pc + 4 * charges qs := by
  induction h with
  | nil => simp [charges]
  | step x y z i qs hi hs rest ih =>
    have hb := step_rank hi hs
    change (qs.length + 1) + rank z.pc ≤ rank x.pc +
      4 * ((if GalilFppTrace.charged x.pc then 1 else 0) + charges qs)
    omega

#print axioms instruction_budget
#print axioms initial_bounds
end PalPeg.GalilFppPrefix
