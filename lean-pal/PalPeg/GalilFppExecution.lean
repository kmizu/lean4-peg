import PalPeg.GalilFppCode
import PalPeg.GalilFppTrace

set_option autoImplicit false
namespace PalPeg.GalilFppExecution
open GalilFppInstruction GalilFppCode GalilFppGraph

theorem lookup_projection {q : ℕ} {i : Instruction} (hi : code[q]? = some i) :
    q < graph.length ∧ projection i = ((graph[q]!).1, (graph[q]!).2.1) := by
  obtain ⟨hq, _⟩ := List.getElem?_eq_some_iff.mp hi
  have hl : code.length = graph.length := by
    have h := congrArg List.length graph_projection
    simpa only [List.length_map] using h
  have hg : q < graph.length := by omega
  have he := congrArg (fun xs => xs[q]?) graph_projection
  simp only [List.getElem?_map, hi, Option.map_some] at he
  rw [List.getElem?_eq_getElem hg] at he
  simp only [Option.map_some] at he
  refine ⟨hg, ?_⟩
  simpa only [getElem!_pos graph q hg] using Option.some.inj he

/-- Tape contents determine read branches, writes update exactly one cell,
and heads move one cell. Every successful terminating execution projects
to the certified graph, including its final halt instruction. -/
theorem completed_trace {x z : Config} {qs : List ℕ} (h : Completed code x qs z) :
    ∃ tail, qs = x.pc :: tail ∧ GalilFppTrace.Trace x.pc tail := by
  induction h with
  | halt x hi =>
    obtain ⟨hq, hp⟩ := lookup_projection hi
    have hc : GalilFppTrace.charged x.pc = true := (congrArg Prod.fst hp).symm
    exact ⟨[], rfl, .last x.pc hq hc⟩
  | step x y z i qs hi hstep rest ih =>
    obtain ⟨tail, he, ht⟩ := ih
    obtain ⟨hq, hp⟩ := lookup_projection hi
    have hs : successors i = GalilFppTrace.successors x.pc := congrArg Prod.snd hp
    have hedge := execute_successor hstep
    rw [hs] at hedge
    exact ⟨y.pc :: tail, by rw [he], .step x.pc y.pc tail hq hedge ht⟩

theorem instructions_le_four_charges {x z : Config} {qs : List ℕ}
    (h : Completed code x qs z) : qs.length ≤ 4 * GalilFppTrace.charges qs := by
  obtain ⟨tail, he, ht⟩ := completed_trace h
  rw [he]
  exact GalilFppTrace.instructions_le_four_charges ht

#print axioms instructions_le_four_charges
end PalPeg.GalilFppExecution
