import PalPeg.GalilFppGraph

set_option autoImplicit false
namespace PalPeg.GalilFppTrace
open GalilFppGraph

def rank (q : ℕ) := (graph[q]!).2.2
def charged (q : ℕ) := (graph[q]!).1
def successors (q : ℕ) := (graph[q]!).2.1

theorem row_facts (q : ℕ) (hq : q < graph.length) :
    1 ≤ rank q ∧ rank q ≤ 4 ∧
      (charged q = true → rank q = 1) ∧
      (charged q = false → ∀ r ∈ successors q, rank r < rank q) := by
  have hm : graph[q]! ∈ graph := by
    rw [getElem!_pos graph q hq]
    exact List.getElem_mem hq
  have hh := List.all_eq_true.mp certified (graph[q]!) hm
  simp only [Bool.and_eq_true] at hh
  have hb := of_decide_eq_true hh.1.1
  refine ⟨hb.1, hb.2, ?_, ?_⟩
  · intro hc
    have hc' : (graph[q]!).1 = true := hc
    have ht := hh.2
    simp only [hc', ↓reduceIte] at ht
    exact of_decide_eq_true ht
  · intro hc
    have hc' : (graph[q]!).1 = false := hc
    have ht := hh.2
    simp only [hc', Bool.false_eq_true, ↓reduceIte] at ht
    intro r he
    exact of_decide_eq_true (List.all_eq_true.mp ht r he)

/-- A graph execution ending at a charged instruction (in particular,
the actual halt). Infeasible read branches are allowed, strengthening the bound. -/
inductive Trace : ℕ → List ℕ → Prop
  | last (q : ℕ) (hq : q < graph.length) (hc : charged q = true) : Trace q []
  | step (q r : ℕ) (tail : List ℕ) (hq : q < graph.length)
      (he : r ∈ successors q) (rest : Trace r tail) : Trace q (r :: tail)

def charges : List ℕ → ℕ
  | [] => 0
  | q :: qs => (if charged q then 1 else 0) + charges qs

theorem trace_start {q : ℕ} {tail : List ℕ} (h : Trace q tail) : q < graph.length := by
  cases h with
  | last _ hq _ => exact hq
  | step _ _ _ hq _ _ => exact hq

theorem trace_budget {q : ℕ} {tail : List ℕ} (h : Trace q tail) :
    0 < charges (q :: tail) ∧
      (q :: tail).length ≤ rank q + 4 * (charges (q :: tail) - 1) := by
  induction h with
  | last q hq hc =>
    have hf := row_facts q hq
    simp only [charges, hc, ↓reduceIte, List.length_cons, List.length_nil]
    omega
  | step q r tail hq he rest ih =>
    have hf := row_facts q hq
    have hr := row_facts r (trace_start rest)
    change 0 < (if charged q then 1 else 0) + charges (r :: tail) ∧
      tail.length + 1 + 1 ≤ rank q + 4 * ((if charged q then 1 else 0) + charges (r :: tail) - 1)
    simp only [List.length_cons] at ih
    cases hc : charged q with
    | false =>
      have hd := hf.2.2.2 hc r he
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      omega
    | true =>
      have hd := hf.2.2.1 hc
      simp only [↓reduceIte]
      omega

/-- The factor four is now an arbitrary-length execution bound, rather
than only a finite control-graph check. Tape-resource bounds remain separate. -/
theorem instructions_le_four_charges {q : ℕ} {tail : List ℕ} (h : Trace q tail) :
    (q :: tail).length ≤ 4 * charges (q :: tail) := by
  have hb := trace_budget h
  have hr := row_facts q (trace_start h)
  omega

#print axioms instructions_le_four_charges

/-- The graph part of the documented 132*N+12 kernel bound. The
33*N+3 resource ledger is explicit, not inferred from finite testing. -/
theorem kernel_from_ledger {q : ℕ} {tail : List ℕ} (h : Trace q tail) (N : ℕ)
    (hledger : charges (q :: tail) ≤ 33 * N + 3) :
    (q :: tail).length ≤ 132 * N + 12 := by
  have hb := instructions_le_four_charges h
  omega

end PalPeg.GalilFppTrace
