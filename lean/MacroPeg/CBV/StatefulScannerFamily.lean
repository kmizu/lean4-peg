import MacroPeg.CBV.StatefulScanner

/-! All stopping-state tests live together in one fixed grammar. The
compiler and query syntax do not receive the state reached on the input. -/
namespace Shallot.MacroPeg.CBV.StatefulScannerFamily
open StatefulScanner

private theorem uniform_lookup {α : Type} (blocks : List (List α)) (width : Nat)
    (h : ∀ b ∈ blocks, b.length = width) (i j : Nat) (hj : j < width) :
    blocks.flatten[i*width+j]? = (blocks[i]?).bind (fun b => b[j]?) := by
  induction blocks generalizing i with
  | nil => simp
  | cons b blocks ih =>
    have hb : b.length = width := h b (by simp)
    have ht : ∀ b ∈ blocks, b.length = width := fun b hb => h b (by simp [hb])
    cases i with
    | zero =>
      simp only [Nat.zero_mul,Nat.zero_add,List.flatten_cons,List.getElem?_cons_zero,Option.bind_some]
      exact List.getElem?_append_left (by omega)
    | succ i =>
      have hi : b.length ≤ (i+1)*width+j := by rw [Nat.add_mul,Nat.one_mul]; omega
      rw [List.flatten_cons,List.getElem?_append_right hi,hb]
      have he : (i+1)*width+j-width = i*width+j := by rw [Nat.add_mul,Nat.one_mul]; omega
      rw [he]
      exact ih ht i

def grammar {n : Nat} (M : Machine n) : MGrammar :=
  ⟨(List.ofFn (fun target : Fin n =>
    block M (fun q => decide (q=target)) (target.val*n))).flatten⟩

def entry {n : Nat} (q target : Fin n) : MExp := .call (target.val*n+q.val) []
def probe {n : Nat} (q target : Fin n) : MExp := .andP (entry q target)

theorem grammar_rule {n : Nat} (M : Machine n) (q target : Fin n) :
    ruleAtM (grammar M).rules (target.val*n+q.val) = some
      ⟨0,branches (target.val*n) (terminal (decide (q=target))) (M.arcs q)⟩ := by
  rw [ruleAtM_eq_getElem?]
  unfold grammar
  rw [uniform_lookup _ n (by
    intro b hb
    obtain ⟨t,rfl⟩ := List.mem_ofFn.mp hb
    exact block_length _ _ _) target.val q.val q.isLt]
  simp [block,target.isLt,q.isLt]

theorem grammar_length {n : Nat} (M : Machine n) : (grammar M).rules.length = n*n := by
  unfold grammar
  rw [List.length_flatten]
  have he : (List.ofFn (fun target : Fin n =>
      block M (fun q => decide (q=target)) (target.val*n))).map List.length = List.replicate n n := by
    simp only [List.map_ofFn,Function.comp_def,block_length]
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  rw [he,List.sum_replicate_nat]

theorem grammar_firstOrder {n : Nat} (M : Machine n) : (grammar M).FirstOrder := by
  intro r hr
  obtain ⟨b,hb,hr⟩ := List.mem_flatten.mp hr
  obtain ⟨target,rfl⟩ := List.mem_ofFn.mp hb
  change r ∈ List.ofFn (fun q : Fin n =>
    ⟨0,branches (target.val*n) (terminal (decide (q=target))) (M.arcs q)⟩) at hr
  obtain ⟨q,rfl⟩ := List.mem_ofFn.mp hr
  apply branches_firstOrder
  cases decide (q=target) <;> trivial

/-- A failed stopping-state selector fails at the real scanner boundary;
it cannot choose a shorter prefix where that state was visited earlier. -/
theorem entry_eval {n : Nat} (M : Machine n) (x : List Char) (s : Strategy)
    (q target : Fin n) (E : List (List Char)) (p m : Nat)
    (hp : p ≤ x.length) (hm : p+1 ≤ m) :
    evV (grammar M) x s (tblV (grammar M) x s m) E (entry q target) p =
      some (if (run M q (sfx x p)).1 = target then some (run M q (sfx x p)).2.length else none) := by
  have hl := grammar_rule M q target
  have he := query_eval M (fun r => decide (r=target)) (grammar M) (target.val*n)
    (fun q => grammar_rule M q target) x s p hp m hm q
  unfold entry
  cases s <;> simpa only [evV,hl,if_true,evParArgs,evSeqArgs,decide_eq_true_eq,List.length_nil] using he

/-- Used as a real Seq argument, a successful selector captures exactly the
original consumed prefix, alongside its actual remaining position. -/
theorem capture_eval {n : Nat} (M : Machine n) (x : List Char) (q target : Fin n)
    (E : List (List Char)) (p m : Nat) (hp : p ≤ x.length) (hm : p+1 ≤ m) :
    evSeqArgs (grammar M) x .callByValueSeq (tblV (grammar M) x .callByValueSeq m)
      E [entry q target] p =
      some (if (run M q (sfx x p)).1 = target then
        some ([pre x p (run M q (sfx x p)).2.length],(run M q (sfx x p)).2.length) else none) := by
  simp only [evSeqArgs,entry_eval M x .callByValueSeq q target E p m hp hm]
  by_cases ht : (run M q (sfx x p)).1 = target <;> simp only [ht,if_true,if_false]

/-- The runtime test restores the caller position, while the compiled scan
itself consumes the unique original prefix and has unbounded possible length. -/
theorem probe_eval {n : Nat} (M : Machine n) (x : List Char) (s : Strategy)
    (q target : Fin n) (E : List (List Char)) (p m : Nat)
    (hp : p ≤ x.length) (hm : p+1 ≤ m) :
    evV (grammar M) x s (tblV (grammar M) x s m) E (probe q target) p =
      if (run M q (sfx x p)).1 = target then some (some p) else some none := by
  rw [probe,CallLookahead.evV_peek,entry_eval M x s q target E p m hp hm]
  split <;> rfl

theorem entry_observation {n : Nat} (M : Machine n) (x : List Char) (s : Strategy)
    (hs : s ≠ .callByName) (q target : Fin n) :
    SObs (grammar M) s (entry q target) x
      (if (run M q x).1 = target then some (run M q x).2 else none) := by
  apply (decideObsV_iff (grammar_firstOrder M) hs (by trivial) x _).mp
  have he := entry_eval M x s q target [] x.length (x.length+1) (Nat.le_refl _) (Nat.le_refl _)
  simp only [sfx_self] at he
  have hb := (tblV_stable (grammar M) x s (Nat.le_refl x.length)).mp ⟨x.length+1,he⟩
  unfold decideObsV
  rw [hb]
  by_cases ht : (run M q x).1 = target
  · simp only [if_pos ht]
    rw [sfx_suffix (run_suffix M q x).choose_spec]
  · simp only [if_neg ht]

theorem probe_observation {n : Nat} (M : Machine n) (x : List Char) (s : Strategy)
    (hs : s ≠ .callByName) (q target : Fin n) :
    SObs (grammar M) s (probe q target) x
      (if (run M q x).1 = target then some x else none) := by
  have he := entry_observation M x s hs q target
  by_cases h : (run M q x).1 = target
  · simp only [if_pos h] at he ⊢
    exact RootObservation.peek_success he
  · simp only [if_neg h] at he ⊢
    exact RootObservation.peek_failure he

end Shallot.MacroPeg.CBV.StatefulScannerFamily
