import MacroPeg.CBVtoCBN.CompilerFirstOrder

namespace Shallot.MacroPeg.CBVtoCBN

/-- Lookup in a list of equal-width blocks respects the compiler's static addressing. -/
theorem ruleAtM_fixedBlocks (blocks : List (List MRule)) (width : Nat)
    (hb : ∀ block ∈ blocks, block.length = width) (i slot : Nat)
    (hi : i < blocks.length) (hs : slot < width) :
    ruleAtM blocks.flatten (width * i + slot) = ruleAtM (blocks[i]?.getD []) slot := by
  induction blocks generalizing i with
  | nil => simp at hi
  | cons block blocks ih =>
    have hlen := hb block (by simp)
    cases i with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, List.getElem?_cons_zero, Option.getD_some]
      rw [List.flatten_cons, ruleAtM_eq_getElem?, List.getElem?_append_left (by omega), ← ruleAtM_eq_getElem?]
    | succ i =>
      have ht : ∀ b ∈ blocks, b.length = width := fun b hmem => hb b (List.mem_cons_of_mem _ hmem)
      rw [List.flatten_cons, show width * (i + 1) + slot = block.length + (width * i + slot) by rw [hlen]; simp only [Nat.mul_add, Nat.mul_one]; omega,
        ruleAtM_append_offset]
      exact ih ht i (by simp only [List.length_cons] at hi; omega)

/-- Generated nodes always occupy exactly one complete slot, including its unused failing addresses. -/
theorem compilerNodeRules_length (source : MGrammar) (s : Strategy) (nodes : List CompileNode)
    (digits base : Nat) (node : CompileNode) :
    (compilerNodeRules source s nodes digits base node).length = compilerSlotSize digits := by
  simp [compilerNodeRules]

theorem compilerGeneratedRules_at (source : MGrammar) (s : Strategy) (nodes : List CompileNode)
    (digits i slot : Nat) (hi : i < nodes.length) (hs : slot < compilerSlotSize digits) :
    ruleAtM (compilerGeneratedRules source s nodes digits) (compilerSlotSize digits * i + slot) =
      some (compilerFragmentAt (compilerFragments source s nodes digits
        (4 + compilerSlotSize digits * i) (nodes[i]?.getD (.expr 0 .eps))) slot) := by
  let blocks := (List.range nodes.length).map (fun k => compilerNodeRules source s nodes digits
    (4 + compilerSlotSize digits * k) (nodes[k]?.getD (.expr 0 .eps)))
  have hb : ∀ b ∈ blocks, b.length = compilerSlotSize digits := by
    intro b hmem
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hmem
    exact compilerNodeRules_length _ _ _ _ _ _
  have h := ruleAtM_fixedBlocks blocks (compilerSlotSize digits) hb i slot (by simpa [blocks] using hi) hs
  change ruleAtM blocks.flatten _ = _
  rw [h]
  simp only [blocks, List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.getD_some,
    compilerNodeRules, ruleAtM_eq_getElem?, List.getElem?_map, List.getElem?_range hs, Option.map_some]

private theorem compilerNode_get_idxOf {nodes : List CompileNode} {node : CompileNode} (hn : node ∈ nodes) :
    nodes[nodes.idxOf node]? = some node := by
  induction nodes with
  | nil => cases hn
  | cons a nodes ih =>
    by_cases he : a = node
    · subst a; simp
    · have hm : node ∈ nodes := by simpa [Ne.symm he] using hn
      have hb : (a == node) = false := Bool.eq_false_iff.mpr (fun h => he (eq_of_beq h))
      simpa [List.idxOf_cons, hb] using ih hm

/-- Every collected source node resolves to exactly the rules generated for that node, at every local slot. -/
theorem compileCandidate_at (source : MGrammar) (s : Strategy) (start : MExp) (alphabet : List Char)
    (digits : Nat) (node : CompileNode) (hn : node ∈ compilerNodes source start)
    (slot : Nat) (hs : slot < compilerSlotSize digits) :
    ruleAtM (compileCandidate source s start alphabet digits).rules
      (compilerAddress (compilerNodes source start) digits node + slot) =
      some (compilerFragmentAt (compilerFragments source s (compilerNodes source start) digits
        (compilerAddress (compilerNodes source start) digits node) node) slot) := by
  let nodes := compilerNodes source start
  have hi : nodes.idxOf node < nodes.length := List.idxOf_lt_length_iff.mpr hn
  have h := compilerGeneratedRules_at source s nodes digits (nodes.idxOf node) slot hi hs
  have hnth : nodes[nodes.idxOf node]? = some node := compilerNode_get_idxOf hn
  simp only [hnth, Option.getD_some] at h
  change ruleAtM (compilerFrontRules source s start alphabet digits ++ compilerGeneratedRules source s nodes digits)
    (4 + compilerSlotSize digits * nodes.idxOf node + slot) = _
  rw [show 4 + compilerSlotSize digits * nodes.idxOf node + slot =
      (compilerFrontRules source s start alphabet digits).length + (compilerSlotSize digits * nodes.idxOf node + slot) by
        simp only [compilerFrontRules, List.length_cons, List.length_nil]; omega,
    ruleAtM_append_offset]
  exact h

theorem collectNodes_self (envArity : Nat) (e : MExp) : .expr envArity e ∈ collectNodes envArity e := by
  cases e <;> exact List.mem_cons_self

theorem collectNodes_argumentStage (envArity callee : Nat) (actuals : List MExp) (stage : Nat)
    (hs : stage ≤ actuals.length) :
    .args envArity callee actuals stage ∈ collectNodes envArity (.call callee actuals) := by
  apply List.mem_cons_of_mem
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨stage, List.mem_range.mpr (by omega), rfl⟩

theorem compilerNodes_start (source : MGrammar) (start : MExp) :
    .expr 0 start ∈ compilerNodes source start :=
  List.mem_append_left _ (List.mem_append_left _ (collectNodes_self _ _))

theorem compilerNodes_body {source : MGrammar} (start : MExp) {i : Nat} {rule : MRule}
    (hr : ruleAtM source.rules i = some rule) : .expr rule.arity rule.body ∈ compilerNodes source start := by
  apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨rule, ?_, collectNodes_self _ _⟩
  rw [ruleAtM_eq_getElem?] at hr
  exact List.mem_of_getElem? hr

theorem compilerNodes_lookup (source : MGrammar) (start : MExp) (i : Nat) (hi : i < source.rules.length) :
    .lookup i ∈ compilerNodes source start := by
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

end Shallot.MacroPeg.CBVtoCBN
