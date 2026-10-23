import MacroPeg.CBV.ParSimulation.CompilerFirstOrder
import MacroPeg.CBVtoCBN.CompilerBlocks

namespace Shallot.MacroPeg.CBV.ParSimulation

open CBVtoCBN (CompileNode CompileFragments compilerSlotSize compilerFragmentAt compilerNodes
  RulesAt ruleAtM_append_offset ruleAtM_fixedBlocks compilerFragmentAt_block)

theorem nodeRules_length (source : MGrammar) (nodes : List CompileNode)
    (digits base : Nat) (node : CompileNode) :
    (nodeRules source nodes digits base node).length = compilerSlotSize digits := by
  simp [nodeRules]

theorem generatedRules_at (source : MGrammar) (nodes : List CompileNode)
    (digits i slot : Nat) (hi : i < nodes.length) (hs : slot < compilerSlotSize digits) :
    ruleAtM (generatedRules source nodes digits) (compilerSlotSize digits * i + slot) =
      some (compilerFragmentAt (fragments source nodes digits
        (8 + compilerSlotSize digits * i) (nodes[i]?.getD (.expr 0 .eps))) slot) := by
  let blocks := (List.range nodes.length).map (fun k => nodeRules source nodes digits
    (8 + compilerSlotSize digits * k) (nodes[k]?.getD (.expr 0 .eps)))
  have hb : ∀ b ∈ blocks, b.length = compilerSlotSize digits := by
    intro b hmem
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hmem
    exact nodeRules_length _ _ _ _ _
  have h := ruleAtM_fixedBlocks blocks (compilerSlotSize digits) hb i slot (by simpa [blocks] using hi) hs
  change ruleAtM blocks.flatten _ = _
  rw [h]
  simp only [blocks, List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.getD_some,
    nodeRules, ruleAtM_eq_getElem?, List.getElem?_map, List.getElem?_range hs, Option.map_some]

private theorem node_get_idxOf {nodes : List CompileNode} {node : CompileNode} (hn : node ∈ nodes) :
    nodes[nodes.idxOf node]? = some node := by
  induction nodes with
  | nil => cases hn
  | cons a nodes ih =>
    by_cases he : a = node
    · subst a; simp
    · have hm : node ∈ nodes := by simpa [Ne.symm he] using hn
      have hb : (a == node) = false := Bool.eq_false_iff.mpr (fun h => he (eq_of_beq h))
      simpa [List.idxOf_cons, hb] using ih hm

/-- Every collected source node resolves to the exact code emitted by the
new Par generator, at every address inside its static slot. -/
theorem compileCandidate_at (source : MGrammar) (start : MExp) (alphabet : List Char)
    (digits : Nat) (node : CompileNode) (hn : node ∈ compilerNodes source start)
    (slot : Nat) (hs : slot < compilerSlotSize digits) :
    ruleAtM (compileCandidate source start alphabet digits).rules
      (address (compilerNodes source start) digits node + slot) =
      some (compilerFragmentAt (fragments source (compilerNodes source start) digits
        (address (compilerNodes source start) digits node) node) slot) := by
  let nodes := compilerNodes source start
  have hi : nodes.idxOf node < nodes.length := List.idxOf_lt_length_iff.mpr hn
  have h := generatedRules_at source nodes digits (nodes.idxOf node) slot hi hs
  have hnth : nodes[nodes.idxOf node]? = some node := node_get_idxOf hn
  simp only [hnth, Option.getD_some] at h
  change ruleAtM (frontRules source start alphabet digits ++ generatedRules source nodes digits)
    (8 + compilerSlotSize digits * nodes.idxOf node + slot) = _
  rw [show 8 + compilerSlotSize digits * nodes.idxOf node + slot =
      (frontRules source start alphabet digits).length + (compilerSlotSize digits * nodes.idxOf node + slot) by
        simp only [frontRules, List.length_cons, List.length_nil]; omega,
    ruleAtM_append_offset]
  exact h

structure CompilerConfig where
  source : MGrammar
  start : MExp
  alphabet : List Char
  digits : Nat

def CompilerConfig.nodes (c : CompilerConfig) : List CompileNode := compilerNodes c.source c.start
def CompilerConfig.target (c : CompilerConfig) : MGrammar := compileCandidate c.source c.start c.alphabet c.digits
def CompilerConfig.address (c : CompilerConfig) (node : CompileNode) : Nat := ParSimulation.address c.nodes c.digits node

theorem CompilerConfig.at (c : CompilerConfig) (node : CompileNode) (hn : node ∈ c.nodes)
    (slot : Nat) (hs : slot < compilerSlotSize c.digits) :
    ruleAtM c.target.rules (c.address node + slot) =
      some (compilerFragmentAt (fragments c.source c.nodes c.digits (c.address node) node) slot) :=
  compileCandidate_at c.source c.start c.alphabet c.digits node hn slot hs

theorem CompilerConfig.block_at (c : CompilerConfig) (node : CompileNode) (hn : node ∈ c.nodes)
    (before : CompileFragments) (offset : Nat) (rules : List MRule) (after : CompileFragments)
    (hplan : fragments c.source c.nodes c.digits (c.address node) node = before ++ (offset, rules) :: after)
    (hbound : offset + rules.length ≤ compilerSlotSize c.digits)
    (hsep : ∀ f ∈ before, f.1 + f.2.length ≤ offset ∨ offset + rules.length ≤ f.1) :
    RulesAt c.target (c.address node + offset) rules := by
  intro j hj
  have h := c.at node hn (offset + j) (by omega)
  rw [hplan, compilerFragmentAt_block before offset rules after j hj hsep] at h
  simpa only [Nat.add_assoc, ruleAtM_eq_getElem?, List.getElem?_eq_getElem hj, Option.getD_some] using h

end Shallot.MacroPeg.CBV.ParSimulation
