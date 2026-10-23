import MacroPeg.CBVtoCBN.ArgumentRouting

namespace Shallot.MacroPeg.CBVtoCBN

theorem compiledArgument_blocks (c : CompilerConfig) (arity callee : Nat) (actuals : List MExp) (stage : Nat)
    {rule : MRule} (hr : ruleAtM c.source.rules callee = some rule) (ha : rule.arity = actuals.length)
    {a : MExp} (hget : actuals[stage]? = some a) (hn : .args arity callee actuals stage ∈ c.nodes) :
    let base := c.address (.args arity callee actuals stage)
    let width := 5 + 2 * c.digits + 4 * arity + 4 * stage
    RulesAt c.target (base + 10) (captureBlock (base + 10) (base + 5) (base + 7)
      (c.strategy == .callByValueSeq) (width - 2)) ∧
    RulesAt c.target (base + 20) (captureBlock (base + 20) (base + 5) (base + 8)
      (c.strategy == .callByValueSeq) (width - 2)) := by
  have ht : stage ≠ actuals.length := by have h := (List.getElem?_eq_some_iff.mp hget).choose; omega
  let node := CompileNode.args arity callee actuals stage
  let fs := compilerFragments c.source c.strategy c.nodes c.digits (c.address node) node
  constructor
  · apply c.block_at node hn (fs.take 2) 10 _ (fs.drop 3)
    · simp [fs, node, compilerFragments, compilerArgumentFragments, hr, ha, ht, hget]
    · simp [captureBlock, pairSearchBlock, compilerSlotSize]
      omega
    · simp [fs, node, compilerFragments, compilerArgumentFragments, hr, ha, ht, hget]
  · apply c.block_at node hn (fs.take 3) 20 _ []
    · simp [fs, node, compilerFragments, compilerArgumentFragments, hr, ha, ht, hget]
    · simp [captureBlock, pairSearchBlock, compilerSlotSize]
      omega
    · simp [fs, node, compilerFragments, compilerArgumentFragments, hr, ha, ht, hget, captureBlock, pairSearchBlock]

theorem compiledArgument_evalRule (c : CompilerConfig) (arity callee : Nat) (actuals : List MExp) (stage : Nat)
    {rule : MRule} (hr : ruleAtM c.source.rules callee = some rule) (ha : rule.arity = actuals.length)
    {a : MExp} (hget : actuals[stage]? = some a) (hn : .args arity callee actuals stage ∈ c.nodes) :
    ruleAtM c.target.rules (c.address (.args arity callee actuals stage) + 5) = some
      ⟨5 + 2 * c.digits + 4 * arity + 4 * stage + 2,
        .call (c.address (.expr arity a)) (argumentEvalParams (5 + 2 * c.digits + 4 * arity - 4))⟩ := by
  have ht : stage ≠ actuals.length := by have h := (List.getElem?_eq_some_iff.mp hget).choose; omega
  have h := c.at (.args arity callee actuals stage) hn 5 (by unfold compilerSlotSize; omega)
  simpa [compilerFragments, compilerArgumentFragments, compilerFragmentAt, hr, ha, ht, hget,
    argumentEvalParams, CompilerConfig.address] using h

theorem compiledArgument_failRule (c : CompilerConfig) (arity callee : Nat) (actuals : List MExp) (stage : Nat)
    {rule : MRule} (hr : ruleAtM c.source.rules callee = some rule) (ha : rule.arity = actuals.length)
    {a : MExp} (hget : actuals[stage]? = some a) (hn : .args arity callee actuals stage ∈ c.nodes) :
    ruleAtM c.target.rules (c.address (.args arity callee actuals stage) + 6) = some
      ⟨5 + 2 * c.digits + 4 * arity + 4 * stage,
        .call (c.address (.expr arity a) + 1) (paramsFrom 0 (5 + 2 * c.digits + 4 * arity))⟩ := by
  have ht : stage ≠ actuals.length := by have h := (List.getElem?_eq_some_iff.mp hget).choose; omega
  have h := c.at (.args arity callee actuals stage) hn 6 (by unfold compilerSlotSize; omega)
  simpa [compilerFragments, compilerArgumentFragments, compilerFragmentAt, hr, ha, ht, hget, CompilerConfig.address] using h

theorem compiledArgument_nextRule (c : CompilerConfig) (arity callee : Nat) (actuals : List MExp) (stage : Nat)
    {rule : MRule} (hr : ruleAtM c.source.rules callee = some rule) (ha : rule.arity = actuals.length)
    {a : MExp} (hget : actuals[stage]? = some a) (hn : .args arity callee actuals stage ∈ c.nodes)
    (failure : Bool) :
    ruleAtM c.target.rules (c.address (.args arity callee actuals stage) + 7 + primarySlot failure) = some
      ⟨5 + 2 * c.digits + 4 * arity + 4 * stage + 4,
        .call (c.address (.args arity callee actuals (stage + 1)) + primarySlot failure)
          (paramsFrom 4 (5 + 2 * c.digits + 4 * arity + 4 * stage) ++ paramsFrom 0 4)⟩ := by
  have ht : stage ≠ actuals.length := by have h := (List.getElem?_eq_some_iff.mp hget).choose; omega
  cases failure
  · have h := c.at (.args arity callee actuals stage) hn 7 (by unfold compilerSlotSize; omega)
    simpa [compilerFragments, compilerArgumentFragments, compilerFragmentAt, hr, ha, ht, hget,
      CompilerConfig.address, primarySlot] using h
  · have h := c.at (.args arity callee actuals stage) hn 8 (by unfold compilerSlotSize; omega)
    simpa [compilerFragments, compilerArgumentFragments, compilerFragmentAt, hr, ha, ht, hget,
      CompilerConfig.address, primarySlot, Nat.add_assoc] using h

end Shallot.MacroPeg.CBVtoCBN
