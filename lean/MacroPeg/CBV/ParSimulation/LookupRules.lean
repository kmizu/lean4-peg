import MacroPeg.CBV.ParSimulation.LookupRouting

namespace Shallot.MacroPeg.CBV.ParSimulation

open PrefixCounters
open CBVtoCBN (CompileNode RulesAt compilerSlotSize compilerFragmentAt)

def lookupClockOffset (digits : Nat) (failure : Bool) : Nat := if failure then 11 + 2 * digits else 10
def lookupPackOffset (digits : Nat) (failure : Bool) : Nat := 12 + 4 * digits + primarySlot failure

theorem compiledLookup_primary (c : CompilerConfig) {callee : Nat} {rule : MRule}
    (hr : ruleAtM c.source.rules callee = some rule) (hn : .lookup callee ∈ c.nodes) (failure : Bool) :
    ruleAtM c.target.rules (c.address (.lookup callee) + primarySlot failure) =
      some ⟨3 + c.digits + 2 * rule.arity,
        .call (c.address (.lookup callee) + lookupClockOffset c.digits failure)
          (lookupClockParams c.digits (2 * rule.arity))⟩ := by
  have h := c.at (.lookup callee) hn (primarySlot failure)
    (by cases failure <;> simp [primarySlot, compilerSlotSize] <;> omega)
  cases failure <;>
    simpa [fragments, lookupFragments, compilerFragmentAt, hr, primarySlot, lookupClockOffset,
      CompilerConfig.address, Nat.add_assoc] using h

theorem compiledLookup_clock (c : CompilerConfig) {callee : Nat} {rule : MRule}
    (hr : ruleAtM c.source.rules callee = some rule) (hn : .lookup callee ∈ c.nodes) (failure : Bool) :
    let base := c.address (.lookup callee)
    RulesAt c.target (base + lookupClockOffset c.digits failure)
      (clockBlock (base + lookupClockOffset c.digits failure) 0
        (base + lookupPackOffset c.digits failure) (base + 14 + 4 * c.digits)
        c.digits (2 + 2 * rule.arity)) := by
  let node := CompileNode.lookup callee
  let fs := fragments c.source c.nodes c.digits (c.address node) node
  cases failure with
  | false =>
    apply c.block_at node hn (fs.take 1) 10 _ (fs.drop 2)
    · simp [fs, node, fragments, lookupFragments, hr, lookupClockOffset, lookupPackOffset, primarySlot,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    · simp only [clockBlock_length, compilerSlotSize]; omega
    · simp [fs, node, fragments, lookupFragments, hr]
  | true =>
    apply c.block_at node hn (fs.take 2) (11 + 2 * c.digits) _ (fs.drop 3)
    · simp [fs, node, fragments, lookupFragments, hr, lookupClockOffset, lookupPackOffset, primarySlot,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      congr 1
      omega
    · simp only [clockBlock_length, compilerSlotSize]; omega
    · simp [fs, node, fragments, lookupFragments, hr, clockBlock_length]
      omega

theorem compiledLookup_callbacks (c : CompilerConfig) {callee : Nat} {rule : MRule}
    (hr : ruleAtM c.source.rules callee = some rule) (hn : .lookup callee ∈ c.nodes) :
    let base := c.address (.lookup callee)
    let body := c.address (.expr rule.arity rule.body)
    let w := 3 + c.digits + 2 * rule.arity
    RulesAt c.target (base + (12 + 4 * c.digits))
      [⟨w, .call body (lookupPackParams c.digits (2 * rule.arity))⟩,
        ⟨w, .call (body + 1) (lookupPackParams c.digits (2 * rule.arity))⟩,
        ⟨2 + 2 * rule.arity, MExp.failAlways⟩] := by
  let node := CompileNode.lookup callee
  let fs := fragments c.source c.nodes c.digits (c.address node) node
  apply c.block_at node hn (fs.take 3) (12 + 4 * c.digits) _ []
  · simp [fs, node, fragments, lookupFragments, hr, CompilerConfig.address, Nat.add_assoc]
  · simp only [List.length_cons, List.length_nil, compilerSlotSize]; omega
  · simp [fs, node, fragments, lookupFragments, hr, clockBlock_length]
    constructor <;> omega

theorem compiledLookup_pack (c : CompilerConfig) {callee : Nat} {rule : MRule}
    (hr : ruleAtM c.source.rules callee = some rule) (hn : .lookup callee ∈ c.nodes) (failure : Bool) :
    ruleAtM c.target.rules (c.address (.lookup callee) + lookupPackOffset c.digits failure) =
      some ⟨3 + c.digits + 2 * rule.arity,
        .call (c.address (.expr rule.arity rule.body) + primarySlot failure)
          (lookupPackParams c.digits (2 * rule.arity))⟩ := by
  have h := compiledLookup_callbacks c hr hn (primarySlot failure)
    (by cases failure <;> simp [primarySlot])
  cases failure <;> simpa only [lookupPackOffset, primarySlot, Bool.false_eq_true, Bool.true_eq,
    if_false, if_true, Nat.add_zero, Nat.add_assoc, ruleAtM] using h

theorem compiledLookup_zero (c : CompilerConfig) {callee : Nat} {rule : MRule}
    (hr : ruleAtM c.source.rules callee = some rule) (hn : .lookup callee ∈ c.nodes) :
    ruleAtM c.target.rules (c.address (.lookup callee) + 14 + 4 * c.digits) =
      some ⟨2 + 2 * rule.arity, MExp.failAlways⟩ := by
  have h := compiledLookup_callbacks c hr hn 2 (by simp)
  have he : c.address (.lookup callee) + (12 + 4 * c.digits) + 2 =
      c.address (.lookup callee) + 14 + 4 * c.digits := by omega
  simpa only [he, ruleAtM] using h

end Shallot.MacroPeg.CBV.ParSimulation
