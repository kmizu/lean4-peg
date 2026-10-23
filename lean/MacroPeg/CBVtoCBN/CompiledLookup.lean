import MacroPeg.CBVtoCBN.LookupRouting

namespace Shallot.MacroPeg.CBVtoCBN

def lookupClockOffset (d : Nat) (failure : Bool) : Nat := if failure then 11 + 2 * d else 10

def lookupPackOffset (d : Nat) (failure : Bool) : Nat := if failure then 13 + 4 * d else 12 + 4 * d

theorem lookupNode_available (c : CompilerConfig) (callee : Nat) {rule : MRule}
    (hr : ruleAtM c.source.rules callee = some rule) : .lookup callee ∈ c.nodes := by
  have hi : callee < c.source.rules.length := by
    rw [ruleAtM_eq_getElem?] at hr
    exact (List.getElem?_eq_some_iff.mp hr).choose
  exact compilerNodes_lookup _ _ _ hi

theorem compiledLookup_rule (c : CompilerConfig) (callee : Nat) {rule : MRule}
    (hr : ruleAtM c.source.rules callee = some rule) (failure : Bool) :
    ruleAtM c.target.rules (c.address (.lookup callee) + primarySlot failure) = some
      ⟨5 + 2 * c.digits + 4 * rule.arity,
        .call (c.address (.lookup callee) + lookupClockOffset c.digits failure)
          (lookupClockParams (2 * c.digits) (4 * rule.arity))⟩ := by
  have h := c.at (.lookup callee) (lookupNode_available c callee hr) (primarySlot failure)
    (by cases failure <;> simp [primarySlot, compilerSlotSize] <;> omega)
  cases failure <;> simpa [compilerFragments, compilerLookupFragments, hr, primarySlot, compilerFragmentAt,
    primaryRule, lookupClockOffset, lookupClockParams, Nat.add_assoc] using h

theorem compiledLookup_zero (c : CompilerConfig) (callee : Nat) {rule : MRule}
    (hr : ruleAtM c.source.rules callee = some rule) :
    ruleAtM c.target.rules (c.address (.lookup callee) + 3) = some ⟨4 + 4 * rule.arity, MExp.failAlways⟩ := by
  have h := c.at (.lookup callee) (lookupNode_available c callee hr) 3 (by unfold compilerSlotSize; omega)
  simpa [compilerFragments, compilerLookupFragments, compilerFragmentAt, hr] using h

theorem compiledLookup_clock (c : CompilerConfig) (callee : Nat) {rule : MRule}
    (hr : ruleAtM c.source.rules callee = some rule) (failure : Bool) :
    let base := c.address (.lookup callee)
    RulesAt c.target (base + lookupClockOffset c.digits failure)
      (clockBlock (base + lookupClockOffset c.digits failure) (base + lookupPackOffset c.digits failure)
        (base + 3) c.digits (4 + 4 * rule.arity)) := by
  let node := CompileNode.lookup callee
  let fs := compilerFragments c.source c.strategy c.nodes c.digits (c.address node) node
  cases failure
  · apply c.block_at node (lookupNode_available c callee hr) (fs.take 2) 10 _ (fs.drop 3)
    · simp [fs, node, compilerFragments, compilerLookupFragments, hr, lookupClockOffset, lookupPackOffset, Nat.add_assoc]
    · simp only [clockBlock_length, compilerSlotSize]
      omega
    · simp [fs, node, compilerFragments, compilerLookupFragments, hr]
  · apply c.block_at node (lookupNode_available c callee hr) (fs.take 3) (11 + 2 * c.digits) _ (fs.drop 4)
    · simp [fs, node, compilerFragments, compilerLookupFragments, hr, lookupClockOffset, lookupPackOffset, Nat.add_assoc]
    · simp only [clockBlock_length, compilerSlotSize]
      omega
    · simp [fs, node, compilerFragments, compilerLookupFragments, hr, clockBlock_length]
      omega

theorem compiledLookup_pack (c : CompilerConfig) (callee : Nat) {rule : MRule}
    (hr : ruleAtM c.source.rules callee = some rule) (failure : Bool) :
    ruleAtM c.target.rules (c.address (.lookup callee) + lookupPackOffset c.digits failure) = some
      ⟨5 + 2 * c.digits + 4 * rule.arity,
        .call (c.address (.expr rule.arity rule.body) + primarySlot failure)
          (lookupBodyParams (2 * c.digits) (4 * rule.arity))⟩ := by
  let node := CompileNode.lookup callee
  let fs := compilerFragments c.source c.strategy c.nodes c.digits (c.address node) node
  have hb : RulesAt c.target (c.address node + (12 + 4 * c.digits))
      [⟨5 + 2 * c.digits + 4 * rule.arity,
        .call (c.address (.expr rule.arity rule.body)) (lookupBodyParams (2 * c.digits) (4 * rule.arity))⟩,
       ⟨5 + 2 * c.digits + 4 * rule.arity,
        .call (c.address (.expr rule.arity rule.body) + 1) (lookupBodyParams (2 * c.digits) (4 * rule.arity))⟩] := by
    apply c.block_at node (lookupNode_available c callee hr) (fs.take 4) (12 + 4 * c.digits) _ []
    · simp [fs, node, compilerFragments, compilerLookupFragments, hr, lookupBodyParams, CompilerConfig.address]
    · simp only [List.length_cons, List.length_nil, compilerSlotSize]
      omega
    · simp [fs, node, compilerFragments, compilerLookupFragments, hr, clockBlock_length]
      omega
  cases failure
  · simpa [node, lookupPackOffset, primarySlot, ruleAtM, Nat.add_assoc] using hb 0 (by simp)
  · have h := hb 1 (by simp)
    rw [show c.address node + (12 + 4 * c.digits) + 1 = c.address node + (13 + 4 * c.digits) by omega] at h
    simpa [node, lookupPackOffset, primarySlot, ruleAtM] using h

theorem RootTest.of_equiv {g : MGrammar} {a b : MExp} {x : List Char} {P : Prop}
    (he : ∀ r, MacroObs g a x r ↔ MacroObs g b x r) (h : RootTest g b x P) : RootTest g a x P :=
  ⟨fun hp => (he _).mpr (h.1 hp), fun hn => (he _).mpr (h.2 hn)⟩

theorem RulesAt.clock_iff {g : MGrammar} {entry next onZero digits : Nat} (ctx : List MExp)
    (h : RulesAt g entry (clockBlock entry next onZero digits ctx.length)) (hg : g.FirstOrder)
    (x : List Char) (ds : List Nat) (hd : ds.length = digits) (hv : ∀ k ∈ ds, k ≤ x.length)
    (r : Option (List Char)) :
    MacroObs g (.call entry (skipN x.length :: (clockArgs x.length ds ++ ctx))) x r ↔
      match predClock x.length ds with
      | none => MacroObs g (.call onZero ctx) x r
      | some out => MacroObs g (.call next (skipN x.length :: (clockArgs x.length out ++ ctx))) x r := by
  obtain ⟨preRules, tail, hpre, he⟩ := h.split (by simp [clockBlock])
  have ht := clockBlock_iff preRules tail next onZero digits ctx
    (by simpa only [hpre, ← he] using hg) x ds hd hv r
  cases hc : predClock x.length ds with
  | none => simpa only [hpre, ← he, hc] using ht
  | some out => simpa only [hpre, ← he, hc] using ht

/-- Generated table lookup agrees with one source table entry, provided called bodies are correct at the predecessor clock. -/
theorem compiledLookup_mode (c : CompilerConfig) (x : List Char) (ds : List Nat) (hd : ds.length = c.digits)
    (hv : ∀ k ∈ ds, k ≤ x.length) (E : CapturedEnv) (callee : Nat) {rule : MRule}
    (hr : ruleAtM c.source.rules callee = some rule) (he : E.length = rule.arity)
    (p q : Nat) (hp : p ≤ x.length) (failure : Bool)
    (ih : ∀ out, predClock x.length ds = some out → ExprCorrect c x out E rule.body p q) :
    RootTest c.target (c.lookupCall callee failure (evalArgs x ds E p q)) x
      (valAt (tblV c.source x c.strategy (clockValue x.length ds) callee (decodeEnv x E)) p =
        some (if failure then none else some q)) := by
  let base := c.address (.lookup callee)
  let ctx := [skipN p, skipN (x.length - p), skipN q, skipN (x.length - q)] ++ envArgs x.length E
  have hctx : ctx.length = 4 + 4 * rule.arity := by simp [ctx, envArgs_length, he]; omega
  have hC : (clockArgs x.length ds).length = 2 * c.digits := by rw [clockArgs_length, hd]
  have hV : (envArgs x.length E).length = 4 * rule.arity := by rw [envArgs_length, he]
  simp only [CompilerConfig.lookupCall]
  rw [rootTest_call_iff (compiledLookup_rule c callee hr failure)
    (by rw [evalArgs_length, hd, he])]
  change RootTest c.target (.call (base + lookupClockOffset c.digits failure)
    (MExp.substArgs ([skipN p, skipN (x.length - p), skipN q, skipN (x.length - q), skipN x.length] ++
      (clockArgs x.length ds ++ envArgs x.length E)) (lookupClockParams (2 * c.digits) (4 * rule.arity)))) x _
  rw [← hC, ← hV, subst_lookupClockParams]
  simp only [List.append_assoc]
  have hb := compiledLookup_clock c callee hr failure
  dsimp only at hb
  rw [← hctx] at hb
  have hobs := hb.clock_iff ctx c.firstOrder x ds hd hv
  cases hc : predClock x.length ds with
  | none =>
    have hz := clockTable_zero c.source x c.strategy callee (decodeEnv x E) ds hv hc p
    have ht : RootTest c.target (.call (base + 3) ctx) x False := by
      rw [rootTest_call_iff (compiledLookup_zero c callee hr) (by rw [hctx])]
      simpa [MExp.failAlways, MExp.subst] using rootTest_fail c.target x
    apply RootTest.of_equiv (fun r => by simpa only [hc] using hobs r)
    exact ht.congr (by rw [hz]; simp)
  | some out =>
    have hs := predClock_spec x.length ds hv
    rw [hc] at hs
    have hdo : out.length = c.digits := hs.1.trans hd
    have hCo : (clockArgs x.length out).length = 2 * c.digits := by rw [clockArgs_length, hdo]
    have ho := ih out hc
    have ht : RootTest c.target (.call (base + lookupPackOffset c.digits failure)
        (skipN x.length :: (clockArgs x.length out ++ ctx))) x
        (evV c.source x c.strategy (tblV c.source x c.strategy (clockValue x.length out)) (decodeEnv x E) rule.body p =
          some (if failure then none else some q)) := by
      rw [rootTest_call_iff (compiledLookup_pack c callee hr failure)
        (by simp only [List.length_cons, List.length_append, clockArgs_length, hctx, hdo]; omega)]
      change RootTest c.target (.call (c.address (.expr rule.arity rule.body) + primarySlot failure)
        (MExp.substArgs (skipN x.length :: (clockArgs x.length out ++
          ([skipN p, skipN (x.length - p), skipN q, skipN (x.length - q)] ++ envArgs x.length E)))
          (lookupBodyParams (2 * c.digits) (4 * rule.arity)))) x _
      rw [← hCo, ← hV, subst_lookupBodyParams]
      cases failure
      · simpa [CompilerConfig.exprCall, primarySlot, evalArgs, evalRest, he] using ho.1
      · simpa [CompilerConfig.exprCall, primarySlot, evalArgs, evalRest, he] using ho.2
    apply RootTest.of_equiv (fun r => by simpa only [hc] using hobs r)
    apply ht.congr
    rw [clockTable_step hr (decodeEnv x E) ds out hv hc hp]

/-- Both lookup predicates preserve source success and source explicit failure at the current clock. -/
theorem compiledLookup_correct (c : CompilerConfig) (x : List Char) (ds : List Nat) (hd : ds.length = c.digits)
    (hv : ∀ k ∈ ds, k ≤ x.length) (E : CapturedEnv) (callee : Nat) {rule : MRule}
    (hr : ruleAtM c.source.rules callee = some rule) (he : E.length = rule.arity)
    (p q : Nat) (hp : p ≤ x.length)
    (ih : ∀ out, predClock x.length ds = some out → ExprCorrect c x out E rule.body p q) :
    LookupCorrect c x ds E callee p q :=
  ⟨compiledLookup_mode c x ds hd hv E callee hr he p q hp false ih,
    compiledLookup_mode c x ds hd hv E callee hr he p q hp true ih⟩

end Shallot.MacroPeg.CBVtoCBN
