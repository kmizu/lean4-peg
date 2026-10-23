import MacroPeg.CBVtoCBN.ArgumentWrappers

namespace Shallot.MacroPeg.CBVtoCBN

/-- One real argument stage preserves evaluation, invoking a continuation only for a successful captured prefix. -/
theorem compiledArguments_step (c : CompilerConfig) (hg : c.source.FirstOrder) (hs : c.strategy ≠ .callByName)
    (x : List Char) (ds : List Nat) (hd : ds.length = c.digits) (E C : CapturedEnv)
    (callee : Nat) (actuals : List MExp) (stage : Nat) (hc : C.length = stage)
    {rule : MRule} (hr : ruleAtM c.source.rules callee = some rule) (ha : rule.arity = actuals.length)
    {a : MExp} (hget : actuals[stage]? = some a) (hfo : a.FirstOrder)
    (hn : .args E.length callee actuals stage ∈ c.nodes) (harg : SyntaxCorrect c x ds E a)
    (p q : Nat) (hp : p ≤ x.length) (hq : q ≤ x.length)
    (hnext : ∀ j, j ≤ p → ArgsCorrect c x ds E (C ++ [(p, j)]) callee actuals (stage + 1)
      (if c.strategy == .callByValueSeq then j else p) q) :
    ArgsCorrect c x ds E C callee actuals stage p q := by
  let base := c.address (.args E.length callee actuals stage)
  let thread := c.strategy == .callByValueSeq
  let rest := stageRest x ds E C q
  let A := evV c.source x c.strategy (tblV c.source x c.strategy (clockValue x.length ds)) (decodeEnv x E) a p
  let F := fun w next => argumentValue c x ds E (decodeEnv x C ++ [w]) callee (actuals.drop (stage + 1)) next
  have ht : stage ≠ actuals.length := by have hi := (List.getElem?_eq_some_iff.mp hget).choose; omega
  have hrest : rest.length = 5 + 2 * c.digits + 4 * E.length + 4 * stage - 2 := by
    rw [stageRest_length, hd, hc]; omega
  have hblocks := compiledArgument_blocks c E.length callee actuals stage hr ha hget hn
  dsimp only at hblocks
  rw [← hrest] at hblocks
  have heval : ∀ j, j ≤ x.length → RootTest c.target
      (.call (base + 5) (skipN p :: skipN (x.length - p) :: skipN j :: skipN (x.length - j) :: rest)) x
      (A = some (some j)) := fun j hj => argumentEval_test c x ds hd E C callee actuals stage hc hr ha hget hn p q j (harg p hp j hj)
  have hcont : ∀ failure j, j ≤ x.length → A = some (some j) → RootTest c.target
      (.call (base + 7 + primarySlot failure)
        (captureNextArgs thread (skipN j) (skipN (x.length - j)) (skipN p) (skipN (x.length - p)) rest)) x
      (F (pre x p j) (if thread then j else p) = some (if failure then none else some q)) := by
    intro failure j _ hsuccess
    have hjp : j ≤ p := evaluatedCapture_le hg hs hfo (decodeEnv x E) (clockValue x.length ds) hp hsuccess
    have h := argumentNext_test c x ds hd E C callee actuals stage hc hr ha hget hn p q j thread failure (hnext j hjp)
    rw [← argumentValue_capture c x ds E C callee (actuals.drop (stage + 1)) p j (if thread then j else p)] at h
    exact h
  have hc0 := hblocks.1.capture_test thread rest x p (some q) A F heval
    (fun j hj hm => by simpa [primarySlot] using hcont false j hj hm)
  have hc1 := hblocks.2.capture_test thread rest x p none A F heval
    (fun j hj hm => by simpa [primarySlot] using hcont true j hj hm)
  have hbound := evV_ok (g := c.source) (s := c.strategy) (E := decodeEnv x E)
    (tblV_ok c.source x c.strategy (clockValue x.length ds)) a p hp
  have hsuccess := captureSuccess_test hbound hc0
  have hfailure := captureFailure_test hbound
    (argumentFailure_test c x ds hd E C callee actuals stage hc hr ha hget hn p q (harg p hp q hq)) hc1
  have hresult : argumentResult c x ds E C callee (actuals.drop stage) p =
      seqResult A (fun j => F (pre x p j) (if thread then j else p)) := by
    rw [drop_argument hget, argumentResult_cons]
  have hlen := stageArgs_length x ds E C p q
  rw [hd, hc] at hlen
  have hall : MExp.substArgs (stageArgs x ds E C p q)
      (paramsFrom 0 (5 + 2 * c.digits + 4 * E.length + 4 * stage)) = stageArgs x ds E C p q := by
    rw [← hlen]
    exact subst_paramsFrom _
  constructor
  · change RootTest c.target (c.argumentCall E.length callee actuals stage false (stageArgs x ds E C p q)) x _
    rw [hresult, c.argument_unfold x ds hd E C callee actuals stage hc hn p q false]
    simp [argumentRule, compilerArgumentFragments, compilerFragmentAt, hr, ha, ht, hget, primarySlot, primaryRule]
    change RootTest c.target (MExp.subst (stageArgs x ds E C p q)
      (.call (base + 10) (.eps :: paramsFrom 0 (5 + 2 * c.digits + 4 * E.length + 4 * stage)))) x _
    simp only [MExp.subst, MExp.substArgs, hall]
    simpa only [stageArgs_split] using hsuccess
  · change RootTest c.target (c.argumentCall E.length callee actuals stage true (stageArgs x ds E C p q)) x _
    rw [hresult, c.argument_unfold x ds hd E C callee actuals stage hc hn p q true]
    simp [argumentRule, compilerArgumentFragments, compilerFragmentAt, hr, ha, ht, hget, primarySlot, primaryRule]
    change RootTest c.target (MExp.subst (stageArgs x ds E C p q)
      (.alt (compilerCall (base + 6) (5 + 2 * c.digits + 4 * E.length + 4 * stage))
        (.call (base + 20) (.eps :: paramsFrom 0 (5 + 2 * c.digits + 4 * E.length + 4 * stage))))) x _
    simp only [compilerCall, MExp.subst, MExp.substArgs, hall]
    simpa only [stageArgs_split] using hfailure

/-- Argument stages are correct once the table oracle at the current clock is correct.
The source expression hypotheses concern only the proper argument subexpressions. -/
theorem compiledArguments_correct (c : CompilerConfig) (hg : c.source.FirstOrder) (hs : c.strategy ≠ .callByName)
    (x : List Char) (ds : List Nat) (hd : ds.length = c.digits) (E : CapturedEnv) (callee : Nat) (actuals : List MExp)
    {rule : MRule} (hr : ruleAtM c.source.rules callee = some rule) (ha : rule.arity = actuals.length)
    (hfo : MExp.FirstOrderArgs actuals) (hav : StagesAvailable c.nodes E.length callee actuals)
    (harg : ∀ a ∈ actuals, SyntaxCorrect c x ds E a)
    (hlookup : ∀ C, ValidEnv x.length C → C.length = rule.arity → ∀ p, p ≤ x.length → ∀ q, q ≤ x.length →
      LookupCorrect c x ds C callee p q) :
    ∀ stage C, stage ≤ actuals.length → C.length = stage → ValidEnv x.length C →
      ∀ p, p ≤ x.length → ∀ q, q ≤ x.length → ArgsCorrect c x ds E C callee actuals stage p q := by
  have aux : ∀ remaining stage C, stage + remaining = actuals.length → C.length = stage → ValidEnv x.length C →
      ∀ p, p ≤ x.length → ∀ q, q ≤ x.length → ArgsCorrect c x ds E C callee actuals stage p q := by
    intro remaining
    induction remaining with
    | zero =>
      intro stage C hlen hc hv p hp q hq
      have heq : stage = actuals.length := by omega
      rw [heq] at hc ⊢
      exact compiledArguments_done c x ds hd E C callee actuals hc (hav _ (by omega)) hr ha p q
        (hlookup C hv (hc.trans ha.symm) p hp q hq)
    | succ remaining ih =>
      intro stage C hlen hc hv p hp q hq
      have hb : stage < actuals.length := by omega
      have hget : actuals[stage]? = some actuals[stage] := List.getElem?_eq_getElem hb
      have hm := List.mem_of_getElem? hget
      have hafo : actuals[stage].FirstOrder := by
        have aux : ∀ es : List MExp, MExp.FirstOrderArgs es → ∀ e ∈ es, e.FirstOrder := by
          intro es
          induction es with
          | nil => intro _ e he; cases he
          | cons e es ih =>
            intro hf a ha
            rcases List.mem_cons.mp ha with rfl | ha
            · exact hf.1
            · exact ih hf.2 a ha
        exact aux actuals hfo _ hm
      apply compiledArguments_step c hg hs x ds hd E C callee actuals stage hc hr ha hget hafo (hav stage (by omega))
        (harg _ hm) p q hp hq
      intro j hj
      apply ih (stage + 1) (C ++ [(p, j)]) (by omega)
      · simp [hc]
      · exact hv.append_capture hp hj
      · cases ht : c.strategy == .callByValueSeq <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega
      · exact hq
  intro stage C hstage hc hv
  exact aux (actuals.length - stage) stage C (by omega) hc hv

end Shallot.MacroPeg.CBVtoCBN
