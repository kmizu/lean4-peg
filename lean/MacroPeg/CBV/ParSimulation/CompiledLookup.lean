import MacroPeg.CBV.ParSimulation.LookupRules

namespace Shallot.MacroPeg.CBV.ParSimulation

open PrefixCounters RootObservation
open CBVtoCBN (CompileNode predClock predClock_spec clockValue clockTable_step clockTable_zero)

def lookupContext (n : Nat) (E : CapturedEnv) (p q : Nat) : List Nat :=
  (n - p) :: (n - q) :: envPositions n E

def lookupClockValues (x : List Char) (ds : List Nat) (E : CapturedEnv) (p q : Nat) : List MExp :=
  prefixValues x (x.length :: (ds ++ lookupContext x.length E p q))

theorem lookup_rotate_values (c : CompilerConfig) (x : List Char) (ds : List Nat)
    (hd : ds.length = c.digits) (E : CapturedEnv) (arity : Nat) (hlen : E.length = arity) (p q : Nat) :
    MExp.substArgs (stateValues x ds E p q) (lookupClockParams c.digits (2 * arity)) =
      lookupClockValues x ds E p q := by
  have h := lookupClockParams_subst (.lit (x.take (x.length - p))) (.lit (x.take (x.length - q)))
    (.lit (x.take x.length)) (prefixValues x ds) (prefixValues x (envPositions x.length E))
  simpa only [prefixValues_length, envPositions_length, hd, hlen, stateValues, statePositions,
    lookupClockValues, lookupContext, prefixValues, prefixValues_append] using h

theorem lookup_unpack_values (c : CompilerConfig) (x : List Char) (ds : List Nat)
    (hd : ds.length = c.digits) (E : CapturedEnv) (arity : Nat) (hlen : E.length = arity) (p q : Nat) :
    MExp.substArgs (lookupClockValues x ds E p q) (lookupPackParams c.digits (2 * arity)) =
      stateValues x ds E p q := by
  have h := lookupPackParams_subst (.lit (x.take (x.length - p))) (.lit (x.take (x.length - q)))
    (.lit (x.take x.length)) (prefixValues x ds) (prefixValues x (envPositions x.length E))
  simpa only [prefixValues_length, envPositions_length, hd, hlen, stateValues, statePositions,
    lookupClockValues, lookupContext, prefixValues, prefixValues_append] using h

/-- Observations of the actual generated lookup equal those of the actual
body after one clock decrement. Exhaustion produces finite predicate failure. -/
theorem compiledLookup_obs_iff (c : CompilerConfig) (x : List Char) (ds : List Nat)
    (hd : ds.length = c.digits) (hv : ∀ k ∈ ds, k ≤ x.length) (E : CapturedEnv)
    (callee : Nat) (rule : MRule) (hr : ruleAtM c.source.rules callee = some rule)
    (hn : .lookup callee ∈ c.nodes) (hlen : E.length = rule.arity)
    (p q : Nat) (failure : Bool) (r : Option (List Char)) :
    SObs c.target .callByValuePar
      (.call (c.address (.lookup callee) + primarySlot failure) (stateValues x ds E p q)) x r ↔
      match predClock x.length ds with
      | none => r = none
      | some out => SObs c.target .callByValuePar
          (c.exprCall E.length rule.body failure (stateValues x out E p q)) x r := by
  have hPrimary := compiledLookup_primary c hr hn failure
  have hArgs := prefixValues_args c.target x (statePositions x.length ds E p q)
  change DerivesArgsPar c.target .callByValuePar x (stateValues x ds E p q) (stateValues x ds E p q) at hArgs
  rw [par_call_iff hPrimary (by rw [stateValues_length, hd, hlen]) hArgs]
  change SObs c.target .callByValuePar
    (.call (c.address (.lookup callee) + lookupClockOffset c.digits failure)
      (MExp.substArgs (stateValues x ds E p q) (lookupClockParams c.digits (2 * rule.arity)))) x r ↔ _
  rw [lookup_rotate_values c x ds hd E rule.arity hlen p q]
  let ctx := lookupContext x.length E p q
  have hCtx : ctx.length = 2 + 2 * rule.arity := by
    simp only [ctx, lookupContext, List.length_cons, envPositions_length, hlen]; omega
  have hBlock := compiledLookup_clock c hr hn failure
  dsimp only at hBlock
  have hClock := RulesAt.clock_iff ctx (by simpa only [hCtx] using hBlock)
    c.equal_rule x ds hd hv r
  change SObs c.target .callByValuePar
    (.call (c.address (.lookup callee) + lookupClockOffset c.digits failure)
      (prefixValues x (x.length :: (ds ++ ctx)))) x r ↔ _
  rw [hClock]
  cases hpred : predClock x.length ds with
  | none =>
    simp only [hpred]
    have hZero := compiledLookup_zero c hr hn
    have ht : SObs c.target .callByValuePar
        (.call (c.address (.lookup callee) + 14 + 4 * c.digits) (prefixValues x ctx)) x none := by
      apply par_call hZero (by simp only [prefixValues_length, hCtx]) (prefixValues_args c.target x ctx)
      exact ⟨_, .notOk _ _ _ _ (.eps x), rfl⟩
    exact unique_iff ht r
  | some out =>
    simp only [hpred]
    have hSpec := predClock_spec x.length ds hv
    rw [hpred] at hSpec
    have hOut : out.length = c.digits := hSpec.1.trans hd
    have hPack := compiledLookup_pack c hr hn failure
    have hVal := prefixValues_args c.target x (x.length :: (out ++ ctx))
    rw [par_call_iff hPack
      (by simp only [prefixValues_length, List.length_cons, List.length_append, hCtx, hOut]; omega) hVal]
    change SObs c.target .callByValuePar
      (.call (c.address (.expr rule.arity rule.body) + primarySlot failure)
        (MExp.substArgs (lookupClockValues x out E p q) (lookupPackParams c.digits (2 * rule.arity)))) x r ↔ _
    rw [lookup_unpack_values c x out hOut E rule.arity hlen p q]
    simp only [CompilerConfig.exprCall, hlen]

def LookupCorrect (c : CompilerConfig) (x : List Char) (ds : List Nat) (E : CapturedEnv)
    (callee p q : Nat) : Prop :=
  Predicate c.target .callByValuePar
    (.call (c.address (.lookup callee)) (stateValues x ds E p q)) x
    (valAt (tblV c.source x .callByValueSeq (clockValue x.length ds) callee (decodeEnv x E)) p = some (some q)) ∧
  Predicate c.target .callByValuePar
    (.call (c.address (.lookup callee) + 1) (stateValues x ds E p q)) x
    (valAt (tblV c.source x .callByValueSeq (clockValue x.length ds) callee (decodeEnv x E)) p = some none)

/-- Table lookup is correct once the source body predicates are correct at
the smaller clock. The premise is precisely the later clock induction. -/
theorem compiledLookup_correct (c : CompilerConfig) (x : List Char) (ds : List Nat)
    (hd : ds.length = c.digits) (hv : ∀ k ∈ ds, k ≤ x.length) (E : CapturedEnv)
    (callee : Nat) (rule : MRule) (hr : ruleAtM c.source.rules callee = some rule)
    (hn : .lookup callee ∈ c.nodes) (hlen : E.length = rule.arity)
    (p q : Nat) (hp : p ≤ x.length)
    (hBody : ∀ out, predClock x.length ds = some out → ExprCorrect c x out E rule.body p q) :
    LookupCorrect c x ds E callee p q := by
  have hFlag : ∀ failure, Predicate c.target .callByValuePar
      (.call (c.address (.lookup callee) + primarySlot failure) (stateValues x ds E p q)) x
      (valAt (tblV c.source x .callByValueSeq (clockValue x.length ds) callee (decodeEnv x E)) p =
        some (if failure then none else some q)) := by
    intro failure
    have hObs := compiledLookup_obs_iff c x ds hd hv E callee rule hr hn hlen p q failure
    cases hpred : predClock x.length ds with
    | none =>
      simp only [hpred] at hObs
      have hSource := clockTable_zero c.source x .callByValueSeq callee (decodeEnv x E) ds hv hpred p
      constructor
      · intro h
        rw [hSource] at h
        cases h
      · intro _
        exact (hObs none).2 rfl
    | some out =>
      simp only [hpred] at hObs
      have hSource := clockTable_step (s := .callByValueSeq) hr (decodeEnv x E) ds out hv hpred hp
      have ht : Predicate c.target .callByValuePar
          (c.exprCall E.length rule.body failure (stateValues x out E p q)) x
          (sourceResult c x out E rule.body p = some (if failure then none else some q)) := by
        cases failure
        · exact (hBody out hpred).1
        · exact (hBody out hpred).2
      constructor
      · intro h
        rw [hSource] at h
        apply (hObs (some x)).2
        exact ht.1 h
      · intro h
        apply (hObs none).2
        exact ht.2 (by intro hs; apply h; rw [hSource]; exact hs)
  exact ⟨by simpa only [primarySlot, Bool.false_eq_true, if_false, Nat.add_zero] using hFlag false,
    by simpa only [primarySlot, Bool.true_eq, if_true] using hFlag true⟩

end Shallot.MacroPeg.CBV.ParSimulation
