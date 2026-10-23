import MacroPeg.CBV.ParSimulation.CompiledCalls

namespace Shallot.MacroPeg.CBV.ParSimulation

open CBVtoCBN (ExprAvailable ArgsAvailable compilerStart_available compilerBody_available
  compilerNodes_lookup unicodeAlphabet clockValue predClock_spec)

def CallHandler (c : CompilerConfig) (x : List Char) (ds : List Nat) (E : CapturedEnv) : Prop :=
  ∀ callee actuals (rule : MRule), ruleAtM c.source.rules callee = some rule → rule.arity = actuals.length →
    MExp.FirstOrderArgs actuals → ExprAvailable c.nodes E.length (.call callee actuals) →
    (∀ a ∈ actuals, SyntaxCorrect c x ds E a) → SyntaxCorrect c x ds E (.call callee actuals)

mutual
  theorem compiledSyntax_correct (c : CompilerConfig) (hAlphabet : c.alphabet = unicodeAlphabet)
      (x : List Char) (ds : List Nat) (hd : ds.length = c.digits) (E : CapturedEnv) (hv : ValidEnv x.length E)
      (hCall : CallHandler c x ds E) :
      ∀ e, e.FirstOrder → ExprAvailable c.nodes E.length e → SyntaxCorrect c x ds E e
    | .eps, _, hav => fun p hp q hq => compiledAtom_correct c x ds hd E .eps hav.self p q hp hq
    | .any, _, hav => fun p hp q hq => compiledAtom_correct c x ds hd E .any hav.self p q hp hq
    | .chr ch, _, hav => fun p hp q hq => compiledAtom_correct c x ds hd E (.chr ch) hav.self p q hp hq
    | .range lo hi, _, hav => fun p hp q hq => compiledAtom_correct c x ds hd E (.range lo hi) hav.self p q hp hq
    | .lit w, _, hav => fun p hp q hq => compiledAtom_correct c x ds hd E (.lit w) hav.self p q hp hq
    | .param k, _, hav => fun p hp q hq => compiledParameter_correct c hAlphabet x ds hd E hv k hav.self p q hp hq
    | .alt a b, he, hav => by
      have ha := compiledSyntax_correct c hAlphabet x ds hd E hv hCall a he.1 hav.alt.1
      have hb := compiledSyntax_correct c hAlphabet x ds hd E hv hCall b he.2 hav.alt.2
      intro p hp q hq
      exact compiledAlt_correct c x ds hd E a b hav.self p q (ha p hp q hq) (hb p hp q hq)
    | .seq a b, he, hav => by
      have ha := compiledSyntax_correct c hAlphabet x ds hd E hv hCall a he.1 hav.seq.1
      have hb := compiledSyntax_correct c hAlphabet x ds hd E hv hCall b he.2 hav.seq.2
      intro p hp q hq
      exact compiledSequence_correct c x ds hd E a b hav p q hp hq (ha p hp) hb
    | .star a, he, hav => by
      have ha := compiledSyntax_correct c hAlphabet x ds hd E hv hCall a he hav.star
      intro p hp q hq
      exact compiledStar_correct c x ds hd E a hav p q hp hq ha
    | .notP a, he, hav => by
      have ha := compiledSyntax_correct c hAlphabet x ds hd E hv hCall a he hav.notP
      intro p hp q hq
      exact compiledNot_correct c x ds hd E a hav.self p q hp hq (ha p hp)
    | .call callee actuals, he, hav => by
      cases hr : ruleAtM c.source.rules callee with
      | none =>
        intro p _ q _
        exact compiledCall_missing c x ds hd E callee actuals hav hr p q
      | some rule =>
        by_cases ha : rule.arity = actuals.length
        · exact hCall callee actuals rule hr ha he hav
            (compiledSyntaxArgs_correct c hAlphabet x ds hd E hv hCall actuals he hav.call.1)
        · intro p _ q _
          exact compiledCall_badArity c x ds hd E callee actuals hav hr ha p q
    | .dbg _, he, _ | .lam _ _, he, _ | .callParam _ _, he, _ | .invoke _ _ _, he, _ => False.elim he
  termination_by structural e _ _ => e

  theorem compiledSyntaxArgs_correct (c : CompilerConfig) (hAlphabet : c.alphabet = unicodeAlphabet)
      (x : List Char) (ds : List Nat) (hd : ds.length = c.digits) (E : CapturedEnv) (hv : ValidEnv x.length E)
      (hCall : CallHandler c x ds E) :
      ∀ es, MExp.FirstOrderArgs es → ArgsAvailable c.nodes E.length es → ∀ a ∈ es, SyntaxCorrect c x ds E a
    | [], _, _, _, hm => False.elim (List.not_mem_nil hm)
    | a :: es, he, hav, b, hm => by
      rcases List.mem_cons.mp hm with heq | hm
      · rw [heq]
        exact compiledSyntax_correct c hAlphabet x ds hd E hv hCall a he.1 hav.cons.1
      · exact compiledSyntaxArgs_correct c hAlphabet x ds hd E hv hCall es he.2 hav.cons.2 b hm
  termination_by structural es _ _ _ _ => es
end

def LookupAll (c : CompilerConfig) (x : List Char) (ds : List Nat) : Prop :=
  ∀ callee (rule : MRule), ruleAtM c.source.rules callee = some rule →
    ∀ E, ValidEnv x.length E → E.length = rule.arity →
      ∀ p, p ≤ x.length → ∀ q, q ≤ x.length → LookupCorrect c x ds E callee p q

theorem callHandler_of_lookup (c : CompilerConfig) (hg : c.source.FirstOrder)
    (x : List Char) (ds : List Nat) (hd : ds.length = c.digits) (E : CapturedEnv)
    (hLookup : LookupAll c x ds) : CallHandler c x ds E := by
  intro callee actuals rule hr ha hfo hav hArg p hp q hq
  have hArgs := compiledArguments_correct c hg x ds hd E callee actuals hr ha hfo hav.call.2 hArg
    (hLookup callee rule hr)
  apply compiledCall_correct c x ds hd E callee actuals hav.self hr ha p q
  exact hArgs 0 [] (by omega) rfl (by intro span hm; cases hm) p hp q hq

/-- Unconditional bounded Seq-to-Par simulation for the actual generator.
The argument stages and table lookups are proved above; no simulation
oracle or call-handler assumption remains in this theorem. -/
theorem compiledEvaluator_correct (c : CompilerConfig) (hAlphabet : c.alphabet = unicodeAlphabet)
    (hg : c.source.FirstOrder) (x : List Char) (ds : List Nat) (hd : ds.length = c.digits)
    (hv : ∀ k ∈ ds, k ≤ x.length) (E : CapturedEnv) (he : ValidEnv x.length E)
    (e : MExp) (hfo : e.FirstOrder) (hav : ExprAvailable c.nodes E.length e) : SyntaxCorrect c x ds E e := by
  have aux : ∀ m ds, clockValue x.length ds = m → ds.length = c.digits → (∀ k ∈ ds, k ≤ x.length) →
      ∀ E, ValidEnv x.length E → ∀ e, e.FirstOrder → ExprAvailable c.nodes E.length e → SyntaxCorrect c x ds E e := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro ds hm hd hv
      have hLookup : LookupAll c x ds := by
        intro callee rule hr E he hlen p hp q hq
        have hIndex : callee < c.source.rules.length := by
          rw [ruleAtM_eq_getElem?] at hr
          exact (List.getElem?_eq_some_iff.mp hr).choose
        have hNode : .lookup callee ∈ c.nodes := compilerNodes_lookup c.source c.start callee hIndex
        apply compiledLookup_correct c x ds hd hv E callee rule hr hNode hlen p q hp
        intro out hout
        have hSpec := predClock_spec x.length ds hv
        rw [hout] at hSpec
        have hSmall : clockValue x.length out < m := by omega
        have hBody : rule.body.FirstOrder := hg rule (by
          rw [ruleAtM_eq_getElem?] at hr
          exact List.mem_of_getElem? hr)
        have hAvailable : ExprAvailable c.nodes E.length rule.body := by
          rw [hlen]
          exact compilerBody_available c.start hr
        exact ih (clockValue x.length out) hSmall out rfl (hSpec.1.trans hd) hSpec.2.1 E he
          rule.body hBody hAvailable p hp q hq
      intro E he e hfo hav
      exact compiledSyntax_correct c hAlphabet x ds hd E he (callHandler_of_lookup c hg x ds hd E hLookup) e hfo hav
  exact aux (clockValue x.length ds) ds rfl hd hv E he e hfo hav

end Shallot.MacroPeg.CBV.ParSimulation
