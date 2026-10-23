import MacroPeg.CBVtoCBN.CompiledArguments

namespace Shallot.MacroPeg.CBVtoCBN

/-- Correctness of every valid source table lookup at one fixed clock value. -/
def LookupAll (c : CompilerConfig) (x : List Char) (ds : List Nat) : Prop :=
  ∀ callee (rule : MRule), ruleAtM c.source.rules callee = some rule →
    ∀ E, ValidEnv x.length E → E.length = rule.arity →
      ∀ p, p ≤ x.length → ∀ q, q ≤ x.length → LookupCorrect c x ds E callee p q

/-- The argument-stage proof discharges the actual call constructor from a correct table oracle. -/
theorem callHandler_of_lookup (c : CompilerConfig) (hg : c.source.FirstOrder) (hs : c.strategy ≠ .callByName)
    (x : List Char) (ds : List Nat) (hd : ds.length = c.digits) (E : CapturedEnv)
    (hl : LookupAll c x ds) : CallHandler c x ds E := by
  intro callee actuals rule hr ha hfo hav harg p hp q hq
  have hargs := compiledArguments_correct c hg hs x ds hd E callee actuals hr ha hfo hav.call.2 harg
    (hl callee rule hr)
  apply compiledCall_correct c x ds hd E callee actuals hav.self hr ha p q
  exact hargs 0 [] (by omega) rfl (by intro span hm; cases hm) p hp q hq

/-- Unconditional bounded simulation for the actual generated first-order CBN grammar.
Clock induction supplies the table oracle, while syntax induction supplies the proper argument predicates. -/
theorem compiledEvaluator_correct (c : CompilerConfig) (halpha : c.alphabet = unicodeAlphabet)
    (hg : c.source.FirstOrder) (hs : c.strategy ≠ .callByName) (x : List Char)
    (ds : List Nat) (hd : ds.length = c.digits) (hv : ∀ k ∈ ds, k ≤ x.length)
    (E : CapturedEnv) (he : ValidEnv x.length E) (e : MExp) (hfo : e.FirstOrder)
    (hav : ExprAvailable c.nodes E.length e) : SyntaxCorrect c x ds E e := by
  have aux : ∀ m ds, clockValue x.length ds = m → ds.length = c.digits → (∀ k ∈ ds, k ≤ x.length) →
      ∀ E, ValidEnv x.length E → ∀ e, e.FirstOrder → ExprAvailable c.nodes E.length e → SyntaxCorrect c x ds E e := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro ds hm hd hv
      have hlookup : LookupAll c x ds := by
        intro callee rule hr E he hlen p hp q hq
        apply compiledLookup_correct c x ds hd hv E callee hr hlen p q hp
        intro out hout
        have hspec := predClock_spec x.length ds hv
        rw [hout] at hspec
        have hsmall : clockValue x.length out < m := by omega
        have hbody : rule.body.FirstOrder := hg rule (by
          rw [ruleAtM_eq_getElem?] at hr
          exact List.mem_of_getElem? hr)
        have havail : ExprAvailable c.nodes E.length rule.body := by
          rw [hlen]
          exact compilerBody_available c.start hr
        exact ih (clockValue x.length out) hsmall out rfl (hspec.1.trans hd) hspec.2.1 E he
          rule.body hbody havail p hp q hq
      intro E he e hfo hav
      exact compiledSyntax_correct c halpha x ds hd E he (callHandler_of_lookup c hg hs x ds hd E hlookup) e hfo hav
  exact aux (clockValue x.length ds) ds rfl hd hv E he e hfo hav

end Shallot.MacroPeg.CBVtoCBN
