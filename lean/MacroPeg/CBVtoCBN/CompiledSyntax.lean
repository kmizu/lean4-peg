import MacroPeg.CBVtoCBN.CompiledCalls

namespace Shallot.MacroPeg.CBVtoCBN

def SyntaxCorrect (c : CompilerConfig) (x : List Char) (ds : List Nat) (E : CapturedEnv) (e : MExp) : Prop :=
  ∀ p, p ≤ x.length → ∀ q, q ≤ x.length → ExprCorrect c x ds E e p q

/-- The remaining call proof receives correctness of all proper argument subexpressions.
It must establish the real generated call, rather than assuming correctness of the surrounding syntax. -/
def CallHandler (c : CompilerConfig) (x : List Char) (ds : List Nat) (E : CapturedEnv) : Prop :=
  ∀ callee actuals (rule : MRule), ruleAtM c.source.rules callee = some rule → rule.arity = actuals.length →
    MExp.FirstOrderArgs actuals → ExprAvailable c.nodes E.length (.call callee actuals) →
    (∀ a ∈ actuals, SyntaxCorrect c x ds E a) → SyntaxCorrect c x ds E (.call callee actuals)

mutual
  /-- All first-order expression constructors are proved for the actual generator.
The call handler is the sole remaining constructor obligation and receives only smaller-expression hypotheses. -/
  theorem compiledSyntax_correct (c : CompilerConfig) (halpha : c.alphabet = unicodeAlphabet)
      (x : List Char) (ds : List Nat) (hd : ds.length = c.digits) (E : CapturedEnv) (hv : ValidEnv x.length E)
      (hcall : CallHandler c x ds E) :
      ∀ e, e.FirstOrder → ExprAvailable c.nodes E.length e → SyntaxCorrect c x ds E e
    | .eps, _, hav => fun p hp q _ => compiledAtom_correct c x ds hd E .eps hav.self p q hp
    | .any, _, hav => fun p hp q _ => compiledAtom_correct c x ds hd E .any hav.self p q hp
    | .chr ch, _, hav => fun p hp q _ => compiledAtom_correct c x ds hd E (.chr ch) hav.self p q hp
    | .range lo hi, _, hav => fun p hp q _ => compiledAtom_correct c x ds hd E (.range lo hi) hav.self p q hp
    | .lit w, _, hav => fun p hp q _ => compiledAtom_correct c x ds hd E (.lit w) hav.self p q hp
    | .param k, _, hav => fun p hp q hq => compiledParameter_correct c halpha x ds hd E hv k hav.self p q hp hq
    | .alt a b, he, hav => by
      have ha := compiledSyntax_correct c halpha x ds hd E hv hcall a he.1 hav.alt.1
      have hb := compiledSyntax_correct c halpha x ds hd E hv hcall b he.2 hav.alt.2
      intro p hp q hq
      exact compiledAlt_correct c x ds hd E a b hav.self p q (ha p hp q hq) (hb p hp q hq)
    | .seq a b, he, hav => by
      have ha := compiledSyntax_correct c halpha x ds hd E hv hcall a he.1 hav.seq.1
      have hb := compiledSyntax_correct c halpha x ds hd E hv hcall b he.2 hav.seq.2
      intro p hp q hq
      exact compiledSequence_correct c x ds hd E a b hav p q hp (ha p hp)
        (fun j hj => hb j hj q hq) (fun j hj => hb j hj 0 (by omega))
    | .star a, he, hav => by
      have ha := compiledSyntax_correct c halpha x ds hd E hv hcall a he hav.star
      intro p hp q hq
      exact compiledStar_correct c x ds hd E a hav ha p q hp hq
    | .notP a, he, hav => by
      have ha := compiledSyntax_correct c halpha x ds hd E hv hcall a he hav.notP
      intro p hp q hq
      exact compiledNot_correct c x ds hd E a hav p q hp hq (ha p hp)
    | .call callee actuals, he, hav => by
      cases hr : ruleAtM c.source.rules callee with
      | none =>
        intro p _ q _
        exact compiledCall_missing c x ds hd E callee actuals hav.self hr p q
      | some rule =>
        by_cases harity : rule.arity = actuals.length
        · exact hcall callee actuals rule hr harity he hav
            (compiledSyntaxArgs_correct c halpha x ds hd E hv hcall actuals he hav.call.1)
        · intro p _ q _
          exact compiledCall_badArity c x ds hd E callee actuals hav.self hr harity p q
    | .dbg _, he, _ | .lam _ _, he, _ | .callParam _ _, he, _ | .invoke _ _ _, he, _ => False.elim he

  termination_by structural e _ _ => e

  theorem compiledSyntaxArgs_correct (c : CompilerConfig) (halpha : c.alphabet = unicodeAlphabet)
      (x : List Char) (ds : List Nat) (hd : ds.length = c.digits) (E : CapturedEnv) (hv : ValidEnv x.length E)
      (hcall : CallHandler c x ds E) :
      ∀ es, MExp.FirstOrderArgs es → ArgsAvailable c.nodes E.length es → ∀ a ∈ es, SyntaxCorrect c x ds E a
    | [], _, _, _, hm => False.elim (List.not_mem_nil hm)
    | a :: es, he, hav, b, hm => by
      rcases List.mem_cons.mp hm with heq | hm
      · rw [heq]
        exact compiledSyntax_correct c halpha x ds hd E hv hcall a he.1 hav.cons.1
      · exact compiledSyntaxArgs_correct c halpha x ds hd E hv hcall es he.2 hav.cons.2 b hm
  termination_by structural es _ _ _ _ => es
end

end Shallot.MacroPeg.CBVtoCBN
