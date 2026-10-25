import MacroPeg.CBV.WordCallUnfolding
import MacroPeg.CBV.WordViewSubstitution

namespace Shallot.MacroPeg.CBV.WordExpansionRefinement
open ClockFreezing (Table)

theorem antisymm {a b : Res} (hab : RLe a b) (hba : RLe b a) : a=b := by
  rcases hab with ha|hab
  · rw [ha] at hba ⊢
    rcases hba with hb|hb <;> exact hb.symm
  · exact hab

theorem context_eq (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) (E : List (List Char))
    (hT : OkTV x.length T) (A B : MExp) (h : ∀ p, p≤x.length → evV g x s T E A p=evV g x s T E B p)
    (C : ExpressionContext.Context) (p : Nat) (hp : p≤x.length) :
    evV g x s T E (ExpressionContext.plug A C) p=evV g x s T E (ExpressionContext.plug B C) p := by
  apply antisymm
  · exact ExpressionContext.refinement g x s T T E hT (TLeV.refl _) A B
      (fun q hq => Or.inr (h q hq)) C p hp
  · exact ExpressionContext.refinement g x s T T E hT (TLeV.refl _) B A
      (fun q hq => Or.inr (h q hq).symm) C p hp

/-- Refinement of a callee body transports through an actual word-valued
argument expansion. The callee receives a singleton environment, even when
the caller has more retained values. -/
theorem expanded (g : MGrammar) (x : List Char) (T U : Table) (A B C : MExp)
    (hA : WordArguments.Word A) (hB : B.FirstOrder) (hC : C.FirstOrder)
    (h : ∀ w p, p≤x.length → RLe (evV g x .callByValuePar T [w] B p)
      (evV g x .callByValuePar U [w] C p)) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    RLe (evV g x .callByValuePar T E (WordCallUnfolding.expanded A B) p)
      (evV g x .callByValuePar U E (WordCallUnfolding.expanded A C) p) := by
  simp only [WordCallUnfolding.expanded]
  have ht := CallLookahead.evV_peek g x .callByValuePar T E A p
  have hu := CallLookahead.evV_peek g x .callByValuePar U E A p
  rw [WordArguments.word_eval g x .callByValuePar T E A hA p] at ht
  rw [WordArguments.word_eval g x .callByValuePar U E A hA p] at hu
  cases hv : WordArguments.value E A with
  | none =>
    simp [hv,WordArguments.literal,MExp.failAlways,evV,CallLookahead.peek] at ht hu
    rw [evV_seq_fail ht,evV_seq_fail hu]
    exact RLe.refl _
  | some w =>
    cases hs : Shallot.stripPrefix? w (sfx x p) with
    | none =>
      simp [hv,WordArguments.literal,evV,hs,CallLookahead.peek] at ht hu
      rw [evV_seq_fail ht,evV_seq_fail hu]
      exact RLe.refl _
    | some rest =>
      simp [hv,WordArguments.literal,evV,hs,CallLookahead.peek] at ht hu
      rw [evV_seq_ok ht,evV_seq_ok hu,
        WordViewSubstitution.evaluator g x .callByValuePar T E A hA w hv B hB p,
        WordViewSubstitution.evaluator g x .callByValuePar U E A hA w hv C hC p]
      exact h w p hp

end Shallot.MacroPeg.CBV.WordExpansionRefinement
