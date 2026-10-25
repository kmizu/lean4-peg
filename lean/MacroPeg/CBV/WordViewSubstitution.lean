import MacroPeg.CBV.WordArguments
import MacroPeg.CBV.ClockFreezing

namespace Shallot.MacroPeg.CBV.WordViewSubstitution
open ClockFreezing (Table)
open WordArguments (Word value word_eval)

mutual
  theorem evaluator (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) (E : List (List Char))
      (A : MExp) (hA : Word A) (w : List Char) (hv : value E A=some w) :
      ∀ B, B.FirstOrder → ∀ p,
        evV g x s T E (MExp.subst [A] B) p=evV g x s T [w] B p
    | .eps,_,_ | .any,_,_ | .chr _,_,_ | .range _ _,_,_ | .lit _,_,_ => rfl
    | .param k,_,p => by
      cases k with
      | zero =>
        simp only [MExp.subst,argAt]
        rw [word_eval g x s T E A hA p,hv]
        rfl
      | succ k => simp [MExp.subst,argAt,MExp.failAlways,evV]
    | .call i args,h,p => by
      cases s <;> simp only [MExp.subst,evV,length_substArgs,
        parallel g x _ T E A hA w hv args h,sequential g x _ T E A hA w hv args h]
    | .seq a b,h,p | .alt a b,h,p => by
      simp only [MExp.subst,evV,evaluator g x s T E A hA w hv a h.1,
        evaluator g x s T E A hA w hv b h.2]
    | .notP a,h,p => by simp only [MExp.subst,evV,evaluator g x s T E A hA w hv a h]
    | .star a,h,p => evStar_congr p (fun q _ => evaluator g x s T E A hA w hv a h q)
    | .dbg _,h,_ | .lam _ _,h,_ | .callParam _ _,h,_ | .invoke _ _ _,h,_ => False.elim h
  termination_by B => sizeOf B
  decreasing_by all_goals simp_wf; all_goals omega

  theorem parallel (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) (E : List (List Char))
      (A : MExp) (hA : Word A) (w : List Char) (hv : value E A=some w) :
      ∀ args, MExp.FirstOrderArgs args → ∀ p,
        evParArgs g x s T E (MExp.substArgs [A] args) p=evParArgs g x s T [w] args p
    | [],_,_ => rfl
    | a::args,h,p => by
      simp only [MExp.substArgs,evParArgs,evaluator g x s T E A hA w hv a h.1,
        parallel g x s T E A hA w hv args h.2]
  termination_by args => sizeOf args
  decreasing_by all_goals simp_wf; all_goals omega

  theorem sequential (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) (E : List (List Char))
      (A : MExp) (hA : Word A) (w : List Char) (hv : value E A=some w) :
      ∀ args, MExp.FirstOrderArgs args → ∀ p,
        evSeqArgs g x s T E (MExp.substArgs [A] args) p=evSeqArgs g x s T [w] args p
    | [],_,_ => rfl
    | a::args,h,p => by
      simp only [MExp.substArgs,evSeqArgs,evaluator g x s T E A hA w hv a h.1,
        sequential g x s T E A hA w hv args h.2]
  termination_by args => sizeOf args
  decreasing_by all_goals simp_wf; all_goals omega
end

end Shallot.MacroPeg.CBV.WordViewSubstitution
