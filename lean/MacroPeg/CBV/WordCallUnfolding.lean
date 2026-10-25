import MacroPeg.CBV.WordArguments
import MacroPeg.CBV.ExpressionContext
import MacroPeg.CBV.CallLookahead

namespace Shallot.MacroPeg.CBV.WordCallUnfolding
open ClockFreezing (Table)
open WordArguments (Word value literal word_eval)

def wordCheck : MExp → Bool
  | .lit _ | .param _ => true
  | .seq a b => wordCheck a && wordCheck b
  | _ => false

theorem word_checked : ∀ a, wordCheck a=true → Word a
  | .lit _,_ | .param _,_ => True.intro
  | .seq a b,h => ⟨word_checked a (Bool.and_eq_true_iff.mp h).1,word_checked b (Bool.and_eq_true_iff.mp h).2⟩
  | .eps,h | .any,h | .chr _,h | .range _ _,h | .call _ _,h | .alt _ _,h | .star _,h | .notP _,h
  | .dbg _,h | .lam _ _,h | .callParam _ _,h | .invoke _ _ _,h => by cases h

/- Substitute the expression producing the fresh word, rather than the
old retained value. The callee's other parameters remain out of range. -/
mutual
  theorem substitution (g : MGrammar) (x : List Char) (T : Table) (E : List (List Char))
      (A : MExp) (hA : Word A) (w : List Char) (hv : value E A=some w) :
      ∀ B, B.FirstOrder → ∀ p,
        evV g x .callByValuePar T E (MExp.subst [A] B) p=evV g x .callByValuePar T [w] B p
    | .eps,_,_ | .any,_,_ | .chr _,_,_ | .range _ _,_,_ | .lit _,_,_ => rfl
    | .param k,_,p => by
      cases k with
      | zero =>
        simp only [MExp.subst,argAt]
        rw [word_eval g x .callByValuePar T E A hA p,hv]
        rfl
      | succ k => simp [MExp.subst,argAt,MExp.failAlways,evV]
    | .call i args,h,p => by
      simp only [MExp.subst,evV,length_substArgs,arguments_substitution g x T E A hA w hv args h]
    | .seq a b,h,p | .alt a b,h,p => by
      simp only [MExp.subst,evV,substitution g x T E A hA w hv a h.1,
        substitution g x T E A hA w hv b h.2]
    | .notP a,h,p => by simp only [MExp.subst,evV,substitution g x T E A hA w hv a h]
    | .star a,h,p => evStar_congr p (fun q _ => substitution g x T E A hA w hv a h q)
    | .dbg _,h,_ | .lam _ _,h,_ | .callParam _ _,h,_ | .invoke _ _ _,h,_ => False.elim h
  termination_by B => sizeOf B
  decreasing_by all_goals simp_wf; all_goals omega

  theorem arguments_substitution (g : MGrammar) (x : List Char) (T : Table) (E : List (List Char))
      (A : MExp) (hA : Word A) (w : List Char) (hv : value E A=some w) :
      ∀ args, MExp.FirstOrderArgs args → ∀ p,
        evParArgs g x .callByValuePar T E (MExp.substArgs [A] args) p=evParArgs g x .callByValuePar T [w] args p
    | [],_,_ => rfl
    | a::args,h,p => by
      simp only [MExp.substArgs,evParArgs,substitution g x T E A hA w hv a h.1,
        arguments_substitution g x T E A hA w hv args h.2]
  termination_by args => sizeOf args
  decreasing_by all_goals simp_wf; all_goals omega
end

def expanded (A B : MExp) : MExp := .seq (.andP A) (MExp.subst [A] B)

theorem one_step (g : MGrammar) (j : Nat) (B : MExp) (hj : ruleAtM g.rules j=some ⟨1,B⟩)
    (hB : B.FirstOrder) (A : MExp) (hA : Word A) (x : List Char) (k : Nat)
    (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x .callByValuePar (tblV g x .callByValuePar (k+1)) E (.call j [A]) p=
      evV g x .callByValuePar (tblV g x .callByValuePar k) E (expanded A B) p := by
  rw [evV_call_par hj rfl (by decide)]
  change (match evParArgs g x .callByValuePar (tblV g x .callByValuePar (k+1)) E [A] p with
    | some (some W) => valAt (tblV g x .callByValuePar (k+1) j W) p
    | some none => some none
    | none => none)=
    (match evV g x .callByValuePar (tblV g x .callByValuePar k) E (.andP A) p with
    | some (some q) => evV g x .callByValuePar (tblV g x .callByValuePar k) E (MExp.subst [A] B) q
    | other => other)
  simp only [evParArgs]
  rw [CallLookahead.evV_peek,
    word_eval g x .callByValuePar (tblV g x .callByValuePar (k+1)) E A hA p,
    word_eval g x .callByValuePar (tblV g x .callByValuePar k) E A hA p]
  cases hv : value E A with
  | none => simp [literal,MExp.failAlways,evV,CallLookahead.peek]
  | some w =>
    cases hs : Shallot.stripPrefix? w (sfx x p) with
    | none => simp [literal,evV,hs,CallLookahead.peek]
    | some y =>
      have hc : pre x p y.length=w := by
        simpa only [length_sfx x hp] using pre_eq (sfx_is_suffix x p) ((CBVtoCBN.stripPrefix_exact _ _ _).mp hs)
      simp only [literal,evV,hs,CallLookahead.peek,hc]
      rw [valAt_tblV_succ hj [w] hp]
      exact (substitution g x _ E A hA w hv B hB p).symm

theorem context_bounds (g : MGrammar) (j : Nat) (B : MExp) (hj : ruleAtM g.rules j=some ⟨1,B⟩)
    (hB : B.FirstOrder) (A : MExp) (hA : Word A) (C : ExpressionContext.Context)
    (x : List Char) (k : Nat) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    RLe (evV g x .callByValuePar (tblV g x .callByValuePar k) E (ExpressionContext.plug (.call j [A]) C) p)
      (evV g x .callByValuePar (tblV g x .callByValuePar k) E (ExpressionContext.plug (expanded A B) C) p) ∧
    RLe (evV g x .callByValuePar (tblV g x .callByValuePar k) E (ExpressionContext.plug (expanded A B) C) p)
      (evV g x .callByValuePar (tblV g x .callByValuePar (k+1)) E (ExpressionContext.plug (.call j [A]) C) p) := by
  constructor
  · apply ExpressionContext.refinement g x .callByValuePar _ _ E (tblV_ok g x .callByValuePar k)
      (TLeV.refl _) (.call j [A]) (expanded A B) _ C p hp
    intro p hp
    rw [←one_step g j B hj hB A hA x k E p hp]
    exact evV_mono (tblV_step g x .callByValuePar k) _ _
  · apply ExpressionContext.refinement g x .callByValuePar _ _ E (tblV_ok g x .callByValuePar k)
      (tblV_step g x .callByValuePar k) (expanded A B) (.call j [A]) _ C p hp
    intro p hp
    exact Or.inr (one_step g j B hj hB A hA x k E p hp).symm

end Shallot.MacroPeg.CBV.WordCallUnfolding
