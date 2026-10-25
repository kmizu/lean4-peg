import MacroPeg.CBV.BoundedBodyRewrite
import MacroPeg.CBV.CallLookahead

namespace Shallot.MacroPeg.CBV.ForwardedCallUnfolding
open ClockFreezing (Table)

mutual
  def unary : MExp → Bool
    | .param k => decide (k=0)
    | .call _ args => unaryArgs args
    | .seq a b | .alt a b => unary a && unary b
    | .notP a | .star a => unary a
    | .eps | .any | .chr _ | .range _ _ | .lit _ => true
    | _ => false
  def unaryArgs : List MExp → Bool
    | [] => true
    | a::args => unary a && unaryArgs args
end

mutual
  theorem environment (g : MGrammar) (x : List Char) (T : Table) (w : List Char) (rest : List (List Char)) :
      ∀ e, unary e=true → ∀ p, evV g x .callByValuePar T (w::rest) e p=evV g x .callByValuePar T [w] e p
    | .param k,h,_ => by
      have hk : k=0 := of_decide_eq_true h
      subst k; rfl
    | .call i args,h,p => by
      simp only [evV,arguments_environment g x T w rest args h p]
    | .seq a b,h,p | .alt a b,h,p => by
      simp only [evV,environment g x T w rest a (Bool.and_eq_true_iff.mp h).1,
        environment g x T w rest b (Bool.and_eq_true_iff.mp h).2]
    | .notP a,h,p => by simp only [evV,environment g x T w rest a h]
    | .star a,h,p => evStar_congr p (fun q _ => environment g x T w rest a h q)
    | .eps,_,_ | .any,_,_ | .chr _,_,_ | .range _ _,_,_ | .lit _,_,_ => rfl
    | .dbg _,h,_ | .lam _ _,h,_ | .callParam _ _,h,_ | .invoke _ _ _,h,_ => by cases h
  termination_by e => sizeOf e
  decreasing_by all_goals simp_wf; all_goals omega

  theorem arguments_environment (g : MGrammar) (x : List Char) (T : Table) (w : List Char) (rest : List (List Char)) :
      ∀ args, unaryArgs args=true → ∀ p,
        evParArgs g x .callByValuePar T (w::rest) args p=evParArgs g x .callByValuePar T [w] args p
    | [],_,_ => rfl
    | a::args,h,p => by
      simp only [evParArgs,environment g x T w rest a (Bool.and_eq_true_iff.mp h).1,
        arguments_environment g x T w rest args (Bool.and_eq_true_iff.mp h).2]
  termination_by args => sizeOf args
  decreasing_by all_goals simp_wf; all_goals omega
end

def unfolded (body : MExp) : MExp := .seq (.andP (.param 0)) body

/-- Actual table unfolding: the source call captures precisely the held
value again. The explicit preflight remains even when the body is independent. -/
theorem one_step (g : MGrammar) (j : Nat) (B : MExp) (hj : ruleAtM g.rules j=some ⟨1,B⟩)
    (hB : unary B=true) (x : List Char) (k : Nat) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x .callByValuePar (tblV g x .callByValuePar (k+1)) E (.call j [.param 0]) p=
      evV g x .callByValuePar (tblV g x .callByValuePar k) E (unfolded B) p := by
  rw [evV_call_par hj rfl (by decide)]
  cases E with
  | nil => simp only [unfolded,MExp.andP,evParArgs,evV,List.getElem?_nil]
  | cons w rest =>
    cases hs : Shallot.stripPrefix? w (sfx x p) with
    | none => simp only [unfolded,MExp.andP,evParArgs,evV,List.getElem?_cons_zero,hs]
    | some y =>
      have hc : pre x p y.length=w := by
        simpa only [length_sfx x hp] using
          pre_eq (sfx_is_suffix x p) ((CBVtoCBN.stripPrefix_exact _ _ _).mp hs)
      simp only [unfolded,MExp.andP,evParArgs,evV,List.getElem?_cons_zero,hs,hc]
      rw [valAt_tblV_succ hj [w] hp]
      exact (environment g x _ w rest B hB p).symm

theorem forward (g : MGrammar) (j : Nat) (B : MExp) (hj : ruleAtM g.rules j=some ⟨1,B⟩)
    (hB : unary B=true) (x : List Char) (k : Nat) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    RLe (evV g x .callByValuePar (tblV g x .callByValuePar k) E (.call j [.param 0]) p)
      (evV g x .callByValuePar (tblV g x .callByValuePar k) E (unfolded B) p) := by
  rw [←one_step g j B hj hB x k E p hp]
  exact evV_mono (tblV_step g x .callByValuePar k) _ _

end Shallot.MacroPeg.CBV.ForwardedCallUnfolding
