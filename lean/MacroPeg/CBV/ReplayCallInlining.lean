import MacroPeg.CBV.ForwardedCallUnfolding
import MacroPeg.CBV.ExpressionContext
import MacroPeg.Properties.MExpEq

namespace Shallot.MacroPeg.CBV.ReplayCallInlining
open ExpressionContext (Context plug)
open ClockFreezing (Table)

def body (tail : MExp) : MExp := .seq (.seq (.lit []) (.param 0)) tail

theorem preflight (g : MGrammar) (x : List Char) (T : Table) (E : List (List Char)) (B : MExp)
    (p : Nat) (hp : p≤x.length) :
    evV g x .callByValuePar T E (ForwardedCallUnfolding.unfolded (body B)) p=
      evV g x .callByValuePar T E (body B) p := by
  have he : evV g x .callByValuePar T E (.lit []) p=some (some p) := by
    simp only [evV,Shallot.stripPrefix?,length_sfx x hp]
  have hh := evV_seq_ok (b := .param 0) he
  change (match evV g x .callByValuePar T E (.andP (.param 0)) p with
    | some (some j) => evV g x .callByValuePar T E (body B) j
    | other => other)=_
  rw [CallLookahead.evV_peek]
  cases hv : evV g x .callByValuePar T E (.param 0) p with
  | none =>
    change none=evV g x .callByValuePar T E (body B) p
    exact (evV_seq_none (hh.trans hv)).symm
  | some v => cases v with
    | none =>
      change some none=evV g x .callByValuePar T E (body B) p
      exact (evV_seq_fail (hh.trans hv)).symm
    | some j => rfl

theorem one_step (g : MGrammar) (j : Nat) (B : MExp) (hj : ruleAtM g.rules j=some ⟨1,body B⟩)
    (hB : ForwardedCallUnfolding.unary B=true) (x : List Char) (k : Nat)
    (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x .callByValuePar (tblV g x .callByValuePar (k+1)) E (.call j [.param 0]) p=
      evV g x .callByValuePar (tblV g x .callByValuePar k) E (body B) p :=
  (ForwardedCallUnfolding.one_step g j (body B) hj
    (by simp [body,ForwardedCallUnfolding.unary,hB]) x k E p hp).trans (preflight g x _ E B p hp)

theorem context_bounds (g : MGrammar) (j : Nat) (B : MExp) (hj : ruleAtM g.rules j=some ⟨1,body B⟩)
    (hB : ForwardedCallUnfolding.unary B=true) (C : Context) (x : List Char) (k : Nat)
    (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    RLe (evV g x .callByValuePar (tblV g x .callByValuePar k) E (plug (.call j [.param 0]) C) p)
      (evV g x .callByValuePar (tblV g x .callByValuePar k) E (plug (body B) C) p) ∧
    RLe (evV g x .callByValuePar (tblV g x .callByValuePar k) E (plug (body B) C) p)
      (evV g x .callByValuePar (tblV g x .callByValuePar (k+1)) E (plug (.call j [.param 0]) C) p) := by
  constructor
  · apply ExpressionContext.refinement g x .callByValuePar _ _ E (tblV_ok g x .callByValuePar k)
      (TLeV.refl _) (.call j [.param 0]) (body B) _ C p hp
    intro p hp
    rw [←one_step g j B hj hB x k E p hp]
    exact evV_mono (tblV_step g x .callByValuePar k) _ _
  · apply ExpressionContext.refinement g x .callByValuePar _ _ E (tblV_ok g x .callByValuePar k)
      (tblV_step g x .callByValuePar k) (body B) (.call j [.param 0]) _ C p hp
    intro p hp
    exact Or.inr (one_step g j B hj hB x k E p hp).symm

/-- A finite grammar edit changes the selected caller only. Its callee
may itself recurse, including calls back to the selected caller. -/
def compile (g : MGrammar) (caller : Nat) (B : MExp) (C : Context) : MGrammar :=
  ⟨g.rules.mapIdx (fun i r => if i=caller then ⟨r.arity,plug (body B) C⟩ else r)⟩

def check (g : MGrammar) (caller callee : Nat) (B : MExp) (C : Context) : Bool :=
  match ruleAtM g.rules caller,ruleAtM g.rules callee with
  | some a,some b => ForwardedCallUnfolding.unary B &&
      (decide (b.arity=1 ∧ b.body=body B) && decide (a.body=plug (.call callee [.param 0]) C))
  | _,_ => false

theorem rule (g : MGrammar) (caller : Nat) (B : MExp) (C : Context) (i : Nat) :
    ruleAtM (compile g caller B C).rules i=
      (ruleAtM g.rules i).map (fun r => if i=caller then ⟨r.arity,plug (body B) C⟩ else r) := by
  simp [compile,ruleAtM_eq_getElem?,List.getElem?_mapIdx]

theorem related (g : MGrammar) (caller callee : Nat) (B : MExp) (C : Context)
    (hc : check g caller callee B C=true) :
    BoundedBodyRewrite.Related g (compile g caller B C) .callByValuePar := by
  cases ha : ruleAtM g.rules caller with
  | none => simp [check,ha] at hc
  | some a =>
    cases hb : ruleAtM g.rules callee with
    | none => simp [check,hb] at hc
    | some b =>
      simp only [check,ha,hb] at hc
      have hs := Bool.and_eq_true_iff.mp hc
      have hUnary : ForwardedCallUnfolding.unary B=true := hs.1
      have hbFields : b.arity=1 ∧ b.body=body B := of_decide_eq_true (Bool.and_eq_true_iff.mp hs.2).1
      have hb' : b=⟨1,body B⟩ := by cases b; cases hbFields.1; cases hbFields.2; rfl
      have ha' : a.body=plug (.call callee [.param 0]) C := of_decide_eq_true (Bool.and_eq_true_iff.mp hs.2).2
      subst b
      intro i
      rw [rule]
      cases hi : ruleAtM g.rules i with
      | none => trivial
      | some r =>
        by_cases hic : i=caller
        · subst i
          have he : r=a := Option.some.inj (hi.symm.trans ha)
          subst r
          simp only [Option.map_some]
          refine ⟨rfl,?_⟩
          intro x k E p hp
          rw [ha']
          exact context_bounds g callee B hb hUnary C x k E p hp
        · simp only [Option.map_some,if_neg hic]
          exact ⟨True.intro,fun x k E p _ => ⟨RLe.refl _,evV_mono (tblV_step g x .callByValuePar k) r.body p⟩⟩

end Shallot.MacroPeg.CBV.ReplayCallInlining
