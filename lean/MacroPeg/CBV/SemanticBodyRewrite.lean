import MacroPeg.CBV.ScannerPairFusion
import MacroPeg.CBV.ClockFreezing

namespace Shallot.MacroPeg.CBV.SemanticBodyRewrite
open ClockFreezing (Table)

/-- Evaluation with a fixed table inspects rule existence and arities,
while recursive rule bodies are evaluated by the table iteration. -/
def ArityEq (g h : MGrammar) : Prop :=
  ∀ i, (ruleAtM g.rules i).map MRule.arity=(ruleAtM h.rules i).map MRule.arity

mutual
  theorem evaluator (g h : MGrammar) (ha : ArityEq g h) (x : List Char)
      (s : Strategy) (T : Table) (E : List (List Char)) :
      ∀ e p, evV g x s T E e p=evV h x s T E e p
    | .call i args,p => by
      have hi := ha i
      cases hg : ruleAtM g.rules i with
      | none =>
        cases hh : ruleAtM h.rules i with
        | none => simp only [evV,hg,hh]
        | some b => simp [hg,hh] at hi
      | some a =>
        cases hh : ruleAtM h.rules i with
        | none => simp [hg,hh] at hi
        | some b =>
          have hab : a.arity=b.arity := by simpa [hg,hh] using hi
          cases s <;> simp only [evV,hg,hh,hab,parallel g h ha x _ T E args p,sequential g h ha x _ T E args p]
    | .seq a b,p | .alt a b,p => by
      simp only [evV,evaluator g h ha x s T E a,evaluator g h ha x s T E b]
    | .notP a,p => by simp only [evV,evaluator g h ha x s T E a]
    | .star a,p => evStar_congr p (fun q _ => evaluator g h ha x s T E a q)
    | .eps,_ | .any,_ | .chr _,_ | .range _ _,_ | .lit _,_ | .param _,_
    | .dbg _,_ | .lam _ _,_ | .callParam _ _,_ | .invoke _ _ _,_ => rfl
  termination_by e => sizeOf e
  decreasing_by all_goals simp_wf; all_goals omega

  theorem parallel (g h : MGrammar) (ha : ArityEq g h) (x : List Char)
      (s : Strategy) (T : Table) (E : List (List Char)) :
      ∀ args p, evParArgs g x s T E args p=evParArgs h x s T E args p
    | [],_ => rfl
    | a::args,p => by
      simp only [evParArgs,evaluator g h ha x s T E a,parallel g h ha x s T E args]
  termination_by args => sizeOf args
  decreasing_by all_goals simp_wf; all_goals omega

  theorem sequential (g h : MGrammar) (ha : ArityEq g h) (x : List Char)
      (s : Strategy) (T : Table) (E : List (List Char)) :
      ∀ args p, evSeqArgs g x s T E args p=evSeqArgs h x s T E args p
    | [],_ => rfl
    | a::args,p => by
      simp only [evSeqArgs,evaluator g h ha x s T E a,sequential g h ha x s T E args]
  termination_by args => sizeOf args
  decreasing_by all_goals simp_wf; all_goals omega
end

/-- Rulewise partial evaluation equality under arbitrary tables. Concrete
syntax normalization supplies this relation, rather than taking it as a
certificate for the final grammar translation. -/
def Related (g h : MGrammar) (s : Strategy) : Prop := ∀ i,
  match ruleAtM g.rules i,ruleAtM h.rules i with
  | none,none => True
  | some a,some b => a.arity=b.arity ∧ ∀ x T E p, p≤x.length →
      evV g x s T E a.body p=evV g x s T E b.body p
  | _,_ => False

theorem arities {g h : MGrammar} {s : Strategy} (hr : Related g h s) : ArityEq g h := by
  intro i
  have hi := hr i
  cases hg : ruleAtM g.rules i with
  | none =>
    cases hh : ruleAtM h.rules i with
    | none => rfl
    | some b => simp [hg,hh] at hi
  | some a =>
    cases hh : ruleAtM h.rules i with
    | none => simp [hg,hh] at hi
    | some b =>
      simp only [hg,hh] at hi
      exact congrArg some hi.1

theorem tables {g h : MGrammar} {s : Strategy} (hr : Related g h s)
    (x : List Char) (k : Nat) : tblV g x s k=tblV h x s k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext i E
    have hi := hr i
    cases hg : ruleAtM g.rules i with
    | none =>
      cases hh : ruleAtM h.rules i with
      | none => simp [tblV,hg,hh]
      | some b => simp [hg,hh] at hi
    | some a =>
      cases hh : ruleAtM h.rules i with
      | none => simp [hg,hh] at hi
      | some b =>
        simp only [hg,hh] at hi
        have hb : ∀ x T E p, p≤x.length → evV g x s T E a.body p=evV g x s T E b.body p := by
          exact hi.2
        simp only [tblV,hg,hh,ih]
        apply List.map_congr_left
        intro p hp
        have hp' : p≤x.length := by have := List.mem_range.mp hp; omega
        exact (hb x (tblV h x s k) E p hp').trans
          (evaluator g h (arities hr) x s (tblV h x s k) E _ p)

theorem physical {g h : MGrammar} {s : Strategy} (hr : Related g h s)
    (x : List Char) (k : Nat) (E : List (List Char)) (e : MExp) (p : Nat) :
    evV g x s (tblV g x s k) E e p=evV h x s (tblV h x s k) E e p := by
  rw [tables hr x k]
  exact evaluator g h (arities hr) x s _ E e p

theorem observations {g h : MGrammar} {s : Strategy} (hr : Related g h s)
    (hg : g.FirstOrder) (hh : h.FirstOrder) (hs : s≠.callByName)
    (e : MExp) (he : e.FirstOrder) (x : List Char) (rest : Option (List Char)) :
    SObs g s e x rest ↔ SObs h s e x rest := by
  rw [←decideObsV_iff hg hs he,←decideObsV_iff hh hs he]
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq g h x s s e e
    (fun k => physical hr x k [] e x.length)]

end Shallot.MacroPeg.CBV.SemanticBodyRewrite
