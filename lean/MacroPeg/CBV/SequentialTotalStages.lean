import MacroPeg.CBV.SequentialLocalCorrectness
import MacroPeg.CBV.SequentialTotalExpression

namespace Shallot.MacroPeg.CBV.SequentialTotalStages
open SequentialLocalCorrectness (canonical clock)
open SequentialLocalClosure (overlay rounds)

def stage (g : MGrammar) (x : List Char) (p j : Nat) : SequentialClock.Table :=
  overlay g x p (canonical g x) (rounds g x p (canonical g x) j)

theorem stage_descending (g : MGrammar) (x : List Char) (p j : Nat) :
    SequentialClock.Descending (stage g x p j) :=
  SequentialLocalClosure.overlay_descending g x p _ (SequentialClock.table_descending g x (clock g x)) _
    (SequentialLocalClosure.rounds_descending g x p _ (SequentialClock.table_descending g x (clock g x)) j)

theorem lower_row (g : MGrammar) (x : List Char) (p j i : Nat) (W : List (List Char))
    (q : Nat) (hp : p≤x.length) (hq : q<p) :
    valAt (stage g x p j i W) q=valAt (canonical g x i W) q :=
  SequentialLocalClosure.overlay_lower g x p _ _ i W q (by omega) hq

theorem lower_expression (g : MGrammar) (x : List Char) (p j : Nat) (E : List (List Char))
    (e : MExp) (q : Nat) (hp : p≤x.length) (hq : q<p) :
    evV g x .callByValueSeq (stage g x p j) E e q=
      evV g x .callByValueSeq (canonical g x) E e q := by
  apply SequentialClock.expression_agree (x:=x) (stage_descending g x p j) _ E e q (Nat.le_refl _)
  intro i r W hr hlen z hz hzero
  exact lower_row g x p j i W z hp (by omega)

theorem full_expression (g : MGrammar) (x : List Char) (p : Nat) (hp : p≤x.length)
    (E : List (List Char)) (e : MExp) :
    evV g x .callByValueSeq (stage g x p g.rules.length) E e p=
      evV g x .callByValueSeq (canonical g x) E e p :=
  SequentialLocalCorrectness.expression_eq_source g x p hp E e

theorem here_row (g : MGrammar) (x : List Char) (p j i : Nat) (r : MRule)
    (hr : ruleAtM g.rules i=some r) (W : List (List Char)) (hp : p≤x.length) :
    valAt (stage g x p j i W) p=rounds g x p (canonical g x) j ⟨i,ruleAtM_lt hr⟩ :=
  SequentialLocalClosure.overlay_here g x p _ _ ⟨i,ruleAtM_lt hr⟩ W hp

theorem source_rule_get (g : MGrammar) (i : Nat) (r : MRule) (hr : ruleAtM g.rules i=some r) :
    g.rules[i]'(ruleAtM_lt hr)=r := by
  have h : g.rules[i]?=some r := by simpa only [ruleAtM_eq_getElem?] using hr
  simpa only [List.getElem?_eq_getElem (ruleAtM_lt hr),Option.some.injEq] using h

theorem next_round (g : MGrammar) (x : List Char) (p j i : Nat) (r : MRule)
    (hr : ruleAtM g.rules i=some r) (he : r.body.FirstOrder) :
    rounds g x p (canonical g x) (j+1) ⟨i,ruleAtM_lt hr⟩=
      evV g x .callByValueSeq (stage g x p j) [] (SequentialResultSyntax.emptyBody r) p := by
  have hi : i<g.rules.length := ruleAtM_lt hr
  change evV g x .callByValueSeq (stage g x p j) (List.replicate g.rules[i].arity []) g.rules[i].body p=_
  rw [source_rule_get g i r hr]
  symm
  simpa only [SequentialResultSyntax.emptyBody,List.map_replicate] using evV_subst
    (g:=g) (x:=x) (s:=.callByValueSeq) (T:=stage g x p j) (E:=[])
    (List.replicate r.arity []) r.body he p

end Shallot.MacroPeg.CBV.SequentialTotalStages
