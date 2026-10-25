import MacroPeg.CBV.EmptyObservedCorrespondence
import MacroPeg.Properties.MExpEq

namespace Shallot.MacroPeg.CBV.EmptyObservedCompiler
open EmptyObservedSyntax
abbrev Term := EmptyObservedSyntax.Expr
abbrev Spec := EmptyObservedSyntax.Rule

def rulesCheck : List MRule → List Spec → Bool
  | [],[] => true
  | r::rules,s::specs => decide (r.arity=s.arity) && MExp.beqE r.body (original s.body) && rulesCheck rules specs
  | _,_ => false

def check (g : MGrammar) (rs : List Spec) := rulesCheck g.rules rs
def rootCheck (root : MExp) (e : Term) := MExp.beqE root (original e)

theorem rules_checked : ∀ rules rs, rulesCheck rules rs=true →
    rules=rs.map (fun r => ({arity := r.arity,body := original r.body} : MRule))
  | [],[],_ => rfl
  | [],_::_,h | _::_,[],h => by cases h
  | r::rules,s::rs,h => by
    obtain ⟨h,hr⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
    have ha := of_decide_eq_true ha
    have hb := (MExp.beqE_iff _ _).mp hb
    have hh : r=⟨s.arity,original s.body⟩ := by cases r; simp_all
    rw [hh,rules_checked rules rs hr]; rfl

theorem checked (g : MGrammar) (rs : List Spec) (hc : check g rs=true) : g=source rs := by
  have hh := rules_checked g.rules rs hc
  cases g
  simp_all [source]

theorem root_checked (root : MExp) (e : Term) (hc : rootCheck root e=true) : root=original e :=
  (MExp.beqE_iff _ _).mp hc

/-- Complete finite checks of the actual source declarations and root. -/
theorem physical (g : MGrammar) (rs : List Spec) (root : MExp) (e : Term)
    (hc : check g rs=true) (he : rootCheck root e=true) (x : List Char) (k : Nat) :
    evV g x .callByValuePar (tblV g x .callByValuePar k) [] root x.length=
      evV (target rs) x .callByValueSeq (tblV (target rs) x .callByValueSeq k) [] (emit rs [] false e) x.length := by
  rw [checked g rs hc,root_checked root e he]
  exact (EmptyObservedCorrespondence.physical rs x e [] x.length k (Nat.le_refl _)).1.symm

theorem observations_iff (g : MGrammar) (rs : List Spec) (root : MExp) (e : Term)
    (hc : check g rs=true) (he : rootCheck root e=true) (x : List Char) (rest : Option (List Char)) :
    SObs g .callByValuePar root x rest ↔ SObs (target rs) .callByValueSeq (emit rs [] false e) x rest := by
  rw [checked g rs hc,root_checked root e he]
  exact EmptyObservedCorrespondence.observations_iff rs e x rest

theorem language_translation (g : MGrammar) (rs : List Spec) (root : MExp) (e : Term)
    (hc : check g rs=true) (he : rootCheck root e=true) :
    (fun x => SObs g .callByValuePar root x (some []))=
      (fun x => SObs (target rs) .callByValueSeq (emit rs [] false e) x (some [])) := by
  funext x
  exact propext (observations_iff g rs root e hc he x (some []))

theorem undefined_iff (g : MGrammar) (rs : List Spec) (root : MExp) (e : Term)
    (hc : check g rs=true) (he : rootCheck root e=true) (x : List Char) :
    (∀ k, evV g x .callByValuePar (tblV g x .callByValuePar k) [] root x.length=none) ↔
      ∀ k, evV (target rs) x .callByValueSeq (tblV (target rs) x .callByValueSeq k) [] (emit rs [] false e) x.length=none := by
  constructor
  · intro h k; exact (physical g rs root e hc he x k).symm.trans (h k)
  · intro h k; exact (physical g rs root e hc he x k).trans (h k)

end Shallot.MacroPeg.CBV.EmptyObservedCompiler
