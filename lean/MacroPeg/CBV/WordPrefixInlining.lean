import MacroPeg.CBV.WordCallUnfolding
import MacroPeg.CBV.FoldedUserPrefix

namespace Shallot.MacroPeg.CBV.WordPrefixInlining
open ClockFreezing (Table)
open ExpressionContext (Context plug)
open ReplayCallInlining (body)

def argument (V : MExp) : MExp := .seq (.param 0) V
def residual (V B : MExp) : MExp := .seq V (MExp.subst [argument V] B)
def expanded (V B : MExp) : MExp := body (residual V B)

def headed (A B : MExp) : MExp := .seq (.seq (.lit []) A) B

theorem headed_eval (g : MGrammar) (x : List Char) (T : Table) (E : List (List Char)) (A B : MExp)
    (p : Nat) (hp : p≤x.length) :
    evV g x .callByValuePar T E (headed A B) p=evV g x .callByValuePar T E (.seq A B) p := by
  have he : evV g x .callByValuePar T E (.lit []) p=some (some p) := by
    simp only [evV,Shallot.stripPrefix?,length_sfx x hp]
  exact congrArg (fun result => match result with
    | some (some j) => evV g x .callByValuePar T E B j | other => other) (evV_seq_ok (b := A) he)

theorem preflight (g : MGrammar) (x : List Char) (T : Table) (E : List (List Char)) (A B : MExp)
    (p : Nat) (hp : p≤x.length) :
    evV g x .callByValuePar T E (.seq (.andP A) (headed A B)) p=
      evV g x .callByValuePar T E (headed A B) p := by
  have he : evV g x .callByValuePar T E (.lit []) p=some (some p) := by
    simp only [evV,Shallot.stripPrefix?,length_sfx x hp]
  have hh := evV_seq_ok (b := A) he
  change (match evV g x .callByValuePar T E (.andP A) p with
    | some (some j) => evV g x .callByValuePar T E (headed A B) j | other => other)=_
  rw [CallLookahead.evV_peek]
  cases hv : evV g x .callByValuePar T E A p with
  | none => exact (evV_seq_none (hh.trans hv)).symm
  | some v => cases v with
    | none => exact (evV_seq_fail (hh.trans hv)).symm
    | some j => rfl

theorem expanded_eval (g : MGrammar) (x : List Char) (T : Table) (E : List (List Char)) (V B : MExp)
    (p : Nat) (hp : p≤x.length) :
    evV g x .callByValuePar T E (WordCallUnfolding.expanded (argument V) (body B)) p=
      evV g x .callByValuePar T E (expanded V B) p := by
  change evV g x .callByValuePar T E
    (.seq (.andP (argument V)) (headed (argument V) (MExp.subst [argument V] B))) p=_
  rw [preflight g x T E _ _ p hp,headed_eval g x T E _ _ p hp]
  exact (LeadingReplayStar.sequence_assoc g x .callByValuePar T E (.param 0) V (MExp.subst [argument V] B) p).trans
    (headed_eval g x T E (.param 0) (residual V B) p hp).symm

/-- R receives a fresh word beginning with the parent's old capture. Its
tail is substituted with the whole new argument, while the parent retains
its original value for later replays. -/
theorem one_step (g : MGrammar) (j : Nat) (B : MExp) (hj : ruleAtM g.rules j=some ⟨1,body B⟩)
    (hB : B.FirstOrder) (V : MExp) (hV : WordArguments.Word V) (x : List Char) (k : Nat)
    (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x .callByValuePar (tblV g x .callByValuePar (k+1)) E (.call j [argument V]) p=
      evV g x .callByValuePar (tblV g x .callByValuePar k) E (expanded V B) p :=
  (WordCallUnfolding.one_step g j (body B) hj ⟨⟨True.intro,True.intro⟩,hB⟩ (argument V)
    ⟨True.intro,hV⟩ x k E p hp).trans (expanded_eval g x _ E V B p hp)

theorem context_bounds (g : MGrammar) (j : Nat) (B : MExp) (hj : ruleAtM g.rules j=some ⟨1,body B⟩)
    (hB : B.FirstOrder) (V : MExp) (hV : WordArguments.Word V) (C : Context)
    (x : List Char) (k : Nat) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    RLe (evV g x .callByValuePar (tblV g x .callByValuePar k) E (plug (.call j [argument V]) C) p)
      (evV g x .callByValuePar (tblV g x .callByValuePar k) E (plug (expanded V B) C) p) ∧
    RLe (evV g x .callByValuePar (tblV g x .callByValuePar k) E (plug (expanded V B) C) p)
      (evV g x .callByValuePar (tblV g x .callByValuePar (k+1)) E (plug (.call j [argument V]) C) p) := by
  constructor
  · apply ExpressionContext.refinement g x .callByValuePar _ _ E (tblV_ok g x .callByValuePar k)
      (TLeV.refl _) (.call j [argument V]) (expanded V B) _ C p hp
    intro p hp
    rw [←one_step g j B hj hB V hV x k E p hp]
    exact evV_mono (tblV_step g x .callByValuePar k) _ _
  · apply ExpressionContext.refinement g x .callByValuePar _ _ E (tblV_ok g x .callByValuePar k)
      (tblV_step g x .callByValuePar k) (expanded V B) (.call j [argument V]) _ C p hp
    intro p hp
    exact Or.inr (one_step g j B hj hB V hV x k E p hp).symm

end Shallot.MacroPeg.CBV.WordPrefixInlining
