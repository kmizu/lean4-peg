import MacroPeg.CBV.SequentialTotalControl
import MacroPeg.CBV.SequentialResultZero

namespace Shallot.MacroPeg.CBV.SequentialTotalAtoms
open SequentialTotalSyntax SequentialTotalControl
variable {g h : MGrammar} {x : List Char} {T U : SequentialClock.Table}
  {E : List (List Char)} {p fuel : Nat}

theorem consuming_correct (e : MExp) (r : Res)
    (he : evV h x .callByValueSeq U E e p=r) (defined : r≠none)
    (strict : ∀ q, r=some (some q) → q≠p) :
    Realizes h x U E ⟨MExp.failAlways,e,.notP e⟩ p r := by
  cases r with
  | none => exact False.elim (defined rfl)
  | some v => cases v with
    | none => simp [Realizes,evV,he,MExp.failAlways,zeroResult,positiveResult,failureResult]
    | some q => simp [Realizes,evV,he,MExp.failAlways,zeroResult,positiveResult,failureResult,strict q rfl]

theorem epsilon_correct :
    Realizes h x U E (compile g fuel .eps) p (evV g x .callByValueSeq T E .eps p) := by
  simp [Realizes,compile,evV,MExp.failAlways,zeroResult,positiveResult,failureResult]

theorem any_correct (hp : p≤x.length) :
    Realizes h x U E (compile g fuel .any) p (evV g x .callByValueSeq T E .any p) := by
  cases hs : sfx x p with
  | nil => simp [Realizes,compile,evV,hs,MExp.failAlways,zeroResult,positiveResult,failureResult]
  | cons c rest =>
    have hl := length_sfx x hp
    rw [hs,List.length_cons] at hl
    simp [Realizes,compile,evV,hs,MExp.failAlways,zeroResult,positiveResult,failureResult,show rest.length≠p by omega]

theorem char_correct (c : Char) (hp : p≤x.length) :
    Realizes h x U E (compile g fuel (.chr c)) p (evV g x .callByValueSeq T E (.chr c) p) := by
  cases hs : sfx x p with
  | nil => simp [Realizes,compile,evV,hs,MExp.failAlways,zeroResult,positiveResult,failureResult]
  | cons d rest =>
    have hl := length_sfx x hp
    rw [hs,List.length_cons] at hl
    cases hc : Shallot.beqChar c d <;>
      simp [Realizes,compile,evV,hs,hc,MExp.failAlways,zeroResult,positiveResult,failureResult,show rest.length≠p by omega]

theorem range_correct (a b : Char) (hp : p≤x.length) :
    Realizes h x U E (compile g fuel (.range a b)) p (evV g x .callByValueSeq T E (.range a b) p) := by
  cases hs : sfx x p with
  | nil => simp [Realizes,compile,evV,hs,MExp.failAlways,zeroResult,positiveResult,failureResult]
  | cons d rest =>
    have hl := length_sfx x hp
    rw [hs,List.length_cons] at hl
    cases hc : (Shallot.leChar a d && Shallot.leChar d b) <;>
      simp [Realizes,compile,evV,hs,hc,MExp.failAlways,zeroResult,positiveResult,failureResult,show rest.length≠p by omega]

theorem literal_correct (w : List Char) (hp : p≤x.length) :
    Realizes h x U E (compile g fuel (.lit w)) p (evV g x .callByValueSeq T E (.lit w) p) := by
  by_cases hw : w=[]
  · subst w
    simp [Realizes,compile,evV,Shallot.stripPrefix?,length_sfx x hp,MExp.failAlways,
      zeroResult,positiveResult,failureResult]
  · have hc : compile g fuel (.lit w)=⟨MExp.failAlways,.lit w,.notP (.lit w)⟩ := by simp [compile,hw]
    rw [hc]
    cases hs : Shallot.stripPrefix? w (sfx x p) with
    | none => simp [Realizes,evV,hs,MExp.failAlways,zeroResult,positiveResult,failureResult]
    | some rest =>
      have hl := congrArg List.length ((CBVtoCBN.stripPrefix_exact _ _ _).mp hs)
      rw [length_sfx x hp,List.length_append] at hl
      have hwlen : 0<w.length := by cases w with | nil => exact False.elim (hw rfl) | cons c cs => simp
      simp [Realizes,evV,hs,MExp.failAlways,zeroResult,positiveResult,failureResult,show rest.length≠p by omega]

theorem parameter_correct (i : Nat) (hp : p≤x.length) :
    Realizes h x U E (compile g fuel (.param i)) p (evV g x .callByValueSeq T E (.param i) p) := by
  have he : evV h x .callByValueSeq U E (.param i) p=evV g x .callByValueSeq T E (.param i) p := rfl
  have hz := SequentialResultZero.emptyParameter_eval h x .callByValueSeq U E i p hp
  rw [he] at hz
  have hd : ∃ v, evV g x .callByValueSeq T E (.param i) p=some v := by
    cases hw : E[i]? with
    | none => exact ⟨none,by simp [evV,hw]⟩
    | some w => cases hs : Shallot.stripPrefix? w (sfx x p) with
      | none => exact ⟨none,by simp [evV,hw,hs]⟩
      | some rest => exact ⟨some rest.length,by simp [evV,hw,hs]⟩
  obtain ⟨v,hv⟩ := hd
  rw [hv] at hz
  have he' := he.trans hv
  simp only [Realizes,compile,hv]
  cases v with
  | none =>
    exact ⟨hz,(evV_seq_ok (evV_not_fail hz)).trans he',evV_not_fail he'⟩
  | some q =>
    by_cases hq : q=p
    · simp only [EmptyResultObservation.project,if_pos hq] at hz
      simp only [zeroResult,positiveResult,failureResult,if_pos hq]
      exact ⟨hz,evV_seq_fail (evV_not_ok hz),evV_not_ok he'⟩
    · simp only [EmptyResultObservation.project,if_neg hq] at hz
      simp only [zeroResult,positiveResult,failureResult,if_neg hq]
      exact ⟨hz,(evV_seq_ok (evV_not_fail hz)).trans he',evV_not_ok he'⟩

end Shallot.MacroPeg.CBV.SequentialTotalAtoms
