import MacroPeg.CBV.DependentProfileCall

namespace Shallot.MacroPeg.CBV.IndependentCaptureControl
open ClockFreezing (Table)
open RegularCaptureProduct (Machine)
abbrev Arg := DependentCaptureFilter.Expr
abbrev NoHelpers (a : Arg) := DependentCaptureFilter.Valid [] a

def check : Arg → Bool
  | .helper _ => false
  | .seq a b | .alt a b => check a && check b
  | .notP a | .star a => check a
  | .lit _ | .param _ => true

theorem check_sound : ∀ a, check a=true → NoHelpers a
  | .helper _, h => by cases h
  | .lit _, _ | .param _, _ => True.intro
  | .seq a b, h | .alt a b, h =>
    ⟨check_sound a (Bool.and_eq_true_iff.mp h).1,check_sound b (Bool.and_eq_true_iff.mp h).2⟩
  | .notP a, h | .star a, h => check_sound a h

/-- Parameter-bearing, call-free control is independent of the surrounding
grammar, strategy and table. Both complete partial results are preserved. -/
theorem eval_eq (g h : MGrammar) (x : List Char) (s t : Strategy) (T U : Table)
    (hT : OkTV x.length T) (E : List (List Char)) (e : MExp)
    (he : ParametricHelperControl.Safe 0 e) (p : Nat) (hp : p≤x.length) :
    evV g x s T E e p=evV h x t U E e p := by
  have hFO := FilteredOverlapCaller.tail_firstOrder 0 e he
  rw [←evV_subst E e hFO,←evV_subst E e hFO]
  have hi (g : MGrammar) : RecursiveParserStability.Installed [] g := by
    intro i e hi; cases i <;> cases hi
  exact RecursiveParserStability.lexical_eval (hi g) (hi h) x s t T U hT
    (fun i hi => by cases hi) [] [] _ (ParametricHelperControl.subst_lexical 0 E e he) p hp

theorem render_safe (D : Machine) (a : Arg) (ha : NoHelpers a) :
    ParametricHelperControl.Safe 0 (DependentCaptureFilter.render a) := by
  simpa [RegularCaptureProduct.grammar] using ParametricHelperControl.render_safe [] D a ha

theorem filter_safe (D : Machine) (hD : 0<D.width) (S : List (List Nat))
    (a : Arg) (ha : NoHelpers a) (q r : Nat) (hq : q<D.width) (hr : r<D.width) :
    ParametricHelperControl.Safe 0 (DependentCaptureFilter.filter [] D S a q r) := by
  simpa [RegularCaptureProduct.grammar] using ParametricHelperControl.filter_safe [] D hD S a ha q r hq hr

theorem filter_correct (D : Machine) (hD : D.Valid) (g h : MGrammar) (x : List Char)
    (T U : Table) (hT : OkTV x.length T) (hU : OkTV x.length U)
    (S : List (List Nat)) (E : List (List Char)) (hS : DependentCaptureFilter.Accurate D S E)
    (a : Arg) (ha : NoHelpers a) (p : Nat) (hp : p≤x.length)
    (q r : Nat) (hq : q<D.width) (hr : r<D.width) :
    evV h x .callByValueSeq U E (DependentCaptureFilter.filter [] D S a q r) p =
      RegularCaptureProduct.filtered D x q r p (evV g x .callByValuePar T E (DependentCaptureFilter.render a) p) := by
  rw [eval_eq h (RegularCaptureProduct.grammar [] D) x .callByValueSeq .callByValueSeq U
      (DependentCaptureFilter.table [] D x) hU E _ (filter_safe D hD.1 S a ha q r hq hr) p hp,
    eval_eq g (RegularCaptureProduct.grammar [] D) x .callByValuePar .callByValueSeq T
      (DependentCaptureFilter.table [] D x) hT E _ (render_safe D a ha) p hp]
  exact DependentCaptureFilter.correct [] (by intro e he; cases he) D hD x S E hS a ha p hp q r hq hr

end Shallot.MacroPeg.CBV.IndependentCaptureControl
