import MacroPeg.CBV.ParametricHelperControl

namespace Shallot.MacroPeg.CBV.FrozenCaptureControl
open ClockFreezing (Table)
open RecursiveParserStability (Installed)
open ParametricHelperControl (Safe)

/-- Widening the installed helper prefix changes no expression syntax. -/
theorem safe_mono {m n : Nat} (hmn : m≤n) : ∀ e, Safe m e → Safe n e
  | .call _ [], h => Nat.lt_of_lt_of_le h hmn
  | .seq a b, h | .alt a b, h => ⟨safe_mono hmn a h.1,safe_mono hmn b h.2⟩
  | .star a, h | .notP a, h => safe_mono hmn a h
  | .eps, h | .lit _, h | .param _, h | .chr _, h | .any, h | .range _ _, h => h
  | .call _ (_::_), h | .dbg _, h | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => False.elim h

/-- Frozen helper-only expressions, including retained parameters, equal
actual canonical evaluation. Arbitrary appended user rules remain active. -/
theorem canonical_eval {bodies : List MExp} (hb : RecursiveParserStability.Valid bodies)
    {g : MGrammar} (hg : Installed bodies g) (x : List Char) (s : Strategy)
    (k : Nat) (E : List (List Char)) (e : MExp) (he : Safe bodies.length e)
    (p : Nat) (hp : p≤x.length) :
    evV g x s (RecursiveParserStability.frozen bodies g x s k) E e p =
      evV g x s (tblV g x s (iterBoundV g x)) E e p := by
  have hFO := FilteredOverlapCaller.tail_firstOrder bodies.length e he
  rw [←evV_subst E e hFO,←evV_subst E e hFO]
  apply RecursiveParserStability.lexical_eval hg hg x s s _ _
    (ClockFreezing.frozen_ok _ _ _ _ _ _) _ [] [] _
    (ParametricHelperControl.subst_lexical bodies.length E e he) p hp
  intro i hi q hq
  have hPick : RecursiveParserStability.pick bodies i=true := by
    simp [RecursiveParserStability.pick,hi]
  rw [ClockFreezing.frozen_rows g x s _ _ k i hPick []]
  rw [RecursiveParserStability.helper_rows_eq hb hg (RecursiveParserStability.installed bodies)
    x s s (RecursiveParserStability.floor bodies x) i hi [] []]
  have hn := List.getElem?_eq_getElem hi
  have hc := agreeV_from
    (RegularCaptureProduct.bound_fixed (RecursiveParserStability.grammar bodies) x s) 1
    i ⟨0,bodies[i]⟩ [] (RecursiveParserStability.installed bodies i bodies[i] hn)
    (by simp [words]) q hq
  rw [show RecursiveParserStability.floor bodies x=
    iterBoundV (RecursiveParserStability.grammar bodies) x+1 from rfl,←hc]
  exact RegularCaptureProduct.canonical_helpers_eq hb (RecursiveParserStability.installed bodies) hg
    x s s i q hi hq

/-- A product parser can be a proper prefix of the frozen component, for
example when residual scanners follow it. No filter row is supplied as advice. -/
theorem base_eval {bodies : List MExp} (hb : RecursiveParserStability.Valid bodies)
    (nodes : List RegularCaptureProduct.Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (D : RegularCaptureProduct.Machine) (hD : 0<D.width)
    {g : MGrammar} (hg : Installed bodies g)
    (hProduct : Installed (RegularCaptureProduct.component nodes D) g)
    (hSize : (RegularCaptureProduct.grammar nodes D).rules.length≤bodies.length)
    (x : List Char) (s : Strategy) (k : Nat) (E : List (List Char))
    (e : MExp) (he : Safe (RegularCaptureProduct.grammar nodes D).rules.length e)
    (p : Nat) (hp : p≤x.length) :
    evV g x s (RecursiveParserStability.frozen bodies g x s k) E e p =
      evV (RegularCaptureProduct.grammar nodes D) x .callByValueSeq
        (DependentCaptureFilter.table nodes D x) E e p := by
  rw [canonical_eval hb hg x s k E e (safe_mono hSize e he) p hp]
  apply ParametricHelperControl.canonical_eval
    (RegularCaptureProduct.component_valid nodes hNodes D hD) hProduct
    (show Installed (RegularCaptureProduct.component nodes D) (RegularCaptureProduct.grammar nodes D) from
      by simpa using RegularCaptureProduct.component_installed nodes D [])
    x s .callByValueSeq E e _ p hp
  simpa [RegularCaptureProduct.component] using he

/-- Complete inline filtering survives arbitrary frozen user stages and
independent recursive helper captures in both real grammars. -/
theorem filter_correct {bodies : List MExp} (hb : RecursiveParserStability.Valid bodies)
    (nodes : List RegularCaptureProduct.Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (D : RegularCaptureProduct.Machine) (hD : D.Valid)
    {g h : MGrammar} (hg : Installed bodies g) (hh : Installed bodies h)
    (hgProduct : Installed (RegularCaptureProduct.component nodes D) g)
    (hhProduct : Installed (RegularCaptureProduct.component nodes D) h)
    (hSize : (RegularCaptureProduct.grammar nodes D).rules.length≤bodies.length)
    (x : List Char) (k l : Nat) (S : List (List Nat)) (E : List (List Char))
    (hS : DependentCaptureFilter.Accurate D S E)
    (a : DependentCaptureFilter.Expr) (ha : DependentCaptureFilter.Valid nodes a)
    (p : Nat) (hp : p≤x.length) (q r : Nat) (hq : q<D.width) (hr : r<D.width) :
    evV h x .callByValueSeq (RecursiveParserStability.frozen bodies h x .callByValueSeq l)
        E (DependentCaptureFilter.filter nodes D S a q r) p =
      RegularCaptureProduct.filtered D x q r p
        (evV g x .callByValuePar (RecursiveParserStability.frozen bodies g x .callByValuePar k)
          E (DependentCaptureFilter.render a) p) := by
  rw [base_eval hb nodes hNodes D hD.1 hh hhProduct hSize x .callByValueSeq l E _
      (ParametricHelperControl.filter_safe nodes D hD.1 S a ha q r hq hr) p hp,
    base_eval hb nodes hNodes D hD.1 hg hgProduct hSize x .callByValuePar k E _
      (ParametricHelperControl.render_safe nodes D a ha) p hp]
  exact DependentCaptureFilter.correct nodes hNodes D hD x S E hS a ha p hp q r hq hr

end Shallot.MacroPeg.CBV.FrozenCaptureControl
