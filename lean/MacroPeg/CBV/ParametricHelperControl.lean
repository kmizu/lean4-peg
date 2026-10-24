import MacroPeg.CBV.DependentCaptureFilter

/-! Retained-parameter control over an independent zero-arity component can
be transported between real caller grammars and seeded user stages. -/
namespace Shallot.MacroPeg.CBV.ParametricHelperControl
open ClockFreezing (Table)
open RecursiveParserStability (Lexical Installed)
abbrev Safe := FilteredOverlapCaller.Tail

theorem subst_lexical (n : Nat) (E : List (List Char)) :
    ∀ e, Safe n e → Lexical n (MExp.subst (E.map MExp.lit) e)
  | .call i [], hi => hi
  | .seq a b, he | .alt a b, he => ⟨subst_lexical n E a he.1,subst_lexical n E b he.2⟩
  | .star a, he | .notP a, he => subst_lexical n E a he
  | .param k, _ => by
    simp only [MExp.subst,argAt_map_lit]
    cases E[k]? <;> trivial
  | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ => True.intro
  | .call _ (_::_), he | .dbg _, he | .lam _ _, he | .callParam _ _, he | .invoke _ _ _, he => False.elim he

/-- Closing parameters by literals preserves helper-only control. This lets
the physical component correspondence apply without discarding retained values. -/
theorem canonical_eval {bodies : List MExp} (hb : RecursiveParserStability.Valid bodies)
    {g h : MGrammar} (hg : Installed bodies g) (hh : Installed bodies h)
    (x : List Char) (s t : Strategy) (E : List (List Char)) (e : MExp)
    (he : Safe bodies.length e) (p : Nat) (hp : p≤x.length) :
    evV g x s (tblV g x s (iterBoundV g x)) E e p =
      evV h x t (tblV h x t (iterBoundV h x)) E e p := by
  have hFO := FilteredOverlapCaller.tail_firstOrder bodies.length e he
  rw [←evV_subst E e hFO,←evV_subst E e hFO]
  exact RecursiveParserStability.lexical_eval hg hh x s t _ _ (tblV_ok _ _ _ _)
    (fun i hi q hq => RegularCaptureProduct.canonical_helpers_eq hb hg hh x s t i q hi hq)
    [] [] _ (subst_lexical bodies.length E e he) p hp

theorem rounds_eval {bodies : List MExp} (hb : RecursiveParserStability.Valid bodies)
    {g : MGrammar} (hg : Installed bodies g) (x : List Char) (s : Strategy)
    (k : Nat) (E : List (List Char)) (e : MExp) (he : Safe bodies.length e)
    (p : Nat) (hp : p≤x.length) :
    evV g x s (SeededClock.rounds bodies g x s k) E e p =
      evV g x s (tblV g x s (iterBoundV g x)) E e p := by
  have hFO := FilteredOverlapCaller.tail_firstOrder bodies.length e he
  rw [←evV_subst E e hFO,←evV_subst E e hFO]
  exact SeededClock.rounds_lexical hb hg x s k [] [] _ (subst_lexical bodies.length E e he) p hp

open RegularCaptureProduct

theorem rounds_base (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (D : Machine) (hD : 0<D.width) (extra : List MRule) (x : List Char) (s : Strategy)
    (k : Nat) (E : List (List Char)) (e : MExp) (he : Safe (grammar nodes D).rules.length e)
    (p : Nat) (hp : p≤x.length) :
    let g := FilteredOverlapCaller.extend nodes D extra
    evV g x s (SeededClock.rounds (component nodes D) g x s k) E e p =
      evV (grammar nodes D) x .callByValueSeq (DependentCaptureFilter.table nodes D x) E e p := by
  have he' : Safe (component nodes D).length e := by simpa [component] using he
  have hb := component_valid nodes hNodes D hD
  have hg := component_installed nodes D extra
  have hh : Installed (component nodes D) (grammar nodes D) := by simpa using component_installed nodes D []
  dsimp only []
  unfold FilteredOverlapCaller.extend
  rw [rounds_eval hb hg x s k E e he' p hp]
  exact canonical_eval hb hg hh x s .callByValueSeq E e he' p hp

theorem render_safe (nodes : List Node) (D : Machine) :
    ∀ a, DependentCaptureFilter.Valid nodes a → Safe (grammar nodes D).rules.length (DependentCaptureFilter.render a)
  | .lit _, _ | .param _, _ => True.intro
  | .helper i, hi => Nat.lt_of_lt_of_le hi (by simp [grammar])
  | .seq a b, ha | .alt a b, ha => ⟨render_safe nodes D a ha.1,render_safe nodes D b ha.2⟩
  | .notP a, ha => render_safe nodes D a ha

theorem choice_safe (n : Nat) : ∀ es, (∀ e∈es, Safe n e) → Safe n (choice es)
  | [], _ => True.intro
  | e::es, h => ⟨h e (by simp),choice_safe n es (fun e he => h e (by simp [he]))⟩

theorem filter_safe (nodes : List Node) (D : Machine) (hD : 0<D.width) (S : List (List Nat)) :
    ∀ a, DependentCaptureFilter.Valid nodes a → ∀ q r, q<D.width → r<D.width →
      Safe (grammar nodes D).rules.length (DependentCaptureFilter.filter nodes D S a q r)
  | .lit _, _, _, _, _, _ | .param _, _, _, _, _, _ => by
    simp only [DependentCaptureFilter.filter]; split <;> trivial
  | .helper i, hi, q, r, hq, hr => key_bound nodes D hD i q r hi hq hr
  | .seq a b, ha, q, r, hq, hr => by
    apply choice_safe
    intro e he
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp he
    exact ⟨filter_safe nodes D hD S a ha.1 q t hq (List.mem_range.mp ht),
      filter_safe nodes D hD S b ha.2 t r (List.mem_range.mp ht) hr⟩
  | .alt a b, ha, q, r, hq, hr =>
    ⟨⟨render_safe nodes D a ha.1,filter_safe nodes D hD S a ha.1 q r hq hr⟩,
      render_safe nodes D a ha.1,filter_safe nodes D hD S b ha.2 q r hq hr⟩
  | .notP a, ha, q, r, _, _ => by
    simp only [DependentCaptureFilter.filter]
    split <;> exact ⟨render_safe nodes D a ha,True.intro⟩

/-- The inline filter is valid inside arbitrary appended caller grammars,
not just in the standalone helper grammar. Both caller stages are arbitrary. -/
theorem filter_correct (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (D : Machine) (hD : D.Valid) (left right : List MRule) (x : List Char)
    (k l : Nat) (S : List (List Nat)) (E : List (List Char)) (hS : DependentCaptureFilter.Accurate D S E)
    (a : DependentCaptureFilter.Expr) (ha : DependentCaptureFilter.Valid nodes a)
    (p : Nat) (hp : p≤x.length) (q r : Nat) (hq : q<D.width) (hr : r<D.width) :
    let g := FilteredOverlapCaller.extend nodes D left
    let h := FilteredOverlapCaller.extend nodes D right
    evV h x .callByValueSeq (SeededClock.rounds (component nodes D) h x .callByValueSeq l) E
        (DependentCaptureFilter.filter nodes D S a q r) p =
      filtered D x q r p (evV g x .callByValuePar
        (SeededClock.rounds (component nodes D) g x .callByValuePar k) E (DependentCaptureFilter.render a) p) := by
  dsimp only []
  rw [rounds_base nodes hNodes D hD.1 right x .callByValueSeq l E _ (filter_safe nodes D hD.1 S a ha q r hq hr) p hp,
    rounds_base nodes hNodes D hD.1 left x .callByValuePar k E _ (render_safe nodes D a ha) p hp]
  exact DependentCaptureFilter.correct nodes hNodes D hD x S E hS a ha p hp q r hq hr

end Shallot.MacroPeg.CBV.ParametricHelperControl
