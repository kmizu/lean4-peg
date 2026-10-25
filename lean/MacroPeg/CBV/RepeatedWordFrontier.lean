import MacroPeg.CBV.SynchronizedStarFrontier
import MacroPeg.CBV.RepeatedWordEvaluation

namespace Shallot.MacroPeg.CBV.RepeatedWordFrontier
open DelimiterTemplate DelimitedWordPattern DelimitedCopyProjection
open ClockFreezing SynchronizedStarFrontier

theorem compile_success (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (hT : OkTV x.length T) (E : List (List Char)) (d : Char) (ps : List Part)
    (p q : Nat) (hp : p≤x.length) :
    evV g x s T E (compile d ps) p=some (some q) ↔
      q≤x.length ∧ run d E ps (sfx x p)=some (sfx x q) := by
  constructor
  · intro he
    have hq := evV_ok hT _ p hp q he
    rw [compile_eval g x s T E d ps p hp] at he
    cases hr : run d E ps (sfx x p) with
    | none => simp [hr] at he
    | some rest =>
      have he : rest.length=q := by simpa [hr] using he
      have hs : sfx x q=rest := by
        rw [←he]
        exact sfx_suffix (suffix_trans (sfx_is_suffix x p)
          (DelimitedRepeatEvaluation.run_suffix d E ps (sfx x p) rest hr)).choose_spec
      exact ⟨hq,congrArg some hs.symm⟩
  · rintro ⟨hq,hr⟩
    simp only [compile_eval g x s T E d ps p hp,hr,Option.map_some,length_sfx x hq]

theorem source_failure_iff (d : Char) (E : List (List Char)) (hn : 0<E.length)
    (hfree : ∀ i, (hi : i<E.length) → Free d E[i])
    (js : List Nat) (hscope : ∀ i∈js, i<E.length) (x : List Char) :
    run d E (sourceParts d js) x=none ↔
      ∃ i, ∃ hi : i<E.length, run d [E[i]] (viewParts d i js) x=none := by
  classical
  constructor
  · intro hs
    by_cases hf : ∃ i, ∃ hi : i<E.length, run d [E[i]] (viewParts d i js) x=none
    · exact hf
    apply False.elim
    have hall : ∀ i, (hi : i<E.length) → ∃ rest, Matches d E[i] i js x rest := by
      intro i hi
      cases hr : run d [E[i]] (viewParts d i js) x with
      | none => exact False.elim (hf ⟨i,hi,hr⟩)
      | some rest => exact ⟨rest,(view_iff d E[i] (hfree i hi) i js x rest).mp hr⟩
    obtain ⟨rest,h0⟩ := hall 0 hn
    have hr : run d E (sourceParts d js) x=some rest := by
      apply (DelimitedWordPattern.source_iff_views d E hn hfree js hscope x rest).mpr
      intro i hi
      obtain ⟨tail,ht⟩ := hall i hi
      have he := matches_endpoint_unique d E[0] E[i] 0 i js x rest tail h0 ht
      simpa [he] using ht
    rw [hs] at hr
    cases hr
  · rintro ⟨i,hi,hf⟩
    cases hs : run d E (sourceParts d js) x with
    | none => rfl
    | some rest =>
      have hm := (DelimitedWordPattern.source_iff_views d E hn hfree js hscope x rest).mp hs i hi
      have hr := (view_iff d E[i] (hfree i hi) i js x rest).mpr hm
      rw [hf] at hr
      cases hr

def sourceStep (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (d : Char) (js : List Nat) : Nat → Res :=
  evV g x s T E (compile d (sourceParts d js))

def viewStep (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (d : Char) (js : List Nat) (i : Nat) : Nat → Res :=
  evV g x s T [E[i]!] (compile d (viewParts d i js))

def components (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (d : Char) (js : List Nat) : List (Nat → Res) :=
  (List.range E.length).map (viewStep g x s T E d js)

theorem step_success (g h : MGrammar) (x : List Char) (s t : Strategy) (T U : Table)
    (hT : OkTV x.length T) (hU : OkTV x.length U)
    (E : List (List Char)) (d : Char) (hn : 0<E.length)
    (hfree : ∀ i, (hi : i<E.length) → Free d E[i])
    (js : List Nat) (hscope : ∀ i∈js, i<E.length)
    (p q : Nat) (hp : p≤x.length) :
    sourceStep g x s T E d js p=some (some q) ↔
      ∀ f∈components h x t U E d js, f p=some (some q) := by
  have he : (∀ f∈components h x t U E d js, f p=some (some q)) ↔
      ∀ i, (hi : i<E.length) →
        evV h x t U [E[i]] (compile d (viewParts d i js)) p=some (some q) := by
    simp only [components,List.forall_mem_map,List.mem_range,viewStep]
    apply forall_congr'; intro i
    apply forall_congr'; intro hi
    simp only [getElem!_pos E i hi]
  rw [he,sourceStep,compile_success g x s T hT E d (sourceParts d js) p q hp]
  constructor
  · rintro ⟨hq,hr⟩ i hi
    apply (compile_success h x t U hU [E[i]] d (viewParts d i js) p q hp).mpr
    exact ⟨hq,(view_iff d E[i] (hfree i hi) i js _ _).mpr
      ((DelimitedWordPattern.source_iff_views d E hn hfree js hscope _ _).mp hr i hi)⟩
  · intro hall
    have hq := ((compile_success h x t U hU [E[0]] d (viewParts d 0 js) p q hp).mp (hall 0 hn)).1
    refine ⟨hq,(DelimitedWordPattern.source_iff_views d E hn hfree js hscope _ _).mpr ?_⟩
    intro i hi
    apply (view_iff d E[i] (hfree i hi) i js _ _).mp
    exact ((compile_success h x t U hU [E[i]] d (viewParts d i js) p q hp).mp (hall i hi)).2

theorem step_failure (g h : MGrammar) (x : List Char) (s t : Strategy) (T U : Table)
    (E : List (List Char)) (d : Char) (hn : 0<E.length)
    (hfree : ∀ i, (hi : i<E.length) → Free d E[i])
    (js : List Nat) (hscope : ∀ i∈js, i<E.length)
    (p : Nat) (hp : p≤x.length) :
    sourceStep g x s T E d js p=some none ↔
      ∃ f∈components h x t U E d js, f p=some none := by
  have hsrc : sourceStep g x s T E d js p=some none ↔ run d E (sourceParts d js) (sfx x p)=none := by
    simp [sourceStep,compile_eval g x s T E d (sourceParts d js) p hp]
  rw [hsrc,source_failure_iff d E hn hfree js hscope (sfx x p)]
  constructor
  · rintro ⟨i,hi,hr⟩
    refine ⟨viewStep h x t U E d js i,List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩,?_⟩
    simp [viewStep,getElem!_pos E i hi,compile_eval h x t U [E[i]] d (viewParts d i js) p hp,hr]
  · rintro ⟨f,hf,hr⟩
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hf
    have hi := List.mem_range.mp hi
    refine ⟨i,hi,?_⟩
    simpa [viewStep,getElem!_pos E i hi,compile_eval h x t U [E[i]] d (viewParts d i js) p hp] using hr

/-- Exact bare-star residual, with arbitrary following input. In the
remaining-suffix position convention, maximum means earliest stop. -/
theorem physical (g h : MGrammar) (x : List Char) (s t : Strategy) (T U : Table)
    (hT : OkTV x.length T) (hU : OkTV x.length U)
    (E : List (List Char)) (d : Char) (hn : 0<E.length)
    (hfree : ∀ i, (hi : i<E.length) → Free d E[i])
    (j : Nat) (js : List Nat) (hscope : ∀ i∈j::js, i<E.length)
    (p : Nat) (hp : p≤x.length) :
    evV g x s T E (.star (compile d (sourceParts d (j::js)))) p=
      loops (components h x t U E d (j::js)) p := by
  rw [evV_star]
  refine star_maximum (sourceStep g x s T E d (j::js)) (components h x t U E d (j::js)) ?_ x.length ?_ ?_ ?_ ?_ ?_ p hp
  · simpa [components] using (Nat.ne_of_gt hn)
  · intro q hq; exact ⟨_,compile_eval g x s T E d _ q hq⟩
  · intro f hf q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hf
    exact ⟨_,compile_eval h x t U [E[i]!] d _ q hq⟩
  · intro f hf q hq r hr
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hf
    have hi := List.mem_range.mp hi
    have hr : evV h x t U [E[i]] (compile d (viewParts d i (j::js))) q=some (some r) := by
      simpa [viewStep,getElem!_pos E i hi] using hr
    have hh := (compile_success h x t U hU [E[i]] d _ q r hq).mp hr
    have hlt := RepeatedWordEvaluation.view_progress d E[i] (hfree i hi) i j js _ _ hh.2
    simpa only [length_sfx x hq,length_sfx x hh.1] using hlt
  · intro q hq r
    exact step_success g h x s t T U hT hU E d hn hfree (j::js) hscope q r hq
  · exact step_failure g h x s t T U E d hn hfree (j::js) hscope

/-- An arbitrary continuation runs at the computed frontier in the
original retained environment. This is an evaluator identity, not a Seq
grammar construction for `loops`. -/
theorem followed_by (g h : MGrammar) (x : List Char) (s t : Strategy) (T U : Table)
    (hT : OkTV x.length T) (hU : OkTV x.length U)
    (E : List (List Char)) (d : Char) (hn : 0<E.length)
    (hfree : ∀ i, (hi : i<E.length) → Free d E[i])
    (j : Nat) (js : List Nat) (hscope : ∀ i∈j::js, i<E.length)
    (tail : MExp) (p : Nat) (hp : p≤x.length) :
    evV g x s T E (.seq (.star (compile d (sourceParts d (j::js)))) tail) p=
      match loops (components h x t U E d (j::js)) p with
      | some (some q) => evV g x s T E tail q
      | other => other := by
  change (match evV g x s T E (.star (compile d (sourceParts d (j::js)))) p with
    | some (some q) => evV g x s T E tail q | other => other)=_
  rw [physical g h x s t T U hT hU E d hn hfree j js hscope p hp]

end Shallot.MacroPeg.CBV.RepeatedWordFrontier
