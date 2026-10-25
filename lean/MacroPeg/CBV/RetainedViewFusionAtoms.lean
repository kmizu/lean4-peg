import MacroPeg.CBV.RetainedViewFusionDeclarations

namespace Shallot.MacroPeg.CBV.RetainedViewFusionAtoms
open RetainedViewFusionSyntax RetainedViewFusionDeclarations
open RegularCaptureProduct (run filtered)
open ExactWordCaptureMachine (machine)
open FiniteSuffixReplay (views palette)
open ClockFreezing (Table)
open SubstringCaptureView (region dictionary)
abbrev project := FiniteSuffixObservedAtoms.project

/-- The unbounded payload stays real. Only its effect on a finite observer
is recovered from the substring metadata. -/
theorem state_views (seeds : List (List Char)) (u : List Char) (hu : u∈dictionary seeds)
    (E : List (List Char)) (q : Nat) (hq : q<(machine u).width) :
    state u q (views (region seeds) E)=run (machine u) q (main E) := by
  cases E with
  | nil => rfl
  | cons w E =>
    change SubstringCaptureView.advance u q (FiniteSuffixReplay.observe (region seeds) w)=run (machine u) q w
    exact SubstringCaptureView.advance_observe seeds u hu w q hq

theorem advance_mem (seeds : List (List Char)) (E : List (List Char)) (m : Mode) (hm : m∈modes (region seeds)) :
    advance (views (region seeds) E) m∈modes (region seeds) := by
  cases m with
  | none => simp [advance,modes]
  | some v =>
    rcases v with ⟨u,q,r⟩
    obtain ⟨hu,hq,hr⟩ := (mode_mem (region seeds) u q r).mp hm
    apply (mode_mem (region seeds) u _ r).mpr
    refine ⟨hu,?_,hr⟩
    rw [state_views seeds u hu E q hq]
    exact RegularCaptureProduct.run_bound (ExactWordCaptureMachine.valid u) q hq _

theorem retained_eval (g h : MGrammar) (x : List Char) (T U : Table) (R : List (List Char)) (E : List (List Char)) (p : Nat) :
    evV h x .callByValuePar U (payload E) (retained (views R E)) p=
      evV g x .callByValuePar T E (.param 0) p := by
  cases E <;> simp [retained,views,payload,main,evV,MExp.failAlways]

theorem retained_word (g : MGrammar) (x : List Char) (U : Table) (R : List (List Char)) (E : List (List Char))
    (p j : Nat) (hp : p≤x.length)
    (hv : evV g x .callByValuePar U (payload E) (retained (views R E)) p=some (some j)) : pre x p j=main E := by
  cases E with
  | nil => simp [retained,views,evV,MExp.failAlways] at hv
  | cons w E =>
    have hh : evV g x .callByValuePar U [w] (.param 0) p=some (some j) := by simpa [retained,views,payload,main] using hv
    exact (Option.some.inj (WordArguments.value_of_success g x _ U [w] (.param 0) True.intro p j hp hh)).symm

theorem retained_correct (g h : MGrammar) (x : List Char) (T U : Table) (seeds : List (List Char)) (E : List (List Char))
    (p : Nat) (hp : p≤x.length) (u : List Char) (hu : u∈dictionary seeds) (q r : Nat) (hq : q<(machine u).width) :
    evV h x .callByValuePar U (payload E) (retainedFilter (views (region seeds) E) (some (u,q,r))) p=
      filtered (machine u) x q r p (evV g x .callByValuePar T E (.param 0) p) := by
  rw [retainedFilter,state_views seeds u hu E q hq]
  have hh := FiniteSuffixObservedAtoms.atom_correct h x .callByValuePar U (payload E) (some (u,q,r))
    (retained (views (region seeds) E)) (main E) p (by intro j hj; exact retained_word h x U (region seeds) E p j hp hj)
  exact hh.trans (congrArg (filtered (machine u) x q r p) (retained_eval g h x T U (region seeds) E p))

theorem head_eval (g h : MGrammar) (x : List Char) (T U : Table) (R : List (List Char)) (E : List (List Char))
    (r : Spec) (he : E.length=r.arity) (p : Nat) (hp : p≤x.length) :
    evV h x .callByValuePar U (payload E) (.param 0) p=evV g x .callByValuePar T E (head r) p := by
  cases E with
  | nil => have ha : r.arity=0 := he.symm; simp [head,ha,payload,main,evV,Shallot.stripPrefix?,length_sfx x hp]
  | cons w E => have ha : r.arity≠0 := by rw [←he]; simp
                simp [head,ha,payload,main,evV]

theorem retainedReplay_eval (g : MGrammar) (x : List Char) (U : Table) (E : List (List Char))
    (R : List (List Char)) (V : View) (i p : Nat) (hp : p≤x.length) :
    evV g x .callByValuePar U E (.seq (FiniteSuffixReplay.guard R) (FiniteSuffixReplay.literal V i)) p=
      evV g x .callByValuePar U [] (.seq (FiniteSuffixReplay.guard R) (FiniteSuffixReplay.literal V i)) p := by
  have hg := FiniteSuffixReplay.guard_eval g x .callByValuePar U E R p hp
  have hh := FiniteSuffixReplay.guard_eval g x .callByValuePar U [] R p hp
  by_cases hv : sfx x p∈R
  · rw [if_pos hv] at hg hh
    rw [evV_seq_ok hg,evV_seq_ok hh]
    unfold FiniteSuffixReplay.literal
    split <;> rfl
  · rw [if_neg hv] at hg hh
    rw [evV_seq_fail hg,evV_seq_fail hh]

theorem replay_word (g : MGrammar) (x : List Char) (U : Table) (E : List (List Char))
    (R : List (List Char)) (V : View) (i p : Nat) (hp : p≤x.length) (j : Nat)
    (hv : evV g x .callByValuePar U E (.seq (FiniteSuffixReplay.guard R) (FiniteSuffixReplay.literal V i)) p=some (some j)) :
    pre x p j=V[i]?.join.getD [] := by
  rw [retainedReplay_eval g x U E R V i p hp] at hv
  exact FiniteSuffixObservedAtoms.replay_word g x .callByValuePar U R V i p hp j hv

theorem not_word (g : MGrammar) (x : List Char) (U : Table) (E : List (List Char))
    (e : MExp) (p j : Nat) (hv : evV g x .callByValuePar U E (.notP e) p=some (some j)) : pre x p j=[] := by
  cases hh : evV g x .callByValuePar U E e p with
  | none => simp [evV,hh] at hv
  | some v => cases v with
    | none => have he : p=j := by simpa [evV,hh] using hv
              simp [pre,he]
    | some q => simp [evV,hh] at hv

end Shallot.MacroPeg.CBV.RetainedViewFusionAtoms
