import MacroPeg.CBV.FiniteSuffixObservedAtoms

namespace Shallot.MacroPeg.CBV.FiniteSuffixObservedDispatch
open FiniteSuffixObservedSyntax
open RegularCaptureProduct (run filtered)
open ExactWordCaptureMachine (machine)
open FiniteSuffixReplay (palette views)
open ClockFreezing (Table)

/-- Ordered exact probes require only the output filters of the actual
expression, including a parent-dependent expression with nested user calls. -/
theorem choose_eval (h : MGrammar) (x : List Char) (U : Table) (F : List Char → Nat → Nat → MExp)
    (p j : Nat) (K : Option (List Char) → MExp) : ∀ ws,
    (∀ u∈ws, evV h x .callByValueSeq U [] (F u 0 u.length) p=
      filtered (machine u) x 0 u.length p (some (some j))) →
    evV h x .callByValueSeq U [] (choose ws F K) p=
      evV h x .callByValueSeq U [] (K (if pre x p j∈ws then some (pre x p j) else none)) p
  | [],_ => rfl
  | u::ws,hf => by
    have hh := hf u (by simp)
    have he := ExactWordCaptureMachine.run_exact u (pre x p j)
    have ht : evV h x .callByValueSeq U [] (.andP (F u 0 u.length)) p=
        if pre x p j=u then some (some p) else some none := by
      rw [CallLookahead.evV_peek,hh]
      by_cases hw : pre x p j=u
      · rw [filtered,if_pos (he.mpr hw)]; simp [CallLookahead.peek,hw]
      · rw [filtered,if_neg (fun h => hw (he.mp h))]; simp [CallLookahead.peek,hw]
    rw [choose]
    by_cases hw : pre x p j=u
    · rw [if_pos hw] at ht
      rw [ScannerFrontier.branch_eval _ _ _ p true ht]
      simp [hw]
    · rw [if_neg hw] at ht
      rw [ScannerFrontier.branch_eval _ _ _ p false ht]
      simp only [Bool.false_eq_true,if_false]
      rw [choose_eval h x U F p j K ws (by intro v hv; exact hf v (by simp [hv]))]
      simp only [List.mem_cons,hw,false_or]

theorem select_eval (g h : MGrammar) (x : List Char) (T U : Table) (E : List (List Char))
    (R : List (List Char)) (a b : MExp) (F : List Char → Nat → Nat → MExp) (p : Nat)
    (hb : evV h x .callByValueSeq U [] b p=evV g x .callByValuePar T E a p)
    (hf : ∀ u∈palette R, evV h x .callByValueSeq U [] (F u 0 u.length) p=
      filtered (machine u) x 0 u.length p (evV g x .callByValuePar T E a p))
    (K : Option (List Char) → MExp) :
    evV h x .callByValueSeq U [] (select R b F K) p=
      match evV g x .callByValuePar T E a p with
      | some (some j) => evV h x .callByValueSeq U [] (K (FiniteSuffixReplay.observe R (pre x p j))) p
      | other => other := by
  change (match evV h x .callByValueSeq U [] (.andP b) p with
    | some (some j) => evV h x .callByValueSeq U [] (choose (palette R) F K) j | other => other)=_
  rw [CallLookahead.evV_peek,hb]
  cases hv : evV g x .callByValuePar T E a p with
  | none => rfl
  | some v => cases v with
    | none => rfl
    | some j =>
      dsimp only [CallLookahead.peek]
      exact choose_eval h x U F p j K (palette R) (by intro u hu; rw [hf u hu,hv])

def ArgRel (g h : MGrammar) (x : List Char) (T U : Table) (E : List (List Char))
    (R : List (List Char)) (rs : List Spec) (a : Term) (p : Nat) : Prop :=
  evV h x .callByValueSeq U [] (emit R rs (views R E) none a) p=evV g x .callByValuePar T E (original R a) p ∧
    ∀ u∈palette R, ∀ q r, q<u.length+2 → r<u.length+2 →
      evV h x .callByValueSeq U [] (emit R rs (views R E) (some (u,q,r)) a) p=
        filtered (machine u) x q r p (evV g x .callByValuePar T E (original R a) p)

theorem gather_eval (g h : MGrammar) (x : List Char) (T U : Table) (E : List (List Char))
    (R : List (List Char)) (rs : List Spec) (args : List Term) (p : Nat)
    (rel : ∀ a∈args, ArgRel g h x T U E R rs a p) (K : View → MExp) :
    evV h x .callByValueSeq U [] (gather R rs (views R E) args K) p=
      match evParArgs g x .callByValuePar T E (FiniteSuffixDependentView.renderArgs R none args) p with
      | some (some W) => evV h x .callByValueSeq U [] (K (views R W)) p
      | some none => some none | none => none := by
  induction args generalizing K with
  | nil => rfl
  | cons a args ih =>
    rw [gather,select_eval g h x T U E R (original R a) _ _ p (rel a (by simp)).1
      (by intro u hu; exact (rel a (by simp)).2 u hu 0 u.length (by omega) (by omega))]
    simp only [FiniteSuffixDependentView.renderArgs,evParArgs]
    cases hv : evV g x .callByValuePar T E (original R a) p with
    | none => rfl
    | some v => cases v with
      | none => rfl
      | some j =>
        dsimp only []
        rw [ih (by intro b hb; exact rel b (by simp [hb]))]
        cases ht : evParArgs g x .callByValuePar T E (FiniteSuffixDependentView.renderArgs R none args) p with
        | none => rfl
        | some v => cases v <;> rfl

end Shallot.MacroPeg.CBV.FiniteSuffixObservedDispatch
