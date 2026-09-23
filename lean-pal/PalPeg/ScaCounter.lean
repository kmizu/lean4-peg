import PalPeg.ScaProg

/-!
# Counters as persistent stacks

An unsigned counter is a stack of units; a signed counter keeps its sign in the control and its
magnitude as a stack of units, as Scala's unary counters do (`ScaffoldCircuitStructs`).
-/
set_option autoImplicit false
namespace PalPeg.ScaCounter
open PalPeg.ScaLocal PalPeg.ScaProg

/-! ## Unsigned -/

/-- The counter `n` is the one stack of `n` units. -/
def NatRep (n : ℕ) (st : Fin 1 → List Unit) : Prop := st 0 = List.replicate n ()

def incN : Prog Unit Unit 1 := .push 0 fun _ _ => ()
def decN : Prog Unit Unit 1 := .pop 0

theorem natRep_inc {n : ℕ} {st : Fin 1 → List Unit} (h : NatRep n st) (peek : ℕ) (c : Unit) :
    NatRep (n + 1) (incN.eval peek c st).2 := by
  unfold NatRep at h ⊢
  simp [incN, Prog.eval, h, List.replicate_succ]

theorem natRep_dec {n : ℕ} {st : Fin 1 → List Unit} (h : NatRep n st) (peek : ℕ) (c : Unit) :
    NatRep (n - 1) (decN.eval peek c st).2 := by
  unfold NatRep at h ⊢
  simp only [decN, Prog.eval, Function.update_self, h]
  cases n <;> simp [List.replicate_succ]

theorem natRep_zero_iff {n : ℕ} {st : Fin 1 → List Unit} (h : NatRep n st) (D : ℕ) (hD : 1 ≤ D) :
    (view D st 0 = []) ↔ n = 0 := by
  unfold NatRep at h
  simp only [view, h, List.take_eq_nil_iff]
  simp
  omega

/-! ## Signed -/

@[simp] theorem upd1 (st : Fin 1 → List Unit) (i j : Fin 1) (l : List Unit) :
    Function.update st i l j = l := by
  rw [Subsingleton.elim j i, Function.update_self]

/-- The signed counter `z`: the control holds `z < 0`, the stack holds `|z|` units. -/
def IntRep (z : ℤ) (neg : Bool) (st : Fin 1 → List Unit) : Prop :=
  st 0 = List.replicate z.natAbs () ∧ neg = decide (z < 0)

/-- `+1`: shrink a negative magnitude (clearing the sign at zero), else grow. -/
def incZ : Prog Unit Bool 1 :=
  .ite (fun c _ => c) (.seq (.pop 0) (.ctl fun _ v => decide (v 0 ≠ []))) (.push 0 fun _ _ => ())

/-- `-1`: shrink a positive magnitude, else grow and set the sign. -/
def decZ : Prog Unit Bool 1 :=
  .ite (fun c v => !c && decide (v 0 ≠ [])) (.pop 0) (.seq (.push 0 fun _ _ => ()) (.ctl fun _ _ => true))

theorem view1 (st : Fin 1 → List Unit) (z : ℤ) (hst : st 0 = List.replicate z.natAbs ())
    (peek : ℕ) (hpeek : 1 ≤ peek) : (view peek st 0 = []) ↔ z = 0 := by
  show (st 0).take peek = [] ↔ _
  rw [hst, List.take_eq_nil_iff]
  simp
  omega

theorem intRep_inc {z : ℤ} {neg : Bool} {st : Fin 1 → List Unit} (h : IntRep z neg st)
    (peek : ℕ) (hpeek : 1 ≤ peek) :
    IntRep (z + 1) (incZ.eval peek neg st).1 (incZ.eval peek neg st).2 := by
  obtain ⟨hst, hneg⟩ := h
  subst hneg
  by_cases hz : z < 0
  · have hn : z.natAbs = (z + 1).natAbs + 1 := by omega
    have hst' : (Function.update st 0 (st 0).tail) 0 = List.replicate (z + 1).natAbs () := by
      rw [upd1, hst, hn, List.replicate_succ, List.tail_cons]
    have hv := view1 (Function.update st 0 (st 0).tail) (z + 1) hst' peek hpeek
    have heval : incZ.eval peek (decide (z < 0)) st =
        (decide (view peek (Function.update st 0 (st 0).tail) 0 ≠ []),
          Function.update st 0 (st 0).tail) := by
      simp [incZ, Prog.eval, hz]
    rw [heval]
    refine ⟨hst', ?_⟩
    simp only [ne_eq, hv, decide_eq_decide]
    omega
  · have heval : incZ.eval peek (decide (z < 0)) st =
        (decide (z < 0), Function.update st 0 (() :: st 0)) := by
      simp [incZ, Prog.eval, hz]
    rw [heval]
    refine ⟨?_, ?_⟩
    · dsimp only; rw [upd1, hst, ← List.replicate_succ]; congr 1; omega
    · simp only [decide_eq_decide]; omega

theorem intRep_dec {z : ℤ} {neg : Bool} {st : Fin 1 → List Unit} (h : IntRep z neg st)
    (peek : ℕ) (hpeek : 1 ≤ peek) :
    IntRep (z - 1) (decZ.eval peek neg st).1 (decZ.eval peek neg st).2 := by
  obtain ⟨hst, hneg⟩ := h
  subst hneg
  have hv := view1 st z hst peek hpeek
  by_cases hz : 0 < z
  · have hc : (!decide (z < 0) && decide (view peek st 0 ≠ [])) = true := by
      simp only [ne_eq, hv]; simp; omega
    have heval : decZ.eval peek (decide (z < 0)) st =
        (decide (z < 0), Function.update st 0 (st 0).tail) := by
      simp only [decZ, Prog.eval, hc, if_true]
    rw [heval]
    have hn : z.natAbs = (z - 1).natAbs + 1 := by omega
    refine ⟨?_, ?_⟩
    · dsimp only; rw [upd1, hst, hn, List.replicate_succ, List.tail_cons]
    · simp only [decide_eq_decide]; omega
  · have hc : (!decide (z < 0) && decide (view peek st 0 ≠ [])) = false := by
      simp only [ne_eq, hv]; simp; omega
    have heval : decZ.eval peek (decide (z < 0)) st =
        (true, Function.update st 0 (() :: st 0)) := by
      simp only [decZ, Prog.eval, hc, Bool.false_eq_true, if_false]
    rw [heval]
    refine ⟨?_, ?_⟩
    · dsimp only; rw [upd1, hst, ← List.replicate_succ]; congr 1; omega
    · simp; omega

/-- Reading the sign and zero-ness from the control and the view. -/
theorem intRep_tests {z : ℤ} {neg : Bool} {st : Fin 1 → List Unit} (h : IntRep z neg st)
    (D : ℕ) (hD : 1 ≤ D) :
    (neg = true ↔ z < 0) ∧ (view D st 0 = [] ↔ z = 0) := by
  obtain ⟨hst, hneg⟩ := h
  subst hneg
  exact ⟨by simp, view1 st z hst D hD⟩

end PalPeg.ScaCounter
