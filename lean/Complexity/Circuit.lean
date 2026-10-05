import Complexity.Formula

namespace Complexity

/-- the definition below is part of the task; keep it exactly -/
def QF.toQbf (φ : QF) : Qbf := ⟨φ.prenex.1, compileF φ.prenex.2 []⟩

theorem lookup_nil : lookup [] = fun _ => false := by
  funext x; simp [lookup]

theorem lookup_cons (σ : List (Name × Bool)) (x : Name) (b : Bool) :
    lookup ((x, b) :: σ) = upd (lookup σ) x b := by
  funext y
  by_cases h : y = x
  · subst h; simp [lookup, upd]
  · have h' : ¬ (x = y) := fun e => h e.symm
    simp [lookup, upd, h, h']

theorem runGates_append (ρ : List (Name × Bool)) (gs hs : List Gate) (vals : List (Name × Bool)) :
    runGates ρ (gs ++ hs) vals = runGates ρ hs (runGates ρ gs vals) := by
  induction gs generalizing vals with
  | nil => rfl
  | cons g gs ih => exact ih _

theorem evalGates_append (ρ : List (Name × Bool)) (gs hs : List Gate) (vals : List (Name × Bool)) (l : Bool) :
    evalGates ρ (gs ++ hs) vals l = evalGates ρ hs (runGates ρ gs vals) (evalGates ρ gs vals l) := by
  induction gs generalizing vals l with
  | nil => rfl
  | cons g gs ih => exact ih _ _

theorem evalGates_single (ρ : List (Name × Bool)) (g : Gate) (vals : List (Name × Bool)) (l : Bool) :
    evalGates ρ [g] vals l = g.op.eval ρ vals := rfl

theorem runGates_single (ρ : List (Name × Bool)) (g : Gate) (vals : List (Name × Bool)) :
    runGates ρ [g] vals = (g.out, g.op.eval ρ vals) :: vals := rfl

private theorem not_pre_01 (p : Name) (a b : Nat) (h : a ≠ b) : ¬ (p ++ [a]) <+: (p ++ [b]) := by
  intro hp
  have := hp.eq_of_length (by simp)
  simp at this
  exact h this

private theorem pre_of_ext (p y : Name) (a : Nat) (h : (p ++ [a]) <+: y) : p <+: y :=
  (List.prefix_append p [a]).trans h

private theorem not_pre_ext_of (p y : Name) (a : Nat) (h : ¬ p <+: y) : ¬ (p ++ [a]) <+: y :=
  fun h' => h (pre_of_ext p y a h')

private theorem gate_step (σ vals : List (Name × Bool)) (p : Name) (op : Op) (y : Name) (hy : ¬ p <+: y) :
    lookup ((p, op.eval σ vals) :: vals) y = lookup vals y := by
  rw [lookup_cons]
  have : y ≠ p := fun e => hy (e ▸ List.prefix_refl _)
  simp [upd, this]

private theorem gate_self (σ vals : List (Name × Bool)) (p : Name) (op : Op) :
    lookup ((p, op.eval σ vals) :: vals) p = op.eval σ vals := by
  rw [lookup_cons]; simp [upd]

theorem compileF_spec (σ : List (Name × Bool)) : ∀ (ψ : Formula) (p : Name) (vals : List (Name × Bool)),
    lookup (runGates σ (compileF ψ p) vals) p = ψ.eval (lookup σ) ∧
    (∀ y, ¬ p <+: y → lookup (runGates σ (compileF ψ p) vals) y = lookup vals y) ∧
    evalGates σ (compileF ψ p) vals false = ψ.eval (lookup σ)
  | .var x, p, vals => by
    simp only [compileF, runGates_single, evalGates_single, Formula.eval]
    exact ⟨gate_self σ vals p (.var x),
      fun y hy => gate_step σ vals p (.var x) y hy, rfl⟩
  | .tt, p, vals => by
    simp only [compileF, runGates_single, evalGates_single, Formula.eval]
    exact ⟨gate_self σ vals p .tt,
      fun y hy => gate_step σ vals p .tt y hy, rfl⟩
  | .ff, p, vals => by
    simp only [compileF, runGates_single, evalGates_single, Formula.eval]
    exact ⟨gate_self σ vals p .ff,
      fun y hy => gate_step σ vals p .ff y hy, rfl⟩
  | .not a, p, vals => by
    obtain ⟨hA, hB, hC⟩ := compileF_spec σ a (p ++ [0]) vals
    simp only [compileF, runGates_append, evalGates_append, runGates_single, evalGates_single, Formula.eval]
    have e : Op.eval σ (runGates σ (compileF a (p ++ [0])) vals) (.not (p ++ [0])) = !a.eval (lookup σ) := by
      simp only [Op.eval, hA]
    rw [e]
    refine ⟨?_, ?_, rfl⟩
    · rw [lookup_cons]; simp [upd]
    · intro y hy
      rw [lookup_cons]
      have : y ≠ p := fun e => hy (e ▸ List.prefix_refl _)
      simp only [upd, this, if_false]
      exact hB y (not_pre_ext_of p y 0 hy)
  | .and a b, p, vals => by
    obtain ⟨hA, hB, _⟩ := compileF_spec σ a (p ++ [0]) vals
    obtain ⟨hA', hB', _⟩ := compileF_spec σ b (p ++ [1]) (runGates σ (compileF a (p ++ [0])) vals)
    have hA2 : lookup (runGates σ (compileF b (p ++ [1])) (runGates σ (compileF a (p ++ [0])) vals)) (p ++ [0])
        = a.eval (lookup σ) := by
      rw [hB' _ (not_pre_01 p 1 0 (by decide)), hA]
    simp only [compileF, runGates_append, evalGates_append, runGates_single, evalGates_single, Formula.eval]
    have e : Op.eval σ (runGates σ (compileF b (p ++ [1])) (runGates σ (compileF a (p ++ [0])) vals))
        (.and (p ++ [0]) (p ++ [1])) = (a.eval (lookup σ) && b.eval (lookup σ)) := by
      simp only [Op.eval, hA2, hA']
    rw [e]
    refine ⟨?_, ?_, rfl⟩
    · rw [lookup_cons]; simp [upd]
    · intro y hy
      rw [lookup_cons]
      have : y ≠ p := fun e => hy (e ▸ List.prefix_refl _)
      simp only [upd, this, if_false]
      rw [hB' y (not_pre_ext_of p y 1 hy)]
      exact hB y (not_pre_ext_of p y 0 hy)
  | .or a b, p, vals => by
    obtain ⟨hA, hB, _⟩ := compileF_spec σ a (p ++ [0]) vals
    obtain ⟨hA', hB', _⟩ := compileF_spec σ b (p ++ [1]) (runGates σ (compileF a (p ++ [0])) vals)
    have hA2 : lookup (runGates σ (compileF b (p ++ [1])) (runGates σ (compileF a (p ++ [0])) vals)) (p ++ [0])
        = a.eval (lookup σ) := by
      rw [hB' _ (not_pre_01 p 1 0 (by decide)), hA]
    simp only [compileF, runGates_append, evalGates_append, runGates_single, evalGates_single, Formula.eval]
    have e : Op.eval σ (runGates σ (compileF b (p ++ [1])) (runGates σ (compileF a (p ++ [0])) vals))
        (.or (p ++ [0]) (p ++ [1])) = (a.eval (lookup σ) || b.eval (lookup σ)) := by
      simp only [Op.eval, hA2, hA']
    rw [e]
    refine ⟨?_, ?_, rfl⟩
    · rw [lookup_cons]; simp [upd]
    · intro y hy
      rw [lookup_cons]
      have : y ≠ p := fun e => hy (e ▸ List.prefix_refl _)
      simp only [upd, this, if_false]
      rw [hB' y (not_pre_ext_of p y 1 hy)]
      exact hB y (not_pre_ext_of p y 0 hy)

theorem matrixValue_compileF (ψ : Formula) (σ : List (Name × Bool)) :
    matrixValue (compileF ψ []) σ = ψ.eval (lookup σ) := by
  exact (compileF_spec σ ψ [] []).2.2

theorem qEval_compileF (ψ : Formula) : ∀ (q : List (Bool × Name)) (σ : List (Name × Bool)),
    qEval (compileF ψ []) q σ = evalPrefix ψ q (lookup σ)
  | [], σ => matrixValue_compileF ψ σ
  | (true, x) :: q, σ => by
    simp only [qEval, evalPrefix, qEval_compileF ψ q, lookup_cons]
  | (false, x) :: q, σ => by
    simp only [qEval, evalPrefix, qEval_compileF ψ q, lookup_cons]

theorem QF.toQbf_value (φ : QF) (h : φ.Clean) : φ.toQbf.value = φ.eval (fun _ => false) := by
  simp only [QF.toQbf, Qbf.value]
  rw [qEval_compileF, lookup_nil, QF.eval_prenex φ h]

end Complexity
