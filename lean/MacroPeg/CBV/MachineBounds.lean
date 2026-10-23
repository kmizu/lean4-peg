import MacroPeg.CBV.RankedArgs

namespace Shallot.MacroPeg.CBV

open Complexity Shallot.MacroPeg.KExp

namespace AddrExpr

theorem value_mono {V : Nat} {f h : Fin V → Nat} (hf : ∀ i, f i ≤ h i) (e : AddrExpr V) :
    value f e ≤ value h e := by
  induction e with
  | num _ => exact Nat.le_refl _
  | var i => exact hf i
  | add a b ha hb => exact Nat.add_le_add ha hb
  | mul a b ha hb => exact Nat.mul_le_mul ha hb

theorem cost_mono {V : Nat} {f h : Fin V → Nat} (hf : ∀ i, f i ≤ h i) (e : AddrExpr V) :
    cost f e ≤ cost h e := by
  induction e with
  | num _ | var _ => exact Nat.le_refl _
  | add a b ha hb =>
    exact Nat.add_le_add (Nat.add_le_add ha hb)
      (Nat.add_le_add_right (Nat.mul_le_mul_left 3 (value_mono hf b)) 8)
  | mul a b ha hb =>
    exact Nat.add_le_add (Nat.add_le_add ha hb)
      (Nat.add_le_add_right (Nat.mul_le_mul (value_mono hf b)
        (Nat.add_le_add_right (Nat.mul_le_mul_left 3 (value_mono hf a)) 5)) 8)

theorem inputs_power {V : Nat} (e : AddrExpr V) (k : Nat) (i : Fin V) :
    i ∈ inputs (power e k) → i ∈ inputs e := by
  induction k with
  | zero => simp [power, inputs]
  | succ k ih =>
    simp only [power, inputs, List.mem_append]
    intro h
    rcases h with h | h
    · exact ih h
    · exact h

end AddrExpr

def grammarArity (g : MGrammar) : Nat := (g.rules.map MRule.arity).sum

private theorem member_sum_bound : ∀ (xs : List Nat) (a : Nat), a ∈ xs → a ≤ xs.sum
  | [], _, h => by simp at h
  | b :: bs, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have := member_sum_bound bs a h; simp; omega

theorem grammarArity_bound {g : MGrammar} {rule : MRule} (hr : rule ∈ g.rules) :
    rule.arity ≤ grammarArity g :=
  member_sum_bound _ _ (List.mem_map.mpr ⟨rule, hr, rfl⟩)

def dictCap (n : Nat) : Nat := (n + 1) * (n + 1)
def rankCap (g : MGrammar) (n : Nat) : Nat := dictCap n ^ grammarArity g
def varsCap (g : MGrammar) (n : Nat) : Nat := n + dictCap n + rankCap g n + 1
def rowCap (g : MGrammar) (n : Nat) : Nat := g.rules.length * (rankCap g n * (n + 1))

theorem rankCap_bound {g : MGrammar} {x : List Char} {a : Nat} (ha : a ≤ grammarArity g) :
    (subStrs x).length ^ a ≤ rankCap g x.length := by
  apply Nat.le_trans (Nat.pow_le_pow_left (length_subStrs_le x) a)
  exact Nat.pow_le_pow_right (by exact Nat.mul_pos (by omega) (by omega)) ha

theorem rowCap_bound (g : MGrammar) (x : List Char) (T : Nat → List (List Char) → Val) :
    (pack g x T).length ≤ rowCap g x.length := by
  rw [pack_length]
  exact iterBoundV_le g x (fun _ hr => grammarArity_bound hr)

def rankStepCost (g : MGrammar) (k n : Nat) : Nat :=
  registerSpanCost n + AddrExpr.cost (fun _ => varsCap g n) (rankUpdateExpr k) + 20

def readCallCost (g : MGrammar) (i n : Nat) : Nat :=
  AddrExpr.cost (fun _ => varsCap g n) (rankAddressExpr g i) + 6 * rowCap g n +
    4 * AddrExpr.value (fun _ => varsCap g n) (rankAddressExpr g i) + 8

/-- Fixed input bounds used to charge every arithmetic operation and every saved-table scan. -/
theorem varsCap_poly (g : MGrammar) : IsPoly (varsCap g) := by
  have hd : IsPoly dictCap := isPoly_mul (isPoly_add isPoly_id (isPoly_const 1)) (isPoly_add isPoly_id (isPoly_const 1))
  exact isPoly_add (isPoly_add (isPoly_add isPoly_id hd) (isPoly_pow hd _)) (isPoly_const 1)

theorem rowCap_poly (g : MGrammar) : IsPoly (rowCap g) :=
  isPoly_mul (isPoly_const _) (isPoly_mul
    (isPoly_pow (isPoly_mul (isPoly_add isPoly_id (isPoly_const 1))
      (isPoly_add isPoly_id (isPoly_const 1))) _) (isPoly_add isPoly_id (isPoly_const 1)))

theorem rankStepCost_poly (g : MGrammar) (k : Nat) : IsPoly (rankStepCost g k) :=
  isPoly_add (isPoly_add registerSpanCost_poly (AddrExpr.cost_poly _ (fun _ => varsCap_poly g) _)) (isPoly_const 20)

theorem readCallCost_poly (g : MGrammar) (i : Nat) : IsPoly (readCallCost g i) :=
  tableRead_cost_poly _ _ _ (fun _ => varsCap_poly g) (rowCap_poly g)

mutual
  /-- The exact cost bound used by the complete fixed-expression compiler. -/
  def exprBudget (g : MGrammar) (m : Nat) : MExp → Nat → Nat
    | .eps, _ | .dbg _, _ | .lam _ _, _ => 3
    | .any, n => remainingLexCost Shallot.Packrat.Machine.anyTest n
    | .chr c, n => remainingLexCost (Shallot.Packrat.Machine.chrTest c) n
    | .range lo hi, n => remainingLexCost (Shallot.Packrat.Machine.rangeTest lo hi) n
    | .lit w, n => Shallot.Packrat.Machine.literalCost w n + 2
    | .param _, n => 12 * m + 10 + paramLiteralCost n
    | .seq a b, n => exprBudget g m a n + exprBudget g m b n + 7
    | .alt a b, n => exprBudget g m a n + exprBudget g m b n + 5
    | .notP a, n => exprBudget g m a n + 8
    | .star a, n => starEvalCost n (exprBudget g m a n)
    | .call i args, n => argsBudget g m args n + readCallCost g i n + 6
    | .callParam _ _, _ => 2
    | .invoke _ _ _, _ => 1

  def argsBudget (g : MGrammar) (m : Nat) : List MExp → Nat → Nat
    | [], _ => 0
    | a :: args, n => exprBudget g m a n + argsBudget g m args n + rankStepCost g args.length n
end

mutual
  theorem exprBudget_poly (g : MGrammar) (m : Nat) : ∀ e, IsPoly (exprBudget g m e)
    | .eps | .dbg _ | .lam _ _ => isPoly_const 3
    | .any => remainingLexCost_poly _
    | .chr _ => remainingLexCost_poly _
    | .range _ _ => remainingLexCost_poly _
    | .lit w => fixedLiteralCost_poly w
    | .param _ => isPoly_add (isPoly_const _) paramLiteralCost_poly
    | .seq a b => isPoly_add (isPoly_add (exprBudget_poly g m a) (exprBudget_poly g m b)) (isPoly_const 7)
    | .alt a b => isPoly_add (isPoly_add (exprBudget_poly g m a) (exprBudget_poly g m b)) (isPoly_const 5)
    | .notP a => isPoly_add (exprBudget_poly g m a) (isPoly_const 8)
    | .star a => starEvalCost_poly _ (exprBudget_poly g m a)
    | .call i args => isPoly_add (isPoly_add (argsBudget_poly g m args) (readCallCost_poly g i)) (isPoly_const 6)
    | .callParam _ _ => isPoly_const 2
    | .invoke _ _ _ => isPoly_const 1

  theorem argsBudget_poly (g : MGrammar) (m : Nat) : ∀ args, IsPoly (argsBudget g m args)
    | [] => isPoly_const 0
    | a :: args => isPoly_add (isPoly_add (exprBudget_poly g m a) (argsBudget_poly g m args)) (rankStepCost_poly g args.length)
end

end Shallot.MacroPeg.CBV
