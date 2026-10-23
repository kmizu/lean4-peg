import MacroPeg.CBV.ExprProgram

namespace Shallot.MacroPeg.CBV

open Complexity Shallot.MacroPeg.Mach Shallot.MacroPeg.KExp

@[simp] theorem rankUpdateExpr_value (f : Fin 5 → Nat) (k : Nat) :
    AddrExpr.value f (rankUpdateExpr k) = f 2 + f 4 * f 0 ^ k := by
  simp [rankUpdateExpr, AddrExpr.value, AddrExpr.value_power]

/-- The rank accumulator is updated by the actual arithmetic program; all other caller stacks survive. -/
theorem rankUpdate_runs {K : Nat} (r : EvalRegs K) (S : Lists K) (f : Fin 5 → Nat) (k : Nat)
    (hf : ∀ i, i ∈ AddrExpr.inputs (rankUpdateExpr k) → ∃ l, S (r.address.vars i) = l ++ [f i]) (ht : S (r.get 1) = [])
    {lr : List Nat} (hr : S (r.get 21) = lr ++ [f 2]) :
    NRuns (rankUpdateP r k) S (S.set (r.get 21) (lr ++ [f 2 + f 4 * f 0 ^ k]))
      (AddrExpr.cost f (rankUpdateExpr k) + 3) := by
  let v := f 2 + f 4 * f 0 ^ k
  have xa := AddrExpr.compile_runs_used r.address f (rankUpdateExpr k) S hf ht
  simp only [rankUpdateExpr_value] at xa
  change NRuns _ S (S.set (r.get 2) (S (r.get 2) ++ [v])) _ at xa
  let X := S.set (r.get 2) (S (r.get 2) ++ [v])
  have xp := nruns_pop (r.get 21) X (l := lr) (v := f 2) (by simp [X, Lists.set, hr])
  let Y := X.set (r.get 21) lr
  have xm := nruns_mv (r.get 2) (r.get 21) (r.ne (by decide)) Y
    (l := S (r.get 2)) (v := v) (by simp [Y, X, Lists.set])
  have he : (Y.set (r.get 21) (Y (r.get 21) ++ [v])).set (r.get 2) (S (r.get 2)) =
      S.set (r.get 21) (lr ++ [v]) := by
    funext z
    by_cases h2 : z = r.get 2
    · subst z; simp [Y, X, Lists.set]
    by_cases h21 : z = r.get 21
    · subst z; simp [Y, X, Lists.set]
    simp [Y, X, Lists.set, h2, h21]
  rw [he] at xm
  exact xa.seq (xp.seq xm)

/-- Accumulating each digit with its fixed suffix weight yields precisely the saved-table rank. -/
theorem wordRank_append (B : Nat) (xs ys : List Nat) :
    wordRank B (xs ++ ys) = wordRank B xs * B ^ ys.length + wordRank B ys := by
  induction xs with
  | nil => simp [wordRank]
  | cons a xs ih =>
    simp only [List.cons_append, wordRank, List.length_append, ih, Nat.pow_add, Nat.add_mul, Nat.mul_assoc]
    omega

theorem rankAddressExpr_value (f : Fin 5 → Nat) (g : MGrammar) (x : List Char)
    (i p : Nat) (ids : List Nat) (hb : f 0 = (subStrs x).length) (hn : f 1 = x.length)
    (hrank : f 2 = wordRank (subStrs x).length ids) (hp : f 3 = p) :
    AddrExpr.value f (rankAddressExpr g i) = address g x i ids p := by
  have ho : AddrExpr.value f (AddrExpr.sumExpr ((List.range i).map
      (fun j => AddrExpr.widthExpr g j (.var 0) (.add (.var 1) (.num 1))))) = ruleOffset g x i := by
    rw [AddrExpr.value_sumExpr, List.map_map]
    unfold ruleOffset
    congr 1
    apply List.map_congr_left
    intro j _
    cases hj : ruleAtM g.rules j <;>
      simp [Function.comp_def, AddrExpr.widthExpr, ruleWidth, hj, AddrExpr.value, AddrExpr.value_power, hb, hn]
  simp only [rankAddressExpr, AddrExpr.value, ho, hrank, hn, hp, address]

/-- Read the rule cell selected by the accumulated argument rank with concrete row access. -/
theorem ruleRead_runs {K : Nat} (r : EvalRegs K) (S : Lists K) (f : Fin 5 → Nat)
    (g : MGrammar) (x : List Char) (i p : Nat) (rule : MRule) (ids : List Nat)
    (T : Nat → List (List Char) → Val)
    (hf : ∀ j, j ∈ AddrExpr.inputs (rankAddressExpr g i) → ∃ l, S (r.address.vars j) = l ++ [f j]) (ht : S (r.get 1) = [])
    (hrow : S (r.get 22) = pack g x T)
    (hb : f 0 = (subStrs x).length) (hn : f 1 = x.length)
    (hrank : f 2 = wordRank (subStrs x).length ids) (hp : f 3 = p)
    (hRule : ruleAtM g.rules i = some rule)
    (hids : ids ∈ words (List.range (subStrs x).length) rule.arity) (hpn : p ≤ x.length) :
    ∃ v, NRuns (ruleReadP r g i) S (S.set (r.get 16) (S (r.get 16) ++ [v]))
      (AddrExpr.cost f (rankAddressExpr g i) + 6 * (pack g x T).length +
        4 * AddrExpr.value f (rankAddressExpr g i) + 8) ∧
      resultDecode v = valAt (T i (ids.map (literalAt x))) p := by
  have he := rankAddressExpr_value f g x i p ids hb hn hrank hp
  have hi : AddrExpr.value f (rankAddressExpr g i) < (pack g x T).length := by
    rw [he]
    have hk := (List.getElem?_eq_some_iff.mp (keys_get_address hRule hids hpn)).1
    simpa only [pack, List.length_map] using hk
  have hx := tableRead_runs_used r.address (r.get 22) (r.get 7) (r.get 16)
    (r.ne (by decide)) (r.ne (by decide)) (r.ne (by decide))
    (by simp [EvalRegs.address, List.nodup_cons]) f (rankAddressExpr g i) S (pack g x T) hrow hf ht hi
  refine ⟨(pack g x T)[AddrExpr.value f (rankAddressExpr g i)], hx, ?_⟩
  have hc := pack_get_address (T := T) hRule hids hpn
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [← he]; exact hi)] at hc
  simpa only [he, Option.getD_some] using hc

theorem rankUpdateCost_poly (f : Nat → Fin 5 → Nat) (hf : ∀ i, IsPoly (fun n => f n i)) (k : Nat) :
    IsPoly (fun n => AddrExpr.cost (f n) (rankUpdateExpr k) + 3) :=
  isPoly_add (AddrExpr.cost_poly f hf _) (isPoly_const 3)

theorem ruleReadCost_poly (f : Nat → Fin 5 → Nat) (rows : Nat → Nat)
    (hf : ∀ i, IsPoly (fun n => f n i)) (hrows : IsPoly rows) (g : MGrammar) (i : Nat) :
    IsPoly (fun n => AddrExpr.cost (f n) (rankAddressExpr g i) + 6 * rows n +
      4 * AddrExpr.value (f n) (rankAddressExpr g i) + 8) :=
  tableRead_cost_poly f _ rows hf hrows

end Shallot.MacroPeg.CBV
