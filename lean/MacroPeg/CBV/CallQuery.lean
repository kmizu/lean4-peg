import MacroPeg.CBV.ArgsRuns

namespace Shallot.MacroPeg.CBV

open Complexity Shallot.MacroPeg.KExp

theorem resultCode_decode (v : Nat) : resultCode (resultDecode v) = v := by
  cases v with
  | zero => rfl
  | succ v => cases v <;> rfl

namespace AddrExpr

theorem inputs_sumExpr {V : Nat} (es : List (AddrExpr V)) (i : Fin V) :
    i ∈ inputs (sumExpr es) → ∃ e ∈ es, i ∈ inputs e := by
  induction es with
  | nil => simp [sumExpr, inputs]
  | cons e es ih =>
    simp only [sumExpr, inputs, List.mem_append]
    intro h
    rcases h with h | h
    · exact ⟨e, List.mem_cons_self, h⟩
    · obtain ⟨e', he', hm⟩ := ih h
      exact ⟨e', List.mem_cons_of_mem e he', hm⟩

end AddrExpr

theorem inputs_rankAddress (g : MGrammar) (i : Nat) (v : Fin 5)
    (hv : v ∈ AddrExpr.inputs (rankAddressExpr g i)) : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by
  simp only [rankAddressExpr, AddrExpr.inputs, List.mem_append, List.mem_singleton,
    List.not_mem_nil, or_false] at hv
  rcases hv with (h | h) | h
  · obtain ⟨e, he, hv⟩ := AddrExpr.inputs_sumExpr _ _ h
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp he
    cases hr : ruleAtM g.rules j with
    | none => simp [AddrExpr.widthExpr, hr, AddrExpr.inputs] at hv
    | some rule =>
      simp only [AddrExpr.widthExpr, hr, AddrExpr.inputs, List.mem_append] at hv
      rcases hv with h | h
      · have := AddrExpr.inputs_power (.var 0) rule.arity v h
        simp only [AddrExpr.inputs, List.mem_singleton] at this
        exact Or.inl this
      · simp only [AddrExpr.inputs, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at h
        exact Or.inr (Or.inl h)
  · rcases h with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr h))

theorem rankAddress_lt {g : MGrammar} {x : List Char} {i p rank : Nat} {rule : MRule}
    (hr : ruleAtM g.rules i = some rule) (hp : p ≤ x.length) (hRank : rank < (subStrs x).length ^ rule.arity) :
    ruleOffset g x i + rank * (x.length + 1) + p < (keys g x).length := by
  have hi := ruleAtM_lt hr
  have hlocal : rank * (x.length + 1) + p < (ruleKeys g x i).length := by
    rw [ruleKeys_length, ruleWidth, hr]
    dsimp only
    have hm := Nat.mul_le_mul_right (x.length + 1) (show rank + 1 ≤ (subStrs x).length ^ rule.arity by omega)
    rw [Nat.add_mul, Nat.one_mul] at hm
    omega
  have hg := get_flatMap_at (ruleKeys g x) (List.range g.rules.length) i (by simpa using hi)
    (rank * (x.length + 1) + p) (by simpa using hlocal)
  rw [ruleOffset_length (Nat.le_of_lt hi)] at hg
  simp only [List.getElem_range] at hg
  rw [List.getElem?_eq_getElem hlocal] at hg
  have hb := (List.getElem?_eq_some_iff.mp hg).1
  change ruleOffset g x i + rank * (x.length + 1) + p <
    ((List.range g.rules.length).flatMap (ruleKeys g x)).length
  simpa only [Nat.add_assoc] using hb

/-- The actual final continuation handles every valid scalar rank and charges its full arithmetic and table scan. -/
theorem ruleRead_bounded {K : Nat} (r : EvalRegs K) (g : MGrammar) (x : List Char)
    (T : Nat → List (List Char) → Val) (E : List Nat) (i : Nat) (rule : MRule)
    (hRule : ruleAtM g.rules i = some rule) (S : Lists K) (ready : EvalReady r S x (pack g x T) E)
    (p rank : Nat) (lp lr : List Nat) (hp : S (r.get 15) = lp ++ [p]) (hr : S (r.get 21) = lr ++ [rank])
    (hpn : p ≤ x.length) (hRank : rank < (subStrs x).length ^ rule.arity) :
    NRuns (ruleReadP r g i) S
      (S.set (r.get 16) (S (r.get 16) ++ [resultCode (rankLookup g x (pack g x T) i rank p)]))
      (readCallCost g i x.length) := by
  let f := evalValues (subStrs x).length x.length rank p 0
  have hf : ∀ j, j ∈ AddrExpr.inputs (rankAddressExpr g i) → ∃ l, S (r.address.vars j) = l ++ [f j] := by
    intro j hj
    rcases inputs_rankAddress g i j hj with rfl | rfl | rfl | rfl
    · refine ⟨[], ?_⟩
      change S (r.get 19) = [] ++ [(subStrs x).length]
      simpa only [List.nil_append, spans_length] using ready.count
    · exact ⟨[], ready.len⟩
    · exact ⟨lr, hr⟩
    · exact ⟨lp, hp⟩
  have he : AddrExpr.value f (rankAddressExpr g i) = ruleOffset g x i + rank * (x.length + 1) + p := by
    have ho : AddrExpr.value f (AddrExpr.sumExpr ((List.range i).map
        (fun j => AddrExpr.widthExpr g j (.var 0) (.add (.var 1) (.num 1))))) = ruleOffset g x i := by
      rw [AddrExpr.value_sumExpr, List.map_map]
      unfold ruleOffset
      congr 1
      apply List.map_congr_left
      intro j _
      cases hj : ruleAtM g.rules j <;>
        simp [AddrExpr.widthExpr, ruleWidth, hj, AddrExpr.value, AddrExpr.value_power, f, evalValues]
    simp only [rankAddressExpr, AddrExpr.value, ho]
    rfl
  have hi : AddrExpr.value f (rankAddressExpr g i) < (pack g x T).length := by
    rw [he]
    simpa only [pack, List.length_map] using rankAddress_lt hRule hpn hRank
  have hx := tableRead_runs_used r.address (r.get 22) (r.get 7) (r.get 16)
    (r.ne (by decide)) (r.ne (by decide)) (r.ne (by decide))
    (by simp [EvalRegs.address, List.nodup_cons]) f (rankAddressExpr g i) S (pack g x T) ready.table hf ready.tmp hi
  have hout : (pack g x T)[AddrExpr.value f (rankAddressExpr g i)] =
      resultCode (rankLookup g x (pack g x T) i rank p) := by
    unfold rankLookup
    rw [resultCode_decode, ← he]
    exact List.getElem_eq_getD 0
  rw [hout] at hx
  have hrankCap := rankCap_bound (x := x) (grammarArity_bound (ruleAtM_mem hRule))
  have hD := length_subStrs_le x
  have hvars : ∀ j, f j ≤ varsCap g x.length := by
    intro j
    rcases fin5_cases j with rfl | rfl | rfl | rfl | rfl
    · change (subStrs x).length ≤ varsCap g x.length; unfold varsCap dictCap; omega
    · change x.length ≤ varsCap g x.length; unfold varsCap; omega
    · change rank ≤ varsCap g x.length; unfold varsCap; omega
    · change p ≤ varsCap g x.length; unfold varsCap; omega
    · change 0 ≤ varsCap g x.length; omega
  have hc := AddrExpr.cost_mono hvars (rankAddressExpr g i)
  have hv := AddrExpr.value_mono hvars (rankAddressExpr g i)
  have ht := rowCap_bound g x T
  exact hx.mono (by unfold readCallCost; omega)

end Shallot.MacroPeg.CBV
