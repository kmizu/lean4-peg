import Complexity.CfgEnc

/-!
# Semantics of the block formulas `initF`, `eqF`, `wfF`

A block that satisfies `wfF` encodes exactly one fitting configuration; `eqF` says two blocks agree on all variables.
-/

namespace Complexity

section WfSem

variable {k : Nat} (M : TM k) (S : Nat)

theorem mem_blockSuf {v : List Nat} : v ∈ blockSuf M S ↔
    (∃ q, q < M.nq ∧ [0, q] = v) ∨ (∃ i j, i < k ∧ j < S ∧ [1, i, j] = v) ∨
    (∃ i j s, i < k ∧ j < S ∧ s < M.na ∧ [2, i, j, s] = v) := by
  simp only [blockSuf, sSuf, hSuf, cSuf, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ((⟨q, hq, h⟩ | ⟨i, hi, j, hj, h⟩) | ⟨i, hi, j, hj, s, hs, h⟩)
    · exact Or.inl ⟨q, hq, h⟩
    · exact Or.inr (Or.inl ⟨i, j, hi, hj, h⟩)
    · exact Or.inr (Or.inr ⟨i, j, s, hi, hj, hs, h⟩)
  · rintro (⟨q, hq, h⟩ | ⟨i, j, hi, hj, h⟩ | ⟨i, j, s, hi, hj, hs, h⟩)
    · exact Or.inl (Or.inl ⟨q, hq, h⟩)
    · exact Or.inl (Or.inr ⟨i, hi, j, hj, h⟩)
    · exact Or.inr ⟨i, hi, j, hj, s, hs, h⟩

theorem bit_state (c : Cfg k) (q : Nat) : bit c [0, q] = decide (c.state = q) := rfl

theorem bit_pos (c : Cfg k) (i : Fin k) (j : Nat) : bit c [1, i.val, j] = decide (c.pos i = j) := by
  simp [bit, i.isLt]

theorem bit_cell (c : Cfg k) (i : Fin k) (j s : Nat) : bit c [2, i.val, j, s] = decide (c.cells i j = s) := by
  simp [bit, i.isLt]

theorem good_ext {c c' : Cfg k} (hc : Good M S c) (hc' : Good M S c')
    (h : ∀ v ∈ blockSuf M S, bit c v = bit c' v) : c = c' := by
  have hst : c.state = c'.state := by
    have hm : [0, c.state] ∈ blockSuf M S := (mem_blockSuf M S).2 (Or.inl ⟨_, hc.1, rfl⟩)
    have h2 := h _ hm
    rw [bit_state, bit_state] at h2
    exact (by simpa using h2.symm : c'.state = c.state).symm
  have hpos : c.pos = c'.pos := by
    funext i
    have hm : [1, i.val, c.pos i] ∈ blockSuf M S :=
      (mem_blockSuf M S).2 (Or.inr (Or.inl ⟨_, _, i.isLt, (hc.2 i).1, rfl⟩))
    have h2 := h _ hm
    rw [bit_pos, bit_pos] at h2
    exact (by simpa using h2.symm : c'.pos i = c.pos i).symm
  have hcl : c.cells = c'.cells := by
    funext i j
    by_cases hj : j < S
    · have hm : [2, i.val, j, c.cells i j] ∈ blockSuf M S :=
        (mem_blockSuf M S).2 (Or.inr (Or.inr ⟨_, _, _, i.isLt, hj, ((hc.2 i).2 j).1 hj, rfl⟩))
      have h2 := h _ hm
      rw [bit_cell, bit_cell] at h2
      exact (by simpa using h2.symm : c'.cells i j = c.cells i j).symm
    · have a1 := ((hc.2 i).2 j).2 (by omega)
      have a2 := ((hc'.2 i).2 j).2 (by omega)
      rw [a1, a2]
  cases c
  cases c'
  simp only [Cfg.mk.injEq]
  exact ⟨hst, hpos, hcl⟩

theorem initF_iff (ρ : Name → Bool) (b : Name) (c : Cfg k) :
    (initF M S b c).eval ρ = true ↔ Encodes M S ρ b c := by
  unfold initF Encodes
  rw [eval_bigAnd]
  simp only [List.mem_map]
  constructor
  · intro h v hv
    have := h _ ⟨v, hv, rfl⟩
    cases hb : bit c v <;> rw [hb] at this <;> simpa [Formula.eval] using this
  · rintro h _ ⟨v, hv, rfl⟩
    have := h v hv
    cases hb : bit c v <;> rw [hb] at this <;> simp [Formula.eval, this]

theorem eqF_iff (ρ : Name → Bool) (b b' : Name) :
    (eqF M S b b').eval ρ = true ↔ ∀ v ∈ blockSuf M S, ρ (b ++ v) = ρ (b' ++ v) := by
  unfold eqF
  rw [eval_bigAnd]
  simp only [List.mem_map]
  constructor
  · intro h v hv
    have := h _ ⟨v, hv, rfl⟩
    rw [eval_iff] at this
    simpa [Formula.eval] using this
  · rintro h _ ⟨v, hv, rfl⟩
    rw [eval_iff]
    simp [Formula.eval, h v hv]

theorem encodes_of_eqF {ρ : Name → Bool} {b b' : Name} {c : Cfg k}
    (he : (eqF M S b b').eval ρ = true) (h : Encodes M S ρ b' c) : Encodes M S ρ b c := by
  intro v hv
  rw [(eqF_iff M S ρ b b').1 he v hv]
  exact h v hv

theorem eqF_of_encodes {ρ : Name → Bool} {b b' : Name} {c : Cfg k}
    (h : Encodes M S ρ b c) (h' : Encodes M S ρ b' c) : (eqF M S b b').eval ρ = true := by
  rw [eqF_iff]
  intro v hv
  rw [h v hv, h' v hv]

theorem cfg_eq_of_eqF {ρ : Name → Bool} {b b' : Name} {c c' : Cfg k} (hc : Good M S c) (hc' : Good M S c')
    (h : Encodes M S ρ b c) (h' : Encodes M S ρ b' c') (he : (eqF M S b b').eval ρ = true) : c = c' := by
  apply good_ext M S hc hc'
  intro v hv
  rw [← h v hv, ← h' v hv]
  exact (eqF_iff M S ρ b b').1 he v hv

end WfSem

/-! ### Exactly-one groups -/

theorem pairsOf_mem {α : Type} : ∀ (l : List α) (p : α × α), p ∈ pairsOf l → p.1 ∈ l ∧ p.2 ∈ l
  | [], p, h => by simp [pairsOf] at h
  | x :: xs, p, h => by
    simp only [pairsOf, List.mem_append, List.mem_map] at h
    rcases h with ⟨y, hy, rfl⟩ | h
    · exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ hy⟩
    · have := pairsOf_mem xs p h
      exact ⟨List.mem_cons_of_mem _ this.1, List.mem_cons_of_mem _ this.2⟩

theorem pairsOf_ne {α : Type} : ∀ (l : List α), l.Nodup → ∀ p ∈ pairsOf l, p.1 ≠ p.2
  | [], _, p, h => by simp [pairsOf] at h
  | x :: xs, hn, p, h => by
    simp only [pairsOf, List.mem_append, List.mem_map] at h
    rw [List.nodup_cons] at hn
    rcases h with ⟨y, hy, rfl⟩ | h
    · intro e
      have e' : x = y := e
      exact hn.1 (e' ▸ hy)
    · exact pairsOf_ne xs hn.2 p h

theorem pairsOf_total {α : Type} : ∀ (l : List α) (x y : α), x ∈ l → y ∈ l → x ≠ y →
    (x, y) ∈ pairsOf l ∨ (y, x) ∈ pairsOf l
  | [], x, y, hx, _, _ => by simp at hx
  | a :: as, x, y, hx, hy, hne => by
    simp only [pairsOf, List.mem_append, List.mem_map]
    rw [List.mem_cons] at hx hy
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · exact absurd rfl hne
      · exact Or.inl (Or.inl ⟨y, hy, rfl⟩)
    · rcases hy with rfl | hy
      · exact Or.inr (Or.inl ⟨x, hx, rfl⟩)
      · rcases pairsOf_total as x y hx hy hne with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inr h)

theorem exOneF_iff (ρ : Name → Bool) (vs : List Name) (hn : vs.Nodup) :
    (exOneF vs).eval ρ = true ↔ ∃ x ∈ vs, ρ x = true ∧ ∀ y ∈ vs, ρ y = true → y = x := by
  unfold exOneF
  simp only [Formula.eval, Bool.and_eq_true, eval_bigOr, eval_bigAnd, List.mem_map]
  constructor
  · rintro ⟨⟨_, ⟨x, hx, rfl⟩, hxv⟩, hp⟩
    refine ⟨x, hx, hxv, fun y hy hyv => ?_⟩
    by_cases hne : y = x
    · exact hne
    exfalso
    rcases pairsOf_total vs y x hy hx hne with h | h
    · have := hp _ ⟨_, h, rfl⟩
      have hxv' : ρ x = true := hxv
      simp [Formula.eval, hyv, hxv'] at this
    · have := hp _ ⟨_, h, rfl⟩
      have hxv' : ρ x = true := hxv
      simp [Formula.eval, hyv, hxv'] at this
  · rintro ⟨x, hx, hxv, hu⟩
    refine ⟨⟨_, ⟨x, hx, rfl⟩, hxv⟩, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    have h1 := pairsOf_mem vs p hp
    have h2 := pairsOf_ne vs hn p hp
    simp only [Formula.eval, Bool.not_eq_true', Bool.and_eq_false_iff]
    cases h3 : ρ p.1 with
    | false => exact Or.inl rfl
    | true =>
      cases h4 : ρ p.2 with
      | false => exact Or.inr rfl
      | true => exact absurd ((hu _ h1.1 h3).trans (hu _ h1.2 h4).symm) h2

theorem exOne_range (ρ : Name → Bool) (f : Nat → Name) (hf : Function.Injective f) (n : Nat) :
    (exOneF ((List.range n).map f)).eval ρ = true ↔
      ∃ x, x < n ∧ ρ (f x) = true ∧ ∀ y, y < n → ρ (f y) = true → y = x := by
  have hn : ((List.range n).map f).Nodup := List.Pairwise.map f (fun a b hab h => hab (hf h)) List.nodup_range
  rw [exOneF_iff ρ _ hn]
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, hxv, hu⟩
    exact ⟨x, hx, hxv, fun y hy hyv => hf (hu _ ⟨y, hy, rfl⟩ hyv)⟩
  · rintro ⟨x, hx, hxv, hu⟩
    refine ⟨f x, ⟨x, hx, rfl⟩, hxv, ?_⟩
    rintro _ ⟨y, hy, rfl⟩ hyv
    rw [hu y hy hyv]

theorem oneHot_val (ρ : Name → Bool) (f : Nat → Name) (n x y : Nat) (hx : ρ (f x) = true)
    (hu : ∀ y, y < n → ρ (f y) = true → y = x) (hy : y < n) : ρ (f y) = decide (x = y) := by
  by_cases h : x = y
  · subst h; simp [hx]
  · cases hρ : ρ (f y)
    · simp [h]
    · exact absurd (hu y hy hρ).symm h

section WfSem2

variable {k : Nat} (M : TM k) (S : Nat)

theorem wfF_char (ρ : Name → Bool) (b : Name) :
    (wfF M S b).eval ρ = true ↔
      (∃ x, x < M.nq ∧ ρ (b ++ [0, x]) = true ∧ ∀ y, y < M.nq → ρ (b ++ [0, y]) = true → y = x) ∧
      (∀ i, i < k → ∃ x, x < S ∧ ρ (b ++ [1, i, x]) = true ∧ ∀ y, y < S → ρ (b ++ [1, i, y]) = true → y = x) ∧
      (∀ i, i < k → ∀ j, j < S → ∃ x, x < M.na ∧ ρ (b ++ [2, i, j, x]) = true ∧
        ∀ y, y < M.na → ρ (b ++ [2, i, j, y]) = true → y = x) := by
  have e0 : (sSuf M.nq).map (b ++ ·) = (List.range M.nq).map (fun q => b ++ [0, q]) := by
    simp [sSuf, List.map_map, Function.comp_def]
  unfold wfF
  rw [eval_bigAnd, e0]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · exact (exOne_range ρ _ (by intro x y h; simpa using h) _).1
        (h _ (List.mem_append_left _ List.mem_cons_self))
    · intro i hi
      exact (exOne_range ρ (fun j => b ++ [1, i, j]) (by intro x y h; simpa using h) _).1
        (h _ (List.mem_append_left _ (List.mem_cons_of_mem _
          (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))))
    · intro i hi j hj
      exact (exOne_range ρ (fun s => b ++ [2, i, j, s]) (by intro x y h; simpa using h) _).1
        (h _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi,
          List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩⟩)))
  · rintro ⟨h0, h1, h2⟩ a ha
    rcases List.mem_append.1 ha with ha | ha
    · rcases List.mem_cons.1 ha with rfl | ha
      · exact (exOne_range ρ _ (by intro x y h; simpa using h) _).2 h0
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
        exact (exOne_range ρ (fun j => b ++ [1, i, j]) (by intro x y h; simpa using h) _).2
          (h1 i (List.mem_range.1 hi))
    · obtain ⟨i, hi, hj'⟩ := List.mem_flatMap.1 ha
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hj'
      exact (exOne_range ρ (fun s => b ++ [2, i, j, s]) (by intro x y h; simpa using h) _).2
        (h2 i (List.mem_range.1 hi) j (List.mem_range.1 hj))

theorem wfF_iff (ρ : Name → Bool) (b : Name) :
    (wfF M S b).eval ρ = true ↔ ∃ c, Good M S c ∧ Encodes M S ρ b c := by
  rw [wfF_char]
  constructor
  · rintro ⟨h0, h1, h2⟩
    obtain ⟨q, hq1, hq2, hq3⟩ := h0
    obtain ⟨p, hp⟩ := Classical.axiomOfChoice (fun i : Fin k => h1 i.val i.isLt)
    obtain ⟨s, hs⟩ := Classical.axiomOfChoice
      (fun ij : Fin k × Fin S => h2 ij.1.val ij.1.isLt ij.2.val ij.2.isLt)
    let c : Cfg k :=
      ⟨q, p, fun i j => if hj : j < S then s (i, ⟨j, hj⟩) else 0⟩
    have hgood : Good M S c := by
      refine ⟨hq1, fun i => ⟨(hp i).1, fun j => ⟨fun hj => ?_, fun hj => ?_⟩⟩⟩
      · show (if hj : j < S then s (i, ⟨j, hj⟩) else 0) < M.na
        rw [dif_pos hj]; exact (hs (i, ⟨j, hj⟩)).1
      · show (if hj : j < S then s (i, ⟨j, hj⟩) else 0) = 0
        rw [dif_neg (by omega)]
    refine ⟨c, hgood, fun v hv => ?_⟩
    rcases (mem_blockSuf M S).1 hv with ⟨x, hx, rfl⟩ | ⟨i, j, hi, hj, rfl⟩ | ⟨i, j, t, hi, hj, ht, rfl⟩
    · rw [bit_state]
      exact oneHot_val ρ (fun y => b ++ [0, y]) M.nq q x hq2 hq3 hx
    · have := oneHot_val ρ (fun y => b ++ [1, i, y]) S (p ⟨i, hi⟩) j (hp ⟨i, hi⟩).2.1
        (hp ⟨i, hi⟩).2.2 hj
      have e := bit_pos c ⟨i, hi⟩ j
      simp only at e
      rw [e]
      exact this
    · have h5 := hs (⟨i, hi⟩, ⟨j, hj⟩)
      have := oneHot_val ρ (fun y => b ++ [2, i, j, y]) M.na (s (⟨i, hi⟩, ⟨j, hj⟩)) t h5.2.1 h5.2.2 ht
      have e := bit_cell c ⟨i, hi⟩ j t
      simp only at e
      rw [e]
      have hc : c.cells ⟨i, hi⟩ j = s (⟨i, hi⟩, ⟨j, hj⟩) := by
        show (if hj' : j < S then s (⟨i, hi⟩, ⟨j, hj'⟩) else 0) = _
        rw [dif_pos hj]
      rw [hc]
      exact this
  · rintro ⟨c, hg, he⟩
    refine ⟨⟨c.state, ?_, ?_, ?_⟩, fun i hi => ?_, fun i hi j hj => ?_⟩
    · exact hg.1
    · have := he [0, c.state] ((mem_blockSuf M S).2 (Or.inl ⟨_, hg.1, rfl⟩))
      rw [this]; simp [bit]
    · intro y hy hyv
      have := he [0, y] ((mem_blockSuf M S).2 (Or.inl ⟨_, hy, rfl⟩))
      rw [hyv] at this
      exact (by simpa [bit] using this : c.state = y).symm
    · refine ⟨c.pos ⟨i, hi⟩, (hg.2 ⟨i, hi⟩).1, ?_, ?_⟩
      · have := he [1, i, c.pos ⟨i, hi⟩]
          ((mem_blockSuf M S).2 (Or.inr (Or.inl ⟨_, _, hi, (hg.2 ⟨i, hi⟩).1, rfl⟩)))
        have e := bit_pos c ⟨i, hi⟩ (c.pos ⟨i, hi⟩)
        simp only at e
        rw [this, e]; simp
      · intro y hy hyv
        have := he [1, i, y] ((mem_blockSuf M S).2 (Or.inr (Or.inl ⟨_, _, hi, hy, rfl⟩)))
        rw [hyv] at this
        have e := bit_pos c ⟨i, hi⟩ y
        simp only at e
        rw [e] at this
        exact (by simpa using this : c.pos ⟨i, hi⟩ = y).symm
    · refine ⟨c.cells ⟨i, hi⟩ j, ((hg.2 ⟨i, hi⟩).2 j).1 hj, ?_, ?_⟩
      · have := he [2, i, j, c.cells ⟨i, hi⟩ j]
          ((mem_blockSuf M S).2 (Or.inr (Or.inr ⟨_, _, _, hi, hj, ((hg.2 ⟨i, hi⟩).2 j).1 hj, rfl⟩)))
        have e := bit_cell c ⟨i, hi⟩ j (c.cells ⟨i, hi⟩ j)
        simp only at e
        rw [this, e]; simp
      · intro y hy hyv
        have := he [2, i, j, y] ((mem_blockSuf M S).2 (Or.inr (Or.inr ⟨_, _, _, hi, hj, hy, rfl⟩)))
        rw [hyv] at this
        have e := bit_cell c ⟨i, hi⟩ j y
        simp only at e
        rw [e] at this
        exact (by simpa using this : c.cells ⟨i, hi⟩ j = y).symm

end WfSem2

end Complexity
