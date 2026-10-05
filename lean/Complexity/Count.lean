namespace Complexity

theorem nodup_map_on' {α β : Type} (f : α → β) : ∀ (l : List α), l.Nodup →
    (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → (l.map f).Nodup := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons a t ih =>
    intro hnd hinj
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hnd.2 (fun x hx y hy => hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))⟩
    intro hm
    rw [List.mem_map] at hm
    obtain ⟨y, hy, hy'⟩ := hm
    have := hinj y (List.mem_cons_of_mem _ hy) a (List.mem_cons_self) hy'
    exact hnd.1 (this ▸ hy)

/-- A duplicate-free list of bit vectors of length `V` has at most `2^V` elements. -/
theorem nodup_bitvecs_length_le {V : Nat} : ∀ (l : List (List Bool)), l.Nodup →
    (∀ v ∈ l, v.length = V) → l.length ≤ 2 ^ V := by
  induction V with
  | zero =>
    intro l hnd hlen
    match l with
    | [] => simp
    | [a] => simp
    | a :: b :: t =>
      exfalso
      have ha : a = [] := List.length_eq_zero_iff.mp (hlen a (by simp))
      have hb : b = [] := List.length_eq_zero_iff.mp (hlen b (by simp))
      have := (List.nodup_cons.mp hnd).1
      exact this (by simp [ha, hb])
  | succ V ih =>
    intro l hnd hlen
    let p : List Bool → Bool := fun v => v.head? == some true
    have hsplit := List.length_eq_countP_add_countP (l := l) p
    simp only [List.countP_eq_length_filter] at hsplit
    have hA : ((l.filter p).map List.tail).length ≤ 2 ^ V := by
      apply ih
      · apply nodup_map_on' _ _ (hnd.filter p)
        intro x hx y hy hxy
        rw [List.mem_filter] at hx hy
        match x, y, hx, hy with
        | a :: x', b :: y', hx, hy =>
          simp [p] at hx hy hxy
          simp [hx.2, hy.2, hxy]
      · intro v hv
        rw [List.mem_map] at hv
        obtain ⟨w, hw, rfl⟩ := hv
        rw [List.mem_filter] at hw
        have := hlen w hw.1
        match w with
        | a :: w' => simpa using this
    have hB : ((l.filter (fun a => decide ¬p a = true)).map List.tail).length ≤ 2 ^ V := by
      apply ih
      · apply nodup_map_on' _ _ (hnd.filter _)
        intro x hx y hy hxy
        rw [List.mem_filter] at hx hy
        have hxl := hlen x hx.1
        have hyl := hlen y hy.1
        match x, y, hx, hy with
        | a :: x', b :: y', hx, hy =>
          simp [p] at hx hy hxy
          have ha : a = false := by simpa using hx.2
          have hb : b = false := by simpa using hy.2
          simp [ha, hb, hxy]
      · intro v hv
        rw [List.mem_map] at hv
        obtain ⟨w, hw, rfl⟩ := hv
        rw [List.mem_filter] at hw
        have := hlen w hw.1
        match w with
        | a :: w' => simpa using this
    rw [List.length_map] at hA hB
    rw [hsplit, Nat.pow_succ]
    omega

theorem halt_within {α : Type} (f : α → α) (g : Nat → α) (hg : ∀ i, g (i + 1) = f (g i))
    (H : α → Prop) (hstay : ∀ y, H y → f y = y)
    (enc : α → List Bool) (V : Nat) (hlen : ∀ i, (enc (g i)).length = V)
    (hinj : ∀ i j, enc (g i) = enc (g j) → g i = g j)
    (t : Nat) (ht : H (g t)) : ∃ t', t' < 2 ^ V ∧ g t' = g t := by
  -- least halting index
  have hmin : ∀ t, H (g t) → ∃ t0, t0 ≤ t ∧ H (g t0) ∧ ∀ i < t0, ¬ H (g i) := by
    intro t
    induction t using Nat.strongRecOn with
    | _ t ih =>
      intro h
      by_cases hex : ∃ i, i < t ∧ H (g i)
      · obtain ⟨i, hi, hHi⟩ := hex
        obtain ⟨t0, h1, h2, h3⟩ := ih i hi hHi
        exact ⟨t0, by omega, h2, h3⟩
      · refine ⟨t, Nat.le_refl _, h, ?_⟩
        intro i hi hHi
        exact hex ⟨i, hi, hHi⟩
  obtain ⟨t0, hle, hH0, hmin0⟩ := hmin t ht
  have hconst : ∀ k, g (t0 + k) = g t0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ihk =>
      rw [← Nat.add_assoc, hg, ihk]
      exact hstay _ hH0
  have hgt : g t = g t0 := by
    have := hconst (t - t0)
    rwa [Nat.add_sub_cancel' hle] at this
  -- periodicity
  have hper : ∀ i j, g i = g j → ∀ k, g (i + k) = g (j + k) := by
    intro i j hij k
    induction k with
    | zero => simpa using hij
    | succ k ihk =>
      rw [← Nat.add_assoc, ← Nat.add_assoc, hg, hg, ihk]
  have hdist : ∀ i j, i < j → j ≤ t0 → g i ≠ g j := by
    intro i j hij hj heq
    obtain ⟨k, hk⟩ : ∃ k, t0 = j + k := ⟨t0 - j, by omega⟩
    have h1 := hper i j heq k
    have h2 : g (i + k) = g t0 := by rw [h1, hk]
    apply hmin0 (i + k) (by omega)
    rw [h2]
    exact hH0
  have hnd : ((List.range (t0 + 1)).map (fun i => enc (g i))).Nodup := by
    apply nodup_map_on' _ _ List.nodup_range
    intro x hx y hy hxy
    rw [List.mem_range] at hx hy
    have hg' := hinj x y hxy
    rcases Nat.lt_trichotomy x y with h | h | h
    · exact absurd hg' (hdist x y h (by omega))
    · exact h
    · exact absurd hg'.symm (hdist y x h (by omega))
  have hcount := nodup_bitvecs_length_le (V := V) _ hnd (by
    intro v hv
    rw [List.mem_map] at hv
    obtain ⟨i, _, rfl⟩ := hv
    exact hlen i)
  rw [List.length_map, List.length_range] at hcount
  exact ⟨t0, by omega, hgt.symm⟩

end Complexity
