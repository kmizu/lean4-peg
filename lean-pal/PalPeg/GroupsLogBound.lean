import PalPeg.GroupsLog

/-!
# 群数の無条件対数上界

`PalPeg.GroupsLog` に残っていた「未完部分」——正準群列の隣接群から `chainRev v` の
連続 3 要素を取り出す list 手術——をここで埋め、

* `tops_shrink` … `(groupChainRevN v).map Group.top` が 2/3 縮小鎖であること
* `groupCount_le` … 群数 ≤ `2 * log₂ |v| + 4`（仮定なし）

を得る。
-/

namespace PalPeg

/-! ## 狭義降順リストにおける「連続」 -/

/-- 狭義降順リストで隣り合う 2 要素の間には何も入らない。 -/
theorem sorted_consecutive {A B : List ℕ} {x y : ℕ}
    (hp : (A ++ x :: y :: B).Pairwise (· > ·)) :
    y < x ∧ ∀ m ∈ A ++ x :: y :: B, m < x → m ≤ y := by
  rw [List.pairwise_append] at hp
  obtain ⟨_hA, hxy, hcross⟩ := hp
  rw [List.pairwise_cons] at hxy
  obtain ⟨hx, hyB⟩ := hxy
  have h1 : y < x := hx y (by simp)
  refine ⟨h1, ?_⟩
  intro m hm hlt
  rcases List.mem_append.mp hm with hm | hm
  · exact absurd (hcross m hm x (by simp)) (by omega)
  · rcases List.mem_cons.mp hm with rfl | hm
    · omega
    · rcases List.mem_cons.mp hm with rfl | hm
      · omega
      · exact le_of_lt ((List.pairwise_cons.mp hyB).1 m hm)

/-- `chainRev v` を `A ++ x :: y :: B` と分解できれば、`x`, `y` は鎖の連続 2 要素。 -/
theorem chainRev_consecutive (v : List (Fin 2)) {A B : List ℕ} {x y : ℕ}
    (hL : chainRev v = A ++ x :: y :: B) :
    x ∈ chainRev v ∧ y ∈ chainRev v ∧ y < x ∧ ∀ m ∈ chainRev v, m < x → m ≤ y := by
  have hp : (A ++ x :: y :: B).Pairwise (· > ·) := by
    rw [← hL]; exact chainRev_pairwise_gt v
  obtain ⟨h1, h2⟩ := sorted_consecutive hp
  refine ⟨by rw [hL]; simp, by rw [hL]; simp, h1, ?_⟩
  intro m hm
  rw [hL] at hm
  exact h2 m hm

/-- **連続 3 要素の縮小**。`chainRev v` の連続 3 要素 `x > y > z` の下側の差が
上側の差と異なれば（`gap_antitone` により真に小さいので）`3 * y < 2 * x`。 -/
theorem triple_shrink (v : List (Fin 2)) {A B : List ℕ} {x y z : ℕ}
    (hL : chainRev v = A ++ x :: y :: z :: B) (hne : y - z ≠ x - y) :
    3 * y < 2 * x := by
  obtain ⟨hx, hy, hxy, hgx⟩ := chainRev_consecutive v hL
  have hL' : chainRev v = (A ++ [x]) ++ y :: z :: B := by rw [hL]; simp
  obtain ⟨_, hz, hyz, hgy⟩ := chainRev_consecutive v hL'
  have hle := gap_antitone v hx hy hxy hyz hgy
  exact boundary_shrink v hx hy hz hxy hyz hgx hgy (by omega)

/-! ## 群の展開の先頭・末尾の剥がし -/

theorem expand_last (p t k : ℕ) (hk : 1 ≤ k) :
    Group.expand ⟨p, t, k⟩ = Group.expand ⟨p, t, k - 1⟩ ++ [t - (k - 1) * p] := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simpa using expand_succ_right p t m

theorem expand_last2 (p t k : ℕ) (hk : 2 ≤ k) (hh : (k - 1) * p ≤ t) :
    Group.expand ⟨p, t, k⟩
      = Group.expand ⟨p, t, k - 2⟩ ++ [t - (k - 1) * p + p, t - (k - 1) * p] := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hmp : (m + 1) * p = m * p + p := by rw [Nat.succ_mul]
  rw [show m + 2 - 1 = m + 1 from by omega, show m + 2 - 2 = m from by omega]
  rw [show m + 2 - 1 = m + 1 from by omega] at hh
  rw [expand_succ_right p t (m + 1), expand_succ_right p t m, List.append_assoc]
  congr 1
  have hstep : t - m * p = t - (m + 1) * p + p := by omega
  simp [hstep]

theorem expand_head (p t k : ℕ) (hk : 1 ≤ k) :
    Group.expand ⟨p, t, k⟩ = t :: Group.expand ⟨p, t - p, k - 1⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simpa using expand_succ p t m

theorem expand_head2 (p t k : ℕ) (hk : 2 ≤ k) :
    Group.expand ⟨p, t, k⟩ = t :: (t - p) :: Group.expand ⟨p, t - p - p, k - 2⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  rw [show m + 2 - 2 = m from by omega, expand_succ p t (m + 1), expand_succ p (t - p) m]

/-! ## 隣接群の先頭は 2/3 で縮む -/

/-- **鍵となる補題**。展開が `chainRev v` の中に（順序を保って）現れる正準な隣接群
`g₁, g₂` について `3 * g₂.top < 2 * g₁.top`。

`g₁` の末項 `e` と `g₂.top` は `chainRev v` の連続 2 要素であり、`¬ Mergeable g₁ g₂`
は「境界での差の変化」を意味する。差が変わる 3 連続要素に `boundary_shrink` を当てる。 -/
theorem adjacent_top_shrink (v : List (Fin 2)) {pre post : List ℕ} {g₁ g₂ : Group}
    (hL : pre ++ (g₁.expand ++ (g₂.expand ++ post)) = chainRev v)
    (hh1 : Honest g₁) (hk1 : 1 ≤ g₁.count)
    (hh2 : Honest g₂) (hk2 : 1 ≤ g₂.count)
    (hnm : ¬ Mergeable g₁ g₂) :
    3 * g₂.top < 2 * g₁.top := by
  obtain ⟨p₁, t₁, k₁⟩ := g₁
  obtain ⟨p₂, t₂, k₂⟩ := g₂
  simp only [Honest] at hh1 hh2
  simp only at hk1 hk2 hh1 hh2 ⊢
  obtain ⟨e, he⟩ : ∃ e, e = t₁ - (k₁ - 1) * p₁ := ⟨_, rfl⟩
  have hetop : e ≤ t₁ := by rw [he]; exact Nat.sub_le _ _
  have hE1 : Group.expand ⟨p₁, t₁, k₁⟩ = Group.expand ⟨p₁, t₁, k₁ - 1⟩ ++ [e] := by
    rw [he]; exact expand_last p₁ t₁ k₁ hk1
  have hE2 : Group.expand ⟨p₂, t₂, k₂⟩ = t₂ :: Group.expand ⟨p₂, t₂ - p₂, k₂ - 1⟩ :=
    expand_head p₂ t₂ k₂ hk2
  have hdec : chainRev v =
      (pre ++ Group.expand ⟨p₁, t₁, k₁ - 1⟩) ++ e :: t₂ ::
        (Group.expand ⟨p₂, t₂ - p₂, k₂ - 1⟩ ++ post) := by
    rw [← hL, hE1, hE2]; simp
  obtain ⟨_hem, _htm, hlt, _hgap⟩ := chainRev_consecutive v hdec
  have ht2t1 : t₂ < t₁ := by omega
  -- 融合不能性を「条件 4 ∧ 条件 5」の否定として取り出す
  have hnm' : ¬ (t₂ + Group.diff ⟨p₁, t₁, k₁⟩ ⟨p₂, t₂, k₂⟩
        = t₁ - (k₁ - 1) * Group.diff ⟨p₁, t₁, k₁⟩ ⟨p₂, t₂, k₂⟩
      ∧ (p₂ = Group.diff ⟨p₁, t₁, k₁⟩ ⟨p₂, t₂, k₂⟩ ∨ k₂ = 1)) := by
    rintro ⟨h4, h5⟩
    exact hnm ⟨hk1, hk2, ht2t1, h4, h5⟩
  have hdval : Group.diff (⟨p₁, t₁, k₁⟩ : Group) ⟨p₂, t₂, k₂⟩
      = if k₁ = 1 then t₁ - t₂ else p₁ := rfl
  rw [hdval] at hnm'
  -- 周期不一致の場合（`g₂` の内部に 3 連続要素を取る）
  have caseB : 2 ≤ k₂ → p₂ ≠ e - t₂ → 3 * t₂ < 2 * t₁ := by
    intro hk2' hpne
    have hp2t : p₂ ≤ t₂ :=
      le_trans (Nat.le_mul_of_pos_left p₂ (by omega)) hh2
    have hE2' : Group.expand ⟨p₂, t₂, k₂⟩
        = t₂ :: (t₂ - p₂) :: Group.expand ⟨p₂, t₂ - p₂ - p₂, k₂ - 2⟩ :=
      expand_head2 p₂ t₂ k₂ hk2'
    have hdec2 : chainRev v =
        (pre ++ Group.expand ⟨p₁, t₁, k₁ - 1⟩) ++ e :: t₂ :: (t₂ - p₂) ::
          (Group.expand ⟨p₂, t₂ - p₂ - p₂, k₂ - 2⟩ ++ post) := by
      rw [← hL, hE1, hE2']; simp
    have h3 := triple_shrink v hdec2 (by omega)
    omega
  -- 境界で差が変わる場合（`g₁` の内部に 3 連続要素を取る）
  have caseA : 2 ≤ k₁ → e - t₂ ≠ p₁ → 3 * t₂ < 2 * t₁ := by
    intro hk1' hne
    have hple : p₁ ≤ (k₁ - 1) * p₁ := Nat.le_mul_of_pos_left p₁ (by omega)
    have hep : e + p₁ ≤ t₁ := by omega
    have hE1' : Group.expand ⟨p₁, t₁, k₁⟩
        = Group.expand ⟨p₁, t₁, k₁ - 2⟩ ++ [e + p₁, e] := by
      rw [he]; exact expand_last2 p₁ t₁ k₁ hk1' hh1
    have hdec1 : chainRev v =
        (pre ++ Group.expand ⟨p₁, t₁, k₁ - 2⟩) ++ (e + p₁) :: e :: t₂ ::
          (Group.expand ⟨p₂, t₂ - p₂, k₂ - 1⟩ ++ post) := by
      rw [← hL, hE1', hE2]; simp
    have h3 := triple_shrink v hdec1 (by omega)
    omega
  by_cases hk1eq : k₁ = 1
  · -- 単項群：実効公差は `t₁ - t₂`、条件 4 は自動的に成立する
    rw [if_pos hk1eq] at hnm'
    have hee : e = t₁ := by rw [he, hk1eq]; simp
    have h4 : t₂ + (t₁ - t₂) = t₁ - (k₁ - 1) * (t₁ - t₂) := by
      rw [hk1eq]; simp only [Nat.sub_self, Nat.zero_mul, Nat.sub_zero]; omega
    have h5 : ¬ (p₂ = t₁ - t₂ ∨ k₂ = 1) := fun h => hnm' ⟨h4, h⟩
    exact caseB (by omega) (by omega)
  · rw [if_neg hk1eq, ← he] at hnm'
    by_cases hc4 : t₂ + p₁ = e
    · have h5 : ¬ (p₂ = p₁ ∨ k₂ = 1) := fun h => hnm' ⟨hc4, h⟩
      exact caseB (by omega) (by omega)
    · exact caseA (by omega) (by omega)

/-! ## 群数の無条件対数上界 -/

theorem tops_isChain_aux (v : List (Fin 2)) : ∀ (gs : List Group) (pre : List ℕ),
    pre ++ expandAll gs = chainRev v →
    (∀ g ∈ gs, Honest g ∧ 1 ≤ g.count) →
    gs.IsChain (fun g₁ g₂ => ¬ Mergeable g₁ g₂) →
    (gs.map Group.top).IsChain (fun a b => 3 * b < 2 * a) := by
  intro gs
  induction gs with
  | nil => intro _ _ _ _; simp
  | cons g gs ih =>
      intro pre hL hprops hchain
      cases gs with
      | nil => simp
      | cons g₂ rest =>
          rw [List.isChain_cons_cons] at hchain
          obtain ⟨hnm, hchain'⟩ := hchain
          rw [List.map_cons, List.map_cons]
          refine List.isChain_cons_cons.mpr ⟨?_, ?_⟩
          · refine adjacent_top_shrink v (pre := pre) (post := expandAll rest) ?_
              (hprops g (by simp)).1 (hprops g (by simp)).2
              (hprops g₂ (by simp)).1 (hprops g₂ (by simp)).2 hnm
            rw [expandAll_cons, expandAll_cons] at hL
            exact hL
          · rw [← List.map_cons]
            refine ih (pre ++ g.expand) ?_ (fun g' hg' => hprops g' (by simp [hg'])) hchain'
            rw [List.append_assoc, ← expandAll_cons]
            exact hL

/-- **境界縮小の橋渡し**。正準群鎖の先頭列は 2/3 縮小鎖。 -/
theorem tops_shrink (v : List (Fin 2)) :
    ((groupChainRevN v).map Group.top).IsChain (fun a b => 3 * b < 2 * a) := by
  obtain ⟨hprops, hchain⟩ := canonical_groupChainRevN v
  refine tops_isChain_aux v (groupChainRevN v) [] ?_ hprops hchain
  simpa using expandAll_groupChainRevN v

/-- **群数の対数上界（無条件）**。 -/
theorem groupCount_le (v : List (Fin 2)) :
    (groupChainRevN v).length ≤ 2 * Nat.log 2 v.length + 4 :=
  groupCount_le_of_tops_shrink v (tops_shrink v)

end PalPeg
