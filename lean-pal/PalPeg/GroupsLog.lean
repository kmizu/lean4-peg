import PalPeg.Groups
import Mathlib.Data.Nat.Log

/-!
# 群表現の正準化 (canonicalization) と群数の対数上界

`PalPeg.Groups` の群表現 `groupChainRev` は「隣り合う群が実は 1 本の等差数列」という
冗長性を残す。本ファイルでは

* `mergeAdj` … 隣接群を 1 パスで融合する正準化（`expandAll_mergeAdj`, `honest_mergeAdj`）
* `Canonical` … 隣接群がもう融合できない状態（`canonical_mergeAdj`）
* `groupChainRevN` … 各ステップで正準化する群鎖（`expandAll_groupChainRevN`,
  `canonical_groupChainRevN`）
* `boundary_shrink` … 群境界で長さが 2/3 未満に落ちること（Fine–Wilf）
* `gap_antitone` … 鎖の差は下るほど広がらない
* `length_le_of_shrink`, `length_le_log_of_shrink` … 2/3 縮小列の長さの対数上界
* `groupCount_le_of_tops_shrink` … 群数 ≤ `2 * log₂ |v| + 4`（境界縮小を仮定した形）

**未完部分**：`boundary_shrink` から `groupCount_le_of_tops_shrink` の仮定
（隣接群の先頭が 2/3 で縮むこと）を導く一歩、すなわち「正準群列の隣接群から
`chainRev v` の連続 3 要素を取り出す」補題は未形式化。
`expandAll gs = chainRev v` のソート性に関する list 手術が必要になる。
なお `Group.diff`（単項群の実効公差）を入れないと群数が語長に比例することは
実測で確認済み（`Group.diff` の docstring 参照）。
-/

namespace PalPeg

/-! ## 隣接群の融合 -/

/-- 融合に使う**実効公差**。`count = 1` の群は公差が意味を持たない（`compress` は
`p = 0` を置き、`groupFilterOne` は古い `p` をそのまま引き継ぐ）ので、
単項の群については次の群の先頭との差を公差として採用する。

この規約を入れないと、`chainRev [0,1,0,1,0,0,…] = [5,3,1,0]` のような鎖に対して
`⟨1,5,1⟩, ⟨1,3,1⟩, ⟨1,1,2⟩`（`p` は履歴由来の 1）が「融合不能」と判定され、
群数が語長に比例して増えてしまう（実測済み）。 -/
def Group.diff (g₁ g₂ : Group) : ℕ := if g₁.count = 1 then g₁.top - g₂.top else g₁.p

/-- 群 `g₁`, `g₂` が 1 本の等差数列をなす（融合可能）。
`g₁` の末項 `top - (count-1)*d` の次が `g₂.top` であり、公差も一致すること
（`d = g₁.diff g₂` は実効公差。`g₁.count ≥ 2` なら `d = g₁.p` そのもの）。 -/
def Mergeable (g₁ g₂ : Group) : Prop :=
  1 ≤ g₁.count ∧ 1 ≤ g₂.count ∧ g₂.top < g₁.top ∧
    g₂.top + g₁.diff g₂ = g₁.top - (g₁.count - 1) * (g₁.diff g₂) ∧
      (g₂.p = g₁.diff g₂ ∨ g₂.count = 1)

instance (g₁ g₂ : Group) : Decidable (Mergeable g₁ g₂) := by
  unfold Mergeable; infer_instance

/-- 融合の結果。 -/
def Group.merge (g₁ g₂ : Group) : Group :=
  ⟨g₁.diff g₂, g₁.top, g₁.count + g₂.count⟩

/-- 隣接群を左から貪欲に融合する 1 パス。融合後は同じ群をもう一度次の群と比較する。 -/
def mergeAdj : List Group → List Group
  | [] => []
  | [g] => [g]
  | g₁ :: g₂ :: rest =>
      if Mergeable g₁ g₂ then mergeAdj (g₁.merge g₂ :: rest)
      else g₁ :: mergeAdj (g₂ :: rest)
termination_by gs => gs.length

/-! ### 融合は展開を変えない -/

/-- 等差数列の分割。`k ≥ 1`, `k' ≥ 1` で融合条件が成り立てば、
長さ `k + k'` の等差数列は 2 つの群の展開の連結。 -/
theorem expand_merge {p t k p' t' k' : ℕ} (hk : 1 ≤ k) (hk' : 1 ≤ k')
    (hcond : t' + p = t - (k - 1) * p) (hdisj : p' = p ∨ k' = 1) :
    Group.expand ⟨p, t, k + k'⟩ = Group.expand ⟨p, t, k⟩ ++ Group.expand ⟨p', t', k'⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hmp : m * p + p = (m + 1) * p := by rw [Nat.succ_mul]
  have ht' : t' = t - (m + 1) * p := by
    simp only [Nat.add_sub_cancel] at hcond
    omega
  simp only [Group.expand]
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  have hfun : ∀ i ∈ List.range k',
      ((fun i => t - i * p) ∘ (fun x => (m + 1) + x)) i = t' - i * p := by
    intro i _
    simp only [Function.comp_apply]
    have : (m + 1 + i) * p = (m + 1) * p + i * p := by rw [Nat.add_mul]
    rw [this, ← Nat.sub_sub, ht']
  rw [List.map_congr_left hfun]
  rcases hdisj with rfl | rfl
  · rfl
  · simp

/-- 単項の群は実効公差で置き換えても展開が変わらない。 -/
theorem expand_diff_eq (g₁ g₂ : Group) :
    Group.expand ⟨g₁.diff g₂, g₁.top, g₁.count⟩ = Group.expand g₁ := by
  obtain ⟨p, t, k⟩ := g₁
  simp only [Group.diff]
  by_cases h : k = 1
  · subst h; simp
  · rw [if_neg h]

theorem expand_Group_merge {g₁ g₂ : Group} (h : Mergeable g₁ g₂) :
    Group.expand (g₁.merge g₂) = Group.expand g₁ ++ Group.expand g₂ := by
  obtain ⟨hk, hk', _hlt, hcond, hdisj⟩ := h
  rw [Group.merge, expand_merge hk hk' hcond hdisj, expand_diff_eq g₁ g₂]

/-- 正直さの数値版。 -/
theorem honest_merge_raw {p t k p' t' k' : ℕ} (hk : 1 ≤ k) (hk' : 1 ≤ k')
    (hcond : t' + p = t - (k - 1) * p) (hdisj : p' = p ∨ k' = 1)
    (h1 : (k - 1) * p ≤ t) (h2 : (k' - 1) * p' ≤ t') : (k + k' - 1) * p ≤ t := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k' = j + 1 := ⟨k' - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h1 h2 hcond
  have hmp : m * p + p = (m + 1) * p := by rw [Nat.succ_mul]
  have hkp : (m + 1) * p ≤ t := by omega
  have hsum : ∀ q : ℕ, j * q + (m + 1) * q = (m + 1 + (j + 1) - 1) * q := by
    intro q
    have he : m + 1 + (j + 1) - 1 = j + (m + 1) := by omega
    rw [he]
    exact (Nat.add_mul j (m + 1) q).symm
  rcases hdisj with rfl | hj
  · -- 公差が一致する場合
    have := hsum p'
    omega
  · -- `g₂` が単項の場合
    have hj0 : j = 0 := by omega
    subst hj0
    have : m + 1 + (0 + 1) - 1 = m + 1 := by omega
    rw [this]
    exact hkp

/-- 実効公差でも正直さは保たれる（単項なら `(count-1)*d = 0`）。 -/
theorem honest_diff (g₁ g₂ : Group) (h1 : Honest g₁) :
    (g₁.count - 1) * (g₁.diff g₂) ≤ g₁.top := by
  simp only [Honest] at h1
  simp only [Group.diff]
  by_cases h : g₁.count = 1
  · rw [if_pos h, h]; simp
  · rw [if_neg h]; exact h1

/-- 融合結果は正直（`Honest`）。 -/
theorem honest_Group_merge {g₁ g₂ : Group} (h : Mergeable g₁ g₂)
    (h1 : Honest g₁) (h2 : Honest g₂) : Honest (g₁.merge g₂) := by
  obtain ⟨hk, hk', _hlt, hcond, hdisj⟩ := h
  exact honest_merge_raw hk hk' hcond hdisj (honest_diff g₁ g₂ h1) h2

/-! ### `mergeAdj` の性質 -/

theorem mergeAdj_nil : mergeAdj [] = [] := by rw [mergeAdj]

theorem mergeAdj_singleton (g : Group) : mergeAdj [g] = [g] := by rw [mergeAdj]

theorem mergeAdj_cons_cons (g₁ g₂ : Group) (rest : List Group) :
    mergeAdj (g₁ :: g₂ :: rest) =
      if Mergeable g₁ g₂ then mergeAdj (g₁.merge g₂ :: rest)
      else g₁ :: mergeAdj (g₂ :: rest) := by
  rw [mergeAdj]

/-- **融合は展開を変えない**。 -/
theorem expandAll_mergeAdj : ∀ (gs : List Group), (∀ g ∈ gs, Honest g) →
    expandAll (mergeAdj gs) = expandAll gs := by
  intro gs
  induction gs using mergeAdj.induct with
  | case1 => intro _; rw [mergeAdj_nil]
  | case2 g => intro _; rw [mergeAdj_singleton]
  | case3 g₁ g₂ rest hm ih =>
      intro hh
      rw [mergeAdj_cons_cons, if_pos hm, ih ?_, expandAll_cons, expandAll_cons,
        expandAll_cons, expand_Group_merge hm, List.append_assoc]
      · intro g hg
        rcases List.mem_cons.mp hg with rfl | hg'
        · exact honest_Group_merge hm (hh _ (by simp)) (hh _ (by simp))
        · exact hh g (by simp [hg'])
  | case4 g₁ g₂ rest hm ih =>
      intro hh
      rw [mergeAdj_cons_cons, if_neg hm, expandAll_cons, expandAll_cons,
        ih (fun g hg => hh g (by simp [List.mem_cons.mp hg]))]

/-- 融合は正直さを保つ。 -/
theorem honest_mergeAdj : ∀ (gs : List Group), (∀ g ∈ gs, Honest g) →
    ∀ g ∈ mergeAdj gs, Honest g := by
  intro gs
  induction gs using mergeAdj.induct with
  | case1 => intro _ g hg; rw [mergeAdj_nil] at hg; cases hg
  | case2 g => intro hh g' hg'; rw [mergeAdj_singleton] at hg'; exact hh g' hg'
  | case3 g₁ g₂ rest hm ih =>
      intro hh g hg
      rw [mergeAdj_cons_cons, if_pos hm] at hg
      refine ih ?_ g hg
      intro g' hg'
      rcases List.mem_cons.mp hg' with rfl | hg''
      · exact honest_Group_merge hm (hh _ (by simp)) (hh _ (by simp))
      · exact hh g' (by simp [hg''])
  | case4 g₁ g₂ rest hm ih =>
      intro hh g hg
      rw [mergeAdj_cons_cons, if_neg hm] at hg
      rcases List.mem_cons.mp hg with rfl | hg'
      · exact hh g (by simp)
      · exact ih (fun g' hg' => hh g' (by simp [List.mem_cons.mp hg'])) g hg'

/-- 融合は `count ≥ 1` を保つ。 -/
theorem pos_mergeAdj : ∀ (gs : List Group), (∀ g ∈ gs, 1 ≤ g.count) →
    ∀ g ∈ mergeAdj gs, 1 ≤ g.count := by
  intro gs
  induction gs using mergeAdj.induct with
  | case1 => intro _ g hg; rw [mergeAdj_nil] at hg; cases hg
  | case2 g => intro hh g' hg'; rw [mergeAdj_singleton] at hg'; exact hh g' hg'
  | case3 g₁ g₂ rest hm ih =>
      intro hh g hg
      rw [mergeAdj_cons_cons, if_pos hm] at hg
      refine ih ?_ g hg
      intro g' hg'
      rcases List.mem_cons.mp hg' with rfl | hg''
      · have := hh g₁ (by simp)
        simp only [Group.merge] at *
        omega
      · exact hh g' (by simp [hg''])
  | case4 g₁ g₂ rest hm ih =>
      intro hh g hg
      rw [mergeAdj_cons_cons, if_neg hm] at hg
      rcases List.mem_cons.mp hg with rfl | hg'
      · exact hh g (by simp)
      · exact ih (fun g' hg' => hh g' (by simp [List.mem_cons.mp hg'])) g hg'

/-! ### 融合後の先頭の形 -/

/-- `mergeAdj (g :: rest)` の先頭は `g` と同じ公差・同じ先頭をもち、個数だけ増えている。 -/
theorem mergeAdj_head : ∀ (gs : List Group) (g : Group) (rest : List Group), gs = g :: rest →
    ∃ q k tl, mergeAdj gs = ⟨q, g.top, k⟩ :: tl ∧ g.count ≤ k ∧ (2 ≤ g.count → q = g.p) := by
  intro gs
  induction gs using mergeAdj.induct with
  | case1 => intro g rest h; cases h
  | case2 g' =>
      intro g rest h
      rw [List.cons.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact ⟨g'.p, g'.count, [], by rw [mergeAdj_singleton], Nat.le_refl _, fun _ => rfl⟩
  | case3 g₁ g₂ rest hm ih =>
      intro g rest' h
      rw [List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨q, k, tl, hk, hk', hq⟩ := ih (g₁.merge g₂) rest rfl
      refine ⟨q, k, tl, ?_, ?_, ?_⟩
      · rw [mergeAdj_cons_cons, if_pos hm]; exact hk
      · simp only [Group.merge] at hk'; omega
      · intro h2
        have hge : 2 ≤ (g₁.merge g₂).count := by
          simp only [Group.merge]
          have := hm.2.1
          omega
        rw [hq hge]
        simp only [Group.merge, Group.diff, if_neg (show ¬ g₁.count = 1 by omega)]
  | case4 g₁ g₂ rest hm ih =>
      intro g rest' h
      rw [List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨g₁.p, g₁.count, mergeAdj (g₂ :: rest), by rw [mergeAdj_cons_cons, if_neg hm],
        Nat.le_refl _, fun _ => rfl⟩

/-! ## 正準形 -/

/-- 群列が正準：各群が正直かつ非空で、隣接群がもう融合できない。 -/
def Canonical (gs : List Group) : Prop :=
  (∀ g ∈ gs, Honest g ∧ 1 ≤ g.count) ∧ gs.IsChain (fun g₁ g₂ => ¬ Mergeable g₁ g₂)

/-- **1 パスで正準形になる**。 -/
theorem canonical_mergeAdj : ∀ (gs : List Group), (∀ g ∈ gs, Honest g ∧ 1 ≤ g.count) →
    Canonical (mergeAdj gs) := by
  have hchain : ∀ (gs : List Group), (∀ g ∈ gs, Honest g ∧ 1 ≤ g.count) →
      (mergeAdj gs).IsChain (fun g₁ g₂ => ¬ Mergeable g₁ g₂) := by
    intro gs
    induction gs using mergeAdj.induct with
    | case1 => intro _; rw [mergeAdj_nil]; exact List.isChain_nil
    | case2 g => intro _; rw [mergeAdj_singleton]; exact List.isChain_singleton _
    | case3 g₁ g₂ rest hm ih =>
        intro hh
        rw [mergeAdj_cons_cons, if_pos hm]
        refine ih ?_
        intro g' hg'
        rcases List.mem_cons.mp hg' with rfl | hg''
        · refine ⟨honest_Group_merge hm (hh _ (by simp)).1 (hh _ (by simp)).1, ?_⟩
          have := (hh g₁ (by simp)).2
          simp only [Group.merge] at *
          omega
        · exact hh g' (by simp [hg''])
    | case4 g₁ g₂ rest hm ih =>
        intro hh
        rw [mergeAdj_cons_cons, if_neg hm]
        obtain ⟨q, k, tl, hk, hkc, hq⟩ := mergeAdj_head (g₂ :: rest) g₂ rest rfl
        rw [hk]
        refine List.isChain_cons.mpr ⟨?_, ?_⟩
        · intro y hy
          simp only [List.head?_cons, Option.mem_def] at hy
          injection hy with hy2
          subst hy2
          intro hmg
          obtain ⟨hc1, _hc2, hc3, hc4, hc5⟩ := hmg
          have hpos2 : 1 ≤ g₂.count := (hh g₂ (by simp)).2
          have hd : g₁.diff (⟨q, g₂.top, k⟩ : Group) = g₁.diff g₂ := by
            simp only [Group.diff]
          refine hm ⟨hc1, hpos2, hc3, by rw [← hd]; exact hc4, ?_⟩
          rcases hc5 with h | h
          · by_cases hc : g₂.count = 1
            · exact Or.inr hc
            · refine Or.inl ?_
              have hq2 : q = g₂.p := hq (by omega)
              rw [← hq2, ← hd]
              exact h
          · refine Or.inr ?_
            have hk1 : k = 1 := h
            omega
        · rw [← hk]
          exact ih (fun g hg => hh g (by simp [List.mem_cons.mp hg]))
  intro gs hh
  refine ⟨fun g hg => ⟨honest_mergeAdj gs (fun g' hg' => (hh g' hg').1) g hg,
    pos_mergeAdj gs (fun g' hg' => (hh g' hg').2) g hg⟩, hchain gs hh⟩

/-! ## 正準化つきの群鎖 -/

theorem pos_groupFilterOne (v : List (Fin 2)) (a : Fin 2) (g : Group) :
    ∀ g' ∈ groupFilterOne v a g, 1 ≤ g'.count := by
  obtain ⟨p, top, k⟩ := g
  intro g' hg'
  unfold groupFilterOne at hg'
  simp only at hg'
  split_ifs at hg' with h0 ht hr hr2 <;>
    simp only [List.mem_singleton, List.not_mem_nil] at hg' <;>
    subst_vars <;> simp only
  · omega
  · omega
  · omega

theorem honest_groupStep (v : List (Fin 2)) (gs : List Group) (a : Fin 2)
    (hh : ∀ g ∈ gs, Honest g) : ∀ g ∈ groupStep v gs a, Honest g := by
  intro g hg
  rw [groupStep, List.mem_append] at hg
  rcases hg with hg | hg
  · rw [List.mem_flatMap] at hg
    obtain ⟨g0, hg0, hg1⟩ := hg
    exact honest_groupFilterOne v a g0 (hh g0 hg0) g hg1
  · simp only [List.mem_singleton] at hg
    subst hg
    simp [Honest]

theorem pos_groupStep (v : List (Fin 2)) (gs : List Group) (a : Fin 2) :
    ∀ g ∈ groupStep v gs a, 1 ≤ g.count := by
  intro g hg
  rw [groupStep, List.mem_append] at hg
  rcases hg with hg | hg
  · rw [List.mem_flatMap] at hg
    obtain ⟨g0, hg0, hg1⟩ := hg
    exact pos_groupFilterOne v a g0 g hg1
  · simp only [List.mem_singleton] at hg
    subst hg
    decide

/-- 各ステップで隣接群を融合する群鎖（正準形）。 -/
def groupChainRevN : List (Fin 2) → List Group
  | [] => [⟨0, 0, 1⟩]
  | a :: v => mergeAdj (groupStep v (groupChainRevN v) a)

theorem groupChainRevN_spec (v : List (Fin 2)) :
    expandAll (groupChainRevN v) = chainRev v ∧
      (∀ g ∈ groupChainRevN v, Honest g ∧ 1 ≤ g.count) := by
  induction v with
  | nil =>
      refine ⟨by simp [groupChainRevN, expandAll, chainRev, Group.expand], ?_⟩
      intro g hg
      simp only [groupChainRevN, List.mem_singleton] at hg
      subst hg
      exact ⟨by simp [Honest], by decide⟩
  | cons a v ih =>
      obtain ⟨hexp, hprops⟩ := ih
      have hh : ∀ g ∈ groupChainRevN v, Honest g := fun g hg => (hprops g hg).1
      have hstep : expandAll (groupStep v (groupChainRevN v) a) = chainRev (a :: v) := by
        rw [expandAll_groupStep_of v _ a (ok_of_expandAll v _ hexp hh), hexp]
        rfl
      have hsh : ∀ g ∈ groupStep v (groupChainRevN v) a, Honest g :=
        honest_groupStep v _ a hh
      have hsp : ∀ g ∈ groupStep v (groupChainRevN v) a, 1 ≤ g.count :=
        pos_groupStep v _ a
      refine ⟨?_, ?_⟩
      · rw [groupChainRevN, expandAll_mergeAdj _ hsh, hstep]
      · intro g hg
        rw [groupChainRevN] at hg
        exact ⟨honest_mergeAdj _ hsh g hg, pos_mergeAdj _ hsp g hg⟩

/-- **主定理**。正準化つきの群鎖も展開すると本物の鎖になる。 -/
theorem expandAll_groupChainRevN (v : List (Fin 2)) :
    expandAll (groupChainRevN v) = chainRev v := (groupChainRevN_spec v).1

theorem honest_groupChainRevN (v : List (Fin 2)) : ∀ g ∈ groupChainRevN v, Honest g :=
  fun g hg => ((groupChainRevN_spec v).2 g hg).1

theorem pos_groupChainRevN (v : List (Fin 2)) : ∀ g ∈ groupChainRevN v, 1 ≤ g.count :=
  fun g hg => ((groupChainRevN_spec v).2 g hg).2

/-- **正準性**。`groupChainRevN` の出力は常に正準形。 -/
theorem canonical_groupChainRevN (v : List (Fin 2)) : Canonical (groupChainRevN v) := by
  cases v with
  | nil =>
      refine ⟨(groupChainRevN_spec []).2, ?_⟩
      rw [show groupChainRevN ([] : List (Fin 2)) = [⟨0, 0, 1⟩] from rfl]
      exact List.isChain_singleton _
  | cons a v =>
      rw [groupChainRevN]
      refine canonical_mergeAdj _ ?_
      intro g hg
      exact ⟨honest_groupStep v _ a (honest_groupChainRevN v) g hg,
        pos_groupStep v _ a g hg⟩

/-! ## 群境界での長さの縮小（Fine–Wilf） -/

/-- 鎖の要素 `ℓ` に対し `q ≤ ℓ` が `v.take ℓ` の周期なら、border の長さ `ℓ - q` も鎖の要素。 -/
theorem period_mem_chainRev (v : List (Fin 2)) {ℓ q : ℕ} (hℓ : ℓ ∈ chainRev v) (hq : q ≤ ℓ)
    (hper : HasPeriod (v.take ℓ) q) : ℓ - q ∈ chainRev v := by
  rw [mem_chainRev_iff] at hℓ ⊢
  obtain ⟨hn, hpal⟩ := hℓ
  have hlen : (v.take ℓ).length = ℓ := by rw [List.length_take]; omega
  refine ⟨by omega, ?_⟩
  have hb : (v.take ℓ).drop q = (v.take ℓ).take ((v.take ℓ).length - q) :=
    (hasPeriod_iff_drop_eq_take (by rw [hlen]; omega)).mp hper
  rw [hlen] at hb
  have hkey : (v.take ℓ).take (ℓ - q) = (v.take ℓ).drop ((v.take ℓ).length - (ℓ - q)) := by
    rw [hlen, show ℓ - (ℓ - q) = q from by omega]
    exact hb.symm
  have hres := (isPal_take_iff hpal (by rw [hlen]; omega)).mpr hkey
  rwa [List.take_take, show min (ℓ - q) ℓ = ℓ - q from by omega] at hres

/-- 鎖で `ℓ` の次が `ℓ'` なら、`ℓ - ℓ'` は `v.take ℓ` の**最小**周期。 -/
theorem minimal_period_of_consecutive (v : List (Fin 2)) {ℓ ℓ' : ℕ} (hℓ : ℓ ∈ chainRev v)
    (h1 : ℓ' < ℓ) (hgap : ∀ m ∈ chainRev v, m < ℓ → m ≤ ℓ') :
    ∀ q, 0 < q → q < ℓ - ℓ' → ¬ HasPeriod (v.take ℓ) q := by
  intro q hq0 hq hper
  have hmem := period_mem_chainRev v hℓ (by omega) hper
  have := hgap _ hmem (by omega)
  omega

/-- **境界縮小補題**。鎖の連続する 3 要素 `ℓ > ℓ' > ℓ''` について、
下側の差 `d' = ℓ' - ℓ''` が上側の差 `d = ℓ - ℓ'` より真に小さければ（＝群の境界）、
`3 * ℓ' < 2 * ℓ`（すなわち `ℓ' < (2/3) * ℓ`）。 -/
theorem boundary_shrink (v : List (Fin 2)) {ℓ ℓ' ℓ'' : ℕ}
    (hℓ : ℓ ∈ chainRev v) (hℓ' : ℓ' ∈ chainRev v) (hℓ'' : ℓ'' ∈ chainRev v)
    (h1 : ℓ' < ℓ) (h2 : ℓ'' < ℓ')
    (hgap1 : ∀ m ∈ chainRev v, m < ℓ → m ≤ ℓ')
    (_hgap2 : ∀ m ∈ chainRev v, m < ℓ' → m ≤ ℓ'')
    (hlt : ℓ' - ℓ'' < ℓ - ℓ') :
    3 * ℓ' < 2 * ℓ := by
  set d := ℓ - ℓ' with hd
  set d' := ℓ' - ℓ'' with hd'
  have hd0 : 0 < d := by omega
  have hd'0 : 0 < d' := by omega
  have hn : ℓ ≤ v.length := ((mem_chainRev_iff v ℓ).mp hℓ).1
  -- `d` は `v.take ℓ` の周期、`d'` は `v.take ℓ'` の周期
  have hxd : HasPeriod (v.take ℓ) d :=
    period_of_chain v (by omega) hℓ (by rw [show ℓ - d = ℓ' from by omega]; exact hℓ')
  have hx'd' : HasPeriod (v.take ℓ') d' :=
    period_of_chain v (by omega) hℓ' (by rw [show ℓ' - d' = ℓ'' from by omega]; exact hℓ'')
  have hmin := minimal_period_of_consecutive v hℓ h1 hgap1
  by_cases hcase : ℓ' < d
  · omega
  · rw [Nat.not_lt] at hcase
    -- `v.take ℓ'` は `d` も周期に持つ
    have htk : (v.take ℓ).take ℓ' = v.take ℓ' := by
      rw [List.take_take, show min ℓ' ℓ = ℓ' from by omega]
    have hx'd : HasPeriod (v.take ℓ') d := by
      rw [← htk]; exact hasPeriod_take hxd
    set g := Nat.gcd d d' with hg
    have hg0 : 0 < g := Nat.gcd_pos_of_pos_left d' hd0
    have hgd' : g ≤ d' := Nat.gcd_le_right _ hd'0
    have hgd : g ∣ d := Nat.gcd_dvd_left d d'
    have hFW : ℓ' < d + d' - g := by
      by_contra hcon
      rw [Nat.not_lt] at hcon
      have hlen' : (v.take ℓ').length = ℓ' := by rw [List.length_take]; omega
      have hgper : HasPeriod (v.take ℓ') g := by
        refine fineWilf hx'd hx'd' hd0 hd'0 ?_
        rw [hlen']; exact hcon
      -- 先頭 `d` 文字へ制限してから `v.take ℓ` 全体へ伝播
      have hpre : HasPeriod ((v.take ℓ).take d) g := by
        rw [List.take_take, show min d ℓ = d from by omega,
          show v.take d = (v.take ℓ').take d from by
            rw [List.take_take, show min d ℓ' = d from by omega]]
        exact hasPeriod_take hgper
      exact hmin g hg0 (by omega) (hasPeriod_of_prefix_dvd hxd hd0 hgd hpre)
    omega

/-- **差は下るほど広がらない**。鎖の連続 3 要素 `ℓ > ℓ' > ℓ''` では `ℓ' - ℓ'' ≤ ℓ - ℓ'`。
（`ℓ - ℓ'` は `v.take ℓ'` の周期でもあるので、最小周期 `ℓ' - ℓ''` はそれ以下。） -/
theorem gap_antitone (v : List (Fin 2)) {ℓ ℓ' ℓ'' : ℕ}
    (hℓ : ℓ ∈ chainRev v) (hℓ' : ℓ' ∈ chainRev v)
    (h1 : ℓ' < ℓ) (h2 : ℓ'' < ℓ')
    (hgap2 : ∀ m ∈ chainRev v, m < ℓ' → m ≤ ℓ'') :
    ℓ' - ℓ'' ≤ ℓ - ℓ' := by
  set d := ℓ - ℓ' with hd
  by_cases hcase : ℓ' < d
  · omega
  · rw [Nat.not_lt] at hcase
    have hxd : HasPeriod (v.take ℓ) d :=
      period_of_chain v (by omega) hℓ (by rw [show ℓ - d = ℓ' from by omega]; exact hℓ')
    have htk : (v.take ℓ).take ℓ' = v.take ℓ' := by
      rw [List.take_take, show min ℓ' ℓ = ℓ' from by omega]
    have hx'd : HasPeriod (v.take ℓ') d := by rw [← htk]; exact hasPeriod_take hxd
    have hmem := period_mem_chainRev v hℓ' hcase hx'd
    have := hgap2 _ hmem (by omega)
    omega

/-! ## 縮小列の長さの対数上界 -/

/-- 2 歩で半分以下になる：`3b < 2a`, `3c < 2b` ならば `2c < a`。 -/
theorem two_step_halving {a b c : ℕ} (h1 : 3 * b < 2 * a) (h2 : 3 * c < 2 * b) : 2 * c < a := by
  omega

/-- 各項が直前の項の `2/3` 未満であるような自然数列の長さは、
先頭が `2 ^ m` 未満なら `2 * m + 2` 以下。 -/
theorem length_le_of_shrink : ∀ (m : ℕ) (ts : List ℕ),
    ts.IsChain (fun a b => 3 * b < 2 * a) → (∀ t ∈ ts.head?, t < 2 ^ m) →
    ts.length ≤ 2 * m + 2 := by
  intro m
  induction m with
  | zero =>
      intro ts hchain hhead
      match ts, hchain with
      | [], _ => simp
      | [_], _ => simp only [List.length_cons, List.length_nil]; omega
      | (a :: b :: rest), (.cons_cons hR _) =>
          have ha : a < 2 ^ 0 := hhead a (by simp)
          simp only [pow_zero] at ha
          have hR' : 3 * b < 2 * a := hR
          omega
  | succ m ih =>
      intro ts hchain hhead
      match ts, hchain with
      | [], _ => simp
      | [_], _ => simp only [List.length_cons, List.length_nil]; omega
      | [_, _], _ => simp only [List.length_cons, List.length_nil]; omega
      | (a :: b :: c :: rest), (.cons_cons hR (.cons_cons hR' htail)) =>
          have ha : a < 2 ^ (m + 1) := hhead a (by simp)
          have hc : c < 2 ^ m := by
            have h2c := two_step_halving hR hR'
            rw [pow_succ] at ha
            omega
          have hrest : (c :: rest).length ≤ 2 * m + 2 := by
            refine ih (c :: rest) htail ?_
            intro t ht
            simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at ht
            subst ht
            exact hc
          simp only [List.length_cons] at hrest ⊢
          omega

/-- 上と同じことを `Nat.log` の形で述べたもの。全項が `n` 以下なら長さは
`2 * Nat.log 2 n + 4` 以下。 -/
theorem length_le_log_of_shrink (ts : List ℕ) (n : ℕ)
    (hchain : ts.IsChain (fun a b => 3 * b < 2 * a)) (hn : ∀ t ∈ ts.head?, t ≤ n) :
    ts.length ≤ 2 * Nat.log 2 n + 4 := by
  have := length_le_of_shrink (Nat.log 2 n + 1) ts hchain (fun t ht =>
    lt_of_le_of_lt (hn t ht) (Nat.lt_pow_succ_log_self (by omega) n))
  omega

/-! ## 群数の対数上界 -/

theorem mem_expandAll_of_mem {gs : List Group} {g : Group} (hg : g ∈ gs) {x : ℕ}
    (hx : x ∈ g.expand) : x ∈ expandAll gs :=
  List.mem_flatMap.mpr ⟨g, hg, hx⟩

/-- 正準群鎖の各群の先頭は鎖の要素。 -/
theorem top_mem_chainRev (v : List (Fin 2)) {g : Group} (hg : g ∈ groupChainRevN v) :
    g.top ∈ chainRev v := by
  rw [← expandAll_groupChainRevN v]
  refine mem_expandAll_of_mem hg ?_
  have hc : 1 ≤ g.count := pos_groupChainRevN v g hg
  simp only [Group.expand, List.mem_map, List.mem_range]
  exact ⟨0, by omega, by simp⟩

/-- **群数の対数上界（境界縮小を仮定した形）**。
群の先頭が境界ごとに `2/3` 未満へ縮むならば、群数は `2 * log₂ |v| + 4` 以下。

境界縮小 `htops` は `boundary_shrink` と `gap_antitone` から従うはずのものだが、
「正準群列の隣接群から鎖の連続 3 要素を取り出す」補題（`expandAll` と
`chainRev` のソート性に関する list 手術）はまだ形式化していない。 -/
theorem groupCount_le_of_tops_shrink (v : List (Fin 2))
    (htops : ((groupChainRevN v).map Group.top).IsChain (fun a b => 3 * b < 2 * a)) :
    (groupChainRevN v).length ≤ 2 * Nat.log 2 v.length + 4 := by
  have hlen : ((groupChainRevN v).map Group.top).length = (groupChainRevN v).length :=
    List.length_map ..
  rw [← hlen]
  refine length_le_log_of_shrink _ v.length htops ?_
  intro t ht
  rw [List.head?_map] at ht
  simp only [Option.mem_def, Option.map_eq_some_iff] at ht
  obtain ⟨g, hg, rfl⟩ := ht
  have hmem : g ∈ groupChainRevN v := List.mem_of_mem_head? hg
  exact ((mem_chainRev_iff v g.top).mp (top_mem_chainRev v hmem)).1

/-! ### 健全性チェック -/

example : groupChainRev [0, 0, 0, 0] = [⟨1, 4, 1⟩, ⟨1, 3, 2⟩, ⟨1, 1, 2⟩] := by decide

/-- 正準化により 3 つの群が 1 つの等差数列にまとまる
（`mergeAdj` は整礎再帰なので `decide` では簡約されない。等式補題で計算する）。 -/
example : mergeAdj [⟨1, 4, 1⟩, ⟨1, 3, 2⟩, ⟨1, 1, 2⟩] = [⟨1, 4, 5⟩] := by
  rw [mergeAdj_cons_cons, if_pos (by decide : Mergeable ⟨1, 4, 1⟩ ⟨1, 3, 2⟩),
    show Group.merge ⟨1, 4, 1⟩ ⟨1, 3, 2⟩ = ⟨1, 4, 3⟩ from rfl,
    mergeAdj_cons_cons, if_pos (by decide : Mergeable ⟨1, 4, 3⟩ ⟨1, 1, 2⟩),
    show Group.merge ⟨1, 4, 3⟩ ⟨1, 1, 2⟩ = ⟨1, 4, 5⟩ from rfl, mergeAdj_singleton]

example : expandAll [(⟨1, 4, 5⟩ : Group)] = [4, 3, 2, 1, 0] := by decide

/-- 実効公差の効果。履歴由来の `p = 1` を持つ単項群 2 つが、
本当の公差 `2` の等差数列として融合される（`chainRev = [5,3,1,0]` の場合）。 -/
example : mergeAdj [⟨1, 5, 1⟩, ⟨1, 3, 1⟩, ⟨1, 1, 2⟩] = [⟨2, 5, 2⟩, ⟨1, 1, 2⟩] := by
  rw [mergeAdj_cons_cons, if_pos (by decide : Mergeable ⟨1, 5, 1⟩ ⟨1, 3, 1⟩),
    show Group.merge ⟨1, 5, 1⟩ ⟨1, 3, 1⟩ = ⟨2, 5, 2⟩ from rfl,
    mergeAdj_cons_cons, if_neg (by decide : ¬ Mergeable ⟨2, 5, 2⟩ ⟨1, 1, 2⟩),
    mergeAdj_singleton]

example : Canonical [(⟨1, 4, 5⟩ : Group)] := by
  refine ⟨?_, List.isChain_singleton _⟩
  intro g hg
  simp only [List.mem_singleton] at hg
  subst hg
  exact ⟨by simp [Honest], by decide⟩

end PalPeg

