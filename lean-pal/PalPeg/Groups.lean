import PalPeg.Chain
import PalPeg.Structure

/-!
# 鎖の群圧縮 (group-compressed representation of the suffix-palindrome chain)

接尾辞回文長の鎖 `chainRev v` は狭義降順の自然数リストだが、周期性のおかげで
**等差数列の並び（群 / group）** に分解できる。本ファイルでは

* `Group` … 等差数列 `top, top - p, …, top - (count-1) * p` の表現
* `compress` … 狭義降順リストを群列へ圧縮（`expandAll_compress`）
* `groupFilterOne` … 群ごとに **記号参照 2 回だけ** で `chainStep` のフィルタを実行
* `groupStep`, `groupChainRev` … 群表現のままのオンライン更新

を定義し、`expandAll (groupChainRev v) = chainRev v` を証明する。

鍵となるのは `group_members_same_symbol`：群の各要素は「回文接頭辞の長さ」であり、
`top` と `top - p` がともに鎖にあることから `v.take top` が周期 `p` を持つ
（`hasPeriod_of_pal_suffix_pal`）。したがって群内部の記号は 1 箇所を見れば全部わかる。
-/

namespace PalPeg

/-! ## 群の定義 -/

/-- 等差数列 `top, top - p, …, top - (count-1) * p` を表す群。 -/
structure Group where
  p : ℕ
  top : ℕ
  count : ℕ
deriving DecidableEq, Repr

/-- 群を実際の長さリストへ展開する。 -/
def Group.expand (g : Group) : List ℕ :=
  (List.range g.count).map (fun i => g.top - i * g.p)

/-- 群列の展開。 -/
def expandAll (gs : List Group) : List ℕ := gs.flatMap Group.expand

/-- 群が「正直」＝ 末尾要素まで自然数の引き算が切り詰められていない。 -/
def Honest (g : Group) : Prop := (g.count - 1) * g.p ≤ g.top

@[simp] theorem expandAll_nil : expandAll [] = [] := rfl

@[simp] theorem expandAll_cons (g : Group) (gs : List Group) :
    expandAll (g :: gs) = g.expand ++ expandAll gs := rfl

theorem expandAll_append (gs hs : List Group) :
    expandAll (gs ++ hs) = expandAll gs ++ expandAll hs := by
  simp [expandAll, List.flatMap_append]

@[simp] theorem expand_zero (p top : ℕ) : Group.expand ⟨p, top, 0⟩ = [] := rfl

@[simp] theorem expand_one (p top : ℕ) : Group.expand ⟨p, top, 1⟩ = [top] := by
  simp [Group.expand]

/-- 群の先頭を剥がす。自然数の引き算でも無条件に成立。 -/
theorem expand_succ (p top k : ℕ) :
    Group.expand ⟨p, top, k + 1⟩ = top :: Group.expand ⟨p, top - p, k⟩ := by
  simp only [Group.expand, List.range_succ_eq_map, List.map_cons, List.map_map,
    Nat.zero_mul, Nat.sub_zero]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply]
  rw [Nat.succ_mul, Nat.sub_add_eq, Nat.sub_right_comm]

/-- 群の末尾に 1 要素足す。 -/
theorem expand_succ_right (p top k : ℕ) :
    Group.expand ⟨p, top, k + 1⟩ = Group.expand ⟨p, top, k⟩ ++ [top - k * p] := by
  simp [Group.expand, List.range_succ]

/-- 正直な群は、定数を足しても展開が平行移動になる。 -/
theorem expand_add_const (p top k c : ℕ) (h : (k - 1) * p ≤ top) :
    Group.expand ⟨p, top + c, k⟩ = (Group.expand ⟨p, top, k⟩).map (· + c) := by
  simp only [Group.expand, List.map_map]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have hle : i * p ≤ (k - 1) * p := Nat.mul_le_mul_right p (by omega)
  simp only [Function.comp_apply]
  omega

/-! ## 圧縮 -/

/-- 圧縮の補助。状態は `(現在の群の公差, 先頭, 個数, 直前に取り込んだ要素)`。 -/
def compressAux : List ℕ → ℕ × ℕ × ℕ × ℕ → List Group
  | [], (p, top, count, _) => [⟨p, top, count⟩]
  | y :: rest, (p, top, count, last) =>
      if count = 1 then compressAux rest (last - y, top, 2, y)
      else if last - y = p then compressAux rest (p, top, count + 1, y)
      else ⟨p, top, count⟩ :: compressAux rest (0, y, 1, y)

/-- 狭義降順リストを群列へ圧縮する。差分の極大な等差ランを 1 群にまとめる貪欲法。
末尾の群は `count = 1` になりうる（`p` は `0` を採る規約）。 -/
def compress : List ℕ → List Group
  | [] => []
  | x :: rest => compressAux rest (0, x, 1, x)

theorem expandAll_compressAux :
    ∀ (rest : List ℕ) (p top count last : ℕ), 1 ≤ count →
      top = last + (count - 1) * p → (last :: rest).Pairwise (· > ·) →
      expandAll (compressAux rest (p, top, count, last))
        = Group.expand ⟨p, top, count⟩ ++ rest := by
  intro rest
  induction rest with
  | nil =>
      intro p top count last _ _ _
      simp [compressAux, expandAll]
  | cons y rest ih =>
      intro p top count last hc htop hpair
      have hlt : last > y := (List.pairwise_cons.mp hpair).1 y (List.mem_cons_self ..)
      have hpair' : (y :: rest).Pairwise (· > ·) := (List.pairwise_cons.mp hpair).2
      by_cases h1 : count = 1
      · subst h1
        have htop' : top = last := by simpa using htop
        rw [compressAux, if_pos rfl]
        rw [ih (last - y) top 2 y (by omega) (by omega) hpair']
        have hval : Group.expand ⟨last - y, top, 2⟩ = [top, y] := by
          rw [show (2 : ℕ) = 1 + 1 from rfl, expand_succ, expand_one,
            show top - (last - y) = y from by omega]
        rw [hval, expand_one]
        rfl
      · rw [compressAux, if_neg h1]
        by_cases h2 : last - y = p
        · rw [if_pos h2]
          have hlast : last = y + p := by omega
          have htop' : top = y + count * p := by
            rw [htop, hlast]
            cases count with
            | zero => omega
            | succ n =>
                simp only [Nat.add_sub_cancel, Nat.succ_mul]
                omega
          rw [ih p top (count + 1) y (by omega) (by simpa using htop') hpair']
          rw [expand_succ_right, List.append_assoc,
            show top - count * p = y from by omega]
          rfl
        · rw [if_neg h2]
          rw [expandAll_cons, ih 0 y 1 y (by omega) (by simp) hpair']
          simp

theorem honest_compressAux :
    ∀ (rest : List ℕ) (p top count last : ℕ), 1 ≤ count →
      top = last + (count - 1) * p → (last :: rest).Pairwise (· > ·) →
      ∀ g ∈ compressAux rest (p, top, count, last), Honest g := by
  intro rest
  induction rest with
  | nil =>
      intro p top count last _ htop _ g hg
      simp only [compressAux, List.mem_singleton] at hg
      subst hg
      simp only [Honest]
      omega
  | cons y rest ih =>
      intro p top count last hc htop hpair g hg
      have hlt : last > y := (List.pairwise_cons.mp hpair).1 y (List.mem_cons_self ..)
      have hpair' : (y :: rest).Pairwise (· > ·) := (List.pairwise_cons.mp hpair).2
      by_cases h1 : count = 1
      · subst h1
        rw [compressAux, if_pos rfl] at hg
        exact ih (last - y) top 2 y (by omega) (by omega) hpair' g hg
      · rw [compressAux, if_neg h1] at hg
        by_cases h2 : last - y = p
        · rw [if_pos h2] at hg
          have hlast : last = y + p := by omega
          have htop' : top = y + count * p := by
            rw [htop, hlast]
            cases count with
            | zero => omega
            | succ n =>
                simp only [Nat.add_sub_cancel, Nat.succ_mul]
                omega
          exact ih p top (count + 1) y (by omega) (by simpa using htop') hpair' g hg
        · rw [if_neg h2] at hg
          rcases List.mem_cons.mp hg with rfl | hg'
          · simp only [Honest]; omega
          · exact ih 0 y 1 y (by omega) (by simp) hpair' g hg'

/-- **圧縮の正当性**。狭義降順リストは圧縮しても展開で元に戻る。 -/
theorem expandAll_compress (l : List ℕ) (hl : l.Pairwise (· > ·)) :
    expandAll (compress l) = l := by
  cases l with
  | nil => rfl
  | cons x rest =>
      rw [compress, expandAll_compressAux rest 0 x 1 x (by omega) (by simp) hl]
      simp

theorem honest_compress (l : List ℕ) (hl : l.Pairwise (· > ·)) :
    ∀ g ∈ compress l, Honest g := by
  cases l with
  | nil => intro g hg; cases hg
  | cons x rest => exact honest_compressAux rest 0 x 1 x (by omega) (by simp) hl

/-! ## 群内部の記号は 1 箇所で決まる（周期性） -/

/-- `top` と `top - p` がともに鎖にあれば、`v.take top` は周期 `p` を持つ。 -/
theorem period_of_chain (v : List (Fin 2)) {top p : ℕ} (hp : p ≤ top)
    (h1 : top ∈ chainRev v) (h2 : top - p ∈ chainRev v) :
    HasPeriod (v.take top) p := by
  rw [mem_chainRev_iff] at h1 h2
  obtain ⟨h1n, h1p⟩ := h1
  obtain ⟨_, h2p⟩ := h2
  have hxlen : (v.take top).length = top := by rw [List.length_take]; omega
  have hk : top - p ≤ (v.take top).length := by omega
  have hz : IsPal ((v.take top).drop ((v.take top).length - (top - p))) := by
    rw [isPal_drop_iff h1p hk, ← isPal_take_iff h1p hk]
    have he : (v.take top).take (top - p) = v.take (top - p) := by
      rw [List.take_take]; congr 1; omega
    rw [he]; exact h2p
  have hres := hasPeriod_of_pal_suffix_pal h1p hk hz
  rwa [hxlen, show top - (top - p) = p from by omega] at hres

/-- 周期 `p` の回文接頭辞では、`top - i*p` 番目の記号は `top - p` 番目と同じ。 -/
theorem getElem?_shift (v : List (Fin 2)) {top p : ℕ} (hp : 1 ≤ p) (htn : top ≤ v.length)
    (hper : HasPeriod (v.take top) p) :
    ∀ i, 1 ≤ i → i * p ≤ top → v[top - i * p]? = v[top - p]? := by
  have hlen : (v.take top).length = top := by rw [List.length_take]; omega
  have hget : ∀ j, j < top → (v.take top)[j]? = v[j]? := by
    intro j hj; exact List.getElem?_take_of_lt hj
  have main : ∀ i, 1 ≤ i → i * p ≤ top →
      (v.take top)[top - i * p]? = (v.take top)[top - p]? := by
    intro i
    induction i with
    | zero => intro h _; omega
    | succ i ih =>
        intro _ hle
        rcases Nat.eq_zero_or_pos i with hi0 | hi0
        · subst hi0; simp
        · have hmul : i * p + p = (i + 1) * p := by rw [Nat.succ_mul]
          have hipos : 0 < i * p := Nat.mul_pos hi0 (by omega)
          have hile : i * p ≤ top := by omega
          have hstep : (v.take top)[top - (i + 1) * p]?
              = (v.take top)[top - (i + 1) * p + p]? := by
            refine hper _ ?_
            rw [hlen]; omega
          rw [hstep, show top - (i + 1) * p + p = top - i * p from by omega]
          exact ih (by omega) hile
  intro i hi hle
  have hppos : 0 < i * p := Nat.mul_pos (by omega) (by omega)
  have hple : p ≤ i * p := Nat.le_mul_of_pos_left p (by omega)
  rw [← hget _ (by omega), ← hget _ (by omega)]
  exact main i hi hle

/-! ## 群単位のフィルタ -/

/-- 群 `g` が語 `v` に対して整合的：正直であり、かつ群内部の記号が `top - p` 位置と一致する。 -/
def Group.Ok (v : List (Fin 2)) (g : Group) : Prop :=
  Honest g ∧ ∀ i, 1 ≤ i → i < g.count → v[g.top - i * g.p]? = v[g.top - g.p]?

/-- **群要素の記号一致補題**。展開が全て鎖の要素なら、群は整合的。
すなわち群の内部要素の記号は `v[top - p]?` 1 箇所を見れば全部わかる。 -/
theorem group_members_same_symbol (v : List (Fin 2)) (g : Group) (hh : Honest g)
    (hmem : ∀ x ∈ g.expand, x ∈ chainRev v) : Group.Ok v g := by
  obtain ⟨p, top, k⟩ := g
  refine ⟨hh, ?_⟩
  simp only [Honest] at hh
  simp only
  intro i hi hik
  rcases Nat.eq_zero_or_pos p with hp0 | hp
  · subst hp0; simp
  · have hpk : p ≤ top := le_trans (Nat.le_mul_of_pos_left p (by omega)) hh
    have hmem0 : top ∈ chainRev v := by
      refine hmem _ ?_
      simp only [Group.expand, List.mem_map, List.mem_range]
      exact ⟨0, by omega, by simp⟩
    have hmem1 : top - p ∈ chainRev v := by
      refine hmem _ ?_
      simp only [Group.expand, List.mem_map, List.mem_range]
      exact ⟨1, by omega, by simp⟩
    have htn : top ≤ v.length := ((mem_chainRev_iff v top).mp hmem0).1
    have hper := period_of_chain v hpk hmem0 hmem1
    have hile : i * p ≤ top := le_trans (Nat.mul_le_mul_right p (by omega)) hh
    exact getElem?_shift v hp htn hper i hi hile

/-- **群単位のフィルタ**。記号参照はちょうど 2 回（`v[top]?` と `v[top - p]?`）で、
群の大きさ `count` に依らず O(1) 時間。群を要素へ展開しない。 -/
def groupFilterOne (v : List (Fin 2)) (a : Fin 2) (g : Group) : List Group :=
  if g.count = 0 then []
  else if v[g.top]? = some a then
    (if 2 ≤ g.count ∧ v[g.top - g.p]? = some a then [⟨g.p, g.top + 2, g.count⟩]
     else [⟨g.p, g.top + 2, 1⟩])
  else
    (if 2 ≤ g.count ∧ v[g.top - g.p]? = some a then
      [⟨g.p, g.top - g.p + 2, g.count - 1⟩] else [])

theorem honest_groupFilterOne (v : List (Fin 2)) (a : Fin 2) (g : Group) (hh : Honest g) :
    ∀ g' ∈ groupFilterOne v a g, Honest g' := by
  obtain ⟨p, top, k⟩ := g
  simp only [Honest] at hh
  intro g' hg'
  unfold groupFilterOne at hg'
  simp only at hg'
  split_ifs at hg' with h0 ht hr hr2 <;>
    simp only [List.mem_singleton, List.not_mem_nil] at hg' <;>
    subst_vars <;> simp only [Honest]
  · omega
  · simp
  · obtain ⟨hk2, _⟩ := hr2
    have hk : k - 1 = (k - 2) + 1 := by omega
    rw [hk, Nat.succ_mul] at hh
    rw [show k - 1 - 1 = k - 2 from by omega]
    omega

/-- **2 回参照フィルタ = 要素ごとフィルタ**。 -/
theorem expandAll_groupFilterOne (v : List (Fin 2)) (a : Fin 2) (g : Group)
    (hg : Group.Ok v g) :
    expandAll (groupFilterOne v a g)
      = ((Group.expand g).filter (fun l => decide (v[l]? = some a))).map (· + 2) := by
  obtain ⟨p, top, k⟩ := g
  obtain ⟨hhon, hper⟩ := hg
  simp only [Honest] at hhon
  simp only at hper
  match k with
  | 0 => simp [groupFilterOne, Group.expand]
  | 1 =>
      by_cases h : v[top]? = some a <;>
        simp [groupFilterOne, h, expandAll]
  | (m + 2) =>
      have hexp : Group.expand ⟨p, top, m + 2⟩ = top :: Group.expand ⟨p, top - p, m + 1⟩ :=
        expand_succ p top (m + 1)
      have hT : ∀ x ∈ Group.expand ⟨p, top - p, m + 1⟩, v[x]? = v[top - p]? := by
        intro x hx
        simp only [Group.expand, List.mem_map, List.mem_range] at hx
        obtain ⟨i, hi, rfl⟩ := hx
        have hrw : top - p - i * p = top - (i + 1) * p := by
          rw [Nat.succ_mul]; omega
        rw [hrw]
        exact hper (i + 1) (by omega) (by omega)
      have htail : (Group.expand ⟨p, top - p, m + 1⟩).filter
            (fun l => decide (v[l]? = some a))
          = if v[top - p]? = some a then Group.expand ⟨p, top - p, m + 1⟩ else [] := by
        by_cases hr : v[top - p]? = some a
        · rw [if_pos hr]
          refine List.filter_eq_self.mpr ?_
          intro x hx
          simp only [decide_eq_true_eq]
          rw [hT x hx]; exact hr
        · rw [if_neg hr]
          refine List.filter_eq_nil_iff.mpr ?_
          intro x hx
          simp only [decide_eq_true_eq]
          rw [hT x hx]; exact hr
      have hhon' : (m + 1) * p ≤ top := by simpa using hhon
      have hmp : m * p ≤ top - p := by
        rw [Nat.succ_mul] at hhon'
        omega
      by_cases ht : v[top]? = some a
      · by_cases hr : v[top - p]? = some a
        · rw [show groupFilterOne v a ⟨p, top, m + 2⟩ = [⟨p, top + 2, m + 2⟩] from by
            simp [groupFilterOne, ht, hr]]
          rw [hexp, List.filter_cons_of_pos (by simp [ht]), htail, if_pos hr, ← hexp]
          simp only [expandAll_cons, expandAll_nil, List.append_nil]
          exact expand_add_const p top (m + 2) 2 (by simpa using hhon)
        · rw [show groupFilterOne v a ⟨p, top, m + 2⟩ = [⟨p, top + 2, 1⟩] from by
            simp [groupFilterOne, ht, hr]]
          rw [hexp, List.filter_cons_of_pos (by simp [ht]), htail, if_neg hr]
          simp
      · by_cases hr : v[top - p]? = some a
        · rw [show groupFilterOne v a ⟨p, top, m + 2⟩ = [⟨p, top - p + 2, m + 1⟩] from by
            simp [groupFilterOne, ht, hr]]
          rw [hexp, List.filter_cons_of_neg (by simp [ht]), htail, if_pos hr]
          simp only [expandAll_cons, expandAll_nil, List.append_nil]
          exact expand_add_const p (top - p) (m + 1) 2 (by simpa using hmp)
        · rw [show groupFilterOne v a ⟨p, top, m + 2⟩ = [] from by
            simp [groupFilterOne, ht, hr]]
          rw [hexp, List.filter_cons_of_neg (by simp [ht]), htail, if_neg hr]
          simp

/-! ## 群単位のステップ -/

/-- 群表現のままの 1 ステップ。各群につき記号参照は 2 回だけ。 -/
def groupStep (v : List (Fin 2)) (gs : List Group) (a : Fin 2) : List Group :=
  gs.flatMap (groupFilterOne v a) ++ [⟨1, 1, 2⟩]

theorem expandAll_flatMap_groupFilterOne (v : List (Fin 2)) (a : Fin 2) (gs : List Group)
    (hok : ∀ g ∈ gs, Group.Ok v g) :
    expandAll (gs.flatMap (groupFilterOne v a))
      = ((expandAll gs).filter (fun l => decide (v[l]? = some a))).map (· + 2) := by
  induction gs with
  | nil => simp [expandAll]
  | cons g gs ih =>
      rw [List.flatMap_cons, expandAll_append,
        expandAll_groupFilterOne v a g (hok g (List.mem_cons_self ..)),
        ih (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))]
      simp [expandAll, List.filter_append]

/-- **主定理 (1 ステップ・一般形)**。群表現のステップは `chainStep` と可換。 -/
theorem expandAll_groupStep_of (v : List (Fin 2)) (gs : List Group) (a : Fin 2)
    (hok : ∀ g ∈ gs, Group.Ok v g) :
    expandAll (groupStep v gs a) = chainStep v (expandAll gs) a := by
  rw [groupStep, expandAll_append, expandAll_flatMap_groupFilterOne v a gs hok, chainStep]
  congr 1

theorem ok_of_expandAll (v : List (Fin 2)) (gs : List Group)
    (hexp : expandAll gs = chainRev v) (hh : ∀ g ∈ gs, Honest g) :
    ∀ g ∈ gs, Group.Ok v g := by
  intro g hg
  refine group_members_same_symbol v g (hh g hg) ?_
  intro x hx
  rw [← hexp]
  have hsub : (Group.expand g).Sublist (expandAll gs) := by
    clear hx hexp hh
    induction gs with
    | nil => cases hg
    | cons h t ih =>
        rw [expandAll_cons]
        rcases List.mem_cons.mp hg with rfl | hg'
        · exact List.sublist_append_left _ _
        · exact (ih hg').trans (List.sublist_append_right _ _)
  exact hsub.subset hx

/-- **主定理 (1 ステップ・圧縮形)**。 -/
theorem expandAll_groupStep (v : List (Fin 2)) (a : Fin 2) :
    expandAll (groupStep v (compress (chainRev v)) a) = chainRev (a :: v) := by
  have hexp : expandAll (compress (chainRev v)) = chainRev v :=
    expandAll_compress _ (chainRev_pairwise_gt v)
  have hh : ∀ g ∈ compress (chainRev v), Honest g :=
    honest_compress _ (chainRev_pairwise_gt v)
  rw [expandAll_groupStep_of v _ a (ok_of_expandAll v _ hexp hh), hexp]
  rfl

/-! ## 群表現の鎖 -/

/-- 群表現のまま鎖を構成する（構造的再帰）。 -/
def groupChainRev : List (Fin 2) → List Group
  | [] => [⟨0, 0, 1⟩]
  | a :: v => groupStep v (groupChainRev v) a

theorem groupChainRev_spec (v : List (Fin 2)) :
    expandAll (groupChainRev v) = chainRev v ∧ ∀ g ∈ groupChainRev v, Honest g := by
  induction v with
  | nil =>
      refine ⟨by simp [groupChainRev, expandAll, chainRev, Group.expand], ?_⟩
      intro g hg
      simp only [groupChainRev, List.mem_singleton] at hg
      subst hg
      simp [Honest]
  | cons a v ih =>
      obtain ⟨hexp, hh⟩ := ih
      refine ⟨?_, ?_⟩
      · rw [groupChainRev, expandAll_groupStep_of v _ a (ok_of_expandAll v _ hexp hh), hexp]
        rfl
      · intro g hg
        rw [groupChainRev, groupStep, List.mem_append] at hg
        rcases hg with hg | hg
        · rw [List.mem_flatMap] at hg
          obtain ⟨g0, hg0, hg1⟩ := hg
          exact honest_groupFilterOne v a g0 (hh g0 hg0) g hg1
        · simp only [List.mem_singleton] at hg
          subst hg
          simp [Honest]

/-- **主定理**。群表現の鎖は展開すると本物の鎖になる。 -/
theorem expandAll_groupChainRev (v : List (Fin 2)) :
    expandAll (groupChainRev v) = chainRev v := (groupChainRev_spec v).1

theorem honest_groupChainRev (v : List (Fin 2)) : ∀ g ∈ groupChainRev v, Honest g :=
  (groupChainRev_spec v).2

/-! ## 健全性チェック -/

example : groupChainRev ([] : List (Fin 2)) = [⟨0, 0, 1⟩] := by decide
example : groupChainRev [0, 0, 0, 0] = [⟨1, 4, 1⟩, ⟨1, 3, 2⟩, ⟨1, 1, 2⟩] := by decide
example : expandAll (groupChainRev [0, 0, 0, 0]) = [4, 3, 2, 1, 0] := by decide
example : compress [6, 3, 1, 0] = [⟨3, 6, 2⟩, ⟨1, 1, 2⟩] := by decide
example : expandAll (compress (chain [0, 1, 0, 0, 1, 0])) = [6, 3, 1, 0] := by decide

end PalPeg
