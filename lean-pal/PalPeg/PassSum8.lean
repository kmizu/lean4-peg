import PalPeg.PassSum7

/-!
# 1 パスの周期和：木構造による `Σ ≤ 2 * max` の還元（PassSum8）

`PassSum7` は残る課題を

```
∀ x b s, stripLoop2Periods x 8 b (|x|+1) s ≤ 2 * stripLoop2MaxPeriod x 8 b (|x|+1) s
```

というスケール不変な形に還元し、同時に **`PassSum` の二分律（隣接 2 項の関係）だけでは
決して閉じない**ことを証明した（`dichotomy_insufficient`）。本ファイルはその指摘に従い、
**木（再帰）による議論**を実装する。

## 数値実験で確認した 1 パスの木構造（`k = 8`）

1 パスの反復列 `(aⱼ, pⱼ, Eⱼ)`（開始位置・周期・極大 run の右端）に対し、
「`i` の親 = `Eᵢ ≤ E_c` を満たす直近の先行反復 `c`」で森を作る。数千語の乱択実験
（入れ子周期語・その連接・接尾辞開始）で次がすべて **例外なし** に成立した：

* **(T1) 木＝二分律**：`j+1` が `j` の子 ⟺ `(k-1) * p_{j+1} < p_j`（DOWN ステップ）。
  すなわち木は周期列と `PassSum.step_dichotomy` だけから決まる。
* **(T2) 末子の上界**：`c` の最後の子 `q_m` は `(k-1) * q_m < p_c`。
* **(T3) 兄弟の成長**：同じ親の連続する子 `q_i, q_{i+1}` は `q_{i+1} ≥ (k-1) * q_i`
  （根の列についても同様）。実測の最小比は `7.33`（兄弟）・`7.75`（根）。

`PassSum4.children_growth_of_next` が現在証明しているのは (T3) の弱い版
`(k-2) * q_i ≤ (k-1) * q_{i+1}`（＝ `q_{i+1} > (6/7) * q_i`）であり、比が `1` 未満なので
等比和が発散し、そのままでは使えない。**本ファイルの計算が示すのは、成長率 `γ` が
`14/5 = 2.8` を超えれば `Σ ≤ 2 * max` が従う**ということである
（総和比の閉じた形は `(k-1)γ / ((γ-1)(k-1) - γ) = 7γ / (6γ - 7)`）。
以下では整数で扱いやすい `γ = 3` を採用する（実測値 `7` には十分な余裕がある）。

## 本ファイルの内容

* `NodeOk` / `KidsOk`：周期木の「周期 `p` と部分木周期和 `T`」だけを保持した抽象化。
  子リストは `(root, subtreeSum)` の対の列で表す。深さ `d` でパラメタ化してあるので
  入れ子帰納型を使わずに済む。
* `NodeOk_bound`：**`11 * T ≤ 14 * p`**（＝ `T ≤ (14/11) p`、`γ = 3` のときの最良係数）。
* `KidsOk_le_two_last`：**森（根の列）の総和 ≤ `2 * (最大の根)`**。
* `passSum_le_two_max_of_hasTree`：橋渡し仮定 `PassHasTree` から
  `PassSum7` の必要条件を出し、`EndToEnd2.PassPeriodSum 8 2` を得る。

橋渡し仮定 `PassHasTree` が**唯一残る課題**であり、その中身は上の (T1)(T2)(T3) である。

すべて `sorry` なし。
-/

namespace PalPeg
namespace PassSum8

/-! ## §1 子リスト上の補助関数

子は `(周期, 部分木の周期和)` の対の列（左から右へ、周期は増加）で表す。 -/

/-- 子リストの部分木周期和の総和。 -/
def sumT : List (ℕ × ℕ) → ℕ
  | [] => 0
  | a :: t => a.2 + sumT t

/-- 子リストの周期（根）の総和。 -/
def sumRoot : List (ℕ × ℕ) → ℕ
  | [] => 0
  | a :: t => a.1 + sumRoot t

/-- 先頭の子の周期（空なら `0`）。 -/
def firstRoot : List (ℕ × ℕ) → ℕ
  | [] => 0
  | a :: _ => a.1

/-- 末尾の子の周期（空なら `0`）。 -/
def lastRoot : List (ℕ × ℕ) → ℕ
  | [] => 0
  | [a] => a.1
  | _ :: t => lastRoot t

@[simp] theorem sumT_nil : sumT [] = 0 := rfl
@[simp] theorem sumRoot_nil : sumRoot [] = 0 := rfl
@[simp] theorem lastRoot_nil : lastRoot [] = 0 := rfl
@[simp] theorem firstRoot_nil : firstRoot [] = 0 := rfl

theorem lastRoot_cons_cons (a b : ℕ × ℕ) (t : List (ℕ × ℕ)) :
    lastRoot (a :: b :: t) = lastRoot (b :: t) := rfl

/-! ## §2 木の抽象化 -/

/-- 子リストの整合性。`N` は「周期 `q` の節点の部分木周期和が `T`」という述語。

* 連続する子の周期は `3` 倍以上に増える（成長仮定、`γ = 3`）。
* 各子は `N` を満たす。 -/
def KidsOk (N : ℕ → ℕ → Prop) : List (ℕ × ℕ) → Prop
  | [] => True
  | [a] => N a.1 a.2
  | a :: b :: t => 3 * a.1 ≤ b.1 ∧ N a.1 a.2 ∧ KidsOk N (b :: t)

/-- 深さ `d` 以下の周期木の「周期 `p`・部分木周期和 `T`」の整合性。

子リスト `ks` は成長条件を満たし、末子 `q_m` は `7 * q_m < p`（＝ (T2)、`k = 8`）。
`ks = []` なら `lastRoot ks = 0` なので条件は `0 < p` に退化し、葉を表す。 -/
def NodeOk : ℕ → ℕ → ℕ → Prop
  | 0, p, T => T = p ∧ 0 < p
  | d + 1, p, T =>
      ∃ ks : List (ℕ × ℕ), KidsOk (NodeOk d) ks ∧ 7 * lastRoot ks < p ∧ T = p + sumT ks

/-! ## §3 子リストの等比和 -/

/-- **成長仮定から出る等比和**：`2 * Σ qᵢ + q₁ ≤ 3 * q_m`。とくに `2 * Σ qᵢ ≤ 3 * q_m`。 -/
theorem KidsOk_geom (N : ℕ → ℕ → Prop) :
    ∀ ks : List (ℕ × ℕ), KidsOk N ks →
      2 * sumRoot ks + firstRoot ks ≤ 3 * lastRoot ks := by
  intro ks
  induction ks with
  | nil => intro _; simp
  | cons a t ih =>
    cases t with
    | nil => intro _; simp [sumRoot, firstRoot, lastRoot]; omega
    | cons b t' =>
      intro h
      obtain ⟨hgrow, _, hrest⟩ := h
      have hIH := ih hrest
      have hf : firstRoot (b :: t') = b.1 := rfl
      have hl : lastRoot (a :: b :: t') = lastRoot (b :: t') := rfl
      have hs : sumRoot (a :: b :: t') = a.1 + sumRoot (b :: t') := rfl
      rw [hf] at hIH
      rw [hs, hl, show firstRoot (a :: b :: t') = a.1 from rfl]
      omega

/-- 各子について `11 * T ≤ 14 * q` なら、総和についても `11 * ΣT ≤ 14 * Σq`。 -/
theorem KidsOk_sum (N : ℕ → ℕ → Prop)
    (hN : ∀ q T, N q T → 11 * T ≤ 14 * q) :
    ∀ ks : List (ℕ × ℕ), KidsOk N ks → 11 * sumT ks ≤ 14 * sumRoot ks := by
  intro ks
  induction ks with
  | nil => intro _; simp
  | cons a t ih =>
    cases t with
    | nil => intro h; simpa [sumT, sumRoot] using hN a.1 a.2 h
    | cons b t' =>
      intro h
      obtain ⟨_, ha, hrest⟩ := h
      have h1 := hN a.1 a.2 ha
      have h2 := ih hrest
      have hs : sumT (a :: b :: t') = a.2 + sumT (b :: t') := rfl
      have hr : sumRoot (a :: b :: t') = a.1 + sumRoot (b :: t') := rfl
      rw [hs, hr]; omega

/-! ## §4 主要な木の不等式 -/

/-- **主定理（節点）**：整合的な周期木の部分木周期和は `T ≤ (14/11) * p`。

成長率 `γ = 3` と末子条件 `7 * q_m < p` から、
`14 * Σqᵢ = 7 * (2 * Σqᵢ) ≤ 7 * (3 * q_m) = 3 * (7 * q_m) ≤ 3 * (p - 1) < 3 * p`。 -/
theorem NodeOk_bound : ∀ (d p T : ℕ), NodeOk d p T → 11 * T ≤ 14 * p := by
  intro d
  induction d with
  | zero =>
    intro p T h
    obtain ⟨rfl, _⟩ := h
    omega
  | succ d ih =>
    intro p T h
    obtain ⟨ks, hks, hlast, rfl⟩ := h
    have hgeom := KidsOk_geom (NodeOk d) ks hks
    have hsum := KidsOk_sum (NodeOk d) (fun q T hq => ih q T hq) ks hks
    -- `14 * sumRoot ≤ 21 * lastRoot ≤ 3 * (p - 1)`
    have h21 : 14 * sumRoot ks ≤ 21 * lastRoot ks := by omega
    have h3 : 21 * lastRoot ks < 3 * p := by omega
    omega

/-- **主定理（森）**：整合的な森（根の列）の周期総和は `2 * (最大の根)` 以下。

`11 * ΣT ≤ 14 * Σρ ≤ 21 * ρ_max ≤ 22 * ρ_max`。実際の係数は `21/11 ≈ 1.909`。 -/
theorem KidsOk_le_two_last (d : ℕ) (ks : List (ℕ × ℕ)) (h : KidsOk (NodeOk d) ks) :
    sumT ks ≤ 2 * lastRoot ks := by
  have hgeom := KidsOk_geom (NodeOk d) ks h
  have hsum := KidsOk_sum (NodeOk d) (fun q T hq => NodeOk_bound d q T hq) ks h
  omega

/-- より精密な形：`11 * ΣT ≤ 21 * ρ_max`。 -/
theorem KidsOk_le_last' (d : ℕ) (ks : List (ℕ × ℕ)) (h : KidsOk (NodeOk d) ks) :
    11 * sumT ks ≤ 21 * lastRoot ks := by
  have hgeom := KidsOk_geom (NodeOk d) ks h
  have hsum := KidsOk_sum (NodeOk d) (fun q T hq => NodeOk_bound d q T hq) ks h
  omega

/-! ## §5 `stripLoop2` への橋渡し -/

universe u
variable {α : Type u} [DecidableEq α]
set_option linter.unusedSectionVars false

/-- **唯一残る仮定**：1 パスの反復列が整合的な周期木の森として表せる。

内容は本ファイル冒頭の (T1)(T2)(T3)：
* 反復列の入れ子構造（`Eⱼ` の単調性）が森を定め、
* 同じ親の連続する子の周期は `3` 倍以上に増え（(T3)、実測は `7` 倍）、
* 末子は `7 * q_m < p_c`（(T2)）を満たし、
* 根の列も `3` 倍以上に増える。

`PassSum4.children_growth_of_next` は現在 `(k-2) * q ≤ (k-1) * q'`（比 `6/7`）までしか
与えていないので、ここを比 `≥ 14/5` に強めるのが残る語の側の課題である。 -/
def PassHasTree (x : List α) (k b : ℕ) : Prop :=
  ∀ s : ℕ, ∃ (d : ℕ) (ks : List (ℕ × ℕ)),
    KidsOk (NodeOk d) ks ∧
    stripLoop2Periods x k b (x.length + 1) s = sumT ks ∧
    lastRoot ks ≤ stripLoop2MaxPeriod x k b (x.length + 1) s

/-- 橋渡し仮定から `PassSum7` が要求する `Σ ≤ 2 * max` が従う。 -/
theorem passSum_le_two_max_of_hasTree (x : List α) (k b : ℕ) (h : PassHasTree x k b) (s : ℕ) :
    stripLoop2Periods x k b (x.length + 1) s
      ≤ 2 * stripLoop2MaxPeriod x k b (x.length + 1) s := by
  obtain ⟨d, ks, hks, hsum, hmax⟩ := h s
  have := KidsOk_le_two_last d ks hks
  omega

/-- **`k = 8` の最終系**：橋渡し仮定から `EndToEnd2.PassPeriodSum 8 2`。 -/
theorem passPeriodSum_eight_of_hasTree
    (h : ∀ (x : List (Fin 2)) (b : ℕ), PassHasTree x 8 b) :
    EndToEnd2.PassPeriodSum 8 2 :=
  passPeriodSum_eight_of_sum_le_max
    (fun x b s => passSum_le_two_max_of_hasTree x 8 b (h x b) s)

end PassSum8
end PalPeg
