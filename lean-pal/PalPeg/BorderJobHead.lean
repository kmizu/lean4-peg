import PalPeg.BorderJob
import PalPeg.MiddleBorder

/-!
# 境界ジョブとヘッド・プログラムの対応（リスト水準）

`SCA_GS_MAPPING.md` §5 "Gaps" の 1〜3 を、`BorderJob.lean` の語彙のまま閉じる。
相手はヘッド・プログラム `dual_flag_controller`（`gs_dual_flags.py`,
`GsDualFlags.scala:22`）が走らせる `border_controller(flags=True, tail_origin="TextOrigin")`
（`gs_heads.py:139-199`）である。

座標の読み替え（Origin = 0, 語 `x`、長さ `m = |x|`）:

* 段長 `L = End`、`Tail = m - End`。テキストは逆向き視点の `[Tail, m)`、すなわち
  `(x.take L).reverse`。
* `P = Tail + pos`、`KP = End - pos = L - pos`＝現在の重なり長（gh:151-152 のコメント）。
* `Cursor` は長さの座標。初期値 `Upper - 1`（`gs_dual_flags.py:16-17`）。
  本ファイルでは `top = Cursor + 1`（未出力の長さの排他的上界）で持つので自然数で済む。

## 1. 第一段の開始位置（Gap 1）

gh:154-155 で第一段だけ `P = Tail + 1`、`KP = End - 1` から始まる。`stageRunFrom` は
開始位置 `start` を引数にした `stageRun` で、`stageRun = stageRunFrom … 0`（定義上）。
`stageRunFrom_mem_iff` は任意の `start` で成り立ち、`start = 1` の差は
「長さ `|y|` そのものを報告しない」ことだけ（`stageRun_eq_cons_stageRunFrom_one`）。
`Upper ≤ |x|` なら `Cursor < |x|` なのでその報告は `_report` に捨てられる
（`flagStream_cons_ge`、`dualFlags_eq_flagStream_borderJob`）。

## 2. 降順とビット列（Gap 2）

`borderJob_pairwise`：`borderJob` の出力は真に降順。`flagStream` は `_report`
（gh:115-127）と `_finish_flags`（gh:130-136）を写したもので、
`flagStream_eq_char` が「降順の報告列から、長さ `top-1, …, lo` ごとに 1 ビット、
隙間を `false` で埋めた列」がちょうど特性列になることを言う。

## 3. 区間による打ち切り（Gap 3）

`headJob` は `End < Lower`（gh:146）で段を打ち切り、`flagStream` は `KP < Lower`
（gh:116-117）で止まる。`headJob_mem_iff` は `ℓ ≥ lo` の範囲で打ち切りのない
ジョブと同じ集合を報告し（`headJob_filter_eq`）、`flagStream_takeWhile` /
`flagStream_filter` は `lo` 未満の報告がビット列に影響しないことを言う。

## 主定理

`dualFlags_eq`：ヘッド・プログラムが積むフラグ列は
`(lensDown lo up).map (fun n => decide (IsPal (x.take n)))`、
すなわち長さ `up-1, up-2, …, lo` の順の回文接頭辞フラグ（`test_gs_dual_flags.py` の
`expected` と同じ形）。前提は `borderJob_mem_iff` と同じ `hOK`（L1 を含む `StageOK`）。
`dualFlags_gsDec` は `MiddleBorder.DecOK`（L1 の既存の形）を `hL1` として取る版。

## 本ファイルが扱わないもの

* ヘッドの一歩一歩と `ovStep` の対応（mapping §5 の表）。ここはリスト水準のみ。
* ヘッドの縮小ループ（gh:188-193）は `End := min End (nextLen s)` を計算する。
  `headJob` は `BorderJob` と同じく `nextLen s` を使う。L1 の下で両者は一致する
  （`min_nextLen_eq`）。L1 がなければヘッドは縮まずに止まらない。
-/

set_option autoImplicit false

namespace PalPeg
namespace BorderJobHead

universe u

/-! ## 0. 降順の長さ列 -/

/-- 長さ `top-1, top-2, …, lo`（降順）。`test_gs_dual_flags.py` の
`range(len(word) - 1, lower - 1, -1)`（`top = Upper`）。 -/
def lensDown (lo : ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => if n < lo then [] else n :: lensDown lo n

theorem lensDown_of_le {lo top : ℕ} (h : top ≤ lo) : lensDown lo top = [] := by
  cases top with
  | zero => rfl
  | succ n => simp only [lensDown]; rw [if_pos (by omega)]

theorem lensDown_succ_of_le {lo n : ℕ} (h : lo ≤ n) : lensDown lo (n + 1) = n :: lensDown lo n := by
  simp only [lensDown]; rw [if_neg (by omega)]

theorem mem_lensDown {lo : ℕ} : ∀ {top n : ℕ}, n ∈ lensDown lo top ↔ lo ≤ n ∧ n < top
  | 0, n => by simp [lensDown]
  | top + 1, n => by
    by_cases h : top < lo
    · rw [lensDown_of_le (by omega)]; simp only [List.not_mem_nil, false_iff]; omega
    · rw [lensDown_succ_of_le (by omega), List.mem_cons, mem_lensDown]; omega

theorem length_lensDown (lo : ℕ) : ∀ top, (lensDown lo top).length = top - lo
  | 0 => by simp [lensDown]
  | top + 1 => by
    by_cases h : top < lo
    · rw [lensDown_of_le (by omega)]; simp only [List.length_nil]; omega
    · rw [lensDown_succ_of_le (by omega), List.length_cons, length_lensDown lo top]; omega

theorem lensDown_append {lo mid : ℕ} (hlo : lo ≤ mid) :
    ∀ top, mid ≤ top → lensDown lo top = lensDown mid top ++ lensDown lo mid
  | 0, h => by
    have hm : mid = 0 := by omega
    subst hm; rfl
  | top + 1, h => by
    rcases Nat.eq_or_lt_of_le h with heq | hlt
    · rw [← heq, lensDown_of_le (le_refl _), List.nil_append]
    · rw [lensDown_succ_of_le (show lo ≤ top by omega),
        lensDown_succ_of_le (show mid ≤ top by omega), List.cons_append,
        lensDown_append hlo top (by omega)]

/-- `lensDown` は `List.range'` の反転。 -/
theorem lensDown_eq_range' (lo : ℕ) : ∀ top, lensDown lo top = (List.range' lo (top - lo)).reverse
  | 0 => by simp [lensDown]
  | top + 1 => by
    by_cases h : top < lo
    · rw [lensDown_of_le (by omega), show top + 1 - lo = 0 by omega]; simp
    · rw [lensDown_succ_of_le (by omega), show top + 1 - lo = (top - lo) + 1 by omega,
        List.range'_concat, List.reverse_append, lensDown_eq_range' lo top]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
      congr 1
      omega

/-- 第 `i` 成分は長さ `top - 1 - i`。 -/
theorem getElem?_lensDown {lo : ℕ} : ∀ {top i : ℕ}, i < top - lo →
    (lensDown lo top)[i]? = some (top - 1 - i)
  | 0, i, h => by omega
  | top + 1, 0, h => by
    rw [lensDown_succ_of_le (by omega)]; simp
  | top + 1, i + 1, h => by
    rw [lensDown_succ_of_le (by omega), List.getElem?_cons_succ,
      getElem?_lensDown (by omega)]
    congr 1; omega

/-! ## 1. フラグの吐き出し（`_report` / `_finish_flags`） -/

/-- `_finish_flags`（gh:130-136）：`Cursor = top-1` から `lo` まで、
`Cursor = Origin`（長さ 0）なら `true`、それ以外は `false`。 -/
def finishBits (lo top : ℕ) : List Bool := (lensDown lo top).map (fun n => decide (n = 0))

theorem finishBits_of_le {lo top : ℕ} (h : top ≤ lo) : finishBits lo top = [] := by
  simp [finishBits, lensDown_of_le h]

/-- 報告列 `R`（`KP` の値の列）を受け取ったフラグ出力。`top = Cursor + 1`。

`_report(ℓ)`（gh:115-127）の分岐をそのまま写す：
* `KP < Lower` なら停止して `_finish_flags`；
* `KP ≤ Cursor`（`ℓ < top`）なら `Cursor` から `ℓ+1` まで `false`、`ℓ` に `true`、
  `Cursor := ℓ - 1`（`top := ℓ`）；
* `KP > Cursor` なら何も出さない；
* 最後に `Cursor < Lower`（`top ≤ lo`）なら停止して `_finish_flags`。
報告列が尽きたとき（段が尽きた、または `End < Lower`）も `_finish_flags`。 -/
def flagStream (lo : ℕ) : ℕ → List ℕ → List Bool
  | top, [] => finishBits lo top
  | top, ℓ :: R =>
      if ℓ < lo then finishBits lo top
      else if ℓ < top then
        List.replicate (top - 1 - ℓ) false ++
          true :: (if ℓ ≤ lo then finishBits lo ℓ else flagStream lo ℓ R)
      else if top ≤ lo then finishBits lo top
      else flagStream lo top R

theorem flagStream_of_le {lo top : ℕ} (h : top ≤ lo) (R : List ℕ) :
    flagStream lo top R = [] := by
  cases R with
  | nil => exact finishBits_of_le h
  | cons ℓ R =>
    simp only [flagStream]
    split_ifs <;> first | exact finishBits_of_le h | omega

/-- `Cursor` より長い報告は捨てられる（第一段の長さ `|x|` の報告がこれ）。 -/
theorem flagStream_cons_ge {lo top ℓ : ℕ} (hlo : lo ≤ ℓ) (htop : top ≤ ℓ) (R : List ℕ) :
    flagStream lo top (ℓ :: R) = flagStream lo top R := by
  simp only [flagStream]
  rw [if_neg (by omega), if_neg (by omega)]
  split_ifs with hle
  · rw [flagStream_of_le hle]; exact finishBits_of_le hle
  · rfl

/-- **`KP < Lower` での停止（Gap 3）**：出力は、報告列のうち最初に `lo` 未満になるまでの
接頭辞だけで決まる。 -/
theorem flagStream_takeWhile (lo : ℕ) : ∀ (R : List ℕ) (top : ℕ),
    flagStream lo top R = flagStream lo top (R.takeWhile (fun ℓ => decide (lo ≤ ℓ)))
  | [], _ => rfl
  | ℓ :: R, top => by
    rw [List.takeWhile_cons]
    by_cases hlo : ℓ < lo
    · rw [if_neg (by simp only [decide_eq_true_eq]; omega)]
      simp only [flagStream]; rw [if_pos hlo]
    · rw [if_pos (by simp only [decide_eq_true_eq]; omega)]
      simp only [flagStream]
      rw [if_neg hlo, if_neg hlo, ← flagStream_takeWhile lo R ℓ,
        ← flagStream_takeWhile lo R top]

/-- 降順の報告列では、`lo` 未満の報告を取り除いても出力は変わらない。 -/
theorem flagStream_filter (lo : ℕ) : ∀ (R : List ℕ) (top : ℕ), R.Pairwise (· > ·) →
    flagStream lo top R = flagStream lo top (R.filter (fun ℓ => decide (lo ≤ ℓ)))
  | [], _, _ => rfl
  | ℓ :: R, top, hR => by
    have hgt : ∀ m ∈ R, ℓ > m := fun _ hm => List.rel_of_pairwise_cons hR hm
    by_cases hlo : ℓ < lo
    · have hnil : (ℓ :: R).filter (fun ℓ => decide (lo ≤ ℓ)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro a ha
        simp only [decide_eq_true_eq]
        rcases List.mem_cons.mp ha with rfl | ha
        · omega
        · have := hgt a ha; omega
      rw [hnil]; simp only [flagStream]; rw [if_pos hlo]
    · rw [List.filter_cons_of_pos (by simp only [decide_eq_true_eq]; omega)]
      simp only [flagStream]
      rw [if_neg hlo, if_neg hlo, ← flagStream_filter lo R ℓ hR.of_cons,
        ← flagStream_filter lo R top hR.of_cons]

/-- **ビット列補題（Gap 2）**：降順の報告列 `R` が、区間 `[lo, top)` の各長さ `n` について
「`n = 0` か `n` が報告される」⇔ `P n` を満たすなら、出力は長さ `top-1, …, lo` の順の
`P` の特性列。区間外の報告（`top` 以上は捨てられ、`lo` 未満は停止）は何でもよい。 -/
theorem flagStream_eq_char {P : ℕ → Prop} [DecidablePred P] {lo : ℕ} :
    ∀ (R : List ℕ) (top : ℕ), R.Pairwise (· > ·) →
      (∀ n, lo ≤ n → n < top → (P n ↔ n = 0 ∨ n ∈ R)) →
      flagStream lo top R = (lensDown lo top).map (fun n => decide (P n))
  | [], top, _, hP => by
    simp only [flagStream, finishBits]
    apply List.map_congr_left
    intro n hn
    rw [mem_lensDown] at hn
    have h := hP n hn.1 hn.2
    simp only [List.not_mem_nil, or_false] at h
    exact decide_eq_decide.mpr h.symm
  | ℓ :: R, top, hsort, hP => by
    have hR : R.Pairwise (· > ·) := hsort.of_cons
    have hgt : ∀ m ∈ R, ℓ > m := fun _ hm => List.rel_of_pairwise_cons hsort hm
    simp only [flagStream]
    by_cases hlo : ℓ < lo
    · rw [if_pos hlo]
      simp only [finishBits]
      apply List.map_congr_left
      intro n hn
      rw [mem_lensDown] at hn
      refine decide_eq_decide.mpr ?_
      rw [hP n hn.1 hn.2, List.mem_cons]
      constructor
      · intro h; exact Or.inl h
      · rintro (h | h | h)
        · exact h
        · omega
        · have := hgt n h; omega
    · rw [if_neg hlo]
      by_cases htop : ℓ < top
      · rw [if_pos htop, lensDown_append (mid := ℓ + 1) (by omega) top (by omega),
          lensDown_succ_of_le (show lo ≤ ℓ by omega), List.map_append, List.map_cons]
        have hfalse : (lensDown (ℓ + 1) top).map (fun n => decide (P n))
            = List.replicate (top - 1 - ℓ) false := by
          rw [List.eq_replicate_iff]
          refine ⟨by rw [List.length_map, length_lensDown]; omega, ?_⟩
          intro b hb
          rw [List.mem_map] at hb
          obtain ⟨n, hn, rfl⟩ := hb
          rw [mem_lensDown] at hn
          rw [decide_eq_false_iff_not, hP n (by omega) hn.2, List.mem_cons]
          rintro (h | h | h)
          · omega
          · omega
          · have := hgt n h; omega
        have htrue : decide (P ℓ) = true :=
          decide_eq_true ((hP ℓ (by omega) htop).mpr (Or.inr List.mem_cons_self))
        rw [hfalse, htrue]
        congr 2
        split_ifs with hle
        · rw [finishBits_of_le hle, lensDown_of_le hle, List.map_nil]
        · apply flagStream_eq_char R ℓ hR
          intro n h1 h2
          rw [hP n h1 (by omega), List.mem_cons]
          constructor
          · rintro (h | h | h)
            · exact Or.inl h
            · omega
            · exact Or.inr h
          · rintro (h | h)
            · exact Or.inl h
            · exact Or.inr (Or.inr h)
      · rw [if_neg htop]
        split_ifs with hle
        · rw [finishBits_of_le hle, lensDown_of_le hle, List.map_nil]
        · apply flagStream_eq_char R top hR
          intro n h1 h2
          rw [hP n h1 h2, List.mem_cons]
          constructor
          · rintro (h | h | h)
            · exact Or.inl h
            · omega
            · exact Or.inr h
          · rintro (h | h)
            · exact Or.inl h
            · exact Or.inr (Or.inr h)

/-! ## 2. 降順のリストは要素の集合で決まる -/

theorem eq_of_pairwise_gt : ∀ {l₁ l₂ : List ℕ}, l₁.Pairwise (· > ·) → l₂.Pairwise (· > ·) →
    (∀ a, a ∈ l₁ ↔ a ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).mpr List.mem_cons_self) List.not_mem_nil
  | a :: _, [], _, _, h => absurd ((h a).mp List.mem_cons_self) List.not_mem_nil
  | a :: t₁, b :: t₂, h₁, h₂, h => by
    have g₁ : ∀ m ∈ t₁, a > m := fun _ hm => List.rel_of_pairwise_cons h₁ hm
    have g₂ : ∀ m ∈ t₂, b > m := fun _ hm => List.rel_of_pairwise_cons h₂ hm
    have hab : a = b := by
      rcases List.mem_cons.mp ((h a).mp List.mem_cons_self) with hab | ha
      · exact hab
      · rcases List.mem_cons.mp ((h b).mpr List.mem_cons_self) with hba | hb
        · exact hba.symm
        · have := g₂ a ha; have := g₁ b hb; omega
    subst hab
    congr 1
    apply eq_of_pairwise_gt h₁.of_cons h₂.of_cons
    intro c
    constructor
    · intro hc
      rcases List.mem_cons.mp ((h c).mp (List.mem_cons_of_mem _ hc)) with hca | hc'
      · have := g₁ c hc; omega
      · exact hc'
    · intro hc
      rcases List.mem_cons.mp ((h c).mpr (List.mem_cons_of_mem _ hc)) with hca | hc'
      · have := g₂ c hc; omega
      · exact hc'

/-! ## 3. 段の走査：開始位置・降順 -/

section Scan

variable {α : Type u} [DecidableEq α]

theorem gsShift_pos {k p₁ r q : ℕ} (hp : 0 < p₁) : 0 < gsShift k p₁ r q := by
  unfold gsShift; split_ifs <;> omega

/-- 不変条件なしで言える報告の範囲：`minimum` 以上で、候補位置を越えない。 -/
theorem ovRun_bounds (u v T : List α) (k p₁ r minimum : ℕ) :
    ∀ (fuel : ℕ) (st : ScanState) (ℓ : ℕ), ℓ ∈ ovRun u v T k p₁ r minimum fuel st →
      minimum ≤ ℓ ∧ ℓ + st.pos ≤ T.length
  | 0, st, ℓ, h => by simp [ovRun] at h
  | fuel + 1, st, ℓ, h => by
    simp only [ovRun] at h
    split_ifs at h with hstop hrep
    · simp at h
    · rcases List.mem_cons.mp h with rfl | h
      · omega
      · have h1 := ovRun_bounds u v T k p₁ r minimum fuel _ ℓ h
        have h2 := ovStep_pos_mono u v T k p₁ r st
        omega
    · have h1 := ovRun_bounds u v T k p₁ r minimum fuel _ ℓ h
      have h2 := ovStep_pos_mono u v T k p₁ r st
      omega

/-- **一段の報告は真に降順**（報告のあとのずらしは `gsShift ≥ 1`）。 -/
theorem ovRun_pairwise {u v T : List α} {k p₁ r minimum : ℕ} (hp : 0 < p₁) :
    ∀ (fuel : ℕ) (st : ScanState), (ovRun u v T k p₁ r minimum fuel st).Pairwise (· > ·)
  | 0, st => by simp [ovRun]
  | fuel + 1, st => by
    simp only [ovRun]
    split_ifs with hstop hrep
    · exact List.Pairwise.nil
    · refine List.Pairwise.cons ?_ (ovRun_pairwise hp fuel _)
      intro ℓ hℓ
      have hb := ovRun_bounds u v T k p₁ r minimum fuel _ ℓ hℓ
      have hstep : (ovStep u v T k p₁ r st).pos = st.pos + gsShift k p₁ r st.q := by
        unfold ovStep; rw [if_pos hrep.1]
      have := gsShift_pos (k := k) (r := r) (q := st.q) hp
      omega
    · exact ovRun_pairwise hp fuel _

/-- 開始位置 `start` から走る一段（ヘッドの第一段は `start = 1`、gh:154-155）。
`stageRun` は `start = 0` の場合（`stageRun_eq_stageRunFrom`）。 -/
def stageRunFrom (y : List α) (k s p₁ r fuel start : ℕ) : List ℕ :=
  ovRun (y.take s) (y.drop s) y.reverse k p₁ r (max 1 (2 * s)) fuel ⟨start, 0⟩

theorem stageRun_eq_stageRunFrom (y : List α) (k s p₁ r fuel : ℕ) :
    stageRun y k s p₁ r fuel = stageRunFrom y k s p₁ r fuel 0 := rfl

theorem stageRunFrom_pairwise {y : List α} {k s p₁ r fuel start : ℕ} (hp : 0 < p₁) :
    (stageRunFrom y k s p₁ r fuel start).Pairwise (· > ·) :=
  ovRun_pairwise hp fuel _

theorem stageRunFrom_bounds {y : List α} {k s p₁ r fuel start ℓ : ℕ}
    (h : ℓ ∈ stageRunFrom y k s p₁ r fuel start) :
    max 1 (2 * s) ≤ ℓ ∧ ℓ + start ≤ y.length := by
  have := ovRun_bounds _ _ _ k p₁ r _ fuel _ ℓ h
  simpa using this

/-- **Gap 1：任意の開始位置での一段の仕様**。報告はちょうど
`{ℓ | max 1 (2s) ≤ ℓ, ℓ + start ≤ |y|, y.take ℓ が回文}`。`start = 0` が
`stageRun_mem_iff`、`start = 1` がヘッドの第一段。 -/
theorem stageRunFrom_mem_iff {y : List α} {k s p₁ r fuel start : ℕ} (hk : 0 < k)
    (hs : s ≤ y.length) (hK : KSimple (y.drop s) k p₁ r)
    (hfuel : (k + 1) * y.length + y.length + 1 ≤ fuel) (ℓ : ℕ) :
    ℓ ∈ stageRunFrom y k s p₁ r fuel start ↔
      max 1 (2 * s) ≤ ℓ ∧ ℓ + start ≤ y.length ∧ IsPal (y.take ℓ) := by
  have hut : (y.take s).length = s := by simp only [List.length_take]; omega
  have hvt : (y.drop s).length = y.length - s := by simp only [List.length_drop]
  have hTt : (y.reverse).length = y.length := by simp
  have hlen : (y.take s).length + (y.drop s).length = (y.reverse).length := by omega
  have hmin : max 1 (2 * (y.take s).length) ≤ max 1 (2 * s) := by rw [hut]
  have happ : y.take s ++ y.drop s = y := List.take_append_drop s y
  by_cases hfit : start + s ≤ y.length
  · have hinv0 : OvInv (y.take s) (y.drop s) y.reverse ⟨start, 0⟩ :=
      ⟨by simpa using matchLen_zero (y.drop s) y.reverse _, by simp only []; omega⟩
    constructor
    · intro hmem
      obtain ⟨h1, h2, h3⟩ := ovRun_sound hK hk hlen hmin _ _ hinv0 ℓ hmem
      rw [happ] at h3
      simp only [] at h2
      exact ⟨h1, by omega, (overlapAt_reverse_iff (by omega)).mp h3⟩
    · rintro ⟨h1, h2, h3⟩
      have hov : OverlapAt (y.take s ++ y.drop s) y.reverse ℓ := by
        rw [happ]; exact (overlapAt_reverse_iff (by omega)).mpr h3
      have hgoal : (k + 1) * (y.reverse).length + (y.drop s).length + 1
          ≤ Phi k (⟨start, 0⟩ : ScanState) + fuel := by
        rw [hTt, hvt]; simp only [Phi]; omega
      exact ovRun_complete hK hk hlen hmin hov h1 (by omega) fuel ⟨start, 0⟩ hinv0
        (by simp only []; omega) hgoal
  · constructor
    · intro hmem
      have := stageRunFrom_bounds hmem
      omega
    · rintro ⟨h1, h2, _⟩; omega

/-- **Gap 1：差は長さ `|y|` だけ**。 -/
theorem stageRunFrom_one_mem_iff {y : List α} {k s p₁ r fuel : ℕ} (hk : 0 < k)
    (hs : s ≤ y.length) (hK : KSimple (y.drop s) k p₁ r)
    (hfuel : (k + 1) * y.length + y.length + 1 ≤ fuel) (ℓ : ℕ) :
    ℓ ∈ stageRunFrom y k s p₁ r fuel 1 ↔ ℓ ∈ stageRun y k s p₁ r fuel ∧ ℓ < y.length := by
  rw [stageRunFrom_mem_iff hk hs hK hfuel, stageRun_mem_iff hk hs hK hfuel]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, by omega, h3⟩, by omega⟩
  · rintro ⟨⟨h1, _, h3⟩, h4⟩; exact ⟨h1, by omega, h3⟩

/-- **Gap 1（リストの等式）**：`⟨1,0⟩` から走る段は、`⟨0,0⟩` から走る段から
長さ `|y|` の報告（あれば先頭）を除いたもの。 -/
theorem stageRun_eq_cons_stageRunFrom_one {y : List α} {k s p₁ r fuel : ℕ} (hk : 0 < k)
    (hs : s ≤ y.length) (hK : KSimple (y.drop s) k p₁ r)
    (hfuel : (k + 1) * y.length + y.length + 1 ≤ fuel) :
    stageRun y k s p₁ r fuel =
      if y.length ∈ stageRun y k s p₁ r fuel then
        y.length :: stageRunFrom y k s p₁ r fuel 1
      else stageRunFrom y k s p₁ r fuel 1 := by
  have hp := hK.period_pos
  have hsort0 : (stageRun y k s p₁ r fuel).Pairwise (· > ·) := stageRunFrom_pairwise hp
  have hsort1 : (stageRunFrom y k s p₁ r fuel 1).Pairwise (· > ·) := stageRunFrom_pairwise hp
  have hbound1 : ∀ m ∈ stageRunFrom y k s p₁ r fuel 1, m < y.length := fun m hm => by
    have := stageRunFrom_bounds hm; omega
  split_ifs with hin
  · apply eq_of_pairwise_gt hsort0 (List.Pairwise.cons (fun m hm => hbound1 m hm) hsort1)
    intro a
    rw [List.mem_cons, stageRunFrom_one_mem_iff hk hs hK hfuel]
    constructor
    · intro ha
      by_cases hal : a = y.length
      · exact Or.inl hal
      · have : a ≤ y.length := (stageRunFrom_bounds (start := 0) ha).2.trans_eq' (by omega)
        exact Or.inr ⟨ha, by omega⟩
    · rintro (rfl | ⟨ha, _⟩)
      · exact hin
      · exact ha
  · apply eq_of_pairwise_gt hsort0 hsort1
    intro a
    rw [stageRunFrom_one_mem_iff hk hs hK hfuel]
    constructor
    · intro ha
      refine ⟨ha, ?_⟩
      have : a ≤ y.length := by have := stageRunFrom_bounds (start := 0) ha; omega
      rcases Nat.lt_or_eq_of_le this with h | h
      · exact h
      · exact absurd (h ▸ ha) hin
    · exact fun h => h.1

/-- **Gap 1（ビット列で無害）**：`lo ≤ |y|` かつ `top ≤ |y|`（`Upper ≤ |x|`）なら、
第一段を `⟨0,0⟩` から走らせても `⟨1,0⟩` から走らせても出力は同じ。 -/
theorem flagStream_stage_start {y : List α} {k s p₁ r fuel : ℕ} (hk : 0 < k)
    (hs : s ≤ y.length) (hK : KSimple (y.drop s) k p₁ r)
    (hfuel : (k + 1) * y.length + y.length + 1 ≤ fuel) {lo top : ℕ}
    (hlo : lo ≤ y.length) (htop : top ≤ y.length) (R : List ℕ) :
    flagStream lo top (stageRun y k s p₁ r fuel ++ R)
      = flagStream lo top (stageRunFrom y k s p₁ r fuel 1 ++ R) := by
  rw [stageRun_eq_cons_stageRunFrom_one hk hs hK hfuel]
  split_ifs
  · rw [List.cons_append, flagStream_cons_ge hlo htop]
  · rfl

end Scan

/-! ## 4. ヘッドのジョブ（第一段は `⟨1,0⟩`、`End < Lower` で打ち切り） -/

section Job

variable {α : Type u} [DecidableEq α]

/-- ヘッド・プログラムの報告列（`KP` の値の列）。第一段は `start`（ヘッドでは 1）から、
以降の段は 0 から走る。段長が `lo` 未満になったら打ち切る（gh:146、`End < Lower`）。
段の燃料・次段長は `borderJob` と同じ。 -/
def headJob (x : List α) (dec : ℕ → ℕ × ℕ × ℕ) (k lo : ℕ) : ℕ → ℕ → ℕ → List ℕ
  | 0, _, _ => []
  | fuel + 1, start, L =>
      if L = 0 then []
      else if L < lo then []
      else
        stageRunFrom (x.take L) k (dec L).1 (dec L).2.1 (dec L).2.2 ((k + 2) * L + 1) start
          ++ headJob x dec k lo fuel 0 (nextLen (dec L).1)

/-- 打ち切りなし（`lo = 0`）・開始位置 0 のヘッドのジョブは `borderJob` そのもの。 -/
theorem borderJob_eq_headJob (x : List α) (dec : ℕ → ℕ × ℕ × ℕ) (k : ℕ) :
    ∀ fuel L, borderJob x dec k fuel L = headJob x dec k 0 fuel 0 L
  | 0, _ => rfl
  | fuel + 1, L => by
    simp only [borderJob, headJob]
    by_cases h0 : L = 0
    · rw [if_pos h0, if_pos h0]
    · rw [if_neg h0, if_neg h0, if_neg (Nat.not_lt_zero L), borderJob_eq_headJob x dec k fuel _]
      rfl

omit [DecidableEq α] in
/-- ヘッドの縮小ループ（gh:188-193）は `End := min End (nextLen s)` を計算する。
L1（`StageOK.cut_short`）の下でこれは `nextLen s` に等しい。 -/
theorem min_nextLen_eq {x : List α} {k L s p₁ r : ℕ} (hk : 4 ≤ k)
    (hOK : StageOK x k L s p₁ r) : min L (nextLen s) = nextLen s := by
  have := nextLen_lt hk hOK.cut_short
  omega

variable {x : List α} {dec : ℕ → ℕ × ℕ × ℕ} {k : ℕ}

/-- 報告は `1 ≤ ℓ ≤ L`。 -/
theorem headJob_bounds (hk : 4 ≤ k)
    (hOK : ∀ L, 1 ≤ L → L ≤ x.length → StageOK x k L (dec L).1 (dec L).2.1 (dec L).2.2)
    (lo : ℕ) : ∀ (fuel start L : ℕ), L ≤ x.length →
      ∀ ℓ ∈ headJob x dec k lo fuel start L, 1 ≤ ℓ ∧ ℓ ≤ L
  | 0, _, _, _, ℓ, h => by simp [headJob] at h
  | fuel + 1, start, L, hL, ℓ, h => by
    simp only [headJob] at h
    split_ifs at h with h0 hlo
    · simp at h
    · simp at h
    · have hnext : nextLen (dec L).1 < L := nextLen_lt hk (hOK L (by omega) hL).cut_short
      rcases List.mem_append.mp h with h | h
      · have := stageRunFrom_bounds h
        simp only [List.length_take] at this
        omega
      · have := headJob_bounds hk hOK lo fuel 0 _ (by omega) ℓ h
        omega

/-- **Gap 2：ヘッドの報告列は真に降順**。 -/
theorem headJob_pairwise (hk : 4 ≤ k)
    (hOK : ∀ L, 1 ≤ L → L ≤ x.length → StageOK x k L (dec L).1 (dec L).2.1 (dec L).2.2)
    (lo : ℕ) : ∀ (fuel start L : ℕ), L ≤ x.length →
      (headJob x dec k lo fuel start L).Pairwise (· > ·)
  | 0, _, _, _ => by simp [headJob]
  | fuel + 1, start, L, hL => by
    simp only [headJob]
    split_ifs with h0 hlo
    · exact List.Pairwise.nil
    · exact List.Pairwise.nil
    · have hOKL := hOK L (by omega) hL
      have hnext : nextLen (dec L).1 < L := nextLen_lt hk hOKL.cut_short
      rw [List.pairwise_append]
      refine ⟨stageRunFrom_pairwise hOKL.ksimple.period_pos,
        headJob_pairwise hk hOK lo fuel 0 _ (by omega), ?_⟩
      intro a ha b hb
      have h1 := stageRunFrom_bounds ha
      have h2 := headJob_bounds hk hOK lo fuel 0 _ (by omega) b hb
      unfold nextLen at h2
      omega

/-- **Gap 2：`borderJob` の出力は真に降順**。 -/
theorem borderJob_pairwise (hk : 4 ≤ k)
    (hOK : ∀ L, 1 ≤ L → L ≤ x.length → StageOK x k L (dec L).1 (dec L).2.1 (dec L).2.2)
    (fuel L : ℕ) (hL : L ≤ x.length) : (borderJob x dec k fuel L).Pairwise (· > ·) := by
  rw [borderJob_eq_headJob]
  exact headJob_pairwise hk hOK 0 fuel 0 L hL

/-- **Gap 1 / Gap 3：ヘッドの報告集合**。`lo` 以上の長さについて、報告はちょうど
長さ `1 .. L - start` の回文接頭辞（`start ≤ 1`）。打ち切り `End < Lower` は
`lo` 以上の報告を一つも落とさない。 -/
theorem headJob_mem_iff (hk : 4 ≤ k)
    (hOK : ∀ L, 1 ≤ L → L ≤ x.length → StageOK x k L (dec L).1 (dec L).2.1 (dec L).2.2)
    (lo : ℕ) : ∀ (fuel start L : ℕ), start ≤ 1 → L ≤ x.length → L < fuel →
      ∀ ℓ, lo ≤ ℓ →
        (ℓ ∈ headJob x dec k lo fuel start L ↔ 1 ≤ ℓ ∧ ℓ + start ≤ L ∧ IsPal (x.take ℓ))
  | 0, _, _, _, _, hf, _, _ => by omega
  | fuel + 1, start, L, hstart, hL, hfuel, ℓ, hℓ => by
    simp only [headJob]
    split_ifs with h0 hlo
    · simp only [List.not_mem_nil, false_iff]; omega
    · simp only [List.not_mem_nil, false_iff]; omega
    · obtain ⟨hcut, hks, hchg, hshort⟩ := hOK L (by omega) hL
      have hylen : (x.take L).length = L := by simp only [List.length_take]; omega
      have hnext : nextLen (dec L).1 < L := nextLen_lt hk hshort
      have htake : ∀ ℓ', ℓ' ≤ L → (IsPal ((x.take L).take ℓ') ↔ IsPal (x.take ℓ')) := by
        intro ℓ' h
        rw [List.take_take, show min ℓ' L = ℓ' from by omega]
      have hsf : (k + 1) * (x.take L).length + (x.take L).length + 1 ≤ (k + 2) * L + 1 := by
        rw [hylen]
        have e : (k + 1) * L + L + 1 = (k + 2) * L + 1 := by ring
        omega
      have hstage := stageRunFrom_mem_iff (y := x.take L) (k := k) (s := (dec L).1)
        (p₁ := (dec L).2.1) (r := (dec L).2.2) (fuel := (k + 2) * L + 1) (start := start)
        (by omega) (by omega) hks hsf ℓ
      rw [List.mem_append, hstage,
        headJob_mem_iff hk hOK lo fuel 0 (nextLen (dec L).1) (by omega) (by omega) (by omega)
          ℓ hℓ, hylen]
      constructor
      · rintro (⟨a, b, c⟩ | ⟨a, b, c⟩)
        · exact ⟨by omega, b, (htake ℓ (by omega)).mp c⟩
        · exact ⟨a, by unfold nextLen at b hnext; omega, c⟩
      · rintro ⟨a, b, c⟩
        by_cases hcs : max 1 (2 * (dec L).1) ≤ ℓ
        · exact Or.inl ⟨hcs, b, (htake ℓ (by omega)).mpr c⟩
        · exact Or.inr ⟨a, by unfold nextLen; omega, c⟩

/-- **Gap 3（`End < Lower`）**：打ち切ったジョブと打ち切らないジョブは、`lo` 以上の
報告の列として一致する。 -/
theorem headJob_filter_eq (hk : 4 ≤ k)
    (hOK : ∀ L, 1 ≤ L → L ≤ x.length → StageOK x k L (dec L).1 (dec L).2.1 (dec L).2.2)
    (lo fuel start L : ℕ) (hstart : start ≤ 1) (hL : L ≤ x.length) (hfuel : L < fuel) :
    (headJob x dec k lo fuel start L).filter (fun ℓ => decide (lo ≤ ℓ))
      = (headJob x dec k 0 fuel start L).filter (fun ℓ => decide (lo ≤ ℓ)) := by
  apply eq_of_pairwise_gt ((headJob_pairwise hk hOK lo fuel start L hL).filter _)
    ((headJob_pairwise hk hOK 0 fuel start L hL).filter _)
  intro a
  simp only [List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨ha, hla⟩
    exact ⟨(headJob_mem_iff hk hOK 0 fuel start L hstart hL hfuel a (Nat.zero_le _)).mpr
      ((headJob_mem_iff hk hOK lo fuel start L hstart hL hfuel a hla).mp ha), hla⟩
  · rintro ⟨ha, hla⟩
    exact ⟨(headJob_mem_iff hk hOK lo fuel start L hstart hL hfuel a hla).mpr
      ((headJob_mem_iff hk hOK 0 fuel start L hstart hL hfuel a (Nat.zero_le _)).mp ha), hla⟩

/-! ## 5. 主定理：ヘッドが積むフラグ列 -/

/-- `dual_flag_controller`（`gs_dual_flags.py:16-20`）が積むフラグ列。
`Cursor := Upper - 1` が `Lower` 未満（`up ≤ lo`）なら何もせず、そうでなければ
`End = OriginalEnd = |x|`、第一段 `⟨1,0⟩` の `headJob` の報告を `_report` に流す。 -/
def dualFlags (x : List α) (dec : ℕ → ℕ × ℕ × ℕ) (k lo up : ℕ) : List Bool :=
  if up ≤ lo then [] else flagStream lo up (headJob x dec k lo (x.length + 1) 1 x.length)

/-- **主定理（Gap 1〜3）**：`up ≤ |x|` なら、ヘッドが積むフラグ列は長さ
`up-1, up-2, …, lo` の順の回文接頭辞フラグ。 -/
theorem dualFlags_eq (hk : 4 ≤ k)
    (hOK : ∀ L, 1 ≤ L → L ≤ x.length → StageOK x k L (dec L).1 (dec L).2.1 (dec L).2.2)
    (lo up : ℕ) (hup : up ≤ x.length) :
    dualFlags x dec k lo up = (lensDown lo up).map (fun n => decide (IsPal (x.take n))) := by
  unfold dualFlags
  split_ifs with hle
  · rw [lensDown_of_le hle, List.map_nil]
  · apply flagStream_eq_char (P := fun n => IsPal (x.take n)) _ _
      (headJob_pairwise hk hOK lo _ 1 _ (le_refl _))
    intro n hlo hn
    rw [headJob_mem_iff hk hOK lo _ 1 _ (le_refl _) (le_refl _) (by omega) n hlo]
    constructor
    · intro hp
      rcases Nat.eq_zero_or_pos n with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, by omega, hp⟩
    · rintro (rfl | ⟨_, _, hp⟩)
      · show IsPal (x.take 0)
        simp [IsPal]
      · exact hp

theorem length_dualFlags (hk : 4 ≤ k)
    (hOK : ∀ L, 1 ≤ L → L ≤ x.length → StageOK x k L (dec L).1 (dec L).2.1 (dec L).2.2)
    (lo up : ℕ) (hup : up ≤ x.length) : (dualFlags x dec k lo up).length = up - lo := by
  rw [dualFlags_eq hk hOK lo up hup, List.length_map, length_lensDown]

/-- 第 `i` ビットは長さ `up - 1 - i` のフラグ（最長のものが先）。 -/
theorem getElem?_dualFlags (hk : 4 ≤ k)
    (hOK : ∀ L, 1 ≤ L → L ≤ x.length → StageOK x k L (dec L).1 (dec L).2.1 (dec L).2.2)
    (lo up : ℕ) (hup : up ≤ x.length) {i : ℕ} (hi : i < up - lo) :
    (dualFlags x dec k lo up)[i]? = some (decide (IsPal (x.take (up - 1 - i)))) := by
  rw [dualFlags_eq hk hOK lo up hup, List.getElem?_map, getElem?_lensDown hi]
  rfl

/-- `BorderJob` の `borderJob`（全段 `⟨0,0⟩` 開始、打ち切りなし）に `_report` を
かけても同じ特性列が出る（`up ≤ |x| + 1` で足りる）。 -/
theorem flagStream_borderJob (hk : 4 ≤ k)
    (hOK : ∀ L, 1 ≤ L → L ≤ x.length → StageOK x k L (dec L).1 (dec L).2.1 (dec L).2.2)
    (lo up : ℕ) (hup : up ≤ x.length + 1) :
    flagStream lo up (borderJob x dec k (x.length + 1) x.length)
      = (lensDown lo up).map (fun n => decide (IsPal (x.take n))) := by
  apply flagStream_eq_char (P := fun n => IsPal (x.take n)) _ _
    (borderJob_pairwise hk hOK _ _ (le_refl _))
  intro n _ hn
  rw [borderJob_mem_iff hk hOK _ _ (le_refl _) (by omega) n]
  constructor
  · intro hp
    rcases Nat.eq_zero_or_pos n with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, by omega, hp⟩
  · rintro (rfl | ⟨_, _, hp⟩)
    · show IsPal (x.take 0)
      simp [IsPal]
    · exact hp

/-- **Gap 1（無害性、ジョブ全体）**：`Upper ≤ |x|` なら、ヘッドの出力は
`borderJob` に `_report` をかけたものに等しい（第一段の開始位置・`End < Lower`・
`KP < Lower` の違いはすべて出力に現れない）。 -/
theorem dualFlags_eq_flagStream_borderJob (hk : 4 ≤ k)
    (hOK : ∀ L, 1 ≤ L → L ≤ x.length → StageOK x k L (dec L).1 (dec L).2.1 (dec L).2.2)
    (lo up : ℕ) (hup : up ≤ x.length) :
    dualFlags x dec k lo up = flagStream lo up (borderJob x dec k (x.length + 1) x.length) := by
  rw [dualFlags_eq hk hOK lo up hup, flagStream_borderJob hk hOK lo up (by omega)]

/-- `palPrefixFlagsGS`（長さ昇順）との関係：ヘッドの出力は、その `[lo, up)` の切り出しの
反転。 -/
theorem dualFlags_eq_reverse_slice (hk : 4 ≤ k)
    (hOK : ∀ L, 1 ≤ L → L ≤ x.length → StageOK x k L (dec L).1 (dec L).2.1 (dec L).2.2)
    (lo up : ℕ) (hup : up ≤ x.length) :
    dualFlags x dec k lo up = (((palPrefixFlagsGS x dec k).drop lo).take (up - lo)).reverse := by
  have hlenP : (palPrefixFlagsGS x dec k).length = x.length + 1 := by
    simp [palPrefixFlagsGS]
  have hlenS : (((palPrefixFlagsGS x dec k).drop lo).take (up - lo)).length = up - lo := by
    simp only [List.length_take, List.length_drop, hlenP]; omega
  apply List.ext_getElem?
  intro i
  by_cases hi : i < up - lo
  · rw [getElem?_dualFlags hk hOK lo up hup hi, List.getElem?_reverse (by rw [hlenS]; omega),
      hlenS,
      List.getElem?_take_of_lt (by omega), List.getElem?_drop,
      palPrefixFlagsGS_spec hk hOK _ (by omega)]
    rw [show lo + (up - lo - 1 - i) = up - 1 - i by omega]
    exact congrArg some (decide_eq_decide.mpr Iff.rfl)
  · rw [List.getElem?_eq_none (by rw [length_dualFlags hk hOK lo up hup]; omega),
      List.getElem?_eq_none (by rw [List.length_reverse, hlenS]; omega)]

end Job

/-! ## 6. `MiddleBorder` の分解 `gsDec` での形（L1 は `DecOK` として仮定） -/

/-- `MiddleBorder.gsDec`（ヘッドが走らせる `decompose (y.take L) 8`）での主定理。
L1 は既存の形 `MiddleBorder.DecOK` を仮定 `hL1` として取る。 -/
theorem dualFlags_gsDec {α : Type} [DecidableEq α] (hL1 : MiddleBorder.DecOK α)
    (y : List α) (lo up : ℕ) (hup : up ≤ y.length) :
    dualFlags y (MiddleBorder.gsDec y 8) 8 lo up
      = (lensDown lo up).map (fun n => decide (IsPal (y.take n))) :=
  dualFlags_eq (by omega) (fun L hL _ => hL1 y L hL) lo up hup

/-! ## 7. 小例 -/

section Examples

/-- `test_gs_dual_flags.py` と同じ形：`[0,1,0,0,1,0]` の長さ `5,4,…,0`。 -/
example : dualFlags ([0, 1, 0, 0, 1, 0] : List ℕ) (fun L => (0, L + 1, 0)) 8 0 6
    = [false, false, true, false, true, true] := by decide

example : dualFlags ([0, 1, 0, 0, 1, 0] : List ℕ) (fun L => (0, L + 1, 0)) 8 3 6
    = [false, false, true] := by decide

/-- 周期ずらしの枝を通る例（`BorderJob` の例と同じ分解）。 -/
example : dualFlags ((List.replicate 9 0) : List ℕ)
    (fun L => if L = 9 then (1, 1, 8) else (0, L + 1, 0)) 8 2 9
    = [true, true, true, true, true, true, true] := by decide

end Examples

end BorderJobHead
end PalPeg
