import PalPeg.TapeLib
import PalPeg.TextFeed
import PalPeg.GSScanTapes

/-!
# 入力コピー用テープ (`InputCopy`)

常駐段が毎ラウンド保持している「入力コピー」テープの抽象ビュー。`StackView` と同型
だが、意味を強調するために別名で提供する：ヘッドは既に受け取った語 `w` の
すぐ右の空白セルにあり（＝「最前線」`frontier`）、到着した記号を 1 回の `.right`
行動で追記できる。

* `FrontierView`       — 最前線ビュー本体。`StackView blank tp w.reverse` と同値。
* `append_spec`        — 記号の到着＝1 行動で `w` の末尾に 1 記号追加。
* `toSeqView`/`walk_left_k` — 最前線から左へ歩いて `SeqView` として読み返す。
* `frontier_padW`      — `TextFeed.padW` との関係：最前線は `padW blank w w.length`
  の添字 `w.length` の `SeqView` でもある。
* `copy_two`           — 2 本の入力コピーテープが同じラウンドで独立に追記できる。
-/

namespace PalPeg.InputCopy

open PegSeparation.RealTimeTM
open PalPeg.Tape

variable {k : ℕ}

/-! ## 1. 最前線ビュー -/

/-- 最前線ビュー：ヘッドは受け取り済みの語 `w` のすぐ右の空白セルにある。
セルを左から右へ読むと `w` が並ぶ（`StackView` の `l = w.reverse` の場合）。 -/
structure FrontierView (blank : Fin k) (tp : TapeConfiguration k) (w : List (Fin k)) :
    Prop where
  left_eq : tp.left = w.reverse
  focus_blank : tp.focus = blank
  right_blanks : Blanks blank tp.right

/-- `FrontierView` は `StackView` の言い換えにすぎない。 -/
theorem frontierView_iff_stackView {blank : Fin k} {tp : TapeConfiguration k}
    {w : List (Fin k)} : FrontierView blank tp w ↔ StackView blank tp w.reverse := by
  constructor
  · intro h; exact ⟨h.left_eq, h.focus_blank, h.right_blanks⟩
  · intro h; exact ⟨h.left_eq, h.focus_blank, h.right_blanks⟩

/-- 初期テープは空語の最前線。 -/
theorem frontierView_initial (blank : Fin k) :
    FrontierView blank ⟨[], blank, []⟩ ([] : List (Fin k)) :=
  ⟨rfl, rfl, blanks_nil blank⟩

/-- 記号 `a` の到着：`a` を書いて右へ（1 行動）。語の末尾に `a` が付く。 -/
theorem append_spec {blank : Fin k} {tp : TapeConfiguration k} {w : List (Fin k)}
    (h : FrontierView blank tp w) (a : Fin k) :
    FrontierView blank (step blank tp a .right) (w ++ [a]) := by
  have hs : StackView blank tp w.reverse := frontierView_iff_stackView.1 h
  have hpush : StackView blank (step blank tp a .right) (a :: w.reverse) :=
    push_spec hs a
  have hrev : (w ++ [a]).reverse = a :: w.reverse := by
    simp [List.reverse_append]
  exact frontierView_iff_stackView.2 (hrev ▸ hpush)

/-! ## 2. 左へ歩いて読み返す -/

/-- 最前線から 1 歩左へ：`w` の最後の記号の上に立つ `SeqView`。 -/
theorem toSeqView {blank : Fin k} {tp : TapeConfiguration k} {w : List (Fin k)}
    (h : FrontierView blank tp w) (hw : 0 < w.length) :
    SeqView blank (step blank tp blank .left) w (w.length - 1) := by
  have hne : w ≠ [] := by rintro rfl; simp at hw
  obtain ⟨L, b, hw'⟩ : ∃ L b, w = L ++ [b] := by
    rcases List.eq_nil_or_concat' w with hn | h'
    · exact absurd hn hne
    · exact h'
  subst hw'
  have hidx : (L ++ [b]).length - 1 = L.length := by simp
  rw [hidx]
  have hleft : tp.left = b :: L.reverse := by
    rw [h.left_eq]; simp
  rw [step_left_of_left_cons hleft]
  refine ⟨?_, ?_, ⟨blank :: tp.right, ?_, (h.right_blanks).cons⟩⟩
  · show L.reverse = ((L ++ [b]).take L.length).reverse
    rw [List.take_left]
  · show (L ++ [b])[L.length]? = some b
    exact List.getElem?_concat_length
  · show blank :: tp.right = (L ++ [b]).drop (L.length + 1) ++ (blank :: tp.right)
    have hlen : (L ++ [b]).length = L.length + 1 := by simp
    rw [← hlen, List.drop_length]; simp

/-- 最前線から `n + 1` 歩左へ：`w` の後ろから `n` 番目の記号の上に立つ `SeqView`。 -/
theorem walk_left_k {blank : Fin k} {tp : TapeConfiguration k} {w : List (Fin k)}
    (h : FrontierView blank tp w) (n : ℕ) (hn : n < w.length) :
    SeqView blank
      (GSTapes.leftN blank (step blank tp blank .left) n) w (w.length - 1 - n) := by
  have hw : 0 < w.length := by omega
  have hbase : SeqView blank (step blank tp blank .left) w (w.length - 1) :=
    toSeqView h hw
  have heq : w.length - 1 - n + n = w.length - 1 := by omega
  have hbase' : SeqView blank (step blank tp blank .left) w (w.length - 1 - n + n) := by
    rw [heq]; exact hbase
  exact GSTapes.seq_leftN n _ (w.length - 1 - n) hbase'

/-! ## 3. `TextFeed.padW` との関係 -/

/-- 最前線ヘッドは、`w` を長さ `|w| + 1` へパディングした語 `padW blank w w.length`
（＝ `w ++ [blank]`）の添字 `w.length`（＝末尾の空白セル）に立つ `SeqView` でもある。 -/
theorem frontier_padW {blank : Fin k} {tp : TapeConfiguration k} {w : List (Fin k)}
    (h : FrontierView blank tp w) :
    SeqView blank tp (TextFeed.padW blank w w.length) w.length := by
  have hpad : TextFeed.padW blank w w.length = w ++ [blank] := by
    simp [TextFeed.padW]
  rw [hpad]
  refine ⟨?_, ?_, ⟨tp.right, ?_, h.right_blanks⟩⟩
  · show tp.left = ((w ++ [blank]).take w.length).reverse
    rw [h.left_eq, List.take_left]
  · show (w ++ [blank])[w.length]? = some tp.focus
    rw [h.focus_blank, List.getElem?_concat_length]
  · show tp.right = (w ++ [blank]).drop (w.length + 1) ++ tp.right
    have hlen : (w ++ [blank]).length = w.length + 1 := by simp
    rw [← hlen, List.drop_length]
    simp

/-! ## 4. 複数本の入力コピーテープ -/

/-- 2 本の入力コピーテープが同じラウンドで独立に 1 記号ずつ追記されても、
それぞれの最前線ビューが保たれる。 -/
theorem copy_two {blank : Fin k} {tp₀ tp₁ : TapeConfiguration k} {w₀ w₁ : List (Fin k)}
    (h₀ : FrontierView blank tp₀ w₀) (h₁ : FrontierView blank tp₁ w₁)
    (a₀ a₁ : Fin k) :
    FrontierView blank (step blank tp₀ a₀ .right) (w₀ ++ [a₀]) ∧
      FrontierView blank (step blank tp₁ a₁ .right) (w₁ ++ [a₁]) :=
  ⟨append_spec h₀ a₀, append_spec h₁ a₁⟩

/-- `Fin 2 → TapeConfiguration k` の形でまとめた版：各テープが独立に 1 行動で
追記されても、すべて `FrontierView` を保つ。 -/
theorem copy_finTwo {blank : Fin k} {tp : Fin 2 → TapeConfiguration k}
    {w : Fin 2 → List (Fin k)} (h : ∀ i, FrontierView blank (tp i) (w i))
    (a : Fin 2 → Fin k) :
    ∀ i, FrontierView blank (step blank (tp i) (a i) .right) (w i ++ [a i]) :=
  fun i => append_spec (h i) (a i)

end PalPeg.InputCopy

