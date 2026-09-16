import PalPeg.InputCopy
import PalPeg.Prologue

/-!
# 左端番兵つき入力コピー (`InputCopySentinel`)

`PatternProg.setupProgL`（前提 `PatternProg.PrepPreL`）と、そのペア版
（`PatternTapesPair` の移植）は、入力コピーテープが **左端番兵** を持つことを要求する：

  `Tape.SeqView blank (S sIn) (leftSym :: w') h`,  `leftSym ∉ w'`

この模型では左端は読みで検出できない（`Tape.step_left_edge_self`：左端で
「同じ記号を書いて左へ」は恒等）ので、左向きのループを止めるには本物のセルに
番兵記号を置くしかない。ここでは

* `sentinelInit` — 1 行動の前置き（`leftSym` を書いて右へ）。空白テープから
  最前線ビュー `[leftSym]` を作る。
* `feed`         — `FullMachineTapes.fullRound` / `InputCopy.append_spec` と同じ形
  （記号 1 個につき `step … a .right` 1 回）で語を流し込む。
* `feed_frontier_sentinel` / `prepView` — 流し込み後は `leftSym :: w'` の最前線ビューになり、
  1 歩左へ戻すと `PrepPreL.inb` の形 `SeqView blank tp (leftSym :: w') w'.length` になる
  （ヘッド添字 = 最後にコピーした記号の位置 = コピー済み記号数）。
* `sentinel_read` / `walk_back_to_sentinel` — `PatternTapesPair.freeze_pair` /
  `copyPairToSingle` で使う「戻り歩き」の番兵版：戻り切ると番兵が **読める** ので歩きが止まる。
* `sentinel_left_edge_lemma` — `PatternProg.copyLoopSentL_exec` のテープ水準の中身の
  一般形：`while read ≠ leftSym: …` の左向きループはちょうど番兵の上で止まり、
  右側の内容 `w'` は保たれる。
-/

namespace PalPeg.InputCopySentinel

open PegSeparation.RealTimeTM
open PalPeg.Tape PalPeg.GSTapes PalPeg.Prologue

variable {k : ℕ}

/-! ## 1. 番兵の設置と記号の流し込み -/

/-- 左端番兵の設置：`leftSym` を書いて右へ（1 行動）。 -/
def sentinelInit (leftSym : Fin k) : TapeProg k := [(leftSym, Move.right)]

@[simp] theorem sentinelInit_length (leftSym : Fin k) :
    (sentinelInit leftSym).length = 1 := rfl

/-- 空スタック（空白テープ）に番兵を置くと、`[leftSym]` の最前線ビューになる。 -/
theorem sentinelInit_spec {blank : Fin k} {tp : TapeConfiguration k}
    (h : StackView blank tp []) (leftSym : Fin k) :
    InputCopy.FrontierView blank (runProg blank tp (sentinelInit leftSym)) [leftSym] := by
  have hf0 : InputCopy.FrontierView blank tp [] :=
    InputCopy.frontierView_iff_stackView.2 (by simpa using h)
  simpa [sentinelInit] using InputCopy.append_spec hf0 leftSym

/-- 到着した記号を 1 個 1 行動（`step … a .right`）で流し込む。
`FullMachineTapes.fullRound` の `cpy` 更新と同じ形。 -/
def feed (blank : Fin k) (tp : TapeConfiguration k) (w : List (Fin k)) :
    TapeConfiguration k :=
  w.foldl (fun t a => step blank t a .right) tp

@[simp] theorem feed_nil (blank : Fin k) (tp : TapeConfiguration k) :
    feed blank tp [] = tp := rfl

@[simp] theorem feed_cons (blank : Fin k) (tp : TapeConfiguration k) (a : Fin k)
    (w : List (Fin k)) : feed blank tp (a :: w) = feed blank (step blank tp a .right) w := rfl

/-- 流し込みは `Prologue.pushProg` の実行と同じ。 -/
theorem feed_eq_runProg (blank : Fin k) (tp : TapeConfiguration k) (w : List (Fin k)) :
    feed blank tp w = runProg blank tp (pushProg w) := by
  induction w generalizing tp with
  | nil => rfl
  | cons a w ih => simpa [feed, pushProg] using ih (step blank tp a .right)

/-- 流し込みは最前線ビューを `v` から `v ++ w` へ進める。 -/
theorem feed_frontier {blank : Fin k} {tp : TapeConfiguration k} {v : List (Fin k)}
    (h : InputCopy.FrontierView blank tp v) (w : List (Fin k)) :
    InputCopy.FrontierView blank (feed blank tp w) (v ++ w) := by
  rw [feed_eq_runProg]; exact runProg_pushProg h w

/-- **番兵つきコピーの構成**：空白テープに番兵を置き、そのあと `w'` を
1 記号 1 行動で流し込むと、`leftSym :: w'` の最前線ビューになる。 -/
theorem feed_frontier_sentinel {blank : Fin k} {tp : TapeConfiguration k}
    (h : StackView blank tp []) (leftSym : Fin k) (w' : List (Fin k)) :
    InputCopy.FrontierView blank
      (feed blank (runProg blank tp (sentinelInit leftSym)) w') (leftSym :: w') := by
  simpa using feed_frontier (sentinelInit_spec h leftSym) w'

/-! ## 2. `PrepPreL.inb` の形への変換 -/

/-- 最前線から 1 歩左：番兵つきの語 `leftSym :: w'` の添字 `w'.length`
（＝最後にコピーした記号の位置）に立つ `SeqView`。`InputCopy.toSeqView` の番兵版。 -/
theorem toSeqView {blank : Fin k} {tp : TapeConfiguration k} {leftSym : Fin k}
    {w' : List (Fin k)} (h : InputCopy.FrontierView blank tp (leftSym :: w')) :
    SeqView blank (step blank tp blank .left) (leftSym :: w') w'.length := by
  have hpos : 0 < (leftSym :: w').length := by simp
  have := InputCopy.toSeqView h hpos
  simpa using this

/-- **`PrepPreL.inb` を作る補題**：空白テープに番兵を置いて `w'` を流し込み、
1 歩左へ戻すと `Tape.SeqView blank tp (leftSym :: w') w'.length` が得られる。 -/
theorem prepView {blank : Fin k} {tp : TapeConfiguration k}
    (h : StackView blank tp []) (leftSym : Fin k) (w' : List (Fin k)) :
    SeqView blank
      (step blank (feed blank (runProg blank tp (sentinelInit leftSym)) w') blank .left)
      (leftSym :: w') w'.length :=
  toSeqView (feed_frontier_sentinel h leftSym w')

/-- 途中の添字 `n ≤ w'.length` 版：さらに `w'.length - n` 歩左へ歩けば
`PrepPreL.inb` の一般形 `SeqView blank _ (leftSym :: w') n` になる。 -/
theorem prepView_at {blank : Fin k} {tp : TapeConfiguration k}
    (h : StackView blank tp []) (leftSym : Fin k) (w' : List (Fin k)) (n : ℕ)
    (hn : n ≤ w'.length) :
    SeqView blank
      (leftN blank
        (step blank (feed blank (runProg blank tp (sentinelInit leftSym)) w') blank .left)
        (w'.length - n))
      (leftSym :: w') n := by
  refine seq_leftN (w'.length - n) _ n ?_
  have heq : n + (w'.length - n) = w'.length := by omega
  rw [heq]
  exact prepView h leftSym w'

/-! ## 3. 番兵の可読性と戻り歩き（`freeze_pair` / `copyPairToSingle` の番兵版） -/

/-- 番兵は `w'` に現れないので、`leftSym :: w'` の中で添字 `0` にちょうど 1 回だけ現れる。
`PatternProg.settleProgG_exec` / `copyProgSent_exec` の番兵条件そのもの。 -/
theorem sentinel_fresh_cons {leftSym : Fin k} {w' : List (Fin k)} (hfresh : leftSym ∉ w') :
    (leftSym :: w')[0]? = some leftSym ∧
      ∀ m : ℕ, 0 < m → (leftSym :: w')[m]? ≠ some leftSym := by
  refine ⟨rfl, ?_⟩
  intro m hm hc
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rw [List.getElem?_cons_succ] at hc
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hc
  exact hfresh (hget ▸ List.getElem_mem hlt)

/-- 番兵の上では番兵が **読める**（左端と違って停留しない本物のセルなので、
`while read ≠ leftSym` のループはここで確実に止まる）。 -/
theorem sentinel_read {blank : Fin k} {tp : TapeConfiguration k} {leftSym : Fin k}
    {w' : List (Fin k)} (h : SeqView blank tp (leftSym :: w') 0) : read tp = leftSym := by
  have := h.focus_eq
  simp only [List.getElem?_cons_zero, Option.some_inj] at this
  exact this.symm

/-- 番兵より右のセルでは、読む記号は必ず `w'` の要素なので番兵とは異なる。 -/
theorem read_ne_sentinel {blank : Fin k} {tp : TapeConfiguration k} {leftSym : Fin k}
    {w' : List (Fin k)} {b : ℕ} (hfresh : leftSym ∉ w')
    (h : SeqView blank tp (leftSym :: w') b) (hb : 0 < b) : read tp ≠ leftSym := by
  intro hc
  exact (sentinel_fresh_cons hfresh).2 b hb (by rw [h.read_eq, hc])

/-- **戻り歩き**：添字 `b` から `b` 歩左へ戻ると番兵の上に立ち、番兵が読める。
`PatternTapesPair.freeze_pair` / `copyPairToSingle` の「凍結して添字 `0` に戻す」段の
番兵版（番兵は消費されず、右側の内容 `w'` はそのまま）。 -/
theorem walk_back_to_sentinel {blank : Fin k} {tp : TapeConfiguration k} {leftSym : Fin k}
    {w' : List (Fin k)} (b : ℕ) (h : SeqView blank tp (leftSym :: w') b) :
    SeqView blank (leftN blank tp b) (leftSym :: w') 0 ∧
      read (leftN blank tp b) = leftSym := by
  have h0 : SeqView blank (leftN blank tp b) (leftSym :: w') 0 :=
    seq_leftN b tp 0 (by simpa using h)
  exact ⟨h0, sentinel_read h0⟩

/-! ## 4. 左端番兵補題（`copyLoopSentL_exec` のテープ水準の中身の一般形） -/

/-- **左端番兵補題**：番兵つきテープ上で `while read ≠ leftSym: （コピーして）左へ`
という左向きループを回すと、

* 番兵に着くまでの各ステップでは読む記号が番兵とは異なり（＝ループは続く）、
* ちょうど `b` ステップ後に番兵の上で停止し（そこで読む記号は `leftSym`）、
* 語の内容 `leftSym :: w'` は一切変わらない（右側 `w'` は保たれる）。

`PatternProg.copyLoopSentL_exec` が使っているテープ側の事実の一般形で、
ペア版の移植でもそのまま再利用できる。 -/
theorem sentinel_left_edge_lemma {blank : Fin k} {tp : TapeConfiguration k}
    {leftSym : Fin k} {w' : List (Fin k)} (hfresh : leftSym ∉ w') (b : ℕ)
    (h : SeqView blank tp (leftSym :: w') b) :
    (∀ m : ℕ, m < b → read (leftN blank tp m) ≠ leftSym) ∧
      SeqView blank (leftN blank tp b) (leftSym :: w') 0 ∧
      read (leftN blank tp b) = leftSym := by
  refine ⟨?_, walk_back_to_sentinel b h⟩
  intro m hm
  have hstep : SeqView blank (leftN blank tp m) (leftSym :: w') (b - m) :=
    seq_leftN m tp (b - m) (by rw [show b - m + m = b from by omega]; exact h)
  exact read_ne_sentinel hfresh hstep (by omega)

end PalPeg.InputCopySentinel

section Audit
open PalPeg.InputCopySentinel
#print axioms PalPeg.InputCopySentinel.sentinelInit_spec
#print axioms PalPeg.InputCopySentinel.feed_frontier_sentinel
#print axioms PalPeg.InputCopySentinel.prepView
#print axioms PalPeg.InputCopySentinel.prepView_at
#print axioms PalPeg.InputCopySentinel.walk_back_to_sentinel
#print axioms PalPeg.InputCopySentinel.sentinel_left_edge_lemma
end Audit
