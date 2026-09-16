import PalPeg.DecompInstance
import PalPeg.PrepInstance
import PalPeg.ClearAny

/-!
# `DecompUniform`：中段ジョブのための**一様な**分解器

`PalPeg.DecompInstance` の `decompInstanceB` は、動作列が段の語 `y` を
そのまま参照して答えを書き込む**非一様**な実装であった。本ファイルでは、
動作列が**テープ状態のみ**（と段幅 `L`）の関数である一様な分解器
`decompUniform` を構成する。

構成は 3 段：

* **prologue**：主テープ `X2`（`leftSym :: y` を保持し、ヘッドは添字 `L`）から
  窓 `y.take L` を左歩きで読み出し、作業テープ `S1`/`S2` に
  `GSPre.pword startSym endSym (y.take L)` の形で積み、カウンタ `S3 … S9` を
  `0` に初期化する。出口は `GSPre.Enc … 0 0 ⟨0,…⟩ (prjB ts)`。
* **分解**：`DecompInstance.decActsB` をそのまま走らせる（`x.length` を `L` に
  置き換えた一様版 `decActsL`）。
* **epilogue**：`S8`（切り出し `s`）と `S6`（生の周期）をテープ上で読みながら
  `P`／`U`／`Cnt` を書き、最後に `S1 … S9` を内容依存の長さで消去する。

本ファイルは 15 本テープ（`BorderTapes.OvTapes`）の上で、`PrepInstance` が
12 本テープ（`PatternTapes.Tapes`、`Fin 12` 添字）に対して行ったのと同じ議論を
やり直したものである。`OvTapes` は構造体なので、作業テープ 9 本を `SIdx` で
添字づけする抽象を先に用意する。
-/

namespace PalPeg
namespace DecompUniform

open PegSeparation.RealTimeTM
open BorderTapes

variable {sc : ℕ}

/-! ## 1. 作業テープ `S1 … S9` のスロット抽象 -/

/-- 作業テープの添字。 -/
inductive SIdx where
  | s1 | s2 | s3 | s4 | s5 | s6 | s7 | s8 | s9
  deriving DecidableEq

/-- スロット `i` への書き込み動作。 -/
def sAct (i : SIdx) (a : Fin sc) (m : Move) : Act sc :=
  match i with
  | .s1 => .S1 a m
  | .s2 => .S2 a m
  | .s3 => .S3 a m
  | .s4 => .S4 a m
  | .s5 => .S5 a m
  | .s6 => .S6 a m
  | .s7 => .S7 a m
  | .s8 => .S8 a m
  | .s9 => .S9 a m

/-- スロット `i` の読み出し。 -/
def sGet (i : SIdx) (ts : OvTapes sc) : TapeConfiguration sc :=
  match i with
  | .s1 => ts.S1
  | .s2 => ts.S2
  | .s3 => ts.S3
  | .s4 => ts.S4
  | .s5 => ts.S5
  | .s6 => ts.S6
  | .s7 => ts.S7
  | .s8 => ts.S8
  | .s9 => ts.S9

/-! ### `S10` / `S11` に触れないことの基本補題

`sAct` は `S1 … S9` にしか写らないので、`NoNew` は自動的に成り立つ。これと
`NoNewAll` の `[]`/`::`/`++` に関する閉包を使って、この後の各動作列生成関数が
すべて `S10`/`S11` に触れないことを一様に示していく。 -/

theorem sAct_noNew (i : SIdx) (a : Fin sc) (m : Move) : NoNew (sAct (sc := sc) i a m) := by
  cases i <;> trivial

theorem noNewAll_nil : NoNewAll ([] : List (Act sc)) := fun a ha => by simp at ha

theorem noNewAll_cons {a : Act sc} {l : List (Act sc)} (ha : NoNew a) (hl : NoNewAll l) :
    NoNewAll (a :: l) := by
  intro b hb
  rcases List.mem_cons.1 hb with rfl | hb
  · exact ha
  · exact hl b hb

theorem noNewAll_append {l₁ l₂ : List (Act sc)} (h₁ : NoNewAll l₁) (h₂ : NoNewAll l₂) :
    NoNewAll (l₁ ++ l₂) := by
  intro a ha
  rcases List.mem_append.1 ha with h | h
  · exact h₁ a h
  · exact h₂ a h

theorem noNewAll_singleton {a : Act sc} (ha : NoNew a) : NoNewAll [a] :=
  noNewAll_cons ha noNewAll_nil

theorem noNewAll_replicate {a : Act sc} (ha : NoNew a) (n : ℕ) : NoNewAll (List.replicate n a) := by
  intro b hb; rw [List.eq_of_mem_replicate hb]; exact ha

section Slots

variable {blank : Fin sc}

@[simp] theorem sGet_sAct_self (i : SIdx) (a : Fin sc) (m : Move) (ts : OvTapes sc) :
    sGet i (applyAct blank ts (sAct i a m)) = Tape.step blank (sGet i ts) a m := by
  cases i <;> rfl

theorem sGet_sAct_ne {i j : SIdx} (h : i ≠ j) (a : Fin sc) (m : Move) (ts : OvTapes sc) :
    sGet i (applyAct blank ts (sAct j a m)) = sGet i ts := by
  cases i <;> cases j <;> first | exact absurd rfl h | rfl

/-- スロットへの書き込みは主テープ 6 本を動かさない。 -/
theorem sAct_main (i : SIdx) (a : Fin sc) (m : Move) (ts : OvTapes sc) :
    (applyAct blank ts (sAct i a m)).P = ts.P
      ∧ (applyAct blank ts (sAct i a m)).X = ts.X
      ∧ (applyAct blank ts (sAct i a m)).Cnt = ts.Cnt
      ∧ (applyAct blank ts (sAct i a m)).U = ts.U
      ∧ (applyAct blank ts (sAct i a m)).X2 = ts.X2
      ∧ (applyAct blank ts (sAct i a m)).F = ts.F := by
  cases i <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem sAct_noScratch_false (i : SIdx) (a : Fin sc) (m : Move) :
    ¬ NoScratch (sAct (sc := sc) i a m) := by
  cases i <;> exact fun h => h

end Slots

/-! ## 2. 1 本のテープに対するプログラムの埋め込み -/

/-- `GSTapes.TapeProg` をスロット `i` の動作列へ埋め込む。 -/
def embedS (i : SIdx) : GSTapes.TapeProg sc → List (Act sc)
  | [] => []
  | (a, m) :: r => sAct i a m :: embedS i r

@[simp] theorem embedS_length (i : SIdx) (p : GSTapes.TapeProg sc) :
    (embedS i p).length = p.length := by
  induction p with
  | nil => rfl
  | cons hd tl ih => cases hd; simp [embedS, ih]

theorem embedS_noNewAll (i : SIdx) (p : GSTapes.TapeProg sc) : NoNewAll (embedS (sc := sc) i p) := by
  induction p with
  | nil => exact noNewAll_nil
  | cons hd tl ih => cases hd; exact noNewAll_cons (sAct_noNew i _ _) ih

section EmbedRun

variable {blank : Fin sc}

theorem embedS_run (i : SIdx) :
    ∀ (p : GSTapes.TapeProg sc) (ts : OvTapes sc),
      sGet i (applyActs blank (embedS i p) ts) = GSTapes.runProg blank (sGet i ts) p := by
  intro p
  induction p with
  | nil => intro ts; rfl
  | cons hd tl ih =>
      intro ts
      obtain ⟨a, m⟩ := hd
      show sGet i (applyActs blank (embedS i tl) (applyAct blank ts (sAct i a m))) = _
      rw [ih, sGet_sAct_self, GSTapes.runProg_cons]

theorem embedS_other {i j : SIdx} (h : j ≠ i) :
    ∀ (p : GSTapes.TapeProg sc) (ts : OvTapes sc),
      sGet j (applyActs blank (embedS i p) ts) = sGet j ts := by
  intro p
  induction p with
  | nil => intro ts; rfl
  | cons hd tl ih =>
      intro ts
      obtain ⟨a, m⟩ := hd
      show sGet j (applyActs blank (embedS i tl) (applyAct blank ts (sAct i a m))) = _
      rw [ih, sGet_sAct_ne h]

theorem embedS_main (i : SIdx) :
    ∀ (p : GSTapes.TapeProg sc) (ts : OvTapes sc),
      (applyActs blank (embedS i p) ts).P = ts.P
        ∧ (applyActs blank (embedS i p) ts).X = ts.X
        ∧ (applyActs blank (embedS i p) ts).Cnt = ts.Cnt
        ∧ (applyActs blank (embedS i p) ts).U = ts.U
        ∧ (applyActs blank (embedS i p) ts).X2 = ts.X2
        ∧ (applyActs blank (embedS i p) ts).F = ts.F := by
  intro p
  induction p with
  | nil => intro ts; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons hd tl ih =>
      intro ts
      obtain ⟨a, m⟩ := hd
      have h := ih (applyAct blank ts (sAct i a m))
      have hm := sAct_main (blank := blank) i a m ts
      rw [show embedS i ((a, m) :: tl) = sAct i a m :: embedS i tl from rfl,
        applyActs_cons]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [h.1, hm.1]
      · rw [h.2.1, hm.2.1]
      · rw [h.2.2.1, hm.2.2.1]
      · rw [h.2.2.2.1, hm.2.2.2.1]
      · rw [h.2.2.2.2.1, hm.2.2.2.2.1]
      · rw [h.2.2.2.2.2, hm.2.2.2.2.2]

end EmbedRun


/-! ## 3. 作業テープの消去（内容依存の長さ） -/

section Clear

open PalPeg.Tape

variable {blank mark : Fin sc}

/-- 単進カウンタ（値 `n`）を空スタックへ戻す：左へ `n + 2` 歩、空白を書きながら。 -/
def clearCtrProg (blank : Fin sc) (i : SIdx) (n : ℕ) : List (Act sc) :=
  embedS i (ClearAny.leftBlankProg blank (n + 2))

@[simp] theorem clearCtrProg_length (i : SIdx) (n : ℕ) :
    (clearCtrProg (sc := sc) blank i n).length = n + 2 := by
  simp [clearCtrProg]

theorem clearCtrProg_noNewAll (i : SIdx) (n : ℕ) : NoNewAll (clearCtrProg (sc := sc) blank i n) :=
  embedS_noNewAll i _

theorem clearCtrProg_other {i j : SIdx} (h : j ≠ i) (n : ℕ) (ts : OvTapes sc) :
    sGet j (applyActs blank (clearCtrProg blank i n) ts) = sGet j ts :=
  embedS_other h _ ts

theorem clearCtrProg_main (i : SIdx) (n : ℕ) (ts : OvTapes sc) :
    (applyActs blank (clearCtrProg blank i n) ts).P = ts.P
      ∧ (applyActs blank (clearCtrProg blank i n) ts).X = ts.X
      ∧ (applyActs blank (clearCtrProg blank i n) ts).Cnt = ts.Cnt
      ∧ (applyActs blank (clearCtrProg blank i n) ts).U = ts.U
      ∧ (applyActs blank (clearCtrProg blank i n) ts).X2 = ts.X2
      ∧ (applyActs blank (clearCtrProg blank i n) ts).F = ts.F :=
  embedS_main i _ ts

theorem clearCtrProg_spec (i : SIdx) (n : ℕ) (ts : OvTapes sc)
    (h : Tape.CounterView' blank mark (sGet i ts) n) :
    Tape.StackView blank (sGet i (applyActs blank (clearCtrProg blank i n) ts)) [] := by
  rw [clearCtrProg, embedS_run]
  have hl : (sGet i ts).left = List.replicate n blank ++ [mark] := h.left_eq
  have hlen : ((sGet i ts).left).length = n + 1 := by
    rw [hl]; simp
  have hcore := ClearAny.leftSweep_core blank (sGet i ts).left (sGet i ts).focus
    (sGet i ts).right
  rw [hlen] at hcore
  rw [show n + 1 + 1 = n + 2 from rfl] at hcore
  rw [hcore]
  refine ⟨rfl, rfl, ?_⟩
  intro s hs
  rcases List.mem_append.1 hs with hh | hh
  · exact List.eq_of_mem_replicate hh
  · exact h.right_blanks s hh

/-- `SeqView blank _ w p`（`w.length = p + 1 + q`）の形のテープを空スタックへ戻す。 -/
def clearSeqProgS (blank : Fin sc) (i : SIdx) (p q : ℕ) : List (Act sc) :=
  embedS i (ClearAny.leftBlankProg blank (p + 1)) ++
    embedS i (ClearAny.rightBlankProg blank (p + q + 1)) ++
    embedS i (ClearAny.leftBlankProg blank (p + q + 1))

@[simp] theorem clearSeqProgS_length (i : SIdx) (p q : ℕ) :
    (clearSeqProgS (sc := sc) blank i p q).length = 3 * p + 2 * q + 3 := by
  simp only [clearSeqProgS, List.length_append, embedS_length, ClearAny.leftBlankProg_length,
    ClearAny.rightBlankProg_length]
  omega

theorem clearSeqProgS_noNewAll (i : SIdx) (p q : ℕ) :
    NoNewAll (clearSeqProgS (sc := sc) blank i p q) :=
  noNewAll_append (noNewAll_append (embedS_noNewAll i _) (embedS_noNewAll i _))
    (embedS_noNewAll i _)

theorem clearSeqProgS_other {i j : SIdx} (h : j ≠ i) (p q : ℕ) (ts : OvTapes sc) :
    sGet j (applyActs blank (clearSeqProgS blank i p q) ts) = sGet j ts := by
  rw [clearSeqProgS, applyActs_append, applyActs_append, embedS_other h, embedS_other h,
    embedS_other h]

theorem clearSeqProgS_main (i : SIdx) (p q : ℕ) (ts : OvTapes sc) :
    (applyActs blank (clearSeqProgS blank i p q) ts).P = ts.P
      ∧ (applyActs blank (clearSeqProgS blank i p q) ts).X = ts.X
      ∧ (applyActs blank (clearSeqProgS blank i p q) ts).Cnt = ts.Cnt
      ∧ (applyActs blank (clearSeqProgS blank i p q) ts).U = ts.U
      ∧ (applyActs blank (clearSeqProgS blank i p q) ts).X2 = ts.X2
      ∧ (applyActs blank (clearSeqProgS blank i p q) ts).F = ts.F := by
  rw [clearSeqProgS, applyActs_append, applyActs_append]
  have h1 := embedS_main (blank := blank) i (ClearAny.leftBlankProg blank (p + 1)) ts
  have h2 := embedS_main (blank := blank) i (ClearAny.rightBlankProg blank (p + q + 1))
    (applyActs blank (embedS i (ClearAny.leftBlankProg blank (p + 1))) ts)
  have h3 := embedS_main (blank := blank) i (ClearAny.leftBlankProg blank (p + q + 1))
    (applyActs blank (embedS i (ClearAny.rightBlankProg blank (p + q + 1)))
      (applyActs blank (embedS i (ClearAny.leftBlankProg blank (p + 1))) ts))
  exact ⟨by rw [h3.1, h2.1, h1.1], by rw [h3.2.1, h2.2.1, h1.2.1],
    by rw [h3.2.2.1, h2.2.2.1, h1.2.2.1], by rw [h3.2.2.2.1, h2.2.2.2.1, h1.2.2.2.1],
    by rw [h3.2.2.2.2.1, h2.2.2.2.2.1, h1.2.2.2.2.1],
    by rw [h3.2.2.2.2.2, h2.2.2.2.2.2, h1.2.2.2.2.2]⟩

theorem clearSeqProgS_spec (i : SIdx) (p q : ℕ) (ts : OvTapes sc) (w : List (Fin sc))
    (hw : Tape.SeqView blank (sGet i ts) w p) (hq : q = w.length - p - 1) :
    Tape.StackView blank (sGet i (applyActs blank (clearSeqProgS blank i p q) ts)) [] := by
  obtain ⟨t, hrt, hbt⟩ := hw.right_eq
  have hple : p ≤ w.length := hw.lt.le
  have hlen1 : ((w.take p).reverse).length = p := by
    rw [List.length_reverse, List.length_take]; omega
  have hqeq : (List.replicate p blank ++ w.drop (p + 1)).length = p + q := by
    rw [List.length_append, List.length_replicate, List.length_drop]; omega
  rw [clearSeqProgS, applyActs_append, applyActs_append, embedS_run, embedS_run, embedS_run]
  have hs1 : GSTapes.runProg blank (sGet i ts) (ClearAny.leftBlankProg blank (p + 1))
      = ⟨[], blank, List.replicate p blank ++ (sGet i ts).right⟩ := by
    have h1 := ClearAny.leftSweep_core blank ((w.take p).reverse) (sGet i ts).focus
      (sGet i ts).right
    rw [hlen1, ← hw.left_eq] at h1
    exact h1
  rw [hs1]
  have hs2 : GSTapes.runProg blank
      (⟨[], blank, List.replicate p blank ++ (sGet i ts).right⟩ : TapeConfiguration sc)
      (ClearAny.rightBlankProg blank (p + q + 1))
      = ⟨List.replicate (p + q + 1) blank, blank, t.tail⟩ := by
    rw [hrt, ← List.append_assoc]
    have h2 := PrepInstance.rightSweep_prefix blank (List.replicate p blank ++ w.drop (p + 1)) [] blank t hbt
    rw [hqeq] at h2
    simpa using h2
  rw [hs2]
  have hblanks : Tape.Blanks blank (List.replicate (p + q + 1) blank) :=
    Tape.blanks_replicate blank _
  have hs3 := ClearAny.leftSweep_blank blank (List.replicate (p + q + 1) blank) hblanks t.tail
  rw [List.length_replicate] at hs3
  rw [hs3]
  refine ⟨rfl, rfl, ?_⟩
  intro s hs
  rcases List.mem_append.1 hs with h | h
  · exact List.eq_of_mem_replicate h
  · exact hbt _ (List.mem_of_mem_tail h)

end Clear


/-! ## 4. 状態を引き継ぐ動作列の連結 -/

/-- 前段のテープ状態を見てから後段を生成する連結。 -/
def seqA (blank : Fin sc) (f g : OvTapes sc → List (Act sc)) (ts : OvTapes sc) :
    List (Act sc) :=
  f ts ++ g (applyActs blank (f ts) ts)

theorem seqA_length (blank : Fin sc) (f g : OvTapes sc → List (Act sc)) (ts : OvTapes sc) :
    (seqA blank f g ts).length = (f ts).length + (g (applyActs blank (f ts) ts)).length := by
  simp [seqA]

theorem seqA_run (blank : Fin sc) (f g : OvTapes sc → List (Act sc)) (ts : OvTapes sc) :
    applyActs blank (seqA blank f g ts) ts
      = applyActs blank (g (applyActs blank (f ts) ts)) (applyActs blank (f ts) ts) := by
  rw [seqA, applyActs_append]

/-- `seqA` で連結した動作列は、各段が `S10`/`S11` に触れなければ全体も触れない。 -/
theorem seqA_noNewAll {blank : Fin sc} {f g : OvTapes sc → List (Act sc)}
    (hf : ∀ t, NoNewAll (f t)) (hg : ∀ t, NoNewAll (g t)) (ts : OvTapes sc) :
    NoNewAll (seqA blank f g ts) :=
  noNewAll_append (hf ts) (hg _)

/-! ## 5. 基本動作の成分ごとの効果 -/

section Components

variable {blank : Fin sc}

@[simp] theorem X2_applyAct_X2 (m : Move) (ts : OvTapes sc) :
    (applyAct blank ts (Act.X2 m)).X2 = Tape.step blank ts.X2 ts.X2.focus m := rfl

@[simp] theorem sGet_applyAct_X2 (i : SIdx) (m : Move) (ts : OvTapes sc) :
    sGet i (applyAct blank ts (Act.X2 m)) = sGet i ts := by cases i <;> rfl

theorem main_applyAct_X2 (m : Move) (ts : OvTapes sc) :
    (applyAct blank ts (Act.X2 m)).P = ts.P
      ∧ (applyAct blank ts (Act.X2 m)).X = ts.X
      ∧ (applyAct blank ts (Act.X2 m)).Cnt = ts.Cnt
      ∧ (applyAct blank ts (Act.X2 m)).U = ts.U
      ∧ (applyAct blank ts (Act.X2 m)).F = ts.F :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

@[simp] theorem X2_applyAct_sAct (i : SIdx) (a : Fin sc) (m : Move) (ts : OvTapes sc) :
    (applyAct blank ts (sAct i a m)).X2 = ts.X2 := (sAct_main i a m ts).2.2.2.2.1

/-- `X2` を左へ `n` 歩（内容は書き戻す）。 -/
def mvX2L (n : ℕ) : List (Act sc) := List.replicate n (Act.X2 .left)

@[simp] theorem mvX2L_length (n : ℕ) : (mvX2L (sc := sc) n).length = n := by simp [mvX2L]

theorem mvX2L_noNewAll (n : ℕ) : NoNewAll (mvX2L (sc := sc) n) :=
  noNewAll_replicate (by trivial) n

theorem mvX2L_run (n : ℕ) (ts : OvTapes sc) :
    applyActs blank (mvX2L n) ts
      = { ts with X2 := DecompInstance.lwalk blank ts.X2 n } := by
  induction n generalizing ts with
  | zero => cases ts; rfl
  | succ n ih =>
      rw [mvX2L, List.replicate_succ, applyActs_cons]
      rw [show List.replicate n (Act.X2 (sc := sc) .left) = mvX2L n from rfl, ih]
      cases ts; rfl

end Components

/-! ## 6. `X2` から `S1`/`S2` への前向きコピー -/

section Copy

variable {blank : Fin sc}

/-- 1 記号ぶん：`X2` が読んでいる記号を `S1`/`S2` の両方に積み、`X2` を右へ 1 歩。 -/
def copyRound (ts : OvTapes sc) : List (Act sc) :=
  [sAct .s1 ts.X2.focus .right, sAct .s2 ts.X2.focus .right, Act.X2 .right]

theorem copyRound_noNewAll (ts : OvTapes sc) : NoNewAll (copyRound ts) :=
  noNewAll_cons (sAct_noNew .s1 _ _) (noNewAll_cons (sAct_noNew .s2 _ _)
    (noNewAll_singleton (by trivial)))

/-- 最後の 1 記号（`X2` は動かさない）。 -/
def copyLast (ts : OvTapes sc) : List (Act sc) :=
  [sAct .s1 ts.X2.focus .right, sAct .s2 ts.X2.focus .right]

theorem copyLast_noNewAll (ts : OvTapes sc) : NoNewAll (copyLast ts) :=
  noNewAll_cons (sAct_noNew .s1 _ _) (noNewAll_singleton (sAct_noNew .s2 _ _))

/-- `n` 記号ぶん。 -/
def copyLoop (blank : Fin sc) : ℕ → OvTapes sc → List (Act sc)
  | 0, _ => []
  | n + 1, ts => copyRound ts ++ copyLoop blank n (applyActs blank (copyRound ts) ts)

theorem copyLoop_noNewAll (blank : Fin sc) :
    ∀ (n : ℕ) (ts : OvTapes sc), NoNewAll (copyLoop blank n ts) := by
  intro n
  induction n with
  | zero => intro ts; exact noNewAll_nil
  | succ n ih => intro ts; exact noNewAll_append (copyRound_noNewAll ts) (ih _)

theorem copyLoop_length (blank : Fin sc) :
    ∀ (n : ℕ) (ts : OvTapes sc), (copyLoop blank n ts).length = 3 * n := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih => intro ts; rw [copyLoop, List.length_append, ih]; simp [copyRound]; omega

/-- 1 記号ぶんの効果。 -/
theorem copyRound_run (ts : OvTapes sc) :
    applyActs blank (copyRound ts) ts
      = { ts with
          S1 := Tape.step blank ts.S1 ts.X2.focus .right
          S2 := Tape.step blank ts.S2 ts.X2.focus .right
          X2 := Tape.step blank ts.X2 ts.X2.focus .right } := by
  cases ts; rfl

theorem copyLast_run (ts : OvTapes sc) :
    applyActs blank (copyLast ts) ts
      = { ts with
          S1 := Tape.step blank ts.S1 ts.X2.focus .right
          S2 := Tape.step blank ts.S2 ts.X2.focus .right } := by
  cases ts; rfl

/-- **主補題**：`X2` の添字 `i` から右へ `n` 記号ぶん、`S1`/`S2` に同時に積む。 -/
theorem copyLoop_spec (blank : Fin sc) :
    ∀ (n i : ℕ) (ts : OvTapes sc) (w l1 l2 : List (Fin sc)), i + n < w.length →
      Tape.SeqView blank ts.X2 w i → Tape.StackView blank ts.S1 l1 →
      Tape.StackView blank ts.S2 l2 →
      Tape.SeqView blank (applyActs blank (copyLoop blank n ts) ts).X2 w (i + n)
        ∧ Tape.StackView blank (applyActs blank (copyLoop blank n ts) ts).S1
            ((((w.take (i + n)).drop i).reverse) ++ l1)
        ∧ Tape.StackView blank (applyActs blank (copyLoop blank n ts) ts).S2
            ((((w.take (i + n)).drop i).reverse) ++ l2) := by
  intro n
  induction n with
  | zero =>
      intro i ts w l1 l2 _ hx h1 h2
      simp only [copyLoop, applyActs_nil, Nat.add_zero]
      refine ⟨hx, ?_, ?_⟩ <;> simp [List.drop_eq_nil_of_le (by simp : (w.take i).length ≤ i)]
      exacts [h1, h2]
  | succ n ih =>
      intro i ts w l1 l2 hlt hx h1 h2
      have hi1 : i + 1 < w.length := by omega
      set ts₁ := applyActs blank (copyRound ts) ts with hts₁
      have hX2 : ts₁.X2 = Tape.step blank ts.X2 ts.X2.focus .right := by
        rw [hts₁, copyRound_run]
      have hS1 : ts₁.S1 = Tape.step blank ts.S1 ts.X2.focus .right := by
        rw [hts₁, copyRound_run]
      have hS2 : ts₁.S2 = Tape.step blank ts.S2 ts.X2.focus .right := by
        rw [hts₁, copyRound_run]
      have hx1 : Tape.SeqView blank ts₁.X2 w (i + 1) := by
        rw [hX2]; exact Tape.seq_move_right hx hi1
      have hst1 : Tape.StackView blank ts₁.S1 (ts.X2.focus :: l1) := by
        rw [hS1]; exact Tape.push_spec h1 _
      have hst2 : Tape.StackView blank ts₁.S2 (ts.X2.focus :: l2) := by
        rw [hS2]; exact Tape.push_spec h2 _
      obtain ⟨g1, g2, g3⟩ := ih (i + 1) ts₁ w (ts.X2.focus :: l1) (ts.X2.focus :: l2)
        (by omega) hx1 hst1 hst2
      have hrun : applyActs blank (copyLoop blank (n + 1) ts) ts
          = applyActs blank (copyLoop blank n ts₁) ts₁ := by
        rw [copyLoop, applyActs_append]
      have hfocus : w[i]? = some ts.X2.focus := hx.focus_eq
      have hkey : ∀ l : List (Fin sc),
          ((w.take (i + 1 + n)).drop (i + 1)).reverse ++ (ts.X2.focus :: l)
            = ((w.take (i + (n + 1))).drop i).reverse ++ l := by
        intro l
        have hd : (w.take (i + 1 + n)).drop i
            = ts.X2.focus :: (w.take (i + 1 + n)).drop (i + 1) := by
          refine List.drop_eq_getElem_cons ?_ |>.trans ?_
          · simp only [List.length_take]; omega
          · congr 1
            have : (w.take (i + 1 + n))[i]'(by simp only [List.length_take]; omega) = w[i] := by
              simp
            rw [this]
            exact (List.getElem?_eq_some_iff.1 hfocus).2
        rw [show i + (n + 1) = i + 1 + n from by omega, hd]
        simp
      rw [hrun]
      refine ⟨by rw [show i + (n + 1) = i + 1 + n from by omega]; exact g1, ?_, ?_⟩
      · rw [← hkey l1]; exact g2
      · rw [← hkey l2]; exact g3

end Copy


section CopyUntouched

variable {blank : Fin sc}

theorem copyLoop_slot (blank : Fin sc) {i : SIdx} (hi : i ≠ .s1) (hi2 : i ≠ .s2) :
    ∀ (n : ℕ) (ts : OvTapes sc),
      sGet i (applyActs blank (copyLoop blank n ts) ts) = sGet i ts := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih =>
      intro ts
      rw [copyLoop, applyActs_append, ih]
      show sGet i (applyAct blank (applyAct blank (applyAct blank ts
        (sAct .s1 ts.X2.focus .right)) (sAct .s2 ts.X2.focus .right)) (Act.X2 .right)) = sGet i ts
      rw [sGet_applyAct_X2, sGet_sAct_ne hi2, sGet_sAct_ne hi]

theorem copyLoop_main (blank : Fin sc) :
    ∀ (n : ℕ) (ts : OvTapes sc),
      (applyActs blank (copyLoop blank n ts) ts).P = ts.P
        ∧ (applyActs blank (copyLoop blank n ts) ts).X = ts.X
        ∧ (applyActs blank (copyLoop blank n ts) ts).Cnt = ts.Cnt
        ∧ (applyActs blank (copyLoop blank n ts) ts).U = ts.U
        ∧ (applyActs blank (copyLoop blank n ts) ts).F = ts.F := by
  intro n
  induction n with
  | zero => intro ts; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
      intro ts
      rw [copyLoop, applyActs_append]
      have h := ih (applyActs blank (copyRound ts) ts)
      rw [copyRound_run] at h ⊢
      exact h

end CopyUntouched


/-! ## 7. スロットの左歩き（内容を書き戻す）と `StackView → SeqView` -/

section Settle

variable {blank : Fin sc}

/-- スロット `i` を左へ `n` 歩（読んだ記号を書き戻す）。 -/
def lwalkS (blank : Fin sc) (i : SIdx) : ℕ → OvTapes sc → List (Act sc)
  | 0, _ => []
  | n + 1, ts =>
      sAct i (sGet i ts).focus .left ::
        lwalkS blank i n (applyAct blank ts (sAct i (sGet i ts).focus .left))

theorem lwalkS_noNewAll (blank : Fin sc) (i : SIdx) :
    ∀ (n : ℕ) (ts : OvTapes sc), NoNewAll (lwalkS blank i n ts) := by
  intro n
  induction n with
  | zero => intro ts; exact noNewAll_nil
  | succ n ih => intro ts; exact noNewAll_cons (sAct_noNew i _ _) (ih _)

theorem lwalkS_length (blank : Fin sc) (i : SIdx) :
    ∀ (n : ℕ) (ts : OvTapes sc), (lwalkS blank i n ts).length = n := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih => intro ts; rw [lwalkS, List.length_cons, ih]

theorem lwalkS_run (blank : Fin sc) (i : SIdx) :
    ∀ (n : ℕ) (ts : OvTapes sc),
      sGet i (applyActs blank (lwalkS blank i n ts) ts)
        = DecompInstance.lwalk blank (sGet i ts) n := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih =>
      intro ts
      rw [lwalkS, applyActs_cons, ih, sGet_sAct_self, DecompInstance.lwalk]

theorem lwalkS_other (blank : Fin sc) {i j : SIdx} (h : j ≠ i) :
    ∀ (n : ℕ) (ts : OvTapes sc),
      sGet j (applyActs blank (lwalkS blank i n ts) ts) = sGet j ts := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih => intro ts; rw [lwalkS, applyActs_cons, ih, sGet_sAct_ne h]

theorem lwalkS_main (blank : Fin sc) (i : SIdx) :
    ∀ (n : ℕ) (ts : OvTapes sc),
      (applyActs blank (lwalkS blank i n ts) ts).P = ts.P
        ∧ (applyActs blank (lwalkS blank i n ts) ts).X = ts.X
        ∧ (applyActs blank (lwalkS blank i n ts) ts).Cnt = ts.Cnt
        ∧ (applyActs blank (lwalkS blank i n ts) ts).U = ts.U
        ∧ (applyActs blank (lwalkS blank i n ts) ts).X2 = ts.X2
        ∧ (applyActs blank (lwalkS blank i n ts) ts).F = ts.F := by
  intro n
  induction n with
  | zero => intro ts; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
      intro ts
      rw [lwalkS, applyActs_cons]
      have h := ih (applyAct blank ts (sAct i (sGet i ts).focus .left))
      have hm := sAct_main (blank := blank) i (sGet i ts).focus Move.left ts
      exact ⟨by rw [h.1, hm.1], by rw [h.2.1, hm.2.1], by rw [h.2.2.1, hm.2.2.1],
        by rw [h.2.2.2.1, hm.2.2.2.1], by rw [h.2.2.2.2.1, hm.2.2.2.2.1],
        by rw [h.2.2.2.2.2, hm.2.2.2.2.2]⟩

/-- **積み終えたスタックを逐次ビューへ**：テープが語 `w` を左から右に保持して
ヘッドが `w` の右隣にある状態から、左へ `|w| - 1` 歩で添字 `1` の逐次ビューになる。 -/
theorem stack_to_seq (blank : Fin sc) (w : List (Fin sc)) (hw : 2 ≤ w.length)
    (tp : TapeConfiguration sc) (h : Tape.StackView blank tp w.reverse) :
    Tape.SeqView blank (DecompInstance.lwalk blank tp (w.length - 1)) w 1 := by
  obtain ⟨t, hrt⟩ : ∃ t, tp.right = t ∧ Tape.Blanks blank t := ⟨tp.right, rfl, h.right_blanks⟩
  have hbig : Tape.SeqView blank tp (w ++ [blank]) w.length := by
    refine ⟨?_, ?_, ⟨tp.right, ?_, h.right_blanks⟩⟩
    · rw [h.left_eq, List.take_left]
    · rw [List.getElem?_append_right (le_refl _)]
      simp [h.focus_blank]
    · rw [List.drop_eq_nil_of_le (by simp)]
      simp
  have hk : 1 + (w.length - 1) = w.length := by omega
  have hres := DecompInstance.lwalk_seq (blank := blank) (w := w ++ [blank]) (w.length - 1) 1
    tp (by rw [hk]; exact hbig)
  exact DecompInstance.seqView_shrink hres (fun s hs => by simpa using hs) (by omega)

end Settle


/-! ## 8. 左歩きと右歩きの往復はテープを元に戻す -/

section RoundTrip

variable {blank : Fin sc}

/-- 読んだ記号を書き戻しながら `n` セル右へ歩く。 -/
def rwalkT (blank : Fin sc) (tp : TapeConfiguration sc) (n : ℕ) : TapeConfiguration sc :=
  (fun t => Tape.step blank t t.focus .right)^[n] tp

theorem lwalk_iter (blank : Fin sc) :
    ∀ (n : ℕ) (tp : TapeConfiguration sc),
      DecompInstance.lwalk blank tp n = (fun t => Tape.step blank t t.focus .left)^[n] tp := by
  intro n
  induction n with
  | zero => intro tp; rfl
  | succ n ih => intro tp; rw [DecompInstance.lwalk, ih, Function.iterate_succ_apply]

/-- 左へ `k` 歩いてから右へ `k` 歩けば元のテープに戻る（左文脈が足りていれば）。 -/
theorem rwalk_lwalk (blank : Fin sc) :
    ∀ (k : ℕ) (tp : TapeConfiguration sc), k ≤ tp.left.length →
      rwalkT blank (DecompInstance.lwalk blank tp k) k = tp := by
  intro k
  induction k with
  | zero => intro tp _; rfl
  | succ k ih =>
      intro tp hk
      cases hl : tp.left with
      | nil => rw [hl] at hk; simp at hk
      | cons a l =>
          set tp₁ : TapeConfiguration sc := ⟨l, a, tp.focus :: tp.right⟩ with htp₁
          have hstep : Tape.step blank tp tp.focus .left = tp₁ :=
            Tape.step_left_of_left_cons hl
          have hlw : DecompInstance.lwalk blank tp (k + 1)
              = DecompInstance.lwalk blank tp₁ k := by
            rw [DecompInstance.lwalk, hstep]
          have hk1 : k ≤ tp₁.left.length := by
            have : tp₁.left.length = l.length := rfl
            rw [this]
            rw [hl] at hk; simp at hk; omega
          have hIH := ih tp₁ hk1
          rw [hlw]
          rw [rwalkT, Function.iterate_succ_apply', ← rwalkT, hIH]
          show Tape.step blank tp₁ tp₁.focus .right = tp
          rw [Tape.step_right]
          show (⟨a :: l, (tp.focus :: tp.right).headD blank, (tp.focus :: tp.right).tail⟩ :
              TapeConfiguration sc) = tp
          simp [← hl]

theorem copyLoop_X2 (blank : Fin sc) :
    ∀ (n : ℕ) (ts : OvTapes sc),
      (applyActs blank (copyLoop blank n ts) ts).X2 = rwalkT blank ts.X2 n := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih =>
      intro ts
      rw [copyLoop, applyActs_append, ih, copyRound_run]
      show rwalkT blank (Tape.step blank ts.X2 ts.X2.focus .right) n = _
      rw [rwalkT, rwalkT, ← Function.iterate_succ_apply]

end RoundTrip


/-! ## 9. prologue -/

section Prologue

variable {blank startSym endSym mark leftSym : Fin sc}

/-- `S1`/`S2` の両方に記号 `a` を積む。 -/
def pushBoth (a : Fin sc) : List (Act sc) := [sAct .s1 a .right, sAct .s2 a .right]

theorem pushBoth_noNewAll (a : Fin sc) : NoNewAll (pushBoth (sc := sc) a) :=
  noNewAll_cons (sAct_noNew .s1 _ _) (noNewAll_singleton (sAct_noNew .s2 _ _))

/-- カウンタ 7 本（`S3 … S9`）に底のマーカを置いて値 `0` にする。 -/
def zeroCtrs (mark : Fin sc) : List (Act sc) :=
  [sAct .s3 mark .right, sAct .s4 mark .right, sAct .s5 mark .right, sAct .s6 mark .right,
    sAct .s7 mark .right, sAct .s8 mark .right, sAct .s9 mark .right]

theorem zeroCtrs_noNewAll (mark : Fin sc) : NoNewAll (zeroCtrs (sc := sc) mark) :=
  noNewAll_cons (sAct_noNew .s3 _ _) (noNewAll_cons (sAct_noNew .s4 _ _)
    (noNewAll_cons (sAct_noNew .s5 _ _) (noNewAll_cons (sAct_noNew .s6 _ _)
      (noNewAll_cons (sAct_noNew .s7 _ _) (noNewAll_cons (sAct_noNew .s8 _ _)
        (noNewAll_singleton (sAct_noNew .s9 _ _)))))))

@[simp] theorem pushBoth_length (a : Fin sc) : (pushBoth a).length = 2 := rfl

@[simp] theorem zeroCtrs_length (mark : Fin sc) : (zeroCtrs (sc := sc) mark).length = 7 := rfl

theorem pushBoth_run (a : Fin sc) (ts : OvTapes sc) :
    applyActs blank (pushBoth a) ts
      = { ts with S1 := Tape.step blank ts.S1 a .right
                  S2 := Tape.step blank ts.S2 a .right } := by
  cases ts; rfl

theorem zeroCtrs_run (mark : Fin sc) (ts : OvTapes sc) :
    applyActs blank (zeroCtrs mark) ts
      = { ts with S3 := Tape.step blank ts.S3 mark .right
                  S4 := Tape.step blank ts.S4 mark .right
                  S5 := Tape.step blank ts.S5 mark .right
                  S6 := Tape.step blank ts.S6 mark .right
                  S7 := Tape.step blank ts.S7 mark .right
                  S8 := Tape.step blank ts.S8 mark .right
                  S9 := Tape.step blank ts.S9 mark .right } := by
  cases ts; rfl

/-- **一様な prologue**：`X2`（`leftSym :: y` の添字 `L`）から窓 `y.take L` を読み、
`S1`/`S2` に `GSPre.pword startSym endSym (y.take L)` を載せ、`S3 … S9` を `0` にする。
`X2` はもとの位置・内容へ戻る。 -/
def prologueU (blank startSym endSym mark : Fin sc) (L : ℕ) (ts : OvTapes sc) :
    List (Act sc) :=
  seqA blank (fun _ => pushBoth startSym ++ mvX2L (L - 1))
    (seqA blank (fun t => copyLoop blank (L - 1) t)
      (seqA blank copyLast
        (seqA blank (fun _ => pushBoth endSym)
          (seqA blank (fun t => lwalkS blank .s1 (L + 1) t)
            (seqA blank (fun t => lwalkS blank .s2 (L + 1) t)
              (fun _ => zeroCtrs mark)))))) ts

theorem prologueU_noNewAll {L : ℕ} (ts : OvTapes sc) :
    NoNewAll (prologueU blank startSym endSym mark L ts) :=
  seqA_noNewAll (fun _ => noNewAll_append (pushBoth_noNewAll startSym) (mvX2L_noNewAll (L - 1)))
    (fun t => seqA_noNewAll (fun t => copyLoop_noNewAll blank (L - 1) t)
      (fun t => seqA_noNewAll copyLast_noNewAll
        (fun t => seqA_noNewAll (fun _ => pushBoth_noNewAll endSym)
          (fun t => seqA_noNewAll (fun t => lwalkS_noNewAll blank .s1 (L + 1) t)
            (fun t => seqA_noNewAll (fun t => lwalkS_noNewAll blank .s2 (L + 1) t)
              (fun _ => zeroCtrs_noNewAll mark) t) t) t) t) t) ts

theorem prologueU_length {L : ℕ} (hL : 1 ≤ L) (ts : OvTapes sc) :
    (prologueU (sc := sc) blank startSym endSym mark L ts).length = 6 * L + 11 := by
  simp only [prologueU, seqA_length, List.length_append, pushBoth_length, mvX2L_length,
    copyLoop_length, lwalkS_length, zeroCtrs_length, copyLast, List.length_cons,
    List.length_nil]
  omega

end Prologue


section PrologueSpec

variable {blank startSym endSym mark leftSym : Fin sc}

/-- **prologue の正しさ**：`X2` が `leftSym :: y` を添字 `L` で保持する状態から、
`S1`/`S2` に `pword startSym endSym (y.take L)`（ヘッド添字 `1`）と、値 `0` の
カウンタ 7 本を作る。`X2` はもとに戻り、主テープ 5 本は変わらない。 -/
theorem prologueU_spec {L : ℕ} {y : List (Fin sc)} (hL : 1 ≤ L) (hLy : L ≤ y.length)
    (ts : OvTapes sc) (hsc : ScratchBlank blank ts)
    (hX2 : Tape.SeqView blank ts.X2 (leftSym :: y) L) :
    GSPre.Enc blank startSym endSym mark (y.take L) 0 0 ⟨0, 0, 0, 0, 0, 0, 0⟩
        (DecompInstance.prjB
          (applyActs blank (prologueU blank startSym endSym mark L ts) ts))
      ∧ (applyActs blank (prologueU blank startSym endSym mark L ts) ts).X2 = ts.X2
      ∧ (applyActs blank (prologueU blank startSym endSym mark L ts) ts).P = ts.P
      ∧ (applyActs blank (prologueU blank startSym endSym mark L ts) ts).X = ts.X
      ∧ (applyActs blank (prologueU blank startSym endSym mark L ts) ts).Cnt = ts.Cnt
      ∧ (applyActs blank (prologueU blank startSym endSym mark L ts) ts).U = ts.U
      ∧ (applyActs blank (prologueU blank startSym endSym mark L ts) ts).F = ts.F := by
  set w : List (Fin sc) := leftSym :: y with hw
  set x : List (Fin sc) := y.take L with hx
  have hxlen : x.length = L := by rw [hx, List.length_take]; omega
  have hwlen : w.length = y.length + 1 := by rw [hw]; simp
  -- 段階のテープ
  obtain ⟨ts₁, h₁⟩ : ∃ t, applyActs blank (pushBoth startSym ++ mvX2L (L - 1)) ts = t := ⟨_, rfl⟩
  obtain ⟨ts₂, h₂⟩ : ∃ t, applyActs blank (copyLoop blank (L - 1) ts₁) ts₁ = t := ⟨_, rfl⟩
  obtain ⟨ts₃, h₃⟩ : ∃ t, applyActs blank (copyLast ts₂) ts₂ = t := ⟨_, rfl⟩
  obtain ⟨ts₄, h₄⟩ : ∃ t, applyActs blank (pushBoth endSym) ts₃ = t := ⟨_, rfl⟩
  obtain ⟨ts₅, h₅⟩ : ∃ t, applyActs blank (lwalkS blank .s1 (L + 1) ts₄) ts₄ = t := ⟨_, rfl⟩
  obtain ⟨ts₆, h₆⟩ : ∃ t, applyActs blank (lwalkS blank .s2 (L + 1) ts₅) ts₅ = t := ⟨_, rfl⟩
  obtain ⟨ts₇, h₇⟩ : ∃ t, applyActs blank (zeroCtrs mark) ts₆ = t := ⟨_, rfl⟩
  have hrun : applyActs blank (prologueU blank startSym endSym mark L ts) ts = ts₇ := by
    rw [prologueU, seqA_run, seqA_run, seqA_run, seqA_run, seqA_run, seqA_run, h₁, h₂, h₃,
      h₄, h₅, h₆, h₇]
  rw [hrun]
  -- 段階 1
  have he₁ : ts₁ = { ts with S1 := Tape.step blank ts.S1 startSym .right
                             S2 := Tape.step blank ts.S2 startSym .right
                             X2 := DecompInstance.lwalk blank ts.X2 (L - 1) } := by
    rw [← h₁, applyActs_append, pushBoth_run, mvX2L_run]
  have h1S1 : Tape.StackView blank ts₁.S1 [startSym] := by
    rw [he₁]; simpa using Tape.push_spec hsc.s1 startSym
  have h1S2 : Tape.StackView blank ts₁.S2 [startSym] := by
    rw [he₁]; simpa using Tape.push_spec hsc.s2 startSym
  have h1X2 : Tape.SeqView blank ts₁.X2 w 1 := by
    rw [he₁]
    have hbase : Tape.SeqView blank ts.X2 w (1 + (L - 1)) := by
      rw [show 1 + (L - 1) = L from by omega]; exact hX2
    exact DecompInstance.lwalk_seq (L - 1) 1 ts.X2 hbase
  -- 段階 2
  have hltw : 1 + (L - 1) < w.length := by rw [hwlen]; omega
  obtain ⟨g2X2, g2S1, g2S2⟩ := copyLoop_spec blank (L - 1) 1 ts₁ w [startSym] [startSym]
    hltw h1X2 h1S1 h1S2
  rw [h₂] at g2X2 g2S1 g2S2
  rw [show 1 + (L - 1) = L from by omega] at g2X2 g2S1 g2S2
  -- 段階 3
  have hfoc : w[L]? = some ts₂.X2.focus := g2X2.focus_eq
  have he₃ : ts₃ = { ts₂ with S1 := Tape.step blank ts₂.S1 ts₂.X2.focus .right
                              S2 := Tape.step blank ts₂.S2 ts₂.X2.focus .right } := by
    rw [← h₃, copyLast_run]
  have hcons : ts₂.X2.focus :: ((w.take L).drop 1).reverse = x.reverse := by
    have hxe : x = (w.take (L + 1)).drop 1 := by
      rw [hx, hw, List.take_succ_cons, List.drop_succ_cons, List.drop_zero]
    have hsplit : w.take (L + 1) = w.take L ++ [ts₂.X2.focus] := by
      rw [List.take_add_one, hfoc]; rfl
    have hlen : (w.take L).length = L := by rw [List.length_take]; omega
    rw [hxe, hsplit, List.drop_append_of_le_length (by rw [hlen]; omega)]
    simp
  have h3S1 : Tape.StackView blank ts₃.S1 (x.reverse ++ [startSym]) := by
    rw [he₃]
    have := Tape.push_spec g2S1 ts₂.X2.focus
    rw [← List.cons_append, hcons] at this
    exact this
  have h3S2 : Tape.StackView blank ts₃.S2 (x.reverse ++ [startSym]) := by
    rw [he₃]
    have := Tape.push_spec g2S2 ts₂.X2.focus
    rw [← List.cons_append, hcons] at this
    exact this
  -- 段階 4
  have hpw : (GSPre.pword startSym endSym x).reverse = endSym :: (x.reverse ++ [startSym]) := by
    rw [GSPre.pword]; simp
  have he₄ : ts₄ = { ts₃ with S1 := Tape.step blank ts₃.S1 endSym .right
                              S2 := Tape.step blank ts₃.S2 endSym .right } := by
    rw [← h₄, pushBoth_run]
  have h4S1 : Tape.StackView blank ts₄.S1 (GSPre.pword startSym endSym x).reverse := by
    rw [he₄, hpw]; exact Tape.push_spec h3S1 endSym
  have h4S2 : Tape.StackView blank ts₄.S2 (GSPre.pword startSym endSym x).reverse := by
    rw [he₄, hpw]; exact Tape.push_spec h3S2 endSym
  have hpwlen : (GSPre.pword startSym endSym x).length = L + 2 := by
    rw [GSPre.pword_length, hxlen]
  -- 段階 5, 6
  have h5S1 : Tape.SeqView blank ts₅.S1 (GSPre.pword startSym endSym x) 1 := by
    have := lwalkS_run blank .s1 (L + 1) ts₄
    rw [h₅] at this
    show Tape.SeqView blank (sGet .s1 ts₅) _ 1
    rw [this]
    have := stack_to_seq blank (GSPre.pword startSym endSym x) (by rw [hpwlen]; omega)
      (sGet .s1 ts₄) h4S1
    rw [hpwlen] at this
    rw [show L + 2 - 1 = L + 1 from by omega] at this
    exact this
  have h5S2 : Tape.StackView blank ts₅.S2 (GSPre.pword startSym endSym x).reverse := by
    have := lwalkS_other blank (i := SIdx.s1) (j := SIdx.s2) (by decide) (L + 1) ts₄
    rw [h₅] at this
    show Tape.StackView blank (sGet .s2 ts₅) _
    rw [this]; exact h4S2
  have h6S2 : Tape.SeqView blank ts₆.S2 (GSPre.pword startSym endSym x) 1 := by
    have := lwalkS_run blank .s2 (L + 1) ts₅
    rw [h₆] at this
    show Tape.SeqView blank (sGet .s2 ts₆) _ 1
    rw [this]
    have := stack_to_seq blank (GSPre.pword startSym endSym x) (by rw [hpwlen]; omega)
      (sGet .s2 ts₅) h5S2
    rw [hpwlen] at this
    rw [show L + 2 - 1 = L + 1 from by omega] at this
    exact this
  have h6S1 : Tape.SeqView blank ts₆.S1 (GSPre.pword startSym endSym x) 1 := by
    have := lwalkS_other blank (i := SIdx.s2) (j := SIdx.s1) (by decide) (L + 1) ts₅
    rw [h₆] at this
    show Tape.SeqView blank (sGet .s1 ts₆) _ 1
    rw [this]; exact h5S1
  -- カウンタ 7 本は prologue の間ずっと空スタック
  have hctr : ∀ i : SIdx, i ≠ .s1 → i ≠ .s2 → Tape.StackView blank (sGet i ts₆) [] := by
    intro i hi1 hi2
    have e1 : sGet i ts₁ = sGet i ts := by
      rw [he₁]
      revert hi1 hi2
      cases i <;> intro hi1 hi2 <;>
        first | exact absurd rfl hi1 | exact absurd rfl hi2 | rfl
    have e2 : sGet i ts₂ = sGet i ts₁ := by
      rw [← h₂]; exact copyLoop_slot blank hi1 hi2 _ _
    have e3 : sGet i ts₃ = sGet i ts₂ := by
      rw [he₃]
      revert hi1 hi2
      cases i <;> intro hi1 hi2 <;>
        first | exact absurd rfl hi1 | exact absurd rfl hi2 | rfl
    have e4 : sGet i ts₄ = sGet i ts₃ := by
      rw [he₄]
      revert hi1 hi2
      cases i <;> intro hi1 hi2 <;>
        first | exact absurd rfl hi1 | exact absurd rfl hi2 | rfl
    have e5 : sGet i ts₅ = sGet i ts₄ := by
      rw [← h₅]; exact lwalkS_other blank hi1 _ _
    have e6 : sGet i ts₆ = sGet i ts₅ := by
      rw [← h₆]; exact lwalkS_other blank hi2 _ _
    rw [e6, e5, e4, e3, e2, e1]
    revert hi1 hi2
    cases i <;> intro hi1 hi2
    exacts [absurd rfl hi1, absurd rfl hi2, hsc.s3, hsc.s4, hsc.s5, hsc.s6, hsc.s7, hsc.s8,
      hsc.s9]
  have he₇ : ts₇ = { ts₆ with S3 := Tape.step blank ts₆.S3 mark .right
                              S4 := Tape.step blank ts₆.S4 mark .right
                              S5 := Tape.step blank ts₆.S5 mark .right
                              S6 := Tape.step blank ts₆.S6 mark .right
                              S7 := Tape.step blank ts₆.S7 mark .right
                              S8 := Tape.step blank ts₆.S8 mark .right
                              S9 := Tape.step blank ts₆.S9 mark .right } := by
    rw [← h₇, zeroCtrs_run]
  have hz : ∀ i : SIdx, i ≠ .s1 → i ≠ .s2 →
      Tape.CounterView' blank mark (Tape.step blank (sGet i ts₆) mark .right) 0 := by
    intro i hi1 hi2
    rw [Tape.counterView'_zero]
    simpa using Tape.push_spec (hctr i hi1 hi2) mark
  -- `Enc`
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show Tape.SeqView blank ts₇.S1 _ (0 + 1)
    rw [he₇]; simpa using h6S1
  · show Tape.SeqView blank ts₇.S2 _ (0 + 1)
    rw [he₇]; simpa using h6S2
  · show Tape.CounterView' blank mark ts₇.S3 0
    rw [he₇]; exact hz .s3 (by decide) (by decide)
  · show Tape.CounterView' blank mark ts₇.S4 0
    rw [he₇]; exact hz .s4 (by decide) (by decide)
  · show Tape.CounterView' blank mark ts₇.S5 0
    rw [he₇]; exact hz .s5 (by decide) (by decide)
  · show Tape.CounterView' blank mark ts₇.S6 0
    rw [he₇]; exact hz .s6 (by decide) (by decide)
  · show Tape.CounterView' blank mark ts₇.S7 0
    rw [he₇]; exact hz .s7 (by decide) (by decide)
  · show Tape.CounterView' blank mark ts₇.S8 0
    rw [he₇]; exact hz .s8 (by decide) (by decide)
  · show Tape.CounterView' blank mark ts₇.S9 0
    rw [he₇]; exact hz .s9 (by decide) (by decide)
  · -- `X2` は元に戻る
    have hXlen : ts.X2.left.length = L := by
      rw [hX2.left_eq, List.length_reverse, List.length_take]
      rw [hwlen]; omega
    have e2 : ts₂.X2 = rwalkT blank ts₁.X2 (L - 1) := by rw [← h₂]; exact copyLoop_X2 blank _ _
    have e3 : ts₃.X2 = ts₂.X2 := by rw [he₃]
    have e4 : ts₄.X2 = ts₃.X2 := by rw [he₄]
    have e5 : ts₅.X2 = ts₄.X2 := by rw [← h₅]; exact (lwalkS_main blank .s1 (L + 1) ts₄).2.2.2.2.1
    have e6 : ts₆.X2 = ts₅.X2 := by rw [← h₆]; exact (lwalkS_main blank .s2 (L + 1) ts₅).2.2.2.2.1
    have e7 : ts₇.X2 = ts₆.X2 := by rw [he₇]
    rw [e7, e6, e5, e4, e3, e2, he₁]
    exact rwalk_lwalk blank (L - 1) ts.X2 (by omega)
  all_goals
      (have hm2 := copyLoop_main blank (L - 1) ts₁
       have hm5 := lwalkS_main (blank := blank) SIdx.s1 (L + 1) ts₄
       have hm6 := lwalkS_main (blank := blank) SIdx.s2 (L + 1) ts₅
       rw [h₂] at hm2
       rw [h₅] at hm5
       rw [h₆] at hm6
       rw [he₇, he₄, he₃, he₁] at *
       simp_all)

end PrologueSpec


/-! ## 10. 分解器本体の一様版 -/

section DecRun

variable {blank startSym endSym mark : Fin sc}

/-- `DecompInstance.decActsB` の一様版：語 `x` の長さの代わりに段幅 `L` を使う。 -/
def decActsL (blank endSym mark : Fin sc) (L : ℕ) (ts : OvTapes sc) : List (Act sc) :=
  let t := applyActs blank (DecompInstance.initSignedB mark) ts
  DecompInstance.initSignedB mark ++
  DecompInstance.liftActsB blank
    (GSPre.decProg blank endSym mark 8 L (L + 1) (DecompInstance.prjB t)) t

theorem decActsL_eq {x : List (Fin sc)} {L : ℕ} (hx : x.length = L) (ts : OvTapes sc) :
    decActsL blank endSym mark L ts = DecompInstance.decActsB blank endSym mark x ts := by
  rw [decActsL, DecompInstance.decActsB, hx]

/-- **一様版の主補題**（`DecompInstance.decActsB_spec` の言い換え）。 -/
theorem decActsL_spec {x : List (Fin sc)} {L : ℕ} (hx : x.length = L) (hend : endSym ∉ x)
    (hmark : mark ≠ blank) (ts : OvTapes sc)
    (hE : GSPre.Enc blank startSym endSym mark x 0 0 ⟨0, 0, 0, 0, 0, 0, 0⟩
      (DecompInstance.prjB ts))
    (hP : Tape.StackView blank ts.P []) (hU : Tape.StackView blank ts.U [])
    (hC : Tape.StackView blank ts.Cnt []) :
    (decActsL blank endSym mark L ts).length
        ≤ 304 * decompose2Work x 8 + 83 * (L + 1)
      ∧ (∃ a b D Q E, GSPre.Enc blank startSym endSym mark x a b
          ⟨D, Q, E, (decompose2 x 8).2.1, 0, (decompose2 x 8).1, (decompose2 x 8).2.2⟩
          (DecompInstance.prjB
            (applyActs blank (decActsL blank endSym mark L ts) ts)))
      ∧ (applyActs blank (decActsL blank endSym mark L ts) ts).X = ts.X
      ∧ (applyActs blank (decActsL blank endSym mark L ts) ts).X2 = ts.X2
      ∧ (applyActs blank (decActsL blank endSym mark L ts) ts).F = ts.F := by
  have h := DecompInstance.decActsB_spec (startSym := startSym) hend hmark ts hE hP hU hC
  rw [decActsL_eq hx]
  rw [hx] at h
  exact h

/-- `decActsL` は分解器の内部使用のために `P`/`U`/`Cnt` を第 2 相の比較カウンタとして
使うので、それらは一般には保たれない。しかし埋め込み `DecompInstance.liftActB` は
`GSPre.Act` を `S1 … S9`／`C`／`Pset`／`Uset` へ写すだけで、`S10`/`S11` を触ることは
ない。 -/
theorem liftActB_noNew (ts' : BorderTapes.OvTapes sc) (act : GSPre.Act sc) :
    NoNew (DecompInstance.liftActB ts' act) := by
  cases act <;> trivial

theorem liftActsB_noNewAll (blank : Fin sc) :
    ∀ (l : List (GSPre.Act sc)) (ts' : BorderTapes.OvTapes sc),
      NoNewAll (DecompInstance.liftActsB blank l ts') := by
  intro l
  induction l with
  | nil => intro ts'; exact noNewAll_nil
  | cons act l ih =>
      intro ts'
      rw [DecompInstance.liftActsB_cons]
      exact noNewAll_cons (liftActB_noNew ts' act) (ih _)

theorem decActsL_noNewAll (L : ℕ) (ts : OvTapes sc) :
    NoNewAll (decActsL blank endSym mark L ts) := by
  apply noNewAll_append
  · simp [DecompInstance.initSignedB, NoNewAll, NoNew]
  · exact liftActsB_noNewAll blank _ _

/-- `decActsL` のあと、`P`/`U`/`Cnt` に残った第 2 相の比較カウンタの後始末を
`MiddleClear.clearPUC` で行う一様版。掃除の長さは走った本体の動作数で決まる。 -/
def decActsLClear (blank endSym mark : Fin sc) (L : ℕ) (ts : OvTapes sc) : List (Act sc) :=
  decActsL blank endSym mark L ts ++
    MiddleClear.clearPUC blank (decActsL blank endSym mark L ts).length

theorem decActsLClear_noNewAll (L : ℕ) (ts : OvTapes sc) :
    NoNewAll (decActsLClear blank endSym mark L ts) :=
  noNewAll_append (decActsL_noNewAll L ts)
    (noNewAll_of_noScratchAll (MiddleClear.clearPUC_noScratch blank _))

set_option maxHeartbeats 800000 in
/-- **`decActsLClear` の主補題**：`decActsL` の結果に `clearPUC` を重ねることで、
`P`/`U`/`Cnt` を（入口が空スタックである限り）**空スタックへ戻して**返す。分解の
符号化（`Enc`）と `X`/`X2`/`F` の保存は `clearPUC` が `S1 … S9` に触れないことから
そのまま引き継がれる。 -/
theorem decActsLClear_spec {x : List (Fin sc)} {L : ℕ} (hx : x.length = L) (hend : endSym ∉ x)
    (hmark : mark ≠ blank) (ts : OvTapes sc)
    (hE : GSPre.Enc blank startSym endSym mark x 0 0 ⟨0, 0, 0, 0, 0, 0, 0⟩
      (DecompInstance.prjB ts))
    (hP0 : Tape.StackView blank ts.P []) (hU0 : Tape.StackView blank ts.U [])
    (hC0 : Tape.StackView blank ts.Cnt []) :
    (decActsLClear blank endSym mark L ts).length
        ≤ 16 * (304 * decompose2Work x 8 + 83 * (L + 1)) + 12
      ∧ (∃ a b D Q E, GSPre.Enc blank startSym endSym mark x a b
          ⟨D, Q, E, (decompose2 x 8).2.1, 0, (decompose2 x 8).1, (decompose2 x 8).2.2⟩
          (DecompInstance.prjB
            (applyActs blank (decActsLClear blank endSym mark L ts) ts)))
      ∧ Tape.StackView blank (applyActs blank (decActsLClear blank endSym mark L ts) ts).P []
      ∧ Tape.StackView blank (applyActs blank (decActsLClear blank endSym mark L ts) ts).U []
      ∧ Tape.StackView blank (applyActs blank (decActsLClear blank endSym mark L ts) ts).Cnt []
      ∧ (applyActs blank (decActsLClear blank endSym mark L ts) ts).X = ts.X
      ∧ (applyActs blank (decActsLClear blank endSym mark L ts) ts).X2 = ts.X2
      ∧ (applyActs blank (decActsLClear blank endSym mark L ts) ts).F = ts.F := by
  obtain ⟨hlen1, ⟨a, b, D, Q, E, hE2⟩, k1X, k1X2, k1F⟩ :=
    decActsL_spec (startSym := startSym) hx hend hmark ts hE hP0 hU0 hC0
  set t1 : OvTapes sc := applyActs blank (decActsL blank endSym mark L ts) ts with ht1
  set nAct : ℕ := (decActsL blank endSym mark L ts).length with hndef
  have hnear := MiddleClear.near_applyActs (blank := blank) (decActsL blank endSym mark L ts) ts 0
    (MiddleClear.Near.of_stack hP0) (MiddleClear.Near.of_stack hU0)
    (MiddleClear.Near.of_stack hC0)
  simp only [Nat.zero_add, ← ht1, ← hndef] at hnear
  obtain ⟨g1, g2, g3⟩ := MiddleClear.clearPUC_stack blank nAct t1 hnear.1 hnear.2.1 hnear.2.2
  have hSC : ScratchEq (applyActs blank (MiddleClear.clearPUC blank nAct) t1) t1 :=
    applyActs_scratchEq _ t1 (MiddleClear.clearPUC_noScratch blank nAct)
  have happ : applyActs blank (decActsLClear blank endSym mark L ts) ts
      = applyActs blank (MiddleClear.clearPUC blank nAct) t1 := by
    rw [decActsLClear, applyActs_append, ← ht1, ← hndef]
  have hE2' : GSPre.Enc blank startSym endSym mark x a b
      ⟨D, Q, E, (decompose2 x 8).2.1, 0, (decompose2 x 8).1, (decompose2 x 8).2.2⟩
      (DecompInstance.prjB (applyActs blank (MiddleClear.clearPUC blank nAct) t1)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show Tape.SeqView blank (applyActs blank (MiddleClear.clearPUC blank nAct) t1).S1 _ _
      rw [hSC.s1]; exact hE2.v1
    · show Tape.SeqView blank (applyActs blank (MiddleClear.clearPUC blank nAct) t1).S2 _ _
      rw [hSC.s2]; exact hE2.v2
    · show Tape.CounterView' blank mark
        (applyActs blank (MiddleClear.clearPUC blank nAct) t1).S3 _
      rw [hSC.s3]; exact hE2.cd
    · show Tape.CounterView' blank mark
        (applyActs blank (MiddleClear.clearPUC blank nAct) t1).S4 _
      rw [hSC.s4]; exact hE2.cq
    · show Tape.CounterView' blank mark
        (applyActs blank (MiddleClear.clearPUC blank nAct) t1).S5 _
      rw [hSC.s5]; exact hE2.ce
    · show Tape.CounterView' blank mark
        (applyActs blank (MiddleClear.clearPUC blank nAct) t1).S6 _
      rw [hSC.s6]; exact hE2.cp
    · show Tape.CounterView' blank mark
        (applyActs blank (MiddleClear.clearPUC blank nAct) t1).S7 _
      rw [hSC.s7]; exact hE2.cf
    · show Tape.CounterView' blank mark
        (applyActs blank (MiddleClear.clearPUC blank nAct) t1).S8 _
      rw [hSC.s8]; exact hE2.cs
    · show Tape.CounterView' blank mark
        (applyActs blank (MiddleClear.clearPUC blank nAct) t1).S9 _
      rw [hSC.s9]; exact hE2.cr
  refine ⟨?_, ⟨a, b, D, Q, E, by rw [happ]; exact hE2'⟩, by rw [happ]; exact g1,
    by rw [happ]; exact g2, by rw [happ]; exact g3, ?_, ?_, ?_⟩
  · rw [decActsLClear, List.length_append, ← hndef, MiddleClear.clearPUC_length]
    omega
  · rw [happ, MiddleClear.clearPUC_X, ht1, k1X]
  · rw [happ, MiddleClear.clearPUC_X2, ht1, k1X2]
  · rw [happ, MiddleClear.clearPUC_F, ht1, k1F]

end DecRun


/-! ## 11. epilogue のテープ駆動ループ

以下のループはすべて**生成時にテープ状態を見て分岐する**（動作列そのものは
分岐を持たない）。判定はカウンタの底のマーカ、あるいは番人 `endSym` の読み取りで行う。 -/

section EpilogueLoops

variable {blank startSym endSym mark : Fin sc}

@[simp] theorem sGet_applyAct_Uset (i : SIdx) (a : Fin sc) (m : Move) (ts : OvTapes sc) :
    sGet i (applyAct blank ts (Act.Uset a m)) = sGet i ts := by cases i <;> rfl

@[simp] theorem sGet_applyAct_Pset (i : SIdx) (a : Fin sc) (m : Move) (ts : OvTapes sc) :
    sGet i (applyAct blank ts (Act.Pset a m)) = sGet i ts := by cases i <;> rfl

@[simp] theorem sGet_applyAct_C (i : SIdx) (a : Fin sc) (m : Move) (ts : OvTapes sc) :
    sGet i (applyAct blank ts (Act.C a m)) = sGet i ts := by cases i <;> rfl

/-! ### 11a. 切り出し `s` に従って `S1` の前半を `U` へ写す -/

/-- 1 記号ぶん：`S1` の読みを `U` へ積み、`S1` を右へ 1 歩、`S8` を 1 減らす。 -/
def splitRound (blank : Fin sc) (ts : OvTapes sc) : List (Act sc) :=
  [Act.Uset (sGet .s1 ts).focus .right, sAct .s1 (sGet .s1 ts).focus .right,
    sAct .s8 blank .left, sAct .s8 blank .stay]

theorem splitRound_noNewAll (ts : OvTapes sc) : NoNewAll (splitRound blank ts) :=
  noNewAll_cons (by trivial) (noNewAll_cons (sAct_noNew .s1 _ _)
    (noNewAll_cons (sAct_noNew .s8 _ _) (noNewAll_singleton (sAct_noNew .s8 _ _))))

theorem splitRound_run (ts : OvTapes sc) :
    applyActs blank (splitRound blank ts) ts
      = { ts with U := Tape.step blank ts.U ts.S1.focus .right
                  S1 := Tape.step blank ts.S1 ts.S1.focus .right
                  S8 := Tape.step blank (Tape.step blank ts.S8 blank .left) blank .stay } := by
  cases ts; rfl

/-- `S8` が底（値 `0`）になるまで繰り返す。 -/
def splitLoop (blank mark : Fin sc) : ℕ → OvTapes sc → List (Act sc)
  | 0, _ => []
  | n + 1, ts =>
      if Tape.read (Tape.step blank (sGet .s8 ts) blank .left) = mark then []
      else splitRound blank ts
        ++ splitLoop blank mark n (applyActs blank (splitRound blank ts) ts)

theorem splitLoop_noNewAll (blank mark : Fin sc) :
    ∀ (n : ℕ) (ts : OvTapes sc), NoNewAll (splitLoop blank mark n ts) := by
  intro n
  induction n with
  | zero => intro ts; exact noNewAll_nil
  | succ n ih =>
      intro ts
      rw [splitLoop]
      split
      · exact noNewAll_nil
      · exact noNewAll_append (splitRound_noNewAll ts) (ih _)

/-- **`splitLoop` の正当性と長さ**。 -/
theorem splitLoop_spec (hmark : mark ≠ blank) :
    ∀ (n s i : ℕ) (ts : OvTapes sc) (w l : List (Fin sc)), s ≤ n → i + s < w.length →
      Tape.CounterView' blank mark ts.S8 s → Tape.SeqView blank ts.S1 w i →
      Tape.StackView blank ts.U l →
      Tape.SeqView blank (applyActs blank (splitLoop blank mark n ts) ts).S1 w (i + s)
        ∧ Tape.StackView blank (applyActs blank (splitLoop blank mark n ts) ts).U
            (((w.take (i + s)).drop i).reverse ++ l)
        ∧ Tape.CounterView' blank mark
            (applyActs blank (splitLoop blank mark n ts) ts).S8 0
        ∧ (splitLoop blank mark n ts).length = 4 * s := by
  intro n
  induction n with
  | zero =>
      intro s i ts w l hsn hlt hc h1 hu
      have hs : s = 0 := by omega
      subst hs
      rw [show splitLoop blank mark 0 ts = [] from rfl]
      refine ⟨by simpa using h1, ?_, by simpa using hc, rfl⟩
      simpa [List.drop_eq_nil_of_le (by simp : (w.take i).length ≤ i)] using hu
  | succ n ih =>
      intro s i ts w l hsn hlt hc h1 hu
      have hSget : sGet SIdx.s8 ts = ts.S8 := rfl
      cases s with
      | zero =>
          have htest : Tape.read (Tape.step blank (sGet SIdx.s8 ts) blank .left) = mark := by
            rw [hSget]
            exact (Tape.counter'_isZero_iff hmark hc).2 rfl
          rw [splitLoop, if_pos htest]
          refine ⟨by simpa using h1, ?_, by simpa using hc, rfl⟩
          simpa [List.drop_eq_nil_of_le (by simp : (w.take i).length ≤ i)] using hu
      | succ k =>
          have htest : ¬ Tape.read (Tape.step blank (sGet SIdx.s8 ts) blank .left) = mark := by
            rw [hSget]
            intro hcon
            exact absurd ((Tape.counter'_isZero_iff hmark hc).1 hcon) (by omega)
          rw [splitLoop, if_neg htest]
          set ts₁ := applyActs blank (splitRound blank ts) ts with hts₁
          have hi1 : i + 1 < w.length := by omega
          have e1 : ts₁.S1 = Tape.step blank ts.S1 ts.S1.focus .right := by
            rw [hts₁, splitRound_run]
          have eU : ts₁.U = Tape.step blank ts.U ts.S1.focus .right := by
            rw [hts₁, splitRound_run]
          have e8 : ts₁.S8
              = Tape.step blank (Tape.step blank ts.S8 blank .left) blank .stay := by
            rw [hts₁, splitRound_run]
          have hc1 : Tape.CounterView' blank mark ts₁.S8 k := by
            rw [e8]; exact Tape.counter'_dec hc
          have hs1 : Tape.SeqView blank ts₁.S1 w (i + 1) := by
            rw [e1]; exact Tape.seq_move_right h1 hi1
          have hu1 : Tape.StackView blank ts₁.U (ts.S1.focus :: l) := by
            rw [eU]; exact Tape.push_spec hu _
          obtain ⟨g1, g2, g3, g4⟩ := ih k (i + 1) ts₁ w (ts.S1.focus :: l) (by omega)
            (by omega) hc1 hs1 hu1
          have hfocus : w[i]? = some ts.S1.focus := h1.focus_eq
          have hkey : ((w.take (i + 1 + k)).drop (i + 1)).reverse ++ (ts.S1.focus :: l)
              = ((w.take (i + (k + 1))).drop i).reverse ++ l := by
            have hd : (w.take (i + 1 + k)).drop i
                = ts.S1.focus :: (w.take (i + 1 + k)).drop (i + 1) := by
              refine List.drop_eq_getElem_cons ?_ |>.trans ?_
              · simp only [List.length_take]; omega
              · congr 1
                have hg : (w.take (i + 1 + k))[i]'(by simp only [List.length_take]; omega)
                    = w[i] := by simp
                rw [hg]
                exact (List.getElem?_eq_some_iff.1 hfocus).2
            rw [show i + (k + 1) = i + 1 + k from by omega, hd]
            simp
          rw [applyActs_append, ← hts₁, List.length_append]
          refine ⟨by rw [show i + (k + 1) = i + 1 + k from by omega]; exact g1, ?_, g3, ?_⟩
          · rw [← hkey]; exact g2
          · rw [g4]; simp [splitRound]; omega



/-! ### 11b. 残りの `S1` を `P` へ写す（番人 `endSym` で止まる） -/

/-- 1 記号ぶん：`S1` の読みを `P` へ積み、`S1` を右へ 1 歩。`inc` が真なら
`Cnt` も 1 増やす。 -/
def copyPRound (blank : Fin sc) (inc : Bool) (ts : OvTapes sc) : List (Act sc) :=
  if inc then
    [Act.Pset (sGet .s1 ts).focus .right, sAct .s1 (sGet .s1 ts).focus .right,
      Act.C blank .right]
  else
    [Act.Pset (sGet .s1 ts).focus .right, sAct .s1 (sGet .s1 ts).focus .right]

theorem copyPRound_noNewAll (blank : Fin sc) (inc : Bool) (ts : OvTapes sc) :
    NoNewAll (copyPRound blank inc ts) := by
  cases inc
  · exact noNewAll_cons (by trivial) (noNewAll_singleton (sAct_noNew .s1 _ _))
  · exact noNewAll_cons (by trivial) (noNewAll_cons (sAct_noNew .s1 _ _) (noNewAll_singleton (by trivial)))
    -- inc = true : [Pset, sAct .s1, C blank .right]

theorem copyPRound_run_true (ts : OvTapes sc) :
    applyActs blank (copyPRound blank true ts) ts
      = { ts with P := Tape.step blank ts.P ts.S1.focus .right
                  S1 := Tape.step blank ts.S1 ts.S1.focus .right
                  Cnt := Tape.step blank ts.Cnt blank .right } := by
  cases ts; rfl

theorem copyPRound_run_false (ts : OvTapes sc) :
    applyActs blank (copyPRound blank false ts) ts
      = { ts with P := Tape.step blank ts.P ts.S1.focus .right
                  S1 := Tape.step blank ts.S1 ts.S1.focus .right } := by
  cases ts; rfl

@[simp] theorem copyPRound_length (inc : Bool) (ts : OvTapes sc) :
    (copyPRound (sc := sc) blank inc ts).length = if inc then 3 else 2 := by
  cases inc <;> rfl

/-- 番人 `endSym` を読むまで繰り返す。 -/
def copyPLoop (blank endSym : Fin sc) (inc : Bool) : ℕ → OvTapes sc → List (Act sc)
  | 0, _ => []
  | n + 1, ts =>
      if (sGet .s1 ts).focus = endSym then []
      else copyPRound blank inc ts
        ++ copyPLoop blank endSym inc n (applyActs blank (copyPRound blank inc ts) ts)

theorem copyPLoop_noNewAll (blank endSym : Fin sc) (inc : Bool) :
    ∀ (n : ℕ) (ts : OvTapes sc), NoNewAll (copyPLoop blank endSym inc n ts) := by
  intro n
  induction n with
  | zero => intro ts; exact noNewAll_nil
  | succ n ih =>
      intro ts
      rw [copyPLoop]
      split
      · exact noNewAll_nil
      · exact noNewAll_append (copyPRound_noNewAll blank inc ts) (ih _)

/-- **`copyPLoop` の正当性と長さ**。 -/
theorem copyPLoop_spec {x : List (Fin sc)} (hend : endSym ∉ x) (inc : Bool) :
    ∀ (n t c : ℕ) (ts : OvTapes sc) (l : List (Fin sc)), x.length - t ≤ n → t ≤ x.length →
      Tape.SeqView blank ts.S1 (GSPre.pword startSym endSym x) (t + 1) →
      Tape.StackView blank ts.P l → Tape.CounterView' blank mark ts.Cnt c →
      Tape.SeqView blank (applyActs blank (copyPLoop blank endSym inc n ts) ts).S1
          (GSPre.pword startSym endSym x) (x.length + 1)
        ∧ Tape.StackView blank (applyActs blank (copyPLoop blank endSym inc n ts) ts).P
            ((x.drop t).reverse ++ l)
        ∧ Tape.CounterView' blank mark
            (applyActs blank (copyPLoop blank endSym inc n ts) ts).Cnt
            (if inc then c + (x.length - t) else c)
        ∧ (copyPLoop blank endSym inc n ts).length
            = (if inc then 3 else 2) * (x.length - t) := by
  intro n
  induction n with
  | zero =>
      intro t c ts l hn ht h1 hp hc
      have ht' : t = x.length := by omega
      subst ht'
      rw [show copyPLoop blank endSym inc 0 ts = [] from rfl]
      refine ⟨by simpa using h1, ?_, ?_, by simp⟩
      · simpa using hp
      · cases inc <;> simpa using hc
  | succ n ih =>
      intro t c ts l hn ht h1 hp hc
      by_cases hfin : t = x.length
      · subst hfin
        have htest : (sGet SIdx.s1 ts).focus = endSym := by
          show Tape.read ts.S1 = endSym
          exact (GSPre.read_pat_end_iff hend h1).2 rfl
        rw [copyPLoop, if_pos htest]
        refine ⟨by simpa using h1, ?_, ?_, by simp⟩
        · simpa using hp
        · cases inc <;> simpa using hc
      · have hlt : t < x.length := lt_of_le_of_ne ht hfin
        have htest : ¬ (sGet SIdx.s1 ts).focus = endSym := by
          show ¬ Tape.read ts.S1 = endSym
          intro hcon
          exact hfin ((GSPre.read_pat_end_iff hend h1).1 hcon)
        rw [copyPLoop, if_neg htest]
        set ts₁ := applyActs blank (copyPRound blank inc ts) ts with hts₁
        have eS1 : ts₁.S1 = Tape.step blank ts.S1 ts.S1.focus .right := by
          rw [hts₁]; cases inc
          · rw [copyPRound_run_false]
          · rw [copyPRound_run_true]
        have eP : ts₁.P = Tape.step blank ts.P ts.S1.focus .right := by
          rw [hts₁]; cases inc
          · rw [copyPRound_run_false]
          · rw [copyPRound_run_true]
        have eC : ts₁.Cnt = if inc then Tape.step blank ts.Cnt blank .right else ts.Cnt := by
          rw [hts₁]; cases inc
          · rw [copyPRound_run_false]; rfl
          · rw [copyPRound_run_true]; rfl
        have hs1 : Tape.SeqView blank ts₁.S1 (GSPre.pword startSym endSym x) (t + 1 + 1) := by
          rw [eS1]; exact GSPre.pat_right h1 hlt
        have hp1 : Tape.StackView blank ts₁.P (ts.S1.focus :: l) := by
          rw [eP]; exact Tape.push_spec hp _
        have hc1 : Tape.CounterView' blank mark ts₁.Cnt (if inc then c + 1 else c) := by
          rw [eC]; cases inc
          · simpa using hc
          · simpa using Tape.counter'_inc hc
        obtain ⟨g1, g2, g3, g4⟩ := ih (t + 1) (if inc then c + 1 else c) ts₁
          (ts.S1.focus :: l) (by omega) (by omega) hs1 hp1 hc1
        have hxfocus : x[t] = ts.S1.focus := by
          have := GSPre.read_pat_lt h1 hlt
          exact (List.getElem?_eq_some_iff.1 this).2
        have hdrop : x.drop t = ts.S1.focus :: x.drop (t + 1) := by
          rw [List.drop_eq_getElem_cons hlt, hxfocus]
        rw [applyActs_append, ← hts₁, List.length_append]
        refine ⟨g1, ?_, ?_, ?_⟩
        · rw [hdrop]; simpa using g2
        · cases inc
          · simpa using g3
          · have harith : c + 1 + (x.length - (t + 1)) = c + (x.length - t) := by omega
            simpa [harith] using g3
        · rw [g4, copyPRound_length]
          cases inc
          · simp; omega
          · simp; omega

/-! ### 11c. `S6` の値を `Cnt` へ移す -/

/-- 1 単位ぶん：`S6` を 1 減らし、`Cnt` を 1 増やす。 -/
def ctrMoveRound (blank : Fin sc) : List (Act sc) :=
  [sAct .s6 blank .left, sAct .s6 blank .stay, Act.C blank .right]

theorem ctrMoveRound_noNewAll (blank : Fin sc) : NoNewAll (ctrMoveRound blank) :=
  noNewAll_cons (sAct_noNew .s6 _ _) (noNewAll_cons (sAct_noNew .s6 _ _)
    (noNewAll_singleton (by trivial)))

theorem ctrMoveRound_run (ts : OvTapes sc) :
    applyActs blank (ctrMoveRound blank) ts
      = { ts with S6 := Tape.step blank (Tape.step blank ts.S6 blank .left) blank .stay
                  Cnt := Tape.step blank ts.Cnt blank .right } := by
  cases ts; rfl

/-- `S6` が底になるまで繰り返す。 -/
def ctrMoveLoop (blank mark : Fin sc) : ℕ → OvTapes sc → List (Act sc)
  | 0, _ => []
  | n + 1, ts =>
      if Tape.read (Tape.step blank (sGet .s6 ts) blank .left) = mark then []
      else ctrMoveRound blank
        ++ ctrMoveLoop blank mark n (applyActs blank (ctrMoveRound blank) ts)

theorem ctrMoveLoop_noNewAll (blank mark : Fin sc) :
    ∀ (n : ℕ) (ts : OvTapes sc), NoNewAll (ctrMoveLoop blank mark n ts) := by
  intro n
  induction n with
  | zero => intro ts; exact noNewAll_nil
  | succ n ih =>
      intro ts
      rw [ctrMoveLoop]
      split
      · exact noNewAll_nil
      · exact noNewAll_append (ctrMoveRound_noNewAll blank) (ih _)

/-- **`ctrMoveLoop` の正当性と長さ**。 -/
theorem ctrMoveLoop_spec (hmark : mark ≠ blank) :
    ∀ (n p c : ℕ) (ts : OvTapes sc), p ≤ n →
      Tape.CounterView' blank mark ts.S6 p → Tape.CounterView' blank mark ts.Cnt c →
      Tape.CounterView' blank mark (applyActs blank (ctrMoveLoop blank mark n ts) ts).S6 0
        ∧ Tape.CounterView' blank mark
            (applyActs blank (ctrMoveLoop blank mark n ts) ts).Cnt (c + p)
        ∧ (ctrMoveLoop blank mark n ts).length = 3 * p := by
  intro n
  induction n with
  | zero =>
      intro p c ts hp h6 hcn
      have hp0 : p = 0 := by omega
      subst hp0
      rw [show ctrMoveLoop blank mark 0 ts = [] from rfl]
      exact ⟨by simpa using h6, by simpa using hcn, rfl⟩
  | succ n ih =>
      intro p c ts hp h6 hcn
      have hSget : sGet SIdx.s6 ts = ts.S6 := rfl
      cases p with
      | zero =>
          have htest : Tape.read (Tape.step blank (sGet SIdx.s6 ts) blank .left) = mark := by
            rw [hSget]; exact (Tape.counter'_isZero_iff hmark h6).2 rfl
          rw [ctrMoveLoop, if_pos htest]
          exact ⟨by simpa using h6, by simpa using hcn, rfl⟩
      | succ k =>
          have htest : ¬ Tape.read (Tape.step blank (sGet SIdx.s6 ts) blank .left) = mark := by
            rw [hSget]
            intro hcon
            exact absurd ((Tape.counter'_isZero_iff hmark h6).1 hcon) (by omega)
          rw [ctrMoveLoop, if_neg htest]
          set ts₁ := applyActs blank (ctrMoveRound blank) ts with hts₁
          have e6 : ts₁.S6
              = Tape.step blank (Tape.step blank ts.S6 blank .left) blank .stay := by
            rw [hts₁, ctrMoveRound_run]
          have ec : ts₁.Cnt = Tape.step blank ts.Cnt blank .right := by
            rw [hts₁, ctrMoveRound_run]
          have h61 : Tape.CounterView' blank mark ts₁.S6 k := by
            rw [e6]; exact Tape.counter'_dec h6
          have hc1 : Tape.CounterView' blank mark ts₁.Cnt (c + 1) := by
            rw [ec]; exact Tape.counter'_inc hcn
          obtain ⟨g1, g2, g3⟩ := ih k (c + 1) ts₁ (by omega) h61 hc1
          rw [applyActs_append, ← hts₁, List.length_append]
          refine ⟨g1, ?_, ?_⟩
          · rw [show c + (k + 1) = c + 1 + k from by omega]; exact g2
          · rw [g3]; simp [ctrMoveRound]; omega

end EpilogueLoops


/-! ## 12. epilogue の補助：ホーム復帰と `P`/`U` の整列 -/

section EpilogueAux

variable {blank : Fin sc}

/-- 左歩きが十分長ければ添字 `0` に落ち着く（左端規則）。 -/
theorem lwalk_seq_ge {w : List (Fin sc)} :
    ∀ (k i : ℕ) (tp : TapeConfiguration sc), i ≤ k → Tape.SeqView blank tp w i →
      Tape.SeqView blank (DecompInstance.lwalk blank tp k) w 0 := by
  intro k
  induction k with
  | zero =>
      intro i tp hik h
      have : i = 0 := by omega
      subst this
      simpa [DecompInstance.lwalk] using h
  | succ k ih =>
      intro i tp hik h
      rw [DecompInstance.lwalk]
      cases i with
      | zero => exact ih 0 _ (by omega) (Tape.seq_move_left_edge h)
      | succ j => exact ih j _ (by omega) (Tape.seq_move_left h)

/-- `P` を左へ `n` 歩（読んだ記号を書き戻す）。 -/
def lwalkP (blank : Fin sc) : ℕ → OvTapes sc → List (Act sc)
  | 0, _ => []
  | n + 1, ts => Act.P .left :: lwalkP blank n (applyAct blank ts (Act.P .left))

/-- `U` を左へ `n` 歩（読んだ記号を書き戻す）。 -/
def lwalkU (blank : Fin sc) : ℕ → OvTapes sc → List (Act sc)
  | 0, _ => []
  | n + 1, ts => Act.U .left :: lwalkU blank n (applyAct blank ts (Act.U .left))

theorem lwalkP_length (blank : Fin sc) :
    ∀ (n : ℕ) (ts : OvTapes sc), (lwalkP blank n ts).length = n := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih => intro ts; rw [lwalkP, List.length_cons, ih]

theorem lwalkU_length (blank : Fin sc) :
    ∀ (n : ℕ) (ts : OvTapes sc), (lwalkU blank n ts).length = n := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih => intro ts; rw [lwalkU, List.length_cons, ih]

theorem lwalkP_run (blank : Fin sc) :
    ∀ (n : ℕ) (ts : OvTapes sc),
      applyActs blank (lwalkP blank n ts) ts
        = { ts with P := DecompInstance.lwalk blank ts.P n } := by
  intro n
  induction n with
  | zero => intro ts; cases ts; rfl
  | succ n ih =>
      intro ts
      rw [lwalkP, applyActs_cons, ih]
      cases ts; rfl

theorem lwalkU_run (blank : Fin sc) :
    ∀ (n : ℕ) (ts : OvTapes sc),
      applyActs blank (lwalkU blank n ts) ts
        = { ts with U := DecompInstance.lwalk blank ts.U n } := by
  intro n
  induction n with
  | zero => intro ts; cases ts; rfl
  | succ n ih =>
      intro ts
      rw [lwalkU, applyActs_cons, ih]
      cases ts; rfl

/-- `S1` を（添字がどこであれ）添字 `0` へ戻し、そこから右へ 1 歩。 -/
def homeS1 (blank : Fin sc) (L : ℕ) (ts : OvTapes sc) : List (Act sc) :=
  seqA blank (fun t => lwalkS blank .s1 (L + 2) t)
    (fun t => [sAct .s1 (sGet .s1 t).focus .right]) ts

theorem homeS1_noNewAll (blank : Fin sc) (L : ℕ) (ts : OvTapes sc) : NoNewAll (homeS1 blank L ts) :=
  seqA_noNewAll (fun t => lwalkS_noNewAll blank .s1 (L + 2) t)
    (fun _ => noNewAll_singleton (sAct_noNew .s1 _ _)) ts

theorem homeS1_length (blank : Fin sc) (L : ℕ) (ts : OvTapes sc) :
    (homeS1 blank L ts).length = L + 3 := by
  rw [homeS1, seqA_length, lwalkS_length]
  simp

theorem homeS1_spec (blank : Fin sc) (L : ℕ) (ts : OvTapes sc) (w : List (Fin sc)) (i : ℕ)
    (hi : i ≤ L + 2) (h : Tape.SeqView blank ts.S1 w i) (hw : 1 < w.length) :
    Tape.SeqView blank (applyActs blank (homeS1 blank L ts) ts).S1 w 1 := by
  rw [homeS1, seqA_run]
  set ts₁ := applyActs blank (lwalkS blank SIdx.s1 (L + 2) ts) ts with hts₁
  have h0 : Tape.SeqView blank ts₁.S1 w 0 := by
    have hrun := lwalkS_run blank SIdx.s1 (L + 2) ts
    show Tape.SeqView blank (sGet SIdx.s1 ts₁) w 0
    rw [hts₁, hrun]
    exact lwalk_seq_ge (L + 2) i ts.S1 hi h
  show Tape.SeqView blank (sGet SIdx.s1
    (applyActs blank [sAct SIdx.s1 (sGet SIdx.s1 ts₁).focus .right] ts₁)) w (0 + 1)
  rw [show applyActs blank [sAct SIdx.s1 (sGet SIdx.s1 ts₁).focus Move.right] ts₁
      = applyAct blank ts₁ (sAct SIdx.s1 (sGet SIdx.s1 ts₁).focus Move.right) from rfl,
    sGet_sAct_self]
  exact Tape.seq_move_right h0 (by omega)

end EpilogueAux


/-! ## 13. epilogue の部品（番人駆動の左歩き、押し込み、不変性） -/

section EpiParts

variable {blank startSym endSym mark : Fin sc}

/-- 積み終えたスタックを、末尾に空白を 1 個足した語の逐次ビューとして見る。 -/
theorem stack_to_seq_end (blank : Fin sc) (w : List (Fin sc)) (tp : TapeConfiguration sc)
    (h : Tape.StackView blank tp w.reverse) :
    Tape.SeqView blank tp (w ++ [blank]) w.length := by
  refine ⟨?_, ?_, ⟨tp.right, ?_, h.right_blanks⟩⟩
  · rw [h.left_eq, List.take_left]
  · rw [List.getElem?_append_right (le_refl _)]
    simp [h.focus_blank]
  · rw [List.drop_eq_nil_of_le (by simp)]
    simp

/-- `P` を番人 `startSym` まで左へ歩く。 -/
def toSentP (startSym : Fin sc) : ℕ → OvTapes sc → List (Act sc)
  | 0, _ => []
  | n + 1, ts =>
      if ts.P.focus = startSym then []
      else Act.P .left :: toSentP startSym n (applyAct blank ts (Act.P .left))

theorem toSentP_noNewAll (startSym : Fin sc) :
    ∀ (n : ℕ) (ts : OvTapes sc), NoNewAll (toSentP (blank := blank) startSym n ts) := by
  intro n
  induction n with
  | zero => intro ts; exact noNewAll_nil
  | succ n ih =>
      intro ts
      rw [toSentP]
      split
      · exact noNewAll_nil
      · exact noNewAll_cons (by trivial) (ih _)

/-- `U` を番人 `startSym` まで左へ歩く。 -/
def toSentU (startSym : Fin sc) : ℕ → OvTapes sc → List (Act sc)
  | 0, _ => []
  | n + 1, ts =>
      if ts.U.focus = startSym then []
      else Act.U .left :: toSentU startSym n (applyAct blank ts (Act.U .left))

theorem toSentU_noNewAll (startSym : Fin sc) :
    ∀ (n : ℕ) (ts : OvTapes sc), NoNewAll (toSentU (blank := blank) startSym n ts) := by
  intro n
  induction n with
  | zero => intro ts; exact noNewAll_nil
  | succ n ih =>
      intro ts
      rw [toSentU]
      split
      · exact noNewAll_nil
      · exact noNewAll_cons (by trivial) (ih _)

/-- 番人駆動の左歩きの正当性（`P`）。 -/
theorem toSentP_spec {v : List (Fin sc)} (hv : startSym ∉ v) :
    ∀ (n i : ℕ) (ts : OvTapes sc), i ≤ n →
      Tape.SeqView blank ts.P (startSym :: v) i →
      Tape.SeqView blank (applyActs blank (toSentP (blank := blank) startSym n ts) ts).P
          (startSym :: v) 0
        ∧ (toSentP (blank := blank) startSym n ts).length = i := by
  intro n
  induction n with
  | zero =>
      intro i ts hi h
      have : i = 0 := by omega
      subst this
      rw [show toSentP (blank := blank) startSym 0 ts = [] from rfl]
      exact ⟨by simpa using h, rfl⟩
  | succ n ih =>
      intro i ts hi h
      cases i with
      | zero =>
          have hf : ts.P.focus = startSym := by
            have := h.focus_eq
            simp at this
            exact this.symm
          rw [toSentP, if_pos hf]
          exact ⟨by simpa using h, rfl⟩
      | succ j =>
          have hf : ¬ ts.P.focus = startSym := by
            intro hc
            have := h.focus_eq
            rw [List.getElem?_cons_succ] at this
            exact hv (hc ▸ (List.getElem?_eq_some_iff.1 this).2 ▸
              List.getElem_mem (List.getElem?_eq_some_iff.1 this).1)
          rw [toSentP, if_neg hf, applyActs_cons]
          have hstep : (applyAct blank ts (Act.P .left)).P
              = Tape.step blank ts.P ts.P.focus .left := rfl
          have h' : Tape.SeqView blank (applyAct blank ts (Act.P .left)).P (startSym :: v) j := by
            rw [hstep]; exact Tape.seq_move_left h
          obtain ⟨g1, g2⟩ := ih j (applyAct blank ts (Act.P .left)) (by omega) h'
          exact ⟨g1, by rw [List.length_cons, g2]⟩

/-- 番人駆動の左歩きの正当性（`U`）。 -/
theorem toSentU_spec {v : List (Fin sc)} (hv : startSym ∉ v) :
    ∀ (n i : ℕ) (ts : OvTapes sc), i ≤ n →
      Tape.SeqView blank ts.U (startSym :: v) i →
      Tape.SeqView blank (applyActs blank (toSentU (blank := blank) startSym n ts) ts).U
          (startSym :: v) 0
        ∧ (toSentU (blank := blank) startSym n ts).length = i := by
  intro n
  induction n with
  | zero =>
      intro i ts hi h
      have : i = 0 := by omega
      subst this
      rw [show toSentU (blank := blank) startSym 0 ts = [] from rfl]
      exact ⟨by simpa using h, rfl⟩
  | succ n ih =>
      intro i ts hi h
      cases i with
      | zero =>
          have hf : ts.U.focus = startSym := by
            have := h.focus_eq
            simp at this
            exact this.symm
          rw [toSentU, if_pos hf]
          exact ⟨by simpa using h, rfl⟩
      | succ j =>
          have hf : ¬ ts.U.focus = startSym := by
            intro hc
            have := h.focus_eq
            rw [List.getElem?_cons_succ] at this
            exact hv (hc ▸ (List.getElem?_eq_some_iff.1 this).2 ▸
              List.getElem_mem (List.getElem?_eq_some_iff.1 this).1)
          rw [toSentU, if_neg hf, applyActs_cons]
          have hstep : (applyAct blank ts (Act.U .left)).U
              = Tape.step blank ts.U ts.U.focus .left := rfl
          have h' : Tape.SeqView blank (applyAct blank ts (Act.U .left)).U (startSym :: v) j := by
            rw [hstep]; exact Tape.seq_move_left h
          obtain ⟨g1, g2⟩ := ih j (applyAct blank ts (Act.U .left)) (by omega) h'
          exact ⟨g1, by rw [List.length_cons, g2]⟩

end EpiParts


/-! ### 13b. 各ループが触らないテープ -/

section Keeps

variable {blank startSym endSym mark : Fin sc}

theorem splitLoop_keep :
    ∀ (n : ℕ) (ts : OvTapes sc),
      (applyActs blank (splitLoop blank mark n ts) ts).X = ts.X
        ∧ (applyActs blank (splitLoop blank mark n ts) ts).X2 = ts.X2
        ∧ (applyActs blank (splitLoop blank mark n ts) ts).F = ts.F
        ∧ (applyActs blank (splitLoop blank mark n ts) ts).P = ts.P
        ∧ (applyActs blank (splitLoop blank mark n ts) ts).Cnt = ts.Cnt
        ∧ (applyActs blank (splitLoop blank mark n ts) ts).S2 = ts.S2
        ∧ (applyActs blank (splitLoop blank mark n ts) ts).S3 = ts.S3
        ∧ (applyActs blank (splitLoop blank mark n ts) ts).S4 = ts.S4
        ∧ (applyActs blank (splitLoop blank mark n ts) ts).S5 = ts.S5
        ∧ (applyActs blank (splitLoop blank mark n ts) ts).S6 = ts.S6
        ∧ (applyActs blank (splitLoop blank mark n ts) ts).S7 = ts.S7
        ∧ (applyActs blank (splitLoop blank mark n ts) ts).S9 = ts.S9 := by
  intro n
  induction n with
  | zero => intro ts; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
      intro ts
      rw [splitLoop]
      split
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · rw [applyActs_append]
        have h := ih (applyActs blank (splitRound blank ts) ts)
        rw [splitRound_run] at h
        exact h

theorem copyPLoop_keep (inc : Bool) :
    ∀ (n : ℕ) (ts : OvTapes sc),
      (applyActs blank (copyPLoop blank endSym inc n ts) ts).X = ts.X
        ∧ (applyActs blank (copyPLoop blank endSym inc n ts) ts).X2 = ts.X2
        ∧ (applyActs blank (copyPLoop blank endSym inc n ts) ts).F = ts.F
        ∧ (applyActs blank (copyPLoop blank endSym inc n ts) ts).U = ts.U
        ∧ (applyActs blank (copyPLoop blank endSym inc n ts) ts).S2 = ts.S2
        ∧ (applyActs blank (copyPLoop blank endSym inc n ts) ts).S3 = ts.S3
        ∧ (applyActs blank (copyPLoop blank endSym inc n ts) ts).S4 = ts.S4
        ∧ (applyActs blank (copyPLoop blank endSym inc n ts) ts).S5 = ts.S5
        ∧ (applyActs blank (copyPLoop blank endSym inc n ts) ts).S6 = ts.S6
        ∧ (applyActs blank (copyPLoop blank endSym inc n ts) ts).S7 = ts.S7
        ∧ (applyActs blank (copyPLoop blank endSym inc n ts) ts).S8 = ts.S8
        ∧ (applyActs blank (copyPLoop blank endSym inc n ts) ts).S9 = ts.S9 := by
  intro n
  induction n with
  | zero => intro ts; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
      intro ts
      rw [copyPLoop]
      split
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · rw [applyActs_append]
        have h := ih (applyActs blank (copyPRound blank inc ts) ts)
        cases inc
        · rw [copyPRound_run_false] at h; exact h
        · rw [copyPRound_run_true] at h; exact h

theorem ctrMoveLoop_keep :
    ∀ (n : ℕ) (ts : OvTapes sc),
      (applyActs blank (ctrMoveLoop blank mark n ts) ts).X = ts.X
        ∧ (applyActs blank (ctrMoveLoop blank mark n ts) ts).X2 = ts.X2
        ∧ (applyActs blank (ctrMoveLoop blank mark n ts) ts).F = ts.F
        ∧ (applyActs blank (ctrMoveLoop blank mark n ts) ts).P = ts.P
        ∧ (applyActs blank (ctrMoveLoop blank mark n ts) ts).U = ts.U
        ∧ (applyActs blank (ctrMoveLoop blank mark n ts) ts).S1 = ts.S1
        ∧ (applyActs blank (ctrMoveLoop blank mark n ts) ts).S2 = ts.S2
        ∧ (applyActs blank (ctrMoveLoop blank mark n ts) ts).S3 = ts.S3
        ∧ (applyActs blank (ctrMoveLoop blank mark n ts) ts).S4 = ts.S4
        ∧ (applyActs blank (ctrMoveLoop blank mark n ts) ts).S5 = ts.S5
        ∧ (applyActs blank (ctrMoveLoop blank mark n ts) ts).S7 = ts.S7
        ∧ (applyActs blank (ctrMoveLoop blank mark n ts) ts).S8 = ts.S8
        ∧ (applyActs blank (ctrMoveLoop blank mark n ts) ts).S9 = ts.S9 := by
  intro n
  induction n with
  | zero => intro ts; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
      intro ts
      rw [ctrMoveLoop]
      split
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · rw [applyActs_append]
        have h := ih (applyActs blank (ctrMoveRound blank) ts)
        rw [ctrMoveRound_run] at h
        exact h

theorem toSentP_keep :
    ∀ (n : ℕ) (ts : OvTapes sc),
      applyActs blank (toSentP (blank := blank) startSym n ts) ts
        = { ts with P := (applyActs blank (toSentP (blank := blank) startSym n ts) ts).P } := by
  intro n
  induction n with
  | zero => intro ts; cases ts; rfl
  | succ n ih =>
      intro ts
      rw [toSentP]
      split
      · cases ts; rfl
      · rw [applyActs_cons]
        have h := ih (applyAct blank ts (Act.P .left))
        rw [h]
        cases ts
        rfl

theorem toSentU_keep :
    ∀ (n : ℕ) (ts : OvTapes sc),
      applyActs blank (toSentU (blank := blank) startSym n ts) ts
        = { ts with U := (applyActs blank (toSentU (blank := blank) startSym n ts) ts).U } := by
  intro n
  induction n with
  | zero => intro ts; cases ts; rfl
  | succ n ih =>
      intro ts
      rw [toSentU]
      split
      · cases ts; rfl
      · rw [applyActs_cons]
        have h := ih (applyAct blank ts (Act.U .left))
        rw [h]
        cases ts
        rfl

theorem homeS1_main (L : ℕ) (ts : OvTapes sc) :
    (applyActs blank (homeS1 blank L ts) ts).P = ts.P
      ∧ (applyActs blank (homeS1 blank L ts) ts).X = ts.X
      ∧ (applyActs blank (homeS1 blank L ts) ts).Cnt = ts.Cnt
      ∧ (applyActs blank (homeS1 blank L ts) ts).U = ts.U
      ∧ (applyActs blank (homeS1 blank L ts) ts).X2 = ts.X2
      ∧ (applyActs blank (homeS1 blank L ts) ts).F = ts.F := by
  rw [homeS1, seqA_run]
  set ts₁ := applyActs blank (lwalkS blank SIdx.s1 (L + 2) ts) ts with hts₁
  have hm := lwalkS_main (blank := blank) SIdx.s1 (L + 2) ts
  rw [← hts₁] at hm
  have hs := sAct_main (blank := blank) SIdx.s1 (sGet SIdx.s1 ts₁).focus Move.right ts₁
  rw [show applyActs blank [sAct SIdx.s1 (sGet SIdx.s1 ts₁).focus Move.right] ts₁
      = applyAct blank ts₁ (sAct SIdx.s1 (sGet SIdx.s1 ts₁).focus Move.right) from rfl]
  exact ⟨by rw [hs.1, hm.1], by rw [hs.2.1, hm.2.1], by rw [hs.2.2.1, hm.2.2.1],
    by rw [hs.2.2.2.1, hm.2.2.2.1], by rw [hs.2.2.2.2.1, hm.2.2.2.2.1],
    by rw [hs.2.2.2.2.2, hm.2.2.2.2.2]⟩

theorem homeS1_slot {j : SIdx} (hj : j ≠ .s1) (L : ℕ) (ts : OvTapes sc) :
    sGet j (applyActs blank (homeS1 blank L ts) ts) = sGet j ts := by
  rw [homeS1, seqA_run]
  set ts₁ := applyActs blank (lwalkS blank SIdx.s1 (L + 2) ts) ts with hts₁
  have ho : sGet j ts₁ = sGet j ts := by rw [hts₁]; exact lwalkS_other blank hj _ _
  rw [show applyActs blank [sAct SIdx.s1 (sGet SIdx.s1 ts₁).focus Move.right] ts₁
      = applyAct blank ts₁ (sAct SIdx.s1 (sGet SIdx.s1 ts₁).focus Move.right) from rfl,
    sGet_sAct_ne hj, ho]

end Keeps


/-! ## 14. 作業テープ 9 本のまとめ消去（内容依存の長さ） -/

section ClearAll

variable {blank mark : Fin sc}

/-- 1 動作でスロットの左文脈は高々 1 しか伸びない。 -/
theorem left_len_step (blank : Fin sc) (i : SIdx) (a : Act sc) (ts : OvTapes sc) :
    (sGet i (applyAct blank ts a)).left.length ≤ (sGet i ts).left.length + 1 := by
  cases a <;> cases i <;>
    first
      | exact Nat.le_succ _
      | exact PrepInstance.left_length_step_le blank _ _ _

/-- 動作列を通した単調性。 -/
theorem left_len_applyActs (blank : Fin sc) (i : SIdx) :
    ∀ (l : List (Act sc)) (ts : OvTapes sc),
      (sGet i (applyActs blank l ts)).left.length ≤ (sGet i ts).left.length + l.length := by
  intro l
  induction l with
  | nil => intro ts; simp
  | cons a l ih =>
      intro ts
      rw [applyActs_cons, List.length_cons]
      have h1 := left_len_step blank i a ts
      have h2 := ih (applyAct blank ts a)
      omega

/-- `SeqView` 形のスロットを、ヘッド位置をテープから読んで消去する。 -/
def clearSlotSeq (blank : Fin sc) (i : SIdx) (wlen : ℕ) (ts : OvTapes sc) : List (Act sc) :=
  clearSeqProgS blank i (sGet i ts).left.length (wlen - (sGet i ts).left.length - 1)

/-- カウンタ形のスロットを、値をテープから読んで消去する。 -/
def clearSlotCtr (blank : Fin sc) (i : SIdx) (ts : OvTapes sc) : List (Act sc) :=
  clearCtrProg blank i ((sGet i ts).left.length - 1)

theorem clearSlotSeq_spec (i : SIdx) (wlen : ℕ) (ts : OvTapes sc) (w : List (Fin sc)) (p : ℕ)
    (hw : Tape.SeqView blank (sGet i ts) w p) (hlen : w.length = wlen) :
    Tape.StackView blank (sGet i (applyActs blank (clearSlotSeq blank i wlen ts) ts)) [] := by
  have hp : (sGet i ts).left.length = p := by
    rw [hw.left_eq, List.length_reverse, List.length_take]
    have := hw.lt; omega
  rw [clearSlotSeq, hp]
  exact clearSeqProgS_spec i p (wlen - p - 1) ts w hw (by omega)

theorem clearSlotSeq_length (i : SIdx) (wlen : ℕ) (ts : OvTapes sc) (w : List (Fin sc)) (p : ℕ)
    (hw : Tape.SeqView blank (sGet i ts) w p) (hlen : w.length = wlen) :
    (clearSlotSeq blank i wlen ts).length = 3 * p + 2 * (wlen - p - 1) + 3 := by
  have hp : (sGet i ts).left.length = p := by
    rw [hw.left_eq, List.length_reverse, List.length_take]
    have := hw.lt; omega
  rw [clearSlotSeq, hp, clearSeqProgS_length]

theorem clearSlotSeq_other {i j : SIdx} (h : j ≠ i) (wlen : ℕ) (ts : OvTapes sc) :
    sGet j (applyActs blank (clearSlotSeq blank i wlen ts) ts) = sGet j ts :=
  clearSeqProgS_other h _ _ ts

theorem clearSlotSeq_main (i : SIdx) (wlen : ℕ) (ts : OvTapes sc) :
    (applyActs blank (clearSlotSeq blank i wlen ts) ts).P = ts.P
      ∧ (applyActs blank (clearSlotSeq blank i wlen ts) ts).X = ts.X
      ∧ (applyActs blank (clearSlotSeq blank i wlen ts) ts).Cnt = ts.Cnt
      ∧ (applyActs blank (clearSlotSeq blank i wlen ts) ts).U = ts.U
      ∧ (applyActs blank (clearSlotSeq blank i wlen ts) ts).X2 = ts.X2
      ∧ (applyActs blank (clearSlotSeq blank i wlen ts) ts).F = ts.F :=
  clearSeqProgS_main i _ _ ts

theorem clearSlotSeq_noNewAll (i : SIdx) (wlen : ℕ) (ts : OvTapes sc) :
    NoNewAll (clearSlotSeq blank i wlen ts) :=
  clearSeqProgS_noNewAll i _ _

theorem clearSlotCtr_noNewAll (i : SIdx) (ts : OvTapes sc) :
    NoNewAll (clearSlotCtr blank i ts) :=
  clearCtrProg_noNewAll i _

theorem clearSlotCtr_spec (i : SIdx) (ts : OvTapes sc) (n : ℕ)
    (h : Tape.CounterView' blank mark (sGet i ts) n) :
    Tape.StackView blank (sGet i (applyActs blank (clearSlotCtr blank i ts) ts)) [] := by
  have hp : (sGet i ts).left.length = n + 1 := by rw [h.left_eq]; simp
  rw [clearSlotCtr, hp]
  simpa using clearCtrProg_spec (mark := mark) i n ts h

theorem clearSlotCtr_length (i : SIdx) (ts : OvTapes sc) (n : ℕ)
    (h : Tape.CounterView' blank mark (sGet i ts) n) :
    (clearSlotCtr blank i ts).length = n + 2 := by
  have hp : (sGet i ts).left.length = n + 1 := by rw [h.left_eq]; simp
  rw [clearSlotCtr, hp, clearCtrProg_length]
  simp

theorem clearSlotCtr_other {i j : SIdx} (h : j ≠ i) (ts : OvTapes sc) :
    sGet j (applyActs blank (clearSlotCtr blank i ts) ts) = sGet j ts :=
  clearCtrProg_other h _ ts

theorem clearSlotCtr_main (i : SIdx) (ts : OvTapes sc) :
    (applyActs blank (clearSlotCtr blank i ts) ts).P = ts.P
      ∧ (applyActs blank (clearSlotCtr blank i ts) ts).X = ts.X
      ∧ (applyActs blank (clearSlotCtr blank i ts) ts).Cnt = ts.Cnt
      ∧ (applyActs blank (clearSlotCtr blank i ts) ts).U = ts.U
      ∧ (applyActs blank (clearSlotCtr blank i ts) ts).X2 = ts.X2
      ∧ (applyActs blank (clearSlotCtr blank i ts) ts).F = ts.F :=
  clearCtrProg_main i _ ts

/-- **作業テープ 9 本をまとめて消去する動作列**。 -/
def clearAllS (blank : Fin sc) (L : ℕ) (ts : OvTapes sc) : List (Act sc) :=
  seqA blank (fun t => clearSlotSeq blank .s1 (L + 2) t)
    (seqA blank (fun t => clearSlotSeq blank .s2 (L + 2) t)
      (seqA blank (fun t => clearSlotCtr blank .s3 t)
        (seqA blank (fun t => clearSlotCtr blank .s4 t)
          (seqA blank (fun t => clearSlotCtr blank .s5 t)
            (seqA blank (fun t => clearSlotCtr blank .s6 t)
              (seqA blank (fun t => clearSlotCtr blank .s7 t)
                (seqA blank (fun t => clearSlotCtr blank .s8 t)
                  (fun t => clearSlotCtr blank .s9 t)))))))) ts

theorem clearAllS_noNewAll (L : ℕ) (ts : OvTapes sc) : NoNewAll (clearAllS blank L ts) := by
  refine seqA_noNewAll (fun t => clearSlotSeq_noNewAll .s1 (L + 2) t)
    (fun t => seqA_noNewAll (fun t => clearSlotSeq_noNewAll .s2 (L + 2) t)
      (fun t => seqA_noNewAll (fun t => clearSlotCtr_noNewAll .s3 t)
        (fun t => seqA_noNewAll (fun t => clearSlotCtr_noNewAll .s4 t)
          (fun t => seqA_noNewAll (fun t => clearSlotCtr_noNewAll .s5 t)
            (fun t => seqA_noNewAll (fun t => clearSlotCtr_noNewAll .s6 t)
              (fun t => seqA_noNewAll (fun t => clearSlotCtr_noNewAll .s7 t)
                (fun t => seqA_noNewAll (fun t => clearSlotCtr_noNewAll .s8 t)
                  (fun t => clearSlotCtr_noNewAll .s9 t) t) t) t) t) t) t) t) ts

/-- **9 本まとめ消去の正当性と長さ**。 -/
theorem clearAllS_spec (L : ℕ) (ts : OvTapes sc) (w1 w2 : List (Fin sc))
    (p1 p2 n3 n4 n5 n6 n7 n8 n9 : ℕ)
    (hw1 : Tape.SeqView blank ts.S1 w1 p1) (hl1 : w1.length = L + 2)
    (hw2 : Tape.SeqView blank ts.S2 w2 p2) (hl2 : w2.length = L + 2)
    (h3 : Tape.CounterView' blank mark ts.S3 n3)
    (h4 : Tape.CounterView' blank mark ts.S4 n4)
    (h5 : Tape.CounterView' blank mark ts.S5 n5)
    (h6 : Tape.CounterView' blank mark ts.S6 n6)
    (h7 : Tape.CounterView' blank mark ts.S7 n7)
    (h8 : Tape.CounterView' blank mark ts.S8 n8)
    (h9 : Tape.CounterView' blank mark ts.S9 n9)
    (h10 : Tape.StackView blank ts.S10 []) (h11 : Tape.StackView blank ts.S11 []) :
    ScratchBlank blank (applyActs blank (clearAllS blank L ts) ts)
      ∧ (applyActs blank (clearAllS blank L ts) ts).P = ts.P
      ∧ (applyActs blank (clearAllS blank L ts) ts).X = ts.X
      ∧ (applyActs blank (clearAllS blank L ts) ts).Cnt = ts.Cnt
      ∧ (applyActs blank (clearAllS blank L ts) ts).U = ts.U
      ∧ (applyActs blank (clearAllS blank L ts) ts).X2 = ts.X2
      ∧ (applyActs blank (clearAllS blank L ts) ts).F = ts.F
      ∧ (clearAllS blank L ts).length
          ≤ 6 * L + 26 + (n3 + n4 + n5 + n6 + n7 + n8 + n9) := by
  obtain ⟨u1, hu1⟩ : ∃ t, applyActs blank (clearSlotSeq blank SIdx.s1 (L + 2) ts) ts = t := ⟨_, rfl⟩
  obtain ⟨u2, hu2⟩ : ∃ t, applyActs blank (clearSlotSeq blank SIdx.s2 (L + 2) u1) u1 = t := ⟨_, rfl⟩
  obtain ⟨u3, hu3⟩ : ∃ t, applyActs blank (clearSlotCtr blank SIdx.s3 u2) u2 = t := ⟨_, rfl⟩
  obtain ⟨u4, hu4⟩ : ∃ t, applyActs blank (clearSlotCtr blank SIdx.s4 u3) u3 = t := ⟨_, rfl⟩
  obtain ⟨u5, hu5⟩ : ∃ t, applyActs blank (clearSlotCtr blank SIdx.s5 u4) u4 = t := ⟨_, rfl⟩
  obtain ⟨u6, hu6⟩ : ∃ t, applyActs blank (clearSlotCtr blank SIdx.s6 u5) u5 = t := ⟨_, rfl⟩
  obtain ⟨u7, hu7⟩ : ∃ t, applyActs blank (clearSlotCtr blank SIdx.s7 u6) u6 = t := ⟨_, rfl⟩
  obtain ⟨u8, hu8⟩ : ∃ t, applyActs blank (clearSlotCtr blank SIdx.s8 u7) u7 = t := ⟨_, rfl⟩
  obtain ⟨u9, hu9⟩ : ∃ t, applyActs blank (clearSlotCtr blank SIdx.s9 u8) u8 = t := ⟨_, rfl⟩
  have v1 : sGet SIdx.s1 ts = sGet SIdx.s1 ts := rfl
  have v2 : sGet SIdx.s2 u1 = sGet SIdx.s2 ts := by
    have e2_1 : sGet SIdx.s2 u1 = sGet SIdx.s2 ts := by
      rw [← hu1]; exact clearSlotSeq_other (show SIdx.s2 ≠ SIdx.s1 by decide) (L + 2) ts
    rw [e2_1]
  have v3 : sGet SIdx.s3 u2 = sGet SIdx.s3 ts := by
    have e3_1 : sGet SIdx.s3 u1 = sGet SIdx.s3 ts := by
      rw [← hu1]; exact clearSlotSeq_other (show SIdx.s3 ≠ SIdx.s1 by decide) (L + 2) ts
    have e3_2 : sGet SIdx.s3 u2 = sGet SIdx.s3 u1 := by
      rw [← hu2]; exact clearSlotSeq_other (show SIdx.s3 ≠ SIdx.s2 by decide) (L + 2) u1
    rw [e3_2, e3_1]
  have v4 : sGet SIdx.s4 u3 = sGet SIdx.s4 ts := by
    have e4_1 : sGet SIdx.s4 u1 = sGet SIdx.s4 ts := by
      rw [← hu1]; exact clearSlotSeq_other (show SIdx.s4 ≠ SIdx.s1 by decide) (L + 2) ts
    have e4_2 : sGet SIdx.s4 u2 = sGet SIdx.s4 u1 := by
      rw [← hu2]; exact clearSlotSeq_other (show SIdx.s4 ≠ SIdx.s2 by decide) (L + 2) u1
    have e4_3 : sGet SIdx.s4 u3 = sGet SIdx.s4 u2 := by
      rw [← hu3]; exact clearSlotCtr_other (show SIdx.s4 ≠ SIdx.s3 by decide) u2
    rw [e4_3, e4_2, e4_1]
  have v5 : sGet SIdx.s5 u4 = sGet SIdx.s5 ts := by
    have e5_1 : sGet SIdx.s5 u1 = sGet SIdx.s5 ts := by
      rw [← hu1]; exact clearSlotSeq_other (show SIdx.s5 ≠ SIdx.s1 by decide) (L + 2) ts
    have e5_2 : sGet SIdx.s5 u2 = sGet SIdx.s5 u1 := by
      rw [← hu2]; exact clearSlotSeq_other (show SIdx.s5 ≠ SIdx.s2 by decide) (L + 2) u1
    have e5_3 : sGet SIdx.s5 u3 = sGet SIdx.s5 u2 := by
      rw [← hu3]; exact clearSlotCtr_other (show SIdx.s5 ≠ SIdx.s3 by decide) u2
    have e5_4 : sGet SIdx.s5 u4 = sGet SIdx.s5 u3 := by
      rw [← hu4]; exact clearSlotCtr_other (show SIdx.s5 ≠ SIdx.s4 by decide) u3
    rw [e5_4, e5_3, e5_2, e5_1]
  have v6 : sGet SIdx.s6 u5 = sGet SIdx.s6 ts := by
    have e6_1 : sGet SIdx.s6 u1 = sGet SIdx.s6 ts := by
      rw [← hu1]; exact clearSlotSeq_other (show SIdx.s6 ≠ SIdx.s1 by decide) (L + 2) ts
    have e6_2 : sGet SIdx.s6 u2 = sGet SIdx.s6 u1 := by
      rw [← hu2]; exact clearSlotSeq_other (show SIdx.s6 ≠ SIdx.s2 by decide) (L + 2) u1
    have e6_3 : sGet SIdx.s6 u3 = sGet SIdx.s6 u2 := by
      rw [← hu3]; exact clearSlotCtr_other (show SIdx.s6 ≠ SIdx.s3 by decide) u2
    have e6_4 : sGet SIdx.s6 u4 = sGet SIdx.s6 u3 := by
      rw [← hu4]; exact clearSlotCtr_other (show SIdx.s6 ≠ SIdx.s4 by decide) u3
    have e6_5 : sGet SIdx.s6 u5 = sGet SIdx.s6 u4 := by
      rw [← hu5]; exact clearSlotCtr_other (show SIdx.s6 ≠ SIdx.s5 by decide) u4
    rw [e6_5, e6_4, e6_3, e6_2, e6_1]
  have v7 : sGet SIdx.s7 u6 = sGet SIdx.s7 ts := by
    have e7_1 : sGet SIdx.s7 u1 = sGet SIdx.s7 ts := by
      rw [← hu1]; exact clearSlotSeq_other (show SIdx.s7 ≠ SIdx.s1 by decide) (L + 2) ts
    have e7_2 : sGet SIdx.s7 u2 = sGet SIdx.s7 u1 := by
      rw [← hu2]; exact clearSlotSeq_other (show SIdx.s7 ≠ SIdx.s2 by decide) (L + 2) u1
    have e7_3 : sGet SIdx.s7 u3 = sGet SIdx.s7 u2 := by
      rw [← hu3]; exact clearSlotCtr_other (show SIdx.s7 ≠ SIdx.s3 by decide) u2
    have e7_4 : sGet SIdx.s7 u4 = sGet SIdx.s7 u3 := by
      rw [← hu4]; exact clearSlotCtr_other (show SIdx.s7 ≠ SIdx.s4 by decide) u3
    have e7_5 : sGet SIdx.s7 u5 = sGet SIdx.s7 u4 := by
      rw [← hu5]; exact clearSlotCtr_other (show SIdx.s7 ≠ SIdx.s5 by decide) u4
    have e7_6 : sGet SIdx.s7 u6 = sGet SIdx.s7 u5 := by
      rw [← hu6]; exact clearSlotCtr_other (show SIdx.s7 ≠ SIdx.s6 by decide) u5
    rw [e7_6, e7_5, e7_4, e7_3, e7_2, e7_1]
  have v8 : sGet SIdx.s8 u7 = sGet SIdx.s8 ts := by
    have e8_1 : sGet SIdx.s8 u1 = sGet SIdx.s8 ts := by
      rw [← hu1]; exact clearSlotSeq_other (show SIdx.s8 ≠ SIdx.s1 by decide) (L + 2) ts
    have e8_2 : sGet SIdx.s8 u2 = sGet SIdx.s8 u1 := by
      rw [← hu2]; exact clearSlotSeq_other (show SIdx.s8 ≠ SIdx.s2 by decide) (L + 2) u1
    have e8_3 : sGet SIdx.s8 u3 = sGet SIdx.s8 u2 := by
      rw [← hu3]; exact clearSlotCtr_other (show SIdx.s8 ≠ SIdx.s3 by decide) u2
    have e8_4 : sGet SIdx.s8 u4 = sGet SIdx.s8 u3 := by
      rw [← hu4]; exact clearSlotCtr_other (show SIdx.s8 ≠ SIdx.s4 by decide) u3
    have e8_5 : sGet SIdx.s8 u5 = sGet SIdx.s8 u4 := by
      rw [← hu5]; exact clearSlotCtr_other (show SIdx.s8 ≠ SIdx.s5 by decide) u4
    have e8_6 : sGet SIdx.s8 u6 = sGet SIdx.s8 u5 := by
      rw [← hu6]; exact clearSlotCtr_other (show SIdx.s8 ≠ SIdx.s6 by decide) u5
    have e8_7 : sGet SIdx.s8 u7 = sGet SIdx.s8 u6 := by
      rw [← hu7]; exact clearSlotCtr_other (show SIdx.s8 ≠ SIdx.s7 by decide) u6
    rw [e8_7, e8_6, e8_5, e8_4, e8_3, e8_2, e8_1]
  have v9 : sGet SIdx.s9 u8 = sGet SIdx.s9 ts := by
    have e9_1 : sGet SIdx.s9 u1 = sGet SIdx.s9 ts := by
      rw [← hu1]; exact clearSlotSeq_other (show SIdx.s9 ≠ SIdx.s1 by decide) (L + 2) ts
    have e9_2 : sGet SIdx.s9 u2 = sGet SIdx.s9 u1 := by
      rw [← hu2]; exact clearSlotSeq_other (show SIdx.s9 ≠ SIdx.s2 by decide) (L + 2) u1
    have e9_3 : sGet SIdx.s9 u3 = sGet SIdx.s9 u2 := by
      rw [← hu3]; exact clearSlotCtr_other (show SIdx.s9 ≠ SIdx.s3 by decide) u2
    have e9_4 : sGet SIdx.s9 u4 = sGet SIdx.s9 u3 := by
      rw [← hu4]; exact clearSlotCtr_other (show SIdx.s9 ≠ SIdx.s4 by decide) u3
    have e9_5 : sGet SIdx.s9 u5 = sGet SIdx.s9 u4 := by
      rw [← hu5]; exact clearSlotCtr_other (show SIdx.s9 ≠ SIdx.s5 by decide) u4
    have e9_6 : sGet SIdx.s9 u6 = sGet SIdx.s9 u5 := by
      rw [← hu6]; exact clearSlotCtr_other (show SIdx.s9 ≠ SIdx.s6 by decide) u5
    have e9_7 : sGet SIdx.s9 u7 = sGet SIdx.s9 u6 := by
      rw [← hu7]; exact clearSlotCtr_other (show SIdx.s9 ≠ SIdx.s7 by decide) u6
    have e9_8 : sGet SIdx.s9 u8 = sGet SIdx.s9 u7 := by
      rw [← hu8]; exact clearSlotCtr_other (show SIdx.s9 ≠ SIdx.s8 by decide) u7
    rw [e9_8, e9_7, e9_6, e9_5, e9_4, e9_3, e9_2, e9_1]
  have sp1 : Tape.StackView blank (sGet SIdx.s1 u1) [] := by
    rw [← hu1]
    exact clearSlotSeq_spec SIdx.s1 (L + 2) ts w1 p1 (by rw [v1]; exact hw1) hl1
  have ln1 : (clearSlotSeq blank SIdx.s1 (L + 2) ts).length = 3 * p1 + 2 * (L + 2 - p1 - 1) + 3 :=
    clearSlotSeq_length SIdx.s1 (L + 2) ts w1 p1 (by rw [v1]; exact hw1) hl1
  have pb1 : p1 ≤ L + 1 := by
    have hlt := hw1.lt
    rw [hl1] at hlt
    omega
  have sp2 : Tape.StackView blank (sGet SIdx.s2 u2) [] := by
    rw [← hu2]
    exact clearSlotSeq_spec SIdx.s2 (L + 2) u1 w2 p2 (by rw [v2]; exact hw2) hl2
  have ln2 : (clearSlotSeq blank SIdx.s2 (L + 2) u1).length = 3 * p2 + 2 * (L + 2 - p2 - 1) + 3 :=
    clearSlotSeq_length SIdx.s2 (L + 2) u1 w2 p2 (by rw [v2]; exact hw2) hl2
  have pb2 : p2 ≤ L + 1 := by
    have hlt := hw2.lt
    rw [hl2] at hlt
    omega
  have sp3 : Tape.StackView blank (sGet SIdx.s3 u3) [] := by
    rw [← hu3]
    exact clearSlotCtr_spec (mark := mark) SIdx.s3 u2 n3 (by rw [v3]; exact h3)
  have ln3 : (clearSlotCtr blank SIdx.s3 u2).length = n3 + 2 :=
    clearSlotCtr_length (mark := mark) SIdx.s3 u2 n3 (by rw [v3]; exact h3)
  have sp4 : Tape.StackView blank (sGet SIdx.s4 u4) [] := by
    rw [← hu4]
    exact clearSlotCtr_spec (mark := mark) SIdx.s4 u3 n4 (by rw [v4]; exact h4)
  have ln4 : (clearSlotCtr blank SIdx.s4 u3).length = n4 + 2 :=
    clearSlotCtr_length (mark := mark) SIdx.s4 u3 n4 (by rw [v4]; exact h4)
  have sp5 : Tape.StackView blank (sGet SIdx.s5 u5) [] := by
    rw [← hu5]
    exact clearSlotCtr_spec (mark := mark) SIdx.s5 u4 n5 (by rw [v5]; exact h5)
  have ln5 : (clearSlotCtr blank SIdx.s5 u4).length = n5 + 2 :=
    clearSlotCtr_length (mark := mark) SIdx.s5 u4 n5 (by rw [v5]; exact h5)
  have sp6 : Tape.StackView blank (sGet SIdx.s6 u6) [] := by
    rw [← hu6]
    exact clearSlotCtr_spec (mark := mark) SIdx.s6 u5 n6 (by rw [v6]; exact h6)
  have ln6 : (clearSlotCtr blank SIdx.s6 u5).length = n6 + 2 :=
    clearSlotCtr_length (mark := mark) SIdx.s6 u5 n6 (by rw [v6]; exact h6)
  have sp7 : Tape.StackView blank (sGet SIdx.s7 u7) [] := by
    rw [← hu7]
    exact clearSlotCtr_spec (mark := mark) SIdx.s7 u6 n7 (by rw [v7]; exact h7)
  have ln7 : (clearSlotCtr blank SIdx.s7 u6).length = n7 + 2 :=
    clearSlotCtr_length (mark := mark) SIdx.s7 u6 n7 (by rw [v7]; exact h7)
  have sp8 : Tape.StackView blank (sGet SIdx.s8 u8) [] := by
    rw [← hu8]
    exact clearSlotCtr_spec (mark := mark) SIdx.s8 u7 n8 (by rw [v8]; exact h8)
  have ln8 : (clearSlotCtr blank SIdx.s8 u7).length = n8 + 2 :=
    clearSlotCtr_length (mark := mark) SIdx.s8 u7 n8 (by rw [v8]; exact h8)
  have sp9 : Tape.StackView blank (sGet SIdx.s9 u9) [] := by
    rw [← hu9]
    exact clearSlotCtr_spec (mark := mark) SIdx.s9 u8 n9 (by rw [v9]; exact h9)
  have ln9 : (clearSlotCtr blank SIdx.s9 u8).length = n9 + 2 :=
    clearSlotCtr_length (mark := mark) SIdx.s9 u8 n9 (by rw [v9]; exact h9)
  have wf1 : sGet SIdx.s1 u9 = sGet SIdx.s1 u1 := by
    have f1_2 : sGet SIdx.s1 u2 = sGet SIdx.s1 u1 := by
      rw [← hu2]; exact clearSlotSeq_other (show SIdx.s1 ≠ SIdx.s2 by decide) (L + 2) u1
    have f1_3 : sGet SIdx.s1 u3 = sGet SIdx.s1 u2 := by
      rw [← hu3]; exact clearSlotCtr_other (show SIdx.s1 ≠ SIdx.s3 by decide) u2
    have f1_4 : sGet SIdx.s1 u4 = sGet SIdx.s1 u3 := by
      rw [← hu4]; exact clearSlotCtr_other (show SIdx.s1 ≠ SIdx.s4 by decide) u3
    have f1_5 : sGet SIdx.s1 u5 = sGet SIdx.s1 u4 := by
      rw [← hu5]; exact clearSlotCtr_other (show SIdx.s1 ≠ SIdx.s5 by decide) u4
    have f1_6 : sGet SIdx.s1 u6 = sGet SIdx.s1 u5 := by
      rw [← hu6]; exact clearSlotCtr_other (show SIdx.s1 ≠ SIdx.s6 by decide) u5
    have f1_7 : sGet SIdx.s1 u7 = sGet SIdx.s1 u6 := by
      rw [← hu7]; exact clearSlotCtr_other (show SIdx.s1 ≠ SIdx.s7 by decide) u6
    have f1_8 : sGet SIdx.s1 u8 = sGet SIdx.s1 u7 := by
      rw [← hu8]; exact clearSlotCtr_other (show SIdx.s1 ≠ SIdx.s8 by decide) u7
    have f1_9 : sGet SIdx.s1 u9 = sGet SIdx.s1 u8 := by
      rw [← hu9]; exact clearSlotCtr_other (show SIdx.s1 ≠ SIdx.s9 by decide) u8
    rw [f1_9, f1_8, f1_7, f1_6, f1_5, f1_4, f1_3, f1_2]
  have wf2 : sGet SIdx.s2 u9 = sGet SIdx.s2 u2 := by
    have f2_3 : sGet SIdx.s2 u3 = sGet SIdx.s2 u2 := by
      rw [← hu3]; exact clearSlotCtr_other (show SIdx.s2 ≠ SIdx.s3 by decide) u2
    have f2_4 : sGet SIdx.s2 u4 = sGet SIdx.s2 u3 := by
      rw [← hu4]; exact clearSlotCtr_other (show SIdx.s2 ≠ SIdx.s4 by decide) u3
    have f2_5 : sGet SIdx.s2 u5 = sGet SIdx.s2 u4 := by
      rw [← hu5]; exact clearSlotCtr_other (show SIdx.s2 ≠ SIdx.s5 by decide) u4
    have f2_6 : sGet SIdx.s2 u6 = sGet SIdx.s2 u5 := by
      rw [← hu6]; exact clearSlotCtr_other (show SIdx.s2 ≠ SIdx.s6 by decide) u5
    have f2_7 : sGet SIdx.s2 u7 = sGet SIdx.s2 u6 := by
      rw [← hu7]; exact clearSlotCtr_other (show SIdx.s2 ≠ SIdx.s7 by decide) u6
    have f2_8 : sGet SIdx.s2 u8 = sGet SIdx.s2 u7 := by
      rw [← hu8]; exact clearSlotCtr_other (show SIdx.s2 ≠ SIdx.s8 by decide) u7
    have f2_9 : sGet SIdx.s2 u9 = sGet SIdx.s2 u8 := by
      rw [← hu9]; exact clearSlotCtr_other (show SIdx.s2 ≠ SIdx.s9 by decide) u8
    rw [f2_9, f2_8, f2_7, f2_6, f2_5, f2_4, f2_3]
  have wf3 : sGet SIdx.s3 u9 = sGet SIdx.s3 u3 := by
    have f3_4 : sGet SIdx.s3 u4 = sGet SIdx.s3 u3 := by
      rw [← hu4]; exact clearSlotCtr_other (show SIdx.s3 ≠ SIdx.s4 by decide) u3
    have f3_5 : sGet SIdx.s3 u5 = sGet SIdx.s3 u4 := by
      rw [← hu5]; exact clearSlotCtr_other (show SIdx.s3 ≠ SIdx.s5 by decide) u4
    have f3_6 : sGet SIdx.s3 u6 = sGet SIdx.s3 u5 := by
      rw [← hu6]; exact clearSlotCtr_other (show SIdx.s3 ≠ SIdx.s6 by decide) u5
    have f3_7 : sGet SIdx.s3 u7 = sGet SIdx.s3 u6 := by
      rw [← hu7]; exact clearSlotCtr_other (show SIdx.s3 ≠ SIdx.s7 by decide) u6
    have f3_8 : sGet SIdx.s3 u8 = sGet SIdx.s3 u7 := by
      rw [← hu8]; exact clearSlotCtr_other (show SIdx.s3 ≠ SIdx.s8 by decide) u7
    have f3_9 : sGet SIdx.s3 u9 = sGet SIdx.s3 u8 := by
      rw [← hu9]; exact clearSlotCtr_other (show SIdx.s3 ≠ SIdx.s9 by decide) u8
    rw [f3_9, f3_8, f3_7, f3_6, f3_5, f3_4]
  have wf4 : sGet SIdx.s4 u9 = sGet SIdx.s4 u4 := by
    have f4_5 : sGet SIdx.s4 u5 = sGet SIdx.s4 u4 := by
      rw [← hu5]; exact clearSlotCtr_other (show SIdx.s4 ≠ SIdx.s5 by decide) u4
    have f4_6 : sGet SIdx.s4 u6 = sGet SIdx.s4 u5 := by
      rw [← hu6]; exact clearSlotCtr_other (show SIdx.s4 ≠ SIdx.s6 by decide) u5
    have f4_7 : sGet SIdx.s4 u7 = sGet SIdx.s4 u6 := by
      rw [← hu7]; exact clearSlotCtr_other (show SIdx.s4 ≠ SIdx.s7 by decide) u6
    have f4_8 : sGet SIdx.s4 u8 = sGet SIdx.s4 u7 := by
      rw [← hu8]; exact clearSlotCtr_other (show SIdx.s4 ≠ SIdx.s8 by decide) u7
    have f4_9 : sGet SIdx.s4 u9 = sGet SIdx.s4 u8 := by
      rw [← hu9]; exact clearSlotCtr_other (show SIdx.s4 ≠ SIdx.s9 by decide) u8
    rw [f4_9, f4_8, f4_7, f4_6, f4_5]
  have wf5 : sGet SIdx.s5 u9 = sGet SIdx.s5 u5 := by
    have f5_6 : sGet SIdx.s5 u6 = sGet SIdx.s5 u5 := by
      rw [← hu6]; exact clearSlotCtr_other (show SIdx.s5 ≠ SIdx.s6 by decide) u5
    have f5_7 : sGet SIdx.s5 u7 = sGet SIdx.s5 u6 := by
      rw [← hu7]; exact clearSlotCtr_other (show SIdx.s5 ≠ SIdx.s7 by decide) u6
    have f5_8 : sGet SIdx.s5 u8 = sGet SIdx.s5 u7 := by
      rw [← hu8]; exact clearSlotCtr_other (show SIdx.s5 ≠ SIdx.s8 by decide) u7
    have f5_9 : sGet SIdx.s5 u9 = sGet SIdx.s5 u8 := by
      rw [← hu9]; exact clearSlotCtr_other (show SIdx.s5 ≠ SIdx.s9 by decide) u8
    rw [f5_9, f5_8, f5_7, f5_6]
  have wf6 : sGet SIdx.s6 u9 = sGet SIdx.s6 u6 := by
    have f6_7 : sGet SIdx.s6 u7 = sGet SIdx.s6 u6 := by
      rw [← hu7]; exact clearSlotCtr_other (show SIdx.s6 ≠ SIdx.s7 by decide) u6
    have f6_8 : sGet SIdx.s6 u8 = sGet SIdx.s6 u7 := by
      rw [← hu8]; exact clearSlotCtr_other (show SIdx.s6 ≠ SIdx.s8 by decide) u7
    have f6_9 : sGet SIdx.s6 u9 = sGet SIdx.s6 u8 := by
      rw [← hu9]; exact clearSlotCtr_other (show SIdx.s6 ≠ SIdx.s9 by decide) u8
    rw [f6_9, f6_8, f6_7]
  have wf7 : sGet SIdx.s7 u9 = sGet SIdx.s7 u7 := by
    have f7_8 : sGet SIdx.s7 u8 = sGet SIdx.s7 u7 := by
      rw [← hu8]; exact clearSlotCtr_other (show SIdx.s7 ≠ SIdx.s8 by decide) u7
    have f7_9 : sGet SIdx.s7 u9 = sGet SIdx.s7 u8 := by
      rw [← hu9]; exact clearSlotCtr_other (show SIdx.s7 ≠ SIdx.s9 by decide) u8
    rw [f7_9, f7_8]
  have wf8 : sGet SIdx.s8 u9 = sGet SIdx.s8 u8 := by
    have f8_9 : sGet SIdx.s8 u9 = sGet SIdx.s8 u8 := by
      rw [← hu9]; exact clearSlotCtr_other (show SIdx.s8 ≠ SIdx.s9 by decide) u8
    rw [f8_9]
  have wf9 : sGet SIdx.s9 u9 = sGet SIdx.s9 u9 := rfl
  have hrun : applyActs blank (clearAllS blank L ts) ts = u9 := by
    rw [clearAllS, seqA_run, seqA_run, seqA_run, seqA_run, seqA_run, seqA_run, seqA_run,
      seqA_run, hu1, hu2, hu3, hu4, hu5, hu6, hu7, hu8, hu9]
  have hlen : (clearAllS blank L ts).length = (clearSlotSeq blank SIdx.s1 (L + 2) ts).length + (clearSlotSeq blank SIdx.s2 (L + 2) u1).length + (clearSlotCtr blank SIdx.s3 u2).length + (clearSlotCtr blank SIdx.s4 u3).length + (clearSlotCtr blank SIdx.s5 u4).length + (clearSlotCtr blank SIdx.s6 u5).length + (clearSlotCtr blank SIdx.s7 u6).length + (clearSlotCtr blank SIdx.s8 u7).length + (clearSlotCtr blank SIdx.s9 u8).length := by
    rw [clearAllS, seqA_length, seqA_length, seqA_length, seqA_length, seqA_length,
      seqA_length, seqA_length, seqA_length, hu1, hu2, hu3, hu4, hu5, hu6, hu7, hu8]
    omega
  have m1 := clearSlotSeq_main (blank := blank) SIdx.s1 (L + 2) ts
  rw [hu1] at m1
  have m2 := clearSlotSeq_main (blank := blank) SIdx.s2 (L + 2) u1
  rw [hu2] at m2
  have m3 := clearSlotCtr_main (blank := blank) SIdx.s3 u2
  rw [hu3] at m3
  have m4 := clearSlotCtr_main (blank := blank) SIdx.s4 u3
  rw [hu4] at m4
  have m5 := clearSlotCtr_main (blank := blank) SIdx.s5 u4
  rw [hu5] at m5
  have m6 := clearSlotCtr_main (blank := blank) SIdx.s6 u5
  rw [hu6] at m6
  have m7 := clearSlotCtr_main (blank := blank) SIdx.s7 u6
  rw [hu7] at m7
  have m8 := clearSlotCtr_main (blank := blank) SIdx.s8 u7
  rw [hu8] at m8
  have m9 := clearSlotCtr_main (blank := blank) SIdx.s9 u8
  rw [hu9] at m9
  have hkeepNew := applyActs_keepNew (blank := blank) (clearAllS blank L ts) ts
    (clearAllS_noNewAll L ts)
  have sp10 : Tape.StackView blank u9.S10 [] := by rw [← hrun]; rw [hkeepNew.1]; exact h10
  have sp11 : Tape.StackView blank u9.S11 [] := by rw [← hrun]; rw [hkeepNew.2]; exact h11
  rw [hrun]
  refine ⟨⟨by have hh := sp1; rw [← wf1] at hh; exact hh, by have hh := sp2; rw [← wf2] at hh; exact hh, by have hh := sp3; rw [← wf3] at hh; exact hh, by have hh := sp4; rw [← wf4] at hh; exact hh, by have hh := sp5; rw [← wf5] at hh; exact hh, by have hh := sp6; rw [← wf6] at hh; exact hh, by have hh := sp7; rw [← wf7] at hh; exact hh, by have hh := sp8; rw [← wf8] at hh; exact hh, by have hh := sp9; rw [← wf9] at hh; exact hh, sp10, sp11⟩,
    by rw [m9.1, m8.1, m7.1, m6.1, m5.1, m4.1, m3.1, m2.1, m1.1],
    by rw [m9.2.1, m8.2.1, m7.2.1, m6.2.1, m5.2.1, m4.2.1, m3.2.1, m2.2.1, m1.2.1],
    by rw [m9.2.2.1, m8.2.2.1, m7.2.2.1, m6.2.2.1, m5.2.2.1, m4.2.2.1, m3.2.2.1, m2.2.2.1, m1.2.2.1],
    by rw [m9.2.2.2.1, m8.2.2.2.1, m7.2.2.2.1, m6.2.2.2.1, m5.2.2.2.1, m4.2.2.2.1, m3.2.2.2.1, m2.2.2.2.1, m1.2.2.2.1],
    by rw [m9.2.2.2.2.1, m8.2.2.2.2.1, m7.2.2.2.2.1, m6.2.2.2.2.1, m5.2.2.2.2.1, m4.2.2.2.2.1, m3.2.2.2.2.1, m2.2.2.2.2.1, m1.2.2.2.2.1],
    by rw [m9.2.2.2.2.2, m8.2.2.2.2.2, m7.2.2.2.2.2, m6.2.2.2.2.2, m5.2.2.2.2.2, m4.2.2.2.2.2, m3.2.2.2.2.2, m2.2.2.2.2.2, m1.2.2.2.2.2],
    ?_⟩
  rw [hlen, ln1, ln2, ln3, ln4, ln5, ln6, ln7, ln8, ln9]
  omega

end ClearAll


/-! ## 15. epilogue -/

section Epilogue

variable {blank startSym endSym mark : Fin sc}

theorem run_Pset (a : Fin sc) (m : Move) (ts : OvTapes sc) :
    applyActs blank [Act.Pset a m] ts = { ts with P := Tape.step blank ts.P a m } := by
  cases ts; rfl

theorem run_Uset (a : Fin sc) (m : Move) (ts : OvTapes sc) :
    applyActs blank [Act.Uset a m] ts = { ts with U := Tape.step blank ts.U a m } := by
  cases ts; rfl

theorem run_Cset (a : Fin sc) (m : Move) (ts : OvTapes sc) :
    applyActs blank [Act.C a m] ts = { ts with Cnt := Tape.step blank ts.Cnt a m } := by
  cases ts; rfl

theorem run_Pmove (m : Move) (ts : OvTapes sc) :
    applyActs blank [Act.P m] ts = { ts with P := Tape.step blank ts.P ts.P.focus m } := by
  cases ts; rfl

theorem run_Umove (m : Move) (ts : OvTapes sc) :
    applyActs blank [Act.U m] ts = { ts with U := Tape.step blank ts.U ts.U.focus m } := by
  cases ts; rfl

theorem run_pushPU (a : Fin sc) (ts : OvTapes sc) :
    applyActs blank [Act.Pset a .right, Act.Uset a .right] ts
      = { ts with P := Tape.step blank ts.P a .right
                  U := Tape.step blank ts.U a .right } := by
  cases ts; rfl

/-- `Cnt` に載せる値を決める分岐：`S6`（生の周期）が `0` なら `|x.drop s| + 1` を
数えながら作り、そうでなければ `S6` の値を移す。 -/
def cntBranch (blank endSym mark : Fin sc) (L : ℕ) (ts : OvTapes sc) : List (Act sc) :=
  if Tape.read (Tape.step blank (sGet .s6 ts) blank .left) = mark then
    seqA blank (fun t => copyPLoop blank endSym true (L + 1) t)
      (fun _ => [Act.C blank .right]) ts
  else
    seqA blank (fun t => copyPLoop blank endSym false (L + 1) t)
      (fun t => ctrMoveLoop blank mark (L + 1) t) ts

theorem cntBranch_noNewAll (blank endSym mark : Fin sc) (L : ℕ) (ts : OvTapes sc) :
    NoNewAll (cntBranch blank endSym mark L ts) := by
  rw [cntBranch]
  split
  · exact seqA_noNewAll (fun t => copyPLoop_noNewAll blank endSym true (L + 1) t)
      (fun _ => noNewAll_singleton (by trivial)) ts
  · exact seqA_noNewAll (fun t => copyPLoop_noNewAll blank endSym false (L + 1) t)
      (fun t => ctrMoveLoop_noNewAll blank mark (L + 1) t) ts

/-- **一様な epilogue**。 -/
def epilogueU (blank startSym endSym mark : Fin sc) (L : ℕ) (ts : OvTapes sc) : List (Act sc) :=
  seqA blank (fun t => homeS1 blank L t)
    (seqA blank (fun _ => [Act.Pset startSym .right, Act.Uset startSym .right])
      (seqA blank (fun t => splitLoop blank mark (L + 1) t)
        (seqA blank (fun _ => [Act.Uset endSym .right])
          (seqA blank (fun t => toSentU (blank := blank) startSym (L + 3) t)
            (seqA blank (fun _ => [Act.U .right])
              (seqA blank (fun _ => [Act.C mark .right])
                (seqA blank (fun t => cntBranch blank endSym mark L t)
                  (seqA blank (fun _ => [Act.Pset endSym .right])
                    (seqA blank (fun t => toSentP (blank := blank) startSym (L + 3) t)
                      (seqA blank (fun _ => [Act.P .right])
                        (fun t => clearAllS blank L t))))))))))) ts

/-- **`cntBranch` の正当性と長さ**。 -/
theorem cntBranch_spec {x : List (Fin sc)} (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (L s p1raw : ℕ) (hx : x.length = L) (hs : s ≤ L) (hp : p1raw ≤ L + 1)
    (ts : OvTapes sc) (l : List (Fin sc))
    (hS1 : Tape.SeqView blank ts.S1 (GSPre.pword startSym endSym x) (s + 1))
    (hP : Tape.StackView blank ts.P l)
    (hCnt : Tape.CounterView' blank mark ts.Cnt 0)
    (hS6 : Tape.CounterView' blank mark ts.S6 p1raw) :
    Tape.SeqView blank (applyActs blank (cntBranch blank endSym mark L ts) ts).S1
        (GSPre.pword startSym endSym x) (L + 1)
      ∧ Tape.StackView blank (applyActs blank (cntBranch blank endSym mark L ts) ts).P
          ((x.drop s).reverse ++ l)
      ∧ Tape.CounterView' blank mark
          (applyActs blank (cntBranch blank endSym mark L ts) ts).Cnt
          (if p1raw = 0 then (L - s) + 1 else p1raw)
      ∧ Tape.CounterView' blank mark
          (applyActs blank (cntBranch blank endSym mark L ts) ts).S6 0
      ∧ (applyActs blank (cntBranch blank endSym mark L ts) ts).X = ts.X
      ∧ (applyActs blank (cntBranch blank endSym mark L ts) ts).X2 = ts.X2
      ∧ (applyActs blank (cntBranch blank endSym mark L ts) ts).F = ts.F
      ∧ (applyActs blank (cntBranch blank endSym mark L ts) ts).U = ts.U
      ∧ (applyActs blank (cntBranch blank endSym mark L ts) ts).S2 = ts.S2
      ∧ (applyActs blank (cntBranch blank endSym mark L ts) ts).S3 = ts.S3
      ∧ (applyActs blank (cntBranch blank endSym mark L ts) ts).S4 = ts.S4
      ∧ (applyActs blank (cntBranch blank endSym mark L ts) ts).S5 = ts.S5
      ∧ (applyActs blank (cntBranch blank endSym mark L ts) ts).S7 = ts.S7
      ∧ (applyActs blank (cntBranch blank endSym mark L ts) ts).S8 = ts.S8
      ∧ (applyActs blank (cntBranch blank endSym mark L ts) ts).S9 = ts.S9
      ∧ (cntBranch blank endSym mark L ts).length ≤ 3 * L + 3 * p1raw + 1 := by
  have hfuel : x.length - s ≤ L + 1 := by omega
  by_cases hz : p1raw = 0
  · subst hz
    have htest : Tape.read (Tape.step blank (sGet SIdx.s6 ts) blank .left) = mark :=
      (Tape.counter'_isZero_iff hmark hS6).2 rfl
    rw [cntBranch, if_pos htest, seqA_run, seqA_length]
    obtain ⟨g1, g2, g3, g4⟩ := copyPLoop_spec (startSym := startSym) (mark := mark) hend true
      (L + 1) s 0 ts l hfuel (by omega) hS1 hP hCnt
    obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12⟩ :=
      copyPLoop_keep (blank := blank) (endSym := endSym) true (L + 1) ts
    set t1 := applyActs blank (copyPLoop blank endSym true (L + 1) ts) ts with ht1
    rw [run_Cset]
    refine ⟨by rw [hx] at g1; exact g1, g2, ?_, ?_, k1, k2, k3, k4, k5, k6, k7, k8, k10,
      k11, k12, ?_⟩
    · show Tape.CounterView' blank mark (Tape.step blank t1.Cnt blank .right) _
      have : (0 : ℕ) + (x.length - s) + 1 = (L - s) + 1 := by rw [hx]; omega
      rw [← this]
      exact Tape.counter'_inc (by simpa using g3)
    · show Tape.CounterView' blank mark t1.S6 0
      rw [k9]; exact hS6
    · rw [g4]
      have h3 : (if (true : Bool) = true then 3 else 2) = 3 := rfl
      rw [h3, hx]
      simp only [List.length_cons, List.length_nil]
      omega
  · have htest : ¬ Tape.read (Tape.step blank (sGet SIdx.s6 ts) blank .left) = mark := by
      intro hcon
      exact hz ((Tape.counter'_isZero_iff hmark hS6).1 hcon)
    rw [cntBranch, if_neg htest, seqA_run, seqA_length]
    obtain ⟨g1, g2, g3, g4⟩ := copyPLoop_spec (startSym := startSym) (mark := mark) hend false
      (L + 1) s 0 ts l hfuel (by omega) hS1 hP hCnt
    obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12⟩ :=
      copyPLoop_keep (blank := blank) (endSym := endSym) false (L + 1) ts
    set t1 := applyActs blank (copyPLoop blank endSym false (L + 1) ts) ts with ht1
    have h6 : Tape.CounterView' blank mark t1.S6 p1raw := by rw [k9]; exact hS6
    obtain ⟨c1, c2, c3⟩ := ctrMoveLoop_spec (blank := blank) hmark (L + 1) p1raw 0 t1
      (by omega) h6 (by simpa using g3)
    obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13⟩ :=
      ctrMoveLoop_keep (blank := blank) (mark := mark) (L + 1) t1
    refine ⟨?_, ?_, ?_, c1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hg := g1
      rw [hx] at hg
      rw [d6]; exact hg
    · rw [d4]; exact g2
    · rw [if_neg hz]; simpa using c2
    · rw [d1, k1]
    · rw [d2, k2]
    · rw [d3, k3]
    · rw [d5, k4]
    · rw [d7, k5]
    · rw [d8, k6]
    · rw [d9, k7]
    · rw [d10, k8]
    · rw [d11, k10]
    · rw [d12, k11]
    · rw [d13, k12]
    · rw [g4, c3]
      have h2 : (if (false : Bool) = true then 3 else 2) = 2 := rfl
      rw [h2, hx]
      omega

/-- **epilogue の正当性と長さ**。 -/
theorem epilogueU_spec {x : List (Fin sc)} {L s p1raw D Q E r a b : ℕ}
    (hmark : mark ≠ blank) (hend : endSym ∉ x) (hstart : startSym ∉ x)
    (hse : startSym ≠ endSym) (hsb : startSym ≠ blank)
    (hx : x.length = L) (hs : s ≤ L) (hp : p1raw ≤ L + 1)
    (ts : OvTapes sc)
    (hE : GSPre.Enc blank startSym endSym mark x a b ⟨D, Q, E, p1raw, 0, s, r⟩
      (DecompInstance.prjB ts))
    (hP0 : Tape.StackView blank ts.P []) (hU0 : Tape.StackView blank ts.U [])
    (hC0 : Tape.StackView blank ts.Cnt [])
    (hS10 : Tape.StackView blank ts.S10 []) (hS11 : Tape.StackView blank ts.S11 []) :
    Tape.SeqView blank (applyActs blank (epilogueU blank startSym endSym mark L ts) ts).P
        (startSym :: (x.drop s ++ [endSym])) 1
      ∧ Tape.SeqView blank (applyActs blank (epilogueU blank startSym endSym mark L ts) ts).U
          (startSym :: (x.take s ++ [endSym])) 1
      ∧ Tape.CounterView' blank mark
          (applyActs blank (epilogueU blank startSym endSym mark L ts) ts).Cnt
          (if p1raw = 0 then (L - s) + 1 else p1raw)
      ∧ ScratchBlank blank (applyActs blank (epilogueU blank startSym endSym mark L ts) ts)
      ∧ (applyActs blank (epilogueU blank startSym endSym mark L ts) ts).X = ts.X
      ∧ (applyActs blank (epilogueU blank startSym endSym mark L ts) ts).X2 = ts.X2
      ∧ (applyActs blank (epilogueU blank startSym endSym mark L ts) ts).F = ts.F
      ∧ (epilogueU blank startSym endSym mark L ts).length
          ≤ 19 * L + 44 + D + Q + E + r := by
  set pw : List (Fin sc) := GSPre.pword startSym endSym x with hpw
  have hpwlen : pw.length = L + 2 := by rw [hpw, GSPre.pword_length, hx]
  have hE1 : Tape.SeqView blank ts.S1 pw (a + 1) := hE.v1
  have hE2 : Tape.SeqView blank ts.S2 pw (b + 1) := hE.v2
  have hE3 : Tape.CounterView' blank mark ts.S3 D := hE.cd
  have hE4 : Tape.CounterView' blank mark ts.S4 Q := hE.cq
  have hE5 : Tape.CounterView' blank mark ts.S5 E := hE.ce
  have hE6 : Tape.CounterView' blank mark ts.S6 p1raw := hE.cp
  have hE7 : Tape.CounterView' blank mark ts.S7 0 := hE.cf
  have hE8 : Tape.CounterView' blank mark ts.S8 s := hE.cs
  have hE9 : Tape.CounterView' blank mark ts.S9 r := hE.cr
  have hale : a ≤ L := by rw [← hx]; exact GSPre.pat_le hE1
  have hble : b ≤ L := by rw [← hx]; exact GSPre.pat_le hE2
  -- 段階
  obtain ⟨t1, e1⟩ : ∃ t, applyActs blank (homeS1 blank L ts) ts = t := ⟨_, rfl⟩
  obtain ⟨t2, e2⟩ : ∃ t,
      applyActs blank [Act.Pset startSym .right, Act.Uset startSym .right] t1 = t := ⟨_, rfl⟩
  obtain ⟨t3, e3⟩ : ∃ t, applyActs blank (splitLoop blank mark (L + 1) t2) t2 = t := ⟨_, rfl⟩
  obtain ⟨t4, e4⟩ : ∃ t, applyActs blank [Act.Uset endSym .right] t3 = t := ⟨_, rfl⟩
  obtain ⟨t5, e5⟩ : ∃ t,
      applyActs blank (toSentU (blank := blank) startSym (L + 3) t4) t4 = t := ⟨_, rfl⟩
  obtain ⟨t6, e6⟩ : ∃ t, applyActs blank [Act.U .right] t5 = t := ⟨_, rfl⟩
  obtain ⟨t7, e7⟩ : ∃ t, applyActs blank [Act.C mark .right] t6 = t := ⟨_, rfl⟩
  obtain ⟨t8, e8⟩ : ∃ t, applyActs blank (cntBranch blank endSym mark L t7) t7 = t := ⟨_, rfl⟩
  obtain ⟨t9, e9⟩ : ∃ t, applyActs blank [Act.Pset endSym .right] t8 = t := ⟨_, rfl⟩
  obtain ⟨t10, e10⟩ : ∃ t,
      applyActs blank (toSentP (blank := blank) startSym (L + 3) t9) t9 = t := ⟨_, rfl⟩
  obtain ⟨t11, e11⟩ : ∃ t, applyActs blank [Act.P .right] t10 = t := ⟨_, rfl⟩
  obtain ⟨t12, e12⟩ : ∃ t, applyActs blank (clearAllS blank L t11) t11 = t := ⟨_, rfl⟩
  -- `S10`/`S11` はこの段のどの動作にも触れられないので、入口の値がそのまま `t11` まで残る。
  have hnS10 : t11.S10 = ts.S10 := by
    have g1 := (applyActs_keepNew (blank := blank) (homeS1 blank L ts) ts (homeS1_noNewAll blank L ts)).1
    rw [e1] at g1
    have g2 := (applyActs_keepNew (blank := blank) [Act.Pset startSym .right, Act.Uset startSym .right] t1
        (noNewAll_cons (by trivial) (noNewAll_singleton (by trivial)))).1
    rw [e2] at g2
    have g3 := (applyActs_keepNew (blank := blank) (splitLoop blank mark (L + 1) t2) t2
        (splitLoop_noNewAll blank mark (L + 1) t2)).1
    rw [e3] at g3
    have g4 := (applyActs_keepNew (blank := blank) [Act.Uset endSym .right] t3 (noNewAll_singleton (by trivial))).1
    rw [e4] at g4
    have g5 := (applyActs_keepNew (blank := blank) (toSentU (blank := blank) startSym (L + 3) t4) t4
        (toSentU_noNewAll (blank := blank) startSym (L + 3) t4)).1
    rw [e5] at g5
    have g6 := (applyActs_keepNew (blank := blank) [Act.U .right] t5 (noNewAll_singleton (by trivial))).1
    rw [e6] at g6
    have g7 := (applyActs_keepNew (blank := blank) [Act.C mark .right] t6 (noNewAll_singleton (by trivial))).1
    rw [e7] at g7
    have g8 := (applyActs_keepNew (blank := blank) (cntBranch blank endSym mark L t7) t7
        (cntBranch_noNewAll blank endSym mark L t7)).1
    rw [e8] at g8
    have g9 := (applyActs_keepNew (blank := blank) [Act.Pset endSym .right] t8 (noNewAll_singleton (by trivial))).1
    rw [e9] at g9
    have g10 := (applyActs_keepNew (blank := blank) (toSentP (blank := blank) startSym (L + 3) t9) t9
        (toSentP_noNewAll (blank := blank) startSym (L + 3) t9)).1
    rw [e10] at g10
    have g11 := (applyActs_keepNew (blank := blank) [Act.P .right] t10 (noNewAll_singleton (by trivial))).1
    rw [e11] at g11
    rw [g11, g10, g9, g8, g7, g6, g5, g4, g3, g2, g1]
  have hnS11 : t11.S11 = ts.S11 := by
    have g1 := (applyActs_keepNew (blank := blank) (homeS1 blank L ts) ts (homeS1_noNewAll blank L ts)).2
    rw [e1] at g1
    have g2 := (applyActs_keepNew (blank := blank) [Act.Pset startSym .right, Act.Uset startSym .right] t1
        (noNewAll_cons (by trivial) (noNewAll_singleton (by trivial)))).2
    rw [e2] at g2
    have g3 := (applyActs_keepNew (blank := blank) (splitLoop blank mark (L + 1) t2) t2
        (splitLoop_noNewAll blank mark (L + 1) t2)).2
    rw [e3] at g3
    have g4 := (applyActs_keepNew (blank := blank) [Act.Uset endSym .right] t3 (noNewAll_singleton (by trivial))).2
    rw [e4] at g4
    have g5 := (applyActs_keepNew (blank := blank) (toSentU (blank := blank) startSym (L + 3) t4) t4
        (toSentU_noNewAll (blank := blank) startSym (L + 3) t4)).2
    rw [e5] at g5
    have g6 := (applyActs_keepNew (blank := blank) [Act.U .right] t5 (noNewAll_singleton (by trivial))).2
    rw [e6] at g6
    have g7 := (applyActs_keepNew (blank := blank) [Act.C mark .right] t6 (noNewAll_singleton (by trivial))).2
    rw [e7] at g7
    have g8 := (applyActs_keepNew (blank := blank) (cntBranch blank endSym mark L t7) t7
        (cntBranch_noNewAll blank endSym mark L t7)).2
    rw [e8] at g8
    have g9 := (applyActs_keepNew (blank := blank) [Act.Pset endSym .right] t8 (noNewAll_singleton (by trivial))).2
    rw [e9] at g9
    have g10 := (applyActs_keepNew (blank := blank) (toSentP (blank := blank) startSym (L + 3) t9) t9
        (toSentP_noNewAll (blank := blank) startSym (L + 3) t9)).2
    rw [e10] at g10
    have g11 := (applyActs_keepNew (blank := blank) [Act.P .right] t10 (noNewAll_singleton (by trivial))).2
    rw [e11] at g11
    rw [g11, g10, g9, g8, g7, g6, g5, g4, g3, g2, g1]
  have h11S10 : Tape.StackView blank t11.S10 [] := by rw [hnS10]; exact hS10
  have h11S11 : Tape.StackView blank t11.S11 [] := by rw [hnS11]; exact hS11
  have hrun : applyActs blank (epilogueU blank startSym endSym mark L ts) ts = t12 := by
    rw [epilogueU, seqA_run, seqA_run, seqA_run, seqA_run, seqA_run, seqA_run, seqA_run,
      seqA_run, seqA_run, seqA_run, seqA_run, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12]
  rw [hrun]
  -- ## 段階 1：`S1` を添字 1 へ
  have h1S1 : Tape.SeqView blank t1.S1 pw 1 := by
    rw [← e1]
    exact homeS1_spec blank L ts pw (a + 1) (by omega) hE1 (by omega)
  have h1main := homeS1_main (blank := blank) L ts
  rw [e1] at h1main
  have h1slot : ∀ j : SIdx, j ≠ .s1 → sGet j t1 = sGet j ts := by
    intro j hj; rw [← e1]; exact homeS1_slot hj L ts
  -- ## 段階 2：`P`/`U` に番人
  have he2 : t2 = { t1 with P := Tape.step blank t1.P startSym .right
                            U := Tape.step blank t1.U startSym .right } := by
    rw [← e2, run_pushPU]
  have h2P : Tape.StackView blank t2.P [startSym] := by
    rw [he2]
    have : Tape.StackView blank t1.P [] := by rw [h1main.1]; exact hP0
    simpa using Tape.push_spec this startSym
  have h2U : Tape.StackView blank t2.U [startSym] := by
    rw [he2]
    have : Tape.StackView blank t1.U [] := by rw [h1main.2.2.2.1]; exact hU0
    simpa using Tape.push_spec this startSym
  have h2S1 : Tape.SeqView blank t2.S1 pw 1 := by rw [he2]; exact h1S1
  have h2S8 : Tape.CounterView' blank mark t2.S8 s := by
    rw [he2]
    have := h1slot .s8 (by decide)
    show Tape.CounterView' blank mark (sGet SIdx.s8 t1) s
    rw [this]; exact hE8
  -- ## 段階 3：切り出し
  have hsplit := splitLoop_spec (blank := blank) hmark (L + 1) s 1 t2 pw [startSym]
    (by omega) (by rw [hpwlen]; omega) h2S8 h2S1 h2U
  rw [e3] at hsplit
  obtain ⟨h3S1, h3U, h3S8, h3len⟩ := hsplit
  have hkeep3 := splitLoop_keep (blank := blank) (mark := mark) (L + 1) t2
  rw [e3] at hkeep3
  have htakes : ((pw.take (1 + s)).drop 1) = x.take s := by
    rw [hpw, GSPre.pword]
    rw [show 1 + s = s + 1 from by omega]
    rw [List.take_succ_cons, List.drop_succ_cons, List.drop_zero,
      List.take_append_of_le_length (by omega : s ≤ x.length)]
  rw [htakes] at h3U
  -- ## 段階 4：`U` に `endSym`
  set uw : List (Fin sc) := startSym :: (x.take s ++ [endSym]) with huw
  have htkl : (x.take s).length = s := by rw [List.length_take]; omega
  have huwlen : uw.length = s + 2 := by
    rw [huw, List.length_cons, List.length_append, htkl, List.length_singleton]
  have huwrev : uw.reverse = endSym :: ((x.take s).reverse ++ [startSym]) := by
    rw [huw]; simp
  have he4 : t4 = { t3 with U := Tape.step blank t3.U endSym .right } := by
    rw [← e4, run_Uset]
  have h4U : Tape.StackView blank t4.U uw.reverse := by
    rw [he4, huwrev]; exact Tape.push_spec h3U endSym
  -- ## 段階 5, 6：`U` を添字 1 へ
  have h4seq : Tape.SeqView blank t4.U (uw ++ [blank]) (s + 2) := by
    have := stack_to_seq_end blank uw t4.U h4U
    rwa [huwlen] at this
  have hvne : startSym ∉ ((x.take s ++ [endSym]) ++ [blank]) := by
    intro hc
    rcases List.mem_append.1 hc with hc | hc
    · rcases List.mem_append.1 hc with hc | hc
      · exact hstart (List.mem_of_mem_take hc)
      · exact hse (by simpa using hc)
    · exact hsb (by simpa using hc)
  have huwb : uw ++ [blank] = startSym :: ((x.take s ++ [endSym]) ++ [blank]) := by
    rw [huw]; rfl
  obtain ⟨h5U, h5len⟩ := toSentU_spec (blank := blank) hvne (L + 3) (s + 2) t4
    (by omega) (by rw [← huwb]; exact h4seq)
  rw [e5] at h5U
  have h5keep : t5 = { t4 with U := t5.U } := by rw [← e5]; exact toSentU_keep (L + 3) t4
  have he6 : t6 = { t5 with U := Tape.step blank t5.U t5.U.focus .right } := by
    rw [← e6, run_Umove]
  have h6U : Tape.SeqView blank t6.U uw 1 := by
    rw [he6]
    have h5U' : Tape.SeqView blank t5.U (uw ++ [blank]) 0 := by rw [huwb]; exact h5U
    have hstep := Tape.seq_move_right h5U' (by rw [List.length_append, huwlen]; omega)
    exact DecompInstance.seqView_shrink hstep (fun c hc => by simpa using hc)
      (by rw [huwlen]; omega)
  -- ## 段階 7：`Cnt` を 0 に
  have hCnt6 : Tape.StackView blank t6.Cnt [] := by
    have c1 : t1.Cnt = ts.Cnt := h1main.2.2.1
    have c2 : t2.Cnt = t1.Cnt := by rw [he2]
    have c3 : t3.Cnt = t2.Cnt := hkeep3.2.2.2.2.1
    have c4 : t4.Cnt = t3.Cnt := by rw [he4]
    have c5 : t5.Cnt = t4.Cnt := by rw [h5keep]
    have c6 : t6.Cnt = t5.Cnt := by rw [he6]
    rw [c6, c5, c4, c3, c2, c1]; exact hC0
  have he7 : t7 = { t6 with Cnt := Tape.step blank t6.Cnt mark .right } := by
    rw [← e7, run_Cset]
  have h7Cnt : Tape.CounterView' blank mark t7.Cnt 0 := by
    rw [he7, Tape.counterView'_zero]
    simpa using Tape.push_spec hCnt6 mark
  -- 段階 7 までの `S1`, `S6`, `P`
  have h7S1 : Tape.SeqView blank t7.S1 pw (s + 1) := by
    have : t7.S1 = t3.S1 := by
      rw [he7, he6, h5keep, he4]
    rw [this]
    rw [show s + 1 = 1 + s from by omega]
    exact h3S1
  have h7P : Tape.StackView blank t7.P [startSym] := by
    have : t7.P = t2.P := by
      rw [he7, he6, h5keep, he4, hkeep3.2.2.2.1]
    rw [this]; exact h2P
  have h7S6 : Tape.CounterView' blank mark t7.S6 p1raw := by
    have : t7.S6 = t2.S6 := by
      rw [he7, he6, h5keep, he4, hkeep3.2.2.2.2.2.2.2.2.2.1]
    rw [this, he2]
    have := h1slot .s6 (by decide)
    show Tape.CounterView' blank mark (sGet SIdx.s6 t1) p1raw
    rw [this]; exact hE6
  -- ## 段階 8：分岐
  obtain ⟨h8S1, h8P, h8Cnt, h8S6, h8X, h8X2, h8F, h8U, h8S2, h8S3, h8S4, h8S5, h8S7, h8S8,
    h8S9, h8len⟩ := cntBranch_spec (blank := blank) (startSym := startSym) hend hmark L s p1raw
      hx hs hp t7 [startSym] h7S1 h7P h7Cnt h7S6
  rw [e8] at h8S1 h8P h8Cnt h8S6 h8X h8X2 h8F h8U h8S2 h8S3 h8S4 h8S5 h8S7 h8S8 h8S9
  -- ## 段階 9, 10, 11：`P` を仕上げる
  set pw' : List (Fin sc) := startSym :: (x.drop s ++ [endSym]) with hpw'
  have hdrl : (x.drop s).length = L - s := by rw [List.length_drop]; omega
  have hpw'len : pw'.length = (L - s) + 2 := by
    rw [hpw', List.length_cons, List.length_append, hdrl, List.length_singleton]
  have hpw'rev : pw'.reverse = endSym :: ((x.drop s).reverse ++ [startSym]) := by
    rw [hpw']; simp
  have he9 : t9 = { t8 with P := Tape.step blank t8.P endSym .right } := by
    rw [← e9, run_Pset]
  have h9P : Tape.StackView blank t9.P pw'.reverse := by
    rw [he9, hpw'rev]; exact Tape.push_spec h8P endSym
  have h9seq : Tape.SeqView blank t9.P (pw' ++ [blank]) ((L - s) + 2) := by
    have := stack_to_seq_end blank pw' t9.P h9P
    rwa [hpw'len] at this
  have hvne' : startSym ∉ ((x.drop s ++ [endSym]) ++ [blank]) := by
    intro hc
    rcases List.mem_append.1 hc with hc | hc
    · rcases List.mem_append.1 hc with hc | hc
      · exact hstart (List.mem_of_mem_drop hc)
      · exact hse (by simpa using hc)
    · exact hsb (by simpa using hc)
  have hpw'b : pw' ++ [blank] = startSym :: ((x.drop s ++ [endSym]) ++ [blank]) := by
    rw [hpw']; rfl
  obtain ⟨h10P, h10len⟩ := toSentP_spec (blank := blank) hvne' (L + 3) ((L - s) + 2) t9
    (by omega) (by rw [← hpw'b]; exact h9seq)
  rw [e10] at h10P
  have h10keep : t10 = { t9 with P := t10.P } := by rw [← e10]; exact toSentP_keep (L + 3) t9
  have he11 : t11 = { t10 with P := Tape.step blank t10.P t10.P.focus .right } := by
    rw [← e11, run_Pmove]
  have h11P : Tape.SeqView blank t11.P pw' 1 := by
    rw [he11]
    have h10P' : Tape.SeqView blank t10.P (pw' ++ [blank]) 0 := by rw [hpw'b]; exact h10P
    have hstep := Tape.seq_move_right h10P' (by rw [List.length_append, hpw'len]; omega)
    exact DecompInstance.seqView_shrink hstep (fun c hc => by simpa using hc)
      (by rw [hpw'len]; omega)
  -- ## 段階 12：作業テープの消去に必要なビュー
  have h11S1 : Tape.SeqView blank t11.S1 pw (L + 1) := by
    have : t11.S1 = t8.S1 := by rw [he11, h10keep, he9]
    rw [this]; exact h8S1
  have h11S2 : Tape.SeqView blank t11.S2 pw (b + 1) := by
    have hc : t11.S2 = ts.S2 := by
      rw [he11, h10keep, he9, h8S2, he7, he6, h5keep, he4, hkeep3.2.2.2.2.2.1, he2]
      have := h1slot .s2 (by decide)
      show sGet SIdx.s2 t1 = sGet SIdx.s2 ts
      exact this
    rw [hc]; exact hE2
  have h11S3 : Tape.CounterView' blank mark t11.S3 D := by
    have hc : t11.S3 = ts.S3 := by
      rw [he11, h10keep, he9, h8S3, he7, he6, h5keep, he4, hkeep3.2.2.2.2.2.2.1, he2]
      exact h1slot .s3 (by decide)
    rw [hc]; exact hE3
  have h11S4 : Tape.CounterView' blank mark t11.S4 Q := by
    have hc : t11.S4 = ts.S4 := by
      rw [he11, h10keep, he9, h8S4, he7, he6, h5keep, he4, hkeep3.2.2.2.2.2.2.2.1, he2]
      exact h1slot .s4 (by decide)
    rw [hc]; exact hE4
  have h11S5 : Tape.CounterView' blank mark t11.S5 E := by
    have hc : t11.S5 = ts.S5 := by
      rw [he11, h10keep, he9, h8S5, he7, he6, h5keep, he4,
        hkeep3.2.2.2.2.2.2.2.2.1, he2]
      exact h1slot .s5 (by decide)
    rw [hc]; exact hE5
  have h11S6 : Tape.CounterView' blank mark t11.S6 0 := by
    have hc : t11.S6 = t8.S6 := by rw [he11, h10keep, he9]
    rw [hc]; exact h8S6
  have h11S7 : Tape.CounterView' blank mark t11.S7 0 := by
    have hc : t11.S7 = ts.S7 := by
      rw [he11, h10keep, he9, h8S7, he7, he6, h5keep, he4,
        hkeep3.2.2.2.2.2.2.2.2.2.2.1, he2]
      exact h1slot .s7 (by decide)
    rw [hc]; exact hE7
  have h11S8 : Tape.CounterView' blank mark t11.S8 0 := by
    have hc : t11.S8 = t3.S8 := by
      rw [he11, h10keep, he9, h8S8, he7, he6, h5keep, he4]
    rw [hc]; exact h3S8
  have h11S9 : Tape.CounterView' blank mark t11.S9 r := by
    have hc : t11.S9 = ts.S9 := by
      rw [he11, h10keep, he9, h8S9, he7, he6, h5keep, he4,
        hkeep3.2.2.2.2.2.2.2.2.2.2.2, he2]
      exact h1slot .s9 (by decide)
    rw [hc]; exact hE9
  obtain ⟨h12sc, h12P, h12X, h12Cnt, h12U, h12X2, h12F, h12len⟩ :=
    clearAllS_spec (blank := blank) (mark := mark) L t11 pw pw (L + 1) (b + 1) D Q E 0 0 0 r
      h11S1 hpwlen h11S2 hpwlen h11S3 h11S4 h11S5 h11S6 h11S7 h11S8 h11S9 h11S10 h11S11
  rw [e12] at h12sc h12P h12X h12Cnt h12U h12X2 h12F
  -- 結論
  refine ⟨?_, ?_, ?_, h12sc, ?_, ?_, ?_, ?_⟩
  · rw [h12P]; exact h11P
  · have q1 : t11.U = t10.U := by rw [he11]
    have q2 : t10.U = t9.U := by rw [h10keep]
    have q3 : t9.U = t8.U := by rw [he9]
    have q4 : t7.U = t6.U := by rw [he7]
    rw [h12U, q1, q2, q3, h8U, q4]
    exact h6U
  · rw [h12Cnt, he11, h10keep, he9]; exact h8Cnt
  · rw [h12X, he11, h10keep, he9, h8X, he7, he6, h5keep, he4, hkeep3.1, he2]
    exact h1main.2.1
  · rw [h12X2, he11, h10keep, he9, h8X2, he7, he6, h5keep, he4, hkeep3.2.1, he2]
    exact h1main.2.2.2.2.1
  · rw [h12F, he11, h10keep, he9, h8F, he7, he6, h5keep, he4, hkeep3.2.2.1, he2]
    exact h1main.2.2.2.2.2
  · -- 長さ
    have hlen : (epilogueU blank startSym endSym mark L ts).length
        = (homeS1 blank L ts).length + 2 + (splitLoop blank mark (L + 1) t2).length + 1
          + (toSentU (blank := blank) startSym (L + 3) t4).length + 1 + 1
          + (cntBranch blank endSym mark L t7).length + 1
          + (toSentP (blank := blank) startSym (L + 3) t9).length + 1
          + (clearAllS blank L t11).length := by
      rw [epilogueU, seqA_length, seqA_length, seqA_length, seqA_length, seqA_length,
        seqA_length, seqA_length, seqA_length, seqA_length, seqA_length, seqA_length,
        e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
      simp only [List.length_cons, List.length_nil]
      omega
    rw [hlen, homeS1_length, h3len, h5len, h10len]
    omega

end Epilogue


/-! ## 16. 一様な分解器の全体 -/

section Full

variable {blank startSym endSym mark leftSym : Fin sc}

/-- **一様な分解器の動作列**：prologue（`X2` から窓を読む）＋ 分解本体 ＋ epilogue。
`y` を参照せず、テープ状態と段幅 `L` だけの関数である。 -/
def decompUniform (blank startSym endSym mark : Fin sc) (L : ℕ) (ts : OvTapes sc) :
    List (Act sc) :=
  seqA blank (fun t => prologueU blank startSym endSym mark L t)
    (seqA blank (fun t => decActsLClear blank endSym mark L t)
      (fun t => epilogueU blank startSym endSym mark L t)) ts

/-- 費用の傾き（周期和定数 `C₁` に依存）。 -/
def CdU (C₁ : ℕ) : ℕ := 826880 * C₁ + 4530185

/-- 費用の切片。 -/
def DdU : ℕ := 517475

/-- **主定理**：入口が `EntryBlank` で、`X2` が `leftSym :: y` を添字 `L` で保持していれば、
`decompUniform` は `P` / `U` / `Cnt` に `EndToEnd2.gsDec2 y 8 L` の分解を載せ、
`X` / `X2` / `F` を保ち、作業テープを空白に戻し、動作数は `L` の 1 次式で抑えられる。 -/
theorem decompUniform_spec {y : List (Fin sc)} {L C₁ : ℕ}
    (hmark : mark ≠ blank) (hend : endSym ∉ y) (hstart : startSym ∉ y)
    (hse : startSym ≠ endSym) (hsb : startSym ≠ blank)
    (hL : 1 ≤ L) (hLy : L ≤ y.length)
    (hsum : ∀ (z : List (Fin sc)) (b s' : ℕ),
      stripLoop2Periods z 8 b (z.length + 1) s' ≤ C₁ * b)
    (ts : OvTapes sc) (hEB : MiddleTapes.EntryBlank blank ts)
    (hX2 : Tape.SeqView blank ts.X2 (leftSym :: y) L) :
    Tape.SeqView blank (applyActs blank (decompUniform blank startSym endSym mark L ts) ts).P
        (startSym :: ((y.take L).drop (EndToEnd2.gsDec2 y 8 L).1 ++ [endSym])) 1
      ∧ Tape.SeqView blank
          (applyActs blank (decompUniform blank startSym endSym mark L ts) ts).U
          (startSym :: ((y.take L).take (EndToEnd2.gsDec2 y 8 L).1 ++ [endSym])) 1
      ∧ Tape.CounterView' blank mark
          (applyActs blank (decompUniform blank startSym endSym mark L ts) ts).Cnt
          (EndToEnd2.gsDec2 y 8 L).2.1
      ∧ ScratchBlank blank
          (applyActs blank (decompUniform blank startSym endSym mark L ts) ts)
      ∧ (applyActs blank (decompUniform blank startSym endSym mark L ts) ts).X = ts.X
      ∧ (applyActs blank (decompUniform blank startSym endSym mark L ts) ts).X2 = ts.X2
      ∧ (applyActs blank (decompUniform blank startSym endSym mark L ts) ts).F = ts.F
      ∧ (decompUniform blank startSym endSym mark L ts).length ≤ CdU C₁ * L + DdU := by
  set x : List (Fin sc) := y.take L with hxdef
  have hxlen : x.length = L := by rw [hxdef, List.length_take]; omega
  have hendx : endSym ∉ x := fun hc => hend (List.mem_of_mem_take hc)
  have hstartx : startSym ∉ x := fun hc => hstart (List.mem_of_mem_take hc)
  set s : ℕ := (decompose2 x 8).1 with hsdef
  set p1raw : ℕ := (decompose2 x 8).2.1 with hpdef
  set rr : ℕ := (decompose2 x 8).2.2 with hrdef
  have hH := decompose2_gsDecomp (k := 8) (by omega) x
  have hsle : s ≤ L := by
    have := hH.cut_le
    rw [← hsdef, hxlen] at this
    exact this
  have hple : p1raw ≤ L + 1 := by
    by_cases hz : p1raw = 0
    · omega
    · have hleast := hH.toGSCore.least (by rw [← hpdef]; exact hz)
      have h8 : 8 * p1raw ≤ (x.drop s).length := by
        rw [hpdef, hsdef]; exact hleast.1.2.1
      have : (x.drop s).length ≤ L := by rw [List.length_drop]; omega
      omega
  -- 段階
  obtain ⟨t1, e1⟩ : ∃ t, applyActs blank (prologueU blank startSym endSym mark L ts) ts = t :=
    ⟨_, rfl⟩
  obtain ⟨t2, e2⟩ : ∃ t, applyActs blank (decActsLClear blank endSym mark L t1) t1 = t :=
    ⟨_, rfl⟩
  obtain ⟨t3, e3⟩ : ∃ t, applyActs blank (epilogueU blank startSym endSym mark L t2) t2 = t :=
    ⟨_, rfl⟩
  have hrun : applyActs blank (decompUniform blank startSym endSym mark L ts) ts = t3 := by
    rw [decompUniform, seqA_run, seqA_run, e1, e2, e3]
  rw [hrun]
  -- prologue
  obtain ⟨hE1, k1X2, k1P, k1X, k1Cnt, k1U, k1F⟩ := prologueU_spec (blank := blank)
    (startSym := startSym) (endSym := endSym) (mark := mark) (leftSym := leftSym)
    hL hLy ts hEB.scratch hX2
  rw [e1] at hE1 k1X2 k1P k1X k1Cnt k1U k1F
  rw [← hxdef] at hE1
  -- `S10`/`S11` はどの段の動作にも触れられないので、入口の値がそのまま残る。
  have hnT1S10 : t1.S10 = ts.S10 := by
    rw [← e1]
    exact (applyActs_keepNew (blank := blank) (prologueU blank startSym endSym mark L ts) ts
      (prologueU_noNewAll ts)).1
  have hnT1S11 : t1.S11 = ts.S11 := by
    rw [← e1]
    exact (applyActs_keepNew (blank := blank) (prologueU blank startSym endSym mark L ts) ts
      (prologueU_noNewAll ts)).2
  -- 分解本体
  obtain ⟨hNlen, ⟨a, b, D, Q, E, hE2⟩, k2P, k2U, k2Cnt, k2X, k2X2, k2F⟩ :=
    decActsLClear_spec (startSym := startSym) hxlen hendx hmark t1 hE1
    (by rw [k1P]; exact hEB.p) (by rw [k1U]; exact hEB.u) (by rw [k1Cnt]; exact hEB.cnt)
  rw [e2] at hE2 k2P k2U k2Cnt k2X k2X2 k2F
  rw [← hsdef, ← hpdef, ← hrdef] at hE2
  have hnT2S10 : t2.S10 = ts.S10 := by
    rw [← e2]
    rw [(applyActs_keepNew (blank := blank) (decActsLClear blank endSym mark L t1) t1
      (decActsLClear_noNewAll L t1)).1]
    exact hnT1S10
  have hnT2S11 : t2.S11 = ts.S11 := by
    rw [← e2]
    rw [(applyActs_keepNew (blank := blank) (decActsLClear blank endSym mark L t1) t1
      (decActsLClear_noNewAll L t1)).2]
    exact hnT1S11
  -- カウンタの値は分解本体の動作数で抑えられる
  set N : ℕ := (decActsLClear blank endSym mark L t1).length with hNdef
  have hval : ∀ (i : SIdx) (v : ℕ), Tape.CounterView' blank mark (sGet i t1) 0 →
      Tape.CounterView' blank mark (sGet i t2) v → v ≤ N := by
    intro i v h0 hv
    have l0 : (sGet i t1).left.length = 1 := by rw [h0.left_eq]; simp
    have l2 : (sGet i t2).left.length = v + 1 := by rw [hv.left_eq]; simp
    have hmono := left_len_applyActs blank i (decActsLClear blank endSym mark L t1) t1
    rw [e2] at hmono
    rw [l0, l2, ← hNdef] at hmono
    omega
  have hD : D ≤ N := hval .s3 D hE1.cd hE2.cd
  have hQ : Q ≤ N := hval .s4 Q hE1.cq hE2.cq
  have hE : E ≤ N := hval .s5 E hE1.ce hE2.ce
  have hR : rr ≤ N := hval .s9 rr hE1.cr hE2.cr
  -- epilogue
  obtain ⟨h3P, h3U, h3Cnt, h3sc, h3X, h3X2, h3F, h3len⟩ := epilogueU_spec (blank := blank)
    (startSym := startSym) (endSym := endSym) (mark := mark) (x := x) (L := L) (s := s)
    (p1raw := p1raw) (D := D) (Q := Q) (E := E) (r := rr) (a := a) (b := b)
    hmark hendx hstartx hse hsb hxlen hsle hple t2 hE2 k2P k2U k2Cnt
    (by rw [hnT2S10]; exact hEB.scratch.s10) (by rw [hnT2S11]; exact hEB.scratch.s11)
  rw [e3] at h3P h3U h3Cnt h3sc h3X h3X2 h3F
  -- `gsDec2` への橋渡し
  have hfst : (EndToEnd2.gsDec2 y 8 L).1 = s := by
    rw [EndToEnd2.gsDec2_fst, ← hxdef, ← hsdef]
  have hdroplen : ((y.take L).drop s).length = L - s := by
    rw [← hxdef, List.length_drop, hxlen]
  have hsnd : (EndToEnd2.gsDec2 y 8 L).2.1 = if p1raw = 0 then (L - s) + 1 else p1raw := by
    rw [EndToEnd2.gsDec2, ← hxdef, ← hpdef, ← hsdef]
    split_ifs with hz
    · rw [hdroplen]
    · rfl
  refine ⟨by rw [hfst]; exact h3P, by rw [hfst]; exact h3U, by rw [hsnd]; exact h3Cnt, h3sc,
    by rw [h3X, k2X, k1X], by rw [h3X2, k2X2, k1X2], by rw [h3F, k2F, k1F], ?_⟩
  -- 長さ
  have hlen : (decompUniform blank startSym endSym mark L ts).length
      = (prologueU blank startSym endSym mark L ts).length + N
        + (epilogueU blank startSym endSym mark L t2).length := by
    rw [decompUniform, seqA_length, seqA_length, e1, e2, ← hNdef]
    omega
  have hwork : decompose2Work x 8 ≤ (34 * C₁ + 186) * L + 21 := by
    have h := decompose2Work_le x 8 C₁ (by omega) (fun b s' => hsum x b s')
    rw [hxlen] at h
    have harith : (4 * 8 + 2) * C₁ + 17 * 8 + 50 = 34 * C₁ + 186 := by ring
    rw [harith] at h
    omega
  have hN : N ≤ (165376 * C₁ + 906032) * L + 103484 := by
    have h1 : 304 * decompose2Work x 8 ≤ 304 * ((34 * C₁ + 186) * L + 21) :=
      Nat.mul_le_mul_left _ hwork
    have h2 : 16 * (304 * ((34 * C₁ + 186) * L + 21) + 83 * (L + 1)) + 12
        = (165376 * C₁ + 906032) * L + 103484 := by ring
    omega
  have hsum5 : 5 * N ≤ (826880 * C₁ + 4530160) * L + 517420 := by
    have h5 := Nat.mul_le_mul_left 5 hN
    have hbig : 5 * ((165376 * C₁ + 906032) * L + 103484)
        = (826880 * C₁ + 4530160) * L + 517420 := by ring
    rw [← hbig]
    exact h5
  rw [hlen, prologueU_length hL ts]
  simp only [CdU, DdU]
  have hexp : (826880 * C₁ + 4530185) * L + 517475
      = (826880 * C₁ + 4530160) * L + 517420 + (25 * L + 55) := by ring
  rw [hexp]
  omega

end Full


/-! ## 17. 一様な分解器のインタフェースと居住者

`MiddleTapes.DecompOnTapes`（および `DecompInstance.DecompOnTapesB`）の
`pat` / `upat` / `cnt` は、入口の仮定が `EntryBlank blank ts` **だけ**であり、
「`X2` が段の語 `y` を保持している」ことをどこにも要求していない。したがって
`acts` が `y` を参照しない**一様な**分解器は、その形のインタフェースを満たせない
（`X2` に何が載っていても `y` の分解を書けと要求されるため）。

そこで、入口条件に**窓の仮定**を加えたインタフェース `DecompOnTapesW` を置く。
`MiddleTapes.DecompOnTapes` 側を `EntryBlank` に直したのと同じ手当てである。 -/

section Iface

/-- **窓の仮定つきの分解器インタフェース**：`acts` は段幅 `L` とテープ状態だけの関数
（`y` を参照しない）。 -/
structure DecompOnTapesW (sc : ℕ) (blank startSym endSym mark leftSym : Fin sc) where
  /-- 計算する段の分解。 -/
  dec : List (Fin sc) → ℕ → ℕ × ℕ × ℕ
  /-- **一様な**動作列（`y` を参照しない）。 -/
  acts : ℕ → OvTapes sc → List (Act sc)
  /-- 費用の傾き。 -/
  Cd : ℕ
  /-- 費用の切片。 -/
  Dd : ℕ
  /-- 段の正当性。 -/
  decOK : ∀ (y : List (Fin sc)) (L : ℕ), 1 ≤ L →
    StageOK y 8 L (dec y L).1 (dec y L).2.1 (dec y L).2.2
  /-- 入口（`EntryBlank` ＋ `X2` に窓）からの動作。 -/
  spec : ∀ (y : List (Fin sc)) (L : ℕ), 1 ≤ L → L ≤ y.length → endSym ∉ y → startSym ∉ y →
    ∀ ts : OvTapes sc, MiddleTapes.EntryBlank blank ts →
      Tape.SeqView blank ts.X2 (leftSym :: y) L →
      Tape.SeqView blank (applyActs blank (acts L ts) ts).P
          (startSym :: ((y.take L).drop (dec y L).1 ++ [endSym])) 1
        ∧ Tape.SeqView blank (applyActs blank (acts L ts) ts).U
            (startSym :: ((y.take L).take (dec y L).1 ++ [endSym])) 1
        ∧ Tape.CounterView' blank mark (applyActs blank (acts L ts) ts).Cnt (dec y L).2.1
        ∧ ScratchBlank blank (applyActs blank (acts L ts) ts)
        ∧ (applyActs blank (acts L ts) ts).X = ts.X
        ∧ (applyActs blank (acts L ts) ts).X2 = ts.X2
        ∧ (applyActs blank (acts L ts) ts).F = ts.F
        ∧ (acts L ts).length ≤ Cd * L + Dd

/-- **一様な分解器の居住者**（`dec := EndToEnd2.gsDec2 · 8`）。 -/
def decompUniformInstance {blank startSym endSym mark leftSym : Fin sc} {C₁ : ℕ}
    (hmark : mark ≠ blank) (hse : startSym ≠ endSym) (hsb : startSym ≠ blank)
    (hsum : ∀ (z : List (Fin sc)) (b s' : ℕ),
      stripLoop2Periods z 8 b (z.length + 1) s' ≤ C₁ * b) :
    DecompOnTapesW sc blank startSym endSym mark leftSym where
  dec := fun y L => EndToEnd2.gsDec2 y 8 L
  acts := fun L ts => decompUniform blank startSym endSym mark L ts
  Cd := CdU C₁
  Dd := DdU
  decOK := fun _ _ hL => EndToEnd2.decOK2 _ _ hL
  spec := fun _ _ hL hLy hend hstart ts hEB hX2 =>
    decompUniform_spec (leftSym := leftSym) hmark hend hstart hse hsb hL hLy hsum ts hEB hX2

theorem decompUniformInstance_Cd {blank startSym endSym mark leftSym : Fin sc} {C₁ : ℕ}
    (hmark : mark ≠ blank) (hse : startSym ≠ endSym) (hsb : startSym ≠ blank)
    (hsum : ∀ (z : List (Fin sc)) (b s' : ℕ),
      stripLoop2Periods z 8 b (z.length + 1) s' ≤ C₁ * b) :
    (decompUniformInstance (leftSym := leftSym) hmark hse hsb hsum).Cd = 826880 * C₁ + 4530185 :=
  rfl

theorem decompUniformInstance_Dd {blank startSym endSym mark leftSym : Fin sc} {C₁ : ℕ}
    (hmark : mark ≠ blank) (hse : startSym ≠ endSym) (hsb : startSym ≠ blank)
    (hsum : ∀ (z : List (Fin sc)) (b s' : ℕ),
      stripLoop2Periods z 8 b (z.length + 1) s' ≤ C₁ * b) :
    (decompUniformInstance (leftSym := leftSym) hmark hse hsb hsum).Dd = 517475 :=
  rfl

/-- **`DecompOnTapesW` から `MiddleTapes.DecompOnTapes` へ**。`acts` は `y` を無視して
段幅 `L` とテープだけで決まるので、そのまま `y` 付きの形に持ち上がる。 -/
def DecompOnTapesW.toDecompOnTapes {blank startSym endSym mark leftSym : Fin sc}
    (W : DecompOnTapesW sc blank startSym endSym mark leftSym) :
    MiddleTapes.DecompOnTapes sc blank startSym endSym mark leftSym where
  dec := W.dec
  acts := fun _ L ts => W.acts L ts
  Cd := W.Cd
  Dd := W.Dd
  decOK := W.decOK
  spec := fun y L h1 h2 hend hstart ts hEB hX2 => W.spec y L h1 h2 hend hstart ts hEB hX2

/-- **`MiddleTapes.DecompOnTapes` の居住者**：一様分解器から作る。
これで `MiddleTapes` の展開は vacuous ではなくなる
（`DecompInstance.decompOnTapes_isEmpty` は古い弱い入口条件に対する結果）。 -/
def middleDecompInstance {blank startSym endSym mark leftSym : Fin sc} {C₁ : ℕ}
    (hmark : mark ≠ blank) (hse : startSym ≠ endSym) (hsb : startSym ≠ blank)
    (hsum : ∀ (z : List (Fin sc)) (b s' : ℕ),
      stripLoop2Periods z 8 b (z.length + 1) s' ≤ C₁ * b) :
    MiddleTapes.DecompOnTapes sc blank startSym endSym mark leftSym :=
  (decompUniformInstance (leftSym := leftSym) hmark hse hsb hsum).toDecompOnTapes

theorem middleDecompInstance_Cd {blank startSym endSym mark leftSym : Fin sc} {C₁ : ℕ}
    (hmark : mark ≠ blank) (hse : startSym ≠ endSym) (hsb : startSym ≠ blank)
    (hsum : ∀ (z : List (Fin sc)) (b s' : ℕ),
      stripLoop2Periods z 8 b (z.length + 1) s' ≤ C₁ * b) :
    (middleDecompInstance (leftSym := leftSym) hmark hse hsb hsum).Cd
      = 826880 * C₁ + 4530185 := rfl

theorem middleDecompInstance_Dd {blank startSym endSym mark leftSym : Fin sc} {C₁ : ℕ}
    (hmark : mark ≠ blank) (hse : startSym ≠ endSym) (hsb : startSym ≠ blank)
    (hsum : ∀ (z : List (Fin sc)) (b s' : ℕ),
      stripLoop2Periods z 8 b (z.length + 1) s' ≤ C₁ * b) :
    (middleDecompInstance (leftSym := leftSym) hmark hse hsb hsum).Dd = 517475 := rfl

end Iface

#print axioms decompUniform_spec
#print axioms prologueU_spec
#print axioms decActsL_spec
#print axioms splitLoop_spec
#print axioms copyPLoop_spec
#print axioms ctrMoveLoop_spec
#print axioms clearSeqProgS_spec
#print axioms clearCtrProg_spec
#print axioms homeS1_spec

end DecompUniform
end PalPeg
