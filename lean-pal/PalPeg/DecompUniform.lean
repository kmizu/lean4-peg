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

/-- 最後の 1 記号（`X2` は動かさない）。 -/
def copyLast (ts : OvTapes sc) : List (Act sc) :=
  [sAct .s1 ts.X2.focus .right, sAct .s2 ts.X2.focus .right]

/-- `n` 記号ぶん。 -/
def copyLoop (blank : Fin sc) : ℕ → OvTapes sc → List (Act sc)
  | 0, _ => []
  | n + 1, ts => copyRound ts ++ copyLoop blank n (applyActs blank (copyRound ts) ts)

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

/-- カウンタ 7 本（`S3 … S9`）に底のマーカを置いて値 `0` にする。 -/
def zeroCtrs (mark : Fin sc) : List (Act sc) :=
  [sAct .s3 mark .right, sAct .s4 mark .right, sAct .s5 mark .right, sAct .s6 mark .right,
    sAct .s7 mark .right, sAct .s8 mark .right, sAct .s9 mark .right]

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
  DecompInstance.liftActsB blank
    (GSPre.decProg blank endSym mark 8 L (L + 1) (DecompInstance.prjB ts)) ts

theorem decActsL_eq {x : List (Fin sc)} {L : ℕ} (hx : x.length = L) (ts : OvTapes sc) :
    decActsL blank endSym mark L ts = DecompInstance.decActsB blank endSym mark x ts := by
  rw [decActsL, DecompInstance.decActsB, hx]

/-- **一様版の主補題**（`DecompInstance.decActsB_spec` の言い換え）。 -/
theorem decActsL_spec {x : List (Fin sc)} {L : ℕ} (hx : x.length = L) (hend : endSym ∉ x)
    (hmark : mark ≠ blank) (ts : OvTapes sc)
    (hE : GSPre.Enc blank startSym endSym mark x 0 0 ⟨0, 0, 0, 0, 0, 0, 0⟩
      (DecompInstance.prjB ts)) :
    (decActsL blank endSym mark L ts).length
        ≤ 237 * decompose2Work x 8 + 49 * (L + 1)
      ∧ (∃ a b D Q E, GSPre.Enc blank startSym endSym mark x a b
          ⟨D, Q, E, (decompose2 x 8).2.1, 0, (decompose2 x 8).1, (decompose2 x 8).2.2⟩
          (DecompInstance.prjB
            (applyActs blank (decActsL blank endSym mark L ts) ts)))
      ∧ (applyActs blank (decActsL blank endSym mark L ts) ts).P = ts.P
      ∧ (applyActs blank (decActsL blank endSym mark L ts) ts).U = ts.U
      ∧ (applyActs blank (decActsL blank endSym mark L ts) ts).Cnt = ts.Cnt
      ∧ (applyActs blank (decActsL blank endSym mark L ts) ts).X = ts.X
      ∧ (applyActs blank (decActsL blank endSym mark L ts) ts).X2 = ts.X2
      ∧ (applyActs blank (decActsL blank endSym mark L ts) ts).F = ts.F := by
  have h := DecompInstance.decActsB_spec (startSym := startSym) hend hmark ts hE
  rw [decActsL_eq hx]
  rw [hx] at h
  exact h

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
