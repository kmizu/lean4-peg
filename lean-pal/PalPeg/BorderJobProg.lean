import PalPeg.BorderJobTapes
import PalPeg.ProgLangLib

/-!
# 境界列挙段（`BorderJobTapes`）の有限制御プログラム化 (`BorderJobProg`)

`PalPeg.BorderJobTapes` の動作列（`uFwd` / `uCheck` / `shiftActs` / `ovProgram` …）は
「テープ状態から計算される `List (Act sc)`」として書かれている。本ファイルはそれを
`PalPeg.ProgLang` の構造化プログラム `Prog (Act15 sc) (Cond15 sc)` として書き直し、
両者のトレースが 1 動作ずつ一致することを示す。方針は `PalPeg.GSScanProg` と同じ。

## 設計

* テープ束は `Fin 15`：主テープ `tP`/`tX`/`tCnt`/`tU`/`tX2`/`tF` と、分解器用の
  作業テープ `tS1 … tS9`。`OvTapes` の全フィールドを覆っているので、
  `Act` の全 16 構成子がそのまま `Act15` に写る（`prAct`）。
* `Act15 sc := Fin 15 × Option (Fin sc) × Move`（`none` は読んだ記号の書き戻し、
  `some a` は `a` の書き込み）。
* 条件は `Cond15.neq j a`（テープ `j` の読みが `a` でない）と `Cond15.matchPX e`
  （`P` の読みが `e` でなく `X` の読みと等しい）の 2 種類。`ovProgram` の分岐は
  どちらもヘッドの読みだけで決まるので**プローブ不要**でそのまま条件に写る。
* `uFwd` は「`U` が `endSym` を読むまで」のループとしてそのまま書ける
  （停止判定に使う記号が、直前の動作の後でヘッド下に来ているため）。

## 移植できなかった部分（仮定として抽象化）

`uBack` / `perLoop`（`periodActs`）/ `resetWalk`（`resetShift`）は、
**ループ本体の最後の動作の直後に停止判定用の記号がヘッド下に来ない**ため、
動作列を 1 個も増やさずに `Prog.loop` へ写すことができない。詳細は末尾の
`Obstructions` 節。これらは `ovStepProg_exec` では「部分プログラム `SP` が
`shiftActs` を実行する」等の**仮定**として抽象化してあり、追加スクラッチテープ
（マーカ）を使う実装が入り次第そのまま埋められる。
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace PalPeg.BorderProg

open PegSeparation.RealTimeTM
open PalPeg.BorderTapes
open PalPeg.Program
open PalPeg.ProgLang

variable {sc : ℕ}

/-! ## 1. テープ番号 -/

/-- パターンテープ。 -/
def tP : Fin 15 := 0
/-- テキストテープ（照合位置）。 -/
def tX : Fin 15 := 1
/-- 周期カウンタ。 -/
def tCnt : Fin 15 := 2
/-- 接頭辞 `u` のテープ。 -/
def tU : Fin 15 := 3
/-- テキストテープ（段位置）。 -/
def tX2 : Fin 15 := 4
/-- フラグテープ。 -/
def tF : Fin 15 := 5
/-- 作業テープ `S1` … `S9`。 -/
def tS : Fin 9 → Fin 15 := fun i => ⟨6 + i.val, by omega⟩

/-! ## 2. 有限な動作・条件の添字型 -/

/-- 動作識別子：`(テープ番号, 書く記号（`none` は読みの書き戻し）, 移動)`。 -/
abbrev Act15 (sc : ℕ) := Fin 15 × Option (Fin sc) × Move

/-- 条件識別子。 -/
inductive Cond15 (sc : ℕ) where
  /-- テープ `j` の読みが `a` でない。 -/
  | neq (j : Fin 15) (a : Fin sc) : Cond15 sc
  /-- 一致枝の条件（`P` の読みが `e` でなく `X` の読みと等しい）。 -/
  | matchPX (e : Fin sc) : Cond15 sc
  deriving DecidableEq

instance : Fintype (Cond15 sc) :=
  Fintype.ofList
    (((List.finRange 15).flatMap fun j => (List.finRange sc).map (Cond15.neq j)) ++
      (List.finRange sc).map Cond15.matchPX)
    (by rintro (j | e) <;> simp)

variable {Terminal : Type}

/-- 動作の解釈。入力記号は見ない。 -/
def actOf15 (a : Act15 sc) (_ : Option Terminal) (σ : Fin 15 → Fin sc) :
    Fin 15 → Fin sc × Move :=
  touchVec a.1 (a.2.1.getD (σ a.1)) a.2.2 σ

/-- 条件の解釈。 -/
def condOf15 : Cond15 sc → (Fin 15 → Fin sc) → Bool
  | .neq j a, σ => decide (σ j ≠ a)
  | .matchPX e, σ => decide (σ tP ≠ e ∧ σ tP = σ tX)

/-- 15 本テープの境界列挙段の解釈。 -/
def I15 : Interp Terminal (Act15 sc) (Cond15 sc) (Fin sc) 15 where
  actOf := actOf15
  condOf := condOf15

theorem inputFree_I15 : InputFree (I15 (Terminal := Terminal) (sc := sc)) := fun _ _ _ => rfl

/-! ## 3. テープ表現の変換 -/

/-- 成果物のテープを `Prog` 側の zipper へ。 -/
def toS (tp : TapeConfiguration sc) : STape (Fin sc) := ⟨tp.left, tp.focus, tp.right⟩

@[simp] theorem toS_focus (tp : TapeConfiguration sc) : (toS tp).focus = tp.focus := rfl

/-- `OvTapes` の 15 本の射影。 -/
def tapeOf (ts : OvTapes sc) (j : Fin 15) : TapeConfiguration sc :=
  match j.val with
  | 0 => ts.P
  | 1 => ts.X
  | 2 => ts.Cnt
  | 3 => ts.U
  | 4 => ts.X2
  | 5 => ts.F
  | 6 => ts.S1
  | 7 => ts.S2
  | 8 => ts.S3
  | 9 => ts.S4
  | 10 => ts.S5
  | 11 => ts.S6
  | 12 => ts.S7
  | 13 => ts.S8
  | _ => ts.S9

/-- 15 本まとめて zipper 束へ。 -/
def TS (ts : OvTapes sc) : Fin 15 → STape (Fin sc) := fun j => toS (tapeOf ts j)

@[simp] theorem TS_focus (ts : OvTapes sc) (j : Fin 15) :
    ((TS ts) j).focus = (tapeOf ts j).focus := rfl

@[simp] theorem tapeOf_tP (ts : OvTapes sc) : tapeOf ts tP = ts.P := rfl
@[simp] theorem tapeOf_tX (ts : OvTapes sc) : tapeOf ts tX = ts.X := rfl
@[simp] theorem tapeOf_tCnt (ts : OvTapes sc) : tapeOf ts tCnt = ts.Cnt := rfl
@[simp] theorem tapeOf_tU (ts : OvTapes sc) : tapeOf ts tU = ts.U := rfl
@[simp] theorem tapeOf_tX2 (ts : OvTapes sc) : tapeOf ts tX2 = ts.X2 := rfl
@[simp] theorem tapeOf_tF (ts : OvTapes sc) : tapeOf ts tF = ts.F := rfl

theorem toS_step (blank : Fin sc) (tp : TapeConfiguration sc) (a : Fin sc) (m : Move) :
    toS (Tape.step blank tp a m) = (toS tp).applyAction blank (a, m) := by
  obtain ⟨L, f, R⟩ := tp
  cases m <;> cases L <;> cases R <;> rfl

/-! ## 4. 動作列 `List (Act sc)` の write+move ベクトル列 -/

/-- `Act` が触るテープ。 -/
def actTape : Act sc → Fin 15
  | .P _ => tP
  | .X _ => tX
  | .C _ _ => tCnt
  | .U _ => tU
  | .X2 _ => tX2
  | .F _ => tF
  | .Fset _ => tF
  | .S1 _ _ => tS 0
  | .S2 _ _ => tS 1
  | .S3 _ _ => tS 2
  | .S4 _ _ => tS 3
  | .S5 _ _ => tS 4
  | .S6 _ _ => tS 5
  | .S7 _ _ => tS 6
  | .S8 _ _ => tS 7
  | .S9 _ _ => tS 8

/-- `Act` が書き込む記号。 -/
def writeOf (ts : OvTapes sc) : Act sc → Fin sc
  | .P _ => ts.P.focus
  | .X _ => ts.X.focus
  | .C a _ => a
  | .U _ => ts.U.focus
  | .X2 _ => ts.X2.focus
  | .F _ => ts.F.focus
  | .Fset a => a
  | .S1 a _ => a
  | .S2 a _ => a
  | .S3 a _ => a
  | .S4 a _ => a
  | .S5 a _ => a
  | .S6 a _ => a
  | .S7 a _ => a
  | .S8 a _ => a
  | .S9 a _ => a

/-- `Act` の移動。 -/
def moveOf : Act sc → Move
  | .P m => m
  | .X m => m
  | .C _ m => m
  | .U m => m
  | .X2 m => m
  | .F m => m
  | .Fset _ => .stay
  | .S1 _ m => m
  | .S2 _ m => m
  | .S3 _ m => m
  | .S4 _ m => m
  | .S5 _ m => m
  | .S6 _ m => m
  | .S7 _ m => m
  | .S8 _ m => m
  | .S9 _ m => m

/-- `Act` に対応する `Prog` の動作識別子。 -/
def prAct : Act sc → Act15 sc
  | .P m => (tP, none, m)
  | .X m => (tX, none, m)
  | .C a m => (tCnt, some a, m)
  | .U m => (tU, none, m)
  | .X2 m => (tX2, none, m)
  | .F m => (tF, none, m)
  | .Fset a => (tF, some a, .stay)
  | .S1 a m => (tS 0, some a, m)
  | .S2 a m => (tS 1, some a, m)
  | .S3 a m => (tS 2, some a, m)
  | .S4 a m => (tS 3, some a, m)
  | .S5 a m => (tS 4, some a, m)
  | .S6 a m => (tS 5, some a, m)
  | .S7 a m => (tS 6, some a, m)
  | .S8 a m => (tS 7, some a, m)
  | .S9 a m => (tS 8, some a, m)

/-- `applyAct` は `actTape a` のテープだけを `Tape.step` で書き換える。 -/
theorem tapeOf_applyAct (blank : Fin sc) (ts : OvTapes sc) (a : Act sc) (j : Fin 15) :
    tapeOf (applyAct blank ts a) j
      = if j = actTape a then
          Tape.step blank (tapeOf ts j) (writeOf ts a) (moveOf a)
        else tapeOf ts j := by
  cases a <;> fin_cases j <;> rfl

/-- `Act` に対応する 15 テープ分の write+move ベクトル。 -/
def avec (ts : OvTapes sc) (a : Act sc) : Fin 15 → Fin sc × Move :=
  fun j => if j = actTape a then (writeOf ts a, moveOf a) else ((tapeOf ts j).focus, Move.stay)

/-- 動作列に対応するベクトル列（各段の状態で評価する）。 -/
def avecs (blank : Fin sc) : List (Act sc) → OvTapes sc → List (Fin 15 → Fin sc × Move)
  | [], _ => []
  | a :: l, ts => avec ts a :: avecs blank l (applyAct blank ts a)

@[simp] theorem avecs_nil (blank : Fin sc) (ts : OvTapes sc) :
    avecs blank [] ts = [] := rfl

@[simp] theorem avecs_cons (blank : Fin sc) (a : Act sc) (l : List (Act sc))
    (ts : OvTapes sc) :
    avecs blank (a :: l) ts = avec ts a :: avecs blank l (applyAct blank ts a) := rfl

@[simp] theorem avecs_length (blank : Fin sc) :
    ∀ (l : List (Act sc)) (ts : OvTapes sc), (avecs blank l ts).length = l.length := by
  intro l
  induction l with
  | nil => intro ts; rfl
  | cons a l ih => intro ts; simp [ih]

theorem avecs_append (blank : Fin sc) :
    ∀ (l₁ l₂ : List (Act sc)) (ts : OvTapes sc),
      avecs blank (l₁ ++ l₂) ts
        = avecs blank l₁ ts ++ avecs blank l₂ (applyActs blank l₁ ts) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ ts; rfl
  | cons a l ih => intro l₂ ts; simp [ih]

/-- 1 動作分：ベクトルの適用は `applyAct` に一致する。 -/
theorem applyTrace_avec (blank : Fin sc) (ts : OvTapes sc) (a : Act sc) :
    (fun j => ((TS ts) j).applyAction blank (avec ts a j)) = TS (applyAct blank ts a) := by
  funext j
  show (toS (tapeOf ts j)).applyAction blank (avec ts a j)
    = toS (tapeOf (applyAct blank ts a) j)
  rw [tapeOf_applyAct]
  by_cases hj : j = actTape a
  · rw [if_pos hj, toS_step]
    simp only [avec, if_pos hj]
  · rw [if_neg hj]
    simp only [avec, if_neg hj]
    exact ProgLang.applyAction_focus_stay (blank := blank) (toS (tapeOf ts j))

theorem applyTrace_avecs (blank : Fin sc) :
    ∀ (l : List (Act sc)) (ts : OvTapes sc),
      applyTrace blank (TS ts) (avecs blank l ts) = TS (applyActs blank l ts) := by
  intro l
  induction l with
  | nil => intro ts; rfl
  | cons a l ih =>
      intro ts
      rw [avecs_cons, applyTrace_cons]
      show applyTrace blank (fun j => ((TS ts) j).applyAction blank (avec ts a j)) _ = _
      rw [applyTrace_avec, ih]
      rfl

/-! ## 5. `Act` の動作列に対する `Exec` -/

section ExecA

variable (Terminal : Type)

/-- 「プログラム `P` は状態 `ts` からちょうど動作列 `L` を実行して継続に戻る」。 -/
def ExecA (blank : Fin sc) (P : Prog (Act15 sc) (Cond15 sc)) (ts : OvTapes sc)
    (L : List (Act sc)) : Prop :=
  Exec (I15 (Terminal := Terminal)) blank P (TS ts) (avecs blank L ts)

variable {Terminal}
variable {blank : Fin sc}

theorem execA_of_eq {P : Prog (Act15 sc) (Cond15 sc)} {ts : OvTapes sc}
    {L L' : List (Act sc)} (h : L = L') (hE : ExecA Terminal blank P ts L) :
    ExecA Terminal blank P ts L' := h ▸ hE

theorem execA_skip {ts : OvTapes sc} :
    ExecA Terminal blank (Prog.skip : Prog (Act15 sc) (Cond15 sc)) ts [] := exec_skip _

theorem execA_seq {P Q : Prog (Act15 sc) (Cond15 sc)} {ts : OvTapes sc}
    {L₁ L₂ : List (Act sc)}
    (h1 : ExecA Terminal blank P ts L₁)
    (h2 : ExecA Terminal blank Q (applyActs blank L₁ ts) L₂) :
    ExecA Terminal blank (Prog.seq P Q) ts (L₁ ++ L₂) := by
  unfold ExecA at h1 h2 ⊢
  rw [avecs_append]
  refine exec_seq h1 ?_
  rw [applyTrace_avecs]
  exact h2

/-- `Act` 1 個に対応する 1 動作プログラム。 -/
def ACT (a : Act sc) : Prog (Act15 sc) (Cond15 sc) := Prog.act (prAct a)

theorem actVec_prAct (a : Act sc) (ts : OvTapes sc) :
    actVec (I15 (Terminal := Terminal)) (prAct a) (TS ts) = avec ts a := by
  funext j
  cases a <;> rfl

theorem execA_act (a : Act sc) (ts : OvTapes sc) :
    ExecA Terminal blank (ACT a) ts [a] := by
  have h := exec_act (blank := blank) (inputFree_I15 (Terminal := Terminal) (sc := sc))
    (prAct a) (TS ts)
  rw [actVec_prAct] at h
  exact h

/-! ### 条件つき分岐 -/

theorem condOf_eq (c : Cond15 sc) (ts : OvTapes sc) :
    (I15 (Terminal := Terminal)).condOf c (fun j => ((TS ts) j).focus)
      = condOf15 c (fun j => (tapeOf ts j).focus) := rfl

theorem execA_ite_pos {c : Cond15 sc} {P Q : Prog (Act15 sc) (Cond15 sc)} {ts : OvTapes sc}
    {L : List (Act sc)} (hc : condOf15 c (fun j => (tapeOf ts j).focus) = true)
    (h : ExecA Terminal blank P ts L) :
    ExecA Terminal blank (Prog.ite c P Q) ts L :=
  exec_ite_pos (by rw [condOf_eq]; exact hc) h

theorem execA_ite_neg {c : Cond15 sc} {P Q : Prog (Act15 sc) (Cond15 sc)} {ts : OvTapes sc}
    {L : List (Act sc)} (hc : condOf15 c (fun j => (tapeOf ts j).focus) = false)
    (h : ExecA Terminal blank Q ts L) :
    ExecA Terminal blank (Prog.ite c P Q) ts L :=
  exec_ite_neg (by rw [condOf_eq]; exact hc) h

theorem execA_loop_stop {c : Cond15 sc} {w : Act15 sc} {b : Prog (Act15 sc) (Cond15 sc)}
    {ts : OvTapes sc} (hc : condOf15 c (fun j => (tapeOf ts j).focus) = false) :
    ExecA Terminal blank (Prog.loop c w b) ts [] :=
  exec_loop_stop (by rw [condOf_eq]; exact hc)

theorem execA_loop_cont {c : Cond15 sc} {a : Act sc} {b : Prog (Act15 sc) (Cond15 sc)}
    {ts : OvTapes sc} {L₁ L₂ : List (Act sc)}
    (hc : condOf15 c (fun j => (tapeOf ts j).focus) = true)
    (h1 : ExecA Terminal blank b (applyAct blank ts a) L₁)
    (h2 : ExecA Terminal blank (Prog.loop c (prAct a) b)
      (applyActs blank L₁ (applyAct blank ts a)) L₂) :
    ExecA Terminal blank (Prog.loop c (prAct a) b) ts (a :: (L₁ ++ L₂)) := by
  unfold ExecA at h1 h2 ⊢
  rw [avecs_cons, avecs_append, ← actVec_prAct (Terminal := Terminal) a ts]
  have hT : (fun j => ((TS ts) j).applyAction blank
      (actVec (I15 (Terminal := Terminal)) (prAct a) (TS ts) j))
      = TS (applyAct blank ts a) := by
    rw [actVec_prAct]; exact applyTrace_avec blank ts a
  refine exec_loop_cont (inputFree_I15 (Terminal := Terminal) (sc := sc))
    (by rw [condOf_eq]; exact hc) ?_ ?_
  · rw [hT]; exact h1
  · rw [hT, applyTrace_avecs]; exact h2

/-! ### トレース・停止 -/

/-- 実行トレースはちょうど動作列 `L` のベクトル列。 -/
theorem execA_trace {P : Prog (Act15 sc) (Cond15 sc)} {ts : OvTapes sc} {L : List (Act sc)}
    (h : ExecA Terminal blank P ts L) (l : List (Option Terminal)) (hl : l.length = L.length) :
    trace (I15 (Terminal := Terminal)) blank l ([P], TS ts) = avecs blank L ts :=
  Exec.trace_eq h [] l (by rw [avecs_length]; exact hl)

/-- **マイクロステップ数は動作列の長さそのもの**（`Prog` 化で増減しない）。 -/
theorem execA_trace_length {P : Prog (Act15 sc) (Cond15 sc)} {ts : OvTapes sc}
    {L : List (Act sc)} (h : ExecA Terminal blank P ts L) (l : List (Option Terminal))
    (hl : l.length = L.length) :
    (trace (I15 (Terminal := Terminal)) blank l ([P], TS ts)).length = L.length := by
  rw [execA_trace h l hl, avecs_length]

/-- 実行後のテープ束は `applyActs` の結果。 -/
theorem execA_run {P : Prog (Act15 sc) (Cond15 sc)} {ts : OvTapes sc} {L : List (Act sc)}
    (h : ExecA Terminal blank P ts L) (l : List (Option Terminal)) (hl : l.length = L.length) :
    ∃ s', runInputs (I15 (Terminal := Terminal)) blank l ([P], TS ts)
      = (s', TS (applyActs blank L ts)) := by
  obtain ⟨-, s', hs', -⟩ := h [] l (by rw [avecs_length]; exact hl)
  rw [show ([P] ++ ([] : Stack (Act15 sc) (Cond15 sc))) = [P] from rfl] at hs'
  refine ⟨s', ?_⟩
  rw [hs', applyTrace_avecs]

/-- `L` を出し切った直後の 1 歩で制御は空になる（＝プログラムは確かに停止する）。 -/
theorem execA_halts {P : Prog (Act15 sc) (Cond15 sc)} {ts : OvTapes sc} {L : List (Act sc)}
    (h : ExecA Terminal blank P ts L) (l : List (Option Terminal))
    (hl : l.length = L.length) (x : Option Terminal) :
    (runInputs (I15 (Terminal := Terminal)) blank (l ++ [x]) ([P], TS ts)).1 = [] :=
  exec_halts h l (by rw [avecs_length]; exact hl) x

end ExecA

/-! ## 6. 段の一歩のプログラム -/

section Programs

/-- `uFwd`：`U` が `endSym` を読むまで、`U` を右・`X2` を左へ。 -/
def uFwdProg (endSym : Fin sc) : Prog (Act15 sc) (Cond15 sc) :=
  Prog.loop (Cond15.neq tU endSym) (prAct (Act.U .right)) (ACT (Act.X2 .left))

/-- 一致枝：`P` を右・`X` を左。 -/
def advStepProg : Prog (Act15 sc) (Cond15 sc) :=
  Prog.seq (ACT (Act.P .right)) (ACT (Act.X .left))

/-- フラグ書き込み（`bu` が真のときだけ）。 -/
def fsetProg (one : Fin sc) (bu : Bool) : Prog (Act15 sc) (Cond15 sc) :=
  if bu then ACT (Act.Fset one) else Prog.skip

/-- 段の一歩（`ovProgram`）の有限制御。`UC` は `uCheck`、`SP` は `shiftActs` を
実行する部分プログラム（下記 `Obstructions` 節の理由でここでは仮定として与える）。 -/
def ovStepProg (leftSym endSym one : Fin sc) (bu : Bool)
    (UC SP : Prog (Act15 sc) (Cond15 sc)) : Prog (Act15 sc) (Cond15 sc) :=
  Prog.ite (Cond15.neq tX leftSym)
    (Prog.ite (Cond15.matchPX endSym) advStepProg SP)
    (Prog.seq UC (Prog.seq (fsetProg one bu) SP))

end Programs

section ProgSpec

variable {Terminal : Type} {blank : Fin sc}

/-! ### `uFwd` -/

/-- `uFwd` の実現。停止条件は「`U` が `endSym` を読む」。 -/
theorem uFwdProg_exec (endSym : Fin sc) :
    ∀ (c : ℕ) (ts : OvTapes sc),
      (∀ i, i < c → ((applyActs blank (uFwd sc i) ts).U).focus ≠ endSym) →
      ((applyActs blank (uFwd sc c) ts).U).focus = endSym →
      ExecA Terminal blank (uFwdProg endSym) ts (uFwd sc c) := by
  intro c
  induction c with
  | zero =>
      intro ts _ hstop
      simp only [uFwd]
      refine execA_loop_stop ?_
      simp only [condOf15, tapeOf_tU, decide_eq_false_iff_not, not_not]
      exact hstop
  | succ c ih =>
      intro ts hne hstop
      have h0 : ts.U.focus ≠ endSym := hne 0 (Nat.succ_pos c)
      have hcond : condOf15 (Cond15.neq tU endSym) (fun j => (tapeOf ts j).focus) = true := by
        simp only [condOf15, tapeOf_tU, decide_eq_true_eq]
        exact h0
      set ts₁ := applyAct blank ts (Act.U (sc := sc) .right) with hts₁
      have hstate : applyActs blank [Act.X2 (sc := sc) .left] ts₁
          = applyActs blank (uFwd sc 1) ts := rfl
      have h1 : ExecA Terminal blank (ACT (Act.X2 (sc := sc) .left)) ts₁
          [Act.X2 (sc := sc) .left] := execA_act _ _
      have hshift : ∀ i, applyActs blank (uFwd sc i)
          (applyActs blank [Act.X2 (sc := sc) .left] ts₁)
          = applyActs blank (uFwd sc (i + 1)) ts := by
        intro i
        show applyActs blank (uFwd sc i) (applyActs blank (uFwd sc 1) ts) = _
        rw [← applyActs_append]
        rfl
      have h2 := ih (applyActs blank [Act.X2 (sc := sc) .left] ts₁)
        (by intro i hi; rw [hshift i]; exact hne (i + 1) (by omega))
        (by rw [hshift c]; exact hstop)
      exact execA_of_eq rfl (execA_loop_cont hcond h1 h2)

/-- `SeqView` 版：`U` が `startSym :: (u ++ [endSym])` を位置 `1` で見ていて
`endSym ∉ u` なら、`uFwdProg` は `uFwd sc u.length` をちょうど実行する。 -/
theorem uFwdProg_exec_seqView {startSym endSym : Fin sc} {u : List (Fin sc)}
    {ts : OvTapes sc} (hend : endSym ∉ u)
    (hU : Tape.SeqView blank ts.U (startSym :: (u ++ [endSym])) 1) :
    ExecA Terminal blank (uFwdProg endSym) ts (uFwd sc u.length) := by
  have hlen : (startSym :: (u ++ [endSym])).length = u.length + 2 := by simp
  have hread : ∀ i, i ≤ u.length →
      (startSym :: (u ++ [endSym]))[1 + i]?
        = some ((applyActs blank (uFwd sc i) ts).U).focus := by
    intro i hi
    rw [uFwd_U]
    exact (seq_rightN (blank := blank) (w := startSym :: (u ++ [endSym])) i ts.U 1 hU
      (by rw [hlen]; omega)).read_eq
  refine uFwdProg_exec endSym u.length ts (fun i hi => ?_) ?_
  · have h1 := hread i (le_of_lt hi)
    rw [show 1 + i = i + 1 from by omega, List.getElem?_cons_succ,
      List.getElem?_append_left hi] at h1
    obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.1 h1
    exact fun hcon => hend (hcon ▸ he ▸ List.getElem_mem hlt)
  · have h1 := hread u.length (le_refl _)
    rw [show 1 + u.length = u.length + 1 from by omega, List.getElem?_cons_succ,
      List.getElem?_append_right (le_refl _)] at h1
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at h1
    exact h1.symm

/-! ### 一致枝・フラグ・段の一歩 -/

theorem advStepProg_exec (ts : OvTapes sc) :
    ExecA Terminal blank advStepProg ts [Act.P .right, Act.X (sc := sc) .left] :=
  execA_seq (execA_act _ _) (execA_act _ _)

theorem fsetProg_exec (one : Fin sc) (bu : Bool) (ts : OvTapes sc) :
    ExecA Terminal blank (fsetProg one bu) ts (if bu then [Act.Fset one] else []) := by
  cases bu with
  | false => exact execA_skip
  | true => exact execA_act _ _

/-- **段の一歩**。`ovStepProg` は `ovProgram` の動作列をちょうど実行する。 -/
theorem ovStepProg_exec {leftSym endSym mark one : Fin sc} {k c : ℕ} {b bu : Bool}
    {UC SP : Prog (Act15 sc) (Cond15 sc)} (ts : OvTapes sc)
    (hUC : ExecA Terminal blank UC ts (uCheck sc c))
    (hSP1 : ExecA Terminal blank SP
        (applyActs blank (uCheck sc c ++ (if bu then [Act.Fset one] else [])) ts)
        (shiftActs blank mark k b ts))
    (hSP2 : ExecA Terminal blank SP ts (shiftActs blank mark k b ts)) :
    ExecA Terminal blank (ovStepProg leftSym endSym one bu UC SP) ts
      (ovProgram blank leftSym endSym mark one k c b bu ts) := by
  unfold ovProgram ovStepProg
  by_cases hfront : Tape.read ts.X = leftSym
  · rw [if_pos hfront]
    have hcond : condOf15 (Cond15.neq tX leftSym) (fun j => (tapeOf ts j).focus) = false := by
      simp only [condOf15, tapeOf_tX, decide_eq_false_iff_not, not_not]
      exact hfront
    refine execA_ite_neg hcond ?_
    have h2 := fsetProg_exec (Terminal := Terminal) (blank := blank) one bu
      (applyActs blank (uCheck sc c) ts)
    have hcat : applyActs blank (if bu then [Act.Fset one] else [])
        (applyActs blank (uCheck sc c) ts)
        = applyActs blank (uCheck sc c ++ (if bu then [Act.Fset one] else [])) ts :=
      (applyActs_append _ _ _ _).symm
    have h3 := hSP1
    rw [← hcat] at h3
    refine execA_of_eq ?_ (execA_seq hUC (execA_seq h2 h3))
    simp [List.append_assoc]
  · rw [if_neg hfront]
    have hcond : condOf15 (Cond15.neq tX leftSym) (fun j => (tapeOf ts j).focus) = true := by
      simp only [condOf15, tapeOf_tX, decide_eq_true_eq]
      exact hfront
    refine execA_ite_pos hcond ?_
    by_cases hmatch : Tape.read ts.P ≠ endSym ∧ Tape.read ts.P = Tape.read ts.X
    · rw [if_pos hmatch]
      refine execA_ite_pos ?_ (advStepProg_exec ts)
      simp only [condOf15, tapeOf_tP, tapeOf_tX, decide_eq_true_eq]
      exact hmatch
    · rw [if_neg hmatch]
      refine execA_ite_neg ?_ hSP2
      simp only [condOf15, tapeOf_tP, tapeOf_tX, decide_eq_false_iff_not]
      exact hmatch

end ProgSpec

/-! ## 7. Obstructions（今回の道具立てでは移植できない部分）

`Prog.loop c a body` の意味は `while c do { act a; body }` であり、条件 `c` は
**ループ本体の最後の動作を終えた直後**のヘッドの読みだけで評価される。したがって
「ループを何回回すか」を決める記号が、本体の最後の動作の直後にヘッド下へ来ている
必要がある。`BorderJobTapes` の以下の 3 つの動作列はこの形になっていない。

* `uBack sc c = (U .left :: X2 .right :: …)` — `U` は位置 `1 + c` から位置 `1` へ
  戻る。停止すべき位置 `1` の読みは `u[0]` であり、途中の読み `u[j]` と区別できない。
  区別できるのは位置 `0` の `startSym` なので、素朴なループは `U .left` を 1 個
  余分に出す（`uBack sc c ++ [Act.U .left]`）。マーカ用スクラッチテープ
  （例：`S1` に `c` の単進カウンタを積む）を使えば動作数を増やさずに書ける。
* `perLoop blank n`（`periodActs` の下げループ）— 1 反復は
  `P .left, C blank .left, C blank .stay` の順で、判定に使えるのは probe
  `C blank .left` の直後だが、反復の最後の動作は `C blank .stay`（空白を書く）で
  あるため、次の判定時点でカウンタの底マーカは読めない。`GSScanProg.perDownLoop`
  では動作列側が `probe` を反復の末尾に置いてあったので写せた。
  なお `periodActs` の上げ部分 `List.replicate n (Act.C blank .right)` は、
  その時点でどのテープにも `n` が残っていないため、そもそも有限制御では
  実現できない（`GSScanProg` の第 2 カウンタ `tC2` に相当する退避先が要る）。
* `resetWalk sc k n c`（`resetShift`）— 停止判定は `P` が左端の `startSym` を
  踏むことだが、それを読めるのは `resetShift` の後続 `Act.P .left` の直後であり、
  歩行ループの反復末尾（`Act.X .right` またはループ最終の `Act.P .left`）では
  位相 `c` に依存して読み位置がずれる。素朴なループは `q % k ≠ 0` のとき
  `Act.X .right` を 1 個余分に出す。

いずれも「動作数を増やさない」制約を外すか、追加スクラッチテープにマーカ／
カウンタを持たせて動作列そのものを probe 末尾形に書き直せば解消する。
本ファイルではこれらを `ovStepProg_exec` の仮定 `hUC` / `hSP1` / `hSP2` として
切り出してあるので、実装が入り次第そのまま埋められる。 -/

end PalPeg.BorderProg
