import Mathlib
import PalPeg.ProgLang
import PalPeg.ProgLangLib
import PalPeg.ProgramMachine
import PalPeg.ProgLangPersist

/-!
# 一般到着動作をもつ持ち越し制御プログラム機械 (`ProgLangPersist2`)

`PalPeg/ProgLangPersist.lean` の `progMachineP` は、ラウンド先頭のフェーズ `0` で
**ただ 1 本のテープ `inp`** に入力記号を書く（`inputAct`）。全体機械
（`FullMachineTapes.fullRound`）は到着時に

* 大域入力テープ `inp` と
* 4 つのスロットのコピー最前線 `cpy i`

の **すべて** に入力記号を書いて右へ進める必要があるため、この単一テープ版では足りない。

本ファイルは到着動作を任意の `ArriveAct` にパラメタ化した機械 `progMachinePA` を与え、
`progMachineP_round / _rounds / _srun / _SAccepts_iff / _recognizedBy` に対応する
補題をすべて再証明する（これらは入力テープ非干渉 `NoInputTouch` を **一切使わない**）。
そのうえで

* (α) 目標テープの述語 `tgt : Fin t → Bool` に沿って同時に書き込む
  `inputActM` / `arriveM` / `progMachinePM`、
* (β) ラウンドごとのテープ変換が与えられたときに `n` ラウンドを合成する
  「ラウンド帰納」ラッパ `progMachinePM_rounds_effect`、
* (γ) `tgt = {inp}` のとき元の `progMachineP` と一致すること
  （`progMachinePM_single`）と、それを経由した `progMachineP_grind` の再取得

を与える。
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.ProgLangPersist2

open PegSeparation.RealTimeTM
open PalPeg.Program
open PalPeg.Speedup
open PalPeg.ProgLang
open PalPeg.ProgLangPersist

variable {A C : Type} {Terminal Γ : Type} {t B : ℕ}

/-! ## 1. 一般到着動作 -/

/-- ラウンド先頭（フェーズ `0`）で行う固定動作。制御スタックには依存せず、
到着記号 `a` と全ヘッドの読み `σ` だけから、各テープの（書き込み記号, 移動）を決める。 -/
abbrev ArriveAct (Terminal Γ : Type) (t : ℕ) : Type :=
  Option Terminal → (Fin t → Γ) → (Fin t → Γ × Move)

/-- 一般到着動作を適用した後のテープ束。 -/
def arriveA (blank : Γ) (arr : ArriveAct Terminal Γ t) (a : Option Terminal)
    (T : Fin t → STape Γ) : Fin t → STape Γ :=
  fun j => (T j).applyAction blank (arr a (fun i => (T i).focus) j)

@[simp] theorem arriveA_apply (blank : Γ) (arr : ArriveAct Terminal Γ t)
    (a : Option Terminal) (T : Fin t → STape Γ) (j : Fin t) :
    arriveA blank arr a T j = (T j).applyAction blank (arr a (fun i => (T i).focus) j) :=
  rfl

/-! ## 2. 機械 `progMachinePA` -/

section Machine

variable [DecidableEq A] [DecidableEq C] [Fintype Γ] [DecidableEq Γ]

/-- フェーズ本体（到着動作を一般化した版）。 -/
noncomputable def roundBodyPA (I : InterpF Terminal A C Γ t) (prog : Prog A C)
    (arr : ArriveAct Terminal Γ t) (hB : 0 < B) :
    PhaseBody Terminal (CtrlS prog × Bool) Γ t B :=
  fun c a ph σ =>
    if ph = ⟨0, hB⟩ then (c, arr a σ)
    else
      ((stepCtrlS prog (evalConds I.toInterp σ) c.1,
          updFlag I c.2 (stepStack (evalConds I.toInterp σ) c.1.val).2),
        match (stepStack (evalConds I.toInterp σ) c.1.val).2 with
        | none => fun j => (σ j, Move.stay)
        | some w => I.actOf w a σ)

/-- **一般到着動作つき持ち越し制御プログラム機械。** -/
noncomputable def progMachinePA (I : InterpF Terminal A C Γ t) (prog : Prog A C)
    (arr : ArriveAct Terminal Γ t) (htape : 0 < t) (hB : 0 < B) (blank : Γ) :
    StructuredMachine Terminal ((CtrlS prog × Bool) × Fin B) Γ t B :=
  ofPhases htape hB blank (startCtrlS prog, false) (fun q => q.2)
    (roundBodyPA I prog arr hB)

omit [DecidableEq A] [DecidableEq C] [Fintype Γ] [DecidableEq Γ] in
/-- フェーズ `0`：到着動作だけが起こり、制御は不変。 -/
theorem bodyStepPA_zero (I : InterpF Terminal A C Γ t) (prog : Prog A C)
    (arr : ArriveAct Terminal Γ t) (hB : 0 < B) (blank : Γ) (a : Option Terminal)
    (c : CtrlS prog × Bool) (T : Fin t → STape Γ) :
    bodyStep blank (roundBodyPA I prog arr hB) ⟨0, hB⟩ a (c, T)
      = (c, arriveA blank arr a T) := rfl

omit [DecidableEq A] [DecidableEq C] [Fintype Γ] [DecidableEq Γ] in
/-- フェーズ `≠ 0`：現在のスタックを 1 歩進める（`microStep` と一致）。 -/
theorem bodyStepPA_ne (I : InterpF Terminal A C Γ t) (prog : Prog A C)
    (arr : ArriveAct Terminal Γ t) (hB : 0 < B) (blank : Γ) (ph : Fin B)
    (hph : ph ≠ ⟨0, hB⟩) (a : Option Terminal) (c : CtrlS prog × Bool)
    (T : Fin t → STape Γ) :
    bodyStep blank (roundBodyPA I prog arr hB) ph a (c, T)
      = ((stepCtrlS prog (evalConds I.toInterp (fun j => (T j).focus)) c.1,
            updFlag I c.2
              (stepStack (evalConds I.toInterp (fun j => (T j).focus)) c.1.val).2),
          (microStep I.toInterp blank a (c.1.val, T)).2) := by
  have h1 : (bodyStep blank (roundBodyPA I prog arr hB) ph a (c, T)).1
      = (stepCtrlS prog (evalConds I.toInterp (fun j => (T j).focus)) c.1,
          updFlag I c.2
            (stepStack (evalConds I.toInterp (fun j => (T j).focus)) c.1.val).2) := by
    simp [bodyStep, roundBodyPA, hph]
  refine Prod.ext h1 ?_
  simp only [bodyStep, roundBodyPA, if_neg hph, microStep]
  cases h : (stepStack (evalConds I.toInterp (fun j => (T j).focus)) c.1.val).2 with
  | none =>
      funext j
      exact applyAction_stay_self blank (T j)
  | some w => simp

omit [DecidableEq A] [DecidableEq C] [Fintype Γ] [DecidableEq Γ] in
/-- **フェーズ実行と `runInputs` / `runFlag` の一致**（ラウンド先頭の到着より後）。 -/
theorem phaseRunPA_eq (I : InterpF Terminal A C Γ t) (prog : Prog A C)
    (arr : ArriveAct Terminal Γ t) (hB : 0 < B) (blank : Γ) :
    ∀ (l : List (Option Terminal)) (i : ℕ) (ph : Fin B) (c : CtrlS prog × Bool)
      (T : Fin t → STape Γ),
      i + l.length ≤ B → (l ≠ [] → (ph : ℕ) = i) → (l ≠ [] → i ≠ 0) →
      ((phaseRun blank (roundBodyPA I prog arr hB) l ph (c, T)).1.1.val
            = (runInputs I.toInterp blank l (c.1.val, T)).1 ∧
        (phaseRun blank (roundBodyPA I prog arr hB) l ph (c, T)).1.2
            = runFlag I blank l (c.1.val, T) c.2 ∧
        (phaseRun blank (roundBodyPA I prog arr hB) l ph (c, T)).2
            = (runInputs I.toInterp blank l (c.1.val, T)).2) := by
  intro l
  induction l with
  | nil => intro i ph c T _ _ _; exact ⟨rfl, rfl, rfl⟩
  | cons a l ih =>
      intro i ph c T hlen hph hi0
      have hne : (a :: l) ≠ [] := by simp
      have hphi : (ph : ℕ) = i := hph hne
      have hi : i ≠ 0 := hi0 hne
      have hlen' : i + 1 + l.length ≤ B := by simp at hlen; omega
      have hphne : ph ≠ ⟨0, hB⟩ := by
        intro hcon
        exact hi (by rw [← hphi, hcon])
      have hnext : l ≠ [] → ((nextPhase ph : Fin B) : ℕ) = i + 1 := by
        intro hl
        have hpos : 0 < l.length := List.length_pos_iff.2 hl
        have hb : ((ph : ℕ) + 1 < B) := by omega
        simp only [nextPhase, dif_pos hb]
        omega
      have hIH := ih (i + 1) (nextPhase ph)
        (stepCtrlS prog (evalConds I.toInterp (fun j => (T j).focus)) c.1,
          updFlag I c.2 (stepStack (evalConds I.toInterp (fun j => (T j).focus)) c.1.val).2)
        (microStep I.toInterp blank a (c.1.val, T)).2
        hlen' hnext (by intro _; omega)
      rw [phaseRun_cons, bodyStepPA_ne I prog arr hB blank ph hphne a c T,
        runInputs_cons, runFlag_cons]
      exact hIH

/-- **主定理（1 ラウンド）。** ラウンド先頭は到着動作 `arriveA` だけを行い、
制御はそのまま。残り `B-1` マイクロステップで現在のスタックの続きを実行する。 -/
theorem progMachinePA_round (I : InterpF Terminal A C Γ t) (prog : Prog A C)
    (arr : ArriveAct Terminal Γ t) (htape : 0 < t) (hB : 0 < B) (blank : Γ)
    (c : CtrlS prog × Bool) (T : Fin t → STape Γ) (a : Terminal) :
    ((progMachinePA I prog arr htape hB blank).sRound
          { state := (c, ⟨0, hB⟩), tape := T } a).state.1.1.val
        = (runInputs I.toInterp blank (List.replicate (B - 1) none)
            (c.1.val, arriveA blank arr (some a) T)).1 ∧
      ((progMachinePA I prog arr htape hB blank).sRound
          { state := (c, ⟨0, hB⟩), tape := T } a).state.1.2
        = runFlag I blank (List.replicate (B - 1) none)
            (c.1.val, arriveA blank arr (some a) T) c.2 ∧
      ((progMachinePA I prog arr htape hB blank).sRound
          { state := (c, ⟨0, hB⟩), tape := T } a).tape
        = (runInputs I.toInterp blank (List.replicate (B - 1) none)
            (c.1.val, arriveA blank arr (some a) T)).2 ∧
      ((progMachinePA I prog arr htape hB blank).sRound
          { state := (c, ⟨0, hB⟩), tape := T } a).state.2 = ⟨0, hB⟩ := by
  have hround := ofPhases_round htape hB blank (startCtrlS prog, false)
    (fun q : CtrlS prog × Bool => q.2) (roundBodyPA I prog arr hB) c T a
  have hlist : MultiStepMachine.roundInputs B a
      = some a :: List.replicate (B - 1) (none : Option Terminal) := rfl
  have hnext : List.replicate (B - 1) (none : Option Terminal) ≠ [] →
      ((nextPhase (⟨0, hB⟩ : Fin B)) : ℕ) = 1 := by
    intro hl
    have hpos : 0 < (List.replicate (B - 1) (none : Option Terminal)).length :=
      List.length_pos_iff.2 hl
    rw [List.length_replicate] at hpos
    have hlt : ((⟨0, hB⟩ : Fin B) : ℕ) + 1 < B := by simp; omega
    simp [nextPhase, hlt]
  have hkey := phaseRunPA_eq I prog arr hB blank
    (List.replicate (B - 1) (none : Option Terminal)) 1 (nextPhase (⟨0, hB⟩ : Fin B))
    c (arriveA blank arr (some a) T)
    (by rw [List.length_replicate]; omega) hnext (by intro _; omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [progMachinePA, hround]
    simp only []
    rw [hlist, phaseRun_cons, bodyStepPA_zero]
    exact hkey.1
  · rw [progMachinePA, hround]
    simp only []
    rw [hlist, phaseRun_cons, bodyStepPA_zero]
    exact hkey.2.1
  · rw [progMachinePA, hround]
    simp only []
    rw [hlist, phaseRun_cons, bodyStepPA_zero]
    exact hkey.2.2
  · rw [progMachinePA, hround]

/-! ## 3. ラウンドの反復 -/

/-- 1 ラウンドぶんの意味論（到着 → 継続実行 `m = B-1` 歩）。 -/
def roundSemA (I : InterpF Terminal A C Γ t) (arr : ArriveAct Terminal Γ t)
    (blank : Γ) (m : ℕ) (x : (Stack A C × Bool) × (Fin t → STape Γ)) (a : Terminal) :
    (Stack A C × Bool) × (Fin t → STape Γ) :=
  (((runInputs I.toInterp blank (List.replicate m none)
        (x.1.1, arriveA blank arr (some a) x.2)).1,
      runFlag I blank (List.replicate m none)
        (x.1.1, arriveA blank arr (some a) x.2) x.1.2),
    (runInputs I.toInterp blank (List.replicate m none)
      (x.1.1, arriveA blank arr (some a) x.2)).2)

/-- **主定理（ラウンドの反復）。** 制御は各ラウンド境界で持ち越される。 -/
theorem progMachinePA_rounds (I : InterpF Terminal A C Γ t) (prog : Prog A C)
    (arr : ArriveAct Terminal Γ t) (htape : 0 < t) (hB : 0 < B) (blank : Γ) :
    ∀ (w : List Terminal) (c : CtrlS prog × Bool) (T : Fin t → STape Γ),
      (((w.foldl (progMachinePA I prog arr htape hB blank).sRound
              { state := (c, ⟨0, hB⟩), tape := T }).state.1.1.val,
          (w.foldl (progMachinePA I prog arr htape hB blank).sRound
              { state := (c, ⟨0, hB⟩), tape := T }).state.1.2),
        (w.foldl (progMachinePA I prog arr htape hB blank).sRound
              { state := (c, ⟨0, hB⟩), tape := T }).tape)
          = w.foldl (roundSemA I arr blank (B - 1)) ((c.1.val, c.2), T) ∧
      (w.foldl (progMachinePA I prog arr htape hB blank).sRound
            { state := (c, ⟨0, hB⟩), tape := T }).state.2 = ⟨0, hB⟩ := by
  intro w
  induction w with
  | nil => intro c T; exact ⟨rfl, rfl⟩
  | cons a w ih =>
      intro c T
      have hr := progMachinePA_round I prog arr htape hB blank c T a
      have hcfg :
          (progMachinePA I prog arr htape hB blank).sRound
              { state := (c, ⟨0, hB⟩), tape := T } a
            = { state :=
                  (((progMachinePA I prog arr htape hB blank).sRound
                      { state := (c, ⟨0, hB⟩), tape := T } a).state.1, ⟨0, hB⟩),
                tape :=
                  ((progMachinePA I prog arr htape hB blank).sRound
                      { state := (c, ⟨0, hB⟩), tape := T } a).tape } :=
        sconfig_eta _ _ hr.2.2.2
      have hstep : roundSemA I arr blank (B - 1) ((c.1.val, c.2), T) a
          = ((((progMachinePA I prog arr htape hB blank).sRound
                  { state := (c, ⟨0, hB⟩), tape := T } a).state.1.1.val,
              ((progMachinePA I prog arr htape hB blank).sRound
                  { state := (c, ⟨0, hB⟩), tape := T } a).state.1.2),
            ((progMachinePA I prog arr htape hB blank).sRound
                { state := (c, ⟨0, hB⟩), tape := T } a).tape) := by
        rw [hr.1, hr.2.1, hr.2.2.1]
        rfl
      rw [List.foldl_cons, List.foldl_cons, hstep]
      rw [hcfg]
      exact ih _ _

/-- 初期配置からの実行（`srun`）版。 -/
theorem progMachinePA_srun (I : InterpF Terminal A C Γ t) (prog : Prog A C)
    (arr : ArriveAct Terminal Γ t) (htape : 0 < t) (hB : 0 < B) (blank : Γ)
    (w : List Terminal) :
    ((((progMachinePA I prog arr htape hB blank).srun w).state.1.1.val,
        ((progMachinePA I prog arr htape hB blank).srun w).state.1.2),
      ((progMachinePA I prog arr htape hB blank).srun w).tape)
        = w.foldl (roundSemA I arr blank (B - 1))
            (([prog], false), fun _ => STape.blankTape blank) :=
  (progMachinePA_rounds I prog arr htape hB blank w (startCtrlS prog, false)
    (fun _ => STape.blankTape blank)).1

/-- **受理判定。** 厳密実時間で認識される言語を定める。 -/
theorem progMachinePA_recognizedBy [DecidableEq Terminal] (I : InterpF Terminal A C Γ t)
    (prog : Prog A C) (arr : ArriveAct Terminal Γ t) (htape : 0 < t) (hB : 0 < B)
    (blank : Γ) :
    RecognizedBy { w | (progMachinePA I prog arr htape hB blank).SAccepts w } :=
  StructuredMachine.structured_recognizedBy hB _

/-- 受理条件は「ラウンド末の受理フラグ」に他ならない。 -/
theorem progMachinePA_SAccepts_iff (I : InterpF Terminal A C Γ t) (prog : Prog A C)
    (arr : ArriveAct Terminal Γ t) (htape : 0 < t) (hB : 0 < B) (blank : Γ)
    (w : List Terminal) :
    (progMachinePA I prog arr htape hB blank).SAccepts w
      ↔ (w.foldl (roundSemA I arr blank (B - 1))
          (([prog], false), fun _ => STape.blankTape blank)).1.2 = true := by
  have h := progMachinePA_srun I prog arr htape hB blank w
  have h2 : ((progMachinePA I prog arr htape hB blank).srun w).state.1.2
      = (w.foldl (roundSemA I arr blank (B - 1))
          (([prog], false), fun _ => STape.blankTape blank)).1.2 :=
    congrArg (fun z => z.1.2) h
  constructor
  · intro hacc
    rw [← h2]
    exact hacc
  · intro hacc
    show ((progMachinePA I prog arr htape hB blank).srun w).state.1.2 = true
    rw [h2]
    exact hacc

end Machine

/-! ## 4. (α) 目標テープ集合への同時書き込み -/

/-- **多目標到着動作。** `tgt j = true` なるすべてのテープ `j` に入力記号 `encT a` を
書いて右へ 1 歩進め、それ以外のテープは読んだ記号を書き戻して `stay`。
入力が尽きた（`a = none`）テープでは、読んだ記号をそのまま書き戻して右へ進む。 -/
def inputActM (tgt : Fin t → Bool) (encT : Terminal → Γ) : ArriveAct Terminal Γ t :=
  fun a σ j => if tgt j then (a.elim (σ j) encT, Move.right) else (σ j, Move.stay)

/-- 多目標到着後のテープ束。 -/
def arriveM (blank : Γ) (tgt : Fin t → Bool) (encT : Terminal → Γ)
    (a : Option Terminal) (T : Fin t → STape Γ) : Fin t → STape Γ :=
  arriveA blank (inputActM tgt encT) a T

/-- 目標外のテープは一切動かない。 -/
@[simp] theorem arriveM_of_not (blank : Γ) (tgt : Fin t → Bool) (encT : Terminal → Γ)
    (a : Option Terminal) (T : Fin t → STape Γ) {j : Fin t} (hj : tgt j = false) :
    arriveM blank tgt encT a T j = T j := by
  simp only [arriveM, arriveA, inputActM, hj, Bool.false_eq_true, if_false]
  exact applyAction_stay_self blank (T j)

/-- 目標テープには `encT a` が書かれ、ヘッドが右へ 1 歩進む。 -/
theorem arriveM_of_target (blank : Γ) (tgt : Fin t → Bool) (encT : Terminal → Γ)
    (a : Terminal) (T : Fin t → STape Γ) {j : Fin t} (hj : tgt j = true) :
    arriveM blank tgt encT (some a) T j
      = (T j).applyAction blank (encT a, Move.right) := by
  simp only [arriveM, arriveA, inputActM, hj, if_true, Option.elim]

section MachineM

variable [DecidableEq A] [DecidableEq C] [Fintype Γ] [DecidableEq Γ]

/-- **多目標到着つき持ち越し制御プログラム機械。** -/
noncomputable def progMachinePM (I : InterpF Terminal A C Γ t) (prog : Prog A C)
    (tgt : Fin t → Bool) (encT : Terminal → Γ) (htape : 0 < t) (hB : 0 < B) (blank : Γ) :
    StructuredMachine Terminal ((CtrlS prog × Bool) × Fin B) Γ t B :=
  progMachinePA I prog (inputActM tgt encT) htape hB blank

/-- 1 ラウンドぶんの意味論（多目標版）。 -/
def roundSemM (I : InterpF Terminal A C Γ t) (tgt : Fin t → Bool) (encT : Terminal → Γ)
    (blank : Γ) (m : ℕ) (x : (Stack A C × Bool) × (Fin t → STape Γ)) (a : Terminal) :
    (Stack A C × Bool) × (Fin t → STape Γ) :=
  roundSemA I (inputActM tgt encT) blank m x a

theorem progMachinePM_round (I : InterpF Terminal A C Γ t) (prog : Prog A C)
    (tgt : Fin t → Bool) (encT : Terminal → Γ) (htape : 0 < t) (hB : 0 < B) (blank : Γ)
    (c : CtrlS prog × Bool) (T : Fin t → STape Γ) (a : Terminal) :
    ((progMachinePM I prog tgt encT htape hB blank).sRound
          { state := (c, ⟨0, hB⟩), tape := T } a).state.1.1.val
        = (runInputs I.toInterp blank (List.replicate (B - 1) none)
            (c.1.val, arriveM blank tgt encT (some a) T)).1 ∧
      ((progMachinePM I prog tgt encT htape hB blank).sRound
          { state := (c, ⟨0, hB⟩), tape := T } a).state.1.2
        = runFlag I blank (List.replicate (B - 1) none)
            (c.1.val, arriveM blank tgt encT (some a) T) c.2 ∧
      ((progMachinePM I prog tgt encT htape hB blank).sRound
          { state := (c, ⟨0, hB⟩), tape := T } a).tape
        = (runInputs I.toInterp blank (List.replicate (B - 1) none)
            (c.1.val, arriveM blank tgt encT (some a) T)).2 ∧
      ((progMachinePM I prog tgt encT htape hB blank).sRound
          { state := (c, ⟨0, hB⟩), tape := T } a).state.2 = ⟨0, hB⟩ :=
  progMachinePA_round I prog (inputActM tgt encT) htape hB blank c T a

theorem progMachinePM_rounds (I : InterpF Terminal A C Γ t) (prog : Prog A C)
    (tgt : Fin t → Bool) (encT : Terminal → Γ) (htape : 0 < t) (hB : 0 < B) (blank : Γ) :
    ∀ (w : List Terminal) (c : CtrlS prog × Bool) (T : Fin t → STape Γ),
      (((w.foldl (progMachinePM I prog tgt encT htape hB blank).sRound
              { state := (c, ⟨0, hB⟩), tape := T }).state.1.1.val,
          (w.foldl (progMachinePM I prog tgt encT htape hB blank).sRound
              { state := (c, ⟨0, hB⟩), tape := T }).state.1.2),
        (w.foldl (progMachinePM I prog tgt encT htape hB blank).sRound
              { state := (c, ⟨0, hB⟩), tape := T }).tape)
          = w.foldl (roundSemM I tgt encT blank (B - 1)) ((c.1.val, c.2), T) ∧
      (w.foldl (progMachinePM I prog tgt encT htape hB blank).sRound
            { state := (c, ⟨0, hB⟩), tape := T }).state.2 = ⟨0, hB⟩ :=
  progMachinePA_rounds I prog (inputActM tgt encT) htape hB blank

theorem progMachinePM_srun (I : InterpF Terminal A C Γ t) (prog : Prog A C)
    (tgt : Fin t → Bool) (encT : Terminal → Γ) (htape : 0 < t) (hB : 0 < B) (blank : Γ)
    (w : List Terminal) :
    ((((progMachinePM I prog tgt encT htape hB blank).srun w).state.1.1.val,
        ((progMachinePM I prog tgt encT htape hB blank).srun w).state.1.2),
      ((progMachinePM I prog tgt encT htape hB blank).srun w).tape)
        = w.foldl (roundSemM I tgt encT blank (B - 1))
            (([prog], false), fun _ => STape.blankTape blank) :=
  progMachinePA_srun I prog (inputActM tgt encT) htape hB blank w

theorem progMachinePM_SAccepts_iff (I : InterpF Terminal A C Γ t) (prog : Prog A C)
    (tgt : Fin t → Bool) (encT : Terminal → Γ) (htape : 0 < t) (hB : 0 < B) (blank : Γ)
    (w : List Terminal) :
    (progMachinePM I prog tgt encT htape hB blank).SAccepts w
      ↔ (w.foldl (roundSemM I tgt encT blank (B - 1))
          (([prog], false), fun _ => STape.blankTape blank)).1.2 = true :=
  progMachinePA_SAccepts_iff I prog (inputActM tgt encT) htape hB blank w

/-- **受理判定（多目標版）。** -/
theorem progMachinePM_recognizedBy [DecidableEq Terminal] (I : InterpF Terminal A C Γ t)
    (prog : Prog A C) (tgt : Fin t → Bool) (encT : Terminal → Γ) (htape : 0 < t)
    (hB : 0 < B) (blank : Γ) :
    RecognizedBy { w | (progMachinePM I prog tgt encT htape hB blank).SAccepts w } :=
  progMachinePA_recognizedBy I prog (inputActM tgt encT) htape hB blank

/-! ## 5. (β) ラウンド帰納：ラウンドごとのテープ変換を合成する -/

/-- ラウンドごとの意味論（テープ変換 `F` と受理フラグ更新 `G`）を語に沿って畳む。 -/
def foldEffect (F : Terminal → (Fin t → STape Γ) → (Fin t → STape Γ))
    (G : Terminal → (Fin t → STape Γ) → Bool → Bool) (w : List Terminal)
    (x : Bool × (Fin t → STape Γ)) : Bool × (Fin t → STape Γ) :=
  w.foldl (fun y a => (G a y.2 y.1, F a y.2)) x

omit [DecidableEq A] [DecidableEq C] [Fintype Γ] [DecidableEq Γ] in
@[simp] theorem foldEffect_nil (F : Terminal → (Fin t → STape Γ) → (Fin t → STape Γ))
    (G : Terminal → (Fin t → STape Γ) → Bool → Bool) (x : Bool × (Fin t → STape Γ)) :
    foldEffect F G [] x = x := rfl

omit [DecidableEq A] [DecidableEq C] [Fintype Γ] [DecidableEq Γ] in
@[simp] theorem foldEffect_cons (F : Terminal → (Fin t → STape Γ) → (Fin t → STape Γ))
    (G : Terminal → (Fin t → STape Γ) → Bool → Bool) (a : Terminal) (w : List Terminal)
    (x : Bool × (Fin t → STape Γ)) :
    foldEffect F G (a :: w) x = foldEffect F G w (G a x.2 x.1, F a x.2) := rfl

omit [DecidableEq A] [DecidableEq C] [Fintype Γ] [DecidableEq Γ] in
/-- **ラウンド帰納（一般到着版）。** 「再開点 `s0` から 1 ラウンド走らせると
制御は再び `s0` に戻り、テープは `F a` に、受理フラグは `G a` に従って変わる」
という前提から、`n` ラウンドの合成が `foldEffect` に等しいことが従う。 -/
theorem roundSemA_foldl_effect (I : InterpF Terminal A C Γ t)
    (arr : ArriveAct Terminal Γ t) (blank : Γ) (m : ℕ) (s0 : Stack A C)
    (F : Terminal → (Fin t → STape Γ) → (Fin t → STape Γ))
    (G : Terminal → (Fin t → STape Γ) → Bool → Bool)
    (hround : ∀ (a : Terminal) (T : Fin t → STape Γ) (b : Bool),
      roundSemA I arr blank m ((s0, b), T) a = ((s0, G a T b), F a T)) :
    ∀ (w : List Terminal) (T : Fin t → STape Γ) (b : Bool),
      w.foldl (roundSemA I arr blank m) ((s0, b), T)
        = ((s0, (foldEffect F G w (b, T)).1), (foldEffect F G w (b, T)).2) := by
  intro w
  induction w with
  | nil => intro T b; rfl
  | cons a w ih =>
      intro T b
      rw [List.foldl_cons, hround a T b, foldEffect_cons]
      exact ih (F a T) (G a T b)

omit [DecidableEq A] [DecidableEq C] [Fintype Γ] [DecidableEq Γ] in
/-- **ラウンド帰納（多目標版）。** -/
theorem roundSemM_foldl_effect (I : InterpF Terminal A C Γ t) (tgt : Fin t → Bool)
    (encT : Terminal → Γ) (blank : Γ) (m : ℕ) (s0 : Stack A C)
    (F : Terminal → (Fin t → STape Γ) → (Fin t → STape Γ))
    (G : Terminal → (Fin t → STape Γ) → Bool → Bool)
    (hround : ∀ (a : Terminal) (T : Fin t → STape Γ) (b : Bool),
      roundSemM I tgt encT blank m ((s0, b), T) a = ((s0, G a T b), F a T)) :
    ∀ (w : List Terminal) (T : Fin t → STape Γ) (b : Bool),
      w.foldl (roundSemM I tgt encT blank m) ((s0, b), T)
        = ((s0, (foldEffect F G w (b, T)).1), (foldEffect F G w (b, T)).2) :=
  ProgLangPersist2.roundSemA_foldl_effect I (inputActM tgt encT) blank m s0 F G hround

/-- **組み立てが要求する形。** 各ラウンドの微小ステップ `B-1` 歩がテープ変換 `F a` と
フラグ更新 `G a` を実現し、制御が初期スタック `[prog]` に戻るなら、
`n` ラウンド後の機械の状態とテープは `foldEffect` そのものである。 -/
theorem progMachinePM_rounds_effect (I : InterpF Terminal A C Γ t) (prog : Prog A C)
    (tgt : Fin t → Bool) (encT : Terminal → Γ) (htape : 0 < t) (hB : 0 < B) (blank : Γ)
    (F : Terminal → (Fin t → STape Γ) → (Fin t → STape Γ))
    (G : Terminal → (Fin t → STape Γ) → Bool → Bool)
    (hround : ∀ (a : Terminal) (T : Fin t → STape Γ) (b : Bool),
      roundSemM I tgt encT blank (B - 1) (([prog], b), T) a = (([prog], G a T b), F a T))
    (w : List Terminal) :
    ((progMachinePM I prog tgt encT htape hB blank).srun w).state.1.1.val = [prog] ∧
      ((progMachinePM I prog tgt encT htape hB blank).srun w).state.1.2
        = (foldEffect F G w (false, fun _ => STape.blankTape blank)).1 ∧
      ((progMachinePM I prog tgt encT htape hB blank).srun w).tape
        = (foldEffect F G w (false, fun _ => STape.blankTape blank)).2 := by
  have h := progMachinePM_srun I prog tgt encT htape hB blank w
  have hf := roundSemM_foldl_effect I tgt encT blank (B - 1) [prog] F G hround w
    (fun _ => STape.blankTape blank) false
  rw [hf] at h
  exact ⟨congrArg (fun z => z.1.1) h, congrArg (fun z => z.1.2) h, congrArg (fun z => z.2) h⟩

/-- 受理条件も `foldEffect` で読める。 -/
theorem progMachinePM_SAccepts_effect (I : InterpF Terminal A C Γ t) (prog : Prog A C)
    (tgt : Fin t → Bool) (encT : Terminal → Γ) (htape : 0 < t) (hB : 0 < B) (blank : Γ)
    (F : Terminal → (Fin t → STape Γ) → (Fin t → STape Γ))
    (G : Terminal → (Fin t → STape Γ) → Bool → Bool)
    (hround : ∀ (a : Terminal) (T : Fin t → STape Γ) (b : Bool),
      roundSemM I tgt encT blank (B - 1) (([prog], b), T) a = (([prog], G a T b), F a T))
    (w : List Terminal) :
    (progMachinePM I prog tgt encT htape hB blank).SAccepts w
      ↔ (foldEffect F G w (false, fun _ => STape.blankTape blank)).1 = true := by
  rw [progMachinePM_SAccepts_iff I prog tgt encT htape hB blank w,
    roundSemM_foldl_effect I tgt encT blank (B - 1) [prog] F G hround w
      (fun _ => STape.blankTape blank) false]

/-! ## 6. (γ) 単一テープ版との一致 -/

/-- 単一目標の述語。 -/
def tgtSingle (inp : Fin t) : Fin t → Bool := fun j => decide (j = inp)

@[simp] theorem tgtSingle_self (inp : Fin t) : tgtSingle inp inp = true := by
  simp [tgtSingle]

@[simp] theorem tgtSingle_ne {inp j : Fin t} (h : j ≠ inp) : tgtSingle inp j = false := by
  simp [tgtSingle, h]

omit [Fintype Γ] [DecidableEq Γ] in
/-- 単一目標の到着動作は元の `inputAct` に一致する。 -/
theorem inputActM_single (inp : Fin t) (encT : Terminal → Γ) :
    (inputActM (tgtSingle inp) encT : ArriveAct Terminal Γ t) = inputAct inp encT := by
  funext a σ j
  by_cases h : j = inp
  · subst h; simp [inputActM, inputAct, tgtSingle]
  · simp [inputActM, inputAct, tgtSingle, h]

omit [Fintype Γ] [DecidableEq Γ] in
/-- 単一目標の到着テープ束は元の `arrive` に一致する。 -/
theorem arriveM_single (blank : Γ) (inp : Fin t) (encT : Terminal → Γ)
    (a : Option Terminal) (T : Fin t → STape Γ) :
    arriveM blank (tgtSingle inp) encT a T = arrive blank inp encT a T := by
  funext j
  simp only [arriveM, arriveA, arrive, inputActM_single]

/-- **(γ) 一致定理。** 目標が `{inp}` のとき、一般化した機械は元の `progMachineP`
そのものである。したがって `progMachineP_grind` などの下流の補題はそのまま使える。 -/
theorem progMachinePM_single (I : InterpF Terminal A C Γ t) (prog : Prog A C)
    (inp : Fin t) (encT : Terminal → Γ) (htape : 0 < t) (hB : 0 < B) (blank : Γ) :
    progMachinePM I prog (tgtSingle inp) encT htape hB blank
      = progMachineP I prog inp encT htape hB blank := by
  have hbody : roundBodyPA I prog (inputActM (tgtSingle inp) encT) hB
      = roundBodyP I prog inp encT hB := by
    rw [inputActM_single]
    rfl
  simp only [progMachinePM, progMachinePA, progMachineP, hbody]

omit [DecidableEq A] [DecidableEq C] [Fintype Γ] [DecidableEq Γ] in
/-- 単一目標なら意味論も一致する。 -/
theorem roundSemM_single (I : InterpF Terminal A C Γ t) (inp : Fin t)
    (encT : Terminal → Γ) (blank : Γ) (m : ℕ) :
    roundSemM I (tgtSingle inp) encT blank m = roundSem I inp encT blank m := by
  funext x a
  have harr : arriveA blank (inputActM (tgtSingle inp) encT) (some a) x.2
      = arrive blank inp encT (some a) x.2 := by
    rw [inputActM_single]
    rfl
  simp only [roundSemM, roundSemA, roundSem, harr]

/-- **(γ) 系。** 入力テープ非干渉のもとでの「挽き潰し」定理は、一般化した機械の
単一目標の場合として（元の証明をそのまま流用して）成り立つ。 -/
theorem progMachinePM_grind {I : InterpF Terminal A C Γ t} {inp : Fin t}
    (hni : NoInputTouch I inp) (prog : Prog A C) (encT : Terminal → Γ) (htape : 0 < t)
    (hB : 0 < B) (blank : Γ) (w : List Terminal) :
    ((progMachinePM I prog (tgtSingle inp) encT htape hB blank).srun w).state.1.1.val
        = (runInputs I.toInterp blank (List.replicate (w.length * (B - 1)) none)
            ([prog], fun _ => STape.blankTape blank)).1 ∧
      ∀ j, j ≠ inp →
        ((progMachinePM I prog (tgtSingle inp) encT htape hB blank).srun w).tape j
          = (runInputs I.toInterp blank (List.replicate (w.length * (B - 1)) none)
              ([prog], fun _ => STape.blankTape blank)).2 j := by
  rw [progMachinePM_single I prog inp encT htape hB blank]
  exact progMachineP_grind hni prog encT htape hB blank w

end MachineM

/-! ## 7. 初期受理フラグの一般化

`progMachinePA` は初期受理フラグを `false` に固定しているので、`srun [] = sInit` より
**空語を必ず拒否する**。空語が言語に属する場合（`[] ∈ PAL` など）に届かせるため、
初期フラグ `b₀ : Bool` を指定できる版を与える。`b₀ = false` は元の機械そのもの
（`progMachinePAb_false` / `progMachinePMb_false` は `rfl`）なので、
既存の主張はすべてそのまま有効である。

`ofPhases` は `initial` だけが `init` に依存し、`micro`（したがって `sRound`）は
依存しないので、ラウンド系の補題は初期状態を任意に取る既存版
（`progMachinePA_rounds`）をそのまま使い回せる。 -/

section InitFlag

variable [DecidableEq A] [DecidableEq C] [Fintype Γ] [DecidableEq Γ]

/-- **初期受理フラグを指定できる版**（一般到着動作）。 -/
noncomputable def progMachinePAb (I : InterpF Terminal A C Γ t) (prog : Prog A C)
    (arr : ArriveAct Terminal Γ t) (htape : 0 < t) (hB : 0 < B) (blank : Γ) (b₀ : Bool) :
    StructuredMachine Terminal ((CtrlS prog × Bool) × Fin B) Γ t B :=
  ofPhases htape hB blank (startCtrlS prog, b₀) (fun q => q.2)
    (roundBodyPA I prog arr hB)

/-- `b₀ = false` は元の機械。 -/
theorem progMachinePAb_false (I : InterpF Terminal A C Γ t) (prog : Prog A C)
    (arr : ArriveAct Terminal Γ t) (htape : 0 < t) (hB : 0 < B) (blank : Γ) :
    progMachinePAb I prog arr htape hB blank false
      = progMachinePA I prog arr htape hB blank := rfl

/-- 初期フラグはラウンド遷移に影響しない。 -/
theorem progMachinePAb_sRound (I : InterpF Terminal A C Γ t) (prog : Prog A C)
    (arr : ArriveAct Terminal Γ t) (htape : 0 < t) (hB : 0 < B) (blank : Γ) (b₀ : Bool) :
    (progMachinePAb I prog arr htape hB blank b₀).sRound
      = (progMachinePA I prog arr htape hB blank).sRound := rfl

/-- 初期配置。 -/
theorem progMachinePAb_sInit (I : InterpF Terminal A C Γ t) (prog : Prog A C)
    (arr : ArriveAct Terminal Γ t) (htape : 0 < t) (hB : 0 < B) (blank : Γ) (b₀ : Bool) :
    (progMachinePAb I prog arr htape hB blank b₀).sInit
      = { state := ((startCtrlS prog, b₀), ⟨0, hB⟩),
          tape := fun _ => STape.blankTape blank } := rfl

/-- 初期配置からの実行（`srun`）版。 -/
theorem progMachinePAb_srun (I : InterpF Terminal A C Γ t) (prog : Prog A C)
    (arr : ArriveAct Terminal Γ t) (htape : 0 < t) (hB : 0 < B) (blank : Γ) (b₀ : Bool)
    (w : List Terminal) :
    ((((progMachinePAb I prog arr htape hB blank b₀).srun w).state.1.1.val,
        ((progMachinePAb I prog arr htape hB blank b₀).srun w).state.1.2),
      ((progMachinePAb I prog arr htape hB blank b₀).srun w).tape)
        = w.foldl (roundSemA I arr blank (B - 1))
            (([prog], b₀), fun _ => STape.blankTape blank) :=
  (progMachinePA_rounds I prog arr htape hB blank w (startCtrlS prog, b₀)
    (fun _ => STape.blankTape blank)).1

/-- 受理条件は「ラウンド末の受理フラグ」。 -/
theorem progMachinePAb_SAccepts_iff (I : InterpF Terminal A C Γ t) (prog : Prog A C)
    (arr : ArriveAct Terminal Γ t) (htape : 0 < t) (hB : 0 < B) (blank : Γ) (b₀ : Bool)
    (w : List Terminal) :
    (progMachinePAb I prog arr htape hB blank b₀).SAccepts w
      ↔ (w.foldl (roundSemA I arr blank (B - 1))
          (([prog], b₀), fun _ => STape.blankTape blank)).1.2 = true := by
  have h2 : ((progMachinePAb I prog arr htape hB blank b₀).srun w).state.1.2
      = (w.foldl (roundSemA I arr blank (B - 1))
          (([prog], b₀), fun _ => STape.blankTape blank)).1.2 :=
    congrArg (fun z => z.1.2) (progMachinePAb_srun I prog arr htape hB blank b₀ w)
  constructor
  · intro hacc; rw [← h2]; exact hacc
  · intro hacc
    show ((progMachinePAb I prog arr htape hB blank b₀).srun w).state.1.2 = true
    rw [h2]; exact hacc

theorem progMachinePAb_recognizedBy [DecidableEq Terminal] (I : InterpF Terminal A C Γ t)
    (prog : Prog A C) (arr : ArriveAct Terminal Γ t) (htape : 0 < t) (hB : 0 < B)
    (blank : Γ) (b₀ : Bool) :
    RecognizedBy { w | (progMachinePAb I prog arr htape hB blank b₀).SAccepts w } :=
  StructuredMachine.structured_recognizedBy hB _

/-- **多目標到着つき・初期フラグ指定版。** -/
noncomputable def progMachinePMb (I : InterpF Terminal A C Γ t) (prog : Prog A C)
    (tgt : Fin t → Bool) (encT : Terminal → Γ) (htape : 0 < t) (hB : 0 < B) (blank : Γ)
    (b₀ : Bool) : StructuredMachine Terminal ((CtrlS prog × Bool) × Fin B) Γ t B :=
  progMachinePAb I prog (inputActM tgt encT) htape hB blank b₀

theorem progMachinePMb_false (I : InterpF Terminal A C Γ t) (prog : Prog A C)
    (tgt : Fin t → Bool) (encT : Terminal → Γ) (htape : 0 < t) (hB : 0 < B) (blank : Γ) :
    progMachinePMb I prog tgt encT htape hB blank false
      = progMachinePM I prog tgt encT htape hB blank := rfl

theorem progMachinePMb_srun (I : InterpF Terminal A C Γ t) (prog : Prog A C)
    (tgt : Fin t → Bool) (encT : Terminal → Γ) (htape : 0 < t) (hB : 0 < B) (blank : Γ)
    (b₀ : Bool) (w : List Terminal) :
    ((((progMachinePMb I prog tgt encT htape hB blank b₀).srun w).state.1.1.val,
        ((progMachinePMb I prog tgt encT htape hB blank b₀).srun w).state.1.2),
      ((progMachinePMb I prog tgt encT htape hB blank b₀).srun w).tape)
        = w.foldl (roundSemM I tgt encT blank (B - 1))
            (([prog], b₀), fun _ => STape.blankTape blank) :=
  progMachinePAb_srun I prog (inputActM tgt encT) htape hB blank b₀ w

theorem progMachinePMb_SAccepts_iff (I : InterpF Terminal A C Γ t) (prog : Prog A C)
    (tgt : Fin t → Bool) (encT : Terminal → Γ) (htape : 0 < t) (hB : 0 < B) (blank : Γ)
    (b₀ : Bool) (w : List Terminal) :
    (progMachinePMb I prog tgt encT htape hB blank b₀).SAccepts w
      ↔ (w.foldl (roundSemM I tgt encT blank (B - 1))
          (([prog], b₀), fun _ => STape.blankTape blank)).1.2 = true :=
  progMachinePAb_SAccepts_iff I prog (inputActM tgt encT) htape hB blank b₀ w

theorem progMachinePMb_recognizedBy [DecidableEq Terminal] (I : InterpF Terminal A C Γ t)
    (prog : Prog A C) (tgt : Fin t → Bool) (encT : Terminal → Γ) (htape : 0 < t)
    (hB : 0 < B) (blank : Γ) (b₀ : Bool) :
    RecognizedBy { w | (progMachinePMb I prog tgt encT htape hB blank b₀).SAccepts w } :=
  progMachinePAb_recognizedBy I prog (inputActM tgt encT) htape hB blank b₀

/-- **ラウンド帰納（初期フラグ指定版）。** -/
theorem progMachinePMb_rounds_effect (I : InterpF Terminal A C Γ t) (prog : Prog A C)
    (tgt : Fin t → Bool) (encT : Terminal → Γ) (htape : 0 < t) (hB : 0 < B) (blank : Γ)
    (b₀ : Bool)
    (F : Terminal → (Fin t → STape Γ) → (Fin t → STape Γ))
    (G : Terminal → (Fin t → STape Γ) → Bool → Bool)
    (hround : ∀ (a : Terminal) (T : Fin t → STape Γ) (b : Bool),
      roundSemM I tgt encT blank (B - 1) (([prog], b), T) a = (([prog], G a T b), F a T))
    (w : List Terminal) :
    ((progMachinePMb I prog tgt encT htape hB blank b₀).srun w).state.1.1.val = [prog] ∧
      ((progMachinePMb I prog tgt encT htape hB blank b₀).srun w).state.1.2
        = (foldEffect F G w (b₀, fun _ => STape.blankTape blank)).1 ∧
      ((progMachinePMb I prog tgt encT htape hB blank b₀).srun w).tape
        = (foldEffect F G w (b₀, fun _ => STape.blankTape blank)).2 := by
  have h := progMachinePMb_srun I prog tgt encT htape hB blank b₀ w
  have hf := roundSemM_foldl_effect I tgt encT blank (B - 1) [prog] F G hround w
    (fun _ => STape.blankTape blank) b₀
  rw [hf] at h
  exact ⟨congrArg (fun z => z.1.1) h, congrArg (fun z => z.1.2) h, congrArg (fun z => z.2) h⟩

/-- 受理条件も `foldEffect` で読める（初期フラグ指定版）。 -/
theorem progMachinePMb_SAccepts_effect (I : InterpF Terminal A C Γ t) (prog : Prog A C)
    (tgt : Fin t → Bool) (encT : Terminal → Γ) (htape : 0 < t) (hB : 0 < B) (blank : Γ)
    (b₀ : Bool)
    (F : Terminal → (Fin t → STape Γ) → (Fin t → STape Γ))
    (G : Terminal → (Fin t → STape Γ) → Bool → Bool)
    (hround : ∀ (a : Terminal) (T : Fin t → STape Γ) (b : Bool),
      roundSemM I tgt encT blank (B - 1) (([prog], b), T) a = (([prog], G a T b), F a T))
    (w : List Terminal) :
    (progMachinePMb I prog tgt encT htape hB blank b₀).SAccepts w
      ↔ (foldEffect F G w (b₀, fun _ => STape.blankTape blank)).1 = true := by
  rw [progMachinePMb_SAccepts_iff I prog tgt encT htape hB blank b₀ w,
    roundSemM_foldl_effect I tgt encT blank (B - 1) [prog] F G hround w
      (fun _ => STape.blankTape blank) b₀]

end InitFlag

end PalPeg.ProgLangPersist2

/-
公理チェック（0 エラー・`sorry` なし・`propext / Classical.choice / Quot.sound` のみ）:

```
#print axioms PalPeg.ProgLangPersist2.progMachinePA_round
#print axioms PalPeg.ProgLangPersist2.progMachinePA_rounds
#print axioms PalPeg.ProgLangPersist2.progMachinePA_srun
#print axioms PalPeg.ProgLangPersist2.progMachinePM_rounds_effect
#print axioms PalPeg.ProgLangPersist2.progMachinePM_SAccepts_iff
#print axioms PalPeg.ProgLangPersist2.progMachinePM_single
#print axioms PalPeg.ProgLangPersist2.progMachinePM_grind
#print axioms PalPeg.ProgLangPersist2.progMachinePM_recognizedBy
#print axioms PalPeg.ProgLangPersist2.progMachinePAb_false
#print axioms PalPeg.ProgLangPersist2.progMachinePAb_srun
#print axioms PalPeg.ProgLangPersist2.progMachinePMb_false
#print axioms PalPeg.ProgLangPersist2.progMachinePMb_rounds_effect
#print axioms PalPeg.ProgLangPersist2.progMachinePMb_SAccepts_effect
#print axioms PalPeg.ProgLangPersist2.progMachinePMb_recognizedBy
```
-/
