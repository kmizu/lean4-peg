import Mathlib
import PalPeg.ProgramMachine

/-!
# 構造化プログラム言語 `Prog` と有限状態インタプリタ (`ProgLang`)

既存の各テープ手続き（`GSScanTapes.program'` など）は、テープ状態から計算される
**動作列** `List (Act sc)` として書かれている。それを `StructuredMachine`
（`PalPeg/ProgramMachine.lean`）へ載せるには、

* 制御が **有限型** であること、
* 1 マイクロステップがちょうど 1 個の動作（全テープへの write+move）であること

が必要になる。本ファイルはその橋渡しとなる小さな構造化プログラム言語を与える。

## 設計

* `Prog A C` — `skip` / `act a` / `seq` / `ite c p q` / `loop c a body` の 5 構成子。
  動作は識別子 `A`、条件は識別子 `C` で表す（`A`, `C` は有限な添字型）。
  こうすると `Prog` は一階の帰納型になり `DecidableEq` が自動で導ける。
* `loop c a body` は「`while c do { act a; body }`」を表す。**ループ本体の先頭が
  必ず 1 動作である**ことを構文で強制しているので、純制御遷移（`skip`/`seq`/`ite`
  の展開）の連鎖は必ず有限で止まる。おかげで小ステップ関数 `stepStack` は
  fuel なしで（構造的な整礎再帰で）全域関数として定義できる。
* 制御状態は継続スタック `List (Prog A C)`。1 プログラム `prog` から `B` 歩以内に
  到達するスタックの有限リスト `reachSet B [prog]` を計算し、その部分型を
  `StructuredMachine` の制御型として使う（`List.Subtype.fintype` で `Fintype`）。
* 入力記号 `Option Terminal` は動作の解釈 `Interp.actOf` に渡す。したがって
  「ラウンド先頭の `act` が入力記号をテープ 0 に書く」という設計がそのまま書ける。

## 主定理

* `stepStack_snd_eq_none` … 動作を出さないのはスタックが空のときだけ（停止の特徴づけ）。
* `runInputs_snd_eq_applyTrace` … `n` マイクロステップの実行は `trace` の
  動作を順に適用したものに等しい。
* `trace_append`, `trace_length_le`, `runInputs_halted` … トレースの前置性・長さ上界・
  停止後の不動性。
* `progMachine_round` … `progMachine` の 1 ラウンドは
  「ラウンドプログラムを `[prog]` から `B` 歩走らせる」ことに等しい。
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.ProgLang

open PegSeparation.RealTimeTM
open PalPeg.Program
open PalPeg.Speedup

/-! ## 1. 構文 -/

/-- 構造化プログラム。`A` は動作識別子、`C` は条件識別子（いずれも有限型を想定）。

* `skip` … 何もしない（制御遷移のみ）
* `act a` … 1 マイクロステップ。全テープに write+move を行う
* `seq p q` … 逐次実行
* `ite c p q` … ヘッドの読みで決まる条件 `c` による分岐
* `loop c a body` … `while c do { act a; body }`。
  本体の先頭に動作 `a` を置くことを構文で強制する（無限の純制御ループを排除）。 -/
inductive Prog (A C : Type) where
  | skip : Prog A C
  | act (a : A) : Prog A C
  | seq (p q : Prog A C) : Prog A C
  | ite (c : C) (p q : Prog A C) : Prog A C
  | loop (c : C) (a : A) (body : Prog A C) : Prog A C
  deriving DecidableEq

namespace Prog

variable {A C : Type}

/-- 構文木のサイズ（`stepStack` の整礎再帰の測度に使う）。 -/
def size : Prog A C → ℕ
  | .skip => 1
  | .act _ => 1
  | .seq p q => p.size + q.size + 1
  | .ite _ p q => p.size + q.size + 1
  | .loop _ _ b => b.size + 1

theorem size_pos (p : Prog A C) : 0 < p.size := by
  cases p <;> simp [size]

end Prog

/-- 継続スタック。先頭が「次に実行するプログラム」。 -/
abbrev Stack (A C : Type) := List (Prog A C)

/-- スタックの測度。 -/
def stackSize {A C : Type} (s : Stack A C) : ℕ := (s.map Prog.size).sum

@[simp] theorem stackSize_nil {A C : Type} : stackSize ([] : Stack A C) = 0 := rfl

@[simp] theorem stackSize_cons {A C : Type} (p : Prog A C) (r : Stack A C) :
    stackSize (p :: r) = p.size + stackSize r := by
  simp [stackSize]

/-! ## 2. 小ステップインタプリタ

`stepStack ev s` は、条件が `ev : C → Bool` で評価される状況でスタック `s` を
**ちょうど 1 動作分**進める。純制御遷移（`skip` の除去、`seq`/`ite` の展開、
条件偽の `loop` の脱出）は同じマイクロステップに畳み込まれる。畳み込みは
`stackSize` について狭義減少するので必ず停止する（fuel 不要）。 -/

/-- 1 マイクロステップ。戻り値は（次のスタック, 実行した動作の識別子）。
動作を返さないのはプログラムが終了したときだけ（`stepStack_snd_eq_none`）。 -/
def stepStack {A C : Type} (ev : C → Bool) : Stack A C → Stack A C × Option A
  | [] => ([], none)
  | .skip :: r => stepStack ev r
  | .act a :: r => (r, some a)
  | .seq p q :: r => stepStack ev (p :: q :: r)
  | .ite c p q :: r => stepStack ev ((if ev c then p else q) :: r)
  | .loop c a b :: r =>
      if ev c then (b :: Prog.loop c a b :: r, some a) else stepStack ev r
termination_by s => stackSize s
decreasing_by
  all_goals (try split) <;> (simp [stackSize, Prog.size]; try omega)

variable {A C : Type}

@[simp] theorem stepStack_nil (ev : C → Bool) :
    stepStack (A := A) ev [] = ([], none) := by
  rw [stepStack]

@[simp] theorem stepStack_skip (ev : C → Bool) (r : Stack A C) :
    stepStack ev (Prog.skip :: r) = stepStack ev r := by
  rw [stepStack]

@[simp] theorem stepStack_act (ev : C → Bool) (a : A) (r : Stack A C) :
    stepStack ev (Prog.act a :: r) = (r, some a) := by
  rw [stepStack]

@[simp] theorem stepStack_seq (ev : C → Bool) (p q : Prog A C) (r : Stack A C) :
    stepStack ev (Prog.seq p q :: r) = stepStack ev (p :: q :: r) := by
  rw [stepStack]

@[simp] theorem stepStack_ite (ev : C → Bool) (c : C) (p q : Prog A C) (r : Stack A C) :
    stepStack ev (Prog.ite c p q :: r) = stepStack ev ((if ev c then p else q) :: r) := by
  rw [stepStack]

@[simp] theorem stepStack_loop (ev : C → Bool) (c : C) (a : A) (b : Prog A C)
    (r : Stack A C) :
    stepStack ev (Prog.loop c a b :: r) =
      (if ev c then (b :: Prog.loop c a b :: r, some a) else stepStack ev r) := by
  rw [stepStack]

/-- **停止の特徴づけ。** 動作を出さないのはスタックが空になったときだけであり、
そのとき次のスタックも空である。 -/
theorem stepStack_snd_eq_none (ev : C → Bool) :
    ∀ s : Stack A C, (stepStack ev s).2 = none → (stepStack ev s).1 = [] := by
  intro s
  induction s using stepStack.induct (ev := ev) with
  | case1 => simp
  | case2 r ih => simpa using ih
  | case3 a r => simp
  | case4 p q r ih => simpa using ih
  | case5 c p q r ih => simpa using ih
  | case6 c a b r h => simp [h]
  | case7 c a b r h ih => simpa [h] using ih

/-- 空スタックは不動点。 -/
theorem stepStack_of_nil (ev : C → Bool) :
    (stepStack (A := A) ev []).1 = [] := by simp

/-! ## 3. テープ意味論

テープは `PalPeg.Program.STape Γ` を `t` 本束ねたもの（`StructuredMachine` と同じ）。
`Interp` が動作識別子・条件識別子の解釈を与える。動作の解釈は入力記号
`Option Terminal` も見られる（ラウンド先頭の `act` で入力をテープに書くため）。 -/

/-- 動作・条件の解釈。 -/
structure Interp (Terminal A C Γ : Type) (t : ℕ) where
  /-- 動作識別子の解釈：入力記号と全ヘッドの読みから、全テープの write+move へ。 -/
  actOf : A → Option Terminal → (Fin t → Γ) → (Fin t → Γ × Move)
  /-- 条件識別子の解釈：全ヘッドの読みから真偽へ。 -/
  condOf : C → (Fin t → Γ) → Bool

variable {Terminal Γ : Type} {t : ℕ}

/-- 現在のヘッドの読みで条件をすべて評価した環境。 -/
def evalConds (I : Interp Terminal A C Γ t) (σ : Fin t → Γ) : C → Bool :=
  fun c => I.condOf c σ

/-- （スタック, テープ束）の 1 マイクロステップ。動作が無い場合はテープ不変。 -/
def microStep (I : Interp Terminal A C Γ t) (blank : Γ) (a : Option Terminal)
    (x : Stack A C × (Fin t → STape Γ)) : Stack A C × (Fin t → STape Γ) :=
  let σ : Fin t → Γ := fun j => (x.2 j).focus
  let r := stepStack (evalConds I σ) x.1
  (r.1,
    match r.2 with
    | none => x.2
    | some w => fun j => (x.2 j).applyAction blank (I.actOf w a σ j))

@[simp] theorem microStep_nil (I : Interp Terminal A C Γ t) (blank : Γ)
    (a : Option Terminal) (T : Fin t → STape Γ) :
    microStep I blank a ([], T) = ([], T) := by
  simp [microStep]

/-- 入力記号列（`roundInputs` など）に沿った実行。 -/
def runInputs (I : Interp Terminal A C Γ t) (blank : Γ) :
    List (Option Terminal) → Stack A C × (Fin t → STape Γ) →
      Stack A C × (Fin t → STape Γ)
  | [], x => x
  | a :: l, x => runInputs I blank l (microStep I blank a x)

@[simp] theorem runInputs_nil (I : Interp Terminal A C Γ t) (blank : Γ)
    (x : Stack A C × (Fin t → STape Γ)) : runInputs I blank [] x = x := rfl

@[simp] theorem runInputs_cons (I : Interp Terminal A C Γ t) (blank : Γ)
    (a : Option Terminal) (l : List (Option Terminal))
    (x : Stack A C × (Fin t → STape Γ)) :
    runInputs I blank (a :: l) x = runInputs I blank l (microStep I blank a x) := rfl

theorem runInputs_append (I : Interp Terminal A C Γ t) (blank : Γ)
    (l₁ l₂ : List (Option Terminal)) (x : Stack A C × (Fin t → STape Γ)) :
    runInputs I blank (l₁ ++ l₂) x =
      runInputs I blank l₂ (runInputs I blank l₁ x) := by
  induction l₁ generalizing x with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- 停止後は何も起こらない。 -/
@[simp] theorem runInputs_halted (I : Interp Terminal A C Γ t) (blank : Γ)
    (l : List (Option Terminal)) (T : Fin t → STape Γ) :
    runInputs I blank l ([], T) = ([], T) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-! ### トレース（実際に実行された動作の列） -/

/-- `trace` は、入力記号列 `l` に沿って実行したときに **実際に行われた動作** を
順に並べたもの。プログラムが途中で終了すれば、それ以降は何も並ばない。 -/
def trace (I : Interp Terminal A C Γ t) (blank : Γ) :
    List (Option Terminal) → Stack A C × (Fin t → STape Γ) →
      List (Fin t → Γ × Move)
  | [], _ => []
  | a :: l, x =>
      (match (stepStack (evalConds I (fun j => (x.2 j).focus)) x.1).2 with
        | none => []
        | some w => [I.actOf w a (fun j => (x.2 j).focus)]) ++
        trace I blank l (microStep I blank a x)

@[simp] theorem trace_nil (I : Interp Terminal A C Γ t) (blank : Γ)
    (x : Stack A C × (Fin t → STape Γ)) : trace I blank [] x = [] := rfl

theorem trace_cons (I : Interp Terminal A C Γ t) (blank : Γ) (a : Option Terminal)
    (l : List (Option Terminal)) (x : Stack A C × (Fin t → STape Γ)) :
    trace I blank (a :: l) x =
      (match (stepStack (evalConds I (fun j => (x.2 j).focus)) x.1).2 with
        | none => []
        | some w => [I.actOf w a (fun j => (x.2 j).focus)]) ++
        trace I blank l (microStep I blank a x) := rfl

/-- 動作列をテープ束に順に適用する。 -/
def applyTrace (blank : Γ) (T : Fin t → STape Γ) :
    List (Fin t → Γ × Move) → Fin t → STape Γ
  | [] => T
  | w :: l => applyTrace blank (fun j => (T j).applyAction blank (w j)) l

@[simp] theorem applyTrace_nil (blank : Γ) (T : Fin t → STape Γ) :
    applyTrace blank T [] = T := rfl

@[simp] theorem applyTrace_cons (blank : Γ) (T : Fin t → STape Γ)
    (w : Fin t → Γ × Move) (l : List (Fin t → Γ × Move)) :
    applyTrace blank T (w :: l) =
      applyTrace blank (fun j => (T j).applyAction blank (w j)) l := rfl

theorem applyTrace_append (blank : Γ) (T : Fin t → STape Γ)
    (l₁ l₂ : List (Fin t → Γ × Move)) :
    applyTrace blank T (l₁ ++ l₂) = applyTrace blank (applyTrace blank T l₁) l₂ := by
  induction l₁ generalizing T with
  | nil => rfl
  | cons w l ih => simp [ih]

/-- **操作的意味論と denotational なトレースの一致。**
入力記号列 `l` に沿った `l.length` マイクロステップの実行結果のテープは、
`trace` の動作を順に適用したものにちょうど等しい。 -/
theorem runInputs_snd_eq_applyTrace (I : Interp Terminal A C Γ t) (blank : Γ)
    (l : List (Option Terminal)) (x : Stack A C × (Fin t → STape Γ)) :
    (runInputs I blank l x).2 = applyTrace blank x.2 (trace I blank l x) := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih =>
      rw [runInputs_cons, ih, trace_cons]
      cases h : (stepStack (evalConds I (fun j => (x.2 j).focus)) x.1).2 with
      | none => simp [microStep, h]
      | some w => simp [microStep, h]

/-- **トレースの前置性。** 先に `l₁` を走らせたトレースは、`l₁ ++ l₂` のトレースの
先頭部分にちょうど一致する。 -/
theorem trace_append (I : Interp Terminal A C Γ t) (blank : Γ)
    (l₁ l₂ : List (Option Terminal)) (x : Stack A C × (Fin t → STape Γ)) :
    trace I blank (l₁ ++ l₂) x =
      trace I blank l₁ x ++ trace I blank l₂ (runInputs I blank l₁ x) := by
  induction l₁ generalizing x with
  | nil => simp
  | cons a l ih => simp [trace_cons, ih, List.append_assoc]

/-- 1 マイクロステップは高々 1 動作。 -/
theorem trace_length_le (I : Interp Terminal A C Γ t) (blank : Γ)
    (l : List (Option Terminal)) (x : Stack A C × (Fin t → STape Γ)) :
    (trace I blank l x).length ≤ l.length := by
  induction l generalizing x with
  | nil => simp
  | cons a l ih =>
      rw [trace_cons]
      cases h : (stepStack (evalConds I (fun j => (x.2 j).focus)) x.1).2 with
      | none =>
          have := ih (microStep I blank a x)
          simp
          omega
      | some w =>
          have := ih (microStep I blank a x)
          simp
          omega

/-- **停止後の不動性。** スタックが空になった後は、トレースは空で、
制御もテープも動かない（全テープ `stay` で読んだ記号を書き戻すのと同じ）。 -/
@[simp] theorem trace_halted (I : Interp Terminal A C Γ t) (blank : Γ)
    (l : List (Option Terminal)) (T : Fin t → STape Γ) :
    trace I blank l ([], T) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [trace_cons, ih]

/-! ## 4. 到達可能な制御の有限集合

条件環境 `ev : C → Bool` は有限個しかないので、スタックの後続も有限個。
`reachSet n s` は `s` から `n` 歩以内に到達しうるスタックの（重複を許す）リスト。 -/

section Reach

variable [Fintype C] [DecidableEq C]

/-- 1 歩で到達しうるスタックの全体。 -/
noncomputable def succStacks (s : Stack A C) : List (Stack A C) :=
  (Finset.univ : Finset (C → Bool)).toList.map (fun ev => (stepStack ev s).1)

theorem mem_succStacks (ev : C → Bool) (s : Stack A C) :
    (stepStack ev s).1 ∈ succStacks s := by
  simp only [succStacks, List.mem_map]
  exact ⟨ev, by simp, rfl⟩

/-- `s` から `n` 歩以内に到達しうるスタックのリスト。 -/
noncomputable def reachSet : ℕ → Stack A C → List (Stack A C)
  | 0, s => [s]
  | n + 1, s => s :: (succStacks s).flatMap (reachSet n)

@[simp] theorem mem_reachSet_self (n : ℕ) (s : Stack A C) : s ∈ reachSet n s := by
  cases n <;> simp [reachSet]

theorem reachSet_mono {n m : ℕ} (h : n ≤ m) {s x : Stack A C}
    (hx : x ∈ reachSet n s) : x ∈ reachSet m s := by
  induction n generalizing m s with
  | zero =>
      simp [reachSet] at hx
      subst hx
      exact mem_reachSet_self _ _
  | succ n ih =>
      obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hm : n ≤ m := by omega
      simp only [reachSet, List.mem_cons, List.mem_flatMap] at hx ⊢
      rcases hx with hx | ⟨y, hy, hxy⟩
      · exact Or.inl hx
      · exact Or.inr ⟨y, hy, ih hm hxy⟩

/-- 到達集合は 1 歩の遷移で閉じている（深さが 1 増える）。 -/
theorem reachSet_step {n : ℕ} {s x : Stack A C} (hx : x ∈ reachSet n s)
    (ev : C → Bool) : (stepStack ev x).1 ∈ reachSet (n + 1) s := by
  induction n generalizing s with
  | zero =>
      have hxs : x = s := by simpa [reachSet] using hx
      subst hxs
      rw [reachSet]
      refine List.mem_cons_of_mem _ ?_
      rw [List.mem_flatMap]
      exact ⟨(stepStack ev x).1, mem_succStacks ev x, by simp [reachSet]⟩
  | succ n ih =>
      rw [reachSet, List.mem_cons] at hx
      rw [reachSet]
      refine List.mem_cons_of_mem _ ?_
      rw [List.mem_flatMap]
      rcases hx with rfl | hx
      · exact ⟨(stepStack ev x).1, mem_succStacks ev x, mem_reachSet_self _ _⟩
      · rw [List.mem_flatMap] at hx
        obtain ⟨y, hy, hxy⟩ := hx
        exact ⟨y, hy, ih hxy⟩

end Reach

/-! ## 5. `StructuredMachine` への橋渡し

ラウンドプログラム `prog` を `B` マイクロステップ／ラウンドで走らせる機械を作る。
制御型は「`[prog]` から `B` 歩以内に到達するスタック」の部分型で、`Fintype`。
ラウンド先頭（フェーズ `0`）で制御は `[prog]` にリセットされる。 -/

section Machine

variable [Fintype C] [DecidableEq C] [DecidableEq A] [Fintype Γ] [DecidableEq Γ]
  {B : ℕ}

/-- 機械の制御型：`[prog]` から `B` 歩以内に到達するスタック。 -/
def Ctrl (prog : Prog A C) (B : ℕ) : Type := { s : Stack A C // s ∈ reachSet B [prog] }

instance (prog : Prog A C) (B : ℕ) : DecidableEq (Ctrl prog B) :=
  inferInstanceAs (DecidableEq { s : Stack A C // s ∈ reachSet B [prog] })

noncomputable instance (prog : Prog A C) (B : ℕ) : Fintype (Ctrl prog B) :=
  inferInstanceAs (Fintype { s : Stack A C // s ∈ reachSet B [prog] })

/-- ラウンド開始時の制御。 -/
def startCtrl (prog : Prog A C) (B : ℕ) : Ctrl prog B :=
  ⟨[prog], mem_reachSet_self _ _⟩

/-- 到達集合からはみ出したら開始状態に落とす（実際のラウンド中は発動しない、
`progMachine_round` 参照）。 -/
noncomputable def clampCtrl (prog : Prog A C) (B : ℕ) (s : Stack A C) : Ctrl prog B :=
  if h : s ∈ reachSet B [prog] then ⟨s, h⟩ else startCtrl prog B

theorem clampCtrl_val {prog : Prog A C} {B : ℕ} {s : Stack A C}
    (h : s ∈ reachSet B [prog]) : (clampCtrl prog B s).val = s := by
  simp [clampCtrl, h]

/-- フェーズ本体。フェーズ `0`（ラウンド先頭）では制御を `[prog]` にリセットし、
入力記号 `a` を見て 1 マイクロステップ実行する。 -/
noncomputable def roundBody (I : Interp Terminal A C Γ t) (prog : Prog A C) (hB : 0 < B) :
    PhaseBody Terminal (Ctrl prog B) Γ t B :=
  fun c a ph σ =>
    let s : Stack A C := if ph = ⟨0, hB⟩ then [prog] else c.val
    let r := stepStack (evalConds I σ) s
    (clampCtrl prog B r.1,
      match r.2 with
      | none => fun j => (σ j, Move.stay)
      | some w => I.actOf w a σ)

/-- ラウンドプログラム `prog` を 1 ラウンド `B` マイクロステップで走らせる機械。 -/
noncomputable def progMachine (I : Interp Terminal A C Γ t) (prog : Prog A C) (htape : 0 < t)
    (hB : 0 < B) (blank : Γ) (acc : Ctrl prog B → Bool) :
    StructuredMachine Terminal (Ctrl prog B × Fin B) Γ t B :=
  ofPhases htape hB blank (startCtrl prog B) acc (roundBody I prog hB)

omit [Fintype C] [DecidableEq C] [DecidableEq A] [Fintype Γ] [DecidableEq Γ] in
/-- 動作なしのマイクロステップはテープを変えない（`stay` で読んだ記号を書き戻す）。 -/
theorem applyAction_stay_focus (blank : Γ) (T : STape Γ) :
    T.applyAction blank (T.focus, Move.stay) = T := by
  cases T; rfl

omit [Fintype Γ] [DecidableEq Γ] in
/-- `bodyStep` を `microStep` に読み替える（フェーズ `0` 以外）。 -/
theorem bodyStep_eq (I : Interp Terminal A C Γ t) (prog : Prog A C) (hB : 0 < B)
    (blank : Γ) (ph : Fin B) (hph : ph ≠ ⟨0, hB⟩) (a : Option Terminal)
    (c : Ctrl prog B) (T : Fin t → STape Γ) :
    (bodyStep blank (roundBody I prog hB) ph a (c, T)) =
      (clampCtrl prog B (microStep I blank a (c.val, T)).1,
        (microStep I blank a (c.val, T)).2) := by
  have h1 : (bodyStep blank (roundBody I prog hB) ph a (c, T)).1 =
      clampCtrl prog B (microStep I blank a (c.val, T)).1 := by
    simp [bodyStep, roundBody, microStep, hph]
  refine Prod.ext h1 ?_
  simp only [bodyStep, roundBody, microStep, if_neg hph]
  cases h : (stepStack (evalConds I (fun j => (T j).focus)) c.val).2 with
  | none =>
      funext j
      exact applyAction_stay_focus blank (T j)
  | some w => simp

omit [Fintype Γ] [DecidableEq Γ] in
/-- フェーズ `0` の 1 歩：制御は `[prog]` にリセットされる。 -/
theorem bodyStep_zero (I : Interp Terminal A C Γ t) (prog : Prog A C) (hB : 0 < B)
    (blank : Γ) (a : Option Terminal) (c : Ctrl prog B) (T : Fin t → STape Γ) :
    (bodyStep blank (roundBody I prog hB) ⟨0, hB⟩ a (c, T)) =
      (clampCtrl prog B (microStep I blank a ([prog], T)).1,
        (microStep I blank a ([prog], T)).2) := by
  have h1 : (bodyStep blank (roundBody I prog hB) ⟨0, hB⟩ a (c, T)).1 =
      clampCtrl prog B (microStep I blank a ([prog], T)).1 := by
    simp [bodyStep, roundBody, microStep]
  refine Prod.ext h1 ?_
  simp only [bodyStep, roundBody, microStep, if_true]
  cases h : (stepStack (evalConds I (fun j => (T j).focus)) ([prog] : Stack A C)).2 with
  | none =>
      funext j
      exact applyAction_stay_focus blank (T j)
  | some w => simp

omit [Fintype Γ] [DecidableEq Γ] in
/-- **フェーズ実行と `runInputs` の一致**（ラウンド先頭以降の部分）。 -/
theorem phaseRun_eq (I : Interp Terminal A C Γ t) (prog : Prog A C) (hB : 0 < B)
    (blank : Γ) :
    ∀ (l : List (Option Terminal)) (i : ℕ) (ph : Fin B) (c : Ctrl prog B)
      (T : Fin t → STape Γ),
      i + l.length ≤ B → (l ≠ [] → (ph : ℕ) = i) → (l ≠ [] → i ≠ 0) →
      c.val ∈ reachSet i [prog] →
      ((phaseRun blank (roundBody I prog hB) l ph (c, T)).1.val
          = (runInputs I blank l (c.val, T)).1 ∧
        (phaseRun blank (roundBody I prog hB) l ph (c, T)).2
          = (runInputs I blank l (c.val, T)).2) := by
  intro l
  induction l with
  | nil => intro i ph c T _ _ _ _; exact ⟨rfl, rfl⟩
  | cons a l ih =>
      intro i ph c T hlen hph hi0 hmem
      have hne : (a :: l) ≠ [] := by simp
      have hphi : (ph : ℕ) = i := hph hne
      have hi : i ≠ 0 := hi0 hne
      have hlen' : i + 1 + l.length ≤ B := by simp at hlen; omega
      have hiB : i + 1 ≤ B := by omega
      have hphne : ph ≠ ⟨0, hB⟩ := by
        intro hcon
        apply hi
        rw [← hphi, hcon]
      have hstep : (stepStack (evalConds I (fun j => (T j).focus)) c.val).1
          ∈ reachSet (i + 1) [prog] := reachSet_step hmem _
      have hstepB : (stepStack (evalConds I (fun j => (T j).focus)) c.val).1
          ∈ reachSet B [prog] := reachSet_mono hiB hstep
      have hmicro : (microStep I blank a (c.val, T)).1
          = (stepStack (evalConds I (fun j => (T j).focus)) c.val).1 := rfl
      have hval : (clampCtrl prog B (microStep I blank a (c.val, T)).1).val
          = (microStep I blank a (c.val, T)).1 := by
        rw [hmicro]; exact clampCtrl_val hstepB
      have hbs := bodyStep_eq I prog hB blank ph hphne a c T
      have hnext : l ≠ [] → ((nextPhase ph : Fin B) : ℕ) = i + 1 := by
        intro hl
        have hpos : 0 < l.length := List.length_pos_iff.2 hl
        have hlt : i + 1 < B := by omega
        have hb : ((ph : ℕ) + 1 < B) := by omega
        simp only [nextPhase, dif_pos hb]
        omega
      have hmem' : (clampCtrl prog B (microStep I blank a (c.val, T)).1).val
          ∈ reachSet (i + 1) [prog] := by
        rw [hval, hmicro]; exact hstep
      have hIH := ih (i + 1) (nextPhase ph)
        (clampCtrl prog B (microStep I blank a (c.val, T)).1)
        (microStep I blank a (c.val, T)).2
        hlen' hnext (by intro _; omega) hmem'
      rw [hval] at hIH
      rw [phaseRun_cons, hbs, runInputs_cons]
      exact hIH

/-- **主定理（橋渡し）。**
`progMachine` の 1 ラウンドは、ラウンドプログラムを `[prog]` から
`roundInputs B a`（先頭のみ入力記号が見える `B` マイクロステップ）に沿って
走らせることに等しい。制御はラウンド末で `runInputs` の到達スタック、
フェーズカウンタは `0` に戻る。 -/
theorem progMachine_round (I : Interp Terminal A C Γ t) (prog : Prog A C)
    (htape : 0 < t) (hB : 0 < B) (blank : Γ) (acc : Ctrl prog B → Bool)
    (c : Ctrl prog B) (T : Fin t → STape Γ) (a : Terminal) :
    ((progMachine I prog htape hB blank acc).sRound
        { state := (c, ⟨0, hB⟩), tape := T } a).state.1.val
        = (runInputs I blank (MultiStepMachine.roundInputs B a) ([prog], T)).1 ∧
      ((progMachine I prog htape hB blank acc).sRound
        { state := (c, ⟨0, hB⟩), tape := T } a).tape
        = (runInputs I blank (MultiStepMachine.roundInputs B a) ([prog], T)).2 ∧
      ((progMachine I prog htape hB blank acc).sRound
        { state := (c, ⟨0, hB⟩), tape := T } a).state.2 = ⟨0, hB⟩ := by
  have hround := ofPhases_round htape hB blank (startCtrl prog B) acc
    (roundBody I prog hB) c T a
  have hlist : MultiStepMachine.roundInputs B a
      = some a :: List.replicate (B - 1) none := rfl
  have hstep1 : (stepStack (evalConds I (fun j => (T j).focus)) ([prog] : Stack A C)).1
      ∈ reachSet 1 [prog] := reachSet_step (mem_reachSet_self _ _) _
  have hstepB : (stepStack (evalConds I (fun j => (T j).focus)) ([prog] : Stack A C)).1
      ∈ reachSet B [prog] := reachSet_mono hB hstep1
  have hmicro : (microStep I blank (some a) (([prog] : Stack A C), T)).1
      = (stepStack (evalConds I (fun j => (T j).focus)) ([prog] : Stack A C)).1 := rfl
  have hval : (clampCtrl prog B (microStep I blank (some a) (([prog] : Stack A C), T)).1).val
      = (microStep I blank (some a) (([prog] : Stack A C), T)).1 := by
    rw [hmicro]; exact clampCtrl_val hstepB
  have hnext : List.replicate (B - 1) (none : Option Terminal) ≠ [] →
      ((nextPhase (⟨0, hB⟩ : Fin B)) : ℕ) = 1 := by
    intro hl
    have hpos : 0 < (List.replicate (B - 1) (none : Option Terminal)).length :=
      List.length_pos_iff.2 hl
    rw [List.length_replicate] at hpos
    have hlt : ((⟨0, hB⟩ : Fin B) : ℕ) + 1 < B := by simp; omega
    simp [nextPhase, hlt]
  have hmem' : (clampCtrl prog B (microStep I blank (some a) (([prog] : Stack A C), T)).1).val
      ∈ reachSet 1 [prog] := by rw [hval, hmicro]; exact hstep1
  have hkey := phaseRun_eq I prog hB blank
    (List.replicate (B - 1) (none : Option Terminal)) 1 (nextPhase (⟨0, hB⟩ : Fin B))
    (clampCtrl prog B (microStep I blank (some a) (([prog] : Stack A C), T)).1)
    (microStep I blank (some a) (([prog] : Stack A C), T)).2
    (by rw [List.length_replicate]; omega) hnext (by intro _; omega) hmem'
  rw [hval] at hkey
  refine ⟨?_, ?_, ?_⟩
  · rw [progMachine, hround]
    simp only []
    rw [hlist, phaseRun_cons, bodyStep_zero, runInputs_cons]
    exact hkey.1
  · rw [progMachine, hround]
    simp only []
    rw [hlist, phaseRun_cons, bodyStep_zero, runInputs_cons]
    exact hkey.2
  · rw [progMachine, hround]

/-- ラウンドの結果テープは、ラウンドプログラムのトレースを順に適用したもの。 -/
theorem progMachine_round_tape_eq_applyTrace (I : Interp Terminal A C Γ t)
    (prog : Prog A C) (htape : 0 < t) (hB : 0 < B) (blank : Γ)
    (acc : Ctrl prog B → Bool) (c : Ctrl prog B) (T : Fin t → STape Γ) (a : Terminal) :
    ((progMachine I prog htape hB blank acc).sRound
        { state := (c, ⟨0, hB⟩), tape := T } a).tape
      = applyTrace blank T
          (trace I blank (MultiStepMachine.roundInputs B a) ([prog], T)) := by
  rw [(progMachine_round I prog htape hB blank acc c T a).2.1]
  exact runInputs_snd_eq_applyTrace I blank _ _

/-- ラウンドプログラムが `B` マイクロステップ以内に停止するなら、ラウンド末の制御は
空スタックであり、次のラウンド先頭のリセットと整合する。 -/
theorem progMachine_round_halted (I : Interp Terminal A C Γ t) (prog : Prog A C)
    (htape : 0 < t) (hB : 0 < B) (blank : Γ) (acc : Ctrl prog B → Bool)
    (c : Ctrl prog B) (T : Fin t → STape Γ) (a : Terminal)
    (hhalt : (runInputs I blank (MultiStepMachine.roundInputs B a) ([prog], T)).1 = []) :
    ((progMachine I prog htape hB blank acc).sRound
        { state := (c, ⟨0, hB⟩), tape := T } a).state.1.val = [] := by
  rw [(progMachine_round I prog htape hB blank acc c T a).1, hhalt]

/-- **系。** `progMachine` は `StructuredMachine` なので、そのまま
`PalPeg.Program.StructuredMachine.structured_recognizedBy` に載り、
厳密実時間で認識される言語を定める。 -/
theorem progMachine_recognizedBy [DecidableEq Terminal] (I : Interp Terminal A C Γ t)
    (prog : Prog A C) (htape : 0 < t) (hB : 0 < B) (blank : Γ)
    (acc : Ctrl prog B → Bool) :
    RecognizedBy { w | (progMachine I prog htape hB blank acc).SAccepts w } :=
  StructuredMachine.structured_recognizedBy hB _

end Machine

end PalPeg.ProgLang

/-
主定理の公理チェック（0 エラー・`propext / Classical.choice / Quot.sound` のみ）:

```
#print axioms PalPeg.ProgLang.stepStack_snd_eq_none
#print axioms PalPeg.ProgLang.runInputs_snd_eq_applyTrace
#print axioms PalPeg.ProgLang.trace_append
#print axioms PalPeg.ProgLang.trace_length_le
#print axioms PalPeg.ProgLang.reachSet_step
#print axioms PalPeg.ProgLang.phaseRun_eq
#print axioms PalPeg.ProgLang.progMachine_round
#print axioms PalPeg.ProgLang.progMachine_round_tape_eq_applyTrace
#print axioms PalPeg.ProgLang.progMachine_round_halted
#print axioms PalPeg.ProgLang.progMachine_recognizedBy
```
-/
