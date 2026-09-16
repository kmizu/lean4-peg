import PalPeg.GSScanTapes
import PalPeg.ProgLangLib

/-!
# GS 走査段（オラクル無し）の有限制御プログラム化 (`GSScanProg`)

`PalPeg.GSScanTapes` の `program'` は「テープ状態から計算される動作列
`List (Act' sc)`」として書かれている。本ファイルはそれを
`PalPeg.ProgLang` の構造化プログラム `Prog Act8 Cond8` として**書き直し**、
両者のトレースが 1 動作ずつ一致することを証明する。

## 設計上のポイント

* `Prog` の条件 `condOf` は**各ヘッドが今読んでいる記号だけ**を見られる。
  `program'` の分岐（`Tape.read (Tape.step blank (ts tAn) blank .left) = mark` など）は
  「左隣のセル」を見るので、**プローブ（左へ動いて読む）を実行してから `ite` する**
  形に組み替える。`program'` 側のプローブ動作（`probeActs` / `sUpActs` / `perDown` /
  `resDown` の先頭動作）がちょうどそのプローブになっているので、
  **マイクロステップ数は増えない**（動作列は完全に一致する）。
* `perLoop1` / `perUp` / `resLoop` は数（`p₁`, `q`）に関する再帰で定義されているので、
  カウンタテープ／パターンテープの読みを条件とする `loop` に組み替え、
  `CounterView'` / `SeqView` 不変量を使った帰納法で一致を示す。
* `resLoop` の mod `k` 位相は `resChain (k-1)` という**右ネストした `ite` の鎖**として
  有限制御に埋め込む（途中で `startSym` を踏んだら鎖を抜ける）。
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace PalPeg.GSProg

open PegSeparation.RealTimeTM
open PalPeg.GSTapes
open PalPeg.Program
open PalPeg.ProgLang

variable {sc : ℕ}

/-! ## 1. 有限な動作・条件の添字型 -/

/-- 動作識別子：`(テープ番号, 読んだ記号を書き戻すか, 移動)`。
`false` のときは `blank` を書く。 -/
abbrev Act8 := Fin 8 × Bool × Move

/-- 条件識別子。 -/
inductive Cond8 where
  /-- テープ `j` の読みが `mark` でない。 -/
  | notMark (j : Fin 8) : Cond8
  /-- パターンテープの読みが `startSym` でない。 -/
  | notStart : Cond8
  /-- 一致枝の条件（`P` の読みが `endSym` でなく `Txt` の読みと等しい）。 -/
  | matchOk : Cond8
  deriving DecidableEq

instance : Fintype Cond8 :=
  Fintype.ofList ((List.finRange 8).map Cond8.notMark ++ [Cond8.notStart, Cond8.matchOk])
    (by rintro (j | _ | _) <;> simp)

variable {Terminal : Type}

/-- 動作の解釈。入力記号は見ない。 -/
def actOf8 (blank : Fin sc) (a : Act8) (_ : Option Terminal) (σ : Fin 8 → Fin sc) :
    Fin 8 → Fin sc × Move :=
  touchVec a.1 (if a.2.1 then σ a.1 else blank) a.2.2 σ

/-- 条件の解釈。 -/
def condOf8 (endSym mark startSym : Fin sc) : Cond8 → (Fin 8 → Fin sc) → Bool
  | .notMark j, σ => decide (σ j ≠ mark)
  | .notStart, σ => decide (σ tP ≠ startSym)
  | .matchOk, σ => decide (σ tP ≠ endSym ∧ σ tP = σ tT)

/-- 8 本テープの GS 走査器の解釈。 -/
def I8 (blank endSym mark startSym : Fin sc) : Interp Terminal Act8 Cond8 (Fin sc) 8 where
  actOf := actOf8 blank
  condOf := condOf8 endSym mark startSym

theorem inputFree_I8 (blank endSym mark startSym : Fin sc) :
    InputFree (I8 (Terminal := Terminal) blank endSym mark startSym) := fun _ _ _ => rfl

/-! ## 2. テープ表現の変換 -/

/-- 成果物のテープを `Prog` 側の zipper へ。 -/
def toS (tp : TapeConfiguration sc) : STape (Fin sc) := ⟨tp.left, tp.focus, tp.right⟩

@[simp] theorem toS_focus (tp : TapeConfiguration sc) : (toS tp).focus = tp.focus := rfl

/-- 8 本まとめて。 -/
def TS (ts : TapesState' sc) : Fin 8 → STape (Fin sc) := fun j => toS (ts j)

@[simp] theorem TS_focus (ts : TapesState' sc) (j : Fin 8) : ((TS ts) j).focus = (ts j).focus :=
  rfl

theorem toS_step (blank : Fin sc) (tp : TapeConfiguration sc) (a : Fin sc) (m : Move) :
    toS (Tape.step blank tp a m) = (toS tp).applyAction blank (a, m) := by
  obtain ⟨L, f, R⟩ := tp
  cases m <;> cases L <;> cases R <;> rfl

/-! ## 3. 動作列 `List (Act' sc)` の write+move ベクトル列 -/

/-- `Act'` が書き込む記号。 -/
def writeOf (ts : TapesState' sc) : Act' sc → Fin sc
  | .keep i _ => (ts i).focus
  | .put _ x _ => x

/-- `Act'` の移動。 -/
def moveOf : Act' sc → Move
  | .keep _ m => m
  | .put _ _ m => m

/-- `Act'` に対応する 8 テープ分の write+move ベクトル。 -/
def avec (ts : TapesState' sc) (a : Act' sc) : Fin 8 → Fin sc × Move :=
  fun j => if j = actTape a then (writeOf ts a, moveOf a) else ((ts j).focus, Move.stay)

/-- 動作列に対応するベクトル列（各段の状態で評価する）。 -/
def avecs (blank : Fin sc) : List (Act' sc) → TapesState' sc → List (Fin 8 → Fin sc × Move)
  | [], _ => []
  | a :: l, ts => avec ts a :: avecs blank l (applyAct' blank ts a)

@[simp] theorem avecs_nil (blank : Fin sc) (ts : TapesState' sc) :
    avecs blank [] ts = [] := rfl

@[simp] theorem avecs_cons (blank : Fin sc) (a : Act' sc) (l : List (Act' sc))
    (ts : TapesState' sc) :
    avecs blank (a :: l) ts = avec ts a :: avecs blank l (applyAct' blank ts a) := rfl

@[simp] theorem avecs_length (blank : Fin sc) :
    ∀ (l : List (Act' sc)) (ts : TapesState' sc), (avecs blank l ts).length = l.length := by
  intro l
  induction l with
  | nil => intro ts; rfl
  | cons a l ih => intro ts; simp [ih]

theorem avecs_append (blank : Fin sc) :
    ∀ (l₁ l₂ : List (Act' sc)) (ts : TapesState' sc),
      avecs blank (l₁ ++ l₂) ts
        = avecs blank l₁ ts ++ avecs blank l₂ (applyActs' blank l₁ ts) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ ts; rfl
  | cons a l ih => intro l₂ ts; simp [ih]

/-- 1 動作分：ベクトルの適用は `applyAct'` に一致する。 -/
theorem applyTrace_avec (blank : Fin sc) (ts : TapesState' sc) (a : Act' sc) :
    (fun j => ((TS ts) j).applyAction blank (avec ts a j)) = TS (applyAct' blank ts a) := by
  funext j
  by_cases hj : j = actTape a
  · subst hj
    cases a with
    | keep i m =>
        show (toS (ts i)).applyAction blank (avec ts (Act'.keep i m) i)
          = toS (applyAct' blank ts (Act'.keep i m) i)
        rw [applyAct'_keep_self, toS_step]
        simp [avec, actTape, writeOf, moveOf]
    | put i x m =>
        show (toS (ts i)).applyAction blank (avec ts (Act'.put i x m) i)
          = toS (applyAct' blank ts (Act'.put i x m) i)
        rw [applyAct'_put_self, toS_step]
        simp [avec, actTape, writeOf, moveOf]
  · show (toS (ts j)).applyAction blank (avec ts a j) = toS (applyAct' blank ts a j)
    rw [applyAct'_ne blank ts a hj]
    simp only [avec, if_neg hj]
    exact ProgLang.applyAction_focus_stay (blank := blank) (toS (ts j))

theorem applyTrace_avecs (blank : Fin sc) :
    ∀ (l : List (Act' sc)) (ts : TapesState' sc),
      applyTrace blank (TS ts) (avecs blank l ts) = TS (applyActs' blank l ts) := by
  intro l
  induction l with
  | nil => intro ts; rfl
  | cons a l ih =>
      intro ts
      rw [avecs_cons, applyTrace_cons]
      show applyTrace blank (fun j => ((TS ts) j).applyAction blank (avec ts a j)) _ = _
      rw [applyTrace_avec, ih]
      rfl

/-! ## 4. `Act'` の動作列に対する `Exec` -/

section ExecA

variable (Terminal : Type)

/-- 「プログラム `P` は状態 `ts` からちょうど動作列 `L` を実行して継続に戻る」。 -/
def ExecA (blank endSym mark startSym : Fin sc)
    (P : Prog Act8 Cond8) (ts : TapesState' sc) (L : List (Act' sc)) : Prop :=
  Exec (I8 (Terminal := Terminal) blank endSym mark startSym) blank P (TS ts) (avecs blank L ts)

variable {Terminal}
variable {blank endSym mark startSym : Fin sc}

theorem execA_of_eq {P : Prog Act8 Cond8} {ts : TapesState' sc} {L L' : List (Act' sc)}
    (h : L = L') (hE : ExecA Terminal blank endSym mark startSym P ts L) :
    ExecA Terminal blank endSym mark startSym P ts L' := h ▸ hE

theorem execA_seq {P Q : Prog Act8 Cond8} {ts : TapesState' sc} {L₁ L₂ : List (Act' sc)}
    (h1 : ExecA Terminal blank endSym mark startSym P ts L₁)
    (h2 : ExecA Terminal blank endSym mark startSym Q (applyActs' blank L₁ ts) L₂) :
    ExecA Terminal blank endSym mark startSym (Prog.seq P Q) ts (L₁ ++ L₂) := by
  unfold ExecA at h1 h2 ⊢
  rw [avecs_append]
  refine exec_seq h1 ?_
  rw [applyTrace_avecs]
  exact h2

theorem execA_skip {ts : TapesState' sc} :
    ExecA Terminal blank endSym mark startSym Prog.skip ts [] := exec_skip _

/-- 読んだ記号を書き戻して移動する動作。 -/
def KEEP (i : Fin 8) (m : Move) : Prog Act8 Cond8 := Prog.act (i, true, m)

/-- `blank` を書いて移動する動作。 -/
def PUT (i : Fin 8) (m : Move) : Prog Act8 Cond8 := Prog.act (i, false, m)

theorem actVec_keep (i : Fin 8) (m : Move) (ts : TapesState' sc) :
    actVec (I8 (Terminal := Terminal) blank endSym mark startSym) (i, true, m) (TS ts)
      = avec ts (Act'.keep i m) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [actVec, I8, actOf8, touchVec, avec, actTape, writeOf, moveOf]
  · simp [actVec, I8, actOf8, touchVec, avec, actTape, hj]

theorem actVec_put (i : Fin 8) (m : Move) (ts : TapesState' sc) :
    actVec (I8 (Terminal := Terminal) blank endSym mark startSym) (i, false, m) (TS ts)
      = avec ts (Act'.put i blank m) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [actVec, I8, actOf8, touchVec, avec, actTape, writeOf, moveOf]
  · simp [actVec, I8, actOf8, touchVec, avec, actTape, hj]

theorem execA_keep (i : Fin 8) (m : Move) (ts : TapesState' sc) :
    ExecA Terminal blank endSym mark startSym (KEEP i m) ts [Act'.keep i m] := by
  have h := exec_act (blank := blank) (inputFree_I8 (Terminal := Terminal)
    blank endSym mark startSym) (i, true, m) (TS ts)
  rw [actVec_keep] at h
  exact h

theorem execA_put (i : Fin 8) (m : Move) (ts : TapesState' sc) :
    ExecA Terminal blank endSym mark startSym (PUT i m) ts [Act'.put i blank m] := by
  have h := exec_act (blank := blank) (inputFree_I8 (Terminal := Terminal)
    blank endSym mark startSym) (i, false, m) (TS ts)
  rw [actVec_put] at h
  exact h

/-! ### 条件つき分岐 -/

theorem condOf_eq (c : Cond8) (ts : TapesState' sc) :
    (I8 (Terminal := Terminal) blank endSym mark startSym).condOf c
        (fun j => ((TS ts) j).focus)
      = condOf8 endSym mark startSym c (fun j => (ts j).focus) := rfl

theorem execA_ite_pos {c : Cond8} {P Q : Prog Act8 Cond8} {ts : TapesState' sc}
    {L : List (Act' sc)} (hc : condOf8 endSym mark startSym c (fun j => (ts j).focus) = true)
    (h : ExecA Terminal blank endSym mark startSym P ts L) :
    ExecA Terminal blank endSym mark startSym (Prog.ite c P Q) ts L :=
  exec_ite_pos (by rw [condOf_eq]; exact hc) h

theorem execA_ite_neg {c : Cond8} {P Q : Prog Act8 Cond8} {ts : TapesState' sc}
    {L : List (Act' sc)} (hc : condOf8 endSym mark startSym c (fun j => (ts j).focus) = false)
    (h : ExecA Terminal blank endSym mark startSym Q ts L) :
    ExecA Terminal blank endSym mark startSym (Prog.ite c P Q) ts L :=
  exec_ite_neg (by rw [condOf_eq]; exact hc) h

theorem execA_loop_stop {c : Cond8} {a : Act8} {b : Prog Act8 Cond8} {ts : TapesState' sc}
    (hc : condOf8 endSym mark startSym c (fun j => (ts j).focus) = false) :
    ExecA Terminal blank endSym mark startSym (Prog.loop c a b) ts [] :=
  exec_loop_stop (by rw [condOf_eq]; exact hc)

theorem execA_loop_cont {c : Cond8} {i : Fin 8} {m : Move} {b : Prog Act8 Cond8}
    {ts : TapesState' sc} {L₁ L₂ : List (Act' sc)}
    (hc : condOf8 endSym mark startSym c (fun j => (ts j).focus) = true)
    (h1 : ExecA Terminal blank endSym mark startSym b
      (applyAct' blank ts (Act'.put i blank m)) L₁)
    (h2 : ExecA Terminal blank endSym mark startSym (Prog.loop c (i, false, m) b)
      (applyActs' blank L₁ (applyAct' blank ts (Act'.put i blank m))) L₂) :
    ExecA Terminal blank endSym mark startSym (Prog.loop c (i, false, m) b) ts
      (Act'.put i blank m :: (L₁ ++ L₂)) := by
  unfold ExecA at h1 h2 ⊢
  rw [avecs_cons, avecs_append]
  have hT : (fun j => ((TS ts) j).applyAction blank
      (actVec (I8 (Terminal := Terminal) blank endSym mark startSym) (i, false, m)
        (TS ts) j)) = TS (applyAct' blank ts (Act'.put i blank m)) := by
    rw [actVec_put]; exact applyTrace_avec blank ts (Act'.put i blank m)
  refine exec_loop_cont (inputFree_I8 blank endSym mark startSym)
    (by rw [condOf_eq]; exact hc) ?_ ?_
  · rw [hT]; exact h1
  · rw [hT, applyTrace_avecs]; exact h2
  
end ExecA

/-! ## 5. 符号付きカウンタ更新のプログラム化 -/

section Programs

/-- `sUpActs` のプローブ後の残り。 -/
def sUpRest (blank mark : Fin sc) (i j : Fin 8) (tpj : TapeConfiguration sc) :
    List (Act' sc) :=
  if Tape.read (Tape.step blank tpj blank .left) = mark then
    [Act'.keep j .right, Act'.put i blank .right]
  else [Act'.put j blank .stay]

theorem sUpActs_eq_cons (blank mark : Fin sc) (i j : Fin 8)
    (tpj : TapeConfiguration sc) :
    sUpActs blank mark i j tpj = Act'.put j blank .left :: sUpRest blank mark i j tpj := by
  unfold sUpActs sUpRest
  split_ifs <;> rfl

/-- `sUpActs` のプローブ後の部分。 -/
def sUpTail (i j : Fin 8) : Prog Act8 Cond8 :=
  Prog.ite (Cond8.notMark j) (PUT j .stay) (Prog.seq (KEEP j .right) (PUT i .right))

/-- 符号付きカウンタ対 `(i, j)` の 1 増加。 -/
def sUpProg (i j : Fin 8) : Prog Act8 Cond8 := Prog.seq (PUT j .left) (sUpTail i j)

/-- `q ← q + 1` のカウンタ更新。 -/
def qIncProg : Prog Act8 Cond8 := Prog.seq (sUpProg tAp tAn) (sUpProg tRn tRp)

/-- `q ← q - 1` のカウンタ更新。 -/
def qDecProg : Prog Act8 Cond8 := Prog.seq (sUpProg tAn tAp) (sUpProg tRp tRn)

/-- `qDecProg` の先頭 1 動作を除いた残り。 -/
def qDecTail : Prog Act8 Cond8 := Prog.seq (sUpTail tAn tAp) (sUpProg tRp tRn)

/-- 一致枝。 -/
def advProg : Prog Act8 Cond8 :=
  Prog.seq (KEEP tP .right) (Prog.seq (KEEP tT .right) qIncProg)

end Programs

section ProgSpec

variable {Terminal : Type} {blank endSym mark startSym : Fin sc}

theorem qIncActs_congr {ts₁ ts₂ : TapesState' sc} (h1 : ts₁ tAn = ts₂ tAn)
    (h2 : ts₁ tRp = ts₂ tRp) :
    qIncActs blank mark ts₁ = qIncActs blank mark ts₂ := by
  unfold qIncActs; rw [h1, h2]

theorem qDecActs_congr {ts₁ ts₂ : TapesState' sc} (h1 : ts₁ tAp = ts₂ tAp)
    (h2 : ts₁ tRn = ts₂ tRn) :
    qDecActs blank mark ts₁ = qDecActs blank mark ts₂ := by
  unfold qDecActs; rw [h1, h2]

theorem sUpTail_exec (i j : Fin 8) (ts : TapesState' sc) :
    ExecA Terminal blank endSym mark startSym (sUpTail i j)
      (applyAct' blank ts (Act'.put j blank .left)) (sUpRest blank mark i j (ts j)) := by
  set ts' := applyAct' blank ts (Act'.put j blank (sc := sc) .left) with hts'
  have hfoc : (ts' j).focus = Tape.read (Tape.step blank (ts j) blank .left) := by
    rw [hts', applyAct'_put_self]
    rfl
  by_cases hc : Tape.read (Tape.step blank (ts j) blank .left) = mark
  · have hcond : condOf8 endSym mark startSym (Cond8.notMark j)
        (fun l => (ts' l).focus) = false := by
      simp [condOf8, hfoc, Tape.read] at hc ⊢
      exact hc
    refine execA_ite_neg hcond ?_
    have h1 := execA_keep (Terminal := Terminal) (blank := blank) (endSym := endSym)
      (mark := mark) (startSym := startSym) j Move.right ts'
    have h2 := execA_put (Terminal := Terminal) (blank := blank) (endSym := endSym)
      (mark := mark) (startSym := startSym) i Move.right
      (applyActs' blank [Act'.keep j (sc := sc) .right] ts')
    have := execA_seq h1 h2
    refine execA_of_eq ?_ this
    unfold sUpRest
    rw [if_pos hc]
    rfl
  · have hcond : condOf8 endSym mark startSym (Cond8.notMark j)
        (fun l => (ts' l).focus) = true := by
      simp [condOf8, hfoc, Tape.read] at hc ⊢
      exact hc
    refine execA_ite_pos hcond ?_
    have h1 := execA_put (Terminal := Terminal) (blank := blank) (endSym := endSym)
      (mark := mark) (startSym := startSym) j Move.stay ts'
    refine execA_of_eq ?_ h1
    unfold sUpRest
    rw [if_neg hc]

theorem sUpProg_exec (i j : Fin 8) (ts : TapesState' sc) :
    ExecA Terminal blank endSym mark startSym (sUpProg i j) ts
      (sUpActs blank mark i j (ts j)) := by
  rw [sUpActs_eq_cons]
  have h1 := execA_put (Terminal := Terminal) (blank := blank) (endSym := endSym)
    (mark := mark) (startSym := startSym) j Move.left ts
  exact execA_seq h1 (sUpTail_exec i j ts)

theorem qIncProg_exec (ts : TapesState' sc) :
    ExecA Terminal blank endSym mark startSym qIncProg ts (qIncActs blank mark ts) := by
  have h1 := sUpProg_exec (Terminal := Terminal) (blank := blank) (endSym := endSym)
    (mark := mark) (startSym := startSym) tAp tAn ts
  have huntouched : (applyActs' blank (sUpActs blank mark tAp tAn (ts tAn)) ts) tRp
      = ts tRp := sUpActs_untouched _ _ _ _ _ _ (by decide) (by decide)
  have h2 := sUpProg_exec (Terminal := Terminal) (blank := blank) (endSym := endSym)
    (mark := mark) (startSym := startSym) tRn tRp
    (applyActs' blank (sUpActs blank mark tAp tAn (ts tAn)) ts)
  rw [huntouched] at h2
  exact execA_seq h1 h2

theorem qDecProg_exec (ts : TapesState' sc) :
    ExecA Terminal blank endSym mark startSym qDecProg ts (qDecActs blank mark ts) := by
  have h1 := sUpProg_exec (Terminal := Terminal) (blank := blank) (endSym := endSym)
    (mark := mark) (startSym := startSym) tAn tAp ts
  have huntouched : (applyActs' blank (sUpActs blank mark tAn tAp (ts tAp)) ts) tRn
      = ts tRn := sUpActs_untouched _ _ _ _ _ _ (by decide) (by decide)
  have h2 := sUpProg_exec (Terminal := Terminal) (blank := blank) (endSym := endSym)
    (mark := mark) (startSym := startSym) tRp tRn
    (applyActs' blank (sUpActs blank mark tAn tAp (ts tAp)) ts)
  rw [huntouched] at h2
  exact execA_seq h1 h2

/-- `qDecActs` の先頭はテープ `tAp` のプローブ。 -/
theorem qDecActs_eq_cons (ts : TapesState' sc) :
    qDecActs blank mark ts = Act'.put tAp blank .left ::
      (sUpRest blank mark tAn tAp (ts tAp) ++ sUpActs blank mark tRp tRn (ts tRn)) := by
  unfold qDecActs
  rw [sUpActs_eq_cons]
  rfl

theorem qDecTail_exec (ts : TapesState' sc) :
    ExecA Terminal blank endSym mark startSym qDecTail
      (applyAct' blank ts (Act'.put tAp blank .left))
      (sUpRest blank mark tAn tAp (ts tAp) ++ sUpActs blank mark tRp tRn (ts tRn)) := by
  have h1 := sUpTail_exec (Terminal := Terminal) (blank := blank) (endSym := endSym)
    (mark := mark) (startSym := startSym) tAn tAp ts
  have huntouched : (applyActs' blank (sUpActs blank mark tAn tAp (ts tAp)) ts) tRn
      = ts tRn := sUpActs_untouched _ _ _ _ _ _ (by decide) (by decide)
  have hstate : applyActs' blank (sUpRest blank mark tAn tAp (ts tAp))
      (applyAct' blank ts (Act'.put tAp blank .left))
      = applyActs' blank (sUpActs blank mark tAn tAp (ts tAp)) ts := by
    rw [sUpActs_eq_cons]
    rfl
  have h2 := sUpProg_exec (Terminal := Terminal) (blank := blank) (endSym := endSym)
    (mark := mark) (startSym := startSym) tRp tRn
    (applyActs' blank (sUpActs blank mark tAn tAp (ts tAp)) ts)
  rw [huntouched] at h2
  rw [← hstate] at h2
  exact execA_seq h1 h2

theorem advProg_exec (ts : TapesState' sc) :
    ExecA Terminal blank endSym mark startSym advProg ts (advActs blank mark ts) := by
  have h1 := execA_keep (Terminal := Terminal) (blank := blank) (endSym := endSym)
    (mark := mark) (startSym := startSym) tP Move.right ts
  set ts1 := applyActs' blank [Act'.keep tP (sc := sc) .right] ts with hts1
  have h2 := execA_keep (Terminal := Terminal) (blank := blank) (endSym := endSym)
    (mark := mark) (startSym := startSym) tT Move.right ts1
  set ts2 := applyActs' blank [Act'.keep tT (sc := sc) .right] ts1 with hts2
  have hAn : ts2 tAn = ts tAn := by
    rw [hts2, hts1]
    exact (applyAct'_keep_ne (i := tT) (j := tAn) blank _ Move.right (by decide)).trans
      (applyAct'_keep_ne (i := tP) (j := tAn) blank ts Move.right (by decide))
  have hRp : ts2 tRp = ts tRp := by
    rw [hts2, hts1]
    exact (applyAct'_keep_ne (i := tT) (j := tRp) blank _ Move.right (by decide)).trans
      (applyAct'_keep_ne (i := tP) (j := tRp) blank ts Move.right (by decide))
  have h3 := qIncProg_exec (Terminal := Terminal) (blank := blank) (endSym := endSym)
    (mark := mark) (startSym := startSym) ts2
  rw [qIncActs_congr hAn hRp] at h3
  have := execA_seq h1 (execA_seq h2 h3)
  refine execA_of_eq ?_ this
  unfold advActs advPre
  rfl

end ProgSpec

/-! ## 6. 周期ずらし枝 -/

section PerProgram

/-- 下げループの本体（プローブ済み・カウンタを 1 下げた直後から）。 -/
def perBody : Prog Act8 Cond8 :=
  Prog.seq (PUT tC2 .right) (Prog.seq (KEEP tP .left) (Prog.seq qDecProg (PUT tC1 .left)))

/-- `perLoop1` に対応するループ。 -/
def perDownLoop : Prog Act8 Cond8 :=
  Prog.loop (Cond8.notMark tC1) (tC1, false, Move.stay) perBody

/-- 上げループの本体。 -/
def perUpBody : Prog Act8 Cond8 := Prog.seq (PUT tC1 .right) (PUT tC2 .left)

/-- `perUp` に対応するループ。 -/
def perUpLoop : Prog Act8 Cond8 :=
  Prog.loop (Cond8.notMark tC2) (tC2, false, Move.stay) perUpBody

/-- 周期ずらし枝の全体。 -/
def perProg : Prog Act8 Cond8 :=
  Prog.seq (PUT tC1 .left)
    (Prog.seq perDownLoop
      (Prog.seq (KEEP tC1 .right)
        (Prog.seq (PUT tC2 .left) (Prog.seq perUpLoop (KEEP tC2 .right)))))

end PerProgram

section PerSpec

variable {Terminal : Type} {blank endSym mark startSym : Fin sc}

/-- プローブ後のカウンタ条件は「カウンタ値が 0 でない」に一致する。 -/
theorem counter_probe_cond {ts : TapesState' sc} {j : Fin 8} {n : ℕ}
    (hne : mark ≠ blank) (h : Tape.CounterView' blank mark (ts j) n) :
    condOf8 endSym mark startSym (Cond8.notMark j)
        (fun l => ((applyAct' blank ts (Act'.put j blank .left)) l).focus)
      = decide (n ≠ 0) := by
  have hfoc : ((applyAct' blank ts (Act'.put j blank .left)) j).focus
      = Tape.read (Tape.step blank (ts j) blank .left) := by
    rw [applyAct'_put_self]; rfl
  simp only [condOf8, hfoc, ne_eq, Tape.counter'_isZero_iff hne h]

theorem perDown_tC1 (ts : TapesState' sc) :
    applyActs' blank (perDown blank mark ts) ts tC1
      = Tape.step blank (Tape.step blank (ts tC1) blank .left) blank .stay := by
  unfold perDown
  rw [applyActs'_append,
    qDecActs_untouched _ _ _ _ (by decide) (by decide) (by decide) (by decide)]
  simp [perPre, applyActs', applyAct', upd, tP, tC1, tC2]

/-- `perLoop1 (m+1)` の展開（先頭はカウンタ `tC1` のプローブ）。 -/
theorem perLoop1_succ_append (blank mark : Fin sc) (m : ℕ) (ts : TapesState' sc)
    (x : Act' sc) :
    perLoop1 blank mark (m + 1) ts ++ [x] = Act'.put tC1 blank .left ::
      ((Act'.put tC1 blank .stay ::
        [Act'.put tC2 blank .right, Act'.keep tP .left]) ++ qDecActs blank mark ts ++
        (perLoop1 blank mark m (applyActs' blank (perDown blank mark ts) ts) ++ [x])) := by
  rw [perLoop1]
  unfold perDown perPre
  simp

theorem perLoop1_head (blank mark : Fin sc) (n : ℕ) (ts : TapesState' sc) :
    ∃ L, perLoop1 blank mark n ts ++ [Act'.put tC1 blank .left]
      = Act'.put tC1 blank .left :: L := by
  cases n with
  | zero => exact ⟨[], rfl⟩
  | succ m => exact ⟨_, perLoop1_succ_append blank mark m ts _⟩

/-- **下げループの一致**。カウンタ `tC1` が `n` を保持していれば、`perDownLoop` は
（先頭のプローブを除き、末尾に次のプローブを足した）`perLoop1` の動作列を出す。 -/
theorem perDownLoop_exec (hne : mark ≠ blank) :
    ∀ (n : ℕ) (ts : TapesState' sc) (L : List (Act' sc)),
      Tape.CounterView' blank mark (ts tC1) n →
      perLoop1 blank mark n ts ++ [Act'.put tC1 blank .left] = Act'.put tC1 blank .left :: L →
      ExecA Terminal blank endSym mark startSym perDownLoop
        (applyAct' blank ts (Act'.put tC1 blank .left)) L := by
  intro n
  induction n with
  | zero =>
      intro ts L hC heq
      have hL : L = [] := by
        have h0 : perLoop1 blank mark 0 ts = [] := rfl
        rw [h0, List.nil_append] at heq
        exact ((List.cons.inj heq).2).symm
      subst hL
      exact execA_loop_stop (by rw [counter_probe_cond hne hC]; simp)
  | succ m ih =>
      intro ts L hC heq
      rw [perLoop1_succ_append] at heq
      have hL := ((List.cons.inj heq).2).symm
      subst hL
      set ts₁ := applyActs' blank (perDown blank mark ts) ts with hts₁
      obtain ⟨L₂, hL₂⟩ := perLoop1_head blank mark m ts₁
      set L₁ : List (Act' sc) :=
        [Act'.put tC2 blank .right, Act'.keep tP .left] ++ qDecActs blank mark ts ++
          [Act'.put tC1 blank .left] with hL₁
      have hsplit :
          (Act'.put tC1 blank .stay :: [Act'.put tC2 blank .right, Act'.keep tP .left]) ++
              qDecActs blank mark ts ++ (perLoop1 blank mark m ts₁ ++ [Act'.put tC1 blank .left])
            = Act'.put tC1 blank .stay :: (L₁ ++ L₂) := by
        rw [hL₂, hL₁]; simp
      rw [hsplit]
      -- 状態の同定
      have hu0 : applyAct' blank (applyAct' blank ts (Act'.put tC1 blank .left))
          (Act'.put tC1 blank .stay)
          = applyActs' blank [Act'.put tC1 blank .left, Act'.put tC1 blank (sc := sc) .stay] ts :=
        rfl
      have hcat : [Act'.put tC1 blank .left, Act'.put tC1 blank (sc := sc) .stay] ++ L₁
          = perDown blank mark ts ++ [Act'.put tC1 blank .left] := by
        rw [hL₁]; unfold perDown perPre; simp
      have hstate : applyActs' blank L₁
            (applyAct' blank (applyAct' blank ts (Act'.put tC1 blank .left))
              (Act'.put tC1 blank .stay))
          = applyAct' blank ts₁ (Act'.put tC1 blank .left) := by
        rw [hu0, ← applyActs'_append, hcat, applyActs'_append, hts₁]
        rfl
      refine execA_loop_cont ?_ ?_ ?_
      · rw [counter_probe_cond hne hC]; simp
      · -- 本体
        set u0 := applyAct' blank (applyAct' blank ts (Act'.put tC1 blank .left))
          (Act'.put tC1 blank .stay) with hu0def
        have e1 := execA_put (Terminal := Terminal) (blank := blank) (endSym := endSym)
          (mark := mark) (startSym := startSym) tC2 Move.right u0
        set u1 := applyActs' blank [Act'.put tC2 blank (sc := sc) .right] u0 with hu1
        have e2 := execA_keep (Terminal := Terminal) (blank := blank) (endSym := endSym)
          (mark := mark) (startSym := startSym) tP Move.left u1
        set u2 := applyActs' blank [Act'.keep tP (sc := sc) .left] u1 with hu2
        have hAp : u2 tAp = ts tAp := by
          rw [hu2, hu1, hu0def]
          exact (applyAct'_keep_ne (i := tP) (j := tAp) blank _ Move.left (by decide)).trans
            ((applyAct'_put_ne (i := tC2) (j := tAp) blank _ blank Move.right (by decide)).trans
              ((applyAct'_put_ne (i := tC1) (j := tAp) blank _ blank Move.stay (by decide)).trans
                (applyAct'_put_ne (i := tC1) (j := tAp) blank ts blank Move.left (by decide))))
        have hRn : u2 tRn = ts tRn := by
          rw [hu2, hu1, hu0def]
          exact (applyAct'_keep_ne (i := tP) (j := tRn) blank _ Move.left (by decide)).trans
            ((applyAct'_put_ne (i := tC2) (j := tRn) blank _ blank Move.right (by decide)).trans
              ((applyAct'_put_ne (i := tC1) (j := tRn) blank _ blank Move.stay (by decide)).trans
                (applyAct'_put_ne (i := tC1) (j := tRn) blank ts blank Move.left (by decide))))
        have e3 := qDecProg_exec (Terminal := Terminal) (blank := blank) (endSym := endSym)
          (mark := mark) (startSym := startSym) u2
        rw [qDecActs_congr hAp hRn] at e3
        set u3 := applyActs' blank (qDecActs blank mark ts) u2 with hu3
        have e4 := execA_put (Terminal := Terminal) (blank := blank) (endSym := endSym)
          (mark := mark) (startSym := startSym) tC1 Move.left u3
        have := execA_seq e1 (execA_seq e2 (execA_seq e3 e4))
        refine execA_of_eq ?_ this
        rw [hL₁]; simp
      · rw [hstate]
        refine ih ts₁ L₂ ?_ hL₂
        have : ts₁ tC1 = Tape.step blank (Tape.step blank (ts tC1) blank .left) blank .stay := by
          rw [hts₁]; exact perDown_tC1 ts
        rw [this]
        exact Tape.counter'_dec hC

/-! ### 上げループ -/

theorem perUp_succ_append (blank : Fin sc) (m : ℕ) (x : Act' sc) :
    perUp blank (m + 1) ++ [x] = Act'.put tC2 blank .left ::
      ((Act'.put tC2 blank .stay :: [Act'.put tC1 blank .right]) ++
        (perUp blank m ++ [x])) := by
  rw [perUp]; simp

theorem perUp_head (blank : Fin sc) (n : ℕ) :
    ∃ L, perUp blank n ++ [Act'.put tC2 blank .left]
      = Act'.put tC2 blank .left :: L := by
  cases n with
  | zero => exact ⟨[], rfl⟩
  | succ m => exact ⟨_, perUp_succ_append blank m _⟩

theorem perUp_tC2 (ts : TapesState' sc) :
    applyActs' blank [Act'.put tC2 blank .left, Act'.put tC2 blank .stay,
        Act'.put tC1 blank (sc := sc) .right] ts tC2
      = Tape.step blank (Tape.step blank (ts tC2) blank .left) blank .stay := by
  simp [applyActs', applyAct', upd, tC1, tC2]

/-- **上げループの一致**。 -/
theorem perUpLoop_exec (hne : mark ≠ blank) :
    ∀ (n : ℕ) (ts : TapesState' sc) (L : List (Act' sc)),
      Tape.CounterView' blank mark (ts tC2) n →
      perUp blank n ++ [Act'.put tC2 blank .left] = Act'.put tC2 blank .left :: L →
      ExecA Terminal blank endSym mark startSym perUpLoop
        (applyAct' blank ts (Act'.put tC2 blank .left)) L := by
  intro n
  induction n with
  | zero =>
      intro ts L hC heq
      have hL : L = [] := by
        have h0 : perUp blank 0 = [] := rfl
        rw [h0, List.nil_append] at heq
        exact ((List.cons.inj heq).2).symm
      subst hL
      exact execA_loop_stop (by rw [counter_probe_cond hne hC]; simp)
  | succ m ih =>
      intro ts L hC heq
      rw [perUp_succ_append] at heq
      have hL := ((List.cons.inj heq).2).symm
      subst hL
      set ts₁ := applyActs' blank [Act'.put tC2 blank .left, Act'.put tC2 blank .stay,
        Act'.put tC1 blank (sc := sc) .right] ts with hts₁
      obtain ⟨L₂, hL₂⟩ := perUp_head blank m
      have hsplit : (Act'.put tC2 blank .stay :: [Act'.put tC1 blank (sc := sc) .right]) ++
            (perUp blank m ++ [Act'.put tC2 blank .left])
          = Act'.put tC2 blank .stay ::
            ([Act'.put tC1 blank .right, Act'.put tC2 blank (sc := sc) .left] ++ L₂) := by
        rw [hL₂]; simp
      rw [hsplit]
      have hstate : applyActs' blank
            [Act'.put tC1 blank .right, Act'.put tC2 blank (sc := sc) .left]
            (applyAct' blank (applyAct' blank ts (Act'.put tC2 blank .left))
              (Act'.put tC2 blank .stay))
          = applyAct' blank ts₁ (Act'.put tC2 blank .left) := by
        rw [hts₁]; rfl
      refine execA_loop_cont ?_ ?_ ?_
      · rw [counter_probe_cond hne hC]; simp
      · set u0 := applyAct' blank (applyAct' blank ts (Act'.put tC2 blank .left))
          (Act'.put tC2 blank .stay) with hu0
        have e1 := execA_put (Terminal := Terminal) (blank := blank) (endSym := endSym)
          (mark := mark) (startSym := startSym) tC1 Move.right u0
        have e2 := execA_put (Terminal := Terminal) (blank := blank) (endSym := endSym)
          (mark := mark) (startSym := startSym) tC2 Move.left
          (applyActs' blank [Act'.put tC1 blank (sc := sc) .right] u0)
        exact execA_seq e1 e2
      · rw [hstate]
        refine ih ts₁ L₂ ?_ hL₂
        have h : ts₁ tC2
            = Tape.step blank (Tape.step blank (ts tC2) blank .left) blank .stay := by
          rw [hts₁]; exact perUp_tC2 ts
        rw [h]
        exact Tape.counter'_dec hC

/-! ### 周期ずらし枝の全体 -/

/-- **周期ずらし枝の一致**。 -/
theorem perProg_exec (hne : mark ≠ blank) {w : List (Fin sc)} {ts : TapesState' sc}
    {p₁ q mm r : ℕ} (hle : p₁ ≤ q)
    (hP : Tape.SeqView blank (ts tP) w (q + 1))
    (hc1 : Tape.CounterView' blank mark (ts tC1) p₁)
    (hc2 : Tape.CounterView' blank mark (ts tC2) 0)
    (hQ : CQuad blank mark ts mm r q) :
    ExecA Terminal blank endSym mark startSym perProg ts (perProgram blank mark p₁ ts) := by
  obtain ⟨lP, l1, l2, lQ, lT⟩ :=
    perLoop1_spec (w := w) hne p₁ ts q p₁ 0 mm r hle (Nat.le_refl _) hP hc1 hc2 hQ
  rw [show p₁ - p₁ = 0 from by omega] at l1
  rw [show (0 : ℕ) + p₁ = p₁ from by omega] at l2
  obtain ⟨LD, hLD⟩ := perLoop1_head blank mark p₁ ts
  obtain ⟨LU, hLU⟩ := perUp_head blank p₁
  set v := applyActs' blank (perLoop1 blank mark p₁ ts) ts with hv
  have hchain : applyActs' blank [Act'.keep tC1 (sc := sc) .right]
      (applyActs' blank LD (applyActs' blank [Act'.put tC1 blank .left] ts)) = v := by
    rw [← applyActs'_append, ← applyActs'_append, ← List.append_assoc, List.singleton_append,
      ← hLD]
    have : perLoop1 blank mark p₁ ts ++ [Act'.put tC1 blank .left] ++
        [Act'.keep tC1 (sc := sc) .right]
        = perLoop1 blank mark p₁ ts ++ probeActs blank tC1 := by
      unfold probeActs; simp
    rw [this, applyActs'_append, hv, probeActs_id l1]
  have e0 := execA_put (Terminal := Terminal) (blank := blank) (endSym := endSym)
    (mark := mark) (startSym := startSym) tC1 Move.left ts
  have eDown := perDownLoop_exec (Terminal := Terminal) (endSym := endSym)
    (startSym := startSym) hne p₁ ts LD hc1 hLD
  have eK1 := execA_keep (Terminal := Terminal) (blank := blank) (endSym := endSym)
    (mark := mark) (startSym := startSym) tC1 Move.right
    (applyActs' blank LD (applyActs' blank [Act'.put tC1 blank .left] ts))
  have eP2 := execA_put (Terminal := Terminal) (blank := blank) (endSym := endSym)
    (mark := mark) (startSym := startSym) tC2 Move.left v
  have eUp := perUpLoop_exec (Terminal := Terminal) (endSym := endSym)
    (startSym := startSym) hne p₁ v LU l2 hLU
  have eK2 := execA_keep (Terminal := Terminal) (blank := blank) (endSym := endSym)
    (mark := mark) (startSym := startSym) tC2 Move.right
    (applyActs' blank LU (applyActs' blank [Act'.put tC2 blank .left] v))
  have hstep2 : applyActs' blank [Act'.put tC2 blank (sc := sc) .left] v
      = applyAct' blank v (Act'.put tC2 blank .left) := rfl
  rw [← hstep2] at eUp
  have eRest : ExecA Terminal blank endSym mark startSym
      (Prog.seq (KEEP tC1 Move.right)
        (Prog.seq (PUT tC2 Move.left) (Prog.seq perUpLoop (KEEP tC2 Move.right))))
      (applyActs' blank LD (applyActs' blank [Act'.put tC1 blank .left] ts))
      ([Act'.keep tC1 (sc := sc) .right] ++ ([Act'.put tC2 blank .left] ++
        (LU ++ [Act'.keep tC2 (sc := sc) .right]))) := by
    refine execA_seq eK1 ?_
    rw [hchain]
    exact execA_seq eP2 (execA_seq eUp eK2)
  have hbig := execA_seq e0 (execA_seq eDown eRest)
  refine execA_of_eq ?_ hbig
  have hassoc : [Act'.put tC1 blank (sc := sc) .left] ++
        (LD ++ ([Act'.keep tC1 (sc := sc) .right] ++ ([Act'.put tC2 blank .left] ++
          (LU ++ [Act'.keep tC2 (sc := sc) .right]))))
      = (Act'.put tC1 blank .left :: LD) ++ [Act'.keep tC1 (sc := sc) .right] ++
        ((Act'.put tC2 blank .left :: LU) ++ [Act'.keep tC2 (sc := sc) .right]) := by
    simp
  rw [hassoc, ← hLD, ← hLU]
  unfold perProgram probeActs
  simp

end PerSpec

/-! ## 7. リセットずらし枝 -/

section ResProgram

/-- mod `k` 位相の鎖。`startSym` を踏んだら（`skip` 側へ抜けて）鎖を終える。 -/
def resChain : ℕ → Prog Act8 Cond8
  | 0 => KEEP tP .left
  | j + 1 =>
      Prog.seq (KEEP tP .left)
        (Prog.ite Cond8.notStart
          (Prog.seq (KEEP tT .left) (Prog.seq qDecProg (resChain j))) Prog.skip)

/-- `resLoop` に対応するループ（位相 `0` の周を本体の先頭に置く）。 -/
def resLoopProg (k : ℕ) : Prog Act8 Cond8 :=
  Prog.loop Cond8.notStart (tAp, false, Move.left) (Prog.seq qDecTail (resChain (k - 1)))

/-- リセットずらし枝の全体。 -/
def resProg (k : ℕ) : Prog Act8 Cond8 :=
  Prog.seq (KEEP tP .left)
    (Prog.ite Cond8.notStart
      (Prog.seq (resLoopProg k) (KEEP tP .right))
      (Prog.seq (KEEP tP .right) (KEEP tT .right)))

end ResProgram

section ResSpec

variable {Terminal : Type} {blank endSym mark startSym : Fin sc} {v : List (Fin sc)}

/-- 逐次実行の分解（`Exec` を二つに割る）。 -/
def SplitExecA (Terminal : Type) (blank endSym mark startSym : Fin sc)
    (P Q : Prog Act8 Cond8) (ts : TapesState' sc) (L : List (Act' sc)) : Prop :=
  ∃ X Y, L = X ++ Y ∧ ExecA Terminal blank endSym mark startSym P ts X ∧
    ExecA Terminal blank endSym mark startSym Q (applyActs' blank X ts) Y

theorem applyActs'_singleton (blank : Fin sc) (a : Act' sc) (ts : TapesState' sc) :
    applyActs' blank [a] ts = applyAct' blank ts a := rfl

theorem execA_of_split {P Q : Prog Act8 Cond8} {ts : TapesState' sc} {L : List (Act' sc)}
    (h : SplitExecA Terminal blank endSym mark startSym P Q ts L) :
    ExecA Terminal blank endSym mark startSym (Prog.seq P Q) ts L := by
  obtain ⟨X, Y, rfl, h1, h2⟩ := h
  exact execA_seq h1 h2

/-- プローブ後のパターンテープの読みによる `q = 0` 判定。 -/
theorem resCond {ts : TapesState' sc} {n : ℕ} (hstart : startSym ∉ v) (hn : n ≤ v.length)
    (hP : Tape.SeqView blank (ts tP) (startSym :: (v ++ [endSym])) (n + 1)) :
    condOf8 endSym mark startSym Cond8.notStart
        (fun l => ((applyAct' blank ts (Act'.keep tP .left)) l).focus)
      = decide (n ≠ 0) := by
  have hstep : (applyAct' blank ts (Act'.keep tP .left)) tP
      = Tape.step blank (ts tP) (ts tP).focus .left := applyAct'_keep_self ..
  have hfocus := (Tape.seq_move_left hP).focus_eq
  simp only [condOf8, hstep]
  cases n with
  | zero =>
      have h0 : startSym = (Tape.step blank (ts tP) (ts tP).focus .left).focus := by
        simpa using hfocus
      simp [← h0]
  | succ m =>
      have hm : m < v.length := by omega
      have hv : v[m]? = some (Tape.step blank (ts tP) (ts tP).focus .left).focus := by
        rw [← hfocus, List.getElem?_cons_succ, List.getElem?_append_left hm]
      have hmem : (Tape.step blank (ts tP) (ts tP).focus .left).focus ∈ v := by
        obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.1 hv
        exact h2 ▸ List.getElem_mem h1
      have hne : (Tape.step blank (ts tP) (ts tP).focus .left).focus ≠ startSym := by
        intro hc; exact hstart (hc ▸ hmem)
      simp [hne]

/-! ### `resLoop` の展開 -/

theorem resLoop_succ_zero (blank mark : Fin sc) (k m : ℕ) (ts : TapesState' sc) :
    resLoop blank mark k (m + 1) 0 ts ++ [Act'.keep tP .left]
      = Act'.keep tP .left ::
        (qDecActs blank mark ts ++
          (resLoop blank mark k m (k - 1) (applyActs' blank (resDown1 blank mark ts) ts) ++
            [Act'.keep tP .left])) := by
  rw [resLoop]
  unfold resDown1
  simp

theorem resLoop_succ_succ (blank mark : Fin sc) (k m j : ℕ) (ts : TapesState' sc) :
    resLoop blank mark k (m + 1) (j + 1) ts ++ [Act'.keep tP .left]
      = Act'.keep tP .left ::
        ([Act'.keep tT (sc := sc) .left] ++ qDecActs blank mark ts ++
          (resLoop blank mark k m j (applyActs' blank (resDown2 blank mark ts) ts) ++
            [Act'.keep tP .left])) := by
  rw [resLoop]
  unfold resDown2
  simp

theorem resLoop_head (blank mark : Fin sc) (k n c : ℕ) (ts : TapesState' sc) :
    ∃ L, resLoop blank mark k n c ts ++ [Act'.keep tP .left]
      = Act'.keep tP .left :: L := by
  cases n with
  | zero => exact ⟨[], rfl⟩
  | succ m =>
      cases c with
      | zero => exact ⟨_, resLoop_succ_zero blank mark k m ts⟩
      | succ j => exact ⟨_, resLoop_succ_succ blank mark k m j ts⟩

/-! ### 主補題：ループと鎖の一致（`n` に関する強帰納法） -/

theorem res_key (hstart : startSym ∉ v) (k : ℕ) :
    ∀ n : ℕ,
      (∀ (ts : TapesState' sc) (L : List (Act' sc)), n ≤ v.length →
        Tape.SeqView blank (ts tP) (startSym :: (v ++ [endSym])) (n + 1) →
        resLoop blank mark k n 0 ts ++ [Act'.keep tP .left] = Act'.keep tP .left :: L →
        ExecA Terminal blank endSym mark startSym (resLoopProg k)
          (applyAct' blank ts (Act'.keep tP .left)) L)
      ∧ (∀ (j : ℕ) (ts : TapesState' sc), n ≤ v.length →
        Tape.SeqView blank (ts tP) (startSym :: (v ++ [endSym])) (n + 1) →
        SplitExecA Terminal blank endSym mark startSym (resChain j) (resLoopProg k) ts
          (resLoop blank mark k n j ts ++ [Act'.keep tP .left])) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    cases n with
    | zero =>
        have hloop : ∀ (ts : TapesState' sc) (L : List (Act' sc)), 0 ≤ v.length →
            Tape.SeqView blank (ts tP) (startSym :: (v ++ [endSym])) (0 + 1) →
            resLoop blank mark k 0 0 ts ++ [Act'.keep tP .left] = Act'.keep tP .left :: L →
            ExecA Terminal blank endSym mark startSym (resLoopProg k)
              (applyAct' blank ts (Act'.keep tP .left)) L := by
          intro ts L hn hP heq
          have hL : L = [] := by
            have h0 : resLoop blank mark k 0 0 ts = [] := rfl
            rw [h0, List.nil_append] at heq
            exact ((List.cons.inj heq).2).symm
          subst hL
          exact execA_loop_stop (by rw [resCond hstart hn hP]; simp)
        refine ⟨hloop, ?_⟩
        intro j ts hn hP
        refine ⟨[Act'.keep tP .left], [], rfl, ?_, ?_⟩
        · cases j with
          | zero => exact execA_keep tP Move.left ts
          | succ i =>
              have hx : ExecA Terminal blank endSym mark startSym (resChain (i + 1)) ts
                  ([Act'.keep tP (sc := sc) .left] ++ []) :=
                execA_seq (execA_keep tP Move.left ts)
                  (execA_ite_neg (by rw [applyActs'_singleton, resCond hstart hn hP]; simp)
                    execA_skip)
              simpa using hx
        · exact hloop ts [] hn hP rfl
    | succ m =>
        have hmlt : m < m + 1 := by omega
        have hloop : ∀ (ts : TapesState' sc) (L : List (Act' sc)), m + 1 ≤ v.length →
            Tape.SeqView blank (ts tP) (startSym :: (v ++ [endSym])) (m + 1 + 1) →
            resLoop blank mark k (m + 1) 0 ts ++ [Act'.keep tP .left]
              = Act'.keep tP .left :: L →
            ExecA Terminal blank endSym mark startSym (resLoopProg k)
              (applyAct' blank ts (Act'.keep tP .left)) L := by
          intro ts L hn hP heq
          rw [resLoop_succ_zero] at heq
          have hL := ((List.cons.inj heq).2).symm
          subst hL
          set ts' := applyAct' blank ts (Act'.keep tP (sc := sc) .left) with hts'
          have hAp : ts' tAp = ts tAp :=
            applyAct'_keep_ne (i := tP) (j := tAp) blank ts Move.left (by decide)
          have hRn : ts' tRn = ts tRn :=
            applyAct'_keep_ne (i := tP) (j := tRn) blank ts Move.left (by decide)
          have hP' : Tape.SeqView blank (ts' tP) (startSym :: (v ++ [endSym])) (m + 1) := by
            rw [hts', applyAct'_keep_self]
            exact Tape.seq_move_left hP
          have hts₁ : applyActs' blank (resDown1 blank mark ts) ts
              = applyActs' blank (qDecActs blank mark ts) ts' := by
            unfold resDown1
            rw [applyActs'_append]
            rfl
          have hP₁ : Tape.SeqView blank
              ((applyActs' blank (resDown1 blank mark ts) ts) tP)
              (startSym :: (v ++ [endSym])) (m + 1) := by
            rw [hts₁,
              qDecActs_untouched _ _ _ _ (by decide) (by decide) (by decide) (by decide)]
            exact hP'
          obtain ⟨X, Y, hXY, hX, hY⟩ :=
            (IH m hmlt).2 (k - 1) (applyActs' blank (resDown1 blank mark ts) ts)
              (by omega) hP₁
          have hgoal : qDecActs blank mark ts ++
                (resLoop blank mark k m (k - 1)
                  (applyActs' blank (resDown1 blank mark ts) ts) ++ [Act'.keep tP .left])
              = Act'.put tAp blank .left ::
                (((sUpRest blank mark tAn tAp (ts tAp) ++
                    sUpActs blank mark tRp tRn (ts tRn)) ++ X) ++ Y) := by
            rw [qDecActs_eq_cons, hXY]
            simp
          rw [hgoal]
          have hstate : applyActs' blank
                (sUpRest blank mark tAn tAp (ts tAp) ++ sUpActs blank mark tRp tRn (ts tRn))
                (applyAct' blank ts' (Act'.put tAp blank .left))
              = applyActs' blank (resDown1 blank mark ts) ts := by
            rw [hts₁, qDecActs_eq_cons]
            rfl
          refine execA_loop_cont ?_ ?_ ?_
          · rw [hts', resCond hstart hn hP]; simp
          · have hd := qDecTail_exec (Terminal := Terminal) (blank := blank)
              (endSym := endSym) (mark := mark) (startSym := startSym) ts'
            rw [hAp, hRn] at hd
            refine execA_seq hd ?_
            rw [hstate]
            exact hX
          · rw [applyActs'_append, hstate]
            exact hY
        refine ⟨hloop, ?_⟩
        intro j ts hn hP
        cases j with
        | zero =>
            refine ⟨[Act'.keep tP .left], _, (resLoop_succ_zero blank mark k m ts), ?_, ?_⟩
            · exact execA_keep tP Move.left ts
            · exact hloop ts _ hn hP (resLoop_succ_zero blank mark k m ts)
        | succ i =>
            set ts' := applyAct' blank ts (Act'.keep tP (sc := sc) .left) with hts'
            set ts'' := applyAct' blank ts' (Act'.keep tT (sc := sc) .left) with hts''
            have hAp : ts'' tAp = ts tAp :=
              (applyAct'_keep_ne (i := tT) (j := tAp) blank ts' Move.left (by decide)).trans
                (applyAct'_keep_ne (i := tP) (j := tAp) blank ts Move.left (by decide))
            have hRn : ts'' tRn = ts tRn :=
              (applyAct'_keep_ne (i := tT) (j := tRn) blank ts' Move.left (by decide)).trans
                (applyAct'_keep_ne (i := tP) (j := tRn) blank ts Move.left (by decide))
            have hP'' : Tape.SeqView blank (ts'' tP) (startSym :: (v ++ [endSym])) (m + 1) := by
              rw [hts'', applyAct'_keep_ne (i := tT) (j := tP) blank ts' Move.left (by decide),
                hts', applyAct'_keep_self]
              exact Tape.seq_move_left hP
            have hts₂ : applyActs' blank (resDown2 blank mark ts) ts
                = applyActs' blank (qDecActs blank mark ts) ts'' := by
              unfold resDown2
              rw [applyActs'_append]
              rfl
            have hP₂ : Tape.SeqView blank
                ((applyActs' blank (resDown2 blank mark ts) ts) tP)
                (startSym :: (v ++ [endSym])) (m + 1) := by
              rw [hts₂,
                qDecActs_untouched _ _ _ _ (by decide) (by decide) (by decide) (by decide)]
              exact hP''
            obtain ⟨X, Y, hXY, hX, hY⟩ :=
              (IH m hmlt).2 i (applyActs' blank (resDown2 blank mark ts) ts) (by omega) hP₂
            refine ⟨Act'.keep tP .left ::
              ([Act'.keep tT (sc := sc) .left] ++ (qDecActs blank mark ts ++ X)), Y, ?_, ?_, ?_⟩
            · rw [resLoop_succ_succ, hXY]; simp
            · have e1 : applyActs' blank [Act'.keep tP (sc := sc) .left] ts = ts' := rfl
              have e2 : applyActs' blank [Act'.keep tT (sc := sc) .left] ts' = ts'' := rfl
              refine execA_seq (execA_keep tP Move.left ts) ?_
              rw [e1]
              refine execA_ite_pos (by rw [hts', resCond hstart hn hP]; simp) ?_
              refine execA_seq (execA_keep tT Move.left ts') ?_
              rw [e2]
              have hq := qDecProg_exec (Terminal := Terminal) (blank := blank)
                (endSym := endSym) (mark := mark) (startSym := startSym) ts''
              rw [qDecActs_congr hAp hRn] at hq
              refine execA_seq hq ?_
              rw [← hts₂]
              exact hX
            · rw [show applyActs' blank (Act'.keep tP .left ::
                  ([Act'.keep tT (sc := sc) .left] ++ (qDecActs blank mark ts ++ X))) ts
                  = applyActs' blank X (applyActs' blank (resDown2 blank mark ts) ts) from by
                    rw [hts₂]
                    simp only [applyActs'_cons, applyActs'_append]
                    rfl]
              exact hY

/-- **リセットずらし枝の一致**。 -/
theorem resProg_exec (hstart : startSym ∉ v) (k n : ℕ) (ts : TapesState' sc)
    (hn : n ≤ v.length)
    (hP : Tape.SeqView blank (ts tP) (startSym :: (v ++ [endSym])) (n + 1)) :
    ExecA Terminal blank endSym mark startSym (resProg k) ts
      (resProgram blank mark k n ts) := by
  cases n with
  | zero =>
      have hlist : resProgram blank mark k 0 ts
          = [Act'.keep tP (sc := sc) .left] ++
            ([Act'.keep tP (sc := sc) .right] ++ [Act'.keep tT (sc := sc) .right]) := by
        unfold resProgram
        have h0 : resLoop blank mark k 0 0 ts = [] := rfl
        rw [h0]
        simp
      rw [hlist]
      refine execA_seq (execA_keep tP Move.left ts) ?_
      refine execA_ite_neg (by rw [applyActs'_singleton, resCond hstart hn hP]; simp) ?_
      exact execA_seq (execA_keep tP Move.right _) (execA_keep tT Move.right _)
  | succ m =>
      obtain ⟨L, hL⟩ := resLoop_head blank mark k (m + 1) 0 ts
      have hlist : resProgram blank mark k (m + 1) ts
          = [Act'.keep tP (sc := sc) .left] ++ (L ++ [Act'.keep tP (sc := sc) .right]) := by
        unfold resProgram
        rw [show ((if m + 1 = 0 then [Act'.keep tT (sc := sc) .right] else [])
            : List (Act' sc)) = [] from by simp]
        rw [show (Act'.keep tP (sc := sc) .left :: Act'.keep tP (sc := sc) .right :: [])
          = [Act'.keep tP (sc := sc) .left] ++ [Act'.keep tP (sc := sc) .right] from rfl,
          ← List.append_assoc, hL]
        simp
      rw [hlist]
      refine execA_seq (execA_keep tP Move.left ts) ?_
      refine execA_ite_pos (by rw [applyActs'_singleton, resCond hstart hn hP]; simp) ?_
      refine execA_seq ?_ (execA_keep tP Move.right _)
      rw [applyActs'_singleton]
      exact (res_key (Terminal := Terminal) (endSym := endSym) (mark := mark) hstart
        k (m + 1)).1
        ts L hn hP hL

end ResSpec

/-! ## 8. 1 ラウンドの走査プログラム -/

section ScanProg

/-- GS 走査の 1 歩を実現する有限制御プログラム。 -/
def scanProg (k : ℕ) : Prog Act8 Cond8 :=
  Prog.ite Cond8.matchOk advProg
    (Prog.seq (PUT tAn .left)
      (Prog.ite (Cond8.notMark tAn)
        (Prog.seq (KEEP tAn .right)
          (Prog.seq (PUT tRn .left) (Prog.seq (KEEP tRn .right) (resProg k))))
        (Prog.seq (KEEP tAn .right)
          (Prog.seq (PUT tRn .left)
            (Prog.ite (Cond8.notMark tRn)
              (Prog.seq (KEEP tRn .right) (resProg k))
              (Prog.seq (KEEP tRn .right) perProg))))))

end ScanProg

section ScanSpec

variable {Terminal : Type} {blank endSym mark startSym : Fin sc}

theorem probe_cond (ts : TapesState' sc) (j : Fin 8) :
    condOf8 endSym mark startSym (Cond8.notMark j)
        (fun l => ((applyAct' blank ts (Act'.put j blank .left)) l).focus)
      = decide (Tape.read (Tape.step blank (ts j) blank .left) ≠ mark) := by
  simp only [condOf8, applyAct'_put_self]
  rfl

/-- **主定理（1 ラウンドの一致）**：`scanProg k` は状態 `ts` からちょうど
`program' blank endSym mark k ts` の動作列を実行して継続に戻る。 -/
theorem scanProg_exec {v Text : List (Fin sc)} {k p₁ r : ℕ} {ts : TapesState' sc}
    {st : ScanState} (hk : 0 < k) (hne : mark ≠ blank) (hstart : startSym ∉ v)
    (hE : Encodes' blank startSym endSym mark v Text k p₁ r ts st) (hq : st.q ≤ v.length) :
    ExecA Terminal blank endSym mark startSym (scanProg k) ts
      (program' blank endSym mark k ts) := by
  unfold scanProg program'
  by_cases hadv : Tape.read (ts tP) ≠ endSym ∧ Tape.read (ts tP) = Tape.read (ts tT)
  · rw [if_pos hadv]
    exact execA_ite_pos (by simp only [condOf8]; exact decide_eq_true hadv) (advProg_exec ts)
  · rw [if_neg hadv]
    refine execA_ite_neg (by simp only [condOf8]; exact decide_eq_false hadv) ?_
    have hA : applyActs' blank [Act'.keep tAn (sc := sc) .right]
        (applyActs' blank [Act'.put tAn blank .left] ts) = ts := probeActs_id hE.quad.an
    have hR : ∀ ts' : TapesState' sc, ts' tRn = ts tRn →
        applyActs' blank [Act'.keep tRn (sc := sc) .right]
          (applyActs' blank [Act'.put tRn blank .left] ts') = ts' := by
      intro ts' h
      exact probeActs_id (by rw [h]; exact hE.quad.rn)
    have hsplit : ∀ REST : List (Act' sc),
        probeActs blank tAn ++ probeActs blank tRn ++ REST
          = [Act'.put tAn blank .left] ++ ([Act'.keep tAn (sc := sc) .right] ++
            ([Act'.put tRn blank .left] ++
              ([Act'.keep tRn (sc := sc) .right] ++ REST))) := by
      intro REST; unfold probeActs; simp
    by_cases hbAn : Tape.read (Tape.step blank (ts tAn) blank .left) = mark
    · by_cases hbRn : Tape.read (Tape.step blank (ts tRn) blank .left) = mark
      · -- 周期ずらし
        rw [if_pos ⟨hbAn, hbRn⟩, hsplit]
        refine execA_seq (execA_put tAn Move.left ts) ?_
        refine execA_ite_neg (by rw [applyActs'_singleton, probe_cond]; simp only [Tape.read] at hbAn; simp [hbAn]) ?_
        refine execA_seq (execA_keep tAn Move.right _) ?_
        rw [hA]
        refine execA_seq (execA_put tRn Move.left ts) ?_
        refine execA_ite_neg (by rw [applyActs'_singleton, probe_cond]; simp only [Tape.read] at hbRn; simp [hbRn]) ?_
        refine execA_seq (execA_keep tRn Move.right _) ?_
        rw [hR ts rfl]
        have hper := (period_iff' hne hE).1 ⟨hbAn, hbRn⟩
        have hle : p₁ ≤ st.q := le_trans (Nat.le_mul_of_pos_left p₁ hk) hper.1
        rw [p1Of'_eq hE]
        exact perProg_exec (w := startSym :: (v ++ [endSym])) hne hle hE.pat hE.c1 hE.c2
          hE.quad
      · -- リセットずらし（`r < q`）
        rw [if_neg (fun h => hbRn h.2), hsplit]
        refine execA_seq (execA_put tAn Move.left ts) ?_
        refine execA_ite_neg (by rw [applyActs'_singleton, probe_cond]; simp only [Tape.read] at hbAn; simp [hbAn]) ?_
        refine execA_seq (execA_keep tAn Move.right _) ?_
        rw [hA]
        refine execA_seq (execA_put tRn Move.left ts) ?_
        refine execA_ite_pos (by rw [applyActs'_singleton, probe_cond]; simp only [Tape.read] at hbRn; simp [hbRn]) ?_
        refine execA_seq (execA_keep tRn Move.right _) ?_
        rw [hR ts rfl, qOf'_eq hE]
        exact resProg_exec hstart k st.q ts hq hE.pat
    · -- リセットずらし（`q < k * p₁`）
      rw [if_neg (fun h => hbAn h.1), hsplit]
      refine execA_seq (execA_put tAn Move.left ts) ?_
      refine execA_ite_pos (by rw [applyActs'_singleton, probe_cond]; simp only [Tape.read] at hbAn; simp [hbAn]) ?_
      refine execA_seq (execA_keep tAn Move.right _) ?_
      rw [hA]
      refine execA_seq (execA_put tRn Move.left ts) ?_
      refine execA_seq (execA_keep tRn Move.right _) ?_
      rw [hR ts rfl, qOf'_eq hE]
      exact resProg_exec hstart k st.q ts hq hE.pat

/-! ### トレース・停止・長さ -/

variable {v Text : List (Fin sc)} {k p₁ r : ℕ} {ts : TapesState' sc} {st : ScanState}

/-- **トレースの一致**。長さ `|program' …|` の任意の入力記号列に沿って
`[scanProg k]` を走らせたとき、実行される動作列は `program' …` そのもの。 -/
theorem scanProg_trace (hk : 0 < k) (hne : mark ≠ blank) (hstart : startSym ∉ v)
    (hE : Encodes' blank startSym endSym mark v Text k p₁ r ts st) (hq : st.q ≤ v.length)
    (l : List (Option Terminal))
    (hl : l.length = (program' blank endSym mark k ts).length) :
    trace (I8 (Terminal := Terminal) blank endSym mark startSym) blank l
        ([scanProg k], TS ts) = avecs blank (program' blank endSym mark k ts) ts := by
  have h := scanProg_exec (Terminal := Terminal) (startSym := startSym) hk hne hstart hE hq
  have := (h [] l (by rw [avecs_length]; exact hl)).1
  rw [show ([scanProg k] ++ ([] : Stack Act8 Cond8)) = [scanProg k] from rfl] at this
  exact this

/-- トレースの長さは動作列の長さに等しい（プローブによる追加ステップは無い）。 -/
theorem scanProg_trace_length (hk : 0 < k) (hne : mark ≠ blank) (hstart : startSym ∉ v)
    (hE : Encodes' blank startSym endSym mark v Text k p₁ r ts st) (hq : st.q ≤ v.length)
    (l : List (Option Terminal))
    (hl : l.length = (program' blank endSym mark k ts).length) :
    (trace (I8 (Terminal := Terminal) blank endSym mark startSym) blank l
        ([scanProg k], TS ts)).length = (program' blank endSym mark k ts).length := by
  rw [scanProg_trace hk hne hstart hE hq l hl, avecs_length]

/-- **テープの一致**。`|program' …|` マイクロステップ走らせた後のテープ束は、
`applyActs'` で動作列を適用したものに等しい。 -/
theorem scanProg_tapes (hk : 0 < k) (hne : mark ≠ blank) (hstart : startSym ∉ v)
    (hE : Encodes' blank startSym endSym mark v Text k p₁ r ts st) (hq : st.q ≤ v.length)
    (l : List (Option Terminal))
    (hl : l.length = (program' blank endSym mark k ts).length) :
    (runInputs (I8 (Terminal := Terminal) blank endSym mark startSym) blank l
        ([scanProg k], TS ts)).2
      = TS (applyActs' blank (program' blank endSym mark k ts) ts) := by
  rw [runInputs_snd_eq_applyTrace, scanProg_trace hk hne hstart hE hq l hl]
  exact applyTrace_avecs blank _ ts

/-- **停止**。動作列を出し切った後の 1 歩で制御スタックは空になる。 -/
theorem scanProg_halts (hk : 0 < k) (hne : mark ≠ blank) (hstart : startSym ∉ v)
    (hE : Encodes' blank startSym endSym mark v Text k p₁ r ts st) (hq : st.q ≤ v.length)
    (l : List (Option Terminal))
    (hl : l.length = (program' blank endSym mark k ts).length) (x : Option Terminal) :
    (runInputs (I8 (Terminal := Terminal) blank endSym mark startSym) blank (l ++ [x])
      ([scanProg k], TS ts)).1 = [] :=
  exec_halts (scanProg_exec (Terminal := Terminal) (startSym := startSym) hk hne hstart hE hq)
    l (by rw [avecs_length]; exact hl) x

/-- **符号化の保存**（`GSScanTapes.encodes_step'` の言い換え）。トレースを適用した
テープ束は次の走査状態を符号化する。 -/
theorem scanProg_encodes (hk : 0 < k) (hne : mark ≠ blank) (hend : endSym ∉ v)
    (hstart : startSym ∉ v)
    (hE : Encodes' blank startSym endSym mark v Text k p₁ r ts st) (hq : st.q ≤ v.length)
    (hfit : (scanStep v k p₁ r Text st).pos + (scanStep v k p₁ r Text st).q < Text.length)
    (l : List (Option Terminal))
    (hl : l.length = (program' blank endSym mark k ts).length) :
    ∃ ts' : TapesState' sc,
      (runInputs (I8 (Terminal := Terminal) blank endSym mark startSym) blank l
          ([scanProg k], TS ts)).2 = TS ts' ∧
        Encodes' blank startSym endSym mark v Text k p₁ r ts' (scanStep v k p₁ r Text st) :=
  ⟨applyActs' blank (program' blank endSym mark k ts) ts,
    scanProg_tapes hk hne hstart hE hq l hl, encodes_step' hk hne hend hE hq hfit⟩

end ScanSpec

end PalPeg.GSProg
