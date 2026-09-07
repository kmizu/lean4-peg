import PalPeg.GSPreprocessTapes
import PalPeg.ProgLangLib

/-!
# 前処理段（9 本テープ）の有限制御プログラム化 (`GSPreprocessProg`)

`PalPeg.GSPreprocessTapes` の各部品は「テープ状態から計算される動作列
`List (Act sc)`」として書かれている。本ファイルはそれらを
`PalPeg.ProgLang` の構造化プログラム `Prog A9 Cond9` として書き直し、
`ExecA` によって「プログラムが実際にその動作列を実行する」ことを示す。

設計は `PalPeg/GSScanProg.lean`（8 本テープ版）に倣う。
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM
open PalPeg.GSPre
open PalPeg.Program
open PalPeg.ProgLang

variable {sc : ℕ}

/-! ## 1. 有限な動作・条件の添字型 -/

/-- 動作が書き込む記号の種類。 -/
inductive W9 where
  | keep : W9
  | blk : W9
  | mrk : W9
  deriving DecidableEq, Fintype

/-- 動作識別子：`(テープ番号, 書き込む記号, 移動)`。 -/
abbrev A9 := Fin 11 × W9 × Move

/-- 条件識別子。 -/
inductive Cond9 where
  /-- テープ `j` の読みがマーカ記号 `mark` でない（カウンタが非零）。 -/
  | notMark (j : Fin 11) : Cond9
  /-- `V2` の読みが右端番人 `endSym` でない。 -/
  | v2NotEnd : Cond9
  /-- `V1` と `V2` の読みが等しい。 -/
  | v12Eq : Cond9
  deriving DecidableEq

/-! ### テープ番号 -/

def tV1 : Fin 11 := ⟨0, by omega⟩
def tV2 : Fin 11 := ⟨1, by omega⟩
def tCd : Fin 11 := ⟨2, by omega⟩
def tCq : Fin 11 := ⟨3, by omega⟩
def tCe : Fin 11 := ⟨4, by omega⟩
def tCp : Fin 11 := ⟨5, by omega⟩
def tCf : Fin 11 := ⟨6, by omega⟩
def tCs : Fin 11 := ⟨7, by omega⟩
def tCr : Fin 11 := ⟨8, by omega⟩
def tCa : Fin 11 := ⟨9, by omega⟩
def tCb : Fin 11 := ⟨10, by omega⟩

instance : Fintype Cond9 :=
  Fintype.ofList ((List.finRange 11).map Cond9.notMark ++ [Cond9.v2NotEnd, Cond9.v12Eq])
    (by rintro (j | _ | _) <;> simp)

variable {Terminal : Type}

/-- 動作の解釈。入力記号は見ない。 -/
def actOf9 (blank mark : Fin sc) (a : A9) (_ : Option Terminal) (σ : Fin 11 → Fin sc) :
    Fin 11 → Fin sc × Move :=
  touchVec a.1 (match a.2.1 with
    | W9.keep => σ a.1
    | W9.blk => blank
    | W9.mrk => mark) a.2.2 σ

/-- 条件の解釈。 -/
def condOf9 (endSym mark : Fin sc) : Cond9 → (Fin 11 → Fin sc) → Bool
  | .notMark j, σ => decide (σ j ≠ mark)
  | .v2NotEnd, σ => decide (σ tV2 ≠ endSym)
  | .v12Eq, σ => decide (σ tV1 = σ tV2)

/-- 9 本テープの前処理器の解釈。 -/
def I9 (blank endSym mark : Fin sc) : Interp Terminal A9 Cond9 (Fin sc) 11 where
  actOf := actOf9 blank mark
  condOf := condOf9 endSym mark

theorem inputFree_I9 (blank endSym mark : Fin sc) :
    InputFree (I9 (Terminal := Terminal) blank endSym mark) := fun _ _ _ => rfl

/-! ## 2. テープ表現の変換 -/

/-- 成果物のテープを `Prog` 側の zipper へ。 -/
def toS (tp : TapeConfiguration sc) : STape (Fin sc) := ⟨tp.left, tp.focus, tp.right⟩

@[simp] theorem toS_focus (tp : TapeConfiguration sc) : (toS tp).focus = tp.focus := rfl

theorem toS_step (blank : Fin sc) (tp : TapeConfiguration sc) (a : Fin sc) (m : Move) :
    toS (PalPeg.Tape.step blank tp a m) = (toS tp).applyAction blank (a, m) := by
  obtain ⟨L, f, R⟩ := tp
  cases m <;> cases L <;> cases R <;> rfl

/-- 9 本のテープの取り出し。 -/
def getT (ts : Tapes sc) : Fin 11 → TapeConfiguration sc
  | ⟨0, _⟩ => ts.V1
  | ⟨1, _⟩ => ts.V2
  | ⟨2, _⟩ => ts.Cd
  | ⟨3, _⟩ => ts.Cq
  | ⟨4, _⟩ => ts.Ce
  | ⟨5, _⟩ => ts.Cp
  | ⟨6, _⟩ => ts.Cf
  | ⟨7, _⟩ => ts.Cs
  | ⟨8, _⟩ => ts.Cr
  | ⟨9, _⟩ => ts.Ca
  | ⟨10, _⟩ => ts.Cb
  | ⟨_ + 11, h⟩ => absurd h (by omega)

/-- 9 本まとめて。 -/
def TS (ts : Tapes sc) : Fin 11 → STape (Fin sc) := fun j => toS (getT ts j)

@[simp] theorem TS_focus (ts : Tapes sc) (j : Fin 11) :
    ((TS ts) j).focus = (getT ts j).focus := rfl

/-! ## 3. 動作列の write+move ベクトル列 -/

/-- `Act` が触れるテープ。 -/
def actTape : Act sc → Fin 11
  | .V1 _ => tV1
  | .V2 _ => tV2
  | .Cd _ _ => tCd
  | .Cq _ _ => tCq
  | .Ce _ _ => tCe
  | .Cp _ _ => tCp
  | .Cf _ _ => tCf
  | .Cs _ _ => tCs
  | .Cr _ _ => tCr
  | .Ca _ _ => tCa
  | .Cb _ _ => tCb

/-- `Act` が書き込む記号。 -/
def writeOf (ts : Tapes sc) : Act sc → Fin sc
  | .V1 _ => ts.V1.focus
  | .V2 _ => ts.V2.focus
  | .Cd a _ => a
  | .Cq a _ => a
  | .Ce a _ => a
  | .Cp a _ => a
  | .Cf a _ => a
  | .Cs a _ => a
  | .Cr a _ => a
  | .Ca a _ => a
  | .Cb a _ => a

/-- `Act` の移動。 -/
def moveOf : Act sc → Move
  | .V1 m => m
  | .V2 m => m
  | .Cd _ m => m
  | .Cq _ m => m
  | .Ce _ m => m
  | .Cp _ m => m
  | .Cf _ m => m
  | .Cs _ m => m
  | .Cr _ m => m
  | .Ca _ m => m
  | .Cb _ m => m

theorem getT_applyAct (blank : Fin sc) (ts : Tapes sc) (a : Act sc) (j : Fin 11) :
    getT (applyAct blank ts a) j
      = if j = actTape a then
          PalPeg.Tape.step blank (getT ts j) (writeOf ts a) (moveOf a)
        else getT ts j := by
  obtain ⟨v, hv⟩ := j
  cases a <;> interval_cases v <;>
    simp [applyAct, getT, actTape, writeOf, moveOf, tV1, tV2, tCd, tCq, tCe, tCp, tCf,
      tCs, tCr, tCa, tCb, Fin.ext_iff]

/-- `Act` に対応する 9 テープ分の write+move ベクトル。 -/
def avec (ts : Tapes sc) (a : Act sc) : Fin 11 → Fin sc × Move :=
  fun j => if j = actTape a then (writeOf ts a, moveOf a) else ((getT ts j).focus, Move.stay)

/-- 動作列に対応するベクトル列（各段の状態で評価する）。 -/
def avecs (blank : Fin sc) : List (Act sc) → Tapes sc → List (Fin 11 → Fin sc × Move)
  | [], _ => []
  | a :: l, ts => avec ts a :: avecs blank l (applyAct blank ts a)

@[simp] theorem avecs_nil (blank : Fin sc) (ts : Tapes sc) : avecs blank [] ts = [] := rfl

@[simp] theorem avecs_cons (blank : Fin sc) (a : Act sc) (l : List (Act sc)) (ts : Tapes sc) :
    avecs blank (a :: l) ts = avec ts a :: avecs blank l (applyAct blank ts a) := rfl

@[simp] theorem avecs_length (blank : Fin sc) :
    ∀ (l : List (Act sc)) (ts : Tapes sc), (avecs blank l ts).length = l.length := by
  intro l
  induction l with
  | nil => intro ts; rfl
  | cons a l ih => intro ts; simp [ih]

theorem avecs_append (blank : Fin sc) :
    ∀ (l₁ l₂ : List (Act sc)) (ts : Tapes sc),
      avecs blank (l₁ ++ l₂) ts
        = avecs blank l₁ ts ++ avecs blank l₂ (applyActs blank l₁ ts) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ ts; rfl
  | cons a l ih => intro l₂ ts; simp [ih]

theorem applyTrace_avec (blank : Fin sc) (ts : Tapes sc) (a : Act sc) :
    (fun j => ((TS ts) j).applyAction blank (avec ts a j)) = TS (applyAct blank ts a) := by
  funext j
  show (toS (getT ts j)).applyAction blank (avec ts a j) = toS (getT (applyAct blank ts a) j)
  rw [getT_applyAct]
  by_cases hj : j = actTape a
  · rw [if_pos hj, toS_step]
    simp only [avec, if_pos hj]
  · rw [if_neg hj]
    simp only [avec, if_neg hj]
    exact ProgLang.applyAction_focus_stay (blank := blank) (toS (getT ts j))

theorem applyTrace_avecs (blank : Fin sc) :
    ∀ (l : List (Act sc)) (ts : Tapes sc),
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

/-! ## 4. `Act` の動作列に対する `Exec` -/

section ExecA

variable (Terminal : Type)

/-- 「プログラム `P` は状態 `ts` からちょうど動作列 `L` を実行して継続に戻る」。 -/
def ExecA (blank endSym mark : Fin sc) (P : Prog A9 Cond9) (ts : Tapes sc)
    (L : List (Act sc)) : Prop :=
  Exec (I9 (Terminal := Terminal) blank endSym mark) blank P (TS ts) (avecs blank L ts)

variable {Terminal}
variable {blank endSym mark : Fin sc}

theorem execA_of_eq {P : Prog A9 Cond9} {ts : Tapes sc} {L L' : List (Act sc)}
    (h : L = L') (hE : ExecA Terminal blank endSym mark P ts L) :
    ExecA Terminal blank endSym mark P ts L' := h ▸ hE

theorem execA_seq {P Q : Prog A9 Cond9} {ts : Tapes sc} {L₁ L₂ : List (Act sc)}
    (h1 : ExecA Terminal blank endSym mark P ts L₁)
    (h2 : ExecA Terminal blank endSym mark Q (applyActs blank L₁ ts) L₂) :
    ExecA Terminal blank endSym mark (Prog.seq P Q) ts (L₁ ++ L₂) := by
  unfold ExecA at h1 h2 ⊢
  rw [avecs_append]
  refine exec_seq h1 ?_
  rw [applyTrace_avecs]
  exact h2

theorem execA_skip {ts : Tapes sc} :
    ExecA Terminal blank endSym mark Prog.skip ts [] := exec_skip _

/-! ### 基本動作 -/

/-- `Act` に対応する `A9` の動作識別子。 -/
def a9 (a : Act sc) : A9 :=
  (actTape a, (match a with
    | .V1 _ => W9.keep
    | .V2 _ => W9.keep
    | _ => W9.blk), moveOf a)

/-- `mark` を書く版（カウンタ復元用）。 -/
def a9m (j : Fin 11) (m : Move) : A9 := (j, W9.mrk, m)

theorem actVec_gen (a : Act sc) (w : W9) (ts : Tapes sc)
    (hw : (match w with
            | W9.keep => (getT ts (actTape a)).focus
            | W9.blk => blank
            | W9.mrk => mark) = writeOf ts a) :
    actVec (I9 (Terminal := Terminal) blank endSym mark) (actTape a, w, moveOf a) (TS ts)
      = avec ts a := by
  funext j
  by_cases hj : j = actTape a
  · subst hj
    simp only [actVec, I9, actOf9, touchVec, avec]
    rw [← hw]
    cases w <;> rfl
  · simp only [actVec, I9, actOf9, touchVec, avec, if_neg hj]
    rfl

theorem execA_act_gen (a : Act sc) (w : W9) (ts : Tapes sc)
    (hw : (match w with
            | W9.keep => (getT ts (actTape a)).focus
            | W9.blk => blank
            | W9.mrk => mark) = writeOf ts a) :
    ExecA Terminal blank endSym mark (Prog.act (actTape a, w, moveOf a)) ts [a] := by
  have h := exec_act (blank := blank) (inputFree_I9 (Terminal := Terminal) blank endSym mark)
    (actTape a, w, moveOf a) (TS ts)
  rw [actVec_gen (Terminal := Terminal) (blank := blank) (endSym := endSym) (mark := mark)
    a w ts hw] at h
  exact h

/-! ### 条件つき分岐 -/

theorem condOf_eq (c : Cond9) (ts : Tapes sc) :
    (I9 (Terminal := Terminal) blank endSym mark).condOf c (fun j => ((TS ts) j).focus)
      = condOf9 endSym mark c (fun j => (getT ts j).focus) := rfl

theorem execA_ite_pos {c : Cond9} {P Q : Prog A9 Cond9} {ts : Tapes sc} {L : List (Act sc)}
    (hc : condOf9 endSym mark c (fun j => (getT ts j).focus) = true)
    (h : ExecA Terminal blank endSym mark P ts L) :
    ExecA Terminal blank endSym mark (Prog.ite c P Q) ts L :=
  exec_ite_pos (by rw [condOf_eq]; exact hc) h

theorem execA_ite_neg {c : Cond9} {P Q : Prog A9 Cond9} {ts : Tapes sc} {L : List (Act sc)}
    (hc : condOf9 endSym mark c (fun j => (getT ts j).focus) = false)
    (h : ExecA Terminal blank endSym mark Q ts L) :
    ExecA Terminal blank endSym mark (Prog.ite c P Q) ts L :=
  exec_ite_neg (by rw [condOf_eq]; exact hc) h

theorem execA_loop_stop {c : Cond9} {a : A9} {b : Prog A9 Cond9} {ts : Tapes sc}
    (hc : condOf9 endSym mark c (fun j => (getT ts j).focus) = false) :
    ExecA Terminal blank endSym mark (Prog.loop c a b) ts [] :=
  exec_loop_stop (by rw [condOf_eq]; exact hc)

theorem execA_loop_cont {c : Cond9} {a : Act sc} {w : W9} {j : Fin 11} {mv : Move}
    {b : Prog A9 Cond9} {ts : Tapes sc} {L₁ L₂ : List (Act sc)}
    (hj : actTape a = j) (hmv : moveOf a = mv)
    (hw : (match w with
            | W9.keep => (getT ts (actTape a)).focus
            | W9.blk => blank
            | W9.mrk => mark) = writeOf ts a)
    (hc : condOf9 endSym mark c (fun j => (getT ts j).focus) = true)
    (h1 : ExecA Terminal blank endSym mark b (applyAct blank ts a) L₁)
    (h2 : ExecA Terminal blank endSym mark (Prog.loop c (j, w, mv) b)
      (applyActs blank L₁ (applyAct blank ts a)) L₂) :
    ExecA Terminal blank endSym mark (Prog.loop c (j, w, mv) b) ts
      (a :: (L₁ ++ L₂)) := by
  subst hj; subst hmv
  unfold ExecA at h1 h2 ⊢
  have hav : actVec (I9 (Terminal := Terminal) blank endSym mark)
      (actTape a, w, moveOf a) (TS ts) = avec ts a :=
    actVec_gen (Terminal := Terminal) (blank := blank) (endSym := endSym) (mark := mark)
      a w ts hw
  rw [avecs_cons, avecs_append, ← hav]
  have hT : (fun j => ((TS ts) j).applyAction blank
      (actVec (I9 (Terminal := Terminal) blank endSym mark) (actTape a, w, moveOf a)
        (TS ts) j)) = TS (applyAct blank ts a) := by
    rw [hav]
    exact applyTrace_avec blank ts a
  refine exec_loop_cont (inputFree_I9 (Terminal := Terminal) blank endSym mark)
    (by rw [condOf_eq]; exact hc) ?_ ?_
  · rw [hT]; exact h1
  · rw [hT, applyTrace_avecs]; exact h2

end ExecA

/-! ## 5. カウンタテープの抽象化 -/

/-- 「9 本のうちの 1 本のカウンタテープ」を表すデータ。すべてのフィールドは
具体的なテープに対して `rfl` で埋まる。 -/
structure CT (sc : ℕ) where
  /-- テープ番号。 -/
  idx : Fin 11
  /-- そのテープへの動作の作り方。 -/
  act : Fin sc → Move → Act sc
  /-- そのテープの取り出し。 -/
  get : Tapes sc → TapeConfiguration sc
  tape_eq : ∀ (a : Fin sc) (m : Move), actTape (act a m) = idx
  write_eq : ∀ (ts : Tapes sc) (a : Fin sc) (m : Move), writeOf ts (act a m) = a
  move_eq : ∀ (a : Fin sc) (m : Move), moveOf (act a m) = m
  get_eq : ∀ (ts : Tapes sc), getT ts idx = get ts
  step_eq : ∀ (blank : Fin sc) (ts : Tapes sc) (a : Fin sc) (m : Move),
    get (applyAct blank ts (act a m)) = PalPeg.Tape.step blank (get ts) a m

def ctCd : CT sc :=
  ⟨tCd, Act.Cd, Tapes.Cd, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl,
    fun _ => rfl, fun _ _ _ _ => rfl⟩
def ctCq : CT sc :=
  ⟨tCq, Act.Cq, Tapes.Cq, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl,
    fun _ => rfl, fun _ _ _ _ => rfl⟩
def ctCe : CT sc :=
  ⟨tCe, Act.Ce, Tapes.Ce, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl,
    fun _ => rfl, fun _ _ _ _ => rfl⟩
def ctCp : CT sc :=
  ⟨tCp, Act.Cp, Tapes.Cp, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl,
    fun _ => rfl, fun _ _ _ _ => rfl⟩
def ctCf : CT sc :=
  ⟨tCf, Act.Cf, Tapes.Cf, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl,
    fun _ => rfl, fun _ _ _ _ => rfl⟩
def ctCs : CT sc :=
  ⟨tCs, Act.Cs, Tapes.Cs, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl,
    fun _ => rfl, fun _ _ _ _ => rfl⟩
def ctCr : CT sc :=
  ⟨tCr, Act.Cr, Tapes.Cr, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl,
    fun _ => rfl, fun _ _ _ _ => rfl⟩
def ctCa : CT sc :=
  ⟨tCa, Act.Ca, Tapes.Ca, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl,
    fun _ => rfl, fun _ _ _ _ => rfl⟩
def ctCb : CT sc :=
  ⟨tCb, Act.Cb, Tapes.Cb, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl,
    fun _ => rfl, fun _ _ _ _ => rfl⟩

section CTLemmas

variable {Terminal : Type} {blank endSym mark : Fin sc}

theorem execA_ct_put (c : CT sc) (m : Move) (ts : Tapes sc) :
    ExecA Terminal blank endSym mark (Prog.act (c.idx, W9.blk, m)) ts [c.act blank m] := by
  have h := execA_act_gen (Terminal := Terminal) (blank := blank) (endSym := endSym)
    (mark := mark) (c.act blank m) W9.blk ts (by simpa using (c.write_eq ts blank m).symm)
  rw [c.tape_eq, c.move_eq] at h
  exact h

theorem execA_ct_mark (c : CT sc) (m : Move) (ts : Tapes sc) :
    ExecA Terminal blank endSym mark (Prog.act (c.idx, W9.mrk, m)) ts [c.act mark m] := by
  have h := execA_act_gen (Terminal := Terminal) (blank := blank) (endSym := endSym)
    (mark := mark) (c.act mark m) W9.mrk ts (by simpa using (c.write_eq ts mark m).symm)
  rw [c.tape_eq, c.move_eq] at h
  exact h

/-- 文字テープ `V1` の移動（読んだ記号を書き戻す）。 -/
theorem execA_v1 (m : Move) (ts : Tapes sc) :
    ExecA Terminal blank endSym mark (Prog.act (tV1, W9.keep, m)) ts [Act.V1 m] :=
  execA_act_gen (Act.V1 m) W9.keep ts rfl

/-- 文字テープ `V2` の移動（読んだ記号を書き戻す）。 -/
theorem execA_v2 (m : Move) (ts : Tapes sc) :
    ExecA Terminal blank endSym mark (Prog.act (tV2, W9.keep, m)) ts [Act.V2 m] :=
  execA_act_gen (Act.V2 m) W9.keep ts rfl

end CTLemmas

/-! ## 6. カウンタ駆動ループ

`GSPreprocessTapes` のカウンタ駆動ループはすべて

```
unit = [c blank .left, c blank .stay] ++ rest
```

という形（`rest` は状態に依存しない固定の動作列で、駆動テープ `c` には触れない）を
`n` 回繰り返したものである。有限制御では反復回数 `n` を持てないので、
**駆動カウンタがゼロになるまで回す** ループとして実現する。ゼロ判定には
probe（左へ動いて読む）が必要なので、末尾に probe と復元の 2 動作
`[c blank .left, c mark .right]` が余分に付く。 -/

section DrivenLoop

/-- 駆動ループ 1 単位の動作列。 -/
def dUnit (c : CT sc) (blank : Fin sc) (rest : List (Act sc)) : List (Act sc) :=
  (c.act blank Move.left :: c.act blank Move.stay :: rest)

/-- 駆動ループ本体の動作列（`n` 単位）。 -/
def dPow (c : CT sc) (blank : Fin sc) (rest : List (Act sc)) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 => dUnit c blank rest ++ dPow c blank rest n

/-- ゼロ判定の 2 動作（probe と復元）。 -/
def dTest (c : CT sc) (blank mark : Fin sc) : List (Act sc) :=
  [c.act blank Move.left, c.act mark Move.right]

@[simp] theorem dPow_length (c : CT sc) (blank : Fin sc) (rest : List (Act sc)) (n : ℕ) :
    (dPow c blank rest n).length = n * (rest.length + 2) := by
  induction n with
  | zero => simp [dPow]
  | succ n ih => simp only [dPow, List.length_append, ih, dUnit]; simp; ring

/-- 有限制御プログラム（テープ番号 `idx` のカウンタで駆動する）。
`sc` にも `blank` にも依存しない、正真正銘の有限制御である。 -/
def DLOOP (idx : Fin 11) (rest : Prog A9 Cond9) : Prog A9 Cond9 :=
  Prog.seq (Prog.act (idx, W9.blk, Move.left))
    (Prog.seq
      (Prog.loop (Cond9.notMark idx) (idx, W9.blk, Move.stay)
        (Prog.seq rest (Prog.act (idx, W9.blk, Move.left))))
      (Prog.act (idx, W9.mrk, Move.right)))

variable {Terminal : Type} {blank endSym mark : Fin sc}

/-- ループ本体（probe 済みの状態から）の実行。 -/
private def dInner (c : CT sc) (blank : Fin sc) (rest : List (Act sc)) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 => (c.act blank Move.stay :: (rest ++ [c.act blank Move.left]))
      ++ dInner c blank rest n

private theorem dInner_eq (c : CT sc) (blank mark : Fin sc) (rest : List (Act sc)) :
    ∀ n, c.act blank Move.left :: (dInner c blank rest n ++ [c.act mark Move.right])
      = dPow c blank rest n ++ dTest c blank mark := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      have h1 : dInner c blank rest (n + 1)
          = c.act blank Move.stay ::
            (rest ++ ([c.act blank Move.left] ++ dInner c blank rest n)) := by
        simp [dInner, List.append_assoc]
      have h2 : dPow c blank rest (n + 1)
          = c.act blank Move.left ::
            (c.act blank Move.stay :: (rest ++ dPow c blank rest n)) := by
        simp [dPow, dUnit]
      rw [h1, h2]
      simp only [List.cons_append, List.append_assoc]
      rw [← ih]
      simp

theorem dLoop_body_exec (c : CT sc) (rest : Prog A9 Cond9) (restL : List (Act sc))
    (hmark : mark ≠ blank)
    (hrest : ∀ ts : Tapes sc, ExecA Terminal blank endSym mark rest ts restL)
    (hrestget : ∀ ts : Tapes sc, c.get (applyActs blank restL ts) = c.get ts) :
    ∀ (n : ℕ) (ts : Tapes sc), PalPeg.Tape.CounterView' blank mark (c.get ts) n →
      ExecA Terminal blank endSym mark
        (Prog.loop (Cond9.notMark c.idx) (c.idx, W9.blk, Move.stay)
          (Prog.seq rest (Prog.act (c.idx, W9.blk, Move.left))))
        (applyAct blank ts (c.act blank Move.left)) (dInner c blank restL n) := by
  intro n
  induction n with
  | zero =>
      intro ts hcv
      refine execA_loop_stop ?_
      have hread : (getT (applyAct blank ts (c.act blank Move.left)) c.idx).focus = mark := by
        rw [c.get_eq, c.step_eq]
        exact (PalPeg.Tape.counter'_read_after_probe hcv).trans (by rw [if_pos rfl])
      simp only [condOf9, decide_eq_false_iff_not, not_not]
      exact hread
  | succ n ih =>
      intro ts hcv
      set ts0 := applyAct blank ts (c.act blank Move.left) with hts0
      have hread : (getT ts0 c.idx).focus = blank := by
        rw [hts0, c.get_eq, c.step_eq]
        exact (PalPeg.Tape.counter'_read_after_probe hcv).trans
          (by rw [if_neg (Nat.succ_ne_zero n)])
      have hcond : condOf9 endSym mark (Cond9.notMark c.idx)
          (fun j => (getT ts0 j).focus) = true := by
        simp only [condOf9, decide_eq_true_eq]
        rw [hread]
        exact Ne.symm hmark
      -- 消去動作
      set ts1 := applyAct blank ts0 (c.act blank Move.stay) with hts1
      have hcv1 : PalPeg.Tape.CounterView' blank mark (c.get ts1) n := by
        rw [hts1, c.step_eq, hts0, c.step_eq]
        exact PalPeg.Tape.counter'_dec hcv
      set ts2 := applyActs blank restL ts1 with hts2
      have hcv2 : PalPeg.Tape.CounterView' blank mark (c.get ts2) n := by
        rw [hts2, hrestget]; exact hcv1
      have hbody : ExecA Terminal blank endSym mark
          (Prog.seq rest (Prog.act (c.idx, W9.blk, Move.left))) ts1
          (restL ++ [c.act blank Move.left]) :=
        execA_seq (hrest ts1) (execA_ct_put c Move.left ts2)
      have htail := ih ts2 hcv2
      have hstate : applyActs blank (restL ++ [c.act blank Move.left]) ts1
          = applyAct blank ts2 (c.act blank Move.left) := by
        rw [applyActs_append]; rfl
      rw [← hstate] at htail
      have := execA_loop_cont (Terminal := Terminal) (c := Cond9.notMark c.idx)
        (a := c.act blank Move.stay) (w := W9.blk)
        (b := Prog.seq rest (Prog.act (c.idx, W9.blk, Move.left)))
        (ts := ts0) (c.tape_eq blank Move.stay) (c.move_eq blank Move.stay)
        (by simpa using (c.write_eq ts0 blank Move.stay).symm) hcond
        (by rw [← hts1]; exact hbody) (by rw [← hts1]; exact htail)
      exact this

/-- **駆動ループの主補題**。駆動カウンタ `c` の値が `n` のとき、
`DLOOP c rest` は `dPow c blank restL n ++ dTest c blank mark` を実行する。 -/
theorem dLoop_exec (c : CT sc) (rest : Prog A9 Cond9) (restL : List (Act sc))
    (hmark : mark ≠ blank)
    (hrest : ∀ ts : Tapes sc, ExecA Terminal blank endSym mark rest ts restL)
    (hrestget : ∀ ts : Tapes sc, c.get (applyActs blank restL ts) = c.get ts)
    (n : ℕ) (ts : Tapes sc) (hcv : PalPeg.Tape.CounterView' blank mark (c.get ts) n) :
    ExecA Terminal blank endSym mark (DLOOP c.idx rest) ts
      (dPow c blank restL n ++ dTest c blank mark) := by
  have h1 : ExecA Terminal blank endSym mark (Prog.act (c.idx, W9.blk, Move.left)) ts
      [c.act blank Move.left] := execA_ct_put c Move.left ts
  have h2 := dLoop_body_exec (Terminal := Terminal) c rest restL hmark hrest hrestget n ts hcv
  have h3 : ExecA Terminal blank endSym mark (Prog.act (c.idx, W9.mrk, Move.right))
      (applyActs blank (dInner c blank restL n)
        (applyAct blank ts (c.act blank Move.left))) [c.act mark Move.right] :=
    execA_ct_mark c Move.right _
  have hs : ExecA Terminal blank endSym mark (DLOOP c.idx rest) ts
      ([c.act blank Move.left] ++ (dInner c blank restL n ++ [c.act mark Move.right])) := by
    refine execA_seq h1 (execA_seq ?_ ?_)
    · show ExecA Terminal blank endSym mark _ (applyActs blank [c.act blank Move.left] ts) _
      exact h2
    · show ExecA Terminal blank endSym mark _
        (applyActs blank (dInner c blank restL n)
          (applyActs blank [c.act blank Move.left] ts)) _
      exact h3
  refine execA_of_eq ?_ hs
  exact dInner_eq c blank mark restL n

end DrivenLoop


/-! ## 7. 固定動作列のプログラム化 -/

section ProgOf

/-- `Act` に対応する書き込み種別（カウンタには常に `blank`）。 -/
def w9Of : Act sc → W9
  | .V1 _ => W9.keep
  | .V2 _ => W9.keep
  | _ => W9.blk

/-- `Act` に対応する `A9`。 -/
def a9Of (a : Act sc) : A9 := (actTape a, w9Of a, moveOf a)

/-- 固定動作列を素朴に並べたプログラム。 -/
def progOf : List (Act sc) → Prog A9 Cond9
  | [] => Prog.skip
  | a :: l => Prog.seq (Prog.act (a9Of a)) (progOf l)

/-- 動作 `a` が `w9Of a` の書き込みと整合する（カウンタなら `blank` を書く）。 -/
def OkAct (blank mark : Fin sc) (a : Act sc) : Prop :=
  ∀ ts : Tapes sc,
    (match w9Of a with
      | W9.keep => (getT ts (actTape a)).focus
      | W9.blk => blank
      | W9.mrk => mark) = writeOf ts a

variable {Terminal : Type} {blank endSym mark : Fin sc}

theorem execA_progOf : ∀ (L : List (Act sc)), (∀ a ∈ L, OkAct blank mark a) →
    ∀ ts : Tapes sc, ExecA Terminal blank endSym mark (progOf L) ts L := by
  intro L
  induction L with
  | nil => intro _ ts; exact execA_skip
  | cons a l ih =>
      intro h ts
      have h1 : ExecA Terminal blank endSym mark (Prog.act (a9Of a)) ts [a] :=
        execA_act_gen a (w9Of a) ts (h a (List.mem_cons_self ..) ts)
      have h2 := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
        (applyActs blank [a] ts)
      exact execA_seq h1 h2

end ProgOf

/-! ## 8. 各カウンタ駆動ループの実現 -/

section Instances

variable {Terminal : Type} {blank endSym mark : Fin sc}


/-! ### `qvLoop` -/

/-- `qvLoop` の 1 単位の残り動作。 -/
def qvRestL (_blank : Fin sc) : List (Act sc) := [Act.V1 Move.left, Act.V2 Move.left]

/-- `qvLoop` の 1 単位の残り部分のプログラム。 -/
def qvRest : Prog A9 Cond9 := Prog.seq (Prog.act (tV1, W9.keep, Move.left)) (Prog.seq (Prog.act (tV2, W9.keep, Move.left)) (Prog.skip))

/-- `qvLoop` の有限制御プログラム。 -/
def qvProg : Prog A9 Cond9 := DLOOP tCq qvRest

theorem qvRest_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark qvRest ts (qvRestL blank) := by
  have h : ∀ a ∈ qvRestL (sc := sc) blank, OkAct blank mark a := by
    intro a ha
    fin_cases ha 
    all_goals (intro ts; rfl)
  exact execA_progOf (qvRestL blank) h ts

theorem qvRest_get (ts : Tapes sc) :
    (ctCq : CT sc).get (applyActs blank (qvRestL blank) ts) = (ctCq : CT sc).get ts := rfl

theorem qv_dPow (n : ℕ) :
    dPow (ctCq : CT sc) blank (qvRestL blank) n = qvLoop blank n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dPow, ih]; rfl

/-- **`qvLoop` の実現**：駆動カウンタ `ctCq` の値が `n` のとき、
`qvProg` は `qvLoop blank n` に続けてゼロ判定の 2 動作を実行する。 -/
theorem qvProg_exec (hmark : mark ≠ blank) (n : ℕ) (ts : Tapes sc)
    (hcv : PalPeg.Tape.CounterView' blank mark ((ctCq : CT sc).get ts) n) :
    ExecA Terminal blank endSym mark qvProg ts
      (qvLoop blank n ++ dTest (ctCq : CT sc) blank mark) := by
  have h := dLoop_exec (Terminal := Terminal) (endSym := endSym) (ctCq : CT sc) qvRest (qvRestL blank)
    hmark (fun ts => qvRest_exec ts) (fun ts => qvRest_get ts) n ts hcv
  rw [qv_dPow] at h
  exact h

/-! ### `fzLoop` -/

/-- `fzLoop` の 1 単位の残り動作。 -/
def fzRestL (_blank : Fin sc) : List (Act sc) := []

/-- `fzLoop` の 1 単位の残り部分のプログラム。 -/
def fzRest : Prog A9 Cond9 := Prog.skip

/-- `fzLoop` の有限制御プログラム。 -/
def fzProg : Prog A9 Cond9 := DLOOP tCf fzRest

theorem fzRest_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark fzRest ts (fzRestL blank) := by
  have h : ∀ a ∈ fzRestL (sc := sc) blank, OkAct blank mark a := by
    intro a ha
    simp [fzRestL] at ha
  exact execA_progOf (fzRestL blank) h ts

theorem fzRest_get (ts : Tapes sc) :
    (ctCf : CT sc).get (applyActs blank (fzRestL blank) ts) = (ctCf : CT sc).get ts := rfl

theorem fz_dPow (n : ℕ) :
    dPow (ctCf : CT sc) blank (fzRestL blank) n = fzLoop blank n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dPow, ih]; rfl

/-- **`fzLoop` の実現**：駆動カウンタ `ctCf` の値が `n` のとき、
`fzProg` は `fzLoop blank n` に続けてゼロ判定の 2 動作を実行する。 -/
theorem fzProg_exec (hmark : mark ≠ blank) (n : ℕ) (ts : Tapes sc)
    (hcv : PalPeg.Tape.CounterView' blank mark ((ctCf : CT sc).get ts) n) :
    ExecA Terminal blank endSym mark fzProg ts
      (fzLoop blank n ++ dTest (ctCf : CT sc) blank mark) := by
  have h := dLoop_exec (Terminal := Terminal) (endSym := endSym) (ctCf : CT sc) fzRest (fzRestL blank)
    hmark (fun ts => fzRest_exec ts) (fun ts => fzRest_get ts) n ts hcv
  rw [fz_dPow] at h
  exact h

/-! ### `ezLoop` -/

/-- `ezLoop` の 1 単位の残り動作。 -/
def ezRestL (_blank : Fin sc) : List (Act sc) := []

/-- `ezLoop` の 1 単位の残り部分のプログラム。 -/
def ezRest : Prog A9 Cond9 := Prog.skip

/-- `ezLoop` の有限制御プログラム。 -/
def ezProg : Prog A9 Cond9 := DLOOP tCe ezRest

theorem ezRest_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark ezRest ts (ezRestL blank) := by
  have h : ∀ a ∈ ezRestL (sc := sc) blank, OkAct blank mark a := by
    intro a ha
    simp [ezRestL] at ha
  exact execA_progOf (ezRestL blank) h ts

theorem ezRest_get (ts : Tapes sc) :
    (ctCe : CT sc).get (applyActs blank (ezRestL blank) ts) = (ctCe : CT sc).get ts := rfl

theorem ez_dPow (n : ℕ) :
    dPow (ctCe : CT sc) blank (ezRestL blank) n = ezLoop blank n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dPow, ih]; rfl

/-- **`ezLoop` の実現**：駆動カウンタ `ctCe` の値が `n` のとき、
`ezProg` は `ezLoop blank n` に続けてゼロ判定の 2 動作を実行する。 -/
theorem ezProg_exec (hmark : mark ≠ blank) (n : ℕ) (ts : Tapes sc)
    (hcv : PalPeg.Tape.CounterView' blank mark ((ctCe : CT sc).get ts) n) :
    ExecA Terminal blank endSym mark ezProg ts
      (ezLoop blank n ++ dTest (ctCe : CT sc) blank mark) := by
  have h := dLoop_exec (Terminal := Terminal) (endSym := endSym) (ctCe : CT sc) ezRest (ezRestL blank)
    hmark (fun ts => ezRest_exec ts) (fun ts => ezRest_get ts) n ts hcv
  rw [ez_dPow] at h
  exact h

/-! ### `rzLoop` -/

/-- `rzLoop` の 1 単位の残り動作。 -/
def rzRestL (_blank : Fin sc) : List (Act sc) := []

/-- `rzLoop` の 1 単位の残り部分のプログラム。 -/
def rzRest : Prog A9 Cond9 := Prog.skip

/-- `rzLoop` の有限制御プログラム。 -/
def rzProg : Prog A9 Cond9 := DLOOP tCr rzRest

theorem rzRest_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark rzRest ts (rzRestL blank) := by
  have h : ∀ a ∈ rzRestL (sc := sc) blank, OkAct blank mark a := by
    intro a ha
    simp [rzRestL] at ha
  exact execA_progOf (rzRestL blank) h ts

theorem rzRest_get (ts : Tapes sc) :
    (ctCr : CT sc).get (applyActs blank (rzRestL blank) ts) = (ctCr : CT sc).get ts := rfl

theorem rz_dPow (n : ℕ) :
    dPow (ctCr : CT sc) blank (rzRestL blank) n = rzLoop blank n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dPow, ih]; rfl

/-- **`rzLoop` の実現**：駆動カウンタ `ctCr` の値が `n` のとき、
`rzProg` は `rzLoop blank n` に続けてゼロ判定の 2 動作を実行する。 -/
theorem rzProg_exec (hmark : mark ≠ blank) (n : ℕ) (ts : Tapes sc)
    (hcv : PalPeg.Tape.CounterView' blank mark ((ctCr : CT sc).get ts) n) :
    ExecA Terminal blank endSym mark rzProg ts
      (rzLoop blank n ++ dTest (ctCr : CT sc) blank mark) := by
  have h := dLoop_exec (Terminal := Terminal) (endSym := endSym) (ctCr : CT sc) rzRest (rzRestL blank)
    hmark (fun ts => rzRest_exec ts) (fun ts => rzRest_get ts) n ts hcv
  rw [rz_dPow] at h
  exact h

/-! ### `pzLoop` -/

/-- `pzLoop` の 1 単位の残り動作。 -/
def pzRestL (_blank : Fin sc) : List (Act sc) := []

/-- `pzLoop` の 1 単位の残り部分のプログラム。 -/
def pzRest : Prog A9 Cond9 := Prog.skip

/-- `pzLoop` の有限制御プログラム。 -/
def pzProg : Prog A9 Cond9 := DLOOP tCp pzRest

theorem pzRest_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark pzRest ts (pzRestL blank) := by
  have h : ∀ a ∈ pzRestL (sc := sc) blank, OkAct blank mark a := by
    intro a ha
    simp [pzRestL] at ha
  exact execA_progOf (pzRestL blank) h ts

theorem pzRest_get (ts : Tapes sc) :
    (ctCp : CT sc).get (applyActs blank (pzRestL blank) ts) = (ctCp : CT sc).get ts := rfl

theorem pz_dPow (n : ℕ) :
    dPow (ctCp : CT sc) blank (pzRestL blank) n = pzLoop blank n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dPow, ih]; rfl

/-- **`pzLoop` の実現**：駆動カウンタ `ctCp` の値が `n` のとき、
`pzProg` は `pzLoop blank n` に続けてゼロ判定の 2 動作を実行する。 -/
theorem pzProg_exec (hmark : mark ≠ blank) (n : ℕ) (ts : Tapes sc)
    (hcv : PalPeg.Tape.CounterView' blank mark ((ctCp : CT sc).get ts) n) :
    ExecA Terminal blank endSym mark pzProg ts
      (pzLoop blank n ++ dTest (ctCp : CT sc) blank mark) := by
  have h := dLoop_exec (Terminal := Terminal) (endSym := endSym) (ctCp : CT sc) pzRest (pzRestL blank)
    hmark (fun ts => pzRest_exec ts) (fun ts => pzRest_get ts) n ts hcv
  rw [pz_dPow] at h
  exact h

/-! ### `dzLoop` -/

/-- `dzLoop` の 1 単位の残り動作。 -/
def dzRestL (_blank : Fin sc) : List (Act sc) := []

/-- `dzLoop` の 1 単位の残り部分のプログラム。 -/
def dzRest : Prog A9 Cond9 := Prog.skip

/-- `dzLoop` の有限制御プログラム。 -/
def dzProg : Prog A9 Cond9 := DLOOP tCd dzRest

theorem dzRest_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark dzRest ts (dzRestL blank) := by
  have h : ∀ a ∈ dzRestL (sc := sc) blank, OkAct blank mark a := by
    intro a ha
    simp [dzRestL] at ha
  exact execA_progOf (dzRestL blank) h ts

theorem dzRest_get (ts : Tapes sc) :
    (ctCd : CT sc).get (applyActs blank (dzRestL blank) ts) = (ctCd : CT sc).get ts := rfl

theorem dz_dPow (n : ℕ) :
    dPow (ctCd : CT sc) blank (dzRestL blank) n = dzLoop blank n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dPow, ih]; rfl

/-- **`dzLoop` の実現**：駆動カウンタ `ctCd` の値が `n` のとき、
`dzProg` は `dzLoop blank n` に続けてゼロ判定の 2 動作を実行する。 -/
theorem dzProg_exec (hmark : mark ≠ blank) (n : ℕ) (ts : Tapes sc)
    (hcv : PalPeg.Tape.CounterView' blank mark ((ctCd : CT sc).get ts) n) :
    ExecA Terminal blank endSym mark dzProg ts
      (dzLoop blank n ++ dTest (ctCd : CT sc) blank mark) := by
  have h := dLoop_exec (Terminal := Terminal) (endSym := endSym) (ctCd : CT sc) dzRest (dzRestL blank)
    hmark (fun ts => dzRest_exec ts) (fun ts => dzRest_get ts) n ts hcv
  rw [dz_dPow] at h
  exact h

/-! ### `pfvLoop` -/

/-- `pfvLoop` の 1 単位の残り動作。 -/
def pfvRestL (blank : Fin sc) : List (Act sc) := [Act.Cf blank Move.right, Act.V2 Move.left]

/-- `pfvLoop` の 1 単位の残り部分のプログラム。 -/
def pfvRest : Prog A9 Cond9 := Prog.seq (Prog.act (tCf, W9.blk, Move.right)) (Prog.seq (Prog.act (tV2, W9.keep, Move.left)) (Prog.skip))

/-- `pfvLoop` の有限制御プログラム。 -/
def pfvProg : Prog A9 Cond9 := DLOOP tCp pfvRest

theorem pfvRest_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark pfvRest ts (pfvRestL blank) := by
  have h : ∀ a ∈ pfvRestL (sc := sc) blank, OkAct blank mark a := by
    intro a ha
    fin_cases ha 
    all_goals (intro ts; rfl)
  exact execA_progOf (pfvRestL blank) h ts

theorem pfvRest_get (ts : Tapes sc) :
    (ctCp : CT sc).get (applyActs blank (pfvRestL blank) ts) = (ctCp : CT sc).get ts := rfl

theorem pfv_dPow (n : ℕ) :
    dPow (ctCp : CT sc) blank (pfvRestL blank) n = pfvLoop blank n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dPow, ih]; rfl

/-- **`pfvLoop` の実現**：駆動カウンタ `ctCp` の値が `n` のとき、
`pfvProg` は `pfvLoop blank n` に続けてゼロ判定の 2 動作を実行する。 -/
theorem pfvProg_exec (hmark : mark ≠ blank) (n : ℕ) (ts : Tapes sc)
    (hcv : PalPeg.Tape.CounterView' blank mark ((ctCp : CT sc).get ts) n) :
    ExecA Terminal blank endSym mark pfvProg ts
      (pfvLoop blank n ++ dTest (ctCp : CT sc) blank mark) := by
  have h := dLoop_exec (Terminal := Terminal) (endSym := endSym) (ctCp : CT sc) pfvRest (pfvRestL blank)
    hmark (fun ts => pfvRest_exec ts) (fun ts => pfvRest_get ts) n ts hcv
  rw [pfv_dPow] at h
  exact h

/-! ### `fcLoop` -/

/-- `fcLoop` の 1 単位の残り動作。 -/
def fcRestL (blank : Fin sc) : List (Act sc) := [Act.Cp blank Move.right]

/-- `fcLoop` の 1 単位の残り部分のプログラム。 -/
def fcRest : Prog A9 Cond9 := Prog.seq (Prog.act (tCp, W9.blk, Move.right)) (Prog.skip)

/-- `fcLoop` の有限制御プログラム。 -/
def fcProg : Prog A9 Cond9 := DLOOP tCf fcRest

theorem fcRest_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark fcRest ts (fcRestL blank) := by
  have h : ∀ a ∈ fcRestL (sc := sc) blank, OkAct blank mark a := by
    intro a ha
    fin_cases ha 
    all_goals (intro ts; rfl)
  exact execA_progOf (fcRestL blank) h ts

theorem fcRest_get (ts : Tapes sc) :
    (ctCf : CT sc).get (applyActs blank (fcRestL blank) ts) = (ctCf : CT sc).get ts := rfl

theorem fc_dPow (n : ℕ) :
    dPow (ctCf : CT sc) blank (fcRestL blank) n = fcLoop blank n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dPow, ih]; rfl

/-- **`fcLoop` の実現**：駆動カウンタ `ctCf` の値が `n` のとき、
`fcProg` は `fcLoop blank n` に続けてゼロ判定の 2 動作を実行する。 -/
theorem fcProg_exec (hmark : mark ≠ blank) (n : ℕ) (ts : Tapes sc)
    (hcv : PalPeg.Tape.CounterView' blank mark ((ctCf : CT sc).get ts) n) :
    ExecA Terminal blank endSym mark fcProg ts
      (fcLoop blank n ++ dTest (ctCf : CT sc) blank mark) := by
  have h := dLoop_exec (Terminal := Terminal) (endSym := endSym) (ctCf : CT sc) fcRest (fcRestL blank)
    hmark (fun ts => fcRest_exec ts) (fun ts => fcRest_get ts) n ts hcv
  rw [fc_dPow] at h
  exact h

/-! ### `qrLoop` -/

/-- `qrLoop` の 1 単位の残り動作。 -/
def qrRestL (blank : Fin sc) : List (Act sc) := [Act.Cr blank Move.right]

/-- `qrLoop` の 1 単位の残り部分のプログラム。 -/
def qrRest : Prog A9 Cond9 := Prog.seq (Prog.act (tCr, W9.blk, Move.right)) (Prog.skip)

/-- `qrLoop` の有限制御プログラム。 -/
def qrProg : Prog A9 Cond9 := DLOOP tCq qrRest

theorem qrRest_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark qrRest ts (qrRestL blank) := by
  have h : ∀ a ∈ qrRestL (sc := sc) blank, OkAct blank mark a := by
    intro a ha
    fin_cases ha 
    all_goals (intro ts; rfl)
  exact execA_progOf (qrRestL blank) h ts

theorem qrRest_get (ts : Tapes sc) :
    (ctCq : CT sc).get (applyActs blank (qrRestL blank) ts) = (ctCq : CT sc).get ts := rfl

theorem qr_dPow (n : ℕ) :
    dPow (ctCq : CT sc) blank (qrRestL blank) n = qrLoop blank n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dPow, ih]; rfl

/-- **`qrLoop` の実現**：駆動カウンタ `ctCq` の値が `n` のとき、
`qrProg` は `qrLoop blank n` に続けてゼロ判定の 2 動作を実行する。 -/
theorem qrProg_exec (hmark : mark ≠ blank) (n : ℕ) (ts : Tapes sc)
    (hcv : PalPeg.Tape.CounterView' blank mark ((ctCq : CT sc).get ts) n) :
    ExecA Terminal blank endSym mark qrProg ts
      (qrLoop blank n ++ dTest (ctCq : CT sc) blank mark) := by
  have h := dLoop_exec (Terminal := Terminal) (endSym := endSym) (ctCq : CT sc) qrRest (qrRestL blank)
    hmark (fun ts => qrRest_exec ts) (fun ts => qrRest_get ts) n ts hcv
  rw [qr_dPow] at h
  exact h

/-! ### `pcLoop` -/

/-- `pcLoop` の 1 単位の残り動作。 -/
def pcRestL (blank : Fin sc) : List (Act sc) := [Act.Cr blank Move.right, Act.Ce blank Move.right]

/-- `pcLoop` の 1 単位の残り部分のプログラム。 -/
def pcRest : Prog A9 Cond9 := Prog.seq (Prog.act (tCr, W9.blk, Move.right)) (Prog.seq (Prog.act (tCe, W9.blk, Move.right)) (Prog.skip))

/-- `pcLoop` の有限制御プログラム。 -/
def pcProg : Prog A9 Cond9 := DLOOP tCp pcRest

theorem pcRest_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark pcRest ts (pcRestL blank) := by
  have h : ∀ a ∈ pcRestL (sc := sc) blank, OkAct blank mark a := by
    intro a ha
    fin_cases ha 
    all_goals (intro ts; rfl)
  exact execA_progOf (pcRestL blank) h ts

theorem pcRest_get (ts : Tapes sc) :
    (ctCp : CT sc).get (applyActs blank (pcRestL blank) ts) = (ctCp : CT sc).get ts := rfl

theorem pc_dPow (n : ℕ) :
    dPow (ctCp : CT sc) blank (pcRestL blank) n = pcLoop blank n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dPow, ih]; rfl

/-- **`pcLoop` の実現**：駆動カウンタ `ctCp` の値が `n` のとき、
`pcProg` は `pcLoop blank n` に続けてゼロ判定の 2 動作を実行する。 -/
theorem pcProg_exec (hmark : mark ≠ blank) (n : ℕ) (ts : Tapes sc)
    (hcv : PalPeg.Tape.CounterView' blank mark ((ctCp : CT sc).get ts) n) :
    ExecA Terminal blank endSym mark pcProg ts
      (pcLoop blank n ++ dTest (ctCp : CT sc) blank mark) := by
  have h := dLoop_exec (Terminal := Terminal) (endSym := endSym) (ctCp : CT sc) pcRest (pcRestL blank)
    hmark (fun ts => pcRest_exec ts) (fun ts => pcRest_get ts) n ts hcv
  rw [pc_dPow] at h
  exact h

/-! ### `cpLoop` -/

/-- `cpLoop` の 1 単位の残り動作。 -/
def cpRestL (blank : Fin sc) : List (Act sc) := [Act.Cp blank Move.right]

/-- `cpLoop` の 1 単位の残り部分のプログラム。 -/
def cpRest : Prog A9 Cond9 := Prog.seq (Prog.act (tCp, W9.blk, Move.right)) (Prog.skip)

/-- `cpLoop` の有限制御プログラム。 -/
def cpProg : Prog A9 Cond9 := DLOOP tCe cpRest

theorem cpRest_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark cpRest ts (cpRestL blank) := by
  have h : ∀ a ∈ cpRestL (sc := sc) blank, OkAct blank mark a := by
    intro a ha
    fin_cases ha 
    all_goals (intro ts; rfl)
  exact execA_progOf (cpRestL blank) h ts

theorem cpRest_get (ts : Tapes sc) :
    (ctCe : CT sc).get (applyActs blank (cpRestL blank) ts) = (ctCe : CT sc).get ts := rfl

theorem cp_dPow (n : ℕ) :
    dPow (ctCe : CT sc) blank (cpRestL blank) n = cpLoop blank n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dPow, ih]; rfl

/-- **`cpLoop` の実現**：駆動カウンタ `ctCe` の値が `n` のとき、
`cpProg` は `cpLoop blank n` に続けてゼロ判定の 2 動作を実行する。 -/
theorem cpProg_exec (hmark : mark ≠ blank) (n : ℕ) (ts : Tapes sc)
    (hcv : PalPeg.Tape.CounterView' blank mark ((ctCe : CT sc).get ts) n) :
    ExecA Terminal blank endSym mark cpProg ts
      (cpLoop blank n ++ dTest (ctCe : CT sc) blank mark) := by
  have h := dLoop_exec (Terminal := Terminal) (endSym := endSym) (ctCe : CT sc) cpRest (cpRestL blank)
    hmark (fun ts => cpRest_exec ts) (fun ts => cpRest_get ts) n ts hcv
  rw [cp_dPow] at h
  exact h

/-! ### `cfLoop` -/

/-- `cfLoop` の 1 単位の残り動作。 -/
def cfRestL (blank : Fin sc) : List (Act sc) := [Act.Cf blank Move.right]

/-- `cfLoop` の 1 単位の残り部分のプログラム。 -/
def cfRest : Prog A9 Cond9 := Prog.seq (Prog.act (tCf, W9.blk, Move.right)) (Prog.skip)

/-- `cfLoop` の有限制御プログラム。 -/
def cfProg : Prog A9 Cond9 := DLOOP tCe cfRest

theorem cfRest_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark cfRest ts (cfRestL blank) := by
  have h : ∀ a ∈ cfRestL (sc := sc) blank, OkAct blank mark a := by
    intro a ha
    fin_cases ha 
    all_goals (intro ts; rfl)
  exact execA_progOf (cfRestL blank) h ts

theorem cfRest_get (ts : Tapes sc) :
    (ctCe : CT sc).get (applyActs blank (cfRestL blank) ts) = (ctCe : CT sc).get ts := rfl

theorem cf_dPow (n : ℕ) :
    dPow (ctCe : CT sc) blank (cfRestL blank) n = cfLoop blank n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dPow, ih]; rfl

/-- **`cfLoop` の実現**：駆動カウンタ `ctCe` の値が `n` のとき、
`cfProg` は `cfLoop blank n` に続けてゼロ判定の 2 動作を実行する。 -/
theorem cfProg_exec (hmark : mark ≠ blank) (n : ℕ) (ts : Tapes sc)
    (hcv : PalPeg.Tape.CounterView' blank mark ((ctCe : CT sc).get ts) n) :
    ExecA Terminal blank endSym mark cfProg ts
      (cfLoop blank n ++ dTest (ctCe : CT sc) blank mark) := by
  have h := dLoop_exec (Terminal := Terminal) (endSym := endSym) (ctCe : CT sc) cfRest (cfRestL blank)
    hmark (fun ts => cfRest_exec ts) (fun ts => cfRest_get ts) n ts hcv
  rw [cf_dPow] at h
  exact h

/-! ### `pfLoop` -/

/-- `pfLoop` の 1 単位の残り動作。 -/
def pfRestL (blank : Fin sc) : List (Act sc) := [Act.Cf blank Move.right, Act.Ce blank Move.right]

/-- `pfLoop` の 1 単位の残り部分のプログラム。 -/
def pfRest : Prog A9 Cond9 := Prog.seq (Prog.act (tCf, W9.blk, Move.right)) (Prog.seq (Prog.act (tCe, W9.blk, Move.right)) (Prog.skip))

/-- `pfLoop` の有限制御プログラム。 -/
def pfProg : Prog A9 Cond9 := DLOOP tCp pfRest

theorem pfRest_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark pfRest ts (pfRestL blank) := by
  have h : ∀ a ∈ pfRestL (sc := sc) blank, OkAct blank mark a := by
    intro a ha
    fin_cases ha 
    all_goals (intro ts; rfl)
  exact execA_progOf (pfRestL blank) h ts

theorem pfRest_get (ts : Tapes sc) :
    (ctCp : CT sc).get (applyActs blank (pfRestL blank) ts) = (ctCp : CT sc).get ts := rfl

theorem pf_dPow (n : ℕ) :
    dPow (ctCp : CT sc) blank (pfRestL blank) n = pfLoop blank n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dPow, ih]; rfl

/-- **`pfLoop` の実現**：駆動カウンタ `ctCp` の値が `n` のとき、
`pfProg` は `pfLoop blank n` に続けてゼロ判定の 2 動作を実行する。 -/
theorem pfProg_exec (hmark : mark ≠ blank) (n : ℕ) (ts : Tapes sc)
    (hcv : PalPeg.Tape.CounterView' blank mark ((ctCp : CT sc).get ts) n) :
    ExecA Terminal blank endSym mark pfProg ts
      (pfLoop blank n ++ dTest (ctCp : CT sc) blank mark) := by
  have h := dLoop_exec (Terminal := Terminal) (endSym := endSym) (ctCp : CT sc) pfRest (pfRestL blank)
    hmark (fun ts => pfRest_exec ts) (fun ts => pfRest_get ts) n ts hcv
  rw [pf_dPow] at h
  exact h

/-! ### `prLoop` -/

/-- `prLoop` の 1 単位の残り動作。 -/
def prRestL (blank : Fin sc) : List (Act sc) := [Act.Cr blank Move.left, Act.Cr blank Move.stay, Act.Ce blank Move.right]

/-- `prLoop` の 1 単位の残り部分のプログラム。 -/
def prRest : Prog A9 Cond9 := Prog.seq (Prog.act (tCr, W9.blk, Move.left)) (Prog.seq (Prog.act (tCr, W9.blk, Move.stay)) (Prog.seq (Prog.act (tCe, W9.blk, Move.right)) (Prog.skip)))

/-- `prLoop` の有限制御プログラム。 -/
def prProg : Prog A9 Cond9 := DLOOP tCp prRest

theorem prRest_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark prRest ts (prRestL blank) := by
  have h : ∀ a ∈ prRestL (sc := sc) blank, OkAct blank mark a := by
    intro a ha
    fin_cases ha 
    all_goals (intro ts; rfl)
  exact execA_progOf (prRestL blank) h ts

theorem prRest_get (ts : Tapes sc) :
    (ctCp : CT sc).get (applyActs blank (prRestL blank) ts) = (ctCp : CT sc).get ts := rfl

theorem pr_dPow (n : ℕ) :
    dPow (ctCp : CT sc) blank (prRestL blank) n = prLoop blank n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dPow, ih]; rfl

/-- **`prLoop` の実現**：駆動カウンタ `ctCp` の値が `n` のとき、
`prProg` は `prLoop blank n` に続けてゼロ判定の 2 動作を実行する。 -/
theorem prProg_exec (hmark : mark ≠ blank) (n : ℕ) (ts : Tapes sc)
    (hcv : PalPeg.Tape.CounterView' blank mark ((ctCp : CT sc).get ts) n) :
    ExecA Terminal blank endSym mark prProg ts
      (prLoop blank n ++ dTest (ctCp : CT sc) blank mark) := by
  have h := dLoop_exec (Terminal := Terminal) (endSym := endSym) (ctCp : CT sc) prRest (prRestL blank)
    hmark (fun ts => prRest_exec ts) (fun ts => prRest_get ts) n ts hcv
  rw [pr_dPow] at h
  exact h

/-! ### `rvLoop` -/

/-- `rvLoop` の 1 単位の残り動作。 -/
def rvRestL (blank : Fin sc) : List (Act sc) := [Act.V1 Move.left, Act.V2 Move.left, Act.Ce blank Move.right]

/-- `rvLoop` の 1 単位の残り部分のプログラム。 -/
def rvRest : Prog A9 Cond9 := Prog.seq (Prog.act (tV1, W9.keep, Move.left)) (Prog.seq (Prog.act (tV2, W9.keep, Move.left)) (Prog.seq (Prog.act (tCe, W9.blk, Move.right)) (Prog.skip)))

/-- `rvLoop` の有限制御プログラム。 -/
def rvProg : Prog A9 Cond9 := DLOOP tCr rvRest

theorem rvRest_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark rvRest ts (rvRestL blank) := by
  have h : ∀ a ∈ rvRestL (sc := sc) blank, OkAct blank mark a := by
    intro a ha
    fin_cases ha 
    all_goals (intro ts; rfl)
  exact execA_progOf (rvRestL blank) h ts

theorem rvRest_get (ts : Tapes sc) :
    (ctCr : CT sc).get (applyActs blank (rvRestL blank) ts) = (ctCr : CT sc).get ts := rfl

theorem rv_dPow (n : ℕ) :
    dPow (ctCr : CT sc) blank (rvRestL blank) n = rvLoop blank n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dPow, ih]; rfl

/-- **`rvLoop` の実現**：駆動カウンタ `ctCr` の値が `n` のとき、
`rvProg` は `rvLoop blank n` に続けてゼロ判定の 2 動作を実行する。 -/
theorem rvProg_exec (hmark : mark ≠ blank) (n : ℕ) (ts : Tapes sc)
    (hcv : PalPeg.Tape.CounterView' blank mark ((ctCr : CT sc).get ts) n) :
    ExecA Terminal blank endSym mark rvProg ts
      (rvLoop blank n ++ dTest (ctCr : CT sc) blank mark) := by
  have h := dLoop_exec (Terminal := Terminal) (endSym := endSym) (ctCr : CT sc) rvRest (rvRestL blank)
    hmark (fun ts => rvRest_exec ts) (fun ts => rvRest_get ts) n ts hcv
  rw [rv_dPow] at h
  exact h

/-! ### `crLoop` -/

/-- `crLoop` の 1 単位の残り動作。 -/
def crRestL (blank : Fin sc) : List (Act sc) := [Act.Cr blank Move.right]

/-- `crLoop` の 1 単位の残り部分のプログラム。 -/
def crRest : Prog A9 Cond9 := Prog.seq (Prog.act (tCr, W9.blk, Move.right)) (Prog.skip)

/-- `crLoop` の有限制御プログラム。 -/
def crProg : Prog A9 Cond9 := DLOOP tCe crRest

theorem crRest_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark crRest ts (crRestL blank) := by
  have h : ∀ a ∈ crRestL (sc := sc) blank, OkAct blank mark a := by
    intro a ha
    fin_cases ha 
    all_goals (intro ts; rfl)
  exact execA_progOf (crRestL blank) h ts

theorem crRest_get (ts : Tapes sc) :
    (ctCe : CT sc).get (applyActs blank (crRestL blank) ts) = (ctCe : CT sc).get ts := rfl

theorem cr_dPow (n : ℕ) :
    dPow (ctCe : CT sc) blank (crRestL blank) n = crLoop blank n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dPow, ih]; rfl

/-- **`crLoop` の実現**：駆動カウンタ `ctCe` の値が `n` のとき、
`crProg` は `crLoop blank n` に続けてゼロ判定の 2 動作を実行する。 -/
theorem crProg_exec (hmark : mark ≠ blank) (n : ℕ) (ts : Tapes sc)
    (hcv : PalPeg.Tape.CounterView' blank mark ((ctCe : CT sc).get ts) n) :
    ExecA Terminal blank endSym mark crProg ts
      (crLoop blank n ++ dTest (ctCe : CT sc) blank mark) := by
  have h := dLoop_exec (Terminal := Terminal) (endSym := endSym) (ctCe : CT sc) crRest (crRestL blank)
    hmark (fun ts => crRest_exec ts) (fun ts => crRest_get ts) n ts hcv
  rw [cr_dPow] at h
  exact h

/-! ### `pvLoop` -/

/-- `pvLoop` の 1 単位の残り動作。 -/
def pvRestL (_blank : Fin sc) : List (Act sc) := [Act.V2 Move.left]

/-- `pvLoop` の 1 単位の残り部分のプログラム。 -/
def pvRest : Prog A9 Cond9 := Prog.seq (Prog.act (tV2, W9.keep, Move.left)) (Prog.skip)

/-- `pvLoop` の有限制御プログラム。 -/
def pvProg : Prog A9 Cond9 := DLOOP tCp pvRest

theorem pvRest_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark pvRest ts (pvRestL blank) := by
  have h : ∀ a ∈ pvRestL (sc := sc) blank, OkAct blank mark a := by
    intro a ha
    fin_cases ha 
    all_goals (intro ts; rfl)
  exact execA_progOf (pvRestL blank) h ts

theorem pvRest_get (ts : Tapes sc) :
    (ctCp : CT sc).get (applyActs blank (pvRestL blank) ts) = (ctCp : CT sc).get ts := rfl

theorem pv_dPow (n : ℕ) :
    dPow (ctCp : CT sc) blank (pvRestL blank) n = pvLoop blank n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dPow, ih]; rfl

/-- **`pvLoop` の実現**：駆動カウンタ `ctCp` の値が `n` のとき、
`pvProg` は `pvLoop blank n` に続けてゼロ判定の 2 動作を実行する。 -/
theorem pvProg_exec (hmark : mark ≠ blank) (n : ℕ) (ts : Tapes sc)
    (hcv : PalPeg.Tape.CounterView' blank mark ((ctCp : CT sc).get ts) n) :
    ExecA Terminal blank endSym mark pvProg ts
      (pvLoop blank n ++ dTest (ctCp : CT sc) blank mark) := by
  have h := dLoop_exec (Terminal := Terminal) (endSym := endSym) (ctCp : CT sc) pvRest (pvRestL blank)
    hmark (fun ts => pvRest_exec ts) (fun ts => pvRest_get ts) n ts hcv
  rw [pv_dPow] at h
  exact h

/-! ### `rv2Loop` -/

/-- `rv2Loop` の 1 単位の残り動作。 -/
def rv2RestL (blank : Fin sc) : List (Act sc) := [Act.V2 Move.left, Act.Ce blank Move.right]

/-- `rv2Loop` の 1 単位の残り部分のプログラム。 -/
def rv2Rest : Prog A9 Cond9 := Prog.seq (Prog.act (tV2, W9.keep, Move.left)) (Prog.seq (Prog.act (tCe, W9.blk, Move.right)) (Prog.skip))

/-- `rv2Loop` の有限制御プログラム。 -/
def rv2Prog : Prog A9 Cond9 := DLOOP tCr rv2Rest

theorem rv2Rest_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark rv2Rest ts (rv2RestL blank) := by
  have h : ∀ a ∈ rv2RestL (sc := sc) blank, OkAct blank mark a := by
    intro a ha
    fin_cases ha 
    all_goals (intro ts; rfl)
  exact execA_progOf (rv2RestL blank) h ts

theorem rv2Rest_get (ts : Tapes sc) :
    (ctCr : CT sc).get (applyActs blank (rv2RestL blank) ts) = (ctCr : CT sc).get ts := rfl

theorem rv2_dPow (n : ℕ) :
    dPow (ctCr : CT sc) blank (rv2RestL blank) n = rv2Loop blank n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dPow, ih]; rfl

/-- **`rv2Loop` の実現**：駆動カウンタ `ctCr` の値が `n` のとき、
`rv2Prog` は `rv2Loop blank n` に続けてゼロ判定の 2 動作を実行する。 -/
theorem rv2Prog_exec (hmark : mark ≠ blank) (n : ℕ) (ts : Tapes sc)
    (hcv : PalPeg.Tape.CounterView' blank mark ((ctCr : CT sc).get ts) n) :
    ExecA Terminal blank endSym mark rv2Prog ts
      (rv2Loop blank n ++ dTest (ctCr : CT sc) blank mark) := by
  have h := dLoop_exec (Terminal := Terminal) (endSym := endSym) (ctCr : CT sc) rv2Rest (rv2RestL blank)
    hmark (fun ts => rv2Rest_exec ts) (fun ts => rv2Rest_get ts) n ts hcv
  rw [rv2_dPow] at h
  exact h

/-! ### `ecLoop` -/

/-- `ecLoop` の 1 単位の残り動作。 -/
def ecRestL (blank : Fin sc) : List (Act sc) := [Act.Ce blank Move.left, Act.Ce blank Move.stay, Act.Cq blank Move.right]

/-- `ecLoop` の 1 単位の残り部分のプログラム。 -/
def ecRest : Prog A9 Cond9 := Prog.seq (Prog.act (tCe, W9.blk, Move.left)) (Prog.seq (Prog.act (tCe, W9.blk, Move.stay)) (Prog.seq (Prog.act (tCq, W9.blk, Move.right)) (Prog.skip)))

/-- `ecLoop` の有限制御プログラム。 -/
def ecProg : Prog A9 Cond9 := DLOOP tCp ecRest

theorem ecRest_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark ecRest ts (ecRestL blank) := by
  have h : ∀ a ∈ ecRestL (sc := sc) blank, OkAct blank mark a := by
    intro a ha
    fin_cases ha 
    all_goals (intro ts; rfl)
  exact execA_progOf (ecRestL blank) h ts

theorem ecRest_get (ts : Tapes sc) :
    (ctCp : CT sc).get (applyActs blank (ecRestL blank) ts) = (ctCp : CT sc).get ts := rfl

theorem ec_dPow (n : ℕ) :
    dPow (ctCp : CT sc) blank (ecRestL blank) n = ecLoop blank n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dPow, ih]; rfl

/-- **`ecLoop` の実現**：駆動カウンタ `ctCp` の値が `n` のとき、
`ecProg` は `ecLoop blank n` に続けてゼロ判定の 2 動作を実行する。 -/
theorem ecProg_exec (hmark : mark ≠ blank) (n : ℕ) (ts : Tapes sc)
    (hcv : PalPeg.Tape.CounterView' blank mark ((ctCp : CT sc).get ts) n) :
    ExecA Terminal blank endSym mark ecProg ts
      (ecLoop blank n ++ dTest (ctCp : CT sc) blank mark) := by
  have h := dLoop_exec (Terminal := Terminal) (endSym := endSym) (ctCp : CT sc) ecRest (ecRestL blank)
    hmark (fun ts => ecRest_exec ts) (fun ts => ecRest_get ts) n ts hcv
  rw [ec_dPow] at h
  exact h

/-! ### `qpLoop` -/

/-- `qpLoop` の 1 単位の残り動作。 -/
def qpRestL (blank : Fin sc) : List (Act sc) := [Act.Cp blank Move.right]

/-- `qpLoop` の 1 単位の残り部分のプログラム。 -/
def qpRest : Prog A9 Cond9 := Prog.seq (Prog.act (tCp, W9.blk, Move.right)) (Prog.skip)

/-- `qpLoop` の有限制御プログラム。 -/
def qpProg : Prog A9 Cond9 := DLOOP tCq qpRest

theorem qpRest_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark qpRest ts (qpRestL blank) := by
  have h : ∀ a ∈ qpRestL (sc := sc) blank, OkAct blank mark a := by
    intro a ha
    fin_cases ha 
    all_goals (intro ts; rfl)
  exact execA_progOf (qpRestL blank) h ts

theorem qpRest_get (ts : Tapes sc) :
    (ctCq : CT sc).get (applyActs blank (qpRestL blank) ts) = (ctCq : CT sc).get ts := rfl

theorem qp_dPow (n : ℕ) :
    dPow (ctCq : CT sc) blank (qpRestL blank) n = qpLoop blank n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dPow, ih]; rfl

/-- **`qpLoop` の実現**：駆動カウンタ `ctCq` の値が `n` のとき、
`qpProg` は `qpLoop blank n` に続けてゼロ判定の 2 動作を実行する。 -/
theorem qpProg_exec (hmark : mark ≠ blank) (n : ℕ) (ts : Tapes sc)
    (hcv : PalPeg.Tape.CounterView' blank mark ((ctCq : CT sc).get ts) n) :
    ExecA Terminal blank endSym mark qpProg ts
      (qpLoop blank n ++ dTest (ctCq : CT sc) blank mark) := by
  have h := dLoop_exec (Terminal := Terminal) (endSym := endSym) (ctCq : CT sc) qpRest (qpRestL blank)
    hmark (fun ts => qpRest_exec ts) (fun ts => qpRest_get ts) n ts hcv
  rw [qp_dPow] at h
  exact h

/-! ### `csLoop` -/

/-- `csLoop` の 1 単位の残り動作。 -/
def csRestL (blank : Fin sc) : List (Act sc) := [Act.Cs blank Move.right, Act.V1 Move.right, Act.V2 Move.right]

/-- `csLoop` の 1 単位の残り部分のプログラム。 -/
def csRest : Prog A9 Cond9 := Prog.seq (Prog.act (tCs, W9.blk, Move.right)) (Prog.seq (Prog.act (tV1, W9.keep, Move.right)) (Prog.seq (Prog.act (tV2, W9.keep, Move.right)) (Prog.skip)))

/-- `csLoop` の有限制御プログラム。 -/
def csProg : Prog A9 Cond9 := DLOOP tCe csRest

theorem csRest_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark csRest ts (csRestL blank) := by
  have h : ∀ a ∈ csRestL (sc := sc) blank, OkAct blank mark a := by
    intro a ha
    fin_cases ha 
    all_goals (intro ts; rfl)
  exact execA_progOf (csRestL blank) h ts

theorem csRest_get (ts : Tapes sc) :
    (ctCe : CT sc).get (applyActs blank (csRestL blank) ts) = (ctCe : CT sc).get ts := rfl

theorem cs_dPow (n : ℕ) :
    dPow (ctCe : CT sc) blank (csRestL blank) n = csLoop blank n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dPow, ih]; rfl

/-- **`csLoop` の実現**：駆動カウンタ `ctCe` の値が `n` のとき、
`csProg` は `csLoop blank n` に続けてゼロ判定の 2 動作を実行する。 -/
theorem csProg_exec (hmark : mark ≠ blank) (n : ℕ) (ts : Tapes sc)
    (hcv : PalPeg.Tape.CounterView' blank mark ((ctCe : CT sc).get ts) n) :
    ExecA Terminal blank endSym mark csProg ts
      (csLoop blank n ++ dTest (ctCe : CT sc) blank mark) := by
  have h := dLoop_exec (Terminal := Terminal) (endSym := endSym) (ctCe : CT sc) csRest (csRestL blank)
    hmark (fun ts => csRest_exec ts) (fun ts => csRest_get ts) n ts hcv
  rw [cs_dPow] at h
  exact h

end Instances

/-! ## 9. ゼロ判定 2 動作の `Enc` 保存 -/

section DTestEnc

variable {blank startSym endSym mark : Fin sc} {x : List (Fin sc)} {a b : ℕ} {ts : Tapes sc}

theorem dTest_enc_Cd {Q E P F S R : ℕ}
    (hE : Enc blank startSym endSym mark x a b ⟨0, Q, E, P, F, S, R⟩ ts) :
    Enc blank startSym endSym mark x a b ⟨0, Q, E, P, F, S, R⟩
      (applyActs blank (dTest (ctCd : CT sc) blank mark) ts) :=
  ⟨hE.v1, hE.v2, PalPeg.Tape.counter'_dec_zero hE.cd, hE.cq, hE.ce, hE.cp, hE.cf, hE.cs, hE.cr⟩

theorem dTest_enc_Cq {D E P F S R : ℕ}
    (hE : Enc blank startSym endSym mark x a b ⟨D, 0, E, P, F, S, R⟩ ts) :
    Enc blank startSym endSym mark x a b ⟨D, 0, E, P, F, S, R⟩
      (applyActs blank (dTest (ctCq : CT sc) blank mark) ts) :=
  ⟨hE.v1, hE.v2, hE.cd, PalPeg.Tape.counter'_dec_zero hE.cq, hE.ce, hE.cp, hE.cf, hE.cs, hE.cr⟩

theorem dTest_enc_Ce {D Q P F S R : ℕ}
    (hE : Enc blank startSym endSym mark x a b ⟨D, Q, 0, P, F, S, R⟩ ts) :
    Enc blank startSym endSym mark x a b ⟨D, Q, 0, P, F, S, R⟩
      (applyActs blank (dTest (ctCe : CT sc) blank mark) ts) :=
  ⟨hE.v1, hE.v2, hE.cd, hE.cq, PalPeg.Tape.counter'_dec_zero hE.ce, hE.cp, hE.cf, hE.cs, hE.cr⟩

theorem dTest_enc_Cp {D Q E F S R : ℕ}
    (hE : Enc blank startSym endSym mark x a b ⟨D, Q, E, 0, F, S, R⟩ ts) :
    Enc blank startSym endSym mark x a b ⟨D, Q, E, 0, F, S, R⟩
      (applyActs blank (dTest (ctCp : CT sc) blank mark) ts) :=
  ⟨hE.v1, hE.v2, hE.cd, hE.cq, hE.ce, PalPeg.Tape.counter'_dec_zero hE.cp, hE.cf, hE.cs, hE.cr⟩

theorem dTest_enc_Cf {D Q E P S R : ℕ}
    (hE : Enc blank startSym endSym mark x a b ⟨D, Q, E, P, 0, S, R⟩ ts) :
    Enc blank startSym endSym mark x a b ⟨D, Q, E, P, 0, S, R⟩
      (applyActs blank (dTest (ctCf : CT sc) blank mark) ts) :=
  ⟨hE.v1, hE.v2, hE.cd, hE.cq, hE.ce, hE.cp, PalPeg.Tape.counter'_dec_zero hE.cf, hE.cs, hE.cr⟩

theorem dTest_enc_Cr {D Q E P F S : ℕ}
    (hE : Enc blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, 0⟩ ts) :
    Enc blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, 0⟩
      (applyActs blank (dTest (ctCr : CT sc) blank mark) ts) :=
  ⟨hE.v1, hE.v2, hE.cd, hE.cq, hE.ce, hE.cp, hE.cf, hE.cs, PalPeg.Tape.counter'_dec_zero hE.cr⟩

@[simp] theorem dTest_length (c : CT sc) (blank mark : Fin sc) :
    (dTest c blank mark).length = 2 := rfl

end DTestEnc

/-! ## 10. 直線的な合成（`cleanProg` / `resetProg` / `swapProg`） -/

section Composites

variable {Terminal : Type} {blank startSym endSym mark : Fin sc} {x : List (Fin sc)} {k : ℕ}

theorem execA_seq' {P Q : Prog A9 Cond9} {ts : Tapes sc} {L₁ L₂ L : List (Act sc)}
    (h1 : ExecA Terminal blank endSym mark P ts L₁)
    (h2 : ExecA Terminal blank endSym mark Q (applyActs blank L₁ ts) L₂)
    (hL : L₁ ++ L₂ = L) : ExecA Terminal blank endSym mark (Prog.seq P Q) ts L :=
  execA_of_eq hL (execA_seq h1 h2)

/-! ### `cleanProg` -/

/-- `cleanProg` の有限制御プログラム（`k`, `P` に依存しない）。 -/
def CLEAN : Prog A9 Cond9 := Prog.seq pvProg dzProg

/-- `CLEAN` が実際に実行する動作列（`cleanProg` にゼロ判定 2 動作 × 2 を足したもの）。 -/
def cleanActs (blank mark : Fin sc) (k P : ℕ) : List (Act sc) :=
  (pvLoop blank P ++ dTest (ctCp : CT sc) blank mark) ++
    (dzLoop blank ((k - 1) * P) ++ dTest (ctCd : CT sc) blank mark)

@[simp] theorem cleanActs_length (blank mark : Fin sc) (k P : ℕ) :
    (cleanActs blank mark k P).length = (cleanProg blank k P).length + 4 := by
  simp [cleanActs, cleanProg]
  omega

theorem CLEAN_exec (hmark : mark ≠ blank) {s P F : ℕ} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x s (s + P) ⟨(k - 1) * P, 0, 0, P, F, s, 0⟩ ts) :
    ExecA Terminal blank endSym mark CLEAN ts (cleanActs blank mark k P) := by
  have h1 := pvProg_exec (Terminal := Terminal) (endSym := endSym) hmark P ts hE.cp
  have e1 := pvLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) P s s ((k - 1) * P) 0 0 0 F s 0 ts
    (by rw [show (0 : ℕ) + P = P from by omega]; exact hE)
  have e2 := dTest_enc_Cp (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) e1
  rw [← applyActs_append] at e2
  have h2 := dzProg_exec (Terminal := Terminal) (endSym := endSym) hmark ((k - 1) * P)
    (applyActs blank (pvLoop blank P ++ dTest (ctCp : CT sc) blank mark) ts) e2.cd
  exact execA_seq' h1 h2 rfl

/-! ### `resetProg` -/

/-- `resetProg` の有限制御プログラム。 -/
def RESET : Prog A9 Cond9 :=
  Prog.seq qvProg (Prog.seq fzProg (Prog.seq pfvProg (Prog.seq rzProg dzProg)))

/-- `RESET` が実際に実行する動作列。 -/
def resetActs (blank mark : Fin sc) (q p₁ p₂ r d : ℕ) : List (Act sc) :=
  (qvLoop blank q ++ dTest (ctCq : CT sc) blank mark) ++
    ((fzLoop blank p₁ ++ dTest (ctCf : CT sc) blank mark) ++
      ((pfvLoop blank p₂ ++ dTest (ctCp : CT sc) blank mark) ++
        ((rzLoop blank r ++ dTest (ctCr : CT sc) blank mark) ++
          (dzLoop blank d ++ dTest (ctCd : CT sc) blank mark))))

@[simp] theorem resetActs_length (blank mark : Fin sc) (q p₁ p₂ r d : ℕ) :
    (resetActs blank mark q p₁ p₂ r d).length
      = (resetProg blank q p₁ p₂ r d).length + 10 := by
  simp [resetActs, resetProg]
  omega

theorem RESET_exec (hmark : mark ≠ blank) {s q p₁ p₂ r d : ℕ} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x (s + q) (s + p₂ + q) ⟨d, q, 0, p₂, p₁, s, r⟩ ts) :
    ExecA Terminal blank endSym mark RESET ts (resetActs blank mark q p₁ p₂ r d) := by
  -- 第 1 区間：`Cq` を落とす
  have h1 := qvProg_exec (Terminal := Terminal) (endSym := endSym) hmark q ts hE.cq
  have e1 := qvLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) q s (s + p₂) d 0 0 p₂ p₁ s r ts (by simpa using hE)
  have e1' := dTest_enc_Cq (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) e1
  rw [← applyActs_append] at e1'
  set ts1 := applyActs blank (qvLoop blank q ++ dTest (ctCq : CT sc) blank mark) ts with hts1
  -- 第 2 区間：`Cf` を落とす
  have h2 := fzProg_exec (Terminal := Terminal) (endSym := endSym) hmark p₁ ts1 e1'.cf
  have e2 := fzLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) p₁ s (s + p₂) d 0 0 p₂ 0 s r ts1 (by simpa using e1')
  have e2' := dTest_enc_Cf (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) e2
  rw [← applyActs_append] at e2'
  set ts2 := applyActs blank (fzLoop blank p₁ ++ dTest (ctCf : CT sc) blank mark) ts1 with hts2
  -- 第 3 区間：`Cp` を `Cf` へ移す
  have h3 := pfvProg_exec (Terminal := Terminal) (endSym := endSym) hmark p₂ ts2 e2'.cp
  have e3 := pfvLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) p₂ s s d 0 0 0 0 s r ts2 (by simpa using e2')
  have e3' := dTest_enc_Cp (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) e3
  rw [← applyActs_append] at e3'
  set ts3 := applyActs blank (pfvLoop blank p₂ ++ dTest (ctCp : CT sc) blank mark) ts2 with hts3
  -- 第 4 区間：`Cr` を落とす
  have h4 := rzProg_exec (Terminal := Terminal) (endSym := endSym) hmark r ts3 e3'.cr
  have e4 := rzLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) r s s d 0 0 0 (0 + p₂) s 0 ts3 (by simpa using e3')
  have e4' := dTest_enc_Cr (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) e4
  rw [← applyActs_append] at e4'
  set ts4 := applyActs blank (rzLoop blank r ++ dTest (ctCr : CT sc) blank mark) ts3 with hts4
  -- 第 5 区間：`Cd` を落とす
  have h5 := dzProg_exec (Terminal := Terminal) (endSym := endSym) hmark d ts4 e4'.cd
  exact execA_seq' h1 (execA_seq' h2 (execA_seq' h3 (execA_seq' h4 h5 rfl) rfl) rfl) rfl

/-! ### `swapProg` -/

/-- `swapProg` の有限制御プログラム。 -/
def SWAP : Prog A9 Cond9 := Prog.seq qvProg (Prog.seq pvProg (Prog.seq fcProg dzProg))

/-- `SWAP` が実際に実行する動作列。 -/
def swapActs (blank mark : Fin sc) (q p p₁ d : ℕ) : List (Act sc) :=
  (qvLoop blank q ++ dTest (ctCq : CT sc) blank mark) ++
    ((pvLoop blank p ++ dTest (ctCp : CT sc) blank mark) ++
      ((fcLoop blank p₁ ++ dTest (ctCf : CT sc) blank mark) ++
        (dzLoop blank d ++ dTest (ctCd : CT sc) blank mark)))

@[simp] theorem swapActs_length (blank mark : Fin sc) (q p p₁ d : ℕ) :
    (swapActs blank mark q p p₁ d).length = (swapProg blank q p p₁ d).length + 8 := by
  simp [swapActs, swapProg]
  omega

theorem SWAP_exec (hmark : mark ≠ blank) {s q p p₁ r d : ℕ} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x (s + q) (s + p + q) ⟨d, q, 0, p, p₁, s, r⟩ ts) :
    ExecA Terminal blank endSym mark SWAP ts (swapActs blank mark q p p₁ d) := by
  have h1 := qvProg_exec (Terminal := Terminal) (endSym := endSym) hmark q ts hE.cq
  have e1 := qvLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) q s (s + p) d 0 0 p p₁ s r ts (by simpa using hE)
  have e1' := dTest_enc_Cq (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) e1
  rw [← applyActs_append] at e1'
  set ts1 := applyActs blank (qvLoop blank q ++ dTest (ctCq : CT sc) blank mark) ts with hts1
  have h2 := pvProg_exec (Terminal := Terminal) (endSym := endSym) hmark p ts1 e1'.cp
  have e2 := pvLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) p s s d 0 0 0 p₁ s r ts1 (by simpa using e1')
  have e2' := dTest_enc_Cp (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) e2
  rw [← applyActs_append] at e2'
  set ts2 := applyActs blank (pvLoop blank p ++ dTest (ctCp : CT sc) blank mark) ts1 with hts2
  have h3 := fcProg_exec (Terminal := Terminal) (endSym := endSym) hmark p₁ ts2 e2'.cf
  have e3 := fcLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) p₁ s s d 0 0 0 0 s r ts2 (by simpa using e2')
  have e3' := dTest_enc_Cf (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) e3
  rw [← applyActs_append] at e3'
  set ts3 := applyActs blank (fcLoop blank p₁ ++ dTest (ctCf : CT sc) blank mark) ts2 with hts3
  have h4 := dzProg_exec (Terminal := Terminal) (endSym := endSym) hmark d ts3 e3'.cd
  exact execA_seq' h1 (execA_seq' h2 (execA_seq' h3 h4 rfl) rfl) rfl

/-! ### `dRst` / `dSwap` / `dCln`（`decProg` が直接使う合成） -/

/-- `dRst` の有限制御プログラム。 -/
def DRST : Prog A9 Cond9 := Prog.seq ezProg RESET

/-- `DRST` が実際に実行する動作列。 -/
def drstActs (blank mark : Fin sc) (e q p₁ p₂ r d : ℕ) : List (Act sc) :=
  (ezLoop blank e ++ dTest (ctCe : CT sc) blank mark) ++ resetActs blank mark q p₁ p₂ r d

@[simp] theorem drstActs_length (blank mark : Fin sc) (e q p₁ p₂ r d : ℕ) :
    (drstActs blank mark e q p₁ p₂ r d).length
      = (ezLoop blank e).length + (resetProg blank q p₁ p₂ r d).length + 12 := by
  simp [drstActs]
  omega

theorem DRST_exec (hmark : mark ≠ blank) {s e q p₁ p₂ r d : ℕ} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x (s + q) (s + p₂ + q) ⟨d, q, e, p₂, p₁, s, r⟩ ts) :
    ExecA Terminal blank endSym mark DRST ts (drstActs blank mark e q p₁ p₂ r d) := by
  have h1 := ezProg_exec (Terminal := Terminal) (endSym := endSym) hmark e ts hE.ce
  have e1 := ezLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) e (s + q) (s + p₂ + q) d q 0 p₂ p₁ s r ts (by simpa using hE)
  have e1' := dTest_enc_Ce (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) e1
  rw [← applyActs_append] at e1'
  have h2 := RESET_exec (Terminal := Terminal) (startSym := startSym) (x := x) hmark e1'
  exact execA_seq' h1 h2 rfl

/-- `dSwap` の有限制御プログラム。 -/
def DSWAP : Prog A9 Cond9 := Prog.seq ezProg SWAP

/-- `DSWAP` が実際に実行する動作列。 -/
def dswapActs (blank mark : Fin sc) (e q p p₁ d : ℕ) : List (Act sc) :=
  (ezLoop blank e ++ dTest (ctCe : CT sc) blank mark) ++ swapActs blank mark q p p₁ d

@[simp] theorem dswapActs_length (blank mark : Fin sc) (e q p p₁ d : ℕ) :
    (dswapActs blank mark e q p p₁ d).length
      = (ezLoop blank e).length + (swapProg blank q p p₁ d).length + 10 := by
  simp [dswapActs]
  omega

theorem DSWAP_exec (hmark : mark ≠ blank) {s e q p p₁ r d : ℕ} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x (s + q) (s + p + q) ⟨d, q, e, p, p₁, s, r⟩ ts) :
    ExecA Terminal blank endSym mark DSWAP ts (dswapActs blank mark e q p p₁ d) := by
  have h1 := ezProg_exec (Terminal := Terminal) (endSym := endSym) hmark e ts hE.ce
  have e1 := ezLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) e (s + q) (s + p + q) d q 0 p p₁ s r ts (by simpa using hE)
  have e1' := dTest_enc_Ce (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) e1
  rw [← applyActs_append] at e1'
  have h2 := SWAP_exec (Terminal := Terminal) (startSym := startSym) (x := x) (r := r) hmark e1'
  exact execA_seq' h1 h2 rfl

/-- `dCln` の有限制御プログラム。 -/
def DCLN : Prog A9 Cond9 := Prog.seq CLEAN fzProg

/-- `DCLN` が実際に実行する動作列。 -/
def dclnActs (blank mark : Fin sc) (k P F : ℕ) : List (Act sc) :=
  cleanActs blank mark k P ++ (fzLoop blank F ++ dTest (ctCf : CT sc) blank mark)

@[simp] theorem dclnActs_length (blank mark : Fin sc) (k P F : ℕ) :
    (dclnActs blank mark k P F).length
      = (cleanProg blank k P).length + (fzLoop blank F).length + 6 := by
  simp [dclnActs]
  omega

theorem DCLN_exec (hmark : mark ≠ blank) {s P F : ℕ} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x s (s + P) ⟨(k - 1) * P, 0, 0, P, F, s, 0⟩ ts) :
    ExecA Terminal blank endSym mark DCLN ts (dclnActs blank mark k P F) := by
  have h1 := CLEAN_exec (Terminal := Terminal) (startSym := startSym) hmark hE
  -- `cleanActs` 実行後の符号化
  have e1 := pvLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) P s s ((k - 1) * P) 0 0 0 F s 0 ts
    (by rw [show (0 : ℕ) + P = P from by omega]; exact hE)
  have e1' := dTest_enc_Cp (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) e1
  rw [← applyActs_append] at e1'
  set ts1 := applyActs blank (pvLoop blank P ++ dTest (ctCp : CT sc) blank mark) ts with hts1
  have e2 := dzLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) ((k - 1) * P) s s 0 0 0 0 F s 0 ts1 (by simpa using e1')
  have e2' := dTest_enc_Cd (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) e2
  rw [← applyActs_append] at e2'
  have hst : applyActs blank (cleanActs blank mark k P) ts
      = applyActs blank (dzLoop blank ((k - 1) * P) ++ dTest (ctCd : CT sc) blank mark) ts1 := by
    rw [cleanActs, applyActs_append, hts1]
  have h2 := fzProg_exec (Terminal := Terminal) (endSym := endSym) hmark F
    (applyActs blank (cleanActs blank mark k P) ts) (by rw [hst]; exact e2'.cf)
  exact execA_seq' h1 h2 rfl

/-! ### `loadR`（`E = 0` の場合） -/

/-- `loadR` の有限制御プログラム。 -/
def LOADR : Prog A9 Cond9 := Prog.seq qrProg (Prog.seq pcProg cpProg)

/-- `LOADR` が実際に実行する動作列。 -/
def loadRActs (blank mark : Fin sc) (Q P : ℕ) : List (Act sc) :=
  (qrLoop blank Q ++ dTest (ctCq : CT sc) blank mark) ++
    ((pcLoop blank P ++ dTest (ctCp : CT sc) blank mark) ++
      (cpLoop blank P ++ dTest (ctCe : CT sc) blank mark))

@[simp] theorem loadRActs_length (blank mark : Fin sc) (Q P : ℕ) :
    (loadRActs blank mark Q P).length = (loadR blank Q P).length + 6 := by
  simp [loadRActs, loadR]
  omega

theorem LOADR_exec (hmark : mark ≠ blank) {a b D P Q F S : ℕ} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x a b ⟨D, Q, 0, P, F, S, 0⟩ ts) :
    ExecA Terminal blank endSym mark LOADR ts (loadRActs blank mark Q P) := by
  have h1 := qrProg_exec (Terminal := Terminal) (endSym := endSym) hmark Q ts hE.cq
  have e1 := qrLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) Q a b D 0 0 P F S 0 ts (by simpa using hE)
  have e1' := dTest_enc_Cq (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) e1
  rw [← applyActs_append] at e1'
  set ts1 := applyActs blank (qrLoop blank Q ++ dTest (ctCq : CT sc) blank mark) ts with hts1
  have h2 := pcProg_exec (Terminal := Terminal) (endSym := endSym) hmark P ts1 e1'.cp
  have e2 := pcLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) P a b D 0 0 0 F S (0 + Q) ts1 (by simpa using e1')
  have e2' := dTest_enc_Cp (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) e2
  rw [← applyActs_append] at e2'
  set ts2 := applyActs blank (pcLoop blank P ++ dTest (ctCp : CT sc) blank mark) ts1 with hts2
  have h3 := cpProg_exec (Terminal := Terminal) (endSym := endSym) hmark P ts2
    (show PalPeg.Tape.CounterView' blank mark ts2.Ce P by simpa using e2'.ce)
  exact execA_seq' h1 (execA_seq' h2 h3 rfl) rfl

/-- `LOADR` 実行後の符号化（`loadR_enc` の `E = 0` 版）。 -/
theorem LOADR_enc {a b D P Q F S : ℕ} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x a b ⟨D, Q, 0, P, F, S, 0⟩ ts) :
    Enc blank startSym endSym mark x a b ⟨D, 0, 0, P, F, S, Q + P⟩
      (applyActs blank (loadRActs blank mark Q P) ts) := by
  have e1 := qrLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) Q a b D 0 0 P F S 0 ts (by simpa using hE)
  have e1' := dTest_enc_Cq (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) e1
  rw [← applyActs_append] at e1'
  set ts1 := applyActs blank (qrLoop blank Q ++ dTest (ctCq : CT sc) blank mark) ts with hts1
  have e2 := pcLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) P a b D 0 0 0 F S (0 + Q) ts1 (by simpa using e1')
  have e2' := dTest_enc_Cp (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) e2
  rw [← applyActs_append] at e2'
  set ts2 := applyActs blank (pcLoop blank P ++ dTest (ctCp : CT sc) blank mark) ts1 with hts2
  have e3 := cpLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) P a b D 0 0 0 F S (0 + Q + P) ts2 (by simpa using e2')
  have e3' := dTest_enc_Ce (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) e3
  rw [← applyActs_append] at e3'
  have hst : applyActs blank (loadRActs blank mark Q P) ts
      = applyActs blank (cpLoop blank P ++ dTest (ctCe : CT sc) blank mark) ts2 := by
    rw [loadRActs, applyActs_append, applyActs_append, hts2, hts1]
  rw [hst]
  simpa using e3'

end Composites

/-! ## 11. まとめと未実現部分

本ファイルで得られたのは、`PalPeg.GSPreprocessTapes` の**カウンタ駆動部分**の
完全な有限制御化である。

* `A9`／`Cond9`／`I9` は 9 本テープの有限制御の解釈であり、条件は
  「あるテープの読みがマーカでない」「`V2` の読みが右端番人でない」
  「`V1` と `V2` の読みが等しい」の 3 種類しかない（すべてヘッドの読みだけ）。
* `DLOOP idx rest` は `sc` にも `blank` にも依存しない真の有限制御プログラムであり、
  `dLoop_exec` により「駆動カウンタの値が `n` なら `dPow … n ++ dTest` を実行する」
  ことが示されている。反復回数はプログラムに埋め込まれていない。
* `dTest`（probe と復元の 2 動作）が元の動作列との唯一の差分であり、
  各ループにつき定数 2 動作しか増えない。

### まだ実現していないもの

1. `perLoop1` と `rewindUnit` は駆動 probe の**前**に `V1` の移動を置くので、
   `DLOOP` の形（`[c blank .left, c blank .stay] ++ rest`）に合わない。
   単位内の動作を並べ替えた変種を新たに定義し、その `_enc` を取り直す必要がある。
2. `repoProg` の末尾 `pvLoop blank (P - 1)` は `Cp` を `P` から `1` までしか
   減らさない**部分ドレイン**なので、ゼロまで回す `DLOOP` では実現できない。
   `Cp` の最後の 1 を退避する追加ガジェットが必要。
3. `subKLoop blank p k` は `k` 回の繰り返しなので `Prog` としては `k` 段の
   `seq` で書けるが、その `_exec` はまだ書いていない。
4. `bottomProg` の `sIncs blank (n - sOf ts)` は `V2` が右端番人 `endSym` を
   読むまで `V2` と `Cs` を同時に右へ動かすループ（条件 `Cond9.v2NotEnd`）で
   実現できる。動作列は `(V2 .right :: Cs blank .right)^(n-s)` となり、
   元の `sIncs` とは `V2` の移動分だけ異なる（終状態で `V2` は右端に来る）。
5. 内側走査 `mProg` / `rProg` / `sProg`、および外側 `oProg` / `fpProg` /
   `frProg` / `soProg` / `spProg` / `stepProg` / `stripProg2` / `decProg` は、
   オラクル `orcR` / `orc2R` / `orcCf` の**カウンタ比較**を実行する副プログラム
   （2 本の単進カウンタを鏡像つきで同時に減らして比較し、復元する）を
   先に作る必要がある。比較 1 回のコストは `Θ(比較する値)` であり、
   比較が起きる外側 1 反復はすでに `Θ(p)` または `Θ(q)` を払っているので
   線形予算には収まるが、その計上をやり直す必要がある。
-/

section AxiomCheck

#print axioms dLoop_exec
#print axioms qvProg_exec
#print axioms fzProg_exec
#print axioms ezProg_exec
#print axioms rzProg_exec
#print axioms pzProg_exec
#print axioms dzProg_exec
#print axioms pfvProg_exec
#print axioms fcProg_exec
#print axioms qrProg_exec
#print axioms pcProg_exec
#print axioms cpProg_exec
#print axioms cfProg_exec
#print axioms pfProg_exec
#print axioms prProg_exec
#print axioms rvProg_exec
#print axioms crProg_exec
#print axioms pvProg_exec
#print axioms rv2Prog_exec
#print axioms ecProg_exec
#print axioms qpProg_exec
#print axioms csProg_exec
#print axioms CLEAN_exec
#print axioms RESET_exec
#print axioms SWAP_exec
#print axioms DRST_exec
#print axioms DSWAP_exec
#print axioms DCLN_exec
#print axioms LOADR_exec
#print axioms LOADR_enc

end AxiomCheck

end PalPeg.GSPreProg
