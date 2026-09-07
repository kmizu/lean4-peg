import PalPeg.PatternTapes
import PalPeg.PatternTapesPair
import PalPeg.ProgLangLib

/-!
# 段の準備フェーズの有限制御プログラム化 (`PatternProg`)

`PalPeg.PatternTapes` / `PalPeg.PatternTapesPair` の準備フェーズは、テープ状態から
計算される**動作列**（`List (SAct sc)` / `List (PAct sc)`）として書かれている。
本ファイルはそれを `PalPeg.ProgLang` の構造化プログラム `Prog` に載せ替える。

## 設計

* 動作識別子 `ActG t sc = (テープ番号, 書く記号の出所, 移動)`。書く記号の出所は
  **定数** `Fin sc`（`blank` / `startSym` / `endSym`）か、**別テープのヘッドの読み**
  （`copyRound` の `put j (read (S i)) .right`）のいずれか。条件識別子
  `CondG t sc = (テープ番号, 記号)` は「そのテープの読みがその記号でない」。
  どちらも有限型なので、`ProgLang` の有限制御に載る。
* テープ手続きは本ファイル内の `TAct`（keep / put / copy）の列として書き直す
  （元ファイルの `SAct` / `PAct` は `copy` を持たないので、`copyRound` の
  「読んだ記号を書く」を静的な動作にするために `copy` を足す）。元の動作列との関係は
  **長さの一致**と**テープへの作用の一致**（`runG_… = run …`）で与える。
* 回数で回っていたループは、テープの境界（カウンタの `mark`、番兵記号）を読む
  `loop` に置き換える。境界を読むには 1 手前へプローブする必要があるので、
  **プローブ＋復元の 2 動作**が余分に入る（テープには作用しない：`probeRestore_*`）。

## 追加仮定について

`Prog` の条件はヘッドが今読んでいる記号しか見られない。したがって

* `copyLoop` の**回数 `s`** は単進カウンタ `sCs` を実際に 1 ずつ消費して数える
  （1 周回あたり 2 動作増える）。
* 入力コピーテープを左端まで読み切る側は、**左端に番兵記号がある**という仮定
  （`SentinelAt`）が要る。この模型では左端で移動が停留するため、番兵無しに
  「左端に来た」ことを読み取ることは（有限制御では）原理的に不可能。

いずれも定理の仮定として明示する。
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.PatternProg

open PegSeparation.RealTimeTM
open PalPeg
open PalPeg.Program
open PalPeg.ProgLang

variable {sc t : ℕ} {Terminal : Type}

/-! ## 1. 動作・条件の有限な添字型と解釈 -/

/-- 書く記号の出所：定数か、別テープのヘッドの読み。 -/
abbrev WSrc (t sc : ℕ) := Fin sc ⊕ Fin t

/-- 動作識別子。 -/
abbrev ActG (t sc : ℕ) := Fin t × WSrc t sc × Move

/-- 条件識別子 `(j, c)`：「テープ `j` の読みが `c` でない」。 -/
abbrev CondG (t sc : ℕ) := Fin t × Fin sc

/-- 書く記号。 -/
def wsym (σ : Fin t → Fin sc) : WSrc t sc → Fin sc
  | .inl c => c
  | .inr j => σ j

/-- 動作の解釈（入力記号は見ない）。 -/
def actOfG (a : ActG t sc) (_ : Option Terminal) (σ : Fin t → Fin sc) :
    Fin t → Fin sc × Move :=
  touchVec a.1 (wsym σ a.2.1) a.2.2 σ

/-- 条件の解釈。 -/
def condOfG (c : CondG t sc) (σ : Fin t → Fin sc) : Bool := decide (σ c.1 ≠ c.2)

/-- `t` 本テープの解釈。 -/
def IG (Terminal : Type) (t sc : ℕ) : Interp Terminal (ActG t sc) (CondG t sc) (Fin sc) t where
  actOf := actOfG
  condOf := condOfG

theorem inputFree_IG : InputFree (IG Terminal t sc) := fun _ _ _ => rfl

/-! ## 2. テープ表現の変換 -/

/-- 成果物のテープを `Prog` 側の zipper へ。 -/
def toS (tp : TapeConfiguration sc) : STape (Fin sc) := ⟨tp.left, tp.focus, tp.right⟩

@[simp] theorem toS_focus (tp : TapeConfiguration sc) : (toS tp).focus = tp.focus := rfl

/-- テープ束。 -/
abbrev Tps (t sc : ℕ) := Fin t → TapeConfiguration sc

/-- `t` 本まとめて。 -/
def TSg (S : Tps t sc) : Fin t → STape (Fin sc) := fun j => toS (S j)

@[simp] theorem TSg_focus (S : Tps t sc) (j : Fin t) : ((TSg S) j).focus = (S j).focus := rfl

theorem toS_step (blank : Fin sc) (tp : TapeConfiguration sc) (a : Fin sc) (m : Move) :
    toS (Tape.step blank tp a m) = (toS tp).applyAction blank (a, m) := by
  obtain ⟨L, f, R⟩ := tp
  cases m <;> cases L <;> cases R <;> rfl

/-! ## 3. テープ手続きの動作 `TAct` -/

/-- 1 本のテープへの 1 動作。`copy i j m` は「テープ `j` の読みをテープ `i` に書いて `m`」。 -/
inductive TAct (t sc : ℕ) where
  | keep : Fin t → Move → TAct t sc
  | put : Fin t → Fin sc → Move → TAct t sc
  | copy : Fin t → Fin t → Move → TAct t sc
  deriving DecidableEq

namespace TAct

/-- 動作が触るテープ。 -/
def tape : TAct t sc → Fin t
  | .keep i _ => i
  | .put i _ _ => i
  | .copy i _ _ => i

/-- 書き込む記号。 -/
def write (S : Tps t sc) : TAct t sc → Fin sc
  | .keep i _ => (S i).focus
  | .put _ x _ => x
  | .copy _ j _ => (S j).focus

/-- 移動。 -/
def mv : TAct t sc → Move
  | .keep _ m => m
  | .put _ _ m => m
  | .copy _ _ m => m

/-- 対応する `Prog` の動作識別子。 -/
def act : TAct t sc → ActG t sc
  | .keep i m => (i, .inr i, m)
  | .put i x m => (i, .inl x, m)
  | .copy i j m => (i, .inr j, m)

end TAct

/-- テープ束の更新。 -/
def updG (S : Tps t sc) (i : Fin t) (tp : TapeConfiguration sc) : Tps t sc :=
  fun j => if j = i then tp else S j

@[simp] theorem updG_self (S : Tps t sc) (i : Fin t) (tp : TapeConfiguration sc) :
    updG S i tp i = tp := by simp [updG]

theorem updG_ne {i j : Fin t} (S : Tps t sc) (tp : TapeConfiguration sc) (h : j ≠ i) :
    updG S i tp j = S j := by simp [updG, h]

/-- 1 動作の適用。 -/
def applyG (blank : Fin sc) (S : Tps t sc) (a : TAct t sc) : Tps t sc :=
  updG S a.tape (Tape.step blank (S a.tape) (a.write S) a.mv)

/-- 動作列の実行。 -/
def runG (blank : Fin sc) (l : List (TAct t sc)) (S : Tps t sc) : Tps t sc :=
  l.foldl (applyG blank) S

@[simp] theorem runG_nil (blank : Fin sc) (S : Tps t sc) : runG blank [] S = S := rfl

@[simp] theorem runG_cons (blank : Fin sc) (a : TAct t sc) (l : List (TAct t sc))
    (S : Tps t sc) : runG blank (a :: l) S = runG blank l (applyG blank S a) := rfl

theorem runG_append (blank : Fin sc) (l₁ l₂ : List (TAct t sc)) (S : Tps t sc) :
    runG blank (l₁ ++ l₂) S = runG blank l₂ (runG blank l₁ S) := by simp [runG]

@[simp] theorem applyG_self (blank : Fin sc) (S : Tps t sc) (a : TAct t sc) :
    applyG blank S a a.tape = Tape.step blank (S a.tape) (a.write S) a.mv := updG_self ..

@[simp] theorem applyG_put_self (blank : Fin sc) (S : Tps t sc) (i : Fin t) (x : Fin sc)
    (m : Move) : applyG blank S (TAct.put i x m) i = Tape.step blank (S i) x m := updG_self ..

@[simp] theorem applyG_keep_self (blank : Fin sc) (S : Tps t sc) (i : Fin t) (m : Move) :
    applyG blank S (TAct.keep i m) i = Tape.step blank (S i) (S i).focus m := updG_self ..

@[simp] theorem applyG_copy_self (blank : Fin sc) (S : Tps t sc) (i j : Fin t) (m : Move) :
    applyG blank S (TAct.copy i j m) i = Tape.step blank (S i) (S j).focus m := updG_self ..

theorem applyG_ne (blank : Fin sc) (S : Tps t sc) (a : TAct t sc) {j : Fin t}
    (h : j ≠ a.tape) : applyG blank S a j = S j := updG_ne _ _ h

theorem runG_untouched (blank : Fin sc) (j : Fin t) :
    ∀ (l : List (TAct t sc)) (S : Tps t sc), (∀ a ∈ l, a.tape ≠ j) → runG blank l S j = S j := by
  intro l
  induction l with
  | nil => intro S _; rfl
  | cons a l ih =>
    intro S h
    rw [runG_cons, ih _ (fun b hb => h b (List.mem_cons_of_mem a hb)),
      applyG_ne blank S a (Ne.symm (h a (List.mem_cons_self ..)))]

/-- 動作が読み書きするテープ。 -/
def TAct.uses : TAct t sc → List (Fin t)
  | .keep i _ => [i]
  | .put i _ _ => [i]
  | .copy i j _ => [i, j]

/-- **局所性**：テープ `cs` を読みも書きもしない動作列は、`cs` 以外で一致する
二つの状態を `cs` 以外で一致したまま保つ。 -/
theorem runG_local (blank : Fin sc) (cs : Fin t) :
    ∀ (L : List (TAct t sc)) (S T : Tps t sc), (∀ a ∈ L, cs ∉ a.uses) →
      (∀ l, l ≠ cs → T l = S l) → ∀ l, l ≠ cs → runG blank L T l = runG blank L S l := by
  intro L
  induction L with
  | nil => intro S T _ h l hl; exact h l hl
  | cons a L ih =>
      intro S T huse h l hl
      have hause : cs ∉ a.uses := huse a (List.mem_cons_self ..)
      have hstep : ∀ m, m ≠ cs → applyG blank T a m = applyG blank S a m := by
        intro m hm
        by_cases hma : m = a.tape
        · have hm' : a.tape ≠ cs := hma ▸ hm
          rw [hma, applyG_self, applyG_self, h a.tape hm']
          congr 1
          cases a with
          | keep i m' => show (T i).focus = (S i).focus; rw [h i hm']
          | put i x m' => rfl
          | copy i j m' =>
              have hj : j ≠ cs := by
                intro hc
                exact hause (by simp only [TAct.uses, List.mem_cons, List.not_mem_nil]; tauto)
              show (T j).focus = (S j).focus
              rw [h j hj]
        · rw [applyG_ne blank _ _ hma, applyG_ne blank _ _ hma, h m hm]
      exact ih (applyG blank S a) (applyG blank T a)
        (fun b hb => huse b (List.mem_cons_of_mem a hb)) hstep l hl

/-- **局所性（2 テープ版）**：テープ `cs1`,`cs2` のどちらも読みも書きもしない動作列は、
その 2 本以外で一致する二つの状態を、その 2 本以外で一致したまま保つ。 -/
theorem runG_local2 (blank : Fin sc) (cs1 cs2 : Fin t) :
    ∀ (L : List (TAct t sc)) (S T : Tps t sc),
      (∀ a ∈ L, cs1 ∉ a.uses ∧ cs2 ∉ a.uses) →
      (∀ l, l ≠ cs1 → l ≠ cs2 → T l = S l) →
      ∀ l, l ≠ cs1 → l ≠ cs2 → runG blank L T l = runG blank L S l := by
  intro L
  induction L with
  | nil => intro S T _ h l hl1 hl2; exact h l hl1 hl2
  | cons a L ih =>
      intro S T huse h l hl1 hl2
      have hause := huse a (List.mem_cons_self ..)
      have hstep : ∀ m, m ≠ cs1 → m ≠ cs2 → applyG blank T a m = applyG blank S a m := by
        intro m hm1 hm2
        by_cases hma : m = a.tape
        · have hm1' : a.tape ≠ cs1 := hma ▸ hm1
          have hm2' : a.tape ≠ cs2 := hma ▸ hm2
          rw [hma, applyG_self, applyG_self, h a.tape hm1' hm2']
          congr 1
          cases a with
          | keep i m' => show (T i).focus = (S i).focus; rw [h i hm1' hm2']
          | put i x m' => rfl
          | copy i j m' =>
              have hj1 : j ≠ cs1 := by
                intro hc
                exact hause.1 (by simp only [TAct.uses, List.mem_cons, List.not_mem_nil]; tauto)
              have hj2 : j ≠ cs2 := by
                intro hc
                exact hause.2 (by simp only [TAct.uses, List.mem_cons, List.not_mem_nil]; tauto)
              show (T j).focus = (S j).focus
              rw [h j hj1 hj2]
        · rw [applyG_ne blank _ _ hma, applyG_ne blank _ _ hma, h m hm1 hm2]
      exact ih (applyG blank S a) (applyG blank T a)
        (fun b hb => huse b (List.mem_cons_of_mem a hb)) hstep l hl1 hl2

/-! ## 4. 動作列に対応するベクトル列 -/

/-- `TAct` に対応する write+move ベクトル。 -/
def gavec (S : Tps t sc) (a : TAct t sc) : Fin t → Fin sc × Move :=
  fun j => if j = a.tape then (a.write S, a.mv) else ((S j).focus, Move.stay)

/-- 動作列に対応するベクトル列（各段の状態で評価する）。 -/
def gavecs (blank : Fin sc) : List (TAct t sc) → Tps t sc → List (Fin t → Fin sc × Move)
  | [], _ => []
  | a :: l, S => gavec S a :: gavecs blank l (applyG blank S a)

@[simp] theorem gavecs_nil (blank : Fin sc) (S : Tps t sc) : gavecs blank [] S = [] := rfl

@[simp] theorem gavecs_cons (blank : Fin sc) (a : TAct t sc) (l : List (TAct t sc))
    (S : Tps t sc) :
    gavecs blank (a :: l) S = gavec S a :: gavecs blank l (applyG blank S a) := rfl

@[simp] theorem gavecs_length (blank : Fin sc) :
    ∀ (l : List (TAct t sc)) (S : Tps t sc), (gavecs blank l S).length = l.length := by
  intro l
  induction l with
  | nil => intro S; rfl
  | cons a l ih => intro S; simp [ih]

theorem gavecs_append (blank : Fin sc) :
    ∀ (l₁ l₂ : List (TAct t sc)) (S : Tps t sc),
      gavecs blank (l₁ ++ l₂) S = gavecs blank l₁ S ++ gavecs blank l₂ (runG blank l₁ S) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ S; rfl
  | cons a l ih => intro l₂ S; simp [ih]

theorem applyTrace_gavec (blank : Fin sc) (S : Tps t sc) (a : TAct t sc) :
    (fun j => ((TSg S) j).applyAction blank (gavec S a j)) = TSg (applyG blank S a) := by
  funext j
  by_cases hj : j = a.tape
  · subst hj
    show (toS (S a.tape)).applyAction blank (gavec S a a.tape) = toS (applyG blank S a a.tape)
    rw [applyG_self]
    simp only [gavec]
    exact (toS_step blank (S a.tape) (a.write S) a.mv).symm
  · show (toS (S j)).applyAction blank (gavec S a j) = toS (applyG blank S a j)
    rw [applyG_ne blank S a hj]
    simp only [gavec, if_neg hj]
    exact ProgLang.applyAction_focus_stay (blank := blank) (toS (S j))

theorem applyTrace_gavecs (blank : Fin sc) :
    ∀ (l : List (TAct t sc)) (S : Tps t sc),
      applyTrace blank (TSg S) (gavecs blank l S) = TSg (runG blank l S) := by
  intro l
  induction l with
  | nil => intro S; rfl
  | cons a l ih =>
      intro S
      rw [gavecs_cons, applyTrace_cons]
      show applyTrace blank (fun j => ((TSg S) j).applyAction blank (gavec S a j)) _ = _
      rw [applyTrace_gavec, ih]
      rfl

/-! ## 5. `TAct` の動作列に対する `Exec` -/

section ExecG

variable (Terminal)

/-- 「プログラム `P` は状態 `S` からちょうど動作列 `L` を実行して継続に戻る」。 -/
def ExecG (blank : Fin sc) (P : Prog (ActG t sc) (CondG t sc)) (S : Tps t sc)
    (L : List (TAct t sc)) : Prop :=
  Exec (IG Terminal t sc) blank P (TSg S) (gavecs blank L S)

variable {Terminal}
variable {blank : Fin sc}

theorem execG_of_eq {P : Prog (ActG t sc) (CondG t sc)} {S : Tps t sc}
    {L L' : List (TAct t sc)} (h : L = L') (hE : ExecG Terminal blank P S L) :
    ExecG Terminal blank P S L' := h ▸ hE

theorem execG_seq {P Q : Prog (ActG t sc) (CondG t sc)} {S : Tps t sc}
    {L₁ L₂ : List (TAct t sc)} (h1 : ExecG Terminal blank P S L₁)
    (h2 : ExecG Terminal blank Q (runG blank L₁ S) L₂) :
    ExecG Terminal blank (Prog.seq P Q) S (L₁ ++ L₂) := by
  unfold ExecG at h1 h2 ⊢
  rw [gavecs_append]
  refine exec_seq h1 ?_
  rw [applyTrace_gavecs]
  exact h2

theorem execG_skip {S : Tps t sc} :
    ExecG Terminal blank (Prog.skip : Prog (ActG t sc) (CondG t sc)) S [] := exec_skip _

/-- 1 動作のプログラム。 -/
def ACT (a : TAct t sc) : Prog (ActG t sc) (CondG t sc) := Prog.act a.act

theorem actVec_gavec (a : TAct t sc) (S : Tps t sc) :
    actVec (IG Terminal t sc) a.act (TSg S) = gavec S a := by
  cases a <;> rfl

theorem execG_act (a : TAct t sc) (S : Tps t sc) :
    ExecG Terminal blank (ACT a) S [a] := by
  have h := exec_act (blank := blank) (inputFree_IG (Terminal := Terminal) (t := t) (sc := sc))
    a.act (TSg S)
  rw [actVec_gavec] at h
  exact h

theorem condOfG_eq (c : CondG t sc) (S : Tps t sc) :
    (IG Terminal t sc).condOf c (fun j => ((TSg S) j).focus) = condOfG c (fun j => (S j).focus) :=
  rfl

theorem execG_ite_pos {c : CondG t sc} {P Q : Prog (ActG t sc) (CondG t sc)} {S : Tps t sc}
    {L : List (TAct t sc)} (hc : condOfG c (fun j => (S j).focus) = true)
    (h : ExecG Terminal blank P S L) :
    ExecG Terminal blank (Prog.ite c P Q) S L :=
  exec_ite_pos (by rw [condOfG_eq]; exact hc) h

theorem execG_ite_neg {c : CondG t sc} {P Q : Prog (ActG t sc) (CondG t sc)} {S : Tps t sc}
    {L : List (TAct t sc)} (hc : condOfG c (fun j => (S j).focus) = false)
    (h : ExecG Terminal blank Q S L) :
    ExecG Terminal blank (Prog.ite c P Q) S L :=
  exec_ite_neg (by rw [condOfG_eq]; exact hc) h

theorem execG_loop_stop {c : CondG t sc} {a : ActG t sc}
    {b : Prog (ActG t sc) (CondG t sc)} {S : Tps t sc}
    (hc : condOfG c (fun j => (S j).focus) = false) :
    ExecG Terminal blank (Prog.loop c a b) S [] :=
  exec_loop_stop (by rw [condOfG_eq]; exact hc)

theorem execG_loop_cont {c : CondG t sc} {a : TAct t sc} {b : Prog (ActG t sc) (CondG t sc)}
    {S : Tps t sc} {L₁ L₂ : List (TAct t sc)}
    (hc : condOfG c (fun j => (S j).focus) = true)
    (h1 : ExecG Terminal blank b (applyG blank S a) L₁)
    (h2 : ExecG Terminal blank (Prog.loop c a.act b) (runG blank L₁ (applyG blank S a)) L₂) :
    ExecG Terminal blank (Prog.loop c a.act b) S (a :: (L₁ ++ L₂)) := by
  unfold ExecG at h1 h2 ⊢
  rw [gavecs_cons, gavecs_append]
  have hT : (fun j => ((TSg S) j).applyAction blank
      (actVec (IG Terminal t sc) a.act (TSg S) j)) = TSg (applyG blank S a) := by
    rw [actVec_gavec]; exact applyTrace_gavec blank S a
  rw [← actVec_gavec (Terminal := Terminal) a S]
  refine exec_loop_cont (inputFree_IG (Terminal := Terminal) (t := t) (sc := sc))
    (by rw [condOfG_eq]; exact hc) ?_ ?_
  · rw [hT]; exact h1
  · rw [hT, applyTrace_gavecs]; exact h2

end ExecG

/-! ## 6. 静的な動作列のプログラム化 -/

section Static

/-- 動作列をそのまま並べたプログラム（分岐もループも無い部分）。 -/
def seqActs : List (TAct t sc) → Prog (ActG t sc) (CondG t sc)
  | [] => Prog.skip
  | a :: l => Prog.seq (ACT a) (seqActs l)

variable {blank : Fin sc}

theorem execG_seqActs : ∀ (L : List (TAct t sc)) (S : Tps t sc),
    ExecG Terminal blank (seqActs L) S L := by
  intro L
  induction L with
  | nil => intro S; exact execG_skip
  | cons a l ih =>
      intro S
      have := execG_seq (Terminal := Terminal) (execG_act (blank := blank) a S)
        (ih (runG blank [a] S))
      exact execG_of_eq rfl this

end Static

/-! ## 7. カウンタ駆動のループ

1 周回が `[put a blank .left, put a blank .stay] ++ body`（`body` は `a` を触らない
静的な動作列）である `n` 周回のループ。`n` はカウンタ `a` の値で、ループの条件は
プローブ後の読みが `mark` かどうかで決まる。先頭のプローブを外に出す代わりに、
末尾に**プローブ＋復元の 2 動作**が付く（テープには作用しない）。 -/

section DecLoop

variable (blank : Fin sc) (a : Fin t) (body : List (TAct t sc))

/-- 1 周回。 -/
def decRound : List (TAct t sc) := TAct.put a blank .left :: TAct.put a blank .stay :: body

/-- `n` 周回。 -/
def decActsN : ℕ → List (TAct t sc)
  | 0 => []
  | n + 1 => decRound blank a body ++ decActsN n

/-- ループ本体側から見た `n` 周回（先頭のプローブを外に出した形）。 -/
def decTail : ℕ → List (TAct t sc)
  | 0 => []
  | n + 1 => TAct.put a blank .stay :: ((body ++ [TAct.put a blank .left]) ++ decTail n)

theorem decActsN_length : ∀ n : ℕ, (decActsN blank a body n).length = (body.length + 2) * n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [decActsN, List.length_append, ih]; simp [decRound]; ring

theorem decCons : ∀ n : ℕ,
    TAct.put a blank .left :: decTail blank a body n
      = decActsN blank a body n ++ [TAct.put a blank (sc := sc) .left] := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [decTail, decActsN, List.append_assoc]
      simp only [decRound, List.cons_append, List.nil_append, List.append_assoc]
      rw [← ih]

/-- カウンタ駆動ループのプログラム。 -/
def decLoopProg (mark : Fin sc) : Prog (ActG t sc) (CondG t sc) :=
  Prog.seq (ACT (TAct.put a blank .left))
    (Prog.seq
      (Prog.loop (a, mark) (TAct.put a blank (sc := sc) .stay).act
        (seqActs (body ++ [TAct.put a blank .left])))
      (ACT (TAct.keep a .right)))

variable {blank a body}

theorem decLoop_cond {mark : Fin sc} {S : Tps t sc} {n : ℕ} (hne : mark ≠ blank)
    (h : Tape.CounterView' blank mark (S a) n) :
    condOfG (a, mark) (fun j => ((applyG blank S (TAct.put a blank .left)) j).focus)
      = decide (n ≠ 0) := by
  have hfoc : ((applyG blank S (TAct.put a blank .left)) a).focus
      = Tape.read (Tape.step blank (S a) blank .left) := by
    rw [applyG_put_self]; rfl
  simp only [condOfG, hfoc, ne_eq, Tape.counter'_isZero_iff hne h]

/-- **ループの一致**。 -/
theorem decLoop_tail_exec {mark : Fin sc} (hne : mark ≠ blank)
    (hbody : ∀ x ∈ body, x.tape ≠ a) :
    ∀ (n : ℕ) (S : Tps t sc), Tape.CounterView' blank mark (S a) n →
      ExecG Terminal blank
        (Prog.loop (a, mark) (TAct.put a blank (sc := sc) .stay).act
          (seqActs (body ++ [TAct.put a blank .left])))
        (applyG blank S (TAct.put a blank .left)) (decTail blank a body n) := by
  intro n
  induction n with
  | zero =>
      intro S hC
      exact execG_loop_stop (by rw [decLoop_cond hne hC]; simp)
  | succ n ih =>
      intro S hC
      rw [decTail]
      refine execG_loop_cont (a := TAct.put a blank .stay) ?_ ?_ ?_
      · rw [decLoop_cond hne hC]; simp
      · exact execG_seqActs _ _
      · rw [runG_append]
        refine ih _ ?_
        have hun : (runG blank body (applyG blank (applyG blank S (TAct.put a blank .left))
            (TAct.put a blank .stay))) a
            = (applyG blank (applyG blank S (TAct.put a blank .left))
                (TAct.put a blank .stay)) a :=
          runG_untouched blank a body _ hbody
        have hstep : (applyG blank (applyG blank S (TAct.put a blank .left))
            (TAct.put a blank .stay)) a
            = Tape.step blank (Tape.step blank (S a) blank .left) blank .stay := by
          rw [applyG_put_self, applyG_put_self]
        have hcv : Tape.CounterView' blank mark
            ((runG blank body (applyG blank (applyG blank S (TAct.put a blank .left))
              (TAct.put a blank .stay))) a) n := by
          rw [hun, hstep]; exact Tape.counter'_dec hC
        exact hcv

/-- **カウンタ駆動ループ全体**。動作列は `n` 周回ぶんに、末尾のプローブ＋復元 2 動作が付く。 -/
theorem decLoopProg_exec {mark : Fin sc} (hne : mark ≠ blank)
    (hbody : ∀ x ∈ body, x.tape ≠ a) (n : ℕ) (S : Tps t sc)
    (hC : Tape.CounterView' blank mark (S a) n) :
    ExecG Terminal blank (decLoopProg blank a body mark) S
      (decActsN blank a body n ++ [TAct.put a blank .left, TAct.keep a .right]) := by
  have e0 := execG_act (Terminal := Terminal) (blank := blank) (TAct.put a blank .left) S
  have e1 := decLoop_tail_exec (Terminal := Terminal) hne hbody n S hC
  have e2 := execG_act (Terminal := Terminal) (blank := blank) (TAct.keep a .right)
    (runG blank (decTail blank a body n) (applyG blank S (TAct.put a blank .left)))
  have hcomb := execG_seq e0 (execG_seq (by
      show ExecG Terminal blank _ (runG blank [TAct.put a blank (sc := sc) .left] S) _
      exact e1) e2)
  refine execG_of_eq ?_ hcomb
  have := decCons blank a body n
  calc [TAct.put a blank (sc := sc) .left] ++ (decTail blank a body n ++ [TAct.keep a .right])
      = (TAct.put a blank .left :: decTail blank a body n) ++ [TAct.keep a (sc := sc) .right] := by
        simp
    _ = decActsN blank a body n ++ [TAct.put a blank .left, TAct.keep a .right] := by
        rw [this]; simp

/-- プローブ（空白を書いて左）＋復元（読みを書き戻して右）はテープを変えない。 -/
theorem probe_restore_tape (blank : Fin sc) (tp : TapeConfiguration sc) {x : Fin sc}
    {l : List (Fin sc)} (hl : tp.left = x :: l) (hf : tp.focus = blank) :
    Tape.step blank (Tape.step blank tp blank .left)
        (Tape.step blank tp blank .left).focus .right = tp := by
  obtain ⟨L, f, R⟩ := tp
  simp only at hl hf
  subst hl; subst hf
  rfl

/-- プローブ＋復元はテープを変えない（カウンタが `0` のとき）。 -/
theorem probeRestore_id {mark : Fin sc} {S : Tps t sc}
    (hC : Tape.CounterView' blank mark (S a) 0) :
    runG blank [TAct.put a blank .left, TAct.keep a .right] S = S := by
  funext j
  by_cases hj : j = a
  · rw [hj]
    show applyG blank (applyG blank S (TAct.put a blank .left)) (TAct.keep a .right) a = S a
    rw [applyG_keep_self, applyG_put_self]
    obtain ⟨hl, hf, hr⟩ := hC
    simp only [List.replicate_zero, List.nil_append] at hl
    exact probe_restore_tape blank (S a) hl hf
  · show applyG blank (applyG blank S (TAct.put a blank .left)) (TAct.keep a .right) j = S j
    rw [applyG_ne blank _ _ hj, applyG_ne blank _ _ hj]

end DecLoop

/-! ## 8. 左向きコピーのループ（左端の番兵で止まる） -/

section CopyLoop

variable (i j : Fin t)

/-- 1 記号ぶん（`i` の読みを `j` に積み、`i` を左へ）。 -/
def copyRoundG : List (TAct t sc) := [TAct.copy j i .right, TAct.keep i .left]

/-- `n` 記号ぶん。 -/
def copyActsN : ℕ → List (TAct t sc)
  | 0 => []
  | n + 1 => copyRoundG i j ++ copyActsN n

@[simp] theorem copyActsN_length (n : ℕ) : (copyActsN (sc := sc) i j n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [copyActsN, List.length_append, ih]; simp [copyRoundG]; omega

theorem copyActsN_snoc (i j : Fin t) : ∀ n : ℕ,
    copyActsN (sc := sc) i j (n + 1) = copyActsN i j n ++ copyRoundG i j := by
  intro n
  induction n with
  | zero => simp [copyActsN]
  | succ n ih =>
      calc copyActsN (sc := sc) i j (n + 1 + 1)
          = copyRoundG i j ++ copyActsN i j (n + 1) := rfl
        _ = copyRoundG i j ++ (copyActsN i j n ++ copyRoundG i j) := by rw [ih]
        _ = (copyRoundG i j ++ copyActsN i j n) ++ copyRoundG i j := by
              rw [List.append_assoc]
        _ = copyActsN i j (n + 1) ++ copyRoundG i j := rfl

/-- 番兵で止まる左向きコピー：番兵セルもコピーして終わる。 -/
def copyProgSent (sent : Fin sc) : Prog (ActG t sc) (CondG t sc) :=
  Prog.seq (Prog.loop (i, sent) (TAct.copy j i (sc := sc) .right).act (ACT (TAct.keep i .left)))
    (seqActs (copyRoundG i j))

variable {i j}
variable {blank : Fin sc}

/-- ループ部分（番兵セルの手前まで）。 -/
theorem copyLoopSent_exec {sent : Fin sc} {w : List (Fin sc)} (hij : j ≠ i)
    (hs0 : w[0]? = some sent) (hfresh : ∀ m : ℕ, 0 < m → w[m]? ≠ some sent) :
    ∀ (b : ℕ) (S : Tps t sc), Tape.SeqView blank (S i) w b →
      ExecG Terminal blank
        (Prog.loop (i, sent) (TAct.copy j i (sc := sc) .right).act (ACT (TAct.keep i .left)))
        S (copyActsN i j b) := by
  intro b
  induction b with
  | zero =>
      intro S hS
      refine execG_loop_stop ?_
      have hf : w[0]? = some (S i).focus := hS.focus_eq
      have : (S i).focus = sent := by rw [hs0] at hf; exact (Option.some.inj hf).symm
      simp [condOfG, this]
  | succ b ih =>
      intro S hS
      have hf : w[b + 1]? = some (S i).focus := hS.focus_eq
      have hne : (S i).focus ≠ sent := by
        intro hc
        exact hfresh (b + 1) (by omega) (by rw [hf, hc])
      rw [copyActsN, copyRoundG]
      refine execG_loop_cont (a := TAct.copy j i .right) ?_ ?_ ?_
      · simp [condOfG, hne]
      · exact execG_act _ _
      · refine ih _ ?_
        have h1 : (applyG blank S (TAct.copy j i (sc := sc) .right)) i = S i :=
          applyG_ne blank S _ (Ne.symm hij)
        have h2 : (runG blank [TAct.keep i (sc := sc) .left]
            (applyG blank S (TAct.copy j i .right))) i
            = Tape.step blank (S i) (S i).focus .left := by
          show (applyG blank (applyG blank S (TAct.copy j i .right)) (TAct.keep i .left)) i = _
          rw [applyG_keep_self, h1]
        rw [h2]
        exact Tape.seq_move_left hS

/-- **左向きコピー全体**：番兵まで（番兵を含めて）`b + 1` 記号をコピーする。 -/
theorem copyProgSent_exec {sent : Fin sc} {w : List (Fin sc)} (hij : j ≠ i)
    (hs0 : w[0]? = some sent) (hfresh : ∀ m : ℕ, 0 < m → w[m]? ≠ some sent)
    (b : ℕ) (S : Tps t sc) (hS : Tape.SeqView blank (S i) w b) :
    ExecG Terminal blank (copyProgSent i j sent) S (copyActsN i j (b + 1)) := by
  have e1 := copyLoopSent_exec (Terminal := Terminal) hij hs0 hfresh b S hS
  have e2 := execG_seqActs (Terminal := Terminal) (blank := blank) (copyRoundG i j)
    (runG blank (copyActsN i j b) S)
  exact execG_of_eq (copyActsN_snoc i j b).symm (execG_seq e1 e2)

/-- **左端の番兵版**：先頭に本物の番兵 `leftSym`（実データではない、`w'` に現れない記号）
を置いた語 `leftSym :: w'` に対して、ループだけを回すと（末尾の追加ラウンドは無し）、
`leftSym` 自身は消費せずに `w'` の実データをちょうど `b` 個だけコピーして止まる。
`s`,`h` が定数でない場合の「左端まで」コピーはこちらを使う。 -/
theorem copyLoopSentL_exec {leftSym : Fin sc} {w' : List (Fin sc)} (hij : j ≠ i)
    (hfresh : leftSym ∉ w') (b : ℕ) (S : Tps t sc)
    (hS : Tape.SeqView blank (S i) (leftSym :: w') b) :
    ExecG Terminal blank
      (Prog.loop (i, leftSym) (TAct.copy j i (sc := sc) .right).act (ACT (TAct.keep i .left)))
      S (copyActsN i j b) :=
  copyLoopSent_exec (Terminal := Terminal) hij rfl
    (fun m hm hc => by
      obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      rw [List.getElem?_cons_succ] at hc
      obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hc
      exact hfresh (hget ▸ List.getElem_mem hlt))
    b S hS

end CopyLoop

/-! ## 9. 右向きコピーのループ（語の右端の空白で止まる） -/

section CopyLoopR

variable (i j : Fin t)

def copyRoundGR : List (TAct t sc) := [TAct.copy j i .right, TAct.keep i .right]

def copyActsR : ℕ → List (TAct t sc)
  | 0 => []
  | n + 1 => copyRoundGR i j ++ copyActsR n

@[simp] theorem copyActsR_length (n : ℕ) : (copyActsR (sc := sc) i j n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [copyActsR, List.length_append, ih]; simp [copyRoundGR]; omega

/-- 空白で止まる右向きコピー。 -/
def copyProgR (blank : Fin sc) : Prog (ActG t sc) (CondG t sc) :=
  Prog.loop (i, blank) (TAct.copy j i (sc := sc) .right).act (ACT (TAct.keep i .right))

variable {i j}
variable {blank : Fin sc}

theorem copyProgR_exec {w : List (Fin sc)} (hij : j ≠ i) (hbl : blank ∉ w) :
    ∀ (n b : ℕ) (S : Tps t sc), b + n = w.length →
      (n = 0 → (S i).focus = blank) → (0 < n → Tape.SeqView blank (S i) w b) →
      ExecG Terminal blank (copyProgR i j blank) S (copyActsR i j n) := by
  intro n
  induction n with
  | zero =>
      intro b S _ h0 _
      exact execG_loop_stop (by simp [condOfG, h0 rfl])
  | succ n ih =>
      intro b S hlen _ hpos
      have hS := hpos (by omega)
      have hf : w[b]? = some (S i).focus := hS.focus_eq
      have hne : (S i).focus ≠ blank := by
        intro hc
        refine hbl ?_
        obtain ⟨hb, hget⟩ := List.getElem?_eq_some_iff.1 hf
        exact hc ▸ hget ▸ List.getElem_mem hb
      rw [copyActsR, copyRoundGR]
      refine execG_loop_cont (a := TAct.copy j i .right) ?_ ?_ ?_
      · simp [condOfG, hne]
      · exact execG_act _ _
      · refine ih (b + 1) _ (by omega) ?_ ?_
        · intro hn0
          subst hn0
          have hend : b + 1 = w.length := by omega
          obtain ⟨tl, hr, htl⟩ := hS.right_eq
          have hdrop : w.drop (b + 1) = [] := List.drop_eq_nil_of_le (by omega)
          show (applyG blank (applyG blank S (TAct.copy j i .right))
              (TAct.keep i .right) i).focus = blank
          rw [applyG_keep_self,
            applyG_ne blank S (TAct.copy j i (sc := sc) .right) (Ne.symm hij), Tape.step_right]
          show (S i).right.headD blank = blank
          rw [hr, hdrop, List.nil_append]
          exact htl.headD
        · intro _
          show Tape.SeqView blank ((applyG blank (applyG blank S (TAct.copy j i .right))
            (TAct.keep i .right)) i) w (b + 1)
          rw [applyG_keep_self,
            applyG_ne blank S (TAct.copy j i (sc := sc) .right) (Ne.symm hij)]
          exact Tape.seq_move_right hS (by omega)

end CopyLoopR

/-! ## 10. スタックから逐次ビューへ（番兵まで歩いて 1 歩戻る） -/

section Settle

variable (i : Fin t)

/-- 左へ `n` 歩。 -/
def leftWalkG (n : ℕ) : List (TAct t sc) := List.replicate n (TAct.keep i .left)

@[simp] theorem leftWalkG_length (n : ℕ) : (leftWalkG (sc := sc) i n).length = n := by
  simp [leftWalkG]

/-- 積み終えたスタックを逐次ビューに直し、ヘッドを添字 `1` に置くプログラム。
番兵（`startSym`）を読むまで左へ歩き、1 歩右へ戻る。 -/
def settleProgG (blank sent : Fin sc) : Prog (ActG t sc) (CondG t sc) :=
  Prog.seq (ACT (TAct.put i blank .left))
    (Prog.seq (Prog.loop (i, sent) (TAct.keep i (sc := sc) .left).act Prog.skip)
      (ACT (TAct.keep i .right)))

variable {i}
variable {blank : Fin sc}

theorem leftWalkLoop_exec {sent : Fin sc} {W : List (Fin sc)}
    (hs0 : W[0]? = some sent) (hfresh : ∀ m : ℕ, 0 < m → W[m]? ≠ some sent) :
    ∀ (p : ℕ) (S : Tps t sc), Tape.SeqView blank (S i) W p →
      ExecG Terminal blank
        (Prog.loop (i, sent) (TAct.keep i (sc := sc) .left).act Prog.skip) S
        (leftWalkG i p) := by
  intro p
  induction p with
  | zero =>
      intro S hS
      refine execG_loop_stop ?_
      have hf : W[0]? = some (S i).focus := hS.focus_eq
      have : (S i).focus = sent := by rw [hs0] at hf; exact (Option.some.inj hf).symm
      simp [condOfG, this]
  | succ p ih =>
      intro S hS
      have hf : W[p + 1]? = some (S i).focus := hS.focus_eq
      have hne : (S i).focus ≠ sent := by
        intro hc
        exact hfresh (p + 1) (by omega) (by rw [hf, hc])
      have hrep : leftWalkG (sc := sc) i (p + 1)
          = TAct.keep i .left :: ([] ++ leftWalkG i p) := by
        simp only [leftWalkG, List.replicate_succ, List.nil_append]
      rw [hrep]
      refine execG_loop_cont (a := TAct.keep i .left) (L₁ := []) ?_ execG_skip ?_
      · simp [condOfG, hne]
      · refine ih _ ?_
        show Tape.SeqView blank ((applyG blank S (TAct.keep i .left)) i) W p
        rw [applyG_keep_self]
        exact Tape.seq_move_left hS

theorem leftWalkG_snoc (n : ℕ) :
    leftWalkG (sc := sc) i (n + 1) = leftWalkG i n ++ [TAct.keep i .left] := by
  simp [leftWalkG, List.replicate_succ']

/-- 左へ 1 歩・右へ 1 歩はテープを変えない（左文脈が空でなければ）。 -/
theorem keep_left_right_tape (blank : Fin sc) (tp : TapeConfiguration sc) {x : Fin sc}
    {l : List (Fin sc)} (hl : tp.left = x :: l) :
    Tape.step blank (Tape.step blank tp tp.focus .left)
        (Tape.step blank tp tp.focus .left).focus .right = tp := by
  obtain ⟨L, f, R⟩ := tp
  simp only at hl
  subst hl
  rfl

theorem keepLR_id {S : Tps t sc} {x : Fin sc} {l : List (Fin sc)}
    (h : (S i).left = x :: l) :
    runG blank [TAct.keep i .left, TAct.keep i .right] S = S := by
  funext m
  by_cases hm : m = i
  · rw [hm]
    show applyG blank (applyG blank S (TAct.keep i .left)) (TAct.keep i .right) i = S i
    rw [applyG_keep_self, applyG_keep_self]
    exact keep_left_right_tape blank (S i) h
  · show applyG blank (applyG blank S (TAct.keep i .left)) (TAct.keep i .right) m = S m
    rw [applyG_ne blank _ _ hm, applyG_ne blank _ _ hm]

/-- **`settle` のプログラム版**。動作列は元の `settle` に左 1 歩・右 1 歩が加わった形。 -/
theorem settleProgG_exec {sent : Fin sc} {S : Tps t sc} {aTop : Fin sc} {l : List (Fin sc)}
    (hst : Tape.StackView blank (S i) (aTop :: l))
    (hs0 : ((aTop :: l).reverse)[0]? = some sent)
    (hfresh : ∀ m : ℕ, 0 < m → ((aTop :: l).reverse)[m]? ≠ some sent) :
    ExecG Terminal blank (settleProgG i blank sent) S
      (TAct.put i blank .left :: (leftWalkG i l.length ++ [TAct.keep i .right])) := by
  have hseq : Tape.SeqView blank ((applyG blank S (TAct.put i blank .left)) i)
      ((aTop :: l).reverse) l.length := by
    rw [applyG_put_self]
    exact PatternTapes.stack_to_seq hst
  have e0 := execG_act (Terminal := Terminal) (blank := blank) (TAct.put i blank .left) S
  have e1 := leftWalkLoop_exec (Terminal := Terminal) hs0 hfresh l.length
    (applyG blank S (TAct.put i blank .left)) hseq
  have e2 := execG_act (Terminal := Terminal) (blank := blank) (TAct.keep i .right)
    (runG blank (leftWalkG i l.length) (applyG blank S (TAct.put i blank .left)))
  have hcomb := execG_seq e0 (execG_seq (by
      show ExecG Terminal blank _ (runG blank [TAct.put i blank (sc := sc) .left] S) _
      exact e1) e2)
  exact execG_of_eq (by simp) hcomb

end Settle

/-! ## 11. 12 本テープ版（`PalPeg.PatternTapes`）への実装 -/

namespace Twelve

open PalPeg.PatternTapes

variable {sc : ℕ} {Terminal : Type}

/-- 12 本版の動作を `TAct` へ。 -/
def lift12 : SAct sc → TAct 12 sc
  | .keep i m => .keep i m
  | .put i x m => .put i x m

theorem applyS_eq (blank : Fin sc) (S : Tapes sc) (a : SAct sc) :
    applyS blank S a = applyG blank S (lift12 a) := by
  cases a <;> rfl

theorem run_eq (blank : Fin sc) : ∀ (l : List (SAct sc)) (S : Tapes sc),
    run blank l S = runG blank (l.map lift12) S := by
  intro l
  induction l with
  | nil => intro S; rfl
  | cons a l ih => intro S; rw [run_cons, ih, List.map_cons, runG_cons, applyS_eq]

/-- コピー 1 周回は元の `copyRound` と同じ作用。 -/
theorem copyRoundG_run (blank : Fin sc) (i j : Fin 12) (S : Tapes sc) :
    runG blank (copyRoundG i j) S = run blank (copyRound i j S) S := rfl

/-- カウンタ駆動のコピーループは、カウンタテープ以外では元の `copyLoop` と同じ作用。 -/
theorem decCopy_run (blank : Fin sc) {cs i j : Fin 12} (hci : cs ≠ i) (hcj : cs ≠ j) :
    ∀ (n : ℕ) (S T : Tapes sc), (∀ l, l ≠ cs → T l = S l) →
      ∀ l, l ≠ cs →
        runG blank (decActsN blank cs (copyRoundG i j) n) T l
          = run blank (copyLoop blank i j n S) S l := by
  have huse : ∀ a ∈ copyRoundG (sc := sc) i j, cs ∉ a.uses := by
    intro a ha
    rcases List.mem_cons.1 ha with h | h
    · subst h; simp only [TAct.uses, List.mem_cons, List.not_mem_nil, or_false]
      exact fun hc => by rcases hc with hc | hc <;> [exact hcj hc; exact hci hc]
    · rcases List.mem_cons.1 h with h | h
      · subst h; simp only [TAct.uses, List.mem_cons, List.not_mem_nil, or_false]
        exact hci
      · simp at h
  intro n
  induction n with
  | zero => intro S T hST l hl; exact hST l hl
  | succ n ih =>
      intro S T hST l hl
      rw [decActsN, runG_append, copyLoop, run_append]
      refine ih _ _ (fun m hm => ?_) l hl
      have hD : ∀ m, m ≠ cs →
          (runG blank (decRound blank cs (copyRoundG i j)) T) m
            = (runG blank (copyRoundG i j) T) m := by
        intro m hm
        rw [show decRound blank cs (copyRoundG i j)
            = [TAct.put cs blank .left, TAct.put cs blank .stay] ++ copyRoundG i j from rfl,
          runG_append]
        refine runG_local blank cs (copyRoundG i j) T _ huse (fun l' hl' => ?_) m hm
        show applyG blank (applyG blank T (TAct.put cs blank .left))
          (TAct.put cs blank .stay) l' = T l'
        rw [applyG_ne blank _ _ hl', applyG_ne blank _ _ hl']
      rw [hD m hm]
      exact runG_local blank cs (copyRoundG i j) S T huse hST m hm

/-! ### カウンタ駆動のコピー（ミラーあり）

`s`,`h` は構成の定数ではない（段幅は 2 冪を渡り、切り分け `s` は入力から決まる）ので、
`copyLoop` の回数をそのまま展開することはできない。カウンタテープ `cs`（値 `s`）を
実際に 1 ずつ消費しながらコピーし、消費した分をミラーのカウンタ `mir`（`SetupPre` では
未使用の `sC2` を使う）に転写しておく（`GSScanTapes.perDown`/`perUp` が `tC1`/`tC2` で
やっているのと同じ手筋）。あとで `xfer1` で `mir → cs` に戻せば `cs` の値も復元できる。 -/

/-- ミラー付きの 1 周回の本体（`cs` 自身には触れない）。 -/
def copyRoundMirror (blank : Fin sc) (i j mir : Fin 12) : List (TAct 12 sc) :=
  copyRoundG i j ++ [TAct.put mir blank .right]

theorem decCopyMirror_run (blank mark : Fin sc) {cs mir i j : Fin 12}
    (hci : cs ≠ i) (hcj : cs ≠ j) (hcm : cs ≠ mir) (hmi : mir ≠ i) (hmj : mir ≠ j) :
    ∀ (n : ℕ) (S T : Tapes sc), (∀ l, l ≠ cs → l ≠ mir → T l = S l) →
      ∀ l, l ≠ cs → l ≠ mir →
        runG blank (decActsN blank cs (copyRoundMirror blank i j mir) n) T l
          = run blank (copyLoop blank i j n S) S l := by
  have huse : ∀ a ∈ copyRoundG (sc := sc) i j, cs ∉ a.uses ∧ mir ∉ a.uses := by
    intro a ha
    rcases List.mem_cons.1 ha with h | h
    · subst h
      refine ⟨?_, ?_⟩ <;>
        simp only [TAct.uses, List.mem_cons, List.not_mem_nil, or_false] <;>
        exact fun hc => by
          rcases hc with hc | hc
          · first | exact hcj hc | exact hmj hc
          · first | exact hci hc | exact hmi hc
    · rcases List.mem_cons.1 h with h | h
      · subst h
        refine ⟨?_, ?_⟩ <;> simp only [TAct.uses, List.mem_cons, List.not_mem_nil, or_false]
        · exact hci
        · exact hmi
      · simp at h
  have hmirNe : ∀ (X : Tps 12 sc) (m : Fin 12), m ≠ mir →
      runG blank (copyRoundMirror blank i j mir) X m = runG blank (copyRoundG i j) X m := by
    intro X m hm
    rw [copyRoundMirror, runG_append]
    exact applyG_ne blank _ _ hm
  intro n
  induction n with
  | zero => intro S T hST l hl1 hl2; exact hST l hl1 hl2
  | succ n ih =>
      intro S T hST l hl1 hl2
      rw [decActsN, runG_append, copyLoop, run_append]
      refine ih _ _ (fun m hm1 hm2 => ?_) l hl1 hl2
      have hD : ∀ m, m ≠ cs → m ≠ mir →
          (runG blank (decRound blank cs (copyRoundMirror blank i j mir)) T) m
            = (runG blank (copyRoundG i j) T) m := by
        intro m hm hm'
        rw [show decRound blank cs (copyRoundMirror blank i j mir)
            = [TAct.put cs blank .left, TAct.put cs blank .stay] ++ copyRoundMirror blank i j mir
            from rfl, runG_append, hmirNe _ m hm']
        refine runG_local2 blank cs mir (copyRoundG i j) T _ (fun a ha => huse a ha)
          (fun l' hl1' hl2' => ?_) m hm hm'
        show applyG blank (applyG blank T (TAct.put cs blank .left))
          (TAct.put cs blank .stay) l' = T l'
        rw [applyG_ne blank _ _ hl1', applyG_ne blank _ _ hl1']
      rw [hD m hm1 hm2]
      exact runG_local2 blank cs mir (copyRoundG i j) S T (fun a ha => huse a ha) hST m hm1 hm2

theorem decCopyMirror_counter (blank mark : Fin sc) {cs mir i j : Fin 12}
    (hcm : cs ≠ mir) (hmi : mir ≠ i) (hmj : mir ≠ j) :
    ∀ (n : ℕ) (T : Tapes sc) (m0 : ℕ), Tape.CounterView' blank mark (T mir) m0 →
      Tape.CounterView' blank mark
        (runG blank (decActsN blank cs (copyRoundMirror blank i j mir) n) T mir) (m0 + n) := by
  have huseI : ∀ a ∈ copyRoundG (sc := sc) i j, mir ∉ a.uses := by
    intro a ha
    rcases List.mem_cons.1 ha with h | h
    · subst h; simp only [TAct.uses, List.mem_cons, List.not_mem_nil, or_false]
      exact fun hc => by rcases hc with hc | hc <;> [exact hmj hc; exact hmi hc]
    · rcases List.mem_cons.1 h with h | h
      · subst h; simp only [TAct.uses, List.mem_cons, List.not_mem_nil, or_false]; exact hmi
      · simp at h
  intro n
  induction n with
  | zero => intro T m0 hm; rw [decActsN]; simpa using hm
  | succ n ih =>
      intro T m0 hm
      rw [decActsN, runG_append]
      have hstep : Tape.CounterView' blank mark
          ((runG blank (decRound blank cs (copyRoundMirror blank i j mir)) T) mir) (m0 + 1) := by
        have heq : decRound blank cs (copyRoundMirror blank i j mir)
            = ([TAct.put cs blank .left, TAct.put cs blank .stay] ++ copyRoundG i j)
              ++ [TAct.put mir blank .right] := by
          simp [decRound, copyRoundMirror]
        rw [heq, runG_append, runG_append]
        have hpm : (runG blank [TAct.put mir blank (sc := sc) .right]
            (runG blank (copyRoundG i j)
              (runG blank [TAct.put cs blank .left, TAct.put cs blank .stay] T))) mir
            = Tape.step blank ((runG blank (copyRoundG i j)
                (runG blank [TAct.put cs blank .left, TAct.put cs blank .stay] T)) mir) blank
              .right := by
          simp only [runG_cons, runG_nil, applyG_put_self]
        rw [hpm]
        refine Tape.counter'_inc ?_
        have h1 : (runG blank [TAct.put cs blank (sc := sc) .left, TAct.put cs blank .stay] T) mir
            = T mir := by
          simp only [runG_cons, runG_nil]
          rw [applyG_ne blank _ _ hcm.symm, applyG_ne blank _ _ hcm.symm]
        have h2 : (runG blank (copyRoundG i j)
            (runG blank [TAct.put cs blank (sc := sc) .left, TAct.put cs blank .stay] T)) mir
            = (runG blank [TAct.put cs blank (sc := sc) .left, TAct.put cs blank .stay] T) mir :=
          runG_untouched blank mir (copyRoundG i j) _
            (fun a ha hc => huseI a ha (by cases a <;> simp_all [TAct.uses] <;> tauto))
        rw [h2, h1]; exact hm
      rw [show m0 + (n + 1) = (m0 + 1) + n from by ring]
      exact ih _ (m0 + 1) hstep

/-- 番兵駆動のコピーループも、（カウンタテープ以外で一致する状態から）
元の `copyLoop` と同じ作用。 -/
theorem copyActsN_run (blank : Fin sc) {cs i j : Fin 12} (hci : cs ≠ i) (hcj : cs ≠ j) :
    ∀ (n : ℕ) (S T : Tapes sc), (∀ l, l ≠ cs → T l = S l) →
      ∀ l, l ≠ cs →
        runG blank (copyActsN i j n) T l = run blank (copyLoop blank i j n S) S l := by
  have huse : ∀ a ∈ copyRoundG (sc := sc) i j, cs ∉ a.uses := by
    intro a ha
    rcases List.mem_cons.1 ha with h | h
    · subst h; simp only [TAct.uses, List.mem_cons, List.not_mem_nil, or_false]
      exact fun hc => by rcases hc with hc | hc <;> [exact hcj hc; exact hci hc]
    · rcases List.mem_cons.1 h with h | h
      · subst h; simp only [TAct.uses, List.mem_cons, List.not_mem_nil, or_false]
        exact hci
      · simp at h
  intro n
  induction n with
  | zero => intro S T hST l hl; exact hST l hl
  | succ n ih =>
      intro S T hST l hl
      rw [copyActsN, runG_append, copyLoop, run_append]
      refine ih _ _ (fun m hm => ?_) l hl
      exact runG_local blank cs (copyRoundG i j) S T huse hST m hm

/-- 静的な動作列（`lift12` の像）は元の作用と一致する。 -/
theorem map_run_local (blank : Fin sc) {cs : Fin 12} (l : List (SAct sc))
    (huse : ∀ a ∈ l, cs ∉ (lift12 a).uses) (S T : Tapes sc)
    (hST : ∀ m, m ≠ cs → T m = S m) :
    ∀ m, m ≠ cs → runG blank (l.map lift12) T m = run blank l S m := by
  intro m hm
  rw [run_eq]
  exact runG_local blank cs (l.map lift12) S T
    (by intro a ha; obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha; exact huse b hb) hST m hm

/-- `settle` のプログラム版の動作列は元の `settle` と同じ作用。 -/
theorem settleActs_run (blank : Fin sc) (i : Fin 12) (n : ℕ) (S : Tapes sc)
    {x : Fin sc} {l : List (Fin sc)}
    (h : ((run blank (settle blank i n) S) i).left = x :: l) :
    runG blank (TAct.put i blank .left :: (leftWalkG i (n + 1) ++ [TAct.keep i .right])) S
      = run blank (settle blank i n) S := by
  have hlist : TAct.put i blank (sc := sc) .left :: (leftWalkG i (n + 1) ++ [TAct.keep i .right])
      = (TAct.put i blank .left :: leftWalkG i n) ++ [TAct.keep i .left, TAct.keep i .right] := by
    rw [leftWalkG_snoc]; simp
  have hpre : runG blank (TAct.put i blank (sc := sc) .left :: leftWalkG i n) S
      = run blank (settle blank i n) S := by
    rw [settle, run_eq, List.map_cons]
    congr 1
    simp [leftWalk, leftWalkG, List.map_replicate, lift12]
  rw [hlist, runG_append, hpre]
  exact keepLR_id h

/-! ### 単進カウンタの転送 -/

/-- `xfer2` の 1 周回本体（プローブ 2 動作を除いた残り）。 -/
def incBody2 (blank : Fin sc) (b c : Fin 12) : List (TAct 12 sc) :=
  [TAct.put b blank .right, TAct.put c blank .right]

/-- `xfer1` の 1 周回本体。 -/
def incBody1 (blank : Fin sc) (b : Fin 12) : List (TAct 12 sc) := [TAct.put b blank .right]

theorem xfer2_map (blank : Fin sc) (a b c : Fin 12) : ∀ n : ℕ,
    decActsN blank a (incBody2 blank b c) n = (xfer2 blank a b c n).map lift12 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [decActsN, xfer2, List.map_append, ih]; rfl

theorem xfer1_map (blank : Fin sc) (a b : Fin 12) : ∀ n : ℕ,
    decActsN blank a (incBody1 blank b) n = (xfer1 blank a b n).map lift12 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [decActsN, xfer1, List.map_append, ih]; rfl

/-- `xfer2` のプログラムと動作列。 -/
def xfer2Prog (blank mark : Fin sc) (a b c : Fin 12) : Prog (ActG 12 sc) (CondG 12 sc) :=
  decLoopProg blank a (incBody2 blank b c) mark

def xfer2Acts (blank : Fin sc) (a b c : Fin 12) (n : ℕ) : List (TAct 12 sc) :=
  decActsN blank a (incBody2 blank b c) n ++ [TAct.put a blank .left, TAct.keep a .right]

def xfer1Prog (blank mark : Fin sc) (a b : Fin 12) : Prog (ActG 12 sc) (CondG 12 sc) :=
  decLoopProg blank a (incBody1 blank b) mark

def xfer1Acts (blank : Fin sc) (a b : Fin 12) (n : ℕ) : List (TAct 12 sc) :=
  decActsN blank a (incBody1 blank b) n ++ [TAct.put a blank .left, TAct.keep a .right]

@[simp] theorem xfer2Acts_length (blank : Fin sc) (a b c : Fin 12) (n : ℕ) :
    (xfer2Acts blank a b c n).length = 4 * n + 2 := by
  rw [xfer2Acts, List.length_append, decActsN_length]
  simp [incBody2]

@[simp] theorem xfer1Acts_length (blank : Fin sc) (a b : Fin 12) (n : ℕ) :
    (xfer1Acts blank a b n).length = 3 * n + 2 := by
  rw [xfer1Acts, List.length_append, decActsN_length]
  simp [incBody1]

variable {blank mark : Fin sc}

theorem xfer2Prog_exec {a b c : Fin 12} (hne : mark ≠ blank) (hab : a ≠ b) (hac : a ≠ c)
    (n : ℕ) (S : Tapes sc) (hC : Tape.CounterView' blank mark (S a) n) :
    ExecG Terminal blank (xfer2Prog blank mark a b c) S (xfer2Acts blank a b c n) :=
  decLoopProg_exec hne
    (by
      intro x hx
      rcases List.mem_cons.1 hx with h | h
      · subst h; exact Ne.symm hab
      · rcases List.mem_cons.1 h with h | h
        · subst h; exact Ne.symm hac
        · simp at h)
    n S hC

theorem xfer1Prog_exec {a b : Fin 12} (hne : mark ≠ blank) (hab : a ≠ b)
    (n : ℕ) (S : Tapes sc) (hC : Tape.CounterView' blank mark (S a) n) :
    ExecG Terminal blank (xfer1Prog blank mark a b) S (xfer1Acts blank a b n) :=
  decLoopProg_exec hne
    (by
      intro x hx
      rcases List.mem_cons.1 hx with h | h
      · subst h; exact Ne.symm hab
      · simp at h)
    n S hC

/-- `xfer2` の動作列はテープに同じ作用（末尾のプローブ＋復元は恒等）。 -/
theorem xfer2Acts_run {a b c : Fin 12} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (n : ℕ)
    (S : Tapes sc) {y z : ℕ} (hC : Tape.CounterView' blank mark (S a) n)
    (hb : Tape.CounterView' blank mark (S b) y) (hc : Tape.CounterView' blank mark (S c) z) :
    runG blank (xfer2Acts blank a b c n) S = run blank (xfer2 blank a b c n) S := by
  obtain ⟨g1, -, -⟩ := xfer2_spec (blank := blank) (mark := mark) hab hac hbc n S 0 y z
    (by simpa using hC) hb hc
  rw [xfer2Acts, runG_append, xfer2_map, ← run_eq]
  exact probeRestore_id (mark := mark) g1

theorem xfer1Acts_run {a b : Fin 12} (hab : a ≠ b) (n : ℕ) (S : Tapes sc) {y : ℕ}
    (hC : Tape.CounterView' blank mark (S a) n)
    (hb : Tape.CounterView' blank mark (S b) y) :
    runG blank (xfer1Acts blank a b n) S = run blank (xfer1 blank a b n) S := by
  obtain ⟨g1, -⟩ := xfer1_spec (blank := blank) (mark := mark) hab n S 0 y
    (by simpa using hC) hb
  rw [xfer1Acts, runG_append, xfer1_map, ← run_eq]
  exact probeRestore_id (mark := mark) g1

/-! ### `sAn` に `k * p₁` を作るループ -/

/-- 1 周回のプログラム。 -/
def kRoundProg (blank mark : Fin sc) : Prog (ActG 12 sc) (CondG 12 sc) :=
  Prog.seq (xfer2Prog blank mark sC1 sAn sC2) (xfer1Prog blank mark sC2 sC1)

/-- 1 周回の動作列（プローブ＋復元が 2 組ぶん増える）。 -/
def kRoundActs (blank : Fin sc) (p : ℕ) : List (TAct 12 sc) :=
  xfer2Acts blank sC1 sAn sC2 p ++ xfer1Acts blank sC2 sC1 p

/-- `k` 周回のプログラム（`k` は構成の定数なので展開してよい）。 -/
def kLoopProg (blank mark : Fin sc) : ℕ → Prog (ActG 12 sc) (CondG 12 sc)
  | 0 => Prog.skip
  | m + 1 => Prog.seq (kRoundProg blank mark) (kLoopProg blank mark m)

def kLoopActs (blank : Fin sc) (p : ℕ) : ℕ → List (TAct 12 sc)
  | 0 => []
  | m + 1 => kRoundActs blank p ++ kLoopActs blank p m

@[simp] theorem kRoundActs_length (blank : Fin sc) (p : ℕ) :
    (kRoundActs blank p).length = 7 * p + 4 := by
  rw [kRoundActs, List.length_append, xfer2Acts_length, xfer1Acts_length]; omega

@[simp] theorem kLoopActs_length (blank : Fin sc) (p m : ℕ) :
    (kLoopActs blank p m).length = m * (7 * p + 4) := by
  induction m with
  | zero => simp [kLoopActs]
  | succ m ih => rw [kLoopActs, List.length_append, ih, kRoundActs_length]; ring

theorem kRoundActs_run {S : Tapes sc} {p y : ℕ}
    (h1 : Tape.CounterView' blank mark (S sC1) p)
    (h2 : Tape.CounterView' blank mark (S sC2) 0)
    (h3 : Tape.CounterView' blank mark (S sAn) y) :
    runG blank (kRoundActs blank p) S = run blank (kRound blank S) S := by
  have hp : cval (S sC1) = p := cval_eq h1
  obtain ⟨g1, g2, g3⟩ := xfer2_spec (blank := blank) (mark := mark) (a := sC1) (b := sAn)
    (c := sC2) (by decide) (by decide) (by decide) p S 0 y 0 (by simpa using h1) h3 h2
  rw [kRoundActs, runG_append,
    xfer2Acts_run (mark := mark) (by decide) (by decide) (by decide) p S h1 h3 h2,
    xfer1Acts_run (mark := mark) (by decide) p _ (by simpa using g3) g1,
    kRound, hp, run_append]

theorem kRoundProg_exec {S : Tapes sc} {p y : ℕ} (hne : mark ≠ blank)
    (h1 : Tape.CounterView' blank mark (S sC1) p)
    (h2 : Tape.CounterView' blank mark (S sC2) 0)
    (h3 : Tape.CounterView' blank mark (S sAn) y) :
    ExecG Terminal blank (kRoundProg blank mark) S (kRoundActs blank p) := by
  obtain ⟨g1, -, g3⟩ := xfer2_spec (blank := blank) (mark := mark) (a := sC1) (b := sAn)
    (c := sC2) (by decide) (by decide) (by decide) p S 0 y 0 (by simpa using h1) h3 h2
  have e1 := xfer2Prog_exec (Terminal := Terminal) (a := sC1) (b := sAn) (c := sC2) hne
    (by decide) (by decide) p S h1
  have e2 := xfer1Prog_exec (Terminal := Terminal) (a := sC2) (b := sC1) hne (by decide) p
    (run blank (xfer2 blank sC1 sAn sC2 p) S) (by simpa using g3)
  rw [← xfer2Acts_run (mark := mark) (by decide) (by decide) (by decide) p S h1 h3 h2] at e2
  exact execG_seq e1 e2

theorem kLoopProg_exec (hne : mark ≠ blank) : ∀ (m : ℕ) (S : Tapes sc) (p y : ℕ),
    Tape.CounterView' blank mark (S sC1) p →
    Tape.CounterView' blank mark (S sC2) 0 →
    Tape.CounterView' blank mark (S sAn) y →
    ExecG Terminal blank (kLoopProg blank mark m) S (kLoopActs blank p m)
      ∧ runG blank (kLoopActs blank p m) S = run blank (kLoop blank m S) S := by
  intro m
  induction m with
  | zero => intro S p y _ _ _; exact ⟨execG_skip, rfl⟩
  | succ m ih =>
      intro S p y h1 h2 h3
      obtain ⟨e1, e2, e3, -, -⟩ := kRound_spec h1 h2 h3
      have hrun := kRoundActs_run (mark := mark) h1 h2 h3
      obtain ⟨f1, f2⟩ := ih (run blank (kRound blank S) S) p (y + p) e1 e2 e3
      refine ⟨?_, ?_⟩
      · refine execG_seq (kRoundProg_exec (Terminal := Terminal) hne h1 h2 h3) ?_
        rw [hrun]; exact f1
      · rw [kLoopActs, runG_append, hrun, f2, kLoop, run_append]

/-! ### 準備フェーズの導入部（`pushBoth`） -/

/-- `pushBoth` のプログラム版：`sU`, `sP` に同じ記号を積む（ループなし、固定長 2）。 -/
def pushBothProg (a : Fin sc) : Prog (ActG 12 sc) (CondG 12 sc) :=
  Prog.seq (ACT (TAct.put sU a .right)) (ACT (TAct.put sP a .right))

/-- `pushBoth` の動作列そのものが `lift12` の像。 -/
def pushBothActs (a : Fin sc) : List (TAct 12 sc) :=
  [TAct.put sU a .right, TAct.put sP a .right]

theorem pushBothActs_run (blank a : Fin sc) (S : Tapes sc) :
    runG blank (pushBothActs a) S = run blank (pushBoth a) S := by
  rw [pushBoth, run_eq]; rfl

theorem pushBothProg_exec (a : Fin sc) (S : Tapes sc) :
    ExecG Terminal blank (pushBothProg a) S (pushBothActs a) :=
  execG_of_eq rfl (execG_seq (execG_act _ S) (execG_act _ _))

/-! ### 番兵無しの左向きコピー（回数は `SetupPre` から決まる定数として展開する） -/

/-- `copyActsN` の作用は元の `copyLoop` と（`cs` などの補助を使わずに）そのまま一致する。
`s`/`h - s` は構成の定数なので `kLoopProg` の `k` と同じ扱いで展開してよい。 -/
theorem copyActsN_run' (blank : Fin sc) (i j : Fin 12) :
    ∀ (n : ℕ) (S : Tapes sc),
      runG blank (copyActsN i j n) S = run blank (copyLoop blank i j n S) S := by
  intro n
  induction n with
  | zero => intro S; rfl
  | succ n ih =>
      intro S
      rw [copyActsN, runG_append, copyRoundG_run, copyLoop, run_append, ih]

/-! ### 準備フェーズの合成プログラム -/

/-- **準備フェーズ全体のプログラム版**。`s`（`sU` へのコピー数）と `hms`（`sP` へのコピー数、
呼び出し側は `h - s` を渡す）は `k` と同じく構成の定数として展開する（回数はテープの
境界を読まず、`SetupPre` の `s`・`h` からあらかじめ決まる）。 -/
def setupProg (blank startSym endSym mark : Fin sc) (s hms k : ℕ) :
    Prog (ActG 12 sc) (CondG 12 sc) :=
  Prog.seq (pushBothProg startSym)
    (Prog.seq (seqActs (copyActsN sIn sU s))
      (Prog.seq (seqActs (copyActsN sIn sP hms))
        (Prog.seq (pushBothProg endSym)
          (Prog.seq
            (seqActs
              (TAct.put sU blank .left :: (leftWalkG sU (s + 1) ++ [TAct.keep sU .right])))
            (Prog.seq
              (seqActs
                (TAct.put sP blank .left :: (leftWalkG sP (hms + 1) ++ [TAct.keep sP .right])))
              (kLoopProg blank mark k))))))

/-- `setupProg` が実際に実行する `TAct` の動作列。 -/
def setupProgActs (blank startSym endSym : Fin sc) (s hms k p₁ : ℕ) : List (TAct 12 sc) :=
  pushBothActs startSym ++
    (copyActsN sIn sU s ++
      (copyActsN sIn sP hms ++
        (pushBothActs endSym ++
          ((TAct.put sU blank .left :: (leftWalkG sU (s + 1) ++ [TAct.keep sU .right])) ++
            ((TAct.put sP blank .left :: (leftWalkG sP (hms + 1) ++ [TAct.keep sP .right])) ++
              kLoopActs blank p₁ k)))))

/-- **主定理**：`setupProg` はちょうど `setupProgActs` を実行し、その `TAct` レベルの
作用は元の `setupProgram`（`SAct` レベル）の作用とテープ状態として一致する
（＝トレースは `setupProgram` の動作列とちょうど対応する）。回数 `s`,`h - s` は
テープの境界を調べずに済む構成の定数として渡す。 -/
theorem setupProg_exec {startSym endSym : Fin sc} {s h p₁ r k : ℕ} {w Text : List (Fin sc)}
    {S : Tapes sc} {leftSym : Fin sc} (H : SetupPre blank mark leftSym s h p₁ r w Text S) (hne : mark ≠ blank) :
    ExecG Terminal blank (setupProg blank startSym endSym mark s (h - s) k) S
        (setupProgActs blank startSym endSym s (h - s) k p₁) ∧
      runG blank (setupProgActs blank startSym endSym s (h - s) k p₁) S
        = run blank (setupProgram blank startSym endSym k S) S := by
  obtain ⟨hpos, hle, hcut, hIn, hU, hP, _hT, _hX2, hCs, hC1, hC2, _hAp, hAn, _hRp, _hRn⟩ := H
  -- フェーズ 1
  set S₁ := run blank (pushBoth startSym) S with hS1
  have p1U : Tape.StackView blank (S₁ sU) [startSym] := by
    rw [hS1, pushBoth_U]; exact Tape.push_spec hU startSym
  have p1P : Tape.StackView blank (S₁ sP) [startSym] := by
    rw [hS1, pushBoth_P]; exact Tape.push_spec hP startSym
  have p1ne : ∀ j : Fin 12, j ≠ sU → j ≠ sP → S₁ j = S j := by
    intro j hu hp; rw [hS1]; exact pushBoth_ne blank startSym hu hp S
  -- フェーズ 2
  have hcs : cval (S₁ sCs) = s := by
    rw [p1ne sCs (by decide) (by decide)]; exact cval_eq hCs
  set S₂ := run blank (copyLoop blank sIn sU s S₁) S₁ with hS2
  have p2 : Tape.SeqView blank (S₂ sIn) (leftSym :: w.take h) (h - s) ∧
      Tape.StackView blank (S₂ sU)
        ((((leftSym :: w.take h).take (h + 1)).drop (h + 1 - s)) ++ [startSym]) := by
    rw [hS2]
    exact copyLoop_spec blank (i := sIn) (j := sU) (by decide) s h S₁ (leftSym :: w.take h)
      [startSym] (by omega) (by rw [p1ne sIn (by decide) (by decide)]; exact hIn) p1U
  have p2ne : ∀ j : Fin 12, j ≠ sIn → j ≠ sU → S₂ j = S₁ j := by
    intro j hi hu; rw [hS2]; exact copyLoop_untouched blank hi hu _ _
  have p2U : Tape.StackView blank (S₂ sU) ((w.take h).drop (h - s) ++ [startSym]) := by
    have := p2.2
    rwa [List.take_of_length_le (by
        simp only [List.length_cons, List.length_take]; omega),
      show h + 1 - s = (h - s) + 1 from by omega, List.drop_succ_cons] at this
  -- フェーズ 3
  have hn3 : (S₂ sIn).left.length = h - s := by
    rw [p2.1.left_eq]
    simp only [List.length_reverse, List.length_take, List.length_cons]
    omega
  set S₃ := run blank (copyLoop blank sIn sP (h - s) S₂) S₂ with hS3
  have p3 : Tape.SeqView blank (S₃ sIn) (leftSym :: w.take h) (h - s - (h - s)) ∧
      Tape.StackView blank (S₃ sP)
        ((((leftSym :: w.take h).take (h - s + 1)).drop (h - s + 1 - (h - s))) ++ [startSym]) := by
    rw [hS3]
    exact copyLoop_spec blank (i := sIn) (j := sP) (by decide) (h - s) (h - s) S₂
      (leftSym :: w.take h) [startSym] (by omega) p2.1
      (by rw [p2ne sP (by decide) (by decide)]; exact p1P)
  have p3ne : ∀ j : Fin 12, j ≠ sIn → j ≠ sP → S₃ j = S₂ j := by
    intro j hi hp; rw [hS3]; exact copyLoop_untouched blank hi hp _ _
  have p3P : Tape.StackView blank (S₃ sP) (w.take (h - s) ++ [startSym]) := by
    have := p3.2
    rwa [show h - s + 1 - (h - s) = 1 from by omega, List.take_succ_cons,
      List.drop_succ_cons, List.drop_zero, List.take_take,
      Nat.min_eq_left (by omega : h - s ≤ h)] at this
  -- フェーズ 4
  set S₄ := run blank (pushBoth endSym) S₃ with hS4
  have p4U : Tape.StackView blank (S₄ sU) (endSym :: ((w.take h).drop (h - s) ++ [startSym])) := by
    rw [hS4, pushBoth_U]
    exact Tape.push_spec (by rw [p3ne sU (by decide) (by decide)]; exact p2U) endSym
  have p4P : Tape.StackView blank (S₄ sP) (endSym :: (w.take (h - s) ++ [startSym])) := by
    rw [hS4, pushBoth_P]; exact Tape.push_spec p3P endSym
  have p4ne : ∀ j : Fin 12, j ≠ sU → j ≠ sP → S₄ j = S₃ j := by
    intro j hu hp; rw [hS4]; exact pushBoth_ne blank endSym hu hp S₃
  -- フェーズ 5・6：`settle` の前提（積んだ段数）と `.left` の非空性
  have hxlen : (w.take h).length = h := by simp only [List.length_take]; omega
  have hulen : ((w.take h).drop (h - s)).length = s := by
    rw [List.length_drop, hxlen]; omega
  have hvlen : (w.take (h - s)).length = h - s := by
    simp only [List.length_take]; omega
  have hlen5 : (S₄ sU).left.length - 2 = s := by
    rw [p4U.left_eq]
    simp only [List.length_cons, List.length_append, List.length_nil, hulen]; omega
  have hlen6 : (S₄ sP).left.length - 2 = h - s := by
    rw [p4P.left_eq]
    simp only [List.length_cons, List.length_append, List.length_nil, hvlen]; omega
  have hs5 := settle_spec blank sU (n := s) p4U (by
    simp only [List.length_cons, List.length_append, List.length_nil, hulen])
  have hxl5 : ∃ x l, ((run blank (settle blank sU s) S₄) sU).left = x :: l := by
    have hlenL : ((run blank (settle blank sU s) S₄) sU).left.length = 1 := by
      rw [hs5.left_eq, List.length_reverse, List.length_take, Nat.min_eq_left (by
        have := hs5.lt; omega)]
    generalize hL : ((run blank (settle blank sU s) S₄) sU).left = L at hlenL ⊢
    cases L with
    | nil => simp at hlenL
    | cons x l => exact ⟨x, l, rfl⟩
  obtain ⟨x5, l5, hxl5⟩ := hxl5
  set S₅ := run blank (settle blank sU s) S₄ with hS5
  have p5ne : ∀ j : Fin 12, j ≠ sU → S₅ j = S₄ j := by
    intro j hu; rw [hS5]; exact settle_untouched blank hu _ _
  have hp4P' : Tape.StackView blank (S₅ sP) (endSym :: (w.take (h - s) ++ [startSym])) := by
    rw [p5ne sP (by decide)]; exact p4P
  have hs6 := settle_spec blank sP (n := h - s) hp4P' (by
    simp only [List.length_cons, List.length_append, List.length_nil, hvlen])
  have hxl6 : ∃ x l, ((run blank (settle blank sP (h - s)) S₅) sP).left = x :: l := by
    have hlenL : ((run blank (settle blank sP (h - s)) S₅) sP).left.length = 1 := by
      rw [hs6.left_eq, List.length_reverse, List.length_take, Nat.min_eq_left (by
        have := hs6.lt; omega)]
    generalize hL : ((run blank (settle blank sP (h - s)) S₅) sP).left = L at hlenL ⊢
    cases L with
    | nil => simp at hlenL
    | cons x l => exact ⟨x, l, rfl⟩
  obtain ⟨x6, l6, hxl6⟩ := hxl6
  set S₆ := run blank (settle blank sP (h - s)) S₅ with hS6
  have p6ne : ∀ j : Fin 12, j ≠ sP → S₆ j = S₅ j := by
    intro j hp; rw [hS6]; exact settle_untouched blank hp _ _
  -- `sC1`,`sC2`,`sAn` は 6 段のいずれにも触れられない
  -- `setupProgram` の各段は元のフォーミュラ（`cval`／`.left.length`）を使うので、
  -- それが `s`／`h - s` に一致することを確認しておく
  have hcount2 : cval (S₁ sCs) = s := hcs
  have hcount3 : (S₂ sIn).left.length = h - s := by rw [hn3]
  have hlen6' : (S₅ sP).left.length - 2 = h - s := by
    rw [p5ne sP (by decide)]; exact hlen6
  have hkeep : ∀ j : Fin 12, j ≠ sU → j ≠ sP → j ≠ sIn → S₆ j = S j := by
    intro j hu hp hi
    rw [p6ne j hp, p5ne j hu, p4ne j hu hp, p3ne j hi hp, p2ne j hi hu, p1ne j hu hp]
  have hC1' : Tape.CounterView' blank mark (S₆ sC1) p₁ := by
    rw [hkeep sC1 (by decide) (by decide) (by decide)]; exact hC1
  have hC2' : Tape.CounterView' blank mark (S₆ sC2) 0 := by
    rw [hkeep sC2 (by decide) (by decide) (by decide)]; exact hC2
  have hAn' : Tape.CounterView' blank mark (S₆ sAn) 0 := by
    rw [hkeep sAn (by decide) (by decide) (by decide)]; exact hAn
  obtain ⟨e7, e7run⟩ := kLoopProg_exec (Terminal := Terminal) hne k S₆ p₁ 0 hC1' hC2' hAn'
  -- 各段を「直前の段の結果テープ」の上で確認する（`runG` を入れ子のまま扱う）
  have hR1 : runG blank (pushBothActs startSym) S = S₁ := pushBothActs_run blank startSym S
  have hR2 : runG blank (copyActsN sIn sU s) S₁ = S₂ := by
    rw [hS2]; exact copyActsN_run' blank sIn sU s S₁
  have hR3 : runG blank (copyActsN sIn sP (h - s)) S₂ = S₃ := by
    rw [hS3]; exact copyActsN_run' blank sIn sP (h - s) S₂
  have hR4 : runG blank (pushBothActs endSym) S₃ = S₄ := by
    rw [hS4]; exact pushBothActs_run blank endSym S₃
  have hR5 : runG blank
      (TAct.put sU blank .left :: (leftWalkG sU (s + 1) ++ [TAct.keep sU .right])) S₄ = S₅ := by
    rw [hS5]; exact settleActs_run blank sU s S₄ hxl5
  have hR6 : runG blank
      (TAct.put sP blank .left :: (leftWalkG sP (h - s + 1) ++ [TAct.keep sP .right])) S₅ = S₆ := by
    rw [hS6]; exact settleActs_run blank sP (h - s) S₅ hxl6
  -- `Exec` の合成（`execG_seq` が要求する入れ子の `runG` にそのまま合わせる）
  have E1 := pushBothProg_exec (Terminal := Terminal) (blank := blank) startSym S
  have E2 : ExecG Terminal blank (seqActs (copyActsN sIn sU s))
      (runG blank (pushBothActs startSym) S) (copyActsN sIn sU s) := by
    rw [hR1]; exact execG_seqActs _ S₁
  have E3 : ExecG Terminal blank (seqActs (copyActsN sIn sP (h - s)))
      (runG blank (copyActsN sIn sU s) (runG blank (pushBothActs startSym) S))
      (copyActsN sIn sP (h - s)) := by
    rw [hR1, hR2]; exact execG_seqActs _ S₂
  have E4 : ExecG Terminal blank (pushBothProg endSym)
      (runG blank (copyActsN sIn sP (h - s))
        (runG blank (copyActsN sIn sU s) (runG blank (pushBothActs startSym) S)))
      (pushBothActs endSym) := by
    rw [hR1, hR2, hR3]; exact pushBothProg_exec endSym S₃
  have E5 : ExecG Terminal blank
      (seqActs (TAct.put sU blank .left :: (leftWalkG sU (s + 1) ++ [TAct.keep sU .right])))
      (runG blank (pushBothActs endSym) (runG blank (copyActsN sIn sP (h - s))
        (runG blank (copyActsN sIn sU s) (runG blank (pushBothActs startSym) S))))
      (TAct.put sU blank .left :: (leftWalkG sU (s + 1) ++ [TAct.keep sU .right])) := by
    rw [hR1, hR2, hR3, hR4]; exact execG_seqActs _ S₄
  have E6 : ExecG Terminal blank
      (seqActs (TAct.put sP blank .left :: (leftWalkG sP (h - s + 1) ++ [TAct.keep sP .right])))
      (runG blank (TAct.put sU blank .left :: (leftWalkG sU (s + 1) ++ [TAct.keep sU .right]))
        (runG blank (pushBothActs endSym) (runG blank (copyActsN sIn sP (h - s))
          (runG blank (copyActsN sIn sU s) (runG blank (pushBothActs startSym) S)))))
      (TAct.put sP blank .left :: (leftWalkG sP (h - s + 1) ++ [TAct.keep sP .right])) := by
    rw [hR1, hR2, hR3, hR4, hR5]; exact execG_seqActs _ S₅
  have E7 : ExecG Terminal blank (kLoopProg blank mark k)
      (runG blank
        (TAct.put sP blank .left :: (leftWalkG sP (h - s + 1) ++ [TAct.keep sP .right]))
        (runG blank (TAct.put sU blank .left :: (leftWalkG sU (s + 1) ++ [TAct.keep sU .right]))
          (runG blank (pushBothActs endSym) (runG blank (copyActsN sIn sP (h - s))
            (runG blank (copyActsN sIn sU s) (runG blank (pushBothActs startSym) S))))))
      (kLoopActs blank p₁ k) := by
    rw [hR1, hR2, hR3, hR4, hR5, hR6]; exact e7
  have hcomb := execG_seq E1 (execG_seq E2 (execG_seq E3 (execG_seq E4
    (execG_seq E5 (execG_seq E6 E7)))))
  refine ⟨execG_of_eq rfl hcomb, ?_⟩
  show runG blank (setupProgActs blank startSym endSym s (h - s) k p₁) S
    = run blank (setupProgram blank startSym endSym k S) S
  have hval : runG blank (setupProgActs blank startSym endSym s (h - s) k p₁) S
      = run blank (kLoop blank k S₆) S₆ := by
    show runG blank (pushBothActs startSym ++
        (copyActsN sIn sU s ++
          (copyActsN sIn sP (h - s) ++
            (pushBothActs endSym ++
              ((TAct.put sU blank .left :: (leftWalkG sU (s + 1) ++ [TAct.keep sU .right])) ++
                ((TAct.put sP blank .left :: (leftWalkG sP (h - s + 1) ++ [TAct.keep sP .right]))
                  ++ kLoopActs blank p₁ k)))))) S
      = run blank (kLoop blank k S₆) S₆
    rw [runG_append, hR1, runG_append, hR2, runG_append, hR3, runG_append, hR4,
      runG_append, hR5, runG_append, hR6, e7run]
  rw [hval]
  simp only [setupProgram, seqP_run]
  rw [← hS1, hcount2, ← hS2, hcount3, ← hS3, ← hS4, hlen5, ← hS5, hlen6', ← hS6]

/-- 動作数：`setupProg` の実行で出るトレース（`gavecs`）の長さは元の `setupProgram`
の動作列の長さそのもの。すなわち `setupProg` は余計なマイクロステップを一切
増やさない（`xfer1`/`xfer2`/`kLoop` のようなプローブ＋復元は不要だった）。 -/
theorem setupProg_trace_length {startSym endSym : Fin sc} (s hms k p₁ : ℕ) :
    (setupProgActs blank startSym endSym s hms k p₁).length
      = 4 + 2 * s + 2 * hms + (s + 3) + (hms + 3) + k * (7 * p₁ + 4) := by
  simp only [setupProgActs, pushBothActs, List.length_append, copyActsN_length, leftWalkG_length,
    kLoopActs_length, List.length_cons, List.length_nil]
  ring

/-- **停止**：`setupProg` を継続 `[]` の下で走らせると、動作列を出し切った後の
継続はちょうど `[]`（＝停止）に戻る。`Exec`（＝`ExecK … [p] …`）の定義そのものから
`r := []` として直ちに従う。 -/
theorem setupProg_halts {startSym endSym : Fin sc} {s h p₁ r k : ℕ} {w Text : List (Fin sc)}
    {S : Tapes sc} {leftSym : Fin sc} (H : SetupPre blank mark leftSym s h p₁ r w Text S) (hne : mark ≠ blank)
    (l : List (Option Terminal))
    (hl : l.length = (setupProgActs blank startSym endSym s (h - s) k p₁).length) :
    ∃ s', runInputs (IG Terminal 12 sc) blank l
        ([setupProg blank startSym endSym mark s (h - s) k], TSg S)
        = (s', applyTrace blank (TSg S)
            (gavecs blank (setupProgActs blank startSym endSym s (h - s) k p₁) S))
      ∧ SEqAt (IG Terminal 12 sc)
          (applyTrace blank (TSg S)
            (gavecs blank (setupProgActs blank startSym endSym s (h - s) k p₁) S))
          s' [] := by
  have hlen : l.length
      = (gavecs blank (setupProgActs blank startSym endSym s (h - s) k p₁) S).length := by
    rw [gavecs_length]; exact hl
  obtain ⟨-, s', hrun, hEq⟩ := (setupProg_exec H hne).1 [] l hlen
  exact ⟨s', by simpa using hrun, hEq⟩

/-- **系**：`setupProg` を走らせた結果には元の `setup_spec` がそのまま適用できる
（`TAct` レベルのトレース `setupProgActs` の作用が `setupProgram` の作用とテープ状態として
一致するため）。 -/
theorem setupProg_spec {startSym endSym : Fin sc} {s h p₁ r k : ℕ} {w Text : List (Fin sc)}
    {S : Tapes sc} {leftSym : Fin sc} (H : SetupPre blank mark leftSym s h p₁ r w Text S) (hne : mark ≠ blank) :
    (ExecG Terminal blank (setupProg blank startSym endSym mark s (h - s) k) S
        (setupProgActs blank startSym endSym s (h - s) k p₁) ∧
      runG blank (setupProgActs blank startSym endSym s (h - s) k p₁) S
        = run blank (setupProgram blank startSym endSym k S) S) ∧
      GSVTapes.VEncodes' blank startSym endSym mark
          ((w.take h).reverse.take s) ((w.take h).reverse.drop s)
          (TextFeed.padW blank Text 0) k p₁ r
          (toGS (setupRun blank startSym endSym k S), toVExt (setupRun blank startSym endSym k S))
          (⟨0, 0⟩, 0)
        ∧ (setupProgram blank startSym endSym k S).length ≤ 7 * (h + k * p₁ + 1) :=
  ⟨setupProg_exec H hne, setup_spec H⟩

/-! ## 13. 真に有限制御な版（`s`,`h` を定数として展開しない）

`s`（段幅の切り分け）と `h`（`= S/2`、段幅は 2 冪を渡る）は構成の定数ではないので、
`copyLoop` の回数として直接展開することはできない。ここでは

* `s` 個のコピー：カウンタ `sCs` を実際に 1 ずつ消費しながら回し、消費した分を
  ミラーの `sC2` に転写し（`decCopyMirror_run`/`decCopyMirror_counter`）、あとで
  `xfer1Prog` で `sC2 → sCs` に戻して `sCs` の値も復元する。
* `h - s` 個のコピー：入力コピーテープ `sIn` の左端に本物の番兵 `leftSym` を置いた
  前提 `PrepPreL` を置き、`leftSym` を読むまで回すだけのループ（`copyLoopSentL_exec`）
  で止める。
* 積み終えたスタックを逐次ビューへ戻す 2 回の `settle` は、もとから番兵駆動
  （`startSym` を読むまで）の `settleProgG` を使う（`s` に依存しない）。

を使って、`s`,`h` を含まない**単一の固定 `Prog`** `setupProgL` を組む。 -/

/-- カウンタ駆動ループ `decActsN` は、`cs` を触れない本体のもとで、`n` 周回後に
`cs` 自身をちょうど `0` にする。 -/
theorem decActsN_counter (blank mark : Fin sc) {cs : Fin 12} (body : List (TAct 12 sc))
    (hbody : ∀ x ∈ body, x.tape ≠ cs) :
    ∀ (n : ℕ) (S : Tapes sc), Tape.CounterView' blank mark (S cs) n →
      Tape.CounterView' blank mark (runG blank (decActsN blank cs body n) S cs) 0 := by
  intro n
  induction n with
  | zero => intro S h; simpa [decActsN] using h
  | succ n ih =>
      intro S h
      rw [decActsN, runG_append]
      refine ih _ ?_
      have h1 : (runG blank (decRound blank cs body) S) cs
          = Tape.step blank (Tape.step blank (S cs) blank .left) blank .stay := by
        show (runG blank body (applyG blank (applyG blank S (TAct.put cs blank .left))
          (TAct.put cs blank .stay))) cs = _
        rw [runG_untouched blank cs body _ hbody, applyG_put_self, applyG_put_self]
      rw [h1]
      exact Tape.counter'_dec h

/-- **フェーズ 2 の内容**：カウンタ駆動コピー＋ミラー＋復元の結果、`sIn`,`sU` は
`copyLoop_spec` どおりの内容になり、`sC2` はちょうど `0` に戻り、それ以外のテープは
`S₁` のまま。`sCs` 自身の値は以後どこにも使わないので追跡しない。 -/
theorem phase2_facts (mark : Fin sc) (S₁ : Tapes sc) (s b : ℕ) (w l : List (Fin sc))
    (hcs1 : Tape.CounterView' blank mark (S₁ sCs) s)
    (hc2 : Tape.CounterView' blank mark (S₁ sC2) 0) (hb : s ≤ b + 1)
    (hIn : Tape.SeqView blank (S₁ sIn) w b) (hU : Tape.StackView blank (S₁ sU) l) :
    ∃ S₂ : Tapes sc,
      runG blank
        ((decActsN blank sCs (copyRoundMirror blank sIn sU sC2) s
            ++ [TAct.put sCs blank .left, TAct.keep sCs .right])
          ++ xfer1Acts blank sC2 sCs s) S₁ = S₂ ∧
      Tape.SeqView blank (S₂ sIn) w (b - s) ∧
      Tape.StackView blank (S₂ sU) (((w.take (b + 1)).drop (b + 1 - s)) ++ l) ∧
      Tape.CounterView' blank mark (S₂ sC2) 0 ∧
      ∀ j : Fin 12, j ≠ sIn → j ≠ sU → j ≠ sCs → j ≠ sC2 → S₂ j = S₁ j := by
  set T1 := runG blank (decActsN blank sCs (copyRoundMirror blank sIn sU sC2) s) S₁ with hT1
  have hbody : ∀ x ∈ copyRoundMirror blank sIn sU sC2 (sc := sc), x.tape ≠ sCs := by
    intro x hx
    fin_cases hx <;> simp only [TAct.tape] <;> decide
  have hT1cs : Tape.CounterView' blank mark (T1 sCs) 0 :=
    decActsN_counter blank mark (copyRoundMirror blank sIn sU sC2) hbody s S₁ hcs1
  have hT1mir : Tape.CounterView' blank mark (T1 sC2) s := by
    simpa using decCopyMirror_counter blank mark (mir := sC2) (i := sIn) (j := sU) (cs := sCs)
      (by decide) (by decide) (by decide) s S₁ 0 hc2
  have hcopyLoop := copyLoop_spec blank (i := sIn) (j := sU) (by decide) s b S₁ w l hb hIn hU
  have hT1eq : ∀ j : Fin 12, j ≠ sCs → j ≠ sC2 → T1 j = run blank (copyLoop blank sIn sU s S₁) S₁ j
      := decCopyMirror_run blank mark (cs := sCs) (mir := sC2) (i := sIn) (j := sU)
        (by decide) (by decide) (by decide) (by decide) (by decide) s S₁ S₁
        (fun m _ _ => rfl)
  have hprobe : runG blank [TAct.put sCs blank (sc := sc) .left, TAct.keep sCs .right] T1 = T1 :=
    probeRestore_id (mark := mark) hT1cs
  have hstep : runG blank (decActsN blank sCs (copyRoundMirror blank sIn sU sC2) s
      ++ [TAct.put sCs blank .left, TAct.keep sCs .right]) S₁ = T1 := by
    rw [runG_append, hT1, hprobe]
  refine ⟨runG blank (xfer1Acts blank sC2 sCs s) T1, by rw [runG_append, hstep], ?_, ?_, ?_, ?_⟩
  · rw [xfer1Acts_run (mark := mark) (a := sC2) (b := sCs) (by decide) s T1
      (by simpa using hT1mir) hT1cs,
      xfer1_untouched blank (a := sC2) (b := sCs) (by decide) (by decide) s T1,
      hT1eq sIn (by decide) (by decide)]
    exact hcopyLoop.1
  · rw [xfer1Acts_run (mark := mark) (a := sC2) (b := sCs) (by decide) s T1
      (by simpa using hT1mir) hT1cs,
      xfer1_untouched blank (a := sC2) (b := sCs) (by decide) (by decide) s T1,
      hT1eq sU (by decide) (by decide)]
    exact hcopyLoop.2
  · obtain ⟨g1, -⟩ := xfer1_spec (blank := blank) (mark := mark) (a := sC2) (b := sCs)
      (by decide) s T1 0 0 (by simpa using hT1mir) hT1cs
    rw [xfer1Acts_run (mark := mark) (a := sC2) (b := sCs) (by decide) s T1
      (by simpa using hT1mir) hT1cs]
    simpa using g1
  · intro j hji hju hjcs hjc2
    rw [xfer1Acts_run (mark := mark) (a := sC2) (b := sCs) (by decide) s T1
      (by simpa using hT1mir) hT1cs, xfer1_untouched blank (a := sC2) (b := sCs) hjc2 hjcs s T1,
      hT1eq j hjcs hjc2, copyLoop_untouched blank hji hju s S₁]

/-- **左端に番兵がある場合の準備前提**。`SetupPre` の `inb` を、本物の番兵 `leftSym`
（`w'` には現れない記号）を先頭に置いた `leftSym :: w'` に対する（`h - 1` ではなく）
`h` の位置での逐次ビューに置き換えたもの。`s`,`h` は入力ごとに変わる値のままでよく、
`setupProgL` の構造自体はこれらに依存しない。 -/
structure PrepPreL (blank mark leftSym : Fin sc) (s h p₁ r : ℕ) (w' Text : List (Fin sc))
    (S : Tapes sc) : Prop where
  hpos : 0 < h
  hle : h ≤ w'.length
  hcut : s < h
  hfresh : leftSym ∉ w'
  inb : Tape.SeqView blank (S sIn) (leftSym :: w') h
  emptyU : Tape.StackView blank (S sU) []
  emptyP : Tape.StackView blank (S sP) []
  txt : Tape.SeqView blank (S sT) (TextFeed.padW blank Text 0) 0
  txt2 : Tape.SeqView blank (S sX2) (TextFeed.padW blank Text 0) 0
  cs : Tape.CounterView' blank mark (S sCs) s
  c1 : Tape.CounterView' blank mark (S sC1) p₁
  c2 : Tape.CounterView' blank mark (S sC2) 0
  ap : Tape.CounterView' blank mark (S sAp) 0
  an : Tape.CounterView' blank mark (S sAn) 0
  rp : Tape.CounterView' blank mark (S sRp) r
  rn : Tape.CounterView' blank mark (S sRn) 0

/-- 添字シフトの補題：`m ≤ n` のとき、先頭に 1 個足した語の
`take (n+1) |>.drop (n+1-m)` は、もとの語の `take n |>.drop (n-m)` に一致する。
`leftSym` を先頭に加えたことによる `PrepPreL` 側の全ての位置計算はこれ 1 本に帰着する。 -/
theorem take_drop_shift (a : Fin sc) (w' : List (Fin sc)) (n m : ℕ) (hm : m ≤ n) :
    ((a :: w').take (n + 1)).drop (n + 1 - m) = (w'.take n).drop (n - m) := by
  rw [show n + 1 - m = (n - m) + 1 from by omega]
  rfl

/-- `startSym` が本体に現れず `endSym` とも異なるとき、
`aTop::(X++[startSym])` を逆順にした語は `startSym` を先頭にちょうど 1 回だけ持つ。
`settleProgG_exec` の番兵条件 `hs0`/`hfresh` はこれで得られる。 -/
theorem settle_sentinel_fresh {startSym : Fin sc} (X : List (Fin sc)) (aTop : Fin sc)
    (hX : startSym ∉ X) (hne : startSym ≠ aTop) :
    ((aTop :: (X ++ [startSym])).reverse)[0]? = some startSym ∧
      ∀ m : ℕ, 0 < m → ((aTop :: (X ++ [startSym])).reverse)[m]? ≠ some startSym := by
  have hrev : (aTop :: (X ++ [startSym])).reverse = startSym :: (X.reverse ++ [aTop]) := by
    simp [List.reverse_cons, List.reverse_append]
  rw [hrev]
  refine ⟨rfl, ?_⟩
  intro m hm hc
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rw [List.getElem?_cons_succ] at hc
  rcases Nat.lt_or_ge m' X.reverse.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hc
    obtain ⟨hlt2, hget⟩ := List.getElem?_eq_some_iff.1 hc
    exact hX (List.mem_reverse.1 (hget ▸ List.getElem_mem hlt2))
  · rw [List.getElem?_append_right hge] at hc
    rcases Nat.eq_zero_or_pos (m' - X.reverse.length) with h0 | hpos
    · rw [h0] at hc; simp at hc; exact hne hc.symm
    · rw [List.getElem?_eq_none (by rw [List.length_singleton]; omega)] at hc; simp at hc

/-! ### 入力に依存しない準備フェーズ（`setupProgL`） -/

/-- フェーズ 2（カウンタ駆動コピー＋ミラー＋復元）の動作列。 -/
def phase2Acts (blank : Fin sc) (n : ℕ) : List (TAct 12 sc) :=
  (decActsN blank sCs (copyRoundMirror blank sIn sU sC2) n
      ++ [TAct.put sCs blank .left, TAct.keep sCs .right])
    ++ xfer1Acts blank sC2 sCs n

/-- **入力に依存しない準備フェーズのプログラム**。`s` にも `h` にも依存しない
（`k` だけが構成の定数）。 -/
def setupProgL (blank startSym endSym mark leftSym : Fin sc) (k : ℕ) :
    Prog (ActG 12 sc) (CondG 12 sc) :=
  Prog.seq (pushBothProg startSym)
    (Prog.seq
      (Prog.seq (decLoopProg blank sCs (copyRoundMirror blank sIn sU sC2) mark)
        (xfer1Prog blank mark sC2 sCs))
      (Prog.seq
        (Prog.loop (sIn, leftSym) (TAct.copy sP sIn (sc := sc) .right).act
          (ACT (TAct.keep sIn .left)))
        (Prog.seq (pushBothProg endSym)
          (Prog.seq (settleProgG sU blank startSym)
            (Prog.seq (settleProgG sP blank startSym) (kLoopProg blank mark k))))))

/-- `setupProgL` が実行する動作列。 -/
def setupProgLActs (blank startSym endSym : Fin sc) (s hms k p₁ : ℕ) : List (TAct 12 sc) :=
  pushBothActs startSym ++
    (phase2Acts blank s ++
      (copyActsN sIn sP hms ++
        (pushBothActs endSym ++
          ((TAct.put sU blank .left :: (leftWalkG sU (s + 1) ++ [TAct.keep sU .right])) ++
            ((TAct.put sP blank .left :: (leftWalkG sP (hms + 1) ++ [TAct.keep sP .right])) ++
              kLoopActs blank p₁ k)))))

/-- `setupProgL` の実行結果テープ（フェーズごとの意味論的な合成）。 -/
def setupTapesL (blank startSym endSym : Fin sc) (s hms k : ℕ) (S : Tapes sc) : Tapes sc :=
  let S₁ := run blank (pushBoth startSym) S
  let S₂ := runG blank (phase2Acts blank s) S₁
  let S₃ := run blank (copyLoop blank sIn sP hms S₂) S₂
  let S₄ := run blank (pushBoth endSym) S₃
  let S₅ := run blank (settle blank sU s) S₄
  let S₆ := run blank (settle blank sP hms) S₅
  run blank (kLoop blank k S₆) S₆

/-- **動作数**：`setupProgL` のトレース長。`setupProgActs` の
`10 + 3*s + 3*hms + k*(7*p₁+4)` に対して、カウンタ駆動化のぶん `4 + 6*s` だけ増える
（フェーズ 2 のミラー書き込み `s`、`decLoop` のプローブ＋復元 `2`、`xfer1` の `3*s+2`）。 -/
theorem setupProgL_trace_length {startSym endSym : Fin sc} (s hms k p₁ : ℕ) :
    (setupProgLActs blank startSym endSym s hms k p₁).length
      = 14 + 9 * s + 3 * hms + k * (7 * p₁ + 4) := by
  simp only [setupProgLActs, phase2Acts, pushBothActs, List.length_append, decActsN_length,
    xfer1Acts_length, copyActsN_length, leftWalkG_length, kLoopActs_length, List.length_cons,
    List.length_nil, copyRoundMirror, copyRoundG]
  ring

theorem setupProgL_exec {startSym endSym leftSym : Fin sc} {s h p₁ r k : ℕ}
    {w' Text : List (Fin sc)} {S : Tapes sc}
    (H : PrepPreL blank mark leftSym s h p₁ r w' Text S) (hne : mark ≠ blank)
    (hSw : startSym ∉ w') (hSE : startSym ≠ endSym) :
    ExecG Terminal blank (setupProgL blank startSym endSym mark leftSym k) S
        (setupProgLActs blank startSym endSym s (h - s) k p₁) ∧
      runG blank (setupProgLActs blank startSym endSym s (h - s) k p₁) S
        = setupTapesL blank startSym endSym s (h - s) k S := by
  obtain ⟨hpos, hle, hcut, hfresh, hIn, hU, hP, _hT, _hX2, hCs, hC1, hC2, _hAp, hAn, _hRp,
    _hRn⟩ := H
  -- フェーズ 1
  obtain ⟨S₁, hS1⟩ : ∃ T, run blank (pushBoth startSym) S = T := ⟨_, rfl⟩
  have p1U : Tape.StackView blank (S₁ sU) [startSym] := by
    rw [← hS1, pushBoth_U]; exact Tape.push_spec hU startSym
  have p1P : Tape.StackView blank (S₁ sP) [startSym] := by
    rw [← hS1, pushBoth_P]; exact Tape.push_spec hP startSym
  have p1ne : ∀ j : Fin 12, j ≠ sU → j ≠ sP → S₁ j = S j := by
    intro j hu hp; rw [← hS1]; exact pushBoth_ne blank startSym hu hp S
  -- フェーズ 2
  have hcs1 : Tape.CounterView' blank mark (S₁ sCs) s := by
    rw [p1ne sCs (by decide) (by decide)]; exact hCs
  have hc21 : Tape.CounterView' blank mark (S₁ sC2) 0 := by
    rw [p1ne sC2 (by decide) (by decide)]; exact hC2
  have hIn1 : Tape.SeqView blank (S₁ sIn) (leftSym :: w') h := by
    rw [p1ne sIn (by decide) (by decide)]; exact hIn
  obtain ⟨S₂, hS2, p2In, p2U0, p2C2, p2ne⟩ :=
    phase2_facts (blank := blank) mark S₁ s h (leftSym :: w') [startSym] hcs1 hc21
      (by omega) hIn1 p1U
  have p2U : Tape.StackView blank (S₂ sU) ((w'.take h).drop (h - s) ++ [startSym]) := by
    rwa [take_drop_shift leftSym w' h s (by omega)] at p2U0
  -- フェーズ 3
  obtain ⟨S₃, hS3⟩ : ∃ T, run blank (copyLoop blank sIn sP (h - s) S₂) S₂ = T := ⟨_, rfl⟩
  have p3 := copyLoop_spec blank (i := sIn) (j := sP) (by decide) (h - s) (h - s) S₂
    (leftSym :: w') [startSym] (by omega) p2In
    (by rw [p2ne sP (by decide) (by decide) (by decide) (by decide)]; exact p1P)
  have p3ne : ∀ j : Fin 12, j ≠ sIn → j ≠ sP → S₃ j = S₂ j := by
    intro j hi hp; rw [← hS3]; exact copyLoop_untouched blank hi hp _ _
  have p3P : Tape.StackView blank (S₃ sP) (w'.take (h - s) ++ [startSym]) := by
    have h2 := p3.2
    rw [hS3, take_drop_shift leftSym w' (h - s) (h - s) (le_refl _), Nat.sub_self,
      List.drop_zero] at h2
    exact h2
  -- フェーズ 4
  obtain ⟨S₄, hS4⟩ : ∃ T, run blank (pushBoth endSym) S₃ = T := ⟨_, rfl⟩
  have p4U : Tape.StackView blank (S₄ sU)
      (endSym :: ((w'.take h).drop (h - s) ++ [startSym])) := by
    rw [← hS4, pushBoth_U]
    exact Tape.push_spec (by rw [p3ne sU (by decide) (by decide)]; exact p2U) endSym
  have p4P : Tape.StackView blank (S₄ sP) (endSym :: (w'.take (h - s) ++ [startSym])) := by
    rw [← hS4, pushBoth_P]; exact Tape.push_spec p3P endSym
  have p4ne : ∀ j : Fin 12, j ≠ sU → j ≠ sP → S₄ j = S₃ j := by
    intro j hu hp; rw [← hS4]; exact pushBoth_ne blank endSym hu hp S₃
  -- 長さ
  have hxlen : (w'.take h).length = h := by simp only [List.length_take]; omega
  have hulen : ((w'.take h).drop (h - s)).length = s := by
    rw [List.length_drop, hxlen]; omega
  have hvlen : (w'.take (h - s)).length = h - s := by
    simp only [List.length_take]; omega
  -- フェーズ 5・6
  have hs5 := settle_spec blank sU (n := s) p4U (by
    simp only [List.length_cons, List.length_append, List.length_nil, hulen])
  have hxl5 : ∃ x l, ((run blank (settle blank sU s) S₄) sU).left = x :: l := by
    have hlenL : ((run blank (settle blank sU s) S₄) sU).left.length = 1 := by
      rw [hs5.left_eq, List.length_reverse, List.length_take, Nat.min_eq_left (by
        have := hs5.lt; omega)]
    generalize hL : ((run blank (settle blank sU s) S₄) sU).left = L at hlenL ⊢
    cases L with
    | nil => simp at hlenL
    | cons x l => exact ⟨x, l, rfl⟩
  obtain ⟨x5, l5, hxl5⟩ := hxl5
  obtain ⟨S₅, hS5⟩ : ∃ T, run blank (settle blank sU s) S₄ = T := ⟨_, rfl⟩
  have p5ne : ∀ j : Fin 12, j ≠ sU → S₅ j = S₄ j := by
    intro j hu; rw [← hS5]; exact settle_untouched blank hu _ _
  have hp4P' : Tape.StackView blank (S₅ sP) (endSym :: (w'.take (h - s) ++ [startSym])) := by
    rw [p5ne sP (by decide)]; exact p4P
  have hs6 := settle_spec blank sP (n := h - s) hp4P' (by
    simp only [List.length_cons, List.length_append, List.length_nil, hvlen])
  have hxl6 : ∃ x l, ((run blank (settle blank sP (h - s)) S₅) sP).left = x :: l := by
    have hlenL : ((run blank (settle blank sP (h - s)) S₅) sP).left.length = 1 := by
      rw [hs6.left_eq, List.length_reverse, List.length_take, Nat.min_eq_left (by
        have := hs6.lt; omega)]
    generalize hL : ((run blank (settle blank sP (h - s)) S₅) sP).left = L at hlenL ⊢
    cases L with
    | nil => simp at hlenL
    | cons x l => exact ⟨x, l, rfl⟩
  obtain ⟨x6, l6, hxl6⟩ := hxl6
  obtain ⟨S₆, hS6⟩ : ∃ T, run blank (settle blank sP (h - s)) S₅ = T := ⟨_, rfl⟩
  have p6ne : ∀ j : Fin 12, j ≠ sP → S₆ j = S₅ j := by
    intro j hp; rw [← hS6]; exact settle_untouched blank hp _ _
  -- 触られなかったテープ
  have hkeep : ∀ j : Fin 12, j ≠ sU → j ≠ sP → j ≠ sIn → j ≠ sCs → j ≠ sC2 → S₆ j = S j := by
    intro j hu hp hi hcs hc2
    rw [p6ne j hp, p5ne j hu, p4ne j hu hp, p3ne j hi hp, p2ne j hi hu hcs hc2, p1ne j hu hp]
  have hC1' : Tape.CounterView' blank mark (S₆ sC1) p₁ := by
    rw [hkeep sC1 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hC1
  have hC2' : Tape.CounterView' blank mark (S₆ sC2) 0 := by
    rw [p6ne sC2 (by decide), p5ne sC2 (by decide), p4ne sC2 (by decide) (by decide),
      p3ne sC2 (by decide) (by decide)]
    exact p2C2
  have hAn' : Tape.CounterView' blank mark (S₆ sAn) 0 := by
    rw [hkeep sAn (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hAn
  obtain ⟨e7, e7run⟩ := kLoopProg_exec (Terminal := Terminal) hne k S₆ p₁ 0 hC1' hC2' hAn'
  -- 各段の作用
  have hR1 : runG blank (pushBothActs startSym) S = S₁ := by
    rw [pushBothActs_run, hS1]
  have hR2 : runG blank (phase2Acts blank s) S₁ = S₂ := hS2
  have hR3 : runG blank (copyActsN sIn sP (h - s)) S₂ = S₃ := by
    rw [copyActsN_run', hS3]
  have hR4 : runG blank (pushBothActs endSym) S₃ = S₄ := by
    rw [pushBothActs_run, hS4]
  have hR5 : runG blank
      (TAct.put sU blank .left :: (leftWalkG sU (s + 1) ++ [TAct.keep sU .right])) S₄ = S₅ := by
    rw [settleActs_run blank sU s S₄ hxl5, hS5]
  have hR6 : runG blank
      (TAct.put sP blank .left :: (leftWalkG sP (h - s + 1) ++ [TAct.keep sP .right])) S₅
        = S₆ := by
    rw [settleActs_run blank sP (h - s) S₅ hxl6, hS6]
  -- 各段の `ExecG`
  have E7 : ExecG Terminal blank (kLoopProg blank mark k) S₆ (kLoopActs blank p₁ k) := e7
  have hsentU := settle_sentinel_fresh (startSym := startSym) ((w'.take h).drop (h - s)) endSym
    (fun hc => hSw (List.mem_of_mem_take (List.mem_of_mem_drop hc))) hSE
  have hsentP := settle_sentinel_fresh (startSym := startSym) (w'.take (h - s)) endSym
    (fun hc => hSw (List.mem_of_mem_take hc)) hSE
  have E6 : ExecG Terminal blank (settleProgG sP blank startSym) S₅
      (TAct.put sP blank .left :: (leftWalkG sP (h - s + 1) ++ [TAct.keep sP .right])) := by
    have := settleProgG_exec (Terminal := Terminal) (i := sP) (sent := startSym) hp4P'
      hsentP.1 hsentP.2
    rwa [show (w'.take (h - s) ++ [startSym]).length = h - s + 1 from by
      simp only [List.length_append, List.length_cons, List.length_nil, hvlen]] at this
  have E5 : ExecG Terminal blank (settleProgG sU blank startSym) S₄
      (TAct.put sU blank .left :: (leftWalkG sU (s + 1) ++ [TAct.keep sU .right])) := by
    have := settleProgG_exec (Terminal := Terminal) (i := sU) (sent := startSym) p4U
      hsentU.1 hsentU.2
    rwa [show ((w'.take h).drop (h - s) ++ [startSym]).length = s + 1 from by
      simp only [List.length_append, List.length_cons, List.length_nil, hulen]] at this
  have E4 : ExecG Terminal blank (pushBothProg endSym) S₃ (pushBothActs endSym) :=
    pushBothProg_exec endSym S₃
  have E3 : ExecG Terminal blank
      (Prog.loop (sIn, leftSym) (TAct.copy sP sIn (sc := sc) .right).act
        (ACT (TAct.keep sIn .left))) S₂ (copyActsN sIn sP (h - s)) :=
    copyLoopSentL_exec (Terminal := Terminal) (by decide) hfresh (h - s) S₂ p2In
  have hbody : ∀ x ∈ copyRoundMirror blank sIn sU sC2 (sc := sc), x.tape ≠ sCs := by
    intro x hx
    fin_cases hx <;> simp only [TAct.tape] <;> decide
  have E2a : ExecG Terminal blank (decLoopProg blank sCs (copyRoundMirror blank sIn sU sC2) mark)
      S₁ (decActsN blank sCs (copyRoundMirror blank sIn sU sC2) s
        ++ [TAct.put sCs blank .left, TAct.keep sCs .right]) :=
    decLoopProg_exec hne hbody s S₁ hcs1
  have hmirD : Tape.CounterView' blank mark
      (runG blank (decActsN blank sCs (copyRoundMirror blank sIn sU sC2) s) S₁ sC2) s := by
    simpa using decCopyMirror_counter blank mark (cs := sCs) (mir := sC2) (i := sIn) (j := sU)
      (by decide) (by decide) (by decide) s S₁ 0 hc21
  have hT1c2 : Tape.CounterView' blank mark
      (runG blank (decActsN blank sCs (copyRoundMirror blank sIn sU sC2) s
        ++ [TAct.put sCs blank .left, TAct.keep sCs .right]) S₁ sC2) s := by
    rw [runG_append, runG_untouched blank sC2 _ _ (by
      intro x hx; fin_cases hx <;> simp only [TAct.tape] <;> decide)]
    exact hmirD
  have E2b : ExecG Terminal blank (xfer1Prog blank mark sC2 sCs)
      (runG blank (decActsN blank sCs (copyRoundMirror blank sIn sU sC2) s
        ++ [TAct.put sCs blank .left, TAct.keep sCs .right]) S₁)
      (xfer1Acts blank sC2 sCs s) :=
    xfer1Prog_exec hne (by decide) s _ hT1c2
  have E2 : ExecG Terminal blank
      (Prog.seq (decLoopProg blank sCs (copyRoundMirror blank sIn sU sC2) mark)
        (xfer1Prog blank mark sC2 sCs)) S₁ (phase2Acts blank s) :=
    execG_seq E2a E2b
  have E1 : ExecG Terminal blank (pushBothProg startSym) S (pushBothActs startSym) :=
    pushBothProg_exec startSym S
  -- 合成
  have F6 := execG_seq E6 (by rw [hR6]; exact E7)
  have F5 := execG_seq E5 (by rw [hR5]; exact F6)
  have F4 := execG_seq E4 (by rw [hR4]; exact F5)
  have F3 := execG_seq E3 (by rw [hR3]; exact F4)
  have F2 := execG_seq E2 (by rw [hR2]; exact F3)
  have F1 := execG_seq E1 (by rw [hR1]; exact F2)
  refine ⟨execG_of_eq rfl F1, ?_⟩
  show runG blank (pushBothActs startSym ++
      (phase2Acts blank s ++
        (copyActsN sIn sP (h - s) ++
          (pushBothActs endSym ++
            ((TAct.put sU blank .left :: (leftWalkG sU (s + 1) ++ [TAct.keep sU .right])) ++
              ((TAct.put sP blank .left ::
                  (leftWalkG sP (h - s + 1) ++ [TAct.keep sP .right])) ++
                kLoopActs blank p₁ k)))))) S
    = setupTapesL blank startSym endSym s (h - s) k S
  rw [runG_append, hR1, runG_append, hR2, runG_append, hR3, runG_append, hR4,
    runG_append, hR5, runG_append, hR6, e7run]
  simp only [setupTapesL]
  rw [hS1, hR2, hS3, hS4, hS5, hS6]

/-- **主定理**：`setupProgL`（`s`,`h` に依存しない単一の固定プログラム）は
`PrepPreL` のもとで `PatternTapes.setup_spec` と同じ符号化を作る。 -/
theorem setupProgL_spec {startSym endSym leftSym : Fin sc} {s h p₁ r k : ℕ}
    {w' Text : List (Fin sc)} {S : Tapes sc}
    (H : PrepPreL blank mark leftSym s h p₁ r w' Text S) (hne : mark ≠ blank)
    (hSw : startSym ∉ w') (hSE : startSym ≠ endSym) :
    (ExecG Terminal blank (setupProgL blank startSym endSym mark leftSym k) S
        (setupProgLActs blank startSym endSym s (h - s) k p₁) ∧
      runG blank (setupProgLActs blank startSym endSym s (h - s) k p₁) S
        = setupTapesL blank startSym endSym s (h - s) k S) ∧
      GSVTapes.VEncodes' blank startSym endSym mark
        ((w'.take h).reverse.take s) ((w'.take h).reverse.drop s)
        (TextFeed.padW blank Text 0) k p₁ r
        (toGS (setupTapesL blank startSym endSym s (h - s) k S),
          toVExt (setupTapesL blank startSym endSym s (h - s) k S))
        (⟨0, 0⟩, 0) := by
  refine ⟨setupProgL_exec (Terminal := Terminal) H hne hSw hSE, ?_⟩
  obtain ⟨hpos, hle, hcut, hfresh, hIn, hU, hP, hT, hX2, hCs, hC1, hC2, hAp, hAn, hRp,
    hRn⟩ := H
  have hxlen : (w'.take h).length = h := by simp only [List.length_take]; omega
  have hueq : ((w'.take h).drop (h - s)).reverse = (w'.take h).reverse.take s := by
    rw [List.take_reverse, hxlen]
  have hveq : (w'.take (h - s)).reverse = (w'.take h).reverse.drop s := by
    rw [List.drop_reverse, hxlen, List.take_take, Nat.min_eq_left (by omega)]
  -- フェーズ 1
  obtain ⟨S₁, hS1⟩ : ∃ T, run blank (pushBoth startSym) S = T := ⟨_, rfl⟩
  have p1U : Tape.StackView blank (S₁ sU) [startSym] := by
    rw [← hS1, pushBoth_U]; exact Tape.push_spec hU startSym
  have p1P : Tape.StackView blank (S₁ sP) [startSym] := by
    rw [← hS1, pushBoth_P]; exact Tape.push_spec hP startSym
  have p1ne : ∀ j : Fin 12, j ≠ sU → j ≠ sP → S₁ j = S j := by
    intro j hu hp; rw [← hS1]; exact pushBoth_ne blank startSym hu hp S
  -- フェーズ 2
  have hcs1 : Tape.CounterView' blank mark (S₁ sCs) s := by
    rw [p1ne sCs (by decide) (by decide)]; exact hCs
  have hc21 : Tape.CounterView' blank mark (S₁ sC2) 0 := by
    rw [p1ne sC2 (by decide) (by decide)]; exact hC2
  have hIn1 : Tape.SeqView blank (S₁ sIn) (leftSym :: w') h := by
    rw [p1ne sIn (by decide) (by decide)]; exact hIn
  obtain ⟨S₂, hS2, p2In, p2U0, p2C2, p2ne⟩ :=
    phase2_facts (blank := blank) mark S₁ s h (leftSym :: w') [startSym] hcs1 hc21
      (by omega) hIn1 p1U
  have p2U : Tape.StackView blank (S₂ sU) ((w'.take h).drop (h - s) ++ [startSym]) := by
    rwa [take_drop_shift leftSym w' h s (by omega)] at p2U0
  -- フェーズ 3
  obtain ⟨S₃, hS3⟩ : ∃ T, run blank (copyLoop blank sIn sP (h - s) S₂) S₂ = T := ⟨_, rfl⟩
  have p3 := copyLoop_spec blank (i := sIn) (j := sP) (by decide) (h - s) (h - s) S₂
    (leftSym :: w') [startSym] (by omega) p2In
    (by rw [p2ne sP (by decide) (by decide) (by decide) (by decide)]; exact p1P)
  have p3ne : ∀ j : Fin 12, j ≠ sIn → j ≠ sP → S₃ j = S₂ j := by
    intro j hi hp; rw [← hS3]; exact copyLoop_untouched blank hi hp _ _
  have p3P : Tape.StackView blank (S₃ sP) (w'.take (h - s) ++ [startSym]) := by
    have h2 := p3.2
    rw [hS3, take_drop_shift leftSym w' (h - s) (h - s) (le_refl _), Nat.sub_self,
      List.drop_zero] at h2
    exact h2
  -- フェーズ 4
  obtain ⟨S₄, hS4⟩ : ∃ T, run blank (pushBoth endSym) S₃ = T := ⟨_, rfl⟩
  have p4U : Tape.StackView blank (S₄ sU)
      (endSym :: ((w'.take h).drop (h - s) ++ [startSym])) := by
    rw [← hS4, pushBoth_U]
    exact Tape.push_spec (by rw [p3ne sU (by decide) (by decide)]; exact p2U) endSym
  have p4P : Tape.StackView blank (S₄ sP) (endSym :: (w'.take (h - s) ++ [startSym])) := by
    rw [← hS4, pushBoth_P]; exact Tape.push_spec p3P endSym
  have p4ne : ∀ j : Fin 12, j ≠ sU → j ≠ sP → S₄ j = S₃ j := by
    intro j hu hp; rw [← hS4]; exact pushBoth_ne blank endSym hu hp S₃
  have hulen : ((w'.take h).drop (h - s)).length = s := by
    rw [List.length_drop, hxlen]; omega
  have hvlen : (w'.take (h - s)).length = h - s := by
    simp only [List.length_take]; omega
  -- フェーズ 5
  obtain ⟨S₅, hS5⟩ : ∃ T, run blank (settle blank sU s) S₄ = T := ⟨_, rfl⟩
  have p5U : Tape.SeqView blank (S₅ sU)
      (startSym :: ((w'.take h).reverse.take s ++ [endSym])) 1 := by
    rw [← hS5]
    have := settle_spec blank sU (n := s) p4U
      (by simp only [List.length_append, List.length_cons, List.length_nil, hulen])
    simpa [← hueq] using this
  have p5ne : ∀ j : Fin 12, j ≠ sU → S₅ j = S₄ j := by
    intro j hu; rw [← hS5]; exact settle_untouched blank hu _ _
  -- フェーズ 6
  obtain ⟨S₆, hS6⟩ : ∃ T, run blank (settle blank sP (h - s)) S₅ = T := ⟨_, rfl⟩
  have p6P : Tape.SeqView blank (S₆ sP)
      (startSym :: ((w'.take h).reverse.drop s ++ [endSym])) 1 := by
    rw [← hS6]
    have hp5 : Tape.StackView blank (S₅ sP) (endSym :: (w'.take (h - s) ++ [startSym])) := by
      rw [p5ne sP (by decide)]; exact p4P
    have := settle_spec blank sP (n := h - s) hp5
      (by simp only [List.length_append, List.length_cons, List.length_nil, hvlen])
    simpa [← hveq] using this
  have p6ne : ∀ j : Fin 12, j ≠ sP → S₆ j = S₅ j := by
    intro j hp; rw [← hS6]; exact settle_untouched blank hp _ _
  have hkeep : ∀ j : Fin 12, j ≠ sU → j ≠ sP → j ≠ sIn → j ≠ sCs → j ≠ sC2 → S₆ j = S j := by
    intro j hu hp hi hcs hc2
    rw [p6ne j hp, p5ne j hu, p4ne j hu hp, p3ne j hi hp, p2ne j hi hu hcs hc2, p1ne j hu hp]
  have hC2' : Tape.CounterView' blank mark (S₆ sC2) 0 := by
    rw [p6ne sC2 (by decide), p5ne sC2 (by decide), p4ne sC2 (by decide) (by decide),
      p3ne sC2 (by decide) (by decide)]
    exact p2C2
  obtain ⟨q1, q2, q3, _qlen, qne⟩ := kLoop_spec (blank := blank) (mark := mark) k S₆ p₁ 0
    (by rw [hkeep sC1 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hC1)
    hC2'
    (by rw [hkeep sAn (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hAn)
  have hrun : setupTapesL blank startSym endSym s (h - s) k S
      = run blank (kLoop blank k S₆) S₆ := by
    have hS2' : runG blank (phase2Acts blank s) S₁ = S₂ := hS2
    simp only [setupTapesL]; rw [hS1, hS2', hS3, hS4, hS5, hS6]
  refine ⟨⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩, ?_, ?_⟩
  · show Tape.SeqView blank (setupTapesL blank startSym endSym s (h - s) k S sP) _ (0 + 1)
    rw [hrun, qne sP (by decide) (by decide) (by decide), Nat.zero_add]
    exact p6P
  · show Tape.SeqView blank (setupTapesL blank startSym endSym s (h - s) k S sT) _ (0 + 0)
    rw [hrun, qne sT (by decide) (by decide) (by decide), Nat.zero_add,
      hkeep sT (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hT
  · show Tape.CounterView' blank mark (setupTapesL blank startSym endSym s (h - s) k S sC1) p₁
    rw [hrun]; exact q1
  · show Tape.CounterView' blank mark (setupTapesL blank startSym endSym s (h - s) k S sC2) 0
    rw [hrun]; exact q2
  · show Tape.CounterView' blank mark
      (setupTapesL blank startSym endSym s (h - s) k S sAp) (0 - k * p₁)
    rw [hrun, qne sAp (by decide) (by decide) (by decide),
      hkeep sAp (by decide) (by decide) (by decide) (by decide) (by decide), Nat.zero_sub]
    exact hAp
  · show Tape.CounterView' blank mark
      (setupTapesL blank startSym endSym s (h - s) k S sAn) (k * p₁ - 0)
    rw [hrun, Nat.sub_zero]
    simpa using q3
  · show Tape.CounterView' blank mark (setupTapesL blank startSym endSym s (h - s) k S sRp) (r - 0)
    rw [hrun, qne sRp (by decide) (by decide) (by decide),
      hkeep sRp (by decide) (by decide) (by decide) (by decide) (by decide), Nat.sub_zero]
    exact hRp
  · show Tape.CounterView' blank mark (setupTapesL blank startSym endSym s (h - s) k S sRn) (0 - r)
    rw [hrun, qne sRn (by decide) (by decide) (by decide),
      hkeep sRn (by decide) (by decide) (by decide) (by decide) (by decide), Nat.zero_sub]
    exact hRn
  · show Tape.SeqView blank (setupTapesL blank startSym endSym s (h - s) k S sU) _ (0 + 1)
    rw [hrun, qne sU (by decide) (by decide) (by decide), Nat.zero_add, p6ne sU (by decide)]
    exact p5U
  · show Tape.SeqView blank (setupTapesL blank startSym endSym s (h - s) k S sX2) _ (0 - _ + 0)
    rw [hrun, qne sX2 (by decide) (by decide) (by decide),
      hkeep sX2 (by decide) (by decide) (by decide) (by decide) (by decide), Nat.zero_sub,
      Nat.zero_add]
    exact hX2

#print axioms setupProgL_spec

end Twelve

end PalPeg.PatternProg
