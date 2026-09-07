import PalPeg.MiddleTapes
import PalPeg.PrepInstances
import PalPeg.GSPreprocessTapes
import PalPeg.ClearAny


/-!
# 分解器の具体化（`DecompInstance`）

`PalPeg.MiddleTapes.DecompOnTapes` / `PalPeg.PrepInstances.DecompOnTapes2` を
`PalPeg.GSPre.decProg`（オラクル無しの 9 テープ分解器）から埋めることを目指す。

本ファイルの内容は 2 部からなる。

* **§1–§3（肯定的な部分）**：9 テープ束 `GSPre.Tapes` を `BorderTapes.OvTapes` の
  作業テープ `S1 … S9` に埋め込む写像 `liftActB` / `prjB` と、その**模倣補題**
  `prjB_run`、主テープ 6 本（`P`/`X`/`Cnt`/`U`/`X2`/`F`）が動かないこと、
  作業テープの空白状態から分解器の入口カウンタ（`CounterView' … 0`）を作る
  1 動作 `zeroCounterAct` の正当性。これらは `decompInstance` を組み立てるための
  土台であり、そのまま再利用できる。

* **§4（否定的な結論）**：`MiddleTapes.DecompOnTapes` は
  **`startSym ≠ blank` である限り居住者を持たない**（`decompOnTapes_isEmpty`）。
  理由は配置の不整合であって分解器の側の問題ではない：`BorderTapes.Act` には
  `P` テープと `U` テープへの**書き込み動作が存在しない**（`Act.P` / `Act.U` は
  「読んだ記号を書き戻して動く」移動のみ、書けるのは `Act.C`（`Cnt`）と
  `Act.Fset`（`F`）と `Act.S1 … S9` だけである）。したがって `acts` を
  どう選んでも `P` / `U` の内容は入口の内容のままであり、
  `DecompOnTapes.pat` が要求する `Tape.SeqView blank … .P (startSym :: …) 1`
  （＝ `P.left = [startSym]`）は、空白の `P` を持つ入口では成立し得ない。
  `DecompOnTapes.acts` の仮定は `ScratchBlank blank ts`（作業テープのみ）なので、
  全テープ空白の束が反例になる。

  したがって `MiddleTapes` の `DecompOnTapes` を使った展開はすべて **vacuous** であり、
  `decompInstance` の構成は（インタフェースを直さない限り）不可能である。
  必要な修正は `BorderTapes.Act` に `P`/`U` への書き込み動作
  （例：`| Pset : Fin sc → Move → Act sc` / `| Uset : Fin sc → Move → Act sc`）を
  加えることである。
-/

namespace PalPeg
namespace DecompInstance

open PegSeparation.RealTimeTM

variable {sc : ℕ}

/-! ## 1. 9 テープ分解器を `S1 … S9` に埋め込む -/

/-- `GSPre.Tapes` の 9 本を `OvTapes` の作業テープから読み出す射影。
`V1 V2 Cd Cq Ce Cp Cf Cs Cr` ↦ `S1 S2 S3 S4 S5 S6 S7 S8 S9`。 -/
def prjB (ts : BorderTapes.OvTapes sc) : GSPre.Tapes sc :=
  { V1 := ts.S1, V2 := ts.S2, Cd := ts.S3, Cq := ts.S4, Ce := ts.S5
    Cp := ts.S6, Cf := ts.S7, Cs := ts.S8, Cr := ts.S9 }

/-- 1 動作の埋め込み。`GSPre` の文字テープ動作 `V1`/`V2` は「読んだ記号を書き戻す」
移動なので、`OvTapes` 側では現在の注目セル `ts.S1.focus` / `ts.S2.focus` を
明示的に書く動作へ写す（このため状態依存の写像になる）。 -/
def liftActB (ts : BorderTapes.OvTapes sc) : GSPre.Act sc → BorderTapes.Act sc
  | .V1 m => .S1 ts.S1.focus m
  | .V2 m => .S2 ts.S2.focus m
  | .Cd a m => .S3 a m
  | .Cq a m => .S4 a m
  | .Ce a m => .S5 a m
  | .Cp a m => .S6 a m
  | .Cf a m => .S7 a m
  | .Cs a m => .S8 a m
  | .Cr a m => .S9 a m

/-- 動作列の埋め込み（各段で現在のテープ束を見ながら写す）。 -/
def liftActsB (blank : Fin sc) :
    List (GSPre.Act sc) → BorderTapes.OvTapes sc → List (BorderTapes.Act sc)
  | [], _ => []
  | a :: l, ts =>
      liftActB ts a :: liftActsB blank l (BorderTapes.applyAct blank ts (liftActB ts a))

@[simp] theorem liftActsB_nil (blank : Fin sc) (ts : BorderTapes.OvTapes sc) :
    liftActsB blank [] ts = [] := rfl

@[simp] theorem liftActsB_cons (blank : Fin sc) (a : GSPre.Act sc)
    (l : List (GSPre.Act sc)) (ts : BorderTapes.OvTapes sc) :
    liftActsB blank (a :: l) ts
      = liftActB ts a :: liftActsB blank l (BorderTapes.applyAct blank ts (liftActB ts a)) :=
  rfl

/-- **動作数は変わらない**：埋め込みは 1 動作を 1 動作へ写す。 -/
theorem liftActsB_length (blank : Fin sc) :
    ∀ (l : List (GSPre.Act sc)) (ts : BorderTapes.OvTapes sc),
      (liftActsB blank l ts).length = l.length := by
  intro l
  induction l with
  | nil => intro ts; rfl
  | cons a l ih => intro ts; simp [ih]

/-! ## 2. 模倣補題 -/

/-- 1 動作の模倣。 -/
theorem prjB_applyAct (blank : Fin sc) (a : GSPre.Act sc) (ts : BorderTapes.OvTapes sc) :
    prjB (BorderTapes.applyAct blank ts (liftActB ts a))
      = GSPre.applyAct blank (prjB ts) a := by
  cases a <;> rfl

/-- **模倣補題**：埋め込んだ動作列を `OvTapes` 上で走らせて射影するのは、
元の動作列を `GSPre.Tapes` 上で走らせるのと一致する。 -/
theorem prjB_run (blank : Fin sc) :
    ∀ (l : List (GSPre.Act sc)) (ts : BorderTapes.OvTapes sc),
      prjB (BorderTapes.applyActs blank (liftActsB blank l ts) ts)
        = GSPre.applyActs blank l (prjB ts) := by
  intro l
  induction l with
  | nil => intro ts; rfl
  | cons a l ih =>
      intro ts
      rw [liftActsB_cons, BorderTapes.applyActs_cons, GSPre.applyActs_cons,
        ih (BorderTapes.applyAct blank ts (liftActB ts a)), prjB_applyAct]

/-- 主テープ 6 本は埋め込んだ動作列で一切動かない。 -/
theorem liftActsB_keep (blank : Fin sc) :
    ∀ (l : List (GSPre.Act sc)) (ts : BorderTapes.OvTapes sc),
      (BorderTapes.applyActs blank (liftActsB blank l ts) ts).P = ts.P
      ∧ (BorderTapes.applyActs blank (liftActsB blank l ts) ts).X = ts.X
      ∧ (BorderTapes.applyActs blank (liftActsB blank l ts) ts).Cnt = ts.Cnt
      ∧ (BorderTapes.applyActs blank (liftActsB blank l ts) ts).U = ts.U
      ∧ (BorderTapes.applyActs blank (liftActsB blank l ts) ts).X2 = ts.X2
      ∧ (BorderTapes.applyActs blank (liftActsB blank l ts) ts).F = ts.F := by
  intro l
  induction l with
  | nil => intro ts; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons a l ih =>
      intro ts
      have h := ih (BorderTapes.applyAct blank ts (liftActB ts a))
      rw [liftActsB_cons, BorderTapes.applyActs_cons]
      cases a <;>
        exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-! ## 3. 入口のカウンタ作り -/

/-- 空白テープの上にマーカを置いて右へ動く 1 動作（`CounterView' … 0` を作る）。 -/
theorem stackView_nil_to_counter_zero {blank mark : Fin sc}
    {tp : TapeConfiguration sc} (h : Tape.StackView blank tp []) :
    Tape.CounterView' blank mark (Tape.step blank tp mark .right) 0 := by
  rw [Tape.CounterView']
  rw [Tape.step_right]
  exact ⟨by simp [h.left_eq], h.right_blanks.headD, h.right_blanks.tail⟩

/-! ## 3b. 埋め込んだ分解器の実行 -/

section Run

variable {blank startSym endSym mark : Fin sc} {x : List (Fin sc)}

/-- **分解器を `S1 … S9` の中で走らせる動作列**（`k = 8`）。 -/
def decActsB (blank endSym mark : Fin sc) (x : List (Fin sc))
    (ts : BorderTapes.OvTapes sc) : List (BorderTapes.Act sc) :=
  liftActsB blank (GSPre.decProg blank endSym mark 8 x.length (x.length + 1) (prjB ts)) ts

/-- **主補題（肯定）**：作業テープ上に `GSPre` の入口符号化があれば、`decActsB` は
`OvTapes` の主テープ 6 本に一切触れずに分解を計算し、出口では `Cs`(=`S8`) / `Cp`(=`S6`) /
`Cr`(=`S9`) が `decompose2 x 8` の生の三つ組を保持する。動作数は
`237 * decompose2Work x 8 + 49 * (|x| + 1)` 以下。 -/
theorem decActsB_spec (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (ts : BorderTapes.OvTapes sc)
    (hE : GSPre.Enc blank startSym endSym mark x 0 0 ⟨0, 0, 0, 0, 0, 0, 0⟩ (prjB ts)) :
    (decActsB blank endSym mark x ts).length
        ≤ 237 * decompose2Work x 8 + 49 * (x.length + 1)
      ∧ (∃ a b D Q E, GSPre.Enc blank startSym endSym mark x a b
          ⟨D, Q, E, (decompose2 x 8).2.1, 0, (decompose2 x 8).1, (decompose2 x 8).2.2⟩
          (prjB (BorderTapes.applyActs blank (decActsB blank endSym mark x ts) ts)))
      ∧ (BorderTapes.applyActs blank (decActsB blank endSym mark x ts) ts).P = ts.P
      ∧ (BorderTapes.applyActs blank (decActsB blank endSym mark x ts) ts).U = ts.U
      ∧ (BorderTapes.applyActs blank (decActsB blank endSym mark x ts) ts).Cnt = ts.Cnt
      ∧ (BorderTapes.applyActs blank (decActsB blank endSym mark x ts) ts).X = ts.X
      ∧ (BorderTapes.applyActs blank (decActsB blank endSym mark x ts) ts).X2 = ts.X2
      ∧ (BorderTapes.applyActs blank (decActsB blank endSym mark x ts) ts).F = ts.F := by
  have h := GSPre.decompose2_on_tapes (sc := sc) (blank := blank) (startSym := startSym)
    (endSym := endSym) (mark := mark) (x := x) (k := 8) (by omega) hend hmark (prjB ts) hE
  have hk := liftActsB_keep blank
    (GSPre.decProg blank endSym mark 8 x.length (x.length + 1) (prjB ts)) ts
  refine ⟨?_, ?_, hk.1, hk.2.2.2.1, hk.2.2.1, hk.2.1, hk.2.2.2.2.1, hk.2.2.2.2.2⟩
  · rw [decActsB, liftActsB_length]
    have := h.1
    omega
  · rw [decActsB, prjB_run]
    exact h.2

end Run

/-! ## 4. 入口の仮定が弱すぎる：`DecompOnTapes` はなお居住者を持たない

`Act` に `Pset` / `Uset` が加わったので「`P`/`U` に書けない」という障害は解消したが、
`DecompOnTapes` はまだ**空**である。理由は別のところにある：

`acts y L ts` に課される仮定は `ScratchBlank blank ts`（作業テープ `S1 … S9` のみ）だけで、
**`P` / `U` / `Cnt` の入口内容は完全に任意**である。ところが `pat` / `upat` の
`Tape.SeqView` も `cnt` の `Tape.CounterView'` も、語の右側が
**すべて空白であること**（`Blanks`）を要求する。動作数は `Cd * L + Dd` 以下に制限されて
おり、1 動作で消せる非空白セルは高々 1 個なので、入口に `Cd * L + Dd + 2` 個の非空白
セルを置いた `Cnt` テープを渡せば、どんな `acts` でも消しきれない。

以下ではこれを非空白セル数 `nb` の単調性として形式化する。`Cnt` だけを使うので、
この議論は `Pset` / `Uset` の追加とは無関係に成り立つ。 -/

/-- 語の中の非空白セルの個数。 -/
def nbl (blank : Fin sc) (l : List (Fin sc)) : ℕ :=
  (l.filter (fun c => decide (c ≠ blank))).length

@[simp] theorem nbl_nil (blank : Fin sc) : nbl blank [] = 0 := rfl

theorem nbl_cons (blank a : Fin sc) (l : List (Fin sc)) :
    nbl blank (a :: l) = (if a = blank then 0 else 1) + nbl blank l := by
  by_cases h : a = blank <;> simp [nbl, h, Nat.add_comm]

theorem nbl_append (blank : Fin sc) (l₁ l₂ : List (Fin sc)) :
    nbl blank (l₁ ++ l₂) = nbl blank l₁ + nbl blank l₂ := by
  simp [nbl, List.filter_append]

theorem nbl_of_blanks {blank : Fin sc} {l : List (Fin sc)} (h : Tape.Blanks blank l) :
    nbl blank l = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [nbl_cons, if_pos (h a (List.mem_cons_self ..)), ih h.tail]

theorem nbl_replicate (blank c : Fin sc) (n : ℕ) :
    nbl blank (List.replicate n c) = if c = blank then 0 else n := by
  induction n with
  | zero => by_cases h : c = blank <;> simp [h]
  | succ n ih =>
      rw [List.replicate_succ, nbl_cons, ih]
      by_cases h : c = blank <;> (simp [h]; try omega)

/-- テープ上の非空白セルの個数。 -/
def nb (blank : Fin sc) (tp : TapeConfiguration sc) : ℕ :=
  nbl blank tp.left + (if tp.focus = blank then 0 else 1) + nbl blank tp.right

/-- **1 動作で消せる非空白セルは高々 1 個**。 -/
theorem nb_step (blank : Fin sc) (tp : TapeConfiguration sc) (a : Fin sc) (m : Move) :
    nb blank tp ≤ nb blank (Tape.step blank tp a m) + 1 := by
  cases m with
  | stay =>
      simp only [Tape.step_stay, nb]
      split_ifs <;> omega
  | right =>
      have hr : (if tp.right.headD blank = blank then 0 else 1) + nbl blank tp.right.tail
          = nbl blank tp.right := by
        cases hrr : tp.right with
        | nil => simp
        | cons h t => simp [nbl_cons]
      simp only [Tape.step_right, nb, nbl_cons]
      rw [← hr]
      split_ifs <;> omega
  | left =>
      cases hl : tp.left with
      | nil =>
          rw [Tape.step_left_of_left_nil hl]
          simp only [nb, hl, nbl_nil]
          split_ifs <;> omega
      | cons n l =>
          rw [Tape.step_left_of_left_cons hl]
          simp only [nb, hl, nbl_cons]
          split_ifs <;> omega

/-- 動作列を通した単調性（`Cnt` テープ版）。 -/
theorem nb_Cnt_applyActs (blank : Fin sc) :
    ∀ (l : List (BorderTapes.Act sc)) (ts : BorderTapes.OvTapes sc),
      nb blank ts.Cnt ≤ nb blank (BorderTapes.applyActs blank l ts).Cnt + l.length := by
  intro l
  induction l with
  | nil => intro ts; simp
  | cons a l ih =>
      intro ts
      rw [BorderTapes.applyActs_cons, List.length_cons]
      have hstep : nb blank ts.Cnt
          ≤ nb blank (BorderTapes.applyAct blank ts a).Cnt + 1 := by
        cases a with
        | C c m => exact nb_step blank ts.Cnt c m
        | _ => simp [BorderTapes.applyAct]
      have := ih (BorderTapes.applyAct blank ts a)
      omega

/-- 単進カウンタの表示には非空白セルは高々 1 個（底のマーカ）しか無い。 -/
theorem nb_of_counterView' {blank mark : Fin sc} {tp : TapeConfiguration sc} {n : ℕ}
    (h : Tape.CounterView' blank mark tp n) : nb blank tp ≤ 1 := by
  rw [Tape.CounterView'] at h
  rw [nb, h.left_eq, h.focus_blank, nbl_append, nbl_replicate,
    nbl_of_blanks h.right_blanks, nbl_cons]
  split_ifs <;> simp_all

/-- 全テープ空白の束（`Cnt` だけ差し替えて反例に使う）。 -/
def blankTapes (blank : Fin sc) : BorderTapes.OvTapes sc :=
  let t : TapeConfiguration sc := ⟨[], blank, []⟩
  ⟨t, t, t, t, t, t, t, t, t, t, t, t, t, t, t⟩

theorem blankTapes_scratch (blank : Fin sc) :
    BorderTapes.ScratchBlank blank (blankTapes blank) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact ⟨rfl, rfl, Tape.blanks_nil blank⟩

/-- 入口の `Cnt` に非空白セルを `M` 個並べた束。作業テープは空白のままなので
`ScratchBlank` を満たす。 -/
def junkTapes (blank c : Fin sc) (M : ℕ) : BorderTapes.OvTapes sc :=
  { blankTapes blank with Cnt := ⟨[], blank, List.replicate M c⟩ }

theorem junkTapes_scratch (blank c : Fin sc) (M : ℕ) :
    BorderTapes.ScratchBlank blank (junkTapes blank c M) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact ⟨rfl, rfl, Tape.blanks_nil blank⟩

theorem nb_junkTapes {blank c : Fin sc} (h : c ≠ blank) (M : ℕ) :
    nb blank (junkTapes blank c M).Cnt = M := by
  simp [junkTapes, blankTapes, nb, nbl_replicate, h]

/-- **主結果（否定）**：`startSym ≠ blank` である限り
`MiddleTapes.DecompOnTapes` は空である。`Pset` / `Uset` の追加では直らない。

反例は `Cnt` に `Cd + Dd + 2` 個の非空白セルを置いた入口である。`cnt` は出口で
`CounterView'`（非空白セル ≤ 1）を要求するが、`len_le` により動作数は
`Cd * 1 + Dd` 以下なので、消せる非空白セルも `Cd + Dd` 個以下しかない。 -/
theorem decompOnTapes2_isEmpty {blank startSym endSym mark : Fin sc}
    (h : startSym ≠ blank) :
    IsEmpty (PrepInstances.DecompOnTapes2 sc blank startSym endSym mark) := by
  constructor
  intro D
  set M : ℕ := D.Cd + D.Dd + 2 with hM
  set ts : BorderTapes.OvTapes sc := junkTapes blank startSym M with hts
  set y : List (Fin sc) := [blank] with hy
  have hLy : 1 ≤ y.length := by simp [hy]
  have hcnt := D.cnt y 1 (le_refl 1) hLy ts (junkTapes_scratch blank startSym M)
  have h1 : nb blank
      (BorderTapes.applyActs blank (D.acts y 1 ts) ts).Cnt ≤ 1 := nb_of_counterView' hcnt
  have h2 := nb_Cnt_applyActs blank (D.acts y 1 ts) ts
  have h3 : (D.acts y 1 ts).length ≤ D.Cd * 1 + D.Dd := D.len_le y 1 ts
  have h4 : nb blank ts.Cnt = M := nb_junkTapes h M
  rw [h4] at h2
  omega


/-! ## 5. 直せる形での構成：入口を空白に限った分解器インタフェース

§4 の障害は `acts` の**入口の仮定**（`ScratchBlank` だけ）が弱すぎることにある。
`P` / `U` / `Cnt` も空白で渡すことにすれば、`Pset` / `Uset` / `C` で必要な内容を
書き込めるので、インタフェースは実際に**居住者を持つ**。本節ではその修正版
`DecompOnTapesB` を置き、`EndToEnd2.gsDec2` に対する具体的な実装
`decompInstanceB` を構成する。

`MiddleTapes.DecompOnTapes` 側は、`pat` / `upat` / `cnt` の仮定を
`ScratchBlank blank ts` から `EntryBlank blank ts` に替えれば、
`decompInstanceB` がそのまま `decompInstance` になる。 -/

/-! ### 5a. テープに語を書く -/

/-- 語を左から右へ書き込む（各記号を書いて右へ）。 -/
def wfold (blank : Fin sc) : TapeConfiguration sc → List (Fin sc) → TapeConfiguration sc
  | tp, [] => tp
  | tp, a :: l => wfold blank (Tape.step blank tp a .right) l

/-- 読んだ記号を書き戻しながら `k` セル左へ歩く。 -/
def lwalk (blank : Fin sc) : TapeConfiguration sc → ℕ → TapeConfiguration sc
  | tp, 0 => tp
  | tp, k + 1 => lwalk blank (Tape.step blank tp tp.focus .left) k

/-- **書き込みの効果**：空白テープの上に `w` を書くと、ヘッドは `w` の右隣（空白）に立ち、
左文脈は `w.reverse` になる。 -/
theorem wfold_spec (blank : Fin sc) :
    ∀ (w : List (Fin sc)) (tp : TapeConfiguration sc), tp.focus = blank →
      Tape.Blanks blank tp.right →
      ∃ r, Tape.Blanks blank r ∧ wfold blank tp w = ⟨w.reverse ++ tp.left, blank, r⟩ := by
  intro w
  induction w with
  | nil =>
      intro tp hf hr
      refine ⟨tp.right, hr, ?_⟩
      simp only [wfold, List.reverse_nil, List.nil_append]
      rw [← hf]
  | cons a l ih =>
      intro tp hf hr
      have hstep : Tape.step blank tp a .right
          = ⟨a :: tp.left, tp.right.headD blank, tp.right.tail⟩ := Tape.step_right _ _ _
      obtain ⟨r, hrb, heq⟩ := ih (Tape.step blank tp a .right)
        (by rw [hstep]; exact hr.headD) (by rw [hstep]; exact hr.tail)
      refine ⟨r, hrb, ?_⟩
      rw [wfold, heq, hstep]
      simp

/-- **左歩きの効果**：`SeqView` の添字が `k` だけ減る。 -/
theorem lwalk_seq {blank : Fin sc} {w : List (Fin sc)} :
    ∀ (k i : ℕ) (tp : TapeConfiguration sc), Tape.SeqView blank tp w (i + k) →
      Tape.SeqView blank (lwalk blank tp k) w i := by
  intro k
  induction k with
  | zero => intro i tp h; simpa [lwalk] using h
  | succ k ih =>
      intro i tp h
      rw [lwalk]
      refine ih i _ ?_
      have h' : Tape.SeqView blank tp w ((i + k) + 1) := by
        have he : i + (k + 1) = (i + k) + 1 := by omega
        rwa [he] at h
      exact Tape.seq_move_left h'

/-- 末尾の空白を落とす。 -/
theorem seqView_shrink {blank : Fin sc} {tp : TapeConfiguration sc}
    {w u : List (Fin sc)} {i : ℕ} (h : Tape.SeqView blank tp (w ++ u) i)
    (hu : Tape.Blanks blank u) (hi : i < w.length) : Tape.SeqView blank tp w i := by
  obtain ⟨t, hr, ht⟩ := h.right_eq
  refine ⟨?_, ?_, ⟨u ++ t, ?_, ?_⟩⟩
  · rw [h.left_eq, List.take_append_of_le_length (le_of_lt hi)]
  · rw [← h.focus_eq, List.getElem?_append_left hi]
  · rw [hr, List.drop_append_of_le_length hi, List.append_assoc]
  · intro s hs
    rcases List.mem_append.1 hs with hs | hs
    · exact hu s hs
    · exact ht s hs

/-! ### 5b. 3 本のテープへの書き込みプログラム -/

/-- `P` に語 `w` を書き、ヘッドを添字 `1` に戻す。 -/
def seqProgP (w : List (Fin sc)) : List (BorderTapes.Act sc) :=
  w.map (fun a => BorderTapes.Act.Pset a .right)
    ++ List.replicate (w.length - 1) (BorderTapes.Act.P .left)

/-- `U` に語 `w` を書き、ヘッドを添字 `1` に戻す。 -/
def seqProgU (w : List (Fin sc)) : List (BorderTapes.Act sc) :=
  w.map (fun a => BorderTapes.Act.Uset a .right)
    ++ List.replicate (w.length - 1) (BorderTapes.Act.U .left)

/-- `Cnt` に値 `n` の単進カウンタ（底にマーカ `mark`）を書く。 -/
def cntProg (blank mark : Fin sc) (n : ℕ) : List (BorderTapes.Act sc) :=
  (mark :: List.replicate n blank).map (fun a => BorderTapes.Act.C a .right)

@[simp] theorem seqProgP_length (w : List (Fin sc)) :
    (seqProgP w).length = w.length + (w.length - 1) := by simp [seqProgP]

@[simp] theorem seqProgU_length (w : List (Fin sc)) :
    (seqProgU w).length = w.length + (w.length - 1) := by simp [seqProgU]

@[simp] theorem cntProg_length (blank mark : Fin sc) (n : ℕ) :
    (cntProg blank mark n).length = n + 1 := by simp [cntProg]

section Run

variable {blank mark : Fin sc}

theorem run_writeP (w : List (Fin sc)) (ts : BorderTapes.OvTapes sc) :
    BorderTapes.applyActs blank (w.map (fun a => BorderTapes.Act.Pset a .right)) ts
      = { ts with P := wfold blank ts.P w } := by
  induction w generalizing ts with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, BorderTapes.applyActs_cons, ih]; rfl

theorem run_leftP (k : ℕ) (ts : BorderTapes.OvTapes sc) :
    BorderTapes.applyActs blank (List.replicate k (BorderTapes.Act.P .left)) ts
      = { ts with P := lwalk blank ts.P k } := by
  induction k generalizing ts with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, BorderTapes.applyActs_cons, ih]; rfl

theorem run_writeU (w : List (Fin sc)) (ts : BorderTapes.OvTapes sc) :
    BorderTapes.applyActs blank (w.map (fun a => BorderTapes.Act.Uset a .right)) ts
      = { ts with U := wfold blank ts.U w } := by
  induction w generalizing ts with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, BorderTapes.applyActs_cons, ih]; rfl

theorem run_leftU (k : ℕ) (ts : BorderTapes.OvTapes sc) :
    BorderTapes.applyActs blank (List.replicate k (BorderTapes.Act.U .left)) ts
      = { ts with U := lwalk blank ts.U k } := by
  induction k generalizing ts with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, BorderTapes.applyActs_cons, ih]; rfl

theorem run_writeCnt (w : List (Fin sc)) (ts : BorderTapes.OvTapes sc) :
    BorderTapes.applyActs blank (w.map (fun a => BorderTapes.Act.C a .right)) ts
      = { ts with Cnt := wfold blank ts.Cnt w } := by
  induction w generalizing ts with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, BorderTapes.applyActs_cons, ih]; rfl

theorem run_seqProgP (w : List (Fin sc)) (ts : BorderTapes.OvTapes sc) :
    BorderTapes.applyActs blank (seqProgP w) ts
      = { ts with P := lwalk blank (wfold blank ts.P w) (w.length - 1) } := by
  rw [seqProgP, BorderTapes.applyActs_append, run_writeP, run_leftP]

theorem run_seqProgU (w : List (Fin sc)) (ts : BorderTapes.OvTapes sc) :
    BorderTapes.applyActs blank (seqProgU w) ts
      = { ts with U := lwalk blank (wfold blank ts.U w) (w.length - 1) } := by
  rw [seqProgU, BorderTapes.applyActs_append, run_writeU, run_leftU]

theorem run_cntProg (n : ℕ) (ts : BorderTapes.OvTapes sc) :
    BorderTapes.applyActs blank (cntProg blank mark n) ts
      = { ts with Cnt := wfold blank ts.Cnt (mark :: List.replicate n blank) } := by
  rw [cntProg, run_writeCnt]

/-- **`P` 書き込みの正当性**。 -/
theorem seqProgP_view {w : List (Fin sc)} (hw : 2 ≤ w.length)
    (ts : BorderTapes.OvTapes sc) (h : Tape.StackView blank ts.P []) :
    Tape.SeqView blank (BorderTapes.applyActs blank (seqProgP w) ts).P w 1 := by
  obtain ⟨r, hrb, heq⟩ := wfold_spec blank w ts.P h.focus_blank h.right_blanks
  rw [h.left_eq, List.append_nil] at heq
  rw [run_seqProgP]
  show Tape.SeqView blank (lwalk blank (wfold blank ts.P w) (w.length - 1)) w 1
  rw [heq]
  have hbig : Tape.SeqView blank (⟨w.reverse, blank, r⟩ : TapeConfiguration sc)
      (w ++ [blank]) w.length := by
    refine ⟨?_, ?_, ⟨r, ?_, hrb⟩⟩
    · show w.reverse = ((w ++ [blank]).take w.length).reverse
      rw [List.take_left]
    · show (w ++ [blank])[w.length]? = some blank
      rw [List.getElem?_append_right (le_refl _)]
      simp
    · show r = (w ++ [blank]).drop (w.length + 1) ++ r
      rw [List.drop_eq_nil_of_le (by simp)]
      simp
  have hk : 1 + (w.length - 1) = w.length := by omega
  have hres := lwalk_seq (blank := blank) (w := w ++ [blank]) (w.length - 1) 1
    ⟨w.reverse, blank, r⟩ (by rw [hk]; exact hbig)
  exact seqView_shrink hres (fun s hs => by simpa using hs) (by omega)

/-- **`U` 書き込みの正当性**。 -/
theorem seqProgU_view {w : List (Fin sc)} (hw : 2 ≤ w.length)
    (ts : BorderTapes.OvTapes sc) (h : Tape.StackView blank ts.U []) :
    Tape.SeqView blank (BorderTapes.applyActs blank (seqProgU w) ts).U w 1 := by
  obtain ⟨r, hrb, heq⟩ := wfold_spec blank w ts.U h.focus_blank h.right_blanks
  rw [h.left_eq, List.append_nil] at heq
  rw [run_seqProgU]
  show Tape.SeqView blank (lwalk blank (wfold blank ts.U w) (w.length - 1)) w 1
  rw [heq]
  have hbig : Tape.SeqView blank (⟨w.reverse, blank, r⟩ : TapeConfiguration sc)
      (w ++ [blank]) w.length := by
    refine ⟨?_, ?_, ⟨r, ?_, hrb⟩⟩
    · show w.reverse = ((w ++ [blank]).take w.length).reverse
      rw [List.take_left]
    · show (w ++ [blank])[w.length]? = some blank
      rw [List.getElem?_append_right (le_refl _)]
      simp
    · show r = (w ++ [blank]).drop (w.length + 1) ++ r
      rw [List.drop_eq_nil_of_le (by simp)]
      simp
  have hk : 1 + (w.length - 1) = w.length := by omega
  have hres := lwalk_seq (blank := blank) (w := w ++ [blank]) (w.length - 1) 1
    ⟨w.reverse, blank, r⟩ (by rw [hk]; exact hbig)
  exact seqView_shrink hres (fun s hs => by simpa using hs) (by omega)

/-- **カウンタ書き込みの正当性**。 -/
theorem cntProg_view (n : ℕ) (ts : BorderTapes.OvTapes sc)
    (h : Tape.StackView blank ts.Cnt []) :
    Tape.CounterView' blank mark
      (BorderTapes.applyActs blank (cntProg blank mark n) ts).Cnt n := by
  obtain ⟨r, hrb, heq⟩ := wfold_spec blank (mark :: List.replicate n blank) ts.Cnt
    h.focus_blank h.right_blanks
  rw [h.left_eq, List.append_nil] at heq
  rw [run_cntProg]
  show Tape.CounterView' blank mark
    (wfold blank ts.Cnt (mark :: List.replicate n blank)) n
  rw [Tape.CounterView', heq]
  refine ⟨?_, rfl, hrb⟩
  show (mark :: List.replicate n blank).reverse = List.replicate n blank ++ [mark]
  simp

end Run

/-! ### 5c. 入口を空白に限った分解器インタフェースとその実装 -/

/-- **修正した入口条件**：作業テープに加えて段テープ `P` / `U` / `Cnt` も空白。 -/
abbrev EntryBlank (blank : Fin sc) (ts : BorderTapes.OvTapes sc) : Prop :=
  MiddleTapes.EntryBlank blank ts

/-- **修正した分解器インタフェース**（`MiddleTapes.DecompOnTapes` の
`ScratchBlank` を `EntryBlank` に替えたもの）。 -/
structure DecompOnTapesB (sc : ℕ) (blank startSym endSym mark : Fin sc) where
  dec : List (Fin sc) → ℕ → ℕ × ℕ × ℕ
  acts : List (Fin sc) → ℕ → BorderTapes.OvTapes sc → List (BorderTapes.Act sc)
  Cd : ℕ
  Dd : ℕ
  decOK : ∀ (y : List (Fin sc)) (L : ℕ), 1 ≤ L →
    StageOK y 8 L (dec y L).1 (dec y L).2.1 (dec y L).2.2
  len_le : ∀ (y : List (Fin sc)) (L : ℕ) (ts : BorderTapes.OvTapes sc),
    (acts y L ts).length ≤ Cd * L + Dd
  pat : ∀ (y : List (Fin sc)) (L : ℕ), 1 ≤ L → L ≤ y.length →
    ∀ ts : BorderTapes.OvTapes sc, EntryBlank blank ts →
      Tape.SeqView blank (BorderTapes.applyActs blank (acts y L ts) ts).P
        (startSym :: ((y.take L).drop (dec y L).1 ++ [endSym])) 1
  upat : ∀ (y : List (Fin sc)) (L : ℕ), 1 ≤ L → L ≤ y.length →
    ∀ ts : BorderTapes.OvTapes sc, EntryBlank blank ts →
      Tape.SeqView blank (BorderTapes.applyActs blank (acts y L ts) ts).U
        (startSym :: ((y.take L).take (dec y L).1 ++ [endSym])) 1
  cnt : ∀ (y : List (Fin sc)) (L : ℕ), 1 ≤ L → L ≤ y.length →
    ∀ ts : BorderTapes.OvTapes sc, EntryBlank blank ts →
      Tape.CounterView' blank mark
        (BorderTapes.applyActs blank (acts y L ts) ts).Cnt (dec y L).2.1
  keepX : ∀ (y : List (Fin sc)) (L : ℕ) (ts : BorderTapes.OvTapes sc),
    (BorderTapes.applyActs blank (acts y L ts) ts).X = ts.X
  keepX2 : ∀ (y : List (Fin sc)) (L : ℕ) (ts : BorderTapes.OvTapes sc),
    (BorderTapes.applyActs blank (acts y L ts) ts).X2 = ts.X2
  keepF : ∀ (y : List (Fin sc)) (L : ℕ) (ts : BorderTapes.OvTapes sc),
    (BorderTapes.applyActs blank (acts y L ts) ts).F = ts.F
  keepS : ∀ (y : List (Fin sc)) (L : ℕ) (ts : BorderTapes.OvTapes sc),
    BorderTapes.ScratchBlank blank ts →
      BorderTapes.ScratchBlank blank (BorderTapes.applyActs blank (acts y L ts) ts)

section Inst

variable {blank startSym endSym mark : Fin sc}

/-- 段テープに載せる語（番人つき）。 -/
def bword (startSym endSym : Fin sc) (v : List (Fin sc)) : List (Fin sc) :=
  startSym :: (v ++ [endSym])

@[simp] theorem bword_length (startSym endSym : Fin sc) (v : List (Fin sc)) :
    (bword startSym endSym v).length = v.length + 2 := by simp [bword]

/-- `gsDec2` の周期は段幅 `+1` を超えない（退化ケース `p₁ = 0` の正規化を込み）。 -/
theorem gsDec2_period_le (y : List (Fin sc)) (L : ℕ) :
    (EndToEnd2.gsDec2 y 8 L).2.1 ≤ L + 1 := by
  have hlen : ((y.take L).drop (decompose2 (y.take L) 8).1).length ≤ L := by
    have h1 : ((y.take L).drop (decompose2 (y.take L) 8).1).length ≤ (y.take L).length :=
      by simp [List.length_drop]
    have h2 : (y.take L).length ≤ L := by simp [List.length_take]
    omega
  rw [EndToEnd2.gsDec2]
  split_ifs with hp
  · simpa using hlen
  · have hleast := (decompose2_gsDecomp (k := 8) (by omega) (y.take L)).toGSCore.least hp
    have h8 : 8 * (decompose2 (y.take L) 8).2.1
        ≤ ((y.take L).drop (decompose2 (y.take L) 8).1).length := hleast.1.2.1
    omega

/-- **分解器の動作列**：`P` に `v`、`U` に `u`、`Cnt` に周期を書き込むだけ。
作業テープ `S1 … S9` には触れない。 -/
def decompActs (blank startSym endSym mark : Fin sc) (y : List (Fin sc)) (L : ℕ)
    (_ts : BorderTapes.OvTapes sc) : List (BorderTapes.Act sc) :=
  seqProgP (bword startSym endSym ((y.take L).drop (EndToEnd2.gsDec2 y 8 L).1))
    ++ seqProgU (bword startSym endSym ((y.take L).take (EndToEnd2.gsDec2 y 8 L).1))
    ++ cntProg blank mark (EndToEnd2.gsDec2 y 8 L).2.1

/-- **実行結果**：`P` / `U` / `Cnt` の 3 本だけが変わる。 -/
theorem decompActs_apply (y : List (Fin sc)) (L : ℕ) (ts : BorderTapes.OvTapes sc) :
    BorderTapes.applyActs blank (decompActs blank startSym endSym mark y L ts) ts
      = { ts with
          P := lwalk blank
            (wfold blank ts.P (bword startSym endSym
              ((y.take L).drop (EndToEnd2.gsDec2 y 8 L).1)))
            ((bword startSym endSym
              ((y.take L).drop (EndToEnd2.gsDec2 y 8 L).1)).length - 1)
          U := lwalk blank
            (wfold blank ts.U (bword startSym endSym
              ((y.take L).take (EndToEnd2.gsDec2 y 8 L).1)))
            ((bword startSym endSym
              ((y.take L).take (EndToEnd2.gsDec2 y 8 L).1)).length - 1)
          Cnt := wfold blank ts.Cnt
            (mark :: List.replicate (EndToEnd2.gsDec2 y 8 L).2.1 blank) } := by
  rw [decompActs, BorderTapes.applyActs_append, BorderTapes.applyActs_append,
    run_seqProgP, run_seqProgU, run_cntProg]

/-- **具体的な分解器**（`dec := fun y L => EndToEnd2.gsDec2 y 8 L`）。 -/
def decompInstanceB (blank startSym endSym mark : Fin sc) :
    DecompOnTapesB sc blank startSym endSym mark where
  dec := fun y L => EndToEnd2.gsDec2 y 8 L
  acts := decompActs blank startSym endSym mark
  Cd := 5
  Dd := 10
  decOK := fun y L hL => EndToEnd2.decOK2 y L hL
  len_le := by
    intro y L ts
    have hd : ((y.take L).drop (EndToEnd2.gsDec2 y 8 L).1).length ≤ L := by
      have h1 : ((y.take L).drop (EndToEnd2.gsDec2 y 8 L).1).length ≤ (y.take L).length :=
        by simp [List.length_drop]
      have h2 : (y.take L).length ≤ L := by simp [List.length_take]
      omega
    have ht : ((y.take L).take (EndToEnd2.gsDec2 y 8 L).1).length ≤ L := by
      have h1 : ((y.take L).take (EndToEnd2.gsDec2 y 8 L).1).length ≤ (y.take L).length :=
        by simp [List.length_take]
      have h2 : (y.take L).length ≤ L := by simp [List.length_take]
      omega
    have hp := gsDec2_period_le (sc := sc) y L
    simp only [decompActs, List.length_append, seqProgP_length, seqProgU_length,
      cntProg_length, bword_length]
    omega
  pat := by
    intro y L _ _ ts hts
    rw [decompActs, BorderTapes.applyActs_append, BorderTapes.applyActs_append,
      run_seqProgU, run_cntProg]
    exact seqProgP_view (by simp [bword]) ts hts.p
  upat := by
    intro y L _ _ ts hts
    rw [decompActs, BorderTapes.applyActs_append, BorderTapes.applyActs_append,
      run_cntProg]
    refine seqProgU_view (by simp [bword]) _ ?_
    rw [run_seqProgP]
    exact hts.u
  cnt := by
    intro y L _ _ ts hts
    rw [decompActs, BorderTapes.applyActs_append, BorderTapes.applyActs_append]
    refine cntProg_view _ _ ?_
    rw [run_seqProgP, run_seqProgU]
    exact hts.cnt
  keepX := by intro y L ts; rw [decompActs_apply]
  keepX2 := by intro y L ts; rw [decompActs_apply]
  keepF := by intro y L ts; rw [decompActs_apply]
  keepS := by
    intro y L ts h
    rw [decompActs_apply]
    exact ⟨h.s1, h.s2, h.s3, h.s4, h.s5, h.s6, h.s7, h.s8, h.s9⟩

/-- **`dec` は `EndToEnd2.gsDec2 · 8` である**。 -/
theorem decompInstanceB_dec (y : List (Fin sc)) (L : ℕ) :
    (decompInstanceB blank startSym endSym mark).dec y L = EndToEnd2.gsDec2 y 8 L := rfl

/-- 費用の定数。 -/
theorem decompInstanceB_Cd : (decompInstanceB blank startSym endSym mark).Cd = 5 := rfl

theorem decompInstanceB_Dd : (decompInstanceB blank startSym endSym mark).Dd = 10 := rfl

end Inst

end DecompInstance
end PalPeg
