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

/-! ## 4. 配置の不整合：`DecompOnTapes` は居住者を持たない -/

/-- テープが全面空白であること（ヘッド位置は任意）。 -/
def AllBlank (blank : Fin sc) (tp : TapeConfiguration sc) : Prop :=
  Tape.Blanks blank tp.left ∧ tp.focus = blank ∧ Tape.Blanks blank tp.right

/-- 「読んだ記号を書き戻す」移動は全面空白性を保つ。 -/
theorem AllBlank.step_self {blank : Fin sc} {tp : TapeConfiguration sc}
    (h : AllBlank blank tp) (m : Move) :
    AllBlank blank (Tape.step blank tp tp.focus m) := by
  obtain ⟨hl, hf, hr⟩ := h
  cases m with
  | stay => exact ⟨hl, by rw [Tape.step_stay]; exact hf, hr⟩
  | right =>
      refine ⟨?_, ?_, ?_⟩
      · simp only [Tape.step_right]
        rw [hf]; exact hl.cons
      · simp only [Tape.step_right]; exact hr.headD
      · simp only [Tape.step_right]; exact hr.tail
  | left =>
      cases hnil : tp.left with
      | nil =>
          rw [Tape.step_left_of_left_nil hnil]
          exact ⟨Tape.blanks_nil blank, hf, hr⟩
      | cons n l =>
          rw [Tape.step_left_of_left_cons hnil]
          refine ⟨?_, ?_, ?_⟩
          · exact fun s hs => hl s (by rw [hnil]; exact List.mem_cons_of_mem _ hs)
          · exact hl n (by rw [hnil]; exact List.mem_cons_self ..)
          · rw [hf] at *; exact hr.cons

/-- **`P` テープには書けない**：どの動作を実行しても `P` の全面空白性は保たれる。 -/
theorem allBlank_P_applyAct (blank : Fin sc) (ts : BorderTapes.OvTapes sc)
    (h : AllBlank blank ts.P) (a : BorderTapes.Act sc) :
    AllBlank blank (BorderTapes.applyAct blank ts a).P := by
  cases a with
  | P m => exact h.step_self m
  | _ => exact h

theorem allBlank_P_applyActs (blank : Fin sc) :
    ∀ (l : List (BorderTapes.Act sc)) (ts : BorderTapes.OvTapes sc),
      AllBlank blank ts.P → AllBlank blank (BorderTapes.applyActs blank l ts).P := by
  intro l
  induction l with
  | nil => intro ts h; exact h
  | cons a l ih =>
      intro ts h
      rw [BorderTapes.applyActs_cons]
      exact ih _ (allBlank_P_applyAct blank ts h a)

/-- **`U` テープにも書けない**。 -/
theorem allBlank_U_applyAct (blank : Fin sc) (ts : BorderTapes.OvTapes sc)
    (h : AllBlank blank ts.U) (a : BorderTapes.Act sc) :
    AllBlank blank (BorderTapes.applyAct blank ts a).U := by
  cases a with
  | U m => exact h.step_self m
  | _ => exact h

theorem allBlank_U_applyActs (blank : Fin sc) :
    ∀ (l : List (BorderTapes.Act sc)) (ts : BorderTapes.OvTapes sc),
      AllBlank blank ts.U → AllBlank blank (BorderTapes.applyActs blank l ts).U := by
  intro l
  induction l with
  | nil => intro ts h; exact h
  | cons a l ih =>
      intro ts h
      rw [BorderTapes.applyActs_cons]
      exact ih _ (allBlank_U_applyAct blank ts h a)

/-- 全テープが空白でヘッドが原点にある束。 -/
def blankTapes (blank : Fin sc) : BorderTapes.OvTapes sc :=
  let t : TapeConfiguration sc := ⟨[], blank, []⟩
  ⟨t, t, t, t, t, t, t, t, t, t, t, t, t, t, t⟩

theorem blankTapes_scratch (blank : Fin sc) :
    BorderTapes.ScratchBlank blank (blankTapes blank) :=
  by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact ⟨rfl, rfl, Tape.blanks_nil blank⟩

theorem blankTapes_P (blank : Fin sc) : AllBlank blank (blankTapes blank).P :=
  ⟨Tape.blanks_nil blank, rfl, Tape.blanks_nil blank⟩

theorem blankTapes_U (blank : Fin sc) : AllBlank blank (blankTapes blank).U :=
  ⟨Tape.blanks_nil blank, rfl, Tape.blanks_nil blank⟩

/-- **主結果（否定）**：`startSym ≠ blank` なら `MiddleTapes.DecompOnTapes` は空である。

`Act` に `P` への書き込み動作が無いので、全面空白の `P` から出発すると
`pat` が要求する `SeqView … (startSym :: …) 1`（すなわち `P.left = [startSym]`）は
作れない。 -/
theorem decompOnTapes_isEmpty {blank startSym endSym mark : Fin sc}
    (h : startSym ≠ blank) :
    IsEmpty (MiddleTapes.DecompOnTapes sc blank startSym endSym mark) := by
  constructor
  intro D
  set y : List (Fin sc) := [blank] with hy
  have hL1 : 1 ≤ 1 := le_refl 1
  have hLy : 1 ≤ y.length := by simp [hy]
  have hview := D.pat y 1 hL1 hLy (blankTapes blank) (blankTapes_scratch blank)
  have hP := allBlank_P_applyActs blank (D.acts y 1 (blankTapes blank))
    (blankTapes blank) (blankTapes_P blank)
  have hleft := hview.left_eq
  simp only [List.take_succ_cons, List.take_zero, List.reverse_cons,
    List.reverse_nil, List.nil_append] at hleft
  have : startSym = blank := by
    have hmem : startSym ∈ (BorderTapes.applyActs blank
        (D.acts y 1 (blankTapes blank)) (blankTapes blank)).P.left := by
      rw [hleft]; exact List.mem_cons_self ..
    exact hP.1 _ hmem
  exact h this

/-- `upat` からも独立に同じ矛盾が出る（`U` にも書き込み動作が無い）。 -/
theorem decompOnTapes_isEmpty_of_upat {blank startSym endSym mark : Fin sc}
    (h : startSym ≠ blank) (D : MiddleTapes.DecompOnTapes sc blank startSym endSym mark) :
    False := by
  set y : List (Fin sc) := [blank] with hy
  have hLy : 1 ≤ y.length := by simp [hy]
  have hview := D.upat y 1 (le_refl 1) hLy (blankTapes blank) (blankTapes_scratch blank)
  have hU := allBlank_U_applyActs blank (D.acts y 1 (blankTapes blank))
    (blankTapes blank) (blankTapes_U blank)
  have hleft := hview.left_eq
  simp only [List.take_succ_cons, List.take_zero, List.reverse_cons,
    List.reverse_nil, List.nil_append] at hleft
  exact h (hU.1 _ (by rw [hleft]; exact List.mem_cons_self ..))

/-- `PrepInstances.DecompOnTapes2` も同じ理由で空である
（`toDecompOnTapes` が `DecompOnTapes` を作ってしまうため）。 -/
theorem decompOnTapes2_isEmpty {blank startSym endSym mark : Fin sc}
    (h : startSym ≠ blank) :
    IsEmpty (PrepInstances.DecompOnTapes2 sc blank startSym endSym mark) := by
  constructor
  intro D
  exact (decompOnTapes_isEmpty (endSym := endSym) (mark := mark) h).false
    D.toDecompOnTapes

end DecompInstance
end PalPeg
