import PalPeg.Prologue
import PalPeg.FullMachineTapes

/-!
# `ClearAny`：形に依存しない全消去プログラム

`FullMachineTapes.clear_fits`（および `Prologue.clearTape` / `spreadClear`）は、消去対象の
テープが `StackView` 形（左文脈がスタック内容そのもの、右文脈が全て空白）であることを
前提にしている。本ファイルでは、その仮定を外し、**任意の形のテープ**を空白テープへ戻す
プログラムを構成する。

* `width`     — テープの非空白セル候補数の目安（左右文脈の長さの和）。
* `width_step` / `width_runProg` — 1 行動・プログラム実行での増分は高々 1 / プログラム長。
* `clearAny`  — 任意のテープを `StackView blank _ []` へ戻すプログラム。長さは
  `3 * width tp + 3` 以下。
* `clearAny_chunks` — 上のプログラムを `c + 1` 動作以下のチャンクへ分割できること
  （`Prologue.chunkList` と `FullMachineTapes.chunkList_length_le` を再利用）。
-/

namespace PalPeg
namespace ClearAny

open PegSeparation.RealTimeTM
open PalPeg.Tape

variable {k : ℕ}

/-! ## 1. `width`：左右文脈の長さの和 -/

/-- テープの左右文脈（フォーカスを除く）の長さの和。 -/
def width (tp : TapeConfiguration k) : ℕ := tp.left.length + tp.right.length

/-- 1 行動で `width` は高々 1 しか増えない（`stay` は不変、`left`/`right` は増減が
互いに打ち消し合うか、左端規則により不変）。 -/
theorem width_step (blank : Fin k) (tp : TapeConfiguration k) (a : Fin k) (m : Move) :
    width (step blank tp a m) ≤ width tp + 1 := by
  cases m with
  | stay => simp [width, step_stay]
  | right =>
      simp only [width, step_right, List.length_cons, List.length_tail]
      omega
  | left =>
      cases hl : tp.left with
      | nil =>
          rw [step_left_of_left_nil hl]
          simp [width, hl]
      | cons n l =>
          rw [step_left_of_left_cons hl]
          simp only [width, hl, List.length_cons]
          omega

/-- プログラム実行での `width` の増分はプログラム長以下。 -/
theorem width_runProg (blank : Fin k) (tp : TapeConfiguration k) (p : GSTapes.TapeProg k) :
    width (GSTapes.runProg blank tp p) ≤ width tp + p.length := by
  induction p generalizing tp with
  | nil => simp [GSTapes.runProg]
  | cons hd tl ih =>
      obtain ⟨a, m⟩ := hd
      rw [GSTapes.runProg_cons]
      have h1 := width_step blank tp a m
      have h2 := ih (step blank tp a m)
      simp only [List.length_cons]
      omega

/-! ## 2. 片方向への「書きながら掃く」プログラム -/

/-- 左へ `n` 回、その都度空白を書きながら動く。 -/
def leftBlankProg (blank : Fin k) : ℕ → GSTapes.TapeProg k
  | 0 => []
  | n + 1 => (blank, Move.left) :: leftBlankProg blank n

@[simp] theorem leftBlankProg_length (blank : Fin k) (n : ℕ) :
    (leftBlankProg blank n).length = n := by
  induction n with
  | zero => simp [leftBlankProg]
  | succ n ih => simp [leftBlankProg, ih]

/-- 右へ `n` 回、その都度空白を書きながら動く。 -/
def rightBlankProg (blank : Fin k) : ℕ → GSTapes.TapeProg k
  | 0 => []
  | n + 1 => (blank, Move.right) :: rightBlankProg blank n

@[simp] theorem rightBlankProg_length (blank : Fin k) (n : ℕ) :
    (rightBlankProg blank n).length = n := by
  induction n with
  | zero => simp [rightBlankProg]
  | succ n ih => simp [rightBlankProg, ih]

/-- `replicate n a ++ (a :: r) = replicate (n + 1) a ++ r`。 -/
private theorem replicate_succ_append {α : Type*} (n : ℕ) (a : α) (r : List α) :
    List.replicate n a ++ (a :: r) = List.replicate (n + 1) a ++ r := by
  rw [List.replicate_succ']
  simp [List.append_assoc]

/-- **左掃き（+1 版）**：左文脈の長さ `+1` 回だけ左へ空白を書きながら動くと、左端に達し、
フォーカスも空白になる（左端規則が最後の 1 手で残った汚れを上書きする）。
フォーカスの初期値は任意でよい。 -/
theorem leftSweep_core (blank : Fin k) :
    ∀ (l : List (Fin k)) (f : Fin k) (r : List (Fin k)),
      GSTapes.runProg blank ⟨l, f, r⟩ (leftBlankProg blank (l.length + 1)) =
        ⟨[], blank, List.replicate l.length blank ++ r⟩ := by
  intro l
  induction l with
  | nil =>
      intro f r
      show GSTapes.runProg blank ⟨[], f, r⟩ (leftBlankProg blank 1) = _
      simp only [leftBlankProg, GSTapes.runProg_cons, GSTapes.runProg_nil]
      rw [step_left_of_left_nil (tp := (⟨[], f, r⟩ : TapeConfiguration k)) rfl]
      simp
  | cons x xs ih =>
      intro f r
      show GSTapes.runProg blank ⟨x :: xs, f, r⟩ (leftBlankProg blank (xs.length + 1 + 1)) = _
      rw [show xs.length + 1 + 1 = (xs.length + 1) + 1 from rfl, leftBlankProg,
        GSTapes.runProg_cons]
      rw [step_left_of_left_cons (tp := (⟨x :: xs, f, r⟩ : TapeConfiguration k)) rfl]
      rw [ih x (blank :: r)]
      simp only [List.length_cons]
      rw [replicate_succ_append]

/-- **右掃き（+1 版）**：右文脈の長さ `+1` 回だけ右へ空白を書きながら動くと、右文脈が
尽き、左文脈の先頭に空白の列が積まれ、フォーカスも空白になる。フォーカスの初期値は
任意でよい。 -/
theorem rightSweep_core (blank : Fin k) :
    ∀ (r : List (Fin k)) (l : List (Fin k)) (f : Fin k),
      GSTapes.runProg blank ⟨l, f, r⟩ (rightBlankProg blank (r.length + 1)) =
        ⟨List.replicate (r.length + 1) blank ++ l, blank, []⟩ := by
  intro r
  induction r with
  | nil =>
      intro l f
      show GSTapes.runProg blank ⟨l, f, []⟩ (rightBlankProg blank 1) = _
      simp only [rightBlankProg, GSTapes.runProg_cons, GSTapes.runProg_nil]
      rw [step_right (blank := blank) (tp := (⟨l, f, []⟩ : TapeConfiguration k)) blank]
      simp
  | cons x xs ih =>
      intro l f
      show GSTapes.runProg blank ⟨l, f, x :: xs⟩
          (rightBlankProg blank (xs.length + 1 + 1)) = _
      rw [show xs.length + 1 + 1 = (xs.length + 1) + 1 from rfl, rightBlankProg,
        GSTapes.runProg_cons]
      rw [step_right (blank := blank) (tp := (⟨l, f, x :: xs⟩ : TapeConfiguration k)) blank]
      simp only [List.headD_cons, List.tail_cons]
      rw [ih (blank :: l) x]
      simp only [List.length_cons]
      rw [show xs.length + 1 + 1 = xs.length + 1 + 1 from rfl]
      congr 1
      rw [show (List.replicate (xs.length + 1 + 1) blank) =
          List.replicate (xs.length + 1) blank ++ [blank] from by
            rw [← List.replicate_succ']]
      simp [List.append_assoc]

/-- **左掃き（既に全部空白の場合）**：左文脈が既にすべて空白なら、その長さちょうどの
回数だけ左へ空白を書きながら動くだけで左端に達し、フォーカスも空白のまま保たれる。 -/
theorem leftSweep_blank (blank : Fin k) :
    ∀ (l : List (Fin k)), Blanks blank l →
      ∀ (r : List (Fin k)),
        GSTapes.runProg blank ⟨l, blank, r⟩ (leftBlankProg blank l.length) =
          ⟨[], blank, List.replicate l.length blank ++ r⟩ := by
  intro l
  induction l with
  | nil =>
      intro _ r
      simp [leftBlankProg, GSTapes.runProg]
  | cons x xs ih =>
      intro hl r
      have hx : x = blank := hl x (List.mem_cons_self ..)
      have hxs : Blanks blank xs := hl.tail
      show GSTapes.runProg blank ⟨x :: xs, blank, r⟩ (leftBlankProg blank (xs.length + 1)) = _
      rw [leftBlankProg, GSTapes.runProg_cons]
      rw [step_left_of_left_cons (tp := (⟨x :: xs, blank, r⟩ : TapeConfiguration k)) rfl]
      rw [hx]
      rw [ih hxs (blank :: r)]
      simp only [List.length_cons]
      rw [replicate_succ_append]

/-! ## 3. 主定理：任意の形のテープを空白テープへ -/

/-- `StackView blank _ []`：残りの開発が「新品のテープ」として使う条件。 -/
abbrev IsBlankTape (blank : Fin k) (tp : TapeConfiguration k) : Prop :=
  StackView blank tp []

/-- **任意の形のテープを空白テープへ戻すプログラム**：長さは `3 * width tp + 3` 以下。 -/
theorem clearAny (blank : Fin k) (tp : TapeConfiguration k) :
    ∃ prog : GSTapes.TapeProg k, prog.length ≤ 3 * width tp + 3 ∧
      IsBlankTape blank (GSTapes.runProg blank tp prog) := by
  obtain ⟨L, F, R⟩ := tp
  set Lc := L.length with hLc
  set Rc := R.length with hRc
  set W := Lc + Rc with hW
  -- フェーズ 1：左端へ。
  set prog1 : GSTapes.TapeProg k := leftBlankProg blank (Lc + 1) with hprog1
  have hstep1 : GSTapes.runProg blank (⟨L, F, R⟩ : TapeConfiguration k) prog1 =
      ⟨[], blank, List.replicate Lc blank ++ R⟩ := by
    rw [hprog1, hLc]
    exact leftSweep_core blank L F R
  -- フェーズ 2：右端（尽きるまで）へ。
  set prog2 : GSTapes.TapeProg k := rightBlankProg blank (W + 1) with hprog2
  have hRlen : (List.replicate Lc blank ++ R).length = W := by
    simp [hW]; omega
  have hstep2 : GSTapes.runProg blank (⟨[], blank, List.replicate Lc blank ++ R⟩ :
      TapeConfiguration k) prog2 =
      ⟨List.replicate (W + 1) blank, blank, []⟩ := by
    rw [hprog2, ← hRlen]
    have := rightSweep_core blank (List.replicate Lc blank ++ R) [] blank
    simpa using this
  -- フェーズ 3：左端へ戻る（既に全部空白なので安全）。
  set prog3 : GSTapes.TapeProg k := leftBlankProg blank (W + 1) with hprog3
  have hblanks : Blanks blank (List.replicate (W + 1) blank) := blanks_replicate blank (W + 1)
  have hstep3 : GSTapes.runProg blank (⟨List.replicate (W + 1) blank, blank, []⟩ :
      TapeConfiguration k) prog3 =
      ⟨[], blank, List.replicate (W + 1) blank ++ []⟩ := by
    rw [hprog3]
    have := leftSweep_blank blank (List.replicate (W + 1) blank) hblanks []
    simpa using this
  refine ⟨prog1 ++ prog2 ++ prog3, ?_, ?_⟩
  · have h1 : prog1.length = Lc + 1 := by simp [hprog1]
    have h2 : prog2.length = W + 1 := by simp [hprog2]
    have h3 : prog3.length = W + 1 := by simp [hprog3]
    simp only [List.length_append, h1, h2, h3, width, hLc, hRc]
    omega
  · rw [GSTapes.runProg_append, GSTapes.runProg_append, hstep1, hstep2, hstep3]
    exact ⟨rfl, rfl, by simpa using hblanks⟩

/-! ## 4. チャンク分割 -/

/-- `clearAny` のプログラムを `c + 1` 動作以下のチャンクへ分割できる。 -/
theorem clearAny_chunks (blank : Fin k) (tp : TapeConfiguration k) (c : ℕ) :
    ∃ chunks : List (GSTapes.TapeProg k),
      (∀ q ∈ chunks, q.length ≤ c + 1) ∧
      chunks.length ≤ (3 * width tp + 3) / (c + 1) + 1 ∧
      IsBlankTape blank (chunks.foldl (fun s q => GSTapes.runProg blank s q) tp) := by
  obtain ⟨prog, hlen, hblank⟩ := clearAny blank tp
  refine ⟨Prologue.chunkList c prog, Prologue.chunkList_chunk_le c prog, ?_, ?_⟩
  · have hcount := FullMachineTapes.chunkList_length_le (k := k) c prog
    set m := (Prologue.chunkList c prog).length with hm
    set n := 3 * width tp + 3 with hn
    by_contra hcon
    push_neg at hcon
    have hdm : (c + 1) * (n / (c + 1)) + n % (c + 1) = n := Nat.div_add_mod n (c + 1)
    have hmod : n % (c + 1) < c + 1 := Nat.mod_lt n (by omega)
    nlinarith [hcount, hlen, hdm, hmod, hcon]
  · rw [← GSTapes.runProg_join, Prologue.chunkList_join]
    exact hblank

end ClearAny
end PalPeg
