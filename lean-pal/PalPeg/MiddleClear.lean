import PalPeg.BorderJobTapes

/-!
# `MiddleClear`：段テープ `P` / `U` / `Cnt` を「新品」に戻す動作列

`MiddleTapes.DecompOnTapes` の `pat` / `upat` / `cnt` は、入口の仮定が
`ScratchBlank`（作業テープだけが空白）では弱すぎて**居住者を持たない**
（`PalPeg.DecompInstance.decompOnTapes_isEmpty`）。段テープ `P` / `U` / `Cnt` に前段の
語が残っていると、`Cd * L + Dd` 動作では消せないからである。

そこで入口条件を `EntryBlank`（作業テープに加えて `P` / `U` / `Cnt` も空スタック）へ
強め、各段の**終わり**に `P` / `U` / `Cnt` を空白へ戻す動作列を挟む。本ファイルは
その消去動作列と、費用を押さえるための不変条件 `Near` を与える。

* `Near blank tp m` — 「左文脈の長さは `m` 以下、右文脈は `m` 番目から先が空白」。
  空スタックから `m` 動作を実行した直後のテープは必ずこれを満たす（`Near.step`）。
* `clearP` / `clearU` / `clearCnt` — 長さ `5 * m + 4` の消去動作列。`Near … m` の
  テープを `Tape.StackView blank … []` へ戻す。
-/

namespace PalPeg
namespace MiddleClear

open PegSeparation.RealTimeTM
open PalPeg.BorderTapes

variable {sc : ℕ}

/-! ## §1 一本のテープの上での掃き出し -/

/-- `replicate` の前に同じ記号を足す。 -/
theorem replicate_append_cons (b : Fin sc) (r : List (Fin sc)) :
    ∀ n, List.replicate n b ++ b :: r = b :: (List.replicate n b ++ r) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.cons_append, ih, List.cons_append]

/-- `tail` と `drop` の交換。 -/
theorem tail_drop_comm (r : List (Fin sc)) (n : ℕ) : r.tail.drop n = r.drop (n + 1) := by
  cases r <;> simp

/-- 空白を書きながら左へ `n` セル。 -/
def runL (blank : Fin sc) : TapeConfiguration sc → ℕ → TapeConfiguration sc
  | tp, 0 => tp
  | tp, n + 1 => runL blank (Tape.step blank tp blank .left) n

/-- 空白を書きながら右へ `n` セル。 -/
def runR (blank : Fin sc) : TapeConfiguration sc → ℕ → TapeConfiguration sc
  | tp, 0 => tp
  | tp, n + 1 => runR blank (Tape.step blank tp blank .right) n

/-- 左端で空白を書き続けても動かない。 -/
theorem runL_edge (blank : Fin sc) (r : List (Fin sc)) :
    ∀ n, runL blank ⟨[], blank, r⟩ n = ⟨[], blank, r⟩ := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [runL, Tape.step_left_of_left_nil (by rfl)]
    exact ih

/-- **左掃き**：左文脈より長く掃けば、左端に空白の頭で立ち、掃いた分は空白になる。 -/
theorem runL_spec (blank : Fin sc) :
    ∀ (n : ℕ) (l : List (Fin sc)) (f : Fin sc) (r : List (Fin sc)), l.length ≤ n →
      runL blank ⟨l, f, r⟩ (n + 1) = ⟨[], blank, List.replicate l.length blank ++ r⟩ := by
  intro n
  induction n with
  | zero =>
    intro l f r hl
    have hl0 : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hl0
    rw [runL, Tape.step_left_of_left_nil (by rfl)]
    simp [runL]
  | succ n ih =>
    intro l f r hl
    match l with
    | [] =>
      rw [runL, Tape.step_left_of_left_nil (by rfl), runL_edge]
      simp
    | a :: l' =>
      rw [runL, Tape.step_left_of_left_cons (a := blank) (n := a) (l := l') (by rfl),
        ih l' a (blank :: r) (by simpa using hl)]
      simp only [List.length_cons, List.replicate_succ, List.cons_append,
        replicate_append_cons]

/-- **右掃き**：右へ `n + 1` セル進むと、左文脈は空白 `n + 1` 個ぶん伸びる。 -/
theorem runR_spec (blank : Fin sc) :
    ∀ (n : ℕ) (l : List (Fin sc)) (f : Fin sc) (r : List (Fin sc)),
      runR blank ⟨l, f, r⟩ (n + 1)
        = ⟨List.replicate (n + 1) blank ++ l, (r.drop n).headD blank, (r.drop n).tail⟩ := by
  intro n
  induction n with
  | zero => intro l f r; simp [runR, Tape.step_right]
  | succ n ih =>
    intro l f r
    rw [runR, Tape.step_right]
    show runR blank ⟨blank :: l, r.headD blank, r.tail⟩ (n + 1) = _
    rw [ih (blank :: l) (r.headD blank) r.tail]
    have hd : r.tail.drop n = r.drop (n + 1) := tail_drop_comm r n
    have hrep : List.replicate (n + 1) blank ++ blank :: l
        = List.replicate (n + 1 + 1) blank ++ l := by
      rw [replicate_append_cons]
      simp [List.replicate_succ]
    rw [hd, hrep]

/-! ## §2 「`m` 動作しか経っていない」不変条件 -/

/-- `m` 動作ぶんしか離れていないテープ：左文脈は `m` 以下、右文脈は `m` 番目から空白。 -/
structure Near (blank : Fin sc) (tp : TapeConfiguration sc) (m : ℕ) : Prop where
  left_le : tp.left.length ≤ m
  right_blanks : Tape.Blanks blank (tp.right.drop m)

theorem blanks_drop_mono {blank : Fin sc} {l : List (Fin sc)} {m m' : ℕ} (h : m ≤ m')
    (hb : Tape.Blanks blank (l.drop m)) : Tape.Blanks blank (l.drop m') := by
  intro s hs
  refine hb s ?_
  obtain ⟨d, rfl⟩ : ∃ d, m' = m + d := ⟨m' - m, by omega⟩
  rw [← List.drop_drop] at hs
  exact List.mem_of_mem_drop hs

theorem Near.mono {blank : Fin sc} {tp : TapeConfiguration sc} {m m' : ℕ}
    (h : Near blank tp m) (hm : m ≤ m') : Near blank tp m' :=
  ⟨le_trans h.left_le hm, blanks_drop_mono hm h.right_blanks⟩

/-- 空スタックは `Near … 0`。 -/
theorem Near.of_stack {blank : Fin sc} {tp : TapeConfiguration sc}
    (h : Tape.StackView blank tp []) : Near blank tp 0 :=
  ⟨by rw [h.left_eq]; simp, by simpa using h.right_blanks⟩

/-- 1 動作で `m` は 1 しか増えない。 -/
theorem Near.step {blank : Fin sc} {tp : TapeConfiguration sc} {m : ℕ}
    (h : Near blank tp m) (a : Fin sc) (mv : Move) :
    Near blank (Tape.step blank tp a mv) (m + 1) := by
  cases mv with
  | stay =>
    refine ⟨?_, ?_⟩
    · show tp.left.length ≤ m + 1
      have := h.left_le; omega
    · show Tape.Blanks blank (tp.right.drop (m + 1))
      exact blanks_drop_mono (by omega) h.right_blanks
  | right =>
    refine ⟨?_, ?_⟩
    · rw [Tape.step_right]; simp only [List.length_cons]; have := h.left_le; omega
    · rw [Tape.step_right]
      show Tape.Blanks blank (tp.right.tail.drop (m + 1))
      have hd : tp.right.tail.drop (m + 1) = tp.right.drop (m + 2) :=
        tail_drop_comm tp.right (m + 1)
      rw [hd]
      exact blanks_drop_mono (by omega) h.right_blanks
  | left =>
    match hl : tp.left with
    | [] =>
      rw [Tape.step_left_of_left_nil hl]
      exact ⟨by simp, blanks_drop_mono (by omega) h.right_blanks⟩
    | b :: l =>
      rw [Tape.step_left_of_left_cons hl]
      refine ⟨by simp only []; have := h.left_le; rw [hl] at this; simp at this; omega, ?_⟩
      show Tape.Blanks blank ((a :: tp.right).drop (m + 1))
      rw [List.drop_succ_cons]
      exact h.right_blanks

/-! ## §3 消去プログラムとその仕様 -/

/-- テープ 1 本の消去プログラムの長さ。 -/
def clearLen (m : ℕ) : ℕ := 5 * m + 4

/-- **消去の仕様**：`Near … m` のテープは `(m+1) + (2m+1) + (2m+2)` 動作で空スタックへ戻る。 -/
theorem clear_spec {blank : Fin sc} {tp : TapeConfiguration sc} {m : ℕ} (h : Near blank tp m) :
    Tape.StackView blank
      (runL blank (runR blank (runL blank tp (m + 1)) (2 * m + 1)) (2 * m + 2)) [] := by
  obtain ⟨l, f, r⟩ := tp
  have hl : l.length ≤ m := h.left_le
  have hr : Tape.Blanks blank (r.drop m) := h.right_blanks
  rw [runL_spec blank m l f r hl]
  set r1 := List.replicate l.length blank ++ r with hr1
  have hr1b : Tape.Blanks blank (r1.drop (2 * m)) := by
    have hdrop : r1.drop (2 * m) = r.drop (2 * m - l.length) := by
      rw [hr1, List.drop_append, List.drop_eq_nil_of_le (by simp; omega)]
      simp
    rw [hdrop]
    exact blanks_drop_mono (by omega) hr
  rw [runR_spec blank (2 * m) [] blank r1]
  have hfocus : (r1.drop (2 * m)).headD blank = blank := by
    cases hc : r1.drop (2 * m) with
    | nil => simp
    | cons a t => simpa [hc] using hr1b a (by rw [hc]; simp)
  rw [hfocus]
  have hlen : (List.replicate (2 * m + 1) blank ++ ([] : List (Fin sc))).length ≤ 2 * m + 1 := by
    simp
  rw [runL_spec blank (2 * m + 1) _ blank _ hlen]
  refine ⟨rfl, rfl, ?_⟩
  intro s hs
  rcases List.mem_append.1 hs with hs | hs
  · exact List.eq_of_mem_replicate hs
  · exact hr1b s (List.mem_of_mem_drop (by simpa using hs))

/-! ## §4 段テープ `P` / `U` / `Cnt` の消去動作列 -/

section Acts

variable (blank : Fin sc)

/-- `P` を空白で掃く動作列（1 方向）。 -/
def sweepP (mv : Move) (n : ℕ) : List (Act sc) := List.replicate n (Act.Pset blank mv)

/-- `U` を空白で掃く動作列（1 方向）。 -/
def sweepU (mv : Move) (n : ℕ) : List (Act sc) := List.replicate n (Act.Uset blank mv)

/-- `Cnt` を空白で掃く動作列（1 方向）。 -/
def sweepC (mv : Move) (n : ℕ) : List (Act sc) := List.replicate n (Act.C blank mv)

theorem sweepP_left_apply (n : ℕ) (ts : OvTapes sc) :
    applyActs blank (sweepP blank .left n) ts = { ts with P := runL blank ts.P n } := by
  induction n generalizing ts with
  | zero => rfl
  | succ n ih =>
    rw [sweepP, List.replicate_succ, applyActs_cons]
    show applyActs blank (sweepP blank .left n) _ = _
    rw [ih]
    rfl

theorem sweepP_right_apply (n : ℕ) (ts : OvTapes sc) :
    applyActs blank (sweepP blank .right n) ts = { ts with P := runR blank ts.P n } := by
  induction n generalizing ts with
  | zero => rfl
  | succ n ih =>
    rw [sweepP, List.replicate_succ, applyActs_cons]
    show applyActs blank (sweepP blank .right n) _ = _
    rw [ih]
    rfl

theorem sweepU_left_apply (n : ℕ) (ts : OvTapes sc) :
    applyActs blank (sweepU blank .left n) ts = { ts with U := runL blank ts.U n } := by
  induction n generalizing ts with
  | zero => rfl
  | succ n ih =>
    rw [sweepU, List.replicate_succ, applyActs_cons]
    show applyActs blank (sweepU blank .left n) _ = _
    rw [ih]
    rfl

theorem sweepU_right_apply (n : ℕ) (ts : OvTapes sc) :
    applyActs blank (sweepU blank .right n) ts = { ts with U := runR blank ts.U n } := by
  induction n generalizing ts with
  | zero => rfl
  | succ n ih =>
    rw [sweepU, List.replicate_succ, applyActs_cons]
    show applyActs blank (sweepU blank .right n) _ = _
    rw [ih]
    rfl

theorem sweepC_left_apply (n : ℕ) (ts : OvTapes sc) :
    applyActs blank (sweepC blank .left n) ts = { ts with Cnt := runL blank ts.Cnt n } := by
  induction n generalizing ts with
  | zero => rfl
  | succ n ih =>
    rw [sweepC, List.replicate_succ, applyActs_cons]
    show applyActs blank (sweepC blank .left n) _ = _
    rw [ih]
    rfl

theorem sweepC_right_apply (n : ℕ) (ts : OvTapes sc) :
    applyActs blank (sweepC blank .right n) ts = { ts with Cnt := runR blank ts.Cnt n } := by
  induction n generalizing ts with
  | zero => rfl
  | succ n ih =>
    rw [sweepC, List.replicate_succ, applyActs_cons]
    show applyActs blank (sweepC blank .right n) _ = _
    rw [ih]
    rfl

/-- **段テープの消去動作列**：`P` / `U` / `Cnt` を順に掃き出す。 -/
def clearPUC (m : ℕ) : List (Act sc) :=
  (sweepP blank .left (m + 1) ++ sweepP blank .right (2 * m + 1) ++
      sweepP blank .left (2 * m + 2)) ++
  (sweepU blank .left (m + 1) ++ sweepU blank .right (2 * m + 1) ++
      sweepU blank .left (2 * m + 2)) ++
  (sweepC blank .left (m + 1) ++ sweepC blank .right (2 * m + 1) ++
      sweepC blank .left (2 * m + 2))

theorem clearPUC_length (m : ℕ) : (clearPUC blank m).length = 3 * (5 * m + 4) := by
  simp only [clearPUC, sweepP, sweepU, sweepC, List.length_append, List.length_replicate]
  omega

/-- 消去は作業テープに触れない。 -/
theorem clearPUC_noScratch (m : ℕ) : NoScratchAll (clearPUC blank m) := by
  simp only [clearPUC, sweepP, sweepU, sweepC]
  refine noScratchAll_append (noScratchAll_append ?_ ?_) ?_ <;>
    refine noScratchAll_append (noScratchAll_append ?_ ?_) ?_ <;>
    exact noScratchAll_replicate (by trivial) _

/-- 消去後のテープ束（`X` / `X2` / `F` と作業テープはそのまま）。 -/
theorem clearPUC_apply (m : ℕ) (ts : OvTapes sc) :
    applyActs blank (clearPUC blank m) ts
      = { ts with
          P := runL blank (runR blank (runL blank ts.P (m + 1)) (2 * m + 1)) (2 * m + 2)
          U := runL blank (runR blank (runL blank ts.U (m + 1)) (2 * m + 1)) (2 * m + 2)
          Cnt := runL blank (runR blank (runL blank ts.Cnt (m + 1)) (2 * m + 1))
            (2 * m + 2) } := by
  simp only [clearPUC, applyActs_append, sweepP_left_apply, sweepP_right_apply,
    sweepU_left_apply, sweepU_right_apply, sweepC_left_apply, sweepC_right_apply]

@[simp] theorem clearPUC_X (m : ℕ) (ts : OvTapes sc) :
    (applyActs blank (clearPUC blank m) ts).X = ts.X := by rw [clearPUC_apply]

@[simp] theorem clearPUC_X2 (m : ℕ) (ts : OvTapes sc) :
    (applyActs blank (clearPUC blank m) ts).X2 = ts.X2 := by rw [clearPUC_apply]

@[simp] theorem clearPUC_F (m : ℕ) (ts : OvTapes sc) :
    (applyActs blank (clearPUC blank m) ts).F = ts.F := by rw [clearPUC_apply]

/-- **消去の主定理**：`m` 動作しか離れていない段テープは空スタックへ戻る。 -/
theorem clearPUC_stack (m : ℕ) (ts : OvTapes sc)
    (hP : Near blank ts.P m) (hU : Near blank ts.U m) (hC : Near blank ts.Cnt m) :
    Tape.StackView blank (applyActs blank (clearPUC blank m) ts).P [] ∧
      Tape.StackView blank (applyActs blank (clearPUC blank m) ts).U [] ∧
        Tape.StackView blank (applyActs blank (clearPUC blank m) ts).Cnt [] := by
  rw [clearPUC_apply]
  exact ⟨clear_spec hP, clear_spec hU, clear_spec hC⟩

end Acts

/-! ## §5 動作列を流したあとの `Near` -/

/-- 1 動作で `P` / `U` / `Cnt` の `Near` の添字は 1 しか増えない。 -/
theorem near_applyAct {blank : Fin sc} {ts : OvTapes sc} {m : ℕ} (a : Act sc)
    (hP : Near blank ts.P m) (hU : Near blank ts.U m) (hC : Near blank ts.Cnt m) :
    Near blank (applyAct blank ts a).P (m + 1) ∧ Near blank (applyAct blank ts a).U (m + 1)
      ∧ Near blank (applyAct blank ts a).Cnt (m + 1) := by
  cases a <;>
    exact ⟨by first | exact hP.step _ _ | exact hP.mono (by omega),
      by first | exact hU.step _ _ | exact hU.mono (by omega),
      by first | exact hC.step _ _ | exact hC.mono (by omega)⟩

/-- 動作列を流すと、`Near` の添字は動作数だけ増える。 -/
theorem near_applyActs {blank : Fin sc} :
    ∀ (l : List (Act sc)) (ts : OvTapes sc) (m : ℕ),
      Near blank ts.P m → Near blank ts.U m → Near blank ts.Cnt m →
      Near blank (applyActs blank l ts).P (m + l.length) ∧
        Near blank (applyActs blank l ts).U (m + l.length) ∧
          Near blank (applyActs blank l ts).Cnt (m + l.length) := by
  intro l
  induction l with
  | nil => intro ts m hP hU hC; exact ⟨hP.mono (by omega), hU.mono (by omega), hC.mono (by omega)⟩
  | cons a l ih =>
    intro ts m hP hU hC
    obtain ⟨h1, h2, h3⟩ := near_applyAct (blank := blank) (ts := ts) (m := m) a hP hU hC
    rw [applyActs_cons]
    obtain ⟨g1, g2, g3⟩ := ih (applyAct blank ts a) (m + 1) h1 h2 h3
    exact ⟨g1.mono (by simp; omega), g2.mono (by simp; omega), g3.mono (by simp; omega)⟩

end MiddleClear
end PalPeg
