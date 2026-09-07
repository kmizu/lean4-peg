import PalPeg.GSVerifierTapes
import PalPeg.TextFeed

/-!
# 段の準備フェーズのテープ実現 (`PatternTapes`)

`PalPeg.StageMatcher` の 1 つの段は、パターン

  `x = (w.take h).reverse`,  `u = x.take s`,  `v = x.drop s`

に対する GS 走査 (`GSScanTapes.Encodes'`) ＋ 接頭辞検証 (`GSVerifierTapes.VExt`) を走らせる。
本ファイルはその **準備フェーズ**、すなわち「入力コピーテープと単進カウンタから、
走査器・検証器の初期テープ配置を実際に作る」動作列を与え、その正しさとコストを示す。

## テープ配置（12 本）

* `sP … sRn` (0–7) — `GSScanTapes` の 8 本（`toGS` でそのまま `TapesState'` になる）。
* `sU`  (8)  — 検証器の接頭辞テープ。最終形は `startSym :: (u ++ [endSym])`、ヘッドは添字 `1`。
* `sX2` (9)  — 検証器のテキスト 2 本目（準備フェーズは触らない）。
* `sIn` (10) — **入力の 2 本目のコピー**。書き手が最前線に置いているテープとは別に、
               ヘッドが自由に使えるコピーを仮定する（時刻 `h` までに `w.take h` が載っている）。
* `sCs` (11) — 切断点 `s` の単進カウンタ（`CounterView'`）。

`p₁`, `r` は前処理 (`GSPreprocessTapes`) がそのまま `sC1`, `sRp` 上の単進カウンタとして
渡してくると仮定する（`Encodes'` が要求するのがまさにその 2 本だから、載せ替えは不要）。

## 手順

1. `sU`, `sP` に `startSym` を積む。
2. `sIn` のヘッドを添字 `h-1` から **左へ** 歩かせ、読んだ記号を `sU` に積む（`s` 回）。
   左へ歩くので、積まれる語は `x = (w.take h).reverse` の接頭辞、すなわち `u` になる。
3. 続けて残り `h - s` 記号を `sP` に積む（`v` が積まれる）。
4. 両者に `endSym` を積む。
5. スタックビューを逐次ビュー (`SeqView`) に橋渡しし（左へ 1 歩）、ヘッドを添字 `1` へ戻す。
6. `sC1`（値 `p₁`）を `sC2` を作業用にして `k` 回コピーし、`sAn` に `k * p₁` を作る
   （各周回で `sC1 → (sAn, sC2)`、続いて `sC2 → sC1`。周回後 `sC1 = p₁`, `sC2 = 0`）。

コストは `≤ 7 * (h + k * p₁ + 1)` 動作（`setup_cost`）。`k * p₁ ≤ |v| ≤ h` なので `O(h)`。

慣例：ループの回数はテープから読んだ値（`cval`, ヘッド位置）を引数に取る。これは
`GSScanTapes.perProgram blank mark (p1Of' ts) ts` と同じ書き方である。
-/

namespace PalPeg.PatternTapes

open PegSeparation.RealTimeTM
open PalPeg

variable {sc : ℕ}

/-! ## 0. テープ番号と動作 -/

def sP : Fin 12 := 0
def sT : Fin 12 := 1
def sC1 : Fin 12 := 2
def sC2 : Fin 12 := 3
def sAp : Fin 12 := 4
def sAn : Fin 12 := 5
def sRp : Fin 12 := 6
def sRn : Fin 12 := 7
def sU : Fin 12 := 8
def sX2 : Fin 12 := 9
def sIn : Fin 12 := 10
def sCs : Fin 12 := 11

/-- 12 本のテープ。 -/
abbrev Tapes (sc : ℕ) := Fin 12 → TapeConfiguration sc

/-- 1 本のテープへの 1 動作。 -/
inductive SAct (sc : ℕ) where
  | keep : Fin 12 → Move → SAct sc
  | put : Fin 12 → Fin sc → Move → SAct sc

/-- 動作が触るテープ。 -/
def sTape : SAct sc → Fin 12
  | .keep i _ => i
  | .put i _ _ => i

def updT (S : Tapes sc) (i : Fin 12) (tp : TapeConfiguration sc) : Tapes sc :=
  fun j => if j = i then tp else S j

@[simp] theorem updT_self (S : Tapes sc) (i : Fin 12) (tp : TapeConfiguration sc) :
    updT S i tp i = tp := by simp [updT]

theorem updT_ne {i j : Fin 12} (S : Tapes sc) (tp : TapeConfiguration sc) (h : j ≠ i) :
    updT S i tp j = S j := by simp [updT, h]

def applyS (blank : Fin sc) (S : Tapes sc) : SAct sc → Tapes sc
  | .keep i m => updT S i (Tape.step blank (S i) (S i).focus m)
  | .put i a m => updT S i (Tape.step blank (S i) a m)

/-- 動作列の実行。 -/
def run (blank : Fin sc) (l : List (SAct sc)) (S : Tapes sc) : Tapes sc :=
  l.foldl (applyS blank) S

@[simp] theorem run_nil (blank : Fin sc) (S : Tapes sc) : run blank [] S = S := rfl

@[simp] theorem run_cons (blank : Fin sc) (a : SAct sc) (l : List (SAct sc)) (S : Tapes sc) :
    run blank (a :: l) S = run blank l (applyS blank S a) := rfl

theorem run_append (blank : Fin sc) (l₁ l₂ : List (SAct sc)) (S : Tapes sc) :
    run blank (l₁ ++ l₂) S = run blank l₂ (run blank l₁ S) := by
  simp [run]

theorem applyS_put_self (blank : Fin sc) (S : Tapes sc) (i : Fin 12) (a : Fin sc) (m : Move) :
    applyS blank S (.put i a m) i = Tape.step blank (S i) a m := updT_self ..

theorem applyS_keep_self (blank : Fin sc) (S : Tapes sc) (i : Fin 12) (m : Move) :
    applyS blank S (.keep i m) i = Tape.step blank (S i) (S i).focus m := updT_self ..

theorem applyS_ne (blank : Fin sc) (S : Tapes sc) (a : SAct sc) {j : Fin 12}
    (h : j ≠ sTape a) : applyS blank S a j = S j := by
  cases a <;> exact updT_ne _ _ h

/-- 触られないテープは変わらない。 -/
theorem run_untouched (blank : Fin sc) (j : Fin 12) :
    ∀ (l : List (SAct sc)) (S : Tapes sc), (∀ a ∈ l, sTape a ≠ j) → run blank l S j = S j := by
  intro l
  induction l with
  | nil => intro S _; rfl
  | cons a l ih =>
    intro S h
    rw [run_cons, ih _ (fun b hb => h b (List.mem_cons_of_mem a hb)),
      applyS_ne blank S a (Ne.symm (h a (List.mem_cons_self ..)))]

/-- 走査段の 8 本を取り出す。 -/
def toGS (S : Tapes sc) : GSTapes.TapesState' sc :=
  fun i => S ⟨i.val, Nat.lt_of_lt_of_le i.isLt (by norm_num)⟩

@[simp] theorem toGS_P (S : Tapes sc) : toGS S GSTapes.tP = S sP := rfl
@[simp] theorem toGS_T (S : Tapes sc) : toGS S GSTapes.tT = S sT := rfl
@[simp] theorem toGS_C1 (S : Tapes sc) : toGS S GSTapes.tC1 = S sC1 := rfl
@[simp] theorem toGS_C2 (S : Tapes sc) : toGS S GSTapes.tC2 = S sC2 := rfl
@[simp] theorem toGS_Ap (S : Tapes sc) : toGS S GSTapes.tAp = S sAp := rfl
@[simp] theorem toGS_An (S : Tapes sc) : toGS S GSTapes.tAn = S sAn := rfl
@[simp] theorem toGS_Rp (S : Tapes sc) : toGS S GSTapes.tRp = S sRp := rfl
@[simp] theorem toGS_Rn (S : Tapes sc) : toGS S GSTapes.tRn = S sRn := rfl

/-- 検証器の 2 本を取り出す。 -/
def toVExt (S : Tapes sc) : GSVTapes.VExt sc := ⟨S sU, S sX2⟩

/-! ## 1. 入力コピーから積む（左へ歩く＝自動的に反転する） -/

/-- 1 記号ぶん：`i` が読んでいる記号を `j` に積み、`i` を左へ 1 歩。 -/
def copyRound (i j : Fin 12) (S : Tapes sc) : List (SAct sc) :=
  [SAct.put j (Tape.read (S i)) .right, SAct.keep i .left]

/-- `n` 記号ぶん。 -/
def copyLoop (blank : Fin sc) (i j : Fin 12) : ℕ → Tapes sc → List (SAct sc)
  | 0, _ => []
  | n + 1, S => copyRound i j S ++ copyLoop blank i j n (run blank (copyRound i j S) S)

theorem copyLoop_length (blank : Fin sc) (i j : Fin 12) :
    ∀ (n : ℕ) (S : Tapes sc), (copyLoop blank i j n S).length = 2 * n := by
  intro n
  induction n with
  | zero => intro S; rfl
  | succ n ih =>
    intro S
    rw [copyLoop, List.length_append, ih]
    simp [copyRound]
    omega

theorem copyLoop_untouched (blank : Fin sc) {i j l : Fin 12} (hi : l ≠ i) (hj : l ≠ j) :
    ∀ (n : ℕ) (S : Tapes sc), run blank (copyLoop blank i j n S) S l = S l := by
  intro n
  induction n with
  | zero => intro S; rfl
  | succ n ih =>
    intro S
    rw [copyLoop, run_append, ih]
    refine run_untouched blank l _ S (fun a ha => ?_)
    rcases List.mem_cons.1 ha with h | h
    · subst h; exact Ne.symm hj
    · rcases List.mem_cons.1 h with h | h
      · subst h; exact Ne.symm hi
      · simp at h

/-- **主補題**：`i` のヘッドを添字 `b` から左へ `n` 歩ぶん歩かせながら `j` に積むと、
`j` には `w[b-n+1], …, w[b]`（最上段が `w[b-n+1]`）が積まれ、`i` のヘッドは `b - n` に来る。
テープのセルとしては `x = (w.take h).reverse` の向きに並ぶ。 -/
theorem copyLoop_spec (blank : Fin sc) {i j : Fin 12} (hij : j ≠ i) :
    ∀ (n b : ℕ) (S : Tapes sc) (w l : List (Fin sc)), n ≤ b + 1 →
      Tape.SeqView blank (S i) w b → Tape.StackView blank (S j) l →
      Tape.SeqView blank (run blank (copyLoop blank i j n S) S i) w (b - n) ∧
        Tape.StackView blank (run blank (copyLoop blank i j n S) S j)
          (((w.take (b + 1)).drop (b + 1 - n)) ++ l) := by
  intro n
  induction n with
  | zero =>
    intro b S w l _ hs hst
    have hz : run blank (copyLoop blank i j 0 S) S = S := rfl
    rw [hz]
    refine ⟨by simpa using hs, ?_⟩
    have hnil : (w.take (b + 1)).drop (b + 1) = [] := by
      refine List.drop_eq_nil_of_le ?_
      simp
    simp [hnil] at hst ⊢
    exact hst
  | succ n ih =>
    intro b S w l hn hs hst
    have hnb : n ≤ b := by omega
    have hblt : b < w.length := hs.lt
    -- 1 周回後の状態
    set S₁ := run blank (copyRound i j S) S with hS₁
    have hS₁i : S₁ i = Tape.step blank (S i) (S i).focus .left := by
      rw [hS₁, copyRound]
      show applyS blank (applyS blank S (SAct.put j (Tape.read (S i)) .right)) (SAct.keep i .left) i
        = _
      rw [applyS_keep_self, applyS_ne blank S (SAct.put j (Tape.read (S i)) .right) (Ne.symm hij)]
    have hS₁j : S₁ j = Tape.step blank (S j) (S i).focus .right := by
      rw [hS₁, copyRound]
      show applyS blank (applyS blank S (SAct.put j (Tape.read (S i)) .right)) (SAct.keep i .left) j
        = _
      rw [applyS_ne blank _ (SAct.keep i .left) hij, applyS_put_self]
      rfl
    have hstack : Tape.StackView blank (S₁ j) ((S i).focus :: l) := by
      rw [hS₁j]; exact Tape.push_spec hst _
    have hseq : Tape.SeqView blank (S₁ i) w (b - 1) := by
      rw [hS₁i]
      cases b with
      | zero => exact Tape.seq_move_left_edge hs
      | succ c => exact Tape.seq_move_left hs
    have hrun : run blank (copyLoop blank i j (n + 1) S) S
        = run blank (copyLoop blank i j n S₁) S₁ := by
      rw [copyLoop, run_append]
    obtain ⟨h1, h2⟩ := ih (b - 1) S₁ w ((S i).focus :: l) (by omega) hseq hstack
    rw [hrun]
    refine ⟨by simpa [Nat.sub_sub, Nat.add_comm] using h1, ?_⟩
    have hfocus : w[b]? = some (S i).focus := hs.focus_eq
    have htake : w.take (b + 1) = w.take b ++ [(S i).focus] := by
      rw [List.take_add_one, hfocus]; rfl
    have hlen : (w.take b).length = b := by
      simp only [List.length_take]; omega
    have hdrop : (w.take (b + 1)).drop (b - n) = (w.take b).drop (b - n) ++ [(S i).focus] := by
      rw [htake, List.drop_append_of_le_length (by rw [hlen]; omega)]
    have key : ((w.take (b - 1 + 1)).drop (b - 1 + 1 - n)) ++ ((S i).focus :: l)
        = ((w.take (b + 1)).drop (b + 1 - (n + 1))) ++ l := by
      rcases Nat.eq_zero_or_pos b with rfl | hbpos
      · have hn0 : n = 0 := by omega
        subst hn0
        simp [htake]
      · rw [show b - 1 + 1 = b from by omega, show b + 1 - (n + 1) = b - n from by omega, hdrop]
        simp
    rw [← key]
    exact h2

/-! ## 2. スタックビューから逐次ビューへ（ヘッドを添字 `1` へ戻す） -/

/-- 積み終えたスタックを 1 歩左へ動かすと、セルに並んだ語 `(a :: l).reverse` の
添字 `|l|` を見る逐次ビューになる。 -/
theorem stack_to_seq {blank : Fin sc} {tp : TapeConfiguration sc} {a : Fin sc}
    {l : List (Fin sc)} (h : Tape.StackView blank tp (a :: l)) :
    Tape.SeqView blank (Tape.step blank tp blank .left) ((a :: l).reverse) l.length := by
  have htop := Tape.pop_spec h
  refine ⟨?_, ?_, ⟨(Tape.step blank tp blank .left).right, ?_, htop.right_blanks⟩⟩
  · rw [htop.left_eq, List.reverse_cons]
    rw [show l.length = l.reverse.length from (List.length_reverse ..).symm, List.take_left]
    exact (List.reverse_reverse l).symm
  · rw [htop.focus_eq, List.reverse_cons,
      show l.length = l.reverse.length from (List.length_reverse ..).symm,
      List.getElem?_append_right (Nat.le_refl _)]
    simp
  · rw [show ((a :: l).reverse).drop (l.length + 1) = [] from
      List.drop_eq_nil_of_le (by simp), List.nil_append]

/-- ヘッドを左へ `n` 歩（読んだ記号を書き戻す）。 -/
def leftWalk (i : Fin 12) (n : ℕ) : List (SAct sc) := List.replicate n (SAct.keep i .left)

@[simp] theorem leftWalk_length (i : Fin 12) (n : ℕ) : (leftWalk (sc := sc) i n).length = n := by
  simp [leftWalk]

theorem leftWalk_untouched (blank : Fin sc) {i j : Fin 12} (h : j ≠ i) (n : ℕ) (S : Tapes sc) :
    run blank (leftWalk i n) S j = S j := by
  refine run_untouched blank j _ S (fun a ha => ?_)
  rw [List.eq_of_mem_replicate ha]
  exact Ne.symm h

theorem leftWalk_spec (blank : Fin sc) (i : Fin 12) :
    ∀ (n m : ℕ) (S : Tapes sc) (w : List (Fin sc)),
      Tape.SeqView blank (S i) w (m + n) →
      Tape.SeqView blank (run blank (leftWalk i n) S i) w m := by
  intro n
  induction n with
  | zero => intro m S w h; simpa [leftWalk] using h
  | succ n ih =>
    intro m S w h
    have hstep : run blank (leftWalk (sc := sc) i (n + 1)) S
        = run blank (leftWalk i n) (applyS blank S (SAct.keep i .left)) := by
      rw [leftWalk, List.replicate_succ, run_cons, leftWalk]
    rw [hstep]
    refine ih m _ w ?_
    rw [applyS_keep_self]
    exact Tape.seq_move_left (by rw [show m + n + 1 = m + (n + 1) from by omega]; exact h)

/-- 積み終えたスタックを逐次ビューに直し、ヘッドを添字 `1` に置く動作列。 -/
def settle (blank : Fin sc) (i : Fin 12) (n : ℕ) : List (SAct sc) :=
  SAct.put i blank .left :: leftWalk i n

@[simp] theorem settle_length (blank : Fin sc) (i : Fin 12) (n : ℕ) :
    (settle (sc := sc) blank i n).length = n + 1 := by simp [settle]

theorem settle_untouched (blank : Fin sc) {i j : Fin 12} (h : j ≠ i) (n : ℕ) (S : Tapes sc) :
    run blank (settle blank i n) S j = S j := by
  rw [settle, run_cons, leftWalk_untouched blank h, applyS_ne blank S _ h]

theorem settle_spec (blank : Fin sc) (i : Fin 12) {S : Tapes sc} {a : Fin sc}
    {l : List (Fin sc)} {n : ℕ} (h : Tape.StackView blank (S i) (a :: l))
    (hn : l.length = n + 1) :
    Tape.SeqView blank (run blank (settle blank i n) S i) ((a :: l).reverse) 1 := by
  rw [settle, run_cons]
  refine leftWalk_spec blank i n 1 _ _ ?_
  rw [applyS_put_self, show 1 + n = l.length from by omega]
  exact stack_to_seq h

/-! ## 3. 単進カウンタの転送 -/

def decActs (blank : Fin sc) (i : Fin 12) : List (SAct sc) :=
  [SAct.put i blank .left, SAct.put i blank .stay]

def incAct (blank : Fin sc) (i : Fin 12) : SAct sc := SAct.put i blank .right

/-- 1 減らして 2 本に 1 ずつ足す（4 動作）。 -/
def xfer2Round (blank : Fin sc) (a b c : Fin 12) : List (SAct sc) :=
  decActs blank a ++ [incAct blank b, incAct blank c]

def xfer2 (blank : Fin sc) (a b c : Fin 12) : ℕ → List (SAct sc)
  | 0 => []
  | n + 1 => xfer2Round blank a b c ++ xfer2 blank a b c n

/-- 1 減らして 1 本に 1 足す（3 動作）。 -/
def xfer1Round (blank : Fin sc) (a b : Fin 12) : List (SAct sc) :=
  decActs blank a ++ [incAct blank b]

def xfer1 (blank : Fin sc) (a b : Fin 12) : ℕ → List (SAct sc)
  | 0 => []
  | n + 1 => xfer1Round blank a b ++ xfer1 blank a b n

theorem xfer2_length (blank : Fin sc) (a b c : Fin 12) (n : ℕ) :
    (xfer2 blank a b c n).length = 4 * n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [xfer2, List.length_append, ih]; simp [xfer2Round, decActs]; omega

theorem xfer1_length (blank : Fin sc) (a b : Fin 12) (n : ℕ) :
    (xfer1 blank a b n).length = 3 * n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [xfer1, List.length_append, ih]; simp [xfer1Round, decActs]; omega

theorem xfer2_untouched (blank : Fin sc) {a b c j : Fin 12} (ha : j ≠ a) (hb : j ≠ b)
    (hc : j ≠ c) : ∀ (n : ℕ) (S : Tapes sc), run blank (xfer2 blank a b c n) S j = S j := by
  intro n
  induction n with
  | zero => intro S; rfl
  | succ n ih =>
    intro S
    rw [xfer2, run_append, ih]
    refine run_untouched blank j _ S (fun x hx => ?_)
    simp only [xfer2Round, decActs, incAct, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h <;> subst h <;>
      simp only [sTape] <;> [exact Ne.symm ha; exact Ne.symm ha; exact Ne.symm hb;
        exact Ne.symm hc]

theorem xfer1_untouched (blank : Fin sc) {a b j : Fin 12} (ha : j ≠ a) (hb : j ≠ b) :
    ∀ (n : ℕ) (S : Tapes sc), run blank (xfer1 blank a b n) S j = S j := by
  intro n
  induction n with
  | zero => intro S; rfl
  | succ n ih =>
    intro S
    rw [xfer1, run_append, ih]
    refine run_untouched blank j _ S (fun x hx => ?_)
    simp only [xfer1Round, decActs, incAct, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h <;> subst h <;>
      simp only [sTape] <;> [exact Ne.symm ha; exact Ne.symm ha; exact Ne.symm hb]

section Xfer

variable {blank mark : Fin sc} {a b c : Fin 12}

theorem xfer2Round_a (hab : a ≠ b) (hac : a ≠ c) (S : Tapes sc) :
    run blank (xfer2Round blank a b c) S a
      = Tape.step blank (Tape.step blank (S a) blank .left) blank .stay := by
  simp [xfer2Round, decActs, incAct, run, applyS, updT, hab, hac,
    Ne.symm hab, Ne.symm hac]

theorem xfer2Round_b (hab : a ≠ b) (hbc : b ≠ c) (S : Tapes sc) :
    run blank (xfer2Round blank a b c) S b = Tape.step blank (S b) blank .right := by
  simp [xfer2Round, decActs, incAct, run, applyS, updT, hbc, Ne.symm hab, Ne.symm hbc]

theorem xfer2Round_c (hac : a ≠ c) (hbc : b ≠ c) (S : Tapes sc) :
    run blank (xfer2Round blank a b c) S c = Tape.step blank (S c) blank .right := by
  simp [xfer2Round, decActs, incAct, run, applyS, updT, Ne.symm hac, Ne.symm hbc]

theorem xfer1Round_a (hab : a ≠ b) (S : Tapes sc) :
    run blank (xfer1Round blank a b) S a
      = Tape.step blank (Tape.step blank (S a) blank .left) blank .stay := by
  simp [xfer1Round, decActs, incAct, run, applyS, updT, Ne.symm hab, hab]

theorem xfer1Round_b (hab : a ≠ b) (S : Tapes sc) :
    run blank (xfer1Round blank a b) S b = Tape.step blank (S b) blank .right := by
  simp [xfer1Round, decActs, incAct, run, applyS, updT, Ne.symm hab]

/-- `a` を空にしながら `b`, `c` を同じだけ増やす。 -/
theorem xfer2_spec (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ (n : ℕ) (S : Tapes sc) (x y z : ℕ),
      Tape.CounterView' blank mark (S a) (x + n) →
      Tape.CounterView' blank mark (S b) y →
      Tape.CounterView' blank mark (S c) z →
      Tape.CounterView' blank mark (run blank (xfer2 blank a b c n) S a) x ∧
        Tape.CounterView' blank mark (run blank (xfer2 blank a b c n) S b) (y + n) ∧
        Tape.CounterView' blank mark (run blank (xfer2 blank a b c n) S c) (z + n) := by
  intro n
  induction n with
  | zero =>
    intro S x y z h1 h2 h3
    rw [show xfer2 blank a b c 0 = [] from rfl, run_nil]
    exact ⟨by simpa using h1, by simpa using h2, by simpa using h3⟩
  | succ n ih =>
    intro S x y z h1 h2 h3
    rw [xfer2, run_append]
    have e1 : Tape.CounterView' blank mark (run blank (xfer2Round blank a b c) S a) (x + n) := by
      rw [xfer2Round_a hab hac]
      exact Tape.counter'_dec (by rw [show x + n + 1 = x + (n + 1) from by omega]; exact h1)
    have e2 : Tape.CounterView' blank mark (run blank (xfer2Round blank a b c) S b) (y + 1) := by
      rw [xfer2Round_b hab hbc]; exact Tape.counter'_inc h2
    have e3 : Tape.CounterView' blank mark (run blank (xfer2Round blank a b c) S c) (z + 1) := by
      rw [xfer2Round_c hac hbc]; exact Tape.counter'_inc h3
    obtain ⟨g1, g2, g3⟩ := ih _ x (y + 1) (z + 1) e1 e2 e3
    exact ⟨g1, by rw [show y + (n + 1) = y + 1 + n from by omega]; exact g2,
      by rw [show z + (n + 1) = z + 1 + n from by omega]; exact g3⟩

/-- `a` を空にしながら `b` を増やす。 -/
theorem xfer1_spec (hab : a ≠ b) :
    ∀ (n : ℕ) (S : Tapes sc) (x y : ℕ),
      Tape.CounterView' blank mark (S a) (x + n) →
      Tape.CounterView' blank mark (S b) y →
      Tape.CounterView' blank mark (run blank (xfer1 blank a b n) S a) x ∧
        Tape.CounterView' blank mark (run blank (xfer1 blank a b n) S b) (y + n) := by
  intro n
  induction n with
  | zero =>
    intro S x y h1 h2
    rw [show xfer1 blank a b 0 = [] from rfl, run_nil]
    exact ⟨by simpa using h1, by simpa using h2⟩
  | succ n ih =>
    intro S x y h1 h2
    rw [xfer1, run_append]
    have e1 : Tape.CounterView' blank mark (run blank (xfer1Round blank a b) S a) (x + n) := by
      rw [xfer1Round_a hab]
      exact Tape.counter'_dec (by rw [show x + n + 1 = x + (n + 1) from by omega]; exact h1)
    have e2 : Tape.CounterView' blank mark (run blank (xfer1Round blank a b) S b) (y + 1) := by
      rw [xfer1Round_b hab]; exact Tape.counter'_inc h2
    obtain ⟨g1, g2⟩ := ih _ x (y + 1) e1 e2
    exact ⟨g1, by rw [show y + (n + 1) = y + 1 + n from by omega]; exact g2⟩

end Xfer

/-! ## 4. `sAn` に `k * p₁` を作る -/

/-- 単進カウンタの値（`GSScanTapes.p1Of'` と同じ読み方）。 -/
def cval (tp : TapeConfiguration sc) : ℕ := tp.left.length - 1

theorem cval_eq {blank mark : Fin sc} {tp : TapeConfiguration sc} {n : ℕ}
    (h : Tape.CounterView' blank mark tp n) : cval tp = n := by
  unfold cval
  rw [Tape.StackView.left_eq h]
  simp

/-- 1 周回：`sC1 → (sAn, sC2)` のあと `sC2 → sC1`。`sC1` は元に戻り `sAn` が `p₁` 増える。 -/
def kRound (blank : Fin sc) (S : Tapes sc) : List (SAct sc) :=
  xfer2 blank sC1 sAn sC2 (cval (S sC1)) ++ xfer1 blank sC2 sC1 (cval (S sC1))

def kLoop (blank : Fin sc) : ℕ → Tapes sc → List (SAct sc)
  | 0, _ => []
  | m + 1, S => kRound blank S ++ kLoop blank m (run blank (kRound blank S) S)

theorem kRound_spec {blank mark : Fin sc} {S : Tapes sc} {p y : ℕ}
    (h1 : Tape.CounterView' blank mark (S sC1) p)
    (h2 : Tape.CounterView' blank mark (S sC2) 0)
    (h3 : Tape.CounterView' blank mark (S sAn) y) :
    Tape.CounterView' blank mark (run blank (kRound blank S) S sC1) p ∧
      Tape.CounterView' blank mark (run blank (kRound blank S) S sC2) 0 ∧
      Tape.CounterView' blank mark (run blank (kRound blank S) S sAn) (y + p) ∧
      (kRound blank S).length = 7 * p ∧
      ∀ j : Fin 12, j ≠ sC1 → j ≠ sC2 → j ≠ sAn → run blank (kRound blank S) S j = S j := by
  have hp : cval (S sC1) = p := cval_eq h1
  have hkR : kRound blank S = xfer2 blank sC1 sAn sC2 p ++ xfer1 blank sC2 sC1 p := by
    rw [kRound, hp]
  obtain ⟨g1, g2, g3⟩ :=
    xfer2_spec (blank := blank) (mark := mark) (a := sC1) (b := sAn) (c := sC2)
      (by decide) (by decide) (by decide) p S 0 y 0 (by simpa using h1) h3 h2
  set T := run blank (xfer2 blank sC1 sAn sC2 p) S with hT
  obtain ⟨f1, f2⟩ :=
    xfer1_spec (blank := blank) (mark := mark) (a := sC2) (b := sC1) (by decide)
      p T 0 0 (by simpa using g3) g1
  have hrun : run blank (kRound blank S) S = run blank (xfer1 blank sC2 sC1 p) T := by
    rw [hkR, run_append]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hrun]; simpa using f2
  · rw [hrun]; exact f1
  · rw [hrun, xfer1_untouched blank (by decide) (by decide)]; exact g2
  · rw [hkR, List.length_append, xfer2_length, xfer1_length]; omega
  · intro j hj1 hj2 hj3
    rw [hrun, xfer1_untouched blank hj2 hj1, hT,
      xfer2_untouched blank hj1 hj3 hj2]

theorem kLoop_spec {blank mark : Fin sc} :
    ∀ (m : ℕ) (S : Tapes sc) (p y : ℕ),
      Tape.CounterView' blank mark (S sC1) p →
      Tape.CounterView' blank mark (S sC2) 0 →
      Tape.CounterView' blank mark (S sAn) y →
      Tape.CounterView' blank mark (run blank (kLoop blank m S) S sC1) p ∧
        Tape.CounterView' blank mark (run blank (kLoop blank m S) S sC2) 0 ∧
        Tape.CounterView' blank mark (run blank (kLoop blank m S) S sAn) (y + m * p) ∧
        (kLoop blank m S).length = 7 * (m * p) ∧
        ∀ j : Fin 12, j ≠ sC1 → j ≠ sC2 → j ≠ sAn → run blank (kLoop blank m S) S j = S j := by
  intro m
  induction m with
  | zero =>
    intro S p y h1 h2 h3
    refine ⟨by simpa [kLoop] using h1, by simpa [kLoop] using h2, ?_, by simp [kLoop], ?_⟩
    · simpa [kLoop] using h3
    · intro j _ _ _; rw [show kLoop blank 0 S = [] from rfl, run_nil]
  | succ m ih =>
    intro S p y h1 h2 h3
    obtain ⟨e1, e2, e3, elen, eun⟩ := kRound_spec h1 h2 h3
    obtain ⟨g1, g2, g3, glen, gun⟩ := ih (run blank (kRound blank S) S) p (y + p) e1 e2 e3
    have hrun : run blank (kLoop blank (m + 1) S) S
        = run blank (kLoop blank m (run blank (kRound blank S) S))
            (run blank (kRound blank S) S) := by
      rw [kLoop, run_append]
    refine ⟨by rw [hrun]; exact g1, by rw [hrun]; exact g2, ?_, ?_, ?_⟩
    · rw [hrun, show y + (m + 1) * p = y + p + m * p from by ring]; exact g3
    · rw [kLoop, List.length_append, elen, glen]; ring
    · intro j hj1 hj2 hj3
      rw [hrun, gun j hj1 hj2 hj3, eun j hj1 hj2 hj3]

/-! ## 5. 準備フェーズのプログラム -/

/-- `sU` と `sP` の両方に同じ記号を積む（`startSym` の初期化と `endSym` の封じ）。 -/
def pushBoth (a : Fin sc) : List (SAct sc) :=
  [SAct.put sU a .right, SAct.put sP a .right]

@[simp] theorem pushBoth_length (a : Fin sc) : (pushBoth (sc := sc) a).length = 2 := rfl

theorem pushBoth_U (blank a : Fin sc) (S : Tapes sc) :
    run blank (pushBoth a) S sU = Tape.step blank (S sU) a .right := by
  show applyS blank (applyS blank S (SAct.put sU a .right)) (SAct.put sP a .right) sU = _
  rw [applyS_ne blank _ _ (show sU ≠ sP by decide), applyS_put_self]

theorem pushBoth_P (blank a : Fin sc) (S : Tapes sc) :
    run blank (pushBoth a) S sP = Tape.step blank (S sP) a .right := by
  show applyS blank (applyS blank S (SAct.put sU a .right)) (SAct.put sP a .right) sP = _
  rw [applyS_put_self, applyS_ne blank _ _ (show sP ≠ sU by decide)]

theorem pushBoth_ne (blank a : Fin sc) {j : Fin 12} (hu : j ≠ sU) (hp : j ≠ sP)
    (S : Tapes sc) : run blank (pushBoth a) S j = S j := by
  refine run_untouched blank j _ S (fun x hx => ?_)
  rcases List.mem_cons.1 hx with h | h
  · subst h; exact Ne.symm hu
  · rcases List.mem_cons.1 h with h | h
    · subst h; exact Ne.symm hp
    · simp at h

/-- 動作列の逐次合成（2 番目は 1 番目の実行後の状態を見る）。 -/
def seqP (blank : Fin sc) (f g : Tapes sc → List (SAct sc)) (S : Tapes sc) : List (SAct sc) :=
  f S ++ g (run blank (f S) S)

theorem seqP_run (blank : Fin sc) (f g : Tapes sc → List (SAct sc)) (S : Tapes sc) :
    run blank (seqP blank f g S) S
      = run blank (g (run blank (f S) S)) (run blank (f S) S) := by
  rw [seqP, run_append]

theorem seqP_length (blank : Fin sc) (f g : Tapes sc → List (SAct sc)) (S : Tapes sc) :
    (seqP blank f g S).length = (f S).length + (g (run blank (f S) S)).length := by
  rw [seqP, List.length_append]

/-- **準備フェーズ全体**。 -/
def setupProgram (blank startSym endSym : Fin sc) (k : ℕ) : Tapes sc → List (SAct sc) :=
  seqP blank (fun _ => pushBoth startSym)
    (seqP blank (fun S => copyLoop blank sIn sU (cval (S sCs)) S)
      (seqP blank (fun S => copyLoop blank sIn sP ((S sIn).left.length) S)
        (seqP blank (fun _ => pushBoth endSym)
          (seqP blank (fun S => settle blank sU ((S sU).left.length - 2))
            (seqP blank (fun S => settle blank sP ((S sP).left.length - 2))
              (fun S => kLoop blank k S))))))

/-- 準備フェーズ実行後のテープ。 -/
def setupRun (blank startSym endSym : Fin sc) (k : ℕ) (S : Tapes sc) : Tapes sc :=
  run blank (setupProgram blank startSym endSym k S) S

/-! ## 6. 主定理 -/

section Setup

variable {blank startSym endSym mark leftSym : Fin sc} {k s h p₁ r : ℕ}
  {w Text : List (Fin sc)} {S : Tapes sc}

/-- 準備フェーズの入力仮定：入力の 2 本目のコピー、空の `sU`/`sP`、空白のテキスト 2 本、
そして前処理が置いた単進カウンタ（`s` は `sCs`、`p₁` は `sC1`、`r` は `sRp`）。 -/
structure SetupPre (blank mark leftSym : Fin sc) (s h p₁ r : ℕ) (w Text : List (Fin sc))
    (S : Tapes sc) : Prop where
  hpos : 0 < h
  hle : h ≤ w.length
  hcut : s < h
  inb : Tape.SeqView blank (S sIn) (leftSym :: w.take h) h
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

/-- **主定理**：準備フェーズは走査器・検証器の初期テープ配置を作り、
その動作数は `≤ 7 * (h + k * p₁ + 1)`。 -/
theorem setup_spec (H : SetupPre blank mark leftSym s h p₁ r w Text S) :
    GSVTapes.VEncodes' blank startSym endSym mark
        ((w.take h).reverse.take s) ((w.take h).reverse.drop s)
        (TextFeed.padW blank Text 0) k p₁ r
        (toGS (setupRun blank startSym endSym k S), toVExt (setupRun blank startSym endSym k S))
        (⟨0, 0⟩, 0)
      ∧ (setupProgram blank startSym endSym k S).length ≤ 7 * (h + k * p₁ + 1) := by
  obtain ⟨hpos, hle, hcut, hIn, hU, hP, hT, hX2, hCs, hC1, hC2, hAp, hAn, hRp, hRn⟩ := H
  have hxlen : (w.take h).length = h := by simp only [List.length_take]; omega
  -- 段のパターン
  have hueq : ((w.take h).drop (h - s)).reverse = (w.take h).reverse.take s := by
    rw [List.take_reverse, hxlen]
  have hveq : (w.take (h - s)).reverse = (w.take h).reverse.drop s := by
    rw [List.drop_reverse, hxlen, List.take_take, Nat.min_eq_left (by omega)]
  -- 各フェーズ後の状態
  obtain ⟨S₁, hS1⟩ : ∃ T, run blank (pushBoth startSym) S = T := ⟨_, rfl⟩
  obtain ⟨S₂, hS2⟩ : ∃ T, run blank (copyLoop blank sIn sU (cval (S₁ sCs)) S₁) S₁ = T := ⟨_, rfl⟩
  obtain ⟨S₃, hS3⟩ : ∃ T,
      run blank (copyLoop blank sIn sP ((S₂ sIn).left.length) S₂) S₂ = T := ⟨_, rfl⟩
  obtain ⟨S₄, hS4⟩ : ∃ T, run blank (pushBoth endSym) S₃ = T := ⟨_, rfl⟩
  obtain ⟨S₅, hS5⟩ : ∃ T, run blank (settle blank sU ((S₄ sU).left.length - 2)) S₄ = T := ⟨_, rfl⟩
  obtain ⟨S₆, hS6⟩ : ∃ T, run blank (settle blank sP ((S₅ sP).left.length - 2)) S₅ = T := ⟨_, rfl⟩
  -- フェーズ 1
  have p1U : Tape.StackView blank (S₁ sU) [startSym] := by
    rw [← hS1, pushBoth_U]; exact Tape.push_spec hU startSym
  have p1P : Tape.StackView blank (S₁ sP) [startSym] := by
    rw [← hS1, pushBoth_P]; exact Tape.push_spec hP startSym
  have p1ne : ∀ j : Fin 12, j ≠ sU → j ≠ sP → S₁ j = S j := by
    intro j hu hp; rw [← hS1]; exact pushBoth_ne blank startSym hu hp S
  -- フェーズ 2
  have hcs : cval (S₁ sCs) = s := by
    rw [p1ne sCs (by decide) (by decide)]; exact cval_eq hCs
  have hvlen0 : (leftSym :: w.take h).length = h + 1 := by
    simp only [List.length_cons, List.length_take]; omega
  have p2 : Tape.SeqView blank (S₂ sIn) (leftSym :: w.take h) (h - s) ∧
      Tape.StackView blank (S₂ sU)
        ((((leftSym :: w.take h).take (h + 1)).drop (h + 1 - s)) ++ [startSym]) := by
    rw [← hS2, hcs]
    exact copyLoop_spec blank (i := sIn) (j := sU) (by decide) s h S₁ (leftSym :: w.take h)
      [startSym] (by omega)
      (by rw [p1ne sIn (by decide) (by decide)]; exact hIn) p1U
  have p2ne : ∀ j : Fin 12, j ≠ sIn → j ≠ sU → S₂ j = S₁ j := by
    intro j hi hu; rw [← hS2]; exact copyLoop_untouched blank hi hu _ _
  have p2U : Tape.StackView blank (S₂ sU) ((w.take h).drop (h - s) ++ [startSym]) := by
    have := p2.2
    rwa [List.take_of_length_le (by omega : (leftSym :: w.take h).length ≤ h + 1),
      show h + 1 - s = (h - s) + 1 from by omega, List.drop_succ_cons] at this
  -- フェーズ 3
  have hn3 : (S₂ sIn).left.length = h - s := by
    rw [p2.1.left_eq]
    simp only [List.length_reverse, List.length_take]
    omega
  have p3 : Tape.SeqView blank (S₃ sIn) (leftSym :: w.take h) (h - s - (h - s)) ∧
      Tape.StackView blank (S₃ sP)
        ((((leftSym :: w.take h).take (h - s + 1)).drop (h - s + 1 - (h - s))) ++ [startSym]) := by
    rw [← hS3, hn3]
    exact copyLoop_spec blank (i := sIn) (j := sP) (by decide) (h - s) (h - s) S₂
      (leftSym :: w.take h) [startSym] (by omega) p2.1
      (by rw [p2ne sP (by decide) (by decide)]; exact p1P)
  have p3ne : ∀ j : Fin 12, j ≠ sIn → j ≠ sP → S₃ j = S₂ j := by
    intro j hi hp; rw [← hS3]; exact copyLoop_untouched blank hi hp _ _
  have p3P : Tape.StackView blank (S₃ sP) (w.take (h - s) ++ [startSym]) := by
    have := p3.2
    rwa [show h - s + 1 - (h - s) = 1 from by omega, List.take_succ_cons,
      List.drop_succ_cons, List.drop_zero, List.take_take,
      Nat.min_eq_left (by omega : h - s ≤ h)] at this
  -- フェーズ 4
  have p4U : Tape.StackView blank (S₄ sU)
      (endSym :: ((w.take h).drop (h - s) ++ [startSym])) := by
    rw [← hS4, pushBoth_U]
    exact Tape.push_spec (by rw [p3ne sU (by decide) (by decide)]; exact p2U) endSym
  have p4P : Tape.StackView blank (S₄ sP) (endSym :: (w.take (h - s) ++ [startSym])) := by
    rw [← hS4, pushBoth_P]; exact Tape.push_spec p3P endSym
  have p4ne : ∀ j : Fin 12, j ≠ sU → j ≠ sP → S₄ j = S₃ j := by
    intro j hu hp; rw [← hS4]; exact pushBoth_ne blank endSym hu hp S₃
  -- フェーズ 5
  have hulen : ((w.take h).drop (h - s)).length = s := by
    rw [List.length_drop, hxlen]; omega
  have hvlen : (w.take (h - s)).length = h - s := by
    simp only [List.length_take]; omega
  have hlen5 : (S₄ sU).left.length - 2 = s := by
    rw [p4U.left_eq]
    simp only [List.length_cons, List.length_append, List.length_nil, hulen]
    omega
  have p5U : Tape.SeqView blank (S₅ sU)
      (startSym :: ((w.take h).reverse.take s ++ [endSym])) 1 := by
    rw [← hS5, hlen5]
    have := settle_spec blank sU (n := s) p4U
      (by simp only [List.length_append, List.length_cons, List.length_nil, hulen])
    simpa [← hueq] using this
  have p5ne : ∀ j : Fin 12, j ≠ sU → S₅ j = S₄ j := by
    intro j hu; rw [← hS5]; exact settle_untouched blank hu _ _
  -- フェーズ 6
  have hlen6 : (S₅ sP).left.length - 2 = h - s := by
    rw [p5ne sP (by decide), p4P.left_eq]
    simp only [List.length_cons, List.length_append, List.length_nil, hvlen]
    omega
  have p6P : Tape.SeqView blank (S₆ sP)
      (startSym :: ((w.take h).reverse.drop s ++ [endSym])) 1 := by
    rw [← hS6, hlen6]
    have hp5 : Tape.StackView blank (S₅ sP) (endSym :: (w.take (h - s) ++ [startSym])) := by
      rw [p5ne sP (by decide)]; exact p4P
    have := settle_spec blank sP (n := h - s) hp5
      (by simp only [List.length_append, List.length_cons, List.length_nil, hvlen])
    simpa [← hveq] using this
  have p6ne : ∀ j : Fin 12, j ≠ sP → S₆ j = S₅ j := by
    intro j hp; rw [← hS6]; exact settle_untouched blank hp _ _
  -- 触られなかったテープ
  have hkeep : ∀ j : Fin 12, j ≠ sU → j ≠ sP → j ≠ sIn → S₆ j = S j := by
    intro j hu hp hi
    rw [p6ne j hp, p5ne j hu, p4ne j hu hp, p3ne j hi hp, p2ne j hi hu, p1ne j hu hp]
  -- フェーズ 7（`sAn` に `k * p₁`）
  obtain ⟨q1, q2, q3, qlen, qne⟩ := kLoop_spec (blank := blank) (mark := mark) k S₆ p₁ 0
    (by rw [hkeep sC1 (by decide) (by decide) (by decide)]; exact hC1)
    (by rw [hkeep sC2 (by decide) (by decide) (by decide)]; exact hC2)
    (by rw [hkeep sAn (by decide) (by decide) (by decide)]; exact hAn)
  -- プログラムの実行結果
  have hrun : setupRun blank startSym endSym k S = run blank (kLoop blank k S₆) S₆ := by
    simp only [setupRun, setupProgram, seqP_run, hS1, hS2, hS3, hS4, hS5, hS6]
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩, ?_, ?_⟩, ?_⟩
  · show Tape.SeqView blank (setupRun blank startSym endSym k S sP) _ (0 + 1)
    rw [hrun, qne sP (by decide) (by decide) (by decide), Nat.zero_add]
    exact p6P
  · show Tape.SeqView blank (setupRun blank startSym endSym k S sT) _ (0 + 0)
    rw [hrun, qne sT (by decide) (by decide) (by decide), Nat.zero_add,
      hkeep sT (by decide) (by decide) (by decide)]
    exact hT
  · show Tape.CounterView' blank mark (setupRun blank startSym endSym k S sC1) p₁
    rw [hrun]; exact q1
  · show Tape.CounterView' blank mark (setupRun blank startSym endSym k S sC2) 0
    rw [hrun]; exact q2
  · show Tape.CounterView' blank mark (setupRun blank startSym endSym k S sAp) (0 - k * p₁)
    rw [hrun, qne sAp (by decide) (by decide) (by decide),
      hkeep sAp (by decide) (by decide) (by decide), Nat.zero_sub]
    exact hAp
  · show Tape.CounterView' blank mark (setupRun blank startSym endSym k S sAn) (k * p₁ - 0)
    rw [hrun, Nat.sub_zero]
    simpa using q3
  · show Tape.CounterView' blank mark (setupRun blank startSym endSym k S sRp) (r - 0)
    rw [hrun, qne sRp (by decide) (by decide) (by decide),
      hkeep sRp (by decide) (by decide) (by decide), Nat.sub_zero]
    exact hRp
  · show Tape.CounterView' blank mark (setupRun blank startSym endSym k S sRn) (0 - r)
    rw [hrun, qne sRn (by decide) (by decide) (by decide),
      hkeep sRn (by decide) (by decide) (by decide), Nat.zero_sub]
    exact hRn
  · show Tape.SeqView blank (setupRun blank startSym endSym k S sU) _ (0 + 1)
    rw [hrun, qne sU (by decide) (by decide) (by decide), Nat.zero_add,
      p6ne sU (by decide)]
    exact p5U
  · show Tape.SeqView blank (setupRun blank startSym endSym k S sX2) _ (0 - _ + 0)
    rw [hrun, qne sX2 (by decide) (by decide) (by decide),
      hkeep sX2 (by decide) (by decide) (by decide), Nat.zero_sub, Nat.zero_add]
    exact hX2
  · -- コスト
    rw [setupProgram, seqP_length, hS1, seqP_length, hS2, seqP_length, hS3, seqP_length, hS4,
      seqP_length, hS5, seqP_length, hS6, pushBoth_length, copyLoop_length, copyLoop_length,
      pushBoth_length, settle_length, settle_length, qlen, hcs, hn3, hlen5, hlen6]
    omega

/-- `k * p₁ ≤ |v| ≤ h` なので、準備フェーズのコストは入力長 `h` に線形。 -/
theorem setup_cost_linear (H : SetupPre blank mark leftSym s h p₁ r w Text S) (hkp : k * p₁ ≤ h) :
    (setupProgram blank startSym endSym k S).length ≤ 21 * h := by
  have h1 := (setup_spec (startSym := startSym) (endSym := endSym) (k := k) H).2
  have h2 : 0 < h := H.hpos
  omega

end Setup

end PalPeg.PatternTapes
