import PalPeg.PatternTapes
import PalPeg.InputCopy

/-!
# 2 本のソーステープからパターンを読む準備フェーズ (`PatternTapesPair`)

`PalPeg.PatternTapes` の準備フェーズは、段のパターン

  `x = (w.take h).reverse`

を **1 本**の入力コピーテープ `sIn`（`w.take h` が載っている）から読んでいた。
本ファイルはこれを **2 本**に分割する：

* `tIn` — 過去の段が凍結した古いコピー。`w.take h₀`（`h₀ = h/2` を想定）を保持し、
  ヘッドは添字 `h₀ - 1`（`SeqView`）。
* `tF`  — 16 本目の**最前線テープ**。`w[h₀ .. h)` を保持し、ヘッドは末尾のすぐ右
  （`InputCopy.FrontierView`）。

パターンを左向きに読むとは、まず `tF` をその末尾から左へ読み（`rev (w[h₀..h))`）、
`tF` を読み切ったら `tIn` を添字 `h₀ - 1` から左へ読む（`rev (w.take h₀)`）ことである：

  `rev (w.take h) = rev (w[h₀..h)) ++ rev (w.take h₀)`.
-/

namespace PalPeg.PatternTapesPair

open PegSeparation.RealTimeTM
open PalPeg

variable {sc : ℕ}

/-! ## 0. 16 本のテープと動作 -/

/-- 15 本版のテープ番号を 16 本版へ埋め込む。 -/
def inj (i : Fin 15) : Fin 16 := ⟨i.val, by omega⟩

def tP : Fin 16 := inj PatternTapes.sP
def tT : Fin 16 := inj PatternTapes.sT
def tC1 : Fin 16 := inj PatternTapes.sC1
def tC2 : Fin 16 := inj PatternTapes.sC2
def tAp : Fin 16 := inj PatternTapes.sAp
def tAn : Fin 16 := inj PatternTapes.sAn
def tRp : Fin 16 := inj PatternTapes.sRp
def tRn : Fin 16 := inj PatternTapes.sRn
def tU : Fin 16 := inj PatternTapes.sU
def tX2 : Fin 16 := inj PatternTapes.sX2
def tIn : Fin 16 := inj PatternTapes.sIn
def tCs : Fin 16 := inj PatternTapes.sCs
def tScr : Fin 16 := inj PatternTapes.sScr
def tScr2 : Fin 16 := inj PatternTapes.sScr2
def tScr3 : Fin 16 := inj PatternTapes.sScr3

/-- 16 本目：最前線テープ。 -/
def tF : Fin 16 := ⟨15, by omega⟩

/-- 16 本のテープ。 -/
abbrev Tapes16 (sc : ℕ) := Fin 16 → TapeConfiguration sc

/-- 1 本のテープへの 1 動作（16 本版）。 -/
inductive PAct (sc : ℕ) where
  | keep : Fin 16 → Move → PAct sc
  | put : Fin 16 → Fin sc → Move → PAct sc

def pTape : PAct sc → Fin 16
  | .keep i _ => i
  | .put i _ _ => i

def updP (S : Tapes16 sc) (i : Fin 16) (tp : TapeConfiguration sc) : Tapes16 sc :=
  fun j => if j = i then tp else S j

@[simp] theorem updP_self (S : Tapes16 sc) (i : Fin 16) (tp : TapeConfiguration sc) :
    updP S i tp i = tp := by simp [updP]

theorem updP_ne {i j : Fin 16} (S : Tapes16 sc) (tp : TapeConfiguration sc) (h : j ≠ i) :
    updP S i tp j = S j := by simp [updP, h]

def applyP (blank : Fin sc) (S : Tapes16 sc) : PAct sc → Tapes16 sc
  | .keep i m => updP S i (Tape.step blank (S i) (S i).focus m)
  | .put i a m => updP S i (Tape.step blank (S i) a m)

def runP (blank : Fin sc) (l : List (PAct sc)) (S : Tapes16 sc) : Tapes16 sc :=
  l.foldl (applyP blank) S

@[simp] theorem runP_nil (blank : Fin sc) (S : Tapes16 sc) : runP blank [] S = S := rfl

@[simp] theorem runP_cons (blank : Fin sc) (a : PAct sc) (l : List (PAct sc))
    (S : Tapes16 sc) : runP blank (a :: l) S = runP blank l (applyP blank S a) := rfl

theorem runP_append (blank : Fin sc) (l₁ l₂ : List (PAct sc)) (S : Tapes16 sc) :
    runP blank (l₁ ++ l₂) S = runP blank l₂ (runP blank l₁ S) := by
  simp [runP]

theorem applyP_put_self (blank : Fin sc) (S : Tapes16 sc) (i : Fin 16) (a : Fin sc) (m : Move) :
    applyP blank S (.put i a m) i = Tape.step blank (S i) a m := updP_self ..

theorem applyP_keep_self (blank : Fin sc) (S : Tapes16 sc) (i : Fin 16) (m : Move) :
    applyP blank S (.keep i m) i = Tape.step blank (S i) (S i).focus m := updP_self ..

theorem applyP_ne (blank : Fin sc) (S : Tapes16 sc) (a : PAct sc) {j : Fin 16}
    (h : j ≠ pTape a) : applyP blank S a j = S j := by
  cases a <;> exact updP_ne _ _ h

theorem runP_untouched (blank : Fin sc) (j : Fin 16) :
    ∀ (l : List (PAct sc)) (S : Tapes16 sc), (∀ a ∈ l, pTape a ≠ j) → runP blank l S j = S j := by
  intro l
  induction l with
  | nil => intro S _; rfl
  | cons a l ih =>
    intro S h
    rw [runP_cons, ih _ (fun b hb => h b (List.mem_cons_of_mem a hb)),
      applyP_ne blank S a (Ne.symm (h a (List.mem_cons_self ..)))]

/-! ## 1. 15 本版からの持ち上げ -/

/-- 15 本版の状態としての眺め。 -/
def prj (S : Tapes16 sc) : PatternTapes.Tapes sc := fun i => S (inj i)

/-- 15 本版の動作を 16 本版へ。 -/
def lift : PatternTapes.SAct sc → PAct sc
  | .keep i m => .keep (inj i) m
  | .put i a m => .put (inj i) a m

theorem inj_injective {i j : Fin 15} (h : inj i = inj j) : i = j := by
  apply Fin.ext
  simpa [inj, Fin.ext_iff] using h

theorem inj_ne_tF (i : Fin 15) : inj i ≠ tF := by
  simp only [inj, tF, Ne, Fin.ext_iff]
  omega

theorem prj_applyP (blank : Fin sc) (S : Tapes16 sc) (a : PatternTapes.SAct sc) :
    prj (applyP blank S (lift a)) = PatternTapes.applyS blank (prj S) a := by
  funext j
  cases a with
  | keep i m =>
    by_cases hj : j = i
    · subst hj
      simp [prj, lift, applyP, PatternTapes.applyS, updP, PatternTapes.updT]
    · have h1 : inj j ≠ inj i := fun h => hj (inj_injective h)
      simp [prj, lift, applyP, PatternTapes.applyS, updP, PatternTapes.updT, hj, h1]
  | put i a m =>
    by_cases hj : j = i
    · subst hj
      simp [prj, lift, applyP, PatternTapes.applyS, updP, PatternTapes.updT]
    · have h1 : inj j ≠ inj i := fun h => hj (inj_injective h)
      simp [prj, lift, applyP, PatternTapes.applyS, updP, PatternTapes.updT, hj, h1]

theorem prj_runP_map (blank : Fin sc) :
    ∀ (l : List (PatternTapes.SAct sc)) (S : Tapes16 sc),
      prj (runP blank (l.map lift) S) = PatternTapes.run blank l (prj S) := by
  intro l
  induction l with
  | nil => intro S; rfl
  | cons a l ih =>
    intro S
    rw [List.map_cons, runP_cons, ih, prj_applyP, PatternTapes.run_cons]

theorem runP_map_tF (blank : Fin sc) (l : List (PatternTapes.SAct sc)) (S : Tapes16 sc) :
    runP blank (l.map lift) S tF = S tF := by
  refine runP_untouched blank tF _ S (fun a ha => ?_)
  obtain ⟨b, _, rfl⟩ := List.mem_map.1 ha
  cases b <;> exact inj_ne_tF _

/-- 単進カウンタ作りは 15 本版をそのまま持ち上げる。 -/
def kLoopP (blank : Fin sc) (k : ℕ) (S : Tapes16 sc) : List (PAct sc) :=
  (PatternTapes.kLoop blank k (prj S)).map lift

@[simp] theorem kLoopP_length (blank : Fin sc) (k : ℕ) (S : Tapes16 sc) :
    (kLoopP blank k S).length = (PatternTapes.kLoop blank k (prj S)).length := by
  simp [kLoopP]

/-! ## 2. 左向きコピー（16 本版） -/

def copyRoundL (i j : Fin 16) (S : Tapes16 sc) : List (PAct sc) :=
  [PAct.put j (Tape.read (S i)) .right, PAct.keep i .left]

def copyLoopL (blank : Fin sc) (i j : Fin 16) : ℕ → Tapes16 sc → List (PAct sc)
  | 0, _ => []
  | n + 1, S => copyRoundL i j S ++ copyLoopL blank i j n (runP blank (copyRoundL i j S) S)

theorem copyLoopL_length (blank : Fin sc) (i j : Fin 16) :
    ∀ (n : ℕ) (S : Tapes16 sc), (copyLoopL blank i j n S).length = 2 * n := by
  intro n
  induction n with
  | zero => intro S; rfl
  | succ n ih =>
    intro S
    rw [copyLoopL, List.length_append, ih]
    simp [copyRoundL]
    omega

theorem copyLoopL_untouched (blank : Fin sc) {i j l : Fin 16} (hi : l ≠ i) (hj : l ≠ j) :
    ∀ (n : ℕ) (S : Tapes16 sc), runP blank (copyLoopL blank i j n S) S l = S l := by
  intro n
  induction n with
  | zero => intro S; rfl
  | succ n ih =>
    intro S
    rw [copyLoopL, runP_append, ih]
    refine runP_untouched blank l _ S (fun a ha => ?_)
    rcases List.mem_cons.1 ha with h | h
    · subst h; exact Ne.symm hj
    · rcases List.mem_cons.1 h with h | h
      · subst h; exact Ne.symm hi
      · simp at h

/-- `PatternTapes.copyLoop_spec` の 16 本版。 -/
theorem copyLoopL_spec (blank : Fin sc) {i j : Fin 16} (hij : j ≠ i) :
    ∀ (n b : ℕ) (S : Tapes16 sc) (w l : List (Fin sc)), n ≤ b + 1 →
      Tape.SeqView blank (S i) w b → Tape.StackView blank (S j) l →
      Tape.SeqView blank (runP blank (copyLoopL blank i j n S) S i) w (b - n) ∧
        Tape.StackView blank (runP blank (copyLoopL blank i j n S) S j)
          (((w.take (b + 1)).drop (b + 1 - n)) ++ l) := by
  intro n
  induction n with
  | zero =>
    intro b S w l _ hs hst
    have hz : runP blank (copyLoopL blank i j 0 S) S = S := rfl
    rw [hz]
    refine ⟨by simpa using hs, ?_⟩
    have hnil : (w.take (b + 1)).drop (b + 1) = [] := by
      refine List.drop_eq_nil_of_le ?_
      simp
    simp [hnil] at hst ⊢
    exact hst
  | succ n ih =>
    intro b S w l hn hs hst
    set S₁ := runP blank (copyRoundL i j S) S with hS₁
    have hS₁i : S₁ i = Tape.step blank (S i) (S i).focus .left := by
      rw [hS₁, copyRoundL]
      show applyP blank (applyP blank S (PAct.put j (Tape.read (S i)) .right))
        (PAct.keep i .left) i = _
      rw [applyP_keep_self, applyP_ne blank S (PAct.put j (Tape.read (S i)) .right)
        (Ne.symm hij)]
    have hS₁j : S₁ j = Tape.step blank (S j) (S i).focus .right := by
      rw [hS₁, copyRoundL]
      show applyP blank (applyP blank S (PAct.put j (Tape.read (S i)) .right))
        (PAct.keep i .left) j = _
      rw [applyP_ne blank _ (PAct.keep i .left) hij, applyP_put_self]
      rfl
    have hstack : Tape.StackView blank (S₁ j) ((S i).focus :: l) := by
      rw [hS₁j]; exact Tape.push_spec hst _
    have hseq : Tape.SeqView blank (S₁ i) w (b - 1) := by
      rw [hS₁i]
      cases b with
      | zero => exact Tape.seq_move_left_edge hs
      | succ c => exact Tape.seq_move_left hs
    have hrun : runP blank (copyLoopL blank i j (n + 1) S) S
        = runP blank (copyLoopL blank i j n S₁) S₁ := by
      rw [copyLoopL, runP_append]
    obtain ⟨h1, h2⟩ := ih (b - 1) S₁ w ((S i).focus :: l) (by omega) hseq hstack
    rw [hrun]
    refine ⟨by simpa [Nat.sub_sub, Nat.add_comm] using h1, ?_⟩
    have hfocus : w[b]? = some (S i).focus := hs.focus_eq
    have htake : w.take (b + 1) = w.take b ++ [(S i).focus] := by
      rw [List.take_add_one, hfocus]; rfl
    have hlen : (w.take b).length = b := by
      simp only [List.length_take]
      have := hs.lt
      omega
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

/-! ## 3. 右向きコピー -/

def copyRoundR (i j : Fin 16) (S : Tapes16 sc) : List (PAct sc) :=
  [PAct.put j (Tape.read (S i)) .right, PAct.keep i .right]

def copyLoopR (blank : Fin sc) (i j : Fin 16) : ℕ → Tapes16 sc → List (PAct sc)
  | 0, _ => []
  | n + 1, S => copyRoundR i j S ++ copyLoopR blank i j n (runP blank (copyRoundR i j S) S)

theorem copyLoopR_length (blank : Fin sc) (i j : Fin 16) :
    ∀ (n : ℕ) (S : Tapes16 sc), (copyLoopR blank i j n S).length = 2 * n := by
  intro n
  induction n with
  | zero => intro S; rfl
  | succ n ih =>
    intro S
    rw [copyLoopR, List.length_append, ih]
    simp [copyRoundR]
    omega

theorem copyLoopR_untouched (blank : Fin sc) {i j l : Fin 16} (hi : l ≠ i) (hj : l ≠ j) :
    ∀ (n : ℕ) (S : Tapes16 sc), runP blank (copyLoopR blank i j n S) S l = S l := by
  intro n
  induction n with
  | zero => intro S; rfl
  | succ n ih =>
    intro S
    rw [copyLoopR, runP_append, ih]
    refine runP_untouched blank l _ S (fun a ha => ?_)
    rcases List.mem_cons.1 ha with h | h
    · subst h; exact Ne.symm hj
    · rcases List.mem_cons.1 h with h | h
      · subst h; exact Ne.symm hi
      · simp at h

/-- 右向きコピー：`i` を添字 `b` から右へ `n` 歩読みながら `j` に積む。 -/
theorem copyLoopR_spec (blank : Fin sc) {i j : Fin 16} (hij : j ≠ i) :
    ∀ (n b : ℕ) (S : Tapes16 sc) (w l : List (Fin sc)), b + n ≤ w.length →
      (0 < n → Tape.SeqView blank (S i) w b) → Tape.StackView blank (S j) l →
      Tape.StackView blank (runP blank (copyLoopR blank i j n S) S j)
        (((w.take (b + n)).drop b).reverse ++ l) := by
  intro n
  induction n with
  | zero =>
    intro b S w l _ _ hst
    have hz : runP blank (copyLoopR blank i j 0 S) S = S := rfl
    rw [hz]
    have hnil : ((w.take (b + 0)).drop b) = [] := by
      refine List.drop_eq_nil_of_le ?_
      simp
    rw [hnil]
    simpa using hst
  | succ n ih =>
    intro b S w l hn hseq hst
    have hs : Tape.SeqView blank (S i) w b := hseq (Nat.succ_pos n)
    set S₁ := runP blank (copyRoundR i j S) S with hS₁
    have hS₁i : S₁ i = Tape.step blank (S i) (S i).focus .right := by
      rw [hS₁, copyRoundR]
      show applyP blank (applyP blank S (PAct.put j (Tape.read (S i)) .right))
        (PAct.keep i .right) i = _
      rw [applyP_keep_self, applyP_ne blank S (PAct.put j (Tape.read (S i)) .right)
        (Ne.symm hij)]
    have hS₁j : S₁ j = Tape.step blank (S j) (S i).focus .right := by
      rw [hS₁, copyRoundR]
      show applyP blank (applyP blank S (PAct.put j (Tape.read (S i)) .right))
        (PAct.keep i .right) j = _
      rw [applyP_ne blank _ (PAct.keep i .right) hij, applyP_put_self]
      rfl
    have hstack : Tape.StackView blank (S₁ j) ((S i).focus :: l) := by
      rw [hS₁j]; exact Tape.push_spec hst _
    have hnext : 0 < n → Tape.SeqView blank (S₁ i) w (b + 1) := by
      intro hnp
      rw [hS₁i]
      exact Tape.seq_move_right hs (by omega)
    have hrun : runP blank (copyLoopR blank i j (n + 1) S) S
        = runP blank (copyLoopR blank i j n S₁) S₁ := by
      rw [copyLoopR, runP_append]
    have h2 := ih (b + 1) S₁ w ((S i).focus :: l) (by omega) hnext hstack
    rw [hrun]
    have hfocus : w[b]? = some (S i).focus := hs.focus_eq
    have hlen : (w.take (b + 1 + n)).length = b + 1 + n := by
      simp only [List.length_take]; omega
    have hget : (w.take (b + 1 + n))[b]? = some (S i).focus := by
      rw [List.getElem?_take_of_lt (by omega), hfocus]
    have hsplit : (w.take (b + 1 + n)).drop b
        = (S i).focus :: (w.take (b + 1 + n)).drop (b + 1) := by
      have hb : b < (w.take (b + 1 + n)).length := by omega
      rw [List.drop_eq_getElem_cons hb]
      congr 1
      have h' := List.getElem?_eq_getElem hb
      rw [h'] at hget
      exact Option.some.inj hget
    have key : ((w.take (b + 1 + n)).drop (b + 1)).reverse ++ ((S i).focus :: l)
        = ((w.take (b + (n + 1))).drop b).reverse ++ l := by
      rw [show b + (n + 1) = b + 1 + n from by omega, hsplit]
      simp
    rw [← key]
    exact h2

/-! ## 4. 補助：左歩きと `settle`（16 本版） -/

def leftWalkP (i : Fin 16) (n : ℕ) : List (PAct sc) := List.replicate n (PAct.keep i .left)

@[simp] theorem leftWalkP_length (i : Fin 16) (n : ℕ) :
    (leftWalkP (sc := sc) i n).length = n := by simp [leftWalkP]

theorem leftWalkP_untouched (blank : Fin sc) {i j : Fin 16} (h : j ≠ i) (n : ℕ)
    (S : Tapes16 sc) : runP blank (leftWalkP i n) S j = S j := by
  refine runP_untouched blank j _ S (fun a ha => ?_)
  rw [List.eq_of_mem_replicate ha]
  exact Ne.symm h

theorem leftWalkP_spec (blank : Fin sc) (i : Fin 16) :
    ∀ (n m : ℕ) (S : Tapes16 sc) (w : List (Fin sc)),
      Tape.SeqView blank (S i) w (m + n) →
      Tape.SeqView blank (runP blank (leftWalkP i n) S i) w m := by
  intro n
  induction n with
  | zero => intro m S w h; simpa [leftWalkP] using h
  | succ n ih =>
    intro m S w h
    have hstep : runP blank (leftWalkP (sc := sc) i (n + 1)) S
        = runP blank (leftWalkP i n) (applyP blank S (PAct.keep i .left)) := by
      rw [leftWalkP, List.replicate_succ, runP_cons, leftWalkP]
    rw [hstep]
    refine ih m _ w ?_
    rw [applyP_keep_self]
    exact Tape.seq_move_left (by rw [show m + n + 1 = m + (n + 1) from by omega]; exact h)

def settleP (blank : Fin sc) (i : Fin 16) (n : ℕ) : List (PAct sc) :=
  PAct.put i blank .left :: leftWalkP i n

@[simp] theorem settleP_length (blank : Fin sc) (i : Fin 16) (n : ℕ) :
    (settleP (sc := sc) blank i n).length = n + 1 := by simp [settleP]

theorem settleP_untouched (blank : Fin sc) {i j : Fin 16} (h : j ≠ i) (n : ℕ)
    (S : Tapes16 sc) : runP blank (settleP blank i n) S j = S j := by
  rw [settleP, runP_cons, leftWalkP_untouched blank h, applyP_ne blank S _ h]

theorem settleP_spec (blank : Fin sc) (i : Fin 16) {S : Tapes16 sc} {a : Fin sc}
    {l : List (Fin sc)} {n : ℕ} (h : Tape.StackView blank (S i) (a :: l))
    (hn : l.length = n + 1) :
    Tape.SeqView blank (runP blank (settleP blank i n) S i) ((a :: l).reverse) 1 := by
  rw [settleP, runP_cons]
  refine leftWalkP_spec blank i n 1 _ _ ?_
  rw [applyP_put_self, show 1 + n = l.length from by omega]
  exact PatternTapes.stack_to_seq h

/-! ## 5. 準備フェーズのプログラム -/

/-- `tU`, `tP` に同じ記号を積む。 -/
def pushBothN (a : Fin sc) : List (PAct sc) :=
  [PAct.put tU a .right, PAct.put tP a .right]

@[simp] theorem pushBothN_length (a : Fin sc) : (pushBothN (sc := sc) a).length = 2 := rfl

theorem pushBothN_U (blank a : Fin sc) (S : Tapes16 sc) :
    runP blank (pushBothN a) S tU = Tape.step blank (S tU) a .right := by
  show applyP blank (applyP blank S (PAct.put tU a .right)) (PAct.put tP a .right) tU = _
  rw [applyP_ne blank _ _ (show tU ≠ tP by decide), applyP_put_self]

theorem pushBothN_P (blank a : Fin sc) (S : Tapes16 sc) :
    runP blank (pushBothN a) S tP = Tape.step blank (S tP) a .right := by
  show applyP blank (applyP blank S (PAct.put tU a .right)) (PAct.put tP a .right) tP = _
  rw [applyP_put_self, applyP_ne blank _ _ (show tP ≠ tU by decide)]

theorem pushBothN_ne (blank a : Fin sc) {j : Fin 16} (hu : j ≠ tU) (hp : j ≠ tP)
    (S : Tapes16 sc) : runP blank (pushBothN a) S j = S j := by
  refine runP_untouched blank j _ S (fun x hx => ?_)
  rcases List.mem_cons.1 hx with h | h
  · subst h; exact Ne.symm hu
  · rcases List.mem_cons.1 h with h | h
    · subst h; exact Ne.symm hp
    · simp at h

/-- 前置き：`tU`, `tP` に `startSym` を積み、最前線テープ `tF` を 1 歩左へ。 -/
def prologueP (blank startSym : Fin sc) : List (PAct sc) :=
  pushBothN startSym ++ [PAct.put tF blank .left]

@[simp] theorem prologueP_length (blank startSym : Fin sc) :
    (prologueP (sc := sc) blank startSym).length = 3 := rfl

/-- 4 つのコピー区間の長さ（すべてテープから読める量で決まる）。 -/
def pairCounts (S : Tapes16 sc) : ℕ × ℕ × ℕ × ℕ :=
  let s := PatternTapes.cval (S tCs)
  let m := (S tF).left.length
  let h0 := (S tIn).left.length + 1
  (min s m, s - m, m - s, h0 + m - s - (m - s))

/-- 動作列の逐次合成（`PatternTapes.seqP` の 16 本版）。 -/
def seqQ (blank : Fin sc) (f g : Tapes16 sc → List (PAct sc)) (S : Tapes16 sc) :
    List (PAct sc) := f S ++ g (runP blank (f S) S)

theorem seqQ_run (blank : Fin sc) (f g : Tapes16 sc → List (PAct sc)) (S : Tapes16 sc) :
    runP blank (seqQ blank f g S) S
      = runP blank (g (runP blank (f S) S)) (runP blank (f S) S) := by
  rw [seqQ, runP_append]

theorem seqQ_length (blank : Fin sc) (f g : Tapes16 sc → List (PAct sc)) (S : Tapes16 sc) :
    (seqQ blank f g S).length = (f S).length + (g (runP blank (f S) S)).length := by
  rw [seqQ, List.length_append]

/-- **準備フェーズ全体（2 本ソース版）**。区間長は最初の状態 `S` から読む。 -/
def setupProgramPair (blank startSym endSym : Fin sc) (k : ℕ) (S : Tapes16 sc) :
    List (PAct sc) :=
  seqQ blank (fun _ => prologueP blank startSym)
    (seqQ blank (fun T => copyLoopL blank tF tU (pairCounts S).1 T)
      (seqQ blank (fun T => copyLoopL blank tIn tU (pairCounts S).2.1 T)
        (seqQ blank (fun T => copyLoopL blank tF tP (pairCounts S).2.2.1 T)
          (seqQ blank (fun T => copyLoopL blank tIn tP (pairCounts S).2.2.2 T)
            (seqQ blank (fun _ => pushBothN endSym)
              (seqQ blank (fun T => settleP blank tU ((T tU).left.length - 2))
                (seqQ blank (fun T => settleP blank tP ((T tP).left.length - 2))
                  (fun T => kLoopP blank k T)))))))) S

def setupRunPair (blank startSym endSym : Fin sc) (k : ℕ) (S : Tapes16 sc) : Tapes16 sc :=
  runP blank (setupProgramPair blank startSym endSym k S) S

theorem prologueP_U (blank a : Fin sc) (S : Tapes16 sc) :
    runP blank (prologueP blank a) S tU = Tape.step blank (S tU) a .right := by
  rw [prologueP, runP_append, runP_cons, runP_nil,
    applyP_ne blank _ (PAct.put tF blank .left) (show tU ≠ tF by decide), pushBothN_U]

theorem prologueP_P (blank a : Fin sc) (S : Tapes16 sc) :
    runP blank (prologueP blank a) S tP = Tape.step blank (S tP) a .right := by
  rw [prologueP, runP_append, runP_cons, runP_nil,
    applyP_ne blank _ (PAct.put tF blank .left) (show tP ≠ tF by decide), pushBothN_P]

theorem prologueP_F (blank a : Fin sc) (S : Tapes16 sc) :
    runP blank (prologueP blank a) S tF = Tape.step blank (S tF) blank .left := by
  rw [prologueP, runP_append, runP_cons, runP_nil, applyP_put_self,
    pushBothN_ne blank a (show tF ≠ tU by decide) (show tF ≠ tP by decide)]

theorem prologueP_ne (blank a : Fin sc) {j : Fin 16} (hu : j ≠ tU) (hp : j ≠ tP)
    (hf : j ≠ tF) (S : Tapes16 sc) : runP blank (prologueP blank a) S j = S j := by
  rw [prologueP, runP_append, runP_cons, runP_nil,
    applyP_ne blank _ (PAct.put tF blank .left) hf, pushBothN_ne blank a hu hp]

/-! ## 6. 主定理 -/

section Setup

variable {blank startSym endSym mark : Fin sc} {k s h h₀ p₁ r : ℕ}
  {w Text : List (Fin sc)} {S : Tapes16 sc}

/-- 準備フェーズの入力仮定（2 本ソース版）。`PatternTapes.SetupPre` の `inb` を
「凍結した古いコピー `tIn`」＋「最前線テープ `tF`」の 2 本に置き換えたもの。 -/
structure SetupPrePair (blank mark : Fin sc) (s h h₀ p₁ r : ℕ) (w Text : List (Fin sc))
    (S : Tapes16 sc) : Prop where
  hpos : 0 < h₀
  hlt : h₀ < h
  hle : h ≤ w.length
  hcut : s < h
  inb₀ : Tape.SeqView blank (S tIn) (w.take h₀) (h₀ - 1)
  inF : InputCopy.FrontierView blank (S tF) ((w.drop h₀).take (h - h₀))
  emptyU : Tape.StackView blank (S tU) []
  emptyP : Tape.StackView blank (S tP) []
  txt : Tape.SeqView blank (S tT) (TextFeed.padW blank Text 0) 0
  txt2 : Tape.SeqView blank (S tX2) (TextFeed.padW blank Text 0) 0
  cs : Tape.CounterView' blank mark (S tCs) s
  c1 : Tape.CounterView' blank mark (S tC1) p₁
  c2 : Tape.CounterView' blank mark (S tC2) 0
  ap : Tape.CounterView' blank mark (S tAp) 0
  an : Tape.CounterView' blank mark (S tAn) 0
  rp : Tape.CounterView' blank mark (S tRp) r
  rn : Tape.CounterView' blank mark (S tRn) 0

/-- 準備フェーズの主要な中間結果をまとめて取り出す補題。
（`setup_spec_pair` と `freeze_pair` で共有する。） -/
theorem setup_core (H : SetupPrePair blank mark s h h₀ p₁ r w Text S) :
    Tape.SeqView blank (setupRunPair blank startSym endSym k S tP)
        (startSym :: ((w.take h).reverse.drop s ++ [endSym])) 1 ∧
      Tape.SeqView blank (setupRunPair blank startSym endSym k S tU)
        (startSym :: ((w.take h).reverse.take s ++ [endSym])) 1 ∧
      Tape.CounterView' blank mark (setupRunPair blank startSym endSym k S tC1) p₁ ∧
      Tape.CounterView' blank mark (setupRunPair blank startSym endSym k S tC2) 0 ∧
      Tape.CounterView' blank mark (setupRunPair blank startSym endSym k S tAn) (k * p₁) ∧
      (∀ j : Fin 16, j ≠ tU → j ≠ tP → j ≠ tC1 → j ≠ tC2 → j ≠ tAn → j ≠ tF → j ≠ tIn →
        setupRunPair blank startSym endSym k S j = S j) ∧
      Tape.SeqView blank (setupRunPair blank startSym endSym k S tF)
        ((w.drop h₀).take (h - h₀)) 0 ∧
      Tape.SeqView blank (setupRunPair blank startSym endSym k S tIn) (w.take h₀) 0 ∧
      (setupProgramPair blank startSym endSym k S).length ≤ 7 * (h + k * p₁ + 1) := by
  obtain ⟨hpos, hlt, hle, hcut, hIn, hF, hU, hP, hT, hX2, hCs, hC1, hC2, hAp, hAn, hRp, hRn⟩ := H
  -- 記号
  set m := h - h₀ with hm
  set w₀ := w.take h₀ with hw₀
  set fw := (w.drop h₀).take m with hfw
  have hmpos : 0 < m := by omega
  have hw₀len : w₀.length = h₀ := by rw [hw₀]; simp only [List.length_take]; omega
  have hfwlen : fw.length = m := by
    rw [hfw]; simp only [List.length_take, List.length_drop]; omega
  have hWlen : (w.take h).length = h := by simp only [List.length_take]; omega
  have hWsplit : w.take h = w₀ ++ fw := by
    have he : h₀ + m = h := by omega
    calc w.take h = w.take (h₀ + m) := by rw [he]
      _ = _ := List.take_add ..
  -- 段のパターン
  have hueq : ((w.take h).drop (h - s)).reverse = (w.take h).reverse.take s := by
    rw [List.take_reverse, hWlen]
  have hveq : (w.take (h - s)).reverse = (w.take h).reverse.drop s := by
    rw [List.drop_reverse, hWlen, List.take_take, Nat.min_eq_left (by omega)]
  -- 区間長
  set a := min s m with ha
  set b := s - m with hb
  set c := m - s with hc
  set d := h₀ + m - s - (m - s) with hd
  have hcvals : PatternTapes.cval (S tCs) = s := PatternTapes.cval_eq hCs
  have hFlen : (S tF).left.length = m := by rw [hF.left_eq]; simp [hfwlen]
  have hInlen : (S tIn).left.length = h₀ - 1 := by
    rw [hIn.left_eq]
    simp only [List.length_reverse, List.length_take, hw₀len]
    omega
  have hcounts : pairCounts S = (a, b, c, d) := by
    rw [pairCounts, hcvals, hFlen, hInlen, ha, hb, hc, hd]
    norm_num
    omega
  have hab : a + b = s := by omega
  have hcd : c + d = h - s := by omega
  -- 状態
  obtain ⟨S0, hS0⟩ : ∃ T, runP blank (prologueP blank startSym) S = T := ⟨_, rfl⟩
  obtain ⟨S1, hS1⟩ : ∃ T, runP blank (copyLoopL blank tF tU a S0) S0 = T := ⟨_, rfl⟩
  obtain ⟨S2, hS2⟩ : ∃ T, runP blank (copyLoopL blank tIn tU b S1) S1 = T := ⟨_, rfl⟩
  obtain ⟨S3, hS3⟩ : ∃ T, runP blank (copyLoopL blank tF tP c S2) S2 = T := ⟨_, rfl⟩
  obtain ⟨S4, hS4⟩ : ∃ T, runP blank (copyLoopL blank tIn tP d S3) S3 = T := ⟨_, rfl⟩
  obtain ⟨S5, hS5⟩ : ∃ T, runP blank (pushBothN endSym) S4 = T := ⟨_, rfl⟩
  obtain ⟨S6, hS6⟩ : ∃ T, runP blank (settleP blank tU ((S5 tU).left.length - 2)) S5 = T :=
    ⟨_, rfl⟩
  obtain ⟨S7, hS7⟩ : ∃ T, runP blank (settleP blank tP ((S6 tP).left.length - 2)) S6 = T :=
    ⟨_, rfl⟩
  -- フェーズ 0
  have p0U : Tape.StackView blank (S0 tU) [startSym] := by
    rw [← hS0, prologueP_U]; exact Tape.push_spec hU startSym
  have p0P : Tape.StackView blank (S0 tP) [startSym] := by
    rw [← hS0, prologueP_P]; exact Tape.push_spec hP startSym
  have p0F : Tape.SeqView blank (S0 tF) fw (m - 1) := by
    rw [← hS0, prologueP_F]
    have := InputCopy.toSeqView hF (by omega)
    rw [hfwlen] at this
    exact this
  have p0ne : ∀ j : Fin 16, j ≠ tU → j ≠ tP → j ≠ tF → S0 j = S j := by
    intro j hu hp hf; rw [← hS0]; exact prologueP_ne blank startSym hu hp hf S
  -- フェーズ 1 : tF → tU （a 個）
  obtain ⟨p1F, p1U⟩ := copyLoopL_spec blank (i := tF) (j := tU) (by decide) a (m - 1) S0 fw
    [startSym] (by omega) p0F p0U
  rw [hS1] at p1F p1U
  have p1ne : ∀ j : Fin 16, j ≠ tF → j ≠ tU → S1 j = S0 j := by
    intro j hf hu; rw [← hS1]; exact copyLoopL_untouched blank hf hu _ _
  -- フェーズ 2 : tIn → tU （b 個）
  obtain ⟨p2In, p2U⟩ := copyLoopL_spec blank (i := tIn) (j := tU) (by decide) b (h₀ - 1) S1 w₀
    _ (by omega)
    (by
      have e := p0ne tIn (by decide) (by decide) (by decide)
      rw [p1ne tIn (by decide) (by decide), e]; exact hIn) p1U
  rw [hS2] at p2In p2U
  have p2ne : ∀ j : Fin 16, j ≠ tIn → j ≠ tU → S2 j = S1 j := by
    intro j hi hu; rw [← hS2]; exact copyLoopL_untouched blank hi hu _ _
  -- フェーズ 3 : tF → tP （c 個）
  obtain ⟨p3F, p3P⟩ := copyLoopL_spec blank (i := tF) (j := tP) (by decide) c (m - 1 - a) S2 fw
    [startSym] (by omega) (by rw [p2ne tF (by decide) (by decide)]; exact p1F)
    (by rw [p2ne tP (by decide) (by decide), p1ne tP (by decide) (by decide)]; exact p0P)
  rw [hS3] at p3F p3P
  have p3ne : ∀ j : Fin 16, j ≠ tF → j ≠ tP → S3 j = S2 j := by
    intro j hf hp; rw [← hS3]; exact copyLoopL_untouched blank hf hp _ _
  -- フェーズ 4 : tIn → tP （d 個）
  obtain ⟨p4In, p4P⟩ := copyLoopL_spec blank (i := tIn) (j := tP) (by decide) d (h₀ - 1 - b) S3
    w₀ _ (by omega) (by rw [p3ne tIn (by decide) (by decide)]; exact p2In) p3P
  rw [hS4] at p4In p4P
  have p4ne : ∀ j : Fin 16, j ≠ tIn → j ≠ tP → S4 j = S3 j := by
    intro j hi hp; rw [← hS4]; exact copyLoopL_untouched blank hi hp _ _
  have p4U : Tape.StackView blank (S4 tU)
      ((w₀.take (h₀ - 1 + 1)).drop (h₀ - 1 + 1 - b)
        ++ ((fw.take (m - 1 + 1)).drop (m - 1 + 1 - a) ++ [startSym])) := by
    rw [p4ne tU (by decide) (by decide), p3ne tU (by decide) (by decide)]; exact p2U
  -- 積まれた語の同定
  have hidU : (w₀.take (h₀ - 1 + 1)).drop (h₀ - 1 + 1 - b)
      ++ ((fw.take (m - 1 + 1)).drop (m - 1 + 1 - a) ++ [startSym])
      = (w.take h).drop (h - s) ++ [startSym] := by
    rw [← List.append_assoc]
    congr 1
    rw [show h₀ - 1 + 1 = h₀ from by omega, show m - 1 + 1 = m from by omega,
      List.take_of_length_le (le_of_eq hw₀len), List.take_of_length_le (le_of_eq hfwlen),
      hWsplit, List.drop_append, hw₀len]
    rcases lt_or_ge s m with hsm | hsm
    · have e1 : w₀.drop (h₀ - b) = [] := by
        refine List.drop_eq_nil_of_le ?_; rw [hw₀len]; omega
      have e2 : w₀.drop (h - s) = [] := by
        refine List.drop_eq_nil_of_le ?_; rw [hw₀len]; omega
      rw [e1, e2, show m - a = h - s - h₀ from by omega]
    · rw [show h₀ - b = h - s from by omega, show m - a = h - s - h₀ from by omega]
  have hidP : (w₀.take (h₀ - 1 - b + 1)).drop (h₀ - 1 - b + 1 - d)
      ++ ((fw.take (m - 1 - a + 1)).drop (m - 1 - a + 1 - c) ++ [startSym])
      = w.take (h - s) ++ [startSym] := by
    rw [← List.append_assoc]
    congr 1
    have hWs : w.take (h - s) = (w.take h).take (h - s) := by
      rw [List.take_take, Nat.min_eq_left (by omega)]
    rw [hWs, hWsplit, List.take_append, hw₀len]
    rcases lt_or_ge s m with hsm | hsm
    · rw [show h₀ - 1 - b + 1 - d = 0 from by omega,
        show m - 1 - a + 1 - c = 0 from by omega,
        show h₀ - 1 - b + 1 = h₀ from by omega,
        show m - 1 - a + 1 = m - s from by omega,
        List.drop_zero, List.drop_zero,
        List.take_of_length_le (show w₀.length ≤ h₀ from le_of_eq hw₀len),
        List.take_of_length_le (show w₀.length ≤ h - s from by omega),
        show h - s - h₀ = m - s from by omega]
    · have e2 : fw.take (h - s - h₀) = [] := by
        rw [show h - s - h₀ = 0 from by omega, List.take_zero]
      have e1 : (fw.take (m - 1 - a + 1)).drop (m - 1 - a + 1 - c) = [] := by
        refine List.drop_eq_nil_of_le ?_
        simp only [List.length_take, hfwlen]
        omega
      rw [e2, e1, show h₀ - 1 - b + 1 - d = 0 from by omega,
        show h₀ - 1 - b + 1 = h - s from by omega, List.drop_zero]
  rw [hidU] at p4U
  rw [hidP] at p4P
  -- フェーズ 5
  have p5U : Tape.StackView blank (S5 tU)
      (endSym :: ((w.take h).drop (h - s) ++ [startSym])) := by
    rw [← hS5, pushBothN_U]; exact Tape.push_spec p4U endSym
  have p5P : Tape.StackView blank (S5 tP) (endSym :: (w.take (h - s) ++ [startSym])) := by
    rw [← hS5, pushBothN_P]; exact Tape.push_spec p4P endSym
  have p5ne : ∀ j : Fin 16, j ≠ tU → j ≠ tP → S5 j = S4 j := by
    intro j hu hp; rw [← hS5]; exact pushBothN_ne blank endSym hu hp S4
  -- フェーズ 6
  have hulen : ((w.take h).drop (h - s)).length = s := by
    rw [List.length_drop, hWlen]; omega
  have hvlen : (w.take (h - s)).length = h - s := by
    simp only [List.length_take]; omega
  have hlen6 : (S5 tU).left.length - 2 = s := by
    rw [p5U.left_eq]
    simp only [List.length_cons, List.length_append, List.length_nil, hulen]
    omega
  have p6U : Tape.SeqView blank (S6 tU)
      (startSym :: ((w.take h).reverse.take s ++ [endSym])) 1 := by
    rw [← hS6, hlen6]
    have := settleP_spec blank tU (n := s) p5U
      (by simp only [List.length_append, List.length_cons, List.length_nil, hulen])
    simpa [← hueq] using this
  have p6ne : ∀ j : Fin 16, j ≠ tU → S6 j = S5 j := by
    intro j hu; rw [← hS6]; exact settleP_untouched blank hu _ _
  -- フェーズ 7
  have hlen7 : (S6 tP).left.length - 2 = h - s := by
    rw [p6ne tP (by decide), p5P.left_eq]
    simp only [List.length_cons, List.length_append, List.length_nil, hvlen]
    omega
  have p7P : Tape.SeqView blank (S7 tP)
      (startSym :: ((w.take h).reverse.drop s ++ [endSym])) 1 := by
    rw [← hS7, hlen7]
    have hp6 : Tape.StackView blank (S6 tP) (endSym :: (w.take (h - s) ++ [startSym])) := by
      rw [p6ne tP (by decide)]; exact p5P
    have := settleP_spec blank tP (n := h - s) hp6
      (by simp only [List.length_append, List.length_cons, List.length_nil, hvlen])
    simpa [← hveq] using this
  have p7ne : ∀ j : Fin 16, j ≠ tP → S7 j = S6 j := by
    intro j hp; rw [← hS7]; exact settleP_untouched blank hp _ _
  -- 触られなかったテープ
  have hkeep : ∀ j : Fin 16, j ≠ tU → j ≠ tP → j ≠ tF → j ≠ tIn → S7 j = S j := by
    intro j hu hp hf hi
    rw [p7ne j hp, p6ne j hu, p5ne j hu hp, p4ne j hi hp, p3ne j hf hp, p2ne j hi hu,
      p1ne j hf hu, p0ne j hu hp hf]
  -- ソース 2 本の凍結
  have hFfin : Tape.SeqView blank (S7 tF) fw 0 := by
    rw [p7ne tF (by decide), p6ne tF (by decide), p5ne tF (by decide) (by decide),
      p4ne tF (by decide) (by decide)]
    have := p3F
    rwa [show m - 1 - a - c = 0 from by omega] at this
  have hInfin : Tape.SeqView blank (S7 tIn) w₀ 0 := by
    rw [p7ne tIn (by decide), p6ne tIn (by decide), p5ne tIn (by decide) (by decide)]
    have := p4In
    rwa [show h₀ - 1 - b - d = 0 from by omega] at this
  -- フェーズ 8 : 単進カウンタ
  obtain ⟨q1, q2, q3, qlen, qne⟩ := PatternTapes.kLoop_spec (blank := blank) (mark := mark)
    k (prj S7) p₁ 0
    (by rw [show prj S7 PatternTapes.sC1 = S7 tC1 from rfl,
      hkeep tC1 (by decide) (by decide) (by decide) (by decide)]; exact hC1)
    (by rw [show prj S7 PatternTapes.sC2 = S7 tC2 from rfl,
      hkeep tC2 (by decide) (by decide) (by decide) (by decide)]; exact hC2)
    (by rw [show prj S7 PatternTapes.sAn = S7 tAn from rfl,
      hkeep tAn (by decide) (by decide) (by decide) (by decide)]; exact hAn)
  have hlift : ∀ i : Fin 15, runP blank (kLoopP blank k S7) S7 (inj i)
      = PatternTapes.run blank (PatternTapes.kLoop blank k (prj S7)) (prj S7) i := by
    intro i
    exact congrFun (prj_runP_map blank (PatternTapes.kLoop blank k (prj S7)) S7) i
  have hrun : setupRunPair blank startSym endSym k S = runP blank (kLoopP blank k S7) S7 := by
    simp only [setupRunPair, setupProgramPair, seqQ_run, hcounts, hS0, hS1, hS2, hS3, hS4,
      hS5, hS6, hS7]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [tP]
    rw [hrun, hlift PatternTapes.sP, qne PatternTapes.sP (by decide) (by decide) (by decide)]
    exact p7P
  · simp only [tU]
    rw [hrun, hlift PatternTapes.sU, qne PatternTapes.sU (by decide) (by decide) (by decide)]
    rw [show prj S7 PatternTapes.sU = S7 tU from rfl, p7ne tU (by decide)]
    exact p6U
  · simp only [tC1]; rw [hrun, hlift PatternTapes.sC1]; exact q1
  · simp only [tC2]; rw [hrun, hlift PatternTapes.sC2]; exact q2
  · simp only [tAn]; rw [hrun, hlift PatternTapes.sAn]; simpa using q3
  · intro j hu hp h1 h2 h3 hf hi
    rcases eq_or_ne j tF with rfl | hjF
    · exact absurd rfl hf
    · have hex : ∃ i : Fin 15, inj i = j := by
        refine ⟨⟨j.val, ?_⟩, ?_⟩
        · have h13 := j.isLt
          have hne : j.val ≠ 15 := by
            intro hv; exact hjF (Fin.ext (by rw [hv]; rfl))
          omega
        · rfl
      obtain ⟨i, rfl⟩ := hex
      rw [hrun, hlift i,
        qne i (fun hEq => h1 (by rw [hEq]; rfl)) (fun hEq => h2 (by rw [hEq]; rfl))
          (fun hEq => h3 (by rw [hEq]; rfl))]
      exact hkeep (inj i) hu hp hf hi
  · rw [hrun]; simp only [kLoopP]; rw [runP_map_tF]; exact hFfin
  · simp only [tIn]
    rw [hrun, hlift PatternTapes.sIn,
      qne PatternTapes.sIn (by decide) (by decide) (by decide)]
    exact hInfin
  · rw [setupProgramPair, seqQ_length, hcounts, hS0, seqQ_length, hS1, seqQ_length, hS2,
      seqQ_length, hS3, seqQ_length, hS4, seqQ_length, hS5, seqQ_length, hS6, seqQ_length,
      hS7, prologueP_length, copyLoopL_length, copyLoopL_length, copyLoopL_length,
      copyLoopL_length, pushBothN_length, settleP_length, settleP_length, hlen6, hlen7,
      kLoopP_length, qlen]
    dsimp only
    omega

/-- **主定理（2 本ソース版）**：`PatternTapes.setup_spec` と同じ結論・同じコスト上界。 -/
theorem setup_spec_pair (H : SetupPrePair blank mark s h h₀ p₁ r w Text S) :
    GSVTapes.VEncodes' blank startSym endSym mark
        ((w.take h).reverse.take s) ((w.take h).reverse.drop s)
        (TextFeed.padW blank Text 0) k p₁ r
        (PatternTapes.toGS (prj (setupRunPair blank startSym endSym k S)),
          PatternTapes.toVExt (prj (setupRunPair blank startSym endSym k S)))
        (⟨0, 0⟩, 0)
      ∧ (setupProgramPair blank startSym endSym k S).length ≤ 7 * (h + k * p₁ + 1) := by
  obtain ⟨gP, gU, g1, g2, g3, gkeep, _, _, glen⟩ :=
    setup_core (startSym := startSym) (endSym := endSym) (k := k) H
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩, ?_, ?_⟩, glen⟩
  · show Tape.SeqView blank (setupRunPair blank startSym endSym k S tP) _ (0 + 1)
    rw [Nat.zero_add]; exact gP
  · show Tape.SeqView blank (setupRunPair blank startSym endSym k S tT) _ (0 + 0)
    rw [Nat.zero_add,
      gkeep tT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]
    exact H.txt
  · exact g1
  · exact g2
  · show Tape.CounterView' blank mark (setupRunPair blank startSym endSym k S tAp) (0 - k * p₁)
    rw [Nat.zero_sub,
      gkeep tAp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]
    exact H.ap
  · show Tape.CounterView' blank mark (setupRunPair blank startSym endSym k S tAn) (k * p₁ - 0)
    rw [Nat.sub_zero]; exact g3
  · show Tape.CounterView' blank mark (setupRunPair blank startSym endSym k S tRp) (r - 0)
    rw [Nat.sub_zero,
      gkeep tRp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]
    exact H.rp
  · show Tape.CounterView' blank mark (setupRunPair blank startSym endSym k S tRn) (0 - r)
    rw [Nat.zero_sub,
      gkeep tRn (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]
    exact H.rn
  · show Tape.SeqView blank (setupRunPair blank startSym endSym k S tU) _ (0 + 1)
    rw [Nat.zero_add]; exact gU
  · show Tape.SeqView blank (setupRunPair blank startSym endSym k S tX2) _ (0 - _ + 0)
    rw [Nat.zero_sub, Nat.zero_add,
      gkeep tX2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]
    exact H.txt2

/-- **凍結**：準備フェーズはソース 2 本の内容を変えない（ヘッドが添字 `0` に戻るだけ）。
よって次の段のコピー元としてそのまま使える。 -/
theorem freeze_pair (H : SetupPrePair blank mark s h h₀ p₁ r w Text S) :
    Tape.SeqView blank (setupRunPair blank startSym endSym k S tF)
        ((w.drop h₀).take (h - h₀)) 0 ∧
      Tape.SeqView blank (setupRunPair blank startSym endSym k S tIn) (w.take h₀) 0 := by
  obtain ⟨_, _, _, _, _, _, gF, gIn, _⟩ :=
    setup_core (startSym := startSym) (endSym := endSym) (k := k) H
  exact ⟨gF, gIn⟩

/-- `k * p₁ ≤ h` なら準備フェーズのコストは入力長 `h` に線形。 -/
theorem setup_cost_linear_pair (H : SetupPrePair blank mark s h h₀ p₁ r w Text S)
    (hkp : k * p₁ ≤ h) :
    (setupProgramPair blank startSym endSym k S).length ≤ 21 * h := by
  have h1 := (setup_spec_pair (startSym := startSym) (endSym := endSym) (k := k) H).2
  have h2 : 0 < h := by have := H.hpos; have := H.hlt; omega
  omega

end Setup

/-! ## 7. 2 本を 1 本にまとめ直す -/

/-- 凍結した 2 本（ヘッドは両方とも添字 `0`）から、`w.take h` を保持する 1 本の
最前線テープ `j` を作る。 -/
def copyPairToSingle (blank : Fin sc) (j : Fin 16) (h₀ m : ℕ) (S : Tapes16 sc) :
    List (PAct sc) :=
  seqQ blank (fun T => copyLoopR blank tIn j h₀ T) (fun T => copyLoopR blank tF j m T) S

@[simp] theorem copyPairToSingle_length (blank : Fin sc) (j : Fin 16) (h₀ m : ℕ)
    (S : Tapes16 sc) : (copyPairToSingle blank j h₀ m S).length = 2 * h₀ + 2 * m := by
  rw [copyPairToSingle, seqQ_length, copyLoopR_length, copyLoopR_length]

/-- **仕様**：`≤ 2 * h + 2` 動作で `j` に `w.take h` の最前線ビューが立つ。 -/
theorem copyPairToSingle_spec (blank : Fin sc) {j : Fin 16} (hjI : j ≠ tIn) (hjF : j ≠ tF)
    {S : Tapes16 sc} {w : List (Fin sc)} {h h₀ : ℕ} (_hpos : 0 < h₀) (hlt : h₀ < h)
    (hle : h ≤ w.length)
    (hIn : Tape.SeqView blank (S tIn) (w.take h₀) 0)
    (hF : Tape.SeqView blank (S tF) ((w.drop h₀).take (h - h₀)) 0)
    (hj : Tape.StackView blank (S j) []) :
    InputCopy.FrontierView blank
        (runP blank (copyPairToSingle blank j h₀ (h - h₀) S) S j) (w.take h) ∧
      (copyPairToSingle blank j h₀ (h - h₀) S).length ≤ 2 * h + 2 := by
  set m := h - h₀ with hm
  set w₀ := w.take h₀ with hw₀
  set fw := (w.drop h₀).take m with hfw
  have hw₀len : w₀.length = h₀ := by rw [hw₀]; simp only [List.length_take]; omega
  have hfwlen : fw.length = m := by
    rw [hfw]; simp only [List.length_take, List.length_drop]; omega
  have hWsplit : w.take h = w₀ ++ fw := by
    have he : h₀ + m = h := by omega
    calc w.take h = w.take (h₀ + m) := by rw [he]
      _ = _ := List.take_add ..
  obtain ⟨T1, hT1⟩ : ∃ T, runP blank (copyLoopR blank tIn j h₀ S) S = T := ⟨_, rfl⟩
  have step1 : Tape.StackView blank (T1 j) w₀.reverse := by
    have := copyLoopR_spec blank (i := tIn) (j := j) hjI h₀ 0 S w₀ []
      (by omega) (fun _ => hIn) hj
    rw [hT1] at this
    rw [List.take_of_length_le (show w₀.length ≤ 0 + h₀ from by omega), List.drop_zero,
      List.append_nil] at this
    exact this
  have hT1F : T1 tF = S tF := by
    rw [← hT1]; exact copyLoopR_untouched blank (by decide) (Ne.symm hjF) _ _
  have step2 : Tape.StackView blank
      (runP blank (copyLoopR blank tF j m T1) T1 j) (fw.reverse ++ w₀.reverse) := by
    have := copyLoopR_spec blank (i := tF) (j := j) hjF m 0 T1 fw w₀.reverse
      (by omega) (fun _ => by rw [hT1F]; exact hF) step1
    rw [List.take_of_length_le (show fw.length ≤ 0 + m from by omega), List.drop_zero] at this
    exact this
  refine ⟨?_, by rw [copyPairToSingle_length]; omega⟩
  rw [copyPairToSingle, seqQ_run, hT1]
  refine InputCopy.frontierView_iff_stackView.2 ?_
  rw [hWsplit, List.reverse_append]
  exact step2

end PalPeg.PatternTapesPair
