import PalPeg.PatternProg
import PalPeg.PatternTapesPair

/-!
# 2 本ソース版準備フェーズの有限制御プログラム化 (`PatternPairProg`)

`PalPeg.PatternTapesPair` の準備フェーズ（13 本テープ：12 本の段テープ＋最前線テープ
`tF`）を、`PalPeg.PatternProg` の `Prog`（`ProgLang` の構造化プログラム）に載せ替える。
`PatternProg.setupProgL` と同じく、**入力に依存しない単一の固定プログラム**を作る：
区間長 `pairCounts`（`min s m`, `s ∸ m`, `m ∸ s`, …）はどこにも定数として現れず、

* `s` はカウンタテープ `tCs` を 1 ずつ消費する**カウンタ駆動ループ**で数える
  （消費分はミラー `tC2` に写し、`xfer1` で `tCs` に戻す）。
  そのループの本体は「`tF` が左端番兵 `leftSym` を読んでいるか」で
  `tF` からのコピーと `tIn` からのコピーを**分岐**する。これで
  `min s m` 個＋`s ∸ m` 個の 2 区間が 1 本のループにまとまる。
* 残り（`tP` 側）は**番兵駆動ループ** 2 本：`tF` を `leftSym` まで、続いて `tIn` を
  `leftSym` まで読む。これが `m ∸ s` 個と残りの `min (h - s) h₀` 個にあたる。
* そのあとは `setupProgL` と同様、`endSym` を積み、`startSym` を番兵とする
  `settleProgG` 2 本、`kLoopProg` の順。

追加仮定は `PrepPreLPair`（`PatternProg.PrepPreL` の 2 本ソース版）にまとめてある：
2 本のソーステープはどちらも内容の左隣に**番兵セル `leftSym`** を持つ。
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.PatternPairProg

open PegSeparation.RealTimeTM
open PalPeg
open PalPeg.PatternTapesPair
open PalPeg.PatternProg
open PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type}

/-! ## 1. 12 本版の `TAct` を 13 本版へ持ち上げる -/

/-- 12 本版のテープ動作を 13 本版へ（テープ番号を `inj` で埋め込む）。 -/
def liftT : TAct 12 sc → TAct 13 sc
  | .keep i m => .keep (inj i) m
  | .put i x m => .put (inj i) x m
  | .copy i j m => .copy (inj i) (inj j) m

@[simp] theorem liftT_tape (a : TAct 12 sc) : (liftT a).tape = inj a.tape := by
  cases a <;> rfl

@[simp] theorem liftT_mv (a : TAct 12 sc) : (liftT a).mv = a.mv := by cases a <;> rfl

theorem liftT_write (S : Tapes13 sc) (a : TAct 12 sc) :
    (liftT a).write S = a.write (prj S) := by cases a <;> rfl

theorem prj_applyG (blank : Fin sc) (S : Tapes13 sc) (a : TAct 12 sc) :
    prj (applyG blank S (liftT a)) = applyG blank (prj S) a := by
  funext j
  show applyG blank S (liftT a) (inj j) = applyG blank (prj S) a j
  by_cases hj : j = a.tape
  · have e1 : applyG blank S (liftT a) (inj j)
        = Tape.step blank (S (inj a.tape)) ((liftT a).write S) (liftT a).mv := by
      rw [hj, ← liftT_tape a, applyG_self]
    have e2 : applyG blank (prj S) a j
        = Tape.step blank (prj S a.tape) (a.write (prj S)) a.mv := by
      rw [hj, applyG_self]
    rw [e1, e2, liftT_write, liftT_mv]
    rfl
  · have h1 : inj j ≠ (liftT a).tape := by
      simp only [liftT_tape]
      exact fun hc => hj (inj_injective hc)
    rw [applyG_ne blank S (liftT a) h1, applyG_ne blank (prj S) a hj]
    rfl

theorem prj_runG_map (blank : Fin sc) :
    ∀ (l : List (TAct 12 sc)) (S : Tapes13 sc),
      prj (runG blank (l.map liftT) S) = runG blank l (prj S) := by
  intro l
  induction l with
  | nil => intro S; rfl
  | cons a l ih => intro S; rw [List.map_cons, runG_cons, ih, prj_applyG, runG_cons]

theorem runG_map_tF (blank : Fin sc) (l : List (TAct 12 sc)) (S : Tapes13 sc) :
    runG blank (l.map liftT) S tF = S tF := by
  refine runG_untouched blank tF _ S (fun a ha => ?_)
  obtain ⟨b, _, rfl⟩ := List.mem_map.1 ha
  simp only [liftT_tape]
  exact inj_ne_tF _

theorem prj_runG_map_at (blank : Fin sc) (l : List (TAct 12 sc)) (S : Tapes13 sc)
    (i : Fin 12) : runG blank (l.map liftT) S (inj i) = runG blank l (prj S) i :=
  congrFun (prj_runG_map blank l S) i

/-! ## 2. 13 本版の `PAct` 動作列との対応 -/

/-- 13 本版の動作を `TAct` へ。 -/
def liftP : PAct sc → TAct 13 sc
  | .keep i m => .keep i m
  | .put i x m => .put i x m

theorem applyP_eq (blank : Fin sc) (S : Tapes13 sc) (a : PAct sc) :
    applyP blank S a = applyG blank S (liftP a) := by
  cases a <;> rfl

theorem runP_eq (blank : Fin sc) : ∀ (l : List (PAct sc)) (S : Tapes13 sc),
    runP blank l S = runG blank (l.map liftP) S := by
  intro l
  induction l with
  | nil => intro S; rfl
  | cons a l ih => intro S; rw [runP_cons, ih, List.map_cons, runG_cons, applyP_eq]

/-- 左向きコピーの 1 周回は `copyRoundL` と同じ作用。 -/
theorem copyRoundG_runP (blank : Fin sc) (i j : Fin 13) (S : Tapes13 sc) :
    runG blank (copyRoundG i j) S = runP blank (copyRoundL i j S) S := rfl

/-- 番兵駆動コピーの動作列は `copyLoopL` と同じ作用。 -/
theorem copyActsN_runP (blank : Fin sc) (i j : Fin 13) :
    ∀ (n : ℕ) (S : Tapes13 sc),
      runG blank (copyActsN i j n) S = runP blank (copyLoopL blank i j n S) S := by
  intro n
  induction n with
  | zero => intro S; rfl
  | succ n ih =>
      intro S
      rw [copyActsN, runG_append, copyRoundG_runP, copyLoopL, runP_append, ih]

/-- 右向きコピーの 1 周回は `copyRoundR` と同じ作用。 -/
theorem copyRoundGR_runP (blank : Fin sc) (i j : Fin 13) (S : Tapes13 sc) :
    runG blank (copyRoundGR i j) S = runP blank (copyRoundR i j S) S := rfl

theorem copyActsR_runP (blank : Fin sc) (i j : Fin 13) :
    ∀ (n : ℕ) (S : Tapes13 sc),
      runG blank (copyActsR i j n) S = runP blank (copyLoopR blank i j n S) S := by
  intro n
  induction n with
  | zero => intro S; rfl
  | succ n ih =>
      intro S
      rw [copyActsR, runG_append, copyRoundGR_runP, copyLoopR, runP_append, ih]

/-- `settleProgG` の動作列は `settleP` と同じ作用（左 1 歩・右 1 歩が余分に入るが恒等）。 -/
theorem settleActs_runP (blank : Fin sc) (i : Fin 13) (n : ℕ) (S : Tapes13 sc)
    {x : Fin sc} {l : List (Fin sc)}
    (h : ((runP blank (settleP blank i n) S) i).left = x :: l) :
    runG blank (TAct.put i blank .left :: (leftWalkG i (n + 1) ++ [TAct.keep i .right])) S
      = runP blank (settleP blank i n) S := by
  have hlist : TAct.put i blank (sc := sc) .left :: (leftWalkG i (n + 1) ++ [TAct.keep i .right])
      = (TAct.put i blank .left :: leftWalkG i n) ++ [TAct.keep i .left, TAct.keep i .right] := by
    rw [leftWalkG_snoc]; simp
  have hpre : runG blank (TAct.put i blank (sc := sc) .left :: leftWalkG i n) S
      = runP blank (settleP blank i n) S := by
    rw [settleP, runP_eq, List.map_cons]
    congr 1
    simp [leftWalkP, leftWalkG, List.map_replicate, liftP]
  rw [hlist, runG_append, hpre]
  exact keepLR_id h

/-! ## 3. `pushBothN` の `Prog` 版 -/

/-- `tU`, `tP` に同じ記号を積む。 -/
def pushBothProgP (a : Fin sc) : Prog (ActG 13 sc) (CondG 13 sc) :=
  Prog.seq (ACT (TAct.put tU a .right)) (ACT (TAct.put tP a .right))

def pushBothActsP (a : Fin sc) : List (TAct 13 sc) :=
  [TAct.put tU a .right, TAct.put tP a .right]

theorem pushBothActsP_runP (blank a : Fin sc) (S : Tapes13 sc) :
    runG blank (pushBothActsP a) S = runP blank (pushBothN a) S := by
  rw [pushBothN, runP_eq]; rfl

theorem pushBothProgP_exec {blank : Fin sc} (a : Fin sc) (S : Tapes13 sc) :
    ExecG Terminal blank (pushBothProgP a) S (pushBothActsP a) :=
  execG_of_eq rfl (execG_seq (execG_act _ S) (execG_act _ _))

/-! ## 4. 2 本ソースを 1 本のカウンタ駆動ループで読む

`tCs`（値 `s`）を 1 ずつ消費するループ。1 周回の本体は、`tF` が左端番兵 `leftSym` を
読んでいるかで分岐する：まだ読んでいなければ `tF` から、読んでいれば `tIn` から
1 記号を `tU` に積む。消費した分はミラー `tC2` に写す。 -/

section PairLoop

/-- `tF` から 1 記号（ミラー付き）。 -/
def pairRoundF (blank : Fin sc) : List (TAct 13 sc) :=
  [TAct.copy tU tF .right, TAct.keep tF .left, TAct.put tC2 blank .right]

/-- `tIn` から 1 記号（ミラー付き）。 -/
def pairRoundI (blank : Fin sc) : List (TAct 13 sc) :=
  [TAct.copy tU tIn .right, TAct.keep tIn .left, TAct.put tC2 blank .right]

/-- 位置 `p`（合成ソース `w₀ ++ fw` の残り長）における 1 周回の本体。 -/
def pairBody (blank : Fin sc) (h₀ p : ℕ) : List (TAct 13 sc) :=
  if h₀ < p then pairRoundF blank else pairRoundI blank

/-- 1 周回（カウンタの減算 2 動作＋本体）。 -/
def pairFirst (blank : Fin sc) (h₀ p : ℕ) : List (TAct 13 sc) :=
  TAct.put tCs blank .left :: TAct.put tCs blank .stay :: pairBody blank h₀ p

/-- `n` 周回ぶんの動作列（位置 `p` から）。 -/
def pairActsN (blank : Fin sc) (h₀ p : ℕ) : ℕ → List (TAct 13 sc)
  | 0 => []
  | n + 1 => pairFirst blank h₀ p ++ pairActsN blank h₀ (p - 1) n

/-- ループ本体側から見た `n` 周回（先頭のプローブを外に出した形）。 -/
def pairTail (blank : Fin sc) (h₀ p : ℕ) : ℕ → List (TAct 13 sc)
  | 0 => []
  | n + 1 => TAct.put tCs blank .stay ::
      ((pairBody blank h₀ p ++ [TAct.put tCs blank .left]) ++ pairTail blank h₀ (p - 1) n)

theorem pairActsN_length (blank : Fin sc) (h₀ : ℕ) :
    ∀ (n p : ℕ), (pairActsN blank h₀ p n).length = 5 * n := by
  intro n
  induction n with
  | zero => intro p; rfl
  | succ n ih =>
      intro p
      rw [pairActsN, List.length_append, ih]
      simp only [pairFirst, pairBody, List.length_cons]
      split <;> simp [pairRoundF, pairRoundI] <;> omega

theorem pairCons (blank : Fin sc) (h₀ : ℕ) : ∀ (n p : ℕ),
    TAct.put tCs blank .left :: pairTail blank h₀ p n
      = pairActsN blank h₀ p n ++ [TAct.put tCs blank (sc := sc) .left] := by
  intro n
  induction n with
  | zero => intro p; rfl
  | succ n ih =>
      intro p
      rw [pairTail, pairActsN, pairFirst, List.append_assoc]
      simp only [List.cons_append, List.nil_append, List.append_assoc]
      rw [← ih]

/-- 分岐する 1 周回本体のプログラム。 -/
def pairLoopBody (blank leftSym : Fin sc) : Prog (ActG 13 sc) (CondG 13 sc) :=
  Prog.ite (tF, leftSym)
    (seqActs (pairRoundF blank ++ [TAct.put tCs blank .left]))
    (seqActs (pairRoundI blank ++ [TAct.put tCs blank .left]))

/-- カウンタ駆動＋ソース分岐のループ全体。 -/
def pairLoopProg (blank mark leftSym : Fin sc) : Prog (ActG 13 sc) (CondG 13 sc) :=
  Prog.seq (ACT (TAct.put tCs blank .left))
    (Prog.seq
      (Prog.loop (tCs, mark) (TAct.put tCs blank (sc := sc) .stay).act
        (pairLoopBody blank leftSym))
      (ACT (TAct.keep tCs .right)))

variable {blank mark leftSym : Fin sc}

/-- **ループ本体の帰納法**：`n` 周回ぶんの実行と、その結果テープの性質。 -/
theorem pairLoop_tail (hne : mark ≠ blank) {w₀ fw : List (Fin sc)}
    (hfF : leftSym ∉ fw) :
    ∀ (n p y : ℕ) (L : List (Fin sc)) (S : Tapes13 sc), n ≤ p →
      p ≤ w₀.length + fw.length →
      Tape.CounterView' blank mark (S tCs) n →
      Tape.CounterView' blank mark (S tC2) y →
      Tape.SeqView blank (S tF) (leftSym :: fw) (p - w₀.length) →
      Tape.SeqView blank (S tIn) (leftSym :: w₀) (min p w₀.length) →
      Tape.StackView blank (S tU) L →
      ExecG Terminal blank
          (Prog.loop (tCs, mark) (TAct.put tCs blank (sc := sc) .stay).act
            (pairLoopBody blank leftSym))
          (applyG blank S (TAct.put tCs blank .left)) (pairTail blank w₀.length p n) ∧
        Tape.CounterView' blank mark
          (runG blank (pairActsN blank w₀.length p n) S tCs) 0 ∧
        Tape.CounterView' blank mark
          (runG blank (pairActsN blank w₀.length p n) S tC2) (y + n) ∧
        Tape.SeqView blank (runG blank (pairActsN blank w₀.length p n) S tF)
          (leftSym :: fw) (p - n - w₀.length) ∧
        Tape.SeqView blank (runG blank (pairActsN blank w₀.length p n) S tIn)
          (leftSym :: w₀) (min (p - n) w₀.length) ∧
        Tape.StackView blank (runG blank (pairActsN blank w₀.length p n) S tU)
          (((w₀ ++ fw).take p).drop (p - n) ++ L) ∧
        (∀ j : Fin 13, j ≠ tU → j ≠ tF → j ≠ tIn → j ≠ tCs → j ≠ tC2 →
          runG blank (pairActsN blank w₀.length p n) S j = S j) := by
  intro n
  induction n with
  | zero =>
      intro p y L S _ _ hcs hc2 hF hIn hU
      refine ⟨execG_loop_stop (by rw [decLoop_cond (a := tCs) hne hcs]; simp), ?_, ?_, ?_, ?_,
        ?_, ?_⟩
      · simpa [pairActsN] using hcs
      · simpa [pairActsN] using hc2
      · simpa [pairActsN] using hF
      · simpa [pairActsN] using hIn
      · have : ((w₀ ++ fw).take p).drop (p - 0) = [] := by
          refine List.drop_eq_nil_of_le ?_
          simp
        simp only [pairActsN, runG_nil]
        rw [this, List.nil_append]
        exact hU
      · intro j _ _ _ _ _; rfl
  | succ n ih =>
      intro p y L S hnp hpl hcs hc2 hF hIn hU
      -- 減算後の状態
      set Q := applyG blank (applyG blank S (TAct.put tCs blank .left))
        (TAct.put tCs blank .stay) with hQ
      have hQne : ∀ j : Fin 13, j ≠ tCs → Q j = S j := by
        intro j hj
        rw [hQ, applyG_ne blank _ _ hj, applyG_ne blank _ _ hj]
      have hQcs : Tape.CounterView' blank mark (Q tCs) n := by
        rw [hQ, applyG_put_self, applyG_put_self]
        exact Tape.counter'_dec hcs
      -- 読む記号
      set c := if w₀.length < p then (S tF).focus else (S tIn).focus with hc
      have hppos : 0 < p := by omega
      have hWlen : ((w₀ ++ fw).take (p - 1)).length = p - 1 := by
        simp only [List.length_take, List.length_append]; omega
      have hWget : (w₀ ++ fw)[p - 1]? = some c := by
        by_cases hcase : w₀.length < p
        · have h1 : (leftSym :: fw)[p - w₀.length]? = some (S tF).focus := hF.focus_eq
          have h2 : p - w₀.length = (p - 1 - w₀.length) + 1 := by omega
          rw [h2, List.getElem?_cons_succ] at h1
          rw [List.getElem?_append_right (by omega), hc, if_pos hcase]
          exact h1
        · have h1 : (leftSym :: w₀)[min p w₀.length]? = some (S tIn).focus := hIn.focus_eq
          have h2 : min p w₀.length = (p - 1) + 1 := by omega
          rw [h2, List.getElem?_cons_succ] at h1
          rw [List.getElem?_append_left (by omega), hc, if_neg hcase]
          exact h1
      have hsplit : (w₀ ++ fw).take p = (w₀ ++ fw).take (p - 1) ++ [c] := by
        rw [show p = (p - 1) + 1 from by omega, List.take_add_one, hWget]
        rfl
      have hkey : ((w₀ ++ fw).take (p - 1)).drop (p - 1 - n) ++ (c :: L)
          = ((w₀ ++ fw).take p).drop (p - (n + 1)) ++ L := by
        rw [show p - (n + 1) = p - 1 - n from by omega, hsplit,
          List.drop_append_of_le_length (by rw [hWlen]; omega)]
        simp
      -- 本体を実行した後の状態
      set S' := runG blank (pairBody blank w₀.length p) Q with hS'
      have hbody_tCs : S' tCs = Q tCs := by
        rw [hS']
        refine runG_untouched blank tCs _ _ (fun a ha => ?_)
        simp only [pairBody] at ha
        split at ha <;> fin_cases ha <;> simp only [TAct.tape] <;> decide
      have hS'cs : Tape.CounterView' blank mark (S' tCs) n := by rw [hbody_tCs]; exact hQcs
      have hS'ne : ∀ j : Fin 13, j ≠ tU → j ≠ tF → j ≠ tIn → j ≠ tCs → j ≠ tC2 →
          S' j = S j := by
        intro j hu hf hi hcsj hc2j
        rw [hS', runG_untouched blank j _ _ (fun a ha => ?_), hQne j hcsj]
        simp only [pairBody] at ha
        split at ha <;> fin_cases ha <;> simp only [TAct.tape] <;>
          first
            | exact fun hh => hu hh.symm
            | exact fun hh => hf hh.symm
            | exact fun hh => hi hh.symm
            | exact fun hh => hc2j hh.symm
      have hS'c2 : Tape.CounterView' blank mark (S' tC2) (y + 1) := by
        have hpre : ∀ (X : List (TAct 13 sc)), (∀ a ∈ X, a.tape ≠ tC2) →
            runG blank (X ++ [TAct.put tC2 blank .right]) Q tC2
              = Tape.step blank (Q tC2) blank .right := by
          intro X hX
          rw [runG_append]
          show applyG blank (runG blank X Q) (TAct.put tC2 blank .right) tC2 = _
          rw [applyG_put_self, runG_untouched blank tC2 X Q hX]
        have hQc2 : Q tC2 = S tC2 := hQne tC2 (by decide)
        rw [hS']
        by_cases hcase : w₀.length < p
        · rw [pairBody, if_pos hcase,
            show pairRoundF blank
              = [TAct.copy tU tF (sc := sc) .right, TAct.keep tF .left]
                  ++ [TAct.put tC2 blank .right] from rfl,
            hpre _ (by intro a ha; fin_cases ha <;> simp only [TAct.tape] <;> decide), hQc2]
          exact Tape.counter'_inc hc2
        · rw [pairBody, if_neg hcase,
            show pairRoundI blank
              = [TAct.copy tU tIn (sc := sc) .right, TAct.keep tIn .left]
                  ++ [TAct.put tC2 blank .right] from rfl,
            hpre _ (by intro a ha; fin_cases ha <;> simp only [TAct.tape] <;> decide), hQc2]
          exact Tape.counter'_inc hc2
      -- 分岐ごとのテープの動き
      have hS'F : Tape.SeqView blank (S' tF) (leftSym :: fw) (p - 1 - w₀.length) := by
        by_cases hcase : w₀.length < p
        · have hstep : S' tF = Tape.step blank (S tF) (S tF).focus .left := by
            rw [hS', pairBody, if_pos hcase, pairRoundF]
            show applyG blank (applyG blank (applyG blank Q (TAct.copy tU tF .right))
              (TAct.keep tF .left)) (TAct.put tC2 blank .right) tF = _
            rw [applyG_ne blank _ _ (by decide : tF ≠ tC2), applyG_keep_self,
              applyG_ne blank Q (TAct.copy tU tF (sc := sc) .right) (by decide : tF ≠ tU),
              hQne tF (by decide)]
          rw [hstep, show p - 1 - w₀.length = (p - w₀.length) - 1 from by omega]
          have h2 : p - w₀.length = (p - 1 - w₀.length) + 1 := by omega
          rw [h2] at hF
          simpa [show p - w₀.length - 1 = p - 1 - w₀.length from by omega] using
            Tape.seq_move_left hF
        · have hstep : S' tF = S tF := by
            rw [hS', pairBody, if_neg hcase]
            rw [runG_untouched blank tF _ _ (by
              intro a ha; fin_cases ha <;> simp only [TAct.tape] <;> decide), hQne tF (by decide)]
          rw [hstep, show p - 1 - w₀.length = 0 from by omega,
            show p - w₀.length = 0 from by omega] at *
          exact hF
      have hS'In : Tape.SeqView blank (S' tIn) (leftSym :: w₀) (min (p - 1) w₀.length) := by
        by_cases hcase : w₀.length < p
        · have hstep : S' tIn = S tIn := by
            rw [hS', pairBody, if_pos hcase]
            rw [runG_untouched blank tIn _ _ (by
              intro a ha; fin_cases ha <;> simp only [TAct.tape] <;> decide), hQne tIn (by decide)]
          rw [hstep, show min (p - 1) w₀.length = min p w₀.length from by omega]
          exact hIn
        · have hstep : S' tIn = Tape.step blank (S tIn) (S tIn).focus .left := by
            rw [hS', pairBody, if_neg hcase, pairRoundI]
            show applyG blank (applyG blank (applyG blank Q (TAct.copy tU tIn .right))
              (TAct.keep tIn .left)) (TAct.put tC2 blank .right) tIn = _
            rw [applyG_ne blank _ _ (by decide : tIn ≠ tC2), applyG_keep_self,
              applyG_ne blank Q (TAct.copy tU tIn (sc := sc) .right) (by decide : tIn ≠ tU),
              hQne tIn (by decide)]
          have h2 : min p w₀.length = (min (p - 1) w₀.length) + 1 := by omega
          rw [h2] at hIn
          rw [hstep]
          exact Tape.seq_move_left hIn
      have hS'U : Tape.StackView blank (S' tU) (c :: L) := by
        by_cases hcase : w₀.length < p
        · have hstep : S' tU = Tape.step blank (S tU) (S tF).focus .right := by
            rw [hS', pairBody, if_pos hcase, pairRoundF]
            show applyG blank (applyG blank (applyG blank Q (TAct.copy tU tF .right))
              (TAct.keep tF .left)) (TAct.put tC2 blank .right) tU = _
            rw [applyG_ne blank _ _ (by decide : tU ≠ tC2),
              applyG_ne blank _ (TAct.keep tF (sc := sc) .left) (by decide : tU ≠ tF),
              applyG_copy_self, hQne tU (by decide), hQne tF (by decide)]
          rw [hstep, hc, if_pos hcase]
          exact Tape.push_spec hU _
        · have hstep : S' tU = Tape.step blank (S tU) (S tIn).focus .right := by
            rw [hS', pairBody, if_neg hcase, pairRoundI]
            show applyG blank (applyG blank (applyG blank Q (TAct.copy tU tIn .right))
              (TAct.keep tIn .left)) (TAct.put tC2 blank .right) tU = _
            rw [applyG_ne blank _ _ (by decide : tU ≠ tC2),
              applyG_ne blank _ (TAct.keep tIn (sc := sc) .left) (by decide : tU ≠ tIn),
              applyG_copy_self, hQne tU (by decide), hQne tIn (by decide)]
          rw [hstep, hc, if_neg hcase]
          exact Tape.push_spec hU _
      -- 帰納法の仮定
      obtain ⟨eIH, f1, f2, f3, f4, f5, f6⟩ := ih (p - 1) (y + 1) (c :: L) S' (by omega)
        (by omega) hS'cs hS'c2 hS'F hS'In hS'U
      have hrunEq : runG blank (pairActsN blank w₀.length p (n + 1)) S
          = runG blank (pairActsN blank w₀.length (p - 1) n) S' := by
        rw [pairActsN, runG_append, hS', pairFirst]
        rfl
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- 実行
        rw [pairTail]
        refine execG_loop_cont (a := TAct.put tCs blank .stay) ?_ ?_ ?_
        · rw [decLoop_cond (a := tCs) hne hcs]; simp
        · -- 本体の分岐
          have hQF : Q tF = S tF := hQne tF (by decide)
          by_cases hcase : w₀.length < p
          · have hfoc : (S tF).focus ≠ leftSym := by
              intro hcf
              have h1 : (leftSym :: fw)[p - w₀.length]? = some (S tF).focus := hF.focus_eq
              have h2 : p - w₀.length = (p - 1 - w₀.length) + 1 := by omega
              rw [h2, List.getElem?_cons_succ] at h1
              obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 h1
              exact hfF (hcf ▸ hget ▸ List.getElem_mem hlt)
            refine execG_ite_pos ?_ ?_
            · simp only [condOfG, decide_eq_true_eq]; exact hfoc
            · rw [pairBody, if_pos hcase]; exact execG_seqActs _ _
          · have hfocF : (S tF).focus = leftSym := by
              have h1 : (leftSym :: fw)[p - w₀.length]? = some (S tF).focus := hF.focus_eq
              rw [show p - w₀.length = 0 from by omega] at h1
              exact (Option.some.inj h1).symm
            refine execG_ite_neg ?_ ?_
            · simp only [condOfG, decide_eq_false_iff_not, not_not]; exact hfocF
            · rw [pairBody, if_neg hcase]; exact execG_seqActs _ _
        · -- 残り
          have hstate : runG blank (pairBody blank w₀.length p ++ [TAct.put tCs blank .left]) Q
              = applyG blank S' (TAct.put tCs blank .left) := by
            rw [runG_append, hS']; rfl
          rw [hstate]
          exact eIH
      · rw [hrunEq]; exact f1
      · rw [hrunEq, show y + (n + 1) = y + 1 + n from by omega]; exact f2
      · rw [hrunEq, show p - (n + 1) - w₀.length = p - 1 - n - w₀.length from by omega]
        exact f3
      · rw [hrunEq, show p - (n + 1) = p - 1 - n from by omega]; exact f4
      · rw [hrunEq, ← hkey]; exact f5
      · intro j hu hf hi hcsj hc2j
        rw [hrunEq, f6 j hu hf hi hcsj hc2j, hS'ne j hu hf hi hcsj hc2j]

/-- `pairLoopProg` の完全な動作列（末尾にプローブ＋復元の 2 動作が付く）。 -/
def pairLoopActs (blank : Fin sc) (h₀ p n : ℕ) : List (TAct 13 sc) :=
  pairActsN blank h₀ p n ++ [TAct.put tCs blank .left, TAct.keep tCs .right]

@[simp] theorem pairLoopActs_length (blank : Fin sc) (h₀ p n : ℕ) :
    (pairLoopActs blank h₀ p n).length = 5 * n + 2 := by
  rw [pairLoopActs, List.length_append, pairActsN_length]; simp

/-- **カウンタ駆動＋ソース分岐ループ全体**。 -/
theorem pairLoopProg_exec (hne : mark ≠ blank) {w₀ fw : List (Fin sc)}
    (hfF : leftSym ∉ fw) (n p y : ℕ) (L : List (Fin sc)) (S : Tapes13 sc)
    (hnp : n ≤ p) (hpl : p ≤ w₀.length + fw.length)
    (hcs : Tape.CounterView' blank mark (S tCs) n)
    (hc2 : Tape.CounterView' blank mark (S tC2) y)
    (hF : Tape.SeqView blank (S tF) (leftSym :: fw) (p - w₀.length))
    (hIn : Tape.SeqView blank (S tIn) (leftSym :: w₀) (min p w₀.length))
    (hU : Tape.StackView blank (S tU) L) :
    ExecG Terminal blank (pairLoopProg blank mark leftSym) S
        (pairLoopActs blank w₀.length p n) ∧
      runG blank (pairLoopActs blank w₀.length p n) S
        = runG blank (pairActsN blank w₀.length p n) S ∧
      Tape.CounterView' blank mark (runG blank (pairActsN blank w₀.length p n) S tCs) 0 ∧
      Tape.CounterView' blank mark (runG blank (pairActsN blank w₀.length p n) S tC2) (y + n) ∧
      Tape.SeqView blank (runG blank (pairActsN blank w₀.length p n) S tF)
        (leftSym :: fw) (p - n - w₀.length) ∧
      Tape.SeqView blank (runG blank (pairActsN blank w₀.length p n) S tIn)
        (leftSym :: w₀) (min (p - n) w₀.length) ∧
      Tape.StackView blank (runG blank (pairActsN blank w₀.length p n) S tU)
        (((w₀ ++ fw).take p).drop (p - n) ++ L) ∧
      (∀ j : Fin 13, j ≠ tU → j ≠ tF → j ≠ tIn → j ≠ tCs → j ≠ tC2 →
        runG blank (pairActsN blank w₀.length p n) S j = S j) := by
  obtain ⟨e, f1, f2, f3, f4, f5, f6⟩ :=
    pairLoop_tail (Terminal := Terminal) hne hfF n p y L S hnp hpl hcs hc2 hF hIn hU
  refine ⟨?_, ?_, f1, f2, f3, f4, f5, f6⟩
  · have e0 := execG_act (Terminal := Terminal) (blank := blank) (TAct.put tCs blank .left) S
    have e2 := execG_act (Terminal := Terminal) (blank := blank) (TAct.keep tCs .right)
      (runG blank (pairTail blank w₀.length p n) (applyG blank S (TAct.put tCs blank .left)))
    have hcomb := execG_seq e0 (execG_seq (by
        show ExecG Terminal blank _ (runG blank [TAct.put tCs blank (sc := sc) .left] S) _
        exact e) e2)
    refine execG_of_eq ?_ hcomb
    calc [TAct.put tCs blank (sc := sc) .left]
            ++ (pairTail blank w₀.length p n ++ [TAct.keep tCs .right])
        = (TAct.put tCs blank .left :: pairTail blank w₀.length p n)
            ++ [TAct.keep tCs (sc := sc) .right] := by simp
      _ = pairLoopActs blank w₀.length p n := by
            rw [pairCons]; simp [pairLoopActs]
  · rw [pairLoopActs, runG_append]
    exact probeRestore_id (mark := mark) f1

end PairLoop

/-! ## 5. 12 本版の単進カウンタ操作を 13 本に持ち上げる -/

section KLoop

open PalPeg.PatternProg.Twelve
open PalPeg.PatternTapes

theorem tC1_inj : tC1 = inj sC1 := rfl
theorem tC2_inj : tC2 = inj sC2 := rfl
theorem tAn_inj : tAn = inj sAn := rfl
theorem tU_inj : tU = inj sU := rfl
theorem tP_inj : tP = inj sP := rfl
theorem tIn_inj : tIn = inj sIn := rfl
theorem tCs_inj : tCs = inj sCs := rfl

theorem decActsN_map (blank : Fin sc) (a : Fin 12) (body : List (TAct 12 sc)) :
    ∀ n : ℕ, (decActsN blank a body n).map liftT
      = decActsN blank (inj a) (body.map liftT) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [decActsN, decActsN, List.map_append, ih]; rfl

/-- `xfer2` の 13 本版プログラムと動作列。 -/
def xfer2Prog13 (blank mark : Fin sc) (a b c : Fin 13) : Prog (ActG 13 sc) (CondG 13 sc) :=
  decLoopProg blank a [TAct.put b blank .right, TAct.put c blank .right] mark

def xfer2Acts13 (blank : Fin sc) (a b c : Fin 13) (n : ℕ) : List (TAct 13 sc) :=
  decActsN blank a [TAct.put b blank .right, TAct.put c blank .right] n
    ++ [TAct.put a blank .left, TAct.keep a .right]

def xfer1Prog13 (blank mark : Fin sc) (a b : Fin 13) : Prog (ActG 13 sc) (CondG 13 sc) :=
  decLoopProg blank a [TAct.put b blank .right] mark

def xfer1Acts13 (blank : Fin sc) (a b : Fin 13) (n : ℕ) : List (TAct 13 sc) :=
  decActsN blank a [TAct.put b blank .right] n ++ [TAct.put a blank .left, TAct.keep a .right]

theorem xfer2Acts13_map (blank : Fin sc) (a b c : Fin 12) (n : ℕ) :
    xfer2Acts13 blank (inj a) (inj b) (inj c) n = (xfer2Acts blank a b c n).map liftT := by
  rw [xfer2Acts13, xfer2Acts, List.map_append, decActsN_map]
  rfl

theorem xfer1Acts13_map (blank : Fin sc) (a b : Fin 12) (n : ℕ) :
    xfer1Acts13 blank (inj a) (inj b) n = (xfer1Acts blank a b n).map liftT := by
  rw [xfer1Acts13, xfer1Acts, List.map_append, decActsN_map]
  rfl

/-- `kRound` の 13 本版。 -/
def kRoundProg13 (blank mark : Fin sc) : Prog (ActG 13 sc) (CondG 13 sc) :=
  Prog.seq (xfer2Prog13 blank mark tC1 tAn tC2) (xfer1Prog13 blank mark tC2 tC1)

def kRoundActs13 (blank : Fin sc) (p : ℕ) : List (TAct 13 sc) :=
  (kRoundActs blank p).map liftT

def kLoopProg13 (blank mark : Fin sc) : ℕ → Prog (ActG 13 sc) (CondG 13 sc)
  | 0 => Prog.skip
  | m + 1 => Prog.seq (kRoundProg13 blank mark) (kLoopProg13 blank mark m)

def kLoopActs13 (blank : Fin sc) (p : ℕ) (m : ℕ) : List (TAct 13 sc) :=
  (kLoopActs blank p m).map liftT

theorem kLoopActs13_succ (blank : Fin sc) (p m : ℕ) :
    kLoopActs13 blank p (m + 1) = kRoundActs13 blank p ++ kLoopActs13 blank p m := by
  simp only [kLoopActs13, kRoundActs13,
    show kLoopActs blank p (m + 1) = kRoundActs blank p ++ kLoopActs blank p m from rfl,
    List.map_append]

@[simp] theorem kLoopActs13_length (blank : Fin sc) (p m : ℕ) :
    (kLoopActs13 blank p m).length = m * (7 * p + 4) := by
  simp [kLoopActs13]

variable {blank mark : Fin sc}

theorem kRoundActs13_eq (p : ℕ) :
    kRoundActs13 (sc := sc) blank p
      = xfer2Acts13 blank tC1 tAn tC2 p ++ xfer1Acts13 blank tC2 tC1 p := by
  rw [kRoundActs13, kRoundActs, List.map_append, tC1_inj, tC2_inj, tAn_inj,
    xfer2Acts13_map blank sC1 sAn sC2 p, xfer1Acts13_map blank sC2 sC1 p]

theorem kRoundProg13_exec {S : Tapes13 sc} {p y : ℕ} (hne : mark ≠ blank)
    (h1 : Tape.CounterView' blank mark (S tC1) p)
    (h2 : Tape.CounterView' blank mark (S tC2) 0)
    (h3 : Tape.CounterView' blank mark (S tAn) y) :
    ExecG Terminal blank (kRoundProg13 blank mark) S (kRoundActs13 blank p) := by
  have h1' : Tape.CounterView' blank mark (prj S sC1) p := h1
  have h2' : Tape.CounterView' blank mark (prj S sC2) 0 := h2
  have h3' : Tape.CounterView' blank mark (prj S sAn) y := h3
  obtain ⟨-, -, g3⟩ := xfer2_spec (blank := blank) (mark := mark) (a := sC1) (b := sAn)
    (c := sC2) (by decide) (by decide) (by decide) p (prj S) 0 y 0 (by simpa using h1') h3' h2'
  have e1 : ExecG Terminal blank (xfer2Prog13 blank mark tC1 tAn tC2) S
      (xfer2Acts13 blank tC1 tAn tC2 p) :=
    decLoopProg_exec hne (by intro x hx; fin_cases hx <;> (simp only [TAct.tape]; decide)) p S h1
  have hmid : Tape.CounterView' blank mark
      (runG blank (xfer2Acts13 blank tC1 tAn tC2 p) S tC2) p := by
    rw [tC1_inj, tC2_inj, tAn_inj, xfer2Acts13_map blank sC1 sAn sC2 p,
      prj_runG_map_at blank _ S sC2,
      xfer2Acts_run (mark := mark) (by decide) (by decide) (by decide) p (prj S) h1' h3' h2']
    simpa using g3
  have e2 : ExecG Terminal blank (xfer1Prog13 blank mark tC2 tC1)
      (runG blank (xfer2Acts13 blank tC1 tAn tC2 p) S) (xfer1Acts13 blank tC2 tC1 p) :=
    decLoopProg_exec hne (by intro x hx; fin_cases hx <;> (simp only [TAct.tape]; decide)) p _
      hmid
  exact execG_of_eq (kRoundActs13_eq p).symm (execG_seq e1 e2)

theorem kRoundActs13_prj {S : Tapes13 sc} {p y : ℕ}
    (h1 : Tape.CounterView' blank mark (S tC1) p)
    (h2 : Tape.CounterView' blank mark (S tC2) 0)
    (h3 : Tape.CounterView' blank mark (S tAn) y) :
    prj (runG blank (kRoundActs13 blank p) S) = run blank (kRound blank (prj S)) (prj S) := by
  rw [kRoundActs13, prj_runG_map]
  exact kRoundActs_run (mark := mark) h1 h2 h3

theorem kLoopProg13_exec (hne : mark ≠ blank) : ∀ (m : ℕ) (S : Tapes13 sc) (p y : ℕ),
    Tape.CounterView' blank mark (S tC1) p →
    Tape.CounterView' blank mark (S tC2) 0 →
    Tape.CounterView' blank mark (S tAn) y →
    ExecG Terminal blank (kLoopProg13 blank mark m) S (kLoopActs13 blank p m) := by
  intro m
  induction m with
  | zero => intro S p y _ _ _; exact execG_skip
  | succ m ih =>
      intro S p y h1 h2 h3
      have hprj := kRoundActs13_prj (mark := mark) h1 h2 h3
      obtain ⟨e1, e2, e3, -, -⟩ := kRound_spec (blank := blank) (mark := mark)
        (S := prj S) (p := p) (y := y) h1 h2 h3
      have k1 : Tape.CounterView' blank mark (runG blank (kRoundActs13 blank p) S tC1) p := by
        show Tape.CounterView' blank mark (prj (runG blank (kRoundActs13 blank p) S) sC1) p
        rw [hprj]; exact e1
      have k2 : Tape.CounterView' blank mark (runG blank (kRoundActs13 blank p) S tC2) 0 := by
        show Tape.CounterView' blank mark (prj (runG blank (kRoundActs13 blank p) S) sC2) 0
        rw [hprj]; exact e2
      have k3 : Tape.CounterView' blank mark
          (runG blank (kRoundActs13 blank p) S tAn) (y + p) := by
        show Tape.CounterView' blank mark (prj (runG blank (kRoundActs13 blank p) S) sAn) (y + p)
        rw [hprj]; exact e3
      have := execG_seq (kRoundProg13_exec (Terminal := Terminal) hne h1 h2 h3)
        (ih (runG blank (kRoundActs13 blank p) S) p (y + p) k1 k2 k3)
      exact execG_of_eq (kLoopActs13_succ blank p m).symm this

theorem kLoopActs13_prj (hne : mark ≠ blank) (m : ℕ) (S : Tapes13 sc) (p y : ℕ)
    (h1 : Tape.CounterView' blank mark (S tC1) p)
    (h2 : Tape.CounterView' blank mark (S tC2) 0)
    (h3 : Tape.CounterView' blank mark (S tAn) y) :
    prj (runG blank (kLoopActs13 blank p m) S) = run blank (kLoop blank m (prj S)) (prj S) := by
  rw [kLoopActs13, prj_runG_map]
  exact (kLoopProg_exec (Terminal := Unit) hne m (prj S) p y h1 h2 h3).2

theorem kLoopActs13_tF (blank : Fin sc) (p m : ℕ) (S : Tapes13 sc) :
    runG blank (kLoopActs13 blank p m) S tF = S tF := runG_map_tF blank _ S

end KLoop

/-! ## 6. 準備フェーズ（2 本ソース・入力非依存版） -/

section Setup

open PalPeg.PatternProg.Twelve
open PalPeg.PatternTapes

/-- 13 本のテープ番号は `tF` か 12 本版の埋め込みかのどちらか。 -/
theorem fin13_cases (j : Fin 13) : j = tF ∨ ∃ i : Fin 12, inj i = j := by
  rcases eq_or_ne j tF with h | h
  · exact Or.inl h
  · refine Or.inr ⟨⟨j.val, ?_⟩, rfl⟩
    have h12 := j.isLt
    have hne : j.val ≠ 12 := fun hv => h (Fin.ext hv)
    omega

/-- 番兵付きの語から `b` 個読んだときに積まれる語。 -/
theorem take_drop_sent (x : Fin sc) (l : List (Fin sc)) (b : ℕ) :
    ((x :: l).take (b + 1)).drop (b + 1 - b) = l.take b := by
  simp

/-- `tF` 側と `tIn` 側の残りを合わせると `w.take (h - s)` になる。 -/
theorem pair_take_split (w : List (Fin sc)) {h h₀ s : ℕ} (hlt : h₀ < h) (hcut : s < h) :
    (w.take h₀).take (min (h - s) h₀)
        ++ ((w.drop h₀).take (h - h₀)).take (h - s - h₀)
      = w.take (h - s) := by
  rcases Nat.lt_or_ge h₀ (h - s) with hgt | hle
  · rw [Nat.min_eq_right (by omega), List.take_take, Nat.min_eq_left (le_refl h₀),
      List.take_take, Nat.min_eq_left (by omega),
      show h - s = h₀ + (h - s - h₀) from by omega, List.take_add]
    simp
  · rw [List.take_take, Nat.min_eq_left (by omega),
      show h - s - h₀ = 0 from by omega, List.take_zero, List.append_nil,
      Nat.min_eq_left hle]

/-- 前置き（`tU`,`tP` に `startSym` を積み、最前線テープを 1 歩左へ）。 -/
def prologueProgP (blank startSym : Fin sc) : Prog (ActG 13 sc) (CondG 13 sc) :=
  Prog.seq (pushBothProgP startSym) (ACT (TAct.put tF blank .left))

def prologueActsP (blank startSym : Fin sc) : List (TAct 13 sc) :=
  pushBothActsP startSym ++ [TAct.put tF blank .left]

theorem prologueActsP_runP (blank startSym : Fin sc) (S : Tapes13 sc) :
    runG blank (prologueActsP blank startSym) S = runP blank (prologueP blank startSym) S := by
  rw [prologueP, runP_eq]; rfl

theorem prologueProgP_exec {blank : Fin sc} (startSym : Fin sc) (S : Tapes13 sc) :
    ExecG Terminal blank (prologueProgP blank startSym) S (prologueActsP blank startSym) :=
  execG_of_eq rfl (execG_seq (pushBothProgP_exec startSym S) (execG_act _ _))

/-- **2 本ソース版の準備前提**（`PatternProg.PrepPreL` の 2 本ソース版）。
`PatternTapesPair.SetupPrePair` の `inb₀` / `inF` を、内容の左隣に番兵 `leftSym` を
置いた形に強めたもの。`s`,`h`,`h₀` は入力ごとに変わってよい。 -/
structure PrepPreLPair (blank mark leftSym : Fin sc) (s h h₀ p₁ r : ℕ)
    (w Text : List (Fin sc)) (S : Tapes13 sc) : Prop where
  hpos : 0 < h₀
  hlt : h₀ < h
  hle : h ≤ w.length
  hcut : s < h
  hfresh : leftSym ∉ w
  inb₀ : Tape.SeqView blank (S tIn) (leftSym :: w.take h₀) h₀
  inF : InputCopy.FrontierView blank (S tF) (leftSym :: (w.drop h₀).take (h - h₀))
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

/-- **入力に依存しない 2 本ソース版準備フェーズのプログラム**。
`s`, `h`, `h₀` のどれにも依存しない（`k` だけが構成の定数）。 -/
def setupProgPairL (blank startSym endSym mark leftSym : Fin sc) (k : ℕ) :
    Prog (ActG 13 sc) (CondG 13 sc) :=
  Prog.seq (prologueProgP blank startSym)
    (Prog.seq (Prog.seq (pairLoopProg blank mark leftSym) (xfer1Prog13 blank mark tC2 tCs))
      (Prog.seq
        (Prog.loop (tF, leftSym) (TAct.copy tP tF (sc := sc) .right).act
          (ACT (TAct.keep tF .left)))
        (Prog.seq
          (Prog.loop (tIn, leftSym) (TAct.copy tP tIn (sc := sc) .right).act
            (ACT (TAct.keep tIn .left)))
          (Prog.seq (pushBothProgP endSym)
            (Prog.seq (settleProgG tU blank startSym)
              (Prog.seq (settleProgG tP blank startSym) (kLoopProg13 blank mark k)))))))

/-- `setupProgPairL` が実行する動作列。 -/
def setupProgPairLActs (blank startSym endSym : Fin sc) (s h h₀ k p₁ : ℕ) :
    List (TAct 13 sc) :=
  prologueActsP blank startSym ++
    (pairLoopActs blank h₀ h s ++
      (xfer1Acts13 blank tC2 tCs s ++
        (copyActsN tF tP (h - s - h₀) ++
          (copyActsN tIn tP (min (h - s) h₀) ++
            (pushBothActsP endSym ++
              ((TAct.put tU blank .left :: (leftWalkG tU (s + 1) ++ [TAct.keep tU .right])) ++
                ((TAct.put tP blank .left ::
                    (leftWalkG tP (h - s + 1) ++ [TAct.keep tP .right])) ++
                  kLoopActs13 blank p₁ k)))))))

/-- 実行結果のテープ。 -/
def setupTapesPairL (blank startSym endSym : Fin sc) (s h h₀ k p₁ : ℕ) (S : Tapes13 sc) :
    Tapes13 sc :=
  runG blank (setupProgPairLActs blank startSym endSym s h h₀ k p₁) S

/-- **動作数**。`tF` 側と `tIn` 側の残りは合わせて `h - s` なので、
`setupProgL` の `14 + 9*s + 3*hms + k*(7*p₁+4)` と同型の式になる。 -/
theorem setupProgPairL_trace_length {blank startSym endSym : Fin sc} (s h h₀ k p₁ : ℕ)
    (_hlt : h₀ < h) (hcut : s < h) :
    (setupProgPairLActs blank startSym endSym s h h₀ k p₁).length
      = 15 + 9 * s + 3 * (h - s) + k * (7 * p₁ + 4) := by
  simp only [setupProgPairLActs, prologueActsP, pushBothActsP, List.length_append,
    pairLoopActs_length, xfer1Acts13, decActsN_length, copyActsN_length, leftWalkG_length,
    kLoopActs13_length, List.length_cons, List.length_nil]
  omega

variable {blank mark : Fin sc}

/-- **中心となる補題**：`setupProgPairL` はちょうど `setupProgPairLActs` を実行し、
その結果のテープは `PatternTapesPair.setup_core` と同じ内容になる。 -/
theorem setupProgPairL_core {startSym endSym leftSym : Fin sc} {s h h₀ p₁ r k : ℕ}
    {w Text : List (Fin sc)} {S : Tapes13 sc}
    (H : PrepPreLPair blank mark leftSym s h h₀ p₁ r w Text S) (hne : mark ≠ blank)
    (hSw : startSym ∉ w) (hSE : startSym ≠ endSym) :
    ExecG Terminal blank (setupProgPairL blank startSym endSym mark leftSym k) S
        (setupProgPairLActs blank startSym endSym s h h₀ k p₁) ∧
      Tape.SeqView blank (setupTapesPairL blank startSym endSym s h h₀ k p₁ S tP)
        (startSym :: ((w.take h).reverse.drop s ++ [endSym])) 1 ∧
      Tape.SeqView blank (setupTapesPairL blank startSym endSym s h h₀ k p₁ S tU)
        (startSym :: ((w.take h).reverse.take s ++ [endSym])) 1 ∧
      Tape.CounterView' blank mark
        (setupTapesPairL blank startSym endSym s h h₀ k p₁ S tC1) p₁ ∧
      Tape.CounterView' blank mark
        (setupTapesPairL blank startSym endSym s h h₀ k p₁ S tC2) 0 ∧
      Tape.CounterView' blank mark
        (setupTapesPairL blank startSym endSym s h h₀ k p₁ S tAn) (k * p₁) ∧
      (∀ j : Fin 13, j ≠ tU → j ≠ tP → j ≠ tC1 → j ≠ tC2 → j ≠ tAn → j ≠ tF → j ≠ tIn →
        j ≠ tCs → setupTapesPairL blank startSym endSym s h h₀ k p₁ S j = S j) := by
  obtain ⟨hpos, hlt, hle, hcut, hfresh, hIn, hF, hU, hP, hT, hX2, hCs, hC1, hC2, hAp, hAn,
    hRp, hRn⟩ := H
  set m := h - h₀ with hm
  set w₀ := w.take h₀ with hw₀
  set fw := (w.drop h₀).take m with hfw
  have hw₀len : w₀.length = h₀ := by rw [hw₀]; simp only [List.length_take]; omega
  have hfwlen : fw.length = m := by
    rw [hfw]; simp only [List.length_take, List.length_drop]; omega
  have hWlen : (w.take h).length = h := by simp only [List.length_take]; omega
  have hWsplit : w.take h = w₀ ++ fw := by
    have he : h₀ + m = h := by omega
    calc w.take h = w.take (h₀ + m) := by rw [he]
      _ = _ := List.take_add ..
  have hWtake : (w₀ ++ fw).take h = w.take h := by
    rw [← hWsplit, List.take_take, Nat.min_self]
  have hfreshF : leftSym ∉ fw := by
    rw [hfw]
    exact fun hc => hfresh (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  have hfreshI : leftSym ∉ w₀ := by
    rw [hw₀]; exact fun hc => hfresh (List.mem_of_mem_take hc)
  -- 段のパターン
  have hueq : ((w.take h).drop (h - s)).reverse = (w.take h).reverse.take s := by
    rw [List.take_reverse, hWlen]
  have hveq : (w.take (h - s)).reverse = (w.take h).reverse.drop s := by
    rw [List.drop_reverse, hWlen, List.take_take, Nat.min_eq_left (by omega)]
  -- フェーズ 0
  obtain ⟨S₀, hS0⟩ : ∃ T, runG blank (prologueActsP blank startSym) S = T := ⟨_, rfl⟩
  have hS0P : S₀ = runP blank (prologueP blank startSym) S := by
    rw [← hS0, prologueActsP_runP]
  have p0U : Tape.StackView blank (S₀ tU) [startSym] := by
    rw [hS0P, prologueP_U]; exact Tape.push_spec hU startSym
  have p0P : Tape.StackView blank (S₀ tP) [startSym] := by
    rw [hS0P, prologueP_P]; exact Tape.push_spec hP startSym
  have p0F : Tape.SeqView blank (S₀ tF) (leftSym :: fw) m := by
    rw [hS0P, prologueP_F]
    have h1 := InputCopy.toSeqView hF (by simp)
    rw [show (leftSym :: fw).length - 1 = m from by simp [hfwlen]] at h1
    exact h1
  have p0ne : ∀ j : Fin 13, j ≠ tU → j ≠ tP → j ≠ tF → S₀ j = S j := by
    intro j hu hp hf; rw [hS0P]; exact prologueP_ne blank startSym hu hp hf S
  -- フェーズ 1（カウンタ駆動＋ソース分岐）
  have p0In : Tape.SeqView blank (S₀ tIn) (leftSym :: w₀) (min h w₀.length) := by
    rw [p0ne tIn (by decide) (by decide) (by decide), hw₀len,
      show min h h₀ = h₀ from by omega]
    exact hIn
  have p0Cs : Tape.CounterView' blank mark (S₀ tCs) s := by
    rw [p0ne tCs (by decide) (by decide) (by decide)]; exact hCs
  have p0C2 : Tape.CounterView' blank mark (S₀ tC2) 0 := by
    rw [p0ne tC2 (by decide) (by decide) (by decide)]; exact hC2
  obtain ⟨E1, hrun1, q1cs, q1c2, q1F, q1In, q1U, q1ne⟩ :=
    pairLoopProg_exec (Terminal := Terminal) (leftSym := leftSym) hne hfreshF s h 0 [startSym] S₀
      (by omega) (by rw [hw₀len, hfwlen]; omega) p0Cs p0C2
      (by rw [hw₀len]; exact p0F) p0In p0U
  rw [hw₀len] at E1 hrun1 q1cs q1c2 q1F q1In q1U q1ne
  rw [← hrun1] at q1cs q1c2 q1F q1In q1U q1ne
  obtain ⟨S₁, hS1⟩ : ∃ T, runG blank (pairLoopActs blank h₀ h s) S₀ = T := ⟨_, rfl⟩
  rw [hS1] at q1cs q1c2 q1F q1In q1U q1ne
  have p1U : Tape.StackView blank (S₁ tU) ((w.take h).drop (h - s) ++ [startSym]) := by
    rwa [hWtake] at q1U
  have p1F : Tape.SeqView blank (S₁ tF) (leftSym :: fw) (h - s - h₀) := q1F
  have p1In : Tape.SeqView blank (S₁ tIn) (leftSym :: w₀) (min (h - s) h₀) := q1In
  have p1P : Tape.StackView blank (S₁ tP) [startSym] := by
    rw [q1ne tP (by decide) (by decide) (by decide) (by decide) (by decide)]; exact p0P
  have p1C1 : Tape.CounterView' blank mark (S₁ tC1) p₁ := by
    rw [q1ne tC1 (by decide) (by decide) (by decide) (by decide) (by decide),
      p0ne tC1 (by decide) (by decide) (by decide)]
    exact hC1
  have p1An : Tape.CounterView' blank mark (S₁ tAn) 0 := by
    rw [q1ne tAn (by decide) (by decide) (by decide) (by decide) (by decide),
      p0ne tAn (by decide) (by decide) (by decide)]
    exact hAn
  -- フェーズ 1b（ミラー `tC2` を `tCs` に戻す）
  obtain ⟨S₂, hS2⟩ : ∃ T, runG blank (xfer1Acts13 blank tC2 tCs s) S₁ = T := ⟨_, rfl⟩
  have hq1c2 : Tape.CounterView' blank mark (S₁ tC2) s := by simpa using q1c2
  have hq1c2' : Tape.CounterView' blank mark (prj S₁ sC2) s := hq1c2
  have hq1cs' : Tape.CounterView' blank mark (prj S₁ sCs) 0 := q1cs
  have hprj2 : prj S₂ = run blank (xfer1 blank sC2 sCs s) (prj S₁) := by
    rw [← hS2, tC2_inj, tCs_inj, xfer1Acts13_map, prj_runG_map]
    exact xfer1Acts_run (mark := mark) (a := sC2) (b := sCs) (by decide) s (prj S₁)
      hq1c2' hq1cs'
  obtain ⟨g1, -⟩ := xfer1_spec (blank := blank) (mark := mark) (a := sC2) (b := sCs)
    (by decide) s (prj S₁) 0 0 (by simpa using hq1c2') hq1cs'
  have p2C2 : Tape.CounterView' blank mark (S₂ tC2) 0 := by
    show Tape.CounterView' blank mark (prj S₂ sC2) 0
    rw [hprj2]; exact g1
  have p2ne : ∀ j : Fin 13, j ≠ tC2 → j ≠ tCs → S₂ j = S₁ j := by
    intro j hc2 hcs
    rcases fin13_cases j with rfl | ⟨i, rfl⟩
    · rw [← hS2, tC2_inj, tCs_inj, xfer1Acts13_map]
      exact runG_map_tF blank _ S₁
    · show prj S₂ i = prj S₁ i
      rw [hprj2]
      exact xfer1_untouched blank (a := sC2) (b := sCs)
        (fun hc => hc2 (by rw [hc]; rfl)) (fun hc => hcs (by rw [hc]; rfl)) s (prj S₁)
  -- フェーズ 2（`tF` → `tP`、番兵まで）
  obtain ⟨S₃, hS3⟩ : ∃ T, runG blank (copyActsN tF tP (h - s - h₀)) S₂ = T := ⟨_, rfl⟩
  have p2F : Tape.SeqView blank (S₂ tF) (leftSym :: fw) (h - s - h₀) := by
    rw [p2ne tF (by decide) (by decide)]; exact p1F
  have p2In : Tape.SeqView blank (S₂ tIn) (leftSym :: w₀) (min (h - s) h₀) := by
    rw [p2ne tIn (by decide) (by decide)]; exact p1In
  have p2P : Tape.StackView blank (S₂ tP) [startSym] := by
    rw [p2ne tP (by decide) (by decide)]; exact p1P
  have p2U : Tape.StackView blank (S₂ tU) ((w.take h).drop (h - s) ++ [startSym]) := by
    rw [p2ne tU (by decide) (by decide)]; exact p1U
  obtain ⟨p3F, p3P⟩ := copyLoopL_spec blank (i := tF) (j := tP) (by decide) (h - s - h₀)
    (h - s - h₀) S₂ (leftSym :: fw) [startSym] (by omega) p2F p2P
  have hS3P : S₃ = runP blank (copyLoopL blank tF tP (h - s - h₀) S₂) S₂ := by
    rw [← hS3, copyActsN_runP]
  rw [← hS3P] at p3F p3P
  rw [Nat.sub_self] at p3F
  rw [take_drop_sent] at p3P
  have p3ne : ∀ j : Fin 13, j ≠ tF → j ≠ tP → S₃ j = S₂ j := by
    intro j hf hp; rw [hS3P]; exact copyLoopL_untouched blank hf hp _ _
  -- フェーズ 3（`tIn` → `tP`、番兵まで）
  obtain ⟨S₄, hS4⟩ : ∃ T, runG blank (copyActsN tIn tP (min (h - s) h₀)) S₃ = T := ⟨_, rfl⟩
  have p3In : Tape.SeqView blank (S₃ tIn) (leftSym :: w₀) (min (h - s) h₀) := by
    rw [p3ne tIn (by decide) (by decide)]; exact p2In
  obtain ⟨p4In, p4P⟩ := copyLoopL_spec blank (i := tIn) (j := tP) (by decide)
    (min (h - s) h₀) (min (h - s) h₀) S₃ (leftSym :: w₀) (fw.take (h - s - h₀) ++ [startSym])
    (by omega) p3In p3P
  have hS4P : S₄ = runP blank (copyLoopL blank tIn tP (min (h - s) h₀) S₃) S₃ := by
    rw [← hS4, copyActsN_runP]
  rw [← hS4P] at p4In p4P
  rw [Nat.sub_self] at p4In
  rw [take_drop_sent, ← List.append_assoc,
    pair_take_split (w := w) (h := h) (h₀ := h₀) (s := s) hlt hcut] at p4P
  have p4ne : ∀ j : Fin 13, j ≠ tIn → j ≠ tP → S₄ j = S₃ j := by
    intro j hi hp; rw [hS4P]; exact copyLoopL_untouched blank hi hp _ _
  have p4U : Tape.StackView blank (S₄ tU) ((w.take h).drop (h - s) ++ [startSym]) := by
    rw [p4ne tU (by decide) (by decide), p3ne tU (by decide) (by decide)]; exact p2U
  -- フェーズ 4（`endSym` を積む）
  obtain ⟨S₅, hS5⟩ : ∃ T, runG blank (pushBothActsP endSym) S₄ = T := ⟨_, rfl⟩
  have hS5P : S₅ = runP blank (pushBothN endSym) S₄ := by rw [← hS5, pushBothActsP_runP]
  have p5U : Tape.StackView blank (S₅ tU)
      (endSym :: ((w.take h).drop (h - s) ++ [startSym])) := by
    rw [hS5P, pushBothN_U]; exact Tape.push_spec p4U endSym
  have p5P : Tape.StackView blank (S₅ tP) (endSym :: (w.take (h - s) ++ [startSym])) := by
    rw [hS5P, pushBothN_P]; exact Tape.push_spec p4P endSym
  have p5ne : ∀ j : Fin 13, j ≠ tU → j ≠ tP → S₅ j = S₄ j := by
    intro j hu hp; rw [hS5P]; exact pushBothN_ne blank endSym hu hp S₄
  -- 長さ
  have hulen : ((w.take h).drop (h - s)).length = s := by
    rw [List.length_drop, hWlen]; omega
  have hvlen : (w.take (h - s)).length = h - s := by
    simp only [List.length_take]; omega
  -- フェーズ 5（`tU` の `settle`）
  obtain ⟨S₆, hS6⟩ : ∃ T, runG blank
      (TAct.put tU blank .left :: (leftWalkG tU (s + 1) ++ [TAct.keep tU .right])) S₅ = T :=
    ⟨_, rfl⟩
  have hs6 := settleP_spec blank tU (n := s) p5U
    (by simp only [List.length_append, List.length_cons, List.length_nil, hulen])
  have hxl6 : ∃ x l, ((runP blank (settleP blank tU s) S₅) tU).left = x :: l := by
    have hlenL : ((runP blank (settleP blank tU s) S₅) tU).left.length = 1 := by
      rw [hs6.left_eq, List.length_reverse, List.length_take, Nat.min_eq_left (by
        have := hs6.lt; omega)]
    generalize hL : ((runP blank (settleP blank tU s) S₅) tU).left = L at hlenL ⊢
    cases L with
    | nil => simp at hlenL
    | cons x l => exact ⟨x, l, rfl⟩
  obtain ⟨x6, l6, hxl6⟩ := hxl6
  have hS6P : S₆ = runP blank (settleP blank tU s) S₅ := by
    rw [← hS6, settleActs_runP blank tU s S₅ hxl6]
  have p6U : Tape.SeqView blank (S₆ tU)
      (startSym :: ((w.take h).reverse.take s ++ [endSym])) 1 := by
    rw [hS6P]; simpa [← hueq] using hs6
  have p6ne : ∀ j : Fin 13, j ≠ tU → S₆ j = S₅ j := by
    intro j hu; rw [hS6P]; exact settleP_untouched blank hu _ _
  -- フェーズ 6（`tP` の `settle`）
  obtain ⟨S₇, hS7⟩ : ∃ T, runG blank
      (TAct.put tP blank .left :: (leftWalkG tP (h - s + 1) ++ [TAct.keep tP .right])) S₆ = T :=
    ⟨_, rfl⟩
  have p6P : Tape.StackView blank (S₆ tP) (endSym :: (w.take (h - s) ++ [startSym])) := by
    rw [p6ne tP (by decide)]; exact p5P
  have hs7 := settleP_spec blank tP (n := h - s) p6P
    (by simp only [List.length_append, List.length_cons, List.length_nil, hvlen])
  have hxl7 : ∃ x l, ((runP blank (settleP blank tP (h - s)) S₆) tP).left = x :: l := by
    have hlenL : ((runP blank (settleP blank tP (h - s)) S₆) tP).left.length = 1 := by
      rw [hs7.left_eq, List.length_reverse, List.length_take, Nat.min_eq_left (by
        have := hs7.lt; omega)]
    generalize hL : ((runP blank (settleP blank tP (h - s)) S₆) tP).left = L at hlenL ⊢
    cases L with
    | nil => simp at hlenL
    | cons x l => exact ⟨x, l, rfl⟩
  obtain ⟨x7, l7, hxl7⟩ := hxl7
  have hS7P : S₇ = runP blank (settleP blank tP (h - s)) S₆ := by
    rw [← hS7, settleActs_runP blank tP (h - s) S₆ hxl7]
  have p7P : Tape.SeqView blank (S₇ tP)
      (startSym :: ((w.take h).reverse.drop s ++ [endSym])) 1 := by
    rw [hS7P]; simpa [← hveq] using hs7
  have p7ne : ∀ j : Fin 13, j ≠ tP → S₇ j = S₆ j := by
    intro j hp; rw [hS7P]; exact settleP_untouched blank hp _ _
  -- 触られなかったテープ
  have hkeep : ∀ j : Fin 13, j ≠ tU → j ≠ tP → j ≠ tF → j ≠ tIn → j ≠ tCs → j ≠ tC2 →
      S₇ j = S j := by
    intro j hu hp hf hi hcs hc2
    rw [p7ne j hp, p6ne j hu, p5ne j hu hp, p4ne j hi hp, p3ne j hf hp, p2ne j hc2 hcs,
      q1ne j hu hf hi hcs hc2, p0ne j hu hp hf]
  have p7C1 : Tape.CounterView' blank mark (S₇ tC1) p₁ := by
    rw [hkeep tC1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hC1
  have p7C2 : Tape.CounterView' blank mark (S₇ tC2) 0 := by
    rw [p7ne tC2 (by decide), p6ne tC2 (by decide), p5ne tC2 (by decide) (by decide),
      p4ne tC2 (by decide) (by decide), p3ne tC2 (by decide) (by decide)]
    exact p2C2
  have p7An : Tape.CounterView' blank mark (S₇ tAn) 0 := by
    rw [hkeep tAn (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hAn
  -- フェーズ 7（単進カウンタ）
  obtain ⟨S₈, hS8⟩ : ∃ T, runG blank (kLoopActs13 blank p₁ k) S₇ = T := ⟨_, rfl⟩
  obtain ⟨u1, u2, u3, -, une⟩ := kLoop_spec (blank := blank) (mark := mark) k (prj S₇) p₁ 0
    p7C1 p7C2 p7An
  have hprj8 : prj S₈ = run blank (kLoop blank k (prj S₇)) (prj S₇) := by
    rw [← hS8]
    exact kLoopActs13_prj hne k S₇ p₁ 0 p7C1 p7C2 p7An
  have p8ne : ∀ j : Fin 13, j ≠ tC1 → j ≠ tC2 → j ≠ tAn → S₈ j = S₇ j := by
    intro j h1 h2 h3
    rcases fin13_cases j with rfl | ⟨i, rfl⟩
    · rw [← hS8]; exact kLoopActs13_tF blank p₁ k S₇
    · show prj S₈ i = prj S₇ i
      rw [hprj8]
      exact une i (fun hc => h1 (by rw [hc]; rfl)) (fun hc => h2 (by rw [hc]; rfl))
        (fun hc => h3 (by rw [hc]; rfl))
  -- 全体のテープ
  have hfinal : setupTapesPairL blank startSym endSym s h h₀ k p₁ S = S₈ := by
    show runG blank (setupProgPairLActs blank startSym endSym s h h₀ k p₁) S = S₈
    rw [setupProgPairLActs, runG_append, hS0, runG_append, hS1, runG_append, hS2,
      runG_append, hS3, runG_append, hS4, runG_append, hS5, runG_append, hS6,
      runG_append, hS7, hS8]
  -- 実行
  have hsentU := settle_sentinel_fresh (startSym := startSym) ((w.take h).drop (h - s)) endSym
    (fun hc => hSw (List.mem_of_mem_take (List.mem_of_mem_drop hc))) hSE
  have hsentP := settle_sentinel_fresh (startSym := startSym) (w.take (h - s)) endSym
    (fun hc => hSw (List.mem_of_mem_take hc)) hSE
  have E7 : ExecG Terminal blank (kLoopProg13 blank mark k) S₇ (kLoopActs13 blank p₁ k) :=
    kLoopProg13_exec hne k S₇ p₁ 0 p7C1 p7C2 p7An
  have E6 : ExecG Terminal blank (settleProgG tP blank startSym) S₆
      (TAct.put tP blank .left :: (leftWalkG tP (h - s + 1) ++ [TAct.keep tP .right])) := by
    have := settleProgG_exec (Terminal := Terminal) (i := tP) (sent := startSym) p6P
      hsentP.1 hsentP.2
    rwa [show (w.take (h - s) ++ [startSym]).length = h - s + 1 from by
      simp only [List.length_append, List.length_cons, List.length_nil, hvlen]] at this
  have E5 : ExecG Terminal blank (settleProgG tU blank startSym) S₅
      (TAct.put tU blank .left :: (leftWalkG tU (s + 1) ++ [TAct.keep tU .right])) := by
    have := settleProgG_exec (Terminal := Terminal) (i := tU) (sent := startSym) p5U
      hsentU.1 hsentU.2
    rwa [show ((w.take h).drop (h - s) ++ [startSym]).length = s + 1 from by
      simp only [List.length_append, List.length_cons, List.length_nil, hulen]] at this
  have E4 : ExecG Terminal blank (pushBothProgP endSym) S₄ (pushBothActsP endSym) :=
    pushBothProgP_exec endSym S₄
  have E3 : ExecG Terminal blank
      (Prog.loop (tIn, leftSym) (TAct.copy tP tIn (sc := sc) .right).act
        (ACT (TAct.keep tIn .left))) S₃ (copyActsN tIn tP (min (h - s) h₀)) :=
    copyLoopSentL_exec (Terminal := Terminal) (by decide) hfreshI _ S₃ p3In
  have E2b : ExecG Terminal blank
      (Prog.loop (tF, leftSym) (TAct.copy tP tF (sc := sc) .right).act
        (ACT (TAct.keep tF .left))) S₂ (copyActsN tF tP (h - s - h₀)) :=
    copyLoopSentL_exec (Terminal := Terminal) (by decide) hfreshF _ S₂ p2F
  have E2a : ExecG Terminal blank (xfer1Prog13 blank mark tC2 tCs) S₁
      (xfer1Acts13 blank tC2 tCs s) :=
    decLoopProg_exec hne (by intro x hx; fin_cases hx <;> (simp only [TAct.tape]; decide)) s S₁
      hq1c2
  have E0 : ExecG Terminal blank (prologueProgP blank startSym) S
      (prologueActsP blank startSym) := prologueProgP_exec startSym S
  have F6 := execG_seq E6 (by rw [hS7]; exact E7)
  have F5 := execG_seq E5 (by rw [hS6]; exact F6)
  have F4 := execG_seq E4 (by rw [hS5]; exact F5)
  have F3 := execG_seq E3 (by rw [hS4]; exact F4)
  have F2 := execG_seq E2b (by rw [hS3]; exact F3)
  have F1 := execG_seq (execG_seq E1 (by rw [hS1]; exact E2a)) (by
    rw [runG_append, hS1, hS2]; exact F2)
  have F0 := execG_seq E0 (by rw [hS0]; exact F1)
  refine ⟨execG_of_eq (by simp [setupProgPairLActs]) F0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfinal, p8ne tP (by decide) (by decide) (by decide)]; exact p7P
  · rw [hfinal, p8ne tU (by decide) (by decide) (by decide), p7ne tU (by decide)]; exact p6U
  · rw [hfinal]
    show Tape.CounterView' blank mark (prj S₈ sC1) p₁
    rw [hprj8]; exact u1
  · rw [hfinal]
    show Tape.CounterView' blank mark (prj S₈ sC2) 0
    rw [hprj8]; exact u2
  · rw [hfinal]
    show Tape.CounterView' blank mark (prj S₈ sAn) (k * p₁)
    rw [hprj8]; simpa using u3
  · intro j hu hp h1 h2 h3 hf hi hcs
    rw [hfinal, p8ne j h1 h2 h3, hkeep j hu hp hf hi hcs h2]

/-- **実行**：`setupProgPairL` はちょうど `setupProgPairLActs` を実行し、
その結果のテープが `setupTapesPairL`。 -/
theorem setupProgPairL_exec {startSym endSym leftSym : Fin sc} {s h h₀ p₁ r k : ℕ}
    {w Text : List (Fin sc)} {S : Tapes13 sc}
    (H : PrepPreLPair blank mark leftSym s h h₀ p₁ r w Text S) (hne : mark ≠ blank)
    (hSw : startSym ∉ w) (hSE : startSym ≠ endSym) :
    ExecG Terminal blank (setupProgPairL blank startSym endSym mark leftSym k) S
        (setupProgPairLActs blank startSym endSym s h h₀ k p₁) ∧
      runG blank (setupProgPairLActs blank startSym endSym s h h₀ k p₁) S
        = setupTapesPairL blank startSym endSym s h h₀ k p₁ S :=
  ⟨(setupProgPairL_core H hne hSw hSE).1, rfl⟩

/-- **主定理**：`setupProgPairL`（`s`,`h`,`h₀` に依存しない単一の固定プログラム）は
`PrepPreLPair` のもとで `PatternTapesPair.setup_spec_pair` と同じ符号化を作る。 -/
theorem setupProgPairL_spec {startSym endSym leftSym : Fin sc} {s h h₀ p₁ r k : ℕ}
    {w Text : List (Fin sc)} {S : Tapes13 sc}
    (H : PrepPreLPair blank mark leftSym s h h₀ p₁ r w Text S) (hne : mark ≠ blank)
    (hSw : startSym ∉ w) (hSE : startSym ≠ endSym) :
    (ExecG Terminal blank (setupProgPairL blank startSym endSym mark leftSym k) S
        (setupProgPairLActs blank startSym endSym s h h₀ k p₁) ∧
      runG blank (setupProgPairLActs blank startSym endSym s h h₀ k p₁) S
        = setupTapesPairL blank startSym endSym s h h₀ k p₁ S) ∧
      GSVTapes.VEncodes' blank startSym endSym mark
        ((w.take h).reverse.take s) ((w.take h).reverse.drop s)
        (TextFeed.padW blank Text 0) k p₁ r
        (PatternTapes.toGS (prj (setupTapesPairL blank startSym endSym s h h₀ k p₁ S)),
          PatternTapes.toVExt (prj (setupTapesPairL blank startSym endSym s h h₀ k p₁ S)))
        (⟨0, 0⟩, 0) := by
  refine ⟨setupProgPairL_exec (Terminal := Terminal) H hne hSw hSE, ?_⟩
  obtain ⟨-, gP, gU, g1, g2, g3, gkeep⟩ :=
    setupProgPairL_core (Terminal := Terminal) (startSym := startSym) (endSym := endSym)
      (k := k) H hne hSw hSE
  refine ⟨⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩, ?_, ?_⟩
  · show Tape.SeqView blank (setupTapesPairL blank startSym endSym s h h₀ k p₁ S tP) _ (0 + 1)
    rw [Nat.zero_add]; exact gP
  · show Tape.SeqView blank (setupTapesPairL blank startSym endSym s h h₀ k p₁ S tT) _ (0 + 0)
    rw [Nat.zero_add,
      gkeep tT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)]
    exact H.txt
  · exact g1
  · exact g2
  · show Tape.CounterView' blank mark
      (setupTapesPairL blank startSym endSym s h h₀ k p₁ S tAp) (0 - k * p₁)
    rw [Nat.zero_sub,
      gkeep tAp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)]
    exact H.ap
  · show Tape.CounterView' blank mark
      (setupTapesPairL blank startSym endSym s h h₀ k p₁ S tAn) (k * p₁ - 0)
    rw [Nat.sub_zero]; exact g3
  · show Tape.CounterView' blank mark
      (setupTapesPairL blank startSym endSym s h h₀ k p₁ S tRp) (r - 0)
    rw [Nat.sub_zero,
      gkeep tRp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)]
    exact H.rp
  · show Tape.CounterView' blank mark
      (setupTapesPairL blank startSym endSym s h h₀ k p₁ S tRn) (0 - r)
    rw [Nat.zero_sub,
      gkeep tRn (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)]
    exact H.rn
  · show Tape.SeqView blank (setupTapesPairL blank startSym endSym s h h₀ k p₁ S tU) _ (0 + 1)
    rw [Nat.zero_add]; exact gU
  · show Tape.SeqView blank (setupTapesPairL blank startSym endSym s h h₀ k p₁ S tX2)
      _ (0 - _ + 0)
    rw [Nat.zero_sub, Nat.zero_add,
      gkeep tX2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)]
    exact H.txt2

end Setup

/-! ## 7. 2 本を 1 本にまとめ直す `Prog` 版 -/

section CopyPair

/-- 凍結した 2 本（ヘッドはどちらも添字 `0`）から 1 本のテープ `j` を作るプログラム。
右向きに、空白を読むまで走る。 -/
def copyPairProg (blank : Fin sc) (j : Fin 13) : Prog (ActG 13 sc) (CondG 13 sc) :=
  Prog.seq (copyProgR tIn j blank) (copyProgR tF j blank)

def copyPairActs (j : Fin 13) (h₀ m : ℕ) : List (TAct 13 sc) :=
  copyActsR tIn j h₀ ++ copyActsR tF j m

@[simp] theorem copyPairActs_length (j : Fin 13) (h₀ m : ℕ) :
    (copyPairActs (sc := sc) j h₀ m).length = 2 * h₀ + 2 * m := by
  rw [copyPairActs, List.length_append, copyActsR_length, copyActsR_length]

theorem copyPairActs_runP (blank : Fin sc) (j : Fin 13) (h₀ m : ℕ) (S : Tapes13 sc) :
    runG blank (copyPairActs j h₀ m) S = runP blank (copyPairToSingle blank j h₀ m S) S := by
  rw [copyPairActs, runG_append, copyActsR_runP, copyActsR_runP, copyPairToSingle, seqQ,
    runP_append]

variable {blank : Fin sc}

/-- **実行**：番兵（末尾の空白）駆動で 2 本を読み切る。 -/
theorem copyPairProg_exec {j : Fin 13} (hjI : j ≠ tIn) (hjF : j ≠ tF)
    {S : Tapes13 sc} {w : List (Fin sc)} {h h₀ : ℕ} (hpos : 0 < h₀) (hlt : h₀ < h)
    (hle : h ≤ w.length) (hbl : blank ∉ w)
    (hIn : Tape.SeqView blank (S tIn) (w.take h₀) 0)
    (hF : Tape.SeqView blank (S tF) ((w.drop h₀).take (h - h₀)) 0) :
    ExecG Terminal blank (copyPairProg blank j) S (copyPairActs j h₀ (h - h₀)) := by
  have hblI : blank ∉ w.take h₀ := fun hc => hbl (List.mem_of_mem_take hc)
  have hblF : blank ∉ (w.drop h₀).take (h - h₀) := fun hc =>
    hbl (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  have hlen0 : (w.take h₀).length = h₀ := by simp only [List.length_take]; omega
  have hlenF : ((w.drop h₀).take (h - h₀)).length = h - h₀ := by
    simp only [List.length_take, List.length_drop]; omega
  have e1 : ExecG Terminal blank (copyProgR tIn j blank) S (copyActsR tIn j h₀) :=
    copyProgR_exec (Terminal := Terminal) (i := tIn) (j := j) hjI hblI h₀ 0 S (by omega)
      (by intro h0; omega) (fun _ => hIn)
  have hFmid : Tape.SeqView blank (runG blank (copyActsR tIn j h₀) S tF)
      ((w.drop h₀).take (h - h₀)) 0 := by
    rw [copyActsR_runP, copyLoopR_untouched blank (i := tIn) (j := j) (l := tF)
      (by decide) (Ne.symm hjF)]
    exact hF
  have e2 : ExecG Terminal blank (copyProgR tF j blank)
      (runG blank (copyActsR tIn j h₀) S) (copyActsR tF j (h - h₀)) :=
    copyProgR_exec (Terminal := Terminal) (i := tF) (j := j) hjF hblF (h - h₀) 0 _ (by omega)
      (by intro h0; omega) (fun _ => hFmid)
  exact execG_of_eq rfl (execG_seq e1 e2)

/-- **系**：`copyPairProg` の実行結果、`j` には `w.take h` の最前線ビューが立つ。 -/
theorem copyPairProg_spec {j : Fin 13} (hjI : j ≠ tIn) (hjF : j ≠ tF)
    {S : Tapes13 sc} {w : List (Fin sc)} {h h₀ : ℕ} (hpos : 0 < h₀) (hlt : h₀ < h)
    (hle : h ≤ w.length) (hbl : blank ∉ w)
    (hIn : Tape.SeqView blank (S tIn) (w.take h₀) 0)
    (hF : Tape.SeqView blank (S tF) ((w.drop h₀).take (h - h₀)) 0)
    (hj : Tape.StackView blank (S j) []) :
    ExecG Terminal blank (copyPairProg blank j) S (copyPairActs j h₀ (h - h₀)) ∧
      InputCopy.FrontierView blank
        (runG blank (copyPairActs j h₀ (h - h₀)) S j) (w.take h) ∧
      (copyPairActs (sc := sc) j h₀ (h - h₀)).length ≤ 2 * h + 2 := by
  refine ⟨copyPairProg_exec (Terminal := Terminal) hjI hjF hpos hlt hle hbl hIn hF, ?_, ?_⟩
  · rw [copyPairActs_runP]
    exact (copyPairToSingle_spec blank hjI hjF hpos hlt hle hIn hF hj).1
  · rw [copyPairActs_length]; omega

end CopyPair

#print axioms setupProgPairL_exec
#print axioms setupProgPairL_spec
#print axioms copyPairProg_spec

end PalPeg.PatternPairProg
