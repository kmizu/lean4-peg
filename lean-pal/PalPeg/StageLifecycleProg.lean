import PalPeg.ProgLang
import PalPeg.ProgLangLib
import PalPeg.ProgLangSum
import PalPeg.ProgLangPersist2
import PalPeg.StageTapes
import PalPeg.PatternPairProg
import PalPeg.StageMatcherProg
import PalPeg.MiddleProg
import PalPeg.Metered

/-!
# 段のライフサイクルを 1 本の `Prog` に載せる (`StageLifecycleProg`)

`ASSEMBLY_PLAN.md` §2–§4 の (ii)「直列化＋テープ上の再開点」を実装する。

## なぜ再開点が要るのか

`ProgLangPersist2.progMachinePM` の制御は **1 本の継続スタック** であり、
ラウンド境界でリセットされない（`bodyStepPA_ne`）。したがって
「長いプログラムを毎ラウンド `R` 動作だけ挽く」は、**プログラムが 1 本だけなら**
持ち越しスタックが自動的に与えてくれる（`progMachinePM_grind`）。
しかし段の本体は 4 スロット × 複数フェーズを 1 ラウンドの中で **直列に** 回す必要があり、
`roundBody = seq (slot0 chunk) (seq (slot1 chunk) …)` は
「4 本の独立な長いプログラムの持ち越し継続」にはなり得ない
（`CtrlS` は 1 本のスタックの部分型であり、4 本組にはできない）。

そこで **再開点をテープに置く**。すなわち長いプログラム `P` を、
「プログラムカウンタ（PC）テープの内容から制御状態を復元できる」形に書き直す。

## `Resumable`

`Resumable I blank work R chunkActs` は「`chunk` を 1 回走らせると、
現在のテープ状態から `P` のトレースの次のかたまり `chunkActs m` の効果を
（作業テープ `work` の上で）実現し、PC テープを更新する」ことを表す。

主定理 `Resumable.chunk_iterate` は
「`chunk` を `k` 回反復した効果 ＝ `P` のトレースの先頭 `k` かたまり分の効果」。
固定レート版は `Resumable.chunk_iterate_rate`
（`chunkActs m = (acts.drop (m*R)).take R` のとき先頭 `k*R` 動作）。
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.StageLifecycleProg

open PegSeparation.RealTimeTM
open PalPeg.Program
open PalPeg.ProgLang
open PalPeg.ProgLangPersist

variable {Terminal A C Γ : Type} {t : ℕ}

/-! ## 1. 補助：`applyTrace` は各テープごとに独立 -/

/-- `applyTrace` はテープ `j` については `T j` にしか依存しない。 -/
theorem applyTrace_congr_at (blank : Γ) (j : Fin t) :
    ∀ (l : List (Fin t → Γ × Move)) (T T' : Fin t → STape Γ), T j = T' j →
      applyTrace blank T l j = applyTrace blank T' l j := by
  intro l
  induction l with
  | nil => intro T T' h; simpa using h
  | cons w l ih =>
      intro T T' h
      simp only [applyTrace_cons]
      exact ih _ _ (by simp [h])

/-! ## 2. `Resumable` -/

/-- **再開可能なプログラム**。`chunk` を 1 回走らせると `chunkActs m` 分だけ進む。

* `work` … 「作業テープ」の述語。PC テープなど補助テープは含めない。
* `R` … 1 ラウンドあたりの動作予算。
* `chunkActs` … 長いプログラムのトレースを前から切ったかたまりの列。 -/
structure Resumable (I : Interp Terminal A C Γ t) (blank : Γ) (work : Fin t → Prop)
    (R : ℕ) (chunkActs : ℕ → List (Fin t → Γ × Move)) where
  /-- 毎ラウンド 1 回走らせるプログラム（数値定数なし・`m` に依存しない）。 -/
  chunk : Prog A C
  /-- PC テープの不変条件：「次に実行するのは `m` 個目のかたまり」。 -/
  pcInv : ℕ → (Fin t → STape Γ) → Prop
  /-- `chunk` が実際に出す動作列。 -/
  chunkTrace : ℕ → (Fin t → STape Γ) → List (Fin t → Γ × Move)
  /-- `chunk` はちょうど `chunkTrace m T` を実行して継続に戻る。 -/
  chunk_exec : ∀ m T, pcInv m T → Exec I blank chunk T (chunkTrace m T)
  /-- 1 ラウンドの動作数は予算 `R` 以下。 -/
  chunk_length_le : ∀ m T, pcInv m T → (chunkTrace m T).length ≤ R
  /-- 作業テープの上での効果は `chunkActs m` の効果に一致する。 -/
  chunk_spec : ∀ m T, pcInv m T → ∀ j, work j →
      applyTrace blank T (chunkTrace m T) j = applyTrace blank T (chunkActs m) j
  /-- PC テープは 1 つ進む。 -/
  chunk_pc : ∀ m T, pcInv m T → pcInv (m + 1) (applyTrace blank T (chunkTrace m T))

namespace Resumable

variable {I : Interp Terminal A C Γ t} {blank : Γ} {work : Fin t → Prop} {R : ℕ}
  {chunkActs : ℕ → List (Fin t → Γ × Move)}

/-- `chunk` を（`m` 個目から）`k` 回反復したときのテープ。 -/
def run (Re : Resumable I blank work R chunkActs) :
    ℕ → ℕ → (Fin t → STape Γ) → (Fin t → STape Γ)
  | _, 0, T => T
  | m, k + 1, T => Re.run (m + 1) k (applyTrace blank T (Re.chunkTrace m T))

@[simp] theorem run_zero (Re : Resumable I blank work R chunkActs) (m : ℕ)
    (T : Fin t → STape Γ) : Re.run m 0 T = T := rfl

theorem run_succ (Re : Resumable I blank work R chunkActs) (m k : ℕ)
    (T : Fin t → STape Γ) :
    Re.run m (k + 1) T = Re.run (m + 1) k (applyTrace blank T (Re.chunkTrace m T)) := rfl

/-- `m` 個目から `k` かたまり分の動作列。 -/
def chunkPrefix (chunkActs : ℕ → List (Fin t → Γ × Move)) (m k : ℕ) :
    List (Fin t → Γ × Move) :=
  ((List.range k).map (fun i => chunkActs (m + i))).flatten

@[simp] theorem chunkPrefix_zero (m : ℕ) : chunkPrefix chunkActs m 0 = [] := by
  simp [chunkPrefix]

theorem chunkPrefix_succ (m k : ℕ) :
    chunkPrefix chunkActs m (k + 1) = chunkActs m ++ chunkPrefix chunkActs (m + 1) k := by
  have hfun : ∀ i : ℕ, chunkActs (m + (i + 1)) = chunkActs (m + 1 + i) := by
    intro i; congr 1; omega
  simp only [chunkPrefix, List.range_succ_eq_map, List.map_cons, List.map_map,
    List.flatten_cons, Nat.add_zero, Function.comp_def, hfun]

/-- PC 不変条件は反復で保たれる。 -/
theorem run_pcInv (Re : Resumable I blank work R chunkActs) :
    ∀ (k m : ℕ) (T : Fin t → STape Γ), Re.pcInv m T → Re.pcInv (m + k) (Re.run m k T) := by
  intro k
  induction k with
  | zero => intro m T h; simpa using h
  | succ k ih =>
      intro m T h
      have hstep := ih (m + 1) _ (Re.chunk_pc m T h)
      have e : m + (k + 1) = m + 1 + k := by omega
      rw [run_succ, e]
      exact hstep

/-- **主定理（チャンクの反復）。** `chunk` を `k` 回走らせた効果は、
長いプログラムのトレースの先頭 `k` かたまり分の効果に（作業テープ上で）一致する。 -/
theorem chunk_iterate (Re : Resumable I blank work R chunkActs) :
    ∀ (k m : ℕ) (T : Fin t → STape Γ), Re.pcInv m T → ∀ j, work j →
      Re.run m k T j = applyTrace blank T (chunkPrefix chunkActs m k) j := by
  intro k
  induction k with
  | zero => intro m T _ j _; simp
  | succ k ih =>
      intro m T h j hj
      rw [run_succ, chunkPrefix_succ, applyTrace_append]
      rw [ih (m + 1) _ (Re.chunk_pc m T h) j hj]
      exact applyTrace_congr_at blank j _ _ _ (Re.chunk_spec m T h j hj)

/-- 固定レートの切り方：`chunkActs m = (acts.drop (m*R)).take R`。 -/
theorem chunkPrefix_rate (acts : List (Fin t → Γ × Move)) (R : ℕ)
    (hc : ∀ m, chunkActs m = (acts.drop (m * R)).take R) :
    ∀ (k m : ℕ), chunkPrefix chunkActs m k = (acts.drop (m * R)).take (k * R) := by
  intro k
  induction k with
  | zero => intro m; simp
  | succ k ih =>
      intro m
      rw [chunkPrefix_succ, hc m, ih (m + 1)]
      have hdrop : acts.drop ((m + 1) * R) = (acts.drop (m * R)).drop R := by
        rw [List.drop_drop]
        congr 1
        ring
      rw [hdrop, ← List.take_add]
      congr 1
      ring

/-- **固定レート版の反復定理**：`k` ラウンド後の効果は長いトレースの先頭 `k*R` 動作分。 -/
theorem chunk_iterate_rate (Re : Resumable I blank work R chunkActs)
    (acts : List (Fin t → Γ × Move)) (hc : ∀ m, chunkActs m = (acts.drop (m * R)).take R)
    (k : ℕ) (T : Fin t → STape Γ) (h0 : Re.pcInv 0 T) (j : Fin t) (hj : work j) :
    Re.run 0 k T j = applyTrace blank T (acts.take (k * R)) j := by
  have h := Re.chunk_iterate k 0 T h0 j hj
  rw [chunkPrefix_rate acts R hc k 0] at h
  simpa using h

end Resumable

/-! ## 3. PC テープによるフェーズ分割 (`phaseChunk`) -/

section PhaseChunk

variable {I : Interp Terminal A C Γ t} {blank : Γ}

/-- **フェーズ分割チャンク**。PC テープが指すフェーズ番号 `i` を条件
`pcCond i` で読み、そのフェーズのプログラムを 1 個だけ実行してから
PC を 1 進める動作 `pcAdv` を打つ。番号がどれにも当たらなければ何もしない。 -/
def phaseChunkAux (pcAdv : A) (pcCond : ℕ → C) : ℕ → List (Prog A C) → Prog A C
  | _, [] => Prog.skip
  | i, p :: ps =>
      Prog.ite (pcCond i) (Prog.seq p (Prog.act pcAdv))
        (phaseChunkAux pcAdv pcCond (i + 1) ps)

/-- フェーズ列の先頭から `0` 番で始める版。 -/
def phaseChunk (pcAdv : A) (pcCond : ℕ → C) (ps : List (Prog A C)) : Prog A C :=
  phaseChunkAux pcAdv pcCond 0 ps

/-- どのフェーズ条件も成り立たなければ、チャンクは何もしない。 -/
theorem phaseChunkAux_exec_skip (pcAdv : A) (pcCond : ℕ → C) :
    ∀ (ps : List (Prog A C)) (i : ℕ) (T : Fin t → STape Γ),
      (∀ d, d < ps.length → I.condOf (pcCond (i + d)) (fun j => (T j).focus) = false) →
      Exec I blank (phaseChunkAux pcAdv pcCond i ps) T [] := by
  intro ps
  induction ps with
  | nil => intro i T _; exact exec_skip T
  | cons p ps ih =>
      intro i T h
      have h0 : I.condOf (pcCond i) (fun j => (T j).focus) = false := by
        have := h 0 (by simp)
        simpa using this
      refine exec_ite_neg h0 (ih (i + 1) T ?_)
      intro d hd
      have := h (d + 1) (by simpa using Nat.succ_lt_succ hd)
      have e : i + (d + 1) = i + 1 + d := by omega
      rwa [e] at this

/-- **チャンクの実行**：PC が `m` を指し、`m` 番目のフェーズが `acts` を実行するなら、
チャンクはちょうど `acts` ＋ PC 前進動作 1 個を実行する。 -/
theorem phaseChunkAux_exec (hI : InputFree I) (pcAdv : A) (pcCond : ℕ → C) :
    ∀ (ps : List (Prog A C)) (i m : ℕ) (T : Fin t → STape Γ)
      (acts : List (Fin t → Γ × Move)) (pm : Prog A C),
      i ≤ m →
      (∀ d, i + d < m → d < ps.length →
        I.condOf (pcCond (i + d)) (fun j => (T j).focus) = false) →
      I.condOf (pcCond m) (fun j => (T j).focus) = true →
      ps[m - i]? = some pm →
      Exec I blank pm T acts →
      Exec I blank (phaseChunkAux pcAdv pcCond i ps) T
        (acts ++ [actVec I pcAdv (applyTrace blank T acts)]) := by
  intro ps
  induction ps with
  | nil => intro i m T acts pm _ _ _ hget _; simp at hget
  | cons p ps ih =>
      intro i m T acts pm hle hlt htrue hget hexec
      rcases Nat.eq_or_lt_of_le hle with rfl | hi
      · have hp : pm = p := by
          simp only [Nat.sub_self] at hget
          simpa using hget.symm
        subst hp
        refine exec_ite_pos htrue ?_
        exact exec_seq hexec (exec_act hI pcAdv _)
      · have h0 : I.condOf (pcCond i) (fun j => (T j).focus) = false := by
          have := hlt 0 (by omega) (by simp)
          simpa using this
        refine exec_ite_neg h0 ?_
        have hsub : m - i = (m - (i + 1)) + 1 := by omega
        have hget' : ps[m - (i + 1)]? = some pm := by
          rw [hsub] at hget
          simpa using hget
        refine ih (i + 1) m T acts pm (by omega) ?_ htrue hget' hexec
        intro d hd hdlt
        have e : i + 1 + d = i + (d + 1) := by omega
        rw [e]
        exact hlt (d + 1) (by omega) (by simpa using Nat.succ_lt_succ hdlt)

/-- **フェーズ分割による `Resumable` の構成データ**。
各フェーズの `Exec` は仮定として受け取る（具体プログラムの差し込み口）。 -/
structure PhaseData (I : Interp Terminal A C Γ t) (blank : Γ) (work : Fin t → Prop)
    (R : ℕ) (ps : List (Prog A C)) (phaseActs : ℕ → List (Fin t → Γ × Move))
    (pcAdv : A) (pcCond : ℕ → C) where
  /-- 動作の解釈は入力記号を見ない。 -/
  inputFree : InputFree I
  /-- PC テープの不変条件：「次に実行するのはフェーズ `m`」。 -/
  pcInv : ℕ → (Fin t → STape Γ) → Prop
  /-- PC が `m` を指すとき、`m` より小さいフェーズ条件はすべて偽。 -/
  cond_lt : ∀ m T, pcInv m T → ∀ d, d < m → d < ps.length →
      I.condOf (pcCond d) (fun j => (T j).focus) = false
  /-- PC が `m` を指すとき、フェーズ `m` の条件は真。 -/
  cond_eq : ∀ m T, pcInv m T → m < ps.length →
      I.condOf (pcCond m) (fun j => (T j).focus) = true
  /-- フェーズ `m` のプログラムはちょうど `phaseActs m` を実行する。 -/
  phase_exec : ∀ m T (h : m < ps.length), pcInv m T →
      Exec I blank ps[m] T (phaseActs m)
  /-- フェーズを使い切ったあとの動作列は空。 -/
  acts_done : ∀ m, ps.length ≤ m → phaseActs m = []
  /-- PC 前進動作は作業テープに触らない。 -/
  adv_work : ∀ (T' : Fin t → STape Γ) j, work j →
      actVec I pcAdv T' j = ((T' j).focus, Move.stay)
  /-- フェーズを 1 個実行すると PC は 1 進む。 -/
  pc_step : ∀ m T, m < ps.length → pcInv m T →
      pcInv (m + 1) (applyTrace blank T
        (phaseActs m ++ [actVec I pcAdv (applyTrace blank T (phaseActs m))]))
  /-- 使い切ったあとは PC の意味だけが進む（テープは不変）。 -/
  pc_stay : ∀ m T, pcInv m T → ps.length ≤ m → pcInv (m + 1) T
  /-- 1 フェーズ ＋ PC 前進は予算 `R` に収まる。 -/
  len_le : ∀ m, (phaseActs m).length + 1 ≤ R

/-- **`PhaseData` から `Resumable` を作る。** -/
def PhaseData.toResumable {work : Fin t → Prop} {R : ℕ} {ps : List (Prog A C)}
    {phaseActs : ℕ → List (Fin t → Γ × Move)} {pcAdv : A} {pcCond : ℕ → C}
    (PD : PhaseData I blank work R ps phaseActs pcAdv pcCond) :
    Resumable I blank work R phaseActs where
  chunk := phaseChunk pcAdv pcCond ps
  pcInv := PD.pcInv
  chunkTrace := fun m T =>
    if m < ps.length then
      phaseActs m ++ [actVec I pcAdv (applyTrace blank T (phaseActs m))]
    else []
  chunk_exec := by
    intro m T h
    by_cases hm : m < ps.length
    · rw [if_pos hm]
      refine phaseChunkAux_exec PD.inputFree pcAdv pcCond ps 0 m T (phaseActs m) ps[m]
        (Nat.zero_le _) ?_ (PD.cond_eq m T h hm) ?_ (PD.phase_exec m T hm h)
      · intro d hd hdlt
        have := PD.cond_lt m T h d (by omega) hdlt
        simpa using this
      · simp [List.getElem?_eq_getElem hm]
    · rw [if_neg hm]
      refine phaseChunkAux_exec_skip pcAdv pcCond ps 0 T ?_
      intro d hd
      have := PD.cond_lt m T h d (by omega) hd
      simpa using this
  chunk_length_le := by
    intro m T _
    by_cases hm : m < ps.length
    · rw [if_pos hm]
      simpa using PD.len_le m
    · rw [if_neg hm]; simp
  chunk_spec := by
    intro m T h j hj
    by_cases hm : m < ps.length
    · rw [if_pos hm, applyTrace_append]
      show (applyTrace blank T (phaseActs m) j).applyAction blank
          (actVec I pcAdv (applyTrace blank T (phaseActs m)) j) = _
      rw [PD.adv_work _ j hj]
      exact applyAction_stay_self blank _
    · rw [if_neg hm, PD.acts_done m (by omega)]
  chunk_pc := by
    intro m T h
    by_cases hm : m < ps.length
    · rw [if_pos hm]; exact PD.pc_step m T hm h
    · rw [if_neg hm, applyTrace_nil]; exact PD.pc_stay m T h (by omega)

end PhaseChunk

/-! ## 4. 準備フェーズ `PatternPairProg.setupProgPairL` の具体化

`setupProgPairL` は 9 個の「番兵／カウンタ駆動ループ」の逐次合成であり、
その動作列 `setupProgPairLActs` はちょうど 9 個の区間の連結である。
したがって PC テープにユナリのフェーズ添字 `0..8` を置けば、
各チャンクは「ヘッドを読み直してループを再開する」だけでよい
（ループはもともとヘッドの読みだけで駆動されているので、追加の再開点は要らない）。 -/

section Setup

variable {sc : ℕ}

open PalPeg.PatternProg PalPeg.PatternTapesPair PalPeg.PatternPairProg

/-- `setupProgPairL` の 9 個のフェーズ。 -/
def setupPhaseProg (bl startSym endSym mark leftSym : Fin sc) (k : ℕ) :
    ℕ → Prog (ActG 13 sc) (CondG 13 sc)
  | 0 => prologueProgP bl startSym
  | 1 => pairLoopProg bl mark leftSym
  | 2 => xfer1Prog13 bl mark tC2 tCs
  | 3 => Prog.loop (tF, leftSym) (TAct.copy tP tF (sc := sc) .right).act
            (PatternProg.ACT (TAct.keep tF .left))
  | 4 => Prog.loop (tIn, leftSym) (TAct.copy tP tIn (sc := sc) .right).act
            (PatternProg.ACT (TAct.keep tIn .left))
  | 5 => pushBothProgP endSym
  | 6 => settleProgG tU bl startSym
  | 7 => settleProgG tP bl startSym
  | 8 => kLoopProg13 bl mark k
  | _ => Prog.skip

/-- `setupProgPairL` と同じ入れ子でフェーズを組み直す。 -/
def setupSeqTree (P : ℕ → Prog (ActG 13 sc) (CondG 13 sc)) : Prog (ActG 13 sc) (CondG 13 sc) :=
  Prog.seq (P 0)
    (Prog.seq (Prog.seq (P 1) (P 2))
      (Prog.seq (P 3)
        (Prog.seq (P 4) (Prog.seq (P 5) (Prog.seq (P 6) (Prog.seq (P 7) (P 8)))))))

/-- **フェーズ分解（プログラム側）**：`setupProgPairL` は 9 個のフェーズの合成そのもの。 -/
theorem setupProgPairL_phases (bl startSym endSym mark leftSym : Fin sc) (k : ℕ) :
    setupProgPairL bl startSym endSym mark leftSym k
      = setupSeqTree (setupPhaseProg bl startSym endSym mark leftSym k) := rfl

/-- フェーズのリスト（`PhaseData` に渡す形）。 -/
def setupPhaseProgList (bl startSym endSym mark leftSym : Fin sc) (k : ℕ) :
    List (Prog (ActG 13 sc) (CondG 13 sc)) :=
  (List.range 9).map (setupPhaseProg bl startSym endSym mark leftSym k)

@[simp] theorem setupPhaseProgList_length (bl startSym endSym mark leftSym : Fin sc) (k : ℕ) :
    (setupPhaseProgList bl startSym endSym mark leftSym k).length = 9 := by
  simp [setupPhaseProgList]

theorem setupPhaseProgList_getElem (bl startSym endSym mark leftSym : Fin sc) (k m : ℕ)
    (hm : m < (setupPhaseProgList bl startSym endSym mark leftSym k).length) :
    (setupPhaseProgList bl startSym endSym mark leftSym k)[m]
      = setupPhaseProg bl startSym endSym mark leftSym k m := by
  simp only [setupPhaseProgList, List.getElem_map, List.getElem_range]

/-- `setupProgPairLActs` の 9 個の区間。 -/
def setupPhaseActs (bl startSym endSym : Fin sc) (s h h₀ k p₁ : ℕ) : ℕ → List (TAct 13 sc)
  | 0 => prologueActsP bl startSym
  | 1 => pairLoopActs bl h₀ h s
  | 2 => xfer1Acts13 bl tC2 tCs s
  | 3 => copyActsN tF tP (h - s - h₀)
  | 4 => copyActsN tIn tP (min (h - s) h₀)
  | 5 => pushBothActsP endSym
  | 6 => TAct.put tU bl .left :: (leftWalkG tU (s + 1) ++ [TAct.keep tU .right])
  | 7 => TAct.put tP bl .left :: (leftWalkG tP (h - s + 1) ++ [TAct.keep tP .right])
  | 8 => kLoopActs13 bl p₁ k
  | _ => []

/-- **フェーズ分解（動作列側）**：`setupProgPairLActs` は 9 個の区間の連結。 -/
theorem setupProgPairLActs_flatten (bl startSym endSym : Fin sc) (s h h₀ k p₁ : ℕ) :
    setupProgPairLActs bl startSym endSym s h h₀ k p₁
      = ((List.range 9).map (setupPhaseActs bl startSym endSym s h h₀ k p₁)).flatten := by
  simp [setupProgPairLActs, setupPhaseActs, List.range_succ]

end Setup

/-! ### `Resumable` への流し込み

`vecOf` は「13 本テープの動作列を大域テープ束の動作ベクトル列に写す」関数
（`PatternProg.gavecs` ＋ `ProgLangSum.Interp.transport` の合成）。
連結を保つことだけを仮定する。 -/

section SetupResumable

variable {sc : ℕ}

open PalPeg.PatternProg PalPeg.PatternPairProg

/-- 連結を保つ写像は連結列（`flatten`）も保つ。 -/
theorem vecOf_flatten {Γ' : Type} {t' : ℕ}
    (vecOf : List (PatternProg.TAct 13 sc) → List (Fin t' → Γ' × Move))
    (hnil : vecOf [] = [])
    (happ : ∀ l₁ l₂, vecOf (l₁ ++ l₂) = vecOf l₁ ++ vecOf l₂) :
    ∀ ls : List (List (PatternProg.TAct 13 sc)),
      vecOf ls.flatten = (ls.map vecOf).flatten := by
  intro ls
  induction ls with
  | nil => simpa using hnil
  | cons l ls ih => simp [happ, ih]

/-- **`setupProgPairL` のチャンク化定理**：PC テープでフェーズを刻んだチャンクを
9 回反復すると、作業テープの上では `setupProgPairL` を一気に走らせたのと同じ効果になる。
途中（`k ≤ 9` 回）は `Resumable.chunk_iterate` により先頭 `k` 区間分の効果に一致する。 -/
theorem setupChunk_iterate {Terminal A C Γ : Type} {t : ℕ}
    {I : Interp Terminal A C Γ t} {blank : Γ} {work : Fin t → Prop} {R : ℕ}
    {ps : List (Prog A C)} {pcAdv : A} {pcCond : ℕ → C}
    (vecOf : List (PatternProg.TAct 13 sc) → List (Fin t → Γ × Move))
    (hnil : vecOf [] = [])
    (happ : ∀ l₁ l₂, vecOf (l₁ ++ l₂) = vecOf l₁ ++ vecOf l₂)
    (bl startSym endSym : Fin sc) (s h h₀ k p₁ : ℕ)
    (PD : PhaseData I blank work R ps
      (fun m => vecOf (setupPhaseActs bl startSym endSym s h h₀ k p₁ m)) pcAdv pcCond)
    (T : Fin t → STape Γ) (h0 : PD.pcInv 0 T) (j : Fin t) (hj : work j) :
    PD.toResumable.run 0 9 T j
      = applyTrace blank T (vecOf (setupProgPairLActs bl startSym endSym s h h₀ k p₁)) j := by
  have hiter := PD.toResumable.chunk_iterate 9 0 T h0 j hj
  rw [hiter]
  congr 1
  rw [setupProgPairLActs_flatten bl startSym endSym s h h₀ k p₁,
    vecOf_flatten vecOf hnil happ]
  simp [Resumable.chunkPrefix, Function.comp_def]

end SetupResumable

/-! ## 5. 段 1 スロットのラウンド本体 `stageRoundProg`

`StageTapes.stround` の 5 分岐（`n ≤ S/2` / `≤ 3(S/4)` / `≤ S` / `≤ S+|u|` / それ以降）に
1 対 1 対応する分岐プログラム。各枝のプログラムは
「前処理の挽き（`Resumable` の `chunk`、たとえば `decProgP`）」
「セットアップの挽き（`§4` の `setupProgPairL` のチャンク）」
「照合器 1 ラウンド（`StageMatcherProg`）」「中央ジョブのバッチ（`MiddleProg`）」
であり、本節では **パラメータ＋実行仮定** として受け取る。 -/

section StageRound

variable {Terminal A C Γ : Type} {tt : ℕ}

/-- **段 1 スロットのラウンド本体**。分岐条件はテープ上のユナリカウンタの比較
（`ASSEMBLY_PLAN.md` §2.4）で与えられる。 -/
def stageRoundProg (cIdle cPrep cSetup cStart : C)
    (pIdle pPrep pSetup pStart pMatch : Prog A C) : Prog A C :=
  Prog.ite cIdle pIdle
    (Prog.ite cPrep pPrep
      (Prog.ite cSetup pSetup
        (Prog.ite cStart pStart pMatch)))

open PalPeg.StageTapes PalPeg.MiddleTapes

/-- **`stageRoundProg` の 1 ラウンドの効果は `stround` のそれに一致する。**

各枝について「その枝のプログラムが予算 `Bs` 以内の動作列を実行し、
その効果が `stround` のその枝の結果の符号化になる」ことを仮定すると、
分岐プログラム全体についても同じことが成り立つ。 -/
theorem stageRoundProg_effect {sc : ℕ} {bl startSym endSym mark forb leftSym : Fin sc}
    (D : DecompOnTapes sc bl startSym endSym mark leftSym)
    (Pre : PrepOnTapes sc bl mark forb)
    (one zero : Fin sc) (u v Text : List (Fin sc))
    (kk pe re : ℕ) (cst : PalPeg.ScanState → ℕ) (AA BB S : ℕ)
    (inp : List (Fin sc)) (a : Fin sc) (n : ℕ) (St : StageT sc)
    {I : Interp Terminal A C Γ tt} {blank : Γ} {Bs : ℕ}
    (enc : ℕ → StageT sc → (Fin tt → STape Γ))
    (cIdle cPrep cSetup cStart : C) (pIdle pPrep pSetup pStart pMatch : Prog A C)
    (T : Fin tt → STape Γ)
    (hcI : I.condOf cIdle (fun j => (T j).focus) = decide (n ≤ S / 2))
    (hcP : I.condOf cPrep (fun j => (T j).focus) = decide (n ≤ 3 * (S / 4)))
    (hcS : I.condOf cSetup (fun j => (T j).focus) = decide (n ≤ S))
    (hcX : I.condOf cStart (fun j => (T j).focus) = decide (n ≤ S + u.length))
    (hIdle : n ≤ S / 2 → ∃ acts, Exec I blank pIdle T acts ∧ acts.length ≤ Bs ∧
      applyTrace blank T acts
        = enc (n + 1) (stround D Pre one zero u v Text kk pe re cst AA BB S inp a n St))
    (hPrep : ¬ n ≤ S / 2 → n ≤ 3 * (S / 4) →
      ∃ acts, Exec I blank pPrep T acts ∧ acts.length ≤ Bs ∧
      applyTrace blank T acts
        = enc (n + 1) (stround D Pre one zero u v Text kk pe re cst AA BB S inp a n St))
    (hSetup : ¬ n ≤ 3 * (S / 4) → n ≤ S →
      ∃ acts, Exec I blank pSetup T acts ∧ acts.length ≤ Bs ∧
      applyTrace blank T acts
        = enc (n + 1) (stround D Pre one zero u v Text kk pe re cst AA BB S inp a n St))
    (hStart : ¬ n ≤ S → n ≤ S + u.length →
      ∃ acts, Exec I blank pStart T acts ∧ acts.length ≤ Bs ∧
      applyTrace blank T acts
        = enc (n + 1) (stround D Pre one zero u v Text kk pe re cst AA BB S inp a n St))
    (hMatch : ¬ n ≤ S + u.length →
      ∃ acts, Exec I blank pMatch T acts ∧ acts.length ≤ Bs ∧
      applyTrace blank T acts
        = enc (n + 1) (stround D Pre one zero u v Text kk pe re cst AA BB S inp a n St)) :
    ∃ acts,
      Exec I blank (stageRoundProg cIdle cPrep cSetup cStart pIdle pPrep pSetup pStart pMatch)
        T acts ∧ acts.length ≤ Bs ∧
      applyTrace blank T acts
        = enc (n + 1)
            (stround D Pre one zero u v Text kk pe re cst AA BB S inp a n St) := by
  unfold stageRoundProg
  by_cases h1 : n ≤ S / 2
  · obtain ⟨acts, hE, hlen, heff⟩ := hIdle h1
    exact ⟨acts, exec_ite_pos (by rw [hcI]; simp [h1]) hE, hlen, heff⟩
  · have hn1 : I.condOf cIdle (fun j => (T j).focus) = false := by rw [hcI]; simp [h1]
    by_cases h2 : n ≤ 3 * (S / 4)
    · obtain ⟨acts, hE, hlen, heff⟩ := hPrep h1 h2
      exact ⟨acts, exec_ite_neg hn1 (exec_ite_pos (by rw [hcP]; simp [h2]) hE), hlen, heff⟩
    · have hn2 : I.condOf cPrep (fun j => (T j).focus) = false := by rw [hcP]; simp [h2]
      by_cases h3 : n ≤ S
      · obtain ⟨acts, hE, hlen, heff⟩ := hSetup h2 h3
        exact ⟨acts,
          exec_ite_neg hn1 (exec_ite_neg hn2 (exec_ite_pos (by rw [hcS]; simp [h3]) hE)),
          hlen, heff⟩
      · have hn3 : I.condOf cSetup (fun j => (T j).focus) = false := by rw [hcS]; simp [h3]
        by_cases h4 : n ≤ S + u.length
        · obtain ⟨acts, hE, hlen, heff⟩ := hStart h3 h4
          exact ⟨acts,
            exec_ite_neg hn1 (exec_ite_neg hn2 (exec_ite_neg hn3
              (exec_ite_pos (by rw [hcX]; simp [h4]) hE))), hlen, heff⟩
        · have hn4 : I.condOf cStart (fun j => (T j).focus) = false := by rw [hcX]; simp [h4]
          obtain ⟨acts, hE, hlen, heff⟩ := hMatch h4
          exact ⟨acts,
            exec_ite_neg hn1 (exec_ite_neg hn2 (exec_ite_neg hn3 (exec_ite_neg hn4 hE))),
            hlen, heff⟩

end StageRound

end PalPeg.StageLifecycleProg


/-
公理チェック（0 エラー・警告なし・`sorry` なし。
`propext / Classical.choice / Quot.sound` のみに依存）:

```
#print axioms PalPeg.StageLifecycleProg.Resumable.chunk_iterate
#print axioms PalPeg.StageLifecycleProg.Resumable.chunk_iterate_rate
#print axioms PalPeg.StageLifecycleProg.Resumable.run_pcInv
#print axioms PalPeg.StageLifecycleProg.phaseChunkAux_exec
#print axioms PalPeg.StageLifecycleProg.phaseChunkAux_exec_skip
#print axioms PalPeg.StageLifecycleProg.PhaseData.toResumable
#print axioms PalPeg.StageLifecycleProg.setupProgPairL_phases
#print axioms PalPeg.StageLifecycleProg.setupProgPairLActs_flatten
#print axioms PalPeg.StageLifecycleProg.setupPhaseProgList_getElem
#print axioms PalPeg.StageLifecycleProg.setupChunk_iterate
#print axioms PalPeg.StageLifecycleProg.stageRoundProg_effect
```
-/
