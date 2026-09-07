import PalPeg.PrepInstances
import PalPeg.GSPreprocessTapes
import PalPeg.StageTapes
import PalPeg.PatternTapesPair
import PalPeg.ClearAny

/-!
# `PrepOnTapes` の具体化に向けた埋め込み (`PrepInstance`)

`GSPre.decompose2_on_tapes`（`GSPreprocessTapes.lean`）が与える 9 本テープの分解器を、
`PatternTapes.Tapes sc`（12 本テープ）の中に埋め込み、最終的に
`StageTapes.PrepOnTapes sc blank mark` を組み立てることを目標にする。

## 割り付け

`GSPre.Tapes sc` の 9 本を、`PatternTapes.Tapes sc` の 12 本のうち
`SetupPre` が **前処理の仕事**として空けている 9 本へ写す：

| `GSPre` | `PatternTapes` | 役割 |
|---|---|---|
| `V1` | `sP` | パターンの作業コピー 1（終了後スタック `[]` に掃除） |
| `V2` | `sU` | パターンの作業コピー 2（終了後スタック `[]` に掃除） |
| `Cd` | `sC2` | 内側ループの残余予算（終了後カウンタ `0` に掃除） |
| `Cq` | `sAp` | 一致長（終了後カウンタ `0` に掃除） |
| `Ce` | `sAn` | シフト幅の作業（終了後カウンタ `0` に掃除） |
| `Cf` | `sRn` | `first` の作業（終了後カウンタ `0` に掃除、`Enc` の終値も `0`） |
| `Cp` | `sC1` | 候補周期 → 最終的に `p₁`（`SetupPre.c1` が要求する値そのもの） |
| `Cs` | `sCs` | 切断位置 → 最終的に `s`（`SetupPre.cs` が要求する値そのもの） |
| `Cr` | `sRp` | 到達域 → 最終的に `r`（`SetupPre.rp` が要求する値そのもの） |

残る 3 本 `sT`, `sX2`, `sIn` は分解器が触らない（テキスト 2 本とパターン原本の
入力コピー）。

## 本ファイルで完結して証明できるもの

1. `liftAct` / `prj` — 上表の埋め込みと、その逆に 9 本を読み出す射影。
2. `prj_run` — **模倣補題**：`prj` を通せば `PatternTapes.run` による
   `liftAct` 込みの実行が、`GSPre.applyActs` による素の実行と一致する。
3. `run_liftActs_other` — 割り付け先 9 本以外（`sT`/`sX2`/`sIn`、および `sAp` 等の
   互いの区別）を `liftAct` 実行が動かさないこと。
4. `width_applyActs_le` — `ClearAny.width_step` を `GSPre.Act` 側へ移した、
   分解器プログラム実行によるテープ幅の増分見積り。これは掃除フェーズの
   コスト見積り（`3 * width + 3` 系）を `decProg` の長さで抑えるための道具。
5. **`prologueProg` / `prologue_spec`**（`sorry` なし）：`StageTapes.PrepPre` から
   `x := PrepInstances.stagePat w L = (w.take L).reverse` を `sP`/`sU` 上に
   `GSPre.pword startSym endSym x`（ヘッド添字 `1`）の形で書き込み、`prj` 越しに
   `GSPre.Enc … x 0 0 ⟨0,…,0⟩` を成立させる。`sT`/`sX2` は不変、`sIn` は
   `SeqView blank _ w (L - 1)` に復元される。長さはちょうど `6 * L + 5`
   （`prologueProg_length`）。副産物として `rightWalk`（`leftWalk` の右版）と
   `copyLoop2`（`copyLoop` の 2 目的地版）を用意した。

## 未完成（`sorry` なし、単に未着手）

* **epilogue**：`decompose2_on_tapes` が返す終状態から、`sP`/`sU` を
  `ClearAny.clearAny` でスタック `[]` に、`sC2/sAp/sAn/sRn` を `ClearAny.clearAny`
  ＋ `mark` 書き戻し 1 手で `CounterView' _ _ 0` に戻し、`SetupPre` を満たす配置を作る。
* **`prepInstance` 本体**と `len_le`（`PrepInstances.prep_prog_len_le` 系の線形上界、
  `prologueProg_length` の `6 * L + 5`、epilogue の `O(L)` 上界を合算するだけで
  閉じるはずだが、epilogue が埋まっていないため未接続）。
-/

namespace PalPeg
namespace PrepInstance

open PegSeparation.RealTimeTM
open PalPeg.PatternTapes

variable {sc : ℕ}

/-! ## 1. 割り付け -/

/-- `GSPre.Act.V1` の書き戻し先。 -/
def sV1 : Fin 12 := sP

/-- `GSPre.Act.V2` の書き戻し先。 -/
def sV2 : Fin 12 := sU

/-- `GSPre.Act.Cd` の書き戻し先。 -/
def sCd : Fin 12 := sC2

/-- `GSPre.Act.Cq` の書き戻し先。 -/
def sCq : Fin 12 := sAp

/-- `GSPre.Act.Ce` の書き戻し先。 -/
def sCe : Fin 12 := sAn

/-- `GSPre.Act.Cf` の書き戻し先。 -/
def sCf : Fin 12 := sRn

/-- 9 本の割り付け先はすべて相異なる。 -/
theorem slots_pairwise :
    List.Pairwise (· ≠ ·)
      ([sV1, sV2, sCd, sCq, sCe, sC1, sCf, sCs, sRp] : List (Fin 12)) := by
  unfold sV1 sV2 sCd sCq sCe sCf
  unfold sP sC1 sC2 sAp sAn sRp sRn sU sCs
  decide

/-- `GSPre.Act` の 1 動作を、割り付け先の `PatternTapes.SAct` へ写す。
`V1`/`V2` は「読んだ記号を書き戻す」動作なので `SAct.keep`、カウンタ 7 本は
`SAct.put` にそのまま対応する。 -/
def liftAct : GSPre.Act sc → SAct sc
  | .V1 m => .keep sV1 m
  | .V2 m => .keep sV2 m
  | .Cd a m => .put sCd a m
  | .Cq a m => .put sCq a m
  | .Ce a m => .put sCe a m
  | .Cp a m => .put sC1 a m
  | .Cf a m => .put sCf a m
  | .Cs a m => .put sCs a m
  | .Cr a m => .put sRp a m

/-- 動作が触る `PatternTapes` 側のスロット。 -/
theorem sTape_liftAct (a : GSPre.Act sc) :
    sTape (liftAct a) =
      match a with
      | .V1 _ => sV1
      | .V2 _ => sV2
      | .Cd _ _ => sCd
      | .Cq _ _ => sCq
      | .Ce _ _ => sCe
      | .Cp _ _ => sC1
      | .Cf _ _ => sCf
      | .Cs _ _ => sCs
      | .Cr _ _ => sRp := by
  cases a <;> rfl

/-- `PatternTapes.Tapes` から `GSPre.Tapes` への射影（割り付け先 9 本を読み出す）。 -/
def prj (S : Tapes sc) : GSPre.Tapes sc :=
  { V1 := S sV1, V2 := S sV2, Cd := S sCd, Cq := S sCq, Ce := S sCe
    Cp := S sC1, Cf := S sCf, Cs := S sCs, Cr := S sRp }

/-! ## 2. 模倣補題 -/

/-- 1 動作の模倣：`liftAct a` を 12 本テープ側で実行してから射影するのは、
`a` を 9 本テープ側で実行してから同じ射影を取るのと一致する。 -/
theorem prj_applyAct (blank : Fin sc) (a : GSPre.Act sc) (S : Tapes sc) :
    prj (applyS blank S (liftAct a)) = GSPre.applyAct blank (prj S) a := by
  cases a <;>
    simp [liftAct, prj, applyS, GSPre.applyAct, updT,
      sV1, sV2, sCd, sCq, sCe, sCf,
      sP, sC1, sC2, sAp, sAn, sRp, sRn, sU, sCs]

/-- **模倣補題**：`liftAct` で写した動作列を 12 本テープ側で実行してから射影するのは、
元の動作列を 9 本テープ側でそのまま実行してから射影するのと一致する。 -/
theorem prj_run (blank : Fin sc) (l : List (GSPre.Act sc)) (S : Tapes sc) :
    prj (run blank (l.map liftAct) S) = GSPre.applyActs blank l (prj S) := by
  induction l generalizing S with
  | nil => rfl
  | cons a l ih =>
      simp only [List.map_cons, run_cons, GSPre.applyActs_cons]
      rw [ih (applyS blank S (liftAct a)), prj_applyAct]

/-- 割り付け先以外のスロットは `liftAct` で写した実行によって変化しない。
特に `sT`, `sX2`, `sIn`（前処理が読み書きしないテキスト・入力コピー）を含む。 -/
theorem run_liftActs_other (blank : Fin sc) (l : List (GSPre.Act sc)) (S : Tapes sc)
    (j : Fin 12) (hj : j ≠ sV1) (hj2 : j ≠ sV2) (hj3 : j ≠ sCd) (hj4 : j ≠ sCq)
    (hj5 : j ≠ sCe) (hj6 : j ≠ sC1) (hj7 : j ≠ sCf) (hj8 : j ≠ sCs) (hj9 : j ≠ sRp) :
    run blank (l.map liftAct) S j = S j := by
  induction l generalizing S with
  | nil => rfl
  | cons a l ih =>
      simp only [List.map_cons, run_cons]
      rw [ih]
      cases a <;>
        simp [liftAct, applyS, updT, hj, hj2, hj3, hj4, hj5, hj6, hj7, hj8, hj9]

/-! ## 3. テープ幅の見積り（`ClearAny` を `GSPre.Act` 側へ移す） -/

open PalPeg.Tape in
/-- 1 動作での `GSPre.Tapes` の 1 成分の幅の増分は高々 `1`
（触らない成分は不変、触る成分は `ClearAny.width_step`）。ここでは
`Cd` 成分について例示し、他の成分も同型に成り立つ（`liftAct`/`applyAct` の
定義がすべての成分について同じ形をしているため）。 -/
theorem width_Cd_applyAct_le (blank : Fin sc) (a : GSPre.Act sc) (ts : GSPre.Tapes sc) :
    ClearAny.width (GSPre.applyAct blank ts a).Cd ≤ ClearAny.width ts.Cd + 1 := by
  cases a with
  | Cd b m => exact ClearAny.width_step blank ts.Cd b m
  | _ => simp [GSPre.applyAct]

/-- `n` 個の動作を経ても `Cd` 成分の幅は高々 `n` しか増えない。 -/
theorem width_Cd_applyActs_le (blank : Fin sc) (l : List (GSPre.Act sc)) (ts : GSPre.Tapes sc) :
    ClearAny.width (GSPre.applyActs blank l ts).Cd ≤ ClearAny.width ts.Cd + l.length := by
  induction l generalizing ts with
  | nil => simp [GSPre.applyActs]
  | cons a l ih =>
      have h1 := width_Cd_applyAct_le blank a ts
      have h2 := ih (GSPre.applyAct blank ts a)
      simp only [GSPre.applyActs_cons, List.length_cons] at *
      omega


/-- 残り 8 成分についても同様（`liftAct`/`applyAct` の定義が全成分で同じ形をしているため）。 -/

theorem width_Cq_applyAct_le (blank : Fin sc) (a : GSPre.Act sc) (ts : GSPre.Tapes sc) :
    ClearAny.width (GSPre.applyAct blank ts a).Cq ≤ ClearAny.width ts.Cq + 1 := by
  cases a with
  | Cq b m => exact ClearAny.width_step blank ts.Cq b m
  | _ => simp [GSPre.applyAct]

theorem width_Cq_applyActs_le (blank : Fin sc) (l : List (GSPre.Act sc)) (ts : GSPre.Tapes sc) :
    ClearAny.width (GSPre.applyActs blank l ts).Cq ≤ ClearAny.width ts.Cq + l.length := by
  induction l generalizing ts with
  | nil => simp [GSPre.applyActs]
  | cons a l ih =>
      have h1 := width_Cq_applyAct_le blank a ts
      have h2 := ih (GSPre.applyAct blank ts a)
      simp only [GSPre.applyActs_cons, List.length_cons] at *
      omega


theorem width_Ce_applyAct_le (blank : Fin sc) (a : GSPre.Act sc) (ts : GSPre.Tapes sc) :
    ClearAny.width (GSPre.applyAct blank ts a).Ce ≤ ClearAny.width ts.Ce + 1 := by
  cases a with
  | Ce b m => exact ClearAny.width_step blank ts.Ce b m
  | _ => simp [GSPre.applyAct]

theorem width_Ce_applyActs_le (blank : Fin sc) (l : List (GSPre.Act sc)) (ts : GSPre.Tapes sc) :
    ClearAny.width (GSPre.applyActs blank l ts).Ce ≤ ClearAny.width ts.Ce + l.length := by
  induction l generalizing ts with
  | nil => simp [GSPre.applyActs]
  | cons a l ih =>
      have h1 := width_Ce_applyAct_le blank a ts
      have h2 := ih (GSPre.applyAct blank ts a)
      simp only [GSPre.applyActs_cons, List.length_cons] at *
      omega


theorem width_Cp_applyAct_le (blank : Fin sc) (a : GSPre.Act sc) (ts : GSPre.Tapes sc) :
    ClearAny.width (GSPre.applyAct blank ts a).Cp ≤ ClearAny.width ts.Cp + 1 := by
  cases a with
  | Cp b m => exact ClearAny.width_step blank ts.Cp b m
  | _ => simp [GSPre.applyAct]

theorem width_Cp_applyActs_le (blank : Fin sc) (l : List (GSPre.Act sc)) (ts : GSPre.Tapes sc) :
    ClearAny.width (GSPre.applyActs blank l ts).Cp ≤ ClearAny.width ts.Cp + l.length := by
  induction l generalizing ts with
  | nil => simp [GSPre.applyActs]
  | cons a l ih =>
      have h1 := width_Cp_applyAct_le blank a ts
      have h2 := ih (GSPre.applyAct blank ts a)
      simp only [GSPre.applyActs_cons, List.length_cons] at *
      omega


theorem width_Cf_applyAct_le (blank : Fin sc) (a : GSPre.Act sc) (ts : GSPre.Tapes sc) :
    ClearAny.width (GSPre.applyAct blank ts a).Cf ≤ ClearAny.width ts.Cf + 1 := by
  cases a with
  | Cf b m => exact ClearAny.width_step blank ts.Cf b m
  | _ => simp [GSPre.applyAct]

theorem width_Cf_applyActs_le (blank : Fin sc) (l : List (GSPre.Act sc)) (ts : GSPre.Tapes sc) :
    ClearAny.width (GSPre.applyActs blank l ts).Cf ≤ ClearAny.width ts.Cf + l.length := by
  induction l generalizing ts with
  | nil => simp [GSPre.applyActs]
  | cons a l ih =>
      have h1 := width_Cf_applyAct_le blank a ts
      have h2 := ih (GSPre.applyAct blank ts a)
      simp only [GSPre.applyActs_cons, List.length_cons] at *
      omega


theorem width_Cs_applyAct_le (blank : Fin sc) (a : GSPre.Act sc) (ts : GSPre.Tapes sc) :
    ClearAny.width (GSPre.applyAct blank ts a).Cs ≤ ClearAny.width ts.Cs + 1 := by
  cases a with
  | Cs b m => exact ClearAny.width_step blank ts.Cs b m
  | _ => simp [GSPre.applyAct]

theorem width_Cs_applyActs_le (blank : Fin sc) (l : List (GSPre.Act sc)) (ts : GSPre.Tapes sc) :
    ClearAny.width (GSPre.applyActs blank l ts).Cs ≤ ClearAny.width ts.Cs + l.length := by
  induction l generalizing ts with
  | nil => simp [GSPre.applyActs]
  | cons a l ih =>
      have h1 := width_Cs_applyAct_le blank a ts
      have h2 := ih (GSPre.applyAct blank ts a)
      simp only [GSPre.applyActs_cons, List.length_cons] at *
      omega


theorem width_Cr_applyAct_le (blank : Fin sc) (a : GSPre.Act sc) (ts : GSPre.Tapes sc) :
    ClearAny.width (GSPre.applyAct blank ts a).Cr ≤ ClearAny.width ts.Cr + 1 := by
  cases a with
  | Cr b m => exact ClearAny.width_step blank ts.Cr b m
  | _ => simp [GSPre.applyAct]

theorem width_Cr_applyActs_le (blank : Fin sc) (l : List (GSPre.Act sc)) (ts : GSPre.Tapes sc) :
    ClearAny.width (GSPre.applyActs blank l ts).Cr ≤ ClearAny.width ts.Cr + l.length := by
  induction l generalizing ts with
  | nil => simp [GSPre.applyActs]
  | cons a l ih =>
      have h1 := width_Cr_applyAct_le blank a ts
      have h2 := ih (GSPre.applyAct blank ts a)
      simp only [GSPre.applyActs_cons, List.length_cons] at *
      omega


theorem width_V1_applyAct_le (blank : Fin sc) (a : GSPre.Act sc) (ts : GSPre.Tapes sc) :
    ClearAny.width (GSPre.applyAct blank ts a).V1 ≤ ClearAny.width ts.V1 + 1 := by
  cases a with
  | V1 m => exact ClearAny.width_step blank ts.V1 ts.V1.focus m
  | _ => simp [GSPre.applyAct]

theorem width_V1_applyActs_le (blank : Fin sc) (l : List (GSPre.Act sc)) (ts : GSPre.Tapes sc) :
    ClearAny.width (GSPre.applyActs blank l ts).V1 ≤ ClearAny.width ts.V1 + l.length := by
  induction l generalizing ts with
  | nil => simp [GSPre.applyActs]
  | cons a l ih =>
      have h1 := width_V1_applyAct_le blank a ts
      have h2 := ih (GSPre.applyAct blank ts a)
      simp only [GSPre.applyActs_cons, List.length_cons] at *
      omega


theorem width_V2_applyAct_le (blank : Fin sc) (a : GSPre.Act sc) (ts : GSPre.Tapes sc) :
    ClearAny.width (GSPre.applyAct blank ts a).V2 ≤ ClearAny.width ts.V2 + 1 := by
  cases a with
  | V2 m => exact ClearAny.width_step blank ts.V2 ts.V2.focus m
  | _ => simp [GSPre.applyAct]

theorem width_V2_applyActs_le (blank : Fin sc) (l : List (GSPre.Act sc)) (ts : GSPre.Tapes sc) :
    ClearAny.width (GSPre.applyActs blank l ts).V2 ≤ ClearAny.width ts.V2 + l.length := by
  induction l generalizing ts with
  | nil => simp [GSPre.applyActs]
  | cons a l ih =>
      have h1 := width_V2_applyAct_le blank a ts
      have h2 := ih (GSPre.applyAct blank ts a)
      simp only [GSPre.applyActs_cons, List.length_cons] at *
      omega

/-! ## 3b. 準備：ヘッドを右へ歩かせる（`leftWalk` の右版） -/

/-- ヘッドを右へ `n` 歩（読んだ記号を書き戻す）。`PatternTapes.leftWalk` の右版。 -/
def rightWalk (i : Fin 12) (n : ℕ) : List (SAct sc) := List.replicate n (SAct.keep i .right)

@[simp] theorem rightWalk_length (i : Fin 12) (n : ℕ) :
    (rightWalk (sc := sc) i n).length = n := by simp [rightWalk]

theorem rightWalk_untouched (blank : Fin sc) {i j : Fin 12} (h : j ≠ i) (n : ℕ) (S : Tapes sc) :
    run blank (rightWalk i n) S j = S j := by
  refine run_untouched blank j _ S (fun a ha => ?_)
  rw [List.eq_of_mem_replicate ha]
  exact Ne.symm h

theorem rightWalk_spec (blank : Fin sc) (i : Fin 12) :
    ∀ (n m : ℕ) (S : Tapes sc) (w : List (Fin sc)), m + n < w.length →
      Tape.SeqView blank (S i) w m →
      Tape.SeqView blank (run blank (rightWalk i n) S i) w (m + n) := by
  intro n
  induction n with
  | zero => intro m S w _ h; simpa [rightWalk] using h
  | succ n ih =>
    intro m S w hlt h
    have hstep : run blank (rightWalk (sc := sc) i (n + 1)) S
        = run blank (rightWalk i n) (applyS blank S (SAct.keep i .right)) := by
      rw [rightWalk, List.replicate_succ, run_cons, rightWalk]
    rw [hstep]
    have h2 : Tape.SeqView blank (run blank (rightWalk i n) (applyS blank S (SAct.keep i .right))
        i) w ((m + 1) + n) := by
      refine ih (m + 1) _ w (by omega) ?_
      rw [applyS_keep_self]
      exact Tape.seq_move_right h (by omega)
    rwa [show (m + 1) + n = m + (n + 1) from by omega] at h2

/-! ## 3c. 同じ読み取りを 2 本に同時に積む（`copyLoop` の 2 目的地版） -/

/-- 1 記号ぶん：`i` が読んでいる記号を `j1`, `j2` の両方に積み、`i` を左へ 1 歩。 -/
def copyRound2 (i j1 j2 : Fin 12) (S : Tapes sc) : List (SAct sc) :=
  [SAct.put j1 (Tape.read (S i)) .right, SAct.put j2 (Tape.read (S i)) .right, SAct.keep i .left]

/-- `n` 記号ぶん。 -/
def copyLoop2 (blank : Fin sc) (i j1 j2 : Fin 12) : ℕ → Tapes sc → List (SAct sc)
  | 0, _ => []
  | n + 1, S =>
      copyRound2 i j1 j2 S ++ copyLoop2 blank i j1 j2 n (run blank (copyRound2 i j1 j2 S) S)

theorem copyLoop2_length (blank : Fin sc) (i j1 j2 : Fin 12) :
    ∀ (n : ℕ) (S : Tapes sc), (copyLoop2 blank i j1 j2 n S).length = 3 * n := by
  intro n
  induction n with
  | zero => intro S; rfl
  | succ n ih =>
    intro S
    rw [copyLoop2, List.length_append, ih]
    simp [copyRound2]
    omega

theorem copyLoop2_untouched (blank : Fin sc) {i j1 j2 l : Fin 12} (hi : l ≠ i) (h1 : l ≠ j1)
    (h2 : l ≠ j2) :
    ∀ (n : ℕ) (S : Tapes sc), run blank (copyLoop2 blank i j1 j2 n S) S l = S l := by
  intro n
  induction n with
  | zero => intro S; rfl
  | succ n ih =>
    intro S
    rw [copyLoop2, run_append, ih]
    refine run_untouched blank l _ S (fun a ha => ?_)
    rcases List.mem_cons.1 ha with h | h
    · subst h; exact Ne.symm h1
    · rcases List.mem_cons.1 h with h | h
      · subst h; exact Ne.symm h2
      · rcases List.mem_cons.1 h with h | h
        · subst h; exact Ne.symm hi
        · simp at h

/-- **主補題**：`i` のヘッドを添字 `b` から左へ `n` 歩ぶん歩かせながら、読んだ記号を
`j1`, `j2` の両方に積む。`PatternTapes.copyLoop_spec` の 2 目的地版。 -/
theorem copyLoop2_spec (blank : Fin sc) {i j1 j2 : Fin 12} (hij1 : j1 ≠ i) (hij2 : j2 ≠ i)
    (hjj : j1 ≠ j2) :
    ∀ (n b : ℕ) (S : Tapes sc) (w l1 l2 : List (Fin sc)), n ≤ b + 1 →
      Tape.SeqView blank (S i) w b →
      Tape.StackView blank (S j1) l1 → Tape.StackView blank (S j2) l2 →
      Tape.SeqView blank (run blank (copyLoop2 blank i j1 j2 n S) S i) w (b - n) ∧
        Tape.StackView blank (run blank (copyLoop2 blank i j1 j2 n S) S j1)
          (((w.take (b + 1)).drop (b + 1 - n)) ++ l1) ∧
        Tape.StackView blank (run blank (copyLoop2 blank i j1 j2 n S) S j2)
          (((w.take (b + 1)).drop (b + 1 - n)) ++ l2) := by
  intro n
  induction n with
  | zero =>
    intro b S w l1 l2 _ hs hst1 hst2
    have hz : run blank (copyLoop2 blank i j1 j2 0 S) S = S := rfl
    rw [hz]
    have hnil : (w.take (b + 1)).drop (b + 1) = [] := by
      refine List.drop_eq_nil_of_le ?_
      simp
    refine ⟨by simpa using hs, ?_, ?_⟩ <;> simp [hnil]
    exacts [hst1, hst2]
  | succ n ih =>
    intro b S w l1 l2 hn hs hst1 hst2
    have hnb : n ≤ b := by omega
    have hblt : b < w.length := hs.lt
    set S₁ := run blank (copyRound2 i j1 j2 S) S with hS₁
    have hS₁i : S₁ i = Tape.step blank (S i) (S i).focus .left := by
      rw [hS₁, copyRound2]
      show applyS blank
          (applyS blank (applyS blank S (SAct.put j1 (Tape.read (S i)) .right))
            (SAct.put j2 (Tape.read (S i)) .right)) (SAct.keep i .left) i = _
      rw [applyS_keep_self,
        applyS_ne blank _ (SAct.put j2 (Tape.read (S i)) .right) (Ne.symm hij2),
        applyS_ne blank _ (SAct.put j1 (Tape.read (S i)) .right) (Ne.symm hij1)]
    have hS₁j1 : S₁ j1 = Tape.step blank (S j1) (S i).focus .right := by
      rw [hS₁, copyRound2]
      show applyS blank
          (applyS blank (applyS blank S (SAct.put j1 (Tape.read (S i)) .right))
            (SAct.put j2 (Tape.read (S i)) .right)) (SAct.keep i .left) j1 = _
      rw [applyS_ne blank _ (SAct.keep i .left) hij1,
        applyS_ne blank _ (SAct.put j2 (Tape.read (S i)) .right) hjj,
        applyS_put_self]
      rfl
    have hS₁j2 : S₁ j2 = Tape.step blank (S j2) (S i).focus .right := by
      rw [hS₁, copyRound2]
      show applyS blank
          (applyS blank (applyS blank S (SAct.put j1 (Tape.read (S i)) .right))
            (SAct.put j2 (Tape.read (S i)) .right)) (SAct.keep i .left) j2 = _
      rw [applyS_ne blank _ (SAct.keep i .left) hij2, applyS_put_self,
        applyS_ne blank S (SAct.put j1 (Tape.read (S i)) .right) (Ne.symm hjj)]
      rfl
    have hstack1 : Tape.StackView blank (S₁ j1) ((S i).focus :: l1) := by
      rw [hS₁j1]; exact Tape.push_spec hst1 _
    have hstack2 : Tape.StackView blank (S₁ j2) ((S i).focus :: l2) := by
      rw [hS₁j2]; exact Tape.push_spec hst2 _
    have hseq : Tape.SeqView blank (S₁ i) w (b - 1) := by
      rw [hS₁i]
      cases b with
      | zero => exact Tape.seq_move_left_edge hs
      | succ c => exact Tape.seq_move_left hs
    have hrun : run blank (copyLoop2 blank i j1 j2 (n + 1) S) S
        = run blank (copyLoop2 blank i j1 j2 n S₁) S₁ := by
      rw [copyLoop2, run_append]
    obtain ⟨h1, h2, h3⟩ := ih (b - 1) S₁ w ((S i).focus :: l1) ((S i).focus :: l2) (by omega)
      hseq hstack1 hstack2
    rw [hrun]
    have hfocus : w[b]? = some (S i).focus := hs.focus_eq
    have htake : w.take (b + 1) = w.take b ++ [(S i).focus] := by
      rw [List.take_add_one, hfocus]; rfl
    have hlen : (w.take b).length = b := by
      simp only [List.length_take]; omega
    have hdrop : (w.take (b + 1)).drop (b - n) = (w.take b).drop (b - n) ++ [(S i).focus] := by
      rw [htake, List.drop_append_of_le_length (by rw [hlen]; omega)]
    have key : ∀ l : List (Fin sc),
        ((w.take (b - 1 + 1)).drop (b - 1 + 1 - n)) ++ ((S i).focus :: l)
          = ((w.take (b + 1)).drop (b + 1 - (n + 1))) ++ l := by
      intro l
      rcases Nat.eq_zero_or_pos b with rfl | hbpos
      · have hn0 : n = 0 := by omega
        subst hn0
        simp [htake]
      · rw [show b - 1 + 1 = b from by omega, show b + 1 - (n + 1) = b - n from by omega, hdrop]
        simp
    refine ⟨by simpa [Nat.sub_sub, Nat.add_comm] using h1, ?_, ?_⟩
    · rw [← key l1]; exact h2
    · rw [← key l2]; exact h3

/-! ## 3d. 前処理の prologue：`sIn` から `x` を `sP`/`sU` に書く -/

section Prologue

variable {blank startSym endSym mark : Fin sc} {L : ℕ} {w Text : List (Fin sc)} {S : Tapes sc}

/-- **prologue プログラム**：`sIn`（ヘッド `L - 1`）から `x = (w.take L).reverse` を
`sP`/`sU` の両方へ `pword startSym endSym x`（ヘッド添字 `1`）の形で書き、`sIn` のヘッドを
`L - 1` へ戻す。`copyLoop2` を左へ歩くことで書き込む語が自動的に反転するので、
実際に反転操作を別に行う必要はない。 -/
def prologueProg (blank startSym endSym : Fin sc) (L : ℕ) : Tapes sc → List (SAct sc) :=
  seqP blank (fun _ => pushBoth startSym)
    (seqP blank (fun S => copyLoop2 blank sIn sU sP L S)
      (seqP blank (fun _ => pushBoth endSym)
        (seqP blank (fun _ => settle blank sU L)
          (seqP blank (fun _ => settle blank sP L)
            (fun _ => rightWalk sIn (L - 1))))))

/-- **prologue の長さ**：`6 * L + 5` ちょうど（`L ≥ 1`）。 -/
theorem prologueProg_length (hL : 0 < L) (S : Tapes sc) :
    (prologueProg (sc := sc) blank startSym endSym L S).length = 6 * L + 5 := by
  simp only [prologueProg, seqP_length, pushBoth_length, copyLoop2_length, settle_length,
    rightWalk_length]
  omega

theorem prologueProg_length_le (hL : 0 < L) (S : Tapes sc) :
    (prologueProg (sc := sc) blank startSym endSym L S).length ≤ 6 * L + 5 :=
  (prologueProg_length hL S).le

/-- **prologue の正しさ**：`PrepPre` から出発すると、`prj` を通して `GSPre.Enc` が
初期状態（`a = b = 0`, `Ctr` は全 `0`）で成立し、テキスト 2 本 (`sT`/`sX2`) は不変、
`sIn` は元の `SeqView` に戻る。 -/
theorem prologue_spec (hpre : StageTapes.PrepPre blank mark L w Text S) :
    GSPre.Enc blank startSym endSym mark (PrepInstances.stagePat w L) 0 0 ⟨0, 0, 0, 0, 0, 0, 0⟩
        (prj (run blank (prologueProg blank startSym endSym L S) S))
      ∧ run blank (prologueProg blank startSym endSym L S) S sT = S sT
      ∧ run blank (prologueProg blank startSym endSym L S) S sX2 = S sX2
      ∧ Tape.SeqView blank (run blank (prologueProg blank startSym endSym L S) S sIn) w (L - 1) := by
  obtain ⟨hpos, hle, hIn, hU, hP, hT, hX2, hCs, hC1, hC2, hAp, hAn, hRp, hRn⟩ := hpre
  set x := PrepInstances.stagePat w L with hx
  have hxlen : x.length = L := PrepInstances.stagePat_length hle
  -- フェーズ 1：両方に `startSym`。
  obtain ⟨S₁, hS1⟩ : ∃ T, run blank (pushBoth startSym) S = T := ⟨_, rfl⟩
  have hS1U : S₁ sU = Tape.step blank (S sU) startSym .right := by rw [← hS1]; exact pushBoth_U ..
  have hS1P : S₁ sP = Tape.step blank (S sP) startSym .right := by rw [← hS1]; exact pushBoth_P ..
  have hS1st1 : Tape.StackView blank (S₁ sU) [startSym] := by
    rw [hS1U]; simpa using Tape.push_spec hU startSym
  have hS1st2 : Tape.StackView blank (S₁ sP) [startSym] := by
    rw [hS1P]; simpa using Tape.push_spec hP startSym
  have hS1In : Tape.SeqView blank (S₁ sIn) w (L - 1) := by
    rw [← hS1]; rwa [pushBoth_ne blank startSym (show sIn ≠ sU by decide)
      (show sIn ≠ sP by decide)]
  have hS1T : S₁ sT = S sT := by
    rw [← hS1]; exact pushBoth_ne blank startSym (show sT ≠ sU by decide)
      (show sT ≠ sP by decide) S
  have hS1X2 : S₁ sX2 = S sX2 := by
    rw [← hS1]; exact pushBoth_ne blank startSym (show sX2 ≠ sU by decide)
      (show sX2 ≠ sP by decide) S
  have hS1cnt : ∀ j : Fin 12, j ≠ sU → j ≠ sP → S₁ j = S j := by
    intro j hju hjp; rw [← hS1]; exact pushBoth_ne blank startSym hju hjp S
  -- フェーズ 2：`sIn` から両方へ `x` を積む。
  obtain ⟨S₂, hS2⟩ : ∃ T, run blank (copyLoop2 blank sIn sU sP L S₁) S₁ = T := ⟨_, rfl⟩
  have hLb : L ≤ (L - 1) + 1 := by omega
  obtain ⟨h2i, h2u, h2p⟩ := copyLoop2_spec blank (show sU ≠ sIn by decide)
    (show sP ≠ sIn by decide) (show sU ≠ sP by decide) L (L - 1) S₁ w [startSym] [startSym]
    hLb hS1In hS1st1 hS1st2
  rw [hS2] at h2i h2u h2p
  have hb1 : (L - 1) + 1 = L := by omega
  have hdrop0 : L - L = 0 := by omega
  rw [hb1] at h2u h2p
  have h2i' : Tape.SeqView blank (S₂ sIn) w 0 := by
    rwa [show L - 1 - L = 0 from by omega] at h2i
  have h2u' : Tape.StackView blank (S₂ sU) (w.take L ++ [startSym]) := by
    simpa [hdrop0] using h2u
  have h2p' : Tape.StackView blank (S₂ sP) (w.take L ++ [startSym]) := by
    simpa [hdrop0] using h2p
  have h2T : S₂ sT = S sT := by
    rw [← hS2, copyLoop2_untouched blank (show sT ≠ sIn by decide) (show sT ≠ sU by decide)
      (show sT ≠ sP by decide) L S₁, hS1T]
  have h2X2 : S₂ sX2 = S sX2 := by
    rw [← hS2, copyLoop2_untouched blank (show sX2 ≠ sIn by decide) (show sX2 ≠ sU by decide)
      (show sX2 ≠ sP by decide) L S₁, hS1X2]
  have h2cnt : ∀ j : Fin 12, j ≠ sIn → j ≠ sU → j ≠ sP → S₂ j = S₁ j := by
    intro j hji hju hjp
    rw [← hS2]; exact copyLoop2_untouched blank hji hju hjp L S₁
  -- フェーズ 3：両方に `endSym`。
  obtain ⟨S₃, hS3⟩ : ∃ T, run blank (pushBoth endSym) S₂ = T := ⟨_, rfl⟩
  have hS3U : S₃ sU = Tape.step blank (S₂ sU) endSym .right := by rw [← hS3]; exact pushBoth_U ..
  have hS3P : S₃ sP = Tape.step blank (S₂ sP) endSym .right := by rw [← hS3]; exact pushBoth_P ..
  have hS3st1 : Tape.StackView blank (S₃ sU) (endSym :: (w.take L ++ [startSym])) := by
    rw [hS3U]; exact Tape.push_spec h2u' endSym
  have hS3st2 : Tape.StackView blank (S₃ sP) (endSym :: (w.take L ++ [startSym])) := by
    rw [hS3P]; exact Tape.push_spec h2p' endSym
  have hS3In : S₃ sIn = S₂ sIn := by
    rw [← hS3]; exact pushBoth_ne blank endSym (show sIn ≠ sU by decide) (show sIn ≠ sP by decide) S₂
  have hS3T : S₃ sT = S sT := by
    rw [← hS3]
    rw [pushBoth_ne blank endSym (show sT ≠ sU by decide) (show sT ≠ sP by decide) S₂, h2T]
  have hS3X2 : S₃ sX2 = S sX2 := by
    rw [← hS3]
    rw [pushBoth_ne blank endSym (show sX2 ≠ sU by decide) (show sX2 ≠ sP by decide) S₂, h2X2]
  have hS3cnt : ∀ j : Fin 12, j ≠ sU → j ≠ sP → S₃ j = S₂ j := by
    intro j hju hjp; rw [← hS3]; exact pushBoth_ne blank endSym hju hjp S₂
  -- フェーズ 4：ヘッドを添字 `1` へ（`sU`）。
  obtain ⟨S₄, hS4⟩ : ∃ T, run blank (settle blank sU L) S₃ = T := ⟨_, rfl⟩
  have hlenU : (w.take L ++ [startSym]).length = L + 1 := by
    simp [List.length_take]; omega
  have hS4U : Tape.SeqView blank (S₄ sU)
      ((endSym :: (w.take L ++ [startSym])).reverse) 1 := by
    rw [← hS4]; exact settle_spec blank sU hS3st1 hlenU
  have hS4other : ∀ j : Fin 12, j ≠ sU → S₄ j = S₃ j := by
    intro j hj; rw [← hS4]; exact settle_untouched blank hj L S₃
  -- フェーズ 5：ヘッドを添字 `1` へ（`sP`）。
  have hS4P_eq : S₄ sP = S₃ sP := hS4other sP (show sP ≠ sU by decide)
  have hS4st2 : Tape.StackView blank (S₄ sP) (endSym :: (w.take L ++ [startSym])) := by
    rw [hS4P_eq]; exact hS3st2
  obtain ⟨S₅, hS5⟩ : ∃ T, run blank (settle blank sP L) S₄ = T := ⟨_, rfl⟩
  have hS5P : Tape.SeqView blank (S₅ sP)
      ((endSym :: (w.take L ++ [startSym])).reverse) 1 := by
    rw [← hS5]; exact settle_spec blank sP hS4st2 hlenU
  have hS5other : ∀ j : Fin 12, j ≠ sP → S₅ j = S₄ j := by
    intro j hj; rw [← hS5]; exact settle_untouched blank hj L S₄
  have hS5U : Tape.SeqView blank (S₅ sU)
      ((endSym :: (w.take L ++ [startSym])).reverse) 1 := by
    rw [hS5other sU (show sU ≠ sP by decide)]; exact hS4U
  have hS5In : S₅ sIn = S₂ sIn := by
    rw [hS5other sIn (show sIn ≠ sP by decide), hS4other sIn (show sIn ≠ sU by decide), hS3In]
  have hS5T : S₅ sT = S sT := by
    rw [hS5other sT (show sT ≠ sP by decide), hS4other sT (show sT ≠ sU by decide), hS3T]
  have hS5X2 : S₅ sX2 = S sX2 := by
    rw [hS5other sX2 (show sX2 ≠ sP by decide), hS4other sX2 (show sX2 ≠ sU by decide), hS3X2]
  have hS5cnt : ∀ j : Fin 12, j ≠ sU → j ≠ sP → j ≠ sIn → S₅ j = S j := by
    intro j hju hjp hji
    rw [hS5other j hjp, hS4other j hju, hS3cnt j hju hjp, h2cnt j hji hju hjp, hS1cnt j hju hjp]
  -- フェーズ 6：`sIn` を `L - 1` へ戻す。
  have hS5In' : Tape.SeqView blank (S₅ sIn) w 0 := by rw [hS5In]; exact h2i'
  obtain ⟨S₆, hS6⟩ : ∃ T, run blank (rightWalk sIn (L - 1)) S₅ = T := ⟨_, rfl⟩
  have hLlt : (0 : ℕ) + (L - 1) < w.length := by omega
  have hS6In : Tape.SeqView blank (S₆ sIn) w (L - 1) := by
    rw [← hS6]
    have h := rightWalk_spec blank sIn (L - 1) 0 S₅ w hLlt hS5In'
    simpa using h
  have hS6other : ∀ j : Fin 12, j ≠ sIn → S₆ j = S₅ j := by
    intro j hj; rw [← hS6]; exact rightWalk_untouched blank hj (L - 1) S₅
  have hS6U : Tape.SeqView blank (S₆ sU)
      ((endSym :: (w.take L ++ [startSym])).reverse) 1 := by
    rw [hS6other sU (show sU ≠ sIn by decide)]; exact hS5U
  have hS6P : Tape.SeqView blank (S₆ sP)
      ((endSym :: (w.take L ++ [startSym])).reverse) 1 := by
    rw [hS6other sP (show sP ≠ sIn by decide)]; exact hS5P
  have hS6T : S₆ sT = S sT := by
    rw [hS6other sT (show sT ≠ sIn by decide)]; exact hS5T
  have hS6X2 : S₆ sX2 = S sX2 := by
    rw [hS6other sX2 (show sX2 ≠ sIn by decide)]; exact hS5X2
  have hS6cnt : ∀ j : Fin 12, j ≠ sU → j ≠ sP → j ≠ sIn → S₆ j = S j := by
    intro j hju hjp hji
    rw [hS6other j hji]; exact hS5cnt j hju hjp hji
  -- 実行結果は `S₆`。
  have hrun : run blank (prologueProg blank startSym endSym L S) S = S₆ := by
    simp only [prologueProg, seqP_run, hS1, hS2, hS3, hS4, hS5, hS6]
  -- `pword` への書き換え。
  have hpword : (endSym :: (w.take L ++ [startSym])).reverse
      = GSPre.pword startSym endSym x := by
    simp [GSPre.pword, hx, PrepInstances.stagePat, List.reverse_append, List.reverse_cons]
  rw [hpword] at hS6U hS6P
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hrun]
    refine
      { v1 := ?_
        v2 := ?_
        cd := ?_
        cq := ?_
        ce := ?_
        cp := ?_
        cf := ?_
        cs := ?_
        cr := ?_ }
    · show Tape.SeqView blank (S₆ sV1) (GSPre.pword startSym endSym x) (0 + 1)
      rw [Nat.zero_add]; show Tape.SeqView blank (S₆ sP) (GSPre.pword startSym endSym x) 1
      exact hS6P
    · show Tape.SeqView blank (S₆ sV2) (GSPre.pword startSym endSym x) (0 + 1)
      rw [Nat.zero_add]; show Tape.SeqView blank (S₆ sU) (GSPre.pword startSym endSym x) 1
      exact hS6U
    · show Tape.CounterView' blank mark (S₆ sCd) 0
      show Tape.CounterView' blank mark (S₆ sC2) 0
      rw [hS6cnt sC2 (by decide) (by decide) (by decide)]; exact hC2
    · show Tape.CounterView' blank mark (S₆ sCq) 0
      show Tape.CounterView' blank mark (S₆ sAp) 0
      rw [hS6cnt sAp (by decide) (by decide) (by decide)]; exact hAp
    · show Tape.CounterView' blank mark (S₆ sCe) 0
      show Tape.CounterView' blank mark (S₆ sAn) 0
      rw [hS6cnt sAn (by decide) (by decide) (by decide)]; exact hAn
    · show Tape.CounterView' blank mark (S₆ sC1) 0
      rw [hS6cnt sC1 (by decide) (by decide) (by decide)]; exact hC1
    · show Tape.CounterView' blank mark (S₆ sCf) 0
      show Tape.CounterView' blank mark (S₆ sRn) 0
      rw [hS6cnt sRn (by decide) (by decide) (by decide)]; exact hRn
    · show Tape.CounterView' blank mark (S₆ sCs) 0
      rw [hS6cnt sCs (by decide) (by decide) (by decide)]; exact hCs
    · show Tape.CounterView' blank mark (S₆ sRp) 0
      rw [hS6cnt sRp (by decide) (by decide) (by decide)]; exact hRp
  · rw [hrun]; exact hS6T
  · rw [hrun]; exact hS6X2
  · rw [hrun]; exact hS6In

end Prologue

/-! ## 3e. 1 本のテープに対する単発プログラムの埋め込み -/

/-- `GSTapes.TapeProg`（1 本のテープに対する `(記号, 移動)` 列）を、固定したスロット `i`
に対する `SAct` 列へ埋め込む。 -/
def embedSlot (i : Fin 12) : GSTapes.TapeProg sc → List (SAct sc)
  | [] => []
  | (a, m) :: rest => SAct.put i a m :: embedSlot i rest

@[simp] theorem embedSlot_length (i : Fin 12) (p : GSTapes.TapeProg sc) :
    (embedSlot i p).length = p.length := by
  induction p with
  | nil => rfl
  | cons hd tl ih => cases hd; simp [embedSlot, ih]

theorem embedSlot_run (blank : Fin sc) (i : Fin 12) :
    ∀ (p : GSTapes.TapeProg sc) (S : Tapes sc),
      run blank (embedSlot i p) S i = GSTapes.runProg blank (S i) p := by
  intro p
  induction p with
  | nil => intro S; rfl
  | cons hd tl ih =>
    intro S
    obtain ⟨a, m⟩ := hd
    show run blank (embedSlot i tl) (applyS blank S (SAct.put i a m)) i = _
    rw [ih, applyS_put_self, GSTapes.runProg_cons]

theorem embedSlot_other (blank : Fin sc) {i j : Fin 12} (h : j ≠ i) :
    ∀ (p : GSTapes.TapeProg sc) (S : Tapes sc), run blank (embedSlot i p) S j = S j := by
  intro p
  induction p with
  | nil => intro S; rfl
  | cons hd tl ih =>
    intro S
    obtain ⟨a, m⟩ := hd
    show run blank (embedSlot i tl) (applyS blank S (SAct.put i a m)) j = _
    rw [ih, applyS_ne blank S (SAct.put i a m) (show j ≠ i from h)]

/-! ## 3f. スタック・カウンタの形非依存クリア -/

/-- `ClearAny.clearAny` が与える存在から選んだ、テープ 1 本を空スタックへ戻す
（1 テープぶんの）プログラム。 -/
noncomputable def clearProgFor (blank : Fin sc) (tp : TapeConfiguration sc) : GSTapes.TapeProg sc :=
  Classical.choose (ClearAny.clearAny blank tp)

theorem clearProgFor_spec (blank : Fin sc) (tp : TapeConfiguration sc) :
    (clearProgFor blank tp).length ≤ 3 * ClearAny.width tp + 3 ∧
      ClearAny.IsBlankTape blank (GSTapes.runProg blank tp (clearProgFor blank tp)) :=
  Classical.choose_spec (ClearAny.clearAny blank tp)

/-- スロット `i` を空スタック `[]` へ戻す動作列。 -/
noncomputable def clearStackToEmptyProg (blank : Fin sc) (i : Fin 12) (S : Tapes sc) :
    List (SAct sc) :=
  embedSlot i (clearProgFor blank (S i))

theorem clearStackToEmptyProg_length (blank : Fin sc) (i : Fin 12) (S : Tapes sc) :
    (clearStackToEmptyProg blank i S).length ≤ 3 * ClearAny.width (S i) + 3 := by
  rw [clearStackToEmptyProg, embedSlot_length]
  exact (clearProgFor_spec blank (S i)).1

theorem clearStackToEmptyProg_spec (blank : Fin sc) (i : Fin 12) (S : Tapes sc) :
    Tape.StackView blank (run blank (clearStackToEmptyProg blank i S) S i) [] := by
  rw [clearStackToEmptyProg, embedSlot_run]
  exact (clearProgFor_spec blank (S i)).2

theorem clearStackToEmptyProg_other (blank : Fin sc) {i j : Fin 12} (h : j ≠ i) (S : Tapes sc) :
    run blank (clearStackToEmptyProg blank i S) S j = S j := by
  rw [clearStackToEmptyProg]; exact embedSlot_other blank h _ S

/-- スロット `i`（現在値は問わない）を単進カウンタの値 `0` へ戻す動作列：
形非依存の全消去のあと、底のマーカ `mark` を 1 手で書き戻す
（`CounterView' blank mark tp 0 ↔ StackView blank tp [mark]`）。 -/
noncomputable def clearCounterToZeroProg (blank mark : Fin sc) (i : Fin 12) (S : Tapes sc) :
    List (SAct sc) :=
  clearStackToEmptyProg blank i S ++ [SAct.put i mark .right]

theorem clearCounterToZeroProg_length (blank mark : Fin sc) (i : Fin 12) (S : Tapes sc) :
    (clearCounterToZeroProg blank mark i S).length ≤ 3 * ClearAny.width (S i) + 4 := by
  rw [clearCounterToZeroProg, List.length_append]
  have h := clearStackToEmptyProg_length blank i S
  simp only [List.length_cons, List.length_nil]
  omega

theorem clearCounterToZeroProg_spec (blank mark : Fin sc) (i : Fin 12) (S : Tapes sc) :
    Tape.CounterView' blank mark (run blank (clearCounterToZeroProg blank mark i S) S i) 0 := by
  rw [clearCounterToZeroProg, run_append]
  have hstack := clearStackToEmptyProg_spec blank i S
  have hstep : run blank [SAct.put i mark .right] (run blank (clearStackToEmptyProg blank i S) S) i
      = Tape.step blank (run blank (clearStackToEmptyProg blank i S) S i) mark .right := by
    show applyS blank (run blank (clearStackToEmptyProg blank i S) S) (SAct.put i mark .right) i
      = _
    exact applyS_put_self ..
  rw [hstep, Tape.counterView'_zero]
  simpa using Tape.push_spec hstack mark

theorem clearCounterToZeroProg_other (blank mark : Fin sc) {i j : Fin 12} (h : j ≠ i)
    (S : Tapes sc) : run blank (clearCounterToZeroProg blank mark i S) S j = S j := by
  rw [clearCounterToZeroProg, run_append, run_cons, run_nil,
    applyS_ne blank _ (SAct.put i mark .right) h, clearStackToEmptyProg_other blank h S]

/-! ## 3g. 単進カウンタの増分ループ -/

/-- `i` を `n` 回インクリメント。 -/
def incLoop (blank : Fin sc) (i : Fin 12) : ℕ → List (SAct sc)
  | 0 => []
  | n + 1 => incAct blank i :: incLoop blank i n

@[simp] theorem incLoop_length (blank : Fin sc) (i : Fin 12) (n : ℕ) :
    (incLoop (sc := sc) blank i n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [incLoop, ih]

theorem incLoop_untouched (blank : Fin sc) {i j : Fin 12} (h : j ≠ i) :
    ∀ (n : ℕ) (S : Tapes sc), run blank (incLoop blank i n) S j = S j := by
  intro n
  induction n with
  | zero => intro S; rfl
  | succ n ih =>
    intro S
    rw [incLoop, run_cons, ih]
    exact applyS_ne blank S (incAct blank i) (show j ≠ i from h)

theorem incLoop_spec (blank mark : Fin sc) (i : Fin 12) :
    ∀ (n : ℕ) (S : Tapes sc) (m0 : ℕ), Tape.CounterView' blank mark (S i) m0 →
      Tape.CounterView' blank mark (run blank (incLoop blank i n) S i) (m0 + n) := by
  intro n
  induction n with
  | zero => intro S m0 h; simpa [incLoop] using h
  | succ n ih =>
    intro S m0 h
    rw [incLoop, run_cons]
    have hstep : applyS blank S (incAct blank i) i = Tape.step blank (S i) blank .right := by
      show applyS blank S (SAct.put i blank .right) i = _
      exact applyS_put_self ..
    have h2 : Tape.CounterView' blank mark (applyS blank S (incAct blank i) i) (m0 + 1) := by
      rw [hstep]; exact Tape.counter'_inc h
    have h3 := ih (applyS blank S (incAct blank i)) (m0 + 1) h2
    rwa [show m0 + 1 + n = m0 + (n + 1) from by omega] at h3

/-! ## 3h. epilogue：`decProg` の終状態から `SetupPre` を作る -/

section Epilogue

variable {blank startSym endSym mark : Fin sc} {L s : ℕ} {ts : Tapes sc}

/-- **epilogue プログラム**：`decompose2_on_tapes` の終状態から `SetupPre` の形へ戻す。
`sC2`（`Cd`）・`sAp`（`Cq`）・`sAn`（`Ce`）・`sRn`（`Cf`）は現在値によらず `0` に掃除し、
`sP`（`V1`）・`sU`（`V2`）はスタック `[]` に掃除する。`sC1`（`Cp`、生の周期 `p₁`）と
`sRp`（`Cr`、生の到達域 `r`）だけは `effPeriod`/`effReach` の正規化が要る：
生の `p₁ = 0`（退化ケース）なら `sC1` を `L - s + 1` へ増分し、`sRp` を `0` へ掃除する。
`p₁ ≠ 0` ならどちらも触らない（すでに正規化後の値と一致している）。
`s` は呼び出し側が渡す `(decompose2 x 8).1`（`= cval (ts sCs)`）。 -/
noncomputable def epilogueProg (blank mark : Fin sc) (L s : ℕ) (ts : Tapes sc) : List (SAct sc) :=
  seqP blank (fun _ => if cval (ts sC1) = 0 then incLoop blank sC1 (L - s + 1) else [])
    (seqP blank (fun S => clearCounterToZeroProg blank mark sC2 S)
      (seqP blank (fun S => clearCounterToZeroProg blank mark sAp S)
        (seqP blank (fun S => clearCounterToZeroProg blank mark sAn S)
          (seqP blank (fun S => clearCounterToZeroProg blank mark sRn S)
            (seqP blank
              (fun S => if cval (ts sC1) = 0 then clearCounterToZeroProg blank mark sRp S else [])
              (seqP blank (fun S => clearStackToEmptyProg blank sP S)
                (fun S => clearStackToEmptyProg blank sU S))))))) ts

/-- **epilogue の正しさ**：`decompose2_on_tapes` の終状態（生の周期 `p1raw`、生の到達域 `r`
を保持していること）から出発すると、`sC1`/`sRp` は `effPeriod`/`effReach` が要求する
正規化済みの値になり、`sC2/sAp/sAn/sRn` は `0`、`sP`/`sU` は空スタックになる。
`sT`/`sX2`/`sIn`/`sCs` は不変。 -/
theorem epilogue_spec (p1raw r : ℕ)
    (hC1 : Tape.CounterView' blank mark (ts sC1) p1raw)
    (hRp : Tape.CounterView' blank mark (ts sRp) r) :
    Tape.CounterView' blank mark (run blank (epilogueProg blank mark L s ts) ts sC1)
        (if p1raw = 0 then (L - s) + 1 else p1raw)
      ∧ Tape.CounterView' blank mark (run blank (epilogueProg blank mark L s ts) ts sRp)
          (if p1raw = 0 then 0 else r)
      ∧ Tape.CounterView' blank mark (run blank (epilogueProg blank mark L s ts) ts sC2) 0
      ∧ Tape.CounterView' blank mark (run blank (epilogueProg blank mark L s ts) ts sAp) 0
      ∧ Tape.CounterView' blank mark (run blank (epilogueProg blank mark L s ts) ts sAn) 0
      ∧ Tape.CounterView' blank mark (run blank (epilogueProg blank mark L s ts) ts sRn) 0
      ∧ Tape.StackView blank (run blank (epilogueProg blank mark L s ts) ts sP) []
      ∧ Tape.StackView blank (run blank (epilogueProg blank mark L s ts) ts sU) []
      ∧ run blank (epilogueProg blank mark L s ts) ts sT = ts sT
      ∧ run blank (epilogueProg blank mark L s ts) ts sX2 = ts sX2
      ∧ run blank (epilogueProg blank mark L s ts) ts sIn = ts sIn
      ∧ run blank (epilogueProg blank mark L s ts) ts sCs = ts sCs := by
  have hcv : cval (ts sC1) = p1raw := cval_eq hC1
  -- フェーズ 0：`sC1` の正規化（`p1raw = 0` のときだけ）。
  obtain ⟨S₀, hS0⟩ : ∃ T,
      run blank (if cval (ts sC1) = 0 then incLoop blank sC1 (L - s + 1) else []) ts = T :=
    ⟨_, rfl⟩
  have hS0C1 : Tape.CounterView' blank mark (S₀ sC1) (if p1raw = 0 then (L - s) + 1 else p1raw) := by
    rw [← hS0, hcv]
    split_ifs with h
    · simpa using incLoop_spec blank mark sC1 (L - s + 1) ts 0 (by rw [h] at hC1; exact hC1)
    · simpa using hC1
  have hS0other : ∀ j : Fin 12, j ≠ sC1 → S₀ j = ts j := by
    intro j hj
    rw [← hS0]
    split_ifs with h
    · exact incLoop_untouched blank hj _ ts
    · rfl
  -- フェーズ 1–4：`sC2`, `sAp`, `sAn`, `sRn` を掃除。
  obtain ⟨S₁, hS1⟩ : ∃ T, run blank (clearCounterToZeroProg blank mark sC2 S₀) S₀ = T := ⟨_, rfl⟩
  obtain ⟨S₂, hS2⟩ : ∃ T, run blank (clearCounterToZeroProg blank mark sAp S₁) S₁ = T := ⟨_, rfl⟩
  obtain ⟨S₃, hS3⟩ : ∃ T, run blank (clearCounterToZeroProg blank mark sAn S₂) S₂ = T := ⟨_, rfl⟩
  obtain ⟨S₄, hS4⟩ : ∃ T, run blank (clearCounterToZeroProg blank mark sRn S₃) S₃ = T := ⟨_, rfl⟩
  have hS1C2 : Tape.CounterView' blank mark (S₁ sC2) 0 := by
    rw [← hS1]; exact clearCounterToZeroProg_spec blank mark sC2 S₀
  have hS1other : ∀ j : Fin 12, j ≠ sC2 → S₁ j = S₀ j := by
    intro j hj; rw [← hS1]; exact clearCounterToZeroProg_other blank mark hj S₀
  have hS2Ap : Tape.CounterView' blank mark (S₂ sAp) 0 := by
    rw [← hS2]; exact clearCounterToZeroProg_spec blank mark sAp S₁
  have hS2other : ∀ j : Fin 12, j ≠ sAp → S₂ j = S₁ j := by
    intro j hj; rw [← hS2]; exact clearCounterToZeroProg_other blank mark hj S₁
  have hS3An : Tape.CounterView' blank mark (S₃ sAn) 0 := by
    rw [← hS3]; exact clearCounterToZeroProg_spec blank mark sAn S₂
  have hS3other : ∀ j : Fin 12, j ≠ sAn → S₃ j = S₂ j := by
    intro j hj; rw [← hS3]; exact clearCounterToZeroProg_other blank mark hj S₂
  have hS4Rn : Tape.CounterView' blank mark (S₄ sRn) 0 := by
    rw [← hS4]; exact clearCounterToZeroProg_spec blank mark sRn S₃
  have hS4other : ∀ j : Fin 12, j ≠ sRn → S₄ j = S₃ j := by
    intro j hj; rw [← hS4]; exact clearCounterToZeroProg_other blank mark hj S₃
  have hchain4 : ∀ j : Fin 12, j ≠ sC2 → j ≠ sAp → j ≠ sAn → j ≠ sRn → S₄ j = S₀ j := by
    intro j h1 h2 h3 h4
    rw [hS4other j h4, hS3other j h3, hS2other j h2, hS1other j h1]
  -- フェーズ 5：`sRp` の正規化（`p1raw = 0` のときだけ掃除、そうでなければ不変）。
  obtain ⟨S₅, hS5⟩ : ∃ T,
      run blank (if cval (ts sC1) = 0 then clearCounterToZeroProg blank mark sRp S₄
        else ([] : List (SAct sc))) S₄ = T := ⟨_, rfl⟩
  have hRp4 : Tape.CounterView' blank mark (S₄ sRp) r := by
    rw [hchain4 sRp (by decide) (by decide) (by decide) (by decide),
      hS0other sRp (by decide)]
    exact hRp
  have hS5Rp : Tape.CounterView' blank mark (S₅ sRp) (if p1raw = 0 then 0 else r) := by
    rw [← hS5, hcv]
    split_ifs with h
    · exact clearCounterToZeroProg_spec blank mark sRp S₄
    · simpa using hRp4
  have hS5other : ∀ j : Fin 12, j ≠ sRp → S₅ j = S₄ j := by
    intro j hj
    rw [← hS5]
    split_ifs with h
    · exact clearCounterToZeroProg_other blank mark hj S₄
    · rfl
  -- フェーズ 6–7：`sP`, `sU` を空スタックへ。
  obtain ⟨S₆, hS6⟩ : ∃ T, run blank (clearStackToEmptyProg blank sP S₅) S₅ = T := ⟨_, rfl⟩
  obtain ⟨S₇, hS7⟩ : ∃ T, run blank (clearStackToEmptyProg blank sU S₆) S₆ = T := ⟨_, rfl⟩
  have hS6P : Tape.StackView blank (S₆ sP) [] := by
    rw [← hS6]; exact clearStackToEmptyProg_spec blank sP S₅
  have hS6other : ∀ j : Fin 12, j ≠ sP → S₆ j = S₅ j := by
    intro j hj; rw [← hS6]; exact clearStackToEmptyProg_other blank hj S₅
  have hS7U : Tape.StackView blank (S₇ sU) [] := by
    rw [← hS7]; exact clearStackToEmptyProg_spec blank sU S₆
  have hS7other : ∀ j : Fin 12, j ≠ sU → S₇ j = S₆ j := by
    intro j hj; rw [← hS7]; exact clearStackToEmptyProg_other blank hj S₆
  have hS7P : Tape.StackView blank (S₇ sP) [] := by
    rw [hS7other sP (by decide)]; exact hS6P
  -- 実行結果は `S₇`。
  have hrun : run blank (epilogueProg blank mark L s ts) ts = S₇ := by
    simp only [epilogueProg, seqP_run, hS0, hS1, hS2, hS3, hS4, hS5, hS6, hS7]
  have hchain7 : ∀ j : Fin 12, j ≠ sP → j ≠ sU → j ≠ sRp → j ≠ sC2 → j ≠ sAp → j ≠ sAn →
      j ≠ sRn → j ≠ sC1 → S₇ j = ts j := by
    intro j h1 h2 h3 h4 h5 h6 h7 h8
    rw [hS7other j h2, hS6other j h1, hS5other j h3, hchain4 j h4 h5 h6 h7, hS0other j h8]
  have hS7sC1 : S₇ sC1 = S₀ sC1 := by
    rw [hS7other sC1 (by decide), hS6other sC1 (by decide), hS5other sC1 (by decide),
      hchain4 sC1 (by decide) (by decide) (by decide) (by decide)]
  have hS7sRp : S₇ sRp = S₅ sRp := by
    rw [hS7other sRp (by decide), hS6other sRp (by decide)]
  have hS7sC2 : S₇ sC2 = S₁ sC2 := by
    rw [hS7other sC2 (by decide), hS6other sC2 (by decide), hS5other sC2 (by decide),
      hS4other sC2 (by decide), hS3other sC2 (by decide), hS2other sC2 (by decide)]
  have hS7sAp : S₇ sAp = S₂ sAp := by
    rw [hS7other sAp (by decide), hS6other sAp (by decide), hS5other sAp (by decide),
      hS4other sAp (by decide), hS3other sAp (by decide)]
  have hS7sAn : S₇ sAn = S₃ sAn := by
    rw [hS7other sAn (by decide), hS6other sAn (by decide), hS5other sAn (by decide),
      hS4other sAn (by decide)]
  have hS7sRn : S₇ sRn = S₄ sRn := by
    rw [hS7other sRn (by decide), hS6other sRn (by decide), hS5other sRn (by decide)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrun, hS7sC1]; exact hS0C1
  · rw [hrun, hS7sRp]; exact hS5Rp
  · rw [hrun, hS7sC2]; exact hS1C2
  · rw [hrun, hS7sAp]; exact hS2Ap
  · rw [hrun, hS7sAn]; exact hS3An
  · rw [hrun, hS7sRn]; exact hS4Rn
  · rw [hrun]; exact hS7P
  · rw [hrun]; exact hS7U
  · rw [hrun, hchain7 sT (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
  · rw [hrun, hchain7 sX2 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
  · rw [hrun, hchain7 sIn (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
  · rw [hrun, hchain7 sCs (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]

end Epilogue

/-! ## 3i. 全体の組み立て：`prologue` ＋ `decProg` ＋ `epilogue` -/

section Full

variable {blank startSym endSym mark : Fin sc} {L : ℕ} {w Text : List (Fin sc)} {ts : Tapes sc}

/-- **全体プログラム**：prologue で `x = (w.take L).reverse` を `sP`/`sU` に書き、
`GSPre.decProg`（`liftAct` で埋め込み）を挽き、epilogue で `SetupPre` の形へ戻す。 -/
noncomputable def fullProg (blank startSym endSym mark : Fin sc) (w : List (Fin sc)) (L : ℕ)
    (ts : Tapes sc) : List (SAct sc) :=
  let x := PrepInstances.stagePat w L
  let T1 := run blank (prologueProg blank startSym endSym L ts) ts
  let decActs :=
    (GSPre.decProg blank endSym mark 8 x.length (x.length + 1) (prj T1)).map liftAct
  let T2 := run blank decActs T1
  let s := (PrepInstances.rawRes w L).1
  prologueProg blank startSym endSym L ts ++ decActs ++ epilogueProg blank mark L s T2

/-- **主定理**：`PrepPre` から `SetupPre` を、`prepRes` が与える正規化済み三つ組で作る。
`decompose2_on_tapes` を実際に呼ぶために必要な `endSym ∉ x` は、ここでは仮定として
外から受け取る（`StageTapes.PrepOnTapes.post` にはこの仮定が現れないため、
これをそのまま `PrepOnTapes` のインスタンスへは接続できない。本ファイル末尾の
コメントを参照）。 -/
theorem prepPre_to_setupPre (hmb : mark ≠ blank)
    (hend : endSym ∉ PrepInstances.stagePat w L)
    (hpre : StageTapes.PrepPre blank mark L w Text ts) :
    SetupPre blank mark (PrepInstances.prepRes w L).1 L (PrepInstances.prepRes w L).2.1
        (PrepInstances.prepRes w L).2.2 w Text
      (run blank (fullProg blank startSym endSym mark w L ts) ts) := by
  set x := PrepInstances.stagePat w L with hx
  have hpos := hpre.hpos
  have hle := hpre.hle
  have hxlen : x.length = L := PrepInstances.stagePat_length hle
  have hcut : (PrepInstances.rawRes w L).1 < L := PrepInstances.prep_cut_lt hpos hle
  -- prologue
  obtain ⟨hEncI, hT1T, hT1X2, hT1In⟩ := prologue_spec (blank := blank) (startSym := startSym)
    (endSym := endSym) (mark := mark) (L := L) (w := w) (Text := Text) (S := ts) hpre
  set T1 := run blank (prologueProg blank startSym endSym L ts) ts with hT1
  -- decompose2_on_tapes（`liftAct` で 12 本テープへ埋め込む）
  have hEncI' : GSPre.Enc blank startSym endSym mark x 0 0 ⟨0, 0, 0, 0, 0, 0, 0⟩ (prj T1) := by
    rw [hx]; exact hEncI
  obtain ⟨_, a, b, D, Q, E, hEncO⟩ := GSPre.decompose2_on_tapes (blank := blank)
    (startSym := startSym) (endSym := endSym) (mark := mark) (x := x) (k := 8)
    (by omega) hend hmb (prj T1) hEncI'
  set decActs := (GSPre.decProg blank endSym mark 8 x.length (x.length + 1) (prj T1)).map liftAct
    with hdecActs
  set T2 := run blank decActs T1 with hT2
  have hprjT2 : prj T2 = GSPre.applyActs blank
      (GSPre.decProg blank endSym mark 8 x.length (x.length + 1) (prj T1)) (prj T1) := by
    rw [hT2, hdecActs, prj_run]
  have hEncO' : GSPre.Enc blank startSym endSym mark x a b
      ⟨D, Q, E, (decompose2 x 8).2.1, 0, (decompose2 x 8).1, (decompose2 x 8).2.2⟩ (prj T2) := by
    rw [hprjT2]; exact hEncO
  have hT2C1 : Tape.CounterView' blank mark (T2 sC1) (decompose2 x 8).2.1 := hEncO'.cp
  have hT2Rp : Tape.CounterView' blank mark (T2 sRp) (decompose2 x 8).2.2 := hEncO'.cr
  have hT2Cs : Tape.CounterView' blank mark (T2 sCs) (decompose2 x 8).1 := hEncO'.cs
  have hT2other : ∀ j : Fin 12, j ≠ sV1 → j ≠ sV2 → j ≠ sCd → j ≠ sCq → j ≠ sCe → j ≠ sC1 →
      j ≠ sCf → j ≠ sCs → j ≠ sRp → T2 j = T1 j := by
    intro j h1 h2 h3 h4 h5 h6 h7 h8 h9
    rw [hT2, hdecActs]; exact run_liftActs_other blank _ T1 j h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hT2T : T2 sT = ts sT := by
    rw [hT2other sT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]; exact hT1T
  have hT2X2 : T2 sX2 = ts sX2 := by
    rw [hT2other sX2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]; exact hT1X2
  have hT2In' : T2 sIn = T1 sIn := by
    rw [hT2other sIn (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
  -- epilogue
  set s := (PrepInstances.rawRes w L).1 with hs
  have hs_eq : s = (decompose2 x 8).1 := by rw [hs, PrepInstances.rawRes]
  have hT2C1' : Tape.CounterView' blank mark (T2 sC1) (decompose2 x 8).2.1 := hT2C1
  obtain ⟨eC1, eRp, eC2, eAp, eAn, eRn, eP, eU, eT, eX2, eIn, eCs⟩ :=
    epilogue_spec (blank := blank) (mark := mark) (L := L) (s := s) (ts := T2)
      (decompose2 x 8).2.1 (decompose2 x 8).2.2 hT2C1' hT2Rp
  set T3 := run blank (epilogueProg blank mark L s T2) T2 with hT3
  have hrunFull : run blank (fullProg blank startSym endSym mark w L ts) ts = T3 := by
    show run blank
        (prologueProg blank startSym endSym L ts ++ decActs ++ epilogueProg blank mark L s T2) ts
        = T3
    rw [run_append, run_append, ← hT1, ← hT2, ← hT3]
  -- 各成分の照合
  have hrawEq : PrepInstances.rawRes w L = decompose2 x 8 := by rw [PrepInstances.rawRes, hx]
  have hpr : PrepInstances.prepRes w L
      = ((decompose2 x 8).1, effPeriod (x.drop (decompose2 x 8).1) (decompose2 x 8).2.1,
          effReach (decompose2 x 8).2.1 (decompose2 x 8).2.2) := by
    rw [PrepInstances.prepRes_eq, hrawEq, hx]
  rw [hrunFull]
  refine
    { hpos := hpos
      hle := hle
      hcut := ?_
      inb := ?_
      emptyU := eU
      emptyP := eP
      txt := ?_
      txt2 := ?_
      cs := ?_
      c1 := ?_
      c2 := eC2
      ap := eAp
      an := eAn
      rp := ?_
      rn := eRn }
  · show (PrepInstances.prepRes w L).1 < L
    rw [hpr]; exact hcut
  · rw [eIn, hT2In']; exact hT1In
  · rw [eT, hT2T]; exact hpre.txt
  · rw [eX2, hT2X2]; exact hpre.txt2
  · show Tape.CounterView' blank mark (T3 sCs) (PrepInstances.prepRes w L).1
    rw [eCs, hpr]; exact hT2Cs
  · show Tape.CounterView' blank mark (T3 sC1) (PrepInstances.prepRes w L).2.1
    rw [hpr, effPeriod]
    have hvlen : (x.drop (decompose2 x 8).1).length = L - (decompose2 x 8).1 := by
      rw [List.length_drop, hxlen]
    rw [hvlen, ← hs_eq]; exact eC1
  · show Tape.CounterView' blank mark (T3 sRp) (PrepInstances.prepRes w L).2.2
    rw [hpr, effReach]; exact eRp

end Full

/-!
## 4. 到達点と `prepInstance` を阻む本質的なギャップ

**完成した部分（`sorry` なし、`#print axioms` は `propext` / `Classical.choice` /
`Quot.sound` のみ）：**

1. `liftAct` / `prj` / `prj_run` / `run_liftActs_other` — 9↔12 本の埋め込みと模倣補題。
2. `width_*_applyAct(s)_le`（9 成分すべて）— `ClearAny.width_step` の `GSPre.Act` 版。
3. `prologueProg` / `prologue_spec` — `PrepPre` から `GSPre.Enc … x 0 0 ⟨0,…,0⟩` を作る
   （`x = (w.take L).reverse`）。長さちょうど `6 * L + 5`。
4. `epilogueProg` / `epilogue_spec` — `decompose2_on_tapes` の終状態（生の `p₁`, `r`）から、
   `effPeriod`/`effReach` の正規化（`p₁ = 0` の退化ケースを含む）・4 本のカウンタの掃除・
   `sP`/`sU` の掃除を行う。正規化は **確率的なオラクル判定を要らない**：`epilogueProg` は
   `Tapes sc` を引数に取る関数なので、分岐 `if cval (ts sC1) = 0 then … else …` を
   定義の時点で（実行列を作る「地の Lean」で）評価でき、テープ上に probe 動作を
   物理的に置く必要がない。
5. `fullProg` / **`prepPre_to_setupPre`** — `prologueProg ++ decProg.map liftAct ++
   epilogueProg` を実行すると、`PrepPre` から `PrepInstances.prepRes` が与える
   正規化済み三つ組で `SetupPre` が成り立つことを完全に証明した。ただし
   `mark ≠ blank` と **`endSym ∉ (w.take L).reverse`** を仮定として受け取る。

**`prepInstance : StageTapes.PrepOnTapes sc blank mark` を作れない理由（本質的なギャップ）：**

`StageTapes.PrepOnTapes` の `post` フィールドは

```
post : ∀ (w Text : List (Fin sc)) (L : ℕ) (ts : Tapes sc),
  PrepPre blank mark L w Text ts → (res w L).1 < L →
  SetupPre blank mark (res w L).1 L (res w L).2.1 (res w L).2.2 w Text
    (run blank (prog (w.take L) L ts) ts)
```

であり、**`w` の中身（記号）には一切制約がない**。ところが `GSPre.decompose2_on_tapes`
（`fullProg` が内部で唯一呼んでいる、分解を実際にテープ上で行う定理）は

```
theorem decompose2_on_tapes (hk : 3 ≤ k) (hend : endSym ∉ x) (hmark : mark ≠ blank) …
```

という形で `hend : endSym ∉ x` を**必須の仮定**として要求する（`V2` の走査で
`endSym` を「パターンの終わりを示す番人」として読み分けるため、`x` の中に
本物のデータとして `endSym` が現れると壊れる）。`x = (w.take L).reverse` なので、
これは `endSym ∉ w.take L` と同値。

`PrepPre`/`post` の型には、この `endSym ∉ w` に相当する仮定が **一切現れない**。
一方で、この仮定は既に隣接ファイルで実際に使われている：`StageTapes.stage_tapes_spec'`
自身が `hend : endSym ∉ w` を明示的な引数として持つ
（`StageTapes.lean:727` 付近）。つまり `PrepOnTapes` を実際に呼び出す上位の定理は
`endSym ∉ w` を知っているのに、`PrepOnTapes.post` の型そのものにはそれを渡す経路が
ない。したがって：

* `prepInstance : StageTapes.PrepOnTapes sc blank mark` は、**`PrepOnTapes` の定義を
  変更せずには構成できない**（`post` が今のままでは、`w` にたまたま `endSym` が
  含まれる入力に対して偽の主張になってしまうため）。
* 修正の方向性は 2 つ考えられる（どちらも本ファイルの範囲外・`StageTapes.lean` の
  変更を要する）：
  (a) `PrepOnTapes.post`（および必要なら `PrepPre`）に `endSym ∉ w` を仮定として
      追加する。`stage_tapes_spec'` は既にこの仮定を持っているので、呼び出し側の
      変更は恐らく小さい。
  (b) `PrepOnTapes` を「`hend` を追加引数に取る」形へ一般化する。

**本ファイルの成果**：上記の型の変更をしなくても証明できる部分（`prepPre_to_setupPre`）は
`hend`/`hmb` を明示的な仮定として受け取る形で **完全に**証明済みである。`PrepOnTapes.post`
の型が `endSym ∉ w` を持てるようになった時点で、`prepInstance` の `post` フィールドは
`prepPre_to_setupPre`（と `PrepInstances.prep_res_eq5` / `prep_prog_len_le` による
`len_le`）をほぼそのまま繋ぐだけで完成するはずである。

`len_le`（`Cp`/`Dp` の具体形）はこのギャップとは独立に導出可能で、
`PrepInstances.prep_prog_len_le`（`hsum` 付きの線形上界）＋ `prologueProg_length`
（ちょうど `6 * L + 5`）＋ epilogue の `O(L)` 上界（`incLoop` は `L - s + 1 ≤ L + 1`、
4 本のカウンタの掃除は `width_*_applyActs_le` で `decProg` の長さに、`sP`/`sU` の掃除は
`GSPre.Enc.v1`/`.v2` の `SeqView` から幅がつねに `x.length + 1 = L + 1`
であることに帰着できる）を合算すれば得られるが、時間の都合上、数値定数の具体的な
`omega` 詰めまでは本ファイルには含めていない。
-/

end PrepInstance
end PalPeg
