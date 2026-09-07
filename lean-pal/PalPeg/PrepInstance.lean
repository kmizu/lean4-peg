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

`epilogue` と `prepPre_to_setupPre`（`PrepOnTapes.post` に相当する内容）は完成した
（`## 3h`, `## 3i`）。`StageTapes.PrepOnTapes` に `forb` パラメータを追加して
`hend`（`endSym ∉ w`）のギャップも解消した。残るのは `prepInstance` 本体の
`len_le` フィールドのみで、これは本ファイルの範囲では埋められない **`PrepOnTapes` の
型そのものの追加のギャップ**（`len_le` が `ts` に一切の前提を課さないため、
`decProg` の実際の内容依存コストを抑えられない）が原因である。詳細は本ファイル末尾の
「## 4. 到達点と `prepInstance` を阻む本質的なギャップ」を参照。
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

/-! ## 3g2. 値／既知内容量で長さが抑えられるクリア

`## 3f`/`## 3g` の `ClearAny` 版クリアは **テープの幅**（左右文脈の長さの和）で
コストを見積もるが、`PrepPre`/`Enc` が与える `StackView`/`SeqView`/`CounterView'` は
右側の余白の**長さを一切固定しない**（`Blanks blank t` の `t` は存在量化されるだけ）ので、
「テープの幅は `L` で抑えられる」という主張は `PrepPre` だけからは出てこない
（前処理段の入口ですでに余白が任意に長いかもしれない）。

`len_le` を成立させるには、**幅ではなく「既知の値」または「既知の内容量」**でコストを
測るクリア手順が要る：

* カウンタ（`sC2`/`sAp`/`sAn`/`sRp`）：`decompose2_on_tapes` の `Enc` はどれも
  **`0` から出発**するので（`Enc … 0 0 ⟨0,…,0⟩ …`）、その値は `decProg` の長さ以下
  （`leftlen_*_applyActs_le`、`ClearAny.width_step` の `left.length` 版）。
  値が分かっていれば、`decActs`（`Tape.counter'_dec`）を値の回数だけ回すだけで `0` に
  戻せる。これは**現在の値**にしかコストが依存しない。
* スタック（`sP`/`sU`）：`Enc` の `v1`/`v2` は `SeqView blank _ (pword …) (a+1)` の形。
  ヘッド位置 `a`（`≤ x.length`）と語長 `pword.length`（`= x.length + 2`）は
  どちらも `L` で抑えられる。**左に `a + 1` 歩、右に「残りの本物の内容」ぶん、
  もう一度左に同じ歩数**という 3 段の掃き（`ClearAny.clearAny` と同じ構造）だが、
  右側の掃きは `pword` の**既知の残り部分だけ**を通過し、その先の未知の余白 `t`
  （既にすべて空白）へは踏み込まない（`rightSweep_prefix`）。 -/

section ContentBoundedClear

open PalPeg.Tape

/-- 1 動作で `left.length` は高々 1 しか増えない（`ClearAny.width_step` の
`left.length` だけを見る版：右文脈の長さに触れないので、右の余白が
どれだけ長くても成り立つ）。 -/
theorem left_length_step_le (blank : Fin sc) (tp : TapeConfiguration sc) (a : Fin sc)
    (m : Move) : (Tape.step blank tp a m).left.length ≤ tp.left.length + 1 := by
  cases m with
  | stay => simp [Tape.step_stay]
  | right => simp [Tape.step_right]
  | left =>
    cases hl : tp.left with
    | nil => rw [Tape.step_left_of_left_nil hl]; simp
    | cons n l => rw [Tape.step_left_of_left_cons hl]; simp only [List.length_cons]; omega

/-- 右へ「空白を書きながら」`realPart.length + 1` 歩：`realPart` を消費しつくすと、
その先はすでに全部空白の `t` なので、`t` の中身や長さを知らなくても結果は
`StackView` になり得る形（左に積み上がるのは空白の列、右は `t.tail`）。
`ClearAny.rightSweep_core` の「既知の接頭辞だけ」版。 -/
theorem rightSweep_prefix (blank : Fin sc) :
    ∀ (realPart : List (Fin sc)) (l : List (Fin sc)) (f : Fin sc) (t : List (Fin sc)),
      Blanks blank t →
      GSTapes.runProg blank (⟨l, f, realPart ++ t⟩ : TapeConfiguration sc)
          (ClearAny.rightBlankProg blank (realPart.length + 1))
        = ⟨List.replicate (realPart.length + 1) blank ++ l, blank, t.tail⟩ := by
  intro realPart
  induction realPart with
  | nil =>
    intro l f t ht
    show GSTapes.runProg blank (⟨l, f, t⟩ : TapeConfiguration sc)
        (ClearAny.rightBlankProg blank 1) = _
    simp only [ClearAny.rightBlankProg, GSTapes.runProg_cons, GSTapes.runProg_nil]
    rw [step_right (blank := blank) (tp := (⟨l, f, t⟩ : TapeConfiguration sc)) blank]
    show (⟨blank :: l, t.headD blank, t.tail⟩ : TapeConfiguration sc)
        = ⟨List.replicate 1 blank ++ l, blank, t.tail⟩
    rw [ht.headD]
    simp
  | cons x xs ih =>
    intro l f t ht
    show GSTapes.runProg blank (⟨l, f, x :: xs ++ t⟩ : TapeConfiguration sc)
        (ClearAny.rightBlankProg blank (xs.length + 1 + 1)) = _
    rw [show xs.length + 1 + 1 = (xs.length + 1) + 1 from rfl, ClearAny.rightBlankProg,
      GSTapes.runProg_cons]
    rw [step_right (blank := blank) (tp := (⟨l, f, x :: xs ++ t⟩ : TapeConfiguration sc)) blank]
    simp only [List.headD_cons, List.tail_cons, List.cons_append]
    rw [ih (blank :: l) x t ht]
    simp only [List.length_cons]
    congr 1
    rw [show (List.replicate (xs.length + 1 + 1) blank) =
        List.replicate (xs.length + 1) blank ++ [blank] from by
          rw [← List.replicate_succ']]
    simp [List.append_assoc]

/-! ### 値で測るカウンタのクリア（`decActs` の繰り返し） -/

/-- `i` を `n` 回デクリメント。 -/
def decLoop (blank : Fin sc) (i : Fin 12) : ℕ → List (SAct sc)
  | 0 => []
  | n + 1 => decActs blank i ++ decLoop blank i n

@[simp] theorem decLoop_length (blank : Fin sc) (i : Fin 12) (n : ℕ) :
    (decLoop (sc := sc) blank i n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [decLoop, decActs, ih]; omega

theorem decLoop_untouched (blank : Fin sc) {i j : Fin 12} (h : j ≠ i) :
    ∀ (n : ℕ) (S : Tapes sc), run blank (decLoop blank i n) S j = S j := by
  intro n
  induction n with
  | zero => intro S; rfl
  | succ n ih =>
    intro S
    rw [decLoop, run_append, ih]
    show applyS blank (applyS blank S (SAct.put i blank .left)) (SAct.put i blank .stay) j = S j
    rw [applyS_ne blank _ (SAct.put i blank .stay) h,
      applyS_ne blank _ (SAct.put i blank .left) h]

theorem decLoop_spec (blank mark : Fin sc) (i : Fin 12) :
    ∀ (n : ℕ) (S : Tapes sc) (m0 : ℕ), Tape.CounterView' blank mark (S i) (m0 + n) →
      Tape.CounterView' blank mark (run blank (decLoop blank i n) S i) m0 := by
  intro n
  induction n with
  | zero => intro S m0 h; simpa [decLoop] using h
  | succ n ih =>
    intro S m0 h
    rw [decLoop, run_append]
    have hstep : run blank (decActs blank i) S i
        = Tape.step blank (Tape.step blank (S i) blank .left) blank .stay := by
      show applyS blank (applyS blank S (SAct.put i blank .left)) (SAct.put i blank .stay) i = _
      rw [applyS_put_self, applyS_put_self]
    have h2 : Tape.CounterView' blank mark (run blank (decActs blank i) S i) (m0 + n) := by
      rw [hstep]
      exact Tape.counter'_dec (by rw [show m0 + n + 1 = m0 + (n + 1) from by omega]; exact h)
    exact ih (run blank (decActs blank i) S) m0 h2

/-! ### 既知の内容量で測るスタック（`SeqView`）のクリア -/

/-- `SeqView blank (S i) w p` の形（`w.length = p + 1 + q`）から、`sP`/`sU` を
`StackView blank _ []` へ戻す動作列：左へ `p + 1` 歩、右へ `p + q + 1` 歩、
また左へ `p + q + 1` 歩（`ClearAny.clearAny` と同じ 3 段構成だが、右の掃きは
`w` の残り `q` 個ぶんだけを通過するので、右文脈の未知の余白の長さに依存しない）。 -/
def clearSeqProg (blank : Fin sc) (i : Fin 12) (p q : ℕ) : List (SAct sc) :=
  embedSlot i (ClearAny.leftBlankProg blank (p + 1)) ++
    embedSlot i (ClearAny.rightBlankProg blank (p + q + 1)) ++
    embedSlot i (ClearAny.leftBlankProg blank (p + q + 1))

theorem clearSeqProg_length (blank : Fin sc) (i : Fin 12) (p q : ℕ) :
    (clearSeqProg (sc := sc) blank i p q).length = 3 * p + 2 * q + 3 := by
  simp only [clearSeqProg, List.length_append, embedSlot_length, ClearAny.leftBlankProg_length,
    ClearAny.rightBlankProg_length]
  omega

theorem clearSeqProg_other (blank : Fin sc) {i j : Fin 12} (h : j ≠ i) (p q : ℕ)
    (S : Tapes sc) : run blank (clearSeqProg blank i p q) S j = S j := by
  rw [clearSeqProg, run_append, run_append, embedSlot_other blank h, embedSlot_other blank h,
    embedSlot_other blank h]

theorem clearSeqProg_spec (blank : Fin sc) (i : Fin 12) (p q : ℕ) (S : Tapes sc)
    (w : List (Fin sc)) (hw : Tape.SeqView blank (S i) w p) (hq : q = w.length - p - 1) :
    Tape.StackView blank (run blank (clearSeqProg blank i p q) S i) [] := by
  obtain ⟨t, hrt, hbt⟩ := hw.right_eq
  have hple : p ≤ w.length := hw.lt.le
  have hlen1 : ((w.take p).reverse).length = p := by
    rw [List.length_reverse, List.length_take]; omega
  have hqeq : (List.replicate p blank ++ w.drop (p + 1)).length = p + q := by
    rw [List.length_append, List.length_replicate, List.length_drop]; omega
  -- フェーズ 1：左端へ。
  obtain ⟨S1, hS1⟩ : ∃ T,
      run blank (embedSlot i (ClearAny.leftBlankProg blank (p + 1))) S = T := ⟨_, rfl⟩
  have hS1i : S1 i = ⟨[], blank, List.replicate p blank ++ (S i).right⟩ := by
    rw [← hS1, embedSlot_run]
    have h1 := ClearAny.leftSweep_core blank ((w.take p).reverse) (S i).focus (S i).right
    rw [hlen1, ← hw.left_eq] at h1
    exact h1
  have hS1other : ∀ k : Fin 12, k ≠ i → S1 k = S k := by
    intro k hk; rw [← hS1]; exact embedSlot_other blank hk _ S
  -- フェーズ 2：右へ、`w` の残りぶんだけ。
  obtain ⟨S2, hS2⟩ : ∃ T,
      run blank (embedSlot i (ClearAny.rightBlankProg blank (p + q + 1))) S1 = T := ⟨_, rfl⟩
  have hS2i : S2 i = ⟨List.replicate (p + q + 1) blank, blank, t.tail⟩ := by
    rw [← hS2, embedSlot_run, hS1i, hrt, ← List.append_assoc]
    have h2 := rightSweep_prefix blank (List.replicate p blank ++ w.drop (p + 1)) [] blank t hbt
    rw [hqeq] at h2
    simpa using h2
  have hS2other : ∀ k : Fin 12, k ≠ i → S2 k = S1 k := by
    intro k hk; rw [← hS2]; exact embedSlot_other blank hk _ S1
  -- フェーズ 3：左端へ戻る（既に全部空白）。
  obtain ⟨S3, hS3⟩ : ∃ T,
      run blank (embedSlot i (ClearAny.leftBlankProg blank (p + q + 1))) S2 = T := ⟨_, rfl⟩
  have hblanks : Blanks blank (List.replicate (p + q + 1) blank) := Tape.blanks_replicate blank _
  have hS3i : S3 i = ⟨[], blank, List.replicate (p + q + 1) blank ++ t.tail⟩ := by
    rw [← hS3, embedSlot_run, hS2i]
    have h3 := ClearAny.leftSweep_blank blank (List.replicate (p + q + 1) blank) hblanks t.tail
    rwa [List.length_replicate] at h3
  have hrunFull : run blank (clearSeqProg blank i p q) S i = S3 i := by
    show run blank
        (embedSlot i (ClearAny.leftBlankProg blank (p + 1)) ++
            embedSlot i (ClearAny.rightBlankProg blank (p + q + 1)) ++
            embedSlot i (ClearAny.leftBlankProg blank (p + q + 1))) S i = S3 i
    rw [run_append, run_append, hS1, hS2, hS3]
  rw [hrunFull, hS3i]
  refine ⟨rfl, rfl, ?_⟩
  intro s hs
  rcases List.mem_append.1 hs with h | h
  · exact List.eq_of_mem_replicate h
  · exact hbt _ (List.mem_of_mem_tail h)

/-! ### 値が動作数で抑えられること（`cval` は `Enc` の初期値 `0` から高々 `1`／動作） -/

theorem leftlen_Cd_applyAct_le (blank : Fin sc) (a : GSPre.Act sc) (ts : GSPre.Tapes sc) :
    (GSPre.applyAct blank ts a).Cd.left.length ≤ ts.Cd.left.length + 1 := by
  cases a with
  | Cd b m => exact left_length_step_le blank ts.Cd b m
  | _ => simp [GSPre.applyAct]

theorem leftlen_Cd_applyActs_le (blank : Fin sc) (l : List (GSPre.Act sc)) (ts : GSPre.Tapes sc) :
    (GSPre.applyActs blank l ts).Cd.left.length ≤ ts.Cd.left.length + l.length := by
  induction l generalizing ts with
  | nil => simp [GSPre.applyActs]
  | cons a l ih =>
      have h1 := leftlen_Cd_applyAct_le blank a ts
      have h2 := ih (GSPre.applyAct blank ts a)
      simp only [GSPre.applyActs_cons, List.length_cons] at *
      omega

theorem leftlen_Cq_applyAct_le (blank : Fin sc) (a : GSPre.Act sc) (ts : GSPre.Tapes sc) :
    (GSPre.applyAct blank ts a).Cq.left.length ≤ ts.Cq.left.length + 1 := by
  cases a with
  | Cq b m => exact left_length_step_le blank ts.Cq b m
  | _ => simp [GSPre.applyAct]

theorem leftlen_Cq_applyActs_le (blank : Fin sc) (l : List (GSPre.Act sc)) (ts : GSPre.Tapes sc) :
    (GSPre.applyActs blank l ts).Cq.left.length ≤ ts.Cq.left.length + l.length := by
  induction l generalizing ts with
  | nil => simp [GSPre.applyActs]
  | cons a l ih =>
      have h1 := leftlen_Cq_applyAct_le blank a ts
      have h2 := ih (GSPre.applyAct blank ts a)
      simp only [GSPre.applyActs_cons, List.length_cons] at *
      omega

theorem leftlen_Ce_applyAct_le (blank : Fin sc) (a : GSPre.Act sc) (ts : GSPre.Tapes sc) :
    (GSPre.applyAct blank ts a).Ce.left.length ≤ ts.Ce.left.length + 1 := by
  cases a with
  | Ce b m => exact left_length_step_le blank ts.Ce b m
  | _ => simp [GSPre.applyAct]

theorem leftlen_Ce_applyActs_le (blank : Fin sc) (l : List (GSPre.Act sc)) (ts : GSPre.Tapes sc) :
    (GSPre.applyActs blank l ts).Ce.left.length ≤ ts.Ce.left.length + l.length := by
  induction l generalizing ts with
  | nil => simp [GSPre.applyActs]
  | cons a l ih =>
      have h1 := leftlen_Ce_applyAct_le blank a ts
      have h2 := ih (GSPre.applyAct blank ts a)
      simp only [GSPre.applyActs_cons, List.length_cons] at *
      omega

theorem leftlen_Cr_applyAct_le (blank : Fin sc) (a : GSPre.Act sc) (ts : GSPre.Tapes sc) :
    (GSPre.applyAct blank ts a).Cr.left.length ≤ ts.Cr.left.length + 1 := by
  cases a with
  | Cr b m => exact left_length_step_le blank ts.Cr b m
  | _ => simp [GSPre.applyAct]

theorem leftlen_Cr_applyActs_le (blank : Fin sc) (l : List (GSPre.Act sc)) (ts : GSPre.Tapes sc) :
    (GSPre.applyActs blank l ts).Cr.left.length ≤ ts.Cr.left.length + l.length := by
  induction l generalizing ts with
  | nil => simp [GSPre.applyActs]
  | cons a l ih =>
      have h1 := leftlen_Cr_applyAct_le blank a ts
      have h2 := ih (GSPre.applyAct blank ts a)
      simp only [GSPre.applyActs_cons, List.length_cons] at *
      omega

end ContentBoundedClear

/-! ## 3h. epilogue：`decProg` の終状態から `SetupPre` を作る -/

section Epilogue

variable {blank startSym endSym mark : Fin sc} {L s : ℕ} {ts : Tapes sc}

/-- **epilogue プログラム**：`decompose2_on_tapes` の終状態から `SetupPre` の形へ戻す。
`sC2`（`Cd`）・`sAp`（`Cq`）・`sAn`（`Ce`）は**現在の値**を `decLoop`（`Tape.counter'_dec` の
繰り返し）でちょうどその値ぶんデクリメントして `0` にする（`ClearAny` の形非依存クリアと
違い、コストは「値」に比例するだけで、右文脈の未知の余白の長さには依存しない）。
`sRn`（`Cf`）は `Enc` の時点で既に `0` なので触らない。`sP`（`V1`）・`sU`（`V2`）は
`clearSeqProg`（`## 3g2`）でスタック `[]` に掃除する：これも `pword` の**既知の長さ**
ぶんしか動かない。`sC1`（`Cp`、生の周期 `p₁`）と `sRp`（`Cr`、生の到達域 `r`）だけは
`effPeriod`/`effReach` の正規化が要る：生の `p₁ = 0`（退化ケース）なら `sC1` を
`L - s + 1` へ増分し、`sRp` を（現在の値ぶんデクリメントして）`0` にする。
`p₁ ≠ 0` ならどちらも触らない。 -/
noncomputable def epilogueProg (blank _mark : Fin sc) (L s : ℕ) (ts : Tapes sc) : List (SAct sc) :=
  seqP blank (fun _ => if cval (ts sC1) = 0 then incLoop blank sC1 (L - s + 1) else [])
    (seqP blank (fun _ => decLoop blank sC2 (cval (ts sC2)))
      (seqP blank (fun _ => decLoop blank sAp (cval (ts sAp)))
        (seqP blank (fun _ => decLoop blank sAn (cval (ts sAn)))
          (seqP blank
            (fun _ => if cval (ts sC1) = 0 then decLoop blank sRp (cval (ts sRp)) else [])
            (seqP blank
              (fun _ => clearSeqProg blank sP (ts sP).left.length
                (L + 1 - (ts sP).left.length))
              (fun _ => clearSeqProg blank sU (ts sU).left.length
                (L + 1 - (ts sU).left.length))))))) ts

/-- **epilogue の正しさと長さ**：`decompose2_on_tapes` の終状態（生の周期 `p1raw`、
生の到達域 `r`、`sC2/sAp/sAn` の値 `D`/`Q`/`E`、`sP`/`sU` が長さ `L + 2` の語 `wp`/`wu`
上の `SeqView`（ヘッド `pP`/`pU`）であること）から出発すると、`sC1`/`sRp` は
`effPeriod`/`effReach` が要求する正規化済みの値になり、`sC2/sAp/sAn/sRn` は `0`、
`sP`/`sU` は空スタックになる。`sT`/`sX2`/`sIn`/`sCs` は不変。動作数は
`D`, `Q`, `E`, `r`, `L` の 1 次式で抑えられる。 -/
theorem epilogue_spec (p1raw r D Q E pP pU : ℕ) (wp wu : List (Fin sc))
    (hC1 : Tape.CounterView' blank mark (ts sC1) p1raw)
    (hRp : Tape.CounterView' blank mark (ts sRp) r)
    (hC2 : Tape.CounterView' blank mark (ts sC2) D)
    (hAp : Tape.CounterView' blank mark (ts sAp) Q)
    (hAn : Tape.CounterView' blank mark (ts sAn) E)
    (hRn : Tape.CounterView' blank mark (ts sRn) 0)
    (hVP : Tape.SeqView blank (ts sP) wp pP) (hwp : wp.length = L + 2)
    (hVU : Tape.SeqView blank (ts sU) wu pU) (hwu : wu.length = L + 2) :
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
      ∧ run blank (epilogueProg blank mark L s ts) ts sCs = ts sCs
      ∧ (epilogueProg blank mark L s ts).length
          ≤ (L + 1) + 2 * D + 2 * Q + 2 * E + 2 * r
            + (3 * pP + 2 * (L + 1 - pP) + 3) + (3 * pU + 2 * (L + 1 - pU) + 3) := by
  have hcv : cval (ts sC1) = p1raw := cval_eq hC1
  have hcvC2 : cval (ts sC2) = D := cval_eq hC2
  have hcvAp : cval (ts sAp) = Q := cval_eq hAp
  have hcvAn : cval (ts sAn) = E := cval_eq hAn
  have hcvRp : cval (ts sRp) = r := cval_eq hRp
  have hpPeq : (ts sP).left.length = pP := by
    rw [hVP.left_eq, List.length_reverse, List.length_take]
    have := hVP.lt; omega
  have hpUeq : (ts sU).left.length = pU := by
    rw [hVU.left_eq, List.length_reverse, List.length_take]
    have := hVU.lt; omega
  -- フェーズ 0：`sC1` の正規化（`p1raw = 0` のときだけ）。
  obtain ⟨S₀, hS0⟩ : ∃ T,
      run blank (if cval (ts sC1) = 0 then incLoop blank sC1 (L - s + 1) else []) ts = T :=
    ⟨_, rfl⟩
  have hS0len : (if cval (ts sC1) = 0 then incLoop blank sC1 (L - s + 1) else
      ([] : List (SAct sc))).length ≤ L + 1 := by
    split_ifs with h <;> simp
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
  -- フェーズ 1–3：`sC2`, `sAp`, `sAn` をデクリメントで掃除。
  obtain ⟨S₁, hS1⟩ : ∃ T, run blank (decLoop blank sC2 (cval (ts sC2))) S₀ = T := ⟨_, rfl⟩
  obtain ⟨S₂, hS2⟩ : ∃ T, run blank (decLoop blank sAp (cval (ts sAp))) S₁ = T := ⟨_, rfl⟩
  obtain ⟨S₃, hS3⟩ : ∃ T, run blank (decLoop blank sAn (cval (ts sAn))) S₂ = T := ⟨_, rfl⟩
  have hS0C2 : Tape.CounterView' blank mark (S₀ sC2) D := by
    rw [hS0other sC2 (by decide)]; exact hC2
  have hS1C2 : Tape.CounterView' blank mark (S₁ sC2) 0 := by
    rw [← hS1]
    have := decLoop_spec blank mark sC2 (cval (ts sC2)) S₀ 0 (by rw [hcvC2]; simpa using hS0C2)
    simpa using this
  have hS1other : ∀ j : Fin 12, j ≠ sC2 → S₁ j = S₀ j := by
    intro j hj; rw [← hS1]; exact decLoop_untouched blank hj _ S₀
  have hS1Ap : Tape.CounterView' blank mark (S₁ sAp) Q := by
    rw [hS1other sAp (by decide), hS0other sAp (by decide)]; exact hAp
  have hS2Ap : Tape.CounterView' blank mark (S₂ sAp) 0 := by
    rw [← hS2]
    have := decLoop_spec blank mark sAp (cval (ts sAp)) S₁ 0 (by rw [hcvAp]; simpa using hS1Ap)
    simpa using this
  have hS2other : ∀ j : Fin 12, j ≠ sAp → S₂ j = S₁ j := by
    intro j hj; rw [← hS2]; exact decLoop_untouched blank hj _ S₁
  have hS2An : Tape.CounterView' blank mark (S₂ sAn) E := by
    rw [hS2other sAn (by decide), hS1other sAn (by decide), hS0other sAn (by decide)]
    exact hAn
  have hS3An : Tape.CounterView' blank mark (S₃ sAn) 0 := by
    rw [← hS3]
    have := decLoop_spec blank mark sAn (cval (ts sAn)) S₂ 0 (by rw [hcvAn]; simpa using hS2An)
    simpa using this
  have hS3other : ∀ j : Fin 12, j ≠ sAn → S₃ j = S₂ j := by
    intro j hj; rw [← hS3]; exact decLoop_untouched blank hj _ S₂
  have hS3Rn : Tape.CounterView' blank mark (S₃ sRn) 0 := by
    rw [hS3other sRn (by decide), hS2other sRn (by decide), hS1other sRn (by decide),
      hS0other sRn (by decide)]
    exact hRn
  have hchain3 : ∀ j : Fin 12, j ≠ sC2 → j ≠ sAp → j ≠ sAn → S₃ j = S₀ j := by
    intro j h1 h2 h3
    rw [hS3other j h3, hS2other j h2, hS1other j h1]
  -- フェーズ 4：`sRp` の正規化（`p1raw = 0` のときだけデクリメントで `0` に）。
  obtain ⟨S₄, hS4⟩ : ∃ T,
      run blank (if cval (ts sC1) = 0 then decLoop blank sRp (cval (ts sRp))
        else ([] : List (SAct sc))) S₃ = T := ⟨_, rfl⟩
  have hS3Rp : Tape.CounterView' blank mark (S₃ sRp) r := by
    rw [hchain3 sRp (by decide) (by decide) (by decide), hS0other sRp (by decide)]
    exact hRp
  have hS4Rp : Tape.CounterView' blank mark (S₄ sRp) (if p1raw = 0 then 0 else r) := by
    rw [← hS4, hcv]
    split_ifs with h
    · have := decLoop_spec blank mark sRp (cval (ts sRp)) S₃ 0 (by
        rw [hcvRp]; simpa using hS3Rp)
      simpa using this
    · simpa using hS3Rp
  have hS4other : ∀ j : Fin 12, j ≠ sRp → S₄ j = S₃ j := by
    intro j hj
    rw [← hS4]
    split_ifs with h
    · exact decLoop_untouched blank hj _ S₃
    · rfl
  -- フェーズ 5–6：`sP`, `sU` を空スタックへ（`clearSeqProg`）。
  obtain ⟨S₅, hS5⟩ : ∃ T,
      run blank (clearSeqProg blank sP (ts sP).left.length (L + 1 - (ts sP).left.length)) S₄
        = T := ⟨_, rfl⟩
  obtain ⟨S₆, hS6⟩ : ∃ T,
      run blank (clearSeqProg blank sU (ts sU).left.length (L + 1 - (ts sU).left.length)) S₅
        = T := ⟨_, rfl⟩
  have hS4P : Tape.SeqView blank (S₄ sP) wp pP := by
    rw [hS4other sP (by decide), hchain3 sP (by decide) (by decide) (by decide),
      hS0other sP (by decide)]
    exact hVP
  have hS5P : Tape.StackView blank (S₅ sP) [] := by
    rw [← hS5, hpPeq]
    exact clearSeqProg_spec blank sP pP (L + 1 - pP) S₄ wp hS4P (by rw [hwp]; omega)
  have hS5other : ∀ j : Fin 12, j ≠ sP → S₅ j = S₄ j := by
    intro j hj
    rw [← hS5]
    have hj' : j ≠ sP := hj
    rw [hpPeq]
    exact clearSeqProg_other blank hj' _ _ S₄
  have hS5U : Tape.SeqView blank (S₅ sU) wu pU := by
    rw [hS5other sU (by decide), hS4other sU (by decide),
      hchain3 sU (by decide) (by decide) (by decide), hS0other sU (by decide)]
    exact hVU
  have hS6U : Tape.StackView blank (S₆ sU) [] := by
    rw [← hS6, hpUeq]
    exact clearSeqProg_spec blank sU pU (L + 1 - pU) S₅ wu hS5U (by rw [hwu]; omega)
  have hS6other : ∀ j : Fin 12, j ≠ sU → S₆ j = S₅ j := by
    intro j hj
    rw [← hS6]
    have hj' : j ≠ sU := hj
    rw [hpUeq]
    exact clearSeqProg_other blank hj' _ _ S₅
  have hS6P : Tape.StackView blank (S₆ sP) [] := by
    rw [hS6other sP (by decide)]; exact hS5P
  -- 実行結果は `S₆`。
  have hrun : run blank (epilogueProg blank mark L s ts) ts = S₆ := by
    simp only [epilogueProg, seqP_run, hS0, hS1, hS2, hS3, hS4, hS5, hS6]
  have hchain6 : ∀ j : Fin 12, j ≠ sP → j ≠ sU → j ≠ sRp → j ≠ sC2 → j ≠ sAp → j ≠ sAn →
      j ≠ sC1 → S₆ j = ts j := by
    intro j h1 h2 h3 h4 h5 h6 h7
    rw [hS6other j h2, hS5other j h1, hS4other j h3, hchain3 j h4 h5 h6, hS0other j h7]
  have hS6sC1 : S₆ sC1 = S₀ sC1 := by
    rw [hS6other sC1 (by decide), hS5other sC1 (by decide), hS4other sC1 (by decide),
      hchain3 sC1 (by decide) (by decide) (by decide)]
  have hS6sRp : S₆ sRp = S₄ sRp := by
    rw [hS6other sRp (by decide), hS5other sRp (by decide)]
  have hS6sC2 : S₆ sC2 = S₁ sC2 := by
    rw [hS6other sC2 (by decide), hS5other sC2 (by decide), hS4other sC2 (by decide),
      hS3other sC2 (by decide), hS2other sC2 (by decide)]
  have hS6sAp : S₆ sAp = S₂ sAp := by
    rw [hS6other sAp (by decide), hS5other sAp (by decide), hS4other sAp (by decide),
      hS3other sAp (by decide)]
  have hS6sAn : S₆ sAn = S₃ sAn := by
    rw [hS6other sAn (by decide), hS5other sAn (by decide), hS4other sAn (by decide)]
  have hS6sRn : S₆ sRn = S₃ sRn := by
    rw [hS6other sRn (by decide), hS5other sRn (by decide), hS4other sRn (by decide)]
  have hlenIf1 : (if cval (ts sC1) = 0 then decLoop blank sRp (cval (ts sRp))
      else ([] : List (SAct sc))).length ≤ 2 * r := by
    split_ifs with h
    · rw [decLoop_length, hcvRp]
    · simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrun, hS6sC1]; exact hS0C1
  · rw [hrun, hS6sRp]; exact hS4Rp
  · rw [hrun, hS6sC2]; exact hS1C2
  · rw [hrun, hS6sAp]; exact hS2Ap
  · rw [hrun, hS6sAn]; exact hS3An
  · rw [hrun, hS6sRn]; exact hS3Rn
  · rw [hrun]; exact hS6P
  · rw [hrun]; exact hS6U
  · rw [hrun, hchain6 sT (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
  · rw [hrun, hchain6 sX2 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
  · rw [hrun, hchain6 sIn (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
  · rw [hrun, hchain6 sCs (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
  · simp only [epilogueProg, seqP_length]
    have e2 : (decLoop (sc := sc) blank sC2 (cval (ts sC2))).length = 2 * D := by
      rw [decLoop_length, hcvC2]
    have e3 : (decLoop (sc := sc) blank sAp (cval (ts sAp))).length = 2 * Q := by
      rw [decLoop_length, hcvAp]
    have e4 : (decLoop (sc := sc) blank sAn (cval (ts sAn))).length = 2 * E := by
      rw [decLoop_length, hcvAn]
    have e6 : (clearSeqProg (sc := sc) blank sP (ts sP).left.length
        (L + 1 - (ts sP).left.length)).length = 3 * pP + 2 * (L + 1 - pP) + 3 := by
      rw [hpPeq, clearSeqProg_length]
    have e7 : (clearSeqProg (sc := sc) blank sU (ts sU).left.length
        (L + 1 - (ts sU).left.length)).length = 3 * pU + 2 * (L + 1 - pU) + 3 := by
      rw [hpUeq, clearSeqProg_length]
    omega

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
  have hpwlen : (GSPre.pword startSym endSym x).length = L + 2 := by
    rw [GSPre.pword_length, hxlen]
  have hT2vP : Tape.SeqView blank (T2 sP) (GSPre.pword startSym endSym x) (a + 1) := hEncO'.v1
  have hT2vU : Tape.SeqView blank (T2 sU) (GSPre.pword startSym endSym x) (b + 1) := hEncO'.v2
  obtain ⟨eC1, eRp, eC2, eAp, eAn, eRn, eP, eU, eT, eX2, eIn, eCs, _⟩ :=
    epilogue_spec (blank := blank) (mark := mark) (L := L) (s := s) (ts := T2)
      (decompose2 x 8).2.1 (decompose2 x 8).2.2 D Q E (a + 1) (b + 1)
      (GSPre.pword startSym endSym x) (GSPre.pword startSym endSym x)
      hT2C1' hT2Rp hEncO'.cd hEncO'.cq hEncO'.ce hEncO'.cf hT2vP hpwlen hT2vU hpwlen
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

/-- **`fullProg` の長さの 1 次上界**：`prologueProg`（`6 * L + 5`）＋ `decProg`
（`PrepInstances.prep_work_le` により `hsum` のもとで `L` の 1 次式）＋ `epilogueProg`
（`epilogue_spec` の 1 次上界；そこに現れる値 `D`, `Q`, `E`, `r` はいずれも `Enc` の
入口で `0` から出発するので `decProg` の長さ以下 —— `leftlen_C*_applyActs_le` ——、
ヘッド位置 `pP = a + 1`, `pU = b + 1` は `GSPre.pat_le` により `L + 1` 以下）を
合算したもの。 -/
theorem fullProg_length_le (C₁ : ℕ) (hmb : mark ≠ blank)
    (hend : endSym ∉ PrepInstances.stagePat w L)
    (hsum : ∀ (y : List (Fin sc)) (b s' : ℕ), stripLoop2Periods y 8 b (y.length + 1) s' ≤ C₁ * b)
    (hpre : StageTapes.PrepPre blank mark L w Text ts) :
    (fullProg blank startSym endSym mark w L ts).length
      ≤ (13 + 9 * ((19 * 8 + 85) * (34 * C₁ + 186) + (4 * 8 + 17))) * L
        + (18 + 9 * ((19 * 8 + 85) * 21 + (4 * 8 + 17))) := by
  set x := PrepInstances.stagePat w L with hx
  have hpos := hpre.hpos
  have hle := hpre.hle
  have hxlen : x.length = L := PrepInstances.stagePat_length hle
  -- prologue
  obtain ⟨hEncI, -, -, -⟩ := prologue_spec (blank := blank) (startSym := startSym)
    (endSym := endSym) (mark := mark) (L := L) (w := w) (Text := Text) (S := ts) hpre
  set T1 := run blank (prologueProg blank startSym endSym L ts) ts with hT1
  have hEncI' : GSPre.Enc blank startSym endSym mark x 0 0 ⟨0, 0, 0, 0, 0, 0, 0⟩ (prj T1) := by
    rw [hx]; exact hEncI
  have hprologueLen : (prologueProg blank startSym endSym L ts).length = 6 * L + 5 :=
    prologueProg_length hpos ts
  -- decompose2_on_tapes
  obtain ⟨hdeclen, a, b, D, Q, E, hEncO⟩ := GSPre.decompose2_on_tapes (blank := blank)
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
  have hdecActsLen : decActs.length
      = (GSPre.decProg blank endSym mark 8 x.length (x.length + 1) (prj T1)).length := by
    rw [hdecActs, List.length_map]
  -- `decompose2Work` の 1 次上界（`hsum` はすべての `x` について成り立つので、
  -- そのまま `x` に特殊化できる）。
  have hwork : decompose2Work x 8 ≤ (34 * C₁ + 186) * L + 21 :=
    PrepInstances.prep_work_le hle (fun b s => hsum x b s)
  have hM : decActs.length
      ≤ (19 * 8 + 85) * ((34 * C₁ + 186) * L + 21) + (4 * 8 + 17) * (L + 1) := by
    rw [hdecActsLen]
    have h1 : (19 * 8 + 85) * decompose2Work x 8
        ≤ (19 * 8 + 85) * ((34 * C₁ + 186) * L + 21) := Nat.mul_le_mul_left _ hwork
    have h2 : (4 * 8 + 17) * (x.length + 1) = (4 * 8 + 17) * (L + 1) := by rw [hxlen]
    omega
  -- `D`, `Q`, `E`, `r` は `decActs.length` で抑えられる（`0` から出発するため）。
  have hCdInit : (prj T1).Cd.left.length = 1 := by
    have h := hEncI'.cd
    rw [h.left_eq]; rfl
  have hCqInit : (prj T1).Cq.left.length = 1 := by
    have h := hEncI'.cq
    rw [h.left_eq]; rfl
  have hCeInit : (prj T1).Ce.left.length = 1 := by
    have h := hEncI'.ce
    rw [h.left_eq]; rfl
  have hCrInit : (prj T1).Cr.left.length = 1 := by
    have h := hEncI'.cr
    rw [h.left_eq]; rfl
  have hDbound : D ≤ decActs.length := by
    have hcv : cval (T2 sC2) = D := cval_eq hEncO'.cd
    have h1 : (prj T2).Cd.left.length
        ≤ (prj T1).Cd.left.length
          + (GSPre.decProg blank endSym mark 8 x.length (x.length + 1) (prj T1)).length := by
      rw [hprjT2]; exact leftlen_Cd_applyActs_le blank _ (prj T1)
    rw [hCdInit] at h1
    have h2 : (prj T2).Cd = T2 sC2 := rfl
    rw [h2] at h1
    unfold cval at hcv
    rw [hdecActsLen]
    omega
  have hQbound : Q ≤ decActs.length := by
    have hcv : cval (T2 sAp) = Q := cval_eq hEncO'.cq
    have h1 : (prj T2).Cq.left.length
        ≤ (prj T1).Cq.left.length
          + (GSPre.decProg blank endSym mark 8 x.length (x.length + 1) (prj T1)).length := by
      rw [hprjT2]; exact leftlen_Cq_applyActs_le blank _ (prj T1)
    rw [hCqInit] at h1
    have h2 : (prj T2).Cq = T2 sAp := rfl
    rw [h2] at h1
    unfold cval at hcv
    rw [hdecActsLen]
    omega
  have hEbound : E ≤ decActs.length := by
    have hcv : cval (T2 sAn) = E := cval_eq hEncO'.ce
    have h1 : (prj T2).Ce.left.length
        ≤ (prj T1).Ce.left.length
          + (GSPre.decProg blank endSym mark 8 x.length (x.length + 1) (prj T1)).length := by
      rw [hprjT2]; exact leftlen_Ce_applyActs_le blank _ (prj T1)
    rw [hCeInit] at h1
    have h2 : (prj T2).Ce = T2 sAn := rfl
    rw [h2] at h1
    unfold cval at hcv
    rw [hdecActsLen]
    omega
  have hrbound : (decompose2 x 8).2.2 ≤ decActs.length := by
    have hcv : cval (T2 sRp) = (decompose2 x 8).2.2 := cval_eq hEncO'.cr
    have h1 : (prj T2).Cr.left.length
        ≤ (prj T1).Cr.left.length
          + (GSPre.decProg blank endSym mark 8 x.length (x.length + 1) (prj T1)).length := by
      rw [hprjT2]; exact leftlen_Cr_applyActs_le blank _ (prj T1)
    rw [hCrInit] at h1
    have h2 : (prj T2).Cr = T2 sRp := rfl
    rw [h2] at h1
    unfold cval at hcv
    rw [hdecActsLen]
    omega
  -- `pP = a + 1`, `pU = b + 1` は `L + 1` 以下。
  have hpwlen : (GSPre.pword startSym endSym x).length = L + 2 := by
    rw [GSPre.pword_length, hxlen]
  have haLe : a ≤ x.length := GSPre.pat_le hEncO'.v1
  have hbLe : b ≤ x.length := GSPre.pat_le hEncO'.v2
  -- epilogue
  set s := (PrepInstances.rawRes w L).1 with hs
  have hT2C1' : Tape.CounterView' blank mark (T2 sC1) (decompose2 x 8).2.1 := hEncO'.cp
  have hT2Rp' : Tape.CounterView' blank mark (T2 sRp) (decompose2 x 8).2.2 := hEncO'.cr
  have hT2vP : Tape.SeqView blank (T2 sP) (GSPre.pword startSym endSym x) (a + 1) := hEncO'.v1
  have hT2vU : Tape.SeqView blank (T2 sU) (GSPre.pword startSym endSym x) (b + 1) := hEncO'.v2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, helen⟩ :=
    epilogue_spec (blank := blank) (mark := mark) (L := L) (s := s) (ts := T2)
      (decompose2 x 8).2.1 (decompose2 x 8).2.2 D Q E (a + 1) (b + 1)
      (GSPre.pword startSym endSym x) (GSPre.pword startSym endSym x)
      hT2C1' hT2Rp' hEncO'.cd hEncO'.cq hEncO'.ce hEncO'.cf hT2vP hpwlen hT2vU hpwlen
  -- 全体の組み立て。
  have hrunFull : (fullProg blank startSym endSym mark w L ts).length
      = (prologueProg blank startSym endSym L ts).length + decActs.length
        + (epilogueProg blank mark L s T2).length := by
    show (prologueProg blank startSym endSym L ts ++ decActs ++
        epilogueProg blank mark L s T2).length = _
    rw [List.length_append, List.length_append]
  rw [hrunFull, hprologueLen]
  have haL : a ≤ L := by rw [← hxlen]; exact haLe
  have hbL : b ≤ L := by rw [← hxlen]; exact hbLe
  have heq : 13 * L + 18
        + 9 * ((19 * 8 + 85) * ((34 * C₁ + 186) * L + 21) + (4 * 8 + 17) * (L + 1))
      = (13 + 9 * ((19 * 8 + 85) * (34 * C₁ + 186) + (4 * 8 + 17))) * L
        + (18 + 9 * ((19 * 8 + 85) * 21 + (4 * 8 + 17))) := by ring
  rw [← heq]
  omega

/-- `stagePat` は「もう一度 `take L` する」ことに対して不変（`w.take L` はすでに
長さ `≤ L`なので、再度 `take L` しても変わらない）。`prog` が `w.take L` を受け取る
という `PrepOnTapes` の呼び出し規約と、`fullProg` が実際には `w` を `stagePat`/`rawRes`
越しにしか使わないことを橋渡しする。 -/
theorem stagePat_take_self (w : List (Fin sc)) (L : ℕ) :
    PrepInstances.stagePat (w.take L) L = PrepInstances.stagePat w L := by
  simp [PrepInstances.stagePat, List.take_take]

theorem rawRes_take_self (w : List (Fin sc)) (L : ℕ) :
    PrepInstances.rawRes (w.take L) L = PrepInstances.rawRes w L := by
  simp only [PrepInstances.rawRes, stagePat_take_self]

theorem prepRes_take_self (w : List (Fin sc)) (L : ℕ) :
    PrepInstances.prepRes (w.take L) L = PrepInstances.prepRes w L := by
  simp only [PrepInstances.prepRes, stagePat_take_self, rawRes_take_self]

theorem fullProg_take_self (blank startSym endSym mark : Fin sc) (w : List (Fin sc)) (L : ℕ)
    (ts : Tapes sc) :
    fullProg blank startSym endSym mark (w.take L) L ts
      = fullProg blank startSym endSym mark w L ts := by
  simp only [fullProg, stagePat_take_self, rawRes_take_self]

end Full

/-! ## 3j. `prepInstance` -/

variable {blank startSym endSym mark : Fin sc}

theorem stagePat_forb_of {w : List (Fin sc)} {L : ℕ} (h : endSym ∉ w) :
    endSym ∉ PrepInstances.stagePat w L := by
  rw [PrepInstances.stagePat, List.mem_reverse]
  intro hmem
  exact h (List.mem_of_mem_take hmem)

/-- **`Cp`**：`13 + 9 * ((19 * 8 + 85) * (34 * C₁ + 186) + (4 * 8 + 17))`。 -/
def prepCp (C₁ : ℕ) : ℕ := 13 + 9 * ((19 * 8 + 85) * (34 * C₁ + 186) + (4 * 8 + 17))

/-- **`Dp`**：`18 + 9 * ((19 * 8 + 85) * 21 + (4 * 8 + 17))`（`C₁` に依存しない）。 -/
def prepDp : ℕ := 18 + 9 * ((19 * 8 + 85) * 21 + (4 * 8 + 17))

/-- **`prepInstance`**：`StageTapes.PrepOnTapes sc blank mark endSym` の具体化。
`prog` は `fullProg`（prologue ＋ `decProg` ＋ epilogue）、`res` は
`PrepInstances.prepRes`（`decompose2` の正規化済み三つ組）。`post` は
`prepPre_to_setupPre`、`len_le` は `fullProg_length_le` からそのまま従う
（`prog` の呼び出し規約 `prog (w.take L) L ts` と `fullProg` の `w` 依存性の橋渡しは
`fullProg_take_self`）。 -/
noncomputable def prepInstance (C₁ : ℕ)
    (hsum : ∀ (y : List (Fin sc)) (b s : ℕ), stripLoop2Periods y 8 b (y.length + 1) s ≤ C₁ * b)
    (hmb : mark ≠ blank) : StageTapes.PrepOnTapes sc blank mark endSym where
  prog := fun x0 L ts => fullProg blank startSym endSym mark x0 L ts
  res := PrepInstances.prepRes
  Cp := prepCp C₁
  Dp := prepDp
  len_le := by
    intro w Text L ts hpre hforb
    show (fullProg blank startSym endSym mark (w.take L) L ts).length ≤ prepCp C₁ * L + prepDp
    rw [fullProg_take_self]
    exact fullProg_length_le C₁ hmb (stagePat_forb_of hforb) hsum hpre
  post := by
    intro w Text L ts hpre hforb _hcut
    show SetupPre blank mark (PrepInstances.prepRes w L).1 L (PrepInstances.prepRes w L).2.1
        (PrepInstances.prepRes w L).2.2 w Text
        (run blank (fullProg blank startSym endSym mark (w.take L) L ts) ts)
    rw [fullProg_take_self]
    exact prepPre_to_setupPre hmb (stagePat_forb_of hforb) hpre

/-- `prepInstance` の分解は `PrepInstances.prepRes`。 -/
theorem prepInstance_res (C₁ : ℕ)
    (hsum : ∀ (y : List (Fin sc)) (b s : ℕ), stripLoop2Periods y 8 b (y.length + 1) s ≤ C₁ * b)
    (hmb : mark ≠ blank) :
    (prepInstance (blank := blank) (startSym := startSym) (endSym := endSym) (mark := mark)
        C₁ hsum hmb).res = PrepInstances.prepRes := rfl

/-!
## 4. 到達点と `prepInstance` を阻む本質的なギャップ

**完成した部分（`sorry` なし、`#print axioms` は `propext` / `Classical.choice` /
`Quot.sound` のみ）：**

1. `liftAct` / `prj` / `prj_run` / `run_liftActs_other` — 9↔12 本の埋め込みと模倣補題。
2. `width_*_applyAct(s)_le`（9 成分すべて）— `ClearAny.width_step` の `GSPre.Act` 版。
3. `prologueProg` / `prologue_spec` — `PrepPre` から `GSPre.Enc … x 0 0 ⟨0,…,0⟩` を作る
   （`x = (w.take L).reverse`）。長さちょうど `6 * L + 5`。
4. `decLoop` / `clearSeqProg`（`## 3g2`）— **値・既知内容量**でコストが決まるクリア：
   `ClearAny` の形非依存クリアは右文脈の未知の余白の長さに依存してしまい（`PrepPre` は
   その長さを一切固定しない）、`len_le` の証明に使えない。そこで
   `decLoop`（カウンタを**現在の値**ぶんだけ `Tape.counter'_dec` する）と
   `clearSeqProg`（`SeqView` の**既知の位置・既知の総語長**ぶんだけ掃く、
   `rightSweep_prefix` で未知の余白 `t` には踏み込まない）に置き換えた。
5. `epilogueProg` / `epilogue_spec` — 上の道具で `decompose2_on_tapes` の終状態
   （生の `p₁ = D` ではなく実際は `Cp` の値 `p1raw`、`r`、`sC2/sAp/sAn` の値 `D`/`Q`/`E`）
   から `effPeriod`/`effReach` の正規化（`p₁ = 0` の退化ケースを含む）・
   4 本のカウンタの掃除・`sP`/`sU` の掃除を行う。正規化の分岐 `if cval (ts sC1) = 0 …`
   は確率的なオラクル判定を要らない（`epilogueProg` は `Tapes sc` を引数に取る関数
   なので、「地の Lean」で評価できる）。動作数は `D`, `Q`, `E`, `r`, `L`（および
   `sP`/`sU` のヘッド位置 `pP`, `pU`）の 1 次式で抑えられる
   （`epilogue_spec` の最後の結論）。
6. `fullProg` / **`prepPre_to_setupPre`** — `prologueProg ++ decProg.map liftAct ++
   epilogueProg` を実行すると、`PrepPre` から `PrepInstances.prepRes` が与える
   正規化済み三つ組で `SetupPre` が成り立つことを完全に証明した。ただし
   `mark ≠ blank` と `endSym ∉ (w.take L).reverse` を仮定として受け取る。

**`StageTapes.PrepOnTapes` の `forb` 一般化（コミット `d1f2280` の後、本タスクで実施）：**

`StageTapes.PrepOnTapes sc blank mark` に第 4 引数 `forb : Fin sc` を追加し、
`post` に仮定 `forb ∉ w` を足した（`PrepPre` の直後、`(res w L).1 < L` の前）。
`stround` / `ststate` / `prep_complete` / `setup_complete'` など `PrepOnTapes` を
使うすべての定義・定理に `forb` を伝播し、`setup_complete'` には `hforb : forb ∉ w` を
追加、`Pre.post` の呼び出し 2 箇所に渡した。`stage_tapes_spec'` では
`Pre : PrepOnTapes sc blank mark endSym`（`forb := endSym` に固定）とし、
既存の `hend : endSym ∉ w` をそのまま使う。`startSym ∉ w` に相当する仮定は
コードベース中どこにも現れず（`grep` で確認）、`decompose2_on_tapes` も要求しない
（`hk, hend, hmark` のみ）ので、`forb` は 1 本で足りる（ペア化は不要）。
これで **`hend` のギャップは解消**され、`prepPre_to_setupPre` が
`PrepOnTapes sc blank mark endSym` の `post` フィールドとして直接使えるようになった。
`FullMachineTapes.lean` / `PrepInstances.lean` は `PrepOnTapes` に言及するのが
コメントのみだったため無変更で再チェック済み。

**新たに判明した、より根深いギャップ：`len_le` が `decompose2_on_tapes` ベースの
`prog` では（今の `PrepOnTapes` の型のままでは）証明できない。**

`PrepOnTapes.len_le` は

```
len_le : ∀ (x : List (Fin sc)) (L : ℕ) (ts : Tapes sc), (prog x L ts).length ≤ Cp * L + Dp
```

という形で、**`ts` に一切の制約を課さない**（`PrepPre` すら要求しない）全称命題である。
ところが `GSPreprocessTapes.decProg`（`decompose2_on_tapes`/`decProg_spec` の主体）の
長さは `ts` の中身に本質的に依存する：たとえば `cleanProg blank k P`
（`GSPreprocessTapes.lean:4054`）は `P := pOf (dFpS …)`——**現在ある時点でテープから
読み取った値**——に比例する長さ `3 * P + 2 * (k - 1) * P` を持ち、`decProg_spec` /
`decompose2_on_tapes` 自身も `hend : endSym ∉ x` と `hE : Enc … ts` を要求している
（つまり「`ts` が `Enc` の形をしている」という保証がなければ、そもそも長さの主張が
証明できない）。`Enc` が成り立たない・でたらめな `ts` を渡せば、`P` はいくらでも
大きくなり得るので、**`Cp * L + Dp` で抑える固定の `Cp, Dp` は存在しない**
（`hsum : EndToEnd2.PassPeriodSum 8 C₁` を足しても、それは「`x` から生成した正しい
`ts`」に対する周期和の上界であって、任意の `ts` に対する `P` の値までは制御しない）。

これは `hend` のギャップと**同型の問題**である：`post` は `PrepPre` を前提に取れるので
解決できたが、`len_le` には対応する前提（`PrepPre` あるいは同等の「`ts` はこの
`x, L` に対して正しく初期化されている」という仮定）が一切ない。したがって：

* `prepInstance : StageTapes.PrepOnTapes sc blank mark endSym` の `prog := fullProg`
  ・`res := PrepInstances.prepRes` ・`post := prepPre_to_setupPre` はここまでの結果を
  そのまま繋げば型に合うはずだが、**`len_le` フィールドだけは正しい `Cp, Dp` が
  存在しないため埋められない**。
* 修正の方向性は `hend` のときと同型：`PrepOnTapes.len_le` に `PrepPre blank mark L
  (何らかの w with x = w.take L) ts` 相当の前提を追加する（`StageTapes.lean` の
  変更を要する。本タスクでの `forb` 追加の許可は `post` 周りに限られていたため、
  ここでは着手していない）。

**本ファイルの成果として持ち帰れるもの**：`prepPre_to_setupPre` は `post` フィールドの
完全な証明として即使える。`epilogue_spec` の最後の結論（1 次式の長さ上界）は
`epilogueProg` 単体の長さを `D, Q, E, r, L, pP, pU` で正確に抑えており、
`len_le` を最終的に埋める際の主要な部品になる：残るのは
`decProg` 自身の長さを（`PrepPre` 相当の前提のもとで）`L` の 1 次式で抑える
`PrepInstances.prep_work_le`/`prep_prog_len_le` を、上記の `PrepOnTapes.len_le` の
型変更後にそのまま接続することだけである。
-/

end PrepInstance
end PalPeg
