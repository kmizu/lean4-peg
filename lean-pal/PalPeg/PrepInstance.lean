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

## 未完成（`sorry` で明示）

* **prologue**：`sIn`（ヘッド `L - 1`）から `x = (w.take L).reverse` を
  `pword startSym endSym x` の形で `sP`/`sU` 上に書き、`Enc … 0 0 ⟨0,…,0⟩` を
  満たす配置を作る動作列。
* **epilogue**：`decompose2_on_tapes` が返す終状態から、`sP`/`sU` を
  `ClearAny.clearAny` でスタック `[]` に、`sC2/sAp/sAn/sRn` を `ClearAny.clearAny`
  ＋ `mark` 書き戻し 1 手で `CounterView' _ _ 0` に戻し、`SetupPre` を満たす配置を作る。
* **`prepInstance` 本体**と `len_le`（`PrepInstances.prep_prog_len_le` 系の線形上界と
  prologue/epilogue の `O(L)` 上界を合算するだけで閉じるはずだが、上記 2 点が
  埋まっていないため未接続）。

いずれも、幅 (`width`) の見積りが `GSPre.Tapes` の各コンポーネントの
「使用前後で `Blanks` として保持されている右文脈の長さ」に依存し、それを
`decompose2_on_tapes` の呼び出し文脈（`stround`/`ststate` が実際に用意する
初期テープ）まで遡って確定する必要がある。本ファイル単体では確定できないため、
`sorry` として残し、ここに明記する。
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

/-!
## 4. 残作業（`sorry`）

`prologue`：`sIn` 側の `PrepPre` から `Enc blank startSym endSym mark x 0 0 ⟨0,…,0⟩` を
`prj` 越しに満たすテープ配置を作る動作列。`x := (w.take L).reverse` であり、`sIn` の
ヘッドは `L - 1` にあるので、そこから **左へ** `L` 回歩いて読んだ記号をそのまま
`sP`（`sV1` 経由で `V1`）と `sU`（`sV2` 経由で `V2`）の両方へ積めば、積まれる順序が
反転して `x` になる（`PatternTapes.copyLoop` 系の技法がそのまま使える）。
両端に `startSym` / `endSym` の番人を足す必要がある。

`epilogue`：`decompose2_on_tapes` の終状態（`∃ a b D Q E, Enc … x a b ⟨D,Q,E,p₁,0,s,r⟩ …`）
から、`ClearAny.clearAny` で `sP`（= `V1`）・`sU`（= `V2`）をスタック `[]` に、
`ClearAny.clearAny` の結果に `SAct.put _ mark .right` を 1 手足すことで
`sC2`（= `Cd`）・`sAp`（= `Cq`）・`sAn`（= `Ce`）・`sRn`（= `Cf`）を
`CounterView' _ _ 0` に戻す（`CounterView' blank mark tp 0 ↔ StackView blank tp [mark]`、
`Tape.push_spec` で最後の 1 手を正当化する）。この 2 つを両方 `run` で連結し、
`SetupPre` の 15 個のフィールドをすべて `prj`/`liftAct` 越しに再構成すれば
`PrepOnTapes.post` が閉じる。

`len_le`：`decProg` の長さは `PrepInstances.prep_prog_len_le`（`hsum` 付き）で
`L` の 1 次式に抑えられる。prologue は `2 * L + O(1)`、epilogue の `clearAny` 部分は
`width_Cd_applyActs_le` 系（4 本のカウンタ）と `V1`/`V2` の `SeqView` から来る
`width ≤ x.length + 1 = L + 1`（一定、`decompose2_on_tapes` の動作でこの 2 本の幅は
`SeqView` の性質上つねに `x.length + 1` — 増えない）という評価から `O(L)`。
これらを合算すれば `Cp * L + Dp` の形に収まるはずだが、上記 prologue/epilogue の
具体的な動作列と `post` の証明を書き切っていないため、`prepInstance` 自体は
本ファイルにまだ存在しない。

以上より、本ファイルは **`PrepOnTapes` を埋めるための模倣層（1〜3）を
`sorry` なしで提供**するにとどまり、`prepInstance` 本体・`prepInstance_res` は
未着手であることをここに明記する。
-/

end PrepInstance
end PalPeg
