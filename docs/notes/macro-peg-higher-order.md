# 高階 Macro PEG の形式化と計算量（2026-10-05）

## 結論

1. **M-PEG-4 の断片（捕獲なしの lambda）は EXPTIME 完全のまま。** 脱関数化で一階の文法へ翻訳でき、観測が一致する
   （`defun_obs`）。だから、一階の判定手続きがそのまま使える（`decideSlice_iff`）。
2. **クロージャ付きの型付き高階 Macro PEG を定義した。** 一階の Macro PEG は、その order 1 の断片として埋め込める（`emb_obs`）。
3. **高階 Macro PEG の認識は判定可能。** 有限の単調モデルでの不動点計算が、call-by-name の実行と一致する
   （`decideHO_iff`）。反復回数は値の個数の塔で抑えられ、order k の規則では |x| について k 重指数になる。
4. 下界は order 1 まで: 交替 TM を模倣する一階の文法を埋め込むと同じ入力を受理するから、高階版も EXPTIME 困難
   （`atm_reduction_HO`）。
5. **order 2 は 2-EXPTIME 困難。** 作業テープが 2^n マスの交替 TM を、型の付いた order 2 の文法で模倣した（`order2_hard`）。
   こちらは AEXPSPACE = 2-EXPTIME を外部の事実として使う。
6. **order j は j-EXPTIME 完全（j ≥ 1、外部の事実なし）。** 上界は費用モデルでの閉じた式 `tower j (C·poly(N))`
   （`decideCost_le`）。下界は決定性多テープ TM の計算表を order j の文法でたどる帰着（`kexp_hard`）。
7. **一様な問題（文法も入力）は TM の時間で j-EXPTIME 完全**（`umpeg_complete`、j ≥ 1）。下界は計算表の文法を
   前置きにした符号への帰着（`uniform_hard`）。上界は判定を数のスタック機械 `mainP j` で書き（`mainP_halts`）、
   手数を `tower j (poly)` で抑え（`mainCost_le`）、リスト機械経由で多テープ TM に写した（`umpeg_kexp`）。

## 1. 捕獲なしの lambda の断片（`Properties/{MExpEq,Defun,DefunCorrect}.lean`）

lambda は `subst` で葉として扱われるから、実行中に出会う lambda は、文法と開始式に書かれた有限個のリスト `Λ` に限られる
（`lams_subst`、`lamsOf_closed`）。

翻訳の仕組み:
- 引数ごとに**タグ**を付ける。0 は lambda でないこと、ℓ+1 は `Λ[ℓ]` を表す。
- 規則と lambda の本体を、そのタグの組ごとに特殊化した一階の規則にする。
- タグ ℓ+1 の引数を呼ぶ式は、`Λ[ℓ]` の特殊化を呼ぶ式になる。

証明の要は、翻訳と代入の可換性 `tr_subst` で、これは前提なしに成り立つ。あとは fuel 付きの実行どうしを一手ずつ対応させる
（`run_forward` / `run_backward`）。

翻訳後の規則数は `Σ (|Λ|+1)^arity` で、文法を固定すれば定数。だから判定は指数時間のまま。下界は、一階の文法が断片に
そのまま入ることから従う（`atm_reduction`）。

## 2. 型付き高階 Macro PEG（`HigherOrder/{Syntax,Semantics,Examples,Embed}.lean`）

定義:
- 型は `p` と `a ⇒ b`。
- 項は PEG 演算、de Bruijn の変数、値としての規則、型注釈付きの lambda、適用。
- 意味論は、ヘッド簡約（規則の展開と β）で PEG 演算まで持っていく call-by-name。
- 引数は評価せずに、閉じた項として代入する。

例（`Examples.lean`）:
- `twice f = f ∘ f` を `twice twice twice a` と重ねると、`a` が 16 回読まれる。
- `pre y = λx. y x` は `y` を覚えたクロージャになる。

埋め込み `emb_obs` の前提は、一階であることとアリティが正しいこと。アリティが違うと、余った引数が本体の呼び出しに
流れ込んで結果が変わるから、この前提は外せない。

## 3. 判定可能性（`HigherOrder/{Typed,Domain,Denote,Subst,Adequacy,Complete,Decide}.lean`）

有限モデル:
- 型 `p` の値は、位置 0..|x| ごとの結果（未定義・失敗・残り j）の表。
- 関数の値は、**単調な**引数の値全体の上の表。単調でない値まで表に入れると、反復が単調に増えなくなる。
- 規則の値は ⊥ から反復で求める。`den_mono` によって反復は増加列になり、定義済みの項目数が狭義に増えることから
  `maxEnv` 回で止まる（`iter_stable`）。

実行との一致は、二つの論理関係で示した。
- 健全性 `RelA`: 反復が出す結果は、実行の結果。
- 完全性 `RelB`: 実行の結果は、不動点の値。これは fuel 添字付きの関係で、関数型では m ≤ n のすべての添字で関係する
  引数を受ける。

代入について要る事実は、β 補題 `inst_substC` だけ。型付きの代入は作っていない。

定理は内在的に型付いた文法 `TGrammar` を erase したものについて述べている。`HasTy` で型が付く文法はどれも、ある
`TGrammar` の erase になる（`HGrammar.WellTyped.toTGrammar`）。だから判定は well-typed な文法全体に使える
（`decide_wellTyped`）。計算する型検査器は作っていない（存在を示しただけ）。

## 計算量について言えること・言えないこと

形式化してあるのは次のことだけ。
- 反復回数は `maxEnv` 以下。
- `maxCount (a ⇒ b) = |elems a| · maxCount b`。
- `|elems τ|` は塔 `sizeBound`（`|p| ≤ (N+3)^(N+1)`、`|a ⇒ b| ≤ |b|^|a|`）以下。
- 一階の規則では `maxCount ≤ ((N+3)^(N+1))^n · (N+1)`。

費用モデル（`Cost.lean`）: `decideHO` の手数を `den` の再帰に沿って数える。値の比較は項目数、λ は引数ごとに本体を 1 回、
適用は引数の索引探し、パーサ演算子は位置ごと。`decideCost_le` は、規則の型の order が k+1 以下で引数と束縛の型の order が
k 以下なら、手数が `tower (k+1) (C·((N+1)(N+2))²)` 以下だと示す（`C = gConst`、構文だけで決まる）。
TM での実装の時間ではなく、この費用モデルでの手数である。

## 4. order 2 の下界（`HigherOrder/ExpSpace/*.lean`）

機械（`Machine.lean`）:
- 作業テープは 2^n マス（n = |w|）。番地は上位ビットが先の n ビット列。
- 頭の左右移動は二進の ±1 で、端ではその場に留まる。
- 初期テープは、マス a に `⋁ⱼ (aⱼ ∧ wⱼ)` を置く。マス eⱼ（ビット j だけ 1）に wⱼ が入るので、機械は入力を読める。

文法 `g2 M`（`Grammar.lean`）:
- **番地**（order 0）: サイト j で x まで読めば、ビット j が 1 という意味のパーサ。最初の番地は `H0`。
  - 後者 `incE H`: サイト j を `Hⱼ xor（以降が全部 1）` で読む。後ろのビットは先読みの走査 `ALL1` で調べる。
  - 前者 `decE H`: 同じく `ALL0` を使う。
- **テープ**（order 1）: 番地を受け取り、そのマスが 1 なら幅 0 で成功するテストを返す。
  - 書き込みはクロージャ `λa. &EQ(a,H) b̂ / !EQ(a,H) T a`。
  - 初期テープは `λa. &SC(a)`。
- **状態**（order 2）: 型は `p ⇒ (p ⇒ p) ⇒ p`。`T H` でマスを読み、遷移ごとに動かした頭と書いたテープで次の状態を呼ぶ。

証明の流れ:
- 一階の観測補題（`codeE_ok` など）は、規則を含まない式に限って高階版へ移す（`runObs_peg`）。
- 規則呼び出しは、代入済みの本体の観測になる（`hobs_call`）。
- 番地の表現 `RepA` とテープの表現 `RepT` を保ったまま、`AtmHard` と同じ形の帰納法で模倣する（`sim`）。
- 型付け（`g2_wellTyped`）と order（`g2_order`）も示した。だから、この文法は上界の定理と同じクラスに入る。

## 5. order j の下界（`HigherOrder/{Levels,Tableau,KExp}/*.lean`）

交替機械を経由せず、決定性多テープ TM（`Complexity.TM`）の計算表を直接たどる。

レベルの数（`Levels/`）:
- レベル 0: 入力先頭の `m` 個のビットサイト上のパーサ。値は 2^m 未満。
- レベル i+1: 型 `lvTy i ⇒ p` の関数。レベル i の数 u を受け取り、ビット u が 1 なら幅 0 で成功する。値は `tower (i+2) m` 未満。
- 演算（inc / dec / isZero / isMax / eq）はブロック i の 12 規則の部分適用で書く。本体に λ は現れない。
- 正しさ `Spec` は i についての帰納法（`spec_succ`、`spec_all`）。

計算表の文法 `gT M K`（`Tableau/`）:
- 規則は STATE_q(t)、HEAD_τ(t, i)、SYM_{τ,s}(t, i)、READ_{τ,s}(t, i) で、t と i はレベル K の数。
- 漸化式は `TM.step` そのもの。停止状態なら前の構成のまま、そうでなければ読んだ記号の組（有限個）ごとに δ を引く。
- 時刻 0 のテープ 0 は入力。INPUT ループが入力サイトを先頭から数えて読む。
- `tableau_sim`: 時刻 `tower (K+1) m` 未満の全ての t で、各テストの真偽が `M.run` の構成と一致する。
- `start_obs`: 開始式が入力を全部読む ⇔ 最後の時刻の状態が受理。
- 型付け `gT_wellTyped`、order `gT_order = K + 1`。

帰着（`KExp/`）:
- `KEXP j L`: 時間 `tower j (c(n+1)^d)` で止まる決定性多テープ TM が L を決める。
- 符号: ビットサイトを m = (c+1)(n+1)^(d+1) 個、`|`、入力サイト、`#`。m > c(n+1)^d かつ m > n なので、
  停止時刻は表の範囲に入り、入力も番地に収まる。
- 符号を出すテンプレート `encT` を、TQBF の帰着と同じリスト機械（`compileT_spec`、`lm_polytime`）で動かす（`enc_polytime`）。
- `kexp_hard`: j ≥ 1 なら、`KEXP j` の言語は型付き order j の文法の言語へ多項式時間で帰着する。

一様な問題（`KExp/Uniform*.lean`、`KExp/Upper.lean`、`Mach/`）:
- `UMPEG j`: ビット列が文法・開始式・入力の符号 `serIn g s x` で、文法は型付き order j、開始式は閉じたパーサで、
  入力を全部読む。符号は単射（`serIn_inj`）。
- 下界 `uniform_hard`: `KEXP j` の言語は、計算表の文法 `gT M (j-1)` と開始式を前置きにした符号で `UMPEG j` に帰着する。
- 上界: 判定を数のスタック機械 `NProg`（40 本のスタック）で書いた `mainP j`。読み取り機械でトークンを読み（`readStage_ok`）、
  order を検査し（`ordStage_first`）、order < j かつ大きさ < 3|w|+2 の「小さい」型だけ値の表を作って（`rowsTableP_runs` ほか）、
  規則の値を不動点まで反復する（`evalP_runs`）。答えは `numDecideT j w`（`mainP_halts`）で、`UMPEG j` の判定（`numDecideT_iff`）。
- 手数は `tower j (c·(n+1)^8)` 以下（`mainCost_le`）。スタック機械はリスト機械を経て多テープ TM に写り
  （`kexp_of_nprog_time`）、`umpeg_kexp` になる。

order の階層（`KExp/Hierarchy.lean`、`KExp/Diag*.lean`、`KExp/Close*.lean`、`Complexity/Univ/`）:
- TM は遷移表に直せて（`tableOf`、`frun_rep`）、数のスタック機械 `simP` が表を B 手シミュレートする（`simP_runs`、
  手数は `simCost_le`）。
- 時間階層 `kexp_strict`: 対角言語 `Diag j` は `KEXP j` に入らず（`diag_not_kexp`）、`KEXP (j+1)` に入る（`diag_kexp`、
  `tower j (2^m) = tower (j+1) m` で 1 段上の塔に収まる）。
- 帰着で閉じる `kexp_reduces`: 帰着の表を動かし、出力を読み戻して（`extractP_runs`）判定の表を動かす。
- 固定文法の TM 上界 `mpeg_kexp`: `fixedMap_polytime` で `UMPEG j` へ帰着する。
- `order_strict`: `Diag j` を `kexp_hard` で order j+1 の文法に帰着すると、その言語は order ≤ j のどの文法の言語でもない。

## 残り

- 大きい機械のファイル（`Mach/EvalLoop.lean`、`ItemLeaf.lean`、`ItemVRA.lean`、`RowsTable.lean`）は 2000〜3000 行あり、
  分割していない。
