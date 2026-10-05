# 高階 Macro PEG の形式化と計算量（2026-10-05）

## 結論

1. **M-PEG-4 の断片（捕獲なしの lambda）は EXPTIME 完全のまま。** 脱関数化で一階の文法へ翻訳でき、観測が一致する
   （`defun_obs`）。だから、一階の判定手続きがそのまま使える（`decideSlice_iff`）。
2. **クロージャ付きの型付き高階 Macro PEG を定義した。** 一階の Macro PEG は、その order 1 の断片として埋め込める（`emb_obs`）。
3. **高階 Macro PEG の認識は判定可能。** 有限の単調モデルでの不動点計算が、call-by-name の実行と一致する
   （`decideHO_iff`）。反復回数は値の個数の塔で抑えられ、order k の規則では |x| について k 重指数になる。
4. 下界（order k で k-EXPTIME 困難）は**未証明**。予想として残す。

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

定理は内在的に型付いた文法 `TGrammar` を erase したものについて述べている。型検査器（`HasTy` から `Tm` を作る関数）は
作っていない。

## 計算量について言えること・言えないこと

形式化してあるのは次のことだけ。
- 反復回数は `maxEnv` 以下。
- `maxCount (a ⇒ b) = |elems a| · maxCount b`。
- `|elems τ|` は塔 `sizeBound`（`|p| ≤ (N+3)^(N+1)`、`|a ⇒ b| ≤ |b|^|a|`）以下。
- 一階の規則では `maxCount ≤ ((N+3)^(N+1))^n · (N+1)`。

「order k なら k 重指数時間」は、ここからの読み取り（引数の型の order は k 未満）で、order ごとの閉じた式までは証明していない。
費用モデル（1 回の反復の手数）も形式化していない。

下界は未証明。一階は EXPTIME 困難（`atm_reduction`）で、order 2 で 2-EXPTIME 困難を示すには、指数長のテープを
order 1 の値（番地 ↦ ビット）で持つ交替 TM の模倣が要る。Jones（2001）と Kop–Simonsen（2017）の cons-free 高階
プログラムの結果からは、order k で k-EXPTIME 完全になると予想している。どちらも外部の参照で、ここでは使っていない。
