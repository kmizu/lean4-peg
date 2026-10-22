# 普通の PEG より一階 call-by-name Macro PEG は真に強い

`Shallot.PegSeparation.pel_strict_in_firstOrder` は、元の文字列言語クラス
`Cfg.IsPEL` と `IsFirstOrderMPEL` の間の真包含を証明する。

```text
(∀ L, Cfg.IsPEL L → IsFirstOrderMPEL L) ∧
∃ L, IsFirstOrderMPEL L ∧ ¬ Cfg.IsPEL L
```

一階とは規則へ渡すものがパーサであり、高階関数・ラムダ・callable の適用を含まないこと。
`MGrammar.FirstOrder` と開始式の `MExp.FirstOrder` で制限する。
規則・開始式は入力から独立した固定の有限データで、引数個数には一様な上限を課さない。
`Cfg.IsMPEL1` の「各規則の引数個数が1以下」という別の制約とは区別する。

両クラスとも全入力消費の有限な成功導出で受理する。
文法全体の停止性は仮定せず、成功・失敗・有限導出の不存在を混同しない。
クラス定義自体は整形式性を追加しないが、分離の証人は文法と開始式の両方の
呼び出しアリティ検査に合格する（`firstOrder_witness`）。

## 証明の接続

1. 普通の PEG を0引数の Macro PEGへ埋め込む既存の双方向証明を使い、
   `pel_subset_firstOrder` を得る。
2. 既存の時間階層定理 `kexp_strict 0` から、EXPTIME に属し P に属さない `Diag 0` を取る。
3. 既存のタブロー構成 `gT M 0` を本来の `MGrammar` / `MExp` へ戻す。
   `first_order_hard` は任意の EXPTIME 言語から、その固定した一階文法の言語への
   **実際の多項式時間 TM で計算できる帰着**を与える。
4. P の帰着閉包 `p_reduces` により、その一階文法の言語は P に属さない。
5. 同じ符号化で普通の PEG を認識する具体的な多項式時間 TM
   （`tokenLanguage_in_P`）と矛盾させ、文字列版 `Cfg.IsPEL` への非所属を得る。

APSPACE = EXPTIME や P ≠ PSPACE を前提として受け取る箇所はない。
既存の機械ベースの時間階層・タブロー・PEG認識器を接続する形式化であり、
新しい計算量クラス分離の発見という主張ではない。

## 高階構文から一階構文への実際の変換

`MacroPeg/HigherOrder/FirstOrder.lean` の `unemb` は、
カリー化された規則適用を引数リスト付きの呼び出しへ、de Bruijn 変数を
元の引数の順序へ戻す。`firstRule` / `firstGrammar` は先頭のパーサ引数宣言を取り除く。

`FirstShape` は、各規則の型が `p → … → p`、本体が対応する先頭ラムダ列と
ラムダなしの本体からなるという構文条件。`tableau_firstShape` が `gT M 0` にこれを証明する。
`emb_firstGrammar` は戻した文法を再び埋め込むと元の文法に完全一致すること、
`firstGrammar_obs` は全入力・全観測について成功・失敗・残余を双方向に保存することを示す。
型から呼び出しアリティも導く。単に「order 1」を一階構文と呼び替えてはいない。

## 入力符号化をそろえる

両方の計算量証明は既存の `ofBits` と `tokChar` を使う。
ビット列を4ビットずつ数へ読み、固定した8文字 `0 1 x ; | a b #` へ写す。
`tokChar` は7以上を `#` へ写すため、この復号は単射ではない。
最後の不完全な4ビット組は `ofBits` と同じく捨てる。
この規約は両クラスに共通で、帰着の出力 `encBits` は完全な組からなる。

`TokenInput.lean` は実入力からこの復号を行うスタック機械を実装し、
既存の packrat 表の初期化・反復・停止処理へつなぐ。
`readToken_spec`、`tokenLoop_spec`、`nruns_loadTokens` が入力からの正しさと時間上限、
`tokenProgram_halts` が文法との一致を証明する。
空入力・不完全な末尾・非停止する文法も全称定理の対象になる。

仮に証人の文字列言語に普通の PEG があれば、同じ `tokenWord` による復号を
その PEG の前に置いて P の判定器が得られ、上の非所属と矛盾する。
結論は符号化された計算問題だけでなく、元の文字列言語クラスの真包含である。

## P の帰着閉包

`Reduce.lean` は既存の具体的な合成機械 `closeP` を使う。
多項式時間の帰着を走らせ、出力を入力として配置し直し、多項式時間の判定器を走らせる。
`closeBoundN_poly` が全段階の多項式上限を与え、`nprog_in_P` が検証済みの
スタック・リスト・TM変換で実際の P 所属へ接続する。
既存の `kexp_reduces` の `j ≥ 1` の仮定を迂回して流用したものではない。

## 検証

主要な15定理の依存を `lean/Audit.lean` のメッセージ検査に固定する。
依存は `propext` / `Classical.choice` / `Quot.sound` のみ（一部はそれ以下）。

```sh
cd lean
lake build
../scripts/audit-source.sh
```
