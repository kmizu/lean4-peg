# lean-pal — `PAL ∈ PEG` の条件付き Lean 4 証明（Kim–Park 成果物経由）

回文言語 `PAL = { w ∈ {0,1}* | wᴿ = w }` が PEG 言語であることを、
**「`PAL` を認識する厳密実時間多テープ TM が存在する」という仮定のもとで** Lean 4 で証明する。
併せて Loff–Moreira–Reis (2020) Conjecture 7（偶数長回文 `{ w wᴿ }` は PEG を持たない）を
同じ仮定のもとで反駁する。

背景と鎖の全体は [`../docs/palindromes-in-peg/FORMALIZATION_SURVEY.md`](../docs/palindromes-in-peg/FORMALIZATION_SURVEY.md)
（特に §1, §3, §4）を参照。

## 何を証明し、何を仮定しているか

### 仮定（Lean では証明していない）

ただ一つ、`PalPeg.pal_recognizedByTotalPEG` などの前提に現れる

```lean
PegSeparation.RealTimeTM.RecognizedBy PalPeg.PAL
```

すなわち **Kim–Park 成果物の `RealTimeTM.Machine` の意味で `PAL` を認識する機械が存在すること**。
この機械は決定的・停止なし・**1 記号につきちょうど 1 遷移**・各遷移で**各テープがちょうど 1 回書き
1 回動く**（`Common/Compiler/RealTimeTM/Model.lean`）。受理は入力を全部読んだ直後の状態だけで決まる。

紙の上でこの仮定を与えるのは Slisenko (1973) / Galil (1978) の実時間回文判定機械だが、

1. Galil の機械を `RealTimeTM.Machine (Fin 2) t s k` として書き下し `∀ w, M.Accepts w ↔ w ∈ PAL` を証明すること、
2. 文献の「定数遅延の実時間」から成果物の「厳密実時間（1 記号 1 遷移、1 テープ 1 書き込み 1 移動）」への正規化
   （Hartmanis–Stearns 流の tape compression）

の**どちらもこのパッケージには含まれていない**（見積もりは調査 §6：8–15k 行）。
したがってここで示したのは「Galil の機械が成果物の厳密実時間モデルで書ける、と認めるなら `PAL ∈ PEG`」であり、
無条件の `PAL ∈ PEG` ではない。

### 証明したもの（`sorry` なし・新規 `axiom` なし）

すべて `PalPeg` 名前空間。成果物の定義（`PegSeparation.*`）をそのまま使う。

| 定理 | 内容 | ファイル |
|---|---|---|
| `PAL : Language (Fin 2)` | `{ w \| w.reverse = w }` | `PalPeg/Basic.lean` |
| `PAL_reverse_mem w` | `w.reverse ∈ PAL ↔ w ∈ PAL` | 同上 |
| `PAL_reverse` | `PAL.reverse = PAL`（`Language.reverse` の形） | 同上 |
| `pal_in_peg_of_realTime M hM` | `M : RealTimeTM.Machine (Fin 2) t s k`, `hM : ∀ w, M.Accepts w ↔ w ∈ PAL` ⇒ `∃ n (G : PegGrammar (Fin 2) n), G.IsLoffTotal ∧ ∀ w, G.Recognizes w ↔ w ∈ PAL` | `PalPeg/Existence.lean` |
| `pal_recognizedByTotalPEG h` | `RealTimeTM.RecognizedBy PAL → RecognizedByTotalPEG PAL` | 同上 |
| `EvenLength`, `OddLength` | `{ w \| Even w.length }`, `{ w \| Odd w.length }` | `PalPeg/EvenLength.lean` |
| `evenLength_isRegular`, `oddLength_isRegular` | 2 状態（`Bool`）DFA `evenDFA` / `oddDFA` による `Language.IsRegular` | 同上 |
| `evenPal_of_pal h` | `RecognizedByTotalPEG PAL → RecognizedByTotalPEG (PAL ⊓ EvenLength)` | 同上 |
| `oddPal_of_pal h` | `RecognizedByTotalPEG PAL → RecognizedByTotalPEG (PAL ⊓ OddLength)` | 同上 |
| `EvenPal`, `mem_PAL_inf_EvenLength_iff` | `EvenPal = { w \| ∃ u, w = u ++ u.reverse }`、`w ∈ PAL ⊓ EvenLength ↔ ∃ u, w = u ++ u.reverse` | 同上 |
| `evenPal_ww_reverse_of_pal h` | `RecognizedByTotalPEG PAL → RecognizedByTotalPEG EvenPal`（LMR Conjecture 7 の原文の形） | 同上 |
| `IsPal`, `HasPeriod` | `x.reverse = x`、`∀ i, i + p < |x| → x[i]? = x[i+p]?` | `PalPeg/Words.lean` |
| `isPal_cons_append_iff` | `IsPal ([a] ++ x ++ [b]) ↔ a = b ∧ IsPal x`（拡張則） | 同上 |
| `isPal_take_iff`, `isPal_drop_iff` | 回文の接頭辞／接尾辞が回文 ⟺ 境界（border） | 同上 |
| `hasPeriod_iff_drop_eq_take` | 周期 ⟺ 境界 | 同上 |
| `fineWilf` | `p + q - gcd p q ≤ |x|` での Fine–Wilf（Mathlib `List.HasPeriod.gcd` への橋） | 同上 |
| `hasPeriod_of_suffix_gcd` | 末尾 `p` 記号が `g`-周期的（`g ∣ p`）なら全体も `g`-周期的 | 同上 |
| `hasPeriod_minimal_of_suffix` | 最小周期 `p` の回文の、長さ `≥ 2p` の接尾辞回文の最小周期も `p`（group 補題） | 同上 |
| `chain`, `mem_chain_iff` | オンライン鎖算法：`ℓ ∈ chain w ↔ ℓ ≤ |w| ∧ 接尾辞回文` | `PalPeg/Chain.lean` |
| `mem_PAL_iff_length_mem_chain` | `w ∈ PAL ↔ w.length ∈ chain w`（機械の仕様） | 同上 |
| `chain_sorted`, `chain_eq_suffixPalLengths` | 鎖は狭義降順、素朴定義と一致 | 同上 |
| `suffixPal_replica` | レプリカ：top（周期 `p`）の下の長さ `L ≤ ℓ-p` の接尾辞回文は時刻 `n-p` のものと一致 | `PalPeg/Structure.lean` |
| `border_of_minimalPeriod` | 最小周期 `p` の回文の第 2 接尾辞回文は `x.drop p`、間に回文なし | 同上 |
| `center_suffix_of_pal`, `pal_prefix_length_ge` | 予測補題：時刻 `m' ∈ [m,2m]` の全接頭辞回文は時刻 `m` の長さ `2m-m'` の接尾辞回文から生じる | 同上 |
| `lsp_shift_bound` | 禁止帯：時刻 `n-p` の接尾辞回文長 `M` は `M ≤ ℓ-p` か `ℓ ≤ M`（`3p ≤ ℓ`） | 同上 |
| `cex_x_longest`, `cex_long_pal` | `001000` による「`LSP(n-p) = ℓ-p`」の反例（機械化） | 同上 |
| `groupChainRev`, `expandAll_groupChainRev` | group 圧縮鎖（1 群あたり記号参照 2 回）が `chainRev` を展開する。群数の対数上界は未証明（併合なし） | `PalPeg/Groups.lean` |
| `matchState_snoc_hit/_miss/_zero` | KMP 一歩（一致／境界鎖から復帰／0） | `PalPeg/Matching.lean` |
| `predictability_step`, `work_le` | Galil 予測補題：failure 連鎖の仕事 ≤ 次の一致までの保証ゼロ数 | 同上 |
| `border_snapshot` | 境界 `b` の状態は `j-b` 記号前のテキスト接頭辞の照合状態 | 同上 |
| `RTQueue.Queue`, `toList_snoc/tail`, `head?_eq`, `inv_*` | Hood–Melville 実時間キュー（最悪 O(1)/操作）の FIFO 仕様 | `PalPeg/RTQueue.lean` |

証明の鎖（`pal_in_peg_of_realTime`）：

```
G.Recognizes w
  ↔ (RealTimeTM.toSCA M).Accepts wᴿ     -- SCAToPEG.loffBackward（LMR Thm 16 十分方向）+ wᴿᴿ = w
  ↔ M.Accepts wᴿ                        -- RealTimeTM.toSCA_accepts_iff（厳密実時間 TM → SCA）
  ↔ wᴿ ∈ PAL                            -- 仮定 hM
  ↔ w ∈ PAL                             -- PAL_reverse_mem
```

Conjecture 7 側は成果物の閉包性 `Closure.recognizedByTotalPEG_inter`（共通部分）と
`Closure.recognizedByTotalPEG_of_isRegular`（正則 ⊆ PEG）に、`EvenLength` の正則性を渡すだけ。

### 公理 guard

`PalPeg/Axioms.lean` が主定理ごとに `#print axioms` を `#guard_msgs` で固定している。
現れる公理は Lean / Mathlib の標準 3 公理 `propext`, `Classical.choice`, `Quot.sound` だけ
（`PAL_reverse_mem` は `propext` のみ）。どこかに `sorry` が入れば `sorryAx` が現れて
`lake build` が失敗する。

```
'PalPeg.PAL_reverse_mem' depends on axioms: [propext]
'PalPeg.pal_in_peg_of_realTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'PalPeg.pal_recognizedByTotalPEG' depends on axioms: [propext, Classical.choice, Quot.sound]
'PalPeg.evenLength_isRegular' depends on axioms: [propext, Classical.choice, Quot.sound]
'PalPeg.evenPal_of_pal' depends on axioms: [propext, Classical.choice, Quot.sound]
'PalPeg.evenPal_ww_reverse_of_pal' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 依存

- Lean `leanprover/lean4:v4.31.0`（`lean-toolchain`）。この repo の `../lean`（v4.32.0、Mathlib 非依存）とは
  別パッケージ。成果物の証明は pin された Mathlib で検査されたものなので動かさない。
- Mathlib `v4.31.0`（`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`）。
- Kim–Park, *Separating Parsing Expression Grammars using Cell-Probe Lower Bounds: Lean Artifact* v0.1.0
  — GitHub `kimjg1119/peg-separation-artifact` commit `c364edb`（Zenodo doi:10.5281/zenodo.22099762）。
  `lakefile.toml` の `[[require]] name = "PegSeparation"` で git から取得する。
  使う定理は `RealTimeTM.toSCA_accepts_iff`（`Common/Compiler/RealTimeTM/Correctness.lean`）、
  `SCAToPEG.loffBackward`（`Common/Compiler/SCAToPEG/Final.lean`）、
  `Closure.recognizedByTotalPEG_inter`（`Closure/BooleanClosure.lean`）、
  `Closure.recognizedByTotalPEG_of_isRegular`（`Closure/RegularToPEG.lean`）。
  いずれも成果物側で標準 3 公理のみ（`axioms/closure.txt`）。

## ビルド

```sh
cd lean-pal
lake exe cache get      # Mathlib の olean を取得（初回は数分〜十数分）
lake build
```

または repo ルートで `make lean-pal`。Mathlib のダウンロードが要るので `make verify` には含めていない。
`elan` が入っていれば `v4.31.0` は自動で取得される。

参考：Mathlib キャッシュ取得済みの状態で、成果物側の必要モジュール 25 個（`Common/*`、`SCAToPEG/*`、
`Closure/{BooleanClosure,RegularToPEG}`、`External/PartialTotalization/TotalityHelpers`）と
`PalPeg` 5 モジュールの `lake build` は WSL2 上で約 2 分 30 秒。
成果物側の linter 警告（`unusedFintypeInType` 等 93 行）は出るがエラーはない。

## 次の一手

仮定を消すこと。方針は RTTM ではなく成果物の SCA（`Scaffolding.Automaton (Fin 2) …`）を直接構成して
`RecognizedBySCA PAL` を示し、`SCAToPEG.loffBackward` で PEG に落とす（`DESIGN_SCA_PAL.md`）。
`Words.lean`／`Chain.lean` はその機械の仕様層と組合せ論の層。SCA の実装と実時間性
（young run、break 後の再構築、Hood–Melville キュー）は未着手で、規模は調査 §6 の見積もりどおり。
