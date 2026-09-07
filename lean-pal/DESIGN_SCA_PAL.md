# PAL を認識する SCA の設計メモ（Fable 5.1, 2026-09-07）

目標：`PegSeparation.RecognizedBySCA PAL`（`Scaffolding.Automaton (Fin 2) s k d r` で
`∀ w, Accepts w ↔ w ∈ PAL`）。これが取れれば `SCAToPEG.loffBackward` と
`PAL_reverse_mem` だけで `RecognizedByTotalPEG PAL` になり、RTTM を経由する必要はない。

## 1. SCA モデル（成果物 `Common/Model/Scaffolding.lean` の要点）

- 1 入力記号につきノードを 1 個生成。ノードは `label : Option (Fin k)` と
  `degree` 本の辺（古いノードへのオフセット）を持ち不変。
- 新ノードの辺は「旧 top から長さ ≤ radius の辺経路で到達できるノード」にしか張れない。
  遷移関数は旧 top の半径 radius 近傍の **ラベルだけ** を見る（ノードの同一性は見えない）。
- したがって SCA ＝ 「有限個のレジスタ（= top の辺）を持つ永続ポインタ機械。
  1 ステップ 1 割当て、後方ポインタのみ、前方移動は不可」。

含意：
- スタックは自明。キューは Hood–Melville 型の実時間キュー（漸進反転）が必要。
- 「過去のノード」はスナップショット。ノード t の辺 = 時刻 t のレジスタ内容。

## 2. 接尾辞回文鎖の構造（証明対象の組合せ論）

`S(n) = { ℓ ≤ n | w[n-ℓ+1..n] は回文 }`、`Pal(n) ⇔ n ∈ S(n)`、`LSP(n) = max S(n)`。

- (E) 拡張則：`ℓ ∈ S(n) ⇔ ℓ ≤ 1 ∨ (ℓ-2 ∈ S(n-1) ∧ w[n] = w[n-ℓ+1])`。
- (B) 回文 P の接尾辞回文 = P の境界（border）。よって鎖の差分 `d_i = ℓ_i - ℓ_{i+1}` は
  上から単調非増加。
- (G) top の最小周期を p とする。`L ≥ 2p` なる鎖要素は全て top-group（差分 p の列）に属し、
  group の最下要素は `< 2p`。証明：`L ≥ 2p` で `L` の最小周期 q < p なら Fine–Wilf で
  gcd 周期が top 全体に伝播し p の最小性に矛盾。
- (R) レプリカ：`Chain(n) = ℓ :: dropWhile (> ℓ-p) Chain(n-p)`（長さ集合として
  `S(n) ∩ [0, ℓ-p] = S(n-p) ∩ [0, ℓ-p]`）。`LSP(n-p) > ℓ-p` は起こり得る（例 `aaaabaa`）。
- (M) 成熟条件：`ℓ ≥ 3p` なら `LSP(n-p) = ℓ-p`。よって鋸歯 `LSP(t+p) = LSP(t)+p` が成り立ち、
  昇格時の新 top の cursor は「p ステップ前のノードの T 辺」に等しい。
- (P) 予測補題：時刻 m+1 で top-group が破れた（`w[m+1] ≠ w[m+1-p]`）とき、
  下位要素（長さ < 2p）が全接頭辞になり得る最早時刻は `2m - ℓ + p ≥ m+1+(p-1)`。
  top が生き残った場合の全接頭辞到達時刻は `2m - ℓ`。
- (N) 二進限定：break 時 `w[m+1] = ¬w[m+1-p]` なので下位要素の生死は時刻 `m+1-p` の生死の否定。

## 3. 機械の状態（1 ノードに詰める辺）

- `prev`：入力鎖。ラベルに `w[t]` を含める。
- `T`：top の実 cursor（ノード `t - LSP(t)`；`LSP(t)=t` なら初期ノード、ラベル `none`）。
- `U`：第 2 要素の cursor（成熟期は `T + p` の位置）。`c2 = (w[t+1] = label U)`。
- `P`：直前の昇格ノード。成熟期の昇格で `(T,U) := (T辺 P, U辺 P)`、`P := 今のノード`。
- `R`：下位構造 = 時刻 `t-p` のスナップショットへの参照（辺 `R` を辿ると鎖が再帰する）。
- FIFO（Hood–Melville）：break 後の遅延照合用。入力ノードを積み、rate 2 で消化。
- 有限制御：局所定数 P0 以下の周期は末尾 2·P0 記号を状態に持って総当たり。

## 4. 未解決（このメモ時点）

1. **young run**（`ℓ < 3p`）：group は ≤ 2 要素。第 2 要素の cursor 実体化を
   遅延照合（FIFO）＋ (P) の猶予で行う手順の明示と、猶予 ≥ 必要作業の不等式。
2. **break 後の下位構造の再構築**：レプリカの下位要素は「各レベルの group 要員セル」の
   stored cursor が誤る（左文脈がずれる）。(N) と graveyard 記録で最大生存者を求める手順の
   O(1)/step 化。
3. Hood–Melville キューの 1 ノード/ステップへの詰め込み（同時生成セルは相互参照不可）。
4. 上記全ての不変量を `Automaton.step` 上で証明する枠組み（`prefixMachine` の 850 行の
   数倍〜十数倍）。

結論：Galil の「オンライン→実時間」の骨格（predictability + FIFO）は永続モデルでも必要で、
成果物側の見積もり（8–15k 行）を下回らない。今セッションでは §2 の組合せ論を Lean で固め、
§3–4 は設計に留める。

## 5. Lean 上の分担

- `PalPeg/Words/*.lean`：§2 (E)(B)(G)(R)(M)(P)(N) を `List (Fin 2)` 上で証明。
- `PalPeg/Chain.lean`：鎖の抽象オンライン算法（group 圧縮なし、O(n)/step）を関数として定義し
  `∀ n, decide n = Pal n` を証明（機械化の仕様として使う）。
- SCA 実装（§3）は着手せず。
