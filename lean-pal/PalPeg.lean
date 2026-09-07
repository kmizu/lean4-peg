import PalPeg.Basic
import PalPeg.Existence
import PalPeg.EvenLength
import PalPeg.Axioms
import PalPeg.Words
import PalPeg.Chain
import PalPeg.Structure
import PalPeg.Groups
import PalPeg.Matching
import PalPeg.RTQueue
import PalPeg.Manacher

/-!
# PalPeg

回文言語 `PAL ⊆ {0,1}*` が PEG 言語であることを、Kim–Park の Lean 成果物
(`PegSeparation`) を経由して**条件付きで**証明する。

* `PalPeg.Basic`     — `PAL` の定義と反転不変性
* `PalPeg.Existence` — 厳密実時間 TM が `PAL` を認識するならば total PEG が `PAL` を認識する
* `PalPeg.EvenLength` — 偶数長への制限（Loff–Moreira–Reis Conjecture 7 の条件付き反駁）
* `PalPeg.Axioms`    — `#print axioms` の guard
* `PalPeg.Words`     — 回文と周期の組合せ論（拡張則・境界・Fine–Wilf・group 補題）
* `PalPeg.Structure` — レプリカ・境界・予測補題・禁止帯（`lsp_shift_bound`）と (M) の反例
* `PalPeg.Groups`    — group 圧縮した鎖（2 回の記号参照/群）が `chain` を展開する
* `PalPeg.Matching`  — KMP 一歩・境界鎖・Galil の予測補題（仕事 ≤ 保証ゼロ出力数）
* `PalPeg.Manacher`  — Manacher の radius 走査の正しさ、接頭辞回文フラグ、仕事量 ≤ n
* `PalPeg.RTQueue`   — Hood–Melville 実時間キューと FIFO 仕様
* `PalPeg.Chain`     — 接尾辞回文鎖のオンライン参照算法と `w ∈ PAL ↔ |w| ∈ chain w`
-/
