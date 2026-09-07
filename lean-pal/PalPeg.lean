import PalPeg.Basic
import PalPeg.Existence
import PalPeg.EvenLength
import PalPeg.Axioms
import PalPeg.Words
import PalPeg.Chain
import PalPeg.Structure
import PalPeg.Groups
import PalPeg.GroupsLog
import PalPeg.Matching
import PalPeg.GSScan
import PalPeg.RTQueue
import PalPeg.Manacher
import PalPeg.ManacherHeads
import PalPeg.MiddleJob
import PalPeg.Stages
import PalPeg.Schedule
import PalPeg.TapeLib

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
* `PalPeg.GroupsLog` — group 併合・正準性・境界縮小 `3ℓ' < 2ℓ`（群数の対数上界は条件付き）
* `PalPeg.Matching`  — KMP 一歩・境界鎖・Galil の予測補題（仕事 ≤ 保証ゼロ出力数）
* `PalPeg.Manacher`  — Manacher の radius 走査の正しさ、接頭辞回文フラグ、仕事量 ≤ n
* `PalPeg.ManacherHeads` — Manacher をテープ上で走らせたときのヘッド総移動 ≤ 7|x|（telescoping）
* `PalPeg.MiddleJob` — 中央回文フラグ：区切り埋め込みで偶奇統一、4 分割ジョブの費用 ≤ 128h と締切 `middle_flag_spec`
* `PalPeg.Stages`    — dyadic stage 分解 `Pal(n) ⇔ match_W ∧ middle_W`、段の被覆と同時稼働 ≤ 2
* `PalPeg.Schedule`  — 順序処理の締切（`finishTime_le`）と Galil の FIFO サービス不等式（Lindley）
* `PalPeg.TapeLib`   — 成果物のテープ上の zipper / stack / seq / counter ビューと 1 アクション補題
* `PalPeg.GSScan`    — Galil–Seiferas 走査：安全シフト、健全性/完全性、ポテンシャル `Φ=(k+1)pos+q`
* `PalPeg.RTQueue`   — Hood–Melville 実時間キューと FIFO 仕様
* `PalPeg.Chain`     — 接尾辞回文鎖のオンライン参照算法と `w ∈ PAL ↔ |w| ∈ chain w`
-/
