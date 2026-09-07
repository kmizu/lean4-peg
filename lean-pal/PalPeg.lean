import PalPeg.Basic
import PalPeg.Existence
import PalPeg.EvenLength
import PalPeg.Axioms
import PalPeg.Words
import PalPeg.Chain
import PalPeg.Structure
import PalPeg.Groups
import PalPeg.GroupsLog
import PalPeg.GroupsLogBound
import PalPeg.Matching
import PalPeg.GSScan
import PalPeg.GSDecomp
import PalPeg.GSPreprocess
import PalPeg.GSRealTime
import PalPeg.GSVerifier
import PalPeg.GSScanTapes
import PalPeg.GSVerifierTapes
import PalPeg.TextFeed
import PalPeg.BorderJob
import PalPeg.RTQueue
import PalPeg.RTQueueTapes
import PalPeg.Manacher
import PalPeg.ManacherHeads
import PalPeg.MiddleJob
import PalPeg.Stages
import PalPeg.Assembly
import PalPeg.StageMatcher
import PalPeg.OnlineMachine
import PalPeg.Schedule
import PalPeg.TapeLib
import PalPeg.Speedup
import PalPeg.ProgramMachine

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
* `PalPeg.GroupsLog` — group 併合・正準性・境界縮小 `3ℓ' < 2ℓ`；`GroupsLogBound` で群数 ≤ 2·log₂|v|+4 を無条件化
* `PalPeg.Matching`  — KMP 一歩・境界鎖・Galil の予測補題（仕事 ≤ 保証ゼロ出力数）
* `PalPeg.Manacher`  — Manacher の radius 走査の正しさ、接頭辞回文フラグ、仕事量 ≤ n
* `PalPeg.ManacherHeads` — Manacher をテープ上で走らせたときのヘッド総移動 ≤ 7|x|（telescoping）
* `PalPeg.MiddleJob` — 中央回文フラグ：区切り埋め込みで偶奇統一、4 分割ジョブの費用 ≤ 128h と締切 `middle_flag_spec`
* `PalPeg.Stages`    — dyadic stage 分解 `Pal(n) ⇔ match_W ∧ middle_W`、段の被覆と同時稼働 ≤ 2
* `PalPeg.Assembly`  — 段の組み立て：照合/中央オラクル ⇒ `answer_correct`、`answer_length_iff_mem_PAL`、生成/退役/オンライン性
* `PalPeg.StageMatcher` — GS 照合器が `MatchOracle` を満たす（`dyadic_gs_mem_PAL`、オンライン性 `answer_take`）
* `PalPeg.OnlineMachine` — 全体機械の添字モデル（2 段、中央/前処理はインターフェース）`output_correctH`（半分割：段 S はパターン rev(w.take(S/2))、前処理 (S/2,S]、テキスト w.drop S）、ラウンド費用 ≤ 3(3(k+1)+Cm+Cp)
* `PalPeg.Schedule`  — 順序処理の締切（`finishTime_le`）と Galil の FIFO サービス不等式（Lindley）
* `PalPeg.TapeLib`   — 成果物のテープ上の zipper / stack / seq / counter ビューと 1 アクション補題
* `PalPeg.GSScan`    — Galil–Seiferas 走査：安全シフト、健全性/完全性、ポテンシャル `Φ=(k+1)pos+q`
* `PalPeg.GSDecomp`  — GS 分解 `GSCore/GSDecomp`、k 反復周期の補題、走査側帰結と `KSimple` への橋（L1 の厳密境界は未了）
* `PalPeg.Speedup`   — 1 記号あたり B マイクロステップの機械 → 厳密実時間 `Machine`（線形加速、`multiStep_recognizedBy`）
* `PalPeg.GSRealTime` — GS 走査の実時間実行：レート k+1 で `online_answer_correct`、有界遅れ不変量 `onlineRun_phi`、u 検証器の締切
* `PalPeg.GSVerifier` — u 検証器を quota 2 で交互実行（オラクルなし `vAnswer_correct`、1 ラウンド ≤ 3(k+1)）
* `PalPeg.ProgramMachine` — 構造化機械 `StructuredMachine`（有限型の制御・記号）→ `MultiStepMachine` → `RecognizedBy`、phase 記法
* `PalPeg.GSScanTapes` — GS 走査 1 歩を 3 テープ（P/Txt/Cnt）の動作列で実現、コスト ≤ (2k+2)ΔΦ+8
* `PalPeg.GSVerifierTapes` — u 検証器の 5 テープ化、走行費用 ≤ (2k+3)ΔΦ+18n（L1 不要で償却）
* `PalPeg.TextFeed`   — 到着記号を FIFO で走査テープに供給、`feed_online` で `onlineRun` を再現
* `PalPeg.BorderJob`  — 中央フラグの GS 系境界列挙（縮小段、`palPrefixFlagsGS_spec`、仕事 ≤ 258|x|）
* `PalPeg.RTQueueTapes` — Hood–Melville キューを 9 本のスタックテープで実現（snoc ≤ 20、tail ≤ 27 動作；`lenr ≤ lenf` 判定は仮定）
* `PalPeg.GSPreprocess` — 計算可能な GS 分解 `decompose`（Python と一致）、`decompose_spec : GSCore`、1 パス線形（全体は L1 待ち）
* `PalPeg.RTQueue`   — Hood–Melville 実時間キューと FIFO 仕様
* `PalPeg.Chain`     — 接尾辞回文鎖のオンライン参照算法と `w ∈ PAL ↔ |w| ∈ chain w`
-/
