# PAL Python → Scala 3 移植 実装計画

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** `docs/palindromes-in-peg/**/*.py`（約 170 ファイル、18,000 行）を全て Scala 3 に移植し、
コウタが Scala だけで目視検証できるようにする。Python 版は当面残す（差分テストの基準）。

**Architecture:** 既存の `scala/` sbt ビルドに新サブプロジェクト `pal`（`scala/pal/`）を追加。
Python モジュール 1 つ = Scala ファイル 1 つ（`snake_case.py` → `SnakeCase.scala`、
パッケージ `pal`）。`unittest` は munit に 1:1 で移植。テキストを出力する生成器は
Python と **バイト一致** を差分テストで確認する。

**Tech Stack:** Scala 3.7.4（ブレース構文）、sbt 1.11、munit 1.1.1、Python 3.14（基準としてのみ）。

**Spec:** `docs/palindromes-in-peg/STATUS.md` §2（構成）と §5B（移植は SHA 再現の鎖を切りうる →
だからこそバイト一致の差分テストを必須にする）。

## Global Constraints（全タスク共通・必読）

1. **Scala 3 だがブレース構文を使う。** indentation syntax、`then`/`do` 省略記法、`end` マーカーは禁止。
   `if (c) { ... } else { ... }`、`for (x <- xs) { ... }`、`match { case ... }` の形で書く。
2. `scalacOptions` は既存の `strictOpts`（`-deprecation -feature -Wunused:all -Werror`）。警告ゼロ。
3. **ファイル対応 1:1**：`foo_bar.py` → `scala/pal/src/main/scala/pal/FooBar.scala`、
   `test_foo_bar.py` → `scala/pal/src/test/scala/pal/FooBarSuite.scala`。テストのヘルパーを
   import している test ファイル（例 `test_scaffold_circuit_program`）は `src/test` 側の
   `object` にする。
4. **忠実性優先、ただし Scala らしく。** アルゴリズムと出力（規則名・順序・整形）は Python と
   同一にする。データ表現は Python のタプル/dict をそのまま持ち込まず、sealed trait / case class /
   enum に置き換える。`Expr` は `symbolic_sca2peg.py` の 14 タグ（and, or, not, const, symbol,
   self, select, read, present, pointer, old, null, exists, edge）で閉じているので sealed ADT。
   hash-consing（`Expr._pool`）は `Expr.share { ... }` 的な明示スコープで再現する。
5. **順序に注意。** Python の `dict`/`set` の反復順は挿入順。Scala では `mutable.LinkedHashMap` /
   `LinkedHashSet` / `Vector` を使い、`Map`/`Set`（不定順）を出力順に使わない。
   `sorted()` の比較（タプル辞書式、文字列）は Scala の `Ordering` で同じ結果になるよう明示する。
6. **不変性の規約は緩める。** 生成器は数百万規則を扱う性能コードなので、局所的な
   `mutable.*` と `var` は可。ただし公開 API は不変値を返す。
7. **差分テスト**：出力を持つモジュールは `PyDiff.assertSameAsPython(...)` で Python の
   出力と比較する（Task 0 で定義）。`generated/*.peg` と `generated/*.json` は Python 版の
   ゴールデン。Scala 版は同じ内容を生成しなければならない。
8. **Python 側は変更しない。** 差分の基準を壊さない。
9. 各タスクの完了条件：`cd scala && sbt -batch "pal/testOnly pal.<Suite>*"` が通り、
   `sbt -batch pal/compile` が警告ゼロ、対応する Python テストと同数以上のテストがある。
10. **コミットはタスク単位**（`feat(pal): port <modules>`）。branch は現在の
    `feat/pal-plain-peg-artifact`。
11. 2 文字の Python コードは Codex 産で密度が高い。Scala では読み手（コウタ）のため
    メソッドを分割し、Python の docstring を Scaladoc として引き継ぐ。日本語コメント可。

## 依存層（leaf → root）。同じ層は並列可能

| 層 | モジュール |
|---|---|
| L0 core | symbolic_sca2peg, phase_peg, scaffold_circuit, scaffold_circuit_structs |
| L0 独立 | scavm, fpp_finite, gs_heads, gs_overlap, gs_local_clock, galil_contracts, fpp, fpp_tape, lps_halving, online_manacher, read_blocks, stage1_kmp_online, stage2_tm_galil, symbolic_tm2peg, tm2peg, twoway, verify_window_pal, compact_scaffold_peg, analysis/grammar_closure, analysis/grammar_scc |
| GS 群 | gs_flag_heads, gs_match_heads, gs_head_liveness, gs_events, gs_dual_flags, gs_batch_clock, delayed_pal, gs_flag_trace, gs_match_trace |
| FPP 群 | fpp_subroutine, fpp_reuse, fpp_cost, dp_finite, dp_search_finite, dp_search_reuse, chain_finite, move_center_finite, galil_clock |
| SCAVM 群 | scavm_structs, scavm_pal, scaffold_input, scaffold_places, scaffold_program, scaffold_search, scaffold_chain, scaffold_galil, galil_realtime, scaffold_pal, stage5_port_block1 |
| 独立小物 | peg_file, twoway_border, stage3_tm_galil_chain, stage3b_design_check, generate_phase_examples, generate_scaffold_examples |
| 回路群 | scaffold_optimize, scaffold_artifact, scaffold_round, scaffold_round_lazy, scaffold_round_tree, scaffold_rom, scaffold_event_buffer, scaffold_queue_registers, scaffold_head_distances, scaffold_live_distances, scaffold_stream_heads, scaffold_circuit_input, scaffold_circuit_program, scaffold_circuit_search, scaffold_circuit_chain, scaffold_circuit_galil, scaffold_match_input, scaffold_gs_heads, scaffold_gs_matcher, scaffold_gs_flags, scaffold_delayed_pal, midpoint_peg, generate_galil_peg, generate_online_peg |
| 窓群 | scaffold_window_counter, scaffold_window_positions, scaffold_window_registers, scaffold_window_live, scaffold_window_stream, scaffold_window_gs, scaffold_window_gs_live, scaffold_flag_packets, scaffold_window_workers, scaffold_window_pal, generate_window_pal |

---

### Task 0: sbt サブプロジェクト `pal` と Python 差分テスト基盤

**Files:**
- Modify: `scala/build.sbt`（`lazy val pal` を追加、`root.aggregate` に加える）
- Create: `scala/pal/src/test/scala/pal/PyDiff.scala`
- Create: `scala/pal/src/test/scala/pal/PyDiffSuite.scala`

**Produces:**
```scala
package pal
object PyDiff {
  /** docs/palindromes-in-peg を cwd にして python3 を実行し、stdout を返す。 */
  def python(args: String*): String
  /** Python スクリプトの stdout と Scala の文字列が完全一致することを検査する。 */
  def assertSameAsPython(actual: String, script: String, args: String*): Unit
  val pyDir: java.nio.file.Path   // docs/palindromes-in-peg の絶対パス
}
```
- [ ] build.sbt に追加（`Test / javaOptions` は `-Xss512m -Xmx8g`、`Test / fork := true`）
- [ ] `PyDiffSuite`：`python("-c", "print('x')")` が `"x\n"` を返す
- [ ] `sbt -batch pal/test` 緑、コミット `chore(pal): sbt subproject and Python diff harness`

### Task 1: L0 core（symbolic_sca2peg, phase_peg, scaffold_circuit, scaffold_circuit_structs）

- `Expr` を sealed ADT に。`Scaffold`, `Node`, `Grammar`, `CompactMemo`, `inverse_repeat`,
  `Value`, `Ref`, `Circuit`, `neg/conjunction/disjunction/choose/choose_pointer` を移植。
- `test_symbolic_sca2peg.py`, `test_phase_peg.py`, `test_scaffold_circuit.py`,
  `test_scaffold_circuit_queue.py` を munit に。
- 差分：`generate_scaffold_examples.py` が出す `generated/sparse_*.peg`, `scaffold_marked_palindrome.peg`
  と `generate_phase_examples.py` が出す `generated/phase_*.peg` をバイト一致で再生成できること。
  （generate_* 2 本はこのタスクに含める。）
- **Produces（後続タスクが依存する名前）**：パッケージ `pal`、`Expr`（+ `Expr.TRUE/FALSE/SELF/NULL`）、
  関数群は Python と同名 camelCase（`symbol, old, exists, negate, both, either, pointer, select,
  read, edge, present`、`neg, conjunction, disjunction, choose, choosePointer`）。
  `Scaffold`/`Circuit` のメソッドも Python 名を camelCase 化。実装後、この Produces 節に
  実際のシグネチャを追記すること。

### Task 2（並列）: L0 独立モジュール群（4 サブタスク、別エージェント）
- 2a: scavm, scavm_structs, scavm_pal, stage5_port_block1 + tests
- 2b: fpp_finite, fpp_subroutine, fpp_reuse, fpp_cost, dp_finite, dp_search_finite,
  dp_search_reuse, chain_finite, move_center_finite, galil_clock, fpp, fpp_tape + tests、
  `generated/*-controller.json` の再生成一致
- 2c: gs_heads, gs_overlap, gs_local_clock, gs_flag_heads, gs_match_heads, gs_head_liveness,
  gs_events, gs_dual_flags, gs_batch_clock, delayed_pal, gs_flag_trace, gs_match_trace,
  galil_contracts + tests
- 2d: tm2peg, symbolic_tm2peg, twoway, twoway_border, lps_halving, online_manacher, read_blocks,
  stage1_kmp_online, stage2_tm_galil, stage3_tm_galil_chain, stage3b_design_check, peg_file,
  compact_scaffold_peg, verify_window_pal, analysis/grammar_closure, analysis/grammar_scc + tests、
  `generated/anbn_from_tm.peg`, `marked_palindrome_from_tm.peg` の一致

### Task 3: SCAVM 足場群（2a, 2b に依存）
scaffold_input, scaffold_places, scaffold_program, scaffold_search, scaffold_chain, scaffold_galil,
galil_realtime, scaffold_pal + tests

### Task 4: 回路群（1, 2b, 2c, 3 に依存。2 サブタスク）
- 4a: scaffold_optimize, scaffold_artifact, scaffold_round, scaffold_round_lazy, scaffold_round_tree,
  scaffold_rom, scaffold_event_buffer, scaffold_queue_registers, scaffold_head_distances,
  scaffold_live_distances, scaffold_stream_heads, midpoint_peg（`generated/midpoint.peg` 一致）
- 4b: scaffold_circuit_input, scaffold_circuit_program, scaffold_circuit_search,
  scaffold_circuit_chain, scaffold_circuit_galil, scaffold_match_input, scaffold_gs_heads,
  scaffold_gs_matcher, scaffold_gs_flags, scaffold_delayed_pal, generate_galil_peg, generate_online_peg

### Task 5: 窓群と最終生成器（4 に依存）
scaffold_window_counter, scaffold_window_positions, scaffold_window_registers, scaffold_window_live,
scaffold_window_stream, scaffold_window_gs, scaffold_window_gs_live, scaffold_flag_packets,
scaffold_window_workers, scaffold_window_pal, generate_window_pal + tests。
差分：`generate_window_pal.py` と Scala 版を `--skip-optimize` で走らせた未圧縮 .peg の SHA 一致
（メモリ 22 GiB 級。無理なら `test_generate_window_pal.py` 相当の小さい構成での一致で代替し、
STATUS.md に未確認と明記）。

### Task 6: 文書・ビルド統合
STATUS.md §4 の再現手順に Scala 版を併記、README の pointer、Makefile `scala` ターゲットに
含まれることの確認、`PLAIN_PAL_ARTIFACT.md` に「Scala 版は Python 版とバイト一致（範囲を明記）」。
