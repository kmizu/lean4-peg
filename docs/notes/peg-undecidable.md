# PEG の空性・同値性・完全性の決定不能性（Ford 2004 に忠実に）

Ford, "Parsing Expression Grammars: A Recognition-Based Syntactic Foundation" (POPL 2004) §3.4–3.5 の証明を Lean で形にした。

## 道筋
1. **Ford の部分**（`Shallot/Peg/Undecidable/{PCP,Ford,FordIff,FordCor}.lean`）
   - PCP の各添字に印を足し、`A`・`B`・`D ← &. &(A !.) B !.` を作る（`fordG`）。
   - `A !.` の正しさ（論文には証明がない）: 成功する選択肢は添字の列の文字列を食べ、その列は印と「x が空でない」ことで決まる（`encS_unique`）。
   - 同値性と完全性は空性から（`ford_equiv_iff`、`ford_complete_iff`）。
2. **PCP の決定不能性**（論文は文献を引くだけ。`Complexity/{OneTape,Undec,Comp}/`）
   - 対角線: `K1`（1 テープの表が自分の符号を受理する）は決定不能（`k1_undecidable`）。
     判定機械を 1 テープにし（`oneTape_decides`）、受理と拒否を入れ替え（`TM.decides_compl`）、自分の符号を読ませる。
   - 1 テープの表 → 文字列書き換え（`tm_sr`）→ MPCP（`sr_mpcp`）→ PCP（`mpcp_pcp`）→ ビットの PCP（`pcpN_pcp`）。
3. **計算可能性**: 写像「`K1` の符号 → `fordG` の符号」を数のスタック機械で書き（`MachCards*`、`MachPrint*`、`kP_computes`）、
   時間の上限なしで TM の判定に移す（`tmDecidable_of_nreduce`）。
4. **まとめ**（`Main.lean`）: `peg_empty_undecidable`、`peg_equiv_undecidable`、`peg_complete_undecidable`。

## 論文が書いていない前提
- PCP の対の文字列は空でない。空の xᵢ があると `A ← … / ε A aᵢ / …` が左再帰で、解があっても受理されない入力が出る。
  TM から作る PCP は空でないので、論文の筋は保てる。
- 完全性の帰着（`A' ← &e_S A'`）は、元の文法 G が完全であることを使う。Ford の文法は完全（`fordG_complete`）。
- Ford の印 `aᵢ` は一文字の終端記号だが、文字は有限個なので、接頭辞にならない文字列 `# |…| $` で代用した。

## 公理
Ford の部分（`ford_iff`、`ford_equiv_iff`、`ford_complete_iff`、`fordG_complete`、`pcpN_pcp`）は `propext, Quot.sound` だけで、
構成的に通る。全体は `propext, Classical.choice, Quot.sound`。
