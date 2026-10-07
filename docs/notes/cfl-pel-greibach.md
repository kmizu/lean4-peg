# 「PEG で書けない文脈自由言語はあるか」を Greibach の最難言語へ

Aho–Ullman と Ford の問い（Loff–Moreira–Reis, JCSS 2020 にも未解決として載る）は、Greibach の最難言語 `L0` 一つの問題と同値（`cfl_pel_iff`）。

## 道筋
- `L0`（Greibach 1973、Nipkow の Isabelle 版 AFP `Greibach_Hardest` 2026 を正本に写す）: `{ε} ∪ {x₁ c y₁ c z₁ d … | y₁…yₙ ∈ ¢D, …}`、`D` は 2 種の括弧の Dyck 言語。
- (→) `L0` は文脈自由（`l0_cfl`、Nipkow の文法 `G` と同じ）。
- (←) どの CFL も、ε を除いて `h⁻¹(L0)`（`stdForm_exists` で標準形にし、`greibach_std`）。PEG の言語は逆準同型で閉じる（`isPEL_invHom`）。
  `h` は Greibach の構成から「有限個の文字を除いて `c d`」なので、有限の文法でまねできる（ブロック内の位置で添字付けした規則と、終わりの位置での順序付き選択）。

## 気づいたこと
- 論文（Loff ら）は「証明できる」とだけ書き、どの閉包性を使うかは書いていない。必要なのは逆準同型での閉包と ε の出し入れ。
- PEG の逆準同型の閉包は自明ではない（ブロックの途中で終わる部分式を、終わりの位置ごとの規則に分けて追う）。
- 問い自体は計算量の壁に当たる: (全て PEG) なら CFL が RAM の線形時間で認識でき、50 年来の壁を破る。(書けないものがある) なら PEG に特有の論法が要る（PEG にポンプの補題は無い。回文は PEG で書ける）。

## 答え（2026-10-07 追記）
問いは Kim–Park, "Separating Parsing Expression Grammars using Cell-Probe Lower Bounds"（arXiv:2608.29592, 2026-08）が否定的に解いた:
全域な PEG（全ての入力で止まる文法）で書けない線形の文脈自由言語がある（証拠は `C^R`、セルプローブの Multiphase Inner Product の下界から）。

Lean での確かめ（Lean 4.31 + mathlib の、Kim–Park の成果物 Zenodo 10.5281/zenodo.22099762 の手元の写し `~/repo/peg-separation-local` で。外には出していない）:
- `fullyInternalSeparation`: 成果物の二つの外部の主張（PEG–SCA の特徴づけ、Ko の下界）を成果物自身の証明（`loffForwardRepaired`、
  Larsen–Yu 経由の `internalMultiphaseIPLowerBound`）で置き換えると、分離は標準の 3 公理だけで通る。
- `greibachHardest_not_totalPEG_noAxioms`: **Greibach の最難言語は文脈自由で、全域な PEG を持たない**（標準の 3 公理だけ）。
  成果物が公理にしていた Greibach の定理と逆像の閉包を、このリポジトリの `Cfg/Greibach/` の証明を写して置き換えた
  （`greibachWitness`、`greibachWitness_nonerasing`、`recognizedByTotalPEG_inverseImage_nonerasing`）。

注意: これは「全域な PEG」についての答え。このリポジトリの `IsPEL`（止まらない文法も許し、止まらない入力は受理しない）で
同じことが言えるかは、全域でない PEG の言語が全域な PEG で書けるかに依る。
