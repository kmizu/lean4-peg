# 止まらない文法も許した PEG の言語は、全域な PEG の言語と一致する

`isPEL_iff_isTotalPEL : IsPEL L ↔ IsTotalPEL L`（`lean/Shallot/Peg/Total/`）。

## 文献
- Ford (POPL 2004) §5: 「Birman の gTS 変換を拡張すれば、任意の PEG を完全な PEG に変換できる」と書くが、証明はない。
  Ford 自身は整形式性の判定を「未検証」と呼んでいる。
- Rubtsov–Chudinov はこれを Ford が示したと書くが、Ford の論文には証明がない。
- Loff–Moreira–Reis (JCSS 2020) は PEG の言語クラスを全域な PEG で定義していて、この同値は扱わない。
- Birman の 1970 年の学位論文は入手できなかった。
→ 既知の主張だが PEG での証明が見当たらないので、自分で構成して証明した。

## 構成（Birman の実行時の循環検査）
- 非終端記号に、今の位置で開いている非終端記号の集合 `S`（ビットマスク）を付ける。`A ∈ S` の呼び出しはループとして報告し、
  文字を食べたら `S` を空に戻す。
- 各式に三つの変換を作る: 食べずに成功（z）、食べて成功（p）、ループ（l）。`r = z / p`、失敗は `fl = !r !l`。
  繰り返しは `p a S · (p a ∅)* · fl a ∅ / fl a S`。
- 仕様（`spec_all`）は入力の長さ、まだ開いていない規則の数、式の順の帰納法。ループの検出の正しさは
  高さで抑えた導出（`DH`）と無限降下（`no_self`）で示す。

## 結果
- `newG_accepts`: 変換した文法は元と同じ語を受理する。
- `newG_allNtTotal`: 変換した文法は全ての非終端記号が全ての入力で止まる（`isPEL_allNtTotal`）。
- 系（別リポジトリ kmizu/peg-separation-axiom-free）: この構成を写し、Kim–Park の全域 PEG への翻訳と系 5.11 を合わせて
  `greibachHardest_not_PEL : ¬ IsPEL L0`。Greibach の最難言語は、止まらない文法を許しても PEG で書けない。
