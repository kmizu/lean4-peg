# 回文 PEG の存在証明を Lean 4 で形式化するための調査（2026-09-07）

読み専用の調査。repo のコードは変更していない。対象読者は `STATUS.md` §5A の
「証明トラック」を実際に始める人。批評者の指摘（「PAL ∈ PEG の*存在*は既発表結果の
鎖から従う。Lean 4 で形式化せよ」）を、形式化できる粒度まで精密化し、必要な成果物を
特定した。引用は原文どおり、識別子は verbatim。本文で「未確認」と書いたものは、
本セッションで原典にアクセスできなかった（ACM / Springer / ScienceDirect が 403）事項。

## 0. 要約

- **存在の鎖**：Slisenko 1973 / Galil 1978（多テープ TM が全接頭辞の回文性を実時間で判定）
  → 実時間の規約の正規化（定数遅延 → 1 記号 1 遷移）→ Kim–Park 2026 の Lean 成果物
  `PegSeparation.RealTimeTM.toSCA_accepts_iff`（厳密実時間 TM → SCA）→
  `PegSeparation.SCAToPEG.loffBackward`（SCA → total PEG、ただし**反転**言語）→ PAL^R = PAL。
- **定理になっていない環は二つ**。(a) Galil の機械を Kim–Park の `RealTimeTM.Machine`
  として書き下し `∀ w, M.Accepts w ↔ w ∈ PAL` を証明すること——どこにもない。
  (b) 「定数遅延の実時間」から「1 記号 1 遷移、各テープ 1 書き込み 1 移動」への正規化——
  Lean にはなく、紙の上でも Hartmanis–Stearns 流の tape compression の folklore で、
  本セッションでは原典の定理番号まで確認できなかった（§1.3）。
- **厳密実時間 TM から先は全部 Lean で証明済み**。成果物の `Closure/PrefixPEG.lean`
  `pref_isPEG`（52 行）がそのまま `pal_in_peg` の雛形になる。条件付き定理（「PAL を認識する
  厳密実時間 TM があれば PAL を認識する total PEG がある」）は 1 日仕事（§4）。
- **成果物はビルドできる**。Lean `v4.31.0` + Mathlib `v4.31.0`。`lake exe cache get` 後、
  関係 22 モジュールが 2 分 31 秒でビルド（エラー 0、linter 警告 91 行）。この repo は
  `v4.32.0` で Mathlib 非依存。橋渡しには別パッケージが要る（§3.6, §5）。
- **成果物の PEG は noncomputable**。`SCAToPEG.grammar` は SCA の近傍（radius-2 の木）
  ごとに非終端を持ち `Fintype.equivFin` で番号付けする**存在証明**。13M 規則ファイルのような
  具体的文法は出てこない。「存在する」と「ここにある」の区別は Lean 上でも残る（§3.4）。
- **Galil の算法自体の形式化**：成果物の玩具機械（2 テープ 15 状態 5 記号の copy-and-compare）
  ですら定義 362 行＋正しさ 850 行。Galil 相当（この repo の `delayed_pal.py` 系の再構成）は
  8k–15k 行、一人で 4–9 か月が妥当な見積もり（§6）。
- **Zenn ドラフトの二つの論拠**（SCC 解析、入力長パラメータなし）は、いずれも「特定の有限展開
  仮説の否定」であって「全長さで正しい」ことの根拠にはならない（§7 に引用と理由）。
  なお当該 URL（`zenn.dev/nextbeat/articles/2026-09-plain-peg-palindromes`）は**未公開**
  （ページ・API とも 403、著者と publication の公開一覧に不在、ローカルは `published: false`）。

## 1. 主張の鎖（出典つき）

### 1.1 鎖の全体

```
(1) PAL の全接頭辞を実時間で判定する多テープ TM が存在する
        Slisenko 1973 / Galil 1978
(2) 実時間（定数遅延）TM ⇒ 厳密実時間 TM（1 記号につき 1 遷移、各テープ 1 書き込み・1 移動）
        Hartmanis–Stearns 1965 流の tape compression（folklore、§1.3）
(3) 厳密実時間 TM が L を認識 ⇒ SCA が L を判定
        Kim–Park 2026、成果物 RealTimeTM.toSCA_accepts_iff / recognizedBySCA_of_recognizedBy
(4) SCA が L を判定 ⇒ total PEG が L^R を認識
        LMR 2020 Theorem 16（十分方向）、成果物 SCAToPEG.loffBackward
(5) PAL^R = PAL
        List.reverse_reverse
∴ PAL ∈ PEG。偶数長回文 {w w^R} も PEG（正則言語 (ΣΣ)* との共通部分：
   成果物 Closure.recognizedByTotalPEG_inter, Closure.recognizedByTotalPEG_of_isRegular）
   ⇒ LMR Conjecture 7 は偽。
```

### 1.2 環 (1)：Slisenko 1973 / Galil 1978

- Z. Galil, *Palindrome recognition in real time by a multitape Turing machine*,
  J. Comput. Syst. Sci. 16(2), 1978, pp. 140–157, doi:10.1016/0022-0000(78)90042-9。
  本文は本セッションから読めない（ScienceDirect 403。repo にも `Galil.pdf` は持ち込まない方針、
  `STATUS.md` §6）。検索エンジンの要約によれば「入力の最小の非自明な initial palindrome を
  見つける実時間 TM 算法を構成し、小さな変更で全ての initial palindrome を見つける実時間 TM
  算法が得られる」。**「全ての initial palindrome を見つける」＝各接頭辞について回文か否かを
  オンラインに出力する**、これが PAL 認識の意味で必要な性質。
- 原結果は A. O. Slisenko, *Recognition of palindromes by multihead Turing machines*,
  Proc. Steklov Inst. Math. 129 (1973) 30–202（露語；英訳 AMS 1976, pp. 25–208）。
  Galil 1978 はその簡略証明。Slisenko 自身の簡略版：*A simplified proof of the real-time
  recognizability of palindromes on Turing machines*, J. Soviet Math. 15 (1981) 68–77。
- 関連：Z. Galil, *Real-time algorithms for string-matching and palindrome recognition*,
  STOC 1976, doi:10.1145/800113.803644；Z. Galil, *On converting on-line algorithms into
  real-time and on real-time algorithms for string-matching and palindrome recognition*,
  SIGACT News 7(4), 1975, doi:10.1145/990502.990505（表題どおり「オンライン算法を実時間化する」
  一般手法＝predictability による buffering。この repo の `GALIL_CLOCK.md` が再導出している
  「次の k/4 個の答えは 0」「FIFO を 1 ラウンドあたり 2c で消化」がこれ）。

**厳密実時間モデルでの「全接頭辞」について**。Kim–Park の `Machine` は決定的で停止せず、
1 記号につきちょうど 1 遷移する。`Accepts w` は「w をすべて読んだ直後の状態が受理状態」
（§3.1）。したがって同じ機械が任意の接頭辞 w' についても `Accepts w'` を決めており、
「PAL を認識する」＝「全接頭辞の回文性をオンラインに答える」が**自動的に**成り立つ。
Galil の「全 initial palindrome を出力」という追加要求は、厳密実時間モデルでは追加ではない。

### 1.3 環 (2)：実時間の規約と定数遅延の正規化

文献の「実時間」は多くの場合**定数遅延**を指す。Jiang–Seiferas–Vitányi（JAMS 1997、
arXiv:cs/0110039 で本文確認）脚注 1：

> On-line recognition requires a verdict for each input prefix before the next input symbol
> is read, and real-time recognition is on-line recognition with some constant delay bound on
> the number of steps between the reading of successive input symbols.

LMR 2020 の Definition 22 / Online(t(n)) も同型（「the computation M(x) does at most t(n)
steps between each input symbol read」）。一方 Kim–Park は Lemma 5.3 の証明で**厳密**版を
明示している（arXiv HTML で確認）：

> We recognize Pref^R by a two-tape Turing machine that is *strictly real time*: it consumes
> one input symbol per step and never pauses. […] A strictly real-time machine with t tapes
> compiles into a scaffolding automaton of degree 3t and radius 2, three pointer roles being
> reserved for each tape and a transition inspecting only a radius-2 neighbourhood of the
> current top.

成果物の `RealTimeTM.Machine`（§3.1）はこの厳密版で、さらに各遷移で各テープが**ちょうど
1 回書き 1 回動く**（`TapeAction`）。Galil の機械は定数遅延（＋predictability による償却）で
書かれているので、鎖を閉じるには

- (2a) 償却線形時間のオンライン算法 → 定数遅延（Galil 1975/1978 の predictability + FIFO；
  数学的には環 (1) の内側。この repo は `GALIL_CLOCK.md` で定数込みに再導出している）、
- (2b) 定数遅延 d → 厳密実時間（tape compression）

の両方が要る。(2b) の引用候補（**いずれも本セッションでは書誌情報のみ確認、定理番号は未確認**）：

- J. Hartmanis, R. E. Stearns, *On the computational complexity of algorithms*,
  Trans. AMS 117 (1965) 285–306 —— 線形加速（tape compression）の原典。二次文献は
  「入出力に関する部分を除いて定数倍加速できる」と要約する。
- A. L. Rosenberg, *Real-time definable languages*, J. ACM 14(4) (1967) 645–662 ——
  決定的多テープ実時間言語クラスの標準文献（LMR も [39] として下界法に引用）。
- P. C. Fischer, A. R. Meyer, A. L. Rosenberg, *Real-time simulation of multihead tape units*,
  J. ACM 19(4) (1972) 590–607；同 *Time-restricted sequence generation*, JCSS 4 (1970) 50–73
  （列生成については実時間＝線形時間の同値を観察）。
- R. V. Book, S. A. Greibach, *Quasi-realtime languages*, Math. Systems Theory 4 (1970) 97–111
  （非決定的定数遅延クラス）。
- P. M. B. Vitányi, *On the power of real-time Turing machines under varying specifications*,
  ICALP 1980, LNCS 85 —— 規約の取り方で能力が変わり得ることを扱う。正規化を「自明」と
  済ませないための注意文献。
- M. O. Rabin, *Real time computation*, Israel J. Math. 1(4) (1963) 203–211；
  J. Bečvář, *Real-time and complexity problems in automata theory*, Kybernetika 1(6) (1965) 475–497。

**形式化に必要な (2b) の中身**（Lean で書く場合の設計。文献の定理をそのまま使うのではなく、
Kim–Park のモデルに合わせて自前で証明することになる）：

1. 遅延 d の機械 `DelayedMachine`：1 記号につき高々 d 個のマイクロステップ（各々 1 書き込み
   1 移動/テープ）を決定的に実行してから次の記号を読む。
2. 厳密機械への変換：テープの 1 セルに旧セル B = 2d 個のブロックを詰め、有限制御に
   「現在ブロックとその両隣」を保持。1 遷移で「記号を読んだ直後から次の読みの直前まで」の
   ≤ d マイクロステップを模倣する。ヘッド移動は ≤ d なので 3 ブロック窓を出ず、
   厳密機械の 1 遷移あたりのテープ移動は高々 1 ブロック。
3. `Accepts` の一致（模倣不変量）。

規模は 1–2k 行。**代替**：Galil の機械を最初から厳密規約で設計する。この repo の構成
（`scaffold_window_pal.py`、`GALIL_CLOCK.md` の「FIFO 2c/ラウンド」）はまさにこれで、
(2) は独立した環ではなくなり、その証明義務（締切不等式）は環 (1) に移る。

補足：LMR §5.3 は「SCA は実時間モデルと見なせる。PEG の反転はすべて実時間 TM で認識できると
予想したが、これは demonstrably false」（Theorem 23）と述べるのみで、**逆向き（実時間 TM ⊆ SCA）
は定理として述べていない**。紙の上でこの環を述べているのは Kim–Park の上記 1 文だけであり、
Formal Verification 節の対応表にも一般定理の行はない（Lemma 5.3 の行は
`Closure.cFirst_isSCA_degree_six_radius_two`）。Lean 上では `toSCA_accepts_iff` が一般定理
として証明されている。「既発表」の重みは、この環については Lean 成果物に依っている。

### 1.4 環 (3)：Kim–Park 2026 と Lean 成果物

- **論文**：Jungyeom Kim, Jihyeok Park, *Separating Parsing Expression Grammars using
  Cell-Probe Lower Bounds*, arXiv:2608.29592 [cs.PL; cs.CC; cs.FL], v1 submitted
  Sun, 30 Aug 2026 06:27:15 UTC, doi:10.48550/arXiv.2608.29592。
  Zenn ドラフトの参考文献は「J. Kim, S. Park」とするが、第二著者は Jihyeok Park
  （Korea University、ORCID 0000-0001-8387-1984）で頭文字は J。要修正。
- **Abstract**（arXiv HTML より verbatim）：

  > We resolve three open problems concerning parsing expression grammars (PEGs). We construct
  > a single language C satisfying C ∈ LIN ∩ PEG and C^R ∈ LIN ∖ PEG. This proves that some
  > linear context-free language is not a PEG language and that PEG languages are not closed
  > under reversal, confirming a conjecture of Loff, Moreira, and Reis. Factoring the same
  > witness resolves the concatenation-closure problem of Rubtsov and Chudinov negatively, in
  > the strong form PEG · REG ⊈ PEG despite REG · PEG ⊆ PEG. It also refutes closure under
  > Kleene star, homomorphisms, and substitutions. Our main technique converts scaffolding
  > automata (SCAs), which characterize reversals of PEG languages, into dynamic data
  > structures in the cell-probe model. For any suitably local serialization of a problem with
  > preprocessing, updates, and a final Boolean query, an SCA recognizer yields an exact
  > deterministic cell-probe data structure whose operation costs are proportional to the
  > corresponding encoding lengths. Cell-probe lower bounds can therefore prove SCA
  > non-membership and, by reversal, PEG non-membership. We apply this transfer to Multiphase
  > Inner Product using one-symbol update blocks and a query suffix of length O(log n), while
  > keeping both the language and its reversal linear context-free. Ko's cell-probe lower
  > bound then yields the witness above. The arguments are additionally formalized in Lean 4.

- **序論の回文への言及**（§1、verbatim）：

  > Loff, Moreira, and Reis asked whether the language of palindromes has a PEG, observing
  > that none was known even for that comparatively simple language [12]; our witness is
  > instead a language built for the reduction below.

  つまり Kim–Park 自身は「回文の PEG は不明」と述べており、PAL ∈ PEG を主張していない。
  彼らの結果から PAL ∈ PEG が「従う」のは、Galil を持ち込んだ場合だけである。
- **Theorem 2.10**（PEG–SCA characterization、LMR Theorem 16 の再掲）：
  「For every language L ⊆ Σ*, L ∈ PEG ⟺ L^R ∈ SCA.」Remark 2.11：「The accompanying
  artifact proves both directions in full and checks them in Lean.」
- **Definition 2.4/2.5**：PEG の意味論は判定 `G ⊢ e, w ⇓ r`（r ∈ Σ* ∪ {fail}、r は残りの
  接尾辞）、`L(G) = {w : G ⊢ S, w ⇓ ε}`、`PEG = {L(G) : G is a total PEG}`、
  total＝「for every e ∈ E(N,Σ) and every w ∈ Σ*, there exists r ∈ Σ* ∪ {fail} such that
  G ⊢ e, w ⇓ r」。
- **Lean 成果物**：
  - Zenodo record 22099762、doi:10.5281/zenodo.22099762、*Separating Parsing Expression
    Grammars using Cell-Probe Lower Bounds: Lean Artifact*, version 0.1.0, published
    2026-08-25, Apache License 2.0, file `kimjg1119/peg-separation-artifact-v0.1.0.zip`
    (353.6 KB)。
  - GitHub: <https://github.com/kimjg1119/peg-separation-artifact> tag `v0.1.0`、
    commit `c364edb` "Release Lean artifact v0.1.0"（唯一のコミット）。
  - `lean-toolchain`: `leanprover/lean4:v4.31.0`。`lakefile.toml`: パッケージ名
    `PegSeparation`、`[[require]] name = "mathlib" rev = "v4.31.0"`、`relaxedAutoImplicit = false`。
    `lake-manifest.json` の mathlib rev `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`（推移依存：
    batteries, aesop, Qq, proofwidgets, importGraph, LeanSearchClient, plausible, Cli）。
  - 規模：`.lean` 152 ファイル、38,034 行、ソース 2.0 MB。うち本調査に関係する層は
    `Common/Compiler/RealTimeTM` 937 行、`Common/Compiler/SCAToPEG` 2,562 行、
    `Common/Model` 530 行、`Common/Loff` 598 行、`Closure` 4,573 行。残り（`CFLNotPEG/External/`
    の Larsen–Yu / Ko の cell-probe 下界）が本体の大半。
  - `README.md`：Apple M2 Max で `lake exe cache get` 約 15 分、`lake build` 約 4 分。
    入口は `PegSeparation/CFLNotPEG/Main.lean` と `PegSeparation/Closure/Main.lean`
    （`#print axioms` を出力）。`axioms/*.txt` に 2026-08-11 生成の出力あり。
  - 論文の Formal Verification 節：「Standard means that only Lean and mathlib's foundational
    axioms (propext, Classical.choice, Quot.sound) are reported. Exactly three further axioms
    occur above」（Ko の下界、Birman–Ullman＋Ford の逆準同型閉包、Greibach の最難言語）。
    「Every positive result in the table is proved outright.」——環 (3)(4) に必要な
    `toSCA_accepts_iff`、`loffBackward`、`loffForwardRepaired` は `axioms/cflnotpeg.txt` /
    `closure.txt` で標準 3 公理のみ。
  - 同節「Generative AI Usage」：「A generative AI tool based on a large language model was
    used to examine the witness language and preliminary proof outlines and to generate all
    Lean 4 proof scripts in the accompanying formal-verification artifact.」
- Zenn ドラフトの「Kim–Park（2026）は実時間多テープチューリング機械を SCA に変換する
  コンパイラを作り、その正しさを Lean で機械検証しました」は成果物については正しいが、
  論文本文では Lemma 5.3 の証明中の 1 文にしか現れない（上記）。

### 1.5 環 (4)：Loff–Moreira–Reis 2020

- B. Loff, N. Moreira, R. Reis, *The computational power of parsing expression grammars*,
  arXiv:1902.08272（本文確認は **v2, 14 Feb 2020**）；JCSS 版は ScienceDirect
  PII S002200002030012X（2020）。先行版 DLT 2018 (LNCS, doi:10.1007/978-3-319-98654-8_40)。
  以下の番号は arXiv v2 のもの。Kim–Park が「[12, Theorem 16]」と引くので同じ番号付け。
  JCSS 版の番号は未確認。
- **序論**（p.3、verbatim）：

  > But no PEG is known, even for the much simpler language of palindromes. The following
  > questions are both open:
  > Can a parsing expression grammar recognise the language of palindromes?
  > Is there any linear-time language without a parsing expression grammar?

- **Conjecture 7**（§3.2、verbatim）：

  > One may get a sense for the limitations of parsing expression grammars when trying to
  > produce a PEG for recognising palindromes. One quickly comes to the conjecture that PEGs
  > cannot find the middle bit of the input. In the case of palindromes, we make the following
  > conjecture:
  > **Conjecture 7.** The language of even-length palindromes has no PEG, i.e.
  > P = {ww^r | w ∈ {0,1}*} ∉ PEG.

  直後の Theorem 8：「The language of palindromes of power-of-two length has a PEG」。
  注意：Conjecture 7 は**偶数長**についての予想。PAL ∈ PEG から P ∈ PEG を出すには
  正則言語 (ΣΣ)* との共通部分を取る（Kim–Park Lemma 5.4「The class PEG contains REG and is
  closed under union, intersection, and complement」、成果物 `Closure.recognizedByTotalPEG_inter`
  (`Closure/BooleanClosure.lean:394`) と `Closure.recognizedByTotalPEG_of_isRegular`
  (`Closure/RegularToPEG.lean:78`)）。
- **Definition 3/4**：`Rec_G` は部分関数、「G is total if its recognition map is total, i.e.
  if it never enters an infinite loop, on any input」；「A total PEG G is said to recognise the
  language L(G) = {x ∈ Σ* | Rec_G(S, x) = x}. Then PEG is the class of languages recognised by
  total PEGs.」
- **Definition 12**（SCA）：`A = ⟨Σ, d, Γ, k, Q, δ, q0, F⟩`、
  `δ : Q × Σ × N_k(d,Γ) → Q × Γ × ([d)^{≤k} ∪ {SELF, ∅})^d`。Definition 15：受理は最終状態
  `q_n ∈ F`。
- **Theorem 16**（verbatim）：「A language L ⊆ Σ* is in PEG if and only if its reverse L^r is
  decided by some scaffolding automaton.」直後：「The question of whether PEG languages are
  closed under reverse now arises quite naturally. We conjecture that they are not」（これが
  Kim–Park の解決した予想）。
- **§5.3**（verbatim）：「Because scaffolding automata are machines which read a single input
  symbol at a time, and which do only a constant number of operations per symbol read, they
  can be thought of as a real-time computational model. This led us to conjecture that the
  reverse of any language in PEG could be recognised by a real-time Turing machine. However
  this conjecture turns out to be demonstrably false.」Theorem 23：PEG 言語で、それも反転も
  Online(o(n/(log n)²)) に入らないものがある。

### 1.6 環 (5)：PAL^R = PAL

`w.reverse ∈ PAL ↔ w ∈ PAL` は `List.reverse_reverse` と `eq_comm` で 1 行。Mathlib には
`List.Palindrome`（`Mathlib/Data/List/Palindrome.lean:42`、`iff_reverse_eq` :63）がある。

## 2. どの環がまだ定理でないか

| 環 | 内容 | Lean（成果物） | Lean（Mathlib） | Lean（この repo） | 紙 |
|---|---|---|---|---|---|
| (1) | Galil の機械が全接頭辞の PAL を判定 | **なし** | なし（`Turing.TM0/TM1/TM2` はオンライン・実時間モデルではない） | なし（Python 再構成と有限テストのみ） | Slisenko 73 / Galil 78 |
| (2b) | 定数遅延 → 厳密実時間 | **なし** | なし | なし | folklore（H–S 65、定理番号未確認） |
| (3) | 厳密実時間 TM → SCA | `RealTimeTM.toSCA_accepts_iff` | — | — | Kim–Park Lemma 5.3 証明中の 1 文 |
| (4) | SCA → total PEG（反転） | `SCAToPEG.loffBackward` | — | — | LMR Thm 16 |
| (5) | PAL^R = PAL | 自明 | `List.reverse_reverse` | — | — |
| Conj.7 | 偶数長への制限 | `Closure.recognizedByTotalPEG_inter` + `_of_isRegular` | `Language.IsRegular` (`Mathlib/Computability/DFA.lean:354`) | — | Kim–Park Lemma 5.4 |

**結論**：Lean 上で欠けているのは (1) と (2b) だけであり、(2b) は Galil の機械を厳密規約で
直接書けば消える。したがって「PAL ∈ PEG の Lean 証明」＝「厳密実時間 `RealTimeTM.Machine` で
PAL を認識する機械を定義し `Accepts` の同値を証明する」に帰着する。

## 3. 成果物の中身（定義と定理、file:line）

パスは成果物ルート `PegSeparation/` からの相対。クローンは
`/tmp/claude-1000/-home-mizushima-repo-lean4-peg/bcf2652f-5135-4b82-a33e-b9555d637fc5/scratchpad/kimpark`。

### 3.1 実時間 TM（`Common/Compiler/RealTimeTM/Model.lean`）

- `Move` (6–10): `left | stay | right`。`TapeAction symbolCount` (12–14): `write : Fin symbolCount`,
  `move : Move`。`Instruction tapeCount stateCount symbolCount` (16–18): `nextState`,
  `tapeAction : Fin tapeCount → TapeAction symbolCount`。
- `TapeConfiguration symbolCount` (20–24): ジッパー `left : List (Fin symbolCount)`,
  `focus : Fin symbolCount`, `right : List (Fin symbolCount)`。`applyAction blank tape action`
  (38–58): `stay` は focus を上書き、`right` は `write :: left` へ push して right から pop
  （空なら blank）、`left` は対称（左端で `left = []` なら動かず上書きのみ）。
- `Machine (Terminal : Type) (tapeCount stateCount symbolCount : ℕ)` (105–112):

  ```lean
  structure Machine (Terminal : Type) (tapeCount stateCount symbolCount : ℕ) where
    tapeCount_pos : 0 < tapeCount
    blank : Fin symbolCount
    initialState : Fin stateCount
    accepting : Finset (Fin stateCount)
    transition :
      Fin stateCount → Terminal → (Fin tapeCount → Fin symbolCount) →
        Instruction tapeCount stateCount symbolCount
  ```

  入力テープはなく、記号は `transition` の引数として渡る。遷移は状態・記号・各テープの
  focus だけを見る。
- `step` (127–135)、`run input := input.foldl machine.step machine.initialConfiguration` (137–139)、
  `Accepts input : Prop := (machine.run input).state ∈ machine.accepting` (141–143)、
  `RecognizedBy language := ∃ tapeCount stateCount symbolCount machine, ∀ input,
  machine.Accepts input ↔ input ∈ language` (159–162)。`Terminal` は任意の `Type`。

**「認識する」の意味**：決定的、停止なし、1 記号 1 遷移、各テープ 1 書き込み 1 移動。
`Accepts` は入力を全部読んだ直後の状態のみで決まる。終端記号・入力長の事前知識なし。
prefix-closed の要請はないが、§1.2 のとおり同じ機械が全接頭辞を判定する。

### 3.2 SCA（`Common/Model/Scaffolding.lean`）

- `Neighborhood WorkLabel degree : Nat → Type` (8–11): radius 0 は `Option WorkLabel`、
  radius+1 は `Option WorkLabel × (Fin degree → Option (Neighborhood … radius))`。
- `Node` (13–15): `label : Option WorkLabel`, `edgeOffset : Fin degree → Option Nat`
  （**相対オフセット**、`some 0` が SELF）。`Scaffold` (17–19): `top`, `older : List Node`。
- `LocalTarget degree radius` (55–58): `missing | self | path (directions : List (Fin degree))
  (withinRadius : directions.length ≤ radius)`。`Action` (60–63): `nextState`, `newLabel`,
  `target : Fin degree → LocalTarget`。
- `Automaton (Terminal : Type) (stateCount workLabelCount degree radius : Nat)` (65–70):
  `degreePositive`, `initialState : Fin stateCount`, `accepting : Finset (Fin stateCount)`,
  `transition : Fin stateCount → Terminal → Neighborhood (Fin workLabelCount) degree radius →
  Action …`。
- `extendScaffold` (80–91)、`step` (93–99)、`run := foldl` (101–104)、
  `Accepts input := (automaton.run input).1 ∈ automaton.accepting` (106–108)。
- `Common/Recognition.lean:14–18` `RecognizedBySCA language := ∃ stateCount workLabelCount degree
  radius automaton, ∀ input, automaton.Accepts input ↔ input ∈ language`。

LMR Definition 12 との差：ラベルは `Fin workLabelCount`、辺は相対オフセット、初期足場は
1 ノード（label `none`）。意味は同じ。

### 3.3 PEG 構文・意味論（`Common/Model/PEG.lean`）

```lean
inductive ParsingExpression (Terminal : Type) (nonterminalCount : Nat) where
  | empty | failure | terminal (symbol : Terminal) | nonterminal (name : Fin nonterminalCount)
  | sequence (left right : …) | orderedChoice (left right : …)
  | notPredicate (body : …) | andPredicate (body : …)                       -- 6–14
structure PegGrammar (Terminal : Type) (nonterminalCount : Nat) where
  rule : Fin nonterminalCount → ParsingExpression Terminal nonterminalCount
  start : Fin nonterminalCount                                               -- 16–18
inductive ParseResult (Terminal : Type) where
  | failure | success (remaining : List Terminal)                             -- 20–23
inductive Evaluates [DecidableEq Terminal] (grammar : PegGrammar Terminal n) :
    ParsingExpression Terminal n → List Terminal → ParseResult Terminal → Prop  -- 34–70
def IsLoffTotal … : Prop := ∀ expression input, ∃ result, Evaluates grammar expression input result  -- 72–75
def Recognizes … (input) : Prop := Evaluates grammar (.nonterminal grammar.start) input (.success [])  -- 77–79
```

`Common/Recognition.lean:7–12`：
`RecognizedByTotalPEG language := ∃ nonterminalCount grammar, grammar.IsLoffTotal ∧
∀ input, grammar.Recognizes input ↔ input ∈ language`（`[DecidableEq Terminal]`）。

- `star`・`any`・文字クラス・文字列リテラルは**ない**（LMR Definition 1 どおり）。`failure` は
  プリミティブ。`andPredicate` もプリミティブ。
- 「認識」は開始非終端が入力を**全部消費して**成功すること。`!.` は不要。
- 意味論は Ford 流の帰納的関係で部分的（左再帰には導出がない）。決定性は
  `Common/Loff/Semantics.lean:15` `evaluates_deterministic`
  （namespace `PegSeparation.External.LoffForwardRepaired.PegGrammar`）。
- ステップ数の概念はない。totality の証明は `SCAToPEG/Final.lean:23–30` の整礎測度
  `nameMeasure` による帰納法で、操作的コストではない。実行器（fuel 付き interpreter）もない。

### 3.4 定理

- `Common/Compiler/RealTimeTM/ToSCA.lean:221–236`

  ```lean
  noncomputable def toSCA {Terminal : Type} {tapeCount stateCount symbolCount : ℕ}
      (machine : Machine Terminal tapeCount stateCount symbolCount) :
      Automaton Terminal
        (CompiledStateCount tapeCount stateCount symbolCount)   -- = card (Fin stateCount × (Fin tapeCount → Fin symbolCount))
        (CompiledLabelCount tapeCount symbolCount)              -- = card (Fin tapeCount → Option (Fin symbolCount))
        (CompiledDegree tapeCount) 2                            -- degree = card (Port tapeCount) = 3·tapeCount, radius 2
  ```

  `Port` (9–13) は `left | right | tail` × テープ。テープのジッパーを SCA の永続スタックに写す。
- `Common/Compiler/RealTimeTM/Correctness.lean:512–520`

  ```lean
  theorem toSCA_accepts_iff
      (machine : Machine Terminal tapeCount stateCount symbolCount)
      (input : List Terminal) :
      (toSCA machine).Accepts input ↔ machine.Accepts input
  ```

  同 522–534 `recognizedBySCA_of_recognizedBy {language} (recognized : RecognizedBy language) :
  ∃ scaStateCount scaLabelCount degree radius automaton, ∀ input, automaton.Accepts input ↔
  input ∈ language`。不変量は `Represents` (40–52)：制御状態＋各テープ focus をエンコードした
  SCA 状態と、左右スタックを表す `tail` ポインタ鎖。
- `Common/Compiler/SCAToPEG/Statements.lean:8–17`

  ```lean
  abbrev LoffBackwardStatement : Prop :=
    ∀ {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
      {stateCount workLabelCount degree radius : Nat}
      (automaton : Scaffolding.Automaton Terminal stateCount workLabelCount degree radius),
      ∃ (nonterminalCount : Nat) (grammar : PegGrammar Terminal nonterminalCount),
        grammar.IsLoffTotal ∧ ∀ input, automaton.Accepts input ↔ grammar.Recognizes input.reverse
  ```

  `Common/Compiler/SCAToPEG/Final.lean:88–89` `theorem loffBackward : LoffBackwardStatement`
  （本体は `loffBackwardStatement` 75–80、`automaton_accepts_iff` 68–73、
  `grammar_isLoffTotal` 63–66）。**アルファベットに `[Fintype Terminal]` が要る**
  （`Construction.lean:87` `anyTerminal` を全記号の選択で作るため）。
- 逆方向 `CFLNotPEG/External/Statements.lean:9–17` `LoffForwardStatement`（total PEG →
  反転を判定する SCA）、`CFLNotPEG/Main.lean:12` `loffForwardRepaired` で証明済み。
  本件には不要。
- **文法は noncomputable**：`SCAToPEG/Construction.lean:9` `noncomputable section`、
  非終端名 (32–39)

  ```lean
  inductive Name (stateCount workLabelCount degree radius : Nat) where
    | state (control : Fin stateCount) | label (work : Fin workLabelCount)
    | hood (view : Neighborhood (Fin workLabelCount) degree radius)
    | path (directions : BoundedPath degree radius) | consumeAll | accepts
  ```

  を `Fintype.equivFin` で `Fin (NameCount …)` に番号付けする (41–57)。`hood` は radius-2 の
  ラベル付き木**すべて**に非終端を割り当てるので、`toSCA` の出力（degree 3t、ラベル
  `Fin t → Option (Fin k)`）に対しては天文学的な非終端数になる。これは存在証明であり、
  `#eval` や抽出で具体的文法を得る道ではない。`symbolic_sca2peg.py` の射出（欄 1 個＝規則 1 個、
  参照＝`. X`）とは別の符号化。**STATUS.md §5A の③（射出の translation validation）は、
  成果物を持ってきても消えない。**
- **雛形**：`Closure/PrefixPEG.lean:36–50`

  ```lean
  theorem cFirst_isSCA : PegSeparation.RecognizedBySCA CFirst :=
    PegSeparation.RealTimeTM.recognizedBySCA_of_recognizedBy cFirst_recognizedBy
  theorem pref_isPEG : PegSeparation.RecognizedByTotalPEG Pref := by
    obtain ⟨stateCount, workLabelCount, degree, radius, automaton, decides⟩ := cFirst_isSCA
    obtain ⟨nonterminalCount, grammar, total, recognizes⟩ :=
      PegSeparation.SCAToPEG.loffBackward automaton
    refine ⟨nonterminalCount, grammar, total, ?_⟩
    intro input
    calc
      grammar.Recognizes input ↔ automaton.Accepts input.reverse := by
        simpa using (recognizes input.reverse).symm
      _ ↔ input.reverse ∈ CFirst := decides input.reverse
      _ ↔ input ∈ Pref := Iff.rfl
  ```

  `cFirst_recognizedBy` (`Closure/PrefixMachineCorrectness.lean:846–848`) は
  `⟨2, 15, 5, prefixMachine, …⟩`、`prefixMachine : Machine Terminal 2 15 5`
  (`Closure/PrefixMachine.lean:269–279`) は抽象機械 `absTrans`（状態 `St` 15 個、記号 `Sym` 5 個）
  を `stToFin`/`symToFin` で `Fin` に写したもの。

### 3.5 ビルド

本セッションで実施（WSL2、既存 elan に `v4.31.0` あり）：

```
git clone https://github.com/kimjg1119/peg-separation-artifact kimpark   # c364edb, tag v0.1.0
lake exe cache get      # mathlib 等の clone 数分 + "Decompressed 8538 already-cached file(s)  Completed successfully in 73701 ms"  EXIT 0
timeout 1200 lake build PegSeparation.Common.Compiler.RealTimeTM.Correctness \
                        PegSeparation.Common.Compiler.SCAToPEG.Final
#   22 モジュール Built（Model.PEG 56s, Scaffolding 57s, RealTimeTM.Model 57s, …, SCAToPEG.Final 6.8s）
#   215.95s user 61.66s system 183% cpu 2:31.30 total, BUILD EXIT 0, error 0, warning 91 行（unusedFintypeInType 等）
```

`Common/` 以下の Mathlib import は `import Mathlib`（全体）なので、初回は Mathlib の olean 取得が
支配的。二つの主要定理は本環境で検査済み。

### 3.6 この repo との toolchain 互換

- repo `lean/lean-toolchain`：`leanprover/lean4:v4.32.0`。`lean/lakefile.toml`：`require` なし、
  `lake-manifest.json` `"packages": []`（Mathlib 非依存）。`autoImplicit = false`。
- 成果物：`v4.31.0` + Mathlib `v4.31.0`。Mathlib には `v4.32.0` タグが存在する
  （`81a5d257c8e410db227a6665ed08f64fea08e997`）。
- 一つの Lake ワークスペースは一つの toolchain なので、橋渡しは (i) 成果物を `v4.32.0` +
  Mathlib `v4.32.0` に上げる（linter/API 変更で修正が要る可能性）か、(ii) `v4.31.0` の
  第三のパッケージが成果物とこの repo の `Shallot` を両方 `require` する（`Shallot` は
  依存なしなので `v4.31.0` でもほぼそのままビルドできる見込み。要確認）か、
  (iii) `Shallot/Peg/Syntax.lean`・`Semantics.lean`（合計 182 行、依存なし）を橋パッケージに
  ベンダーする。**推奨は (ii) または (iii)**：成果物の証明は pin された Mathlib で検査された
  ものなので動かさない。

## 4. 最初に証明すべき Lean 命題

成果物の定義で書く。`Terminal := Fin 2`（`Fintype`・`DecidableEq` は Mathlib のインスタンス）。

```lean
import PegSeparation.Common.Compiler.RealTimeTM.Correctness
import PegSeparation.Common.Compiler.SCAToPEG.Final
import PegSeparation.Closure.BooleanClosure
import PegSeparation.Closure.RegularToPEG

open PegSeparation

/-- 二進回文言語。`Language α := Set (List α)`（Mathlib.Computability.Language）。 -/
def PAL : Language (Fin 2) := { w | w.reverse = w }

theorem PAL_reverse_mem (w : List (Fin 2)) : w.reverse ∈ PAL ↔ w ∈ PAL := by
  simp only [PAL, Set.mem_setOf_eq, List.reverse_reverse]; exact eq_comm

/-- 条件付き主定理（成果物だけで閉じる。`pref_isPEG` の写し）。 -/
theorem pal_in_peg_of_realTime {t s k : ℕ}
    (M : RealTimeTM.Machine (Fin 2) t s k) (hM : ∀ w, M.Accepts w ↔ w ∈ PAL) :
    ∃ (n : ℕ) (G : PegGrammar (Fin 2) n),
      G.IsLoffTotal ∧ ∀ w, G.Recognizes w ↔ w ∈ PAL := by
  obtain ⟨n, G, hT, hG⟩ := SCAToPEG.loffBackward (RealTimeTM.toSCA M)
  refine ⟨n, G, hT, fun w => ?_⟩
  calc G.Recognizes w ↔ (RealTimeTM.toSCA M).Accepts w.reverse := by
          simpa using (hG w.reverse).symm
    _ ↔ M.Accepts w.reverse := RealTimeTM.toSCA_accepts_iff M w.reverse
    _ ↔ w.reverse ∈ PAL := hM w.reverse
    _ ↔ w ∈ PAL := PAL_reverse_mem w

/-- 言語クラスの言い方。 -/
theorem pal_recognizedByTotalPEG (h : RealTimeTM.RecognizedBy PAL) :
    RecognizedByTotalPEG PAL := by
  obtain ⟨t, s, k, M, hM⟩ := h
  exact pal_in_peg_of_realTime M hM

/-- LMR Conjecture 7 の反駁（偶数長）。`EvenLength` は正則。 -/
def EvenLength : Language (Fin 2) := { w | Even w.length }
theorem evenLength_isRegular : EvenLength.IsRegular := sorry   -- 2 状態 DFA
theorem evenPal_in_peg (h : RecognizedByTotalPEG PAL) :
    RecognizedByTotalPEG (PAL ⊓ EvenLength) :=
  Closure.recognizedByTotalPEG_inter h (Closure.recognizedByTotalPEG_of_isRegular evenLength_isRegular)

/-- 本丸。これが環 (1)+(2)。 -/
theorem pal_recognizedBy : RealTimeTM.RecognizedBy PAL :=
  ⟨t, s, k, galilMachine, galilMachine_accepts_iff⟩   -- 未定義
```

必要な補題と所在：

| 補題 | 所在 | 状態 |
|---|---|---|
| `SCAToPEG.loffBackward` | `Common/Compiler/SCAToPEG/Final.lean:88` | あり |
| `RealTimeTM.toSCA_accepts_iff` / `recognizedBySCA_of_recognizedBy` | `Common/Compiler/RealTimeTM/Correctness.lean:512/522` | あり |
| `List.reverse_reverse` | Lean core | あり |
| `PAL_reverse_mem` | 新規 | 1 行 |
| `Closure.recognizedByTotalPEG_inter`, `Closure.recognizedByTotalPEG_of_isRegular` | `Closure/BooleanClosure.lean:394`, `Closure/RegularToPEG.lean:78` | あり（`[Fintype Terminal]`） |
| `EvenLength.IsRegular` | 新規（Mathlib `DFA` で 2 状態） | 数十行 |
| `galilMachine : RealTimeTM.Machine (Fin 2) t s k` と `∀ w, galilMachine.Accepts w ↔ w ∈ PAL` | **新規** | §6 |

条件付き定理までは 1 日以内。`pal_in_peg_of_realTime` の `Fin s` 状態は、Galil 級の機械を
直接 `Fin s` で書くのは不可能（制御状態が 2^(4 万) 級）なので、`prefixMachine` と同様に
構造体の抽象機械 `absStep` を先に定義し、`Fintype` な状態型から `Fintype.equivFin` で
`Fin s` に写す補題（成果物の `Machine` を有限状態型で一般化するか、`stToFin` 方式で写す）が
要る。noncomputable でよい。

## 5. この repo の PEG 意味論への橋

### 5.1 定義の対応

| | この repo (`lean/Shallot/Peg/`) | 成果物 (`Common/Model/PEG.lean`) |
|---|---|---|
| 式 | `PExp`: `eps, any, chr c, range lo hi, lit s, nt (i : Nat), seq, alt, star, notP`（`Syntax.lean:31–50`）；`andP := notP ∘ notP` | `ParsingExpression`: `empty, failure, terminal, nonterminal (Fin n), sequence, orderedChoice, notPredicate, andPredicate` |
| 文法 | `Grammar := {rules : List PExp, start : Nat}`；欠番は `ntMissing` で失敗（`Semantics.lean:52`） | `PegGrammar := {rule : Fin n → PE, start : Fin n}`（全域） |
| 入力 | `List Char`、比較は `beqChar`（codepoint） | `List Terminal`、`[DecidableEq Terminal]` |
| 結果 | `Outcome := fail \| ok (t : PTree) (rest)`（**構文木つき**） | `ParseResult := failure \| success remaining` |
| 意味論 | `Derives g e input o : Prop`（`Semantics.lean:19–88`、Ford 流、部分的） | `Evaluates grammar e input r : Prop`（同上） |
| 決定性 | `derives_det`（`Determinism.lean:21`、公理なし） | `evaluates_deterministic`（`Loff/Semantics.lean:15`） |
| 実行器 | `pegRun g fuel e input : Option Outcome`（`Interp.lean:19`）、`pegRun_sound` (`Soundness.lean:41`)、`pegRun_complete` (`Completeness.lean:25`)、`pegRun_mono` | なし（noncomputable、存在証明のみ） |
| totality | 述語なし（「no totality claim for all grammars」） | `IsLoffTotal` |
| ステップ数 | fuel が上界の代理 | なし（`nameMeasure` は整礎測度） |
| 認識 | 定義なし（`palGrammar_sound` 等は `Derives … (.ok t [])` を直接書く） | `Recognizes := Evaluates (nonterminal start) input (success [])` |

構成子は**同じではない**が、成果物 → repo は全射的に写せる：`empty ↦ eps`、
`failure ↦ notP eps`、`terminal a ↦ chr (enc a)`、`nonterminal i ↦ nt i.val`、
`sequence ↦ seq`、`orderedChoice ↦ alt`、`notPredicate ↦ notP`、`andPredicate ↦ notP (notP _)`。
逆方向（repo → 成果物）は `star`・`any`・`range`・`lit` を LMR Definition 1 の注のとおり
新しい非終端で展開する必要があり、本件には不要。

### 5.2 橋の補題の形

```lean
variable {n : Nat} (enc : Fin 2 → Char) (henc : Function.Injective enc)
def trE : ParsingExpression (Fin 2) n → Shallot.PExp        -- 上の表
def trG (G : PegGrammar (Fin 2) n) : Shallot.Grammar :=
  { rules := List.ofFn (fun i => trE (G.rule i)), start := G.start.val }
def trR : ParseResult (Fin 2) → Shallot.Outcome → Prop        -- 木を捨てて rest を比較
  | .failure, .fail => True
  | .success rest, .ok _ rest' => rest' = rest.map enc
  | _, _ => False

theorem tr_forward (G) {e w r} (h : G.Evaluates e w r) :
    ∃ o, Shallot.Derives (trG G) (trE e) (w.map enc) o ∧ trR r o
theorem tr_backward (G) {e w o} (h : Shallot.Derives (trG G) (trE e) (w.map enc) o) :
    ∃ r, G.Evaluates e w r ∧ trR r o
theorem recognizes_iff (G) (w) :
    G.Recognizes w ↔ ∃ t, Shallot.Derives (trG G) (.nt G.start.val) (w.map enc) (.ok t [])
```

いずれも導出の帰納法。`terminal` の場合に `beqChar (enc a) (enc b) = true ↔ a = b`
（単射性）、`nonterminal` の場合に `ruleAt (List.ofFn …) i.val = some (trE (G.rule i))`
（`Syntax.lean:84–87` の `ruleAt` と `List.ofFn` の補題）を使う。`success rest` の rest が
`w.map enc` の接尾辞であることは `Loff/Semantics.lean:129` `success_isSuffix` が既にある。
規模 300–600 行。これで

```lean
theorem pal_in_shallot (h : RecognizedByTotalPEG PAL) :
    ∃ g : Shallot.Grammar, ∀ w : List (Fin 2),
      (∃ t, Shallot.Derives g (.nt g.start) (w.map enc) (.ok t [])) ↔ w ∈ PAL
```

が出る。`pegRun_complete` と合わせれば「十分な fuel で `pegRun` が `.ok _ []` を返す」形にも
できる。ただし文法 `g` は noncomputable のままなので**実行はできない**。この repo の
`Palindrome.lean`（`palGrammar_incomplete_on_aaaa` :89、`exists_palindrome_palGrammar_rejects`
:108）や `MidpointObstruction.lean` とは矛盾しない（あれは教科書文法と「接尾辞だけ見る」
規則についての否定結果）。

### 5.3 STATUS.md の層との対応

| STATUS §5A | 成果物で埋まるか |
|---|---|
| ⑤ PEG 意味論 | 橋（§5.2）で同一視できる |
| ④ inline の意味保存 | 埋まらない（成果物に非終端置換の補題はない；`MacroPeg/ExpandSemantics.lean` の方が近い） |
| ③ SCA → PEG 射出の translation validation | **埋まらない**。成果物の `SCAToPEG.grammar` は別の符号化で、しかも noncomputable。`Scaffolding.Automaton` の意味論（§3.2）を仕様として、`symbolic_sca2peg.py` の出力を検査する検証済みチェッカーは別途必要 |
| ② 回路が ① の 1 遷移を実装 | 埋まらない |
| ① 算法の正しさと有界性 | 埋まらない（これが環 (1)） |

成果物が与えるのは「SCA の定義」（⑤の上に置く SCA の定義そのもの）と、「SCA まで行けば PEG が
存在する」という保険であり、13M 規則ファイルの検証には直接寄与しない。

## 6. Galil の算法そのものを形式化する規模の見積もり

**比較対象**：成果物の `prefixMachine`（2 テープ・15 状態・5 記号。キーと payload を
スタックに積み、`$` 以降を 1 記号ずつ照合して内積の偶奇を数えるだけ）で、定義 362 行
（`Closure/PrefixMachine.lean`）＋正しさ 850 行（`PrefixMachineCorrectness.lean`）＋
PEG 化 52 行。不変量 `Inv` の step 補題が約 30 個。

**形式化対象の候補**：Galil 1978 の紙の機械そのものではなく、この repo の再構成
（`delayed_pal.py` 129 行、`gs_heads.py` 376 行、`gs_match_heads.py` 128 行、
`gs_flag_heads.py` 52 行、`scaffold_window_pal.py` 148 行、`galil_clock.py`・`galil_realtime.py`・
`galil_contracts.py` 258 行；設計文書 `DELAYED_PAL.md`、`GS_LOCAL_CLOCK.md`、`GS_OVERLAP.md`、
`WINDOW_ROUNDS.md`、`GALIL_CLOCK.md`）。定数（stage 幅 2,4,8,…、1 arrival あたり matcher 512
命令・flag 1,024 命令、match interval 256、predictability 定数 3,169、`215b+109 ≤ 512K`）が
明示されているのが利点。`GALIL_CLOCK.md` 自身が「A complete arbitrary-length verification of
the implemented source remains separate from these tests」と書いている部分が、そのまま
証明義務になる。

**内訳の見積もり**（Lean 経験者 1 名、Mathlib 利用）：

| 部分 | 内容 | 行数 | 期間 |
|---|---|---|---|
| A. 文字列組合せ論 | 回文と周期の相互作用（Fine–Wilf 型、回文の周期鎖、Galil の move lemma `δC > (k−1)/4`、predictability「次の k/4 は 0」）。Mathlib に `List.Palindrome` はあるが周期性は薄い | 2–4k | 1–2 か月 |
| B. オンライン算法の正しさ | 二段階コントローラ＋GS 型定数空間照合が全接頭辞で PAL を判定（`delayed_pal.py` の仕様化と証明） | 2–3k | 1–2 か月 |
| C. 実時間性 | 1 arrival あたりの仕事の上界、締切不等式（`GALIL_CLOCK.md`）、FIFO 遅延の会計。定数は調整ではなく証明 | 2–4k | 1–2 か月 |
| D. 機械への符号化 | 抽象機械 → `RealTimeTM.Machine`（ジッパーテープ、1 書き込み 1 移動/テープ/遷移）。定数遅延で設計した場合は (2b) の tape compression をここで | 1–2k | 2–4 週 |
| E. 組み立て | §4 の条件付き定理との接続、Conjecture 7 形 | 0.2k | 数日 |
| 合計 | | **8–15k 行** | **4–9 か月** |

比較：成果物全体 38k 行（うち cell-probe 下界が大半）、RTTM/SCA/PEG コンパイラ層 3.5k 行。
STATUS.md の「①②は週〜月」は楽観的で、月単位（複数）が妥当。B と C は分離できず、
「有界の仕事で正しい答えが出る」を同時に扱う不変量が要る。A の一部（周期補題）は独立に
Mathlib へ出せる。

**近道の検討**：Galil より単純な実時間回文判定は知られていない（Fischer–Paterson 1974 は
O(n log n)、Manacher / eertree はランダムアクセスが要り SCA に載らない——`fpp.py` 冒頭と
`HANDOFF.md` §3a）。偶数長だけに絞っても簡単にならない。

## 7. Zenn ドラフトの二つの論拠（引用と評価）

出典：`~/repo/zenn-blog/articles/2026-09-plain-peg-palindromes.md`（branch `publish`、
commit `fde84b2`「draft: STATUS.md の流れに沿って再構成、文体を既存記事に寄せる」、
frontmatter `published: false`、`publication_name: "nextbeat"`）。公開 URL は 403。
見出しの順：はじめに／先に結論／前提：PEG と Scaffolding Automaton（SCA とはどんな機械か・
なぜ PEG と同じなのか・実時間 TM から SCA へ、そして回文へ）／なぜ手で書けないのか／
構成：機械 → 回路 → SCA → PEG（なぜこんなに大きいのか）／検証：本当に PAL なのか、それとも
「有限長のデカい文法」なのか（挙動・構造・生成器）／これは証明なのか／AI エージェントとの
分業について／お願い／参考文献。

### 7.1 SCC の論拠（「検証 › 構造」節）

> 二つ目が本命で、**呼び出しグラフの強連結成分（SCC）解析**です。長さに上限のある文法は、
> 規則の呼び出しグラフが非巡回になります（同じ規則に戻ってこられるなら、その分だけ長い入力を
> 扱えてしまうからです）。逆に、本物の機械の符号化なら「1文字消費して次の位置の規則を呼ぶ」辺
> （`. X` の形）が閉路の中に入っているはずです。

> 全13,248,052規則が開始規則から到達可能、強連結成分は2,190,652個、そのうち最大のものは
> **4,002,097規則**を含み、中身は機械のBoolean欄です。そして「1文字消費して次位置へ」の辺は
> 全部で73,261本あり、そのうち**72,638本（99%）が強連結成分の内部**にありました。入力を
> 進めながら同じ規則群に戻ってくる構造で、有限展開ではあり得ません。

> ただし正直に書いておくと、これで示せたのは「消費を通る閉路がある」ことまでで、「すべての
> 閉路が消費を通る」（非消費再帰がない）ことは静的には示していません。

**なぜ弱いか**。(i) 「長さに上限のある文法 ⇒ 呼び出しグラフが非巡回」は偽。閉路が述語の
内側や決して選ばれない選択肢を通る文法、あるいは閉路とは別の規則で長さを切る文法は、
巡回していても有限言語を認識する。逆も成り立たない。(ii) 消費辺を通る閉路の存在が示すのは
「文法の導出が任意に長くなり得る」ことであって、「長い入力に対する判定が正しい」ことでは
ない。有限テストと SCC が否定するのは「`bounded(N)` 型の展開」という特定の仮説だけで、
「符号化した機械が長さ 2,049 以上で間違う」仮説には触れない。(iii) guard 判定は過大評価
（記事自身が認める）。

### 7.2 「入力長パラメータなし」の論拠（「検証 › 生成器」節ほか）

> そして、いちばん素朴でいちばん強い根拠です。**生成器は入力長を知りません。**
> `scaffold_window_pal.py` は機械の1遷移分の回路を1個作るだけ、`symbolic_sca2peg.py` は
> それを位置に依存しない規則に写すだけです。長さを知らないものは長さの上限を符号化できません。

（「先に結論」節）「生成器のどこにも入力長のパラメータがない。」／（「構成」節）「ここに
入力長は一切現れません。」

**なぜ弱いか**。生成器が長さを引数に取らないことと、出力が全長さで正しいことは別。回路の
中の定数（match interval 256、predictability 定数 3,169、1 arrival あたり 512/1,024 命令、
`depth >= 16` 等）は暗黙の上界であり、それらが全入力に対して十分であることは算法レベルの
定理（環 (1)、§6 の C）でしか保証されない。`GALIL_CLOCK.md` 自身が「A complete arbitrary-length
verification of the implemented source remains separate from these tests」と述べており、
「長さを知らないものは上限を符号化できない」は直観であって定理ではない。生成器が
忠実に符号化した機械が間違っていれば、文法も間違う。

いずれの論拠も「有限長の巨大文法ではない」という**特定の疑い**への答えとしては有効で、
記事の「証明ではない」という位置づけと整合する。批評者が求めるのは、この二つを根拠に
「PAL の PEG が書けた」と読ませないことと、存在の側を Lean で閉じること。前者は記事の
表現の問題、後者は §4–§6。

## 8. 参考文献（本セッションでの確認状況つき）

- Z. Galil, *Palindrome recognition in real time by a multitape Turing machine*, JCSS 16(2)
  (1978) 140–157. doi:10.1016/0022-0000(78)90042-9 ——書誌のみ（本文 403）。
- A. O. Slisenko, *Recognition of palindromes by multihead Turing machines*, Proc. Steklov
  Inst. Math. 129 (1973) 30–202；英訳 AMS 1976 ——書誌のみ。
- A. O. Slisenko, *A simplified proof of the real-time recognizability of palindromes on Turing
  machines*, J. Soviet Math. 15 (1981) 68–77 ——書誌のみ。
- Z. Galil, *Real-time algorithms for string-matching and palindrome recognition*, STOC 1976.
  doi:10.1145/800113.803644 ——書誌のみ。
- Z. Galil, *On converting on-line algorithms into real-time and on real-time algorithms for
  string-matching and palindrome recognition*, SIGACT News 7(4) (1975). doi:10.1145/990502.990505
  ——書誌のみ。
- J. Hartmanis, R. E. Stearns, *On the computational complexity of algorithms*, Trans. AMS 117
  (1965) 285–306 ——書誌のみ。
- A. L. Rosenberg, *Real-time definable languages*, J. ACM 14(4) (1967) 645–662 ——書誌のみ。
- P. C. Fischer, A. R. Meyer, A. L. Rosenberg, *Real-time simulation of multihead tape units*,
  J. ACM 19(4) (1972) 590–607；*Time-restricted sequence generation*, JCSS 4 (1970) 50–73
  ——書誌のみ。
- R. V. Book, S. A. Greibach, *Quasi-realtime languages*, Math. Systems Theory 4 (1970) 97–111
  ——書誌のみ。
- P. M. B. Vitányi, *On the power of real-time Turing machines under varying specifications*,
  ICALP 1980, LNCS 85. doi:10.1007/3-540-10003-2_106 ——書誌のみ。
- T. Jiang, J. I. Seiferas, P. M. B. Vitányi, *Two heads are better than two tapes*, J. AMS
  (1997); arXiv:cs/0110039 ——本文確認（脚注 1 の実時間の定義）。
- B. Loff, N. Moreira, R. Reis, *The computational power of parsing expression grammars*,
  arXiv:1902.08272v2 (2020)；JCSS 2020, PII S002200002030012X；DLT 2018 ——arXiv v2 本文確認。
- J. Kim, J. Park, *Separating Parsing Expression Grammars using Cell-Probe Lower Bounds*,
  arXiv:2608.29592 (30 Aug 2026) ——arXiv HTML 本文確認。
- J. Kim, J. Park, *… : Lean Artifact*, v0.1.0, Zenodo, doi:10.5281/zenodo.22099762
  (2026-08-25); GitHub `kimjg1119/peg-separation-artifact` ——クローンしてビルド確認。
- この repo：`lean/Shallot/Peg/{Syntax,Semantics,Interp,Soundness,Completeness,Determinism,
  Palindrome,MidpointObstruction}.lean`、`docs/palindromes-in-peg/{STATUS,PLAIN_PAL_ARTIFACT,
  GALIL_CLOCK,DELAYED_PAL,SCA_GALIL}.md` ——本文確認。
