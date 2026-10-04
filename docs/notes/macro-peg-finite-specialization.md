# Macro PEG の性質: 有限特殊化・引数同値・評価戦略（報告）

`instructions.md`（2026-10-03）に沿った作業の報告。Lean 4（v4.32.0、Mathlib なし）、`lean/MacroPeg/Properties/`。

- 開始コミット: `5751729`（`main`、PR #4 のマージ）。指示書が出発点として挙げる `6451576` は、
  リポジトリ作り直し前の `main` で、`lean/MacroPeg` と `lean/Shallot/Peg` に差分がないことを作業開始時に確認した。
- 最終コミット: PR の先頭コミット（本文末尾の「検証」節に記す）。

## 1. 採用した断片と評価戦略

**評価戦略**は A・B が call-by-name（CBN）、C は三戦略（CBN、Par = `callByValuePar`、Seq = `callByValueSeq`）。

**観測**は解析木を消した `Option (List Char)`: 失敗が `none`、成功が `some rest`。Macro PEG 側は既存の
`MOutcome.restOf` を再利用し、通常 PEG 側に `pegRestOf` を新設した（`CmpOutcome` 側には二重に整備していない）。

```lean
def MacroObs (g : MGrammar) (e : MExp) (x : List Char) (r : Option (List Char)) : Prop :=
  ∃ o, MDerives g .callByName e x o ∧ o.restOf = r
def PegObs (g : Grammar) (e : PExp) (x : List Char) (r : Option (List Char)) : Prop :=
  ∃ o, Derives g e x o ∧ pegRestOf o = r
def ObsEquiv (g : MGrammar) (e f : MExp) : Prop := ∀ x r, MacroObs g e x r ↔ MacroObs g f x r
def MAccepts g e x := ∃ rest, MacroObs g e x (some rest)      -- 成功言語
def MRecognizesAll g e x := MacroObs g e x (some [])          -- 全消費言語
```

言語クラスは両方の観測について述べる（主定理から両方が系として出る）。

**A の断片**は制限構文と `MExp` への埋め込みで表した（指示書 §5.1 の選択肢のうち後者）。既存 `MExp` には
決定可能な等号がなく、構造的述語で「実引数は仮引数の転送か `D` の要素」を書くと等号判定が要るため。

```lean
inductive FArg | fwd (j : Nat) | const (k : Nat)
inductive FExp | eps | any | chr | range | lit | param (j) | env (i) | call (B) (args : List FArg)
               | seq | alt | star | notP
structure FRule where arity : Nat; body : FExp
structure FGrammar where env : List PExp; D : List PExp; rules : List FRule
```

- `env` は固定した通常 PEG 環境（`env` と `D` の中の `.nt i` は環境の規則 `i`）。`D` は自由な仮引数を持たない
  通常 PEG 式の有限リスト。`lam`、`callParam`、`invoke`、構築した実引数（`x "a"` など）は構文上存在しない。
- 埋め込み `FGrammar.toMacro`: マクロ規則 `0 … |env|-1` が環境の規則（アリティ 0、既存の `embedExp`）、その後に
  断片の規則（`|env|` ずらし）。識別子写像は環境側が恒等、断片側が `B ↦ |env| + B` で単射・復号可能。
  入口は `F.entry A ks = .call (|env| + A) [embedExp D[k] | k ∈ ks]`。
- `FGrammar.WF`（構文的）: 環境・`D`・本体の環境参照が範囲内、呼び出し先が存在してアリティ一致、仮引数・転送の
  添字が範囲内、定数の添字が `D` 内。実行可能な検査器 `wfB` とその健全性 `wfB_sound`。入口の妥当性は
  `ValidVec F A ks`（規則があり、長さがアリティ、各要素が `D` の添字）。

**特殊化**（入力に依存しない全関数）: 全組 `specs` は各規則 `B` と長さ `arity(B)` の `D` 添字ベクトル全部
（`vecs`）を規則順に並べたもの。`(B, w)` の非終端は `|env| + (specs 内の位置)`。本体は `FExp.spec`:
`param j ↦ D[w[j]]`、`env i ↦ .nt i`、`call C as ↦ (C, as を w で解決したベクトル) の非終端`。再帰は再帰のまま
（`Loop ← Loop` は通常 PEG の規則 `L ← L` になる。例 `loopF`）。

## 2. 主定理の型と方向

### A

```lean
theorem finite_specialization_cbn (F : FGrammar) (hF : F.WF) {A : Nat} {ks : List Nat} (hv : F.ValidVec A ks)
    (x : List Char) (r : Option (List Char)) :
    MacroObs F.toMacro (F.entry A ks) x r ↔ PegObs (F.specialize A ks) (.nt (F.specialize A ks).start) x r
```

証明は帰納関係 `Rel F S : MExp → PExp → Prop`（同じ結合子、環境参照 `call i [] ~ .nt i`、特殊化参照
`call (|env|+B) (D[w]) ~ .nt (|env| + code B w)`）による。

- **保存**（Macro→PEG）`spec_preserve`: `MDerives F.toMacro .callByName m x o → Rel F S m p →
  ∃ o', Derives (F.specializeOn S A ks) p x o' ∧ Corr o o'`。`Corr` は「両方失敗」か「同じ残余で両方成功」。
  成功・失敗・残余を一度に運ぶ。失敗した連接（`seqFail₁`／`seqFail₂`）、選択の後続分岐（`altR`／`altFail`）、
  否定先読み、`star` の両規則も帰納法の場合に含む。`callMissing`／`callArity`／`paramFail` は `Rel` と `WF`
  から起こらない。
- **反映**（PEG→Macro）`spec_reflect`: `Derives (F.specializeOn S A ks) p x o' → Rel F S m p →
  ∃ o, MDerives F.toMacro .callByName m x o ∧ Corr o o'`。`ntMissing` は参照の範囲から起こらない。

どちらも燃料も決定性も使わない。したがって「有限導出が存在しない」ことも両方向に保存される
（`Loop` の例 `loopF_no_obs`: 全入力・全観測で Macro 側に導出がない）。

系（すべて同じ前提）:

```lean
theorem finite_specialization_accepts ... :
    MAccepts F.toMacro (F.entry A ks) x ↔ PAccepts (F.specialize A ks) (.nt (F.specialize A ks).start) x
theorem finite_specialization_recognizesAll ... :
    MRecognizesAll F.toMacro (F.entry A ks) x ↔ PRecognizesAll (F.specialize A ks) (.nt (F.specialize A ks).start) x
theorem finite_specialization_run ... :
    (∃ f o, mpegRun F.toMacro .callByName f (F.entry A ks) x = some o ∧ o.restOf = r) ↔
      (∃ f o, pegRun (F.specialize A ks) f (.nt (F.specialize A ks).start) x = some o ∧ pegRestOf o = r)
```

燃料版は既存の `mpegRun_sound/complete` と `pegRun_sound/complete` に通すだけで、両側は別々の燃料を選ぶ。

§5.4 の各義務と対応する定理:

| 義務 | 定理 |
|---|---|
| 断片検査の健全性 | `FGrammar.wfB_sound`, `FGrammar.validVecB_sound` |
| 引数領域の閉性 | `FGrammar.validVec_call`（妥当なベクトルからの呼び出しの解決結果も妥当） |
| 有限性・構築の停止性 | `specialize` は全関数（構成が入力を読まない）、`FGrammar.specialize_size` |
| 参照と代入の整合性 | `rel_spec`（代入した本体と特殊化した本体が `Rel` で対応）、`FArg.subst_toM` |
| 成功・失敗の保存 | `spec_preserve` |
| 成功・失敗の反映 | `spec_reflect` |
| 言語保存の系 | `finite_specialization_accepts`, `finite_specialization_recognizesAll` |
| 実行との接続 | `finite_specialization_run` |
| 符号化の単射性・復号・参照正当性 | `codeOn_inj`, `FGrammar.specializeOn_decode`, `FGrammar.specialize_selfContained` |
| 環境の意味の一致（§5.1(7)） | `env_obs_iff`（環境そのもの ↔ 埋め込み）と `rel_obs_iff`（埋め込み ↔ 生成側） |

**大きさ（§5.5）**: `FGrammar.specialize_size` は規則数がちょうど `|env| + Σ_B |D|^arity(B)` であることを示す
（`specialize_size_le` が指示書の上界の形）。環境の規則は別項、入口は規則を増やさない（入口の非終端は
`(A, ks)` の特殊化規則そのもの）。アリティ 0 は空ベクトル 1 個、`|D| = 0` は `0^0 = 1`、`0^m = 0`（例 `zeroF`）。
これは非終端の個数であり、定数式の複製で本体が大きくなる分の総構文サイズは上界に含めていない。アリティが
入力文法とともに増える場合に多項式サイズだとは主張しない。

**表現力（§5.6）**:

```lean
theorem fragment_lang_is_peg (F : FGrammar) (hF : F.WF) {A : Nat} {ks : List Nat} (hv : F.ValidVec A ks) :
    ∃ (g : Grammar) (s : Nat), g.SelfContained ∧ s < g.rules.length ∧
      ∀ x, (MAccepts F.toMacro (F.entry A ks) x ↔ PAccepts g (.nt s) x) ∧
        (MRecognizesAll F.toMacro (F.entry A ks) x ↔ PRecognizesAll g (.nt s) x)
theorem peg_lang_is_fragment (g : Grammar) (hself : g.SelfContained) {s : Nat} (hs : s < g.rules.length) :
    ∃ (F : FGrammar) (A : Nat) (ks : List Nat), F.WF ∧ F.ValidVec A ks ∧
      ∀ x, (PAccepts g (.nt s) x ↔ MAccepts F.toMacro (F.entry A ks) x) ∧
        (PRecognizesAll g (.nt s) x ↔ MRecognizesAll F.toMacro (F.entry A ks) x)
```

この断片（一階・CBN・実引数は転送か有限集合 `D` の定数）と通常 PEG は、両方の観測で同じ言語クラスを持つ。
**これは Macro PEG 全体の表現力についての結論ではない。** 実引数の構築（`F(x) ← F(x "a")` など）を許す
一般の Macro PEG では A の前提（実引数が有限集合に留まる）が成り立たない。この断片の構文 `FArg` はそもそも
そのような実引数を書けない。

### 既存の非循環展開（M-PEG-6）との違い

| | `expand_preserves_cbn`（既存） | `finite_specialization_cbn`（今回） |
|---|---|---|
| 前提 | 非循環（`acyclicB`）、`arityOk`、`NoCallableRules` | 断片の `WF`、入口の妥当性。再帰を許す |
| 構成 | 呼び出しを本体で置き換え続ける（呼び出しが残らない） | 有限個の非終端に写し、再帰は再帰のまま |
| 結論の方向 | 保存のみ（元の導出 → 展開後の導出） | 保存と反映の両方（観測の同値） |
| 対象 | 高階を含む `MExp` 全般（条件つき） | 一階の有限引数断片だけ |

### D: 到達可能な組だけの特殊化（指示書 §8 の 3）

特殊化と正当性を「特殊化する組のリスト `S`」で一般化した（`specializeOn`、`finite_specialization_on`）。`S` に
要るのは `SpecSet`（妥当な組だけで、各組の本体の呼び出し先も `S` に入る）だけで、全列挙 `specs` はその一例
（`specs_specSet`）。`reach F A ks` は「現在の組の呼び出し先を加える」反復を `|specs| + 1` 回行ったもの。
各段は `specs` のフィルタで長さが単調、`|specs|` で抑えられるので、鳩の巣でどこかの段が繰り返し、そこから先は
不動点になる（`stage_fix_exists`、`reach_fix`）。不動点は呼び出しで閉じる（`reach_specSet`）。

```lean
theorem reachable_specialization (F : FGrammar) (hF : F.WF) {A : Nat} {ks : List Nat} (hv : F.ValidVec A ks)
    (x : List Char) (r : Option (List Char)) :
    MacroObs F.toMacro (F.entry A ks) x r ↔
      PegObs (F.specializeOn (F.reach A ks) A ks) (.nt (F.specializeOn (F.reach A ks) A ks).start) x r
theorem reach_length_le (F : FGrammar) (A : Nat) (ks : List Nat) :
    (F.specializeOn (F.reach A ks) A ks).rules.length ≤ (F.specialize A ks).rules.length
```

例（`decide` で計算）: `altF` の入口 `Alt("a","b")` は 8 組中 2 組、`mutF` の `E("a")` は 18 組中 2 組。

### B

```lean
theorem subst_obsEquiv_general {g : MGrammar} (hg : g.FirstOrder) {body : MExp} (hb : body.FirstOrder)
    {ρ ρ' : List MExp} (hl : ρ.length = ρ'.length)
    (h : ∀ (i : Nat) a a', ρ[i]? = some a → ρ'[i]? = some a' → ObsEquiv g a a') :
    ObsEquiv g (MExp.subst ρ body) (MExp.subst ρ' body)
theorem subst_obsEquiv_of_argEquiv ... (_hscope : body.ParamsBelow ρ.length) ... -- 指示書の形
```

`FirstOrder` は `lam`／`callParam`／`invoke`／`dbg` を含まないこと（規則本体全部と `body` に要求）。

- **構文の帰納法で足りる部分**（`sim_subst`）: 対応する成分が関係 `Sim`（同じ構文、ただし観測同値な式が
  入った葉を許す）にある引数リストを一階の式に代入すると、結果も `Sim`。
- **導出の帰納法が要る部分**（`sim_preserve`）: `Sim` の式は同じ観測を持つ。構文だけで足りないのは再帰呼び出しの
  場合で、`call i as` は `subst as r.body` に進み、その新しい組が再び `Sim` になることを規則本体への `sim_subst`
  で示す。

引数が閉じていることも一階であることも要らない（引数は `Sim` の葉にだけ現れ、観測同値だけで扱われる）。
スコープ条件（`body` の仮引数が `ρ` の長さ未満）は証明で使っていない。範囲外の仮引数は両側とも同じ
`failAlways` になるため。指示書の注意に従い、指示書の形の定理ではこの条件を仮定に残し、フォールバックに依存しない
読み方ができるようにした。

**反例（§6.1）**は実際の構文で定義し、導出で証明した: `ceG = F(x) ← x "a" !.`。`same_recognizesAll`（`"a"` と
`"a" !.` の全消費言語はどちらも `{"a"}`）、`ce_call_argA`（`F("a")` は `"aa"` を全部消費して成功）、
`ce_call_argAEnd`（`F("a" !.)` は `"aa"` で失敗）、`ce_not_accepts`、`argA_not_equiv_argAEnd`（`"aa"` で残余が
違うので観測同値ではない）。

### C

`SObs g s e x r` は任意の戦略での観測。

| 文法・入力 | CBN | Par | Seq |
|---|---|---|---|
| `F(x) ← ε; S ← F(!ε)`、任意の `w` | 成功(`w`) `row1_cbn` | 失敗 `row1_par` | 失敗 `row1_seq` |
| `F(x) ← x; S ← F("a")`、`"a"` | 成功(`[]`) `row2_cbn` | 成功(`[]`) `row2_par` | 失敗 `row2_seq` |
| `F(x,y) ← ε; S ← F("a","a")`、`"a"` | 成功(`"a"`) `row3_cbn` | 成功(`"a"`) `row3_par` | 失敗 `row3_seq` |
| `F(x,y) ← ε; S ← F("a","b")`、`"ab"` | 成功(`"ab"`) `row4_cbn` | 失敗 `row4_par` | 成功(`[]`) `row4_seq` |
| `F(x) ← ε; S ← F(&"a")`、`"b"` | 成功(`"b"`) `rowAnd_cbn` | 失敗 `rowAnd_par` | 失敗 `rowAnd_seq` |

指示書の表は実ソースの規則（`callParArgFail`、`callSeqArgFail`、`DerivesArgsSeq` の入力の受け渡し）に照らして
そのまま成り立った。各観測は戦略ごとに一意（`sObs_unique`、決定性から）。

**短絡と非停止（§7.2）**: `loop_no_derivation`（`Loop()` はどの戦略でも有限導出を持たない、導出の帰納法）、
`par_shortCircuit`／`seq_shortCircuit`（`F(!ε, Loop())` は第 1 引数で失敗）、`par_first_loops`／`seq_first_loops`
（`F(Loop(), !ε)` は導出を持たない）、`cbn_unused_first_fails`／`_loops`（CBN では成功）。どれも燃料を使わない。

**条件付きの戦略一致（§7.3）**:

```lean
def ZeroArg (g : MGrammar) (a : MExp) : Prop := ∀ s x, ∃ t, MDerives g s a x (.ok t x)
def Closed (a : MExp) : Prop := ∀ σ, MExp.subst σ a = a
theorem strategy_agree {g : MGrammar} (hg : g.ZArgs) {e : MExp} (he : ZArgs g e) (s s' : Strategy)
    (x : List Char) (r : Option (List Char)) : SObs g s e x r ↔ SObs g s' e x r
theorem strategy_agree_eps {g : MGrammar} (hg : ∀ r ∈ g.rules, EpsArgs r.body) {e : MExp} (he : EpsArgs e)
    (s s' : Strategy) (x : List Char) (r : Option (List Char)) : SObs g s e x r ↔ SObs g s' e x r
```

- 量化範囲: `ZArgs g e` は `e` が一階・純粋で、`e` の中の**すべての構文上の実引数**（使われるかどうかに関係なく）が
  閉じていて `ZeroArg` であること。`g.ZArgs` は全規則本体について同じ。`ZeroArg` は三戦略すべて・全入力について
  「停止してゼロ文字で成功する導出がある」こと。CBN で評価されない引数も、Par／Seq でだけ評価される引数も
  構文上の出現として数えるので、未使用の失敗引数を見落とさない。
- 最初の段階は全実引数が構文的に `ε` の断片（`strategy_agree_eps`）で、それを一般の `ZeroArg` の場合の一例として
  得た。
- 「空文字を受理することがある」への弱化は偽: `&"a"` は `"a"` ではゼロ文字で成功する（`andA_zero_on_a`）が、
  `"b"` では CBN と Par／Seq が分かれる（表の最終行）。
- 反例表から言語クラスの包含関係は主張していない。

## 3. 既存・新規・予想・未形式化の区別

- **既存（使っただけ）**: `MDerives`／`Derives`、`mpegRun_sound/complete`、`pegRun_sound/complete`、`mderives_det`、
  `derives_det`、`MOutcome.restOf` とその補題、`subst_subst`、`embedExp`、`derives_append_preserved/reflect`、
  `ruleAtM_mem`。既存ファイルは変更していない（`MacroPeg.lean` の import と `Audit.lean` の監査ブロック追加だけ）。
- **今回証明**: 上記の A・B・C・D の定理すべて（`#print axioms` は第 5 節）。
- **予想・未証明**: 第 6 節の次の目標。C で、実引数に仮引数の転送（`.param j`）を含む場合（`Closed` を満たさない）は
  扱っていない。
- **研究上の新規性は評価していない**。有限の引数領域による特殊化はテンプレート実体化・単相化と同じ発想の古典的な
  手法で、一次資料との比較はしていない。ここで言えるのは「この Lean 形式化の中で、既存の Macro PEG 意味論に対して
  双方向の観測同値として機械検証した」ことまで。

## 4. 前提について

- **A の `WF` と入口の妥当性**は構文的な条件で、結論（観測の同値）を仮定していない。検査器 `wfB` が、参照先不足・
  アリティ不一致・範囲外の仮引数・範囲外の定数・範囲外の環境参照を拒否する例を `SpecExamples.lean` に置いた。
  ただし、**これらの条件を外すと主定理が偽になる反例は作っていない**（除去不可能性は未検証）。例えば
  アリティ不一致は Macro 側で `callArity` の失敗、生成側でも範囲外の非終端の失敗になり、偶然一致する可能性がある。
- **定数が環境の外を参照しないこと**（`D` の要素が `NtBounded |env|`）は、生成文法で環境の規則を同じ添字に置く
  ために強く置いた前提。
- **B の一階性**は `sim_subst` の帰納法に要る。`callParam k` の代入は `k` 番目の引数の構文の形（`lam` かどうか）で
  分岐するが、`Sim` の葉の両側は観測同値なだけで形は揃っていない。除去できないことの反例は作っていない。
- **C の `Closed`** は、規則本体の中の実引数が代入で変わらないことを使うための前提。転送された仮引数は対象外。

## 5. 検証

コマンドと結果（すべてこの作業環境で実行）:

- 各モジュールを `cd lean && lake env lean MacroPeg/Properties/<X>.lean` で個別に検査（エラーなし）。
  注意: この単体検査は lakefile の `autoImplicit = false` を使わない。全体ビルドで暗黙変数 1 件
  （`substArgs_closed` の `g`）が見つかり、修正した。
- `cd lean && lake build`: `Build completed successfully (109 jobs).`
- `bash scripts/audit-source.sh`: `audit-source: OK (no sorry/admit/native_decide/axiom)`
- `lean/Audit.lean` に新規の公開定理 76 件の `#guard_msgs in #print axioms` を追加し、`lake build Audit` が通る。
  内訳（実測）: 公理なし 1、`[propext]` 32、`[propext, Quot.sound]` 21、`[propext, Classical.choice, Quot.sound]` 22。
  独自公理なし。主定理 `finite_specialization_cbn` は `[propext, Classical.choice, Quot.sound]`。

新規モジュール: `Observation`、`FiniteArgs`、`Specialize`、`SpecializeCorrect`、`Reachable`、`SpecExamples`、
`ArgEquiv`、`Strategy`（`lean/MacroPeg/Properties/`）。

§10 の入力・境界条件と例（`SpecExamples.lean`）: 空入力（`Twice("b")` は `[]` で失敗）、空の定数式（`Fst(ε, "a")`）、
アリティ 0（`zeroF`、`loopF`）、空の定数集合（`zeroF`）、相互再帰（`mutF` の `E`／`O`）、同じベクトルへの再帰
（`Loop`）、未使用の引数（`Fst`）、同じ引数の 2 回使用（`Twice`）、引数順序の入れ替え（`Alt(y, x)`）、失敗する
引数（`Fst(!ε, "a")`）、連接の後半の失敗（`Twice("b")` on `"ba"`）、選択の後続分岐（`Alt` の `/ !.`）、残余を
観測する先読み（`Peek("a")` on `"ab"` は `"ab"` を残す）、断片の条件で除外される文法（`wfB = false` の 6 例）、
非停止する再帰が失敗にも成功にも変わらないこと（`loopF_no_obs`）。解析木は観測から消しており、木が違っても
（Macro 側 `nodeCall`、生成側 `nodeNT`）観測が一致することは主定理そのもの。

## 6. 次の具体的な定理目標（2 つ）

1. **有限の意味論的同値類による特殊化（D の 1）**: 実引数を構築する文法でも、到達する実引数が有限個の代表に
   観測同値でまとまるなら、B（`subst_obsEquiv_general`）で代表に置き換えてから A を適用できる、という定理。
   代表への写像と同値性の証明書を入力として受け取る形にする。
2. **転送つきの戦略一致（C の拡張）**: 規則本体の実引数に仮引数の転送 `.param j` を許した場合の
   `strategy_agree`。呼び出し元の実引数がすべて `ZeroArg` なら転送先でも `ZeroArg` になることを、代入後の式に
   対する不変条件として示す。

## 7. A と C／D の状況

- **A: 完了。** 有限で入力に依存しない実行可能な特殊化、成功・失敗・残余の保存と反映（双方向）、非終端個数、
  成功言語・全消費言語の系、実行との接続、表現力の系、再帰を含む例と境界例。
- **B: 完了。** 反例（導出で証明）と、一階・純粋な固定文法での引数同値 ⇒ 代入同値。
- **C: 完了（範囲は上記）。** 表の 4 行 × 3 戦略と `&"a"` の行、短絡・非停止（導出の不存在）、全実引数が構文的に
  `ε` の場合の全称定理と、閉じた `ZeroArg` 実引数への一般化。転送される仮引数は未着手。
- **D: 3（到達可能な組だけの特殊化）を完了。** 1・2・4 は未着手。
