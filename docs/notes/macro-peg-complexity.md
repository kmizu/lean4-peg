# 一階 call-by-name Macro PEG の認識問題の計算量（報告）

前回（[macro-peg-memo-bounds.md](macro-peg-memo-bounds.md)）は、構文的なメモ化表の大きさを測っただけで、
認識問題そのものの計算量ではなかった。今回は認識問題そのものを扱う。

## 問題と結論

**問題**: 一階（`lam`／`callParam`／`invoke`／`dbg` を含まない）の call-by-name Macro PEG `g` と開始式 `e` を固定し、
入力 `x` について「`e` が `x` を全消費して成功する有限導出があるか」（より一般に、観測＝失敗か残余はどれか）を判定する。

**結論**（すべて Lean で証明、`sorry`・独自公理なし、標準の 3 公理のみ）:

| | 内容 | 主な定理 |
|---|---|---|
| 下界 | ある固定の文法について PSPACE 困難（QBF からの多項式長の帰着） | `qbf_reduction`, `qbf_reject`, `enc_length` |
| 上界 | 決定可能。反復回数は `\|rules\|·(n+3)^((n+1)·K)·(n+1)` 以下 → 指数時間 | `decideObs_iff`, `decideObs_none_iff`, `iterBound_le` |
| 接続 | 判定手続きを下界の文法で走らせると QBF を評価する | `qbf_by_decision` |

通常の PEG は packrat 構文解析で線形時間に認識できる。したがって、P ≠ PSPACE のもとでは、一階 CBN Macro PEG は
通常の PEG より真に難しい言語を定義する。ただしこれは条件つきの結論で、無条件の分離は証明していない。

## 下界: QBF の評価（`QbfHard.lean`）

```
[0] Q(C, A) ← "A" &Q(C "1", A / C "0") Q(C "1", A)
            / "E" (Q(C "1", A / C "0") / Q(C "1", A))
            / "#" M(A)
[1] M(A)    ← (Cl(A) ";")* !.
[2] Cl(A)   ← TL(A) Lit* / FL(A) Cl(A)
[3] TL(A)   ← "+" &A Code / "-" !A Code
[4] FL(A)   ← "+" !A Code / "-" &A Code
[5] Lit     ← ("+" / "-") Code
[6] Code    ← "1"* "0"
開始: Q(ε, !ε)
```

- `C = "1"^k` は読んだ量化子の数を数える。`A` は割り当てで、真にした変数の符号 `1^j 0` を並べた順序つき選択。
  `A / C "0"` で変数 `k` を真にする。
- 母式は CNF。リテラル `+v` が真 ⇔ 変数 `v` の符号の上で `&A` が成功する。
- ∀ は `&（真の場合）（偽の場合）` で両方を要求し、∃ は選択で表す。

```lean
theorem qbf_reduction (q : List Bool) (m : QMatrix) :
    MRecognizesAll qbfG qbfStart (enc q m) ↔ qbfTrue q 0 [] m = true
theorem qbf_reject (q : List Bool) (m : QMatrix) :
    MacroObs qbfG qbfStart (enc q m) none ↔ qbfTrue q 0 [] m = false
theorem enc_length (q : List Bool) (m : QMatrix) :
    (enc q m).length = q.length + 1 + (m.map (fun cl => (cl.map (fun l => l.2 + 2)).sum + 1)).sum
```

証明は、観測の合成則（`obs_seq`、`obs_alt_none`、`obs_star_some`、`obs_call` など）を積み上げる。
`cNum` → `codeP` → `asg` → `Code`／`Lit`／`Lit*` → `TL`／`FL` → `Cl` → `M` → `Q` の順に、
「真偽で結果が決まる有限導出がある」ことを一つずつ示す。偽の式では非停止ではなく有限の失敗導出になるので、
`qbf_reject` も成り立つ。逆向き（受理 ⇒ 真）は決定性 `mderives_det` から出る。

- **PSPACE 困難の根拠**: `enc` は構造的な写像で長さは式の大きさの二乗以下なので、多項式時間で計算できる。
  TQBF が PSPACE 完全であること（Stockmeyer–Meyer 1973）は外部の事実として使う。どちらも計算モデルを
  形式化していないので、「多項式時間帰着である」ことは Lean の定理ではない。Lean の定理は帰着の正当性
  （受理 ⇔ 真）と長さの式。
- 実引数を構築するので（`C "1"`、`A / C "0"`）、この文法は有限引数断片の外にある。有限引数断片は通常 PEG に
  特殊化できる（PR #1）ので、困難さは実引数の構築から来ている。

## 上界: 判定手続き（`Decide.lean`）

**値の意味**: 位置 `p`（残りの長さ、`p ≤ n`）での結果を `Res = Option (Option Nat)` で表す。`none` は有限導出なし、
`some none` は失敗、`some (some j)` は残り `j` で成功。CBN の実引数（thunk）の意味は、各位置での結果を並べた列
`Val = List Res`（長さ `n+1`）として持つ。CBN の代入が環境での評価と一致する、という代入補題がこの表現の要。

```lean
theorem ev_subst ... : ev g x T E (MExp.subst args b) p = ev g x T (evArgs g x T E args) b p
```

**規則表の反復**: `tbl 0 = ⊥`、`tbl (m+1) i W = 各位置 p で ev (tbl m) W (規則 i の本体) p`。これは規則の意味を
「引数の値の列 → 値」という表として持つ Kleene 反復。

- `derives_ev`: 有限導出があれば、ある段 `m` で `ev (tbl m) [] e |y| = obsR o`（導出の帰納法。呼び出しの場合は
  代入補題と、表の単調性（表と引数値についての情報順序）で次の段へ上げる）。
- `ev_derives`: どの段の定義された結果にも、その結果の有限導出がある（不変条件「健全な表」: 定義された項目は、
  健全な実引数に対する呼び出しの導出を持つ）。
- `tbl_stable`: 値の全体は有限（長さ `n+1` の `n+3` 記号の列）。関連する項目（存在する規則、`allVals` の引数値の列、
  位置 `≤ n`）の定義済みの個数は単調に増え、`iterBound` で上から抑えられる。鳩の巣でどこかの段が何も変えず、
  そこから先は不動点（`agree_from`）。したがって `iterBound` 段で十分。
- 判定手続き `decideObs g x e`: `iterBound` 段目の表で `e` を `|x|` で評価する。

```lean
theorem decideObs_iff (hg : g.FirstOrder) (he : e.FirstOrder) (he0 : MExp.subst [] e = e) (x) (r) :
    decideObs g x e = some r ↔ MacroObs g e x r
theorem decideObs_none_iff ... : decideObs g x e = none ↔ ∀ r, ¬ MacroObs g e x r
theorem iterBound_le (g) (x) {K} (hK : ∀ r ∈ g.rules, r.arity ≤ K) :
    iterBound g x ≤ g.rules.length * ((x.length + 3) ^ ((x.length + 1) * K) * (x.length + 1))
```

`decideObs_none_iff` は、非停止（有限導出の不存在）も判定できることを言っている。燃料の打ち切りではない
（例: `L ← L` で `decideObs = none` を `decide` で計算し、全観測の不存在を導いた）。

**時間の見積もり（Lean の定理ではない部分）**: 1 段で各項目 `(i, W, p)` を 1 回ずつ計算する。項目数は `iterBound` と
同じで、1 項目の計算は文法の大きさと `n` の多項式で済む（実引数の値は表から読む）。したがって全体は
`iterBound² · poly(|g|, n) = 2^{O(K·n·log n)}`（固定文法では入力長について指数時間）。Lean の `decideObs` は
この反復を素直な関数として書いたもので、その実行時間そのものは形式化していない。形式化したのは
「`iterBound` 段で正しい答えが出る」ことと `iterBound` の大きさ。

## 主張していないこと・未解決

- **ちょうどの計算量は未解決**: PSPACE 困難と EXPTIME の間のどこにあるか（EXPTIME 完全か、PSPACE に入るか）は
  分からない。
- **対象**: 一階・call-by-name だけ。高階（`lam`／`callParam`）は値の空間が関数の関数になるので、同じ方法では
  もっと高い上界になる見込み（未検討）。CBV（Par／Seq）では実引数の値が入力の部分文字列になり、値の空間が
  多項式になる見込みだが、証明していない。
- **固定文法の計算量**（データ計算量）だけを扱った。文法も入力とする場合の計算量（指数部のアリティ `K` が効く）は
  別問題。
- 計算モデル（チューリング機械など）は形式化していない。下界は帰着の正当性と長さ、上界は反復回数と正しさまでが
  Lean の定理。

## 検証

- `lake env lean -DautoImplicit=false` で `QbfHard.lean`・`Decide.lean`・`TrueComplexity.lean` を個別に検査
- `cd lean && lake build`: `Build completed successfully (114 jobs).`
- `bash scripts/audit-source.sh`: `audit-source: OK (no sorry/admit/native_decide/axiom)`
- 新規の公開定理 50 件を `Audit.lean` に `#guard_msgs in #print axioms` で固定（`[propext]` 5、
  `[propext, Quot.sound]` 10、`[propext, Classical.choice, Quot.sound]` 35）
- 具体例: QBF 4 本（`∀x. x ∨ ¬x` 真、`∀x. x` 偽、`∃x∀y. (x∨y)∧(x∨¬y)` 真、`∀x∃y. …` 偽）を主定理で、
  判定手続きの 3 例（受理・残余・`L ← L` の非停止）を `decide` で計算

## 次の目標

1. **ちょうどの計算量**: 一階 CBN Macro PEG が EXPTIME 困難であること（交替線形空間機械の模倣など）か、
   PSPACE に入ること（値の列を全部持たずに済む評価）のどちらか。
2. **CBV は多項式時間**: Par／Seq では実引数の値が入力の部分文字列なので、同じ表の方法で反復回数が多項式になる
   ことを示す。CBN と CBV の計算量の分離（P ≠ PSPACE のもとで）になる。
