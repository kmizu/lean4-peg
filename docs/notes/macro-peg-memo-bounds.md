# Macro PEG のメモ化表の大きさ: 上界と下界（報告）

`lean/MacroPeg/Properties/Visits.lean` と `Complexity.lean`。有限引数断片の特殊化
（[macro-peg-finite-specialization.md](macro-peg-finite-specialization.md)、PR #1）の上に積んでいる。

## 何を測るか

packrat（メモ化）評価器は、評価した判断（呼び出し式, 入力位置）ごとに表の項目を一つ持つ。表の大きさが packrat の
計算量を決めるので、その種類数を測る。

```lean
inductive Visits (g : MGrammar) : MExp → List Char → MExp → List Char → Prop
  -- self / seqL / seqR（前半の成功導出のあと後半を残余で）/ altL / altR（前半の失敗導出のあと）
  -- star / starR（中身の成功導出のあと star を残余で）/ notP
  -- call（規則があってアリティが合えば、代入した本体を同じ位置で。CBN なので実引数は評価しない）
def IsCall : MExp → Prop   -- 呼び出し形の式
```

`Visits` は全体の評価が終わることを要求しない。補題:

- `visits_suffix`: 訪れる位置は入力の接尾辞。
- `visits_derivable`: 全体に有限導出があれば、訪れた判断にも有限導出がある（決定性 `mderives_det` を使った反転）。
  つまり表の各項目は有限の結果を持つ。

## 上界（有限引数断片）

```lean
theorem memo_bound (F : FGrammar) (hF : F.WF) {A : Nat} {ks : List Nat} (hv : F.ValidVec A ks) (x : List Char) :
    ∀ e x', Visits F.toMacro (F.entry A ks) x e x' → IsCall e →
      memoSlot F x e x' < (F.env.length + F.specs.length) * (x.length + 1) ∧
      ∀ e₂ x₂, Visits F.toMacro (F.entry A ks) x e₂ x₂ → IsCall e₂ →
        memoSlot F x e x' = memoSlot F x e₂ x₂ → e = e₂ ∧ x' = x₂
```

`memo_bound_sum` は `|specs|` を `Σ_B |D|^arity(B)` に書き換えた形。証明:

1. `visits_rel`: 入口から訪れる式はすべて、特殊化した文法のある式と前回の対応関係 `Rel` で結ばれる
   （`Visits` の帰納法。呼び出しの場合は `rel_embed` と `rel_spec` を使う）。
2. `rel_call_nt`／`rel_call_inj`: 呼び出し形の式に対応するのは非終端 `.nt k`（`k < |env| + |specs|`）だけで、
   `k` が式を決める（環境参照と特殊化参照は添字の範囲で分かれ、特殊化参照どうしは `codeOn_inj`）。
3. 位置は接尾辞なので長さで決まる。番号は `k·(|x|+1) + (|x| − |x'|)`（`memoSlot`、古典的選択で定義した
   非計算的な関数）。

つまり有限引数断片では、表は入力の長さに線形で、定数は `|env| + Σ_B |D|^arity(B)`。

## 下界（一般の Macro PEG）

文法 `expG`: `F(x) ← "a" (F(x "0") / F(x "1"))`、開始 `F(ε)`。実引数を構築するので有限引数断片の外にある。

- `expF_fails`: どの実引数でも、どの `a^m` でも `F` は失敗する（`m` の帰納法、導出を構成）。
- `exp_step`: `F(argOf w)` を `a^(m+1)` で評価すると、`F(argOf (b :: w))` を `a^m` で評価する（`b = false` は
  左の選択肢、`b = true` は左の失敗導出 `expF_fails` のあと右の選択肢）。
- `exp_visits_all`: 入力 `a^n` で、長さ `n` の全ビット列 `w` について `F(argOf w)` を入力の末尾で訪れる。
  `argOf` は単射（`argOf_inj`）なので `2^n` 種類。

```lean
theorem no_linear_memo_bound :
    ¬ ∃ N : Nat, ∀ x : List Char, ∃ slot : MExp → List Char → Nat,
      ∀ e x', Visits expG expStart x e x' → IsCall e →
        slot e x' < N * (x.length + 1) ∧
        ∀ e₂ x₂, Visits expG expStart x e₂ x₂ → IsCall e₂ → slot e x' = slot e₂ x₂ → e = e₂ ∧ x' = x₂
```

`memo_bound` が有限引数断片のすべての文法に与える形の上界は、一般の Macro PEG では定数をどう選んでも成り立たない。
証明は鳩の巣: 長さ `n` のビット列全部（`allWords n`、`2^n` 個、重複なし）の番号は重複なしで `N·(n+1)` 未満なので
`2^n ≤ N·(n+1)`（`nodup_length_le`）、`n = 2(N+3)` で矛盾（`exists_pow_gt`）。

## 主張していないこと

- 測っているのは、呼び出し式を構文として区別したときの表の種類数。実行時間そのもの（各項目の計算量や表の操作の
  費用）は形式化していない。上界は packrat の表が線形になることの核心だが、線形時間の定理ではない。
- 下界は、実引数を構文のまま持つメモ化についての下界。部分項を共有する表現（`argOf w` を DAG で持つなど）や
  別の実装への下界ではない。言語 `{a^n}` 自体は自明に線形時間で認識できるので、**認識問題の計算複雑性の下界ではない**。
- `Visits` が CBN 評価器の評価順序を写していることは定義による。`mpegRun` との形式的な一致は示していない。
  導出との整合は `visits_derivable` で示した。

## 検証

- `lake env lean -DautoImplicit=false MacroPeg/Properties/{Visits,Complexity}.lean`（エラーなし）
- `cd lean && lake build`: `Build completed successfully (111 jobs).`
- `bash scripts/audit-source.sh`: `audit-source: OK (no sorry/admit/native_decide/axiom)`
- 新規の公開定理 19 件を `Audit.lean` に `#guard_msgs in #print axioms` で固定。すべて標準の公理だけ
  （`[propext]` 4、`[propext, Quot.sound]` 5、`[propext, Classical.choice, Quot.sound]` 10）。

## 次の目標

1. **線形時間の定理**: メモ化表つきの評価器を定義し、有限引数断片では評価の手数が `O(N·(|x|+1)·|G|)` に収まる
   ことを示す（`memo_bound` が表の大きさを、残りが項目あたりの仕事量を受け持つ）。
2. **認識問題の下界**: 実引数の構築を許す CBN Macro PEG で、構文的なメモ化ではなく言語そのものについての困難さ
   （例えばチューリング機械の模倣による決定不能性）を示す。
