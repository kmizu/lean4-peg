import PalPeg.GSPreprocessProg2

/-!
# 第 2 相のオラクル `orcR` / `orc2R` の資源解析 (`GSPreprocessProg3`)

**現在の実装**：`GSPreprocessTapes` は12本のテープを使い、符号つき差を
各走査ステップで更新する。`sActs_step_enc` もこの実装を扱う。
以下の9本・しきい値のみの設計案と末尾の資源棚卸しは以前の検討記録であり、
現在のテープ本数・定理の型・コスト定数を記述するものではない。
分解器全体を入力長非依存の有限 `Prog` にする接続は未完了である。

`PalPeg.GSPreprocessProg2` で `orcCf` の比較ガジェット `CMPLT_PF` を作ったが、
`orcR` / `orc2R` については同じ構成が使えない。本ファイルはその理由を明示し、
代わりに必要となる**しきい値による書き換え**を証明する。

## なぜ `orcR` に比較ガジェットを置けないか

`sProg`（第 2 相の内側走査）は

```
sCond endSym orc ts = (V2 の読み ≠ endSym ∧ V1 の読み = V2 の読み ∧ orc ts = false)
sActs … = if sCond … then [V1 .right, V2 .right, Cq blank .right] else []
```

なので、`orcR` は**内側走査の 1 ステップごとに 1 回**評価される。1 ステップの
コストは 3 動作しかないから、評価 1 回に `Θ(p + q + r)` 動作かかる比較ガジェットを
置くと内側走査全体が `Θ(q · |x|)` になり、目標の線形計上
`A · decompose2Work + B · (|x|+1)` を超える。
（`orc2R` は `soShift` の中で外側 1 反復につき 1 回しか評価されないので、
この問題は起きない。）

## 逃げ道：`orcR` は `q` について単調（しきい値述語）である

`sActs` は `Cq` を 1 増やすだけで `Cp` にも `Cr` にも触れないので、内側走査のあいだ
`p` と `r` は不変で `q` だけが 1 ずつ増える。`orcR` の 2 つの連言項は
どちらも `q` について単調増加なので、`orcR` は

```
orcR  ⟺  orcThreshold k r p ≤ q,    orcThreshold k r p = max (r - p) ((k-1)*p - 1)
```

という**しきい値述語**である。したがって内側走査に入る前に `orcThreshold k r p - q`
をカウンタに載せ、1 ステップごとに 1 減らして「ゼロか」を probe すれば、
1 ステップあたり `O(1)` 動作で `orcR` を判定できる。本ファイルはこの書き換えが
正しいことを証明する（実装は `sProg` 自体の作り直しになるので未着手）。
-/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM
open PalPeg.GSPre

variable {sc : ℕ}

/-! ## 19. `orcR` のしきい値表現 -/

/-- 内側走査の中断しきい値。`q` がこの値以上になった瞬間に `orcR` が真になる。 -/
def orcThreshold (k r p : ℕ) : ℕ := max (r - p) ((k - 1) * p - 1)

/-- **`orcR` はしきい値述語**。 -/
theorem orcR_iff_threshold (k r p q : ℕ) :
    (r < p + q + 1 ∧ (k - 1) * p ≤ q + 1) ↔ orcThreshold k r p ≤ q := by
  unfold orcThreshold
  omega

/-- `orcR` は `q` について単調（いったん真になったら真のまま）。 -/
theorem orcR_mono_q (k r p : ℕ) {q : ℕ}
    (h : r < p + q + 1 ∧ (k - 1) * p ≤ q + 1) :
    r < p + (q + 1) + 1 ∧ (k - 1) * p ≤ (q + 1) + 1 := by
  omega

/-- 1 ステップでしきい値までの残りがちょうど 1 減る。 -/
theorem orcThreshold_countdown (k r p q : ℕ) :
    orcThreshold k r p - (q + 1) = (orcThreshold k r p - q) - 1 := by
  omega

/-- カウントダウンがゼロであることが `orcR` と一致する。 -/
theorem orcThreshold_zero_iff (k r p q : ℕ) :
    orcThreshold k r p - q = 0 ↔ (r < p + q + 1 ∧ (k - 1) * p ≤ q + 1) := by
  rw [orcR_iff_threshold]
  omega

section Spec

variable {blank startSym endSym mark : Fin sc} {x : List (Fin sc)} {k : ℕ}

/-- **カウントダウン実装が満たすべき仕様**：`orcR` はテープ上の
`orcThreshold k r (pOf ts') ≤ qOf ts'` の判定と一致する。 -/
theorem orcR_threshold_spec {s q' D' E' p' F' S' r : ℕ} {ts' : Tapes sc}
    (hE : Enc blank startSym endSym mark x (s + q') (s + p' + q')
      ⟨D', q', E', p', F', S', r⟩ ts') :
    orcR k ts' = decide (orcThreshold k r p' ≤ q') := by
  rw [orcR_spec (k := k) hE]
  exact decide_eq_decide.2 (orcR_iff_threshold k r p' q')

/-- 内側走査は `p` と `r` を保ち、`q` を増やして符号つき差を更新する。 -/
theorem sActs_step_enc {s q' D' E' p' F' S' r : ℕ} {g : Ctr3} {ts : Tapes sc}
    (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (h : sCond endSym (orcR k) ts)
    (hE : EncS blank startSym endSym mark x (s + q') (s + p' + q')
      ⟨D', q', E', p', F', S', r⟩ g ts) :
    EncS blank startSym endSym mark x (s + (q' + 1)) (s + p' + (q' + 1))
      ⟨D' - 1, q' + 1, E', p', F', S', r⟩
      ⟨g.ap - 1, g.an + (if g.ap = 0 then 1 else 0), g.bn + (if D' = 0 then 1 else 0)⟩
      (applyActs blank (sActs blank endSym mark (orcR k) ts) ts) := by
  simpa only [Nat.add_assoc] using encS_s_step hend hmark hE (by omega) h

end Spec

/-! ## 20. 資源の棚卸し（9 本テープで何が空いているか）

第 2 相（`soProg` / `sProg`）の符号化は `⟨D, q, 0, p, first, S, r⟩` である
（`soProg_spec` の入口条件、および `Ce` は最後のフラグ書き込みまで常に `0`）。
したがって

* `Ce` … **空いている**（値 `0`）。
* `Cd` … **空いていない**。`shiftPhase_enc` が示すとおり `Cd` は
  `(k-1)*p - q` から `(k-1)*(p + shiftNoPeriod q k)` へと増えていく、
  第 1 相の予算カウンタとして生きている。
* `Cq`, `Cp`, `Cf`, `Cr` … 比較の対象そのもの。`Cs` は切断位置 `s` を保持。
* `V1`, `V2` … 文字テープ。

つまり第 2 相で自由に使えるカウンタは `Ce` **1 本だけ**である。
`GSPreprocessProg2` の `CMPLT_PF` は鏡像を **2 本**（`Cq` と `Ce`）必要とするので、
そのままでは `orcR` にも `orc2R` にも適用できない。
（`orcCf` の判定点では `Cq = Ce = 0` の 2 本が空いていた。）

### 10 本目のテープを足さずに 2 本目を空ける道

`spProg_spec` の入口では `Cd = 0` である（`firstPeriod` の成功判定が
`probe Cd = mark`、すなわち `Cd = 0` そのものであり、`frTail` も `repoProg` も
`Cd` に触れないため）。`Cd` が非零になるのは `soProg` の反復のなかで
`shiftPhase` が予算 `(k-1)*p - q` を積むからである。そしてこの値は
`Cp` と `Cq` から `(k-1)*p - q` として**再計算できる**（コストは `Θ(k·p + q)`、
外側 1 反復あたり 1 回）。したがって `shiftPhase` を「`Cd` に予算を保持する」形から
「必要になった時点で `Cp`/`Cq` から作り直す」形へ変えれば、第 2 相を通じて
`Cd` を空きテープにでき、`Ce` と合わせて鏡像 2 本が確保できる。
これは `Tapes` の本数を増やさずに済む唯一の道筋であり、`PrepInstance` の
9→12 スロット（空きなし）を触らなくてよい。ただし `shiftPhase_enc`,
`soProg_spec`, `spProg_spec`, `stepProg_spec` のコスト計上をすべて取り直す必要がある。
-/

#print axioms orcR_iff_threshold
#print axioms orcR_threshold_spec
#print axioms sActs_step_enc

/-! ## 21. `Cd` の解放（実施済み）と、カウントダウン設計の訂正

### 実施済み：第 2 相で `Cd` を空けた

`GSPreprocessTapes` に `rewindUnit2` / `rewindLoop2` / `rewind2_enc` /
`shiftPhase2` / `shiftPhase2_enc'` を追加し、`soShift` を `shiftPhase2` に切り替えた。
第 2 相で `Cd` は**まったく書かれなくなった**（`shiftPhase2_enc'` の結論は `Cd = D` で不変）。
`soProg_spec` / `spProg_spec` / `stepProg_spec` / `decProg_spec` /
`decompose2_on_tapes` の**文はすべてそのまま**で通り、`PrepInstance` /
`PrepInstances` / `DecompInstance` も無修正で通る（動作数はむしろ減るので
既存の上界はそのまま成立する）。

### 訂正：「しきい値を 1 度だけ載せる」設計では線形にならない

§19 の `orcThreshold` を内側走査の入口で 1 度計算する案は、コストが合わない。
`secondOuterWork` の 1 反復ぶんの取り分は `1 + secondInnerWork` であって、
`Θ(p)` も `Θ(k·p)` も含まない。一方 `orcThreshold k r p = max (r - p) ((k-1)*p - 1)`
を作るには `Cr` と `(k-1)·Cp` を読む必要があり `Θ(k·p + r)` かかる。
反復ごとにこれを払うと、`p` は反復ごとに 1 以上増え反復数は `Θ(|x|)` なので
総計 `Θ(k·|x|²)` になり、目標の線形計上を超える。

### 正しい設計：2 つの符号つきカウンタを漸進的に保つ

`orcR` は 2 つの飽和差の同時ゼロ判定である：

```
orcR  ⟺  A = 0 ∧ B = 0,   A = r ∸ (p+q),   B = (k-1)*p ∸ (q+1)
```

内側 1 ステップ（`q += 1`）では `A`, `B` がそれぞれ 1 減るだけなので `O(1)`。
問題は外側のずらしで、飽和値だけでは更新できない（`satB_not_incremental`）。
**符号つき**（正部・負部の 2 本組）で持てば更新は正確になり、しかも

* 周期ずらし（`p += first`, `q -= first`）では `A` は**不変**（`satA_period_shift_invariant`）、
  `B` は `+ k*first`（`signedB_period_shift`）。この枝は `k*first ≤ q'` を満たすので
  更新コスト `Θ(k*first) ≤ Θ(q')` はその反復の内側走査に付け替えられる。
* リセットずらし（`p += e`, `q := 0`）では `A` の変化は `q - e`、`B` の変化は
  `q + (k-1)*e`。`e ≤ q+1` なので `Θ(k*q)`、やはりその反復の内側走査（`q` ステップ）に
  付け替えられる。

つまり計上は通る。**しかしテープが足りない。** 符号つきカウンタは 1 つにつき 2 本、
`A` と `B` で計 4 本の作業テープが要る。第 2 相で空いているのは
`Cd`（本節で解放）と、`shiftPhase2` のスクラッチ兼フラグである `Ce` の
実質 1〜2 本にすぎない（`Cq`=q, `Cp`=p, `Cf`=first, `Cs`=s, `Cr`=r は生きている）。
`Cr` を `A` の正部に転用しても 3 本目・4 本目が出てこない。

したがって **9 本のままでは `orcR` を `O(1)/ステップ` で判定できない**。
`Tapes` を 11〜12 本へ増やすのが（線形計上を保ったままの）唯一の道であり、
そのとき `PrepInstance` の 9→12 スロット割り当ての見直しが必要になる。
-/

section Countdown

/-- `orcR` は 2 つの飽和差の同時ゼロ判定。 -/
theorem orcR_iff_two_counters (k r p q : ℕ) :
    (r < p + q + 1 ∧ (k - 1) * p ≤ q + 1)
      ↔ (r - (p + q) = 0 ∧ (k - 1) * p - (q + 1) = 0) := by
  omega

/-- 内側 1 ステップで両方ちょうど 1 ずつ（飽和的に）減る。 -/
theorem two_counters_step (k r p q : ℕ) :
    r - (p + (q + 1)) = (r - (p + q)) - 1
      ∧ (k - 1) * p - ((q + 1) + 1) = ((k - 1) * p - (q + 1)) - 1 := by
  omega

/-- 周期ずらしで `A` は不変。 -/
theorem satA_period_shift_invariant (r p q first : ℕ) (h : first ≤ q) :
    r - ((p + first) + (q - first)) = r - (p + q) := by omega

/-- **飽和値だけでは `B` を漸進更新できない**：`B` が等しい 2 つの状態が、
周期ずらし後に異なる `B` を持つ。 -/
theorem satB_not_incremental :
    ∃ (k p first q₁ q₂ : ℕ),
      3 ≤ k ∧ first ≤ q₁ ∧ first ≤ q₂ ∧
      (k - 1) * p - (q₁ + 1) = (k - 1) * p - (q₂ + 1) ∧
      (k - 1) * (p + first) - ((q₁ - first) + 1)
        ≠ (k - 1) * (p + first) - ((q₂ - first) + 1) :=
  ⟨3, 1, 1, 3, 5, by norm_num⟩

/-- 符号つきで持てば周期ずらしの更新は正確に `+ k*first`。 -/
theorem signedB_period_shift (k p q first : ℤ) :
    (k - 1) * (p + first) - ((q - first) + 1) = ((k - 1) * p - (q + 1)) + k * first := by
  ring

/-- 符号つきで持てばリセットずらしの `A` の更新は `+ (q - e)`。 -/
theorem signedA_noperiod_shift (r p q e : ℤ) :
    r - (p + e) = (r - (p + q)) + (q - e) := by ring

/-- 符号つきで持てばリセットずらしの `B` の更新は `+ (q + (k-1)*e)`。 -/
theorem signedB_noperiod_shift (k p q e : ℤ) :
    (k - 1) * (p + e) - (0 + 1) = ((k - 1) * p - (q + 1)) + (q + (k - 1) * e) := by
  ring

end Countdown

#print axioms orcR_iff_two_counters
#print axioms satB_not_incremental
#print axioms signedB_period_shift

end PalPeg.GSPreProg
