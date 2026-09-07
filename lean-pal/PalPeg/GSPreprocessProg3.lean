import PalPeg.GSPreprocessProg2

/-!
# 第 2 相のオラクル `orcR` / `orc2R` の資源解析 (`GSPreprocessProg3`)

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

/-- 内側走査 1 ステップ (`sActs` の継続枝) は `p` と `r` を変えず `q` だけ 1 増やす。
これが単調性（＝カウントダウンでよいこと）の根拠。 -/
theorem sActs_step_enc {s q' D' E' p' F' S' r : ℕ} {ts : Tapes sc}
    (h : sCond endSym (orcR k) ts)
    (hE : Enc blank startSym endSym mark x (s + q') (s + p' + q')
      ⟨D', q', E', p', F', S', r⟩ ts)
    (hlt : s + p' + q' < x.length) :
    Enc blank startSym endSym mark x (s + (q' + 1)) (s + p' + (q' + 1))
      ⟨D', q' + 1, E', p', F', S', r⟩ (applyActs blank (sActs blank endSym (orcR k) ts) ts) := by
  rw [applyActs_sActs_pos h]
  have h1 : s + q' < x.length := by omega
  have e1 : s + (q' + 1) = s + q' + 1 := by omega
  have e2 : s + p' + (q' + 1) = s + p' + q' + 1 := by omega
  rw [e1, e2]
  exact ⟨pat_right hE.v1 h1, pat_right hE.v2 hlt, hE.cd,
    Tape.counter'_inc hE.cq, hE.ce, hE.cp, hE.cf, hE.cs, hE.cr⟩

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

end PalPeg.GSPreProg
