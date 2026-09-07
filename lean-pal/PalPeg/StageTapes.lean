import PalPeg.StageMatcherTapes
import PalPeg.MiddleTapes
import PalPeg.EndToEnd2

/-!
# 一つの段の全生涯をテープ上で実現する (`StageTapes`)

幅 `S`（偶数）の段は `OnlineMachine` §7 の半分割スケジュール `stageStateH` に従い、
絶対ラウンド `S / 2` に生まれ、`[2S, 4S)` の各ラウンドで答えを出して `4S` で死ぬ。
本ファイルはその 1 段を **テープ機械の一枚の記録** として組み立てる。

## スケジュール（`8 ≤ S`, `4 * (S / 4) = S`）

| ラウンド | 動作 |
|---|---|
| `n ≤ S/2` | 休止（段は未生成） |
| `S/2 < n ≤ 3(S/4)` | 前処理 `PrepOnTapes.prog` を毎ラウンド `rateP` 動作ずつ挽く ＋ 中央仕事 `mround` |
| `3(S/4) < n ≤ S` | 準備 `PatternTapes.setupProgram` を毎ラウンド `rateS = 160` 動作ずつ挽く ＋ `mround` |
| `S < n ≤ S + |u|` | 照合器の起動フェーズ（`≤ 86` 動作／ラウンド） ＋ `mround` |
| `S + |u| < n < 4S` | 照合器 `sround` ＋ 中央仕事 `mround` |

前処理は `S/4` ラウンドで、準備は `S/4` ラウンドで終わる（`prep_rate_ok` / `setup_rate_ok`）。
照合器の局所時計は `Metered.metered_start` により `[0, |u|]` で止まっているので、
`stage` の反復 `i` は絶対ラウンド `S + |u| + i` に対応する（`ststate_sm`）。

## 残るインタフェース仮定

* `PrepOnTapes`（`GSPreprocessTapes.decompose2_on_tapes` の抽象化）。
* `MiddleTapes.DecompOnTapes`（既存）。
* `hInB` : 誕生時に入力コピー `sIn` が使えること（`PrepOnTapes.post` の `SetupPre.inb` に内包）。
* `hbirth` : 絶対ラウンド `S + |u|` に照合器成分が `initSM` に一致していること
  （起動フェーズ `vstartT'` を `(S, S + |u|]` に配ることの帰結。ここでは仮定）。
-/

namespace PalPeg
namespace StageTapes

open PegSeparation.RealTimeTM
open PalPeg.PatternTapes
open PalPeg.StageMatcherTapes
open PalPeg.MiddleTapes
open PalPeg.VerifierFeed

variable {sc : ℕ}

/-! ## 1. 12 本テープ上の汎用「挽き」機構 -/

/-- 挽き途中の 12 本テープのジョブ。 -/
structure SGrind (sc : ℕ) where
  /-- まだ実行していない動作。 -/
  rem : List (SAct sc)
  /-- 12 本のテープ。 -/
  ts : Tapes sc

/-- 1 ラウンド：先頭 `R` 個の動作を実行する。 -/
def sgstep (blank : Fin sc) (R : ℕ) (g : SGrind sc) : SGrind sc :=
  ⟨g.rem.drop R, run blank (g.rem.take R) g.ts⟩

/-- `n` ラウンド挽く。 -/
def sgsteps (blank : Fin sc) (R : ℕ) : ℕ → SGrind sc → SGrind sc
  | 0, g => g
  | n + 1, g => sgsteps blank R n (sgstep blank R g)

/-- 1 ラウンドの実費用。 -/
def sgcost (R : ℕ) (g : SGrind sc) : ℕ := min R g.rem.length

theorem sgcost_le (R : ℕ) (g : SGrind sc) : sgcost R g ≤ R := Nat.min_le_left _ _

theorem sgsteps_nil (blank : Fin sc) (R : ℕ) :
    ∀ (n : ℕ) (ts : Tapes sc), sgsteps blank R n ⟨[], ts⟩ = ⟨[], ts⟩ := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih =>
    intro ts
    rw [sgsteps, show sgstep blank R (⟨[], ts⟩ : SGrind sc) = ⟨[], ts⟩ by simp [sgstep, run]]
    exact ih _

/-- **完了**：`n * R` が動作数以上なら `n` ラウンドで挽き終わる。 -/
theorem sgsteps_done (blank : Fin sc) {R : ℕ} :
    ∀ (n : ℕ) (l : List (SAct sc)) (ts : Tapes sc), l.length ≤ n * R →
      sgsteps blank R n ⟨l, ts⟩ = ⟨[], run blank l ts⟩ := by
  intro n
  induction n with
  | zero =>
    intro l ts h
    simp only [Nat.zero_mul, Nat.le_zero, List.length_eq_zero_iff] at h
    subst h; rfl
  | succ n ih =>
    intro l ts h
    have hlen : (l.drop R).length ≤ n * R := by
      simp only [List.length_drop]
      have : (n + 1) * R = n * R + R := by ring
      omega
    have hstep : sgstep blank R (⟨l, ts⟩ : SGrind sc)
        = ⟨l.drop R, run blank (l.take R) ts⟩ := rfl
    rw [sgsteps, hstep, ih (l.drop R) (run blank (l.take R) ts) hlen,
      ← run_append, List.take_append_drop]

/-! ## 2. 前処理のテープ実装インタフェース -/

/-- **前処理の入力仮定**。段が生まれる時点（絶対ラウンド `S/2`）に 12 本のテープが
満たしている配置：入力コピー `sIn` には左端番兵つきのパターン `leftSym :: w.take L` が
載りヘッドは添字 `L`（＝最後にコピーした記号の位置。番兵より右は未来の入力を含まない）、
`sT` / `sX2` にはテキスト、`sU` / `sP` は空、単進カウンタ 7 本はすべて `0`。
`PatternTapes.SetupPre` との差は、`sCs` / `sC1` / `sRp` が「まだ `0`」である点だけで、
それらを埋めるのが前処理の仕事である。 -/
structure PrepPre (blank mark leftSym : Fin sc) (L : ℕ) (w Text : List (Fin sc))
    (ts : Tapes sc) : Prop where
  /-- パターン長は正。 -/
  hpos : 0 < L
  /-- 到着済みの入力はパターンを含む。 -/
  hle : L ≤ w.length
  /-- 左端番兵は入力に現れない。 -/
  hfresh : leftSym ∉ w
  /-- 入力コピー `sIn`：左端番兵つきの `leftSym :: w.take L` の添字 `L`
  （＝最後にコピーした記号 `w[L-1]` の位置）。 -/
  inb : Tape.SeqView blank (ts sIn) (leftSym :: w.take L) L
  /-- 検証器の接頭辞テープは空。 -/
  emptyU : Tape.StackView blank (ts sU) []
  /-- 走査器のパターンテープは空。 -/
  emptyP : Tape.StackView blank (ts sP) []
  /-- テキスト 1 本目。 -/
  txt : Tape.SeqView blank (ts sT) (TextFeed.padW blank Text 0) 0
  /-- テキスト 2 本目。 -/
  txt2 : Tape.SeqView blank (ts sX2) (TextFeed.padW blank Text 0) 0
  /-- 作業用カウンタはすべて `0`。 -/
  cs : Tape.CounterView' blank mark (ts sCs) 0
  c1 : Tape.CounterView' blank mark (ts sC1) 0
  c2 : Tape.CounterView' blank mark (ts sC2) 0
  ap : Tape.CounterView' blank mark (ts sAp) 0
  an : Tape.CounterView' blank mark (ts sAn) 0
  rp : Tape.CounterView' blank mark (ts sRp) 0
  rn : Tape.CounterView' blank mark (ts sRn) 0

/-- **前処理のインタフェース**（`GSPreprocessTapes` の抽象化）。
入力コピー `sIn` に載っているパターン `w.take L` から、切断点・周期・到達域の
単進カウンタ（`sCs` / `sC1` / `sRp`）を作り、`PatternTapes.SetupPre` を満たす
テープ配置を作る動作列。長さは `Cp * L + Dp` 以下。

`decompose2_on_tapes`（`GSPreprocessTapes.GSPre`）の具体化は、パターン `x` の中に
「終端の番人」として使う記号 `forb` が現れないことを必要とする（さもないと `x` 内の
データを番人と誤認する）。この必要条件は `PrepOnTapes` 自身には現れず、これを
呼び出す `stage_tapes_spec'` 側がすでに `hend : endSym ∉ w` を持っているので、
`forb` をパラメータとして持たせ、`post` にその不在仮定を追加する。 -/
structure PrepOnTapes (sc : ℕ) (blank mark forb : Fin sc) where
  /-- 動作列（読んだ入力とパターン長とテープから決まる）。 -/
  prog : List (Fin sc) → ℕ → Tapes sc → List (SAct sc)
  /-- 分解 `(s, p₁, r)`。 -/
  res : List (Fin sc) → ℕ → ℕ × ℕ × ℕ
  /-- 費用の傾き。 -/
  Cp : ℕ
  /-- 費用の切片。 -/
  Dp : ℕ
  len_le : ∀ (w Text : List (Fin sc)) (L : ℕ) (ts : Tapes sc) (leftSym : Fin sc),
    PrepPre blank mark leftSym L w Text ts → forb ∉ w →
    (prog (w.take L) L ts).length ≤ Cp * L + Dp
  post : ∀ (w Text : List (Fin sc)) (L : ℕ) (ts : Tapes sc) (leftSym : Fin sc),
    PrepPre blank mark leftSym L w Text ts → forb ∉ w → (res w L).1 < L →
    SetupPre blank mark leftSym (res w L).1 L (res w L).2.1 (res w L).2.2 w Text
      (run blank (prog (w.take L) L ts) ts)

/-- 前処理を挽く速度。 -/
def rateP {blank mark forb : Fin sc} (Pre : PrepOnTapes sc blank mark forb) : ℕ :=
  2 * Pre.Cp + Pre.Dp

/-- 準備フェーズ（`setupProgram`）を挽く速度。 -/
def rateS : ℕ := 160

/-! ## 3. スケジュールの算術 -/

/-- **前処理は `S/4` ラウンドで終わる**：`Cp * (S/2) + Dp ≤ (S/4) * rateP`。 -/
theorem prep_rate_ok {Cp Dp S : ℕ} (hS : 8 ≤ S) (hq : 4 * (S / 4) = S) :
    Cp * (S / 2) + Dp ≤ (S / 4) * (2 * Cp + Dp) := by
  have hq1 : 1 ≤ S / 4 := by omega
  have hhalf : S / 2 = 2 * (S / 4) := by omega
  have hexp : (S / 4) * (2 * Cp + Dp) = Cp * (2 * (S / 4)) + (S / 4) * Dp := by ring
  have : Dp ≤ (S / 4) * Dp := Nat.le_mul_of_pos_left _ hq1
  rw [hhalf, hexp]
  omega

/-- **準備フェーズは `S/4` ラウンドで終わる**：`setup_spec` の上界
`7 * (S/2 + k*p₁ + 1)` は `(S/4) * 160` 以下（`k * p₁ ≤ 5 * S` のとき）。 -/
theorem setup_rate_ok {S k p₁ : ℕ} (hS : 8 ≤ S) (hq : 4 * (S / 4) = S)
    (hkp : k * p₁ ≤ 5 * S) :
    7 * (S / 2 + k * p₁ + 1) ≤ (S / 4) * rateS := by
  have hq1 : 2 ≤ S / 4 := by omega
  have hhalf : S / 2 = 2 * (S / 4) := by omega
  have hexp : (S / 4) * rateS = 160 * (S / 4) := by rw [rateS]; ring
  omega

/-! ## 3b. 準備フェーズのテープから照合器を起こす -/

section StartVM

variable {blank startSym endSym mark : Fin sc}

/-- **準備フェーズの 12 本テープから作る照合器の初期機械**。走査 8 本と検証器 2 本は
`PatternTapes.toGS` / `toVExt` でそのまま取り、待ち行列は 2 本とも空
（`RTQueueTapes.initQT`）、書き込み済み記号数は `0`、ゴーストは `(⟨0,0⟩, 0)`。 -/
def startVM (blank _startSym _endSym mark : Fin sc) (ts : Tapes sc) : VMachine' sc :=
  { m1 := 0
    m2 := 0
    vt := (toGS ts, toVExt ts)
    Q1 := (RTQueue.empty : RTQueue.Queue (Fin sc))
    Q2 := (RTQueue.empty : RTQueue.Queue (Fin sc))
    R1 := ⟨RTQueueTapes.initQT blank mark, 0⟩
    R2 := ⟨RTQueueTapes.initQT blank mark, 0⟩
    z := ((⟨0, 0⟩ : ScanState), 0) }

/-- `startVM` の走査段は `TextFeed.FeedInv'` をラウンド `0` で満たす
（`PatternTapes.setup_spec` の `VEncodes'` と `RTQueueTapes.initQT_encodes` から）。 -/
theorem startVM_feedInv {u v Text : List (Fin sc)} {k p₁ r : ℕ} {ts : Tapes sc}
    (hE : GSVTapes.VEncodes' blank startSym endSym mark u v (TextFeed.padW blank Text 0) k p₁ r
      (toGS ts, toVExt ts) ((⟨0, 0⟩ : ScanState), 0)) :
    TextFeed.FeedInv' blank startSym endSym mark v Text k p₁ r 0
      (toM (startVM blank startSym endSym mark ts)) :=
  { scan := hE.scan
    buf := RTQueueTapes.initQT_encodes blank mark
    qinv := RTQueue.inv_empty
    qlist := by
      show RTQueue.toList (RTQueue.empty : RTQueue.Queue (Fin sc)) = (Text.take 0).drop 0
      simp [RTQueue.toList_empty]
    mle := Nat.le_refl 0
    hd := Nat.le_refl 0
    qle := Nat.zero_le _ }

/-- **`vstart_spec_of`**：`VerifierFeed.vstart_spec` を、`initVM'` ではなく
`VEncodes'` を満たす任意のテープ配置から起こした機械について述べたもの。 -/
theorem vstart_spec_of {u v Text : List (Fin sc)} {k p₁ r : ℕ} {ts : Tapes sc}
    (hmb : mark ≠ blank) (hv : 0 < v.length) (hlen : u.length ≤ Text.length)
    (hE : GSVTapes.VEncodes' blank startSym endSym mark u v (TextFeed.padW blank Text 0) k p₁ r
      (toGS ts, toVExt ts) ((⟨0, 0⟩ : ScanState), 0)) :
    VFeedInv' blank startSym endSym mark u v Text k p₁ r u.length
        (vstartT' blank mark Text u.length (startVM blank startSym endSym mark ts)) ∧
      (vstartT' blank mark Text u.length (startVM blank startSym endSym mark ts)).z
        = vOnlineRun u v k p₁ r Text u.length ∧
      (vstartT' blank mark Text u.length
        (startVM blank startSym endSym mark ts)).cost ≤ 86 * u.length := by
  set M0 := startVM blank startSym endSym mark ts with hM0
  set MS := vstartT' blank mark Text u.length M0 with hMS
  obtain ⟨s1, s2, _, s4⟩ := TextFeed.startT'_spec (blank := blank) (mark := mark) (v := v)
    (startSym := startSym) (endSym := endSym) (k := k) (p₁ := p₁) (r := r) hmb rfl rfl
    (startVM_feedInv hE) u.length hlen
  have hproj : toM MS = TextFeed.startT' blank mark Text u.length (toM M0) := by
    rw [hMS, toM_vstartT']
  rw [← hproj] at s1 s2 s4
  have hR1 : (toM MS).R.cost = MS.R1.cost := rfl
  have hI0 : (toM M0).R.cost = 0 := rfl
  rw [hR1, hI0] at s4
  obtain ⟨x1, x2, x3⟩ := vstartT'_ext blank mark Text u.length M0
  obtain ⟨q1, q2, q3, q4⟩ := vstartT'_queue2 (Text := Text) (M := M0) hmb u.length hlen
    (RTQueueTapes.initQT_encodes blank mark) RTQueue.inv_empty
    (by show RTQueue.toList (RTQueue.empty : RTQueue.Queue (Fin sc)) = []
        simp [RTQueue.toList_empty])
  rw [← hMS] at q1 q2 q3 q4
  have hQ0 : M0.R2.cost = 0 := rfl
  rw [hQ0] at q4
  have hz : MS.z = ((⟨u.length, 0⟩ : ScanState), 0) := by
    have h1 : MS.z.1 = (⟨u.length, 0⟩ : ScanState) := s2
    have h2 : MS.z.2 = 0 := by rw [x3]; rfl
    exact Prod.ext h1 h2
  have hm2 : MS.m2 = 0 := by rw [x2]; rfl
  have hvt2 : MS.vt.2 = M0.vt.2 := x1
  have hstart : VFeedInv' blank startSym endSym mark u v Text k p₁ r u.length MS := by
    refine ⟨s1.scan, ?_, ?_, s1.buf, s1.qinv, s1.qlist, s1.mle, q1, q2, ?_, ?_,
      s1.hd, ?_, s1.qle, ?_, ?_⟩
    · rw [hz]
      show Tape.SeqView blank MS.vt.2.U (startSym :: (u ++ [endSym])) (0 + 1)
      rw [hvt2]
      exact hE.pat
    · rw [hz, hm2]
      show Tape.SeqView blank MS.vt.2.Txt2 (TextFeed.padW blank Text 0) (u.length - u.length + 0)
      rw [hvt2, show u.length - u.length + 0 = 0 from by omega]
      have := hE.txt2
      rwa [show (0 : ℕ) - u.length + 0 = 0 from by omega] at this
    · rw [hm2, q3]; simp
    · rw [hm2]; exact Nat.zero_le _
    · rw [hz, hm2]
      show u.length - u.length + 0 ≤ 0
      omega
    · rw [hz]; exact Nat.zero_le _
    · rw [hz]
  have hcost0 : MS.cost ≤ 86 * u.length := by
    show MS.R1.cost + MS.R2.cost ≤ 86 * u.length
    have e : 86 * u.length = 60 * u.length + 26 * u.length := by ring
    omega
  exact ⟨hstart, by rw [hz, vOnlineRun_start hv u.length (Nat.le_refl _)], hcost0⟩

/-- 準備フェーズのテープから起こした照合器の起動後の状態（`initSM` の一般化）。 -/
def initSM' (blank startSym endSym mark : Fin sc) (u Text : List (Fin sc))
    (ts : Tapes sc) : SMachine sc :=
  ⟨vstartT' blank mark Text u.length (startVM blank startSym endSym mark ts), 0⟩

/-- **`stage_init_of`**：`StageMatcherTapes.stage_init` の一般化。ゴーストは
`Metered.metered … |u|` に一致し、起動フェーズの費用は `≤ 86 * |u|`。 -/
theorem stage_init_of {u v Text : List (Fin sc)} {k p₁ r : ℕ} {ts : Tapes sc}
    {cst : ScanState → ℕ} {A B' : ℕ}
    (hmb : mark ≠ blank) (hv : 0 < v.length) (hlen : u.length ≤ Text.length)
    (hE : GSVTapes.VEncodes' blank startSym endSym mark u v (TextFeed.padW blank Text 0) k p₁ r
      (toGS ts, toVExt ts) ((⟨0, 0⟩ : ScanState), 0)) :
    SBnd blank startSym endSym mark u v Text k p₁ r u.length
        (initSM' blank startSym endSym mark u Text ts) ∧
      gm (initSM' blank startSym endSym mark u Text ts)
        = metered u v k p₁ r Text cst A B' u.length ∧
      (initSM' blank startSym endSym mark u Text ts).M.cost ≤ 86 * u.length := by
  obtain ⟨h1, h2, h3⟩ := vstart_spec_of hmb hv hlen hE
  have hz : (initSM' blank startSym endSym mark u Text ts).M.z
      = ((⟨u.length, 0⟩ : ScanState), 0) := by
    show (vstartT' blank mark Text u.length (startVM blank startSym endSym mark ts)).z = _
    rw [h2, vOnlineRun_start hv u.length (Nat.le_refl _)]
  exact ⟨⟨h1, by simp [initSM']⟩, gm_start (cst := cst) (A := A) (B' := B') hv hz rfl, h3⟩

end StartVM

/-! ## 4. 段の状態と 1 ラウンド -/

/-- **一つの段のテープ側の記録**。 -/
structure StageT (sc : ℕ) where
  /-- 照合器（走査 8 本＋検証器 2 本＋待ち行列 2 本、計量スケジューラつき）。 -/
  sm : SMachine sc
  /-- 中央フラグの仕事（6 本＋読み出しフラグ＋入力コピー）。 -/
  md : MiddleTapes.MState sc
  /-- 前処理・準備フェーズの挽き（12 本）。 -/
  pg : SGrind sc

variable {blank startSym endSym mark forb : Fin sc}

/-- 準備フェーズの 1 ラウンド分の挽き（起動ラウンドではプログラムを載せる）。 -/
def setupGrind (blank startSym endSym : Fin sc) (k S n : ℕ) (g : SGrind sc) : SGrind sc :=
  sgstep blank rateS
    (if n = 3 * (S / 4) + 1 then ⟨setupProgram blank startSym endSym k g.ts, g.ts⟩ else g)

/-- **段の 1 ラウンド**。`t` は到着済みの入力、`a` はこのラウンドに到着した記号、
`n` は絶対ラウンド番号。 -/
def stround (D : DecompOnTapes sc blank startSym endSym mark)
    (Pre : PrepOnTapes sc blank mark forb) (leftSym one zero : Fin sc)
    (u v Text : List (Fin sc)) (k pe re : ℕ) (cst : ScanState → ℕ) (A B' S : ℕ)
    (t : List (Fin sc)) (a : Fin sc) (n : ℕ) (St : StageT sc) : StageT sc :=
  if n ≤ S / 2 then St
  else if n ≤ 3 * (S / 4) then
    ⟨St.sm, mround blank startSym endSym mark leftSym one zero D t a n St.md,
      sgstep blank (rateP Pre)
        (if n = S / 2 + 1 then ⟨Pre.prog (t.take (S / 2)) (S / 2) St.pg.ts, St.pg.ts⟩
          else St.pg)⟩
  else if n ≤ S then
    ⟨if n = S then
        ⟨startVM blank startSym endSym mark (setupGrind blank startSym endSym k S n St.pg).ts,
          0⟩
      else St.sm,
      mround blank startSym endSym mark leftSym one zero D t a n St.md,
      setupGrind blank startSym endSym k S n St.pg⟩
  else if n ≤ S + u.length then
    ⟨⟨vstartRound' blank mark (Text.getD (n - 1 - S) blank) St.sm.M, St.sm.rem⟩,
      mround blank startSym endSym mark leftSym one zero D t a n St.md, St.pg⟩
  else
    ⟨sround blank endSym mark u v k pe re Text cst A B' (n - 1 - S)
        (Text.getD (n - 1 - S) blank) St.sm,
      mround blank startSym endSym mark leftSym one zero D t a n St.md, St.pg⟩

/-- 1 ラウンドの費用。 -/
def stcost (D : DecompOnTapes sc blank startSym endSym mark)
    (Pre : PrepOnTapes sc blank mark forb) (u : List (Fin sc)) (U A B' k S : ℕ)
    (n : ℕ) (St : StageT sc) : ℕ :=
  if n ≤ S / 2 then 0
  else
    mcost D n St.md +
      (if n ≤ 3 * (S / 4) then sgcost (rateP Pre) St.pg
        else if n ≤ S then sgcost rateS St.pg
        else if n ≤ S + u.length then 86
        else roundBudget U A B' k)

/-- **1 ラウンドの費用の上界**。 -/
def Cstage (D : DecompOnTapes sc blank startSym endSym mark)
    (Pre : PrepOnTapes sc blank mark forb) (U A B' k : ℕ) : ℕ :=
  CmT' D + rateP Pre + rateS + 86 + roundBudget U A B' k

/-- **`stage_round_actions`**：段の 1 ラウンドの動作数は `Cstage` 以下。 -/
theorem stage_round_actions (D : DecompOnTapes sc blank startSym endSym mark)
    (Pre : PrepOnTapes sc blank mark forb) (u : List (Fin sc)) (U A B' k S : ℕ)
    (n : ℕ) (St : StageT sc) :
    stcost D Pre u U A B' k S n St ≤ Cstage D Pre U A B' k := by
  have hm := mcost_le D n St.md
  have hp := sgcost_le (rateP Pre) St.pg
  have hs := sgcost_le (sc := sc) rateS St.pg
  unfold stcost Cstage
  simp only [rateS] at *
  split_ifs <;> omega

/-- ラウンド `n` 終了時の段の状態。 -/
def ststate (D : DecompOnTapes sc blank startSym endSym mark)
    (Pre : PrepOnTapes sc blank mark forb) (leftSym one zero : Fin sc)
    (u v Text : List (Fin sc)) (k pe re : ℕ) (cst : ScanState → ℕ) (A B' S : ℕ)
    (w : List (Fin sc)) (init : StageT sc) : ℕ → StageT sc
  | 0 => init
  | n + 1 =>
      stround D Pre leftSym one zero u v Text k pe re cst A B' S
        (w.take (n + 1)) (w.getD n blank) (n + 1)
        (ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init n)

/-! ## 5. 成分の同定 -/

section Components

variable {D : DecompOnTapes sc blank startSym endSym mark} {Pre : PrepOnTapes sc blank mark forb}
  {leftSym one zero : Fin sc}
  {u v Text : List (Fin sc)} {k pe re : ℕ} {cst : ScanState → ℕ} {A B' S : ℕ}
  {w : List (Fin sc)} {init : StageT sc}

/-- 展開補題。 -/
theorem ststate_succ (n : ℕ) :
    ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init (n + 1)
      = stround D Pre leftSym one zero u v Text k pe re cst A B' S
          (w.take (n + 1)) (w.getD n blank) (n + 1)
          (ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init n) := rfl

/-- `n ≤ S/2` のあいだ、段の状態はまったく動かない。 -/
theorem ststate_idle :
    ∀ n, n ≤ S / 2 →
      ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init n = init := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    rw [ststate_succ, ih (by omega), stround, if_pos hn]

/-- **中央成分は `MiddleTapes.mstate` そのもの**。 -/
theorem ststate_md :
    ∀ n, (ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init n).md
      = mstate blank startSym endSym mark leftSym one zero D w S init.md n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ststate_succ, mstate, stround]
    by_cases h : n + 1 ≤ S / 2
    · rw [if_pos h, if_pos h, ststate_idle (D := D) (Pre := Pre) (leftSym := leftSym)
        (one := one) (zero := zero) (u := u) (v := v) (Text := Text) (k := k) (pe := pe)
        (re := re) (cst := cst) (A := A) (B' := B') (S := S) (w := w) (init := init)
        n (by omega)]
    · rw [if_neg h, if_neg h, ih]
      split_ifs <;> rfl

/-- 照合器成分はラウンド `S` まで動かない。 -/
theorem ststate_sm_pre :
    ∀ n, n < S →
      (ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init n).sm = init.sm := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    rw [ststate_succ, stround]
    split_ifs <;> first | exact ih (by omega) | omega

/-- ラウンド `S` に照合器は、**準備フェーズが実際に作った 12 本のテープ**
（`setupGrind` 後の `pg.ts`）から `startVM` で起こされる。 -/
theorem ststate_sm_birth (hS : 8 ≤ S) (hq : 4 * (S / 4) = S) :
    (ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init S).sm
      = ⟨startVM blank startSym endSym mark
          (ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init S).pg.ts, 0⟩ := by
  obtain ⟨m, hm⟩ : ∃ m, S = m + 1 := ⟨S - 1, by omega⟩
  have hst : ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init S
      = stround D Pre leftSym one zero u v Text k pe re cst A B' S
          (w.take S) (w.getD (S - 1) blank) S
          (ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init (S - 1)) := by
    rw [hm]; exact ststate_succ m
  rw [hst, stround, if_neg (by omega), if_neg (by omega), if_pos le_rfl]
  show (if S = S then _ else _) = _
  rw [if_pos rfl]

/-- **起動フェーズ**：ラウンド `(S, S + |u|]` では毎ラウンド 1 回の `vstartRound'`
（到着 `varrive'` ＋ `Txt` の供給 ＋ 右送り、`≤ 86` 動作）を行う。したがって
ラウンド `S + i` の照合器成分は `vstartT'` の `i` 段目そのもの。 -/
theorem ststate_sm_start (hS : 8 ≤ S) (hq : 4 * (S / 4) = S) :
    ∀ i, i ≤ u.length →
      (ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init (S + i)).sm
        = ⟨vstartT' blank mark Text i (startVM blank startSym endSym mark
            (ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init S).pg.ts),
          0⟩ := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [Nat.add_zero]
    exact ststate_sm_birth (D := D) (Pre := Pre) (leftSym := leftSym) (one := one)
      (zero := zero) (u := u) (v := v) (Text := Text) (k := k) (pe := pe) (re := re)
      (cst := cst) (A := A) (B' := B') (w := w) (init := init) hS hq
  | succ i ih =>
    intro hi
    rw [show S + (i + 1) = (S + i) + 1 from by omega, ststate_succ, stround,
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    show (⟨vstartRound' blank mark (Text.getD (S + i + 1 - 1 - S) blank)
        (ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init (S + i)).sm.M,
      (ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init (S + i)).sm.rem⟩
        : SMachine sc) = _
    rw [ih (by omega), show S + i + 1 - 1 - S = i from by omega]
    rfl

/-- ラウンド `S + |u|` の照合器成分はまさに `StageMatcherTapes.initSM`。 -/
theorem ststate_sm_idle (hS : 8 ≤ S) (hq : 4 * (S / 4) = S) :
    (ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init
        (S + u.length)).sm
      = initSM' blank startSym endSym mark u Text
          (ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init S).pg.ts :=
  ststate_sm_start (D := D) (Pre := Pre) (leftSym := leftSym) (one := one) (zero := zero)
    (u := u) (v := v) (Text := Text) (k := k) (pe := pe) (re := re) (cst := cst)
    (A := A) (B' := B') (w := w) (init := init) hS hq u.length le_rfl

/-- **照合器成分は `StageMatcherTapes.stage` そのもの**：絶対ラウンド `S + |u| + i` が
照合器の反復 `i` に対応する（`Metered.metered_start` により `[0, |u|]` は停止区間）。 -/
theorem ststate_sm (hS : 8 ≤ S) (hq : 4 * (S / 4) = S) :
    ∀ n, S + u.length ≤ n →
      (ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init n).sm
      = stage blank endSym mark u v k pe re Text cst A B' u.length (n - (S + u.length))
          (initSM' blank startSym endSym mark u Text
            (ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init S).pg.ts) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    rw [Nat.sub_self]
    exact ststate_sm_idle (D := D) (Pre := Pre) (leftSym := leftSym) (one := one)
      (zero := zero) (u := u) (v := v) (Text := Text) (k := k) (pe := pe) (re := re)
      (cst := cst) (A := A) (B' := B') (w := w) (init := init) hS hq
  | succ n hn ih =>
    rw [ststate_succ, stround, if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
    show sround blank endSym mark u v k pe re Text cst A B' (n + 1 - 1 - S)
        (Text.getD (n + 1 - 1 - S) blank) _ = _
    rw [ih, show n + 1 - (S + u.length) = (n - (S + u.length)) + 1 from by omega,
      show n + 1 - 1 - S = u.length + (n - (S + u.length)) from by omega]
    rfl

end Components

/-! ## 6. 前処理・準備フェーズの完了 -/

section Grind

variable {D : DecompOnTapes sc blank startSym endSym mark} {Pre : PrepOnTapes sc blank mark forb}
  {leftSym one zero : Fin sc}
  {u v Text : List (Fin sc)} {k pe re : ℕ} {cst : ScanState → ℕ} {A B' S : ℕ}
  {w : List (Fin sc)} {init : StageT sc}

theorem sgsteps_succ' (blank : Fin sc) (R : ℕ) :
    ∀ (m : ℕ) (g : SGrind sc),
      sgsteps blank R (m + 1) g = sgstep blank R (sgsteps blank R m g) := by
  intro m
  induction m with
  | zero => intro g; rfl
  | succ m ih => intro g; rw [sgsteps, ih, ← sgsteps]

/-- 誕生ラウンド `S/2 + 1` に前処理のプログラムが載る。 -/
theorem pg_install_prep (hS : 8 ≤ S) (hq : 4 * (S / 4) = S) :
    (ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init (S / 2 + 1)).pg
      = sgstep blank (rateP Pre)
          ⟨Pre.prog (w.take (S / 2)) (S / 2) init.pg.ts, init.pg.ts⟩ := by
  rw [ststate_succ, ststate_idle (D := D) (Pre := Pre) (leftSym := leftSym) (one := one)
    (zero := zero) (u := u) (v := v) (Text := Text) (k := k) (pe := pe) (re := re)
    (cst := cst) (A := A) (B' := B') (S := S) (w := w) (init := init) (S / 2) le_rfl,
    stround, if_neg (by omega), if_pos (by omega)]
  show sgstep blank (rateP Pre) (if S / 2 + 1 = S / 2 + 1 then _ else _) = _
  rw [if_pos rfl, List.take_take, Nat.min_eq_left (by omega)]

/-- 前処理の窓の内部では `pg` はただ挽かれるだけ。 -/
theorem pg_window_prep (_hS : 8 ≤ S) (hq : 4 * (S / 4) = S) :
    ∀ j, S / 2 + 1 + j ≤ 3 * (S / 4) →
      (ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init
          (S / 2 + 1 + j)).pg
      = sgsteps blank (rateP Pre) j
          (ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init
            (S / 2 + 1)).pg := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    rw [show S / 2 + 1 + (j + 1) = (S / 2 + 1 + j) + 1 from by omega, ststate_succ,
      stround, if_neg (by omega), if_pos (by omega)]
    show sgstep blank (rateP Pre) (if S / 2 + 1 + j + 1 = S / 2 + 1 then _ else _) = _
    rw [if_neg (by omega), ih (by omega), sgsteps_succ']

/-- **前処理はラウンド `3(S/4)` までに完了する**。 -/
theorem prep_complete (hS : 8 ≤ S) (hq : 4 * (S / 4) = S) (Text' : List (Fin sc))
    (hpp : PrepPre blank mark leftSym (S / 2) w Text' init.pg.ts) (hforb : forb ∉ w) :
    (ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init (3 * (S / 4))).pg
      = ⟨[], run blank (Pre.prog (w.take (S / 2)) (S / 2) init.pg.ts) init.pg.ts⟩ := by
  have hwin := pg_window_prep (D := D) (Pre := Pre) (leftSym := leftSym) (one := one)
    (zero := zero) (u := u) (v := v) (Text := Text) (k := k) (pe := pe) (re := re)
    (cst := cst) (A := A) (B' := B') (S := S) (w := w) (init := init) hS hq
    (S / 4 - 1) (by omega)
  rw [show S / 2 + 1 + (S / 4 - 1) = 3 * (S / 4) from by omega] at hwin
  rw [hwin, pg_install_prep (D := D) (Pre := Pre) (leftSym := leftSym) (one := one)
    (zero := zero) (u := u) (v := v) (Text := Text) (k := k) (pe := pe) (re := re)
    (cst := cst) (A := A) (B' := B') (S := S) (w := w) (init := init) hS hq,
    show sgsteps blank (rateP Pre) (S / 4 - 1)
        (sgstep blank (rateP Pre) ⟨Pre.prog (w.take (S / 2)) (S / 2) init.pg.ts,
          init.pg.ts⟩)
      = sgsteps blank (rateP Pre) (S / 4 - 1 + 1)
        ⟨Pre.prog (w.take (S / 2)) (S / 2) init.pg.ts, init.pg.ts⟩ from rfl,
    show S / 4 - 1 + 1 = S / 4 from by omega]
  refine sgsteps_done blank (S / 4) _ _ ?_
  have hlen := Pre.len_le w Text' (S / 2) init.pg.ts leftSym hpp hforb
  have harith := prep_rate_ok (Cp := Pre.Cp) (Dp := Pre.Dp) (S := S) hS hq
  have hR : rateP Pre = 2 * Pre.Cp + Pre.Dp := rfl
  rw [hR]
  omega

/-- 準備フェーズのプログラムがラウンド `3(S/4) + 1` に載る。 -/
theorem pg_install_setup (hS : 8 ≤ S) (hq : 4 * (S / 4) = S) :
    (ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init
        (3 * (S / 4) + 1)).pg
      = sgstep blank rateS
          ⟨setupProgram blank startSym endSym k
              (ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init
                (3 * (S / 4))).pg.ts,
            (ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init
              (3 * (S / 4))).pg.ts⟩ := by
  rw [ststate_succ, stround, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  show setupGrind blank startSym endSym k S (3 * (S / 4) + 1) _ = _
  rw [setupGrind, if_pos rfl]

/-- 準備フェーズの窓の内部では `pg` はただ挽かれるだけ。 -/
theorem pg_window_setup (hS : 8 ≤ S) (hq : 4 * (S / 4) = S) :
    ∀ j, 3 * (S / 4) + 1 + j ≤ S →
      (ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init
          (3 * (S / 4) + 1 + j)).pg
      = sgsteps blank rateS j
          (ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init
            (3 * (S / 4) + 1)).pg := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    rw [show 3 * (S / 4) + 1 + (j + 1) = (3 * (S / 4) + 1 + j) + 1 from by omega,
      ststate_succ, stround, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    show setupGrind blank startSym endSym k S (3 * (S / 4) + 1 + j + 1) _ = _
    rw [setupGrind, if_neg (by omega), ih (by omega), sgsteps_succ']

/-- **準備フェーズはラウンド `S` までに完了する**（`k * p₁ ≤ 5 * S` のとき）。 -/
theorem setup_complete (hS : 8 ≤ S) (hq : 4 * (S / 4) = S) {p₁ : ℕ} (hkp : k * p₁ ≤ 5 * S)
    (hsetup : (setupProgram blank startSym endSym k
        (ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init
          (3 * (S / 4))).pg.ts).length ≤ 7 * (S / 2 + k * p₁ + 1)) :
    (ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init S).pg
      = ⟨[], setupRun blank startSym endSym k
          (ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init
            (3 * (S / 4))).pg.ts⟩ := by
  have hwin := pg_window_setup (D := D) (Pre := Pre) (leftSym := leftSym) (one := one)
    (zero := zero) (u := u) (v := v) (Text := Text) (k := k) (pe := pe) (re := re)
    (cst := cst) (A := A) (B' := B') (S := S) (w := w) (init := init) hS hq
    (S / 4 - 1) (by omega)
  rw [show 3 * (S / 4) + 1 + (S / 4 - 1) = S from by omega] at hwin
  rw [hwin, pg_install_setup (D := D) (Pre := Pre) (leftSym := leftSym) (one := one)
    (zero := zero) (u := u) (v := v) (Text := Text) (k := k) (pe := pe) (re := re)
    (cst := cst) (A := A) (B' := B') (S := S) (w := w) (init := init) hS hq]
  rw [show sgsteps blank rateS (S / 4 - 1)
        (sgstep blank rateS ⟨setupProgram blank startSym endSym k _, _⟩)
      = sgsteps blank rateS (S / 4 - 1 + 1) ⟨setupProgram blank startSym endSym k _, _⟩
      from rfl,
    show S / 4 - 1 + 1 = S / 4 from by omega,
    sgsteps_done blank (S / 4) _ _ (le_trans hsetup (setup_rate_ok hS hq hkp))]
  rfl


/-- **`setup_complete'`**：`hsetup` は `PrepOnTapes.post` と `PatternTapes.setup_spec` から
自動的に従う。すなわち準備フェーズの完了は前処理インタフェースだけに依存する。 -/
theorem setup_complete' (hS : 8 ≤ S) (hq : 4 * (S / 4) = S) (Textp : List (Fin sc))
    (hpp : PrepPre blank mark leftSym (S / 2) w Textp init.pg.ts) (hforb : forb ∉ w)
    (hcut : (Pre.res w (S / 2)).1 < S / 2)
    (hkp : k * (Pre.res w (S / 2)).2.1 ≤ 5 * S) :
    (ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init S).pg
      = ⟨[], setupRun blank startSym endSym k
          (ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init
            (3 * (S / 4))).pg.ts⟩ := by
  have hpc := prep_complete (D := D) (Pre := Pre) (leftSym := leftSym) (one := one)
    (zero := zero) (u := u) (v := v) (Text := Text) (k := k) (pe := pe) (re := re)
    (cst := cst) (A := A) (B' := B') (S := S) (w := w) (init := init) hS hq Textp hpp hforb
  have hpre := Pre.post w Textp (S / 2) init.pg.ts leftSym hpp hforb hcut
  have hspec := setup_spec (startSym := startSym) (endSym := endSym) (k := k) hpre
  refine setup_complete (D := D) (Pre := Pre) (leftSym := leftSym) (one := one)
    (zero := zero) (u := u) (v := v) (Text := Text) (k := k) (pe := pe) (re := re)
    (cst := cst) (A := A) (B' := B') (S := S) (w := w) (init := init)
    hS hq (p₁ := (Pre.res w (S / 2)).2.1) hkp ?_
  rw [hpc]
  exact hspec.2

end Grind

/-! ## 7. 段の出力ビットと主定理 -/

section Answer

/-- **段の出力ビット**：照合器のゴースト（走査状態と残り計量動作数、いずれもテープ上の
値）から読み出す `Metered.manswer` の形と、中央仕事の読み出しフラグの論理積。 -/
def stAnswerBit (u v Text : List (Fin sc)) (k pe re : ℕ) (cst : ScanState → ℕ)
    (A B' S : ℕ) (one : Fin sc) (n : ℕ) (Sprev Scur : StageT sc) : Bool :=
  (mreported v k pe re Text cst (n - S) (mRate A B' k) (gm Sprev.sm)
      && decide (MatchLen u Text (n - S - (u.length + v.length)) u.length))
    && decide (Tape.read Scur.md.fout = one)

theorem stAnswerBit_eq {u v Text : List (Fin sc)} {k pe re : ℕ} {cst : ScanState → ℕ}
    {A B' S : ℕ} {one : Fin sc} {n : ℕ} {Sprev Scur : StageT sc} (hn : S < n)
    (hg : gm Sprev.sm = metered u v k pe re Text cst A B' (n - S - 1)) :
    stAnswerBit u v Text k pe re cst A B' S one n Sprev Scur
      = (manswer u v k pe re Text cst A B' (n - S)
          && decide (Tape.read Scur.md.fout = one)) := by
  obtain ⟨m, hm⟩ : ∃ m, n - S = m + 1 := ⟨n - S - 1, by omega⟩
  rw [stAnswerBit, hm, manswer]
  rw [show n - S - 1 = m from by omega] at hg
  rw [hg]

/-- **主定理 `stage_tapes_spec'`**：答える区間 `[2S, 4S)` の各ラウンドで、段の出力ビットは
「パターン `(w.take (S/2)).reverse` が `w.take n` に出現する」かつ
「中央部 `(w.drop (S/2)).take (n - S)` が回文である」と同値。

残る仮定はインタフェース `PrepOnTapes` / `MiddleTapes.DecompOnTapes` と、記号の相異・
`GSCore`・費用関数の仕様だけである（起動フェーズの `hgm0` は `ststate_sm_idle` と
`StageMatcherTapes.stage_init` から導かれる）。 -/
theorem stage_tapes_spec'
    {D : DecompOnTapes sc blank startSym endSym mark} {Pre : PrepOnTapes sc blank mark endSym}
    {leftSym one zero : Fin sc}
    {w : List (Fin sc)} {S k s p₁ r A B' : ℕ} {cst : ScanState → ℕ} {init : StageT sc}
    (hmb : mark ≠ blank) (hS : 8 ≤ S) (hq : 4 * (S / 4) = S)
    (hres : Pre.res w (S / 2)
      = (s, effPeriod ((w.take (S / 2)).reverse.drop s) p₁, effReach p₁ r))
    (hkp : k * effPeriod ((w.take (S / 2)).reverse.drop s) p₁ ≤ 5 * S)
    (hpinit : PrepPre blank mark leftSym (S / 2) w (w.drop S) init.pg.ts)
    (hk : 0 < k) (hs : s < S / 2)
    (H : GSCore ((w.take (S / 2)).reverse) k s p₁ r)
    (hC : 0 < A + B')
    (hcost : ∀ st, cst st ≤ (A + B')
      * (Phi k (scanStep ((w.take (S / 2)).reverse.drop s) k
          (effPeriod ((w.take (S / 2)).reverse.drop s) p₁) (effReach p₁ r) (w.drop S) st)
        - Phi k st))
    (hadvance : ∀ st, st.q ≠ ((w.take (S / 2)).reverse.drop s).length →
      (w.drop S)[st.pos + st.q]? = ((w.take (S / 2)).reverse.drop s)[st.q]? → cst st ≤ 1)
    (hne : one ≠ zero) (hleft : leftSym ∉ w) (hend : endSym ∉ w)
    (hev : 2 * (S / 2) = S)
    (hminit : ∀ m, m ≤ S / 2 →
      MEncodes blank startSym endSym mark leftSym one zero D w S m init.md)
    {n : ℕ} (h1 : 2 * S ≤ n) (h2 : n < 4 * S) (hw : n ≤ w.length) :
    stAnswerBit ((w.take (S / 2)).reverse.take s) ((w.take (S / 2)).reverse.drop s)
        (w.drop S) k (effPeriod ((w.take (S / 2)).reverse.drop s) p₁) (effReach p₁ r)
        cst A B' S one n
        (ststate D Pre leftSym one zero
          ((w.take (S / 2)).reverse.take s) ((w.take (S / 2)).reverse.drop s) (w.drop S)
          k (effPeriod ((w.take (S / 2)).reverse.drop s) p₁) (effReach p₁ r) cst A B' S w init
          (n - 1))
        (ststate D Pre leftSym one zero
          ((w.take (S / 2)).reverse.take s) ((w.take (S / 2)).reverse.drop s) (w.drop S)
          k (effPeriod ((w.take (S / 2)).reverse.drop s) p₁) (effReach p₁ r) cst A B' S w init
          n) = true
      ↔ (occursAt (w.take (S / 2)).reverse (w.take n)
          ∧ IsPal ((w.drop (S / 2)).take (n - S))) := by
  set u := (w.take (S / 2)).reverse.take s with hu
  set v := (w.take (S / 2)).reverse.drop s with hv
  set pe := effPeriod v p₁ with hpe
  set re := effReach p₁ r with hre
  have hS2 : 2 ≤ S := by omega
  have hxlen : ((w.take (S / 2)).reverse).length = S / 2 := by
    rw [List.length_reverse, List.length_take_of_le (by omega)]
  have hulen : u.length = s := by
    rw [hu, List.length_take, hxlen]; omega
  have hvpos : 0 < v.length := by rw [hv, List.length_drop, hxlen]; omega
  have hTlen : u.length ≤ (w.drop S).length := by
    rw [hulen, List.length_drop]; omega
  -- 起動フェーズの帰結：ラウンド `S + |u|` の照合器は `initSM`
  have hbirth := ststate_sm_idle (D := D) (Pre := Pre) (leftSym := leftSym) (one := one)
    (zero := zero) (u := u) (v := v) (Text := w.drop S) (k := k) (pe := pe) (re := re)
    (cst := cst) (A := A) (B' := B') (S := S) (w := w) (init := init) hS hq
  -- 準備フェーズの出力テープ：`setup_complete'` ＋ `PatternTapes.setup_spec`
  have hcut : (Pre.res w (S / 2)).1 < S / 2 := by rw [hres]; exact hs
  have hpc := prep_complete (D := D) (Pre := Pre) (leftSym := leftSym) (one := one)
    (zero := zero) (u := u) (v := v) (Text := w.drop S) (k := k) (pe := pe) (re := re)
    (cst := cst) (A := A) (B' := B') (S := S) (w := w) (init := init) hS hq
    (w.drop S) hpinit hend
  have hpre := Pre.post w (w.drop S) (S / 2) init.pg.ts leftSym hpinit hend hcut
  have hsc := setup_complete' (D := D) (Pre := Pre) (leftSym := leftSym) (one := one)
    (zero := zero) (u := u) (v := v) (Text := w.drop S) (k := k) (pe := pe) (re := re)
    (cst := cst) (A := A) (B' := B') (S := S) (w := w) (init := init) hS hq (w.drop S)
    hpinit hend hcut (by rw [hres]; exact hkp)
  have hE : GSVTapes.VEncodes' blank startSym endSym mark u v
      (TextFeed.padW blank (w.drop S) 0) k pe re
      (toGS (ststate D Pre leftSym one zero u v (w.drop S) k pe re cst A B' S w init S).pg.ts,
        toVExt (ststate D Pre leftSym one zero u v (w.drop S) k pe re cst A B' S w init S).pg.ts)
      ((⟨0, 0⟩ : ScanState), 0) := by
    have h := (setup_spec (startSym := startSym) (endSym := endSym) (k := k) hpre).1
    rw [hres] at h
    rw [hsc, hpc]
    exact h
  have hgm0 : gm (ststate D Pre leftSym one zero u v (w.drop S) k pe re cst A B' S w init
      (S + u.length)).sm
      = metered u v k pe re (w.drop S) cst A B' u.length := by
    rw [hbirth]
    exact (stage_init_of (cst := cst) (A := A) (B' := B') hmb hvpos hTlen hE).2.1
  have hsm := ststate_sm (D := D) (Pre := Pre) (leftSym := leftSym) (one := one)
    (zero := zero) (u := u) (v := v) (Text := w.drop S) (k := k) (pe := pe) (re := re)
    (cst := cst) (A := A) (B' := B') (S := S) (w := w) (init := init) hS hq
    (n - 1) (by rw [hulen]; omega)
  have hghost : gm (ststate D Pre leftSym one zero
      u v (w.drop S) k pe re cst A B' S w init (n - 1)).sm
      = metered u v k pe re (w.drop S) cst A B' (n - S - 1) := by
    rw [hsm, ← hbirth, stage_round_spec (blank := blank) (endSym := endSym)
      (mark := mark) hvpos hgm0,
      show u.length + (n - 1 - (S + u.length)) = n - S - 1 from by rw [hulen]; omega]
  rw [stAnswerBit_eq (by omega) hghost, Bool.and_eq_true, decide_eq_true_iff]
  have hmatch := stage_answer_stageMatchH (w := w) (S := S) (k := k) (s := s)
    (p₁ := p₁) (r := r) (A := A) (B' := B') (cst := cst) hk hs H hC hcost hadvance
    (n := n) h1 hw
  have hmid := middle_flag_read (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (leftSym := leftSym) (one := one) (zero := zero) D
    hne hleft hend hev hS2 hminit n h1 h2 hw
  have hmdst := ststate_md (D := D) (Pre := Pre) (leftSym := leftSym) (one := one)
    (zero := zero) (u := u) (v := v) (Text := w.drop S) (k := k) (pe := pe) (re := re)
    (cst := cst) (A := A) (B' := B') (S := S) (w := w) (init := init) n
  rw [hmdst, hmid]
  exact and_congr hmatch Iff.rfl

end Answer

end StageTapes
end PalPeg

