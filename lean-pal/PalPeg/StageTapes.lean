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
| `3(S/4) < n ≤ S` | 準備 `PatternTapes.setupProgram` を毎ラウンド `rateS = 36` 動作ずつ挽く ＋ `mround` |
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

/-- **前処理のインタフェース**（`GSPreprocessTapes` の抽象化）。
入力コピー `sIn` に載っているパターン `w.take L` から、切断点・周期・到達域の
単進カウンタ（`sCs` / `sC1` / `sRp`）を作り、`PatternTapes.SetupPre` を満たす
テープ配置を作る動作列。長さは `Cp * L + Dp` 以下。 -/
structure PrepOnTapes (sc : ℕ) (blank mark : Fin sc) where
  /-- 動作列（読んだ入力とパターン長とテープから決まる）。 -/
  prog : List (Fin sc) → ℕ → Tapes sc → List (SAct sc)
  /-- 分解 `(s, p₁, r)`。 -/
  res : List (Fin sc) → ℕ → ℕ × ℕ × ℕ
  /-- 費用の傾き。 -/
  Cp : ℕ
  /-- 費用の切片。 -/
  Dp : ℕ
  len_le : ∀ (x : List (Fin sc)) (L : ℕ) (ts : Tapes sc), (prog x L ts).length ≤ Cp * L + Dp
  post : ∀ (w Text : List (Fin sc)) (L : ℕ) (ts : Tapes sc), 0 < L → L ≤ w.length →
    (res w L).1 < L →
    SetupPre blank mark (res w L).1 L (res w L).2.1 (res w L).2.2 w Text
      (run blank (prog (w.take L) L ts) ts)

/-- 前処理を挽く速度。 -/
def rateP {blank mark : Fin sc} (Pre : PrepOnTapes sc blank mark) : ℕ :=
  2 * Pre.Cp + Pre.Dp

/-- 準備フェーズ（`setupProgram`）を挽く速度。 -/
def rateS : ℕ := 36

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
`7 * (S/2 + k*p₁ + 1)` は `(S/4) * 36` 以下（`k * p₁ ≤ S/2` のとき）。 -/
theorem setup_rate_ok {S k p₁ : ℕ} (hS : 8 ≤ S) (hq : 4 * (S / 4) = S)
    (hkp : k * p₁ ≤ S / 2) :
    7 * (S / 2 + k * p₁ + 1) ≤ (S / 4) * rateS := by
  have hq1 : 1 ≤ S / 4 := by omega
  have hhalf : S / 2 = 2 * (S / 4) := by omega
  have hexp : (S / 4) * rateS = 36 * (S / 4) := by rw [rateS]; ring
  omega

/-! ## 4. 段の状態と 1 ラウンド -/

/-- **一つの段のテープ側の記録**。 -/
structure StageT (sc : ℕ) where
  /-- 照合器（走査 8 本＋検証器 2 本＋待ち行列 2 本、計量スケジューラつき）。 -/
  sm : SMachine sc
  /-- 中央フラグの仕事（6 本＋読み出しフラグ＋入力コピー）。 -/
  md : MiddleTapes.MState sc
  /-- 前処理・準備フェーズの挽き（12 本）。 -/
  pg : SGrind sc

variable {blank startSym endSym mark : Fin sc}

/-- **段の 1 ラウンド**。`t` は到着済みの入力、`a` はこのラウンドに到着した記号、
`n` は絶対ラウンド番号。 -/
def stround (D : DecompOnTapes sc blank startSym endSym mark)
    (Pre : PrepOnTapes sc blank mark) (leftSym one zero : Fin sc)
    (u v Text : List (Fin sc)) (k pe re : ℕ) (cst : ScanState → ℕ) (A B' S : ℕ)
    (t : List (Fin sc)) (a : Fin sc) (n : ℕ) (St : StageT sc) : StageT sc :=
  if n ≤ S / 2 then St
  else if n ≤ 3 * (S / 4) then
    ⟨St.sm, mround blank startSym endSym mark leftSym one zero D t a n St.md,
      sgstep blank (rateP Pre)
        (if n = S / 2 + 1 then ⟨Pre.prog (t.take (S / 2)) (S / 2) St.pg.ts, St.pg.ts⟩
          else St.pg)⟩
  else if n ≤ S then
    ⟨St.sm, mround blank startSym endSym mark leftSym one zero D t a n St.md,
      sgstep blank rateS
        (if n = 3 * (S / 4) + 1 then
            ⟨setupProgram blank startSym endSym k St.pg.ts, St.pg.ts⟩
          else St.pg)⟩
  else if n ≤ S + u.length then
    ⟨St.sm, mround blank startSym endSym mark leftSym one zero D t a n St.md, St.pg⟩
  else
    ⟨sround blank endSym mark u v k pe re Text cst A B' (n - 1 - S)
        (Text.getD (n - 1 - S) blank) St.sm,
      mround blank startSym endSym mark leftSym one zero D t a n St.md, St.pg⟩

/-- 1 ラウンドの費用。 -/
def stcost (D : DecompOnTapes sc blank startSym endSym mark)
    (Pre : PrepOnTapes sc blank mark) (u : List (Fin sc)) (U A B' k S : ℕ)
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
    (Pre : PrepOnTapes sc blank mark) (U A B' k : ℕ) : ℕ :=
  CmT' D + rateP Pre + rateS + 86 + roundBudget U A B' k

/-- **`stage_round_actions`**：段の 1 ラウンドの動作数は `Cstage` 以下。 -/
theorem stage_round_actions (D : DecompOnTapes sc blank startSym endSym mark)
    (Pre : PrepOnTapes sc blank mark) (u : List (Fin sc)) (U A B' k S : ℕ)
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
    (Pre : PrepOnTapes sc blank mark) (leftSym one zero : Fin sc)
    (u v Text : List (Fin sc)) (k pe re : ℕ) (cst : ScanState → ℕ) (A B' S : ℕ)
    (w : List (Fin sc)) (init : StageT sc) : ℕ → StageT sc
  | 0 => init
  | n + 1 =>
      stround D Pre leftSym one zero u v Text k pe re cst A B' S
        (w.take (n + 1)) (w.getD n blank) (n + 1)
        (ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init n)

/-! ## 5. 成分の同定 -/

section Components

variable {D : DecompOnTapes sc blank startSym endSym mark} {Pre : PrepOnTapes sc blank mark}
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

/-- 照合器成分は `S + |u|` まで動かない。 -/
theorem ststate_sm_idle :
    ∀ n, n ≤ S + u.length →
      (ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init n).sm = init.sm := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    rw [ststate_succ, stround]
    split_ifs <;> exact ih (by omega)

/-- **照合器成分は `StageMatcherTapes.stage` そのもの**：絶対ラウンド `S + |u| + i` が
照合器の反復 `i` に対応する（`Metered.metered_start` により `[0, |u|]` は停止区間）。 -/
theorem ststate_sm (hSu : S / 2 < S + u.length) (hS4 : 3 * (S / 4) ≤ S) :
    ∀ n, S + u.length ≤ n →
      (ststate D Pre leftSym one zero u v Text k pe re cst A B' S w init n).sm
      = stage blank endSym mark u v k pe re Text cst A B' u.length (n - (S + u.length))
          init.sm := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    rw [Nat.sub_self]
    exact ststate_sm_idle (D := D) (Pre := Pre) (leftSym := leftSym) (one := one)
      (zero := zero) (u := u) (v := v) (Text := Text) (k := k) (pe := pe) (re := re)
      (cst := cst) (A := A) (B' := B') (S := S) (w := w) (init := init)
      (S + u.length) le_rfl
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

variable {D : DecompOnTapes sc blank startSym endSym mark} {Pre : PrepOnTapes sc blank mark}
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
theorem prep_complete (hS : 8 ≤ S) (hq : 4 * (S / 4) = S) :
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
  have hlen := Pre.len_le (w.take (S / 2)) (S / 2) init.pg.ts
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
  show sgstep blank rateS (if 3 * (S / 4) + 1 = 3 * (S / 4) + 1 then _ else _) = _
  rw [if_pos rfl]

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
    show sgstep blank rateS (if 3 * (S / 4) + 1 + j + 1 = 3 * (S / 4) + 1 then _ else _) = _
    rw [if_neg (by omega), ih (by omega), sgsteps_succ']

/-- **準備フェーズはラウンド `S` までに完了する**（`k * p₁ ≤ S / 2` のとき）。 -/
theorem setup_complete (hS : 8 ≤ S) (hq : 4 * (S / 4) = S) {p₁ : ℕ} (hkp : k * p₁ ≤ S / 2)
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

/-- **主定理 `stage_tapes_spec`**：答える区間 `[2S, 4S)` の各ラウンドで、段の出力ビットは
「パターン `(w.take (S/2)).reverse` が `w.take n` に出現する」かつ
「中央部 `(w.drop (S/2)).take (n - S)` が回文である」と同値。 -/
theorem stage_tapes_spec
    {D : DecompOnTapes sc blank startSym endSym mark} {Pre : PrepOnTapes sc blank mark}
    {leftSym one zero : Fin sc}
    {w : List (Fin sc)} {S k s p₁ r A B' : ℕ} {cst : ScanState → ℕ} {init : StageT sc}
    (hk : 0 < k) (hs : s < S / 2)
    (H : GSCore ((w.take (S / 2)).reverse) k s p₁ r)
    (hC : 0 < A + B')
    (hcost : ∀ st, cst st ≤ (A + B')
      * (Phi k (scanStep ((w.take (S / 2)).reverse.drop s) k
          (effPeriod ((w.take (S / 2)).reverse.drop s) p₁) (effReach p₁ r) (w.drop S) st)
        - Phi k st))
    (hadvance : ∀ st, st.q ≠ ((w.take (S / 2)).reverse.drop s).length →
      (w.drop S)[st.pos + st.q]? = ((w.take (S / 2)).reverse.drop s)[st.q]? → cst st ≤ 1)
    (hgm0 : gm (ststate D Pre leftSym one zero
        ((w.take (S / 2)).reverse.take s) ((w.take (S / 2)).reverse.drop s) (w.drop S)
        k (effPeriod ((w.take (S / 2)).reverse.drop s) p₁) (effReach p₁ r) cst A B' S w init
        (S + ((w.take (S / 2)).reverse.take s).length)).sm
      = metered ((w.take (S / 2)).reverse.take s) ((w.take (S / 2)).reverse.drop s) k
          (effPeriod ((w.take (S / 2)).reverse.drop s) p₁) (effReach p₁ r) (w.drop S)
          cst A B' ((w.take (S / 2)).reverse.take s).length)
    (hne : one ≠ zero) (hleft : leftSym ∉ w) (hend : endSym ∉ w)
    (hDec : MiddleBorder.DecOK (Fin sc)) (hev : 2 * (S / 2) = S) (hS2 : 2 ≤ S)
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
  have hxlen : ((w.take (S / 2)).reverse).length = S / 2 := by
    rw [List.length_reverse, List.length_take_of_le (by omega)]
  have hulen : u.length = s := by
    rw [hu, List.length_take, hxlen]; omega
  have hvpos : 0 < v.length := by rw [hv, List.length_drop, hxlen]; omega
  have hsm := ststate_sm (D := D) (Pre := Pre) (leftSym := leftSym) (one := one)
    (zero := zero) (u := u) (v := v) (Text := w.drop S) (k := k) (pe := pe) (re := re)
    (cst := cst) (A := A) (B' := B') (S := S) (w := w) (init := init)
    (by rw [hulen]; omega) (by omega) (n - 1) (by rw [hulen]; omega)
  rw [ststate_sm_idle (D := D) (Pre := Pre) (leftSym := leftSym) (one := one)
    (zero := zero) (u := u) (v := v) (Text := w.drop S) (k := k) (pe := pe) (re := re)
    (cst := cst) (A := A) (B' := B') (S := S) (w := w) (init := init)
    (S + u.length) le_rfl] at hgm0
  have hghost : gm (ststate D Pre leftSym one zero
      u v (w.drop S) k pe re cst A B' S w init (n - 1)).sm
      = metered u v k pe re (w.drop S) cst A B' (n - S - 1) := by
    rw [hsm, stage_round_spec (blank := blank) (endSym := endSym)
      (mark := mark) hvpos hgm0,
      show u.length + (n - 1 - (S + u.length)) = n - S - 1 from by rw [hulen]; omega]
  rw [stAnswerBit_eq (by omega) hghost, Bool.and_eq_true, decide_eq_true_iff]
  have hmatch := stage_answer_stageMatchH (w := w) (S := S) (k := k) (s := s)
    (p₁ := p₁) (r := r) (A := A) (B' := B') (cst := cst) hk hs H hC hcost hadvance
    (n := n) h1 hw
  have hmid := middle_flag_read (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (leftSym := leftSym) (one := one) (zero := zero) D
    hne hleft hend hDec hev hS2 hminit n h1 h2 hw
  have hmdst := ststate_md (D := D) (Pre := Pre) (leftSym := leftSym) (one := one)
    (zero := zero) (u := u) (v := v) (Text := w.drop S) (k := k) (pe := pe) (re := re)
    (cst := cst) (A := A) (B' := B') (S := S) (w := w) (init := init) n
  rw [hmdst, hmid, (MiddleBorder.borderMiddle_spec hDec).correct w S n hS2 hev h1 h2 hw]
  exact and_congr hmatch Iff.rfl

end Answer

end StageTapes
end PalPeg

