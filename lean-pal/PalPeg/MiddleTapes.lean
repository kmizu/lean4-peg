import PalPeg.BorderJobTapes
import PalPeg.InputCopy
import PalPeg.MiddleBorder

-- `lake build` は lakefile の `autoImplicit = false` を使う。本ファイルは自動束縛変数に依存する。
set_option autoImplicit true

/-!
# 中央フラグのテープ実現 (`MiddleTapes`)

`PalPeg.MiddleBorder.borderMiddle` は「凍結窓 `Wnd w S j` を境界ジョブで挽き、
`gw S` ラウンドごとに次のバッチを解放し、直前に完了したバッチのフラグ列を
`out` として読む」ラウンド実装であった。本ファイルはこの実装を
`PegSeparation.RealTimeTM` のテープ模型の上に**具体的なヘッド動作列**として実現する。

## テープ配置

段幅 `S`（偶数, `8 ≤ S`）の常駐段は次のテープを持つ。

* `X`, `X2` — 入力コピー（`InputCopy.FrontierView`）。ラウンド `S/2 + 1` 以降に
  到着した記号を 1 ラウンド 1 個ずつ書き足すので、ラウンド `n` の終わりには
  語 `w.drop (S/2)` の接頭辞を保持している。バッチ解放時にヘッドを窓の右端へ
  置き直す（費用 `≤ |窓|`、そのバッチに課金）。
* `P`, `U`, `Cnt` — 境界ジョブの段テープ。段ごとに `DecompOnTapes` インタフェース
  （＋コピー歩き）で載せ替える。
* `F0`, `F1` — フラグテープ **2 本（ダブルバッファ）**。進行中のバッチは一方に
  `jobFlags` を書き込み（ヘッドは段の中で左へ掃く）、完了したバッチの側は
  1 ラウンド 1 セルずつ右へ歩いて読み出される。`borderMiddle` の
  `out.getD (n - S)` がちょうどこの読み出しに対応する。

## 本ファイルの構成

* §0 ヘッドの置き直し（左端まで掃いてから右へ `m` セル）。
* §1 「1 ラウンドに `rate` 動作だけ挽く」機構（`Grind`）。
* §2 分解器のインタフェース `DecompOnTapes`（`GSPreprocessTapes` の抽象化）。
* §3 1 バッチ分の平坦な動作列 `jobActs` とその長さの上界。
* §4 ラウンド機械（ダブルバッファ）とフラグの読み出し。
-/

namespace PalPeg
namespace MiddleTapes

open PegSeparation.RealTimeTM
open PalPeg.BorderTapes
open PalPeg.MiddleBorder

variable {sc : ℕ}

/-! ## §0 ヘッドの反復移動と置き直し -/

/-- 現在の記号を書き戻しながら `m` の向きへ `n` セル。 -/
def iterM (blank : Fin sc) (m : Move) : TapeConfiguration sc → ℕ → TapeConfiguration sc
  | tp, 0 => tp
  | tp, n + 1 => iterM blank m (Tape.step blank tp tp.focus m) n

theorem iterM_left (blank : Fin sc) :
    ∀ (n : ℕ) (tp : TapeConfiguration sc), iterM blank .left tp n = GSTapes.leftN blank tp n := by
  intro n
  induction n with
  | zero => intro tp; rfl
  | succ n ih => intro tp; simp only [iterM, GSTapes.leftN, ih]

theorem iterM_right (blank : Fin sc) :
    ∀ (n : ℕ) (tp : TapeConfiguration sc), iterM blank .right tp n = rightN blank tp n := by
  intro n
  induction n with
  | zero => intro tp; rfl
  | succ n ih => intro tp; simp only [iterM, rightN, ih]

/-- **左端への掃き出し**：位置 `i ≤ n` から左へ `n` 歩けば、左端規則により位置 `0`。 -/
theorem seq_leftN_clamp {blank : Fin sc} {w : List (Fin sc)} :
    ∀ (n : ℕ) (tp : TapeConfiguration sc) (i : ℕ), Tape.SeqView blank tp w i → i ≤ n →
      Tape.SeqView blank (GSTapes.leftN blank tp n) w 0 := by
  intro n
  induction n with
  | zero => intro tp i h hi; rw [show i = 0 by omega] at h; exact h
  | succ n ih =>
    intro tp i h hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact ih _ 0 (Tape.seq_move_left_edge h) (Nat.zero_le _)
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      exact ih _ j (Tape.seq_move_left h) (by omega)

/-- **置き直し**：位置 `i ≤ n` から「左へ `n`、右へ `m`」で位置 `m`。 -/
theorem seq_home {blank : Fin sc} {w : List (Fin sc)} {tp : TapeConfiguration sc}
    {i n m : ℕ} (h : Tape.SeqView blank tp w i) (hi : i ≤ n) (hm : m < w.length) :
    Tape.SeqView blank (rightN blank (GSTapes.leftN blank tp n) m) w m := by
  have h0 := seq_leftN_clamp n tp i h hi
  have := seq_rightN (blank := blank) (w := w) m _ 0 h0 (by omega)
  simpa using this

/-! ### 継ぎ目の動作列 -/

/-- `X` を `m` の向きへ `n` 歩。 -/
def mvX (m : Move) (n : ℕ) : List (Act sc) := List.replicate n (Act.X m)

/-- `X2` を `m` の向きへ `n` 歩。 -/
def mvX2 (m : Move) (n : ℕ) : List (Act sc) := List.replicate n (Act.X2 m)

/-- `F` を `m` の向きへ `n` 歩。 -/
def mvF (m : Move) (n : ℕ) : List (Act sc) := List.replicate n (Act.F m)

@[simp] theorem mvX_length (m : Move) (n : ℕ) : (mvX (sc := sc) m n).length = n := by
  simp [mvX]

@[simp] theorem mvX2_length (m : Move) (n : ℕ) : (mvX2 (sc := sc) m n).length = n := by
  simp [mvX2]

@[simp] theorem mvF_length (m : Move) (n : ℕ) : (mvF (sc := sc) m n).length = n := by
  simp [mvF]

section MoveEffect

variable {blank : Fin sc}

theorem mvX_eff (m : Move) : ∀ (n : ℕ) (ts : OvTapes sc),
    applyActs blank (mvX m n) ts = { ts with X := iterM blank m ts.X n } := by
  intro n
  induction n with
  | zero => intro ts; cases ts; rfl
  | succ n ih =>
    intro ts
    simp only [mvX, List.replicate_succ, applyActs_cons, applyAct, iterM]
    exact ih _

theorem mvX2_eff (m : Move) : ∀ (n : ℕ) (ts : OvTapes sc),
    applyActs blank (mvX2 m n) ts = { ts with X2 := iterM blank m ts.X2 n } := by
  intro n
  induction n with
  | zero => intro ts; cases ts; rfl
  | succ n ih =>
    intro ts
    simp only [mvX2, List.replicate_succ, applyActs_cons, applyAct, iterM]
    exact ih _

theorem mvF_eff (m : Move) : ∀ (n : ℕ) (ts : OvTapes sc),
    applyActs blank (mvF m n) ts = { ts with F := iterM blank m ts.F n } := by
  intro n
  induction n with
  | zero => intro ts; cases ts; rfl
  | succ n ih =>
    intro ts
    simp only [mvF, List.replicate_succ, applyActs_cons, applyAct, iterM]
    exact ih _

end MoveEffect

/-- 段の継ぎ目：`X`／`X2`／`F` のヘッドを（左端まで `n` セル掃いてから）
`X` は添字 `a`、`X2`／`F` は添字 `b` へ置き直す。 -/
def homeActs (sc n a b : ℕ) : List (Act sc) :=
  mvX .left n ++ mvX2 .left n ++ mvF .left n ++
    mvX .right a ++ mvX2 .right b ++ mvF .right b

@[simp] theorem homeActs_length (sc n a b : ℕ) :
    (homeActs sc n a b).length = 3 * n + a + 2 * b := by
  simp only [homeActs, List.length_append, mvX_length, mvX2_length, mvF_length]
  omega

/-- `F` のヘッドだけを置き直す（読み出し用）。 -/
def homeF (sc n m : ℕ) : List (Act sc) := mvF .left n ++ mvF .right m

@[simp] theorem homeF_length (sc n m : ℕ) : (homeF sc n m).length = n + m := by
  simp only [homeF, List.length_append, mvF_length]

theorem homeActs_eff {blank : Fin sc} (n a b : ℕ) (ts : OvTapes sc) :
    applyActs blank (homeActs sc n a b) ts =
      { ts with
        X := rightN blank (GSTapes.leftN blank ts.X n) a
        X2 := rightN blank (GSTapes.leftN blank ts.X2 n) b
        F := rightN blank (GSTapes.leftN blank ts.F n) b } := by
  simp only [homeActs, applyActs_append, mvX_eff, mvX2_eff, mvF_eff, iterM_left, iterM_right]

theorem homeF_eff {blank : Fin sc} (n m : ℕ) (ts : OvTapes sc) :
    applyActs blank (homeF sc n m) ts =
      { ts with F := rightN blank (GSTapes.leftN blank ts.F n) m } := by
  simp only [homeF, applyActs_append, mvF_eff, iterM_left, iterM_right]

/-! ### 継ぎ目の動作列も作業テープに触れない -/

theorem noScratch_mvX (m : Move) (n : ℕ) : NoScratchAll (mvX (sc := sc) m n) :=
  noScratchAll_replicate (a := Act.X m) trivial n

theorem noScratch_mvX2 (m : Move) (n : ℕ) : NoScratchAll (mvX2 (sc := sc) m n) :=
  noScratchAll_replicate (a := Act.X2 m) trivial n

theorem noScratch_mvF (m : Move) (n : ℕ) : NoScratchAll (mvF (sc := sc) m n) :=
  noScratchAll_replicate (a := Act.F m) trivial n

theorem noScratch_homeActs (sc n a b : ℕ) : NoScratchAll (homeActs sc n a b) := by
  simp only [homeActs]
  exact noScratchAll_append (noScratchAll_append (noScratchAll_append
    (noScratchAll_append (noScratchAll_append (noScratch_mvX _ _) (noScratch_mvX2 _ _))
      (noScratch_mvF _ _)) (noScratch_mvX _ _)) (noScratch_mvX2 _ _)) (noScratch_mvF _ _)

theorem noScratch_homeF (sc n m : ℕ) : NoScratchAll (homeF sc n m) :=
  noScratchAll_append (noScratch_mvF _ _) (noScratch_mvF _ _)

/-! ## §1 「1 ラウンドに `rate` 動作だけ挽く」機構 -/

/-- 挽き途中のジョブ：残りの動作列と現在のテープ。 -/
structure Grind (sc : ℕ) where
  /-- まだ実行していない動作。 -/
  rem : List (Act sc)
  /-- 6 本のテープ。 -/
  ts : OvTapes sc

/-- 1 ラウンド：先頭 `r` 個の動作を実行する。 -/
def gstep (blank : Fin sc) (r : ℕ) (g : Grind sc) : Grind sc :=
  ⟨g.rem.drop r, applyActs blank (g.rem.take r) g.ts⟩

/-- 1 ラウンドの実費用（動作数）。 -/
def gcost (r : ℕ) (g : Grind sc) : ℕ := min r g.rem.length

theorem gcost_le (r : ℕ) (g : Grind sc) : gcost r g ≤ r := Nat.min_le_left _ _

/-- `n` ラウンド挽く。 -/
def gsteps (blank : Fin sc) (r : ℕ) : ℕ → Grind sc → Grind sc
  | 0, g => g
  | n + 1, g => gsteps blank r n (gstep blank r g)

theorem gstep_apply (blank : Fin sc) (r : ℕ) (g : Grind sc) :
    applyActs blank (gstep blank r g).rem (gstep blank r g).ts
      = applyActs blank g.rem g.ts := by
  show applyActs blank (g.rem.drop r) (applyActs blank (g.rem.take r) g.ts)
      = applyActs blank g.rem g.ts
  rw [← applyActs_append, List.take_append_drop]

/-- 挽き終えていない途中でも、「残り＋現状」を合成すればジョブ全体の結果に等しい。 -/
theorem gsteps_apply (blank : Fin sc) (r : ℕ) :
    ∀ (n : ℕ) (g : Grind sc),
      applyActs blank (gsteps blank r n g).rem (gsteps blank r n g).ts
        = applyActs blank g.rem g.ts := by
  intro n
  induction n with
  | zero => intro g; rfl
  | succ n ih => intro g; rw [gsteps, ih, gstep_apply]

/-- **完了**：`n * r` が動作数以上なら、`n` ラウンドでジョブは挽き終わっている。 -/
theorem gsteps_done (blank : Fin sc) {r : ℕ} :
    ∀ (n : ℕ) (l : List (Act sc)) (ts : OvTapes sc), l.length ≤ n * r →
      gsteps blank r n ⟨l, ts⟩ = ⟨[], applyActs blank l ts⟩ := by
  intro n
  induction n with
  | zero =>
    intro l ts h
    simp only [Nat.zero_mul, Nat.le_zero] at h
    rw [List.length_eq_zero_iff] at h
    subst h
    rfl
  | succ n ih =>
    intro l ts h
    rw [gsteps]
    have hlen : (l.drop r).length ≤ n * r := by
      simp only [List.length_drop]
      have : (n + 1) * r = n * r + r := by ring
      omega
    have := ih (l.drop r) (applyActs blank (l.take r) ts) hlen
    show gsteps blank r n ⟨l.drop r, applyActs blank (l.take r) ts⟩ = _
    rw [this, ← applyActs_append, List.take_append_drop]

/-- 残りが空なら以後は動かない。 -/
theorem gsteps_nil (blank : Fin sc) (r : ℕ) :
    ∀ (n : ℕ) (ts : OvTapes sc), gsteps blank r n ⟨[], ts⟩ = ⟨[], ts⟩ := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih =>
    intro ts
    rw [gsteps, show gstep blank r ⟨[], ts⟩ = ⟨[], ts⟩ by simp [gstep]]
    exact ih _

/-! ## §2 段の走査を平坦な動作列にする -/

/-- `ovRunTapes` が実際に流す動作を、そのまま 1 本のリストへ並べたもの。 -/
def ovRunActs (blank leftSym endSym mark one : Fin sc) (u v T : List (Fin sc))
    (k p₁ r minimum c : ℕ) : ℕ → ScanState → OvTapes sc → List (Act sc)
  | 0, _, _ => []
  | fuel + 1, st, ts =>
      if T.length < st.pos + minimum then []
      else
        ovProgram blank leftSym endSym mark one k c
            (decide (k * p₁ ≤ st.q ∧ st.q ≤ r))
            (decide (MatchLen u T st.pos u.length)) ts ++
          ovRunActs blank leftSym endSym mark one u v T k p₁ r minimum c fuel
            (ovStep u v T k p₁ r st)
            (applyActs blank (ovProgram blank leftSym endSym mark one k c
              (decide (k * p₁ ≤ st.q ∧ st.q ≤ r))
              (decide (MatchLen u T st.pos u.length)) ts) ts)

/-- 段の走査の動作列は `ScratchBlank` を保つ（フロンティア枝の `uCheck` が
一時的に `S2` に触れるので、もはや `NoScratchAll` ではない：`ovProgram_scratchBlank`
を参照）。 -/
theorem ovRunActs_scratchBlank {blank leftSym endSym mark one : Fin sc} {u v T : List (Fin sc)}
    {k p₁ r minimum c : ℕ} :
    ∀ (fuel : ℕ) (st : ScanState) (ts : OvTapes sc), ScratchBlank blank ts →
      ScratchBlank blank (applyActs blank
        (ovRunActs blank leftSym endSym mark one u v T k p₁ r minimum c fuel st ts) ts) := by
  intro fuel
  induction fuel with
  | zero => intro st ts hSB; simpa [ovRunActs] using hSB
  | succ fuel ih =>
    intro st ts hSB
    simp only [ovRunActs]
    split_ifs with h
    · simpa using hSB
    · rw [applyActs_append]
      exact ih _ _ (ovProgram_scratchBlank _ _ _ _ _ _ _ _ _ _ hSB)

/-- 平坦化はテープへの作用を変えない。 -/
theorem ovRunActs_apply {blank leftSym endSym mark one : Fin sc} {u v T : List (Fin sc)}
    {k p₁ r minimum c : ℕ} :
    ∀ (fuel : ℕ) (st : ScanState) (ts : OvTapes sc),
      applyActs blank (ovRunActs blank leftSym endSym mark one u v T k p₁ r minimum c
          fuel st ts) ts
        = ovRunTapes blank leftSym endSym mark one u v T k p₁ r minimum c fuel st ts := by
  intro fuel
  induction fuel with
  | zero => intro st ts; rfl
  | succ fuel ih =>
    intro st ts
    simp only [ovRunActs, ovRunTapes]
    by_cases hstop : T.length < st.pos + minimum
    · rw [if_pos hstop, if_pos hstop]; rfl
    · rw [if_neg hstop, if_neg hstop, applyActs_append, ih]

/-- 平坦化した動作列の長さは `ovRunCost`。 -/
theorem ovRunActs_length {blank leftSym startSym endSym mark one : Fin sc}
    {u v xw T : List (Fin sc)} {L p₁ k r minimum c : ℕ}
    (hK : KSimple v k p₁ r) (hk : 0 < k) (hL : L ≤ xw.length)
    (hleft : leftSym ∉ xw) (hend : endSym ∉ v)
    (hT : T = (xw.take L).reverse) (hc : c = u.length)
    (hlen : u.length + v.length = T.length)
    (hmin : max 1 (2 * u.length) ≤ minimum) :
    ∀ (fuel : ℕ) (st : ScanState) (ts : OvTapes sc) (fw : List (Fin sc)),
      OvInv u v T st →
      OvEncodes blank leftSym startSym endSym mark u v xw fw L p₁ ts st →
      (ovRunActs blank leftSym endSym mark one u v T k p₁ r minimum c fuel st ts).length
        = ovRunCost u v T k p₁ r minimum fuel st := by
  have hTlen : T.length = L := by rw [hT]; exact revTake_length hL
  intro fuel
  induction fuel with
  | zero => intro st ts fw _ _; rfl
  | succ fuel ih =>
    intro st ts fw hinv hE
    simp only [ovRunActs, ovRunCost]
    by_cases hstop : T.length < st.pos + minimum
    · rw [if_pos hstop, if_pos hstop]; rfl
    · rw [if_neg hstop, if_neg hstop]
      have hrange : st.pos + minimum ≤ T.length := by omega
      have hstep := ovStep_inv hK hk hlen hmin hrange hinv
      have hE' := ovEncodes_step (one := one) (c := c) (r := r) (L := L) hk hL hleft hend hT hc rfl rfl hE
        (by have := hinv.front; omega) (by have := hstep.front; omega)
      rw [List.length_append,
        ovProgram_length (one := one) (T := T) (fw := fw) (r := r) (L := L)
          hk hL hleft hend hT hc rfl rfl hE (by have := hinv.front; omega),
        ih _ _ _ hstep hE']

/-! ## §3 分解器のインタフェース -/

/-- **分解器のインタフェース**（`GSPreprocessTapes` の抽象化）。

段のパターン `y.take L` に対する GS 分解 `decompose (y.take L) 8 = (s, p₁, r)` を計算し、
段テープ `P`／`U`／`Cnt` を次の段のために載せ直す動作列を与えるもの。
入力コピー `X`／`X2` とフラグ `F` には触らない。費用は `Cd * L + Dd` 以下。
（分解器が内部で使う作業テープは、この 6 本とは別に持つものとし、その上の動作数も
`Cd * L + Dd` に含まれているものとする。） -/
structure DecompOnTapes (sc : ℕ) (blank startSym endSym mark : Fin sc) where
  /-- この分解器が実際に計算する段の分解（`GSPreprocess` の素朴版でも
  `EndToEnd2.gsDec2` の正規化版でもよい）。 -/
  dec : List (Fin sc) → ℕ → ℕ × ℕ × ℕ
  /-- 段テープを載せ直す動作列。 -/
  acts : List (Fin sc) → ℕ → OvTapes sc → List (Act sc)
  /-- 費用の傾き。 -/
  Cd : ℕ
  /-- 費用の切片。 -/
  Dd : ℕ
  /-- **段の正当性**（`MiddleBorder.DecOK` の `dec` 版）。 -/
  decOK : ∀ (y : List (Fin sc)) (L : ℕ), 1 ≤ L →
    StageOK y 8 L (dec y L).1 (dec y L).2.1 (dec y L).2.2
  len_le : ∀ (y : List (Fin sc)) (L : ℕ) (ts : OvTapes sc),
    (acts y L ts).length ≤ Cd * L + Dd
  pat : ∀ (y : List (Fin sc)) (L : ℕ), 1 ≤ L → L ≤ y.length → ∀ ts : OvTapes sc,
    ScratchBlank blank ts →
    Tape.SeqView blank (applyActs blank (acts y L ts) ts).P
      (startSym :: ((y.take L).drop (dec y L).1 ++ [endSym])) 1
  upat : ∀ (y : List (Fin sc)) (L : ℕ), 1 ≤ L → L ≤ y.length → ∀ ts : OvTapes sc,
    ScratchBlank blank ts →
    Tape.SeqView blank (applyActs blank (acts y L ts) ts).U
      (startSym :: ((y.take L).take (dec y L).1 ++ [endSym])) 1
  cnt : ∀ (y : List (Fin sc)) (L : ℕ), 1 ≤ L → L ≤ y.length → ∀ ts : OvTapes sc,
    ScratchBlank blank ts →
    Tape.CounterView' blank mark (applyActs blank (acts y L ts) ts).Cnt (dec y L).2.1
  keepX : ∀ (y : List (Fin sc)) (L : ℕ) (ts : OvTapes sc),
    (applyActs blank (acts y L ts) ts).X = ts.X
  keepX2 : ∀ (y : List (Fin sc)) (L : ℕ) (ts : OvTapes sc),
    (applyActs blank (acts y L ts) ts).X2 = ts.X2
  keepF : ∀ (y : List (Fin sc)) (L : ℕ) (ts : OvTapes sc),
    (applyActs blank (acts y L ts) ts).F = ts.F
  /-- **作業テープ**：空白で渡せば空白で返す。 -/
  keepS : ∀ (y : List (Fin sc)) (L : ℕ) (ts : OvTapes sc), ScratchBlank blank ts →
    ScratchBlank blank (applyActs blank (acts y L ts) ts)

namespace DecompOnTapes

variable {blank startSym endSym mark : Fin sc}

/-- 段幅ごとの余裕込みの傾き。 -/
def A (D : DecompOnTapes sc blank startSym endSym mark) : ℕ := D.Cd + 2949

/-- ジョブ全体（ループ部分）の費用係数。 -/
def M (D : DecompOnTapes sc blank startSym endSym mark) : ℕ := 2 * D.A + D.Dd

end DecompOnTapes

/-! ## §4 1 バッチ分の平坦な動作列 -/

/-- 段の切り出し位置 `s`（分解器 `dec` に相対）。 -/
def stageS (dec : List (Fin sc) → ℕ → ℕ × ℕ × ℕ) (y : List (Fin sc)) (L : ℕ) : ℕ :=
  (dec y L).1

/-- 幾何級数の評価に使う算術補題。 -/
theorem geo_key {A B L L' R : ℕ} (h3 : 3 * L' + 1 ≤ L) (hR : R ≤ (2 * A + B) * L') :
    A * L + B + R ≤ (2 * A + B) * L := by
  obtain ⟨e, rfl⟩ : ∃ e, L = 3 * L' + 1 + e := ⟨L - (3 * L' + 1), by omega⟩
  have key : (2 * A + B) * (3 * L' + 1 + e)
      = (A * (3 * L' + 1 + e) + B + (2 * A + B) * L')
        + (A * L' + 2 * B * L' + A + A * e + B * e) := by ring
  calc A * (3 * L' + 1 + e) + B + R
      ≤ A * (3 * L' + 1 + e) + B + (2 * A + B) * L' := by omega
    _ ≤ (2 * A + B) * (3 * L' + 1 + e) := by rw [key]; exact Nat.le_add_right _ _

/-- 1 段分の動作列：段テープの載せ替え ＋ 段の走査。 -/
def stageActs (blank startSym endSym mark leftSym one : Fin sc)
    (D : DecompOnTapes sc blank startSym endSym mark) (y : List (Fin sc)) (L : ℕ)
    (ts : OvTapes sc) : List (Act sc) :=
  D.acts y L ts ++
    ovRunActs blank leftSym endSym mark one
      ((y.take L).take (stageS D.dec y L)) ((y.take L).drop (stageS D.dec y L)) (y.take L).reverse
      8 (D.dec y L).2.1 (D.dec y L).2.2
      (max 1 (2 * stageS D.dec y L)) (stageS D.dec y L) ((8 + 2) * L + 1) ⟨0, 0⟩
      (applyActs blank (D.acts y L ts) ts)

/-- **バッチのループ部分**：段を縮めながら、同じ `F` テープに書き続ける。
各段の終わりに `X`／`X2`／`F` のヘッドを次段の初期位置へ置き直す。 -/
def jobLoop (blank startSym endSym mark leftSym one : Fin sc)
    (D : DecompOnTapes sc blank startSym endSym mark) (y : List (Fin sc)) :
    ℕ → ℕ → OvTapes sc → List (Act sc)
  | 0, _, _ => []
  | fuel + 1, L, ts =>
      if L = 0 then [] else
        let a := stageActs blank startSym endSym mark leftSym one D y L ts
        let L' := nextLen (stageS D.dec y L)
        let h := homeActs sc L (L' - stageS D.dec y L') L'
        a ++ h ++ jobLoop blank startSym endSym mark leftSym one D y fuel L'
          (applyActs blank h (applyActs blank a ts))

/-- **1 バッチ分の動作列**：初期のヘッド合わせ ＋ ループ ＋ 読み出し位置 `rd` への `F` の
置き直し。 -/
def jobActs (blank startSym endSym mark leftSym one : Fin sc)
    (D : DecompOnTapes sc blank startSym endSym mark) (y : List (Fin sc)) (rd : ℕ)
    (ts : OvTapes sc) : List (Act sc) :=
  let h0 := homeActs sc y.length (y.length - stageS D.dec y y.length) y.length
  let l := jobLoop blank startSym endSym mark leftSym one D y (y.length + 1) y.length
    (applyActs blank h0 ts)
  h0 ++ l ++ homeF sc y.length rd

/-- フラグ語の長さは段の走査で変わらない。 -/
theorem ovRunFlags_length {u v T : List (Fin sc)} {one : Fin sc} {k p₁ r minimum : ℕ} :
    ∀ (fuel : ℕ) (st : ScanState) (fw : List (Fin sc)),
      (ovRunFlags u v T one k p₁ r minimum fuel st fw).length = fw.length := by
  intro fuel
  induction fuel with
  | zero => intro st fw; rfl
  | succ fuel ih =>
    intro st fw
    simp only [ovRunFlags]
    split_ifs with h
    · rfl
    · rw [ih]
      unfold stepFlags
      split_ifs <;> simp

/-- フラグ語の長さはジョブ全体でも変わらない。 -/
theorem jobFlags_length {x : List (Fin sc)} {dec : ℕ → ℕ × ℕ × ℕ} {one : Fin sc} {k : ℕ} :
    ∀ (fuel L : ℕ) (fw : List (Fin sc)),
      (jobFlags x dec one k fuel L fw).length = fw.length := by
  intro fuel
  induction fuel with
  | zero => intro L fw; rfl
  | succ fuel ih =>
    intro L fw
    simp only [jobFlags]
    split_ifs with h
    · rfl
    · rw [ih]
      simp only [stageFlags, ovRunFlags_length]

/-! ### バッチの正当性と費用 -/

section JobLoop

variable {blank startSym endSym mark leftSym one : Fin sc}

/-! ### 作業テープの空白性はバッチ全体で保たれる -/

/-- 一段：分解器が空白で返し、走査は作業テープに触れない。 -/
theorem stageActs_scratch (D : DecompOnTapes sc blank startSym endSym mark)
    (y : List (Fin sc)) (L : ℕ) (ts : OvTapes sc) (h : ScratchBlank blank ts) :
    ScratchBlank blank
      (applyActs blank (stageActs blank startSym endSym mark leftSym one D y L ts) ts) := by
  rw [stageActs, applyActs_append]
  exact ovRunActs_scratchBlank _ _ _ (D.keepS y L ts h)

/-- ループ部分。 -/
theorem jobLoop_scratch (D : DecompOnTapes sc blank startSym endSym mark)
    (y : List (Fin sc)) :
    ∀ (fuel L : ℕ) (ts : OvTapes sc), ScratchBlank blank ts →
      ScratchBlank blank (applyActs blank
        (jobLoop blank startSym endSym mark leftSym one D y fuel L ts) ts) := by
  intro fuel
  induction fuel with
  | zero => intro L ts h; exact h
  | succ fuel ih =>
    intro L ts h
    simp only [jobLoop]
    by_cases h0 : L = 0
    · rw [if_pos h0]; exact h
    · rw [if_neg h0, applyActs_append, applyActs_append]
      exact ih _ _ (applyActs_scratchBlank (noScratch_homeActs _ _ _ _)
        (stageActs_scratch D y L ts h))

/-- 1 バッチ分。 -/
theorem jobActs_scratch (D : DecompOnTapes sc blank startSym endSym mark)
    (y : List (Fin sc)) (rd : ℕ) (ts : OvTapes sc) (h : ScratchBlank blank ts) :
    ScratchBlank blank
      (applyActs blank (jobActs blank startSym endSym mark leftSym one D y rd ts) ts) := by
  simp only [jobActs, applyActs_append]
  exact applyActs_scratchBlank (noScratch_homeF _ _ _)
    (jobLoop_scratch D y _ _ _ (applyActs_scratchBlank (noScratch_homeActs _ _ _ _) h))

/-- **バッチのループ部分の主定理**：動作数は `D.M * L` 以下で、走り終えたあとの
`F` テープは `jobFlags` を保持し、ヘッドは添字 `≤ L` にある。 -/
theorem jobLoop_ok (D : DecompOnTapes sc blank startSym endSym mark) {y : List (Fin sc)}
    (hleft : leftSym ∉ y) (hend : endSym ∉ y)
 :
    ∀ (fuel L : ℕ) (ts : OvTapes sc) (fw : List (Fin sc)),
      L ≤ y.length → y.length + 1 ≤ fw.length → ScratchBlank blank ts →
      Tape.SeqView blank ts.X (leftSym :: y) (L - stageS D.dec y L) →
      Tape.SeqView blank ts.X2 (leftSym :: y) L →
      Tape.SeqView blank ts.F fw L →
      (jobLoop blank startSym endSym mark leftSym one D y fuel L ts).length ≤ D.M * L ∧
      ∃ i, i ≤ L ∧
        Tape.SeqView blank
          (applyActs blank
            (jobLoop blank startSym endSym mark leftSym one D y fuel L ts) ts).F
          (jobFlags y (D.dec y) one 8 fuel L fw) i := by
  have hOK : ∀ L, 1 ≤ L → L ≤ y.length →
      StageOK y 8 L (D.dec y L).1 (D.dec y L).2.1 (D.dec y L).2.2 :=
    fun L hL _ => D.decOK y L hL
  intro fuel
  induction fuel with
  | zero =>
    intro L ts fw _ _ _ _ _ hF
    exact ⟨Nat.zero_le _, L, le_rfl, hF⟩
  | succ fuel ih =>
    intro L ts fw hL hfw hSB hX hX2 hF
    simp only [jobLoop, jobFlags]
    by_cases h0 : L = 0
    · rw [if_pos h0, if_pos (show L = 0 from h0)]
      exact ⟨Nat.zero_le _, L, le_rfl, hF⟩
    rw [if_neg h0, if_neg h0]
    -- 段のデータ
    have hOKL : StageOK y 8 L (stageS D.dec y L) (D.dec y L).2.1
        (D.dec y L).2.2 := hOK L (by omega) hL
    have hylen : (y.take L).length = L := by simp only [List.length_take]; omega
    have hcut : stageS D.dec y L ≤ L := hOKL.cut_le
    have hshort : 7 * stageS D.dec y L < L := by have := hOKL.cut_short; omega
    have hulen : ((y.take L).take (stageS D.dec y L)).length = stageS D.dec y L := by
      simp only [List.length_take]; omega
    have hvlen : ((y.take L).drop (stageS D.dec y L)).length = L - stageS D.dec y L := by
      simp only [List.length_drop]; omega
    have hTlen : ((y.take L).reverse).length = L := by
      simp only [List.length_reverse]; omega
    have hlenuv : ((y.take L).take (stageS D.dec y L)).length
        + ((y.take L).drop (stageS D.dec y L)).length = ((y.take L).reverse).length := by omega
    have hendv : endSym ∉ (y.take L).drop (stageS D.dec y L) := fun hc =>
      hend (List.mem_of_mem_take (List.mem_of_mem_drop hc))
    have hmin : max 1 (2 * ((y.take L).take (stageS D.dec y L)).length) ≤ max 1 (2 * stageS D.dec y L) := by
      rw [hulen]
    have hinv0 : OvInv ((y.take L).take (stageS D.dec y L)) ((y.take L).drop (stageS D.dec y L))
        ((y.take L).reverse) ⟨0, 0⟩ :=
      ⟨by simpa using matchLen_zero _ _ _, by simp only []; omega⟩
    -- 段テープの載せ替え後の符号化
    have hE0 : OvEncodes blank leftSym startSym endSym mark
        ((y.take L).take (stageS D.dec y L)) ((y.take L).drop (stageS D.dec y L)) y fw L
        (D.dec y L).2.1 (applyActs blank (D.acts y L ts) ts) ⟨0, 0⟩ := by
      refine ⟨D.pat y L (by omega) hL ts hSB, ?_, D.cnt y L (by omega) hL ts hSB,
        D.upat y L (by omega) hL ts hSB, ?_, ?_⟩
      · rw [D.keepX y L ts]; simpa [hulen] using hX
      · rw [D.keepX2 y L ts]; simpa using hX2
      · rw [D.keepF y L ts]; simpa using hF
    have hK := hOKL.ksimple
    have hrun := ovRunTapes_encodes (one := one) (c := stageS D.dec y L) (xw := y)
      hK (by omega : (0:ℕ) < 8) hL hleft hendv rfl hulen.symm hlenuv hmin
      ((8 + 2) * L + 1) ⟨0, 0⟩ (applyActs blank (D.acts y L ts) ts) fw hinv0 hE0
    have hSA := ovRunActs_length (one := one) (c := stageS D.dec y L) (xw := y) (startSym := startSym)
      (mark := mark) hK (by omega : (0:ℕ) < 8) hL hleft hendv rfl hulen.symm hlenuv hmin
      ((8 + 2) * L + 1) ⟨0, 0⟩ (applyActs blank (D.acts y L ts) ts) fw hinv0 hE0
    have hSAcost : ovRunCost ((y.take L).take (stageS D.dec y L)) ((y.take L).drop (stageS D.dec y L))
        ((y.take L).reverse) 8 (D.dec y L).2.1 (D.dec y L).2.2
        (max 1 (2 * stageS D.dec y L)) ((8 + 2) * L + 1) ⟨0, 0⟩ ≤ 2945 * L :=
      stage_tape_cost_le (x := y) (dec := D.dec y) hL (by omega) hOKL
    have hts2 : applyActs blank (stageActs blank startSym endSym mark leftSym one D y L ts) ts
        = ovRunTapes blank leftSym endSym mark one ((y.take L).take (stageS D.dec y L))
            ((y.take L).drop (stageS D.dec y L)) ((y.take L).reverse) 8
            (D.dec y L).2.1 (D.dec y L).2.2
            (max 1 (2 * stageS D.dec y L)) (stageS D.dec y L) ((8 + 2) * L + 1) ⟨0, 0⟩
            (applyActs blank (D.acts y L ts) ts) := by
      simp only [stageActs, applyActs_append, ovRunActs_apply]
    have hrun' : OvEncodes blank leftSym startSym endSym mark
        ((y.take L).take (stageS D.dec y L)) ((y.take L).drop (stageS D.dec y L)) y
        (ovRunFlags ((y.take L).take (stageS D.dec y L)) ((y.take L).drop (stageS D.dec y L))
          ((y.take L).reverse) one 8 (D.dec y L).2.1
          (D.dec y L).2.2 (max 1 (2 * stageS D.dec y L)) ((8 + 2) * L + 1) ⟨0, 0⟩ fw)
        L (D.dec y L).2.1
        (applyActs blank (stageActs blank startSym endSym mark leftSym one D y L ts) ts)
        (ovRunState ((y.take L).take (stageS D.dec y L)) ((y.take L).drop (stageS D.dec y L))
          ((y.take L).reverse) 8 (D.dec y L).2.1 (D.dec y L).2.2
          (max 1 (2 * stageS D.dec y L)) ((8 + 2) * L + 1) ⟨0, 0⟩) := by
      rw [hts2]; exact hrun
    -- 継ぎ目
    have h3 : 3 * nextLen (stageS D.dec y L) + 1 ≤ L := nextLen_shrink hshort
    have hL' : nextLen (stageS D.dec y L) ≤ y.length := by omega
    have hfw2 : y.length + 1 ≤ (ovRunFlags ((y.take L).take (stageS D.dec y L))
        ((y.take L).drop (stageS D.dec y L))
        ((y.take L).reverse) one 8 (D.dec y L).2.1
        (D.dec y L).2.2 (max 1 (2 * stageS D.dec y L)) ((8 + 2) * L + 1) ⟨0, 0⟩
        fw).length := by rw [ovRunFlags_length]; exact hfw
    have hhome := homeActs_eff (blank := blank) L
      (nextLen (stageS D.dec y L) - stageS D.dec y (nextLen (stageS D.dec y L))) (nextLen (stageS D.dec y L))
      (applyActs blank (stageActs blank startSym endSym mark leftSym one D y L ts) ts)
    have hcons : (leftSym :: y).length = y.length + 1 := by simp
    have hih := ih (nextLen (stageS D.dec y L))
      (applyActs blank (homeActs sc L
        (nextLen (stageS D.dec y L) - stageS D.dec y (nextLen (stageS D.dec y L))) (nextLen (stageS D.dec y L)))
        (applyActs blank (stageActs blank startSym endSym mark leftSym one D y L ts) ts)) _
      hL' hfw2
      (applyActs_scratchBlank (noScratch_homeActs _ _ _ _) (stageActs_scratch D y L ts hSB))
      (by rw [hhome]; exact seq_home hrun'.txt (Nat.sub_le _ _) (by rw [hcons]; omega))
      (by rw [hhome]; exact seq_home hrun'.txt2 (Nat.sub_le _ _) (by rw [hcons]; omega))
      (by rw [hhome]; exact seq_home hrun'.flg (Nat.sub_le _ _) (by omega))
    have hstage : (stageActs blank startSym endSym mark leftSym one D y L ts).length
        ≤ D.Cd * L + D.Dd + 2945 * L := by
      simp only [stageActs, List.length_append, hSA]
      have := D.len_le y L ts
      omega
    refine ⟨?_, ?_⟩
    · rw [List.length_append, List.length_append, homeActs_length]
      have hMdef : (2 * D.A + D.Dd) * L = D.M * L := rfl
      have hAdef : D.A * L = D.Cd * L + 2949 * L := by
        simp only [DecompOnTapes.A, Nat.add_mul]
      have hgeo := geo_key (A := D.A) (B := D.Dd) (L := L) (L' := nextLen (stageS D.dec y L))
        (R := (jobLoop blank startSym endSym mark leftSym one D y fuel (nextLen (stageS D.dec y L))
          (applyActs blank (homeActs sc L
            (nextLen (stageS D.dec y L) - stageS D.dec y (nextLen (stageS D.dec y L))) (nextLen (stageS D.dec y L)))
            (applyActs blank (stageActs blank startSym endSym mark leftSym one D y L ts)
              ts))).length) h3 (by rw [show (2 * D.A + D.Dd) = D.M from rfl]; exact hih.1)
      omega
    · obtain ⟨i, hi, hsv⟩ := hih.2
      refine ⟨i, by omega, ?_⟩
      rw [applyActs_append, applyActs_append]
      exact hsv

/-- 1 バッチ分の費用係数。 -/
def Cjob (D : DecompOnTapes sc blank startSym endSym mark) : ℕ := D.M + 8

/-- **1 バッチの主定理**：ヘッドがどこにあっても（添字 `≤ |y|`）、`jobActs` を流し切れば
`F` テープは窓 `y` の回文接頭辞フラグ `jobFlags` を保持し、ヘッドは読み出し位置 `rd` に
立つ。動作数は `Cjob D * |y|` 以下。 -/
theorem jobActs_ok (D : DecompOnTapes sc blank startSym endSym mark) {y : List (Fin sc)}
    (hleft : leftSym ∉ y) (hend : endSym ∉ y)
    (ts : OvTapes sc) (fw : List (Fin sc)) (rd : ℕ)
    (hfw : y.length + 1 ≤ fw.length) (hrd : rd ≤ y.length)
    (hSB : ScratchBlank blank ts)
    (hX : ∃ i, i ≤ y.length ∧ Tape.SeqView blank ts.X (leftSym :: y) i)
    (hX2 : ∃ i, i ≤ y.length ∧ Tape.SeqView blank ts.X2 (leftSym :: y) i)
    (hF : ∃ i, i ≤ y.length ∧ Tape.SeqView blank ts.F fw i) :
    (jobActs blank startSym endSym mark leftSym one D y rd ts).length
        ≤ Cjob D * y.length ∧
      Tape.SeqView blank
        (applyActs blank (jobActs blank startSym endSym mark leftSym one D y rd ts) ts).F
        (jobFlags y (D.dec y) one 8 (y.length + 1) y.length fw) rd := by
  have hOK : ∀ L, 1 ≤ L → L ≤ y.length →
      StageOK y 8 L (D.dec y L).1 (D.dec y L).2.1 (D.dec y L).2.2 :=
    fun L hL _ => D.decOK y L hL
  obtain ⟨iX, hiX, hXv⟩ := hX
  obtain ⟨iX2, hiX2, hX2v⟩ := hX2
  obtain ⟨iF, hiF, hFv⟩ := hF
  have hcons : (leftSym :: y).length = y.length + 1 := by simp
  simp only [jobActs]
  have hh0 := homeActs_eff (blank := blank) y.length
    (y.length - stageS D.dec y y.length) y.length ts
  have hj := jobLoop_ok (one := one) D hleft hend (y.length + 1) y.length
    (applyActs blank (homeActs sc y.length (y.length - stageS D.dec y y.length) y.length) ts) fw
    le_rfl hfw
    (applyActs_scratchBlank (noScratch_homeActs _ _ _ _) hSB)
    (by rw [hh0]; exact seq_home hXv hiX (by rw [hcons]; omega))
    (by rw [hh0]; exact seq_home hX2v hiX2 (by rw [hcons]; omega))
    (by rw [hh0]; exact seq_home hFv hiF (by omega))
  obtain ⟨hlen, i, hi, hsv⟩ := hj
  constructor
  · rw [List.length_append, List.length_append, homeActs_length, homeF_length]
    have hC : Cjob D * y.length = D.M * y.length + 8 * y.length := by
      simp only [Cjob, Nat.add_mul]
    omega
  · rw [applyActs_append, applyActs_append, homeF_eff]
    exact seq_home hsv hi (by rw [jobFlags_length]; omega)

end JobLoop

/-! ## §5 フラグテープの初期化とバッチ全体 -/

/-- `F` テープの添字 `0..n` を `zero` で埋める動作列（ヘッドは添字 `n` から左へ）。 -/
def clearF (zero : Fin sc) : ℕ → List (Act sc)
  | 0 => [Act.Fset zero]
  | n + 1 => Act.Fset zero :: Act.F .left :: clearF zero n

@[simp] theorem clearF_length (zero : Fin sc) : ∀ n, (clearF zero n).length = 2 * n + 1 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp only [clearF, List.length_cons, ih]; omega

/-- 初期化も作業テープに触れない。 -/
theorem noScratch_clearF (zero : Fin sc) : ∀ n, NoScratchAll (clearF zero n) := by
  intro n
  induction n with
  | zero => exact noScratchAll_cons trivial noScratchAll_nil
  | succ n ih => exact noScratchAll_cons trivial (noScratchAll_cons trivial ih)

/-- 埋めたあとのフラグ語。 -/
def clearWord (zero : Fin sc) : ℕ → List (Fin sc) → List (Fin sc)
  | 0, w => w.set 0 zero
  | n + 1, w => clearWord zero n (w.set (n + 1) zero)

@[simp] theorem clearWord_length (zero : Fin sc) :
    ∀ (n : ℕ) (w : List (Fin sc)), (clearWord zero n w).length = w.length := by
  intro n
  induction n with
  | zero => intro w; simp [clearWord]
  | succ n ih => intro w; simp [clearWord, ih]

theorem clearWord_gt (zero : Fin sc) :
    ∀ (n : ℕ) (w : List (Fin sc)) (ℓ : ℕ), n < ℓ → (clearWord zero n w)[ℓ]? = w[ℓ]? := by
  intro n
  induction n with
  | zero =>
    intro w ℓ h
    simp only [clearWord]
    exact List.getElem?_set_ne (by omega)
  | succ n ih =>
    intro w ℓ h
    rw [clearWord, ih _ ℓ (by omega)]
    exact List.getElem?_set_ne (by omega)

theorem clearWord_le (zero : Fin sc) :
    ∀ (n : ℕ) (w : List (Fin sc)) (ℓ : ℕ), ℓ ≤ n → ℓ < w.length →
      (clearWord zero n w)[ℓ]? = some zero := by
  intro n
  induction n with
  | zero =>
    intro w ℓ h hw
    have : ℓ = 0 := by omega
    subst this
    simp only [clearWord]
    exact List.getElem?_set_self (by omega)
  | succ n ih =>
    intro w ℓ h hw
    rcases Nat.lt_or_ge n ℓ with hlt | hge
    · have hℓ : ℓ = n + 1 := by omega
      subst hℓ
      rw [clearWord, clearWord_gt zero n _ (n + 1) (by omega)]
      exact List.getElem?_set_self (by simpa using hw)
    · rw [clearWord]
      exact ih _ ℓ hge (by simpa using hw)

theorem clearF_spec {blank zero : Fin sc} :
    ∀ (n : ℕ) (ts : OvTapes sc) (w : List (Fin sc)), Tape.SeqView blank ts.F w n →
      (applyActs blank (clearF zero n) ts).X = ts.X ∧
        (applyActs blank (clearF zero n) ts).X2 = ts.X2 ∧
        Tape.SeqView blank (applyActs blank (clearF zero n) ts).F (clearWord zero n w) 0 := by
  intro n
  induction n with
  | zero =>
    intro ts w h
    refine ⟨rfl, rfl, ?_⟩
    exact Tape.seq_write h zero
  | succ n ih =>
    intro ts w h
    have h1 : Tape.SeqView blank (Tape.step blank ts.F zero .stay) (w.set (n + 1) zero) (n + 1) :=
      Tape.seq_write h zero
    have h2 : Tape.SeqView blank
        (Tape.step blank (Tape.step blank ts.F zero .stay)
          (Tape.step blank ts.F zero .stay).focus .left) (w.set (n + 1) zero) n :=
      Tape.seq_move_left h1
    have := ih (applyAct blank (applyAct blank ts (Act.Fset zero)) (Act.F .left))
      (w.set (n + 1) zero) h2
    simpa [clearF, applyActs_cons, applyAct, clearWord] using this

/-- **1 バッチの全動作列**：`F` のヘッド合わせ → フラグ語の初期化 → ジョブ本体。 -/
def batchActs (blank startSym endSym mark leftSym one zero : Fin sc)
    (D : DecompOnTapes sc blank startSym endSym mark) (y : List (Fin sc)) (rd : ℕ)
    (ts : OvTapes sc) : List (Act sc) :=
  let h := homeF sc y.length y.length
  let c := clearF zero y.length
  h ++ c ++ jobActs blank startSym endSym mark leftSym one D y rd
    (applyActs blank c (applyActs blank h ts))

/-- 1 バッチの費用係数（`Cjob D + 4` 倍と定数 1）。 -/
def Cbatch (D : DecompOnTapes sc blank startSym endSym mark) : ℕ := Cjob D + 4

section Batch

variable {blank startSym endSym mark leftSym one zero : Fin sc}

/-- バッチ全体でも作業テープの空白性は保たれる。 -/
theorem batchActs_scratch (D : DecompOnTapes sc blank startSym endSym mark)
    (y : List (Fin sc)) (rd : ℕ) (ts : OvTapes sc) (h : ScratchBlank blank ts) :
    ScratchBlank blank (applyActs blank
      (batchActs blank startSym endSym mark leftSym one zero D y rd ts) ts) := by
  simp only [batchActs, applyActs_append]
  exact jobActs_scratch D y rd _ (applyActs_scratchBlank (noScratch_clearF _ _)
    (applyActs_scratchBlank (noScratch_homeF _ _ _) h))

/-- **バッチの主定理**：バッチを流し切ると、`F` のヘッドは添字 `rd` に立ち、そこで読める
記号が `one` であることと `y.take rd` が回文であることが同値になる。 -/
theorem batchActs_ok (D : DecompOnTapes sc blank startSym endSym mark) {y : List (Fin sc)}
    (hne : one ≠ zero) (hleft : leftSym ∉ y) (hend : endSym ∉ y)
    (ts : OvTapes sc) (fw : List (Fin sc)) (rd : ℕ)
    (hfw : y.length + 1 ≤ fw.length) (h1 : 1 ≤ rd) (h2 : rd ≤ y.length)
    (hSB : ScratchBlank blank ts)
    (hX : ∃ i, i ≤ y.length ∧ Tape.SeqView blank ts.X (leftSym :: y) i)
    (hX2 : ∃ i, i ≤ y.length ∧ Tape.SeqView blank ts.X2 (leftSym :: y) i)
    (hF : ∃ i, i ≤ y.length ∧ Tape.SeqView blank ts.F fw i) :
    (batchActs blank startSym endSym mark leftSym one zero D y rd ts).length
        ≤ Cbatch D * y.length + 1 ∧
      (Tape.read (applyActs blank
        (batchActs blank startSym endSym mark leftSym one zero D y rd ts) ts).F = one
          ↔ IsPal (y.take rd)) := by
  have hOK : ∀ L, 1 ≤ L → L ≤ y.length →
      StageOK y 8 L (D.dec y L).1 (D.dec y L).2.1 (D.dec y L).2.2 :=
    fun L hL _ => D.decOK y L hL
  obtain ⟨iF, hiF, hFv⟩ := hF
  simp only [batchActs]
  have hh := homeF_eff (blank := blank) y.length y.length ts
  have hFh : Tape.SeqView blank (applyActs blank (homeF sc y.length y.length) ts).F
      fw y.length := by
    rw [hh]; exact seq_home hFv hiF (by omega)
  have hcl := clearF_spec (zero := zero) y.length
    (applyActs blank (homeF sc y.length y.length) ts) fw hFh
  have hXk : (applyActs blank (clearF zero y.length)
      (applyActs blank (homeF sc y.length y.length) ts)).X = ts.X := by
    rw [hcl.1, hh]
  have hX2k : (applyActs blank (clearF zero y.length)
      (applyActs blank (homeF sc y.length y.length) ts)).X2 = ts.X2 := by
    rw [hcl.2.1, hh]
  have hcw : y.length + 1 ≤ (clearWord zero y.length fw).length := by
    rw [clearWord_length]; exact hfw
  have hjob := jobActs_ok (one := one) D hleft hend
    (applyActs blank (clearF zero y.length)
      (applyActs blank (homeF sc y.length y.length) ts))
    (clearWord zero y.length fw) rd hcw h2
    (applyActs_scratchBlank (noScratch_clearF _ _)
      (applyActs_scratchBlank (noScratch_homeF _ _ _) hSB))
    (by rw [hXk]; exact hX) (by rw [hX2k]; exact hX2)
    ⟨0, Nat.zero_le _, hcl.2.2⟩
  refine ⟨?_, ?_⟩
  · rw [List.length_append, List.length_append, homeF_length, clearF_length]
    have hC : Cbatch D * y.length = Cjob D * y.length + 4 * y.length := by
      simp only [Cbatch, Nat.add_mul]
    have := hjob.1
    omega
  · rw [applyActs_append, applyActs_append]
    have hread := hjob.2.read_eq
    have hz : (clearWord zero y.length fw)[rd]? = some zero :=
      clearWord_le zero y.length fw rd h2 (by omega)
    have hiff := flags_on_tape_eq_palPrefixFlagsGS (x := y) (dec := D.dec y)
      (one := one) (zero := zero) (k := 8) (fw := clearWord zero y.length fw)
      (by omega) hne hOK rd h1 h2 (by omega) hz
    have hpal := palPrefixFlagsGS_spec (x := y) (dec := D.dec y) (k := 8)
      (by omega) hOK rd h2
    constructor
    · intro hr
      have : (jobFlags y (D.dec y) one 8 (y.length + 1) y.length
          (clearWord zero y.length fw))[rd]? = some one := by rw [hread, hr]
      have := hiff.1 this
      rw [hpal] at this
      simpa using this
    · intro hp
      have : (palPrefixFlagsGS y (D.dec y) 8)[rd]? = some true := by
        rw [hpal]; simpa using hp
      have h' := hiff.2 this
      rw [hread] at h'
      exact Option.some_inj.1 h'

end Batch

/-! ## §6 レートと締切 -/

/-- テープ版のサービスレート：1 ラウンドに進める動作数。 -/
def rateM (D : DecompOnTapes sc blank startSym endSym mark) : ℕ := 50 * Cbatch D + 1

/-- 1 ラウンドの費用上界（挽きの動作数 ＋ 出力テープの 1 歩）。 -/
def CmT (D : DecompOnTapes sc blank startSym endSym mark) : ℕ := rateM D + 1

section Fits

variable {blank startSym endSym mark : Fin sc}

/-- 窓の長さの上界（`borderMiddle_work_fits` と同じ評価）。 -/
theorem wnd_length_le {α : Type} (w : List α) {S p : ℕ} (hS : 8 ≤ S)
    (hp : p ≤ MiddleBorder.numJobs) : (MiddleBorder.Wnd w S p).length ≤ 5 * S := by
  have h1 : p * MiddleBorder.gw S ≤ 13 * MiddleBorder.gw S :=
    Nat.mul_le_mul_right _ (by simp only [MiddleBorder.numJobs] at hp; omega)
  have h2 : 13 * MiddleBorder.gw S ≤ 4 * S := by simp only [MiddleBorder.gw]; omega
  simp only [MiddleBorder.Wnd, List.length_take, List.length_drop]
  omega

/-- **レートの妥当性（テープ版）**：`Cbatch D * L + 1` 動作のバッチは、窓長が `L ≤ 5S` なら
解放から次の解放までに使える `gw S - 1` ラウンド分の動作 `rateM D * (gw S - 1)` に収まる。 -/
theorem fits_of_length_le (D : DecompOnTapes sc blank startSym endSym mark) {S L n : ℕ}
    (_hS : 8 ≤ S) (hev : 2 * (S / 2) = S) (hL : L ≤ 5 * S) (h : n ≤ Cbatch D * L + 1) :
    n ≤ rateM D * (MiddleBorder.gw S - 1) := by
  have hg : 2 ≤ MiddleBorder.gw S := by simp only [MiddleBorder.gw]; omega
  have hS10 : 5 * S ≤ 5 * (10 * (MiddleBorder.gw S - 1)) := by
    simp only [MiddleBorder.gw]; omega
  calc n ≤ Cbatch D * L + 1 := h
    _ ≤ Cbatch D * (5 * S) + 1 := Nat.add_le_add_right (Nat.mul_le_mul_left _ hL) 1
    _ ≤ Cbatch D * (5 * (10 * (MiddleBorder.gw S - 1))) + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hS10) 1
    _ = 50 * Cbatch D * (MiddleBorder.gw S - 1) + 1 := by ring
    _ ≤ 50 * Cbatch D * (MiddleBorder.gw S - 1) + (MiddleBorder.gw S - 1) :=
        Nat.add_le_add_left (by omega) _
    _ = rateM D * (MiddleBorder.gw S - 1) := by simp only [rateM]; ring

/-- **締切**：バッチ `p` は解放 `relTime S p` の直後から `gw S - 1` ラウンド挽けば
完成し（`fits_of_length_le` と `gsteps_done`）、その完成時刻 `relTime S (p+1)` は
そのバッチのフラグが最初に必要になる時刻 `2*S + (p-1)*gw S` 以下である。 -/
theorem deadline_ok {S p : ℕ} (hS : 8 ≤ S) (hev : 2 * (S / 2) = S) (hp : 1 ≤ p) :
    MiddleBorder.relTime S (p + 1) ≤ 2 * S + (p - 1) * MiddleBorder.gw S :=
  MiddleBorder.borderMiddle_deadline hS hev hp

/-- **完成**：`gw S - 1` ラウンド挽けば、バッチの動作列は残らず実行されている。 -/
theorem batch_complete (D : DecompOnTapes sc blank startSym endSym mark) {S L : ℕ}
    (hS : 8 ≤ S) (hev : 2 * (S / 2) = S) (hL : L ≤ 5 * S) (l : List (Act sc)) (ts : OvTapes sc)
    (hl : l.length ≤ Cbatch D * L + 1) :
    gsteps blank (rateM D) (MiddleBorder.gw S - 1) ⟨l, ts⟩
      = ⟨[], applyActs blank l ts⟩ :=
  gsteps_done blank _ l ts (by
    have := fits_of_length_le D hS hev hL hl
    calc l.length ≤ rateM D * (MiddleBorder.gw S - 1) := this
      _ = (MiddleBorder.gw S - 1) * rateM D := Nat.mul_comm _ _)

end Fits

/-! ## §7 出力テープ（ダブルバッファの読み出し側） -/

/-- 出力側のフラグテープを 1 セル右へ（1 ラウンド 1 歩）。 -/
def outStep (sc : ℕ) : List (Act sc) := mvF .right 1

@[simp] theorem outStep_length (sc : ℕ) : (outStep sc).length = 1 := by simp [outStep]

theorem noScratch_outStep (sc : ℕ) : NoScratchAll (outStep sc) := noScratch_mvF _ _

/-- 読み出しヘッドは 1 ラウンドで添字を 1 進める。 -/
theorem outStep_spec {blank : Fin sc} {ts : OvTapes sc} {w : List (Fin sc)} {i : ℕ}
    (h : Tape.SeqView blank ts.F w i) (hi : i + 1 < w.length) :
    Tape.SeqView blank (applyActs blank (outStep sc) ts).F w (i + 1) := by
  rw [outStep, mvF_eff]
  exact Tape.seq_move_right h hi

/-! ## §8 読み出しと `borderMiddle` のフラグの一致 -/

section FlagRead

variable {blank startSym endSym mark leftSym one zero : Fin sc}

/-- 凍結窓に記号は増えない。 -/
theorem mem_wnd {w : List (Fin sc)} {S p : ℕ} {a : Fin sc}
    (h : a ∈ MiddleBorder.Wnd w S p) : a ∈ w :=
  List.mem_of_mem_drop (List.mem_of_mem_take h)

/-- **フラグの読み出し**：バッチ `p` を流し切ったテープの、添字 `n - S` で読める記号が
`one` であることは、中央部 `(w.drop (S/2)).take (n - S)` が回文であることと同値。
これは `MiddleBorder.borderMiddle_flag_correct` の右辺そのものである。 -/
theorem batch_read_flag (D : DecompOnTapes sc blank startSym endSym mark)
    {w : List (Fin sc)} {S p n : ℕ}
    (hne : one ≠ zero)
    (hleft : leftSym ∉ w) (hend : endSym ∉ w)
    (ts : OvTapes sc) (fw : List (Fin sc))
    (hfw : (MiddleBorder.Wnd w S p).length + 1 ≤ fw.length)
    (h1 : 1 ≤ n - S) (h2 : n - S ≤ (MiddleBorder.Wnd w S p).length)
    (hcov : n - S ≤ S + p * MiddleBorder.gw S)
    (hSB : ScratchBlank blank ts)
    (hX : ∃ i, i ≤ (MiddleBorder.Wnd w S p).length ∧
      Tape.SeqView blank ts.X (leftSym :: MiddleBorder.Wnd w S p) i)
    (hX2 : ∃ i, i ≤ (MiddleBorder.Wnd w S p).length ∧
      Tape.SeqView blank ts.X2 (leftSym :: MiddleBorder.Wnd w S p) i)
    (hF : ∃ i, i ≤ (MiddleBorder.Wnd w S p).length ∧ Tape.SeqView blank ts.F fw i) :
    (Tape.read (applyActs blank (batchActs blank startSym endSym mark leftSym one zero D
        (MiddleBorder.Wnd w S p) (n - S) ts) ts).F = one)
      ↔ IsPal ((w.drop (S / 2)).take (n - S)) := by
  have hOK : ∀ L, 1 ≤ L → L ≤ (MiddleBorder.Wnd w S p).length →
      StageOK (MiddleBorder.Wnd w S p) 8 L (D.dec (MiddleBorder.Wnd w S p) L).1
        (D.dec (MiddleBorder.Wnd w S p) L).2.1 (D.dec (MiddleBorder.Wnd w S p) L).2.2 :=
    fun L hL _ => D.decOK (MiddleBorder.Wnd w S p) L hL
  have hkey : (MiddleBorder.Wnd w S p).take (n - S) = (w.drop (S / 2)).take (n - S) := by
    simp only [MiddleBorder.Wnd, List.take_take]
    congr 1
    omega
  have h := (batchActs_ok D hne (fun hc => hleft (mem_wnd hc)) (fun hc => hend (mem_wnd hc))
    ts fw (n - S) hfw h1 h2 hSB hX hX2 hF).2
  rw [h, hkey]

end FlagRead

/-! ## §9 フラグ語の仕様と、バッチが残すフラグ語 -/

/-- フラグ語の仕様：添字 `1..|y|` で `one` が読めることと `y.take ℓ` が回文であることが
同値。 -/
def FlagWordOK (one : Fin sc) (N : ℕ) (y ω : List (Fin sc)) : Prop :=
  N ≤ ω.length ∧
    ∀ ℓ, 1 ≤ ℓ → ℓ ≤ y.length → ((ω[ℓ]? = some one) ↔ IsPal (y.take ℓ))

theorem FlagWordOK.read {blank one : Fin sc} {y ω : List (Fin sc)} {N : ℕ}
    {tp : TapeConfiguration sc} {ℓ : ℕ} (h : FlagWordOK one N y ω)
    (hs : Tape.SeqView blank tp ω ℓ) (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ y.length) :
    Tape.read tp = one ↔ IsPal (y.take ℓ) := by
  rw [← h.2 ℓ h1 h2, hs.read_eq]
  constructor
  · intro hc; rw [hc]
  · intro hc; exact Option.some_inj.1 hc

section BatchWord

variable {blank startSym endSym mark leftSym one zero : Fin sc}

/-- **バッチが残すフラグ語**：バッチを流し切ると、`F` テープには `FlagWordOK` を満たす語が
残り、ヘッドは読み出し位置 `rd` に立つ。 -/
theorem batchActs_word (D : DecompOnTapes sc blank startSym endSym mark) {y : List (Fin sc)}
    (hne : one ≠ zero) (hleft : leftSym ∉ y) (hend : endSym ∉ y)
    (ts : OvTapes sc) (fw : List (Fin sc)) (rd N : ℕ)
    (hfw : y.length + 1 ≤ fw.length) (hN : N ≤ fw.length) (hrd : rd ≤ y.length)
    (hSB : ScratchBlank blank ts)
    (hX : ∃ i, i ≤ y.length ∧ Tape.SeqView blank ts.X (leftSym :: y) i)
    (hX2 : ∃ i, i ≤ y.length ∧ Tape.SeqView blank ts.X2 (leftSym :: y) i)
    (hF : ∃ i, i ≤ y.length ∧ Tape.SeqView blank ts.F fw i) :
    (batchActs blank startSym endSym mark leftSym one zero D y rd ts).length
        ≤ Cbatch D * y.length + 1 ∧
      ∃ ω, FlagWordOK one N y ω ∧
        Tape.SeqView blank (applyActs blank
          (batchActs blank startSym endSym mark leftSym one zero D y rd ts) ts).F ω rd := by
  have hOK : ∀ L, 1 ≤ L → L ≤ y.length →
      StageOK y 8 L (D.dec y L).1 (D.dec y L).2.1 (D.dec y L).2.2 :=
    fun L hL _ => D.decOK y L hL
  obtain ⟨iF, hiF, hFv⟩ := hF
  simp only [batchActs]
  have hh := homeF_eff (blank := blank) y.length y.length ts
  have hFh : Tape.SeqView blank (applyActs blank (homeF sc y.length y.length) ts).F
      fw y.length := by
    rw [hh]; exact seq_home hFv hiF (by omega)
  have hcl := clearF_spec (zero := zero) y.length
    (applyActs blank (homeF sc y.length y.length) ts) fw hFh
  have hXk : (applyActs blank (clearF zero y.length)
      (applyActs blank (homeF sc y.length y.length) ts)).X = ts.X := by
    rw [hcl.1, hh]
  have hX2k : (applyActs blank (clearF zero y.length)
      (applyActs blank (homeF sc y.length y.length) ts)).X2 = ts.X2 := by
    rw [hcl.2.1, hh]
  have hcw : y.length + 1 ≤ (clearWord zero y.length fw).length := by
    rw [clearWord_length]; exact hfw
  have hjob := jobActs_ok (one := one) D hleft hend
    (applyActs blank (clearF zero y.length)
      (applyActs blank (homeF sc y.length y.length) ts))
    (clearWord zero y.length fw) rd hcw hrd
    (applyActs_scratchBlank (noScratch_clearF _ _)
      (applyActs_scratchBlank (noScratch_homeF _ _ _) hSB))
    (by rw [hXk]; exact hX) (by rw [hX2k]; exact hX2)
    ⟨0, Nat.zero_le _, hcl.2.2⟩
  refine ⟨?_, ?_⟩
  · rw [List.length_append, List.length_append, homeF_length, clearF_length]
    have hC : Cbatch D * y.length = Cjob D * y.length + 4 * y.length := by
      simp only [Cbatch, Nat.add_mul]
    have := hjob.1
    omega
  · refine ⟨jobFlags y (D.dec y) one 8 (y.length + 1) y.length
      (clearWord zero y.length fw), ⟨?_, ?_⟩, ?_⟩
    · rw [jobFlags_length, clearWord_length]; exact hN
    · intro ℓ h1 h2
      have hz : (clearWord zero y.length fw)[ℓ]? = some zero :=
        clearWord_le zero y.length fw ℓ h2 (by omega)
      have hiff := flags_on_tape_eq_palPrefixFlagsGS (x := y) (dec := D.dec y)
        (one := one) (zero := zero) (k := 8) (fw := clearWord zero y.length fw)
        (by omega) hne hOK ℓ h1 h2 (by omega) hz
      have hpal := palPrefixFlagsGS_spec (x := y) (dec := D.dec y) (k := 8)
        (by omega) hOK ℓ h2
      rw [hiff, hpal]
      simp
    · rw [applyActs_append, applyActs_append]
      exact hjob.2

end BatchWord

/-! ## §10 ラウンド機械 -/

/-- 段幅 `S` の中で現れる最大の窓長。フラグテープの語はこの長さ ＋1 以上を保つ。 -/
def Lmax (S : ℕ) : ℕ := S + MiddleBorder.numJobs * MiddleBorder.gw S

/-- バッチ `j` の出力が最初に読まれる添字（＝そのバッチが完成するラウンド `relTime S (j+1)`
における `n - S`）。 -/
def rdOf (S j : ℕ) : ℕ := S / 2 + (j + 1) * MiddleBorder.gw S

theorem rdOf_eq (S j : ℕ) : MiddleBorder.relTime S (j + 1) - S = rdOf S j := by
  simp only [MiddleBorder.relTime, rdOf]
  omega

/-- 1 バッチを起動できるテープの条件。 -/
def BatchEntry (blank leftSym : Fin sc) (N : ℕ) (y : List (Fin sc)) (ts : OvTapes sc) :
    Prop :=
  (∃ i, i ≤ y.length ∧ Tape.SeqView blank ts.X (leftSym :: y) i) ∧
    (∃ i, i ≤ y.length ∧ Tape.SeqView blank ts.X2 (leftSym :: y) i) ∧
    (∃ ω, N ≤ ω.length ∧ ∃ i, i ≤ y.length ∧ Tape.SeqView blank ts.F ω i) ∧
    ScratchBlank blank ts

/-! ### 入力コピーの供給 -/

/-- 到着した記号 `a` を、まだ凍結していないコピー（添字 `j < i ≤ numJobs`）に追記する。 -/
def feed (blank a : Fin sc) (j : ℕ) (c : ℕ → TapeConfiguration sc) :
    ℕ → TapeConfiguration sc :=
  fun i => if j < i ∧ i ≤ MiddleBorder.numJobs then Tape.step blank (c i) a .right else c i

theorem feed_spec {blank a : Fin sc} {j : ℕ} {c : ℕ → TapeConfiguration sc}
    {v : List (Fin sc)} (h : ∀ i, j < i → i ≤ MiddleBorder.numJobs →
      InputCopy.FrontierView blank (c i) v) :
    ∀ i, j < i → i ≤ MiddleBorder.numJobs →
      InputCopy.FrontierView blank (feed blank a j c i) (v ++ [a]) := by
  intro i h1 h2
  simp only [feed, if_pos (⟨h1, h2⟩ : j < i ∧ i ≤ MiddleBorder.numJobs)]
  exact InputCopy.append_spec (h i h1 h2) a

/-- ラウンド `n` の終わりにコピーが保持している語。 -/
theorem feedWord_succ (w : List (Fin sc)) (blank : Fin sc) {S n : ℕ}
    (hS : S / 2 ≤ n) (hn : n < w.length) :
    ((w.take n).drop (S / 2)) ++ [w.getD n blank] = (w.take (n + 1)).drop (S / 2) := by
  have hget : w.getD n blank = w[n] := by
    rw [List.getD_eq_getElem _ _ hn]
  have hsucc : w.take (n + 1) = w.take n ++ [w[n]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hn]
    rfl
  have hlen : S / 2 ≤ (w.take n).length := by
    simp only [List.length_take]; omega
  rw [hget, hsucc, List.drop_append_of_le_length hlen]

/-! ### 退化した段（`S < 8`）の 1 ラウンド

窓は高々 `3 * S ≤ 21` 記号なので、`MiddleBorder.bstep` の素朴枝と同じく、
回文性は窓の決定可能な関数として直接求まる。テープ側では「定数個の走査ののち
判定結果を 1 セルに書く」だけでよく、動作数は `MiddleBorder` が数えている
`3 * S * S + 1` に収まる。 -/
def naiveWrite (blank one zero : Fin sc) (win : List (Fin sc)) (m : ℕ)
    (tp : TapeConfiguration sc) : TapeConfiguration sc :=
  Tape.step blank tp (if IsPal (win.take m) then one else zero) .stay

@[simp] theorem naiveWrite_read {blank one zero : Fin sc} {win : List (Fin sc)} {m : ℕ}
    {tp : TapeConfiguration sc} :
    Tape.read (naiveWrite blank one zero win m tp)
      = if IsPal (win.take m) then one else zero := rfl

/-! ### 状態と 1 ラウンド -/

/-- ラウンド機械の状態。 -/
structure MState (sc : ℕ) where
  /-- 段幅。 -/
  width : ℕ
  /-- これまでに解放されたバッチ数。 -/
  idx : ℕ
  /-- 次の解放ラウンド。 -/
  next : ℕ
  /-- 進行中のバッチ（残りの動作列と 6 本のテープ。`g.ts.F` が書き込み側フラグ）。 -/
  g : Grind sc
  /-- 読み出し側フラグテープ。 -/
  fout : TapeConfiguration sc
  /-- 入力コピー（`X` 用、バッチ番号で添字づけ）。 -/
  cp1 : ℕ → TapeConfiguration sc
  /-- 入力コピー（`X2` 用）。 -/
  cp2 : ℕ → TapeConfiguration sc

/-- **1 ラウンド**。`t` は到着済みの入力、`a` はこのラウンドに到着した記号。 -/
def mround (blank startSym endSym mark leftSym one zero : Fin sc)
    (D : DecompOnTapes sc blank startSym endSym mark)
    (t : List (Fin sc)) (a : Fin sc) (n : ℕ) (st : MState sc) : MState sc :=
  if st.width < 8 then
    let win := (t.drop (st.width / 2)).take (3 * st.width)
    { st with fout := naiveWrite blank one zero win (n - st.width) st.fout }
  else if n = st.next ∧ st.idx < MiddleBorder.numJobs then
    let j := st.idx + 1
    let c1 := feed blank a st.idx st.cp1
    let c2 := feed blank a st.idx st.cp2
    let y := (t.drop (st.width / 2)).take (st.width + j * MiddleBorder.gw st.width)
    let ts' : OvTapes sc :=
      { P := st.g.ts.P, X := Tape.step blank (c1 j) blank .left, Cnt := st.g.ts.Cnt,
        U := st.g.ts.U, X2 := Tape.step blank (c2 j) blank .left, F := st.fout,
        S1 := st.g.ts.S1, S2 := st.g.ts.S2, S3 := st.g.ts.S3, S4 := st.g.ts.S4,
        S5 := st.g.ts.S5, S6 := st.g.ts.S6, S7 := st.g.ts.S7, S8 := st.g.ts.S8,
        S9 := st.g.ts.S9 }
    { width := st.width, idx := j, next := n + MiddleBorder.gw st.width,
      g := ⟨batchActs blank startSym endSym mark leftSym one zero D y
              (rdOf st.width j) ts', ts'⟩,
      fout := st.g.ts.F, cp1 := c1, cp2 := c2 }
  else
    let fo : TapeConfiguration sc :=
      if st.width < n ∧ 2 ≤ st.idx then Tape.step blank st.fout st.fout.focus .right
      else st.fout
    let gg : Grind sc := gstep blank (rateM D) st.g
    let d1 : ℕ → TapeConfiguration sc := feed blank a st.idx st.cp1
    let d2 : ℕ → TapeConfiguration sc := feed blank a st.idx st.cp2
    { width := st.width, idx := st.idx, next := st.next, g := gg, fout := fo,
      cp1 := d1, cp2 := d2 }

/-- 1 ラウンドの費用（実際に流した動作の個数）。 -/
def mcost (D : DecompOnTapes sc blank startSym endSym mark) (n : ℕ) (st : MState sc) : ℕ :=
  if st.width < 8 then 3 * st.width * st.width + 1
  else if n = st.next ∧ st.idx < MiddleBorder.numJobs then 2 * MiddleBorder.numJobs + 2
  else 2 * MiddleBorder.numJobs + gcost (rateM D) st.g + 1

/-- 1 ラウンドの費用上界。 -/
def CmT' (D : DecompOnTapes sc blank startSym endSym mark) : ℕ := rateM D + 148

theorem mcost_le (D : DecompOnTapes sc blank startSym endSym mark) (n : ℕ)
    (st : MState sc) : mcost D n st ≤ CmT' D := by
  simp only [mcost, CmT']
  split_ifs with h1 h2
  · have : st.width ≤ 7 := by omega
    have h3 : 3 * st.width * st.width ≤ 3 * 7 * 7 :=
      calc 3 * st.width * st.width ≤ 3 * 7 * st.width :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 3 this)
        _ ≤ 3 * 7 * 7 := Nat.mul_le_mul_left _ this
    omega
  · simp only [MiddleBorder.numJobs]; omega
  · have := gcost_le (rateM D) st.g
    simp only [MiddleBorder.numJobs]
    omega

theorem gsteps_succ (blank : Fin sc) (r : ℕ) :
    ∀ (m : ℕ) (g : Grind sc),
      gsteps blank r (m + 1) g = gstep blank r (gsteps blank r m g) := by
  intro m
  induction m with
  | zero => intro g; rfl
  | succ m ih => intro g; rw [gsteps, ih, ← gsteps]

theorem gstep_nil (blank : Fin sc) (r : ℕ) (ts : OvTapes sc) :
    gstep blank r ⟨[], ts⟩ = ⟨[], ts⟩ := by simp [gstep]

/-- **不変条件**：テープ機械の状態が `MiddleBorder.bstate` を符号化していること。 -/
structure MEncodes (blank startSym endSym mark leftSym one zero : Fin sc)
    (D : DecompOnTapes sc blank startSym endSym mark)
    (w : List (Fin sc)) (S n : ℕ) (st : MState sc) : Prop where
  width_eq : st.width = S
  idx_eq : st.idx = (MiddleBorder.bstate w S n).idx
  next_eq : st.next = (MiddleBorder.bstate w S n).next
  next_rel : 8 ≤ S → st.next = MiddleBorder.relTime S (st.idx + 1)
  rel_le : 8 ≤ S → 1 ≤ st.idx → st.next ≤ n + MiddleBorder.gw S
  copy1 : 8 ≤ S → ∀ i, st.idx < i → i ≤ MiddleBorder.numJobs →
    InputCopy.FrontierView blank (st.cp1 i) (leftSym :: ((w.take n).drop (S / 2)))
  copy2 : 8 ≤ S → ∀ i, st.idx < i → i ≤ MiddleBorder.numJobs →
    InputCopy.FrontierView blank (st.cp2 i) (leftSym :: ((w.take n).drop (S / 2)))
  job : 8 ≤ S → n < 4 * S → 1 ≤ st.idx →
    ∃ ts₀ : OvTapes sc,
      st.g = gsteps blank (rateM D) (n + MiddleBorder.gw S - st.next)
        ⟨batchActs blank startSym endSym mark leftSym one zero D
          (MiddleBorder.Wnd w S st.idx) (rdOf S st.idx) ts₀, ts₀⟩ ∧
      BatchEntry blank leftSym (Lmax S + 1) (MiddleBorder.Wnd w S st.idx) ts₀
  gwf : 8 ≤ S → n < 4 * S → st.idx = 0 →
    st.g.rem = [] ∧ (∃ ω, Lmax S + 1 ≤ ω.length ∧ Tape.SeqView blank st.g.ts.F ω 0) ∧
      ScratchBlank blank st.g.ts
  foutWF : 8 ≤ S → n < 4 * S → st.idx ≤ 1 →
    ∃ ω, Lmax S + 1 ≤ ω.length ∧ Tape.SeqView blank st.fout ω 0
  out : 8 ≤ S → n < 4 * S → 2 ≤ st.idx →
    ∃ ω, FlagWordOK one (Lmax S + 1) (MiddleBorder.Wnd w S (st.idx - 1)) ω ∧
      Tape.SeqView blank st.fout ω (n - S)
  outNaive : S < 8 → S / 2 < n → n < 4 * S →
    Tape.read st.fout = (if IsPal ((w.drop (S / 2)).take (n - S)) then one else zero)

/-! ### 補助的な評価 -/

theorem three_S_le_Lmax {S : ℕ} (hS : 8 ≤ S) : 3 * S ≤ Lmax S := by
  simp only [Lmax, MiddleBorder.numJobs, MiddleBorder.gw]
  omega

theorem gw_two {S : ℕ} (hS : 8 ≤ S) : 2 ≤ MiddleBorder.gw S := by
  simp only [MiddleBorder.gw]; omega

/-- ラウンド `n = relTime S p` に届いている入力コピーの中身はちょうど窓 `Wnd w S p`。 -/
theorem fed_eq_wnd (w : List (Fin sc)) {S p n : ℕ} (hn : n = MiddleBorder.relTime S p) :
    (w.take n).drop (S / 2) = MiddleBorder.Wnd w S p := by
  rw [List.drop_take]
  simp only [MiddleBorder.Wnd]
  congr 1
  simp only [MiddleBorder.relTime] at hn
  omega

theorem wnd_length_eq (w : List (Fin sc)) {S p : ℕ}
    (hw : MiddleBorder.relTime S p ≤ w.length) :
    (MiddleBorder.Wnd w S p).length = S + p * MiddleBorder.gw S := by
  simp only [MiddleBorder.Wnd, List.length_take, List.length_drop]
  simp only [MiddleBorder.relTime] at hw
  omega

/-- 素朴枝の窓の切り出し。 -/
theorem naive_window_take (w : List (Fin sc)) {S n m : ℕ} (hm : m ≤ 3 * S)
    (hm2 : m + S / 2 ≤ n) :
    ((((w.take n).drop (S / 2)).take (3 * S)).take m) = (w.drop (S / 2)).take m := by
  rw [List.drop_take, List.take_take, List.take_take]
  congr 1
  omega

/-! ### 1 ラウンドの正当性 -/

section Round

variable {blank startSym endSym mark leftSym one zero : Fin sc}

theorem mround_encodes_small (D : DecompOnTapes sc blank startSym endSym mark)
    {w : List (Fin sc)} {S n : ℕ} {st : MState sc}
    (hsmall : S < 8) (hn : S / 2 ≤ n)
    (h : MEncodes blank startSym endSym mark leftSym one zero D w S n st) :
    MEncodes blank startSym endSym mark leftSym one zero D w S (n + 1)
      (mround blank startSym endSym mark leftSym one zero D
        (w.take (n + 1)) (w.getD n blank) (n + 1) st) := by
  have hbs : MiddleBorder.bstate w S (n + 1)
      = MiddleBorder.bstep (w.take (n + 1)) (n + 1) (MiddleBorder.bstate w S n) :=
    MiddleBorder.bstate_succ (by omega)
  have hbw : (MiddleBorder.bstate w S n).width = S := MiddleBorder.bstate_width w S n
  have hw8 : st.width < 8 := by rw [h.width_eq]; exact hsmall
  have hbstep : MiddleBorder.bstate w S (n + 1)
      = { MiddleBorder.bstate w S n with
          out := MiddleBorder.naiveFlags
            (((w.take (n + 1)).drop ((MiddleBorder.bstate w S n).width / 2)).take
              (3 * (MiddleBorder.bstate w S n).width)) } := by
    rw [hbs]
    simp only [MiddleBorder.bstep, hbw, if_pos hsmall]
  simp only [mround, if_pos hw8]
  refine ⟨h.width_eq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show st.idx = _
    rw [hbstep]; exact h.idx_eq
  · show st.next = _
    rw [hbstep]; exact h.next_eq
  · exact h.next_rel
  · intro h8; omega
  · intro h8; omega
  · intro h8; omega
  · intro h8; omega
  · intro h8; omega
  · intro h8; omega
  · intro h8; omega
  · intro _ _ h4
    show Tape.read (naiveWrite blank one zero
      (((w.take (n + 1)).drop (st.width / 2)).take (3 * st.width)) (n + 1 - st.width)
      st.fout) = _
    rw [naiveWrite_read, h.width_eq,
      naive_window_take w (m := n + 1 - S) (by omega) (by omega)]

theorem mround_encodes_release (D : DecompOnTapes sc blank startSym endSym mark)
    {w : List (Fin sc)} {S n : ℕ} {st : MState sc}
    (hne : one ≠ zero) (hleft : leftSym ∉ w) (hend : endSym ∉ w)
    (hbig : 8 ≤ S) (hev : 2 * (S / 2) = S)
    (hn : S / 2 ≤ n) (hw : n + 1 ≤ w.length)
    (hrel : n + 1 = st.next ∧ st.idx < MiddleBorder.numJobs)
    (h : MEncodes blank startSym endSym mark leftSym one zero D w S n st) :
    MEncodes blank startSym endSym mark leftSym one zero D w S (n + 1)
      (mround blank startSym endSym mark leftSym one zero D
        (w.take (n + 1)) (w.getD n blank) (n + 1) st) := by
  have hg2 : 2 ≤ MiddleBorder.gw S := gw_two hbig
  have hbs : MiddleBorder.bstate w S (n + 1)
      = MiddleBorder.bstep (w.take (n + 1)) (n + 1) (MiddleBorder.bstate w S n) :=
    MiddleBorder.bstate_succ (by omega)
  have hbw : (MiddleBorder.bstate w S n).width = S := MiddleBorder.bstate_width w S n
  have hcond : n + 1 = (MiddleBorder.bstate w S n).next ∧
      (MiddleBorder.bstate w S n).idx < MiddleBorder.numJobs := by
    rw [← h.next_eq, ← h.idx_eq]; exact hrel
  have hbi : (MiddleBorder.bstate w S (n + 1)).idx = st.idx + 1 := by
    rw [hbs]
    simp only [MiddleBorder.bstep, hbw, if_neg (show ¬ S < 8 by omega), if_pos hcond]
    rw [h.idx_eq]
  have hbn : (MiddleBorder.bstate w S (n + 1)).next = n + 1 + MiddleBorder.gw S := by
    rw [hbs]
    simp only [MiddleBorder.bstep, hbw, if_neg (show ¬ S < 8 by omega), if_pos hcond]
  -- 解放ラウンドの時刻
  have hnext : st.next = MiddleBorder.relTime S (st.idx + 1) := h.next_rel hbig
  have hn1 : n + 1 = MiddleBorder.relTime S (st.idx + 1) := by rw [hrel.1, hnext]
  have hfed : (w.take (n + 1)).drop (S / 2) = MiddleBorder.Wnd w S (st.idx + 1) :=
    fed_eq_wnd w hn1
  have hylen : (MiddleBorder.Wnd w S (st.idx + 1)).length
      = S + (st.idx + 1) * MiddleBorder.gw S := wnd_length_eq w (by omega)
  have hy : ((w.take (n + 1)).drop (S / 2)).take (S + (st.idx + 1) * MiddleBorder.gw S)
      = MiddleBorder.Wnd w S (st.idx + 1) := by
    rw [hfed]
    simp only [MiddleBorder.Wnd, List.take_take]
    congr 1
    omega
  have hfeedw : ((w.take n).drop (S / 2)) ++ [w.getD n blank] = (w.take (n + 1)).drop (S / 2) :=
    feedWord_succ w blank hn (by omega)
  have hw8 : ¬ (st.width < 8) := by rw [h.width_eq]; omega
  have hrel' : n + 1 = st.next ∧ st.idx < MiddleBorder.numJobs := hrel
  simp only [mround, h.width_eq, if_neg (show ¬ (S < 8) by omega), if_pos hrel']
  have hnum : st.idx + 1 ≤ MiddleBorder.numJobs := by
    have := hrel.2; omega
  have hcopy1 : ∀ i, st.idx < i → i ≤ MiddleBorder.numJobs →
      InputCopy.FrontierView blank (feed blank (w.getD n blank) st.idx st.cp1 i)
        (leftSym :: ((w.take (n + 1)).drop (S / 2))) := by
    intro i h1 h2
    have := feed_spec (a := w.getD n blank) (h.copy1 hbig) i h1 h2
    rwa [List.cons_append, hfeedw] at this
  have hcopy2 : ∀ i, st.idx < i → i ≤ MiddleBorder.numJobs →
      InputCopy.FrontierView blank (feed blank (w.getD n blank) st.idx st.cp2 i)
        (leftSym :: ((w.take (n + 1)).drop (S / 2))) := by
    intro i h1 h2
    have := feed_spec (a := w.getD n blank) (h.copy2 hbig) i h1 h2
    rwa [List.cons_append, hfeedw] at this
  have hXsv : Tape.SeqView blank
      (Tape.step blank (feed blank (w.getD n blank) st.idx st.cp1 (st.idx + 1)) blank .left)
      (leftSym :: MiddleBorder.Wnd w S (st.idx + 1))
      (MiddleBorder.Wnd w S (st.idx + 1)).length := by
    have hfv := hcopy1 (st.idx + 1) (by omega) hnum
    rw [hfed] at hfv
    have := InputCopy.toSeqView hfv (by simp)
    simpa using this
  have hX2sv : Tape.SeqView blank
      (Tape.step blank (feed blank (w.getD n blank) st.idx st.cp2 (st.idx + 1)) blank .left)
      (leftSym :: MiddleBorder.Wnd w S (st.idx + 1))
      (MiddleBorder.Wnd w S (st.idx + 1)).length := by
    have hfv := hcopy2 (st.idx + 1) (by omega) hnum
    rw [hfed] at hfv
    have := InputCopy.toSeqView hfv (by simp)
    simpa using this
  -- 新しいバッチの `F` テープ（＝古い読み出し側）
  have hFentry : n + 1 < 4 * S → ∃ ω, Lmax S + 1 ≤ ω.length ∧
      ∃ i, i ≤ (MiddleBorder.Wnd w S (st.idx + 1)).length ∧
        Tape.SeqView blank st.fout ω i := by
    intro h4
    rcases Nat.lt_or_ge st.idx 2 with hlt | hge
    · obtain ⟨ω, hω, hsv⟩ := h.foutWF hbig (by omega) (by omega)
      exact ⟨ω, hω, 0, Nat.zero_le _, hsv⟩
    · obtain ⟨ω, hFW, hsv⟩ := h.out hbig (by omega) hge
      refine ⟨ω, hFW.1, n - S, ?_, hsv⟩
      rw [hylen]
      simp only [MiddleBorder.relTime] at hn1
      omega
  -- 作業テープ：解放時点で前のバッチは挽き終わっているので空白
  have hgsb : n + 1 < 4 * S → ScratchBlank blank st.g.ts := by
    intro h4
    rcases Nat.eq_zero_or_pos st.idx with h0 | hp1
    · exact (h.gwf hbig (by omega) h0).2.2
    · have hple : st.idx ≤ MiddleBorder.numJobs := by have := hrel.2; omega
      obtain ⟨ts₀, hgeq, hBE⟩ := h.job hbig (by omega) hp1
      obtain ⟨hXe, hX2e, ⟨ωF, hωF, iF, hiF, hsvF⟩, hSB0⟩ := hBE
      have hrelle : MiddleBorder.relTime S st.idx ≤ w.length := by
        have := MiddleBorder.relTime_succ S st.idx
        omega
      have hlenW : (MiddleBorder.Wnd w S st.idx).length = S + st.idx * MiddleBorder.gw S :=
        wnd_length_eq w hrelle
      have hrd : rdOf S st.idx ≤ (MiddleBorder.Wnd w S st.idx).length := by
        rw [hlenW]
        have hexp : (st.idx + 1) * MiddleBorder.gw S
            = st.idx * MiddleBorder.gw S + MiddleBorder.gw S := by ring
        have hhalf : S / 2 + MiddleBorder.gw S ≤ S := by simp only [MiddleBorder.gw]; omega
        simp only [rdOf, hexp]
        omega
      have hWmax : (MiddleBorder.Wnd w S st.idx).length ≤ Lmax S := by
        rw [hlenW]
        have hmm : st.idx * MiddleBorder.gw S ≤ MiddleBorder.numJobs * MiddleBorder.gw S :=
          Nat.mul_le_mul_right _ hple
        simp only [Lmax]
        omega
      have hbatch := batchActs_word (one := one) (zero := zero) D hne
        (fun hc => hleft (mem_wnd hc)) (fun hc => hend (mem_wnd hc))
        ts₀ ωF (rdOf S st.idx) (Lmax S + 1) (by omega) hωF hrd hSB0 hXe hX2e ⟨iF, hiF, hsvF⟩
      have hcount : n + MiddleBorder.gw S - st.next = MiddleBorder.gw S - 1 := by omega
      have hdone := batch_complete D hbig hev
        (show (MiddleBorder.Wnd w S st.idx).length ≤ 5 * S from wnd_length_le w hbig hple)
        (batchActs blank startSym endSym mark leftSym one zero D (MiddleBorder.Wnd w S st.idx)
          (rdOf S st.idx) ts₀) ts₀ hbatch.1
      rw [hcount, hdone] at hgeq
      rw [hgeq]
      exact batchActs_scratch D (MiddleBorder.Wnd w S st.idx) (rdOf S st.idx) ts₀ hSB0
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show st.idx + 1 = _
    rw [hbi]
  · show n + 1 + MiddleBorder.gw S = _
    rw [hbn]
  · intro _
    show n + 1 + MiddleBorder.gw S = MiddleBorder.relTime S (st.idx + 1 + 1)
    rw [MiddleBorder.relTime_succ, ← hn1]
  · intro _ _
    exact Nat.le_refl _
  · intro _ i h1 h2; exact hcopy1 i (Nat.lt_of_succ_lt h1) h2
  · intro _ i h1 h2; exact hcopy2 i (Nat.lt_of_succ_lt h1) h2
  · intro _ hjob4 _
    obtain ⟨ts', hts'⟩ : ∃ z : OvTapes sc, z = OvTapes.mk st.g.ts.P (Tape.step blank (feed blank (w.getD n blank) st.idx st.cp1 (st.idx + 1)) blank .left) st.g.ts.Cnt st.g.ts.U (Tape.step blank (feed blank (w.getD n blank) st.idx st.cp2 (st.idx + 1)) blank .left) st.fout st.g.ts.S1 st.g.ts.S2 st.g.ts.S3 st.g.ts.S4 st.g.ts.S5 st.g.ts.S6 st.g.ts.S7 st.g.ts.S8 st.g.ts.S9 := ⟨_, rfl⟩
    refine ⟨ts', ?_, ?_⟩
    · rw [hy, Nat.sub_self, hts']
      rfl
    · refine ⟨⟨_, le_rfl, ?_⟩, ⟨_, le_rfl, ?_⟩, ⟨?_, ?_⟩⟩
      · rw [hts']; exact hXsv
      · rw [hts']; exact hX2sv
      · rw [hts']; exact hFentry hjob4
      · rw [hts']
        have hg := hgsb hjob4
        exact ⟨hg.s1, hg.s2, hg.s3, hg.s4, hg.s5, hg.s6, hg.s7, hg.s8, hg.s9⟩
  · intro _ _ h0
    exact absurd h0 (Nat.succ_ne_zero _)
  · intro _ h4 h1
    have h1' : st.idx + 1 ≤ 1 := h1
    have h4' : n + 1 < 4 * S := h4
    exact (h.gwf hbig (by omega) (by omega)).2.1
  · intro _ h4 h2
    have h4' : n + 1 < 4 * S := h4
    have hp1 : 1 ≤ st.idx := by
      have h2' : 2 ≤ st.idx + 1 := h2
      omega
    have hple : st.idx ≤ MiddleBorder.numJobs := by have := hrel.2; omega
    obtain ⟨ts₀, hgeq, hBE⟩ := h.job hbig (by omega) hp1
    obtain ⟨hXe, hX2e, ⟨ωF, hωF, iF, hiF, hsvF⟩, hSB0⟩ := hBE
    have hrelle : MiddleBorder.relTime S st.idx ≤ w.length := by
      have := MiddleBorder.relTime_succ S st.idx
      omega
    have hlenW : (MiddleBorder.Wnd w S st.idx).length = S + st.idx * MiddleBorder.gw S :=
      wnd_length_eq w hrelle
    have hWmax : (MiddleBorder.Wnd w S st.idx).length ≤ Lmax S := by
      rw [hlenW]
      have hmm : st.idx * MiddleBorder.gw S ≤ MiddleBorder.numJobs * MiddleBorder.gw S :=
        Nat.mul_le_mul_right _ hple
      simp only [Lmax]
      omega
    have hrd : rdOf S st.idx ≤ (MiddleBorder.Wnd w S st.idx).length := by
      rw [hlenW]
      have hexp : (st.idx + 1) * MiddleBorder.gw S
          = st.idx * MiddleBorder.gw S + MiddleBorder.gw S := by ring
      have hhalf : S / 2 + MiddleBorder.gw S ≤ S := by simp only [MiddleBorder.gw]; omega
      simp only [rdOf, hexp]
      omega
    have hbatch := batchActs_word (one := one) (zero := zero) D hne
      (fun hc => hleft (mem_wnd hc)) (fun hc => hend (mem_wnd hc))
      ts₀ ωF (rdOf S st.idx) (Lmax S + 1) (by omega) hωF hrd hSB0 hXe hX2e ⟨iF, hiF, hsvF⟩
    have hcount : n + MiddleBorder.gw S - st.next = MiddleBorder.gw S - 1 := by omega
    have hdone := batch_complete D hbig hev
      (show (MiddleBorder.Wnd w S st.idx).length ≤ 5 * S from wnd_length_le w hbig hple)
      (batchActs blank startSym endSym mark leftSym one zero D (MiddleBorder.Wnd w S st.idx)
        (rdOf S st.idx) ts₀) ts₀ hbatch.1
    rw [hcount, hdone] at hgeq
    obtain ⟨ω, hFW, hsv⟩ := hbatch.2
    refine ⟨ω, ?_, ?_⟩
    · show FlagWordOK one (Lmax S + 1) (MiddleBorder.Wnd w S (st.idx + 1 - 1)) ω
      rw [Nat.add_sub_cancel]
      exact hFW
    · show Tape.SeqView blank st.g.ts.F ω (n + 1 - S)
      rw [hgeq]
      have hidx : n + 1 - S = rdOf S st.idx := by rw [← rdOf_eq S st.idx, hn1]
      rw [hidx]
      exact hsv
  · intro hc; omega


theorem mround_encodes_grind (D : DecompOnTapes sc blank startSym endSym mark)
    {w : List (Fin sc)} {S n : ℕ} {st : MState sc}
    (hbig : 8 ≤ S) (hn : S / 2 ≤ n) (hw : n + 1 ≤ w.length)
    (hnrel : ¬ (n + 1 = st.next ∧ st.idx < MiddleBorder.numJobs))
    (h : MEncodes blank startSym endSym mark leftSym one zero D w S n st) :
    MEncodes blank startSym endSym mark leftSym one zero D w S (n + 1)
      (mround blank startSym endSym mark leftSym one zero D
        (w.take (n + 1)) (w.getD n blank) (n + 1) st) := by
  have hbs : MiddleBorder.bstate w S (n + 1)
      = MiddleBorder.bstep (w.take (n + 1)) (n + 1) (MiddleBorder.bstate w S n) :=
    MiddleBorder.bstate_succ (by omega)
  have hbw : (MiddleBorder.bstate w S n).width = S := MiddleBorder.bstate_width w S n
  have hcond : ¬ (n + 1 = (MiddleBorder.bstate w S n).next ∧
      (MiddleBorder.bstate w S n).idx < MiddleBorder.numJobs) := by
    rw [← h.next_eq, ← h.idx_eq]; exact hnrel
  have hbi : (MiddleBorder.bstate w S (n + 1)).idx = st.idx := by
    rw [hbs]
    simp only [MiddleBorder.bstep, hbw, if_neg (show ¬ S < 8 by omega), if_neg hcond]
    rw [h.idx_eq]
  have hbn : (MiddleBorder.bstate w S (n + 1)).next = st.next := by
    rw [hbs]
    simp only [MiddleBorder.bstep, hbw, if_neg (show ¬ S < 8 by omega), if_neg hcond]
    rw [h.next_eq]
  have hfeedw : ((w.take n).drop (S / 2)) ++ [w.getD n blank] = (w.take (n + 1)).drop (S / 2) :=
    feedWord_succ w blank hn (by omega)
  have hcopy1 : ∀ i, st.idx < i → i ≤ MiddleBorder.numJobs →
      InputCopy.FrontierView blank (feed blank (w.getD n blank) st.idx st.cp1 i)
        (leftSym :: ((w.take (n + 1)).drop (S / 2))) := by
    intro i h1 h2
    have := feed_spec (a := w.getD n blank) (h.copy1 hbig) i h1 h2
    rwa [List.cons_append, hfeedw] at this
  have hcopy2 : ∀ i, st.idx < i → i ≤ MiddleBorder.numJobs →
      InputCopy.FrontierView blank (feed blank (w.getD n blank) st.idx st.cp2 i)
        (leftSym :: ((w.take (n + 1)).drop (S / 2))) := by
    intro i h1 h2
    have := feed_spec (a := w.getD n blank) (h.copy2 hbig) i h1 h2
    rwa [List.cons_append, hfeedw] at this
  simp only [mround, h.width_eq, if_neg (show ¬ (S < 8) by omega), if_neg hnrel]
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show st.idx = _
    rw [hbi]
  · show st.next = _
    rw [hbn]
  · exact h.next_rel
  · intro h8 h1
    have hr := h.rel_le h8 h1
    show st.next ≤ n + 1 + MiddleBorder.gw S
    omega
  · intro _ i h1 h2; exact hcopy1 i h1 h2
  · intro _ i h1 h2; exact hcopy2 i h1 h2
  · intro _ h4 h1
    obtain ⟨ts₀, hgeq, hBE⟩ := h.job hbig (by omega) h1
    refine ⟨ts₀, ?_, hBE⟩
    have hr := h.rel_le hbig h1
    show gstep blank (rateM D) st.g
        = gsteps blank (rateM D) (n + 1 + MiddleBorder.gw S - st.next)
          ⟨batchActs blank startSym endSym mark leftSym one zero D
            (MiddleBorder.Wnd w S st.idx) (rdOf S st.idx) ts₀, ts₀⟩
    rw [hgeq, ← gsteps_succ]
    congr 1
    omega
  · intro _ h4 h0
    obtain ⟨hrem, ⟨ω, hω, hsv⟩, hsc⟩ := h.gwf hbig (by omega) h0
    refine ⟨?_, ⟨ω, hω, ?_⟩, ?_⟩
    · show st.g.rem.drop (rateM D) = []
      rw [hrem]; simp
    · show Tape.SeqView blank (applyActs blank (st.g.rem.take (rateM D)) st.g.ts).F ω 0
      rw [hrem]
      simpa using hsv
    · show ScratchBlank blank (applyActs blank (st.g.rem.take (rateM D)) st.g.ts)
      rw [hrem]
      simpa using hsc
  · intro _ h4 h1
    have h1' : st.idx ≤ 1 := h1
    rw [if_neg (show ¬ (S < n + 1 ∧ 2 ≤ st.idx) by omega)]
    exact h.foutWF hbig (by omega) h1'
  · intro _ h4 h2
    have h2' : 2 ≤ st.idx := h2
    obtain ⟨ω, hFW, hsv⟩ := h.out hbig (by omega) h2'
    have hLm := three_S_le_Lmax hbig
    refine ⟨ω, hFW, ?_⟩
    by_cases hSn : S < n + 1
    · rw [if_pos (⟨hSn, h2'⟩ : S < n + 1 ∧ 2 ≤ st.idx)]
      have hlt : n - S + 1 < ω.length := by
        have hw1 := hFW.1
        omega
      have := Tape.seq_move_right hsv hlt
      have heq : n - S + 1 = n + 1 - S := by omega
      rwa [heq] at this
    · rw [if_neg (show ¬ (S < n + 1 ∧ 2 ≤ st.idx) by omega)]
      have heq : n + 1 - S = n - S := by omega
      rw [heq]
      exact hsv
  · intro hc; omega

/-- **1 ラウンドの主定理**：不変条件はラウンドをまたいで保たれる。 -/
theorem mround_encodes (D : DecompOnTapes sc blank startSym endSym mark)
    {w : List (Fin sc)} {S n : ℕ} {st : MState sc}
    (hne : one ≠ zero) (hleft : leftSym ∉ w) (hend : endSym ∉ w)
    (hev : 2 * (S / 2) = S)
    (hn : S / 2 ≤ n) (hw : n + 1 ≤ w.length)
    (h : MEncodes blank startSym endSym mark leftSym one zero D w S n st) :
    MEncodes blank startSym endSym mark leftSym one zero D w S (n + 1)
      (mround blank startSym endSym mark leftSym one zero D
        (w.take (n + 1)) (w.getD n blank) (n + 1) st) := by
  by_cases hsmall : S < 8
  · exact mround_encodes_small D hsmall hn h
  · by_cases hrel : n + 1 = st.next ∧ st.idx < MiddleBorder.numJobs
    · exact mround_encodes_release D hne hleft hend (by omega) hev hn hw hrel h
    · exact mround_encodes_grind D (by omega) hn hw hrel h

/-- **1 ラウンドの費用**は `CmT' D = rateM D + 148` 以下。 -/
theorem mround_cost (D : DecompOnTapes sc blank startSym endSym mark) (n : ℕ)
    (st : MState sc) : mcost D n st ≤ CmT' D :=
  mcost_le D n st

/-! ### ラウンドの反復 -/

/-- ラウンド `n` 終了時のテープ機械の状態（`MiddleImpl.runToH` と同じ刻み）。 -/
def mstate (blank startSym endSym mark leftSym one zero : Fin sc)
    (D : DecompOnTapes sc blank startSym endSym mark)
    (w : List (Fin sc)) (S : ℕ) (init : MState sc) : ℕ → MState sc
  | 0 => init
  | n + 1 =>
      if n + 1 ≤ S / 2 then init
      else mround blank startSym endSym mark leftSym one zero D
        (w.take (n + 1)) (w.getD n blank) (n + 1)
        (mstate blank startSym endSym mark leftSym one zero D w S init n)

/-- 初期状態。 -/
def minit (S : ℕ) (g0 : Grind sc) (fo : TapeConfiguration sc)
    (c1 c2 : ℕ → TapeConfiguration sc) : MState sc :=
  ⟨S, 0, MiddleBorder.relTime S 1, g0, fo, c1, c2⟩

theorem minit_encodes (D : DecompOnTapes sc blank startSym endSym mark)
    {w : List (Fin sc)} {S : ℕ} {g0 : Grind sc} {fo : TapeConfiguration sc}
    {c1 c2 : ℕ → TapeConfiguration sc}
    (hc1 : ∀ i, InputCopy.FrontierView blank (c1 i) [leftSym])
    (hc2 : ∀ i, InputCopy.FrontierView blank (c2 i) [leftSym])
    (hrem : g0.rem = [])
    (hgF : ∃ ω, Lmax S + 1 ≤ ω.length ∧ Tape.SeqView blank g0.ts.F ω 0)
    (hgsc : ScratchBlank blank g0.ts)
    (hfo : ∃ ω, Lmax S + 1 ≤ ω.length ∧ Tape.SeqView blank fo ω 0) :
    ∀ m, m ≤ S / 2 →
      MEncodes blank startSym endSym mark leftSym one zero D w S m (minit S g0 fo c1 c2) := by
  intro m hm
  have hb : MiddleBorder.bstate w S m = ⟨S, 0, MiddleBorder.relTime S 1, [], 0, []⟩ :=
    MiddleBorder.bstate_init hm
  have hnil : (w.take m).drop (S / 2) = [] := by
    refine List.drop_eq_nil_of_le ?_
    simp only [List.length_take]
    omega
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (0 : ℕ) = (MiddleBorder.bstate w S m).idx
    rw [hb]
  · show MiddleBorder.relTime S 1 = (MiddleBorder.bstate w S m).next
    rw [hb]
  · intro _; rfl
  · intro _ h1; exact absurd (show 1 ≤ 0 from h1) (by omega)
  · intro _ i _ _; rw [hnil]; exact hc1 i
  · intro _ i _ _; rw [hnil]; exact hc2 i
  · intro _ _ h1; exact absurd (show 1 ≤ 0 from h1) (by omega)
  · intro _ _ _; exact ⟨hrem, hgF, hgsc⟩
  · intro _ _ _; exact hfo
  · intro _ _ h2; exact absurd (show 2 ≤ 0 from h2) (by omega)
  · intro _ h2 _; exact absurd h2 (by omega)

theorem mstate_encodes (D : DecompOnTapes sc blank startSym endSym mark)
    {w : List (Fin sc)} {S : ℕ} {init : MState sc}
    (hne : one ≠ zero) (hleft : leftSym ∉ w) (hend : endSym ∉ w)
    (hev : 2 * (S / 2) = S)
    (hinit : ∀ m, m ≤ S / 2 →
      MEncodes blank startSym endSym mark leftSym one zero D w S m init) :
    ∀ n, n ≤ w.length →
      MEncodes blank startSym endSym mark leftSym one zero D w S n
        (mstate blank startSym endSym mark leftSym one zero D w S init n) := by
  intro n
  induction n with
  | zero => intro _; exact hinit 0 (Nat.zero_le _)
  | succ n ih =>
    intro hw
    by_cases hle : n + 1 ≤ S / 2
    · rw [mstate, if_pos hle]; exact hinit (n + 1) hle
    · rw [mstate, if_neg hle]
      exact mround_encodes D hne hleft hend hev (by omega) hw (ih (by omega))

end Round

/-! ## §11 主定理：読み出し側の記号は `borderMiddle` のフラグに一致する -/

section Read

variable {blank startSym endSym mark leftSym one zero : Fin sc}

/-- **主定理**：ラウンド `n ∈ [2S, 4S)` に読み出し側フラグテープで読める記号が `one` で
あることは、`MiddleBorder.borderMiddle` がそのラウンドに出すフラグが `true` であること
（＝ 中央部 `(w.drop (S/2)).take (n - S)` が回文であること）と同値。 -/
theorem middle_flag_read (D : DecompOnTapes sc blank startSym endSym mark)
    {w : List (Fin sc)} {S : ℕ} {init : MState sc}
    (hne : one ≠ zero) (hleft : leftSym ∉ w) (hend : endSym ∉ w)
    (hDec : MiddleBorder.DecOK (Fin sc)) (hev : 2 * (S / 2) = S) (hS2 : 2 ≤ S)
    (hinit : ∀ m, m ≤ S / 2 →
      MEncodes blank startSym endSym mark leftSym one zero D w S m init)
    (n : ℕ) (h1 : 2 * S ≤ n) (h2 : n < 4 * S) (hw : n ≤ w.length) :
    (Tape.read (mstate blank startSym endSym mark leftSym one zero D w S init n).fout = one)
      ↔ (MiddleBorder.borderMiddle (Fin sc)).flag
          ((MiddleBorder.borderMiddle (Fin sc)).runToH w S n) n = true := by
  have hM := mstate_encodes D hne hleft hend hev hinit n hw
  have hspec := (MiddleBorder.borderMiddle_spec hDec).correct w S n hS2 hev h1 h2 hw
  rw [hspec]
  rcases Nat.lt_or_ge S 8 with hsmall | hbig
  · rw [hM.outNaive hsmall (by omega) h2]
    by_cases hp : IsPal ((w.drop (S / 2)).take (n - S))
    · rw [if_pos hp]; exact ⟨fun _ => hp, fun _ => rfl⟩
    · rw [if_neg hp]
      simp only [hp, iff_false]
      exact fun hc => hne hc.symm
  · obtain ⟨p, i, hp2, hple, hn, hi, hcov⟩ := MiddleBorder.find_batch hbig hev h1 h2
    have hblk := MiddleBorder.inv_block w S hbig p (by omega) hple i hi
    rw [← hn] at hblk
    have hidx : (mstate blank startSym endSym mark leftSym one zero D w S init n).idx = p := by
      rw [hM.idx_eq, hblk.2.1]
    obtain ⟨ω, hFW, hsv⟩ := hM.out hbig h2 (by rw [hidx]; omega)
    rw [hidx] at hFW
    have hlen : n - S ≤ (MiddleBorder.Wnd w S (p - 1)).length := by
      simp only [MiddleBorder.Wnd, List.length_take, List.length_drop]
      omega
    have hkey : (MiddleBorder.Wnd w S (p - 1)).take (n - S) = (w.drop (S / 2)).take (n - S) := by
      simp only [MiddleBorder.Wnd, List.take_take]
      congr 1
      omega
    rw [hFW.read hsv (by omega) hlen, hkey]

end Read

/-! ## §12 全体像と、残っている前提

### できあがったもの

* §1–§8：凍結窓 1 個分（＝ 1 バッチ）を平坦な動作列 `batchActs` に落とし、
  その長さ（`Cbatch D * |y| + 1`）と、流し切ったあとの `F` テープの内容
  （`FlagWordOK`：添字 `ℓ` で `one` が読めることと `y.take ℓ` の回文性が同値）を与えた。
* §6：`rateM D = 50 * Cbatch D + 1` の速さで挽けば、解放から次の解放までの
  `gw S - 1` ラウンドでバッチは必ず挽き終わる（`fits_of_length_le`, `batch_complete`）。
  締切そのものは `MiddleBorder.borderMiddle_deadline` が与える。
* §10–§11：ラウンド機械 `MState` / `mround` / `mcost` と不変条件 `MEncodes`、
  その保存 `mround_encodes`、反復 `mstate_encodes`、そして主定理 `middle_flag_read`。

### 1 ラウンドにやること（`mround`）

* `S < 8`：窓は `≤ 21` 記号なので回文性は窓の決定可能な関数。判定結果を 1 セルに書く
  （費用は `MiddleBorder` と同じ `3S² + 1` を計上）。
* `8 ≤ S`：
  * 到着記号を、まだ凍結していない入力コピー（`X` 用・`X2` 用の各 `numJobs` 本）へ
    1 個ずつ追記する（`feed`、`2 * numJobs = 26` 動作）。`InputCopy.FrontierView` が
    そのまま不変条件になる。
  * 解放ラウンド `n = relTime S j`：バッチ `j` 用のコピー 2 本を 1 動作ずつで凍結し
    （`InputCopy.toSeqView`：`SeqView` の添字 `|y|` に立つ）、フラグテープを入れ替える
    （書き込み側 ↔ 読み出し側のダブルバッファ）。完成したバッチの `F` は
    ちょうど読み出し開始位置 `rdOf S (j-1) = n - S` にヘッドが立っている。
  * それ以外：`rateM D` 個の動作を挽き（`gstep`）、読み出し側を 1 セル右へ（`outStep`）。

1 ラウンドの費用は `CmT' D = rateM D + 148` 以下（`mround_cost`）。

### 残っている前提

1. `DecompOnTapes` は抽象のまま（指示どおり）。`GSPreprocessTapes` 側で具体化すれば
   `Cd`／`Dd` が定まり、`rateM D`・`Cbatch D`・`CmT' D` がすべて具体的な数になる。
2. `minit_encodes` の初期条件（各コピーが `[leftSym]` の最前線であること、フラグテープ
   2 本が長さ `Lmax S + 1` 以上の語を持ちヘッドが添字 `0` にあること）は仮定として
   置いてある。これは段の立ち上げに 1 度だけ必要な `O(S)` の前処理
   （空白を `Lmax S + 1` セル分書いて戻る／各コピーに `leftSym` を 1 個書く）で作れる。
3. 入力コピーはバッチごとに専用の 2 本を使う（段あたり `2 * numJobs = 26` 本）。
   凍結したコピーを作り直す必要がないので、追い付き用の FIFO は要らない。
   1 ラウンドあたりの追記は 26 回で定数。
-/

end MiddleTapes
end PalPeg
