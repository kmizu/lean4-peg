import PalPeg.BorderJobTapes
import PalPeg.InputCopy
import PalPeg.MiddleBorder

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
  /-- 段テープを載せ直す動作列。 -/
  acts : List (Fin sc) → ℕ → OvTapes sc → List (Act sc)
  /-- 費用の傾き。 -/
  Cd : ℕ
  /-- 費用の切片。 -/
  Dd : ℕ
  len_le : ∀ (y : List (Fin sc)) (L : ℕ) (ts : OvTapes sc),
    (acts y L ts).length ≤ Cd * L + Dd
  pat : ∀ (y : List (Fin sc)) (L : ℕ), 1 ≤ L → L ≤ y.length → ∀ ts : OvTapes sc,
    Tape.SeqView blank (applyActs blank (acts y L ts) ts).P
      (startSym :: ((y.take L).drop (decompose (y.take L) 8).1 ++ [endSym])) 1
  upat : ∀ (y : List (Fin sc)) (L : ℕ), 1 ≤ L → L ≤ y.length → ∀ ts : OvTapes sc,
    Tape.SeqView blank (applyActs blank (acts y L ts) ts).U
      (startSym :: ((y.take L).take (decompose (y.take L) 8).1 ++ [endSym])) 1
  cnt : ∀ (y : List (Fin sc)) (L : ℕ), 1 ≤ L → L ≤ y.length → ∀ ts : OvTapes sc,
    Tape.CounterView' blank mark (applyActs blank (acts y L ts) ts).Cnt
      (decompose (y.take L) 8).2.1
  keepX : ∀ (y : List (Fin sc)) (L : ℕ) (ts : OvTapes sc),
    (applyActs blank (acts y L ts) ts).X = ts.X
  keepX2 : ∀ (y : List (Fin sc)) (L : ℕ) (ts : OvTapes sc),
    (applyActs blank (acts y L ts) ts).X2 = ts.X2
  keepF : ∀ (y : List (Fin sc)) (L : ℕ) (ts : OvTapes sc),
    (applyActs blank (acts y L ts) ts).F = ts.F

namespace DecompOnTapes

variable {blank startSym endSym mark : Fin sc}

/-- 段幅ごとの余裕込みの傾き。 -/
def A (D : DecompOnTapes sc blank startSym endSym mark) : ℕ := D.Cd + 2436

/-- ジョブ全体（ループ部分）の費用係数。 -/
def M (D : DecompOnTapes sc blank startSym endSym mark) : ℕ := 2 * D.A + D.Dd

end DecompOnTapes

/-! ## §4 1 バッチ分の平坦な動作列 -/

/-- 段の切り出し位置 `s`。 -/
def stageS (y : List (Fin sc)) (L : ℕ) : ℕ := (decompose (y.take L) 8).1

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
      ((y.take L).take (stageS y L)) ((y.take L).drop (stageS y L)) (y.take L).reverse
      8 (decompose (y.take L) 8).2.1 (decompose (y.take L) 8).2.2
      (max 1 (2 * stageS y L)) (stageS y L) ((8 + 2) * L + 1) ⟨0, 0⟩
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
        let L' := nextLen (stageS y L)
        let h := homeActs sc L (L' - stageS y L') L'
        a ++ h ++ jobLoop blank startSym endSym mark leftSym one D y fuel L'
          (applyActs blank h (applyActs blank a ts))

/-- **1 バッチ分の動作列**：初期のヘッド合わせ ＋ ループ ＋ 読み出し位置 `rd` への `F` の
置き直し。 -/
def jobActs (blank startSym endSym mark leftSym one : Fin sc)
    (D : DecompOnTapes sc blank startSym endSym mark) (y : List (Fin sc)) (rd : ℕ)
    (ts : OvTapes sc) : List (Act sc) :=
  let h0 := homeActs sc y.length (y.length - stageS y y.length) y.length
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

/-- **バッチのループ部分の主定理**：動作数は `D.M * L` 以下で、走り終えたあとの
`F` テープは `jobFlags` を保持し、ヘッドは添字 `≤ L` にある。 -/
theorem jobLoop_ok (D : DecompOnTapes sc blank startSym endSym mark) {y : List (Fin sc)}
    (hleft : leftSym ∉ y) (hend : endSym ∉ y)
    (hOK : ∀ L, 1 ≤ L → L ≤ y.length →
      StageOK y 8 L (gsDec y 8 L).1 (gsDec y 8 L).2.1 (gsDec y 8 L).2.2) :
    ∀ (fuel L : ℕ) (ts : OvTapes sc) (fw : List (Fin sc)),
      L ≤ y.length → fw.length = y.length + 1 →
      Tape.SeqView blank ts.X (leftSym :: y) (L - stageS y L) →
      Tape.SeqView blank ts.X2 (leftSym :: y) L →
      Tape.SeqView blank ts.F fw L →
      (jobLoop blank startSym endSym mark leftSym one D y fuel L ts).length ≤ D.M * L ∧
      ∃ i, i ≤ L ∧
        Tape.SeqView blank
          (applyActs blank
            (jobLoop blank startSym endSym mark leftSym one D y fuel L ts) ts).F
          (jobFlags y (gsDec y 8) one 8 fuel L fw) i := by
  intro fuel
  induction fuel with
  | zero =>
    intro L ts fw _ _ _ _ hF
    exact ⟨Nat.zero_le _, L, le_rfl, hF⟩
  | succ fuel ih =>
    intro L ts fw hL hfw hX hX2 hF
    simp only [jobLoop, jobFlags]
    by_cases h0 : L = 0
    · rw [if_pos h0, if_pos (show L = 0 from h0)]
      exact ⟨Nat.zero_le _, L, le_rfl, hF⟩
    rw [if_neg h0, if_neg h0]
    -- 段のデータ
    have hOKL : StageOK y 8 L (stageS y L) (decompose (y.take L) 8).2.1
        (decompose (y.take L) 8).2.2 := hOK L (by omega) hL
    have hylen : (y.take L).length = L := by simp only [List.length_take]; omega
    have hcut : stageS y L ≤ L := hOKL.cut_le
    have hshort : 7 * stageS y L < L := by have := hOKL.cut_short; omega
    have hulen : ((y.take L).take (stageS y L)).length = stageS y L := by
      simp only [List.length_take]; omega
    have hvlen : ((y.take L).drop (stageS y L)).length = L - stageS y L := by
      simp only [List.length_drop]; omega
    have hTlen : ((y.take L).reverse).length = L := by
      simp only [List.length_reverse]; omega
    have hlenuv : ((y.take L).take (stageS y L)).length
        + ((y.take L).drop (stageS y L)).length = ((y.take L).reverse).length := by omega
    have hendv : endSym ∉ (y.take L).drop (stageS y L) := fun hc =>
      hend (List.mem_of_mem_take (List.mem_of_mem_drop hc))
    have hmin : max 1 (2 * ((y.take L).take (stageS y L)).length) ≤ max 1 (2 * stageS y L) := by
      rw [hulen]
    have hinv0 : OvInv ((y.take L).take (stageS y L)) ((y.take L).drop (stageS y L))
        ((y.take L).reverse) ⟨0, 0⟩ :=
      ⟨by simpa using matchLen_zero _ _ _, by simp only []; omega⟩
    -- 段テープの載せ替え後の符号化
    have hE0 : OvEncodes blank leftSym startSym endSym mark
        ((y.take L).take (stageS y L)) ((y.take L).drop (stageS y L)) y fw L
        (decompose (y.take L) 8).2.1 (applyActs blank (D.acts y L ts) ts) ⟨0, 0⟩ := by
      refine ⟨D.pat y L (by omega) hL ts, ?_, D.cnt y L (by omega) hL ts,
        D.upat y L (by omega) hL ts, ?_, ?_⟩
      · rw [D.keepX y L ts]; simpa [hulen] using hX
      · rw [D.keepX2 y L ts]; simpa using hX2
      · rw [D.keepF y L ts]; simpa using hF
    have hK := hOKL.ksimple
    have hrun := ovRunTapes_encodes (one := one) (c := stageS y L) (xw := y)
      hK (by omega : (0:ℕ) < 8) hL hleft hendv rfl hulen.symm hlenuv hmin
      ((8 + 2) * L + 1) ⟨0, 0⟩ (applyActs blank (D.acts y L ts) ts) fw hinv0 hE0
    have hSA := ovRunActs_length (one := one) (c := stageS y L) (xw := y) (startSym := startSym)
      (mark := mark) hK (by omega : (0:ℕ) < 8) hL hleft hendv rfl hulen.symm hlenuv hmin
      ((8 + 2) * L + 1) ⟨0, 0⟩ (applyActs blank (D.acts y L ts) ts) fw hinv0 hE0
    have hSAcost : ovRunCost ((y.take L).take (stageS y L)) ((y.take L).drop (stageS y L))
        ((y.take L).reverse) 8 (decompose (y.take L) 8).2.1 (decompose (y.take L) 8).2.2
        (max 1 (2 * stageS y L)) ((8 + 2) * L + 1) ⟨0, 0⟩ ≤ 2432 * L :=
      stage_tape_cost_le (x := y) (dec := gsDec y 8) hL (by omega) hOKL
    have hts2 : applyActs blank (stageActs blank startSym endSym mark leftSym one D y L ts) ts
        = ovRunTapes blank leftSym endSym mark one ((y.take L).take (stageS y L))
            ((y.take L).drop (stageS y L)) ((y.take L).reverse) 8
            (decompose (y.take L) 8).2.1 (decompose (y.take L) 8).2.2
            (max 1 (2 * stageS y L)) (stageS y L) ((8 + 2) * L + 1) ⟨0, 0⟩
            (applyActs blank (D.acts y L ts) ts) := by
      simp only [stageActs, applyActs_append, ovRunActs_apply]
    have hrun' : OvEncodes blank leftSym startSym endSym mark
        ((y.take L).take (stageS y L)) ((y.take L).drop (stageS y L)) y
        (ovRunFlags ((y.take L).take (stageS y L)) ((y.take L).drop (stageS y L))
          ((y.take L).reverse) one 8 (decompose (y.take L) 8).2.1
          (decompose (y.take L) 8).2.2 (max 1 (2 * stageS y L)) ((8 + 2) * L + 1) ⟨0, 0⟩ fw)
        L (decompose (y.take L) 8).2.1
        (applyActs blank (stageActs blank startSym endSym mark leftSym one D y L ts) ts)
        (ovRunState ((y.take L).take (stageS y L)) ((y.take L).drop (stageS y L))
          ((y.take L).reverse) 8 (decompose (y.take L) 8).2.1 (decompose (y.take L) 8).2.2
          (max 1 (2 * stageS y L)) ((8 + 2) * L + 1) ⟨0, 0⟩) := by
      rw [hts2]; exact hrun
    -- 継ぎ目
    have h3 : 3 * nextLen (stageS y L) + 1 ≤ L := nextLen_shrink hshort
    have hL' : nextLen (stageS y L) ≤ y.length := by omega
    have hfw2 : (ovRunFlags ((y.take L).take (stageS y L)) ((y.take L).drop (stageS y L))
        ((y.take L).reverse) one 8 (decompose (y.take L) 8).2.1
        (decompose (y.take L) 8).2.2 (max 1 (2 * stageS y L)) ((8 + 2) * L + 1) ⟨0, 0⟩
        fw).length = y.length + 1 := by rw [ovRunFlags_length]; exact hfw
    have hhome := homeActs_eff (blank := blank) L
      (nextLen (stageS y L) - stageS y (nextLen (stageS y L))) (nextLen (stageS y L))
      (applyActs blank (stageActs blank startSym endSym mark leftSym one D y L ts) ts)
    have hcons : (leftSym :: y).length = y.length + 1 := by simp
    have hih := ih (nextLen (stageS y L))
      (applyActs blank (homeActs sc L
        (nextLen (stageS y L) - stageS y (nextLen (stageS y L))) (nextLen (stageS y L)))
        (applyActs blank (stageActs blank startSym endSym mark leftSym one D y L ts) ts)) _
      hL' hfw2
      (by rw [hhome]; exact seq_home hrun'.txt (Nat.sub_le _ _) (by rw [hcons]; omega))
      (by rw [hhome]; exact seq_home hrun'.txt2 (Nat.sub_le _ _) (by rw [hcons]; omega))
      (by rw [hhome]; exact seq_home hrun'.flg (Nat.sub_le _ _) (by rw [hfw2]; omega))
    have hstage : (stageActs blank startSym endSym mark leftSym one D y L ts).length
        ≤ D.Cd * L + D.Dd + 2432 * L := by
      simp only [stageActs, List.length_append, hSA]
      have := D.len_le y L ts
      omega
    refine ⟨?_, ?_⟩
    · rw [List.length_append, List.length_append, homeActs_length]
      have hMdef : (2 * D.A + D.Dd) * L = D.M * L := rfl
      have hAdef : D.A * L = D.Cd * L + 2436 * L := by
        simp only [DecompOnTapes.A, Nat.add_mul]
      have hgeo := geo_key (A := D.A) (B := D.Dd) (L := L) (L' := nextLen (stageS y L))
        (R := (jobLoop blank startSym endSym mark leftSym one D y fuel (nextLen (stageS y L))
          (applyActs blank (homeActs sc L
            (nextLen (stageS y L) - stageS y (nextLen (stageS y L))) (nextLen (stageS y L)))
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
    (hOK : ∀ L, 1 ≤ L → L ≤ y.length →
      StageOK y 8 L (gsDec y 8 L).1 (gsDec y 8 L).2.1 (gsDec y 8 L).2.2)
    (ts : OvTapes sc) (fw : List (Fin sc)) (rd : ℕ)
    (hfw : fw.length = y.length + 1) (hrd : rd ≤ y.length)
    (hX : ∃ i, i ≤ y.length ∧ Tape.SeqView blank ts.X (leftSym :: y) i)
    (hX2 : ∃ i, i ≤ y.length ∧ Tape.SeqView blank ts.X2 (leftSym :: y) i)
    (hF : ∃ i, i ≤ y.length ∧ Tape.SeqView blank ts.F fw i) :
    (jobActs blank startSym endSym mark leftSym one D y rd ts).length
        ≤ Cjob D * y.length ∧
      Tape.SeqView blank
        (applyActs blank (jobActs blank startSym endSym mark leftSym one D y rd ts) ts).F
        (jobFlags y (gsDec y 8) one 8 (y.length + 1) y.length fw) rd := by
  obtain ⟨iX, hiX, hXv⟩ := hX
  obtain ⟨iX2, hiX2, hX2v⟩ := hX2
  obtain ⟨iF, hiF, hFv⟩ := hF
  have hcons : (leftSym :: y).length = y.length + 1 := by simp
  simp only [jobActs]
  have hh0 := homeActs_eff (blank := blank) y.length
    (y.length - stageS y y.length) y.length ts
  have hj := jobLoop_ok (one := one) D hleft hend hOK (y.length + 1) y.length
    (applyActs blank (homeActs sc y.length (y.length - stageS y y.length) y.length) ts) fw
    le_rfl hfw
    (by rw [hh0]; exact seq_home hXv hiX (by rw [hcons]; omega))
    (by rw [hh0]; exact seq_home hX2v hiX2 (by rw [hcons]; omega))
    (by rw [hh0]; exact seq_home hFv hiF (by rw [hfw]; omega))
  obtain ⟨hlen, i, hi, hsv⟩ := hj
  constructor
  · rw [List.length_append, List.length_append, homeActs_length, homeF_length]
    have hC : Cjob D * y.length = D.M * y.length + 8 * y.length := by
      simp only [Cjob, Nat.add_mul]
    omega
  · rw [applyActs_append, applyActs_append, homeF_eff]
    exact seq_home hsv hi (by rw [jobFlags_length, hfw]; omega)

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

/-- **バッチの主定理**：バッチを流し切ると、`F` のヘッドは添字 `rd` に立ち、そこで読める
記号が `one` であることと `y.take rd` が回文であることが同値になる。 -/
theorem batchActs_ok (D : DecompOnTapes sc blank startSym endSym mark) {y : List (Fin sc)}
    (hne : one ≠ zero) (hleft : leftSym ∉ y) (hend : endSym ∉ y)
    (hOK : ∀ L, 1 ≤ L → L ≤ y.length →
      StageOK y 8 L (gsDec y 8 L).1 (gsDec y 8 L).2.1 (gsDec y 8 L).2.2)
    (ts : OvTapes sc) (fw : List (Fin sc)) (rd : ℕ)
    (hfw : fw.length = y.length + 1) (h1 : 1 ≤ rd) (h2 : rd ≤ y.length)
    (hX : ∃ i, i ≤ y.length ∧ Tape.SeqView blank ts.X (leftSym :: y) i)
    (hX2 : ∃ i, i ≤ y.length ∧ Tape.SeqView blank ts.X2 (leftSym :: y) i)
    (hF : ∃ i, i ≤ y.length ∧ Tape.SeqView blank ts.F fw i) :
    (batchActs blank startSym endSym mark leftSym one zero D y rd ts).length
        ≤ Cbatch D * y.length + 1 ∧
      (Tape.read (applyActs blank
        (batchActs blank startSym endSym mark leftSym one zero D y rd ts) ts).F = one
          ↔ IsPal (y.take rd)) := by
  obtain ⟨iF, hiF, hFv⟩ := hF
  simp only [batchActs]
  have hh := homeF_eff (blank := blank) y.length y.length ts
  have hFh : Tape.SeqView blank (applyActs blank (homeF sc y.length y.length) ts).F
      fw y.length := by
    rw [hh]; exact seq_home hFv hiF (by rw [hfw]; omega)
  have hcl := clearF_spec (zero := zero) y.length
    (applyActs blank (homeF sc y.length y.length) ts) fw hFh
  have hXk : (applyActs blank (clearF zero y.length)
      (applyActs blank (homeF sc y.length y.length) ts)).X = ts.X := by
    rw [hcl.1, hh]
  have hX2k : (applyActs blank (clearF zero y.length)
      (applyActs blank (homeF sc y.length y.length) ts)).X2 = ts.X2 := by
    rw [hcl.2.1, hh]
  have hcw : (clearWord zero y.length fw).length = y.length + 1 := by
    rw [clearWord_length]; exact hfw
  have hjob := jobActs_ok (one := one) D hleft hend hOK
    (applyActs blank (clearF zero y.length)
      (applyActs blank (homeF sc y.length y.length) ts))
    (clearWord zero y.length fw) rd hcw h2
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
    have hiff := flags_on_tape_eq_palPrefixFlagsGS (x := y) (dec := gsDec y 8)
      (one := one) (zero := zero) (k := 8) (fw := clearWord zero y.length fw)
      (by omega) hne hOK rd h1 h2 (by omega) hz
    have hpal := palPrefixFlagsGS_spec (x := y) (dec := gsDec y 8) (k := 8)
      (by omega) hOK rd h2
    constructor
    · intro hr
      have : (jobFlags y (gsDec y 8) one 8 (y.length + 1) y.length
          (clearWord zero y.length fw))[rd]? = some one := by rw [hread, hr]
      have := hiff.1 this
      rw [hpal] at this
      simpa using this
    · intro hp
      have : (palPrefixFlagsGS y (gsDec y 8) 8)[rd]? = some true := by
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
    (hS : 8 ≤ S) (hev : 2 * (S / 2) = S) (hL : L ≤ 5 * S) (h : n ≤ Cbatch D * L + 1) :
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
    (hOK : ∀ L, 1 ≤ L → L ≤ (MiddleBorder.Wnd w S p).length →
      StageOK (MiddleBorder.Wnd w S p) 8 L (gsDec (MiddleBorder.Wnd w S p) 8 L).1
        (gsDec (MiddleBorder.Wnd w S p) 8 L).2.1 (gsDec (MiddleBorder.Wnd w S p) 8 L).2.2)
    (ts : OvTapes sc) (fw : List (Fin sc))
    (hfw : fw.length = (MiddleBorder.Wnd w S p).length + 1)
    (h1 : 1 ≤ n - S) (h2 : n - S ≤ (MiddleBorder.Wnd w S p).length)
    (hcov : n - S ≤ S + p * MiddleBorder.gw S)
    (hX : ∃ i, i ≤ (MiddleBorder.Wnd w S p).length ∧
      Tape.SeqView blank ts.X (leftSym :: MiddleBorder.Wnd w S p) i)
    (hX2 : ∃ i, i ≤ (MiddleBorder.Wnd w S p).length ∧
      Tape.SeqView blank ts.X2 (leftSym :: MiddleBorder.Wnd w S p) i)
    (hF : ∃ i, i ≤ (MiddleBorder.Wnd w S p).length ∧ Tape.SeqView blank ts.F fw i) :
    (Tape.read (applyActs blank (batchActs blank startSym endSym mark leftSym one zero D
        (MiddleBorder.Wnd w S p) (n - S) ts) ts).F = one)
      ↔ IsPal ((w.drop (S / 2)).take (n - S)) := by
  have hkey : (MiddleBorder.Wnd w S p).take (n - S) = (w.drop (S / 2)).take (n - S) := by
    simp only [MiddleBorder.Wnd, List.take_take]
    congr 1
    omega
  have h := (batchActs_ok D hne (fun hc => hleft (mem_wnd hc)) (fun hc => hend (mem_wnd hc))
    hOK ts fw (n - S) hfw h1 h2 hX hX2 hF).2
  rw [h, hkey]

end FlagRead

/-! ## §9 まだ組み立てていない部分（ラウンド機械）

本ファイルは「1 バッチ分」を完全にテープ上へ落とし、レートと締切の評価まで与えた。
`MiddleBorder.borderMiddle` のラウンド機械そのもの（`MState` / `mround` / `MEncodes` /
`mround_encodes` / `middle_flag_read`）を組むには、さらに次が必要である。

1. **入力コピーの供給**：`InputCopy.FrontierView` の 2 本組を、ラウンド `S/2 + 1` 以降
   毎ラウンド 1 記号ずつ伸ばし、バッチ解放のときにその 2 本を凍結して境界ジョブの
   `X`／`X2` として渡す。凍結した組は次の解放までに再生成する必要があるので、
   コピーは 2 組（計 4 本）を交互に使う。再生成の費用は `≤ |窓| ≤ 5S` で、
   `rateM D` の中に吸収できる（`fits_of_length_le` の余裕に含める形で係数を上げればよい）。
   本ファイルの `batchActs` は、ヘッドが添字 `≤ |y|` のどこにあってもよい形にしてあるので、
   凍結したコピーをそのまま渡せる。
2. **フラグテープのダブルバッファ**：`Grind` の `ts.F` が書き込み側、別に持つ `fout` が
   読み出し側。解放のたびに 2 本を入れ替え、非解放ラウンドでは `outStep` を 1 回。
   §7 の `outStep_spec` が読み出しヘッドの前進を、§5 の `batchActs_ok` が
   書き込み側の完成形を与えるので、あとは「解放時に書き込み側の残り動作が空である」
   ことを `batch_complete` と `MiddleBorder.inv_block`（ブロックの長さが `gw S`）から
   言えばよい。
3. **`MEncodes` と `mround_encodes`**：上の 1., 2. を `MiddleBorder.BState` の
   各成分（`width`／`idx`／`next`／`cur`／`rem`／`out`）に対応させる不変条件。
   `out` に対応するのが読み出し側テープで、その内容の正しさが §8 の `batch_read_flag`、
   ラウンド費用が `CmT D = rateM D + 1` である。
4. **退化した段（`S < 8`）**：`MiddleBorder.naiveFlags` の側は定数長なので、
   定数個の動作で直接計算する別プログラムを与える。
-/

end MiddleTapes
end PalPeg
