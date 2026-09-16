import PalPeg.VerifierFeedX
import PalPeg.GSVerifierTapesZ

/-!
# 供給つきのジグザグ一歩 (`VerifierFeedZ`)

`PalPeg.VerifierFeedX` は `GSVTapes.vprogramX` の一歩を **`.X .right` のたびに
`Txt2` を養いながら** 実行する機械 `vscanOneX` / `fstepX` を与えた。
本ファイルはその **`GSVTapesZ.vprogramZ'` 版**を同じ構成で与える。

`vprogramX` との違いは 2 点だけで、供給つき機械にもそのまま反映される。

* **比較枝**：`vcomp2Fed`（`vcompFed` を 2 回）を、ジグザグ単位動作 `zQuota = 4` 個
  `zUnitsFed` に置き換える。上りの単位はちょうど `vcompFed`（`.X .right` に供給がつく）、
  下りの単位は `U` を 1 つ左へ動かしてから `startSym` かどうかで
  「`U` を戻す」か「`Txt2` も 1 つ左へ」を選ぶ（**左移動には供給は要らない**）。
* **ずらし枝**：`vwalkFedX`（相乗りループ ＋ `uxWalk`）から **`uxWalk` を削除**し、
  相乗りループ `vwalkXRFed`（`Txt2` を `gsShift` だけ右へ、各歩に供給）だけにする。

## 費用（点ごと）

* 比較枝：`zUnitsFed 4 ≤ 4 * 35 = 140`
* ずらし枝：`34 * gsShift`

に走査段の `program'` の適用（`|program'|`）と歩頭の供給（`33`）を足したものが
一歩の費用 `fcostZ` である。`X` 版の `2·checked`（`U` の巻き戻し）に当たる項は
**存在しない**ので、`fcostZ` は `ΔΦ` だけで**点ごとに**抑えられる
（`fcostZ_le`）——これが `PalPeg.PointwiseGap.rewind_not_pointwise` の壁を
回避するという主張の、供給つき機械での実現である。
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg
namespace VerifierFeedZ

open PegSeparation.RealTimeTM
open PalPeg.TextFeed
open PalPeg.VerifierFeed
open PalPeg.GSVTapesZ
open PalPeg.GSVerifierZ (ZS ZWf zQuota zMove zMoves zReset)

variable {sc : ℕ}

/-! ## 1. 1 単位動作（供給つき） -/

/-- `U` を 1 つ左（動作 1、供給不要）。 -/
abbrev vmoveUL (blank : Fin sc) (M : VMachine' sc) : VMachine' sc := vmoveULN blank 1 M

/-- `Txt2` を 1 つ左（動作 1、供給不要）。 -/
abbrev vmoveXL (blank : Fin sc) (M : VMachine' sc) : VMachine' sc := vmoveXLN blank 1 M

@[simp] theorem vmoveUL_U (blank : Fin sc) (M : VMachine' sc) :
    (vmoveUL blank M).vt.2.U = Tape.step blank M.vt.2.U M.vt.2.U.focus .left := rfl

/-- **1 単位動作（供給つき）**。 -/
def zUnitFed (blank startSym endSym mark : Fin sc) (up : Bool) (M : VMachine' sc) :
    VMachine' sc :=
  if up then vcompFed blank endSym mark M
  else if zPeekL blank M.vt.2 = startSym then vmoveUR blank (vmoveUL blank M)
    else vmoveXL blank (vmoveUL blank M)

/-- 1 単位動作のあとの向き。 -/
def zNextDirM (blank startSym : Fin sc) (up : Bool) (M : VMachine' sc) : Bool :=
  zNextDir blank startSym up M.vt.2

/-- `n` 単位動作（供給つき）。 -/
def zUnitsFed (blank startSym endSym mark : Fin sc) :
    ℕ → Bool → VMachine' sc → VMachine' sc
  | 0, _, M => M
  | n + 1, up, M =>
      zUnitsFed blank startSym endSym mark n (zNextDirM blank startSym up M)
        (zUnitFed blank startSym endSym mark up M)

/-- `n` 単位動作のあとの向き。 -/
def zDirsFed (blank startSym endSym mark : Fin sc) : ℕ → Bool → VMachine' sc → Bool
  | 0, up, _ => up
  | n + 1, up, M =>
      zDirsFed blank startSym endSym mark n (zNextDirM blank startSym up M)
        (zUnitFed blank startSym endSym mark up M)

/-- ヘッド位置と向きからゴースト状態を作る（`lo`/`hi` はゴーストなので、
`ZWf` を満たす最小の張り方をとる）。 -/
def zsOf (c : ℕ) (up : Bool) : ZS := ⟨c, if up then 0 else c, c, up⟩

@[simp] theorem zsOf_head (c : ℕ) (up : Bool) : (zsOf c up).head = c := rfl
@[simp] theorem zsOf_up (c : ℕ) (up : Bool) : (zsOf c up).up = up := rfl

theorem zsOf_wf {s c : ℕ} (up : Bool) (h : c ≤ s) : ZWf s (zsOf c up) := by
  refine ⟨h, h, ?_⟩
  intro hup
  have hup' : up = true := hup
  refine ⟨?_, rfl⟩
  show (if up = true then 0 else c) = 0
  rw [hup']; rfl

/-! ### 射影 -/

section Proj

variable (blank startSym endSym mark : Fin sc)

@[simp] theorem zUnitFed_z (up : Bool) (M : VMachine' sc) :
    (zUnitFed blank startSym endSym mark up M).z = M.z := by
  unfold zUnitFed; split_ifs
  · exact vcompFed_z blank endSym mark M
  · rfl
  · rfl

@[simp] theorem zUnitFed_m1 (up : Bool) (M : VMachine' sc) :
    (zUnitFed blank startSym endSym mark up M).m1 = M.m1 := by
  unfold zUnitFed; split_ifs
  · exact vcompFed_m1 blank endSym mark M
  · rfl
  · rfl

@[simp] theorem zUnitFed_vt1 (up : Bool) (M : VMachine' sc) :
    (zUnitFed blank startSym endSym mark up M).vt.1 = M.vt.1 := by
  unfold zUnitFed; split_ifs
  · exact vcompFed_vt1 blank endSym mark M
  · rfl
  · rfl

@[simp] theorem zUnitFed_Q1 (up : Bool) (M : VMachine' sc) :
    (zUnitFed blank startSym endSym mark up M).Q1 = M.Q1 := by
  unfold zUnitFed; split_ifs
  · exact vcompFed_Q1 blank endSym mark M
  · rfl
  · rfl

@[simp] theorem zUnitFed_R1qt (up : Bool) (M : VMachine' sc) :
    (zUnitFed blank startSym endSym mark up M).R1.qt = M.R1.qt := by
  unfold zUnitFed; split_ifs
  · exact vcompFed_R1qt blank endSym mark M
  · rfl
  · rfl

@[simp] theorem zUnitsFed_z :
    ∀ (n : ℕ) (up : Bool) (M : VMachine' sc),
      (zUnitsFed blank startSym endSym mark n up M).z = M.z := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro up M
    show (zUnitsFed blank startSym endSym mark n _ (zUnitFed blank startSym endSym mark up M)).z
      = M.z
    rw [ih, zUnitFed_z]

@[simp] theorem zUnitsFed_m1 :
    ∀ (n : ℕ) (up : Bool) (M : VMachine' sc),
      (zUnitsFed blank startSym endSym mark n up M).m1 = M.m1 := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro up M
    show (zUnitsFed blank startSym endSym mark n _
      (zUnitFed blank startSym endSym mark up M)).m1 = M.m1
    rw [ih, zUnitFed_m1]

@[simp] theorem zUnitsFed_vt1 :
    ∀ (n : ℕ) (up : Bool) (M : VMachine' sc),
      (zUnitsFed blank startSym endSym mark n up M).vt.1 = M.vt.1 := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro up M
    show (zUnitsFed blank startSym endSym mark n _
      (zUnitFed blank startSym endSym mark up M)).vt.1 = M.vt.1
    rw [ih, zUnitFed_vt1]

@[simp] theorem zUnitsFed_Q1 :
    ∀ (n : ℕ) (up : Bool) (M : VMachine' sc),
      (zUnitsFed blank startSym endSym mark n up M).Q1 = M.Q1 := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro up M
    show (zUnitsFed blank startSym endSym mark n _
      (zUnitFed blank startSym endSym mark up M)).Q1 = M.Q1
    rw [ih, zUnitFed_Q1]

@[simp] theorem zUnitsFed_R1qt :
    ∀ (n : ℕ) (up : Bool) (M : VMachine' sc),
      (zUnitsFed blank startSym endSym mark n up M).R1.qt = M.R1.qt := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro up M
    show (zUnitsFed blank startSym endSym mark n _
      (zUnitFed blank startSym endSym mark up M)).R1.qt = M.R1.qt
    rw [ih, zUnitFed_R1qt]

end Proj

/-! ### 費用 -/

theorem zUnitFed_cost (blank startSym endSym mark : Fin sc) (up : Bool) (M : VMachine' sc) :
    (zUnitFed blank startSym endSym mark up M).cost ≤ M.cost + 35 := by
  unfold zUnitFed
  split_ifs
  · exact vcompFed_cost blank endSym mark M
  · show (vmoveUR blank (vmoveUL blank M)).cost ≤ M.cost + 35
    show M.R1.cost + 1 + 1 + M.R2.cost ≤ M.R1.cost + M.R2.cost + 35
    omega
  · show (vmoveXL blank (vmoveUL blank M)).cost ≤ M.cost + 35
    show M.R1.cost + 1 + 1 + M.R2.cost ≤ M.R1.cost + M.R2.cost + 35
    omega

theorem zUnitsFed_cost (blank startSym endSym mark : Fin sc) :
    ∀ (n : ℕ) (up : Bool) (M : VMachine' sc),
      (zUnitsFed blank startSym endSym mark n up M).cost ≤ M.cost + 35 * n := by
  intro n
  induction n with
  | zero => intro _ M; show M.cost ≤ M.cost + 35 * 0; omega
  | succ n ih =>
    intro up M
    have h1 := zUnitFed_cost blank startSym endSym mark up M
    have h2 := ih (zNextDirM blank startSym up M) (zUnitFed blank startSym endSym mark up M)
    show (zUnitsFed blank startSym endSym mark n _
      (zUnitFed blank startSym endSym mark up M)).cost ≤ M.cost + 35 * (n + 1)
    omega

/-! ## 2. 1 単位動作の実現 -/

section UnitSpec

variable {blank startSym endSym mark : Fin sc} {u Text : List (Fin sc)}

/-- **1 単位動作の実現**：`GSVerifierZ.zMove` と一致する。 -/
theorem zUnitFed_spec {n pos : ℕ} {zz : ZS} {M : VMachine' sc}
    (hmb : mark ≠ blank) (hb : blank ∉ Text) (hmT : mark ∉ Text) (hendu : endSym ∉ u)
    (hstartu : startSym ∉ u) (hse : startSym ≠ endSym) (hn : n ≤ Text.length)
    (hwf : ZWf u.length zz)
    (hU : Tape.SeqView blank M.vt.2.U (startSym :: (u ++ [endSym])) (zz.head + 1))
    (hX : Txt2Inv blank mark Text n M (pos - u.length + zz.head))
    (hok : Ok2 n M (pos - u.length + zz.head))
    (hpos : u.length ≤ pos) (hroom : pos < n) :
    Tape.SeqView blank (zUnitFed blank startSym endSym mark zz.up M).vt.2.U
        (startSym :: (u ++ [endSym])) ((zMove u Text pos zz).head + 1) ∧
      Txt2Inv blank mark Text n (zUnitFed blank startSym endSym mark zz.up M)
        (pos - u.length + (zMove u Text pos zz).head) ∧
      Ok2 n (zUnitFed blank startSym endSym mark zz.up M)
        (pos - u.length + (zMove u Text pos zz).head) ∧
      zNextDirM blank startSym zz.up M = (zMove u Text pos zz).up := by
  obtain ⟨w1, w2, w3⟩ := hwf
  by_cases hup : zz.up = true
  · -- 上り：`vcompFed` そのもの。
    have hacts : zUnitFed blank startSym endSym mark zz.up M
        = vcompFed blank endSym mark M := by unfold zUnitFed; rw [if_pos hup]
    obtain ⟨s1, s2, s3⟩ := vcompFed_spec (blank := blank) (startSym := startSym)
      (pos := pos) hmb hb hmT hendu hn hU hX hok w1 hpos hroom
    rw [hacts, zMove_head_up (u := u) (Text := Text) (pos := pos) hup]
    refine ⟨s1, s2, s3, ?_⟩
    rw [zMove_up_up (u := u) (Text := Text) (pos := pos) hup]
    simp only [zNextDirM, zNextDir, hup, Bool.true_or]
  · have hupf : zz.up = false := by simpa using hup
    have hhead := zMove_head_down (u := u) (Text := Text) (pos := pos) hupf
    have hdir := zMove_up_down (u := u) (Text := Text) (pos := pos) hupf
    by_cases h0 : zz.head = 0
    · -- 左端：`U` を戻して上りへ（正味の移動なし）。
      have hpk : zPeekL blank M.vt.2 = startSym :=
        (zPeekL_startSym_iff (u := u) hstartu hse w1 hU).2 h0
      have hacts : zUnitFed blank startSym endSym mark zz.up M
          = vmoveUR blank (vmoveUL blank M) := by
        unfold zUnitFed; rw [if_neg hup, if_pos hpk]
      have hUeq : (vmoveUR blank (vmoveUL blank M)).vt.2.U
          = Tape.step blank (Tape.step blank M.vt.2.U M.vt.2.U.focus .left)
              (Tape.step blank M.vt.2.U M.vt.2.U.focus .left).focus .right := rfl
      have hXeq : (vmoveUR blank (vmoveUL blank M)).vt.2.Txt2 = M.vt.2.Txt2 := rfl
      have hm2 : (vmoveUR blank (vmoveUL blank M)).m2 = M.m2 := rfl
      have hQ2 : (vmoveUR blank (vmoveUL blank M)).Q2 = M.Q2 := rfl
      have hR2 : (vmoveUR blank (vmoveUL blank M)).R2 = M.R2 := rfl
      have hUlen : (0 : ℕ) + 1 < (startSym :: (u ++ [endSym])).length := by
        simp only [List.length_cons, List.length_append]; omega
      rw [hacts, hhead, hdir, h0]
      simp only [Nat.zero_sub, decide_true]
      refine ⟨?_, ?_, ?_, ?_⟩
      · show Tape.SeqView blank (vmoveUR blank (vmoveUL blank M)).vt.2.U _ (0 + 1)
        rw [hUeq]
        refine Tape.seq_move_right (Tape.seq_move_left (i := 0) ?_) hUlen
        rw [← h0]; exact hU
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · show Tape.SeqView blank (vmoveUR blank (vmoveUL blank M)).vt.2.Txt2
            (padW blank Text (vmoveUR blank (vmoveUL blank M)).m2) (pos - u.length + 0)
          rw [hXeq, hm2, ← h0]; exact hX.view
        · rw [hR2, hQ2]; exact hX.buf
        · rw [hQ2]; exact hX.qinv
        · rw [hQ2, hm2]; exact hX.qlist
        · rw [hm2]; exact hX.m2le
        · show pos - u.length + 0 ≤ (vmoveUR blank (vmoveUL blank M)).m2
          rw [hm2, ← h0]; exact hX.hle
      · show pos - u.length + 0 < (vmoveUR blank (vmoveUL blank M)).m2 ∨
          (vmoveUR blank (vmoveUL blank M)).m2 = n
        rw [hm2, ← h0]; exact hok
      · simp only [zNextDirM, zNextDir, hupf, Bool.false_or, hpk, decide_true]
    · -- 左端でない：`U` と `Txt2` を 1 つずつ左へ。
      have hpk : ¬ zPeekL blank M.vt.2 = startSym := by
        intro hc; exact h0 ((zPeekL_startSym_iff (u := u) hstartu hse w1 hU).1 hc)
      have hacts : zUnitFed blank startSym endSym mark zz.up M
          = vmoveXL blank (vmoveUL blank M) := by
        unfold zUnitFed; rw [if_neg hup, if_neg hpk]
      have hUeq : (vmoveXL blank (vmoveUL blank M)).vt.2.U
          = Tape.step blank M.vt.2.U M.vt.2.U.focus .left := rfl
      have hXeq : (vmoveXL blank (vmoveUL blank M)).vt.2.Txt2
          = Tape.step blank M.vt.2.Txt2 M.vt.2.Txt2.focus .left := rfl
      have hm2 : (vmoveXL blank (vmoveUL blank M)).m2 = M.m2 := rfl
      have hQ2 : (vmoveXL blank (vmoveUL blank M)).Q2 = M.Q2 := rfl
      have hR2 : (vmoveXL blank (vmoveUL blank M)).R2 = M.R2 := rfl
      have hi : pos - u.length + (zz.head - 1) + 1 = pos - u.length + zz.head := by omega
      rw [hacts, hhead, hdir]
      refine ⟨?_, ?_, ?_, ?_⟩
      · show Tape.SeqView blank (vmoveXL blank (vmoveUL blank M)).vt.2.U _ (zz.head - 1 + 1)
        rw [hUeq, show zz.head - 1 + 1 = zz.head from by omega]
        exact Tape.seq_move_left (i := zz.head) hU
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · show Tape.SeqView blank (vmoveXL blank (vmoveUL blank M)).vt.2.Txt2
            (padW blank Text (vmoveXL blank (vmoveUL blank M)).m2)
            (pos - u.length + (zz.head - 1))
          rw [hXeq, hm2]
          refine Tape.seq_move_left (i := pos - u.length + (zz.head - 1)) ?_
          rw [hi]; exact hX.view
        · rw [hR2, hQ2]; exact hX.buf
        · rw [hQ2]; exact hX.qinv
        · rw [hQ2, hm2]; exact hX.qlist
        · rw [hm2]; exact hX.m2le
        · show pos - u.length + (zz.head - 1) ≤ (vmoveXL blank (vmoveUL blank M)).m2
          have := hX.hle; rw [hm2]; omega
      · show pos - u.length + (zz.head - 1) < (vmoveXL blank (vmoveUL blank M)).m2 ∨
          (vmoveXL blank (vmoveUL blank M)).m2 = n
        rw [hm2]
        rcases hok with hc | hc
        · left; omega
        · right; exact hc
      · simp only [zNextDirM, zNextDir, hupf, Bool.false_or]
        rw [decide_eq_false hpk, (decide_eq_false (by omega : ¬ zz.head = 0))]

/-- **`n` 単位動作の実現**：`GSVerifierZ.zMoves` と一致する。 -/
theorem zUnitsFed_spec {n pos : ℕ}
    (hmb : mark ≠ blank) (hb : blank ∉ Text) (hmT : mark ∉ Text) (hendu : endSym ∉ u)
    (hstartu : startSym ∉ u) (hse : startSym ≠ endSym) (hn : n ≤ Text.length)
    (hpos : u.length ≤ pos) (hroom : pos < n) :
    ∀ (j : ℕ) (zz : ZS) (M : VMachine' sc), ZWf u.length zz →
      Tape.SeqView blank M.vt.2.U (startSym :: (u ++ [endSym])) (zz.head + 1) →
      Txt2Inv blank mark Text n M (pos - u.length + zz.head) →
      Ok2 n M (pos - u.length + zz.head) →
      Tape.SeqView blank (zUnitsFed blank startSym endSym mark j zz.up M).vt.2.U
          (startSym :: (u ++ [endSym])) ((zMoves u Text pos j zz).head + 1) ∧
        Txt2Inv blank mark Text n (zUnitsFed blank startSym endSym mark j zz.up M)
          (pos - u.length + (zMoves u Text pos j zz).head) ∧
        Ok2 n (zUnitsFed blank startSym endSym mark j zz.up M)
          (pos - u.length + (zMoves u Text pos j zz).head) ∧
        zDirsFed blank startSym endSym mark j zz.up M = (zMoves u Text pos j zz).up := by
  intro j
  induction j with
  | zero => intro zz M _ hU hX hok; exact ⟨hU, hX, hok, rfl⟩
  | succ j ih =>
    intro zz M hwf hU hX hok
    obtain ⟨s1, s2, s3, s4⟩ := zUnitFed_spec (u := u) (Text := Text) (pos := pos)
      hmb hb hmT hendu hstartu hse hn hwf hU hX hok hpos hroom
    have key := ih (zMove u Text pos zz) (zUnitFed blank startSym endSym mark zz.up M)
      (GSVerifierZ.zMove_wf hwf) s1 s2 s3
    rw [← s4] at key
    exact key

end UnitSpec

/-! ## 3. 検証器 2 本への作用（`vprogramZ'` 版） -/

/-- **`VerifierFeed.vExtFed` のジグザグ版**：比較枝は `zUnitsFed`、
ずらし枝は相乗りループだけ（**`uxWalk` は無い**）。 -/
def vExtFedZ (blank startSym endSym mark : Fin sc) (k : ℕ) (up : Bool) (M : VMachine' sc) :
    VMachine' sc :=
  if Tape.read (M.vt.1 GSTapes.tP) ≠ endSym ∧
      Tape.read (M.vt.1 GSTapes.tP) = Tape.read (M.vt.1 GSTapes.tT) then
    zUnitsFed blank startSym endSym mark zQuota up M
  else vwalkXRFed blank mark (GSVTapes.vDelta' blank mark k M.vt.1) M

/-- 検証器 2 本への作用のあとの向き。 -/
def vDirFedZ (blank startSym endSym mark : Fin sc) (up : Bool) (M : VMachine' sc) : Bool :=
  if Tape.read (M.vt.1 GSTapes.tP) ≠ endSym ∧
      Tape.read (M.vt.1 GSTapes.tP) = Tape.read (M.vt.1 GSTapes.tT) then
    zDirsFed blank startSym endSym mark zQuota up M
  else false

section ExtProj

variable (blank startSym endSym mark : Fin sc) (k : ℕ) (up : Bool) (M : VMachine' sc)

@[simp] theorem vExtFedZ_z : (vExtFedZ blank startSym endSym mark k up M).z = M.z := by
  unfold vExtFedZ; split_ifs
  · exact zUnitsFed_z blank startSym endSym mark zQuota up M
  · exact vwalkXRFed_z blank mark _ M

@[simp] theorem vExtFedZ_m1 : (vExtFedZ blank startSym endSym mark k up M).m1 = M.m1 := by
  unfold vExtFedZ; split_ifs
  · exact zUnitsFed_m1 blank startSym endSym mark zQuota up M
  · exact vwalkXRFed_m1 blank mark _ M

@[simp] theorem vExtFedZ_vt1 : (vExtFedZ blank startSym endSym mark k up M).vt.1 = M.vt.1 := by
  unfold vExtFedZ; split_ifs
  · exact zUnitsFed_vt1 blank startSym endSym mark zQuota up M
  · exact vwalkXRFed_vt1 blank mark _ M

@[simp] theorem vExtFedZ_Q1 : (vExtFedZ blank startSym endSym mark k up M).Q1 = M.Q1 := by
  unfold vExtFedZ; split_ifs
  · exact zUnitsFed_Q1 blank startSym endSym mark zQuota up M
  · exact vwalkXRFed_Q1 blank mark _ M

@[simp] theorem vExtFedZ_R1qt :
    (vExtFedZ blank startSym endSym mark k up M).R1.qt = M.R1.qt := by
  unfold vExtFedZ; split_ifs
  · exact zUnitsFed_R1qt blank startSym endSym mark zQuota up M
  · exact vwalkXRFed_R1qt blank mark _ M

end ExtProj

/-- 検証器 2 本への作用の費用（枝別）。**`2·checked` の項は無い**。 -/
def fextZ (blank endSym mark : Fin sc) (k : ℕ) (M : VMachine' sc) : ℕ :=
  if Tape.read (M.vt.1 GSTapes.tP) ≠ endSym ∧
      Tape.read (M.vt.1 GSTapes.tP) = Tape.read (M.vt.1 GSTapes.tT) then 140
  else 34 * GSVTapes.vDelta' blank mark k M.vt.1

theorem vExtFedZ_cost (blank startSym endSym mark : Fin sc) (k : ℕ) (up : Bool)
    (M : VMachine' sc) :
    (vExtFedZ blank startSym endSym mark k up M).cost ≤ M.cost + fextZ blank endSym mark k M := by
  unfold vExtFedZ fextZ
  split_ifs
  · have := zUnitsFed_cost blank startSym endSym mark zQuota up M
    simp only [zQuota] at this ⊢
    omega
  · exact vwalkXRFed_cost blank mark _ M

/-! ## 4. 一歩 -/

/-- **供給つきジグザグの一歩**（`VerifierFeedX.vscanOneX` のジグザグ版）。
ゴースト状態 `z` の第 2 成分は `U` のヘッド位置 `head` を表す。 -/
def zNextHead (u v : List (Fin sc)) (Text : List (Fin sc)) (up : Bool)
    (z : VState) : ℕ :=
  if z.1.q ≠ v.length ∧ Text[z.1.pos + z.1.q]? = v[z.1.q]? then
    (zMoves u Text z.1.pos zQuota (zsOf z.2 up)).head
  else z.2

def vscanOneZ (blank startSym endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r : ℕ)
    (Text : List (Fin sc)) (up : Bool) (M : VMachine' sc) : VMachine' sc :=
  { vscanApply blank endSym mark k (vExtFedZ blank startSym endSym mark k up M) with
    z := (scanStep v k p₁ r Text M.z.1, zNextHead u v Text up M.z) }

@[simp] theorem vscanOneZ_z (blank startSym endSym mark : Fin sc) (u v : List (Fin sc))
    (k p₁ r : ℕ) (Text : List (Fin sc)) (up : Bool) (M : VMachine' sc) :
    (vscanOneZ blank startSym endSym mark u v k p₁ r Text up M).z
      = (scanStep v k p₁ r Text M.z.1, zNextHead u v Text up M.z) := rfl

@[simp] theorem vscanOneZ_m1 (blank startSym endSym mark : Fin sc) (u v : List (Fin sc))
    (k p₁ r : ℕ) (Text : List (Fin sc)) (up : Bool) (M : VMachine' sc) :
    (vscanOneZ blank startSym endSym mark u v k p₁ r Text up M).m1 = M.m1 := by
  show (vExtFedZ blank startSym endSym mark k up M).m1 = M.m1
  rw [vExtFedZ_m1]

@[simp] theorem vscanOneZ_Q1 (blank startSym endSym mark : Fin sc) (u v : List (Fin sc))
    (k p₁ r : ℕ) (Text : List (Fin sc)) (up : Bool) (M : VMachine' sc) :
    (vscanOneZ blank startSym endSym mark u v k p₁ r Text up M).Q1 = M.Q1 := by
  show (vExtFedZ blank startSym endSym mark k up M).Q1 = M.Q1
  rw [vExtFedZ_Q1]

@[simp] theorem vscanOneZ_R1qt (blank startSym endSym mark : Fin sc) (u v : List (Fin sc))
    (k p₁ r : ℕ) (Text : List (Fin sc)) (up : Bool) (M : VMachine' sc) :
    (vscanOneZ blank startSym endSym mark u v k p₁ r Text up M).R1.qt = M.R1.qt := by
  show (vExtFedZ blank startSym endSym mark k up M).R1.qt = M.R1.qt
  rw [vExtFedZ_R1qt]

/-- **一歩（歩頭の供給込み）**：`VerifierFeedX.fstepX` のジグザグ版。 -/
def fstepZ (blank startSym endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r n : ℕ)
    (Text : List (Fin sc)) (up : Bool) (M : VMachine' sc) : VMachine' sc :=
  vscanOneZ blank startSym endSym mark u v k p₁ r Text up (vfillIf1' blank mark n M)

/-- **一歩の費用**：`|program'| + fextZ + 33`（歩頭の供給）。 -/
def fcostZ (blank endSym mark : Fin sc) (k n : ℕ) (M : VMachine' sc) : ℕ :=
  (GSTapes.program' blank endSym mark k (vfillIf1' blank mark n M).vt.1).length
    + fextZ blank endSym mark k (vfillIf1' blank mark n M) + 33

theorem vscanOneZ_cost (blank startSym endSym mark : Fin sc) (u v : List (Fin sc))
    (k p₁ r : ℕ) (Text : List (Fin sc)) (up : Bool) (M : VMachine' sc) :
    (vscanOneZ blank startSym endSym mark u v k p₁ r Text up M).cost
      ≤ M.cost + ((GSTapes.program' blank endSym mark k M.vt.1).length
        + fextZ blank endSym mark k M) := by
  have h1 := vExtFedZ_cost blank startSym endSym mark k up M
  have hsa : ∀ N : VMachine' sc, (vscanApply blank endSym mark k N).cost
      = N.cost + (GSTapes.program' blank endSym mark k N.vt.1).length := by
    intro N
    show N.R1.cost + (GSTapes.program' blank endSym mark k N.vt.1).length + N.R2.cost
      = N.R1.cost + N.R2.cost + (GSTapes.program' blank endSym mark k N.vt.1).length
    omega
  have hz : (vscanOneZ blank startSym endSym mark u v k p₁ r Text up M).cost
      = (vscanApply blank endSym mark k (vExtFedZ blank startSym endSym mark k up M)).cost :=
    rfl
  rw [hz, hsa, vExtFedZ_vt1]
  omega

theorem fstepZ_cost (blank startSym endSym mark : Fin sc) (u v : List (Fin sc))
    (k p₁ r n : ℕ) (Text : List (Fin sc)) (up : Bool) (M : VMachine' sc) :
    (fstepZ blank startSym endSym mark u v k p₁ r n Text up M).cost
      ≤ M.cost + fcostZ blank endSym mark k n M := by
  have h1 := vfillIf1'_cost blank mark n M
  have h2 := vscanOneZ_cost blank startSym endSym mark u v k p₁ r Text up
    (vfillIf1' blank mark n M)
  show (vscanOneZ blank startSym endSym mark u v k p₁ r Text up
    (vfillIf1' blank mark n M)).cost ≤ _
  unfold fcostZ
  omega

/-! ### 一歩の実現（供給の不変条件） -/

theorem zNextHead_le {u v Text : List (Fin sc)} {up : Bool} {z : VState}
    (hc : z.2 ≤ u.length) : zNextHead u v Text up z ≤ u.length := by
  unfold zNextHead
  split_ifs with h
  · exact (GSVerifierZ.zMoves_wf (u := u) (T := Text) (pos := z.1.pos) zQuota
      (zsOf_wf up hc)).1
  · exact hc

section StepSpec

variable {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)} {k p₁ r n : ℕ}
  {up : Bool} {M : VMachine' sc}

/-- **`VerifierFeedX.vExtFedX_spec` のジグザグ版**。 -/
theorem vExtFedZ_spec
    (hk : 0 < k) (hp : 0 < p₁) (hne : mark ≠ blank) (hv : 0 < v.length)
    (hend : endSym ∉ v) (hendu : endSym ∉ u) (hstartu : startSym ∉ u)
    (hse : startSym ≠ endSym) (hb : blank ∉ Text) (hmT : mark ∉ Text)
    (hscan : GSTapes.Encodes' blank startSym endSym mark v (padW blank Text M.m1) k p₁ r
      M.vt.1 M.z.1)
    (hpat : Tape.SeqView blank M.vt.2.U (startSym :: (u ++ [endSym])) (M.z.2 + 1))
    (hX : Txt2Inv blank mark Text n M (M.z.1.pos - u.length + M.z.2))
    (hok : Ok2 n M (M.z.1.pos - u.length + M.z.2))
    (hq : M.z.1.q ≤ v.length) (hc : M.z.2 ≤ u.length) (hpos : u.length ≤ M.z.1.pos)
    (hn : n ≤ Text.length) (hm1n : M.m1 ≤ n)
    (hd1 : M.z.1.pos + M.z.1.q ≤ M.m1)
    (hrd1 : M.z.1.q ≠ v.length → M.z.1.pos + M.z.1.q < M.m1) :
    Tape.SeqView blank (vExtFedZ blank startSym endSym mark k up M).vt.2.U
        (startSym :: (u ++ [endSym])) (zNextHead u v Text up M.z + 1) ∧
      Txt2Inv blank mark Text n (vExtFedZ blank startSym endSym mark k up M)
        ((scanStep v k p₁ r Text M.z.1).pos - u.length + zNextHead u v Text up M.z) ∧
      Ok2 n (vExtFedZ blank startSym endSym mark k up M)
        ((scanStep v k p₁ r Text M.z.1).pos - u.length + zNextHead u v Text up M.z) := by
  have hm1 : M.m1 ≤ Text.length := le_trans hm1n hn
  have hidx : (scanStep v k p₁ r Text M.z.1).pos + (scanStep v k p₁ r Text M.z.1).q ≤ M.m1 :=
    scanStep_index_le (p₁ := p₁) (r := r) (T := Text) hk hv hd1 hrd1
  unfold vExtFedZ
  by_cases hadv : Tape.read (M.vt.1 GSTapes.tP) ≠ endSym ∧
      Tape.read (M.vt.1 GSTapes.tP) = Tape.read (M.vt.1 GSTapes.tT)
  · rw [if_pos hadv]
    obtain ⟨ha1, ha2⟩ := (GSTapes.advance_iff' hend hscan hq).1 hadv
    have haT : Text[M.z.1.pos + M.z.1.q]? = v[M.z.1.q]? := by
      rw [← padW_getElem?_of_lt (blank := blank) hm1 (hrd1 ha1)]; exact ha2
    have hss : scanStep v k p₁ r Text M.z.1
        = (⟨M.z.1.pos, M.z.1.q + 1⟩ : ScanState) := GSTapes.scanStep_adv ⟨ha1, haT⟩
    have hroom : M.z.1.pos < n := by have := hrd1 ha1; omega
    have hnh : zNextHead u v Text up M.z
        = (zMoves u Text M.z.1.pos zQuota (zsOf M.z.2 up)).head := by
      unfold zNextHead; rw [if_pos ⟨ha1, haT⟩]
    obtain ⟨s1, s2, s3, _⟩ := zUnitsFed_spec (u := u) (Text := Text) (pos := M.z.1.pos)
      hne hb hmT hendu hstartu hse hn hpos hroom zQuota (zsOf M.z.2 up) M
      (zsOf_wf up hc) (by simpa using hpat) (by simpa using hX) (by simpa using hok)
    rw [hnh, hss]
    exact ⟨by simpa using s1, by simpa using s2, by simpa using s3⟩
  · rw [if_neg hadv]
    have hna : ¬ (M.z.1.q ≠ v.length ∧ Text[M.z.1.pos + M.z.1.q]? = v[M.z.1.q]?) := by
      rintro ⟨hcon1, hcon2⟩
      refine hadv ((GSTapes.advance_iff' hend hscan hq).2 ⟨hcon1, ?_⟩)
      rw [padW_getElem?_of_lt (blank := blank) hm1 (hrd1 hcon1)]; exact hcon2
    have hss : scanStep v k p₁ r Text M.z.1
        = (⟨M.z.1.pos + gsShift k p₁ r M.z.1.q, gsNextQ k p₁ r M.z.1.q⟩ : ScanState) :=
      GSTapes.scanStep_shift hna
    have hd : GSVTapes.vDelta' blank mark k M.vt.1 = gsShift k p₁ r M.z.1.q := by
      unfold GSVTapes.vDelta' gsShift
      by_cases hcd : Tape.read (Tape.step blank (M.vt.1 GSTapes.tAn) blank .left) = mark ∧
          Tape.read (Tape.step blank (M.vt.1 GSTapes.tRn) blank .left) = mark
      · rw [if_pos hcd, if_pos ((GSTapes.period_iff' hne hscan).1 hcd),
          GSTapes.p1Of'_eq hscan]
      · rw [if_neg hcd, if_neg (fun hcon => hcd ((GSTapes.period_iff' hne hscan).2 hcon)),
          GSTapes.qOf'_eq hscan]
    have hnh : zNextHead u v Text up M.z = M.z.2 := by unfold zNextHead; rw [if_neg hna]
    have hroom : M.z.1.pos - u.length + M.z.2 + gsShift k p₁ r M.z.1.q ≤ n := by
      rw [hss] at hidx; simp only at hidx; omega
    obtain ⟨w1, w2⟩ := vwalkXRFed_inv hne hb hmT hn (gsShift k p₁ r M.z.1.q) M
      (M.z.1.pos - u.length + M.z.2) hX hok hroom
    rw [hd, hnh, hss]
    refine ⟨?_, ?_, ?_⟩
    · rw [vwalkXRFed_U]; exact hpat
    · show Txt2Inv blank mark Text n (vwalkXRFed blank mark (gsShift k p₁ r M.z.1.q) M)
        (M.z.1.pos + gsShift k p₁ r M.z.1.q - u.length + M.z.2)
      rw [show M.z.1.pos + gsShift k p₁ r M.z.1.q - u.length + M.z.2
          = M.z.1.pos - u.length + M.z.2 + gsShift k p₁ r M.z.1.q from by omega]
      exact w1
    · show Ok2 n (vwalkXRFed blank mark (gsShift k p₁ r M.z.1.q) M)
        (M.z.1.pos + gsShift k p₁ r M.z.1.q - u.length + M.z.2)
      rw [show M.z.1.pos + gsShift k p₁ r M.z.1.q - u.length + M.z.2
          = M.z.1.pos - u.length + M.z.2 + gsShift k p₁ r M.z.1.q from by omega]
      exact w2

/-- **`VerifierFeedX.vencodes_stepFX` のジグザグ版**。 -/
theorem vencodes_stepFZ
    (hk : 0 < k) (hp : 0 < p₁) (hne : mark ≠ blank) (hv : 0 < v.length)
    (hend : endSym ∉ v) (hendu : endSym ∉ u) (hstartu : startSym ∉ u)
    (hse : startSym ≠ endSym) (hb : blank ∉ Text) (hmT : mark ∉ Text)
    (hscan : GSTapes.Encodes' blank startSym endSym mark v (padW blank Text M.m1) k p₁ r
      M.vt.1 M.z.1)
    (hpat : Tape.SeqView blank M.vt.2.U (startSym :: (u ++ [endSym])) (M.z.2 + 1))
    (hX : Txt2Inv blank mark Text n M (M.z.1.pos - u.length + M.z.2))
    (hok : Ok2 n M (M.z.1.pos - u.length + M.z.2))
    (hq : M.z.1.q ≤ v.length) (hc : M.z.2 ≤ u.length) (hpos : u.length ≤ M.z.1.pos)
    (hn : n ≤ Text.length) (hm1n : M.m1 ≤ n)
    (hd1 : M.z.1.pos + M.z.1.q ≤ M.m1)
    (hrd1 : M.z.1.q ≠ v.length → M.z.1.pos + M.z.1.q < M.m1) :
    GSTapes.Encodes' blank startSym endSym mark v (padW blank Text M.m1) k p₁ r
        (vscanOneZ blank startSym endSym mark u v k p₁ r Text up M).vt.1
        (scanStep v k p₁ r Text M.z.1) ∧
      Tape.SeqView blank (vscanOneZ blank startSym endSym mark u v k p₁ r Text up M).vt.2.U
        (startSym :: (u ++ [endSym])) (zNextHead u v Text up M.z + 1) ∧
      Txt2Inv blank mark Text n (vscanOneZ blank startSym endSym mark u v k p₁ r Text up M)
        ((scanStep v k p₁ r Text M.z.1).pos - u.length + zNextHead u v Text up M.z) ∧
      Ok2 n (vscanOneZ blank startSym endSym mark u v k p₁ r Text up M)
        ((scanStep v k p₁ r Text M.z.1).pos - u.length + zNextHead u v Text up M.z) := by
  have hm1 : M.m1 ≤ Text.length := le_trans hm1n hn
  have hstep : scanStep v k p₁ r (padW blank Text M.m1) M.z.1
      = scanStep v k p₁ r Text M.z.1 := scanStep_padW hm1 hrd1
  have hidx : (scanStep v k p₁ r Text M.z.1).pos + (scanStep v k p₁ r Text M.z.1).q ≤ M.m1 :=
    scanStep_index_le (p₁ := p₁) (r := r) (T := Text) hk hv hd1 hrd1
  have hfit : (scanStep v k p₁ r (padW blank Text M.m1) M.z.1).pos
      + (scanStep v k p₁ r (padW blank Text M.m1) M.z.1).q
      < (padW blank Text M.m1).length := by
    rw [hstep, padW_length hm1]; omega
  have hscan' := GSTapes.encodes_step' hk hne hend hscan hq hfit
  rw [hstep] at hscan'
  obtain ⟨e1, e2, e3⟩ := vExtFedZ_spec (up := up) hk hp hne hv hend hendu hstartu hse hb hmT
    hscan hpat hX hok hq hc hpos hn hm1n hd1 hrd1
  refine ⟨?_, e1, ⟨e2.view, e2.buf, e2.qinv, e2.qlist, e2.m2le, e2.hle⟩, e3⟩
  show GSTapes.Encodes' blank startSym endSym mark v (padW blank Text M.m1) k p₁ r
    (GSTapes.applyActs' blank
      (GSTapes.program' blank endSym mark k (vExtFedZ blank startSym endSym mark k up M).vt.1)
      (vExtFedZ blank startSym endSym mark k up M).vt.1) _
  rw [vExtFedZ_vt1]
  exact hscan'

/-- **`VerifierFeedX.vscanOneX_feedInv` のジグザグ版**。 -/
theorem vscanOneZ_feedInv
    (hk : 0 < k) (hp : 0 < p₁) (hne : mark ≠ blank) (hv : 0 < v.length)
    (hend : endSym ∉ v) (hendu : endSym ∉ u) (hstartu : startSym ∉ u)
    (hse : startSym ≠ endSym) (hb : blank ∉ Text) (hmT : mark ∉ Text)
    (hn : n ≤ Text.length)
    (hrd1 : M.z.1.q ≠ v.length → M.z.1.pos + M.z.1.q < M.m1)
    (h : VFeedInv' blank startSym endSym mark u v Text k p₁ r n M)
    (hok : Ok2 n M (M.z.1.pos - u.length + M.z.2)) :
    VFeedInv' blank startSym endSym mark u v Text k p₁ r n
        (vscanOneZ blank startSym endSym mark u v k p₁ r Text up M) ∧
      Ok2 n (vscanOneZ blank startSym endSym mark u v k p₁ r Text up M)
        ((vscanOneZ blank startSym endSym mark u v k p₁ r Text up M).z.1.pos - u.length
          + (vscanOneZ blank startSym endSym mark u v k p₁ r Text up M).z.2) := by
  obtain ⟨e1, e2, e3, e4⟩ := vencodes_stepFZ (up := up) hk hp hne hv hend hendu hstartu hse
    hb hmT h.scan h.pat h.txt2Inv hok h.qle h.cle h.posle hn h.m1le h.hd1 hrd1
  refine ⟨⟨?_, e2, ?_, ?_, ?_, ?_, ?_, e3.buf, e3.qinv, e3.qlist, e3.m2le,
    ?_, ?_, ?_, ?_, ?_⟩, e4⟩
  · rw [vscanOneZ_m1]; exact e1
  · exact e3.view
  · rw [vscanOneZ_R1qt, vscanOneZ_Q1]; exact h.buf1
  · rw [vscanOneZ_Q1]; exact h.qinv1
  · rw [vscanOneZ_Q1, vscanOneZ_m1]; exact h.qlist1
  · rw [vscanOneZ_m1]; exact h.m1le
  · show (scanStep v k p₁ r Text M.z.1).pos + (scanStep v k p₁ r Text M.z.1).q
      ≤ (vscanOneZ blank startSym endSym mark u v k p₁ r Text up M).m1
    rw [vscanOneZ_m1]
    exact scanStep_index_le (p₁ := p₁) (r := r) (T := Text) hk hv h.hd1 hrd1
  · exact e3.hle
  · show (scanStep v k p₁ r Text M.z.1).q ≤ v.length
    exact scanStep_q_le h.qle
  · exact zNextHead_le (v := v) (Text := Text) (up := up) h.cle
  · show u.length ≤ (scanStep v k p₁ r Text M.z.1).pos
    exact le_trans h.posle (scanStep_pos_le v k p₁ r Text M.z.1)

/-- **`VerifierFeedX.fstepX_feedInv` のジグザグ版**。 -/
theorem fstepZ_feedInv
    (hk : 0 < k) (hp : 0 < p₁) (hne : mark ≠ blank) (hv : 0 < v.length)
    (hend : endSym ∉ v) (hendu : endSym ∉ u) (hstartu : startSym ∉ u)
    (hse : startSym ≠ endSym) (hb : blank ∉ Text) (hmT : mark ∉ Text)
    (hn : n ≤ Text.length)
    (h : VFeedInv' blank startSym endSym mark u v Text k p₁ r n M)
    (hok : Ok2 n M (M.z.1.pos - u.length + M.z.2))
    (he : Enabled v n M.z.1) :
    VFeedInv' blank startSym endSym mark u v Text k p₁ r n
        (fstepZ blank startSym endSym mark u v k p₁ r n Text up M) ∧
      Ok2 n (fstepZ blank startSym endSym mark u v k p₁ r n Text up M)
        ((fstepZ blank startSym endSym mark u v k p₁ r n Text up M).z.1.pos - u.length
          + (fstepZ blank startSym endSym mark u v k p₁ r n Text up M).z.2) := by
  have hfF := vfillIf1'_feedInv (u := u) (v := v) (k := k) (p₁ := p₁) (r := r) hne hn h
  have hfok : Ok2 n (vfillIf1' blank mark n M)
      ((vfillIf1' blank mark n M).z.1.pos - u.length + (vfillIf1' blank mark n M).z.2) := by
    unfold vfillIf1'
    split_ifs with hcc
    · exact hok
    · exact hok
  exact vscanOneZ_feedInv (up := up) hk hp hne hv hend hendu hstartu hse hb hmT hn
    (vfillIf1'_ready h he) hfF hfok

end StepSpec

/-! ## 5. 費用の点ごとの上界 -/

/-- 供給つきジグザグの償却係数 `A_Z = 8k + 47`
（走査プログラム `8k+13` ＋ `Txt2` の右移動 `34`）。 -/
def zfA (k : ℕ) : ℕ := 8 * k + 47

/-- 供給つきジグザグの償却定数 `B_Z = 181`（`140 + 8 + 33`）。 -/
def zfB : ℕ := 181

example : zfA 8 = 111 := by norm_num [zfA]

section CostBound

variable {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)} {k p₁ r n : ℕ}
  {M : VMachine' sc}

/-- **一歩の費用の点ごとの上界**：`fcostZ ≤ A_Z·ΔΦ + B_Z`。

`VerifierFeedX.fcostX_amortized` は `Ψ = 2·checked` を含む **償却形** でしか
成り立たなかった（`U` の巻き戻しのため）。ジグザグでは `U` を巻き戻さないので、
**ポテンシャル `Ψ` を一切使わずに、走査状態の `ΔΦ` だけで点ごとに**抑えられる。
これが `PalPeg.PointwiseGap.rewind_not_pointwise` の壁を回避するという主張の、
供給つき機械での実現である。 -/
theorem fcostZ_le (hk : 0 < k) (hp : 0 < p₁) (hne : mark ≠ blank) (hend : endSym ∉ v)
    (hn : n ≤ Text.length)
    (h : VFeedInv' blank startSym endSym mark u v Text k p₁ r n M)
    (he : Enabled v n M.z.1) :
    fcostZ blank endSym mark k n M
      ≤ zfA k * (Phi k (scanStep v k p₁ r Text M.z.1) - Phi k M.z.1) + zfB := by
  have hfF := vfillIf1'_feedInv (u := u) (v := v) (k := k) (p₁ := p₁) (r := r) hne hn h
  have hrd1 := vfillIf1'_ready h he
  set M' := vfillIf1' blank mark n M with hM'
  have hzz : M'.z = M.z := vfillIf1'_z blank mark n M
  have hm1 : M'.m1 ≤ Text.length := le_trans hfF.m1le hn
  have hstep : scanStep v k p₁ r (padW blank Text M'.m1) M'.z.1
      = scanStep v k p₁ r Text M'.z.1 := scanStep_padW hm1 hrd1
  have hscan' : GSTapes.Encodes' blank startSym endSym mark v (padW blank Text M'.m1) k p₁ r
      M'.vt.1 M.z.1 := by rw [← hzz]; exact hfF.scan
  have hqle' : M.z.1.q ≤ v.length := by rw [← hzz]; exact hfF.qle
  have hprog := GSTapes.program_cost' (p₁ := p₁) (r := r) hk hne hend hscan' hqle'
  rw [show scanStep v k p₁ r (padW blank Text M'.m1) M.z.1
      = scanStep v k p₁ r Text M.z.1 from by rw [← hzz]; exact hstep] at hprog
  unfold fcostZ fextZ zfA zfB
  rw [← hM']
  set D := Phi k (scanStep v k p₁ r Text M.z.1) - Phi k M.z.1 with hD
  have hD1 : 1 ≤ D := by
    have := phi_step_lt (v := v) (T := Text) (p₁ := p₁) (r := r) hk hp M.z.1
    omega
  have h34 : 34 ≤ 34 * D := by
    have := Nat.mul_le_mul_left 34 hD1; omega
  have e : (8 * k + 47) * D = (8 * k + 13) * D + 34 * D := by ring
  by_cases hadv : Tape.read (M'.vt.1 GSTapes.tP) ≠ endSym ∧
      Tape.read (M'.vt.1 GSTapes.tP) = Tape.read (M'.vt.1 GSTapes.tT)
  · rw [if_pos hadv]; omega
  · rw [if_neg hadv]
    have hna : ¬ (M.z.1.q ≠ v.length ∧ Text[M.z.1.pos + M.z.1.q]? = v[M.z.1.q]?) := by
      rintro ⟨hcon1, hcon2⟩
      refine hadv ((GSTapes.advance_iff' hend hscan' hqle').2 ⟨hcon1, ?_⟩)
      rw [padW_getElem?_of_lt (blank := blank) hm1
        (by rw [← hzz]; exact hrd1 (by rw [hzz]; exact hcon1))]
      exact hcon2
    have hss : scanStep v k p₁ r Text M.z.1
        = (⟨M.z.1.pos + gsShift k p₁ r M.z.1.q, gsNextQ k p₁ r M.z.1.q⟩ : ScanState) :=
      GSTapes.scanStep_shift hna
    have hd : GSVTapes.vDelta' blank mark k M'.vt.1 = gsShift k p₁ r M.z.1.q := by
      unfold GSVTapes.vDelta' gsShift
      by_cases hcd : Tape.read (Tape.step blank (M'.vt.1 GSTapes.tAn) blank .left) = mark ∧
          Tape.read (Tape.step blank (M'.vt.1 GSTapes.tRn) blank .left) = mark
      · rw [if_pos hcd, if_pos ((GSTapes.period_iff' hne hscan').1 hcd),
          GSTapes.p1Of'_eq hscan']
      · rw [if_neg hcd,
          if_neg (fun hcon => hcd ((GSTapes.period_iff' hne hscan').2 hcon)),
          GSTapes.qOf'_eq hscan']
    have hsh : gsShift k p₁ r M.z.1.q ≤ D := by
      have hg := GSVTapes.gsShift_le_dPhi (p₁ := p₁) (r := r) hk M.z.1
      rw [hD, hss]
      exact hg
    rw [hd]
    have h34' : 34 * gsShift k p₁ r M.z.1.q ≤ 34 * D := Nat.mul_le_mul_left 34 hsh
    omega

/-- **前進（比較成功）枝の費用**：`|program'| ≤ 8k+21`（`ΔΦ = 1`）に
`zUnitsFed` の `140` と歩頭の供給 `33` を足して `≤ 8k+194`。 -/
theorem fcostZ_adv_le (hk : 0 < k) (hne : mark ≠ blank) (hend : endSym ∉ v)
    (hn : n ≤ Text.length)
    (h : VFeedInv' blank startSym endSym mark u v Text k p₁ r n M)
    (he : Enabled v n M.z.1)
    (hadv : M.z.1.q ≠ v.length ∧ Text[M.z.1.pos + M.z.1.q]? = v[M.z.1.q]?) :
    fcostZ blank endSym mark k n M ≤ 8 * k + 194 := by
  have hfF := vfillIf1'_feedInv (u := u) (v := v) (k := k) (p₁ := p₁) (r := r) hne hn h
  have hrd1 := vfillIf1'_ready h he
  set M' := vfillIf1' blank mark n M with hM'
  have hzz : M'.z = M.z := vfillIf1'_z blank mark n M
  have hm1 : M'.m1 ≤ Text.length := le_trans hfF.m1le hn
  have hstep : scanStep v k p₁ r (padW blank Text M'.m1) M'.z.1
      = scanStep v k p₁ r Text M'.z.1 := scanStep_padW hm1 hrd1
  have hscan' : GSTapes.Encodes' blank startSym endSym mark v (padW blank Text M'.m1) k p₁ r
      M'.vt.1 M.z.1 := by rw [← hzz]; exact hfF.scan
  have hqle' : M.z.1.q ≤ v.length := by rw [← hzz]; exact hfF.qle
  have hprog := GSTapes.program_cost' (p₁ := p₁) (r := r) hk hne hend hscan' hqle'
  rw [show scanStep v k p₁ r (padW blank Text M'.m1) M.z.1
      = scanStep v k p₁ r Text M.z.1 from by rw [← hzz]; exact hstep] at hprog
  have hss : scanStep v k p₁ r Text M.z.1 = (⟨M.z.1.pos, M.z.1.q + 1⟩ : ScanState) :=
    GSTapes.scanStep_adv hadv
  have hD : Phi k (scanStep v k p₁ r Text M.z.1) - Phi k M.z.1 = 1 := by
    rw [hss]
    show (k + 1) * M.z.1.pos + (M.z.1.q + 1) - ((k + 1) * M.z.1.pos + M.z.1.q) = 1
    omega
  rw [hD, Nat.mul_one] at hprog
  have hadvT : Tape.read (M'.vt.1 GSTapes.tP) ≠ endSym ∧
      Tape.read (M'.vt.1 GSTapes.tP) = Tape.read (M'.vt.1 GSTapes.tT) := by
    refine (GSTapes.advance_iff' hend hscan' hqle').2 ⟨hadv.1, ?_⟩
    rw [padW_getElem?_of_lt (blank := blank) hm1
      (by rw [← hzz]; exact hrd1 (by rw [hzz]; exact hadv.1))]
    exact hadv.2
  unfold fcostZ fextZ
  rw [← hM', if_pos hadvT]
  omega

end CostBound

/-! ## 6. 公理の確認 -/

#print axioms zUnitFed_spec
#print axioms zUnitsFed_spec
#print axioms zUnitsFed_cost
#print axioms vExtFedZ_cost
#print axioms vExtFedZ_spec
#print axioms vencodes_stepFZ
#print axioms vscanOneZ_feedInv
#print axioms fstepZ_feedInv
#print axioms fstepZ_cost
#print axioms fcostZ_le
#print axioms fcostZ_adv_le

end VerifierFeedZ
end PalPeg
