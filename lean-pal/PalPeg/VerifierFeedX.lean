import PalPeg.VerifierFeed
import PalPeg.GSVerifierFused

/-!
# 供給つきの `vprogramX` 一歩 (`VerifierFeedX`)

`PalPeg.VerifierFeed` §16–19 は、一歩の動作列 `GSVTapes.vprogram'` を
**`.X .right` のたびに `Txt2` を養いながら** 実行する機械 `vscanOne''` を与えた
（`vscanApply`（走査 8 本へ `program'` を一括適用）∘ `vExtFed`（検証器 2 本＋供給））。

本ファイルは、その **`GSVTapes.vprogramX` 版** `vscanOneX` を同じ構成で与える。
`vprogramX` が `vprogram'` と違うのは **ずらし枝だけ**であり、

* 比較枝：`advActs ++ vcomp2Acts` ＝ `vprogram'` と同一 → `vcomp2Fed` をそのまま使う。
* ずらし枝：`probe ×2` ＋ 相乗りループ（`perLoop1X` / `resLoopX`：`Txt2` を
  ちょうど `d = gsShift` 歩 **右**へ）＋ `uxWalk`（`(U .left, X .left)` を
  `c+1` 回、続けて `(U .right, X .right)`）。

`vscanOne''` が走査段の動作を `vscanApply` で一括適用し `Txt2` の移動だけを
細粒度に扱うのと同じ粒度で、ずらし枝の供給つき実現を

  `vwalkFedX c d = (X .right ＋供給) を d 回 → U を c+1 左 → Txt2 を c+1 左`
  `→ U を 1 右 → (X .right ＋供給)`

と定める（`uxWalk` の `Txt2` 左移動は供給不要、最後の右 1 歩だけ供給がつく）。
正味の効果は `vwalkFed`（`uWalk ++ txt2Rewind` の供給つき版）と同じ
——`U` は添字 `0+1`（`checked = 0`）へ、`Txt2` は `pos + d - |u| + 0` へ。

## 費用

* 比較枝：`vcomp2Fed ≤ 70`
* ずらし枝：`34*d + 2*c + 37`（`34 = 1 + 33`（`Txt2` 1 歩＋供給））

に走査段の `program'` の適用（`|program'|`）と歩頭の供給（`33`）を足したものが
一歩の費用 `fcostX` である（`§4`）。
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg
namespace VerifierFeedX

open PegSeparation.RealTimeTM
open PalPeg.TextFeed
open PalPeg.VerifierFeed

variable {sc : ℕ}

/-! ## 1. ずらし枝の供給つき実現 -/

/-- **`vprogramX` のずらし枝（相乗りループ ＋ `uxWalk`）の供給つき実現**。
`c = checked`, `d = gsShift`。 -/
def vwalkFedX (blank mark : Fin sc) (c d : ℕ) (M : VMachine' sc) : VMachine' sc :=
  vstepXR blank mark (vmoveUR blank
    (vmoveXLN blank (c + 1) (vmoveULN blank (c + 1) (vwalkXRFed blank mark d M))))

@[simp] theorem vwalkFedX_z (blank mark : Fin sc) (c d : ℕ) (M : VMachine' sc) :
    (vwalkFedX blank mark c d M).z = M.z := by
  unfold vwalkFedX
  rw [vstepXR_z]
  show (vwalkXRFed blank mark d M).z = M.z
  rw [vwalkXRFed_z]

@[simp] theorem vwalkFedX_m1 (blank mark : Fin sc) (c d : ℕ) (M : VMachine' sc) :
    (vwalkFedX blank mark c d M).m1 = M.m1 := by
  unfold vwalkFedX
  rw [vstepXR_m1]
  show (vwalkXRFed blank mark d M).m1 = M.m1
  rw [vwalkXRFed_m1]

@[simp] theorem vwalkFedX_vt1 (blank mark : Fin sc) (c d : ℕ) (M : VMachine' sc) :
    (vwalkFedX blank mark c d M).vt.1 = M.vt.1 := by
  unfold vwalkFedX
  rw [vstepXR_vt1]
  show (vwalkXRFed blank mark d M).vt.1 = M.vt.1
  rw [vwalkXRFed_vt1]

@[simp] theorem vwalkFedX_R1qt (blank mark : Fin sc) (c d : ℕ) (M : VMachine' sc) :
    (vwalkFedX blank mark c d M).R1.qt = M.R1.qt := by
  unfold vwalkFedX
  rw [vstepXR_R1qt]
  show (vwalkXRFed blank mark d M).R1.qt = M.R1.qt
  rw [vwalkXRFed_R1qt]

@[simp] theorem vwalkFedX_Q1 (blank mark : Fin sc) (c d : ℕ) (M : VMachine' sc) :
    (vwalkFedX blank mark c d M).Q1 = M.Q1 := by
  unfold vwalkFedX
  rw [vstepXR_Q1]
  show (vwalkXRFed blank mark d M).Q1 = M.Q1
  rw [vwalkXRFed_Q1]

theorem vwalkFedX_cost (blank mark : Fin sc) (c d : ℕ) (M : VMachine' sc) :
    (vwalkFedX blank mark c d M).cost ≤ M.cost + (34 * d + 2 * c + 37) := by
  have h1 := vwalkXRFed_cost blank mark d M
  set M1 := vwalkXRFed blank mark d M with hM1
  have h2 : (vmoveULN blank (c + 1) M1).cost = M1.cost + (c + 1) := by
    show M1.R1.cost + (c + 1) + M1.R2.cost = M1.R1.cost + M1.R2.cost + (c + 1)
    omega
  set M2 := vmoveULN blank (c + 1) M1 with hM2
  have h3 : (vmoveXLN blank (c + 1) M2).cost = M2.cost + (c + 1) := by
    show M2.R1.cost + (c + 1) + M2.R2.cost = M2.R1.cost + M2.R2.cost + (c + 1)
    omega
  set M3 := vmoveXLN blank (c + 1) M2 with hM3
  have h4 : (vmoveUR blank M3).cost = M3.cost + 1 := by
    show M3.R1.cost + 1 + M3.R2.cost = M3.R1.cost + M3.R2.cost + 1
    omega
  have h5 := vstepXR_cost blank mark (vmoveUR blank M3)
  show (vstepXR blank mark (vmoveUR blank M3)).cost ≤ M.cost + (34 * d + 2 * c + 37)
  omega

/-- **ずらし枝の実現**：`U` は添字 `0+1` へ、`Txt2` は `pos + d - |u| + 0` へ。
`VerifierFeed.vwalkFed_spec` の `vprogramX` 版。 -/
theorem vwalkFedX_spec {blank startSym endSym mark : Fin sc} {u Text : List (Fin sc)}
    {n pos c d : ℕ} {M : VMachine' sc} (hmb : mark ≠ blank) (hb : blank ∉ Text)
    (hmT : mark ∉ Text) (hn : n ≤ Text.length)
    (hU : Tape.SeqView blank M.vt.2.U (startSym :: (u ++ [endSym])) (c + 1))
    (hX : Txt2Inv blank mark Text n M (pos - u.length + c))
    (hok : Ok2 n M (pos - u.length + c))
    (hc : c ≤ u.length) (hpos : u.length ≤ pos) (hd : 1 ≤ d) (hroom : pos + d ≤ n) :
    Tape.SeqView blank (vwalkFedX blank mark c d M).vt.2.U
        (startSym :: (u ++ [endSym])) (0 + 1) ∧
      Txt2Inv blank mark Text n (vwalkFedX blank mark c d M) (pos + d - u.length + 0) ∧
      Ok2 n (vwalkFedX blank mark c d M) (pos + d - u.length + 0) := by
  -- 相乗りループ：`Txt2` を右へ `d`（各歩に供給）
  obtain ⟨i1, i2⟩ := vwalkXRFed_inv hmb hb hmT hn d M (pos - u.length + c) hX hok (by omega)
  set M1 := vwalkXRFed blank mark d M with hM1
  have hU1 : Tape.SeqView blank M1.vt.2.U (startSym :: (u ++ [endSym])) (c + 1) := by
    rw [hM1, vwalkXRFed_U]; exact hU
  -- `uxWalk` の左移動：`U` を `c+1`、`Txt2` を `c+1`
  have hU2 : Tape.SeqView blank (vmoveULN blank (c + 1) M1).vt.2.U
      (startSym :: (u ++ [endSym])) 0 := by
    show Tape.SeqView blank (GSTapes.leftN blank M1.vt.2.U (c + 1)) _ 0
    refine GSTapes.seq_leftN (c + 1) M1.vt.2.U 0 ?_
    rw [show 0 + (c + 1) = c + 1 from by omega]
    exact hU1
  set M2 := vmoveULN blank (c + 1) M1 with hM2
  have hX2 : Txt2Inv blank mark Text n M2 (pos - u.length + c + d) :=
    ⟨i1.view, i1.buf, i1.qinv, i1.qlist, i1.m2le, i1.hle⟩
  have hok2 : Ok2 n M2 (pos - u.length + c + d) := i2
  have hidx : pos + d - u.length - 1 + (c + 1) = pos - u.length + c + d := by omega
  have hX3 : Txt2Inv blank mark Text n (vmoveXLN blank (c + 1) M2)
      (pos + d - u.length - 1) := by
    refine ⟨?_, hX2.buf, hX2.qinv, hX2.qlist, hX2.m2le, ?_⟩
    · show Tape.SeqView blank (GSTapes.leftN blank M2.vt.2.Txt2 (c + 1))
        (padW blank Text M2.m2) (pos + d - u.length - 1)
      refine GSTapes.seq_leftN (c + 1) M2.vt.2.Txt2 (pos + d - u.length - 1) ?_
      rw [hidx]
      exact hX2.view
    · show pos + d - u.length - 1 ≤ M2.m2
      have := hX2.hle
      omega
  have hok3 : Ok2 n (vmoveXLN blank (c + 1) M2) (pos + d - u.length - 1) := by
    show pos + d - u.length - 1 < M2.m2 ∨ M2.m2 = n
    rcases hok2 with h1 | h1
    · left; omega
    · right; exact h1
  set M3 := vmoveXLN blank (c + 1) M2 with hM3
  -- `U` を 1 右（添字 `0+1`）
  have hU4 : Tape.SeqView blank (vmoveUR blank M3).vt.2.U
      (startSym :: (u ++ [endSym])) (0 + 1) := by
    show Tape.SeqView blank (Tape.step blank M3.vt.2.U M3.vt.2.U.focus .right) _ (0 + 1)
    refine Tape.seq_move_right (by exact hU2) ?_
    simp only [List.length_cons, List.length_append]
    omega
  have hX4 : Txt2Inv blank mark Text n (vmoveUR blank M3) (pos + d - u.length - 1) :=
    ⟨hX3.view, hX3.buf, hX3.qinv, hX3.qlist, hX3.m2le, hX3.hle⟩
  have hok4 : Ok2 n (vmoveUR blank M3) (pos + d - u.length - 1) := hok3
  -- 最後の `.X .right` ＋供給
  obtain ⟨j1, j2⟩ := vstepXR_inv hmb hb hmT hn hX4 hok4 (by omega)
  rw [show pos + d - u.length - 1 + 1 = pos + d - u.length + 0 from by omega] at j1 j2
  refine ⟨?_, j1, j2⟩
  show Tape.SeqView blank (vstepXR blank mark (vmoveUR blank M3)).vt.2.U _ (0 + 1)
  rw [vstepXR_U]
  exact hU4

/-! ## 2. 検証器 2 本への作用（`vprogramX` 版） -/

/-- **`VerifierFeed.vExtFed` の `vprogramX` 版**：比較枝は同一、ずらし枝は
相乗りループ ＋ `uxWalk`。 -/
def vExtFedX (blank endSym mark : Fin sc) (k : ℕ) (M : VMachine' sc) : VMachine' sc :=
  if Tape.read (M.vt.1 GSTapes.tP) ≠ endSym ∧
      Tape.read (M.vt.1 GSTapes.tP) = Tape.read (M.vt.1 GSTapes.tT) then
    vcomp2Fed blank endSym mark M
  else vwalkFedX blank mark (GSVTapes.cOf M.vt.2) (GSVTapes.vDelta' blank mark k M.vt.1) M

@[simp] theorem vExtFedX_z (blank endSym mark : Fin sc) (k : ℕ) (M : VMachine' sc) :
    (vExtFedX blank endSym mark k M).z = M.z := by
  unfold vExtFedX; split_ifs
  · rw [vcomp2Fed, vcompFed_z, vcompFed_z]
  · rw [vwalkFedX_z]

@[simp] theorem vExtFedX_m1 (blank endSym mark : Fin sc) (k : ℕ) (M : VMachine' sc) :
    (vExtFedX blank endSym mark k M).m1 = M.m1 := by
  unfold vExtFedX; split_ifs
  · rw [vcomp2Fed, vcompFed_m1, vcompFed_m1]
  · rw [vwalkFedX_m1]

@[simp] theorem vExtFedX_vt1 (blank endSym mark : Fin sc) (k : ℕ) (M : VMachine' sc) :
    (vExtFedX blank endSym mark k M).vt.1 = M.vt.1 := by
  unfold vExtFedX; split_ifs
  · rw [vcomp2Fed, vcompFed_vt1, vcompFed_vt1]
  · rw [vwalkFedX_vt1]

@[simp] theorem vExtFedX_Q1 (blank endSym mark : Fin sc) (k : ℕ) (M : VMachine' sc) :
    (vExtFedX blank endSym mark k M).Q1 = M.Q1 := by
  unfold vExtFedX; split_ifs
  · rw [vcomp2Fed, vcompFed_Q1, vcompFed_Q1]
  · rw [vwalkFedX_Q1]

@[simp] theorem vExtFedX_R1qt (blank endSym mark : Fin sc) (k : ℕ) (M : VMachine' sc) :
    (vExtFedX blank endSym mark k M).R1.qt = M.R1.qt := by
  unfold vExtFedX; split_ifs
  · rw [vcomp2Fed, vcompFed_R1qt, vcompFed_R1qt]
  · rw [vwalkFedX_R1qt]

/-- 検証器 2 本への作用の費用（枝別）。 -/
def fextX (blank endSym mark : Fin sc) (k : ℕ) (M : VMachine' sc) : ℕ :=
  if Tape.read (M.vt.1 GSTapes.tP) ≠ endSym ∧
      Tape.read (M.vt.1 GSTapes.tP) = Tape.read (M.vt.1 GSTapes.tT) then 70
  else 34 * GSVTapes.vDelta' blank mark k M.vt.1 + 2 * GSVTapes.cOf M.vt.2 + 37

theorem vExtFedX_cost (blank endSym mark : Fin sc) (k : ℕ) (M : VMachine' sc) :
    (vExtFedX blank endSym mark k M).cost ≤ M.cost + fextX blank endSym mark k M := by
  unfold vExtFedX fextX
  split_ifs
  · exact vcomp2Fed_cost blank endSym mark M
  · exact vwalkFedX_cost blank mark (GSVTapes.cOf M.vt.2)
      (GSVTapes.vDelta' blank mark k M.vt.1) M

/-- **`VerifierFeed.vExtFed_spec` の `vprogramX` 版**。 -/
theorem vExtFedX_spec {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)}
    {k p₁ r n : ℕ} {M : VMachine' sc}
    (hk : 0 < k) (hp : 0 < p₁) (hne : mark ≠ blank) (hv : 0 < v.length)
    (hend : endSym ∉ v) (hendu : endSym ∉ u) (hb : blank ∉ Text) (hmT : mark ∉ Text)
    (hscan : GSTapes.Encodes' blank startSym endSym mark v (padW blank Text M.m1) k p₁ r
      M.vt.1 M.z.1)
    (hpat : Tape.SeqView blank M.vt.2.U (startSym :: (u ++ [endSym])) (M.z.2 + 1))
    (hX : Txt2Inv blank mark Text n M (M.z.1.pos - u.length + M.z.2))
    (hok : Ok2 n M (M.z.1.pos - u.length + M.z.2))
    (hq : M.z.1.q ≤ v.length) (hc : M.z.2 ≤ u.length) (hpos : u.length ≤ M.z.1.pos)
    (hn : n ≤ Text.length) (hm1n : M.m1 ≤ n)
    (hd1 : M.z.1.pos + M.z.1.q ≤ M.m1)
    (hrd1 : M.z.1.q ≠ v.length → M.z.1.pos + M.z.1.q < M.m1) :
    Tape.SeqView blank (vExtFedX blank endSym mark k M).vt.2.U
        (startSym :: (u ++ [endSym])) ((vStep u v k p₁ r Text M.z).2 + 1) ∧
      Txt2Inv blank mark Text n (vExtFedX blank endSym mark k M)
        ((vStep u v k p₁ r Text M.z).1.pos - u.length + (vStep u v k p₁ r Text M.z).2) ∧
      Ok2 n (vExtFedX blank endSym mark k M)
        ((vStep u v k p₁ r Text M.z).1.pos - u.length + (vStep u v k p₁ r Text M.z).2) := by
  have hm1 : M.m1 ≤ Text.length := le_trans hm1n hn
  have hidx : (scanStep v k p₁ r Text M.z.1).pos + (scanStep v k p₁ r Text M.z.1).q ≤ M.m1 :=
    scanStep_index_le (p₁ := p₁) (r := r) (T := Text) hk hv hd1 hrd1
  unfold vExtFedX
  by_cases hadv : Tape.read (M.vt.1 GSTapes.tP) ≠ endSym ∧
      Tape.read (M.vt.1 GSTapes.tP) = Tape.read (M.vt.1 GSTapes.tT)
  · rw [if_pos hadv]
    obtain ⟨ha1, ha2⟩ := (GSTapes.advance_iff' hend hscan hq).1 hadv
    have haT : Text[M.z.1.pos + M.z.1.q]? = v[M.z.1.q]? := by
      rw [← padW_getElem?_of_lt (blank := blank) hm1 (hrd1 ha1)]; exact ha2
    have hss : scanStep v k p₁ r Text M.z.1
        = (⟨M.z.1.pos, M.z.1.q + 1⟩ : ScanState) := GSTapes.scanStep_adv ⟨ha1, haT⟩
    have hvs : vStep u v k p₁ r Text M.z
        = (scanStep v k p₁ r Text M.z.1,
            vComp u Text M.z.1.pos (vComp u Text M.z.1.pos M.z.2)) := by
      unfold vStep; rw [if_neg ha1, if_pos haT]
    have hroom : M.z.1.pos < n := by
      have := hrd1 ha1; omega
    obtain ⟨c1, c2, c3⟩ := vcomp2Fed_spec (startSym := startSym) (pos := M.z.1.pos)
      hne hb hmT hendu hn hpat hX hok hc hpos hroom
    rw [hvs]
    refine ⟨c1, ?_, ?_⟩
    · show Txt2Inv blank mark Text n (vcomp2Fed blank endSym mark M)
        ((scanStep v k p₁ r Text M.z.1).pos - u.length
          + vComp u Text M.z.1.pos (vComp u Text M.z.1.pos M.z.2))
      rw [hss]; exact c2
    · show Ok2 n (vcomp2Fed blank endSym mark M)
        ((scanStep v k p₁ r Text M.z.1).pos - u.length
          + vComp u Text M.z.1.pos (vComp u Text M.z.1.pos M.z.2))
      rw [hss]; exact c3
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
    have hcc : GSVTapes.cOf M.vt.2 = M.z.2 := GSVTapes.cOf_eq hpat
    have hroom : M.z.1.pos + gsShift k p₁ r M.z.1.q ≤ n := by
      rw [hss] at hidx
      simp only at hidx
      omega
    have hdpos : 1 ≤ gsShift k p₁ r M.z.1.q := by
      unfold gsShift
      split_ifs
      · omega
      · exact le_max_left _ _
    obtain ⟨w1, w2, w3⟩ := vwalkFedX_spec (startSym := startSym) (endSym := endSym) (u := u)
      (pos := M.z.1.pos) (c := M.z.2) (d := gsShift k p₁ r M.z.1.q)
      hne hb hmT hn hpat hX hok hc hpos hdpos hroom
    rw [hd, hcc, GSVTapes.vStep_shift hna]
    refine ⟨w1, ?_, ?_⟩
    · show Txt2Inv blank mark Text n
        (vwalkFedX blank mark M.z.2 (gsShift k p₁ r M.z.1.q) M)
        ((scanStep v k p₁ r Text M.z.1).pos - u.length + 0)
      rw [hss]; exact w2
    · show Ok2 n (vwalkFedX blank mark M.z.2 (gsShift k p₁ r M.z.1.q) M)
        ((scanStep v k p₁ r Text M.z.1).pos - u.length + 0)
      rw [hss]; exact w3

/-! ## 3. 一歩 `vscanOneX` -/

/-- **供給つき `vprogramX` の一歩**（`VerifierFeed.vscanOne''` の X 版）。 -/
def vscanOneX (blank endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r : ℕ)
    (Text : List (Fin sc)) (M : VMachine' sc) : VMachine' sc :=
  { vscanApply blank endSym mark k (vExtFedX blank endSym mark k M) with
    z := vStep u v k p₁ r Text M.z }

@[simp] theorem vscanOneX_z (blank endSym mark : Fin sc) (u v : List (Fin sc))
    (k p₁ r : ℕ) (Text : List (Fin sc)) (M : VMachine' sc) :
    (vscanOneX blank endSym mark u v k p₁ r Text M).z = vStep u v k p₁ r Text M.z := rfl

@[simp] theorem vscanOneX_m1 (blank endSym mark : Fin sc) (u v : List (Fin sc))
    (k p₁ r : ℕ) (Text : List (Fin sc)) (M : VMachine' sc) :
    (vscanOneX blank endSym mark u v k p₁ r Text M).m1 = M.m1 := by
  show (vExtFedX blank endSym mark k M).m1 = M.m1
  rw [vExtFedX_m1]

@[simp] theorem vscanOneX_Q1 (blank endSym mark : Fin sc) (u v : List (Fin sc))
    (k p₁ r : ℕ) (Text : List (Fin sc)) (M : VMachine' sc) :
    (vscanOneX blank endSym mark u v k p₁ r Text M).Q1 = M.Q1 := by
  show (vExtFedX blank endSym mark k M).Q1 = M.Q1
  rw [vExtFedX_Q1]

@[simp] theorem vscanOneX_R1qt (blank endSym mark : Fin sc) (u v : List (Fin sc))
    (k p₁ r : ℕ) (Text : List (Fin sc)) (M : VMachine' sc) :
    (vscanOneX blank endSym mark u v k p₁ r Text M).R1.qt = M.R1.qt := by
  show (vExtFedX blank endSym mark k M).R1.qt = M.R1.qt
  rw [vExtFedX_R1qt]

theorem vscanOneX_vt1 (blank endSym mark : Fin sc) (u v : List (Fin sc))
    (k p₁ r : ℕ) (Text : List (Fin sc)) (M : VMachine' sc) :
    (vscanOneX blank endSym mark u v k p₁ r Text M).vt.1
      = GSTapes.applyActs' blank (GSTapes.program' blank endSym mark k M.vt.1) M.vt.1 := by
  show GSTapes.applyActs' blank
      (GSTapes.program' blank endSym mark k (vExtFedX blank endSym mark k M).vt.1)
      (vExtFedX blank endSym mark k M).vt.1 = _
  rw [vExtFedX_vt1]

theorem vscanOneX_vt2 (blank endSym mark : Fin sc) (u v : List (Fin sc))
    (k p₁ r : ℕ) (Text : List (Fin sc)) (M : VMachine' sc) :
    (vscanOneX blank endSym mark u v k p₁ r Text M).vt.2
      = (vExtFedX blank endSym mark k M).vt.2 := rfl

/-- **一歩の費用**：走査段への `program'` の適用 ＋ 検証器 2 本への作用。 -/
theorem vscanOneX_cost (blank endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r : ℕ)
    (Text : List (Fin sc)) (M : VMachine' sc) :
    (vscanOneX blank endSym mark u v k p₁ r Text M).cost
      ≤ M.cost + ((GSTapes.program' blank endSym mark k M.vt.1).length
        + fextX blank endSym mark k M) := by
  have h1 := vExtFedX_cost blank endSym mark k M
  have hsa : ∀ N : VMachine' sc, (vscanApply blank endSym mark k N).cost
      = N.cost + (GSTapes.program' blank endSym mark k N.vt.1).length := by
    intro N
    show N.R1.cost + (GSTapes.program' blank endSym mark k N.vt.1).length + N.R2.cost
      = N.R1.cost + N.R2.cost + (GSTapes.program' blank endSym mark k N.vt.1).length
    omega
  have hz : (vscanOneX blank endSym mark u v k p₁ r Text M).cost
      = (vscanApply blank endSym mark k (vExtFedX blank endSym mark k M)).cost := rfl
  rw [hz, hsa, vExtFedX_vt1]
  omega

/-- **`VerifierFeed.vencodes_step''` の X 版**。 -/
theorem vencodes_stepFX {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)}
    {k p₁ r n : ℕ} {M : VMachine' sc}
    (hk : 0 < k) (hp : 0 < p₁) (hne : mark ≠ blank) (hv : 0 < v.length)
    (hend : endSym ∉ v) (hendu : endSym ∉ u) (hb : blank ∉ Text) (hmT : mark ∉ Text)
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
        (vscanOneX blank endSym mark u v k p₁ r Text M).vt.1
        (vStep u v k p₁ r Text M.z).1 ∧
      Tape.SeqView blank (vscanOneX blank endSym mark u v k p₁ r Text M).vt.2.U
        (startSym :: (u ++ [endSym])) ((vStep u v k p₁ r Text M.z).2 + 1) ∧
      Txt2Inv blank mark Text n (vscanOneX blank endSym mark u v k p₁ r Text M)
        ((vStep u v k p₁ r Text M.z).1.pos - u.length + (vStep u v k p₁ r Text M.z).2) ∧
      Ok2 n (vscanOneX blank endSym mark u v k p₁ r Text M)
        ((vStep u v k p₁ r Text M.z).1.pos - u.length + (vStep u v k p₁ r Text M.z).2) := by
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
  obtain ⟨e1, e2, e3⟩ := vExtFedX_spec (startSym := startSym) (p₁ := p₁) (r := r)
    hk hp hne hv hend hendu hb hmT hscan hpat hX hok hq hc hpos hn hm1n hd1 hrd1
  refine ⟨?_, e1, ⟨e2.view, e2.buf, e2.qinv, e2.qlist, e2.m2le, e2.hle⟩, e3⟩
  rw [vscanOneX_vt1, vStep_fst]
  exact hscan'

/-- **`VerifierFeed.vscanOne''_feedInv` の X 版**。 -/
theorem vscanOneX_feedInv {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)}
    {k p₁ r n : ℕ} {M : VMachine' sc} (hk : 0 < k) (hp : 0 < p₁) (hne : mark ≠ blank)
    (hv : 0 < v.length)
    (hend : endSym ∉ v) (hendu : endSym ∉ u) (hb : blank ∉ Text) (hmT : mark ∉ Text)
    (hn : n ≤ Text.length)
    (hrd1 : M.z.1.q ≠ v.length → M.z.1.pos + M.z.1.q < M.m1)
    (h : VFeedInv' blank startSym endSym mark u v Text k p₁ r n M)
    (hok : Ok2 n M (M.z.1.pos - u.length + M.z.2)) :
    VFeedInv' blank startSym endSym mark u v Text k p₁ r n
        (vscanOneX blank endSym mark u v k p₁ r Text M) ∧
      Ok2 n (vscanOneX blank endSym mark u v k p₁ r Text M)
        ((vscanOneX blank endSym mark u v k p₁ r Text M).z.1.pos - u.length
          + (vscanOneX blank endSym mark u v k p₁ r Text M).z.2) := by
  obtain ⟨e1, e2, e3, e4⟩ := vencodes_stepFX hk hp hne hv hend hendu hb hmT h.scan h.pat
    h.txt2Inv hok h.qle h.cle h.posle hn h.m1le h.hd1 hrd1
  refine ⟨⟨?_, e2, ?_, ?_, ?_, ?_, ?_, e3.buf, e3.qinv, e3.qlist, e3.m2le,
    ?_, ?_, ?_, ?_, ?_⟩, e4⟩
  · rw [vscanOneX_m1]; exact e1
  · exact e3.view
  · rw [vscanOneX_R1qt, vscanOneX_Q1]; exact h.buf1
  · rw [vscanOneX_Q1]; exact h.qinv1
  · rw [vscanOneX_Q1, vscanOneX_m1]; exact h.qlist1
  · rw [vscanOneX_m1]; exact h.m1le
  · show (vStep u v k p₁ r Text M.z).1.pos + (vStep u v k p₁ r Text M.z).1.q
      ≤ (vscanOneX blank endSym mark u v k p₁ r Text M).m1
    rw [vscanOneX_m1, vStep_fst]
    exact scanStep_index_le (p₁ := p₁) (r := r) (T := Text) hk hv h.hd1 hrd1
  · exact e3.hle
  · show (vStep u v k p₁ r Text M.z).1.q ≤ v.length
    rw [vStep_fst]; exact scanStep_q_le h.qle
  · exact GSVTapes.vStep_checked_le h.cle
  · show u.length ≤ (vStep u v k p₁ r Text M.z).1.pos
    rw [vStep_fst]; exact le_trans h.posle (scanStep_pos_le v k p₁ r Text M.z.1)

/-! ## 4. 供給つき一歩（歩頭の `vfillIf1'` 込み） -/

/-- **一歩（歩頭の供給込み）**：`StageMatcherTapes.fstep` の X 版。 -/
def fstepX (blank endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r n : ℕ)
    (Text : List (Fin sc)) (M : VMachine' sc) : VMachine' sc :=
  vscanOneX blank endSym mark u v k p₁ r Text (vfillIf1' blank mark n M)

/-- **一歩の費用**：`|program'| + fextX + 33`。 -/
def fcostX (blank endSym mark : Fin sc) (k n : ℕ) (M : VMachine' sc) : ℕ :=
  (GSTapes.program' blank endSym mark k (vfillIf1' blank mark n M).vt.1).length
    + fextX blank endSym mark k (vfillIf1' blank mark n M) + 33

theorem fstepX_z (blank endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r n : ℕ)
    (Text : List (Fin sc)) (M : VMachine' sc) :
    (fstepX blank endSym mark u v k p₁ r n Text M).z = vStep u v k p₁ r Text M.z := by
  rw [fstepX, vscanOneX_z, vfillIf1'_z]

theorem fstepX_cost (blank endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r n : ℕ)
    (Text : List (Fin sc)) (M : VMachine' sc) :
    (fstepX blank endSym mark u v k p₁ r n Text M).cost
      ≤ M.cost + fcostX blank endSym mark k n M := by
  have h1 := vfillIf1'_cost blank mark n M
  have h2 := vscanOneX_cost blank endSym mark u v k p₁ r Text (vfillIf1' blank mark n M)
  show (vscanOneX blank endSym mark u v k p₁ r Text (vfillIf1' blank mark n M)).cost ≤ _
  unfold fcostX
  omega

theorem fstepX_feedInv {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)}
    {k p₁ r n : ℕ} {M : VMachine' sc} (hk : 0 < k) (hp : 0 < p₁) (hne : mark ≠ blank)
    (hv : 0 < v.length) (hend : endSym ∉ v) (hendu : endSym ∉ u) (hb : blank ∉ Text)
    (hmT : mark ∉ Text) (hn : n ≤ Text.length)
    (h : VFeedInv' blank startSym endSym mark u v Text k p₁ r n M)
    (hok : Ok2 n M (M.z.1.pos - u.length + M.z.2))
    (he : Enabled v n M.z.1) :
    VFeedInv' blank startSym endSym mark u v Text k p₁ r n
        (fstepX blank endSym mark u v k p₁ r n Text M) ∧
      Ok2 n (fstepX blank endSym mark u v k p₁ r n Text M)
        ((fstepX blank endSym mark u v k p₁ r n Text M).z.1.pos - u.length
          + (fstepX blank endSym mark u v k p₁ r n Text M).z.2) := by
  have hfF := vfillIf1'_feedInv (u := u) (v := v) (k := k) (p₁ := p₁) (r := r) hne hn h
  have hfok : Ok2 n (vfillIf1' blank mark n M)
      ((vfillIf1' blank mark n M).z.1.pos - u.length
        + (vfillIf1' blank mark n M).z.2) := by
    unfold vfillIf1'
    split_ifs with hcc
    · exact hok
    · exact hok
  exact vscanOneX_feedInv hk hp hne hv hend hendu hb hmT hn (vfillIf1'_ready h he) hfF hfok

/-! ## 5. 一歩の償却（`Ψ = 2·checked` 込み） -/

/-- 償却係数 `A_X = 8k + 47`（走査プログラム `8k+13` ＋ `Txt2` の右移動 `34`）。 -/
def xfA (k : ℕ) : ℕ := 8 * k + 47

/-- 償却定数 `B_X = 82`。 -/
def xfB : ℕ := 82

example : xfA 8 = 111 := by norm_num [xfA]

/-- **一歩の償却**：`fcostX + Ψ' ≤ A_X·ΔΦ + B_X + Ψ`（`Ψ = 2·checked`）。
`GSVerifierTapes` の `vprogram'_amortized` / `StageMatcherProg.vprogramX_amortized` に
対応する、**供給つき機械の実費用** 版。走査プログラムは `GSTapes.program_cost'`
（`≤ (8k+13)·ΔΦ + 8`）、ずらし枝の `Txt2` 右移動は `gsShift ≤ ΔΦ`、
`U` の巻き戻し `2·checked` は `Ψ` の減少で払う。 -/
theorem fcostX_amortized {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)}
    {k p₁ r n : ℕ} {M : VMachine' sc}
    (hk : 0 < k) (hp : 0 < p₁) (hne : mark ≠ blank) (hend : endSym ∉ v)
    (hn : n ≤ Text.length)
    (h : VFeedInv' blank startSym endSym mark u v Text k p₁ r n M)
    (he : Enabled v n M.z.1) :
    fcostX blank endSym mark k n M + 2 * (vStep u v k p₁ r Text M.z).2
      ≤ xfA k * (Phi k (vStep u v k p₁ r Text M.z).1 - Phi k M.z.1) + xfB + 2 * M.z.2 := by
  have hfF := vfillIf1'_feedInv (u := u) (v := v) (k := k) (p₁ := p₁) (r := r) hne hn h
  have hrd1 := vfillIf1'_ready h he
  set M' := vfillIf1' blank mark n M with hM'
  have hzz : M'.z = M.z := vfillIf1'_z blank mark n M
  have hm1 : M'.m1 ≤ Text.length := le_trans hfF.m1le hn
  have hstep : scanStep v k p₁ r (padW blank Text M'.m1) M'.z.1
      = scanStep v k p₁ r Text M'.z.1 := scanStep_padW hm1 hrd1
  -- 走査プログラムの長さ
  have hscan' : GSTapes.Encodes' blank startSym endSym mark v (padW blank Text M'.m1) k p₁ r
      M'.vt.1 M.z.1 := by rw [← hzz]; exact hfF.scan
  have hqle' : M.z.1.q ≤ v.length := by rw [← hzz]; exact hfF.qle
  have hprog := GSTapes.program_cost' (p₁ := p₁) (r := r) hk hne hend hscan' hqle'
  rw [show scanStep v k p₁ r (padW blank Text M'.m1) M.z.1
      = scanStep v k p₁ r Text M.z.1 from by rw [← hzz]; exact hstep] at hprog
  have hcc : GSVTapes.cOf M'.vt.2 = M.z.2 := by
    have := GSVTapes.cOf_eq hfF.pat
    rwa [hzz] at this
  rw [vStep_fst]
  unfold fcostX fextX xfA xfB
  rw [← hM']
  set D := Phi k (scanStep v k p₁ r Text M.z.1) - Phi k M.z.1 with hD
  have hD1 : 1 ≤ D := by
    have := phi_step_lt (v := v) (T := Text) (p₁ := p₁) (r := r) hk hp M.z.1
    omega
  by_cases hadv : Tape.read (M'.vt.1 GSTapes.tP) ≠ endSym ∧
      Tape.read (M'.vt.1 GSTapes.tP) = Tape.read (M'.vt.1 GSTapes.tT)
  · rw [if_pos hadv]
    obtain ⟨ha1, ha2⟩ := (GSTapes.advance_iff' hend hscan' hqle').1 hadv
    have haT : Text[M.z.1.pos + M.z.1.q]? = v[M.z.1.q]? := by
      rw [← padW_getElem?_of_lt (blank := blank) hm1
        (by rw [← hzz]; exact hrd1 (by rw [hzz]; exact ha1))]
      exact ha2
    have hvs : (vStep u v k p₁ r Text M.z).2
        = vComp u Text M.z.1.pos (vComp u Text M.z.1.pos M.z.2) :=
      GSVTapes.vStep_snd_adv ⟨ha1, haT⟩
    have h3 := vComp_le_succ u Text M.z.1.pos M.z.2
    have h4 := vComp_le_succ u Text M.z.1.pos (vComp u Text M.z.1.pos M.z.2)
    have h34 : 34 ≤ 34 * D := by
      have := Nat.mul_le_mul_left 34 hD1; omega
    rw [hvs]
    have e : (8 * k + 47) * D = (8 * k + 13) * D + 34 * D := by ring
    omega
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
    have hvs : (vStep u v k p₁ r Text M.z).2 = 0 := GSVTapes.vStep_snd_shift hna
    rw [hvs, hd, hcc]
    have h34 : 34 * gsShift k p₁ r M.z.1.q ≤ 34 * D := Nat.mul_le_mul_left 34 hsh
    have e : (8 * k + 47) * D = (8 * k + 13) * D + 34 * D := by ring
    omega

/-- **前進（比較成功）枝の費用**：`|program'| ≤ 8k+21`（`ΔΦ = 1`）に
`vcomp2Fed` の `70` と歩頭の供給 `33` を足して `≤ 8k+124`。 -/
theorem fcostX_adv_le {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)}
    {k p₁ r n : ℕ} {M : VMachine' sc}
    (hk : 0 < k) (hne : mark ≠ blank) (hend : endSym ∉ v) (hn : n ≤ Text.length)
    (h : VFeedInv' blank startSym endSym mark u v Text k p₁ r n M)
    (he : Enabled v n M.z.1)
    (hadv : M.z.1.q ≠ v.length ∧ Text[M.z.1.pos + M.z.1.q]? = v[M.z.1.q]?) :
    fcostX blank endSym mark k n M ≤ 8 * k + 124 := by
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
  unfold fcostX fextX
  rw [← hM', if_pos hadvT]
  omega

/-! ## 6. 公理の確認 -/

#print axioms vwalkFedX_spec
#print axioms vExtFedX_spec
#print axioms vencodes_stepFX
#print axioms vscanOneX_feedInv
#print axioms fstepX_cost
#print axioms fstepX_feedInv
#print axioms fcostX_amortized
#print axioms fcostX_adv_le

end VerifierFeedX
end PalPeg
