import PalPeg.ShiftPalAlongTrace

/-!
# `H_freshShiftAtShiftEntry` は左端の不一致では偽（条件付き反証）

**2026-09-19（n233）**。ヘッドモデル（`GalilScaffoldInputHead.layout`）では左スタックの
末尾が `none` 番兵で、最初の文字に居るヘッド `⟨layout [a] rs qs, false⟩`（位置 1）が
`left` すると `focus = none`（`read = none`）になる。走査がそこで比較すると必ず不一致で、
chain が phase 4・`margin ≥ 0`・予測一致なら `shiftGuardVM` が立ち `Tick.scan_shift` が
発火する。ところが `H_freshShiftAtShiftEntry` はその tick の着地 `t` に
`ShiftInv`（`CloseoutPackRun37.lean:59`）を要求し、その `leftPresent : t.left.head.focus ≠ none`
は `t.left = u.left = left s.left` で偽。

未構成の証人: そういう状態に `InvLPS` から到達する run。`a^n` では `Leftmost`
（`GalilLiveCentre.Live` の `n < 2c`）が右ヘッド `2c − 1` で中心 `c` を強制するので、
次の比較は左端に当たる。chain は DP が `4h+1` セル見た時点で生まれ、`4h` セル消費で
phase 4 になるので、十分長い `a^n` では guard が立つ。

同じ理由で `GalilRoundPeriod.RoundScan` の `room : R + 2 ≤ C` と
`origin : (encoded raw)[C−R−1]? ≠ (encoded raw)[C+R+1]?`（左端では両方 `some 2`）も
その round では偽。**`ShiftInv` / `RoundScan` は「不一致は本物の文字の不一致」を
前提にしており、左端の不一致（`read = none`）を扱えない。**

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false

namespace PalPeg.ShiftEntryBoundary

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.CloseoutPackRun37

/-- **REFUTED（条件付き）.**  左ヘッドが最初の文字に居る状態 `s` から `scan_shift` 形の
tick（compare・不一致・shift guard・`beginShift`）が出るなら、`H_freshShiftAtShiftEntry`
はその tick で `False` を導く。証人（そういう状態への到達）は未構成。 -/
theorem refuted_freshShiftAtShiftEntry_at_left_end
    (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9)
    {w : List (Fin 2)} {c : Control} {s u t : GalilVM}
    {a : Fin 2} {rs : List (Option (Fin 2))} {qs : List (Fin 2)}
    (hmode : c.mode = Mode.scan) (hreplaying : c.replaying = false) (hclock : c.clock = 1)
    (hperiodOnly : s.periodOnly = false)
    (hfirstLetter : s.left = ⟨layout [a] rs qs, false⟩)
    (hcmp : (galilFrameS (PofC centre place entry w) q first).compare s u)
    (hmis : ¬ (galilFrameS (PofC centre place entry w) q first).matched u)
    (hguard : (galilFrameS (PofC centre place entry w) q first).shiftGuard u)
    (hbegin : (galilFrameS (PofC centre place entry w) q first).beginShift u t)
    (hF : H_freshShiftAtShiftEntry centre place entry q first w c s t) : False := by
  have hbegin' : beginShiftVM' u t := hbegin
  obtain ⟨w', -, ht⟩ := hbegin'
  obtain ⟨C, R, k, hinv⟩ := hF hmode hreplaying hclock hperiodOnly
    ⟨u, hcmp, hmis, hguard, hbegin⟩ (GalilScaffoldChainWatch.immediate w') (by rw [ht])
  have hcmp' : compareFound (PofC centre place entry w) q first s u := hcmp
  obtain ⟨vs, vq, matchedBit, hvl, -, -, -, -, hu⟩ := hcmp'
  have hul : u.left = GalilScaffoldInputHead.left s.left := by
    rw [hu, afterBirth_left]
    cases matchedBit <;> exact hvl
  apply hinv.leftPresent
  rw [ht]
  show u.left.head.focus = none
  rw [hul, hfirstLetter]
  rfl

#print axioms refuted_freshShiftAtShiftEntry_at_left_end

end PalPeg.ShiftEntryBoundary
