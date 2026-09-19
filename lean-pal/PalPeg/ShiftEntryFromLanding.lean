import PalPeg.ShiftPalAlongTrace

/-!
# `FreshShiftLedger` を、不一致比較の直前の窓から（どの shift 入口でも）

`obligation_shiftPalResiduesAlongRun` は、run の各点 `z` とその不一致比較の着地 `s'` で
shift guard が立つとき、**誕生中心 `cen₀` に anchor した窓**
（`ShiftPalAlongTrace.WatchWindow … z.vm.chain`: `LagAt`／`BlockOn`／`CoreX` の 3 場）と
`ScanInvariant`・`canRight`・誕生中心の記号・`2h ≤ R` を要求する。
`ShiftPalAlongTrace.freshShiftLedger_of_chainW` はそれらから `FreshShiftLedger`（の 5 成分）を
出し、`shiftPal_of_freshShiftLedger` が `ShiftPal` にする。ここではその入力を**比較前**の
状態 `s` の持ち物から作る:

* 窓: `WatchWindow … s.chain` を、比較量子の中の chain の 1 歩（`compareFound` の
  `chainAt false` ＝ `ChainStep` 1 歩 ＝ watch では `Internal` 1 歩）越しに
  `watchWindow_step` で `s'.chain` へ運ぶ
* 右ヘッド: `s'.right = right s.right`（`afterMismatch`）と `ScanInvariant` の右ヘッド事実

不一致側（`¬ matched s'`）に限る——`ShiftPal` の前提に `¬ matched` があるので消費者は
それしか要らない。`periodOnly` には触れない: 新鮮な shift（margin から `4h ≤ R`）も
継続 round の終端の shift（`cycleEnd`）も同じ議論で、左端の不一致でも成り立つ。

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false

namespace PalPeg.ShiftEntryFromLanding

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.ShiftPalAlongTrace

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`FreshShiftLedger` at a mismatched comparison, from the window before it.**
The window is anchored at the birth centre `cen₀`, the scan centre is `cen₀ + k·h`, and the
window reaches the right head `position s.right = position s.center + R`. -/
theorem freshShiftLedger_of_chainW_scan {raw : List (Fin 2)} {cen₀ k R : ℕ}
    {cc b : Fin 3} {xs : List (Fin 3)} {s s' : GalilVM}
    (hW : WatchWindow raw cen₀ (position s.center + R) cc b xs s.chain)
    (hk : position s.center = cen₀ + k * (xs.length + 1))
    (hscan : ScanInvariant raw (position s.center) R s.left s.right)
    (hcan : canRight s.right)
    (hcentre : (encoded raw)[cen₀]? = some cc)
    (hsize : 2 * (xs.length + 1) ≤ R)
    (hcmp : compareFound (PofC centre place entry raw) q first s s')
    (hmis : ¬ (galilFrameS (PofC centre place entry raw) q first).matched s') :
    FreshShiftLedger raw s s' := by
  obtain ⟨vs, vq, matchedBit, hvl, hvr, hmatch, -, hchainAt, hs'⟩ := hcmp
  -- the chain is watching
  obtain ⟨w, hwatch⟩ : ∃ w, s.chain = ChainVM.watch w := by
    cases hx : s.chain with
    | watch w => exact ⟨w, rfl⟩
    | idle => rw [hx] at hW; exact hW.elim
    | copy => rw [hx] at hW; exact hW.elim
    | back => rw [hx] at hW; exact hW.elim
    | broken => rw [hx] at hW; exact hW.elim
  rw [hwatch] at hW
  have hnotIdle : s.chain ≠ ChainVM.idle := fun h => by rw [hwatch] at h; cases h
  -- the comparison mismatched
  have hbit : matchedBit = false := by
    cases matchedBit with
    | false => rfl
    | true =>
      exfalso
      apply hmis
      have hm : read vs.left = read vs.right := hmatch.1 rfl
      show read s'.left = read s'.right
      rw [hs', afterBirth_left, afterBirth_right, if_pos rfl]
      exact hm
  subst hbit
  -- the chain was alive, so this is no birth: `s' = afterMismatch s vs vq`
  have hborn : chainBorn (decide (vq.search.mode = .found)) s.chain = false := by
    rw [hwatch]; rfl
  have hs'' : s' = afterMismatch s vs vq := by
    rw [hs', hborn, afterBirth_false, if_neg (by simp)]
  subst hs''
  -- the chain stepped once: on a watch that is one `Internal` step
  rcases hchainAt with ⟨-, y, hstep, hy⟩ | ⟨hidle, -⟩ | ⟨hidle, -⟩
  · simp only [Bool.false_eq_true, ↓reduceIte] at hy
    rw [hwatch] at hstep
    cases hstep with
    | watchBreak _ _ =>
      intro _ wch hwch
      have h2 : vs.chain = ChainVM.watch wch := hwch
      rw [hy] at h2
      cases h2
    | watchStep _ _ hint =>
      have hW' := watchWindow_step hW hint
      rw [← hy] at hW'
      -- the right head moved one place right
      have hl0 : 0 < s.right.head.left.length :=
        (represented_position _ raw hscan.rightRep hscan.rightPresent).1
      have hrRep : GalilScaffoldInputTrace.Represents vs.right.head raw := by
        rw [hvr]; exact right_word _ raw hscan.rightRep hcan
      have hrPres : vs.right.head.focus ≠ none := by
        rw [hvr]; exact right_present _ raw hscan.rightRep hscan.rightPresent hcan
      have hrPos : position vs.right = position s.center + R + 1 := by
        rw [hvr, right_position _ hcan hl0, hscan.rightPos]
      exact freshShiftLedger_of_chainW (cen := position s.center) rfl hk hW' hscan.rightPos
        hrRep hrPres hrPos hcentre hsize
  · exact absurd hidle hnotIdle
  · exact absurd hidle hnotIdle

#print axioms freshShiftLedger_of_chainW_scan

end

end PalPeg.ShiftEntryFromLanding
