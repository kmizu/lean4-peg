import PalPeg.ShiftPalAlongTrace
import PalPeg.CloseoutWatchRound48
import PalPeg.GalilScaffoldTopChainUnique

/-!
# 第 3 連言 `FreshShiftLedger` を、不一致比較の直前の窓から

`obligation_shiftPalResiduesAlongRun` の第 3 連言は、run の各点 `z`（`periodOnly = false`）と
その不一致比較の着地 `s'` について `FreshShiftLedger w z.vm s'` を要求する。
`ShiftPalAlongTrace.freshShiftLedger_of_chainW` はそれを `ChainW` 形の窓（比較後の chain）＋
中心記号＋右ヘッド 3 事実から出す。ここではその入力を**比較前**の状態 `s` の持ち物から作る:

* 窓: `ChainW … s.chain`（`CloseoutWatchRound42.LandingData` の第 2 成分の形）を、
  比較量子の中の chain の 1 歩（`compareFound` の `chainAt false` ＝ `ChainStep` 1 歩）越しに
  `GalilReplaySpan.chainW_step` ＋ `chainStep_unique` で `s'.chain` へ運ぶ
* 右ヘッド: `s'.right = right s.right`（`afterMismatch`）と `ScanInvariant` の右ヘッド事実
* 中心記号 `x[cen] = cc`: 窓に**無い**ので外から取る（誕生時の `Candidate` 由来）

不一致側（`¬ matched s'`）に限る——`ShiftPal` の前提に `¬ matched` があるので消費者は
それしか要らない。

`freshShiftLedger_of_chainW_scan` が核で、`LandingData` から使うのは 3 場だけ
（`freshShiftLedger_of_landing` はその射影）。

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false

namespace PalPeg.ShiftEntryFromLanding

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.ShiftPalAlongTrace
open PalPeg.CloseoutWatchRound42 (LandingData)

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`FreshShiftLedger` at a mismatched comparison, from the window before it.**
The window is anchored at the scan centre `position s.center` and reaches the right
head `position s.right = position s.center + R`. -/
theorem freshShiftLedger_of_chainW_scan {raw : List (Fin 2)} {R bud : ℕ}
    {cc b : Fin 3} {xs : List (Fin 3)} {s s' : GalilVM}
    (hCW : PalPeg.GalilReplaySpan.ChainW raw (position s.center) (position s.center + R)
      (position s.center + R) bud false cc b xs s.chain)
    (hscan : ScanInvariant raw (position s.center) R s.left s.right)
    (hcan : canRight s.right)
    (hcentre : (encoded raw)[position s.center]? = some cc)
    (hpo : s.periodOnly = false)
    (hcmp : compareFound (PofC centre place entry raw) q first s s')
    (hmis : ¬ (galilFrameS (PofC centre place entry raw) q first).matched s') :
    FreshShiftLedger raw s s' := by
  obtain ⟨vs, vq, matchedBit, hvl, hvr, hmatch, -, hchainAt, hs'⟩ := hcmp
  have hnotIdle : s.chain ≠ ChainVM.idle := PalPeg.GalilReplaySpan.chainW_ne_idle hCW
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
    cases hx : s.chain with
    | idle => exact absurd hx hnotIdle
    | copy => rfl
    | back => rfl
    | watch => rfl
    | broken => rfl
  have hs'' : s' = afterMismatch s vs vq := by
    rw [hs', hborn, afterBirth_false, if_neg (by simp)]
  subst hs''
  -- the chain stepped once, by `ChainStep`
  rcases hchainAt with ⟨-, y, hstep, hy⟩ | ⟨hidle, -⟩ | ⟨hidle, -⟩
  · simp only [Bool.false_eq_true, ↓reduceIte] at hy
    have hlen : position s.center + R < (encoded raw).length := hscan.palindrome.2.1
    obtain ⟨y', hstep', hCW'⟩ := PalPeg.GalilReplaySpan.chainW_step
      (PalPeg.GalilReplaySpan.chainW_mono hCW (Nat.le_succ _)) hlen le_rfl
    have hyy : y = y' := chainStep_unique hstep hstep'
    subst hyy
    rw [← hy] at hCW'
    -- the right head moved one place right
    have hl0 : 0 < s.right.head.left.length :=
      (represented_position _ raw hscan.rightRep hscan.rightPresent).1
    have hrRep : GalilScaffoldInputTrace.Represents vs.right.head raw := by
      rw [hvr]; exact right_word _ raw hscan.rightRep hcan
    have hrPres : vs.right.head.focus ≠ none := by
      rw [hvr]; exact right_present _ raw hscan.rightRep hscan.rightPresent hcan
    have hrPos : position vs.right = position s.center + R + 1 := by
      rw [hvr, right_position _ hcan hl0, hscan.rightPos]
    exact freshShiftLedger_of_chainW (cen := position s.center) rfl hCW' hscan.rightPos
      hrRep hrPres hrPos hcentre hpo
  · exact absurd hidle hnotIdle
  · exact absurd hidle hnotIdle

#print axioms freshShiftLedger_of_chainW_scan

/-- **The same from a `LandingData` state** (its window, right-head place and scan
invariant are the three fields used). -/
theorem freshShiftLedger_of_landing {raw : List (Fin 2)} {R : ℕ} {sT : GalilVM}
    {cc b : Fin 3} {xs : List (Fin 3)} {c : Control} {s s' : GalilVM}
    (hland : LandingData raw R sT cc b xs c s)
    (hcan : canRight s.right)
    (hcentre : (encoded raw)[position s.center]? = some cc)
    (hpo : s.periodOnly = false)
    (hcmp : compareFound (PofC centre place entry raw) q first s s')
    (hmis : ¬ (galilFrameS (PofC centre place entry raw) q first).matched s') :
    FreshShiftLedger raw s s' := by
  obtain ⟨-, hCW, hR, -, -, hscan, -, -, -, -, -⟩ := hland
  rw [← hR, hscan.rightPos] at hCW
  exact freshShiftLedger_of_chainW_scan centre place entry q first hCW hscan hcan hcentre hpo
    hcmp hmis

#print axioms freshShiftLedger_of_landing

end

end PalPeg.ShiftEntryFromLanding
