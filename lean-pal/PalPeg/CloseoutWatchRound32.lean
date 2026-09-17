import PalPeg.CloseoutWatchRound30
import PalPeg.GalilShiftPack
import PalPeg.GalilChainCoupling

/-!
# Closeout watch round 32 — the tick-local pieces 1–4 of `shiftRoundAtC'_of_tick`

Round 30 produced `ShiftRoundAtC'` from six named pieces.  This file works the
four tick-local ones.

**Piece 1 (`ShiftChainStableC`) — verdict.**  The frame's compare at a watching
chain is `ChainTick false (.watch w) vs.chain`, i.e. one `ChainStep.watchStep`
with `GalilScaffoldChainWatch.Internal w w'`.  `Internal` has two constructors:
`idle` (lag not positive, `w' = w`) and `take` (lag positive, `w' = caught w`,
which consumes one verifier step and decrements the lag).  So the disabled
tick of a mismatching compare keeps the watch state **iff the lag is not
positive at the landing** (`watch_after_compare`); the guard's `zero w'.lag`
does not exclude `take` (lag `1` ↦ `0`).  Hence `ShiftChainStableC` is not
derivable from the tick; it reduces to the landing-lag fact `ShiftLagZeroC`
(`shiftChainStableC_of_lagZero`), which keeps `ShiftRoundData` verbatim (no
`ShiftRoundData'` needed: `beginShiftVM h w (afterMismatch …)` demands
`vs.chain = .watch w`, so the data really asserts stability).

**Piece 2 (`ShiftPeriodC h`)**: not tick-local.  `beginShiftVM'` reads
`periodLength w` definitionally, but `ShiftRoundData` fixes `h` from outside
(the same `h` as `ShiftRun … (ofNat h)`), so the tie is a landing invariant
of the chain's period tape; it stays named.

**Piece 3 (`ShiftCopyIdleC`)**: transported from the preparation landing with
`GalilChainCoupling.copyPack_steps` (`shiftCopyIdleC_of_copyPack`); what is
left is `CopyPack cP sP` at that landing (`copyPack_of_invLPC` supplies it
from `InvLPC`).

**Piece 4 (`ShiftRunC h`)**: `GalilShiftPack.shiftRun_of_scan` builds the run
from `ScanInv raw s1 radius` with `0 < h ≤ radius` (`shiftRunC_of_scanInv`);
what is left is that scan invariant with the radius bound at the landing.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchRound32

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton
open PalPeg.CloseoutWatchRun (LiveScanWatch)
open PalPeg.CloseoutWatchRound30 (ShiftChainStableC ShiftPeriodC ShiftCopyIdleC ShiftRunC)
open PalPeg.GalilChainCoupling (CopyPack copyPack_steps)
open PalPeg.GalilShiftPack (shiftRun_of_scan)

/-! ## 1. Piece 1: the post-compare chain at a watching landing -/

/-- The compare's chain tick at a watching chain: the watch is kept (lag not
positive) or replaced by `caught w` (lag positive, a `Good` consume). -/
theorem watch_after_compare {P : Shared} {q : ℕ} {first : Fin 9} {s1 : GalilVM}
    {vs : ScanVM} {w : GalilScaffoldChainWatch.State} (hw : s1.chain = ChainVM.watch w)
    (hcmp : (galilFrame P q first).compare s1 (scanLens.set s1 vs))
    (hmis : ¬ (galilFrame P q first).matched (scanLens.set s1 vs)) :
    (positive w.lag = false ∧ vs.chain = ChainVM.watch w) ∨
    (positive w.lag = true ∧ GalilScaffoldChainWatch.Good w ∧
      vs.chain = ChainVM.watch (GalilScaffoldChainWatch.caught w)) := by
  obtain ⟨⟨hl, hr, htick⟩, -⟩ := hcmp
  have hl' : vs.left = left s1.left := hl
  have hr' : vs.right = right s1.right := hr
  have hne : read (left s1.left) ≠ read (right s1.right) := by
    intro heq
    apply hmis
    show read vs.left = read vs.right
    rw [hl', hr']; exact heq
  have htick' : ChainTick (decide (read (left s1.left) = read (right s1.right)))
      s1.chain vs.chain := htick
  rw [decide_eq_false hne, hw] at htick'
  obtain ⟨y, hstep, hy⟩ := htick'
  simp only [Bool.false_eq_true, ↓reduceIte] at hy
  cases hstep with
  | watchStep _ w' hint =>
    cases hint with
    | idle hz => exact Or.inl ⟨hz, hy⟩
    | take hp hg => exact Or.inr ⟨hp, hg, hy⟩

/-- **NAMED (open) — the landing lag.**  At a watching chain whose compare
mismatches, the lag is not positive.  (This is exactly what piece 1 needs and
exactly what the tick cannot supply: `Internal.take` is available otherwise.) -/
def ShiftLagZeroC (P : Shared) (q : ℕ) (first : Fin 9) : Prop :=
  ∀ (s1 : GalilVM) (vs : ScanVM) (w : GalilScaffoldChainWatch.State),
    s1.chain = ChainVM.watch w →
    (galilFrame P q first).compare s1 (scanLens.set s1 vs) →
    ¬ (galilFrame P q first).matched (scanLens.set s1 vs) →
    positive w.lag = false

/-- **Derived — piece 1 from the landing lag.** -/
theorem shiftChainStableC_of_lagZero (P : Shared) (q : ℕ) (first : Fin 9)
    (hlag : ShiftLagZeroC P q first) : ShiftChainStableC P q first := by
  intro s1 vs w hw hcmp hmis
  rcases watch_after_compare hw hcmp hmis with ⟨-, hvs⟩ | ⟨hp, -, -⟩
  · exact hvs
  · exact absurd hp (by rw [hlag s1 vs w hw hcmp hmis]; decide)

/-- Conversely, piece 1 forces the lag: if the post-compare chain is
`.watch w` then the tick was `idle` (a `take` would have consumed). -/
theorem lagZero_of_shiftChainStable (P : Shared) (q : ℕ) (first : Fin 9)
    (hst : ShiftChainStableC P q first)
    (hinj : ∀ w : GalilScaffoldChainWatch.State, GalilScaffoldChainWatch.Good w →
      GalilScaffoldChainWatch.caught w ≠ w) :
    ShiftLagZeroC P q first := by
  intro s1 vs w hw hcmp hmis
  rcases watch_after_compare hw hcmp hmis with ⟨hz, -⟩ | ⟨hp, hg, hvs⟩
  · exact hz
  · exfalso
    have h1 := hst s1 vs w hw hcmp hmis
    rw [hvs] at h1
    exact hinj w hg (ChainVM.watch.inj h1)

/-! ## 2. Piece 3: `CopyIdle` transported from the preparation landing -/

/-- **Derived — piece 3 from `CopyPack` at a source state reaching every
clock-`1` landing.**  The source is quantified: whoever provides the
`Steps` run from `⟨cP, sP⟩` to the landing (e.g. `watchSegE_steps`) and
`CopyPack cP sP` (e.g. `copyPack_of_invLPC`) gets `ShiftCopyIdleC`. -/
theorem shiftCopyIdleC_of_copyPack (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hsrc : ∀ (c1 : Control) (s1 : GalilVM), LiveScanWatch c1 s1 → c1.clock = 1 →
      ∃ (cP : Control) (sP : GalilVM) (k : ℕ),
        CopyPack cP sP ∧
        Steps (galilFrameS (PofC centre place entry raw) q first) 2048 k ⟨cP, sP⟩ ⟨c1, s1⟩) :
    ShiftCopyIdleC := by
  intro c1 s1 hL hclk
  obtain ⟨cP, sP, k, hP, hsteps⟩ := hsrc c1 s1 hL hclk
  have hP1 : CopyPack c1 s1 :=
    copyPack_steps (onLetterVM raw) leftFirstVM centre place entry q first 2048 hsteps hP
  exact hP1 (by rw [hL.1]; decide)

/-! ## 3. Piece 4: the shift run from the scan invariant -/

/-- **NAMED (open) — the landing scan invariant with the radius bound.** -/
def ShiftScanInvC (raw : List (Fin 2)) (h : ℕ) : Prop :=
  ∀ (c1 : Control) (s1 : GalilVM), LiveScanWatch c1 s1 → c1.clock = 1 →
    canRight s1.right →
    ∃ radius : ℕ, ScanInv raw s1 radius ∧ 0 < h ∧ h ≤ radius

/-- **Derived — piece 4 from the scan invariant.** -/
theorem shiftRunC_of_scanInv (raw : List (Fin 2)) (h : ℕ) (hinv : ShiftScanInvC raw h) :
    ShiftRunC h := by
  intro c1 s1 hL hclk hav
  obtain ⟨radius, hi, hpos, hle⟩ := hinv c1 s1 hL hclk hav
  exact shiftRun_of_scan raw s1 radius h hi hpos hle

end PalPeg.CloseoutWatchRound32

#print axioms PalPeg.CloseoutWatchRound32.watch_after_compare
#print axioms PalPeg.CloseoutWatchRound32.shiftChainStableC_of_lagZero
#print axioms PalPeg.CloseoutWatchRound32.lagZero_of_shiftChainStable
#print axioms PalPeg.CloseoutWatchRound32.shiftCopyIdleC_of_copyPack
#print axioms PalPeg.CloseoutWatchRound32.shiftRunC_of_scanInv
