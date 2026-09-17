import PalPeg.CloseoutWatchRound31

/-!
# Closeout watch round 35 — `ReplayOutC` closed; `ReplayNoBusyC` is *not* a
model divergence, only a too-strong leaf

## (1) `replayOutC_of_landing` — `ReplayOutC` from the landing data alone

The replay landing `⟨cT, sT⟩` is `Restarted raw sT 0 reset`, so its scan
invariant has radius `0`.  A `WatchSegE` out of it advances the right head by
exactly `esR.count true` (`watchSegE_right_position`) and keeps the centre
(`watchSegE_center`); `InvScan 2048 raw c' t' R` puts the right head at
`center + R`.  Hence `esR.count true = R > 0`: the replay segment contains a
matched comparison, and `watchSegE_outputM` (its `0 < count true` branch)
refreshes the output there, giving `OutputRel raw c' t'` whatever the output
at the fallback landing was.  **No hypothesis left.**

## (2) `ReplayNoBusyC` — verdict

* Mode-`shift` is disabled while replaying on both sides: Scala
  `ScaffoldGalil.scala:270` (`!replaying && chain.canShift`) /
  `ScaffoldCircuitGalil.scala:176`, Lean `GalilScaffoldTop.lean:125`
  (`Tick.scan_shift` carries `hr : c.replaying = false`); `scan_fallback` too
  (`:131`).  `replayNoShiftC_of_model` proves this (`ReplayNoShiftC`).
* But `ChainEnd`/`BrokeAndRestarted` are about a **watch chain** started by
  `chain.start()` when the search co-run lands in `found`, and that has *no*
  `replaying` guard on either side: Scala `ScaffoldGalil.scala:226-228`
  (`if (search.mode == Found) chain.start()`, inside the scan tick, regardless of
  `replaying`) / `ScaffoldCircuitGalil.scala:146`; Lean `compareFound`
  (`GalilScaffoldTopSearch.lean:144-152`) and `backgroundS` (`:158-163`) via
  `chainAt … (decide (vq.search.mode = .found))`.  So the Lean model is
  **faithful** here, and `ReplayNoBusyC` cannot be proved from the model: a
  chain may start inside the replay.  The honest closeout of
  `replayRunC_of_decodes` is to consume branches (ii)/(iii) of
  `replay_after_fallback_general''_R_of_decodes` (a `ChainEnd` landing is not
  an `InvScan` landing), not to exclude them.  `ReplayNoBusyC` stays open as a
  *false-in-general* leaf and should be retired.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchRound35

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilOneFallback
open PalPeg.CloseoutWatchRound21 (FallbackLanding)
open PalPeg.CloseoutWatchRound28 (ReplayOutC ReplayNoBusyC)

/-! ## 1. `ReplayOutC` -/

/-- **`ReplayOutC` from the landing data.**  The replay segment out of a
positive-radius fallback landing contains `R > 0` matched comparisons, so its
landing output is refreshed and sound. -/
theorem replayOutC_of_landing (raw : List (Fin 2)) (P : Shared)
    (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9)
    (cP : Control) (sP : GalilVM) : ReplayOutC P q first raw cP sP := by
  intro es c1 s1 _ n R cT sT hR hL esR c' t' hsegR hIS
  have hRL : ReplayLanding raw cT sT R := hL.2.2.2.1 hR
  have hi0 : ScanInvariant raw (position sT.center) 0 sT.left sT.right := hRL.rest.2.2.2.1
  have hpos := (watchSegE_right_position raw P q first 2048 hsegR hi0).2
  have hcen : t'.center = sT.center :=
    watchSegE_center P q first 2048 hsegR
  have hcount : esR.count true = R := by
    have h1 := hIS.scan.rightPos
    have h2 := hi0.rightPos
    rw [hcen] at h1
    omega
  exact PalPeg.GalilLeafOutReplay.watchSegE_outputM raw P hP hP' q first 2048 hsegR
    (position sT.center) 0 hi0 (Or.inr (by omega))

#print axioms replayOutC_of_landing

/-! ## 2. `ReplayNoShiftC` — the part of `ReplayNoBusyC` the model supports -/

/-- No scan tick taken while replaying enters mode `shift` or `copy`: the
`scan_shift`/`scan_fallback` constructors require `replaying = false`
(Scala `!replaying && chain.canShift`, `require(!replaying, fallback)`). -/
def ReplayNoShiftC (P : Shared) (q : ℕ) (first : Fin 9) : Prop :=
  ∀ (c c' : Control) (s s' : GalilVM), c.mode = .scan → c.replaying = true →
    Tick (galilFrameS P q first) 2048 ⟨c, s⟩ ⟨c', s'⟩ → c'.mode = .scan

theorem replayNoShiftC_of_model (P : Shared) (q : ℕ) (first : Fin 9) :
    ReplayNoShiftC P q first := by
  intro c c' s s' hm hrpl h
  cases h <;> simp_all

#print axioms replayNoShiftC_of_model

end PalPeg.CloseoutWatchRound35
