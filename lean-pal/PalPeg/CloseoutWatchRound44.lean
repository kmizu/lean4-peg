import PalPeg.CloseoutWatchRound41

/-!
# Closeout watch round 44 — the three Round 41 leaves: verdict

Round 41 replaced `MismatchLandingLagZeroC` by three named pieces
(`PrepBirthLagC`, `WatchDrainC`, `LandingFreshC`).  This round audits them.

* **`LandingFreshC` is FALSE as stated** (`not_landingFreshC`): its shift
  amount `h` is universally quantified and only constrained by
  `beginShiftVM h w' (afterMismatch s1 vs vq') s2'`, which is satisfiable for
  *every* `h` (it merely records the post-state).  The clause
  `periodLength w' = h` therefore forces `periodLength w' = 0` and
  `periodLength w' = 1` simultaneously at any landing that has a watching
  chain.  So the clause cannot live in this leaf; it must be produced at the
  route, where `h` is chosen (Round 33 chose `h := periodLength w'`).
  `LandingFreshC'` below is the residue (the three transport clauses).

* **`WatchDrainC` is not provable as stated**: `SumRel (.watch w') Rnow`
  is vacuous when the chain is broken (`sumRel_watch_broken`), so `Rnow` is
  unconstrained there; and even unbroken it reads
  `distance w' + lag w'`, so `Rnow = value w0.lag + m'` additionally needs
  the birth state's distance to vanish (`sumRel_watch_of_unbroken`).  Two
  hypotheses are missing; see the report.

* **`PrepBirthLagC`** is untouched here (it needs the prep-segment transport
  of `found_to_watchStart`/`prepEvents`).

Nothing is closed, so there is no `foundExit_compare_final17`.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchRound44

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.CloseoutContracts
open PalPeg.GalilRunSkeleton PalPeg.GalilInvPlus PalPeg.GalilInvPlus2
open PalPeg.GalilFoundStage PalPeg.GalilTraceCost
open PalPeg.GalilChainCoupling (FreshC SumRel)
open PalPeg.CloseoutWatchRound41 (LandingL LandingFreshC)

/-! ## 1. `SumRel` on a watch is vacuous when broken -/

theorem sumRel_watch_broken (w : GalilScaffoldChainWatch.State) (R : ℤ)
    (hb : w.machine.control.broken = true) : SumRel (.watch w) R := by
  intro h; rw [hb] at h; exact Bool.noConfusion h

theorem sumRel_watch_of_unbroken {w : GalilScaffoldChainWatch.State} {R : ℤ}
    (hb : w.machine.control.broken = false) (hs : SumRel (.watch w) R) :
    value w.machine.control.distance + value w.lag = R := hs hb

/-! ## 2. `LandingFreshC` is false -/

/-- **`LandingFreshC` is refuted** by any landing whose chain watches and whose
compare lens carries the post-`Internal` chain: `h` is free, so the clause
`periodLength w' = h` is contradictory. -/
theorem not_landingFreshC (P : Shared) (q : ℕ) (first : Fin 9) (cP : Control) (sP : GalilVM)
    (hex : ∃ (c1 : Control) (s1 : GalilVM) (w w' : GalilScaffoldChainWatch.State)
      (vs : ScanVM) (vq' : SearchVM),
      LandingL P q first cP sP c1 s1 ∧ s1.chain = ChainVM.watch w ∧
      GalilScaffoldChainWatch.Internal w w' ∧
      (afterMismatch s1 vs vq').chain = ChainVM.watch w') :
    ¬ LandingFreshC P q first cP sP := by
  intro hL
  obtain ⟨c1, s1, w, w', vs, vq', hland, hw, hint, hch⟩ := hex
  have h0 := (hL c1 s1 w w' 0 vs vq' _ hland hw hint ⟨hch, rfl⟩).2.2.2
  have h1 := (hL c1 s1 w w' 1 vs vq' _ hland hw hint ⟨hch, rfl⟩).2.2.2
  omega

/-! ## 3. The residue: the leaf without the period clause -/

/-- **`LandingFreshC` with the (false) period clause removed.**  This is the
part that is genuinely a transport statement about the landing; the shift
amount `h` no longer occurs, so it is `h`-free and consistent. -/
def LandingFreshC' (P : Shared) (q : ℕ) (first : Fin 9) (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (c1 : Control) (s1 : GalilVM) (w w' : GalilScaffoldChainWatch.State),
    LandingL P q first cP sP c1 s1 → s1.chain = ChainVM.watch w →
    GalilScaffoldChainWatch.Internal w w' →
    GalilScaffoldChainWatch.CanonicalState w ∧ FreshC w'.machine.control ∧
      (∃ Rnow : ℤ, SumRel (.watch w') Rnow)

/-- The period clause, at the level where `h` is actually chosen. -/
def ShiftPeriodC (P : Shared) (q : ℕ) (first : Fin 9) (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (c1 : Control) (s1 : GalilVM) (w w' : GalilScaffoldChainWatch.State) (h : ℕ)
    (vs : ScanVM) (vq' : SearchVM) (s2' : GalilVM),
    LandingL P q first cP sP c1 s1 → s1.chain = ChainVM.watch w →
    GalilScaffoldChainWatch.Internal w w' →
    P.beginShift (afterMismatch s1 vs vq') s2' →
    beginShiftVM h w' (afterMismatch s1 vs vq') s2' → periodLength w' = h

/-- Round 41's leaf is exactly the residue plus the route-level period clause
(so the split is faithful). -/
theorem landingFreshC_of_parts (P : Shared) (q : ℕ) (first : Fin 9) (cP : Control) (sP : GalilVM)
    (h1 : LandingFreshC' P q first cP sP)
    (h2 : ∀ (c1 : Control) (s1 : GalilVM) (w w' : GalilScaffoldChainWatch.State) (h : ℕ)
      (vs : ScanVM) (vq' : SearchVM) (s2' : GalilVM),
      LandingL P q first cP sP c1 s1 → s1.chain = ChainVM.watch w →
      GalilScaffoldChainWatch.Internal w w' →
      beginShiftVM h w' (afterMismatch s1 vs vq') s2' → periodLength w' = h) :
    LandingFreshC P q first cP sP := by
  intro c1 s1 w w' h vs vq' s2' hland hw hint hb
  exact ⟨(h1 c1 s1 w w' hland hw hint).1, (h1 c1 s1 w w' hland hw hint).2.1,
    (h1 c1 s1 w w' hland hw hint).2.2, h2 c1 s1 w w' h vs vq' s2' hland hw hint hb⟩

end PalPeg.CloseoutWatchRound44

#print axioms PalPeg.CloseoutWatchRound44.not_landingFreshC
#print axioms PalPeg.CloseoutWatchRound44.landingFreshC_of_parts
#print axioms PalPeg.CloseoutWatchRound44.sumRel_watch_of_unbroken
