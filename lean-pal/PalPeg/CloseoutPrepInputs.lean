import PalPeg.CloseoutFoundCompare
import PalPeg.GalilSearchResult

/-!
# `PrepInputs` from the stage entry

`CloseoutFoundCompare.PrepInputs` is the search machine's own record of a found
answer, in the shape `GalilPrepConstruct.prep_segment_construct_of_found`
consumes.  This file derives the two components that the development really
proves — the **search quantum** (`SafeQuanta`, entered in `run`, left in
`found`) and the **DP `Result`** on the stage window — from the closeout entry
`StageEntryC` plus `Decodes` and a found `searchEffect`, and names, with their
exact types, the components that no lemma reachable from `InvLPS` exports.

Derived here (`prepInputs_of_found`, arrival bit `aF` free, so it serves both
the comparison tick `aF = true` and the background tick `aF = false`):

* `idle_segment_found_quantum` over the restart segment of
  `StageEntryC.stage` (carried by `GalilFoundStageInv.replayStage_trans`) gives
  `v2.search.mode = .run`, `SafeQuanta v2.search v2.dp usedQ vq.search vq.dp`
  and `Result ((stream p).take (8*max k 1+1)) k 0 (denote vq.dp.config)` — i.e.
  `lower = k = value last`, `span = 8*max k 1`.

Open, as NAMED hypotheses (exact types below):

* `FirstStageC` — the found tick belongs to the first stage of the restart
  (the second disjunct of `idle_segment_found_quantum`: the first stage already
  halted inside the segment in a non-`found` mode).  A later stage does carry a
  quantum (`GalilSearchResult.search_later_stage`), but nothing on the route
  `found_radius_le_all_stages` → `later_found` exports it at the tick.
* `PostCompareC` — the post-tick control/state shape (`cP.mode = .scan`,
  `cP.replaying = false`, `cP.clock = 2048`) together with the chain match
  `ChainMatched (chainStart …) sP.chain`.  This is a fact about the *step* out
  of the found tick, not about the found tick.
* `SpanFitsC` — every candidate semiperiod of a stage window fits in one delay
  (`2*k+2 < 2048`).  `Candidate` on `take (span+1)` bounds `k` by `span` only,
  and `span = 8*max lower 1` is not bounded by the delay in the present
  development, so this is a genuine gap, not bookkeeping.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPrepInputs

open PalPeg PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilScaffoldInputHead
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter
open PalPeg.GalilRunSkeleton PalPeg.GalilInvPlus
open PalPeg.GalilFoundStage PalPeg.GalilFoundStageInv
open PalPeg.CloseoutContracts PalPeg.CloseoutFoundCompare

/-! ## 1. The named hypotheses -/

/-- **NAMED 1.**  The found tick belongs to the first stage after the restart:
the escape disjunct of `idle_segment_found_quantum` is
excluded. -/
def FirstStageC (p : GalilScaffoldPlace.Place) (r : GalilVM) (es1 : List Bool) : Prop :=
  ¬ ∃ (L : ℕ) (vL : SearchVM), L ≤ es1.length ∧
      SearchRun p (es1.take L) (searchLens.get r) vL ∧
      vL.search.mode ≠ .run ∧ vL.search.mode ≠ .found

/-- **NAMED 2.**  The state the preparation starts from: the control after the
tick is a fresh full-clock non-replaying scan, and the chain carries the fresh
watch of the answer tape. -/
def PostCompareC (p : GalilScaffoldPlace.Place) (y : GalilScaffoldControl.Machine 12)
    (cP : Control) (sP : GalilVM) : Prop :=
  cP.mode = .scan ∧ cP.replaying = false ∧ cP.clock = 2048 ∧
    ∀ cen : Fin 3, GalilScaffoldPlace.read p = some cen →
      ChainMatched (chainStart (y.config.tapes 11) cen p sP.center sP.radius) sP.chain

/-- **NAMED 3.**  Every candidate semiperiod of a stage window fits in one
delay. -/
def SpanFitsC (p : GalilScaffoldPlace.Place) : Prop :=
  ∀ lower k : ℕ,
    GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream p).take (8 * max lower 1 + 1)) lower k →
    2 * k + 2 < 2048

/-! ## 2. The derivation -/

/-- **`PrepInputs` at a found tick of the first stage.**  `aF` is the arrival
bit: `aF = true` is the comparison tick of `CloseoutFoundCompare`, `aF = false`
the background tick.  The quantum and the DP `Result` are derived; the three
named hypotheses above are passed through. -/
theorem prepInputs_of_found (centreC : GalilVM → Fin 3)
    (placeC : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (hP : Decodes (PofC centreC placeC entry w))
    {c c' cP : Control} {r t sP : GalilVM}
    (hE : StageEntryC (PofC centreC placeC entry w) q first w c r)
    (hsW : SegReachedW centreC placeC entry q first w c r c' t)
    (aF : Bool) (hcl : aF = true → c'.clock = 1) (hidle : t.chain = .idle)
    (a : Fin 2) (ls rs qq : List (Fin 2)) (gap : Bool)
    (hcen : t.center = represent ⟨a :: ls, gap⟩ (rs.map some) qq)
    (vq : SearchVM) (hq : searchEffect (PofC centreC placeC entry w) aF t vq)
    (hfound : vq.search.mode = .found)
    (hfit : SpanFitsC ⟨a :: ls, gap⟩)
    (hpost : PostCompareC ⟨a :: ls, gap⟩ vq.dp cP sP)
    (hfirst : ∀ (r0 : GalilVM) (es1 : List Bool), FirstStageC ⟨a :: ls, gap⟩ r0 es1) :
    ∃ lower span : ℕ,
      PrepInputs (PofC centreC placeC entry w) q first ⟨a :: ls, gap⟩ lower span cP sP := by
  classical
  obtain ⟨-, es, hseg⟩ := hsW
  obtain ⟨r0, Rad, last, es0, c0, hR0, hSt0, hcl0, hseg0⟩ :=
    replayStage_trans hE.stage hseg
  obtain ⟨hidle0, hrep0, hfoc0, hscan0, ⟨hrc, hrv⟩, -, hsearch, hlower, hlast, hlv⟩ := hR0
  have hcen0 : r0.center = represent ⟨a :: ls, gap⟩ (rs.map some) qq := by
    rw [← watchSegE_center (PofC centreC placeC entry w) q first 2048 hseg0]; exact hcen
  obtain ⟨hreadr, hplr⟩ := hP.1 r0 a ls rs qq gap hcen0
  obtain ⟨k, hk⟩ : ∃ k : ℕ, value last = (k : ℤ) :=
    ⟨(value last).toNat, (Int.toNat_of_nonneg hlv).symm⟩
  have hstep : searchStep ((PofC centreC placeC entry w).place t) aF (searchLens.get t) vq := by
    rcases hq with ⟨-, hstep⟩ | ⟨hne, -⟩
    · exact hstep
    · exact absurd hidle hne
  rcases idle_segment_found_quantum (PofC centreC placeC entry w) q first hP.2
      a ls rs qq gap hcl0 hplr hcen0 ((PofC centreC placeC entry w).centre r0) hreadr
      last r0.radius hlast k hk hrc Rad hrv (hSt0 k hk) hsearch hlower hseg0 hidle aF hcl vq hstep
      hfound with
    ⟨v2, usedQ, hm2, hqq, -, hres, -⟩ | hesc
  · exact ⟨k, 8 * max k 1, v2.search, vq.search, v2.dp, vq.dp, usedQ,
      hqq, hm2, hfound, hres, hpost.1, hpost.2.1, hpost.2.2.1, hpost.2.2.2,
      fun k' hc' => hfit k k' hc'⟩
  · exact absurd hesc (hfirst r0 es0)

end PalPeg.CloseoutPrepInputs

#print axioms PalPeg.CloseoutPrepInputs.prepInputs_of_found
