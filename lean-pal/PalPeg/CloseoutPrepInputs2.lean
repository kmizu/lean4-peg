import PalPeg.CloseoutPrepInputs
import PalPeg.GalilPrepMatch

/-!
# The preparation without the delay-fit assumption (`SpanFitsC` removed)

`CloseoutPrepInputs.SpanFitsC` (`2k+2 < 2048` for every candidate semiperiod of
a stage window) is **not** a bookkeeping gap: a stage window has span
`8 * max lower 1`, so a large period genuinely does not fit inside one
comparison delay, and the background-only construction
`GalilPrepConstruct.prep_segment_construct_of_found` cannot be used.

This file replaces it by the *general* preparation
(`GalilPrepMatch.prep_segment_construct_or_fallback_matched`, built on
`GalilPrepClock.prep_segment_construct_general`), which drives the same `2h+2`
chain ticks through an arbitrary clock — background ticks and matched
comparisons as the clock dictates — and needs **no** bound on `h` versus the
delay.  Two things change, and both are handled rather than assumed:

* the comparisons the clock forces inside the segment are no longer vacuous, so
  the construction has a second exit: a strictly shorter prefix ending at a
  clock-one *mismatch* with the chain still preparing.  That exit is a
  `fallback` route (`GalilPrepMatch.fallback_from_prep`), named here as
  `MismatchExitG`.  Note that `hmatch` is therefore **not** a named hypothesis
  anywhere in this file: the mismatch case is carried as a disjunct;
* the landing watch is `⟨⟨ver, ready cen ys b⟩, lag, margin⟩` with
  `value lag = value radius + 1 + es.count true`, **not**
  `GalilNoShiftStage.freshWatch` (whose lag is exactly `inc radius`).  So the
  `hwatch2` premise of `GalilNoShiftDischarge.foundRouteMC_noshift_d` — which
  asks for `s2.chain = .watch (freshWatch sF.center cen ys b sF.radius)` — is
  *not* available on this route.  The break continuation is therefore consumed
  in its segment-shaped form (`WatchSegE` + length + `∃ ww, .watch ww`), which
  is exactly what `CloseoutFoundCompare.BreakExit`/`RoundsExit` ask for.
  Recovering the `freshWatch` shape needs `es.count true = 0`, i.e. the
  delay-fit again; that is recorded as `NoCompareInPrepG` and is *not* used.

Derived here:

* `prep_of_prepInputsG` — from `PrepInputsG` (`PrepInputs` with the `hfit`
  conjunct deleted and `0 ≤ value sP.radius` added), either the full `2*hh+2`
  preparation segment out of the post-comparison state, with the landing watch
  and the lag ledger, or the mismatch stop.
* `foundExit_of_compare'` — `CloseoutFoundCompare.foundExit_of_compare` over
  `PrepInputsG`, with the mismatch branch as the one extra continuation.
* `prepInputs_of_found'` — `CloseoutPrepInputs.prepInputs_of_found` with
  `SpanFitsC` deleted from its premises.

Still open, unchanged, as NAMED hypotheses (see `CloseoutPrepInputs`):
`FirstStageC`, `PostCompareC`, plus the new `MismatchExitG`.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPrepInputs2

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilInvPlus
open PalPeg.GalilFoundStage PalPeg.GalilFoundStageInv
open PalPeg.GalilScaffoldChainInputSupply (Decodes)
open PalPeg.CloseoutContracts PalPeg.CloseoutFoundCompare
open PalPeg.CloseoutPrepInputs (FirstStageC PostCompareC)

/-! ## 1. The search datum without the delay-fit conjunct -/

/-- `CloseoutFoundCompare.PrepInputs` with the `2k+2 < 2048` conjunct deleted
and the sign condition on the radius added, as `prep_segment_construct_matched`
needs it. -/
def PrepInputsG (P : Shared) (qq : ℕ) (first : Fin 9) (p : GalilScaffoldPlace.Place)
    (lower span : ℕ) (cP : Control) (sP : GalilVM) : Prop :=
  ∃ (sq tq : GalilScaffoldSearchFinish.State) (x y : GalilScaffoldControl.Machine 12)
    (as : List Bool),
    GalilScaffoldSearchRun.SafeQuanta sq x as tq y ∧ sq.mode = .run ∧ tq.mode = .found ∧
    GalilDpCorrect.Result ((GalilScaffoldPlace.stream p).take (span+1)) lower 0
      (GalilScaffoldProgram.denote y.config) ∧
    cP.mode = .scan ∧ cP.replaying = false ∧ cP.clock = 2048 ∧
    0 ≤ value sP.radius ∧
    (∀ cen : Fin 3, GalilScaffoldPlace.read p = some cen →
      ChainMatched (chainStart (y.config.tapes 11) cen p sP.center sP.radius) sP.chain)

/-- `PrepInputs` (with its `hfit`) refines `PrepInputsG`, given the radius sign,
so every consumer of `PrepInputsG` also serves the old datum. -/
theorem prepInputsG_of_prepInputs (P : Shared) (qq : ℕ) (first : Fin 9)
    (p : GalilScaffoldPlace.Place) (lower span : ℕ) {cP : Control} {sP : GalilVM}
    (hrad : 0 ≤ value sP.radius)
    (h : PrepInputs P qq first p lower span cP sP) :
    PrepInputsG P qq first p lower span cP sP := by
  obtain ⟨sq, tq, x, y, as, hrq, hsq, htq, hv, hm, hr, hclk, hchv, -⟩ := h
  exact ⟨sq, tq, x, y, as, hrq, hsq, htq, hv, hm, hr, hclk, hrad, hchv⟩

/-! ## 2. The general preparation, or the mismatch stop -/

/-- **The preparation segment from `PrepInputsG`.**  No bound on the candidate
semiperiod versus the delay.  Either the full `2*hh+2`-tick watched segment
(with the landing watch and the lag ledger `radius + 1 + #true`), or a strictly
shorter prefix stopping at a clock-one mismatch with the chain still
preparing. -/
theorem prep_of_prepInputsG (P : Shared) (qq : ℕ) (first : Fin 9)
    (p : GalilScaffoldPlace.Place) (lower span : ℕ) {cP : Control} {sP : GalilVM}
    (h : PrepInputsG P qq first p lower span cP sP) :
    (∃ (hh : ℕ) (es : List Bool) (c2 : Control) (s2 : GalilVM),
        GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream p).take (span+1)) lower hh ∧
        WatchSegE P qq first 2048 es cP sP c2 s2 ∧ es.length = 2*hh+2 ∧
        (∃ ww : GalilScaffoldChainWatch.State, s2.chain = ChainVM.watch ww) ∧
        (∃ (cen : Fin 3) (ys : List (Fin 3)) (b : Fin 3) (lag margin : Counter),
          s2.chain = ChainVM.watch
            ⟨⟨sP.center, GalilScaffoldChainConsume.ready cen ys b⟩, lag, margin⟩ ∧
          value lag = value sP.radius + 1 + (es.count true : ℤ)) ∧
        c2.mode = .scan ∧ c2.replaying = false ∧ 1 ≤ c2.clock ∧ c2.clock ≤ 2048) ∨
    (∃ (hh : ℕ) (es : List Bool) (c1 : Control) (s1 : GalilVM),
        WatchSegE P qq first 2048 es cP sP c1 s1 ∧ es.length < 2*hh+2 ∧
        c1.mode = .scan ∧ c1.replaying = false ∧ c1.clock = 1 ∧ canRight s1.right ∧
        read (left s1.left) ≠ read (right s1.right) ∧
        GalilPrepMatch.PrepChain s1.chain ∧
        GalilPrepClock.lagv s1.chain = value sP.radius + 1 + (es.count true : ℤ) ∧
        (∃ z, ChainTick false s1.chain z) ∧
        (∀ (vs : ScanVM) (vq : SearchVM), ChainTick false s1.chain vs.chain →
          ¬ shiftGuardVM (afterMismatch s1 vs vq))) := by
  classical
  obtain ⟨sq, tq, x, y, as, hrq, hsq, htq, hv, hm, hr, hclk, hrad, hchv⟩ := h
  obtain ⟨hh, cen, u, q', ys, b, hcand, hread, hcopy, hu, hpos, hfocus, hback, -, -⟩ :=
    GalilScaffoldChainPeriod.found_start_back p rfl hrq hsq htq hv
  rcases GalilPrepMatch.prep_segment_construct_or_fallback_matched P qq first 2048
      (by omega) (y.config.tapes 11) cen p q' sP.center sP.radius hrad u hh ys b hcopy hu hpos
      hfocus hback cP sP hm hr (by omega) (by omega) (hchv cen hread) with
    ⟨es, bs, cs, dm, c2, s2, hseg, hes, hlen, hbs, hcs, ⟨lag, margin, hw, hvv⟩, hm2, hr2, h12,
      h22⟩ |
    ⟨es, c1, s1, hseg, hlen, hm1, hr1, hc1, ha1, hmis, hpc, hlagv, htk, hg⟩
  · exact Or.inl ⟨hh, es, c2, s2, hcand, hseg, hlen, ⟨_, hw⟩,
      ⟨cen, ys, b, lag, margin, hw, hvv⟩, hm2, hr2, h12, h22⟩
  · exact Or.inr ⟨hh, es, c1, s1, hseg, hlen, hm1, hr1, hc1, ha1, hmis, hpc, hlagv, htk, hg⟩

/-! ## 3. The new named continuation: the mismatch stop -/

/-- **NAMED (new).**  The mismatch exit of the general preparation: the segment
stops at a clock-one comparison whose outer symbols disagree while the chain is
still copying or walking back, and the guard failure that
`GalilPrepMatch.fallback_from_prep` needs is already proved there.  Its landing
is assumed to carry `FoundExit`. -/
def MismatchExitG (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es : List Bool) (c1 : Control) (s1 : GalilVM),
    WatchSegE P q first 2048 es cP sP c1 s1 → c1.mode = .scan → c1.replaying = false →
    c1.clock = 1 → canRight s1.right → read (left s1.left) ≠ read (right s1.right) →
    GalilPrepMatch.PrepChain s1.chain →
    (∀ (vs : ScanVM) (vq : SearchVM), ChainTick false s1.chain vs.chain →
      ¬ shiftGuardVM (afterMismatch s1 vs vq)) →
    FoundExit P q first raw m c r

/-- **NAMED (recorded, unused).**  The landing watch has the `freshWatch` shape
exactly when no comparison is credited inside the preparation.  This is the
`hwatch2` premise of `GalilNoShiftDischarge.foundRouteMC_noshift_d`, and it is
equivalent to the delay-fit assumption this file removes. -/
def NoCompareInPrepG (P : Shared) (qq : ℕ) (first : Fin 9) (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es : List Bool) (c2 : Control) (s2 : GalilVM),
    WatchSegE P qq first 2048 es cP sP c2 s2 → es.count true = 0

/-! ## 4. The comparison-tick found leaf over `PrepInputsG` -/

/-- **`CloseoutFoundCompare.foundExit_of_compare` without `SpanFitsC`.**  Same
statement, `PrepInputs` replaced by `PrepInputsG`, with the mismatch exit of the
general preparation as the one extra named continuation. -/
theorem foundExit_of_compare' (centreC : GalilVM → Fin 3)
    (placeC : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (m : ℕ) (hP : Decodes (PofC centreC placeC entry w))
    {c c' cP : Control} {r t sP : GalilVM}
    (hE : StageEntryC (PofC centreC placeC entry w) q first w c r)
    (hsW : SegReachedW centreC placeC entry q first w c r c' t)
    (hcl : c'.clock = 1) (hav : canRight t.right) (hidle : t.chain = .idle)
    (hmt : read (left t.left) = read (right t.right))
    (a : Fin 2) (ls rs qq : List (Fin 2)) (gap : Bool)
    (hcen : t.center = represent ⟨a :: ls, gap⟩ (rs.map some) qq)
    (vq : SearchVM) (hq : searchEffect (PofC centreC placeC entry w) true t vq)
    (hfound : vq.search.mode = .found)
    (hpos : position t.right ≤ 2 * m - 2)
    {lower span : ℕ}
    (hprep : PrepInputsG (PofC centreC placeC entry w) q first ⟨a :: ls, gap⟩ lower span cP sP)
    (hmis : MismatchExitG (PofC centreC placeC entry w) q first w m c r cP sP)
    (hbranch : RoundsExit (PofC centreC placeC entry w) q first w m c r cP sP ∨
      BreakExit (PofC centreC placeC entry w) q first w m c r cP sP) :
    FoundExit (PofC centreC placeC entry w) q first w m c r := by
  classical
  rcases prep_of_prepInputsG (PofC centreC placeC entry w) q first ⟨a :: ls, gap⟩ lower span
      hprep with
    ⟨hh, es, c2, s2, -, hseg2, hlen, hwatch, -, -, -, -, -⟩ |
    ⟨-, es, c1, s1, hseg1, -, hm1, hr1, hc1, ha1, hne1, hpc1, -, -, hg1⟩
  · rcases hbranch with hro | hbr
    · obtain ⟨cT, sT, k, L, hst, hcr, hM, hR, hres, hSpan, hprog, hp⟩ :=
        hro hh es c2 s2 hseg2 hlen hwatch
      exact .landed cT sT k L hst hcr hM hR hres hSpan hprog hp
    · obtain ⟨cT, sT, k, L, hst, hcr, hIT, hcenT, hstg, hcc, hlt, hp⟩ :=
        hbr hh es c2 s2 hseg2 hlen hwatch
      exact .broke cT sT k L hst hcr hIT hcenT hstg hcc hlt hp
  · exact hmis es c1 s1 hseg1 hm1 hr1 hc1 ha1 hne1 hpc1 hg1

/-! ## 5. `prepInputs_of_found` without `SpanFitsC` -/

/-- **`CloseoutPrepInputs.prepInputs_of_found` with `SpanFitsC` deleted.**  The
quantum and the DP `Result` come from `idle_segment_found_quantum` exactly as
before; only the delay-fit conjunct of the conclusion is gone, replaced by the
radius sign that the general preparation needs. -/
theorem prepInputs_of_found' (centreC : GalilVM → Fin 3)
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
    (hrad : 0 ≤ value sP.radius)
    (hpost : PostCompareC ⟨a :: ls, gap⟩ vq.dp cP sP)
    (hfirst : ∀ (r0 : GalilVM) (es1 : List Bool), FirstStageC ⟨a :: ls, gap⟩ r0 es1) :
    ∃ lower span : ℕ,
      PrepInputsG (PofC centreC placeC entry w) q first ⟨a :: ls, gap⟩ lower span cP sP := by
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
      hqq, hm2, hfound, hres, hpost.1, hpost.2.1, hpost.2.2.1, hrad, hpost.2.2.2⟩
  · exact absurd hesc (hfirst r0 es0)

end PalPeg.CloseoutPrepInputs2

#print axioms PalPeg.CloseoutPrepInputs2.prepInputsG_of_prepInputs
#print axioms PalPeg.CloseoutPrepInputs2.prep_of_prepInputsG
#print axioms PalPeg.CloseoutPrepInputs2.foundExit_of_compare'
#print axioms PalPeg.CloseoutPrepInputs2.prepInputs_of_found'
