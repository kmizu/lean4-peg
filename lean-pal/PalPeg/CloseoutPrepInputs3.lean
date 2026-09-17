import PalPeg.CloseoutPrepInputs2
import PalPeg.CloseoutFoundExits
import PalPeg.GalilLeafReport

/-!
# The three named hypotheses of `CloseoutPrepInputs` / `CloseoutPrepInputs2`

## 1. `PostCompareC` — **discharged, and the stated form refuted**

`compareFound`'s chain clause is `chainAt a found ans (P.centre s) (P.place s)
s.center s.radius s.chain vs.chain`: the `chainStart` of a found comparison is
taken at the **pre**-comparison radius, while `afterCompare` leaves with
`radius := inc s.radius`.  So at the post state `sP`:

* `postCompare_shape` — `sP.center = t.center`, `sP.radius = inc t.radius`, and
  `sP.chain = chainStart (vq.dp.config.tapes 11) (P.centre t) (P.place t)
  sP.center sP.radius` (the `ChainMatched.copy` of the start at `t.radius`
  *is* the start at `inc t.radius`);
* `not_postCompareC` — therefore `CloseoutPrepInputs.PostCompareC`, which asks
  for `ChainMatched (chainStart … sP.radius) sP.chain`, is **false** at that
  state: `not_chainMatched_self` shows `ChainMatched` on a `copy` strictly
  increments the lag.  `PostCompareC` is off by one increment;
* `PostCompareG` / `postCompareG_of_compare` — the corrected contract (the
  start taken at a radius `rad0` with `sP.radius = inc rad0`), **proved** from
  the comparison tick, with no named residue.

The correction propagates: `prep_of_prepInputsG3` lands with lag
`value sP.radius + #true`, **not** `value sP.radius + 1 + #true` as
`CloseoutPrepInputs2.prep_of_prepInputsG` claims — the `+1` of
`prep_segment_construct_or_fallback_matched` is the increment the comparison has
already paid into `sP.radius`.  `PrepInputsG3`, `foundExit_of_compare3` and
`prepInputs3_of_found` are the datum and the two consumers over the corrected
contract.

## 2. `FirstStageC` — traded for a positive obligation

`LaterQuantumC` is the later stage's own quantum and DP `Result` in the shape
`PrepInputsG3` needs (the conclusion of `GalilSearchResult.search_later_stage`).
`prepInputs3_of_found_or_later` discharges the escape branch with it, so the
negative assumption `FirstStageC` is no longer needed.  `LaterQuantumC` stays
NAMED: `search_later_stage` needs a `.double` entry with `n % 4 = 0`, `8 ≤ n`,
`4*k ≤ n` and the stage length budget, and neither
`GalilLaterRadius.found_radius_le_all_stages` nor `later_found` exports that
entry *at the found tick* — they export the DP facts only.

## 3. `MismatchExitG` — reduced to the landing record

`FallbackRouteG` + `mismatchExitG_of_route`.  `GalilPrepMatch.fallback_from_prep`
already proves the guard failure and the existence of the fallback landing from
the mismatch stop; what is missing is the *record* — the run from `⟨c, r⟩`, its
`CostedRun`, the upgrade of the landing to the restart pack `Inv` with
`SpanRep`, and the two head positions.  That is exactly `FallbackRouteG`, and
`CloseoutFoundExits.landed_pack` turns it into `FoundExit.landed`.  So
`MismatchExitG` carries no obligation beyond the fallback route itself.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPrepInputs3
open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilInvPlus
open PalPeg.CloseoutContracts PalPeg.CloseoutFoundCompare

theorem postCompare_shape (P : Shared) (q : ℕ) (first : Fin 9) {t s' : GalilVM}
    (hcmp : (galilFrameS P q first).compare t s')
    (hmt : read (left t.left) = read (GalilScaffoldChainVerifier.right t.right))
    (hidle : t.chain = ChainVM.idle) :
    ∃ vq : SearchVM, searchEffect P true t vq ∧
      s'.center = t.center ∧ s'.radius = inc t.radius ∧
      (vq.search.mode = .found →
        s'.chain = chainStart (vq.dp.config.tapes 11) (P.centre t) (P.place t) s'.center s'.radius) := by
  obtain ⟨vs, vq, a, hl, hr, hiff, hq, hch, hteq⟩ : compareFound P q first t s' := hcmp
  have hma : (galilFrame P q first).matched (scanLens.set t vs) := by
    show read vs.left = read vs.right
    rw [hl, hr]; exact hmt
  have ha : a = true := hiff.2 hma
  subst ha
  rw [if_pos rfl] at hteq
  subst hteq
  refine ⟨vq, hq, ?_, ?_, ?_⟩
  · rw [afterBirth_center]; exact afterCompare_center _ _ _
  · rw [afterBirth_radius]; exact afterCompare_radius _ _ _
  intro hf
  rw [afterBirth_chain, afterBirth_center, afterBirth_radius,
    afterCompare_chain, afterCompare_center, afterCompare_radius]
  rcases hch with ⟨hne, -⟩ | ⟨-, hfalse, -⟩ | ⟨-, -, hstart⟩
  · exact absurd hidle hne
  · rw [hf] at hfalse; simp at hfalse
  · rw [if_pos rfl] at hstart
    generalize hx : vs.chain = x at hstart
    cases hstart
    rfl

/-! ## 2. The off-by-one in `CloseoutPrepInputs.PostCompareC` -/

/-- **Negative.**  A chain that *is* `chainStart … sP.center sP.radius` is not a
`ChainMatched` successor of `chainStart … sP.center sP.radius`: `ChainMatched`
on a `copy` increments the lag.  By `postCompare_shape` this is exactly the
chain the machine has after the found comparison, so
`CloseoutPrepInputs.PostCompareC` — whose `chainStart` is taken at the *post*
radius — is unsatisfiable at the state it is meant to describe. -/
theorem chainMatched_copy_shape {t : GalilScaffoldTape.Tape} {h : Counter}
    {p : GalilScaffoldPlace.Place} {v : GalilScaffoldChainPeriod.Tape} {lag margin : Counter}
    {ver : PlaceHead} {z : ChainVM}
    (h2 : ChainMatched (ChainVM.copy t h p v lag margin ver) z) :
    z = ChainVM.copy t h p v (inc lag) (inc margin) ver := by
  cases h2; rfl

theorem not_chainMatched_self (ans : GalilScaffoldTape.Tape) (cen : Fin 3)
    (p : GalilScaffoldPlace.Place) (ver : PlaceHead) (rad : Counter) {z : ChainVM}
    (hz : z = chainStart ans cen p ver rad) :
    ¬ ChainMatched (chainStart ans cen p ver rad) z := by
  intro h
  have hs := chainMatched_copy_shape h
  rw [hz] at hs
  unfold chainStart at hs
  rw [ChainVM.copy.injEq] at hs
  have hinc : rad = inc rad := hs.2.2.2.2.1
  have := inc_value rad
  rw [← hinc] at this
  omega

/-- **The refutation at the machine's own post-compare state.** -/
theorem not_postCompareC (P : Shared) (q : ℕ) (first : Fin 9) {t s' : GalilVM}
    (hcmp : (galilFrameS P q first).compare t s')
    (hmt : read (left t.left) = read (GalilScaffoldChainVerifier.right t.right))
    (hidle : t.chain = ChainVM.idle) {vq : SearchVM} (hq : searchEffect P true t vq)
    (hdet : ∀ v : SearchVM, searchEffect P true t v → v = vq)
    (hf : vq.search.mode = .found)
    (hread : GalilScaffoldPlace.read (P.place t) = some (P.centre t)) (cP : Control) :
    ¬ CloseoutPrepInputs.PostCompareC (P.place t) vq.dp cP s' := by
  intro hpost
  obtain ⟨v, hqv, -, -, hchain⟩ := postCompare_shape P q first hcmp hmt hidle
  have hv : v = vq := hdet v hqv
  subst hv
  exact not_chainMatched_self _ _ _ _ _ (hchain hf)
    (hpost.2.2.2 (P.centre t) hread)


/-! ## 3. The corrected post-compare contract, and the preparation over it -/

/-- **`PostCompareC` corrected.**  The `chainStart` of the found comparison is
taken at the *pre*-comparison radius, and the post radius is its increment —
which is what `compareFound`'s `chainAt … s.center s.radius` actually says. -/
def PostCompareG (p : GalilScaffoldPlace.Place) (y : GalilScaffoldControl.Machine 12)
    (cP : Control) (sP : GalilVM) : Prop :=
  cP.mode = .scan ∧ cP.replaying = false ∧ cP.clock = 2048 ∧
    ∃ rad0 : Counter, sP.radius = inc rad0 ∧ 0 ≤ value rad0 ∧
      ∀ cen : Fin 3, GalilScaffoldPlace.read p = some cen →
        ChainMatched (chainStart (y.config.tapes 11) cen p sP.center rad0) sP.chain

/-- **NAMED 1 discharged.**  `PostCompareG` at the machine's own post-compare
state: the control facts are the ones the scan tick installs, the chain fact is
`postCompare_shape`. -/
theorem postCompareG_of_compare (P : Shared) (q : ℕ) (first : Fin 9) {t s' : GalilVM}
    (hcmp : (galilFrameS P q first).compare t s')
    (hmt : read (left t.left) = read (GalilScaffoldChainVerifier.right t.right))
    (hidle : t.chain = ChainVM.idle) {vq : SearchVM} (hq : searchEffect P true t vq)
    (hdet : ∀ v : SearchVM, searchEffect P true t v → v = vq)
    (hf : vq.search.mode = .found) (hrad : 0 ≤ value t.radius)
    (hread0 : GalilScaffoldPlace.read (P.place t) = some (P.centre t))
    {cP : Control} (hm : cP.mode = .scan) (hr : cP.replaying = false) (hc : cP.clock = 2048) :
    PostCompareG (P.place t) vq.dp cP s' := by
  obtain ⟨v, hqv, hcen, hradE, hchain⟩ := postCompare_shape P q first hcmp hmt hidle
  have hv : v = vq := hdet v hqv
  subst hv
  refine ⟨hm, hr, hc, t.radius, hradE, hrad, ?_⟩
  intro cen hread
  have hcc : cen = P.centre t := Option.some.inj (hread.symm.trans hread0)
  subst hcc
  have hz := hchain hf
  rw [hradE] at hz
  rw [hz]
  exact ChainMatched.copy _ _ _ _ _ _ _

/-- `CloseoutPrepInputs2.PrepInputsG` with the chain clause corrected. -/
def PrepInputsG3 (P : Shared) (qq : ℕ) (first : Fin 9) (p : GalilScaffoldPlace.Place)
    (lower span : ℕ) (cP : Control) (sP : GalilVM) : Prop :=
  ∃ (sq tq : GalilScaffoldSearchFinish.State) (x y : GalilScaffoldControl.Machine 12)
    (as : List Bool),
    GalilScaffoldSearchRun.SafeQuanta sq x as tq y ∧ sq.mode = .run ∧ tq.mode = .found ∧
    GalilDpCorrect.Result ((GalilScaffoldPlace.stream p).take (span+1)) lower 0
      (GalilScaffoldProgram.denote y.config) ∧
    cP.mode = .scan ∧ cP.replaying = false ∧ cP.clock = 2048 ∧
    ∃ rad0 : Counter, sP.radius = inc rad0 ∧ 0 ≤ value rad0 ∧
      (∀ cen : Fin 3, GalilScaffoldPlace.read p = some cen →
        ChainMatched (chainStart (y.config.tapes 11) cen p sP.center rad0) sP.chain)

/-- **The preparation segment, with the ledger corrected.**  Same two exits as
`CloseoutPrepInputs2.prep_of_prepInputsG`, but the landing lag is
`value sP.radius + #true`, not `value sP.radius + 1 + #true`: the `+1` of
`prep_segment_construct_or_fallback_matched` is the increment the comparison
already paid into `sP.radius`. -/
theorem prep_of_prepInputsG3 (P : Shared) (qq : ℕ) (first : Fin 9)
    (p : GalilScaffoldPlace.Place) (lower span : ℕ) {cP : Control} {sP : GalilVM}
    (h : PrepInputsG3 P qq first p lower span cP sP) :
    (∃ (hh : ℕ) (es : List Bool) (c2 : Control) (s2 : GalilVM),
        GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream p).take (span+1)) lower hh ∧
        WatchSegE P qq first 2048 es cP sP c2 s2 ∧ es.length = 2*hh+2 ∧
        (∃ ww : GalilScaffoldChainWatch.State, s2.chain = ChainVM.watch ww) ∧
        (∃ (cen : Fin 3) (ys : List (Fin 3)) (b : Fin 3) (lag margin : Counter),
          s2.chain = ChainVM.watch
            ⟨⟨sP.center, GalilScaffoldChainConsume.ready cen ys b⟩, lag, margin⟩ ∧
          value lag = value sP.radius + (es.count true : ℤ)) ∧
        c2.mode = .scan ∧ c2.replaying = false ∧ 1 ≤ c2.clock ∧ c2.clock ≤ 2048) ∨
    (∃ (hh : ℕ) (es : List Bool) (c1 : Control) (s1 : GalilVM),
        WatchSegE P qq first 2048 es cP sP c1 s1 ∧ es.length < 2*hh+2 ∧
        c1.mode = .scan ∧ c1.replaying = false ∧ c1.clock = 1 ∧ canRight s1.right ∧
        read (left s1.left) ≠ read (GalilScaffoldChainVerifier.right s1.right) ∧
        GalilPrepMatch.PrepChain s1.chain ∧
        GalilPrepClock.lagv s1.chain = value sP.radius + (es.count true : ℤ) ∧
        (∃ z, ChainTick false s1.chain z) ∧
        (∀ (vs : ScanVM) (vq : SearchVM), ChainTick false s1.chain vs.chain →
          ¬ shiftGuardVM (afterMismatch s1 vs vq))) := by
  classical
  obtain ⟨sq, tq, x, y, as, hrq, hsq, htq, hv, hm, hr, hclk, rad0, hrad0, hrnn, hchv⟩ := h
  obtain ⟨hh, cen, u, q', ys, b, hcand, hread, hcopy, hu, hpos, hfocus, hback, -, -⟩ :=
    GalilScaffoldChainPeriod.found_start_back p rfl hrq hsq htq hv
  have hledger : value rad0 + 1 = value sP.radius := by
    rw [hrad0, inc_value]
  rcases GalilPrepMatch.prep_segment_construct_or_fallback_matched P qq first 2048
      (by omega) (y.config.tapes 11) cen p q' sP.center rad0 hrnn u hh ys b hcopy hu hpos
      hfocus hback cP sP hm hr (by omega) (by omega) (hchv cen hread) with
    ⟨es, bs, cs, dm, c2, s2, hseg, hes, hlen, hbs, hcs, ⟨lag, margin, hw, hvv⟩, hm2, hr2, h12,
      h22⟩ |
    ⟨es, c1, s1, hseg, hlen, hm1, hr1, hc1, ha1, hmis, hpc, hlagv, htk, hg⟩
  · exact Or.inl ⟨hh, es, c2, s2, hcand, hseg, hlen, ⟨_, hw⟩,
      ⟨cen, ys, b, lag, margin, hw, by rw [hvv, ← hledger]⟩, hm2, hr2, h12, h22⟩
  · exact Or.inr ⟨hh, es, c1, s1, hseg, hlen, hm1, hr1, hc1, ha1, hmis, hpc,
      by rw [hlagv, ← hledger], htk, hg⟩


/-! ## 4. The two consumers, over the corrected datum -/

open PalPeg.GalilFoundStage PalPeg.GalilFoundStageInv
open PalPeg.GalilScaffoldChainInputSupply (Decodes)
open PalPeg.CloseoutPrepInputs (FirstStageC)
open PalPeg.CloseoutPrepInputs2 (MismatchExitG)

/-- `CloseoutPrepInputs2.foundExit_of_compare'` over `PrepInputsG3`. -/
theorem foundExit_of_compare3 (centreC : GalilVM → Fin 3)
    (placeC : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (m : ℕ) (hP : Decodes (PofC centreC placeC entry w))
    {c c' cP : Control} {r t sP : GalilVM}
    (hE : StageEntryC (PofC centreC placeC entry w) q first w c r)
    (hsW : SegReachedW centreC placeC entry q first w c r c' t)
    (a : Fin 2) (ls rs qq : List (Fin 2)) (gap : Bool)
    {lower span : ℕ}
    (hprep : PrepInputsG3 (PofC centreC placeC entry w) q first ⟨a :: ls, gap⟩ lower span cP sP)
    (hmis : MismatchExitG (PofC centreC placeC entry w) q first w m c r cP sP)
    (hbranch : RoundsExit (PofC centreC placeC entry w) q first w m c r cP sP ∨
      BreakExit (PofC centreC placeC entry w) q first w m c r cP sP) :
    FoundExit (PofC centreC placeC entry w) q first w m c r := by
  classical
  rcases prep_of_prepInputsG3 (PofC centreC placeC entry w) q first ⟨a :: ls, gap⟩ lower span
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

/-- `CloseoutPrepInputs2.prepInputs_of_found'` with `PostCompareC` replaced by
the corrected `PostCompareG`.  `FirstStageC` is the only hypothesis left. -/
theorem prepInputs3_of_found (centreC : GalilVM → Fin 3)
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
    (hpost : PostCompareG ⟨a :: ls, gap⟩ vq.dp cP sP)
    (hfirst : ∀ (r0 : GalilVM) (es1 : List Bool), FirstStageC ⟨a :: ls, gap⟩ r0 es1) :
    ∃ lower span : ℕ,
      PrepInputsG3 (PofC centreC placeC entry w) q first ⟨a :: ls, gap⟩ lower span cP sP := by
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
      hqq, hm2, hfound, hres, hpost.1, hpost.2.1, hpost.2.2.1, hpost.2.2.2⟩
  · exact absurd hesc (hfirst r0 es0)


/-! ## 5. `MismatchExitG` reduced to a fallback landing record -/

/-- **NAMED (the residue of `MismatchExitG`).**  The machine's continuation from
the clock-one mismatch stop of the general preparation.  `fallback_from_prep`
already proves, from the mismatch stop alone, that the guard fails and that the
fallback landing exists as a `StepsAll` into a `Restarted` state; what it does
*not* supply — and what no lemma reachable from the closeout entry supplies —
is the landing *record*: the run from `⟨c, r⟩` (not from the stop), its
`CostedRun`, the upgrade of the landing to the restart pack `Inv` with
`SpanRep`, and the two head-position facts. -/
def FallbackRouteG (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es : List Bool) (c1 : Control) (s1 : GalilVM),
    WatchSegE P q first 2048 es cP sP c1 s1 → c1.mode = .scan → c1.replaying = false →
    c1.clock = 1 → canRight s1.right →
    read (left s1.left) ≠ read (GalilScaffoldChainVerifier.right s1.right) →
    GalilPrepMatch.PrepChain s1.chain →
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List GalilTraceCost.Piece),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      GalilTraceCost.CostedRun r sT k L ∧ Inv raw cT sT ∧ SpanRep sT ∧
      position r.center < position sT.center ∧ position sT.right ≤ 2 * m - 1

/-- **Derived.**  `FallbackRouteG` is `CloseoutPrepInputs2.MismatchExitG`: the
landing record is `CloseoutFoundExits.landed_pack`, and the guard-failure
argument of `MismatchExitG` is not needed on this side (it is what
`fallback_from_prep` consumes, not what the exit produces). -/
theorem mismatchExitG_of_route {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c cP : Control} {r sP : GalilVM}
    (h : FallbackRouteG P q first raw m c r cP sP) :
    MismatchExitG P q first raw m c r cP sP := by
  intro es c1 s1 hseg hm hr hc hav hne hpc hg
  obtain ⟨cT, sT, k, L, hst, hcr, hI, hS, hprog, hpos⟩ := h es c1 s1 hseg hm hr hc hav hne hpc
  obtain ⟨hM, hR, hres, hSpan⟩ := PalPeg.CloseoutFoundExits.landed_pack hI hS
  exact .landed cT sT k L hst hcr hM hR hres hSpan hprog hpos

/-! ## 6. `FirstStageC` traded for a positive later-stage export -/

/-- **NAMED (replacing `FirstStageC`).**  The positive form of the escape
branch of `idle_segment_found_quantum`: when the found tick belongs to a later
stage, that stage's own quantum and DP `Result`, in exactly the shape
`PrepInputsG3` asks for.  `GalilSearchResult.search_later_stage` proves this
from a `.double` entry with `n % 4 = 0`, `8 ≤ n`, `4*k ≤ n` and the stage's
length budget; nothing on the route
`found_radius_le_all_stages` → `later_found` exports that entry *at the tick*,
which is why this stays named — but unlike `FirstStageC` it is a statement the
development can hope to prove, not a negative assumption. -/
def LaterQuantumC (p : GalilScaffoldPlace.Place) (y : GalilScaffoldControl.Machine 12) : Prop :=
  ∃ (lower span : ℕ) (sq tq : GalilScaffoldSearchFinish.State)
    (x : GalilScaffoldControl.Machine 12) (as : List Bool),
    GalilScaffoldSearchRun.SafeQuanta sq x as tq y ∧ sq.mode = .run ∧ tq.mode = .found ∧
    GalilDpCorrect.Result ((GalilScaffoldPlace.stream p).take (span+1)) lower 0
      (GalilScaffoldProgram.denote y.config)

/-- **`prepInputs3_of_found` without `FirstStageC`.**  The escape branch is
discharged by `LaterQuantumC` instead of being excluded. -/
theorem prepInputs3_of_found_or_later (centreC : GalilVM → Fin 3)
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
    (hpost : PostCompareG ⟨a :: ls, gap⟩ vq.dp cP sP)
    (hlater : LaterQuantumC ⟨a :: ls, gap⟩ vq.dp) :
    ∃ lower span : ℕ,
      PrepInputsG3 (PofC centreC placeC entry w) q first ⟨a :: ls, gap⟩ lower span cP sP := by
  obtain ⟨lower, span, sq, tq, x, as, hqq, hsq, htq, hres⟩ := hlater
  exact ⟨lower, span, sq, tq, x, vq.dp, as, hqq, hsq, htq, hres,
    hpost.1, hpost.2.1, hpost.2.2.1, hpost.2.2.2⟩


end PalPeg.CloseoutPrepInputs3

#print axioms PalPeg.CloseoutPrepInputs3.postCompare_shape
#print axioms PalPeg.CloseoutPrepInputs3.not_chainMatched_self
#print axioms PalPeg.CloseoutPrepInputs3.not_postCompareC
#print axioms PalPeg.CloseoutPrepInputs3.postCompareG_of_compare
#print axioms PalPeg.CloseoutPrepInputs3.prep_of_prepInputsG3
#print axioms PalPeg.CloseoutPrepInputs3.foundExit_of_compare3
#print axioms PalPeg.CloseoutPrepInputs3.prepInputs3_of_found
#print axioms PalPeg.CloseoutPrepInputs3.mismatchExitG_of_route
#print axioms PalPeg.CloseoutPrepInputs3.prepInputs3_of_found_or_later
