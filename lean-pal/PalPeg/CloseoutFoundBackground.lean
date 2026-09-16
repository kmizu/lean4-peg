import PalPeg.CloseoutContracts

/-!
# The background found leaf of the closeout

A found tick that is **not** a matched comparison (`SegEnd.foundBackground`):
the search reports `.found` on the background event `false`, the chain is still
idle, and the route of `GalilInvPlus3.cycleOracleMC3_of_pieces`' leaf `hfoundBg`
therefore restarts at the *cycle entry* `⟨c, r⟩` rather than at the segment exit.

This file produces the shared landing `CloseoutContracts.FoundExit` for that
leaf.  Proved here, unconditionally:

* `stage_bg` — the stage datum travels from the cycle entry to the found tick;
* `bg_found_data` — the radius/candidate data of the background found answer,
  i.e. `GalilFoundStageInv.found_radius_bg` entered through `StageEntryC`;
* `foundExit_of_bgLanding` — the landing/break dichotomy, in the `FoundCost`
  form the background route produces at `c0 s0 = c r`, is a `FoundExit`.

Open, as NAMED hypotheses of the assembling theorem `foundExit_bg`:
`BgPrep` (the preparation segment at a background found tick — the analogue of
`GalilPrepConstruct.prep_segment_construct_of_found`, whose `SafeQuanta` at a
background tick is not yet extracted) and the continuation `H_after` from that
preparation landing to the dichotomy (the analogue of the rounds/break case
split `GalilFoundLandingL.foundRouteMC_shift` /
`GalilNoShiftDischarge.foundRouteMC_noshift_d`).

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutFoundBackground

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilTraceCost
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleM PalPeg.GalilOracleMC PalPeg.GalilOracleMC2
open PalPeg.GalilInvPlus3
open PalPeg.GalilFoundStage PalPeg.GalilFoundStageInv
open PalPeg.CloseoutContracts

/-! ## 1. The stage datum at the background found tick -/

/-- The entry's `ReplayStage` extended through the cycle's own segment. -/
theorem stage_bg (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) {c c' : Control} {r t : GalilVM}
    (hE : StageEntryC (PofC centre place entry raw) q first raw c r)
    (hsW : SegReachedW centre place entry q first raw c r c' t) :
    ReplayStage raw (PofC centre place entry raw) q first c' t := by
  obtain ⟨-, es, hw⟩ := id hsW
  exact replayStage_trans hE.stage hw

/-! ## 2. The radius and the candidate of the background found answer -/

/-- **`found_radius_bg` entered through `StageEntryC`.**  The restart state and
its stage budget come from the entry's stage datum, the chain-idleness of the
found tick from `SegReached.idle`, and the centre of the restart is decomposed
by `represents_decompose`. -/
theorem bg_found_data (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (hP : Decodes (PofC centre place entry raw))
    {c c' : Control} {r t : GalilVM}
    (hE : StageEntryC (PofC centre place entry raw) q first raw c r)
    (hsW : SegReachedW centre place entry q first raw c r c' t)
    {vq : SearchVM} (hq : searchEffect (PofC centre place entry raw) false t vq)
    (hfound : vq.search.mode = .found) :
    ∃ (a : Fin 2) (ls rs qw : List (Fin 2)) (gap : Bool) (k h span : ℕ),
      GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (span+1)) k 0
        (GalilScaffoldProgram.denote vq.dp.config) ∧
      (GalilScaffoldProgram.denote vq.dp.config).pc = 346 ∧
      (GalilScaffoldProgram.denote vq.dp.config).pos 11 = h ∧
      GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (span+1)) k h ∧
      1 ≤ h ∧ value t.radius ≤ 2 * (h : ℤ) := by
  obtain ⟨r0, Rad, last, es0, c0, hRst, hSt, hcl, hseg⟩ := stage_bg centre place entry q first raw hE hsW
  obtain ⟨al, ls, rs, qw, hdec, -⟩ := represents_decompose r0.center raw hRst.2.1 hRst.2.2.1
  obtain ⟨k, h, span, hres, hpc, hpos, hcand, h1, hrad⟩ :=
    found_radius_bg (PofC centre place entry raw) q first hP al ls rs qw r0.center.gap
      hRst hdec hcl hSt hseg hsW.1.idle vq hq hfound
  exact ⟨al, ls, rs, qw, r0.center.gap, k, h, span, hres, hpc, hpos, hcand, h1, hrad⟩

/-! ## 3. The landing dichotomy of the background route -/

/-- **The two exits of the background found route**, stated at `c0 s0 = c r`
(the background route restarts at the cycle entry).  The first disjunct is the
`shift` / `noShift` landing of `GalilInvPlus3.FoundRouteMC3` — `FoundCost` at
the entry, the residual landing data and strict progress of the centre — and
the second is its `broke` landing. -/
def BgLanding (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) : Prop :=
  (∃ (cT : Control) (sT : GalilVM),
      FoundCost P q first raw c r cT sT ∧ MInv raw cT sT ∧
      (∃ (Rad : ℕ) (last : Counter), Restarted raw sT Rad last) ∧
      FoundResidual raw cT sT ∧ SpanRep sT ∧
      position r.center < position sT.center ∧ position sT.right ≤ 2 * m - 1) ∨
  (∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧ InvLP2 raw cT sT ∧ CentreRep raw sT ∧
      ReplayStage raw P q first cT sT ∧
      position sT.center = position r.center ∧ position r.right < position sT.right ∧
      position sT.right ≤ 2 * m - 1)

/-- **The dichotomy is a `FoundExit`.**  The entry clock is `2048`
(`invL_entry`), so the `FoundCost` may be spent with no pending ticks and the
landing branch becomes `FoundExit.landed` on the very same run. -/
theorem foundExit_of_bgLanding {centre : GalilVM → Fin 3}
    {place : GalilVM → GalilScaffoldPlace.Place} {entry q : ℕ} {first : Fin 9}
    {raw : List (Fin 2)} {m : ℕ} {c : Control} {r : GalilVM}
    (hE : StageEntryC (PofC centre place entry raw) q first raw c r)
    (h : BgLanding (PofC centre place entry raw) q first raw m c r) :
    FoundExit (PofC centre place entry raw) q first raw m c r := by
  obtain ⟨-, hc0, -⟩ := invL_entry (invLPC_invL hE.invLPC)
  rcases h with ⟨cT, sT, hcost, hM, hR, hres, hSpan, hprog, hpos⟩ |
      ⟨cT, sT, k, L, hst, hcr, hIT, hcenT, hstage, hc, hlt, hpos⟩
  · obtain ⟨k, L, hst, hcr⟩ := hcost 0 (by omega)
    exact .landed cT sT k L hst (by simpa using hcr) hM hR hres hSpan hprog hpos
  · exact .broke cT sT k L hst hcr hIT hcenT hstage hc hlt hpos

/-! ## 4. The leaf, assembled -/

/-- **NAMED hypothesis: the preparation segment at a background found tick.**
The analogue of `GalilPrepConstruct.prep_segment_construct_of_found` for the
event `false`: from the found tick the chain is started and the walker copies
the candidate semiperiod, landing in a watching state that has not moved the
heads.  Open: the `SafeQuanta` of a *background* found quantum is not extracted
yet. -/
def BgPrep (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (c' : Control) (t : GalilVM) : Prop :=
  ∃ (h k : ℕ) (c2 : Control) (s2 : GalilVM) (w : GalilScaffoldChainWatch.State),
    StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c', t⟩ ⟨c2, s2⟩ ∧
    s2.chain = ChainVM.watch w ∧ c2.mode = Mode.scan ∧ c2.replaying = false ∧
    s2.center = t.center ∧ s2.right = t.right ∧ 2 * h + 2 < 2048

/-- **The background found leaf.**  Entry `StageEntryC`, the cycle's segment,
the background found answer and the position bound of the found tick; the
radius/candidate data is derived here (`bg_found_data`), and the two NAMED
hypotheses are the preparation segment and the continuation from its landing to
the dichotomy (rounds with a shift, or no shift, or a break — the background
analogue of `foundRouteMC_shift` / `foundRouteMC_noshift_d`). -/
theorem foundExit_bg (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ raw.length)
    (hP : Decodes (PofC centre place entry raw))
    {c c' : Control} {r t : GalilVM}
    (hE : StageEntryC (PofC centre place entry raw) q first raw c r)
    (hsW : SegReachedW centre place entry q first raw c r c' t)
    (hclk : 1 ≤ c'.clock)
    (hq : ∃ vq, searchEffect (PofC centre place entry raw) false t vq ∧
      vq.search.mode = .found)
    (hpos : position t.right ≤ 2 * m - 2)
    -- NAMED: the preparation segment at the background found tick
    (H_prep : BgPrep (PofC centre place entry raw) q first raw c' t)
    -- NAMED: the continuation from the preparation landing to the dichotomy
    (H_after : ∀ (h k : ℕ) (c2 : Control) (s2 : GalilVM) (w : GalilScaffoldChainWatch.State),
      StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundScanNR raw) k
        ⟨c', t⟩ ⟨c2, s2⟩ →
      s2.chain = ChainVM.watch w → c2.mode = Mode.scan → c2.replaying = false →
      s2.center = t.center → s2.right = t.right → 2 * h + 2 < 2048 →
      ∀ (a : Fin 2) (ls rs qw : List (Fin 2)) (gap : Bool) (kk hh span : ℕ),
        GalilDpCorrect.Candidate
          ((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (span+1)) kk hh →
        1 ≤ hh → value t.radius ≤ 2 * (hh : ℤ) →
      BgLanding (PofC centre place entry raw) q first raw m c r) :
    FoundExit (PofC centre place entry raw) q first raw m c r := by
  obtain ⟨vq, hqe, hfound⟩ := hq
  obtain ⟨a, ls, rs, qw, gap, kk, hh, span, hres, hpc, hpos11, hcand, h1, hrad⟩ :=
    bg_found_data centre place entry q first raw hP hE hsW hqe hfound
  obtain ⟨h, k, c2, s2, w, hst, hchain, hm2, hr2, hcen2, hrt2, hfit⟩ := H_prep
  exact foundExit_of_bgLanding hE
    (H_after h k c2 s2 w hst hchain hm2 hr2 hcen2 hrt2 hfit a ls rs qw gap kk hh span hcand h1 hrad)

end PalPeg.CloseoutFoundBackground

#print axioms PalPeg.CloseoutFoundBackground.stage_bg
#print axioms PalPeg.CloseoutFoundBackground.bg_found_data
#print axioms PalPeg.CloseoutFoundBackground.foundExit_of_bgLanding
#print axioms PalPeg.CloseoutFoundBackground.foundExit_bg
