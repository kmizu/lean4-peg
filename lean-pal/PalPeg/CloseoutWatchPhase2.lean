import PalPeg.CloseoutWatchPhase
import PalPeg.CloseoutPrepInputs3
import PalPeg.GalilOracleLeaves2
import PalPeg.GalilBreakTerminal
import PalPeg.GalilCatchUpDistance
import PalPeg.GalilScaffoldTopLifeRestart

/-!
# Closing the watch phase: `LandingRestart`, and the two routes from a typed tail

`CloseoutWatchPhase` measured the gap between what the two found-route theorems
conclude (`InvLP` / `InvLP2`) and what the closeout's landing record needs, and
named three things: `RoundsRouteLP`, `BreakRouteLP`, `LandingRestart`.  This
file closes the first two *relative to a typed per-instance tail*, and closes
`LandingRestart` outright wherever the landing is already known to be a restart
state.

## Derived here

1. **`LandingRestart` is exactly `Inv.rest` + `Inv.stage`**
   (`landingRestart_of_inv`), and a *single* restart witness with its stage
   budget suffices, because `Restarted` pins both of its parameters
   (`GalilRunInv.restarted_unique`).  That is `landingRestart_of_restarted`,
   and `landingRestart_of_foundCycle` is its found-cycle instance: the restart
   radius `GalilRestartStage.foundRestartRadius org.radius h m n` and the lower
   bound `w3'.machine.control.last` that
   `GalilScaffoldTopLifeRestart.life_restarted` produces, with the budget from
   `GalilBreakTerminal.stageEntry_after_found_closed` /
   `GalilCatchUpDistance.stageEntry_after_found_of_rounds`
   (`landingRestart_of_break`).  So the sharpening from `InvLP` to `Inv` is
   *not* an extra proof obligation at the landing: it is already discharged by
   the main-loop restart theorems, for the landing they name.
2. **The routes reduce to their `InvLP`-only forms plus one reach statement.**
   `RoundsRouteLPraw` / `BreakRouteLPraw` are literally the conclusions of
   `GalilFoundLandingL.foundRouteMC_shift` /
   `GalilInvPlus2.foundRouteMC_noshift''` together with the right-head bound;
   `roundsRouteLP_of_raw` / `breakRouteLP_of_raw` lift them to
   `CloseoutWatchPhase.RoundsRouteLP` / `BreakRouteLP` given
   `LandingRestartReach`, the uniform form of `LandingRestart` (every `InvLP`
   landing reachable from the cycle entry is a restart state with its budget).
   By (1) this is the *only* residue of the sharpening, and it is a statement
   about landings, not about the route.
3. **The routes themselves, from a typed tail.**  `ShiftTailC` / `NoShiftTailC`
   package exactly the per-instance premises of the two route theorems that the
   closeout's entry data does not supply — the found tick (`hraw`, `hCen`, the
   search answer, the matched chain, `oF`), and, over the *given* preparation
   segment, the terminal mismatch, the shift, the rounds and the breaking match
   (resp. the `freshWatch` landing shape, `es.count true = 0` and the two
   `PalAt` facts).  `roundsRouteLPraw_of_tail` / `breakRouteLPraw_of_tail` then
   prove the raw routes outright.  Everything the entry data *does* supply is
   supplied here and appears in no tail: `hI` is `StageEntryC.invLPC` through
   `GalilOracleMC2.invLPC_invLP`, and `hlive` is
   `GalilOracleLeaves2.hlive_of_invLPC` at that same entry — neither is a
   hypothesis of the theorems below.
4. **The fallback sibling.**  `fallbackRouteG_of_raw` does for
   `CloseoutPrepInputs3.FallbackRouteG` what (2) does for the two found routes:
   an `InvLP` landing record plus `LandingRestartReach` is a `FallbackRouteG`,
   hence (`CloseoutPrepInputs3.mismatchExitG_of_route`) a
   `CloseoutPrepInputs2.MismatchExitG`.

## Open, NAMED with exact types

* `LandingRestartReach P q first raw c r` — see (2).  True of the real machine
  (every landing of a found or fallback cycle is produced by a `restart` tick),
  but the route theorems existentially quantify their landing and do not export
  it, so it cannot be read off their conclusions.
* `ShiftTailC` / `NoShiftTailC` — see (3).  These are per-instance data about
  one cycle, not facts about the entry state: `WatchSegE` from `cP sP` alone
  determines neither where the mismatch falls nor whether the shift guard
  passes.

The lag ledger of the preparation landing is the corrected one
(`CloseoutPrepInputs3.PrepInputsG3`: `value sP.radius + #true`); the `+1` of
`CloseoutPrepInputs2` is the increment the found comparison already paid.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchPhase2

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilTraceCost
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus3
open PalPeg.GalilFoundStage PalPeg.GalilFoundStageInv
open PalPeg.GalilInvPlus2 (CentreRep InvLP2 InvLPC invLP2_invLP invLPC_invLP2)
open PalPeg.GalilOracleMC2 (invLPC_invLP)
open PalPeg.CloseoutContracts
open PalPeg.CloseoutWatchPhase (LandingRestart)

/-! ## 1. `LandingRestart`, closed -/

/-- **Derived.**  `LandingRestart` is literally the pair of `Inv` fields that
`InvLP` lacks. -/
theorem landingRestart_of_inv {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    (h : Inv raw c s) : LandingRestart raw c s := ⟨h.rest, h.stage⟩

/-- **Derived.**  One restart witness together with *its* stage budget is
enough: `Restarted` pins both parameters, so the `∀`-form of the budget follows
from the single instance. -/
theorem landingRestart_of_restarted {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    {Rad : ℕ} {last : Counter} (hR : Restarted raw s Rad last) (hS : StageEntry Rad last) :
    LandingRestart raw c s := by
  refine ⟨⟨Rad, last, hR⟩, ?_⟩
  intro Rad' last' hR'
  obtain ⟨e1, e2⟩ := restarted_unique hR' hR
  rw [e1, e2]
  exact hS

/-- **Derived.**  The found cycle's landing.  `life_restarted` delivers the
restart witness at radius `foundRestartRadius org.radius h m n` and lower bound
`w3'.machine.control.last`; `GalilRestartStage.FoundCycleStage` is exactly the
budget for that pair. -/
theorem landingRestart_of_foundCycle {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    {orgRadius h m n : ℕ} {w3' : GalilScaffoldChainWatch.State}
    (hR : Restarted raw s (foundRestartRadius orgRadius h m n)
      w3'.machine.control.last)
    (hS : FoundCycleStage orgRadius h m n w3'.machine.control.last) :
    LandingRestart raw c s := landingRestart_of_restarted hR hS

/-- **Derived.**  The break-terminal instance: the budget comes from
`GalilBreakTerminal.stageEntry_after_found_closed`, so a found cycle that ends
at a *matched* breaking comparison needs nothing beyond its own restart
witness. -/
theorem landingRestart_of_break (P : Shared) (qq : ℕ) (first : Fin 9) (delay h : ℕ)
    {raw : List (Fin 2)} (org : ReadOrigin raw)
    (hint : org.interior.length + 1 = h)
    {s2' : GalilVM} {t' : ShiftState} {v : GalilScaffoldChainWatch.State} {cycle : Counter}
    (hpo : (shiftLens.set s2' ⟨t', .watch v, cycle⟩).periodOnly = true)
    (hzv : zero v.lag = true)
    (hee : Entry raw org (toOnly (shiftLens.set s2' ⟨t', .watch v, cycle⟩) v))
    {m : ℕ} {c1 c' : Control} {o : Bool} {s' : GalilVM}
    (hrounds : Rounds P qq first delay h m {c1 with mode := .scan, clock := delay, output := o}
      (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c' s')
    {n : ℕ} {c3 : Control} {s3 : GalilVM} (hseg3 : ScanSeg P qq first delay n c' s' c3 s3)
    (w3 : GalilScaffoldChainWatch.State) (hs3 : s3.chain = ChainVM.watch w3)
    (w3' : GalilScaffoldChainWatch.State) (hw3' : w3' = GalilScaffoldChainWatch.immediate w3)
    (ha : PalPeg.GalilRadiusConsumed.Aligned org)
    (hbroken : w3'.machine.control.broken = true)
    (hav3 : canRight s3.right) (vs3 : ScanVM)
    (hcmp3 : (galilFrame P qq first).compare s3 (scanLens.set s3 vs3))
    (hmt3 : (galilFrame P qq first).matched (scanLens.set s3 vs3))
    (hbr3 : vs3.chain = ChainVM.broken w3')
    {cT : Control} {sT : GalilVM}
    (hR : Restarted raw sT
      (foundRestartRadius org.radius h m n) w3'.machine.control.last) :
    LandingRestart raw cT sT :=
  landingRestart_of_foundCycle hR
    (PalPeg.GalilBreakTerminal.stageEntry_after_found_closed P qq first delay h org hint hpo hzv
      hee hrounds hseg3 w3 hs3 w3' hw3' ha hbroken hav3 vs3 hcmp3 hmt3 hbr3)

/-! ## 2. The reach form of the sharpening -/

/-- **NAMED (open).**  Every `InvLP` landing reachable from the cycle entry is a
restart state with its stage budget.  This is the whole residue of "sharpen
`InvLP` to `Inv`": by §1 it is `Inv.rest` + `Inv.stage`, and by
`landingRestart_of_restarted` a single restart witness discharges it. -/
def LandingRestartReach (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (c : Control) (r : GalilVM) : Prop :=
  ∀ (k : ℕ) (cT : Control) (sT : GalilVM),
    StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ →
    InvLP raw cT sT → LandingRestart raw cT sT

/-! ## 3. The two routes without the sharpening -/

/-- **The rounds route as `GalilFoundLandingL.foundRouteMC_shift` states it**,
plus the right-head bound `CloseoutFoundCompare` charges: `RoundsRouteLP` minus
its `LandingRestart` conjunct. -/
def RoundsRouteLPraw (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (hh : ℕ) (es : List Bool) (c2 : Control) (s2 : GalilVM),
    WatchSegE P q first 2048 es cP sP c2 s2 → es.length = 2*hh+2 →
    (∃ ww : GalilScaffoldChainWatch.State, s2.chain = ChainVM.watch ww) →
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧ InvLP raw cT sT ∧
      position r.center < position sT.center ∧ position sT.right ≤ 2 * m - 1

/-- **The break route as `GalilInvPlus2.foundRouteMC_noshift''` states it**, plus
the right-head bound: `BreakRouteLP` minus its `LandingRestart` conjunct. -/
def BreakRouteLPraw (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (hh : ℕ) (es : List Bool) (c2 : Control) (s2 : GalilVM),
    WatchSegE P q first 2048 es cP sP c2 s2 → es.length = 2*hh+2 →
    (∃ ww : GalilScaffoldChainWatch.State, s2.chain = ChainVM.watch ww) →
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧ InvLP2 raw cT sT ∧
      position sT.center = position r.center ∧ position r.right < position sT.right ∧
      position sT.right ≤ 2 * m - 1

/-- **Derived.**  The raw rounds route plus `LandingRestartReach` is
`CloseoutWatchPhase.RoundsRouteLP`. -/
theorem roundsRouteLP_of_raw {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c cP : Control} {r sP : GalilVM}
    (h : RoundsRouteLPraw P q first raw m c r cP sP)
    (hLR : LandingRestartReach P q first raw c r) :
    PalPeg.CloseoutWatchPhase.RoundsRouteLP P q first raw m c r cP sP := by
  intro hh es c2 s2 hseg hlen hw
  obtain ⟨cT, sT, k, L, hst, hcr, hLP, hprog, hpos⟩ := h hh es c2 s2 hseg hlen hw
  exact ⟨cT, sT, k, L, hst, hcr, hLP, hLR k cT sT hst hLP, hprog, hpos⟩

/-- **Derived.**  Likewise for the break route (`InvLP2` refines `InvLP`, so the
same reach statement serves). -/
theorem breakRouteLP_of_raw {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c cP : Control} {r sP : GalilVM}
    (h : BreakRouteLPraw P q first raw m c r cP sP)
    (hLR : LandingRestartReach P q first raw c r) :
    PalPeg.CloseoutWatchPhase.BreakRouteLP P q first raw m c r cP sP := by
  intro hh es c2 s2 hseg hlen hw
  obtain ⟨cT, sT, k, L, hst, hcr, hLP2, hc, hlt, hpos⟩ := h hh es c2 s2 hseg hlen hw
  exact ⟨cT, sT, k, L, hst, hcr, hLP2, hLR k cT sT hst (invLP2_invLP hLP2), hc, hlt, hpos⟩

/-! ## 4. The typed tails, and the raw routes proved from them -/

/-- **NAMED (open), per instance.**  The shift route's cycle data: the found
tick reaching `cP sP`, and, over the preparation segment the closeout hands in,
the terminal mismatch, the shift, the rounds and the breaking match.  `hI` and
`hlive` are *not* here: they come from the entry contract. -/
def ShiftTailC (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry qq : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c0 : Control) (r : GalilVM) (cP : Control) (sP : GalilVM) : Prop :=
  ∃ (a : Fin 2) (ls rs qw : List (Fin 2)) (gap : Bool) (es0 : List Bool) (cF : Control)
    (sF : GalilVM) (vq : SearchVM) (ch : ChainVM) (oF : Bool) (lower span : ℕ),
    raw = (a :: ls).reverse ++ rs ++ qw ∧
    WatchSegE (PofC centre place entry raw) qq first 2048 es0 c0 r cF sF ∧
    cF.mode = .scan ∧ cF.replaying = false ∧ cF.clock = 1 ∧ canRight sF.right ∧
    sF.chain = ChainVM.idle ∧
    sF.center = represent ⟨a :: ls, gap⟩ (rs.map some) qw ∧
    searchEffect (PofC centre place entry raw) true sF vq ∧ vq.search.mode = .found ∧
    read (left sF.left) = read (right sF.right) ∧
    ChainMatched (chainStart (vq.dp.config.tapes 11)
      ((PofC centre place entry raw).centre sF) ((PofC centre place entry raw).place sF)
      sF.center sF.radius) ch ∧
    ch ≠ ChainVM.idle ∧
    refresh (galilFrame (PofC centre place entry raw) qq first)
      (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)) cF.output oF ∧
    cP = {cF with clock := 2048, output := oF, replaying := false} ∧
    sP = afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) ∧
    GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (span+1)) lower 0
      (GalilScaffoldProgram.denote vq.dp.config) ∧
    (GalilScaffoldProgram.denote vq.dp.config).pc = 346 ∧
    (∀ (es : List Bool) (c2 : Control) (s2 : GalilVM),
      WatchSegE (PofC centre place entry raw) qq first 2048 es cP sP c2 s2 →
      (∃ wLive : GalilScaffoldChainWatch.State, s2.chain = ChainVM.watch wLive) →
      ∃ (c1 : Control) (s1 : GalilVM) (h : ℕ) (w : GalilScaffoldChainWatch.State)
        (vs : ScanVM) (vq' : SearchVM) (s2' : GalilVM) (t' : ShiftState)
        (v : GalilScaffoldChainWatch.State) (cycle : Counter) (o : Bool)
        (org : ReadOrigin raw) (mm : ℕ) (c' : Control) (s' : GalilVM)
        (n : ℕ) (c3 : Control) (s3 : GalilVM) (w3 : GalilScaffoldChainWatch.State)
        (vs3 : ScanVM) (vq3 : SearchVM) (o3 : Bool) (w3' : GalilScaffoldChainWatch.State),
        WatchSeg (PofC centre place entry raw) qq first 2048 c2 s2 c1 s1 ∧
        c1.mode = .scan ∧ c1.replaying = false ∧ c1.clock = 1 ∧
        s1.chain = ChainVM.watch w ∧ zero w.lag = true ∧ canRight s1.right ∧
        (galilFrame (PofC centre place entry raw) qq first).compare s1 (scanLens.set s1 vs) ∧
        ¬ (galilFrame (PofC centre place entry raw) qq first).matched (scanLens.set s1 vs) ∧
        searchEffect (PofC centre place entry raw) false s1 vq' ∧
        (PofC centre place entry raw).shiftGuard (afterMismatch s1 vs vq') ∧
        (PofC centre place entry raw).beginShift (afterMismatch s1 vs vq') s2' ∧
        beginShiftVM h w (afterMismatch s1 vs vq') s2' ∧ CopyIdle s2' ∧
        ChainShiftRun ⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩
          (GalilScaffoldChainWatch.immediate w) reset h t' v cycle ∧
        refresh (galilFrameS (PofC centre place entry raw) qq first)
          (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c1.output o ∧
        org.interior.length + 1 = h ∧
        Entry raw org (toOnly (shiftLens.set s2' ⟨t', .watch v, cycle⟩) v) ∧
        org.center = position sF.center ∧
        PalPeg.GalilRadiusConsumed.Aligned org ∧
        (GalilScaffoldProgram.denote vq.dp.config).pos 11 = h ∧
        (∀ δ, 0 < δ → δ ≤ lower → ¬ HasPeriod (Span raw org.center org.radius) (2*δ)) ∧
        Rounds (PofC centre place entry raw) qq first 2048 h mm
          {c1 with mode := .scan, clock := 2048, output := o}
          (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c' s' ∧
        ScanSeg (PofC centre place entry raw) qq first 2048 n c' s' c3 s3 ∧
        c3.mode = .scan ∧ c3.replaying = false ∧ c3.clock = 1 ∧
        s3.chain = ChainVM.watch w3 ∧ canRight s3.right ∧
        (galilFrame (PofC centre place entry raw) qq first).compare s3 (scanLens.set s3 vs3) ∧
        (galilFrame (PofC centre place entry raw) qq first).matched (scanLens.set s3 vs3) ∧
        searchEffect (PofC centre place entry raw) true s3 vq3 ∧
        refresh (galilFrame (PofC centre place entry raw) qq first)
          (afterCompare s3 vs3 vq3) c3.output o3 ∧
        (afterCompare s3 vs3 vq3).chain = ChainVM.broken w3' ∧
        negative w3'.margin = false ∧ positive w3'.machine.control.last = true ∧
        zero w3'.lag = true ∧
        position (afterCompare s3 vs3 vq3).right ≤ 2 * m - 1)

/-- **Derived.**  The raw rounds route, from the typed tail.  The entry data
supplies `hI` (`StageEntryC.invLPC` through `invLPC_invLP`) and `hlive`
(`GalilOracleLeaves2.hlive_of_invLPC`); everything else is the tail. -/
theorem roundsRouteLPraw_of_tail (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ)
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    {c0 cP : Control} {r sP : GalilVM}
    (hE : StageEntryC (PofC centre place entry raw) qq first raw c0 r)
    (htail : ShiftTailC centre place entry qq first raw m c0 r cP sP) :
    RoundsRouteLPraw (PofC centre place entry raw) qq first raw m c0 r cP sP := by
  classical
  obtain ⟨a, ls, rs, qw, gap, es0, cF, sF, vq, ch, oF, lower, span, hraw, hseg0, hmF, hrF, hcF,
    havF, hidle, hCen, hq, hfound, hmt, hch, hchne, hoF, hcPeq, hsPeq, hdp, hpc, htl⟩ := htail
  subst hcPeq
  subst hsPeq
  intro hh es c2 s2 hprepSeg hlen hw
  obtain ⟨c1, s1, h, w, vs, vq', s2', t', v, cycle, o, org, mm, c', s', n, c3, s3, w3, vs3, vq3,
    o3, w3', hseg, hm1, hr1, hc1, hs1, hz, hav, hcmp, hmis, hq', hg, hb, hs2', hi2, hchain, ho,
    hint, he, hoc, ha, hpos11, hlow, hrounds, hseg3, hm3, hr3, hc3, hs3, hav3, hcmp3, hmt3, hq3,
    ho3, hbroken, hmargin, hlast, hlag, hbound⟩ := htl es c2 s2 hprepSeg hw
  obtain ⟨cT, sT, k, L, hst, hcr, hLP, hprog, hright⟩ :=
    PalPeg.GalilFoundLandingL.foundRouteMC_shift centre place entry qq first raw hex
      (invLPC_invLP hE.invLPC)
      (PalPeg.GalilOracleLeaves2.hlive_of_invLPC centre place entry qq first hE.invLPC)
      a ls rs qw gap hraw hseg0 hmF hrF hcF havF hidle hCen vq hq hfound hmt ch hch hchne oF hoF
      hprepSeg hseg h hm1 hr1 hc1 w hs1 hz hav vs vq' hcmp hmis hq' hg s2' hb hs2' hi2 hchain o ho
      org hint he hoc ha hdp hpc hpos11 hlow hrounds hseg3 hm3 hr3 hc3 w3 hs3 hav3 vs3 vq3 hcmp3
      hmt3 hq3 o3 ho3 w3' hbroken hmargin hlast hlag
  refine ⟨cT, sT, k, L, hst, hcr, hLP, hprog, ?_⟩
  rw [hright]
  exact hbound

/-- **NAMED (open), per instance.**  The no-shift break route's cycle data.  The
preparation landing must have the `freshWatch` shape and credit no comparison
(`es.count true = 0`) — i.e. the delay-fit that `CloseoutPrepInputs3` removes —
so this tail is *strictly stronger* than `ShiftTailC` on the preparation side,
and that is exactly the gap `CloseoutPrepInputs2.NoCompareInPrepG` records. -/
def NoShiftTailC (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry qq : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c0 : Control) (r : GalilVM) (cP : Control) (sP : GalilVM) : Prop :=
  ∃ (es0 : List Bool) (cF : Control) (sF : GalilVM) (vq : SearchVM) (ch : ChainVM) (oF : Bool),
    WatchSegE (PofC centre place entry raw) qq first 2048 es0 c0 r cF sF ∧
    cF.mode = .scan ∧ cF.replaying = false ∧ cF.clock = 1 ∧ canRight sF.right ∧
    sF.chain = ChainVM.idle ∧
    searchEffect (PofC centre place entry raw) true sF vq ∧ vq.search.mode = .found ∧
    read (left sF.left) = read (right sF.right) ∧
    ChainMatched (chainStart (vq.dp.config.tapes 11)
      ((PofC centre place entry raw).centre sF) ((PofC centre place entry raw).place sF)
      sF.center sF.radius) ch ∧
    ch ≠ ChainVM.idle ∧
    refresh (galilFrame (PofC centre place entry raw) qq first)
      (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)) cF.output oF ∧
    cP = {cF with clock := 2048, output := oF, replaying := false} ∧
    sP = afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) ∧
    (∀ (es : List Bool) (c2 : Control) (s2 : GalilVM),
      WatchSegE (PofC centre place entry raw) qq first 2048 es cP sP c2 s2 →
      ∃ (cen : Fin 3) (ys : List (Fin 3)) (b : Fin 3) (c3 : Control) (s3 : GalilVM)
        (w3 : GalilScaffoldChainWatch.State) (vs3 : ScanVM) (vq3 : SearchVM) (o3 : Bool)
        (w3' : GalilScaffoldChainWatch.State),
        s2.chain = ChainVM.watch
          (PalPeg.GalilNoShiftStage.freshWatch sF.center cen ys b sF.radius) ∧
        es.count true = 0 ∧
        Manacher.PalAt (encoded raw) (position r.center - (ys.length + 1)) (ys.length + 1) ∧
        Manacher.PalAt (encoded raw) (position r.center - 2 * (ys.length + 1)) (2 * (ys.length + 1)) ∧
        WatchSeg (PofC centre place entry raw) qq first 2048 c2 s2 c3 s3 ∧
        c3.mode = .scan ∧ c3.replaying = false ∧ c3.clock = 1 ∧
        s3.chain = ChainVM.watch w3 ∧ canRight s3.right ∧
        (galilFrame (PofC centre place entry raw) qq first).compare s3 (scanLens.set s3 vs3) ∧
        (galilFrame (PofC centre place entry raw) qq first).matched (scanLens.set s3 vs3) ∧
        searchEffect (PofC centre place entry raw) true s3 vq3 ∧
        refresh (galilFrame (PofC centre place entry raw) qq first)
          (afterCompare s3 vs3 vq3) c3.output o3 ∧
        (afterCompare s3 vs3 vq3).chain = ChainVM.broken w3' ∧
        negative w3'.margin = false ∧
        position (afterCompare s3 vs3 vq3).right ≤ 2 * m - 1)

/-- **Derived.**  The raw break route, from the typed tail, through
`GalilInvPlus2.foundRouteMC_noshift''` (whose landing is already `InvLP2`). -/
theorem breakRouteLPraw_of_tail (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ)
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    {c0 cP : Control} {r sP : GalilVM}
    (hE : StageEntryC (PofC centre place entry raw) qq first raw c0 r)
    (htail : NoShiftTailC centre place entry qq first raw m c0 r cP sP) :
    BreakRouteLPraw (PofC centre place entry raw) qq first raw m c0 r cP sP := by
  classical
  obtain ⟨es0, cF, sF, vq, ch, oF, hseg0, hmF, hrF, hcF, havF, hidle, hq, hfound, hmt, hch,
    hchne, hoF, hcPeq, hsPeq, htl⟩ := htail
  subst hcPeq
  subst hsPeq
  intro hh es c2 s2 hprepSeg hlen hw
  obtain ⟨cen, ys, b, c3, s3, w3, vs3, vq3, o3, w3', hwatch2, hes0, hpal1, hpal2, hseg, hm3, hr3,
    hc3, hs3, hav3, hcmp3, hmt3, hq3, ho3, hbroken, hmargin, hbound⟩ := htl es c2 s2 hprepSeg
  obtain ⟨cT, sT, k, L, hst, hcr, hLP2, hc, hlt, hright⟩ :=
    PalPeg.GalilInvPlus2.foundRouteMC_noshift'' centre place entry qq first raw hex hE.invLPC
      (PalPeg.GalilOracleLeaves2.hlive_of_invLPC centre place entry qq first hE.invLPC)
      hseg0 hmF hrF hcF havF hidle vq hq hfound hmt ch hch hchne oF hoF hprepSeg cen ys b hwatch2
      hes0 hpal1 hpal2 hseg hm3 hr3 hc3 w3 hs3 hav3 vs3 vq3 hcmp3 hmt3 hq3 o3 ho3 w3' hbroken
      hmargin
  refine ⟨cT, sT, k, L, hst, hcr, hLP2, hc, hlt, ?_⟩
  rw [hright]
  exact hbound

/-! ## 5. The fallback sibling -/

/-- The `InvLP` form of a fallback landing record: `FallbackRouteG` with `Inv`
weakened to `InvLP`, which is what the route theorems of the prep-time mismatch
actually produce. -/
def FallbackRouteLP (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es : List Bool) (c1 : Control) (s1 : GalilVM),
    WatchSegE P q first 2048 es cP sP c1 s1 → c1.mode = .scan → c1.replaying = false →
    c1.clock = 1 → canRight s1.right →
    read (left s1.left) ≠ read (right s1.right) →
    GalilPrepMatch.PrepChain s1.chain →
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧ InvLP raw cT sT ∧
      position r.center < position sT.center ∧ position sT.right ≤ 2 * m - 1

/-- **Derived.**  `CloseoutPrepInputs3.FallbackRouteG` from the `InvLP` record
and the same reach statement: the mismatch exit needs no more sharpening than
the two found routes do. -/
theorem fallbackRouteG_of_raw {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c cP : Control} {r sP : GalilVM}
    (h : FallbackRouteLP P q first raw m c r cP sP)
    (hLR : LandingRestartReach P q first raw c r) :
    PalPeg.CloseoutPrepInputs3.FallbackRouteG P q first raw m c r cP sP := by
  intro es c1 s1 hseg hm hr hc hav hne hpc
  obtain ⟨cT, sT, k, L, hst, hcr, hLP, hprog, hpos⟩ := h es c1 s1 hseg hm hr hc hav hne hpc
  have hL := hLR k cT sT hst hLP
  exact ⟨cT, sT, k, L, hst, hcr,
    PalPeg.CloseoutWatchPhase.inv_of_invLP hLP hL,
    PalPeg.CloseoutWatchPhase.spanRep_of_invLP hLP, hprog, hpos⟩

/-- **Derived.**  …hence the named mismatch exit of the general preparation. -/
theorem mismatchExitG_of_raw {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c cP : Control} {r sP : GalilVM}
    (h : FallbackRouteLP P q first raw m c r cP sP)
    (hLR : LandingRestartReach P q first raw c r) :
    PalPeg.CloseoutPrepInputs2.MismatchExitG P q first raw m c r cP sP :=
  PalPeg.CloseoutPrepInputs3.mismatchExitG_of_route (fallbackRouteG_of_raw h hLR)

end PalPeg.CloseoutWatchPhase2

#print axioms PalPeg.CloseoutWatchPhase2.landingRestart_of_inv
#print axioms PalPeg.CloseoutWatchPhase2.landingRestart_of_restarted
#print axioms PalPeg.CloseoutWatchPhase2.landingRestart_of_foundCycle
#print axioms PalPeg.CloseoutWatchPhase2.landingRestart_of_break
#print axioms PalPeg.CloseoutWatchPhase2.roundsRouteLP_of_raw
#print axioms PalPeg.CloseoutWatchPhase2.breakRouteLP_of_raw
#print axioms PalPeg.CloseoutWatchPhase2.roundsRouteLPraw_of_tail
#print axioms PalPeg.CloseoutWatchPhase2.breakRouteLPraw_of_tail
#print axioms PalPeg.CloseoutWatchPhase2.fallbackRouteG_of_raw
#print axioms PalPeg.CloseoutWatchPhase2.mismatchExitG_of_raw
