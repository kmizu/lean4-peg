import PalPeg.GalilRunInv
import PalPeg.GalilScaffoldTopLifeRestart
import PalPeg.GalilScaffoldTopRoundBreak

/-!
# The landing state of a found cycle, named

`foundCycle_step` (`PalPeg/GalilMainLoopMInv.lean`) hides its landing state
behind two existentials, and the `Restarted` conjunct the `FoundCycle` bundle
carries names neither its radius nor — through the step lemma — anything that
would let a caller identify it.  That is exactly gaps 4–5 of
`FoundResidual` (`PalPeg/GalilRunInv.lean`): the residual facts
(`mode = .scan`, `replaying = false`, `clock = delay`, the stage budget) are
facts *about a particular control and VM record*, so they cannot be discharged
while those records are anonymous.

This file re-runs the same cycle with the landing data exposed:

* `foundLandingControl` / `foundLandingVM` — the two records the found cycle
  actually lands in (`cycle_found_stepsAll`, `cycle_found_minv`,
  `life_restarted` all end in these);
* `foundCycle_step'` — the same hypotheses as `foundCycle_step`, with the
  landing records named, the three controller fields discharged, and the
  carried `Restarted` turned into a statement whose radius is pinned by any
  `RadiusRep` of the landing radius (`restarted_radiusRep`).  The radius
  `rounds_break` / `life_restarted` actually produce is
  `foundRestartRadius org.radius h m n`, and `radiusRep_at_break` below is the
  `RadiusRep` that pins it;
* `stageEntry_after_found` — `StageEntry` at that radius and at the lower
  bound `w3'.machine.control.last` installed by `restartVM`, via
  `foundCycleStage_final'`, with the `CompareRounds` / `OnlyMatchedRun` inputs
  lifted from the controller-level rounds and final segment (`rounds_lift`,
  `scanSeg_only`).

The pieces that are *not* derivable from the `FoundCycle` bundle are isolated
as named hypotheses; they are listed in the module docstring of each theorem.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-! ## The two landing records -/

/-- The controller record a found cycle lands in. -/
def foundLandingControl (c3 : Control) (delay : ℕ) (o3 : Bool) : Control :=
  {c3 with clock := delay, output := o3, replaying := false}

/-- The VM record a found cycle lands in: the state after the breaking
comparison, with the chain dropped, the new lower bound installed and the
search and DP restarted. -/
def foundLandingVM (e : GalilVM) (w3' : GalilScaffoldChainWatch.State) (entry : ℕ) : GalilVM :=
  {e with chain := .idle, lower := w3'.machine.control.last, search := GalilScaffoldSearchFinish.begin w3'.machine.control.last e.radius, dp := GalilScaffoldControl.reset entry e.dp}

theorem foundLandingControl_mode (c3 : Control) (delay : ℕ) (o3 : Bool) :
    (foundLandingControl c3 delay o3).mode = c3.mode := rfl

theorem foundLandingControl_replaying (c3 : Control) (delay : ℕ) (o3 : Bool) :
    (foundLandingControl c3 delay o3).replaying = false := rfl

theorem foundLandingControl_clock (c3 : Control) (delay : ℕ) (o3 : Bool) :
    (foundLandingControl c3 delay o3).clock = delay := rfl

theorem foundLandingVM_radius (e : GalilVM) (w3' : GalilScaffoldChainWatch.State) (entry : ℕ) :
    (foundLandingVM e w3' entry).radius = e.radius := rfl

/-- A `RadiusRep` of the state's radius pins the radius parameter of any
`Restarted` derivation at that state. -/
theorem restarted_radiusRep {raw : List (Fin 2)} {s : GalilVM} {Rad R : ℕ} {last : Counter}
    (h : Restarted raw s Rad last) (hRR : RadiusRep s.radius R) : Restarted raw s R last := by
  have hRR' : RadiusRep s.radius Rad := h.2.2.2.2.1
  have : (Rad : ℤ) = (R : ℤ) := by rw [← hRR'.2, hRR.2]
  have hRad : Rad = R := by exact_mod_cast this
  exact hRad ▸ h

#print axioms foundLandingControl_mode
#print axioms foundLandingControl_replaying
#print axioms foundLandingControl_clock
#print axioms foundLandingVM_radius
#print axioms restarted_radiusRep

/-! ## (Gap 4) The found cycle with its landing state named -/

/-- **`foundCycle_step'`.**  The same statement as `foundCycle_step`, with the
landing state exposed: the landing control is `foundLandingControl c3 delay o3`
for the `c3`/`o3` of the bundle — so `mode = .scan` (from the bundle's `hm3`),
`replaying = false` and `clock = delay` are available at the landing — and the
landing VM is `foundLandingVM (afterCompare s3 vs3 vq3) w3' entry`, the restart
record of `cycle_found_minv`'s conclusion.

The `Restarted` conjunct is exported in the pinned form: its lower bound is
`w3'.machine.control.last`, and its radius is whatever any `RadiusRep` of the
landing radius says.  `radiusRep_at_break` supplies the `RadiusRep` whose value
is `foundRestartRadius org.radius h m n` — the radius `life_restarted` /
`rounds_break` produce — so the two together name the radius. -/
theorem foundCycle_step' (P : Shared) (qq : ℕ) (first : Fin 9) (delay : ℕ) (raw : List (Fin 2))
    (c0 : Control) (r : GalilVM) (hC : FoundCycle P qq first delay raw c0 r)
    (Rad : ℕ) (last : Counter) (hR : Restarted raw r Rad last) (hM0 : MInv raw c0 r) :
    ∃ (c3 : Control) (o3 : Bool) (e : GalilVM) (w3' : GalilScaffoldChainWatch.State) (entry : ℕ)
      (org : ReadOrigin raw) (h m n : ℕ),
      (∃ k, StepsAll (galilFrameS P qq first) delay (SoundScanNR raw) k ⟨c0, r⟩
          ⟨foundLandingControl c3 delay o3, foundLandingVM e w3' entry⟩) ∧
      MInv raw (foundLandingControl c3 delay o3) (foundLandingVM e w3' entry) ∧
      (foundLandingControl c3 delay o3).mode = Mode.scan ∧
      (foundLandingControl c3 delay o3).replaying = false ∧
      (foundLandingControl c3 delay o3).clock = delay ∧
      org.interior.length + 1 = h ∧
      (∀ R : ℕ, RadiusRep (foundLandingVM e w3' entry).radius R →
        Restarted raw (foundLandingVM e w3' entry) R w3'.machine.control.last) ∧
      (RadiusRep (foundLandingVM e w3' entry).radius (foundRestartRadius org.radius h m n) →
        Restarted raw (foundLandingVM e w3' entry) (foundRestartRadius org.radius h m n)
          w3'.machine.control.last) ∧
      ∃ Rad' : ℕ, Restarted raw (foundLandingVM e w3' entry) Rad' w3'.machine.control.last := by
  obtain ⟨a, ls, rs, q, gap, es0, cF, sF, vq, ch, oF, es, c2, s2, cM, sM, h, w, vs, vq', s2',
    t', v, cycle, o, org, lower, span, m, c', s', n, c3, s3, w3, vs3, vq3, o3, cen3, r3, w3', entry,
    hP, hP', hex, hraw, hout0, hseg0, hmF, hrF, hcF, havF, hidle, hCen, hq, hfound, hmt, hch, hchne,
    hoF, hprepSeg, hseg, hm1, hr1, hc1, hs1, hz, hav, hcmp, hmis, hq', hg, hb, hs2', hi2, hchain,
    ho, hint, he, hoc, hdp, hpc, hposout, hlow, hrounds, hseg3, hm3, hr3, hc3, hs3, hav3, hcmp3,
    hmt3, hq3, ho3, hinv3, hbroken, hmargin, hlast, hlag, hrestart, Rad', hRnext⟩ := hC
  obtain ⟨k, hk⟩ := cycle_found_stepsAll raw P hP hP' qq first delay hR hout0 hseg0 hmF hrF hcF havF
      hidle vq hq hfound hmt ch hch hchne oF hoF hprepSeg hseg h hm1 hr1 hc1 w hs1 hz hav vs vq'
      hcmp hmis hq' hg s2' hb hs2' hi2 hchain o ho org hint he hrounds hseg3 hm3 hr3 hc3 w3 hs3 hav3
      vs3 vq3 hcmp3 hmt3 hq3 o3 ho3 hinv3 w3' hbroken hmargin hlast hlag entry hrestart
  refine ⟨c3, o3, afterCompare s3 vs3 vq3, w3', entry, org, h, m, n, ⟨k, hk⟩,
    cycle_found_minv raw P hex qq first delay a ls rs q gap hraw hR hM0 hseg0 hmF hrF hcF havF
      hidle hCen vq hq hfound hmt ch hch hchne oF hoF hprepSeg hseg h hm1 hr1 hc1 w hs1 hz hav vs
      vq' hcmp hmis hq' hg s2' hb hs2' hi2 hchain o ho org hint he hoc hdp hpc hposout hlow hrounds
      hseg3 hm3 hr3 hc3 w3 hs3 hav3 vs3 vq3 hcmp3 hmt3 hq3 o3 ho3 w3' hbroken entry,
    hm3, rfl, rfl, hint, fun R hRR => restarted_radiusRep hRnext hRR,
    fun hRR => restarted_radiusRep hRnext hRR, Rad', hRnext⟩

#print axioms foundCycle_step'

/-! ## The `RadiusRep` that pins the landing radius -/

/-- **`radiusRep_at_break`.**  `rounds_break`, specialised to the landing state
of a found cycle: the landing radius represents
`foundRestartRadius org.radius h m n`.

Named hypotheses (not carried by the `FoundCycle` bundle):
`hend3` — the final segment ends at the last continuation cell
(`singlePositive s3.cycle = true`), and `hcenterS` — the centre after the
rounds still reads a symbol (`read s'.center ≠ none`). -/
theorem radiusRep_at_break (P : Shared) (qq : ℕ) (first : Fin 9) (delay h : ℕ)
    {raw : List (Fin 2)} (org : ReadOrigin raw) (hint : org.interior.length + 1 = h)
    {s2' : GalilVM} {t' : ShiftState} {v : GalilScaffoldChainWatch.State} {cycle : Counter}
    (hpo : (shiftLens.set s2' ⟨t', .watch v, cycle⟩).periodOnly = true)
    (hzv : zero v.lag = true)
    (he : Entry raw org (toOnly (shiftLens.set s2' ⟨t', .watch v, cycle⟩) v))
    {m : ℕ} {c1 c' : Control} {o : Bool} {s' : GalilVM}
    (hrounds : Rounds P qq first delay h m {c1 with mode := .scan, clock := delay, output := o}
      (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c' s')
    {n : ℕ} {c3 : Control} {s3 : GalilVM} (hseg3 : ScanSeg P qq first delay n c' s' c3 s3)
    (hm3 : c3.mode = .scan) (hr3 : c3.replaying = false) (hc3 : c3.clock = 1)
    (w3 : GalilScaffoldChainWatch.State) (hs3 : s3.chain = .watch w3) (hav3 : canRight s3.right)
    (vs3 : ScanVM) (vq3 : SearchVM)
    (hcmp3 : (galilFrame P qq first).compare s3 (scanLens.set s3 vs3))
    (hmt3 : (galilFrame P qq first).matched (scanLens.set s3 vs3))
    (hq3 : searchEffect P true s3 vq3)
    (w3' : GalilScaffoldChainWatch.State) (hbr3 : vs3.chain = .broken w3')
    (o3 : Bool) (ho3 : refresh (galilFrame P qq first) (afterCompare s3 vs3 vq3) c3.output o3)
    (entry : ℕ)
    (hend3 : singlePositive s3.cycle = true) (hcenterS : read s'.center ≠ none) :
    RadiusRep (foundLandingVM (afterCompare s3 vs3 vq3) w3' entry).radius
      (foundRestartRadius org.radius h m n) := by
  obtain ⟨-, -, -, hrest⟩ :=
    rounds_break P qq first delay h hrounds v hpo rfl hzv hseg3 hm3 hr3 hc3 w3 hs3 hav3 vs3 vq3
      hcmp3 hmt3 hq3 hend3 w3' hbr3 o3 ho3
  obtain ⟨-, -, -, -, -, -, hRR, -⟩ := hrest raw org hint he hcenterS
  show RadiusRep (afterCompare s3 vs3 vq3).radius _
  have hEq : org.radius + 1 + m * h - h + n + 1 = foundRestartRadius org.radius h m n := rfl
  exact hEq ▸ hRR

#print axioms radiusRep_at_break

/-! ## (Gap 5) The stage budget at the landing state -/

/-- **`stageEntry_after_found`.**  `StageEntry` at the found-cycle restart:
radius `foundRestartRadius org.radius h m n`, lower bound
`w3'.machine.control.last`.

The chain-side inputs of `foundCycleStage_final'` are lifted from the
controller-level data: `rounds_lift` turns the `m` controller rounds into
`CompareRounds h (toOnly … v) m (toOnly s' w')`, and `scanSeg_only` turns the
final segment into `OnlyMatchedRun (toOnly s' w') n (toOnly s3 w3)`.  The break
identity is `w3' = GalilScaffoldChainWatch.immediate w3` (`rounds_break`'s
second conjunct, via `chainTick_true_broken`), which makes
`w3'.machine.control` the `consume` of `w3.machine.control` on the symbol the
verifier reads.

Named hypotheses (not derivable from the `FoundCycle` bundle):
* `ha : Aligned org` — the read-origin alignment invariant; free at a fresh
  origin (`aligned_of_only`) and preserved by the rounds (`aligned_rounds`),
  but the bundle carries no origin history, so it is threaded in;
* `hbroken` — the break comparison really broke the watch;
* `hlow` — the chain's own lower bound `3 * h ≤ value last` (`watch_last_lower`
  at the break state). -/
theorem stageEntry_after_found (P : Shared) (qq : ℕ) (first : Fin 9) (delay h : ℕ)
    {raw : List (Fin 2)} (org : ReadOrigin raw) (hint : org.interior.length + 1 = h)
    {s2' : GalilVM} {t' : ShiftState} {v : GalilScaffoldChainWatch.State} {cycle : Counter}
    (hpo : (shiftLens.set s2' ⟨t', .watch v, cycle⟩).periodOnly = true)
    (hzv : zero v.lag = true)
    (he : Entry raw org (toOnly (shiftLens.set s2' ⟨t', .watch v, cycle⟩) v))
    {m : ℕ} {c1 c' : Control} {o : Bool} {s' : GalilVM}
    (hrounds : Rounds P qq first delay h m {c1 with mode := .scan, clock := delay, output := o}
      (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c' s')
    {n : ℕ} {c3 : Control} {s3 : GalilVM} (hseg3 : ScanSeg P qq first delay n c' s' c3 s3)
    (w3 : GalilScaffoldChainWatch.State) (hs3 : s3.chain = .watch w3)
    (w3' : GalilScaffoldChainWatch.State) (hw3' : w3' = GalilScaffoldChainWatch.immediate w3)
    (ha : PalPeg.GalilRadiusConsumed.Aligned org)
    (hbroken : w3'.machine.control.broken = true)
    (hlow : (3 * h : ℤ) ≤ value w3'.machine.control.last) :
    StageEntry (foundRestartRadius org.radius h m n) w3'.machine.control.last := by
  -- the rounds, lifted to the projection
  obtain ⟨-, w', hw', hz', hp', hcr⟩ := rounds_lift P qq first delay h hrounds v hpo rfl hzv
  -- the final segment, lifted to the projection
  obtain ⟨w'', hw'', -, -, hrun⟩ := scanSeg_only P qq first delay hseg3 w' hp' hw' hz'
  have hww : w'' = w3 := by rw [hs3] at hw''; injection hw'' with e; exact e.symm
  subst hww
  subst hw3'
  exact PalPeg.GalilRadiusConsumed.foundCycleStage_final' org hint he hcr hrun ha
    (seen := read (right w''.machine.verifier)) hbroken rfl hlow

#print axioms stageEntry_after_found

end PalPeg.GalilScaffoldChainInputSupply
