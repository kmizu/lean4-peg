import PalPeg.CloseoutPackRun7

/-!
# `CloseoutPackRun8`: `lpackO_tick`, and how far `MInv`-freedom actually reaches

`CloseoutPackRun7` deleted the centre invariant from the left-head pack
(`LPackO` = `CloseoutLPack5.LPackG` minus `minvG`) and showed that the whole
trail bridge re-runs over it, ending in `h_trailI_of_O`.  It left two named
pieces open.  This file settles the first outright and maps the second.

## §1–§2 `lpackO_tick`

`CloseoutLPack5.lpackG_tick` consumes `LPackG` and cannot be reused, so the
23-constructor `Tick` induction is re-run here over `LPackO` with the `minv`
corners deleted.  The re-run is purely mechanical, exactly as `CloseoutPackRun7`
predicted: no branch needed a machine fact that was not already available, and
two leaves of `CloseoutLPack5.LTickLeavesG` **disappear**:

* `shiftDoneMinv` — the corner the `MInvG` re-cut *added* at the `shift → scan`
  exit (it was to be `GalilLiveCentreShift.leftmost_shift` at
  `CloseoutPackRun3.Extra.cand`).  `shift_done` moves no head, so with `minv`
  gone the branch is `lrep` transport plus `shiftDoneScan`.
* the `scan_match` centre transport (`minv_match` / `minv_matchR`), which was
  the only branch that still had to *prove* something about `MInv` rather than
  dispatch it by `Mode.noConfusion`.

So `LTickLeavesO` has **eight** fields against `LTickLeavesG`'s nine, and one of
the nine (`replayPackG`) gets weaker, since its landing pack is now `LPackO`.

## §3 `BigResid5O`: five contracts

`lticksO_of_big5O` and `bigPack2O_tick` re-run `CloseoutPackRun5.§4–5` over the
`MInv`-free payload.  The contract list is `CloseoutPackRun5.BigResid5G` minus
`rShiftDoneMinv` and with the `MInv` half of `rInitPackG` / `rReplayPackG`
dropped, i.e. the six `rInitPackO`, `rScanInvR`, `rShiftDoneScan`,
`rChoosePackL`, `rReplayPackO`, `rShiftNext` — of which only five are pack
corners, `rShiftNext` being the shift-entry contract.  `big5O_of_big5G` relates the
two lists, but only conditionally: the contracts' *hypothesis* weakens along
with their conclusion, so the implication needs an explicit upgrade `hup` that
is not provable.  `bigPack2O_of_bigPack2` is the true direction.

`canR_of_bigPack2` is re-derived inline (`canR_of_partsO`) because it is stated
over `CloseoutPackRun.BigPack`, whose `ipack` field carries `LPackG`; its proof
only ever reads `FrontPack` and `Extra.scanAvail`.

## §4 `packRunR_O`, and why `pal_in_peg_final12` does **not** follow

`packRunR_O` proves `PackRunRO`: `CloseoutPackRun2.PackRunR` with `StepsI`
replaced by `StepsIO` (the same run predicate carrying `IPackO` instead of
`IPack`).  `stepsIO_of_stepsI` records that this is a weakening.

**The obstruction (`obstruction_of_final12`, stated as a comment-level fact and
witnessed by the type of `packRunR_O`).**  `CloseoutPackRun5.pal_in_peg_final11`
factors through `CloseoutPackRun2.cycleOracleI_of_cycleOracleMC3R`, which
consumes `PackRunR` and produces `CloseoutLPack5.CycleOracleI`; and
`CycleOracleI` → `H_oracleI` → `preTraceI_exists` → `PreTraceI.packs` →
`H_trailI` is a chain in which `IPack` is **produced** at the oracle end and
**consumed** at the trail end.  `CloseoutPackRun7.h_trailI_of_O` weakened the
consumer, which is free; `packRunR_O` weakens the producer, which is not — every
intermediate definition (`StepsI`, `ReachAtI`, `CycleOutI`, `CycleOracleI`,
`PreTraceI`, `H_bootI`, `H_oracleI`) mentions `IPack` positively and has to be
re-cut over `IPackO` before `pal_in_peg_final5` can be re-run.  That is seven
definitions and the `preTraceI_exists` recursion, not a corollary of anything
proved here.

So `pal_in_peg_final12` is **not** stated as a theorem in this file.  What is
stated is the exact residual: `packRunR_O` on one side, `h_trailI_of_O` on the
other, and the `StepsI`-family re-cut between them.  Recording that as a named
gap rather than an assumption keeps the honest line: standard axioms only,
unconditional `PAL ∈ PEG` remains open.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun8

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilCheckpoints
open PalPeg.GalilThrottledRun PalPeg.GalilTrailProof
open PalPeg.GalilFinalAssembly PalPeg.GalilFinalAssembly2 PalPeg.GalilFinalAssembly4
open PalPeg.CloseoutRadPack PalPeg.CloseoutRadPack2 PalPeg.CloseoutRadPack3
open PalPeg.CloseoutRadPack4
open PalPeg.CloseoutLPack PalPeg.CloseoutLPack3 PalPeg.CloseoutLPack4 PalPeg.CloseoutLPack5
open PalPeg.CloseoutLPack6
open PalPeg.CloseoutPackRun PalPeg.CloseoutPackRun2 PalPeg.CloseoutPackRun3
open PalPeg.CloseoutPackRun5 PalPeg.CloseoutPackRun7
open PalPeg.CloseoutOracleI PalPeg.CloseoutOracleI2 PalPeg.GalilInvPlus3
open PalPeg.GalilTrailScan PalPeg.GalilTrailBudget PalPeg.GalilTrailChain
open PalPeg.GalilTrailAssembly PalPeg.GalilTrailRad
open PalPeg.GalilFrontMono PalPeg.GalilInvPlus2

/-! ## 1. `LPackO` transport along a head-preserving step -/

/-- A VM step that leaves the three heads and the replay counter alone
transports the `MInv`-free pack.  `CloseoutLPack5.lpackG_of_same` without the
`hscm` argument: with `minv` gone there is nothing for it to feed. -/
theorem lpackO_of_same {w : List (Fin 2)} {c c' : Control} {s t : GalilVM}
    (hP : LPackO w c s) (hni : c.mode ≠ Mode.init)
    (hL : t.left = s.left) (hC : t.center = s.center) (hR : t.right = s.right)
    (hsc : c'.mode = Mode.scan → c'.replaying = false →
      c.mode = Mode.scan ∧ c.replaying = false) :
    LPackO w c' t := by
  refine ⟨fun _ => by rw [hL]; exact hP.lrep hni, ?_⟩
  intro hm hrr
  obtain ⟨hm0, hr0⟩ := hsc hm hrr
  obtain ⟨r, hi⟩ := hP.scanGeom hm0 hr0
  exact ⟨r, by rw [hL, hR, hC]; exact hi⟩

#print axioms lpackO_of_same

/-! ## 2. The leaves, and `lpackO_tick` -/

section LeavesO
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) the leaves of one tick, with `MInv` gone.**
`CloseoutLPack5.LTickLeavesG` minus `shiftDoneMinv`, and with `initPackG` /
`replayPackG` landing in `LPackO`. -/
structure LTickLeavesO (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  /-- The `init` landing. -/
  initPackO : c.mode = Mode.init → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).init s t →
    LPackO w {c with mode := Mode.scan, output := true} t
  /-- **The origin corner** — the one `CloseoutPackRun7.§3` showed is sharp. -/
  scanLeft : c.mode = Mode.scan → 0 < position (GalilScaffoldInputHead.left s.left)
  /-- The scan invariant in `scan` mode including a replay. -/
  scanInvR : c.mode = Mode.scan →
    ∃ r, ScanInvariant w (position s.center) r s.left s.right
  /-- The right head can move in `scan` mode. -/
  scanCanR : c.mode = Mode.scan → GalilScaffoldChainVerifier.canRight s.right
  /-- **The shift exit** — scan half only; the centre half is gone. -/
  shiftDoneScan : c.mode = Mode.shift →
    ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos s →
    ∃ r, ScanInvariant w (position s.center) r s.left s.right
  /-- `choose` re-centres on the right head — head half only. -/
  choosePackL : c.mode = Mode.choose → c.odd = true → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).choose s t →
    GalilScaffoldInputTrace.Represents t.left.head w ∧ t.left.head.focus ≠ none
  /-- A rewind unit walks `L` one place left. -/
  rewindLeft : c.mode = Mode.rewind → 0 < position (GalilScaffoldInputHead.left s.left)
  /-- The fallback landing, now without the centre invariant. -/
  replayPackO : c.mode = Mode.replayStart → ∀ (t : GalilVM) (o : Bool),
    (galilFrameS (PofC centre place entry w) q first).replayStart s t →
    LPackO w {c with mode := Mode.scan, clock := 2048, output := o, replaying := (galilFrameS (PofC centre place entry w) q first).replayPos t} t

/-- **`LTickLeavesG` forgets down to `LTickLeavesO`**: every surviving field is
weaker, and `shiftDoneMinv` is simply dropped. -/
theorem lticksO_of_lticksG {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (h : LTickLeavesG centre place entry q first w c s) :
    LTickLeavesO centre place entry q first w c s where
  initPackO := fun hm t ht => lpackO_of_lpackG (h.initPackG hm t ht)
  scanLeft := h.scanLeft
  scanInvR := h.scanInvR
  scanCanR := h.scanCanR
  shiftDoneScan := h.shiftDoneScan
  choosePackL := h.choosePackL
  rewindLeft := h.rewindLeft
  replayPackO := fun hm t o ht => lpackO_of_lpackG (h.replayPackG hm t o ht)

/-- **(KEY) `LPackO` survives one tick.**  `CloseoutLPack5.lpackG_tick` re-run
with the `minv` component deleted from every one of the 23 constructors.  The
two branches that changed in substance are `scan_match` (the `minv_match` /
`minv_matchR` transport is gone) and `shift_done` (the added `shiftDoneMinv`
corner is gone); the remaining 21 lose a `Mode.noConfusion` or a `minv_same`. -/
theorem lpackO_tick {w : List (Fin 2)} {c c' : Control} {s t : GalilVM}
    (hP : LPackO w c s) (hL : LTickLeavesO centre place entry q first w c s)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 ⟨c, s⟩ ⟨c', t⟩) :
    LPackO w c' t := by
  cases h
  case init =>
    rename_i hm hi
    exact hL.initPackO hm _ hi
  case scan_wait =>
    rename_i hm hav hb
    obtain ⟨hl, hr, -, hC, -, -, -, -, -, hrep, -, -⟩ :=
      backgroundS_fields (PofC centre place entry w) q first hb
    exact lpackO_of_same hP (by rw [hm]; decide) hl hC hr (fun hm' hr' => ⟨hm', hr'⟩)
  case scan_count =>
    rename_i hm hc hav hb
    obtain ⟨hl, hr, -, hC, -, -, -, -, -, hrep, -, -⟩ :=
      backgroundS_fields (PofC centre place entry w) q first hb
    exact lpackO_of_same hP (by rw [hm]; decide) hl hC hr (fun hm' hr' => ⟨hm', hr'⟩)
  case restart =>
    rename_i hm hb
    obtain ⟨wch, -, -, -, -, ht⟩ : restartVM entry s t := hb
    subst ht
    exact lpackO_of_same hP (by rw [hm]; decide) rfl rfl rfl (fun hm' hr' => ⟨hm', hr'⟩)
  case scan_match =>
    rename_i s' o hmt hm hc hcmp hav hpl ho
    obtain ⟨vs, vq, hvl, hvr, hmatch, rfl⟩ :=
      compare_matched_form centre place entry q first hcmp hmt
    have hni : c.mode ≠ Mode.init := by rw [hm]; decide
    have hpl' : t = (if c.replaying then
        {afterCompare s vs vq with replay := dec (afterCompare s vs vq).replay}
      else afterCompare s vs vq) := hpl
    have htl : t.left = (afterCompare s vs vq).left := by
      rw [hpl']; cases c.replaying <;> rfl
    have htr : t.right = (afterCompare s vs vq).right := by
      rw [hpl']; cases c.replaying <;> rfl
    have htc : t.center = s.center := by rw [hpl']; cases c.replaying <;> rfl
    have hcan := hL.scanCanR hm
    obtain ⟨r, hi⟩ := hL.scanInvR hm
    have hi' := matched_invariant' w vq hvl hvr hmatch hcan hi
    obtain ⟨hrepr, hpres⟩ := hP.lrep hni
    refine ⟨fun _ => ?_, fun _ _ => ⟨r + 1, ?_⟩⟩
    · rw [htl, afterCompare_left, hvl]
      exact lrep_left hrepr hpres (hL.scanLeft hm)
    · rw [htc, htl, htr]; exact hi'
  case scan_shift =>
    rename_i s' hmt hg hm hc hr hcmp hav hb
    obtain ⟨vs, vq, hvl, hvr, rfl⟩ :=
      compare_mismatch_form centre place entry q first hcmp hmt
    have hni : c.mode ≠ Mode.init := by rw [hm]; decide
    obtain ⟨wch, hchain, ht⟩ : beginShiftVM' (afterMismatch s vs vq) t := hb
    obtain ⟨hrepr, hpres⟩ := hP.lrep hni
    refine ⟨fun _ => ?_, fun hm' _ => Mode.noConfusion hm'⟩
    have htl : t.left = GalilScaffoldInputHead.left s.left := by
      rw [ht]; show vs.left = _; exact hvl
    rw [htl]; exact lrep_left hrepr hpres (hL.scanLeft hm)
  case scan_fallback =>
    rename_i s' hmt hm hc hg hr hcmp hav hb
    obtain ⟨vs, vq, hvl, hvr, rfl⟩ :=
      compare_mismatch_form centre place entry q first hcmp hmt
    have hni : c.mode ≠ Mode.init := by rw [hm]; decide
    obtain ⟨pl, ht⟩ : beginFallbackVM' (afterMismatch s vs vq) t := hb
    obtain ⟨hrepr, hpres⟩ := hP.lrep hni
    refine ⟨fun _ => ?_, fun hm' _ => Mode.noConfusion hm'⟩
    have htl : t.left = GalilScaffoldInputHead.left s.left := by
      rw [ht]; show vs.left = _; exact hvl
    rw [htl]; exact lrep_left hrepr hpres (hL.scanLeft hm)
  case shift_one =>
    rename_i hm hp hi
    have hni : c.mode ≠ Mode.init := by rw [hm]; decide
    obtain ⟨hcC, hcL, hcL2, wch, hw, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    obtain ⟨hrepr, hpres⟩ := hP.lrep hni
    refine ⟨fun _ => ?_, fun hm' _ => Mode.noConfusion (hm.symm.trans hm')⟩
    have htl : t.left = GalilScaffoldChainVerifier.right
        (GalilScaffoldChainVerifier.right s.left) := by rw [ht]; rfl
    rw [htl]
    obtain ⟨h1, h2⟩ := lrep_right hrepr hpres hcL
    exact lrep_right h1 h2 hcL2
  case shift_done =>
    rename_i o hm hp ho
    have hni : c.mode ≠ Mode.init := by rw [hm]; decide
    exact ⟨fun _ => hP.lrep hni, fun _ _ => hL.shiftDoneScan hm hp⟩
  case copy_one =>
    rename_i hm hp hi
    obtain ⟨-, hset⟩ := hi
    exact lpackO_of_same hP (by rw [hm]; decide) (by rw [hset]; rfl) (by rw [hset]; rfl)
      (by rw [hset]; rfl) (fun hm' _ => Mode.noConfusion (hm.symm.trans hm'))
  case copy_done =>
    rename_i hm hp hi
    obtain ⟨-, hset⟩ := hi
    exact lpackO_of_same hP (by rw [hm]; decide) (by rw [hset]; rfl) (by rw [hset]; rfl)
      (by rw [hset]; rfl) (fun hm' _ => Mode.noConfusion hm')
  case home_start =>
    rename_i hm hl hi
    obtain ⟨-, hset⟩ := hi
    exact lpackO_of_same hP (by rw [hm]; decide) (by rw [hset]; rfl) (by rw [hset]; rfl)
      (by rw [hset]; rfl) (fun hm' _ => Mode.noConfusion hm')
  case home_step =>
    rename_i hm hl hi
    obtain ⟨-, hset⟩ := hi
    exact lpackO_of_same hP (by rw [hm]; decide) (by rw [hset]; rfl) (by rw [hset]; rfl)
      (by rw [hset]; rfl) (fun hm' _ => Mode.noConfusion (hm.symm.trans hm'))
  case fpp_slice =>
    rename_i hm hi
    obtain ⟨-, hset⟩ := hi
    exact lpackO_of_same hP (by rw [hm]; decide) (by rw [hset]; rfl) (by rw [hset]; rfl)
      (by rw [hset]; rfl) (fun hm' _ => Mode.noConfusion (hm.symm.trans hm'))
  case fpp_done =>
    rename_i hm hi
    obtain ⟨-, hset⟩ := hi
    exact lpackO_of_same hP (by rw [hm]; decide) (by rw [hset]; rfl) (by rw [hset]; rfl)
      (by rw [hset]; rfl) (fun hm' _ => Mode.noConfusion hm')
  case markEnd_step =>
    rename_i hm he hi
    obtain ⟨-, hset⟩ := hi
    exact lpackO_of_same hP (by rw [hm]; decide) (by rw [hset]; rfl) (by rw [hset]; rfl)
      (by rw [hset]; rfl) (fun hm' _ => Mode.noConfusion (hm.symm.trans hm'))
  case markEnd_found =>
    rename_i hm he hi
    obtain ⟨⟨-, heq⟩, hset⟩ := hi
    exact lpackO_of_same hP (by rw [hm]; decide)
      (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl)
      (fun hm' _ => Mode.noConfusion hm')
  case choose_step =>
    rename_i hm hs hi
    obtain ⟨⟨-, heq⟩, hset⟩ := hi
    exact lpackO_of_same hP (by rw [hm]; decide)
      (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl)
      (fun hm' _ => Mode.noConfusion (hm.symm.trans hm'))
  case rewind_done =>
    rename_i hm hfi hi
    obtain ⟨heq, hset⟩ := hi
    exact lpackO_of_same hP (by rw [hm]; decide)
      (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl)
      (fun hm' _ => Mode.noConfusion hm')
  case choose_select =>
    rename_i hm hodd hs hi
    obtain ⟨hrepr, hpres⟩ := hL.choosePackL hm hodd _ hi
    exact ⟨fun _ => ⟨hrepr, hpres⟩, fun hm' _ => Mode.noConfusion hm'⟩
  case rewind_one =>
    rename_i hm hfi hpr hi
    have hni : c.mode ≠ Mode.init := by rw [hm]; decide
    obtain ⟨⟨-, heq⟩, hset⟩ := hi
    have htl : t.left = GalilScaffoldInputHead.left s.left := by rw [hset, heq]; rfl
    obtain ⟨hrepr, hpres⟩ := hP.lrep hni
    refine ⟨fun _ => ?_, fun hm' _ => Mode.noConfusion (hm.symm.trans hm')⟩
    rw [htl]; exact lrep_left hrepr hpres (hL.rewindLeft hm)
  case rewind_pair =>
    rename_i hm hfi hpr hi
    have hni : c.mode ≠ Mode.init := by rw [hm]; decide
    have heq := hi.1.2
    have hset := hi.2
    have htl : t.left = GalilScaffoldInputHead.left s.left := by rw [hset, heq]; rfl
    obtain ⟨hrepr, hpres⟩ := hP.lrep hni
    refine ⟨fun _ => ?_, fun hm' _ => Mode.noConfusion (hm.symm.trans hm')⟩
    rw [htl]; exact lrep_left hrepr hpres (hL.rewindLeft hm)
  case replayStart =>
    rename_i o hm ho ho' hi
    exact hL.replayPackO hm _ o hi

/-- `lpackO_tick` in state form. -/
theorem lpackO_tick' {w : List (Fin 2)} {x y : State GalilVM}
    (hP : LPackO w x.ctl x.vm) (hL : LTickLeavesO centre place entry q first w x.ctl x.vm)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y) :
    LPackO w y.ctl y.vm := by
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  exact lpackO_tick centre place entry q first hP hL h

/-- **The tick induction**: `LPackO` at every state of a pre-loaded trace. -/
theorem lpackO_steps {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : PreTrace centre place entry q first w st Tc)
    (hLv : ∀ i, i ≤ Tc w.length →
      LTickLeavesO centre place entry q first w (st i).ctl (st i).vm) :
    ∀ i, i ≤ Tc w.length → LPackO w (st i).ctl (st i).vm := by
  intro i
  induction i with
  | zero => intro _; rw [hP.start]; exact lpackO_boot w
  | succ n ih =>
    intro hi
    exact lpackO_tick' centre place entry q first (ih (by omega)) (hLv n (by omega))
      (hP.trace.tick n (by omega))

end LeavesO

#print axioms lticksO_of_lticksG
#print axioms lpackO_tick
#print axioms lpackO_steps

/-! ## 3. `BigPack2O` and the five-contract residual -/

section ResidO
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **The enlarged `MInv`-free pack.**  `CloseoutPackRun3.BigPack2` with
`BigPack.ipack : IPack` replaced by `IPackO` (the other four fields of
`BigPack` are `AuxPack` plus `CentreLive`, neither of which reads the pack). -/
structure BigPack2O (w : List (Fin 2)) (x : State GalilVM) : Prop where
  ipackO : IPackO centre place entry q first w x
  aux : AuxPack x.ctl x.vm
  live : CentreLive x.ctl x.vm
  extra : Extra centre place entry w x

/-- `BigPack2` forgets down to `BigPack2O`. -/
theorem bigPack2O_of_bigPack2 {w : List (Fin 2)} {x : State GalilVM}
    (h : BigPack2 centre place entry q first w x) :
    BigPack2O centre place entry q first w x :=
  ⟨ipackO_of_ipack centre place entry q first h.big.ipack,
    auxPack_of_bigPack centre place entry q first h.big, h.big.live, h.extra⟩

/-- **`canR_of_bigPack2` without the pack.**  Its proof only ever reads
`FrontPack` (replay half, via `GalilTrailRad.replayCan_of_pack`) and
`Extra.scanAvail` (non-replay half). -/
theorem canR_of_partsO {w : List (Fin 2)} {x : State GalilVM}
    (hf : FrontPack x.ctl x.vm) (he : Extra centre place entry w x)
    (hm : x.ctl.mode = Mode.scan) : GalilScaffoldChainVerifier.canRight x.vm.right := by
  cases hrep : x.ctl.replaying with
  | true => exact PalPeg.GalilTrailRad.replayCan_of_pack hf hrep
  | false => exact he.scanAvail hm hrep

/-- **(NAMED) the residual over the `MInv`-free enlarged pack — six fields.**
`CloseoutPackRun5.BigResid5G` minus `rShiftDoneMinv`, with `rInitPackG` and
`rReplayPackG` landing in `LPackO`, and every contract handed the weaker
hypothesis `BigPack2O`. -/
structure BigResid5O (w : List (Fin 2)) : Prop where
  rInitPackO : ∀ x : State GalilVM, BigPack2O centre place entry q first w x →
    x.ctl.mode = Mode.init → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).init x.vm t →
    LPackO w {x.ctl with mode := Mode.scan, output := true} t
  rScanInvR : ∀ x : State GalilVM, BigPack2O centre place entry q first w x →
    x.ctl.mode = Mode.scan →
    ∃ r, ScanInvariant w (position x.vm.center) r x.vm.left x.vm.right
  rShiftDoneScan : ∀ x : State GalilVM, BigPack2O centre place entry q first w x →
    x.ctl.mode = Mode.shift →
    ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos x.vm →
    ∃ r, ScanInvariant w (position x.vm.center) r x.vm.left x.vm.right
  rChoosePackL : ∀ x : State GalilVM, BigPack2O centre place entry q first w x →
    x.ctl.mode = Mode.choose → x.ctl.odd = true → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).choose x.vm t →
    GalilScaffoldInputTrace.Represents t.left.head w ∧ t.left.head.focus ≠ none
  rReplayPackO : ∀ x : State GalilVM, BigPack2O centre place entry q first w x →
    x.ctl.mode = Mode.replayStart → ∀ (t : GalilVM) (o : Bool),
    (galilFrameS (PofC centre place entry w) q first).replayStart x.vm t →
    LPackO w {x.ctl with mode := Mode.scan, clock := 2048, output := o, replaying := (galilFrameS (PofC centre place entry w) q first).replayPos t} t
  rShiftNext : ∀ x y : State GalilVM, BigPack2O centre place entry q first w x →
    Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y →
    SoundScanNR w y → ShiftLocal centre place entry q first w y

/-- **The leaves from the six contracts plus `Extra`.** -/
theorem lticksO_of_big5O {w : List (Fin 2)} (hr : BigResid5O centre place entry q first w)
    {x : State GalilVM} (hx : BigPack2O centre place entry q first w x) :
    LTickLeavesO centre place entry q first w x.ctl x.vm where
  initPackO := hr.rInitPackO x hx
  scanLeft := fun hm => by
    obtain ⟨r, hi⟩ := hr.rScanInvR x hx hm
    exact left_pos_of_two (margin_of_scanInv hi (hx.extra.scanMargin hm r hi))
  scanInvR := hr.rScanInvR x hx
  scanCanR := fun hm => canR_of_partsO centre place entry hx.aux.front hx.extra hm
  shiftDoneScan := hr.rShiftDoneScan x hx
  choosePackL := hr.rChoosePackL x hx
  rewindLeft := fun hm => left_pos_of_two (hx.extra.rewindMargin hm)
  replayPackO := hr.rReplayPackO x hx

/-- **`BigResid5G` implies `BigResid5O` — conditionally.**  The *conclusions*
weaken (`rShiftDoneMinv` goes unused, `LPackG` lands as `LPackO`), but the
*hypotheses* weaken too, in the wrong direction: each contract of `BigResid5G`
demands `BigPack2`, so it cannot be applied at a merely `BigPack2O` state.  The
explicit `hup` records that gap rather than hiding it; it is **not** provable
(`bigPack2O_of_bigPack2` is the true direction, and `MInvG` is real content).
`hup` is satisfiable exactly when the `MInv` half is re-derived at each state —
which is what deleting it was meant to avoid. -/
theorem big5O_of_big5G {w : List (Fin 2)}
    (hr : BigResid5G centre place entry q first w)
    (hup : ∀ x : State GalilVM, BigPack2O centre place entry q first w x →
      BigPack2 centre place entry q first w x) :
    BigResid5O centre place entry q first w where
  rInitPackO := fun x hx hm t ht => lpackO_of_lpackG (hr.rInitPackG x (hup x hx) hm t ht)
  rScanInvR := fun x hx => hr.rScanInvR x (hup x hx)
  rShiftDoneScan := fun x hx => hr.rShiftDoneScan x (hup x hx)
  rChoosePackL := fun x hx => hr.rChoosePackL x (hup x hx)
  rReplayPackO := fun x hx hm t o ht => lpackO_of_lpackG (hr.rReplayPackG x (hup x hx) hm t o ht)
  rShiftNext := fun x y hx => hr.rShiftNext x y (hup x hx)

/-- **One tick of the enlarged `MInv`-free pack.** -/
theorem bigPack2O_tick {w : List (Fin 2)} (hr : BigResid5O centre place entry q first w)
    (het : H_extraTick centre place entry q first w)
    {x y : State GalilVM} (hx : BigPack2O centre place entry q first w x)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hg : SoundScanNR w y) (hlv : CentreLive y.ctl y.vm) :
    BigPack2O centre place entry q first w y := by
  refine ⟨⟨?_, hr.rShiftNext x y hx h hg⟩,
    auxPack_tick centre place entry q first hx.aux hx.live h, hlv,
    het x y hx.extra h⟩
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  exact lpackO_tick centre place entry q first hx.ipackO.pack
    (lticksO_of_big5O centre place entry q first hr hx) h

end ResidO

#print axioms bigPack2O_of_bigPack2
#print axioms canR_of_partsO
#print axioms lticksO_of_big5O
#print axioms big5O_of_big5G
#print axioms bigPack2O_tick

/-! ## 4. `packRunR_O` -/

section RunO
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `CloseoutLPack5.StepsI` carrying `IPackO` instead of `IPack`. -/
def StepsIO (w : List (Fin 2)) (k : ℕ) (x y : State GalilVM) : Prop :=
  ∃ g : ℕ → State GalilVM, g 0 = x ∧ g k = y ∧
    Trace (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) g k ∧
    ∀ i, i ≤ k → IPackO centre place entry q first w (g i)

/-- A packed run is an `MInv`-free packed run. -/
theorem stepsIO_of_stepsI {w : List (Fin 2)} {k : ℕ} {x y : State GalilVM}
    (h : StepsI centre place entry q first w k x y) :
    StepsIO centre place entry q first w k x y := by
  obtain ⟨g, h0, hk, htr, hp⟩ := h
  exact ⟨g, h0, hk, htr, fun i hi => ipackO_of_ipack centre place entry q first (hp i hi)⟩

/-- `CloseoutPackRun2.PackRunR` over `StepsIO`. -/
def PackRunRO (w : List (Fin 2)) : Prop :=
  ∀ (c : Control) (r : GalilVM), InvLPC w c r →
    ∀ (j : ℕ) (x : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 j ⟨c, r⟩ x →
      ∀ (k : ℕ) (y : State GalilVM), IPackO centre place entry q first w x →
        StepsAll (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) k x y →
        StepsIO centre place entry q first w k x y

/-- **(KEY) `PackRunRO` from the six re-cut contracts plus the two `Extra`
obligations.**  `CloseoutPackRun5.packRunR_G` verbatim over `BigResid5O`. -/
theorem packRunR_O {w : List (Fin 2)}
    (hr : BigResid5O centre place entry q first w)
    (hee : H_extraEntry centre place entry w)
    (het : H_extraTick centre place entry q first w) :
    PackRunRO centre place entry q first w := by
  intro c r hIC j x hjx k y hx h
  have hlv0 : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 m ⟨c, r⟩ z →
      CentreLive z.ctl z.vm :=
    PalPeg.GalilOracleLeaves2.hlive_of_invLPC centre place entry q first hIC
  have haux0 : AuxPack c r :=
    ⟨coupled_of_invLPC hIC, front_of_invLPC hIC, copyPack_of_invLPC hIC⟩
  have hauxx : AuxPack x.ctl x.vm :=
    auxPack_steps centre place entry q first (x := ⟨c, r⟩) hlv0 haux0 hjx
  have hexx : Extra centre place entry w x :=
    extra_steps centre place entry q first het (x := ⟨c, r⟩) (hee c r hIC) hjx
  have hbx : BigPack2O centre place entry q first w x :=
    ⟨hx, hauxx, hlv0 j x hjx, hexx⟩
  obtain ⟨g, hg0, hgk, htr⟩ := stepsAll_fn h
  have hreach : ∀ i, i ≤ k →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 (j + i) ⟨c, r⟩ (g i) := by
    intro i hi
    have := steps_of_trace htr i hi
    rw [hg0] at this
    exact steps_trans hjx this
  have hbig : ∀ i, i ≤ k → BigPack2O centre place entry q first w (g i) := by
    intro i
    induction i with
    | zero => intro _; rw [hg0]; exact hbx
    | succ n ih =>
      intro hi
      exact bigPack2O_tick centre place entry q first hr het (ih (by omega))
        (htr.tick n (by omega)) (htr.good (n+1) hi)
        (hlv0 (j + (n+1)) (g (n+1)) (hreach (n+1) hi))
  exact ⟨g, hg0, hgk, htr, fun i hi => (hbig i hi).ipackO⟩

end RunO

#print axioms stepsIO_of_stepsI
#print axioms packRunR_O

end PalPeg.CloseoutPackRun8
