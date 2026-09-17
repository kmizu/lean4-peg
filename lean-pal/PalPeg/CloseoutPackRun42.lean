import PalPeg.CloseoutPackRun39
import PalPeg.CloseoutPackRun36

/-!
# `CloseoutPackRun42`: `Extra4`, the transportable shape of the enlargement

`CloseoutPackRun39` established two facts about `CloseoutPackRun18.Extra3`:

* **`Extra3.failed` is FALSE as stated.**  It asks for `StageFailed` — in
  particular `pc = 347` — at *every* `scan` state, but `restartVM` sets
  `dp := reset entry _`, so at the `restart` landing the DP sits at
  `pc = entry`.  The transportable shape is stage-relative: *once the search is
  parked* (`search.mode = .missed`, absorbing under `searchStep`) the DP has
  completed and failed on the stage window.  That is exactly
  `CloseoutPackRun39.DpFieldP.parked` / `.pc347` / `.stage`.
* **`Extra3.cand` is stated in the wrong orientation.**  The DP reports
  *prefix* palindromes of the calibrated window
  (`GalilDpCorrect.Candidate ((stream (P.place s)).take n)`), while `Extra3.cand`
  asks for `GalilDpSuffix.Candidate` — *suffix* palindromes of the whole
  stream.  `CloseoutPackRun39.H_candOrient` is the named bridge.

`Extra4` (§1) is `Extra3` with both corrections applied: `parked` is promoted to
a field of its own, `failed` is guarded by it and split into `pc347` + `DpStage`,
and `cand` is stated in the DP's own prefix orientation.  `ready` and
`scanAvail` are copied verbatim.

## §2 The consumer audit

Every reader of `Extra3.failed` / `Extra3.cand` in the chain
`CloseoutPackRun11 / 18 / 22 / 30 / 36` was inspected.  The result is that
**no consumer reads either field at all**:

* `Extra3` is consumed only through `extra'_of_extra3` (Run18:115, Run30:206,
  Run36:153), which repackages `failed` and `cand` into `Extra'` unchanged.
* `Extra'` in turn is read by exactly three lemmas — `canR_of_partsM`
  (Run11:387, reads `scanAvail`), `lticksN_of_big6` / `lticksN_of_big6G` /
  `lticksN_of_lpackM2_pt` (Run11:455, Run30:152, Run36:98, reads `scanAvail`
  and `rewindMargin`) — and `bigPack2M''_tick` / `bigPack2MG2''_tick` /
  `packRunR_M''` / `packRunR_MG2`, which only *transport* it.
* `extra3_scanAvail_tick` (Run22:176) reads `scanAvail` only.

So `failed` and `cand` are, at present, **dead weight in the pack**: they are
carried from entry to every run state and never eliminated.  The live
consumers of the DP datum are elsewhere and reach it by their own route —
`GalilLeafDp.MismatchDp` takes `StageFailed` as its *conclusion* at a segment
mismatch exit `t` reached from an `InvLPC` entry (`GalilLeafDp.lean:123`), and
feeds `dpPack_of_stageFailed` (`GalilLeafDp.lean:109`), which is what
`GalilOracleMC3`'s `hdp` leaf consumes.  That consumer never touches
`Extra3.failed`.

Consequently the audit's answer to the two questions asked is:

* `failed` is read at parked states **only because it is read nowhere at all**;
  the stage-relative form loses nothing.
* `cand` is likewise read nowhere, so the *prefix* orientation is free to use
  inside the pack.  The bridge `cand_orient` is therefore **not proved here**:
  the one place a `GalilDpSuffix.Candidate` is genuinely wanted is
  `CloseoutPackRun19`'s shift-geometry discussion (Run19:26), which is not on
  the `final20` path, and `H_candOrient` (Run39:127) already names it at that
  single site.  Proving it needs `GalilDpSuffix.candidate_iff` together with the
  identification of `(stream (P.place t)).take (span+1)` with a *reversed*
  suffix-aligned slice of the raw word — i.e. `represents_decompose` +
  `Decodes` as in `dpPack_of_stageFailed` — and is named, not assumed, below.

## §3 The producers and `pal_in_peg_final21`

`extra4_of_fields` builds `Extra4` from `CloseoutPackRun39.DpFieldP`,
`CloseoutPackRun27.ReadyFieldP` and the `scanAvail` piece.  `H_extraEntry4`
and `H_extraTick4P` are the two obligations in the new shape, and
`extra3_of_extra4` turns `Extra4` back into `Extra3` under the single
orientation hypothesis `H_candOrient`.  `pal_in_peg_final21` is
`CloseoutPackRun36.pal_in_peg_final20` (Run36:712) with `hee` / `het` replaced
by the `Extra4` forms.

## Honest status

Standard axioms only; unconditional `PAL ∈ PEG` remains **open**.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun42

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilRunSkeleton PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2
open PalPeg.GalilThrottledRun PalPeg.GalilTrailProof PalPeg.GalilFinalAssembly
open PalPeg.CloseoutRadPack PalPeg.CloseoutRadPack2 PalPeg.CloseoutRadPack3
open PalPeg.CloseoutRadPack4 PalPeg.CloseoutLPack PalPeg.CloseoutLPack2
open PalPeg.CloseoutLPack3 PalPeg.CloseoutLPack4 PalPeg.CloseoutLPack5
open PalPeg.CloseoutLPack6
open PalPeg.GalilCheckpoints PalPeg.GalilTraceCost PalPeg.GalilLexMeasure
open PalPeg.GalilOracleMC PalPeg.GalilOracleMC2
open PalPeg.GalilLookRefined PalPeg.GalilFinalBaseNeed PalPeg.GalilFinalAssembly2
open PalPeg.GalilLedgerQ64 PalPeg.GalilLedgerAssembly PalPeg.GalilIntervalCost
open PalPeg.GalilLatchTracking PalPeg.GalilArriveChain PalPeg.GalilTickArrive
open PalPeg.GalilTruncTick PalPeg.GalilFinalAssembly4
open PalPeg.GalilTrailScan PalPeg.GalilTrailBudget PalPeg.GalilTrailChain
open PalPeg.GalilTrailAssembly PalPeg.GalilTrailRad PalPeg.GalilFrontMono
open PalPeg.CloseoutOracleI PalPeg.CloseoutOracleI2 PalPeg.GalilInvPlus3
open PalPeg.CloseoutPackRun5 PalPeg.CloseoutPackRun7 PalPeg.CloseoutPackRun8
open PalPeg.CloseoutPackRun9 PalPeg.CloseoutPackRun10
open PalPeg.CloseoutPackRun12 PalPeg.CloseoutPackRun16
open PalPeg.CloseoutPackRun19 PalPeg.CloseoutPackRun20 PalPeg.CloseoutPackRun21
open PalPeg.CloseoutPackRun23 PalPeg.CloseoutPackRun24 PalPeg.CloseoutPackRun26
open PalPeg.CloseoutPackRun29 PalPeg.CloseoutPackRun30 PalPeg.CloseoutPackRun33
open PalPeg.CloseoutPackRun35
open PalPeg.CloseoutPackRun PalPeg.CloseoutPackRun2 PalPeg.CloseoutPackRun3
open PalPeg.CloseoutPackRun11 PalPeg.CloseoutPackRun18 PalPeg.CloseoutPackRun22
open PalPeg.CloseoutPackRun27 PalPeg.CloseoutPackRun36 PalPeg.CloseoutPackRun39
open PalPeg.GalilLeafDp
open GalilScaffoldInputHead GalilScaffoldCounter GalilScaffoldChainVerifier

/-! ## 1. `Extra4` -/

section ExtraT
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) the transportable enlargement.**  `CloseoutPackRun18.Extra3` with
`failed` made stage-relative (guard `parked`, split into `pc347` + `DpStage`)
and `cand` stated in the DP's own prefix orientation. -/
structure Extra4 (w : List (Fin 2)) (x : State GalilVM) : Prop where
  ready : PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get x.vm)
  /-- The search is parked in `.missed` at every `scan` state. -/
  parked : x.ctl.mode = Mode.scan →
    x.vm.search.mode = GalilScaffoldSearchFinish.Mode.missed
  /-- **The stage-relative `failed`.**  Once the search is parked, the DP has
  completed and failed on the stage window. -/
  failed : x.ctl.mode = Mode.scan →
    x.vm.search.mode = GalilScaffoldSearchFinish.Mode.missed →
    (GalilScaffoldProgram.denote x.vm.dp.config).pc = 347 ∧
      DpStage (PofC centre place entry w) w x.vm (value x.vm.radius).toNat
  /-- **`cand` in the DP's orientation**: a prefix palindrome of the window. -/
  cand : x.ctl.mode = Mode.shift →
    ∃ n lower h, GalilDpCorrect.Candidate
      ((GalilScaffoldPlace.stream ((PofC centre place entry w).place x.vm)).take n) lower h
  scanAvail : x.ctl.mode = Mode.scan → x.ctl.replaying = false →
    GalilScaffoldChainVerifier.canRight x.vm.right

/-- **`Extra4` → `Extra3`.**  `failed` is discharged by `Extra4.parked`; `cand`
needs the ONE orientation hypothesis `CloseoutPackRun39.H_candOrient`. -/
theorem extra3_of_extra4 {w : List (Fin 2)} {x : State GalilVM}
    (hO : H_candOrient) (h : Extra4 centre place entry w x) :
    Extra3 centre place entry w x := by
  refine ⟨h.ready, fun hm => ?_, fun hm => ?_, h.scanAvail⟩
  · obtain ⟨hpc, span, h1, h2, h3⟩ := h.failed hm (h.parked hm)
    exact ⟨(value x.vm.lower).toNat, span, h1, h2, hpc, h3⟩
  · obtain ⟨n, lower, hh, hc⟩ := h.cand hm
    exact ⟨lower, hh, hO _ n lower hh hc⟩

/-- **(NAMED) the DP-orientation bridge, as a theorem statement.**  The window
of the pack is `(stream (P.place t)).take (span+1)`, a suffix-aligned slice of
the raw word (`GalilLeafDp.dpPack_of_stageFailed` / `represents_decompose`);
`GalilDpSuffix.candidate_iff` relates the two orientations through `reverse`.
`H_candOrient` is the general form; this is the same obligation restricted to
the windows that actually occur. -/
def CandOrientAt (w : List (Fin 2)) (x : State GalilVM) : Prop :=
  ∀ n lower h, GalilDpCorrect.Candidate
      ((GalilScaffoldPlace.stream ((PofC centre place entry w).place x.vm)).take n) lower h →
    PalPeg.GalilDpSuffix.Candidate
      (GalilScaffoldPlace.stream ((PofC centre place entry w).place x.vm)) lower h

/-- The general bridge specialises to every state. -/
theorem candOrientAt_of_candOrient (hO : H_candOrient) {w : List (Fin 2)}
    {x : State GalilVM} : CandOrientAt centre place entry w x :=
  fun n lower h hc => hO _ n lower h hc

/-- **`Extra4` → `Extra3`, pointwise bridge version.** -/
theorem extra3_of_extra4' {w : List (Fin 2)} {x : State GalilVM}
    (hO : CandOrientAt centre place entry w x) (h : Extra4 centre place entry w x) :
    Extra3 centre place entry w x := by
  refine ⟨h.ready, fun hm => ?_, fun hm => ?_, h.scanAvail⟩
  · obtain ⟨hpc, span, h1, h2, h3⟩ := h.failed hm (h.parked hm)
    exact ⟨(value x.vm.lower).toNat, span, h1, h2, hpc, h3⟩
  · obtain ⟨n, lower, hh, hc⟩ := h.cand hm
    exact ⟨lower, hh, hO n lower hh hc⟩

/-! ## 2. The producers -/

/-- **`Extra4` from the three data of the pack.**  `ready` from
`CloseoutPackRun27.ReadyFieldP` off `scan` is not needed — `Extra4.ready` is
unguarded, so the bare `SearchReady` is taken directly; `parked` / `failed` /
`cand` are `CloseoutPackRun39.DpFieldP`; `scanAvail` is Run22's piece. -/
theorem extra4_of_fields {w : List (Fin 2)} {x : State GalilVM}
    (hr : PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get x.vm))
    (hd : DpFieldP centre place entry w x)
    (ha : x.ctl.mode = Mode.scan → x.ctl.replaying = false → canRight x.vm.right) :
    Extra4 centre place entry w x := by
  refine ⟨hr, hd.parked, fun hm _ => ⟨hd.pc347 hm, hd.stage hm⟩, fun hm => ?_, ha⟩
  exact dpField_to_cand centre place entry hd hm

/-- **(NAMED) `Extra4` at an `InvLPC` origin.** -/
def H_extraEntry4 (w : List (Fin 2)) : Prop :=
  ∀ (c : Control) (r : GalilVM), InvLPC w c r → Extra4 centre place entry w ⟨c, r⟩

/-- **(NAMED) `Extra4` along one tick, bare source datum `Extra3`.**  This is
the shape `H_extraTick3` needs: the datum at `y` is produced in the corrected
form, and `extra3_of_extra4` converts it back. -/
def H_extraTick4 (w : List (Fin 2)) : Prop :=
  ∀ x y : State GalilVM, Extra3 centre place entry w x →
    Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y →
    Extra4 centre place entry w y

/-- **(NAMED) the pack-relative tick obligation**, `CloseoutPackRun22`'s
`H_extraTick3P` in the corrected shape. -/
def H_extraTick4P (w : List (Fin 2)) : Prop :=
  ∀ x y : State GalilVM, BigPack2M'' centre place entry q first w x →
    Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y →
    Extra4 centre place entry w y

/-- **`H_extraEntry4` from the entry pieces.**  `ready` is
`CloseoutPackRun22.extraEntry3_ready` (free), `scanAvail` is
`extraEntry3_scanAvail` modulo the end-of-input bound, and the DP datum at the
origin is the ONE residue `hdp`. -/
theorem extraEntry4_of_parts {w : List (Fin 2)}
    (hdp : ∀ (c : Control) (r : GalilVM), InvLPC w c r → DpFieldP centre place entry w ⟨c, r⟩)
    (hend : ∀ (c : Control) (r : GalilVM), InvLPC w c r → position r.right ≠ 2 * w.length) :
    H_extraEntry4 centre place entry w := by
  intro c r hIC
  exact extra4_of_fields centre place entry (extraEntry3_ready hIC) (hdp c r hIC)
    (fun _ _ => extraEntry3_scanAvail hIC (hend c r hIC))

/-- **`H_extraTick4P` from the three transported data.**  `scanAvail` is
`CloseoutPackRun22.extra3_scanAvail_tick` with its residue `hres`; the DP datum
at the landing is `hdp` (`CloseoutPackRun39.dpField_tick` with its six
hypotheses), and `hready` is `CloseoutPackRun27.readyField_tick`'s conclusion.
No field is assumed in the refuted shape. -/
theorem extraTick4P_of_parts {w : List (Fin 2)}
    (hready : ∀ x y : State GalilVM, BigPack2M'' centre place entry q first w x →
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y →
      PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get y.vm))
    (hdp : ∀ x y : State GalilVM, BigPack2M'' centre place entry q first w x →
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y →
      DpFieldP centre place entry w y)
    (hres : ∀ x y : State GalilVM, BigPack2M'' centre place entry q first w x →
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y →
      (x.ctl.mode ≠ Mode.scan ∨ x.ctl.clock = 1) →
      y.ctl.mode = Mode.scan → y.ctl.replaying = false → canRight y.vm.right) :
    H_extraTick4P centre place entry q first w :=
  fun x y hx h =>
    extra4_of_fields centre place entry (hready x y hx h) (hdp x y hx h)
      (extra3_scanAvail_tick centre place entry q first hx h (hres x y hx h))

/-- `H_extraTick4` yields `CloseoutPackRun18.H_extraTick3` under the bridge. -/
theorem h_extraTick3_of_h_extraTick4 {w : List (Fin 2)} (hO : H_candOrient)
    (h : H_extraTick4 centre place entry q first w) :
    H_extraTick3 centre place entry q first w :=
  fun x y he ht => extra3_of_extra4 centre place entry hO (h x y he ht)

/-- `H_extraEntry4` yields `CloseoutPackRun18.H_extraEntry3` under the bridge. -/
theorem h_extraEntry3_of_h_extraEntry4 {w : List (Fin 2)} (hO : H_candOrient)
    (h : H_extraEntry4 centre place entry w) :
    H_extraEntry3 centre place entry w :=
  fun c r hIC => extra3_of_extra4 centre place entry hO (h c r hIC)

end ExtraT

#print axioms extra3_of_extra4
#print axioms candOrientAt_of_candOrient
#print axioms extra3_of_extra4'
#print axioms extra4_of_fields
#print axioms extraEntry4_of_parts
#print axioms extraTick4P_of_parts
#print axioms h_extraTick3_of_h_extraTick4
#print axioms h_extraEntry3_of_h_extraEntry4

/-! ## 3. `pal_in_peg_final21` -/

/-- **`CloseoutPackRun36.pal_in_peg_final20` over `Extra4`.**  `hee` / `het` are
replaced by the corrected forms `H_extraEntry4` / `H_extraTick4`, plus the ONE
orientation hypothesis `hO : H_candOrient` (`CloseoutPackRun39`).  Nothing else
changes: `Extra3.failed` in its refuted universal shape no longer appears
anywhere on the path to the top. -/
theorem pal_in_peg_final21 (entry q : ℕ) (first : Fin 9)
    (hSP : ∀ (w : List (Fin 2)) (x : State GalilVM),
      BigPack2MG2 centreC placeC entry q first w x →
      ScanNR x → ShiftPal centreC placeC entry q first w x.vm)
    (hws : ∀ w : List (Fin 2), ∀ y : State GalilVM, WatchShiftG centreC placeC entry q first w y)
    (hO : H_candOrient)
    (hee : ∀ w : List (Fin 2), H_extraEntry4 centreC placeC entry w)
    (het : ∀ w : List (Fin 2), H_extraTick4 centreC placeC entry q first w)
    (hme : ∀ w : List (Fin 2), H_marksEntry' (PofC centreC placeC entry w) q first)
    (hsl : ∀ w : List (Fin 2), H_shiftLocalG centreC placeC entry q first w)
    (hsc : ∀ w : List (Fin 2), H_stageScan centreC placeC entry q first w)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleMC3 (PofC centreC placeC entry w) q first w)
    (hbs : H_bootShift centreC placeC entry q first)
    (hls : H_landShift centreC placeC entry q first)
    (hC : H_realizeLIMG2' centreC placeC entry q first) :
    RecognizedByTotalPEG PAL :=
  pal_in_peg_final20 entry q first hSP hws
    (fun w => h_extraEntry3_of_h_extraEntry4 centreC placeC entry hO (hee w))
    (fun w => h_extraTick3_of_h_extraTick4 centreC placeC entry q first hO (het w))
    hme hsl hsc hor hbs hls hC

#print axioms pal_in_peg_final21

end PalPeg.CloseoutPackRun42
