import PalPeg.CloseoutPackRun27
import PalPeg.GalilLeafDp

/-!
# `CloseoutPackRun39`: the DP-tape datum for the pack

`CloseoutPackRun22` left `Extra3.failed` (the DP tape, `StageFailed`) open at
entry and along every tick, and `Extra3.cand` open at `scan_shift`: `InvLPC`
says nothing about `r.dp`, and nothing produces `GalilDpSuffix.Candidate` from
`shiftGuardVM`.  This file names the datum that *does* live on the DP tape.

`DpStage P raw t Rad` is `GalilLeafDp.StageFailed` with the `pc = 347` clause
removed and `lower` pinned to the counter `t.lower` (the bound installed by
`restartVM`): the DP of the state has a `Result` on the calibrated window of
the centre, the window covers the scan radius, and the periods `2δ`, `δ ≤ lower`
were excluded by the earlier stages.  `DpFieldP x` carries, in `scan`, that the
search is parked in `.missed` with `pc = 347` and the stage datum, and, in
`shift`, that the DP landed in `pc = 346` with the stage datum.

* `dpField_to_failed` — `Extra3.failed` at every `scan` state, no hypothesis.
* `dpField_to_cand` — the DP's own candidate (`GalilDpCorrect.Candidate` on the
  window) at every `shift` state; `dpField_to_cand'` turns it into `Extra3.cand`
  under the ONE orientation hypothesis `H_candOrient` (the DP reports
  *prefix* palindromes of the window, `Extra3.cand` asks for `GalilDpSuffix`'s
  *suffix* form on the whole stream — that mismatch is the open producer).
* `dpField_tick` — transport.  Closed: `init` (pack), `scan_wait` /
  `scan_count` (a parked search is inert under `searchEffect`, so the DP tape,
  `lower`, `center`, `radius` are all kept by `backgroundS`), and every landing
  outside `scan`/`shift`.  ONE hypothesis per blocked branch: `hmatch`
  (`scan_match`: `radius` grows by one, so `Rad ≤ span` and the period
  exclusion at the larger span are new obligations), `hshiftEntry`
  (`scan_shift`: the DP result at the shift entry), `hshiftOne` (`shift_one`:
  the centre moves, so the window changes), `hshiftDone` (`shift_done`: the
  datum re-entering `scan`), `hreplayStart`, `hrestart`.

**Honest status of `hrestart`.**  `restartVM` sets `dp := reset entry _` and
`search := begin …`, so right after `restart` the DP is at `pc = entry`, not
`347`: `Extra3.failed` as stated (at *every* `scan` state) is refuted at the
restart landing, exactly as `GalilLeafPres` refuted the bare `ready`.  The
transportable shape is the stage-relative one ("`pc = 347` once the search is
parked"); `hrestart` is named here so that the refutation is visible at the
call site rather than hidden.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun39

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilRunSkeleton PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2
open PalPeg.CloseoutPackRun PalPeg.CloseoutPackRun2 PalPeg.CloseoutPackRun3
open PalPeg.CloseoutPackRun11 PalPeg.CloseoutPackRun18 PalPeg.CloseoutPackRun22
open PalPeg.CloseoutPackRun27 PalPeg.GalilLeafDp
open GalilScaffoldInputHead GalilScaffoldCounter GalilScaffoldChainVerifier

/-! ## 1. The datum -/

/-- **The stage datum on the DP tape.**  `StageFailed` minus the `pc = 347`
clause, with `lower` pinned to the counter `t.lower`. -/
def DpStage (P : Shared) (raw : List (Fin 2)) (t : GalilVM) (Rad : ℕ) : Prop :=
  ∃ span : ℕ,
    Rad ≤ span ∧
    GalilDpCorrect.Result ((GalilScaffoldPlace.stream (P.place t)).take (span+1))
      (value t.lower).toNat 0 (GalilScaffoldProgram.denote t.dp.config) ∧
    (∀ δ, 0 < δ → δ ≤ (value t.lower).toNat →
      ¬ HasPeriod (Span raw (position t.center) Rad) (2*δ))

/-- `DpStage` only looks at the window, the DP config, `lower` and `center`. -/
theorem dpStage_congr {P : Shared} {raw : List (Fin 2)} {s t : GalilVM} {Rad : ℕ}
    (hpl : P.place t = P.place s) (hdp : t.dp = s.dp) (hlo : t.lower = s.lower)
    (hce : t.center = s.center) (h : DpStage P raw s Rad) : DpStage P raw t Rad := by
  obtain ⟨span, h1, h2, h3⟩ := h
  refine ⟨span, h1, ?_, ?_⟩
  · rw [hpl, hdp, hlo]; exact h2
  · rw [hlo, hce]; exact h3

section FieldT
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry : ℕ) (first : Fin 9)

/-- **The DP-tape datum of the pack.**  In `scan` the search is parked
(`.missed`, absorbing under `searchStep`), the DP halted in failure, and the
stage datum holds at the scan radius; in `shift` the DP halted in success. -/
structure DpFieldP (w : List (Fin 2)) (x : State GalilVM) : Prop where
  parked : x.ctl.mode = Mode.scan →
    x.vm.search.mode = GalilScaffoldSearchFinish.Mode.missed
  pc347 : x.ctl.mode = Mode.scan → (GalilScaffoldProgram.denote x.vm.dp.config).pc = 347
  stage : x.ctl.mode = Mode.scan →
    DpStage (PofC centre place entry w) w x.vm (value x.vm.radius).toNat
  found : x.ctl.mode = Mode.shift →
    (GalilScaffoldProgram.denote x.vm.dp.config).pc = 346 ∧
      DpStage (PofC centre place entry w) w x.vm (value x.vm.radius).toNat

/-- Outside `scan` and `shift` the datum is vacuous. -/
theorem dpField_vacuous {w : List (Fin 2)} {x : State GalilVM}
    (hs : x.ctl.mode ≠ Mode.scan) (hsh : x.ctl.mode ≠ Mode.shift) :
    DpFieldP centre place entry w x :=
  ⟨fun h => absurd h hs, fun h => absurd h hs, fun h => absurd h hs, fun h => absurd h hsh⟩

/-! ## 2. The projections -/

/-- **(a) `Extra3.failed`** at every `scan` state, from the datum alone. -/
theorem dpField_to_failed {w : List (Fin 2)} {x : State GalilVM}
    (hf : DpFieldP centre place entry w x) (hm : x.ctl.mode = Mode.scan) :
    StageFailed (PofC centre place entry w) w x.vm (value x.vm.radius).toNat := by
  obtain ⟨span, h1, h2, h3⟩ := hf.stage hm
  exact ⟨(value x.vm.lower).toNat, span, h1, h2, hf.pc347 hm, h3⟩

/-- **(b) the DP's candidate** at every `shift` state: `Result` with `pc = 346`
is the success disjunct, which names a least candidate on the window. -/
theorem dpField_to_cand {w : List (Fin 2)} {x : State GalilVM}
    (hf : DpFieldP centre place entry w x) (hm : x.ctl.mode = Mode.shift) :
    ∃ n lower h, GalilDpCorrect.Candidate
      ((GalilScaffoldPlace.stream ((PofC centre place entry w).place x.vm)).take n) lower h := by
  obtain ⟨hpc, span, -, hres, -⟩ := hf.found hm
  rcases hres with ⟨k, -, hc, -, -, -, -⟩ | ⟨h347, -⟩
  · exact ⟨span + 1, _, k, hc⟩
  · rw [hpc] at h347; cases h347

/-- **(NAMED) the orientation bridge.**  The DP reports *prefix* palindromes of
the window (`GalilDpCorrect.Candidate`); `Extra3.cand` asks for
`GalilDpSuffix.Candidate` (suffix palindromes) on the *whole* stream.  This is
the open producer `CloseoutPackRun22` identified at `scan_shift`. -/
def H_candOrient : Prop :=
  ∀ (W : List (Fin 3)) (n lower h : ℕ),
    GalilDpCorrect.Candidate (W.take n) lower h → PalPeg.GalilDpSuffix.Candidate W lower h

/-- `Extra3.cand` from the datum, under the orientation bridge. -/
theorem dpField_to_cand' {w : List (Fin 2)} {x : State GalilVM}
    (hO : H_candOrient) (hf : DpFieldP centre place entry w x) (hm : x.ctl.mode = Mode.shift) :
    ∃ lower h, PalPeg.GalilDpSuffix.Candidate
      (GalilScaffoldPlace.stream ((PofC centre place entry w).place x.vm)) lower h := by
  obtain ⟨n, lower, h, hc⟩ := dpField_to_cand centre place entry hf hm
  exact ⟨lower, h, hO _ n lower h hc⟩

/-! ## 3. Transport -/

/-- A parked search is inert under `searchEffect`: the search view is kept. -/
theorem searchEffect_missed (P : Shared) {a : Bool} {s : GalilVM} {vq : SearchVM}
    (h : searchEffect P a s vq)
    (hmis : s.search.mode = GalilScaffoldSearchFinish.Mode.missed) :
    vq = searchLens.get s := by
  rcases h with ⟨_, hs⟩ | ⟨_, he⟩
  · have hm : (searchLens.get s).search.mode = GalilScaffoldSearchFinish.Mode.missed := hmis
    unfold searchStep at hs
    rw [hm] at hs
    exact hs
  · exact he

/-- `(PofC centre place entry w).place` is `place`. -/
theorem PofC_place (w : List (Fin 2)) : (PofC centre place entry w).place = place := rfl

/-- The concrete `placeC` is a function of the centre head, so the side
condition `hplace` of `dpField_tick` is discharged at the concrete instance. -/
theorem placeC_of_center {s t : GalilVM} (h : t.center = s.center) :
    GalilFinalAssembly2.placeC t = GalilFinalAssembly2.placeC s := by
  unfold GalilFinalAssembly2.placeC
  rw [h]

variable (q : ℕ)

/-- **`DpFieldP` along one `galilFrameS` tick.**  See the header for the
closed branches and the ONE hypothesis per blocked branch. -/
theorem dpField_tick {w : List (Fin 2)} {x y : State GalilVM}
    (hx : BigPack2M'' centre place entry q first w x) (hf : DpFieldP centre place entry w x)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hplace : ∀ s t : GalilVM, t.center = s.center → place t = place s)
    (hmatch : x.ctl.mode = Mode.scan → x.ctl.clock = 1 → y.ctl.mode = Mode.scan →
      y.ctl.clock = 2048 → DpFieldP centre place entry w y)
    (hshiftEntry : x.ctl.mode = Mode.scan → y.ctl.mode = Mode.shift →
      DpFieldP centre place entry w y)
    (hshiftOne : x.ctl.mode = Mode.shift → y.ctl.mode = Mode.shift →
      DpFieldP centre place entry w y)
    (hshiftDone : x.ctl.mode = Mode.shift → y.ctl.mode = Mode.scan →
      DpFieldP centre place entry w y)
    (hreplayStart : x.ctl.mode = Mode.replayStart → DpFieldP centre place entry w y)
    (hrestart : restartVM entry x.vm y.vm → DpFieldP centre place entry w y) :
    DpFieldP centre place entry w y := by
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  cases h
  case init =>
    rename_i hm0 h0
    exact absurd hm0 hx.aux.front.notInit
  case scan_wait =>
    rename_i hm0 h0 hb
    obtain ⟨-, -, -, hce, -, hrad, -, -, -, -, -, hse⟩ := backgroundS_fields _ q first hb
    have hvq : searchLens.get t = searchLens.get s :=
      searchEffect_missed _ hse (hf.parked hm0)
    have hdp : t.dp = s.dp := congrArg SearchVM.dp hvq
    have hlo : t.lower = s.lower := congrArg SearchVM.lower hvq
    have hsr : t.search = s.search := congrArg SearchVM.search hvq
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun hsh => ?_⟩
    · show t.search.mode = _
      rw [hsr]; exact hf.parked hm0
    · show (GalilScaffoldProgram.denote t.dp.config).pc = 347
      rw [hdp]; exact hf.pc347 hm0
    · show DpStage _ w t (value t.radius).toNat
      rw [hrad]
      exact dpStage_congr (hplace s t hce) hdp hlo hce (hf.stage hm0)
    · exact absurd (hm0.symm.trans hsh) (by decide)
  case scan_count =>
    rename_i hm0 h0 hc hb
    obtain ⟨-, -, -, hce, -, hrad, -, -, -, -, -, hse⟩ := backgroundS_fields _ q first hb
    have hvq : searchLens.get t = searchLens.get s :=
      searchEffect_missed _ hse (hf.parked hm0)
    have hdp : t.dp = s.dp := congrArg SearchVM.dp hvq
    have hlo : t.lower = s.lower := congrArg SearchVM.lower hvq
    have hsr : t.search = s.search := congrArg SearchVM.search hvq
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun hsh => ?_⟩
    · show t.search.mode = _
      rw [hsr]; exact hf.parked hm0
    · show (GalilScaffoldProgram.denote t.dp.config).pc = 347
      rw [hdp]; exact hf.pc347 hm0
    · show DpStage _ w t (value t.radius).toNat
      rw [hrad]
      exact dpStage_congr (hplace s t hce) hdp hlo hce (hf.stage hm0)
    · exact absurd (hm0.symm.trans hsh) (by decide)
  case scan_match =>
    have hm0 : c.mode = Mode.scan := by assumption
    have hc : c.clock = 1 := by assumption
    exact hmatch hm0 hc hm0 rfl
  case scan_shift =>
    have hm0 : c.mode = Mode.scan := by assumption
    exact hshiftEntry hm0 rfl
  case shift_one =>
    rename_i hm0 hp h0
    exact hshiftOne hm0 hm0
  case shift_done =>
    rename_i o hm0 hp ho
    exact hshiftDone hm0 rfl
  case replayStart =>
    rename_i o hm0 h0 ho ho'
    exact hreplayStart hm0
  case restart =>
    rename_i hm0 hb
    exact hrestart hb
  all_goals
    (clear hx hf hplace hmatch hshiftEntry hshiftOne hshiftDone hreplayStart hrestart
     refine dpField_vacuous centre place entry ?_ ?_ <;> (intro hm; simp_all))

end FieldT

#print axioms dpStage_congr
#print axioms dpField_to_failed
#print axioms dpField_to_cand
#print axioms dpField_to_cand'
#print axioms searchEffect_missed
#print axioms placeC_of_center
#print axioms dpField_tick

end PalPeg.CloseoutPackRun39
