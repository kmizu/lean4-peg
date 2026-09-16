import PalPeg.GalilRunInv
import PalPeg.GalilReportReach
import PalPeg.GalilReportReplay

/-!
# Top-down skeleton for `H_run`

`PalPeg.GalilStructuredSkeleton.pal_in_peg_of_galil'` reduces `PAL ∈ PEG` to
four obligations, of which only two are open: `H_run` (the scaffold alone
reaches a refreshed report point on every nonempty input) and `H_realize`
(the machine's accept flag agrees with the controller's output there).

This file closes the *shape* of `H_run`: the unbounded main loop is turned
into a terminating well-founded recursion, driven by a single hypothesis, the
**cycle oracle**.  The oracle says exactly what the segment-construction and
glue lemmas have to deliver at an arbitrary restarted state: either the run
can already be finished at a report point, or one sound run reaches another
restarted state carrying the same invariant pack with the tracked centre
*strictly further right*.

Nothing in this file proves the oracle.  It proves that the oracle suffices:

* `run_from_restarted` — the well-founded recursion, on the measure
  `2·|raw| − position center`, which is a natural number because a restarted
  state's centre never passes the last cell of `encoded raw`
  (`inv_center_le`, from `Inv.input`, `ScanInvariant.rightPos` and
  `PalPeg.GalilEndOfInput.position_le`);
* `H_run_of_oracle` — prepending the `init` tick (`inv_init`), which is what
  establishes `Inv` in the first place;
* `pal_in_peg_of_oracles` — `pal_in_peg_of_galil'` with `H_letter`/`H_first`
  discharged by `rfl` and `H_run` supplied, leaving `H_realize` and `H_empty`.

The two glue lemmas `oracle_right_of_found` / `oracle_right_of_fallback` show
how `foundCycle_step` / `fallbackCycle_step` (via `inv_of_residual`) produce
the oracle's right disjunct, once a *progress* fact about the landing state is
available; that progress fact is the remaining mathematical content.
-/

set_option autoImplicit false

namespace PalPeg.GalilRunSkeleton

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainInputSupply
open PalPeg.GalilEndOfInput (position_le)

/-! ## The two predicates -/

/-- A finished run: a sound run from `⟨c, r⟩` to a refreshed report point. -/
def ReportReach (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (c : Control) (r : GalilVM) (y : State GalilVM) : Prop :=
  (∃ k, StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ y) ∧
    ReportPoint raw y ∧ Refreshed P q first y

/-- **The cycle oracle.**  At every state carrying the invariant pack `Inv`,
either the run can be finished at a refreshed report point, or one sound run
reaches a state that again carries `Inv` and whose tracked centre is strictly
further right.

This is the single hypothesis that the segment-construction and glue lemmas
(`PalPeg.GalilSegmentConstruct*`, `PalPeg.GalilCycleGlue`,
`PalPeg.GalilMainLoopMInv`, `PalPeg.GalilReportReach`,
`PalPeg.GalilReportReplay`) have to discharge. -/
def CycleOracle (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) : Prop :=
  ∀ (c : Control) (r : GalilVM), Inv raw c r →
    (∃ y : State GalilVM, ReportReach P q first raw c r y) ∨
    (∃ (cT : Control) (sT : GalilVM) (k : ℕ),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      Inv raw cT sT ∧ position r.center < position sT.center)

/-! ## The measure -/

/-- The tracked centre of an `Inv` state never passes the last cell of
`encoded raw`.  This is what makes `2 * raw.length - position r.center` a
decreasing natural-number measure. -/
theorem inv_center_le {raw : List (Fin 2)} {c : Control} {r : GalilVM} (h : Inv raw c r) :
    position r.center ≤ 2 * raw.length := by
  obtain ⟨Rad, last, hR⟩ := h.rest
  have hpos : position r.right = position r.center + Rad := hR.2.2.2.1.rightPos
  have hle : position r.right ≤ 2 * raw.length := position_le r.right raw h.input
  omega

/-! ## The well-founded recursion -/

/-- **The recursion, fuelled form.**  From any `Inv` state whose remaining
measure is at most `n`, the oracle drives the run to a refreshed report
point. -/
theorem run_fuel (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (hor : CycleOracle P q first raw) :
    ∀ (n : ℕ) (c : Control) (r : GalilVM), 2 * raw.length - position r.center ≤ n →
      Inv raw c r → ∃ y : State GalilVM, ReportReach P q first raw c r y := by
  intro n
  induction n with
  | zero =>
    intro c r hn hI
    rcases hor c r hI with hdone | ⟨cT, sT, k, hst, hIT, hlt⟩
    · exact hdone
    · exact absurd (inv_center_le hIT) (by have := inv_center_le hI; omega)
  | succ n ih =>
    intro c r hn hI
    rcases hor c r hI with hdone | ⟨cT, sT, k, hst, hIT, hlt⟩
    · exact hdone
    · have hn' : 2 * raw.length - position sT.center ≤ n := by
        have := inv_center_le hIT; omega
      obtain ⟨y, ⟨k', hst'⟩, hrp, hfr⟩ := ih cT sT hn' hIT
      exact ⟨y, ⟨k + k', stepsAll_trans hst hst'⟩, hrp, hfr⟩

/-- **The recursion.**  Well-founded on `2 * raw.length - position r.center`,
which decreases at every turn by the oracle's progress clause and stays a
natural number by `inv_center_le`. -/
theorem run_from_restarted (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (hor : CycleOracle P q first raw) (c : Control) (r : GalilVM) (hI : Inv raw c r) :
    ∃ y : State GalilVM,
      (∃ k, StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ y) ∧
        ReportPoint raw y ∧ Refreshed P q first y :=
  run_fuel P q first raw hor (2 * raw.length - position r.center) c r le_rfl hI

/-! ## Prepending the `init` tick -/

/-- The per-input shared record of the concrete scaffold: `sharedC` with the
input-dependent `onLetter`.  `H_letter` and `H_first` of
`pal_in_peg_of_galil'` are `rfl` for it. -/
def PofC (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ)
    (w : List (Fin 2)) : Shared :=
  sharedC (onLetterVM w) leftFirstVM centre place entry

theorem PofC_onLetter (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry : ℕ) (w : List (Fin 2)) : (PofC centre place entry w).onLetter = onLetterVM w := rfl

theorem PofC_leftFirst (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry : ℕ) (w : List (Fin 2)) : (PofC centre place entry w).leftFirst = leftFirstVM := rfl

/-- **`H_run` from the oracle.**  The `init` tick of `inv_init` establishes the
pack; the recursion finishes the run.

The boot VM is taken as a parameter with exactly the hypotheses `inv_init`
consumes (right head on the first place, the three counters empty, the shift
idle); constructing one explicitly is a separate, purely definitional task —
see the gap note in the module header. -/
theorem H_run_of_oracle (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9)
    (boot : List (Fin 2) → GalilVM)
    (hbr : ∀ w : List (Fin 2), (boot w).right = initialHead w)
    (hbrad : ∀ w : List (Fin 2), (boot w).radius = reset)
    (hblen : ∀ w : List (Fin 2), (boot w).length = reset)
    (hbrep : ∀ w : List (Fin 2), (boot w).replay = reset)
    (hbsi : ∀ w : List (Fin 2), ShiftIdle (boot w))
    (hor : ∀ w : List (Fin 2), CycleOracle (PofC centre place entry w) q first w) :
    ∀ w : List (Fin 2), 0 < w.length →
      ∃ y : State GalilVM,
        ScaffoldRun (PofC centre place entry) (fun _ => q) (fun _ => first) 2048 w y ∧
        ReportPoint w y ∧ Refreshed (PofC centre place entry w) q first y := by
  intro w hw
  rcases w with _ | ⟨a, rest⟩
  · simp at hw
  · obtain ⟨c1, t, hst, hI⟩ :=
      inv_init (onLetterVM (a :: rest)) leftFirstVM centre place entry q first
        (boot (a :: rest)) a rest (hbr (a :: rest)) (hbrad (a :: rest)) (hblen (a :: rest))
        (hbrep (a :: rest)) (hbsi (a :: rest))
    obtain ⟨y, ⟨k, hst'⟩, hrp, hfr⟩ :=
      run_from_restarted (PofC centre place entry (a :: rest)) q first (a :: rest)
        (hor (a :: rest)) c1 t hI
    exact ⟨y, ⟨1 + k, ⟨initial 2048, boot (a :: rest)⟩, rfl,
      stepsAll_mono (fun _ _ => trivial) (stepsAll_trans hst hst')⟩, hrp, hfr⟩

/-! ## The global variant, for the published report lemmas

`scaffoldRun_report_of_last_consume` (`PalPeg.GalilReportReach`) and
`scaffoldRun_report_after_replay` (`PalPeg.GalilReportReplay`) conclude in the
*global* form `∃ y, ScaffoldRun … w y ∧ ReportPoint w y ∧ Refreshed … y`: they
absorb the prefix of the run themselves (they take the run so far as a
hypothesis).  `CycleOracleG` is the oracle whose left disjunct is exactly that
form, so those two lemmas discharge it verbatim, and `H_run_of_oracleG` needs
no trailing composition at all. -/

/-- The oracle with the *global* termination clause. -/
def CycleOracleG (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (raw : List (Fin 2)) : Prop :=
  ∀ (c : Control) (r : GalilVM), Inv raw c r →
    (∃ y : State GalilVM,
      ScaffoldRun (PofC centre place entry) (fun _ => q) (fun _ => first) 2048 raw y ∧
      ReportPoint raw y ∧ Refreshed (PofC centre place entry raw) q first y) ∨
    (∃ (cT : Control) (sT : GalilVM) (k : ℕ),
      StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundScanNR raw) k
        ⟨c, r⟩ ⟨cT, sT⟩ ∧
      Inv raw cT sT ∧ position r.center < position sT.center)

theorem runG_fuel (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (hor : CycleOracleG centre place entry q first raw) :
    ∀ (n : ℕ) (c : Control) (r : GalilVM), 2 * raw.length - position r.center ≤ n →
      Inv raw c r →
      ∃ y : State GalilVM,
        ScaffoldRun (PofC centre place entry) (fun _ => q) (fun _ => first) 2048 raw y ∧
        ReportPoint raw y ∧ Refreshed (PofC centre place entry raw) q first y := by
  intro n
  induction n with
  | zero =>
    intro c r hn hI
    rcases hor c r hI with hdone | ⟨cT, sT, k, _, hIT, hlt⟩
    · exact hdone
    · exact absurd (inv_center_le hIT) (by have := inv_center_le hI; omega)
  | succ n ih =>
    intro c r hn hI
    rcases hor c r hI with hdone | ⟨cT, sT, k, _, hIT, hlt⟩
    · exact hdone
    · exact ih cT sT (by have := inv_center_le hIT; omega) hIT

/-- **`H_run` from the global oracle.** -/
theorem H_run_of_oracleG (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9)
    (boot : List (Fin 2) → GalilVM)
    (hbr : ∀ w : List (Fin 2), (boot w).right = initialHead w)
    (hbrad : ∀ w : List (Fin 2), (boot w).radius = reset)
    (hblen : ∀ w : List (Fin 2), (boot w).length = reset)
    (hbrep : ∀ w : List (Fin 2), (boot w).replay = reset)
    (hbsi : ∀ w : List (Fin 2), ShiftIdle (boot w))
    (hor : ∀ w : List (Fin 2), CycleOracleG centre place entry q first w) :
    ∀ w : List (Fin 2), 0 < w.length →
      ∃ y : State GalilVM,
        ScaffoldRun (PofC centre place entry) (fun _ => q) (fun _ => first) 2048 w y ∧
        ReportPoint w y ∧ Refreshed (PofC centre place entry w) q first y := by
  intro w hw
  rcases w with _ | ⟨a, rest⟩
  · simp at hw
  · obtain ⟨c1, t, _, hI⟩ :=
      inv_init (onLetterVM (a :: rest)) leftFirstVM centre place entry q first
        (boot (a :: rest)) a rest (hbr (a :: rest)) (hbrad (a :: rest)) (hblen (a :: rest))
        (hbrep (a :: rest)) (hbsi (a :: rest))
    exact runG_fuel centre place entry q first (a :: rest) (hor (a :: rest))
      (2 * (a :: rest).length - position t.center) c1 t le_rfl hI

/-! ## `PAL ∈ PEG` from the oracle -/

/-- **The oracle form of the skeleton theorem.**  `H_letter` and `H_first` are
`rfl`; `H_run` comes from the oracle; `H_realize` and `H_empty` are kept as
hypotheses. -/
theorem pal_in_peg_of_oracles {Q Γ : Type} [Fintype Q] [DecidableEq Q]
    [Fintype Γ] [DecidableEq Γ] {t B : ℕ} (hB : 0 < B)
    (M : PalPeg.Program.StructuredMachine (Fin 2) Q Γ t B)
    (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9)
    (boot : List (Fin 2) → GalilVM)
    (hbr : ∀ w : List (Fin 2), (boot w).right = initialHead w)
    (hbrad : ∀ w : List (Fin 2), (boot w).radius = reset)
    (hblen : ∀ w : List (Fin 2), (boot w).length = reset)
    (hbrep : ∀ w : List (Fin 2), (boot w).replay = reset)
    (hbsi : ∀ w : List (Fin 2), ShiftIdle (boot w))
    (hor : ∀ w : List (Fin 2), CycleOracle (PofC centre place entry w) q first w)
    (H_realize : ∀ w : List (Fin 2), 0 < w.length → ∀ y : State GalilVM,
      ScaffoldRun (PofC centre place entry) (fun _ => q) (fun _ => first) 2048 w y →
      ReportPoint w y → (M.SAccepts w ↔ y.ctl.output = true))
    (H_empty : M.SAccepts []) :
    PegSeparation.RecognizedByTotalPEG PAL :=
  pal_in_peg_of_galil' hB M (PofC centre place entry) (fun _ => q) (fun _ => first) 2048
    (PofC_onLetter centre place entry) (PofC_leftFirst centre place entry)
    (H_run_of_oracle centre place entry q first boot hbr hbrad hblen hbrep hbsi hor)
    H_realize H_empty

/-! ## How the main-loop cycles produce the oracle's right disjunct -/

/-- The pack, rebuilt at the landing state of a cycle from what the cycle
lemmas export (`MInv` + `Restarted`) plus the residual facts.  This is the
construction inside `inv_after_found`, isolated so that the fallback cycle can
reuse it. -/
theorem inv_of_residual {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    (hM : MInv raw c s) (hR : ∃ (Rad : ℕ) (last : Counter), Restarted raw s Rad last)
    (hres : FoundResidual raw c s) : Inv raw c s := by
  obtain ⟨hmode, hstage, hfr, hrr, hsi⟩ := hres
  obtain ⟨Rad, last, hR'⟩ := hR
  exact
    { rest := ⟨Rad, last, hR'⟩, minv := hM, mode := hmode, stage := hstage
      search := searchReady_of_restarted hR'
      block := blockInv_of_restarted hR'
      frontier := hfr, rest_replay := hrr
      input := input_of_restarted hR'
      shiftIdle := hsi }

/-- A found cycle supplies the oracle's right disjunct, given the residual
facts at the landing state and the progress fact about it. -/
theorem oracle_right_of_found (P : Shared) (qq : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (c : Control) (r : GalilVM) (hC : FoundCycle P qq first 2048 raw c r) (hI : Inv raw c r)
    (hres : ∀ (cT : Control) (sT : GalilVM), MInv raw cT sT →
      (∃ (Rad' : ℕ) (last' : Counter), Restarted raw sT Rad' last') → FoundResidual raw cT sT)
    (hprog : ∀ (cT : Control) (sT : GalilVM), Inv raw cT sT →
      (∃ k, StepsAll (galilFrameS P qq first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩) →
      position r.center < position sT.center) :
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ),
      StepsAll (galilFrameS P qq first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      Inv raw cT sT ∧ position r.center < position sT.center := by
  obtain ⟨Rad, last, hR⟩ := hI.rest
  obtain ⟨cT, sT, ⟨k, hst⟩, hM, hRT⟩ := foundCycle_step P qq first 2048 raw c r hC Rad last hR hI.minv
  have hIT : Inv raw cT sT := inv_of_residual hM hRT (hres cT sT hM hRT)
  exact ⟨cT, sT, k, hst, hIT, hprog cT sT hIT ⟨k, hst⟩⟩

/-- A fallback cycle supplies the oracle's right disjunct, under the same two
side conditions. -/
theorem oracle_right_of_fallback (P : Shared) (qq : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (c : Control) (r : GalilVM) (hC : FallbackCycle P qq first 2048 raw c r) (hI : Inv raw c r)
    (hres : ∀ (cT : Control) (sT : GalilVM), MInv raw cT sT →
      (∃ (Rad' : ℕ) (last' : Counter), Restarted raw sT Rad' last') → FoundResidual raw cT sT)
    (hprog : ∀ (cT : Control) (sT : GalilVM), Inv raw cT sT →
      (∃ k, StepsAll (galilFrameS P qq first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩) →
      position r.center < position sT.center) :
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ),
      StepsAll (galilFrameS P qq first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      Inv raw cT sT ∧ position r.center < position sT.center := by
  obtain ⟨Rad, last, hR⟩ := hI.rest
  obtain ⟨cT, sT, ⟨k, hst⟩, hM, hRT⟩ :=
    fallbackCycle_step P qq first 2048 raw c r hC Rad last hR hI.minv
  have hIT : Inv raw cT sT := inv_of_residual hM hRT (hres cT sT hM hRT)
  exact ⟨cT, sT, k, hst, hIT, hprog cT sT hIT ⟨k, hst⟩⟩

/-! ## How a report point finishes the run

The two published "reach the report point" lemmas produce exactly
`ReportReach`'s payload, but relative to the *initial* state of the whole run
rather than to the current `Inv` state.  `reportReach_of_scaffoldRun` records
that the oracle's left disjunct is what they give once the prefix of the run
is absorbed; it is stated as a pure repackaging so that the call sites of
`scaffoldRun_report_of_last_consume` and `scaffoldRun_report_after_replay`
have a named target. -/
theorem reportReach_of_run (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (c : Control) (r : GalilVM) (y : State GalilVM)
    (hst : ∃ k, StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ y)
    (hrp : ReportPoint raw y) (hfr : Refreshed P q first y) :
    ReportReach P q first raw c r y := ⟨hst, hrp, hfr⟩

#print axioms inv_center_le
#print axioms run_fuel
#print axioms run_from_restarted
#print axioms PofC_onLetter
#print axioms PofC_leftFirst
#print axioms H_run_of_oracle
#print axioms pal_in_peg_of_oracles
#print axioms CycleOracleG
#print axioms runG_fuel
#print axioms H_run_of_oracleG
#print axioms inv_of_residual
#print axioms oracle_right_of_found
#print axioms oracle_right_of_fallback
#print axioms reportReach_of_run

end PalPeg.GalilRunSkeleton
