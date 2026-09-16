import PalPeg.Main
import PalPeg.Chain
import PalPeg.GalilReportComplete
import PalPeg.GalilScaffoldTopOutputTrace

/-!
# Top-down skeleton: from the Galil scaffold to `PAL ∈ PEG`

This file is a *skeleton*: it states, with explicit named hypotheses, the exact
remaining obligations that turn the Galil scaffold controller
(`PalPeg.GalilScaffoldTop.Tick` over `galilFrameS`) into the unconditional
`RecognizedByTotalPEG PAL`.

The chain of reductions already present in the artifact is

* `PalPeg.pal_in_peg_of_structured` — a `StructuredMachine` recognizing exactly
  `PAL` gives `PAL ∈ PEG`;
* `refresh_exact` (`PalPeg.GalilReportComplete`) — at a *report point* of the
  scaffold (scan mode, not replaying, right head on the `k`-th letter), under
  the scan invariant and the leftmost-live-centre invariant `MInv`, the
  refreshed `output` flag is *exactly* the palindrome flag of `raw.take k`;
* `report_sound` (`PalPeg.GalilScaffoldTopOutputSound`) — the one-sided
  version, from `OutputRel` alone.

What this file adds is the bookkeeping that turns the *local* report-point
equivalence into the *global* language equivalence `M.SAccepts w ↔ w ∈ PAL`,
and then into `PAL ∈ PEG`. Everything that is genuinely open is isolated into
the named hypotheses `H_letter`, `H_first`, `H_report`, `H_empty` of
`pal_in_peg_of_galil`; the report-point equivalence itself is *discharged*
here (`output_iff_pal`).
-/

set_option autoImplicit false

namespace PalPeg.GalilStructuredSkeleton

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation

/-! ## Report points -/

/-- A **report point** of the scaffold for the input word `raw`: the controller
is not replaying, the scan invariant holds about the tracked centre, the
leftmost-live-centre invariant `MInv` holds, and the right head stands on the
last letter of `raw` (`position = 2·|raw| - 1`, the "letter" parity).

All four fields are stated over existing definitions
(`Control.replaying`, `ScanInvariant`, `MInv`, `position`). -/
structure ReportPoint (raw : List (Fin 2)) (st : State GalilVM) : Prop where
  /-- The controller is not in a replay. -/
  notReplaying : st.ctl.replaying = false
  /-- The scan invariant about the tracked centre, at some radius. -/
  scanInv : ∃ r : ℕ, ScanInvariant raw (position st.vm.center) r st.vm.left st.vm.right
  /-- The tracked centre is the leftmost live centre (Galil's global invariant). -/
  centre : MInv raw st.ctl st.vm
  /-- The right head stands on the last letter of `raw`. -/
  atLast : position st.vm.right = 2 * raw.length - 1
  /-- `raw` is nonempty (there is a letter to stand on). -/
  nonempty : 0 < raw.length

/-- The controller's `output` flag at the state is a *refreshed* value, i.e. it
was produced by the Scala refresh `if (!right.gap) output = left.isFirst` from
some previous value `old`. This is exactly `refresh` of the frame. -/
def Refreshed (P : Shared) (q : ℕ) (first : Fin 9) (st : State GalilVM) : Prop :=
  ∃ old : Bool, refresh (galilFrame P q first) st.vm old st.ctl.output

/-! ## The report-point equivalence (discharged) -/

/-- **Discharged.** At a report point whose output is refreshed, the output flag
is exactly the palindrome flag of the whole input. Proved from `refresh_exact`
with `k := raw.length` and `List.take_length`. -/
theorem output_iff_pal (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9) (st : State GalilVM)
    (hrp : ReportPoint raw st) (hfr : Refreshed P q first st) :
    st.ctl.output = true ↔ raw ∈ PAL := by
  obtain ⟨r, hi⟩ := hrp.scanInv
  obtain ⟨old, ho⟩ := hfr
  have h := refresh_exact raw P hP hP' q first (r := r) (k := raw.length) hi hrp.centre
    hrp.notReplaying hrp.nonempty (le_refl _) hrp.atLast old st.ctl.output ho
  rw [mem_PAL_iff_isPal]
  simpa [List.take_length] using h

/-- **Discharged (one-sided).** The soundness half also follows from `OutputRel`
alone, via `report_sound`; this is the statement the trace predicate `SoundOut`
propagates in `PalPeg.GalilScaffoldTopOutputTrace`.

Not used by the `PAL ∈ PEG` chain below: `output_iff_pal` gives both directions
at a report point, and the runs in `ScaffoldRun` carry no soundness decoration
at all. It is kept because `SoundScanNR` at a *non-replaying scan* report point
unfolds to exactly the `OutputRel` this lemma consumes. -/
theorem pal_of_output (raw : List (Fin 2)) (st : State GalilVM)
    (hsound : SoundOut raw st) (hrp : ReportPoint raw st) (hout : st.ctl.output = true) :
    raw ∈ PAL := by
  obtain ⟨r, hi⟩ := hrp.scanInv
  have hgap : st.vm.right.gap = false := by
    by_contra hg
    have hg' : st.vm.right.gap = true := by
      cases h : st.vm.right.gap with
      | false => exact absurd h hg
      | true => rfl
    have hpos : position st.vm.right = 2 * st.vm.right.head.left.length := by
      simp [position, hg']
    have hlast := hrp.atLast
    have hn := hrp.nonempty
    omega
  have h := report_sound raw st.ctl st.vm hsound hi hgap hout
  have hlen : st.vm.right.head.left.length = raw.length := by
    have hpos : position st.vm.right = 2 * st.vm.right.head.left.length - 1 := by
      simp [position, hgap]
    have hlast := hrp.atLast
    have hn := hrp.nonempty
    have hpres := hi.rightPresent
    have hp := represented_position st.vm.right.head raw hi.rightRep hpres
    omega
  rw [mem_PAL_iff_isPal]
  rw [hlen] at h
  simpa [List.take_length] using h

/-! ## The remaining obligation, and `PAL ∈ PEG` -/

/-- **The skeleton theorem.**

Given

* a structured (strictly real-time, `B` micro-steps per input symbol) machine
  `M` over a finite control type `Q` and tape alphabet `Γ`;
* per-input scaffold parameters `Pof w : Shared`, `qof w : ℕ`,
  `firstOf w : Fin 9` and a fixed match delay `delay`;

and the four hypotheses `H_letter`, `H_first`, `H_report`, `H_empty` below,
we get `RecognizedByTotalPEG PAL`, i.e. `PAL ∈ PEG`, unconditionally.

`H_report` is the only substantial obligation: it says that for every nonempty
input the scaffold has a *concrete run* — a `StepsAll` chain of
`GalilScaffoldTop.Tick`s of the merged scan frame `galilFrameS` — which starts
in the Scala initial controller `Control.initial delay` and ends in a report
point whose output is refreshed and equals `M`'s accept flag on `w`. -/
theorem pal_in_peg_of_galil {Q Γ : Type} [Fintype Q] [DecidableEq Q]
    [Fintype Γ] [DecidableEq Γ] {t B : ℕ} (hB : 0 < B)
    (M : StructuredMachine (Fin 2) Q Γ t B)
    (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ)
    (firstOf : List (Fin 2) → Fin 9) (delay : ℕ)
    -- H_letter: the shared `onLetter` predicate is the concrete "right head on a
    -- letter of `w`" predicate.
    (H_letter : ∀ w : List (Fin 2), (Pof w).onLetter = onLetterVM w)
    -- H_first: the shared `leftFirst` predicate is the concrete "left head on
    -- the first letter" predicate.
    (H_first : ∀ w : List (Fin 2), (Pof w).leftFirst = leftFirstVM)
    -- H_report: the scaffold run on a nonempty input reaches a refreshed report
    -- point, and the machine's accept flag there is the controller's `output`.
    (H_report : ∀ w : List (Fin 2), 0 < w.length →
      ∃ (n : ℕ) (x y : State GalilVM),
        x.ctl = GalilScaffoldController.initial delay ∧
        StepsAll (galilFrameS (Pof w) (qof w) (firstOf w)) delay (fun _ => True) n x y ∧
        ReportPoint w y ∧
        Refreshed (Pof w) (qof w) (firstOf w) y ∧
        (M.SAccepts w ↔ y.ctl.output = true))
    -- H_empty: the machine accepts the empty word (which is a palindrome).
    (H_empty : M.SAccepts []) :
    RecognizedByTotalPEG PAL := by
  refine pal_in_peg_of_structured hB M ?_
  intro w
  rcases w with _ | ⟨a, w⟩
  · simp only [H_empty, true_iff]
    rw [mem_PAL_iff_isPal]
    simp [PalPeg.IsPal]
  · have hlen : 0 < (a :: w).length := by simp
    obtain ⟨n, x, y, _hx, _hrun, hrp, hfr, hacc⟩ := H_report (a :: w) hlen
    exact hacc.trans
      (output_iff_pal (a :: w) (Pof (a :: w)) (H_letter (a :: w)) (H_first (a :: w))
        (qof (a :: w)) (firstOf (a :: w)) y hrp hfr)

/-- Packaged form: the existence of the machine and the run is a single
hypothesis. -/
theorem pal_in_peg_of_galil_exists {Q Γ : Type} [Fintype Q] [DecidableEq Q]
    [Fintype Γ] [DecidableEq Γ] {t B : ℕ} (hB : 0 < B) (delay : ℕ) :
    (∃ (M : StructuredMachine (Fin 2) Q Γ t B) (Pof : List (Fin 2) → Shared)
        (qof : List (Fin 2) → ℕ) (firstOf : List (Fin 2) → Fin 9),
      (∀ w : List (Fin 2), (Pof w).onLetter = onLetterVM w) ∧
      (∀ w : List (Fin 2), (Pof w).leftFirst = leftFirstVM) ∧
      (∀ w : List (Fin 2), 0 < w.length →
        ∃ (n : ℕ) (x y : State GalilVM),
          x.ctl = GalilScaffoldController.initial delay ∧
          StepsAll (galilFrameS (Pof w) (qof w) (firstOf w)) delay (fun _ => True) n x y ∧
          ReportPoint w y ∧
          Refreshed (Pof w) (qof w) (firstOf w) y ∧
          (M.SAccepts w ↔ y.ctl.output = true)) ∧
      M.SAccepts []) →
    RecognizedByTotalPEG PAL := by
  rintro ⟨M, Pof, qof, firstOf, hl, hf, hr, he⟩
  exact pal_in_peg_of_galil hB M Pof qof firstOf delay hl hf hr he

/-! ## Splitting the obligation: scaffold run vs. machine realization -/

/-- A **scaffold run** for the input `w` ending in the state `y`: some number of
`GalilScaffoldTop.Tick`s of the merged scan frame `galilFrameS`, all of whose
states satisfy the trivial predicate `fun _ => True`, starting in the Scala
initial controller `Control.initial delay`.

The run is stated over `galilFrameS` (the merged scan frame), which is what
every cycle lemma of the scaffold actually produces
(`PalPeg.GalilScaffoldTopOutputCycle`, `PalPeg.GalilMainLoopMInv`,
`PalPeg.GalilScaffoldTopFallbackRestartAll`).  Those lemmas decorate their runs
with `SoundScanNR w`; since nothing downstream of `ScaffoldRun` consumes the
decoration (both directions of the report-point equivalence come from
`output_iff_pal`, not from soundness), the predicate is left trivial here and
producers weaken theirs with `stepsAll_mono`.  This also lets the local layer
(`PalPeg.LocalTracking`), whose induction only ever carries `fun _ => True`,
supply a `ScaffoldRun` without an upgrade oracle. -/
def ScaffoldRun (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ)
    (firstOf : List (Fin 2) → Fin 9) (delay : ℕ) (w : List (Fin 2)) (y : State GalilVM) : Prop :=
  ∃ (n : ℕ) (x : State GalilVM),
    x.ctl = GalilScaffoldController.initial delay ∧
    StepsAll (galilFrameS (Pof w) (qof w) (firstOf w)) delay (fun _ => True) n x y

/-- **The skeleton theorem, split form.** Same conclusion as
`pal_in_peg_of_galil`, but the single hypothesis `H_report` is broken into two
*independent* obligations: `H_run` talks only about the scaffold (no `M`), and
`H_realize` only about the machine's agreement with a scaffold run (no claim
that such a run exists). -/
theorem pal_in_peg_of_galil' {Q Γ : Type} [Fintype Q] [DecidableEq Q]
    [Fintype Γ] [DecidableEq Γ] {t B : ℕ} (hB : 0 < B)
    (M : StructuredMachine (Fin 2) Q Γ t B)
    (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ)
    (firstOf : List (Fin 2) → Fin 9) (delay : ℕ)
    (H_letter : ∀ w : List (Fin 2), (Pof w).onLetter = onLetterVM w)
    (H_first : ∀ w : List (Fin 2), (Pof w).leftFirst = leftFirstVM)
    -- H_run: the scaffold alone reaches a refreshed report point.
    (H_run : ∀ w : List (Fin 2), 0 < w.length →
      ∃ y : State GalilVM,
        ScaffoldRun Pof qof firstOf delay w y ∧
        ReportPoint w y ∧
        Refreshed (Pof w) (qof w) (firstOf w) y)
    -- H_realize: the machine's accept flag agrees with the controller's output
    -- at any report point of any scaffold run.
    (H_realize : ∀ w : List (Fin 2), 0 < w.length → ∀ y : State GalilVM,
      ScaffoldRun Pof qof firstOf delay w y → ReportPoint w y →
        (M.SAccepts w ↔ y.ctl.output = true))
    (H_empty : M.SAccepts []) :
    RecognizedByTotalPEG PAL := by
  refine pal_in_peg_of_galil hB M Pof qof firstOf delay H_letter H_first ?_ H_empty
  intro w hw
  obtain ⟨y, ⟨n, x, hx, hrun⟩, hrp, hfr⟩ := H_run w hw
  exact ⟨n, x, y, hx, hrun, hrp, hfr, H_realize w hw y ⟨n, x, hx, hrun⟩ hrp⟩

#print axioms ScaffoldRun
#print axioms pal_in_peg_of_galil'

#print axioms output_iff_pal
#print axioms pal_of_output
#print axioms pal_in_peg_of_galil
#print axioms pal_in_peg_of_galil_exists

end PalPeg.GalilStructuredSkeleton
