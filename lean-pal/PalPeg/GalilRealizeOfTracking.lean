import PalPeg.GalilStructuredSkeleton

/-!
# From *tracking* to `H_realize`, and to `PAL ∈ PEG`

`PalPeg.GalilStructuredSkeleton.pal_in_peg_of_galil'` splits the scaffold
obligation into

* `H_run`   — the scaffold alone reaches a *refreshed* report point, and
* `H_realize` — at *any* report point of *any* scaffold run the machine's
  accept flag agrees with the controller's `output`.

In practice one proves a single *tracking* statement: for every nonempty input
there is **one** state `y0` which is simultaneously the end of a scaffold run,
a report point, refreshed, and where `M.SAccepts w ↔ y0.ctl.output = true`.
This file performs the purely logical reduction from that tracking statement.

The key observation is that `output_iff_pal` pins the controller's `output` at a
refreshed report point to `decide (w ∈ PAL)`. Hence tracking at a *single*
`y0` already determines the machine's language:

  `M.SAccepts w ↔ w ∈ PAL`   (`saccepts_iff_pal_of_tracking`)

and from that, agreement at *every* refreshed report point follows.

## Gap (why `Refreshed` cannot be dropped from `H_realize`)

`output_iff_pal` genuinely needs `Refreshed`: it is proved from `refresh_exact`,
which reasons about the value produced by the Scala refresh
`if (!right.gap) output = left.isFirst`. An arbitrary `y` satisfying only
`ScaffoldRun`/`ReportPoint` carries `SoundScanNR w` (a *one-sided* soundness
predicate), which cannot force `y.ctl.output = true` when `w ∈ PAL`; a state
whose `output` is a stale `false` is still sound. So the literal
`H_realize` shape of `pal_in_peg_of_galil'` is **not** derivable from tracking,
and `H_realize_of_tracking` below carries `Refreshed` on the target `y` as an
extra premise.

This is harmless for the chain: `pal_in_peg_of_tracking` goes through the
original combined form `pal_in_peg_of_galil`, where `H_realize` is only ever
used at the very `y0` that the run provides — and that `y0` *is* refreshed.
-/

set_option autoImplicit false

namespace PalPeg.GalilRealizeOfTracking

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton

/-- **The tracking hypothesis**, as a predicate: for every nonempty input there
is a single state `y0` that is the end of a scaffold run, a report point, has a
refreshed `output`, and at which the machine's accept flag agrees with that
`output`. -/
def Tracking {Q Γ : Type} [Fintype Q] [DecidableEq Q] [Fintype Γ] [DecidableEq Γ]
    {t B : ℕ} (M : StructuredMachine (Fin 2) Q Γ t B)
    (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ)
    (firstOf : List (Fin 2) → Fin 9) (delay : ℕ) : Prop :=
  ∀ w : List (Fin 2), 0 < w.length →
    ∃ y0 : State GalilVM,
      ScaffoldRun Pof qof firstOf delay w y0 ∧
      ReportPoint w y0 ∧
      Refreshed (Pof w) (qof w) (firstOf w) y0 ∧
      (M.SAccepts w ↔ y0.ctl.output = true)

/-- Tracking at a single state already determines the machine's language on
nonempty inputs: the refreshed report point's `output` *is* the palindrome flag
(`output_iff_pal`). -/
theorem saccepts_iff_pal_of_tracking {Q Γ : Type} [Fintype Q] [DecidableEq Q]
    [Fintype Γ] [DecidableEq Γ] {t B : ℕ}
    (M : StructuredMachine (Fin 2) Q Γ t B)
    (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ)
    (firstOf : List (Fin 2) → Fin 9) (delay : ℕ)
    (H_letter : ∀ w : List (Fin 2), (Pof w).onLetter = onLetterVM w)
    (H_first : ∀ w : List (Fin 2), (Pof w).leftFirst = leftFirstVM)
    (htrack : Tracking M Pof qof firstOf delay) :
    ∀ w : List (Fin 2), 0 < w.length → (M.SAccepts w ↔ w ∈ PAL) := by
  intro w hw
  obtain ⟨y0, _hrun0, hrp0, hfr0, hacc0⟩ := htrack w hw
  exact hacc0.trans
    (output_iff_pal w (Pof w) (H_letter w) (H_first w) (qof w) (firstOf w) y0 hrp0 hfr0)

/-- **`H_realize` from tracking** (with the unavoidable `Refreshed` premise on
the target state `y`, see the module docstring).

Both sides are pinned to `w ∈ PAL`: the machine by
`saccepts_iff_pal_of_tracking`, the controller by `output_iff_pal` at `y`. -/
theorem H_realize_of_tracking {Q Γ : Type} [Fintype Q] [DecidableEq Q]
    [Fintype Γ] [DecidableEq Γ] {t B : ℕ}
    (M : StructuredMachine (Fin 2) Q Γ t B)
    (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ)
    (firstOf : List (Fin 2) → Fin 9) (delay : ℕ)
    (H_letter : ∀ w : List (Fin 2), (Pof w).onLetter = onLetterVM w)
    (H_first : ∀ w : List (Fin 2), (Pof w).leftFirst = leftFirstVM)
    (htrack : Tracking M Pof qof firstOf delay) :
    ∀ w : List (Fin 2), 0 < w.length → ∀ y : State GalilVM,
      ScaffoldRun Pof qof firstOf delay w y → ReportPoint w y →
        Refreshed (Pof w) (qof w) (firstOf w) y →
        (M.SAccepts w ↔ y.ctl.output = true) := by
  intro w hw y _hrun hrp hfr
  refine (saccepts_iff_pal_of_tracking M Pof qof firstOf delay H_letter H_first htrack w hw).trans ?_
  exact (output_iff_pal w (Pof w) (H_letter w) (H_first w) (qof w) (firstOf w) y hrp hfr).symm

/-- **`PAL ∈ PEG` from tracking.** No `H_realize`-over-all-`y` obligation is
needed: `pal_in_peg_of_galil` consumes the *combined* existential, which is
exactly what `Tracking` provides. -/
theorem pal_in_peg_of_tracking {Q Γ : Type} [Fintype Q] [DecidableEq Q]
    [Fintype Γ] [DecidableEq Γ] {t B : ℕ} (hB : 0 < B)
    (M : StructuredMachine (Fin 2) Q Γ t B)
    (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ)
    (firstOf : List (Fin 2) → Fin 9) (delay : ℕ)
    (H_letter : ∀ w : List (Fin 2), (Pof w).onLetter = onLetterVM w)
    (H_first : ∀ w : List (Fin 2), (Pof w).leftFirst = leftFirstVM)
    (htrack : Tracking M Pof qof firstOf delay)
    (H_empty : M.SAccepts []) :
    RecognizedByTotalPEG PAL := by
  refine pal_in_peg_of_galil hB M Pof qof firstOf delay H_letter H_first ?_ H_empty
  intro w hw
  obtain ⟨y0, ⟨n, x, hx, hrun⟩, hrp0, hfr0, hacc0⟩ := htrack w hw
  exact ⟨n, x, y0, hx, hrun, hrp0, hfr0, hacc0⟩

/-- Fully packaged: tracking plus the two shared-predicate identifications and
the empty-word case give `PAL ∈ PEG`. -/
theorem pal_in_peg_of_tracking_exists {Q Γ : Type} [Fintype Q] [DecidableEq Q]
    [Fintype Γ] [DecidableEq Γ] {t B : ℕ} (hB : 0 < B) (delay : ℕ) :
    (∃ (M : StructuredMachine (Fin 2) Q Γ t B) (Pof : List (Fin 2) → Shared)
        (qof : List (Fin 2) → ℕ) (firstOf : List (Fin 2) → Fin 9),
      (∀ w : List (Fin 2), (Pof w).onLetter = onLetterVM w) ∧
      (∀ w : List (Fin 2), (Pof w).leftFirst = leftFirstVM) ∧
      Tracking M Pof qof firstOf delay ∧
      M.SAccepts []) →
    RecognizedByTotalPEG PAL := by
  rintro ⟨M, Pof, qof, firstOf, hl, hf, ht, he⟩
  exact pal_in_peg_of_tracking hB M Pof qof firstOf delay hl hf ht he

#print axioms Tracking
#print axioms saccepts_iff_pal_of_tracking
#print axioms H_realize_of_tracking
#print axioms pal_in_peg_of_tracking
#print axioms pal_in_peg_of_tracking_exists

end PalPeg.GalilRealizeOfTracking
