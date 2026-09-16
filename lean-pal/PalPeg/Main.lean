import PalPeg.Existence
import PalPeg.ProgramMachine

/-!
# Glue: from a `StructuredMachine` recognizing `PAL` to `PAL ∈ PEG`

This file connects `PalPeg.Program.StructuredMachine` (the ergonomic,
program-notation layer for strictly real-time multi-tape machines defined in
`PalPeg/ProgramMachine.lean`) to the conditional existence theorems in
`PalPeg/Existence.lean`.

The remaining mathematical obligation of the whole `lean-pal` project is
*unconditional*: exhibit a concrete `StructuredMachine` `M` over some finite
control type `Q` and finite tape alphabet `Γ`, with `B` micro-steps per round,
such that `M.SAccepts w ↔ w ∈ PAL` for every input word `w`. Such an `M` is the
"tape realization" of the artifact's `OnlineMachine.output_correctH` (the
existence, at the level of an *idealized* online/systolic recognizer, of a
strictly real-time procedure for palindromes à la Galil 1978 / Slisenko 1973).
Once `M` and `hM : ∀ w, M.SAccepts w ↔ w ∈ PAL` are in hand, the two theorems
below discharge `PAL ∈ PEG` unconditionally, with no further work.
-/

set_option autoImplicit false

namespace PalPeg

open PegSeparation PalPeg.Program

/-- A `StructuredMachine` that recognizes exactly `PAL` witnesses
`RealTimeTM.RecognizedBy PAL`, via `StructuredMachine.structured_recognizedBy`
and rewriting `{ w | M.SAccepts w } = PAL` along `hM`. -/
theorem recognizedBy_of_structured {Q Γ : Type} [Fintype Q] [DecidableEq Q]
    [Fintype Γ] [DecidableEq Γ] {t B : ℕ} (hB : 0 < B)
    (M : StructuredMachine (Fin 2) Q Γ t B)
    (hM : ∀ w, M.SAccepts w ↔ w ∈ PAL) : RealTimeTM.RecognizedBy PAL := by
  have hSet : { w | M.SAccepts w } = PAL := Set.ext hM
  have h := M.structured_recognizedBy hB
  rwa [hSet] at h

/-- **Main corollary.** A `StructuredMachine` that recognizes exactly `PAL`
yields a total PEG that recognizes `PAL`, i.e. `PAL ∈ PEG`. Chains
`recognizedBy_of_structured` with `pal_recognizedByTotalPEG`. -/
theorem pal_in_peg_of_structured {Q Γ : Type} [Fintype Q] [DecidableEq Q]
    [Fintype Γ] [DecidableEq Γ] {t B : ℕ} (hB : 0 < B)
    (M : StructuredMachine (Fin 2) Q Γ t B)
    (hM : ∀ w, M.SAccepts w ↔ w ∈ PAL) : RecognizedByTotalPEG PAL :=
  pal_recognizedByTotalPEG (recognizedBy_of_structured hB M hM)

/-- Sanity check: the statement typechecks as an implication from the single
remaining hypothesis (existence of `M` with `hM`) to `PAL ∈ PEG`, with no
other assumptions. -/
example {Q Γ : Type} [Fintype Q] [DecidableEq Q] [Fintype Γ] [DecidableEq Γ]
    {t B : ℕ} (hB : 0 < B) :
    (∃ (M : StructuredMachine (Fin 2) Q Γ t B), ∀ w, M.SAccepts w ↔ w ∈ PAL) →
      RecognizedByTotalPEG PAL := by
  rintro ⟨M, hM⟩
  exact pal_in_peg_of_structured hB M hM

end PalPeg
