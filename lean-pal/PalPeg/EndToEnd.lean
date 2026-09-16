import PalPeg.OnlineMachine
import PalPeg.MiddleBorder
import PalPeg.PrepDecompose

/-!
# End-to-end assembly of the online PAL recognizer (half-split schedule, `k = 8`)

This file plugs the concrete `borderMiddle` (GS border-job) middle implementation and
the concrete `prepDecompose` preprocessing implementation into the half-split online
machine of `PalPeg.OnlineMachine` (§7), instantiated at `k = 8`, and derives the
end-to-end correctness and cost bounds.
-/

namespace PalPeg

open MiddleBorder

/-- **End-to-end correctness** of the assembled half-split online machine at `k = 8`. -/
theorem endToEnd_correct
    (hdec : ∀ x : List (Fin 2), GSDecomp x 8 (decompose x 8).1 (decompose x 8).2.1
      (decompose x 8).2.2)
    (hOK : MiddleBorder.DecOK (Fin 2)) (w : List (Fin 2)) (n : ℕ) (hn : n ≤ w.length) :
    outputH (MiddleBorder.borderMiddle (Fin 2)) (prepDecompose 8) (w.take n) n
        (fullStateH (MiddleBorder.borderMiddle (Fin 2)) (prepDecompose 8) 8 w n) = true
      ↔ IsPal (w.take n) :=
  output_correctH (MiddleBorder.borderMiddle (Fin 2)) (prepDecompose 8) 8 w
    (MiddleBorder.borderMiddle_spec hOK) (prepDecompose_spec 8 (by omega) hdec)
    (by omega) hn

/-- **Corollary**: the assembled machine decides `PAL` at the end of the word. -/
theorem endToEnd_mem_PAL
    (hdec : ∀ x : List (Fin 2), GSDecomp x 8 (decompose x 8).1 (decompose x 8).2.1
      (decompose x 8).2.2)
    (hOK : MiddleBorder.DecOK (Fin 2)) (w : List (Fin 2)) :
    outputH (MiddleBorder.borderMiddle (Fin 2)) (prepDecompose 8) (w.take w.length)
        w.length
        (fullStateH (MiddleBorder.borderMiddle (Fin 2)) (prepDecompose 8) 8 w w.length)
        = true
      ↔ w ∈ PAL :=
  output_mem_PALH (MiddleBorder.borderMiddle_spec hOK) (prepDecompose_spec 8 (by omega) hdec)
    (by omega)

/-- **End-to-end per-round cost bound** of the assembled half-split online machine. -/
theorem endToEnd_round_cost
    (hdec : ∀ x : List (Fin 2), GSDecomp x 8 (decompose x 8).1 (decompose x 8).2.1
      (decompose x 8).2.2)
    (hOK : MiddleBorder.DecOK (Fin 2)) (w : List (Fin 2)) (n : ℕ) :
    roundCostH (MiddleBorder.borderMiddle (Fin 2)) (prepDecompose 8) 8 w n
      ≤ 3 * (gsRateInterleaved 8 + MiddleBorder.Cm + prepCp 8) :=
  round_cost_leH (MiddleBorder.borderMiddle (Fin 2)) (prepDecompose 8) 8 w
    (MiddleBorder.borderMiddle_spec hOK) (prepDecompose_spec 8 (by omega) hdec) n

/-- Numeric value of the constant per-round cost bound at `k = 8`. -/
example : 3 * (gsRateInterleaved 8 + MiddleBorder.Cm + prepCp 8) = 84846 := by
  decide

end PalPeg
