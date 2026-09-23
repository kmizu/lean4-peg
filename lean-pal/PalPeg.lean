import PalPeg.PalInPegFinal
import PalPeg.Axioms

/-!
# `PalPeg` — `PAL ∈ PEG` in Lean 4

The root of the package. The main theorem:

```lean
theorem PalPeg.PalInPeg.unconditional : PegSeparation.RecognizedByTotalPEG PalPeg.PAL
```

(`PalPeg/PalInPegFinal.lean`), and its corollary refuting Loff–Moreira–Reis (2020) Conjecture 7,
`PalPeg.PalInPeg.evenPal_in_peg`. `PalPeg/Axioms.lean` pins the axioms of the main results with
`#guard_msgs`: only `propext`, `Classical.choice`, `Quot.sound`.

See `README.md` (English, with a Japanese version `README.ja.md`) and `PROOF.md` for a guided
tour of the proof.
-/
