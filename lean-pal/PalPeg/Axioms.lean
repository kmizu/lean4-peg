import PalPeg.PalInPegFinal

/-!
# Axiom audit

`#guard_msgs in #print axioms` pins the axioms of the main results: only the three standard axioms
of Lean/Mathlib (`propext`, `Classical.choice`, `Quot.sound`). A new `axiom`, a `sorry` or a
`native_decide` anywhere below these theorems breaks the build here. The package declares no
`axiom`.
-/

/-- info: 'PalPeg.PalInPeg.unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.PalInPeg.unconditional

/-- info: 'PalPeg.PalInPeg.evenPal_in_peg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.PalInPeg.evenPal_in_peg

/-- info: 'PalPeg.ScaWindowFast.pal_in_peg_of_fast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.ScaWindowFast.pal_in_peg_of_fast

/-- info: 'PalPeg.ScaWindowReal.pal_in_peg_of_real_promises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.ScaWindowReal.pal_in_peg_of_real_promises

/-- info: 'PalPeg.pal_recognizedByTotalPEG_of_sca' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.pal_recognizedByTotalPEG_of_sca

/-- info: 'PalPeg.pal_in_peg_of_realTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.pal_in_peg_of_realTime
