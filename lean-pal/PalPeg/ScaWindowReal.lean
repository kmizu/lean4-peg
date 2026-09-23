import PalPeg.ScaWorkerEnc
import PalPeg.ScaWindowPlumbing

/-!
# `PAL ∈ PEG` from the real workers' promises

The window route with the real (table-compiled, Scala-derived) matcher and flag workers and their
stack encodings. What remains are three statements about the real workers' runs: the matcher's
answer at the answering tick (`hmatch`), the flag workers' promise (`FlagsContract`), and no
worker fault (`hworkers`).
-/
set_option autoImplicit false
namespace PalPeg.ScaWindowReal
open PalPeg.ScaWindowPal PalPeg.ScaWindowInstance PalPeg.ScaWindowPlumbing

theorem pal_in_peg_of_real_promises
    (hmatch : ∀ w : List (Fin 2), 4 ≤ w.length →
      (matcherOps.output ((run matcherOps flagsOps matcherInit flagsInit w).matchers
          (ScaWindowSchedule.idx (Nat.log 2 w.length))) = true ↔
        occursAt (w.take (stageOf w.length)).reverse w))
    (hflags : ∀ W, FlagsContract matcherOps flagsOps matcherInit flagsInit W)
    (hworkers : ∀ (w : List (Fin 2)) (i : Fin 2),
      matcherOps.faulted ((run matcherOps flagsOps matcherInit flagsInit w).matchers i) = false ∧
        flagsOps.faulted ((run matcherOps flagsOps matcherInit flagsInit w).flags i) = false) :
    PegSeparation.RecognizedByTotalPEG PalPeg.PAL :=
  ScaWorkerEnc.pal_in_peg_of_real_workers hmatch (hmiddle_of_contract hflags)
    (hclean_of_contract hflags) hworkers

/-- info: 'PalPeg.ScaWindowReal.pal_in_peg_of_real_promises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pal_in_peg_of_real_promises

end PalPeg.ScaWindowReal
