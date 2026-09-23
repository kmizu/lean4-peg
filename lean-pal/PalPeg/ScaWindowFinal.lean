import PalPeg.ScaWindowEncodeTick
import PalPeg.ScaWindowPlumbing

/-!
# `PAL ∈ PEG` from the workers' promises

The top of the window route: the stack encodings of the two worker kinds, the matcher's
answer at the answering tick (`hmatch`), the flag workers' promise (`FlagsContract`), and no
worker fault.
-/
set_option autoImplicit false
namespace PalPeg.ScaWindowFinal
open PalPeg.ScaWindowPal PalPeg.ScaWindowEncode PalPeg.ScaWindowPlumbing

theorem pal_in_peg_of_promises {Wm Wf Γm Γf Cm Cf : Type} [Inhabited Γm] [Inhabited Γf]
    [Finite Γm] [Finite Γf] [Finite Cm] [Finite Cf] {Km Kf D : ℕ}
    {mOps : WorkerOps Wm} {fOps : WorkerOps Wf}
    (mE : WorkerEnc Wm mOps Γm Cm Km D) (fE : WorkerEnc Wf fOps Γf Cf Kf D) (hD : 1 ≤ D)
    (m0 : Wm) (f0 : Wf) (cm0 : Cm) (cf0 : Cf)
    (hm0 : mE.Rep m0 cm0 fun _ => []) (hf0 : fE.Rep f0 cf0 fun _ => [])
    (hmatch : ∀ w : List (Fin 2), 4 ≤ w.length →
      (mOps.output ((run mOps fOps m0 f0 w).matchers
          (ScaWindowSchedule.idx (Nat.log 2 w.length))) = true ↔
        occursAt (w.take (stageOf w.length)).reverse w))
    (hflags : ∀ W, FlagsContract mOps fOps m0 f0 W)
    (hworkers : ∀ (w : List (Fin 2)) (i : Fin 2),
      mOps.faulted ((run mOps fOps m0 f0 w).matchers i) = false ∧
        fOps.faulted ((run mOps fOps m0 f0 w).flags i) = false) :
    PegSeparation.RecognizedByTotalPEG PalPeg.PAL :=
  pal_in_peg_of_workers mE fE hD m0 f0 cm0 cf0 hm0 hf0 hmatch (hmiddle_of_contract hflags)
    (hclean_of_contract hflags) hworkers

/-- info: 'PalPeg.ScaWindowFinal.pal_in_peg_of_promises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pal_in_peg_of_promises

end PalPeg.ScaWindowFinal
