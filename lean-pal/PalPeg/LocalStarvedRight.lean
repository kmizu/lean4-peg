import PalPeg.LocalSysConcrete
import PalPeg.HeadBehindRight

/-!
# What the starvation test says about the right head

`LocalSysConcrete.Starved` reads the abstraction of the local state, which on a tracked state is
the pre-loaded trace state truncated to the arrived letters.  If the state is not starved, its
right head can still move right after truncation, so the move uses no letter that has not
arrived: the right-head half of the lookahead of a scan tick has arrived.
-/

set_option autoImplicit false

namespace PalPeg.LocalStarvedRight

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilThrottledRun (truncS truncVM truncPH usedPH usedVM SufVM)
open PalPeg.LocalReplayParked (Mirrored1 abs'')
open PalPeg.LocalSysConcrete (Starved Needy)

variable {P : ℕ}

/-- **The right head of a tracked state that is not starved looks ahead within the arrived
letters.** -/
theorem usedPH_right_le_of_notStarved {raw : List (Fin 2)} {stOf : ℕ → State GalilVM}
    {k j : ℕ} {m : Mirrored1 P} (hneedy : Needy raw stOf k j m.vm)
    (hnotStarved : ¬ Starved m.vm) (hsuffix : SufVM raw (stOf k).vm)
    (hused : usedVM raw (stOf k).vm ≤ j) :
    usedPH raw.length (GalilScaffoldChainVerifier.right (stOf k).vm.right) ≤ j := by
  have hvm : abs'' m.vm = truncVM (raw.length - j) (stOf k).vm := congrArg State.vm hneedy.2
  have hcanRight : GalilScaffoldChainVerifier.canRight (abs'' m.vm).right :=
    (Classical.not_not.mp hnotStarved).2.2.1
  rw [hvm] at hcanRight
  obtain ⟨drop, hdrop⟩ := hsuffix.2.2.1
  refine PalPeg.HeadBehindRight.usedPH_right_le_of_canRight_trunc raw.length j _ ?_
    ((PalPeg.GalilTruncTick.usedVM_right raw (stOf k).vm).trans hused) hcanRight
  rw [hdrop, List.length_drop]
  omega

#print axioms usedPH_right_le_of_notStarved

end PalPeg.LocalStarvedRight
