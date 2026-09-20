import PalPeg.LocalSysConcrete
import PalPeg.HeadBehindRight

/-!
# What the starvation test says about the right head

`LocalSysConcrete.Starved` reads the abstraction of the local state, which on a tracked state is
the pre-loaded trace state truncated to the arrived letters.  If the state is not starved, its
right head can still move right after truncation, so the move uses no letter that has not
arrived: the right-head half of the lookahead of a scan tick has arrived.  The other three
readings of the test (the centre head, the left head, the left head moved once) give the same for
the heads a shift moves.
-/

set_option autoImplicit false

namespace PalPeg.LocalStarvedRight

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilThrottledRun (truncS truncVM truncPH usedPH usedVM SufVM)
open PalPeg.LocalReplayParked (Mirrored1 abs'')
open PalPeg.LocalSysConcrete (Starved Needy)

variable {P : ℕ}

/-- A head whose pending letters are a suffix of the word, and which can still move right after
truncation to the arrived letters, moves right within the arrived letters. -/
theorem usedPH_right_le_of_suffix {raw : List (Fin 2)} {j : ℕ}
    {head : GalilScaffoldInputHead.PlaceHead} (hsuffix : PalPeg.GalilThrottledRun.SufPH raw head)
    (hused : usedPH raw.length head ≤ j)
    (hcanRight : GalilScaffoldChainVerifier.canRight (truncPH (raw.length - j) head)) :
    usedPH raw.length (GalilScaffoldChainVerifier.right head) ≤ j := by
  obtain ⟨drop, hdrop⟩ := hsuffix
  refine PalPeg.HeadBehindRight.usedPH_right_le_of_canRight_trunc raw.length j _ ?_ hused hcanRight
  rw [hdrop, List.length_drop]
  omega

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
  exact usedPH_right_le_of_suffix hsuffix.2.2.1
    ((PalPeg.GalilTruncTick.usedVM_right raw (stOf k).vm).trans hused) hcanRight

#print axioms usedPH_right_le_of_notStarved

/-- **The heads a shift moves, of a tracked state that is not starved, move within the arrived
letters**: the centre head one place, the left head two places.  These are the other three
readings of the starvation test. -/
theorem usedPH_shiftHeads_le_of_notStarved {raw : List (Fin 2)} {stOf : ℕ → State GalilVM}
    {k j : ℕ} {m : Mirrored1 P} (hneedy : Needy raw stOf k j m.vm)
    (hnotStarved : ¬ Starved m.vm) (hsuffix : SufVM raw (stOf k).vm)
    (hused : usedVM raw (stOf k).vm ≤ j) :
    usedPH raw.length (GalilScaffoldChainVerifier.right (stOf k).vm.center) ≤ j ∧
      usedPH raw.length (GalilScaffoldChainVerifier.right
        (GalilScaffoldChainVerifier.right (stOf k).vm.left)) ≤ j := by
  have hvm : abs'' m.vm = truncVM (raw.length - j) (stOf k).vm := congrArg State.vm hneedy.2
  obtain ⟨hcanLeft, hcanCenter, -, hcanLeftTwice⟩ := Classical.not_not.mp hnotStarved
  rw [hvm] at hcanLeft hcanCenter hcanLeftTwice
  have hleftOnce := usedPH_right_le_of_suffix hsuffix.1
    ((PalPeg.GalilTruncTick.usedVM_left raw (stOf k).vm).trans hused) hcanLeft
  refine ⟨usedPH_right_le_of_suffix hsuffix.2.1
    ((PalPeg.GalilTruncTick.usedVM_center raw (stOf k).vm).trans hused) hcanCenter, ?_⟩
  have hcanLeftTwice' : GalilScaffoldChainVerifier.canRight
      (truncPH (raw.length - j) (GalilScaffoldChainVerifier.right (stOf k).vm.left)) := by
    rw [← PalPeg.GalilTruncTick.truncPH_right raw.length j _ hleftOnce]
    exact hcanLeftTwice
  exact usedPH_right_le_of_suffix (PalPeg.GalilTruncTick.sufPH_right hsuffix.1) hleftOnce
    hcanLeftTwice'

#print axioms usedPH_shiftHeads_le_of_notStarved

end PalPeg.LocalStarvedRight
