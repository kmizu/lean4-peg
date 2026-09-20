import PalPeg.GalilRunSkeleton

/-!
# A tick does not depend on the word beyond the on-letter test at its target

The shared frame `PofC centre place entry w` depends on the word only through `onLetterVM w`,
and a tick reads that test only at its target state, to refresh the output bit.  So a tick of the
frame of one word is a tick of the frame of another word as soon as the two tests agree at the
target.  This is what lets the machine that runs on `w` follow the canonical trace of an extension
of `w`: the two tests differ only where the right head stands on a letter beyond `w`.
-/

set_option autoImplicit false

namespace PalPeg.TickOnLetterCongr

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilRunSkeleton

variable {centre : GalilVM → Fin 3} {place : GalilVM → GalilScaffoldPlace.Place}
  {entry q delay : ℕ} {first : Fin 9} {w w' : List (Fin 2)}

/-- The output refresh of the frame of `w'` is that of the frame of `w` where the two on-letter
tests agree. -/
theorem refresh_of_onLetter_agree {s : GalilVM} {old o : Bool}
    (hagree : onLetterVM w' s ↔ onLetterVM w s)
    (hrefresh : refresh (galilFrameS (PofC centre place entry w') q first) s old o) :
    refresh (galilFrameS (PofC centre place entry w) q first) s old o :=
  ⟨fun hon => hrefresh.1 (hagree.mpr hon), fun hnot => hrefresh.2 (fun hon => hnot (hagree.mp hon))⟩

/-- **A tick of the frame of `w'` is a tick of the frame of `w`** when the on-letter tests of the
two words agree at the target. -/
theorem tick_of_onLetter_agree {x y : State GalilVM}
    (htick : Tick (galilFrameS (PofC centre place entry w') q first) delay x y)
    (hagree : onLetterVM w' y.vm ↔ onLetterVM w y.vm) :
    Tick (galilFrameS (PofC centre place entry w) q first) delay x y := by
  cases htick
  case scan_match c s s' s'' o hm hready hclock hcompare hmatched hplace hrefresh =>
    exact Tick.scan_match c s s' s'' o hm hready hclock hcompare hmatched hplace
      (refresh_of_onLetter_agree hagree hrefresh)
  case shift_one c s s' hm hpos hstep => exact Tick.shift_one c s s' hm hpos hstep
  case shift_done c s o hm hpos hrefresh =>
    exact Tick.shift_done c s o hm hpos (refresh_of_onLetter_agree hagree hrefresh)
  case copy_one c s s' hm hpos hstep => exact Tick.copy_one c s s' hm hpos hstep
  case home_step c s s' hm hleft hstep => exact Tick.home_step c s s' hm hleft hstep
  case fpp_slice c s s' hm hstep => exact Tick.fpp_slice c s s' hm hstep
  case markEnd_step c s s' hm hend hstep => exact Tick.markEnd_step c s s' hm hend hstep
  case replayStart c s s' o hm hstep hkeep hrefresh =>
    exact Tick.replayStart c s s' o hm hstep hkeep
      (fun hpos => refresh_of_onLetter_agree hagree (hrefresh hpos))
  all_goals (constructor <;> assumption)

#print axioms tick_of_onLetter_agree

end PalPeg.TickOnLetterCongr
