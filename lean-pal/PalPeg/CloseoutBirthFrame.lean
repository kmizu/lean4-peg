import PalPeg.GalilRunSkeleton

/-!
# `hbirth` at the concrete shared record

The `M-periodOnly` fix wraps every chain-birth transition in
`afterBirth born` (`GalilScaffoldTopSearch:77`), which clears `periodOnly` and
resets the `cycle` counter.  `LocalTick1.tickL1_abs` therefore needs the side
condition that the three `Shared` predicates it reads are blind to that change.
For an abstract `Shared` the three fields are opaque functions and the condition
is not provable; at the concrete `PofC` it is, because

* `onLetterVM raw s` reads only `position s.right`;
* `leftFirstVM s` reads only `position s.left`;
* `replayExhaustedVM s` reads only `s.replay`,

and `afterBirth` touches none of `left`, `right`, `replay`.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.CloseoutBirthFrame

open PalPeg.GalilRunSkeleton
open PalPeg.GalilScaffoldChainInputSupply

/-- **`hbirth` is a theorem at `PofC`.**  Exactly the hypothesis
`LocalTick1.tickL1_abs` and `LocalReplayParked.tickL1_abs''_nonreplay` take. -/
theorem hbirth_PofC (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ) (w : List (Fin 2))
    (bb : Bool) (s : GalilVM) :
    ((PofC centre place entry w).onLetter (afterBirth bb s)
        ↔ (PofC centre place entry w).onLetter s) ∧
    ((PofC centre place entry w).leftFirst (afterBirth bb s)
        ↔ (PofC centre place entry w).leftFirst s) ∧
    (PofC centre place entry w).replayExhausted (afterBirth bb s)
      = (PofC centre place entry w).replayExhausted s := by
  refine ⟨?_, ?_, ?_⟩
  · show onLetterVM w (afterBirth bb s) ↔ onLetterVM w s
    unfold onLetterVM
    rw [afterBirth_right]
  · show leftFirstVM (afterBirth bb s) ↔ leftFirstVM s
    unfold leftFirstVM
    rw [afterBirth_left]
  · show replayExhaustedVM (afterBirth bb s) = replayExhaustedVM s
    unfold replayExhaustedVM
    rw [afterBirth_replay]

#print axioms hbirth_PofC

end PalPeg.CloseoutBirthFrame
