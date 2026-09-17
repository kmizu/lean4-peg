import PalPeg.CloseoutPackRun28
import PalPeg.CloseoutPreload7

/-!
# The unrestricted place bound is false

`CloseoutPackRun28.walkerInOrigin_of_run` (and `bounded_step`, `:225`) carries a
hypothesis

```
hplace : ∀ u, (GalilScaffoldPlace.stream (place u)).length ≤ position u.right
```

quantified over **every** `GalilVM`, not over the reachable ones.  At the
concrete `place := placeC` (`GalilFinalAssembly2:320`) that is refutable: the
left side reads only the *centre* head and the right side only the *right*
head, and nothing in the type couples them.  Put the centre one letter in and
the right head at the origin and the bound fails.

So `hplace` is not an assumption one can discharge; it has to be restricted to
states reached along a run, where `position u.center ≤ position u.right` holds.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.CloseoutPlaceBound

open PalPeg.GalilFinalAssembly2
open PalPeg.GalilScaffoldChainInputSupply

/-- **The `∀ u` place bound is false at `placeC`.**  Given any state at all,
the state with the centre head one letter in and the right head at the origin
breaks it. -/
theorem hplace_false (u : GalilVM) :
    ¬ (∀ v : GalilVM,
        (GalilScaffoldPlace.stream (placeC v)).length ≤ position v.right) := by
  intro h
  have hbad := h { u with
    center := ⟨⟨some 0, [some 0], [], []⟩, true⟩,
    right := ⟨⟨none, [], [], []⟩, true⟩ }
  simp [placeC, lettersOf, GalilScaffoldPlace.stream, GalilScaffoldPlace.gaps,
    position] at hbad

/-- **The restricted place bound.**  On a state whose heads are in order
(`GalilTrailOrder.Order`), the centre's stream is no longer than the right
head's position.  `stream_length_le` bounds the stream by twice the letters at
and left of the centre, `position center` counts those cells, and `Order.cr`
puts the centre at or before the right head. -/
theorem hplace_of_order {u : GalilVM} (ho : PalPeg.GalilTrailOrder.Order u)
    (hlen : 2 * (placeC u).letters.length ≤ position u.center) :
    (GalilScaffoldPlace.stream (placeC u)).length ≤ position u.right :=
  le_trans (le_trans (PalPeg.CloseoutPreload7.stream_length_le _) hlen) ho.cr

#print axioms hplace_false
#print axioms hplace_of_order

end PalPeg.CloseoutPlaceBound
