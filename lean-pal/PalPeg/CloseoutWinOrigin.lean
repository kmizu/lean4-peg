import PalPeg.CloseoutPackRun25
import PalPeg.CloseoutSpanTick

/-!
# `WindowInOrigin` from `WalkerInOrigin` plus the walker pin

`CloseoutPackRun17.marks_steps`'s last side input is

```
hwin : ∀ m z, Steps … m x z → z.ctl.mode = Mode.copy → WindowInOrigin z.vm
```

with `WindowInOrigin s := (stream s.fpp.walker).length ≤ position s.right`
(`CloseoutPackRun17:62`) and
`WalkerInOrigin s := (stream s.walker).length ≤ position s.right`
(`CloseoutPackRun25:53`) — the same bound on two different walkers.

`CloseoutPackRun25.windowInOrigin_of_fair` bridges them at a `scan → copy`
landing using `Fair.fallbackPlace`, and reading `GalilTickFair.Fair` shows that
clause says exactly

```
fallbackPlace : x.ctl.mode = Mode.scan → y.ctl.mode = Mode.copy →
  y.vm.fpp.walker = y.vm.walker
```

i.e. **the two walkers agree at the landing**.  That is a statement about the
landing state alone, so it does not need `Fair` as a hypothesis — it can be a
field of a run-carried bundle, like every other single-state property in
`CloseoutChainPack`.

`WalkerPin` below is that agreement, and `windowInOrigin_of_pin` is the bridge
with `Fair` replaced by it.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.CloseoutWinOrigin

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead
open PalPeg.CloseoutPackRun17 PalPeg.CloseoutPackRun25

/-- **(NAMED) `WalkerPin`**: the FPP walker and the search walker agree.  This is
the content of `Fair.fallbackPlace` at a `scan → copy` landing, as a property of
the landing state by itself. -/
def WalkerPin (s : GalilVM) : Prop := s.fpp.walker = s.walker

/-- **`WindowInOrigin` from `WalkerInOrigin` and the pin.**  `windowInOrigin_of_fair`
(`CloseoutPackRun25:56`) with `Fair` replaced by the single-state pin. -/
theorem windowInOrigin_of_pin {s : GalilVM} (hp : WalkerPin s)
    (hw : WalkerInOrigin s) : WindowInOrigin s := by
  unfold WindowInOrigin WalkerPin at *
  rw [hp]
  exact hw

/-- The pin is what `Fair.fallbackPlace` gives, so the old bridge factors
through it. -/
theorem pin_of_fair {entry delay : ℕ} {x y : State GalilVM}
    (hf : PalPeg.GalilTickFair.Fair entry delay x y)
    (hm : x.ctl.mode = Mode.scan) (hm' : y.ctl.mode = Mode.copy) : WalkerPin y.vm :=
  hf.fallbackPlace hm hm'

#print axioms windowInOrigin_of_pin
#print axioms pin_of_fair

end PalPeg.CloseoutWinOrigin
