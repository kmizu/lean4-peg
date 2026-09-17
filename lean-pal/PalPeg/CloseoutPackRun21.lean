import PalPeg.CloseoutPackRun16

/-!
# `CloseoutPackRun21`: the two `LPackM`-at-scan-entry contracts of `BigResid6`

`CloseoutPackRun11.BigResid6` asks, at the two ticks that *enter* `scan`
from outside, for the guarded left pack `CloseoutPackRun10.LPackM` at the
landing:

* `rInitPackM` — the `init → scan` boot tick;
* `rReplayPackM` — the `replayStart → scan` fallback landing.

## §1 `rInitPackM` is vacuous over `BigPack2M`

`BigPack2M` carries `AuxPack`, whose `FrontPack` component has the field
`notInit : c.mode ≠ Mode.init` (`GalilFrontMono.FrontPack`).  So a
`BigPack2M` state in `Mode.init` does not exist, and the contract holds
by `absurd` (`rInitPackM_of_pack`).  This is the same reason
`CloseoutPackRun4` found every `LPack` field vacuous at the boot state: the
run pack is only *installed* by the `init` tick (`inv_init`), never carried
across it.  Nothing about `initVM`'s free components (`periodOnly`, `walker`,
`GalilTickDet`) enters.

## §2 `rReplayPackM` reduces to the centre head at `replayStart`

`replayStartVM` (`GalilScaffoldTopReplay`) fixes *all three heads* of the
landing to the source centre: `t.left = t.center = t.right = s.center`.  Both
fields of `LPackM` at the landing are therefore statements about
`s.center` alone:

* `lrepM` (strict, since the landing mode is `scan`) is
  `Represents s.center.head w ∧ s.center.head.focus ≠ none`;
* `scanGeom` (read only when `replayPos t = false`) is `ScanInvariant` at
  radius `0` with all heads at `s.center`, i.e. `scan_initial` applied to the
  same pair.

Neither `periodOnly` nor `walker` occurs, so the contract is proved for
*every* `replayStart` witness; `Fair` (`GalilTickFair`) is not needed.

The pair itself is **not in `BigPack2M`**.  At `Mode.replayStart` the pack
knows `FrontPack.rewind` (`RewindEq`: `Sane s.center` and
`position C + r = position R`), `RewindPhase` (`position C + r ≤ 2·arrived C`),
and `LPackM.lrepM` for the *left* head only (`replayStart` is not `StrictAt`).
`Sane` is `gap = true ∨ 0 < left.length`, which neither represents `w` nor
places the focus.  So the single named hypothesis is

```
H_centreReplay : ∀ x, BigPack2M … x → x.ctl.mode = Mode.replayStart →
  GalilInvPlus2.CentreRep w x.vm
```

(`CentreRep raw s := Represents s.center.head raw ∧ s.center.head.focus ≠ none`,
the centre half of `GalilInvPlus2`'s `InvScan` branch).  The field that should
carry it is `FrontPack.rewind`'s `Sane s.center` conjunct, strengthened to
`CentreRep w s` at `rewind ∨ replayStart`; along a run it is what
`GalilFoundLandingL`/`GalilInvPlus2` establish at the fallback landing
(`hcenR`), and `CentreLive` already records its positional shadow
`0 < position C` for the paired rewind.

## Honest status

Standard axioms only; unconditional `PAL ∈ PEG` remains open.
`rInitPackM_of_pack` is unconditional; `rReplayPackM_of_pack` is conditional
on `H_centreReplay`.
-/
set_option autoImplicit false

namespace PalPeg.CloseoutPackRun21

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldInputHead GalilScaffoldCounter
open PalPeg.GalilRunSkeleton PalPeg.GalilFrontMono
open PalPeg.CloseoutPackRun10 PalPeg.CloseoutPackRun11

section Entry
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-! ## 1. `rInitPackM` -/

/-- **`BigPack2M` never holds in `Mode.init`** (`FrontPack.notInit`). -/
theorem bigPack2M_not_init {w : List (Fin 2)} {x : State GalilVM}
    (hx : BigPack2M centre place entry q first w x) : x.ctl.mode ≠ Mode.init :=
  hx.aux.front.notInit

/-- **`rInitPackM` over `BigPack2M`, unconditionally.** -/
theorem rInitPackM_of_pack {w : List (Fin 2)} :
    ∀ x : State GalilVM, BigPack2M centre place entry q first w x →
      x.ctl.mode = Mode.init → ∀ t : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).init x.vm t →
      LPackM w {x.ctl with mode := Mode.scan, output := true} t :=
  fun _ hx hm _ _ => absurd hm (bigPack2M_not_init centre place entry q first hx)

/-! ## 2. `rReplayPackM` -/

/-- The three heads of a `replayStart` landing all sit on the source centre. -/
theorem replayStart_heads {w : List (Fin 2)} {s t : GalilVM}
    (h : (galilFrameS (PofC centre place entry w) q first).replayStart s t) :
    t.left = s.center ∧ t.center = s.center ∧ t.right = s.center := by
  obtain ⟨-, hr, hl, hc, -⟩ := h
  exact ⟨hl, hc, hr⟩

/-- **`LPackM` at a `replayStart` landing, from the centre head alone.**  The
controller record `c'` is arbitrary: `lrepM` is given in its strict form
(so the landing mode need not be named), and the guard of `scanGeom` is
discharged by the radius-`0` invariant either way. -/
theorem lpackM_replayStart_of_centreRep {w : List (Fin 2)} {c' : Control} {s t : GalilVM}
    (hcen : PalPeg.GalilInvPlus2.CentreRep w s)
    (h : (galilFrameS (PofC centre place entry w) q first).replayStart s t) :
    LPackM w c' t := by
  obtain ⟨hl, hc, hr⟩ := replayStart_heads centre place entry q first h
  obtain ⟨hrep, hpres⟩ := hcen
  refine ⟨fun _ => ⟨by rw [hl]; exact hrep, fun _ => by rw [hl]; exact hpres⟩, ?_⟩
  intro _ _
  refine ⟨0, ?_⟩
  rw [hl, hc, hr]
  exact scan_initial w s.center hrep hpres

/-- **(NAMED) the one missing fact:** the centre head is represented and
present at every `replayStart` state of the pack. -/
def H_centreReplay (w : List (Fin 2)) : Prop :=
  ∀ x : State GalilVM, BigPack2M centre place entry q first w x →
    x.ctl.mode = Mode.replayStart → PalPeg.GalilInvPlus2.CentreRep w x.vm

/-- **`rReplayPackM` over `BigPack2M`, under `H_centreReplay`.**  Holds for
every `replayStart` witness (`periodOnly`/`walker` free), no `Fair` needed. -/
theorem rReplayPackM_of_pack {w : List (Fin 2)}
    (hcen : H_centreReplay centre place entry q first w) :
    ∀ x : State GalilVM, BigPack2M centre place entry q first w x →
      x.ctl.mode = Mode.replayStart → ∀ (t : GalilVM) (o : Bool),
      (galilFrameS (PofC centre place entry w) q first).replayStart x.vm t →
      LPackM w {x.ctl with mode := Mode.scan, clock := 2048, output := o, replaying := (galilFrameS (PofC centre place entry w) q first).replayPos t} t :=
  fun x hx hm _ _ h =>
    lpackM_replayStart_of_centreRep centre place entry q first (hcen x hx hm) h

end Entry

#print axioms bigPack2M_not_init
#print axioms rInitPackM_of_pack
#print axioms replayStart_heads
#print axioms lpackM_replayStart_of_centreRep
#print axioms rReplayPackM_of_pack

end PalPeg.CloseoutPackRun21
