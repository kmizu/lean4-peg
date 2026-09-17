import PalPeg.CloseoutRoundBundle

/-!
# `OriginAt`: carry the read origin, not the numbers

`CloseoutRoundBundle` left two leaves, `H_readsShift` and `H_freshShift`.
Measuring `H_readsShift` turned up the structural reason both are there.

`CloseoutPackRun37.ReadsInv` states the sweep witness as an **equality**

```
w0.machine.control = GalilScaffoldChainSweep.run o.shifted.machine.control extra
```

but `chainShiftOne` (`GalilScaffoldChainInputSupply:1481`) decrements
`distance`, `boundary` and `last`, so the equality is destroyed by the shift
phase — only the weaker `Offset` (same period tape and `broken`, counters off
by a constant) survives, which is exactly what `ReadOrigin.offset` records.

The development already has the right carrier, one level up:

| lemma | file | content |
|---|---|---|
| `Entry raw o s` | `GalilScaffoldChainReadOrigin:976` | the origin's data at a round start, including `machine : s.watch.machine = o.shifted.machine` |
| `rounds_origin` | `GalilScaffoldChainReadOrigin:1010` | `Entry raw o s → CompareRounds h s m s' → ∃ o', Entry raw o' s' ∧ o'.center = o.center + m*h ∧ o'.radius = o.radius + m*h` |
| `roundScan_entry` | `GalilRoundPeriod:327` | `Entry → RoundScan raw o.center o.radius h 0` |
| `rounds_lift` | `GalilScaffoldTopRounds:65` | a controller `Rounds` projects to `CompareRounds` |

So the origin travels **per round**, not per tick, and at `m = 1`
`rounds_origin` lands exactly on the next round's coordinates
`(C + h, R + h)` — the pair `roundScan_of_shiftInv` produces numerically.

`OriginAt` below is that carrier as a single-state field, and it yields both
halves the bundle needs at a round start: the `RoundScan` **and** the
`ReadsInv`.  Re-basing the bundle on it is what removes `H_readsShift`; the
round-boundary step is `rounds_origin`, and the only genuinely missing piece is
then the *first* round (`H_freshShift` / `H_fresh`, whose content is
`GalilScaffoldTopFirstRound.first_round`).

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutOriginAt

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton
open PalPeg.GalilRoundPeriod PalPeg.CloseoutPackRun31 PalPeg.CloseoutPackRun37

/-- **(NAMED) the read origin at a state.**  Every watching chain is at a round
start of some read origin whose half period matches, and whose mismatching
place is not the very first cell (`roundScan_entry`'s one arithmetic side
condition). -/
def OriginAt (w : List (Fin 2)) (s : GalilVM) : Prop :=
  ∀ wch : GalilScaffoldChainWatch.State, s.chain = ChainVM.watch wch →
    ∃ o : ReadOrigin w, Entry w o (toOnly s wch) ∧
      o.interior.length + 1 = periodLength wch ∧ o.radius + 2 ≤ o.center

/-- **`ReadsInv` at a round start, from `Entry`.**  `Entry.machine` says the
watch's machine *is* the origin's shifted machine, so the sweep witness holds
with the empty continuation. -/
theorem readsInv_of_entry {w : List (Fin 2)} {o : ReadOrigin w}
    {s : GalilVM} {wch : GalilScaffoldChainWatch.State}
    (he : Entry w o (toOnly s wch)) (hint : o.interior.length + 1 = periodLength wch) :
    ReadsInv w o.center o.radius (periodLength wch) 0 wch :=
  ⟨o, [], rfl, rfl, hint, rfl, by
    have h := he.machine
    show wch.machine.control = GalilScaffoldChainSweep.run o.shifted.machine.control []
    show wch.machine.control = o.shifted.machine.control
    exact congrArg (fun m => m.control) h⟩

/-- **Both halves at a round start.**  `OriginAt` gives the round datum and the
sweep witness together, with the same `(C, R)`. -/
theorem round_of_originAt {w : List (Fin 2)} {s : GalilVM}
    {wch : GalilScaffoldChainWatch.State}
    (hO : OriginAt w s) (hch : s.chain = ChainVM.watch wch) :
    ∃ C R : ℕ, RoundScan w C R (periodLength wch) 0 s wch ∧
      ReadsInv w C R (periodLength wch) 0 wch := by
  obtain ⟨o, he, hint, hroom⟩ := hO wch hch
  exact ⟨o.center, o.radius,
    roundScan_entry o (periodLength wch) hint hch he hroom,
    readsInv_of_entry he hint⟩

/-- **The round-boundary step.**  `rounds_origin` at `m = 1` moves the origin
to the next round, whose coordinates are `(C + h, R + h)` — exactly the pair
`roundScan_of_shiftInv` produces. -/
theorem originAt_next {w : List (Fin 2)} {h : ℕ} {o : ReadOrigin w} {s s' : GalilVM}
    {wch wch' : GalilScaffoldChainWatch.State}
    (he : Entry w o (toOnly s wch)) (hint : o.interior.length + 1 = h)
    (hroom : o.radius + 2 ≤ o.center) (hh' : periodLength wch' = h)
    (hcr : CompareRounds h (toOnly s wch) 1 (toOnly s' wch')) :
    ∃ o' : ReadOrigin w, Entry w o' (toOnly s' wch') ∧
      o'.interior.length + 1 = periodLength wch' ∧ o'.radius + 2 ≤ o'.center ∧
      o'.center = o.center + h ∧ o'.radius = o.radius + h := by
  obtain ⟨o', he', -, hinterior, -, -, -, hcenter, hradius⟩ :=
    rounds_origin hcr o hint he
  refine ⟨o', he', ?_, ?_, ?_, ?_⟩
  · rw [hinterior, hint, hh']
  · rw [hcenter, hradius]; omega
  · rw [hcenter]; omega
  · rw [hradius]; omega

#print axioms readsInv_of_entry
#print axioms round_of_originAt
#print axioms originAt_next

end PalPeg.CloseoutOriginAt
