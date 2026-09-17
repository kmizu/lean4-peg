import PalPeg.CloseoutRoundSeg

/-!
# `hSP`'s residue is inside `hor`'s found-route leaf

`CloseoutRoundSeg` reduced `hSP` to two items: `RoundSeg` (one round's
projection) and the first round (`H_freshShift` / `H_fresh`).  Both are
**already stated** in the found-route family, inside one named leaf:

`CloseoutWatchRound5.ShiftRoundC` (marked *NAMED (open)*) packages, for a live
watch landing whose fuel is spent or whose guard already holds,

```
WatchSeg → terminal mismatch → shiftGuard → beginShift → ChainShiftRun →
  Entry raw org (toOnly (post-shift state) v) → Rounds … → ScanSeg … → break
```

i.e. exactly the first round's origin **and** the subsequent rounds.  So the
two walls — `hSP`'s round assembly and `hor`'s `hfound` family — are the same
named leaf, not two independent problems.

This file makes the link a theorem rather than a remark:

* `originAt_of_entry` — an `Entry` at a state *is* `OriginAt` there (the watch
  is unique, so no side condition);
* `originAt_of_rounds` — `Entry` plus a controller `Rounds` gives `OriginAt` at
  the end, by `rounds_lift` then `rounds_origin`.

Together with `CloseoutRoundSeg.round_of_originAt` that turns `ShiftRoundC`'s
`Entry` + `Rounds` into the round datum and the sweep witness at every round
start of the run.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutOriginRounds

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton
open PalPeg.GalilRoundPeriod PalPeg.CloseoutPackRun31 PalPeg.CloseoutPackRun37
open PalPeg.CloseoutOriginAt PalPeg.CloseoutRoundSeg

/-- **An `Entry` at a state is `OriginAt` there.**  The watching chain is
determined by the state, so the universal quantifier costs nothing. -/
theorem originAt_of_entry {w : List (Fin 2)} {o : ReadOrigin w} {s : GalilVM}
    {wch : GalilScaffoldChainWatch.State}
    (hch : s.chain = ChainVM.watch wch)
    (he : Entry w o (toOnly s wch))
    (hint : o.interior.length + 1 = periodLength wch)
    (hroom : o.radius + 2 ≤ o.center) : OriginAt w s := by
  intro wch2 hch2
  rw [hch] at hch2
  cases hch2
  exact ⟨o, he, hint, hroom⟩

/-- **`OriginAt` after `m` controller rounds.**  `rounds_lift` projects the
rounds and `rounds_origin` carries the origin; the coordinates grow by `m*h`,
so `roundScan_entry`'s side condition `radius + 2 ≤ center` is preserved. -/
theorem originAt_of_rounds {w : List (Fin 2)} {P : Shared} {q : ℕ} {first : Fin 9}
    {delay h m : ℕ} {c c' : Control} {s s' : GalilVM}
    {w0 : GalilScaffoldChainWatch.State} {o : ReadOrigin w}
    (hr : Rounds P q first delay h m c s c' s')
    (hp : s.periodOnly = true) (hs : s.chain = ChainVM.watch w0)
    (hz : zero w0.lag = true)
    (he : Entry w o (toOnly s w0)) (hint : o.interior.length + 1 = h)
    (hroom : o.radius + 2 ≤ o.center)
    (hpl : ∀ v : GalilScaffoldChainWatch.State, s'.chain = ChainVM.watch v →
      periodLength v = h) :
    OriginAt w s' := by
  obtain ⟨-, w', hw', -, -, hcr⟩ := rounds_lift P q first delay h hr w0 hp hs hz
  obtain ⟨o', he', -, hinterior, -, -, -, hcenter, hradius⟩ := rounds_origin hcr o hint he
  refine originAt_of_entry hw' he' ?_ ?_
  · rw [hinterior, hint, hpl w' hw']
  · rw [hcenter, hradius]; omega

/-- **The round datum and the sweep witness at the end of the rounds.**
`originAt_of_rounds` composed with `CloseoutOriginAt.round_of_originAt`: this is
what `ShiftRoundC`'s `Entry` + `Rounds` deliver. -/
theorem round_of_rounds {w : List (Fin 2)} {P : Shared} {q : ℕ} {first : Fin 9}
    {delay h m : ℕ} {c c' : Control} {s s' : GalilVM}
    {w0 w' : GalilScaffoldChainWatch.State} {o : ReadOrigin w}
    (hr : Rounds P q first delay h m c s c' s')
    (hp : s.periodOnly = true) (hs : s.chain = ChainVM.watch w0)
    (hz : zero w0.lag = true)
    (he : Entry w o (toOnly s w0)) (hint : o.interior.length + 1 = h)
    (hroom : o.radius + 2 ≤ o.center)
    (hpl : ∀ v : GalilScaffoldChainWatch.State, s'.chain = ChainVM.watch v →
      periodLength v = h)
    (hch' : s'.chain = ChainVM.watch w') :
    ∃ C R : ℕ, RoundScan w C R (periodLength w') 0 s' w' ∧
      ReadsInv w C R (periodLength w') 0 w' :=
  round_of_originAt (originAt_of_rounds hr hp hs hz he hint hroom hpl) hch'

#print axioms originAt_of_entry
#print axioms originAt_of_rounds
#print axioms round_of_rounds

end PalPeg.CloseoutOriginRounds
