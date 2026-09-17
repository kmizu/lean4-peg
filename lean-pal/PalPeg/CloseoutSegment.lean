import PalPeg.CloseoutOracleBridge
import PalPeg.GalilSpanCounter
import PalPeg.GalilScaffoldTopRounds

/-!
# The one obligation everything reduces to: run segmentation

Twenty turns of measurement keep landing on the same shape.  Here it is once,
named, with the consequences that are already theorems.

## Why `SpanRep` is not a tick invariant

`GalilScaffoldTopSearch:48` / `:53`:

```
afterCompare  s vs vq = {… with radius := inc s.radius, length := inc (inc s.length), …}
afterMismatch s vs vq = {… with radius := inc s.radius}
```

so a *matched* comparison bumps both and keeps `value length = 2 * value radius + 1`
(`GalilSpanCounter.spanRep_afterCompare`), while a **mismatched** one bumps only
the radius and breaks it.  `beginShiftVM` then bumps `length` twice and restores
it — so `SpanRep` survives the `scan_shift` tick as a composite but fails at the
intermediate `afterMismatch`, and after `scan_fallback` it stays broken until
the fallback cycle resets both counters (`spanRep_of_fallback`).

`SpanRep` is therefore an invariant of **scan states**, and the transport
lemmas in `GalilSpanCounter` are all segment-shaped:
`spanRep_scanSeg`, `spanRep_watchSeg`, `spanRep_watchSegE`, `spanRep_shift`,
`spanRep_rounds`, `spanRep_restart`, `spanRep_of_init`, `spanRep_of_fallback`.

## The obligation

`ScanToScan` says every scan-to-scan run decomposes the way the round
machinery expects: a `ScanSeg` of matched comparisons, then `m` complete
`Rounds`.  Everything the closeout still needs is downstream of it:

| needs | via |
|---|---|
| `SpanRep` at oracle landings (half of `hor`'s `InvLPS` lift) | `spanRep_of_scanToScan` below |
| `RoundSeg` (`hSP`'s round boundary) | `rounds_lift` then `rounds_origin` |
| `H_freshShift` / `H_fresh` | `GalilScaffoldTopFirstRound.first_round` on the first segment |
| `hor`'s found leaves `hfound` / `hfoundBg` / `hfoundReplay` | `CloseoutWatchRound5.ShiftRoundC`, which is `WatchSeg` + terminal + shift + `Rounds` + `ScanSeg` |

So the remaining independent walls are **`ScanToScan`** (this), **`hC`**
(`H_realizeLIMW'`, the local machine), and the part of `hpack` that touches
model defect (e) (`marks` / `hwin`, the free fallback landing place).

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutSegment

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilInvPlus3

/-- **(NAMED) run segmentation.**  Every scan-to-scan sound run is a `ScanSeg`
of matched comparisons followed by `m` complete rounds. -/
def ScanToScan (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) : Prop :=
  ∀ (k : ℕ) (c c' : Control) (s s' : GalilVM),
    StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, s⟩ ⟨c', s'⟩ →
    c.mode = Mode.scan → c'.mode = Mode.scan →
    ∃ (n h m : ℕ) (cm : Control) (sm : GalilVM),
      ScanSeg P q first 2048 n c s cm sm ∧
      Rounds P q first 2048 h m cm sm c' s'

/-- **`SpanRep` travels a segmented run.**  `GalilSpanCounter.spanRep_scanSeg`
then `spanRep_rounds`; both are already proved. -/
theorem spanRep_of_scanToScan {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    (hseg : ScanToScan P q first raw)
    {k : ℕ} {c c' : Control} {s s' : GalilVM}
    (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, s⟩ ⟨c', s'⟩)
    (hm : c.mode = Mode.scan) (hm' : c'.mode = Mode.scan)
    (hs : SpanRep s) : SpanRep s' := by
  obtain ⟨n, h, m, cm, sm, hsc, hr⟩ := hseg k c c' s s' hst hm hm'
  exact spanRep_rounds P q first 2048 h hr (spanRep_scanSeg P q first 2048 hsc hs)

/-- **The `InvLPS` landing lift from the segmentation and the `Inv` half.**
`GalilInvPlus3.invLPS_of_landed` needs `CopyPack` at the origin (which the
`InvLPS` origin carries), `Inv` at the landing, and `SpanRep` at the landing —
and the last is now `spanRep_of_scanToScan`. -/
theorem invLPS_of_landing {centre : GalilVM → Fin 3}
    {place : GalilVM → GalilScaffoldPlace.Place} {entry q : ℕ} {first : Fin 9}
    {raw : List (Fin 2)} {c cT : Control} {r sT : GalilVM} {k : ℕ}
    (hO : InvLPS (PofC centre place entry raw) q first raw c r)
    (hs : SpanRep r)
    (hseg : ScanToScan (PofC centre place entry raw) q first raw)
    (hst : StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048
      (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
    (hm : c.mode = Mode.scan) (hm' : cT.mode = Mode.scan)
    (hInv : Inv raw cT sT) :
    InvLPS (PofC centre place entry raw) q first raw cT sT :=
  invLPS_of_landed centre place entry q first (x := ⟨c, r⟩) hO.1.1.2 hst hInv
    (spanRep_of_scanToScan hseg hst hm hm' hs)

#print axioms spanRep_of_scanToScan
#print axioms invLPS_of_landing

end PalPeg.CloseoutSegment
