import PalPeg.CloseoutStageTrans
import PalPeg.CloseoutWatchRound2
import PalPeg.CloseoutPackRun31

/-!
# `MatchTickC` is false at a terminal match — and the map it redraws

## The map correction

Earlier entries called run segmentation (`ScanToScan` / `RoundSeg`) *the* wall.
Reading `CloseoutWatchRound9`'s header shows the construction is **already
there, unconditionally and with no `sorry`**:

| item | content |
|---|---|
| `scanSeg_countdown` | the post-shift idle interval as a `ScanSeg` |
| `scanSeg_matchStep` | one matched comparison as a `ScanSeg` of length 1, *constructed* |
| `scanRun_construct` / `scanRun_of_distance` | the fuel induction in `ScanSeg` form |
| `segRun_terminal` | a live post-shift landing reaches a `SegEndS` landing by one `ScanSeg` |
| `roundOne_of_segRun` | **one `Rounds` step built from the run** |

So the segmentation is not the wall.  Its residue, per that header, is exactly

1. `CloseoutWatchRound.RoundDataC` — discharged by
   `CloseoutWatchRound2.roundStepC_of_align` down to `MatchTickC`;
2. `CloseoutWatchRound9.ShiftAtMismatchC` — input-dependent, open;
3. one terminal head bound `position (afterCompare s3 vs3 vq3).right ≤ 2*m - 1`.

## And (1) is false

`CloseoutWatchRound2.MatchTickC` (`:136`) asks, at **every** matched comparison
with a watching chain and an available right head, for `zero lag` *and*
`Good w1`.  It carries **no non-terminal premise**.  But
`CloseoutPackRun31.not_good_of_terminal_match` proves the opposite
under exactly those premises plus `singlePositive s.cycle = true`: at the
terminal of a round a matched comparison **breaks** the chain, so `Good` fails.
(`RoundScan.good_of_match` is the companion and does carry
`hend : singlePositive v.cycle = false`.)

`matchTickC_false_at_terminal` below is that contradiction, machine-checked.

Consequence: `RoundDataC` cannot be closed through `MatchTickC` as stated.  The
reformulation is the one `GalilRoundPeriod` already prescribes — premise the
round's non-terminality, and route the terminal match to
`RoundScan.break_of_match` instead, which is where the machine actually goes.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutMatchTickRefute

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRoundPeriod

/-- **`MatchTickC` contradicts a terminal matched comparison.**  Directly from
`CloseoutPackRun31.not_good_of_terminal_match`: the round's terminal match breaks the
chain, while `MatchTickC` claims it is `Good`. -/
theorem matchTickC_false_at_terminal {raw : List (Fin 2)} {C R h used : ℕ} {s : GalilVM}
    {w0 : GalilScaffoldChainWatch.State}
    (hI : RoundScan raw C R h used s w0)
    (hch : s.chain = ChainVM.watch w0)
    (hav : canRight s.right)
    (hend : singlePositive s.cycle = true)
    (hmatch : read (GalilScaffoldInputHead.left s.left) = read (right s.right))
    (hM : PalPeg.CloseoutWatchRound2.MatchTickC) : False :=
  PalPeg.CloseoutPackRun31.not_good_of_terminal_match hI hav hend hmatch
    (hM s w0 hch hav hmatch).2

#print axioms matchTickC_false_at_terminal

end PalPeg.CloseoutMatchTickRefute
