import PalPeg.CloseoutTerminalN
import PalPeg.GalilLeafPos

/-!
# The terminal head bound is `hpos`, and `hpos` is the crossing split

`CloseoutTerminalN` left the terminal head bound
`position (afterCompare s3 vs3 vq3).right ≤ 2 * m - 1` open.  Measuring it:

* `afterCompare` puts the right head on `vs3.right = right s3.right`, so the
  bound is `position (right s3.right) ≤ 2 * m - 1` — **exactly** the `hpos`
  residue of `GalilLeafMismatch.hmismatch_of_residues`;
* `GalilLeafPos`'s header already shows `hpos` is **false as stated**
  (`not_hpos_of_report_place`: an entry at the extreme allowed place
  `position r.right = 2 * m - 1` lands the comparison on `2 * m`), and gives
  `hpos_of_segBudget` as the replacement, which asks for a *segment budget*
  `position r.right + es.count true ≤ 2 * m - 2`;
* `GalilOracleLeaves2.segment_of_invLPC` / `CloseoutReadyStage.segment_of_invLPCS`
  produce `SegReachedW ∧ SegEnd` and know nothing about `m`, so the budget is
  not available from them.

So the terminal head bound and `hpos` are **one obligation**, and its shape is
settled by the proved dichotomy `GalilLeafPos.hpos_or_reportPoint`:

```
position t.right ≤ 2*m-1 →
  position (right t.right) ≤ 2*m-1 ∨ ReportPointAt w m ⟨c', t⟩
```

— at every comparison either the head stays inside the checkpoint, or the state
*is* the report point at `m`, where the oracle takes its `ReachAtC2` branch
instead.  Iterating that along the segment is the missing step, and
`GalilOneFallback.watchSegE_right_position` makes it pure arithmetic on the
event list: the head advance is `es.count true`.  `headBound_iff_count` below
records that reduction, and `SegCrossSplit` names the split the iteration needs
— the *split* direction of `WatchSegE`, which the tree already has
(`GalilScaffoldTopWatchSegE.watchSegE_append`).

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutSegBudget

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOneFallback
open PalPeg.GalilFinalAssembly2 PalPeg.GalilLeafPos

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **The head bound is a bound on the segment's matched count.**
`GalilLeafPos.seg_right_place` turns the exit place into
`position r.right + es.count true`, so the whole obligation is arithmetic on
the event list. -/
theorem headBound_iff_count {w : List (Fin 2)} {m : ℕ} {c c' : Control} {r t : GalilVM}
    {es : List Bool} (hIC : InvLPC w c r)
    (hw : WatchSegE (PofC centre place entry w) q first 2048 es c r c' t) :
    position t.right ≤ 2 * m - 1 ↔ position r.right + es.count true ≤ 2 * m - 1 := by
  rw [seg_right_place centre place entry q first w hIC hw]

/-- **(NAMED) the crossing split.**  If the segment's matched count would take
the head past the checkpoint, the segment has a prefix that lands exactly on
it — and there, by `GalilLeafPos.reportPointAt_of_seg`, the state is the report
point at `m`, so the oracle reports instead of continuing.

The split itself is `GalilScaffoldTopWatchSegE.watchSegE_append`; what is named
here is the choice of prefix, i.e. that the count reaches the bound exactly. -/
def SegCrossSplit (w : List (Fin 2)) : Prop :=
  ∀ (m : ℕ) (c c' : Control) (r t : GalilVM) (es : List Bool),
    1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
    WatchSegE (PofC centre place entry w) q first 2048 es c r c' t →
    2 * m - 1 < position r.right + es.count true →
    ∃ (es1 es2 : List Bool) (c1 : Control) (t1 : GalilVM),
      es = es1 ++ es2 ∧
      WatchSegE (PofC centre place entry w) q first 2048 es1 c r c1 t1 ∧
      position r.right + es1.count true = 2 * m - 1

/-- **`hpos` from the split.**  Either the count stays inside the checkpoint —
and then `hpos_or_reportPoint`'s first branch applies — or the split gives the
prefix that lands on it, where the state is the report point. -/
theorem hpos_or_report_of_split {w : List (Fin 2)} (hsplit : SegCrossSplit centre place entry q first w)
    {m : ℕ} {c c' : Control} {r t : GalilVM} {es : List Bool}
    (hm1 : 1 ≤ m) (hmle : m ≤ w.length) (hIC : InvLPC w c r)
    (hrt : position r.right ≤ 2 * m - 1)
    (hw : WatchSegE (PofC centre place entry w) q first 2048 es c r c' t)
    (hs : SegReachedW centre place entry q first w c r c' t)
    (hnr : c'.replaying = false) (hav : canRight t.right) :
    position (right t.right) ≤ 2 * m - 1 ∨
      PalPeg.GalilReportPrefix.ReportPointAt w m ⟨c', t⟩ ∨
      ∃ (es1 es2 : List Bool) (c1 : Control) (t1 : GalilVM),
        es = es1 ++ es2 ∧
        WatchSegE (PofC centre place entry w) q first 2048 es1 c r c1 t1 ∧
        position r.right + es1.count true = 2 * m - 1 := by
  rcases Nat.lt_or_ge (2 * m - 1) (position r.right + es.count true) with hgt | hle
  · exact Or.inr (Or.inr (hsplit m c c' r t es hm1 hmle hIC hrt hw hgt))
  · rcases hpos_or_reportPoint centre place entry q first w m hm1 hmle hs hnr hav
      ((headBound_iff_count centre place entry q first hIC hw).mpr hle) with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)

end

#print axioms headBound_iff_count
#print axioms hpos_or_report_of_split

end PalPeg.CloseoutSegBudget
