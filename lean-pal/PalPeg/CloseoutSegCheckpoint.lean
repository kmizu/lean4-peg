import PalPeg.CloseoutSegPrefix
import PalPeg.CloseoutReadyStage

/-!
# The segment budget is free: construct the segment to the checkpoint

The last named fact behind the terminal head bound / `hpos` was the *segment
budget*.  Splitting an existing segment (`CloseoutSegPrefix`) gives the prefix,
but its landing then has to be re-equipped with `SegReached`'s eleven fields.

`CloseoutReadyStage.watchSegE_constructS` makes that unnecessary: it
**constructs** a `WatchSegE` of a *chosen* length `n` and hands back, at the
landing,

```
c'.mode = .scan ∧ 1 ≤ c'.clock ∧ t.chain = ChainVM.idle ∧
SearchReady (searchLens.get t) ∧ MInv raw c' t ∧
ScanInvariant raw (position t.center) r' t.left t.right ∧
(es.length = n ∨ SegEnd P c' t)
```

and `GalilOneFallback.watchSegE_right_position` gives
`position t.right = position s.right + es.count true`.  Since
`es.count true ≤ es.length`, choosing

```
n := 2 * m - 1 - position s.right
```

bounds the exit head by the checkpoint outright — **no budget hypothesis at
all**.  The other branch is `SegEnd`, which is where the oracle's `hends` /
`hended` leaves already take over.

`segment_to_checkpoint` below is exactly `hsegmentM`'s shape ("`SegReachedW`
together with `AtTarget m c' t ∨ SegEnd …`") with the target bound *derived*
rather than assumed, and `reportPointAt_of_seg` needs only three of the landing
facts it returns (`replaying`, `scan`, `minv`), all present.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutSegCheckpoint

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilBranchInvariants2
open PalPeg.GalilOracleDischarge PalPeg.GalilOneFallback
open PalPeg.CloseoutReadyStage PalPeg.GalilSegmentConstruct

/-- **The segment stops at the checkpoint, by construction.**  `n` is the exact
distance to the checkpoint, so the matched count — hence the head advance —
cannot exceed it. -/
theorem segment_to_checkpoint (raw : List (Fin 2)) (P : Shared)
    (hex : ∀ s, P.replayExhausted s = zero s.replay) (q : ℕ) (first : Fin 9)
    (hsearch : ∀ s' : GalilVM, SearchReady (searchLens.get s') → ∀ a : Bool,
      ∃ v, searchEffect P a s' v)
    (m : ℕ) (c : Control) (s : GalilVM) (r k : ℕ)
    (hm : c.mode = Mode.scan) (hclk : 1 ≤ c.clock) (hk : 2048 ≤ c.clock + k)
    (hidle : s.chain = ChainVM.idle)
    (hsr : ReadyPacedS (searchLens.get s) (2 * m - 1 - position s.right) k)
    (hM : MInv raw c s)
    (hi : ScanInvariant raw (position s.center) r s.left s.right)
    (hrt : position s.right ≤ 2 * m - 1) :
    ∃ (es : List Bool) (c' : Control) (t : GalilVM) (r' : ℕ),
      WatchSegE P q first 2048 es c s c' t ∧
      c'.mode = Mode.scan ∧ 1 ≤ c'.clock ∧ t.chain = ChainVM.idle ∧
      SearchReady (searchLens.get t) ∧ MInv raw c' t ∧
      ScanInvariant raw (position t.center) r' t.left t.right ∧
      (position t.right ≤ 2 * m - 1 ∨ SegEnd P c' t) := by
  obtain ⟨es, c', t, r', hw, hm', hclk', hidle', hsr', hM', hi', hend⟩ :=
    watchSegE_constructS raw P hex q first hsearch (readyIface_readyPacedS P)
      (2 * m - 1 - position s.right) c s r k hm hclk hk hidle hsr hM hi
  refine ⟨es, c', t, r', hw, hm', hclk', hidle', hsr', hM', hi', ?_⟩
  rcases hend with hlen | hse
  · left
    have hp := (watchSegE_right_position raw P q first 2048 hw hi).2
    have hle : es.count true ≤ es.length := List.count_le_length
    rw [hlen] at hle
    omega
  · exact Or.inr hse

#print axioms segment_to_checkpoint

end PalPeg.CloseoutSegCheckpoint
