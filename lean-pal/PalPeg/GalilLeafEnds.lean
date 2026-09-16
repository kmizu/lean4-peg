import PalPeg.GalilOracleLeaves2

/-!
# The fuel leaf `hends` of `GalilOracleLeaves2.h_oracle_of_leaves'`

`hends` asks for a *computable* segment length after which the chain-idle
phase is over: a number `n` such that **every** `WatchSegE` run of exactly `n`
events out of an `InvLPC` state lands in `SegEnd`.

The bound is the right head's own fuel.  Give the head the rank

```
headRank p = 2 * (p.head.right.length + p.head.incoming.length) + (if p.gap then 0 else 1)
```

— one unit per half step of `GalilScaffoldChainVerifier.right`, which
alternates a gap step (`gap = false ↦ true`, stack untouched) with a letter
step (`gap = true ↦ false`, one cell popped off the right stack or the
incoming FIFO).  Then `headRank p = 0` is exactly `¬ canRight p`, and
`headRank (right p) + 1 = headRank p` whenever `canRight p` (`rank_right`).

Now read the seven `WatchSegE` constructors as a descent of
`headRank s.right * delay + c.clock`:

* `count`/`countR` need `1 < c.clock` and decrement the clock, leaving the
  head alone;
* the three match constructors need `c.clock = 1` and `canRight s.right`, and
  step the head once while resetting the clock to `delay` — so the measure
  falls from `(R+1) * delay + 1` to `R * delay + delay`, again by one;
* `wait` needs `¬ canRight s.right`, and an exhausted head never comes back
  (`exhausted_persists`): every other constructor demands `canRight`, and both
  `wait` and `countR` tick the head through `background`, which is a frame.

So a run longer than the measure has run the head dry
(`exhausted_of_long`), and `SegEnd.ended` closes the leaf with

```
n := headRank r.right * 2048 + c.clock
```

which `hends_C` reads off an `InvLPC` state (`1 ≤ c.clock` is its scan mode
clause, exactly as in `GalilOracleLeaves2.segment_of_invLPC`).

Note that the other four `SegEnd` exits are never needed: the claim is not
that the run *must* stop at this length, only that a run of this length can
only end with the input exhausted.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.GalilLeafEnds

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilSegmentConstruct
open PalPeg.GalilFinalAssembly2

/-! ## 1. The rank of the right head -/

/-- Half steps of `GalilScaffoldChainVerifier.right` left in the right head:
two per cell still to be read (stack or incoming FIFO), plus one for a pending
gap step. -/
def headRank (p : PlaceHead) : ℕ :=
  2 * (p.head.right.length + p.head.incoming.length) + (if p.gap then 0 else 1)

/-- A movable right head has positive rank, and moving it spends exactly one
unit: the gap step keeps the cells and clears the `+1`, the letter step pops a
cell and re-arms the `+1`. -/
theorem rank_right (p : PlaceHead) (h : canRight p) :
    headRank (right p) + 1 = headRank p := by
  rcases p with ⟨⟨f, ls, rs, qs⟩, g⟩
  cases g with
  | false => simp [headRank, right]
  | true =>
    cases rs with
    | cons a rs' =>
      simp [headRank, right, headRight, GalilScaffoldInputTrace.moveRight]
      omega
    | nil =>
      cases qs with
      | nil => simp [canRight] at h
      | cons b qs' =>
        simp [headRank, right, headRight, GalilScaffoldInputTrace.moveRight]
        omega

/-! ## 2. An exhausted right head stays exhausted -/

/-- Once `canRight` fails the segment can only `wait`/`countR`/`stop`, and all
three leave the right head alone. -/
theorem exhausted_persists (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {es : List Bool}
    {c c' : Control} {s t : GalilVM} (h : WatchSegE P q first delay es c s c' t) :
    ¬ canRight s.right → ¬ canRight t.right := by
  induction h with
  | stop c s => exact id
  | wait c s s' hm hr hn hb _ ih =>
    intro h0; exact ih (by rw [(background_frame P q first hb).2.1]; exact h0)
  | count c s s' hm hr ha hc hb _ ih => intro h0; exact absurd ha h0
  | «match» c s vs vq o hm hr ha hc hne hcmp hmt hq ho _ ih => intro h0; exact absurd ha h0
  | matchIdle c s vs vq o hm hr ha hc hidle hl hrr hvs hmt hq hnf ho _ ih =>
    intro h0; exact absurd ha h0
  | countR c s s' hm hr hc hidle hb _ ih =>
    intro h0; exact ih (by rw [(background_frame P q first hb).2.1]; exact h0)
  | matchIdleR c s vs vq o hm hr hc ha hidle hl hrr hvs hmt hq hnf ho _ ih =>
    intro h0; exact absurd ha h0

/-! ## 3. The descent -/

/-- **The fuel bound.**  A segment of more than `headRank s.right * delay +
c.clock` events out of a scan state with a running clock has exhausted the
right head. -/
theorem exhausted_of_long (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (hd : 1 ≤ delay)
    {es : List Bool} {c c' : Control} {s t : GalilVM}
    (h : WatchSegE P q first delay es c s c' t) :
    1 ≤ c.clock → headRank s.right * delay + c.clock ≤ es.length → ¬ canRight t.right := by
  induction h with
  | stop c s =>
    intro h1 h2
    simp only [List.length_nil] at h2
    omega
  | wait c s s' hm hr hn hb rest ih =>
    intro _ _
    exact exhausted_persists P q first delay rest
      (by rw [(background_frame P q first hb).2.1]; exact hn)
  | count c s s' hm hr ha hc hb rest ih =>
    intro h1 h2
    simp only [List.length_cons] at h2
    have hrr : s'.right = s.right := (background_frame P q first hb).2.1
    refine ih (by dsimp only; omega) ?_
    dsimp only
    rw [hrr]
    omega
  | «match» c s vs vq o hm hr ha hc hne hcmp hmt hq ho rest ih =>
    intro h1 h2
    simp only [List.length_cons] at h2
    have hmatch : read (left s.left) = read (right s.right) := by
      obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp
      rw [scanLens.get_set] at hl0 hr0
      have hmp := matched_parts P q first hmt
      rw [hl0, hr0] at hmp; exact hmp
    have hvr : vs.right = right s.right := (compare_parts P q first hcmp hmatch).2.1
    have hrank : headRank (afterCompare s vs vq).right + 1 = headRank s.right := by
      rw [afterCompare_right, hvr]; exact rank_right s.right ha
    have hexp : headRank s.right * delay
        = headRank (afterCompare s vs vq).right * delay + delay := by
      rw [← hrank, Nat.add_mul, Nat.one_mul]
    refine ih (by dsimp only; exact hd) ?_
    dsimp only
    omega
  | matchIdle c s vs vq o hm hr ha hc hidle hl hrr hvs hmt hq hnf ho rest ih =>
    intro h1 h2
    simp only [List.length_cons] at h2
    have hrank : headRank (afterCompare s vs vq).right + 1 = headRank s.right := by
      rw [afterCompare_right, hrr]; exact rank_right s.right ha
    have hexp : headRank s.right * delay
        = headRank (afterCompare s vs vq).right * delay + delay := by
      rw [← hrank, Nat.add_mul, Nat.one_mul]
    refine ih (by dsimp only; exact hd) ?_
    dsimp only
    omega
  | countR c s s' hm hr hc hidle hb rest ih =>
    intro h1 h2
    simp only [List.length_cons] at h2
    have hrr : s'.right = s.right := (background_frame P q first hb).2.1
    refine ih (by dsimp only; omega) ?_
    dsimp only
    rw [hrr]
    omega
  | matchIdleR c s vs vq o hm hr hc ha hidle hl hrr hvs hmt hq hnf ho rest ih =>
    intro h1 h2
    simp only [List.length_cons] at h2
    have hrank : headRank (replayDec true (afterCompare s vs vq)).right + 1
        = headRank s.right := by
      rw [replayDec_right, afterCompare_right, hrr]; exact rank_right s.right ha
    have hexp : headRank s.right * delay
        = headRank (replayDec true (afterCompare s vs vq)).right * delay + delay := by
      rw [← hrank, Nat.add_mul, Nat.one_mul]
    refine ih (by dsimp only; exact hd) ?_
    dsimp only
    omega

/-! ## 4. The leaf -/

/-- **`hends`, generic form.**  At any scan state with a running clock the
length `headRank s.right * delay + c.clock` forces `SegEnd` — by exhaustion. -/
theorem hends_of_clock (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (hd : 1 ≤ delay)
    (c : Control) (s : GalilVM) (hc : 1 ≤ c.clock) :
    ∃ n : ℕ, ∀ (es : List Bool) (c' : Control) (t : GalilVM),
      WatchSegE P q first delay es c s c' t → es.length = n → SegEnd P c' t := by
  refine ⟨headRank s.right * delay + c.clock, fun es c' t hseg hlen => ?_⟩
  exact .ended (exhausted_of_long P q first delay hd hseg hc (by rw [hlen]))

/-- **`hends`, closed.**  The fourth residual leaf of
`GalilOracleLeaves2.h_oracle_of_leaves'`.  `1 ≤ c.clock` is read off `InvLPC`
exactly as in `segment_of_invLPC`. -/
theorem hends_C (entry q : ℕ) (first : Fin 9) :
    ∀ (w : List (Fin 2)) (c : Control) (r : GalilVM), InvLPC w c r →
      ∃ n : ℕ, ∀ (es : List Bool) (c' : Control) (t : GalilVM),
        WatchSegE (PofC centreC placeC entry w) q first 2048 es c r c' t →
        es.length = n → SegEnd (PofC centreC placeC entry w) c' t := by
  intro w c r hIC
  have hIP : InvLP w c r := hIC.1.1
  have hI : InvS w c r := hIP.1.1
  have hclk : 1 ≤ c.clock := by
    rcases hI with h | ⟨k, h⟩
    · rw [h.mode.2.2]; omega
    · rw [h.mode.2.2]; omega
  exact hends_of_clock _ q first 2048 (by norm_num) c r hclk

#print axioms rank_right
#print axioms exhausted_persists
#print axioms exhausted_of_long
#print axioms hends_of_clock
#print axioms hends_C

end PalPeg.GalilLeafEnds
