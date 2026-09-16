import PalPeg.GalilOracleLeaves2
import PalPeg.GalilSearchReadyInv

/-!
# The `hpres` leaf: `SearchReady` is *not* preserved, and what replaces it

`GalilOracleLeaves2.h_oracle_of_leaves'` leaves

```
hpres : ∀ w s a v, SearchReady (searchLens.get s) →
          searchEffect (PofC centreC placeC entry w) a s v → SearchReady v
```

open, with the note that `GalilSearchReadyInv.searchReady_step` proves it only
with the stage budget `ReadyRem` + `RunEntry`.  This file settles which of the
two possible readings is the right one.

## The verdict: (b).  `SearchReady` alone is refuted, not merely unproved.

§1 pins down exactly how much of the DP budget a bare `SearchReady` sees.  The
`as` of `DpSafeHere` is existentially quantified and unrelated to the events
the machine will actually be fed, so it may be padded with `false`s: the length
clause `3186*|w|+1683 ≤ 64*|bs ++ as|` is then free and the debt clause
`count true (bs ++ as) ≤ value s0.debt` collapses to `count true bs ≤
value s0.debt`, i.e. — since `SafeQuanta` pays one unit of debt per `true`
event (`safeQuanta_value`) — to

```
dpSafeHere_iff_nonneg :  DpSafeHere v.search v.dp  ↔  0 ≤ value v.search.debt
```
(at a fixed reachability witness).  Hence `searchReady_run_true_iff`: after a
`.run` quantum on the event `true` that stays in `.run`,

```
SearchReady v'  ↔  1 ≤ value v.search.debt,
```

and `SearchReady v` gives only `0 ≤ value v.search.debt`.  `hpres` is therefore
*false at every ready, chain-idle, run-mode state whose debt is exhausted and
whose next 64 calls do not finish the DP* (`hpres_false_at`), and such a state
is `SearchReady`: `searchReady_at_preload_zero_debt` builds one from nothing but
`SafeQuanta.nil`.  The missing unit of debt is exactly one stage event, i.e.
the stage ledger — it cannot be recovered from the state.

## What (b) looks like

§2 carries the budget.  `SearchReadyB v as` is `ReadyRem v as` (the `PrepInv`
half plus `DpSafeRem`, the budget re-indexed by the events of the stage still
ahead) together with `RunEntriesAll as v`, the ∀-closure of
`GalilSearchReadyInv.RunEntry` over those events and over every centre the
walker can present.  It is preserved by one `searchStep` (`searchReadyB_step`)
and by one chain-idle `searchEffect` (`searchReadyB_effect`), it implies
`SearchReady` (`searchReadyB_ready`), and at a stage restart its `ReadyRem` half
is free for *any* `as` (`searchReadyB_restarted`, from `searchReady_begin`: the
search sits in `.grow`).  The residual leaf moves from the false `hpres` to
`RunEntriesAll`, the `.run`-entry datum — the single named gap of
`GalilSearchReadyInv`, which `search_first_stage` / `search_later_stage`
establish for a calibrated stage.

## Why there is no `segment_of_invLPC'` here

`GalilOracleLeaves2.segment_of_invLPC` consumes `hpres` by handing it to
`GalilSegmentConstruct.watchSegE_construct`, whose signature hard-codes the
unindexed `SearchReady` and takes `hpres` ∀-quantified over *all* states and
*both* events.  By §1 that premise is unsatisfiable, so `segment_of_invLPC`
(and `h_oracle_of_leaves'` through it) is vacuous in that argument, and no
re-export can repair it: the event-indexed invariant has to be threaded through
`watchSegE_construct`'s fuel induction itself, which means re-proving that
theorem with `SearchReadyB` in place of `SearchReady`.  That is a separate file;
it is not a wrapper.
-/

set_option autoImplicit false

namespace PalPeg.GalilLeafPres

open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilBranchInvariants2
open PalPeg.GalilSearchReadyInv
open GalilScaffoldCounter (value dec dec_value Canonical)
open GalilScaffoldSearchRun (SafeCalls SafeQuanta advance)

/-! ## 1. How much of the budget a bare `SearchReady` sees -/

/-- Calls never touch the debt (`SafeCalls` mirror of `calls_debt`). -/
theorem safeCalls_debt {s t : GalilScaffoldSearchFinish.State}
    {x y : GalilScaffoldControl.Machine 12} {bs : List Bool}
    (h : SafeCalls s x bs t y) : t.debt = s.debt := by
  induction h with
  | nil => rfl
  | cons s x y z b bs t ht hsafe hr ih =>
      exact ih.trans (GalilScaffoldSearchRun.finish_debt _ _ _ _)

/-- A quantum run pays exactly one unit of debt per `true` event. -/
theorem safeQuanta_value {s t : GalilScaffoldSearchFinish.State}
    {x y : GalilScaffoldControl.Machine 12} {as : List Bool}
    (h : SafeQuanta s x as t y) :
    value t.debt = value s.debt - (as.count true : ℤ) := by
  induction h with
  | nil s x => simp
  | cons s u t x y z a as hm hq hr ih =>
      have hu : u.debt = s.debt := safeCalls_debt hq
      rw [ih]
      cases a with
      | false => simp [advance, hu]
      | true =>
          have : (advance true u).debt = dec u.debt := rfl
          rw [this, dec_value, hu, List.count_cons]
          simp
          omega

/-- **The bound `SearchReady` really carries.**  Every `DpSafeHere` witness
forces the debt at the current configuration to be non-negative. -/
theorem dpSafeHere_debt_nonneg {s : GalilScaffoldSearchFinish.State}
    {x : GalilScaffoldControl.Machine 12} (h : DpSafeHere s x) : 0 ≤ value s.debt := by
  obtain ⟨w, lower, s0, bs, as, hbud, hs0, hc, hb, hreach⟩ := h
  have hd : value s.debt = value s0.debt - (bs.count true : ℤ) := safeQuanta_value hreach
  have hsplit : ((bs ++ as).count true : ℤ) = (bs.count true : ℤ) + (as.count true : ℤ) := by
    simp [List.count_append]
  omega

/-- **…and it carries nothing more.**  At a fixed reachability witness the two
numeric clauses of `DpSafeHere` are equivalent to that bound: pad `as` with
`false`s. -/
theorem dpSafeHere_of_nonneg {w : List (Fin 3)} {lower : ℕ}
    {s0 s : GalilScaffoldSearchFinish.State} {bs : List Bool}
    {x : GalilScaffoldControl.Machine 12}
    (hs0 : s0.mode = .run) (hc : Canonical s0.debt)
    (hreach : DpReached w lower s0 bs s x) (hnn : 0 ≤ value s.debt) : DpSafeHere s x := by
  refine ⟨w, lower, s0, bs, List.replicate (3186*w.length+1683) false, ?_, hs0, hc, ?_, hreach⟩
  · have hlen : (bs ++ List.replicate (3186*w.length+1683) false).length
        = bs.length + (3186*w.length+1683) := by simp
    rw [hlen]
    omega
  · have hd : value s.debt = value s0.debt - (bs.count true : ℤ) := safeQuanta_value hreach
    have hzero : (List.replicate (3186*w.length+1683) false).count true = 0 := by
      simp [List.count_replicate]
    have hsplit : (bs ++ List.replicate (3186*w.length+1683) false).count true
        = bs.count true + (List.replicate (3186*w.length+1683) false).count true := by
      simp [List.count_append]
    rw [hsplit, hzero]
    omega

theorem dpSafeHere_iff_nonneg {w : List (Fin 3)} {lower : ℕ}
    {s0 s : GalilScaffoldSearchFinish.State} {bs : List Bool}
    {x : GalilScaffoldControl.Machine 12}
    (hs0 : s0.mode = .run) (hc : Canonical s0.debt) (hreach : DpReached w lower s0 bs s x) :
    DpSafeHere s x ↔ 0 ≤ value s.debt :=
  ⟨dpSafeHere_debt_nonneg, dpSafeHere_of_nonneg hs0 hc hreach⟩

/-- One `.run` quantum of `searchStep` on the event `a`. -/
theorem searchStep_run_value {center : GalilScaffoldPlace.Place} {a : Bool} {v v' : SearchVM}
    (hm : v.search.mode = .run) (h : searchStep center a v v') :
    value v'.search.debt = value v.search.debt - (if a then 1 else 0) := by
  unfold searchStep at h
  rw [hm] at h
  obtain ⟨hq, _, _⟩ := h
  have hv := safeQuanta_value hq
  cases a <;> simpa using hv

/-- A run-mode state with a negative debt is not `SearchReady`. -/
theorem not_searchReady_of_run_neg {v : SearchVM} (hm : v.search.mode = .run)
    (hneg : value v.search.debt < 0) : ¬ SearchReady v := by
  intro h
  have := dpSafeHere_debt_nonneg (h.2 hm)
  omega

/-- **The exact preservation law for a bare `SearchReady`.**  After a `.run`
quantum on the event `true` that stays in `.run`, readiness survives *iff* the
debt had a unit left — a stage-ledger fact, invisible to `SearchReady v`, which
only gives `0 ≤ value v.search.debt`. -/
theorem searchReady_run_true_iff {center : GalilScaffoldPlace.Place} {v v' : SearchVM}
    (hm : v.search.mode = .run) (hm' : v'.search.mode = .run)
    (hsr : SearchReady v) (h : searchStep center true v v') :
    SearchReady v' ↔ 1 ≤ value v.search.debt := by
  have hval : value v'.search.debt = value v.search.debt - 1 := by
    simpa using searchStep_run_value hm h
  constructor
  · intro h'
    have := dpSafeHere_debt_nonneg (h'.2 hm')
    omega
  · intro hpos
    obtain ⟨w, lower, s0, bs, as, _, hs0, hc, _, hreach⟩ := hsr.2 hm
    refine ⟨prepInv_of_notPrep (Or.inr (Or.inr (Or.inl hm'))), fun _ => ?_⟩
    have hstep : SafeQuanta v.search v.dp [true] v'.search v'.dp := by
      unfold searchStep at h
      rw [hm] at h
      exact h.1
    refine dpSafeHere_of_nonneg (bs := bs ++ [true]) hs0 hc (dpReached_step hreach hstep) ?_
    omega

/-- A state that is `SearchReady` with the debt already exhausted: the DP is at
its preload and no event has been charged yet.  (`s0.debt` is any canonical
zero counter; `GalilScaffoldCounter.reset` is one.) -/
theorem searchReady_at_preload_zero_debt (v : SearchVM) (w : List (Fin 3)) (lower : ℕ)
    (hm : v.search.mode = .run) (hc : Canonical v.search.debt)
    (hz : value v.search.debt = 0)
    (hdp : v.dp = ⟨GalilScaffoldPreload.initial w lower, false⟩) :
    SearchReady v := by
  refine ⟨prepInv_of_notPrep (Or.inr (Or.inr (Or.inl hm))), fun _ => ?_⟩
  refine dpSafeHere_of_nonneg (w := w) (lower := lower) (bs := []) hm hc ?_ (by omega)
  show SafeQuanta v.search ⟨GalilScaffoldPreload.initial w lower, false⟩ [] v.search v.dp
  rw [hdp]
  exact .nil _ _

/-- **`hpres` is refuted.**  At any ready, chain-idle, run-mode state whose debt
is exhausted and whose next quantum on a match does not finish the DP, the leaf
`hpres` of `GalilOracleLeaves2.h_oracle_of_leaves'` is contradictory. -/
theorem hpres_false_at (P : Shared)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) → searchEffect P a s v → SearchReady v)
    (s : GalilVM) (hidle : s.chain = ChainVM.idle)
    (hsr : SearchReady (searchLens.get s)) (hm : (searchLens.get s).search.mode = .run)
    (hz : value (searchLens.get s).search.debt = 0) (v : SearchVM)
    (hstep : searchStep (P.place s) true (searchLens.get s) v)
    (hm' : v.search.mode = .run) : False := by
  have hready : SearchReady v := hpres s true v hsr (Or.inl ⟨hidle, hstep⟩)
  have := (searchReady_run_true_iff hm hm' hsr hstep).1 hready
  omega

/-! ## 2. (b): carrying the stage budget -/

/-- The ∀-closure of `GalilSearchReadyInv.RunEntry` over the events of the stage
still ahead, and over every centre the walker can present.  This is the single
named gap: when the preparation hands control to the DP run, the machine handed
over is the preload of the stage window and the events still ahead pay for the
calibrated run budget. -/
def RunEntriesAll : List Bool → SearchVM → Prop
  | [], _ => True
  | a :: as, v =>
      ∀ (center : GalilScaffoldPlace.Place) (v' : SearchVM), searchStep center a v v' →
        RunEntry center a v v' as ∧ RunEntriesAll as v'

/-- `SearchReady` with the stage budget carried: the `PrepInv` half and the DP
budget re-indexed by the events still ahead, plus the `.run`-entry datum for
those events. -/
def SearchReadyB (v : SearchVM) (as : List Bool) : Prop :=
  ReadyRem v as ∧ RunEntriesAll as v

theorem searchReadyB_ready {v : SearchVM} {as : List Bool} (h : SearchReadyB v as) :
    SearchReady v :=
  searchReady_of_readyRem h.1

/-- **Preservation.**  One `searchStep` consumes one event of the stage. -/
theorem searchReadyB_step {center : GalilScaffoldPlace.Place} {a : Bool} {as : List Bool}
    {v v' : SearchVM} (hstep : searchStep center a v v') (h : SearchReadyB v (a :: as)) :
    SearchReadyB v' as := by
  obtain ⟨hrem, hE⟩ := h
  obtain ⟨hentry, hrest⟩ := hE center v' hstep
  exact ⟨searchReady_step center a as hstep hrem hentry, hrest⟩

/-- **Preservation through the scan tick.**  Inside a chain-idle segment the
search effect *is* the search step, so the same law applies verbatim — this is
the replacement for the false `hpres`. -/
theorem searchReadyB_effect (P : Shared) {a : Bool} {as : List Bool} {s : GalilVM}
    {v : SearchVM} (hidle : s.chain = ChainVM.idle)
    (h : SearchReadyB (searchLens.get s) (a :: as)) (he : searchEffect P a s v) :
    SearchReadyB v as := by
  rcases he with ⟨_, hs⟩ | ⟨hne, _⟩
  · exact searchReadyB_step hs h
  · exact absurd hidle hne

/-- **Boot.**  At a stage restart the search sits in `.grow`, so the `ReadyRem`
half is free for *any* remaining-event list; only `RunEntriesAll` survives. -/
theorem searchReadyB_restarted {raw : List (Fin 2)} {r : GalilVM} {Rad : ℕ}
    {last : GalilScaffoldCounter.Counter} (hR : Restarted raw r Rad last) (as : List Bool)
    (hE : RunEntriesAll as (searchLens.get r)) : SearchReadyB (searchLens.get r) as :=
  ⟨searchReady_restarted hR as, hE⟩

#print axioms safeCalls_debt
#print axioms safeQuanta_value
#print axioms dpSafeHere_debt_nonneg
#print axioms dpSafeHere_of_nonneg
#print axioms dpSafeHere_iff_nonneg
#print axioms searchStep_run_value
#print axioms not_searchReady_of_run_neg
#print axioms searchReady_run_true_iff
#print axioms searchReady_at_preload_zero_debt
#print axioms hpres_false_at
#print axioms searchReadyB_ready
#print axioms searchReadyB_step
#print axioms searchReadyB_effect
#print axioms searchReadyB_restarted

end PalPeg.GalilLeafPres
