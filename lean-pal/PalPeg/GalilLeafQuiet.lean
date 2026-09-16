import PalPeg.GalilOracleLeaves2
import PalPeg.GalilReplaySegment

/-!
# The `hquiet` leaf of `GalilOracleLeaves2.h_oracle_of_leaves'` is **false**

The leaf asks for

```
∀ w : List (Fin 2), PalPeg.GalilReplaySegment.SearchQuiet (PofC centreC placeC entry w)
```

with

```
def SearchQuiet (P : Shared) : Prop :=
  ∀ (s : GalilVM) (a : Bool) (v : SearchVM), SearchReady (searchLens.get s) →
    searchEffect P a s v → v.search.mode ≠ .found
```

The quantifier `∀ s : GalilVM` is unrestricted, so it ranges over states whose
search *already* reads `.found`.  On such a state the offending constructor is
the stutter branch of `searchStep`,

```
  match v.search.mode with
  | .idle | .found | .missed => v' = v      -- PalPeg/GalilScaffoldTopSearch.lean:93
```

which is a legal `searchEffect` through its idle-chain disjunct
(`GalilScaffoldTopSearch.lean:119`), and `SearchReady` is *vacuous* at mode
`.found`: `PrepInv v.toPrep` only constrains the four preparation modes and
`SearchVM.toPrep` copies `v.search.mode` verbatim, while the `DpSafeHere`
clause is guarded by `v.search.mode = .run`.  So `SearchQuiet P` implies that
*no* `GalilVM` at all carries a found search (`searchQuiet_forces_never_found`),
i.e. it asserts the FPP never reports — for every `P`, including every
`PofC centreC placeC entry w`.  `not_searchQuiet_PofC` refutes it outright from
an explicit witness VM.  (The second disjunct of `searchEffect`,
`s.chain ≠ .idle ∧ vq = searchLens.get s`, refutes it just as well.)

## The weakest variant the use sites need

`SearchQuiet` is used at exactly two places, both inside one replay round of
`PalPeg.GalilReplaySegment`:

* `countR_run` — `hquiet s false v hsr hv`, feeding `idle_background_exists`;
* `match_round` — `hquiet s true vq hsr hq`, as the `hnf` of the comparison.

At both, the caller already owns `c.mode = .scan`, `c.replaying = true`,
`s.chain = ChainVM.idle` and `SearchReady (searchLens.get s)`.  `SearchQuiet'`
below keeps those, and turns the conclusion into a *preservation* statement by
adding the not-found premise that the stutter destroys.  It is implied by
`SearchQuiet` (`quiet'_of_quiet`), it is not refutable by the stutter, and it
is exactly the ledger's claim — the FPP cannot finish a stage inside the
`≤ 4δ` ticks of a replay — in its weakest usable form; it is *not* discharged
here.  `countR_step_notFound` and `match_call_notFound` are the two call sites
rewritten against it: the first also returns the not-found premise at the
successor state, which is what lets `countR_run`'s induction thread the new
premise alongside `SearchReady`/`hpres`.
-/

set_option autoImplicit false

namespace PalPeg.GalilLeafQuiet

open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilBranchInvariants2
  PalPeg.GalilSegmentConstruct PalPeg.GalilFinalAssembly2 PalPeg.GalilRunSkeleton
open GalilScaffoldTop GalilScaffoldController
open PalPeg.GalilReplaySegment (SearchQuiet)

/-! ## `SearchReady` is vacuous at `.found` -/

/-- A search state that already reads `.found` is `SearchReady`: `PrepInv`
constrains only `.lower`/`.lowerHome`/`.copy`/`.home` (and
`SearchVM.toPrep` copies the mode), and the `DpSafeHere` clause is guarded by
`.run`. -/
theorem searchReady_of_found {v : SearchVM}
    (h : v.search.mode = GalilScaffoldSearchFinish.Mode.found) : SearchReady v := by
  have hm : v.toPrep.mode = GalilScaffoldSearchFinish.Mode.found := h
  refine ⟨⟨fun hx => ?_, fun hx => ?_, fun hx => ?_, fun hx => ?_⟩, fun hx => ?_⟩
  · exact absurd (hm.symm.trans hx) (by decide)
  · exact absurd (hm.symm.trans hx) (by decide)
  · exact absurd (hm.symm.trans hx) (by decide)
  · exact absurd (hm.symm.trans hx) (by decide)
  · exact absurd (h.symm.trans hx) (by decide)

/-- The stutter of an already-found search is a `searchEffect` on an idle
chain: the `.found` branch of `searchStep` is `v' = v`. -/
theorem searchEffect_found_stutter (P : Shared) (a : Bool) {s : GalilVM}
    (hidle : s.chain = ChainVM.idle)
    (h : (searchLens.get s).search.mode = GalilScaffoldSearchFinish.Mode.found) :
    searchEffect P a s (searchLens.get s) := by
  refine Or.inl ⟨hidle, ?_⟩
  unfold searchStep
  rw [h]

/-- **`SearchQuiet` asserts that no `GalilVM` whatsoever carries a found
search.**  This is the exact content of the leaf, for every `P`. -/
theorem searchQuiet_forces_never_found (P : Shared) (h : SearchQuiet P) (s : GalilVM) :
    s.search.mode ≠ GalilScaffoldSearchFinish.Mode.found := by
  intro hs
  have hs' : ((searchLens.get ({s with chain := ChainVM.idle} : GalilVM)).search.mode)
      = GalilScaffoldSearchFinish.Mode.found := hs
  exact h _ false _ (searchReady_of_found hs')
    (searchEffect_found_stutter P false rfl hs') hs'

/-! ## An explicit witness VM, and the refutation -/

def zeroCounter : GalilScaffoldCounter.Counter := GalilScaffoldCounter.reset
def zeroPlace : GalilScaffoldPlace.Place := ⟨[], false⟩
def zeroPlaceHead : GalilScaffoldInputHead.PlaceHead := ⟨⟨none, [], [], []⟩, false⟩
def zeroMachine (n : ℕ) : GalilScaffoldControl.Machine n :=
  ⟨⟨0, fun _ => GalilScaffoldTape.reset⟩, true⟩
def zeroFpp : FppControl.State := ⟨.run, zeroMachine 9, zeroCounter, zeroPlace, false⟩

/-- A `GalilVM` with an idle chain and a search that already reads `.found`. -/
def foundVM : GalilVM :=
  { left := zeroPlaceHead, center := zeroPlaceHead, right := zeroPlaceHead
    chain := ChainVM.idle
    cycle := zeroCounter, remaining := zeroCounter, radius := zeroCounter
    length := zeroCounter, replay := zeroCounter
    fpp := zeroFpp
    search := ⟨.found, false, zeroCounter, zeroCounter, zeroCounter, 0⟩
    dp := zeroMachine 12, lower := zeroCounter, periodOnly := false, walker := zeroPlace }

theorem foundVM_mode : foundVM.search.mode = GalilScaffoldSearchFinish.Mode.found := rfl

/-- **The leaf is false, for every `P`.** -/
theorem not_searchQuiet (P : Shared) : ¬ SearchQuiet P :=
  fun h => searchQuiet_forces_never_found P h foundVM foundVM_mode

/-- **The leaf of `h_oracle_of_leaves'` itself is false.** -/
theorem not_searchQuiet_PofC (entry : ℕ) :
    ¬ (∀ w : List (Fin 2), SearchQuiet (PofC centreC placeC entry w)) :=
  fun h => not_searchQuiet _ (h [])

/-! ## The weakest variant the two use sites need -/

/-- Quietness scoped to one replay round (`scan`, `replaying`, idle chain) and
in preservation form.  Still a ledger obligation; not discharged here. -/
def SearchQuiet' (P : Shared) : Prop :=
  ∀ (c : Control) (s : GalilVM) (a : Bool) (v : SearchVM),
    c.mode = Mode.scan → c.replaying = true → s.chain = ChainVM.idle →
    SearchReady (searchLens.get s) →
    (searchLens.get s).search.mode ≠ GalilScaffoldSearchFinish.Mode.found →
    searchEffect P a s v → v.search.mode ≠ GalilScaffoldSearchFinish.Mode.found

/-- `SearchQuiet'` is genuinely weaker. -/
theorem quiet'_of_quiet (P : Shared) (h : SearchQuiet P) : SearchQuiet' P :=
  fun _ s a v _ _ _ hsr _ he => h s a v hsr he

/-- **`countR_run`'s use site under the variant.**  The background tick of
`idle_background_exists` goes through, and the not-found premise is available
again at the successor state (`searchLens.get s' = v`), so `countR_run`'s
induction threads it exactly like `SearchReady`/`hpres`. -/
theorem countR_step_notFound (P : Shared) (q : ℕ) (first : Fin 9)
    (hq : SearchQuiet' P) (c : Control) (s : GalilVM) (v : SearchVM)
    (hm : c.mode = Mode.scan) (hr : c.replaying = true) (hidle : s.chain = ChainVM.idle)
    (hsr : SearchReady (searchLens.get s))
    (hnf : (searchLens.get s).search.mode ≠ GalilScaffoldSearchFinish.Mode.found)
    (hv : searchEffect P false s v) :
    ∃ s', (galilFrameS P q first).background s s' ∧ s'.chain = ChainVM.idle ∧
      s'.left = s.left ∧ s'.right = s.right ∧ s'.center = s.center ∧ s'.replay = s.replay ∧
      searchLens.get s' = v ∧
      (searchLens.get s').search.mode ≠ GalilScaffoldSearchFinish.Mode.found := by
  have hnfv : v.search.mode ≠ GalilScaffoldSearchFinish.Mode.found :=
    hq c s false v hm hr hidle hsr hnf hv
  obtain ⟨s', hb, hch, hl, hrr, hcC, hrp, hget⟩ :=
    idle_background_exists P q first s hidle hv hnfv
  exact ⟨s', hb, hch, hl, hrr, hcC, hrp, hget, by rw [hget]; exact hnfv⟩

/-- **`match_round`'s use site under the variant**: the comparison's `hnf`. -/
theorem match_call_notFound (P : Shared) (hq : SearchQuiet' P) (c : Control) (s : GalilVM)
    (vq : SearchVM) (hm : c.mode = Mode.scan) (hr : c.replaying = true)
    (hidle : s.chain = ChainVM.idle) (hsr : SearchReady (searchLens.get s))
    (hnf : (searchLens.get s).search.mode ≠ GalilScaffoldSearchFinish.Mode.found)
    (hqe : searchEffect P true s vq) :
    vq.search.mode ≠ GalilScaffoldSearchFinish.Mode.found :=
  hq c s true vq hm hr hidle hsr hnf hqe

#print axioms searchReady_of_found
#print axioms searchEffect_found_stutter
#print axioms searchQuiet_forces_never_found
#print axioms not_searchQuiet
#print axioms not_searchQuiet_PofC
#print axioms quiet'_of_quiet
#print axioms countR_step_notFound
#print axioms match_call_notFound

end PalPeg.GalilLeafQuiet
