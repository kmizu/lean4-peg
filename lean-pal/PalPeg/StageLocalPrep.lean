import PalPeg.CloseoutPreload10

/-!
# `StageLocalPrep`: the preparation backbone, without the walk

`CloseoutPreload5.Phase` / `CloseoutPreload8.StagePrep` / `CloseoutPreload11.StagePrep2`
all carry the *walk* `bs` from the stage's own `begin` (`ReachP w bs v`).  That is
what makes `CloseoutPreload5.NoReturn` false and `CloseoutPreload8.PostRun`
unprovable: after `run → wait → double → prepare` the machine is preparing again,
but the walk that got it there is **not** a `ReachP`, so neither predicate can be
re-established at the next stage.

The datum the consumers actually use is **state-local**.  `CloseoutPreload2.
preloadAt_of_prepRun` needs only

* a fresh `.lower` entry `v0` (mode, `work`, `span`, tape 10, all other tapes reset), and
* `PrepTrace v0 n v`.

`CloseoutPreload10.PrepAt k m` is exactly that fresh entry, and
`CloseoutPreload10.prepAt_of_double_exit` re-establishes it **at the stage
boundary from the `.double` exit alone** — no walk.  So this file carries
`PrepAt` + `PrepTrace` as one state predicate, `PrepPhase`, and shows

1. it starts at a `PrepAt` (`prepPhase_start`),
2. it is preserved by every non-`.run` step (`prepPhase_step`),
3. **it is re-established at the stage boundary** (`prepPhase_of_double_exit`),
4. at a `.run` dispatch it yields the DP preload with the window bound
   `w.length ≤ m + 1` (`preloadAt_of_prepPhase`).

(4) needs **no calibration hypothesis**: `CloseoutPreload2.preloadAtEntry_of_trace`
asked for `((stream s.walker).take (span+1)).length = stageWindow1 k`, but the
consumer `CloseoutPreload11.dpSafe_entry_km` only wants `W.length ≤ m + 1`, and
that is `List.length_take` — free.

**This file removes no axiom by itself.**  It is the backbone the readiness
induction needs so that `PostRun` / `NoReturn` can be dropped; the list
bookkeeping at the boundary (pacing, event supply, debt) is *not* done here.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.StageLocalPrep

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop
open PalPeg.GalilScaffoldSearchFinish (Mode)
open PalPeg.GalilScaffoldCounter (Counter Canonical value ofNat positive)
open PalPeg.CloseoutPreload (PreloadAt)
open PalPeg.CloseoutPreload2 (PrepTrace preloadAt_of_prepRun)
open PalPeg.CloseoutPreload4 (prepTrace_mode)
open PalPeg.CloseoutPreload5 (prepTrace_snoc prepMode_four)
open PalPeg.CloseoutPreload10 (PrepAt prepAt_of_double_exit)

/-! ## 1. The state-local preparation phase -/

/-- **NAMED — the preparation phase, state-local.**  `v` is `n` preparation
ticks past a fresh `.lower` entry at lower bound `k` and span `m`, and is not
yet in `.run`.  Compare `CloseoutPreload11.StagePrep2`, whose first clause is
`ReachP w bs v` — a walk out of *this stage's* `begin`, which the machine leaves
for good at the first `.run` entry. -/
def PrepPhase (k m n : ℕ) (v : SearchVM) : Prop :=
  (∃ e : SearchVM, PrepAt k m e ∧ PrepTrace e n v) ∧ v.search.mode ≠ Mode.run

theorem prepPhase_prepMode {k m n : ℕ} {v : SearchVM} (h : PrepPhase k m n v) :
    PalPeg.CloseoutPreload4.PrepMode v.search.mode := by
  obtain ⟨⟨e, he, htr⟩, -⟩ := h
  exact prepTrace_mode htr (Or.inl he.mode)

theorem prepPhase_four {k m n : ℕ} {v : SearchVM} (h : PrepPhase k m n v) :
    v.search.mode = Mode.lower ∨ v.search.mode = Mode.lowerHome ∨
      v.search.mode = Mode.copy ∨ v.search.mode = Mode.home :=
  prepMode_four (prepPhase_prepMode h) h.2

/-- The phase starts at the fresh entry itself. -/
theorem prepPhase_start {k m : ℕ} {v : SearchVM} (h : PrepAt k m v) :
    PrepPhase k m 0 v :=
  ⟨⟨v, h, .nil v⟩, by rw [h.mode]; exact fun hc => by cases hc⟩

/-- **The phase is preserved by every step that does not enter `.run`.**  The
step count is the only thing that grows; `k` and `m` are untouched. -/
theorem prepPhase_step {k m n : ℕ} {v v' : SearchVM} {c : GalilScaffoldPlace.Place}
    {a : Bool} (h : PrepPhase k m n v) (hs : searchStep c a v v')
    (hne : v'.search.mode ≠ Mode.run) :
    PrepPhase k m (n + 1) v' := by
  obtain ⟨⟨e, he, htr⟩, hnr⟩ := id h
  exact ⟨⟨e, he, prepTrace_snoc htr (prepPhase_four h) ⟨c, a, hs⟩⟩, hne⟩

/-! ## 2. The stage boundary -/

/-- **NAMED — the phase is re-established at the stage boundary.**  This is the
step `ReachP` cannot take: the doubling phase dispatches `prepare`, and the
landing state is a fresh `.lower` entry at the *same* lower bound `k` and the
span `m` the doubling reached.  The hypotheses are all state-local — the walk
that led into the `.double` phase plays no part. -/
theorem prepPhase_of_double_exit {c : GalilScaffoldPlace.Place} {t t' : SearchVM}
    {a : Bool} {k m : ℕ}
    (htm : t.search.mode = Mode.double)
    (htw : positive t.search.work = false)
    (hsp : t.search.span = ofNat m) (hlow : t.lower = ofNat k)
    (hc : Canonical t.search.debt) (hs : searchStep c a t t') :
    PrepPhase k m 0 t' :=
  prepPhase_start (prepAt_of_double_exit htm htw hsp hlow hc hs).1

/-! ## 3. The DP preload at the dispatch, without a calibration -/

/-- **NAMED — the preload at the `.run` dispatch, state-local.**  From the phase
alone the DP entered at the dispatch is the preload of the window
`(stream entry.walker).take (m+1)`, whose length is `≤ m + 1` by
`List.length_take` — the calibration `((stream s.walker).take (span+1)).length =
stageWindow1 k` that `CloseoutPreload2.preloadAtEntry_of_trace` demanded is
**not needed**: `CloseoutPreload11.dpSafe_entry_km` reads the window as
`W.length ≤ m + 1`. -/
theorem preloadAt_of_prepPhase {k m n : ℕ} {v v' : SearchVM}
    {c : GalilScaffoldPlace.Place} {a : Bool}
    (h : PrepPhase k m n v) (hs : searchStep c a v v')
    (hr : v'.search.mode = Mode.run) :
    ∃ (w : List (Fin 3)) (l : ℕ), w.length ≤ m + 1 ∧ PreloadAt v.toPrep w l := by
  obtain ⟨⟨e, he, htr⟩, hne⟩ := h
  refine ⟨(GalilScaffoldPlace.stream e.toPrep.walker).take (m + 1), k, by simp, ?_⟩
  exact preloadAt_of_prepRun e.toPrep k m n he.mode he.work he.span he.ten
    (he.other 7 (by decide)) (fun i _ hi => he.other i hi)
    ⟨e, rfl, htr⟩ hs hne hr

#print axioms prepPhase_start
#print axioms prepPhase_step
#print axioms prepPhase_of_double_exit
#print axioms preloadAt_of_prepPhase

end PalPeg.StageLocalPrep
