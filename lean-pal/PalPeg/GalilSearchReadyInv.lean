import PalPeg.GalilBranchInvariants2
import PalPeg.GalilSearchResult

/-!
# `SearchReady` along a stage

`searchEffect_exists` (`PalPeg/GalilBranchInvariants2.lean`) needs
`SearchReady (searchLens.get s)` at *every* scan state of a segment, not only
at the restart.  This file propagates it:

* `searchReady_begin` — at a `Restarted` state the search sits in
  `GalilScaffoldSearchFinish.begin lower radius`, i.e. in `.grow`; both
  conjuncts of `SearchReady` are then vacuous.
* `searchReady_step` — one `searchStep` preserves it.
* `searchReady_run` — hence so does a whole `SearchRun`, and
  `searchEffect_exists` applies at the end state.

The `PrepInv` half is fully discharged here (`prepInv_prepare`,
`prepInv_tick`, plus the fact that every non-preparation branch of
`searchStep` lands in a mode outside `{lower, lowerHome, copy, home}`).

The `DpSafeHere` half splits in two.  *Staying* inside `.run` is discharged
here, by `DpSafeRem`: the budget witness of `DpSafeHere` is re-indexed by the
list of events **still ahead in the stage**, so that a quantum only moves one
event from the remaining list into the consumed prefix and the two numeric
side conditions (`3186*w.length+1683 ≤ 64*(bs ++ as).length` and
`count true ≤ value s0.debt`) are literally unchanged.

*Entering* `.run` cannot be derived from `PrepInv`: the fact that the program
handed over by the `startRun` tick is `GalilScaffoldPreload.initial w lower`
is a whole-phase statement (`GalilScaffoldPreparePaced.PacedPrepared` /
`prepare_complete`), and the budget `3186*w.length+1683 ≤ 64*as.length` is a
statement about how many events the stage still has left — neither is a
per-tick invariant, and `GalilScaffoldTimingCost.runBudget` only bounds the
length of the calibrated run *prefix*, not the suffix of the actual event
stream.  Both are therefore packaged into the single named hypothesis
`RunEntries` below.
-/

set_option autoImplicit false
namespace PalPeg.GalilSearchReadyInv

open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilBranchInvariants2
open GalilScaffoldCounter (Counter Canonical value)

/-! ## `DpSafeHere` with the remaining events recorded -/

/-- `DpSafeHere` re-indexed by the events of the stage that are still ahead.
`bs` is what the DP run has already consumed, `as` what is left; the two
numeric side conditions speak about `bs ++ as`, the whole stage, so they are
invariant under moving one event from `as` to `bs`. -/
def DpSafeRem (v : SearchVM) (as : List Bool) : Prop :=
  ∃ (w : List (Fin 3)) (lower : ℕ) (s0 : GalilScaffoldSearchFinish.State) (bs : List Bool),
    3186*w.length+1683 ≤ 64*(bs ++ as).length ∧ s0.mode = .run ∧
    Canonical s0.debt ∧ (((bs ++ as).count true : ℤ)) ≤ value s0.debt ∧
    DpReached w lower s0 bs v.search v.dp

theorem dpSafeHere_of_rem {v : SearchVM} {as : List Bool} (h : DpSafeRem v as) :
    DpSafeHere v.search v.dp := by
  obtain ⟨w, lower, s0, bs, hbud, hs0, hc, hb, hreach⟩ := h
  exact ⟨w, lower, s0, bs, as, hbud, hs0, hc, hb, hreach⟩

/-- The entry form: at the first configuration of a stage the DP machine is
the preload of the stage window and nothing has been consumed yet. -/
theorem dpSafeRem_entry (v : SearchVM) (w : List (Fin 3)) (lower : ℕ) (as : List Bool)
    (hdp : v.dp = ⟨GalilScaffoldPreload.initial w lower, false⟩)
    (hmode : v.search.mode = .run)
    (hbud : 3186*w.length+1683 ≤ 64*as.length)
    (hc : Canonical v.search.debt)
    (hb : ((as.count true : ℤ)) ≤ value v.search.debt) :
    DpSafeRem v as := by
  refine ⟨w, lower, v.search, [], by simpa using hbud, hmode, hc, by simpa using hb, ?_⟩
  show GalilScaffoldSearchRun.SafeQuanta v.search
    ⟨GalilScaffoldPreload.initial w lower, false⟩ [] v.search v.dp
  rw [hdp]
  exact .nil _ _

/-- One quantum moves the event `a` from the remaining list into the consumed
prefix. -/
theorem dpSafeRem_step {v v' : SearchVM} {a : Bool} {as : List Bool}
    (h : DpSafeRem v (a :: as))
    (hq : GalilScaffoldSearchRun.SafeQuanta v.search v.dp [a] v'.search v'.dp) :
    DpSafeRem v' as := by
  obtain ⟨w, lower, s0, bs, hbud, hs0, hc, hb, hreach⟩ := h
  refine ⟨w, lower, s0, bs ++ [a], ?_, hs0, hc, ?_, dpReached_step hreach hq⟩
  · simpa using hbud
  · simpa using hb

/-! ## The `PrepInv` half -/

/-- Outside the four preparation modes `PrepInv` is vacuous. -/
theorem prepInv_of_notPrep {x : GalilScaffoldPrepareControl.State}
    (hx : x.mode = .idle ∨ x.mode = .grow ∨ x.mode = .run ∨ x.mode = .found ∨
      x.mode = .missed ∨ x.mode = .wait ∨ x.mode = .double) : PrepInv x := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    rw [h] at hx <;> simp at hx

/-- The outer advance only pays debt, so it preserves `PrepInv`. -/
theorem prepInv_afterAdvance (a : Bool) {x : GalilScaffoldPrepareControl.State}
    (h : PrepInv x) : PrepInv (GalilScaffoldPreparePaced.afterAdvance a x) := by
  cases a
  · exact h
  · exact h

theorem advance_mode (a : Bool) (s : GalilScaffoldSearchFinish.State) :
    (GalilScaffoldSearchRun.advance a s).mode = s.mode := by cases a <;> rfl

theorem waitStep_mode (s : GalilScaffoldSearchFinish.State) :
    (GalilScaffoldDouble.waitStep true s).mode = .double ∨
      (GalilScaffoldDouble.waitStep true s).mode = s.mode := by
  unfold GalilScaffoldDouble.waitStep
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem doubleStep_mode (s : GalilScaffoldSearchFinish.State) :
    (GalilScaffoldDouble.step s).mode = s.mode := rfl

theorem growStep_mode (x : GalilScaffoldPrepareControl.State) :
    (GalilScaffoldStagePrepare.growStep x).mode = x.mode := rfl

theorem prepare_mode (x : GalilScaffoldPrepareControl.State) (lower : Counter)
    (center : GalilScaffoldPlace.Place) :
    (GalilScaffoldPrepareControl.prepare x lower center).mode = .lower := rfl

/-! ## The invariant along a stage -/

/-- `SearchReady` with the remaining events of the stage recorded. -/
def ReadyRem (v : SearchVM) (as : List Bool) : Prop :=
  PrepInv v.toPrep ∧ (v.search.mode = .run → DpSafeRem v as)

theorem searchReady_of_readyRem {v : SearchVM} {as : List Bool} (h : ReadyRem v as) :
    SearchReady v :=
  ⟨h.1, fun hm => dpSafeHere_of_rem (h.2 hm)⟩

/-! ### (1) The restart -/

/-- **(1)** At `GalilScaffoldSearchFinish.begin` the search is in `.grow`: the
preparation tapes are not yet in play and the DP run has not started, so both
halves of the invariant are vacuous. -/
theorem searchReady_begin (v : SearchVM) (lower radius : Counter)
    (h : v.search = GalilScaffoldSearchFinish.begin lower radius) (as : List Bool) :
    ReadyRem v as := by
  have hm : v.search.mode = .grow := by rw [h]; rfl
  refine ⟨prepInv_of_notPrep (Or.inr (Or.inl hm)), fun hr => ?_⟩
  rw [hm] at hr
  simp at hr

/-- The restart of a stage supplies the invariant for the search projection. -/
theorem searchReady_restarted {raw : List (Fin 2)} {r : GalilVM} {Rad : ℕ}
    {last : Counter} (hR : Restarted raw r Rad last) (as : List Bool) :
    ReadyRem (searchLens.get r) as :=
  searchReady_begin _ last r.radius hR.2.2.2.2.2.2.1 as

/-! ### (2) One tick -/

/-- The entry datum a single tick cannot supply: when the preparation hands
control to the DP run, the machine handed over is the preload of the stage
window and the events still ahead pay for the calibrated run budget. -/
def RunEntry (center : GalilScaffoldPlace.Place) (a : Bool) (v v' : SearchVM)
    (as : List Bool) : Prop :=
  searchStep center a v v' → v.search.mode ≠ .run → v'.search.mode = .run → DpSafeRem v' as

/-- **(2)** One `searchStep` preserves the invariant, consuming one event of
the stage.  Every branch is discharged here except the entry into `.run`,
which is `hentry`. -/
theorem searchReady_step (center : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool)
    {v v' : SearchVM} (hstep : searchStep center a v v') (h : ReadyRem v (a :: as))
    (hentry : RunEntry center a v v' as) :
    ReadyRem v' as := by
  classical
  obtain ⟨hprep, hdp⟩ := h
  unfold searchStep at hstep
  cases hm : v.search.mode with
  | idle =>
    rw [hm] at hstep; subst hstep
    exact ⟨hprep, fun hr => by rw [hm] at hr; simp at hr⟩
  | found =>
    rw [hm] at hstep; subst hstep
    exact ⟨hprep, fun hr => by rw [hm] at hr; simp at hr⟩
  | missed =>
    rw [hm] at hstep; subst hstep
    exact ⟨hprep, fun hr => by rw [hm] at hr; simp at hr⟩
  | grow =>
    rw [hm] at hstep
    by_cases hp : GalilScaffoldCounter.positive v.search.work = true
    · simp only [hp, if_true] at hstep
      have hmode : v'.search.mode = .grow := by
        rw [hstep, ofPrep_mode, afterAdvance_mode, growStep_mode]
        exact hm
      refine ⟨prepInv_of_notPrep (Or.inr (Or.inl hmode)), fun hr => ?_⟩
      rw [hmode] at hr; simp at hr
    · simp only [hp, Bool.false_eq_true, if_false] at hstep
      have hmode : v'.search.mode = .lower := by
        rw [hstep, ofPrep_mode, afterAdvance_mode, prepare_mode]
      refine ⟨?_, fun hr => ?_⟩
      · rw [hstep]
        show PrepInv (GalilScaffoldPreparePaced.afterAdvance a _)
        exact prepInv_afterAdvance a (prepInv_prepare _ _ _)
      · rw [hmode] at hr; simp at hr
  | lower =>
    rw [hm] at hstep
    obtain ⟨y, hy, hv'⟩ := hstep
    refine ⟨?_, fun hr => ?_⟩
    · rw [hv']
      show PrepInv (GalilScaffoldPreparePaced.afterAdvance a y)
      exact prepInv_afterAdvance a (prepInv_tick hy hprep)
    · exact hentry (by unfold searchStep; rw [hm]; exact ⟨y, hy, hv'⟩)
        (by rw [hm]; simp) hr
  | lowerHome =>
    rw [hm] at hstep
    obtain ⟨y, hy, hv'⟩ := hstep
    refine ⟨?_, fun hr => ?_⟩
    · rw [hv']
      show PrepInv (GalilScaffoldPreparePaced.afterAdvance a y)
      exact prepInv_afterAdvance a (prepInv_tick hy hprep)
    · exact hentry (by unfold searchStep; rw [hm]; exact ⟨y, hy, hv'⟩)
        (by rw [hm]; simp) hr
  | copy =>
    rw [hm] at hstep
    obtain ⟨y, hy, hv'⟩ := hstep
    refine ⟨?_, fun hr => ?_⟩
    · rw [hv']
      show PrepInv (GalilScaffoldPreparePaced.afterAdvance a y)
      exact prepInv_afterAdvance a (prepInv_tick hy hprep)
    · exact hentry (by unfold searchStep; rw [hm]; exact ⟨y, hy, hv'⟩)
        (by rw [hm]; simp) hr
  | home =>
    rw [hm] at hstep
    obtain ⟨y, hy, hv'⟩ := hstep
    refine ⟨?_, fun hr => ?_⟩
    · rw [hv']
      show PrepInv (GalilScaffoldPreparePaced.afterAdvance a y)
      exact prepInv_afterAdvance a (prepInv_tick hy hprep)
    · exact hentry (by unfold searchStep; rw [hm]; exact ⟨y, hy, hv'⟩)
        (by rw [hm]; simp) hr
  | run =>
    rw [hm] at hstep
    obtain ⟨hq, _, _⟩ := hstep
    refine ⟨?_, fun _ => dpSafeRem_step (hdp hm) hq⟩
    by_cases hrun : v'.search.mode = .run
    · exact prepInv_of_notPrep (Or.inr (Or.inr (Or.inl hrun)))
    · rcases GalilScaffoldSearchRun.quanta_exit_mode hq hm hrun with hf | hmi | hw | hd
      · exact prepInv_of_notPrep (Or.inr (Or.inr (Or.inr (Or.inl hf))))
      · exact prepInv_of_notPrep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hmi)))))
      · exact prepInv_of_notPrep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hw))))))
      · exact prepInv_of_notPrep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hd))))))
  | wait =>
    rw [hm] at hstep
    have hmode : v'.search.mode = .double ∨ v'.search.mode = .wait := by
      rw [hstep]
      show (GalilScaffoldSearchRun.advance a (GalilScaffoldDouble.waitStep true v.search)).mode = _ ∨
        (GalilScaffoldSearchRun.advance a (GalilScaffoldDouble.waitStep true v.search)).mode = _
      rw [advance_mode]
      rcases waitStep_mode v.search with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (h1.trans hm)
    refine ⟨?_, fun hr => ?_⟩
    · rcases hmode with h1 | h1
      · exact prepInv_of_notPrep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1))))))
      · exact prepInv_of_notPrep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))))
    · rcases hmode with h1 | h1 <;> rw [h1] at hr <;> simp at hr
  | double =>
    rw [hm] at hstep
    by_cases hp : GalilScaffoldCounter.positive v.search.work = true
    · simp only [hp, if_true] at hstep
      have hmode : v'.search.mode = .double := by
        rw [hstep]
        show (GalilScaffoldSearchRun.advance a (GalilScaffoldDouble.step v.search)).mode = _
        rw [advance_mode, doubleStep_mode]
        exact hm
      refine ⟨prepInv_of_notPrep (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hmode)))))),
        fun hr => ?_⟩
      rw [hmode] at hr; simp at hr
    · simp only [hp, Bool.false_eq_true, if_false] at hstep
      have hmode : v'.search.mode = .lower := by
        rw [hstep, ofPrep_mode, afterAdvance_mode, prepare_mode]
      refine ⟨?_, fun hr => ?_⟩
      · rw [hstep]
        show PrepInv (GalilScaffoldPreparePaced.afterAdvance a _)
        exact prepInv_afterAdvance a (prepInv_prepare _ _ _)
      · rw [hmode] at hr; simp at hr

/-! ### (3) A whole run -/

/-- **The one named gap.**  At every tick of the stage that enters the DP run,
the entry datum of `dpSafeRem_entry` is available for the events that remain.
This is exactly what `search_first_stage` / `search_later_stage` establish for
a *calibrated* stage; it is assumed here because neither the preload identity
of the handed-over program nor the count of events still ahead is a per-tick
invariant. -/
def RunEntries (center : GalilScaffoldPlace.Place) (es : List Bool) (v : SearchVM) : Prop :=
  ∀ (cs ds : List Bool) (b : Bool) (u u' : SearchVM), es = cs ++ b :: ds →
    SearchRun center cs v u → searchStep center b u u' →
    u.search.mode ≠ .run → u'.search.mode = .run → DpSafeRem u' ds

/-- **(3)** The invariant survives a whole `SearchRun`. -/
theorem searchReady_run (center : GalilScaffoldPlace.Place) {es : List Bool} {v v' : SearchVM}
    (h : SearchRun center es v v') : ReadyRem v es → RunEntries center es v → ReadyRem v' [] := by
  induction h with
  | nil w => intro hready _; exact hready
  | @cons b as v0 v1 v2 hstep hrun ih =>
    intro hready hE
    refine ih (searchReady_step center b as hstep hready ?_) ?_
    · intro _ hnr hr
      exact hE [] as b v0 v1 rfl (.nil _) hstep hnr hr
    · intro cs ds c u u' heq hru hstepu hnr hr
      exact hE (b :: cs) ds c u u' (by rw [heq]; rfl) (.cons hstep hru) hstepu hnr hr

/-- The form `searchEffect_exists` consumes: after any `SearchRun` from a
state satisfying the invariant, the end state is `SearchReady`. -/
theorem searchReady_of_run (center : GalilScaffoldPlace.Place) {es : List Bool}
    {v v' : SearchVM} (h : SearchRun center es v v') (hready : ReadyRem v es)
    (hE : RunEntries center es v) : SearchReady v' :=
  searchReady_of_readyRem (searchReady_run center h hready hE)

/-- From a restart: every state the search co-run reaches inside the stage is
`SearchReady`, hence `searchEffect_exists` applies there. -/
theorem searchEffect_exists_of_restarted (P : Shared) {raw : List (Fin 2)}
    {r : GalilVM} {Rad : ℕ} {last : Counter}
    (hR : Restarted raw r Rad last) {es : List Bool} {v' : SearchVM}
    (h : SearchRun (P.place r) es (searchLens.get r) v')
    (hE : RunEntries (P.place r) es (searchLens.get r))
    (a : Bool) (s : GalilVM) (hs : searchLens.get s = v') :
    ∃ vq, searchEffect P a s vq :=
  searchEffect_exists P a s (hs ▸ searchReady_of_run (P.place r) h (searchReady_restarted hR es) hE)

#print axioms dpSafeHere_of_rem
#print axioms dpSafeRem_entry
#print axioms dpSafeRem_step
#print axioms prepInv_of_notPrep
#print axioms prepInv_afterAdvance
#print axioms waitStep_mode
#print axioms searchReady_begin
#print axioms searchReady_restarted
#print axioms searchReady_step
#print axioms searchReady_run
#print axioms searchReady_of_run
#print axioms searchEffect_exists_of_restarted

end PalPeg.GalilSearchReadyInv
