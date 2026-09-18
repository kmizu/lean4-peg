import PalPeg.StageCycleSearch

/-!
# The `.double` leg, step-locally

`CloseoutRunEntriesS.EntryInv Q` hands its invariant one `searchStep` at a time
and quantifies over *every* event list, so `Q` cannot name the leg it is in the
middle of.  `CloseoutPreload17.double_spends` and
`CloseoutPreload35.postRunF_round_trip_S` both take the whole `.double` leg
(`bs.length = mw`) as a hypothesis; this file re-states that leg as an invariant
that survives one tick at a time.

* `doubleTrace_snoc` — `DoubleTrace` is built by consing at the *front*, so
  growing it at the far end (which is what a step-local invariant does) needs
  its own induction.
* `doubleTrace_frame` — after `ds` ticks the work has fallen by `ds.length`
  (hence `ds.length ≤ mw`) and the span has risen by `2 * ds.length`.
* `DoubleLeg` — the invariant: the ticks consumed so far, the pacing of the
  whole remaining stream measured from the leg's start, and the frame data at
  that start.  The pacing has to be measured from the start because
  `bal_of_paced_slack_S` reads the comparison count of the *whole* leg, which a
  state predicate at the current tick has already forgotten.
* `doubleLeg_step` / `doubleLeg_exit` — the two branches of a tick: work still
  positive keeps the invariant, work spent dispatches into `PrepAt k (2 * mw)`
  with `StageInvS k (2 * mw)`.

**Not done here.**  This is one of the four phases of the stage cycle
(`.run` / `.wait` / `.double` / preparation).  The other three, and the
assembly into an `EntryInv` invariant, are not in this file, so nothing is
removed from any axiom or hypothesis list yet.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.StageDoubleLeg

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop
open PalPeg.GalilScaffoldSearchFinish (Mode)
open PalPeg.GalilScaffoldCounter (Canonical value ofNat positive reset
  inc_ofNat dec_ofNat_succ)
open PalPeg.CloseoutReadyStage (PacedL)
open PalPeg.CloseoutPreload10 (PrepAt)
open PalPeg.CloseoutPreload17 (DoubleTrace double_step_pos)
open PalPeg.CloseoutPreload35 (StageInvS stageInvS_of_double_exit bal_of_paced_slack_S
  pacedL_prefix_count_slack)

/-! ## 1. Growing and reading a `DoubleTrace` -/

/-- **One more tick at the far end.**  `DoubleTrace` conses at the front, so the
step that a step-local invariant performs — at the trace's *end* — is an
induction. -/
theorem doubleTrace_snoc {ds : List Bool} {u v v' : SearchVM}
    {c : GalilScaffoldPlace.Place} {a : Bool} (hr : DoubleTrace ds u v) :
    v.search.mode = Mode.double → positive v.search.work = true →
      searchStep c a v v' → DoubleTrace (ds ++ [a]) u v' := by
  induction hr with
  | nil w => intro hm hp hs; exact .cons c a [] w v' v' hm hp hs (.nil v')
  | cons c0 a0 as w w' t hm0 hp0 hs0 _ ih =>
      intro hm hp hs
      exact .cons c0 a0 (as ++ [a]) w w' v' hm0 hp0 hs0 (ih hm hp hs)

/-- **What `ds` ticks of doubling have done.**  Each tick spends one unit of
work and adds two to the span, so a trace can never be longer than the work it
started with. -/
theorem doubleTrace_frame {ds : List Bool} {u v : SearchVM} (hr : DoubleTrace ds u v) :
    ∀ mw sp : ℕ, u.search.mode = Mode.double → u.search.work = ofNat mw →
      u.search.span = ofNat sp →
      ds.length ≤ mw ∧ v.search.mode = Mode.double ∧
        v.search.work = ofNat (mw - ds.length) ∧
        v.search.span = ofNat (sp + 2 * ds.length) ∧ v.lower = u.lower := by
  induction hr with
  | nil w =>
      intro mw sp hm hw hsp
      exact ⟨Nat.zero_le _, hm, by simpa using hw, by simpa using hsp, rfl⟩
  | cons c0 a0 as w w' t hm0 hp0 hs0 _ ih =>
      intro mw sp hm hw hsp
      have hmwpos : 0 < mw := (positive_ofNat_iff mw).1 (by rw [← hw]; exact hp0)
      obtain ⟨mw', rfl⟩ : ∃ mw', mw = mw' + 1 := ⟨mw - 1, by omega⟩
      have he : w' = {w with
          search := GalilScaffoldSearchRun.advance a0 (GalilScaffoldDouble.step w.search)} :=
        double_step_pos hm0 hp0 hs0
      have hm' : w'.search.mode = Mode.double := by
        cases a0 <;>
          simpa [he, GalilScaffoldSearchRun.advance, GalilScaffoldDouble.step] using hm0
      have hw' : w'.search.work = ofNat mw' := by
        cases a0 <;>
          simp [he, GalilScaffoldSearchRun.advance, GalilScaffoldDouble.step, hw,
            dec_ofNat_succ]
      have hsp' : w'.search.span = ofNat (sp + 2) := by
        cases a0 <;>
          simp [he, GalilScaffoldSearchRun.advance, GalilScaffoldDouble.step, hsp,
            inc_ofNat, Nat.add_assoc]
      have hlow' : w'.lower = w.lower := by rw [he]
      obtain ⟨hle, htm, htw, hts, htl⟩ := ih mw' (sp + 2) hm' hw' hsp'
      refine ⟨by simp only [List.length_cons]; omega, htm, ?_, ?_, by rw [htl, hlow']⟩
      · have harg : mw' + 1 - (a0 :: as).length = mw' - as.length := by
          simp only [List.length_cons]; omega
        rw [htw, harg]
      · have harg : sp + 2 * (a0 :: as).length = sp + 2 + 2 * as.length := by
          simp only [List.length_cons]; omega
        rw [hts, harg]

#print axioms doubleTrace_snoc
#print axioms doubleTrace_frame

/-! ## 2. The pacing of a prefix, at an arbitrary slack -/

/-- `CloseoutPreload35.pacedL_prefix_of_append` at an arbitrary slack: its
statement is fixed at slack `0`, and the `.double` leg is entered at whatever
phase the clock is in. -/
theorem pacedL_prefix_slack {d slack : ℕ} {xs ys : List Bool}
    (h : PacedL d slack (xs ++ ys)) : PacedL d slack xs := by
  intro n
  by_cases hn : n ≤ xs.length
  · have h2 := h n
    rw [List.take_append_of_le_length hn] at h2
    exact h2
  · have h2 := pacedL_prefix_count_slack h
    rw [List.take_of_length_le (by omega : xs.length ≤ n)]
    omega

#print axioms pacedL_prefix_slack

/-! ## 3. The leg as a step-local invariant -/

/-- **The `.double` leg in progress.**  `ds` are the ticks already spent, the
pacing is measured from the leg's start `u` (so the comparison count of the
whole leg is still readable at the exit), and the rest is the frame `u` was
left in by `CloseoutPreload14.wait_exit_double`. -/
def DoubleLeg (k mw slack : ℕ) (u v : SearchVM) (as : List Bool) : Prop :=
  ∃ ds : List Bool,
    DoubleTrace ds u v ∧ PacedL 2048 slack (ds ++ as) ∧
      u.search.mode = Mode.double ∧ u.search.work = ofNat mw ∧
      u.search.span = reset ∧ u.search.quarter = 0 ∧
      value u.search.debt = 0 ∧ Canonical u.search.debt ∧ u.lower = ofNat k

/-- **A tick with work left keeps the leg.** -/
theorem doubleLeg_step {k mw slack : ℕ} {u v v' : SearchVM} {as : List Bool}
    {c : GalilScaffoldPlace.Place} {a : Bool}
    (h : DoubleLeg k mw slack u v (a :: as)) (hpos : positive v.search.work = true)
    (hs : searchStep c a v v') :
    DoubleLeg k mw slack u v' as := by
  obtain ⟨ds, hr, hpaced, hm, hw, hsp, hq, hd, hcan, hlow⟩ := h
  obtain ⟨-, hvm, -, -, -⟩ := doubleTrace_frame hr mw 0 hm hw (by rw [hsp]; rfl)
  refine ⟨ds ++ [a], doubleTrace_snoc hr hvm hpos hs, ?_, hm, hw, hsp, hq, hd, hcan, hlow⟩
  simpa [List.append_assoc] using hpaced

/-- **A tick with the work spent dispatches into the next stage.**  This is
`CloseoutPreload35.stageInvS_of_double_exit` reached from the invariant instead
of from a leg given whole: the length `ds.length = mw` is read off
`doubleTrace_frame` rather than assumed. -/
theorem doubleLeg_exit {k mw slack : ℕ} {u v v' : SearchVM} {as : List Bool}
    {c : GalilScaffoldPlace.Place} {a : Bool}
    (h : DoubleLeg k mw slack u v (a :: as)) (hpos : positive v.search.work = false)
    (hs : searchStep c a v v')
    (hcal : 8 * max k 1 ≤ 2 * mw) (hmw : 16 ≤ mw) (hslack : slack ≤ 2047) :
    PrepAt k (2 * mw) v' ∧ StageInvS k (2 * mw) v' := by
  obtain ⟨ds, hr, hpaced, hm, hw, hsp, hq, hd, hcan, hlow⟩ := h
  obtain ⟨hle, hvm, hvw, hvs, hvl⟩ := doubleTrace_frame hr mw 0 hm hw (by rw [hsp]; rfl)
  have hlen : ds.length = mw := by
    rcases Nat.lt_or_ge ds.length mw with hlt | hge
    · exfalso
      have : positive v.search.work = true := by
        rw [hvw]; exact (positive_ofNat_iff _).2 (by omega)
      rw [hpos] at this; exact Bool.noConfusion this
    · omega
  have hts : v.search.span = ofNat (2 * mw) := by rw [hvs, hlen]; simp
  have htl : v.lower = ofNat k := by rw [hvl, hlow]
  have hpa : PacedL 2048 slack (ds ++ [a]) :=
    pacedL_prefix_slack (ys := as) (by simpa [List.append_assoc] using hpaced)
  exact stageInvS_of_double_exit hr hd hq hcan hvm hpos hts htl hlen
    (bal_of_paced_slack_S hcal hlen hmw hslack hpa) hs

#print axioms doubleLeg_step
#print axioms doubleLeg_exit

end PalPeg.StageDoubleLeg
