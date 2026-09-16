import PalPeg.CloseoutPreload2

/-!
# The two residuals of `CloseoutPreload2`, settled

`CloseoutPreload2` left `StageCalibration` and `RestartEntryS`.  This file
settles both — one by an off-by-one correction, the other by a refutation.

* §1 **`StageCalibration` is false as stated, by exactly one cell.**  From the
  restart the search runs `max k 1` grow ticks (`grow_span_calibration`), each
  adding `8` to the span (`GalilScaffoldStagePrepare.growStep`), so at `prepare`
  the span is `8 * max k 1 = stageWindow k` and the window the preparation
  copies is `(stream walker).take (stageWindow k + 1)`.  Since the place stream
  is a *finite* list (`GalilScaffoldPlace.stream`), that window has length
  `min (stageWindow k + 1) (stream).length`: it is `stageWindow k` only when the
  stream is exhausted exactly at the stage boundary
  (`stageCalibration_of_exhausted`), and is `stageWindow k + 1` at every
  interior stage (`stageCalibration_off_by_one`,
  `not_stageCalibration_of_long`).  The machine's own window agrees with the
  latter: `GalilScaffoldTopReadyFound.restarted_next_found` states its DP result
  for `take (8 * max k 1 + 1)`.  So `CloseoutDebtAudit.stageWindow` is one cell
  short of the real window.

  The correction has since been **landed**: `CloseoutDebtAudit.stageWindow1 k =
  8 * max k 1 + 1` with `paced_bound1` / `stage_budget_closes1` (the stage budget
  still closes unconditionally), `CloseoutReadyStage.dpSafeStage_entry_pacedW` /
  `dpSafeStage_entry_paced1`, and the window-length clauses of
  `CloseoutPreload.EntryPreload` and `CloseoutPreload2.TracePreload`.  With it
  the calibration clause is *true* at every interior stage
  (`stageCalibration1_of_long`); `stageWindow` itself is kept only because
  `CloseoutRunEntriesS.stageWindow_restart` reads `stageWindow 0 = 8` off it.

* §2 **`RestartEntryS` is false as stated.**  It asks `RunEntriesS as` for
  *every* clock-paced `as`, with no lower bound on `as.length`, and
  `DpSafeStage` at a `.run` entry needs a charged prefix of the events still
  ahead (`CloseoutReadyStage.dpSafeStage_pre_ne_nil`).  The explicit restarted
  trace of `CloseoutRunEntriesPaced` enters `.run` after eight background
  events, so the all-`false` list of length eight — which is paced with no
  slack — already refutes it (`not_runEntriesS_eight`,
  `not_restartEntryS_ofSearch`).  This is the mirror image of
  `CloseoutRunEntriesPaced.not_runEntriesPaced`: there the counterexample was a
  paced list that is too *long*, here one that is too *short*.

  The culprit downstream is `CloseoutPreload.RdPaced`, which quantifies over
  *every* `n` and then feeds `readyPacedS_restarted` a witness that discards the
  `n ≤ as.length` premise (`rdPaced_restart`).  The repair is to carry the
  length side condition through the ledger.  That too has been landed:
  `CloseoutPreload.RdPaced` is now `∃ n0, ∀ n, n0 ≤ n → ∃ k, 2048 ≤ c.clock + k ∧
  ReadyPacedS … n k` (`rdPaced_ready` / `rdPaced_seg` / `rdPaced_restart`
  re-proved), and the entry datum is `CloseoutPreload2.RestartEntryS'`:

    `∀ u Rad last, Restarted raw u Rad last → StageEntry Rad last →
        ∀ (m : ℕ) (as : List Bool), dpEntry (value last).toNat + m ≤ as.length →
        PacedL 2048 0 as → RunEntriesS as (searchLens.get u)`

  with `dpEntry k = 8 + dpEvents (stageWindow1 k)` (the eight preparation events
  of §2 plus the charged prefix of the stage).  §3 reduces it to a single trace
  datum, `RestartTrace` (`restartEntryS'_of_trace`), and re-exports the closure
  and the final replay theorem at it.

## What is still named

`RestartTrace` (§3) — the begin → `prepare` linkage: at every
`Restarted`/`StageEntry` state, an invariant `Q` that exhibits the freshly
prepared `.lower` state with the calibrated window, is preserved by `searchStep`,
supplies the two debt facts and the length/pacing clauses at every `.run` entry,
and holds at the restart for every clock-paced list of length at least
`dpEntry k`.  `Restarted` fixes the scan tapes and the search mode (`begin last
radius`), not the preparation tapes, so this cannot be read off it; everything
else on the path from `RestartEntryS'` to `ReadyClosure` is now proved.
`StageCalibration` is no longer named: it was off by one cell, and the corrected
window makes it true (§1.3).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload3

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController
open PalPeg.GalilScaffoldPrepareControl (State)
open PalPeg.GalilScaffoldCounter (Counter Canonical value ofNat)
open PalPeg.CloseoutReadyStage
open PalPeg.CloseoutRunEntriesS
open PalPeg.CloseoutPreload
open PalPeg.CloseoutDebtAudit (dpEvents stageWindow pacedComparisons)

/-! ## 1. The window calibration: off by one -/

/-- **The span at `prepare`.**  From the restart the search sits in `.grow` with
`work = max k 1` and `span = 0`; the `max k 1` grow ticks each add `8`, so the
span handed to `prepare` is `stageWindow k`, and the debt has gained
`2 * max k 1`. -/
theorem grow_span_calibration (s : State) (k : ℕ) (hm : s.mode = .grow)
    (hw : s.work = ofNat (max k 1)) (hs : s.span = ofNat 0) :
    ∃ t, GalilScaffoldStagePrepare.Growing s (max k 1) t ∧ t.mode = .grow ∧
      t.work = ofNat 0 ∧ t.span = ofNat (stageWindow k) ∧
      value t.debt = value s.debt + 2 * max k 1 := by
  obtain ⟨t, hg, htm, htw, hts, htd⟩ :=
    GalilScaffoldStagePrepare.growing_complete s (max k 1) 0 hm hw hs
  refine ⟨t, hg, htm, htw, ?_, htd⟩
  rw [hts]
  congr 1
  simp [PalPeg.CloseoutDebtAudit.stageWindow]

#print axioms grow_span_calibration

/-- The place stream is a finite list, so the copied window is capped by it. -/
theorem window_length (p : GalilScaffoldPlace.Place) (n : ℕ) :
    ((GalilScaffoldPlace.stream p).take n).length =
      min n (GalilScaffoldPlace.stream p).length := by
  simp

/-- `StageCalibration` holds exactly when the stream is exhausted at the stage
boundary — i.e. only at the final stage. -/
theorem stageCalibration_of_exhausted (p : GalilScaffoldPlace.Place) (k : ℕ)
    (hlen : (GalilScaffoldPlace.stream p).length = stageWindow k) :
    ((GalilScaffoldPlace.stream p).take (stageWindow k + 1)).length = stageWindow k := by
  rw [window_length, hlen]; omega

/-- **The off-by-one.**  At an interior stage the copied window is one cell
longer than `CloseoutDebtAudit.stageWindow`. -/
theorem stageCalibration_off_by_one (p : GalilScaffoldPlace.Place) (k : ℕ)
    (hlen : stageWindow k < (GalilScaffoldPlace.stream p).length) :
    ((GalilScaffoldPlace.stream p).take (stageWindow k + 1)).length = stageWindow k + 1 := by
  rw [window_length]; omega

/-- **`StageCalibration` is false.**  Hence `EntryPreload`'s window-length
clause cannot be met at an interior stage with `stageWindow` as written. -/
theorem not_stageCalibration_of_long (p : GalilScaffoldPlace.Place) (k : ℕ)
    (hlen : stageWindow k < (GalilScaffoldPlace.stream p).length) :
    ((GalilScaffoldPlace.stream p).take (stageWindow k + 1)).length ≠ stageWindow k := by
  rw [stageCalibration_off_by_one p k hlen]; omega

#print axioms stageCalibration_of_exhausted
#print axioms stageCalibration_off_by_one
#print axioms not_stageCalibration_of_long

/-! ### 1.3 The true window is now the one the ledger uses -/

/-- The window the preparation really copies: `span + 1` cells.  Since this file
was written the correction has been landed in `CloseoutDebtAudit`, and the whole
chain (`CloseoutReadyStage.dpSafeStage_entry_paced1`,
`CloseoutPreload.EntryPreload`, `CloseoutPreload2.TracePreload`) is calibrated at
it; `paced_bound1` / `stage_budget_closes1` live there. -/
theorem stageWindow1_eq' (k : ℕ) :
    PalPeg.CloseoutDebtAudit.stageWindow1 k = stageWindow k + 1 := rfl

/-- **The calibration clause, now true.**  With the corrected window the
preparation's copy `take (span + 1)` at `span = stageWindow k` has exactly the
length `CloseoutPreload2.TracePreload` asks for, at every interior stage. -/
theorem stageCalibration1_of_long (p : GalilScaffoldPlace.Place) (k : ℕ)
    (hlen : stageWindow k < (GalilScaffoldPlace.stream p).length) :
    ((GalilScaffoldPlace.stream p).take (stageWindow k + 1)).length =
      PalPeg.CloseoutDebtAudit.stageWindow1 k := by
  rw [stageCalibration_off_by_one p k hlen]
  rfl

/-- The stage budget for the true window, re-exported. -/
theorem paced_bound1 (k : ℕ) :
    8192 * pacedComparisons 2048 (dpEvents (PalPeg.CloseoutDebtAudit.stageWindow1 k))
      ≤ 1593 * k + 9894 :=
  PalPeg.CloseoutDebtAudit.paced_bound1 k

theorem stage_budget_closes1 {k Rad : ℕ} (hstage : 3 * Rad ≤ 5 * k) :
    ((pacedComparisons 2048 (dpEvents (PalPeg.CloseoutDebtAudit.stageWindow1 k)) : ℕ) : ℤ)
      ≤ PalPeg.GalilReplaySpan.stageDebt Rad (k : ℤ) :=
  PalPeg.CloseoutDebtAudit.stage_budget_closes1 hstage

#print axioms stageCalibration1_of_long
#print axioms paced_bound1
#print axioms stage_budget_closes1

/-! ## 2. `RestartEntryS` is false: the paced list may be too short -/

open PalPeg.CloseoutRunEntriesPaced (v0 w p1 p2 p3 p4 p5 p6 p7 p8 ctr)

/-- **The refutation.**  The explicit restarted trace enters `.run` at the
eighth background event, and then `DpSafeStage` has no events left to charge:
`dpSafeStage_pre_ne_nil` forces a non-empty charged prefix of `[]`. -/
theorem not_runEntriesS_eight : ¬ RunEntriesS (List.replicate 8 false) v0 := by
  intro h
  obtain ⟨-, h1⟩ := h ctr (w p1) PalPeg.CloseoutRunEntriesPaced.step1
  obtain ⟨-, h2⟩ := h1 ctr (w p2) PalPeg.CloseoutRunEntriesPaced.step2
  obtain ⟨-, h3⟩ := h2 ctr (w p3) PalPeg.CloseoutRunEntriesPaced.step3
  obtain ⟨-, h4⟩ := h3 ctr (w p4) PalPeg.CloseoutRunEntriesPaced.step4
  obtain ⟨-, h5⟩ := h4 ctr (w p5) PalPeg.CloseoutRunEntriesPaced.step5
  obtain ⟨-, h6⟩ := h5 ctr (w p6) PalPeg.CloseoutRunEntriesPaced.step6
  obtain ⟨-, h7⟩ := h6 ctr (w p7) PalPeg.CloseoutRunEntriesPaced.step7
  obtain ⟨hentry, -⟩ := h7 ctr (w p8) PalPeg.CloseoutRunEntriesPaced.step8
  have hsafe : DpSafeStage (w p8) [] :=
    hentry PalPeg.CloseoutRunEntriesPaced.step8
      PalPeg.CloseoutRunEntriesPaced.p7_not_run PalPeg.CloseoutRunEntriesPaced.p8_run
  obtain ⟨wd, lower, s0, bs, pre, post, hsplit, hbud, hs0, hc, hb, hreach⟩ := hsafe
  have hpre : pre = [] := by
    cases pre with
    | nil => rfl
    | cons a as => simp at hsplit
  exact dpSafeStage_pre_ne_nil PalPeg.CloseoutRunEntriesPaced.p8_run hsplit hbud hs0 hc hb
    hreach hpre

#print axioms not_runEntriesS_eight

/-- The eight-event list is clock-paced with no slack. -/
theorem paced_eight : PacedL 2048 0 (List.replicate 8 false) :=
  pacedL_replicate_false 2048 0 8

/-- **`RestartEntryS` is unobtainable.**  Its search-side content — the entry
datum for every paced list at a state whose search is a `begin` — is false; the
`Restarted`/`StageEntry` premises constrain the scan tapes, not the length of
the event list, so they cannot repair it. -/
theorem not_restartEntryS_ofSearch :
    ¬ (∀ (v : SearchVM), (∃ last radius : Counter,
        v.search = GalilScaffoldSearchFinish.begin last radius) →
      ∀ as : List Bool, PacedL 2048 0 as → RunEntriesS as v) := by
  intro h
  exact not_runEntriesS_eight
    (h v0 ⟨_, _, PalPeg.CloseoutRunEntriesPaced.v0_search⟩ _ paced_eight)

#print axioms paced_eight
#print axioms not_restartEntryS_ofSearch

/-! ## 3. The length-guarded entry datum, and the closure -/

open PalPeg.CloseoutPreload2 (RestartEntryS' TracePreload runEntriesS_of_trace)

/-- **The restart trace datum.**  What `RestartEntryS'` still needs: at every
`Restarted`/`StageEntry` state the search trace out of the restart is carried by
*some* invariant `Q` that (i) exhibits the freshly prepared `.lower` state with
the calibrated window (`TracePreload`, §1.3 for the calibration clause),
(ii) is preserved by `searchStep`, (iii) supplies the two debt facts and the
length/pacing clauses at every `.run` entry, and (iv) holds at the restart for
every event list at least `dpEntry k` long and clock-paced.

This is the begin → `prepare` linkage: `Restarted` constrains the scan tapes and
the search *mode* (`begin last radius`), not the preparation tapes, so the datum
cannot be read off it — the trace from `begin` through `grow` to the prepared
`.lower` state is what has to be exhibited. -/
def RestartTrace (raw : List (Fin 2)) : Prop :=
  ∀ (u : GalilVM) (Rad : ℕ) (last : Counter),
    Restarted raw u Rad last → StageEntry Rad last →
    ∃ Q : SearchVM → List Bool → Prop,
      TracePreload Q (value last).toNat ∧
      (∀ (v v' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool),
        Q v (a :: as) → searchStep c a v v' → Q v' as) ∧
      (∀ (v v' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool),
        Q v (a :: as) → searchStep c a v v' → v.search.mode ≠ .run →
          v'.search.mode = .run → Canonical v'.search.debt) ∧
      (∀ (v v' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool),
        Q v (a :: as) → searchStep c a v v' → v.search.mode ≠ .run →
          v'.search.mode = .run →
            PalPeg.GalilReplaySpan.stageDebt Rad (((value last).toNat : ℕ) : ℤ)
              ≤ value v'.search.debt) ∧
      (∀ (v v' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool),
        Q v (a :: as) → searchStep c a v v' → v.search.mode ≠ .run →
          v'.search.mode = .run →
            dpEvents (PalPeg.CloseoutDebtAudit.stageWindow1 (value last).toNat)
              ≤ as.length) ∧
      (∀ (v v' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool),
        Q v (a :: as) → searchStep c a v v' → v.search.mode ≠ .run →
          v'.search.mode = .run → PacedL 2048 0 as) ∧
      (∀ (m : ℕ) (as : List Bool),
        PalPeg.CloseoutDebtAudit.dpEntry (value last).toNat + m ≤ as.length →
        PacedL 2048 0 as → Q (searchLens.get u) as)

/-- **`RestartEntryS'` from the restart trace datum.**  The stage side condition
comes from `StageEntry` at `k = (value last).toNat`, which is legitimate because
`Restarted` gives `0 ≤ value last`. -/
theorem restartEntryS'_of_trace {raw : List (Fin 2)} (h : RestartTrace raw) :
    RestartEntryS' raw := by
  intro u Rad last hR hSE m as hlen hpaced
  obtain ⟨Q, htr, hnext, hcan, hdebt, hlenQ, hpacedQ, hinit⟩ := h u Rad last hR hSE
  have hval : value last = ((value last).toNat : ℤ) := (Int.toNat_of_nonneg hR.2.2.2.2.2.2.2.2.2).symm
  have hstage : 3 * Rad ≤ 5 * (value last).toNat := hSE _ hval
  exact runEntriesS_of_trace (Rad := Rad) (k := (value last).toNat) (slack := 0)
    hstage (by omega) htr hnext hcan hdebt hlenQ hpacedQ as (searchLens.get u)
    (hinit m as hlen hpaced)

#print axioms restartEntryS'_of_trace

/-- **`GalilReplaySpan.ReadyClosure` for the weakened `RdPaced`** —
`CloseoutPreload2.readyClosure_paced`, now at the length-guarded entry datum
`RestartEntryS'` (§2 refutes the unguarded form, and `restartEntryS'_of_trace`
reduces the guarded one to `RestartTrace`). -/
theorem readyClosure_C (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    (hE : RestartEntryS' raw) :
    PalPeg.GalilReplaySpan.ReadyClosure raw P q first 2048 RdPaced :=
  PalPeg.CloseoutPreload2.readyClosure_paced raw P q first hE

#print axioms readyClosure_C

/-- The same from the trace datum. -/
theorem readyClosure_C_of_trace (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    (hE : RestartTrace raw) :
    PalPeg.GalilReplaySpan.ReadyClosure raw P q first 2048 RdPaced :=
  readyClosure_C raw P q first (restartEntryS'_of_trace hE)

#print axioms readyClosure_C_of_trace

/-- **The final replay theorem with the concrete ledger.**
`GalilReplaySpan.replay_after_fallback_general''_R_of_decodes` at `Rd = RdPaced`,
with the restart datum in its corrected, length-guarded shape. -/
def replay_final_of_decodes (raw : List (Fin 2)) (P : Shared)
    (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM)
    (q : ℕ) (first : Fin 9)
    (hex : ∀ s, P.replayExhausted s = GalilScaffoldCounter.zero s.replay)
    (hsearch : ∀ s : GalilVM, PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect P a s v)
    (hE : RestartEntryS' raw)
    (hdec : Decodes P)
    (hbudget : PalPeg.GalilReplaySpan.ReplayBudgetRD raw P q first 2048)
    (hrs : PalPeg.GalilReplaySpan.RestartShapeL P)
    (r : ℕ) (hr0 : 0 < r) (c : Control) (t : GalilVM)
    (hm : c.mode = Mode.scan) (hc : c.clock = 2048) (hrpl : c.replaying = true)
    (hR : Restarted raw t 0 GalilScaffoldCounter.reset) (hrep : t.replay = ofNat r)
    (hM : MInv raw c t) (hfr : Frontier t) (hsi : ShiftIdle t) :=
  PalPeg.GalilReplaySpan.replay_after_fallback_general''_R_of_decodes
    raw P hP hP' q first hex hsearch (readyClosure_C raw P q first hE) hdec hbudget hrs
    r hr0 c t hm hc hrpl hR hrep hM hfr hsi

#print axioms replay_final_of_decodes

end PalPeg.CloseoutPreload3
