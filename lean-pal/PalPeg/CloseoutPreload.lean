import PalPeg.CloseoutRunEntriesS

/-!
# `PreloadHandover`: the preload identification at the `.run` entry

`CloseoutRunEntriesS` reduced `RunEntryS` to a single residual, named there as

  `PreloadHandover : ∀ (v v' : SearchVM) (center : GalilScaffoldPlace.Place) (a : Bool)
      (w : List (Fin 3)) (lower : ℕ),
      searchStep center a v v' → v.search.mode ≠ .run → v'.search.mode = .run →
      v'.dp = ⟨GalilScaffoldPreload.initial w lower, false⟩`

with `w` the calibrated stage window (`w.length = stageWindow k`).  As stated it
is *not* a per-tick fact — it is a statement about the whole preparation phase
(`grow → lower/lowerHome → copy → home → startRun`) that precedes the entry.
This file splits it at the right seam.

* §1 `PreloadAt x w lower` — the **tape shape** the preparation phase is aiming
  at: SOURCE (tape `7`) holds the bounded window, LOWER (tape `10`) the bounded
  unary lower counter, every other tape is `reset`.  `start_dp_preload` is the
  per-tick half: `GalilScaffoldControl.start 320` of such a program *is*
  `⟨GalilScaffoldPreload.initial w lower, false⟩`, because `start` only sets the
  `pc` to `320` and clears `done`, and `initial` is exactly this tape family at
  `pc = 320`.  No hypothesis on the mode is needed.

* §2 `run_entry_preload` — `PreloadHandover` for a state that satisfies
  `PreloadAt`.  Combined with `CloseoutRunEntriesS.run_entry_dp` (entering `.run`
  is `startRun`, so the handed-over machine is `start 320 v.dp`) this is the
  whole content of the hand-over.

* §3 `prep_run_preload` — the **unconditional whole-phase** fact: along a
  complete `GalilScaffoldPrepareControl.Run` out of a freshly prepared `.lower`
  state, the state that reaches `.run` has
  `program = ⟨initial w lower, false⟩` for `w = (stream walker).take (span+1)`.
  `preloadAt_of_program` reads the tape shape back off it.  So the hand-over is
  *proved* for the preparation phase as a whole; what a single `searchStep`
  cannot see is only that the entry it is looking at is the end of such a phase.

* §4 `runEntryS_of_preloadAt` — the packaging: `PreloadAt` at the predecessor,
  plus the two debt facts of the stage, give `RunEntryS` outright via
  `CloseoutRunEntriesS.runEntryS_of_handover`.  `runEntriesS_of_preloadInv`
  turns a preservation invariant carrying `PreloadAt` into `RunEntriesS` for
  *every* event list.

* §5 the ledger closure: `RdPaced c s := ∀ n, ∃ k, 2048 ≤ c.clock + k ∧
  ReadyPacedS (searchLens.get s) n k` satisfies
  the three fields of `GalilReplaySpan.ReadyClosure raw P q first 2048 RdPaced`
  (`rdPaced_ready`, `rdPaced_seg`, `rdPaced_restart`), the last one fed by the
  residual `RunEntriesS` datum at restarts.  Assembling the structure itself is
  the one-line re-export that `''_S_of_decodes` consumes downstream.

## What is still named

`PreloadAtEntry` — that at every `.run` entry of the concrete search the
predecessor satisfies `PreloadAt` for the calibrated window of the current
stage.  Its precise type is

  `PreloadAtEntry : ∀ (v v' : SearchVM) (center : GalilScaffoldPlace.Place) (a : Bool)
      (k : ℕ), searchStep center a v v' → v.search.mode ≠ .run → v'.search.mode = .run →
      ∃ (w : List (Fin 3)) (lower : ℕ),
        w.length = PalPeg.CloseoutDebtAudit.stageWindow k ∧ PreloadAt v.toPrep w lower`

and `runEntriesS_of_preloadInv` below shows that this, plus the two debt facts,
is all that `RunEntriesS` still needs.  §3 proves the corresponding statement
along a complete preparation `Run`, so what is missing is only the *linkage* of
the `searchStep` trace at the entry to such a run — i.e. that the search really
did pass through `prepare … → lower → … → home` since the last restart, with the
span counter carrying the stage's calibration.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController
open PalPeg.GalilScaffoldPrepareControl (State Tick Run prepare)
open PalPeg.GalilScaffoldCounter (Counter Canonical value)
open PalPeg.CloseoutReadyStage
open PalPeg.CloseoutRunEntriesS
open PalPeg.CloseoutDebtAudit (dpEvents stageWindow)

/-! ## 1. The preload tape shape and the per-tick half -/

/-- **The preload tape shape.**  SOURCE holds the bounded window, LOWER the
bounded unary counter, every other tape is blank.  This is exactly the tape
family of `GalilScaffoldPreload.initial w lower`, with no constraint on the
program counter or the `done` flag. -/
def PreloadAt (x : State) (w : List (Fin 3)) (lower : ℕ) : Prop :=
  x.program.config.tapes 7 =
      GalilScaffoldPreload.bounded (w.map GalilFppPreparation.symbol) ∧
  x.program.config.tapes 10 = GalilScaffoldPreload.bounded (List.replicate lower 8) ∧
  ∀ i : Fin 12, i ≠ 7 → i ≠ 10 → x.program.config.tapes i = GalilScaffoldTape.reset

/-- **The per-tick half of the hand-over.**  `start 320` of a program whose tapes
have the preload shape is the preload machine on the nose. -/
theorem start_dp_preload {x : State} {w : List (Fin 3)} {lower : ℕ}
    (h : PreloadAt x w lower) :
    GalilScaffoldControl.start 320 x.program =
      (⟨GalilScaffoldPreload.initial w lower, false⟩ :
        GalilScaffoldControl.Machine 12) := by
  obtain ⟨h7, h10, hoth⟩ := h
  have hc : ({x.program.config with pc := 320} : GalilScaffoldProgram.Config 12)
      = GalilScaffoldPreload.initial w lower := by
    refine GalilScaffoldLoading.config_ext rfl ?_
    funext i
    by_cases hi7 : i = 7
    · subst i; simpa [GalilScaffoldPreload.initial] using h7
    · by_cases hi10 : i = 10
      · subst i; simpa [GalilScaffoldPreload.initial, hi7] using h10
      · simpa [GalilScaffoldPreload.initial, hi7, hi10] using hoth i hi7 hi10
  simp [GalilScaffoldControl.start, hc]

#print axioms start_dp_preload

/-- The preload shape puts the SOURCE head on the `LEFT` mark, which is the
enabling guard of `startRun`. -/
theorem preloadAt_focus {x : State} {w : List (Fin 3)} {lower : ℕ}
    (h : PreloadAt x w lower) : (x.program.config.tapes 7).focus = 4 := by
  rw [h.1]; rfl

#print axioms preloadAt_focus

/-! ## 2. `PreloadHandover` from the shape -/

/-- **`PreloadHandover` for a predecessor in preload shape.**  Entering `.run` is
`startRun` (`CloseoutRunEntriesS.run_entry_dp`), so the handed-over machine is
`start 320 v.dp`, which §1 identifies with the preload. -/
theorem run_entry_preload {center : GalilScaffoldPlace.Place} {a : Bool}
    {v v' : SearchVM} {w : List (Fin 3)} {lower : ℕ}
    (hs : searchStep center a v v') (hne : v.search.mode ≠ .run)
    (hr : v'.search.mode = .run) (hpre : PreloadAt v.toPrep w lower) :
    v'.dp = (⟨GalilScaffoldPreload.initial w lower, false⟩ :
      GalilScaffoldControl.Machine 12) := by
  rw [run_entry_dp hs hne hr]
  exact start_dp_preload hpre

#print axioms run_entry_preload

/-! ## 3. The whole-phase fact, unconditionally -/

/-- **The preparation phase really does build the preload.**  `prepared_run`
promoted from a `Config` equation to a `Machine` equation: the state that reaches
`.run` along a complete preparation run holds exactly
`⟨GalilScaffoldPreload.initial w lower, false⟩`. -/
theorem prep_run_preload (s : State) (lower span : ℕ)
    (hm : s.mode = .lower) (hw : s.work = GalilScaffoldCounter.ofNat lower)
    (hspan : s.span = GalilScaffoldCounter.ofNat span)
    (h10 : s.program.config.tapes 10 =
      GalilScaffoldTape.moveRight (GalilScaffoldTape.write GalilScaffoldTape.reset 4))
    (h7 : s.program.config.tapes 7 = GalilScaffoldTape.reset)
    (hother : ∀ i : Fin 12, i ≠ 7 → i ≠ 10 →
      s.program.config.tapes i = GalilScaffoldTape.reset) :
    let w := (GalilScaffoldPlace.stream s.walker).take (span+1)
    ∃ t, Run s (List.replicate (2*lower+2*w.length+6) true) t ∧
      t.mode = .run ∧
      t.program = (⟨GalilScaffoldPreload.initial w lower, false⟩ :
        GalilScaffoldControl.Machine 12) ∧
      t.debt = s.debt := by
  obtain ⟨t, hrun, hmode, hcfg, hdone, hdebt, -⟩ :=
    GalilScaffoldPrepareControl.prepared_run s lower span hm hw hspan h10 h7 hother
  refine ⟨t, hrun, hmode, ?_, hdebt⟩
  rcases ht : t.program with ⟨cfg, done⟩
  rw [ht] at hcfg hdone
  simp_all

#print axioms prep_run_preload

/-- The preload machine is in preload shape: `PreloadAt` reads the tape family of
`GalilScaffoldPreload.initial` straight back. -/
theorem preloadAt_of_program {x : State} {w : List (Fin 3)} {lower : ℕ}
    (h : x.program = (⟨GalilScaffoldPreload.initial w lower, false⟩ :
      GalilScaffoldControl.Machine 12)) :
    PreloadAt x w lower := by
  refine ⟨?_, ?_, ?_⟩
  · rw [h]; rfl
  · rw [h]; rfl
  · intro i hi7 hi10
    rw [h]
    simp [GalilScaffoldPreload.initial, hi7, hi10]

#print axioms preloadAt_of_program

/-! ## 4. Packaging into `RunEntryS` and `RunEntriesS` -/

/-- **`RunEntryS` from the preload shape.**  `CloseoutRunEntriesS.runEntryS_of_handover`
with its hand-over premise discharged by §2. -/
theorem runEntryS_of_preloadAt (center : GalilScaffoldPlace.Place) (a : Bool)
    (v v' : SearchVM) (as : List Bool) (w : List (Fin 3)) (lower Rad k slack : ℕ)
    (hw : w.length = stageWindow k)
    (hpre : searchStep center a v v' → v.search.mode ≠ .run → v'.search.mode = .run →
      PreloadAt v.toPrep w lower)
    (hcan : searchStep center a v v' → v.search.mode ≠ .run → v'.search.mode = .run →
      Canonical v'.search.debt)
    (hdebt : searchStep center a v v' → v.search.mode ≠ .run → v'.search.mode = .run →
      PalPeg.GalilReplaySpan.stageDebt Rad (k : ℤ) ≤ value v'.search.debt)
    (hstage : 3 * Rad ≤ 5 * k) (hslack : slack ≤ 2047)
    (hlen : dpEvents (stageWindow k) ≤ as.length) (hpaced : PacedL 2048 slack as) :
    RunEntryS center a v v' as :=
  runEntryS_of_handover center a v v' as w lower Rad k slack hw
    (fun hs hne hr => run_entry_preload hs hne hr (hpre hs hne hr))
    hcan hdebt hstage hslack hlen hpaced

#print axioms runEntryS_of_preloadAt

/-- **The named residual, as a predicate.**  At every `.run` entry the
predecessor is in preload shape for the calibrated window of the current stage,
and the entry debt is the stage debt.  This is all that `RunEntriesS` still
needs; `runEntriesS_of_preloadInv` below closes the induction. -/
def EntryPreload (Q : SearchVM → List Bool → Prop) (Rad k slack : ℕ) : Prop :=
  ∀ (v v' : SearchVM) (center : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool),
    Q v (a :: as) → searchStep center a v v' →
      ((v.search.mode ≠ .run → v'.search.mode = .run →
        (∃ (w : List (Fin 3)) (lower : ℕ), w.length = stageWindow k ∧
          PreloadAt v.toPrep w lower) ∧
        Canonical v'.search.debt ∧
        PalPeg.GalilReplaySpan.stageDebt Rad (k : ℤ) ≤ value v'.search.debt) ∧
        dpEvents (stageWindow k) ≤ as.length ∧ PacedL 2048 slack as) ∧ Q v' as

/-- **`RunEntriesS` for every event list from the preload invariant.**  The
budget half is `dpSafeStage_entry_paced` (budget-free); the shape half is §2. -/
theorem runEntriesS_of_preloadInv {Q : SearchVM → List Bool → Prop} {Rad k slack : ℕ}
    (hstage : 3 * Rad ≤ 5 * k) (hslack : slack ≤ 2047)
    (hQ : EntryPreload Q Rad k slack) :
    ∀ (as : List Bool) (v : SearchVM), Q v as → RunEntriesS as v := by
  intro as
  induction as with
  | nil => intro v _; trivial
  | cons a as ih =>
    intro v hq center v' hstep
    obtain ⟨hentry, hnext⟩ := hQ v v' center a as hq hstep
    obtain ⟨hdata, hlen, hpaced⟩ := hentry
    refine ⟨?_, ih v' hnext⟩
    by_cases hne : v.search.mode = .run
    · intro _ hne' _; exact absurd hne hne'
    · by_cases hr : v'.search.mode = .run
      · obtain ⟨⟨w, lower, hw, hpre⟩, hcan, hdebt⟩ := hdata hne hr
        exact runEntryS_of_preloadAt center a v v' as w lower Rad k slack hw
          (fun _ _ _ => hpre) (fun _ _ _ => hcan) (fun _ _ _ => hdebt)
          hstage hslack hlen hpaced
      · intro _ _ hr'; exact absurd hr' hr

#print axioms runEntriesS_of_preloadInv

/-! ## 5. The ledger closure for `''_S_of_decodes` -/

/-- The concrete readiness ledger: at every reachable state the paced closure
holds with a slack that, together with the controller clock, fills a full
quantum.  This is the `Rd` that `GalilReplaySpan.ReadyClosure` is meant to be
instantiated at. -/
def RdPaced (c : Control) (s : GalilVM) : Prop :=
  ∀ n : ℕ, ∃ k : ℕ, 2048 ≤ c.clock + k ∧ ReadyPacedS (searchLens.get s) n k

/-- `ReadyClosure.ready` for `RdPaced`. -/
theorem rdPaced_ready (c : Control) (s : GalilVM) (h : RdPaced c s) :
    PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) := by
  obtain ⟨k, -, hk⟩ := h 0
  exact readyPacedS_ready hk

/-- `ReadyClosure.seg` for `RdPaced`: the ledger travels along a chain-idle
segment, by `readyPacedS_watchSegE`. -/
theorem rdPaced_seg (P : Shared) (q : ℕ) (first : Fin 9) (es : List Bool)
    (c c' : Control) (s t : GalilVM)
    (hseg : WatchSegE P q first 2048 es c s c' t) (hidle : t.chain = ChainVM.idle)
    (h : RdPaced c s) : RdPaced c' t := by
  intro n
  obtain ⟨k, hk, hp⟩ := h (n + es.length)
  exact readyPacedS_watchSegE P q first hseg hidle n k hk hp

/-- `ReadyClosure.restart` for `RdPaced`: at a `Restarted`/`StageEntry` state with
a full clock the ledger reduces to the residual `RunEntriesS` datum, by
`readyPacedS_restarted`. -/
theorem rdPaced_restart {raw : List (Fin 2)} (c : Control) (u : GalilVM) (Rad : ℕ)
    (last : Counter) (hclk : c.clock = 2048) (hR : Restarted raw u Rad last)
    (hE : ∀ as : List Bool, PacedL 2048 0 as → RunEntriesS as (searchLens.get u)) :
    RdPaced c u := by
  intro n
  exact ⟨0, by omega, readyPacedS_restarted hR n 0 (fun as _ hp => hE as hp)⟩

#print axioms rdPaced_ready
#print axioms rdPaced_seg
#print axioms rdPaced_restart

/-!
`GalilReplaySpan.ReadyClosure raw P q first 2048 RdPaced` is
`⟨rdPaced_ready, rdPaced_seg …, rdPaced_restart …⟩` — the one-line re-export the
downstream `''_S_of_decodes` consumes.  It is not written here because this file
is checked against a build of `PalPeg.GalilReplaySpan` that predates the
`ReadyClosure` structure; assembling it is a one-liner once the root build is
refreshed.
-/

end PalPeg.CloseoutPreload
