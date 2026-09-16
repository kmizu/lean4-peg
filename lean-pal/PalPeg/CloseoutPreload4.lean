import PalPeg.CloseoutPreload3

/-!
# `CloseoutPreload3.RestartTrace` is false, and the corrected restart datum

The goal was to prove `CloseoutPreload3.RestartTrace raw` and thereby make
`RestartEntryS'` — and with it `readyClosure_C` / `replay_final_of_decodes` —
unconditional.  It cannot be proved: **`RestartTrace` is false as stated**, and
§1 refutes it.  §2–§3 give the corrected datum, at which the whole closure is
re-exported, and §4 reduces that datum to three narrow NAMED contracts about
the entry, with all the bookkeeping (reachability, event count, pacing slack)
discharged.

* §1 **The refutation.**  `RestartTrace` asks for an invariant `Q` that (a)
  satisfies `CloseoutPreload2.TracePreload` — so *every* state in `Q` is the
  endpoint of a `PrepTrace` out of a freshly prepared `.lower` state — and (b)
  holds at the restart state itself.  But a `PrepTrace` never leaves the five
  modes `{lower, lowerHome, copy, home, run}` (`tick_true_mode`,
  `prepTrace_mode`), whereas the restart state is in `.grow`
  (`Restarted` ⇒ `search = begin last radius`, whose mode is `.grow`).  Hence
  `tracePreload_not_grow` and `not_restartTrace`: no `Q` can do both.  (The same
  argument shows `TracePreload` fails at every `.run` state too, so `Q` cannot
  even be closed under `searchStep` — clause (ii) of `RestartTrace` collides
  with clause (i) as soon as one entry is taken.)

* §2 **The repair: condition `TracePreload` on the entry.**  The preload shape
  is only ever *used* at a `.run` entry (`CloseoutPreload2.entryPreload_of_trace`
  applies it under `mode ≠ .run`, `mode' = .run`), so the datum belongs there:
  `TracePreloadE` (below) asks for the prepared-`.lower` witness only at states
  that actually hand over to the DP run.  `entryPreload_of_traceE` /
  `runEntriesS_of_traceE` rebuild `CloseoutPreload.EntryPreload` and
  `RunEntriesS` from it, using the exported `preloadAtEntry_of_trace` and
  `runEntriesS_of_preloadInv` — no change to any existing file.

* §3 `RestartTraceE` — `RestartTrace` with `TracePreload` replaced by
  `TracePreloadE` and the pacing clause at the full slack `2047` — and the
  re-exports `restartEntryS'_of_traceE`, `readyClosure_C_E`,
  `replay_final_of_decodes_E`.  This is the shape the begin → `prepare` linkage
  should be proved in.

* §4 **The reduction.**  `Reach`/`ReachN` (the reflexive-transitive closure of
  `searchStep` with a step count) gives the canonical invariant
  `Qreach u k v as := ∃ j, ReachN j (searchLens.get u) v ∧ dpEntry k ≤ j + as.length
  ∧ PacedL 2048 j as`.  Closure under `searchStep` (`reachN_snoc`), the event
  count and the pacing slack (`pacedL_tail`) are all discharged here;
  `restartTraceE_of_contracts` then assembles `RestartTraceE` from exactly three
  NAMED contracts (§5).

## What is still named

`EntryPrepShapeC raw k` — the begin → `prepare` linkage, now entry-local:

    ∀ u Rad last, Restarted raw u Rad last → StageEntry Rad last →
      ∀ (j : ℕ) (v v' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool)
        (as : List Bool), ReachN j (searchLens.get u) v → searchStep c a v v' →
        v.search.mode ≠ .run → v'.search.mode = .run →
        ∃ (s : State) (lower span n : ℕ) (v0 : SearchVM),
          s.mode = .lower ∧ s.work = ofNat lower ∧ s.span = ofNat span ∧
          s.program.config.tapes 10 = moveRight (write reset 4) ∧
          s.program.config.tapes 7 = reset ∧
          (∀ i : Fin 12, i ≠ 7 → i ≠ 10 → s.program.config.tapes i = reset) ∧
          ((GalilScaffoldPlace.stream s.walker).take (span + 1)).length
            = stageWindow1 (value last).toNat ∧
          v0.toPrep = s ∧ PrepTrace v0 n v

`EntryDebtC raw` — `Canonical v'.search.debt` and
`GalilReplaySpan.stageDebt Rad ((value last).toNat : ℤ) ≤ value v'.search.debt`
at those entries (the `initialDebt`/`grow` ledger: `2 * max k 1` credits are
added by the grow ticks, `grow_span_calibration`).

`EntryDepthC raw` — the entry is reached within the eight preparation events
the ledger's `dpEntry k = 8 + dpEvents (stageWindow1 k)` budgets: `j + 1 ≤ 8`.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload4

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController
open PalPeg.GalilScaffoldPrepareControl (State Tick Run)
open PalPeg.GalilScaffoldCounter (Counter Canonical value ofNat)
open PalPeg.CloseoutReadyStage
open PalPeg.CloseoutRunEntriesS
open PalPeg.CloseoutPreload
open PalPeg.CloseoutPreload2 (PrepTrace dErase prepStep_tick)
open PalPeg.CloseoutDebtAudit (dpEvents stageWindow1 dpEntry)

/-! ## 1. `RestartTrace` is false: a preparation trace never reaches `.grow` -/

/-- The five modes a `true` preparation tick can land in.  `.grow`, `.wait`,
`.double` and the inactive modes are not among them: the preparation phase is
entered from `.grow` by `prepare`, which is *not* a `Tick`. -/
def PrepMode (m : GalilScaffoldSearchFinish.Mode) : Prop :=
  m = .lower ∨ m = .lowerHome ∨ m = .copy ∨ m = .home ∨ m = .run

/-- **A `true` preparation tick lands in a preparation mode.** -/
theorem tick_true_mode {x y : State} (ht : Tick true x y) : PrepMode y.mode := by
  cases ht with
  | lowerBit x hm hp => exact Or.inl hm
  | lowerEnd x hm hp => exact Or.inr (Or.inl rfl)
  | lowerLeft x hm hf hl => exact Or.inr (Or.inl hm)
  | beginCopy x hm hf => exact Or.inr (Or.inr (Or.inl rfl))
  | copyBit x a hm ha hw => exact Or.inr (Or.inr (Or.inl hm))
  | copyEnd x hm he => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | sourceLeft x hm hf hl => exact Or.inr (Or.inr (Or.inr (Or.inl hm)))
  | startRun x hm hf => exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

#print axioms tick_true_mode

/-- **A preparation trace stays in the preparation modes.** -/
theorem prepTrace_mode : ∀ {v w : SearchVM} {n : ℕ}, PrepTrace v n w →
    PrepMode v.search.mode → PrepMode w.search.mode := by
  intro v w n h
  induction h with
  | nil v => exact fun hv => hv
  | cons v v' w n hm hs hr ih =>
    intro _
    obtain ⟨c, a, hstep⟩ := hs
    have hmode : (dErase v'.toPrep).mode = v'.search.mode := rfl
    exact ih (hmode ▸ tick_true_mode (prepStep_tick hm hstep))

#print axioms prepTrace_mode

/-- **`TracePreload` excludes `.grow`.**  Every state of a `TracePreload`
invariant is the endpoint of a preparation trace out of a `.lower` state, hence
its mode is a preparation mode. -/
theorem tracePreload_prepMode {Q : SearchVM → List Bool → Prop} {k : ℕ}
    (htr : PalPeg.CloseoutPreload2.TracePreload Q k) {v : SearchVM} {as : List Bool}
    (hq : Q v as) : PrepMode v.search.mode := by
  obtain ⟨s, lower, span, n, v0, hm, -, -, -, -, -, -, hv0, htrace⟩ := htr v as hq
  refine prepTrace_mode htrace ?_
  have : v0.search.mode = s.mode := by rw [← hv0]; rfl
  exact Or.inl (this.trans hm)

theorem tracePreload_not_grow {Q : SearchVM → List Bool → Prop} {k : ℕ}
    (htr : PalPeg.CloseoutPreload2.TracePreload Q k) {v : SearchVM} {as : List Bool}
    (hq : Q v as) : v.search.mode ≠ .grow := by
  intro hg
  rcases tracePreload_prepMode htr hq with h | h | h | h | h <;> rw [hg] at h <;>
    exact absurd h (by decide)

#print axioms tracePreload_not_grow

/-- The restart state is in `.grow`. -/
theorem restart_mode_grow {raw : List (Fin 2)} {u : GalilVM} {Rad : ℕ} {last : Counter}
    (hR : Restarted raw u Rad last) :
    (searchLens.get u).search.mode = GalilScaffoldSearchFinish.Mode.grow := by
  have hs : u.search = GalilScaffoldSearchFinish.begin last u.radius := hR.2.2.2.2.2.2.1
  show u.search.mode = _
  rw [hs]; rfl

/-- **`CloseoutPreload3.RestartTrace` is false.**  Its clause (i) forbids `.grow`
(`tracePreload_not_grow`), its clause (iv) puts the restart state — which is in
`.grow` — into `Q`. -/
theorem not_restartTrace {raw : List (Fin 2)} {u : GalilVM} {Rad : ℕ} {last : Counter}
    (hR : Restarted raw u Rad last) (hSE : StageEntry Rad last)
    (h : PalPeg.CloseoutPreload3.RestartTrace raw) : False := by
  obtain ⟨Q, htr, -, -, -, -, -, hinit⟩ := h u Rad last hR hSE
  have hq : Q (searchLens.get u) (List.replicate (dpEntry (value last).toNat) false) :=
    hinit 0 _ (by simp) (pacedL_replicate_false 2048 0 _)
  exact tracePreload_not_grow htr hq (restart_mode_grow hR)

#print axioms not_restartTrace

/-! ## 2. The repair: the preload witness only at the `.run` entry -/

/-- **The entry-conditioned restart datum.**  `CloseoutPreload2.TracePreload`
asked the preparation witness of *every* state of the invariant; the witness is
only ever used at a `.run` entry, and that is where it is true. -/
def TracePreloadE (Q : SearchVM → List Bool → Prop) (k : ℕ) : Prop :=
  ∀ (v v' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool),
    Q v (a :: as) → searchStep c a v v' → v.search.mode ≠ .run →
    v'.search.mode = .run →
    ∃ (s : State) (lower span n : ℕ) (v0 : SearchVM),
      s.mode = .lower ∧ s.work = ofNat lower ∧ s.span = ofNat span ∧
      s.program.config.tapes 10 =
        GalilScaffoldTape.moveRight (GalilScaffoldTape.write GalilScaffoldTape.reset 4) ∧
      s.program.config.tapes 7 = GalilScaffoldTape.reset ∧
      (∀ i : Fin 12, i ≠ 7 → i ≠ 10 →
        s.program.config.tapes i = GalilScaffoldTape.reset) ∧
      ((GalilScaffoldPlace.stream s.walker).take (span + 1)).length = stageWindow1 k ∧
      v0.toPrep = s ∧ PrepTrace v0 n v

/-- Every `TracePreload` invariant is entry-conditioned. -/
theorem tracePreloadE_of_tracePreload {Q : SearchVM → List Bool → Prop} {k : ℕ}
    (htr : PalPeg.CloseoutPreload2.TracePreload Q k) : TracePreloadE Q k :=
  fun v _ _ a as hq _ _ _ => htr v (a :: as) hq

/-- **`CloseoutPreload.EntryPreload` from the entry-conditioned datum.**  The
preload half is `CloseoutPreload2.preloadAtEntry_of_trace`. -/
theorem entryPreload_of_traceE {Q : SearchVM → List Bool → Prop} {Rad k slack : ℕ}
    (htr : TracePreloadE Q k)
    (hnext : ∀ (v v' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool),
      Q v (a :: as) → searchStep c a v v' → Q v' as)
    (hcan : ∀ (v v' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool),
      Q v (a :: as) → searchStep c a v v' → v.search.mode ≠ .run →
        v'.search.mode = .run → Canonical v'.search.debt)
    (hdebt : ∀ (v v' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool),
      Q v (a :: as) → searchStep c a v v' → v.search.mode ≠ .run →
        v'.search.mode = .run →
          PalPeg.GalilReplaySpan.stageDebt Rad (k : ℤ) ≤ value v'.search.debt)
    (hlen : ∀ (v v' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool),
      Q v (a :: as) → searchStep c a v v' → v.search.mode ≠ .run →
        v'.search.mode = .run → dpEvents (stageWindow1 k) ≤ as.length)
    (hpaced : ∀ (v v' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool),
      Q v (a :: as) → searchStep c a v v' → v.search.mode ≠ .run →
        v'.search.mode = .run → PacedL 2048 slack as) :
    EntryPreload Q Rad k slack := by
  intro v v' c a as hq hstep
  refine ⟨fun hne hr => ⟨?_, hcan v v' c a as hq hstep hne hr,
    hdebt v v' c a as hq hstep hne hr, hlen v v' c a as hq hstep hne hr,
    hpaced v v' c a as hq hstep hne hr⟩,
    hnext v v' c a as hq hstep⟩
  obtain ⟨s, lower, span, n, v0, hm, hw, hspan, h10, h7, hother, hcal, hv0, htrace⟩ :=
    htr v v' c a as hq hstep hne hr
  exact PalPeg.CloseoutPreload2.preloadAtEntry_of_trace s lower span n k hm hw hspan
    h10 h7 hother hcal ⟨v0, hv0, htrace⟩ hstep hne hr

#print axioms entryPreload_of_traceE

/-- **`RunEntriesS` for every event list, from the entry-conditioned datum.** -/
theorem runEntriesS_of_traceE {Q : SearchVM → List Bool → Prop} {Rad k slack : ℕ}
    (hstage : 3 * Rad ≤ 5 * k) (hslack : slack ≤ 2047)
    (htr : TracePreloadE Q k)
    (hnext : ∀ (v v' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool),
      Q v (a :: as) → searchStep c a v v' → Q v' as)
    (hcan : ∀ (v v' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool),
      Q v (a :: as) → searchStep c a v v' → v.search.mode ≠ .run →
        v'.search.mode = .run → Canonical v'.search.debt)
    (hdebt : ∀ (v v' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool),
      Q v (a :: as) → searchStep c a v v' → v.search.mode ≠ .run →
        v'.search.mode = .run →
          PalPeg.GalilReplaySpan.stageDebt Rad (k : ℤ) ≤ value v'.search.debt)
    (hlen : ∀ (v v' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool),
      Q v (a :: as) → searchStep c a v v' → v.search.mode ≠ .run →
        v'.search.mode = .run → dpEvents (stageWindow1 k) ≤ as.length)
    (hpaced : ∀ (v v' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool),
      Q v (a :: as) → searchStep c a v v' → v.search.mode ≠ .run →
        v'.search.mode = .run → PacedL 2048 slack as) :
    ∀ (as : List Bool) (v : SearchVM), Q v as → RunEntriesS as v :=
  runEntriesS_of_preloadInv hstage hslack
    (entryPreload_of_traceE htr hnext hcan hdebt hlen hpaced)

#print axioms runEntriesS_of_traceE

/-! ## 3. The corrected restart datum, and the closure at it -/

/-- **`RestartTrace`, corrected.**  Clause (i) is now entry-conditioned (§2), and
the pacing clause is at the full slack the DP entry tolerates
(`runEntriesS_of_preloadInv` allows any `slack ≤ 2047`). -/
def RestartTraceE (raw : List (Fin 2)) : Prop :=
  ∀ (u : GalilVM) (Rad : ℕ) (last : Counter),
    Restarted raw u Rad last → StageEntry Rad last →
    ∃ Q : SearchVM → List Bool → Prop,
      TracePreloadE Q (value last).toNat ∧
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
            dpEvents (stageWindow1 (value last).toNat) ≤ as.length) ∧
      (∀ (v v' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool),
        Q v (a :: as) → searchStep c a v v' → v.search.mode ≠ .run →
          v'.search.mode = .run → PacedL 2048 2047 as) ∧
      (∀ (m : ℕ) (as : List Bool),
        dpEntry (value last).toNat + m ≤ as.length → PacedL 2048 0 as →
        Q (searchLens.get u) as)

/-- **`RestartEntryS'` from the corrected datum.** -/
theorem restartEntryS'_of_traceE {raw : List (Fin 2)} (h : RestartTraceE raw) :
    PalPeg.CloseoutPreload2.RestartEntryS' raw := by
  intro u Rad last hR hSE m as hlen hpaced
  obtain ⟨Q, htr, hnext, hcan, hdebt, hlenQ, hpacedQ, hinit⟩ := h u Rad last hR hSE
  have hval : value last = ((value last).toNat : ℤ) :=
    (Int.toNat_of_nonneg hR.2.2.2.2.2.2.2.2.2).symm
  have hstage : 3 * Rad ≤ 5 * (value last).toNat := hSE _ hval
  exact runEntriesS_of_traceE (Rad := Rad) (k := (value last).toNat) (slack := 2047)
    hstage (le_refl _) htr hnext hcan hdebt hlenQ hpacedQ as (searchLens.get u)
    (hinit m as hlen hpaced)

#print axioms restartEntryS'_of_traceE

/-- `GalilReplaySpan.ReadyClosure` for `RdPaced`, from the corrected datum. -/
theorem readyClosure_C_E (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    (hE : RestartTraceE raw) :
    PalPeg.GalilReplaySpan.ReadyClosure raw P q first 2048 RdPaced :=
  PalPeg.CloseoutPreload2.readyClosure_paced raw P q first (restartEntryS'_of_traceE hE)

#print axioms readyClosure_C_E

/-- The final replay theorem with the concrete ledger, at the corrected datum. -/
def replay_final_of_decodes_E (raw : List (Fin 2)) (P : Shared)
    (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM)
    (q : ℕ) (first : Fin 9)
    (hex : ∀ s, P.replayExhausted s = GalilScaffoldCounter.zero s.replay)
    (hsearch : ∀ s : GalilVM, PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect P a s v)
    (hE : RestartTraceE raw)
    (hdec : Decodes P)
    (hbudget : PalPeg.GalilReplaySpan.ReplayBudgetRD raw P q first 2048)
    (hrs : PalPeg.GalilReplaySpan.RestartShapeL P)
    (r : ℕ) (hr0 : 0 < r) (c : Control) (t : GalilVM)
    (hm : c.mode = Mode.scan) (hc : c.clock = 2048) (hrpl : c.replaying = true)
    (hR : Restarted raw t 0 GalilScaffoldCounter.reset) (hrep : t.replay = ofNat r)
    (hM : MInv raw c t) (hfr : Frontier t) (hsi : ShiftIdle t) :=
  PalPeg.GalilReplaySpan.replay_after_fallback_general''_R_of_decodes
    raw P hP hP' q first hex hsearch (readyClosure_C_E raw P q first hE) hdec hbudget hrs
    r hr0 c t hm hc hrpl hR hrep hM hfr hsi

#print axioms replay_final_of_decodes_E

/-! ## 4. The canonical invariant: reachability from the restart -/

/-- `searchStep`-reachability with a step count. -/
inductive ReachN : ℕ → SearchVM → SearchVM → Prop
  | refl (v : SearchVM) : ReachN 0 v v
  | step (j : ℕ) (v v' w : SearchVM)
      (h : ∃ (c : GalilScaffoldPlace.Place) (a : Bool), searchStep c a v v')
      (hr : ReachN j v' w) : ReachN (j + 1) v w

/-- Reachability extends on the right. -/
theorem reachN_snoc : ∀ {j : ℕ} {u v v' : SearchVM}, ReachN j u v →
    (∃ (c : GalilScaffoldPlace.Place) (a : Bool), searchStep c a v v') →
    ReachN (j + 1) u v' := by
  intro j u v v' h
  induction h with
  | refl v => intro hs; exact .step 0 _ _ _ hs (.refl _)
  | step j x x' w hs' hr ih =>
    intro hs
    exact .step (j + 1) _ _ _ hs' (ih hs)

#print axioms reachN_snoc

/-- **Pacing survives dropping the head event, at the cost of one unit of
slack.**  The converse of `pacedL_false` / `pacedL_true`. -/
theorem pacedL_tail {d k : ℕ} {a : Bool} {as : List Bool}
    (h : PacedL d k (a :: as)) : PacedL d (k + 1) as := by
  intro n
  have hle : (as.take n).count true ≤ (((a :: as)).take (n + 1)).count true := by
    cases a <;> simp [List.take_succ_cons]
  calc d * ((as.take n).count true)
      ≤ d * ((((a :: as)).take (n + 1)).count true) := Nat.mul_le_mul_left _ hle
    _ ≤ n + 1 + k := h (n + 1)
    _ = n + (k + 1) := by omega

#print axioms pacedL_tail

/-- **The canonical restart invariant.**  The state is reachable from the
restart in `j` steps, the ledger's entry budget `dpEntry k` is still covered by
the steps already taken plus the events still ahead, and the event list is paced
with `j` units of slack. -/
def Qreach (u : GalilVM) (k : ℕ) (v : SearchVM) (as : List Bool) : Prop :=
  ∃ j : ℕ, ReachN j (searchLens.get u) v ∧ dpEntry k ≤ j + as.length ∧ PacedL 2048 j as

/-- `Qreach` is closed under `searchStep`: the step count and the event count
trade off exactly, and the slack grows by one (`pacedL_tail`). -/
theorem qreach_next (u : GalilVM) (k : ℕ) (v v' : SearchVM)
    (c : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool)
    (hq : Qreach u k v (a :: as)) (hs : searchStep c a v v') : Qreach u k v' as := by
  obtain ⟨j, hreach, hlen, hpaced⟩ := hq
  refine ⟨j + 1, reachN_snoc hreach ⟨c, a, hs⟩, ?_, pacedL_tail hpaced⟩
  simp only [List.length_cons] at hlen
  omega

#print axioms qreach_next

/-- `Qreach` holds at the restart for every list the ledger's entry bound
covers. -/
theorem qreach_init (u : GalilVM) (k m : ℕ) (as : List Bool)
    (hlen : dpEntry k + m ≤ as.length) (hpaced : PacedL 2048 0 as) :
    Qreach u k (searchLens.get u) as :=
  ⟨0, .refl _, by omega, hpaced⟩

/-- **The event count at an entry, discharged from the depth contract.**  With
`dpEntry k = 8 + dpEvents (stageWindow1 k)` and an entry at depth `j + 1 ≤ 8`,
the charged prefix of the stage still fits in the events ahead. -/
theorem qreach_entry_len {u : GalilVM} {k j : ℕ} {v : SearchVM} {a : Bool}
    {as : List Bool} (hlen : dpEntry k ≤ j + (a :: as).length) (hdepth : j + 1 ≤ 8) :
    dpEvents (stageWindow1 k) ≤ as.length := by
  simp only [List.length_cons] at hlen
  have : dpEntry k = 8 + dpEvents (stageWindow1 k) := rfl
  omega

/-- The pacing at an entry: the slack never exceeds the depth, hence `2047`. -/
theorem qreach_entry_paced {u : GalilVM} {k j : ℕ} {v : SearchVM} {a : Bool}
    {as : List Bool} (hpaced : PacedL 2048 j (a :: as)) (hdepth : j + 1 ≤ 8) :
    PacedL 2048 2047 as :=
  pacedL_mono (by omega) (pacedL_tail hpaced)

#print axioms qreach_entry_len
#print axioms qreach_entry_paced

/-! ## 5. The three NAMED entry contracts, and the assembly -/

/-- **NAMED — the begin → `prepare` linkage, entry-local.**  At a `.run` entry
reached from the restart, the preparation witness: the freshly prepared `.lower`
state with the calibrated window, and a preparation trace from it to the
predecessor of the entry.  (`CloseoutPreload3.grow_span_calibration` supplies the
span, `stageCalibration1_of_long` the window length; what is missing is the
`prepare` dispatch itself and the identification of the reached `.lower` state.) -/
def EntryPrepShapeC (raw : List (Fin 2)) : Prop :=
  ∀ (u : GalilVM) (Rad : ℕ) (last : Counter),
    Restarted raw u Rad last → StageEntry Rad last →
    ∀ (j : ℕ) (v v' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool)
      (as : List Bool),
      ReachN j (searchLens.get u) v → searchStep c a v v' →
      v.search.mode ≠ .run → v'.search.mode = .run →
      ∃ (s : State) (lower span n : ℕ) (v0 : SearchVM),
        s.mode = .lower ∧ s.work = ofNat lower ∧ s.span = ofNat span ∧
        s.program.config.tapes 10 =
          GalilScaffoldTape.moveRight (GalilScaffoldTape.write GalilScaffoldTape.reset 4) ∧
        s.program.config.tapes 7 = GalilScaffoldTape.reset ∧
        (∀ i : Fin 12, i ≠ 7 → i ≠ 10 →
          s.program.config.tapes i = GalilScaffoldTape.reset) ∧
        ((GalilScaffoldPlace.stream s.walker).take (span + 1)).length =
          stageWindow1 (value last).toNat ∧
        v0.toPrep = s ∧ PrepTrace v0 n v

/-- **NAMED — the entry debt.**  The `initialDebt radius` at the restart plus the
`2 * max k 1` credits of the grow ticks (`grow_span_calibration`) cover the
stage debt at the hand-over. -/
def EntryDebtC (raw : List (Fin 2)) : Prop :=
  ∀ (u : GalilVM) (Rad : ℕ) (last : Counter),
    Restarted raw u Rad last → StageEntry Rad last →
    ∀ (j : ℕ) (v v' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool)
      (as : List Bool),
      ReachN j (searchLens.get u) v → searchStep c a v v' →
      v.search.mode ≠ .run → v'.search.mode = .run →
      Canonical v'.search.debt ∧
        PalPeg.GalilReplaySpan.stageDebt Rad (((value last).toNat : ℕ) : ℤ)
          ≤ value v'.search.debt

/-- **NAMED — the entry depth.**  The hand-over happens within the eight
preparation events the ledger budgets in `dpEntry k = 8 + dpEvents
(stageWindow1 k)`. -/
def EntryDepthC (raw : List (Fin 2)) : Prop :=
  ∀ (u : GalilVM) (Rad : ℕ) (last : Counter),
    Restarted raw u Rad last → StageEntry Rad last →
    ∀ (j : ℕ) (v v' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool)
      (as : List Bool),
      ReachN j (searchLens.get u) v → searchStep c a v v' →
      v.search.mode ≠ .run → v'.search.mode = .run → j + 1 ≤ 8

/-- **The assembly.**  `RestartTraceE` from the three entry contracts: the
invariant is `Qreach`, whose closure, event count and pacing are §4. -/
theorem restartTraceE_of_contracts {raw : List (Fin 2)}
    (hshape : EntryPrepShapeC raw) (hdebt : EntryDebtC raw) (hdepth : EntryDepthC raw) :
    RestartTraceE raw := by
  intro u Rad last hR hSE
  refine ⟨Qreach u (value last).toNat, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v v' c a as hq hs hne hr
    obtain ⟨j, hreach, -, -⟩ := hq
    exact hshape u Rad last hR hSE j v v' c a as hreach hs hne hr
  · intro v v' c a as hq hs
    exact qreach_next u _ v v' c a as hq hs
  · intro v v' c a as hq hs hne hr
    obtain ⟨j, hreach, -, -⟩ := hq
    exact (hdebt u Rad last hR hSE j v v' c a as hreach hs hne hr).1
  · intro v v' c a as hq hs hne hr
    obtain ⟨j, hreach, -, -⟩ := hq
    exact (hdebt u Rad last hR hSE j v v' c a as hreach hs hne hr).2
  · intro v v' c a as hq hs hne hr
    obtain ⟨j, hreach, hlen, -⟩ := hq
    exact qreach_entry_len (u := u) (v := v) hlen
      (hdepth u Rad last hR hSE j v v' c a as hreach hs hne hr)
  · intro v v' c a as hq hs hne hr
    obtain ⟨j, hreach, -, hpaced⟩ := hq
    exact qreach_entry_paced (u := u) (k := (value last).toNat) (v := v) hpaced
      (hdepth u Rad last hR hSE j v v' c a as hreach hs hne hr)
  · intro m as hlen hpaced
    exact qreach_init u _ m as hlen hpaced

#print axioms restartTraceE_of_contracts

/-- `GalilReplaySpan.ReadyClosure` for `RdPaced` from the three entry
contracts — the shape `readyClosure_C` should have had. -/
theorem readyClosure_C_of_contracts (raw : List (Fin 2)) (P : Shared) (q : ℕ)
    (first : Fin 9) (hshape : EntryPrepShapeC raw) (hdebt : EntryDebtC raw)
    (hdepth : EntryDepthC raw) :
    PalPeg.GalilReplaySpan.ReadyClosure raw P q first 2048 RdPaced :=
  readyClosure_C_E raw P q first (restartTraceE_of_contracts hshape hdebt hdepth)

#print axioms readyClosure_C_of_contracts

end PalPeg.CloseoutPreload4
