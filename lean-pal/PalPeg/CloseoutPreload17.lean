import PalPeg.CloseoutPreload16

/-!
# The paced form of `PostRun`, and the `.double` consumption leg

`CloseoutPreload16` §5 records why `CloseoutPreload8.PostRun` cannot be proved as
stated: it quantifies over an *arbitrary* event list `as`, while every route to a
`DpSafeStage` witness at a later `.run` entry charges the events it meets against
the clock.  This file does two things.

* §1 `PostRunP` — the same contract with the pacing premise the consumers can
  actually supply, and the whole consumption chain re-threaded through it:
  `runEntriesS_of_stageInv2P` / `runEntriesS_of_restartS2P` /
  `readyClosure_S2P` / `replay_final_of_decodes_S2P` (the restart stage) and
  `runEntriesS_of_stageInvPP` / `runEntriesS_of_double_exitP` (the doubling
  stage).  Every application site of `PostRun` in `CloseoutPreload11` /
  `CloseoutPreload12` sits under a `StagePrep2` witness, whose pacing clause
  `PacedL 2048 0 (bs ++ a :: as)` hands the suffix `as` a `PacedL 2048 _`
  (`CloseoutPreload5.pacedL_suffix`), so **replacing `PostRun` by `PostRunP`
  costs nothing** — §1 proves exactly the same conclusions.

* §2 the `.double` consumption leg, the machine fact `CloseoutPreload16` §5
  names as missing: `CloseoutPreload14.wait_exit_double` lands at
  `work = ofNat mw`, `span = reset`, `quarter = 0`, whereas
  `CloseoutPreload12.runEntriesS_of_double_exit` consumes a *spent* `.double`
  state (`positive work = false`).  `DoubleTrace` is the `.double`-only trace on
  `SearchVM`, `doubleTrace_run` lifts it to `GalilScaffoldDouble.Run`, and
  `double_complete` runs `work` down to zero in exactly `mw` ticks, leaving
  `span = ofNat (2 * mw)` — the doubled window — with the frame (`lower`,
  `walker`, `dp`) untouched and the debt controlled by the quarter-cell balance
  (`double_exit_debt`).  `double_leg_entries` chains that into §1.

§3 records what is still missing for `postRunP_of_machine`.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload17

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController
open PalPeg.GalilScaffoldSearchFinish (Mode)
open PalPeg.GalilScaffoldCounter (Counter Canonical value ofNat positive reset)
open PalPeg.CloseoutReadyStage (DpSafeStage PacedL RunEntriesS)
open PalPeg.CloseoutPreload (RdPaced rdPaced_ready rdPaced_seg rdPaced_restart)
open PalPeg.CloseoutDebtAudit (dpEvents)
open PalPeg.CloseoutPreload5 (pacedL_suffix append_cons_eq)
open PalPeg.CloseoutPreload6 (prepLen)
open PalPeg.CloseoutPreload8 (BeginAt CentreLongAt DepthAt beginAt_of_restarted)
open PalPeg.CloseoutPreload10 (PrepAt prepAt_of_double_exit)
open PalPeg.CloseoutPreload11 (StagePrep2 StageInv2 stagePrep_next2 stageCredit
  dpSafe_of_stagePrep2 RestartS2 stageStart_of_double_exit)
open PalPeg.CloseoutPreload12 (dpSafe_of_stagePrepP)
open PalPeg.GalilReplaySpan (stageDebt)

/-! ## 1. `PostRun`, with the pacing the consumers supply -/

/-- **NAMED — the paced post-run contract.**  `CloseoutPreload8.PostRun` with the
premise that the events charged are clock-paced at *some* phase.  This is the
strongest form the `.run` leg can hope to establish (an unpaced suffix carries no
debt at all, `CloseoutPreload16` §5) and, by §1 below, the weakest form the
stage chain needs. -/
def PostRunP : Prop :=
  ∀ (v : SearchVM) (as : List Bool) (slack : ℕ), v.search.mode = Mode.run →
    DpSafeStage v as → PacedL 2048 slack as → RunEntriesS as v

/-- `PostRun` is stronger: it does not look at the pacing at all. -/
theorem postRunP_of_postRun (h : PalPeg.CloseoutPreload8.PostRun) : PostRunP :=
  fun v as _ hm hsafe _ => h v as hm hsafe

#print axioms postRunP_of_postRun

/-- `CloseoutPreload11.runEntriesS_of_stageInv2`, on `PostRunP`.  The pacing the
contract now asks for is read off the stage's own `StagePrep2` witness. -/
theorem runEntriesS_of_stageInv2P {u : GalilVM} {w : SearchVM} {k m Rad D : ℕ}
    (hb : BeginAt k Rad w) (hm : m = 8 * max k 1) (hstage : 3 * Rad ≤ 5 * k)
    (hcl : CentreLongAt w k) (hdep : DepthAt w D) (hD : D ≤ prepLen k)
    (hpost : PostRunP) :
    ∀ (as : List Bool) (v : SearchVM), StageInv2 k m D w v as → RunEntriesS as v := by
  intro as
  induction as with
  | nil => intro v _; trivial
  | cons a as ih =>
    intro v hq
    rcases hq with hq | hq
    · intro c v' hstep
      by_cases hr : v'.search.mode = Mode.run
      · have hsafe := dpSafe_of_stagePrep2 (u := u) hb hm hstage hcl hdep hD hq hstep hr
        obtain ⟨bs, -, -, hpaced⟩ := hq
        have hpaced' : PacedL 2048 0 ((bs ++ [a]) ++ as) := by
          rw [← append_cons_eq]; exact hpaced
        exact ⟨fun _ _ _ => hsafe, hpost v' as _ hr hsafe (pacedL_suffix hpaced')⟩
      · exact ⟨fun _ _ h => absurd h hr,
          ih v' (Or.inl (stagePrep_next2 hq hstep hr))⟩
    · exact hq

#print axioms runEntriesS_of_stageInv2P

/-- `CloseoutPreload11.runEntriesS_of_restartS2`, on `PostRunP`. -/
theorem runEntriesS_of_restartS2P {raw : List (Fin 2)} {u : GalilVM} {Rad D : ℕ}
    {last : Counter} (hR : Restarted raw u Rad last) (hSE : StageEntry Rad last)
    (hcl : CentreLongAt (searchLens.get u) (value last).toNat)
    (hdep : DepthAt (searchLens.get u) D) (hD : D ≤ prepLen (value last).toNat)
    (hpost : PostRunP) :
    ∀ (as : List Bool),
      D + dpEvents (8 * max (value last).toNat 1 + 1) ≤ as.length → PacedL 2048 0 as →
      RunEntriesS as (searchLens.get u) := by
  have hval : value last = ((value last).toNat : ℤ) :=
    (Int.toNat_of_nonneg hR.2.2.2.2.2.2.2.2.2).symm
  have hstage : 3 * Rad ≤ 5 * (value last).toNat := hSE _ hval
  intro as hlen hpaced
  refine runEntriesS_of_stageInv2P (u := u) (beginAt_of_restarted hR) rfl hstage hcl hdep hD
    hpost as _ (Or.inl ⟨[], .nil _ ?_, by simpa using hlen, by simpa using hpaced⟩)
  rw [(PalPeg.CloseoutPreload5.restart_facts hR).1]
  decide

#print axioms runEntriesS_of_restartS2P

/-- **`GalilReplaySpan.ReadyClosure` for `RdPaced`, on `PostRunP`.** -/
theorem readyClosure_S2P (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    (hpost : PostRunP) (h : RestartS2 raw) :
    PalPeg.GalilReplaySpan.ReadyClosure raw P q first 2048 RdPaced where
  ready := fun c s hs => rdPaced_ready c s hs
  seg := fun es c c' s t hseg hidle hs => rdPaced_seg P q first es c c' s t hseg hidle hs
  restart := fun c u Rad last _ hclk hR hSE => by
    obtain ⟨D, hD, hcl, hdep⟩ := h u Rad last hR hSE
    exact rdPaced_restart c u Rad last
      (D + dpEvents (8 * max (value last).toNat 1 + 1)) hclk hR
      (fun m as hlen hp =>
        runEntriesS_of_restartS2P hR hSE hcl hdep hD hpost as (by omega) hp)

#print axioms readyClosure_S2P

/-- The final replay theorem, on `PostRunP`. -/
def replay_final_of_decodes_S2P (raw : List (Fin 2)) (P : Shared)
    (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM)
    (q : ℕ) (first : Fin 9)
    (hex : ∀ s, P.replayExhausted s = GalilScaffoldCounter.zero s.replay)
    (hsearch : ∀ s : GalilVM, PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect P a s v)
    (hpost : PostRunP) (hS : RestartS2 raw)
    (hdec : Decodes P)
    (hbudget : PalPeg.GalilReplaySpan.ReplayBudgetRD raw P q first 2048)
    (hrs : PalPeg.GalilReplaySpan.RestartShapeL P)
    (r : ℕ) (hr0 : 0 < r) (c : Control) (t : GalilVM)
    (hm : c.mode = Mode.scan) (hc : c.clock = 2048) (hrpl : c.replaying = true)
    (hR : Restarted raw t 0 GalilScaffoldCounter.reset) (hrep : t.replay = ofNat r)
    (hM : MInv raw c t) (hfr : Frontier t) (hsi : ShiftIdle t) :=
  PalPeg.GalilReplaySpan.replay_after_fallback_general''_R_of_decodes
    raw P hP hP' q first hex hsearch (readyClosure_S2P raw P q first hpost hS) hdec hbudget hrs
    r hr0 c t hm hc hrpl hR hrep hM hfr hsi

#print axioms replay_final_of_decodes_S2P

/-- `CloseoutPreload12.runEntriesS_of_stageInvP`, on `PostRunP`. -/
theorem runEntriesS_of_stageInvPP {k m Rad D : ℕ} {v : SearchVM}
    (hp : PrepAt k m v) (hstage : 3 * Rad ≤ 5 * k) (hcal : 8 * max k 1 ≤ m)
    (hE : stageDebt Rad (k : ℤ) + (stageCredit k m : ℤ) ≤ value v.search.debt)
    (hdep : DepthAt v D) (hD : D ≤ prepLen k) (hpost : PostRunP) :
    ∀ (as : List Bool) (x : SearchVM), StageInv2 k m D v x as → RunEntriesS as x := by
  intro as
  induction as with
  | nil => intro x _; trivial
  | cons a as ih =>
    intro x hq
    rcases hq with hq | hq
    · intro c x' hstep
      by_cases hr : x'.search.mode = Mode.run
      · have hsafe := dpSafe_of_stagePrepP hp hstage hcal hE hdep hD hq hstep hr
        obtain ⟨bs, -, -, hpaced⟩ := hq
        have hpaced' : PacedL 2048 0 ((bs ++ [a]) ++ as) := by
          rw [← append_cons_eq]; exact hpaced
        exact ⟨fun _ _ _ => hsafe, hpost x' as _ hr hsafe (pacedL_suffix hpaced')⟩
      · exact ⟨fun _ _ h => absurd h hr, ih x' (Or.inl (stagePrep_next2 hq hstep hr))⟩
    · exact hq

#print axioms runEntriesS_of_stageInvPP

/-- `CloseoutPreload12.runEntriesS_of_double_exit`, on `PostRunP`. -/
theorem runEntriesS_of_double_exitP {c : GalilScaffoldPlace.Place} {t t' : SearchVM}
    {a : Bool} {k m Rad D : ℕ}
    (htm : t.search.mode = Mode.double)
    (htw : positive t.search.work = false)
    (hsp : t.search.span = ofNat m) (hlow : t.lower = ofNat k)
    (hcal : 8 * max k 1 ≤ m) (hc : Canonical t.search.debt)
    (hstage : 3 * Rad ≤ 5 * k)
    (hE : stageDebt Rad (k : ℤ) + (stageCredit k m : ℤ) + 1 ≤ value t.search.debt)
    (hs : searchStep c a t t')
    (hdep : DepthAt t' D) (hD : D ≤ prepLen k) (hpost : PostRunP) :
    ∀ (as : List Bool),
      D + dpEvents (m + 1) ≤ as.length → PacedL 2048 0 as → RunEntriesS as t' := by
  have hst := stageStart_of_double_exit (E := stageDebt Rad (k : ℤ) + (stageCredit k m : ℤ))
    htm htw hsp hlow hcal hc hE hs
  obtain ⟨hprep, -, -⟩ := prepAt_of_double_exit htm htw hsp hlow hc hs
  intro as hlen hpaced
  refine runEntriesS_of_stageInvPP hprep hstage hcal hst.debt hdep hD hpost as _
    (Or.inl ⟨[], .nil _ ?_, by simpa using hlen, by simpa using hpaced⟩)
  rw [hprep.mode]; decide

#print axioms runEntriesS_of_double_exitP

/-! ## 2. The `.double` consumption leg -/

/-- Consecutive ticks all taken in `.double` mode with work still positive. -/
inductive DoubleTrace : List Bool → SearchVM → SearchVM → Prop
  | nil (v : SearchVM) : DoubleTrace [] v v
  | cons (c : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool) (v v' t : SearchVM)
      (hm : v.search.mode = Mode.double) (hp : positive v.search.work = true)
      (hs : searchStep c a v v')
      (hr : DoubleTrace as v' t) : DoubleTrace (a :: as) v t

/-- A single `.double` tick with work still positive, unfolded. -/
theorem double_step_pos {c : GalilScaffoldPlace.Place} {a : Bool} {v v' : SearchVM}
    (hm : v.search.mode = Mode.double) (hp : positive v.search.work = true)
    (hs : searchStep c a v v') :
    v' = {v with
      search := GalilScaffoldSearchRun.advance a (GalilScaffoldDouble.step v.search)} := by
  unfold searchStep at hs
  rw [hm] at hs
  simpa [hp] using hs

#print axioms double_step_pos

/-- **The `.double` leg is `GalilScaffoldDouble.Run` on the search projection.** -/
theorem doubleTrace_run {as : List Bool} {v t : SearchVM} (hr : DoubleTrace as v t)
    (hmt : t.search.mode = Mode.double) (hwt : positive t.search.work = false) :
    GalilScaffoldDouble.Run v.search as t.search := by
  induction hr with
  | nil v => exact .stop _ hmt hwt
  | cons c a as v v' t hm hp hs hrest ih =>
      have he : v'.search
          = GalilScaffoldSearchRun.advance a (GalilScaffoldDouble.step v.search) := by
        rw [double_step_pos hm hp hs]
      refine .next _ _ a as hm hp ?_
      rw [← he]
      exact ih hmt hwt

#print axioms doubleTrace_run

/-- **NAMED — the `.double` phase spends its work.**  From the shape
`CloseoutPreload14.wait_exit_double` leaves (`work = ofNat mw`, `span = reset`)
the doubling phase runs `work` down to zero in exactly `mw` ticks, whatever the
events are, leaving the doubled window in `span` and the frame untouched.  This
is the leg `CloseoutPreload16` §5 names as missing between `wait_exit_double`
and `CloseoutPreload12.runEntriesS_of_double_exit`. -/
theorem double_complete (c : GalilScaffoldPlace.Place) :
    ∀ (as : List Bool) (v : SearchVM) (span : ℕ),
      v.search.mode = Mode.double → v.search.work = ofNat as.length →
      v.search.span = ofNat span →
      ∃ t, DoubleTrace as v t ∧ t.search.mode = Mode.double ∧
        positive t.search.work = false ∧
        t.search.span = ofNat (span + 2 * as.length) ∧
        t.lower = v.lower ∧ t.walker = v.walker ∧ t.dp = v.dp := by
  intro as
  induction as with
  | nil =>
      intro v span hm hw hsp
      exact ⟨v, .nil v, hm, by simp [hw, positive, ofNat], by simpa using hsp,
        rfl, rfl, rfl⟩
  | cons a as ih =>
      intro v span hm hw hsp
      set v' : SearchVM := {v with
        search := GalilScaffoldSearchRun.advance a (GalilScaffoldDouble.step v.search)}
        with hv'
      have hpos : positive v.search.work = true := by
        simp [hw, positive, ofNat, List.replicate_succ]
      have hstep : searchStep c a v v' := by
        unfold searchStep
        rw [hm]
        simpa [hpos] using hv'
      have hm' : v'.search.mode = Mode.double := by
        cases a <;>
          simpa [hv', GalilScaffoldSearchRun.advance, GalilScaffoldDouble.step] using hm
      have hw' : v'.search.work = ofNat as.length := by
        cases a <;>
          simp [hv', GalilScaffoldSearchRun.advance, GalilScaffoldDouble.step, hw,
            GalilScaffoldCounter.dec_ofNat_succ]
      have hsp' : v'.search.span = ofNat (span + 2) := by
        cases a <;>
          simp [hv', GalilScaffoldSearchRun.advance, GalilScaffoldDouble.step, hsp,
            GalilScaffoldCounter.inc_ofNat, Nat.add_assoc]
      obtain ⟨t, hr, htm, htw, hts, htl, htwk, htdp⟩ := ih v' (span + 2) hm' hw' hsp'
      refine ⟨t, .cons c a as v v' t hm hpos hstep hr, htm, htw, ?_, ?_, ?_, ?_⟩
      · rw [hts]; congr 1; simp; omega
      · rw [htl]
      · rw [htwk]
      · rw [htdp]

#print axioms double_complete

/-- **The debt at the `.double` exit.**  `GalilScaffoldDouble.balance` on the
lifted trace: the quarter cell credits one unit of debt per four ticks, each
comparison spends one. -/
theorem double_exit_debt {as : List Bool} {v t : SearchVM} (hr : DoubleTrace as v t)
    (hmt : t.search.mode = Mode.double) (hwt : positive t.search.work = false) :
    4 * value t.search.debt + t.search.quarter.val
      = 4 * value v.search.debt + v.search.quarter.val + as.length
        - 4 * (as.count true : ℤ) :=
  GalilScaffoldDouble.balance (doubleTrace_run hr hmt hwt)

#print axioms double_exit_debt

/-- The `.double` exit is canonical if the entry was. -/
theorem double_exit_canonical {as : List Bool} {v t : SearchVM} (hr : DoubleTrace as v t)
    (hmt : t.search.mode = Mode.double) (hwt : positive t.search.work = false)
    (hc : Canonical v.search.debt) : Canonical t.search.debt :=
  GalilScaffoldDouble.canonical (doubleTrace_run hr hmt hwt) hc

#print axioms double_exit_canonical

/-- **NAMED — the `.double` phase spends its work, at the shape
`CloseoutPreload14.wait_exit_double` leaves.**  `span = reset` is `ofNat 0`, so
the doubled window is exactly `2 * mw`. -/
theorem double_spends (c : GalilScaffoldPlace.Place) {mw : ℕ} {bs : List Bool}
    {v : SearchVM} (hm : v.search.mode = Mode.double) (hw : v.search.work = ofNat mw)
    (hsp : v.search.span = reset) (hlen : bs.length = mw) :
    ∃ t, DoubleTrace bs v t ∧ t.search.mode = Mode.double ∧
      positive t.search.work = false ∧ t.search.span = ofNat (2 * mw) ∧
      t.lower = v.lower ∧ t.walker = v.walker ∧ t.dp = v.dp := by
  obtain ⟨t, hr, htm, htw, hts, htl, htwk, htdp⟩ :=
    double_complete c bs v 0 hm (by rw [hw, hlen]) (by rw [hsp]; rfl)
  exact ⟨t, hr, htm, htw, by rw [hts, hlen]; congr 1; omega, htl, htwk, htdp⟩

#print axioms double_spends

/-- **NAMED — the spent `.double` state dispatches into the next stage.**  This
is `runEntriesS_of_double_exitP` at the window `2 * mw` produced by
`double_spends`: the leg `CloseoutPreload16` §5 names as missing, now between
`CloseoutPreload14.wait_exit_double` and the `(k, 2 * mw)` stage. -/
theorem double_leg_entries {c' : GalilScaffoldPlace.Place} {k Rad D mw : ℕ}
    {a : Bool} {t t' : SearchVM}
    (htm : t.search.mode = Mode.double) (htw : positive t.search.work = false)
    (hts : t.search.span = ofNat (2 * mw)) (htl : t.lower = ofNat k)
    (hcal : 8 * max k 1 ≤ 2 * mw) (hstage : 3 * Rad ≤ 5 * k)
    (hcan : Canonical t.search.debt)
    (hE : stageDebt Rad (k : ℤ) + (stageCredit k (2 * mw) : ℤ) + 1 ≤ value t.search.debt)
    (hs : searchStep c' a t t') (hdep : DepthAt t' D) (hD : D ≤ prepLen k)
    (hpost : PostRunP) :
    ∀ (as : List Bool),
      D + dpEvents (2 * mw + 1) ≤ as.length → PacedL 2048 0 as → RunEntriesS as t' :=
  runEntriesS_of_double_exitP htm htw hts htl hcal hcan hstage hE hs hdep hD hpost

#print axioms double_leg_entries

/-!
## 3. What is left

Closed here:

* **§1 — the `PostRun` → `PostRunP` substitution is free.**  Every consumer of
  `CloseoutPreload8.PostRun` in the stage chain (`CloseoutPreload11` §4–§5,
  `CloseoutPreload12` §5) applies it at a `.run` entry reached along a
  `StagePrep2` witness, whose pacing clause `PacedL 2048 0 (bs ++ a :: as)`
  yields `PacedL 2048 (bs ++ [a]).length as` by `CloseoutPreload5.pacedL_suffix`.
  So `readyClosure_S2P` / `replay_final_of_decodes_S2P` are the two-index stage's
  final theorems with `PostRun` weakened to `PostRunP` — and it is `PostRunP`,
  not `PostRun`, that the `.run` leg has a chance of proving
  (`CloseoutPreload16` §5).
* **§2 — the `.double` consumption leg.**  `DoubleTrace` / `doubleTrace_run` /
  `double_complete` close the gap `CloseoutPreload16` §5 names: from the shape
  `CloseoutPreload14.wait_exit_double` leaves, the doubling phase reaches
  `positive work = false` in exactly `mw` ticks with `span = ofNat (2 * mw)` and
  `lower` / `walker` / `dp` untouched, which is precisely the datum
  `runEntriesS_of_double_exitP` consumes (`double_leg_entries`).  The debt is
  tracked by `double_exit_debt` and stays canonical (`double_exit_canonical`).

**NOT closed — `postRunP_of_machine` is not proved here.**  Composing
`CloseoutPreload16.runP_exit_debt_at_exit_take` with §2 gives the *budget* along
one `.run` → `.wait` → `.double` → `prepare` round trip, but three pieces are
still missing before that composition is a proof of `PostRunP`:

1. **The slack normalisation.**  `runP_exit_debt_at_exit_take` requires
   `slack ≤ 2047`, while §1 hands the suffix `slack = (bs ++ [a]).length`, which
   is only bounded by the preparation length.  The list-level `PacedL` cannot be
   sharpened (`pacedL_mono` goes the wrong way): the true local slack is the
   machine's clock phase, so `PostRunP` will have to carry the clock, not just a
   pacing of the event list — i.e. the premise must come from
   `GalilScaffoldMatchClock`, not from `PacedL` alone.
2. **The `.wait` leg's length.**  `CloseoutPreload14.waitTrace_frame` measures
   the `.wait` leg by the debt, so the number of events between the `.run` exit
   and the `.double` entry is bounded by `value t.search.debt`; nothing yet
   converts that into a bound inside the stage's own event budget, which is what
   the *next* stage's `DepthAt` / supply clause needs.
3. **The exit-debt hypothesis of `double_leg_entries`** (`hE`) is still an
   input: `double_exit_debt` gives the balance identity, but turning it into
   `stageDebt Rad k + stageCredit k (2 * mw) + 1 ≤ value t.search.debt` needs the
   `.run`-exit budget of `runP_exit_debt_at_exit_take` *at the window `2 * mw`*,
   and hence the same slack normalisation as (1).

**無条件 PAL ∈ PEG は未完.**
-/

end PalPeg.CloseoutPreload17
