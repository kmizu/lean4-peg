import PalPeg.CloseoutPreload7

/-!
# Readiness, closed at the stage instead of at the restart

`CloseoutPreload7` showed that two of `CloseoutPreload6`'s three named contracts
are *false* as stated: `CentreLongRun` fails on short inputs, and `NoReturn`
asks the restart window to contain no `.run` interval.  §1 pins down why the
second one cannot be repaired: on `searchStep`, `.found` and `.missed` are
**absorbing** (`step_found_fix`, `step_missed_fix`), so a stage does not exit
to a new `begin` at all — it exits through `wait`/`double`, and the spent
`.double` counter dispatches `prepare` again (`step_double_dispatch`).  A second
`.run` entry on the same event list is therefore the *normal* behaviour.

So the closure is rebuilt with the restart replaced by the stage:

* §2 `BeginAt k Rad v` — the shape `restart_facts` extracts, as a free-standing
  property of one search state; `beginVM` parks such a state in a machine so
  that `CloseoutPreload5.Phase`, which mentions its `GalilVM` only through
  `lower` and `search.debt`, becomes usable at *any* begin.
* §3 `CentreLongAt` / `DepthAt`, `phase_reach_at`, `entry_shape_at`,
  `entry_debt_at` — the whole begin → `prepare` → `.run` analysis, relocated.
  `DepthAt` quantifies over `ReachP`, not `ReachL`: the depth is now a bound on
  the stage's own preparation trace, which is what removes `NoReturn`.
* §4 `dpSafeStage_entry_min` — the window clause weakened from `=` to `≤`.  The
  preparation copies `(stream s.walker).take (span+1)`, so a short input gives a
  *shorter* window, and every budget inequality only gets slacker.
* §5 `StageInv = StagePrep ∨ RunEntriesS`, `stagePrep_next`,
  `dpSafe_of_stagePrep`, `runEntriesS_of_stageInv`.
* §6 `RestartS`, `readyClosure_S`, `replay_final_of_decodes_S` — two named
  clauses per restart instead of three, both local to the stage, plus the single
  global `PostRun`.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload8

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController
open PalPeg.GalilScaffoldPrepareControl (State)
open PalPeg.GalilScaffoldCounter (Counter Canonical value ofNat)
open PalPeg.CloseoutReadyStage
open PalPeg.CloseoutRunEntriesS
open PalPeg.CloseoutPreload
open PalPeg.CloseoutDebtAudit (dpEvents stageWindow1)
open PalPeg.CloseoutPreload5 (Phase ReachP ReachL CentreLong phase_step reachP_ne_run
  pacedL_prefix_count pacedL_suffix append_cons_eq)
open PalPeg.CloseoutPreload6 (prepLen dpSafeStage_entry_gen)

/-! ## 1. `found` / `missed` are absorbing -/

theorem step_found_fix {c : GalilScaffoldPlace.Place} {a : Bool} {v v' : SearchVM}
    (hm : v.search.mode = GalilScaffoldSearchFinish.Mode.found)
    (hs : searchStep c a v v') : v' = v := by
  unfold searchStep at hs; rw [hm] at hs; exact hs

theorem step_missed_fix {c : GalilScaffoldPlace.Place} {a : Bool} {v v' : SearchVM}
    (hm : v.search.mode = GalilScaffoldSearchFinish.Mode.missed)
    (hs : searchStep c a v v') : v' = v := by
  unfold searchStep at hs; rw [hm] at hs; exact hs

/-- The `.double` dispatch with the work counter spent is the *same* `prepare`
dispatch the `.grow` branch performs. -/
theorem step_double_dispatch {c : GalilScaffoldPlace.Place} {a : Bool} {v v' : SearchVM}
    (hm : v.search.mode = GalilScaffoldSearchFinish.Mode.double)
    (hz : GalilScaffoldCounter.positive v.search.work = false)
    (hs : searchStep c a v v') :
    v' = SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a
      (GalilScaffoldPrepareControl.prepare v.toPrep v.lower c)) v.search.quarter v.lower := by
  unfold searchStep at hs
  rw [hm] at hs
  simp only [hz, Bool.false_eq_true, if_false] at hs
  exact hs

#print axioms step_found_fix
#print axioms step_missed_fix
#print axioms step_double_dispatch

/-! ## 2. The stage's `begin`, locally -/

/-- The shape `CloseoutPreload5.restart_facts` extracts from `Restarted`, as a
free-standing property of a single search state.  Nothing here mentions the
controller, the input, or the restart. -/
structure BeginAt (k Rad : ℕ) (v : SearchVM) : Prop where
  mode : v.search.mode = GalilScaffoldSearchFinish.Mode.grow
  work : v.search.work = ofNat (max k 1)
  span : v.search.span = ofNat 0
  can : Canonical v.search.debt
  debt : value v.search.debt = -(Rad : ℤ)
  low : v.lower = ofNat k

theorem beginAt_of_restarted {raw : List (Fin 2)} {u : GalilVM} {Rad : ℕ} {last : Counter}
    (hR : Restarted raw u Rad last) :
    BeginAt (value last).toNat Rad (searchLens.get u) := by
  obtain ⟨hm, hw, hsp, hc, hd, hlow⟩ := PalPeg.CloseoutPreload5.restart_facts hR
  exact ⟨hm, hw, hsp, hc, hd, by rw [hlow]; exact PalPeg.CloseoutPreload5.restart_lower hR⟩

#print axioms beginAt_of_restarted

/-- **Relocation.**  `CloseoutPreload5.Phase` mentions its `GalilVM` argument only
through `lower` and `search.debt`, so parking an arbitrary search state in an
arbitrary machine makes `Phase` usable at *any* begin state. -/
def beginVM (u : GalilVM) (v : SearchVM) : GalilVM := searchLens.set u v

theorem beginVM_get (u : GalilVM) (v : SearchVM) : searchLens.get (beginVM u v) = v :=
  searchLens.get_set u v

theorem beginVM_lower (u : GalilVM) (v : SearchVM) : (beginVM u v).lower = v.lower := rfl
theorem beginVM_search (u : GalilVM) (v : SearchVM) : (beginVM u v).search = v.search := rfl

/-! ## 3. The two contracts, relocated to the stage -/

/-- `CloseoutPreload5.CentreLongRun`, from a begin state instead of a restart. -/
def CentreLongAt (w : SearchVM) (k : ℕ) : Prop :=
  ∀ (bs : List Bool) (x x' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool),
    ReachP w bs x → searchStep c a x x' →
    x.search.mode = GalilScaffoldSearchFinish.Mode.grow →
    GalilScaffoldCounter.positive x.search.work = false → CentreLong k c

/-- `CloseoutPreload5.EntryDepthG`, from a begin state — and quantified over
`ReachP`, not `ReachL`.  This is what kills `NoReturn`: the depth is now a bound
on the stage's own preparation trace, not on a global window. -/
def DepthAt (w : SearchVM) (D : ℕ) : Prop :=
  ∀ (bs : List Bool) (x x' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool),
    ReachP w bs x → searchStep c a x x' →
    x'.search.mode = GalilScaffoldSearchFinish.Mode.run → bs.length + 1 ≤ D

/-- **The phase invariant from a local begin.** -/
theorem phase_reach_at {u : GalilVM} {w : SearchVM} {k Rad : ℕ}
    (hb : BeginAt k Rad w) (hcl : CentreLongAt w k) :
    ∀ {bs : List Bool} {v : SearchVM}, ReachP w bs v → Phase (beginVM u w) k bs v := by
  intro bs v h
  induction h with
  | nil hne =>
    refine Or.inl ⟨hb.mode, by simp, ?_, ?_, rfl, ?_, hb.can⟩
    · simpa using hb.work
    · simpa using hb.span
    · show value w.search.debt = value w.search.debt + 2 * (0 : ℤ) - ((0 : ℕ) : ℤ)
      simp
  | snoc x x' bs a c hr hs hne ih =>
    exact phase_step (beginVM u w) k bs x x' c a
      (fun h1 h2 => hcl bs x x' c a hr hs h1 h2) ih hs hne

#print axioms phase_reach_at

/-- **The entry shape, from a local begin.** -/
theorem entry_shape_at {u : GalilVM} {w : SearchVM} {k Rad : ℕ}
    (hb : BeginAt k Rad w) (hcl : CentreLongAt w k)
    {bs : List Bool} {v v' : SearchVM} {c : GalilScaffoldPlace.Place} {a : Bool}
    (hp : ReachP w bs v) (hs : searchStep c a v v')
    (hr : v'.search.mode = GalilScaffoldSearchFinish.Mode.run) :
    ∃ (s : State) (span n : ℕ) (v0 : SearchVM),
      s.mode = GalilScaffoldSearchFinish.Mode.lower ∧ s.work = ofNat k ∧
      s.span = ofNat span ∧
      s.program.config.tapes 10 =
        GalilScaffoldTape.moveRight (GalilScaffoldTape.write GalilScaffoldTape.reset 4) ∧
      s.program.config.tapes 7 = GalilScaffoldTape.reset ∧
      (∀ i : Fin 12, i ≠ 7 → i ≠ 10 →
        s.program.config.tapes i = GalilScaffoldTape.reset) ∧
      ((GalilScaffoldPlace.stream s.walker).take (span + 1)).length = stageWindow1 k ∧
      v0.toPrep = s ∧ PalPeg.CloseoutPreload2.PrepTrace v0 n v ∧
      bs.length = max k 1 + 1 + n := by
  have hne := reachP_ne_run hp
  rcases phase_reach_at (u := u) hb hcl hp with ⟨hmg, -, -, -, -, -, -⟩ | hprep
  · exact absurd ((run_entry_startRun hs hne hr).1 ▸ hmg) (by decide)
  · obtain ⟨s, span, n, v0, hm, hwk, hsp, -, h10, h7, hother, hcal, hv0, htr, hn, -, -, -⟩ :=
      hprep
    exact ⟨s, span, n, v0, hm, by rw [hwk]; exact hb.low, hsp, h10, h7, hother, hcal,
      hv0, htr, hn⟩

#print axioms entry_shape_at

/-- **The entry debt, from a local begin.** -/
theorem entry_debt_at {u : GalilVM} {w : SearchVM} {k Rad : ℕ}
    (hb : BeginAt k Rad w) (hcl : CentreLongAt w k)
    {bs : List Bool} {v v' : SearchVM} {c : GalilScaffoldPlace.Place} {a : Bool}
    (hp : ReachP w bs v) (hs : searchStep c a v v')
    (hr : v'.search.mode = GalilScaffoldSearchFinish.Mode.run) :
    Canonical v'.search.debt ∧
      value v'.search.debt =
        PalPeg.GalilReplaySpan.stageDebt Rad ((k : ℕ) : ℤ)
          - (((bs ++ [a]).count true : ℕ) : ℤ) := by
  have hne := reachP_ne_run hp
  have hdebt := run_entry_debt hs hne hr
  rcases phase_reach_at (u := u) hb hcl hp with ⟨hmg, -, -, -, -, -, -⟩ | hprep
  · exact absurd ((run_entry_startRun hs hne hr).1 ▸ hmg) (by decide)
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hd, hc⟩ := hprep
    have hcount : (((bs ++ [a]).count true : ℕ) : ℤ)
        = ((bs.count true : ℕ) : ℤ) + (if a then 1 else 0) := by cases a <;> simp
    have hdu : value (beginVM u w).search.debt = -(Rad : ℤ) := hb.debt
    constructor
    · rw [hdebt]; cases a
      · exact hc
      · exact GalilScaffoldCounter.dec_canonical _ hc
    · rw [hdebt, hcount]
      have hmax : PalPeg.GalilReplaySpan.stageDebt Rad ((k : ℕ) : ℤ)
          = 2 * ((max k 1 : ℕ) : ℤ) - (Rad : ℤ) := by
        unfold PalPeg.GalilReplaySpan.stageDebt
        push_cast
        omega
      rw [hmax]
      cases a
      · simp only [Bool.false_eq_true, if_false]
        rw [hd, hdu]; ring
      · simp only [if_true]
        rw [GalilScaffoldCounter.dec_value, hd, hdu]; ring

#print axioms entry_debt_at

/-! ## 4. Short inputs: the window is a `take`, so `≤` is the right shape -/

/-- `CloseoutPreload6.dpSafeStage_entry_gen` with the window length relaxed to an
upper bound.  On an input shorter than `stageWindow1 k` the preparation copies a
truncated window (`Phase`'s `hcal` clause is a `List.take`), and the DP then
halts *earlier*, so every budget inequality only gets slacker. -/
theorem dpSafeStage_entry_min (v : SearchVM) (w : List (Fin 3)) (lower k slack : ℕ)
    (as : List Bool)
    (hw : w.length ≤ stageWindow1 k)
    (hdp : v.dp = ⟨GalilScaffoldPreload.initial w lower, false⟩)
    (hmode : v.search.mode = .run)
    (hc : Canonical v.search.debt)
    (hb : (((slack + dpEvents (stageWindow1 k)) / 2048 + 1 : ℕ) : ℤ)
      ≤ value v.search.debt)
    (hlen : dpEvents (stageWindow1 k) ≤ as.length)
    (hpaced : PacedL 2048 slack as) :
    DpSafeStage v as := by
  set N : ℕ := dpEvents (stageWindow1 k) with hN
  refine dpSafeStage_entry v w lower as (as.take N) (as.drop N) hdp hmode
    (by rw [List.take_append_drop]) ?_ hc ?_
  · have hlenpre : (as.take N).length = N := by rw [List.length_take]; omega
    have hbud := dpEvents_budget (stageWindow1 k)
    rw [hlenpre, hN]
    omega
  · have h1 : (as.take N).count true ≤ (slack + N) / 2048 + 1 :=
      PalPeg.CloseoutPreload6.pacedL_count_take_gen hpaced
    have h3 : (((as.take N).count true : ℕ) : ℤ) ≤ (((slack + N) / 2048 + 1 : ℕ) : ℤ) :=
      Int.ofNat_le.mpr h1
    omega

#print axioms dpSafeStage_entry_min

/-! ## 5. The stage invariant and its step -/

/-- **NAMED — the run phase of a stage keeps the ledger.**  Once the DP has been
handed a safe stage, every later `.run` entry on the same event list is safe.
This is the *one* residual: it replaces `NoReturn`, which was false because the
`.run` phase exits through `wait`/`double` back into `prepare` (§1), and it is
local — nothing in it mentions the restart. -/
def PostRun : Prop :=
  ∀ (v : SearchVM) (as : List Bool), v.search.mode = GalilScaffoldSearchFinish.Mode.run →
    DpSafeStage v as → RunEntriesS as v

/-- The preparation half of the stage invariant. -/
def StagePrep (k D : ℕ) (w v : SearchVM) (as : List Bool) : Prop :=
  ∃ bs : List Bool, ReachP w bs v ∧ D + dpEvents (stageWindow1 k) ≤ bs.length + as.length ∧
    PacedL 2048 0 (bs ++ as)

/-- **The stage invariant.**  Either the stage is still preparing — and then the
whole `ReachP` path back to its own `begin` is available — or the DP run has
already been handed a safe stage and the readiness ledger travels by itself. -/
def StageInv (k D : ℕ) (w v : SearchVM) (as : List Bool) : Prop :=
  StagePrep k D w v as ∨ RunEntriesS as v

theorem stagePrep_next {k D : ℕ} {w v v' : SearchVM} {c : GalilScaffoldPlace.Place}
    {a : Bool} {as : List Bool} (hq : StagePrep k D w v (a :: as))
    (hs : searchStep c a v v')
    (hne : v'.search.mode ≠ GalilScaffoldSearchFinish.Mode.run) :
    StagePrep k D w v' as := by
  obtain ⟨bs, hreach, hlen, hpaced⟩ := hq
  refine ⟨bs ++ [a], .snoc _ _ _ _ _ c hreach hs hne, ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton]
    simp only [List.length_cons] at hlen
    omega
  · rw [← append_cons_eq]; exact hpaced

/-- **The entry clause, from the stage invariant alone.** -/
theorem dpSafe_of_stagePrep {u : GalilVM} {w : SearchVM} {k Rad D : ℕ}
    (hb : BeginAt k Rad w) (hstage : 3 * Rad ≤ 5 * k) (hcl : CentreLongAt w k)
    (hdep : DepthAt w D) (hD : D ≤ prepLen k)
    {v v' : SearchVM} {c : GalilScaffoldPlace.Place} {a : Bool} {as : List Bool}
    (hq : StagePrep k D w v (a :: as)) (hs : searchStep c a v v')
    (hr : v'.search.mode = GalilScaffoldSearchFinish.Mode.run) :
    DpSafeStage v' as := by
  obtain ⟨bs, hreach, hlen, hpaced⟩ := hq
  have hne := reachP_ne_run hreach
  have hdlen := hdep bs v v' c a hreach hs hr
  -- the preload shape
  obtain ⟨s, span, n, v0, hm, hwk, hsp, h10, h7, hother, hcal, hv0, htrace, -⟩ :=
    entry_shape_at (u := u) hb hcl hreach hs hr
  have hpre := PalPeg.CloseoutPreload2.preloadAtEntry_of_trace s k span n k hm hwk hsp
    h10 h7 hother hcal ⟨v0, hv0, htrace⟩ hs hne hr
  obtain ⟨W, lower, hW, hpreload⟩ := hpre
  -- the debt
  obtain ⟨hcan, hdv⟩ := entry_debt_at (u := u) hb hcl hreach hs hr
  have hpaced' : PacedL 2048 0 ((bs ++ [a]) ++ as) := by
    rw [← append_cons_eq]; exact hpaced
  have hlenpref : (bs ++ [a]).length ≤ D := by
    simp only [List.length_append, List.length_singleton]; omega
  have hadv : 2048 * ((bs ++ [a]).count true) ≤ prepLen k :=
    le_trans (pacedL_prefix_count hpaced') (by omega)
  have hm2 : 2048 * (((bs ++ [a]).length + dpEvents (stageWindow1 k)) / 2048 + 1)
      ≤ prepLen k + dpEvents (stageWindow1 k) + 2048 := by
    have h1 := Nat.div_add_mod ((bs ++ [a]).length + dpEvents (stageWindow1 k)) 2048
    have h2 : ((bs ++ [a]).length + dpEvents (stageWindow1 k)) % 2048 < 2048 :=
      Nat.mod_lt _ (by norm_num)
    omega
  have hbud := PalPeg.CloseoutPreload6.budget_adv (k := k) (Rad := Rad)
    (adv := (bs ++ [a]).count true)
    (m := ((bs ++ [a]).length + dpEvents (stageWindow1 k)) / 2048 + 1) hstage hadv hm2
  refine dpSafeStage_entry_min v' W lower k (bs ++ [a]).length as (le_of_eq hW)
    (run_entry_preload hs hne hr hpreload) hr hcan ?_ ?_ (pacedL_suffix hpaced')
  · rw [hdv]; omega
  · have hlen' : D + dpEvents (stageWindow1 k) ≤ bs.length + (as.length + 1) := hlen
    omega

#print axioms dpSafe_of_stagePrep

/-- **`RunEntriesS` from the stage invariant.**  The induction closes with no
`NoReturn`, no `CentreLongRun` over the restart window, and no depth bound over
anything but the stage's own preparation trace. -/
theorem runEntriesS_of_stageInv {u : GalilVM} {w : SearchVM} {k Rad D : ℕ}
    (hb : BeginAt k Rad w) (hstage : 3 * Rad ≤ 5 * k) (hcl : CentreLongAt w k)
    (hdep : DepthAt w D) (hD : D ≤ prepLen k) (hpost : PostRun) :
    ∀ (as : List Bool) (v : SearchVM), StageInv k D w v as → RunEntriesS as v := by
  intro as
  induction as with
  | nil => intro v _; trivial
  | cons a as ih =>
    intro v hq
    rcases hq with hq | hq
    · intro c v' hstep
      by_cases hr : v'.search.mode = GalilScaffoldSearchFinish.Mode.run
      · have hsafe := dpSafe_of_stagePrep (u := u) hb hstage hcl hdep hD hq hstep hr
        exact ⟨fun _ _ _ => hsafe, hpost v' as hr hsafe⟩
      · exact ⟨fun _ _ h => absurd h hr,
          ih v' (Or.inl (stagePrep_next hq hstep hr))⟩
    · exact hq

#print axioms runEntriesS_of_stageInv

/-! ## 6. The closure -/

/-- **The restart datum, at the stage.**  Compared with
`CloseoutPreload6.RestartG'` the `NoReturn` clause is gone and both remaining
clauses are relocated to the stage's own `begin`. -/
def RestartS (raw : List (Fin 2)) : Prop :=
  ∀ (u : GalilVM) (Rad : ℕ) (last : Counter),
    Restarted raw u Rad last → StageEntry Rad last →
    ∃ D : ℕ, D ≤ prepLen (value last).toNat ∧
      CentreLongAt (searchLens.get u) (value last).toNat ∧
      DepthAt (searchLens.get u) D

theorem runEntriesS_of_restartS {raw : List (Fin 2)} {u : GalilVM} {Rad D : ℕ}
    {last : Counter} (hR : Restarted raw u Rad last) (hSE : StageEntry Rad last)
    (hcl : CentreLongAt (searchLens.get u) (value last).toNat)
    (hdep : DepthAt (searchLens.get u) D) (hD : D ≤ prepLen (value last).toNat)
    (hpost : PostRun) :
    ∀ (as : List Bool),
      D + dpEvents (stageWindow1 (value last).toNat) ≤ as.length → PacedL 2048 0 as →
      RunEntriesS as (searchLens.get u) := by
  have hval : value last = ((value last).toNat : ℤ) :=
    (Int.toNat_of_nonneg hR.2.2.2.2.2.2.2.2.2).symm
  have hstage : 3 * Rad ≤ 5 * (value last).toNat := hSE _ hval
  intro as hlen hpaced
  refine runEntriesS_of_stageInv (u := u) (beginAt_of_restarted hR) hstage hcl hdep hD
    hpost as _ (Or.inl ⟨[], .nil _ ?_, by simpa using hlen, by simpa using hpaced⟩)
  rw [(PalPeg.CloseoutPreload5.restart_facts hR).1]
  decide

#print axioms runEntriesS_of_restartS

/-- **`GalilReplaySpan.ReadyClosure` for `RdPaced`, at the stage datum.** -/
theorem readyClosure_S (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    (hpost : PostRun) (h : RestartS raw) :
    PalPeg.GalilReplaySpan.ReadyClosure raw P q first 2048 RdPaced where
  ready := fun c s hs => rdPaced_ready c s hs
  seg := fun es c c' s t hseg hidle hs => rdPaced_seg P q first es c c' s t hseg hidle hs
  restart := fun c u Rad last _ hclk hR hSE => by
    obtain ⟨D, hD, hcl, hdep⟩ := h u Rad last hR hSE
    exact rdPaced_restart c u Rad last (D + dpEvents (stageWindow1 (value last).toNat))
      hclk hR
      (fun m as hlen hp => runEntriesS_of_restartS hR hSE hcl hdep hD hpost as (by omega) hp)

#print axioms readyClosure_S

/-- The final replay theorem at the stage datum. -/
def replay_final_of_decodes_S (raw : List (Fin 2)) (P : Shared)
    (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM)
    (q : ℕ) (first : Fin 9)
    (hex : ∀ s, P.replayExhausted s = GalilScaffoldCounter.zero s.replay)
    (hsearch : ∀ s : GalilVM, PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect P a s v)
    (hpost : PostRun) (hS : RestartS raw)
    (hdec : Decodes P)
    (hbudget : PalPeg.GalilReplaySpan.ReplayBudgetRD raw P q first 2048)
    (hrs : PalPeg.GalilReplaySpan.RestartShapeL P)
    (r : ℕ) (hr0 : 0 < r) (c : Control) (t : GalilVM)
    (hm : c.mode = Mode.scan) (hc : c.clock = 2048) (hrpl : c.replaying = true)
    (hR : Restarted raw t 0 GalilScaffoldCounter.reset) (hrep : t.replay = ofNat r)
    (hM : MInv raw c t) (hfr : Frontier t) (hsi : ShiftIdle t) :=
  PalPeg.GalilReplaySpan.replay_after_fallback_general''_R_of_decodes
    raw P hP hP' q first hex hsearch (readyClosure_S raw P q first hpost hS) hdec hbudget hrs
    r hr0 c t hm hc hrpl hR hrep hM hfr hsi

#print axioms replay_final_of_decodes_S

/-!
## Note — the one missing machine fact

`PostRun` is what is left, and unlike `NoReturn` it is a finite, local
statement: *once the DP has been handed a safe stage, the rest of the event list
is safe for that state.*  Unwinding it one step, what has to be proved is

> from a `.run` state with `DpSafeStage v (a :: as)`, the successor `v'` either
> stays in `.run` (`dpSafeStage_step`, already available), or leaves through
> `finish` to `.found` / `.missed` — both absorbing by §1, so `RunEntriesS` is
> immediate — or to `.wait` / `.double`, and then the `.double` phase runs its
> work counter down (`GalilScaffoldDouble.Run`, whose `balance` gives
> `4·debt + quarter` exactly) and dispatches `prepare` (`step_double_dispatch`)
> into a state satisfying `BeginAt k' Rad' ·` for the doubled stage, with
> `CentreLongAt` and `DepthAt` at `k'`.

Two pieces of that are genuinely absent: the `.double` phase reaches
`positive work = false` (a termination fact about the doubling counter), and the
doubled stage's parameters still satisfy `3 * Rad' ≤ 5 * k'` and
`dpEvents (stageWindow1 k') ≤` the events remaining.  The second is the supply
condition — `k'` grows with the stage while the event list shrinks — and it is
the only place where an input-length hypothesis is still needed.
-/

end PalPeg.CloseoutPreload8
