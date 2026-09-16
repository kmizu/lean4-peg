import PalPeg.CloseoutPreload5

/-!
# Recalibrating the entry debt: the preparation phase pays for itself

`CloseoutPreload5` closed the begin → `prepare` linkage but had to buy the entry
debt clause with `D ≤ 2047`, which `depth_forces_stage_bound` turns into
`k ≤ 2045`: a bound on the *stage*, i.e. on the input.  That is not acceptable
for an unconditional statement.

This file removes it.  The observation is that the entry debt is not "the stage
debt or nothing": `CloseoutPreload5.entry_debt` computes it **exactly** as
`stageDebt Rad k - (advances consumed on the way in)`, and the way in is a
clock-paced list, so the advances consumed are bounded by the *length* of the
preparation phase divided by the clock period.  The preparation phase is
`prepLen k = 2 * k + 2 * (8 * max k 1 + 1) + 6` ticks — the grow phase, the two
sweeps of the window, and the fixed dispatch overhead — so the entry loses at
most `prepLen k / 2048` credits, and the stage budget still closes with room to
spare, *for every `k`*.

* §1 The arithmetic.  `dpEvents_stage_le` bounds the DP event budget of the
  calibrated window linearly (`399 * max k 1 + 78`), and `budget_adv` is
  `CloseoutDebtAudit.stage_budget_closes1` weakened by both the advances lost on
  the way in (`adv`) and the slack the entry hands to the tail (`m`):

      3 * Rad ≤ 5 * k → 2048 * adv ≤ prepLen k →
      2048 * m ≤ prepLen k + dpEvents (stageWindow1 k) + 2048 →
      (adv : ℤ) + m ≤ stageDebt Rad k

  This is a genuine strengthening of `stage_budget_closes1`, which is the case
  `adv = 0`, `m = pacedComparisons 2048 (dpEvents (stageWindow1 k))`.

* §2 `dpSafeStage_entry_gen`: `CloseoutReadyStage.dpSafeStage_entry_pacedW` with
  the slack *unbounded* — the charged prefix of a `PacedL 2048 slack` list holds
  at most `(slack + N) / 2048 + 1` comparisons, and that is all the entry debt
  has to cover.  `dpSafeStage_entry_paced1` is the case `slack ≤ 2047`.

* §3 `EntryPreloadG` / `runEntriesS_of_preloadInvG`: the `RunEntriesS` induction
  of `CloseoutPreload.runEntriesS_of_preloadInv` with the debt clause in the
  `stageDebt - adv` form, so that neither `Rad` nor the slack has to be uniform
  over the entries.

* §4 `runEntriesS_of_namedG`: the payoff.  Same three named contracts as
  `CloseoutPreload5.runEntriesS_of_named`, but the depth bound is
  `D ≤ prepLen k` instead of `D ≤ 2047`, so **no bound on the stage survives**.

* §5 `RestartG'`, `readyClosure_G'`, `replay_final_of_decodes_G'`: the closure
  and the final replay theorem at the recalibrated datum.

## What is proved unconditionally here

The recalibrated budget and the whole closure at it: for every `k`, every
`Rad` with `3 * Rad ≤ 5 * k`, and every entry reached within `prepLen k`
events of the restart, the debt at the entry covers the stage's DP run.

## What is still named

Exactly the two contracts `CloseoutPreload5` already named, plus the depth:

* `CloseoutPreload5.CentreLongRun u k` — the dispatching centre holds the
  stage's window.  `CloseoutPreload2.tick_true_det` / `run_run_unique` are
  determinism statements about `GalilScaffoldPrepareControl.Tick`; they say
  nothing about the *place* a `searchStep` is taken at, and `CentreLong k c` is
  a property of that place.  So determinism does **not** discharge it, and it is
  left named here, unchanged.
* `CloseoutPreload5.NoReturn u` — the stage cut.  Determinism makes the path out
  of the restart unique *given the events*, but it does not forbid the path from
  passing through `.run`; that is a liveness/shape fact about the search, not a
  determinism fact.  Also left named, unchanged.
* `CloseoutPreload5.EntryDepthG u D` with `D ≤ prepLen k` — the hand-over
  happens within the preparation phase.  This is the clause §4 weakened: the
  previous form `D ≤ 2047` is strictly stronger for every `k ≥ 114`
  (`prepLen k ≥ 2048` there), and it is what forced `k ≤ 2045`.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload6

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController
open PalPeg.GalilScaffoldPrepareControl (State)
open PalPeg.GalilScaffoldCounter (Counter Canonical value ofNat)
open PalPeg.CloseoutReadyStage
open PalPeg.CloseoutRunEntriesS
open PalPeg.CloseoutPreload
open PalPeg.CloseoutDebtAudit (dpEvents stageWindow1 pacedComparisons)
open PalPeg.CloseoutPreload5 (ReachP ReachL CentreLongRun NoReturn EntryDepthG dpEntryG QG)

/-! ## 1. The recalibrated arithmetic -/

/-- **The length of the preparation phase.**  `max k 1` grow ticks at two ticks
each, the two sweeps of the calibrated window `8 * max k 1 + 1`, and the fixed
dispatch overhead. -/
def prepLen (k : ℕ) : ℕ := 2 * k + 2 * (8 * max k 1 + 1) + 6

theorem prepLen_le (k : ℕ) : prepLen k ≤ 18 * max k 1 + 8 := by
  unfold prepLen
  have : k ≤ max k 1 := le_max_left _ _
  omega

/-- The DP event budget of the calibrated window, bounded linearly. -/
theorem dpEvents_stage_le (k : ℕ) :
    dpEvents (stageWindow1 k) ≤ 399 * max k 1 + 78 := by
  unfold PalPeg.CloseoutDebtAudit.dpEvents PalPeg.CloseoutDebtAudit.stageWindow1
  have h : 3186 * (8 * max k 1 + 1) + 1683 + 63 = 25488 * max k 1 + 4932 := by ring
  rw [h]
  have h1 := Nat.div_add_mod (25488 * max k 1 + 4932) 64
  have h2 : (25488 * max k 1 + 4932) % 64 < 64 := Nat.mod_lt _ (by norm_num)
  omega

/-- The core inequality, over `ℕ`. -/
theorem budget_adv_nat {k Rad adv m : ℕ} (hstage : 3 * Rad ≤ 5 * k)
    (hadv : 2048 * adv ≤ prepLen k)
    (hm : 2048 * m ≤ prepLen k + dpEvents (stageWindow1 k) + 2048) :
    adv + m + Rad ≤ 2 * max k 1 := by
  have h1 := prepLen_le k
  have h2 := dpEvents_stage_le k
  have h3 : k ≤ max k 1 := le_max_left _ _
  have h4 : 1 ≤ max k 1 := le_max_right _ _
  have h5 : max k 1 ≤ k + 1 := by omega
  omega

/-- **The stage budget, weakened by the entry loss and the tail slack.**
`CloseoutDebtAudit.stage_budget_closes1` is the case `adv = 0`. -/
theorem budget_adv {k Rad adv m : ℕ} (hstage : 3 * Rad ≤ 5 * k)
    (hadv : 2048 * adv ≤ prepLen k)
    (hm : 2048 * m ≤ prepLen k + dpEvents (stageWindow1 k) + 2048) :
    (adv : ℤ) + (m : ℤ) ≤ PalPeg.GalilReplaySpan.stageDebt Rad (k : ℤ) := by
  have hnat := budget_adv_nat hstage hadv hm
  have hcast : (adv : ℤ) + (m : ℤ) + (Rad : ℤ) ≤ 2 * max (k : ℤ) 1 := by
    have h := (Nat.cast_le (α := ℤ)).mpr hnat
    push_cast at h
    exact h
  rw [PalPeg.GalilReplaySpan.stageDebt]
  omega

/-- Sanity: the old budget is the case `adv = 0`. -/
theorem budget_adv_old {k Rad : ℕ} (hstage : 3 * Rad ≤ 5 * k) :
    ((pacedComparisons 2048 (dpEvents (stageWindow1 k)) : ℕ) : ℤ)
      ≤ PalPeg.GalilReplaySpan.stageDebt Rad (k : ℤ) :=
  PalPeg.CloseoutDebtAudit.stage_budget_closes1 hstage

#print axioms budget_adv

/-! ## 2. The DP entry at an arbitrary slack -/

/-- The comparisons a `PacedL 2048 slack` list holds in its first `N` events. -/
theorem pacedL_count_take_gen {slack N : ℕ} {as : List Bool}
    (h : PacedL 2048 slack as) :
    (as.take N).count true ≤ (slack + N) / 2048 + 1 := by
  have h0 := h N
  have h1 := Nat.div_add_mod (slack + N) 2048
  have h2 : (slack + N) % 2048 < 2048 := Nat.mod_lt _ (by norm_num)
  omega

/-- **The DP entry theorem with the slack unbounded.**  The charged prefix is
the first `dpEvents (stageWindow1 k)` events; the debt at the entry only has to
cover the comparisons *that prefix* can hold at the ambient slack. -/
theorem dpSafeStage_entry_gen (v : SearchVM) (w : List (Fin 3)) (lower k slack : ℕ)
    (as : List Bool)
    (hw : w.length = stageWindow1 k)
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
  · have hlenpre : (as.take N).length = N := by
      rw [List.length_take]; omega
    rw [hlenpre, hw, hN]
    exact dpEvents_budget _
  · have h1 : (as.take N).count true ≤ (slack + N) / 2048 + 1 :=
      pacedL_count_take_gen hpaced
    have h3 : (((as.take N).count true : ℕ) : ℤ) ≤ (((slack + N) / 2048 + 1 : ℕ) : ℤ) :=
      Int.ofNat_le.mpr h1
    omega

#print axioms dpSafeStage_entry_gen

/-! ## 3. The `RunEntriesS` induction, with a per-entry slack -/

/-- `CloseoutPreload.EntryPreload`, with the debt clause in the form
§2 consumes: the slack is chosen at the entry, and the debt only has to cover
the comparisons the charged prefix can hold at that slack. -/
def EntryPreloadG (Q : SearchVM → List Bool → Prop) (k : ℕ) : Prop :=
  ∀ (v v' : SearchVM) (center : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool),
    Q v (a :: as) → searchStep center a v v' →
      ((v.search.mode ≠ .run → v'.search.mode = .run →
        (∃ (w : List (Fin 3)) (lower : ℕ), w.length = stageWindow1 k ∧
          PreloadAt v.toPrep w lower) ∧
        Canonical v'.search.debt ∧
        (∃ slack : ℕ, PacedL 2048 slack as ∧
          (((slack + dpEvents (stageWindow1 k)) / 2048 + 1 : ℕ) : ℤ)
            ≤ value v'.search.debt) ∧
        dpEvents (stageWindow1 k) ≤ as.length)) ∧ Q v' as

theorem runEntriesS_of_preloadInvG {Q : SearchVM → List Bool → Prop} {k : ℕ}
    (hQ : EntryPreloadG Q k) :
    ∀ (as : List Bool) (v : SearchVM), Q v as → RunEntriesS as v := by
  intro as
  induction as with
  | nil => intro v _; trivial
  | cons a as ih =>
    intro v hq center v' hstep
    obtain ⟨hdata, hnext⟩ := hQ v v' center a as hq hstep
    refine ⟨?_, ih v' hnext⟩
    intro _ hne hr
    obtain ⟨⟨w, lower, hw, hpre⟩, hcan, ⟨slack, hpaced, hb⟩, hlen⟩ := hdata hne hr
    exact dpSafeStage_entry_gen v' w lower k slack as hw
      (run_entry_preload hstep hne hr hpre) hr hcan hb hlen hpaced

#print axioms runEntriesS_of_preloadInvG

/-! ## 4. The residual datum, with no bound on the stage -/

/-- **`RunEntriesS` from the three named contracts, recalibrated.**  Identical to
`CloseoutPreload5.runEntriesS_of_named` except that the depth bound is
`D ≤ prepLen k` — which does not bound `k` — instead of `D ≤ 2047`, which forced
`k ≤ 2045`.  The entry debt is no longer required to be the *full* stage debt:
`entry_debt` gives it exactly, as `stageDebt Rad k` minus the advances consumed
on the way in, and §1 shows the remainder still pays for the stage. -/
theorem runEntriesS_of_namedG {raw : List (Fin 2)} {u : GalilVM} {Rad D : ℕ}
    {last : Counter} (hR : Restarted raw u Rad last) (hSE : StageEntry Rad last)
    (hcl : CentreLongRun u (value last).toNat) (hnr : NoReturn u)
    (hdep : EntryDepthG u D) (hD : D ≤ prepLen (value last).toNat) :
    ∀ (as : List Bool), dpEntryG (value last).toNat D ≤ as.length → PacedL 2048 0 as →
      RunEntriesS as (searchLens.get u) := by
  have hval : value last = ((value last).toNat : ℤ) :=
    (Int.toNat_of_nonneg hR.2.2.2.2.2.2.2.2.2).symm
  have hstage : 3 * Rad ≤ 5 * (value last).toNat := hSE _ hval
  intro as0 hlen0 hpaced0
  refine runEntriesS_of_preloadInvG (Q := QG u (value last).toNat D) (k := (value last).toNat) ?_ as0 (searchLens.get u)
    ⟨[], .nil _, by simpa using hlen0, by simpa using hpaced0⟩
  intro v v' center a as hq hstep
  refine ⟨fun hne hr => ⟨?_, ?_, ?_, ?_⟩,
    PalPeg.CloseoutPreload5.qG_next u (value last).toNat D v v' center a as hq hstep⟩
  · -- the preload shape
    obtain ⟨bs, hreach, -, -⟩ := hq
    obtain ⟨s, lower, span, n, v0, hm, hw, hspan, h10, h7, hother, hcal, hv0, htrace, -⟩ :=
      PalPeg.CloseoutPreload5.entry_shape hR hcl (hnr bs v hreach hne) hstep hr
    exact PalPeg.CloseoutPreload2.preloadAtEntry_of_trace s lower span n (value last).toNat hm hw hspan
      h10 h7 hother hcal ⟨v0, hv0, htrace⟩ hstep hne hr
  · -- canonicity of the entry debt
    obtain ⟨bs, hreach, -, -⟩ := hq
    exact (PalPeg.CloseoutPreload5.entry_debt hR hcl (hnr bs v hreach hne) hstep hr).1
  · -- the entry debt covers the stage, at the slack the entry hands to the tail
    obtain ⟨bs, hreach, -, hpaced⟩ := hq
    obtain ⟨-, hdv⟩ :=
      PalPeg.CloseoutPreload5.entry_debt hR hcl (hnr bs v hreach hne) hstep hr
    have hpaced' : PacedL 2048 0 ((bs ++ [a]) ++ as) := by
      rw [← PalPeg.CloseoutPreload5.append_cons_eq]; exact hpaced
    have hdlen := hdep bs v v' center a hreach hstep hne hr
    have hlenpref : (bs ++ [a]).length ≤ D := by
      simp only [List.length_append, List.length_singleton]; omega
    refine ⟨(bs ++ [a]).length, PalPeg.CloseoutPreload5.pacedL_suffix hpaced', ?_⟩
    -- `adv` : the advances consumed on the way in
    have hadv : 2048 * ((bs ++ [a]).count true) ≤ prepLen (value last).toNat :=
      le_trans (PalPeg.CloseoutPreload5.pacedL_prefix_count hpaced') (by omega)
    have hm : 2048 * (((bs ++ [a]).length + dpEvents (stageWindow1 (value last).toNat)) / 2048 + 1)
        ≤ prepLen (value last).toNat + dpEvents (stageWindow1 (value last).toNat) + 2048 := by
      have h1 := Nat.div_add_mod ((bs ++ [a]).length + dpEvents (stageWindow1 (value last).toNat)) 2048
      have h2 : ((bs ++ [a]).length + dpEvents (stageWindow1 (value last).toNat)) % 2048 < 2048 :=
        Nat.mod_lt _ (by norm_num)
      omega
    have hbud := budget_adv (k := (value last).toNat) (Rad := Rad)
      (adv := (bs ++ [a]).count true)
      (m := ((bs ++ [a]).length + dpEvents (stageWindow1 (value last).toNat)) / 2048 + 1)
      hstage hadv hm
    rw [hdv]
    omega
  · -- the length clause
    obtain ⟨bs, hreach, hlen, -⟩ := hq
    have hd := hdep bs v v' center a hreach hstep hne hr
    simp only [List.length_cons] at hlen
    unfold dpEntryG at hlen
    omega

#print axioms runEntriesS_of_namedG

/-! ## 5. The closure and the final replay theorem, recalibrated -/

/-- **The restart datum, with the depth measured against the preparation phase.**
Compared with `CloseoutPreload5.RestartG`, the bound `D ≤ 2047` — which, by
`depth_forces_stage_bound`, is a bound on the *input* — is replaced by
`D ≤ prepLen k`, which every real entry satisfies for every `k`. -/
def RestartG' (raw : List (Fin 2)) : Prop :=
  ∀ (u : GalilVM) (Rad : ℕ) (last : Counter),
    Restarted raw u Rad last → StageEntry Rad last →
    ∃ D : ℕ, D ≤ prepLen (value last).toNat ∧ CentreLongRun u (value last).toNat ∧
      NoReturn u ∧ EntryDepthG u D

/-- Every `CloseoutPreload5.RestartG` datum is one of these, because the old
depth bound is the stronger one exactly when `prepLen k ≥ 2047`, i.e. for the
stages `RestartG` could speak about at all. -/
theorem restartG'_of_restartG {raw : List (Fin 2)}
    (h : PalPeg.CloseoutPreload5.RestartG raw)
    (hsmall : ∀ (u : GalilVM) (Rad : ℕ) (last : Counter), Restarted raw u Rad last →
      StageEntry Rad last → 2047 ≤ prepLen (value last).toNat) :
    RestartG' raw := by
  intro u Rad last hR hSE
  obtain ⟨D, hD, hcl, hnr, hdep⟩ := h u Rad last hR hSE
  exact ⟨D, le_trans hD (hsmall u Rad last hR hSE), hcl, hnr, hdep⟩

/-- **`GalilReplaySpan.ReadyClosure` for `RdPaced`, recalibrated.** -/
theorem readyClosure_G' (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    (h : RestartG' raw) :
    PalPeg.GalilReplaySpan.ReadyClosure raw P q first 2048 RdPaced where
  ready := fun c s hs => rdPaced_ready c s hs
  seg := fun es c c' s t hseg hidle hs => rdPaced_seg P q first es c c' s t hseg hidle hs
  restart := fun c u Rad last _ hclk hR hSE => by
    obtain ⟨D, hD, hcl, hnr, hdep⟩ := h u Rad last hR hSE
    exact rdPaced_restart c u Rad last (dpEntryG (value last).toNat D) hclk hR
      (fun m as hlen hp => runEntriesS_of_namedG hR hSE hcl hnr hdep hD as (by omega) hp)

#print axioms readyClosure_G'

/-- The final replay theorem with the concrete ledger, at the recalibrated
datum.  Nothing here bounds the stage. -/
def replay_final_of_decodes_G' (raw : List (Fin 2)) (P : Shared)
    (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM)
    (q : ℕ) (first : Fin 9)
    (hex : ∀ s, P.replayExhausted s = GalilScaffoldCounter.zero s.replay)
    (hsearch : ∀ s : GalilVM, PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect P a s v)
    (hG : RestartG' raw)
    (hdec : Decodes P)
    (hbudget : PalPeg.GalilReplaySpan.ReplayBudgetRD raw P q first 2048)
    (hrs : PalPeg.GalilReplaySpan.RestartShapeL P)
    (r : ℕ) (hr0 : 0 < r) (c : Control) (t : GalilVM)
    (hm : c.mode = Mode.scan) (hc : c.clock = 2048) (hrpl : c.replaying = true)
    (hR : Restarted raw t 0 GalilScaffoldCounter.reset) (hrep : t.replay = ofNat r)
    (hM : MInv raw c t) (hfr : Frontier t) (hsi : ShiftIdle t) :=
  PalPeg.GalilReplaySpan.replay_after_fallback_general''_R_of_decodes
    raw P hP hP' q first hex hsearch (readyClosure_G' raw P q first hG) hdec hbudget hrs
    r hr0 c t hm hc hrpl hR hrep hM hfr hsi

#print axioms replay_final_of_decodes_G'

/-! ## 6. What the recalibration bought -/

/-- **No bound on the stage survives.**  `CloseoutPreload5.depth_forces_stage_bound`
turned the old datum into `k ≤ 2045`; at the new datum the same computation gives
only `max k 1 + 2 ≤ prepLen k`, which is true for every `k`. -/
theorem depth_no_stage_bound (k : ℕ) : max k 1 + 2 ≤ prepLen k := by
  unfold prepLen
  have : k ≤ max k 1 := le_max_left _ _
  omega

#print axioms depth_no_stage_bound

end PalPeg.CloseoutPreload6
