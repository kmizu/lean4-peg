import PalPeg.CloseoutPreload10

/-!
# The stage, re-indexed on `(k, m)`

`CloseoutPreload10` closed with a diagnosis rather than a theorem: the stage
chain of `CloseoutPreload8` reads a stage through **one** number `k`, used both
as the lower bound (`work = lower = ofNat k`, and in the debt budget
`3 * Rad ≤ 5 * k`) and as the window (`stageWindow1 k = 8 * max k 1 + 1`).  At a
restart the two agree; after a doubling they part company, because the span
doubles while `lower` is untouched.

This file separates them.  `k` is the **budget** index — the lower bound, moved
only by a restart — and `m` is the **window** index — the real span, doubled by
the `.double` phase.  Everything the chain needs is re-proved at `(k, m)`.

* §1 `stageCredit`, `budget_adv2` — the arithmetic.  The debt available to a
  stage is no longer `stageDebt Rad k` but `stageDebt Rad k + stageCredit k m`,
  where `stageCredit k m = (m - 8 * max k 1) / 4` is the `+1/4`-cell credit the
  `.double` phase accumulates while it scans the window.  `budget_adv2_nat` is
  `CloseoutPreload6.budget_adv_nat` with the window `m + 1` in place of
  `stageWindow1 k`; it closes for **every** `m ≥ 8 * max k 1`, because the credit
  grows like `m / 4` while the DP demand grows like `3186 * m / (64 * 2048)`,
  i.e. about `m / 41` (§1.3 `credit_double`, `budget_adv2_pow`).
* §2 `StageStart k m E v` — the common entry of a stage: either the `.grow`
  entry of a restart (`BeginAt`, and then `m = 8 * max k 1`) or the `.lower`
  entry of a doubling (`CloseoutPreload10.PrepAt k m`), with `E` the debt the
  stage starts with.  `stageStart_of_beginAt` / `stageStart_of_double_exit`.
* §3 `dpSafe_entry_km` — the DP entry at `(k, m)`: the window clause is
  `W.length ≤ m + 1` (the real window, `CloseoutPreload10.dpSafeStage_entry_real`)
  and the debt clause is `stageDebt Rad k + stageCredit k m - adv`.
* §4 `StagePrep2` / `stagePrep_next2` / `dpSafe_of_stagePrep2` / `StageInv2` /
  `runEntriesS_of_stageInv2` — `CloseoutPreload8` §5, re-indexed.
* §5 `RestartS2`, `readyClosure_S2`, `replay_final_of_decodes_S2`.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload11

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController
open PalPeg.GalilScaffoldPrepareControl (State)
open PalPeg.GalilScaffoldCounter (Counter Canonical value ofNat positive)
open PalPeg.CloseoutReadyStage (DpSafeStage PacedL RunEntriesS)
open PalPeg.CloseoutPreload (PreloadAt run_entry_preload rdPaced_ready rdPaced_seg
  rdPaced_restart RdPaced)
open PalPeg.CloseoutDebtAudit (dpEvents stageWindow1)
open PalPeg.CloseoutPreload5 (ReachP reachP_ne_run pacedL_prefix_count pacedL_suffix
  append_cons_eq)
open PalPeg.CloseoutPreload6 (prepLen prepLen_le)
open PalPeg.CloseoutPreload8 (BeginAt CentreLongAt DepthAt PostRun entry_shape_at
  entry_debt_at beginAt_of_restarted)
open PalPeg.CloseoutPreload10 (PrepAt prepAt_of_double_exit dpSafeStage_entry_real)
open PalPeg.GalilReplaySpan (stageDebt)

/-! ## 1. The arithmetic of a doubled stage -/

/-- **The doubling credit.**  A stage whose window is `m` rather than the
calibrated `8 * max k 1` has scanned `m - 8 * max k 1` extra cells since its
restart, and the `.double` phase credits a quarter of a unit of debt per cell
(`GalilScaffoldDouble.Run`'s balance `4 * debt + quarter`). -/
def stageCredit (k m : ℕ) : ℕ := (m - 8 * max k 1) / 4

theorem stageCredit_base (k : ℕ) : stageCredit k (8 * max k 1) = 0 := by
  unfold stageCredit; simp

/-- The DP demand of the window `m + 1`, bounded linearly. -/
theorem dpEvents_win_le (m : ℕ) : 64 * dpEvents (m + 1) ≤ 3186 * m + 4932 := by
  unfold PalPeg.CloseoutDebtAudit.dpEvents
  have h : 3186 * (m + 1) + 1683 + 63 = 3186 * m + 4932 := by ring
  rw [h, Nat.mul_comm]
  exact Nat.div_mul_le_self _ _

/-- **The core inequality at `(k, m)`.**  `CloseoutPreload6.budget_adv_nat` with
the calibrated window replaced by the real one and the budget enlarged by the
doubling credit. -/
theorem budget_adv2_nat {k Rad adv mm m : ℕ} (hstage : 3 * Rad ≤ 5 * k)
    (hm : 8 * max k 1 ≤ m)
    (hadv : 2048 * adv ≤ prepLen k)
    (hmm : 2048 * mm ≤ prepLen k + dpEvents (m + 1) + 2048) :
    adv + mm + Rad ≤ 2 * max k 1 + stageCredit k m := by
  have h1 := prepLen_le k
  have h2 := dpEvents_win_le m
  have h3 : k ≤ max k 1 := le_max_left _ _
  have h4 : 1 ≤ max k 1 := le_max_right _ _
  have h5 : max k 1 ≤ k + 1 := by omega
  have hq := Nat.div_add_mod (m - 8 * max k 1) 4
  have hq2 : (m - 8 * max k 1) % 4 < 4 := Nat.mod_lt _ (by norm_num)
  unfold stageCredit
  omega

/-- **The stage budget at `(k, m)`.**  `CloseoutPreload6.budget_adv` is the case
`m = 8 * max k 1`, where the credit is `0` (`stageCredit_base`). -/
theorem budget_adv2 {k Rad adv mm m : ℕ} (hstage : 3 * Rad ≤ 5 * k)
    (hm : 8 * max k 1 ≤ m)
    (hadv : 2048 * adv ≤ prepLen k)
    (hmm : 2048 * mm ≤ prepLen k + dpEvents (m + 1) + 2048) :
    (adv : ℤ) + (mm : ℤ) ≤ stageDebt Rad (k : ℤ) + (stageCredit k m : ℤ) := by
  have hnat := budget_adv2_nat hstage hm hadv hmm
  have hcast : (adv : ℤ) + (mm : ℤ) + (Rad : ℤ)
      ≤ 2 * max (k : ℤ) 1 + (stageCredit k m : ℤ) := by
    have h := (Nat.cast_le (α := ℤ)).mpr hnat
    push_cast at h
    exact h
  have hmax : stageDebt Rad (k : ℤ) = 2 * max (k : ℤ) 1 - (Rad : ℤ) := rfl
  rw [hmax]
  omega

#print axioms budget_adv2

/-! ### 1.3 The credit outruns the demand under doubling -/

/-- **NAMED — one doubling pays for itself and more.**  Doubling the window from
`m` to `2 * m` adds `m / 4` to the credit, while the DP demand it has to cover
grows only by about `m / 41`. -/
theorem credit_double {k m : ℕ} (hm : 8 * max k 1 ≤ m) :
    stageCredit k m + m / 4 ≤ stageCredit k (2 * m) := by
  unfold stageCredit
  have h1 := Nat.div_add_mod (m - 8 * max k 1) 4
  have h2 : (m - 8 * max k 1) % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have h3 := Nat.div_add_mod m 4
  have h4 : m % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have h5 := Nat.div_add_mod (2 * m - 8 * max k 1) 4
  have h6 : (2 * m - 8 * max k 1) % 4 < 4 := Nat.mod_lt _ (by norm_num)
  omega

/-- The window index stays above the calibration under doubling, so
`budget_adv2` applies at every stage of a doubling chain. -/
theorem le_double {k m : ℕ} (hm : 8 * max k 1 ≤ m) : 8 * max k 1 ≤ 2 * m := by omega

/-- **The budget after `j` doublings.**  With `m = 2 ^ j * (8 * max k 1)` the
inequality of `budget_adv2` still closes — the credit is never the binding
constraint. -/
theorem budget_adv2_pow {k Rad adv mm : ℕ} (j : ℕ) (hstage : 3 * Rad ≤ 5 * k)
    (hadv : 2048 * adv ≤ prepLen k)
    (hmm : 2048 * mm ≤ prepLen k + dpEvents (2 ^ j * (8 * max k 1) + 1) + 2048) :
    (adv : ℤ) + (mm : ℤ)
      ≤ stageDebt Rad (k : ℤ) + (stageCredit k (2 ^ j * (8 * max k 1)) : ℤ) := by
  refine budget_adv2 hstage ?_ hadv hmm
  have hp : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  calc 8 * max k 1 = 1 * (8 * max k 1) := by ring
    _ ≤ 2 ^ j * (8 * max k 1) := Nat.mul_le_mul_right _ hp

#print axioms budget_adv2_pow

/-! ## 2. The common stage entry -/

/-- **NAMED — the stage entry, on two indices.**  A stage begins either at the
`.grow` entry a restart installs — and then its window is the calibrated
`8 * max k 1` — or at the `.lower` entry the spent doubling phase dispatches
(`CloseoutPreload10.prepAt_of_double_exit`), whose window is whatever the
doubling produced.  `E` is the debt the stage starts with; `k` is the (unchanged)
lower bound. -/
structure StageStart (k m : ℕ) (E : ℤ) (v : SearchVM) : Prop where
  entry :
    (v.search.mode = GalilScaffoldSearchFinish.Mode.grow ∧
        v.search.work = ofNat (max k 1) ∧ v.search.span = ofNat 0 ∧
        m = 8 * max k 1) ∨ PrepAt k m v
  can : Canonical v.search.debt
  debt : E ≤ value v.search.debt
  low : v.lower = ofNat k
  calib : 8 * max k 1 ≤ m

/-- A restart's `begin` is a stage entry at the calibrated window. -/
theorem stageStart_of_beginAt {k Rad m : ℕ} {v : SearchVM} (hb : BeginAt k Rad v)
    (hm : m = 8 * max k 1) : StageStart k m (-(Rad : ℤ)) v where
  entry := Or.inl ⟨hb.mode, hb.work, hb.span, hm⟩
  can := hb.can
  debt := le_of_eq hb.debt.symm
  low := hb.low
  calib := by omega

/-- **NAMED — the doubling exit is a stage entry.**  The state the spent
`.double` phase dispatches satisfies `StageStart` at the *same* `k` and the
doubled window, with the debt paid down by at most one. -/
theorem stageStart_of_double_exit {c : GalilScaffoldPlace.Place} {t t' : SearchVM}
    {a : Bool} {k m : ℕ} {E : ℤ}
    (htm : t.search.mode = GalilScaffoldSearchFinish.Mode.double)
    (htw : positive t.search.work = false)
    (hsp : t.search.span = ofNat m) (hlow : t.lower = ofNat k)
    (hcal : 8 * max k 1 ≤ m)
    (hc : Canonical t.search.debt) (hE : E + 1 ≤ value t.search.debt)
    (hs : searchStep c a t t') : StageStart k m E t' := by
  obtain ⟨hprep, -, hdv⟩ := prepAt_of_double_exit htm htw hsp hlow hc hs
  refine ⟨Or.inr hprep, hprep.can, ?_, hprep.low, hcal⟩
  rw [hdv]; cases a <;> simp <;> omega

#print axioms stageStart_of_double_exit

/-! ## 3. The DP entry at `(k, m)` -/

/-- **NAMED — the DP entry, on two indices.**  The window clause reads the real
window (`W.length ≤ m + 1`), the budget clause reads
`stageDebt Rad k + stageCredit k m`, and the supply clause reads
`dpEvents (m + 1)`.  Nothing here mentions `stageWindow1 k`. -/
theorem dpSafe_entry_km {Rad k m L adv lower : ℕ} {v' : SearchVM} {W : List (Fin 3)}
    {as : List Bool}
    (hstage : 3 * Rad ≤ 5 * k) (hm : 8 * max k 1 ≤ m)
    (hW : W.length ≤ m + 1)
    (hadv : 2048 * adv ≤ prepLen k) (hL : L ≤ prepLen k)
    (hdp : v'.dp = ⟨GalilScaffoldPreload.initial W lower, false⟩)
    (hmode : v'.search.mode = .run)
    (hc : Canonical v'.search.debt)
    (hdebt : stageDebt Rad (k : ℤ) + (stageCredit k m : ℤ) - (adv : ℤ)
      ≤ value v'.search.debt)
    (hlen : dpEvents (m + 1) ≤ as.length)
    (hpaced : PacedL 2048 L as) :
    DpSafeStage v' as := by
  have hmono := PalPeg.CloseoutPreload9.dpEvents_mono hW
  set mm : ℕ := (L + dpEvents (m + 1)) / 2048 + 1 with hmmdef
  have hmm : 2048 * mm ≤ prepLen k + dpEvents (m + 1) + 2048 := by
    have h1 := Nat.div_add_mod (L + dpEvents (m + 1)) 2048
    have h2 : (L + dpEvents (m + 1)) % 2048 < 2048 := Nat.mod_lt _ (by norm_num)
    rw [hmmdef]
    omega
  have hbud := budget_adv2 (k := k) (Rad := Rad) (adv := adv) (mm := mm) (m := m)
    hstage hm hadv hmm
  refine dpSafeStage_entry_real v' W lower L as hdp hmode hc ?_ (by omega) hpaced
  have hstep : (L + dpEvents W.length) / 2048 ≤ (L + dpEvents (m + 1)) / 2048 :=
    Nat.div_le_div_right (by omega)
  have hcast : (((L + dpEvents W.length) / 2048 + 1 : ℕ) : ℤ) ≤ (mm : ℤ) :=
    Int.ofNat_le.mpr (by rw [hmmdef]; omega)
  omega

#print axioms dpSafe_entry_km

/-! ## 4. The stage invariant on `(k, m)` -/

/-- `CloseoutPreload8.StagePrep`, with the supply clause at the real window. -/
def StagePrep2 (_k m D : ℕ) (w v : SearchVM) (as : List Bool) : Prop :=
  ∃ bs : List Bool, ReachP w bs v ∧ D + dpEvents (m + 1) ≤ bs.length + as.length ∧
    PacedL 2048 0 (bs ++ as)

theorem stagePrep_next2 {k m D : ℕ} {w v v' : SearchVM} {c : GalilScaffoldPlace.Place}
    {a : Bool} {as : List Bool} (hq : StagePrep2 k m D w v (a :: as))
    (hs : searchStep c a v v')
    (hne : v'.search.mode ≠ GalilScaffoldSearchFinish.Mode.run) :
    StagePrep2 k m D w v' as := by
  obtain ⟨bs, hreach, hlen, hpaced⟩ := hq
  refine ⟨bs ++ [a], .snoc _ _ _ _ _ c hreach hs hne, ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton]
    simp only [List.length_cons] at hlen
    omega
  · rw [← append_cons_eq]; exact hpaced

/-- **NAMED — the entry clause at `(k, m)`, from a `.grow` stage entry.**
`CloseoutPreload8.dpSafe_of_stagePrep` re-proved through `dpSafe_entry_km`: the
window is read as `≤ m + 1`, the budget carries the credit, and `m` appears as
an index rather than as `stageWindow1 k`.  At a restart `m = 8 * max k 1` and the
credit is `0` (`stageCredit_base`), so this specialises to the old statement. -/
theorem dpSafe_of_stagePrep2 {u : GalilVM} {w : SearchVM} {k m Rad D : ℕ}
    (hb : BeginAt k Rad w) (hm : m = 8 * max k 1) (hstage : 3 * Rad ≤ 5 * k)
    (hcl : CentreLongAt w k) (hdep : DepthAt w D) (hD : D ≤ prepLen k)
    {v v' : SearchVM} {c : GalilScaffoldPlace.Place} {a : Bool} {as : List Bool}
    (hq : StagePrep2 k m D w v (a :: as)) (hs : searchStep c a v v')
    (hr : v'.search.mode = GalilScaffoldSearchFinish.Mode.run) :
    DpSafeStage v' as := by
  obtain ⟨bs, hreach, hlen, hpaced⟩ := hq
  have hne := reachP_ne_run hreach
  have hdlen := hdep bs v v' c a hreach hs hr
  obtain ⟨s, span, n, v0, hmo, hwk, hsp, h10, h7, hother, hcal, hv0, htrace, -⟩ :=
    entry_shape_at (u := u) hb hcl hreach hs hr
  have hpre := PalPeg.CloseoutPreload2.preloadAtEntry_of_trace s k span n k hmo hwk hsp
    h10 h7 hother hcal ⟨v0, hv0, htrace⟩ hs hne hr
  obtain ⟨W, lower, hW, hpreload⟩ := hpre
  obtain ⟨hcan, hdv⟩ := entry_debt_at (u := u) hb hcl hreach hs hr
  have hpaced' : PacedL 2048 0 ((bs ++ [a]) ++ as) := by
    rw [← append_cons_eq]; exact hpaced
  have hlenpref : (bs ++ [a]).length ≤ D := by
    simp only [List.length_append, List.length_singleton]; omega
  have hadv : 2048 * ((bs ++ [a]).count true) ≤ prepLen k :=
    le_trans (pacedL_prefix_count hpaced') (by omega)
  have hWm : W.length ≤ m + 1 := by
    rw [hW, hm]; unfold stageWindow1; omega
  have hmcal : 8 * max k 1 ≤ m := by omega
  have hcred : (stageCredit k m : ℤ) = 0 := by rw [hm, stageCredit_base]; simp
  refine dpSafe_entry_km (Rad := Rad) (k := k) (m := m) (L := (bs ++ [a]).length)
    (adv := (bs ++ [a]).count true) (lower := lower) hstage hmcal hWm hadv (by omega)
    (run_entry_preload hs hne hr hpreload) hr hcan ?_ ?_ (pacedL_suffix hpaced')
  · rw [hdv, hcred]
    have : stageDebt Rad ((k : ℕ) : ℤ) = stageDebt Rad (k : ℤ) := by norm_cast
    omega
  · have hlen' : D + dpEvents (m + 1) ≤ bs.length + (as.length + 1) := hlen
    omega

#print axioms dpSafe_of_stagePrep2

/-- `CloseoutPreload8.StageInv`, on two indices. -/
def StageInv2 (k m D : ℕ) (w v : SearchVM) (as : List Bool) : Prop :=
  StagePrep2 k m D w v as ∨ RunEntriesS as v

theorem runEntriesS_of_stageInv2 {u : GalilVM} {w : SearchVM} {k m Rad D : ℕ}
    (hb : BeginAt k Rad w) (hm : m = 8 * max k 1) (hstage : 3 * Rad ≤ 5 * k)
    (hcl : CentreLongAt w k) (hdep : DepthAt w D) (hD : D ≤ prepLen k)
    (hpost : PostRun) :
    ∀ (as : List Bool) (v : SearchVM), StageInv2 k m D w v as → RunEntriesS as v := by
  intro as
  induction as with
  | nil => intro v _; trivial
  | cons a as ih =>
    intro v hq
    rcases hq with hq | hq
    · intro c v' hstep
      by_cases hr : v'.search.mode = GalilScaffoldSearchFinish.Mode.run
      · have hsafe := dpSafe_of_stagePrep2 (u := u) hb hm hstage hcl hdep hD hq hstep hr
        exact ⟨fun _ _ _ => hsafe, hpost v' as hr hsafe⟩
      · exact ⟨fun _ _ h => absurd h hr,
          ih v' (Or.inl (stagePrep_next2 hq hstep hr))⟩
    · exact hq

#print axioms runEntriesS_of_stageInv2

/-! ## 5. The closure -/

/-- `CloseoutPreload8.RestartS`, unchanged: the two stage-local contracts. -/
def RestartS2 (raw : List (Fin 2)) : Prop :=
  ∀ (u : GalilVM) (Rad : ℕ) (last : Counter),
    Restarted raw u Rad last → StageEntry Rad last →
    ∃ D : ℕ, D ≤ prepLen (value last).toNat ∧
      CentreLongAt (searchLens.get u) (value last).toNat ∧
      DepthAt (searchLens.get u) D

theorem runEntriesS_of_restartS2 {raw : List (Fin 2)} {u : GalilVM} {Rad D : ℕ}
    {last : Counter} (hR : Restarted raw u Rad last) (hSE : StageEntry Rad last)
    (hcl : CentreLongAt (searchLens.get u) (value last).toNat)
    (hdep : DepthAt (searchLens.get u) D) (hD : D ≤ prepLen (value last).toNat)
    (hpost : PostRun) :
    ∀ (as : List Bool),
      D + dpEvents (8 * max (value last).toNat 1 + 1) ≤ as.length → PacedL 2048 0 as →
      RunEntriesS as (searchLens.get u) := by
  have hval : value last = ((value last).toNat : ℤ) :=
    (Int.toNat_of_nonneg hR.2.2.2.2.2.2.2.2.2).symm
  have hstage : 3 * Rad ≤ 5 * (value last).toNat := hSE _ hval
  intro as hlen hpaced
  refine runEntriesS_of_stageInv2 (u := u) (beginAt_of_restarted hR) rfl hstage hcl hdep hD
    hpost as _ (Or.inl ⟨[], .nil _ ?_, by simpa using hlen, by simpa using hpaced⟩)
  rw [(PalPeg.CloseoutPreload5.restart_facts hR).1]
  decide

#print axioms runEntriesS_of_restartS2

/-- **`GalilReplaySpan.ReadyClosure` for `RdPaced`, on the two-index stage.** -/
theorem readyClosure_S2 (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    (hpost : PostRun) (h : RestartS2 raw) :
    PalPeg.GalilReplaySpan.ReadyClosure raw P q first 2048 RdPaced where
  ready := fun c s hs => rdPaced_ready c s hs
  seg := fun es c c' s t hseg hidle hs => rdPaced_seg P q first es c c' s t hseg hidle hs
  restart := fun c u Rad last _ hclk hR hSE => by
    obtain ⟨D, hD, hcl, hdep⟩ := h u Rad last hR hSE
    exact rdPaced_restart c u Rad last
      (D + dpEvents (8 * max (value last).toNat 1 + 1)) hclk hR
      (fun m as hlen hp =>
        runEntriesS_of_restartS2 hR hSE hcl hdep hD hpost as (by omega) hp)

#print axioms readyClosure_S2

/-- The final replay theorem at the two-index stage datum. -/
def replay_final_of_decodes_S2 (raw : List (Fin 2)) (P : Shared)
    (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM)
    (q : ℕ) (first : Fin 9)
    (hex : ∀ s, P.replayExhausted s = GalilScaffoldCounter.zero s.replay)
    (hsearch : ∀ s : GalilVM, PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect P a s v)
    (hpost : PostRun) (hS : RestartS2 raw)
    (hdec : Decodes P)
    (hbudget : PalPeg.GalilReplaySpan.ReplayBudgetRD raw P q first 2048)
    (hrs : PalPeg.GalilReplaySpan.RestartShapeL P)
    (r : ℕ) (hr0 : 0 < r) (c : Control) (t : GalilVM)
    (hm : c.mode = Mode.scan) (hc : c.clock = 2048) (hrpl : c.replaying = true)
    (hR : Restarted raw t 0 GalilScaffoldCounter.reset) (hrep : t.replay = ofNat r)
    (hM : MInv raw c t) (hfr : Frontier t) (hsi : ShiftIdle t) :=
  PalPeg.GalilReplaySpan.replay_after_fallback_general''_R_of_decodes
    raw P hP hP' q first hex hsearch (readyClosure_S2 raw P q first hpost hS) hdec hbudget hrs
    r hr0 c t hm hc hrpl hR hrep hM hfr hsi

#print axioms replay_final_of_decodes_S2

/-!
## Note — what the re-indexing leaves open

The `(k, m)` split removes the *calibration* obstruction of `CloseoutPreload10`:
the budget (§1) closes for every window `m ≥ 8 * max k 1`, with room to spare
(`credit_double`), and the DP entry (§3) and the stage induction (§4) no longer
mention `stageWindow1 k` at all.  §2 gives the two constructors of a stage entry,
including the doubling exit.

The one fact still missing is the **preparation phase invariant from a `.lower`
entry**:

> `CloseoutPreload5.Phase`, re-proved from `PrepAt k m v` instead of from
> `BeginAt k Rad v`: along any `ReachP v bs x` the state stays in the
> preparation branch with span `ofNat m`, window
> `((stream walker).take (m + 1)).length = m + 1`, and debt
> `value v.search.debt - bs.count true`.

With that, `entry_shape_at` / `entry_debt_at` — and hence
`dpSafe_of_stagePrep2` — follow at a doubling entry exactly as they do at a
`.grow` entry here, and `PostRun` unwinds through `stageStart_of_double_exit`.

**無条件 PAL ∈ PEG は未完.**
-/

end PalPeg.CloseoutPreload11
