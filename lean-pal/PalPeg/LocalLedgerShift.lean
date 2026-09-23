import PalPeg.LocalTrackingLatch
import PalPeg.GalilLookRefined

/-!
# The deadline slot for the **local** run

`LocalTrackingLatch.pal_in_peg_of_local_latch` needs
`H_ledger : LedgerObligation … (fun w => stAbs S absS w x0) (fun w => |w|·nLocalL)`,
i.e. the ledger for the run the *local* machine abstracts to, at the shifted
deadline `|w|·τ` (`τ := nLocalL = 2^18`).  `GalilThrottledRunGen.ledger_throttledG`
and `GalilLookRefined.ledger_throttledLG'` prove the ledger for the *scheduled*
run `stTG` / `stLG'`, whose arrival counter is the schedule's `cfgG … .j` and
whose deadline is `(|w|+1)·τ`.  Neither shape matches `stAbs`:

* the local run's arrival counter is `arrL w s = min |w| ⌈s/τ⌉` — letter `m`
  (0-based) arrives *at* micro-step `m·τ`, one slot earlier than `cfgG`, which
  may only take letter `j` at `t ≥ j·τ`;
* the local run's tick counter is not a schedule but whatever the local core
  does: it ticks unless `S.Starved` holds.

So the O-step is re-proved here directly for a *tracking function* `K`
(`Sched`), and the three inputs of `LocalTrackingLatch.reported_of_shift`
(shifted O-step, zero backlog, refreshed report point at checkpoint `|w|`) are
assembled into `Reported … (|w|·τ)`.

`Sched` is the abstract form of "stutter iff starved": §6 builds it from the
starvation oracle of `LocalTrackingLatch` (`kOf`, `sched_of_starved`), counting
exactly the non-stuttering micro-steps of `micro` — the ticks that
`LocalTrackingLatch.run_progress` / `abstractRun_of_oracles` produce.

**Still hypotheses here** (oracles 1–3 of `LocalTrackingLatch`, proved
elsewhere): the tracking equation `habs` (the local run's abstraction *is* the
truncated pre-loaded trace), the pre-loaded trace's `PreloadL'` data, the
checkpoint costs, and the report point at `Tc |w|`.  Unconditional `PAL ∈ PEG`
is **not** finished.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.LocalLedgerShift

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilLatchTracking PalPeg.GalilArriveChain PalPeg.GalilThrottledRun
open PalPeg.GalilLedgerQ64 PalPeg.LocalTrackingLatch

/-! ## 1. The local arrival counter -/

theorem arrL_mono (w : List (Fin 2)) {s s' : ℕ} (h : s ≤ s') : arrL w s ≤ arrL w s' := by
  unfold arrL; rw [nLocalL_eq]; omega

theorem arrL_le (w : List (Fin 2)) (s : ℕ) : arrL w s ≤ w.length := by
  unfold arrL; omega

/-- After micro-step `m·τ` (the arrival slot of letter `m`) at least `m+1`
letters have arrived. -/
theorem arrL_ge (w : List (Fin 2)) (m s : ℕ) (hm : m < w.length) (hs : m * nLocalL < s) :
    m + 1 ≤ arrL w s := by
  unfold arrL
  rw [nLocalL_eq] at hs ⊢
  omega

/-- Number of arrival slots in the micro-step window `[t0, t0+L)`. -/
def cnt (t0 L : ℕ) : ℕ :=
  (t0 + L + nLocalL - 1) / nLocalL - (t0 + nLocalL - 1) / nLocalL

theorem cnt_zero (t0 : ℕ) : cnt t0 0 = 0 := by
  unfold cnt; rw [nLocalL_eq]; simp only [Nat.add_zero]; omega

theorem cnt_step_arrival (t0 L : ℕ) (h : (t0 + L) % nLocalL = 0) :
    cnt t0 (L+1) = cnt t0 L + 1 := by
  unfold cnt
  rw [nLocalL_eq] at h ⊢
  omega

theorem cnt_step_le (t0 L : ℕ) : cnt t0 L ≤ cnt t0 (L+1) := by
  unfold cnt; rw [nLocalL_eq]; omega

/-! ## 2. The tracking function and the window lemma -/

/-- **What the local run does to the pre-loaded trace's index.**  `K s` is the
pre-loaded index the local state after `s` micro-steps stands for: it never
moves by more than one, it moves at a non-arrival micro-step whose need has
arrived (no starvation), and it moves only when the need has arrived (stutter
while starved). -/
structure Sched (w : List (Fin 2)) (nd gd : ℕ → ℕ) (e : ℕ) (K : ℕ → ℕ) : Prop where
  k0 : K 0 = 0
  mono : ∀ s, K s ≤ K (s+1)
  step_le : ∀ s, K (s+1) ≤ K s + 1
  progress : ∀ s, inp w s = none → K s < e → nd (K s) ≤ arrL w s → K (s+1) = K s + 1
  /-- What a tick guarantees: `gd` may be weaker than the need `nd` that forces a tick (a tick
  can be legitimate although the lookahead of its target has not arrived). -/
  guard : ∀ s, K s < e → K (s+1) = K s + 1 → gd (K s) ≤ arrL w s

theorem Sched.mono_le {w : List (Fin 2)} {nd gd : ℕ → ℕ} {e : ℕ} {K : ℕ → ℕ}
    (hs : Sched w nd gd e K) {s s' : ℕ} (h : s ≤ s') : K s ≤ K s' := by
  induction s' with
  | zero => have : s = 0 := by omega
            subst this; exact le_rfl
  | succ s' ih =>
      by_cases h' : s ≤ s'
      · exact le_trans (ih h') (hs.mono s')
      · have : s = s' + 1 := by omega
        subst this; exact le_rfl

/-- **The consumed prefix has arrived.**  If `f` is the per-index need and `nd`
the per-tick need (`f i ≤ nd k` for `i ≤ k+1`), the pre-loaded index `K s` never
needs more letters than have arrived by `s`. -/
theorem used_le_arr {w : List (Fin 2)} {nd gd : ℕ → ℕ} {e : ℕ} {K : ℕ → ℕ}
    (hs : Sched w nd gd e K) (f : ℕ → ℕ) (hf0 : f 0 = 0)
    (hfgd : ∀ k, f (k+1) ≤ gd k) : ∀ s, K s ≤ e → f (K s) ≤ arrL w s := by
  intro s
  induction s with
  | zero => intro _; rw [hs.k0, hf0]; exact Nat.zero_le _
  | succ s ih =>
      intro hbound
      rcases Nat.eq_or_lt_of_le (hs.mono s) with h | h
      · rw [← h]; exact le_trans (ih (h ▸ hbound)) (arrL_mono w (Nat.le_succ s))
      · have he : K (s+1) = K s + 1 := by have := hs.step_le s; omega
        rw [he]
        exact le_trans (hfgd (K s))
          (le_trans (hs.guard s (by omega) he) (arrL_mono w (Nat.le_succ s)))

/-- **No stutter inside a window whose needs have arrived**, except at the
arrival slots themselves. -/
theorem windowL {w : List (Fin 2)} {nd gd : ℕ → ℕ} {e : ℕ} {K : ℕ → ℕ} (hs : Sched w nd gd e K)
    (B J t0 : ℕ) (hB : B ≤ e) (hnd : ∀ k, k < B → nd k ≤ J)
    (hJ : ∀ s, t0 ≤ s → inp w s = none → J ≤ arrL w s) :
    ∀ L, K (t0+L) < B → K t0 + L ≤ K (t0+L) + cnt t0 L := by
  intro L
  induction L with
  | zero => intro _; simp only [Nat.add_zero, cnt_zero]; exact le_rfl
  | succ L ih =>
      intro hK
      have heq : t0 + (L+1) = (t0 + L) + 1 := by omega
      rw [heq] at hK ⊢
      have hKL : K (t0+L) < B := lt_of_le_of_lt (hs.mono (t0+L)) hK
      have ih' := ih hKL
      have hc := cnt_step_le t0 L
      cases hi : inp w (t0+L) with
      | some a =>
          have h0 := (inp_some w (t0+L) a hi).1
          rw [cnt_step_arrival t0 L h0]
          have := hs.mono (t0+L)
          omega
      | none =>
          have hprog := hs.progress (t0+L) hi (lt_of_lt_of_le hKL hB)
            (le_trans (hnd _ hKL) (hJ _ (Nat.le_add_right _ _) hi))
          omega

/-- **The shifted O-step for the local run.**  Letter `m` is available from
micro-step `m·τ + 1`, so the window may start at `max t1 (m·τ)` — one slot
earlier than `GalilThrottledRunGen.ostepG`, which starts at `max t1 ((m+1)·τ)`. -/
theorem ostepL {w : List (Fin 2)} {nd gd : ℕ → ℕ} {K : ℕ → ℕ} {e : ℕ} (hs : Sched w nd gd e K)
    (Tc : ℕ → ℕ) (m : ℕ) (hm : m < w.length) (hTc : Tc m ≤ Tc (m+1)) (hTe : Tc (m+1) ≤ e)
    (hnd : ∀ k, k < Tc (m+1) → nd k ≤ m+1) (t1 : ℕ) (hK1 : Tc m ≤ K t1) :
    Tc (m+1) ≤ K (max t1 (m * nLocalL) + (2 * (Tc (m+1) - Tc m) + 1)) := by
  generalize ht0 : max t1 (m * nLocalL) = t0
  have ha : t1 ≤ t0 := ht0 ▸ le_max_left _ _
  have hb : m * nLocalL ≤ t0 := ht0 ▸ le_max_right _ _
  generalize hL : 2 * (Tc (m+1) - Tc m) + 1 = L
  by_contra hlt
  have hlt' : K (t0 + L) < Tc (m+1) := by omega
  have hJ : ∀ s, t0 ≤ s → inp w s = none → m + 1 ≤ arrL w s := by
    intro s hsle hi
    have hne : s ≠ m * nLocalL := by
      intro hc
      rw [hc, inp_at w m hm] at hi
      cases hi
    exact arrL_ge w m s hm (by omega)
  have hw := windowL hs (Tc (m+1)) (m+1) t0 hTe hnd hJ L hlt'
  have hk0 : Tc m ≤ K t0 := le_trans hK1 (hs.mono_le ha)
  have hcnt : cnt t0 L = (t0 + L + nLocalL - 1) / nLocalL - (t0 + nLocalL - 1) / nLocalL := rfl
  rw [nLocalL_eq] at hcnt
  omega

/-! ## 3. The local checkpoint times -/

open Classical in
/-- The first micro-step at which the local run has reached pre-loaded
checkpoint `Tc m`. -/
noncomputable def TA (K Tc : ℕ → ℕ) (m : ℕ) : ℕ :=
  if h : ∃ s, Tc m ≤ K s then Nat.find h else 0

theorem TA_spec (K Tc : ℕ → ℕ) (m : ℕ) (h : ∃ s, Tc m ≤ K s) :
    Tc m ≤ K (TA K Tc m) ∧ ∀ s, Tc m ≤ K s → TA K Tc m ≤ s := by
  unfold TA
  rw [dif_pos h]
  exact ⟨Nat.find_spec h, fun s hsx => Nat.find_min' h hsx⟩

theorem TA_exact {w : List (Fin 2)} {nd gd : ℕ → ℕ} {e : ℕ} {K : ℕ → ℕ} (hs : Sched w nd gd e K)
    (Tc : ℕ → ℕ) (m : ℕ) (h : ∃ s, Tc m ≤ K s) : K (TA K Tc m) = Tc m := by
  obtain ⟨h1, h2⟩ := TA_spec K Tc m h
  refine le_antisymm ?_ h1
  rcases hT : TA K Tc m with _ | s'
  · rw [hs.k0]; rw [hT, hs.k0] at h1; omega
  · have hlt : ¬ Tc m ≤ K s' := fun hc => by have := h2 s' hc; omega
    have := hs.step_le s'
    omega

/-- Every checkpoint up to `|w|` is reached. -/
theorem TA_exists {w : List (Fin 2)} {nd gd : ℕ → ℕ} {K : ℕ → ℕ} {Tc : ℕ → ℕ}
    (hs : Sched w nd gd (Tc w.length) K) (htc0 : Tc 0 = 0)
    (htcm : ∀ m, m < w.length → Tc m ≤ Tc (m+1))
    (hnd : ∀ m, m < w.length → ∀ k, k < Tc (m+1) → nd k ≤ m+1) :
    ∀ m, m ≤ w.length → ∃ s, Tc m ≤ K s := by
  intro m
  induction m with
  | zero => intro _; exact ⟨0, by rw [htc0]; exact Nat.zero_le _⟩
  | succ m ih =>
      intro hm
      obtain ⟨hK, -⟩ := TA_spec K Tc m (ih (by omega))
      exact ⟨_, ostepL hs Tc m hm (htcm m hm)
        (PalPeg.GalilCheckpoints.mono_of_step Tc w.length htcm (m+1) w.length hm le_rfl)
        (hnd m hm) _ hK⟩

theorem TA_zero {w : List (Fin 2)} {nd gd : ℕ → ℕ} {K : ℕ → ℕ} {Tc : ℕ → ℕ}
    (hs : Sched w nd gd (Tc w.length) K) (htc0 : Tc 0 = 0)
    (htcm : ∀ m, m < w.length → Tc m ≤ Tc (m+1))
    (hnd : ∀ m, m < w.length → ∀ k, k < Tc (m+1) → nd k ≤ m+1) :
    TA K Tc 0 = 0 := by
  have h := TA_exists hs htc0 htcm hnd 0 (Nat.zero_le _)
  have := (TA_spec K Tc 0 h).2 0 (by rw [htc0]; exact Nat.zero_le _)
  omega

/-- **(1) The shifted O-step**, in the shape `LocalTrackingLatch.reported_of_shift`
consumes: the deadline slope is `m·τ`, not `(m+1)·τ`. -/
theorem O_step_local {w : List (Fin 2)} {nd gd : ℕ → ℕ} {K : ℕ → ℕ} {Tc : ℕ → ℕ}
    (hs : Sched w nd gd (Tc w.length) K) (htc0 : Tc 0 = 0)
    (htcm : ∀ m, m < w.length → Tc m ≤ Tc (m+1))
    (hnd : ∀ m, m < w.length → ∀ k, k < Tc (m+1) → nd k ≤ m+1)
    (m : ℕ) (hm : m < w.length) :
    TA K Tc (m+1) ≤ max (TA K Tc m) (m * nLocalL) + dwT Tc (m+1) := by
  obtain ⟨hK, -⟩ := TA_spec K Tc m (TA_exists hs htc0 htcm hnd m hm.le)
  have ho := ostepL hs Tc m hm (htcm m hm)
    (PalPeg.GalilCheckpoints.mono_of_step Tc w.length htcm (m+1) w.length hm le_rfl)
    (hnd m hm) _ hK
  have := (TA_spec K Tc (m+1) (TA_exists hs htc0 htcm hnd (m+1) hm)).2 _ ho
  simpa [dwT] using this

/-! ## 4. The deadline: `Reported` by `|w|·τ` -/

/-- **The local ledger, per word.**  The three inputs of `reported_of_shift`:
(1) the shifted O-step `O_step_local`; (2) zero backlog at `|w|`
(`GalilLedgerThrottled.backlog_zero_trunc'` with the throttled work `dwT`);
(3) a refreshed report point at checkpoint `|w|`, transported along the tracking
equation `habs` (at `TA K Tc |w|` all letters have arrived, so the truncation is
the identity). -/
theorem reported_local (P : Shared) (q : ℕ) (first : Fin 9) (w : List (Fin 2))
    (hw : 0 < w.length) (hpal : w ∈ PAL) (st run : ℕ → State GalilVM) (nd gd f K Tc : ℕ → ℕ)
    (hs : Sched w nd gd (Tc w.length) K)
    (hf0 : f 0 = 0) (hfgd : ∀ k, f (k+1) ≤ gd k)
    (htc0 : Tc 0 = 0) (htcm : ∀ m, m < w.length → Tc m ≤ Tc (m+1))
    (hnd : ∀ m, m < w.length → ∀ k, k < Tc (m+1) → nd k ≤ m+1)
    (hbase : Tc 1 ≤ 2050)
    (hcost : ∀ m, 1 ≤ m → m < w.length →
      Tc (m+1) - Tc m ≤ alpha' 2048 * (Cw w (m+1) - Cw w m) + beta' 2048)
    (hend : w.length ≤ f (Tc w.length))
    (habs : ∀ s, K s ≤ Tc w.length → run s = truncS (w.length - arrL w s) (st (K s)))
    (hrep : GalilLedgerAssembly.ReportPointAt P q first w w.length (st (Tc w.length))) :
    Reported P q first w run (w.length * nLocalL - 1) := by
  set α := 2 * alpha' 2048 with hα
  set β := 2 * beta' 2048 + 1 with hβ
  have hτ : 2 * (α + β) ≤ nLocalL := by
    have h := GalilLedgerThrottled.two_c2_le_τ'
    unfold GalilLedgerThrottled.c2 GalilLedgerThrottled.τ' at h
    unfold nLocalL
    omega
  -- (2) zero backlog at `|w|`
  have hz : PalPeg.Predictability.backlog
      (fun m => if m ≤ w.length then dwT Tc m else 0) (α + β) w.length = 0 :=
    GalilLedgerThrottled.backlog_zero_trunc' α β nLocalL hτ w hw hpal (dwT Tc)
      (fun m hm => GalilLedgerThrottled.dwT_cost w Tc htc0 hbase hcost m hm)
  -- (1) the shifted O-step, for the checkpoint times truncated at `|w|`
  have hstep : ∀ m, TA K Tc (min (m+1) w.length) ≤
      max (TA K Tc (min m w.length)) (m * nLocalL) +
        (if m+1 ≤ w.length then dwT Tc (m+1) else 0) := by
    intro m
    by_cases hm : m < w.length
    · have e1 : min (m+1) w.length = m+1 := by omega
      have e2 : min m w.length = m := by omega
      have e3 : m+1 ≤ w.length := hm
      rw [e1, e2, if_pos e3]
      exact O_step_local hs htc0 htcm hnd m hm
    · have e1 : min (m+1) w.length = w.length := by omega
      have e2 : min m w.length = w.length := by omega
      have e3 : ¬ (m+1 ≤ w.length) := by omega
      rw [e1, e2, if_neg e3]
      exact le_trans (le_max_left _ _) (Nat.le_add_right _ _)
  -- (3) the report point at checkpoint `|w|`, transported by the tracking equation
  have hfull : arrL w (TA K Tc w.length) = w.length := by
    have h2 := TA_exact hs Tc w.length (TA_exists hs htc0 htcm hnd w.length le_rfl)
    have h1 := used_le_arr hs f hf0 hfgd (TA K Tc w.length) (le_of_eq h2)
    have h3 := arrL_le w (TA K Tc w.length)
    rw [h2] at h1
    omega
  have hrun : run (TA K Tc w.length) = st (Tc w.length) := by
    rw [habs _ (le_of_eq (TA_exact hs Tc w.length (TA_exists hs htc0 htcm hnd w.length le_rfl))),
      hfull, Nat.sub_self, truncS_zero,
      TA_exact hs Tc w.length (TA_exists hs htc0 htcm hnd w.length le_rfl)]
  obtain ⟨hrp, hfr⟩ := GalilLedgerAssembly.reportPoint_of_at_length hw hrep
  have hrep' : ReportPoint w (run (TA K Tc (min w.length w.length))) ∧
      Refreshed P q first (run (TA K Tc (min w.length w.length))) := by
    rw [min_self, hrun]; exact ⟨hrp, hfr⟩
  have hτs : 2 * (α + β) < nLocalL := by
    rw [hα, hβ, nLocalL_eq]
    decide
  exact reported_of_shift_early P q first w hw run (fun m => TA K Tc (min m w.length))
    (fun m => if m ≤ w.length then dwT Tc m else 0) (α + β) hτs
    (by simp only [Nat.zero_min]; exact TA_zero hs htc0 htcm hnd) hstep hz hrep'


theorem reported_local_with (P : Shared) (q : ℕ) (first : Fin 9) (w : List (Fin 2))
    (hw : 0 < w.length) (hpal : w ∈ PAL) (st run : ℕ → State GalilVM) (nd gd f K Tc : ℕ → ℕ)
    (hs : Sched w nd gd (Tc w.length) K)
    (hf0 : f 0 = 0) (hfgd : ∀ k, f (k+1) ≤ gd k)
    (htc0 : Tc 0 = 0) (htcm : ∀ m, m < w.length → Tc m ≤ Tc (m+1))
    (hnd : ∀ m, m < w.length → ∀ k, k < Tc (m+1) → nd k ≤ m+1)
    (hbase : Tc 1 ≤ 2050)
    (hcost : ∀ m, 1 ≤ m → m < w.length →
      Tc (m+1) - Tc m ≤ alpha' 2048 * (Cw w (m+1) - Cw w m) + beta' 2048)
    (hend : w.length ≤ f (Tc w.length))
    (habs : ∀ s, K s ≤ Tc w.length → run s = truncS (w.length - arrL w s) (st (K s)))
    (hrep : GalilLedgerAssembly.ReportPointAt P q first w w.length (st (Tc w.length)))
    (R : State GalilVM → Prop) (hR : R (st (Tc w.length))) :
    ∃ t ≤ w.length * nLocalL - 1, ReportPoint w (run t) ∧ Refreshed P q first (run t) ∧ R (run t) := by
  set α := 2 * alpha' 2048 with hα
  set β := 2 * beta' 2048 + 1 with hβ
  have hτ : 2 * (α + β) ≤ nLocalL := by
    have h := GalilLedgerThrottled.two_c2_le_τ'
    unfold GalilLedgerThrottled.c2 GalilLedgerThrottled.τ' at h
    unfold nLocalL
    omega
  -- (2) zero backlog at `|w|`
  have hz : PalPeg.Predictability.backlog
      (fun m => if m ≤ w.length then dwT Tc m else 0) (α + β) w.length = 0 :=
    GalilLedgerThrottled.backlog_zero_trunc' α β nLocalL hτ w hw hpal (dwT Tc)
      (fun m hm => GalilLedgerThrottled.dwT_cost w Tc htc0 hbase hcost m hm)
  -- (1) the shifted O-step, for the checkpoint times truncated at `|w|`
  have hstep : ∀ m, TA K Tc (min (m+1) w.length) ≤
      max (TA K Tc (min m w.length)) (m * nLocalL) +
        (if m+1 ≤ w.length then dwT Tc (m+1) else 0) := by
    intro m
    by_cases hm : m < w.length
    · have e1 : min (m+1) w.length = m+1 := by omega
      have e2 : min m w.length = m := by omega
      have e3 : m+1 ≤ w.length := hm
      rw [e1, e2, if_pos e3]
      exact O_step_local hs htc0 htcm hnd m hm
    · have e1 : min (m+1) w.length = w.length := by omega
      have e2 : min m w.length = w.length := by omega
      have e3 : ¬ (m+1 ≤ w.length) := by omega
      rw [e1, e2, if_neg e3]
      exact le_trans (le_max_left _ _) (Nat.le_add_right _ _)
  -- (3) the report point at checkpoint `|w|`, transported by the tracking equation
  have hfull : arrL w (TA K Tc w.length) = w.length := by
    have h2 := TA_exact hs Tc w.length (TA_exists hs htc0 htcm hnd w.length le_rfl)
    have h1 := used_le_arr hs f hf0 hfgd (TA K Tc w.length) (le_of_eq h2)
    have h3 := arrL_le w (TA K Tc w.length)
    rw [h2] at h1
    omega
  have hrun : run (TA K Tc w.length) = st (Tc w.length) := by
    rw [habs _ (le_of_eq (TA_exact hs Tc w.length (TA_exists hs htc0 htcm hnd w.length le_rfl))),
      hfull, Nat.sub_self, truncS_zero,
      TA_exact hs Tc w.length (TA_exists hs htc0 htcm hnd w.length le_rfl)]
  obtain ⟨hrp, hfr⟩ := GalilLedgerAssembly.reportPoint_of_at_length hw hrep
  have hrep' : ReportPoint w (run (TA K Tc (min w.length w.length))) ∧
      Refreshed P q first (run (TA K Tc (min w.length w.length))) := by
    rw [min_self, hrun]; exact ⟨hrp, hfr⟩
  have hτs : 2 * (α + β) < nLocalL := by
    rw [hα, hβ, nLocalL_eq]
    decide
  obtain ⟨t', ht', hrp', hrf'⟩ := reported_of_shift_early P q first w hw run
    (fun m => TA K Tc (min m w.length))
    (fun m => if m ≤ w.length then dwT Tc m else 0) (α + β) hτs
    (by simp only [Nat.zero_min]; exact TA_zero hs htc0 htcm hnd) hstep hz hrep'
  -- the witness `reported_of_shift_early` returns is the checkpoint itself
  refine ⟨TA K Tc (min w.length w.length), ?_, hrep'.1, hrep'.2, ?_⟩
  · have hle := run_on_time_shift_slack (fun m => if m ≤ w.length then dwT Tc m else 0)
      (α + β) nLocalL hτs.le (fun m => TA K Tc (min m w.length))
      (by simp only [Nat.zero_min]; exact TA_zero hs htc0 htcm hnd) hstep w.length hw hz
    omega
  · rw [min_self, hrun]; exact hR

/-! ## 5. The ledger obligation -/

/-- **Oracle 4 of `LocalTrackingLatch`, generic form.** -/
theorem ledger_local (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ)
    (firstOf : List (Fin 2) → Fin 9) (stOf runOf : List (Fin 2) → ℕ → State GalilVM)
    (ndOf gdOf fOf KOf TcOf : List (Fin 2) → ℕ → ℕ)
    (hs : ∀ w : List (Fin 2), 0 < w.length →
      Sched w (ndOf w) (gdOf w) (TcOf w w.length) (KOf w))
    (hf0 : ∀ w : List (Fin 2), 0 < w.length → fOf w 0 = 0)
    (hfgd : ∀ (w : List (Fin 2)), 0 < w.length → ∀ k, fOf w (k+1) ≤ gdOf w k)
    (htc0 : ∀ w : List (Fin 2), 0 < w.length → TcOf w 0 = 0)
    (htcm : ∀ (w : List (Fin 2)), 0 < w.length → ∀ m, m < w.length → TcOf w m ≤ TcOf w (m+1))
    (hnd : ∀ (w : List (Fin 2)), 0 < w.length → ∀ m, m < w.length → ∀ k, k < TcOf w (m+1) →
      ndOf w k ≤ m+1)
    (hbase : ∀ w : List (Fin 2), 0 < w.length → TcOf w 1 ≤ 2050)
    (hcost : ∀ (w : List (Fin 2)), 0 < w.length → ∀ m, 1 ≤ m → m < w.length →
      TcOf w (m+1) - TcOf w m ≤ alpha' 2048 * (Cw w (m+1) - Cw w m) + beta' 2048)
    (hend : ∀ w : List (Fin 2), 0 < w.length → w.length ≤ fOf w (TcOf w w.length))
    (habs : ∀ (w : List (Fin 2)), 0 < w.length → ∀ s, KOf w s ≤ TcOf w w.length →
      runOf w s = truncS (w.length - arrL w s) (stOf w (KOf w s)))
    (hrep : ∀ w : List (Fin 2), 0 < w.length →
      GalilLedgerAssembly.ReportPointAt (Pof w) (qof w) (firstOf w) w w.length
        (stOf w (TcOf w w.length))) :
    LedgerObligation Pof qof firstOf runOf (fun w => w.length * nLocalL - 1) :=
  fun w hw hpal =>
    reported_local (Pof w) (qof w) (firstOf w) w hw hpal (stOf w) (runOf w) (ndOf w) (gdOf w) (fOf w)
      (KOf w) (TcOf w) (hs w hw) (hf0 w hw) (hfgd w hw) (htc0 w hw) (htcm w hw) (hnd w hw)
      (hbase w hw) (hcost w hw) (hend w hw) (habs w hw) (hrep w hw)


/-- The ledger with an extra fact `R` carried from the checkpoint to the witness. -/
def LedgerWith (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ)
    (firstOf : List (Fin 2) → Fin 9) (runOf : List (Fin 2) → ℕ → State GalilVM)
    (T : List (Fin 2) → ℕ) (R : List (Fin 2) → State GalilVM → Prop) : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → w ∈ PAL →
    ∃ t ≤ T w, ReportPoint w (runOf w t) ∧ Refreshed (Pof w) (qof w) (firstOf w) (runOf w t) ∧
      R w (runOf w t)

theorem ledger_local_with (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ)
    (firstOf : List (Fin 2) → Fin 9) (stOf runOf : List (Fin 2) → ℕ → State GalilVM)
    (ndOf gdOf fOf KOf TcOf : List (Fin 2) → ℕ → ℕ)
    (hs : ∀ w : List (Fin 2), 0 < w.length →
      Sched w (ndOf w) (gdOf w) (TcOf w w.length) (KOf w))
    (hf0 : ∀ w : List (Fin 2), 0 < w.length → fOf w 0 = 0)
    (hfgd : ∀ (w : List (Fin 2)), 0 < w.length → ∀ k, fOf w (k+1) ≤ gdOf w k)
    (htc0 : ∀ w : List (Fin 2), 0 < w.length → TcOf w 0 = 0)
    (htcm : ∀ (w : List (Fin 2)), 0 < w.length → ∀ m, m < w.length → TcOf w m ≤ TcOf w (m+1))
    (hnd : ∀ (w : List (Fin 2)), 0 < w.length → ∀ m, m < w.length → ∀ k, k < TcOf w (m+1) →
      ndOf w k ≤ m+1)
    (hbase : ∀ w : List (Fin 2), 0 < w.length → TcOf w 1 ≤ 2050)
    (hcost : ∀ (w : List (Fin 2)), 0 < w.length → ∀ m, 1 ≤ m → m < w.length →
      TcOf w (m+1) - TcOf w m ≤ alpha' 2048 * (Cw w (m+1) - Cw w m) + beta' 2048)
    (hend : ∀ w : List (Fin 2), 0 < w.length → w.length ≤ fOf w (TcOf w w.length))
    (habs : ∀ (w : List (Fin 2)), 0 < w.length → ∀ s, KOf w s ≤ TcOf w w.length →
      runOf w s = truncS (w.length - arrL w s) (stOf w (KOf w s)))
    (hrep : ∀ w : List (Fin 2), 0 < w.length →
      GalilLedgerAssembly.ReportPointAt (Pof w) (qof w) (firstOf w) w w.length
        (stOf w (TcOf w w.length)))
    (R : List (Fin 2) → State GalilVM → Prop)
    (hR : ∀ w : List (Fin 2), 0 < w.length → R w (stOf w (TcOf w w.length))) :
    LedgerWith Pof qof firstOf runOf (fun w => w.length * nLocalL - 1) R :=
  fun w hw hpal =>
    reported_local_with (Pof w) (qof w) (firstOf w) w hw hpal (stOf w) (runOf w) (ndOf w) (gdOf w) (fOf w)
      (KOf w) (TcOf w) (hs w hw) (hf0 w hw) (hfgd w hw) (htc0 w hw) (htcm w hw) (hnd w hw)
      (hbase w hw) (hcost w hw) (hend w hw) (habs w hw) (hrep w hw) (R w) (hR w hw)

/-- **Oracle 4 with the refined lookahead need** (`GalilLookRefined.PreloadL'`):
`nd := needT'`, `f := needL'`, and the end bound `|w| ≤ needL' (Tc |w|)` comes
from the report point itself (`GalilThrottledRun.used_of_report`). -/
theorem ledger_localL' (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ)
    (firstOf : List (Fin 2) → Fin 9) (stOf runOf : List (Fin 2) → ℕ → State GalilVM)
    (KOf TcOf : List (Fin 2) → ℕ → ℕ)
    (hpre : ∀ w : List (Fin 2), 0 < w.length →
      GalilLookRefined.PreloadL' w (stOf w) (TcOf w))
    (hs : ∀ w : List (Fin 2), 0 < w.length →
      Sched w (GalilLookRefined.needT' w (stOf w)) (fun k => needS w (stOf w) (k+1))
        (TcOf w w.length) (KOf w))
    (hbase : ∀ w : List (Fin 2), 0 < w.length → TcOf w 1 ≤ 2050)
    (hcost : ∀ (w : List (Fin 2)), 0 < w.length → ∀ m, 1 ≤ m → m < w.length →
      TcOf w (m+1) - TcOf w m ≤ alpha' 2048 * (Cw w (m+1) - Cw w m) + beta' 2048)
    (habs : ∀ (w : List (Fin 2)), 0 < w.length → ∀ s, KOf w s ≤ TcOf w w.length →
      runOf w s = truncS (w.length - arrL w s) (stOf w (KOf w s)))
    (hrep : ∀ w : List (Fin 2), 0 < w.length →
      GalilLedgerAssembly.ReportPointAt (Pof w) (qof w) (firstOf w) w w.length
        (stOf w (TcOf w w.length))) :
    LedgerObligation Pof qof firstOf runOf (fun w => w.length * nLocalL - 1) :=
  ledger_local Pof qof firstOf stOf runOf
    (fun w => GalilLookRefined.needT' w (stOf w)) (fun w k => needS w (stOf w) (k+1))
    (fun w => needS w (stOf w))
    KOf TcOf hs
    (fun w hw => Nat.le_zero.mp
      ((GalilLookRefined.needS_le_needL' w (stOf w) 0).trans (hpre w hw).need0.le))
    (fun w hw k => le_rfl)
    (fun w hw => (hpre w hw).tc0)
    (fun w hw => (hpre w hw).mono)
    (fun w hw => (hpre w hw).needLe)
    hbase hcost
    (fun w hw => used_of_report w hw (hrep w hw))
    habs hrep


theorem ledger_localL'_with (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ)
    (firstOf : List (Fin 2) → Fin 9) (stOf runOf : List (Fin 2) → ℕ → State GalilVM)
    (KOf TcOf : List (Fin 2) → ℕ → ℕ)
    (hpre : ∀ w : List (Fin 2), 0 < w.length →
      GalilLookRefined.PreloadL' w (stOf w) (TcOf w))
    (hs : ∀ w : List (Fin 2), 0 < w.length →
      Sched w (GalilLookRefined.needT' w (stOf w)) (fun k => needS w (stOf w) (k+1))
        (TcOf w w.length) (KOf w))
    (hbase : ∀ w : List (Fin 2), 0 < w.length → TcOf w 1 ≤ 2050)
    (hcost : ∀ (w : List (Fin 2)), 0 < w.length → ∀ m, 1 ≤ m → m < w.length →
      TcOf w (m+1) - TcOf w m ≤ alpha' 2048 * (Cw w (m+1) - Cw w m) + beta' 2048)
    (habs : ∀ (w : List (Fin 2)), 0 < w.length → ∀ s, KOf w s ≤ TcOf w w.length →
      runOf w s = truncS (w.length - arrL w s) (stOf w (KOf w s)))
    (hrep : ∀ w : List (Fin 2), 0 < w.length →
      GalilLedgerAssembly.ReportPointAt (Pof w) (qof w) (firstOf w) w w.length
        (stOf w (TcOf w w.length)))
    (R : List (Fin 2) → State GalilVM → Prop)
    (hR : ∀ w : List (Fin 2), 0 < w.length → R w (stOf w (TcOf w w.length))) :
    LedgerWith Pof qof firstOf runOf (fun w => w.length * nLocalL - 1) R :=
  ledger_local_with Pof qof firstOf stOf runOf
    (fun w => GalilLookRefined.needT' w (stOf w)) (fun w k => needS w (stOf w) (k+1))
    (fun w => needS w (stOf w))
    KOf TcOf hs
    (fun w hw => Nat.le_zero.mp
      ((GalilLookRefined.needS_le_needL' w (stOf w) 0).trans (hpre w hw).need0.le))
    (fun w hw k => le_rfl)
    (fun w hw => (hpre w hw).tc0)
    (fun w hw => (hpre w hw).mono)
    (fun w hw => (hpre w hw).needLe)
    hbase hcost
    (fun w hw => used_of_report w hw (hrep w hw))
    habs hrep R hR

/-! ## 6. `Sched` from the starvation oracle -/

section FromOracles

variable {X : Type}

open Classical in
/-- The pre-loaded index the local run stands for: the number of non-stuttering
micro-steps so far.  A micro-step ticks iff it is not an arrival slot and the
local core is not starved — exactly the disjunct
`LocalTrackingLatch.run_progress` turns into a `Tick`. -/
noncomputable def kOf (S : LocalSys X) (w : List (Fin 2)) (x0 : LX X) : ℕ → ℕ
  | 0 => 0
  | s+1 => if inp w s = none ∧ ¬ S.Starved (micro S w x0 s).core then
      kOf S w x0 s + 1 else kOf S w x0 s

open Classical in
theorem kOf_succ_tick (S : LocalSys X) (w : List (Fin 2)) (x0 : LX X) (s : ℕ)
    (h : inp w s = none ∧ ¬ S.Starved (micro S w x0 s).core) :
    kOf S w x0 (s+1) = kOf S w x0 s + 1 := by
  show (if inp w s = none ∧ ¬ S.Starved (micro S w x0 s).core then
    kOf S w x0 s + 1 else kOf S w x0 s) = _
  rw [if_pos h]

open Classical in
theorem kOf_succ_stutter (S : LocalSys X) (w : List (Fin 2)) (x0 : LX X) (s : ℕ)
    (h : ¬ (inp w s = none ∧ ¬ S.Starved (micro S w x0 s).core)) :
    kOf S w x0 (s+1) = kOf S w x0 s := by
  show (if inp w s = none ∧ ¬ S.Starved (micro S w x0 s).core then
    kOf S w x0 s + 1 else kOf S w x0 s) = _
  rw [if_neg h]

theorem kOf_step (S : LocalSys X) (w : List (Fin 2)) (x0 : LX X) (s : ℕ) :
    kOf S w x0 (s+1) = kOf S w x0 s + 1 ∨ kOf S w x0 (s+1) = kOf S w x0 s := by
  by_cases h : inp w s = none ∧ ¬ S.Starved (micro S w x0 s).core
  · exact Or.inl (kOf_succ_tick S w x0 s h)
  · exact Or.inr (kOf_succ_stutter S w x0 s h)

/-- **`Sched` from "stutter iff starved".**  `starved_need` is the direction the
local core owes: a core that is *not* starved really has the letters its next
pre-loaded tick needs; `need_not_starved` is its converse (the core ticks once
its need has arrived). -/
theorem sched_of_starved (S : LocalSys X) (w : List (Fin 2)) (x0 : LX X) (nd gd : ℕ → ℕ) (e : ℕ)
    (starved_need : ∀ s, kOf S w x0 s < e → ¬ S.Starved (micro S w x0 s).core →
      gd (kOf S w x0 s) ≤ arrL w s)
    (need_not_starved : ∀ s, kOf S w x0 s < e → nd (kOf S w x0 s) ≤ arrL w s →
      ¬ S.Starved (micro S w x0 s).core) :
    Sched w nd gd e (kOf S w x0) where
  k0 := rfl
  mono := fun s => by rcases kOf_step S w x0 s with h | h <;> omega
  step_le := fun s => by rcases kOf_step S w x0 s with h | h <;> omega
  progress := fun s hi hk hnd =>
    kOf_succ_tick S w x0 s ⟨hi, need_not_starved s hk hnd⟩
  guard := fun s hbefore hstep => by
    by_cases h : inp w s = none ∧ ¬ S.Starved (micro S w x0 s).core
    · exact starved_need s hbefore h.2
    · have := kOf_succ_stutter S w x0 s h; omega

/-- **Oracle 4 of `LocalTrackingLatch`, for the local run itself.**  Exactly the
`H_ledger` argument of `LocalTrackingLatch.pal_in_peg_of_local_latch`: the
ledger for `fun w => stAbs S absS w x0` at the shifted deadline `|w|·nLocalL`.

What is still assumed: the pre-loaded trace `stOf` with its `PreloadL'` data,
its checkpoint costs (`GalilTraceCost.checkpoints_cost`), its report point at
`TcOf w |w|`, the starvation oracle in both directions, and the tracking
equation `habs` (the local run's abstraction is the pre-loaded trace truncated
to the letters that have arrived). -/
theorem H_ledger_of_local_oracles (S : List (Fin 2) → LocalSys X) (absS : X → State GalilVM) (x0 : LX X)
    (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ) (firstOf : List (Fin 2) → Fin 9)
    (stOf : List (Fin 2) → ℕ → State GalilVM) (TcOf : List (Fin 2) → ℕ → ℕ)
    (hpre : ∀ w : List (Fin 2), 0 < w.length → GalilLookRefined.PreloadL' w (stOf w) (TcOf w))
    (starved_need : ∀ (w : List (Fin 2)), 0 < w.length → ∀ s,
      kOf (S w) w x0 s < TcOf w w.length → ¬ (S w).Starved (micro (S w) w x0 s).core →
        needS w (stOf w) (kOf (S w) w x0 s + 1) ≤ arrL w s)
    (need_not_starved : ∀ (w : List (Fin 2)), 0 < w.length → ∀ s,
      kOf (S w) w x0 s < TcOf w w.length →
        GalilLookRefined.needT' w (stOf w) (kOf (S w) w x0 s) ≤ arrL w s →
        ¬ (S w).Starved (micro (S w) w x0 s).core)
    (hbase : ∀ w : List (Fin 2), 0 < w.length → TcOf w 1 ≤ 2050)
    (hcost : ∀ (w : List (Fin 2)), 0 < w.length → ∀ m, 1 ≤ m → m < w.length →
      TcOf w (m+1) - TcOf w m ≤ alpha' 2048 * (Cw w (m+1) - Cw w m) + beta' 2048)
    (habs : ∀ (w : List (Fin 2)), 0 < w.length → ∀ s, kOf (S w) w x0 s ≤ TcOf w w.length →
      stAbs (S w) absS w x0 s = truncS (w.length - arrL w s) (stOf w (kOf (S w) w x0 s)))
    (hrep : ∀ w : List (Fin 2), 0 < w.length →
      GalilLedgerAssembly.ReportPointAt (Pof w) (qof w) (firstOf w) w w.length
        (stOf w (TcOf w w.length))) :
    LedgerObligation Pof qof firstOf (fun w => stAbs (S w) absS w x0)
      (fun w => w.length * nLocalL - 1) :=
  ledger_localL' Pof qof firstOf stOf (fun w => stAbs (S w) absS w x0) (fun w => kOf (S w) w x0) TcOf
    hpre
    (fun w hw => sched_of_starved (S w) w x0 (GalilLookRefined.needT' w (stOf w))
      (fun k => needS w (stOf w) (k+1)) (TcOf w w.length)
      (starved_need w hw) (need_not_starved w hw))
    hbase hcost habs hrep


theorem H_ledger_of_local_oracles_with (S : List (Fin 2) → LocalSys X) (absS : X → State GalilVM) (x0 : LX X)
    (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ) (firstOf : List (Fin 2) → Fin 9)
    (stOf : List (Fin 2) → ℕ → State GalilVM) (TcOf : List (Fin 2) → ℕ → ℕ)
    (hpre : ∀ w : List (Fin 2), 0 < w.length → GalilLookRefined.PreloadL' w (stOf w) (TcOf w))
    (starved_need : ∀ (w : List (Fin 2)), 0 < w.length → ∀ s,
      kOf (S w) w x0 s < TcOf w w.length → ¬ (S w).Starved (micro (S w) w x0 s).core →
        needS w (stOf w) (kOf (S w) w x0 s + 1) ≤ arrL w s)
    (need_not_starved : ∀ (w : List (Fin 2)), 0 < w.length → ∀ s,
      kOf (S w) w x0 s < TcOf w w.length →
        GalilLookRefined.needT' w (stOf w) (kOf (S w) w x0 s) ≤ arrL w s →
        ¬ (S w).Starved (micro (S w) w x0 s).core)
    (hbase : ∀ w : List (Fin 2), 0 < w.length → TcOf w 1 ≤ 2050)
    (hcost : ∀ (w : List (Fin 2)), 0 < w.length → ∀ m, 1 ≤ m → m < w.length →
      TcOf w (m+1) - TcOf w m ≤ alpha' 2048 * (Cw w (m+1) - Cw w m) + beta' 2048)
    (habs : ∀ (w : List (Fin 2)), 0 < w.length → ∀ s, kOf (S w) w x0 s ≤ TcOf w w.length →
      stAbs (S w) absS w x0 s = truncS (w.length - arrL w s) (stOf w (kOf (S w) w x0 s)))
    (hrep : ∀ w : List (Fin 2), 0 < w.length →
      GalilLedgerAssembly.ReportPointAt (Pof w) (qof w) (firstOf w) w w.length
        (stOf w (TcOf w w.length)))
    (R : List (Fin 2) → State GalilVM → Prop)
    (hR : ∀ w : List (Fin 2), 0 < w.length → R w (stOf w (TcOf w w.length))) :
    LedgerWith Pof qof firstOf (fun w => stAbs (S w) absS w x0)
      (fun w => w.length * nLocalL - 1) R :=
  ledger_localL'_with Pof qof firstOf stOf (fun w => stAbs (S w) absS w x0) (fun w => kOf (S w) w x0) TcOf
    hpre
    (fun w hw => sched_of_starved (S w) w x0 (GalilLookRefined.needT' w (stOf w))
      (fun k => needS w (stOf w) (k+1)) (TcOf w w.length)
      (starved_need w hw) (need_not_starved w hw))
    hbase hcost habs hrep R hR

end FromOracles

#print axioms arrL_mono
#print axioms arrL_ge
#print axioms cnt_step_arrival
#print axioms used_le_arr
#print axioms windowL
#print axioms ostepL
#print axioms TA_exact
#print axioms TA_exists
#print axioms TA_zero
#print axioms O_step_local
#print axioms reported_local
#print axioms ledger_local
#print axioms ledger_localL'
#print axioms sched_of_starved
#print axioms H_ledger_of_local_oracles

end PalPeg.LocalLedgerShift
