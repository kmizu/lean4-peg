import PalPeg.GalilThrottledRun
import PalPeg.GalilLedgerThrottled

/-!
# The throttled run, generic in the arrival spacing `τ`

`GalilThrottledRun` spaces arrivals `GalilLedgerAssembly.τ = 2^17` indices apart.
Here the schedule (`stepCfgG`, `cfgG`), its invariants, the O-step and the ledger
are re-proved for any spacing `τ ≥ 2`, and instantiated at
`GalilLedgerThrottled.ticksPerSymbol = 2^18`, so the run's arrival spacing and the
Lindley deadline slope coincide.
-/

set_option autoImplicit false

namespace PalPeg.GalilThrottledRunGen

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilTickArrive PalPeg.GalilLatchTracking PalPeg.GalilArriveChain
open PalPeg.GalilThrottledRun PalPeg.GalilLedgerQ64

/-! ## 1. The τ-generic schedule -/

def stepCfgG (τ n e : ℕ) (nd : ℕ → ℕ) (t : ℕ) (c : Cfg) : Cfg :=
  if c.j < n ∧ c.j * τ ≤ t then ⟨c.k, c.j + 1⟩
  else if c.k < e ∧ nd c.k ≤ c.j then ⟨c.k + 1, c.j⟩ else c

def cfgG (τ n e : ℕ) (nd : ℕ → ℕ) : ℕ → Cfg
  | 0 => ⟨0, 0⟩
  | t+1 => stepCfgG τ n e nd t (cfgG τ n e nd t)

theorem cfgG_succ_cases (τ n e : ℕ) (nd : ℕ → ℕ) (t : ℕ) :
    ((cfgG τ n e nd t).j < n ∧ (cfgG τ n e nd t).j * τ ≤ t ∧
        cfgG τ n e nd (t+1) = ⟨(cfgG τ n e nd t).k, (cfgG τ n e nd t).j + 1⟩) ∨
      (¬ ((cfgG τ n e nd t).j < n ∧ (cfgG τ n e nd t).j * τ ≤ t) ∧
        (cfgG τ n e nd t).k < e ∧ nd (cfgG τ n e nd t).k ≤ (cfgG τ n e nd t).j ∧
        cfgG τ n e nd (t+1) = ⟨(cfgG τ n e nd t).k + 1, (cfgG τ n e nd t).j⟩) ∨
      (¬ ((cfgG τ n e nd t).j < n ∧ (cfgG τ n e nd t).j * τ ≤ t) ∧
        ¬ ((cfgG τ n e nd t).k < e ∧ nd (cfgG τ n e nd t).k ≤ (cfgG τ n e nd t).j) ∧
        cfgG τ n e nd (t+1) = cfgG τ n e nd t) := by
  show _ ∨ _ ∨ _
  have hd : cfgG τ n e nd (t+1) = stepCfgG τ n e nd t (cfgG τ n e nd t) := rfl
  rw [hd]
  unfold stepCfgG
  by_cases h1 : (cfgG τ n e nd t).j < n ∧ (cfgG τ n e nd t).j * τ ≤ t
  · exact Or.inl ⟨h1.1, h1.2, if_pos h1⟩
  · by_cases h2 : (cfgG τ n e nd t).k < e ∧ nd (cfgG τ n e nd t).k ≤ (cfgG τ n e nd t).j
    · exact Or.inr (Or.inl ⟨h1, h2.1, h2.2, by rw [if_neg h1, if_pos h2]⟩)
    · exact Or.inr (Or.inr ⟨h1, h2, by rw [if_neg h1, if_neg h2]⟩)

/-- Arithmetic invariants of the schedule: arrivals happen exactly on time. -/
theorem cfgG_inv (τ : ℕ) (hτ : 2 ≤ τ) (n e : ℕ) (nd : ℕ → ℕ) : ∀ t,
    (cfgG τ n e nd t).j ≤ n ∧ (cfgG τ n e nd t).k ≤ e ∧
    ((cfgG τ n e nd t).j < n → t ≤ (cfgG τ n e nd t).j * τ) ∧
    (0 < (cfgG τ n e nd t).j → ((cfgG τ n e nd t).j - 1) * τ < t) := by
  intro t
  induction t with
  | zero => simp [cfgG]
  | succ t ih =>
    obtain ⟨i1, i2, i3, i4⟩ := ih
    rcases cfgG_succ_cases τ n e nd t with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
    · rw [h3]; simp only
      have hs : ((cfgG τ n e nd t).j + 1) * τ = (cfgG τ n e nd t).j * τ + τ := Nat.succ_mul _ _
      have hp : (cfgG τ n e nd t).j + 1 - 1 = (cfgG τ n e nd t).j := by omega
      rw [hs, hp]
      have := i3 h1
      omega
    · rw [h4]; simp only
      refine ⟨i1, by omega, fun h => ?_, fun h => by have := i4 h; omega⟩
      have := i3 h
      by_contra hc
      exact h1 ⟨h, by omega⟩
    · rw [h3]
      refine ⟨i1, i2, fun h => ?_, fun h => by have := i4 h; omega⟩
      by_contra hc
      exact h1 ⟨h, by omega⟩

theorem cfgG_used (τ n e : ℕ) (nd f : ℕ → ℕ) (hf0 : f 0 = 0)
    (hnd : ∀ k i, i ≤ k+1 → f i ≤ nd k) :
    ∀ t i, i ≤ (cfgG τ n e nd t).k → f i ≤ (cfgG τ n e nd t).j := by
  intro t
  induction t with
  | zero =>
    intro i hi
    have : i = 0 := by simpa [cfgG] using hi
    subst this
    simp [cfgG, hf0]
  | succ t ih =>
    intro i hi
    rcases cfgG_succ_cases τ n e nd t with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
    · rw [h3] at hi ⊢; exact le_trans (ih i hi) (Nat.le_succ _)
    · rw [h4] at hi ⊢; exact le_trans (hnd _ i hi) h3
    · rw [h3] at hi ⊢; exact ih i hi

theorem cfgG_mono (τ n e : ℕ) (nd : ℕ → ℕ) (t : ℕ) :
    (cfgG τ n e nd t).k ≤ (cfgG τ n e nd (t+1)).k ∧
      (cfgG τ n e nd (t+1)).k ≤ (cfgG τ n e nd t).k + 1 ∧
      (cfgG τ n e nd t).j ≤ (cfgG τ n e nd (t+1)).j := by
  rcases cfgG_succ_cases τ n e nd t with ⟨_, _, h3⟩ | ⟨_, _, _, h4⟩ | ⟨_, _, h3⟩
  · rw [h3]; simp
  · rw [h4]; simp
  · rw [h3]; simp

theorem cfgG_mono_le (τ n e : ℕ) (nd : ℕ → ℕ) {t t' : ℕ} (h : t ≤ t') :
    (cfgG τ n e nd t).k ≤ (cfgG τ n e nd t').k ∧ (cfgG τ n e nd t).j ≤ (cfgG τ n e nd t').j := by
  induction t' with
  | zero => have : t = 0 := by omega
            subst this; exact ⟨le_rfl, le_rfl⟩
  | succ t' ih =>
    by_cases ht : t ≤ t'
    · obtain ⟨a, b⟩ := ih ht
      obtain ⟨c, -, d⟩ := cfgG_mono τ n e nd t'
      exact ⟨le_trans a c, le_trans b d⟩
    · have : t = t' + 1 := by omega
      subst this; exact ⟨le_rfl, le_rfl⟩

/-- No stutter inside a window where the pending ticks' needs have arrived. -/
theorem windowG (τ n e : ℕ) (nd : ℕ → ℕ) (B J t0 : ℕ) (hB : B ≤ e)
    (hnd : ∀ k, k < B → nd k ≤ J) (hJ : J ≤ (cfgG τ n e nd t0).j) :
    ∀ L, (cfgG τ n e nd (t0+L)).k < B →
      (cfgG τ n e nd (t0+L)).k + (cfgG τ n e nd (t0+L)).j =
        (cfgG τ n e nd t0).k + (cfgG τ n e nd t0).j + L := by
  intro L
  induction L with
  | zero => intro _; rfl
  | succ L ih =>
    intro hK
    have hm := cfgG_mono τ n e nd (t0+L)
    have hK' : (cfgG τ n e nd (t0+L)).k < B := by
      have : t0 + (L+1) = t0 + L + 1 := by omega
      rw [this] at hK; omega
    have e1 := ih hK'
    have hjj := (cfgG_mono_le τ n e nd (Nat.le_add_right t0 L)).2
    have heq : t0 + (L+1) = t0 + L + 1 := by omega
    rw [heq] at hK ⊢
    rcases cfgG_succ_cases τ n e nd (t0+L) with ⟨_, _, h3⟩ | ⟨_, _, _, h4⟩ | ⟨_, h2, _⟩
    · rw [h3]; simp only; omega
    · rw [h4]; simp only; omega
    · exact absurd ⟨by omega, le_trans (hnd _ hK') (le_trans hJ hjj)⟩ h2

/-- **The per-prefix throttled step** at spacing `τ ≥ 2`. -/
theorem ostepG (τ : ℕ) (hτ : 2 ≤ τ) (n e : ℕ) (nd Tc : ℕ → ℕ) (m : ℕ) (hm : m < n)
    (hTc : Tc m ≤ Tc (m+1))
    (hTe : Tc (m+1) ≤ e) (hnd : ∀ k, k < Tc (m+1) → nd k ≤ m+1) (t1 : ℕ)
    (hK1 : Tc m ≤ (cfgG τ n e nd t1).k) :
    Tc (m+1) ≤ (cfgG τ n e nd (max t1 ((m+1) * τ) +
      (2 * (Tc (m+1) - Tc m) + 1))).k := by
  generalize ht0 : max t1 ((m+1) * τ) = t0
  have ha : t1 ≤ t0 := ht0 ▸ le_max_left _ _
  have hb : (m+1) * τ ≤ t0 := ht0 ▸ le_max_right _ _
  generalize hL : 2 * (Tc (m+1) - Tc m) + 1 = L
  by_contra hlt
  have hlt' : (cfgG τ n e nd (t0+L)).k < Tc (m+1) := by omega
  obtain ⟨i1, -, i3, -⟩ := cfgG_inv τ hτ n e nd t0
  obtain ⟨j1, -, -, j4⟩ := cfgG_inv τ hτ n e nd (t0+L)
  have hj0 : m+1 ≤ (cfgG τ n e nd t0).j := by
    by_cases h : (cfgG τ n e nd t0).j < n
    · have h3 := i3 h
      by_contra hc
      have hle : (cfgG τ n e nd t0).j * τ ≤ m * τ := Nat.mul_le_mul_right _ (by omega)
      have hs : (m+1) * τ = m * τ + τ := Nat.succ_mul _ _
      omega
    · omega
  have hw := windowG τ n e nd (Tc (m+1)) (m+1) t0 hTe hnd hj0 L hlt'
  have hk0 := (cfgG_mono_le τ n e nd ha).1
  have hjm := (cfgG_mono_le τ n e nd (Nat.le_add_right t0 L)).2
  -- set j := cfg t0 .j, j' := cfg (t0+L) .j; from hw, j' = j + (L - (k' - k0))
  generalize hjdef : (cfgG τ n e nd t0).j = j at *
  generalize hj'def : (cfgG τ n e nd (t0+L)).j = j' at *
  by_cases h : j < n
  · have h3 := i3 h
    have hp : 0 < j' := by omega
    have h4 := j4 hp
    -- `k' + j' = k0 + j + L`, `Tc m ≤ k0 ≤ k' < Tc (m+1)`, so `j' - j ≥ Δ + 2` and `L ≤ 2(j'-j) - 3`;
    -- but `(j'-1)·τ < t0 + L ≤ j·τ + L` forces `2(j'-j-1) < L`.
    have hjj : j + (Tc (m+1) - Tc m) + 2 ≤ j' := by omega
    have hmul : (j' - 1) * τ = j * τ + (j' - j - 1) * τ := by
      have e : j' - 1 = j + (j' - j - 1) := by omega
      rw [e, Nat.add_mul]
    have hmul2 : (j' - j - 1) * 2 ≤ (j' - j - 1) * τ := Nat.mul_le_mul_left _ hτ
    omega
  · omega

/-! ## 2. The τ-generic throttled run -/

variable (τ : ℕ) (raw : List (Fin 2)) (st : ℕ → State GalilVM) (e : ℕ)

abbrev cfgTG (t : ℕ) : Cfg := cfgG τ raw.length e (need raw st) t

def stTG (t : ℕ) : State GalilVM :=
  truncS (raw.length - (cfgTG τ raw st e t).j) (st (cfgTG τ raw st e t).k)

def arrTG (t : ℕ) : ℕ := (cfgTG τ raw st e t).j

/-- **`AbstractRun'` for the τ-throttled run.** -/
theorem abstractRun_throttledG (hτ : 2 ≤ τ) (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (hctl : (st 0).ctl = GalilScaffoldController.initial delay)
    (h0 : needS raw st 0 = 0)
    (hsuf : ∀ k, k ≤ e → SufVM raw (st k).vm)
    (htt : TruncTick raw st e (galilFrameS P q first) delay) :
    AbstractRun' P q first delay raw (stTG τ raw st e) (arrTG τ raw st e) := by
  refine ⟨hctl, rfl, fun t => ?_⟩
  have hused := cfgG_used τ raw.length e (need raw st) (needS raw st) h0
    (fun k i hi => needS_le_need raw st hi) t
  obtain ⟨-, hke, -, -⟩ := cfgG_inv τ hτ raw.length e (need raw st) t
  rcases cfgG_succ_cases τ raw.length e (need raw st) t with
    ⟨h1, _, h3⟩ | ⟨_, h2, h3, h4⟩ | ⟨_, _, h3⟩
  · refine Or.inr ⟨by simp only [arrTG, cfgTG, h3], raw[(cfgTG τ raw st e t).j], ?_, ?_⟩
    · exact List.getElem?_eq_getElem h1
    · simp only [stTG, cfgTG, h3]
      exact (arrive_trunc raw _ h1 _ (hsuf _ hke) (hused _ le_rfl)).symm
  · refine Or.inl ⟨by simp only [arrTG, cfgTG, h4], Or.inl ?_⟩
    simp only [stTG, cfgTG, h4]
    obtain ⟨i1, -, -, -⟩ := cfgG_inv τ hτ raw.length e (need raw st) t
    exact htt _ h2 _ i1 (hused _ le_rfl) (le_trans (needS_le_need raw st le_rfl) h3)
  · refine Or.inl ⟨by simp only [arrTG, cfgTG, h3], Or.inr ?_⟩
    simp only [stTG, cfgTG, h3]

open Classical in
noncomputable def TcTG (Tc : ℕ → ℕ) (m : ℕ) : ℕ :=
  if h : ∃ t, Tc m ≤ (cfgTG τ raw st e t).k then Nat.find h else 0

theorem TcTG_spec (Tc : ℕ → ℕ) (m : ℕ) (h : ∃ t, Tc m ≤ (cfgTG τ raw st e t).k) :
    Tc m ≤ (cfgTG τ raw st e (TcTG τ raw st e Tc m)).k ∧
      ∀ t, Tc m ≤ (cfgTG τ raw st e t).k → TcTG τ raw st e Tc m ≤ t := by
  unfold TcTG
  rw [dif_pos h]
  exact ⟨Nat.find_spec h, fun t ht => Nat.find_min' h ht⟩

theorem TcTG_exact (Tc : ℕ → ℕ) (m : ℕ) (h : ∃ t, Tc m ≤ (cfgTG τ raw st e t).k) :
    (cfgTG τ raw st e (TcTG τ raw st e Tc m)).k = Tc m := by
  obtain ⟨h1, h2⟩ := TcTG_spec τ raw st e Tc m h
  refine le_antisymm ?_ h1
  rcases hT : TcTG τ raw st e Tc m with _ | t'
  · simp [cfgTG, cfgG]
  · have hlt : ¬ Tc m ≤ (cfgTG τ raw st e t').k := fun hc => by
      have := h2 t' hc; omega
    have := (cfgG_mono τ raw.length e (need raw st) t').2.1
    simp only [cfgTG] at hlt this ⊢
    omega

theorem TcTG_exists (hτ : 2 ≤ τ) {Tc : ℕ → ℕ} (hp : Preload raw st Tc) :
    ∀ m, m ≤ raw.length → ∃ t, Tc m ≤ (cfgG τ raw.length (Tc raw.length) (need raw st) t).k := by
  intro m
  induction m with
  | zero => intro _; exact ⟨0, by rw [hp.tc0]; exact Nat.zero_le _⟩
  | succ m ih =>
    intro hm
    obtain ⟨hK, -⟩ := TcTG_spec τ raw st (Tc raw.length) Tc m (ih (by omega))
    exact ⟨_, ostepG τ hτ raw.length _ (need raw st) Tc m hm (hp.mono m hm)
      (preload_le_end raw st hp hm) (hp.needLe m hm) _ hK⟩

theorem TcTG_zero (hτ : 2 ≤ τ) {Tc : ℕ → ℕ} (hp : Preload raw st Tc) :
    TcTG τ raw st (Tc raw.length) Tc 0 = 0 := by
  have h := TcTG_exists τ raw st hτ hp 0 (Nat.zero_le _)
  have := (TcTG_spec τ raw st _ Tc 0 h).2 0 (by rw [hp.tc0]; exact Nat.zero_le _)
  omega

/-- **O-step for the τ-throttled checkpoint times.** -/
theorem O_step_throttledG (hτ : 2 ≤ τ) {Tc : ℕ → ℕ} (hp : Preload raw st Tc) (m : ℕ)
    (hm : m < raw.length) :
    TcTG τ raw st (Tc raw.length) Tc (m+1) ≤
      max (TcTG τ raw st (Tc raw.length) Tc m) ((m+1) * τ) + dwT Tc (m+1) := by
  obtain ⟨hK, -⟩ := TcTG_spec τ raw st (Tc raw.length) Tc m (TcTG_exists τ raw st hτ hp m hm.le)
  have ho := ostepG τ hτ raw.length _ (need raw st) Tc m hm (hp.mono m hm)
    (preload_le_end raw st hp hm) (hp.needLe m hm) _ hK
  have := (TcTG_spec τ raw st (Tc raw.length) Tc (m+1)
    (TcTG_exists τ raw st hτ hp (m+1) hm)).2 _ ho
  simpa [dwT] using this

/-- **Report point transport** for the τ-throttled run. -/
theorem stTG_at_end (hτ : 2 ≤ τ) {Tc : ℕ → ℕ} (hp : Preload raw st Tc) (hn : 0 < raw.length)
    {P : Shared} {q : ℕ} {first : Fin 9}
    (hrep : GalilLedgerAssembly.ReportPointAt P q first raw raw.length (st (Tc raw.length))) :
    stTG τ raw st (Tc raw.length) (TcTG τ raw st (Tc raw.length) Tc raw.length) =
      st (Tc raw.length) := by
  have hex := TcTG_exists τ raw st hτ hp raw.length le_rfl
  have hk := TcTG_exact τ raw st (Tc raw.length) Tc raw.length hex
  have hused := cfgG_used τ raw.length (Tc raw.length) (need raw st) (needS raw st) hp.need0
    (fun k i hi => needS_le_need raw st hi) (TcTG τ raw st (Tc raw.length) Tc raw.length)
    (Tc raw.length) (by simp only [cfgTG] at hk; omega)
  have hu := used_of_report raw hn hrep
  obtain ⟨i1, -, -, -⟩ := cfgG_inv τ hτ raw.length (Tc raw.length) (need raw st)
    (TcTG τ raw st (Tc raw.length) Tc raw.length)
  have hjn : (cfgTG τ raw st (Tc raw.length)
      (TcTG τ raw st (Tc raw.length) Tc raw.length)).j = raw.length := by
    simp only [cfgTG, needS] at hused i1 ⊢
    omega
  unfold stTG
  rw [hjn, hk, Nat.sub_self, truncS_zero]

/-! ## 3. The ledger, τ-generic and at `2^18` -/

/-- Ledger obligation for τ-throttled runs, any cost `dwT ≤ α·ΔC + β`, `2(α+β) ≤ τ`. -/
theorem ledger_throttledG (hτ2 : 2 ≤ τ) (α β : ℕ) (hτ : 2 * (α + β) ≤ τ)
    (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ)
    (firstOf : List (Fin 2) → Fin 9) (stOf : List (Fin 2) → ℕ → State GalilVM)
    (TcOf : List (Fin 2) → ℕ → ℕ)
    (hpre : ∀ w : List (Fin 2), 0 < w.length → Preload w (stOf w) (TcOf w))
    (hrep : ∀ w : List (Fin 2), 0 < w.length →
      GalilLedgerAssembly.ReportPointAt (Pof w) (qof w) (firstOf w) w w.length
        (stOf w (TcOf w w.length)))
    (O_cost : ∀ w : List (Fin 2), 0 < w.length → ∀ m, m < w.length →
      dwT (TcOf w) (m+1) ≤ α * (Cw w (m+1) - Cw w m) + β) :
    LedgerObligation Pof qof firstOf
      (fun w => stTG τ w (stOf w) (TcOf w w.length))
      (fun w => (w.length + 1) * τ) := by
  intro w hw hpal
  have hp := hpre w hw
  have hz := GalilLedgerThrottled.backlog_zero_trunc' α β τ hτ w hw hpal (dwT (TcOf w))
    (O_cost w hw)
  have ht := GalilLedgerThrottled.on_time_trunc' α β τ hτ w (dwT (TcOf w))
    (TcTG τ w (stOf w) (TcOf w w.length) (TcOf w)) (TcTG_zero τ w (stOf w) hτ2 hp)
    (O_step_throttledG τ w (stOf w) hτ2 hp) hz
  obtain ⟨hrp, hfr⟩ := GalilLedgerAssembly.reportPoint_of_at_length hw (hrep w hw)
  refine ⟨TcTG τ w (stOf w) (TcOf w w.length) (TcOf w) w.length, ht, ?_, ?_⟩
  · show ReportPoint w (stTG τ w (stOf w) (TcOf w w.length) _)
    rw [stTG_at_end τ w (stOf w) hτ2 hp hw (hrep w hw)]; exact hrp
  · show Refreshed _ _ _ (stTG τ w (stOf w) (TcOf w w.length) _)
    rw [stTG_at_end τ w (stOf w) hτ2 hp hw (hrep w hw)]; exact hfr

theorem two_le_ticksPerSymbol : 2 ≤ GalilLedgerThrottled.ticksPerSymbol := by
  unfold GalilLedgerThrottled.ticksPerSymbol; norm_num

/-- **`AbstractRun'` for the run with arrivals `2^18` apart.** -/
theorem abstractRun_throttled_2p18 (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (hctl : (st 0).ctl = GalilScaffoldController.initial delay)
    (h0 : needS raw st 0 = 0)
    (hsuf : ∀ k, k ≤ e → SufVM raw (st k).vm)
    (htt : TruncTick raw st e (galilFrameS P q first) delay) :
    AbstractRun' P q first delay raw (stTG GalilLedgerThrottled.ticksPerSymbol raw st e)
      (arrTG GalilLedgerThrottled.ticksPerSymbol raw st e) :=
  abstractRun_throttledG _ raw st e two_le_ticksPerSymbol P q first delay hctl h0 hsuf htt

/-- **Ledger obligation, run spacing = deadline slope = `2^18`.** -/
theorem ledger_throttled_2p18 (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ)
    (firstOf : List (Fin 2) → Fin 9) (stOf : List (Fin 2) → ℕ → State GalilVM)
    (TcOf : List (Fin 2) → ℕ → ℕ)
    (hpre : ∀ w : List (Fin 2), 0 < w.length → Preload w (stOf w) (TcOf w))
    (hrep : ∀ w : List (Fin 2), 0 < w.length →
      GalilLedgerAssembly.ReportPointAt (Pof w) (qof w) (firstOf w) w w.length
        (stOf w (TcOf w w.length)))
    (O_base : ∀ w : List (Fin 2), 0 < w.length → TcOf w 1 ≤ 2050)
    (O_cost : ∀ w : List (Fin 2), 0 < w.length → ∀ m, 1 ≤ m → m < w.length →
      TcOf w (m+1) - TcOf w m ≤ alpha' 2048 * (Cw w (m+1) - Cw w m) + beta' 2048) :
    LedgerObligation Pof qof firstOf
      (fun w => stTG GalilLedgerThrottled.ticksPerSymbol w (stOf w) (TcOf w w.length))
      (fun w => (w.length + 1) * GalilLedgerThrottled.ticksPerSymbol) := by
  have hτ : 2 * (2 * alpha' 2048 + (2 * beta' 2048 + 1)) ≤ GalilLedgerThrottled.ticksPerSymbol := by
    have := GalilLedgerThrottled.two_c2_le_τ'
    unfold GalilLedgerThrottled.c2 at this
    exact this.trans_eq' (by ring)
  exact ledger_throttledG _ two_le_ticksPerSymbol _ _ hτ Pof qof firstOf stOf TcOf hpre hrep
    (fun w hw m hm => GalilLedgerThrottled.dwT_cost w (TcOf w) (hpre w hw).tc0 (O_base w hw)
      (O_cost w hw) m hm)

#print axioms cfgG_inv
#print axioms cfgG_used
#print axioms windowG
#print axioms ostepG
#print axioms abstractRun_throttledG
#print axioms TcTG_exact
#print axioms TcTG_exists
#print axioms O_step_throttledG
#print axioms stTG_at_end
#print axioms ledger_throttledG
#print axioms abstractRun_throttled_2p18
#print axioms ledger_throttled_2p18

end PalPeg.GalilThrottledRunGen
