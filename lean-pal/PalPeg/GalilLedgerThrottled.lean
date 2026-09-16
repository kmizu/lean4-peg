import PalPeg.GalilThrottledRun
import PalPeg.GalilLedgerAssembly
import PalPeg.GalilLedgerAssembly2
import PalPeg.GalilTraceCost
import PalPeg.GalilLedgerQ64
import PalPeg.GalilLindley
import PalPeg.GalilLatchTracking

/-!
# The throttled ledger at deadline slope `2^18`

`GalilThrottledRun.O_step_throttled` charges `dwT Tc k = 2·(Tc k − Tc (k−1)) + 1`
per interval. With `GalilTraceCost.checkpoints_cost`
(`Tc (m+1) − Tc m ≤ α'·ΔC + β'` for `1 ≤ m`) and the base bound `Tc 1 ≤ 2050`
this is `≤ 2α'·ΔC + (2β'+1)`, i.e. service constant
`c2 = 2α' + 2β' + 1 = 90617`, and `2·c2 = 181234 ≤ 2^18`.

`GalilLedgerAssembly.τ = 2^17` is left untouched; the backlog / Lindley steps
are re-proved generically in `(α β τ)` with `2(α+β) ≤ τ`, and the throttled
O-step (stated with `2^17`) is weakened to `2^18` by monotonicity of `max`.

**Caveat (for the local machine).** The throttled *schedule*
(`GalilThrottledRun.stepCfg`) still spaces arrivals `2^17` apart; only the
Lindley deadline uses slope `2^18`. A local machine taking
`ticksPerSymbol = 2^18` ticks per letter spaces arrivals `2^18` apart, so the
schedule's spacing must be made `2^18` as well (or τ-generic) before the two
match. `LocalTracking.nLocal = 2·delayS = 4096` must become `2^18 = 64·4096`.
-/

set_option autoImplicit false
namespace PalPeg.GalilLedgerThrottled

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilStructuredSkeleton
  PalPeg.GalilLatchTracking PalPeg.GalilLedgerQ64 PalPeg.Predictability PalPeg.Lindley
  PalPeg.GalilThrottledRun

/-! ## 1. Constants -/

/-- Ticks per input symbol (deadline slope). -/
def ticksPerSymbol : ℕ := 2^18

/-- Deadline slope of the throttled ledger. -/
abbrev τ' : ℕ := ticksPerSymbol

/-- Service constant of the throttled work `dwT`. -/
def c2 : ℕ := 2 * alpha' 2048 + 2 * beta' 2048 + 1

theorem c2_eq : c2 = 90617 := by unfold c2; rw [alpha'_2048, beta'_2048]

theorem two_c2_le_τ' : 2 * c2 ≤ τ' := by
  rw [c2_eq]; unfold τ' ticksPerSymbol; norm_num

theorem ticksPerSymbol_eq : ticksPerSymbol = 64 * (2 * 2048) := by
  unfold ticksPerSymbol; norm_num

/-! ## 2. τ-generic backlog and Lindley -/

theorem cost_int' (α β d C0 C1 : ℕ) (hle : C0 ≤ C1) (h : d ≤ α * (C1 - C0) + β) :
    (d : ℤ) ≤ ((α + β : ℕ) : ℤ) * ((C1 : ℤ) - C0 + 1) := by
  have hδ : ((C1 - C0 : ℕ) : ℤ) = (C1 : ℤ) - C0 := by push_cast [hle]; ring
  have h' : (d : ℤ) ≤ (α : ℤ) * ((C1 - C0 : ℕ) : ℤ) + β := by exact_mod_cast h
  rw [hδ] at h'
  have hnn : (0 : ℤ) ≤ (C1 : ℤ) - C0 := by
    have : (C0 : ℤ) ≤ C1 := by exact_mod_cast hle
    linarith
  have ha : (0 : ℤ) ≤ α := by positivity
  have hb : (0 : ℤ) ≤ β := by positivity
  push_cast
  nlinarith

/-- Backlog zero at `|w|` with service constant `α+β`. -/
theorem backlog_zero_trunc' (α β τ : ℕ) (_hτ : 2 * (α + β) ≤ τ)
    (w : List (Fin 2)) (hw : 0 < w.length) (hpal : w ∈ PAL) (dw : ℕ → ℕ)
    (hcost : ∀ m, m < w.length → dw (m+1) ≤ α * (Cw w (m+1) - Cw w m) + β) :
    backlog (fun m => if m ≤ w.length then dw m else 0) (α + β) w.length = 0 := by
  refine realtime_of_predictable _ (Cw w) (α + β) (cw_mono w) (cw_ge w) ?_ (cw_pal hw hpal)
  intro m
  by_cases hm : m < w.length
  · have e : (m+1 ≤ w.length) := hm
    simp only [e, if_true]
    exact_mod_cast cost_int' α β _ _ _ (cw_mono w m) (hcost m hm)
  · have e : ¬ (m+1 ≤ w.length) := by omega
    simp only [e, if_false, Nat.cast_zero]
    have hle : (Cw w m : ℤ) ≤ Cw w (m+1) := by exact_mod_cast cw_mono w m
    have : (0 : ℤ) ≤ ((α + β : ℕ) : ℤ) := by positivity
    push_cast at this ⊢
    nlinarith

/-- Lindley at `|w|` with spacing `τ` and service constant `α+β`. -/
theorem on_time_trunc' (α β τ : ℕ) (hτ : 2 * (α + β) ≤ τ)
    (w : List (Fin 2)) (dw Tc : ℕ → ℕ) (h0 : Tc 0 = 0)
    (hstep : ∀ m, m < w.length → Tc (m+1) ≤ max (Tc m) ((m+1)*τ) + dw (m+1))
    (hz : backlog (fun m => if m ≤ w.length then dw m else 0) (α + β) w.length = 0) :
    Tc w.length ≤ (w.length + 1) * τ := by
  have key := run_on_time (fun m => if m ≤ w.length then dw m else 0) (α + β) τ hτ
    (fun m => Tc (min m w.length)) (by simp [h0]) ?_ w.length hz
  · simpa using key
  · intro m
    by_cases hm : m < w.length
    · have e1 : min (m+1) w.length = m+1 := by omega
      have e2 : min m w.length = m := by omega
      have e3 : m+1 ≤ w.length := hm
      simp only [e1, e2, e3, if_true]
      exact hstep m hm
    · have e1 : min (m+1) w.length = w.length := by omega
      have e2 : min m w.length = w.length := by omega
      simp only [e1, e2]
      exact le_trans (le_max_left _ _) (Nat.le_add_right _ _)

/-! ## 3. The throttled work bound -/

/-- `dwT` from `checkpoints_cost` (for `1 ≤ m`) and the base bound (for `m = 0`). -/
theorem dwT_cost (w : List (Fin 2)) (Tc : ℕ → ℕ) (h0 : Tc 0 = 0) (hbase : Tc 1 ≤ 2050)
    (hck : ∀ m, 1 ≤ m → m < w.length →
      Tc (m+1) - Tc m ≤ alpha' 2048 * (Cw w (m+1) - Cw w m) + beta' 2048)
    (m : ℕ) (hm : m < w.length) :
    dwT Tc (m+1) ≤
      (2 * alpha' 2048) * (Cw w (m+1) - Cw w m) + (2 * beta' 2048 + 1) := by
  unfold dwT
  simp only [Nat.add_sub_cancel]
  by_cases h : m = 0
  · subst h
    simp only [Nat.zero_add] at *
    rw [h0, beta'_2048]
    omega
  · have := hck m (by omega) hm
    have e : 2 * alpha' 2048 * (Cw w (m+1) - Cw w m) =
        2 * (alpha' 2048 * (Cw w (m+1) - Cw w m)) := by ring
    omega

/-- The throttled O-step weakened from spacing `2^17` to `2^18`. -/
theorem O_step_throttled' (raw : List (Fin 2)) (st : ℕ → State GalilVM) {Tc : ℕ → ℕ}
    (hp : Preload raw st Tc) (m : ℕ) (hm : m < raw.length) :
    TcT raw st (Tc raw.length) Tc (m+1) ≤
      max (TcT raw st (Tc raw.length) Tc m) ((m+1) * τ') + dwT Tc (m+1) := by
  have h := O_step_throttled raw st hp m hm
  have hτ : (m+1) * GalilLedgerAssembly.τ ≤ (m+1) * τ' := by
    apply Nat.mul_le_mul_left
    rw [τ_eq]; unfold τ' ticksPerSymbol; norm_num
  have := max_le_max (le_refl (TcT raw st (Tc raw.length) Tc m)) hτ
  omega

/-! ## 4. The ledger obligation at slope `2^18` -/

/-- Generic form: any cost bound `dwT ≤ α·ΔC + β` with `2(α+β) ≤ 2^18`. -/
theorem ledger_throttled_gen (α β : ℕ) (hτ : 2 * (α + β) ≤ τ')
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
      (fun w => stT w (stOf w) (TcOf w w.length))
      (fun w => (w.length + 1) * τ') := by
  intro w hw hpal
  have hp := hpre w hw
  have hz := backlog_zero_trunc' α β τ' hτ w hw hpal (dwT (TcOf w)) (O_cost w hw)
  have ht := on_time_trunc' α β τ' hτ w (dwT (TcOf w))
    (TcT w (stOf w) (TcOf w w.length) (TcOf w)) (TcT_zero w (stOf w) hp)
    (O_step_throttled' w (stOf w) hp) hz
  obtain ⟨hrp, hfr⟩ := GalilLedgerAssembly.reportPoint_of_at_length hw (hrep w hw)
  refine ⟨TcT w (stOf w) (TcOf w w.length) (TcOf w) w.length, ht, ?_, ?_⟩
  · show ReportPoint w (stT w (stOf w) (TcOf w w.length) _)
    rw [stT_at_end w (stOf w) hp hw (hrep w hw)]; exact hrp
  · show Refreshed _ _ _ (stT w (stOf w) (TcOf w w.length) _)
    rw [stT_at_end w (stOf w) hp hw (hrep w hw)]; exact hfr

/-- **Ledger obligation for the throttled runs, deadline `(|w|+1)·2^18`.**
Costs in `checkpoints_cost` form (`1 ≤ m`) plus the base bound `Tc 1 ≤ 2050`. -/
theorem ledger_throttled' (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ)
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
      (fun w => stT w (stOf w) (TcOf w w.length))
      (fun w => (w.length + 1) * ticksPerSymbol) := by
  have hτ : 2 * (2 * alpha' 2048 + (2 * beta' 2048 + 1)) ≤ τ' := by
    have := two_c2_le_τ'; unfold c2 at this; omega
  exact ledger_throttled_gen _ _ hτ Pof qof firstOf stOf TcOf hpre hrep
    (fun w hw m hm => dwT_cost w (TcOf w) (hpre w hw).tc0 (O_base w hw) (O_cost w hw) m hm)

/-- **What the local machine must realize.** The deadline of `ledger_throttled'`
is `|w|·ticksPerSymbol + ticksPerSymbol`, i.e. one extra symbol's worth of ticks
after `|w|` letters at `ticksPerSymbol = 2^18 = 64·nLocal_old` local steps per
letter (`LocalTracking.nLocal` must become `2^18`). -/
theorem deadline_local (w : List (Fin 2)) :
    (w.length + 1) * ticksPerSymbol = w.length * ticksPerSymbol + ticksPerSymbol ∧
      ticksPerSymbol = 2^18 :=
  ⟨Nat.succ_mul _ _, rfl⟩

#print axioms c2_eq
#print axioms two_c2_le_τ'
#print axioms ticksPerSymbol_eq
#print axioms cost_int'
#print axioms backlog_zero_trunc'
#print axioms on_time_trunc'
#print axioms dwT_cost
#print axioms O_step_throttled'
#print axioms ledger_throttled_gen
#print axioms ledger_throttled'
#print axioms deadline_local

end PalPeg.GalilLedgerThrottled
