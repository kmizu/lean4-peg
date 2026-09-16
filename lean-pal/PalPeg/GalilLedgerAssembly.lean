import PalPeg.GalilLatchTracking
import PalPeg.GalilLindley
import PalPeg.GalilLedgerCentres
import PalPeg.GalilLedgerQ64
import PalPeg.GalilLedgerObligations2
import PalPeg.GalilPredictability

/-!
# Top-down assembly of `LedgerObligation` from three oracles

Constants: arrival spacing `τ = 2^17`, service constant
`c = alpha' 2048 + beta' 2048` (so `2c ≤ τ` by `service'_2048`).

For each nonempty `w`, over the run `stOf w`:
* (O-check) checkpoint times `Tc w` with `Tc w 0 = 0` and, for `1 ≤ m ≤ |w|`,
  a refreshed report point for the prefix `m` at `stOf w (Tc w m)`;
* (O-step)  `Tc w (m+1) ≤ max (Tc w m) ((m+1)·τ) + dw w (m+1)` for `m < |w|`;
* (O-cost)  `dw w (m+1) ≤ alpha'·(Cw w (m+1) − Cw w m) + beta'` for `m < |w|`.

Then on palindromes the FIFO backlog at `|w|` is zero
(`realtime_of_predictable` with `Cw`), the Lindley bound gives
`Tc w |w| ≤ (|w|+1)·τ`, and the report point at `m = |w|` witnesses
`Reported` by the deadline `(|w|+1)·τ`.
-/

set_option autoImplicit false
namespace PalPeg.GalilLedgerAssembly

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilStructuredSkeleton
  PalPeg.GalilLatchTracking PalPeg.GalilLedgerQ64 PalPeg.Predictability PalPeg.Lindley

/-- Arrival spacing. -/
def τ : ℕ := 2^17

/-- Service constant. -/
def cSvc : ℕ := alpha' 2048 + beta' 2048

theorem two_c_le_τ : 2 * cSvc ≤ τ := by
  have := service'_2048
  unfold cSvc τ
  omega

/-- A refreshed report point for the prefix of length `m` of `w`
(not replaying, scan invariant, `MInv w`, right head at `2m-1`, refreshed). -/
structure ReportPointAt (P : Shared) (q : ℕ) (first : Fin 9) (w : List (Fin 2)) (m : ℕ)
    (st : State GalilVM) : Prop where
  notReplaying : st.ctl.replaying = false
  scanInv : ∃ r : ℕ, ScanInvariant w (position st.vm.center) r st.vm.left st.vm.right
  centre : MInv w st.ctl st.vm
  atPrefix : position st.vm.right = 2 * m - 1
  refreshed : Refreshed P q first st

theorem reportPoint_of_at_length {P : Shared} {q : ℕ} {first : Fin 9} {w : List (Fin 2)}
    {st : State GalilVM} (hw : 0 < w.length) (h : ReportPointAt P q first w w.length st) :
    ReportPoint w st ∧ Refreshed P q first st :=
  ⟨⟨h.notReplaying, h.scanInv, h.centre, h.atPrefix, hw⟩, h.refreshed⟩

/-- (O-cost) in the predictability form. -/
theorem cost_int (d C0 C1 : ℕ) (hle : C0 ≤ C1)
    (h : d ≤ alpha' 2048 * (C1 - C0) + beta' 2048) :
    (d : ℤ) ≤ (cSvc : ℤ) * ((C1 : ℤ) - C0 + 1) := by
  have hδ : ((C1 - C0 : ℕ) : ℤ) = (C1 : ℤ) - C0 := by push_cast [hle]; ring
  have h' : (d : ℤ) ≤ (alpha' 2048 : ℤ) * ((C1 - C0 : ℕ) : ℤ) + beta' 2048 := by exact_mod_cast h
  rw [hδ] at h'
  have hnn : (0 : ℤ) ≤ (C1 : ℤ) - C0 := by
    have : (C0 : ℤ) ≤ C1 := by exact_mod_cast hle
    linarith
  have ha : (0 : ℤ) ≤ alpha' 2048 := by positivity
  have hb : (0 : ℤ) ≤ beta' 2048 := by positivity
  unfold cSvc
  push_cast
  nlinarith

/-- Backlog zero at `|w|` for nonempty palindromes, from (O-cost) below `|w|`. -/
theorem backlog_zero_trunc (w : List (Fin 2)) (hw : 0 < w.length) (hpal : w ∈ PAL)
    (dw : ℕ → ℕ)
    (hcost : ∀ m, m < w.length →
      dw (m+1) ≤ alpha' 2048 * (Cw w (m+1) - Cw w m) + beta' 2048) :
    backlog (fun m => if m ≤ w.length then dw m else 0) cSvc w.length = 0 := by
  refine realtime_of_predictable _ (Cw w) cSvc (cw_mono w) (cw_ge w) ?_ (cw_pal hw hpal)
  intro m
  by_cases hm : m < w.length
  · have e : (m+1 ≤ w.length) := hm
    simp only [e, if_true]
    exact cost_int _ _ _ (cw_mono w m) (hcost m hm)
  · have e : ¬ (m+1 ≤ w.length) := by omega
    simp only [e, if_false, Nat.cast_zero]
    have hle : (Cw w m : ℤ) ≤ Cw w (m+1) := by exact_mod_cast cw_mono w m
    have : (0 : ℤ) ≤ cSvc := by positivity
    nlinarith

/-- Lindley at `|w|` from (O-step) below `|w|` and a zero backlog. -/
theorem on_time_trunc (w : List (Fin 2)) (dw Tc : ℕ → ℕ) (h0 : Tc 0 = 0)
    (hstep : ∀ m, m < w.length → Tc (m+1) ≤ max (Tc m) ((m+1)*τ) + dw (m+1))
    (hz : backlog (fun m => if m ≤ w.length then dw m else 0) cSvc w.length = 0) :
    Tc w.length ≤ (w.length + 1) * τ := by
  have key := run_on_time (fun m => if m ≤ w.length then dw m else 0) cSvc τ two_c_le_τ
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

/-- **Assembly.** The three oracles give the ledger obligation with deadline
`(|w|+1)·τ`. -/
theorem ledgerObligation_of_oracles (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ)
    (firstOf : List (Fin 2) → Fin 9) (stOf : List (Fin 2) → ℕ → State GalilVM)
    (Tc dw : List (Fin 2) → ℕ → ℕ)
    (O_check : ∀ w : List (Fin 2), 0 < w.length →
      Tc w 0 = 0 ∧ ∀ m, 1 ≤ m → m ≤ w.length →
        ReportPointAt (Pof w) (qof w) (firstOf w) w m (stOf w (Tc w m)))
    (O_step : ∀ w : List (Fin 2), 0 < w.length → ∀ m, m < w.length →
      Tc w (m+1) ≤ max (Tc w m) ((m+1)*τ) + dw w (m+1))
    (O_cost : ∀ w : List (Fin 2), 0 < w.length → ∀ m, m < w.length →
      dw w (m+1) ≤ alpha' 2048 * (Cw w (m+1) - Cw w m) + beta' 2048) :
    LedgerObligation Pof qof firstOf stOf (fun w => (w.length + 1) * τ) := by
  intro w hw hpal
  obtain ⟨h0, hchk⟩ := O_check w hw
  have hz := backlog_zero_trunc w hw hpal (dw w) (O_cost w hw)
  have ht := on_time_trunc w (dw w) (Tc w) h0 (O_step w hw) hz
  obtain ⟨hrp, hfr⟩ := reportPoint_of_at_length hw (hchk w.length hw le_rfl)
  exact ⟨Tc w w.length, ht, hrp, hfr⟩

#print axioms two_c_le_τ
#print axioms reportPoint_of_at_length
#print axioms cost_int
#print axioms backlog_zero_trunc
#print axioms on_time_trunc
#print axioms ledgerObligation_of_oracles

end PalPeg.GalilLedgerAssembly
