import PalPeg.GalilLedgerAssembly
import PalPeg.GalilTraceCost
import PalPeg.GalilLindley
import PalPeg.GalilLedgerCentres

/-!
# Ledger assembly with a base case at `m = 0`

`GalilTraceCost.checkpoints_cost` bounds `Tc (m+1) - Tc m` only for `1 ≤ m`.
The first interval (init tick + first scan segment) is covered by an explicit
constant `B0 ≤ beta' 2048` (`O_base : Tc w 1 ≤ B0`): at `m = 0` we take the
step cost `Tc w 1` itself, for which (O-step) is trivial and (O-cost) follows
from `B0 ≤ beta' 2048`.
-/

set_option autoImplicit false
namespace PalPeg.GalilLedgerAssembly2

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilStructuredSkeleton
  PalPeg.GalilLatchTracking PalPeg.GalilLedgerQ64 PalPeg.Predictability PalPeg.Lindley
  PalPeg.GalilLedgerAssembly

/-- Variant of `ledgerObligation_of_oracles`: (O-step)/(O-cost) only for `1 ≤ m`,
plus a base bound `Tc w 1 ≤ B0` with `B0 ≤ beta' 2048`. -/
theorem ledgerObligation_of_oracles' (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ)
    (firstOf : List (Fin 2) → Fin 9) (stOf : List (Fin 2) → ℕ → State GalilVM)
    (Tc dw : List (Fin 2) → ℕ → ℕ) (B0 : ℕ) (hB0 : B0 ≤ beta' 2048)
    (O_check : ∀ w : List (Fin 2), 0 < w.length →
      Tc w 0 = 0 ∧ ∀ m, 1 ≤ m → m ≤ w.length →
        ReportPointAt (Pof w) (qof w) (firstOf w) w m (stOf w (Tc w m)))
    (O_base : ∀ w : List (Fin 2), 0 < w.length → Tc w 1 ≤ B0)
    (O_step : ∀ w : List (Fin 2), 0 < w.length → ∀ m, 1 ≤ m → m < w.length →
      Tc w (m+1) ≤ max (Tc w m) ((m+1)*τ) + dw w (m+1))
    (O_cost : ∀ w : List (Fin 2), 0 < w.length → ∀ m, 1 ≤ m → m < w.length →
      dw w (m+1) ≤ alpha' 2048 * (Cw w (m+1) - Cw w m) + beta' 2048) :
    LedgerObligation Pof qof firstOf stOf (fun w => (w.length + 1) * τ) := by
  let dw' : List (Fin 2) → ℕ → ℕ := fun w m => if m = 1 then Tc w 1 else dw w m
  refine ledgerObligation_of_oracles Pof qof firstOf stOf Tc dw' O_check ?_ ?_
  · intro w hw m hm
    by_cases h0 : m = 0
    · subst h0
      simp [dw']
    · have e : m + 1 ≠ 1 := by omega
      simp only [dw', e, if_false]
      exact O_step w hw m (by omega) hm
  · intro w hw m hm
    by_cases h0 : m = 0
    · subst h0
      simp only [dw', if_true]
      exact le_trans (O_base w hw) (le_trans hB0 (Nat.le_add_left _ _))
    · have e : m + 1 ≠ 1 := by omega
      simp only [dw', e, if_false]
      exact O_cost w hw m (by omega) hm

/-- **From `checkpoints_cost`.** For each nonempty `w`, the conclusion of
`GalilTraceCost.checkpoints_cost` for `stOf w`, `Tc w` (with `raw = w`), plus the
base bound `Tc w 1 ≤ B0 ≤ beta' 2048`, gives the ledger obligation. (O-step)
holds with `dw := Tc (m+1) - Tc m` by monotonicity. -/
theorem ledgerObligation_of_checkpoints_cost (Pof : List (Fin 2) → Shared)
    (qof : List (Fin 2) → ℕ) (firstOf : List (Fin 2) → Fin 9)
    (stOf : List (Fin 2) → ℕ → State GalilVM) (Tc : List (Fin 2) → ℕ → ℕ)
    (B0 : ℕ) (hB0 : B0 ≤ beta' 2048)
    (hck : ∀ w : List (Fin 2), 0 < w.length →
      Tc w 0 = 0 ∧
      (∀ m m', m ≤ m' → m' ≤ w.length → Tc w m ≤ Tc w m') ∧
      (∀ m, 1 ≤ m → m ≤ w.length →
        ReportPointAt (Pof w) (qof w) (firstOf w) w m (stOf w (Tc w m))) ∧
      (∀ m, 1 ≤ m → m < w.length →
        Tc w (m+1) - Tc w m ≤ alpha' 2048 * (Cw w (m+1) - Cw w m) + beta' 2048))
    (O_base : ∀ w : List (Fin 2), 0 < w.length → Tc w 1 ≤ B0) :
    LedgerObligation Pof qof firstOf stOf (fun w => (w.length + 1) * τ) := by
  refine ledgerObligation_of_oracles' Pof qof firstOf stOf Tc
    (fun w m => Tc w m - Tc w (m-1)) B0 hB0
    (fun w hw => ⟨(hck w hw).1, (hck w hw).2.2.1⟩) O_base ?_ ?_
  · intro w hw m _ hm
    have hmono := (hck w hw).2.1 m (m+1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel]
    have := le_max_left (Tc w m) ((m+1)*τ)
    omega
  · intro w hw m h1 hm
    simpa using (hck w hw).2.2.2 m h1 hm

/-- Existential form: per-word checkpoint data (as produced by
`checkpoints_cost`) with the base bound yields some run family meeting the
ledger obligation. -/
theorem exists_ledgerObligation_of_checkpoints_cost (Pof : List (Fin 2) → Shared)
    (qof : List (Fin 2) → ℕ) (firstOf : List (Fin 2) → Fin 9)
    (B0 : ℕ) (hB0 : B0 ≤ beta' 2048)
    (hck : ∀ w : List (Fin 2), ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ), 0 < w.length →
      Tc 0 = 0 ∧
      (∀ m m', m ≤ m' → m' ≤ w.length → Tc m ≤ Tc m') ∧
      (∀ m, 1 ≤ m → m ≤ w.length →
        ReportPointAt (Pof w) (qof w) (firstOf w) w m (st (Tc m))) ∧
      (∀ m, 1 ≤ m → m < w.length →
        Tc (m+1) - Tc m ≤ alpha' 2048 * (Cw w (m+1) - Cw w m) + beta' 2048) ∧
      Tc 1 ≤ B0) :
    ∃ stOf : List (Fin 2) → ℕ → State GalilVM,
      LedgerObligation Pof qof firstOf stOf (fun w => (w.length + 1) * τ) := by
  choose stOf Tc h using hck
  exact ⟨stOf, ledgerObligation_of_checkpoints_cost Pof qof firstOf stOf Tc B0 hB0
    (fun w hw => let H := h w hw; ⟨H.1, H.2.1, H.2.2.1, H.2.2.2.1⟩)
    (fun w hw => (h w hw).2.2.2.2)⟩

theorem base_2050 : 2050 ≤ beta' 2048 := by rw [beta'_2048]; omega

#print axioms ledgerObligation_of_oracles'
#print axioms ledgerObligation_of_checkpoints_cost
#print axioms exists_ledgerObligation_of_checkpoints_cost
#print axioms base_2050

end PalPeg.GalilLedgerAssembly2
