import PalPeg.GalilLedgerObligations

/-!
# The `q = 64`, `M = 2048` specialisation of the ledger

`GalilLedger.stage_meets_barrier` is stated for every quantum `q ≥ 1`, which
forces `K ≥ 400` and `M ≥ 24K = 9600` — inconsistent with the calibrated
`delay = M = 2048`.  Here `q = 64` is fixed and the true constant is used:

* `stageCost_le_factor_q64` : `stageCost 64 r m ≤ 10·ell` (`K = 10` is minimal:
  at `r ≤ 1`, `m = 9` the cost is `78 > 9·8`).
* `stage_meets_barrier_q64` / `stage_deadline_q64` with `M = 2048 ≥ 24·10`.
* The interval constants `alphaCoef 64 2048 = 16462`, `betaCoef 64 2048 = 8212`,
  `serviceRate 64 2048 = 24674`, and `2·24674 + 1 ≤ 2^17`.

`alphaCoef` only charges the *paper* fallback ledger `40 + ⌈8·296/q⌉` per unit
of centre advance, whereas the machine-side `GalilLedger2.fallback_cost_move`
counts `12704·δ + 4012` ticks for copy → home → FPP → markEnd → choose →
rewind.  `alpha'`/`beta'` are the constants that absorb that real tick count
(plus a chain shift `δ+1`), and `ledger_slots'` checks that the two
new-place slots of an interval fit `alpha'·δ + beta'`; the constant still
fits the `2^17` budget at `M = 2048`.
-/

set_option autoImplicit false

namespace PalPeg.GalilLedgerQ64

open PalPeg.GalilLedger

/-- **Obligation 1, uniform factor at `q = 64`.**  `K = 10`. -/
theorem stageCost_le_factor_q64 (r m ell : ℕ) (hell : ell = 8 * max r 1)
    (hm : m ≤ ell + 1) : stageCost 64 r m ≤ 10 * ell := by
  have ha : 1 ≤ max r 1 := le_max_right _ _
  have hr : r ≤ max r 1 := le_max_left _ _
  unfold stageCost
  omega

/-- `K = 9` fails (so `10` is the minimal factor): `r = 1`, `m = 9`. -/
theorem stageCost_q64_not_le_nine : ¬ stageCost 64 1 9 ≤ 9 * (8 * max 1 1) := by
  decide

/-- **Obligation 1, the barrier at `q = 64`.**  Needs only `M ≥ 24·10 = 240`. -/
theorem stage_meets_barrier_q64' (M r m ell rad : ℕ) (hr : 1 ≤ r)
    (hell : ell = 8*r) (hm : m ≤ ell + 1) (hM : 24*10 ≤ M)
    (hentry : 3*rad ≤ 5*r) : stageCost 64 r m ≤ M * (2*r - rad) := by
  have hbase : stageCost 64 r m ≤ 80 * r := by
    have := stageCost_le_factor_q64 r m ell (by rw [hell, max_eq_left hr]) hm
    omega
  have hslack : r ≤ 3 * (2*r - rad) := by omega
  have hrate : 240 * (2*r - rad) ≤ M * (2*r - rad) := Nat.mul_le_mul_right _ (by omega)
  omega

/-- **Obligation 1, the barrier at `q = 64`, `M = 2048`.** -/
theorem stage_meets_barrier_q64 (r m ell rad : ℕ) (hr : 1 ≤ r)
    (hell : ell = 8*r) (hm : m ≤ ell + 1) (hentry : 3*rad ≤ 5*r) :
    stageCost 64 r m ≤ 2048 * (2*r - rad) :=
  stage_meets_barrier_q64' 2048 r m ell rad hr hell hm (by norm_num) hentry

/-- **Obligation 1 as used, at `q = 64`, `K = 10`, `M = 2048`.** -/
theorem stage_deadline_q64 (r m ell rad cost : ℕ) (hr : 1 ≤ r)
    (hell : ell = 8*r) (hm : m ≤ ell + 1) (hentry : 3*rad ≤ 5*r)
    (hcost : cost ≤ stageCost 64 r m) :
    cost ≤ 10 * ell ∧ cost ≤ 2048 * (2*r - rad) :=
  ⟨le_trans hcost (stageCost_le_factor_q64 r m ell (by rw [hell, max_eq_left hr]) hm),
   le_trans hcost (stage_meets_barrier_q64 r m ell rad hr hell hm hentry)⟩

/-! ## The interval constants at `q = 64`, `M = 2048` -/

theorem alphaCoef_q64 : alphaCoef 64 2048 = 16462 := by decide
theorem betaCoef_q64 : betaCoef 64 2048 = 8212 := by decide
theorem serviceRate_q64_eq : serviceRate 64 2048 = 24674 := by decide

theorem serviceRate_q64 : 2 * serviceRate 64 2048 + 1 ≤ 2^17 := by
  rw [serviceRate_q64_eq]; norm_num

/-! ## Constants absorbing the machine-side fallback tick count -/

/-- A chain shift advancing the centre by `δ` takes `δ + 1`; its `δ` part is
absorbed by `alpha'`, its constant part (two slots) is `shiftCost`. -/
def shiftCost : ℕ := 2

/-- Replay `8M` plus the real fallback coefficient `12704`
(`GalilLedger2.fallback_cost_move`). -/
def alpha' (M : ℕ) : ℕ := 8*M + 12704

/-- Two new-place comparisons `4M`, two fallback constants `2·4012`, two
dispatch units, and the chain-shift constants. -/
def beta' (M : ℕ) : ℕ := 4*M + 2*4012 + 2 + shiftCost

theorem alpha'_2048 : alpha' 2048 = 29088 := by decide
theorem beta'_2048 : beta' 2048 = 16220 := by decide

theorem service'_2048 : 2 * (alpha' 2048 + beta' 2048) + 1 ≤ 2^17 := by
  rw [alpha'_2048, beta'_2048]; norm_num

/-- One new-place slot: either a move (replay `≤ 8M·δ`, fallback
`≤ 12704·δ + 4012`) or a chain shift (`≤ δ + 1`). -/
def SlotOK (M δ cost : ℕ) : Prop :=
  (∃ rep fb, cost = rep + fb ∧ rep ≤ 8*M*δ ∧ fb ≤ 12704*δ + 4012) ∨ cost ≤ δ + 1

/-- **The corrected interval ledger.**  Two slots with advances `δ₁, δ₂`,
comparisons `≤ 4M`, dispatch `≤ 2`: the interval costs at most
`alpha'·(δ₁+δ₂) + beta'`. -/
theorem ledger_slots' (M δ₁ δ₂ s₁ s₂ compare dispatch : ℕ)
    (h₁ : SlotOK M δ₁ s₁) (h₂ : SlotOK M δ₂ s₂)
    (hcompare : compare ≤ 4*M) (hdispatch : dispatch ≤ 2) :
    s₁ + s₂ + compare + dispatch ≤ alpha' M * (δ₁ + δ₂) + beta' M := by
  have slot : ∀ δ s, SlotOK M δ s → s ≤ (8*M + 12704)*δ + 4012 + 1 := by
    intro δ s h
    have e : (8*M + 12704)*δ = 8*M*δ + 12704*δ := by ring
    rcases h with ⟨rep, fb, hs, hr, hf⟩ | h
    · omega
    · have : δ ≤ 12704*δ := by omega
      omega
  have a := slot δ₁ s₁ h₁
  have b := slot δ₂ s₂ h₂
  have e : alpha' M * (δ₁ + δ₂) = (8*M + 12704)*δ₁ + (8*M + 12704)*δ₂ := by
    unfold alpha'; ring
  unfold beta' shiftCost
  omega

#print axioms stageCost_le_factor_q64
#print axioms stageCost_q64_not_le_nine
#print axioms stage_meets_barrier_q64'
#print axioms stage_meets_barrier_q64
#print axioms stage_deadline_q64
#print axioms alphaCoef_q64
#print axioms betaCoef_q64
#print axioms serviceRate_q64_eq
#print axioms serviceRate_q64
#print axioms alpha'_2048
#print axioms beta'_2048
#print axioms service'_2048
#print axioms ledger_slots'

end PalPeg.GalilLedgerQ64
