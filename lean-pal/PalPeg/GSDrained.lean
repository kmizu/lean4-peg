import PalPeg.GSVerifier
import Mathlib.Logic.Function.Iterate

set_option autoImplicit false

/-!
# The drained answer of the interleaved Galil–Seiferas matcher

`SCA_GS_MAPPING.md` §3 ("L lemma to add: the drained answer").

`PalPeg.GSVerifier` runs the verifier step `vStep` at a fixed rate of `gsRate k = k+1` steps
per round (`vOnlineRun`), and proves the lag argument that this rate is enough. A head program
behaves differently: within a tick it runs `vStep` **for as long as it is `Enabled`**, and it
spins only when it is *drained*. This file supplies the list-level facts that such a
head-level simulation needs.

## Definitions

* `orbit j` — the `j`-th iterate of `vStep` from `vInit = (⟨|u|, 0⟩, 0)`. The online run
  `vOnlineRun` and every drained state lie on this one orbit (`vOnlineRun_le_drained`).
* `vRunSteps n m z` — the number of steps that `vRunIn n m z` actually takes.
* `drained n` / `drainIdx n` — run `vStep` while `Enabled v n`, with fuel
  `drainFuel k n = (k+1)·n + 1`. This is `vRunIn` with enough fuel.
  `drainIdx n` is the first index `j` at which `orbit j` is not `Enabled v n`
  (`drainIdx_spec`, `drained_eq_orbit`).
* `matchEvent z` — `q = |v|` and `checked = |u|`. This is the head's `match` condition when it
  leaves `z` (site 21; `prefixOk ↔ checked = |u|` there).
* `drainedAnswer n` — the `vReportedIn` flag of round `n`, read along the drained segment from
  `drained (n-1)` to `drained n`.

## Main results

* **Drained shape** (`drained_pos_add_q`): for `|u| ≤ n` the drained state has
  `pos + q = n` and `q < |v|`. Hence `Φ + k·q = (k+1)·n` (`phi_drained`), so
  `Φ ≤ (k+1)·n` (`phi_drained_le`).
* **Monotone along the orbit** (`drainIdx_mono`, `drained_eq_iterate`,
  `vRunIn_drained_of_le`, `drained_succ`): `drained (n+1)` is reached from `drained n` by
  exactly `drainIdx (n+1) - drainIdx n` further `vStep`s. It is also what `vRunIn` at round
  `n+1` computes from `drained n` given any fuel at least that large.
* **Step bounds via `Φ = (k+1)·pos + q`** (`drainIdx_sub_add_phi_le`,
  `drainIdx_succ_sub_le`, `drainIdx_succ_sub_le_coarse`, `drainIdx_le`):
  `drainIdx n' - drainIdx n ≤ Φ(drained n') - Φ(drained n)`. Per tick this is
  `drainIdx (n+1) - drainIdx n + k·q_{n+1} ≤ (k+1) + k·q_n ≤ k·|v| + 1`, and in total
  `drainIdx n ≤ (k+1)·(n - |u|)`.
* **Where reports sit** (`report_index`, `report_round`): an orbit state with `q = |v|` lies in
  the tick segment of round `pos + |v|`, i.e. `drainIdx (pos+|v|-1) ≤ j < drainIdx (pos+|v|)`.
* **Answer** (`drainedAnswer_succ_iff`): the round-`n+1` drained answer holds iff some index
  `j` with `drainIdx n ≤ j < drainIdx (n+1)` has `matchEvent (orbit j)`.
  (`drainedAnswer_correct`): for `|x| ≤ n` it equals `decide (OccAt (u ++ v) T (n - |x|))`.
  (`drainedAnswer_eq_vAnswer`): it equals `vAnswer` at every `n`.

## Hypotheses

These are the ones `GSVerifier` uses: `KSimple v k p₁ r`, `0 < |v|`, `0 < k` (`3 ≤ k` where
`VInv` is needed), and L1 as the explicit hypothesis `hL1` (the two bounds `hL1a`/`hL1b` of
`vStep_inv`, bundled). L1 is used only through `VInv`: for the `u`-deadline in completeness,
and in `drainedAnswer_eq_vAnswer` through `vAnswer_correct`. The shape, monotonicity and step
bounds need no L1.
-/

namespace PalPeg.GSDrained

universe u
variable {α : Type u}

/-! ## Definitions -/

/-- The initial verifier state `(⟨|u|, 0⟩, 0)`, the same as `vOnlineRun … 0`. -/
def vInit (u : List α) : VState := (⟨u.length, 0⟩, 0)

/-- The head's `match` condition when it leaves `z`: `v` has fully matched (`q = |v|`) and the
prefix verifier has finished (`checked = |u|`). -/
def matchEvent (u v : List α) (z : VState) : Bool :=
  decide (z.1.q = v.length ∧ z.2 = u.length)

/-- Fuel that is always enough to drain round `n` from `vInit` (see `drainIdx_le`). -/
def drainFuel (k n : ℕ) : ℕ := (k + 1) * n + 1

/-- `Enabled` is monotone in the arrival bound. -/
theorem enabled_mono {v : List α} {n n' : ℕ} {st : ScanState}
    (h : Enabled v n st) (hn : n ≤ n') : Enabled v n' st := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (by omega)

section Defs

variable [DecidableEq α]

/-- The `vStep` orbit from `vInit`. -/
def orbit (u v : List α) (k p₁ r : ℕ) (T : List α) (j : ℕ) : VState :=
  (vStep u v k p₁ r T)^[j] (vInit u)

/-- The number of steps actually taken by `vRunIn n m z`. -/
def vRunSteps (u v : List α) (k p₁ r : ℕ) (T : List α) (n : ℕ) : ℕ → VState → ℕ
  | 0, _ => 0
  | m + 1, z =>
      if Enabled v n z.1 then vRunSteps u v k p₁ r T n m (vStep u v k p₁ r T z) + 1 else 0

/-- The drained state of round `n`: run `vStep` from `vInit` while `Enabled v n`. -/
def drained (u v : List α) (k p₁ r : ℕ) (T : List α) (n : ℕ) : VState :=
  vRunIn u v k p₁ r T n (drainFuel k n) (vInit u)

/-- The orbit index of the drained state of round `n`. -/
def drainIdx (u v : List α) (k p₁ r : ℕ) (T : List α) (n : ℕ) : ℕ :=
  vRunSteps u v k p₁ r T n (drainFuel k n) (vInit u)

/-- The answer of round `n`, read along the drained segment
`drained (n-1) → drained n`. -/
def drainedAnswer (u v : List α) (k p₁ r : ℕ) (T : List α) : ℕ → Bool
  | 0 => false
  | n + 1 => vReportedIn u v k p₁ r T (n + 1) (drainFuel k (n + 1)) (drained u v k p₁ r T n)

end Defs

/-! ## Arithmetic -/

theorem ceilDiv_le_self {q k : ℕ} (hk : 0 < k) : ceilDiv q k ≤ q := by
  have hb := (ceilDiv_bounds (q := q) hk).2
  by_contra hc
  have hlt : q < ceilDiv q k := Nat.lt_of_not_le hc
  have h1 : k * (q + 1) ≤ k * ceilDiv q k := Nat.mul_le_mul_left _ hlt
  have h2 : q ≤ k * q := Nat.le_mul_of_pos_left q hk
  have h3 : k * (q + 1) = k * q + k := by ring
  omega

/-- A shift never moves the right end `pos + q` past `pos + max 1 q`. -/
theorem shift_add_nextQ_le {k p₁ r q : ℕ} (hk : 0 < k) :
    gsShift k p₁ r q + gsNextQ k p₁ r q ≤ max 1 q := by
  unfold gsShift gsNextQ
  split_ifs with hc
  · have h1 : p₁ ≤ q := le_trans (Nat.le_mul_of_pos_left p₁ hk) hc.1
    have h2 : q ≤ max 1 q := le_max_right _ _
    omega
  · have h1 := ceilDiv_le_self (q := q) hk
    have h2 : max 1 (ceilDiv q k) ≤ max 1 q := max_le_max (le_refl 1) h1
    omega

/-- An `Enabled` state that `Fits` lies below the bound: `Φ ≤ (k+1)·n`. -/
theorem phi_le_of_enabled {v : List α} {k n : ℕ} {st : ScanState} (hv : 0 < v.length)
    (he : Enabled v n st) (hf : Fits n st) : Phi k st ≤ (k + 1) * n := by
  have h1 : st.pos + st.q ≤ n := by
    rcases he with h | h
    · exact hf (by omega)
    · omega
  have h2 : (k + 1) * (st.pos + st.q) ≤ (k + 1) * n := Nat.mul_le_mul_left _ h1
  have h3 : (k + 1) * (st.pos + st.q) = (k + 1) * st.pos + st.q + k * st.q := by ring
  show (k + 1) * st.pos + st.q ≤ (k + 1) * n
  omega

/-- One `Enabled` scan step keeps the right end `pos + q` within the bound `n`. -/
theorem scanStep_bounded [DecidableEq α] {v T : List α} {k p₁ r n : ℕ} (hk : 0 < k)
    (hv : 0 < v.length) {st : ScanState} (he : Enabled v n st) (hb : st.pos + st.q ≤ n) :
    (scanStep v k p₁ r T st).pos + (scanStep v k p₁ r T st).q ≤ n := by
  have hs := shift_add_nextQ_le (k := k) (p₁ := p₁) (r := r) (q := st.q) hk
  unfold scanStep
  split_ifs with h1 h2
  · dsimp only
    have hm : max 1 st.q = st.q := max_eq_right (by omega)
    omega
  · have hlt : st.pos + st.q < n := he.resolve_left h1
    dsimp only
    omega
  · have hlt : st.pos + st.q < n := he.resolve_left h1
    dsimp only
    have hm : max 1 st.q ≤ st.q + 1 := max_le (by omega) (by omega)
    omega

/-! ## Runs with fuel -/

section Run

variable [DecidableEq α] {u v T : List α} {k p₁ r : ℕ}

theorem vRunIn_eq_iterate (n : ℕ) : ∀ (m : ℕ) (z : VState),
    vRunIn u v k p₁ r T n m z = (vStep u v k p₁ r T)^[vRunSteps u v k p₁ r T n m z] z := by
  intro m
  induction m with
  | zero => intro z; rfl
  | succ m ih =>
    intro z
    simp only [vRunIn, vRunSteps]
    split_ifs with he
    · rw [ih]; rfl
    · rfl

theorem vRunSteps_le (n : ℕ) : ∀ (m : ℕ) (z : VState), vRunSteps u v k p₁ r T n m z ≤ m := by
  intro m
  induction m with
  | zero => intro z; simp [vRunSteps]
  | succ m ih =>
    intro z
    simp only [vRunSteps]
    split_ifs
    · have := ih (vStep u v k p₁ r T z); omega
    · omega

/-- Every step that `vRunIn` takes is `Enabled`. -/
theorem enabled_of_lt_vRunSteps (n : ℕ) : ∀ (m : ℕ) (z : VState) (i : ℕ),
    i < vRunSteps u v k p₁ r T n m z → Enabled v n ((vStep u v k p₁ r T)^[i] z).1 := by
  intro m
  induction m with
  | zero => intro z i hi; simp [vRunSteps] at hi
  | succ m ih =>
    intro z i hi
    simp only [vRunSteps] at hi
    split_ifs at hi with he
    · cases i with
      | zero => exact he
      | succ i => exact ih (vStep u v k p₁ r T z) i (by omega)
    · omega

/-- **First stop**: if the first non-`Enabled` iterate from `z` is the `j`-th one, then
`vRunIn` with any fuel `m ≥ j` takes exactly `j` steps and lands there. -/
theorem vRunIn_of_firstStop (n : ℕ) : ∀ (j : ℕ) (z : VState),
    (∀ i, i < j → Enabled v n ((vStep u v k p₁ r T)^[i] z).1) →
    ¬ Enabled v n ((vStep u v k p₁ r T)^[j] z).1 →
    ∀ m, j ≤ m → vRunSteps u v k p₁ r T n m z = j ∧
      vRunIn u v k p₁ r T n m z = (vStep u v k p₁ r T)^[j] z := by
  intro j
  induction j with
  | zero =>
    intro z _ hstop m _
    have hs : ¬ Enabled v n z.1 := hstop
    cases m with
    | zero => exact ⟨rfl, rfl⟩
    | succ m => exact ⟨by simp [vRunSteps, hs], by simp [vRunIn, hs]⟩
  | succ j ih =>
    intro z hen hstop m hm
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have he : Enabled v n z.1 := hen 0 (by omega)
    have h := ih (vStep u v k p₁ r T z) (fun i hi => hen (i + 1) (by omega)) hstop m (by omega)
    simp only [vRunSteps, vRunIn, if_pos he]
    exact ⟨by rw [h.1], h.2⟩

/-- Past the potential bound, `vRunIn` is drained: its end state is not `Enabled`. -/
theorem not_enabled_vRunIn (hk : 0 < k) (hp : 0 < p₁) (hv : 0 < v.length) (n : ℕ) :
    ∀ (m : ℕ) (z : VState), z.1.q ≤ v.length → Fits n z.1 →
      (k + 1) * n < Phi k z.1 + m → ¬ Enabled v n (vRunIn u v k p₁ r T n m z).1 := by
  intro m
  induction m with
  | zero =>
    intro z _ hf hlt
    show ¬ Enabled v n z.1
    intro he
    have := phi_le_of_enabled (k := k) hv he hf
    omega
  | succ m ih =>
    intro z hq hf hlt
    simp only [vRunIn]
    split_ifs with he
    · have hlt' := phi_step_lt (v := v) (T := T) (p₁ := p₁) (r := r) hk hp z.1
      refine ih (vStep u v k p₁ r T z) ?_ ?_ ?_
      · rw [vStep_fst]; exact scanStep_q_le hq
      · rw [vStep_fst]; exact scanStep_fits hk hv he hf
      · rw [vStep_fst]; omega
    · exact he

/-- `vReportedIn` sees exactly the states that `vRunIn` passes through, the end included. -/
theorem vReportedIn_iff (n : ℕ) : ∀ (m : ℕ) (z : VState),
    vReportedIn u v k p₁ r T n m z = true ↔
      ∃ i, i ≤ vRunSteps u v k p₁ r T n m z ∧
        vReportFlag u v n ((vStep u v k p₁ r T)^[i] z) = true := by
  intro m
  induction m with
  | zero =>
    intro z
    simp only [vReportedIn, vRunSteps]
    constructor
    · intro h; exact ⟨0, le_refl 0, h⟩
    · rintro ⟨i, hi, h⟩
      obtain rfl : i = 0 := by omega
      exact h
  | succ m ih =>
    intro z
    simp only [vReportedIn, vRunSteps, Bool.or_eq_true]
    by_cases he : Enabled v n z.1
    · rw [if_pos he, if_pos he, ih]
      constructor
      · rintro (h | ⟨i, hi, h⟩)
        · exact ⟨0, Nat.zero_le _, h⟩
        · exact ⟨i + 1, by omega, h⟩
      · rintro ⟨i, hi, h⟩
        cases i with
        | zero => exact Or.inl h
        | succ i => exact Or.inr ⟨i, by omega, h⟩
    · rw [if_neg he, if_neg he]
      constructor
      · rintro (h | h)
        · exact ⟨0, le_refl 0, h⟩
        · exact absurd h (by simp)
      · rintro ⟨i, hi, h⟩
        obtain rfl : i = 0 := by omega
        exact Or.inl h

/-- Along any iterate, `Φ` grows by at least the number of steps. -/
theorem phi_iterate (hk : 0 < k) (hp : 0 < p₁) :
    ∀ (i : ℕ) (z : VState), Phi k z.1 + i ≤ Phi k ((vStep u v k p₁ r T)^[i] z).1 := by
  intro i
  induction i with
  | zero => intro z; simp
  | succ i ih =>
    intro z
    have h1 := phi_step_lt (v := v) (T := T) (p₁ := p₁) (r := r) hk hp z.1
    have h2 := ih (vStep u v k p₁ r T z)
    rw [vStep_fst] at h2
    show Phi k z.1 + (i + 1) ≤ Phi k ((vStep u v k p₁ r T)^[i] (vStep u v k p₁ r T z)).1
    omega

/-- `pos` never decreases along an iterate. -/
theorem pos_le_iterate : ∀ (i : ℕ) (z : VState),
    z.1.pos ≤ ((vStep u v k p₁ r T)^[i] z).1.pos := by
  intro i
  induction i with
  | zero => intro z; exact le_refl _
  | succ i ih =>
    intro z
    have h1 := scanStep_pos_le v k p₁ r T z.1
    have h2 := ih (vStep u v k p₁ r T z)
    rw [vStep_fst] at h2
    exact le_trans h1 h2

end Run

/-! ## The orbit, and where the drained states sit on it -/

section Orbit

variable [DecidableEq α] {u v T : List α} {k p₁ r : ℕ}

theorem orbit_zero : orbit u v k p₁ r T 0 = vInit u := rfl

theorem orbit_succ (j : ℕ) :
    orbit u v k p₁ r T (j + 1) = vStep u v k p₁ r T (orbit u v k p₁ r T j) :=
  Function.iterate_succ_apply' _ _ _

theorem iterate_orbit (i j : ℕ) :
    (vStep u v k p₁ r T)^[i] (orbit u v k p₁ r T j) = orbit u v k p₁ r T (i + j) := by
  unfold orbit
  rw [Function.iterate_add_apply]

theorem drained_eq_orbit (n : ℕ) :
    drained u v k p₁ r T n = orbit u v k p₁ r T (drainIdx u v k p₁ r T n) :=
  vRunIn_eq_iterate n _ _

theorem enabled_of_lt_drainIdx {n i : ℕ} (hi : i < drainIdx u v k p₁ r T n) :
    Enabled v n (orbit u v k p₁ r T i).1 :=
  enabled_of_lt_vRunSteps n _ _ i hi

theorem not_enabled_drained (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length)
    (n : ℕ) : ¬ Enabled v n (drained u v k p₁ r T n).1 := by
  refine not_enabled_vRunIn hk hK.period_pos hv n _ _ (Nat.zero_le _)
    (fun h => absurd h (Nat.lt_irrefl 0)) ?_
  show (k + 1) * n < (k + 1) * u.length + 0 + ((k + 1) * n + 1)
  omega

/-- **`drainIdx n` is the first stop**: every earlier orbit state is `Enabled v n`, and
`orbit (drainIdx n)` is not. -/
theorem drainIdx_spec (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length) (n : ℕ) :
    (∀ i, i < drainIdx u v k p₁ r T n → Enabled v n (orbit u v k p₁ r T i).1) ∧
      ¬ Enabled v n (orbit u v k p₁ r T (drainIdx u v k p₁ r T n)).1 := by
  refine ⟨fun i hi => enabled_of_lt_drainIdx hi, ?_⟩
  rw [← drained_eq_orbit]
  exact not_enabled_drained hK hk hv n

theorem drainIdx_eq_zero_of_lt (hv : 0 < v.length) {n : ℕ} (h : n < u.length) :
    drainIdx u v k p₁ r T n = 0 := by
  have hne : ¬ Enabled v n (vInit u).1 := by
    rintro (h1 | h1)
    · change 0 = v.length at h1; omega
    · change u.length + 0 < n at h1; omega
  show vRunSteps u v k p₁ r T n ((k + 1) * n + 1) (vInit u) = 0
  simp only [vRunSteps, if_neg hne]

theorem orbit_scanInv (hK : KSimple v k p₁ r) :
    ∀ j, ScanInv v T (orbit u v k p₁ r T j).1 := by
  intro j
  induction j with
  | zero => exact ⟨matchLen_zero v T u.length, Nat.zero_le _⟩
  | succ j ih => rw [orbit_succ, vStep_fst]; exact scanStep_inv hK ih

theorem orbit_vInv (hK : KSimple v k p₁ r) (hk : 3 ≤ k)
    (hL1 : (k - 1) * u.length < (u ++ v).length ∧ (k - 2) * u.length < (k - 1) * p₁) :
    ∀ j, VInv u v T (orbit u v k p₁ r T j) := by
  intro j
  induction j with
  | zero => exact vOnlineRun_inv (u := u) (T := T) hK hk hL1.1 hL1.2 0
  | succ j ih =>
    rw [orbit_succ]
    exact vStep_inv hK hk hL1.1 hL1.2 (orbit_scanInv hK j) ih

theorem orbit_pos_mono {j j' : ℕ} (h : j ≤ j') :
    (orbit u v k p₁ r T j).1.pos ≤ (orbit u v k p₁ r T j').1.pos := by
  obtain ⟨i, rfl⟩ : ∃ i, j' = i + j := ⟨j' - j, by omega⟩
  rw [← iterate_orbit]
  exact pos_le_iterate i _

theorem orbit_pos_ge (j : ℕ) : u.length ≤ (orbit u v k p₁ r T j).1.pos :=
  orbit_pos_mono (Nat.zero_le j)

/-- Up to the drained index, every orbit state keeps its right end within `n`. -/
theorem orbit_bounded (hk : 0 < k) (hv : 0 < v.length) {n : ℕ} (hun : u.length ≤ n) :
    ∀ j, j ≤ drainIdx u v k p₁ r T n →
      (orbit u v k p₁ r T j).1.pos + (orbit u v k p₁ r T j).1.q ≤ n := by
  intro j
  induction j with
  | zero => intro _; show u.length + 0 ≤ n; omega
  | succ j ih =>
    intro hj
    rw [orbit_succ, vStep_fst]
    exact scanStep_bounded hk hv (enabled_of_lt_drainIdx (by omega)) (ih (by omega))

/-- **Drained shape**: `pos + q = n` and `q < |v|`. -/
theorem drained_pos_add_q (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length) {n : ℕ}
    (hun : u.length ≤ n) :
    (drained u v k p₁ r T n).1.pos + (drained u v k p₁ r T n).1.q = n ∧
      (drained u v k p₁ r T n).1.q < v.length := by
  have hb := orbit_bounded (T := T) (p₁ := p₁) (r := r) hk hv hun _
    (le_refl (drainIdx u v k p₁ r T n))
  have hst := not_enabled_drained (u := u) (T := T) hK hk hv n
  have hq := (orbit_scanInv (u := u) (T := T) hK (drainIdx u v k p₁ r T n)).2
  rw [drained_eq_orbit] at hst ⊢
  unfold Enabled at hst
  omega

/-- `Φ + k·q = (k+1)·n` at the drained state. -/
theorem phi_drained (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length) {n : ℕ}
    (hun : u.length ≤ n) :
    Phi k (drained u v k p₁ r T n).1 + k * (drained u v k p₁ r T n).1.q = (k + 1) * n := by
  obtain ⟨h1, -⟩ := drained_pos_add_q (T := T) hK hk hv hun
  have h2 : (k + 1) * ((drained u v k p₁ r T n).1.pos + (drained u v k p₁ r T n).1.q)
      = (k + 1) * n := by rw [h1]
  have h3 : (k + 1) * ((drained u v k p₁ r T n).1.pos + (drained u v k p₁ r T n).1.q)
      = Phi k (drained u v k p₁ r T n).1 + k * (drained u v k p₁ r T n).1.q := by
    unfold Phi; ring
  omega

theorem phi_drained_le (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length) {n : ℕ}
    (hun : u.length ≤ n) : Phi k (drained u v k p₁ r T n).1 ≤ (k + 1) * n := by
  have := phi_drained (T := T) hK hk hv hun
  omega

/-! ## Monotonicity: the drained states advance along the one orbit -/

theorem drainIdx_mono (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length) {n n' : ℕ}
    (hn : n ≤ n') : drainIdx u v k p₁ r T n ≤ drainIdx u v k p₁ r T n' := by
  by_contra hc
  have hlt : drainIdx u v k p₁ r T n' < drainIdx u v k p₁ r T n := Nat.lt_of_not_le hc
  have he := enabled_of_lt_drainIdx (u := u) (T := T) (p₁ := p₁) (r := r) hlt
  have hst := not_enabled_drained (u := u) (T := T) hK hk hv n'
  rw [drained_eq_orbit] at hst
  exact hst (enabled_mono he hn)

/-- `drained n'` is reached from `drained n` by `drainIdx n' - drainIdx n` more `vStep`s. -/
theorem drained_eq_iterate (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length)
    {n n' : ℕ} (hn : n ≤ n') :
    drained u v k p₁ r T n' =
      (vStep u v k p₁ r T)^[drainIdx u v k p₁ r T n' - drainIdx u v k p₁ r T n]
        (drained u v k p₁ r T n) := by
  have hle := drainIdx_mono (u := u) (T := T) hK hk hv hn
  rw [drained_eq_orbit n', drained_eq_orbit n, iterate_orbit, Nat.sub_add_cancel hle]

/-- Running round `n'` from `drained n` (`n ≤ n'`) with fuel at least
`drainIdx n' - drainIdx n` takes exactly that many steps and lands on `drained n'`. -/
theorem vRunIn_drained_of_le (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length)
    {n n' : ℕ} (hn : n ≤ n') (m : ℕ)
    (hm : drainIdx u v k p₁ r T n' - drainIdx u v k p₁ r T n ≤ m) :
    vRunSteps u v k p₁ r T n' m (drained u v k p₁ r T n)
        = drainIdx u v k p₁ r T n' - drainIdx u v k p₁ r T n ∧
      vRunIn u v k p₁ r T n' m (drained u v k p₁ r T n) = drained u v k p₁ r T n' := by
  have hle := drainIdx_mono (u := u) (T := T) hK hk hv hn
  have hen : ∀ i, i < drainIdx u v k p₁ r T n' - drainIdx u v k p₁ r T n →
      Enabled v n' ((vStep u v k p₁ r T)^[i] (drained u v k p₁ r T n)).1 := by
    intro i hi
    rw [drained_eq_orbit, iterate_orbit]
    exact enabled_of_lt_drainIdx (by omega)
  have hstop : ¬ Enabled v n' ((vStep u v k p₁ r T)^[drainIdx u v k p₁ r T n'
      - drainIdx u v k p₁ r T n] (drained u v k p₁ r T n)).1 := by
    rw [← drained_eq_iterate hK hk hv hn]
    exact not_enabled_drained hK hk hv n'
  have h := vRunIn_of_firstStop n' _ _ hen hstop m hm
  exact ⟨h.1, h.2.trans (drained_eq_iterate hK hk hv hn).symm⟩

/-- **One tick**: `drained (n+1)` is `vRunIn` of round `n+1` started at `drained n`. -/
theorem drained_succ (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length) (n : ℕ) :
    drained u v k p₁ r T (n + 1) =
      vRunIn u v k p₁ r T (n + 1) (drainFuel k (n + 1)) (drained u v k p₁ r T n) := by
  have hfuel : drainIdx u v k p₁ r T (n + 1) - drainIdx u v k p₁ r T n ≤ drainFuel k (n + 1) :=
    le_trans (Nat.sub_le _ _) (vRunSteps_le _ _ _)
  exact ((vRunIn_drained_of_le hK hk hv (Nat.le_add_right n 1) _ hfuel).2).symm

/-- The fixed-rate online run `vOnlineRun` lies on the same orbit. -/
theorem vOnlineRun_eq_orbit : ∀ n, ∃ j, vOnlineRun u v k p₁ r T n = orbit u v k p₁ r T j := by
  intro n
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    obtain ⟨j, hj⟩ := ih
    refine ⟨vRunSteps u v k p₁ r T (n + 1) (gsRate k) (orbit u v k p₁ r T j) + j, ?_⟩
    show vRunIn u v k p₁ r T (n + 1) (gsRate k) (vOnlineRun u v k p₁ r T n) = _
    rw [hj, vRunIn_eq_iterate, iterate_orbit]

/-- ... and at or behind the drained point of the same round. -/
theorem vOnlineRun_le_drained (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length) :
    ∀ n, ∃ j, j ≤ drainIdx u v k p₁ r T n ∧ vOnlineRun u v k p₁ r T n = orbit u v k p₁ r T j := by
  intro n
  induction n with
  | zero => exact ⟨0, Nat.zero_le _, rfl⟩
  | succ n ih =>
    obtain ⟨j, hjle, hj⟩ := ih
    have hmono := drainIdx_mono (u := u) (T := T) hK hk hv (Nat.le_add_right n 1)
    refine ⟨vRunSteps u v k p₁ r T (n + 1) (gsRate k) (orbit u v k p₁ r T j) + j, ?_, ?_⟩
    · by_contra hc
      have hlt := Nat.lt_of_not_le hc
      have he := enabled_of_lt_vRunSteps (u := u) (v := v) (k := k) (p₁ := p₁) (r := r) (T := T)
        (n + 1) (gsRate k)
        (orbit u v k p₁ r T j) (drainIdx u v k p₁ r T (n + 1) - j) (by omega)
      rw [iterate_orbit, Nat.sub_add_cancel (by omega), ← drained_eq_orbit] at he
      exact not_enabled_drained hK hk hv (n + 1) he
    · show vRunIn u v k p₁ r T (n + 1) (gsRate k) (vOnlineRun u v k p₁ r T n) = _
      rw [hj, vRunIn_eq_iterate, iterate_orbit]

/-! ## Step bounds through the potential `Φ = (k+1)·pos + q` -/

/-- From `vInit`, the drained index is at most the potential gained. -/
theorem drainIdx_add_phi_le (hK : KSimple v k p₁ r) (hk : 0 < k) (n : ℕ) :
    drainIdx u v k p₁ r T n + (k + 1) * u.length ≤ Phi k (drained u v k p₁ r T n).1 := by
  have h := phi_iterate (u := u) (v := v) (T := T) (r := r) hk hK.period_pos
    (drainIdx u v k p₁ r T n) (vInit u)
  have e : Phi k (vInit u).1 = (k + 1) * u.length := by
    show (k + 1) * u.length + 0 = (k + 1) * u.length
    omega
  rw [drained_eq_orbit]
  unfold orbit
  omega

/-- **Steps between drained states are paid by `Φ`**: for `n ≤ n'`,
`drainIdx n' - drainIdx n ≤ Φ(drained n') - Φ(drained n)`. -/
theorem drainIdx_sub_add_phi_le (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length)
    {n n' : ℕ} (hn : n ≤ n') :
    drainIdx u v k p₁ r T n' - drainIdx u v k p₁ r T n + Phi k (drained u v k p₁ r T n).1
      ≤ Phi k (drained u v k p₁ r T n').1 := by
  have h := phi_iterate (u := u) (v := v) (T := T) (r := r) hk hK.period_pos
    (drainIdx u v k p₁ r T n' - drainIdx u v k p₁ r T n) (drained u v k p₁ r T n)
  rw [← drained_eq_iterate hK hk hv hn] at h
  omega

/-- **Per-tick bound**: `drainIdx (n+1) - drainIdx n + k·q_{n+1} ≤ (k+1) + k·q_n`,
where `q_n` is the `q` of `drained n`. -/
theorem drainIdx_succ_sub_le (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length)
    {n : ℕ} (hun : u.length ≤ n) :
    drainIdx u v k p₁ r T (n + 1) - drainIdx u v k p₁ r T n
        + k * (drained u v k p₁ r T (n + 1)).1.q
      ≤ (k + 1) + k * (drained u v k p₁ r T n).1.q := by
  have h1 := drainIdx_sub_add_phi_le (u := u) (T := T) hK hk hv (Nat.le_add_right n 1)
  have h2 := phi_drained (T := T) hK hk hv hun
  have h3 := phi_drained (T := T) hK hk hv (show u.length ≤ n + 1 by omega)
  have e : (k + 1) * (n + 1) = (k + 1) * n + (k + 1) := by ring
  omega

/-- The per-tick bound in constant form: at most `k·|v| + 1` steps per tick. -/
theorem drainIdx_succ_sub_le_coarse (hK : KSimple v k p₁ r) (hk : 0 < k)
    (hv : 0 < v.length) {n : ℕ} (hun : u.length ≤ n) :
    drainIdx u v k p₁ r T (n + 1) - drainIdx u v k p₁ r T n ≤ k * v.length + 1 := by
  have h1 := drainIdx_succ_sub_le (T := T) hK hk hv hun
  have hq := (drained_pos_add_q (T := T) hK hk hv hun).2
  have h2 : k * ((drained u v k p₁ r T n).1.q + 1) ≤ k * v.length :=
    Nat.mul_le_mul_left _ hq
  have e : k * ((drained u v k p₁ r T n).1.q + 1) = k * (drained u v k p₁ r T n).1.q + k := by
    ring
  omega

/-- **Total bound**: `drainIdx n ≤ (k+1)·(n - |u|)`. -/
theorem drainIdx_le (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length) (n : ℕ) :
    drainIdx u v k p₁ r T n ≤ (k + 1) * (n - u.length) := by
  by_cases hun : u.length ≤ n
  · have h1 := drainIdx_add_phi_le (u := u) (T := T) hK hk n
    have h2 := phi_drained_le (T := T) hK hk hv hun
    have e : (k + 1) * (n - u.length) + (k + 1) * u.length = (k + 1) * n := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hun]
    omega
  · rw [drainIdx_eq_zero_of_lt hv (by omega)]
    exact Nat.zero_le _

/-! ## Where the report states sit -/

/-- **An orbit state with `q = |v|` lies in the tick segment of round `pos + |v|`**:
`drainIdx (pos + |v| - 1) ≤ j < drainIdx (pos + |v|)`. -/
theorem report_index (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length) {j : ℕ}
    (hq : (orbit u v k p₁ r T j).1.q = v.length) :
    drainIdx u v k p₁ r T ((orbit u v k p₁ r T j).1.pos + v.length - 1) ≤ j ∧
      j < drainIdx u v k p₁ r T ((orbit u v k p₁ r T j).1.pos + v.length) := by
  have hPu := orbit_pos_ge (u := u) (v := v) (k := k) (p₁ := p₁) (r := r) (T := T) j
  constructor
  · by_contra hc
    have hlt := Nat.lt_of_not_le hc
    have hb := orbit_bounded (T := T) (p₁ := p₁) (r := r) hk hv
      (n := (orbit u v k p₁ r T j).1.pos + v.length - 1) (by omega) j hlt.le
    omega
  · by_contra hc
    have hle := Nat.le_of_not_lt hc
    have hmono := orbit_pos_mono (u := u) (v := v) (k := k) (p₁ := p₁) (r := r) (T := T) hle
    obtain ⟨h1, h2⟩ := drained_pos_add_q (u := u) (T := T) hK hk hv
      (n := (orbit u v k p₁ r T j).1.pos + v.length) (by omega)
    rw [drained_eq_orbit] at h1 h2
    omega

/-- Inside the tick segment of round `n+1`, a state with `q = |v|` ends exactly at `n+1`. -/
theorem report_round (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length) {n j : ℕ}
    (hj1 : drainIdx u v k p₁ r T n ≤ j) (hj2 : j < drainIdx u v k p₁ r T (n + 1))
    (hq : (orbit u v k p₁ r T j).1.q = v.length) :
    (orbit u v k p₁ r T j).1.pos + v.length = n + 1 := by
  obtain ⟨h1, h2⟩ := report_index (T := T) hK hk hv hq
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have := drainIdx_mono (u := u) (T := T) hK hk hv
      (show (orbit u v k p₁ r T j).1.pos + v.length ≤ n by omega)
    omega
  · have := drainIdx_mono (u := u) (T := T) hK hk hv
      (show n + 1 ≤ (orbit u v k p₁ r T j).1.pos + v.length - 1 by omega)
    omega

/-! ## The drained answer -/

/-- **Head-level form of the answer**: the round-`n+1` drained answer holds iff the head, running
the orbit segment `[drainIdx n, drainIdx (n+1))`, leaves some state with a `match` event. -/
theorem drainedAnswer_succ_iff (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length)
    (n : ℕ) :
    drainedAnswer u v k p₁ r T (n + 1) = true ↔
      ∃ j, drainIdx u v k p₁ r T n ≤ j ∧ j < drainIdx u v k p₁ r T (n + 1) ∧
        matchEvent u v (orbit u v k p₁ r T j) = true := by
  have hfuel : drainIdx u v k p₁ r T (n + 1) - drainIdx u v k p₁ r T n ≤ drainFuel k (n + 1) :=
    le_trans (Nat.sub_le _ _) (vRunSteps_le _ _ _)
  obtain ⟨hsteps, -⟩ := vRunIn_drained_of_le hK hk hv (Nat.le_add_right n 1) _ hfuel
  have hle := drainIdx_mono (u := u) (T := T) hK hk hv (Nat.le_add_right n 1)
  show vReportedIn u v k p₁ r T (n + 1) (drainFuel k (n + 1)) (drained u v k p₁ r T n) = true ↔ _
  rw [vReportedIn_iff, hsteps]
  constructor
  · rintro ⟨i, hi, hflag⟩
    rw [drained_eq_orbit, iterate_orbit] at hflag
    simp only [vReportFlag, decide_eq_true_eq] at hflag
    obtain ⟨hq, -, hc⟩ := hflag
    refine ⟨i + drainIdx u v k p₁ r T n, by omega, ?_, ?_⟩
    · rcases Nat.lt_or_ge (i + drainIdx u v k p₁ r T n) (drainIdx u v k p₁ r T (n + 1))
        with h | h
      · exact h
      · exfalso
        have heq : i + drainIdx u v k p₁ r T n = drainIdx u v k p₁ r T (n + 1) := by omega
        have hst := not_enabled_drained (u := u) (T := T) hK hk hv (n + 1)
        rw [drained_eq_orbit, ← heq] at hst
        exact hst (Or.inl hq)
    · simp only [matchEvent, decide_eq_true_eq]
      exact ⟨hq, hc⟩
  · rintro ⟨j, hj1, hj2, hm⟩
    refine ⟨j - drainIdx u v k p₁ r T n, by omega, ?_⟩
    rw [drained_eq_orbit, iterate_orbit, Nat.sub_add_cancel hj1]
    simp only [matchEvent, decide_eq_true_eq] at hm
    simp only [vReportFlag, decide_eq_true_eq]
    exact ⟨hm.1, report_round hK hk hv hj1 hj2 hm.1, hm.2⟩

/-- A `match` event on the orbit is a real occurrence of `x = u ++ v`. -/
theorem occAt_of_matchEvent (hK : KSimple v k p₁ r) (hk : 3 ≤ k)
    (hL1 : (k - 1) * u.length < (u ++ v).length ∧ (k - 2) * u.length < (k - 1) * p₁) {j : ℕ}
    (hm : matchEvent u v (orbit u v k p₁ r T j) = true) :
    OccAt (u ++ v) T ((orbit u v k p₁ r T j).1.pos - u.length) := by
  simp only [matchEvent, decide_eq_true_eq] at hm
  obtain ⟨hq, hc⟩ := hm
  obtain ⟨hpos, hml, -, -⟩ := orbit_vInv (T := T) hK hk hL1 j
  have hsv := (orbit_scanInv (u := u) (T := T) hK j).1
  rw [occAt_append_iff]
  refine ⟨?_, ?_⟩
  · rw [hc] at hml
    exact hml
  · rw [Nat.sub_add_cancel hpos]
    rw [hq] at hsv
    exact hsv

/-- **The drained answer is correct**: for `|x| ≤ n` it is
`decide (OccAt (u ++ v) T (n - |x|))`, the predicate behind `StageMatcher`/`MatchOracle`. -/
theorem drainedAnswer_correct (hK : KSimple v k p₁ r) (hk : 3 ≤ k) (hv : 0 < v.length)
    (hL1 : (k - 1) * u.length < (u ++ v).length ∧ (k - 2) * u.length < (k - 1) * p₁)
    (n : ℕ) (hn : u.length + v.length ≤ n) :
    drainedAnswer u v k p₁ r T n = decide (OccAt (u ++ v) T (n - (u.length + v.length))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hk0 : 0 < k := by omega
  rw [Bool.eq_iff_iff, decide_eq_true_iff, drainedAnswer_succ_iff hK hk0 hv m]
  constructor
  · rintro ⟨j, hj1, hj2, hm⟩
    have hocc := occAt_of_matchEvent hK hk hL1 hm
    have hq : (orbit u v k p₁ r T j).1.q = v.length := by
      simp only [matchEvent, decide_eq_true_eq] at hm
      exact hm.1
    have hround := report_round hK hk0 hv hj1 hj2 hq
    rwa [show m + 1 - (u.length + v.length) = (orbit u v k p₁ r T j).1.pos - u.length by omega]
  · intro hocc
    rw [occAt_append_iff] at hocc
    obtain ⟨hu, hvocc⟩ := hocc
    -- the scan cannot overtake the occurrence of `v` at `i`, so it reports it before draining
    have hex : ∃ j, j < drainIdx u v k p₁ r T (m + 1) ∧
        (orbit u v k p₁ r T j).1.q = v.length ∧
        (orbit u v k p₁ r T j).1.pos = m + 1 - (u.length + v.length) + u.length := by
      by_contra hcon
      have hno : ∀ j, j ≤ drainIdx u v k p₁ r T (m + 1) →
          (orbit u v k p₁ r T j).1.pos ≤ m + 1 - (u.length + v.length) + u.length := by
        intro j
        induction j with
        | zero => intro _; show u.length ≤ _; omega
        | succ j ih =>
          intro hj
          rw [orbit_succ, vStep_fst]
          exact scanStep_pos_le_of_occ hK hk0 (orbit_scanInv hK j) hvocc (ih (by omega))
            (fun hq hp => hcon ⟨j, by omega, hq, hp⟩)
      have h1 := hno _ (le_refl _)
      obtain ⟨h2, h3⟩ := drained_pos_add_q (u := u) (T := T) hK hk0 hv (n := m + 1) (by omega)
      rw [drained_eq_orbit] at h2 h3
      omega
    obtain ⟨j, hj, hq, hp⟩ := hex
    have hround : (orbit u v k p₁ r T j).1.pos + v.length = m + 1 := by omega
    have hidx := (report_index (T := T) hK hk0 hv hq).1
    rw [hround] at hidx
    refine ⟨j, by simpa using hidx, hj, ?_⟩
    obtain ⟨-, -, hcle, hdead⟩ := orbit_vInv (T := T) hK hk hL1 j
    rw [show (orbit u v k p₁ r T j).1.pos - u.length = m + 1 - (u.length + v.length) by omega]
      at hdead
    have hd := hdead hu
    simp only [matchEvent, decide_eq_true_eq]
    refine ⟨hq, ?_⟩
    rw [hq] at hd
    omega

/-- Before the pattern fits (`n < |x|`), the drained answer is `false`. -/
theorem drainedAnswer_eq_false_of_lt (hK : KSimple v k p₁ r) (hk : 0 < k) (hv : 0 < v.length)
    {n : ℕ} (hn : n < u.length + v.length) : drainedAnswer u v k p₁ r T n = false := by
  cases n with
  | zero => rfl
  | succ m =>
    rw [Bool.eq_false_iff]
    intro h
    rw [drainedAnswer_succ_iff hK hk hv] at h
    obtain ⟨j, hj1, hj2, hm⟩ := h
    have hq : (orbit u v k p₁ r T j).1.q = v.length := by
      simp only [matchEvent, decide_eq_true_eq] at hm
      exact hm.1
    have h1 := report_round hK hk hv hj1 hj2 hq
    have h2 := orbit_pos_ge (u := u) (v := v) (k := k) (p₁ := p₁) (r := r) (T := T) j
    omega

/-- Before the pattern fits (`n < |x|`), `vAnswer` is `false` too (no hypotheses needed). -/
theorem vAnswer_eq_false_of_lt {n : ℕ} (hn : n < u.length + v.length) :
    vAnswer u v k p₁ r T n = false := by
  cases n with
  | zero => rfl
  | succ m =>
    rw [Bool.eq_false_iff]
    intro h
    have h' : vReportedIn u v k p₁ r T (m + 1) (gsRate k) (vOnlineRun u v k p₁ r T m) = true := h
    rw [vReportedIn_iff] at h'
    obtain ⟨i, -, hflag⟩ := h'
    obtain ⟨j, hj⟩ := vOnlineRun_eq_orbit (u := u) (v := v) (k := k) (p₁ := p₁) (r := r)
      (T := T) m
    rw [hj, iterate_orbit] at hflag
    simp only [vReportFlag, decide_eq_true_eq] at hflag
    have h2 := orbit_pos_ge (u := u) (v := v) (k := k) (p₁ := p₁) (r := r) (T := T) (i + j)
    omega

/-- **The drained answer equals the fixed-rate answer `vAnswer` at every round.** -/
theorem drainedAnswer_eq_vAnswer (hK : KSimple v k p₁ r) (hk : 3 ≤ k) (hv : 0 < v.length)
    (hL1 : (k - 1) * u.length < (u ++ v).length ∧ (k - 2) * u.length < (k - 1) * p₁)
    (n : ℕ) : drainedAnswer u v k p₁ r T n = vAnswer u v k p₁ r T n := by
  by_cases hn : u.length + v.length ≤ n
  · rw [drainedAnswer_correct hK hk hv hL1 n hn,
      vAnswer_correct hK hk hK.period_pos (by simpa using hL1.1) hL1.2 hv n hn]
  · rw [drainedAnswer_eq_false_of_lt hK (by omega) hv (by omega),
      vAnswer_eq_false_of_lt (by omega)]

end Orbit

/-! ## Small sanity checks (the same instances as in `GSVerifier`) -/

section Examples

/-- `u = [1]`, `v = [0]*8`, `k = 8`, `p₁ = 1`, `r = 8`: the only occurrence ends at round 9. -/
example :
    drainedAnswer ([1] : List ℕ) [0, 0, 0, 0, 0, 0, 0, 0] 8 1 8
      [1, 0, 0, 0, 0, 0, 0, 0, 0, 0] 9 = true := by decide

example :
    drainedAnswer ([1] : List ℕ) [0, 0, 0, 0, 0, 0, 0, 0] 8 1 8
      [1, 0, 0, 0, 0, 0, 0, 0, 0, 0] 10 = false := by decide

/-- `u = []`, `v = [0,1,1]` (no period): rounds 3 and 6 report. -/
example : drainedAnswer ([] : List ℕ) [0, 1, 1] 8 3 0 [0, 1, 1, 0, 1, 1] 6 = true := by decide
example : drainedAnswer ([] : List ℕ) [0, 1, 1] 8 3 0 [0, 1, 1, 0, 1, 1] 5 = false := by decide

/-- The drained state of round 5 in the last example: `pos + q = 5`, `q < |v|`. -/
example : (drained ([] : List ℕ) [0, 1, 1] 8 3 0 [0, 1, 1, 0, 1, 1] 5).1 = ⟨3, 2⟩ := by decide

end Examples

end PalPeg.GSDrained
