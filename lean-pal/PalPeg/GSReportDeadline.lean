import PalPeg.GSDrained
import PalPeg.GSDecomposeL1

/-!
# The prefix check is never late: an unconditional report deadline

Along the verifier orbit (`GSDrained.orbit`, the `vStep` iterates from
`vInit u = (⟨|u|, 0⟩, 0)`), whenever the scan reaches a full match of `v` (`q = |v|`), the
interleaved prefix check has either **finished** (`checked = |u|`) or is **stuck on a real
mismatch** (`checked < |u|` and `T[pos - |u| + checked]? ≠ u[checked]?`).

This is list level only (no head VM, no `KSimple`, no `MatchLen`).

## The invariant (`DeadlineInv`)

`VInv` (`GSVerifier.lean:64`) carries the deadline only under the hypothesis that the candidate
really matches. Here it is **unconditional**, with the stuck case as the alternative:

* `checked ≤ |u|`, `q ≤ |v|`, and
* `Stuck ∨ |u| ≤ checked + 2 * (|v| - q)`.

It is preserved by `vStep` (`vStep_deadlineInv`):

* a shift (report or mismatch) sets `checked := 0` and `q := gsNextQ …`, and the arithmetic
  deadline `ShiftDeadline` (`|u| ≤ 2 * (|v| - gsNextQ k p₁ r q)` for every `q ≤ |v|`) restores
  the right disjunct;
* a successful `v` comparison keeps `pos`, raises `q` by one and runs `vComp` twice: each
  comparison either succeeds (`checked` grows, paying for the lost `2`) or fails, and then the
  check is stuck at the same `pos`, where it stays (`vComp` does not move past a mismatch).

At `q = |v|` the right disjunct reads `|u| ≤ checked`, so `checked = |u|`
(`done_or_stuck_of_inv`).

## The arithmetic for `decompose` (`decompose_shiftDeadline`)

* `p₁ ≠ 0`: `GSDecomposeL1.decompose_deadline` (L1 through `prefix_verifier_deadline`).
* `p₁ = 0` (no period): `GSCore.none_case` gives `r = 0`, so `gsNextQ k 0 0 q = 0` for all
  `q`, and `|u| ≤ 2|v|` follows from `3s < |x|` (`decompose_three_mul_cut_lt`).

The only hypothesis is `4 ≤ k` (the head program runs `k = 8`). Nothing is assumed about `x`
or `T`.

## Main results

* `orbit_report_deadline` — the generic statement under `ShiftDeadline`.
* `report_deadline` — the instance `(s, p₁, r) = decompose x k`, `u = x.take s`,
  `v = x.drop s`, every orbit index.
* `report_deadline_iterate` — the same, stated on `(vStep …)^[j] (⟨s, 0⟩, 0)`.

## A side fact about the raw no-period output

In the raw no-period output `(s, 0, 0)` the shift at `q = 0` is `gsShift k 0 0 0 = 0`
(`gsShift_noPeriod_zero`): a mismatch at `q = 0` leaves `pos` unchanged, so the scan never
advances. The deadline statement here holds anyway (it is about `checked`, not progress), but
anything that needs the scan to move must use the normalized `(|v| + 1, 0)` (`gsDecN`).
-/

set_option autoImplicit false

namespace PalPeg.GSReportDeadline

open GSDrained

universe u
variable {α : Type u}

/-! ## §1 Definitions -/

/-- The prefix check of the current candidate is stuck on a real mismatch: it has not
finished and the next comparison `T[pos - |u| + checked]? = u[checked]?` fails. -/
def Stuck (u T : List α) (z : VState) : Prop :=
  z.2 < u.length ∧ T[z.1.pos - u.length + z.2]? ≠ u[z.2]?

/-- The unconditional deadline invariant: `checked ≤ |u|`, `q ≤ |v|`, and either the check is
stuck, or it will finish by the time `q` reaches `|v|` at 2 comparisons per `v` match. -/
def DeadlineInv (u v T : List α) (z : VState) : Prop :=
  z.2 ≤ u.length ∧ z.1.q ≤ v.length ∧
    (Stuck u T z ∨ u.length ≤ z.2 + 2 * (v.length - z.1.q))

/-- The arithmetic deadline after any shift: `|u| ≤ 2 * (|v| - gsNextQ k p₁ r q)`. -/
def ShiftDeadline (u v : List α) (k p₁ r : ℕ) : Prop :=
  ∀ q, q ≤ v.length → u.length ≤ 2 * (v.length - gsNextQ k p₁ r q)

/-! ## §2 Small facts about `gsNextQ` and `vComp` -/

theorem gsNextQ_zero (k p₁ r : ℕ) : gsNextQ k p₁ r 0 = 0 := by
  unfold gsNextQ; split_ifs <;> omega

theorem gsNextQ_le (k p₁ r q : ℕ) : gsNextQ k p₁ r q ≤ q := by
  unfold gsNextQ; split_ifs <;> omega

/-- No period (`p₁ = 0`, `r = 0`): the retained match is always reset. -/
theorem gsNextQ_noPeriod (k q : ℕ) : gsNextQ k 0 0 q = 0 := by
  unfold gsNextQ; split_ifs <;> omega

/-- No period (`p₁ = 0`, `r = 0`): the shift at `q = 0` is `0`, so the scan does not move. -/
theorem gsShift_noPeriod_zero (k : ℕ) : gsShift k 0 0 0 = 0 := by
  unfold gsShift; rw [if_pos (by omega)]

/-- `ShiftDeadline` at `q = 0` is the deadline of the initial state. -/
theorem ShiftDeadline.init {u v : List α} {k p₁ r : ℕ} (hdl : ShiftDeadline u v k p₁ r) :
    u.length ≤ 2 * v.length := by
  have h := hdl 0 (Nat.zero_le _)
  rwa [gsNextQ_zero, Nat.sub_zero] at h

/-! ## §3 The invariant along the orbit -/

theorem deadlineInv_init {u v T : List α} {k p₁ r : ℕ} (hdl : ShiftDeadline u v k p₁ r) :
    DeadlineInv u v T (vInit u) := by
  refine ⟨Nat.zero_le _, Nat.zero_le _, Or.inr ?_⟩
  show u.length ≤ 0 + 2 * (v.length - 0)
  have := hdl.init
  omega

/-- The state right after a shift (report or mismatch) satisfies the invariant. -/
theorem deadlineInv_shift {u v T : List α} {k p₁ r : ℕ} (hdl : ShiftDeadline u v k p₁ r)
    {pos q : ℕ} (hq : q ≤ v.length) :
    DeadlineInv u v T ((⟨pos + gsShift k p₁ r q, gsNextQ k p₁ r q⟩ : ScanState), 0) := by
  refine ⟨Nat.zero_le _, ?_, Or.inr ?_⟩
  · show gsNextQ k p₁ r q ≤ v.length
    exact le_trans (gsNextQ_le k p₁ r q) hq
  · show u.length ≤ 0 + 2 * (v.length - gsNextQ k p₁ r q)
    have := hdl q hq
    omega

section Step

variable [DecidableEq α]

/-- A comparison that fails leaves `checked` where it is. -/
theorem vComp_of_mismatch {u T : List α} {pos c : ℕ}
    (hne : T[pos - u.length + c]? ≠ u[c]?) : vComp u T pos c = c := by
  unfold vComp
  rw [if_neg (fun h => hne h.2)]

/-- A comparison that succeeds advances `checked` by one. -/
theorem vComp_of_match {u T : List α} {pos c : ℕ} (hc : c < u.length)
    (heq : T[pos - u.length + c]? = u[c]?) : vComp u T pos c = c + 1 := by
  unfold vComp
  rw [if_pos ⟨hc, heq⟩]

/-- **One step.** `vStep` preserves the unconditional deadline invariant. -/
theorem vStep_deadlineInv {u v T : List α} {k p₁ r : ℕ} (hdl : ShiftDeadline u v k p₁ r)
    {z : VState} (h : DeadlineInv u v T z) : DeadlineInv u v T (vStep u v k p₁ r T z) := by
  obtain ⟨hc, hq, hor⟩ := h
  unfold vStep
  split_ifs with hfull hmatch
  · rw [show scanStep v k p₁ r T z.1
        = (⟨z.1.pos + gsShift k p₁ r z.1.q, gsNextQ k p₁ r z.1.q⟩ : ScanState) from by
      unfold scanStep; rw [if_pos hfull]]
    exact deadlineInv_shift hdl hq
  · rw [show scanStep v k p₁ r T z.1 = (⟨z.1.pos, z.1.q + 1⟩ : ScanState) from by
      unfold scanStep; rw [if_neg hfull, if_pos hmatch]]
    have hqlt : z.1.q < v.length := lt_of_le_of_ne hq hfull
    refine ⟨vComp_le_length (vComp_le_length hc), ?_, ?_⟩
    · show z.1.q + 1 ≤ v.length
      omega
    · show Stuck u T ((⟨z.1.pos, z.1.q + 1⟩ : ScanState),
            vComp u T z.1.pos (vComp u T z.1.pos z.2)) ∨
          u.length ≤ vComp u T z.1.pos (vComp u T z.1.pos z.2) + 2 * (v.length - (z.1.q + 1))
      rcases hor with ⟨hlt, hne⟩ | hdd
      · -- stuck before: the same comparison fails again, twice
        have e : vComp u T z.1.pos z.2 = z.2 := vComp_of_mismatch hne
        rw [e, e]
        exact Or.inl ⟨hlt, hne⟩
      · by_cases hcu : z.2 < u.length
        · by_cases hm1 : T[z.1.pos - u.length + z.2]? = u[z.2]?
          · rw [vComp_of_match hcu hm1]
            by_cases hcu2 : z.2 + 1 < u.length
            · by_cases hm2 : T[z.1.pos - u.length + (z.2 + 1)]? = u[z.2 + 1]?
              · rw [vComp_of_match hcu2 hm2]
                right
                omega
              · rw [vComp_of_mismatch hm2]
                exact Or.inl ⟨hcu2, hm2⟩
            · rw [vComp_eq_of_ge (by omega)]
              right
              omega
          · have e : vComp u T z.1.pos z.2 = z.2 := vComp_of_mismatch hm1
            rw [e, e]
            exact Or.inl ⟨hcu, hm1⟩
        · have e : vComp u T z.1.pos z.2 = z.2 := vComp_eq_of_ge (by omega)
          rw [e, e]
          right
          omega
  · rw [show scanStep v k p₁ r T z.1
        = (⟨z.1.pos + gsShift k p₁ r z.1.q, gsNextQ k p₁ r z.1.q⟩ : ScanState) from by
      unfold scanStep; rw [if_neg hfull, if_neg hmatch]]
    exact deadlineInv_shift hdl hq

/-- The invariant along any `vStep` run from a state that satisfies it. -/
theorem iterate_deadlineInv {u v T : List α} {k p₁ r : ℕ} (hdl : ShiftDeadline u v k p₁ r) :
    ∀ (j : ℕ) (z : VState), DeadlineInv u v T z →
      DeadlineInv u v T ((vStep u v k p₁ r T)^[j] z) := by
  intro j
  induction j with
  | zero => intro z h; exact h
  | succ j ih =>
    intro z h
    rw [Function.iterate_succ_apply]
    exact ih _ (vStep_deadlineInv hdl h)

/-- The invariant at every orbit index. -/
theorem orbit_deadlineInv {u v T : List α} {k p₁ r : ℕ} (hdl : ShiftDeadline u v k p₁ r)
    (j : ℕ) : DeadlineInv u v T (orbit u v k p₁ r T j) :=
  iterate_deadlineInv hdl j _ (deadlineInv_init hdl)

end Step

/-! ## §4 Reading the invariant at a full match -/

/-- At `q = |v|` the invariant says: finished or stuck. -/
theorem done_or_stuck_of_inv {u v T : List α} {z : VState} (h : DeadlineInv u v T z)
    (hq : z.1.q = v.length) : z.2 = u.length ∨ Stuck u T z := by
  obtain ⟨hc, -, hor⟩ := h
  rcases hor with hst | hdd
  · exact Or.inr hst
  · left
    rw [hq, Nat.sub_self, Nat.mul_zero, Nat.add_zero] at hdd
    omega

section Main

variable [DecidableEq α]

/-- **Generic report deadline.** Under the arithmetic deadline `ShiftDeadline`, at every orbit
index where `v` has fully matched, the prefix check has finished or is stuck on a real
mismatch. -/
theorem orbit_report_deadline {u v T : List α} {k p₁ r : ℕ} (hdl : ShiftDeadline u v k p₁ r)
    (j : ℕ) (hq : (orbit u v k p₁ r T j).1.q = v.length) :
    (orbit u v k p₁ r T j).2 = u.length ∨
      ((orbit u v k p₁ r T j).2 < u.length ∧
        T[(orbit u v k p₁ r T j).1.pos - u.length + (orbit u v k p₁ r T j).2]?
          ≠ u[(orbit u v k p₁ r T j).2]?) :=
  done_or_stuck_of_inv (orbit_deadlineInv hdl j) hq

/-! ## §5 The instance `decompose` -/

/-- **The arithmetic deadline holds for `decompose`** at every `k ≥ 4`, for every `x`
(both the period case, by L1, and the no-period case, where `gsNextQ` is always `0`). -/
theorem decompose_shiftDeadline {k : ℕ} (hk : 4 ≤ k) (x : List α) :
    ShiftDeadline (x.take (decompose x k).1) (x.drop (decompose x k).1) k
      (decompose x k).2.1 (decompose x k).2.2 := by
  intro q hq
  by_cases hp : (decompose x k).2.1 = 0
  · have H := GSDecomposeL1.decompose_gsDecomp hk x
    have hr : (decompose x k).2.2 = 0 := (H.none_case hp).1
    rw [hp, hr, gsNextQ_noPeriod, Nat.sub_zero]
    have hcut : (decompose x k).1 ≤ x.length := H.cut_le
    rw [List.length_take, List.length_drop]
    by_cases hx : x = []
    · subst hx
      simp
    · have h3 := GSDecomposeL1.decompose_three_mul_cut_lt hk hx
      omega
  · exact le_of_lt (GSDecomposeL1.decompose_deadline hk x hp hq)

/-- The initial state of the orbit is `(⟨s, 0⟩, 0)`. -/
theorem vInit_take_decompose {k : ℕ} (hk : 4 ≤ k) (x : List α) :
    vInit (x.take (decompose x k).1) = ((⟨(decompose x k).1, 0⟩ : ScanState), 0) := by
  have hcut : (decompose x k).1 ≤ x.length := (GSDecomposeL1.decompose_gsDecomp hk x).cut_le
  unfold vInit
  rw [List.length_take, Nat.min_eq_left hcut]

/-- **Main theorem (unconditional report deadline for `decompose`).**
Let `(s, p₁, r) = decompose x k` with `k ≥ 4`, `u = x.take s`, `v = x.drop s`. At every index
`j` of the verifier orbit from `(⟨s, 0⟩, 0)` where the scan has fully matched `v`
(`q = |v|`), the prefix check has finished (`checked = |u|`) or is stuck on a real mismatch
(`checked < |u|` and `T[pos - |u| + checked]? ≠ u[checked]?`). -/
theorem report_deadline {k : ℕ} (hk : 4 ≤ k) {x : List α} {s p₁ r : ℕ}
    (hdec : decompose x k = (s, p₁, r)) (T : List α) (j : ℕ)
    (hq : (orbit (x.take s) (x.drop s) k p₁ r T j).1.q = (x.drop s).length) :
    (orbit (x.take s) (x.drop s) k p₁ r T j).2 = (x.take s).length ∨
      ((orbit (x.take s) (x.drop s) k p₁ r T j).2 < (x.take s).length ∧
        T[(orbit (x.take s) (x.drop s) k p₁ r T j).1.pos - (x.take s).length
            + (orbit (x.take s) (x.drop s) k p₁ r T j).2]?
          ≠ (x.take s)[(orbit (x.take s) (x.drop s) k p₁ r T j).2]?) := by
  have hdl := decompose_shiftDeadline hk x
  rw [hdec] at hdl
  exact orbit_report_deadline hdl j hq

/-- **The same, on the iterates of `vStep` from `(⟨s, 0⟩, 0)`** (`s` is `|u|`). -/
theorem report_deadline_iterate {k : ℕ} (hk : 4 ≤ k) {x : List α} {s p₁ r : ℕ}
    (hdec : decompose x k = (s, p₁, r)) (T : List α) (j : ℕ)
    (hq : ((vStep (x.take s) (x.drop s) k p₁ r T)^[j]
        ((⟨s, 0⟩ : ScanState), 0)).1.q = (x.drop s).length) :
    ((vStep (x.take s) (x.drop s) k p₁ r T)^[j] ((⟨s, 0⟩ : ScanState), 0)).2
        = (x.take s).length ∨
      (((vStep (x.take s) (x.drop s) k p₁ r T)^[j] ((⟨s, 0⟩ : ScanState), 0)).2
          < (x.take s).length ∧
        T[((vStep (x.take s) (x.drop s) k p₁ r T)^[j] ((⟨s, 0⟩ : ScanState), 0)).1.pos
            - (x.take s).length
            + ((vStep (x.take s) (x.drop s) k p₁ r T)^[j] ((⟨s, 0⟩ : ScanState), 0)).2]?
          ≠ (x.take s)[((vStep (x.take s) (x.drop s) k p₁ r T)^[j]
              ((⟨s, 0⟩ : ScanState), 0)).2]?) := by
  have hinit : vInit (x.take s) = ((⟨s, 0⟩ : ScanState), 0) := by
    have h := vInit_take_decompose hk x
    rw [hdec] at h
    exact h
  have horb : (vStep (x.take s) (x.drop s) k p₁ r T)^[j] ((⟨s, 0⟩ : ScanState), 0)
      = orbit (x.take s) (x.drop s) k p₁ r T j := by
    unfold orbit
    rw [hinit]
  rw [horb] at hq ⊢
  exact report_deadline hk hdec T j hq

/-- `k = 8`, the head program's constant. -/
theorem report_deadline_eight {x : List α} {s p₁ r : ℕ}
    (hdec : decompose x 8 = (s, p₁, r)) (T : List α) (j : ℕ)
    (hq : (orbit (x.take s) (x.drop s) 8 p₁ r T j).1.q = (x.drop s).length) :
    (orbit (x.take s) (x.drop s) 8 p₁ r T j).2 = (x.take s).length ∨
      ((orbit (x.take s) (x.drop s) 8 p₁ r T j).2 < (x.take s).length ∧
        T[(orbit (x.take s) (x.drop s) 8 p₁ r T j).1.pos - (x.take s).length
            + (orbit (x.take s) (x.drop s) 8 p₁ r T j).2]?
          ≠ (x.take s)[(orbit (x.take s) (x.drop s) 8 p₁ r T j).2]?) :=
  report_deadline (by decide) hdec T j hq

end Main

/-! ## §6 Checks -/

section Examples

/-- The raw no-period output stalls the scan: with `p₁ = r = 0`, a mismatch at `q = 0`
shifts by `0`. -/
example : scanStep ([0, 1] : List ℕ) 8 0 0 [1, 1] ⟨0, 0⟩ = ⟨0, 0⟩ := by decide

end Examples

end PalPeg.GSReportDeadline
