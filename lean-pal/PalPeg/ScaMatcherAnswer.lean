import PalPeg.GSDrained
import PalPeg.GSReportDeadline
import PalPeg.GSDecomposeL1

/-!
# The matcher's answer on the verifier orbit of the head's decomposition

List level only (no head VM). The head matcher runs the verifier orbit
`GSDrained.orbit u v 8 p₁ r T` with `u = x.take s`, `v = x.drop s`, where
`(s, p₁raw, r) = decompose x 8` and `p₁` is the **normalized** first period `normP1 x`:
`p₁raw` when a period exists, and `|v| + 1` when it does not (`p₁raw = 0`, and then `r = 0`).
With `r = 0` and `|v| < 8·(|v| + 1)` the shift rule `gsShift`/`gsNextQ` never takes the
period branch, which is the head's "reset shift whenever `pe = false`". `normP1` is the period
of `GSDecomposeL1.gsDecN x 8 |x|` (`normP1_eq_gsDecN`).

## Results

* `normP1_none` / `normP1_some` / `normP1_pe`: the two cases of the normalization, with
  `pe = decide (p₁raw ≠ 0)`.
* The hypotheses of `GSDrained` / `GSReportDeadline`, for every `x ≠ []`, with no further
  condition: `shiftDeadline_normP1` (`ShiftDeadline`, even for `x = []`), `ksimple_normP1`
  (`KSimple v 8 p₁ r`, for every `x`), `drop_length_pos` (`0 < |v|`), `l1_normP1` (L1:
  `7·|u| < |u ++ v|` and `6·|u| < 7·p₁`).
* **The answer** (`answer_iff_occAt`): some orbit index `j` has a `match` event and ends at
  text length `n` (`pos + |v| = n`) iff `|x| ≤ n` and `x` occurs in `T` starting at `n - |x|`.
  In the suffix form of `Matching.occursAt`: `answer_iff_occursAt_take` (`n ≤ |T|`:
  iff `x` is a suffix of `T.take n`) and `answer_iff_occursAt` (`n = |T|`).
* **Uniqueness** (`matchEvent_orbit_unique`, `answer_index_unique`): two match events at the
  same `pos` are the same orbit index; hence at most one `j` answers each `n`.
-/

set_option autoImplicit false

namespace PalPeg.ScaMatcherAnswer

open GSDrained GSReportDeadline

universe u
variable {α : Type u}

/-! ## The normalized first period -/

section Norm
variable [DecidableEq α]

/-- The normalized first period of the head's decomposition `decompose x 8`: the raw `p₁` when
it is a period, `|x.drop s| + 1` in the no-period case `p₁ = 0`. -/
def normP1 (x : List α) : ℕ :=
  if (decompose x 8).2.1 = 0 then (x.drop (decompose x 8).1).length + 1
  else (decompose x 8).2.1

theorem normP1_of_dec {x : List α} {s p r : ℕ} (hdec : decompose x 8 = (s, p, r)) :
    normP1 x = if p = 0 then (x.drop s).length + 1 else p := by
  simp only [normP1, hdec]

theorem normP1_pos (x : List α) : 0 < normP1 x := by
  unfold normP1; split_ifs with h <;> omega

/-- `normP1` is the period of the normalized decomposition `GSDecomposeL1.gsDecN`. -/
theorem normP1_eq_gsDecN {β : Type} [DecidableEq β] (x : List β) :
    normP1 x = (GSDecomposeL1.gsDecN x 8 x.length).2.1 := by
  simp only [normP1, GSDecomposeL1.gsDecN, List.take_length]
  split_ifs <;> rfl

/-- **No period** (`p₁raw = 0`): `|x| - s < 8·p₁`, so the shift never takes the period branch. -/
theorem normP1_none {x : List α} {s p r : ℕ} (hdec : decompose x 8 = (s, p, r)) (hp : p = 0) :
    x.length - s < 8 * normP1 x := by
  rw [normP1_of_dec hdec, if_pos hp, List.length_drop]
  omega

/-- **A period** (`p₁raw ≠ 0`): the normalized period is the raw one. -/
theorem normP1_some {x : List α} {s p r : ℕ} (hdec : decompose x 8 = (s, p, r)) (hp : p ≠ 0) :
    1 ≤ normP1 x ∧ normP1 x = p := by
  rw [normP1_of_dec hdec, if_neg hp]
  omega

/-- The two cases, with the head's flag `pe = decide (p₁raw ≠ 0)`. -/
theorem normP1_pe {x : List α} {s p r : ℕ} (hdec : decompose x 8 = (s, p, r)) :
    (decide (p ≠ 0) = false → x.length - s < 8 * normP1 x) ∧
      (decide (p ≠ 0) = true → 1 ≤ normP1 x ∧ normP1 x = p) := by
  refine ⟨fun h => normP1_none hdec (by simpa using h), fun h => normP1_some hdec (by simpa using h)⟩

/-! ## The hypotheses of `GSDrained` and `GSReportDeadline` -/

theorem gsDecomp_eight (x : List α) :
    GSDecomp x 8 (decompose x 8).1 (decompose x 8).2.1 (decompose x 8).2.2 :=
  GSDecomposeL1.decompose_gsDecomp (by decide) x

/-- In the no-period case the reach is `0`. -/
theorem reach_of_none {x : List α} {s p r : ℕ} (hdec : decompose x 8 = (s, p, r)) (hp : p = 0) :
    r = 0 := by
  have H := gsDecomp_eight x
  rw [hdec] at H
  exact (H.none_case hp).1

/-- The retained match after a shift is the same for the raw and the normalized period. -/
theorem gsNextQ_normP1 {x : List α} {s p r : ℕ} (hdec : decompose x 8 = (s, p, r)) {q : ℕ}
    (hq : q ≤ (x.drop s).length) : gsNextQ 8 (normP1 x) r q = gsNextQ 8 p r q := by
  by_cases hp : p = 0
  · have hr := reach_of_none hdec hp
    subst hr
    rw [hp, gsNextQ_noPeriod]
    unfold gsNextQ
    rw [normP1_of_dec hdec, if_pos hp, if_neg (by omega)]
  · rw [(normP1_some hdec hp).2]

/-- **`ShiftDeadline` for the normalized period** (every `x`). -/
theorem shiftDeadline_normP1 {x : List α} {s p r : ℕ} (hdec : decompose x 8 = (s, p, r)) :
    ShiftDeadline (x.take s) (x.drop s) 8 (normP1 x) r := by
  intro q hq
  have h := decompose_shiftDeadline (k := 8) (by decide) x q
  rw [hdec] at h
  rw [gsNextQ_normP1 hdec hq]
  exact h hq

/-- **`KSimple` for the normalized period** (every `x`). -/
theorem ksimple_normP1 {x : List α} {s p r : ℕ} (hdec : decompose x 8 = (s, p, r)) :
    KSimple (x.drop s) 8 (normP1 x) r := by
  have H := gsDecomp_eight x
  rw [hdec] at H
  by_cases hp : p = 0
  · have hr := reach_of_none hdec hp
    subst hr
    rw [normP1_of_dec hdec, if_pos hp]
    exact H.toGSCore.ksimple_none hp
  · rw [(normP1_some hdec hp).2]
    exact H.ksimple hp

theorem cut_le {x : List α} {s p r : ℕ} (hdec : decompose x 8 = (s, p, r)) : s ≤ x.length := by
  have H := gsDecomp_eight x
  rw [hdec] at H
  exact H.cut_le

/-- `7·s < |x|` for `x ≠ []` (L1, first half). -/
theorem seven_cut_lt {x : List α} {s p r : ℕ} (hdec : decompose x 8 = (s, p, r)) (hx : x ≠ []) :
    7 * s < x.length := by
  have H := gsDecomp_eight x
  rw [hdec] at H
  exact H.cut_bound hx

/-- **`0 < |x.drop s|`** for `x ≠ []`. -/
theorem drop_length_pos {x : List α} {s p r : ℕ} (hdec : decompose x 8 = (s, p, r))
    (hx : x ≠ []) : 0 < (x.drop s).length := by
  have := seven_cut_lt hdec hx
  rw [List.length_drop]
  omega

theorem take_length {x : List α} {s p r : ℕ} (hdec : decompose x 8 = (s, p, r)) :
    (x.take s).length = s := by
  rw [List.length_take]; have := cut_le hdec; omega

/-- **L1 for the normalized period** (`x ≠ []`): `7·|u| < |u ++ v|` and `6·|u| < 7·p₁`. -/
theorem l1_normP1 {x : List α} {s p r : ℕ} (hdec : decompose x 8 = (s, p, r)) (hx : x ≠ []) :
    (8 - 1) * (x.take s).length < (x.take s ++ x.drop s).length ∧
      (8 - 2) * (x.take s).length < (8 - 1) * normP1 x := by
  have H := gsDecomp_eight x
  rw [hdec] at H
  have h7 := seven_cut_lt hdec hx
  rw [List.take_append_drop, take_length hdec]
  refine ⟨by omega, ?_⟩
  by_cases hp : p = 0
  · rw [normP1_of_dec hdec, if_pos hp, List.length_drop]
    omega
  · rw [(normP1_some hdec hp).2]
    exact H.cut_period_bound hp

end Norm

/-! ## The answer -/

section Answer
variable [DecidableEq α]

/-- **The answer at text length `n`.** For `x ≠ []`, `(s, p₁raw, r) = decompose x 8`,
`u = x.take s`, `v = x.drop s` and the normalized period: some index of the verifier orbit has
a `match` event and ends at `n` (`pos + |v| = n`) iff `|x| ≤ n` and `x` occurs in `T` at the
start index `n - |x|`. -/
theorem answer_iff_occAt {x : List α} {s p r : ℕ} (hdec : decompose x 8 = (s, p, r))
    (hx : x ≠ []) (T : List α) (n : ℕ) :
    (∃ j, matchEvent (x.take s) (x.drop s) (orbit (x.take s) (x.drop s) 8 (normP1 x) r T j) = true ∧
        (orbit (x.take s) (x.drop s) 8 (normP1 x) r T j).1.pos + (x.drop s).length = n) ↔
      (x.length ≤ n ∧ OccAt x T (n - x.length)) := by
  have hK := ksimple_normP1 hdec
  have hv := drop_length_pos hdec hx
  have hL1 := l1_normP1 hdec hx
  have hlen : (x.take s).length + (x.drop s).length = x.length := by
    rw [take_length hdec, List.length_drop]; have := cut_le hdec; omega
  constructor
  · rintro ⟨j, hm, hpos⟩
    have hocc := occAt_of_matchEvent hK (by decide) hL1 hm
    rw [List.take_append_drop] at hocc
    have hge := orbit_pos_ge (u := x.take s) (v := x.drop s) (k := 8) (p₁ := normP1 x) (r := r)
      (T := T) j
    refine ⟨by omega, ?_⟩
    rwa [show n - x.length = (orbit (x.take s) (x.drop s) 8 (normP1 x) r T j).1.pos
      - (x.take s).length by omega]
  · rintro ⟨hn, hocc⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hv; omega⟩
    have hd := drainedAnswer_correct hK (by decide) hv hL1 (m + 1) (by omega) (T := T)
    rw [List.take_append_drop, hlen] at hd
    have htrue : drainedAnswer (x.take s) (x.drop s) 8 (normP1 x) r T (m + 1) = true := by
      rw [hd]; exact decide_eq_true hocc
    rw [drainedAnswer_succ_iff hK (by decide) hv] at htrue
    obtain ⟨j, hj1, hj2, hm⟩ := htrue
    have hq : (orbit (x.take s) (x.drop s) 8 (normP1 x) r T j).1.q = (x.drop s).length := by
      simp only [matchEvent, decide_eq_true_eq] at hm
      exact hm.1
    exact ⟨j, hm, report_round hK (by decide) hv hj1 hj2 hq⟩

/-- **The answer in the suffix form** of `Matching.occursAt`, for a text length `n ≤ |T|`:
`x` is a suffix of `T.take n`. -/
theorem answer_iff_occursAt_take {x : List α} {s p r : ℕ} (hdec : decompose x 8 = (s, p, r))
    (hx : x ≠ []) (T : List α) {n : ℕ} (hn : n ≤ T.length) :
    (∃ j, matchEvent (x.take s) (x.drop s) (orbit (x.take s) (x.drop s) 8 (normP1 x) r T j) = true ∧
        (orbit (x.take s) (x.drop s) 8 (normP1 x) r T j).1.pos + (x.drop s).length = n) ↔
      occursAt x (T.take n) := by
  rw [answer_iff_occAt hdec hx T n]
  constructor
  · rintro ⟨hxn, hocc⟩
    have h := (occAt_iff_occursAt (v := x) (T := T) (i := n - x.length) (by omega)).mp hocc
    rwa [show n - x.length + x.length = n by omega] at h
  · intro h
    have hxn : x.length ≤ n := by
      have := h.1; rw [List.length_take] at this; omega
    refine ⟨hxn, (occAt_iff_occursAt (v := x) (T := T) (i := n - x.length) (by omega)).mpr ?_⟩
    rwa [show n - x.length + x.length = n by omega]

/-- **The answer at the whole text** (`n = |T|`): `x` is a suffix of `T`. -/
theorem answer_iff_occursAt {x : List α} {s p r : ℕ} (hdec : decompose x 8 = (s, p, r))
    (hx : x ≠ []) (T : List α) :
    (∃ j, matchEvent (x.take s) (x.drop s) (orbit (x.take s) (x.drop s) 8 (normP1 x) r T j) = true ∧
        (orbit (x.take s) (x.drop s) 8 (normP1 x) r T j).1.pos + (x.drop s).length = T.length) ↔
      occursAt x T := by
  rw [answer_iff_occursAt_take hdec hx T (le_refl _), List.take_length]

end Answer

/-! ## Uniqueness -/

section Unique
variable [DecidableEq α] {u v T : List α} {k p₁ r : ℕ}

/-- After a full match (`q = |v|`) the scan shifts by a positive amount. -/
theorem orbit_pos_lt_succ (hp : 0 < p₁) {j : ℕ} (hq : (orbit u v k p₁ r T j).1.q = v.length) :
    (orbit u v k p₁ r T j).1.pos < (orbit u v k p₁ r T (j + 1)).1.pos := by
  rw [orbit_succ, vStep_fst]
  unfold scanStep
  rw [if_pos hq]
  have := gsShift_pos (k := k) (r := r) (q := (orbit u v k p₁ r T j).1.q) hp
  dsimp only
  omega

/-- **Two match events at the same position are the same orbit index.** -/
theorem matchEvent_orbit_unique (hp : 0 < p₁) {j j' : ℕ}
    (hm : matchEvent u v (orbit u v k p₁ r T j) = true)
    (hm' : matchEvent u v (orbit u v k p₁ r T j') = true)
    (hpos : (orbit u v k p₁ r T j).1.pos = (orbit u v k p₁ r T j').1.pos) : j = j' := by
  simp only [matchEvent, decide_eq_true_eq] at hm hm'
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have h1 := orbit_pos_lt_succ (T := T) hp hm.1
    have h2 := orbit_pos_mono (u := u) (v := v) (k := k) (p₁ := p₁) (r := r) (T := T)
      (show j + 1 ≤ j' by omega)
    omega
  · have h1 := orbit_pos_lt_succ (T := T) hp hm'.1
    have h2 := orbit_pos_mono (u := u) (v := v) (k := k) (p₁ := p₁) (r := r) (T := T)
      (show j' + 1 ≤ j by omega)
    omega

/-- **At most one orbit index answers each text length `n`.** -/
theorem answer_index_unique (hp : 0 < p₁) {n j j' : ℕ}
    (hm : matchEvent u v (orbit u v k p₁ r T j) = true)
    (hn : (orbit u v k p₁ r T j).1.pos + v.length = n)
    (hm' : matchEvent u v (orbit u v k p₁ r T j') = true)
    (hn' : (orbit u v k p₁ r T j').1.pos + v.length = n) : j = j' :=
  matchEvent_orbit_unique hp hm hm' (by omega)

end Unique

end PalPeg.ScaMatcherAnswer
