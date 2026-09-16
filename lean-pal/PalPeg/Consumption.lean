import PalPeg.PassSum11
import PalPeg.PassSumGen

/-!
# Unconditional consumption for `k = 8`

`consumption_eight` proves `Consumption x 8 b` for arbitrary alphabets.
The proof uses the executable loop's pointwise coverage of consumed positions.
If it consumed a full parent period, that interval would contain a position
congruent to the parent's start. Its small power fits inside the parent run and
copies back to the start, contradicting the parent's least-power period.

No late-UP hypothesis, experimental bound, or external periodicity theorem is
assumed. The final corollaries discharge both period-sum formulations.
-/

namespace PalPeg.PassSum10

variable {α : Type*} [DecidableEq α]

/-- A finite prefix of the very same loop used by `segExit`. -/
inductive SegPath (x : List α) (k b L : ℕ) : ℕ → ℕ → Prop
  | refl (s) : SegPath x k b L s s
  | step {s t q m} :
      firstOuter (x.drop s) k b (x.length + 1) 1 = some (q, m) →
      segEnd x k s q ≤ L →
      SegPath x k b L (nextPos x k s q) t → SegPath x k b L s t

/-- Executing any finite amount of fuel gives such a path. -/
theorem segExit_path (x : List α) (k b L : ℕ) :
    ∀ fuel s, SegPath x k b L s (segExit x k b L fuel s) := by
  intro fuel
  induction fuel with
  | zero => intro s; exact .refl s
  | succ fuel ih =>
    intro s
    rcases hf : firstOuter (x.drop s) k b (x.length + 1) 1 with _ | ⟨q, m⟩
    · simpa only [segExit, hf] using (SegPath.refl (x := x) (k := k) (b := b) (L := L) s)
    · by_cases hL : segEnd x k s q ≤ L
      · simpa only [segExit, hf, if_pos hL] using (SegPath.step hf hL (ih _))
      · simpa only [segExit, hf, if_neg hL] using
          (SegPath.refl (x := x) (k := k) (b := b) (L := L) s)

/-- Every position skipped by one loop step still starts a `k`-power
of that step's period. The strict endpoint is essential. -/
theorem step_covers_krep (x : List α) (k b : ℕ) (hk : 3 ≤ k)
    {s q m v : ℕ} (hs : s ≤ x.length)
    (hf : firstOuter (x.drop s) k b (x.length + 1) 1 = some (q, m))
    (hsv : s ≤ v) (hv : v < nextPos x k s q) : KRep (x.drop v) k q := by
  obtain ⟨hq, _, hkr, hR⟩ := stripLoop2_step_data x k b hk hs hf
  let r := extendReach (x.drop s) q (x.length + 1) (k * q)
  have hr : r ≤ x.length - s := by simpa [r] using hR.1
  have hkr' : k * q ≤ r := hkr
  have hd : nextPos x k s q = s + (r - k * q + 1) := rfl
  have hshift : (x.drop s).drop (v - s) = x.drop v := by
    rw [List.drop_drop]; congr 1; omega
  refine ⟨hq.1.1, by simp only [List.length_drop]; omega, ?_⟩
  have hper := hasPeriod_drop_take hR.2.1 hR.1 (show v - s ≤ r by omega)
  rw [hshift] at hper
  exact hasPeriod_take_of_le hper (by omega)

/-- A path covers every intervening position by one of its actual steps. -/
theorem SegPath.covers {x : List α} {k b L s t : ℕ} (hpath : SegPath x k b L s t)
    (hk : 3 ≤ k) (hs : s ≤ x.length) {v : ℕ} (hsv : s ≤ v) (hvt : v < t) :
    ∃ u q m, s ≤ u ∧ u ≤ v ∧ v < nextPos x k u q ∧ u ≤ x.length ∧
      firstOuter (x.drop u) k b (x.length + 1) 1 = some (q, m) ∧
      segEnd x k u q ≤ L := by
  induction hpath with
  | refl => omega
  | @step s t q m hf hL hpath ih =>
    by_cases hvn : v < nextPos x k s q
    · exact ⟨s, q, m, le_rfl, hsv, hvn, hs, hf, hL⟩
    · obtain ⟨u, q', m', hnu, huv, hvn', hu, hf', hL'⟩ :=
        ih (nextPos_le x k b hk hs hf) (by omega) hvt
      exact ⟨u, q', m', le_trans (Nat.le_of_lt (nextPos_gt x k b hk hs hf)) hnu,
        huv, hvn', hu, hf', hL'⟩

/-- A loop which crosses a boundary has an actual first crossing step.
The witness is selected from the executable loop, not an arbitrary inner run. -/
theorem segExit_crossing (x : List α) (k b L B : ℕ) (hk : 3 ≤ k) :
    ∀ fuel s, s ≤ x.length → s < B → B ≤ segExit x k b L fuel s →
      ∃ u q m, s ≤ u ∧ u < B ∧ u ≤ x.length ∧
        firstOuter (x.drop u) k b (x.length + 1) 1 = some (q, m) ∧
        segEnd x k u q ≤ L ∧ B ≤ nextPos x k u q ∧ SegPath x k b L s u := by
  intro fuel
  induction fuel with
  | zero => intro s hs hB he; simp only [segExit] at he; omega
  | succ fuel ih =>
    intro s hs hB he
    rcases hf : firstOuter (x.drop s) k b (x.length + 1) 1 with _ | ⟨q, m⟩
    · simp only [segExit, hf] at he; omega
    · by_cases hL : segEnd x k s q ≤ L
      · simp only [segExit, hf, if_pos hL] at he
        by_cases hn : B ≤ nextPos x k s q
        · exact ⟨s, q, m, le_rfl, hB, hs, hf, hL, hn, .refl s⟩
        · obtain ⟨u, q', m', hu, hBu, hux, hf', hL', hn', hpath⟩ :=
            ih _ (nextPos_le x k b hk hs hf) (by omega) he
          exact ⟨u, q', m', le_trans (Nat.le_of_lt (nextPos_gt x k b hk hs hf)) hu,
            hBu, hux, hf', hL', hn', .step hf hL hpath⟩
      · simp only [segExit, hf, if_neg hL] at he; omega

/-- Failure of consumption yields a first step crossing the parent's period.
In particular its start is still strictly before the boundary. -/
theorem consumption_failure_crossing (x : List α) (k b : ℕ) (hk : 3 ≤ k)
    {s p m : ℕ} (hs : s ≤ x.length)
    (hf : firstOuter (x.drop s) k b (x.length + 1) 1 = some (p, m))
    (hfail : p ≤ subExit x k b s p - nextPos x k s p) :
    ∃ u q m', nextPos x k s p ≤ u ∧ u < nextPos x k s p + p ∧
      u ≤ x.length ∧
      firstOuter (x.drop u) k b (x.length + 1) 1 = some (q, m') ∧
      segEnd x k u q ≤ segEnd x k s p ∧
      nextPos x k s p + p ≤ nextPos x k u q ∧
      SegPath x k b (segEnd x k s p) (nextPos x k s p) u := by
  have hp := (stripLoop2_step_data x k b hk hs hf).1.1.1
  have hn := nextPos_le x k b hk hs hf
  have he := segExit_ge x k b (segEnd x k s p) hk (x.length + 1) _ hn
  exact segExit_crossing x k b (segEnd x k s p) (nextPos x k s p + p) hk
    (x.length + 1) _ hn (by omega) (by dsimp [subExit] at hfail ⊢; omega)

/-- Every inner step has period strictly smaller than the parent's period,
even when its start was reached through multiple intervening steps. -/
theorem inner_step_period_bound (x : List α) (k b : ℕ) (hk : 4 ≤ k)
    {s p m u q m' : ℕ} (hs : s ≤ x.length) (hu : u ≤ x.length)
    (hf : firstOuter (x.drop s) k b (x.length + 1) 1 = some (p, m))
    (hf' : firstOuter (x.drop u) k b (x.length + 1) 1 = some (q, m'))
    (hstart : nextPos x k s p ≤ u)
    (hfit : segEnd x k u q ≤ segEnd x k s p) : (k - 1) * q < p := by
  obtain ⟨hp, _, hkr, hR⟩ := stripLoop2_step_data x k b (by omega) hs hf
  obtain ⟨hq, _, hkq, _⟩ := stripLoop2_step_data x k b (by omega) hu hf'
  have hd := nextPos_gt x k b (by omega) hs hf
  have hdrop : (x.drop s).drop (u - s) = x.drop u := by
    rw [List.drop_drop]; congr 1; omega
  have hqshift : IsLeastKRep ((x.drop s).drop (u - s)) k q := by
    rw [hdrop]; exact hq
  have hfit' : (u - s) + k * q ≤
      extendReach (x.drop s) p (x.length + 1) (k * p) := by
    dsimp [segEnd] at hfit; omega
  have hprod : k * q < k * p := by
    dsimp [nextPos] at hstart; omega
  have hqp : q < p := (Nat.mul_lt_mul_left (by omega : 0 < k)).mp hprod
  exact child_period_bound hk hp hR hkr hqshift hfit' (by omega)

/-- Consuming a complete period would cover every position of that period
by a small `k`-power. This forgets the execution schedule only after obtaining
the pointwise covering property from the actual path. -/
theorem consumption_failure_cover (x : List α) (k b : ℕ) (hk : 4 ≤ k)
    {s p m : ℕ} (hs : s ≤ x.length)
    (hf : firstOuter (x.drop s) k b (x.length + 1) 1 = some (p, m))
    (hfail : p ≤ subExit x k b s p - nextPos x k s p) :
    ∀ v, nextPos x k s p ≤ v → v < nextPos x k s p + p →
      ∃ q, (k - 1) * q < p ∧ KRep (x.drop v) k q := by
  intro v hv hvp
  have hn := nextPos_le x k b (by omega) hs hf
  have he := segExit_ge x k b (segEnd x k s p) (by omega) (x.length + 1) _ hn
  have hve : v < subExit x k b s p := by
    dsimp [subExit] at hfail ⊢; omega
  obtain ⟨u, q, m', hnu, huv, hvnext, hu, hf', hfit⟩ :=
    (segExit_path x k b (segEnd x k s p) (x.length + 1) (nextPos x k s p)).covers
      (by omega) hn hv hve
  exact ⟨q, inner_step_period_bound x k b hk hs hu hf hf' hnu hfit,
    step_covers_krep x k b (by omega) hu hf' huv hvnext⟩

/-- A crossing witness must be late. This uses the executable run's true
maximal reach and does not assume the exact-threshold equality from
`shortRun_iff_late`. -/
theorem crossing_is_late (x : List α) (k b : ℕ) (hk : 4 ≤ k)
    {s p m u q m' : ℕ} (hs : s ≤ x.length) (hu : u ≤ x.length)
    (hf : firstOuter (x.drop s) k b (x.length + 1) 1 = some (p, m))
    (hf' : firstOuter (x.drop u) k b (x.length + 1) 1 = some (q, m'))
    (hstart : nextPos x k s p ≤ u)
    (hfit : segEnd x k u q ≤ segEnd x k s p)
    (hcross : nextPos x k s p + p ≤ nextPos x k u q) :
    (k - 1) * q < p ∧ (k - 1) * q ≤ u - nextPos x k s p := by
  obtain ⟨hp, _, hkr, hR⟩ := stripLoop2_step_data x k b (by omega) hs hf
  obtain ⟨hq, _, hkq, hQ⟩ := stripLoop2_step_data x k b (by omega) hu hf'
  let r := extendReach (x.drop s) p (x.length + 1) (k * p)
  let r' := extendReach (x.drop u) q (x.length + 1) (k * q)
  have hd : nextPos x k s p = s + (r - k * p + 1) := rfl
  have hd' : nextPos x k u q = u + (r' - k * q + 1) := rfl
  have hfit' : u + r' ≤ s + r := hfit
  have hkr' : k * p ≤ r := hkr
  have hkq' : k * q ≤ r' := hkq
  have hprod : k * q < k * p := by omega
  have hqp : q < p := (Nat.mul_lt_mul_left (by omega : 0 < k)).mp hprod
  have hdrop : (x.drop s).drop (u - s) = x.drop u := by
    rw [List.drop_drop]; congr 1; omega
  have hqshift : IsLeastKRep ((x.drop s).drop (u - s)) k q := by
    rw [hdrop]; exact hq
  have hsmall := child_period_bound hk hp hR hkr hqshift (by omega) (by omega)
  have hshort : r' < p + q := by
    by_contra hn
    apply PassSum11.far_crossing_contradiction hp hR hq.1.1 hqp
      (s := u - s) (r' := r')
    · rw [hdrop]; exact hQ.2.1
    · omega
    · omega
    · omega
  have hmul : (k - 1) * q + q = k * q := by
    rw [← Nat.succ_mul]; congr 1; omega
  exact ⟨hsmall, by omega⟩

/-- Every counterexample to Consumption supplies a genuine inner crossing
whose period is small and whose start is late. No exact-threshold assumption
on its run end is needed. The final proof below excludes counterexamples
using the stronger pointwise cover, without analyzing late crossings. -/
theorem not_consumption_witness (x : List α) (k b : ℕ) (hk : 4 ≤ k)
    (hfail : ¬ Consumption x k b) :
    ∃ s p m u q m', s ≤ x.length ∧
      firstOuter (x.drop s) k b (x.length + 1) 1 = some (p, m) ∧
      nextPos x k s p ≤ u ∧ u < nextPos x k s p + p ∧ u ≤ x.length ∧
      firstOuter (x.drop u) k b (x.length + 1) 1 = some (q, m') ∧
      segEnd x k u q ≤ segEnd x k s p ∧
      nextPos x k s p + p ≤ nextPos x k u q ∧
      (k - 1) * q < p ∧ (k - 1) * q ≤ u - nextPos x k s p ∧
      SegPath x k b (segEnd x k s p) (nextPos x k s p) u := by
  simp only [Consumption, not_forall, not_lt] at hfail
  obtain ⟨s, p, m, hs, hf, hfail⟩ := hfail
  obtain ⟨u, q, m', hstart, hbefore, hu, hf', hfit, hcross, hpath⟩ :=
    consumption_failure_crossing x k b (by omega) hs hf hfail
  obtain ⟨hsmall, hlate⟩ := crossing_is_late x k b hk hs hu hf hf' hstart hfit hcross
  exact ⟨s, p, m, u, q, m', hs, hf, hstart, hbefore, hu, hf', hfit, hcross,
    hsmall, hlate, hpath⟩

omit [DecidableEq α] in
/-- Within a periodic region, a factor at a multiple of the period is a
copy of the prefix. Both factors must fit in the region. -/
theorem factor_eq_prefix_of_mod_zero {w : List α} {p r t n : ℕ}
    (hper : HasPeriod (w.take r) p) (hr : r ≤ w.length)
    (ht : t % p = 0) (hfit : t + n ≤ r) : (w.drop t).take n = w.take n := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < n
  · rw [List.getElem?_take_of_lt hi, List.getElem?_take_of_lt hi, List.getElem?_drop]
    have ha := hasPeriod_getElem?_mod hper
      (show t + i < (w.take r).length by rw [List.length_take]; omega)
    have hb := hasPeriod_getElem?_mod hper
      (show i < (w.take r).length by rw [List.length_take]; omega)
    have hm : (t + i) % p = i % p := by simp [Nat.add_mod, ht]
    rw [hm] at ha
    have he := ha.symm.trans hb
    simpa only [List.getElem?_take_of_lt (show t + i < r by omega),
      List.getElem?_take_of_lt (show i < r by omega)] using he
  · rw [List.getElem?_eq_none (by rw [List.length_take, List.length_drop]; omega),
      List.getElem?_eq_none (by rw [List.length_take]; omega)]

/-- The consumption bound, with no hypothesis about the execution tree.
If a full parent period were consumed, the pointwise cover would include
the parent's original phase. Copying its small power back to the parent
prefix contradicts the parent's least-period property. -/
theorem consumption_eight (x : List α) (b : ℕ) : Consumption x 8 b := by
  intro s p m hs hf
  by_contra hn
  have hfail : p ≤ subExit x 8 b s p - nextPos x 8 s p := by omega
  obtain ⟨hp, _, hkr, hR⟩ := stripLoop2_step_data x 8 b (by omega) hs hf
  have hpos : 0 < p := hp.1.1
  let r := extendReach (x.drop s) p (x.length + 1) (8 * p)
  have hkr' : 8 * p ≤ r := hkr
  have hquot : 8 ≤ r / p := (Nat.le_div_iff_mul_le hpos).2 hkr'
  let t := (r / p - 7) * p
  have hrem : r % p < p := Nat.mod_lt r hpos
  have ht : t + 7 * p + r % p = r := by
    dsimp [t]
    rw [Nat.sub_mul]
    have hdiv := Nat.mod_add_div r p
    rw [Nat.mul_comm p (r / p)] at hdiv
    have h7 : 7 * p ≤ (r / p) * p := Nat.mul_le_mul_right p (by omega)
    omega
  have hd : nextPos x 8 s p = s + (r - 8 * p + 1) := rfl
  obtain ⟨q, hsmall, hq⟩ := consumption_failure_cover x 8 b (by omega) hs hf hfail
    (s + t) (by omega) (by omega)
  simp only [Nat.reduceSub] at hsmall
  have hfit : t + 8 * q ≤ r := by omega
  have htmod : t % p = 0 := by simp [t]
  have hcopy := factor_eq_prefix_of_mod_zero hR.2.1 hR.1 htmod hfit
  have hshift : (x.drop s).drop t = x.drop (s + t) := by rw [List.drop_drop]
  have hper : HasPeriod ((x.drop s).take (8 * q)) q := by
    rw [← hcopy, hshift]
    exact hq.2.2
  have hlen : 8 * q ≤ (x.drop s).length := le_trans (by omega) hR.1
  have hmin := hp.2 q ⟨hq.1, hlen, hper⟩
  omega

/-- Unconditional period-sum bound over an arbitrary alphabet. -/
theorem passPeriodSumGen_eight : PassSumGen.PassPeriodSumGen α 8 2 :=
  PassSumGen.passPeriodSumGen_of_consumption consumption_eight

/-- The original binary-alphabet period-sum obligation is discharged. -/
theorem passPeriodSum_eight : EndToEnd2.PassPeriodSum 8 2 :=
  passPeriodSum_eight_of_consumption consumption_eight

end PalPeg.PassSum10

/-- info: 'PalPeg.PassSum10.not_consumption_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PalPeg.PassSum10.not_consumption_witness

/-- info: 'PalPeg.PassSum10.consumption_failure_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PalPeg.PassSum10.consumption_failure_cover

/-- info: 'PalPeg.PassSum10.consumption_eight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PalPeg.PassSum10.consumption_eight

/-- info: 'PalPeg.PassSum10.passPeriodSumGen_eight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PalPeg.PassSum10.passPeriodSumGen_eight

/-- info: 'PalPeg.PassSum10.passPeriodSum_eight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PalPeg.PassSum10.passPeriodSum_eight
