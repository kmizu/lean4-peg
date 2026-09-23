import PalPeg.GSDecompose2
import PalPeg.MiddleBorder
import PalPeg.GSRealTime

/-!
# L1 for the per-period deletion `GSPreprocess.decompose`

`GSPreprocess.decompose` (the decomposition the head program runs, `gs_overlap.decompose`)
deletes **one least period at a time** (`stripLoop`). L1 (`GSDecomp`: `(k-1)s < |x|` and
`(k-2)s < (k-1)p₁`) was proved only for the run-skip variant `decompose2`
(`GSDecompose2.decompose2_gsDecomp`). The two functions are **not** equal (for example
`k = 4`, `x = 1010101001111010101001111010101001111010101001110`: `decompose` returns
`(2, 0, 0)` and `decompose2` returns `(1, 0, 0)`), so L1 cannot be transferred. This file
proves it directly.

## The missing step

`decompose2`'s proof needs one fact about a deletion pass: it stops before the second
period `T = p₂` (`stripLoop2_lt_second`). For run-skip deletion, every passed position still
has a `k`-repetition shorter than `T`, and `pass_stops_before_second` finishes the proof.
Per-period deletion can jump over the first position without one, so that argument fails.
Here we prove the bound by **strong induction on `T`** (`perPeriodReach_lt`):

* Along the trajectory the least period never decreases (`strip_period_ge`). Hence the
  positions with least period `P` form one block, and the block's windows glue into one
  `P`-periodic stretch `[g, b + kP)`. The block is entered at `g`, reached using only periods
  `< P` (`perPeriodReach_group`).
* Suppose a step from `b < T` with period `P < T` lands at `b + P ≥ T`. By `T`-periodicity
  the window at `b` puts a `P`-periodic prefix of length `ρ = b + kP - T ≥ (k-1)P` at
  position `0`, and `v.take P` is primitive (it is a rotation of the primitive root at `b`).
  So the hypotheses hold again at the smaller bound `P`. The induction hypothesis puts the
  block entry at `g < P`. Gluing gives the period `P` on `v.take (b + kP)`, whose length is
  at least `T + P`. This contradicts `reach_lt_add_of_periodic_window`.

The induction only needs a `T`-periodic prefix of length `(k-1)T`, not `kT`. That weaker
hypothesis is what makes the recursive call possible.

## Results

* `decompose_gsDecomp : 4 ≤ k → GSDecomp x k (decompose x k).1 …` — the unconditional L1.
* `hdec_discharged` — exactly the hypothesis `hdec` of `EndToEnd.endToEnd_*` (`k = 8`).
* `not_decOK` — the raw `MiddleBorder.DecOK (Fin 2)` is **false**. `StageOK` demands
  `KSimple … p₁ …` with `0 < p₁`, while `decompose [0] 8 = (0, 0, 0)`. The hypothesis `hOK`
  of `EndToEnd.endToEnd_*` is therefore unsatisfiable.
* `gsDecN` / `decOK_normalized` — the normalized decomposition (same shape as
  `EndToEnd2.gsDec2`, but for `decompose`) with its unconditional `StageOK`. This is the
  `decOK` field of `MiddleTapes.DecompOnTapes`.
* `decompose_deadline` / `decompose_nextLen_lt` — the two consumers listed in
  `SCA_GS_MAPPING.md` §4.5 (`prefix_verifier_deadline` and the stage shrink).
-/

set_option autoImplicit false

namespace PalPeg
namespace GSDecomposeL1

universe u
variable {α : Type u}

/-! ## §1 The per-period deletion trajectory (relational form) -/

/-- Positions of `v` reached from `0` by per-period deletion with bound `T`: from `b`, if the
least `k`-repetition period `q` of `v.drop b` is `< T`, advance to `b + q`. -/
inductive PerPeriodReach (v : List α) (k T : ℕ) : ℕ → Prop
  | start : PerPeriodReach v k T 0
  | step {b q : ℕ} : PerPeriodReach v k T b → IsLeastKRep (v.drop b) k q → q < T →
      PerPeriodReach v k T (b + q)

theorem PerPeriodReach.mono {v : List α} {k T T' : ℕ} (hTT : T ≤ T') {b : ℕ}
    (h : PerPeriodReach v k T b) : PerPeriodReach v k T' b := by
  induction h with
  | start => exact .start
  | step _ hq hqT ih => exact .step ih hq (by omega)

/-- **Block structure of the trajectory** (no periodicity assumption). If `P` is the least
period at a reached position `b`, then
* every step up to `b` used a period `≤ P` (`b` is reached with bound `P + 1`), and
* there is an entry point `g ≤ b` of the `P`-block, reached with steps `< P` only, such that
  `v[g, b + kP)` has period `P`. -/
theorem perPeriodReach_group {v : List α} {k T : ℕ} (hk : 4 ≤ k) {b : ℕ}
    (h : PerPeriodReach v k T b) :
    ∀ P, IsLeastKRep (v.drop b) k P →
      PerPeriodReach v k (P + 1) b ∧
      ∃ g, g ≤ b ∧ PerPeriodReach v k P g ∧
        HasPeriod ((v.drop g).take (b + k * P - g)) P := by
  induction h with
  | start =>
    intro P hP
    refine ⟨.start, 0, le_refl _, .start, ?_⟩
    simpa using hP.1.2.2
  | @step b q _hb hq _hqT ih =>
    intro P hP
    have hd : (v.drop b).drop q = v.drop (b + q) := by rw [List.drop_drop]
    have hqpos : 0 < q := hq.1.1
    have hqP : q ≤ P :=
      strip_period_ge hk hq.2 hqpos hq.1.2.2 hq.1.2.1 (le_refl _) (by rw [hd]; exact hP)
    obtain ⟨hreach, g, hgb, hg, hper⟩ := ih q hq
    have hlenb : k * q ≤ (v.drop b).length := hq.1.2.1
    have hlenbq : k * P ≤ (v.drop (b + q)).length := hP.1.2.1
    have hdl1 : (v.drop b).length = v.length - b := List.length_drop
    have hdl2 : (v.drop (b + q)).length = v.length - (b + q) := List.length_drop
    have hdl3 : (v.drop g).length = v.length - g := List.length_drop
    have h2q : 2 * q ≤ k * q := Nat.mul_le_mul_right q (by omega)
    have hqkq : q ≤ k * q := Nat.le_mul_of_pos_left q (by omega)
    rcases Nat.eq_or_lt_of_le hqP with heq | hlt
    · -- same period: glue the new window onto the block
      rw [← heq] at hP hlenbq ⊢
      refine ⟨.step hreach hq (by omega), g, by omega, hg, ?_⟩
      have hB : HasPeriod (((v.drop g).drop (b + q - g)).take (k * q)) q := by
        have e : (v.drop g).drop (b + q - g) = v.drop (b + q) := by
          rw [List.drop_drop]; congr 1; omega
        rw [e]; exact hP.1.2.2
      have hglue := hasPeriod_glue (w := v.drop g) (p := q) (d := b + q - g)
        (A := b + k * q - g) (B := k * q) hper hB (by omega) (by omega) (by omega)
      have e2 : b + q + k * q - g = b + q - g + k * q := by omega
      rw [e2]; exact hglue
    · -- the period grows: a new block starts at `b + q`
      refine ⟨.step (hreach.mono (by omega)) hq (by omega), b + q, le_refl _,
        .step (hreach.mono (by omega)) hq hlt, ?_⟩
      rw [show b + q + k * P - (b + q) = k * P by omega]
      exact hP.1.2.2

/-! ## §2 Rotations of a primitive root are primitive -/

/-- A length-`q` factor of a `q`-periodic word whose first block is primitive is primitive. -/
theorem primitive_drop_take_of_period {w : List α} {d q : ℕ} (hq : 0 < q)
    (hper : HasPeriod (w.take (d + q)) q) (hlen : d + q ≤ w.length)
    (hprim : Primitive (w.take q)) : Primitive ((w.drop d).take q) := by
  intro z n hzn
  by_contra hn
  have hflen : ((w.drop d).take q).length = q := by
    rw [List.length_take, List.length_drop]; omega
  have hzl : n * z.length = q := by
    have := congrArg List.length hzn
    rw [hflen, length_wpow] at this
    omega
  have hn0 : n ≠ 0 := by rintro rfl; rw [Nat.zero_mul] at hzl; omega
  have hn2 : 2 ≤ n := by omega
  have hzpos : 0 < z.length := by
    rcases Nat.eq_zero_or_pos z.length with h | h
    · rw [h, Nat.mul_zero] at hzl; omega
    · exact h
  have hzlt : z.length < q := by
    have : 2 * z.length ≤ n * z.length := Nat.mul_le_mul_right _ hn2
    omega
  have hdvd : z.length ∣ q := ⟨n, by rw [← hzl]; exact Nat.mul_comm n z.length⟩
  have hfper : HasPeriod ((w.drop d).take q) z.length := by
    rw [hzn]; exact hasPeriod_wpow z n
  have hxlen : (w.take (d + q)).length = d + q := by rw [List.length_take]; omega
  have hsuf : (w.take (d + q)).drop ((w.take (d + q)).length - q) = (w.drop d).take q := by
    rw [hxlen, show d + q - q = d by omega]
    apply List.ext_getElem?
    intro i
    by_cases hi : i < q
    · rw [List.getElem?_drop, List.getElem?_take_of_lt (show d + i < d + q by omega),
        List.getElem?_take_of_lt hi, List.getElem?_drop]
    · rw [List.getElem?_eq_none (by rw [List.length_drop, hxlen]; omega),
        List.getElem?_eq_none (by rw [List.length_take, List.length_drop]; omega)]
  have hall : HasPeriod (w.take (d + q)) z.length :=
    hasPeriod_of_suffix_gcd hper hq hdvd (by rw [hsuf]; exact hfper) (by rw [hxlen]; omega)
  have hroot : HasPeriod (w.take q) z.length := hasPeriod_take_of_le hall (by omega)
  have hrlen : (w.take q).length = q := by rw [List.length_take]; omega
  exact not_primitive_of_period hzpos (by omega) (by rw [hrlen]; exact hdvd) hroot hprim

/-! ## §3 The key lemma: a per-period pass stops before the second period -/

/-- **Per-period deletion stops before `T`.** Suppose `v.take m` has period `T`, its root
`v.take T` is primitive, and `(k-1)T ≤ m`. Then every position reached from `0` by
per-period deletion with bound `T` is `< T`. Strong induction on `T`; see the module
docstring. -/
theorem perPeriodReach_lt {k : ℕ} (hk : 4 ≤ k) : ∀ (T : ℕ) (v : List α) (m : ℕ), 0 < T →
    Primitive (v.take T) → (k - 1) * T ≤ m → m ≤ v.length → HasPeriod (v.take m) T →
    ∀ b, PerPeriodReach v k T b → b < T := by
  intro T
  induction T using Nat.strong_induction_on with
  | _ T IH =>
  intro v m hT hprim hkm hmv hperT b hb
  induction hb with
  | start => exact hT
  | @step b q hb hq hqT ihb =>
    by_contra hcon
    have hbT : b < T := ihb
    have hbq : T ≤ b + q := by omega
    have hqpos : 0 < q := hq.1.1
    have h3T : 3 * T ≤ (k - 1) * T := Nat.mul_le_mul_right T (by omega)
    have h3q : 3 * q ≤ (k - 1) * q := Nat.mul_le_mul_right q (by omega)
    have hkq1 : (k - 1) * q + q = k * q := by
      have h1 := Nat.sub_one_mul k q
      have h2 : q ≤ k * q := Nat.le_mul_of_pos_left q (by omega)
      omega
    have hlenb : k * q ≤ (v.drop b).length := hq.1.2.1
    have hdlb : (v.drop b).length = v.length - b := List.length_drop
    have hwin : HasPeriod ((v.drop b).take (k * q)) q := hq.1.2.2
    -- Step 1: the window at `b` is shorter than `q + T`, i.e. `(k-1) q < T`.
    have hkq : k * q < q + T := by
      have hrw := reach_lt_add_of_periodic_window (D := b) (rw := min (k * q) (m - b))
        hT hprim hmv (by omega) hperT hqpos hqT (by omega)
        (hasPeriod_take_of_le hwin (min_le_left _ _))
      omega
    have hbkq : b + k * q ≤ m := by omega
    -- `T`-periodicity: reading at `T` is reading at `0`
    have hshift0 : ∀ L, T + L ≤ m → (v.drop T).take L = v.take L := by
      intro L hL
      have h := drop_shift_take_eq (b := 0) (T := T) (L := L) hperT hmv (by omega)
      simpa using h
    have hdT : (v.drop b).drop (T - b) = v.drop T := by
      rw [List.drop_drop]; congr 1; omega
    -- Step 2: a `q`-periodic prefix of length `ρ = b + kq - T ≥ (k-1) q`
    set ρ := b + k * q - T with hρ
    have hρper : HasPeriod (v.take ρ) q := by
      have h1 := hasPeriod_drop_take (d := T - b) hwin hlenb (by omega)
      rw [hdT, show k * q - (T - b) = ρ by omega, hshift0 ρ (by omega)] at h1
      exact h1
    -- Step 3: `v.take q` is primitive (a rotation of the primitive root at `b`)
    have hprimq : Primitive (v.take q) := by
      have hprimb : Primitive ((v.drop b).take q) := IsLeastKRep.primitive (by omega) hq
      have hrot := primitive_drop_take_of_period (w := v.drop b) (d := T - b) hqpos
        (hasPeriod_take_of_le hwin (by omega)) (by omega) hprimb
      rw [hdT, hshift0 q (by omega)] at hrot
      exact hrot
    -- Step 4: the block of period `q` is entered before `q` (induction hypothesis)
    obtain ⟨-, g, hgb, hg, hgper⟩ := perPeriodReach_group hk hb q hq
    have hgq : g < q :=
      IH q hqT v ρ hqpos hprimq (by omega) (by omega) hρper g hg
    -- Step 5: glue; a `q`-periodic prefix of length `≥ T + q` is impossible
    have hglue := hasPeriod_glue (w := v) (p := q) (d := g) (A := ρ) (B := b + k * q - g)
      hρper hgper (by omega) (by omega) (by omega)
    rw [show g + (b + k * q - g) = b + k * q by omega] at hglue
    have hfin := reach_lt_add_of_periodic_window (D := 0) (rw := b + k * q)
      hT hprim hmv (by omega) hperT hqpos hqT (by omega) (by simpa using hglue)
    omega

section Dec

variable [DecidableEq α]

/-- `stripLoop` computes a position of the relational trajectory. -/
theorem stripLoop_reach (x : List α) (k T : ℕ) (hk : 3 ≤ k) (s : ℕ) :
    ∀ (fuel b : ℕ), PerPeriodReach (x.drop s) k T b → s + b ≤ x.length →
      ∃ b', PerPeriodReach (x.drop s) k T b' ∧ stripLoop x k T fuel (s + b) = s + b' := by
  intro fuel
  induction fuel with
  | zero => intro b hb _; exact ⟨b, hb, rfl⟩
  | succ fuel ih =>
    intro b hb hsb
    rw [stripLoop]
    rcases hfo : firstOuter (x.drop (s + b)) k T (x.length + 1) 1 with _ | ⟨p, m⟩
    · exact ⟨b, hb, rfl⟩
    · simp only []
      have hbelow : ∀ p', p' < 1 → ¬ KRep (x.drop (s + b)) k p' := by
        intro p' hp'; rintro ⟨h1, -, -⟩; omega
      obtain ⟨hleast, -⟩ :=
        firstOuter_some (x.drop (s + b)) k T hk (x.length + 1) 1 p m (by omega) hbelow hfo
      have hpT : p < T := firstOuter_lt_bound (x.drop (s + b)) k T (x.length + 1) 1 p m hfo
      have hplt := firstOuter_lt (x.drop (s + b)) k T (x.length + 1) 1 p m (by omega) hfo
      have hd : (x.drop s).drop b = x.drop (s + b) := by rw [List.drop_drop]
      have hb' : PerPeriodReach (x.drop s) k T (b + p) := .step hb (by rw [hd]; exact hleast) hpT
      have hlen : (x.drop (s + b)).length = x.length - (s + b) := List.length_drop
      obtain ⟨b', hb'', heq⟩ := ih (b + p) hb' (by omega)
      refine ⟨b', hb'', ?_⟩
      rw [show s + b + p = s + (b + p) by omega]
      exact heq

/-- **One per-period pass stops before the second period** (the `stripLoop` counterpart of
`GSDecompose2.stripLoop2_lt_second`). -/
theorem stripLoop_lt_second (x : List α) (k : ℕ) (hk : 4 ≤ k) {s T m : ℕ}
    (hs : s ≤ x.length) (hT : 0 < T) (hprim : Primitive ((x.drop s).take T))
    (hkT : (k - 1) * T ≤ m) (hm : m ≤ (x.drop s).length)
    (hperT : HasPeriod ((x.drop s).take m) T) (fuel : ℕ) :
    stripLoop x k T fuel s < s + T := by
  obtain ⟨b', hb', heq⟩ := stripLoop_reach x k T (by omega) s fuel 0 .start (by omega)
  rw [Nat.add_zero] at heq
  rw [heq]
  have := perPeriodReach_lt hk T (x.drop s) m hT hprim hkT hm hperT b' hb'
  omega

/-! ## §4 The invariant along `decomposeLoop` and L1 -/

/-- Invariant along `decomposeLoop` (same shape as `GSDecompose2.decomposeLoop2_bound`). -/
private theorem decomposeLoop_bound (x : List α) (k : ℕ) (hk : 4 ≤ k) :
    ∀ (fuel s : ℕ), s ≤ x.length → x.length ≤ fuel + s →
      ∃ d, (decomposeLoop x k fuel s).1 = s + d ∧ s + d ≤ x.length ∧
        (d = 0 ∨ ∃ T₁ Tn q, IsLeastKRep (x.drop s) k q ∧ (k - 1) * q ≤ T₁ ∧
          (k - 2) * d + T₁ ≤ (k - 1) * Tn ∧ (k - 1) * Tn + d < x.length - s ∧
          ((decomposeLoop x k fuel s).2.1 ≠ 0 → Tn ≤ (decomposeLoop x k fuel s).2.1)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro s hs hf
    refine ⟨0, ?_, by omega, Or.inl rfl⟩
    show x.length = s + 0
    omega
  | succ fuel ih =>
    intro s hs hf
    have hvlen : (x.drop s).length = x.length - s := by simp
    rcases hfp : firstPeriod (x.drop s) k with _ | ⟨p₁, m⟩
    · have heq : decomposeLoop x k (fuel + 1) s = (s, 0, 0) := by
        rw [decomposeLoop]; simp only [hfp]
      rw [heq]
      exact ⟨0, by omega, by omega, Or.inl rfl⟩
    · obtain ⟨hleast, rfl⟩ := firstPeriod_some (x.drop s) k (by omega) hfp
      have hp₁ : 0 < p₁ := hleast.1.1
      obtain ⟨r, hrdef, hrge, hreach⟩ :
          ∃ r, extendReach (x.drop s) p₁ (x.length + 1) (k * p₁) = r ∧ k * p₁ ≤ r ∧
            ReachOf (x.drop s) p₁ r := by
        obtain ⟨h1, h2⟩ := extendReach_spec (x.drop s) p₁ (x.length + 1) (k * p₁) (by omega)
          (Nat.le_mul_of_pos_left p₁ (by omega)) hleast.1.2.1 hleast.1.2.2
        exact ⟨_, rfl, h1, h2⟩
      rcases hsp : secondPeriod (x.drop s) k p₁ r with _ | p₂
      · have heq : decomposeLoop x k (fuel + 1) s = (s, p₁, r) := by
          rw [decomposeLoop]; simp only [hfp, hrdef, hsp]
        rw [heq]
        exact ⟨0, by omega, by omega, Or.inl rfl⟩
      · set s' := stripLoop x k p₂ (x.length + 1) s with hs'def
        have heq : decomposeLoop x k (fuel + 1) s = decomposeLoop x k fuel s' := by
          rw [decomposeLoop]; simp only [hfp, hrdef, hsp, hs'def]
        rw [heq]
        obtain ⟨hsec, hsecmin⟩ :=
          secondPeriod_some (x.drop s) k p₁ r p₂ (by omega) hleast hreach.2.1 hreach.1 hsp
        have hkrep₂ : KRep (x.drop s) k p₂ := kRep_of_second hsec
        have hprim : Primitive ((x.drop s).take p₂) :=
          second_primitive_of_least (by omega) hsec hsecmin
        have hle12 : p₁ ≤ p₂ := hleast.2 _ hkrep₂
        have hne12 : p₁ ≠ p₂ := fun heq2 => not_second_reach hreach (heq2 ▸ hsec)
        have hlt12 : p₁ < p₂ := lt_of_le_of_ne hle12 hne12
        have hkp : (k - 1) * p₁ ≤ p₂ :=
          kRepetition_periods (by omega) hleast.1 hkrep₂ hprim hlt12
        have hkp₂len : k * p₂ ≤ x.length - s := by
          have h1 := hsec.2.1
          have h2 : k * p₂ ≤ max (k * p₂) (r + 1) := le_max_left _ _
          omega
        have hk1 : (k - 1) * p₂ ≤ max (k * p₂) (r + 1) := by
          have h1 : (k - 1) * p₂ ≤ k * p₂ := Nat.mul_le_mul_right p₂ (by omega)
          have h2 : k * p₂ ≤ max (k * p₂) (r + 1) := le_max_left _ _
          omega
        have hs'lt : s' < s + p₂ :=
          stripLoop_lt_second x k hk hs hsec.1 hprim hk1 hsec.2.1 hsec.2.2 _
        have hs'ge : s ≤ s' := stripLoop_ge x k p₂ (x.length + 1) s
        have hs'le : s' ≤ x.length := stripLoop_le x k p₂ (x.length + 1) s hs
        have hstop : ∀ p', p' < p₂ → ¬ KRep (x.drop s') k p' :=
          stripLoop_spec x k p₂ (by omega) (x.length + 1) s hs (by omega)
        have hs'ne : s ≠ s' := fun heq2 => hstop p₁ hlt12 (heq2 ▸ hleast.1)
        obtain ⟨d', hd'eq, hd'le, hd'inv⟩ := ih s' hs'le (by omega)
        refine ⟨(s' - s) + d', by rw [hd'eq]; omega, by omega, Or.inr ?_⟩
        have hnew : ∀ q, IsLeastKRep (x.drop s') k q → p₂ ≤ q := by
          intro q hq
          by_contra hc
          exact hstop q (by omega) hq.1
        have hmul2 : (k - 2) * p₂ + p₂ = (k - 1) * p₂ := by
          rw [← Nat.succ_mul]; congr 1; omega
        have hmul1 : (k - 1) * p₂ + p₂ = k * p₂ := by
          rw [← Nat.succ_mul]; congr 1; omega
        have hma : (k - 2) * (s' - s) ≤ (k - 2) * p₂ :=
          Nat.mul_le_mul_left (k - 2) (by omega)
        rcases hd'inv with h0 | ⟨T₁', Tn', q', hq', hq'T, hsum', hlast', hTn'⟩
        · subst h0
          simp only [Nat.add_zero]
          refine ⟨p₂, p₂, p₁, hleast, hkp, by omega, by omega, ?_⟩
          intro hne
          refine hnew _ ?_
          have hL := (decomposeLoop_spec x k (by omega) fuel s' hs'le).least hne
          rwa [hd'eq, Nat.add_zero] at hL
        · refine ⟨p₂, Tn', p₁, hleast, hkp, ?_, ?_, hTn'⟩
          · have h4 : (k - 1) * p₂ ≤ (k - 1) * q' := Nat.mul_le_mul_left (k - 1) (hnew q' hq')
            have h5 : (k - 2) * ((s' - s) + d') = (k - 2) * (s' - s) + (k - 2) * d' := by ring
            omega
          · omega

/-- **Main theorem (unconditional L1 for the per-period deletion).** The output of
`GSPreprocess.decompose x k` is a `GSDecomp`, including the two L1 bounds
`(k-1)s < |x|` and `(k-2)s < (k-1)p₁`. -/
theorem decompose_gsDecomp {k : ℕ} (hk : 4 ≤ k) (x : List α) :
    GSDecomp x k (decompose x k).1 (decompose x k).2.1 (decompose x k).2.2 := by
  have H : GSCore x k (decompose x k).1 (decompose x k).2.1 (decompose x k).2.2 :=
    decompose_spec x k (by omega)
  have hdec : decompose x k = decomposeLoop x k (x.length + 1) 0 := rfl
  obtain ⟨d, hd, hdle, hinv⟩ := decomposeLoop_bound x k hk (x.length + 1) 0
    (Nat.zero_le _) (by omega)
  rw [← hdec] at hd hinv
  have hs : (decompose x k).1 = d := by omega
  rcases hinv with h0 | ⟨T₁, Tn, q, hq, hqT, hsum, hlast, hTn⟩
  · subst h0
    rw [hs] at H ⊢
    exact gsDecomp_of_core_zero (by omega) H
  · have hqpos : 0 < q := hq.1.1
    have hT₁pos : 0 < T₁ := by
      have : k - 1 ≤ (k - 1) * q := Nat.le_mul_of_pos_right (k - 1) hqpos
      omega
    have hks : (k - 2) * d + d = (k - 1) * d := by
      rw [← Nat.succ_mul]; congr 1; omega
    refine ⟨H, ?_, ?_⟩
    · intro _; rw [hs]; omega
    · intro hne
      rw [hs]
      have hle := Nat.mul_le_mul_left (k - 1) (hTn hne)
      omega

/-! ## §5 Discharging the consumers -/

/-- **`hdec` of `EndToEnd.endToEnd_correct` / `endToEnd_mem_PAL` / `endToEnd_round_cost`**
(`EndToEnd.lean:20,32,45`), verbatim. -/
theorem hdec_discharged : ∀ x : List (Fin 2), GSDecomp x 8 (decompose x 8).1
    (decompose x 8).2.1 (decompose x 8).2.2 :=
  fun x => decompose_gsDecomp (by decide) x

/-- The two facts the verifier deadline needs (`SCA_GS_MAPPING.md` §4.2/§4.5):
`3s < |x|` and `s < 2p₁`, for every `k ≥ 4` (in particular the head program's `k = 8`). -/
theorem decompose_three_mul_cut_lt {k : ℕ} (hk : 4 ≤ k) {x : List α} (hx : x ≠ []) :
    3 * (decompose x k).1 < x.length := by
  have h := (decompose_gsDecomp hk x).cut_bound hx
  have : 3 * (decompose x k).1 ≤ (k - 1) * (decompose x k).1 :=
    Nat.mul_le_mul_right _ (by omega)
  omega

theorem decompose_cut_lt_two_period {k : ℕ} (hk : 4 ≤ k) (x : List α)
    (hp : (decompose x k).2.1 ≠ 0) : (decompose x k).1 < 2 * (decompose x k).2.1 := by
  have h := (decompose_gsDecomp hk x).cut_period_bound hp
  set s := (decompose x k).1
  set p := (decompose x k).2.1
  by_contra hcon
  have h1 : (k - 2) * (2 * p) ≤ (k - 2) * s := Nat.mul_le_mul_left (k - 2) (by omega)
  have h2 : (k - 1) * p ≤ (k - 2) * (2 * p) := by
    have e : (k - 2) * (2 * p) = (2 * (k - 2)) * p := by ring
    rw [e]; exact Nat.mul_le_mul_right p (by omega)
  omega

/-- **`prefix_verifier_deadline` (GSRealTime.lean:440) instantiated with `decompose`**:
the arithmetic deadline of the prefix check holds for the decomposition the head runs. -/
theorem decompose_deadline {k : ℕ} (hk : 4 ≤ k) (x : List α)
    (hp : (decompose x k).2.1 ≠ 0) {q : ℕ} (hq : q ≤ (x.drop (decompose x k).1).length) :
    (x.take (decompose x k).1).length
      < 2 * ((x.drop (decompose x k).1).length
        - gsNextQ k (decompose x k).2.1 (decompose x k).2.2 q) := by
  have H := decompose_gsDecomp hk x
  have hx : x ≠ [] := by
    have hK := (H.least hp).1
    have hkp : 0 < k * (decompose x k).2.1 := Nat.mul_pos (by omega) hK.1
    have hl : (x.drop (decompose x k).1).length = x.length - (decompose x k).1 :=
      List.length_drop
    have := hK.2.1
    exact List.ne_nil_of_length_pos (by omega)
  have hcut := H.cut_le
  have hts : (x.take (decompose x k).1).length = (decompose x k).1 := by
    rw [List.length_take]; omega
  refine prefix_verifier_deadline (by omega) (Nat.pos_of_ne_zero hp) ?_ ?_ hq
  · rw [List.take_append_drop, hts]; exact H.cut_bound hx
  · rw [hts]; exact H.cut_period_bound hp

/-- The flag stages shrink: `nextLen s < |x|` (`BorderJob.nextLen_lt`), so
`border_controller` terminates. -/
theorem decompose_nextLen_lt {k : ℕ} (hk : 4 ≤ k) {x : List α} (hx : x ≠ []) :
    nextLen (decompose x k).1 < x.length :=
  nextLen_lt hk ((decompose_gsDecomp hk x).cut_bound hx)

end Dec

/-! ### The raw `DecOK` is false; the normalized one is a theorem -/

/-- **`MiddleBorder.DecOK (Fin 2)` is false.** `StageOK` asks for `KSimple … p₁ …`, whose
first field is `0 < p₁`. But `decompose [0] 8 = (0, 0, 0)` has `p₁ = 0`, which is how
`decompose` encodes "no period". So the hypothesis `hOK` of the `EndToEnd.endToEnd_*`
theorems cannot be satisfied, and those theorems are vacuous. -/
theorem not_decOK : ¬ MiddleBorder.DecOK (Fin 2) := by
  intro h
  have h1 := (h [0] 1 le_rfl).ksimple.period_pos
  have h2 : (MiddleBorder.gsDec ([0] : List (Fin 2)) 8 1).2.1 = 0 := by decide
  omega

section Norm

variable {β : Type} [DecidableEq β]

/-- `MiddleBorder.gsDec`, normalized in the no-period case `p₁ = 0`: return
`(s, |v|+1, 0)`, as `EndToEnd2.gsDec2` does for `decompose2`. The cut `s` and every
`p₁ ≠ 0` output are unchanged. -/
def gsDecN (y : List β) (k : ℕ) : ℕ → ℕ × ℕ × ℕ := fun L =>
  if (decompose (y.take L) k).2.1 = 0 then
    ((decompose (y.take L) k).1, ((y.take L).drop (decompose (y.take L) k).1).length + 1, 0)
  else decompose (y.take L) k

theorem gsDecN_fst (y : List β) (k L : ℕ) :
    (gsDecN y k L).1 = (MiddleBorder.gsDec y k L).1 := by
  simp only [gsDecN, MiddleBorder.gsDec]; split_ifs <;> rfl

theorem gsDecN_of_ne (y : List β) (k L : ℕ) (hp : (MiddleBorder.gsDec y k L).2.1 ≠ 0) :
    gsDecN y k L = MiddleBorder.gsDec y k L := by
  simp only [MiddleBorder.gsDec] at hp
  simp only [gsDecN, MiddleBorder.gsDec, if_neg hp]

/-- **Unconditional stage correctness for `decompose`** at any `k ≥ 4`: the `StageOK`
(`BorderJob.lean:625`) for the normalized decomposition. -/
theorem stageOK_decompose {k : ℕ} (hk : 4 ≤ k) (y : List β) (L : ℕ) (hL : 1 ≤ L) :
    StageOK y k L (gsDecN y k L).1 (gsDecN y k L).2.1 (gsDecN y k L).2.2 := by
  set x := y.take L with hx
  have hxL : x.length ≤ L := by simp [hx, List.length_take]
  have H := decompose_gsDecomp hk x
  set s := (decompose x k).1 with hs
  have hcut : s ≤ x.length := H.cut_le
  have hne : x.length = 0 → s = 0 := by intro h; omega
  have hpos : 0 < x.length → (k - 1) * s < x.length := by
    intro h
    have hx0 : x ≠ [] := by
      intro hc; rw [hc] at h; simp at h
    exact H.cut_bound hx0
  have hshort : (k - 1) * s < L := by
    rcases Nat.eq_zero_or_pos x.length with h0 | h0
    · have h00 := hne h0; rw [h00, Nat.mul_zero]; omega
    · have := hpos h0; omega
  have hdlen : (x.drop s).length = x.length - s := List.length_drop
  have hsle : s ≤ (k - 1) * s := Nat.le_mul_of_pos_left s (by omega)
  have h3s : 3 * s ≤ (k - 1) * s := Nat.mul_le_mul_right s (by omega)
  simp only [gsDecN, ← hx, ← hs]
  split_ifs with hp
  · refine ⟨by omega, H.toGSCore.ksimple_none hp, ?_, hshort⟩
    show s ≤ k * ((x.drop s).length + 1)
    have : (x.drop s).length + 1 ≤ k * ((x.drop s).length + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    rcases Nat.eq_zero_or_pos x.length with h0 | h0
    · have := hne h0; omega
    · have := hpos h0; omega
  · exact ⟨by omega, H.ksimple hp, cut_charge_of_ratio hk (H.cut_period_bound hp), hshort⟩

/-- **The `DecOK` form at `k = 8`** (`MiddleBorder.lean:43`, and the `decOK` field of
`MiddleTapes.DecompOnTapes`), for the normalized `decompose`. -/
theorem decOK_normalized (y : List β) (L : ℕ) (hL : 1 ≤ L) :
    StageOK y 8 L (gsDecN y 8 L).1 (gsDecN y 8 L).2.1 (gsDecN y 8 L).2.2 :=
  stageOK_decompose (by decide) y L hL

/-- The raw `DecOK` holds exactly off the no-period case: whenever the raw
`gsDec y 8 L` has `p₁ ≠ 0`, it is `StageOK`. -/
theorem decOK_of_period (y : List β) (L : ℕ) (hL : 1 ≤ L)
    (hp : (MiddleBorder.gsDec y 8 L).2.1 ≠ 0) :
    StageOK y 8 L (MiddleBorder.gsDec y 8 L).1 (MiddleBorder.gsDec y 8 L).2.1
      (MiddleBorder.gsDec y 8 L).2.2 := by
  rw [← gsDecN_of_ne y 8 L hp]
  exact decOK_normalized y L hL

end Norm

end GSDecomposeL1
end PalPeg
