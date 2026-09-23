import PalPeg.ScaWindowFault

/-!
# The controller's plumbing: middle bits and clean ticks from the flag workers' promise

A stage born at tick `b` with half `S` releases flag job `r` (`r < 4`) at tick `b + (r+1)S`,
into batch `r`; batch `r` is popped, one bit per tick, during interval `r + 2`, i.e. at ticks
`b + (r+2)S, …, b + (r+3)S - 1`. The flag worker promises (`FlagsContract`) that job `r` is
captured at some tick `cap r` before the next release, is not done before, and is done at
`cap r` with the job's bits: the palindrome bits of the middles `W[b, b + rS + j)`, `j < S`.

`JobInv` describes a stage's fields after `d` ticks of its life in terms of the word and the
capture ticks; `jobInv_step` / `jobInv_birth` carry it through a tick and show that the tick
raises no controller violation.
-/
set_option autoImplicit false
namespace PalPeg.ScaWindowPlumbing
open PalPeg.ScaWindowPal PalPeg.ScaWindowSchedule

/-! ## Jobs -/

/-- The bits of job `r` of the stage born at `b` with half `S`: whether the middle
`W[b, b + rS + j)` is a palindrome, for `j < S`, top of the flag stack first. -/
def jobBits (W : List (Fin 2)) (b S r : ℕ) : List Bool :=
  (List.range S).map fun j => ((W.drop b).take (r * S + j)).reverse == (W.drop b).take (r * S + j)

@[simp] theorem length_jobBits (W : List (Fin 2)) (b S r : ℕ) : (jobBits W b S r).length = S := by
  simp [jobBits]

theorem getD_jobBits (W : List (Fin 2)) (b S r : ℕ) {j : ℕ} (hj : j < S) :
    (jobBits W b S r).getD j false = true ↔ IsPal ((W.drop b).take (r * S + j)) := by
  simp only [jobBits, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, beq_iff_eq, IsPal]

/-! ## `advance` of a live stage, in closed form -/

/-- The boundary test of `advance` on a live stage is `(d + 1) % S = 0`. -/
theorem bnd_eq {st : StageState} {S d : ℕ} (hS : 1 ≤ S) (h : StageAt st S d) :
    (st.alive && (if st.alive then st.clock.pred else st.clock) == 0) = decide ((d + 1) % S = 0) := by
  obtain ⟨ha, -, hc, -⟩ := h
  obtain ⟨q, m, hm, rfl⟩ : ∃ q m, m < S ∧ d = q * S + m :=
    ⟨d / S, d % S, Nat.mod_lt _ (by omega), by rw [Nat.div_add_mod' d S]⟩
  have hmod : (q * S + m) % S = m := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hm]
  simp only [ha, if_true, Bool.true_and, hc, hmod, Nat.pred_eq_sub_one]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  rcases Nat.lt_or_ge (m + 1) S with hl | hl
  · have h1 : (q * S + m + 1) % S = m + 1 := by
      rw [Nat.add_assoc, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]
    rw [h1]; omega
  · have hmS : m + 1 = S := by omega
    have h1 : (q * S + m + 1) % S = 0 := by
      rw [Nat.add_assoc, hmS, show q * S + S = (q + 1) * S by ring, Nat.mul_mod_left]
    rw [h1]; omega

/-- `advance` of a live stage off a boundary: only the clock moves. -/
theorem advance_off {st : StageState} {S d : ℕ} (hS : 1 ≤ S) (h : StageAt st S d)
    (hb : (d + 1) % S ≠ 0) (src : ℕ) :
    advance st false src =
      ({ st with clock := st.clock.pred, birth := false, release := false }, false) := by
  have hbnd := bnd_eq hS h
  have hb' : (st.alive && (if st.alive then st.clock.pred else st.clock) == 0) = false := by
    rw [hbnd]; simpa using hb
  obtain ⟨ha, -, -, -⟩ := h
  unfold advance
  simp only [ha, if_true] at hb' ⊢
  simp only [hb', Bool.false_and, if_false, Bool.or_false, Bool.not_false,
    Bool.and_true, Bool.false_eq_true]

/-- Whether a boundary into interval `iv` is a release. -/
def relOf (iv : Fin 7) : Bool := iv.val == 1 || iv.val == 2 || iv.val == 3 || iv.val == 4

/-- `advance` of a live stage on a boundary: the interval moves on, a release when it is `1..4`. -/
theorem advance_on {st : StageState} {S d : ℕ} (hS : 1 ≤ S) (h : StageAt st S d)
    (hb : (d + 1) % S = 0) (src : ℕ) :
    advance st false src =
      ({ st with
          clock := st.half
          interval := incInterval st.interval
          alive := !((incInterval st.interval).val == 6)
          batch := if relOf (incInterval st.interval) then batchOfInterval (incInterval st.interval)
            else st.batch
          birth := false
          release := relOf (incInterval st.interval) },
        relOf (incInterval st.interval) && st.pending) := by
  have hbnd := bnd_eq hS h
  have hb' : (st.alive && (if st.alive then st.clock.pred else st.clock) == 0) = true := by
    rw [hbnd]; simpa using hb
  obtain ⟨ha, -, -, -⟩ := h
  unfold advance
  simp only [ha, if_true] at hb' ⊢
  simp only [hb', if_true, Bool.true_and, Bool.or_false, Bool.not_false,
    Bool.and_true, Bool.false_eq_true, if_false, relOf]
  simp

/-! ## `consume` and `capture` -/

theorem consume_not (t : StageState) (h : answering t = false) :
    consume t = ({ t with middle := false }, false) := by
  unfold consume
  simp only [h]
  split
  · rename_i x
    cases h2 : t.results ⟨t.interval.val - 2, by omega⟩ <;> simp [popFlag, h2]
  · simp [popFlag]

theorem consume_ans (t : StageState) (r : Fin 4) (hans : answering t = true)
    (hr : t.interval.val = r.val + 2) :
    consume t = ({ t with
      middle := (t.results r).headD false
      results := Function.update t.results r (t.results r).tail }, (t.results r).isEmpty) := by
  unfold consume
  simp only [hans]
  rw [dif_pos (by omega)]
  have hr' : (⟨t.interval.val - 2, by omega⟩ : Fin 4) = r := Fin.ext (by simp; omega)
  simp only [hr']
  rcases hl : t.results r with _ | ⟨b, rest⟩
  · simp only [popFlag, Bool.true_and, List.headD_nil, List.tail_nil, List.isEmpty_nil]
    refine Prod.ext ?_ rfl
    simp only [StageState.mk.injEq, true_and, and_true]
    funext r'
    by_cases hrr : r = r'
    · subst hrr; simp
    · simp [hrr, Function.update_of_ne (Ne.symm hrr)]
  · simp only [popFlag, Bool.true_and, List.headD_cons, List.tail_cons, List.isEmpty_cons]
    refine Prod.ext ?_ rfl
    simp only [StageState.mk.injEq, true_and, and_true]
    funext r'
    by_cases hrr : r = r'
    · subst hrr; simp
    · simp [hrr, Function.update_of_ne (Ne.symm hrr)]

theorem sched_consume (t : StageState) : sched (consume t).1 = sched t := by
  unfold consume; split <;> rfl

theorem sched_capture (t : StageState) (wd : Bool) (wf : List Bool) :
    sched (capture t wd wf) = sched t := rfl

/-! ## The stage invariant -/

/-- Stage `st`, born at tick `b` with half `S`, after `d` more ticks; `cap r` is the tick at
which job `r` is captured. -/
structure JobInv (W : List (Fin 2)) (cap : ℕ → ℕ) (b S d : ℕ) (st : StageState) : Prop where
  sched : StageAt st S d
  release : st.release = decide (0 < d ∧ d % S = 0 ∧ 1 ≤ d / S ∧ d / S ≤ 4)
  batch : 1 ≤ d / S → d / S ≤ 4 → st.batch.val = d / S - 1
  pending : st.pending = decide (1 ≤ d / S ∧ d / S ≤ 4 ∧ b + d < cap (d / S - 1))
  results : ∀ r : Fin 4, st.results r =
    if (r.val + 1) * S ≤ d ∧ cap r.val ≤ b + d then
      (jobBits W b S r.val).drop (d + 1 - (r.val + 2) * S)
    else []
  middle : st.middle =
    if 2 ≤ d / S ∧ d / S ≤ 5 then (jobBits W b S (d / S - 2)).getD (d % S) false else false

/-! ## One tick off a boundary -/

theorem divmod_off {S q m : ℕ} (hm : m + 1 < S) :
    (q * S + m + 1) / S = q ∧ (q * S + m + 1) % S = m + 1 := by
  constructor
  · rw [Nat.add_assoc, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega),
      Nat.div_eq_of_lt hm, Nat.zero_add]
  · rw [Nat.add_assoc, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hm]

theorem divmod_at {S q m : ℕ} (hm : m < S) :
    (q * S + m) / S = q ∧ (q * S + m) % S = m := by
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hm, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hm]

theorem jobInv_off {W : List (Fin 2)} {cap : ℕ → ℕ} {b S q m : ℕ} {st : StageState} {src : ℕ}
    {wd : Bool} {wf : List Bool} (hS : 1 ≤ S) (hm : m + 1 < S) (hq5 : q ≤ 5)
    (h : JobInv W cap b S (q * S + m) st)
    (hcap : ∀ r, r < 4 → (r + 1) * S ≤ q * S + m + 1 →
      b + (r + 1) * S ≤ cap r ∧ cap r < b + (r + 2) * S)
    (hwd : 1 ≤ q → q ≤ 4 → b + (q * S + m) + 1 ≤ cap (q - 1) →
      (wd = true ↔ b + (q * S + m) + 1 = cap (q - 1)))
    (hwf : 1 ≤ q → q ≤ 4 → b + (q * S + m) + 1 = cap (q - 1) → wf = jobBits W b S (q - 1)) :
    (advance st false src).2 = false ∧ (consume (advance st false src).1).2 = false ∧
    JobInv W cap b S (q * S + m + 1) (capture (consume (advance st false src).1).1 wd wf) := by
  have hmS : m < S := by omega
  obtain ⟨hq0, hm0⟩ := divmod_at (q := q) hmS
  obtain ⟨hq1, hm1⟩ := divmod_off (q := q) hm
  have hb : (q * S + m + 1) % S ≠ 0 := by rw [hm1]; omega
  have hadv := advance_off hS h.sched hb src
  have hst1 := stageAt_step st S (q * S + m) src hS h.sched (by rw [hq1]; exact hq5)
  rw [hadv]
  set t := ({ st with clock := st.clock.pred, birth := false, release := false } : StageState)
    with ht
  have hsch : StageAt t S (q * S + m + 1) := by
    rw [hadv] at hst1; exact hst1
  have hans : answering t = (decide (2 ≤ q) && decide (q ≤ 5)) := by
    rw [answering_of_stageAt hsch, hq1]
  -- consume
  obtain ⟨tc, vio, hcons, hvio, hctc⟩ : ∃ tc vio, consume t = (tc, vio) ∧ vio = false ∧
      tc.pending = st.pending ∧ tc.batch = st.batch ∧ tc.release = false ∧
      sched tc = sched t ∧
      (∀ r : Fin 4, tc.results r =
        if 2 ≤ q ∧ q ≤ 5 ∧ r.val = q - 2 then (st.results r).tail else st.results r) ∧
      tc.middle = (if 2 ≤ q ∧ q ≤ 5 then (st.results ⟨q - 2, by omega⟩).headD false else false)
      := by
    by_cases hq : 2 ≤ q ∧ q ≤ 5
    · set r : Fin 4 := ⟨q - 2, by omega⟩ with hr
      have e2 : (r.val + 2) * S = q * S := by simp only [hr]; congr 1; omega
      have e1 : (r.val + 1) * S + S = q * S := by rw [← e2]; ring
      have hiv : t.interval.val = r.val + 2 := by
        obtain ⟨_, _, _, h4⟩ := hsch
        rw [h4, hq1]; simp only [hr]; omega
      have hc := hcap r.val (by omega) (by omega)
      have hres : st.results r = (jobBits W b S r.val).drop (q * S + m + 1 - (r.val + 2) * S) := by
        rw [h.results r, if_pos ⟨by omega, by omega⟩, e2]
      have hne : (st.results r).isEmpty = false := by
        rw [hres]
        have : q * S + m + 1 - (r.val + 2) * S < S := by omega
        cases hl : (jobBits W b S r.val).drop (q * S + m + 1 - (r.val + 2) * S)
        · have := congrArg List.length hl; simp at this; omega
        · rfl
      refine ⟨_, _, consume_ans t r (by rw [hans]; simp; omega) hiv, hne, rfl, rfl, rfl,
        sched_consume t ▸ rfl, fun r' => ?_, ?_⟩
      · by_cases hrr : r' = r
        · subst hrr
          show Function.update t.results r (t.results r).tail r = _
          rw [Function.update_self, if_pos ⟨hq.1, hq.2, by simp only [hr]⟩]
        · show Function.update t.results r (t.results r).tail r' = _
          rw [Function.update_of_ne hrr, if_neg]
          intro ⟨_, _, h3⟩; exact hrr (Fin.ext (by simp only [hr]; omega))
      · show (t.results r).headD false = _
        rw [if_pos hq]
    · refine ⟨_, _, consume_not t (by rw [hans]; simp; omega), rfl, rfl, rfl, rfl, rfl,
        fun r' => by rw [if_neg (fun h' => hq ⟨h'.1, h'.2.1⟩)], by rw [if_neg hq]⟩
  obtain ⟨hpend, hbat, hrel, hsc, hres, hmid⟩ := hctc
  refine ⟨rfl, by show (consume t).2 = false; rw [hcons]; exact hvio, ?_⟩
  show JobInv W cap b S (q * S + m + 1) (capture (consume t).1 wd wf)
  rw [hcons]
  have hsch' : StageAt tc S (q * S + m + 1) := (stageAt_congr hsc.symm _ _).mpr hsch
  have hle : ∀ a, a * S ≤ q * S + m ↔ a ≤ q := fun a => by
    rw [← Nat.le_div_iff_mul_le (by omega), hq0]
  have hle' : ∀ a, a * S ≤ q * S + m + 1 ↔ a ≤ q := fun a => by
    rw [← Nat.le_div_iff_mul_le (by omega), hq1]
  have hpst := h.pending
  rw [hq0] at hpst
  have hdone : (st.pending && wd) =
      decide (1 ≤ q ∧ q ≤ 4 ∧ b + (q * S + m) + 1 = cap (q - 1)) := by
    by_cases hp : 1 ≤ q ∧ q ≤ 4 ∧ b + (q * S + m) < cap (q - 1)
    · rw [hpst, decide_eq_true hp, Bool.true_and]
      have := hwd hp.1 hp.2.1 (by omega)
      cases hw : wd
      · symm; rw [decide_eq_false_iff_not]; intro h3; rw [hw] at this; simp_all
      · symm; rw [decide_eq_true_eq]; rw [hw] at this; exact ⟨hp.1, hp.2.1, this.mp rfl⟩
    · rw [hpst, decide_eq_false hp, Bool.false_and]
      symm; rw [decide_eq_false_iff_not]; intro h3; exact hp ⟨h3.1, h3.2.1, by omega⟩
  refine ⟨hsch', ?_, ?_, ?_, fun r => ?_, ?_⟩
  · show tc.release = _
    rw [hrel]; symm; rw [decide_eq_false_iff_not]; intro h3; rw [hm1] at h3; omega
  · intro h1 h2
    rw [hq1] at h1 h2
    show tc.batch.val = _
    rw [hbat, hq1]; have := h.batch; rw [hq0] at this; exact this h1 h2
  · show ((tc.pending || tc.release) && (!((tc.pending || tc.release) && wd))) = _
    rw [hpend, hrel, Bool.or_false, hdone, hpst, hq1]
    by_cases hp : 1 ≤ q ∧ q ≤ 4 ∧ b + (q * S + m) < cap (q - 1)
    · by_cases he : b + (q * S + m) + 1 = cap (q - 1)
      · rw [decide_eq_true hp, decide_eq_true ⟨hp.1, hp.2.1, he⟩]
        symm; simp; omega
      · rw [decide_eq_true hp, decide_eq_false (fun h3 => he h3.2.2)]
        symm; simp; omega
    · rw [decide_eq_false hp]
      simp only [Bool.false_and]
      symm; rw [decide_eq_false_iff_not]; intro h3; exact hp ⟨h3.1, h3.2.1, by omega⟩
  · show (if (tc.pending || tc.release) && wd && tc.batch == r then wf else tc.results r) = _
    rw [hpend, hrel, Bool.or_false, hdone, hres r, h.results r]
    have hr4 := r.isLt
    by_cases hc : 1 ≤ q ∧ q ≤ 4 ∧ b + (q * S + m) + 1 = cap (q - 1) ∧ r.val = q - 1
    · -- job `q - 1` is captured now
      have hb2 : (tc.batch == r) = true := by
        rw [beq_iff_eq, hbat]; apply Fin.ext
        have := h.batch; rw [hq0] at this; rw [this hc.1 hc.2.1]; exact hc.2.2.2.symm
      rw [decide_eq_true ⟨hc.1, hc.2.1, hc.2.2.1⟩, Bool.true_and, hb2, if_pos rfl,
        hwf hc.1 hc.2.1 hc.2.2.1, hc.2.2.2]
      have hq1S : (q - 1 + 1) * S = q * S := by congr 1; omega
      rw [if_pos ⟨by rw [hq1S]; omega, by omega⟩]
      have : q * S + m + 1 + 1 - (q - 1 + 2) * S = 0 := by
        have : (q - 1 + 2) * S = q * S + S := by rw [show q - 1 + 2 = q + 1 by omega]; ring
        omega
      rw [this, List.drop_zero]
    · have hnc : ((decide (1 ≤ q ∧ q ≤ 4 ∧ b + (q * S + m) + 1 = cap (q - 1))) && (tc.batch == r))
          = false := by
        by_cases hd : 1 ≤ q ∧ q ≤ 4 ∧ b + (q * S + m) + 1 = cap (q - 1)
        · rw [decide_eq_true hd, Bool.true_and, beq_eq_false_iff_ne, hbat]
          intro he; apply hc; refine ⟨hd.1, hd.2.1, hd.2.2, ?_⟩
          have := h.batch; rw [hq0] at this; rw [← he, this hd.1 hd.2.1]
        · rw [decide_eq_false hd, Bool.false_and]
      rw [hnc]; simp only [Bool.false_eq_true, if_false]
      have hJ : (jobBits W b S r.val).length = S := length_jobBits _ _ _ _
      rcases Nat.lt_or_ge (r.val + 1) q with hA | hA
      · -- released at least a full interval ago: captured, maybe being popped
        have hr1 : (r.val + 1) * S ≤ q * S + m := (hle _).mpr (by omega)
        have hr1' : (r.val + 1) * S ≤ q * S + m + 1 := (hle' _).mpr (by omega)
        have hr2 : (r.val + 2) * S ≤ q * S := Nat.mul_le_mul_right _ (by omega)
        have hc := hcap r.val hr4 hr1'
        have hcr : cap r.val ≤ b + (q * S + m) := by omega
        by_cases hpop : 2 ≤ q ∧ q ≤ 5 ∧ r.val = q - 2
        · rw [if_pos hpop, if_pos ⟨hr1, hcr⟩, if_pos ⟨hr1', by omega⟩]
          have e2 : (r.val + 2) * S = q * S := by congr 1; omega
          rw [e2, List.tail_drop]
          congr 1; omega
        · rw [if_neg hpop, if_pos ⟨hr1, hcr⟩, if_pos ⟨hr1', by omega⟩]
          have hr3 : (r.val + 3) * S ≤ q * S := Nat.mul_le_mul_right _ (by omega)
          have e3 : (r.val + 3) * S = (r.val + 2) * S + S := by ring
          rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)]
      · rcases Nat.lt_or_ge r.val q with hB | hB
        · -- job `q - 1`: released, not captured this tick
          have hrq : r.val = q - 1 := by omega
          have hq1' : 1 ≤ q := by omega
          have hr1 : (r.val + 1) * S ≤ q * S + m := (hle _).mpr (by omega)
          have hr1' : (r.val + 1) * S ≤ q * S + m + 1 := (hle' _).mpr (by omega)
          have hne : b + (q * S + m) + 1 ≠ cap (q - 1) := fun he =>
            hc ⟨hq1', by omega, he, hrq⟩
          rw [if_neg (fun h3 => by omega)]
          have hcc : (cap r.val ≤ b + (q * S + m)) ↔ (cap r.val ≤ b + (q * S + m + 1)) := by
            rw [hrq]; omega
          have e2 : (r.val + 2) * S = q * S + S := by rw [hrq, show q - 1 + 2 = q + 1 by omega]; ring
          by_cases hcp : cap r.val ≤ b + (q * S + m)
          · rw [if_pos ⟨hr1, hcp⟩, if_pos ⟨hr1', hcc.mp hcp⟩, e2]
            congr 1; omega
          · rw [if_neg (fun h3 => hcp h3.2), if_neg (fun h3 => hcp (hcc.mpr h3.2))]
        · -- not released yet
          have hn1 : ¬ (r.val + 1) * S ≤ q * S + m := fun h3 => by have := (hle _).mp h3; omega
          have hn1' : ¬ (r.val + 1) * S ≤ q * S + m + 1 := fun h3 => by have := (hle' _).mp h3; omega
          rw [if_neg (fun h3 => by omega), if_neg (fun h3 => hn1 h3.1), if_neg (fun h3 => hn1' h3.1)]
  · show tc.middle = _
    rw [hmid, hq1, hm1]
    by_cases hq : 2 ≤ q ∧ q ≤ 5
    · rw [if_pos hq, if_pos hq]
      have hr1 : (q - 2 + 1) * S ≤ q * S + m := (hle _).mpr (by omega)
      have hc := hcap (q - 2) (by omega) ((hle' _).mpr (by omega))
      have hr2 : (q - 2 + 2) * S = q * S := by congr 1; omega
      have hres2 := h.results ⟨q - 2, by omega⟩
      simp only at hres2
      rw [if_pos ⟨hr1, by rw [hr2] at hc; omega⟩, hr2] at hres2
      rw [hres2, show q * S + m + 1 - q * S = m + 1 by omega]
      rw [List.headD_eq_head?_getD, List.head?_drop, List.getD_eq_getElem?_getD]
    · rw [if_neg hq, if_neg hq]

/-! ## One tick onto a boundary -/

theorem jobInv_on {W : List (Fin 2)} {cap : ℕ → ℕ} {b S q : ℕ} {st : StageState} {src : ℕ}
    {wd : Bool} {wf : List Bool} (hS : 1 ≤ S) (hq4 : q ≤ 4)
    (h : JobInv W cap b S (q * S + (S - 1)) st)
    (hcap : ∀ r, r < 4 → (r + 1) * S ≤ (q + 1) * S →
      b + (r + 1) * S ≤ cap r ∧ cap r < b + (r + 2) * S)
    (hwd : q + 1 ≤ 4 → b + (q + 1) * S ≤ cap q → (wd = true ↔ b + (q + 1) * S = cap q))
    (hwf : q + 1 ≤ 4 → b + (q + 1) * S = cap q → wf = jobBits W b S q) :
    (advance st false src).2 = false ∧ (consume (advance st false src).1).2 = false ∧
    JobInv W cap b S ((q + 1) * S) (capture (consume (advance st false src).1).1 wd wf) := by
  have hmS : S - 1 < S := by omega
  obtain ⟨hq0, hm0⟩ := divmod_at (q := q) hmS
  have hd1 : q * S + (S - 1) + 1 = (q + 1) * S := by rw [Nat.add_mul, Nat.one_mul]; omega
  have hq1 : (q + 1) * S / S = q + 1 := Nat.mul_div_cancel _ (by omega)
  have hm1 : (q + 1) * S % S = 0 := Nat.mul_mod_left _ _
  have hb : (q * S + (S - 1) + 1) % S = 0 := by rw [hd1, hm1]
  have hadv := advance_on hS h.sched hb src
  have hiv0 : st.interval.val = q := by rw [h.sched.2.2.2, hq0]
  have hiv : (incInterval st.interval).val = q + 1 := by simp [incInterval, hiv0]; omega
  have hrel : relOf (incInterval st.interval) = decide (q + 1 ≤ 4) := by
    simp only [relOf, hiv]
    rcases (show q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 by omega) with h0 | h0 | h0 | h0 | h0 <;>
      simp [h0]
  have hst1 := stageAt_step st S (q * S + (S - 1)) src hS h.sched (by rw [hd1, hq1]; omega)
  rw [hd1] at hst1
  have hpend0 : st.pending = false := by
    rw [h.pending, hq0, decide_eq_false_iff_not]
    intro h3
    have := hcap (q - 1) (by omega) (Nat.mul_le_mul_right _ (by omega))
    have e : (q - 1 + 2) * S = (q + 1) * S := by congr 1; omega
    rw [e] at this; omega
  rw [hadv]
  set t := ({ st with
          clock := st.half
          interval := incInterval st.interval
          alive := !((incInterval st.interval).val == 6)
          batch := if relOf (incInterval st.interval) then batchOfInterval (incInterval st.interval)
            else st.batch
          birth := false
          release := relOf (incInterval st.interval) } : StageState) with ht
  have hsch : StageAt t S ((q + 1) * S) := by rw [hadv] at hst1; exact hst1
  have hans : answering t = (decide (1 ≤ q) && decide (q ≤ 4)) := by
    rw [answering_of_stageAt hsch, hq1]
    cases hq : decide (1 ≤ q) <;> cases hq' : decide (q ≤ 4) <;> simp_all <;> omega
  refine ⟨by simp [hpend0], ?_⟩
  have hle : ∀ a, a * S ≤ q * S + (S - 1) ↔ a ≤ q := fun a => by
    rw [← Nat.le_div_iff_mul_le (by omega), hq0]
  have hle' : ∀ a, a * S ≤ (q + 1) * S ↔ a ≤ q + 1 := fun a => by
    rw [← Nat.le_div_iff_mul_le (by omega), hq1]
  have hJ : ∀ r, (jobBits W b S r).length = S := fun r => length_jobBits _ _ _ _
  -- consume
  obtain ⟨tc, vio, hcons, hvio, hpend, hbat, hrel', hsc, hres, hmid⟩ : ∃ tc vio,
      consume t = (tc, vio) ∧ vio = false ∧
      tc.pending = st.pending ∧ tc.batch = t.batch ∧ tc.release = t.release ∧
      sched tc = sched t ∧
      (∀ r : Fin 4, tc.results r =
        if 1 ≤ q ∧ r.val = q - 1 then (st.results r).tail else st.results r) ∧
      tc.middle = (if 1 ≤ q then (jobBits W b S (q - 1)).getD 0 false else false) := by
    by_cases hq : 1 ≤ q
    · set r : Fin 4 := ⟨q - 1, by omega⟩ with hr
      have hivt : t.interval.val = r.val + 2 := by
        show (incInterval st.interval).val = _; rw [hiv]; simp only [hr]; omega
      have hr1 : (r.val + 1) * S ≤ q * S + (S - 1) := (hle _).mpr (by simp only [hr]; omega)
      have hc := hcap r.val (by omega) ((hle' _).mpr (by simp only [hr]; omega))
      have e2 : (r.val + 2) * S = (q + 1) * S := by simp only [hr]; congr 1; omega
      have hres0 : st.results r = jobBits W b S r.val := by
        rw [h.results r, if_pos ⟨hr1, by rw [e2] at hc; omega⟩, e2, hd1, Nat.sub_self,
          List.drop_zero]
      have hne : (st.results r).isEmpty = false := by
        rw [hres0]
        cases hl : jobBits W b S r.val
        · have := congrArg List.length hl; rw [hJ] at this; simp at this; omega
        · rfl
      refine ⟨_, _, consume_ans t r (by rw [hans]; simp; omega) hivt, hne, rfl, rfl, rfl,
        sched_consume t ▸ rfl, fun r' => ?_, ?_⟩
      · by_cases hrr : r' = r
        · subst hrr
          show Function.update t.results r (t.results r).tail r = _
          rw [Function.update_self, if_pos ⟨hq, by simp only [hr]⟩]
        · show Function.update t.results r (t.results r).tail r' = _
          rw [Function.update_of_ne hrr, if_neg]
          intro ⟨_, h3⟩; exact hrr (Fin.ext (by simp only [hr]; omega))
      · show (t.results r).headD false = _
        rw [if_pos hq]
        show (st.results r).headD false = _
        rw [hres0]
        cases hl : jobBits W b S (q - 1) <;> simp_all
    · refine ⟨_, _, consume_not t (by rw [hans]; simp; omega), rfl, rfl, rfl, rfl, rfl,
        fun r' => by rw [if_neg (fun h' => hq h'.1)], by rw [if_neg hq]⟩
  refine ⟨by show (consume t).2 = false; rw [hcons]; exact hvio, ?_⟩
  show JobInv W cap b S ((q + 1) * S) (capture (consume t).1 wd wf)
  rw [hcons]
  have hsch' : StageAt tc S ((q + 1) * S) := (stageAt_congr hsc.symm _ _).mpr hsch
  have htrel : t.release = decide (q + 1 ≤ 4) := hrel
  have hdone : ((tc.pending || tc.release) && wd) = decide (q + 1 ≤ 4 ∧ b + (q + 1) * S = cap q) := by
    rw [hpend, hpend0, hrel', htrel, Bool.false_or]
    by_cases hq : q + 1 ≤ 4
    · rw [decide_eq_true hq, Bool.true_and]
      have hc := hcap q (by omega) (le_refl _)
      have := hwd hq hc.1
      cases hw : wd
      · symm; rw [decide_eq_false_iff_not]; intro h3; rw [hw] at this; simp_all
      · symm; rw [decide_eq_true_eq]; rw [hw] at this; exact ⟨hq, this.mp rfl⟩
    · rw [decide_eq_false hq, Bool.false_and]
      symm; rw [decide_eq_false_iff_not]; intro h3; exact hq h3.1
  refine ⟨hsch', ?_, ?_, ?_, fun r => ?_, ?_⟩
  · show tc.release = _
    rw [hrel', htrel, hq1, hm1]
    cases hq : decide (q + 1 ≤ 4) <;> simp_all <;> omega
  · intro h1 h2
    rw [hq1] at h1 h2
    show tc.batch.val = _
    rw [hbat, hq1]
    show (if relOf (incInterval st.interval) then batchOfInterval (incInterval st.interval)
      else st.batch).val = _
    rw [hrel, decide_eq_true h2, if_pos rfl]
    simp [batchOfInterval, hiv]; omega
  · show ((tc.pending || tc.release) && (!((tc.pending || tc.release) && wd))) = _
    rw [hdone, hpend, hpend0, hrel', htrel, Bool.false_or, hq1]
    by_cases hq : q + 1 ≤ 4
    · have hc := hcap q (by omega) (le_refl _)
      by_cases he : b + (q + 1) * S = cap q
      · rw [decide_eq_true hq, decide_eq_true ⟨hq, he⟩]
        symm; simp; omega
      · rw [decide_eq_true hq, decide_eq_false (fun h3 => he h3.2)]
        symm; simp; omega
    · rw [decide_eq_false hq, Bool.false_and]
      symm; rw [decide_eq_false_iff_not]; intro h3; omega
  · show (if (tc.pending || tc.release) && wd && tc.batch == r then wf else tc.results r) = _
    rw [hdone, hres r, h.results r]
    have hr4 := r.isLt
    by_cases hc : q + 1 ≤ 4 ∧ b + (q + 1) * S = cap q ∧ r.val = q
    · have hb2 : (tc.batch == r) = true := by
        rw [beq_iff_eq, hbat]; apply Fin.ext
        show (if relOf (incInterval st.interval) then batchOfInterval (incInterval st.interval)
          else st.batch).val = _
        rw [hrel, decide_eq_true hc.1, if_pos rfl]
        simp [batchOfInterval, hiv]; omega
      rw [decide_eq_true ⟨hc.1, hc.2.1⟩, Bool.true_and, hb2, if_pos rfl, hwf hc.1 hc.2.1, hc.2.2]
      rw [if_pos ⟨le_refl _, by omega⟩]
      have : (q + 1) * S + 1 - (q + 2) * S = 0 := by
        have : (q + 2) * S = (q + 1) * S + S := by ring
        omega
      rw [this, List.drop_zero]
    · have hnc : (decide (q + 1 ≤ 4 ∧ b + (q + 1) * S = cap q) && (tc.batch == r)) = false := by
        by_cases hd : q + 1 ≤ 4 ∧ b + (q + 1) * S = cap q
        · rw [decide_eq_true hd, Bool.true_and, beq_eq_false_iff_ne, hbat]
          intro he; apply hc; refine ⟨hd.1, hd.2, ?_⟩
          rw [← he]
          show (if relOf (incInterval st.interval) then batchOfInterval (incInterval st.interval)
            else st.batch).val = _
          rw [hrel, decide_eq_true hd.1, if_pos rfl]
          simp [batchOfInterval, hiv]; omega
        · rw [decide_eq_false hd, Bool.false_and]
      rw [hnc]; simp only [Bool.false_eq_true, if_false]
      rcases Nat.lt_or_ge (r.val + 1) q with hA | hA
      · -- long released: already fully popped
        have hr1 : (r.val + 1) * S ≤ q * S + (S - 1) := (hle _).mpr (by omega)
        have hr1' : (r.val + 1) * S ≤ (q + 1) * S := (hle' _).mpr (by omega)
        have hc2 := hcap r.val hr4 hr1'
        have hr3 : (r.val + 3) * S ≤ (q + 1) * S := Nat.mul_le_mul_right _ (by omega)
        have e3 : (r.val + 3) * S = (r.val + 2) * S + S := by ring
        rw [if_neg (fun h3 => by omega), if_pos ⟨hr1, by omega⟩, if_pos ⟨hr1', by omega⟩]
        rw [List.drop_eq_nil_of_le (by rw [hJ]; omega), List.drop_eq_nil_of_le (by rw [hJ]; omega)]
      · rcases Nat.lt_or_ge r.val q with hB | hB
        · -- job `q - 1`: popped now for the first time
          have hrq : r.val = q - 1 := by omega
          have hr1 : (r.val + 1) * S ≤ q * S + (S - 1) := (hle _).mpr (by omega)
          have hr1' : (r.val + 1) * S ≤ (q + 1) * S := (hle' _).mpr (by omega)
          have hc2 := hcap r.val hr4 hr1'
          have e2 : (r.val + 2) * S = (q + 1) * S := by rw [hrq]; congr 1; omega
          rw [if_pos ⟨by omega, hrq⟩, if_pos ⟨hr1, by rw [e2] at hc2; omega⟩,
            if_pos ⟨hr1', by omega⟩, e2, hd1, Nat.sub_self, List.drop_zero, ← List.drop_one,
            show (q + 1) * S + 1 - (q + 1) * S = 1 by omega]
        · rcases Nat.lt_or_ge q r.val with hC | hC
          · -- not released
            have hn1 : ¬ (r.val + 1) * S ≤ q * S + (S - 1) := fun h3 => by
              have := (hle _).mp h3; omega
            have hn1' : ¬ (r.val + 1) * S ≤ (q + 1) * S := fun h3 => by
              have := (hle' _).mp h3; omega
            rw [if_neg (fun h3 => by omega), if_neg (fun h3 => hn1 h3.1),
              if_neg (fun h3 => hn1' h3.1)]
          · -- job `q`: released now, not captured now
            have hrq : r.val = q := by omega
            have hn1 : ¬ (r.val + 1) * S ≤ q * S + (S - 1) := fun h3 => by
              have := (hle _).mp h3; omega
            rw [if_neg (fun h3 => by omega), if_neg (fun h3 => hn1 h3.1)]
            by_cases hq : q + 1 ≤ 4
            · have hc2 := hcap q (by omega) (le_refl _)
              rw [if_neg]
              intro h3; rw [hrq] at h3; exact hc ⟨hq, by omega, hrq⟩
            · omega
  · show tc.middle = _
    rw [hmid, hq1, hm1]
    by_cases hq : 1 ≤ q
    · rw [if_pos hq, if_pos ⟨by omega, by omega⟩, show q + 1 - 2 = q - 1 by omega]
    · rw [if_neg hq, if_neg (fun h3 => by omega)]

/-! ## Births and dormant stages -/

theorem advance_viol (st : StageState) (nb : Bool) (src : ℕ) :
    (advance st nb src).2 = (advance st false src).2 := rfl

/-- **A birth**: the new stage satisfies the invariant at `d = 0`, and the tick is clean for it
(given that `advance` raises nothing). -/
theorem jobInv_birth {W : List (Fin 2)} {cap : ℕ → ℕ} {b S : ℕ} (hS : 1 ≤ S) (st : StageState)
    (wd : Bool) (wf : List Bool) :
    (consume (advance st true S).1).2 = false ∧
    JobInv W cap b S 0 (capture (consume (advance st true S).1).1 wd wf) := by
  have hsch := stageAt_birth st S
  have hans : answering (advance st true S).1 = false := by
    rw [answering_of_stageAt hsch]; simp
  rw [consume_not _ hans]
  refine ⟨rfl, (stageAt_congr rfl _ _).mpr hsch, ?_, fun h1 => by simp at h1, ?_,
    fun r => ?_, ?_⟩
  · simp [capture, advance]
  · simp [capture, advance]
  · have : ¬ ((r.val + 1) * S ≤ 0 ∧ cap r.val ≤ b + 0) := fun h3 => by
      have := Nat.mul_le_mul_right S (show 1 ≤ r.val + 1 by omega)
      omega
    rw [if_neg this]
    simp [capture, advance]
  · simp [capture]

/-- A stage that has not been born yet. -/
def Dormant (st : StageState) : Prop := st.alive = false ∧ st.pending = false ∧ st.release = false

theorem dormant_initial : Dormant StageState.initial := ⟨rfl, rfl, rfl⟩

theorem advance_dormant {st : StageState} (h : Dormant st) (src : ℕ) :
    (advance st false src).2 = false := by
  obtain ⟨ha, hp, -⟩ := h
  simp [advance, ha, hp]

theorem dormant_step {st : StageState} (h : Dormant st) (src : ℕ) (wd : Bool) (wf : List Bool) :
    (consume (advance st false src).1).2 = false ∧
    Dormant (capture (consume (advance st false src).1).1 wd wf) := by
  obtain ⟨ha, hp, hr⟩ := h
  have hans : answering (advance st false src).1 = false := by
    simp [answering, advance, ha]
  rw [consume_not _ hans]
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp [capture, advance, ha, hp]

/-! ## A tick, stage by stage -/

section Run
variable {Wm Wf : Type} (mOps : WorkerOps Wm) (fOps : WorkerOps Wf)

/-- Stage `i` after a tick: `advance`, `consume`, then `capture` from flag worker `i`'s state after
the tick. -/
theorem tick_stage (s : PalState Wm Wf) (a : Fin 2) (i : Fin 2) :
    (tick mOps fOps s a).stages i =
      capture (consume (advance (s.stages i) (birthOf s && s.slot == i) s.power).1).1
        (fOps.modeDone ((tick mOps fOps s a).flags i))
        (fOps.flags ((tick mOps fOps s a).flags i)) := by
  have hb : (s.powerReady && (if s.powerReady then s.nextBirth.pred else s.nextBirth) == 0) =
      birthOf s := by unfold birthOf; cases s.powerReady <;> simp
  fin_cases i
  · show _ = capture (consume (advance (s.stages 0) (birthOf s && s.slot == 0) s.power).1).1 _ _
    rw [← hb]; rfl
  · show _ = capture (consume (advance (s.stages 1) (birthOf s && s.slot == 1) s.power).1).1 _ _
    rw [← hb]; rfl

theorem ctlViolation_eq (s : PalState Wm Wf) :
    ScaWindowFault.ctlViolation s =
      ((advance (s.stages 0) (birthOf s && s.slot == 0) s.power).2 ||
        (advance (s.stages 1) (birthOf s && s.slot == 1) s.power).2 ||
        (consume (advance (s.stages 0) (birthOf s && s.slot == 0) s.power).1).2 ||
        (consume (advance (s.stages 1) (birthOf s && s.slot == 1) s.power).1).2) := rfl

end Run

/-! ## One tick of a live stage, either way -/

theorem jobInv_tick {W : List (Fin 2)} {cap : ℕ → ℕ} {b S d : ℕ} {st : StageState} {src : ℕ}
    {wd : Bool} {wf : List Bool} (hS : 1 ≤ S) (h : JobInv W cap b S d st)
    (hlive : (d + 1) / S ≤ 5)
    (hcap : ∀ r, r < 4 → (r + 1) * S ≤ d + 1 →
      b + (r + 1) * S ≤ cap r ∧ cap r < b + (r + 2) * S)
    (hwd : ∀ r, r < 4 → (r + 1) * S ≤ d + 1 → b + d + 1 ≤ cap r → (wd = true ↔ b + d + 1 = cap r))
    (hwf : ∀ r, r < 4 → (r + 1) * S ≤ d + 1 → b + d + 1 = cap r → wf = jobBits W b S r) :
    (advance st false src).2 = false ∧ (consume (advance st false src).1).2 = false ∧
    JobInv W cap b S (d + 1) (capture (consume (advance st false src).1).1 wd wf) := by
  obtain ⟨q, m, hm, rfl⟩ : ∃ q m, m < S ∧ d = q * S + m :=
    ⟨d / S, d % S, Nat.mod_lt _ (by omega), by rw [Nat.div_add_mod' d S]⟩
  rcases Nat.lt_or_ge (m + 1) S with hm1 | hm1
  · have hq1 := (divmod_off (q := q) hm1).1
    rw [hq1] at hlive
    have hle : q * S ≤ q * S + m + 1 := by omega
    exact jobInv_off hS hm1 hlive h hcap
      (fun h1 h2 h3 => hwd (q - 1) (by omega)
        (by rw [show q - 1 + 1 = q by omega]; omega) h3)
      (fun h1 h2 h3 => hwf (q - 1) (by omega)
        (by rw [show q - 1 + 1 = q by omega]; omega) h3)
  · have hmS : m = S - 1 := by omega
    subst hmS
    have hd1 : q * S + (S - 1) + 1 = (q + 1) * S := by rw [Nat.add_mul, Nat.one_mul]; omega
    have hq1 : (q + 1) * S / S = q + 1 := Nat.mul_div_cancel _ (by omega)
    rw [hd1, hq1] at hlive
    have e : ∀ x, b + (q * S + (S - 1)) + 1 = x ↔ b + (q + 1) * S = x := fun x => by omega
    have := jobInv_on (src := src) (wd := wd) (wf := wf) hS (by omega) h
      (fun r hr hr' => hcap r hr (by rw [hd1]; exact hr'))
      (fun h1 h2 => by
        have := hwd q (by omega) (by rw [hd1]) (by omega)
        rw [this, e])
      (fun h1 h2 => hwf q (by omega) (by rw [hd1]) (by omega))
    rwa [← hd1] at this

/-- A stage at the end of its life (`d + 1 = 6S`) raises no violation when it is replaced. -/
theorem retire_clean {W : List (Fin 2)} {cap : ℕ → ℕ} {b S : ℕ} {st : StageState} (src : ℕ)
    (hS : 1 ≤ S) (h : JobInv W cap b S (5 * S + (S - 1)) st) (nb : Bool) :
    (advance st nb src).2 = false := by
  rw [advance_viol]
  have hb : (5 * S + (S - 1) + 1) % S = 0 := by
    rw [show 5 * S + (S - 1) + 1 = 6 * S by omega, Nat.mul_mod_left]
  rw [advance_on hS h.sched hb src]
  have hiv0 : st.interval.val = 5 := by
    rw [h.sched.2.2.2, (divmod_at (q := 5) (show S - 1 < S by omega)).1]
  simp [relOf, incInterval, hiv0]

/-! ## The flag workers' promise, and one slot through one tick of the run -/

section Contract
variable {Wm Wf : Type} (mOps : WorkerOps Wm) (fOps : WorkerOps Wf) (m0 : Wm) (f0 : Wf)

/-- Job `r` of the stage born at `2^j` (slot `idx (j-1)`, half `2^(j-1)`) is captured at `c`:
before the next release, done exactly at `c` from its release on, with the job's bits. -/
def CapAt (W : List (Fin 2)) (j r c : ℕ) : Prop :=
  2 ^ j + (r + 1) * 2 ^ (j - 1) ≤ c ∧ c < 2 ^ j + (r + 2) * 2 ^ (j - 1) ∧
  (∀ n, 2 ^ j + (r + 1) * 2 ^ (j - 1) ≤ n → n ≤ c → n ≤ W.length →
    (fOps.modeDone ((run mOps fOps m0 f0 (W.take n)).flags (idx (j - 1))) = true ↔ n = c)) ∧
  (c ≤ W.length →
    fOps.flags ((run mOps fOps m0 f0 (W.take c)).flags (idx (j - 1))) =
      jobBits W (2 ^ j) (2 ^ (j - 1)) r)

/-- **The flag workers' promise** on the word `W`. -/
def FlagsContract (W : List (Fin 2)) : Prop :=
  ∃ cap : ℕ → ℕ → ℕ, ∀ j r, 1 ≤ j → r < 4 → 2 ^ j + (r + 1) * 2 ^ (j - 1) ≤ W.length →
    CapAt mOps fOps m0 f0 W j r (cap j r)

theorem run_take_succ (W : List (Fin 2)) {n : ℕ} (hn : n < W.length) :
    run mOps fOps m0 f0 (W.take (n + 1)) = tick mOps fOps (run mOps fOps m0 f0 (W.take n)) W[n] := by
  rw [List.take_succ, List.getElem?_eq_getElem hn, Option.toList_some, ScaWindowSchedule.run_append]

/-- **One slot through one tick**, from the promise: the stage born at `2^j` in its slot. -/
theorem slot_step {W : List (Fin 2)} {cap : ℕ → ℕ → ℕ} {j d : ℕ}
    (hC : ∀ r, r < 4 → 2 ^ j + (r + 1) * 2 ^ (j - 1) ≤ W.length →
      CapAt mOps fOps m0 f0 W j r (cap j r))
    (hj : 1 ≤ j) (hn : 2 ^ j + d < W.length)
    (h : JobInv W (cap j) (2 ^ j) (2 ^ (j - 1)) d
      ((run mOps fOps m0 f0 (W.take (2 ^ j + d))).stages (idx (j - 1))))
    (hlive : (d + 1) / 2 ^ (j - 1) ≤ 5) (src : ℕ) :
    let s := run mOps fOps m0 f0 (W.take (2 ^ j + d))
    (advance (s.stages (idx (j - 1))) false src).2 = false ∧
      (consume (advance (s.stages (idx (j - 1))) false src).1).2 = false ∧
      JobInv W (cap j) (2 ^ j) (2 ^ (j - 1)) (d + 1)
        (capture (consume (advance (s.stages (idx (j - 1))) false src).1).1
          (fOps.modeDone ((run mOps fOps m0 f0 (W.take (2 ^ j + d + 1))).flags (idx (j - 1))))
          (fOps.flags ((run mOps fOps m0 f0 (W.take (2 ^ j + d + 1))).flags (idx (j - 1))))) := by
  intro s
  have hS : 1 ≤ 2 ^ (j - 1) := Nat.one_le_two_pow
  refine jobInv_tick hS h hlive (fun r hr hr' => ?_) (fun r hr hr' hle => ?_)
    (fun r hr hr' he => ?_)
  · obtain ⟨h1, h2, -⟩ := hC r hr (by omega); exact ⟨h1, h2⟩
  · obtain ⟨h1, h2, h3, -⟩ := hC r hr (by omega)
    exact h3 _ (by omega) (by omega) (by omega)
  · obtain ⟨h1, h2, h3, h4⟩ := hC r hr (by omega)
    rw [← he] at h4; exact h4 (by omega)

end Contract

/-! ## The whole run -/

section Global
variable {Wm Wf : Type} (mOps : WorkerOps Wm) (fOps : WorkerOps Wf) (m0 : Wm) (f0 : Wf)

/-- The job invariants of both stages after `n` letters, `2^k ≤ n < 2^(k+1)`. -/
def GInv (W : List (Fin 2)) (cap : ℕ → ℕ → ℕ) (k n : ℕ) (s : PalState Wm Wf) : Prop :=
  (1 ≤ k → JobInv W (cap k) (2 ^ k) (2 ^ (k - 1)) (n - 2 ^ k) (s.stages (idx (k - 1)))) ∧
  (2 ≤ k → JobInv W (cap (k - 1)) (2 ^ (k - 1)) (2 ^ (k - 1 - 1)) (n - 2 ^ (k - 1))
    (s.stages (idx k))) ∧
  (k = 0 → ∀ i, Dormant (s.stages i)) ∧
  (k = 1 → Dormant (s.stages (idx 1)))

/-- A stage's tick is clean. -/
def Clean (st : StageState) (nb : Bool) (src : ℕ) : Prop :=
  (advance st nb src).2 = false ∧ (consume (advance st nb src).1).2 = false

theorem clean_of_all (s : PalState Wm Wf)
    (h : ∀ i : Fin 2, Clean (s.stages i) (birthOf s && s.slot == i) s.power) :
    ScaWindowFault.ctlViolation s = false := by
  rw [ctlViolation_eq]
  obtain ⟨h0a, h0c⟩ := h 0
  obtain ⟨h1a, h1c⟩ := h 1
  simp [h0a, h0c, h1a, h1c]

theorem fin2_cover (k : ℕ) (hk : 1 ≤ k) (i : Fin 2) : i = idx k ∨ i = idx (k - 1) := by
  have h1 := idx_succ_ne (k - 1)
  rw [show k - 1 + 1 = k by omega] at h1
  have : ∀ a b c : Fin 2, a ≠ b → c = a ∨ c = b := by decide
  exact (this _ _ i h1.symm)

variable {mOps fOps m0 f0}

theorem ginv_step {W : List (Fin 2)} {cap : ℕ → ℕ → ℕ}
    (hC : ∀ j r, 1 ≤ j → r < 4 → 2 ^ j + (r + 1) * 2 ^ (j - 1) ≤ W.length →
      CapAt mOps fOps m0 f0 W j r (cap j r))
    {k n : ℕ} (hk : 2 ^ k ≤ n) (hkn : n < 2 ^ (k + 1)) (hnW : n < W.length)
    (hI : Inv k n (run mOps fOps m0 f0 (W.take n)))
    (h : GInv W cap k n (run mOps fOps m0 f0 (W.take n))) :
    ScaWindowFault.ctlViolation (run mOps fOps m0 f0 (W.take n)) = false ∧
      (n + 1 < 2 ^ (k + 1) → GInv W cap k (n + 1) (run mOps fOps m0 f0 (W.take (n + 1)))) ∧
      (n + 1 = 2 ^ (k + 1) →
        GInv W cap (k + 1) (n + 1) (run mOps fOps m0 f0 (W.take (n + 1)))) := by
  set s := run mOps fOps m0 f0 (W.take n) with hs
  obtain ⟨_, hready, hpow, hnb, hslot, _, _⟩ := hI
  have hbirth : birthOf s = decide (n + 1 = 2 ^ (k + 1)) := by
    simp only [birthOf, hready, hnb, Bool.true_and, Nat.pred_eq_sub_one]
    by_cases he : n + 1 = 2 ^ (k + 1)
    · simp [he]; omega
    · simp [he]; omega
  have hs' := run_take_succ mOps fOps m0 f0 W hnW
  have hstage : ∀ i, (run mOps fOps m0 f0 (W.take (n + 1))).stages i =
      capture (consume (advance (s.stages i) (birthOf s && s.slot == i) s.power).1).1
        (fOps.modeDone ((run mOps fOps m0 f0 (W.take (n + 1))).flags i))
        (fOps.flags ((run mOps fOps m0 f0 (W.take (n + 1))).flags i)) := by
    intro i; rw [hs']; exact tick_stage mOps fOps s _ i
  have h2k : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  -- the young stage (born at `2^k`, slot `idx (k-1)`), when `1 ≤ k`
  have young : 1 ≤ k → (birthOf s && s.slot == idx (k - 1)) = false ∧
      Clean (s.stages (idx (k - 1))) false s.power ∧
      JobInv W (cap k) (2 ^ k) (2 ^ (k - 1)) (n + 1 - 2 ^ k)
        ((run mOps fOps m0 f0 (W.take (n + 1))).stages (idx (k - 1))) := by
    intro hk1
    have hS : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
    have hne : (s.slot == idx (k - 1)) = false := by
      rw [hslot, beq_eq_false_iff_ne]
      have := idx_succ_ne (k - 1); rw [show k - 1 + 1 = k by omega] at this; exact this.symm
    have hstep := slot_step mOps fOps m0 f0 (fun r hr hr' => hC k r hk1 hr hr') hk1
      (d := n - 2 ^ k) (by omega) (by rw [show 2 ^ k + (n - 2 ^ k) = n by omega]; exact h.1 hk1)
      (Nat.div_le_of_le_mul (by omega)) s.power
    rw [show 2 ^ k + (n - 2 ^ k) = n by omega] at hstep
    refine ⟨by rw [hne, Bool.and_false], ⟨hstep.1, hstep.2.1⟩, ?_⟩
    rw [hstage, hne, Bool.and_false, show n + 1 - 2 ^ k = n - 2 ^ k + 1 by omega]
    exact hstep.2.2
  -- the old stage (born at `2^(k-1)`, slot `idx k`), when `2 ≤ k`
  have hidx : ∀ k, 2 ≤ k → idx k = idx (k - 1 - 1) := fun k hk2 => by
    rw [← idx_add_two (k - 1 - 1)]; congr 1; omega
  have old_nb : 2 ≤ k → n + 1 < 2 ^ (k + 1) →
      (birthOf s && s.slot == idx k) = false ∧ Clean (s.stages (idx k)) false s.power ∧
      JobInv W (cap (k - 1)) (2 ^ (k - 1)) (2 ^ (k - 1 - 1)) (n + 1 - 2 ^ (k - 1))
        ((run mOps fOps m0 f0 (W.take (n + 1))).stages (idx k)) := by
    intro hk2 hlt
    have hS : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
    have hS1 : 2 ^ (k - 1) = 2 * 2 ^ (k - 1 - 1) := by rw [← pow_succ']; congr 1; omega
    have hnb0 : birthOf s = false := by rw [hbirth]; simp; omega
    have hst := h.2.1 hk2
    rw [hidx k hk2] at hst ⊢
    have hstep := slot_step mOps fOps m0 f0 (fun r hr hr' => hC (k - 1) r (by omega) hr hr')
      (by omega) (d := n - 2 ^ (k - 1)) (by omega)
      (by rw [show 2 ^ (k - 1) + (n - 2 ^ (k - 1)) = n by omega]; exact hst)
      (Nat.lt_succ_iff.mp (Nat.div_lt_of_lt_mul (by omega))) s.power
    rw [show 2 ^ (k - 1) + (n - 2 ^ (k - 1)) = n by omega] at hstep
    refine ⟨by rw [hnb0, Bool.false_and], ⟨hstep.1, hstep.2.1⟩, ?_⟩
    rw [hstage, hnb0, Bool.false_and, show n + 1 - 2 ^ (k - 1) = n - 2 ^ (k - 1) + 1 by omega]
    exact hstep.2.2
  have old_birth : 2 ≤ k → n + 1 = 2 ^ (k + 1) →
      (birthOf s && s.slot == idx k) = true ∧ Clean (s.stages (idx k)) true s.power ∧
      JobInv W (cap (k + 1)) (2 ^ (k + 1)) (2 ^ k) 0
        ((run mOps fOps m0 f0 (W.take (n + 1))).stages (idx k)) := by
    intro hk2 heq
    have hS : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
    have hS1 : 2 ^ (k - 1) = 2 * 2 ^ (k - 1 - 1) := by rw [← pow_succ']; congr 1; omega
    have hnb1 : (birthOf s && s.slot == idx k) = true := by
      rw [hbirth, hslot]; simp [heq]
    have hst := h.2.1 hk2
    rw [show n - 2 ^ (k - 1) = 5 * 2 ^ (k - 1 - 1) + (2 ^ (k - 1 - 1) - 1) by omega] at hst
    have hv := retire_clean s.power (Nat.one_le_two_pow) hst true
    have hb := jobInv_birth (W := W) (cap := cap (k + 1)) (b := 2 ^ (k + 1)) (S := 2 ^ k)
      Nat.one_le_two_pow (s.stages (idx k))
      (fOps.modeDone ((run mOps fOps m0 f0 (W.take (n + 1))).flags (idx k)))
      (fOps.flags ((run mOps fOps m0 f0 (W.take (n + 1))).flags (idx k)))
    refine ⟨hnb1, ⟨hv, by rw [hpow]; exact hb.1⟩, ?_⟩
    rw [hstage, hnb1, hpow]
    exact hb.2
  -- dormant stages
  have dorm_nb : ∀ i, Dormant (s.stages i) → (birthOf s && s.slot == i) = false →
      Clean (s.stages i) false s.power ∧
      Dormant ((run mOps fOps m0 f0 (W.take (n + 1))).stages i) := by
    intro i hd hnb0
    have := dormant_step hd s.power
      (fOps.modeDone ((run mOps fOps m0 f0 (W.take (n + 1))).flags i))
      (fOps.flags ((run mOps fOps m0 f0 (W.take (n + 1))).flags i))
    refine ⟨⟨advance_dormant hd _, this.1⟩, ?_⟩
    rw [hstage, hnb0]; exact this.2
  have dorm_birth : ∀ i, Dormant (s.stages i) → (birthOf s && s.slot == i) = true →
      Clean (s.stages i) true s.power ∧
      JobInv W (cap (k + 1)) (2 ^ (k + 1)) (2 ^ k) 0
        ((run mOps fOps m0 f0 (W.take (n + 1))).stages i) := by
    intro i hd hnb1
    have hb := jobInv_birth (W := W) (cap := cap (k + 1)) (b := 2 ^ (k + 1)) (S := 2 ^ k)
      Nat.one_le_two_pow (s.stages i)
      (fOps.modeDone ((run mOps fOps m0 f0 (W.take (n + 1))).flags i))
      (fOps.flags ((run mOps fOps m0 f0 (W.take (n + 1))).flags i))
    refine ⟨⟨by rw [advance_viol]; exact advance_dormant hd _, by rw [hpow]; exact hb.1⟩, ?_⟩
    rw [hstage, hnb1, hpow]; exact hb.2
  -- assembly
  have hk0 : k = 0 → n = 1 := fun h0 => by subst h0; simp at hk hkn; omega
  have hsl1 : k = 0 → s.slot = 0 := fun h0 => by rw [hslot, h0]; rfl
  by_cases hB : n + 1 = 2 ^ (k + 1)
  · -- a birth into slot `idx k`
    have hnbk : (birthOf s && s.slot == idx k) = true := by rw [hbirth, hslot]; simp [hB]
    have newborn : Clean (s.stages (idx k)) true s.power ∧
        JobInv W (cap (k + 1)) (2 ^ (k + 1)) (2 ^ k) 0
          ((run mOps fOps m0 f0 (W.take (n + 1))).stages (idx k)) := by
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · rcases Nat.lt_or_ge k 1 with hk1 | hk1
        · have := (h.2.2.1 (by omega)) (idx k)
          exact dorm_birth _ this hnbk
        · have hk1' : k = 1 := by omega
          have := h.2.2.2 hk1'; rw [← hk1'] at this
          exact dorm_birth _ this hnbk
      · exact (old_birth hk2 hB).2
    refine ⟨clean_of_all s fun i => ?_, fun h' => absurd hB (Nat.ne_of_lt h'), fun _ => ?_⟩
    · rcases Nat.lt_or_ge k 1 with hk1 | hk1
      · -- `k = 0`: slot `0` is born, slot `1` sleeps
        have hk00 : k = 0 := by omega
        by_cases hi : i = idx k
        · rw [hi, hnbk]; exact newborn.1
        · have hnb0 : (birthOf s && s.slot == i) = false := by
            rw [hbirth, hslot]; simp [hB]; exact fun h3 => hi h3.symm
          rw [hnb0]; exact (dorm_nb i ((h.2.2.1 hk00) i) hnb0).1
      · rcases fin2_cover k hk1 i with hi | hi
        · rw [hi, hnbk]; exact newborn.1
        · rw [hi, (young hk1).1]; exact (young hk1).2.1
    · refine ⟨fun _ => ?_, fun hk2 => ?_, fun h3 => absurd h3 (by omega), fun h3 => ?_⟩
      · simp only [show k + 1 - 1 = k by omega, show n + 1 - 2 ^ (k + 1) = 0 by omega]
        exact newborn.2
      · have hk1 : 1 ≤ k := by omega
        have e1 : k + 1 - 1 = k := by omega
        have e2 : k + 1 - 1 - 1 = k - 1 := by omega
        have e3 : idx (k + 1) = idx (k - 1) := by
          rw [show k + 1 = k - 1 + 2 by omega, idx_add_two]
        rw [e1, e3]
        exact (young hk1).2.2
      · have hk00 : k = 0 := by omega
        subst hk00
        have hnb0 : (birthOf s && s.slot == idx 1) = false := by
          rw [hslot]; simp only [Bool.and_eq_false_iff]; right; decide
        exact (dorm_nb (idx 1) ((h.2.2.1 rfl) (idx 1)) hnb0).2
  · -- no birth
    have hnb0 : birthOf s = false := by rw [hbirth]; simp [hB]
    have hk1 : 1 ≤ k := by
      by_contra hk1; have := hk0 (by omega); subst this; omega
    refine ⟨clean_of_all s fun i => ?_, fun _ => ?_, fun h' => absurd h' hB⟩
    · rcases fin2_cover k hk1 i with hi | hi
      · rw [hi]
        rcases Nat.lt_or_ge k 2 with hk2 | hk2
        · have hk1' : k = 1 := by omega
          have hd := h.2.2.2 hk1'; rw [← hk1'] at hd
          have hnb : (birthOf s && s.slot == idx k) = false := by rw [hnb0, Bool.false_and]
          rw [hnb]; exact (dorm_nb _ hd hnb).1
        · rw [(old_nb hk2 (by omega)).1]; exact (old_nb hk2 (by omega)).2.1
      · rw [hi, (young hk1).1]; exact (young hk1).2.1
    · refine ⟨fun _ => (young hk1).2.2, fun hk2 => (old_nb hk2 (by omega)).2.2,
        fun h3 => absurd h3 (by omega), fun h3 => ?_⟩
      have hd := h.2.2.2 h3
      have hnb : (birthOf s && s.slot == idx 1) = false := by rw [hnb0, Bool.false_and]
      exact (dorm_nb _ hd hnb).2

end Global

/-! ## Every prefix, and the two obligations -/

section Final
variable {Wm Wf : Type} {mOps : WorkerOps Wm} {fOps : WorkerOps Wf} {m0 : Wm} {f0 : Wf}

theorem ginv_one (W : List (Fin 2)) (cap : ℕ → ℕ → ℕ) (hW : 1 ≤ W.length) :
    GInv W cap 0 1 (run mOps fOps m0 f0 (W.take 1)) := by
  have hs' := run_take_succ mOps fOps m0 f0 W (n := 0) (by omega)
  refine ⟨fun h => absurd h (by omega), fun h => absurd h (by omega), fun _ i => ?_,
    fun h => absurd h (by omega)⟩
  rw [hs', tick_stage]
  have hd : Dormant ((run mOps fOps m0 f0 (W.take 0)).stages i) := by
    simp [run]; exact dormant_initial
  have hb : birthOf (run mOps fOps m0 f0 (W.take 0)) = false := by simp [run, birthOf, initial]
  rw [hb, Bool.false_and]
  exact (dormant_step hd _ _ _).2

theorem ginv_run (W : List (Fin 2)) (cap : ℕ → ℕ → ℕ)
    (hC : ∀ j r, 1 ≤ j → r < 4 → 2 ^ j + (r + 1) * 2 ^ (j - 1) ≤ W.length →
      CapAt mOps fOps m0 f0 W j r (cap j r)) :
    ∀ n, 1 ≤ n → n ≤ W.length → GInv W cap (Nat.log 2 n) n (run mOps fOps m0 f0 (W.take n)) := by
  intro n hn1
  induction n with
  | zero => omega
  | succ n ih =>
    intro hnW
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; exact ginv_one W cap hnW
    · have h := ih hpos (by omega)
      have hI := inv_run mOps fOps m0 f0 (W.take n) (by simp; omega)
      simp only [List.length_take, Nat.min_eq_left (show n ≤ W.length by omega)] at hI
      set k := Nat.log 2 n
      have hk : 2 ^ k ≤ n := Nat.pow_log_le_self 2 (by omega)
      have hkn : n < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
      have hstep := ginv_step hC hk hkn (by omega) hI h
      rcases Nat.lt_or_ge (n + 1) (2 ^ (k + 1)) with hlt | hge
      · rw [show Nat.log 2 (n + 1) = k from Nat.log_eq_of_pow_le_of_lt_pow (by omega) hlt]
        exact hstep.2.1 hlt
      · have heq : n + 1 = 2 ^ (k + 1) := by omega
        rw [show Nat.log 2 (n + 1) = k + 1 by rw [heq, Nat.log_pow (by norm_num)]]
        exact hstep.2.2 heq

theorem clean_run (W : List (Fin 2)) (cap : ℕ → ℕ → ℕ)
    (hC : ∀ j r, 1 ≤ j → r < 4 → 2 ^ j + (r + 1) * 2 ^ (j - 1) ≤ W.length →
      CapAt mOps fOps m0 f0 W j r (cap j r)) :
    ∀ n, n < W.length → ScaWindowFault.ctlViolation (run mOps fOps m0 f0 (W.take n)) = false := by
  intro n hn
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; rfl
  · have h := ginv_run W cap hC n hpos (by omega)
    have hI := inv_run mOps fOps m0 f0 (W.take n) (by simp; omega)
    simp only [List.length_take, Nat.min_eq_left (show n ≤ W.length by omega)] at hI
    exact (ginv_step hC (Nat.pow_log_le_self 2 (by omega))
      (Nat.lt_pow_succ_log_self (by norm_num) n) hn hI h).1

/-- **`hclean` from the flag workers' promise.** -/
theorem hclean_of_contract (hC : ∀ W, FlagsContract mOps fOps m0 f0 W) :
    ∀ u : List (Fin 2), ScaWindowFault.ctlViolation (run mOps fOps m0 f0 u) = false := by
  intro u
  obtain ⟨cap, hcap⟩ := hC (u ++ [0])
  have := clean_run (u ++ [0]) cap hcap u.length (by simp)
  rwa [List.take_left] at this

/-- **`hmiddle` from the flag workers' promise.** -/
theorem hmiddle_of_contract (hC : ∀ W, FlagsContract mOps fOps m0 f0 W) :
    ∀ w : List (Fin 2), 4 ≤ w.length →
      (((run mOps fOps m0 f0 w).stages (idx (Nat.log 2 w.length))).middle = true ↔
        IsPal ((w.drop (stageOf w.length)).take (w.length - 2 * stageOf w.length))) := by
  intro w hw
  obtain ⟨cap, hcap⟩ := hC w
  have h := ginv_run w cap hcap w.length (by omega) le_rfl
  rw [List.take_length] at h
  set n := w.length
  set k := Nat.log 2 n with hkdef
  have hk : 2 ^ k ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hkn : n < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have : 2 ^ (k + 1) ≤ 4 := by
      calc 2 ^ (k + 1) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 4 := by norm_num
    omega
  have hj := h.2.1 hk2
  have hS : 2 ^ (k - 1) = 2 * 2 ^ (k - 1 - 1) := by rw [← pow_succ']; congr 1; omega
  have h2k : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  have hS2 : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
  set S := 2 ^ (k - 1 - 1)
  set d := n - 2 ^ (k - 1)
  have hq2 : 2 ≤ d / S := (Nat.le_div_iff_mul_le (by positivity)).mpr (by omega)
  have hq5 : d / S ≤ 5 := Nat.lt_succ_iff.mp (Nat.div_lt_of_lt_mul (by omega))
  rw [hj.middle, if_pos ⟨hq2, hq5⟩,
    getD_jobBits w _ _ _ (Nat.mod_lt _ (by positivity))]
  have hst : stageOf n = 2 ^ (k - 1) := rfl
  rw [hst]
  have hdm := Nat.div_add_mod d S
  have : (d / S - 2) * S + d % S = n - 2 * 2 ^ (k - 1) := by
    have e : (d / S - 2) * S = d / S * S - 2 * S := by rw [Nat.sub_mul]
    rw [e]
    have := Nat.mul_le_mul_right S hq2
    rw [Nat.mul_comm] at hdm
    omega
  rw [this]

end Final

/-- info: 'PalPeg.ScaWindowPlumbing.hclean_of_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hclean_of_contract

/-- info: 'PalPeg.ScaWindowPlumbing.hmiddle_of_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hmiddle_of_contract

end PalPeg.ScaWindowPlumbing
