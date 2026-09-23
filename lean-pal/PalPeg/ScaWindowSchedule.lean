import PalPeg.ScaWindowPal

/-!
# The window controller's schedule

The unary counters of `WindowPAL` (`history`, `power`, `nextBirth`) and each stage's `half`,
`clock`, `alive`, `interval` evolve independently of the workers. A stage born with `half = S`
has, `d` ticks later, `clock = S - d % S` and `interval = d / S`.
-/
set_option autoImplicit false
namespace PalPeg.ScaWindowSchedule
open PalPeg.ScaWindowPal

/-- A live stage with period `S`, `d` ticks after its birth. -/
def StageAt (st : StageState) (S d : ℕ) : Prop :=
  st.alive = true ∧ st.half = S ∧ st.clock = S - d % S ∧ st.interval.val = d / S

/-- **A birth**: the stage restarts with the given period. -/
theorem stageAt_birth (st : StageState) (S : ℕ) :
    StageAt (advance st true S).1 S 0 := by
  refine ⟨?_, rfl, ?_, ?_⟩ <;> simp [advance]

/-- The fields of a live stage after a tick without birth. -/
theorem advance_live (st : StageState) (src : ℕ) (h : st.alive = true) :
    (advance st false src).1.half = st.half ∧
    (advance st false src).1.clock = (if st.clock - 1 = 0 then st.half else st.clock - 1) ∧
    (advance st false src).1.interval
      = (if st.clock - 1 = 0 then incInterval st.interval else st.interval) ∧
    (advance st false src).1.alive
      = !(decide (st.clock - 1 = 0) && ((incInterval st.interval).val == 6)) := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp only [advance, h, Nat.pred_eq_sub_one, Bool.true_and,
    Bool.false_eq_true, if_false, Bool.or_false] <;> split_ifs <;> simp_all

/-- **One tick of a live stage** that does not reach interval `6`. -/
theorem stageAt_step (st : StageState) (S d src : ℕ) (hS : 1 ≤ S) (h : StageAt st S d)
    (hlive : (d + 1) / S ≤ 5) : StageAt (advance st false src).1 S (d + 1) := by
  obtain ⟨halive, hhalf, hclock, hint⟩ := h
  obtain ⟨hh, hc, hi, ha⟩ := advance_live st src halive
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < S ∧ d = q * S + r :=
    ⟨d / S, d % S, Nat.mod_lt _ (by omega), by rw [Nat.div_add_mod' d S]⟩
  have hmod : (q * S + r) % S = r := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
  have hdiv : (q * S + r) / S = q := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hr, Nat.zero_add]
  rw [hmod] at hclock
  rw [hdiv] at hint
  rcases Nat.lt_or_ge (r + 1) S with hr1 | hr1
  · have hmod' : (q * S + r + 1) % S = r + 1 := by
      rw [Nat.add_assoc, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr1]
    have hdiv' : (q * S + r + 1) / S = q := by
      rw [Nat.add_assoc, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega),
        Nat.div_eq_of_lt hr1, Nat.zero_add]
    have hc0 : st.clock - 1 ≠ 0 := by rw [hclock]; omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [ha]; simp [hc0]
    · rw [hh, hhalf]
    · rw [hc, if_neg hc0, hclock, hmod']; omega
    · rw [hi, if_neg hc0, hint, hdiv']
  · have hrS : r + 1 = S := by omega
    have hmod' : (q * S + r + 1) % S = 0 := by
      rw [Nat.add_assoc, hrS, show q * S + S = (q + 1) * S by ring, Nat.mul_mod_left]
    have hdiv' : (q * S + r + 1) / S = q + 1 := by
      rw [Nat.add_assoc, hrS, show q * S + S = (q + 1) * S by ring,
        Nat.mul_div_cancel _ (by omega)]
    have hc0 : st.clock - 1 = 0 := by rw [hclock]; omega
    rw [hdiv'] at hlive
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [ha]; simp [hc0, incInterval, hint]; omega
    · rw [hh, hhalf]
    · rw [hc, if_pos hc0, hhalf, hmod']; simp
    · rw [hi, if_pos hc0, hdiv']; simp [incInterval, hint]; omega

/-- The schedule part of a stage. -/
def sched (st : StageState) : ℕ × ℕ × Bool × Fin 7 := (st.half, st.clock, st.alive, st.interval)

theorem stageAt_congr {st st' : StageState} (h : sched st = sched st') (S d : ℕ) :
    StageAt st' S d ↔ StageAt st S d := by
  simp only [sched, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp [StageAt, h1, h2, h3, h4]

section
variable {Wm Wf : Type} (mOps : WorkerOps Wm) (fOps : WorkerOps Wf)

/-- The workers' round leaves the schedule alone. -/
theorem stageRound_sched (a : Fin 2) (i j : Fin 2) (s : PalState Wm Wf) :
    sched ((stageRound mOps fOps a i s).stages j) = sched (s.stages j) ∧
    (stageRound mOps fOps a i s).history = s.history ∧
    (stageRound mOps fOps a i s).power = s.power ∧
    (stageRound mOps fOps a i s).nextBirth = s.nextBirth ∧
    (stageRound mOps fOps a i s).powerReady = s.powerReady ∧
    (stageRound mOps fOps a i s).slot = s.slot := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  by_cases hj : j = i
  · subst hj
    simp [stageRound, sched, capture, consume]
  · simp [stageRound, sched, Function.update_of_ne hj]

/-- The birth of this tick. -/
def birthOf (s : PalState Wm Wf) : Bool := s.powerReady && s.nextBirth.pred == 0

theorem tick_sched (a : Fin 2) (s : PalState Wm Wf) :
    (∀ i : Fin 2, sched ((tick mOps fOps s a).stages i)
      = sched (advance (s.stages i) (birthOf s && s.slot == i) s.power).1) ∧
    (tick mOps fOps s a).history = s.history + 1 ∧
    (tick mOps fOps s a).power = (if !s.powerReady || birthOf s then s.history + 1 else s.power) ∧
    (tick mOps fOps s a).nextBirth
      = (if !s.powerReady || birthOf s then s.history + 1
          else if s.powerReady then s.nextBirth.pred else s.nextBirth) ∧
    (tick mOps fOps s a).powerReady = true ∧
    (tick mOps fOps s a).slot = (if birthOf s then s.slot + 1 else s.slot) := by
  refine ⟨fun i => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [tick]
    rw [(stageRound_sched mOps fOps a 1 i _).1, (stageRound_sched mOps fOps a 0 i _).1]
    fin_cases i <;> cases hp : s.powerReady <;> simp [birthOf, hp]
  · simp only [tick]
    rw [(stageRound_sched mOps fOps a 1 0 _).2.1, (stageRound_sched mOps fOps a 0 0 _).2.1]
  · simp only [tick]
    rw [(stageRound_sched mOps fOps a 1 0 _).2.2.1, (stageRound_sched mOps fOps a 0 0 _).2.2.1]
    cases hp : s.powerReady <;> simp [birthOf, hp]
  · simp only [tick]
    rw [(stageRound_sched mOps fOps a 1 0 _).2.2.2.1, (stageRound_sched mOps fOps a 0 0 _).2.2.2.1]
    cases hp : s.powerReady <;> simp [birthOf, hp]
  · simp only [tick]
    rw [(stageRound_sched mOps fOps a 1 0 _).2.2.2.2.1, (stageRound_sched mOps fOps a 0 0 _).2.2.2.2.1]
  · simp only [tick]
    rw [(stageRound_sched mOps fOps a 1 0 _).2.2.2.2.2, (stageRound_sched mOps fOps a 0 0 _).2.2.2.2.2]
    cases hp : s.powerReady <;> simp [birthOf, hp]

/-- The slot of index `m`. -/
def idx (m : ℕ) : Fin 2 := ⟨m % 2, Nat.mod_lt _ (by norm_num)⟩

theorem idx_succ (m : ℕ) : idx (m + 1) = idx m + 1 := by
  apply Fin.ext
  simp only [idx, Fin.val_add]
  omega

theorem idx_add_two (m : ℕ) : idx (m + 2) = idx m := by
  apply Fin.ext
  simp only [idx]
  omega

theorem idx_succ_ne (m : ℕ) : idx m ≠ idx (m + 1) := by
  intro h
  have := congrArg Fin.val h
  simp only [idx] at this
  omega

/-- **The schedule after `n` letters**, with `2^k ≤ n < 2^(k+1)`. -/
def Inv (k n : ℕ) (s : PalState Wm Wf) : Prop :=
  s.history = n ∧ s.powerReady = true ∧ s.power = 2 ^ k ∧ s.nextBirth = 2 ^ (k + 1) - n ∧
  s.slot = idx k ∧
  (1 ≤ k → StageAt (s.stages (idx (k - 1))) (2 ^ (k - 1)) (n - 2 ^ k)) ∧
  (2 ≤ k → StageAt (s.stages (idx k)) (2 ^ (k - 2)) (n - 2 ^ (k - 1)))

theorem inv_first (a : Fin 2) (m0 : Wm) (f0 : Wf) :
    Inv 0 1 (tick mOps fOps (initial m0 f0) a) := by
  obtain ⟨_, hh, hp, hn, hr, hs⟩ := tick_sched mOps fOps a (initial m0 f0)
  refine ⟨?_, hr, ?_, ?_, ?_, fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
  · rw [hh]; rfl
  · rw [hp]; rfl
  · rw [hn]; rfl
  · rw [hs]; simp [birthOf, initial]; rfl

theorem inv_step {k n : ℕ} (a : Fin 2) (s : PalState Wm Wf) (hk : 2 ^ k ≤ n)
    (hnext : n + 1 < 2 ^ (k + 1)) (h : Inv k n s) : Inv k (n + 1) (tick mOps fOps s a) := by
  obtain ⟨hhist, hready, hpow, hnb, hslot, hnew, hold⟩ := h
  obtain ⟨hsched, hh, hp, hn, hr, hs⟩ := tick_sched mOps fOps a s
  have hb : birthOf s = false := by
    simp only [birthOf, hready, hnb, Bool.true_and, Nat.pred_eq_sub_one, beq_eq_false_iff_ne]
    omega
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  refine ⟨?_, hr, ?_, ?_, ?_, fun hk1 => ?_, fun hk2 => ?_⟩
  · rw [hh, hhist]
  · rw [hp, hready, hb]; simpa using hpow
  · rw [hn, hready, hb, hnb]; simp; omega
  · rw [hs, hb, hslot]; rfl
  · rw [← stageAt_congr (hsched _), hb, Bool.false_and, hpow]
    have hS : 2 ^ k = 2 * 2 ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    have := stageAt_step _ (2 ^ (k - 1)) (n - 2 ^ k) (2 ^ k) (Nat.one_le_two_pow) (hnew hk1)
      (Nat.lt_succ_iff.mp (Nat.div_lt_of_lt_mul (by omega)))
    rwa [show n - 2 ^ k + 1 = n + 1 - 2 ^ k by omega] at this
  · rw [← stageAt_congr (hsched _), hb, Bool.false_and, hpow]
    have hS : 2 ^ k = 4 * 2 ^ (k - 2) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
    have hS1 : 2 ^ (k - 1) = 2 * 2 ^ (k - 2) := by
      rw [← pow_succ']; congr 1; omega
    have := stageAt_step _ (2 ^ (k - 2)) (n - 2 ^ (k - 1)) (2 ^ k) (Nat.one_le_two_pow) (hold hk2)
      (Nat.lt_succ_iff.mp (Nat.div_lt_of_lt_mul (by omega)))
    rwa [show n - 2 ^ (k - 1) + 1 = n + 1 - 2 ^ (k - 1) by omega] at this

theorem inv_birth {k n : ℕ} (a : Fin 2) (s : PalState Wm Wf) (hk : 2 ^ k ≤ n)
    (hbirth : n + 1 = 2 ^ (k + 1)) (h : Inv k n s) : Inv (k + 1) (n + 1) (tick mOps fOps s a) := by
  obtain ⟨hhist, hready, hpow, hnb, hslot, hnew, hold⟩ := h
  obtain ⟨hsched, hh, hp, hn, hr, hs⟩ := tick_sched mOps fOps a s
  have hb : birthOf s = true := by
    simp only [birthOf, hready, hnb, Bool.true_and, Nat.pred_eq_sub_one, beq_iff_eq]
    omega
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  have h3 : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by ring
  refine ⟨?_, hr, ?_, ?_, ?_, fun _ => ?_, fun hk2 => ?_⟩
  · rw [hh, hhist]
  · rw [hp, hb, hhist]; simp; omega
  · rw [hn, hb, hhist]; simp; omega
  · rw [hs, hb, hslot, idx_succ]; rfl
  · -- the newborn, in the slot of the old one
    rw [show k + 1 - 1 = k by omega, ← stageAt_congr (hsched _), hb, hslot, hpow]
    simp only [Bool.true_and, beq_self_eq_true]
    rw [show n + 1 - 2 ^ (k + 1) = 0 by omega]
    exact stageAt_birth _ _
  · -- the previous newborn grows old
    have hk1 : 1 ≤ k := by omega
    rw [show k + 1 - 2 = k - 1 by omega, ← stageAt_congr (hsched _), hb, hslot, hpow]
    have hne : (idx k == idx (k + 1)) = false := by
      simpa using idx_succ_ne k
    rw [show idx (k + 1) = idx (k - 1) by rw [show k + 1 = (k - 1) + 2 by omega, idx_add_two]] at hne ⊢
    simp only [Bool.true_and, hne]
    have hS : 2 ^ k = 2 * 2 ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    have := stageAt_step _ (2 ^ (k - 1)) (n - 2 ^ k) (2 ^ k) (Nat.one_le_two_pow) (hnew hk1)
      (Nat.lt_succ_iff.mp (Nat.div_lt_of_lt_mul (by omega)))
    rwa [show n - 2 ^ k + 1 = n + 1 - 2 ^ (k + 1 - 1) by rw [show k + 1 - 1 = k by omega]; omega] at this

theorem run_append (m0 : Wm) (f0 : Wf) (w : List (Fin 2)) (a : Fin 2) :
    run mOps fOps m0 f0 (w ++ [a]) = tick mOps fOps (run mOps fOps m0 f0 w) a := by
  simp [run, List.foldl_append]

/-- **The schedule after any nonempty word.** -/
theorem inv_run (m0 : Wm) (f0 : Wf) (w : List (Fin 2)) (hw : 1 ≤ w.length) :
    Inv (Nat.log 2 w.length) w.length (run mOps fOps m0 f0 w) := by
  induction w using List.reverseRecOn with
  | nil => simp at hw
  | append_singleton w a ih =>
    rw [run_append, List.length_append, List.length_singleton]
    rcases Nat.eq_zero_or_pos w.length with h0 | hpos
    · rw [List.length_eq_zero_iff.mp h0]
      simpa [run] using inv_first mOps fOps a m0 f0
    · have h := ih hpos
      set n := w.length
      set k := Nat.log 2 n
      have hk : 2 ^ k ≤ n := Nat.pow_log_le_self 2 (by omega)
      have hn : n < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
      rcases Nat.lt_or_ge (n + 1) (2 ^ (k + 1)) with hlt | hge
      · have hlog : Nat.log 2 (n + 1) = k :=
          Nat.log_eq_of_pow_le_of_lt_pow (by omega) hlt
        rw [hlog]
        exact inv_step mOps fOps a _ hk hlt h
      · have heq : n + 1 = 2 ^ (k + 1) := by omega
        have hlog : Nat.log 2 (n + 1) = k + 1 := by
          rw [heq, Nat.log_pow (by norm_num)]
        rw [hlog]
        exact inv_birth mOps fOps a _ hk heq h

theorem answering_of_stageAt {st : StageState} {S d : ℕ} (h : StageAt st S d) :
    answering st = (decide (2 ≤ d / S) && decide (d / S ≤ 5)) := by
  obtain ⟨ha, -, -, hi⟩ := h
  simp only [answering, ha, hi, Bool.true_and]
  generalize d / S = q
  rcases q with _ | _ | _ | _ | _ | _ | q <;> simp

/-- **From four letters on, exactly the older stage answers**, and it is the stage born at
`2^(k-1)` with period `2^(k-2)`, where `2^k ≤ n < 2^(k+1)`. -/
theorem answering_run (m0 : Wm) (f0 : Wf) (w : List (Fin 2)) (hw : 4 ≤ w.length) :
    2 ≤ Nat.log 2 w.length ∧
    answering ((run mOps fOps m0 f0 w).stages (idx (Nat.log 2 w.length))) = true ∧
    answering ((run mOps fOps m0 f0 w).stages (idx (Nat.log 2 w.length - 1))) = false ∧
    StageAt ((run mOps fOps m0 f0 w).stages (idx (Nat.log 2 w.length)))
      (2 ^ (Nat.log 2 w.length - 2)) (w.length - 2 ^ (Nat.log 2 w.length - 1)) := by
  obtain ⟨-, -, -, -, -, hnew, hold⟩ := inv_run mOps fOps m0 f0 w (by omega)
  set k := Nat.log 2 w.length with hkdef
  have hk : 2 ^ k ≤ w.length := Nat.pow_log_le_self 2 (by omega)
  have hn : w.length < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hk2 : 2 ≤ k := by
    have := Nat.log_mono_right (b := 2) hw
    rwa [show Nat.log 2 4 = 2 by rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.log_pow (by norm_num)]]
      at this
  have hX : 2 ^ k = 4 * 2 ^ (k - 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  have hY : 2 ^ (k - 1) = 2 * 2 ^ (k - 2) := by
    rw [← pow_succ']; congr 1; omega
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  have hpos : 0 < 2 ^ (k - 2) := Nat.two_pow_pos _
  refine ⟨hk2, ?_, ?_, hold hk2⟩
  · rw [answering_of_stageAt (hold hk2)]
    have h1 : 2 ≤ (w.length - 2 ^ (k - 1)) / 2 ^ (k - 2) :=
      (Nat.le_div_iff_mul_le hpos).mpr (by omega)
    have h2' : (w.length - 2 ^ (k - 1)) / 2 ^ (k - 2) ≤ 5 :=
      Nat.lt_succ_iff.mp (Nat.div_lt_of_lt_mul (by omega))
    simp [h1, h2']
  · rw [answering_of_stageAt (hnew (by omega))]
    have h1 : (w.length - 2 ^ k) / 2 ^ (k - 1) < 2 := Nat.div_lt_of_lt_mul (by omega)
    simp; omega

end

end PalPeg.ScaWindowSchedule
