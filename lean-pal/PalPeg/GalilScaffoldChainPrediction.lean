import PalPeg.GalilScaffoldChainWatchTrace
import PalPeg.Words

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainPrediction
open GalilScaffoldChainConsume GalilScaffoldChainSweep

/-- Counters and phase do not determine the next prediction; the period
tape and traversal direction do. This also covers mismatching reads. -/
def SamePrediction (s t : State) : Prop := s.period = t.period ∧ s.forward = t.forward

theorem consume_same_prediction {s t : State} (h : SamePrediction s t)
    (seen : Option (Fin 3)) : SamePrediction (consume s seen) (consume t seen) := by
  obtain ⟨hp,hf⟩ := h
  unfold SamePrediction consume
  simp only [hp,hf]
  split <;> simp_all
  all_goals split <;> simp_all

theorem run_same_prediction {s t : State} (h : SamePrediction s t)
    (word : List (Fin 3)) : SamePrediction (run s word) (run t word) := by
  induction word generalizing s t with
  | nil => exact h
  | cons a word ih => exact ih (consume_same_prediction h (some a))

#print axioms run_same_prediction

theorem consume_same_broken {s t : State} (hp : SamePrediction s t)
    (hb : s.broken = t.broken) (seen : Option (Fin 3)) :
    (consume s seen).broken = (consume t seen).broken := by
  obtain ⟨hp,hf⟩ := hp
  unfold consume
  simp only [hp,hf,hb]
  split <;> simp_all
  all_goals split <;> simp_all

theorem run_same_broken {s t : State} (hp : SamePrediction s t)
    (hb : s.broken = t.broken) (word : List (Fin 3)) :
    (run s word).broken = (run t word).broken := by
  induction word generalizing s t with
  | nil => exact hb
  | cons a word ih =>
    exact ih (consume_same_prediction hp (some a)) (consume_same_broken hp hb (some a))

#print axioms run_same_broken

theorem broken_run (s : State) (xs : List (Fin 3)) (hs : s.broken = true) :
    (run s xs).broken = true := by
  induction xs generalizing s with
  | nil => exact hs
  | cons a xs ih =>
    apply ih
    cases ht : symbol s.period.focus with
    | none => simp [consume,ht]
    | some b =>
      by_cases ha : a = b
      all_goals simp [consume,ht,ha,hs]

theorem unbroken_start (s : State) (xs : List (Fin 3)) (hs : (run s xs).broken = false) :
    s.broken = false := by
  cases hb : s.broken
  · rfl
  · have he := broken_run s xs hb
    rw [hs] at he
    contradiction

theorem successful_head (s : State) (a : Fin 3) (xs : List (Fin 3))
    (hs : (run s (a :: xs)).broken = false) : symbol s.period.focus = some a := by
  have hb := unbroken_start (consume s (some a)) xs hs
  cases ht : symbol s.period.focus with
  | none => simp [consume,ht] at hb
  | some b =>
    by_cases ha : a = b
    · simpa [ha] using ht
    · simp [consume,ht,ha] at hb

/-- Successful words from one controller have a unique common prefix. -/
theorem successful_prefix (expected actual : List (Fin 3)) (s : State)
    (he : (run s expected).broken = false) (ha : (run s actual).broken = false)
    (hlen : expected.length ≤ actual.length) : actual.take expected.length = expected := by
  induction expected generalizing actual s with
  | nil => simp
  | cons a expected ih =>
    cases actual with
    | nil => simp at hlen
    | cons b actual =>
      have h1 := successful_head s a expected he
      have h2 := successful_head s b actual ha
      have hab : a = b := by rw [h1] at h2; exact Option.some.inj h2
      subst b
      have ht := ih actual (consume s (some a)) he ha (by simpa using hlen)
      simpa using congrArg (List.cons a) ht

def cycles (word : List (Fin 3)) : ℕ → List (Fin 3)
  | 0 => []
  | k+1 => word ++ cycles word k

theorem successful_next (actual expected : List (Fin 3)) (s : State)
    (ha : (run s actual).broken = false) (he : (run s expected).broken = false)
    (hlen : actual.length < expected.length) :
    symbol (run s actual).period.focus = expected[actual.length]? := by
  induction actual generalizing s expected with
  | nil =>
    cases expected with
    | nil => simp at hlen
    | cons a rest => exact successful_head s a rest he
  | cons a actual ih =>
    cases expected with
    | nil => simp at hlen
    | cons b expected =>
      have h1 := successful_head s a actual ha
      have h2 := successful_head s b expected he
      have hab : a = b := by rw [h1] at h2; exact Option.some.inj h2
      subst b
      exact ih expected (consume s (some a)) ha he (by simpa using hlen)

theorem cycles_length (word : List (Fin 3)) (k : ℕ) :
    (cycles word k).length = k*word.length := by
  induction k with
  | zero => simp [cycles]
  | succ k ih => simp [cycles,ih,Nat.succ_mul,Nat.add_comm]

theorem cycles_index (word : List (Fin 3)) (k i : ℕ)
    (hi : i < (cycles word k).length) :
    (cycles word k)[i]? = word[i % word.length]? := by
  induction k generalizing i with
  | zero => simp [cycles] at hi
  | succ k ih =>
    by_cases hb : i < word.length
    · rw [cycles,List.getElem?_append_left hb,Nat.mod_eq_of_lt hb]
    · have hge : word.length ≤ i := by omega
      have ht : i-word.length < (cycles word k).length := by
        simp only [cycles,List.length_append] at hi
        omega
      rw [cycles,List.getElem?_append_right hge,ih _ ht,← Nat.mod_eq_sub_mod hge]

theorem cycles_period (word : List (Fin 3)) (k : ℕ) :
    HasPeriod (cycles word k) word.length := by
  intro i hi
  rw [cycles_index word k i (by omega),cycles_index word k (i+word.length) hi]
  simp

theorem cycles_run (center b : Fin 3) (xs : List (Fin 3)) (k : ℕ) (s : State)
    (hp : s.period = (ready center xs b).period) (hf : s.forward = true) :
    let t := run s (cycles (bounce center b xs) k)
    t.period = s.period ∧ t.forward = true ∧ t.broken = s.broken := by
  induction k generalizing s with
  | zero => exact ⟨rfl,hf,rfl⟩
  | succ k ih =>
    obtain ⟨hperiod,_,_,_,_,hforward,hbroken⟩ := round_trip center b xs s hp hf
    have ht := ih (run s (bounce center b xs)) (hperiod.trans hp) hforward
    dsimp only at ht
    simp only [cycles,run_append]
    exact ⟨ht.1.trans hperiod,ht.2.1,ht.2.2.trans hbroken⟩

/-- Every finite successful verifier word is a prefix of repeated full
round trips, including words extending beyond the first four boundaries. -/
theorem successful_cycles (center b : Fin 3) (xs actual : List (Fin 3))
    (ha : (run (ready center xs b) actual).broken = false) :
    (cycles (bounce center b xs) actual.length).take actual.length = actual := by
  have he := cycles_run center b xs actual.length (ready center xs b) rfl rfl
  have hb : (run (ready center xs b) (cycles (bounce center b xs) actual.length)).broken = false :=
    he.2.2
  apply successful_prefix actual _ _ ha hb
  rw [cycles_length]
  have hl : 1 ≤ (bounce center b xs).length := by simp [bounce]; omega
  simpa using Nat.mul_le_mul_left actual.length hl

theorem watch_cycles {s t : GalilScaffoldChainWatch.State} {bs : List Bool}
    (hr : GalilScaffoldChainWatch.Run s bs t) (center b : Fin 3) (xs : List (Fin 3))
    (hs : s.machine.control = ready center xs b) :
    ∃ actual, GalilScaffoldChainWatchTrace.Trace s.machine actual t.machine ∧
      (cycles (bounce center b xs) actual.length).take actual.length = actual := by
  obtain ⟨actual,ht,_⟩ := GalilScaffoldChainWatchTrace.run_trace hr
  have hb : (run (ready center xs b) actual).broken = false := by
    rw [← hs,← ht.control,ht.broken,hs]
    rfl
  exact ⟨actual,ht,successful_cycles center b xs actual hb⟩

theorem successful_prediction (center b : Fin 3) (xs actual : List (Fin 3))
    (ha : (run (ready center xs b) actual).broken = false) :
    symbol (run (ready center xs b) actual).period.focus =
      (bounce center b xs)[actual.length % (2*(xs.length+1))]? := by
  let expected := cycles (bounce center b xs) (actual.length+1)
  have he : (run (ready center xs b) expected).broken = false :=
    (cycles_run center b xs (actual.length+1) (ready center xs b) rfl rfl).2.2
  have hsize : (bounce center b xs).length = 2*(xs.length+1) := by simp [bounce]; omega
  have hmul := Nat.mul_le_mul_left (actual.length+1)
    (show 1 ≤ (bounce center b xs).length by omega)
  have hlen : actual.length < expected.length := by
    dsimp only [expected]
    rw [cycles_length]
    omega
  have hn := successful_next actual expected (ready center xs b) ha he hlen
  rw [cycles_index _ _ _ hlen,hsize] at hn
  exact hn

#print axioms successful_prediction

/-- A counter-adjusted continuation retains the original predictor's
absolute phase. Success is required only for the actual continuation. -/
theorem continued_prediction (center b : Fin 3) (xs pre extra : List (Fin 3))
    (s : State) (hp : SamePrediction s (run (ready center xs b) pre))
    (hb : s.broken = (run (ready center xs b) pre).broken)
    (hs : (run s extra).broken = false) :
    symbol (run s extra).period.focus =
      (bounce center b xs)[(pre.length+extra.length) % (2*(xs.length+1))]? := by
  have he := run_same_prediction hp extra
  have hbroken := run_same_broken hp hb extra
  have hfull : (run (ready center xs b) (pre ++ extra)).broken = false := by
    rw [run_append,← hbroken]
    exact hs
  have hpred := successful_prediction center b xs (pre ++ extra) hfull
  rw [run_append,List.length_append] at hpred
  rw [he.1]
  exact hpred

#print axioms continued_prediction

theorem watch_period {s t : GalilScaffoldChainWatch.State} {bs : List Bool}
    (hr : GalilScaffoldChainWatch.Run s bs t) (center b : Fin 3) (xs : List (Fin 3))
    (hs : s.machine.control = ready center xs b) :
    ∃ actual, GalilScaffoldChainWatchTrace.Trace s.machine actual t.machine ∧
      HasPeriod actual (2*(xs.length+1)) := by
  obtain ⟨actual,ht,he⟩ := watch_cycles hr center b xs hs
  refine ⟨actual,ht,?_⟩
  have hp := hasPeriod_take (k := actual.length)
    (cycles_period (bounce center b xs) actual.length)
  rw [he] at hp
  have hl : (bounce center b xs).length = 2*(xs.length+1) := by simp [bounce]; omega
  simpa only [hl] using hp

#print axioms watch_period
#print axioms watch_cycles
#print axioms successful_cycles

theorem watch_phase {s t : GalilScaffoldChainWatch.State} {bs : List Bool}
    (hr : GalilScaffoldChainWatch.Run s bs t) (center b : Fin 3) (xs : List (Fin 3))
    (hs : s.machine.control = ready center xs b)
    (hd : 4*(xs.length+1) ≤ GalilScaffoldCounter.value t.machine.control.distance) :
    t.machine.control.phase = 4 ∧ t.machine.control.broken = false := by
  obtain ⟨actual,ht,_⟩ := GalilScaffoldChainWatchTrace.run_trace hr
  let expected := bounce center b xs ++ bounce center b xs
  have hf := four_boundaries center b xs
  have hex : (run (ready center xs b) expected).broken = false := hf.2.2.2.2.2.2
  have hbroken : t.machine.control.broken = false := by rw [ht.broken,hs]; rfl
  have hac : (run (ready center xs b) actual).broken = false := by
    rw [← hs,← ht.control]; exact hbroken
  have hv := ht.distance
  rw [hs] at hv
  have hz : GalilScaffoldCounter.value (ready center xs b).distance = 0 := rfl
  rw [hz,zero_add] at hv
  have heLen : expected.length = 4*(xs.length+1) := by simp [expected,bounce]; omega
  have hlen : expected.length ≤ actual.length := by rw [heLen]; omega
  have htake := successful_prefix expected actual (ready center xs b) hex hac hlen
  have hsplit : actual = expected ++ actual.drop expected.length := by
    have he := List.take_append_drop expected.length actual
    rw [htake] at he
    exact he.symm
  rw [hsplit] at ht
  have hp := GalilScaffoldChainWatchTrace.four_prefix center b xs
    (actual.drop expected.length) hs ht
  exact ⟨hp.1,hbroken⟩

theorem consume_phase_mono (s : State) (seen : Option (Fin 3)) :
    s.phase.val ≤ (consume s seen).phase.val := by
  cases ht : symbol s.period.focus with
  | none => simp [consume,ht]
  | some a =>
    by_cases he : seen = some a
    · by_cases hb : (GalilScaffoldChainPeriod.isFirst s.period.focus ||
          isLast s.period.focus) = true
      · simp only [consume,ht,he,decide_true,ite_true,hb,advancePhase]
        have := s.phase.isLt
        omega
      · simp [consume,ht,he,hb]
    · simp [consume,ht,he]

theorem run_phase_mono (s : State) (word : List (Fin 3)) :
    s.phase.val ≤ (run s word).phase.val := by
  induction word generalizing s with
  | nil => exact le_refl _
  | cons a word ih => exact (consume_phase_mono s (some a)).trans (ih _)

/-- Immediately before the fourth boundary the phase is still three. -/
theorem before_four_phase (center b : Fin 3) (xs : List (Fin 3)) :
    (run (ready center xs b)
      ((bounce center b xs ++ (xs ++ [b])) ++ xs.reverse)).phase = 3 := by
  have hround := first_round_trip center b xs
  have hf := forward_boundary center b xs (run (ready center xs b) (bounce center b xs))
    hround.1 hround.2.2.2.2.2.1
  have ht := hf.2.2.2.2.2.2
  have hrear := backward_interior xs.reverse [] [.last b] center
    (run (run (ready center xs b) (bounce center b xs)) (xs ++ [b]))
    (ht.trans (rear_after_last xs center b)) hf.2.2.2.2.1
  rw [run_append,run_append]
  rw [hrear.2.2.2.2.1,hf.2.2.2.1]
  change advancePhase (run (ready center xs b)
    ((xs ++ [b]) ++ (xs.reverse ++ [center]))).phase = 3
  rw [hround.2.2.2.2.1]
  rfl

theorem watch_phase_distance {s t : GalilScaffoldChainWatch.State} {bs : List Bool}
    (hr : GalilScaffoldChainWatch.Run s bs t) (center b : Fin 3) (xs : List (Fin 3))
    (hs : s.machine.control = ready center xs b) (hp : t.machine.control.phase = 4) :
    4*(xs.length+1) ≤ GalilScaffoldCounter.value t.machine.control.distance := by
  obtain ⟨actual,ht,_⟩ := GalilScaffoldChainWatchTrace.run_trace hr
  have hv := ht.distance
  rw [hs] at hv
  have hz : GalilScaffoldCounter.value (ready center xs b).distance = 0 := rfl
  rw [hz,zero_add] at hv
  by_contra hsmall
  let pre := (bounce center b xs ++ (xs ++ [b])) ++ xs.reverse
  have hlen : actual.length ≤ pre.length := by
    have hpre : pre.length = 4*(xs.length+1)-1 := by simp [pre,bounce]; omega
    omega
  have hbroken : (run (ready center xs b) actual).broken = false := by
    rw [← hs,← ht.control,ht.broken,hs]
    rfl
  have hex : (run (ready center xs b) pre).broken = false := by
    apply unbroken_start _ [center]
    have hf := (four_boundaries center b xs).2.2.2.2.2.2
    rw [← run_append]
    have he : pre ++ [center] = bounce center b xs ++ bounce center b xs := by
      simp only [pre,bounce,List.append_assoc]
    rw [he]
    exact hf
  have he := successful_prefix actual pre (ready center xs b) hbroken hex hlen
  have hsplit : pre = actual ++ pre.drop actual.length := by
    have h := List.take_append_drop actual.length pre
    rw [he] at h
    exact h.symm
  have hm := run_phase_mono (run (ready center xs b) actual) (pre.drop actual.length)
  rw [← run_append,← hsplit,before_four_phase] at hm
  have hphase : (run (ready center xs b) actual).phase = 4 := by
    rw [← hs,← ht.control,hp]
  rw [hphase] at hm
  contradiction

#print axioms watch_phase_distance

theorem margin_mono {s t : GalilScaffoldChainWatch.State} {bs : List Bool}
    (hr : GalilScaffoldChainWatch.Run s bs t) :
    GalilScaffoldCounter.value s.margin ≤ GalilScaffoldCounter.value t.margin := by
  induction hr with
  | stop => exact le_refl _
  | @next s m t b bs ht hr ih =>
    have hm : GalilScaffoldCounter.value s.margin ≤ GalilScaffoldCounter.value m.margin := by
      cases ht with
      | step hi ho =>
        cases hi <;> cases ho <;>
          simp [GalilScaffoldChainWatch.caught,GalilScaffoldChainWatch.queued,
            GalilScaffoldChainWatch.immediate,GalilScaffoldCounter.inc_value]
    exact hm.trans ih

theorem margin_exact {s t : GalilScaffoldChainWatch.State} {bs : List Bool}
    (hr : GalilScaffoldChainWatch.Run s bs t) :
    GalilScaffoldCounter.value t.margin = GalilScaffoldCounter.value s.margin + (bs.count true : ℤ) := by
  induction hr with
  | stop => simp
  | @next s m t b bs ht hr ih =>
    have hm : GalilScaffoldCounter.value m.margin = GalilScaffoldCounter.value s.margin +
        (if b then 1 else 0) := by
      cases ht with
      | step hi ho =>
        cases hi <;> cases ho <;>
          simp [GalilScaffoldChainWatch.caught,GalilScaffoldChainWatch.queued,
            GalilScaffoldChainWatch.immediate,GalilScaffoldCounter.inc_value]
    cases b <;> simp_all <;> omega

/-- The same clock-bounded successful watch run supplies lag zero,
distance≥4h, its prediction prefix, phase4, and the fresh shift guard. -/
theorem clock_shift {s t : GalilScaffoldChainWatch.State} {bs : List Bool}
    (hr : GalilScaffoldChainWatch.Run s bs t)
    (hc : GalilScaffoldChainWatch.CanonicalState s)
    (center b : Fin 3) (xs : List (Fin 3)) (hs : s.machine.control = ready center xs b)
    (hb : GalilScaffoldChainWatch.balance s = 4*((xs.length+1 : ℕ) : ℤ))
    (hm : 0 ≤ GalilScaffoldCounter.value s.margin + (bs.count true : ℤ))
    (hn : 0 ≤ GalilScaffoldCounter.value s.lag) (k clock : ℕ)
    (hk : GalilScaffoldCounter.value s.lag ≤ k) (hclock : 1 ≤ clock ∧ clock ≤ 2048)
    (available : List Bool) (hlen : available.length = bs.length)
    (hmatched : bs.count true ≤ (GalilScaffoldMatchClock.run 2048 clock available).2)
    (hticks : 2*k+2 ≤ bs.length) :
    GalilScaffoldChainCatch.freshShiftGuard t.machine t.lag t.margin = true := by
  have hz := GalilScaffoldChainLag.clock_catches hr hc hn k clock hk hclock available hlen hmatched hticks
  have hcan := GalilScaffoldChainWatch.run_canonical hr hc
  have hzero := (GalilScaffoldCounter.zero_iff _ hcan.1).mp hz
  have hmargin := margin_exact hr
  have hbalance := GalilScaffoldChainWatch.run_balance hr
  rw [hb] at hbalance
  unfold GalilScaffoldChainWatch.balance at hbalance
  have hd : 4*(xs.length+1) ≤ GalilScaffoldCounter.value t.machine.control.distance := by omega
  obtain ⟨hp,hbroken⟩ := watch_phase hr center b xs hs hd
  exact GalilScaffoldChainWatch.shift_ready hr hc (xs.length+1) hb hz (by simpa using hd) hp hbroken

/-- Negative starting margin is paid by successful compares of the same
clock. Equality of matched/compare counts excludes intervening failed
compares or shifts; it is an explicit online correspondence obligation. -/
theorem clock_shift_supply {s t : GalilScaffoldChainWatch.State} {bs : List Bool}
    (hr : GalilScaffoldChainWatch.Run s bs t)
    (hc : GalilScaffoldChainWatch.CanonicalState s)
    (center b : Fin 3) (xs : List (Fin 3)) (hs : s.machine.control = ready center xs b)
    (hb : GalilScaffoldChainWatch.balance s = 4*((xs.length+1 : ℕ) : ℤ))
    (deficit : ℕ) (hm : -(deficit : ℤ) ≤ GalilScaffoldCounter.value s.margin)
    (hn : 0 ≤ GalilScaffoldCounter.value s.lag) (k clock : ℕ)
    (hk : GalilScaffoldCounter.value s.lag ≤ k) (hclock : 1 ≤ clock ∧ clock ≤ 2048)
    (available : List Bool) (hlen : available.length = bs.length)
    (hmatched : bs.count true = (GalilScaffoldMatchClock.run 2048 clock available).2)
    (hsupply : 2048*deficit ≤ available.count true) (hticks : 2*k+2 ≤ bs.length) :
    GalilScaffoldChainCatch.freshShiftGuard t.machine t.lag t.margin = true := by
  have hi := GalilScaffoldMatchClock.run_invariant 2048 clock available (by omega) hclock
  have hmcount : deficit ≤ bs.count true := by omega
  apply clock_shift hr hc center b xs hs hb _ hn k clock hk hclock available hlen (le_of_eq hmatched) hticks
  omega

/-- Ready distance=0 and preparation balance=4h bound any negative margin
by 4h. Thus its credit supply can be stated without a margin premise. -/
theorem clock_shift_ready {s t : GalilScaffoldChainWatch.State} {bs : List Bool}
    (hr : GalilScaffoldChainWatch.Run s bs t)
    (hc : GalilScaffoldChainWatch.CanonicalState s)
    (center b : Fin 3) (xs : List (Fin 3)) (hs : s.machine.control = ready center xs b)
    (hb : GalilScaffoldChainWatch.balance s = 4*((xs.length+1 : ℕ) : ℤ))
    (hn : 0 ≤ GalilScaffoldCounter.value s.lag) (k clock : ℕ)
    (hk : GalilScaffoldCounter.value s.lag ≤ k) (hclock : 1 ≤ clock ∧ clock ≤ 2048)
    (available : List Bool) (hlen : available.length = bs.length)
    (hmatched : bs.count true = (GalilScaffoldMatchClock.run 2048 clock available).2)
    (hsupply : 8192*(xs.length+1) ≤ available.count true) (hticks : 2*k+2 ≤ bs.length) :
    GalilScaffoldChainCatch.freshShiftGuard t.machine t.lag t.margin = true := by
  have hd : GalilScaffoldCounter.value s.machine.control.distance = 0 := by rw [hs]; rfl
  have hm : -((4*(xs.length+1) : ℕ) : ℤ) ≤ GalilScaffoldCounter.value s.margin := by
    unfold GalilScaffoldChainWatch.balance at hb
    rw [hd] at hb
    push_cast
    omega
  apply clock_shift_supply hr hc center b xs hs hb (4*(xs.length+1)) hm hn k clock hk hclock
    available hlen hmatched _ hticks
  omega

#print axioms clock_shift_ready
#print axioms clock_shift_supply
#print axioms margin_exact
#print axioms clock_shift
#print axioms watch_phase
#print axioms successful_prefix
end PalPeg.GalilScaffoldChainPrediction
