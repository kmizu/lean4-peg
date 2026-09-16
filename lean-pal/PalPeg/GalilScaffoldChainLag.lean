import PalPeg.GalilScaffoldChainWatch
import PalPeg.GalilScaffoldMatchClock

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainLag
open GalilScaffoldChainWatch GalilScaffoldCounter

theorem tick_lag {s t : State} {b : Bool} (hr : Tick s b t)
    (hc : CanonicalState s) (hn : 0 ≤ value s.lag) :
    0 ≤ value t.lag ∧ value t.lag ≤ max 0 (value s.lag - (if b then 0 else 1)) := by
  cases hr with
  | step hi ho =>
    cases hi with
    | idle hz =>
      have hp := positive_iff s.lag hc.1
      rw [hz] at hp
      have hv : value s.lag = 0 := by simp at hp; omega
      cases ho with
      | idle => simp [hv]
      | queued hz =>
        have he := (zero_iff s.lag hc.1).mpr hv
        rw [hz] at he
        contradiction
      | immediate hz hg => simp [immediate,hv]
    | take hp hg =>
      have hv := (positive_iff s.lag hc.1).mp hp
      cases ho with
      | idle => simp only [caught,dec_value]; simp; omega
      | queued hz => simp [queued,caught,inc_value,dec_value]; omega
      | immediate hz hg => simp [immediate,caught,dec_value]; omega

/-- Every non-matched tick pays down one unit until lag reaches zero;
matched ticks cannot increase lag. The same successful Run supplies the count. -/
theorem run_lag {s t : State} {bs : List Bool} (hr : Run s bs t)
    (hc : CanonicalState s) (hn : 0 ≤ value s.lag) :
    0 ≤ value t.lag ∧ value t.lag ≤ max 0 (value s.lag - (bs.count false : ℤ)) := by
  induction hr with
  | stop s => simp; omega
  | @next s m t b bs ht hr ih =>
    have hm := tick_lag ht hc hn
    have hcan : CanonicalState m := by
      cases ht with
      | step hi ho => exact outer_canonical ho (internal_canonical hi hc)
    have htail := ih hcan hm.1
    cases b <;> simp_all <;> omega

theorem catches {s t : State} {bs : List Bool} (hr : Run s bs t)
    (hc : CanonicalState s) (hn : 0 ≤ value s.lag)
    (hsupply : value s.lag ≤ (bs.count false : ℤ)) : zero t.lag = true := by
  have hl := run_lag hr hc hn
  have hcan := run_canonical hr hc
  apply (zero_iff t.lag hcan.1).mpr
  omega

theorem bool_counts (bs : List Bool) : bs.count true + bs.count false = bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [List.count_cons] <;> omega

/-- Conservative wall-tick bound within a continuous enabled successful
watch interval. Matched events are a subset of the same clock's compares;
arbitrary availability and any initial clock phase are allowed. -/
theorem clock_catches {s t : State} {bs : List Bool} (hr : Run s bs t)
    (hc : CanonicalState s) (hn : 0 ≤ value s.lag) (k clock : ℕ)
    (hk : value s.lag ≤ k) (hclock : 1 ≤ clock ∧ clock ≤ 2048)
    (available : List Bool) (hlen : available.length = bs.length)
    (hmatched : bs.count true ≤ (GalilScaffoldMatchClock.run 2048 clock available).2)
    (hticks : 2*k+2 ≤ bs.length) : zero t.lag = true := by
  have hi := GalilScaffoldMatchClock.run_invariant 2048 clock available (by omega) hclock
  have ha := List.count_le_length (l := available) (a := true)
  have hb := bool_counts bs
  apply catches hr hc hn
  omega

#print axioms clock_catches
#print axioms catches
#print axioms run_lag
end PalPeg.GalilScaffoldChainLag
