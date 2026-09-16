import PalPeg.GalilScaffoldMatchClock
import PalPeg.GalilScaffoldGrow

set_option autoImplicit false
namespace PalPeg.GalilScaffoldAdvanceClock

/-- Each event contains scan availability and Search.active && chain.idle.
The latter is sampled after search.tick, as in the Scala caller. -/
def advances (delay : ℕ) : ℕ → List (Bool × Bool) → List Bool
  | _,[] => []
  | clock,(available,eligible) :: es =>
      (available && decide (clock = 1) && eligible) ::
        advances delay (if available then if clock = 1 then delay else clock-1 else clock) es

theorem advances_length (delay clock : ℕ) (es : List (Bool × Bool)) :
    (advances delay clock es).length = es.length := by
  induction es generalizing clock with
  | nil => rfl
  | cons e es ih => simp [advances,ih]

theorem advances_le_compares (delay clock : ℕ) (es : List (Bool × Bool)) :
    (advances delay clock es).count true ≤
      (GalilScaffoldMatchClock.run delay clock (es.map Prod.fst)).2 := by
  induction es generalizing clock with
  | nil => simp [advances,GalilScaffoldMatchClock.run]
  | cons e es ih =>
    rcases e with ⟨available,eligible⟩
    cases available <;> cases eligible <;> by_cases hc : clock = 1 <;>
      simp [advances,GalilScaffoldMatchClock.run,hc] <;>
      first | exact ih _ | (have := ih delay; omega)

theorem advances_budget (delay : ℕ) (es : List (Bool × Bool)) (hd : 0 < delay) :
    (advances delay delay es).count true * delay ≤ (es.map Prod.fst).count true := by
  exact (Nat.mul_le_mul_right delay (advances_le_compares delay delay es)).trans
    (GalilScaffoldMatchClock.compare_budget delay _ hd)

/-- Before the first comparison after reset, grow incurs no advance debt. -/
theorem grow_before_first_compare (delay g : ℕ) (es : List (Bool × Bool))
    (span debt : GalilScaffoldCounter.Counter) (hd : 0 < delay)
    (he : es.length < delay) (hg : es.length ≤ g) :
    GalilScaffoldCounter.value
      (GalilScaffoldGrow.paced (advances delay delay es)
        ⟨GalilScaffoldCounter.ofNat g,span,debt⟩).debt =
      GalilScaffoldCounter.value debt+2*es.length := by
  have hb := advances_budget delay es hd
  have hl : (es.map Prod.fst).count true ≤ es.length := by
    simpa using List.count_le_length (l := es.map Prod.fst) (a := true)
  have hz : (advances delay delay es).count true = 0 := by
    by_contra hn
    have hm := Nat.mul_le_mul_right delay (show 1 ≤ (advances delay delay es).count true by omega)
    simp only [Nat.one_mul] at hm
    omega
  have hv := (GalilScaffoldGrow.paced_values (advances delay delay es) g span debt
    (by simpa [advances_length] using hg)).2.2
  simpa [advances_length,hz] using hv

/-- Initial-stage barrier from the explicit new clock calibration.
The source radius contract and real stage-duration bound remain premises. -/
theorem first_stage_barrier (r radius : ℕ) (es : List (Bool × Bool))
    (hr : 3*radius ≤ 5*r) (ht : es.length ≤ 63*(8*max r 1)) :
    radius + (advances 2048 2048 es).count true ≤ 2*max r 1 := by
  have hb := advances_budget 2048 es (by decide)
  have hl : (es.map Prod.fst).count true ≤ es.length := by
    simpa using List.count_le_length (l := es.map Prod.fst) (a := true)
  by_cases hz : r = 0
  · subst r
    simp only [Nat.max_eq_right (by omega : 0 ≤ 1)] at ht ⊢
    omega
  · rw [max_eq_left (by omega : 1 ≤ r)] at ht ⊢
    omega

theorem first_stage_debt (r radius : ℕ) (es : List (Bool × Bool))
    (debt : GalilScaffoldCounter.Counter)
    (hr : 3*radius ≤ 5*r) (ht : es.length ≤ 63*(8*max r 1))
    (hc : GalilScaffoldCounter.Canonical debt)
    (hbalance : GalilScaffoldCounter.value debt =
      -(radius : ℤ)+2*(max r 1 : ℕ)-(advances 2048 2048 es).count true) :
    GalilScaffoldCounter.negative debt ≠ true := by
  have hb := first_stage_barrier r radius es hr ht
  have hn : 0 ≤ GalilScaffoldCounter.value debt := by
    rw [hbalance]
    omega
  intro he
  have := (GalilScaffoldCounter.negative_iff debt hc).mp he
  omega

/-- Later stages allow an immediately due comparison: the clock is not reset. -/
theorem later_stage_advances (span clock : ℕ) (es : List (Bool × Bool))
    (hs : 16 ≤ span) (hc : 1 ≤ clock ∧ clock ≤ 2048)
    (ht : es.length ≤ 63*span) :
    (advances 2048 clock es).count true ≤ span/8 := by
  have ha := advances_le_compares 2048 clock es
  have hi := GalilScaffoldMatchClock.run_invariant 2048 clock (es.map Prod.fst) (by decide) hc
  have hl : (es.map Prod.fst).count true ≤ es.length := by
    simpa using List.count_le_length (l := es.map Prod.fst) (a := true)
  omega

theorem advances_append (delay clock : ℕ) (es fs : List (Bool × Bool)) :
    advances delay clock (es++fs) = advances delay clock es ++
      advances delay (GalilScaffoldMatchClock.run delay clock (es.map Prod.fst)).1 fs := by
  induction es generalizing clock with
  | nil => rfl
  | cons e es ih =>
    rcases e with ⟨a,b⟩
    cases a <;> by_cases hc : clock = 1 <;>
      simp [advances,GalilScaffoldMatchClock.run,hc,ih]

theorem advances_take (delay clock n : ℕ) (es : List (Bool × Bool)) :
    advances delay clock (es.take n) = (advances delay clock es).take n := by
  induction n generalizing clock es with
  | zero => rfl
  | succ n ih =>
    cases es with
    | nil => rfl
    | cons e es =>
      rcases e with ⟨a,b⟩
      simp [advances,ih]

theorem eligible_compares (delay clock : ℕ) (bs : List Bool) :
    (advances delay clock (bs.map (fun b => (b,true)))).count true =
      (GalilScaffoldMatchClock.run delay clock bs).2 := by
  induction bs generalizing clock with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> by_cases hc : clock = 1 <;>
      simp [advances,GalilScaffoldMatchClock.run,hc,ih]

/-- Enough available ticks supply k advances when every comparison is eligible. -/
theorem eligible_supply (delay clock k : ℕ) (bs : List Bool)
    (hd : 0 < delay) (hc : 1 ≤ clock ∧ clock ≤ delay)
    (hb : k*delay ≤ bs.count true) :
    k ≤ (advances delay clock (bs.map (fun b => (b,true)))).count true := by
  rw [eligible_compares]
  have hi := GalilScaffoldMatchClock.run_invariant delay clock bs hd hc
  by_contra hn
  have hm := Nat.mul_le_mul_right delay
    (show (GalilScaffoldMatchClock.run delay clock bs).2+1 ≤ k by omega)
  simp only [Nat.add_mul,Nat.one_mul] at hm
  omega

#print axioms eligible_supply
#print axioms advances_append
#print axioms later_stage_advances
#print axioms first_stage_debt
#print axioms advances_budget
#print axioms grow_before_first_compare
end PalPeg.GalilScaffoldAdvanceClock
