import PalPeg.GalilScaffoldChainPrediction

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainRestart
open GalilScaffoldChainConsume GalilScaffoldCounter

def Ordered (s : State) : Prop :=
  value s.last ≤ value s.boundary ∧ value s.boundary ≤ value s.distance

theorem consume_order (s : State) (seen : Option (Fin 3)) (hs : Ordered s) :
    Ordered (consume s seen) ∧ value s.last ≤ value (consume s seen).last := by
  cases ht : symbol s.period.focus with
  | none => simpa [consume,ht,Ordered] using And.intro hs (le_refl (value s.last))
  | some a =>
    by_cases ha : seen = some a
    · by_cases hb : (GalilScaffoldChainPeriod.isFirst s.period.focus || isLast s.period.focus) = true
      all_goals simp [consume,ht,ha,hb,Ordered,inc_value] at * <;> omega
    · simpa [consume,ht,ha,Ordered] using And.intro hs (le_refl (value s.last))

theorem run_order (s : State) (xs : List (Fin 3)) (hs : Ordered s) :
    Ordered (GalilScaffoldChainSweep.run s xs) ∧
      value s.last ≤ value (GalilScaffoldChainSweep.run s xs).last := by
  induction xs generalizing s with
  | nil => exact ⟨hs,le_refl _⟩
  | cons a xs ih =>
    have hh := consume_order s (some a) hs
    have ht := ih (consume s (some a)) hh.1
    exact ⟨ht.1,hh.2.trans ht.2⟩

theorem consume_canonical (s : State) (seen : Option (Fin 3))
    (hl : Canonical s.last) (hb : Canonical s.boundary) (hd : Canonical s.distance) :
    Canonical (consume s seen).last ∧ Canonical (consume s seen).boundary ∧
      Canonical (consume s seen).distance := by
  have hi := inc_canonical s.distance hd
  cases ht : symbol s.period.focus with
  | none => simpa [consume,ht] using And.intro hl (And.intro hb hd)
  | some a =>
    by_cases ha : seen = some a
    · by_cases he : (GalilScaffoldChainPeriod.isFirst s.period.focus || isLast s.period.focus) = true
      all_goals simp [consume,ht,ha,he,hl,hb,hi]
    · simpa [consume,ht,ha] using And.intro hl (And.intro hb hd)

theorem run_canonical (s : State) (xs : List (Fin 3))
    (hl : Canonical s.last) (hb : Canonical s.boundary) (hd : Canonical s.distance) :
    Canonical (GalilScaffoldChainSweep.run s xs).last ∧
    Canonical (GalilScaffoldChainSweep.run s xs).boundary ∧
    Canonical (GalilScaffoldChainSweep.run s xs).distance := by
  induction xs generalizing s with
  | nil => exact ⟨hl,hb,hd⟩
  | cons a xs ih =>
    have hc := consume_canonical s (some a) hl hb hd
    exact ih (consume s (some a)) hc.1 hc.2.1 hc.2.2

/-- After the first complete bounce last=h>0. Any further consumes,
including a failing one, preserve positivity of last. -/
theorem last_positive_after_bounce (center b : Fin 3) (xs suffix : List (Fin 3)) :
    positive (GalilScaffoldChainSweep.run (ready center xs b)
      (GalilScaffoldChainSweep.bounce center b xs ++ suffix)).last = true := by
  let mid := GalilScaffoldChainSweep.run (ready center xs b) (GalilScaffoldChainSweep.bounce center b xs)
  have hmid := GalilScaffoldChainSweep.first_round_trip center b xs
  change mid.period = _ ∧ _ at hmid
  have ho : Ordered (ready center xs b) := by simp [Ordered,ready,reset,value]
  have hm := run_order (ready center xs b) (GalilScaffoldChainSweep.bounce center b xs) ho
  have ht := run_order mid suffix hm.1
  have hc := run_canonical (ready center xs b)
    (GalilScaffoldChainSweep.bounce center b xs ++ suffix) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
  apply (positive_iff _ hc.1).mpr
  rw [GalilScaffoldChainSweep.run_append]
  have hl : value mid.last = xs.length+1 := hmid.2.2.2.1
  change 0 < value (GalilScaffoldChainSweep.run mid suffix).last
  omega

/-- Ready outer consume failure after a full bounce. Margin.inc occurs
even on failure, so an entry margin of -1 is sufficient for restart.
The seen symbol still needs to be supplied by the actual moved verifier. -/
theorem failed_outer_restart (center b : Fin 3) (xs suffix : List (Fin 3))
    (credits : GalilScaffoldChainCredits.State) (seen : Option (Fin 3)) (a : Fin 3)
    (ht : symbol (GalilScaffoldChainSweep.run (ready center xs b)
      (GalilScaffoldChainSweep.bounce center b xs ++ suffix)).period.focus = some a)
    (hne : seen ≠ some a) (hz : zero credits.lag = true)
    (hc : Canonical credits.margin) (hm : -1 ≤ value credits.margin) :
    let s := GalilScaffoldChainSweep.run (ready center xs b)
      (GalilScaffoldChainSweep.bounce center b xs ++ suffix)
    let result := outerMatched s credits true seen
    result.1.broken = true ∧ negative result.2.margin = false ∧
      positive result.1.last = true ∧ zero result.2.lag = true := by
  let s := GalilScaffoldChainSweep.run (ready center xs b)
    (GalilScaffoldChainSweep.bounce center b xs ++ suffix)
  have hf := outer_zero_mismatch s credits a seen ht hne hz
  have hl := last_positive_after_bounce center b xs suffix
  have hn : negative (inc credits.margin) = false := by
    cases he : negative (inc credits.margin)
    · rfl
    · have hv := (negative_iff _ (inc_canonical _ hc)).mp he
      rw [inc_value] at hv
      omega
  dsimp only
  change (outerMatched s credits true seen).1.broken = true ∧ _
  rw [hf,outer_zero s credits seen hz]
  exact ⟨rfl,hn,hl,hz⟩

theorem watch_last_positive {s t : GalilScaffoldChainWatch.State} {bs : List Bool}
    (hr : GalilScaffoldChainWatch.Run s bs t) (center b : Fin 3) (xs : List (Fin 3))
    (hs : s.machine.control = ready center xs b)
    (hd : 2*(xs.length+1) ≤ value t.machine.control.distance) :
    positive t.machine.control.last = true := by
  obtain ⟨actual,ht,_⟩ := GalilScaffoldChainWatchTrace.run_trace hr
  let expected := GalilScaffoldChainSweep.bounce center b xs
  have he : (GalilScaffoldChainSweep.run (ready center xs b) expected).broken = false :=
    (GalilScaffoldChainSweep.first_round_trip center b xs).2.2.2.2.2.2
  have ha : (GalilScaffoldChainSweep.run (ready center xs b) actual).broken = false := by
    rw [← hs,← ht.control,ht.broken,hs]; rfl
  have hv := ht.distance
  rw [hs] at hv
  have hz : value (ready center xs b).distance = 0 := rfl
  rw [hz,zero_add] at hv
  have hlen : expected.length ≤ actual.length := by
    have hl : expected.length = 2*(xs.length+1) := by simp [expected,GalilScaffoldChainSweep.bounce]; omega
    rw [hl]; omega
  have hp := GalilScaffoldChainPrediction.successful_prefix expected actual (ready center xs b) he ha hlen
  have hsplit : actual = expected ++ actual.drop expected.length := by
    have hh := List.take_append_drop expected.length actual
    rw [hp] at hh
    exact hh.symm
  rw [ht.control,hs,hsplit]
  exact last_positive_after_bounce center b xs (actual.drop expected.length)

/-- After enough successful watch distance, a subsequent ready mismatch
of the actual moved verifier meets all restart assertions. Margin and
last conditions are derived from that same prefix, not supplied anew. -/
theorem failed_after_watch {s t : GalilScaffoldChainWatch.State} {bs : List Bool}
    (hr : GalilScaffoldChainWatch.Run s bs t)
    (hc : GalilScaffoldChainWatch.CanonicalState s)
    (center b : Fin 3) (xs : List (Fin 3)) (hs : s.machine.control = ready center xs b)
    (hb : GalilScaffoldChainWatch.balance s = 4*((xs.length+1 : ℕ) : ℤ))
    (hz : zero t.lag = true) (hd : 4*(xs.length+1)-1 ≤ value t.machine.control.distance)
    (a : Fin 3) (hp : GalilScaffoldChainVerifier.canRight t.machine.verifier)
    (ht : symbol t.machine.control.period.focus = some a)
    (hne : GalilScaffoldInputHead.read (GalilScaffoldChainVerifier.right t.machine.verifier) ≠ some a) :
    let moved := GalilScaffoldChainVerifier.right t.machine.verifier
    let result := outerMatched t.machine.control ⟨t.margin,t.lag⟩ true (GalilScaffoldInputHead.read moved)
    GalilScaffoldChainVerifier.Right t.machine.verifier moved ∧
    result.1.broken = true ∧ negative result.2.margin = false ∧
      positive result.1.last = true ∧ zero result.2.lag = true := by
  have hcan := GalilScaffoldChainWatch.run_canonical hr hc
  have hzero := (zero_iff _ hcan.1).mp hz
  have hbal := GalilScaffoldChainWatch.run_balance hr
  rw [hb] at hbal
  unfold GalilScaffoldChainWatch.balance at hbal
  have hm : -1 ≤ value t.margin := by omega
  have hl := watch_last_positive hr center b xs hs (by omega)
  have hneg : negative (inc t.margin) = false := by
    cases he : negative (inc t.margin)
    · rfl
    · have hv := (negative_iff _ (inc_canonical _ hcan.2)).mp he
      rw [inc_value] at hv
      omega
  have hf := outer_zero_mismatch t.machine.control ⟨t.margin,t.lag⟩ a _ ht hne hz
  dsimp only
  refine ⟨GalilScaffoldChainVerifier.right_realize _ hp,?_⟩
  rw [hf,outer_zero t.machine.control ⟨t.margin,t.lag⟩ _ hz]
  exact ⟨rfl,hneg,hl,hz⟩

#print axioms failed_after_watch
#print axioms watch_last_positive
#print axioms failed_outer_restart
#print axioms last_positive_after_bounce
#print axioms run_order
end PalPeg.GalilScaffoldChainRestart
