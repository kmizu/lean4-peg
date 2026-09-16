import PalPeg.GalilScaffoldTopJointRun

/-!
# Existence of the chain watch tick

`GalilScaffoldChainWatch.Tick s true t` is `Internal` (consume once if the
lag is positive) then `Outer` (queue, or consume again if the lag is zero).
Both consumes need `Good` (the verifier can advance and the period symbol
matches the input under it). Under those two `Good` conditions the tick
exists; otherwise the chain breaks (`JointBreak` for the immediate case).
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldChainWatch GalilScaffoldCounter

theorem watch_tick_exists (s : State)
    (h1 : positive s.lag = true → Good s)
    (h2 : ∀ m, Internal s m → zero m.lag = true → Good m) :
    ∃ t, Tick s true t := by
  by_cases hp : positive s.lag = true
  · have hi : Internal s (caught s) := .take s hp (h1 hp)
    by_cases hz : zero (caught s).lag = true
    · exact ⟨_, .step hi (.immediate _ hz (h2 _ hi hz))⟩
    · exact ⟨_, .step hi (.queued _ (Bool.eq_false_iff.mpr hz))⟩
  · have hi : Internal s s := .idle s (Bool.eq_false_iff.mpr hp)
    by_cases hz : zero s.lag = true
    · exact ⟨_, .step hi (.immediate _ hz (h2 _ hi hz))⟩
    · exact ⟨_, .step hi (.queued _ (Bool.eq_false_iff.mpr hz))⟩

/-- The disabled tick exists whenever a positive lag can be consumed. -/
theorem watch_tick_false (s : State) (h1 : positive s.lag = true → Good s) : ∃ t, Tick s false t := by
  by_cases hp : positive s.lag = true
  · exact ⟨_, .step (.take s hp (h1 hp)) (.idle _)⟩
  · exact ⟨s, .step (.idle s (Bool.eq_false_iff.mpr hp)) (.idle s)⟩

#print axioms watch_tick_exists
#print axioms watch_tick_false

end PalPeg.GalilScaffoldChainInputSupply
