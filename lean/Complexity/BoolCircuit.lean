/-! Numbered Boolean circuits in evaluation order. Wire indices refer to
earlier gates in well-formed circuits. Out-of-range wires default to false,
so evaluation is defined even without the well-formedness condition. -/
namespace Complexity.BoolCircuit

inductive Gate where
  | bit (value : Bool)
  | neg (wire : Nat)
  | conj (left right : Nat)
  deriving DecidableEq, Repr

def Gate.eval (values : List Bool) : Gate → Bool
  | .bit b => b
  | .neg i => !(values.getD i false)
  | .conj i j => values.getD i false && values.getD j false

def Gate.Before (bound : Nat) : Gate → Prop
  | .bit _ => True
  | .neg i => i < bound
  | .conj i j => i < bound ∧ j < bound

def WellFormedFrom : Nat → List Gate → Prop
  | _, [] => True
  | n, g::gs => g.Before n ∧ WellFormedFrom (n+1) gs

def WellFormed (gates : List Gate) : Prop := WellFormedFrom 0 gates

def run (initial : List Bool) (gates : List Gate) : List Bool :=
  gates.foldl (fun values gate => values ++ [gate.eval values]) initial

def values (gates : List Gate) : List Bool := run [] gates

theorem run_length (gates : List Gate) (initial : List Bool) :
    (run initial gates).length = initial.length + gates.length := by
  induction gates generalizing initial with
  | nil => simp [run]
  | cons g gs ih => simpa [run,Nat.add_assoc,Nat.add_comm 1] using ih (initial ++ [g.eval initial])

theorem values_length (gates : List Gate) : (values gates).length = gates.length := by
  simpa only [values,List.length_nil,Nat.zero_add] using run_length gates []

theorem before_mono {g : Gate} {n m : Nat} (h : g.Before n) (hn : n ≤ m) : g.Before m := by
  cases g <;> simp only [Gate.Before] at * <;> omega

theorem wellFormedFrom_bound {n : Nat} {gates : List Gate} (h : WellFormedFrom n gates) :
    ∀ g ∈ gates, g.Before (n + gates.length) := by
  induction gates generalizing n with
  | nil => simp
  | cons g gs ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact before_mono h.1 (by simp)
    · simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1] using ih h.2 a ha

theorem wellFormed_bound {gates : List Gate} (h : WellFormed gates) :
    ∀ g ∈ gates, g.Before gates.length := by
  simpa only [Nat.zero_add] using wellFormedFrom_bound h

end Complexity.BoolCircuit
