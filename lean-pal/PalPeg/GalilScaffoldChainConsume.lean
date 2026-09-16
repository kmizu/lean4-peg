import PalPeg.GalilScaffoldChainReady

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainConsume
open GalilScaffoldChainPeriod GalilScaffoldCounter

def symbol : Token → Option (Fin 3)
  | .plain a | .first a | .last a => some a
  | _ => none

def isLast : Token → Bool
  | .last _ => true
  | _ => false

structure State where
  period : Tape
  distance : Counter
  boundary : Counter
  last : Counter
  phase : Fin 5
  forward : Bool
  broken : Bool

def advancePhase (p : Fin 5) : Fin 5 := ⟨min 4 (p.val+1), by omega⟩

/-- Enabled consume, after verifier.right. `seen` must be supplied by that
same moved verifier. Absent/invalid period tokens never match. -/
def consume (s : State) (seen : Option (Fin 3)) : State :=
  let same := match symbol s.period.focus with
    | none => false
    | some a => decide (seen = some a)
  if same then
    let distance := inc s.distance
    let boundaryEvent := isFirst s.period.focus || isLast s.period.focus
    let forward := if boundaryEvent then isFirst s.period.focus else s.forward
    {s with distance := distance, last := if boundaryEvent then s.boundary else s.last, boundary := if boundaryEvent then distance else s.boundary, phase := if boundaryEvent then advancePhase s.phase else s.phase, forward := forward, period := if forward then moveRight s.period else moveLeft s.period}
  else {s with broken := true}

theorem mismatch (s : State) (a : Fin 3) (seen : Option (Fin 3))
    (ht : symbol s.period.focus = some a) (hne : seen ≠ some a) :
    consume s seen = {s with broken := true} := by simp [consume, ht, hne]

theorem plain (s : State) (a : Fin 3) (ht : s.period.focus = .plain a) :
    consume s (some a) = {s with distance := inc s.distance, period := if s.forward then moveRight s.period else moveLeft s.period} := by
  simp [consume, ht, symbol, isFirst, isLast]

theorem first (s : State) (a : Fin 3) (ht : s.period.focus = .first a) :
    consume s (some a) = {s with distance := inc s.distance, last := s.boundary, boundary := inc s.distance, phase := advancePhase s.phase, forward := true, period := moveRight s.period} := by
  simp [consume, ht, symbol, isFirst, isLast]

theorem last (s : State) (a : Fin 3) (ht : s.period.focus = .last a) :
    consume s (some a) = {s with distance := inc s.distance, last := s.boundary, boundary := inc s.distance, phase := advancePhase s.phase, forward := false, period := moveLeft s.period} := by
  simp [consume, ht, symbol, isFirst, isLast]

def ready (center : Fin 3) (ys : List (Fin 3)) (b : Fin 3) : State :=
  ⟨moveRight ⟨[], .first center, ys.map Token.plain ++ [.last b]⟩,
    reset,reset,reset,0,true,false⟩

/-- The first prediction after back is a real token, even for semiperiod 1. -/
theorem ready_symbol (center b : Fin 3) (ys : List (Fin 3)) :
    symbol (ready center ys b).period.focus = (ys ++ [b]).head? := by
  cases ys <;> rfl

/-- Semiperiod 1 starts directly on LAST: the first successful consume
turns left and records boundary 1, rather than taking the plain branch. -/
theorem ready_one (center b : Fin 3) :
    (consume (ready center [] b) (some b)).period =
      ⟨[], .first center, [.last b]⟩ ∧
    value (consume (ready center [] b) (some b)).boundary = 1 ∧
    (consume (ready center [] b) (some b)).forward = false := by
  rw [last (ready center [] b) b rfl]
  simp [ready, moveRight, moveLeft, inc, reset, value]

/-- Longer periods begin with a plain symbol and move right without
raising the boundary phase. -/
theorem ready_long (center a b : Fin 3) (ys : List (Fin 3)) :
    (consume (ready center (a :: ys) b) (some a)).phase = 0 ∧
    (consume (ready center (a :: ys) b) (some a)).forward = true ∧
    value (consume (ready center (a :: ys) b) (some a)).distance = 1 := by
  rw [plain (ready center (a :: ys) b) a rfl]
  simp [ready, inc, reset, value]

/-- The outer matched dispatch at fresh watch entry, where only=false.
`seen` is the read after the verifier move if ready consume is enabled. -/
def outerMatched (s : State) (credits : GalilScaffoldChainCredits.State)
    (enabled : Bool) (seen : Option (Fin 3)) : State × GalilScaffoldChainCredits.State :=
  if enabled then
    if zero credits.lag then
      (consume s seen, {credits with margin := inc credits.margin})
    else (s, GalilScaffoldChainCredits.step credits (false,true))
  else (s,credits)

theorem outer_disabled (s : State) (credits : GalilScaffoldChainCredits.State)
    (seen : Option (Fin 3)) : outerMatched s credits false seen = (s,credits) := rfl

theorem outer_nonzero (s : State) (credits : GalilScaffoldChainCredits.State)
    (seen : Option (Fin 3)) (hz : zero credits.lag = false) :
    outerMatched s credits true seen = (s, GalilScaffoldChainCredits.step credits (false,true)) := by
  simp [outerMatched, hz]

theorem outer_zero (s : State) (credits : GalilScaffoldChainCredits.State)
    (seen : Option (Fin 3)) (hz : zero credits.lag = true) :
    outerMatched s credits true seen =
      (consume s seen, {credits with margin := inc credits.margin}) := by
  simp [outerMatched, hz]

/-- Zero lag does not increment on ready consume, even if verification
fails and the Chain becomes broken. Margin still increments. -/
theorem outer_zero_credits (s : State) (credits : GalilScaffoldChainCredits.State)
    (seen : Option (Fin 3)) (hz : zero credits.lag = true) :
    (outerMatched s credits true seen).2.lag = credits.lag ∧
    value (outerMatched s credits true seen).2.margin = value credits.margin+1 := by
  rw [outer_zero s credits seen hz]
  exact ⟨rfl, inc_value _⟩

theorem outer_zero_mismatch (s : State) (credits : GalilScaffoldChainCredits.State)
    (a : Fin 3) (seen : Option (Fin 3)) (ht : symbol s.period.focus = some a)
    (hne : seen ≠ some a) (hz : zero credits.lag = true) :
    (outerMatched s credits true seen).1 = {s with broken := true} := by
  rw [outer_zero s credits seen hz]
  exact mismatch s a seen ht hne

#print axioms outer_zero_mismatch
#print axioms outer_zero_credits
#print axioms ready_one
#print axioms ready_long
#print axioms mismatch
end PalPeg.GalilScaffoldChainConsume
