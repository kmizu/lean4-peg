import PalPeg.GalilScaffoldChainVerifier

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainSweep
open GalilScaffoldChainPeriod GalilScaffoldChainConsume GalilScaffoldCounter

def run : State → List (Fin 3) → State
  | s, [] => s
  | s, a :: xs => run (consume s (some a)) xs

def front (ls : List Token) (xs : List (Fin 3)) (b : Fin 3) (rs : List Token) : Tape :=
  match xs with
  | [] => ⟨ls, .last b, rs⟩
  | a :: xs => ⟨ls, .plain a, xs.map Token.plain ++ .last b :: rs⟩

theorem run_append (s : State) (xs ys : List (Fin 3)) :
    run s (xs ++ ys) = run (run s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons a xs ih => exact ih (consume s (some a))

/-- Successful forward traversal of the interior changes only distance
and period; it stops on LAST without consuming it. -/
theorem forward_interior (xs : List (Fin 3)) (ls rs : List Token) (b : Fin 3)
    (s : State) (ht : s.period = front ls xs b rs) (hf : s.forward = true) :
    let t := run s xs
    t.period = ⟨(xs.map Token.plain).reverse ++ ls, .last b, rs⟩ ∧
    value t.distance = value s.distance + (xs.length : ℤ) ∧
    t.boundary = s.boundary ∧ t.last = s.last ∧ t.phase = s.phase ∧
    t.forward = true ∧ t.broken = s.broken := by
  induction xs generalizing ls s with
  | nil => simpa [run, front, hf] using ht
  | cons a xs ih =>
    have hplain : s.period.focus = .plain a := by rw [ht]; rfl
    have he := plain s a hplain
    have hp : (consume s (some a)).period = front (.plain a :: ls) xs b rs := by
      rw [he]
      simp [hf, ht, front, moveRight]
      cases xs <;> rfl
    have hd : (consume s (some a)).forward = true := by rw [he]; exact hf
    have hi := ih (.plain a :: ls) (consume s (some a)) hp hd
    rw [he] at hi
    simpa [run, he, List.reverse_cons, List.append_assoc, inc_value,
      Int.add_assoc, Int.add_comm, Int.add_left_comm] using hi

/-- The first successful semiperiod from ready records its exact length
as the boundary and turns left, including the h=1 case. -/
theorem first_boundary (center b : Fin 3) (xs : List (Fin 3)) :
    let t := run (ready center xs b) (xs ++ [b])
    value t.distance = xs.length+1 ∧ value t.boundary = xs.length+1 ∧
    t.last = reset ∧ t.phase = 1 ∧ t.forward = false ∧ t.broken = false ∧
    t.period = moveLeft ⟨(xs.map Token.plain).reverse ++ [.first center], .last b, []⟩ := by
  have hp : (ready center xs b).period = front [.first center] xs b [] := by
    cases xs <;> rfl
  have hi := forward_interior xs [.first center] [] b (ready center xs b) hp rfl
  dsimp only at hi
  have he := last (run (ready center xs b) xs) b (by rw [hi.1])
  dsimp only
  rw [run_append]
  simp only [run, he]
  rcases hi with ⟨ht,hd,hb,hl,hphase,hforward,hbroken⟩
  simp only [inc_value, ht, hd, hb, hphase, hbroken]
  simp [ready, reset, value, advancePhase]

/-- LAST's left move at the first boundary is legal because the initial
FIRST marker remains at the bottom of the left stack. -/
theorem first_turn_legal (center b : Fin 3) (xs : List (Fin 3)) :
    (run (ready center xs b) xs).period.left ≠ [] := by
  have hp : (ready center xs b).period = front [.first center] xs b [] := by
    cases xs <;> rfl
  have hi := (forward_interior xs [.first center] [] b (ready center xs b) hp rfl).1
  rw [hi]
  simp

def rear (ls : List Token) (xs : List (Fin 3)) (c : Fin 3) (rs : List Token) : Tape :=
  match xs with
  | [] => ⟨ls, .first c, rs⟩
  | a :: xs => ⟨xs.map Token.plain ++ .first c :: ls, .plain a, rs⟩

theorem backward_interior (xs : List (Fin 3)) (ls rs : List Token) (c : Fin 3)
    (s : State) (ht : s.period = rear ls xs c rs) (hf : s.forward = false) :
    let t := run s xs
    t.period = ⟨ls, .first c, (xs.map Token.plain).reverse ++ rs⟩ ∧
    value t.distance = value s.distance + (xs.length : ℤ) ∧
    t.boundary = s.boundary ∧ t.last = s.last ∧ t.phase = s.phase ∧
    t.forward = false ∧ t.broken = s.broken := by
  induction xs generalizing rs s with
  | nil => simpa [run, rear, hf] using ht
  | cons a xs ih =>
    have hplain : s.period.focus = .plain a := by rw [ht]; rfl
    have he := plain s a hplain
    have hp : (consume s (some a)).period = rear ls xs c (.plain a :: rs) := by
      rw [he]
      simp [hf, ht, rear, moveLeft]
      cases xs <;> rfl
    have hd : (consume s (some a)).forward = false := by rw [he]; exact hf
    have hi := ih (.plain a :: rs) (consume s (some a)) hp hd
    rw [he] at hi
    simpa [run, he, List.reverse_cons, List.append_assoc, inc_value,
      Int.add_assoc, Int.add_comm, Int.add_left_comm] using hi

theorem rear_after_last (xs : List (Fin 3)) (c b : Fin 3) :
    moveLeft ⟨(xs.map Token.plain).reverse ++ [.first c], .last b, []⟩ =
      rear [] xs.reverse c [.last b] := by
  rw [← List.map_reverse]
  cases xs.reverse <;> rfl

/-- A successful full bounce restores the ready period position, but not
the counters: boundary=distance=2h, last=h, phase=2. -/
theorem first_round_trip (center b : Fin 3) (xs : List (Fin 3)) :
    let t := run (ready center xs b) ((xs ++ [b]) ++ (xs.reverse ++ [center]))
    t.period = (ready center xs b).period ∧
    value t.distance = 2*(xs.length+1) ∧ value t.boundary = 2*(xs.length+1) ∧
    value t.last = xs.length+1 ∧ t.phase = 2 ∧ t.forward = true ∧ t.broken = false := by
  let mid := run (ready center xs b) (xs ++ [b])
  have hf := first_boundary center b xs
  change value mid.distance = _ ∧ _ at hf
  rcases hf with ⟨hd,hb,hl,hphase,hforward,hbroken,ht⟩
  change value mid.boundary = _ at hb
  change mid.phase = 1 at hphase
  change mid.broken = false at hbroken
  have hp : mid.period = rear [] xs.reverse center [.last b] := by
    rw [ht, rear_after_last]
  have hi := backward_interior xs.reverse [] [.last b] center mid hp hforward
  dsimp only at hi
  rcases hi with ⟨ht2,hd2,hb2,hl2,hphase2,hforward2,hbroken2⟩
  have he := first (run mid xs.reverse) center (by rw [ht2])
  dsimp only
  rw [run_append]
  change let t := run mid (xs.reverse ++ [center]); _
  rw [run_append]
  simp only [run, he, inc_value, ht2, hd2, hb2, hphase2, hbroken2,
    hd, hb, hphase, hbroken, List.length_reverse]
  simp [ready, advancePhase, List.map_reverse]
  omega

theorem forward_boundary (center b : Fin 3) (xs : List (Fin 3)) (s : State)
    (hp : s.period = (ready center xs b).period) (hf : s.forward = true) :
    let t := run s (xs ++ [b])
    value t.distance = value s.distance + (xs.length+1) ∧
    t.boundary = t.distance ∧ t.last = s.boundary ∧
    t.phase = advancePhase s.phase ∧ t.forward = false ∧ t.broken = s.broken ∧
    t.period = moveLeft ⟨(xs.map Token.plain).reverse ++ [.first center], .last b, []⟩ := by
  have ht : s.period = front [.first center] xs b [] := by
    rw [hp]; cases xs <;> rfl
  have hi := forward_interior xs [.first center] [] b s ht hf
  dsimp only at hi
  have he := last (run s xs) b (by rw [hi.1])
  dsimp only
  rw [run_append]
  rcases hi with ⟨ht,hd,hb,hl,hphase,hforward,hbroken⟩
  simp only [run, he, inc_value, ht, hd, hb, hphase, hbroken]
  simp [Int.add_assoc]

def bounce (center b : Fin 3) (xs : List (Fin 3)) : List (Fin 3) :=
  (xs ++ [b]) ++ (xs.reverse ++ [center])

theorem round_trip (center b : Fin 3) (xs : List (Fin 3)) (s : State)
    (hp : s.period = (ready center xs b).period) (hf : s.forward = true) :
    let t := run s (bounce center b xs)
    t.period = s.period ∧
    value t.distance = value s.distance + 2*(xs.length+1) ∧
    t.boundary = t.distance ∧ value t.last = value s.distance + (xs.length+1) ∧
    t.phase = advancePhase (advancePhase s.phase) ∧
    t.forward = true ∧ t.broken = s.broken := by
  let mid := run s (xs ++ [b])
  have hm := forward_boundary center b xs s hp hf
  change value mid.distance = _ ∧ mid.boundary = mid.distance ∧ mid.last = s.boundary ∧
    mid.phase = advancePhase s.phase ∧ mid.forward = false ∧ mid.broken = s.broken ∧ _ at hm
  rcases hm with ⟨hd,hb,hl,hphase,hforward,hbroken,ht⟩
  have hperiod : mid.period = rear [] xs.reverse center [.last b] := by
    rw [ht, rear_after_last]
  have hi := backward_interior xs.reverse [] [.last b] center mid hperiod hforward
  dsimp only at hi
  rcases hi with ⟨ht2,hd2,hb2,hl2,hphase2,hforward2,hbroken2⟩
  have he := first (run mid xs.reverse) center (by rw [ht2])
  dsimp only [bounce]
  rw [run_append]
  change let t := run mid (xs.reverse ++ [center]); _
  rw [run_append]
  simp only [run, he, inc_value, ht2, hd2, hb2, hphase2, hbroken2,
    hb, hd, hphase, hbroken, List.length_reverse]
  rw [hp]
  simp [ready, List.map_reverse]
  omega

theorem four_boundaries (center b : Fin 3) (xs : List (Fin 3)) :
    let word := bounce center b xs
    let t := run (ready center xs b) (word ++ word)
    t.period = (ready center xs b).period ∧
    value t.distance = 4*(xs.length+1) ∧ value t.boundary = 4*(xs.length+1) ∧
    value t.last = 3*(xs.length+1) ∧ t.phase = 4 ∧ t.forward = true ∧ t.broken = false := by
  let s := ready center xs b
  let word := bounce center b xs
  have h1 := round_trip center b xs s rfl rfl
  dsimp only at h1
  rcases h1 with ⟨hp,hd,hb,hl,hphase,hforward,hbroken⟩
  have h2 := round_trip center b xs (run s word) hp hforward
  dsimp only at h2
  rcases h2 with ⟨hp2,hd2,hb2,hl2,hphase2,hforward2,hbroken2⟩
  change (run s (word ++ word)).period = s.period ∧
    value (run s (word ++ word)).distance = 4*(xs.length+1) ∧
    value (run s (word ++ word)).boundary = 4*(xs.length+1) ∧
    value (run s (word ++ word)).last = 3*(xs.length+1) ∧
    (run s (word ++ word)).phase = 4 ∧ (run s (word ++ word)).forward = true ∧
    (run s (word ++ word)).broken = false
  rw [run_append]
  dsimp only [word, s] at *
  simp only [hp2, hp, hd2, hl2, hb2, hphase2, hforward2, hbroken2,
    hd, hphase, hbroken]
  simp [ready, reset, value, advancePhase]
  omega

#print axioms four_boundaries
#print axioms round_trip
#print axioms first_round_trip
#print axioms backward_interior
#print axioms first_turn_legal
#print axioms first_boundary
#print axioms forward_interior
end PalPeg.GalilScaffoldChainSweep
