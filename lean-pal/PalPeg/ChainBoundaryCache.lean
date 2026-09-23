import PalPeg.GalilScaffoldChainInputSupply

/-!
# Rebuilding the next boundary snapshot during a period traversal

The retired last-boundary counter can be reused as the next snapshot. Its
increment rate is 1 before the first boundary, 2 before the second, and 3
thereafter. The rate depends only on the existing finite phase. Uniform shifts
also decrement the spare. This file proves the schedule against the actual
period tape and consume operation; physical role/tape allocation remains open.
-/
set_option autoImplicit false

namespace PalPeg.ChainBoundaryCache
open PalPeg.GalilScaffoldChainPeriod
open PalPeg.GalilScaffoldChainConsume
open PalPeg.GalilScaffoldCounter

/-- A split of the existing FIRST, plain symbols, LAST tape in its traversal direction.
`age` is a proof index, not a field in finite control. -/
def Cursor (h age : ℕ) (t : Tape) (forward : Bool) : Prop :=
  ∃ (passed future : List (Fin 3)) (first last : Fin 3),
    passed.length = age ∧ passed.length + future.length + 1 = h ∧
    if forward then
      t.left = (passed.map Token.plain).reverse ++ [.first first] ∧
      t.focus :: t.right = future.map Token.plain ++ [.last last]
    else
      t.right = passed.map Token.plain ++ [.last last] ∧
      t.focus :: t.left = future.map Token.plain ++ [.first first]

def boundaryEvent (s : State) : Bool := isFirst s.period.focus || isLast s.period.focus

def nextAge (s : State) (age : ℕ) : ℕ := if boundaryEvent s then 0 else age + 1

theorem cursor_ready (first last : Fin 3) (xs : List (Fin 3)) :
    Cursor (xs.length + 1) 0 (ready first xs last).period true := by
  refine ⟨[], xs, first, last, rfl, by simp, ?_⟩
  cases xs <;> simp [ready, moveRight]

/-- The end marker is reached after exactly one semiperiod, in either direction. -/
theorem cursor_boundary {h age : ℕ} {s : State} (hc : Cursor h age s.period s.forward) :
    boundaryEvent s = true ↔ age + 1 = h := by
  obtain ⟨passed, future, first, last, hp, hlen, ht⟩ := hc
  cases hf : s.forward <;> simp only [hf, Bool.false_eq_true, if_false, if_true] at ht
  all_goals
    cases future with
    | nil =>
      have hfocus := (List.cons.inj (by simpa using ht.2)).1
      simp [boundaryEvent, hfocus, isFirst, isLast]
      simp only [List.length_nil] at hlen
      omega
    | cons a rest =>
      have hfocus := (List.cons.inj (by simpa using ht.2)).1
      simp [boundaryEvent, hfocus, isFirst, isLast]
      simp only [List.length_cons] at hlen
      omega

/-- The proof index is exactly the semiperiod length read by shift entry. -/
theorem cursor_length {h age : ℕ} {t : Tape} {forward : Bool} (hc : Cursor h age t forward) :
    t.left.length + t.right.length = h := by
  obtain ⟨passed, future, first, last, _, hlen, ht⟩ := hc
  cases hf : forward <;> simp only [hf, Bool.false_eq_true, if_false, if_true] at ht
  all_goals
    have hside := congrArg List.length ht.1
    have hfocus := congrArg List.length ht.2
    simp only [List.length_append, List.length_reverse, List.length_map,
      List.length_cons, List.length_nil] at hside hfocus
    omega

/-- The cursor invariant uses the real `consume`, including both direction flips. -/
theorem cursor_consume {h age : ℕ} {s : State} (hc : Cursor h age s.period s.forward)
    (a : Fin 3) (ha : symbol s.period.focus = some a) :
    Cursor h (nextAge s age) (consume s (some a)).period (consume s (some a)).forward := by
  obtain ⟨passed, future, first, last, hp, hlen, ht⟩ := hc
  cases hf : s.forward <;> simp only [hf, Bool.false_eq_true, if_false, if_true] at ht
  · cases future with
    | nil =>
      have htape : s.period = ⟨[], .first first, passed.map Token.plain ++ [.last last]⟩ := by
        have hh := List.cons.inj (by simpa using ht.2)
        change (⟨s.period.left, s.period.focus, s.period.right⟩ : Tape) = _
        rw [ht.1, hh.1, hh.2]
      have he : a = first := by simpa [htape, symbol] using ha.symm
      subst a
      rw [PalPeg.GalilScaffoldChainConsume.first s first (by rw [htape])]
      refine ⟨[], passed, first, last, ?_, ?_, ?_⟩
      · simp [nextAge, boundaryEvent, htape, isFirst]
      · simpa using hlen
      · cases passed <;> simp [htape, moveRight]
    | cons b rest =>
      have htape : s.period = ⟨rest.map Token.plain ++ [.first first], .plain b,
          passed.map Token.plain ++ [.last last]⟩ := by
        have hh := List.cons.inj (by simpa using ht.2)
        change (⟨s.period.left, s.period.focus, s.period.right⟩ : Tape) = _
        rw [ht.1, hh.1, hh.2]
      have he : a = b := by simpa [htape, symbol] using ha.symm
      subst a
      rw [plain s b (by rw [htape])]
      simp only [hf, Bool.false_eq_true, if_false]
      refine ⟨b :: passed, rest, first, last, ?_, ?_, ?_⟩
      · simp [nextAge, boundaryEvent, htape, isFirst, isLast, hp]
      · simp only [List.length_cons] at hlen ⊢; omega
      · cases rest <;> simp [htape, moveLeft]
  · cases future with
    | nil =>
      have htape : s.period = ⟨(passed.map Token.plain).reverse ++ [.first first], .last last, []⟩ := by
        have hh := List.cons.inj (by simpa using ht.2)
        change (⟨s.period.left, s.period.focus, s.period.right⟩ : Tape) = _
        rw [ht.1, hh.1, hh.2]
      have he : a = last := by simpa [htape, symbol] using ha.symm
      subst a
      rw [PalPeg.GalilScaffoldChainConsume.last s last (by rw [htape])]
      refine ⟨[], passed.reverse, first, last, ?_, ?_, ?_⟩
      · simp [nextAge, boundaryEvent, htape, isFirst, isLast]
      · simpa using hlen
      · have he : (passed.map Token.plain).reverse = passed.reverse.map Token.plain := by simp
        rw [htape, he]
        cases passed.reverse <;> simp [moveLeft]
    | cons b rest =>
      have htape : s.period = ⟨(passed.map Token.plain).reverse ++ [.first first], .plain b,
          rest.map Token.plain ++ [.last last]⟩ := by
        have hh := List.cons.inj (by simpa using ht.2)
        change (⟨s.period.left, s.period.focus, s.period.right⟩ : Tape) = _
        rw [ht.1, hh.1, hh.2]
      have he : a = b := by simpa [htape, symbol] using ha.symm
      subst a
      rw [plain s b (by rw [htape])]
      simp only [hf, if_true]
      refine ⟨passed ++ [b], rest, first, last, ?_, ?_, ?_⟩
      · simp [nextAge, boundaryEvent, htape, isFirst, isLast, hp]
      · simp only [List.length_cons, List.length_append, List.length_nil] at hlen ⊢; omega
      · cases rest <;> simp [htape, moveRight, List.reverse_append]

/-- Finite amount of work per successful consume. -/
def rate (phase : Fin 5) : ℕ := min phase.val 2 + 1

theorem rate_le (phase : Fin 5) : rate phase ≤ 3 := by unfold rate; omega

def advanceCounter : ℕ → Counter → Counter
  | 0, c => c
  | n+1, c => advanceCounter n (inc c)

theorem advanceCounter_value (n : ℕ) (c : Counter) :
    value (advanceCounter n c) = value c + n := by
  induction n generalizing c with
  | zero => simp [advanceCounter]
  | succ n ih => simp [advanceCounter, ih, inc_value]; omega

theorem advanceCounter_succ (n : ℕ) (c : Counter) :
    advanceCounter (n+1) c = inc (advanceCounter n c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => exact ih (inc c)

theorem advanceCounter_canonical (n : ℕ) (c : Counter) (hc : Canonical c) :
    Canonical (advanceCounter n c) := by
  induction n generalizing c with
  | zero => exact hc
  | succ n ih => exact ih (inc c) (inc_canonical c hc)

/-- Canonical counters are determined by their signed values, even after shifts. -/
theorem counter_eq_of_value {a b : Counter} (ha : Canonical a) (hb : Canonical b)
    (he : value a = value b) : a = b := by
  have hp : a.pos.length = b.pos.length := by
    rcases ha with ha | ha <;> rcases hb with hb | hb <;>
      simp only [value, ha, hb, List.length_nil] at he ⊢ <;> omega
  have hn : a.neg.length = b.neg.length := by
    simp only [value] at he
    omega
  have hep : a.pos = b.pos := List.length_injective hp
  have hen : a.neg = b.neg := List.length_injective hn
  cases a; cases b; simp_all

/-- At a boundary the prepared counter becomes the new boundary; the retired
last counter becomes the spare. No variable-sized copy appears in this update. -/
def nextSpare (s : State) (spare : Counter) : Counter :=
  if boundaryEvent s then s.last else advanceCounter (rate s.phase) spare

/-- Affine schedule relative to the current boundary. Values may be negative:
center shifts are accounted for uniformly. -/
structure Inv (h age : ℕ) (s : State) (spare : Counter) : Prop where
  cursor : Cursor h age s.period s.forward
  distance : value s.distance = value s.boundary + age
  last : value s.last = value s.boundary - (if s.phase = 0 then 0 else (h : ℤ))
  spare : value spare = value s.boundary - (min s.phase.val 2 : ℕ) * (h : ℤ)
    + (rate s.phase : ℤ) * age

theorem inv_ready (first last : Fin 3) (xs : List (Fin 3)) :
    Inv (xs.length + 1) 0 (ready first xs last) reset := by
  exact ⟨cursor_ready first last xs, by simp [ready], by simp [ready],
    by simp [ready, rate]⟩

/-- Before a boundary rotation, bounded rebuilding has caught the distance. -/
theorem spare_at_boundary {h age : ℕ} {s : State} {spare : Counter}
    (hi : Inv h age s spare) (he : boundaryEvent s = true) :
    value (advanceCounter (rate s.phase) spare) = value (inc s.distance) := by
  have hend := (cursor_boundary hi.cursor).mp he
  rw [advanceCounter_value, hi.spare, inc_value, hi.distance]
  have hage : (age : ℤ) + 1 = h := by exact_mod_cast hend
  dsimp only [rate]
  push_cast
  rw [← hage]
  ring

/-- Literal logical equality, suitable for the existing `absCtr` representation. -/
theorem spare_eq_at_boundary {h age : ℕ} {s : State} {spare : Counter}
    (hi : Inv h age s spare) (he : boundaryEvent s = true)
    (hc : Canonical spare) (hd : Canonical s.distance) :
    advanceCounter (rate s.phase) spare = inc s.distance :=
  counter_eq_of_value (advanceCounter_canonical _ _ hc) (inc_canonical _ hd)
    (spare_at_boundary hi he)

/-- Successful consume preserves both the actual tape traversal and the cache
schedule, so the next boundary will again have its copy ready. -/
theorem inv_consume {h age : ℕ} {s : State} {spare : Counter}
    (hi : Inv h age s spare) (a : Fin 3) (ha : symbol s.period.focus = some a) :
    Inv h (nextAge s age) (consume s (some a)) (nextSpare s spare) := by
  have hcursor := cursor_consume hi.cursor a ha
  refine ⟨hcursor, ?_, ?_, ?_⟩
  all_goals
    simp only [consume, ha, decide_true, if_true]
    by_cases he : boundaryEvent s = true
    · have hend := (cursor_boundary hi.cursor).mp he
      have he' : (isFirst s.period.focus || isLast s.period.focus) = true := he
      simp only [he', if_true, nextAge, he, nextSpare, inc_value]
      have hd := hi.distance
      have hl := hi.last
      have hs := hi.spare
      have hage : (age : ℤ) + 1 = h := by exact_mod_cast hend
      generalize hp : s.phase = phase at *
      fin_cases phase <;> simp [advancePhase, rate] at * <;> omega
    · have he' : (isFirst s.period.focus || isLast s.period.focus) ≠ true := he
      simp only [he', nextAge, he, nextSpare, inc_value]
      have hd := hi.distance
      have hl := hi.last
      have hs := hi.spare
      generalize hp : s.phase = phase at *
      fin_cases phase <;> simp [rate, he, advanceCounter_value] at * <;> omega

/-- The actual center-shift update, including the spare's decrement. -/
theorem inv_shift {h age : ℕ} {wm : PalPeg.GalilScaffoldChainWatch.State} {spare : Counter}
    (hi : Inv h age wm.machine.control spare) :
    Inv h age (PalPeg.GalilScaffoldChainInputSupply.chainShiftOne wm).machine.control
      (dec spare) := by
  refine ⟨hi.cursor, ?_, ?_, ?_⟩
  all_goals
    simp only [PalPeg.GalilScaffoldChainInputSupply.chainShiftOne, dec_value]
    first | rw [hi.distance]; omega | rw [hi.last]; omega | rw [hi.spare]; ring

/-- info: 'PalPeg.ChainBoundaryCache.cursor_consume' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cursor_consume

/-- info: 'PalPeg.ChainBoundaryCache.spare_eq_at_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms spare_eq_at_boundary

/-- info: 'PalPeg.ChainBoundaryCache.inv_consume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inv_consume

/-- info: 'PalPeg.ChainBoundaryCache.inv_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inv_shift

end PalPeg.ChainBoundaryCache
