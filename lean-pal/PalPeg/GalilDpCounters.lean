import PalPeg.GalilDpStart

set_option autoImplicit false
namespace PalPeg.GalilDpCounters
open GalilFppWide GalilDpAdvance

/-- OUTPUT has no right sentinel: Scala decodes its consecutive ones. -/
def output (h i : ℕ) : Fin 9 := if i = 0 then 4 else if i ≤ h then 8 else 6

theorem output_succ (h : ℕ) : Function.update (output h) (h+1) 8 = output (h+1) := by
  funext i
  by_cases he : i = h+1
  · subst i; simp [output]
  · by_cases hz : i = 0
    · subst i; simp [output]
    · have hi : i ≤ h+1 ↔ i ≤ h := by omega
      simp [Function.update_of_ne he, output, hz, hi]

/-- Cursor is h at candidate entry and h+1 after its lower-bound test.
Keeping it separate also describes the h=0 bootstrap. -/
structure Tracked (lower cursor h : ℕ) (x : Config 12) : Prop where
  lowerPos : x.pos 10 = min cursor (lower+1)
  outputPos : x.pos 11 = h
  outputTape : x.tape 11 = output h

theorem Tracked.set_pc {lower cursor h : ℕ} {x : Config 12}
    (hx : Tracked lower cursor h x) (pc : ℕ) : Tracked lower cursor h { x with pc := pc } :=
  ⟨hx.lowerPos, hx.outputPos, hx.outputTape⟩

theorem tracked_next {lower cursor h : ℕ} {x : Config 12}
    (hx : Tracked lower cursor h x) :
    Tracked lower cursor (h+1) { next x with pc := 348 } := by
  constructor
  · simpa [next_pos] using hx.lowerPos
  · simp [next_pos, hx.outputPos]
  · simpa [next_tape, hx.outputPos, hx.outputTape] using output_succ h

theorem tracked_start (lower : ℕ) (x : Config 12)
    (hl : x.pos 10 = 0) (ho : x.pos 11 = 0) (ht : x.tape 11 = fun _ => 6) :
    Tracked lower 1 0 (GalilDpStart.start x) := by
  constructor
  · simp [GalilDpStart.start, hl]
  · simpa [GalilDpStart.start] using ho
  · simp only [GalilDpStart.start, Function.update_self, ho, ht]
    funext i
    by_cases hi : i = 0 <;> simp [output, hi]

theorem tracked_skip_lower {lower h : ℕ} {x : Config 12}
    (hx : Tracked lower h h x) (hh : h ≤ lower) :
    Tracked lower (h+1) h
      { x with pc := 363, pos := Function.update x.pos 10 (x.pos 10+1) } := by
  constructor
  · simp [hx.lowerPos, Nat.min_eq_left (by omega : h ≤ lower+1),
      Nat.min_eq_left (by omega : h+1 ≤ lower+1)]
  · simpa using hx.outputPos
  · exact hx.outputTape

theorem tracked_skip_mark {lower h : ℕ} {x : Config 12}
    (hx : Tracked lower h h x) (hh : lower < h) :
    Tracked lower (h+1) h { x with pc := 363 } := by
  constructor
  · simpa [Nat.min_eq_right (by omega : lower+1 ≤ h),
      Nat.min_eq_right (by omega : lower+1 ≤ h+1)] using hx.lowerPos
  · exact hx.outputPos
  · exact hx.outputTape

theorem output_ones (h i : ℕ) : output h i = 8 ↔ 0 < i ∧ i ≤ h := by
  by_cases hi : i = 0
  · subst i; simp [output]
  · have hp : 0 < i := by omega
    by_cases hn : i ≤ h <;> simp [output, hi, hp, hn]

#print axioms tracked_next
#print axioms tracked_start
end PalPeg.GalilDpCounters
