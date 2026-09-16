import PalPeg.GalilFifoDeadline

set_option autoImplicit false
namespace PalPeg.GalilSourceCost

/-- Scala's default quantum is 64. These constants come from
GalilClock.derive(64), not from an observed maximum input length. -/
def matchDelay : ℕ := 256
def moveSlope : ℕ := 2125
def intervalOverhead : ℕ := 1044
def predictability : ℕ := 3169
def service : ℕ := 6338

/-- The marked-FPP ledger at quantum 64, including a partial final batch.
The instruction ledger 296*m+190 remains an obligation of the actual FPP. -/
theorem marked_batches (m delta instructions rounds : ℕ)
    (hm : m ≤ 8 * delta) (hi : instructions ≤ 296 * m + 190)
    (hr : rounds ≤ (instructions + 63) / 64) : rounds ≤ 37 * delta + 3 := by
  omega

/-- A center move's copy/home/marker/rewind, marked FPP, and replay costs
give exactly the coefficient and residual used in the Scala clock. -/
theorem move_cost (delta radius m instructions rounds navigation replay : ℕ)
    (hradius : radius ≤ 4 * delta) (hm : m = 2 * radius)
    (hi : instructions ≤ 296 * m + 190)
    (hrounds : rounds ≤ (instructions + 63) / 64)
    (hnavigation : navigation ≤ 5 * m + 6)
    (hreplay : replay ≤ 8 * matchDelay * delta) :
    navigation + rounds + replay ≤ moveSlope * delta + 9 := by
  have hb := marked_batches m delta instructions rounds (by omega) hi hrounds
  simp only [matchDelay] at hreplay
  simp only [moveSlope]
  omega

/-- The chain-shift branch fits the same budget as an FPP fallback. -/
theorem shift_cost (delta ticks : ℕ) (ht : ticks ≤ delta + 1) :
    ticks ≤ moveSlope * delta + 9 := by
  simp only [moveSlope]
  omega

/-- Two newly exposed places permit at most two move/shift costs between
outputs. The zero-cost case represents an absent move. -/
theorem interval_cost (delta₁ delta₂ ticks₁ ticks₂ comparisons dispatch : ℕ)
    (h₁ : ticks₁ ≤ moveSlope * delta₁ + 9)
    (h₂ : ticks₂ ≤ moveSlope * delta₂ + 9)
    (hc : comparisons ≤ 4 * matchDelay) (hd : dispatch ≤ 2) :
    ticks₁ + ticks₂ + comparisons + dispatch ≤
      moveSlope * (delta₁ + delta₂) + intervalOverhead := by
  simp only [moveSlope, matchDelay, intervalOverhead] at *
  omega

/-- Once the concrete source supplies the center and interval contracts,
Scala's default service preserves its answers, including late negatives. -/
theorem default_answers (work center : ℕ → ℕ) (source : ℕ → Bool)
    (hcenter : ∀ n, n ≤ center n)
    (hmono : ∀ n, center n ≤ center (n + 1))
    (htime : ∀ n, work n ≤ moveSlope * (center (n + 1) - center n) + intervalOverhead)
    (hpositive : ∀ n, source n = true → center n = n) :
    ∀ n, GalilFifoDeadline.answer predictability work source n = source n := by
  exact GalilFifoDeadline.center_answer_eq moveSlope intervalOverhead work center source
    hcenter hmono htime hpositive

example : service = 2 * predictability := by decide

/-- info: 'PalPeg.GalilSourceCost.default_answers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms default_answers

/-- info: 'PalPeg.GalilSourceCost.move_cost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms move_cost

end PalPeg.GalilSourceCost
