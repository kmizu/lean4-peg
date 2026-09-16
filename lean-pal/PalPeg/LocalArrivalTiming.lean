import PalPeg.LocalArrival
import PalPeg.LocalTracking

/-!
# Arrival timing: the right view never needs a not-yet-arrived letter

`PalPeg.LocalArrival.moveRight_ok` needs the side condition `Ahead v q`.  This
file does the clock bookkeeping that discharges it, and the upper (and, under a
named keep-up hypothesis, the lower) half of the timing oracle `O5`.

## Conventions

* A view's stored content is `cells v = back.reverse ++ focus :: absRight v`.
  After `j` letters have been delivered, `(cells v).length = j + 1`
  (`ContentLen v j`): one initial cell plus the `j` arrived letters, so the
  `k`-th letter sits at `pos = k`.
* The **place** of a view is `2 * pos v + (if gap then 1 else 0)`.  A right
  move increases the place by exactly one (`(p,false) → (p,true) → (p+1,false)`).
  The last letter of a `j`-letter word, on its letter half, is place `2 * j`.

## Results

* `ahead_of_place` (**`ahead_invariant`**): `ContentLen v j` and `place v ≤ 2 * j`
  give `Ahead v q` for every `q`.  (`gap = true` forces `2 * pos + 1 ≤ 2 * j`,
  i.e. `pos < j`, so some content lies right of the focus.)
* `contentLen_arrive` / `contentLen_moveRight` / `contentLen_moveLeftV`: the
  content invariant moves with arrivals only.
* `place_bound`: if place increments are `≤ 1` per local tick (`hstep`), start
  at `0`, and two increments are `≥ d` local ticks apart (`hclock`), then
  `d * p t ≤ t + d - 1`.
* `hclock_of_abstract`: `hclock` in local ticks follows from the abstract clock
  (`≥ d` abstract ticks between increments) and `hcost` (each local tick
  advances the abstract tick counter by at most one).
* `ahead_along_run`: along the concrete `stepW` run, every state on which a
  local tick is taken satisfies `Ahead` for the right view.
* `report_place_le`: after `|w|` `stepW`s, `place ≤ 2 * |w|`.
* `report_place_eq`: with `hfast` (`p t + 1 ≤ p (t + delayS)` while in the
  run), `place = 2 * |w|` exactly.
-/

set_option autoImplicit false

namespace PalPeg.LocalArrivalTiming

open PalPeg.LocalInputView (InputView WF arrive moveRight moveLeftV stepRight stepLeft cells pos
  absRight farList)
open PalPeg.LocalArrival (Ahead)
open PalPeg.LocalState (GalilVML)
open PalPeg.LocalTracking (stepW runW feed feedL delayS nLocal)

/-! ## 1. Place and content -/

/-- The place of a view: two places per cell (gap half, then letter half). -/
def place (v : InputView) : ℕ := 2 * pos v + (if v.gap then 1 else 0)

/-- After `j` delivered letters the view stores `j + 1` cells. -/
def ContentLen (v : InputView) (j : ℕ) : Prop := (cells v).length = j + 1

/-- **`ahead_invariant`.**  A view whose place is at most `2 * j`, with `j`
letters delivered, never needs a not-yet-arrived letter. -/
theorem ahead_of_place {v : InputView} {j : ℕ} (hc : ContentLen v j)
    (hp : place v ≤ 2 * j) (q : List (Fin 2)) : Ahead v q := by
  intro hg hn
  left
  have hlen := PalPeg.LocalInputView.length_cells v
  unfold ContentLen at hc
  have hpl : 2 * pos v + 1 ≤ 2 * j := by simpa [place, hg] using hp
  have hpos : 0 < (absRight v).length := by omega
  have hab : absRight v = farList v := by simp [absRight, hn]
  rw [hab] at hpos
  intro hnil
  simp [farList, hnil] at hpos

theorem ahead_invariant {v : InputView} {j : ℕ} (hc : ContentLen v j)
    (hp : place v ≤ 2 * j) (q : List (Fin 2)) : Ahead v q := ahead_of_place hc hp q

theorem contentLen_arrive {v : InputView} (hw : WF v) {j : ℕ} (hc : ContentLen v j)
    (a : Fin 2) : ContentLen (arrive a v) (j + 1) := by
  unfold ContentLen at hc ⊢
  rw [PalPeg.LocalInputView.cells_arrive hw a, List.length_append, hc]
  rfl

theorem contentLen_moveRight {v : InputView} (hw : WF v) {j : ℕ} (hc : ContentLen v j) :
    ContentLen (moveRight v) j := by
  unfold ContentLen at hc ⊢
  unfold moveRight
  cases hg : v.gap
  · simpa [cells, absRight, farList] using hc
  · have h := PalPeg.LocalInputView.cells_stepRight hw
    simp only [if_true]
    have : cells { stepRight v with gap := false } = cells (stepRight v) := rfl
    rw [this, h, hc]

theorem contentLen_moveLeftV {v : InputView} {j : ℕ} (hc : ContentLen v j) :
    ContentLen (moveLeftV v) j := by
  unfold ContentLen at hc ⊢
  unfold moveLeftV
  cases hg : v.gap
  · have h := PalPeg.LocalInputView.cells_stepLeft v
    simp only [Bool.false_eq_true, if_false]
    have : cells { stepLeft v with gap := true } = cells (stepLeft v) := rfl
    rw [this, h, hc]
  · simpa [cells, absRight, farList] using hc

/-! ## 2. The clock bound, in local ticks -/

section Clock

variable (p : ℕ → ℕ)

/-- An increment of the place at local tick `t`. -/
def Inc (t : ℕ) : Prop := p t < p (t + 1)

/-- Either no increment happened before `t` (so `p` never rose above `p 0`), or
there is a last one, `s`, and `p t ≤ p (s + 1)`. -/
theorem last_inc (_hstep : ∀ t, p (t + 1) ≤ p t + 1) :
    ∀ t, p t ≤ p 0 ∨ ∃ s, s < t ∧ Inc p s ∧ p t ≤ p (s + 1) ∧
      ∀ u, s < u → u < t → ¬ Inc p u := by
  intro t
  induction t with
  | zero => exact Or.inl le_rfl
  | succ t ih =>
      by_cases hi : Inc p t
      · exact Or.inr ⟨t, by omega, hi, le_rfl, fun u h1 h2 => by omega⟩
      · have hle : p (t + 1) ≤ p t := by unfold Inc at hi; omega
        rcases ih with h | ⟨s, hs, hsi, hps, hno⟩
        · exact Or.inl (le_trans hle h)
        · refine Or.inr ⟨s, by omega, hsi, le_trans hle hps, fun u h1 h2 => ?_⟩
          rcases Nat.lt_or_ge u t with hu | hu
          · exact hno u h1 hu
          · have : u = t := by omega
            subst this; exact hi

/-- At an increment, `d * p s ≤ s`. -/
theorem inc_bound (d : ℕ) (hstep : ∀ t, p (t + 1) ≤ p t + 1) (hp0 : p 0 = 0)
    (hclock : ∀ s u, s < u → Inc p s → Inc p u → s + d ≤ u) :
    ∀ s, Inc p s → d * p s ≤ s := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
      intro hs
      rcases last_inc p hstep s with h | ⟨s', hs', hi', hps, -⟩
      · rw [hp0] at h
        have : p s = 0 := by omega
        rw [this]; simp
      · have h1 := ih s' hs' hi'
        have h2 := hclock s' s hs' hi' hs
        have h3 : p s ≤ p s' + 1 := le_trans hps (hstep s')
        calc d * p s ≤ d * (p s' + 1) := Nat.mul_le_mul_left d h3
          _ = d * p s' + d := by ring
          _ ≤ s := by omega

/-- **The clock bound.**  `d * p t ≤ t + d - 1`, i.e. `p t ≤ ⌈t / d⌉`. -/
theorem place_bound (d : ℕ) (hd : 0 < d) (hstep : ∀ t, p (t + 1) ≤ p t + 1) (hp0 : p 0 = 0)
    (hclock : ∀ s u, s < u → Inc p s → Inc p u → s + d ≤ u) :
    ∀ t, d * p t + 1 ≤ t + d := by
  intro t
  rcases last_inc p hstep t with h | ⟨s, hs, hi, hps, -⟩
  · rw [hp0] at h
    have : p t = 0 := by omega
    rw [this]; simp; omega
  · have h1 := inc_bound p d hstep hp0 hclock s hi
    have h3 : p t ≤ p s + 1 := le_trans hps (hstep s)
    calc d * p t + 1 ≤ d * (p s + 1) + 1 := by
          have := Nat.mul_le_mul_left d h3; omega
      _ = d * p s + d + 1 := by ring
      _ ≤ t + d := by omega

end Clock

/-- Local clock from the abstract clock.  `a t` = number of abstract ticks
completed after `t` local ticks.  `hcost`: one local tick completes at most one
abstract tick (every abstract tick costs `≥ 1` local step).  `hclockAbs`: two
place increments are `≥ d` abstract ticks apart. -/
theorem hclock_of_abstract (p a : ℕ → ℕ) (d : ℕ)
    (hcost : ∀ t, a (t + 1) ≤ a t + 1)
    (hclockAbs : ∀ s u, s < u → Inc p s → Inc p u → a s + d ≤ a u) :
    ∀ s u, s < u → Inc p s → Inc p u → s + d ≤ u := by
  have hmono : ∀ s k, a (s + k) ≤ a s + k := by
    intro s k
    induction k with
    | zero => simp
    | succ k ih => have := hcost (s + k); rw [← Nat.add_assoc]; omega
  intro s u hsu hs hu
  have h1 := hclockAbs s u hsu hs hu
  have h2 := hmono s (u - s)
  rw [Nat.add_sub_cancel' (le_of_lt hsu)] at h2
  omega

/-! ## 3. The concrete run -/

section Run

variable {Np : ℕ} (tickL : GalilVML Np → GalilVML Np) (x0 : GalilVML Np) (w : List (Fin 2))

/-- The state inside the `(k+1)`-st `stepW`, after `r` local ticks
(`k + 1` letters delivered). -/
def trajW (k r : ℕ) (a : Fin 2) : GalilVML Np :=
  tickL^[r] (feed (some a) (runW tickL nLocal x0 (w.take k)))

/-- The right view's place at global local time `t` (`t = k * nLocal + r`).
Past the run it is the place of the final state. -/
noncomputable def placeAt (t : ℕ) : ℕ :=
  if h : t / nLocal < w.length then
    place (trajW tickL x0 w (t / nLocal) (t % nLocal) (w.get ⟨t / nLocal, h⟩)).right
  else place (runW tickL nLocal x0 w).right

theorem runW_take_succ (k : ℕ) (hk : k < w.length) :
    runW tickL nLocal x0 (w.take (k + 1))
      = stepW tickL nLocal (runW tickL nLocal x0 (w.take k)) (w.get ⟨k, hk⟩) := by
  unfold runW
  rw [List.take_add_one, List.foldl_append]
  simp [List.getElem?_eq_getElem hk]

theorem placeAt_kr (k r : ℕ) (hk : k < w.length) (hr : r < nLocal) :
    placeAt tickL x0 w (k * nLocal + r)
      = place (trajW tickL x0 w k r (w.get ⟨k, hk⟩)).right := by
  have hq : (k * nLocal + r) / nLocal = k := by
    unfold nLocal delayS at hr ⊢; omega
  have hm : (k * nLocal + r) % nLocal = r := by
    unfold nLocal delayS at hr ⊢; omega
  unfold placeAt
  have hk' : (k * nLocal + r) / nLocal < w.length := by rw [hq]; exact hk
  rw [dif_pos hk']
  simp only [hm]
  congr 3; simp [hq]

/-- Delivery on the right view: `feed` only touches `far`. -/
theorem feed_right_place (a : Fin 2) (x : GalilVML Np) :
    place (feed (some a) x).right = place x.right := rfl

/-- **`Ahead` along the whole run.**  Hypotheses:

* `hcontent`: the right view of every intermediate state stores exactly the
  delivered letters (`ContentLen … (k+1)`) — preserved by `feedL`
  (`contentLen_arrive`) and by right/left moves (`contentLen_moveRight`,
  `contentLen_moveLeftV`); a `tickL` that only moves the view keeps it;
* `hstep`, `hp0`, `hclock`: the clock facts on `placeAt`. -/
theorem ahead_along_run
    (hcontent : ∀ k r (hk : k < w.length), r < nLocal →
      ContentLen (trajW tickL x0 w k r (w.get ⟨k, hk⟩)).right (k + 1))
    (hstep : ∀ t, placeAt tickL x0 w (t + 1) ≤ placeAt tickL x0 w t + 1)
    (hp0 : placeAt tickL x0 w 0 = 0)
    (hclock : ∀ s u, s < u → Inc (placeAt tickL x0 w) s → Inc (placeAt tickL x0 w) u →
      s + delayS ≤ u)
    (k r : ℕ) (hk : k < w.length) (hr : r < nLocal) (q : List (Fin 2)) :
    Ahead (trajW tickL x0 w k r (w.get ⟨k, hk⟩)).right q := by
  apply ahead_of_place (hcontent k r hk hr)
  have hb := place_bound (placeAt tickL x0 w) delayS (by decide) hstep hp0 hclock (k * nLocal + r)
  rw [placeAt_kr tickL x0 w k r hk hr] at hb
  unfold nLocal delayS at hr hb
  omega

theorem placeAt_end (_hw : 0 < w.length) :
    placeAt tickL x0 w (w.length * nLocal) = place (runW tickL nLocal x0 w).right := by
  unfold placeAt
  have : ¬ (w.length * nLocal / nLocal < w.length) := by
    unfold nLocal delayS; omega
  rw [dif_neg this]

/-- **O5, upper half.**  After `|w|` `stepW`s the right head is at place
`≤ 2 * |w|`: at most the letter half of the last letter. -/
theorem report_place_le (hw : 0 < w.length)
    (hstep : ∀ t, placeAt tickL x0 w (t + 1) ≤ placeAt tickL x0 w t + 1)
    (hp0 : placeAt tickL x0 w 0 = 0)
    (hclock : ∀ s u, s < u → Inc (placeAt tickL x0 w) s → Inc (placeAt tickL x0 w) u →
      s + delayS ≤ u) :
    place (runW tickL nLocal x0 w).right ≤ 2 * w.length := by
  have hb := place_bound (placeAt tickL x0 w) delayS (by decide) hstep hp0 hclock (w.length * nLocal)
  rw [placeAt_end tickL x0 w hw] at hb
  generalize place (runW tickL nLocal x0 w).right = P at hb ⊢
  unfold nLocal delayS at hb
  omega

/-- The keep-up lemma: `hfast` iterated. -/
theorem fast_iter (p : ℕ → ℕ) (T : ℕ) (_hp0 : p 0 = 0)
    (hfast : ∀ t, t + delayS ≤ T → p t + 1 ≤ p (t + delayS)) :
    ∀ m, m * delayS ≤ T → m ≤ p (m * delayS) := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
      intro hm
      have h1 := ih (by rw [Nat.succ_mul] at hm; omega)
      have h2 := hfast (m * delayS) (by rw [Nat.succ_mul] at hm; exact hm)
      rw [Nat.succ_mul]; omega

/-- **O5, both halves.**  With `hfast` — the scaffold keeps up: within the run,
every `delayS` local ticks the right head gains a place — the report place
`2 * |w|` is *reached*, exactly. -/
theorem report_place_eq (hw : 0 < w.length)
    (hstep : ∀ t, placeAt tickL x0 w (t + 1) ≤ placeAt tickL x0 w t + 1)
    (hp0 : placeAt tickL x0 w 0 = 0)
    (hclock : ∀ s u, s < u → Inc (placeAt tickL x0 w) s → Inc (placeAt tickL x0 w) u →
      s + delayS ≤ u)
    (hfast : ∀ t, t + delayS ≤ w.length * nLocal →
      placeAt tickL x0 w t + 1 ≤ placeAt tickL x0 w (t + delayS)) :
    place (runW tickL nLocal x0 w).right = 2 * w.length := by
  have hle := report_place_le tickL x0 w hw hstep hp0 hclock
  have hge := fast_iter (placeAt tickL x0 w) (w.length * nLocal) hp0 hfast (2 * w.length)
    (le_of_eq (by unfold nLocal; ring))
  have he : 2 * w.length * delayS = w.length * nLocal := by unfold nLocal; ring
  rw [he, placeAt_end tickL x0 w hw] at hge
  omega

end Run

#print axioms ahead_of_place
#print axioms ahead_invariant
#print axioms contentLen_arrive
#print axioms contentLen_moveRight
#print axioms contentLen_moveLeftV
#print axioms last_inc
#print axioms inc_bound
#print axioms place_bound
#print axioms hclock_of_abstract
#print axioms runW_take_succ
#print axioms placeAt_kr
#print axioms ahead_along_run
#print axioms placeAt_end
#print axioms report_place_le
#print axioms fast_iter
#print axioms report_place_eq

end PalPeg.LocalArrivalTiming
