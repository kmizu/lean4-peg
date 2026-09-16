import PalPeg.GalilLedgerAssembly
import PalPeg.GalilLedgerObligations
import PalPeg.GalilMoveLemma

/-!
# (O-cost): the tick cost between two consecutive report points

Between the report point for the prefix `m` (right head at `2m-1`, centre
`Cw w m`) and the one for `m+1` (right head at `2m+1`, centre `Cw w (m+1)`)
the right head crosses the two places `2m` and `2m+1`.  The segment belonging
to one place is a `PlaceEvent`:

* a (possibly empty) sequence of chain shifts, each advancing the centre by
  its half period `h ≥ 1` in at most `h + 1` ticks
  (`GalilScaffoldTopShiftCycle` / `shift_phase_stepsAll`, `rounds_center`);
* at most one fallback (copy → home → FPP → markEnd → choose → rewind,
  `≤ 12704·δ + 4012` by `fallback_cost_move`) followed by its replay
  (`≤ 8M·δ` by `replay_cost_le_window`), `δ = k + 1 - chosenRadius (x :: P)`;
  the replay only re-reads places already passed, so it is charged here;
* the background wait (`≤ M = delay` ticks) and the one comparison tick.

`place_event_cost` shows each place fits one `SlotOK` slot plus a comparison
`≤ M` and one dispatch tick; `interval_cost` combines two places with
`ledger_slots'`; `interval_cost_report` identifies the total centre advance
with `Cw w (m+1) - Cw w m` via `cw_eq_of_minv`; `oCost_of_events` is the
`O_cost` oracle of `ledgerObligation_of_oracles`.

The single isolated hypothesis is `AtMostOneFallback` (per place).
Galil guarantees it: the fallback window ends at the mismatching place, the
chosen palindrome (hence the new, leftmost-live centre, `MInv`) covers that
place, and the replay reaches it without a mismatch — so the place is consumed
by the fallback and no second fallback (nor a later shift) occurs at it.
It is needed: a second fallback at one place would add a second constant
`4012`, which `alpha'·δ + beta'` cannot absorb (`3176k + 4012 ≰ 12704·δ` in
general, even with `δ ≥ 1`).
-/

set_option autoImplicit false

namespace PalPeg.GalilIntervalCost

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilLedgerQ64 PalPeg.GalilLedgerAssembly PalPeg.GalilScaffoldChainInputSupply

/-! ## Events -/

/-- One chain shift: centre advance `adv = h ≥ 1`, at most `h + 1` ticks. -/
structure ShiftEv where
  ticks : ℕ
  adv : ℕ
  adv_pos : 1 ≤ adv
  ticks_le : ticks ≤ adv + 1

/-- One fallback together with its replay, at window radius `k` and chosen
radius `r ≤ k`; the centre advance is `k + 1 - r`. -/
structure FallbackEv (M : ℕ) where
  k : ℕ
  r : ℕ
  fb : ℕ
  replay : ℕ
  r_le : r ≤ k
  fb_le : fb ≤ 12704 * (k + 1 - r) + 4012
  replay_le : replay ≤ 8 * M * (k + 1 - r)

namespace FallbackEv
variable {M : ℕ}
def adv (e : FallbackEv M) : ℕ := e.k + 1 - e.r
def ticks (e : FallbackEv M) : ℕ := e.fb + e.replay
end FallbackEv

/-- The segment of the run belonging to one place. -/
structure PlaceEvent (M : ℕ) where
  shifts : List ShiftEv
  fallbacks : List (FallbackEv M)
  wait : ℕ
  wait_le : wait ≤ M

namespace PlaceEvent
variable {M : ℕ}

def shiftTicks (e : PlaceEvent M) : ℕ := (e.shifts.map ShiftEv.ticks).sum
def shiftAdv (e : PlaceEvent M) : ℕ := (e.shifts.map ShiftEv.adv).sum
def fbTicks (e : PlaceEvent M) : ℕ := (e.fallbacks.map FallbackEv.fb).sum
def replayTicks (e : PlaceEvent M) : ℕ := (e.fallbacks.map FallbackEv.replay).sum
def fbAdv (e : PlaceEvent M) : ℕ := (e.fallbacks.map FallbackEv.adv).sum

/-- Slot part: shifts, fallback and replay. -/
def slot (e : PlaceEvent M) : ℕ := e.shiftTicks + e.fbTicks + e.replayTicks

/-- Total ticks of the place: slot, the wait, one comparison tick. -/
def ticks (e : PlaceEvent M) : ℕ := e.slot + e.wait + 1

/-- Total centre advance at the place. -/
def adv (e : PlaceEvent M) : ℕ := e.shiftAdv + e.fbAdv

/-- **The isolated hypothesis.** -/
def AtMostOneFallback (e : PlaceEvent M) : Prop := e.fallbacks.length ≤ 1

end PlaceEvent

/-! ## Per-place cost -/

theorem shifts_ticks_le (l : List ShiftEv) :
    (l.map ShiftEv.ticks).sum ≤ 2 * (l.map ShiftEv.adv).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := a.ticks_le
    have := a.adv_pos
    omega

theorem fallbacks_le {M : ℕ} (e : PlaceEvent M) (h1 : e.AtMostOneFallback) :
    e.fbTicks ≤ 12704 * e.fbAdv + 4012 ∧ e.replayTicks ≤ 8 * M * e.fbAdv := by
  unfold PlaceEvent.AtMostOneFallback at h1
  unfold PlaceEvent.fbTicks PlaceEvent.replayTicks PlaceEvent.fbAdv
  match e.fallbacks, h1 with
  | [], _ => simp
  | [f], _ =>
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    exact ⟨f.fb_le, f.replay_le⟩
  | _ :: _ :: _, h => simp at h

/-- **Per-place cost.** With at most one fallback, the slot part of a place
satisfies `SlotOK M (adv e)`, and the rest is a comparison `≤ M` plus one
dispatch tick. -/
theorem place_event_cost {M : ℕ} (e : PlaceEvent M) (h1 : e.AtMostOneFallback) :
    SlotOK M e.adv e.slot ∧ e.wait ≤ M ∧ e.ticks = e.slot + e.wait + 1 := by
  refine ⟨?_, e.wait_le, rfl⟩
  have hsh : e.shiftTicks ≤ 2 * e.shiftAdv := shifts_ticks_le e.shifts
  obtain ⟨hfb, hrep⟩ := fallbacks_le e h1
  left
  refine ⟨e.replayTicks, e.shiftTicks + e.fbTicks, by unfold PlaceEvent.slot; omega, ?_, ?_⟩
  · have : 8 * M * e.fbAdv ≤ 8 * M * e.adv :=
      Nat.mul_le_mul_left _ (by unfold PlaceEvent.adv; omega)
    omega
  · have : 12704 * e.adv = 12704 * e.shiftAdv + 12704 * e.fbAdv := by
      unfold PlaceEvent.adv; ring
    omega

/-! ## Two consecutive places -/

/-- **Interval cost.** Two consecutive place events, each with at most one
fallback, cost at most `alpha' M · (total advance) + beta' M`. -/
theorem interval_cost {M : ℕ} (e₁ e₂ : PlaceEvent M)
    (h₁ : e₁.AtMostOneFallback) (h₂ : e₂.AtMostOneFallback) :
    e₁.ticks + e₂.ticks ≤ alpha' M * (e₁.adv + e₂.adv) + beta' M := by
  obtain ⟨s₁, w₁, t₁⟩ := place_event_cost e₁ h₁
  obtain ⟨s₂, w₂, t₂⟩ := place_event_cost e₂ h₂
  have := ledger_slots' M e₁.adv e₂.adv e₁.slot e₂.slot (e₁.wait + e₂.wait) 2 s₁ s₂
    (by omega) le_rfl
  omega

/-- Interval cost with the total advance given as a difference of centres. -/
theorem interval_cost_centres {M : ℕ} (e₁ e₂ : PlaceEvent M)
    (h₁ : e₁.AtMostOneFallback) (h₂ : e₂.AtMostOneFallback) (C0 C1 d : ℕ)
    (hadv : C1 = C0 + e₁.adv + e₂.adv) (hd : d = e₁.ticks + e₂.ticks) :
    d ≤ alpha' M * (C1 - C0) + beta' M := by
  have e : C1 - C0 = e₁.adv + e₂.adv := by omega
  rw [e, hd]
  exact interval_cost e₁ e₂ h₁ h₂

/-- **Interval cost between report points.** The run goes from a report point
for `m` to one for `m+1`; the centre moved by the events' advances. Then the
ticks are bounded in terms of `Cw w (m+1) - Cw w m` (`cw_eq_of_minv` at both
ends). -/
theorem interval_cost_report {P : Shared} {q : ℕ} {first : Fin 9} {w : List (Fin 2)} {m : ℕ}
    {st0 st1 : State GalilVM} (hm : 1 ≤ m)
    (r0 : ReportPointAt P q first w m st0) (r1 : ReportPointAt P q first w (m+1) st1)
    (e₁ e₂ : PlaceEvent 2048) (h₁ : e₁.AtMostOneFallback) (h₂ : e₂.AtMostOneFallback)
    (hcentre : position st1.vm.center =
      position st0.vm.center + e₁.adv + e₂.adv)
    (d : ℕ) (hd : d = e₁.ticks + e₂.ticks) :
    d ≤ alpha' 2048 * (Cw w (m+1) - Cw w m) + beta' 2048 := by
  have c0 := cw_eq_of_minv r0.centre r0.notReplaying r0.atPrefix
  have c1 := cw_eq_of_minv r1.centre r1.notReplaying r1.atPrefix
  have _ := hm
  exact interval_cost_centres e₁ e₂ h₁ h₂ _ _ d (by rw [← c0, ← c1]; exact hcentre) hd

/-- **The `O_cost` oracle.** If every interval `m → m+1` (`m < |w|`) of the
run decomposes into two place events with at most one fallback each, whose
advances sum to `Cw w (m+1) - Cw w m`, and `dw w (m+1)` is their tick count,
then `O_cost` of `ledgerObligation_of_oracles` holds. The centre hypothesis is
stated on `Cw` so that the `m = 0` interval (no report point at `0`) is
covered as well; for `m ≥ 1` it follows from `interval_cost_report`'s
`hcentre`. -/
theorem oCost_of_events (dw : List (Fin 2) → ℕ → ℕ)
    (ev : List (Fin 2) → ℕ → PlaceEvent 2048 × PlaceEvent 2048)
    (hone : ∀ w : List (Fin 2), 0 < w.length → ∀ m, m < w.length →
      (ev w m).1.AtMostOneFallback ∧ (ev w m).2.AtMostOneFallback)
    (hadv : ∀ w : List (Fin 2), 0 < w.length → ∀ m, m < w.length →
      Cw w (m+1) = Cw w m + (ev w m).1.adv + (ev w m).2.adv)
    (hticks : ∀ w : List (Fin 2), 0 < w.length → ∀ m, m < w.length →
      dw w (m+1) = (ev w m).1.ticks + (ev w m).2.ticks) :
    ∀ w : List (Fin 2), 0 < w.length → ∀ m, m < w.length →
      dw w (m+1) ≤ alpha' 2048 * (Cw w (m+1) - Cw w m) + beta' 2048 := by
  intro w hw m hm
  exact interval_cost_centres _ _ (hone w hw m hm).1 (hone w hw m hm).2 _ _ _
    (hadv w hw m hm) (hticks w hw m hm)

/-! ## Building events from the machine lemmas -/

/-- A fallback event from the real window `x :: P` (matched palindrome of
radius `k`): the move inequality comes from `galil_move_of_contract`, the
replay bound from `replay_cost_le_window`, and the fallback tick bound is the
conclusion shape of `GalilLedger2.fallback_cost_move` (`∀ δ, k ≤ 4δ → …`). -/
noncomputable def fallbackEv_of_window (M : ℕ) (x : Fin 3) (P : List (Fin 3)) (hP : IsPal P)
    (k fb replay : ℕ) (hlen : P.length = 2*k + 1)
    (contract : ∀ p, 0 < p → HasPeriod P p → k < 2*p)
    (hfb : ∀ δ, k ≤ 4*δ → fb ≤ 12704*δ + 4012)
    (hreplay : replay ≤ 2*M*k) : FallbackEv M where
  k := k
  r := chosenRadius (x :: P)
  fb := fb
  replay := replay
  r_le := by
    have h := (chosen_spec (x :: P) (List.cons_ne_nil x P)).1
    rw [List.length_cons, hlen] at h
    omega
  fb_le := hfb _ (galil_move_of_contract x P hP k hlen contract)
  replay_le := GalilLedger.replay_cost_le_window M x P hP k replay hlen hreplay contract

theorem fallbackEv_of_window_adv (M : ℕ) (x : Fin 3) (P : List (Fin 3)) (hP : IsPal P)
    (k fb replay : ℕ) (hlen : P.length = 2*k + 1)
    (contract : ∀ p, 0 < p → HasPeriod P p → k < 2*p)
    (hfb : ∀ δ, k ≤ 4*δ → fb ≤ 12704*δ + 4012) (hreplay : replay ≤ 2*M*k) :
    (fallbackEv_of_window M x P hP k fb replay hlen contract hfb hreplay).adv =
      k + 1 - chosenRadius (x :: P) := rfl

/-- The fallback advances the centre by at least one. -/
theorem fallbackEv_adv_pos {M : ℕ} (f : FallbackEv M) : 1 ≤ f.adv := by
  have := f.r_le
  unfold FallbackEv.adv
  omega

/-- A matched place: no shift, no fallback, only the wait and the comparison. -/
def matchedEv (M wait : ℕ) (h : wait ≤ M) : PlaceEvent M := ⟨[], [], wait, h⟩

theorem matchedEv_cost (M wait : ℕ) (h : wait ≤ M) :
    (matchedEv M wait h).ticks = wait + 1 ∧ (matchedEv M wait h).adv = 0 := by
  simp [matchedEv, PlaceEvent.ticks, PlaceEvent.slot, PlaceEvent.shiftTicks, PlaceEvent.fbTicks,
    PlaceEvent.replayTicks, PlaceEvent.adv, PlaceEvent.shiftAdv, PlaceEvent.fbAdv]

#print axioms shifts_ticks_le
#print axioms fallbacks_le
#print axioms place_event_cost
#print axioms interval_cost
#print axioms interval_cost_centres
#print axioms interval_cost_report
#print axioms oCost_of_events
#print axioms fallbackEv_of_window
#print axioms fallbackEv_of_window_adv
#print axioms fallbackEv_adv_pos
#print axioms matchedEv_cost

end PalPeg.GalilIntervalCost
