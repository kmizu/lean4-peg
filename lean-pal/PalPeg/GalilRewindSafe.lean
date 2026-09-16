import PalPeg.GalilRunInv

/-!
# `RewindSafe` holds all along a run (gap 7 of `GalilRunInv`)

`GalilRunInv.frontier_replayRest_steps` carries `Frontier` and `ReplayRest`
along a run of the concrete scaffold, but only under the per-state side
condition `RewindSafe`: at a `replayStart` the radius counter is a
natural number `r`, and the rewind it authorises (`r` left steps of the
centre) stays inside the arrived material.

This module discharges that condition from the control flow itself.  The
carrier is `RewindPhase`, a *mode-guarded* invariant:

> while the controller is in `rewind` or `replayStart` mode, the radius is
> `ofNat r` for some `r` and `position center + r ≤ 2 * arrived center`.

Guarding by the mode is essential.  The radius is **not** globally an
`ofNat`: `shiftTick` decrements it during a chain shift, and a decrement
below zero leaves the `ofNat` image.  But the only entry into `rewind` is
`choose_select`, which *resets* the radius and puts the centre on the right
head, so the invariant is re-established from scratch at every rewind, and
the two rewind ticks plus `rewind_done` preserve it.

One step is not derivable from `Tick` alone and is isolated as
`CentreLive`: `rewind_pair` moves the centre one place left, and that only
lowers `position` when the centre is not already at the origin.  In the
machine the walk stops at the `FIRST` mark strictly before the origin; that
is a property of the MARKS tape, not of the controller, so it is assumed.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter

/-! ## The carrier -/

/-- The rewind-phase invariant: during `rewind`/`replayStart` the radius is a
natural-number counter and the rewind it authorises stays inside the arrived
material of the centre head. -/
def RewindPhase (c : Control) (s : GalilVM) : Prop :=
  (c.mode = Mode.rewind ∨ c.mode = Mode.replayStart) →
    ∃ r, s.radius = ofNat r ∧ position s.center + r ≤ 2 * arrived s.center

/-- **The one isolated assumption.**  A `rewind_pair` tick moves the centre
one place left; that lowers `position` only away from the origin.  Scala's
rewind walk stops at the `FIRST` mark, which sits strictly to the right of
the origin, but the stopping condition lives on the MARKS tape and is not
visible to `Tick`. -/
def CentreLive (c : Control) (s : GalilVM) : Prop :=
  c.mode = Mode.rewind → c.pair = true → 0 < position s.center

/-- `RewindPhase` is exactly the side condition `frontier_replayRest_steps`
asks for. -/
theorem rewindSafe_of_phase {c : Control} {s : GalilVM} (h : RewindPhase c s) :
    RewindSafe c s := by
  refine ⟨fun hm => ?_, fun hm r hr => ?_⟩
  · obtain ⟨r, hr, -⟩ := h (Or.inr hm)
    exact ⟨r, hr⟩
  · obtain ⟨r', hr', hb⟩ := h (Or.inr hm)
    have hrr : r = r' := ofNat_inj (hr.symm.trans hr')
    rw [hrr]; exact hb

/-- Outside the two rewind modes the invariant is vacuous. -/
theorem rewindPhase_of_mode {c : Control} {s : GalilVM} {m : Mode}
    (h1 : m ≠ Mode.rewind) (h2 : m ≠ Mode.replayStart) (h : c.mode = m) :
    RewindPhase c s := by
  intro hm
  rcases hm with hm | hm
  · exact absurd (h.symm.trans hm) h1
  · exact absurd (h.symm.trans hm) h2

/-- Discharge a tick whose landing mode is neither `rewind` nor `replayStart`. -/
macro "vacuous_mode" : tactic =>
  `(tactic| first
    | exact rewindPhase_of_mode (m := Mode.init) (by decide) (by decide)
        (by first | rfl | assumption)
    | exact rewindPhase_of_mode (m := Mode.scan) (by decide) (by decide)
        (by first | rfl | assumption)
    | exact rewindPhase_of_mode (m := Mode.shift) (by decide) (by decide)
        (by first | rfl | assumption)
    | exact rewindPhase_of_mode (m := Mode.copy) (by decide) (by decide)
        (by first | rfl | assumption)
    | exact rewindPhase_of_mode (m := Mode.home) (by decide) (by decide)
        (by first | rfl | assumption)
    | exact rewindPhase_of_mode (m := Mode.fpp) (by decide) (by decide)
        (by first | rfl | assumption)
    | exact rewindPhase_of_mode (m := Mode.markEnd) (by decide) (by decide)
        (by first | rfl | assumption)
    | exact rewindPhase_of_mode (m := Mode.choose) (by decide) (by decide)
        (by first | rfl | assumption))

/-! ## (1) Preservation by one tick -/

/-- Every controller tick of the concrete scaffold preserves `RewindPhase`,
given `CentreLive` at the source state. -/
theorem rewindPhase_tick (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)
    {c c' : Control} {s t : GalilVM}
    (hp : RewindPhase c s) (hg : CentreLive c s)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : RewindPhase c' t := by
  cases h
  all_goals try vacuous_mode
  -- the establishment: `stepChoose` puts C on R and zeroes the radius
  case choose_select =>
    rename_i hm hodd hs hi
    have hc : t.center = s.right := congrArg RewindVM.center hi.1
    have hr : t.radius = reset := congrArg RewindVM.radius hi.1
    intro _
    refine ⟨0, by rw [hr]; rfl, ?_⟩
    rw [hc]
    simpa using position_le_arrived s.right
  -- `stepRewind` without the centre move: C and the radius are untouched
  case rewind_one =>
    rename_i hm h1 h2 hi
    have hc : t.center = s.center := congrArg RewindVM.center hi.1.2
    have hr : t.radius = s.radius := congrArg RewindVM.radius hi.1.2
    intro _
    obtain ⟨r, hrad, hb⟩ := hp (Or.inl hm)
    exact ⟨r, by rw [hr]; exact hrad, by rw [hc]; exact hb⟩
  -- `stepRewind` with the centre move: C one place left, `radius++`
  case rewind_pair =>
    rename_i hm h1 h2 hi
    have hc : t.center = GalilScaffoldInputHead.left s.center :=
      congrArg RewindVM.center hi.1.2
    have hr : t.radius = inc s.radius := congrArg RewindVM.radius hi.1.2
    intro _
    obtain ⟨r, hrad, hb⟩ := hp (Or.inl hm)
    have hpos : 0 < position s.center := hg hm h1
    have hstep := left_position_pos hpos
    have harr := arrived_left s.center
    refine ⟨r + 1, ?_, ?_⟩
    · rw [hr, hrad, inc_ofNat]
    · rw [hc, harr]; omega
  -- `rewind_done`: `fpp.reset()` touches neither C nor the radius
  case rewind_done =>
    rename_i hm h1 hi
    have hc : t.center = s.center := congrArg RewindVM.center hi.1
    have hr : t.radius = s.radius := congrArg RewindVM.radius hi.1
    intro _
    obtain ⟨r, hrad, hb⟩ := hp (Or.inl hm)
    exact ⟨r, by rw [hr]; exact hrad, by rw [hc]; exact hb⟩

/-! ## (2) Preservation along a run -/

/-- `RewindPhase` travels along any run whose states are all `CentreLive`. -/
theorem rewindPhase_steps (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)
    {n : ℕ} {x y : State GalilVM}
    (h : Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay n x y)
    (hg : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay m x z →
      CentreLive z.ctl z.vm)
    (hp : RewindPhase x.ctl x.vm) : RewindPhase y.ctl y.vm := by
  induction h with
  | zero x => exact hp
  | @succ n x w y ht _ ih =>
    refine ih (fun m z hz => hg (m+1) z (.succ ht hz)) ?_
    exact rewindPhase_tick onLetter leftFirst centre place entry q first delay hp
      (hg 0 x (.zero x)) ht

/-! ## (3) The deliverable -/

/-- **`rewindSafe_of_run`.**  From a state parked in `scan` mode — where the
rewind invariant is vacuous — every state reachable by the concrete scaffold
is `RewindSafe`, provided the rewind walk never steps the centre at the
origin (`CentreLive`). -/
theorem rewindSafe_of_run (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)
    {x : State GalilVM} (hx : x.ctl.mode = Mode.scan)
    (hg : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay m x z →
      CentreLive z.ctl z.vm) :
    ∀ (n : ℕ) (y : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay n x y →
      RewindSafe y.ctl y.vm := by
  intro n y hy
  exact rewindSafe_of_phase (rewindPhase_steps onLetter leftFirst centre place entry q first delay
    hy hg (rewindPhase_of_mode (by decide) (by decide) hx))

/-- The gap-7 consequence: `Frontier` and `ReplayRest` travel along a run out
of a `scan` state with no `RewindSafe` side condition left to supply. -/
theorem frontier_replayRest_of_scan (onLetter leftFirst : GalilVM → Prop)
    (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ)
    (first : Fin 9) (delay : ℕ) {n : ℕ} {x y : State GalilVM}
    (h : Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay n x y)
    (hx : x.ctl.mode = Mode.scan)
    (hg : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay m x z →
      CentreLive z.ctl z.vm)
    (hf : Frontier x.vm) (hr : ReplayRest x.ctl x.vm) :
    Frontier y.vm ∧ ReplayRest y.ctl y.vm :=
  frontier_replayRest_steps onLetter leftFirst centre place entry q first delay h
    (fun m z hz => rewindSafe_of_run onLetter leftFirst centre place entry q first delay hx hg m z hz)
    hf hr

#print axioms rewindSafe_of_phase
#print axioms rewindPhase_of_mode
#print axioms rewindPhase_tick
#print axioms rewindPhase_steps
#print axioms rewindSafe_of_run
#print axioms frontier_replayRest_of_scan

end PalPeg.GalilScaffoldChainInputSupply
