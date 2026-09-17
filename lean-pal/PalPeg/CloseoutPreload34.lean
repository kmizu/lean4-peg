import PalPeg.CloseoutPreload33

/-!
# Discharging `H_exitNotFire`: the `.wait → .double` exit is not a comparison

`CloseoutPreload33.legsCoupled_galil` takes the one named hypothesis
`H_exitNotFire : p3.ctl.clock ≠ 1` on the `.wait → .double` exit tick.  This
file proves it from the machine run (`exitNotFire_of_wait`) and restates the
round trip without it (`postRunF_round_trip_galil'`).

* §1 the run exit.  `finish` enters `.wait` only at a non-zero debt
  (`finish_wait_nonzero`, kept along the 64 calls by `safeCalls_wait_nonzero`),
  and the quantum's outer `advance a` is the only place the debt moves; so a
  `.run` tick that lands in `.wait` with debt `0` is a match, `a = true`
  (`run_exit_wait_match`).  This is the empty-leg case (`ws = []`): the clock
  at `p2 = p3` was set by that tick.
* §2 the wait leg.  The exit fires at `zero debt = true` (`wait_step_cases`),
  a tick that stays in `.wait` starts at `zero debt = false`, and the debt
  falls only at matches — so the last tick of a non-empty leg ending at zero
  debt is a match (`idleLeg_wait_last`).
* §3 a `ScanTrace` tick recording `true` is the `fire` branch and resets the
  clock to `2048` (`scanTrace_single_true_clock`); both cases give
  `p3.ctl.clock = 2048 ≠ 1`.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload34

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController
open PalPeg.GalilScaffoldSearchFinish (Mode finish)
open PalPeg.GalilScaffoldSearchRun (SafeCalls SafeQuanta advance)
open PalPeg.GalilScaffoldCounter (Canonical value ofNat positive zero zero_iff)
open PalPeg.CloseoutReadyStage (PacedL)
open PalPeg.CloseoutPreload10 (PrepAt)
open PalPeg.CloseoutPreload13 (RunTrace run_step_quanta)
open PalPeg.CloseoutPreload14 (WaitTrace wait_step_cases)
open PalPeg.CloseoutPreload17 (DoubleTrace)
open PalPeg.CloseoutPreload21 (ScanTrace)
open PalPeg.CloseoutPreload22 (ClockInv)
open PalPeg.CloseoutPreload23 (ScanSupplyInv)
open PalPeg.CloseoutPreload28 (StageInvD)
open PalPeg.CloseoutPreload32 (canonical_runTrace canonical_run_step canonical_wait_step
  canonical_waitTrace)
open PalPeg.CloseoutPreload33 (RestartOnBroken IdleLeg scanTrace_single_searchStep
  idleLeg_runTrace idleLeg_waitTrace postRunF_round_trip_galil)
open PalPeg.GalilLeafPres (safeCalls_debt)

/-! ## 1. The run exit lands in `.wait` only at a non-zero debt -/

/-- `finish` enters `.wait` only when `zero debt = false`; elsewhere it keeps
the state (and so the invariant). -/
theorem finish_wait_nonzero (s : GalilScaffoldSearchFinish.State) (b done : Bool) (pc : ℕ)
    (h : s.mode = Mode.wait → zero s.debt = false) :
    (finish s (b && decide (s.mode = Mode.run)) done pc).mode = Mode.wait →
      zero (finish s (b && decide (s.mode = Mode.run)) done pc).debt = false := by
  by_cases hm : s.mode = Mode.run
  · cases b <;> cases done <;> by_cases hp : pc = 346 <;>
      cases hf : s.finalStage <;> cases hz : zero s.debt <;>
      simp [finish, hm, hp, hf, hz]
  · simpa [finish, hm] using h

theorem safeCalls_wait_nonzero {s t : GalilScaffoldSearchFinish.State}
    {x y : GalilScaffoldControl.Machine 12} {bs : List Bool}
    (hr : SafeCalls s x bs t y) (h : s.mode = Mode.wait → zero s.debt = false) :
    t.mode = Mode.wait → zero t.debt = false := by
  induction hr with
  | nil => exact h
  | cons s x y z b bs t ht hsafe hr ih => exact ih (finish_wait_nonzero s b y.done y.config.pc h)

/-- A one-tick quantum is 64 calls then one outer `advance`. -/
theorem safeQuanta_single {s t : GalilScaffoldSearchFinish.State}
    {x y : GalilScaffoldControl.Machine 12} {a : Bool}
    (h : SafeQuanta s x [a] t y) :
    ∃ u z, SafeCalls s x (List.replicate 64 true) u z ∧ t = advance a u := by
  cases h with
  | cons s u t x y z a as hm hq hr =>
      cases hr
      exact ⟨u, y, hq, rfl⟩

/-- **NAMED — a `.run` tick landing in `.wait` with zero debt is a match.** -/
theorem run_exit_wait_match {c : GalilScaffoldPlace.Place} {a : Bool} {v v' : SearchVM}
    (hm : v.search.mode = Mode.run) (hs : searchStep c a v v')
    (hc : Canonical v.search.debt) (hw : v'.search.mode = Mode.wait)
    (hz : value v'.search.debt = 0) : a = true := by
  obtain ⟨hq, -, -⟩ := run_step_quanta hm hs
  obtain ⟨u, z, hcalls, ht⟩ := safeQuanta_single hq
  have hnz := safeCalls_wait_nonzero hcalls (fun h => by rw [hm] at h; exact Mode.noConfusion h)
  have hud : u.debt = v.search.debt := safeCalls_debt hcalls
  cases a with
  | true => rfl
  | false =>
      exfalso
      have hu : v'.search = u := ht
      rw [hu] at hw hz
      have hcu : Canonical u.debt := hud ▸ hc
      have := (zero_iff _ hcu).mpr hz
      rw [hnz hw] at this
      exact Bool.noConfusion this

#print axioms run_exit_wait_match

/-! ## 2. The wait leg: its last tick before zero debt is a match -/

/-- A `ScanTrace` tick recording `true` is the `fire` branch: the clock is
reset to the delay. -/
theorem scanTrace_single_true_clock {σ : Type} {F : Frame σ} {t : Bool}
    {p p' : State σ} (h : ScanTrace F 2048 [t] [true] p p') : p'.ctl.clock = 2048 := by
  cases h with
  | fire c s s'' o rp ts as qq ht hm hav hc1 hr =>
      cases hr
      rfl

variable (P : Shared) (q : ℕ) (first : Fin 9)

/-- **NAMED — the last tick of a `.wait` idle leg ending at zero debt.**
Either the leg is empty, or its last tick is a match and so resets the clock. -/
theorem idleLeg_wait_last (hres : RestartOnBroken P) {ws : List Bool} {p2 p3 : State GalilVM}
    (hwaitL : IdleLeg P q first (fun s => s.search.mode = Mode.wait) ws p2 p3)
    (hcan : Canonical p2.vm.search.debt)
    (hw1 : p3.vm.search.mode = Mode.wait) (hz : zero p3.vm.search.debt = true) :
    (ws = [] ∧ p3 = p2) ∨ p3.ctl.clock = 2048 := by
  induction hwaitL with
  | nil p => exact Or.inl ⟨rfl, rfl⟩
  | cons t a as p p' r hidle hM h1 hr ih =>
      have hs : searchStep (P.place p.vm) a (searchLens.get p.vm) (searchLens.get p'.vm) :=
        scanTrace_single_searchStep P q first hres h1 hidle
      have hcan' : Canonical p'.vm.search.debt := canonical_wait_step hM hs hcan
      rcases ih hcan' hw1 hz with ⟨-, hrp⟩ | hclk
      · rw [hrp] at hz hw1
        rw [hrp]
        obtain ⟨-, -, hd, hc | hc⟩ := wait_step_cases hM hs
        · have hd' : value p'.vm.search.debt =
              value p.vm.search.debt - (if a then 1 else 0) := hd
          have hc1 : zero p.vm.search.debt = false := hc.1
          have hv' : value p'.vm.search.debt = 0 := (zero_iff _ hcan').mp hz
          cases a with
          | false =>
              exfalso
              have hv : value p.vm.search.debt = 0 := by simp at hd'; omega
              have := (zero_iff _ hcan).mpr hv
              rw [hc1] at this
              exact Bool.noConfusion this
          | true => exact Or.inr (scanTrace_single_true_clock h1)
        · exfalso
          have h2 : p'.vm.search.mode = Mode.double := hc.2.1
          rw [hw1] at h2
          exact Mode.noConfusion h2
      · exact Or.inr hclk

#print axioms idleLeg_wait_last

/-! ## 3. `H_exitNotFire`, and the round trip without it -/

/-- **NAMED — the `.wait → .double` exit tick is taken off clock `1`.**  The
hypotheses are those of `postRunF_round_trip_galil` (the run leg, its exit, the
wait leg, its exit, the mode/idle annotations, and `Canonical` at `p0`; the
`.run` mode at `p0` is not needed). -/
theorem exitNotFire_of_wait {rs ws : List Bool} {t1 t2 a1 a2 : Bool}
    {p0 p1 p2 p3 p4 : State GalilVM}
    (hres : RestartOnBroken P) (hcan : Canonical p0.vm.search.debt)
    (hrunL : IdleLeg P q first (fun s => s.search.mode = Mode.run) rs p0 p1)
    (ht0 : p1.vm.search.mode = Mode.run) (hidle1 : p1.vm.chain = ChainVM.idle)
    (hex1 : ScanTrace (galilFrameS P q first) 2048 [t1] [a1] p1 p2)
    (hw0 : p2.vm.search.mode = Mode.wait)
    (hwaitL : IdleLeg P q first (fun s => s.search.mode = Mode.wait) ws p2 p3)
    (hw1 : p3.vm.search.mode = Mode.wait) (hidle3 : p3.vm.chain = ChainVM.idle)
    (hex2 : ScanTrace (galilFrameS P q first) 2048 [t2] [a2] p3 p4)
    (hne : p4.vm.search.mode ≠ Mode.wait) :
    p3.ctl.clock ≠ 1 := by
  have hrun := idleLeg_runTrace P q first hres hrunL
  have hwait := idleLeg_waitTrace P q first hres hwaitL
  have hs1 := scanTrace_single_searchStep P q first hres hex1 hidle1
  have hs2 := scanTrace_single_searchStep P q first hres hex2 hidle3
  have hcan1 : Canonical p1.vm.search.debt := canonical_runTrace hrun hcan
  have hcan2 : Canonical p2.vm.search.debt := canonical_run_step ht0 hs1 hcan1
  have hcan3 : Canonical p3.vm.search.debt := canonical_waitTrace hwait hcan2
  -- the exit fires at zero debt
  have hz3 : zero p3.vm.search.debt = true := by
    obtain ⟨-, -, -, hc | hc⟩ := wait_step_cases hw1 hs2
    · exact absurd hc.2.1 hne
    · exact hc.1
  rcases idleLeg_wait_last P q first hres hwaitL hcan2 hw1 hz3 with ⟨-, hp⟩ | hclk
  · subst hp
    have hv2 : value p3.vm.search.debt = 0 := (zero_iff _ hcan2).mp hz3
    have ha1 : a1 = true := run_exit_wait_match ht0 hs1 hcan1 hw0 hv2
    subst ha1
    rw [scanTrace_single_true_clock hex1]
    decide
  · rw [hclk]; decide

#print axioms exitNotFire_of_wait

/-- **NAMED — `postRunF_round_trip_galil` with `H_exitNotFire` discharged.** -/
theorem postRunF_round_trip_galil' {I : State GalilVM → Prop} {k mw : ℕ}
    {ts0 pre rs ws bs : List Bool} {t1 t2 a1 a2 a3 : Bool}
    {p p0 p1 p2 p3 p4 : State GalilVM}
    (hres : RestartOnBroken P)
    (hsup : ScanSupplyInv (galilFrameS P q first) 2048 I)
    (hm : p0.vm.search.mode = Mode.run) (hsp : p0.vm.search.span = ofNat mw)
    (hlow : p0.vm.lower = ofNat k) (hcal : 8 * max k 1 ≤ mw)
    (hcan : Canonical p0.vm.search.debt)
    (hpre : ScanTrace (galilFrameS P q first) 2048 ts0 pre p p0)
    (hrunL : IdleLeg P q first (fun s => s.search.mode = Mode.run) rs p0 p1)
    (ht0 : p1.vm.search.mode = Mode.run) (hidle1 : p1.vm.chain = ChainVM.idle)
    (hex1 : ScanTrace (galilFrameS P q first) 2048 [t1] [a1] p1 p2)
    (hw0 : p2.vm.search.mode = Mode.wait)
    (hwaitL : IdleLeg P q first (fun s => s.search.mode = Mode.wait) ws p2 p3)
    (hw1 : p3.vm.search.mode = Mode.wait) (hidle3 : p3.vm.chain = ChainVM.idle)
    (hex2 : ScanTrace (galilFrameS P q first) 2048 [t2] [a2] p3 p4)
    (hne : p4.vm.search.mode ≠ Mode.wait)
    (hp : I p) (hclk : ClockInv 2048 p.ctl)
    (hblen : bs.length = mw)
    (hpaced : PacedL 2048 0 ((pre ++ (rs ++ a1 :: (ws ++ [false]))) ++ (bs ++ [a3]))) :
    ∃ t1 : SearchVM, DoubleTrace bs (searchLens.get p4.vm) t1 ∧ t1.search.mode = Mode.double ∧
      positive t1.search.work = false ∧ t1.search.span = ofNat (2 * mw) ∧
      t1.lower = ofNat k ∧
      ∀ (c' : GalilScaffoldPlace.Place) (t' : SearchVM), searchStep c' a3 t1 t' →
        PrepAt k (2 * mw) t' ∧ StageInvD k (2 * mw) t' ∧ t'.walker = c' ∧
          8 * max k 1 ≤ 2 * mw :=
  postRunF_round_trip_galil P q first hres hsup hm hsp hlow hcal hcan hpre hrunL ht0 hidle1
    hex1 hw0 hwaitL hw1 hidle3 hex2
    (exitNotFire_of_wait P q first hres hcan hrunL ht0 hidle1 hex1 hw0 hwaitL hw1 hidle3
      hex2 hne)
    hne hp hclk hblen hpaced

#print axioms postRunF_round_trip_galil'

/-!
## 4. What is left

Closed: `H_exitNotFire` (`exitNotFire_of_wait`), hence `postRunF_round_trip_galil'`
takes no clock hypothesis on the `.wait → .double` exit.  No new hypothesis was
needed for the empty wait leg: `finish` refuses `.wait` at zero debt, so the run
exit that lands in `.wait` with zero debt is itself a match tick.

**無条件 PAL ∈ PEG は未完.**
-/

end PalPeg.CloseoutPreload34
