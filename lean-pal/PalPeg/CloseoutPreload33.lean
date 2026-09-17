import PalPeg.CloseoutPreload32
import PalPeg.GalilTickFair

/-!
# `LegsCoupled` on the concrete frame `galilFrameS`

`CloseoutPreload32` packages the event coupling of the `.run` / `.wait` legs
with the scan leg as the single hypothesis `LegsCoupled`, and observes that it
cannot be built for a generic `Frame σ`.  This file builds it on `galilFrameS`.

* §1 `IdleLeg`: a scan leg of `galilFrameS` ticks, one `ScanTrace` tick at a
  time, each taken with the chain idle and the search VM in the mode `M`.
  `ScanTrace` alone does *not* pin a tick to `scan_wait` / `scan_count` /
  `scan_match`: `Tick.restart` shares all three controller shapes when the
  clock is already at `delay`, and `P.restart` is unconstrained.  So §1 also
  names `RestartOnBroken P` — the restart fires only at a non-idle chain —
  and discharges it for the concrete `restartVM` (`GalilTickFair`,
  `restartGuard_of_restartVM`).
* §2 the per-tick coupling: a one-tick `ScanTrace` at an idle chain feeds
  `searchStep (P.place s)` exactly the boolean it records
  (`scanTrace_single_searchStep`; the three branches are
  `CloseoutPreload22.background_event_false` / `compare_event_true_of_matched`,
  the `matchedPlace` step leaves the search lens alone).  Hence
  `idleLeg_runTrace` / `idleLeg_waitTrace`: the search projection of an
  `IdleLeg` in mode `.run` / `.wait` is a `RunTrace` / `WaitTrace` with the
  same booleans.
* §3 `scanTrace_append` and `idleLeg_scanTrace`, then `legsCoupled_galil`.
  The exit tick's boolean is `false` because a tick taken off clock `1` is
  never `scan_match` (`scanTrace_single_false_of_clock`) — the **one named
  hypothesis** is `H_exitNotFire : p3.ctl.clock ≠ 1` on the `.wait → .double`
  exit tick.
* §4 `postRunF_round_trip_galil`: `CloseoutPreload32.postRunF_round_trip'`
  with the four `SearchVM` legs *derived* from the machine run.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload33

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController
open PalPeg.GalilScaffoldSearchFinish (Mode)
open PalPeg.GalilScaffoldCounter (Canonical value ofNat positive zero)
open PalPeg.CloseoutReadyStage (PacedL)
open PalPeg.CloseoutPreload10 (PrepAt)
open PalPeg.CloseoutPreload13 (RunTrace)
open PalPeg.CloseoutPreload14 (WaitTrace)
open PalPeg.CloseoutPreload17 (DoubleTrace)
open PalPeg.CloseoutPreload21 (ScanTrace)
open PalPeg.CloseoutPreload22 (ClockInv background_event_false compare_event_true_of_matched)
open PalPeg.CloseoutPreload23 (ScanSupplyInv)
open PalPeg.CloseoutPreload28 (StageInvD)
open PalPeg.CloseoutPreload32 (LegsCoupled postRunF_round_trip')
open PalPeg.GalilTickFair (tick_scan_cases restartGuard_of_restartVM)

/-! ## 1. Idle scan legs, and the restart shape -/

/-- **NAMED — the restart fires only at a non-idle chain.**  `Tick.restart`
carries the abstract `P.restart`; on the concrete `restartVM` the source chain
is `.broken _`. -/
def RestartOnBroken (P : Shared) : Prop :=
  ∀ s s' : GalilVM, P.restart s s' → s.chain ≠ ChainVM.idle

/-- The concrete restart satisfies `RestartOnBroken`. -/
theorem restartOnBroken_of_restartVM {P : Shared} {entry : ℕ}
    (h : ∀ s s', P.restart s s' → restartVM entry s s') : RestartOnBroken P := by
  intro s s' hr hidle
  obtain ⟨w, hw, -, -, -⟩ := restartGuard_of_restartVM (h s s' hr)
  rw [hidle] at hw
  exact ChainVM.noConfusion hw

theorem restartOnBroken_sharedC (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ) :
    RestartOnBroken (sharedC onLetter leftFirst centre place entry) :=
  restartOnBroken_of_restartVM (entry := entry) (fun _ _ h => h)

#print axioms restartOnBroken_sharedC

variable (P : Shared) (q : ℕ) (first : Fin 9)

/-- **NAMED — an idle scan leg.**  Consecutive one-tick `ScanTrace`s of
`galilFrameS P q first`, each taken with the chain idle and the search VM in
mode `M`; `as` is the event list `ScanTrace` records. -/
inductive IdleLeg (M : GalilVM → Prop) : List Bool → State GalilVM → State GalilVM → Prop
  | nil (p : State GalilVM) : IdleLeg M [] p p
  | cons (t a : Bool) (as : List Bool) (p p' r : State GalilVM)
      (hidle : p.vm.chain = ChainVM.idle) (hM : M p.vm)
      (h1 : ScanTrace (galilFrameS P q first) 2048 [t] [a] p p')
      (hr : IdleLeg M as p' r) : IdleLeg M (a :: as) p r

/-! ## 2. The per-tick coupling -/

/-- The `matchedPlace` step touches only `replay`: the search lens is kept. -/
theorem searchLens_matchedPlace {b : Bool} {s t : GalilVM}
    (h : (galilFrameS P q first).matchedPlace b s t) : searchLens.get t = searchLens.get s := by
  have e : t = (if b then {s with replay := GalilScaffoldCounter.dec s.replay} else s) := h
  rw [e]
  cases b <;> rfl

/-- **NAMED — the per-tick coupling on `galilFrameS`.**  A one-tick scan leg at
an idle chain feeds `searchStep (P.place s)` the boolean it records. -/
theorem scanTrace_single_searchStep (hres : RestartOnBroken P) {t a : Bool}
    {p p' : State GalilVM}
    (h : ScanTrace (galilFrameS P q first) 2048 [t] [a] p p')
    (hidle : p.vm.chain = ChainVM.idle) :
    searchStep (P.place p.vm) a (searchLens.get p.vm) (searchLens.get p'.vm) := by
  cases h with
  | wait c s s' ts as qq ht hm hav hr =>
      cases hr
      rcases tick_scan_cases hm ht with ⟨s1, -, -, hb, he⟩ | ⟨s1, -, hc, -, he⟩ |
        ⟨s1, -, hc, -, hd⟩ | ⟨s1, hb, he⟩
      · cases he
        exact background_event_false P q first hb hidle
      · exfalso
        have := congrArg (fun x : State GalilVM => x.ctl.clock) he
        simp at this
        omega
      · exfalso
        rcases hd with ⟨s2, o2, -, -, -, he⟩ | ⟨s2, -, -, -, -, he⟩ | ⟨s2, -, -, -, -, he⟩
        all_goals
          have := congrArg (fun x : State GalilVM => x.ctl.clock) he
          simp at this
          omega
      · exact absurd hidle (hres _ _ hb)
  | count c s s' ts as qq ht hm hav hc hr =>
      cases hr
      rcases tick_scan_cases hm ht with ⟨s1, -, -, hb, he⟩ | ⟨s1, -, -, hb, he⟩ |
        ⟨s1, -, hc1, -, hd⟩ | ⟨s1, hb, he⟩
      · exfalso
        have := congrArg (fun x : State GalilVM => x.ctl.clock) he
        simp at this
        omega
      · cases he
        exact background_event_false P q first hb hidle
      · exfalso
        rcases hd with ⟨s2, o2, -, -, -, he⟩ | ⟨s2, -, -, -, -, he⟩ | ⟨s2, -, -, -, -, he⟩
        all_goals
          have := congrArg (fun x : State GalilVM => x.ctl.clock) he
          simp at this
          omega
      · exact absurd hidle (hres _ _ hb)
  | fire c s s'' o rp ts as qq ht hm hav hc hr =>
      cases hr
      rcases tick_scan_cases hm ht with ⟨s1, -, -, -, he⟩ | ⟨s1, -, hc1, -, he⟩ |
        ⟨s1, -, -, hcmp, he⟩ | ⟨s1, hb, he⟩
      · exfalso
        have := congrArg (fun x : State GalilVM => x.ctl.clock) he
        simp at this
        omega
      · exfalso
        have := congrArg (fun x : State GalilVM => x.ctl.clock) he
        simp at this
        omega
      · rcases he with ⟨s2, o2, hmt, hpl, -, he⟩ | ⟨s2, -, -, -, -, he⟩ | ⟨s2, -, -, -, -, he⟩
        · have hs2 : s'' = s2 := congrArg (fun x : State GalilVM => x.vm) he
          subst hs2
          have hl := searchLens_matchedPlace P q first hpl
          show searchStep (P.place s) true (searchLens.get s) (searchLens.get s'')
          rw [hl]
          exact compare_event_true_of_matched P q first hcmp hmt hidle
        · exfalso
          have := congrArg (fun x : State GalilVM => x.ctl.mode) he
          simp at this
          rw [hm] at this
          exact Mode.noConfusion this
        · exfalso
          have := congrArg (fun x : State GalilVM => x.ctl.mode) he
          simp at this
          rw [hm] at this
          exact Mode.noConfusion this
      · exact absurd hidle (hres _ _ hb)

#print axioms scanTrace_single_searchStep

/-- **NAMED — the search projection of a `.run` idle leg is a `RunTrace` with
the same booleans.** -/
theorem idleLeg_runTrace (hres : RestartOnBroken P) {as : List Bool} {p r : State GalilVM}
    (h : IdleLeg P q first (fun s => s.search.mode = Mode.run) as p r) :
    RunTrace as (searchLens.get p.vm) (searchLens.get r.vm) := by
  induction h with
  | nil p => exact .nil _
  | cons t a as p p' r hidle hM h1 hr ih =>
      exact .cons (P.place p.vm) a as _ _ _ hM
        (scanTrace_single_searchStep P q first hres h1 hidle) ih

/-- **NAMED — the search projection of a `.wait` idle leg is a `WaitTrace`
with the same booleans.** -/
theorem idleLeg_waitTrace (hres : RestartOnBroken P) {as : List Bool} {p r : State GalilVM}
    (h : IdleLeg P q first (fun s => s.search.mode = Mode.wait) as p r) :
    WaitTrace as (searchLens.get p.vm) (searchLens.get r.vm) := by
  induction h with
  | nil p => exact .nil _
  | cons t a as p p' r hidle hM h1 hr ih =>
      exact .cons (P.place p.vm) a as _ _ _ hM
        (scanTrace_single_searchStep P q first hres h1 hidle) ih

#print axioms idleLeg_runTrace
#print axioms idleLeg_waitTrace

/-! ## 3. Assembling the scan leg, and `LegsCoupled` -/

/-- Scan legs concatenate. -/
theorem scanTrace_append {σ : Type} {F : Frame σ} {delay : ℕ} {ts1 as1 ts2 as2 : List Bool}
    {p r u : State σ} (h1 : ScanTrace F delay ts1 as1 p r) (h2 : ScanTrace F delay ts2 as2 r u) :
    ScanTrace F delay (ts1 ++ ts2) (as1 ++ as2) p u := by
  induction h1 with
  | nil => simpa using h2
  | wait c s s' ts as qq ht hm hav hr ih => exact .wait c s s' _ _ u ht hm hav (ih h2)
  | count c s s' ts as qq ht hm hav hc hr ih => exact .count c s s' _ _ u ht hm hav hc (ih h2)
  | fire c s s'' o rp ts as qq ht hm hav hc hr ih =>
      exact .fire c s s'' o rp _ _ u ht hm hav hc (ih h2)

/-- An idle leg is a scan leg. -/
theorem idleLeg_scanTrace {M : GalilVM → Prop} {as : List Bool} {p r : State GalilVM}
    (h : IdleLeg P q first M as p r) :
    ∃ ts : List Bool, ScanTrace (galilFrameS P q first) 2048 ts as p r := by
  induction h with
  | nil p => exact ⟨[], .nil p⟩
  | cons t a as p p' r hidle hM h1 hr ih =>
      obtain ⟨ts, hts⟩ := ih
      exact ⟨[t] ++ ts, scanTrace_append h1 hts⟩

/-- A tick taken off clock `1` is never `scan_match`: its event is `false`. -/
theorem scanTrace_single_false_of_clock {σ : Type} {F : Frame σ} {t a : Bool}
    {p p' : State σ} (h : ScanTrace F 2048 [t] [a] p p') (hc : p.ctl.clock ≠ 1) : a = false := by
  cases h with
  | wait => rfl
  | count => rfl
  | fire c s s'' o rp ts as qq ht hm hav hc1 hr => exact absurd hc1 hc

#print axioms scanTrace_single_false_of_clock

/-- **NAMED — `LegsCoupled` on `galilFrameS`.**  Inputs: a scan leg over
`pre` from `p` to `p0`, an idle `.run` leg `rs`, the exit tick `a1`, an idle
`.wait` leg `ws`, and the `.wait → .double` exit tick `a2` taken off clock `1`
(`H_exitNotFire`). -/
theorem legsCoupled_galil {ts0 pre rs ws : List Bool} {t1 t2 a1 a2 : Bool}
    {p p0 p1 p2 p3 p4 : State GalilVM}
    (hpre : ScanTrace (galilFrameS P q first) 2048 ts0 pre p p0)
    (hrunL : IdleLeg P q first (fun s => s.search.mode = Mode.run) rs p0 p1)
    (hex1 : ScanTrace (galilFrameS P q first) 2048 [t1] [a1] p1 p2)
    (hwaitL : IdleLeg P q first (fun s => s.search.mode = Mode.wait) ws p2 p3)
    (hex2 : ScanTrace (galilFrameS P q first) 2048 [t2] [a2] p3 p4)
    (H_exitNotFire : p3.ctl.clock ≠ 1) :
    LegsCoupled (galilFrameS P q first) pre p rs ws a1 a2 := by
  have ha2 : a2 = false := scanTrace_single_false_of_clock hex2 H_exitNotFire
  subst ha2
  refine ⟨rfl, ?_⟩
  obtain ⟨tsr, hr⟩ := idleLeg_scanTrace P q first hrunL
  obtain ⟨tsw, hw⟩ := idleLeg_scanTrace P q first hwaitL
  refine ⟨ts0 ++ (tsr ++ [t1] ++ (tsw ++ [t2])), p4, ?_⟩
  have h := scanTrace_append hpre
    (scanTrace_append (scanTrace_append hr hex1) (scanTrace_append hw hex2))
  simpa using h

#print axioms legsCoupled_galil

/-! ## 4. The round trip on the concrete frame -/

/-- **NAMED — `postRunF_round_trip'` on `galilFrameS`, with the four
`SearchVM` legs derived from the machine run.**  The search VM at each
milestone is the lens projection of the machine state; the centre places are
`P.place`. -/
theorem postRunF_round_trip_galil {I : State GalilVM → Prop} {k mw : ℕ}
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
    (H_exitNotFire : p3.ctl.clock ≠ 1)
    (hne : p4.vm.search.mode ≠ Mode.wait)
    (hp : I p) (hclk : ClockInv 2048 p.ctl)
    (hblen : bs.length = mw)
    (hpaced : PacedL 2048 0 ((pre ++ (rs ++ a1 :: (ws ++ [false]))) ++ (bs ++ [a3]))) :
    ∃ t1 : SearchVM, DoubleTrace bs (searchLens.get p4.vm) t1 ∧ t1.search.mode = Mode.double ∧
      positive t1.search.work = false ∧ t1.search.span = ofNat (2 * mw) ∧
      t1.lower = ofNat k ∧
      ∀ (c' : GalilScaffoldPlace.Place) (t' : SearchVM), searchStep c' a3 t1 t' →
        PrepAt k (2 * mw) t' ∧ StageInvD k (2 * mw) t' ∧ t'.walker = c' ∧
          8 * max k 1 ≤ 2 * mw := by
  have hrun := idleLeg_runTrace P q first hres hrunL
  have hwait := idleLeg_waitTrace P q first hres hwaitL
  have hs1 := scanTrace_single_searchStep P q first hres hex1 hidle1
  have hs2 := scanTrace_single_searchStep P q first hres hex2 hidle3
  have hcoup := legsCoupled_galil P q first hpre hrunL hex1 hwaitL hex2 H_exitNotFire
  exact postRunF_round_trip' (v := searchLens.get p0.vm) (t0 := searchLens.get p1.vm)
    (w0 := searchLens.get p2.vm) (w1 := searchLens.get p3.vm) (u0 := searchLens.get p4.vm)
    hsup hm hsp hlow hcal hcan hrun ht0 hs1 hw0 hwait hw1 hs2 hne hcoup hp hclk hblen hpaced

#print axioms postRunF_round_trip_galil

/-!
## 5. What is left

Closed: `legsCoupled_galil` (§3) — `CloseoutPreload32.LegsCoupled` on
`galilFrameS`, from the machine run itself — and `postRunF_round_trip_galil`
(§4), which needs no `SearchVM` leg as input.

Inputs it takes: `RestartOnBroken P` (discharged for `sharedC`), the idle-chain
and search-mode annotations on the legs (`IdleLeg`, `hidle1`, `hidle3`, the
mode facts), and the **one named hypothesis** `H_exitNotFire : p3.ctl.clock ≠ 1`
— the `.wait → .double` exit tick is not a comparison tick.  Its discharge is a
debt/clock argument (the debt reaches zero on a `scan_match`, after which the
clock is `2048`) and is not done here.

**無条件 PAL ∈ PEG は未完.**
-/

end PalPeg.CloseoutPreload33
