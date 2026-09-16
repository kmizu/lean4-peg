import PalPeg.CloseoutPreload4

/-!
# The restart entry, from the restart state: the grow phase, the `prepare`
dispatch, and the true entry depth

`CloseoutPreload4` reduced the ledger closure to three NAMED entry contracts
(`EntryPrepShapeC`, `EntryDebtC`, `EntryDepthC`) quantified over `ReachN`-
reachability from the restart.  This file walks the restart state
`begin last radius` (mode `.grow`) forward and discharges the first two of them,
in the form the corrected depth allows.

* §1 The restart state, read off `Restarted`: mode `.grow`, `work = max k 1`
  (`begin_work`), `span = 0`, `debt = initialDebt radius` with value `-Rad` and
  canonical, `lower = last = ofNat k` (`canonical_eq_ofNat`).

* §2 `ReachL` (reachability labelled by the events consumed) and the **phase
  invariant** `Phase`: every state reachable before the first `.run` entry is
  either still growing — `work`, `span`, the debt and the step count in
  lockstep — or already in the preparation phase, carrying the freshly prepared
  `.lower` state and the `PrepTrace` to it.  `phase_step` proves it is preserved:
  a grow tick, the `prepare` dispatch when the work counter is spent (which lands
  exactly in the shape `CloseoutPreload2.preloadAtEntry_of_trace` consumes), and
  a preparation tick.

* §3 `ReachP` (pre-entry reachability) and `phase_reach`.

* §4 The payoff.  `entry_shape`: at the first `.run` entry the whole preparation
  witness of `EntryPrepShapeC`, **plus the exact depth** `bs.length =
  max k 1 + 1 + n`.  `entry_debt`: the entry debt *exactly*,
  `stageDebt Rad k - (consumed advances)`.  `pacedL_prefix_zero`: a clock-paced
  prefix of at most `2047` events holds no advance at all.

* §5 The closure.  `dpEntryG k D = D + dpEvents (stageWindow1 k)` replaces
  `dpEntry k = 8 + dpEvents (stageWindow1 k)`; `QG` is the labelled restart
  invariant (keeping the consumed events, so the *whole* list's pacing travels
  instead of a slack that decays with the depth); `runEntriesS_of_named` and
  `readyClosure_G` rebuild `GalilReplaySpan.ReadyClosure … RdPaced` from three
  named facts only.  `CloseoutPreload.rdPaced_restart` takes the budget as a
  parameter, so nothing downstream had to change.

## What is proved unconditionally here

The begin → `prepare` linkage itself: the grow phase, the dispatch, the tape
shape, the window length (given the centre), the debt at the entry, the depth
identity, and the closure of the invariant.

## What is still named

* `CentreLong` / `CentreLongRun` — the centre place the window is copied from
  holds the stage's window, `8 * max k 1 < (stream c).length`, at the step at
  which `prepare` is dispatched.  (`CloseoutPreload3.stageCalibration1_of_long`
  turns it into the calibration clause.)  For an arbitrary centre the clause is
  false, so this cannot be dropped.
* `NoReturn` — the stage cut: inside a restart window the search does not come
  back out of `.run` and prepare a second stage.  §3 only walks the *first*
  entry.
* `EntryDepthG u D` with `D ≤ 2047` — the hand-over happens within `D` events.
  §4 computes the depth exactly, so this is a bound on the preparation trace's
  length `n`; §6 (`depth_forces_stage_bound`) shows the price: at a real entry
  `max k 1 + 2 ≤ D ≤ 2047`.

## Two corrections to `CloseoutPreload4`

1. `EntryDepthC`'s `j + 1 ≤ 8` is false for `max k 1 ≥ 7`: the grow ticks alone
   are `max k 1` events (`entry_shape`, `depth_forces_stage_bound`).  Hence
   `dpEntryG` and `readyClosure_G` in place of `dpEntry` and
   `CloseoutPreload2.readyClosure_paced`.
2. `EntryDebtC`'s `stageDebt Rad k ≤ value debt` is *tight*: `entry_debt` shows
   the entry debt is `stageDebt Rad k` minus every advance consumed on the way
   in, so the clause holds exactly when the prefix holds no advance — which is
   what `D ≤ 2047` buys through `pacedL_prefix_zero`, and which fails once the
   preparation is long enough to span a full clock period.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload5

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController
open PalPeg.GalilScaffoldPrepareControl (State Tick prepare tape)
open PalPeg.GalilScaffoldCounter (Counter Canonical value ofNat)
open PalPeg.CloseoutReadyStage
open PalPeg.CloseoutRunEntriesS
open PalPeg.CloseoutPreload
open PalPeg.CloseoutPreload2 (PrepTrace dErase prepStep_tick)
open PalPeg.CloseoutDebtAudit (dpEvents stageWindow1 dpEntry)
open PalPeg.GalilScaffoldStagePrepare (growStep)

/-! ## 0. Counters: a canonical non-negative counter is a numeral -/

theorem unit_list_eq : ∀ l : List Unit, l = List.replicate l.length ()
  | [] => rfl
  | () :: l => by rw [List.length_cons, List.replicate_succ, ← unit_list_eq l]

theorem canonical_eq_ofNat {c : Counter} (hc : Canonical c) (h : 0 ≤ value c) :
    c = ofNat (value c).toNat := by
  rcases c with ⟨ps, ns⟩
  rcases hc with hc | hc
  · subst hc
    have hn : ns = [] := by
      simp only [value, List.length_nil] at h
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hn; rfl
  · subst hc
    have : (value (⟨ps, []⟩ : Counter)).toNat = ps.length := by
      simp [value]
    rw [this]
    show (⟨ps, []⟩ : Counter) = ⟨List.replicate ps.length (), []⟩
    rw [← unit_list_eq ps]

#print axioms canonical_eq_ofNat

/-- `begin`'s work counter at a numeral lower bound: `max k 1`. -/
theorem begin_work (k : ℕ) (radius : Counter) :
    (GalilScaffoldSearchFinish.begin (ofNat k) radius).work = ofNat (max k 1) := by
  show (if GalilScaffoldCounter.zero (ofNat k) then
      GalilScaffoldCounter.inc (ofNat k) else ofNat k) = ofNat (max k 1)
  cases k with
  | zero =>
    show (if GalilScaffoldCounter.zero (ofNat 0) then
      GalilScaffoldCounter.inc (ofNat 0) else ofNat 0) = ofNat (max 0 1)
    rfl
  | succ n =>
    have hz : GalilScaffoldCounter.zero (ofNat (n + 1)) = false := by
      simp [GalilScaffoldCounter.zero, ofNat, List.replicate_succ]
    rw [hz]
    simp only [Bool.false_eq_true, if_false]
    exact congrArg ofNat (by omega)

#print axioms begin_work

/-! ## 1. The restart state, read off `Restarted` -/

/-- The stage's lower bound as a numeral. -/
theorem restart_lower {raw : List (Fin 2)} {u : GalilVM} {Rad : ℕ} {last : Counter}
    (hR : Restarted raw u Rad last) : last = ofNat (value last).toNat :=
  canonical_eq_ofNat hR.2.2.2.2.2.2.2.2.1 hR.2.2.2.2.2.2.2.2.2

/-- **The restart state's search fields.**  `begin last u.radius` sits in `.grow`
with `work = max k 1`, `span = 0` and `debt = initialDebt u.radius`, whose value
is `-Rad` and which is canonical. -/
theorem restart_facts {raw : List (Fin 2)} {u : GalilVM} {Rad : ℕ} {last : Counter}
    (hR : Restarted raw u Rad last) :
    (searchLens.get u).search.mode = GalilScaffoldSearchFinish.Mode.grow ∧
      (searchLens.get u).search.work = ofNat (max (value last).toNat 1) ∧
      (searchLens.get u).search.span = ofNat 0 ∧
      Canonical (searchLens.get u).search.debt ∧
      value (searchLens.get u).search.debt = -(Rad : ℤ) ∧
      (searchLens.get u).lower = last := by
  have hs : u.search = GalilScaffoldSearchFinish.begin last u.radius := hR.2.2.2.2.2.2.1
  have hlow : u.lower = last := hR.2.2.2.2.2.2.2.1
  have hlast : last = ofNat (value last).toNat := restart_lower hR
  have hrad : Canonical u.radius ∧ value u.radius = Rad := hR.2.2.2.2.1
  have hget : (searchLens.get u).search = u.search := rfl
  refine ⟨by rw [hget, hs]; rfl, ?_, by rw [hget, hs]; rfl, ?_, ?_, hlow⟩
  · rw [hget, hs]
    conv_lhs => rw [hlast]
    exact begin_work _ _
  · rw [hget, hs]
    show Canonical (GalilScaffoldSearchFinish.initialDebt u.radius)
    rcases hrad.1 with h | h
    · exact Or.inr h
    · exact Or.inl h
  · rw [hget, hs]
    show value (GalilScaffoldSearchFinish.initialDebt u.radius) = -(Rad : ℤ)
    have := hrad.2
    simp only [GalilScaffoldSearchFinish.initialDebt, value] at this ⊢
    omega

#print axioms restart_facts

/-! ## 2. Labelled reachability and the phase invariant -/

/-- `searchStep`-reachability labelled by the events consumed, in order. -/
inductive ReachL : SearchVM → List Bool → SearchVM → Prop
  | nil (v : SearchVM) : ReachL v [] v
  | snoc (v w w' : SearchVM) (bs : List Bool) (a : Bool)
      (c : GalilScaffoldPlace.Place) (hr : ReachL v bs w) (hs : searchStep c a w w') :
      ReachL v (bs ++ [a]) w'

/-- Forgetting the labels gives `CloseoutPreload4.ReachN` at the label length. -/
theorem reachN_of_reachL : ∀ {v w : SearchVM} {bs : List Bool}, ReachL v bs w →
    PalPeg.CloseoutPreload4.ReachN bs.length v w := by
  intro v w bs h
  induction h with
  | nil => exact .refl _
  | snoc w w' bs a c hr hs ih =>
    rw [List.length_append, List.length_singleton]
    exact PalPeg.CloseoutPreload4.reachN_snoc ih ⟨c, a, hs⟩

#print axioms reachN_of_reachL

/-- The centre place the window is copied from must hold the stage's window.
This is the only property of the dispatching step's centre the shape needs. -/
def CentreLong (k : ℕ) (c : GalilScaffoldPlace.Place) : Prop :=
  8 * max k 1 < (GalilScaffoldPlace.stream c).length

/-- A preparation tick leaves the debt alone. -/
theorem tick_debt {x y : State} {b : Bool} (ht : Tick b x y) : y.debt = x.debt := by
  cases ht <;> rfl

#print axioms tick_debt

/-- The debt after a preparation `searchStep`. -/
theorem prepStep_debt {c : GalilScaffoldPlace.Place} {a : Bool} {v v' : SearchVM}
    (hm : v.search.mode = .lower ∨ v.search.mode = .lowerHome ∨
      v.search.mode = .copy ∨ v.search.mode = .home)
    (hs : searchStep c a v v') :
    v'.search.debt =
      (if a then GalilScaffoldCounter.dec v.search.debt else v.search.debt) := by
  unfold searchStep at hs
  have hstep : ∃ y, Tick true v.toPrep y ∧
      v' = SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a y)
        v.search.quarter v.lower := by
    rcases hm with hm | hm | hm | hm <;> rw [hm] at hs <;> exact hs
  obtain ⟨y, hy, hv'⟩ := hstep
  have hd : y.debt = v.search.debt := tick_debt hy
  rw [hv']
  cases a
  · show y.debt = v.search.debt
    exact hd
  · show GalilScaffoldCounter.dec y.debt = _
    rw [hd]
    simp

#print axioms prepStep_debt

/-- **The phase invariant.**  Every state reachable from the restart before the
first `.run` entry is either still growing the span (with the work counter, the
span, the debt and the step count in lockstep) or already in the preparation
phase, carrying the freshly prepared `.lower` state and the trace to it. -/
def Phase (u : GalilVM) (k : ℕ) (bs : List Bool) (v : SearchVM) : Prop :=
  (v.search.mode = GalilScaffoldSearchFinish.Mode.grow ∧ bs.length ≤ max k 1 ∧
      v.search.work = ofNat (max k 1 - bs.length) ∧
      v.search.span = ofNat (8 * bs.length) ∧ v.lower = u.lower ∧
      value v.search.debt =
        value u.search.debt + 2 * bs.length - (bs.count true : ℤ) ∧
      Canonical v.search.debt) ∨
  (∃ (s : State) (span n : ℕ) (v0 : SearchVM),
      s.mode = GalilScaffoldSearchFinish.Mode.lower ∧ s.work = u.lower ∧
      s.span = ofNat span ∧ span = 8 * max k 1 ∧
      s.program.config.tapes 10 =
        GalilScaffoldTape.moveRight (GalilScaffoldTape.write GalilScaffoldTape.reset 4) ∧
      s.program.config.tapes 7 = GalilScaffoldTape.reset ∧
      (∀ i : Fin 12, i ≠ 7 → i ≠ 10 →
        s.program.config.tapes i = GalilScaffoldTape.reset) ∧
      ((GalilScaffoldPlace.stream s.walker).take (span + 1)).length = stageWindow1 k ∧
      v0.toPrep = s ∧ PrepTrace v0 n v ∧ bs.length = max k 1 + 1 + n ∧
      v.search.mode ≠ GalilScaffoldSearchFinish.Mode.run ∧
      value v.search.debt =
        value u.search.debt + 2 * max k 1 - (bs.count true : ℤ) ∧
      Canonical v.search.debt)

/-! ### 2.1 Projections -/

theorem ofPrep_span (p : State) (q : Fin 4) (l : Counter) :
    (SearchVM.ofPrep p q l).search.span = p.span := rfl
theorem ofPrep_debt (p : State) (q : Fin 4) (l : Counter) :
    (SearchVM.ofPrep p q l).search.debt = p.debt := rfl
theorem ofPrep_walker (p : State) (q : Fin 4) (l : Counter) :
    (SearchVM.ofPrep p q l).walker = p.walker := rfl
theorem toPrep_span (v : SearchVM) : v.toPrep.span = v.search.span := rfl
theorem toPrep_debt (v : SearchVM) : v.toPrep.debt = v.search.debt := rfl
theorem toPrep_lowerWork (v : SearchVM) : v.toPrep.work = v.search.work := rfl

theorem afterAdvance_span (a : Bool) (p : State) :
    (GalilScaffoldPreparePaced.afterAdvance a p).span = p.span := by cases a <;> rfl
theorem afterAdvance_walker (a : Bool) (p : State) :
    (GalilScaffoldPreparePaced.afterAdvance a p).walker = p.walker := by cases a <;> rfl
theorem afterAdvance_program (a : Bool) (p : State) :
    (GalilScaffoldPreparePaced.afterAdvance a p).program = p.program := by cases a <;> rfl
theorem afterAdvance_debt (a : Bool) (p : State) :
    value (GalilScaffoldPreparePaced.afterAdvance a p).debt =
      value p.debt - (if a then 1 else 0) := by
  cases a
  · simp [GalilScaffoldPreparePaced.afterAdvance]
  · show value (GalilScaffoldCounter.dec p.debt) = _
    rw [GalilScaffoldCounter.dec_value]; simp
theorem afterAdvance_canonical (a : Bool) (p : State) (hc : Canonical p.debt) :
    Canonical (GalilScaffoldPreparePaced.afterAdvance a p).debt := by
  cases a
  · exact hc
  · exact GalilScaffoldCounter.dec_canonical _ hc

/-- A non-`.run` preparation mode is one of the four tick modes. -/
theorem prepMode_four {m : GalilScaffoldSearchFinish.Mode}
    (h : PalPeg.CloseoutPreload4.PrepMode m) (hne : m ≠ .run) :
    m = .lower ∨ m = .lowerHome ∨ m = .copy ∨ m = .home := by
  rcases h with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  · exact absurd h hne

/-- A preparation trace extends at its far end. -/
theorem prepTrace_snoc : ∀ {v w : SearchVM} {n : ℕ}, PrepTrace v n w →
    ∀ {w' : SearchVM}, (w.search.mode = GalilScaffoldSearchFinish.Mode.lower ∨
      w.search.mode = GalilScaffoldSearchFinish.Mode.lowerHome ∨
      w.search.mode = GalilScaffoldSearchFinish.Mode.copy ∨
      w.search.mode = GalilScaffoldSearchFinish.Mode.home) →
    (∃ (c : GalilScaffoldPlace.Place) (a : Bool), searchStep c a w w') →
    PrepTrace v (n + 1) w' := by
  intro v w n h
  induction h with
  | nil v => intro w' hm hs; exact .cons v w' w' 0 hm hs (.nil _)
  | cons v v1 w n hm0 hs0 hr ih =>
    intro w' hm hs
    exact .cons v v1 w' (n + 1) hm0 hs0 (ih hm hs)

#print axioms prepTrace_snoc

/-! ### 2.2 The phase invariant is preserved -/

/-- **One step of the phase invariant.**  The grow branch either grows the span
one notch or — when the work counter is spent — dispatches `prepare`, which lands
in the preparation branch with the shape the entry needs; the preparation branch
extends its trace. -/
theorem phase_step (u : GalilVM) (k : ℕ) (bs : List Bool) (v v' : SearchVM)
    (c : GalilScaffoldPlace.Place) (a : Bool)
    (hcl : v.search.mode = GalilScaffoldSearchFinish.Mode.grow →
      GalilScaffoldCounter.positive v.search.work = false → CentreLong k c)
    (hP : Phase u k bs v) (hs : searchStep c a v v')
    (hne : v'.search.mode ≠ GalilScaffoldSearchFinish.Mode.run) :
    Phase u k (bs ++ [a]) v' := by
  have hcount : ((bs ++ [a]).count true : ℤ) = (bs.count true : ℤ) + (if a then 1 else 0) := by
    cases a <;> simp
  have hlen : (bs ++ [a]).length = bs.length + 1 := by simp
  rcases hP with ⟨hm, hi, hw, hsp, hlow, hd, hc⟩ | hprep
  · -- grow branch
    unfold searchStep at hs
    rw [hm] at hs
    by_cases hp : GalilScaffoldCounter.positive v.search.work = true
    · -- one more grow tick
      simp only [hp, if_true] at hs
      have hpos : 0 < max k 1 - bs.length := by
        rw [hw] at hp
        by_contra hz
        have : max k 1 - bs.length = 0 := by omega
        rw [this] at hp
        simp [GalilScaffoldCounter.positive, ofNat] at hp
      refine Or.inl ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hs, ofPrep_mode, afterAdvance_mode]
        show (growStep v.toPrep).mode = _
        exact hm
      · rw [hlen]; omega
      · rw [hs, ofPrep_work, afterAdvance_work]
        show GalilScaffoldCounter.dec v.toPrep.work = _
        rw [toPrep_lowerWork, hw, hlen]
        have : max k 1 - bs.length = (max k 1 - (bs.length + 1)) + 1 := by omega
        rw [this, GalilScaffoldCounter.dec_ofNat_succ]
      · rw [hs, ofPrep_span, afterAdvance_span]
        show GalilScaffoldGrow.add 8 v.toPrep.span = _
        rw [toPrep_span, hsp, GalilScaffoldStagePrepare.add_ofNat, hlen]
        exact congrArg ofNat (by omega)
      · rw [hs, ofPrep_lower]; exact hlow
      · rw [hs, ofPrep_debt, afterAdvance_debt]
        show value (GalilScaffoldGrow.add 2 v.toPrep.debt) - _ = _
        rw [GalilScaffoldGrow.add_value, toPrep_debt, hd, hlen, hcount]
        push_cast
        ring
      · rw [hs, ofPrep_debt]
        refine afterAdvance_canonical _ _ ?_
        show Canonical (GalilScaffoldGrow.add 2 v.toPrep.debt)
        exact GalilScaffoldGrow.add_canonical _ _ hc
    · -- the work counter is spent: `prepare` dispatches
      simp only [hp, Bool.false_eq_true, if_false] at hs
      have hspent : bs.length = max k 1 := by
        rw [hw] at hp
        by_contra hz
        have hlt : 0 < max k 1 - bs.length := by omega
        have : max k 1 - bs.length = (max k 1 - bs.length - 1) + 1 := by omega
        rw [this] at hp
        simp [GalilScaffoldCounter.positive, ofNat, List.replicate_succ] at hp
      set s : State := GalilScaffoldPreparePaced.afterAdvance a (prepare v.toPrep v.lower c)
        with hsdef
      refine Or.inr ⟨s, 8 * max k 1, 0, v', ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hsdef, afterAdvance_mode]
        exact GalilSearchReadyInv.prepare_mode v.toPrep v.lower c
      · rw [hsdef, afterAdvance_work]
        show v.lower = u.lower
        exact hlow
      · rw [hsdef, afterAdvance_span]
        show v.toPrep.span = _
        rw [toPrep_span, hsp, hspent]
      · rw [hsdef, afterAdvance_program]
        simp [prepare, GalilScaffoldLoading.put]
      · rw [hsdef, afterAdvance_program]
        simp [prepare, GalilScaffoldLoading.put, GalilScaffoldControl.reset]
      · intro i hi7 hi10
        rw [hsdef, afterAdvance_program]
        simp [prepare, GalilScaffoldLoading.put, GalilScaffoldControl.reset, hi10]
      · have hwalk : s.walker = c := by
          rw [hsdef, afterAdvance_walker]; rfl
        rw [hwalk]
        exact PalPeg.CloseoutPreload3.stageCalibration1_of_long c k
          (hcl hm (by simpa using hp))
      · rw [hs]; exact toPrep_ofPrep _ _ _
      · exact .nil _
      · rw [hlen, hspent]
      · exact hne
      · rw [hs, ofPrep_debt, hsdef, afterAdvance_debt]
        show value (prepare v.toPrep v.lower c).debt - _ = _
        have hpd : (prepare v.toPrep v.lower c).debt = v.search.debt := rfl
        rw [hpd, hd, hspent, hcount]
        push_cast
        ring
      · rw [hs, ofPrep_debt, hsdef]
        refine afterAdvance_canonical _ _ ?_
        show Canonical (prepare v.toPrep v.lower c).debt
        exact hc
  · -- preparation branch
    obtain ⟨s, span, n, v0, hm, hwk, hsp, hspan, h10, h7, hother, hcal, hv0, htr, hn,
      hnr, hd, hc⟩ := hprep
    have h4 : v.search.mode = .lower ∨ v.search.mode = .lowerHome ∨
        v.search.mode = .copy ∨ v.search.mode = .home := by
      refine prepMode_four ?_ hnr
      refine PalPeg.CloseoutPreload4.prepTrace_mode htr ?_
      have : v0.search.mode = s.mode := by rw [← hv0]; rfl
      exact Or.inl (this.trans hm)
    refine Or.inr ⟨s, span, n + 1, v0, hm, hwk, hsp, hspan, h10, h7, hother, hcal, hv0,
      ?_, ?_, hne, ?_, ?_⟩
    · exact prepTrace_snoc htr h4 ⟨c, a, hs⟩
    · rw [hlen, hn]; omega
    · rw [prepStep_debt h4 hs, hcount]
      cases a <;> simp [GalilScaffoldCounter.dec_value, hd] <;> omega
    · rw [prepStep_debt h4 hs]
      cases a
      · exact hc
      · exact GalilScaffoldCounter.dec_canonical _ hc

#print axioms phase_step

/-! ## 3. Pre-entry reachability, and the shape at the first `.run` entry -/

/-- Reachability from the restart that has not yet handed over to the DP run:
every state on the path, the endpoint included, is outside `.run`. -/
inductive ReachP : SearchVM → List Bool → SearchVM → Prop
  | nil (v : SearchVM) (h : v.search.mode ≠ GalilScaffoldSearchFinish.Mode.run) :
      ReachP v [] v
  | snoc (v w w' : SearchVM) (bs : List Bool) (a : Bool)
      (c : GalilScaffoldPlace.Place) (hr : ReachP v bs w) (hs : searchStep c a w w')
      (hne : w'.search.mode ≠ GalilScaffoldSearchFinish.Mode.run) :
      ReachP v (bs ++ [a]) w'

theorem reachL_of_reachP : ∀ {v w : SearchVM} {bs : List Bool}, ReachP v bs w →
    ReachL v bs w := by
  intro v w bs h
  induction h with
  | nil h => exact .nil _
  | snoc w w' bs a c hr hs hne ih => exact .snoc _ _ _ _ _ c ih hs

/-- **NAMED — the dispatching centre holds the stage's window.**  The only fact
about the centre place the preparation shape needs, at exactly the step at which
`prepare` is dispatched. -/
def CentreLongRun (u : GalilVM) (k : ℕ) : Prop :=
  ∀ (bs : List Bool) (w w' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool),
    ReachP (searchLens.get u) bs w → searchStep c a w w' →
    w.search.mode = GalilScaffoldSearchFinish.Mode.grow →
    GalilScaffoldCounter.positive w.search.work = false → CentreLong k c

/-- **The phase invariant holds all along the pre-entry reachability.** -/
theorem phase_reach {raw : List (Fin 2)} {u : GalilVM} {Rad : ℕ} {last : Counter}
    (hR : Restarted raw u Rad last) (hcl : CentreLongRun u (value last).toNat) :
    ∀ {bs : List Bool} {v : SearchVM}, ReachP (searchLens.get u) bs v →
      Phase u (value last).toNat bs v := by
  obtain ⟨hm, hw, hsp, hc, hd, hlow⟩ := restart_facts hR
  intro bs v h
  induction h with
  | nil hne =>
    exact Or.inl ⟨hm, by simp, by simpa using hw, by simpa using hsp, rfl,
      by simp [show (searchLens.get u).search.debt = u.search.debt from rfl], hc⟩
  | snoc w w' bs a c hr hs hne ih =>
    exact phase_step u _ bs w w' c a
      (fun h1 h2 => hcl bs w w' c a hr hs h1 h2) ih hs hne

#print axioms phase_reach

/-! ## 4. The shape, the depth and the debt at the first `.run` entry -/

theorem reachP_ne_run : ∀ {v w : SearchVM} {bs : List Bool}, ReachP v bs w →
    w.search.mode ≠ GalilScaffoldSearchFinish.Mode.run := by
  intro v w bs h
  cases h with
  | nil h => exact h
  | snoc w w' bs a c hr hs hne => exact hne

/-- **The begin → `prepare` linkage, proved.**  At the first `.run` entry
reachable from the restart, the preparation witness `CloseoutPreload4`'s
`EntryPrepShapeC` asks for — together with the exact depth of the entry:
`max k 1` grow ticks, the `prepare` dispatch, and the `n` ticks of the
preparation trace. -/
theorem entry_shape {raw : List (Fin 2)} {u : GalilVM} {Rad : ℕ} {last : Counter}
    (hR : Restarted raw u Rad last) (hcl : CentreLongRun u (value last).toNat)
    {bs : List Bool} {v v' : SearchVM} {c : GalilScaffoldPlace.Place} {a : Bool}
    (hp : ReachP (searchLens.get u) bs v) (hs : searchStep c a v v')
    (hr : v'.search.mode = GalilScaffoldSearchFinish.Mode.run) :
    ∃ (s : State) (lower span n : ℕ) (v0 : SearchVM),
      s.mode = GalilScaffoldSearchFinish.Mode.lower ∧ s.work = ofNat lower ∧
      s.span = ofNat span ∧
      s.program.config.tapes 10 =
        GalilScaffoldTape.moveRight (GalilScaffoldTape.write GalilScaffoldTape.reset 4) ∧
      s.program.config.tapes 7 = GalilScaffoldTape.reset ∧
      (∀ i : Fin 12, i ≠ 7 → i ≠ 10 →
        s.program.config.tapes i = GalilScaffoldTape.reset) ∧
      ((GalilScaffoldPlace.stream s.walker).take (span + 1)).length =
        stageWindow1 (value last).toNat ∧
      v0.toPrep = s ∧ PrepTrace v0 n v ∧
      bs.length = max (value last).toNat 1 + 1 + n := by
  have hne := reachP_ne_run hp
  rcases phase_reach hR hcl hp with ⟨hmg, -, -, -, -, -, -⟩ | hprep
  · exact absurd ((run_entry_startRun hs hne hr).1 ▸ hmg) (by decide)
  · obtain ⟨s, span, n, v0, hm, hwk, hsp, hspan, h10, h7, hother, hcal, hv0, htr, hn,
      -, -, -⟩ := hprep
    refine ⟨s, (value last).toNat, span, n, v0, hm, ?_, hsp, h10, h7, hother, hcal,
      hv0, htr, hn⟩
    rw [hwk, hR.2.2.2.2.2.2.2.1]
    exact restart_lower hR

#print axioms entry_shape

/-- **The entry debt, exactly.**  The restart installs `-Rad`, the `max k 1` grow
ticks add `2` each, and every event that fires an advance costs one credit. -/
theorem entry_debt {raw : List (Fin 2)} {u : GalilVM} {Rad : ℕ} {last : Counter}
    (hR : Restarted raw u Rad last) (hcl : CentreLongRun u (value last).toNat)
    {bs : List Bool} {v v' : SearchVM} {c : GalilScaffoldPlace.Place} {a : Bool}
    (hp : ReachP (searchLens.get u) bs v) (hs : searchStep c a v v')
    (hr : v'.search.mode = GalilScaffoldSearchFinish.Mode.run) :
    Canonical v'.search.debt ∧
      value v'.search.debt =
        PalPeg.GalilReplaySpan.stageDebt Rad (((value last).toNat : ℕ) : ℤ)
          - (((bs ++ [a]).count true : ℕ) : ℤ) := by
  have hne := reachP_ne_run hp
  obtain ⟨-, -, -, -, hdu, -⟩ := restart_facts hR
  have hdebt := run_entry_debt hs hne hr
  rcases phase_reach hR hcl hp with ⟨hmg, -, -, -, -, -, -⟩ | hprep
  · exact absurd ((run_entry_startRun hs hne hr).1 ▸ hmg) (by decide)
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hd, hc⟩ := hprep
    have hcount : (((bs ++ [a]).count true : ℕ) : ℤ)
        = ((bs.count true : ℕ) : ℤ) + (if a then 1 else 0) := by
      cases a <;> simp
    have hdu' : value u.search.debt = -(Rad : ℤ) := hdu
    constructor
    · rw [hdebt]; cases a
      · exact hc
      · exact GalilScaffoldCounter.dec_canonical _ hc
    · rw [hdebt, hcount]
      have hmax : PalPeg.GalilReplaySpan.stageDebt Rad (((value last).toNat : ℕ) : ℤ)
          = 2 * ((max (value last).toNat 1 : ℕ) : ℤ) - (Rad : ℤ) := by
        unfold PalPeg.GalilReplaySpan.stageDebt
        push_cast
        omega
      rw [hmax]
      cases a
      · simp only [Bool.false_eq_true, if_false]
        rw [hd, hdu']; ring
      · simp only [if_true]
        rw [GalilScaffoldCounter.dec_value, hd, hdu']; ring

#print axioms entry_debt

/-! ### 4.1 Pacing on a prefix -/

theorem pacedL_prefix_count {d : ℕ} {bs as : List Bool} (h : PacedL d 0 (bs ++ as)) :
    d * (bs.count true) ≤ bs.length := by
  have h2 := h bs.length
  rw [List.take_left] at h2
  omega

/-- **A short paced prefix carries no comparison.**  With `d = 2048` a prefix of
at most `2047` events cannot hold a single advance. -/
theorem pacedL_prefix_zero {bs as : List Bool} (h : PacedL 2048 0 (bs ++ as))
    (hlen : bs.length ≤ 2047) : bs.count true = 0 := by
  have := pacedL_prefix_count h
  omega

theorem pacedL_suffix {d : ℕ} {bs as : List Bool} (h : PacedL d 0 (bs ++ as)) :
    PacedL d bs.length as := by
  intro n
  have h2 := h (bs.length + n)
  rw [List.take_length_add_append, List.count_append] at h2
  have : d * (bs.count true + (as.take n).count true)
      = d * (bs.count true) + d * ((as.take n).count true) := by ring
  omega

#print axioms pacedL_prefix_zero
#print axioms pacedL_suffix

/-! ## 5. The corrected entry budget and the ledger closure -/

/-- **NAMED — the restart window contains no return to `.run`.**  Every state
reachable from the restart outside `.run` is reachable without having passed
through `.run`: the stage cut. -/
def NoReturn (u : GalilVM) : Prop :=
  ∀ (bs : List Bool) (v : SearchVM), ReachL (searchLens.get u) bs v →
    v.search.mode ≠ GalilScaffoldSearchFinish.Mode.run → ReachP (searchLens.get u) bs v

/-- **NAMED — the entry depth.**  The hand-over happens within `D` events of the
restart.  `entry_shape` computes the depth exactly — `max k 1` grow ticks, the
`prepare` dispatch and the `n` preparation ticks — so this is a bound on the
preparation trace's own length; §6 records why `D ≤ 2047` is the sharp form. -/
def EntryDepthG (u : GalilVM) (D : ℕ) : Prop :=
  ∀ (bs : List Bool) (v v' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool),
    ReachL (searchLens.get u) bs v → searchStep c a v v' →
    v.search.mode ≠ GalilScaffoldSearchFinish.Mode.run →
    v'.search.mode = GalilScaffoldSearchFinish.Mode.run → bs.length + 1 ≤ D

/-- The entry budget at depth `D`: the preparation events plus the charged
prefix of the stage.  `CloseoutDebtAudit.dpEntry k` is this at `D = 8`, which
`CloseoutPreload4.EntryDepthC` assumed; the true depth is `max k 1 + 1 + n`. -/
def dpEntryG (k D : ℕ) : ℕ := D + dpEvents (stageWindow1 k)

/-- **The canonical restart invariant, labelled.**  The events consumed so far
are kept, so the pacing of the whole list — not a slack that decays with the
depth — is what travels. -/
def QG (u : GalilVM) (k D : ℕ) (v : SearchVM) (as : List Bool) : Prop :=
  ∃ bs : List Bool, ReachL (searchLens.get u) bs v ∧
    dpEntryG k D ≤ bs.length + as.length ∧ PacedL 2048 0 (bs ++ as)

theorem append_cons_eq (bs : List Bool) (a : Bool) (as : List Bool) :
    bs ++ (a :: as) = (bs ++ [a]) ++ as := by simp

theorem qG_next (u : GalilVM) (k D : ℕ) (v v' : SearchVM)
    (c : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool)
    (hq : QG u k D v (a :: as)) (hs : searchStep c a v v') : QG u k D v' as := by
  obtain ⟨bs, hreach, hlen, hpaced⟩ := hq
  refine ⟨bs ++ [a], .snoc _ _ _ _ _ c hreach hs, ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton]
    simp only [List.length_cons] at hlen
    omega
  · rw [← append_cons_eq]; exact hpaced

#print axioms qG_next

/-- **The residual `RunEntriesS` datum, from the three named contracts.**  The
preload shape is `entry_shape`, the entry debt is `entry_debt` together with the
pacing of the prefix (a prefix of at most `2047` events holds no advance, so the
stage debt is exactly the ledger's `stageDebt Rad k`), the event count and the
pacing of the tail come from `QG`. -/
theorem runEntriesS_of_named {raw : List (Fin 2)} {u : GalilVM} {Rad D : ℕ}
    {last : Counter} (hR : Restarted raw u Rad last) (hSE : StageEntry Rad last)
    (hcl : CentreLongRun u (value last).toNat) (hnr : NoReturn u)
    (hdep : EntryDepthG u D) (hD : D ≤ 2047) :
    ∀ (as : List Bool), dpEntryG (value last).toNat D ≤ as.length → PacedL 2048 0 as →
      RunEntriesS as (searchLens.get u) := by
  have hval : value last = ((value last).toNat : ℤ) :=
    (Int.toNat_of_nonneg hR.2.2.2.2.2.2.2.2.2).symm
  have hstage : 3 * Rad ≤ 5 * (value last).toNat := hSE _ hval
  -- the prefix of an entry holds no advance
  have hzero : ∀ (bs as : List Bool) (v v' : SearchVM) (c : GalilScaffoldPlace.Place)
      (a : Bool), ReachL (searchLens.get u) bs v → searchStep c a v v' →
      v.search.mode ≠ GalilScaffoldSearchFinish.Mode.run →
      v'.search.mode = GalilScaffoldSearchFinish.Mode.run →
      PacedL 2048 0 (bs ++ (a :: as)) → (bs ++ [a]).count true = 0 := by
    intro bs as v v' c a hreach hs hne hr hpaced
    have hlen : (bs ++ [a]).length ≤ 2047 := by
      have := hdep bs v v' c a hreach hs hne hr
      simp only [List.length_append, List.length_singleton]
      omega
    exact pacedL_prefix_zero (as := as) (by rw [← append_cons_eq]; exact hpaced) hlen
  intro as0 hlen0 hpaced0
  refine PalPeg.CloseoutPreload4.runEntriesS_of_traceE
    (Q := QG u (value last).toNat D)
    (Rad := Rad) (k := (value last).toNat) (slack := 2047)
    hstage (le_refl _) ?_ ?_ ?_ ?_ ?_ ?_ as0 (searchLens.get u) ?_
  · -- `TracePreloadE`
    intro v v' c a as hq hs hne hr
    obtain ⟨bs, hreach, -, -⟩ := hq
    obtain ⟨s, lower, span, n, v0, h⟩ :=
      entry_shape hR hcl (hnr bs v hreach hne) hs hr
    exact ⟨s, lower, span, n, v0, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
      h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1⟩
  · exact fun v v' c a as hq hs => qG_next u _ D v v' c a as hq hs
  · intro v v' c a as hq hs hne hr
    obtain ⟨bs, hreach, -, -⟩ := hq
    exact (entry_debt hR hcl (hnr bs v hreach hne) hs hr).1
  · intro v v' c a as hq hs hne hr
    obtain ⟨bs, hreach, -, hpaced⟩ := hq
    obtain ⟨-, hdv⟩ := entry_debt hR hcl (hnr bs v hreach hne) hs hr
    rw [hdv, hzero bs as v v' c a hreach hs hne hr hpaced]
    simp
  · intro v v' c a as hq hs hne hr
    obtain ⟨bs, hreach, hlen, -⟩ := hq
    have hd := hdep bs v v' c a hreach hs hne hr
    simp only [List.length_cons] at hlen
    unfold dpEntryG at hlen
    omega
  · intro v v' c a as hq hs hne hr
    obtain ⟨bs, hreach, -, hpaced⟩ := hq
    have hd := hdep bs v v' c a hreach hs hne hr
    refine pacedL_mono (k := (bs ++ [a]).length) ?_
      (pacedL_suffix (bs := bs ++ [a]) (by rw [← append_cons_eq]; exact hpaced))
    simp only [List.length_append, List.length_singleton]
    omega
  · exact ⟨[], .nil _, by simpa using hlen0, by simpa using hpaced0⟩

#print axioms runEntriesS_of_named

/-- **The restart datum, at the corrected depth.**  Three named facts per
restart: the dispatching centre holds the window, the restart window contains no
return to `.run`, and the hand-over happens within `D ≤ 2047` events. -/
def RestartG (raw : List (Fin 2)) : Prop :=
  ∀ (u : GalilVM) (Rad : ℕ) (last : Counter),
    Restarted raw u Rad last → StageEntry Rad last →
    ∃ D : ℕ, D ≤ 2047 ∧ CentreLongRun u (value last).toNat ∧ NoReturn u ∧
      EntryDepthG u D

/-- **`GalilReplaySpan.ReadyClosure` for `RdPaced`, at the corrected depth.**
`CloseoutPreload2.readyClosure_paced` pins the ledger's restart budget at
`dpEntry k = 8 + dpEvents (stageWindow1 k)`, which presumes an entry at depth
`8`; `CloseoutPreload.rdPaced_restart` takes the budget as a parameter, so the
true budget `dpEntryG k D` is installed here instead. -/
theorem readyClosure_G (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    (h : RestartG raw) :
    PalPeg.GalilReplaySpan.ReadyClosure raw P q first 2048 RdPaced where
  ready := fun c s hs => rdPaced_ready c s hs
  seg := fun es c c' s t hseg hidle hs => rdPaced_seg P q first es c c' s t hseg hidle hs
  restart := fun c u Rad last _ hclk hR hSE => by
    obtain ⟨D, hD, hcl, hnr, hdep⟩ := h u Rad last hR hSE
    exact rdPaced_restart c u Rad last (dpEntryG (value last).toNat D) hclk hR
      (fun m as hlen hp => runEntriesS_of_named hR hSE hcl hnr hdep hD as (by omega) hp)

#print axioms readyClosure_G

/-- The final replay theorem with the concrete ledger, at the corrected datum. -/
def replay_final_of_decodes_G (raw : List (Fin 2)) (P : Shared)
    (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM)
    (q : ℕ) (first : Fin 9)
    (hex : ∀ s, P.replayExhausted s = GalilScaffoldCounter.zero s.replay)
    (hsearch : ∀ s : GalilVM, PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect P a s v)
    (hG : RestartG raw)
    (hdec : Decodes P)
    (hbudget : PalPeg.GalilReplaySpan.ReplayBudgetRD raw P q first 2048)
    (hrs : PalPeg.GalilReplaySpan.RestartShapeL P)
    (r : ℕ) (hr0 : 0 < r) (c : Control) (t : GalilVM)
    (hm : c.mode = Mode.scan) (hc : c.clock = 2048) (hrpl : c.replaying = true)
    (hR : Restarted raw t 0 GalilScaffoldCounter.reset) (hrep : t.replay = ofNat r)
    (hM : MInv raw c t) (hfr : Frontier t) (hsi : ShiftIdle t) :=
  PalPeg.GalilReplaySpan.replay_after_fallback_general''_R_of_decodes
    raw P hP hP' q first hex hsearch (readyClosure_G raw P q first hG) hdec hbudget hrs
    r hr0 c t hm hc hrpl hR hrep hM hfr hsi

#print axioms replay_final_of_decodes_G

/-! ## 6. What the depth bound costs -/

/-- **The depth is `max k 1 + 2 + n`, so `D ≤ 2047` bounds the stage.**  At an
entry that really happens, `EntryDepthG u D` forces the grow phase — hence the
stage's lower bound `k` — to fit inside `D`.  In particular
`CloseoutPreload4.EntryDepthC`'s `j + 1 ≤ 8` is false as soon as `max k 1 ≥ 7`:
the grow ticks alone are `max k 1` events.  The closure above therefore installs
the budget `dpEntryG k D` rather than `dpEntry k`. -/
theorem depth_forces_stage_bound {raw : List (Fin 2)} {u : GalilVM} {Rad D : ℕ}
    {last : Counter} (hR : Restarted raw u Rad last)
    (hcl : CentreLongRun u (value last).toNat) (hdep : EntryDepthG u D) (hD : D ≤ 2047)
    {bs : List Bool} {v v' : SearchVM} {c : GalilScaffoldPlace.Place} {a : Bool}
    (hp : ReachP (searchLens.get u) bs v) (hs : searchStep c a v v')
    (hr : v'.search.mode = GalilScaffoldSearchFinish.Mode.run) :
    max (value last).toNat 1 + 2 ≤ D ∧ (value last).toNat ≤ 2045 := by
  obtain ⟨s, lower, span, n, v0, hm, hwk, hsp, h10, h7, hother, hcal, hv0, htr, hn⟩ :=
    entry_shape hR hcl hp hs hr
  have hle := hdep bs v v' c a (reachL_of_reachP hp) hs (reachP_ne_run hp) hr
  constructor <;> omega

#print axioms depth_forces_stage_bound

end PalPeg.CloseoutPreload5

