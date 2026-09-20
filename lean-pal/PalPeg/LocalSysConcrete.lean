import PalPeg.LocalTrackingLatch
import PalPeg.LocalLedgerShift
import PalPeg.LocalTick1
import PalPeg.LocalTick2
import PalPeg.LocalTick3
import PalPeg.LocalChain
import PalPeg.LocalArrival
import PalPeg.LocalReplayParked

/-!
# `LocalTrackingLatch.LocalSys` on the concrete `GalilVML` local state

The core is `LocalReplayParked.Mirrored1 P` (a `LocalState.GalilVML P` plus the
one mirror the parked `replayStart` swap needs), abstracted by
`LocalReplayParked.absState''`.

* `feedC a` = append `a` to the shared `pending` list and to the chain verifier
  (`feedV`, which *is* the abstract `GalilArriveChain.arriveState'`), then
  distribute it to the five cursors and the mirror with `LocalArrival.feed'`
  (abstractly invisible).  **`feed_abs` is proved** (`feed_abs_core`).
* `tickL` = `tickC M`: stutter when `Starved`, else the local step of the
  current control mode (`stepOf`).  **`stutter_of_starved` is proved** by
  construction (`tickC_starved`).
* `repL`/`outL` read the **finite control only** (`repC x.ctl`, `x.ctl.output`),
  as `LocalLatchRealize.encL_step` requires.  **`outL_abs` is `rfl`**.
* `Inv w x` (`InvC`) = the physical pack (`LocalTick1.Inv`, `ParkedOK`,
  `pending = []`) + `MirInv1` + **the tracking datum** `Tracked`: the
  abstraction of `x` is the pre-loaded trace state `stOf k` truncated to the
  letters that have not arrived (`Needy`, the shape
  `LocalLedgerShift.H_ledger_of_local_oracles.habs` needs).  The abstract
  successor is therefore taken from the *run*, never guessed from the state —
  at a positive-lag mispredicted watch the abstract `Tick` has no successor at
  all.
* **`tick_of_not_starved` is derived**, not assumed: `¬Starved` plus `H_ready`
  gives `needT' raw stOf k ≤ j`, which `used_le_of_need` turns into the three
  side conditions of `GalilLookRefined.tick_trunc'`, so the trace's own tick
  `stOf k → stOf (k+1)` survives truncation (`tick_of_need`); the mode
  obligation only has to say where the local step lands.
* **Tracking across an arrival is a theorem for the letter the run delivers**
  (`tracked_feedC`, via `GalilThrottledRun.arrive_trunc`); it is false for a wrong letter, and
  the run never feeds one.
* **`x0_ctl`, `x0_started`, `x0_ans` are `rfl`** for `x0C`; `x0_inv` splits into
  `x0C_physWF` (proved from `LocalTick1.Inv` of the blank core) and
  `x0C_mirInv1`.

**Left open**: one `Realizes` obligation per mode, below the last tick of the trace.  The
consumer is `LocalShadowConcrete.pal_in_peg_of_shadowed_sysC`.  `realizes_of_parts` splits a
`Realizes` into its abstract and physical halves; the **physical half of the
seven phase modes is closed** by `physWF_of_tickL3` (from
`LocalTick3.tickL3_inv` / `tickL3_replaying` / `pending_tickL3`) and the
physical half of a non-replaying scan tick by `physWF_of_tickL1`.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace PalPeg.LocalSysConcrete

open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldInputHead (PlaceHead)
open PalPeg.LocalState
open PalPeg.LocalInputView (InputView)
open PalPeg.LocalArrival (absHead' abs' absState' Ahead feedL')
open PalPeg.LocalReplayParked (abs'' absState'' absR physHead rval ParkedOK Mirrored1 MirInv1)
open PalPeg.LocalTick1 (Inv)
open PalPeg.LocalTrackingLatch (LocalSys)
open PalPeg.GalilArriveChain (arriveVM' arriveState' arriveChain)
open PalPeg.GalilTickArrive (arrivePH)

variable {P : ℕ}

/-! ## 1. Arrival on the concrete local state -/

/-- The arrival of a letter on the core: it joins the shared `pending` list and
the chain's own verifier. -/
def feedV (a : Fin 2) (x : GalilVML P) : GalilVML P :=
  { x with pending := x.pending ++ [a], chain := arriveChain a x.chain }

theorem absHead'_append (v : InputView) (q : List (Fin 2)) (a : Fin 2) :
    absHead' v (q ++ [a]) = arrivePH a (absHead' v q) := by
  show (⟨⟨v.focus, v.back, v.near, RTQueue.toList v.far ++ (q ++ [a])⟩, v.gap⟩ : PlaceHead) = _
  show _ = (⟨⟨v.focus, v.back, v.near, (RTQueue.toList v.far ++ q) ++ [a]⟩, v.gap⟩ : PlaceHead)
  rw [List.append_assoc]

theorem physHead_feedV (a : Fin 2) (x : GalilVML P) :
    physHead (feedV a x) = arrivePH a (physHead x) := absHead'_append _ _ _

theorem left_iterate_arrive (a : Fin 2) :
    ∀ (n : ℕ) (p : PlaceHead),
      GalilScaffoldInputHead.left^[n] (arrivePH a p) = arrivePH a (GalilScaffoldInputHead.left^[n] p)
  | 0, _ => rfl
  | n + 1, p => by
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        PalPeg.GalilTickArrive.left_arrive a p, left_iterate_arrive a n]

theorem absR_feedV (a : Fin 2) (x : GalilVML P) : absR (feedV a x) = arrivePH a (absR x) := by
  have hr : (feedV a x).ctl.replaying = x.ctl.replaying := rfl
  have hv : rval (feedV a x) = rval x := rfl
  unfold absR
  rw [hr, hv, physHead_feedV]
  cases x.ctl.replaying
  · rfl
  · exact left_iterate_arrive a (rval x) (physHead x)

theorem abs''_feedV (a : Fin 2) (x : GalilVML P) : abs'' (feedV a x) = arriveVM' a (abs'' x) := by
  have hl : absHead' (feedV a x).left (feedV a x).pending
      = arrivePH a (absHead' x.left x.pending) := absHead'_append _ _ _
  have hc : absHead' (feedV a x).center (feedV a x).pending
      = arrivePH a (absHead' x.center x.pending) := absHead'_append _ _ _
  have hr := absR_feedV a x
  show ({ abs' (feedV a x) with right := absR (feedV a x) } : GalilVM) = _
  rw [hr]
  show ({ abs' (feedV a x) with right := arrivePH a (absR x) } : GalilVM) = _
  simp only [feedV, abs', PalPeg.LocalState.abs, arriveVM', PalPeg.LocalTracking.arriveVM, abs'',
    absHead', arrivePH, List.append_assoc]
  rfl

open PalPeg.GalilThrottledRun (truncS usedVM needS SufVM arrive_trunc)
open PalPeg.GalilLookRefined (needL' needT' look' tick_trunc' needL'_le_needT' needS_le_needL')
open PalPeg.GalilScaffoldChainVerifier (canRight)
open PalPeg.LocalTrackingLatch (LX)


/-! ## 2. The concrete local state -/

/-- The physical well-formedness the whole local layer carries. -/
structure PhysWF (x : GalilVML P) : Prop where
  inv : PalPeg.LocalTick1.Inv x
  parked : ParkedOK x
  pend : x.pending = []

/-- The arrival step of the concrete `LocalSys`: the letter joins the shared
`pending` list and the chain verifier (`feedV`, the abstract arrival), and is
immediately distributed to the five cursors and the left mirror (abstractly
invisible, `LocalArrival.absState'_feed'`). -/
def feedC (a : Fin 2) (m : Mirrored1 P) : Mirrored1 P :=
  ⟨PalPeg.LocalArrival.feed' (feedV a m.vm), PalPeg.LocalInputView.arrive a m.mirL⟩

/-- The guard of the moving tick of a shift (`Tick.shift_one`), which does not depend on the
shared part of the frame. -/
def ShiftMoves (s : GalilVM) : Prop :=
  (Frame.pull shiftLens (shiftFrame (fun _ => True) (fun _ => True))).remainingPos s ∨
    (Frame.pull fppLens (fallbackFrame (fun _ => True) (fun _ => True))).remainingPos s

theorem shiftMoves_eq (Pw : Shared) (q : ℕ) (first : Fin 9) (s : GalilVM) :
    ShiftMoves s = (galilFrameS Pw q first).remainingPos s := rfl

/-- **The local starvation test.**  The next abstract tick would have to move a cursor onto a
cell that has not arrived.  Which cursors a tick moves depends on the mode, and the test reads
exactly those: an `init` or `scan` tick moves the right head one place; the moving tick of a
shift moves the centre head one place and the left head two; every other tick moves no head to
the right.  A test that read all four places in every mode would starve a scan state whose left
head stands on the last arrived letter, although its tick needs no further letter. -/
def Starved (x : GalilVML P) : Prop :=
  ¬ ((x.ctl.mode = .init ∨ x.ctl.mode = .scan → canRight (abs'' x).right) ∧
      (x.ctl.mode = .shift → ShiftMoves (abs'' x) →
        canRight (abs'' x).center ∧ canRight (abs'' x).left ∧
          canRight (PalPeg.GalilScaffoldChainVerifier.right (abs'' x).left)))

/-- **The tracking datum.**  The abstraction of the local state is the pre-loaded
trace state `stOf k`, truncated to the `raw.length - j` letters that have not
arrived yet. -/
def Needy (raw : List (Fin 2)) (stOf : ℕ → State GalilVM) (k j : ℕ) (x : GalilVML P) : Prop :=
  j ≤ raw.length ∧ absState'' x = truncS (raw.length - j) (stOf k)

/-- `x` sits on the pre-loaded trace. -/
def Tracked (raw : List (Fin 2)) (stOf : ℕ → State GalilVM) (x : GalilVML P) : Prop :=
  ∃ k j, Needy raw stOf k j x

/-- **The invariant of the concrete local system.**  The physical pack, the left
mirror's twin invariant, and the tracking datum. -/
structure InvC (Good : Mirrored1 P → Prop) (raw : List (Fin 2)) (stOf : ℕ → State GalilVM)
    (m : Mirrored1 P) : Prop where
  phys : PhysWF m.vm
  mir : MirInv1 m
  track : Tracked raw stOf m.vm
  /-- The invariants of the local layer that are neither physical nor read off the trace (the
  polarity bundle, the counter magnitudes, the parking of the cursors).  They are carried along
  the run, not assumed of every tracked state. -/
  good : Good m

/-! ## 3. The arrival oracles -/

theorem pending_feedV {x : GalilVML P} (hp : x.pending = []) (a : Fin 2) :
    (feedV a x).pending = a :: [] := by
  show x.pending ++ [a] = _
  rw [hp]
  rfl

theorem viewsWF_feedV (a : Fin 2) (x : GalilVML P) (h : ViewsWF x) : ViewsWF (feedV a x) := h

theorem parkedOK_feedV {x : GalilVML P} (a : Fin 2) (h : ParkedOK x) : ParkedOK (feedV a x) := by
  intro hr
  have hph : physHead (feedV a x) = arrivePH a (physHead x) := physHead_feedV a x
  have hpos : PalPeg.GalilScaffoldChainInputSupply.position (physHead (feedV a x))
      = PalPeg.GalilScaffoldChainInputSupply.position (physHead x) := by rw [hph]; rfl
  have hv : rval (feedV a x) = rval x := rfl
  rw [hpos, hv]
  exact h hr

/-- **Oracle `feed_abs`.**  Arrival on the core is the abstract `arriveState'`. -/
theorem feed_abs_core {m : Mirrored1 P} (hw : ViewsWF m.vm) (hp : m.vm.pending = []) (a : Fin 2) :
    absState'' (feedC a m).vm = arriveState' a (absState'' m.vm) := by
  have hpv := pending_feedV hp a
  have h1 : PalPeg.LocalArrival.feed' (feedV a m.vm) = feedL' a [] (feedV a m.vm) :=
    PalPeg.LocalArrival.feed'_cons hpv
  have h2 : abs'' (feedL' a [] (feedV a m.vm)) = abs'' (feedV a m.vm) :=
    PalPeg.LocalReplayParked.abs''_feedL' (viewsWF_feedV a m.vm hw) a [] hpv
  show (⟨(feedC a m).vm.ctl, abs'' (feedC a m).vm⟩ : State GalilVM) = _
  have h3 : (feedC a m).vm = feedL' a [] (feedV a m.vm) := h1
  rw [h3, h2, abs''_feedV]
  rfl

/-- **Oracle `inv_feed`, physical half.** -/
theorem physWF_feedC {m : Mirrored1 P} (h : PhysWF m.vm) (a : Fin 2) :
    PhysWF (feedC a m).vm := by
  have hw := h.inv.views
  have hpv := pending_feedV h.pend a
  have h1 : (feedC a m).vm = feedL' a [] (feedV a m.vm) :=
    PalPeg.LocalArrival.feed'_cons hpv
  refine ⟨?_, ?_, ?_⟩
  · rw [h1]
    exact ⟨h.inv.roles, h.inv.attached,
      ⟨PalPeg.LocalInputView.WF_arrive hw.1 a, PalPeg.LocalInputView.WF_arrive hw.2.1 a,
        PalPeg.LocalInputView.WF_arrive hw.2.2.1 a,
        PalPeg.LocalInputView.WF_arrive hw.2.2.2.1 a,
        PalPeg.LocalInputView.WF_arrive hw.2.2.2.2 a⟩,
      h.inv.radiusShaped, h.inv.lowerShaped, h.inv.lengthShaped, h.inv.shaped⟩
  · rw [h1]
    exact PalPeg.LocalReplayParked.parkedOK_feedL' (viewsWF_feedV a m.vm hw) a []
      hpv (parkedOK_feedV a h.parked)
  · rw [h1]; rfl

/-- **Oracle `inv_feed`, mirror half.** -/
theorem mirInv1_feedC {m : Mirrored1 P} (h : MirInv1 m) (hp : m.vm.pending = [])
    (hc : PalPeg.LocalInputView.WF m.vm.center) (a : Fin 2) : MirInv1 (feedC a m) := by
  have h1 : (feedC a m).vm = feedL' a [] (feedV a m.vm) :=
    PalPeg.LocalArrival.feed'_cons (pending_feedV hp a)
  refine ⟨?_, PalPeg.LocalInputView.WF_arrive h.2 a⟩
  show PalPeg.LocalReplaySwap.Twin (PalPeg.LocalInputView.arrive a m.mirL) (feedC a m).vm.center
  rw [h1]
  exact h.1.applyAct h.2 hc (PalPeg.LocalReplaySwap.ViewAct.arrive a)

/-! ## 4. One local tick, dispatching on the control mode -/

/-- The per-mode local steps.  Each field is meant to be the local realization
of one family of `GalilScaffoldTop.Tick` cases: `scan` composes
`LocalTick1.bgState` / `LocalTick1.matchVm` (and, while replaying,
`LocalReplayParked.matchVmR`) with the `LocalTick2` restart-family commits;
`shift`…`rewind` are the `LocalTick3` phase steps; `replayStart` is
`LocalReplayParked.commitReplayParked`. -/
structure Steps (P : ℕ) where
  init : Mirrored1 P → Mirrored1 P
  scan : Mirrored1 P → Mirrored1 P
  shift : Mirrored1 P → Mirrored1 P
  copy : Mirrored1 P → Mirrored1 P
  home : Mirrored1 P → Mirrored1 P
  fpp : Mirrored1 P → Mirrored1 P
  markEnd : Mirrored1 P → Mirrored1 P
  choose : Mirrored1 P → Mirrored1 P
  rewind : Mirrored1 P → Mirrored1 P
  replayStart : Mirrored1 P → Mirrored1 P

/-- The mode dispatch. -/
def stepOf (M : Steps P) : Mode → (Mirrored1 P → Mirrored1 P)
  | .init => M.init
  | .scan => M.scan
  | .shift => M.shift
  | .copy => M.copy
  | .home => M.home
  | .fpp => M.fpp
  | .markEnd => M.markEnd
  | .choose => M.choose
  | .rewind => M.rewind
  | .replayStart => M.replayStart

open Classical in
/-- **One local tick.**  Stutter exactly when starved; otherwise take the local
step of the current mode. -/
noncomputable def tickC (M : Steps P) (m : Mirrored1 P) : Mirrored1 P :=
  if Starved m.vm then m else stepOf M m.vm.ctl.mode m

open Classical in
theorem tickC_starved (M : Steps P) {m : Mirrored1 P} (h : Starved m.vm) : tickC M m = m := by
  unfold tickC; rw [if_pos h]

open Classical in
theorem tickC_step (M : Steps P) {m : Mirrored1 P} (h : ¬ Starved m.vm) :
    tickC M m = stepOf M m.vm.ctl.mode m := by
  unfold tickC; rw [if_neg h]

/-! ## 5. The per-mode obligation -/

/-- **What a truncated tick needs of the arrivals**: the three side conditions of
`GalilLookRefined.tick_trunc'` — the letters used by the source and by the target, and the
lookahead of the source.  It is weaker than `needT' raw stOf k ≤ j`, which also bounds the
lookahead of the target: a tick can be legitimate although the lookahead of its target has not
arrived (the right head stands on the last arrived letter and steps into the gap after it). -/
def TickNeed (raw : List (Fin 2)) (stOf : ℕ → State GalilVM) (k j : ℕ) : Prop :=
  usedVM raw (stOf k).vm ≤ j ∧ usedVM raw (stOf (k+1)).vm ≤ j ∧ look' raw (stOf k) ≤ j

/-- **The `LocalStep`-style obligation of one mode.**  On an invariant,
non-starved state standing at trace index `k` with `j` letters arrived and the
need of tick `k` met, the mode's local step lands on the trace's next state and
keeps the physical invariants.  Only ticks below `lastTick` are concerned: a pre-loaded trace
is a trace of ticks up to its last report point only. -/
def Realizes (Good : Mirrored1 P → Prop) (raw : List (Fin 2)) (stOf : ℕ → State GalilVM)
    (lastTick : ℕ)
    (f : Mirrored1 P → Mirrored1 P) (md : Mode) : Prop :=
  ∀ (m : Mirrored1 P) (k j : ℕ), InvC Good raw stOf m → m.vm.ctl.mode = md → ¬ Starved m.vm →
    Needy raw stOf k j m.vm → TickNeed raw stOf k j → k < lastTick →
      Needy raw stOf (k+1) j (f m).vm ∧ PhysWF (f m).vm ∧ MirInv1 (f m)

/-! ## 6. The `LocalSys` instance -/

/-- The abstraction of the concrete local state. -/
def absSC (m : Mirrored1 P) : State GalilVM := absState'' m.vm

/-- **The concrete `LocalSys` with a report test on the local state.**  The control of the
abstract layer has no information on the heads, so a report test that recognizes the report
points has to read the state; in the shadowed bridge the physical machine keeps the bit in its
own control (`LocalShadowRealize`). -/
noncomputable def sysM (M : Steps P) (repM : Mirrored1 P → Bool) : LocalSys (Mirrored1 P) where
  tickL := tickC M
  feedC := feedC
  repL := repM
  outL := fun m => m.vm.ctl.output
  Starved := fun m => Starved m.vm

/-- **The concrete `LocalSys`.**  `repL` and `outL` read the finite control only
(as `LocalLatchRealize.encL_step` requires). -/
noncomputable def sysC (M : Steps P) (repC : Control → Bool) : LocalSys (Mirrored1 P) where
  tickL := tickC M
  feedC := feedC
  repL := fun m => repC m.vm.ctl
  outL := fun m => m.vm.ctl.output
  Starved := fun m => Starved m.vm

@[simp] theorem sysC_tickL (M : Steps P) (repC : Control → Bool) (m : Mirrored1 P) :
    (sysC M repC).tickL m = tickC M m := rfl

@[simp] theorem sysC_feedC (M : Steps P) (repC : Control → Bool) (a : Fin 2) (m : Mirrored1 P) :
    (sysC M repC).feedC a m = feedC a m := rfl

@[simp] theorem sysC_starved (M : Steps P) (repC : Control → Bool) (m : Mirrored1 P) :
    (sysC M repC).Starved m = Starved m.vm := rfl

/-- **Oracle `outL_abs`.**  The output bit is a control field. -/
theorem outL_abs (M : Steps P) (repC : Control → Bool) (m : Mirrored1 P) :
    (sysC M repC).outL m = (absSC m).ctl.output := rfl

/-! ## 7. From the need to the truncated tick -/

theorem used_le_of_need {raw : List (Fin 2)} {stOf : ℕ → State GalilVM} {k j : ℕ}
    (h : needT' raw stOf k ≤ j) : TickNeed raw stOf k j := by
  have e1 : needL' raw stOf k ≤ needT' raw stOf k :=
    needL'_le_needT' raw stOf (Nat.le_succ k)
  have e2 : needL' raw stOf (k+1) ≤ needT' raw stOf k :=
    needL'_le_needT' raw stOf le_rfl
  have hu : usedVM raw (stOf k).vm ≤ needL' raw stOf k := le_max_left _ _
  have hu' : usedVM raw (stOf (k+1)).vm ≤ needL' raw stOf (k+1) := le_max_left _ _
  have hl : look' raw (stOf k) ≤ needL' raw stOf k := le_max_right _ _
  exact ⟨by omega, by omega, by omega⟩

/-- **The truncated tick.**  A trace tick whose need has arrived survives
truncation to the letters that have arrived. -/
theorem tick_of_need {raw : List (Fin 2)} {stOf : ℕ → State GalilVM} {Pw : Shared}
    {qq : ℕ} {first : Fin 9} {delay : ℕ} {k j : ℕ}
    (hP : PalPeg.GalilTruncTick.SharedTrunc raw j Pw)
    (hT : Tick (galilFrameS Pw qq first) delay (stOf k) (stOf (k+1)))
    (h : TickNeed raw stOf k j) :
    Tick (galilFrameS Pw qq first) delay
      (truncS (raw.length - j) (stOf k)) (truncS (raw.length - j) (stOf (k+1))) := by
  obtain ⟨h1, h2, h3⟩ := h
  exact tick_trunc' raw j hP qq first delay hT h1 h2 h3

/-! ## 8. The oracles -/

theorem stepOf_realizes {Good : Mirrored1 P → Prop} {raw : List (Fin 2)} {stOf : ℕ → State GalilVM} {lastTick : ℕ}
    {M : Steps P}
    (H_init : Realizes Good raw stOf lastTick M.init .init)
    (H_scan : Realizes Good raw stOf lastTick M.scan .scan)
    (H_shift : Realizes Good raw stOf lastTick M.shift .shift)
    (H_copy : Realizes Good raw stOf lastTick M.copy .copy)
    (H_home : Realizes Good raw stOf lastTick M.home .home)
    (H_fpp : Realizes Good raw stOf lastTick M.fpp .fpp)
    (H_markEnd : Realizes Good raw stOf lastTick M.markEnd .markEnd)
    (H_choose : Realizes Good raw stOf lastTick M.choose .choose)
    (H_rewind : Realizes Good raw stOf lastTick M.rewind .rewind)
    (H_replayStart : Realizes Good raw stOf lastTick M.replayStart .replayStart) :
    ∀ md : Mode, Realizes Good raw stOf lastTick (stepOf M md) md := by
  intro md; cases md <;> assumption

/-! ## 9. Arrival of the *correct* letter keeps the trace

The run only ever feeds the letter of its input slot
(`LocalTrackingLatch.inv_micro`), and `LocalShadowConcrete.pal_in_peg_of_shadowed_sysC` tracks
the run across an arrival with the theorem below.  For the letter the run actually delivers it is a theorem: -/

theorem tracked_feedC {raw : List (Fin 2)} {stOf : ℕ → State GalilVM} {m : Mirrored1 P}
    {k j : ℕ} (hw : ViewsWF m.vm) (hp : m.vm.pending = [])
    (hn : Needy raw stOf k j m.vm) (hj : j < raw.length)
    (hs : SufVM raw (stOf k).vm) (hu : usedVM raw (stOf k).vm ≤ j) :
    Needy raw stOf k (j+1) (feedC raw[j] m).vm := by
  refine ⟨by omega, ?_⟩
  show absState'' (feedC raw[j] m).vm = _
  rw [feed_abs_core hw hp raw[j], show absState'' m.vm = truncS (raw.length - j) (stOf k) from hn.2]
  exact arrive_trunc raw j hj (stOf k) hs hu

/-! ## 10. The initial state -/

/-- The initial latched local state: any core, with the controller record reset
to `GalilScaffoldController.initial delay` and nothing pending. -/
def x0C (blank : GalilVML P) (delay : ℕ) : LX (Mirrored1 P) :=
  ⟨⟨{ blank with ctl := GalilScaffoldController.initial delay, pending := [] }, blank.left⟩,
    false, false⟩

/-- **Oracle `x0_ctl`.** -/
theorem x0C_ctl (blank : GalilVML P) (delay : ℕ) :
    (absSC (x0C blank delay).core).ctl = GalilScaffoldController.initial delay := rfl

/-- **Oracle `x0_started`.** -/
theorem x0C_started (blank : GalilVML P) (delay : ℕ) : (x0C blank delay).started = false := rfl

theorem x0C_ans (blank : GalilVML P) (delay : ℕ) : (x0C blank delay).ans = false := rfl

/-- **Oracle `x0_inv`, physical half.** -/
theorem x0C_physWF {blank : GalilVML P} (h : PalPeg.LocalTick1.Inv blank) (delay : ℕ) :
    PhysWF (x0C blank delay).core.vm := by
  refine ⟨⟨h.roles, h.attached, h.views, h.radiusShaped, h.lowerShaped, h.lengthShaped,
    h.shaped⟩, ?_, rfl⟩
  intro hr
  exact absurd (show (false : Bool) = true from hr) (by decide)

/-- **Oracle `x0_inv`, mirror half.** -/
theorem x0C_mirInv1 {blank : GalilVML P} (h : PalPeg.LocalReplaySwap.Twin blank.left blank.center)
    (hw : PalPeg.LocalInputView.WF blank.left) (delay : ℕ) : MirInv1 (x0C blank delay).core :=
  ⟨h, hw⟩

/-! ## 11. The physical half of a mode obligation, closed by `LocalTick1`/`LocalTick3` -/

theorem pending_tickL3 {S : Shared} {qq : ℕ} {firstT : Fin 9} {x y : GalilVML P}
    (h : PalPeg.LocalTick3.TickL3 S qq firstT x y) : y.pending = x.pending := by
  cases h <;> rfl

/-- **The seven phase modes keep the physical pack.**  `LocalTick3.tickL3_inv`
gives `LocalTick1.Inv`; `tickL3_replaying` makes `ParkedOK` vacuous; no phase
tick touches `pending`. -/
theorem physWF_of_tickL3 {S : Shared} {qq : ℕ} {firstT : Fin 9} {x y : GalilVML P}
    (h : PhysWF x) (ht : PalPeg.LocalTick3.TickL3 S qq firstT x y) : PhysWF y := by
  refine ⟨PalPeg.LocalTick3.tickL3_inv h.inv ht, ?_, ?_⟩
  · intro hr
    exact absurd ((PalPeg.LocalTick3.tickL3_replaying ht).2 ▸ hr) (by decide)
  · rw [pending_tickL3 ht]; exact h.pend

theorem pending_tickL1 {S : Shared} {qq : ℕ} {firstT : Fin 9} {d : ℕ} {x y : GalilVML P}
    (h : PalPeg.LocalTick1.TickL1 S qq firstT d x y) : y.pending = x.pending := by
  cases h with
  | wait z ch hm hr hav hs hch =>
      exact (PalPeg.LocalTick1.bgState_pending _ _ _ _).trans hs.frame.pending
  | count z ch hm hav hc hs hch =>
      exact (PalPeg.LocalTick1.bgState_pending _ _ _ _).trans hs.frame.pending
  | «match» z ch o hm hav hc hpol hrep hper hahead hcan hs hmt hch ho =>
      exact (PalPeg.LocalTick1.birthL_pending _ _).trans hs.frame.pending

/-- **A non-replaying scan tick keeps the physical pack.** -/
theorem physWF_of_tickL1 {S : Shared} {qq : ℕ} {firstT : Fin 9} {d : ℕ} {x y : GalilVML P}
    (h : PhysWF x) (hr : x.ctl.replaying = false)
    (ht : PalPeg.LocalTick1.TickL1 S qq firstT d x y) : PhysWF y := by
  refine ⟨PalPeg.LocalTick1.tickL1_inv h.inv ht, ?_, ?_⟩
  · intro hr'
    exact absurd (PalPeg.LocalReplayParked.tickL1_replaying_false ht hr ▸ hr') (by decide)
  · rw [pending_tickL1 ht]; exact h.pend

/-- **A mode obligation splits into its abstract and physical halves.** -/
theorem realizes_of_parts {Good : Mirrored1 P → Prop} {raw : List (Fin 2)} {stOf : ℕ → State GalilVM} {lastTick : ℕ}
    (f : Mirrored1 P → Mirrored1 P) (md : Mode)
    (habs : ∀ (m : Mirrored1 P) (k j : ℕ), InvC Good raw stOf m → m.vm.ctl.mode = md →
      ¬ Starved m.vm → Needy raw stOf k j m.vm → TickNeed raw stOf k j → k < lastTick →
      Needy raw stOf (k+1) j (f m).vm)
    (hphys : ∀ m : Mirrored1 P, InvC Good raw stOf m → m.vm.ctl.mode = md → ¬ Starved m.vm →
      PhysWF (f m).vm ∧ MirInv1 (f m)) :
    Realizes Good raw stOf lastTick f md := by
  intro m k j hinv hmd hns hn hneed hbefore
  exact ⟨habs m k j hinv hmd hns hn hneed hbefore, (hphys m hinv hmd hns).1,
    (hphys m hinv hmd hns).2⟩


#print axioms absHead'_append
#print axioms absR_feedV
#print axioms abs''_feedV
#print axioms feed_abs_core
#print axioms physWF_feedC
#print axioms mirInv1_feedC
#print axioms used_le_of_need
#print axioms tick_of_need
#print axioms stepOf_realizes
#print axioms tracked_feedC
#print axioms x0C_ctl
#print axioms x0C_physWF
#print axioms x0C_mirInv1
#print axioms outL_abs
#print axioms pending_tickL3
#print axioms physWF_of_tickL3
#print axioms pending_tickL1
#print axioms physWF_of_tickL1
#print axioms realizes_of_parts

end PalPeg.LocalSysConcrete
