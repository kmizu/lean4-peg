import PalPeg.LocalState
import PalPeg.LocalArrival
import PalPeg.LocalTick2
import PalPeg.GalilScaffoldTopSearch

/-!
# 局所化計画, piece 7: the *local* scan-mode ticks (`TickL1`)

`PalPeg.LocalState` assembled the local refinements into one record
`GalilVML P`; `PalPeg.LocalArrival` corrected its abstraction to `abs'` /
`absState'` (the never-yet-visited suffix goes into the abstract `incoming`
FIFO, so that an arrival is abstraction-invisible); `PalPeg.LocalTick2` gave the
iterated locality budget `StepLocalN`.  This file takes the **first slice** of
the local step relation: the three scan-mode constructors of
`PalPeg.GalilScaffoldTop.Tick` that a *scan* tick can use, namely `scan_wait`,
`scan_count` and `scan_match`, against the frame `galilFrameS` of
`GalilScaffoldTopSearch.lean`.

## What is realized here, and at what cost

A scan tick of the Scala scaffold does, at the VM level,

* `clock` decrement / reset — finite control, free (`Control` is not
  constrained by `StepLocal`);
* the counters `radius.inc()`, `length.inc(); length.inc()`, `replay.dec()`
  (while replaying) and — inside `chain.matched()` when `periodOnly` —
  `cycle.dec()`: each is **one** `push`/`pop` on one segmented unary tape
  (`LocalCounter`), and `radius`/`length` additionally push their mirror banks
  (`LocalMirror.pushAll`) so that `MirrorsAttached` survives;
* the head moves `left.left()` and `right.right()`: **one**
  `LocalInputView.moveLeftV` / `LocalInputView.moveRight` on the cursor's own
  maintained copy of the input, abstracted by `absHead'_moveLeft` and by
  `PalPeg.LocalArrival.moveRight_ok` under `Ahead`;
* one DP quantum: `GalilScaffoldSearchRun.SafeQuanta` is at most **64** safe
  program calls, realized as 64 `LocalBuffers.stepL` on `dpBuf`, each of which
  is visible at the abstract level by `LocalBuffers.abs_stepL`
  (`dpRun`/`stepLocalN_dpRun` below give the witness);
* one chain tick, which stays **abstract** (`chain : ChainVM` is still a
  finite-control tag in `GalilVML`) — the unrealized component.

So one local scan tick costs `c₁ = 66` local steps: 64 for the search/DP
quantum plus the two comparison micro-steps.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.LocalTick1

open PalPeg.Program (STape)
open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldTop
open PalPeg.GalilScaffoldController (Control)
open PalPeg.LocalState
open PalPeg.LocalCounter (Seg)
open PalPeg.LocalInputView (InputView)
open PalPeg.LocalMirror (Shaped)
open PalPeg.LocalArrival (absHead' abs' absState' Ahead)
open PalPeg.LocalTick2 (StepLocal2 StepLocalN)

attribute [local ext] GalilVM

variable {P : ℕ}

/-! ## 1. Iterated locality

`StepLocalN` is `PalPeg.LocalTick2.StepLocalN`; only the arithmetic of chaining
is added here. -/

theorem stepLocalN_zero (x : GalilVML P) : StepLocalN 0 x x := rfl

theorem stepLocalN_one {x y : GalilVML P} (h : StepLocal x y) : StepLocalN 1 x y :=
  ⟨y, h, rfl⟩

theorem stepLocalN_succ : ∀ (n : ℕ) {x y : GalilVML P},
    StepLocalN n x y → StepLocalN (n + 1) x y := by
  intro n
  induction n with
  | zero => intro x y h; cases h; exact ⟨_, stepLocal_refl _, rfl⟩
  | succ n ih => intro x y h; obtain ⟨w, hw, hr⟩ := h; exact ⟨w, hw, ih hr⟩

theorem stepLocalN_le {n m : ℕ} {x y : GalilVML P} (hnm : n ≤ m)
    (h : StepLocalN n x y) : StepLocalN m x y := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  clear hnm
  induction k with
  | zero => simpa using h
  | succ k ih => exact stepLocalN_succ _ ih

theorem stepLocalN_trans : ∀ (m n : ℕ) {x y z : GalilVML P},
    StepLocalN m x y → StepLocalN n y z → StepLocalN (m + n) x z := by
  intro m
  induction m with
  | zero =>
      intro n x y z h1 h2
      cases h1
      simpa using h2
  | succ m ih =>
      intro n x y z h1 h2
      obtain ⟨w, hw, hr⟩ := h1
      have he : m + 1 + n = (m + n) + 1 := by omega
      rw [he]
      exact ⟨w, hw, ih n hr h2⟩

/-- A `LocalTick2` two-step commit is two local steps. -/
theorem stepLocalN_of_stepLocal2 {x y : GalilVML P} (h : StepLocal2 x y) :
    StepLocalN 2 x y := by
  obtain ⟨m, h1, h2⟩ := h
  exact ⟨m, h1, stepLocalN_one h2⟩

/-! ### The DP quantum is 64 local steps

`dpRun g n` applies `n` pointwise `LocalBuffers.stepL` actions to the DP double
buffer.  It is `n`-local, and by `LocalBuffers.abs_stepL` each of them is exactly
one micro-step of the abstract twelve-tape DP machine.  This is the witness that
the `SafeQuanta` of 64 safe calls is locally realizable; that the *particular*
64 functions compute `SafeQuanta` is the gap kept in `SearchLocal.effect`. -/

/-- One pointwise program step on the DP buffer. -/
def dpStep (g : Fin 12 → GalilScaffoldTape.Tape → GalilScaffoldTape.Tape)
    (x : GalilVML P) : GalilVML P :=
  { x with dpBuf := LocalBuffers.stepL (fun ts i => g i (ts i)) x.dpBuf }

/-- `n` pointwise program steps. -/
def dpRun (g : ℕ → Fin 12 → GalilScaffoldTape.Tape → GalilScaffoldTape.Tape) :
    ℕ → GalilVML P → GalilVML P
  | 0, x => x
  | n + 1, x => dpRun g n (dpStep (g n) x)

theorem stepLocal_dpStep (g : Fin 12 → GalilScaffoldTape.Tape → GalilScaffoldTape.Tape)
    (x : GalilVML P) : StepLocal x (dpStep g x) :=
  ⟨fun _ => tapeLocal_refl _,
    ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
    ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
    ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
    viewLocal_refl _, viewLocal_refl _, viewLocal_refl _, viewLocal_refl _, viewLocal_refl _,
    bufLocal_stepL _ _, bufLocal_refl _⟩

theorem abs_dpStep (g : Fin 12 → GalilScaffoldTape.Tape → GalilScaffoldTape.Tape)
    (x : GalilVML P) :
    (abs' (dpStep g x)).dp.config.tapes
      = fun i => g i ((abs' x).dp.config.tapes i) :=
  LocalBuffers.abs_stepL _ _

theorem stepLocalN_dpRun (g : ℕ → Fin 12 → GalilScaffoldTape.Tape → GalilScaffoldTape.Tape) :
    ∀ (n : ℕ) (x : GalilVML P), StepLocalN n x (dpRun g n x) := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih => intro x; exact ⟨dpStep (g n) x, stepLocal_dpStep _ _, ih _⟩

/-- The search quantum's budget: 64 safe DP calls. -/
def searchSteps : ℕ := 64

/-- **The per-tick local budget of a scan tick.** -/
def c₁ : ℕ := 66

/-! ## 2. The well-formedness invariant -/

/-- Every logical counter tape carries the segmented-unary shape. -/
def CountersShaped (x : GalilVML P) : Prop :=
  ∀ c : Ctr, ∃ v, LocalCounter.SegCtr (x.phys (x.roles c)) v

/-- The counters a scan tick increments/decrements sit on the positive side of
the polarity bundle. -/
def PolPos (x : GalilVML P) : Prop :=
  x.pol .radius = true ∧ x.pol .length = true ∧ x.pol .replay = true ∧ x.pol .cycle = true

/-- The well-formedness invariant carried through a local tick. -/
structure Inv (x : GalilVML P) : Prop where
  roles : RolesInjective x
  attached : MirrorsAttached x
  views : ViewsWF x
  radiusShaped : ∃ v, Shaped x.radiusMir v
  lowerShaped : ∃ v, Shaped x.lowerMir v
  lengthShaped : ∃ v, Shaped x.lengthMir v
  shaped : CountersShaped x

theorem roles_ne {w : GalilVML P} (h : RolesInjective w) {c d : Ctr} (hcd : c ≠ d) :
    w.roles c ≠ w.roles d := fun he => hcd (h he)

/-- `push` on a positively-signed counter is `Counter.inc`. -/
theorem absCtr_push_pol (t : STape Seg) {b : Bool} (hb : b = true) :
    LocalCounter.absCtr (LocalCounter.push t) b
      = GalilScaffoldCounter.inc (LocalCounter.absCtr t b) := by
  rw [LocalCounter.absCtr_push, if_pos hb]

/-- `pop` on a nonzero, positively-signed counter is `Counter.dec`. -/
theorem absCtr_pop_pol {t : STape Seg} (h : 0 < LocalCounter.val t) {b : Bool} (hb : b = true) :
    LocalCounter.absCtr (LocalCounter.pop t) b
      = GalilScaffoldCounter.dec (LocalCounter.absCtr t b) := by
  rw [LocalCounter.absCtr_pop (v := LocalCounter.val t - 1) (by omega) b, if_pos hb]

/-! ### The corrected abstraction of a left move

`PalPeg.LocalArrival` proved `moveRight_ok`; the left move needs the same
statement for `absHead'`, and it is unconditional. -/

theorem absHead'_moveLeft (v : InputView) (q : List (Fin 2)) :
    absHead' (LocalInputView.moveLeftV v) q
      = GalilScaffoldInputHead.left (absHead' v q) := by
  cases hg : v.gap
  · cases hb : v.back with
    | nil =>
        simp [LocalInputView.moveLeftV, GalilScaffoldInputHead.left,
          PalPeg.LocalArrival.absHead', GalilScaffoldInputHead.moveLeft,
          LocalInputView.stepLeft, hg, hb]
    | cons c r =>
        simp [LocalInputView.moveLeftV, GalilScaffoldInputHead.left,
          PalPeg.LocalArrival.absHead', GalilScaffoldInputHead.moveLeft,
          LocalInputView.stepLeft, hg, hb]
  · simp [LocalInputView.moveLeftV, GalilScaffoldInputHead.left,
      PalPeg.LocalArrival.absHead', hg]

theorem WF_moveLeftV {v : InputView} (hw : LocalInputView.WF v) :
    LocalInputView.WF (LocalInputView.moveLeftV v) := by
  unfold LocalInputView.moveLeftV
  split
  · exact hw
  · exact LocalInputView.WF_stepLeft hw

theorem WF_moveRight {v : InputView} (hw : LocalInputView.WF v) :
    LocalInputView.WF (LocalInputView.moveRight v) := by
  unfold LocalInputView.moveRight
  split
  · exact LocalInputView.WF_stepRight hw
  · exact hw

/-! ## 3. The search co-process, kept as a hypothesis

`SearchFrame x z` says that `z` differs from `x` only in the components the
search owns: its walker cursor, the DP double buffer and program counter, its
mode bits, and the three counter tapes `span`/`work`/`debt`. -/

structure SearchFrame (x z : GalilVML P) : Prop where
  left : z.left = x.left
  center : z.center = x.center
  right : z.right = x.right
  pending : z.pending = x.pending
  fppWalker : z.fppWalker = x.fppWalker
  roles : z.roles = x.roles
  pol : z.pol = x.pol
  phys : ∀ j : Fin P, j ≠ x.roles .span → j ≠ x.roles .work → j ≠ x.roles .debt →
    z.phys j = x.phys j
  radiusMir : z.radiusMir = x.radiusMir
  lowerMir : z.lowerMir = x.lowerMir
  lengthMir : z.lengthMir = x.lengthMir
  fppBuf : z.fppBuf = x.fppBuf
  fppPc : z.fppPc = x.fppPc
  fppDone : z.fppDone = x.fppDone
  chain : z.chain = x.chain
  ctl : z.ctl = x.ctl
  fppMode : z.fppMode = x.fppMode
  fppFinalStage : z.fppFinalStage = x.fppFinalStage
  periodOnly : z.periodOnly = x.periodOnly

/-- **The search hypothesis.**  The search co-process's own local realization on
the event `a`: `searchSteps` local steps, confined to the search components,
preserving `Inv`, and abstracting to the scaffold's `searchEffect`. -/
structure SearchLocal (S : Shared) (a : Bool) (x z : GalilVML P) : Prop where
  steps : StepLocalN searchSteps x z
  frame : SearchFrame x z
  inv : Inv x → Inv z
  effect : searchEffect S a (abs' x) (searchLens.get (abs' z))

theorem searchFrame_absCtrs {x z : GalilVML P} (hinj : RolesInjective x)
    (hf : SearchFrame x z) {c : Ctr} (h1 : c ≠ .span) (h2 : c ≠ .work) (h3 : c ≠ .debt) :
    absCtrs z c = absCtrs x c := by
  show LocalCounter.absCtr (z.phys (z.roles c)) (z.pol c)
      = LocalCounter.absCtr (x.phys (x.roles c)) (x.pol c)
  rw [hf.roles, hf.pol,
    hf.phys (x.roles c) (roles_ne hinj h1) (roles_ne hinj h2) (roles_ne hinj h3)]

/-- The search step is invisible outside the search projection. -/
theorem searchFrame_abs {x z : GalilVML P} (hinj : RolesInjective x) (hf : SearchFrame x z) :
    abs' z = searchLens.set (abs' x) (searchLens.get (abs' z)) := by
  have hc : ∀ {c : Ctr}, c ≠ .span → c ≠ .work → c ≠ .debt → absCtrs z c = absCtrs x c :=
    fun {c} h1 h2 h3 => searchFrame_absCtrs hinj hf h1 h2 h3
  ext
  · show absHead' z.left z.pending = absHead' x.left x.pending
    rw [hf.left, hf.pending]
  · show absHead' z.center z.pending = absHead' x.center x.pending
    rw [hf.center, hf.pending]
  · show absHead' z.right z.pending = absHead' x.right x.pending
    rw [hf.right, hf.pending]
  · show z.chain = x.chain
    rw [hf.chain]
  · exact hc (by decide) (by decide) (by decide)
  · exact hc (by decide) (by decide) (by decide)
  · exact hc (by decide) (by decide) (by decide)
  · exact hc (by decide) (by decide) (by decide)
  · exact hc (by decide) (by decide) (by decide)
  · show (⟨z.fppMode, ⟨⟨z.fppPc, LocalBuffers.abs z.fppBuf⟩, z.fppDone⟩, absCtrs z .fppWork,
        absPlace z.fppWalker, z.fppFinalStage⟩ : FppControl.State) = _
    rw [hf.fppMode, hf.fppPc, hf.fppBuf, hf.fppDone, hf.fppWalker, hf.fppFinalStage,
      hc (c := Ctr.fppWork) (by decide) (by decide) (by decide)]
    rfl
  · rfl
  · rfl
  · rfl
  · show z.periodOnly = x.periodOnly
    rw [hf.periodOnly]
  · rfl

/-! ## 4. The concrete local operations of a scan comparison -/

/-- The tape bank after the first micro-step of a comparison: `radius++`,
the first unit of `length += 2`, `replay--` while replaying, `cycle--` in
`periodOnly`.  Four distinct tapes (under `RolesInjective`), one action each. -/
def physStep1 (w : GalilVML P) : Fin P → STape Seg := fun j =>
  if j = w.roles .radius then LocalCounter.push (w.phys j)
  else if j = w.roles .length then LocalCounter.push (w.phys j)
  else if j = w.roles .replay ∧ w.ctl.replaying = true then LocalCounter.pop (w.phys j)
  else if j = w.roles .cycle ∧ w.periodOnly = true then LocalCounter.pop (w.phys j)
  else w.phys j

/-- First micro-step of a comparison: `L.left()`, `R.right()`, the bank update
and the two mirror pushes that keep `MirrorsAttached`. -/
def scanStep1 (w : GalilVML P) : GalilVML P :=
  { w with left := LocalInputView.moveLeftV w.left,
           right := LocalInputView.moveRight w.right,
           phys := physStep1 w,
           radiusMir := LocalMirror.pushAll w.radiusMir,
           lengthMir := LocalMirror.pushAll w.lengthMir }

/-- The second unit of `length += 2`. -/
def physStep2 (w : GalilVML P) : Fin P → STape Seg := fun j =>
  if j = w.roles .length then LocalCounter.push (w.phys j) else w.phys j

/-- Second micro-step of a comparison: the second `length` unit (with its
mirror) and the chain tag (finite control). -/
def scanStep2 (ch : ChainVM) (w : GalilVML P) : GalilVML P :=
  { w with phys := physStep2 w, chain := ch,
           lengthMir := LocalMirror.pushAll w.lengthMir }

/-- The VM part of a matched scan tick. -/
def matchVm (ch : ChainVM) (w : GalilVML P) : GalilVML P := scanStep2 ch (scanStep1 w)

/-- The state after a background-only scan tick: a new chain tag and a new
controller record, nothing else. -/
def bgState (ch : ChainVM) (c : Control) (z : GalilVML P) : GalilVML P :=
  { z with chain := ch, ctl := c }

/-- The controller record a matched comparison installs. -/
def matchCtl (S : Shared) (delay : ℕ) (o : Bool) (c : Control) (v : GalilVM) : Control :=
  { c with clock := delay, output := o, replaying := c.replaying && !S.replayExhausted v }

theorem scanStep1_phys (w : GalilVML P) : (scanStep1 w).phys = physStep1 w := rfl
theorem scanStep1_roles (w : GalilVML P) : (scanStep1 w).roles = w.roles := rfl
theorem scanStep1_pol (w : GalilVML P) : (scanStep1 w).pol = w.pol := rfl
theorem scanStep1_ctl (w : GalilVML P) : (scanStep1 w).ctl = w.ctl := rfl
theorem scanStep1_periodOnly (w : GalilVML P) : (scanStep1 w).periodOnly = w.periodOnly := rfl

theorem abs_bgState (ch : ChainVM) (c : Control) (z : GalilVML P) :
    abs' (bgState ch c z) = { abs' z with chain := ch } := rfl

/-! ### Locality of the two concrete micro-steps -/

theorem stepLocal_scanStep1 (w : GalilVML P) : StepLocal w (scanStep1 w) := by
  refine ⟨fun j => ?_, mirLocal_pushAll _,
    ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩, mirLocal_pushAll _,
    viewLocal_moveLeft _, viewLocal_refl _, viewLocal_moveRight _,
    viewLocal_refl _, viewLocal_refl _, bufLocal_refl _, bufLocal_refl _⟩
  show TapeLocal (w.phys j) (physStep1 w j)
  unfold physStep1
  split_ifs <;>
    first
      | exact tapeLocal_push _
      | exact tapeLocal_pop _
      | exact tapeLocal_refl _

theorem stepLocal_scanStep2 (ch : ChainVM) (c : Control) (w : GalilVML P) :
    StepLocal w { scanStep2 ch w with ctl := c } := by
  refine ⟨fun j => ?_, ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
    ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩, mirLocal_pushAll _,
    viewLocal_refl _, viewLocal_refl _, viewLocal_refl _,
    viewLocal_refl _, viewLocal_refl _, bufLocal_refl _, bufLocal_refl _⟩
  show TapeLocal (w.phys j) (physStep2 w j)
  unfold physStep2
  split_ifs <;> first | exact tapeLocal_push _ | exact tapeLocal_refl _

/-- A pure finite-control update (chain tag and controller record) is local. -/
theorem stepLocal_bgState (w : GalilVML P) (ch : ChainVM) (c : Control) :
    StepLocal w (bgState ch c w) := stepLocal_refl w

/-! ### The bank after the two micro-steps -/

theorem physMatch_radius {w : GalilVML P} (h : RolesInjective w) (ch : ChainVM) :
    (matchVm ch w).phys (w.roles .radius) = LocalCounter.push (w.phys (w.roles .radius)) := by
  have h1 : w.roles .radius ≠ w.roles .length := roles_ne h (by decide)
  show physStep2 (scanStep1 w) (w.roles .radius) = _
  simp [physStep2, physStep1, scanStep1_phys, scanStep1_roles, h1]

theorem physMatch_length {w : GalilVML P} (h : RolesInjective w) (ch : ChainVM) :
    (matchVm ch w).phys (w.roles .length)
      = LocalCounter.push (LocalCounter.push (w.phys (w.roles .length))) := by
  have h1 : w.roles .length ≠ w.roles .radius := roles_ne h (by decide)
  show physStep2 (scanStep1 w) (w.roles .length) = _
  simp [physStep2, physStep1, scanStep1_phys, scanStep1_roles, h1]

theorem physMatch_replay {w : GalilVML P} (h : RolesInjective w) (ch : ChainVM) :
    (matchVm ch w).phys (w.roles .replay)
      = (if w.ctl.replaying = true then LocalCounter.pop (w.phys (w.roles .replay))
         else w.phys (w.roles .replay)) := by
  have h1 : w.roles .replay ≠ w.roles .length := roles_ne h (by decide)
  have h2 : w.roles .replay ≠ w.roles .radius := roles_ne h (by decide)
  have h3 : w.roles .replay ≠ w.roles .cycle := roles_ne h (by decide)
  show physStep2 (scanStep1 w) (w.roles .replay) = _
  by_cases hr : w.ctl.replaying = true
  · simp [physStep2, physStep1, scanStep1_phys, scanStep1_roles, h1, h2, hr]
  · simp [physStep2, physStep1, scanStep1_phys, scanStep1_roles, h1, h2, h3, hr]

theorem physMatch_cycle {w : GalilVML P} (h : RolesInjective w) (ch : ChainVM) :
    (matchVm ch w).phys (w.roles .cycle)
      = (if w.periodOnly = true then LocalCounter.pop (w.phys (w.roles .cycle))
         else w.phys (w.roles .cycle)) := by
  have h1 : w.roles .cycle ≠ w.roles .length := roles_ne h (by decide)
  have h2 : w.roles .cycle ≠ w.roles .radius := roles_ne h (by decide)
  have h3 : w.roles .cycle ≠ w.roles .replay := roles_ne h (by decide)
  show physStep2 (scanStep1 w) (w.roles .cycle) = _
  by_cases hp : w.periodOnly = true
  · simp [physStep2, physStep1, scanStep1_phys, scanStep1_roles, h1, h2, h3, hp]
  · simp [physStep2, physStep1, scanStep1_phys, scanStep1_roles, h1, h2, h3, hp]

theorem physMatch_other {w : GalilVML P} (h : RolesInjective w) (ch : ChainVM) {c : Ctr}
    (h1 : c ≠ .radius) (h2 : c ≠ .length) (h3 : c ≠ .replay) (h4 : c ≠ .cycle) :
    (matchVm ch w).phys (w.roles c) = w.phys (w.roles c) := by
  have e1 : w.roles c ≠ w.roles .radius := roles_ne h h1
  have e2 : w.roles c ≠ w.roles .length := roles_ne h h2
  have e3 : w.roles c ≠ w.roles .replay := roles_ne h h3
  have e4 : w.roles c ≠ w.roles .cycle := roles_ne h h4
  show physStep2 (scanStep1 w) (w.roles c) = _
  simp [physStep2, physStep1, scanStep1_phys, scanStep1_roles, e1, e2, e3, e4]

theorem matchVm_radiusMir (ch : ChainVM) (w : GalilVML P) :
    (matchVm ch w).radiusMir = LocalMirror.pushAll w.radiusMir := rfl

theorem matchVm_lowerMir (ch : ChainVM) (w : GalilVML P) :
    (matchVm ch w).lowerMir = w.lowerMir := rfl

theorem matchVm_lengthMir (ch : ChainVM) (w : GalilVML P) :
    (matchVm ch w).lengthMir = LocalMirror.pushAll (LocalMirror.pushAll w.lengthMir) := rfl

/-! ## 5. `replayDec` projections not already in `GalilScaffoldTopSearch` -/

theorem replayDec_replay' (b : Bool) (s : GalilVM) :
    (replayDec b s).replay =
      if b = true then GalilScaffoldCounter.dec s.replay else s.replay := by cases b <;> rfl

theorem replayDec_dp (b : Bool) (s : GalilVM) : (replayDec b s).dp = s.dp := by cases b <;> rfl

theorem replayDec_lower (b : Bool) (s : GalilVM) : (replayDec b s).lower = s.lower := by
  cases b <;> rfl

theorem replayDec_walker (b : Bool) (s : GalilVM) : (replayDec b s).walker = s.walker := by
  cases b <;> rfl

theorem replayDec_search' (b : Bool) (s : GalilVM) : (replayDec b s).search = s.search := by
  cases b <;> rfl

/-! ## 6. The abstraction of a matched comparison -/

/-- The scan projection a matched comparison produces. -/
def matchScan (x : GalilVML P) (ch : ChainVM) : ScanVM :=
  ⟨GalilScaffoldInputHead.left (abs' x).left,
   GalilScaffoldChainVerifier.right (abs' x).right, ch⟩

theorem abs_matchVm {x z : GalilVML P} (hinv : Inv x) (hpol : PolPos x)
    (hf : SearchFrame x z)
    (hrep : x.ctl.replaying = true → 0 < LocalCounter.val (x.phys (x.roles .replay)))
    (hper : x.periodOnly = true → 0 < LocalCounter.val (x.phys (x.roles .cycle)))
    (hahead : Ahead x.right x.pending)
    (hcan : GalilScaffoldChainVerifier.canRight (absHead' x.right x.pending))
    (ch : ChainVM) :
    abs' (matchVm ch z)
      = replayDec x.ctl.replaying
          (afterCompare (abs' x) (matchScan x ch) (searchLens.get (abs' z))) := by
  have hinj : RolesInjective x := hinv.roles
  have hinjz : RolesInjective z := by
    intro a b hab
    apply hinj
    rw [← hf.roles]; exact hab
  have hctr : ∀ {c : Ctr}, c ≠ .span → c ≠ .work → c ≠ .debt → absCtrs z c = absCtrs x c :=
    fun {c} h1 h2 h3 => searchFrame_absCtrs hinj hf h1 h2 h3
  have hzr : z.phys (z.roles .radius) = x.phys (x.roles .radius) := by
    rw [hf.roles]
    exact hf.phys _ (roles_ne hinj (by decide)) (roles_ne hinj (by decide))
      (roles_ne hinj (by decide))
  have hzl : z.phys (z.roles .length) = x.phys (x.roles .length) := by
    rw [hf.roles]
    exact hf.phys _ (roles_ne hinj (by decide)) (roles_ne hinj (by decide))
      (roles_ne hinj (by decide))
  have hzp : z.phys (z.roles .replay) = x.phys (x.roles .replay) := by
    rw [hf.roles]
    exact hf.phys _ (roles_ne hinj (by decide)) (roles_ne hinj (by decide))
      (roles_ne hinj (by decide))
  have hzc : z.phys (z.roles .cycle) = x.phys (x.roles .cycle) := by
    rw [hf.roles]
    exact hf.phys _ (roles_ne hinj (by decide)) (roles_ne hinj (by decide))
      (roles_ne hinj (by decide))
  ext
  -- left
  · rw [replayDec_left]
    show absHead' (LocalInputView.moveLeftV z.left) z.pending = _
    rw [absHead'_moveLeft, hf.left, hf.pending]
    rfl
  -- center
  · rw [replayDec_center]
    show absHead' z.center z.pending = _
    rw [hf.center, hf.pending]
    rfl
  -- right
  · rw [replayDec_right]
    show absHead' (LocalInputView.moveRight z.right) z.pending = _
    have hwz : LocalInputView.WF z.right := by rw [hf.right]; exact hinv.views.2.2.1
    have haz : Ahead z.right z.pending := by rw [hf.right, hf.pending]; exact hahead
    have hcz : GalilScaffoldChainVerifier.canRight (absHead' z.right z.pending) := by
      rw [hf.right, hf.pending]; exact hcan
    rw [PalPeg.LocalArrival.moveRight_ok hwz haz hcz, hf.right, hf.pending]
    rfl
  -- chain
  · rw [replayDec_chain]
    rfl
  -- cycle
  · rw [replayDec_cycle]
    show LocalCounter.absCtr ((matchVm ch z).phys (z.roles .cycle)) (z.pol .cycle)
        = cycleAfter (abs' x)
    rw [physMatch_cycle hinjz ch, hzc, hf.pol, hf.periodOnly, cycleAfter]
    by_cases hp : x.periodOnly = true
    · rw [if_pos hp, absCtr_pop_pol (hper hp) hpol.2.2.2,
        if_pos (show (abs' x).periodOnly = true from hp)]
      rfl
    · rw [if_neg hp, if_neg (show ¬ ((abs' x).periodOnly = true) from hp)]
      rfl
  -- remaining
  · rw [replayDec_remaining]
    show LocalCounter.absCtr ((matchVm ch z).phys (z.roles .remaining)) (z.pol .remaining) = _
    rw [physMatch_other hinjz ch (by decide) (by decide) (by decide) (by decide)]
    exact hctr (by decide) (by decide) (by decide)
  -- radius
  · rw [replayDec_radius]
    show LocalCounter.absCtr ((matchVm ch z).phys (z.roles .radius)) (z.pol .radius) = _
    rw [physMatch_radius hinjz ch, hzr, hf.pol, absCtr_push_pol _ hpol.1]
    rfl
  -- length
  · rw [replayDec_length]
    show LocalCounter.absCtr ((matchVm ch z).phys (z.roles .length)) (z.pol .length) = _
    rw [physMatch_length hinjz ch, hzl, hf.pol, absCtr_push_pol _ hpol.2.1,
      absCtr_push_pol _ hpol.2.1]
    rfl
  -- replay
  · rw [replayDec_replay']
    show LocalCounter.absCtr ((matchVm ch z).phys (z.roles .replay)) (z.pol .replay)
        = if x.ctl.replaying = true then GalilScaffoldCounter.dec (abs' x).replay
          else (abs' x).replay
    rw [physMatch_replay hinjz ch, hzp, hf.pol, hf.ctl]
    by_cases hr : x.ctl.replaying = true
    · rw [if_pos hr, if_pos hr, absCtr_pop_pol (hrep hr) hpol.2.2.1]
      rfl
    · rw [if_neg hr, if_neg hr]
      rfl
  -- fpp
  · rw [replayDec_fpp]
    show (⟨z.fppMode, ⟨⟨z.fppPc, LocalBuffers.abs z.fppBuf⟩, z.fppDone⟩,
        LocalCounter.absCtr ((matchVm ch z).phys (z.roles .fppWork)) (z.pol .fppWork),
        absPlace z.fppWalker, z.fppFinalStage⟩ : FppControl.State) = _
    rw [physMatch_other hinjz ch (by decide) (by decide) (by decide) (by decide)]
    rw [hf.fppMode, hf.fppPc, hf.fppBuf, hf.fppDone, hf.fppWalker, hf.fppFinalStage,
      show LocalCounter.absCtr (z.phys (z.roles .fppWork)) (z.pol .fppWork)
        = absCtrs x .fppWork from hctr (by decide) (by decide) (by decide)]
    rfl
  -- search
  · rw [replayDec_search']
    show (⟨z.searchMode, z.searchFinalStage,
        LocalCounter.absCtr ((matchVm ch z).phys (z.roles .span)) (z.pol .span),
        LocalCounter.absCtr ((matchVm ch z).phys (z.roles .work)) (z.pol .work),
        LocalCounter.absCtr ((matchVm ch z).phys (z.roles .debt)) (z.pol .debt),
        z.searchQuarter⟩ : GalilScaffoldSearchFinish.State) = _
    rw [physMatch_other hinjz ch (by decide) (by decide) (by decide) (by decide),
      physMatch_other hinjz ch (by decide) (by decide) (by decide) (by decide),
      physMatch_other hinjz ch (by decide) (by decide) (by decide) (by decide)]
    rfl
  -- dp
  · rw [replayDec_dp]
    rfl
  -- lower
  · rw [replayDec_lower]
    show LocalCounter.absCtr ((matchVm ch z).phys (z.roles .lower)) (z.pol .lower) = _
    rw [physMatch_other hinjz ch (by decide) (by decide) (by decide) (by decide)]
    rfl
  -- periodOnly
  · rw [replayDec_periodOnly]
    show z.periodOnly = _
    rw [hf.periodOnly]
    rfl
  -- walker
  · rw [replayDec_walker]
    rfl

/-! ## 7. The local scan ticks -/

/-- **The first slice of the local step relation**: the three scan-mode ticks
that stay inside `scan` (`scan_wait`, `scan_count`) or perform a matched
comparison (`scan_match`). -/
inductive TickL1 {P : ℕ} (S : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) :
    GalilVML P → GalilVML P → Prop
  | wait (x z : GalilVML P) (ch : ChainVM)
      (hm : x.ctl.mode = .scan)
      (hr : x.ctl.replaying = false)
      (hav : ¬ (galilFrameS S q first).available (abs' x))
      (hs : SearchLocal S false x z)
      (hch : chainAt false
        (decide ((searchLens.get (abs' z)).search.mode = .found))
        ((searchLens.get (abs' z)).dp.config.tapes 11)
        (S.centre (abs' x)) (S.place (abs' x))
        (abs' x).center (abs' x).radius x.chain ch) :
      TickL1 S q first delay x (bgState ch x.ctl z)
  | count (x z : GalilVML P) (ch : ChainVM)
      (hm : x.ctl.mode = .scan)
      (hav : x.ctl.replaying = true ∨ (galilFrameS S q first).available (abs' x))
      (hc : 1 < x.ctl.clock)
      (hs : SearchLocal S false x z)
      (hch : chainAt false
        (decide ((searchLens.get (abs' z)).search.mode = .found))
        ((searchLens.get (abs' z)).dp.config.tapes 11)
        (S.centre (abs' x)) (S.place (abs' x))
        (abs' x).center (abs' x).radius x.chain ch) :
      TickL1 S q first delay x (bgState ch { x.ctl with clock := x.ctl.clock - 1 } z)
  | «match» (x z : GalilVML P) (ch : ChainVM) (o : Bool)
      (hm : x.ctl.mode = .scan)
      (hav : x.ctl.replaying = true ∨ (galilFrameS S q first).available (abs' x))
      (hc : x.ctl.clock = 1)
      (hpol : PolPos x)
      (hrep : x.ctl.replaying = true → 0 < LocalCounter.val (x.phys (x.roles .replay)))
      (hper : x.periodOnly = true → 0 < LocalCounter.val (x.phys (x.roles .cycle)))
      (hahead : Ahead x.right x.pending)
      (hcan : GalilScaffoldChainVerifier.canRight (absHead' x.right x.pending))
      (hs : SearchLocal S true x z)
      (hmt : (galilFrameS S q first).matched (scanLens.set (abs' x) (matchScan x ch)))
      (hch : chainAt true
        (decide ((searchLens.get (abs' z)).search.mode = .found))
        ((searchLens.get (abs' z)).dp.config.tapes 11)
        (S.centre (abs' x)) (S.place (abs' x))
        (abs' x).center (abs' x).radius x.chain (matchScan x ch).chain)
      (ho : refresh (galilFrameS S q first) (abs' (matchVm ch z)) x.ctl.output o) :
      TickL1 S q first delay x
        { matchVm ch z with ctl := matchCtl S delay o x.ctl (abs' (matchVm ch z)) }

/-! ### Locality: every local scan tick costs at most `c₁ = 66` steps -/

theorem tickL1_local {S : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ} {x y : GalilVML P}
    (h : TickL1 S q first delay x y) : StepLocalN c₁ x y := by
  cases h with
  | wait z ch hm hr hav hs hch =>
      refine stepLocalN_le (n := searchSteps + 1) (by decide) ?_
      exact stepLocalN_trans searchSteps 1 hs.steps
        (stepLocalN_one (stepLocal_bgState z ch _))
  | count z ch hm hav hc hs hch =>
      refine stepLocalN_le (n := searchSteps + 1) (by decide) ?_
      exact stepLocalN_trans searchSteps 1 hs.steps
        (stepLocalN_one (stepLocal_bgState z ch _))
  | «match» z ch o hm hav hc hpol hrep hper hahead hcan hs hmt hch ho =>
      have h2 : StepLocalN 2 z
          { matchVm ch z with ctl := matchCtl S delay o x.ctl (abs' (matchVm ch z)) } :=
        stepLocalN_trans 1 1 (stepLocalN_one (stepLocal_scanStep1 z))
          (stepLocalN_one (stepLocal_scanStep2 ch
            (matchCtl S delay o x.ctl (abs' (matchVm ch z))) (scanStep1 z)))
      exact stepLocalN_le (n := searchSteps + 2) (by decide)
        (stepLocalN_trans searchSteps 2 hs.steps h2)

/-! ### The invariants are preserved -/

theorem inv_matchVm {x : GalilVML P} (hinv : Inv x) (ch : ChainVM)
    (hrep : x.ctl.replaying = true → 0 < LocalCounter.val (x.phys (x.roles .replay)))
    (hper : x.periodOnly = true → 0 < LocalCounter.val (x.phys (x.roles .cycle))) :
    Inv (matchVm ch x) := by
  have hinj : RolesInjective x := hinv.roles
  obtain ⟨vr, hvr⟩ := hinv.radiusShaped
  obtain ⟨vl, hvl⟩ := hinv.lengthShaped
  refine ⟨hinj, ?_, ?_, ⟨vr + 1, LocalMirror.shaped_pushAll hvr⟩, hinv.lowerShaped,
    ⟨vl + 1 + 1, LocalMirror.shaped_pushAll (LocalMirror.shaped_pushAll hvl)⟩, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · show LocalCounter.push x.radiusMir.src = (matchVm ch x).phys (x.roles .radius)
      rw [physMatch_radius hinj ch, hinv.attached.1]
    · show x.lowerMir.src = (matchVm ch x).phys (x.roles .lower)
      rw [physMatch_other hinj ch (by decide) (by decide) (by decide) (by decide)]
      exact hinv.attached.2.1
    · show LocalCounter.push (LocalCounter.push x.lengthMir.src)
        = (matchVm ch x).phys (x.roles .length)
      rw [physMatch_length hinj ch, hinv.attached.2.2]
  · exact ⟨WF_moveLeftV hinv.views.1, hinv.views.2.1, WF_moveRight hinv.views.2.2.1,
      hinv.views.2.2.2.1, hinv.views.2.2.2.2⟩
  · intro c
    obtain ⟨v, hv⟩ := hinv.shaped c
    show ∃ w, LocalCounter.SegCtr ((matchVm ch x).phys (x.roles c)) w
    by_cases h1 : c = .radius
    · subst h1
      exact ⟨v + 1, by rw [physMatch_radius hinj ch]; exact LocalCounter.segCtr_push hv⟩
    by_cases h2 : c = .length
    · subst h2
      exact ⟨v + 2, by
        rw [physMatch_length hinj ch]
        exact LocalCounter.segCtr_push (LocalCounter.segCtr_push hv)⟩
    by_cases h3 : c = .replay
    · subst h3
      by_cases hr : x.ctl.replaying = true
      · have hvv : LocalCounter.val (x.phys (x.roles .replay)) = v :=
          LocalCounter.val_eq_of_segCtr hv
        have hpos := hrep hr
        have hv1 : LocalCounter.SegCtr (x.phys (x.roles .replay)) (v - 1 + 1) := by
          rw [show v - 1 + 1 = v by omega]; exact hv
        exact ⟨v - 1, by
          rw [physMatch_replay hinj ch, if_pos hr]; exact LocalCounter.segCtr_pop hv1⟩
      · exact ⟨v, by rw [physMatch_replay hinj ch, if_neg hr]; exact hv⟩
    by_cases h4 : c = .cycle
    · subst h4
      by_cases hp : x.periodOnly = true
      · have hvv : LocalCounter.val (x.phys (x.roles .cycle)) = v :=
          LocalCounter.val_eq_of_segCtr hv
        have hpos := hper hp
        have hv1 : LocalCounter.SegCtr (x.phys (x.roles .cycle)) (v - 1 + 1) := by
          rw [show v - 1 + 1 = v by omega]; exact hv
        exact ⟨v - 1, by
          rw [physMatch_cycle hinj ch, if_pos hp]; exact LocalCounter.segCtr_pop hv1⟩
      · exact ⟨v, by rw [physMatch_cycle hinj ch, if_neg hp]; exact hv⟩
    · exact ⟨v, by rw [physMatch_other hinj ch h1 h2 h3 h4]; exact hv⟩

theorem tickL1_inv {S : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ} {x y : GalilVML P}
    (hinv : Inv x) (h : TickL1 S q first delay x y) : Inv y := by
  cases h with
  | wait z ch hm hr hav hs hch =>
      obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := hs.inv hinv
      exact ⟨i1, i2, i3, i4, i5, i6, i7⟩
  | count z ch hm hav hc hs hch =>
      obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := hs.inv hinv
      exact ⟨i1, i2, i3, i4, i5, i6, i7⟩
  | «match» z ch o hm hav hc hpol hrep hper hahead hcan hs hmt hch ho =>
      have hinvz : Inv z := hs.inv hinv
      have hf := hs.frame
      have hzp : z.phys (z.roles .replay) = x.phys (x.roles .replay) := by
        rw [hf.roles]
        exact hf.phys _ (roles_ne hinv.roles (by decide)) (roles_ne hinv.roles (by decide))
          (roles_ne hinv.roles (by decide))
      have hzc : z.phys (z.roles .cycle) = x.phys (x.roles .cycle) := by
        rw [hf.roles]
        exact hf.phys _ (roles_ne hinv.roles (by decide)) (roles_ne hinv.roles (by decide))
          (roles_ne hinv.roles (by decide))
      have hrepz : z.ctl.replaying = true →
          0 < LocalCounter.val (z.phys (z.roles .replay)) := by
        rw [hzp, hf.ctl]; exact hrep
      have hperz : z.periodOnly = true → 0 < LocalCounter.val (z.phys (z.roles .cycle)) := by
        rw [hzc, hf.periodOnly]; exact hper
      obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := inv_matchVm hinvz ch hrepz hperz
      exact ⟨i1, i2, i3, i4, i5, i6, i7⟩

/-! ### The abstraction: a local scan tick is a scaffold `Tick` -/

theorem tickL1_abs {S : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ} {x y : GalilVML P}
    (hinv : Inv x) (h : TickL1 S q first delay x y) :
    Tick (galilFrameS S q first) delay (absState' x) (absState' y) := by
  cases h with
  | wait z ch hm hr hav hs hch =>
      have hf := hs.frame
      have habs : abs' (bgState ch x.ctl z)
          = searchLens.set
              (scanLens.set (abs' x) (scanLens.get (abs' (bgState ch x.ctl z))))
              (searchLens.get (abs' (bgState ch x.ctl z))) := by
        show abs' (bgState ch x.ctl z)
            = searchLens.set
                (scanLens.set (abs' x) ⟨(abs' z).left, (abs' z).right, ch⟩)
                (searchLens.get (abs' z))
        rw [abs_bgState, searchFrame_abs hinv.roles hf]
        ext <;> rfl
      have hb : (galilFrameS S q first).background (abs' x) (abs' (bgState ch x.ctl z)) := by
        refine ⟨?_, ?_, hs.effect, hch, habs⟩
        · show absHead' z.left z.pending = _
          rw [hf.left, hf.pending]
          rfl
        · show absHead' z.right z.pending = _
          rw [hf.right, hf.pending]
          rfl
      exact Tick.scan_wait (F := galilFrameS S q first) (delay := delay)
        x.ctl (abs' x) _ hm ⟨hr, hav⟩ hb
  | count z ch hm hav hc hs hch =>
      have hf := hs.frame
      have habs : abs' (bgState ch { x.ctl with clock := x.ctl.clock - 1 } z)
          = searchLens.set
              (scanLens.set (abs' x)
                (scanLens.get (abs' (bgState ch { x.ctl with clock := x.ctl.clock - 1 } z))))
              (searchLens.get (abs' (bgState ch { x.ctl with clock := x.ctl.clock - 1 } z))) := by
        show abs' (bgState ch { x.ctl with clock := x.ctl.clock - 1 } z)
            = searchLens.set
                (scanLens.set (abs' x) ⟨(abs' z).left, (abs' z).right, ch⟩)
                (searchLens.get (abs' z))
        rw [abs_bgState, searchFrame_abs hinv.roles hf]
        ext <;> rfl
      have hb : (galilFrameS S q first).background (abs' x)
          (abs' (bgState ch { x.ctl with clock := x.ctl.clock - 1 } z)) := by
        refine ⟨?_, ?_, hs.effect, hch, habs⟩
        · show absHead' z.left z.pending = _
          rw [hf.left, hf.pending]
          rfl
        · show absHead' z.right z.pending = _
          rw [hf.right, hf.pending]
          rfl
      exact Tick.scan_count (F := galilFrameS S q first) (delay := delay)
        x.ctl (abs' x) _ hm hav hc hb
  | «match» z ch o hm hav hc hpol hrep hper hahead hcan hs hmt hch ho =>
      have hf := hs.frame
      have habs := abs_matchVm hinv hpol hf hrep hper hahead hcan ch
      have hcmp : (galilFrameS S q first).compare (abs' x)
          (afterCompare (abs' x) (matchScan x ch) (searchLens.get (abs' z))) :=
        ⟨matchScan x ch, searchLens.get (abs' z), true, rfl, rfl,
          ⟨fun _ => hmt, fun _ => rfl⟩, hs.effect, hch, rfl⟩
      have hmt' : (galilFrameS S q first).matched
          (afterCompare (abs' x) (matchScan x ch) (searchLens.get (abs' z))) := hmt
      have ho' : refresh (galilFrameS S q first)
          (replayDec x.ctl.replaying
            (afterCompare (abs' x) (matchScan x ch) (searchLens.get (abs' z))))
          x.ctl.output o := by
        rw [← habs]; exact ho
      have ht := Tick.scan_match (F := galilFrameS S q first) (delay := delay)
        x.ctl (abs' x) _ _ o hm hav hc hcmp hmt'
        (matchedPlace_replayDec S q first x.ctl.replaying _) ho'
      rw [← habs] at ht
      exact ht

#print axioms stepLocalN_trans
#print axioms stepLocalN_dpRun
#print axioms absHead'_moveLeft
#print axioms searchFrame_abs
#print axioms abs_matchVm
#print axioms tickL1_local
#print axioms tickL1_inv
#print axioms tickL1_abs

end PalPeg.LocalTick1
