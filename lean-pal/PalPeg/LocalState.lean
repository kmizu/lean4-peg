import PalPeg.LocalCounter
import PalPeg.LocalRoles
import PalPeg.LocalMirror
import PalPeg.LocalBuffers
import PalPeg.LocalInputView
import PalPeg.GalilVMEncode
import PalPeg.GalilChainEncode

/-!
# 局所化計画, piece 6: the locally realizable state `GalilVML` and its abstraction

The five preceding `Local*` files each remove one non-local effect of the Galil
scaffold in isolation:

* `LocalCounter` — `Counter.reset` in one tape action (segmented unary);
* `LocalRoles`   — a whole-counter move whose source dies, as a role permutation;
* `LocalMirror`  — a whole-counter copy whose source survives, as an eagerly
  synchronized mirror bank plus a background rebuild;
* `LocalBuffers` — `GalilScaffoldControl.reset` (a whole `ProgLang` machine wiped
  in one step) as a double buffer with background erasure;
* `LocalInputView` — the head/walker copies (`left := right`, `walker := p`) as a
  repositioning job on a cursor's own maintained copy of the input.

This file assembles them into **one** record, `GalilVML`, and gives the
abstraction map `abs : GalilVML P → GalilVM` onto the scaffold VM of
`GalilScaffoldTopVM.lean`, together with `absState` onto
`GalilScaffoldTop.State GalilVM`.

Two points about `abs`.

* It is *total and job-independent*: it reads only the active half of each
  double buffer, the `roles`/`pol` bundle of the counter bank and the views —
  never a `job` field, never an idle buffer, never a mirror.  So no
  well-formedness hypothesis is needed to state it, and the background jobs
  (erasure, rebuild, repositioning) are invisible at the abstract level
  (`abs_clearTick_dp`, `abs_mirror_irrelevant`, …).
* The mirrors are nevertheless *pinned* to the bank by `MirrorsAttached`, so
  that a detached mirror abstracts to the very counter it mirrors
  (`abs_radius_mirror`, `abs_lower_mirror`, via `LocalMirror.absCtr_mirror`).

The chain component is kept abstract (`chain : ChainVM`) — its own local
refinement is future work; `GalilChainEncode` already shows it is finitely
tape-encodable.

Finally `StepLocal`/`Local` fix the `K`-locality budget that the eventual
`LocalStepRealize` obligation will consume: in one tick every physical counter
tape undergoes **at most one** `STape.applyAction`, every cursor **at most one**
`arrive`/`moveRight`/`moveLeftV`/`repositionStep`, and every double buffer at
most one `resetL`/`clearTick`/pointwise program step.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.LocalState

open PalPeg.Program
open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldInputHead (PlaceHead)
open PalPeg.GalilScaffoldPlace (Place)
open PalPeg.GalilScaffoldCounter (Counter)
open PalPeg.LocalCounter (Seg)
open PalPeg.LocalRoles (absL)
open PalPeg.LocalMirror (Mirrored Synced Shaped)
open PalPeg.LocalInputView (InputView absHead)

/-! ## 1. The finite type of logical counters

The scaffold's counters, read off `GalilVM` (`cycle`, `remaining`, `radius`,
`length`, `replay`, `lower`), off `SearchVM`'s `GalilScaffoldSearchFinish.State`
(`span`, `work`, `debt`) and off `FppControl.State` (`fppWork`). -/

/-- The logical counters of the Galil scaffold. -/
inductive Ctr
  | cycle | remaining | radius | length | replay | lower
  | span | work | debt | fppWork
  deriving DecidableEq, Fintype

/-! ## 2. Cursors as places

A `Place` is the read-only projection "current letter, then the letters to its
left"; an `InputView` carries exactly that in `focus :: back`, the sentinel
`none` marking the left edge. -/

/-- Strip the cells of a view down to the letters of a `Place`, stopping at the
absent-focus sentinel. -/
def placeLetters : List (Option (Fin 2)) → List (Fin 2)
  | [] => []
  | none :: _ => []
  | some a :: rest => a :: placeLetters rest

/-- The `Place` a cursor stands for. -/
def absPlace (v : InputView) : Place := ⟨placeLetters (v.focus :: v.back), v.gap⟩

@[simp] theorem absPlace_gap (v : InputView) : (absPlace v).gap = v.gap := rfl

@[simp] theorem absPlace_letters (v : InputView) :
    (absPlace v).letters = placeLetters (v.focus :: v.back) := rfl

/-! ## 3. The locally realizable state -/

/-- The `K`-local realization of `GalilVM`.

* `left`/`center`/`right`/`walkerView`/`fppWalker` — five cursors, each owning
  its own maintained copy of the input (`LocalInputView`), fed from the single
  shared arrival list `pending`;
* `phys`/`roles`/`pol` — the counter bank of `LocalRoles` over `P` segmented
  unary tapes (`LocalCounter`);
* `radiusMir`/`lowerMir`/`lengthMir` — the eagerly synchronized mirror banks of
  `LocalMirror` for the three counters that are copied while alive
  (`radius`: `lag := radius`, `margin := radius`, `debt := negate radius`;
  `lower`: `work := lower` at `Search.start`;
  `length`: `fpp.work := inc length` at `FppControl.beginFallback`);
* `dpBuf`/`fppBuf` — the double buffers of `LocalBuffers` for the twelve-tape DP
  machine and the nine-tape fpp machine, their program counters and `done` bits
  living in the finite control;
* `chain` — kept abstract for now;
* `ctl` plus the finite control bits of `GalilVMEncode.encodeCtl`.

Note the deviation from the sketch in `ASSEMBLY_PLAN.md`: `GalilVM` has *two*
walker places (the search walker and `fpp.walker`), so five views are needed for
`abs` to be total, not four. -/
structure GalilVML (P : ℕ) where
  /-- (a) the three input heads, and the arrivals not yet delivered to them. -/
  left : InputView
  center : InputView
  right : InputView
  pending : List (Fin 2)
  /-- The search walker (`prepareWindow`'s copy cursor). -/
  walkerView : InputView
  /-- (b) the fpp walker, as a fourth/fifth cursor. -/
  fppWalker : InputView
  /-- (c) the counter bank: `P` segmented unary tapes, addressed by role. -/
  phys : Fin P → STape Seg
  roles : Ctr → Fin P
  pol : Ctr → Bool
  /-- Two mirrors of `radius`, one of `lower` and one of `length`. -/
  radiusMir : Mirrored 2
  lowerMir : Mirrored 1
  lengthMir : Mirrored 1
  /-- (d) the two `ProgLang` machines as double buffers, pcs in control. -/
  dpBuf : LocalBuffers.Buffered 12
  dpPc : ℕ
  dpDone : Bool
  fppBuf : LocalBuffers.Buffered 9
  fppPc : ℕ
  fppDone : Bool
  /-- (e) the chain view, still abstract. -/
  chain : ChainVM
  /-- (f) the controller record and the finite control bits. -/
  ctl : GalilScaffoldController.Control
  searchMode : GalilScaffoldSearchFinish.Mode
  searchFinalStage : Bool
  searchQuarter : Fin 4
  fppMode : FppControl.Mode
  fppFinalStage : Bool
  periodOnly : Bool

variable {P : ℕ}

/-! ## 4. Well-formedness of the bank -/

/-- Distinct logical counters live on distinct physical tapes. -/
def RolesInjective (x : GalilVML P) : Prop := Function.Injective x.roles

/-- The mirror banks are pinned to the tapes their counters own. -/
def MirrorsAttached (x : GalilVML P) : Prop :=
  x.radiusMir.src = x.phys (x.roles .radius) ∧ x.lowerMir.src = x.phys (x.roles .lower) ∧
    x.lengthMir.src = x.phys (x.roles .length)

/-- The cursors' queues satisfy the Hood–Melville invariant. -/
def ViewsWF (x : GalilVML P) : Prop :=
  LocalInputView.WF x.left ∧ LocalInputView.WF x.center ∧ LocalInputView.WF x.right ∧
    LocalInputView.WF x.walkerView ∧ LocalInputView.WF x.fppWalker

/-! ## 5. The abstraction map -/

/-- The logical counter values of the bank. -/
def absCtrs (x : GalilVML P) : Ctr → Counter := absL x.phys x.roles x.pol

@[simp] theorem absCtrs_apply (x : GalilVML P) (c : Ctr) :
    absCtrs x c = LocalCounter.absCtr (x.phys (x.roles c)) (x.pol c) := rfl

/-- **The abstraction map.**  Reads only the cursors, the `roles`/`pol` bundle
and the *active* half of each double buffer — no job state, no mirror, no idle
buffer.  Hence it is total, with no well-formedness hypothesis. -/
def abs (x : GalilVML P) : GalilVM where
  left := absHead x.left x.pending
  center := absHead x.center x.pending
  right := absHead x.right x.pending
  chain := x.chain
  cycle := absCtrs x .cycle
  remaining := absCtrs x .remaining
  radius := absCtrs x .radius
  length := absCtrs x .length
  replay := absCtrs x .replay
  fpp :=
    { mode := x.fppMode
      program := ⟨⟨x.fppPc, LocalBuffers.abs x.fppBuf⟩, x.fppDone⟩
      work := absCtrs x .fppWork
      walker := absPlace x.fppWalker
      finalStage := x.fppFinalStage }
  search :=
    { mode := x.searchMode
      finalStage := x.searchFinalStage
      span := absCtrs x .span
      work := absCtrs x .work
      debt := absCtrs x .debt
      quarter := x.searchQuarter }
  dp := ⟨⟨x.dpPc, LocalBuffers.abs x.dpBuf⟩, x.dpDone⟩
  lower := absCtrs x .lower
  periodOnly := x.periodOnly
  walker := absPlace x.walkerView

/-- The abstraction onto a full scaffold state. -/
def absState (x : GalilVML P) : GalilScaffoldTop.State GalilVM := ⟨x.ctl, abs x⟩

@[simp] theorem absState_ctl (x : GalilVML P) : (absState x).ctl = x.ctl := rfl
@[simp] theorem absState_vm (x : GalilVML P) : (absState x).vm = abs x := rfl

/-! ### Field lemmas -/

@[simp] theorem abs_left (x : GalilVML P) : (abs x).left = absHead x.left x.pending := rfl
@[simp] theorem abs_center (x : GalilVML P) : (abs x).center = absHead x.center x.pending := rfl
@[simp] theorem abs_right (x : GalilVML P) : (abs x).right = absHead x.right x.pending := rfl
@[simp] theorem abs_chain (x : GalilVML P) : (abs x).chain = x.chain := rfl
@[simp] theorem abs_cycle (x : GalilVML P) : (abs x).cycle = absCtrs x .cycle := rfl
@[simp] theorem abs_remaining (x : GalilVML P) : (abs x).remaining = absCtrs x .remaining := rfl
@[simp] theorem abs_radius (x : GalilVML P) : (abs x).radius = absCtrs x .radius := rfl
@[simp] theorem abs_length (x : GalilVML P) : (abs x).length = absCtrs x .length := rfl
@[simp] theorem abs_replay (x : GalilVML P) : (abs x).replay = absCtrs x .replay := rfl
@[simp] theorem abs_lower (x : GalilVML P) : (abs x).lower = absCtrs x .lower := rfl
@[simp] theorem abs_periodOnly (x : GalilVML P) : (abs x).periodOnly = x.periodOnly := rfl
@[simp] theorem abs_walker (x : GalilVML P) : (abs x).walker = absPlace x.walkerView := rfl

@[simp] theorem abs_dp (x : GalilVML P) :
    (abs x).dp = ⟨⟨x.dpPc, LocalBuffers.abs x.dpBuf⟩, x.dpDone⟩ := rfl
@[simp] theorem abs_dp_tapes (x : GalilVML P) :
    (abs x).dp.config.tapes = LocalBuffers.abs x.dpBuf := rfl
@[simp] theorem abs_dp_pc (x : GalilVML P) : (abs x).dp.config.pc = x.dpPc := rfl
@[simp] theorem abs_dp_done (x : GalilVML P) : (abs x).dp.done = x.dpDone := rfl

@[simp] theorem abs_fpp_mode (x : GalilVML P) : (abs x).fpp.mode = x.fppMode := rfl
@[simp] theorem abs_fpp_program (x : GalilVML P) :
    (abs x).fpp.program = ⟨⟨x.fppPc, LocalBuffers.abs x.fppBuf⟩, x.fppDone⟩ := rfl
@[simp] theorem abs_fpp_tapes (x : GalilVML P) :
    (abs x).fpp.program.config.tapes = LocalBuffers.abs x.fppBuf := rfl
@[simp] theorem abs_fpp_work (x : GalilVML P) : (abs x).fpp.work = absCtrs x .fppWork := rfl
@[simp] theorem abs_fpp_walker (x : GalilVML P) : (abs x).fpp.walker = absPlace x.fppWalker := rfl
@[simp] theorem abs_fpp_finalStage (x : GalilVML P) :
    (abs x).fpp.finalStage = x.fppFinalStage := rfl

@[simp] theorem abs_search_mode (x : GalilVML P) : (abs x).search.mode = x.searchMode := rfl
@[simp] theorem abs_search_finalStage (x : GalilVML P) :
    (abs x).search.finalStage = x.searchFinalStage := rfl
@[simp] theorem abs_search_span (x : GalilVML P) : (abs x).search.span = absCtrs x .span := rfl
@[simp] theorem abs_search_work (x : GalilVML P) : (abs x).search.work = absCtrs x .work := rfl
@[simp] theorem abs_search_debt (x : GalilVML P) : (abs x).search.debt = absCtrs x .debt := rfl
@[simp] theorem abs_search_quarter (x : GalilVML P) :
    (abs x).search.quarter = x.searchQuarter := rfl

/-- Every abstracted counter is canonical, with no hypothesis at all. -/
theorem abs_canonical (x : GalilVML P) (c : Ctr) :
    GalilScaffoldCounter.Canonical (absCtrs x c) :=
  LocalCounter.absCtr_canonical _ _

/-! ### `abs` does not read job state

The four lemmas below are the precise sense in which `abs` is well defined
independently of the background jobs: mirrors, `job` fields and idle buffer
halves are all invisible. -/

/-- Mirror banks are invisible to `abs`. -/
theorem abs_mirror_irrelevant (x : GalilVML P) (m : Mirrored 2) (m' m'' : Mirrored 1) :
    abs { x with radiusMir := m, lowerMir := m', lengthMir := m'' } = abs x := rfl

/-- The erasure-job counters are invisible to `abs`. -/
theorem abs_job_irrelevant (x : GalilVML P) (j₁ j₂ : Option ℕ) :
    abs { x with dpBuf := { x.dpBuf with job := j₁ },
                 fppBuf := { x.fppBuf with job := j₂ } } = abs x := rfl

/-- One background erasure tick on the DP buffer is invisible to `abs`. -/
theorem abs_clearTick_dp (x : GalilVML P) :
    abs { x with dpBuf := LocalBuffers.clearTick x.dpBuf } = abs x := by
  simp only [abs, absCtrs, LocalRoles.absL, LocalBuffers.abs_clearTick]

/-- One background erasure tick on the fpp buffer is invisible to `abs`. -/
theorem abs_clearTick_fpp (x : GalilVML P) :
    abs { x with fppBuf := LocalBuffers.clearTick x.fppBuf } = abs x := by
  simp only [abs, absCtrs, LocalRoles.absL, LocalBuffers.abs_clearTick]

/-- `n` background erasure ticks on both buffers are invisible to `abs`. -/
theorem abs_clearTickN (x : GalilVML P) (m n : ℕ) :
    abs { x with dpBuf := LocalBuffers.clearTickN m x.dpBuf,
                 fppBuf := LocalBuffers.clearTickN n x.fppBuf } = abs x := by
  simp only [abs, absCtrs, LocalRoles.absL, LocalBuffers.abs_clearTickN]

/-! ### A local reset really is the non-local `GalilScaffoldControl.reset`

The `abs` image of `resetL` on a cleaned buffer is the wholesale tape wipe of
`GalilScaffoldControl.reset`, i.e. the non-local effect is realized. -/

theorem abs_resetL_dp {x : GalilVML P} {W : ℕ} (hj : x.dpBuf.job.isSome)
    (hW : ∀ i, LocalBuffers.size (LocalBuffers.idle x.dpBuf i) ≤ W) (entry : ℕ) :
    (abs { x with dpBuf := LocalBuffers.resetL (LocalBuffers.clearTickN (W + 1) x.dpBuf),
                  dpPc := entry, dpDone := true }).dp
      = GalilScaffoldControl.reset entry (abs x).dp := by
  show (⟨⟨entry, LocalBuffers.abs
      (LocalBuffers.resetL (LocalBuffers.clearTickN (W + 1) x.dpBuf))⟩, true⟩ :
        GalilScaffoldControl.Machine 12) = _
  rw [LocalBuffers.abs_resetL_clearTickN hj hW]
  rfl

theorem abs_resetL_fpp {x : GalilVML P} {W : ℕ} (hj : x.fppBuf.job.isSome)
    (hW : ∀ i, LocalBuffers.size (LocalBuffers.idle x.fppBuf i) ≤ W) (entry : ℕ) :
    (abs { x with fppBuf := LocalBuffers.resetL (LocalBuffers.clearTickN (W + 1) x.fppBuf),
                  fppPc := entry, fppDone := true }).fpp.program
      = GalilScaffoldControl.reset entry (abs x).fpp.program := by
  show (⟨⟨entry, LocalBuffers.abs
      (LocalBuffers.resetL (LocalBuffers.clearTickN (W + 1) x.fppBuf))⟩, true⟩ :
        GalilScaffoldControl.Machine 9) = _
  rw [LocalBuffers.abs_resetL_clearTickN hj hW]
  rfl

/-! ### Mirrors abstract to the counters they mirror -/

/-- A synchronized mirror of `radius`, detached, *is* the abstract `radius`. -/
theorem abs_radius_mirror {x : GalilVML P} (ha : MirrorsAttached x)
    (hs : Synced x.radiusMir) (i : Fin 2) :
    LocalCounter.absCtr (x.radiusMir.mir i) (x.pol .radius) = (abs x).radius := by
  rw [LocalMirror.absCtr_mirror hs i, ha.1]; rfl

/-- The same mirror handed over with the flipped polarity bit is
`initialDebt radius = negate radius`. -/
theorem abs_radius_mirror_negate {x : GalilVML P} (ha : MirrorsAttached x)
    (hs : Synced x.radiusMir) (i : Fin 2) :
    LocalCounter.absCtr (x.radiusMir.mir i) (!x.pol .radius)
      = LocalCounter.negate (abs x).radius := by
  rw [LocalCounter.neg_flip, LocalMirror.absCtr_mirror hs i, ha.1]; rfl

/-- A synchronized mirror of `lower`, detached, *is* the abstract `lower`. -/
theorem abs_lower_mirror {x : GalilVML P} (ha : MirrorsAttached x)
    (hs : Synced x.lowerMir) (i : Fin 1) :
    LocalCounter.absCtr (x.lowerMir.mir i) (x.pol .lower) = (abs x).lower := by
  rw [LocalMirror.absCtr_mirror hs i, ha.2.1]; rfl

/-- A synchronized mirror of `length`, detached, *is* the abstract `length`.
This is what makes `fpp.work := inc length` a one-action commit: take the mirror,
`push` it once. -/
theorem abs_length_mirror {x : GalilVML P} (ha : MirrorsAttached x)
    (hs : Synced x.lengthMir) (i : Fin 1) :
    LocalCounter.absCtr (x.lengthMir.mir i) (x.pol .length) = (abs x).length := by
  rw [LocalMirror.absCtr_mirror hs i, ha.2.2]; rfl

/-! ### A role move realizes a whole-counter assignment -/

/-- `dst := src ; src := reset` on the abstract counters, at the cost of one
`resetSeg` on one physical tape. -/
theorem absCtrs_move {x : GalilVML P} {src dst : Ctr} (hne : src ≠ dst)
    (hinj : RolesInjective x) :
    absCtrs { x with phys := LocalRoles.moveTapes (x.roles dst) x.phys,
                     roles := LocalRoles.moveRoles src dst x.roles,
                     pol := LocalRoles.movePol src dst x.pol }
      = fun c => if c = dst then absCtrs x src
                 else if c = src then GalilScaffoldCounter.reset
                 else absCtrs x c :=
  LocalRoles.absL_move hne hinj

/-! ## 6. The `K`-locality budget -/

/-- One physical counter tape changes by at most one `STape.applyAction`. -/
def TapeLocal (t t' : STape Seg) : Prop :=
  t' = t ∨ ∃ wa : Seg × PegSeparation.RealTimeTM.Move,
    t' = STape.applyAction LocalCounter.blank t wa

theorem tapeLocal_refl (t : STape Seg) : TapeLocal t t := Or.inl rfl

theorem tapeLocal_push (t : STape Seg) : TapeLocal t (LocalCounter.push t) :=
  Or.inr ⟨(LocalCounter.mark, .right), rfl⟩

theorem tapeLocal_pop (t : STape Seg) : TapeLocal t (LocalCounter.pop t) :=
  Or.inr ⟨(LocalCounter.blank, .left), rfl⟩

theorem tapeLocal_resetSeg (t : STape Seg) : TapeLocal t (LocalCounter.resetSeg t) :=
  Or.inr ⟨(LocalCounter.sep, .right), rfl⟩

/-- A whole mirror bank moves locally. -/
def MirLocal {k : ℕ} (m m' : Mirrored k) : Prop :=
  TapeLocal m.src m'.src ∧ ∀ i, TapeLocal (m.mir i) (m'.mir i)

theorem mirLocal_pushAll {k : ℕ} (m : Mirrored k) : MirLocal m (LocalMirror.pushAll m) :=
  ⟨tapeLocal_push _, fun _ => tapeLocal_push _⟩

theorem mirLocal_popAll {k : ℕ} (m : Mirrored k) : MirLocal m (LocalMirror.popAll m) :=
  ⟨tapeLocal_pop _, fun _ => tapeLocal_pop _⟩

theorem mirLocal_resetAll {k : ℕ} (m : Mirrored k) : MirLocal m (LocalMirror.resetAll m) :=
  ⟨tapeLocal_resetSeg _, fun _ => tapeLocal_resetSeg _⟩

/-- One cursor changes by at most one of the four `O(1)` view actions. -/
def ViewLocal (v v' : InputView) : Prop :=
  v' = v ∨ (∃ a : Fin 2, v' = LocalInputView.arrive a v) ∨
    v' = LocalInputView.moveRight v ∨ v' = LocalInputView.moveLeftV v ∨
    ∃ target : ℕ, v' = LocalInputView.repositionStep target v

theorem viewLocal_refl (v : InputView) : ViewLocal v v := Or.inl rfl

theorem viewLocal_arrive (a : Fin 2) (v : InputView) :
    ViewLocal v (LocalInputView.arrive a v) := Or.inr (Or.inl ⟨a, rfl⟩)

theorem viewLocal_moveRight (v : InputView) :
    ViewLocal v (LocalInputView.moveRight v) := Or.inr (Or.inr (Or.inl rfl))

theorem viewLocal_moveLeft (v : InputView) :
    ViewLocal v (LocalInputView.moveLeftV v) := Or.inr (Or.inr (Or.inr (Or.inl rfl)))

theorem viewLocal_repositionStep (target : ℕ) (v : InputView) :
    ViewLocal v (LocalInputView.repositionStep target v) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨target, rfl⟩)))

/-- One double buffer changes by at most one control-level act (`resetL`), one
background erasure tick (`clearTick`), or one *pointwise* program step — one
action per tape, which is what a `ProgLang` micro-step does. -/
def BufLocal {n : ℕ} (x y : LocalBuffers.Buffered n) : Prop :=
  y = x ∨ y = LocalBuffers.resetL x ∨ y = LocalBuffers.clearTick x ∨
    ∃ g : Fin n → GalilScaffoldTape.Tape → GalilScaffoldTape.Tape,
      y = LocalBuffers.stepL (fun ts i => g i (ts i)) x

theorem bufLocal_refl {n : ℕ} (x : LocalBuffers.Buffered n) : BufLocal x x := Or.inl rfl

theorem bufLocal_resetL {n : ℕ} (x : LocalBuffers.Buffered n) :
    BufLocal x (LocalBuffers.resetL x) := Or.inr (Or.inl rfl)

theorem bufLocal_clearTick {n : ℕ} (x : LocalBuffers.Buffered n) :
    BufLocal x (LocalBuffers.clearTick x) := Or.inr (Or.inr (Or.inl rfl))

theorem bufLocal_stepL {n : ℕ} (g : Fin n → GalilScaffoldTape.Tape → GalilScaffoldTape.Tape)
    (x : LocalBuffers.Buffered n) :
    BufLocal x (LocalBuffers.stepL (fun ts i => g i (ts i)) x) :=
  Or.inr (Or.inr (Or.inr ⟨g, rfl⟩))

/-- **The locality predicate on a pair of states.**  Everything that is not a
tape or a cursor (`roles`, `pol`, pcs, `done` bits, the chain tag, `ctl` and the
finite control bits) is unconstrained: those are finite-control data, and a
finite control may rewrite them arbitrarily in one step. -/
def StepLocal (x y : GalilVML P) : Prop :=
  (∀ j : Fin P, TapeLocal (x.phys j) (y.phys j)) ∧
  MirLocal x.radiusMir y.radiusMir ∧
  MirLocal x.lowerMir y.lowerMir ∧
  MirLocal x.lengthMir y.lengthMir ∧
  ViewLocal x.left y.left ∧
  ViewLocal x.center y.center ∧
  ViewLocal x.right y.right ∧
  ViewLocal x.walkerView y.walkerView ∧
  ViewLocal x.fppWalker y.fppWalker ∧
  BufLocal x.dpBuf y.dpBuf ∧
  BufLocal x.fppBuf y.fppBuf

/-- A state transformer is `K`-local when every pair `(x, f x)` is. -/
def Local (f : GalilVML P → GalilVML P) : Prop := ∀ x : GalilVML P, StepLocal x (f x)

theorem stepLocal_refl (x : GalilVML P) : StepLocal x x :=
  ⟨fun _ => tapeLocal_refl _, ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
    ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
    ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
    viewLocal_refl _, viewLocal_refl _, viewLocal_refl _, viewLocal_refl _, viewLocal_refl _,
    bufLocal_refl _, bufLocal_refl _⟩

theorem local_id : Local (id : GalilVML P → GalilVML P) := fun x => stepLocal_refl x

/-- Pure finite-control updates — including the role permutation that realizes a
whole-counter move — are local: no tape and no cursor moves. -/
theorem stepLocal_control (x : GalilVML P) (roles : Ctr → Fin P) (pol : Ctr → Bool)
    (pc₁ pc₂ : ℕ) (d₁ d₂ : Bool) (ch : ChainVM) (c : GalilScaffoldController.Control)
    (sm : GalilScaffoldSearchFinish.Mode) (sf : Bool) (sq : Fin 4)
    (fm : FppControl.Mode) (ff po : Bool) (q : List (Fin 2)) :
    StepLocal x { x with roles := roles, pol := pol, dpPc := pc₁, fppPc := pc₂,
                         dpDone := d₁, fppDone := d₂, chain := ch, ctl := c,
                         searchMode := sm, searchFinalStage := sf, searchQuarter := sq,
                         fppMode := fm, fppFinalStage := ff, periodOnly := po,
                         pending := q } :=
  stepLocal_refl x

/-- The role move of `absCtrs_move` costs exactly one tape action, on one tape. -/
theorem stepLocal_move (x : GalilVML P) (src dst : Ctr) :
    StepLocal x { x with phys := LocalRoles.moveTapes (x.roles dst) x.phys,
                         roles := LocalRoles.moveRoles src dst x.roles,
                         pol := LocalRoles.movePol src dst x.pol } := by
  refine ⟨fun j => ?_, ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
    ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
    ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
    viewLocal_refl _, viewLocal_refl _, viewLocal_refl _, viewLocal_refl _, viewLocal_refl _,
    bufLocal_refl _, bufLocal_refl _⟩
  show TapeLocal (x.phys j) (LocalRoles.moveTapes (x.roles dst) x.phys j)
  by_cases h : j = x.roles dst
  · rw [h, LocalRoles.moveTapes_apply_self]
    exact h ▸ tapeLocal_resetSeg (x.phys (x.roles dst))
  · rw [LocalRoles.moveTapes_apply_of_ne x.phys h]
    exact tapeLocal_refl _

/-- Delivering one arrival to all five cursors is local. -/
theorem stepLocal_arrive (x : GalilVML P) (a : Fin 2) (q : List (Fin 2)) :
    StepLocal x { x with left := LocalInputView.arrive a x.left,
                         center := LocalInputView.arrive a x.center,
                         right := LocalInputView.arrive a x.right,
                         walkerView := LocalInputView.arrive a x.walkerView,
                         fppWalker := LocalInputView.arrive a x.fppWalker,
                         pending := q } :=
  ⟨fun _ => tapeLocal_refl _, ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
    ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
    ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
    viewLocal_arrive a _, viewLocal_arrive a _, viewLocal_arrive a _,
    viewLocal_arrive a _, viewLocal_arrive a _,
    bufLocal_refl _, bufLocal_refl _⟩

/-- One repositioning micro-step of the "copy a head" job is local. -/
theorem stepLocal_reposition (x : GalilVML P) (target : ℕ) :
    StepLocal x { x with left := LocalInputView.repositionStep target x.left } :=
  ⟨fun _ => tapeLocal_refl _, ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
    ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
    ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
    viewLocal_repositionStep target _, viewLocal_refl _, viewLocal_refl _,
    viewLocal_refl _, viewLocal_refl _,
    bufLocal_refl _, bufLocal_refl _⟩

/-- One background erasure tick on both buffers is local (and, by
`abs_clearTick_dp`/`abs_clearTick_fpp`, invisible to `abs`). -/
theorem stepLocal_clearTick (x : GalilVML P) :
    StepLocal x { x with dpBuf := LocalBuffers.clearTick x.dpBuf,
                         fppBuf := LocalBuffers.clearTick x.fppBuf } :=
  ⟨fun _ => tapeLocal_refl _, ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
    ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
    ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
    viewLocal_refl _, viewLocal_refl _, viewLocal_refl _, viewLocal_refl _, viewLocal_refl _,
    bufLocal_clearTick _, bufLocal_clearTick _⟩

#print axioms abs
#print axioms absState
#print axioms abs_canonical
#print axioms abs_mirror_irrelevant
#print axioms abs_job_irrelevant
#print axioms abs_clearTick_dp
#print axioms abs_clearTick_fpp
#print axioms abs_clearTickN
#print axioms abs_resetL_dp
#print axioms abs_resetL_fpp
#print axioms abs_radius_mirror
#print axioms abs_radius_mirror_negate
#print axioms abs_lower_mirror
#print axioms abs_length_mirror
#print axioms absCtrs_move
#print axioms local_id
#print axioms stepLocal_control
#print axioms stepLocal_move
#print axioms stepLocal_arrive
#print axioms stepLocal_reposition
#print axioms stepLocal_clearTick

end PalPeg.LocalState
