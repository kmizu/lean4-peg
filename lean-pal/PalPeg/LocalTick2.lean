import PalPeg.LocalState
import PalPeg.GalilScaffoldTopRestart
import PalPeg.GalilScaffoldTopShiftCycle

/-!
# 局所化計画, piece 7: the *non-local* abstract effects as O(1) commits

`LocalState` gave the state `GalilVML P`, its abstraction `abs` and the locality
budget `StepLocal`.  This file is the second slice of the local step relation:
the four scaffold transitions whose abstract effect touches *many* components at
once,

* `restartVM entry`            (`GalilScaffoldTopRestart`),
* `replayStartVM entry`        (`GalilScaffoldTopReplay`),
* `beginShiftVM h w`           (`GalilScaffoldTopShiftCycle`),
* `FppControl.beginFallback`   (`GalilScaffoldChainFallback`),

realized by **commits**: O(1) finite-control acts (a role repoint, a `resetSeg`
or `push` on one tape each, a `resetL` on a double buffer) plus *background
jobs* that must already have finished.  The jobs appear here as `stutter` steps
whose `abs` image moves only the one view they drive.

Two deliberate design points.

* A commit never *writes* a counter value: it only repoints `roles`/`pol` at a
  physical tape that already holds the value.  For a value copied off a *live*
  source the tape is an eagerly synchronized mirror (`LocalMirror.take`), which
  is why `commitRestart` takes the `work := max lower 1` copy off the lower
  mirror and the `debt := initialDebt radius` copy off the radius mirror with
  the polarity bit flipped.
* A commit is at most **two** `StepLocal` steps (`StepLocal2`): the length
  counter of `beginShiftVM` needs two `push`es, and the fpp program of
  `beginFallback` needs a buffer swap *and* a write on tape 7.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.LocalTick2

open PalPeg.Program
open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (Counter)
open PalPeg.LocalCounter (Seg)
open PalPeg.LocalInputView (InputView absHead cells pos)
open PalPeg.LocalState

variable {P : ℕ}

/-! ## 1. Two-step locality -/

/-- A commit that needs two local ticks. -/
def StepLocal2 (x y : GalilVML P) : Prop := ∃ m : GalilVML P, StepLocal x m ∧ StepLocal m y

theorem stepLocal2_of_stepLocal {x y : GalilVML P} (h : StepLocal x y) : StepLocal2 x y :=
  ⟨y, h, stepLocal_refl y⟩

/-! ## 2. Commit primitives

Three O(1) acts, each with its effect on `absCtrs` and its `StepLocal` proof. -/

/-- **Repoint** a logical counter at a physical tape that already holds the
value, with a chosen sign bit.  Pure finite control: no tape moves. -/
def setRole (c : Ctr) (j : Fin P) (b : Bool) (x : GalilVML P) : GalilVML P :=
  { x with roles := Function.update x.roles c j, pol := Function.update x.pol c b }

@[simp] theorem setRole_phys (c : Ctr) (j : Fin P) (b : Bool) (x : GalilVML P) :
    (setRole c j b x).phys = x.phys := rfl

theorem absCtrs_setRole (c : Ctr) (j : Fin P) (b : Bool) (x : GalilVML P) :
    absCtrs (setRole c j b x)
      = Function.update (absCtrs x) c (LocalCounter.absCtr (x.phys j) b) := by
  funext d
  by_cases h : d = c
  · subst h; simp [absCtrs, LocalRoles.absL, setRole]
  · simp [absCtrs, LocalRoles.absL, setRole, Function.update_of_ne h]

theorem stepLocal_setRole (c : Ctr) (j : Fin P) (b : Bool) (x : GalilVML P) :
    StepLocal x (setRole c j b x) := stepLocal_refl x

/-- **Reset** the physical tapes in `l`, one `resetSeg` action each. -/
def resetSlots (l : List (Fin P)) (ph : Fin P → STape Seg) : Fin P → STape Seg :=
  fun j => if j ∈ l then LocalCounter.resetSeg (ph j) else ph j

theorem resetSlots_mem {l : List (Fin P)} {ph : Fin P → STape Seg} {j : Fin P} (h : j ∈ l) :
    resetSlots l ph j = LocalCounter.resetSeg (ph j) := by simp [resetSlots, h]

theorem resetSlots_not_mem {l : List (Fin P)} {ph : Fin P → STape Seg} {j : Fin P} (h : j ∉ l) :
    resetSlots l ph j = ph j := by simp [resetSlots, h]

theorem tapeLocal_resetSlots (l : List (Fin P)) (ph : Fin P → STape Seg) (j : Fin P) :
    TapeLocal (ph j) (resetSlots l ph j) := by
  by_cases h : j ∈ l
  · rw [resetSlots_mem h]; exact tapeLocal_resetSeg _
  · rw [resetSlots_not_mem h]; exact tapeLocal_refl _

/-- **Push** on the physical tapes in `l`, one `push` action each. -/
def pushSlots (l : List (Fin P)) (ph : Fin P → STape Seg) : Fin P → STape Seg :=
  fun j => if j ∈ l then LocalCounter.push (ph j) else ph j

theorem pushSlots_mem {l : List (Fin P)} {ph : Fin P → STape Seg} {j : Fin P} (h : j ∈ l) :
    pushSlots l ph j = LocalCounter.push (ph j) := by simp [pushSlots, h]

theorem pushSlots_not_mem {l : List (Fin P)} {ph : Fin P → STape Seg} {j : Fin P} (h : j ∉ l) :
    pushSlots l ph j = ph j := by simp [pushSlots, h]

theorem tapeLocal_pushSlots (l : List (Fin P)) (ph : Fin P → STape Seg) (j : Fin P) :
    TapeLocal (ph j) (pushSlots l ph j) := by
  by_cases h : j ∈ l
  · rw [pushSlots_mem h]; exact tapeLocal_push _
  · rw [pushSlots_not_mem h]; exact tapeLocal_refl _

/-- A whole state whose only tape motion is `resetSlots` is one local step. -/
theorem stepLocal_resetSlots (x : GalilVML P) (l : List (Fin P)) (y : GalilVML P)
    (hp : y.phys = resetSlots l x.phys)
    (hm : y.radiusMir = x.radiusMir) (hm' : y.lowerMir = x.lowerMir)
    (hm'' : y.lengthMir = x.lengthMir)
    (h1 : y.left = x.left) (h2 : y.center = x.center) (h3 : y.right = x.right)
    (h4 : y.walkerView = x.walkerView) (h5 : y.fppWalker = x.fppWalker)
    (h6 : y.dpBuf = x.dpBuf) (h7 : y.fppBuf = x.fppBuf) : StepLocal x y := by
  refine ⟨fun j => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [hp, hm, hm', hm'', h1, h2, h3, h4, h5, h6, h7]
  · exact tapeLocal_resetSlots l x.phys j
  · exact ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩
  · exact ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩
  · exact ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩
  all_goals first
    | exact viewLocal_refl _
    | exact bufLocal_refl _

/-! ## 3. The head copies as stuttering repositioning jobs

`replayStartVM` asks for `right := center` and `left := center`, `beginFallback`
for `walker := p`.  No cursor is ever copied: each cursor walks its *own*
maintained copy of the input to the target position, one cell per tick, and the
commit only has to find it already there.  These are the `stutter` steps: they
move exactly one view and leave every other component of `abs` alone. -/

/-- Two views holding the same content, standing at the same place, have the
same abstract head. -/
theorem absHead_congr {v w : InputView} (hc : cells v = cells w) (hp : pos v = pos w)
    (hg : v.gap = w.gap) (q : List (Fin 2)) : absHead v q = absHead w q := by
  have hlen : v.back.reverse.length = w.back.reverse.length := by
    simpa [LocalInputView.pos] using hp
  obtain ⟨hb, ht⟩ := List.append_inj hc hlen
  have hback : v.back = w.back := by
    have := congrArg List.reverse hb; simpa using this
  have hfocus : v.focus = w.focus := (List.cons.inj ht).1
  have hright : LocalInputView.absRight v = LocalInputView.absRight w := (List.cons.inj ht).2
  simp only [LocalInputView.absHead, hback, hfocus, hright, hg]

/-- The `abs`-level reading: a view repositioned onto another view's place, with
the same content, abstracts to the same head. -/
theorem abs_right_of_repositioned {x : GalilVML P}
    (hc : cells x.right = cells x.center) (hp : pos x.right = pos x.center)
    (hg : x.right.gap = x.center.gap) : (abs x).right = (abs x).center :=
  absHead_congr hc hp hg x.pending

theorem abs_left_of_repositioned {x : GalilVML P}
    (hc : cells x.left = cells x.center) (hp : pos x.left = pos x.center)
    (hg : x.left.gap = x.center.gap) : (abs x).left = (abs x).center :=
  absHead_congr hc hp hg x.pending

/-! ### A chain of `n` local ticks -/

/-- `n` consecutive local steps. -/
def StepLocalN : ℕ → GalilVML P → GalilVML P → Prop
  | 0, x, y => y = x
  | n + 1, x, y => ∃ m : GalilVML P, StepLocal x m ∧ StepLocalN n m y

theorem stepLocalN_refl (x : GalilVML P) : StepLocalN 0 x x := rfl

/-! ### The three repositioning jobs -/

/-- `n` micro-steps of the job that walks `right` to `target`. -/
def repRight (target : ℕ) : ℕ → GalilVML P → GalilVML P
  | 0, x => x
  | n + 1, x => repRight target n { x with right := LocalInputView.repositionStep target x.right }

def repLeft (target : ℕ) : ℕ → GalilVML P → GalilVML P
  | 0, x => x
  | n + 1, x => repLeft target n { x with left := LocalInputView.repositionStep target x.left }

def repFppWalker (target : ℕ) : ℕ → GalilVML P → GalilVML P
  | 0, x => x
  | n + 1, x =>
    repFppWalker target n { x with fppWalker := LocalInputView.repositionStep target x.fppWalker }

theorem repRight_eq (target : ℕ) :
    ∀ (n : ℕ) (x : GalilVML P),
      repRight target n x = { x with right := LocalInputView.reposition target n x.right } := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih => intro x; rw [repRight, ih]; rfl

theorem repLeft_eq (target : ℕ) :
    ∀ (n : ℕ) (x : GalilVML P),
      repLeft target n x = { x with left := LocalInputView.reposition target n x.left } := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih => intro x; rw [repLeft, ih]; rfl

theorem repFppWalker_eq (target : ℕ) :
    ∀ (n : ℕ) (x : GalilVML P),
      repFppWalker target n x
        = { x with fppWalker := LocalInputView.reposition target n x.fppWalker } := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih => intro x; rw [repFppWalker, ih]; rfl

theorem stepLocal_repRightStep (target : ℕ) (x : GalilVML P) :
    StepLocal x { x with right := LocalInputView.repositionStep target x.right } :=
  ⟨fun _ => tapeLocal_refl _, ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
    ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
    ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
    viewLocal_refl _, viewLocal_refl _, viewLocal_repositionStep target _,
    viewLocal_refl _, viewLocal_refl _, bufLocal_refl _, bufLocal_refl _⟩

theorem stepLocal_repLeftStep (target : ℕ) (x : GalilVML P) :
    StepLocal x { x with left := LocalInputView.repositionStep target x.left } :=
  ⟨fun _ => tapeLocal_refl _, ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
    ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
    ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
    viewLocal_repositionStep target _, viewLocal_refl _, viewLocal_refl _,
    viewLocal_refl _, viewLocal_refl _, bufLocal_refl _, bufLocal_refl _⟩

theorem stepLocal_repFppWalkerStep (target : ℕ) (x : GalilVML P) :
    StepLocal x { x with fppWalker := LocalInputView.repositionStep target x.fppWalker } :=
  ⟨fun _ => tapeLocal_refl _, ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
    ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
    ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
    viewLocal_refl _, viewLocal_refl _, viewLocal_refl _,
    viewLocal_refl _, viewLocal_repositionStep target _, bufLocal_refl _, bufLocal_refl _⟩

theorem stepLocalN_repRight (target : ℕ) :
    ∀ (n : ℕ) (x : GalilVML P), StepLocalN n x (repRight target n x) := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih => intro x; exact ⟨_, stepLocal_repRightStep target x, ih _⟩

theorem stepLocalN_repLeft (target : ℕ) :
    ∀ (n : ℕ) (x : GalilVML P), StepLocalN n x (repLeft target n x) := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih => intro x; exact ⟨_, stepLocal_repLeftStep target x, ih _⟩

theorem stepLocalN_repFppWalker (target : ℕ) :
    ∀ (n : ℕ) (x : GalilVML P), StepLocalN n x (repFppWalker target n x) := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih => intro x; exact ⟨_, stepLocal_repFppWalkerStep target x, ih _⟩

/-! ### The job is invisible to everything but its own view -/

theorem abs_repRight (target n : ℕ) (x : GalilVML P) :
    abs (repRight target n x)
      = { abs x with right := absHead (LocalInputView.reposition target n x.right) x.pending } := by
  rw [repRight_eq]; rfl

theorem abs_repLeft (target n : ℕ) (x : GalilVML P) :
    abs (repLeft target n x)
      = { abs x with left := absHead (LocalInputView.reposition target n x.left) x.pending } := by
  rw [repLeft_eq]; rfl

theorem abs_repFppWalker (target n : ℕ) (x : GalilVML P) :
    abs (repFppWalker target n x)
      = { abs x with
          fpp := { (abs x).fpp with
                   walker := absPlace (LocalInputView.reposition target n x.fppWalker) } } := by
  rw [repFppWalker_eq]; rfl

/-! ### The job terminates on time -/

/-- After `repDist` micro-steps the `right` cursor stands where `center` stands,
with its content and gap untouched; hence `(abs ·).right = (abs ·).center`.
This is the hypothesis `commitReplay` consumes. -/
theorem repRight_reaches {x : GalilVML P} (hw : LocalInputView.WF x.right)
    (hc : cells x.right = cells x.center) (hg : x.right.gap = x.center.gap)
    (hcap : pos x.center ≤ pos x.right + (LocalInputView.absRight x.right).length) :
    let y := repRight (pos x.center) (LocalInputView.repDist (pos x.right) (pos x.center)) x
    (abs y).right = (abs y).center := by
  intro y
  obtain ⟨h1, h2, _, h4⟩ :=
    LocalInputView.reposition_reaches (pos x.center)
      (LocalInputView.repDist (pos x.right) (pos x.center)) x.right hw rfl hcap
  have hy : y = { x with right := _ } := repRight_eq _ _ x
  refine abs_right_of_repositioned (x := y) ?_ ?_ ?_
  · rw [hy]; exact h2.trans hc
  · rw [hy]; exact h1
  · rw [hy]; exact h4.trans hg

/-! ## 4. `restartVM entry`: the Broken-chain restart

```
t = { s with chain := .idle, lower := last,
             search := SearchFinish.begin last s.radius,
             dp := GalilScaffoldControl.reset entry s.dp }
```
with `begin last radius = ⟨.grow, false, reset, max last 1, initialDebt radius, 0⟩`.

Four non-local effects, four O(1) acts:

* `lower := last` — repoint `.lower` at the tape `jL` on which the chain has
  staged `last` (the chain component is still abstract: *which* tape that is, is
  hypothesis `lowerSrc`);
* `work := max last 1` — a copy of a counter that stays alive, so it comes off
  the **lower mirror**, whose source is `jL`;
* `debt := initialDebt radius` — a copy of the live `radius` with the sign
  flipped, so it comes off the **radius mirror** with `!pol .radius`;
* `span := reset` — one `resetSeg` on the span tape;
* `dp := reset entry` — one `resetL` on the DP double buffer, the erasure job on
  its idle half having finished (`clean`).
-/

/-- Everything `commitRestart` needs of the state it fires in. -/
structure RestartStaged (x : GalilVML P) (jL jW jD : Fin P) (iW : Fin 1) (iD : Fin 2) : Prop where
  /-- Distinct logical counters sit on distinct tapes. -/
  inj : RolesInjective x
  /-- The chain has staged the new lower bound on `jL`, with the lower mirror
  bank already attached to it and synchronized. -/
  lowerSrc : x.lowerMir.src = x.phys jL
  lowerSyn : LocalMirror.Synced x.lowerMir
  workSlot : x.phys jW = x.lowerMir.mir iW
  /-- The radius mirror bank is attached to the live `radius` and synchronized. -/
  radSrc : x.radiusMir.src = x.phys (x.roles .radius)
  radSyn : LocalMirror.Synced x.radiusMir
  debtSlot : x.phys jD = x.radiusMir.mir iD
  /-- The three staged tapes are not the span tape that this tick resets. -/
  freshL : jL ≠ x.roles .span
  freshW : jW ≠ x.roles .span
  freshD : jD ≠ x.roles .span
  /-- The DP buffer's idle half has been erased by the background job. -/
  clean : ∀ i, LocalBuffers.Cleared (LocalBuffers.idle x.dpBuf i)

/-- The commit realizing `restartVM entry`. -/
def commitRestart (entry : ℕ) (jL jW jD : Fin P) (bL : Bool) (x : GalilVML P) : GalilVML P :=
  setRole .debt jD (!x.pol .radius) (setRole .work jW bL (setRole .lower jL bL
    { x with phys := resetSlots [x.roles .span] x.phys
             chain := .idle
             searchMode := .grow
             searchFinalStage := false
             searchQuarter := 0
             dpBuf := LocalBuffers.resetL x.dpBuf
             dpPc := entry
             dpDone := true }))

theorem stepLocal_commitRestart (entry : ℕ) (jL jW jD : Fin P) (bL : Bool) (x : GalilVML P) :
    StepLocal x (commitRestart entry jL jW jD bL x) := by
  refine ⟨fun j => ?_, ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
    ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
    ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
    viewLocal_refl _, viewLocal_refl _, viewLocal_refl _, viewLocal_refl _, viewLocal_refl _,
    bufLocal_resetL _, bufLocal_refl _⟩
  exact tapeLocal_resetSlots _ _ j

theorem stepLocal2_commitRestart (entry : ℕ) (jL jW jD : Fin P) (bL : Bool) (x : GalilVML P) :
    StepLocal2 x (commitRestart entry jL jW jD bL x) :=
  stepLocal2_of_stepLocal (stepLocal_commitRestart entry jL jW jD bL x)

section RestartAbs

variable {x : GalilVML P} {jL jW jD : Fin P} {iW : Fin 1} {iD : Fin 2} {bL : Bool} {entry : ℕ}

/-- Counters neither reset nor repointed by the commit keep their value. -/
theorem absCtrs_commitRestart_other (h : RestartStaged x jL jW jD iW iD) (c : Ctr)
    (h1 : c ≠ Ctr.span) (h2 : c ≠ Ctr.lower) (h3 : c ≠ Ctr.work) (h4 : c ≠ Ctr.debt) :
    absCtrs (commitRestart entry jL jW jD bL x) c = absCtrs x c := by
  simp only [absCtrs_apply, commitRestart, setRole]
  rw [Function.update_of_ne h4, Function.update_of_ne h3, Function.update_of_ne h2,
    Function.update_of_ne h4, Function.update_of_ne h3, Function.update_of_ne h2,
    resetSlots_not_mem (by simpa using fun hh => h1 (h.inj hh))]

theorem absCtrs_commitRestart_span (x : GalilVML P) (jL jW jD : Fin P) (bL : Bool) (entry : ℕ) :
    absCtrs (commitRestart entry jL jW jD bL x) Ctr.span = GalilScaffoldCounter.reset := by
  simp only [absCtrs_apply, commitRestart, setRole]
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
    Function.update_of_ne (by decide), resetSlots_mem (by simp)]
  exact LocalCounter.absCtr_reset _ _

theorem absCtrs_commitRestart_lower (h : RestartStaged x jL jW jD iW iD) :
    absCtrs (commitRestart entry jL jW jD bL x) Ctr.lower
      = LocalCounter.absCtr (x.phys jL) bL := by
  simp only [absCtrs_apply, commitRestart, setRole]
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
    Function.update_self, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
    Function.update_self, resetSlots_not_mem (by simpa using h.freshL)]

/-- The `work := max lower 1` copy comes off the **lower mirror**. -/
theorem absCtrs_commitRestart_work (h : RestartStaged x jL jW jD iW iD) :
    absCtrs (commitRestart entry jL jW jD bL x) Ctr.work
      = LocalCounter.absCtr (x.phys jL) bL := by
  simp only [absCtrs_apply, commitRestart, setRole]
  rw [Function.update_of_ne (by decide), Function.update_self,
    Function.update_of_ne (by decide), Function.update_self,
    resetSlots_not_mem (by simpa using h.freshW), h.workSlot,
    LocalMirror.absCtr_mirror h.lowerSyn, h.lowerSrc]

/-- The `debt := initialDebt radius` copy comes off the **radius mirror**, with
the polarity bit flipped. -/
theorem absCtrs_commitRestart_debt (h : RestartStaged x jL jW jD iW iD) :
    absCtrs (commitRestart entry jL jW jD bL x) Ctr.debt
      = GalilScaffoldSearchFinish.initialDebt (LocalState.abs x).radius := by
  simp only [absCtrs_apply, commitRestart, setRole]
  rw [Function.update_self, Function.update_self,
    resetSlots_not_mem (by simpa using h.freshD), h.debtSlot]
  show LocalCounter.absCtr (LocalMirror.take x.radiusMir iD) (!x.pol Ctr.radius) = _
  rw [LocalMirror.negate_via_pol h.radSyn iD (x.pol Ctr.radius), h.radSrc]
  rfl

/-- **The restart commit realizes `restartVM entry`'s effect on the VM.** -/
theorem abs_commitRestart (h : RestartStaged x jL jW jD iW iD)
    (hpos : GalilScaffoldCounter.positive (LocalCounter.absCtr (x.phys jL) bL) = true) :
    LocalState.abs (commitRestart entry jL jW jD bL x)
      = { LocalState.abs x with
          chain := .idle
          lower := LocalCounter.absCtr (x.phys jL) bL
          search := GalilScaffoldSearchFinish.begin (LocalCounter.absCtr (x.phys jL) bL)
                      (LocalState.abs x).radius
          dp := GalilScaffoldControl.reset entry (LocalState.abs x).dp } := by
  have hz : GalilScaffoldCounter.zero (LocalCounter.absCtr (x.phys jL) bL) = false := by
    revert hpos
    cases hb : (LocalCounter.absCtr (x.phys jL) bL).pos <;>
      simp [GalilScaffoldCounter.positive, GalilScaffoldCounter.zero, hb]
  have hdp : LocalBuffers.abs (LocalBuffers.resetL x.dpBuf) = fun _ => GalilScaffoldTape.reset :=
    LocalBuffers.abs_resetL_of_clean h.clean
  simp only [LocalState.abs, GalilScaffoldSearchFinish.begin, GalilScaffoldControl.reset, hz,
    absCtrs_commitRestart_other h Ctr.cycle (by decide) (by decide) (by decide) (by decide),
    absCtrs_commitRestart_other h Ctr.remaining (by decide) (by decide) (by decide) (by decide),
    absCtrs_commitRestart_other h Ctr.radius (by decide) (by decide) (by decide) (by decide),
    absCtrs_commitRestart_other h Ctr.length (by decide) (by decide) (by decide) (by decide),
    absCtrs_commitRestart_other h Ctr.replay (by decide) (by decide) (by decide) (by decide),
    absCtrs_commitRestart_other h Ctr.fppWork (by decide) (by decide) (by decide) (by decide),
    absCtrs_commitRestart_span x jL jW jD bL entry, absCtrs_commitRestart_lower h,
    absCtrs_commitRestart_work h, absCtrs_commitRestart_debt h]
  show (_ : GalilVM) = _
  simp only [commitRestart, setRole, hdp]
  rfl

end RestartAbs

/-- `commitRestart` really is a `restartVM` transition of the scaffold VM. -/
theorem restartVM_commitRestart {x : GalilVML P} {jL jW jD : Fin P} {iW : Fin 1} {iD : Fin 2}
    {bL : Bool} {entry : ℕ} (h : RestartStaged x jL jW jD iW iD)
    (w : GalilScaffoldChainWatch.State) (hchain : x.chain = .broken w)
    (hmargin : GalilScaffoldCounter.negative w.margin = false)
    (hlast : GalilScaffoldCounter.positive w.machine.control.last = true)
    (hlag : GalilScaffoldCounter.zero w.lag = true)
    (hval : LocalCounter.absCtr (x.phys jL) bL = w.machine.control.last) :
    restartVM entry (LocalState.abs x) (LocalState.abs (commitRestart entry jL jW jD bL x)) := by
  refine ⟨w, hchain, hmargin, hlast, hlag, ?_⟩
  rw [abs_commitRestart h (by rw [hval]; exact hlast), hval]

/-! ## 5. Slot bookkeeping by logical counter -/

/-- The physical slots of a list of logical counters. -/
def ctrSlots (l : List Ctr) (x : GalilVML P) : List (Fin P) := l.map x.roles

theorem roles_mem_ctrSlots {l : List Ctr} {c : Ctr} (x : GalilVML P) (h : c ∈ l) :
    x.roles c ∈ ctrSlots l x := List.mem_map_of_mem h

theorem roles_not_mem_ctrSlots {l : List Ctr} {c : Ctr} {x : GalilVML P}
    (hinj : RolesInjective x) (h : c ∉ l) : x.roles c ∉ ctrSlots l x := by
  simp only [ctrSlots, List.mem_map, not_exists, not_and]
  intro d hd he
  exact h (hinj he ▸ hd)

/-! ## 6. `replayStartVM entry`: the fallback exit to scan

```
t.replay = s.radius,  t.radius = reset,  t.length = ofNat 1,
t.right = t.left = t.center = s.center,  t.chain = .idle,
t.search = begin reset reset,  t.lower = reset,  t.dp = reset entry s.dp
```

`replay := radius` with `radius := reset` is a **role move**: the radius tape is
handed over to `replay` and the dead replay tape is `resetSeg`ed into the radius
role.  `length := 1` and `search.work = inc reset = 1` are `resetSeg` followed by
`push` — the only place two ticks are needed.  The three head copies are *not*
copies: they are the stuttering repositioning jobs of §3, consumed here as the
hypotheses `hright`/`hleft`. -/

/-- The counters this commit clears (the replay role's dead tape included). -/
def replayCleared : List Ctr :=
  [Ctr.replay, Ctr.length, Ctr.span, Ctr.work, Ctr.debt, Ctr.lower]

/-- The commit realizing `replayStartVM entry`; two local ticks. -/
def commitReplay (entry : ℕ) (x : GalilVML P) : GalilVML P :=
  { x with
    phys := pushSlots [x.roles Ctr.length, x.roles Ctr.work]
              (resetSlots (ctrSlots replayCleared x) x.phys)
    roles := LocalRoles.moveRoles Ctr.radius Ctr.replay x.roles
    -- `length` and `work` are cleared and pushed: they restart on the positive side, as in
    -- `LocalInitStep.initVml`
    pol := fun c => if c = Ctr.length ∨ c = Ctr.work then true
      else LocalRoles.movePol Ctr.radius Ctr.replay x.pol c
    chain := .idle
    searchMode := .grow
    searchFinalStage := false
    searchQuarter := 0
    dpBuf := LocalBuffers.resetFresh x.dpBuf
    dpPc := entry
    dpDone := true }

section ReplayAbs

variable {x : GalilVML P} {entry : ℕ}

private theorem replay_push_not_mem (hinj : RolesInjective x) {c : Ctr}
    (h4 : c ≠ Ctr.length) (h5 : c ≠ Ctr.work) :
    x.roles c ∉ [x.roles Ctr.length, x.roles Ctr.work] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨fun hh => h4 (hinj hh), fun hh => h5 (hinj hh)⟩

theorem absCtrs_commitReplay_stable (hinj : RolesInjective x) (c : Ctr)
    (h1 : c ≠ Ctr.radius) (h2 : c ≠ Ctr.replay) (h3 : c ∉ replayCleared)
    (h4 : c ≠ Ctr.length) (h5 : c ≠ Ctr.work) :
    absCtrs (commitReplay entry x) c = absCtrs x c := by
  simp only [absCtrs_apply, commitReplay, LocalRoles.moveRoles, LocalRoles.movePol,
    LocalRoles.swapAt_other h2 h1, if_neg (not_or.mpr ⟨h4, h5⟩)]
  rw [pushSlots_not_mem (replay_push_not_mem hinj h4 h5),
    resetSlots_not_mem (roles_not_mem_ctrSlots hinj h3)]

theorem absCtrs_commitReplay_radius (hinj : RolesInjective x) :
    absCtrs (commitReplay entry x) Ctr.radius = GalilScaffoldCounter.reset := by
  simp only [absCtrs_apply, commitReplay, LocalRoles.moveRoles, LocalRoles.movePol,
    LocalRoles.swapAt_src (by decide : (Ctr.radius : Ctr) ≠ Ctr.replay)]
  rw [pushSlots_not_mem (replay_push_not_mem hinj (by decide) (by decide)),
    resetSlots_mem (roles_mem_ctrSlots x (by decide : Ctr.replay ∈ replayCleared))]
  exact LocalCounter.absCtr_reset _ _

theorem absCtrs_commitReplay_replay (hinj : RolesInjective x) :
    absCtrs (commitReplay entry x) Ctr.replay = absCtrs x Ctr.radius := by
  simp only [absCtrs_apply, commitReplay, LocalRoles.moveRoles, LocalRoles.movePol,
    LocalRoles.swapAt_dst,
    if_neg (by decide : ¬ ((Ctr.replay : Ctr) = Ctr.length ∨ (Ctr.replay : Ctr) = Ctr.work))]
  rw [pushSlots_not_mem (replay_push_not_mem hinj (by decide) (by decide)),
    resetSlots_not_mem (roles_not_mem_ctrSlots hinj (by decide : Ctr.radius ∉ replayCleared))]

theorem absCtrs_commitReplay_cleared (hinj : RolesInjective x) (c : Ctr)
    (h1 : c ≠ Ctr.radius) (h2 : c ≠ Ctr.replay) (h3 : c ∈ replayCleared)
    (h4 : c ≠ Ctr.length) (h5 : c ≠ Ctr.work) :
    absCtrs (commitReplay entry x) c = GalilScaffoldCounter.reset := by
  simp only [absCtrs_apply, commitReplay, LocalRoles.moveRoles, LocalRoles.movePol,
    LocalRoles.swapAt_other h2 h1]
  rw [pushSlots_not_mem (replay_push_not_mem hinj h4 h5),
    resetSlots_mem (roles_mem_ctrSlots x h3)]
  exact LocalCounter.absCtr_reset _ _

/-- `resetSeg` then `push` on a nonnegative counter tape is the literal `1`. -/
theorem absCtr_push_reset (t : STape Seg) :
    LocalCounter.absCtr (LocalCounter.push (LocalCounter.resetSeg t)) true
      = GalilScaffoldCounter.ofNat 1 := by
  rw [LocalCounter.absCtr_push, if_pos rfl, LocalCounter.absCtr_reset]
  rfl

theorem absCtrs_commitReplay_one (c : Ctr)
    (h3 : c ∈ replayCleared) (h6 : c = Ctr.length ∨ c = Ctr.work) :
    absCtrs (commitReplay entry x) c = GalilScaffoldCounter.ofNat 1 := by
  have h1 : c ≠ Ctr.radius := by rcases h6 with h | h <;> simp [h]
  have h2 : c ≠ Ctr.replay := by rcases h6 with h | h <;> simp [h]
  have hmem : x.roles c ∈ [x.roles Ctr.length, x.roles Ctr.work] := by
    rcases h6 with h | h <;> simp [h]
  simp only [absCtrs_apply, commitReplay, LocalRoles.moveRoles, LocalRoles.movePol,
    LocalRoles.swapAt_other h2 h1, if_pos h6]
  rw [pushSlots_mem hmem, resetSlots_mem (roles_mem_ctrSlots x h3)]
  exact absCtr_push_reset _

/-- **The replay-start commit realizes `replayStartVM entry`'s effect.** -/
theorem abs_commitReplay (hinj : RolesInjective x) :
    LocalState.abs (commitReplay entry x)
      = { LocalState.abs x with
          replay := (LocalState.abs x).radius
          radius := GalilScaffoldCounter.reset
          length := GalilScaffoldCounter.ofNat 1
          chain := .idle
          search := GalilScaffoldSearchFinish.begin GalilScaffoldCounter.reset
                      GalilScaffoldCounter.reset
          lower := GalilScaffoldCounter.reset
          dp := GalilScaffoldControl.reset entry (LocalState.abs x).dp } := by
  have hdp : LocalBuffers.abs (LocalBuffers.resetFresh x.dpBuf)
      = fun _ => GalilScaffoldTape.reset := LocalBuffers.abs_resetFresh _
  simp only [LocalState.abs, GalilScaffoldSearchFinish.begin, GalilScaffoldControl.reset,
    GalilScaffoldSearchFinish.initialDebt,
    absCtrs_commitReplay_stable hinj Ctr.cycle (by decide) (by decide) (by decide)
      (by decide) (by decide),
    absCtrs_commitReplay_stable hinj Ctr.remaining (by decide) (by decide) (by decide)
      (by decide) (by decide),
    absCtrs_commitReplay_stable hinj Ctr.fppWork (by decide) (by decide) (by decide)
      (by decide) (by decide),
    absCtrs_commitReplay_radius hinj, absCtrs_commitReplay_replay hinj,
    absCtrs_commitReplay_cleared hinj Ctr.span (by decide) (by decide) (by decide)
      (by decide) (by decide),
    absCtrs_commitReplay_cleared hinj Ctr.debt (by decide) (by decide) (by decide)
      (by decide) (by decide),
    absCtrs_commitReplay_cleared hinj Ctr.lower (by decide) (by decide) (by decide)
      (by decide) (by decide),
    absCtrs_commitReplay_one Ctr.length (by decide) (by decide),
    absCtrs_commitReplay_one Ctr.work (by decide) (by decide)]
  show (_ : GalilVM) = _
  simp only [commitReplay, hdp]
  rfl

/-- …and it is a `replayStartVM` transition, once the two head-copy jobs of §3
have brought `right` and `left` onto `center`. -/
theorem replayStartVM_commitReplay (hinj : RolesInjective x)
    (hright : (LocalState.abs x).right = (LocalState.abs x).center)
    (hleft : (LocalState.abs x).left = (LocalState.abs x).center) :
    replayStartVM entry (LocalState.abs x) (LocalState.abs (commitReplay entry x)) := by
  rw [abs_commitReplay hinj]
  exact ⟨rfl, hright, hleft, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end ReplayAbs

/-! ## 7. `beginShiftVM h w`: entering a chain shift

```
t = {s with remaining := ofNat h, length := inc (inc s.length),
            chain := .watch (immediate w), cycle := reset, periodOnly := true}
```

`length` gains two units, so two `push`es on its tape: this is the second place
where a commit needs two ticks.  `cycle := reset` is one `resetSeg`.
`remaining := ofNat h` is a repoint onto a tape the chain has staged with the
period length — `h = periodLength w` lives in the still-abstract chain
component, so *which* tape that is stays a hypothesis (`shiftSlot`). -/

theorem tapeLocal_push_reset {rl rc : Fin P} (hne : rl ≠ rc) (ph : Fin P → STape Seg)
    (j : Fin P) : TapeLocal (ph j) (pushSlots [rl] (resetSlots [rc] ph) j) := by
  by_cases h : j = rl
  · subst h
    rw [pushSlots_mem (by simp), resetSlots_not_mem (by simpa using hne)]
    exact tapeLocal_push _
  · rw [pushSlots_not_mem (by simpa using h)]
    exact tapeLocal_resetSlots _ _ j

/-- The commit realizing `beginShiftVM h w`; two local ticks. -/
def commitShift (jR : Fin P) (bR : Bool) (w : GalilScaffoldChainWatch.State) (x : GalilVML P) :
    GalilVML P :=
  setRole Ctr.remaining jR bR
    { x with phys := pushSlots [x.roles Ctr.length]
                       (pushSlots [x.roles Ctr.length] (resetSlots [x.roles Ctr.cycle] x.phys))
             chain := .watch (GalilScaffoldChainWatch.immediate w)
             periodOnly := true }

theorem stepLocal2_commitShift {x : GalilVML P} (hinj : RolesInjective x)
    (jR : Fin P) (bR : Bool) (w : GalilScaffoldChainWatch.State) :
    StepLocal2 x (commitShift jR bR w x) := by
  have hne : x.roles Ctr.length ≠ x.roles Ctr.cycle := fun hh => by
    have := hinj hh; exact absurd this (by decide)
  refine ⟨{ x with phys := pushSlots [x.roles Ctr.length] (resetSlots [x.roles Ctr.cycle] x.phys)
                   chain := .watch (GalilScaffoldChainWatch.immediate w)
                   periodOnly := true }, ?_, ?_⟩
  · exact ⟨fun j => tapeLocal_push_reset hne x.phys j,
      ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
      ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
      ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
      viewLocal_refl _, viewLocal_refl _, viewLocal_refl _, viewLocal_refl _, viewLocal_refl _,
      bufLocal_refl _, bufLocal_refl _⟩
  · exact ⟨fun j => tapeLocal_pushSlots _ _ j,
      ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
      ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
      ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
      viewLocal_refl _, viewLocal_refl _, viewLocal_refl _, viewLocal_refl _, viewLocal_refl _,
      bufLocal_refl _, bufLocal_refl _⟩

section ShiftAbs

variable {x : GalilVML P} {jR : Fin P} {bR : Bool} {w : GalilScaffoldChainWatch.State}

private theorem shift_phys_stable (hinj : RolesInjective x) {c : Ctr}
    (h1 : c ≠ Ctr.length) (h2 : c ≠ Ctr.cycle) :
    pushSlots [x.roles Ctr.length]
        (pushSlots [x.roles Ctr.length] (resetSlots [x.roles Ctr.cycle] x.phys)) (x.roles c)
      = x.phys (x.roles c) := by
  have e1 : x.roles c ∉ [x.roles Ctr.length] := by
    simpa using fun hh => h1 (hinj hh)
  have e2 : x.roles c ∉ [x.roles Ctr.cycle] := by
    simpa using fun hh => h2 (hinj hh)
  rw [pushSlots_not_mem e1, pushSlots_not_mem e1, resetSlots_not_mem e2]

theorem absCtrs_commitShift_stable (hinj : RolesInjective x) (c : Ctr)
    (h0 : c ≠ Ctr.remaining) (h1 : c ≠ Ctr.length) (h2 : c ≠ Ctr.cycle) :
    absCtrs (commitShift jR bR w x) c = absCtrs x c := by
  simp only [absCtrs_apply, commitShift, setRole, Function.update_of_ne h0]
  rw [shift_phys_stable hinj h1 h2]

theorem absCtrs_commitShift_cycle (hinj : RolesInjective x) :
    absCtrs (commitShift jR bR w x) Ctr.cycle = GalilScaffoldCounter.reset := by
  have e1 : x.roles Ctr.cycle ∉ [x.roles Ctr.length] := by
    simpa using fun hh => (by decide : (Ctr.cycle : Ctr) ≠ Ctr.length) (hinj hh)
  simp only [absCtrs_apply, commitShift, setRole, Function.update_of_ne (by decide : (Ctr.cycle : Ctr) ≠ Ctr.remaining)]
  rw [pushSlots_not_mem e1, pushSlots_not_mem e1, resetSlots_mem (by simp)]
  exact LocalCounter.absCtr_reset _ _

theorem absCtrs_commitShift_length (hinj : RolesInjective x) (hp : x.pol Ctr.length = true) :
    absCtrs (commitShift jR bR w x) Ctr.length
      = GalilScaffoldCounter.inc (GalilScaffoldCounter.inc (absCtrs x Ctr.length)) := by
  have e2 : x.roles Ctr.length ∉ [x.roles Ctr.cycle] := by
    simpa using fun hh => (by decide : (Ctr.length : Ctr) ≠ Ctr.cycle) (hinj hh)
  simp only [absCtrs_apply, commitShift, setRole,
    Function.update_of_ne (by decide : (Ctr.length : Ctr) ≠ Ctr.remaining)]
  rw [pushSlots_mem (by simp), pushSlots_mem (by simp), resetSlots_not_mem e2, hp,
    LocalCounter.absCtr_push, if_pos rfl, LocalCounter.absCtr_push, if_pos rfl]

theorem absCtrs_commitShift_remaining
    (hfl : jR ≠ x.roles Ctr.length) (hfc : jR ≠ x.roles Ctr.cycle) :
    absCtrs (commitShift jR bR w x) Ctr.remaining = LocalCounter.absCtr (x.phys jR) bR := by
  simp only [absCtrs_apply, commitShift, setRole, Function.update_self]
  rw [pushSlots_not_mem (by simpa using hfl), pushSlots_not_mem (by simpa using hfl),
    resetSlots_not_mem (by simpa using hfc)]

/-- **The shift commit realizes `beginShiftVM h w`.** -/
theorem beginShiftVM_commitShift {h : ℕ} (hinj : RolesInjective x)
    (hp : x.pol Ctr.length = true)
    (hfl : jR ≠ x.roles Ctr.length) (hfc : jR ≠ x.roles Ctr.cycle)
    (hchain : x.chain = .watch w)
    (hstaged : LocalCounter.absCtr (x.phys jR) bR = GalilScaffoldCounter.ofNat h) :
    beginShiftVM h w (LocalState.abs x) (LocalState.abs (commitShift jR bR w x)) := by
  refine ⟨hchain, ?_⟩
  simp only [LocalState.abs,
    absCtrs_commitShift_stable hinj Ctr.radius (by decide) (by decide) (by decide),
    absCtrs_commitShift_stable hinj Ctr.replay (by decide) (by decide) (by decide),
    absCtrs_commitShift_stable hinj Ctr.span (by decide) (by decide) (by decide),
    absCtrs_commitShift_stable hinj Ctr.work (by decide) (by decide) (by decide),
    absCtrs_commitShift_stable hinj Ctr.debt (by decide) (by decide) (by decide),
    absCtrs_commitShift_stable hinj Ctr.lower (by decide) (by decide) (by decide),
    absCtrs_commitShift_stable hinj Ctr.fppWork (by decide) (by decide) (by decide),
    absCtrs_commitShift_cycle hinj, absCtrs_commitShift_length hinj hp,
    absCtrs_commitShift_remaining hfl hfc, hstaged]
  show (_ : GalilVM) = _
  simp only [commitShift, setRole]

end ShiftAbs

/-! ## 8. `FppControl.beginFallback`: restarting the fpp machine

```
beginFallback old p length =
  { mode := .copy,
    program := { reset 320 old with config := put _ 7 (moveRight (write reset 4)) },
    work := inc length, walker := p, finalStage := false }
```

The program is a whole nine-tape machine wiped *and* one symbol written, so it
is a `resetL` followed by one pointwise program step — the third and last place
where two ticks are needed.  `walker := p` is again a repositioning job on the
fpp cursor (hypothesis `hwalker`).

`work := inc length` is localized by the third mirror bank, `lengthMir`: the
commit *takes* the (eagerly synchronized) length mirror — a control act, zero
cost — and performs **one** `push` on it, which is `inc` on a counter carrying a
positive sign bit (`LocalCounter.absCtr_push`).  Hence no tape holding
`inc length` has to be assumed any more: the hypotheses are just
`MirrorsAttached x`, `Synced x.lengthMir` and the slot equation saying that the
detached mirror is the physical tape `jF` the role is repointed at. -/

/-- The single pointwise write the fpp restart performs on tape 7. -/
def fppWriteAt : Fin 9 → GalilScaffoldTape.Tape → GalilScaffoldTape.Tape :=
  fun i t =>
    if i = 7 then GalilScaffoldTape.moveRight (GalilScaffoldTape.write GalilScaffoldTape.reset 4)
    else t

theorem fppWriteAt_eq_update (ts : Fin 9 → GalilScaffoldTape.Tape) :
    (fun i => fppWriteAt i (ts i))
      = Function.update ts 7
          (GalilScaffoldTape.moveRight (GalilScaffoldTape.write GalilScaffoldTape.reset 4)) := by
  funext i
  by_cases h : i = 7
  · subst h; simp [fppWriteAt]
  · simp [fppWriteAt, h]

/-- The commit realizing `FppControl.beginFallback`; two local ticks.

Tick 1: `resetL` on the fpp buffer *and* the single `push` on tape `jF`, the
length mirror just detached (`work := inc length`).  Tick 2: the pointwise write
on tape 7.  The role repoint is pure finite control. -/
def commitFallback (jF : Fin P) (bF : Bool) (x : GalilVML P) : GalilVML P :=
  setRole Ctr.fppWork jF bF
    { x with phys := pushSlots [jF] x.phys
             fppBuf := LocalBuffers.stepL (fun ts i => fppWriteAt i (ts i))
                         (LocalBuffers.resetL x.fppBuf)
             fppPc := 320
             fppDone := true
             fppMode := .copy
             fppFinalStage := false }

theorem stepLocal2_commitFallback (jF : Fin P) (bF : Bool) (x : GalilVML P) :
    StepLocal2 x (commitFallback jF bF x) := by
  refine ⟨{ x with phys := pushSlots [jF] x.phys
                   fppBuf := LocalBuffers.resetL x.fppBuf
                   fppPc := 320, fppDone := true
                   fppMode := .copy, fppFinalStage := false }, ?_, ?_⟩
  · exact ⟨fun j => tapeLocal_pushSlots [jF] x.phys j,
      ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
      ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
      ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
      viewLocal_refl _, viewLocal_refl _, viewLocal_refl _, viewLocal_refl _, viewLocal_refl _,
      bufLocal_refl _, bufLocal_resetL _⟩
  · exact ⟨fun _ => tapeLocal_refl _, ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
      ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
      ⟨tapeLocal_refl _, fun _ => tapeLocal_refl _⟩,
      viewLocal_refl _, viewLocal_refl _, viewLocal_refl _, viewLocal_refl _, viewLocal_refl _,
      bufLocal_refl _, bufLocal_stepL fppWriteAt _⟩

/-- **The fallback commit realizes `FppControl.beginFallback`.**

`work := inc length` is discharged by the length mirror: `jF` *is* the detached
mirror tape (`hslot`), it carries the value of `length` because the bank is
attached and synchronized (`ha`, `hs`), and the single `push` of `commitFallback`
turns that value into `inc length` because `length` carries a positive sign bit
(`hpol`, `hbF`). -/
theorem abs_commitFallback {x : GalilVML P} {jF : Fin P} {bF : Bool} {iF : Fin 1}
    {p : GalilScaffoldPlace.Place}
    (hclean : ∀ i, LocalBuffers.Cleared (LocalBuffers.idle x.fppBuf i))
    (ha : MirrorsAttached x) (hs : LocalMirror.Synced x.lengthMir)
    (hslot : x.phys jF = x.lengthMir.mir iF)
    (hpol : x.pol Ctr.length = true) (hbF : bF = x.pol Ctr.length)
    (hwalker : absPlace x.fppWalker = p) :
    (LocalState.abs (commitFallback jF bF x)).fpp
      = FppControl.beginFallback (LocalState.abs x).fpp.program p (LocalState.abs x).length := by
  have hbuf : LocalBuffers.abs (LocalBuffers.stepL (fun ts i => fppWriteAt i (ts i))
      (LocalBuffers.resetL x.fppBuf))
      = Function.update (fun _ => GalilScaffoldTape.reset) 7
          (GalilScaffoldTape.moveRight (GalilScaffoldTape.write GalilScaffoldTape.reset 4)) := by
    rw [LocalBuffers.abs_stepL, LocalBuffers.abs_resetL_of_clean hclean]
    exact fppWriteAt_eq_update _
  have hb : bF = true := hbF.trans hpol
  have hval : LocalCounter.absCtr (x.phys jF) true = (LocalState.abs x).length := by
    rw [hslot, ← hpol]
    exact LocalState.abs_length_mirror ha hs iF
  have hw : absCtrs (commitFallback jF bF x) Ctr.fppWork
      = GalilScaffoldCounter.inc (LocalState.abs x).length := by
    simp only [absCtrs_apply, commitFallback, setRole, Function.update_self]
    rw [pushSlots_mem (by simp : jF ∈ [jF]), hb, LocalCounter.absCtr_push]
    simp only [if_true, hval]
  simp only [LocalState.abs, FppControl.beginFallback, GalilScaffoldControl.reset,
    GalilScaffoldLoading.put, hw]
  show (_ : FppControl.State) = _
  simp only [commitFallback, setRole, hbuf, hwalker]

/-! ## 9. What is *not* localized here

Named hypotheses this slice could not discharge, each isolated in the statement
that consumes it.

* `RestartStaged.lowerSrc` / `.workSlot` — *which* physical tape carries the
  chain's `w.machine.control.last` at the moment of the restart.  `chain` is
  still an abstract `ChainVM` in `GalilVML`, so this cannot be derived here; it
  becomes an obligation on the chain's own local refinement.
* `beginShiftVM_commitShift.hstaged` — likewise for `ofNat h` with
  `h = periodLength w`.
* `abs_commitFallback` — `work := inc length` used to be assumed (`hwork`);
  it is now localized by the third mirror bank `lengthMir` (the uniform fix).
  What remains assumed is only what the mirror machinery always assumes:
  `MirrorsAttached`/`Synced` on the pre-state (maintained by the ticks, with
  `LocalMirror.shaped_attach` for the re-attachment after a `take`), the slot
  equation `hslot` naming the detached mirror tape, and `hpol` — that `length`
  carries a positive sign bit, so that one `push` is `inc` and not `dec`.
* Tape *reuse*: a commit abandons the tapes its repointed roles used to own, and
  nothing here shows the bank of `P` tapes suffices.  `RolesInjective` is
  assumed of the pre-state and is **not** re-established for the post-state;
  freshness of `jL`/`jW`/`jD`/`jR`/`jF` is assumed, not allocated.
* The repositioning jobs are shown to *reach* their target
  (`repRight_reaches`, via `LocalInputView.reposition_reaches`) but not to
  *finish in time*: the deadline argument — distance ≤ the number of ticks
  between the two events — belongs to the schedule layer.
* `LocalBuffers.Cleared` on the idle halves (`RestartStaged.clean`,
  `hclean`) is assumed, not scheduled; `LocalBuffers.clearTick_done` gives it
  after `W + 1` background ticks, again a deadline obligation.

**無条件 PAL ∈ PEG は未完.**
-/

#print axioms StepLocal2
#print axioms absCtrs_setRole
#print axioms tapeLocal_resetSlots
#print axioms tapeLocal_pushSlots
#print axioms absHead_congr
#print axioms abs_right_of_repositioned
#print axioms abs_left_of_repositioned
#print axioms stepLocalN_repRight
#print axioms abs_repRight
#print axioms abs_repLeft
#print axioms abs_repFppWalker
#print axioms repRight_reaches
#print axioms stepLocal_commitRestart
#print axioms stepLocal2_commitRestart
#print axioms abs_commitRestart
#print axioms restartVM_commitRestart
#print axioms abs_commitReplay
#print axioms replayStartVM_commitReplay
#print axioms stepLocal2_commitShift
#print axioms beginShiftVM_commitShift
#print axioms stepLocal2_commitFallback
#print axioms abs_commitFallback

end PalPeg.LocalTick2
