import PalPeg.CloseoutCoreStep
import PalPeg.FrameFunction
import PalPeg.LocalCounter
import PalPeg.GalilScaffoldChainPeriod
import PalPeg.LocalStepRealize
import PalPeg.LocalViewLayout
import PalPeg.LocalViewSlot
import PalPeg.LocalArrival
import PalPeg.LocalQueueMachine
import PalPeg.LocalBuffers
import PalPeg.LocalReplayParked
import PalPeg.LocalTick3
import PalPeg.LocalStepFusion
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import PalPeg.MachineStep

/-!
# The physical encoding of the local machine

The local refinement `PalPeg.LocalState.GalilVML` is a finite record over a fixed number of
tapes, four cursors and a counter bank.  This module encodes that record as the tapes of a
persistent physical finite machine, and shows that **one tick of the abstract controller is one
step of the physical state**.

Two things live here.

* The *encoding*: an alphabet `Γm`, a slot table `Slot`, a padded tape layout (`padLeft`, with a
  floor sentinel so a component that has reached its left edge can say so from its window), and
  the predicates `EncControl` / `EncTapes` / `Enc` relating a scaffold state to a physical one.
* The *tick bridges* `vml_*`: for each branch of the controller, the abstract `tickFun` applied
  to `absState'' y` is `absState''` of a named local step of `y`.  The local steps themselves are
  `PalPeg.LocalTick3`'s (`copyVm`, `sliceVm`, …); what is proved here is that the controller's
  own step function lands on exactly those.
-/

set_option autoImplicit false
namespace PalPeg.PhysicalEncoding

open PalPeg.Program (STape)
open PalPeg.CloseoutCoreStep (Γc blankc)
open PalPeg.LocalCounter (Seg absCtr)
open PalPeg.GalilScaffoldChainPeriod (Token)
open PalPeg.GalilScaffoldChainInputSupply (GalilVM)
open PalPeg.GalilScaffoldTop (State)

/-! ### the alphabet and the tapes -/

abbrev Γm : Type := Bool ⊕ Γc ⊕ Fin 9 ⊕ Token ⊕ Seg

def blankM : Γm := .inl false

/-- **the floor a component's tape stands on.**  A component's tape is bounded on the
left: asked to move left from its first cell it stays where it is.  The machine's own tapes are
bounded further down, below the blanks that give the head its margin, so the encoding lays this
one symbol directly under the component's cells.  A rule about to move a tape left sees it in
its window and stays instead. -/
def bottomM : Γm := .inl true

def encCell (c : Γc) : Γm := if c = blankc then blankM else .inr (.inl c)
def encProg (s : Fin 9) : Γm := if s = 6 then blankM else .inr (.inr (.inl s))
def encToken (t : Token) : Γm := if t = Token.blank then blankM else .inr (.inr (.inr (.inl t)))
def encSeg (s : Seg) : Γm :=
  if s = PalPeg.LocalCounter.blank then blankM else .inr (.inr (.inr (.inr s)))

abbrev Slot : Type :=
  (Fin 4 × Fin 12) ⊕ Fin 9 ⊕ Fin 12 ⊕ Unit ⊕ Unit ⊕ Fin 3 ⊕ Fin 16 ⊕ Fin 7 ⊕ Fin 9 ⊕ Fin 12

/-- the number of tapes the machine keeps: the four views, **both halves** of each of the two
program machines, the mirrors, the three places, the counter bank and the answer.

There is one mirror per alias the controller performs.  A mirror is a second tape carrying its
source's value, kept in step with it, so that an alias is a change of which tape plays which part
and not a walk along a unary tape. -/
abbrev tapeCountM : ℕ := 118

/-- the slot of the `i`-th tape of the preparation program's live half, and of its idle half.
The two halves are what makes a wipe of the whole machine a flip of one bit rather than nine
erasures in one tick. -/
def progSlotOf (live : Bool) (i : Fin 9) : Slot :=
  if live then .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))
  else .inr (.inl i)

/-- the same for the search program's twelve tapes. -/
def dpSlotOf (live : Bool) (i : Fin 12) : Slot :=
  if live then .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr i))))))))
  else .inr (.inr (.inl i))

theorem progSlotOf_false (i : Fin 9) : progSlotOf false i = .inr (.inl i) := rfl

theorem progSlotOf_true (i : Fin 9) :
    progSlotOf true i = .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))) := rfl
theorem dpSlotOf_false (i : Fin 12) : dpSlotOf false i = .inr (.inr (.inl i)) := rfl

theorem progSlotOf_injective (live : Bool) : Function.Injective (progSlotOf live) := by
  intro i j h
  cases live <;> simpa [progSlotOf] using h

theorem progSlotOf_ne (i j : Fin 9) : progSlotOf true i ≠ progSlotOf false j := by
  simp [progSlotOf]

@[simp] theorem progSlotOf_ne_flip (l : Bool) (i j : Fin 9) :
    progSlotOf l i ≠ progSlotOf (!l) j := by
  cases l <;> simp [progSlotOf]

@[simp] theorem dpSlotOf_ne_flip (l : Bool) (i j : Fin 12) :
    dpSlotOf l i ≠ dpSlotOf (!l) j := by
  cases l <;> simp [dpSlotOf]

/-! The disequalities a proof needs once a slot's address carries the live bit.  Without them
`simp` cannot see that a view's slot, or the search program's, is not the preparation program's,
because it does not know which half is live.  Each is stated so that `simp` discharges the two
concrete cases itself. -/

@[simp] theorem dpSlotOf_ne_progSlotOf (l l' : Bool) (j : Fin 12) (i : Fin 9) :
    dpSlotOf l j ≠ progSlotOf l' i := by
  cases l <;> cases l' <;> simp [dpSlotOf, progSlotOf]

@[simp] theorem progSlotOf_ne_dpSlotOf (l l' : Bool) (i : Fin 9) (j : Fin 12) :
    progSlotOf l i ≠ dpSlotOf l' j := by
  cases l <;> cases l' <;> simp [dpSlotOf, progSlotOf]

@[simp] theorem progSlotOf_inj_iff (live : Bool) (i j : Fin 9) :
    progSlotOf live i = progSlotOf live j ↔ i = j :=
  ⟨fun h => progSlotOf_injective live h, fun h => by rw [h]⟩

@[simp] theorem dpSlotOf_inj_iff (live : Bool) (i j : Fin 12) :
    dpSlotOf live i = dpSlotOf live j ↔ i = j := by
  cases live <;> simp [dpSlotOf]

/-- a slot that is neither half's `i`-th program tape is not the live one, whichever half is
live. -/
@[simp] theorem ne_progSlotOf (live : Bool) (i : Fin 9) (slot : Slot)
    (h₀ : slot ≠ (.inr (.inl i) : Slot))
    (h₁ : slot ≠ (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))  : Slot)) :
    slot ≠ progSlotOf live i := by
  cases live
  · exact h₀
  · exact h₁

@[simp] theorem ne_dpSlotOf (live : Bool) (i : Fin 12) (slot : Slot)
    (h₀ : slot ≠ (.inr (.inr (.inl i)) : Slot))
    (h₁ : slot ≠ (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr i)))))))) : Slot)) :
    slot ≠ dpSlotOf live i := by
  cases live
  · exact h₀
  · exact h₁

def mapTape {Γ₁ Γ₂ : Type} (f : Γ₁ → Γ₂) (T : STape Γ₁) : STape Γ₂ :=
  ⟨T.left.map f, f T.focus, T.right.map f⟩

/-- the blanks a component's tape carries below its own cells, so that its head stands
clear of the left edge whatever the component does. -/
def padLeft (n : ℕ) (T : STape Γm) : STape Γm :=
  ⟨T.left ++ bottomM :: List.replicate n blankM, T.focus, T.right⟩

theorem pos_padLeft (n : ℕ) (T : STape Γm) :
    PalPeg.Local.pos (padLeft n T) = PalPeg.Local.pos T + n + 1 := by
  show (T.left ++ bottomM :: List.replicate n blankM).length = T.left.length + n + 1
  rw [List.length_append, List.length_cons, List.length_replicate]
  omega

theorem encProg_ne_bottom (s : Fin 9) : encProg s ≠ bottomM := by
  unfold encProg bottomM blankM
  split <;> simp

def encTape (t : PalPeg.GalilScaffoldTape.Tape) : STape (Fin 9) := ⟨t.left, t.focus, t.right⟩
def encPeriod (t : PalPeg.GalilScaffoldChainPeriod.Tape) : STape Token :=
  ⟨t.left, t.focus, t.right⟩

/-! ### the counters the state carries, by slot -/

/-- the sixteen counters, in the order the slots list them.  The chain's own four are
read off its tag; an idle chain carries none, and its slots then hold whatever was left there. -/
def counterOf (x : State GalilVM) : Fin 16 → Option PalPeg.GalilScaffoldCounter.Counter
  | 0 => some x.vm.cycle
  | 1 => some x.vm.remaining
  | 2 => some x.vm.radius
  | 3 => some x.vm.length
  | 4 => some x.vm.replay
  | 5 => some x.vm.lower
  | 6 => some x.vm.search.span
  | 7 => some x.vm.search.work
  | 8 => some x.vm.search.debt
  | 9 => some x.vm.fpp.work
  | 10 => match x.vm.chain with
    | .copy _ h _ _ _ _ _ => some h
    | .back _ h _ _ _ => some h
    | _ => none
  | 11 => match x.vm.chain with
    | .copy _ _ _ _ lag _ _ => some lag
    | .back _ _ lag _ _ => some lag
    | .watch w => some w.lag
    | .broken w => some w.lag
    | _ => none
  | 12 => match x.vm.chain with
    | .copy _ _ _ _ _ margin _ => some margin
    | .back _ _ _ margin _ => some margin
    | .watch w => some w.margin
    | .broken w => some w.margin
    | _ => none
  | 13 => match x.vm.chain with
    | .watch w => some w.machine.control.distance
    | .broken w => some w.machine.control.distance
    | _ => none
  | 14 => match x.vm.chain with
    | .watch w => some w.machine.control.boundary
    | .broken w => some w.machine.control.boundary
    | _ => none
  | _ => match x.vm.chain with
    | .watch w => some w.machine.control.last
    | .broken w => some w.machine.control.last
    | _ => none

/-! ### a component's step is one action on its physical tape -/

theorem mapTape_applyAction {Γ₁ : Type} (f : Γ₁ → Γm) {blank₁ : Γ₁} (hblank : f blank₁ = blankM)
    (T : STape Γ₁) (written : Γ₁) (move : PegSeparation.RealTimeTM.Move) :
    mapTape f (T.applyAction blank₁ (written, move))
      = (mapTape f T).applyAction blankM (f written, move) := by
  obtain ⟨left, focus, right⟩ := T
  cases move with
  | stay => rfl
  | right =>
    cases right with
    | nil =>
      show (⟨(written :: left).map f, f blank₁, []⟩ : STape Γm) = _
      rw [hblank]
      rfl
    | cons head rest => rfl
  | left =>
    cases left with
    | nil => rfl
    | cons head rest => rfl

/-- the action of the machine that an action of a component names: the symbol it writes is the
symbol's own, and the direction is the same. -/
def encAct {Γ₁ : Type} (f : Γ₁ → Γm) (a : PalPeg.CloseoutCoreEnc12.Act Γ₁) :
    PalPeg.CloseoutCoreEnc12.Act Γm :=
  a.map (fun sm => (f sm.1, sm.2))

theorem mapTape_actOnG {Γ₁ : Type} (f : Γ₁ → Γm) {blank₁ : Γ₁} (hblank : f blank₁ = blankM)
    (T : STape Γ₁) (a : PalPeg.CloseoutCoreEnc12.Act Γ₁) :
    mapTape f (PalPeg.CloseoutCoreEnc12.actOnG blank₁ T a)
      = PalPeg.CloseoutCoreEnc12.actOnG blankM (mapTape f T) (encAct f a) := by
  cases a with
  | none => rfl
  | some sm => exact mapTape_applyAction f hblank T sm.1 sm.2

/-- **a composite step of a component is the same composite step on the tape the machine keeps.**
Each action commutes with the change of alphabet, so a whole list does. -/
theorem mapTape_actList {Γ₁ : Type} (f : Γ₁ → Γm) {blank₁ : Γ₁} (hblank : f blank₁ = blankM) :
    ∀ (acts : List (PalPeg.CloseoutCoreEnc12.Act Γ₁)) (T : STape Γ₁),
      mapTape f (PalPeg.CloseoutCoreEnc12.actList blank₁ T acts)
        = PalPeg.CloseoutCoreEnc12.actList blankM (mapTape f T) (acts.map (encAct f))
  | [], T => rfl
  | a :: rest, T => by
    rw [PalPeg.CloseoutCoreEnc12.actList_cons, List.map_cons,
      PalPeg.CloseoutCoreEnc12.actList_cons, ← mapTape_actOnG f hblank T a]
    exact mapTape_actList f hblank rest _

theorem padLeft_applyAction_right (n : ℕ) (T : STape Γm) (written : Γm) :
    padLeft n (T.applyAction blankM (written, .right))
      = (padLeft n T).applyAction blankM (written, .right) := by
  obtain ⟨left, focus, right⟩ := T
  cases right <;> rfl

/-- **a right move of a component's tape is one action on the tape the machine keeps.**
The component's own move, the change of alphabet and the padding below all commute with it, so
the rule has only to name the symbol under the head and the direction.  Every branch of the
tick that moves a program tape, a period tape or a stack is this composition. -/
theorem padded_moveRight (n : ℕ) (t : PalPeg.GalilScaffoldTape.Tape) :
    padLeft n (mapTape encProg (encTape (PalPeg.GalilScaffoldTape.moveRight t)))
      = (padLeft n (mapTape encProg (encTape t))).applyAction blankM
          (encProg t.focus, .right) := by
  have hmove : encTape (PalPeg.GalilScaffoldTape.moveRight t)
      = (encTape t).applyAction (6 : Fin 9) (t.focus, .right) := by
    obtain ⟨left, focus, right⟩ := t
    cases right <;> rfl
  rw [hmove, mapTape_applyAction encProg (if_pos rfl) (encTape t) t.focus .right,
    padLeft_applyAction_right]

/-- a left move carries across the padding whenever the component still has a cell
below its head. -/
theorem padLeft_applyAction_left (n : ℕ) (T : STape Γm) (written : Γm) (hleft : T.left ≠ []) :
    padLeft n (T.applyAction blankM (written, .left))
      = (padLeft n T).applyAction blankM (written, .left) := by
  obtain ⟨left, focus, right⟩ := T
  cases left with
  | nil => exact absurd rfl hleft
  | cons head rest => rfl

/-- **a left move of a component's tape, away from its floor, is one action on the tape
the machine keeps.** -/
theorem padded_moveLeft (n : ℕ) (t : PalPeg.GalilScaffoldTape.Tape) (hleft : t.left ≠ []) :
    padLeft n (mapTape encProg (encTape (PalPeg.GalilScaffoldTape.moveLeft t)))
      = (padLeft n (mapTape encProg (encTape t))).applyAction blankM
          (encProg t.focus, .left) := by
  obtain ⟨left, focus, right⟩ := t
  cases left with
  | nil => exact absurd rfl hleft
  | cons head rest => rfl

/-- **on its floor the component's tape stays**, which is what the rule must do there. -/
theorem moveLeft_atFloor (t : PalPeg.GalilScaffoldTape.Tape) (hleft : t.left = []) :
    PalPeg.GalilScaffoldTape.moveLeft t = t := by
  obtain ⟨left, focus, right⟩ := t
  cases left with
  | nil => rfl
  | cons a rest => exact absurd hleft (by simp)

/-! ### what the window sees just below the head -/

theorem toList_padLeft (n : ℕ) (T : STape Γm) :
    PalPeg.Local.toList (padLeft n T)
      = List.replicate n blankM ++ bottomM :: PalPeg.Local.toList T := by
  show (T.left ++ bottomM :: List.replicate n blankM).reverse ++ T.focus :: T.right
    = List.replicate n blankM ++ bottomM :: (T.left.reverse ++ T.focus :: T.right)
  rw [List.reverse_append, List.reverse_cons, List.reverse_replicate]
  simp

theorem getD_replicate_append (n k : ℕ) (rest : List Γm) :
    (List.replicate n blankM ++ rest).getD (n + k) blankM = rest.getD k blankM := by
  induction n with
  | zero => simp
  | succ n ih =>
    show (blankM :: (List.replicate n blankM ++ rest)).getD (n + 1 + k) blankM = _
    have h : n + 1 + k = (n + k) + 1 := by omega
    rw [h]
    exact ih

theorem getD_append_at (A : List Γm) (x : Γm) (B : List Γm) :
    (A ++ x :: B).getD A.length blankM = x := by
  induction A with
  | nil => rfl
  | cons a rest ih => exact ih

/-- **the cell the window shows just below the head is the component's next cell down,
and the floor when it has none.**  This is the reading a rule tests before it moves a tape
left: `bottomM` says stay, anything else says move. -/
theorem window_below (n K : ℕ) (T : STape Γm) (hK1 : 1 ≤ K) (hKn : K ≤ n + 1) :
    PalPeg.Local.readWin blankM K (padLeft n T) ⟨K - 1, by omega⟩ = T.left.headD bottomM := by
  rw [PalPeg.Local.readWin_eq, pos_padLeft]
  have hidx : PalPeg.Local.pos T + n + 1 - K + ((⟨K - 1, by omega⟩ : Fin (2 * K + 1)) : ℕ)
      = n + PalPeg.Local.pos T := by
    simp only []
    omega
  rw [hidx, PalPeg.Local.rd, toList_padLeft, getD_replicate_append]
  obtain ⟨left, focus, right⟩ := T
  cases left with
  | nil => rfl
  | cons a rest =>
    show (bottomM :: PalPeg.Local.toList (⟨a :: rest, focus, right⟩ : STape Γm)).getD
      (rest.length + 1) blankM = a
    show (PalPeg.Local.toList (⟨a :: rest, focus, right⟩ : STape Γm)).getD rest.length blankM = a
    show ((a :: rest).reverse ++ focus :: right).getD rest.length blankM = a
    rw [List.reverse_cons, List.append_assoc]
    show (rest.reverse ++ a :: (focus :: right)).getD rest.length blankM = a
    have hlen : rest.length = rest.reverse.length := by simp
    rw [hlen]
    exact getD_append_at rest.reverse a (focus :: right)

/-- **the cell the window shows at its centre is the cell under the head.**  Together
with `window_below` this is everything a one-cell move of a component's tape needs to read. -/
theorem window_centre (K : ℕ) (T : STape Γm) (hK : K ≤ PalPeg.Local.pos T) :
    PalPeg.Local.readWin blankM K T ⟨K, by omega⟩ = T.focus := by
  rw [PalPeg.Local.readWin_eq]
  have hidx : PalPeg.Local.pos T - K + ((⟨K, by omega⟩ : Fin (2 * K + 1)) : ℕ)
      = PalPeg.Local.pos T := by
    simp only []
    omega
  rw [hidx]
  exact PalPeg.Local.rd_pos blankM T

/-- **a counter's zero test is one cell of its window.**  The value a counter tape holds is the
run of marks at the top of its left stack, so it is zero exactly when the cell below the head is
not a mark — and that is the cell `window_below` reads.  The machine therefore decides the test
without moving a head. -/
theorem counterZero_iff_below {K margin : ℕ} (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (segments : STape PalPeg.LocalCounter.Seg) :
    PalPeg.LocalCounter.val segments = 0
      ↔ PalPeg.Local.readWin blankM K (padLeft margin (mapTape encSeg segments))
          ⟨K - 1, by omega⟩ ≠ encSeg PalPeg.LocalCounter.mark := by
  have hinj : ∀ a : PalPeg.LocalCounter.Seg,
      (encSeg a = encSeg PalPeg.LocalCounter.mark) ↔ a = PalPeg.LocalCounter.mark := by decide
  rw [window_below margin K (mapTape encSeg segments) hK1 hKn]
  obtain ⟨left, focus, right⟩ := segments
  cases left with
  | nil =>
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    show ¬ (bottomM = encSeg PalPeg.LocalCounter.mark)
    decide
  | cons a rest =>
    have hm : PalPeg.LocalCounter.markRun (a :: rest) = 0
        ↔ a ≠ PalPeg.LocalCounter.mark := by
      by_cases ha : a = PalPeg.LocalCounter.mark
      · subst ha
        simp [PalPeg.LocalCounter.markRun]
      · simp [PalPeg.LocalCounter.markRun, ha]
    show PalPeg.LocalCounter.markRun (a :: rest) = 0 ↔ _
    rw [hm]
    show ¬ a = PalPeg.LocalCounter.mark ↔ ¬ (encSeg a = encSeg PalPeg.LocalCounter.mark)
    rw [hinj a]

/-- **the test that a cursor has run out is a test on the top cell of its stack.**  A cursor is
stored as its remaining letters followed by sealed junk, and junk never shows a letter, so the top
cell holds a letter exactly when the cursor still has one.  The stack is kept with its head just
above the top, so that cell is the one below the head — the one `window_below` reads. -/
theorem placeRead_isNone_iff_head (p : PalPeg.GalilScaffoldPlace.Place)
    (junk : List (Option (Fin 2))) (hsealed : PalPeg.ConcreteLocalMachine.Sealed junk) :
    (PalPeg.GalilScaffoldPlace.read p).isNone = true
      ↔ ∀ a : Fin 2,
          (p.letters.map (fun letter => some letter) ++ junk).head? ≠ some (some a) := by
  unfold PalPeg.GalilScaffoldPlace.read
  cases hl : p.letters with
  | nil =>
    simp only [List.map_nil, List.nil_append, Option.isNone_none]
    exact ⟨fun _ => hsealed, fun _ => trivial⟩
  | cons b rest =>
    simp only [List.map_cons, List.cons_append, List.head?_cons, Option.isNone_some]
    refine ⟨fun h => absurd h (by simp), fun h => absurd (h b) (by simp)⟩

/-- **the top of a cursor's stack is the symbol under its head.**  `dTape` puts the top of the
stack at the focus and the rest below it, so the head stands on the top cell rather than above it,
and `TEqG` hands that cell across unchanged. -/
theorem stackTape_focus (stackTape : STape PalPeg.CloseoutCoreStep.Γc)
    (stack : List (Option (Fin 2)))
    (h : PalPeg.ConcreteLocalMachine.StackTape stackTape stack) :
    stackTape.focus
      = stack.head?.elim PalPeg.CloseoutCoreStep.blankc PalPeg.CloseoutCoreEnc.cellSym := by
  obtain ⟨debris, hteq⟩ := h
  have hfocus : stackTape.focus
      = (PalPeg.CloseoutCoreEnc18.dTape stack debris).focus := by
    rw [← PalPeg.Local.rd_pos PalPeg.CloseoutCoreStep.blankc stackTape, hteq.2, hteq.1,
      PalPeg.Local.rd_pos]
  rw [hfocus]
  cases stack <;> rfl

/-- a program tape's cells are told apart by their encodings, so a rule testing the
window against `encProg r` is testing the cell against `r`. -/
theorem encProg_eq_iff (s r : Fin 9) : encProg s = encProg r ↔ s = r := by
  unfold encProg blankM
  split <;> split <;> simp_all <;> omega

/-- **a cursor with a cell on its stack stands clear of the left edge.**  Its head sits on the
top of the stack and the rest of the stack lies below, so its left stack is not empty. -/
theorem stackTape_left_ne_nil (stackTape : STape PalPeg.CloseoutCoreStep.Γc)
    (cell : Option (Fin 2)) (rest : List (Option (Fin 2)))
    (h : PalPeg.ConcreteLocalMachine.StackTape stackTape (cell :: rest)) :
    stackTape.left ≠ [] := by
  obtain ⟨debris, hteq⟩ := h
  have hpos : stackTape.left.length = rest.length + 1 := by
    have h1 : PalPeg.Local.pos stackTape
        = PalPeg.Local.pos (PalPeg.CloseoutCoreEnc18.dTape (cell :: rest) debris) := hteq.1
    rw [show PalPeg.Local.pos stackTape = stackTape.left.length from rfl] at h1
    rw [h1]
    show (rest.map PalPeg.CloseoutCoreEnc.cellSym ++ [PalPeg.CloseoutCoreStep.blankc]).length
      = rest.length + 1
    simp
  intro hnil
  rw [hnil] at hpos
  simp at hpos

/-- **popping a cursor's stack is one step left.**  `dTape` keeps the top of the stack under the
head and the rest of it below, so writing the top back and stepping left uncovers the next cell.
The cursor's own tape need only agree with `dTape` on its readings, and one action preserves that
agreement. -/
theorem stackTape_pop (stackTape : STape PalPeg.CloseoutCoreStep.Γc)
    (cell : Option (Fin 2)) (rest : List (Option (Fin 2)))
    (h : PalPeg.ConcreteLocalMachine.StackTape stackTape (cell :: rest)) :
    PalPeg.ConcreteLocalMachine.StackTape
      (PalPeg.CloseoutCoreEnc12.actOnG PalPeg.CloseoutCoreStep.blankc stackTape
        (some (PalPeg.CloseoutCoreEnc.cellSym cell, (.left : PalPeg.CloseoutCoreEnc12.MoveC))))
      rest := by
  obtain ⟨debris, hteq⟩ := h
  refine ⟨PalPeg.CloseoutCoreEnc.cellSym cell :: debris, ?_⟩
  have hstep := PalPeg.ConcreteLocalMachine.teqG_actOnG hteq
    (some (PalPeg.CloseoutCoreEnc.cellSym cell, (.left : PalPeg.CloseoutCoreEnc12.MoveC)))
  have hideal : PalPeg.CloseoutCoreEnc12.actOnG PalPeg.CloseoutCoreStep.blankc
      (PalPeg.CloseoutCoreEnc18.dTape (cell :: rest) debris)
      (some (PalPeg.CloseoutCoreEnc.cellSym cell, (.left : PalPeg.CloseoutCoreEnc12.MoveC)))
      = PalPeg.CloseoutCoreEnc18.dTape rest (PalPeg.CloseoutCoreEnc.cellSym cell :: debris) := by
    cases rest <;> rfl
  rw [hideal] at hstep
  exact hstep

/-- **pushing a cell onto a stack tape is two actions.**  The head stands on the top of the
stack, so the old top has to be written back and stepped over before the new one can be written
where the head now stands.  What the head steps onto is debris, and debris is what the encoding
allows below a stack. -/
theorem stackTape_push (stackTape : STape PalPeg.CloseoutCoreStep.Γc)
    (cell : Option (Fin 2)) (stack : List (Option (Fin 2)))
    (h : PalPeg.ConcreteLocalMachine.StackTape stackTape stack) :
    PalPeg.ConcreteLocalMachine.StackTape
      (PalPeg.CloseoutCoreEnc12.actList PalPeg.CloseoutCoreStep.blankc stackTape
        [some (stackTape.focus, (.right : PalPeg.CloseoutCoreEnc12.MoveC)),
          some (PalPeg.CloseoutCoreEnc.cellSym cell,
            (.stay : PalPeg.CloseoutCoreEnc12.MoveC))])
      (cell :: stack) := by
  obtain ⟨debris, hteq⟩ := h
  have hfocus : stackTape.focus
      = (PalPeg.CloseoutCoreEnc18.dTape stack debris).focus := by
    rw [← PalPeg.Local.rd_pos PalPeg.CloseoutCoreStep.blankc stackTape, hteq.2, hteq.1,
      PalPeg.Local.rd_pos]
  refine ⟨debris.tail, ?_⟩
  have hstep := PalPeg.ConcreteLocalMachine.teqG_actList hteq
    [some (stackTape.focus, (.right : PalPeg.CloseoutCoreEnc12.MoveC)),
      some (PalPeg.CloseoutCoreEnc.cellSym cell,
        (.stay : PalPeg.CloseoutCoreEnc12.MoveC))]
  have hideal : PalPeg.CloseoutCoreEnc12.actList PalPeg.CloseoutCoreStep.blankc
      (PalPeg.CloseoutCoreEnc18.dTape stack debris)
      [some (stackTape.focus, (.right : PalPeg.CloseoutCoreEnc12.MoveC)),
        some (PalPeg.CloseoutCoreEnc.cellSym cell,
          (.stay : PalPeg.CloseoutCoreEnc12.MoveC))]
      = PalPeg.CloseoutCoreEnc18.dTape (cell :: stack) debris.tail := by
    rw [hfocus]
    cases stack <;> cases debris <;> rfl
  rw [hideal] at hstep
  exact hstep

/-- **and the same step on the encoded tape.**  The cursor's tape is padded below, so the step
left cannot reach the floor. -/
theorem padded_place_pop (margin : ℕ) (stackTape : STape PalPeg.CloseoutCoreStep.Γc)
    (cell : Option (Fin 2)) (rest : List (Option (Fin 2)))
    (h : PalPeg.ConcreteLocalMachine.StackTape stackTape (cell :: rest)) :
    padLeft margin (mapTape encCell
        (PalPeg.CloseoutCoreEnc12.actOnG PalPeg.CloseoutCoreStep.blankc stackTape
          (some (PalPeg.CloseoutCoreEnc.cellSym cell, (.left : PalPeg.CloseoutCoreEnc12.MoveC)))))
      = PalPeg.CloseoutCoreEnc12.actOnG blankM (padLeft margin (mapTape encCell stackTape))
          (some (encCell (PalPeg.CloseoutCoreEnc.cellSym cell),
            (.left : PalPeg.CloseoutCoreEnc12.MoveC))) := by
  show padLeft margin (mapTape encCell
      (STape.applyAction PalPeg.CloseoutCoreStep.blankc stackTape
        (PalPeg.CloseoutCoreEnc.cellSym cell, .left))) = _
  rw [mapTape_applyAction encCell rfl stackTape (PalPeg.CloseoutCoreEnc.cellSym cell) .left,
    padLeft_applyAction_left margin (mapTape encCell stackTape)
      (encCell (PalPeg.CloseoutCoreEnc.cellSym cell))
      (by
        obtain ⟨left, focus, right⟩ := stackTape
        cases left with
        | nil => exact absurd rfl (stackTape_left_ne_nil _ cell rest h)
        | cons head tail => exact List.cons_ne_nil _ _)]
  rfl

/-- **writing a cell without moving is one action too.**  Every branch that stamps a
symbol on a program tape — the end marker the copy leaves, the letters the preparation lays down
— is this one. -/
theorem padded_write (n : ℕ) (t : PalPeg.GalilScaffoldTape.Tape) (symbol : Fin 9) :
    padLeft n (mapTape encProg (encTape (PalPeg.GalilScaffoldTape.write t symbol)))
      = (padLeft n (mapTape encProg (encTape t))).applyAction blankM (encProg symbol, .stay) := by
  obtain ⟨left, focus, right⟩ := t
  rfl

/-- **writing a symbol and stepping right is one action.**  The fallback copy stamps the
walker's letter on its tape and moves on, and the encoded tape does it in one. -/
theorem padded_writeRight (n : ℕ) (t : PalPeg.GalilScaffoldTape.Tape) (symbol : Fin 9) :
    padLeft n (mapTape encProg (encTape
        (PalPeg.GalilScaffoldTape.moveRight (PalPeg.GalilScaffoldTape.write t symbol))))
      = (padLeft n (mapTape encProg (encTape t))).applyAction blankM (encProg symbol, .right) := by
  obtain ⟨left, focus, right⟩ := t
  cases right <;> rfl

/-- **marking a new block, as two actions on the encoded tape.**  `markNew` steps right, writes
the component's label and steps right again; writing and then stepping is one action, so the whole
of it is the pair the branch names. -/
theorem padded_markNew (margin : ℕ) (t : PalPeg.GalilScaffoldTape.Tape) (first : Fin 9) :
    PalPeg.CloseoutCoreEnc12.actList blankM (padLeft margin (mapTape encProg (encTape t)))
        [some (encProg t.focus, (.right : PalPeg.CloseoutCoreEnc12.MoveC)),
          some (encProg first, (.right : PalPeg.CloseoutCoreEnc12.MoveC))]
      = padLeft margin (mapTape encProg (encTape
          (PalPeg.GalilScaffoldTape.moveRight
            (PalPeg.GalilScaffoldTape.write
              (PalPeg.GalilScaffoldTape.moveRight t) first)))) := by
  obtain ⟨left, focus, right⟩ := t
  cases right with
  | nil => rfl
  | cons a as => cases as <;> rfl

/-- the bookkeeping for a rule that stamps one program tape and leaves the rest alone. -/
theorem prog_slots_after_write {n : ℕ} (margin : ℕ) (i : Fin n) (symbol : Fin 9)
    (source : Fin n → PalPeg.GalilScaffoldTape.Tape) (T : Fin n → STape Γm)
    (hT : ∀ j, T j = padLeft margin (mapTape encProg (encTape (source j)))) (j : Fin n) :
    (if j = i then
        PalPeg.CloseoutCoreEnc12.actList blankM (T j) [some (encProg symbol, .stay)] else T j)
      = padLeft margin (mapTape encProg (encTape
          (Function.update source i (PalPeg.GalilScaffoldTape.write (source i) symbol) j))) := by
  rw [Function.update_apply]
  by_cases hji : j = i
  · subst hji
    rw [if_pos rfl, if_pos rfl, hT j]
    show (padLeft margin (mapTape encProg (encTape (source j)))).applyAction blankM
      (encProg symbol, .stay) = _
    rw [padded_write]
  · rw [if_neg hji, if_neg hji, hT j]

/-! ### one tape moves, the others stand still -/

/-- the symbol the rule writes back is the one already under the head. -/
theorem focus_padded (margin : ℕ) (t : PalPeg.GalilScaffoldTape.Tape) :
    (padLeft margin (mapTape encProg (encTape t))).focus = encProg t.focus := rfl

/-- **the bookkeeping of a rule that moves one program tape right and leaves the rest
alone.**  The rule names an action only at the slot it moves, so the other slots keep their
tapes, and at that slot the action is exactly the component's move (`padded_moveRight`).  It
serves both program machines: the preparation's nine tapes and the search's twelve. -/
theorem prog_slots_after_right {n : ℕ} (margin : ℕ) (i : Fin n)
    (source : Fin n → PalPeg.GalilScaffoldTape.Tape) (T : Fin n → STape Γm)
    (hT : ∀ j, T j = padLeft margin (mapTape encProg (encTape (source j)))) (j : Fin n) :
    (if j = i then
        PalPeg.CloseoutCoreEnc12.actList blankM (T j) [some ((T j).focus, .right)] else T j)
      = padLeft margin (mapTape encProg (encTape
          (Function.update source i (PalPeg.GalilScaffoldTape.moveRight (source i)) j))) := by
  rw [Function.update_apply]
  by_cases hji : j = i
  · subst hji
    rw [if_pos rfl, if_pos rfl, hT j, focus_padded]
    show (padLeft margin (mapTape encProg (encTape (source j)))).applyAction blankM
      (encProg (source j).focus, .right) = _
    rw [padded_moveRight]
  · rw [if_neg hji, if_neg hji, hT j]

/-- the same for a rule that moves one program tape left, where the component still has
a cell below its head. -/
theorem prog_slots_after_left {n : ℕ} (margin : ℕ) (i : Fin n)
    (source : Fin n → PalPeg.GalilScaffoldTape.Tape) (T : Fin n → STape Γm)
    (hT : ∀ j, T j = padLeft margin (mapTape encProg (encTape (source j))))
    (hfloor : (source i).left ≠ []) (j : Fin n) :
    (if j = i then
        PalPeg.CloseoutCoreEnc12.actList blankM (T j) [some ((T j).focus, .left)] else T j)
      = padLeft margin (mapTape encProg (encTape
          (Function.update source i (PalPeg.GalilScaffoldTape.moveLeft (source i)) j))) := by
  rw [Function.update_apply]
  by_cases hji : j = i
  · subst hji
    rw [if_pos rfl, if_pos rfl, hT j, focus_padded]
    show (padLeft margin (mapTape encProg (encTape (source j)))).applyAction blankM
      (encProg (source j).focus, .left) = _
    rw [padded_moveLeft margin (source j) hfloor]
  · rw [if_neg hji, if_neg hji, hT j]

/-- **and on the floor the rule stands still, which is what the component does.**  So
a left move needs no invariant about where the component's head is: the window decides. -/
theorem prog_slots_at_floor {n : ℕ} (margin : ℕ) (i : Fin n)
    (source : Fin n → PalPeg.GalilScaffoldTape.Tape) (T : Fin n → STape Γm)
    (hT : ∀ j, T j = padLeft margin (mapTape encProg (encTape (source j))))
    (hfloor : (source i).left = []) (j : Fin n) :
    T j = padLeft margin (mapTape encProg (encTape
        (Function.update source i (PalPeg.GalilScaffoldTape.moveLeft (source i)) j))) := by
  rw [Function.update_apply, hT j]
  by_cases hji : j = i
  · subst hji
    rw [if_pos rfl, moveLeft_atFloor (source j) hfloor]
  · rw [if_neg hji]

/-- **a step of the preparation machine touches one of its nine tapes and leaves the
other eight where they are.**  The mark walk is the case `i = 8`, the copy and the walk home the
case `i = 7`. -/
theorem fppTape_tapes (x : PalPeg.GalilScaffoldChainInputSupply.FppControl.State) (i : Fin 9)
    (f : PalPeg.GalilScaffoldTape.Tape → PalPeg.GalilScaffoldTape.Tape) (j : Fin 9) :
    (PalPeg.GalilScaffoldChainInputSupply.FppControl.tape x i f).config.tapes j
      = Function.update x.program.config.tapes i (f (x.program.config.tapes i)) j := rfl

/-! ### the heads, the places and the chain's tapes, by slot -/

/-- the four cursors the machine keeps a view for: the scan's three heads and the
chain's verifier.  An idle chain has no verifier, and its view then holds whatever was left. -/
def headOf (x : State GalilVM) : Fin 4 → Option PalPeg.GalilScaffoldInputHead.PlaceHead
  | 0 => some x.vm.left
  | 1 => some x.vm.center
  | 2 => some x.vm.right
  | _ => match x.vm.chain with
    | .idle => none
    | .copy _ _ _ _ _ _ verifier => some verifier
    | .back _ _ _ _ verifier => some verifier
    | .watch w => some w.machine.verifier
    | .broken w => some w.machine.verifier

/-- the three copy cursors. -/
def placeOf (x : State GalilVM) : Fin 3 → Option PalPeg.GalilScaffoldPlace.Place
  | 0 => some x.vm.walker
  | 1 => some x.vm.fpp.walker
  | _ => match x.vm.chain with
    | .copy _ _ walker _ _ _ _ => some walker
    | _ => none

/-- the chain's period tape, when it has one. -/
def periodOf (x : State GalilVM) : Option PalPeg.GalilScaffoldChainPeriod.Tape :=
  match x.vm.chain with
  | .idle => none
  | .copy _ _ _ period _ _ _ => some period
  | .back period _ _ _ _ => some period
  | .watch w => some w.machine.control.period
  | .broken w => some w.machine.control.period

/-- the chain's answer tape, which only the copy phase reads. -/
def answerOf (x : State GalilVM) : Option PalPeg.GalilScaffoldTape.Tape :=
  match x.vm.chain with
  | .copy answer _ _ _ _ _ _ => some answer
  | _ => none

/-- the slot of the preparation program's `i`-th tape. -/
abbrev progSlot (live : Bool) (i : Fin 9) : Slot := progSlotOf live i

/-- the slot of the `i`-th tape of the `v`-th input head's view. -/
abbrev headSlot (v : Fin 4) (i : Fin 12) : Slot := .inl (v, i)

/-- the slot of the machine's `i`-th cursor. -/
abbrev placeSlot (i : Fin 3) : Slot := .inr (.inr (.inr (.inr (.inr (.inl i)))))

/-- the slot of the machine's `c`-th counter. -/
abbrev counterSlot (c : Fin 16) : Slot := .inr (.inr (.inr (.inr (.inr (.inr (.inl c))))))

theorem progSlotOf_ne_headSlot (live : Bool) (i : Fin 9) (v : Fin 4) (t : Fin 12) :
    progSlotOf live i ≠ headSlot v t := by
  unfold progSlotOf
  split <;> simp [headSlot]

theorem dpSlotOf_ne_headSlot (live : Bool) (i : Fin 12) (v : Fin 4) (t : Fin 12) :
    dpSlotOf live i ≠ headSlot v t := by
  unfold dpSlotOf
  split <;> simp [headSlot]

theorem progSlot_ne_counterSlot (live : Bool) (i : Fin 9) (c : Fin 16) :
    progSlot live i ≠ counterSlot c := by
  cases live <;> simp [progSlotOf]

theorem progSlot_ne_placeSlot (live : Bool) (i : Fin 9) (p : Fin 3) :
    progSlot live i ≠ placeSlot p := by
  cases live <;> simp [progSlotOf]

theorem counterSlot_ne_placeSlot (c : Fin 16) (p : Fin 3) : counterSlot c ≠ placeSlot p := by
  simp

/-- the slot of the machine's `m`-th mirror of a counter. -/
abbrev mirrorSlot (m : Fin 7) : Slot := .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl m)))))))

theorem progSlot_ne_mirrorSlot (live : Bool) (i : Fin 9) (m : Fin 7) :
    progSlot live i ≠ mirrorSlot m := by
  cases live <;> simp [progSlotOf]

theorem counterSlot_ne_mirrorSlot (c : Fin 16) (m : Fin 7) : counterSlot c ≠ mirrorSlot m := by
  simp

theorem headSlot_ne_mirrorSlot (v : Fin 4) (t : Fin 12) (m : Fin 7) :
    headSlot v t ≠ mirrorSlot m := by
  simp

theorem headSlot_ne_of_head_ne (v v' : Fin 4) (t t' : Fin 12) (h : v ≠ v') :
    headSlot v t ≠ headSlot v' t' := by
  intro hEq
  have hpair : v = v' ∧ t = t' := by simpa [headSlot] using hEq
  exact h hpair.1

theorem mirrorSlot_injective : Function.Injective mirrorSlot := by
  intro m m' hEq
  simpa using hEq

theorem progSlot_ne_headSlot (live : Bool) (i : Fin 9) (v : Fin 4) (t : Fin 12) :
    progSlot live i ≠ headSlot v t := by
  cases live <;> simp [progSlotOf]

theorem counterSlot_ne_headSlot (c : Fin 16) (v : Fin 4) (t : Fin 12) :
    counterSlot c ≠ headSlot v t := by
  simp

/-- **which counter each spare copy is kept in step with.**  Three of `radius`, for the
`lag` and `margin` a chain is born with and for the negated `debt` a restart starts from; one of
`lower`, for the `work` a preparation starts from; one of `span`, for the `work` the doubling
enters with.  Handing one over is a move of the finite control and costs no action
(`LocalMirror.take`), and the opposite polarity bit hands over the negated copy
(`LocalMirror.negate_via_pol`). -/
def mirrorSource : Fin 7 → Fin 16
  | 0 => 2
  | 1 => 2
  | 2 => 2
  | 3 => 5
  | 4 => 6
  | 5 => 10
  | _ => 3

/-! ### what the tapes hold -/

/-- **the twelve slots of one cursor hold a view.**  This is what `EncTapes.heads` says about a
cursor, with the abstract head left out: the slots hold the encoded tapes of some view, whatever
that view abstracts to.

The abstraction names only three of the four cursors always.  The fourth is the chain's verifier,
and `headOf x 3` is `none` exactly when the chain is idle — but `EncTapes.margins` asks for the
margin of every slot, that cursor's twelve included.  So the margin of those slots cannot come
from `heads`, and this is the property it comes from instead. -/
def HeadSlotsRep (margin : ℕ) (gap : Fin 4 → Bool)
    (micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl) (tapes : Slot → STape Γm)
    (v : Fin 4) : Prop :=
  ∃ (view : PalPeg.LocalInputView.InputView)
      (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc),
    PalPeg.ConcreteLocalMachine.ViewRep margin view (gap v) (micro v) viewTapes ∧
      (∀ i, tapes (headSlot v i) = mapTape encCell (viewTapes i)) ∧
        PalPeg.LocalViewCells.ViewCells view ∧ PalPeg.LocalInputView.WF view

/-- the same, with the view named: what a cursor's twelve slots hold. -/
def HeadSlotsRepAt (margin : ℕ) (gap : Fin 4 → Bool)
    (micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl) (tapes : Slot → STape Γm)
    (v : Fin 4) (view : PalPeg.LocalInputView.InputView) : Prop :=
  ∃ viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc,
    PalPeg.ConcreteLocalMachine.ViewRep margin view (gap v) (micro v) viewTapes ∧
      (∀ i, tapes (headSlot v i) = mapTape encCell (viewTapes i)) ∧
        PalPeg.LocalViewCells.ViewCells view ∧ PalPeg.LocalInputView.WF view

/-- **the verifier's slots mirror the centre while the chain is idle.**  The encoding's own field
says those twelve slots hold some view; this says which one — the centre cursor's.

The point of asking for it is the moment a chain is born.  The scan's background quantum starts a
chain whose verifier *is* the centre cursor (`FrameFunction.chainAtFun`, with `ver := s.center`),
and no command of a view copies a cursor.  If the slots already hold the centre's view, nothing
has to be copied: the encoding of the new verifier is the encoding that was already there. -/
def IdleHeadMirrorsCentre (margin : ℕ) (gap : Fin 4 → Bool)
    (micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl) (tapes : Slot → STape Γm)
    (x : State GalilVM) : Prop :=
  headOf x 3 = none →
    ∃ view : PalPeg.LocalInputView.InputView,
      HeadSlotsRepAt margin gap micro tapes 3 view ∧
        PalPeg.LocalArrival.absHead' view [] = x.vm.center

/-- **so a chain's birth costs the machine nothing on the verifier's slots.**  Whatever tick
starts the chain, the twelve slots of the fourth cursor already encode a view of the head the new
verifier is, and that is exactly what the `heads` field of the encoding asks for it.

This is the whole of `M-headCopy` for the chain's birth: the copy is not made, it is kept. -/
theorem heads_atChainBirth {margin : ℕ} {gap : Fin 4 → Bool}
    {micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl} {tapes : Slot → STape Γm}
    {x y : State GalilVM} (hmirror : IdleHeadMirrorsCentre margin gap micro tapes x)
    (hidle : headOf x 3 = none) (head : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hborn : headOf y 3 = some head) (hver : head = x.vm.center) :
    ∃ (view : PalPeg.LocalInputView.InputView)
        (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc),
      PalPeg.LocalArrival.absHead' view [] = head ∧
        PalPeg.ConcreteLocalMachine.ViewRep margin view (gap 3) (micro 3) viewTapes ∧
        (∀ i, tapes (headSlot 3 i) = mapTape encCell (viewTapes i)) ∧
          PalPeg.LocalViewCells.ViewCells view ∧ PalPeg.LocalInputView.WF view := by
  obtain ⟨view, ⟨viewTapes, hrep, hslots, hcells, hwf⟩, habs⟩ := hmirror hidle
  exact ⟨view, viewTapes, by rw [hver]; exact habs, hrep, hslots, hcells, hwf⟩

/-- **the part of the encoding that is an exact reading of the state**: the two program
bundles, the chain's answer and period tapes, and the counters whose slot the state fills.  The
heads, the places and the chain's own counters are the components whose representation carries
its own invariants (`ViewRep`, `LaysSealed`, the mirrors), and they enter the encoding through
those. -/
structure EncTapes (margin : ℕ) (x : State GalilVM) (polarity : Fin 16 → Bool)
    (gap : Fin 4 → Bool) (micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl)
    (fppLive dpLive : Bool) (tapes : Slot → STape Γm) : Prop where
  margins : ∀ slot, margin ≤ PalPeg.Local.pos (tapes slot)
  heads : ∀ (v : Fin 4) head, headOf x v = some head →
    ∃ (view : PalPeg.LocalInputView.InputView) (viewTapes : Fin 12 → STape Γc),
      PalPeg.LocalArrival.absHead' view [] = head ∧
        PalPeg.ConcreteLocalMachine.ViewRep margin view (gap v) (micro v) viewTapes ∧
        (∀ i, tapes (.inl (v, i)) = mapTape encCell (viewTapes i)) ∧
          PalPeg.LocalViewCells.ViewCells view ∧ PalPeg.LocalInputView.WF view
  /-- the chain's verifier holds a view even while the chain is idle and the abstraction does not
  name it.  Without this the margin of those twelve slots has no source: `heads` speaks of a
  cursor only through its abstract head, and `headOf x 3` is `none` exactly then. -/
  idleHead : headOf x 3 = none → HeadSlotsRep margin gap micro tapes 3
  fpp : ∀ i : Fin 9,
    tapes (progSlotOf fppLive i) = padLeft margin (mapTape encProg (encTape (x.vm.fpp.program.config.tapes i)))
  dp : ∀ i : Fin 12, tapes (dpSlotOf dpLive i) = padLeft margin (mapTape encProg (encTape (x.vm.dp.config.tapes i)))
  /-- the idle half of the preparation program still has the shape of a padded tape.  Its
  contents are nobody's business, but the shape is: it is what keeps its heads clear of the
  left edge while the background erasure walks them back. -/
  idleShape : ∀ i : Fin 9, ∃ raw : STape (Fin 9),
    tapes (progSlotOf (!fppLive) i) = padLeft margin (mapTape encProg raw)
  counters : ∀ c : Fin 16, ∀ value, counterOf x c = some value →
    ∃ segments : STape Seg, absCtr segments (polarity c) = value ∧
      tapes (.inr (.inr (.inr (.inr (.inr (.inr (.inl c)))))) ) = padLeft margin (mapTape encSeg segments)
  places : ∀ (i : Fin 3) place, placeOf x i = some place →
    ∃ (stackTape : STape Γc) (junk : List (Option (Fin 2))),
      PalPeg.ConcreteLocalMachine.Sealed junk ∧ margin ≤ junk.length ∧
        PalPeg.ConcreteLocalMachine.StackTape stackTape
          (place.letters.map (fun letter => some letter) ++ junk) ∧
        tapes (.inr (.inr (.inr (.inr (.inr (.inl i)))))) = padLeft margin (mapTape encCell stackTape)
  mirrors : ∀ (m : Fin 7) value, counterOf x (mirrorSource m) = some value →
    ∃ segments : STape Seg, absCtr segments (polarity (mirrorSource m)) = value ∧
      tapes (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl m)))))))) = padLeft margin (mapTape encSeg segments)
  period : ∀ tape, periodOf x = some tape →
    tapes (.inr (.inr (.inr (.inr (.inl ()))))) = padLeft margin (mapTape encToken (encPeriod tape))
  answer : ∀ tape, answerOf x = some tape →
    tapes (.inr (.inr (.inr (.inl ())))) = padLeft margin (mapTape encProg (encTape tape))

/-- **every head of the machine stands clear of the left edge**, which is what the
sweep of `compStep` asks of a rule with window radius `K ≤ margin`. -/
theorem margin_le_pos {margin : ℕ} {x : State GalilVM} {polarity : Fin 16 → Bool}
    {gap : Fin 4 → Bool} {micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl} {fppLive dpLive : Bool}
    {tapes : Slot → STape Γm} (henc : EncTapes margin x polarity gap micro fppLive dpLive tapes)
    {K : ℕ} (hK : K ≤ margin) (slot : Slot) : K ≤ PalPeg.Local.pos (tapes slot) :=
  hK.trans (henc.margins slot)

/-- **the encoding of the tapes reads seven things and nothing else**: the two program
bundles' tapes, the sixteen counters, the four heads, the three cursors, and the chain's period
and answer tapes.  Two states that agree on those are encoded by the same tapes.  In particular
the control word does not appear, and neither does a program's counter or its halting flag. -/
theorem encTapes_congr (margin : ℕ) (x y : State GalilVM) (polarity : Fin 16 → Bool)
    (gap : Fin 4 → Bool) (micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl) (fppLive dpLive : Bool)
    (tapes : Slot → STape Γm)
    (hfpp : ∀ i, y.vm.fpp.program.config.tapes i = x.vm.fpp.program.config.tapes i)
    (hdp : ∀ i, y.vm.dp.config.tapes i = x.vm.dp.config.tapes i)
    (hcounters : counterOf y = counterOf x) (hheads : headOf y = headOf x)
    (hplaces : placeOf y = placeOf x) (hperiod : periodOf y = periodOf x)
    (hanswer : answerOf y = answerOf x)
    (h : EncTapes margin x polarity gap micro fppLive dpLive tapes) :
    EncTapes margin y polarity gap micro fppLive dpLive tapes where
  idleShape := h.idleShape
  margins := h.margins
  heads := by
    intro v head hhead
    exact h.heads v head (by rw [← congrFun hheads v]; exact hhead)
  idleHead := fun h3 => h.idleHead ((congrFun hheads 3).symm.trans h3)
  fpp := by
    intro i
    rw [hfpp i]
    exact h.fpp i
  dp := by
    intro i
    rw [hdp i]
    exact h.dp i
  counters := by
    intro c value hvalue
    exact h.counters c value (by rw [← congrFun hcounters c]; exact hvalue)
  mirrors := by
    intro m value hvalue
    exact h.mirrors m value (by rw [← congrFun hcounters (mirrorSource m)]; exact hvalue)
  places := by
    intro i pl hpl
    exact h.places i pl (by rw [← congrFun hplaces i]; exact hpl)
  period := by
    intro tape htape
    exact h.period tape (by rw [← hperiod]; exact htape)
  answer := by
    intro tape htape
    exact h.answer tape (by rw [← hanswer]; exact htape)

/-- **the encoding survives a step of the preparation machine.**  The state changes in
one place only — one of the nine tapes of its program — and the machine changes in one place
only — that tape's slot.  Everything else the encoding speaks about (the views, the counters,
the cursors, the chain's two tapes) reads parts of the state the step does not touch, and sits
in slots the rule does not name.  This is what lets a rule realize `markForward`, `markBack`,
`homeStep` and the copy: they are all this one shape. -/
theorem encTapes_fppTapes (margin : ℕ) (x : State GalilVM) (polarity : Fin 16 → Bool)
    (gap : Fin 4 → Bool) (micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl) (fppLive dpLive : Bool)
    (tapes newTapes : Slot → STape Γm)
    (henc : EncTapes margin x polarity gap micro fppLive dpLive tapes)
    (prog : PalPeg.GalilScaffoldControl.Machine 9)
    (ctl : PalPeg.GalilScaffoldController.Control)
    (hmoved : ∀ j : Fin 9, newTapes (progSlotOf fppLive j)
      = padLeft margin (mapTape encProg (encTape (prog.config.tapes j))))
    (hkept : ∀ slot, (∀ j : Fin 9, slot ≠ progSlotOf fppLive j) →
      (∀ k : Fin 9, slot ≠ progSlotOf (!fppLive) k) → newTapes slot = tapes slot)
    (hidleShape : ∀ k : Fin 9, ∃ raw : STape (Fin 9),
      newTapes (progSlotOf (!fppLive) k) = padLeft margin (mapTape encProg raw)) :
    EncTapes margin
      ⟨ctl, {x.vm with fpp := {x.vm.fpp with program := prog}}⟩
      polarity gap micro fppLive dpLive newTapes where
  margins := by
    intro slot
    by_cases hs : ∃ j : Fin 9, slot = progSlotOf fppLive j
    · obtain ⟨j, hj⟩ := hs
      rw [hj, hmoved j, pos_padLeft]
      omega
    · by_cases hidle : ∃ k : Fin 9, slot = progSlotOf (!fppLive) k
      · obtain ⟨k, hk⟩ := hidle
        obtain ⟨raw, hraw⟩ := hidleShape k
        rw [hk, hraw, pos_padLeft]
        omega
      · rw [hkept slot (fun j hj => hs ⟨j, hj⟩) (fun k hk => hidle ⟨k, hk⟩)]
        exact henc.margins slot
  heads := by
    intro v head hhead
    obtain ⟨view, viewTapes, habs, hrep, hslots, hcells, hwf⟩ := henc.heads v head hhead
    exact ⟨view, viewTapes, habs, hrep, fun j => by
      rw [hkept _ (by intro j; cases fppLive <;> cases dpLive <;> simp [progSlotOf, dpSlotOf]) (by intro k; cases fppLive <;> cases dpLive <;> simp [progSlotOf, dpSlotOf]), hslots j], hcells, hwf⟩
  idleHead := by
    intro h3
    obtain ⟨view, viewTapes, hrep, hslots, hcells, hwf⟩ := henc.idleHead h3
    exact ⟨view, viewTapes, hrep, fun j => by
      rw [hkept _ (by intro j; cases fppLive <;> cases dpLive <;> simp [progSlotOf, dpSlotOf]) (by intro k; cases fppLive <;> cases dpLive <;> simp [progSlotOf, dpSlotOf]), hslots j], hcells, hwf⟩
  fpp := hmoved
  dp := by
    intro j
    rw [hkept _ (by intro j; cases fppLive <;> cases dpLive <;> simp [progSlotOf, dpSlotOf]) (by intro k; cases fppLive <;> cases dpLive <;> simp [progSlotOf, dpSlotOf])]
    exact henc.dp j
  counters := by
    intro c value hvalue
    obtain ⟨segments, habs, hslot⟩ := henc.counters c value hvalue
    exact ⟨segments, habs, by rw [hkept _ (by intro j; cases fppLive <;> simp [progSlotOf]) (by intro k; cases fppLive <;> simp [progSlotOf]), hslot]⟩
  mirrors := by
    intro m value hvalue
    obtain ⟨segments, habs, hslot⟩ := henc.mirrors m value hvalue
    exact ⟨segments, habs, by rw [hkept _ (by intro j; cases fppLive <;> simp [progSlotOf]) (by intro k; cases fppLive <;> simp [progSlotOf]), hslot]⟩
  places := by
    intro j place hplace
    obtain ⟨stackTape, junk, hsealed, hlen, hstack, hslot⟩ := henc.places j place hplace
    exact ⟨stackTape, junk, hsealed, hlen, hstack, by rw [hkept _ (by intro j; cases fppLive <;> simp [progSlotOf]) (by intro k; cases fppLive <;> simp [progSlotOf]), hslot]⟩
  idleShape := hidleShape
  period := by
    intro tape htape
    rw [hkept _ (by intro j; cases fppLive <;> cases dpLive <;> simp [progSlotOf, dpSlotOf]) (by intro k; cases fppLive <;> cases dpLive <;> simp [progSlotOf, dpSlotOf])]
    exact henc.period tape htape
  answer := by
    intro tape htape
    rw [hkept _ (by intro j; cases fppLive <;> cases dpLive <;> simp [progSlotOf, dpSlotOf]) (by intro k; cases fppLive <;> cases dpLive <;> simp [progSlotOf, dpSlotOf])]
    exact henc.answer tape htape

/-- **the tick of the fallback copy, on the tapes.**  Three components move at once: one tape of
the preparation program, the work counter, and the walker.  Everything else the encoding speaks
about is where it was, and the sign of the work counter is the only polarity that moves. -/
theorem encTapes_copyOne (margin : ℕ) (x : State GalilVM) (polarity newPolarity : Fin 16 → Bool)
    (gap : Fin 4 → Bool) (micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl)
    (fppLive dpLive : Bool) (tapes newTapes : Slot → STape Γm)
    (henc : EncTapes margin x polarity gap micro fppLive dpLive tapes)
    (ctl : PalPeg.GalilScaffoldController.Control) (a : Fin 3)
    (hpolarity : ∀ c : Fin 16, c ≠ 9 → newPolarity c = polarity c)
    (segments : STape Seg)
    (hwork : absCtr segments (newPolarity 9) = PalPeg.GalilScaffoldCounter.dec x.vm.fpp.work)
    (hcounterTape : newTapes (counterSlot 9) = padLeft margin (mapTape encSeg segments))
    (stackTape : STape PalPeg.CloseoutCoreStep.Γc) (junk : List (Option (Fin 2)))
    (hsealed : PalPeg.ConcreteLocalMachine.Sealed junk) (hjunk : margin ≤ junk.length)
    (hstack : PalPeg.ConcreteLocalMachine.StackTape stackTape
      ((PalPeg.GalilScaffoldPlace.left x.vm.fpp.walker).letters.map (fun letter => some letter)
        ++ junk))
    (hplaceTape : newTapes (placeSlot 1) = padLeft margin (mapTape encCell stackTape))
    (hprog : newTapes (progSlotOf fppLive 7)
      = padLeft margin (mapTape encProg (encTape
          (PalPeg.GalilScaffoldTape.moveRight (PalPeg.GalilScaffoldTape.write
            (x.vm.fpp.program.config.tapes 7) (PalPeg.GalilFppPreparation.symbol a))))))
    (hprogOther : ∀ j : Fin 9, j ≠ 7 →
      newTapes (progSlotOf fppLive j) = tapes (progSlotOf fppLive j))
    (hkept : ∀ slot, (∀ j : Fin 9, slot ≠ progSlotOf fppLive j) → slot ≠ counterSlot 9 →
      slot ≠ placeSlot 1 → (∀ k : Fin 9, slot ≠ progSlotOf (!fppLive) k) →
      newTapes slot = tapes slot)
    (hidleShape : ∀ k : Fin 9, ∃ raw : STape (Fin 9),
      newTapes (progSlotOf (!fppLive) k) = padLeft margin (mapTape encProg raw)) :
    EncTapes margin
      ⟨ctl, {x.vm with fpp := {x.vm.fpp with program := PalPeg.GalilScaffoldChainInputSupply.FppControl.tape x.vm.fpp 7 (fun t => PalPeg.GalilScaffoldTape.moveRight (PalPeg.GalilScaffoldTape.write t (PalPeg.GalilFppPreparation.symbol a))), work := PalPeg.GalilScaffoldCounter.dec x.vm.fpp.work, walker := PalPeg.GalilScaffoldPlace.left x.vm.fpp.walker}}⟩
      newPolarity gap micro fppLive dpLive newTapes where
  margins := by
    intro slot
    by_cases hs : ∃ j : Fin 9, slot = progSlotOf fppLive j
    · obtain ⟨j, hj⟩ := hs
      subst hj
      by_cases hj7 : j = 7
      · subst hj7
        rw [hprog, pos_padLeft]
        omega
      · rw [hprogOther j hj7]
        exact henc.margins _
    · by_cases hidle : ∃ k : Fin 9, slot = progSlotOf (!fppLive) k
      · obtain ⟨k, hk⟩ := hidle
        obtain ⟨raw, hraw⟩ := hidleShape k
        rw [hk, hraw, pos_padLeft]
        omega
      · by_cases hc : slot = counterSlot 9
        · rw [hc, hcounterTape, pos_padLeft]
          omega
        · by_cases hp : slot = placeSlot 1
          · rw [hp, hplaceTape, pos_padLeft]
            omega
          · rw [hkept slot (fun j hj => hs ⟨j, hj⟩) hc hp (fun k hk => hidle ⟨k, hk⟩)]
            exact henc.margins slot
  heads := by
    intro v head hhead
    obtain ⟨view, viewTapes, habs, hrep, hslots, hcells, hwf⟩ := henc.heads v head hhead
    exact ⟨view, viewTapes, habs, hrep, fun j => by
      rw [hkept _ (by intro j; cases fppLive <;> simp [progSlotOf]) (by simp) (by simp)
        (by intro k; cases fppLive <;> simp [progSlotOf]), hslots j], hcells, hwf⟩
  idleHead := by
    intro h3
    obtain ⟨view, viewTapes, hrep, hslots, hcells, hwf⟩ := henc.idleHead h3
    exact ⟨view, viewTapes, hrep, fun j => by
      rw [hkept _ (by intro j; cases fppLive <;> simp [progSlotOf]) (by simp) (by simp)
        (by intro k; cases fppLive <;> simp [progSlotOf]), hslots j], hcells, hwf⟩
  fpp := by
    intro j
    by_cases hj7 : j = 7
    · subst hj7
      rw [hprog]
      rfl
    · have hj : (PalPeg.GalilScaffoldChainInputSupply.FppControl.tape x.vm.fpp 7 (fun t => PalPeg.GalilScaffoldTape.moveRight (PalPeg.GalilScaffoldTape.write t (PalPeg.GalilFppPreparation.symbol a)))).config.tapes j
          = x.vm.fpp.program.config.tapes j := by
        rw [fppTape_tapes, Function.update_of_ne hj7]
      rw [hprogOther j hj7, henc.fpp j]
      dsimp only
      rw [hj]
  dp := by
    intro j
    rw [hkept _ (by intro j; cases fppLive <;> cases dpLive <;> simp [progSlotOf, dpSlotOf])
      (by cases dpLive <;> simp [dpSlotOf]) (by cases dpLive <;> simp [dpSlotOf])
      (by intro k; cases fppLive <;> cases dpLive <;> simp [progSlotOf, dpSlotOf])]
    exact henc.dp j
  counters := by
    intro c value hvalue
    by_cases hc9 : c = 9
    · subst hc9
      exact ⟨segments, by rw [hwork]; exact Option.some.inj hvalue, hcounterTape⟩
    · have hold : counterOf x c = some value := by
        rw [← hvalue]
        fin_cases c <;> first | exact absurd rfl hc9 | rfl
      obtain ⟨seg, habs, hslot⟩ := henc.counters c value hold
      exact ⟨seg, by rw [hpolarity c hc9]; exact habs, by
        rw [hkept _ (by intro j; cases fppLive <;> simp [progSlotOf])
          (by simpa using fun h => hc9 h) (by simp)
          (by intro k; cases fppLive <;> simp [progSlotOf]), hslot]⟩
  mirrors := by
    intro m value hvalue
    have hne : mirrorSource m ≠ 9 := by fin_cases m <;> decide
    have hold : counterOf x (mirrorSource m) = some value := by
      rw [← hvalue]
      fin_cases m <;> rfl
    obtain ⟨seg, habs, hslot⟩ := henc.mirrors m value hold
    exact ⟨seg, by rw [hpolarity _ hne]; exact habs, by
      rw [hkept _ (by intro j; cases fppLive <;> simp [progSlotOf]) (by simp) (by simp), hslot]
      intro k
      cases fppLive <;> simp [progSlotOf]⟩
  places := by
    intro i pl hpl
    by_cases hi1 : i = 1
    · subst hi1
      exact ⟨stackTape, junk, hsealed, hjunk, (Option.some.inj hpl) ▸ hstack, hplaceTape⟩
    · have hold : placeOf x i = some pl := by
        rw [← hpl]
        fin_cases i <;> first | exact absurd rfl hi1 | rfl
      obtain ⟨st, jk, hsl, hln, hstk, hslot⟩ := henc.places i pl hold
      exact ⟨st, jk, hsl, hln, hstk, by
        rw [hkept _ (by intro j; cases fppLive <;> simp [progSlotOf]) (by simp)
          (by simpa using fun h => hi1 h)
          (by intro k; cases fppLive <;> simp [progSlotOf]), hslot]⟩
  idleShape := hidleShape
  period := by
    intro tape htape
    rw [hkept _ (by intro j; cases fppLive <;> simp [progSlotOf]) (by simp) (by simp)
      (by intro k; cases fppLive <;> simp [progSlotOf])]
    exact henc.period tape htape
  answer := by
    intro tape htape
    rw [hkept _ (by intro j; cases fppLive <;> simp [progSlotOf]) (by simp) (by simp)
      (by intro k; cases fppLive <;> simp [progSlotOf])]
    exact henc.answer tape htape

/-- **one tick of the rewind, on the tapes.**  Three components move: the marks tape of the
preparation program, the left input head, and the counter of the length.  The head's new view is
the caller's to supply — `headSlots_left` supplies it — and everything else the encoding speaks
about is where it was. -/
theorem encTapes_rewindOne (margin : ℕ) (x : State GalilVM) (polarity newPolarity : Fin 16 → Bool)
    (gap newGap : Fin 4 → Bool) (micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl)
    (fppLive dpLive : Bool) (tapes newTapes : Slot → STape Γm)
    (henc : EncTapes margin x polarity gap micro fppLive dpLive tapes)
    (ctl : PalPeg.GalilScaffoldController.Control)
    (hheads : ∃ (view : PalPeg.LocalInputView.InputView)
        (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc),
      PalPeg.LocalArrival.absHead' view []
          = PalPeg.GalilScaffoldInputHead.left x.vm.left ∧
        PalPeg.ConcreteLocalMachine.ViewRep margin view (newGap 0) (micro 0) viewTapes ∧
        (∀ i, newTapes (headSlot 0 i) = mapTape encCell (viewTapes i)) ∧
          PalPeg.LocalViewCells.ViewCells view ∧ PalPeg.LocalInputView.WF view)
    (hgapOther : ∀ v : Fin 4, v ≠ 0 → newGap v = gap v)
    (hpolarity : ∀ c : Fin 16, c ≠ 3 → newPolarity c = polarity c)
    (segments : STape Seg)
    (hlength : absCtr segments (newPolarity 3)
      = PalPeg.GalilScaffoldCounter.inc x.vm.length)
    (hcounterTape : newTapes (counterSlot 3) = padLeft margin (mapTape encSeg segments))
    (hmirrorLen : ∀ m : Fin 7, mirrorSource m = 3 → ∃ seg : STape Seg,
      absCtr seg (newPolarity 3) = PalPeg.GalilScaffoldCounter.inc x.vm.length
        ∧ newTapes (mirrorSlot m) = padLeft margin (mapTape encSeg seg))
    (hprog : newTapes (progSlotOf fppLive 8)
      = padLeft margin (mapTape encProg (encTape
          (PalPeg.GalilScaffoldTape.moveLeft (x.vm.fpp.program.config.tapes 8)))))
    (hprogOther : ∀ j : Fin 9, j ≠ 8 →
      newTapes (progSlotOf fppLive j) = tapes (progSlotOf fppLive j))
    (hkept : ∀ slot, (∀ j : Fin 9, slot ≠ progSlotOf fppLive j) → slot ≠ counterSlot 3 →
      (∀ m : Fin 7, mirrorSource m = 3 → slot ≠ mirrorSlot m) →
      (∀ i : Fin 12, slot ≠ headSlot 0 i) →
      (∀ k : Fin 9, slot ≠ progSlotOf (!fppLive) k) → newTapes slot = tapes slot)
    (hmarginHead : ∀ i : Fin 12, margin ≤ PalPeg.Local.pos (newTapes (headSlot 0 i)))
    (hidleShape : ∀ k : Fin 9, ∃ raw : STape (Fin 9),
      newTapes (progSlotOf (!fppLive) k) = padLeft margin (mapTape encProg raw)) :
    EncTapes margin
      ⟨ctl, {x.vm with fpp := PalPeg.GalilScaffoldChainInputSupply.markStep x.vm.fpp PalPeg.GalilScaffoldTape.moveLeft, left := PalPeg.GalilScaffoldInputHead.left x.vm.left, length := PalPeg.GalilScaffoldCounter.inc x.vm.length}⟩
      newPolarity newGap micro fppLive dpLive newTapes where
  margins := by
    intro slot
    by_cases hs : ∃ j : Fin 9, slot = progSlotOf fppLive j
    · obtain ⟨j, hj⟩ := hs
      subst hj
      by_cases hj8 : j = 8
      · subst hj8
        rw [hprog, pos_padLeft]
        omega
      · rw [hprogOther j hj8]
        exact henc.margins _
    · by_cases hidle : ∃ k : Fin 9, slot = progSlotOf (!fppLive) k
      · obtain ⟨k, hk⟩ := hidle
        obtain ⟨raw, hraw⟩ := hidleShape k
        rw [hk, hraw, pos_padLeft]
        omega
      · by_cases hc : slot = counterSlot 3
        · rw [hc, hcounterTape, pos_padLeft]
          omega
        · by_cases hm : ∃ m : Fin 7, mirrorSource m = 3 ∧ slot = mirrorSlot m
          · obtain ⟨m, hsrc, hmslot⟩ := hm
            obtain ⟨seg, -, hseg⟩ := hmirrorLen m hsrc
            rw [hmslot, hseg, pos_padLeft]
            omega
          · by_cases hh : ∃ i : Fin 12, slot = headSlot 0 i
            · obtain ⟨i, hi⟩ := hh
              rw [hi]
              exact hmarginHead i
            · rw [hkept slot (fun j hj => hs ⟨j, hj⟩) hc
                (fun m hsrc hmslot => hm ⟨m, hsrc, hmslot⟩) (fun i hi => hh ⟨i, hi⟩)
                (fun k hk => hidle ⟨k, hk⟩)]
              exact henc.margins slot
  heads := by
    intro v head hhead
    by_cases hv0 : v = 0
    · subst hv0
      obtain ⟨view, viewTapes, habs, hrep, hslots, hcells, hwf⟩ := hheads
      exact ⟨view, viewTapes, (Option.some.inj hhead) ▸ habs, hrep, hslots, hcells, hwf⟩
    · have hold : headOf x v = some head := by
        rw [← hhead]
        fin_cases v <;> first | exact absurd rfl hv0 | rfl
      obtain ⟨view, viewTapes, habs, hrep, hslots, hcells, hwf⟩ := henc.heads v head hold
      refine ⟨view, viewTapes, habs, ?_, ?_, hcells, hwf⟩
      · rw [hgapOther v hv0]
        exact hrep
      · intro i
        rw [hkept _ (by intro j; cases fppLive <;> simp [progSlotOf]) (by simp)
          (by intro m _ hEq; exact (headSlot_ne_mirrorSlot v i m) hEq)
          (by
            intro k hEq
            have hpair : v = 0 ∧ i = k := by simpa [headSlot] using hEq
            exact hv0 hpair.1)
          (by intro k; cases fppLive <;> simp [progSlotOf]), hslots i]
  idleHead := by
    intro h3
    obtain ⟨view, viewTapes, hrep, hslots, hcells, hwf⟩ := henc.idleHead (by rw [← h3]; rfl)
    refine ⟨view, viewTapes, ?_, ?_, hcells, hwf⟩
    · rw [hgapOther 3 (by decide)]
      exact hrep
    · intro i
      rw [hkept _ (by intro j; cases fppLive <;> simp [progSlotOf]) (by simp)
        (by intro m _ hEq; exact (headSlot_ne_mirrorSlot 3 i m) hEq)
        (by
          intro k hEq
          have hpair : (3 : Fin 4) = 0 ∧ i = k := by simpa [headSlot] using hEq
          exact absurd hpair.1 (by decide))
        (by intro k; cases fppLive <;> simp [progSlotOf]), hslots i]
  fpp := by
    intro j
    by_cases hj8 : j = 8
    · subst hj8
      rw [hprog]
      rfl
    · have hj : (PalPeg.GalilScaffoldChainInputSupply.markStep x.vm.fpp PalPeg.GalilScaffoldTape.moveLeft).program.config.tapes j
          = x.vm.fpp.program.config.tapes j := by
        show (PalPeg.GalilScaffoldChainInputSupply.FppControl.tape x.vm.fpp 8 PalPeg.GalilScaffoldTape.moveLeft).config.tapes j = _
        rw [fppTape_tapes, Function.update_of_ne hj8]
      rw [hprogOther j hj8, henc.fpp j]
      dsimp only
      rw [hj]
  dp := by
    intro j
    rw [hkept _ (by intro j; cases fppLive <;> cases dpLive <;> simp [progSlotOf, dpSlotOf])
      (by cases dpLive <;> simp [dpSlotOf])
      (by intro m _; cases dpLive <;> simp [dpSlotOf])
      (by intro i; cases dpLive <;> simp [dpSlotOf])
      (by intro k; cases fppLive <;> cases dpLive <;> simp [progSlotOf, dpSlotOf])]
    exact henc.dp j
  counters := by
    intro c value hvalue
    by_cases hc3 : c = 3
    · subst hc3
      exact ⟨segments, by rw [hlength]; exact Option.some.inj hvalue, hcounterTape⟩
    · have hold : counterOf x c = some value := by
        rw [← hvalue]
        fin_cases c <;> first | exact absurd rfl hc3 | rfl
      obtain ⟨seg, habs, hslot⟩ := henc.counters c value hold
      exact ⟨seg, by rw [hpolarity c hc3]; exact habs, by
        rw [hkept _ (by intro j; cases fppLive <;> simp [progSlotOf])
          (by simpa using fun h => hc3 h)
          (by intro m _ hEq; exact (counterSlot_ne_mirrorSlot c m) hEq) (by simp)
          (by intro k; cases fppLive <;> simp [progSlotOf]), hslot]⟩
  mirrors := by
    intro m value hvalue
    by_cases hsrc : mirrorSource m = 3
    · obtain ⟨seg, habs, hslot⟩ := hmirrorLen m hsrc
      have hval : PalPeg.GalilScaffoldCounter.inc x.vm.length = value := by
        rw [hsrc] at hvalue
        exact Option.some.inj hvalue
      exact ⟨seg, by rw [hsrc, habs, hval], hslot⟩
    · have hne : mirrorSource m ≠ 3 := hsrc
      have hold : counterOf x (mirrorSource m) = some value := by
        rw [← hvalue]
        fin_cases m <;> first | exact absurd rfl hne | rfl
      have hmirrorKept : newTapes (mirrorSlot m) = tapes (mirrorSlot m) :=
        hkept _ (by intro j; cases fppLive <;> simp [progSlotOf]) (by simp)
          (by
            intro m' hsrc' hEq
            have hmm : m = m' := by simpa [mirrorSlot] using hEq
            exact hne (by rw [hmm]; exact hsrc'))
          (by simp)
          (by intro k; cases fppLive <;> simp [progSlotOf])
      obtain ⟨seg, habs, hslot⟩ := henc.mirrors m value hold
      exact ⟨seg, by rw [hpolarity _ hne]; exact habs, by rw [hmirrorKept, hslot]⟩
  places := by
    intro i pl hpl
    obtain ⟨st, jk, hsl, hln, hstk, hslot⟩ := henc.places i pl hpl
    exact ⟨st, jk, hsl, hln, hstk, by
      rw [hkept _ (by intro j; cases fppLive <;> simp [progSlotOf]) (by simp)
        (by intro m _; simp) (by simp)
        (by intro k; cases fppLive <;> simp [progSlotOf]), hslot]⟩
  idleShape := hidleShape
  period := by
    intro tape htape
    rw [hkept _ (by intro j; cases fppLive <;> simp [progSlotOf]) (by simp)
      (by intro m _; simp) (by simp)
      (by intro k; cases fppLive <;> simp [progSlotOf])]
    exact henc.period tape htape
  answer := by
    intro tape htape
    rw [hkept _ (by intro j; cases fppLive <;> simp [progSlotOf]) (by simp)
      (by intro m _; simp) (by simp)
      (by intro k; cases fppLive <;> simp [progSlotOf])]
    exact henc.answer tape htape

/-- **a tick that moves one input head and nothing else the encoding speaks about.**  The
caller supplies the head's new view and the twelve tapes that represent it; everything else is
carried across.  Stated for two states that agree everywhere but at that head. -/
theorem encTapes_headStep (margin : ℕ) (x y : State GalilVM) (polarity : Fin 16 → Bool)
    (gap newGap : Fin 4 → Bool) (micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl)
    (fppLive dpLive : Bool) (tapes newTapes : Slot → STape Γm)
    (henc : EncTapes margin x polarity gap micro fppLive dpLive tapes)
    (v : Fin 4) (head : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hhead : headOf y v = some head)
    (hother : ∀ v' : Fin 4, v' ≠ v → headOf y v' = headOf x v')
    (hcounters : counterOf y = counterOf x) (hplaces : placeOf y = placeOf x)
    (hfpp : ∀ i, y.vm.fpp.program.config.tapes i = x.vm.fpp.program.config.tapes i)
    (hdp : ∀ i, y.vm.dp.config.tapes i = x.vm.dp.config.tapes i)
    (hperiod : periodOf y = periodOf x) (hanswer : answerOf y = answerOf x)
    (hgapOther : ∀ v' : Fin 4, v' ≠ v → newGap v' = gap v')
    (view : PalPeg.LocalInputView.InputView)
    (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (habsView : PalPeg.LocalArrival.absHead' view [] = head)
    (hrep : PalPeg.ConcreteLocalMachine.ViewRep margin view (newGap v) (micro v) viewTapes)
    (hcells : PalPeg.LocalViewCells.ViewCells view) (hwf : PalPeg.LocalInputView.WF view)
    (hslots : ∀ i, newTapes (headSlot v i) = mapTape encCell (viewTapes i))
    (hkept : ∀ slot, (∀ i : Fin 12, slot ≠ headSlot v i) → newTapes slot = tapes slot)
    (hmargin : ∀ i : Fin 12, margin ≤ PalPeg.Local.pos (newTapes (headSlot v i))) :
    EncTapes margin y polarity newGap micro fppLive dpLive newTapes where
  margins := by
    intro slot
    by_cases hh : ∃ i : Fin 12, slot = headSlot v i
    · obtain ⟨i, hi⟩ := hh
      rw [hi]
      exact hmargin i
    · rw [hkept slot (fun i hi => hh ⟨i, hi⟩)]
      exact henc.margins slot
  heads := by
    intro v' head' hhead'
    by_cases hv : v' = v
    · subst hv
      exact ⟨view, viewTapes, (Option.some.inj (hhead.symm.trans hhead')) ▸ habsView, hrep,
        hslots, hcells, hwf⟩
    · obtain ⟨view', viewTapes', habs', hrep', hslots', hcells', hwf'⟩ :=
        henc.heads v' head' (by rw [← hother v' hv]; exact hhead')
      refine ⟨view', viewTapes', habs', ?_, ?_, hcells', hwf'⟩
      · rw [hgapOther v' hv]
        exact hrep'
      · intro i
        rw [hkept _ (by
          intro k hEq
          have hpair : v' = v ∧ i = k := by simpa [headSlot] using hEq
          exact hv hpair.1), hslots' i]
  idleHead := by
    intro h3
    by_cases hv3 : v = 3
    · subst hv3
      exact ⟨view, viewTapes, hrep, hslots, hcells, hwf⟩
    · obtain ⟨view', viewTapes', hrep', hslots', hcells', hwf'⟩ :=
        henc.idleHead (by rw [← hother 3 (fun h => hv3 h.symm)]; exact h3)
      refine ⟨view', viewTapes', ?_, ?_, hcells', hwf'⟩
      · rw [hgapOther 3 (fun h => hv3 h.symm)]
        exact hrep'
      · intro i
        rw [hkept _ (by
          intro k hEq
          have hpair : (3 : Fin 4) = v ∧ i = k := by simpa [headSlot] using hEq
          exact hv3 hpair.1.symm), hslots' i]
  fpp := by
    intro i
    rw [hkept _ (by intro k; cases fppLive <;> simp [progSlotOf]), henc.fpp i, hfpp i]
  dp := by
    intro i
    rw [hkept _ (by intro k; cases dpLive <;> simp [dpSlotOf]), henc.dp i, hdp i]
  idleShape := by
    intro i
    obtain ⟨raw, hraw⟩ := henc.idleShape i
    exact ⟨raw, by rw [hkept _ (by intro k; cases fppLive <;> simp [progSlotOf]), hraw]⟩
  counters := by
    intro c value hvalue
    obtain ⟨seg, habsOld, hslotOld⟩ :=
      henc.counters c value (by rw [← congrFun hcounters c]; exact hvalue)
    exact ⟨seg, habsOld, by rw [hkept _ (by intro k; simp), hslotOld]⟩
  mirrors := by
    intro m value hvalue
    obtain ⟨seg, habsOld, hslotOld⟩ :=
      henc.mirrors m value (by rw [← congrFun hcounters _]; exact hvalue)
    exact ⟨seg, habsOld, by rw [hkept _ (by intro k; simp), hslotOld]⟩
  places := by
    intro i pl hpl
    obtain ⟨st, jk, hsl, hln, hstk, hslotOld⟩ :=
      henc.places i pl (by rw [← congrFun hplaces i]; exact hpl)
    exact ⟨st, jk, hsl, hln, hstk, by rw [hkept _ (by intro k; simp), hslotOld]⟩
  period := by
    intro tape htape
    rw [hkept _ (by intro k; simp)]
    exact henc.period tape (by rw [← hperiod]; exact htape)
  answer := by
    intro tape htape
    rw [hkept _ (by intro k; simp)]
    exact henc.answer tape (by rw [← hanswer]; exact htape)

/-- **a tick that changes one counter and nothing else the encoding speaks about.**  A counter
may be mirrored — three of the five mirror slots hold copies of the radius — so the mirrors of
the counter that moved are written too, with the same segments.  Stated for two states that agree
everywhere but at that counter, so that a branch which moves several components can apply it once
for each of them. -/
theorem encTapes_counterStep (margin : ℕ) (x y : State GalilVM)
    (polarity newPolarity : Fin 16 → Bool) (gap : Fin 4 → Bool)
    (micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl) (fppLive dpLive : Bool)
    (tapes newTapes : Slot → STape Γm)
    (henc : EncTapes margin x polarity gap micro fppLive dpLive tapes)
    (c : Fin 16) (value : PalPeg.GalilScaffoldCounter.Counter)
    (hcounter : counterOf y c = some value)
    (hother : ∀ c' : Fin 16, c' ≠ c → counterOf y c' = counterOf x c')
    (hheads : headOf y = headOf x) (hplaces : placeOf y = placeOf x)
    (hfpp : ∀ i, y.vm.fpp.program.config.tapes i = x.vm.fpp.program.config.tapes i)
    (hdp : ∀ i, y.vm.dp.config.tapes i = x.vm.dp.config.tapes i)
    (hperiod : periodOf y = periodOf x) (hanswer : answerOf y = answerOf x)
    (hpolOther : ∀ c' : Fin 16, c' ≠ c → newPolarity c' = polarity c')
    (segments : STape Seg) (habs : absCtr segments (newPolarity c) = value)
    (hslot : newTapes (counterSlot c) = padLeft margin (mapTape encSeg segments))
    (hmirrorSlot : ∀ m : Fin 7, mirrorSource m = c → ∃ seg : STape Seg,
      absCtr seg (newPolarity c) = value
        ∧ newTapes (mirrorSlot m) = padLeft margin (mapTape encSeg seg))
    (hkept : ∀ slot, slot ≠ counterSlot c →
      (∀ m : Fin 7, mirrorSource m = c → slot ≠ mirrorSlot m) →
      newTapes slot = tapes slot) :
    EncTapes margin y newPolarity gap micro fppLive dpLive newTapes where
  margins := by
    intro slot
    by_cases hc : slot = counterSlot c
    · rw [hc, hslot, pos_padLeft]
      omega
    · by_cases hm : ∃ m : Fin 7, mirrorSource m = c ∧ slot = mirrorSlot m
      · obtain ⟨m, hsrc, hmm⟩ := hm
        obtain ⟨seg, -, hseg⟩ := hmirrorSlot m hsrc
        rw [hmm, hseg, pos_padLeft]
        omega
      · rw [hkept slot hc (fun m hsrc hEq => hm ⟨m, hsrc, hEq⟩)]
        exact henc.margins slot
  heads := by
    intro v head hhead
    obtain ⟨view, viewTapes, habsView, hrep, hslots, hcells⟩ :=
      henc.heads v head (by rw [← congrFun hheads v]; exact hhead)
    exact ⟨view, viewTapes, habsView, hrep, fun i => by
      rw [hkept _ (by simp) (fun m _ => by simp), hslots i], hcells⟩
  idleHead := by
    intro h3
    obtain ⟨view, viewTapes, hrep, hslots, hcells⟩ :=
      henc.idleHead ((congrFun hheads 3).symm.trans h3)
    exact ⟨view, viewTapes, hrep, fun i => by
      rw [hkept _ (by simp) (fun m _ => by simp), hslots i], hcells⟩
  fpp := by
    intro i
    rw [hkept _ (by cases fppLive <;> simp [progSlotOf])
      (fun m _ => by cases fppLive <;> simp [progSlotOf]), henc.fpp i, hfpp i]
  dp := by
    intro i
    rw [hkept _ (by cases dpLive <;> simp [dpSlotOf])
      (fun m _ => by cases dpLive <;> simp [dpSlotOf]), henc.dp i, hdp i]
  idleShape := by
    intro i
    obtain ⟨raw, hraw⟩ := henc.idleShape i
    exact ⟨raw, by
      rw [hkept _ (by cases fppLive <;> simp [progSlotOf])
        (fun m _ => by cases fppLive <;> simp [progSlotOf]), hraw]⟩
  counters := by
    intro c' value' hvalue'
    by_cases hc : c' = c
    · subst hc
      exact ⟨segments, by rw [habs]; exact Option.some.inj (hcounter.symm.trans hvalue'), hslot⟩
    · obtain ⟨seg, habsOld, hslotOld⟩ :=
        henc.counters c' value' (by rw [← hother c' hc]; exact hvalue')
      exact ⟨seg, by rw [hpolOther c' hc]; exact habsOld, by
        rw [hkept _ (fun h => hc (by simpa using h)) (fun m _ => by simp), hslotOld]⟩
  mirrors := by
    intro m value' hvalue'
    by_cases hsrc : mirrorSource m = c
    · obtain ⟨seg, habsSeg, hseg⟩ := hmirrorSlot m hsrc
      refine ⟨seg, ?_, hseg⟩
      rw [hsrc, habsSeg]
      rw [hsrc] at hvalue'
      exact Option.some.inj (hcounter.symm.trans hvalue')
    · obtain ⟨seg, habsOld, hslotOld⟩ :=
        henc.mirrors m value' (by rw [← hother _ hsrc]; exact hvalue')
      exact ⟨seg, by rw [hpolOther _ hsrc]; exact habsOld, by
        rw [hkept _ (by simp) (fun m' hsrc' hEq => by
          rw [show m = m' from by simpa using hEq] at hsrc
          exact hsrc hsrc'), hslotOld]⟩
  places := by
    intro i pl hpl
    obtain ⟨st, jk, hsl, hln, hstk, hslotOld⟩ :=
      henc.places i pl (by rw [← congrFun hplaces i]; exact hpl)
    exact ⟨st, jk, hsl, hln, hstk, by
      rw [hkept _ (by simp) (fun m _ => by simp), hslotOld]⟩
  period := by
    intro tape htape
    rw [hkept _ (by simp) (fun m _ => by simp)]
    exact henc.period tape (by rw [← hperiod]; exact htape)
  answer := by
    intro tape htape
    rw [hkept _ (by simp) (fun m _ => by simp)]
    exact henc.answer tape (by rw [← hanswer]; exact htape)

/-- **the paired step of the rewind, on the tapes.**  It is the single step with the centre head
and the radius added, so it is proved by adding them: the radius first, with its three mirrors,
then the centre head, then the single step's own transport on top. -/
theorem encTapes_rewindPair (margin : ℕ) (x : State GalilVM) (polarity newPolarity : Fin 16 → Bool)
    (gap newGap : Fin 4 → Bool) (micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl)
    (fppLive dpLive : Bool) (tapes newTapes : Slot → STape Γm)
    (henc : EncTapes margin x polarity gap micro fppLive dpLive tapes)
    (ctl : PalPeg.GalilScaffoldController.Control)
    (viewLeft : PalPeg.LocalInputView.InputView)
    (viewTapesLeft : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (habsLeft : PalPeg.LocalArrival.absHead' viewLeft []
      = PalPeg.GalilScaffoldInputHead.left x.vm.left)
    (hrepLeft : PalPeg.ConcreteLocalMachine.ViewRep margin viewLeft (newGap 0) (micro 0)
      viewTapesLeft)
    (hslotsLeft : ∀ i, newTapes (headSlot 0 i) = mapTape encCell (viewTapesLeft i))
    (hcellsLeft : PalPeg.LocalViewCells.ViewCells viewLeft) (hwfLeft : PalPeg.LocalInputView.WF viewLeft)
    (viewCentre : PalPeg.LocalInputView.InputView)
    (viewTapesCentre : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (habsCentre : PalPeg.LocalArrival.absHead' viewCentre []
      = PalPeg.GalilScaffoldInputHead.left x.vm.center)
    (hrepCentre : PalPeg.ConcreteLocalMachine.ViewRep margin viewCentre (newGap 1) (micro 1)
      viewTapesCentre)
    (hslotsCentre : ∀ i, newTapes (headSlot 1 i) = mapTape encCell (viewTapesCentre i))
    (hcellsCentre : PalPeg.LocalViewCells.ViewCells viewCentre) (hwfCentre : PalPeg.LocalInputView.WF viewCentre)
    (hgapOther : ∀ v : Fin 4, v ≠ 0 → v ≠ 1 → newGap v = gap v)
    (hpolarity : ∀ c : Fin 16, c ≠ 3 → c ≠ 2 → newPolarity c = polarity c)
    (segLen : STape Seg)
    (hlength : absCtr segLen (newPolarity 3) = PalPeg.GalilScaffoldCounter.inc x.vm.length)
    (hcounterLen : newTapes (counterSlot 3) = padLeft margin (mapTape encSeg segLen))
    (hmirrorLen : ∀ m : Fin 7, mirrorSource m = 3 → ∃ seg : STape Seg,
      absCtr seg (newPolarity 3) = PalPeg.GalilScaffoldCounter.inc x.vm.length
        ∧ newTapes (mirrorSlot m) = padLeft margin (mapTape encSeg seg))
    (segRad : STape Seg)
    (hradius : absCtr segRad (newPolarity 2) = PalPeg.GalilScaffoldCounter.inc x.vm.radius)
    (hcounterRad : newTapes (counterSlot 2) = padLeft margin (mapTape encSeg segRad))
    (hmirrorRad : ∀ m : Fin 7, mirrorSource m = 2 → ∃ seg : STape Seg,
      absCtr seg (newPolarity 2) = PalPeg.GalilScaffoldCounter.inc x.vm.radius
        ∧ newTapes (mirrorSlot m) = padLeft margin (mapTape encSeg seg))
    (hprog : newTapes (progSlotOf fppLive 8)
      = padLeft margin (mapTape encProg (encTape
          (PalPeg.GalilScaffoldTape.moveLeft (x.vm.fpp.program.config.tapes 8)))))
    (hprogOther : ∀ j : Fin 9, j ≠ 8 →
      newTapes (progSlotOf fppLive j) = tapes (progSlotOf fppLive j))
    (hkept : ∀ slot, (∀ j : Fin 9, slot ≠ progSlotOf fppLive j) → slot ≠ counterSlot 3 →
      slot ≠ counterSlot 2 → (∀ m : Fin 7, mirrorSource m = 2 → slot ≠ mirrorSlot m) →
      (∀ m : Fin 7, mirrorSource m = 3 → slot ≠ mirrorSlot m) →
      (∀ i : Fin 12, slot ≠ headSlot 0 i) → (∀ i : Fin 12, slot ≠ headSlot 1 i) →
      (∀ k : Fin 9, slot ≠ progSlotOf (!fppLive) k) → newTapes slot = tapes slot)
    (hmarginLeft : ∀ i : Fin 12, margin ≤ PalPeg.Local.pos (newTapes (headSlot 0 i)))
    (hmarginCentre : ∀ i : Fin 12, margin ≤ PalPeg.Local.pos (newTapes (headSlot 1 i)))
    (hidleShape : ∀ k : Fin 9, ∃ raw : STape (Fin 9),
      newTapes (progSlotOf (!fppLive) k) = padLeft margin (mapTape encProg raw)) :
    EncTapes margin
      ⟨ctl, {x.vm with fpp := PalPeg.GalilScaffoldChainInputSupply.markStep x.vm.fpp PalPeg.GalilScaffoldTape.moveLeft, left := PalPeg.GalilScaffoldInputHead.left x.vm.left, length := PalPeg.GalilScaffoldCounter.inc x.vm.length, center := PalPeg.GalilScaffoldInputHead.left x.vm.center, radius := PalPeg.GalilScaffoldCounter.inc x.vm.radius}⟩
      newPolarity newGap micro fppLive dpLive newTapes := by
  classical
  have hradStep := encTapes_counterStep margin x
    ⟨x.ctl, {x.vm with radius := PalPeg.GalilScaffoldCounter.inc x.vm.radius}⟩
    polarity (fun c => if c = 2 then newPolarity 2 else polarity c) gap micro fppLive dpLive
    tapes
    (fun slot => if slot = counterSlot 2
        ∨ (∃ m : Fin 7, mirrorSource m = 2 ∧ slot = mirrorSlot m) then newTapes slot
      else tapes slot)
    henc 2 (PalPeg.GalilScaffoldCounter.inc x.vm.radius) rfl
    (fun c' hc' => by fin_cases c' <;> first | exact absurd rfl hc' | rfl)
    rfl rfl (fun i => rfl) (fun i => rfl) rfl rfl
    (fun c' hc' => if_neg hc') segRad (by rw [if_pos rfl]; exact hradius)
    (by rw [if_pos (Or.inl rfl)]; exact hcounterRad)
    (fun m hsrc => by
      obtain ⟨seg, habsSeg, hseg⟩ := hmirrorRad m hsrc
      refine ⟨seg, ?_, ?_⟩
      · rw [if_pos rfl]
        exact habsSeg
      · rw [if_pos (Or.inr ⟨m, hsrc, rfl⟩)]
        exact hseg)
    (fun slot hc hm => if_neg (fun h => by
      rcases h with h | ⟨m, hsrc, hEq⟩
      · exact hc h
      · exact hm m hsrc hEq))
  have hcentreStep := encTapes_headStep margin
    ⟨x.ctl, {x.vm with radius := PalPeg.GalilScaffoldCounter.inc x.vm.radius}⟩
    ⟨x.ctl, {x.vm with radius := PalPeg.GalilScaffoldCounter.inc x.vm.radius, center := PalPeg.GalilScaffoldInputHead.left x.vm.center}⟩
    (fun c => if c = 2 then newPolarity 2 else polarity c) gap
    (fun v => if v = 1 then newGap 1 else gap v) micro fppLive dpLive
    (fun slot => if slot = counterSlot 2
        ∨ (∃ m : Fin 7, mirrorSource m = 2 ∧ slot = mirrorSlot m) then newTapes slot
      else tapes slot)
    (fun slot => if (∃ i : Fin 12, slot = headSlot 1 i) then newTapes slot
      else if slot = counterSlot 2
          ∨ (∃ m : Fin 7, mirrorSource m = 2 ∧ slot = mirrorSlot m) then newTapes slot
        else tapes slot)
    hradStep 1 (PalPeg.GalilScaffoldInputHead.left x.vm.center) rfl
    (fun v' hv' => by fin_cases v' <;> first | exact absurd rfl hv' | rfl)
    rfl rfl (fun i => rfl) (fun i => rfl) rfl rfl
    (fun v' hv' => if_neg hv') viewCentre viewTapesCentre habsCentre
    (by rw [if_pos rfl]; exact hrepCentre) hcellsCentre hwfCentre
    (fun i => by rw [if_pos ⟨i, rfl⟩]; exact hslotsCentre i)
    (fun slot hi => if_neg (fun h => by obtain ⟨i, hEq⟩ := h; exact hi i hEq))
    (fun i => by rw [if_pos ⟨i, rfl⟩]; exact hmarginCentre i)
  exact encTapes_rewindOne margin
    ⟨x.ctl, {x.vm with radius := PalPeg.GalilScaffoldCounter.inc x.vm.radius, center := PalPeg.GalilScaffoldInputHead.left x.vm.center}⟩
    (fun c => if c = 2 then newPolarity 2 else polarity c) newPolarity
    (fun v => if v = 1 then newGap 1 else gap v) newGap micro fppLive dpLive
    (fun slot => if (∃ i : Fin 12, slot = headSlot 1 i) then newTapes slot
      else if slot = counterSlot 2
          ∨ (∃ m : Fin 7, mirrorSource m = 2 ∧ slot = mirrorSlot m) then newTapes slot
        else tapes slot)
    newTapes hcentreStep ctl
    ⟨viewLeft, viewTapesLeft, habsLeft, hrepLeft, hslotsLeft, hcellsLeft, hwfLeft⟩
    (fun v hv => by
      by_cases h1 : v = 1
      · subst h1
        rw [if_pos rfl]
      · rw [if_neg h1]
        exact hgapOther v hv h1)
    (fun c hc => by
      by_cases h2 : c = 2
      · subst h2
        rw [if_pos rfl]
      · rw [if_neg h2]
        exact hpolarity c hc h2)
    segLen hlength hcounterLen hmirrorLen hprog
    (fun j hj => by
      rw [if_neg (fun h => by
          obtain ⟨i, hEq⟩ := h
          exact (progSlot_ne_headSlot fppLive j 1 i) hEq),
        if_neg (fun h => by
          rcases h with h | ⟨m, -, hEq⟩
          · exact (progSlot_ne_counterSlot fppLive j 2) h
          · exact absurd hEq (by cases fppLive <;> simp [progSlotOf]))]
      exact hprogOther j hj)
    (fun slot hprogSlot hc3 hmirror3 hhead0 hidle => by
      by_cases hh1 : ∃ i : Fin 12, slot = headSlot 1 i
      · rw [if_pos hh1]
      · rw [if_neg hh1]
        by_cases hrad : slot = counterSlot 2
            ∨ (∃ m : Fin 7, mirrorSource m = 2 ∧ slot = mirrorSlot m)
        · rw [if_pos hrad]
        · rw [if_neg hrad]
          refine hkept slot hprogSlot hc3 (fun h => hrad (Or.inl h))
            (fun m hsrc hEq => hrad (Or.inr ⟨m, hsrc, hEq⟩)) hmirror3 hhead0
            (fun i hEq => hh1 ⟨i, hEq⟩) hidle)
    hmarginLeft hidleShape

/-- **the case of a tick that moves one tape of the preparation program**, which is what the
walks do.  The other eight keep what they had, so the whole machine's tapes are known. -/
theorem encTapes_fppStep (margin : ℕ) (x : State GalilVM) (polarity : Fin 16 → Bool)
    (gap : Fin 4 → Bool) (micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl) (fppLive dpLive : Bool)
    (tapes newTapes : Slot → STape Γm)
    (henc : EncTapes margin x polarity gap micro fppLive dpLive tapes)
    (i : Fin 9) (f : PalPeg.GalilScaffoldTape.Tape → PalPeg.GalilScaffoldTape.Tape)
    (ctl : PalPeg.GalilScaffoldController.Control)
    (hmoved : newTapes (progSlotOf fppLive i)
      = padLeft margin (mapTape encProg (encTape (f (x.vm.fpp.program.config.tapes i)))))
    (hkept : ∀ slot, slot ≠ (progSlotOf fppLive i) → (∀ k : Fin 9, slot ≠ progSlotOf (!fppLive) k) →
      newTapes slot = tapes slot)
    (hidleShape : ∀ k : Fin 9, ∃ raw : STape (Fin 9),
      newTapes (progSlotOf (!fppLive) k) = padLeft margin (mapTape encProg raw)) :
    EncTapes margin
      ⟨ctl, {x.vm with fpp := {x.vm.fpp with program := PalPeg.GalilScaffoldChainInputSupply.FppControl.tape x.vm.fpp i f}}⟩
      polarity gap micro fppLive dpLive newTapes :=
  encTapes_fppTapes margin x polarity gap micro fppLive dpLive tapes newTapes henc
    (PalPeg.GalilScaffoldChainInputSupply.FppControl.tape x.vm.fpp i f) ctl
    (fun j => by
      rw [fppTape_tapes, Function.update_apply]
      by_cases hji : j = i
      · subst hji
        rw [if_pos rfl, hmoved]
      · rw [if_neg hji, hkept _ (by simp [hji]) (by intro k; cases fppLive <;> cases dpLive <;> simp [progSlotOf, dpSlotOf])]
        exact henc.fpp j)
    (fun slot hs hidle => hkept slot (hs i) hidle)
    hidleShape
/-! ### the mark walk, both directions -/

/-- **the rule that moves the marks tape forward realizes `markForward`.**  It names one
action, at the slot of the preparation machine's eighth tape: write back what the window shows at
its centre, and move right. -/
theorem encTapes_progRight (margin : ℕ) (x : State GalilVM) (polarity : Fin 16 → Bool)
    (gap : Fin 4 → Bool) (micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl) (fppLive dpLive : Bool)
    (tapes newTapes : Slot → STape Γm)
    (henc : EncTapes margin x polarity gap micro fppLive dpLive tapes)
    (ctl : PalPeg.GalilScaffoldController.Control) (i : Fin 9)
    (hmoved : newTapes (progSlotOf fppLive i)
      = PalPeg.CloseoutCoreEnc12.actList blankM (tapes (progSlotOf fppLive i))
          [some ((tapes (progSlotOf fppLive i)).focus, .right)])
    (hkept : ∀ slot, slot ≠ (progSlotOf fppLive i) → (∀ k : Fin 9, slot ≠ progSlotOf (!fppLive) k) →
      newTapes slot = tapes slot)
    (hidleShape : ∀ k : Fin 9, ∃ raw : STape (Fin 9),
      newTapes (progSlotOf (!fppLive) k) = padLeft margin (mapTape encProg raw)) :
    EncTapes margin
      ⟨ctl, {x.vm with fpp := {x.vm.fpp with program := PalPeg.GalilScaffoldChainInputSupply.FppControl.tape x.vm.fpp i PalPeg.GalilScaffoldTape.moveRight}}⟩
      polarity gap micro fppLive dpLive newTapes := by
  refine encTapes_fppStep margin x polarity gap micro fppLive dpLive tapes newTapes henc i
    PalPeg.GalilScaffoldTape.moveRight ctl ?_ hkept hidleShape
  rw [hmoved, henc.fpp i, focus_padded]
  show (padLeft margin (mapTape encProg (encTape (x.vm.fpp.program.config.tapes i)))).applyAction
      blankM (encProg (x.vm.fpp.program.config.tapes i).focus, .right) = _
  rw [padded_moveRight]

/-- **and the rule that moves it back realizes `markBack`, when the tape still has a
cell below its head.**  The window's cell below the head says which case this is. -/
theorem encTapes_progLeft (margin : ℕ) (x : State GalilVM) (polarity : Fin 16 → Bool)
    (gap : Fin 4 → Bool) (micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl) (fppLive dpLive : Bool)
    (tapes newTapes : Slot → STape Γm)
    (henc : EncTapes margin x polarity gap micro fppLive dpLive tapes)
    (ctl : PalPeg.GalilScaffoldController.Control) (i : Fin 9)
    (hfloor : (x.vm.fpp.program.config.tapes i).left ≠ [])
    (hmoved : newTapes (progSlotOf fppLive i)
      = PalPeg.CloseoutCoreEnc12.actList blankM (tapes (progSlotOf fppLive i))
          [some ((tapes (progSlotOf fppLive i)).focus, .left)])
    (hkept : ∀ slot, slot ≠ (progSlotOf fppLive i) → (∀ k : Fin 9, slot ≠ progSlotOf (!fppLive) k) →
      newTapes slot = tapes slot)
    (hidleShape : ∀ k : Fin 9, ∃ raw : STape (Fin 9),
      newTapes (progSlotOf (!fppLive) k) = padLeft margin (mapTape encProg raw)) :
    EncTapes margin
      ⟨ctl, {x.vm with fpp := {x.vm.fpp with program := PalPeg.GalilScaffoldChainInputSupply.FppControl.tape x.vm.fpp i PalPeg.GalilScaffoldTape.moveLeft}}⟩
      polarity gap micro fppLive dpLive newTapes := by
  refine encTapes_fppStep margin x polarity gap micro fppLive dpLive tapes newTapes henc i
    PalPeg.GalilScaffoldTape.moveLeft ctl ?_ hkept hidleShape
  rw [hmoved, henc.fpp i, focus_padded]
  show (padLeft margin (mapTape encProg (encTape (x.vm.fpp.program.config.tapes i)))).applyAction
      blankM (encProg (x.vm.fpp.program.config.tapes i).focus, .left) = _
  rw [padded_moveLeft margin (x.vm.fpp.program.config.tapes i) hfloor]

/-- **a step that leaves a tape where it is leaves the state where it is.**  On the
floor the component's tape does not move, so the rule names no action and the encoding is the
one it already had. -/
theorem fppStep_fixed (x : PalPeg.GalilScaffoldChainInputSupply.FppControl.State) (i : Fin 9)
    (f : PalPeg.GalilScaffoldTape.Tape → PalPeg.GalilScaffoldTape.Tape)
    (hfix : f (x.program.config.tapes i) = x.program.config.tapes i) :
    PalPeg.GalilScaffoldChainInputSupply.FppControl.tape x i f = x.program := by
  show {x.program with config := PalPeg.GalilScaffoldLoading.put x.program.config i (f (x.program.config.tapes i))} = x.program
  rw [hfix, PalPeg.GalilScaffoldLoading.put_same]

/-- the mark walk on the floor: the state stands still and so does the machine. -/
theorem encTapes_progLeftAtFloor (margin : ℕ) (x : State GalilVM) (polarity : Fin 16 → Bool)
    (gap : Fin 4 → Bool) (micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl) (fppLive dpLive : Bool)
    (tapes : Slot → STape Γm)
    (henc : EncTapes margin x polarity gap micro fppLive dpLive tapes)
    (ctl : PalPeg.GalilScaffoldController.Control) (i : Fin 9)
    (hfloor : (x.vm.fpp.program.config.tapes i).left = []) :
    EncTapes margin
      ⟨ctl, {x.vm with fpp := {x.vm.fpp with program := PalPeg.GalilScaffoldChainInputSupply.FppControl.tape x.vm.fpp i PalPeg.GalilScaffoldTape.moveLeft}}⟩
      polarity gap micro fppLive dpLive tapes := by
  have hstep : {x.vm.fpp with program := PalPeg.GalilScaffoldChainInputSupply.FppControl.tape x.vm.fpp i PalPeg.GalilScaffoldTape.moveLeft} = x.vm.fpp := by
    rw [fppStep_fixed x.vm.fpp i PalPeg.GalilScaffoldTape.moveLeft
      (moveLeft_atFloor (x.vm.fpp.program.config.tapes i) hfloor)]
  rw [hstep]
  exact encTapes_congr margin x ⟨ctl, x.vm⟩ polarity gap micro fppLive dpLive tapes (fun i => rfl) (fun i => rfl) rfl rfl rfl rfl rfl henc

/-! ### the finite control word -/

/-- **the controller's word, as the machine holds it.**  The abstract controller carries
its clock as a natural number; the machine's control must be finite, so it carries the clock as a
bounded number.  The bound is the match delay the clock is reset to, which the abstract clock
never exceeds. -/
structure CtlPhys where
  mode : PalPeg.GalilScaffoldController.Mode
  clock : Fin 2049
  output : Bool
  replaying : Bool
  odd : Bool
  pair : Bool
  deriving DecidableEq, Fintype

/-- what a control word says about the abstract controller. -/
def ctlAbs (c : CtlPhys) : PalPeg.GalilScaffoldController.Control :=
  ⟨c.mode, c.clock.val, c.output, c.replaying, c.odd, c.pair⟩

/-! ### the finite control the machine carries -/

instance : Fintype PalPeg.GalilScaffoldChainInputSupply.FppControl.Mode :=
  ⟨{.copy, .home, .run}, by intro x; cases x <;> decide⟩

instance : Fintype PalPeg.GalilScaffoldSearchFinish.Mode :=
  ⟨{.idle, .grow, .lower, .lowerHome, .copy, .home, .run, .found, .missed, .wait, .double},
    by intro x; cases x <;> decide⟩

/-- **which shape the chain is in.**  Everything a chain carries — its answer and period
tapes, its counters, its cursor and its verifier — lives on the machine's tapes and in its views;
what the finite control has to remember is only which of the five shapes it is in, because that
is what says which of those slots mean anything. -/
inductive ChainTag | idle | copy | back | watchers | broken
  deriving DecidableEq, Fintype

def chainTagOf : PalPeg.GalilScaffoldChainInputSupply.ChainVM → ChainTag
  | .idle => .idle
  | .copy _ _ _ _ _ _ _ => .copy
  | .back _ _ _ _ _ => .back
  | .watch _ => .watchers
  | .broken _ => .broken

/-- the consuming verifier's own three finite fields, which only a watching or broken
chain has.  A chain in another shape reports the values a fresh verifier would have, so that the
machine's reading is a function of the state and not a choice. -/
def chainConsumeOf (c : PalPeg.GalilScaffoldChainInputSupply.ChainVM) : Fin 5 × Bool × Bool :=
  match c with
  | .watch w => (w.machine.control.phase, w.machine.control.forward, w.machine.control.broken)
  | .broken w => (w.machine.control.phase, w.machine.control.forward, w.machine.control.broken)
  | _ => (0, false, false)

/-- **where a program counter stands, as a finite control can hold it.**  A program's
code is a finite list; a counter pointing outside it halts, and every such counter halts the same
way, so the machine need not tell them apart. -/
def PcPhys (bound : ℕ) : Type := Option (Fin bound)

instance instDecidableEqPcPhys {bound : ℕ} : DecidableEq (PcPhys bound) :=
  inferInstanceAs (DecidableEq (Option (Fin bound)))

instance instFintypePcPhys {bound : ℕ} : Fintype (PcPhys bound) :=
  inferInstanceAs (Fintype (Option (Fin bound)))

def EncPc {bound : ℕ} (held : PcPhys bound) (pc : ℕ) : Prop :=
  match held with
  | some i => (i : ℕ) = pc
  | none => bound ≤ pc

/-! ### the control is finite

The local realization asks for a finite control and a finite alphabet, so the state has to be
seen to be finite.  Every field of it is, but four of the view layer's own types were declared
with decidable equality only, so their finiteness is derived here. -/

deriving instance Fintype for PalPeg.CloseoutCoreEnc25.SOp
deriving instance Fintype for PalPeg.ConcreteLocalMachine.MicroOp
deriving instance Fintype for PalPeg.ConcreteLocalMachine.QueueJob
deriving instance Fintype for PalPeg.ConcreteLocalMachine.ViewCommand

/-- **the whole finite control.**  Counters, cursors and heads do not appear: they are on
the tapes.  What is left is the controller's word, the two programs' counters and flags, the
shapes of the chain and of the search, the continuation bit, and the bookkeeping the views and
the counter copies need. -/
structure QPhys (fppBound dpBound : ℕ) where
  ctl : CtlPhys
  chainTag : ChainTag
  chainPhase : Fin 5
  chainForward : Bool
  chainBroken : Bool
  fppMode : PalPeg.GalilScaffoldChainInputSupply.FppControl.Mode
  fppFinalStage : Bool
  fppPc : PcPhys fppBound
  fppDone : Bool
  dpPc : PcPhys dpBound
  dpDone : Bool
  searchMode : PalPeg.GalilScaffoldSearchFinish.Mode
  searchFinalStage : Bool
  searchQuarter : Fin 4
  periodOnly : Bool
  /-- the half-step bit of each cursor.  A cursor's letters live on its tape, but the bit
  saying whether it stands on a letter or on the gap beside it is one bit, so it lives in the
  finite control. -/
  placeGap : Fin 3 → Bool
  /-- whether the right input head stands on a letter of the input.  The head's own tapes do not
  say it — the cell below the head of a view's back tape is not sealed, and the comparison with
  the length of the input is not local at all — so the answer is a bit the control carries and
  the branches that move a head maintain. -/
  onLetterBit : Bool
  /-- whether the left input head stands on the first letter.  Carried for the same reason. -/
  leftFirstBit : Bool
  polarity : Fin 16 → Bool
  gap : Fin 4 → Bool
  micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl
  /-- the queue job of each view: what the ten tapes of the queue of pending arrivals are busy
  with for the rest of this slot.  Step `0` of a slot computes it afresh from the windows and
  the later steps only carry it, so nothing the abstraction can see depends on it — the field is
  physical only, like the live halves of the double buffers. -/
  job : Fin 4 → Option PalPeg.ConcreteLocalMachine.QueueJob
  /-- the command each view is carrying out for the rest of this tick.  A view's command is
  decided once, from the state and the letter that arrives, and the eleven steps of the slot that
  carries it out only read it — so it has to be in the control before the slot starts, and that
  is why a tick is twelve steps and not eleven. -/
  commands : Fin 4 → PalPeg.ConcreteLocalMachine.ViewCommand
  /-- which of the twelve steps of a tick the machine is on.  Step `0` reads the letter and
  decides what everything does; the eleven after it are the slot that does it. -/
  slot : Fin 12
  /-- which half of each double buffer the encoding speaks about.  The bit is physical only:
  the abstraction cannot see it, and a wipe of a program machine is its flip.  The encoding's
  own fields still address the `false` half; moving them onto this bit is the next step. -/
  fppLive : Bool
  dpLive : Bool

set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
deriving instance DecidableEq for QPhys

/-- the fields of the control as one tuple.  The derive handler for finiteness builds a chain of
sigma types 26 deep and its instance search gives up on it, so the finiteness of the control is
shown the plain way: this tuple is injective and its type is finite. -/
def qphysTuple {fppBound dpBound : ℕ} (q : QPhys fppBound dpBound) :
    CtlPhys × ChainTag × Fin 5 × Bool × Bool ×
      PalPeg.GalilScaffoldChainInputSupply.FppControl.Mode × Bool × PcPhys fppBound × Bool ×
      PcPhys dpBound × Bool × PalPeg.GalilScaffoldSearchFinish.Mode × Bool × Fin 4 × Bool ×
      (Fin 3 → Bool) × Bool × Bool × (Fin 16 → Bool) × (Fin 4 → Bool) ×
      (Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl) ×
      (Fin 4 → Option PalPeg.ConcreteLocalMachine.QueueJob) ×
      (Fin 4 → PalPeg.ConcreteLocalMachine.ViewCommand) × Fin 12 × Bool × Bool :=
  (q.ctl, q.chainTag, q.chainPhase, q.chainForward, q.chainBroken, q.fppMode, q.fppFinalStage,
    q.fppPc, q.fppDone, q.dpPc, q.dpDone, q.searchMode, q.searchFinalStage, q.searchQuarter,
    q.periodOnly, q.placeGap, q.onLetterBit, q.leftFirstBit, q.polarity, q.gap, q.micro, q.job,
    q.commands, q.slot, q.fppLive, q.dpLive)

theorem qphysTuple_injective {fppBound dpBound : ℕ} :
    Function.Injective (qphysTuple (fppBound := fppBound) (dpBound := dpBound)) := by
  intro a b hab
  cases a
  cases b
  simp only [qphysTuple, Prod.mk.injEq] at hab
  simp only [QPhys.mk.injEq]
  exact hab

instance instFiniteQPhys {fppBound dpBound : ℕ} : Finite (QPhys fppBound dpBound) :=
  Finite.of_injective _ (qphysTuple_injective (fppBound := fppBound) (dpBound := dpBound))

noncomputable instance instFintypeQPhys {fppBound dpBound : ℕ} :
    Fintype (QPhys fppBound dpBound) :=
  Fintype.ofFinite _

/-- **the control of one view, as the finite control carries it.**  The view layer's own rule
reads a view's gap bit, its queue job and the control of the micro-schedule; the state of the
machine carries all three, so a view's control is a projection of it and needs nothing else. -/
def viewControlOf {fppBound dpBound : ℕ} (q : QPhys fppBound dpBound) (v : Fin 4) :
    PalPeg.ConcreteLocalMachine.ViewControl :=
  (q.gap v, q.job v, (q.micro v).2)

@[simp] theorem viewControlOf_gap {fppBound dpBound : ℕ} (q : QPhys fppBound dpBound)
    (v : Fin 4) : (viewControlOf q v).1 = q.gap v := rfl

@[simp] theorem viewControlOf_micro {fppBound dpBound : ℕ} (q : QPhys fppBound dpBound)
    (v : Fin 4) : (viewControlOf q v).2.2 = (q.micro v).2 := rfl

/-- **what the finite control says about the state.**  Each field is read off the state;
nothing here mentions a tape. -/
structure EncControl {fppBound dpBound : ℕ} (w : List (Fin 2)) (x : State GalilVM)
    (q : QPhys fppBound dpBound) : Prop where
  ctl : ctlAbs q.ctl = x.ctl
  chainTag : q.chainTag = chainTagOf x.vm.chain
  chainPhase : q.chainPhase = (chainConsumeOf x.vm.chain).1
  chainForward : q.chainForward = (chainConsumeOf x.vm.chain).2.1
  chainBroken : q.chainBroken = (chainConsumeOf x.vm.chain).2.2
  fppMode : q.fppMode = x.vm.fpp.mode
  fppFinalStage : q.fppFinalStage = x.vm.fpp.finalStage
  fppPc : EncPc q.fppPc x.vm.fpp.program.config.pc
  fppDone : q.fppDone = x.vm.fpp.program.done
  dpPc : EncPc q.dpPc x.vm.dp.config.pc
  dpDone : q.dpDone = x.vm.dp.done
  searchMode : q.searchMode = x.vm.search.mode
  searchFinalStage : q.searchFinalStage = x.vm.search.finalStage
  searchQuarter : q.searchQuarter = x.vm.search.quarter
  periodOnly : q.periodOnly = x.vm.periodOnly
  placeGap : ∀ (i : Fin 3) place, placeOf x i = some place → q.placeGap i = place.gap
  onLetter : q.onLetterBit = PalPeg.GalilScaffoldChainInputSupply.onLetterTest w x.vm
  leftFirst : q.leftFirstBit = PalPeg.GalilScaffoldChainInputSupply.leftFirstTest x.vm

/-- **a step of a program's tapes leaves the finite control where it was.**  The
counter and the halting flag of the program sit beside its tapes, and putting a tape back changes
neither. -/
theorem encControl_fppStep {fppBound dpBound : ℕ} {w : List (Fin 2)} (x : State GalilVM)
    (q : QPhys fppBound dpBound) (henc : EncControl w x q)
    (f : PalPeg.GalilScaffoldTape.Tape → PalPeg.GalilScaffoldTape.Tape) (i : Fin 9) :
    EncControl w ⟨x.ctl, {x.vm with fpp := {x.vm.fpp with program := PalPeg.GalilScaffoldChainInputSupply.FppControl.tape x.vm.fpp i f}}⟩ q where
  ctl := henc.ctl
  chainTag := henc.chainTag
  chainPhase := henc.chainPhase
  chainForward := henc.chainForward
  chainBroken := henc.chainBroken
  fppMode := henc.fppMode
  fppFinalStage := henc.fppFinalStage
  fppPc := henc.fppPc
  fppDone := henc.fppDone
  dpPc := henc.dpPc
  dpDone := henc.dpDone
  searchMode := henc.searchMode
  searchFinalStage := henc.searchFinalStage
  searchQuarter := henc.searchQuarter
  periodOnly := henc.periodOnly
  placeGap := henc.placeGap
  onLetter := henc.onLetter
  leftFirst := henc.leftFirst

/-- **and a change of the control word is the same change on both sides**, whenever the
new word reads as the new controller.  Every branch discharges that by computation: the reading
takes each field across unchanged and only widens the clock. -/
theorem encControl_ctl {fppBound dpBound : ℕ} {w : List (Fin 2)} (x : State GalilVM)
    (q : QPhys fppBound dpBound) (henc : EncControl w x q) (c : CtlPhys)
    (a : PalPeg.GalilScaffoldController.Control) (hc : ctlAbs c = a) :
    EncControl w ⟨a, x.vm⟩ {q with ctl := c} where
  ctl := hc
  chainTag := henc.chainTag
  chainPhase := henc.chainPhase
  chainForward := henc.chainForward
  chainBroken := henc.chainBroken
  fppMode := henc.fppMode
  fppFinalStage := henc.fppFinalStage
  fppPc := henc.fppPc
  fppDone := henc.fppDone
  dpPc := henc.dpPc
  dpDone := henc.dpDone
  searchMode := henc.searchMode
  searchFinalStage := henc.searchFinalStage
  searchQuarter := henc.searchQuarter
  periodOnly := henc.periodOnly
  placeGap := henc.placeGap
  onLetter := henc.onLetter
  leftFirst := henc.leftFirst

/-! ### the mark walk, as the tick function computes it -/

/-- the test the mark walk branches on is the symbol under the head of the preparation
machine's eighth tape. -/
theorem frameFun_atEnd (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (s : GalilVM) :
    (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).atEnd s
      = decide ((s.fpp.program.config.tapes 8).focus = 5) := rfl

/-- and its two moves are a step of that tape, forward and back. -/
theorem frameFun_markForward (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (s : GalilVM) :
    (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).markForward s
      = {s with fpp := {s.fpp with program := PalPeg.GalilScaffoldChainInputSupply.FppControl.tape s.fpp 8 PalPeg.GalilScaffoldTape.moveRight}} := rfl

theorem frameFun_markBack (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (s : GalilVM) :
    (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).markBack s
      = {s with fpp := {s.fpp with program := PalPeg.GalilScaffoldChainInputSupply.FppControl.tape s.fpp 8 PalPeg.GalilScaffoldTape.moveLeft}} := rfl

/-! ### the branch of the rule that walks the marks -/

/-- **the whole encoding**: the finite control reads the state's finite part, the tapes
read the rest. -/
def Enc {fppBound dpBound : ℕ} (w : List (Fin 2)) (margin : ℕ) (x : State GalilVM)
    (p : QPhys fppBound dpBound × (Slot → STape Γm)) : Prop :=
  EncControl w x p.1 ∧ EncTapes margin x p.1.polarity p.1.gap p.1.micro p.1.fppLive p.1.dpLive p.2

/-- **the mark walk forward, both sides at once.**  In `markEnd`, with the marks tape
not yet on the end symbol, the tick moves that tape one cell right and leaves the control word
alone; a rule that names one action, at that tape's slot, write-back-and-right, keeps the whole
encoding. -/
theorem markEnd_forward {fppBound dpBound : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (tapes newTapes : Slot → STape Γm)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd)
    (hnotEnd : (x.vm.fpp.program.config.tapes 8).focus ≠ 5)
    (henc : Enc w margin x (q, tapes))
    (hmoved : newTapes (progSlotOf q.fppLive 8)
      = PalPeg.CloseoutCoreEnc12.actList blankM (tapes (progSlotOf q.fppLive 8))
          [some ((tapes (progSlotOf q.fppLive 8)).focus, .right)])
    (hkept : ∀ slot, slot ≠ (progSlotOf q.fppLive 8) →
      (∀ k : Fin 9, slot ≠ progSlotOf (!q.fppLive) k) → newTapes slot = tapes slot)
    (hidleShape : ∀ k : Fin 9, ∃ raw : STape (Fin 9),
      newTapes (progSlotOf (!q.fppLive) k) = padLeft margin (mapTape encProg raw)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      (q, newTapes) := by
  have hval : PalPeg.GalilScaffoldTop.tickFun
      (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x
      = ⟨x.ctl, {x.vm with fpp := PalPeg.GalilScaffoldChainInputSupply.markStep x.vm.fpp PalPeg.GalilScaffoldTape.moveRight}⟩ := by
    simp only [PalPeg.GalilScaffoldTop.tickFun, hmode, frameFun_atEnd, frameFun_markForward]
    rw [if_neg (by simpa using hnotEnd)]
    rfl
  rw [hval]
  exact ⟨encControl_fppStep x q henc.1 PalPeg.GalilScaffoldTape.moveRight 8,
    encTapes_progRight margin x q.polarity q.gap q.micro q.fppLive q.dpLive tapes newTapes henc.2 x.ctl 8 hmoved hkept hidleShape⟩

/-- **the mark walk back, both sides at once**, when the marks tape still has a cell
below its head.  The tick also sends the controller to `choose` and clears the parity bit, and
the machine's control word makes the same change. -/
theorem markEnd_back {fppBound dpBound : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (tapes newTapes : Slot → STape Γm)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd)
    (hatEnd : (x.vm.fpp.program.config.tapes 8).focus = 5)
    (hfloor : (x.vm.fpp.program.config.tapes 8).left ≠ [])
    (henc : Enc w margin x (q, tapes))
    (hmoved : newTapes (progSlotOf q.fppLive 8)
      = PalPeg.CloseoutCoreEnc12.actList blankM (tapes (progSlotOf q.fppLive 8))
          [some ((tapes (progSlotOf q.fppLive 8)).focus, .left)])
    (hkept : ∀ slot, slot ≠ (progSlotOf q.fppLive 8) →
      (∀ k : Fin 9, slot ≠ progSlotOf (!q.fppLive) k) → newTapes slot = tapes slot)
    (hidleShape : ∀ k : Fin 9, ∃ raw : STape (Fin 9),
      newTapes (progSlotOf (!q.fppLive) k) = padLeft margin (mapTape encProg raw)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ({q with ctl := {q.ctl with mode := PalPeg.GalilScaffoldController.Mode.choose, odd := false}},
        newTapes) := by
  have hval : PalPeg.GalilScaffoldTop.tickFun
      (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x
      = ⟨{x.ctl with mode := PalPeg.GalilScaffoldController.Mode.choose, odd := false}, {x.vm with fpp := PalPeg.GalilScaffoldChainInputSupply.markStep x.vm.fpp PalPeg.GalilScaffoldTape.moveLeft}⟩ := by
    simp only [PalPeg.GalilScaffoldTop.tickFun, hmode, frameFun_atEnd, frameFun_markBack]
    rw [if_pos (by simpa using hatEnd)]
    rfl
  rw [hval]
  refine ⟨encControl_fppStep ⟨{x.ctl with mode := PalPeg.GalilScaffoldController.Mode.choose, odd := false}, x.vm⟩ _ (encControl_ctl x q henc.1 {q.ctl with mode := PalPeg.GalilScaffoldController.Mode.choose, odd := false} {x.ctl with mode := PalPeg.GalilScaffoldController.Mode.choose, odd := false} (by rw [← henc.1.ctl]; rfl)) PalPeg.GalilScaffoldTape.moveLeft 8, ?_⟩
  exact encTapes_progLeft margin x q.polarity q.gap q.micro q.fppLive q.dpLive tapes newTapes henc.2 _ 8 hfloor hmoved hkept hidleShape

/-- **and on the floor the marks tape stays**, so the rule names no action at all and
only the control word changes. -/
theorem markEnd_back_atFloor {fppBound dpBound : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (tapes : Slot → STape Γm)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd)
    (hatEnd : (x.vm.fpp.program.config.tapes 8).focus = 5)
    (hfloor : (x.vm.fpp.program.config.tapes 8).left = [])
    (henc : Enc w margin x (q, tapes)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ({q with ctl := {q.ctl with mode := PalPeg.GalilScaffoldController.Mode.choose, odd := false}},
        tapes) := by
  have hval : PalPeg.GalilScaffoldTop.tickFun
      (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x
      = ⟨{x.ctl with mode := PalPeg.GalilScaffoldController.Mode.choose, odd := false}, {x.vm with fpp := PalPeg.GalilScaffoldChainInputSupply.markStep x.vm.fpp PalPeg.GalilScaffoldTape.moveLeft}⟩ := by
    simp only [PalPeg.GalilScaffoldTop.tickFun, hmode, frameFun_atEnd, frameFun_markBack]
    rw [if_pos (by simpa using hatEnd)]
    rfl
  rw [hval]
  refine ⟨encControl_fppStep ⟨{x.ctl with mode := PalPeg.GalilScaffoldController.Mode.choose, odd := false}, x.vm⟩ _ (encControl_ctl x q henc.1 {q.ctl with mode := PalPeg.GalilScaffoldController.Mode.choose, odd := false} {x.ctl with mode := PalPeg.GalilScaffoldController.Mode.choose, odd := false} (by rw [← henc.1.ctl]; rfl)) PalPeg.GalilScaffoldTape.moveLeft 8, ?_⟩
  exact encTapes_progLeftAtFloor margin x q.polarity q.gap q.micro q.fppLive q.dpLive tapes henc.2 _ 8 hfloor

/-! ### the walk home, and the start of the preparation program -/

/-- the walk home branches on the symbol under the head of the preparation machine's
seventh tape, and walks that tape one cell left. -/
theorem frameFun_atLeft (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (s : GalilVM) :
    (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).atLeft s
      = decide ((s.fpp.program.config.tapes 7).focus = 4) := rfl

theorem frameFun_homeStep (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (s : GalilVM) :
    (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).homeStep s
      = {s with fpp := {s.fpp with program := PalPeg.GalilScaffoldChainInputSupply.FppControl.tape s.fpp 7 PalPeg.GalilScaffoldTape.moveLeft}} := rfl

/-- **starting the preparation program moves no tape at all.**  It sets the program's
counter to the entry point, clears its halting flag and puts the preparation into its running
mode — three changes of the finite control and nothing else. -/
theorem frameFun_fppStart (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (s : GalilVM) :
    (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).fppStart s
      = {s with fpp := {s.fpp with program := PalPeg.GalilScaffoldControl.start 320 s.fpp.program, mode := .run}} := rfl

/-- **a quantum of the preparation program is a run of the marked code.**  The frame's halting
test asks whether that run reaches the halt; the tick's non-halting branch installs the run's
machine and leaves every other component of the state alone. -/
theorem frameFun_fppHalts (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (s : GalilVM) :
    (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).fppHalts s
      = (PalPeg.ProgramFunction.fppRunFun entryQ s.fpp.program).done := rfl

theorem frameFun_fppDone (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (s : GalilVM) :
    (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).fppDone s
      = {s with fpp := {s.fpp with
          program := PalPeg.GalilScaffoldChainInputSupply.markNew
            (PalPeg.ProgramFunction.fppRunFun entryQ s.fpp.program) first}} := rfl

theorem frameFun_fppSlice (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (s : GalilVM) :
    (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).fppSlice s
      = {s with fpp := {s.fpp with
          program := PalPeg.ProgramFunction.fppRunFun entryQ s.fpp.program}} := rfl

/-- and the run is exactly the quantum the action table walks: `fppRunFun` unfolds to the run of
the marked code on a list of `entryQ` enabled calls. -/
theorem fppRunFun_eq_runFun (entryQ : ℕ) (m : PalPeg.GalilScaffoldControl.Machine 9) :
    PalPeg.ProgramFunction.fppRunFun entryQ m
      = PalPeg.ProgramFunction.runFun PalPeg.GalilFppMarkedCode.code
          (List.replicate entryQ true) m := rfl

/-- the shape of one tick of the fallback copy, once the walker is known to show a symbol:
one stamp and one step right on the program's copy tape, one off the work counter, and the
walker half a place to the left. -/
theorem copyOneFun_eq (x : PalPeg.GalilScaffoldChainInputSupply.FppControl.State) (a : Fin 3)
    (hread : PalPeg.GalilScaffoldPlace.read x.walker = some a) :
    PalPeg.FrameFunction.copyOneFun x
      = {x with program := PalPeg.GalilScaffoldChainInputSupply.FppControl.tape x 7 (fun t => PalPeg.GalilScaffoldTape.moveRight (PalPeg.GalilScaffoldTape.write t (PalPeg.GalilFppPreparation.symbol a))), work := PalPeg.GalilScaffoldCounter.dec x.work, walker := PalPeg.GalilScaffoldPlace.left x.walker} := by
  unfold PalPeg.FrameFunction.copyOneFun
  rw [hread]

/-- **a tick of the fallback copy moves the walker half a place and nothing else in the
control.**  The controller's word is unchanged, the preparation's mode and flag are unchanged,
and the program's counter and halting flag sit beside its tapes.  What does change is the
walker's half-step bit, which `GalilScaffoldPlace.left` flips whichever way it steps. -/
theorem encControl_copyOne {fppBound dpBound : ℕ} {w : List (Fin 2)} (x : State GalilVM)
    (q : QPhys fppBound dpBound) (henc : EncControl w x q)
    (a : Fin 3) (hread : PalPeg.GalilScaffoldPlace.read x.vm.fpp.walker = some a)
    (newPolarity : Fin 16 → Bool) :
    EncControl w ⟨x.ctl, {x.vm with fpp := {x.vm.fpp with program := PalPeg.GalilScaffoldChainInputSupply.FppControl.tape x.vm.fpp 7 (fun t => PalPeg.GalilScaffoldTape.moveRight (PalPeg.GalilScaffoldTape.write t (PalPeg.GalilFppPreparation.symbol a))), work := PalPeg.GalilScaffoldCounter.dec x.vm.fpp.work, walker := PalPeg.GalilScaffoldPlace.left x.vm.fpp.walker}}⟩
      {q with placeGap := Function.update q.placeGap 1 (!q.placeGap 1), polarity := newPolarity} where
  ctl := henc.ctl
  chainTag := henc.chainTag
  chainPhase := henc.chainPhase
  chainForward := henc.chainForward
  chainBroken := henc.chainBroken
  fppMode := henc.fppMode
  fppFinalStage := henc.fppFinalStage
  fppPc := henc.fppPc
  fppDone := henc.fppDone
  dpPc := henc.dpPc
  dpDone := henc.dpDone
  searchMode := henc.searchMode
  searchFinalStage := henc.searchFinalStage
  searchQuarter := henc.searchQuarter
  periodOnly := henc.periodOnly
  onLetter := henc.onLetter
  leftFirst := henc.leftFirst
  placeGap := by
    intro i place hplace
    fin_cases i
    · show Function.update q.placeGap 1 (!q.placeGap 1) 0 = place.gap
      rw [Function.update_of_ne (by decide)]
      exact henc.placeGap 0 place hplace
    · show Function.update q.placeGap 1 (!q.placeGap 1) 1 = place.gap
      rw [Function.update_self]
      have hwalk : place = PalPeg.GalilScaffoldPlace.left x.vm.fpp.walker :=
        (Option.some.inj hplace).symm
      rw [hwalk, henc.placeGap 1 x.vm.fpp.walker rfl]
      unfold PalPeg.GalilScaffoldPlace.left
      cases x.vm.fpp.walker.gap <;> simp
    · show Function.update q.placeGap 1 (!q.placeGap 1) 2 = place.gap
      rw [Function.update_of_ne (by decide)]
      exact henc.placeGap 2 place hplace

/-- **the paired step of the rewind leaves the control where the single step does.**  It moves
the centre head as well, and counts that on the radius; neither is a field of the control, and
the bit for the first letter is about the left head, so the two sides agree. -/
theorem encControl_rewindPair {fppBound dpBound : ℕ} {w : List (Fin 2)} (x : State GalilVM)
    (q : QPhys fppBound dpBound) (henc : EncControl w x q)
    (c : CtlPhys) (a : PalPeg.GalilScaffoldController.Control) (hc : ctlAbs c = a)
    (bit : Bool)
    (hbit : bit = decide (PalPeg.GalilScaffoldChainInputSupply.position
      (PalPeg.GalilScaffoldInputHead.left x.vm.left) = 1))
    (newPolarity : Fin 16 → Bool) (newGap : Fin 4 → Bool) :
    EncControl w ⟨a, {x.vm with fpp := PalPeg.GalilScaffoldChainInputSupply.markStep x.vm.fpp PalPeg.GalilScaffoldTape.moveLeft, left := PalPeg.GalilScaffoldInputHead.left x.vm.left, length := PalPeg.GalilScaffoldCounter.inc x.vm.length, center := PalPeg.GalilScaffoldInputHead.left x.vm.center, radius := PalPeg.GalilScaffoldCounter.inc x.vm.radius}⟩
      {q with ctl := c, leftFirstBit := bit, polarity := newPolarity, gap := newGap} where
  ctl := hc
  chainTag := henc.chainTag
  chainPhase := henc.chainPhase
  chainForward := henc.chainForward
  chainBroken := henc.chainBroken
  fppMode := henc.fppMode
  fppFinalStage := henc.fppFinalStage
  fppPc := henc.fppPc
  fppDone := henc.fppDone
  dpPc := henc.dpPc
  dpDone := henc.dpDone
  searchMode := henc.searchMode
  searchFinalStage := henc.searchFinalStage
  searchQuarter := henc.searchQuarter
  periodOnly := henc.periodOnly
  placeGap := henc.placeGap
  onLetter := henc.onLetter
  leftFirst := hbit

/-- **one tick of the rewind leaves all of the control but two bits where it was.**  The tick
steps the marks tape left, steps the left input head left and counts the step; the controller's
word changes by its own pair bit, and the only field of the control that follows the state is the
bit for the first letter, which the head's step is about. -/
theorem encControl_rewindOne {fppBound dpBound : ℕ} {w : List (Fin 2)} (x : State GalilVM)
    (q : QPhys fppBound dpBound) (henc : EncControl w x q)
    (c : CtlPhys) (a : PalPeg.GalilScaffoldController.Control) (hc : ctlAbs c = a)
    (bit : Bool)
    (hbit : bit = decide (PalPeg.GalilScaffoldChainInputSupply.position
      (PalPeg.GalilScaffoldInputHead.left x.vm.left) = 1))
    (newPolarity : Fin 16 → Bool) (newGap : Fin 4 → Bool) :
    EncControl w ⟨a, {x.vm with fpp := PalPeg.GalilScaffoldChainInputSupply.markStep x.vm.fpp PalPeg.GalilScaffoldTape.moveLeft, left := PalPeg.GalilScaffoldInputHead.left x.vm.left, length := PalPeg.GalilScaffoldCounter.inc x.vm.length}⟩
      {q with ctl := c, leftFirstBit := bit, polarity := newPolarity, gap := newGap} where
  ctl := hc
  chainTag := henc.chainTag
  chainPhase := henc.chainPhase
  chainForward := henc.chainForward
  chainBroken := henc.chainBroken
  fppMode := henc.fppMode
  fppFinalStage := henc.fppFinalStage
  fppPc := henc.fppPc
  fppDone := henc.fppDone
  dpPc := henc.dpPc
  dpDone := henc.dpDone
  searchMode := henc.searchMode
  searchFinalStage := henc.searchFinalStage
  searchQuarter := henc.searchQuarter
  periodOnly := henc.periodOnly
  placeGap := henc.placeGap
  onLetter := henc.onLetter
  leftFirst := hbit

/-- **the last tick of the fallback copy leaves the control where the copy put it.**  The copy
writes the end mark on its own tape, hands the machine to the walk home and records whether the
cursor ran out; the program's counter and halting flag are untouched, and so is every cursor. -/
theorem encControl_copyEnd {fppBound dpBound : ℕ} {w : List (Fin 2)} (x : State GalilVM)
    (q : QPhys fppBound dpBound) (henc : EncControl w x q)
    (c : CtlPhys) (a : PalPeg.GalilScaffoldController.Control) (hc : ctlAbs c = a)
    (bit : Bool) (hbit : bit = (PalPeg.GalilScaffoldPlace.read x.vm.fpp.walker).isNone) :
    EncControl w ⟨a, {x.vm with fpp := PalPeg.FrameFunction.copyEndFun x.vm.fpp}⟩
      {q with ctl := c, fppMode := PalPeg.GalilScaffoldChainInputSupply.FppControl.Mode.home, fppFinalStage := bit} where
  ctl := hc
  chainTag := henc.chainTag
  chainPhase := henc.chainPhase
  chainForward := henc.chainForward
  chainBroken := henc.chainBroken
  fppMode := rfl
  fppFinalStage := hbit
  fppPc := henc.fppPc
  fppDone := henc.fppDone
  dpPc := henc.dpPc
  dpDone := henc.dpDone
  searchMode := henc.searchMode
  searchFinalStage := henc.searchFinalStage
  searchQuarter := henc.searchQuarter
  periodOnly := henc.periodOnly
  placeGap := henc.placeGap
  onLetter := henc.onLetter
  leftFirst := henc.leftFirst

/-- and the finite control makes exactly those three changes. -/
theorem encControl_fppStart {fppBound dpBound : ℕ} {w : List (Fin 2)} (x : State GalilVM)
    (q : QPhys fppBound dpBound) (henc : EncControl w x q) (hbound : 320 < fppBound)
    (c : CtlPhys) (a : PalPeg.GalilScaffoldController.Control) (hc : ctlAbs c = a) :
    EncControl w ⟨a, {x.vm with fpp := {x.vm.fpp with program := PalPeg.GalilScaffoldControl.start 320 x.vm.fpp.program, mode := .run}}⟩
      {q with ctl := c, fppMode := .run, fppPc := some ⟨320, hbound⟩, fppDone := false} where
  ctl := hc
  chainTag := henc.chainTag
  chainPhase := henc.chainPhase
  chainForward := henc.chainForward
  chainBroken := henc.chainBroken
  fppMode := rfl
  fppFinalStage := henc.fppFinalStage
  fppPc := rfl
  fppDone := rfl
  dpPc := henc.dpPc
  dpDone := henc.dpDone
  searchMode := henc.searchMode
  searchFinalStage := henc.searchFinalStage
  searchQuarter := henc.searchQuarter
  periodOnly := henc.periodOnly
  placeGap := henc.placeGap
  onLetter := henc.onLetter
  leftFirst := henc.leftFirst

/-- **the walk home, both sides at once**, while the seventh tape still has a cell below
its head. -/
theorem home_step {fppBound dpBound : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (tapes newTapes : Slot → STape Γm)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.home)
    (hnotLeft : (x.vm.fpp.program.config.tapes 7).focus ≠ 4)
    (hfloor : (x.vm.fpp.program.config.tapes 7).left ≠ [])
    (henc : Enc w margin x (q, tapes))
    (hmoved : newTapes (progSlotOf q.fppLive 7)
      = PalPeg.CloseoutCoreEnc12.actList blankM (tapes (progSlotOf q.fppLive 7))
          [some ((tapes (progSlotOf q.fppLive 7)).focus, .left)])
    (hkept : ∀ slot, slot ≠ (progSlotOf q.fppLive 7) →
      (∀ k : Fin 9, slot ≠ progSlotOf (!q.fppLive) k) → newTapes slot = tapes slot)
    (hidleShape : ∀ k : Fin 9, ∃ raw : STape (Fin 9),
      newTapes (progSlotOf (!q.fppLive) k) = padLeft margin (mapTape encProg raw)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      (q, newTapes) := by
  have hval : PalPeg.GalilScaffoldTop.tickFun
      (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x
      = ⟨x.ctl, {x.vm with fpp := {x.vm.fpp with program := PalPeg.GalilScaffoldChainInputSupply.FppControl.tape x.vm.fpp 7 PalPeg.GalilScaffoldTape.moveLeft}}⟩ := by
    simp only [PalPeg.GalilScaffoldTop.tickFun, hmode, frameFun_atLeft, frameFun_homeStep]
    rw [if_neg (by simpa using hnotLeft)]
  rw [hval]
  exact ⟨encControl_fppStep x q henc.1 PalPeg.GalilScaffoldTape.moveLeft 7,
    encTapes_progLeft margin x q.polarity q.gap q.micro q.fppLive q.dpLive tapes newTapes henc.2 x.ctl 7 hfloor hmoved hkept hidleShape⟩

/-- and on the floor the seventh tape stays, so the rule names no action. -/
theorem home_step_atFloor {fppBound dpBound : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (tapes : Slot → STape Γm)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.home)
    (hnotLeft : (x.vm.fpp.program.config.tapes 7).focus ≠ 4)
    (hfloor : (x.vm.fpp.program.config.tapes 7).left = [])
    (henc : Enc w margin x (q, tapes)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      (q, tapes) := by
  have hval : PalPeg.GalilScaffoldTop.tickFun
      (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x
      = ⟨x.ctl, {x.vm with fpp := {x.vm.fpp with program := PalPeg.GalilScaffoldChainInputSupply.FppControl.tape x.vm.fpp 7 PalPeg.GalilScaffoldTape.moveLeft}}⟩ := by
    simp only [PalPeg.GalilScaffoldTop.tickFun, hmode, frameFun_atLeft, frameFun_homeStep]
    rw [if_neg (by simpa using hnotLeft)]
  rw [hval]
  exact ⟨encControl_fppStep x q henc.1 PalPeg.GalilScaffoldTape.moveLeft 7,
    encTapes_progLeftAtFloor margin x q.polarity q.gap q.micro q.fppLive q.dpLive tapes henc.2 x.ctl 7 hfloor⟩

/-- **and at the left end the preparation program starts.**  No tape moves; the control
word takes the entry point, clears the halting flag, and the controller goes to `fpp`. -/
theorem home_fppStart {fppBound dpBound : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (tapes : Slot → STape Γm)
    (hbound : 320 < fppBound)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.home)
    (hatLeft : (x.vm.fpp.program.config.tapes 7).focus = 4)
    (henc : Enc w margin x (q, tapes)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ({q with ctl := {q.ctl with mode := PalPeg.GalilScaffoldController.Mode.fpp}, fppMode := .run, fppPc := some ⟨320, hbound⟩, fppDone := false}, tapes) := by
  have hval : PalPeg.GalilScaffoldTop.tickFun
      (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x
      = ⟨{x.ctl with mode := PalPeg.GalilScaffoldController.Mode.fpp}, {x.vm with fpp := {x.vm.fpp with program := PalPeg.GalilScaffoldControl.start 320 x.vm.fpp.program, mode := .run}}⟩ := by
    simp only [PalPeg.GalilScaffoldTop.tickFun, hmode, frameFun_atLeft, frameFun_fppStart]
    rw [if_pos (by simpa using hatLeft)]
  rw [hval]
  refine ⟨encControl_fppStart x q henc.1 hbound {q.ctl with mode := PalPeg.GalilScaffoldController.Mode.fpp} {x.ctl with mode := PalPeg.GalilScaffoldController.Mode.fpp} (by rw [← henc.1.ctl]; rfl), ?_⟩
  exact encTapes_congr margin x _ q.polarity q.gap q.micro q.fppLive q.dpLive tapes
    (fun i => rfl) (fun i => rfl) rfl rfl rfl rfl rfl henc.2

/-! ### the parity walk of `choose` -/

/-- the test `choose` branches on is again a symbol under the head of the preparation
machine's eighth tape: a mark, or the letter the run started from. -/
theorem frameFun_markSet (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (s : GalilVM) :
    (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).markSet s
      = (decide ((s.fpp.program.config.tapes 8).focus = 8)
          || decide ((s.fpp.program.config.tapes 8).focus = first)) := rfl

/-- **the step of `choose` that keeps looking**: it flips the parity bit and walks the
marks tape back one cell.  Both halves are already in hand — the control word's own change and
the same move the mark walk makes. -/
theorem choose_back {fppBound dpBound : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (tapes newTapes : Slot → STape Γm)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.choose)
    (hkeep : (x.ctl.odd && (decide ((x.vm.fpp.program.config.tapes 8).focus = 8)
        || decide ((x.vm.fpp.program.config.tapes 8).focus = first))) = false)
    (hfloor : (x.vm.fpp.program.config.tapes 8).left ≠ [])
    (henc : Enc w margin x (q, tapes))
    (hmoved : newTapes (progSlotOf q.fppLive 8)
      = PalPeg.CloseoutCoreEnc12.actList blankM (tapes (progSlotOf q.fppLive 8))
          [some ((tapes (progSlotOf q.fppLive 8)).focus, .left)])
    (hkept : ∀ slot, slot ≠ (progSlotOf q.fppLive 8) →
      (∀ k : Fin 9, slot ≠ progSlotOf (!q.fppLive) k) → newTapes slot = tapes slot)
    (hidleShape : ∀ k : Fin 9, ∃ raw : STape (Fin 9),
      newTapes (progSlotOf (!q.fppLive) k) = padLeft margin (mapTape encProg raw)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ({q with ctl := {q.ctl with odd := !q.ctl.odd}}, newTapes) := by
  have hval : PalPeg.GalilScaffoldTop.tickFun
      (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x
      = ⟨{x.ctl with odd := !x.ctl.odd}, {x.vm with fpp := {x.vm.fpp with program := PalPeg.GalilScaffoldChainInputSupply.FppControl.tape x.vm.fpp 8 PalPeg.GalilScaffoldTape.moveLeft}}⟩ := by
    simp only [PalPeg.GalilScaffoldTop.tickFun, hmode, frameFun_markSet, frameFun_markBack]
    rw [if_neg (by simp [hkeep])]
  rw [hval]
  have hctl : ctlAbs {q.ctl with odd := !q.ctl.odd} = {x.ctl with odd := !x.ctl.odd} := by
    rw [← henc.1.ctl]
    rfl
  refine ⟨encControl_fppStep ⟨{x.ctl with odd := !x.ctl.odd}, x.vm⟩ _
    (encControl_ctl x q henc.1 {q.ctl with odd := !q.ctl.odd} {x.ctl with odd := !x.ctl.odd} hctl)
    PalPeg.GalilScaffoldTape.moveLeft 8, ?_⟩
  exact encTapes_progLeft margin x q.polarity q.gap q.micro q.fppLive q.dpLive tapes newTapes henc.2 _ 8 hfloor hmoved hkept hidleShape

/-- and on the floor the marks tape stays, so only the parity bit changes. -/
theorem choose_back_atFloor {fppBound dpBound : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (tapes : Slot → STape Γm)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.choose)
    (hkeep : (x.ctl.odd && (decide ((x.vm.fpp.program.config.tapes 8).focus = 8)
        || decide ((x.vm.fpp.program.config.tapes 8).focus = first))) = false)
    (hfloor : (x.vm.fpp.program.config.tapes 8).left = [])
    (henc : Enc w margin x (q, tapes)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ({q with ctl := {q.ctl with odd := !q.ctl.odd}}, tapes) := by
  have hval : PalPeg.GalilScaffoldTop.tickFun
      (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x
      = ⟨{x.ctl with odd := !x.ctl.odd}, {x.vm with fpp := {x.vm.fpp with program := PalPeg.GalilScaffoldChainInputSupply.FppControl.tape x.vm.fpp 8 PalPeg.GalilScaffoldTape.moveLeft}}⟩ := by
    simp only [PalPeg.GalilScaffoldTop.tickFun, hmode, frameFun_markSet, frameFun_markBack]
    rw [if_neg (by simp [hkeep])]
  rw [hval]
  have hctl : ctlAbs {q.ctl with odd := !q.ctl.odd} = {x.ctl with odd := !x.ctl.odd} := by
    rw [← henc.1.ctl]
    rfl
  refine ⟨encControl_fppStep ⟨{x.ctl with odd := !x.ctl.odd}, x.vm⟩ _
    (encControl_ctl x q henc.1 {q.ctl with odd := !q.ctl.odd} {x.ctl with odd := !x.ctl.odd} hctl)
    PalPeg.GalilScaffoldTape.moveLeft 8, ?_⟩
  exact encTapes_progLeftAtFloor margin x q.polarity q.gap q.micro q.fppLive q.dpLive tapes henc.2 _ 8 hfloor

/-! ### the programs as double buffers, which is where they actually live

The local refinement (`PalPeg/LocalState.lean`) keeps each program machine as a `Buffered n`:
two bundles of tapes and a bit saying which one is live.  `LocalBuffers.abs` reads the live one,
so the abstract wipe of a whole machine is a flip of that bit and a background erasure job on the
other half — no content moves.  The encoding therefore holds **both** halves, and the lemmas
proved above about moving one tape apply to the live half unchanged. -/

def BufEnc (margin : ℕ) {n : ℕ} (b : PalPeg.LocalBuffers.Buffered n)
    (tapesA tapesB : Fin n → STape Γm) : Prop :=
  (∀ i, tapesA i = padLeft margin (mapTape encProg (encTape (b.A i)))) ∧
    (∀ i, tapesB i = padLeft margin (mapTape encProg (encTape (b.B i))))

/-- **wiping a whole program machine costs the tapes nothing.**  `resetL` flips the live
bit and starts an erasure job; both halves keep their contents, so the rule names no action at
all.  This is what the earlier reading of `GalilScaffoldControl.reset` — nine tapes blanked in one
step — turns into once the state is the physical one. -/
theorem bufEnc_resetL (margin : ℕ) {n : ℕ} (b : PalPeg.LocalBuffers.Buffered n)
    (tapesA tapesB : Fin n → STape Γm) (h : BufEnc margin b tapesA tapesB) :
    BufEnc margin (PalPeg.LocalBuffers.resetL b) tapesA tapesB := h

/-- and an erasure tick touches only the idle half, which no reading of the state looks
at, so the live half's encoding survives it. -/
theorem bufEnc_live_clearTick (margin : ℕ) {n : ℕ} (b : PalPeg.LocalBuffers.Buffered n)
    (tapesA tapesB : Fin n → STape Γm) (h : BufEnc margin b tapesA tapesB)
    (hactive : b.active = true) :
    ∀ i, tapesA i = padLeft margin (mapTape encProg (encTape
      (PalPeg.LocalBuffers.abs (PalPeg.LocalBuffers.clearTick b) i))) := by
  intro i
  have habs : PalPeg.LocalBuffers.abs (PalPeg.LocalBuffers.clearTick b) i = b.A i := by
    cases hjob : b.job <;>
      simp [PalPeg.LocalBuffers.clearTick, PalPeg.LocalBuffers.abs, hjob, hactive]
  rw [h.1 i, habs]

/-- **one step of the live program is one action on one slot**, exactly as the lemmas
above say.  `stepL` lifts a change of the bundle onto whichever half is live. -/
theorem bufEnc_stepRight (margin : ℕ) {n : ℕ} (b : PalPeg.LocalBuffers.Buffered n) (i : Fin n)
    (tapesA tapesB newA : Fin n → STape Γm) (h : BufEnc margin b tapesA tapesB)
    (hactive : b.active = true)
    (hmoved : newA i = PalPeg.CloseoutCoreEnc12.actList blankM (tapesA i)
      [some ((tapesA i).focus, .right)])
    (hkept : ∀ j, j ≠ i → newA j = tapesA j) :
    BufEnc margin (PalPeg.LocalBuffers.stepL
      (fun T => Function.update T i (PalPeg.GalilScaffoldTape.moveRight (T i))) b) newA tapesB := by
  refine ⟨fun j => ?_, ?_⟩
  · show newA j = padLeft margin (mapTape encProg (encTape
      ((PalPeg.LocalBuffers.stepL (fun T => Function.update T i
        (PalPeg.GalilScaffoldTape.moveRight (T i))) b).A j)))
    have hA : (PalPeg.LocalBuffers.stepL (fun T => Function.update T i
        (PalPeg.GalilScaffoldTape.moveRight (T i))) b).A
        = Function.update b.A i (PalPeg.GalilScaffoldTape.moveRight (b.A i)) := by
      unfold PalPeg.LocalBuffers.stepL
      rw [hactive]
    rw [hA]
    have hsel : (if j = i then PalPeg.CloseoutCoreEnc12.actList blankM (tapesA j)
        [some ((tapesA j).focus, .right)] else tapesA j) = newA j := by
      by_cases hji : j = i
      · subst hji
        rw [if_pos rfl, hmoved]
      · rw [if_neg hji, hkept j hji]
    rw [← hsel]
    exact prog_slots_after_right margin i b.A tapesA h.1 j
  · intro j
    show tapesB j = padLeft margin (mapTape encProg (encTape
      ((PalPeg.LocalBuffers.stepL (fun T => Function.update T i
        (PalPeg.GalilScaffoldTape.moveRight (T i))) b).B j)))
    have hB : (PalPeg.LocalBuffers.stepL (fun T => Function.update T i
        (PalPeg.GalilScaffoldTape.moveRight (T i))) b).B = b.B := by
      unfold PalPeg.LocalBuffers.stepL
      rw [hactive]
    rw [hB]
    exact h.2 j

/-! ### one abstract tick is one local step of the physical state

This is the statement the whole obligation turns on, and it can only be made once the state is
the physical one.  `abs` sends `GalilVML`'s live buffer half to the abstract program's tapes
(`LocalState.lean:189`), so a step of the live half *is* the abstract step of the program. -/

theorem abs_stepL {n : ℕ} (f : (Fin n → PalPeg.GalilScaffoldTape.Tape) → (Fin n → PalPeg.GalilScaffoldTape.Tape))
    (b : PalPeg.LocalBuffers.Buffered n) :
    PalPeg.LocalBuffers.abs (PalPeg.LocalBuffers.stepL f b) = f (PalPeg.LocalBuffers.abs b) := by
  cases hactive : b.active <;>
    simp [PalPeg.LocalBuffers.abs, PalPeg.LocalBuffers.stepL, hactive]

/-- **the mark walk forward, as a step of the physical state.**  The abstract tick moves
tape 8 of the preparation program; the physical state moves tape 8 of whichever buffer half is
live, and nothing else changes — not the counter bank, not the cursors, not the idle half. -/
theorem vml_markEnd_forward {P : ℕ} (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (y : PalPeg.LocalState.GalilVML P)
    (hmode : y.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd)
    (hnotEnd : (PalPeg.LocalBuffers.abs y.fppBuf 8).focus ≠ 5) :
    PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay
        (PalPeg.LocalReplayParked.absState'' y)
      = PalPeg.LocalReplayParked.absState''
          {y with fppBuf := PalPeg.LocalBuffers.stepL (fun T => Function.update T 8 (PalPeg.GalilScaffoldTape.moveRight (T 8))) y.fppBuf} := by
  have hstate : PalPeg.LocalReplayParked.absState'' y
      = (⟨y.ctl, PalPeg.LocalReplayParked.abs'' y⟩ : State GalilVM) := rfl
  rw [hstate]
  simp only [PalPeg.GalilScaffoldTop.tickFun, hmode, frameFun_atEnd, frameFun_markForward]
  rw [if_neg (show ¬ (decide (((PalPeg.LocalReplayParked.abs'' y).fpp.program.config.tapes 8).focus = 5) = true) from by simp only [decide_eq_true_eq]; exact hnotEnd)]
  unfold PalPeg.LocalReplayParked.absState'' PalPeg.LocalReplayParked.abs''
    PalPeg.LocalArrival.abs' PalPeg.LocalState.abs
    PalPeg.GalilScaffoldChainInputSupply.FppControl.tape PalPeg.GalilScaffoldLoading.put
  simp only [abs_stepL]
  rfl

/-- **the mark walk back, as a step of the physical state.**  The tick also
sends the controller to `choose` and clears the parity bit -/
theorem vml_markEnd_back {P : ℕ} (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (y : PalPeg.LocalState.GalilVML P)
    (hmode : y.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd)
    (htest : (PalPeg.LocalBuffers.abs y.fppBuf 8).focus = 5) :
    PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay
        (PalPeg.LocalReplayParked.absState'' y)
      = PalPeg.LocalReplayParked.absState'' {y with ctl := {y.ctl with mode := PalPeg.GalilScaffoldController.Mode.choose, odd := false}, fppBuf := PalPeg.LocalBuffers.stepL (fun T => Function.update T 8 (PalPeg.GalilScaffoldTape.moveLeft (T 8))) y.fppBuf} := by
  have hstate : PalPeg.LocalReplayParked.absState'' y
      = (⟨y.ctl, PalPeg.LocalReplayParked.abs'' y⟩ : State GalilVM) := rfl
  rw [hstate]
  simp only [PalPeg.GalilScaffoldTop.tickFun, hmode, frameFun_atEnd, frameFun_markBack]
  rw [if_pos (show (decide (((PalPeg.LocalReplayParked.abs'' y).fpp.program.config.tapes 8).focus = 5) = true) from by simp only [decide_eq_true_eq]; exact htest)]
  unfold PalPeg.LocalReplayParked.absState'' PalPeg.LocalReplayParked.abs''
    PalPeg.LocalArrival.abs' PalPeg.LocalState.abs
    PalPeg.GalilScaffoldChainInputSupply.FppControl.tape PalPeg.GalilScaffoldLoading.put
  simp only [abs_stepL]
  rfl

/-- the walk home, as a step of the physical state: the seventh tape of the
live half moves one cell left and the controller stands still -/
theorem vml_home_step {P : ℕ} (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (y : PalPeg.LocalState.GalilVML P)
    (hmode : y.ctl.mode = PalPeg.GalilScaffoldController.Mode.home)
    (htest : (PalPeg.LocalBuffers.abs y.fppBuf 7).focus ≠ 4) :
    PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay
        (PalPeg.LocalReplayParked.absState'' y)
      = PalPeg.LocalReplayParked.absState'' {y with ctl := y.ctl, fppBuf := PalPeg.LocalBuffers.stepL (fun T => Function.update T 7 (PalPeg.GalilScaffoldTape.moveLeft (T 7))) y.fppBuf} := by
  have hstate : PalPeg.LocalReplayParked.absState'' y
      = (⟨y.ctl, PalPeg.LocalReplayParked.abs'' y⟩ : State GalilVM) := rfl
  rw [hstate]
  simp only [PalPeg.GalilScaffoldTop.tickFun, hmode, frameFun_atLeft, frameFun_homeStep]
  rw [if_neg (show ¬ (decide (((PalPeg.LocalReplayParked.abs'' y).fpp.program.config.tapes 7).focus = 4) = true) from by simp only [decide_eq_true_eq]; exact htest)]
  unfold PalPeg.LocalReplayParked.absState'' PalPeg.LocalReplayParked.abs''
    PalPeg.LocalArrival.abs' PalPeg.LocalState.abs
    PalPeg.GalilScaffoldChainInputSupply.FppControl.tape PalPeg.GalilScaffoldLoading.put
  simp only [abs_stepL]
  rfl

/-- the parity walk of `choose`, as a step of the physical state: the same
move as the mark walk, with the parity bit flipped -/
theorem vml_choose_back {P : ℕ} (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (y : PalPeg.LocalState.GalilVML P)
    (hmode : y.ctl.mode = PalPeg.GalilScaffoldController.Mode.choose)
    (htest : (y.ctl.odd && (decide ((PalPeg.LocalBuffers.abs y.fppBuf 8).focus = 8) || decide ((PalPeg.LocalBuffers.abs y.fppBuf 8).focus = first))) = false) :
    PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay
        (PalPeg.LocalReplayParked.absState'' y)
      = PalPeg.LocalReplayParked.absState'' {y with ctl := {y.ctl with odd := !y.ctl.odd}, fppBuf := PalPeg.LocalBuffers.stepL (fun T => Function.update T 8 (PalPeg.GalilScaffoldTape.moveLeft (T 8))) y.fppBuf} := by
  have hstate : PalPeg.LocalReplayParked.absState'' y
      = (⟨y.ctl, PalPeg.LocalReplayParked.abs'' y⟩ : State GalilVM) := rfl
  rw [hstate]
  simp only [PalPeg.GalilScaffoldTop.tickFun, hmode, frameFun_markSet, frameFun_markBack]
  rw [if_neg (show ¬ ((y.ctl.odd && (decide (((PalPeg.LocalReplayParked.abs'' y).fpp.program.config.tapes 8).focus = 8) || decide (((PalPeg.LocalReplayParked.abs'' y).fpp.program.config.tapes 8).focus = first))) = true) from by
    have hfold : ((PalPeg.LocalReplayParked.abs'' y).fpp.program.config.tapes 8)
        = PalPeg.LocalBuffers.abs y.fppBuf 8 := rfl
    rw [hfold, htest]
    simp)]
  unfold PalPeg.LocalReplayParked.absState'' PalPeg.LocalReplayParked.abs''
    PalPeg.LocalArrival.abs' PalPeg.LocalState.abs
    PalPeg.GalilScaffoldChainInputSupply.FppControl.tape PalPeg.GalilScaffoldLoading.put
  simp only [abs_stepL]
  rfl

/-- **starting the preparation program, as a step of the physical state.**  No tape
moves at all: the program counter, the halting flag and the preparation's mode are fields of the
finite control, and the buffer keeps both halves untouched. -/
theorem vml_home_fppStart {P : ℕ} (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (y : PalPeg.LocalState.GalilVML P)
    (hmode : y.ctl.mode = PalPeg.GalilScaffoldController.Mode.home)
    (hatLeft : (PalPeg.LocalBuffers.abs y.fppBuf 7).focus = 4) :
    PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay
        (PalPeg.LocalReplayParked.absState'' y)
      = PalPeg.LocalReplayParked.absState'' {y with ctl := {y.ctl with mode := PalPeg.GalilScaffoldController.Mode.fpp}, fppPc := 320, fppDone := false, fppMode := .run} := by
  have hstate : PalPeg.LocalReplayParked.absState'' y
      = (⟨y.ctl, PalPeg.LocalReplayParked.abs'' y⟩ : State GalilVM) := rfl
  rw [hstate]
  simp only [PalPeg.GalilScaffoldTop.tickFun, hmode, frameFun_atLeft, frameFun_fppStart]
  rw [if_pos (show (decide (((PalPeg.LocalReplayParked.abs'' y).fpp.program.config.tapes 7).focus = 4) = true) from by simp only [decide_eq_true_eq]; exact hatLeft)]
  rfl

/-- the rewind's end test is the symbol under the head of the marks tape. -/
theorem frameFun_atFirst (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (s : GalilVM) :
    (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).atFirst s
      = decide ((s.fpp.program.config.tapes 8).focus = first) := rfl

theorem frameFun_fppReset (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (s : GalilVM) :
    (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).fppReset s
      = {s with fpp := {s.fpp with program := PalPeg.GalilScaffoldControl.reset 320 s.fpp.program}} := rfl

/-- **wiping the preparation program, as a step of the physical state.**  The abstract
tick replaces all nine tapes by blanks; the physical state switches to the other half of the
double buffer and starts an erasure job on the one it left.  `LocalBuffers.abs_resetFresh` says
the live half then reads as the fresh bundle, so the two agree — and the machine moved no tape.
This is the step the earlier reading called "nine tapes blanked in one tick". -/
theorem vml_rewind_fppReset {P : ℕ} (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (y : PalPeg.LocalState.GalilVML P)
    (hmode : y.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind)
    (hatFirst : (PalPeg.LocalBuffers.abs y.fppBuf 8).focus = first) :
    PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay
        (PalPeg.LocalReplayParked.absState'' y)
      = PalPeg.LocalReplayParked.absState'' {y with ctl := {y.ctl with mode := PalPeg.GalilScaffoldController.Mode.replayStart}, fppBuf := PalPeg.LocalBuffers.resetFresh y.fppBuf, fppPc := 320, fppDone := true} := by
  have hstate : PalPeg.LocalReplayParked.absState'' y
      = (⟨y.ctl, PalPeg.LocalReplayParked.abs'' y⟩ : State GalilVM) := rfl
  rw [hstate]
  simp only [PalPeg.GalilScaffoldTop.tickFun, hmode, frameFun_atFirst, frameFun_fppReset]
  rw [if_pos (show (decide (((PalPeg.LocalReplayParked.abs'' y).fpp.program.config.tapes 8).focus = first) = true) from by simp only [decide_eq_true_eq]; exact hatFirst)]
  unfold PalPeg.LocalReplayParked.absState'' PalPeg.LocalReplayParked.abs''
    PalPeg.LocalArrival.abs' PalPeg.LocalState.abs PalPeg.GalilScaffoldControl.reset
  simp only [PalPeg.LocalBuffers.abs_resetFresh]
  rfl

/-- the end of the copy stamps the seventh tape with the end marker, without moving it,
and puts the preparation into its walk-home mode. -/
theorem frameFun_copyEnd (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (s : GalilVM) :
    (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).copyEnd s
      = {s with fpp := {s.fpp with program := PalPeg.GalilScaffoldChainInputSupply.FppControl.tape s.fpp 7 (fun t => PalPeg.GalilScaffoldTape.write t 5), mode := .home, finalStage := (PalPeg.GalilScaffoldPlace.read s.fpp.walker).isNone}} := rfl

/-- **the end of the copy, as a step of the physical state.**  One stamp on the live
half's seventh tape, and three fields of the finite control: the controller's mode, the
preparation's mode, and its final-stage flag.  The flag is a reading of the preparation's cursor,
which the machine has in its own window. -/
theorem vml_copy_end {P : ℕ} (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (y : PalPeg.LocalState.GalilVML P)
    (hmode : y.ctl.mode = PalPeg.GalilScaffoldController.Mode.copy)
    (htest : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).remainingPos
      (PalPeg.LocalReplayParked.abs'' y) = false) :
    PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay
        (PalPeg.LocalReplayParked.absState'' y)
      = PalPeg.LocalReplayParked.absState'' {y with ctl := {y.ctl with mode := PalPeg.GalilScaffoldController.Mode.home}, fppBuf := PalPeg.LocalBuffers.stepL (fun T => Function.update T 7 (PalPeg.GalilScaffoldTape.write (T 7) 5)) y.fppBuf, fppMode := .home, fppFinalStage := (PalPeg.GalilScaffoldPlace.read (PalPeg.LocalReplayParked.abs'' y).fpp.walker).isNone} := by
  have hstate : PalPeg.LocalReplayParked.absState'' y
      = (⟨y.ctl, PalPeg.LocalReplayParked.abs'' y⟩ : State GalilVM) := rfl
  rw [hstate]
  simp only [PalPeg.GalilScaffoldTop.tickFun, hmode, frameFun_copyEnd]
  rw [if_neg (by simp [htest])]
  unfold PalPeg.LocalReplayParked.absState'' PalPeg.LocalReplayParked.abs''
    PalPeg.LocalArrival.abs' PalPeg.LocalState.abs
    PalPeg.GalilScaffoldChainInputSupply.FppControl.tape PalPeg.GalilScaffoldLoading.put
  simp only [abs_stepL]
  rfl

/-- **the last tick of the fallback copy**: the copy has nothing left to move, so it writes the
end mark where its head stands and hands the machine to the walk home.  One action on one tape,
and two bits of the finite control. -/
theorem copy_end {fppBound dpBound : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (tapes newTapes : Slot → STape Γm)
    (bit : Bool)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.copy)
    (hdone : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).remainingPos x.vm
      = false)
    (hbit : bit = (PalPeg.GalilScaffoldPlace.read x.vm.fpp.walker).isNone)
    (henc : Enc w margin x (q, tapes))
    (hmoved : newTapes (progSlotOf q.fppLive 7)
      = PalPeg.CloseoutCoreEnc12.actList blankM (tapes (progSlotOf q.fppLive 7))
          [some (encProg 5, (.stay : PalPeg.CloseoutCoreEnc12.MoveC))])
    (hkept : ∀ slot, slot ≠ progSlotOf q.fppLive 7 →
      (∀ k : Fin 9, slot ≠ progSlotOf (!q.fppLive) k) → newTapes slot = tapes slot)
    (hidleShape : ∀ k : Fin 9, ∃ raw : STape (Fin 9),
      newTapes (progSlotOf (!q.fppLive) k) = padLeft margin (mapTape encProg raw)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ({q with ctl := {q.ctl with mode := PalPeg.GalilScaffoldController.Mode.home}, fppMode := PalPeg.GalilScaffoldChainInputSupply.FppControl.Mode.home, fppFinalStage := bit}, newTapes) := by
  have hval : PalPeg.GalilScaffoldTop.tickFun
      (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x
      = ⟨{x.ctl with mode := PalPeg.GalilScaffoldController.Mode.home}, {x.vm with fpp := PalPeg.FrameFunction.copyEndFun x.vm.fpp}⟩ := by
    simp only [PalPeg.GalilScaffoldTop.tickFun, hmode, frameFun_copyEnd]
    rw [if_neg (by simp [hdone])]
    rfl
  have hstep : newTapes (progSlotOf q.fppLive 7)
      = padLeft margin (mapTape encProg (encTape
          (PalPeg.GalilScaffoldTape.write (x.vm.fpp.program.config.tapes 7) 5))) := by
    rw [hmoved, show tapes (progSlotOf q.fppLive 7)
        = padLeft margin (mapTape encProg (encTape (x.vm.fpp.program.config.tapes 7)))
        from henc.2.fpp 7, padded_write]
    rfl
  rw [hval]
  refine ⟨encControl_copyEnd x q henc.1 {q.ctl with mode := PalPeg.GalilScaffoldController.Mode.home} {x.ctl with mode := PalPeg.GalilScaffoldController.Mode.home} (by rw [← henc.1.ctl]; rfl) bit hbit, ?_⟩
  exact encTapes_congr margin
    ⟨{x.ctl with mode := PalPeg.GalilScaffoldController.Mode.home}, {x.vm with fpp := {x.vm.fpp with program := PalPeg.GalilScaffoldChainInputSupply.FppControl.tape x.vm.fpp 7 (fun t => PalPeg.GalilScaffoldTape.write t 5)}}⟩
    ⟨{x.ctl with mode := PalPeg.GalilScaffoldController.Mode.home}, {x.vm with fpp := PalPeg.FrameFunction.copyEndFun x.vm.fpp}⟩
    q.polarity q.gap q.micro q.fppLive q.dpLive newTapes
    (fun i => rfl) (fun i => rfl) rfl rfl rfl rfl rfl
    (encTapes_fppStep margin x q.polarity q.gap q.micro q.fppLive q.dpLive tapes newTapes henc.2
      7 (fun t => PalPeg.GalilScaffoldTape.write t 5)
      {x.ctl with mode := PalPeg.GalilScaffoldController.Mode.home} hstep hkept hidleShape)

/-! ### the fallback copy: a tick that moves three components at once

`copyOne` writes the walker's letter onto the seventh tape of the preparation program, walks that
tape right, takes one off the `fppWork` counter and steps the walker one place left.  All three
are already local operations of `GalilVML` — `LocalTick3.copyVm` is the step and
`LocalTick3.abs'_copyVm` is its abstraction.  What is new here is the *tick* form: the abstract
controller's own step function lands on exactly that physical state. -/

/-- the parked right head is decided by three readings: the replay flag, the replay counter and
the physical right view.  A step that leaves all three alone leaves it alone. -/
theorem absR_congr {P : ℕ} {y z : PalPeg.LocalState.GalilVML P}
    (hctl : z.ctl.replaying = y.ctl.replaying)
    (hrval : PalPeg.LocalReplayParked.rval z = PalPeg.LocalReplayParked.rval y)
    (hhead : PalPeg.LocalReplayParked.physHead z = PalPeg.LocalReplayParked.physHead y) :
    PalPeg.LocalReplayParked.absR z = PalPeg.LocalReplayParked.absR y := by
  unfold PalPeg.LocalReplayParked.absR
  rw [hctl, hrval, hhead]

/-- and a bank tick that keeps the replay counter keeps the replay counter's value, whatever it
does to the other fifteen. -/
theorem rval_bankTick {P : ℕ} {y : PalPeg.LocalState.GalilVML P}
    (hinj : PalPeg.LocalState.RolesInjective y) {f : PalPeg.LocalState.Ctr → PalPeg.LocalTick3.Op}
    (hkeep : f .replay = PalPeg.LocalTick3.Op.keep) :
    PalPeg.LocalReplayParked.rval (PalPeg.LocalTick3.bankTick f y)
      = PalPeg.LocalReplayParked.rval y := by
  show PalPeg.LocalCounter.val ((PalPeg.LocalTick3.bankTick f y).phys
    ((PalPeg.LocalTick3.bankTick f y).roles .replay)) = _
  rw [PalPeg.LocalTick3.bankTick_phys hinj f .replay, hkeep]
  rfl

/-- **one copy tick of the controller is one local step of the physical state.** -/
theorem vml_copy_one {P : ℕ} (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (y : PalPeg.LocalState.GalilVML P) (a : Fin 3)
    (hmode : y.ctl.mode = PalPeg.GalilScaffoldController.Mode.copy)
    (hrem : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).remainingPos
      (PalPeg.LocalReplayParked.abs'' y) = true)
    (hread : PalPeg.GalilScaffoldPlace.read (PalPeg.LocalState.absPlace y.fppWalker) = some a)
    (hinj : PalPeg.LocalState.RolesInjective y)
    (hpol : y.pol .fppWork = true)
    (hval : 0 < PalPeg.LocalCounter.val (y.phys (y.roles .fppWork)))
    (hprop : PalPeg.LocalChain.ProperView y.fppWalker) :
    PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay
        (PalPeg.LocalReplayParked.absState'' y)
      = PalPeg.LocalReplayParked.absState'' (PalPeg.LocalTick3.copyVm a y) := by
  have hstate : PalPeg.LocalReplayParked.absState'' y
      = (⟨y.ctl, PalPeg.LocalReplayParked.abs'' y⟩ : State GalilVM) := rfl
  rw [hstate]
  simp only [PalPeg.GalilScaffoldTop.tickFun, hmode]
  rw [if_pos hrem]
  show (⟨y.ctl, _⟩ : State GalilVM) = _
  have habs : PalPeg.LocalReplayParked.abs'' (PalPeg.LocalTick3.copyVm a y)
      = { PalPeg.LocalReplayParked.abs'' y with
          fpp := PalPeg.FrameFunction.copyOneFun (PalPeg.LocalReplayParked.abs'' y).fpp } := by
    have hfpp : (PalPeg.LocalReplayParked.abs'' y).fpp
        = (PalPeg.LocalArrival.abs' y).fpp := rfl
    have hcopy : PalPeg.FrameFunction.copyOneFun (PalPeg.LocalArrival.abs' y).fpp
        = { (PalPeg.LocalArrival.abs' y).fpp with
            program := PalPeg.GalilScaffoldChainInputSupply.FppControl.tape
              (PalPeg.LocalArrival.abs' y).fpp 7 (fun t => PalPeg.GalilScaffoldTape.moveRight
                (PalPeg.GalilScaffoldTape.write t (PalPeg.GalilFppPreparation.symbol a))),
            work := PalPeg.GalilScaffoldCounter.dec (PalPeg.LocalArrival.abs' y).fpp.work,
            walker := PalPeg.GalilScaffoldPlace.left (PalPeg.LocalArrival.abs' y).fpp.walker } := by
      unfold PalPeg.FrameFunction.copyOneFun
      rw [show (PalPeg.LocalArrival.abs' y).fpp.walker
        = PalPeg.LocalState.absPlace y.fppWalker from rfl, hread]
    show { PalPeg.LocalArrival.abs' (PalPeg.LocalTick3.copyVm a y) with
        right := PalPeg.LocalReplayParked.absR (PalPeg.LocalTick3.copyVm a y) } = _
    rw [PalPeg.LocalTick3.abs'_copyVm hinj a hpol hval hprop,
      absR_congr (z := PalPeg.LocalTick3.copyVm a y) (y := y) rfl
        (rval_bankTick hinj (f := PalPeg.LocalTick3.workOps) rfl) rfl, hfpp, hcopy]
    rfl
  show _ = (⟨y.ctl, PalPeg.LocalReplayParked.abs'' (PalPeg.LocalTick3.copyVm a y)⟩ : State GalilVM)
  rw [habs]
  rfl

/-! ### the program run, decomposed into one action per tick

The abstract `fpp` quantum is `fppRunFun q`, a run of `q` calls of the program machine, and the
local layer runs the same quantum as `fppRunBuf g q`, `g k` being the tape action of the `k`-th
call.  For the two to be the same the program's own tick has to be exhibited as *one action on
one slot*, which is what this section does: a tick either moves a head one cell, writes one
symbol, or touches no tape at all (a `read`, a halt, a stuck program counter). -/

open PalPeg.GalilFppWide (Instruction)

/-- **the tape action of one call of the program machine.**  Constant in the tape it is
given: which slot moves and how is decided by the instruction under the program counter. -/
def progStepTapes {n : ℕ} (code : List (Instruction n)) (m : PalPeg.GalilScaffoldControl.Machine n) :
    Fin n → PalPeg.GalilScaffoldTape.Tape → PalPeg.GalilScaffoldTape.Tape :=
  if m.done then fun _ => id
  else
    match code[m.config.pc]? with
    | some (.move t true _) => Function.update (fun _ => id) t PalPeg.GalilScaffoldTape.moveRight
    | some (.move t false _) => Function.update (fun _ => id) t PalPeg.GalilScaffoldTape.moveLeft
    | some (.write t sym _) =>
        Function.update (fun _ => id) t (fun tp => PalPeg.GalilScaffoldTape.write tp sym)
    | _ => fun _ => id

/-- **and that is the whole tape effect of the call.**  Everything else a tick does —
the new program counter, the halting flag — lives in the finite control. -/
theorem progTickFun_tapes {n : ℕ} (code : List (Instruction n))
    (m : PalPeg.GalilScaffoldControl.Machine n) :
    (PalPeg.ProgramFunction.tickFun code true m).config.tapes
      = fun i => progStepTapes code m i (m.config.tapes i) := by
  unfold PalPeg.ProgramFunction.tickFun progStepTapes
  cases hdone : m.done
  · rw [if_neg (by simp [hdone])]
    simp only [Bool.false_eq_true, if_false]
    match hcode : code[m.config.pc]? with
    | none => simp [hcode]
    | some .halt => simp [hcode]
    | some (.read t cs) =>
        simp only [hcode]
        show (PalPeg.ProgramFunction.executeFun (.read t cs) m.config).tapes = _
        unfold PalPeg.ProgramFunction.executeFun
        cases hfind : (cs.find? (fun choice => choice.1 = (m.config.tapes t).focus)) <;>
          simp [hfind]
    | some (.write t sym pc) =>
        simp only [hcode]
        show (PalPeg.GalilScaffoldProgram.changed m.config t
          (PalPeg.GalilScaffoldTape.write (m.config.tapes t) sym) pc).tapes = _
        funext i
        by_cases hit : i = t
        · subst hit; simp [PalPeg.GalilScaffoldProgram.changed]
        · simp [PalPeg.GalilScaffoldProgram.changed, hit]
    | some (.move t dir pc) =>
        cases dir
        · simp only [hcode]
          show (PalPeg.GalilScaffoldProgram.changed m.config t
            (PalPeg.GalilScaffoldTape.moveLeft (m.config.tapes t)) pc).tapes = _
          funext i
          by_cases hit : i = t
          · subst hit; simp [PalPeg.GalilScaffoldProgram.changed]
          · simp [PalPeg.GalilScaffoldProgram.changed, hit]
        · simp only [hcode]
          show (PalPeg.GalilScaffoldProgram.changed m.config t
            (PalPeg.GalilScaffoldTape.moveRight (m.config.tapes t)) pc).tapes = _
          funext i
          by_cases hit : i = t
          · subst hit; simp [PalPeg.GalilScaffoldProgram.changed]
          · simp [PalPeg.GalilScaffoldProgram.changed, hit]
  · rw [if_pos (by simp [hdone])]
    simp [hdone]

/-- the quantum only reads the actions below its own length. -/
theorem fppRunBuf_congr (g g' : ℕ → Fin 9 → PalPeg.GalilScaffoldTape.Tape → PalPeg.GalilScaffoldTape.Tape) :
    ∀ (q : ℕ) (b : PalPeg.LocalBuffers.Buffered 9), (∀ k, k < q → g k = g' k) →
      PalPeg.LocalTick3.fppRunBuf g q b = PalPeg.LocalTick3.fppRunBuf g' q b := by
  intro q
  induction q with
  | zero => intro b _; rfl
  | succ q ih =>
      intro b h
      show PalPeg.LocalTick3.fppRunBuf g q
          (PalPeg.LocalBuffers.stepL (fun ts i => g q i (ts i)) b) = _
      rw [h q (Nat.lt_succ_self q)]
      exact ih _ (fun k hk => h k (Nat.lt_succ_of_lt hk))

/-- **the abstract quantum is the local quantum.**  Running the program machine `q`
times from the live half of the buffer is running the buffer `q` times, the `k`-th step carrying
the action the `k`-th call performs.  The actions are built from the run itself, so nothing here
assumes the program's control flow is known in advance. -/
theorem abs_fppRunBuf (code : List (Instruction 9)) :
    ∀ (q : ℕ) (b : PalPeg.LocalBuffers.Buffered 9) (pc : ℕ) (done : Bool),
      ∃ g : ℕ → Fin 9 → PalPeg.GalilScaffoldTape.Tape → PalPeg.GalilScaffoldTape.Tape,
        PalPeg.LocalBuffers.abs (PalPeg.LocalTick3.fppRunBuf g q b)
          = (PalPeg.ProgramFunction.runFun code (List.replicate q true)
              ⟨⟨pc, PalPeg.LocalBuffers.abs b⟩, done⟩).config.tapes := by
  intro q
  induction q with
  | zero => intro b pc done; exact ⟨fun _ _ => id, rfl⟩
  | succ q ih =>
      intro b pc done
      obtain ⟨g', hg'⟩ := ih
        (PalPeg.LocalBuffers.stepL (fun ts i => (progStepTapes code (⟨⟨pc, PalPeg.LocalBuffers.abs b⟩, done⟩ : PalPeg.GalilScaffoldControl.Machine 9)) i (ts i)) b)
        (PalPeg.ProgramFunction.tickFun code true
          ⟨⟨pc, PalPeg.LocalBuffers.abs b⟩, done⟩).config.pc
        (PalPeg.ProgramFunction.tickFun code true
          ⟨⟨pc, PalPeg.LocalBuffers.abs b⟩, done⟩).done
      refine ⟨Function.update g' q (progStepTapes code (⟨⟨pc, PalPeg.LocalBuffers.abs b⟩, done⟩ : PalPeg.GalilScaffoldControl.Machine 9)), ?_⟩
      have hstep : PalPeg.LocalTick3.fppRunBuf (Function.update g' q (progStepTapes code (⟨⟨pc, PalPeg.LocalBuffers.abs b⟩, done⟩ : PalPeg.GalilScaffoldControl.Machine 9))) (q + 1) b
          = PalPeg.LocalTick3.fppRunBuf g'  q
              (PalPeg.LocalBuffers.stepL (fun ts i => (progStepTapes code (⟨⟨pc, PalPeg.LocalBuffers.abs b⟩, done⟩ : PalPeg.GalilScaffoldControl.Machine 9)) i (ts i)) b) := by
        show PalPeg.LocalTick3.fppRunBuf (Function.update g' q (progStepTapes code (⟨⟨pc, PalPeg.LocalBuffers.abs b⟩, done⟩ : PalPeg.GalilScaffoldControl.Machine 9))) q
            (PalPeg.LocalBuffers.stepL
              (fun ts i => Function.update g' q (progStepTapes code (⟨⟨pc, PalPeg.LocalBuffers.abs b⟩, done⟩ : PalPeg.GalilScaffoldControl.Machine 9)) q i (ts i)) b) = _
        rw [show Function.update g' q (progStepTapes code (⟨⟨pc, PalPeg.LocalBuffers.abs b⟩, done⟩ : PalPeg.GalilScaffoldControl.Machine 9)) q = (progStepTapes code (⟨⟨pc, PalPeg.LocalBuffers.abs b⟩, done⟩ : PalPeg.GalilScaffoldControl.Machine 9)) by simp]
        exact fppRunBuf_congr _ _ q _
          (fun k hk => by simp [Nat.ne_of_lt hk])
      have habs : PalPeg.LocalBuffers.abs
          (PalPeg.LocalBuffers.stepL (fun ts i => (progStepTapes code (⟨⟨pc, PalPeg.LocalBuffers.abs b⟩, done⟩ : PalPeg.GalilScaffoldControl.Machine 9)) i (ts i)) b)
          = (PalPeg.ProgramFunction.tickFun code true
              ⟨⟨pc, PalPeg.LocalBuffers.abs b⟩, done⟩).config.tapes := by
        rw [abs_stepL]
        exact (progTickFun_tapes code ⟨⟨pc, PalPeg.LocalBuffers.abs b⟩, done⟩).symm
      rw [hstep, hg', habs, List.replicate_succ]
      rfl

/-- **a quantum of the preparation program, as a step of the physical state.**  The
controller's `fpp` tick runs `q` calls of the marked code; the physical state runs the same `q`
calls on the live half of its buffer and keeps the resulting program counter in its finite
control.  The actions come from the run, so the branch names them without knowing the control
flow in advance. -/
theorem vml_fpp_slice {P : ℕ} (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (y : PalPeg.LocalState.GalilVML P)
    (hmode : y.ctl.mode = PalPeg.GalilScaffoldController.Mode.fpp)
    (hnothalt : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).fppHalts
      (PalPeg.LocalReplayParked.abs'' y) = false) :
    ∃ (g : ℕ → Fin 9 → PalPeg.GalilScaffoldTape.Tape → PalPeg.GalilScaffoldTape.Tape) (pc : ℕ),
      PalPeg.GalilScaffoldTop.tickFun
          (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay
          (PalPeg.LocalReplayParked.absState'' y)
        = PalPeg.LocalReplayParked.absState'' (PalPeg.LocalTick3.sliceVm g entryQ pc y) := by
  obtain ⟨g, hg⟩ := abs_fppRunBuf PalPeg.GalilFppMarkedCode.code entryQ y.fppBuf y.fppPc y.fppDone
  refine ⟨g, (PalPeg.ProgramFunction.fppRunFun entryQ
    ⟨⟨y.fppPc, PalPeg.LocalBuffers.abs y.fppBuf⟩, y.fppDone⟩).config.pc, ?_⟩
  have hstate : PalPeg.LocalReplayParked.absState'' y
      = (⟨y.ctl, PalPeg.LocalReplayParked.abs'' y⟩ : State GalilVM) := rfl
  rw [hstate]
  simp only [PalPeg.GalilScaffoldTop.tickFun, hmode]
  rw [if_neg (by simp [hnothalt])]
  have hdone : (PalPeg.ProgramFunction.fppRunFun entryQ
      ⟨⟨y.fppPc, PalPeg.LocalBuffers.abs y.fppBuf⟩, y.fppDone⟩).done = false := hnothalt
  have hprog : PalPeg.ProgramFunction.fppRunFun entryQ
        ⟨⟨y.fppPc, PalPeg.LocalBuffers.abs y.fppBuf⟩, y.fppDone⟩
      = ⟨⟨(PalPeg.ProgramFunction.fppRunFun entryQ
            ⟨⟨y.fppPc, PalPeg.LocalBuffers.abs y.fppBuf⟩, y.fppDone⟩).config.pc,
          PalPeg.LocalBuffers.abs
            (PalPeg.LocalTick3.fppRunBuf g entryQ y.fppBuf)⟩, false⟩ := by
    rw [hg]
    exact congrArg (fun d => (⟨(PalPeg.ProgramFunction.fppRunFun entryQ
      ⟨⟨y.fppPc, PalPeg.LocalBuffers.abs y.fppBuf⟩, y.fppDone⟩).config, d⟩ :
        PalPeg.GalilScaffoldControl.Machine 9)) hdone
  have habs : PalPeg.LocalReplayParked.abs''
        (PalPeg.LocalTick3.sliceVm g entryQ (PalPeg.ProgramFunction.fppRunFun entryQ
          ⟨⟨y.fppPc, PalPeg.LocalBuffers.abs y.fppBuf⟩, y.fppDone⟩).config.pc y)
      = { PalPeg.LocalReplayParked.abs'' y with
          fpp := PalPeg.ProgramFunction.fppSliceFun entryQ
            (PalPeg.LocalReplayParked.abs'' y).fpp } := by
    show { PalPeg.LocalArrival.abs' (PalPeg.LocalTick3.sliceVm g entryQ _ y) with
        right := PalPeg.LocalReplayParked.absR y } = _
    rw [PalPeg.LocalTick3.abs'_sliceVm]
    show _ = { PalPeg.LocalReplayParked.abs'' y with
      fpp := { (PalPeg.LocalArrival.abs' y).fpp with
        program := PalPeg.ProgramFunction.fppRunFun entryQ
          ⟨⟨y.fppPc, PalPeg.LocalBuffers.abs y.fppBuf⟩, y.fppDone⟩ } }
    rw [hprog]
    rfl
  show _ = (⟨y.ctl, PalPeg.LocalReplayParked.abs''
    (PalPeg.LocalTick3.sliceVm g entryQ _ y)⟩ : State GalilVM)
  rw [habs]
  rfl

/-- **one rewind tick that walks a single head.**  The marks tape moves one cell left, the left
head one place left and `length` takes a push; the controller flips its pair bit. -/
theorem vml_rewind_one {P : ℕ} (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (y : PalPeg.LocalState.GalilVML P)
    (hmode : y.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind)
    (hnotFirst : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).atFirst
      (PalPeg.LocalReplayParked.abs'' y) = false)
    (hpair : y.ctl.pair = false)
    (hinj : PalPeg.LocalState.RolesInjective y)
    (hlen : y.pol .length = true) :
    PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay
        (PalPeg.LocalReplayParked.absState'' y)
      = PalPeg.LocalReplayParked.absState''
          (PalPeg.LocalTick3.rewindOneVm {y.ctl with pair := true} y) := by
  have hstate : PalPeg.LocalReplayParked.absState'' y
      = (⟨y.ctl, PalPeg.LocalReplayParked.abs'' y⟩ : State GalilVM) := rfl
  rw [hstate]
  simp only [PalPeg.GalilScaffoldTop.tickFun, hmode]
  rw [if_neg (by simp [hnotFirst]), if_neg (by simp [hpair])]
  show _ = (⟨{y.ctl with mode := PalPeg.GalilScaffoldController.Mode.rewind, pair := true},
    PalPeg.LocalReplayParked.abs'' (PalPeg.LocalTick3.rewindOneVm
      {y.ctl with mode := PalPeg.GalilScaffoldController.Mode.rewind, pair := true} y)⟩ :
      State GalilVM)
  have habs : PalPeg.LocalReplayParked.abs''
        (PalPeg.LocalTick3.rewindOneVm
          {y.ctl with mode := PalPeg.GalilScaffoldController.Mode.rewind, pair := true} y)
      = (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).rewindOne
          (PalPeg.LocalReplayParked.abs'' y) := by
    show { PalPeg.LocalArrival.abs'
        (PalPeg.LocalTick3.rewindOneVm {y.ctl with mode := PalPeg.GalilScaffoldController.Mode.rewind, pair := true} y) with
        right := PalPeg.LocalReplayParked.absR
          (PalPeg.LocalTick3.rewindOneVm
            {y.ctl with mode := PalPeg.GalilScaffoldController.Mode.rewind, pair := true} y) } = _
    rw [PalPeg.LocalTick3.abs'_rewindOneVm hinj _ hlen,
      absR_congr (z := PalPeg.LocalTick3.rewindOneVm
          {y.ctl with mode := PalPeg.GalilScaffoldController.Mode.rewind, pair := true} y)
        (y := y) rfl
        (rval_bankTick hinj (f := PalPeg.LocalTick3.rewindOps1) rfl) rfl]
    rfl
  rw [habs]

/-- **one rewind tick that walks both heads.**  The same marks move, with the centre head and
`radius` carried along. -/
theorem vml_rewind_pair {P : ℕ} (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (y : PalPeg.LocalState.GalilVML P)
    (hmode : y.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind)
    (hnotFirst : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).atFirst
      (PalPeg.LocalReplayParked.abs'' y) = false)
    (hpair : y.ctl.pair = true)
    (hinj : PalPeg.LocalState.RolesInjective y)
    (hlen : y.pol .length = true) (hrad : y.pol .radius = true) :
    PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay
        (PalPeg.LocalReplayParked.absState'' y)
      = PalPeg.LocalReplayParked.absState''
          (PalPeg.LocalTick3.rewindPairVm {y.ctl with pair := false} y) := by
  have hstate : PalPeg.LocalReplayParked.absState'' y
      = (⟨y.ctl, PalPeg.LocalReplayParked.abs'' y⟩ : State GalilVM) := rfl
  rw [hstate]
  simp only [PalPeg.GalilScaffoldTop.tickFun, hmode]
  rw [if_neg (by simp [hnotFirst]), if_pos (by simp [hpair])]
  show _ = (⟨{y.ctl with mode := PalPeg.GalilScaffoldController.Mode.rewind, pair := false},
    PalPeg.LocalReplayParked.abs'' (PalPeg.LocalTick3.rewindPairVm
      {y.ctl with mode := PalPeg.GalilScaffoldController.Mode.rewind, pair := false} y)⟩ :
      State GalilVM)
  have habs : PalPeg.LocalReplayParked.abs''
        (PalPeg.LocalTick3.rewindPairVm
          {y.ctl with mode := PalPeg.GalilScaffoldController.Mode.rewind, pair := false} y)
      = (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).rewindPair
          (PalPeg.LocalReplayParked.abs'' y) := by
    show { PalPeg.LocalArrival.abs'
        (PalPeg.LocalTick3.rewindPairVm {y.ctl with mode := PalPeg.GalilScaffoldController.Mode.rewind, pair := false} y) with
        right := PalPeg.LocalReplayParked.absR
          (PalPeg.LocalTick3.rewindPairVm
            {y.ctl with mode := PalPeg.GalilScaffoldController.Mode.rewind, pair := false} y) } = _
    rw [PalPeg.LocalTick3.abs'_rewindPairVm hinj _ hlen hrad,
      absR_congr (z := PalPeg.LocalTick3.rewindPairVm
          {y.ctl with mode := PalPeg.GalilScaffoldController.Mode.rewind, pair := false} y)
        (y := y) rfl
        (rval_bankTick hinj (f := PalPeg.LocalTick3.rewindOps2) rfl) rfl]
    rfl
  rw [habs]

/-- **the tick that chooses a centre.**  Two bank ticks (`length` and `radius` reset, then
`length++`) and the ghost copy of the right head into the left and centre cursors. -/
theorem vml_choose_select {P : ℕ} (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (y : PalPeg.LocalState.GalilVML P)
    (hmode : y.ctl.mode = PalPeg.GalilScaffoldController.Mode.choose)
    (hset : (y.ctl.odd && (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).markSet
      (PalPeg.LocalReplayParked.abs'' y)) = true)
    (hinj : PalPeg.LocalState.RolesInjective y)
    (hlen : y.pol .length = true)
    (hpark : PalPeg.LocalReplayParked.abs'' y = PalPeg.LocalArrival.abs' y) :
    PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay
        (PalPeg.LocalReplayParked.absState'' y)
      = PalPeg.LocalReplayParked.absState''
          (PalPeg.LocalTick3.chooseSelectVm
            {y.ctl with mode := PalPeg.GalilScaffoldController.Mode.rewind, pair := false} y) := by
  have hstate : PalPeg.LocalReplayParked.absState'' y
      = (⟨y.ctl, PalPeg.LocalReplayParked.abs'' y⟩ : State GalilVM) := rfl
  rw [hstate]
  simp only [PalPeg.GalilScaffoldTop.tickFun, hmode]
  rw [if_pos hset]
  show _ = (⟨{y.ctl with mode := PalPeg.GalilScaffoldController.Mode.rewind, pair := false},
    PalPeg.LocalReplayParked.abs'' (PalPeg.LocalTick3.chooseSelectVm _ y)⟩ : State GalilVM)
  have hinj1 : PalPeg.LocalState.RolesInjective
      (PalPeg.LocalTick3.bankTick PalPeg.LocalTick3.chooseOps1 y) := hinj
  have habs : PalPeg.LocalReplayParked.abs''
        (PalPeg.LocalTick3.chooseSelectVm
          {y.ctl with mode := PalPeg.GalilScaffoldController.Mode.rewind, pair := false} y)
      = (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).choose
          (PalPeg.LocalReplayParked.abs'' y) := by
    show { PalPeg.LocalArrival.abs' (PalPeg.LocalTick3.chooseSelectVm {y.ctl with mode := PalPeg.GalilScaffoldController.Mode.rewind, pair := false} y) with
        right := PalPeg.LocalReplayParked.absR
          (PalPeg.LocalTick3.chooseSelectVm {y.ctl with mode := PalPeg.GalilScaffoldController.Mode.rewind, pair := false} y) } = _
    rw [PalPeg.LocalTick3.abs'_chooseSelectVm hinj _ hlen,
      absR_congr (z := PalPeg.LocalTick3.chooseSelectVm
          {y.ctl with mode := PalPeg.GalilScaffoldController.Mode.rewind, pair := false} y)
        (y := y) rfl
        ((rval_bankTick hinj1 (f := PalPeg.LocalTick3.chooseOps2) rfl).trans
          (rval_bankTick hinj (f := PalPeg.LocalTick3.chooseOps1) rfl)) rfl,
      show PalPeg.LocalReplayParked.absR y = (PalPeg.LocalArrival.abs' y).right from
        congrArg GalilVM.right hpark, hpark]
    rfl
  rw [habs]

/-- **the tick on which the preparation program halts.**  The same quantum as `vml_fpp_slice`,
followed by the two marks actions that open a fresh mark block. -/
theorem vml_fpp_done {P : ℕ} (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (y : PalPeg.LocalState.GalilVML P)
    (hmode : y.ctl.mode = PalPeg.GalilScaffoldController.Mode.fpp)
    (hhalt : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).fppHalts
      (PalPeg.LocalReplayParked.abs'' y) = true) :
    ∃ (g : ℕ → Fin 9 → PalPeg.GalilScaffoldTape.Tape → PalPeg.GalilScaffoldTape.Tape) (pc : ℕ),
      PalPeg.GalilScaffoldTop.tickFun
          (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay
          (PalPeg.LocalReplayParked.absState'' y)
        = PalPeg.LocalReplayParked.absState''
            (PalPeg.LocalTick3.doneVm first g entryQ pc
              {y.ctl with mode := PalPeg.GalilScaffoldController.Mode.markEnd} y) := by
  obtain ⟨g, hg⟩ := abs_fppRunBuf PalPeg.GalilFppMarkedCode.code entryQ y.fppBuf y.fppPc y.fppDone
  refine ⟨g, (PalPeg.ProgramFunction.fppRunFun entryQ
    ⟨⟨y.fppPc, PalPeg.LocalBuffers.abs y.fppBuf⟩, y.fppDone⟩).config.pc, ?_⟩
  have hstate : PalPeg.LocalReplayParked.absState'' y
      = (⟨y.ctl, PalPeg.LocalReplayParked.abs'' y⟩ : State GalilVM) := rfl
  rw [hstate]
  simp only [PalPeg.GalilScaffoldTop.tickFun, hmode]
  rw [if_pos hhalt]
  have hdone : (PalPeg.ProgramFunction.fppRunFun entryQ
      ⟨⟨y.fppPc, PalPeg.LocalBuffers.abs y.fppBuf⟩, y.fppDone⟩).done = true := hhalt
  have hprog : PalPeg.ProgramFunction.fppRunFun entryQ
        ⟨⟨y.fppPc, PalPeg.LocalBuffers.abs y.fppBuf⟩, y.fppDone⟩
      = ⟨⟨(PalPeg.ProgramFunction.fppRunFun entryQ
            ⟨⟨y.fppPc, PalPeg.LocalBuffers.abs y.fppBuf⟩, y.fppDone⟩).config.pc,
          PalPeg.LocalBuffers.abs
            (PalPeg.LocalTick3.fppRunBuf g entryQ y.fppBuf)⟩, true⟩ := by
    rw [hg]
    exact congrArg (fun d => (⟨(PalPeg.ProgramFunction.fppRunFun entryQ
      ⟨⟨y.fppPc, PalPeg.LocalBuffers.abs y.fppBuf⟩, y.fppDone⟩).config, d⟩ :
        PalPeg.GalilScaffoldControl.Machine 9)) hdone
  show _ = (⟨{y.ctl with mode := PalPeg.GalilScaffoldController.Mode.markEnd},
    PalPeg.LocalReplayParked.abs'' (PalPeg.LocalTick3.doneVm first g entryQ _ _ y)⟩ :
      State GalilVM)
  have habs : PalPeg.LocalReplayParked.abs''
        (PalPeg.LocalTick3.doneVm first g entryQ (PalPeg.ProgramFunction.fppRunFun entryQ
          ⟨⟨y.fppPc, PalPeg.LocalBuffers.abs y.fppBuf⟩, y.fppDone⟩).config.pc
          {y.ctl with mode := PalPeg.GalilScaffoldController.Mode.markEnd} y)
      = { PalPeg.LocalReplayParked.abs'' y with
          fpp := PalPeg.ProgramFunction.fppDoneFun entryQ first
            (PalPeg.LocalReplayParked.abs'' y).fpp } := by
    show { PalPeg.LocalArrival.abs' (PalPeg.LocalTick3.doneVm first g entryQ _ _ y) with
        right := PalPeg.LocalReplayParked.absR y } = _
    rw [PalPeg.LocalTick3.abs'_doneVm]
    show _ = { PalPeg.LocalReplayParked.abs'' y with
      fpp := { (PalPeg.LocalArrival.abs' y).fpp with
        program := PalPeg.GalilScaffoldChainInputSupply.markNew
          (PalPeg.ProgramFunction.fppRunFun entryQ
            ⟨⟨y.fppPc, PalPeg.LocalBuffers.abs y.fppBuf⟩, y.fppDone⟩) first } }
    rw [hprog]
    rfl
  rw [habs]
  rfl

/-- **the tick that leaves the shift.**  No tape and no cursor moves: the controller goes back
to scanning and refreshes its output bit, both readings of the state it already has. -/
theorem vml_shift_exit {P : ℕ} (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (y : PalPeg.LocalState.GalilVML P)
    (hmode : y.ctl.mode = PalPeg.GalilScaffoldController.Mode.shift)
    (hrem : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).remainingPos
      (PalPeg.LocalReplayParked.abs'' y) = false) :
    PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay
        (PalPeg.LocalReplayParked.absState'' y)
      = PalPeg.LocalReplayParked.absState''
          {y with ctl := {y.ctl with mode := PalPeg.GalilScaffoldController.Mode.scan, output := PalPeg.GalilScaffoldTop.refreshFun (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) (PalPeg.LocalReplayParked.abs'' y) y.ctl.output}} := by
  have hstate : PalPeg.LocalReplayParked.absState'' y
      = (⟨y.ctl, PalPeg.LocalReplayParked.abs'' y⟩ : State GalilVM) := rfl
  rw [hstate]
  simp only [PalPeg.GalilScaffoldTop.tickFun, hmode]
  rw [if_neg (by simp [hrem])]
  rfl

/-- **one shift tick.**  The centre and left heads walk right (the left one twice), the bank
takes its four ops and the chain's watch advances — the multi-component step at its widest.  The
side conditions are the local layer's own (`Inv`, `ShiftCounters`, and that each head really has
a cell to walk onto). -/
theorem vml_shift_one {P : ℕ} (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (y : PalPeg.LocalState.GalilVML P) (wv : PalPeg.GalilScaffoldChainWatch.State)
    (hmode : y.ctl.mode = PalPeg.GalilScaffoldController.Mode.shift)
    (hrem : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).remainingPos
      (PalPeg.LocalReplayParked.abs'' y) = true)
    (hchain : y.chain = PalPeg.GalilScaffoldChainInputSupply.ChainVM.watch wv)
    (hinv : PalPeg.LocalTick1.Inv y) (hcnt : PalPeg.LocalTick3.ShiftCounters y)
    (haC : PalPeg.LocalArrival.Ahead y.center y.pending)
    (haL : PalPeg.LocalArrival.Ahead y.left y.pending)
    (haL' : PalPeg.LocalArrival.Ahead (PalPeg.LocalInputView.moveRight y.left) y.pending)
    (hcC : PalPeg.GalilScaffoldChainVerifier.canRight (PalPeg.LocalArrival.abs' y).center)
    (hcL : PalPeg.GalilScaffoldChainVerifier.canRight (PalPeg.LocalArrival.abs' y).left)
    (hcL' : PalPeg.GalilScaffoldChainVerifier.canRight
      (PalPeg.GalilScaffoldChainVerifier.right (PalPeg.LocalArrival.abs' y).left)) :
    PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay
        (PalPeg.LocalReplayParked.absState'' y)
      = PalPeg.LocalReplayParked.absState'' (PalPeg.LocalTick3.shiftVm wv y) := by
  have hstate : PalPeg.LocalReplayParked.absState'' y
      = (⟨y.ctl, PalPeg.LocalReplayParked.abs'' y⟩ : State GalilVM) := rfl
  rw [hstate]
  simp only [PalPeg.GalilScaffoldTop.tickFun, hmode]
  rw [if_pos hrem]
  show _ = (⟨y.ctl, PalPeg.LocalReplayParked.abs''
    (PalPeg.LocalTick3.shiftVm wv y)⟩ : State GalilVM)
  have hframe : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).shiftOne
        (PalPeg.LocalReplayParked.abs'' y)
      = PalPeg.GalilScaffoldChainInputSupply.shiftLens.set (PalPeg.LocalReplayParked.abs'' y)
          ⟨PalPeg.GalilScaffoldChainInputSupply.shiftTick
              ⟨(PalPeg.LocalArrival.abs' y).center, (PalPeg.LocalArrival.abs' y).left,
                (PalPeg.LocalArrival.abs' y).remaining, (PalPeg.LocalArrival.abs' y).radius,
                (PalPeg.LocalArrival.abs' y).length⟩,
            .watch (PalPeg.GalilScaffoldChainInputSupply.chainShiftOne wv),
            PalPeg.GalilScaffoldCounter.inc (PalPeg.GalilScaffoldCounter.inc
              (PalPeg.LocalArrival.abs' y).cycle)⟩ := by
    show PalPeg.GalilScaffoldChainInputSupply.shiftLens.set (PalPeg.LocalReplayParked.abs'' y)
        (PalPeg.FrameFunction.shiftOneFun
          (PalPeg.GalilScaffoldChainInputSupply.shiftLens.get
            (PalPeg.LocalReplayParked.abs'' y))) = _
    unfold PalPeg.FrameFunction.shiftOneFun
    rw [show (PalPeg.GalilScaffoldChainInputSupply.shiftLens.get
      (PalPeg.LocalReplayParked.abs'' y)).chain
        = PalPeg.GalilScaffoldChainInputSupply.ChainVM.watch wv from hchain]
    rfl
  rw [hframe]
  congr 1
  show _ = { PalPeg.LocalArrival.abs' (PalPeg.LocalTick3.shiftVm wv y) with
      right := PalPeg.LocalReplayParked.absR (PalPeg.LocalTick3.shiftVm wv y) }
  rw [PalPeg.LocalTick3.abs'_shiftVm hinv hcnt wv haC haL haL' hcC hcL hcL',
    absR_congr (z := PalPeg.LocalTick3.shiftVm wv y) (y := y) rfl
      ((rval_bankTick (y := PalPeg.LocalTick3.shiftMid wv y) (hinj := hinv.roles)
          (f := PalPeg.LocalTick3.shiftOps2) rfl).trans
        (rval_bankTick (y := y) (hinj := hinv.roles)
          (f := PalPeg.LocalTick3.shiftOps1) rfl)) rfl]
  rfl

/-! ### the rule: one action on one slot

Every branch proved above moves at most one slot, by at most one action.  `actsAt` is that
shape as a rule's action table, and `idealStep_oneAct` says what the ideal step then does: the
named slot takes the action, every other slot stands still.  These are the two halves the
branch lemmas above ask for as `hmoved` and `hkept`. -/

/-- the action table of a rule that touches one slot. -/
def actsAt {Γ : Type} {t : ℕ} (i : Fin t) (l : List (PalPeg.CloseoutCoreEnc12.Act Γ)) :
    Fin t → List (PalPeg.CloseoutCoreEnc12.Act Γ) :=
  fun j => if j = i then l else []

theorem actsAt_length {Γ : Type} {t K : ℕ} (i : Fin t) (l : List (PalPeg.CloseoutCoreEnc12.Act Γ))
    (hl : l.length ≤ K) (j : Fin t) : (actsAt i l j).length ≤ K := by
  unfold actsAt
  by_cases hj : j = i
  · rw [if_pos hj]; exact hl
  · rw [if_neg hj]; exact Nat.zero_le K

/-- **the ideal step of a one-slot rule.**  The named slot takes the action list; every other
slot is returned untouched. -/
theorem idealStep_oneAct {Q Γ : Type} {t K : ℕ}
    (R : PalPeg.CloseoutCoreEnc12.ActRule (Fin 2) Q Γ t K) (blank : Γ)
    (q : Q) (tapes : Fin t → STape Γ) (i : Fin t) (l : List (PalPeg.CloseoutCoreEnc12.Act Γ))
    (hacts : R.acts q none (fun tape => PalPeg.Local.readWin blank K (tapes tape)) = actsAt i l) :
    (PalPeg.LocalStepFusion.idealStep R blank (q, tapes) none).2 i
        = PalPeg.CloseoutCoreEnc12.actList blank (tapes i) l
      ∧ ∀ j, j ≠ i → (PalPeg.LocalStepFusion.idealStep R blank (q, tapes) none).2 j = tapes j := by
  refine ⟨?_, ?_⟩
  · show PalPeg.CloseoutCoreEnc12.actList blank (tapes i)
      (R.acts q none (fun tape => PalPeg.Local.readWin blank K (tapes tape)) i) = _
    rw [hacts]
    show PalPeg.CloseoutCoreEnc12.actList blank (tapes i) (if i = i then l else []) = _
    rw [if_pos rfl]
  · intro j hj
    show PalPeg.CloseoutCoreEnc12.actList blank (tapes j)
      (R.acts q none (fun tape => PalPeg.Local.readWin blank K (tapes tape)) j) = _
    rw [hacts]
    show PalPeg.CloseoutCoreEnc12.actList blank (tapes j) (if j = i then l else []) = _
    rw [if_neg hj]
    rfl

/-! ### the slots as the machine's tape indices

The encoding names a component's tape by a `Slot`; a rule names it by a `Fin t`.  The two are
the same finite set, so one equivalence carries the one-slot lemma across. -/

theorem card_slot : Fintype.card Slot = tapeCountM := by decide

/-- the machine's tape index of a slot. -/
noncomputable def slotIndex : Slot ≃ Fin tapeCountM :=
  (Fintype.equivFin Slot).trans (finCongr card_slot)

/-- the tapes of the encoding, as the machine holds them. -/
noncomputable def tapesOf (T : Slot → STape Γm) : Fin tapeCountM → STape Γm :=
  fun j => T (slotIndex.symm j)

@[simp] theorem tapesOf_apply (T : Slot → STape Γm) (i : Slot) :
    tapesOf T (slotIndex i) = T i := by
  unfold tapesOf
  rw [Equiv.symm_apply_apply]

/-- **the ideal step of a one-slot rule, read back through the slots.** -/
theorem idealStep_oneSlot {Q : Type} {K : ℕ}
    (R : PalPeg.CloseoutCoreEnc12.ActRule (Fin 2) Q Γm tapeCountM K) (q : Q)
    (T : Slot → STape Γm) (i : Slot) (l : List (PalPeg.CloseoutCoreEnc12.Act Γm))
    (hacts : R.acts q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = actsAt (slotIndex i) l) :
    (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2 (slotIndex i)
        = PalPeg.CloseoutCoreEnc12.actList blankM (T i) l
      ∧ ∀ j : Slot, j ≠ i →
        (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2 (slotIndex j) = T j := by
  obtain ⟨hmoved, hkept⟩ := idealStep_oneAct R blankM q (tapesOf T) (slotIndex i) l hacts
  refine ⟨?_, ?_⟩
  · rw [hmoved, tapesOf_apply]
  · intro j hj
    rw [hkept (slotIndex j) (fun h => hj (slotIndex.injective h)), tapesOf_apply]

/-! ### rules that touch two slots

Some branches move a program tape and a bank counter in the same tick.  The general fact is that
the ideal step applies each slot's own action list and nothing else; `actsAtPair` is the table
for two named slots, and `idealStep_pair` reads it back. -/

/-- **the ideal step, slot by slot.**  Nothing more than the definition, but it is the statement
every branch needs: each slot gets its own list and no slot gets anything else. -/
theorem idealStep_tapes {Q Γ : Type} {t K : ℕ}
    (R : PalPeg.CloseoutCoreEnc12.ActRule (Fin 2) Q Γ t K) (blank : Γ)
    (q : Q) (tapes : Fin t → STape Γ) (j : Fin t) :
    (PalPeg.LocalStepFusion.idealStep R blank (q, tapes) none).2 j
      = PalPeg.CloseoutCoreEnc12.actList blank (tapes j)
          (R.acts q none (fun tape => PalPeg.Local.readWin blank K (tapes tape)) j) := rfl

/-- the action table of a rule that touches two slots. -/
def actsAtPair {Γ : Type} {t : ℕ} (i i' : Fin t)
    (l l' : List (PalPeg.CloseoutCoreEnc12.Act Γ)) :
    Fin t → List (PalPeg.CloseoutCoreEnc12.Act Γ) :=
  fun j => if j = i then l else if j = i' then l' else []

theorem actsAtPair_length {Γ : Type} {t K : ℕ} (i i' : Fin t)
    (l l' : List (PalPeg.CloseoutCoreEnc12.Act Γ)) (hl : l.length ≤ K) (hl' : l'.length ≤ K)
    (j : Fin t) : (actsAtPair i i' l l' j).length ≤ K := by
  unfold actsAtPair
  by_cases hj : j = i
  · rw [if_pos hj]; exact hl
  · rw [if_neg hj]
    by_cases hj' : j = i'
    · rw [if_pos hj']; exact hl'
    · rw [if_neg hj']; exact Nat.zero_le K

/-- **the ideal step of a two-slot rule, read back through the slots.** -/
theorem idealStep_pair {Q : Type} {K : ℕ}
    (R : PalPeg.CloseoutCoreEnc12.ActRule (Fin 2) Q Γm tapeCountM K) (q : Q)
    (T : Slot → STape Γm) (i i' : Slot) (hne : i' ≠ i)
    (l l' : List (PalPeg.CloseoutCoreEnc12.Act Γm))
    (hacts : R.acts q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = actsAtPair (slotIndex i) (slotIndex i') l l') :
    (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2 (slotIndex i)
        = PalPeg.CloseoutCoreEnc12.actList blankM (T i) l
      ∧ (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2 (slotIndex i')
        = PalPeg.CloseoutCoreEnc12.actList blankM (T i') l'
      ∧ ∀ j : Slot, j ≠ i → j ≠ i' →
        (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2 (slotIndex j) = T j := by
  refine ⟨?_, ?_, ?_⟩
  · rw [idealStep_tapes, hacts, tapesOf_apply]
    show PalPeg.CloseoutCoreEnc12.actList blankM (T i)
      (if slotIndex i = slotIndex i then l else _) = _
    rw [if_pos rfl]
  · rw [idealStep_tapes, hacts, tapesOf_apply]
    show PalPeg.CloseoutCoreEnc12.actList blankM (T i')
      (if slotIndex i' = slotIndex i then l else if slotIndex i' = slotIndex i' then l' else []) = _
    rw [if_neg (fun h => hne (slotIndex.injective h)), if_pos rfl]
  · intro j hj hj'
    rw [idealStep_tapes, hacts, tapesOf_apply]
    show PalPeg.CloseoutCoreEnc12.actList blankM (T j)
      (if slotIndex j = slotIndex i then l else if slotIndex j = slotIndex i' then l' else []) = _
    rw [if_neg (fun h => hj (slotIndex.injective h)),
      if_neg (fun h => hj' (slotIndex.injective h))]
    rfl

/-! ### carrying the idle half's blankness

`rewind_fppReset` asks that the half becoming live is already blank.  Every other branch proved
so far names an action only on the live half, so it leaves that blankness alone — which is what
lets the condition be carried along a run rather than assumed at each tick. -/

theorem progSlotOf_ne_of_live {l l' : Bool} (h : l ≠ l') (i j : Fin 9) :
    progSlotOf l i ≠ progSlotOf l' j := by
  cases l <;> cases l' <;> simp_all [progSlotOf]

theorem dpSlotOf_ne_of_live {l l' : Bool} (h : l ≠ l') (i j : Fin 12) :
    dpSlotOf l i ≠ dpSlotOf l' j := by
  cases l <;> cases l' <;> simp_all [dpSlotOf]

/-- **a step that names one slot of the live half leaves the idle half blank.**  The two halves
are distinct slots, so the rule that moves one cannot reach the other. -/
theorem idle_blank_of_oneSlot {fppBound dpBound : ℕ} (margin : ℕ) (q : QPhys fppBound dpBound)
    (T newT : Slot → STape Γm) (i : Fin 9)
    (hkept : ∀ slot, slot ≠ progSlotOf q.fppLive i → newT slot = T slot)
    (hidle : ∀ j : Fin 9, T (progSlotOf (!q.fppLive) j)
      = padLeft margin (mapTape encProg (encTape PalPeg.GalilScaffoldTape.reset))) :
    ∀ j : Fin 9, newT (progSlotOf (!q.fppLive) j)
      = padLeft margin (mapTape encProg (encTape PalPeg.GalilScaffoldTape.reset)) := by
  intro j
  rw [hkept _ (progSlotOf_ne_of_live (by cases q.fppLive <;> simp) j i), hidle j]

/-- and after the flip the roles swap: the half that was live becomes the one the erasure must
blank, and the half that was idle is the one the encoding now speaks about. -/
theorem idle_blank_after_flip {fppBound dpBound : ℕ} (margin : ℕ) (q : QPhys fppBound dpBound)
    (T : Slot → STape Γm)
    (hidle : ∀ j : Fin 9, T (progSlotOf (!q.fppLive) j)
      = padLeft margin (mapTape encProg (encTape PalPeg.GalilScaffoldTape.reset))) :
    ∀ j : Fin 9, T (progSlotOf ({q with fppLive := !q.fppLive} : QPhys fppBound dpBound).fppLive j)
      = padLeft margin (mapTape encProg (encTape PalPeg.GalilScaffoldTape.reset)) := hidle

/-! ### the background erasure

The half retired by a wipe holds whatever the program left on it, and it must be blank again by
the next wipe.  The machine erases it in the background: every tick, one cell of each of the nine
idle tapes, walking left until the floor sentinel is under the head.  Nine slots at once costs
nothing, because a rule names each slot's actions separately. -/

/-- the erasure's action on one slot: blank the cell and step left, unless the cell below is the
floor, in which case the tape is already back at its own left edge. -/
noncomputable def eraseAct {K : ℕ} (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (j : Fin tapeCountM) : List (PalPeg.CloseoutCoreEnc12.Act Γm) :=
  if ws j ⟨K - 1, by omega⟩ = bottomM then []
  else [some (blankM, (.left : PalPeg.CloseoutCoreEnc12.MoveC))]

/-- the erasure's whole table: the idle half's nine slots, and nothing else. -/
noncomputable def eraseOf {K : ℕ} (live : Bool)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (j : Fin tapeCountM) :
    List (PalPeg.CloseoutCoreEnc12.Act Γm) :=
  if ∃ i : Fin 9, j = slotIndex (progSlotOf (!live) i) then eraseAct ws j else []

theorem eraseOf_length {K : ℕ} (hK : 1 ≤ K) (live : Bool)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (j : Fin tapeCountM) :
    (eraseOf live ws j).length ≤ K := by
  unfold eraseOf eraseAct
  split
  · split
    · simp
    · simpa using hK
  · simp

/-- **the erasure never touches the live half.**  Its table is empty on every slot that is not
one of the idle half's nine, so it composes with any branch's own actions. -/
theorem eraseOf_live {K : ℕ} (live : Bool) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (i : Fin 9) : eraseOf live ws (slotIndex (progSlotOf live i)) = [] := by
  unfold eraseOf
  rw [if_neg]
  rintro ⟨k, hk⟩
  exact progSlotOf_ne_of_live (by cases live <;> simp) i k (slotIndex.injective hk)

/-- and it is empty on every slot outside the two program halves. -/
theorem eraseOf_other {K : ℕ} (live : Bool) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (slot : Slot) (h : ∀ i : Fin 9, slot ≠ progSlotOf (!live) i) :
    eraseOf live ws (slotIndex slot) = [] := by
  unfold eraseOf
  rw [if_neg]
  rintro ⟨k, hk⟩
  exact h k (slotIndex.injective hk)

/-- **a branch's actions together with the erasure.**  The two never name the same slot, so the
composition is just the branch's own table on the live half and elsewhere, and the erasure's on
the idle half. -/
noncomputable def withErase {K : ℕ} (live : Bool)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (base : Fin tapeCountM → List (PalPeg.CloseoutCoreEnc12.Act Γm)) :
    Fin tapeCountM → List (PalPeg.CloseoutCoreEnc12.Act Γm) :=
  fun j => base j ++ eraseOf live ws j

/-- two actions in a tick is all it costs: the branch's own, and one cell of one idle tape. -/
theorem withErase_length {K b : ℕ} (hK : b + 1 ≤ K) (live : Bool)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (base : Fin tapeCountM → List (PalPeg.CloseoutCoreEnc12.Act Γm))
    (hbase : ∀ j, (base j).length ≤ b) (j : Fin tapeCountM) :
    (withErase live ws base j).length ≤ K := by
  have herase : (eraseOf live ws j).length ≤ 1 := by
    unfold eraseOf eraseAct
    split
    · split
      · simp
      · simp
    · simp
  have := hbase j
  unfold withErase
  rw [List.length_append]
  omega

theorem withErase_at_live {K : ℕ} (live : Bool)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (base : Fin tapeCountM → List (PalPeg.CloseoutCoreEnc12.Act Γm)) (i : Fin 9) :
    withErase live ws base (slotIndex (progSlotOf live i))
      = base (slotIndex (progSlotOf live i)) := by
  unfold withErase
  rw [eraseOf_live, List.append_nil]

theorem withErase_at_other {K : ℕ} (live : Bool)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (base : Fin tapeCountM → List (PalPeg.CloseoutCoreEnc12.Act Γm)) (slot : Slot)
    (h : ∀ i : Fin 9, slot ≠ progSlotOf (!live) i) :
    withErase live ws base (slotIndex slot) = base (slotIndex slot) := by
  unfold withErase
  rw [eraseOf_other live ws slot h, List.append_nil]

/-- naming actions at one slot of the live half names none anywhere else on it. -/
theorem actsAt_off_live (live : Bool) (i : Fin 9)
    (l : List (PalPeg.CloseoutCoreEnc12.Act Γm)) (slot : Slot)
    (hslot : ∀ j : Fin 9, slot ≠ progSlotOf live j) :
    actsAt (slotIndex (progSlotOf live i)) l (slotIndex slot) = [] := by
  show (if slotIndex slot = slotIndex (progSlotOf live i) then l else []) = []
  exact if_neg (fun h => hslot i (slotIndex.injective h))

/-- **the ideal step of a branch that also erases.**  Away from the retired half — which is the
only place the erasure writes — every slot gets exactly the branch's own action list, whichever
slot it is.  A branch that names actions on a counter or a cursor is served by this as much as
one that names them on a program tape. -/
theorem idealStep_withErase {Q : Type} {K : ℕ}
    (R : PalPeg.CloseoutCoreEnc12.ActRule (Fin 2) Q Γm tapeCountM K) (q : Q)
    (T : Slot → STape Γm) (live : Bool)
    (base : Fin tapeCountM → List (PalPeg.CloseoutCoreEnc12.Act Γm))
    (hacts : R.acts q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = withErase live (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) base)
    (slot : Slot) (hidle : ∀ k : Fin 9, slot ≠ progSlotOf (!live) k) :
    (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2 (slotIndex slot)
      = PalPeg.CloseoutCoreEnc12.actList blankM (T slot) (base (slotIndex slot)) := by
  rw [idealStep_tapes, hacts, withErase_at_other live _ _ slot hidle, tapesOf_apply]

/-- **a branch whose actions live on the live half leaves every other slot alone.**  The shape
every branch but the fallback copy has: outside the live half the action list is empty, and an
empty action list is the identity on a tape. -/
theorem idealStep_offBase {Q : Type} {K : ℕ}
    (R : PalPeg.CloseoutCoreEnc12.ActRule (Fin 2) Q Γm tapeCountM K) (q : Q)
    (T : Slot → STape Γm) (live : Bool)
    (base : Fin tapeCountM → List (PalPeg.CloseoutCoreEnc12.Act Γm))
    (hacts : R.acts q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = withErase live (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) base)
    (hbase : ∀ slot : Slot, (∀ j : Fin 9, slot ≠ progSlotOf live j) →
      base (slotIndex slot) = []) :
    (∀ i : Fin 9, (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2
        (slotIndex (progSlotOf live i))
        = PalPeg.CloseoutCoreEnc12.actList blankM (T (progSlotOf live i))
            (base (slotIndex (progSlotOf live i))))
      ∧ ∀ slot : Slot, (∀ j : Fin 9, slot ≠ progSlotOf live j) →
        (∀ k : Fin 9, slot ≠ progSlotOf (!live) k) →
        (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2 (slotIndex slot)
          = T slot := by
  refine ⟨fun i => ?_, ?_⟩
  · exact idealStep_withErase R q T live base hacts (progSlotOf live i)
      (fun k => progSlotOf_ne_flip live i k)
  · intro slot hs hidle
    rw [idealStep_withErase R q T live base hacts slot hidle, hbase slot hs]
    rfl

/-- **the case of a branch that names actions on a single slot of the live half.**  Every branch
but the one that runs the preparation program is of this shape: the other eight live slots get the
empty list, which leaves their tapes where they were. -/
theorem idealStep_atLiveSlot {Q : Type} {K : ℕ}
    (R : PalPeg.CloseoutCoreEnc12.ActRule (Fin 2) Q Γm tapeCountM K) (q : Q)
    (T : Slot → STape Γm) (live : Bool) (i : Fin 9)
    (l : List (PalPeg.CloseoutCoreEnc12.Act Γm))
    (hacts : R.acts q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = withErase live (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (actsAt (slotIndex (progSlotOf live i)) l)) :
    (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2
        (slotIndex (progSlotOf live i))
        = PalPeg.CloseoutCoreEnc12.actList blankM (T (progSlotOf live i)) l
      ∧ ∀ slot : Slot, slot ≠ progSlotOf live i →
        (∀ k : Fin 9, slot ≠ progSlotOf (!live) k) →
        (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2 (slotIndex slot)
          = T slot := by
  obtain ⟨hmoved, hkept⟩ :=
    idealStep_offBase R q T live _ hacts (actsAt_off_live live i l)
  refine ⟨?_, ?_⟩
  · have hi := hmoved i
    rwa [show actsAt (slotIndex (progSlotOf live i)) l (slotIndex (progSlotOf live i)) = l from
      if_pos rfl] at hi
  · intro slot hs hidle
    by_cases hlive : ∃ j : Fin 9, slot = progSlotOf live j
    · obtain ⟨j, hj⟩ := hlive
      subst hj
      have hjj := hmoved j
      rw [show actsAt (slotIndex (progSlotOf live i)) l (slotIndex (progSlotOf live j)) = [] from by
        show (if slotIndex (progSlotOf live j) = slotIndex (progSlotOf live i) then l else []) = []
        exact if_neg (fun h => hs (slotIndex.injective h))] at hjj
      exact hjj
    · exact hkept slot (fun j hj => hlive ⟨j, hj⟩) hidle

/-- **the erasure keeps the shape it needs.**  Blanking a cell and stepping left sends a padded
tape to a padded tape: the blank the machine writes is the component alphabet's own blank, so the
result is still in the image of the encoding, and the step left cannot reach the floor because
the rule only takes it while the cell below is not the sentinel. -/
theorem erase_preserves_shape (margin K : ℕ) (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (raw : STape (Fin 9))
    (hbelow : PalPeg.Local.readWin blankM K (padLeft margin (mapTape encProg raw))
      ⟨K - 1, by omega⟩ ≠ bottomM) :
    PalPeg.CloseoutCoreEnc12.actList blankM (padLeft margin (mapTape encProg raw))
        [some (blankM, (.left : PalPeg.CloseoutCoreEnc12.MoveC))]
      = padLeft margin (mapTape encProg
          (STape.applyAction (6 : Fin 9) raw ((6 : Fin 9), .left))) := by
  have hleft : raw.left ≠ [] := by
    intro hnil
    apply hbelow
    rw [window_below margin K (mapTape encProg raw) hK1 hKn]
    show ((mapTape encProg raw).left).headD bottomM = bottomM
    show (raw.left.map encProg).headD bottomM = bottomM
    rw [hnil]
    rfl
  have hmapped : (mapTape encProg raw).left ≠ [] := by
    intro hnil
    apply hleft
    have : raw.left.map encProg = [] := hnil
    exact List.map_eq_nil_iff.mp this
  rw [mapTape_applyAction encProg (if_pos rfl) raw (6 : Fin 9) .left,
    padLeft_applyAction_left margin (mapTape encProg raw) (encProg 6) hmapped]
  rfl

/-- a branch that names no action off the live half names none on the retired half either. -/
theorem offLive_offIdle {live : Bool}
    {base : Fin tapeCountM → List (PalPeg.CloseoutCoreEnc12.Act Γm)}
    (h : ∀ slot : Slot, (∀ j : Fin 9, slot ≠ progSlotOf live j) → base (slotIndex slot) = [])
    (k : Fin 9) : base (slotIndex (progSlotOf (!live) k)) = [] :=
  h (progSlotOf (!live) k) (fun j => (progSlotOf_ne_flip live j k).symm)

/-- **the idle half's shape survives the tick.**  At each of its nine slots the rule's table is
the erasure's alone — the branch names nothing there — and the erasure either stops, or blanks a
cell and steps left, which `erase_preserves_shape` shows keeps the padding. -/
theorem idle_shape_after_erase {Q : Type} {K : ℕ} (margin : ℕ) (hK1 : 1 ≤ K)
    (hKn : K ≤ margin + 1)
    (R : PalPeg.CloseoutCoreEnc12.ActRule (Fin 2) Q Γm tapeCountM K) (q : Q)
    (T : Slot → STape Γm) (live : Bool)
    (base : Fin tapeCountM → List (PalPeg.CloseoutCoreEnc12.Act Γm))
    (hacts : R.acts q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = withErase live (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) base)
    (hbase : ∀ k : Fin 9, base (slotIndex (progSlotOf (!live) k)) = [])
    (hshape : ∀ k : Fin 9, ∃ raw : STape (Fin 9),
      T (progSlotOf (!live) k) = padLeft margin (mapTape encProg raw)) (k : Fin 9) :
    ∃ raw : STape (Fin 9),
      (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2
        (slotIndex (progSlotOf (!live) k)) = padLeft margin (mapTape encProg raw) := by
  obtain ⟨raw, hraw⟩ := hshape k
  have htable : R.acts q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (slotIndex (progSlotOf (!live) k))
      = eraseAct (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (slotIndex (progSlotOf (!live) k)) := by
    rw [hacts]
    show base (slotIndex (progSlotOf (!live) k))
      ++ eraseOf live _ (slotIndex (progSlotOf (!live) k)) = _
    rw [hbase k]
    show [] ++ eraseOf live _ (slotIndex (progSlotOf (!live) k)) = _
    rw [List.nil_append]
    unfold eraseOf
    rw [if_pos ⟨k, rfl⟩]
  rw [idealStep_tapes, htable, tapesOf_apply, hraw]
  unfold eraseAct
  by_cases hstop : PalPeg.Local.readWin blankM K (tapesOf T (slotIndex (progSlotOf (!live) k)))
      ⟨K - 1, by omega⟩ = bottomM
  · rw [if_pos hstop]
    exact ⟨raw, rfl⟩
  · rw [if_neg hstop]
    refine ⟨STape.applyAction (6 : Fin 9) raw ((6 : Fin 9), .left), ?_⟩
    rw [tapesOf_apply, hraw] at hstop
    exact erase_preserves_shape margin K hK1 hKn raw hstop

/-- **a tick in which only the idle half moved.**  The branches that name no action at all — the
three that stop at a floor, the start of the program, the wipe — still see the background erasure
write on the retired half.  Everything the encoding speaks about is untouched, and the retired
half keeps its shape, so the encoding moves across unchanged. -/
theorem encTapes_idleOnly (margin : ℕ) (x : State GalilVM) (polarity : Fin 16 → Bool)
    (gap : Fin 4 → Bool) (micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl)
    (fppLive dpLive : Bool) (tapes newTapes : Slot → STape Γm)
    (henc : EncTapes margin x polarity gap micro fppLive dpLive tapes)
    (hkept : ∀ slot, (∀ k : Fin 9, slot ≠ progSlotOf (!fppLive) k) → newTapes slot = tapes slot)
    (hidleShape : ∀ k : Fin 9, ∃ raw : STape (Fin 9),
      newTapes (progSlotOf (!fppLive) k) = padLeft margin (mapTape encProg raw)) :
    EncTapes margin x polarity gap micro fppLive dpLive newTapes where
  margins := by
    intro slot
    by_cases hidle : ∃ k : Fin 9, slot = progSlotOf (!fppLive) k
    · obtain ⟨k, hk⟩ := hidle
      obtain ⟨raw, hraw⟩ := hidleShape k
      rw [hk, hraw, pos_padLeft]
      omega
    · rw [hkept slot (fun k hk => hidle ⟨k, hk⟩)]
      exact henc.margins slot
  heads := by
    intro v head hhead
    obtain ⟨view, viewTapes, habs, hrep, hslots, hcells, hwf⟩ := henc.heads v head hhead
    exact ⟨view, viewTapes, habs, hrep, fun j => by
      rw [hkept _ (by intro k; cases fppLive <;> simp [progSlotOf]), hslots j], hcells, hwf⟩
  idleHead := by
    intro h3
    obtain ⟨view, viewTapes, hrep, hslots, hcells, hwf⟩ := henc.idleHead h3
    exact ⟨view, viewTapes, hrep, fun j => by
      rw [hkept _ (by intro k; cases fppLive <;> simp [progSlotOf]), hslots j], hcells, hwf⟩
  fpp := by
    intro j
    rw [hkept _ (by intro k; cases fppLive <;> simp [progSlotOf])]
    exact henc.fpp j
  idleShape := hidleShape
  dp := by
    intro j
    rw [hkept _ (by intro k; cases fppLive <;> cases dpLive <;> simp [progSlotOf, dpSlotOf])]
    exact henc.dp j
  counters := by
    intro c value hvalue
    obtain ⟨segments, habs, hslot⟩ := henc.counters c value hvalue
    exact ⟨segments, habs, by
      rw [hkept _ (by intro k; cases fppLive <;> simp [progSlotOf]), hslot]⟩
  mirrors := by
    intro m value hvalue
    obtain ⟨segments, habs, hslot⟩ := henc.mirrors m value hvalue
    exact ⟨segments, habs, by
      rw [hkept _ (by intro k; cases fppLive <;> simp [progSlotOf]), hslot]⟩
  places := by
    intro j place hplace
    obtain ⟨stackTape, junk, hsealed, hlen, hstack, hslot⟩ := henc.places j place hplace
    exact ⟨stackTape, junk, hsealed, hlen, hstack, by
      rw [hkept _ (by intro k; cases fppLive <;> simp [progSlotOf]), hslot]⟩
  period := by
    intro tape htape
    rw [hkept _ (by intro k; cases fppLive <;> simp [progSlotOf])]
    exact henc.period tape htape
  answer := by
    intro tape htape
    rw [hkept _ (by intro k; cases fppLive <;> simp [progSlotOf])]
    exact henc.answer tape htape

/-! ### the first branch of the rule: the mark walk

The machine decides this branch from one reading — the symbol under the head of the marks tape
— and performs one action on that same tape.  Both halves are readings of the window, so the
rule is a function of what the machine can see. -/

/-- the symbol under the head of a slot, as the rule reads it from the window. -/
noncomputable def centreRead {K : ℕ} (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (i : Slot) : Γm :=
  ws (slotIndex i) ⟨K, by omega⟩

theorem centreRead_of_margin {K : ℕ} (T : Slot → STape Γm) (i : Slot)
    (hm : K ≤ PalPeg.Local.pos (T i)) :
    centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) i = (T i).focus := by
  show PalPeg.Local.readWin blankM K (tapesOf T (slotIndex i)) ⟨K, by omega⟩ = _
  rw [tapesOf_apply]
  exact window_centre K (T i) hm

/-- **a cursor is exhausted exactly when the centre of its window is blank.**  The abstract
test `(read place).isNone` asks whether the cursor's letters have run out; physically the
cursor's remaining letters sit on its tape with the top of the stack under the head, padded
below by sealed junk, so the test is one reading of the window's centre cell. -/
theorem placeRead_isNone_iff_centre {margin K : ℕ} {x : State GalilVM} {polarity : Fin 16 → Bool}
    {gap : Fin 4 → Bool} {micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl}
    {fppLive dpLive : Bool} {T : Slot → STape Γm}
    (henc : EncTapes margin x polarity gap micro fppLive dpLive T) (hK : K ≤ margin)
    (i : Fin 3) (place : PalPeg.GalilScaffoldPlace.Place) (hplace : placeOf x i = some place) :
    (PalPeg.GalilScaffoldPlace.read place).isNone = true
      ↔ centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) (placeSlot i)
          = blankM := by
  obtain ⟨stackTape, junk, hsealed, _, hstack, htape⟩ := henc.places i place hplace
  have hcentre :
      centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) (placeSlot i)
        = encCell stackTape.focus := by
    rw [centreRead_of_margin T (placeSlot i) (margin_le_pos henc hK _)]
    show (T (placeSlot i)).focus = encCell stackTape.focus
    rw [show T (placeSlot i) = padLeft margin (mapTape encCell stackTape) from htape]
    rfl
  rw [hcentre, stackTape_focus stackTape _ hstack, placeRead_isNone_iff_head place junk hsealed]
  cases hhead : (place.letters.map (fun letter => some letter) ++ junk).head? with
  | none => simp [encCell, PalPeg.CloseoutCoreStep.blankc]
  | some cell =>
    cases cell with
    | none =>
      simp [encCell, PalPeg.CloseoutCoreEnc.cellSym, PalPeg.CloseoutCoreStep.blankc,
        PalPeg.GalilVMEncode.blank]
    | some a =>
      have hletter : PalPeg.CloseoutCoreEnc.cellSym (some a) ≠ PalPeg.CloseoutCoreStep.blankc := by
        simp [PalPeg.CloseoutCoreEnc.cellSym, PalPeg.CloseoutCoreStep.blankc,
          PalPeg.GalilVMEncode.blank, PalPeg.GalilVMEncode.sOpt]
      simp [encCell, hletter, blankM]

/-- the symbol one cell below the head of a slot, as the rule reads it from the window. -/
noncomputable def belowRead {K : ℕ} (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (i : Slot) : Γm :=
  ws (slotIndex i) ⟨K - 1, by omega⟩

/-- **one decrement of a counter, on its tape.**  A counter tape holds the absolute value and
the finite control holds the sign, so a decrement is a pop while the value is positive and a push
otherwise — and the sign bit that comes out is exactly the bit that chose between them.  At zero
on the positive side the push is what crosses into the negative numbers. -/
theorem absCtr_dec (t : STape Seg) (b : Bool) :
    absCtr
        (if b && decide (PalPeg.LocalCounter.val t ≠ 0) then PalPeg.LocalCounter.pop t
          else PalPeg.LocalCounter.push t)
        (b && decide (PalPeg.LocalCounter.val t ≠ 0))
      = PalPeg.GalilScaffoldCounter.dec (absCtr t b) := by
  cases b
  · simp [absCtr, PalPeg.LocalCounter.negOfNat, PalPeg.GalilScaffoldCounter.dec,
      List.replicate_succ]
  · by_cases hv : PalPeg.LocalCounter.val t = 0
    · simp [hv, absCtr, PalPeg.LocalCounter.negOfNat, PalPeg.GalilScaffoldCounter.ofNat,
        PalPeg.GalilScaffoldCounter.dec]
    · obtain ⟨v, hvv⟩ : ∃ v, PalPeg.LocalCounter.val t = v + 1 := by
        cases hval : PalPeg.LocalCounter.val t with
        | zero => exact absurd hval hv
        | succ v => exact ⟨v, rfl⟩
      simp only [hv, Bool.true_and, decide_not, ne_eq, decide_false, Bool.not_false, if_pos]
      rw [PalPeg.LocalCounter.absCtr_pop hvv true]
      simp

/-- **one increment of a counter, on its tape.**  The mirror of `absCtr_dec`: a counter tape
holds the absolute value, so an increment is a push while the sign is positive and a pop while it
is negative — and at zero on the negative side it is a push that turns the sign around. -/
theorem absCtr_inc (t : STape Seg) (b : Bool) :
    absCtr
        (if b || decide (PalPeg.LocalCounter.val t = 0) then PalPeg.LocalCounter.push t
          else PalPeg.LocalCounter.pop t)
        (b || decide (PalPeg.LocalCounter.val t = 0))
      = PalPeg.GalilScaffoldCounter.inc (absCtr t b) := by
  cases b
  · by_cases hv : PalPeg.LocalCounter.val t = 0
    · simp only [hv, Bool.false_or, decide_true, if_true]
      simp [absCtr, PalPeg.LocalCounter.negOfNat, PalPeg.GalilScaffoldCounter.ofNat,
        PalPeg.GalilScaffoldCounter.inc, hv]
    · obtain ⟨n, hn⟩ : ∃ n, PalPeg.LocalCounter.val t = n + 1 := by
        cases hval : PalPeg.LocalCounter.val t with
        | zero => exact absurd hval hv
        | succ n => exact ⟨n, rfl⟩
      simp only [Bool.false_or, decide_eq_false hv, Bool.false_eq_true, if_false]
      rw [PalPeg.LocalCounter.absCtr_pop hn false]
      simp
  · simp only [Bool.true_or, if_true]
    rw [PalPeg.LocalCounter.absCtr_push t true]
    simp

/-- **a counter is positive exactly when it carries marks on the positive side.**  A counter
tape holds only the absolute value; the sign is a bit of the finite control, so the sign test
is that bit together with the zero test. -/
theorem positive_absCtr (t : STape Seg) (b : Bool) :
    PalPeg.GalilScaffoldCounter.positive (absCtr t b)
      = (b && decide (PalPeg.LocalCounter.val t ≠ 0)) := by
  cases b <;> cases hv : PalPeg.LocalCounter.val t <;>
    simp [absCtr, PalPeg.GalilScaffoldCounter.positive, PalPeg.GalilScaffoldCounter.ofNat,
      PalPeg.LocalCounter.negOfNat, hv, List.replicate_succ]

/-- **a counter is zero exactly when the cell below its head is not a mark.**  A counter is
stored as a run of marks at the top of its left stack, so its value is zero exactly when the
cell below the head carries something else — and that cell is in the window.  This is the
counter half of the branch conditions, as `placeRead_isNone_iff_centre` is the cursor half. -/
theorem counterZero_iff_belowRead {margin K : ℕ} {x : State GalilVM} {polarity : Fin 16 → Bool}
    {gap : Fin 4 → Bool} {micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl}
    {fppLive dpLive : Bool} {T : Slot → STape Γm}
    (henc : EncTapes margin x polarity gap micro fppLive dpLive T) (hK1 : 1 ≤ K) (hK : K ≤ margin)
    (c : Fin 16) (value : PalPeg.GalilScaffoldCounter.Counter)
    (hvalue : counterOf x c = some value) :
    PalPeg.GalilScaffoldCounter.zero value = true
      ↔ belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) (counterSlot c)
          ≠ encSeg PalPeg.LocalCounter.mark := by
  obtain ⟨segments, habs, htape⟩ := henc.counters c value hvalue
  have hzero : PalPeg.GalilScaffoldCounter.zero value
      = decide (PalPeg.LocalCounter.val segments = 0) := by
    rw [← habs]
    exact PalPeg.LocalCounter.zero_iff segments (polarity c)
  have hbelow :
      belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) (counterSlot c)
        = PalPeg.Local.readWin blankM K (padLeft margin (mapTape encSeg segments))
            ⟨K - 1, by omega⟩ := by
    show PalPeg.Local.readWin blankM K (tapesOf T (slotIndex (counterSlot c))) ⟨K - 1, by omega⟩ = _
    rw [tapesOf_apply,
      show T (counterSlot c) = padLeft margin (mapTape encSeg segments) from htape]
  rw [hbelow, hzero, decide_eq_true_eq]
  exact counterZero_iff_below hK1 (by omega) segments

/-- the slot of the chain's period tape. -/
abbrev periodSlot : Slot := .inr (.inr (.inr (.inr (.inl ()))))

/-- **the symbol the chain's period tape offers is in the window.**  The period tape is stored
with the symbol under the head, so the machine reads it as the centre cell of one slot.

This is what the scan's row needs of the chain: a watching chain steps its verifier exactly when
it has lag to spend and its period tape offers a symbol, and the second of those two conditions
is this reading.  The verdict itself — whether the symbol matches the input — decides which way
the chain goes, but not whether the cursor moves, so the row does not have to read it. -/
theorem centreRead_periodSlot {margin K : ℕ} {x : State GalilVM} {polarity : Fin 16 → Bool}
    {gap : Fin 4 → Bool} {micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl}
    {fppLive dpLive : Bool} {T : Slot → STape Γm}
    (henc : EncTapes margin x polarity gap micro fppLive dpLive T) (hK : K ≤ margin)
    (tape : PalPeg.GalilScaffoldChainPeriod.Tape) (hperiod : periodOf x = some tape) :
    centreRead (fun t => PalPeg.Local.readWin blankM K (tapesOf T t)) periodSlot
      = encToken (encPeriod tape).focus := by
  rw [centreRead_of_margin T periodSlot (hK.trans (henc.margins periodSlot)),
    show T periodSlot = padLeft margin (mapTape encToken (encPeriod tape)) from
      henc.period tape hperiod]
  rfl

/-- **a tick in which the chain consumes a letter, on the slots the step writes.**  Three things
move and nothing else the encoding speaks about does: the lag comes down by one, the distance
goes up by one, and the period tape takes a step.  Neither counter is anybody's mirror, so the
three slots are the whole of it.

The cursors are not here.  The chain's verifier moves too, but a step right is not an action of
the step's own table — it is eleven slots of the view layer — so this theorem is about the state
in which the cursor has not moved yet, which is `stepState`. -/
theorem encTapes_chainConsume (margin : ℕ) (x y : State GalilVM)
    (polarity newPolarity : Fin 16 → Bool) (gap : Fin 4 → Bool)
    (micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl) (fppLive dpLive : Bool)
    (tapes newTapes : Slot → STape Γm)
    (henc : EncTapes margin x polarity gap micro fppLive dpLive tapes)
    (hheads : headOf y = headOf x) (hplaces : placeOf y = placeOf x)
    (hfpp : ∀ i, y.vm.fpp.program.config.tapes i = x.vm.fpp.program.config.tapes i)
    (hdp : ∀ i, y.vm.dp.config.tapes i = x.vm.dp.config.tapes i)
    (hanswer : answerOf y = answerOf x)
    (hcountersOther : ∀ c : Fin 16, c ≠ 11 → c ≠ 13 → counterOf y c = counterOf x c)
    (hpolOther : ∀ c : Fin 16, c ≠ 11 → c ≠ 13 → newPolarity c = polarity c)
    (lag : PalPeg.GalilScaffoldCounter.Counter) (hlag : counterOf y 11 = some lag)
    (segLag : STape Seg) (habsLag : absCtr segLag (newPolarity 11) = lag)
    (hslotLag : newTapes (counterSlot 11) = padLeft margin (mapTape encSeg segLag))
    (dist : PalPeg.GalilScaffoldCounter.Counter) (hdist : counterOf y 13 = some dist)
    (segDist : STape Seg) (habsDist : absCtr segDist (newPolarity 13) = dist)
    (hslotDist : newTapes (counterSlot 13) = padLeft margin (mapTape encSeg segDist))
    (tape : PalPeg.GalilScaffoldChainPeriod.Tape) (hperiod : periodOf y = some tape)
    (hslotPeriod : newTapes periodSlot = padLeft margin (mapTape encToken (encPeriod tape)))
    (hidleShape : ∀ k : Fin 9, ∃ raw : STape (Fin 9),
      newTapes (progSlotOf (!fppLive) k) = padLeft margin (mapTape encProg raw))
    (hkept : ∀ slot, slot ≠ counterSlot 11 → slot ≠ counterSlot 13 → slot ≠ periodSlot →
      (∀ k : Fin 9, slot ≠ progSlotOf (!fppLive) k) → newTapes slot = tapes slot) :
    EncTapes margin y newPolarity gap micro fppLive dpLive newTapes where
  margins := by
    intro slot
    by_cases h11 : slot = counterSlot 11
    · rw [h11, hslotLag, pos_padLeft]; omega
    · by_cases h13 : slot = counterSlot 13
      · rw [h13, hslotDist, pos_padLeft]; omega
      · by_cases hp : slot = periodSlot
        · rw [hp, hslotPeriod, pos_padLeft]; omega
        · by_cases hidle : ∃ k : Fin 9, slot = progSlotOf (!fppLive) k
          · obtain ⟨k, hk⟩ := hidle
            obtain ⟨raw, hraw⟩ := hidleShape k
            rw [hk, hraw, pos_padLeft]
            omega
          · rw [hkept slot h11 h13 hp (fun k hk => hidle ⟨k, hk⟩)]
            exact henc.margins slot
  heads := by
    intro v head hhead
    obtain ⟨view, viewTapes, habs, hrep, hslots, hcells, hwf⟩ :=
      henc.heads v head (by rw [← congrFun hheads v]; exact hhead)
    exact ⟨view, viewTapes, habs, hrep, fun i => by
      rw [hkept _ (by simp [headSlot, counterSlot]) (by simp [headSlot, counterSlot])
        (by simp [headSlot, periodSlot])
        (by intro k; cases fppLive <;> simp [progSlotOf, headSlot]), hslots i], hcells, hwf⟩
  idleHead := by
    intro h3
    obtain ⟨view, viewTapes, hrep, hslots, hcells, hwf⟩ :=
      henc.idleHead (by rw [← congrFun hheads 3]; exact h3)
    exact ⟨view, viewTapes, hrep, fun i => by
      rw [hkept _ (by simp [headSlot, counterSlot]) (by simp [headSlot, counterSlot])
        (by simp [headSlot, periodSlot])
        (by intro k; cases fppLive <;> simp [progSlotOf, headSlot]), hslots i], hcells, hwf⟩
  fpp := by
    intro i
    rw [hkept _ (by cases fppLive <;> simp [progSlotOf, counterSlot])
      (by cases fppLive <;> simp [progSlotOf, counterSlot])
      (by cases fppLive <;> simp [progSlotOf, periodSlot])
      (fun k => progSlotOf_ne_flip fppLive i k), henc.fpp i, hfpp i]
  dp := by
    intro i
    rw [hkept _ (by cases dpLive <;> simp [dpSlotOf, counterSlot])
      (by cases dpLive <;> simp [dpSlotOf, counterSlot])
      (by cases dpLive <;> simp [dpSlotOf, periodSlot])
      (by intro k; cases fppLive <;> cases dpLive <;> simp [progSlotOf, dpSlotOf]),
      henc.dp i, hdp i]
  idleShape := hidleShape
  counters := by
    intro c value hvalue
    by_cases h11 : c = 11
    · subst h11
      rw [hlag] at hvalue
      exact ⟨segLag, by rw [habsLag, Option.some.inj hvalue], hslotLag⟩
    · by_cases h13 : c = 13
      · subst h13
        rw [hdist] at hvalue
        exact ⟨segDist, by rw [habsDist, Option.some.inj hvalue], hslotDist⟩
      · obtain ⟨seg, habs, hslot⟩ :=
          henc.counters c value (by rw [← hcountersOther c h11 h13]; exact hvalue)
        exact ⟨seg, by rw [hpolOther c h11 h13]; exact habs, by
          rw [hkept _ (by simpa using fun h => h11 h) (by simpa using fun h => h13 h)
            (by simp [counterSlot, periodSlot])
            (by intro k; cases fppLive <;> simp [progSlotOf, counterSlot]), hslot]⟩
  places := by
    intro i place hplace
    obtain ⟨st, jk, hsealed, hlen, hstack, hslotp⟩ :=
      henc.places i place (by rw [← congrFun hplaces i]; exact hplace)
    exact ⟨st, jk, hsealed, hlen, hstack, by
      rw [hkept _ (by simp [placeSlot, counterSlot]) (by simp [placeSlot, counterSlot])
        (by simp [placeSlot, periodSlot])
        (by intro k; cases fppLive <;> simp [progSlotOf, placeSlot]), hslotp]⟩
  mirrors := by
    intro m value hvalue
    have h11 : mirrorSource m ≠ 11 := by fin_cases m <;> decide
    have h13 : mirrorSource m ≠ 13 := by fin_cases m <;> decide
    obtain ⟨seg, habs, hslotm⟩ :=
      henc.mirrors m value (by rw [← hcountersOther _ h11 h13]; exact hvalue)
    exact ⟨seg, by rw [hpolOther _ h11 h13]; exact habs, by
      rw [hkept _ (by simp [mirrorSlot, counterSlot]) (by simp [mirrorSlot, counterSlot])
        (by simp [mirrorSlot, periodSlot])
        (by intro k; cases fppLive <;> simp [progSlotOf, mirrorSlot]), hslotm]⟩
  period := by
    intro tape' htape'
    rw [hperiod] at htape'
    rw [← Option.some.inj htape', hslotPeriod]
  answer := by
    intro tape' htape'
    rw [hkept _ (by simp [counterSlot]) (by simp [counterSlot]) (by simp [periodSlot])
      (by intro k; cases fppLive <;> simp [progSlotOf])]
    exact henc.answer tape' (by rw [← hanswer]; exact htape')

/-- **a tick that walks the chain's period tape and nothing else the encoding speaks about.**
The period tape is nobody's mirror, so one slot changes.  Stated for two states that agree
everywhere but there, so that a branch which moves several components applies it once among the
others. -/
theorem encTapes_periodStep (margin : ℕ) (x y : State GalilVM) (polarity : Fin 16 → Bool)
    (gap : Fin 4 → Bool) (micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl)
    (fppLive dpLive : Bool) (tapes newTapes : Slot → STape Γm)
    (henc : EncTapes margin x polarity gap micro fppLive dpLive tapes)
    (tape : PalPeg.GalilScaffoldChainPeriod.Tape) (hperiod : periodOf y = some tape)
    (hcounters : counterOf y = counterOf x) (hheads : headOf y = headOf x)
    (hplaces : placeOf y = placeOf x)
    (hfpp : ∀ i, y.vm.fpp.program.config.tapes i = x.vm.fpp.program.config.tapes i)
    (hdp : ∀ i, y.vm.dp.config.tapes i = x.vm.dp.config.tapes i)
    (hanswer : answerOf y = answerOf x)
    (hslot : newTapes periodSlot = padLeft margin (mapTape encToken (encPeriod tape)))
    (hkept : ∀ slot, slot ≠ periodSlot → newTapes slot = tapes slot) :
    EncTapes margin y polarity gap micro fppLive dpLive newTapes where
  margins := by
    intro slot
    by_cases hp : slot = periodSlot
    · rw [hp, hslot, pos_padLeft]
      omega
    · rw [hkept slot hp]
      exact henc.margins slot
  heads := by
    intro v head hhead
    obtain ⟨view, viewTapes, habs, hrep, hslots, hcells, hwf⟩ :=
      henc.heads v head (by rw [← congrFun hheads v]; exact hhead)
    exact ⟨view, viewTapes, habs, hrep, fun i => by
      rw [hkept _ (by simp [headSlot, periodSlot]), hslots i], hcells, hwf⟩
  idleHead := by
    intro h3
    obtain ⟨view, viewTapes, hrep, hslots, hcells, hwf⟩ :=
      henc.idleHead (by rw [← congrFun hheads 3]; exact h3)
    exact ⟨view, viewTapes, hrep, fun i => by
      rw [hkept _ (by simp [headSlot, periodSlot]), hslots i], hcells, hwf⟩
  fpp := by
    intro i
    rw [hkept _ (by cases fppLive <;> simp [progSlotOf, periodSlot]), henc.fpp i, hfpp i]
  dp := by
    intro i
    rw [hkept _ (by cases dpLive <;> simp [dpSlotOf, periodSlot]), henc.dp i, hdp i]
  idleShape := by
    intro i
    obtain ⟨raw, hraw⟩ := henc.idleShape i
    exact ⟨raw, by
      rw [hkept _ (by cases fppLive <;> simp [progSlotOf, periodSlot]), hraw]⟩
  counters := by
    intro c value hvalue
    obtain ⟨seg, habs, hslotc⟩ :=
      henc.counters c value (by rw [← congrFun hcounters c]; exact hvalue)
    exact ⟨seg, habs, by rw [hkept _ (by simp [counterSlot, periodSlot]), hslotc]⟩
  places := by
    intro i place hplace
    obtain ⟨st, jk, hsealed, hlen, hstack, hslotp⟩ :=
      henc.places i place (by rw [← congrFun hplaces i]; exact hplace)
    exact ⟨st, jk, hsealed, hlen, hstack, by
      rw [hkept _ (by simp [placeSlot, periodSlot]), hslotp]⟩
  mirrors := by
    intro m value hvalue
    obtain ⟨seg, habs, hslotm⟩ :=
      henc.mirrors m value (by rw [← congrFun hcounters _]; exact hvalue)
    exact ⟨seg, habs, by rw [hkept _ (by simp [mirrorSlot, periodSlot]), hslotm]⟩
  period := by
    intro tape' htape'
    rw [hperiod] at htape'
    rw [← Option.some.inj htape', hslot]
  answer := by
    intro tape' htape'
    rw [hkept _ (by simp [periodSlot])]
    exact henc.answer tape' (by rw [← hanswer]; exact htape')

/-- **a counter is positive exactly when its sign bit is set and the cell below its head is a
mark.**  The counterpart of `counterZero_iff_belowRead` for the sign test. -/
theorem counterPositive_iff_belowRead {margin K : ℕ} {x : State GalilVM} {polarity : Fin 16 → Bool}
    {gap : Fin 4 → Bool} {micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl}
    {fppLive dpLive : Bool} {T : Slot → STape Γm}
    (henc : EncTapes margin x polarity gap micro fppLive dpLive T) (hK1 : 1 ≤ K) (hK : K ≤ margin)
    (c : Fin 16) (value : PalPeg.GalilScaffoldCounter.Counter)
    (hvalue : counterOf x c = some value) :
    PalPeg.GalilScaffoldCounter.positive value = true
      ↔ polarity c = true
        ∧ belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) (counterSlot c)
            = encSeg PalPeg.LocalCounter.mark := by
  obtain ⟨segments, habs, htape⟩ := henc.counters c value hvalue
  have hbelow :
      belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) (counterSlot c)
        = PalPeg.Local.readWin blankM K (padLeft margin (mapTape encSeg segments))
            ⟨K - 1, by omega⟩ := by
    show PalPeg.Local.readWin blankM K (tapesOf T (slotIndex (counterSlot c))) ⟨K - 1, by omega⟩ = _
    rw [tapesOf_apply,
      show T (counterSlot c) = padLeft margin (mapTape encSeg segments) from htape]
  have hval := counterZero_iff_below hK1 (show K ≤ margin + 1 by omega) segments
  rw [← habs, positive_absCtr, hbelow, Bool.and_eq_true, decide_eq_true_eq]
  refine and_congr_right (fun _ => ⟨fun hne => ?_, fun hmark hzero => (hval.mp hzero) hmark⟩)
  exact not_not.mp (fun hnotmark => hne (hval.mpr hnotmark))

/-- **the fallback copy's branch condition is two readings of the window.**  The copy continues
while the walker still has a letter and the work counter is not yet spent; the first is the
centre of the walker's slot, the second the cell below the head of the work counter's slot.
Neither asks the machine to move a head, so the branch is taken on what the rule can see. -/
theorem copyRemainingTest_iff_window {margin K : ℕ} {x : State GalilVM} {polarity : Fin 16 → Bool}
    {gap : Fin 4 → Bool} {micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl}
    {fppLive dpLive : Bool} {T : Slot → STape Γm}
    (henc : EncTapes margin x polarity gap micro fppLive dpLive T) (hK1 : 1 ≤ K) (hK : K ≤ margin) :
    PalPeg.FrameFunction.copyRemainingTest x.vm.fpp = true
      ↔ centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) (placeSlot 1)
            ≠ blankM
          ∧ belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) (counterSlot 9)
            = encSeg PalPeg.LocalCounter.mark := by
  have hwalker := placeRead_isNone_iff_centre henc hK 1 x.vm.fpp.walker rfl
  have hwork := counterZero_iff_belowRead henc hK1 hK 9 x.vm.fpp.work rfl
  unfold PalPeg.FrameFunction.copyRemainingTest
  cases hread : (PalPeg.GalilScaffoldPlace.read x.vm.fpp.walker).isNone <;>
    cases hzero : PalPeg.GalilScaffoldCounter.zero x.vm.fpp.work <;> simp_all

/-- the test the tick function asks in both the shift mode and the copy mode, read off the
frame. -/
theorem frameFun_remainingPos (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (s : GalilVM) :
    (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).remainingPos s
      = (PalPeg.GalilScaffoldCounter.positive s.remaining
          || PalPeg.FrameFunction.copyRemainingTest s.fpp) := rfl

/-- **the whole branch condition of the copy mode is three cells of the window and one bit of
the finite control.**  The tick function asks one test in both the shift mode and the copy mode,
and it is a disjunction: the shift's own counter is still positive, or the fallback copy still
has a letter and work left.  Each disjunct is decided where it stands. -/
theorem remainingPos_iff_window {margin K : ℕ} {x : State GalilVM} {polarity : Fin 16 → Bool}
    {gap : Fin 4 → Bool} {micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl}
    {fppLive dpLive : Bool} {T : Slot → STape Γm}
    (henc : EncTapes margin x polarity gap micro fppLive dpLive T) (hK1 : 1 ≤ K) (hK : K ≤ margin)
    (centre : GalilVM → Fin 3) (place : GalilVM → PalPeg.GalilScaffoldPlace.Place)
    (entry entryQ : ℕ) (first : Fin 9) (w : List (Fin 2)) :
    (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).remainingPos x.vm
        = true
      ↔ (polarity 1 = true
            ∧ belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) (counterSlot 1)
                = encSeg PalPeg.LocalCounter.mark)
          ∨ (centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) (placeSlot 1)
                ≠ blankM
              ∧ belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
                  (counterSlot 9) = encSeg PalPeg.LocalCounter.mark) := by
  rw [frameFun_remainingPos, Bool.or_eq_true]
  exact or_congr (counterPositive_iff_belowRead henc hK1 hK 1 x.vm.remaining rfl)
    (copyRemainingTest_iff_window henc hK1 hK)

/-- **one tick of the fallback copy, on the walker.**  A cursor standing on the gap beside a
letter only flips its own bit, so its tape does not move; one standing on a letter hands that
letter over and pops it.  Either way the tape that comes out represents the cursor that
`GalilScaffoldPlace.left` returns. -/
theorem copy_one_place {margin K : ℕ} (hK : K ≤ margin)
    (tapes : Slot → STape Γm) (walker : PalPeg.GalilScaffoldPlace.Place)
    (gapBit : Bool) (hgap : gapBit = walker.gap)
    (a : Fin 3) (hread : PalPeg.GalilScaffoldPlace.read walker = some a)
    (stackTape : STape PalPeg.CloseoutCoreStep.Γc) (junk : List (Option (Fin 2)))
    (hstack : PalPeg.ConcreteLocalMachine.StackTape stackTape
      (walker.letters.map (fun letter => some letter) ++ junk))
    (hslot : tapes (placeSlot 1) = padLeft margin (mapTape encCell stackTape)) :
    ∃ stackTape' : STape PalPeg.CloseoutCoreStep.Γc,
      PalPeg.ConcreteLocalMachine.StackTape stackTape'
          ((PalPeg.GalilScaffoldPlace.left walker).letters.map (fun letter => some letter) ++ junk)
        ∧ PalPeg.CloseoutCoreEnc12.actList blankM (tapes (placeSlot 1))
            (if gapBit then []
              else [some (centreRead
                  (fun tape => PalPeg.Local.readWin blankM K (tapesOf tapes tape)) (placeSlot 1),
                (.left : PalPeg.CloseoutCoreEnc12.MoveC))])
          = padLeft margin (mapTape encCell stackTape') := by
  by_cases hg : gapBit = true
  · refine ⟨stackTape, ?_, ?_⟩
    · have hletters : (PalPeg.GalilScaffoldPlace.left walker).letters = walker.letters := by
        unfold PalPeg.GalilScaffoldPlace.left
        rw [if_pos (hgap ▸ hg)]
      rw [hletters]
      exact hstack
    · rw [if_pos hg]
      exact hslot
  · have hnotGap : walker.gap = false := by
      cases hw : walker.gap
      · rfl
      · exact absurd (hgap.trans hw) hg
    obtain ⟨letter, rest, hletters⟩ : ∃ letter rest, walker.letters = letter :: rest := by
      cases hl : walker.letters with
      | nil =>
        exfalso
        rw [show PalPeg.GalilScaffoldPlace.read walker = none from by
          unfold PalPeg.GalilScaffoldPlace.read
          rw [hl]] at hread
        simp at hread
      | cons b bs => exact ⟨b, bs, rfl⟩
    have hmargin : K ≤ PalPeg.Local.pos (tapes (placeSlot 1)) := by
      rw [hslot, pos_padLeft]
      omega
    have hcentre : centreRead
        (fun tape => PalPeg.Local.readWin blankM K (tapesOf tapes tape)) (placeSlot 1)
        = encCell (PalPeg.CloseoutCoreEnc.cellSym (some letter)) := by
      rw [centreRead_of_margin tapes (placeSlot 1) hmargin, hslot]
      show encCell stackTape.focus = _
      rw [stackTape_focus stackTape _ hstack, hletters]
      rfl
    have hstack2 : PalPeg.ConcreteLocalMachine.StackTape stackTape
        (some letter :: (rest.map (fun letter => some letter) ++ junk)) := by
      have h := hstack
      rw [hletters] at h
      simpa only [List.map_cons, List.cons_append] using h
    have hstack' := stackTape_pop stackTape (some letter)
      (rest.map (fun letter => some letter) ++ junk) hstack2
    refine ⟨PalPeg.CloseoutCoreEnc12.actOnG PalPeg.CloseoutCoreStep.blankc stackTape
        (some (PalPeg.CloseoutCoreEnc.cellSym (some letter),
          (.left : PalPeg.CloseoutCoreEnc12.MoveC))), ?_, ?_⟩
    · have hletters' : (PalPeg.GalilScaffoldPlace.left walker).letters = rest := by
        unfold PalPeg.GalilScaffoldPlace.left
        rw [if_neg (by simp [hnotGap]), hletters]
        rfl
      rw [hletters']
      exact hstack'
    · rw [if_neg hg, hcentre, hslot]
      exact (padded_place_pop margin stackTape (some letter)
        (rest.map (fun letter => some letter) ++ junk) hstack2).symm

/-- the refresh of the controller's output, read off the frame: two questions about the input
heads, and the old bit when the first of them says no. -/
theorem frameFun_refresh (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (s : GalilVM) (old : Bool) :
    PalPeg.GalilScaffoldTop.refreshFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) s old
      = if PalPeg.GalilScaffoldChainInputSupply.onLetterTest w s then
          PalPeg.GalilScaffoldChainInputSupply.leftFirstTest s else old := rfl

/-- **the control table of the end of the shift.**  The shift has nothing left to move, so the
machine goes back to scanning and refreshes its output — and the refresh is the two bits the
control already carries. -/
noncomputable def shiftExitNext {fppBound dpBound : ℕ} (q : QPhys fppBound dpBound) :
    QPhys fppBound dpBound :=
  {q with ctl := {q.ctl with mode := PalPeg.GalilScaffoldController.Mode.scan, output := if q.onLetterBit then q.leftFirstBit else q.ctl.output}}

/-- **the end of the shift, on the whole state.**  Not one tape moves: the tick changes the
controller's mode and its output bit, and the output bit is what the two carried bits say. -/
theorem shift_exit {fppBound dpBound : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (tapes : Slot → STape Γm)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.shift)
    (hdone : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).remainingPos x.vm
      = false)
    (henc : Enc w margin x (q, tapes)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      (shiftExitNext q, tapes) := by
  have hval : PalPeg.GalilScaffoldTop.tickFun
      (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x
      = ⟨{x.ctl with mode := PalPeg.GalilScaffoldController.Mode.scan, output := PalPeg.GalilScaffoldTop.refreshFun (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) x.vm x.ctl.output}, x.vm⟩ := by
    simp only [PalPeg.GalilScaffoldTop.tickFun, hmode]
    rw [if_neg (by simp [hdone])]
  have hctl : ctlAbs {q.ctl with mode := PalPeg.GalilScaffoldController.Mode.scan, output := if q.onLetterBit then q.leftFirstBit else q.ctl.output}
      = {x.ctl with mode := PalPeg.GalilScaffoldController.Mode.scan, output := PalPeg.GalilScaffoldTop.refreshFun (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) x.vm x.ctl.output} := by
    rw [frameFun_refresh, ← henc.1.ctl, henc.1.onLetter, henc.1.leftFirst]
    rfl
  rw [hval]
  exact ⟨encControl_ctl x q henc.1 _ _ hctl,
    encTapes_congr margin x _ q.polarity q.gap q.micro q.fppLive q.dpLive tapes
      (fun i => rfl) (fun i => rfl) rfl rfl rfl rfl rfl henc.2⟩

/-- **the end of the shift, rule and encoding together.**  The branch names no action at all. -/
theorem shift_exit_of_rule {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (R : PalPeg.CloseoutCoreEnc12.ActRule (Fin 2) (QPhys fppBound dpBound) Γm tapeCountM K)
    (hnq : R.nq q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = shiftExitNext q)
    (hacts : R.acts q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = withErase q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (fun _ => []))
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.shift)
    (hdone : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).remainingPos x.vm
      = false)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2
          (slotIndex i)) := by
  have hq : (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).1 = shiftExitNext q := by
    show R.nq q none _ = _
    rw [hnq]
  obtain ⟨hmovedAll, hkept⟩ := idealStep_offBase R q T q.fppLive _ hacts (fun _ _ => rfl)
  have hkeptAll : ∀ slot : Slot, (∀ k : Fin 9, slot ≠ progSlotOf (!q.fppLive) k) →
      (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2 (slotIndex slot)
        = T slot := by
    intro slot hslot
    by_cases hlive : ∃ j : Fin 9, slot = progSlotOf q.fppLive j
    · obtain ⟨j, hj⟩ := hlive
      subst hj
      exact hmovedAll j
    · exact hkept slot (fun j hj => hlive ⟨j, hj⟩) hslot
  rw [hq]
  exact ⟨(shift_exit margin centre place entry entryQ first w F delay x q T hmode hdone henc).1,
    encTapes_idleOnly margin _ _ _ _ _ _ T _
      (shift_exit margin centre place entry entryQ first w F delay x q T hmode hdone henc).2
      hkeptAll
      (idle_shape_after_erase margin hK1 hKn R q T q.fppLive _ hacts (fun _ => rfl)
        henc.2.idleShape)⟩

/-- **the view a head steps left onto.**  The head's own step takes the top of the back stack
for its focus and drops the old focus onto the near stack; the queue is not touched. -/
def leftView (v : PalPeg.LocalInputView.InputView) : PalPeg.LocalInputView.InputView :=
  match v.back with
  | [] => {v with gap := true}
  | a :: tail => ⟨tail, a, v.focus :: v.near, v.far, true⟩

/-- **a head's step does not change what its view holds.**  The cells of a view are its back
reversed, its focus and everything right of it; a step left moves the boundary and not the
content. -/
theorem cells_leftView (v : PalPeg.LocalInputView.InputView) (a : Option (Fin 2))
    (tail : List (Option (Fin 2))) (hback : v.back = a :: tail) :
    PalPeg.LocalInputView.cells (leftView v) = PalPeg.LocalInputView.cells v := by
  unfold PalPeg.LocalInputView.cells leftView
  rw [hback]
  simp [PalPeg.LocalInputView.absRight, PalPeg.LocalInputView.farList]

theorem viewCells_leftView (v : PalPeg.LocalInputView.InputView) (a : Option (Fin 2))
    (tail : List (Option (Fin 2))) (hback : v.back = a :: tail)
    (hcells : PalPeg.LocalViewCells.ViewCells v) :
    PalPeg.LocalViewCells.ViewCells (leftView v) := by
  obtain ⟨letters, hletters⟩ := hcells
  exact ⟨letters, by rw [cells_leftView v a tail hback, hletters]⟩

theorem viewCells_setGap (v : PalPeg.LocalInputView.InputView) (b : Bool)
    (hcells : PalPeg.LocalViewCells.ViewCells v) :
    PalPeg.LocalViewCells.ViewCells {v with gap := b} := by
  obtain ⟨letters, hletters⟩ := hcells
  exact ⟨letters, hletters⟩

/-- **the view a head steps left onto is the one the view layer's own command names.**  A head
move is already a `ViewCommand`, and `LocalInputView.moveLeftV` is what applying it does; the
`leftView` written here is that, on the half-step that moves the zipper. -/
theorem leftView_eq_moveLeftV (v : PalPeg.LocalInputView.InputView) (hgap : v.gap = false) :
    leftView v = PalPeg.LocalInputView.moveLeftV v := by
  obtain ⟨back, focus, near, far, g⟩ := v
  subst hgap
  unfold leftView PalPeg.LocalInputView.moveLeftV PalPeg.LocalInputView.stepLeft
  rw [if_neg (by simp)]
  cases back <;> rfl

/-- **the abstraction of that view is the head one step left**, when the head was on a letter
rather than on the gap beside it. -/
theorem absHead_leftView (v : PalPeg.LocalInputView.InputView) (hgap : v.gap = false)
    (a : Option (Fin 2)) (tail : List (Option (Fin 2))) (hback : v.back = a :: tail) :
    PalPeg.LocalArrival.absHead' (leftView v) []
      = PalPeg.GalilScaffoldInputHead.left (PalPeg.LocalArrival.absHead' v []) := by
  simp [leftView, PalPeg.GalilScaffoldInputHead.left, PalPeg.LocalArrival.absHead',
    PalPeg.GalilScaffoldInputHead.moveLeft, hgap, hback]

/-- **a head's step left, on the twelve tapes of its view.**  One action pops the back stack and
two push the old focus onto the near stack; the ten tapes of the queue are not touched, so the
queue's own representation survives with the same micro-control. -/
theorem viewRep_left {margin : ℕ} (v : PalPeg.LocalInputView.InputView)
    (micro : PalPeg.ConcreteLocalMachine.MicroControl)
    (tapes tapes' : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (a : Option (Fin 2)) (tail : List (Option (Fin 2))) (hback : v.back = a :: tail)
    (hrep : PalPeg.ConcreteLocalMachine.ViewRep margin v false micro tapes)
    (hbackTape : tapes' PalPeg.ConcreteLocalMachine.backTape
      = PalPeg.CloseoutCoreEnc12.actOnG PalPeg.CloseoutCoreStep.blankc
          (tapes PalPeg.ConcreteLocalMachine.backTape)
          (some (PalPeg.CloseoutCoreEnc.cellSym v.focus,
            (.left : PalPeg.CloseoutCoreEnc12.MoveC))))
    (hnearTape : tapes' PalPeg.ConcreteLocalMachine.nearTape
      = PalPeg.CloseoutCoreEnc12.actList PalPeg.CloseoutCoreStep.blankc
          (tapes PalPeg.ConcreteLocalMachine.nearTape)
          [some ((tapes PalPeg.ConcreteLocalMachine.nearTape).focus,
              (.right : PalPeg.CloseoutCoreEnc12.MoveC)),
            some (PalPeg.CloseoutCoreEnc.cellSym v.focus,
              (.stay : PalPeg.CloseoutCoreEnc12.MoveC))])
    (hkept : ∀ t, t ≠ PalPeg.ConcreteLocalMachine.backTape →
      t ≠ PalPeg.ConcreteLocalMachine.nearTape → tapes' t = tapes t) :
    PalPeg.ConcreteLocalMachine.ViewRep margin (leftView v) true micro tapes' where
  gap := by
    unfold leftView
    rw [hback]
  queue := by
    have hq : (fun tape => tapes' (PalPeg.ConcreteLocalMachine.queueTapeOfView tape))
        = fun tape => tapes (PalPeg.ConcreteLocalMachine.queueTapeOfView tape) := by
      funext t
      have ht := t.isLt
      refine hkept _ ?_ ?_ <;>
        · intro hEq
          have hv := congrArg Fin.val hEq
          simp [PalPeg.ConcreteLocalMachine.queueTapeOfView,
            PalPeg.ConcreteLocalMachine.backTape, PalPeg.ConcreteLocalMachine.nearTape] at hv
          omega
    have hfar : (leftView v).far = v.far := by
      unfold leftView
      rw [hback]
    rw [hfar, hq]
    exact hrep.queue
  back := by
    obtain ⟨bottom, hlen, hst⟩ := hrep.back
    refine ⟨bottom, hlen, ?_⟩
    have hstack : PalPeg.ConcreteLocalMachine.backStack (leftView v) ++ bottom
        = v.back ++ bottom := by
      unfold PalPeg.ConcreteLocalMachine.backStack leftView
      rw [hback]
    rw [hstack, hbackTape]
    exact stackTape_pop (tapes PalPeg.ConcreteLocalMachine.backTape) v.focus (v.back ++ bottom)
      (by
        have : PalPeg.ConcreteLocalMachine.backStack v ++ bottom
            = v.focus :: (v.back ++ bottom) := rfl
        rwa [this] at hst)
  near := by
    obtain ⟨bottom, hsealed, hlen, hst⟩ := hrep.near
    refine ⟨bottom, hsealed, hlen, ?_⟩
    have hnear : (leftView v).near = v.focus :: v.near := by
      unfold leftView
      rw [hback]
    rw [hnear, hnearTape, List.cons_append]
    exact stackTape_push (tapes PalPeg.ConcreteLocalMachine.nearTape) v.focus (v.near ++ bottom) hst

/-- **a head with nothing behind it steps left for free too.**  `moveLeft` leaves a head whose
back is empty where it is, so again only the bit moves — and `leftView` is the same view with
the bit flipped. -/
theorem headRep_leftEmpty {margin : ℕ} {micro : PalPeg.ConcreteLocalMachine.MicroControl}
    (view : PalPeg.LocalInputView.InputView)
    (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (hback : view.back = []) (hgap : view.gap = false)
    (hrep : PalPeg.ConcreteLocalMachine.ViewRep margin view false micro viewTapes) :
    PalPeg.LocalArrival.absHead' (leftView view) []
        = PalPeg.GalilScaffoldInputHead.left (PalPeg.LocalArrival.absHead' view [])
      ∧ PalPeg.ConcreteLocalMachine.ViewRep margin (leftView view) true micro viewTapes := by
  have hleftView : leftView view = {view with gap := true} := by
    unfold leftView
    rw [hback]
  refine ⟨?_, ?_⟩
  · rw [hleftView]
    simp [PalPeg.GalilScaffoldInputHead.left, PalPeg.LocalArrival.absHead',
      PalPeg.GalilScaffoldInputHead.moveLeft, hgap, hback]
  · rw [hleftView]
    exact
      { gap := rfl
        queue := hrep.queue
        back := hrep.back
        near := hrep.near }

/-- **a head with nothing left to read steps right for free.**  `moveRight` leaves a head whose
near stack and whose queue are both empty exactly where it is, so only the bit moves.  This is
the third of the four cases of a step right; the fourth, where the queue still holds a letter, is
the micro-schedule's. -/
theorem headRep_rightExhausted {margin : ℕ} {micro : PalPeg.ConcreteLocalMachine.MicroControl}
    (view : PalPeg.LocalInputView.InputView)
    (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (hgap : view.gap = true) (hnear : view.near = [])
    (hfar : PalPeg.RTQueue.toList view.far = [])
    (hrep : PalPeg.ConcreteLocalMachine.ViewRep margin view true micro viewTapes) :
    PalPeg.LocalArrival.absHead' {view with gap := false} []
        = PalPeg.GalilScaffoldChainVerifier.right (PalPeg.LocalArrival.absHead' view [])
      ∧ PalPeg.ConcreteLocalMachine.ViewRep margin {view with gap := false} false micro
          viewTapes := by
  refine ⟨?_, ?_⟩
  · simp [PalPeg.GalilScaffoldChainVerifier.right, PalPeg.LocalArrival.absHead',
      PalPeg.GalilScaffoldInputTrace.moveRight, hgap, hnear, hfar]
  · exact
      { gap := rfl
        queue := hrep.queue
        back := hrep.back
        near := hrep.near }

/-- **the view a head steps right onto, when the cell it steps onto is on its near stack.**
The mirror of `leftView`: the old focus goes onto the back stack and the top of the near stack
becomes the focus.  The case where the near stack is empty is the queue's, and is not this. -/
def rightViewOn (v : PalPeg.LocalInputView.InputView) (a : Option (Fin 2))
    (rest : List (Option (Fin 2))) : PalPeg.LocalInputView.InputView :=
  ⟨v.focus :: v.back, a, rest, v.far, false⟩

/-- **and the view a head steps right onto is `LocalInputView.moveRight`**, on the half-step that
moves the zipper and while the cell it steps onto is on the near stack. -/
theorem rightViewOn_eq_moveRight (v : PalPeg.LocalInputView.InputView) (hgap : v.gap = true)
    (a : Option (Fin 2)) (rest : List (Option (Fin 2))) (hnear : v.near = a :: rest) :
    rightViewOn v a rest = PalPeg.LocalInputView.moveRight v := by
  unfold rightViewOn PalPeg.LocalInputView.moveRight PalPeg.LocalInputView.stepRight
  rw [if_pos (by simp [hgap])]
  rw [hnear]

/-- **the abstraction of that view is the head one step right**, when the head stood on a gap
with a cell on its near stack. -/
theorem absHead_rightViewOn (v : PalPeg.LocalInputView.InputView) (hgap : v.gap = true)
    (a : Option (Fin 2)) (rest : List (Option (Fin 2))) (hnear : v.near = a :: rest) :
    PalPeg.LocalArrival.absHead' (rightViewOn v a rest) []
      = PalPeg.GalilScaffoldChainVerifier.right (PalPeg.LocalArrival.absHead' v []) := by
  simp [rightViewOn, PalPeg.GalilScaffoldChainVerifier.right, PalPeg.LocalArrival.absHead',
    PalPeg.GalilScaffoldInputTrace.moveRight, hgap, hnear]

/-- **a head that stands on a letter steps right for free.**  Only its own bit moves; the cell
it steps onto is the gap beside the letter it is on. -/
theorem headRep_rightGap {margin : ℕ} {micro : PalPeg.ConcreteLocalMachine.MicroControl}
    (view : PalPeg.LocalInputView.InputView)
    (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (hgap : view.gap = false)
    (hrep : PalPeg.ConcreteLocalMachine.ViewRep margin view false micro viewTapes) :
    PalPeg.LocalArrival.absHead' {view with gap := true} []
        = PalPeg.GalilScaffoldChainVerifier.right (PalPeg.LocalArrival.absHead' view [])
      ∧ PalPeg.ConcreteLocalMachine.ViewRep margin {view with gap := true} true micro
          viewTapes := by
  refine ⟨?_, ?_⟩
  · simp [PalPeg.GalilScaffoldChainVerifier.right, PalPeg.LocalArrival.absHead', hgap]
  · exact
      { gap := rfl
        queue := hrep.queue
        back := hrep.back
        near := hrep.near }

/-- **a head's step right, on the twelve tapes of its view.**  The mirror of `viewRep_left`:
two actions push the old focus onto the back stack and one pops the near stack.  The queue is
untouched, so its representation survives with the same micro-control — which is why this step,
like the step left, is one physical step. -/
theorem viewRep_rightOn {margin : ℕ} (v : PalPeg.LocalInputView.InputView)
    (micro : PalPeg.ConcreteLocalMachine.MicroControl)
    (tapes tapes' : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (a : Option (Fin 2)) (rest : List (Option (Fin 2))) (hnear : v.near = a :: rest)
    (hrep : PalPeg.ConcreteLocalMachine.ViewRep margin v true micro tapes)
    (hbackTape : tapes' PalPeg.ConcreteLocalMachine.backTape
      = PalPeg.CloseoutCoreEnc12.actList PalPeg.CloseoutCoreStep.blankc
          (tapes PalPeg.ConcreteLocalMachine.backTape)
          [some ((tapes PalPeg.ConcreteLocalMachine.backTape).focus,
              (.right : PalPeg.CloseoutCoreEnc12.MoveC)),
            some (PalPeg.CloseoutCoreEnc.cellSym a,
              (.stay : PalPeg.CloseoutCoreEnc12.MoveC))])
    (hnearTape : tapes' PalPeg.ConcreteLocalMachine.nearTape
      = PalPeg.CloseoutCoreEnc12.actOnG PalPeg.CloseoutCoreStep.blankc
          (tapes PalPeg.ConcreteLocalMachine.nearTape)
          (some (PalPeg.CloseoutCoreEnc.cellSym a,
            (.left : PalPeg.CloseoutCoreEnc12.MoveC))))
    (hkept : ∀ t, t ≠ PalPeg.ConcreteLocalMachine.backTape →
      t ≠ PalPeg.ConcreteLocalMachine.nearTape → tapes' t = tapes t) :
    PalPeg.ConcreteLocalMachine.ViewRep margin (rightViewOn v a rest) false micro tapes' where
  gap := rfl
  queue := by
    have hq : (fun tape => tapes' (PalPeg.ConcreteLocalMachine.queueTapeOfView tape))
        = fun tape => tapes (PalPeg.ConcreteLocalMachine.queueTapeOfView tape) := by
      funext t
      have ht := t.isLt
      refine hkept _ ?_ ?_ <;>
        · intro hEq
          have hv := congrArg Fin.val hEq
          simp [PalPeg.ConcreteLocalMachine.queueTapeOfView,
            PalPeg.ConcreteLocalMachine.backTape, PalPeg.ConcreteLocalMachine.nearTape] at hv
          omega
    show PalPeg.ConcreteLocalMachine.MicroRep margin v.far micro _
    rw [hq]
    exact hrep.queue
  back := by
    obtain ⟨bottom, hlen, hst⟩ := hrep.back
    refine ⟨bottom, hlen, ?_⟩
    have hstack : PalPeg.ConcreteLocalMachine.backStack (rightViewOn v a rest) ++ bottom
        = a :: (PalPeg.ConcreteLocalMachine.backStack v ++ bottom) := rfl
    rw [hstack, hbackTape]
    exact stackTape_push (tapes PalPeg.ConcreteLocalMachine.backTape) a
      (PalPeg.ConcreteLocalMachine.backStack v ++ bottom) hst
  near := by
    obtain ⟨bottom, hsealed, hlen, hst⟩ := hrep.near
    refine ⟨bottom, hsealed, hlen, ?_⟩
    have hstack : (rightViewOn v a rest).near ++ bottom = rest ++ bottom := rfl
    rw [hstack, hnearTape]
    exact stackTape_pop (tapes PalPeg.ConcreteLocalMachine.nearTape) a (rest ++ bottom)
      (by
        have h := hst
        rw [hnear] at h
        simpa only [List.cons_append] using h)

/-- **a head's own step leaves the queue of pending arrivals alone**, so the queue's invariant
survives every step a head takes by itself.  A step left, a step right onto the near stack and a
half-step that moves only the head's bit all rebuild the zipper and copy `far` through. -/
theorem far_leftView (v : PalPeg.LocalInputView.InputView) : (leftView v).far = v.far := by
  unfold leftView
  split <;> rfl

theorem wf_leftView (v : PalPeg.LocalInputView.InputView) (hwf : PalPeg.LocalInputView.WF v) :
    PalPeg.LocalInputView.WF (leftView v) := by
  unfold PalPeg.LocalInputView.WF
  rw [far_leftView]
  exact hwf

theorem wf_rightViewOn (v : PalPeg.LocalInputView.InputView) (a : Option (Fin 2))
    (rest : List (Option (Fin 2))) (hwf : PalPeg.LocalInputView.WF v) :
    PalPeg.LocalInputView.WF (rightViewOn v a rest) := hwf

theorem wf_setGap (v : PalPeg.LocalInputView.InputView) (b : Bool)
    (hwf : PalPeg.LocalInputView.WF v) :
    PalPeg.LocalInputView.WF {v with gap := b} := hwf

/-- **a head's step right does not change what its view holds either.** -/
theorem cells_rightViewOn (v : PalPeg.LocalInputView.InputView) (a : Option (Fin 2))
    (rest : List (Option (Fin 2))) (hnear : v.near = a :: rest) :
    PalPeg.LocalInputView.cells (rightViewOn v a rest) = PalPeg.LocalInputView.cells v := by
  unfold PalPeg.LocalInputView.cells rightViewOn PalPeg.LocalInputView.absRight
  rw [hnear]
  simp [PalPeg.LocalInputView.farList]

theorem viewCells_rightViewOn (v : PalPeg.LocalInputView.InputView) (a : Option (Fin 2))
    (rest : List (Option (Fin 2))) (hnear : v.near = a :: rest)
    (hcells : PalPeg.LocalViewCells.ViewCells v) :
    PalPeg.LocalViewCells.ViewCells (rightViewOn v a rest) := by
  obtain ⟨letters, hletters⟩ := hcells
  exact ⟨letters, by rw [cells_rightViewOn v a rest hnear, hletters]⟩

/-- the twelve tapes of a view after its head steps right: two actions on the back stack, one on
the near stack, and the queue untouched. -/
noncomputable def rightViewTapes (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (a : Option (Fin 2)) : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc :=
  fun t =>
    if t = PalPeg.ConcreteLocalMachine.backTape then
      PalPeg.CloseoutCoreEnc12.actList PalPeg.CloseoutCoreStep.blankc
        (viewTapes PalPeg.ConcreteLocalMachine.backTape)
        [some ((viewTapes PalPeg.ConcreteLocalMachine.backTape).focus,
            (.right : PalPeg.CloseoutCoreEnc12.MoveC)),
          some (PalPeg.CloseoutCoreEnc.cellSym a,
            (.stay : PalPeg.CloseoutCoreEnc12.MoveC))]
    else if t = PalPeg.ConcreteLocalMachine.nearTape then
      PalPeg.CloseoutCoreEnc12.actOnG PalPeg.CloseoutCoreStep.blankc
        (viewTapes PalPeg.ConcreteLocalMachine.nearTape)
        (some (PalPeg.CloseoutCoreEnc.cellSym a,
          (.left : PalPeg.CloseoutCoreEnc12.MoveC)))
    else viewTapes t

theorem encCell_rightViewTapes_back (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (a : Option (Fin 2)) :
    mapTape encCell (rightViewTapes viewTapes a PalPeg.ConcreteLocalMachine.backTape)
      = PalPeg.CloseoutCoreEnc12.actList blankM
          (mapTape encCell (viewTapes PalPeg.ConcreteLocalMachine.backTape))
          [some ((mapTape encCell (viewTapes PalPeg.ConcreteLocalMachine.backTape)).focus,
              (.right : PalPeg.CloseoutCoreEnc12.MoveC)),
            some (encCell (PalPeg.CloseoutCoreEnc.cellSym a),
              (.stay : PalPeg.CloseoutCoreEnc12.MoveC))] := by
  unfold rightViewTapes
  rw [if_pos rfl]
  simp only [PalPeg.CloseoutCoreEnc12.actList, PalPeg.CloseoutCoreEnc12.actOnG]
  rw [mapTape_applyAction encCell rfl _ (PalPeg.CloseoutCoreEnc.cellSym a) .stay,
    mapTape_applyAction encCell rfl _
      (viewTapes PalPeg.ConcreteLocalMachine.backTape).focus .right]
  rfl

theorem encCell_rightViewTapes_near (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (a : Option (Fin 2)) :
    mapTape encCell (rightViewTapes viewTapes a PalPeg.ConcreteLocalMachine.nearTape)
      = PalPeg.CloseoutCoreEnc12.actOnG blankM
          (mapTape encCell (viewTapes PalPeg.ConcreteLocalMachine.nearTape))
          (some (encCell (PalPeg.CloseoutCoreEnc.cellSym a),
            (.left : PalPeg.CloseoutCoreEnc12.MoveC))) := by
  unfold rightViewTapes
  rw [if_neg (by decide), if_pos rfl]
  exact mapTape_applyAction encCell rfl _ _ _

theorem encCell_rightViewTapes_other (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (a : Option (Fin 2)) (t : Fin 12) (hback : t ≠ PalPeg.ConcreteLocalMachine.backTape)
    (hnear : t ≠ PalPeg.ConcreteLocalMachine.nearTape) :
    mapTape encCell (rightViewTapes viewTapes a t) = mapTape encCell (viewTapes t) := by
  unfold rightViewTapes
  rw [if_neg hback, if_neg hnear]

/-- **a head that stands on the gap beside a letter steps left for free.**  Only its own bit
moves; not one of its twelve tapes does. -/
theorem headRep_leftGap {margin : ℕ} {micro : PalPeg.ConcreteLocalMachine.MicroControl}
    (view : PalPeg.LocalInputView.InputView)
    (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (hgap : view.gap = true)
    (hrep : PalPeg.ConcreteLocalMachine.ViewRep margin view true micro viewTapes) :
    PalPeg.LocalArrival.absHead' {view with gap := false} []
        = PalPeg.GalilScaffoldInputHead.left (PalPeg.LocalArrival.absHead' view [])
      ∧ PalPeg.ConcreteLocalMachine.ViewRep margin {view with gap := false} false micro
          viewTapes := by
  refine ⟨?_, ?_⟩
  · simp [PalPeg.GalilScaffoldInputHead.left, PalPeg.LocalArrival.absHead', hgap]
  · exact
      { gap := rfl
        queue := hrep.queue
        back := hrep.back
        near := hrep.near }

/-- the twelve tapes of a view after its head steps left: one action on the back stack, two on
the near stack, and the queue untouched. -/
noncomputable def leftViewTapes (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (focus : Option (Fin 2)) : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc :=
  fun t =>
    if t = PalPeg.ConcreteLocalMachine.backTape then
      PalPeg.CloseoutCoreEnc12.actOnG PalPeg.CloseoutCoreStep.blankc
        (viewTapes PalPeg.ConcreteLocalMachine.backTape)
        (some (PalPeg.CloseoutCoreEnc.cellSym focus,
          (.left : PalPeg.CloseoutCoreEnc12.MoveC)))
    else if t = PalPeg.ConcreteLocalMachine.nearTape then
      PalPeg.CloseoutCoreEnc12.actList PalPeg.CloseoutCoreStep.blankc
        (viewTapes PalPeg.ConcreteLocalMachine.nearTape)
        [some ((viewTapes PalPeg.ConcreteLocalMachine.nearTape).focus,
            (.right : PalPeg.CloseoutCoreEnc12.MoveC)),
          some (PalPeg.CloseoutCoreEnc.cellSym focus,
            (.stay : PalPeg.CloseoutCoreEnc12.MoveC))]
    else viewTapes t

/-- **a head that stands on a letter steps left in one step**, and what the encoding asks for
afterwards is the view `leftView` names on the tapes `leftViewTapes` names. -/
theorem headRep_left {margin : ℕ} {micro : PalPeg.ConcreteLocalMachine.MicroControl}
    (view : PalPeg.LocalInputView.InputView)
    (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (a : Option (Fin 2)) (tail : List (Option (Fin 2))) (hback : view.back = a :: tail)
    (hgap : view.gap = false)
    (hrep : PalPeg.ConcreteLocalMachine.ViewRep margin view false micro viewTapes) :
    PalPeg.LocalArrival.absHead' (leftView view) []
        = PalPeg.GalilScaffoldInputHead.left (PalPeg.LocalArrival.absHead' view [])
      ∧ PalPeg.ConcreteLocalMachine.ViewRep margin (leftView view) true micro
          (leftViewTapes viewTapes view.focus) := by
  refine ⟨absHead_leftView view hgap a tail hback, ?_⟩
  refine viewRep_left view micro viewTapes (leftViewTapes viewTapes view.focus) a tail hback hrep
    ?_ ?_ ?_
  · unfold leftViewTapes
    rw [if_pos rfl]
  · unfold leftViewTapes
    rw [if_neg (by decide), if_pos rfl]
  · intro t hbackT hnearT
    unfold leftViewTapes
    rw [if_neg hbackT, if_neg hnearT]

/-! ### a head's step left, on the slots the whole machine carries

The twelve tapes of a view sit on the machine's own tapes under `mapTape encCell`, so the three
actions of the step have to be named in the machine's alphabet.  Each of them writes a symbol the
rule can read: the back stack's action writes back the symbol under its own head, and the near
stack's two write the symbol under the near head and then the one under the back head. -/

theorem encCell_leftViewTapes_back (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (focus : Option (Fin 2)) :
    mapTape encCell (leftViewTapes viewTapes focus PalPeg.ConcreteLocalMachine.backTape)
      = PalPeg.CloseoutCoreEnc12.actOnG blankM
          (mapTape encCell (viewTapes PalPeg.ConcreteLocalMachine.backTape))
          (some (encCell (PalPeg.CloseoutCoreEnc.cellSym focus),
            (.left : PalPeg.CloseoutCoreEnc12.MoveC))) := by
  unfold leftViewTapes
  rw [if_pos rfl]
  exact mapTape_applyAction encCell rfl _ _ _

theorem encCell_leftViewTapes_near (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (focus : Option (Fin 2)) :
    mapTape encCell (leftViewTapes viewTapes focus PalPeg.ConcreteLocalMachine.nearTape)
      = PalPeg.CloseoutCoreEnc12.actList blankM
          (mapTape encCell (viewTapes PalPeg.ConcreteLocalMachine.nearTape))
          [some ((mapTape encCell (viewTapes PalPeg.ConcreteLocalMachine.nearTape)).focus,
              (.right : PalPeg.CloseoutCoreEnc12.MoveC)),
            some (encCell (PalPeg.CloseoutCoreEnc.cellSym focus),
              (.stay : PalPeg.CloseoutCoreEnc12.MoveC))] := by
  unfold leftViewTapes
  rw [if_neg (by decide), if_pos rfl]
  simp only [PalPeg.CloseoutCoreEnc12.actList, PalPeg.CloseoutCoreEnc12.actOnG]
  rw [mapTape_applyAction encCell rfl _ (PalPeg.CloseoutCoreEnc.cellSym focus) .stay,
    mapTape_applyAction encCell rfl _
      (viewTapes PalPeg.ConcreteLocalMachine.nearTape).focus .right]
  rfl

theorem encCell_leftViewTapes_other (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (focus : Option (Fin 2)) (t : Fin 12) (hback : t ≠ PalPeg.ConcreteLocalMachine.backTape)
    (hnear : t ≠ PalPeg.ConcreteLocalMachine.nearTape) :
    mapTape encCell (leftViewTapes viewTapes focus t) = mapTape encCell (viewTapes t) := by
  unfold leftViewTapes
  rw [if_neg hback, if_neg hnear]

/-- **a head's step left, on the slots of the whole machine.**  The three actions name only
symbols the rule reads off its own windows — the symbol under the back head and the one under
the near head — and what comes out is a view of the head one step left, on tapes the encoding
accepts. -/
theorem headSlots_left {margin : ℕ} {polarity : Fin 16 → Bool} {gap : Fin 4 → Bool}
    {micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl} {fppLive dpLive : Bool}
    {x : State GalilVM} {tapes : Slot → STape Γm}
    (henc : EncTapes margin x polarity gap micro fppLive dpLive tapes)
    (v : Fin 4) (head : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hhead : headOf x v = some head) (hgap : head.gap = false)
    (a : Option (Fin 2)) (tail : List (Option (Fin 2)))
    (hleft : head.head.left = a :: tail)
    (newTapes : Slot → STape Γm)
    (hbackSlot : newTapes (headSlot v PalPeg.ConcreteLocalMachine.backTape)
      = PalPeg.CloseoutCoreEnc12.actOnG blankM
          (tapes (headSlot v PalPeg.ConcreteLocalMachine.backTape))
          (some ((tapes (headSlot v PalPeg.ConcreteLocalMachine.backTape)).focus,
            (.left : PalPeg.CloseoutCoreEnc12.MoveC))))
    (hnearSlot : newTapes (headSlot v PalPeg.ConcreteLocalMachine.nearTape)
      = PalPeg.CloseoutCoreEnc12.actList blankM
          (tapes (headSlot v PalPeg.ConcreteLocalMachine.nearTape))
          [some ((tapes (headSlot v PalPeg.ConcreteLocalMachine.nearTape)).focus,
              (.right : PalPeg.CloseoutCoreEnc12.MoveC)),
            some ((tapes (headSlot v PalPeg.ConcreteLocalMachine.backTape)).focus,
              (.stay : PalPeg.CloseoutCoreEnc12.MoveC))])
    (hotherSlot : ∀ i, i ≠ PalPeg.ConcreteLocalMachine.backTape →
      i ≠ PalPeg.ConcreteLocalMachine.nearTape →
      newTapes (headSlot v i) = tapes (headSlot v i)) :
    ∃ (view : PalPeg.LocalInputView.InputView) (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc),
      PalPeg.LocalArrival.absHead' view []
          = PalPeg.GalilScaffoldInputHead.left head ∧
        PalPeg.ConcreteLocalMachine.ViewRep margin view true (micro v) viewTapes ∧
        (∀ i, newTapes (headSlot v i) = mapTape encCell (viewTapes i)) ∧
          PalPeg.LocalViewCells.ViewCells view ∧ PalPeg.LocalInputView.WF view := by
  obtain ⟨view, viewTapes, habs, hrep, hold, hviewCells⟩ := henc.heads v head hhead
  have hviewGap : view.gap = false := by
    have : (PalPeg.LocalArrival.absHead' view []).gap = head.gap := by rw [habs]
    rw [← hgap]
    exact this
  have hviewBack : view.back = a :: tail := by
    have : (PalPeg.LocalArrival.absHead' view []).head.left = head.head.left := by rw [habs]
    rw [← hleft]
    exact this
  have hgapBit : gap v = false := by rw [hrep.gap, hviewGap]
  have hrep' : PalPeg.ConcreteLocalMachine.ViewRep margin view false (micro v) viewTapes := by
    rw [← hgapBit]
    exact hrep
  obtain ⟨habs', hrep''⟩ := headRep_left view viewTapes a tail hviewBack hviewGap hrep'
  have hbackFocus : (viewTapes PalPeg.ConcreteLocalMachine.backTape).focus
      = PalPeg.CloseoutCoreEnc.cellSym view.focus := by
    obtain ⟨bottom, -, hst⟩ := hrep'.back
    have hstack : PalPeg.ConcreteLocalMachine.backStack view ++ bottom
        = view.focus :: (view.back ++ bottom) := rfl
    rw [hstack] at hst
    rw [stackTape_focus _ _ hst]
    rfl
  have hmapFocus : (mapTape encCell (viewTapes PalPeg.ConcreteLocalMachine.backTape)).focus
      = encCell (PalPeg.CloseoutCoreEnc.cellSym view.focus) := by
    show encCell (viewTapes PalPeg.ConcreteLocalMachine.backTape).focus = _
    rw [hbackFocus]
  refine ⟨leftView view, leftViewTapes viewTapes view.focus, habs.symm ▸ habs', hrep'', ?_,
    viewCells_leftView view a tail hviewBack hviewCells.1, wf_leftView view hviewCells.2⟩
  intro i
  by_cases hb : i = PalPeg.ConcreteLocalMachine.backTape
  · subst hb
    rw [hbackSlot, encCell_leftViewTapes_back, hold PalPeg.ConcreteLocalMachine.backTape,
      hmapFocus]
  · by_cases hn : i = PalPeg.ConcreteLocalMachine.nearTape
    · subst hn
      rw [hnearSlot, encCell_leftViewTapes_near, hold PalPeg.ConcreteLocalMachine.nearTape,
        hold PalPeg.ConcreteLocalMachine.backTape, hmapFocus]
    · rw [hotherSlot i hb hn, encCell_leftViewTapes_other viewTapes view.focus i hb hn, hold i]

/-- **a head has one cell behind it exactly when that cell is the sentinel.**  A view holds the
left sentinel and then letters, so the only cell of a view that is not a letter is the one at its
left end — and the head has one cell behind it exactly when the cell behind it is that one. -/
theorem back_singleton_iff_sentinel (v : PalPeg.LocalInputView.InputView)
    (hcells : PalPeg.LocalViewCells.ViewCells v) (c : Option (Fin 2))
    (rest : List (Option (Fin 2))) (hback : v.back = c :: rest) :
    rest = [] ↔ c = none := by
  obtain ⟨letters, hletters⟩ := hcells
  constructor
  · intro hrest
    have hcells' : PalPeg.LocalInputView.cells v
        = c :: (v.focus :: PalPeg.LocalInputView.absRight v) := by
      unfold PalPeg.LocalInputView.cells
      rw [hback, hrest]
      rfl
    rw [hcells'] at hletters
    exact (List.cons.inj hletters).1
  · intro hc
    by_contra hne
    obtain ⟨e, es, hes⟩ : ∃ e es, rest.reverse = e :: es := by
      cases hrev : rest.reverse with
      | nil => exact absurd (by simpa using congrArg List.reverse hrev) hne
      | cons e es => exact ⟨e, es, rfl⟩
    have hcells' : PalPeg.LocalInputView.cells v
        = e :: (es ++ c :: (v.focus :: PalPeg.LocalInputView.absRight v)) := by
      unfold PalPeg.LocalInputView.cells
      rw [hback]
      show (c :: rest).reverse ++ _ = _
      rw [List.reverse_cons, hes]
      simp
    rw [hcells'] at hletters
    have htail : es ++ c :: (v.focus :: PalPeg.LocalInputView.absRight v)
        = letters.map some := (List.cons.inj hletters).2
    have hmem : c ∈ letters.map some := by
      rw [← htail]
      simp
    rw [hc] at hmem
    simp at hmem

/-- **after a head steps left it stands on the first letter exactly when it was on the gap
beside it with one cell behind.**  A head on a letter steps onto the gap, and a gap is at an
even coordinate, so it is never the first letter; a head on a gap steps back onto the letter it
just left, and that is the first one exactly when there is a single cell behind the head. -/
theorem leftFirst_after_left (p : PalPeg.GalilScaffoldInputHead.PlaceHead) :
    PalPeg.GalilScaffoldChainInputSupply.position
        (PalPeg.GalilScaffoldInputHead.left p) = 1
      ↔ (p.gap = true ∧ p.head.left.length = 1) := by
  unfold PalPeg.GalilScaffoldInputHead.left PalPeg.GalilScaffoldChainInputSupply.position
  cases hgap : p.gap
  · simp only [Bool.false_eq_true, if_false, Bool.not_false, if_true, false_and, iff_false]
    cases hleft : p.head.left with
    | nil =>
      show ¬ (2 * (PalPeg.GalilScaffoldInputHead.moveLeft p.head).left.length = 1)
      unfold PalPeg.GalilScaffoldInputHead.moveLeft
      rw [hleft]
      simp
    | cons b rest =>
      show ¬ (2 * (PalPeg.GalilScaffoldInputHead.moveLeft p.head).left.length = 1)
      unfold PalPeg.GalilScaffoldInputHead.moveLeft
      rw [hleft]
      simp
  · simp only [if_true, Bool.not_true, Bool.false_eq_true, if_false, true_and]
    show 2 * p.head.left.length - 1 = 1 ↔ _
    omega

/-- **the sign a counter takes after one increment.**  A counter tape holds the absolute value,
so an increment pushes while the sign is positive and pops while it is negative; at zero on the
negative side the push turns the sign around, and that is the one case where the bit moves. -/
noncomputable def incSignAt {K : ℕ} (bit : Bool) (slot : Slot)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) : Bool :=
  bit || decide (belowRead ws slot ≠ encSeg PalPeg.LocalCounter.mark)

/-- **the action an increment names, on whichever tape carries the counter.**  A mirror carries
its source's value with its source's sign, so the mirror is incremented by this same action read
off the mirror's own window — which is what `counter_inc_at` is stated for. -/
noncomputable def incActAt {K : ℕ} (bit : Bool) (slot : Slot)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) : PalPeg.CloseoutCoreEnc12.Act Γm :=
  if incSignAt bit slot ws then
    some (encSeg PalPeg.LocalCounter.mark, (.right : PalPeg.CloseoutCoreEnc12.MoveC))
  else some (blankM, (.left : PalPeg.CloseoutCoreEnc12.MoveC))

noncomputable def incSign {K : ℕ} (polarity : Fin 16 → Bool) (c : Fin 16)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) : Bool :=
  incSignAt (polarity c) (counterSlot c) ws

/-- **the control table of one step of the rewind.**  The controller's pair bit is set, the
head's own gap bit flips, the sign of the length counter follows the increment, and the bit for
the first letter is the three readings `leftFirst_after_step_iff` names. -/
noncomputable def rewindOneNext {fppBound dpBound K : ℕ} (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) : QPhys fppBound dpBound :=
  {q with ctl := {q.ctl with pair := true}, leftFirstBit := q.gap 0 && decide (centreRead ws (headSlot 0 PalPeg.ConcreteLocalMachine.backTape) ≠ encCell (PalPeg.CloseoutCoreEnc.cellSym none)) && decide (belowRead ws (headSlot 0 PalPeg.ConcreteLocalMachine.backTape) = encCell (PalPeg.CloseoutCoreEnc.cellSym none)), polarity := Function.update q.polarity 3 (incSign q.polarity 3 ws), gap := Function.update q.gap 0 (!q.gap 0)}

/-- the action a counter's increment names, on whichever tape carries the value. -/
noncomputable def incAct {fppBound dpBound K : ℕ} (q : QPhys fppBound dpBound) (c : Fin 16)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) : PalPeg.CloseoutCoreEnc12.Act Γm :=
  incActAt (q.polarity c) (counterSlot c) ws

/-- **a counter and its mirror take the same action.**  The mirror's own window supplies the
frontier and the control supplies the source's sign, so nothing about the mirror has to be said
twice. -/
theorem incAct_eq_incActAt {fppBound dpBound K : ℕ} (q : QPhys fppBound dpBound) (c : Fin 16)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) :
    incAct q c ws = incActAt (q.polarity c) (counterSlot c) ws := rfl

/-- the actions one head's step left names on that head's own two stacks. -/
noncomputable def headStepActs {fppBound dpBound K : ℕ} (q : QPhys fppBound dpBound) (v : Fin 4)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (t : Fin 12) :
    List (PalPeg.CloseoutCoreEnc12.Act Γm) :=
  if q.gap v
      || decide (centreRead ws (headSlot v PalPeg.ConcreteLocalMachine.backTape)
          = encCell (PalPeg.CloseoutCoreEnc.cellSym none)) then []
    else if t = PalPeg.ConcreteLocalMachine.backTape then
      [some (centreRead ws (headSlot v PalPeg.ConcreteLocalMachine.backTape),
        (.left : PalPeg.CloseoutCoreEnc12.MoveC))]
    else if t = PalPeg.ConcreteLocalMachine.nearTape then
      [some (centreRead ws (headSlot v PalPeg.ConcreteLocalMachine.nearTape),
          (.right : PalPeg.CloseoutCoreEnc12.MoveC)),
        some (centreRead ws (headSlot v PalPeg.ConcreteLocalMachine.backTape),
          (.stay : PalPeg.CloseoutCoreEnc12.MoveC))]
    else []

theorem headStepActs_length {fppBound dpBound K : ℕ} (q : QPhys fppBound dpBound) (v : Fin 4)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (t : Fin 12) :
    (headStepActs q v ws t).length ≤ 2 := by
  unfold headStepActs
  split_ifs <;> simp

/-- **the action table of one step of the rewind.**  The marks tape steps left, the length
counter is incremented, and the left head takes its own step — which is nothing at all unless it
stands on a letter with something behind it. -/
noncomputable def rewindOneActs {fppBound dpBound K : ℕ} (live : Bool) (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) :
    Fin tapeCountM → List (PalPeg.CloseoutCoreEnc12.Act Γm) :=
  fun j =>
    if j = slotIndex (progSlot live 8) then
      [some (centreRead ws (progSlot live 8), (.left : PalPeg.CloseoutCoreEnc12.MoveC))]
    else if j = slotIndex (counterSlot 3) then [incAct q 3 ws]
    else if ∃ m : Fin 7, mirrorSource m = 3 ∧ j = slotIndex (mirrorSlot m) then [incAct q 3 ws]
    else if j = slotIndex (headSlot 0 PalPeg.ConcreteLocalMachine.backTape) then
      headStepActs q 0 ws PalPeg.ConcreteLocalMachine.backTape
    else if j = slotIndex (headSlot 0 PalPeg.ConcreteLocalMachine.nearTape) then
      headStepActs q 0 ws PalPeg.ConcreteLocalMachine.nearTape
    else []

theorem headSlot_ne_of_tape_ne (v : Fin 4) (t t' : Fin 12) (h : t ≠ t') :
    slotIndex (headSlot v t) ≠ slotIndex (headSlot v t') := by
  intro hEq
  have hpair : v = v ∧ t = t' := by simpa [headSlot] using slotIndex.injective hEq
  exact h hpair.2

theorem rewindOneActs_prog {fppBound dpBound K : ℕ} (live : Bool) (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) :
    rewindOneActs live q ws (slotIndex (progSlot live 8))
      = [some (centreRead ws (progSlot live 8), (.left : PalPeg.CloseoutCoreEnc12.MoveC))] := by
  unfold rewindOneActs
  rw [if_pos rfl]

theorem rewindOneActs_counter {fppBound dpBound K : ℕ} (live : Bool) (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) :
    rewindOneActs live q ws (slotIndex (counterSlot 3)) = [incAct q 3 ws] := by
  unfold rewindOneActs
  rw [if_neg (fun h => (progSlot_ne_counterSlot live 8 3) (slotIndex.injective h).symm),
    if_pos rfl]

/-- **and so does the length's mirror.**  A mirror carries its source's value, so the step that
increments the length increments the mirror by the same action. -/
theorem rewindOneActs_mirror {fppBound dpBound K : ℕ} (live : Bool) (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (m : Fin 7) (hsrc : mirrorSource m = 3) :
    rewindOneActs live q ws (slotIndex (mirrorSlot m)) = [incAct q 3 ws] := by
  unfold rewindOneActs
  rw [if_neg (fun h => (progSlot_ne_mirrorSlot live 8 m) (slotIndex.injective h).symm),
    if_neg (fun h => (counterSlot_ne_mirrorSlot 3 m) (slotIndex.injective h).symm),
    if_pos ⟨m, hsrc, rfl⟩]

theorem rewindOneActs_head {fppBound dpBound K : ℕ} (live : Bool) (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (t : Fin 12) :
    rewindOneActs live q ws (slotIndex (headSlot 0 t)) = headStepActs q 0 ws t := by
  unfold rewindOneActs
  rw [if_neg (fun h => (progSlot_ne_headSlot live 8 0 t) (slotIndex.injective h).symm),
    if_neg (fun h => (counterSlot_ne_headSlot 3 0 t) (slotIndex.injective h).symm),
    if_neg (fun h => by
      obtain ⟨m, -, hEq⟩ := h
      exact (headSlot_ne_mirrorSlot 0 t m) (slotIndex.injective hEq))]
  by_cases hb : t = PalPeg.ConcreteLocalMachine.backTape
  · subst hb
    rw [if_pos rfl]
  · rw [if_neg (headSlot_ne_of_tape_ne 0 t PalPeg.ConcreteLocalMachine.backTape hb)]
    by_cases hn : t = PalPeg.ConcreteLocalMachine.nearTape
    · subst hn
      rw [if_pos rfl]
    · rw [if_neg (headSlot_ne_of_tape_ne 0 t PalPeg.ConcreteLocalMachine.nearTape hn)]
      simp [headStepActs, hb, hn]

theorem rewindOneActs_progOther {fppBound dpBound K : ℕ} (live : Bool)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (j : Fin 9) (hj : j ≠ 8) :
    rewindOneActs live q ws (slotIndex (progSlot live j)) = [] := by
  unfold rewindOneActs
  rw [if_neg (fun h => hj (progSlotOf_injective live (slotIndex.injective h))),
    if_neg (fun h => (progSlot_ne_counterSlot live j 3) (slotIndex.injective h)),
    if_neg (fun h => by
      obtain ⟨m, -, hEq⟩ := h
      exact (progSlot_ne_mirrorSlot live j m) (slotIndex.injective hEq)),
    if_neg (fun h => (progSlot_ne_headSlot live j 0 _) (slotIndex.injective h)),
    if_neg (fun h => (progSlot_ne_headSlot live j 0 _) (slotIndex.injective h))]

theorem rewindOneActs_off {fppBound dpBound K : ℕ} (live : Bool) (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (slot : Slot)
    (hprog : ∀ j : Fin 9, slot ≠ progSlot live j) (hcounter : slot ≠ counterSlot 3)
    (hmirrorLen : ∀ m : Fin 7, mirrorSource m = 3 → slot ≠ mirrorSlot m)
    (hhead : ∀ t : Fin 12, slot ≠ headSlot 0 t) :
    rewindOneActs live q ws (slotIndex slot) = [] := by
  unfold rewindOneActs
  rw [if_neg (fun h => hprog 8 (slotIndex.injective h)),
    if_neg (fun h => hcounter (slotIndex.injective h)),
    if_neg (fun h => by
      obtain ⟨m, hsrc, hEq⟩ := h
      exact hmirrorLen m hsrc (slotIndex.injective hEq)),
    if_neg (fun h => hhead _ (slotIndex.injective h)),
    if_neg (fun h => hhead _ (slotIndex.injective h))]

/-- **the control table of the rewind's paired step.**  Both heads' bits flip, both counters'
signs follow their increments, and the bit for the first letter is about the left head. -/
noncomputable def rewindPairNext {fppBound dpBound K : ℕ} (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) : QPhys fppBound dpBound :=
  {q with ctl := {q.ctl with pair := false}, leftFirstBit := q.gap 0 && decide (centreRead ws (headSlot 0 PalPeg.ConcreteLocalMachine.backTape) ≠ encCell (PalPeg.CloseoutCoreEnc.cellSym none)) && decide (belowRead ws (headSlot 0 PalPeg.ConcreteLocalMachine.backTape) = encCell (PalPeg.CloseoutCoreEnc.cellSym none)), polarity := Function.update (Function.update q.polarity 3 (incSign q.polarity 3 ws)) 2 (incSign q.polarity 2 ws), gap := Function.update (Function.update q.gap 0 (!q.gap 0)) 1 (!q.gap 1)}

/-- **the action table of the rewind's paired step.**  The marks tape, the two counters with the
radius's three mirrors, and the two heads' stacks. -/
noncomputable def rewindPairActs {fppBound dpBound K : ℕ} (live : Bool)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) :
    Fin tapeCountM → List (PalPeg.CloseoutCoreEnc12.Act Γm) :=
  fun j =>
    if j = slotIndex (progSlot live 8) then
      [some (centreRead ws (progSlot live 8), (.left : PalPeg.CloseoutCoreEnc12.MoveC))]
    else if j = slotIndex (counterSlot 3) then [incAct q 3 ws]
    else if ∃ m : Fin 7, mirrorSource m = 3 ∧ j = slotIndex (mirrorSlot m) then [incAct q 3 ws]
    else if j = slotIndex (counterSlot 2) then [incAct q 2 ws]
    else if ∃ m : Fin 7, mirrorSource m = 2 ∧ j = slotIndex (mirrorSlot m) then [incAct q 2 ws]
    else if j = slotIndex (headSlot 0 PalPeg.ConcreteLocalMachine.backTape) then
      headStepActs q 0 ws PalPeg.ConcreteLocalMachine.backTape
    else if j = slotIndex (headSlot 0 PalPeg.ConcreteLocalMachine.nearTape) then
      headStepActs q 0 ws PalPeg.ConcreteLocalMachine.nearTape
    else if j = slotIndex (headSlot 1 PalPeg.ConcreteLocalMachine.backTape) then
      headStepActs q 1 ws PalPeg.ConcreteLocalMachine.backTape
    else if j = slotIndex (headSlot 1 PalPeg.ConcreteLocalMachine.nearTape) then
      headStepActs q 1 ws PalPeg.ConcreteLocalMachine.nearTape
    else []

theorem rewindPairActs_prog {fppBound dpBound K : ℕ} (live : Bool)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) :
    rewindPairActs live q ws (slotIndex (progSlot live 8))
      = [some (centreRead ws (progSlot live 8), (.left : PalPeg.CloseoutCoreEnc12.MoveC))] := by
  unfold rewindPairActs
  rw [if_pos rfl]

theorem rewindPairActs_counterLen {fppBound dpBound K : ℕ} (live : Bool)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) :
    rewindPairActs live q ws (slotIndex (counterSlot 3)) = [incAct q 3 ws] := by
  unfold rewindPairActs
  rw [if_neg (fun h => (progSlot_ne_counterSlot live 8 3) (slotIndex.injective h).symm),
    if_pos rfl]

/-- **the length's mirror, in the paired step.**  It moves with the length, by the same action. -/
theorem rewindPairActs_mirrorLen {fppBound dpBound K : ℕ} (live : Bool)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (m : Fin 7) (hsrc : mirrorSource m = 3) :
    rewindPairActs live q ws (slotIndex (mirrorSlot m)) = [incAct q 3 ws] := by
  unfold rewindPairActs
  rw [if_neg (fun h => (progSlot_ne_mirrorSlot live 8 m) (slotIndex.injective h).symm),
    if_neg (fun h => (counterSlot_ne_mirrorSlot 3 m) (slotIndex.injective h).symm),
    if_pos ⟨m, hsrc, rfl⟩]

theorem rewindPairActs_counterRad {fppBound dpBound K : ℕ} (live : Bool)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) :
    rewindPairActs live q ws (slotIndex (counterSlot 2)) = [incAct q 2 ws] := by
  unfold rewindPairActs
  rw [if_neg (fun h => (progSlot_ne_counterSlot live 8 2) (slotIndex.injective h).symm),
    if_neg (fun h => by simpa using slotIndex.injective h),
    if_neg (fun h => by
      obtain ⟨m, -, hEq⟩ := h
      exact (counterSlot_ne_mirrorSlot 2 m) (slotIndex.injective hEq)),
    if_pos rfl]

theorem rewindPairActs_mirror {fppBound dpBound K : ℕ} (live : Bool)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (m : Fin 7) (hsrc : mirrorSource m = 2) :
    rewindPairActs live q ws (slotIndex (mirrorSlot m)) = [incAct q 2 ws] := by
  unfold rewindPairActs
  rw [if_neg (fun h => (progSlot_ne_mirrorSlot live 8 m) (slotIndex.injective h).symm),
    if_neg (fun h => (counterSlot_ne_mirrorSlot 3 m) (slotIndex.injective h).symm),
    if_neg (fun h => by
      obtain ⟨m', hsrc', hEq⟩ := h
      have hmm : m' = m := (by simpa [mirrorSlot] using slotIndex.injective hEq : m = m').symm
      rw [hmm, hsrc] at hsrc'
      exact absurd hsrc' (by decide)),
    if_neg (fun h => (counterSlot_ne_mirrorSlot 2 m) (slotIndex.injective h).symm),
    if_pos ⟨m, hsrc, rfl⟩]

theorem rewindPairActs_head {fppBound dpBound K : ℕ} (live : Bool)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (v : Fin 4) (hv : v = 0 ∨ v = 1) (t : Fin 12) :
    rewindPairActs live q ws (slotIndex (headSlot v t)) = headStepActs q v ws t := by
  unfold rewindPairActs
  rw [if_neg (fun h => (progSlot_ne_headSlot live 8 v t) (slotIndex.injective h).symm),
    if_neg (fun h => (counterSlot_ne_headSlot 3 v t) (slotIndex.injective h).symm),
    if_neg (fun h => by
      obtain ⟨m, -, hEq⟩ := h
      exact (headSlot_ne_mirrorSlot v t m) (slotIndex.injective hEq)),
    if_neg (fun h => (counterSlot_ne_headSlot 2 v t) (slotIndex.injective h).symm),
    if_neg (fun h => by
      obtain ⟨m, -, hEq⟩ := h
      exact (headSlot_ne_mirrorSlot v t m) (slotIndex.injective hEq))]
  rcases hv with hv | hv
  · subst hv
    by_cases hb : t = PalPeg.ConcreteLocalMachine.backTape
    · subst hb
      rw [if_pos rfl]
    · rw [if_neg (headSlot_ne_of_tape_ne 0 t PalPeg.ConcreteLocalMachine.backTape hb)]
      by_cases hn : t = PalPeg.ConcreteLocalMachine.nearTape
      · subst hn
        rw [if_pos rfl]
      · rw [if_neg (headSlot_ne_of_tape_ne 0 t PalPeg.ConcreteLocalMachine.nearTape hn),
          if_neg (fun h => (headSlot_ne_of_head_ne 0 1 t _ (by decide))
            (slotIndex.injective h)),
          if_neg (fun h => (headSlot_ne_of_head_ne 0 1 t _ (by decide))
            (slotIndex.injective h))]
        simp [headStepActs, hb, hn]
  · subst hv
    rw [if_neg (fun h => (headSlot_ne_of_head_ne 1 0 t _ (by decide)) (slotIndex.injective h)),
      if_neg (fun h => (headSlot_ne_of_head_ne 1 0 t _ (by decide)) (slotIndex.injective h))]
    by_cases hb : t = PalPeg.ConcreteLocalMachine.backTape
    · subst hb
      rw [if_pos rfl]
    · rw [if_neg (headSlot_ne_of_tape_ne 1 t PalPeg.ConcreteLocalMachine.backTape hb)]
      by_cases hn : t = PalPeg.ConcreteLocalMachine.nearTape
      · subst hn
        rw [if_pos rfl]
      · rw [if_neg (headSlot_ne_of_tape_ne 1 t PalPeg.ConcreteLocalMachine.nearTape hn)]
        simp [headStepActs, hb, hn]

theorem rewindPairActs_progOther {fppBound dpBound K : ℕ} (live : Bool)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (j : Fin 9) (hj : j ≠ 8) :
    rewindPairActs live q ws (slotIndex (progSlot live j)) = [] := by
  unfold rewindPairActs
  rw [if_neg (fun h => hj (progSlotOf_injective live (slotIndex.injective h))),
    if_neg (fun h => (progSlot_ne_counterSlot live j 3) (slotIndex.injective h)),
    if_neg (fun h => by
      obtain ⟨m, -, hEq⟩ := h
      exact (progSlot_ne_mirrorSlot live j m) (slotIndex.injective hEq)),
    if_neg (fun h => (progSlot_ne_counterSlot live j 2) (slotIndex.injective h)),
    if_neg (fun h => by
      obtain ⟨m, -, hEq⟩ := h
      exact (progSlot_ne_mirrorSlot live j m) (slotIndex.injective hEq)),
    if_neg (fun h => (progSlot_ne_headSlot live j 0 _) (slotIndex.injective h)),
    if_neg (fun h => (progSlot_ne_headSlot live j 0 _) (slotIndex.injective h)),
    if_neg (fun h => (progSlot_ne_headSlot live j 1 _) (slotIndex.injective h)),
    if_neg (fun h => (progSlot_ne_headSlot live j 1 _) (slotIndex.injective h))]

theorem rewindPairActs_off {fppBound dpBound K : ℕ} (live : Bool) (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (slot : Slot)
    (hprog : ∀ j : Fin 9, slot ≠ progSlot live j) (hlen : slot ≠ counterSlot 3)
    (hrad : slot ≠ counterSlot 2)
    (hmirrorLen : ∀ m : Fin 7, mirrorSource m = 3 → slot ≠ mirrorSlot m)
    (hmirror : ∀ m : Fin 7, mirrorSource m = 2 → slot ≠ mirrorSlot m)
    (hhead0 : ∀ t : Fin 12, slot ≠ headSlot 0 t) (hhead1 : ∀ t : Fin 12, slot ≠ headSlot 1 t) :
    rewindPairActs live q ws (slotIndex slot) = [] := by
  unfold rewindPairActs
  rw [if_neg (fun h => hprog 8 (slotIndex.injective h)),
    if_neg (fun h => hlen (slotIndex.injective h)),
    if_neg (fun h => by
      obtain ⟨m, hsrc, hEq⟩ := h
      exact hmirrorLen m hsrc (slotIndex.injective hEq)),
    if_neg (fun h => hrad (slotIndex.injective h)),
    if_neg (fun h => by
      obtain ⟨m, hsrc, hEq⟩ := h
      exact hmirror m hsrc (slotIndex.injective hEq)),
    if_neg (fun h => hhead0 _ (slotIndex.injective h)),
    if_neg (fun h => hhead0 _ (slotIndex.injective h)),
    if_neg (fun h => hhead1 _ (slotIndex.injective h)),
    if_neg (fun h => hhead1 _ (slotIndex.injective h))]

theorem rewindPairActs_length {fppBound dpBound K : ℕ} (live : Bool)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (j : Fin tapeCountM) : (rewindPairActs live q ws j).length ≤ 2 := by
  unfold rewindPairActs
  split_ifs <;> first | simp | exact headStepActs_length q _ ws _

theorem rewindOneActs_length {fppBound dpBound K : ℕ} (live : Bool) (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (j : Fin tapeCountM) :
    (rewindOneActs live q ws j).length ≤ 2 := by
  unfold rewindOneActs
  split_ifs <;> first | exact headStepActs_length q 0 ws _ | simp

/-- the tick function's own name for the paired step of the rewind. -/
theorem frameFun_rewindPair (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (s : GalilVM) :
    (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).rewindPair s
      = {s with fpp := PalPeg.GalilScaffoldChainInputSupply.markStep s.fpp PalPeg.GalilScaffoldTape.moveLeft, left := PalPeg.GalilScaffoldInputHead.left s.left, length := PalPeg.GalilScaffoldCounter.inc s.length, center := PalPeg.GalilScaffoldInputHead.left s.center, radius := PalPeg.GalilScaffoldCounter.inc s.radius} := rfl

/-- the tick function's own name for one step of the rewind. -/
theorem frameFun_rewindOne (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (s : GalilVM) :
    (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).rewindOne s
      = {s with fpp := PalPeg.GalilScaffoldChainInputSupply.markStep s.fpp PalPeg.GalilScaffoldTape.moveLeft, left := PalPeg.GalilScaffoldInputHead.left s.left, length := PalPeg.GalilScaffoldCounter.inc s.length} := rfl

/-- **one step of the rewind, on the whole state.**  The marks tape steps left, the left input
head steps left and the length counter counts the step.  The head's new view is the caller's to
supply; what this lemma does is put the three together and keep the finite control honest. -/
theorem rewind_one {fppBound dpBound : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (tapes newTapes : Slot → STape Γm)
    (newPolarity : Fin 16 → Bool) (newGap : Fin 4 → Bool) (bit : Bool)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind)
    (hnotFirst : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).atFirst x.vm
      = false)
    (hpair : x.ctl.pair = false)
    (hbit : bit = decide (PalPeg.GalilScaffoldChainInputSupply.position
      (PalPeg.GalilScaffoldInputHead.left x.vm.left) = 1))
    (henc : Enc w margin x (q, tapes))
    (hheads : ∃ (view : PalPeg.LocalInputView.InputView)
        (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc),
      PalPeg.LocalArrival.absHead' view []
          = PalPeg.GalilScaffoldInputHead.left x.vm.left ∧
        PalPeg.ConcreteLocalMachine.ViewRep margin view (newGap 0) (q.micro 0) viewTapes ∧
        (∀ i, newTapes (headSlot 0 i) = mapTape encCell (viewTapes i)) ∧
          PalPeg.LocalViewCells.ViewCells view ∧ PalPeg.LocalInputView.WF view)
    (hgapOther : ∀ v : Fin 4, v ≠ 0 → newGap v = q.gap v)
    (hpolarity : ∀ c : Fin 16, c ≠ 3 → newPolarity c = q.polarity c)
    (segments : STape Seg)
    (hlength : absCtr segments (newPolarity 3)
      = PalPeg.GalilScaffoldCounter.inc x.vm.length)
    (hcounterTape : newTapes (counterSlot 3) = padLeft margin (mapTape encSeg segments))
    (hmirrorLen : ∀ m : Fin 7, mirrorSource m = 3 → ∃ seg : STape Seg,
      absCtr seg (newPolarity 3) = PalPeg.GalilScaffoldCounter.inc x.vm.length
        ∧ newTapes (mirrorSlot m) = padLeft margin (mapTape encSeg seg))
    (hprog : newTapes (progSlotOf q.fppLive 8)
      = padLeft margin (mapTape encProg (encTape
          (PalPeg.GalilScaffoldTape.moveLeft (x.vm.fpp.program.config.tapes 8)))))
    (hprogOther : ∀ j : Fin 9, j ≠ 8 →
      newTapes (progSlotOf q.fppLive j) = tapes (progSlotOf q.fppLive j))
    (hkept : ∀ slot, (∀ j : Fin 9, slot ≠ progSlotOf q.fppLive j) → slot ≠ counterSlot 3 →
      (∀ m : Fin 7, mirrorSource m = 3 → slot ≠ mirrorSlot m) →
      (∀ i : Fin 12, slot ≠ headSlot 0 i) →
      (∀ k : Fin 9, slot ≠ progSlotOf (!q.fppLive) k) → newTapes slot = tapes slot)
    (hmarginHead : ∀ i : Fin 12, margin ≤ PalPeg.Local.pos (newTapes (headSlot 0 i)))
    (hidleShape : ∀ k : Fin 9, ∃ raw : STape (Fin 9),
      newTapes (progSlotOf (!q.fppLive) k) = padLeft margin (mapTape encProg raw)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ({q with ctl := {q.ctl with pair := true}, leftFirstBit := bit, polarity := newPolarity, gap := newGap}, newTapes) := by
  have hval : PalPeg.GalilScaffoldTop.tickFun
      (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x
      = ⟨{x.ctl with pair := true}, {x.vm with fpp := PalPeg.GalilScaffoldChainInputSupply.markStep x.vm.fpp PalPeg.GalilScaffoldTape.moveLeft, left := PalPeg.GalilScaffoldInputHead.left x.vm.left, length := PalPeg.GalilScaffoldCounter.inc x.vm.length}⟩ := by
    simp only [PalPeg.GalilScaffoldTop.tickFun, hmode, frameFun_rewindOne]
    rw [if_neg (by simp [hnotFirst]), if_neg (by simp [hpair])]
  rw [hval]
  exact ⟨encControl_rewindOne x q henc.1 {q.ctl with pair := true} {x.ctl with pair := true}
      (by rw [← henc.1.ctl]; rfl) bit hbit newPolarity newGap,
    encTapes_rewindOne margin x q.polarity newPolarity q.gap newGap q.micro q.fppLive q.dpLive
      tapes newTapes henc.2 {x.ctl with pair := true} hheads hgapOther hpolarity segments hlength
      hcounterTape hmirrorLen hprog hprogOther hkept hmarginHead hidleShape⟩

/-- **a program tape that steps left, from the action the rule names.**  The rule writes back
the symbol under the head and steps left; the head is not on the floor, so what comes out is the
padded encoding of the tape one cell left. -/
theorem progSlot_after_moveLeft {margin K : ℕ} {x : State GalilVM} {polarity : Fin 16 → Bool}
    {gap : Fin 4 → Bool} {micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl}
    {fppLive dpLive : Bool} {T newTapes : Slot → STape Γm}
    (henc : EncTapes margin x polarity gap micro fppLive dpLive T) (hK : K ≤ margin)
    (i : Fin 9) (hfloor : (x.vm.fpp.program.config.tapes i).left ≠ [])
    (hmoved : newTapes (progSlotOf fppLive i)
      = PalPeg.CloseoutCoreEnc12.actList blankM (T (progSlotOf fppLive i))
          [some (centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
              (progSlot fppLive i), (.left : PalPeg.CloseoutCoreEnc12.MoveC))]) :
    newTapes (progSlotOf fppLive i)
      = padLeft margin (mapTape encProg (encTape
          (PalPeg.GalilScaffoldTape.moveLeft (x.vm.fpp.program.config.tapes i)))) := by
  have hslot : T (progSlotOf fppLive i)
      = padLeft margin (mapTape encProg (encTape (x.vm.fpp.program.config.tapes i))) := henc.fpp i
  have hcentre : centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot fppLive i) = encProg (x.vm.fpp.program.config.tapes i).focus := by
    rw [centreRead_of_margin T (progSlot fppLive i) (le_trans hK (henc.margins _)), hslot]
    exact focus_padded margin (x.vm.fpp.program.config.tapes i)
  rw [hmoved, hcentre, hslot,
    padded_moveLeft margin (x.vm.fpp.program.config.tapes i) hfloor]
  rfl

/-- **the paired step of the rewind, on the whole state.**  The marks tape steps left, both the
left and the centre input head step left, and the two counters count the step.  The heads' new
views are the caller's to supply, as in the single step. -/
theorem rewind_pair {fppBound dpBound : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (tapes newTapes : Slot → STape Γm)
    (newPolarity : Fin 16 → Bool) (newGap : Fin 4 → Bool) (bit : Bool)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind)
    (hnotFirst : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).atFirst x.vm
      = false)
    (hpair : x.ctl.pair = true)
    (hbit : bit = decide (PalPeg.GalilScaffoldChainInputSupply.position
      (PalPeg.GalilScaffoldInputHead.left x.vm.left) = 1))
    (henc : Enc w margin x (q, tapes))
    (viewLeft : PalPeg.LocalInputView.InputView)
    (viewTapesLeft : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (habsLeft : PalPeg.LocalArrival.absHead' viewLeft []
      = PalPeg.GalilScaffoldInputHead.left x.vm.left)
    (hrepLeft : PalPeg.ConcreteLocalMachine.ViewRep margin viewLeft (newGap 0) (q.micro 0)
      viewTapesLeft)
    (hslotsLeft : ∀ i, newTapes (headSlot 0 i) = mapTape encCell (viewTapesLeft i))
    (hcellsLeft : PalPeg.LocalViewCells.ViewCells viewLeft) (hwfLeft : PalPeg.LocalInputView.WF viewLeft)
    (viewCentre : PalPeg.LocalInputView.InputView)
    (viewTapesCentre : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (habsCentre : PalPeg.LocalArrival.absHead' viewCentre []
      = PalPeg.GalilScaffoldInputHead.left x.vm.center)
    (hrepCentre : PalPeg.ConcreteLocalMachine.ViewRep margin viewCentre (newGap 1) (q.micro 1)
      viewTapesCentre)
    (hslotsCentre : ∀ i, newTapes (headSlot 1 i) = mapTape encCell (viewTapesCentre i))
    (hcellsCentre : PalPeg.LocalViewCells.ViewCells viewCentre) (hwfCentre : PalPeg.LocalInputView.WF viewCentre)
    (hgapOther : ∀ v : Fin 4, v ≠ 0 → v ≠ 1 → newGap v = q.gap v)
    (hpolarity : ∀ c : Fin 16, c ≠ 3 → c ≠ 2 → newPolarity c = q.polarity c)
    (segLen : STape Seg)
    (hlength : absCtr segLen (newPolarity 3) = PalPeg.GalilScaffoldCounter.inc x.vm.length)
    (hcounterLen : newTapes (counterSlot 3) = padLeft margin (mapTape encSeg segLen))
    (hmirrorLen : ∀ m : Fin 7, mirrorSource m = 3 → ∃ seg : STape Seg,
      absCtr seg (newPolarity 3) = PalPeg.GalilScaffoldCounter.inc x.vm.length
        ∧ newTapes (mirrorSlot m) = padLeft margin (mapTape encSeg seg))
    (segRad : STape Seg)
    (hradius : absCtr segRad (newPolarity 2) = PalPeg.GalilScaffoldCounter.inc x.vm.radius)
    (hcounterRad : newTapes (counterSlot 2) = padLeft margin (mapTape encSeg segRad))
    (hmirrorRad : ∀ m : Fin 7, mirrorSource m = 2 → ∃ seg : STape Seg,
      absCtr seg (newPolarity 2) = PalPeg.GalilScaffoldCounter.inc x.vm.radius
        ∧ newTapes (mirrorSlot m) = padLeft margin (mapTape encSeg seg))
    (hprog : newTapes (progSlotOf q.fppLive 8)
      = padLeft margin (mapTape encProg (encTape
          (PalPeg.GalilScaffoldTape.moveLeft (x.vm.fpp.program.config.tapes 8)))))
    (hprogOther : ∀ j : Fin 9, j ≠ 8 →
      newTapes (progSlotOf q.fppLive j) = tapes (progSlotOf q.fppLive j))
    (hkept : ∀ slot, (∀ j : Fin 9, slot ≠ progSlotOf q.fppLive j) → slot ≠ counterSlot 3 →
      slot ≠ counterSlot 2 → (∀ m : Fin 7, mirrorSource m = 2 → slot ≠ mirrorSlot m) →
      (∀ m : Fin 7, mirrorSource m = 3 → slot ≠ mirrorSlot m) →
      (∀ i : Fin 12, slot ≠ headSlot 0 i) → (∀ i : Fin 12, slot ≠ headSlot 1 i) →
      (∀ k : Fin 9, slot ≠ progSlotOf (!q.fppLive) k) → newTapes slot = tapes slot)
    (hmarginLeft : ∀ i : Fin 12, margin ≤ PalPeg.Local.pos (newTapes (headSlot 0 i)))
    (hmarginCentre : ∀ i : Fin 12, margin ≤ PalPeg.Local.pos (newTapes (headSlot 1 i)))
    (hidleShape : ∀ k : Fin 9, ∃ raw : STape (Fin 9),
      newTapes (progSlotOf (!q.fppLive) k) = padLeft margin (mapTape encProg raw)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ({q with ctl := {q.ctl with pair := false}, leftFirstBit := bit, polarity := newPolarity, gap := newGap}, newTapes) := by
  have hval : PalPeg.GalilScaffoldTop.tickFun
      (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x
      = ⟨{x.ctl with pair := false}, {x.vm with fpp := PalPeg.GalilScaffoldChainInputSupply.markStep x.vm.fpp PalPeg.GalilScaffoldTape.moveLeft, left := PalPeg.GalilScaffoldInputHead.left x.vm.left, length := PalPeg.GalilScaffoldCounter.inc x.vm.length, center := PalPeg.GalilScaffoldInputHead.left x.vm.center, radius := PalPeg.GalilScaffoldCounter.inc x.vm.radius}⟩ := by
    simp only [PalPeg.GalilScaffoldTop.tickFun, hmode, frameFun_rewindPair]
    rw [if_neg (by simp [hnotFirst]), if_pos (by simp [hpair])]
  rw [hval]
  exact ⟨encControl_rewindPair x q henc.1 {q.ctl with pair := false} {x.ctl with pair := false}
      (by rw [← henc.1.ctl]; rfl) bit hbit newPolarity newGap,
    encTapes_rewindPair margin x q.polarity newPolarity q.gap newGap q.micro q.fppLive q.dpLive
      tapes newTapes henc.2 {x.ctl with pair := false} viewLeft viewTapesLeft habsLeft hrepLeft
      hslotsLeft hcellsLeft hwfLeft viewCentre viewTapesCentre habsCentre hrepCentre
      hslotsCentre hcellsCentre hwfCentre hgapOther hpolarity segLen hlength hcounterLen hmirrorLen segRad hradius hcounterRad
      hmirrorRad hprog hprogOther hkept hmarginLeft hmarginCentre hidleShape⟩

/-- **the branch the shift and copy modes take, as a reading of the window.**  The rule cannot
ask the abstraction anything; it computes this bit from three cells of the window and the sign
bit of the shift counter, and `remainsTest_eq` says the bit it computes is the test the tick
function asks. -/
noncomputable def remainsTest {K : ℕ} (polarity : Fin 16 → Bool)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) : Bool :=
  (polarity 1 && decide (belowRead ws (counterSlot 1) = encSeg PalPeg.LocalCounter.mark))
    || (decide (centreRead ws (placeSlot 1) ≠ blankM)
        && decide (belowRead ws (counterSlot 9) = encSeg PalPeg.LocalCounter.mark))

theorem remainsTest_eq {margin K : ℕ} {x : State GalilVM} {polarity : Fin 16 → Bool}
    {gap : Fin 4 → Bool} {micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl}
    {fppLive dpLive : Bool} {T : Slot → STape Γm}
    (henc : EncTapes margin x polarity gap micro fppLive dpLive T) (hK1 : 1 ≤ K) (hK : K ≤ margin)
    (centre : GalilVM → Fin 3) (place : GalilVM → PalPeg.GalilScaffoldPlace.Place)
    (entry entryQ : ℕ) (first : Fin 9) (w : List (Fin 2)) :
    remainsTest polarity (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).remainingPos x.vm := by
  rw [Bool.eq_iff_iff, remainingPos_iff_window henc hK1 hK centre place entry entryQ first w]
  simp [remainsTest]

/-- **the action table of the mark walk.**  The marks tape walks right while the head is not on
the end mark, and left on the step that finds it. -/
noncomputable def markEndActs {K : ℕ} (live : Bool) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) :
    Fin tapeCountM → List (PalPeg.CloseoutCoreEnc12.Act Γm) :=
  if centreRead ws (progSlot live 8) = encProg 5 then
    (if belowRead ws (progSlot live 8) = bottomM then actsAt (slotIndex (progSlot live 8)) []
      else actsAt (slotIndex (progSlot live 8))
        [some (centreRead ws (progSlot live 8), (.left : PalPeg.CloseoutCoreEnc12.MoveC))])
  else actsAt (slotIndex (progSlot live 8))
    [some (centreRead ws (progSlot live 8), (.right : PalPeg.CloseoutCoreEnc12.MoveC))]

/-- **the control table of the mark walk.**  Finding the end mark sends the controller to
`choose` with its parity bit cleared; otherwise the control stands still. -/
noncomputable def markEndNext {fppBound dpBound K : ℕ} (live : Bool) (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) : QPhys fppBound dpBound :=
  if centreRead ws (progSlot live 8) = encProg 5 then
    {q with ctl := {q.ctl with mode := PalPeg.GalilScaffoldController.Mode.choose, odd := false}}
  else q

/-- **the mark walk forward, rule and encoding together.**  Given a rule whose control and
actions in this state are `markEndNext` and `markEndActs`, the ideal step it prescribes carries
the encoding across the controller's tick. -/
theorem markEnd_forward_of_rule {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (R : PalPeg.CloseoutCoreEnc12.ActRule (Fin 2) (QPhys fppBound dpBound) Γm tapeCountM K)
    (hnq : R.nq q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = markEndNext q.fppLive q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)))
    (hacts : R.acts q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = withErase q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (markEndActs q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))))
    (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i))
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd)
    (hnotEnd : (x.vm.fpp.program.config.tapes 8).focus ≠ 5)
    (hnotMark : (T (progSlot q.fppLive 8)).focus ≠ encProg 5)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2
          (slotIndex i)) := by
  have hread : centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot q.fppLive 8) = (T (progSlot q.fppLive 8)).focus :=
    centreRead_of_margin T (progSlot q.fppLive 8) (hmargin _)
  have hq : (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).1 = q := by
    show R.nq q none _ = _
    rw [hnq]
    unfold markEndNext
    rw [hread, if_neg hnotMark]
  have hacts' : R.acts q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = withErase q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (actsAt (slotIndex (progSlot q.fppLive 8))
            [some ((T (progSlot q.fppLive 8)).focus,
              (.right : PalPeg.CloseoutCoreEnc12.MoveC))]) := by
    rw [hacts]
    congr 1
    unfold markEndActs
    rw [hread, if_neg hnotMark]
  obtain ⟨hmoved, hkept⟩ := idealStep_atLiveSlot R q T q.fppLive 8 _ hacts'
  rw [hq]
  exact markEnd_forward margin centre place entry entryQ first w F delay x q T
    (fun slot => (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2 (slotIndex slot))
    hmode hnotEnd henc hmoved hkept
    (idle_shape_after_erase margin hK1 hKn R q T q.fppLive _ hacts'
      (offLive_offIdle (actsAt_off_live q.fppLive 8 _)) henc.2.idleShape)

/-- **the mark walk back, rule and encoding together.**  The step that finds the end mark: the
marks tape walks one cell left and the controller goes to `choose`. -/
theorem markEnd_back_of_rule {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (R : PalPeg.CloseoutCoreEnc12.ActRule (Fin 2) (QPhys fppBound dpBound) Γm tapeCountM K)
    (hnq : R.nq q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = markEndNext q.fppLive q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)))
    (hacts : R.acts q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = withErase q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (markEndActs q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))))
    (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i))
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd)
    (hatEnd : (x.vm.fpp.program.config.tapes 8).focus = 5)
    (hfloor : (x.vm.fpp.program.config.tapes 8).left ≠ [])
    (hatMark : (T (progSlot q.fppLive 8)).focus = encProg 5)
    (hnotFloor : belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot q.fppLive 8) ≠ bottomM)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2
          (slotIndex i)) := by
  have hread : centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot q.fppLive 8) = (T (progSlot q.fppLive 8)).focus :=
    centreRead_of_margin T (progSlot q.fppLive 8) (hmargin _)
  have hq : (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).1
      = {q with ctl := {q.ctl with mode := PalPeg.GalilScaffoldController.Mode.choose, odd := false}} := by
    show R.nq q none _ = _
    rw [hnq]
    unfold markEndNext
    rw [hread, if_pos hatMark]
  have hacts' : R.acts q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = withErase q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (actsAt (slotIndex (progSlot q.fppLive 8))
            [some ((T (progSlot q.fppLive 8)).focus,
              (.left : PalPeg.CloseoutCoreEnc12.MoveC))]) := by
    rw [hacts]
    congr 1
    unfold markEndActs
    rw [hread, if_pos hatMark, if_neg hnotFloor]
  obtain ⟨hmoved, hkept⟩ := idealStep_atLiveSlot R q T q.fppLive 8 _ hacts'
  rw [hq]
  exact markEnd_back margin centre place entry entryQ first w F delay x q T
    (fun slot => (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2 (slotIndex slot))
    hmode hatEnd hfloor henc hmoved hkept
    (idle_shape_after_erase margin hK1 hKn R q T q.fppLive _ hacts'
      (offLive_offIdle (actsAt_off_live q.fppLive 8 _)) henc.2.idleShape)

/-! ### the walk home

Two readings decide this branch: the symbol under the head of the source slot, and the symbol
one cell below it.  The second is what the floor sentinel is for — a component that has reached
its own left edge must say so from the window, because the padded tape it lives on still has
cells below the head. -/

/-- **the control table of the walk home.**  Reaching the left end starts the preparation
program: a program counter, a cleared halting flag and a mode, all finite control. -/
noncomputable def homeNext {fppBound dpBound K : ℕ} (live : Bool) (hbound : 320 < fppBound)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) :
    QPhys fppBound dpBound :=
  if centreRead ws (progSlot live 7) = encProg 4 then
    {q with ctl := {q.ctl with mode := PalPeg.GalilScaffoldController.Mode.fpp}, fppMode := .run, fppPc := some ⟨320, hbound⟩, fppDone := false}
  else q

/-- **the action table of the walk home.**  The source tape walks one cell left, unless the
head is on the left mark — which starts the program — or the cell below is the floor. -/
noncomputable def homeActs {K : ℕ} (live : Bool) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) :
    Fin tapeCountM → List (PalPeg.CloseoutCoreEnc12.Act Γm) :=
  if centreRead ws (progSlot live 7) = encProg 4 then actsAt (slotIndex (progSlot live 7)) []
  else if belowRead ws (progSlot live 7) = bottomM then actsAt (slotIndex (progSlot live 7)) []
  else actsAt (slotIndex (progSlot live 7))
    [some (centreRead ws (progSlot live 7), (.left : PalPeg.CloseoutCoreEnc12.MoveC))]

/-- **the start of the preparation program, rule and encoding together.**  The one branch of the
whole machine that names no action at all. -/
theorem home_fppStart_of_rule {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (R : PalPeg.CloseoutCoreEnc12.ActRule (Fin 2) (QPhys fppBound dpBound) Γm tapeCountM K)
    (hbound : 320 < fppBound)
    (hnq : R.nq q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = homeNext q.fppLive hbound q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)))
    (hacts : R.acts q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = withErase q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (homeActs q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))))
    (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i))
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.home)
    (hatLeft : (x.vm.fpp.program.config.tapes 7).focus = 4)
    (hatMark : (T (progSlot q.fppLive 7)).focus = encProg 4)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2
          (slotIndex i)) := by
  have hread : centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot q.fppLive 7) = (T (progSlot q.fppLive 7)).focus :=
    centreRead_of_margin T (progSlot q.fppLive 7) (hmargin _)
  have hq : (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).1
      = {q with ctl := {q.ctl with mode := PalPeg.GalilScaffoldController.Mode.fpp}, fppMode := .run, fppPc := some ⟨320, hbound⟩, fppDone := false} := by
    show R.nq q none _ = _
    rw [hnq]
    unfold homeNext
    rw [hread, if_pos hatMark]
  have hacts' : R.acts q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = withErase q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (actsAt (slotIndex (progSlot q.fppLive 7)) []) := by
    rw [hacts]
    congr 1
    unfold homeActs
    rw [hread, if_pos hatMark]
  obtain ⟨hmoved, hkept⟩ := idealStep_atLiveSlot R q T q.fppLive 7 _ hacts'
  have hkeptAll : ∀ slot : Slot, (∀ k : Fin 9, slot ≠ progSlotOf (!q.fppLive) k) →
      (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2 (slotIndex slot)
        = T slot := by
    intro slot hslot
    by_cases hi : slot = progSlot q.fppLive 7
    · subst hi; rw [hmoved]; rfl
    · exact hkept slot hi hslot
  rw [hq]
  exact ⟨(home_fppStart margin centre place entry entryQ first w F delay x q T hbound hmode
      hatLeft henc).1,
    encTapes_idleOnly margin _ _ _ _ _ _ T _
      (home_fppStart margin centre place entry entryQ first w F delay x q T hbound hmode
        hatLeft henc).2 hkeptAll
      (idle_shape_after_erase margin hK1 hKn R q T q.fppLive _ hacts'
      (offLive_offIdle (actsAt_off_live q.fppLive 7 _)) henc.2.idleShape)⟩

/-- **the walk home itself, rule and encoding together.**  The head is not on the left mark and
the cell below it is not the floor, so the source tape walks one cell left. -/
theorem home_step_of_rule {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (R : PalPeg.CloseoutCoreEnc12.ActRule (Fin 2) (QPhys fppBound dpBound) Γm tapeCountM K)
    (hbound : 320 < fppBound)
    (hnq : R.nq q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = homeNext q.fppLive hbound q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)))
    (hacts : R.acts q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = withErase q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (homeActs q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))))
    (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i))
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.home)
    (hnotLeft : (x.vm.fpp.program.config.tapes 7).focus ≠ 4)
    (hfloor : (x.vm.fpp.program.config.tapes 7).left ≠ [])
    (hnotMark : (T (progSlot q.fppLive 7)).focus ≠ encProg 4)
    (hnotFloor : belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot q.fppLive 7) ≠ bottomM)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2
          (slotIndex i)) := by
  have hread : centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot q.fppLive 7) = (T (progSlot q.fppLive 7)).focus :=
    centreRead_of_margin T (progSlot q.fppLive 7) (hmargin _)
  have hq : (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).1 = q := by
    show R.nq q none _ = _
    rw [hnq]
    unfold homeNext
    rw [hread, if_neg hnotMark]
  have hacts' : R.acts q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = withErase q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (actsAt (slotIndex (progSlot q.fppLive 7))
            [some ((T (progSlot q.fppLive 7)).focus,
              (.left : PalPeg.CloseoutCoreEnc12.MoveC))]) := by
    rw [hacts]
    congr 1
    unfold homeActs
    rw [hread, if_neg hnotMark, if_neg hnotFloor]
  obtain ⟨hmoved, hkept⟩ := idealStep_atLiveSlot R q T q.fppLive 7 _ hacts'
  rw [hq]
  exact home_step margin centre place entry entryQ first w F delay x q T
    (fun slot => (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2 (slotIndex slot))
    hmode hnotLeft hfloor henc hmoved hkept
    (idle_shape_after_erase margin hK1 hKn R q T q.fppLive _ hacts'
      (offLive_offIdle (actsAt_off_live q.fppLive 7 _)) henc.2.idleShape)

/-! ### the parity walk of `choose`

The step that keeps looking is the mark walk again, with the parity bit flipped.  The step that
stops looking resets two bank counters and copies a head, so it is named by its own table
further on; this section is the walking one. -/

/-- the control of the parity walk: the bit flips, nothing else. -/
def chooseBackNext {fppBound dpBound : ℕ} (q : QPhys fppBound dpBound) :
    QPhys fppBound dpBound :=
  {q with ctl := {q.ctl with odd := !q.ctl.odd}}

/-- the actions of the parity walk: the marks tape one cell left, unless it is on its floor. -/
noncomputable def chooseBackActs {K : ℕ} (live : Bool) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) :
    Fin tapeCountM → List (PalPeg.CloseoutCoreEnc12.Act Γm) :=
  if belowRead ws (progSlot live 8) = bottomM then actsAt (slotIndex (progSlot live 8)) []
  else actsAt (slotIndex (progSlot live 8))
    [some (centreRead ws (progSlot live 8), (.left : PalPeg.CloseoutCoreEnc12.MoveC))]

/-- **the parity walk, rule and encoding together.** -/
theorem choose_back_of_rule {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (R : PalPeg.CloseoutCoreEnc12.ActRule (Fin 2) (QPhys fppBound dpBound) Γm tapeCountM K)
    (hnq : R.nq q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = chooseBackNext q)
    (hacts : R.acts q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = withErase q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (chooseBackActs q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))))
    (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i))
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.choose)
    (hkeep : (x.ctl.odd && (decide ((x.vm.fpp.program.config.tapes 8).focus = 8)
        || decide ((x.vm.fpp.program.config.tapes 8).focus = first))) = false)
    (hfloor : (x.vm.fpp.program.config.tapes 8).left ≠ [])
    (hnotFloor : belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot q.fppLive 8) ≠ bottomM)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2
          (slotIndex i)) := by
  have hread : centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot q.fppLive 8) = (T (progSlot q.fppLive 8)).focus :=
    centreRead_of_margin T (progSlot q.fppLive 8) (hmargin _)
  have hq : (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).1
      = {q with ctl := {q.ctl with odd := !q.ctl.odd}} := hnq
  have hacts' : R.acts q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = withErase q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (actsAt (slotIndex (progSlot q.fppLive 8))
            [some ((T (progSlot q.fppLive 8)).focus,
              (.left : PalPeg.CloseoutCoreEnc12.MoveC))]) := by
    rw [hacts]
    congr 1
    unfold chooseBackActs
    rw [if_neg hnotFloor, hread]
  obtain ⟨hmoved, hkept⟩ := idealStep_atLiveSlot R q T q.fppLive 8 _ hacts'
  rw [hq]
  exact choose_back margin centre place entry entryQ first w F delay x q T
    (fun slot => (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2 (slotIndex slot))
    hmode hkeep hfloor henc hmoved hkept
    (idle_shape_after_erase margin hK1 hKn R q T q.fppLive _ hacts'
      (offLive_offIdle (actsAt_off_live q.fppLive 8 _)) henc.2.idleShape)

/-! ### the three branches that stop at a component's own floor

A component whose head sits on its first cell must not walk further left: the padded tape it
lives on would move onto the blanks below, and the encoding would no longer be `padLeft margin`
of anything.  The rule sees this in the window — the cell below the head is the sentinel — and
names no action, which is exactly what the abstraction does, since the abstract move at the left
edge is the identity. -/

/-- **the mark walk back, on the floor.**  The marks tape is already on its first cell, so the
tick only sends the controller to `choose` -/
theorem markEnd_back_of_rule_atFloor {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (R : PalPeg.CloseoutCoreEnc12.ActRule (Fin 2) (QPhys fppBound dpBound) Γm tapeCountM K)
    (hnq : R.nq q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = markEndNext q.fppLive q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)))
    (hacts : R.acts q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = withErase q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (markEndActs q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))))
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd)
    (hatEnd : (x.vm.fpp.program.config.tapes 8).focus = 5)
    (hfloor : (x.vm.fpp.program.config.tapes 8).left = [])
    (hatMark : (T (progSlot q.fppLive 8)).focus = encProg 5)
    (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i))
    (hisFloor : belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot q.fppLive 8) = bottomM)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2
          (slotIndex i)) := by
  have hread : centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot q.fppLive 8) = (T (progSlot q.fppLive 8)).focus :=
    centreRead_of_margin T (progSlot q.fppLive 8) (hmargin _)
  have hq : (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).1 = {q with ctl := {q.ctl with mode := PalPeg.GalilScaffoldController.Mode.choose, odd := false}} := by
    show R.nq q none _ = _
    rw [hnq]
    unfold markEndNext
    rw [hread, if_pos hatMark]
  have hacts' : R.acts q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = withErase q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (actsAt (slotIndex (progSlot q.fppLive 8)) []) := by
    rw [hacts]
    congr 1
    unfold markEndActs
    rw [hread, if_pos hatMark, if_pos hisFloor]
  obtain ⟨hmoved, hkept⟩ := idealStep_atLiveSlot R q T q.fppLive 8 _ hacts'
  have hkeptAll : ∀ slot : Slot, (∀ k : Fin 9, slot ≠ progSlotOf (!q.fppLive) k) →
      (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2 (slotIndex slot)
        = T slot := by
    intro slot hslot
    by_cases hi : slot = progSlot q.fppLive 8
    · subst hi; rw [hmoved]; rfl
    · exact hkept slot hi hslot
  rw [hq]
  exact ⟨(markEnd_back_atFloor margin centre place entry entryQ first w F delay x q T hmode
    hatEnd hfloor henc).1,
    encTapes_idleOnly margin _ _ _ _ _ _ T _ (markEnd_back_atFloor margin centre place entry entryQ first w F delay x q T hmode
    hatEnd hfloor henc).2 hkeptAll
      (idle_shape_after_erase margin hK1 hKn R q T q.fppLive _ hacts'
      (offLive_offIdle (actsAt_off_live q.fppLive 8 _))
        henc.2.idleShape)⟩

/-- **the walk home, on the floor.**  The source tape is already on its first cell, so nothing
moves at all -/
theorem home_step_of_rule_atFloor {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (R : PalPeg.CloseoutCoreEnc12.ActRule (Fin 2) (QPhys fppBound dpBound) Γm tapeCountM K)
    (hbound : 320 < fppBound)
    (hnq : R.nq q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = homeNext q.fppLive hbound q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)))
    (hacts : R.acts q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = withErase q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (homeActs q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))))
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.home)
    (hnotLeft : (x.vm.fpp.program.config.tapes 7).focus ≠ 4)
    (hfloor : (x.vm.fpp.program.config.tapes 7).left = [])
    (hnotMark : (T (progSlot q.fppLive 7)).focus ≠ encProg 4)
    (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i))
    (hisFloor : belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot q.fppLive 7) = bottomM)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2
          (slotIndex i)) := by
  have hread : centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot q.fppLive 7) = (T (progSlot q.fppLive 7)).focus :=
    centreRead_of_margin T (progSlot q.fppLive 7) (hmargin _)
  have hq : (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).1 = q := by
    show R.nq q none _ = _
    rw [hnq]
    unfold homeNext
    rw [hread, if_neg hnotMark]
  have hacts' : R.acts q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = withErase q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (actsAt (slotIndex (progSlot q.fppLive 7)) []) := by
    rw [hacts]
    congr 1
    unfold homeActs
    rw [hread, if_neg hnotMark, if_pos hisFloor]
  obtain ⟨hmoved, hkept⟩ := idealStep_atLiveSlot R q T q.fppLive 7 _ hacts'
  have hkeptAll : ∀ slot : Slot, (∀ k : Fin 9, slot ≠ progSlotOf (!q.fppLive) k) →
      (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2 (slotIndex slot)
        = T slot := by
    intro slot hslot
    by_cases hi : slot = progSlot q.fppLive 7
    · subst hi; rw [hmoved]; rfl
    · exact hkept slot hi hslot
  rw [hq]
  exact ⟨(home_step_atFloor margin centre place entry entryQ first w F delay x q T hmode
    hnotLeft hfloor henc).1,
    encTapes_idleOnly margin _ _ _ _ _ _ T _ (home_step_atFloor margin centre place entry entryQ first w F delay x q T hmode
    hnotLeft hfloor henc).2 hkeptAll
      (idle_shape_after_erase margin hK1 hKn R q T q.fppLive _ hacts'
      (offLive_offIdle (actsAt_off_live q.fppLive 7 _))
        henc.2.idleShape)⟩

/-- **the parity walk, on the floor.**  Only the parity bit changes -/
theorem choose_back_of_rule_atFloor {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (R : PalPeg.CloseoutCoreEnc12.ActRule (Fin 2) (QPhys fppBound dpBound) Γm tapeCountM K)
    (hnq : R.nq q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = chooseBackNext q)
    (hacts : R.acts q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = withErase q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (chooseBackActs q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))))
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.choose)
    (hkeep : (x.ctl.odd && (decide ((x.vm.fpp.program.config.tapes 8).focus = 8)
        || decide ((x.vm.fpp.program.config.tapes 8).focus = first))) = false)
    (hfloor : (x.vm.fpp.program.config.tapes 8).left = [])
    (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i))
    (hisFloor : belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot q.fppLive 8) = bottomM)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2
          (slotIndex i)) := by
  have hread : centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot q.fppLive 8) = (T (progSlot q.fppLive 8)).focus :=
    centreRead_of_margin T (progSlot q.fppLive 8) (hmargin _)
  have hq : (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).1 = {q with ctl := {q.ctl with odd := !q.ctl.odd}} := hnq
  have hacts' : R.acts q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = withErase q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (actsAt (slotIndex (progSlot q.fppLive 8)) []) := by
    rw [hacts]
    congr 1
    unfold chooseBackActs
    rw [if_pos hisFloor]
  obtain ⟨hmoved, hkept⟩ := idealStep_atLiveSlot R q T q.fppLive 8 _ hacts'
  have hkeptAll : ∀ slot : Slot, (∀ k : Fin 9, slot ≠ progSlotOf (!q.fppLive) k) →
      (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2 (slotIndex slot)
        = T slot := by
    intro slot hslot
    by_cases hi : slot = progSlot q.fppLive 8
    · subst hi; rw [hmoved]; rfl
    · exact hkept slot hi hslot
  rw [hq]
  exact ⟨(choose_back_atFloor margin centre place entry entryQ first w F delay x q T hmode hkeep
    hfloor henc).1,
    encTapes_idleOnly margin _ _ _ _ _ _ T _ (choose_back_atFloor margin centre place entry entryQ first w F delay x q T hmode hkeep
    hfloor henc).2 hkeptAll
      (idle_shape_after_erase margin hK1 hKn R q T q.fppLive _ hacts'
      (offLive_offIdle (actsAt_off_live q.fppLive 8 _))
        henc.2.idleShape)⟩

/-! ### the counter bank: three tape actions and no more

A counter of the bank is a segmented unary tape, and each of the three things the machine does
to one — `push`, `pop`, `resetSeg` — is a single `applyAction`.  So a counter slot obeys the
same one-action discipline as a program slot, with the alphabet `Seg` in place of `Fin 9`. -/

theorem encSeg_blank : encSeg PalPeg.LocalCounter.blank = blankM := if_pos rfl

theorem padded_seg_right (n : ℕ) (segments : STape Seg) (written : Seg) :
    padLeft n (mapTape encSeg
        (STape.applyAction PalPeg.LocalCounter.blank segments (written, .right)))
      = (padLeft n (mapTape encSeg segments)).applyAction blankM (encSeg written, .right) := by
  rw [mapTape_applyAction encSeg encSeg_blank segments written .right,
    padLeft_applyAction_right]

theorem padded_seg_left (n : ℕ) (segments : STape Seg) (written : Seg)
    (hleft : segments.left ≠ []) :
    padLeft n (mapTape encSeg
        (STape.applyAction PalPeg.LocalCounter.blank segments (written, .left)))
      = (padLeft n (mapTape encSeg segments)).applyAction blankM (encSeg written, .left) := by
  rw [mapTape_applyAction encSeg encSeg_blank segments written .left,
    padLeft_applyAction_left n (mapTape encSeg segments) (encSeg written)
      (by obtain ⟨left, focus, right⟩ := segments
          cases left with
          | nil => exact absurd rfl hleft
          | cons head rest => exact List.cons_ne_nil _ _)]

/-- **a push of a counter is one action on the tape the machine keeps.** -/
theorem padded_push (n : ℕ) (segments : STape Seg) :
    padLeft n (mapTape encSeg (PalPeg.LocalCounter.push segments))
      = (padLeft n (mapTape encSeg segments)).applyAction blankM
          (encSeg PalPeg.LocalCounter.mark, .right) :=
  padded_seg_right n segments PalPeg.LocalCounter.mark

/-- **a pop of a counter is one action**: blank the frontier and step back onto the top mark.
The written symbol is the blank of the machine's own alphabet. -/
theorem padded_pop (n : ℕ) (segments : STape Seg) (hleft : segments.left ≠ []) :
    padLeft n (mapTape encSeg (PalPeg.LocalCounter.pop segments))
      = (padLeft n (mapTape encSeg segments)).applyAction blankM (blankM, .left) := by
  rw [show (blankM : Γm) = encSeg PalPeg.LocalCounter.blank from encSeg_blank.symm]
  exact padded_seg_left n segments PalPeg.LocalCounter.blank hleft

/-- **a reset of a counter is one action**: drop a fresh separator and step past it. -/
theorem padded_resetSeg (n : ℕ) (segments : STape Seg) :
    padLeft n (mapTape encSeg (PalPeg.LocalCounter.resetSeg segments))
      = (padLeft n (mapTape encSeg segments)).applyAction blankM
          (encSeg PalPeg.LocalCounter.sep, .right) :=
  padded_seg_right n segments PalPeg.LocalCounter.sep

/-! ### one call of the program machine, as actions on the encoded tapes

`progTickFun_tapes` said the call changes at most one slot, by at most one action.  Here that
action is named in the machine's own alphabet, and the encoding is shown to survive it. -/

/-- **a counter is positive exactly when its sign bit is set and its frontier is a mark**, read
off whichever tape carries it.  This is the bit a decrement branches on, and the bit it leaves
behind as the counter's new sign. -/
noncomputable def decSignAt {K : ℕ} (bit : Bool) (slot : Slot)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) : Bool :=
  bit && decide (belowRead ws slot = encSeg PalPeg.LocalCounter.mark)

/-- **the action a decrement names, on whichever tape carries the counter.**  Pop while the value
is positive, push otherwise — the mirror image of `incActAt`, and what `counter_dec_at` is stated
for. -/
noncomputable def decActAt {K : ℕ} (bit : Bool) (slot : Slot)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) : PalPeg.CloseoutCoreEnc12.Act Γm :=
  if decSignAt bit slot ws then some (blankM, (.left : PalPeg.CloseoutCoreEnc12.MoveC))
  else some (encSeg PalPeg.LocalCounter.mark, (.right : PalPeg.CloseoutCoreEnc12.MoveC))

noncomputable def decAct {fppBound dpBound K : ℕ} (q : QPhys fppBound dpBound) (c : Fin 16)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) : PalPeg.CloseoutCoreEnc12.Act Γm :=
  decActAt (q.polarity c) (counterSlot c) ws

/-- **the bit that says the work counter can be decremented without crossing zero.**  A counter
tape holds the absolute value, so a decrement is a pop on the positive side and a push on the
negative side — and on the positive side of zero it is a push that changes the sign. -/
noncomputable def workPositive {K : ℕ} (polarity : Fin 16 → Bool)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) : Bool :=
  polarity 9 && decide (belowRead ws (counterSlot 9) = encSeg PalPeg.LocalCounter.mark)

/-- **the fallback copy's work counter comes down by that action.**  Said once, so that the
chain's lag — which comes down the same way — does not have to say it again. -/
theorem decAct_workCounter {fppBound dpBound K : ℕ} (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) :
    decAct q 9 ws
      = (if workPositive q.polarity ws then
          some (blankM, (.left : PalPeg.CloseoutCoreEnc12.MoveC))
        else some (encSeg PalPeg.LocalCounter.mark,
          (.right : PalPeg.CloseoutCoreEnc12.MoveC))) := rfl

/-- **a counter whose value is not zero stands clear of the left edge.** -/
theorem counter_left_ne_nil (segments : STape Seg) (h : PalPeg.LocalCounter.val segments ≠ 0) :
    segments.left ≠ [] := by
  intro hnil
  exact h (by show PalPeg.LocalCounter.markRun segments.left = 0; rw [hnil]; rfl)

/-- **two tapes that stand for the same counter with the same sign carry the same run of
marks.**  Which is why the sign bit computed from a counter's own window serves for its mirrors:
they hold the same value, so they hold the same number of marks. -/
theorem val_eq_of_absCtr_eq {t t' : STape Seg} {b : Bool} (h : absCtr t b = absCtr t' b) :
    PalPeg.LocalCounter.val t = PalPeg.LocalCounter.val t' := by
  cases b
  · have hneg := congrArg (fun c => c.neg.length) h
    simpa [absCtr, PalPeg.LocalCounter.negOfNat] using hneg
  · have hpos := congrArg (fun c => c.pos.length) h
    simpa [absCtr, PalPeg.GalilScaffoldCounter.ofNat] using hpos

/-- **the bit a decrement branches on, read off the counter's own tape.**  The counterpart of
`incSign_eq`: a counter is positive exactly when its sign bit is set and its value is not zero,
and the zero test is the cell below the head. -/
theorem decSignAt_eq {margin K : ℕ} (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (bit : Bool) (c : Fin 16) (tapes : Slot → STape Γm) (segments : STape Seg)
    (hslot : tapes (counterSlot c) = padLeft margin (mapTape encSeg segments)) :
    decSignAt bit (counterSlot c) (fun tape => PalPeg.Local.readWin blankM K (tapesOf tapes tape))
      = (bit && decide (PalPeg.LocalCounter.val segments ≠ 0)) := by
  have hbelow :
      belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf tapes tape)) (counterSlot c)
        = PalPeg.Local.readWin blankM K (padLeft margin (mapTape encSeg segments))
            ⟨K - 1, by omega⟩ := by
    show PalPeg.Local.readWin blankM K (tapesOf tapes (slotIndex (counterSlot c)))
      ⟨K - 1, by omega⟩ = _
    rw [tapesOf_apply, hslot]
  unfold decSignAt
  rw [hbelow]
  congr 1
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
  constructor
  · intro hmark hzero
    exact ((counterZero_iff_below hK1 (by omega) segments).mp hzero) hmark
  · intro hne
    by_contra hmark
    exact hne ((counterZero_iff_below hK1 (by omega) segments).mpr hmark)

/-- **the sign bit an increment produces, from the window of the counter's own slot.**  A
counter's mirrors hold the same value with the same sign, so they hold tapes of the same run of
marks, and the bit computed from the counter's own window serves for all of them. -/
theorem incSign_eq {margin K : ℕ} (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (polarity : Fin 16 → Bool) (c : Fin 16) (tapes : Slot → STape Γm) (segments : STape Seg)
    (hslot : tapes (counterSlot c) = padLeft margin (mapTape encSeg segments)) :
    incSign polarity c (fun tape => PalPeg.Local.readWin blankM K (tapesOf tapes tape))
      = (polarity c || decide (PalPeg.LocalCounter.val segments = 0)) := by
  have hbelow :
      belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf tapes tape)) (counterSlot c)
        = PalPeg.Local.readWin blankM K (padLeft margin (mapTape encSeg segments))
            ⟨K - 1, by omega⟩ := by
    show PalPeg.Local.readWin blankM K (tapesOf tapes (slotIndex (counterSlot c)))
      ⟨K - 1, by omega⟩ = _
    rw [tapesOf_apply, hslot]
  unfold incSign incSignAt
  rw [hbelow]
  congr 1
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
  exact (counterZero_iff_below hK1 hKn segments).symm

/-- **one increment of a counter, on whichever tape carries it.**  Stated for a tape rather than
a slot, so that a counter's mirrors are served by the same lemma as the counter.  The sign bit is
an input, because all of them take the bit the counter's own window gives. -/
theorem counter_inc_at {margin : ℕ} (polarity : Fin 16 → Bool) (c : Fin 16) (bit : Bool)
    (segments : STape Seg) (value : PalPeg.GalilScaffoldCounter.Counter)
    (habs : absCtr segments (polarity c) = value)
    (hbit : bit = (polarity c || decide (PalPeg.LocalCounter.val segments = 0)))
    (tape : STape Γm) (hslot : tape = padLeft margin (mapTape encSeg segments)) :
    ∃ segments' : STape Seg,
      absCtr segments' bit = PalPeg.GalilScaffoldCounter.inc value
      ∧ PalPeg.CloseoutCoreEnc12.actList blankM tape
            [if bit then
                some (encSeg PalPeg.LocalCounter.mark,
                  (.right : PalPeg.CloseoutCoreEnc12.MoveC))
              else some (blankM, (.left : PalPeg.CloseoutCoreEnc12.MoveC))]
          = padLeft margin (mapTape encSeg segments') := by
  refine ⟨if bit then PalPeg.LocalCounter.push segments else PalPeg.LocalCounter.pop segments,
    ?_, ?_⟩
  · rw [hbit, ← habs]
    exact absCtr_inc segments (polarity c)
  · rw [hslot]
    by_cases hb : bit = true
    · rw [if_pos hb, if_pos hb]
      exact (padded_push margin segments).symm
    · rw [if_neg hb, if_neg hb]
      have hne : PalPeg.LocalCounter.val segments ≠ 0 := by
        intro hzero
        exact hb (by rw [hbit]; simp [hzero])
      exact (padded_pop margin segments (counter_left_ne_nil segments hne)).symm

/-- **one decrement of a counter, on whichever tape carries it.**  The counterpart of
`counter_inc_at`: the rule pops while the value is positive and pushes otherwise, and the bit it
branches on becomes the counter's new sign.  Stated for a tape and for any index, because the
chain's lag is decremented by the same two actions as the fallback copy's work counter. -/
theorem counter_dec_at {margin : ℕ} (polarity : Fin 16 → Bool) (c : Fin 16) (bit : Bool)
    (segments : STape Seg) (value : PalPeg.GalilScaffoldCounter.Counter)
    (habs : absCtr segments (polarity c) = value)
    (hbit : bit = (polarity c && decide (PalPeg.LocalCounter.val segments ≠ 0)))
    (tape : STape Γm) (hslot : tape = padLeft margin (mapTape encSeg segments)) :
    ∃ segments' : STape Seg,
      absCtr segments' bit = PalPeg.GalilScaffoldCounter.dec value
      ∧ PalPeg.CloseoutCoreEnc12.actList blankM tape
            [if bit then some (blankM, (.left : PalPeg.CloseoutCoreEnc12.MoveC))
              else some (encSeg PalPeg.LocalCounter.mark,
                (.right : PalPeg.CloseoutCoreEnc12.MoveC))]
          = padLeft margin (mapTape encSeg segments') := by
  refine ⟨if bit then PalPeg.LocalCounter.pop segments else PalPeg.LocalCounter.push segments,
    ?_, ?_⟩
  · rw [hbit, ← habs]
    exact absCtr_dec segments (polarity c)
  · rw [hslot]
    by_cases hb : bit = true
    · rw [if_pos hb, if_pos hb]
      have hne : PalPeg.LocalCounter.val segments ≠ 0 := by
        have hand := (Bool.and_eq_true _ _).mp (by rw [← hbit]; exact hb)
        exact of_decide_eq_true hand.2
      exact (padded_pop margin segments (counter_left_ne_nil segments hne)).symm
    · rw [if_neg hb, if_neg hb]
      exact (padded_push margin segments).symm

/-- **one tick of the fallback copy, on the work counter.**  The rule pops while the value is
positive and pushes otherwise, and the bit it branches on becomes the counter's new sign, so the
counter it leaves behind holds one less than it did. -/
theorem copy_one_counter {margin K : ℕ} (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (polarity : Fin 16 → Bool) (tapes : Slot → STape Γm) (segments : STape Seg)
    (value : PalPeg.GalilScaffoldCounter.Counter)
    (habs : absCtr segments (polarity 9) = value)
    (hslot : tapes (counterSlot 9) = padLeft margin (mapTape encSeg segments)) :
    ∃ segments' : STape Seg,
      absCtr segments'
          (workPositive polarity (fun tape => PalPeg.Local.readWin blankM K (tapesOf tapes tape)))
        = PalPeg.GalilScaffoldCounter.dec value
      ∧ PalPeg.CloseoutCoreEnc12.actList blankM (tapes (counterSlot 9))
            [if workPositive polarity
                  (fun tape => PalPeg.Local.readWin blankM K (tapesOf tapes tape)) then
                some (blankM, (.left : PalPeg.CloseoutCoreEnc12.MoveC))
              else some (encSeg PalPeg.LocalCounter.mark,
                (.right : PalPeg.CloseoutCoreEnc12.MoveC))]
          = padLeft margin (mapTape encSeg segments') := by
  have hbelow :
      belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf tapes tape)) (counterSlot 9)
        = PalPeg.Local.readWin blankM K (padLeft margin (mapTape encSeg segments))
            ⟨K - 1, by omega⟩ := by
    show PalPeg.Local.readWin blankM K (tapesOf tapes (slotIndex (counterSlot 9)))
      ⟨K - 1, by omega⟩ = _
    rw [tapesOf_apply, hslot]
  have hval := counterZero_iff_below hK1 hKn segments
  have hwp : workPositive polarity
      (fun tape => PalPeg.Local.readWin blankM K (tapesOf tapes tape))
      = (polarity 9 && decide (PalPeg.LocalCounter.val segments ≠ 0)) := by
    unfold workPositive
    rw [hbelow]
    congr 1
    rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
    constructor
    · intro hmark hzero
      exact (hval.mp hzero) hmark
    · intro hne
      exact not_not.mp (fun hnotmark => hne (hval.mpr hnotmark))
  refine ⟨if polarity 9 && decide (PalPeg.LocalCounter.val segments ≠ 0) then
      PalPeg.LocalCounter.pop segments else PalPeg.LocalCounter.push segments, ?_, ?_⟩
  · rw [hwp, ← habs]
    exact absCtr_dec segments (polarity 9)
  · rw [hwp, hslot]
    by_cases hbit : (polarity 9 && decide (PalPeg.LocalCounter.val segments ≠ 0)) = true
    · rw [if_pos hbit, if_pos hbit]
      have hne : PalPeg.LocalCounter.val segments ≠ 0 := by
        have := (Bool.and_eq_true _ _).mp hbit
        exact of_decide_eq_true this.2
      exact (padded_pop margin segments (counter_left_ne_nil segments hne)).symm
    · rw [if_neg hbit, if_neg hbit]
      exact (padded_push margin segments).symm

/-- the tick function's own name for a tick of the fallback copy that still has work. -/
theorem frameFun_copyOne (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (s : GalilVM) :
    (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).copyOne s
      = {s with fpp := PalPeg.FrameFunction.copyOneFun s.fpp} := rfl

/-- **a tick of the fallback copy that still has work, on the whole state.**  Three components
move: the program's copy tape takes the walker's letter and steps right, the work counter goes
down by one, and the walker steps half a place left.  Every one of the three is named by a
reading the rule has, and the encoding comes out the other side. -/
theorem copy_one {fppBound dpBound : ℕ} (margin K : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (tapes newTapes : Slot → STape Γm)
    (a : Fin 3) (hK1 : 1 ≤ K) (hK : K ≤ margin)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.copy)
    (hremains : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).remainingPos x.vm
      = true)
    (hread : PalPeg.GalilScaffoldPlace.read x.vm.fpp.walker = some a)
    (henc : Enc w margin x (q, tapes))
    (hprog : newTapes (progSlotOf q.fppLive 7)
      = PalPeg.CloseoutCoreEnc12.actList blankM (tapes (progSlotOf q.fppLive 7))
          [some (encProg (PalPeg.GalilFppPreparation.symbol a),
            (.right : PalPeg.CloseoutCoreEnc12.MoveC))])
    (hcounterTape : newTapes (counterSlot 9)
      = PalPeg.CloseoutCoreEnc12.actList blankM (tapes (counterSlot 9))
          [if workPositive q.polarity
                (fun tape => PalPeg.Local.readWin blankM K (tapesOf tapes tape)) then
              some (blankM, (.left : PalPeg.CloseoutCoreEnc12.MoveC))
            else some (encSeg PalPeg.LocalCounter.mark,
              (.right : PalPeg.CloseoutCoreEnc12.MoveC))])
    (hplaceTape : newTapes (placeSlot 1)
      = PalPeg.CloseoutCoreEnc12.actList blankM (tapes (placeSlot 1))
          (if q.placeGap 1 then []
            else [some (centreRead
                (fun tape => PalPeg.Local.readWin blankM K (tapesOf tapes tape)) (placeSlot 1),
              (.left : PalPeg.CloseoutCoreEnc12.MoveC))]))
    (hprogOther : ∀ j : Fin 9, j ≠ 7 →
      newTapes (progSlotOf q.fppLive j) = tapes (progSlotOf q.fppLive j))
    (hkept : ∀ slot, (∀ j : Fin 9, slot ≠ progSlotOf q.fppLive j) → slot ≠ counterSlot 9 →
      slot ≠ placeSlot 1 → (∀ k : Fin 9, slot ≠ progSlotOf (!q.fppLive) k) →
      newTapes slot = tapes slot)
    (hidleShape : ∀ k : Fin 9, ∃ raw : STape (Fin 9),
      newTapes (progSlotOf (!q.fppLive) k) = padLeft margin (mapTape encProg raw)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ({q with placeGap := Function.update q.placeGap 1 (!q.placeGap 1), polarity := Function.update q.polarity 9 (workPositive q.polarity (fun tape => PalPeg.Local.readWin blankM K (tapesOf tapes tape)))}, newTapes) := by
  obtain ⟨segments, habsWork, hslotWork⟩ := henc.2.counters 9 x.vm.fpp.work rfl
  obtain ⟨stackTape, junk, hsealed, hjunk, hstack, hslotPlace⟩ :=
    henc.2.places 1 x.vm.fpp.walker rfl
  obtain ⟨segments', habs', hcount'⟩ :=
    copy_one_counter hK1 (by omega) q.polarity tapes segments x.vm.fpp.work habsWork hslotWork
  obtain ⟨stackTape', hstack', hplace'⟩ :=
    copy_one_place hK tapes x.vm.fpp.walker (q.placeGap 1)
      (henc.1.placeGap 1 x.vm.fpp.walker rfl) a hread stackTape junk hstack hslotPlace
  have hval : PalPeg.GalilScaffoldTop.tickFun
      (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x
      = ⟨x.ctl, {x.vm with fpp := {x.vm.fpp with program := PalPeg.GalilScaffoldChainInputSupply.FppControl.tape x.vm.fpp 7 (fun t => PalPeg.GalilScaffoldTape.moveRight (PalPeg.GalilScaffoldTape.write t (PalPeg.GalilFppPreparation.symbol a))), work := PalPeg.GalilScaffoldCounter.dec x.vm.fpp.work, walker := PalPeg.GalilScaffoldPlace.left x.vm.fpp.walker}}⟩ := by
    simp only [PalPeg.GalilScaffoldTop.tickFun, hmode, frameFun_copyOne]
    rw [if_pos (by simp [hremains]), copyOneFun_eq x.vm.fpp a hread]
  rw [hval]
  refine ⟨encControl_copyOne x q henc.1 a hread _,
    encTapes_copyOne margin x q.polarity _ q.gap q.micro q.fppLive q.dpLive tapes newTapes
      henc.2 x.ctl a (fun c hc => Function.update_of_ne hc _ _) segments' ?_ ?_
      stackTape' junk hsealed hjunk hstack' ?_ ?_ hprogOther hkept hidleShape⟩
  · show absCtr segments' (Function.update q.polarity 9 (workPositive q.polarity (fun tape => PalPeg.Local.readWin blankM K (tapesOf tapes tape))) 9) = _
    rw [Function.update_self]
    exact habs'
  · rw [hcounterTape]
    exact hcount'
  · rw [hplaceTape]
    exact hplace'
  · rw [hprog, show tapes (progSlotOf q.fppLive 7)
        = padLeft margin (mapTape encProg (encTape (x.vm.fpp.program.config.tapes 7)))
        from henc.2.fpp 7]
    exact (padded_writeRight margin (x.vm.fpp.program.config.tapes 7)
      (PalPeg.GalilFppPreparation.symbol a)).symm

/-- the action one call of the program machine performs on a given slot. -/
noncomputable def progActOf (code : List (Instruction 9))
    (m : PalPeg.GalilScaffoldControl.Machine 9) (i : Fin 9) :
    List (PalPeg.CloseoutCoreEnc12.Act Γm) :=
  if m.done then []
  else
    match code[m.config.pc]? with
    | some (.move t true _) =>
        if i = t then [some (encProg (m.config.tapes t).focus, .right)] else []
    | some (.move t false _) =>
        if i = t then [some (encProg (m.config.tapes t).focus, .left)] else []
    | some (.write t sym _) => if i = t then [some (encProg sym, .stay)] else []
    | _ => []

/-- **the encoding survives one call of the program machine.**  A left move needs the tape to
have a cell below its head, which is the same floor condition every component carries. -/
theorem padded_progStep (margin : ℕ) (code : List (Instruction 9))
    (m : PalPeg.GalilScaffoldControl.Machine 9) (i : Fin 9)
    (hfloor : ∀ t : Fin 9, (m.config.tapes t).left ≠ []) :
    PalPeg.CloseoutCoreEnc12.actList blankM
        (padLeft margin (mapTape encProg (encTape (m.config.tapes i)))) (progActOf code m i)
      = padLeft margin (mapTape encProg (encTape
          ((PalPeg.ProgramFunction.tickFun code true m).config.tapes i))) := by
  rw [progTickFun_tapes code m]
  unfold progActOf progStepTapes
  cases hdone : m.done
  · simp only [Bool.false_eq_true, if_false]
    match hcode : code[m.config.pc]? with
    | none => simp [hcode]
    | some .halt => simp [hcode]
    | some (.read t cs) => simp [hcode]
    | some (.write t sym pc) =>
        simp only [hcode]
        by_cases hit : i = t
        · subst hit
          rw [if_pos rfl]
          show PalPeg.CloseoutCoreEnc12.actList blankM _ [some (encProg sym, .stay)]
            = padLeft margin (mapTape encProg (encTape
                (Function.update (fun _ => id) i (fun tp =>
                  PalPeg.GalilScaffoldTape.write tp sym) i (m.config.tapes i))))
          rw [Function.update_self, padded_write]
          rfl
        · rw [if_neg hit, Function.update_of_ne hit]
          rfl
    | some (.move t dir pc) =>
        cases dir
        · simp only [hcode]
          by_cases hit : i = t
          · subst hit
            rw [if_pos rfl]
            show PalPeg.CloseoutCoreEnc12.actList blankM _
              [some (encProg (m.config.tapes i).focus, .left)]
              = padLeft margin (mapTape encProg (encTape
                  (Function.update (fun _ => id) i PalPeg.GalilScaffoldTape.moveLeft i
                    (m.config.tapes i))))
            rw [Function.update_self, padded_moveLeft margin (m.config.tapes i) (hfloor i)]
            rfl
          · rw [if_neg hit, Function.update_of_ne hit]
            rfl
        · simp only [hcode]
          by_cases hit : i = t
          · subst hit
            rw [if_pos rfl]
            show PalPeg.CloseoutCoreEnc12.actList blankM _
              [some (encProg (m.config.tapes i).focus, .right)]
              = padLeft margin (mapTape encProg (encTape
                  (Function.update (fun _ => id) i PalPeg.GalilScaffoldTape.moveRight i
                    (m.config.tapes i))))
            rw [Function.update_self, padded_moveRight]
            rfl
          · rw [if_neg hit, Function.update_of_ne hit]
            rfl
  · simp [hdone]

theorem actList_append {Γ : Type} (blank : Γ) (T : STape Γ)
    (l l' : List (PalPeg.CloseoutCoreEnc12.Act Γ)) :
    PalPeg.CloseoutCoreEnc12.actList blank T (l ++ l')
      = PalPeg.CloseoutCoreEnc12.actList blank
          (PalPeg.CloseoutCoreEnc12.actList blank T l) l' := by
  induction l generalizing T with
  | nil => rfl
  | cons a as ih => exact ih _

/-- the actions a quantum of `n` calls performs on a given slot, in order. -/
noncomputable def progRunActs (code : List (Instruction 9)) :
    ℕ → PalPeg.GalilScaffoldControl.Machine 9 → Fin 9 →
      List (PalPeg.CloseoutCoreEnc12.Act Γm)
  | 0, _ => fun _ => []
  | n + 1, m => fun i =>
      progActOf code m i ++ progRunActs code n (PalPeg.ProgramFunction.tickFun code true m) i

/-- **the encoding survives a whole quantum.**  Each slot's actions are exactly the ones its own
calls perform, in order, and applying them to the encoded tape lands on the encoding of the tape
the run leaves behind. -/
theorem padded_progRun (margin : ℕ) (code : List (Instruction 9)) :
    ∀ (n : ℕ) (m : PalPeg.GalilScaffoldControl.Machine 9) (i : Fin 9),
      (∀ k, ∀ t : Fin 9, ((PalPeg.ProgramFunction.runFun code
        (List.replicate k true) m).config.tapes t).left ≠ []) →
      PalPeg.CloseoutCoreEnc12.actList blankM
          (padLeft margin (mapTape encProg (encTape (m.config.tapes i))))
          (progRunActs code n m i)
        = padLeft margin (mapTape encProg (encTape
            ((PalPeg.ProgramFunction.runFun code (List.replicate n true) m).config.tapes i))) := by
  intro n
  induction n with
  | zero => intro m i _; rfl
  | succ n ih =>
      intro m i hfloor
      show PalPeg.CloseoutCoreEnc12.actList blankM _
        (progActOf code m i ++ progRunActs code n
          (PalPeg.ProgramFunction.tickFun code true m) i) = _
      rw [actList_append, padded_progStep margin code m i (hfloor 0),
        ih (PalPeg.ProgramFunction.tickFun code true m) i
          (fun k t => hfloor (k + 1) t), List.replicate_succ]
      rfl

/-- **one call of the program machine is decided by what the machine can see.**  The halting
bit, the program counter and the symbols under the heads settle both the action and the tape it
falls on — nothing below or beyond the heads is consulted.  This is why the rule can name the
call from its windows. -/
theorem progActOf_congr (code : List (Instruction 9))
    (m m' : PalPeg.GalilScaffoldControl.Machine 9)
    (hdone : m.done = m'.done) (hpc : m.config.pc = m'.config.pc)
    (hfocus : ∀ t : Fin 9, (m.config.tapes t).focus = (m'.config.tapes t).focus) (i : Fin 9) :
    progActOf code m i = progActOf code m' i := by
  unfold progActOf
  rw [hdone, hpc]
  cases hdone' : m'.done
  · simp only [Bool.false_eq_true, if_false]
    match hcode : code[m'.config.pc]? with
    | none => simp [hcode]
    | some .halt => simp [hcode]
    | some (.read t cs) => simp [hcode]
    | some (.write t sym pc) => simp [hcode]
    | some (.move t dir pc) =>
        cases dir
        · simp only [hcode, hfocus t]
        · simp only [hcode, hfocus t]
  · simp

/-! ### the wipe of the preparation program

This is the branch the double buffer exists for.  Abstractly `fppReset` blanks all nine tapes of
the preparation program at once; on the machine nothing is written, the live bit flips, and the
half that becomes live was blanked in the background while the other one was in use. -/

theorem encControl_fppReset {fppBound dpBound : ℕ} {w : List (Fin 2)} (x : State GalilVM)
    (q : QPhys fppBound dpBound) (henc : EncControl w x q) (hbound : 320 < fppBound)
    (c : CtlPhys) (a : PalPeg.GalilScaffoldController.Control) (hc : ctlAbs c = a) :
    EncControl w ⟨a, {x.vm with fpp := {x.vm.fpp with program := PalPeg.GalilScaffoldControl.reset 320 x.vm.fpp.program}}⟩
      {q with ctl := c, fppPc := some ⟨320, hbound⟩, fppDone := true, fppLive := !q.fppLive} where
  ctl := hc
  chainTag := henc.chainTag
  chainPhase := henc.chainPhase
  chainForward := henc.chainForward
  chainBroken := henc.chainBroken
  fppMode := henc.fppMode
  fppFinalStage := henc.fppFinalStage
  fppPc := rfl
  fppDone := rfl
  dpPc := henc.dpPc
  dpDone := henc.dpDone
  searchMode := henc.searchMode
  searchFinalStage := henc.searchFinalStage
  searchQuarter := henc.searchQuarter
  periodOnly := henc.periodOnly
  placeGap := henc.placeGap
  onLetter := henc.onLetter
  leftFirst := henc.leftFirst

/-- **the wipe of the preparation program, encoding and tick together.**  The rule names no
action: the nine tapes the abstraction blanks are the nine the machine stops looking at.  What it
needs instead is that the other half is already blank, which is what the background erasure job
maintains while that half is idle. -/
theorem rewind_fppReset {fppBound dpBound : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (tapes : Slot → STape Γm)
    (hbound : 320 < fppBound)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind)
    (hatFirst : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).atFirst
      x.vm = true)
    (henc : Enc w margin x (q, tapes))
    (hidle : ∀ i : Fin 9, tapes (progSlotOf (!q.fppLive) i)
      = padLeft margin (mapTape encProg (encTape PalPeg.GalilScaffoldTape.reset))) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ({q with ctl := {q.ctl with mode := PalPeg.GalilScaffoldController.Mode.replayStart}, fppPc := some ⟨320, hbound⟩, fppDone := true, fppLive := !q.fppLive},
        tapes) := by
  have hval : PalPeg.GalilScaffoldTop.tickFun
      (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x
      = ⟨{x.ctl with mode := PalPeg.GalilScaffoldController.Mode.replayStart}, {x.vm with fpp := {x.vm.fpp with program := PalPeg.GalilScaffoldControl.reset 320 x.vm.fpp.program}}⟩ := by
    simp only [PalPeg.GalilScaffoldTop.tickFun, hmode]
    rw [if_pos hatFirst]
    rfl
  rw [hval]
  refine ⟨encControl_fppReset x q henc.1 hbound
    {q.ctl with mode := PalPeg.GalilScaffoldController.Mode.replayStart}
    {x.ctl with mode := PalPeg.GalilScaffoldController.Mode.replayStart} (by rw [← henc.1.ctl]; rfl), ?_⟩
  exact { margins := henc.2.margins
          heads := henc.2.heads
          idleHead := henc.2.idleHead
          fpp := hidle
          idleShape := fun i => ⟨encTape (x.vm.fpp.program.config.tapes i), by
            simpa [Bool.not_not] using henc.2.fpp i⟩
          dp := henc.2.dp
          counters := henc.2.counters
          mirrors := henc.2.mirrors
          places := henc.2.places
          period := henc.2.period
          answer := henc.2.answer }

/-! ### the machine reads from its window what the abstraction knows

Every branch above carries two hypotheses of the same fact, one about the abstract component and
one about the machine's tape.  They are the same fact: the encoding makes the window's centre the
component's own symbol, and the cell below it the sentinel exactly when the component sits on its
first cell. -/

/-- **the symbol the rule reads is the component's own.** -/
theorem focus_iff_of_enc {fppBound dpBound K : ℕ} {margin : ℕ} {w : List (Fin 2)} {x : State GalilVM}
    {q : QPhys fppBound dpBound} {T : Slot → STape Γm} (henc : Enc w margin x (q, T))
    (i : Fin 9) (sym : Fin 9) :
    (T (progSlot q.fppLive i)).focus = encProg sym
      ↔ (x.vm.fpp.program.config.tapes i).focus = sym := by
  have hfpp : T (progSlot q.fppLive i)
      = padLeft margin (mapTape encProg (encTape (x.vm.fpp.program.config.tapes i))) :=
    henc.2.fpp i
  rw [hfpp, focus_padded]
  exact encProg_eq_iff _ _

/-- **the sentinel below the head means the component is on its first cell.** -/
theorem floor_iff_of_enc {fppBound dpBound K : ℕ} {margin : ℕ} {w : List (Fin 2)} {x : State GalilVM}
    {q : QPhys fppBound dpBound} {T : Slot → STape Γm} (henc : Enc w margin x (q, T))
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1) (i : Fin 9) :
    belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) (progSlot q.fppLive i)
        = bottomM
      ↔ (x.vm.fpp.program.config.tapes i).left = [] := by
  have hbelow : belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot q.fppLive i)
      = ((x.vm.fpp.program.config.tapes i).left.map encProg).headD bottomM := by
    show PalPeg.Local.readWin blankM K (tapesOf T (slotIndex (progSlot q.fppLive i)))
      ⟨K - 1, by omega⟩ = _
    have hfpp : T (progSlot q.fppLive i)
        = padLeft margin (mapTape encProg (encTape (x.vm.fpp.program.config.tapes i))) :=
      henc.2.fpp i
    rw [tapesOf_apply, hfpp,
      window_below margin K (mapTape encProg (encTape (x.vm.fpp.program.config.tapes i))) hK1 hKn]
    rfl
  rw [hbelow]
  constructor
  · intro h
    cases hl : (x.vm.fpp.program.config.tapes i).left with
    | nil => rfl
    | cons head rest =>
        rw [hl] at h
        exact absurd h (encProg_ne_bottom head)
  · intro h
    rw [h]
    rfl

/-- one call names at most one action on a slot. -/
theorem progActOf_length (code : List (Instruction 9))
    (m : PalPeg.GalilScaffoldControl.Machine 9) (i : Fin 9) : (progActOf code m i).length ≤ 1 := by
  unfold progActOf
  split
  · simp
  · split
    · split <;> simp
    · split <;> simp
    · split <;> simp
    · simp

/-- **a quantum of `n` calls names at most `n` actions on a slot**, which is what lets the `fpp`
branch of the rule fit inside a window of radius `n`. -/
theorem progRunActs_length (code : List (Instruction 9)) :
    ∀ (n : ℕ) (m : PalPeg.GalilScaffoldControl.Machine 9) (i : Fin 9),
      (progRunActs code n m i).length ≤ n := by
  intro n
  induction n with
  | zero => intro m i; simp [progRunActs]
  | succ n ih =>
      intro m i
      show (progActOf code m i
        ++ progRunActs code n (PalPeg.ProgramFunction.tickFun code true m) i).length ≤ n + 1
      rw [List.length_append]
      have h₁ := progActOf_length code m i
      have h₂ := ih (PalPeg.ProgramFunction.tickFun code true m) i
      omega

/-! ### reading a component's symbol back out of the window

The rule sees the machine's alphabet; the program it is simulating works in the component's.
`decProg` is the way back, and it is exact on everything the encoding can produce — including
the blank, which both alphabets share. -/

/-- the component symbol a machine symbol stands for. -/
def decProg (a : Γm) : Fin 9 :=
  match a with
  | .inr (.inr (.inl s)) => s
  | _ => 6

@[simp] theorem decProg_encProg (s : Fin 9) : decProg (encProg s) = s := by
  unfold decProg encProg
  by_cases h : s = 6
  · rw [if_pos h, h]
    rfl
  · rw [if_neg h]

/-- **so the rule can read a component's symbol from its window.** -/
theorem decProg_centreRead {fppBound dpBound K : ℕ} {margin : ℕ} {w : List (Fin 2)} {x : State GalilVM}
    {q : QPhys fppBound dpBound} {T : Slot → STape Γm} (henc : Enc w margin x (q, T))
    (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i)) (i : Fin 9) :
    decProg (centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
        (progSlot q.fppLive i))
      = (x.vm.fpp.program.config.tapes i).focus := by
  rw [centreRead_of_margin T (progSlot q.fppLive i) (hmargin _)]
  have hfpp : T (progSlot q.fppLive i)
      = padLeft margin (mapTape encProg (encTape (x.vm.fpp.program.config.tapes i))) :=
    henc.2.fpp i
  rw [hfpp, focus_padded, decProg_encProg]

/-- **the component tape a window stands for.**  The rule cannot see a whole tape, only the
`2K+1` cells around the head; this is that stretch read back into the component's alphabet, with
nothing beyond it.  A run of at most `K` calls never looks further, so it cannot tell the
difference. -/
def winTape {K : ℕ} (ws : PalPeg.Local.Window Γm K) : PalPeg.GalilScaffoldTape.Tape :=
  ⟨(List.ofFn (fun j : Fin K => decProg (ws ⟨j.val, by omega⟩))).reverse,
    decProg (ws ⟨K, by omega⟩),
    List.ofFn (fun j : Fin K => decProg (ws ⟨K + 1 + j.val, by omega⟩))⟩

@[simp] theorem winTape_focus {K : ℕ} (ws : PalPeg.Local.Window Γm K) :
    (winTape ws).focus = decProg (ws ⟨K, by omega⟩) := rfl

/-- the machine the rule runs in its head: the program counter and halting bit it carries in its
finite control, on the tapes its windows stand for. -/
noncomputable def winMachine {K : ℕ} (pc : ℕ) (done : Bool) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (live : Bool) : PalPeg.GalilScaffoldControl.Machine 9 :=
  ⟨⟨pc, fun t => winTape (ws (slotIndex (progSlotOf live t)))⟩, done⟩

@[simp] theorem winMachine_pc {K : ℕ} (pc : ℕ) (done : Bool)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (live : Bool) :
    (winMachine pc done ws live).config.pc = pc := rfl

@[simp] theorem winMachine_done {K : ℕ} (pc : ℕ) (done : Bool)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (live : Bool) :
    (winMachine pc done ws live).done = done := rfl

/-- **the head of a window machine's tape carries the component's own symbol.** -/
theorem winMachine_focus {fppBound dpBound K : ℕ} {margin : ℕ} {w : List (Fin 2)} {x : State GalilVM}
    {q : QPhys fppBound dpBound} {T : Slot → STape Γm} (henc : Enc w margin x (q, T))
    (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i)) (pc : ℕ) (done : Bool) (i : Fin 9) :
    ((winMachine pc done (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
        q.fppLive).config.tapes i).focus = (x.vm.fpp.program.config.tapes i).focus := by
  show (winTape (PalPeg.Local.readWin blankM K
    (tapesOf T (slotIndex (progSlotOf q.fppLive i))))).focus = _
  rw [winTape_focus]
  exact decProg_centreRead henc hmargin i

/-- **one call cannot tell the two machines apart.**  The rule's machine and the abstraction's
agree on the halting bit, on the program counter and on every symbol under a head, and
`progActOf_congr` says that is all a call consults. -/
theorem progActOf_winMachine {fppBound dpBound K : ℕ} {margin : ℕ} {w : List (Fin 2)} {x : State GalilVM}
    {q : QPhys fppBound dpBound} {T : Slot → STape Γm} (code : List (Instruction 9))
    (henc : Enc w margin x (q, T)) (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i))
    (pc : ℕ) (done : Bool) (hpc : x.vm.fpp.program.config.pc = pc)
    (hdone : x.vm.fpp.program.done = done) (i : Fin 9) :
    progActOf code (winMachine pc done
        (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) q.fppLive) i
      = progActOf code x.vm.fpp.program i :=
  progActOf_congr code _ _ (by rw [winMachine_done, hdone]) (by rw [winMachine_pc, hpc])
    (fun t => winMachine_focus henc hmargin pc done t) i

/-- **the window tape's head sits at the window's centre.**  Its `K` cells to the left are the
window's left half, so the head is at `K` however far along the real tape the component's head
has walked. -/
@[simp] theorem winTape_pos {K : ℕ} (ws : PalPeg.Local.Window Γm K) :
    PalPeg.Local.pos (encTape (winTape ws)) = K := by
  show (List.ofFn (fun j : Fin K => decProg (ws ⟨j.val, by omega⟩))).reverse.length = K
  simp

/-- **the window tape is the window.**  Laid out from its left end, the tape the rule
reconstructs is exactly the window's `2K+1` cells, decoded. -/
theorem toList_winTape {K : ℕ} (ws : PalPeg.Local.Window Γm K) :
    PalPeg.Local.toList (encTape (winTape ws))
      = List.ofFn (fun j : Fin (2 * K + 1) => decProg (ws j)) := by
  show (List.ofFn (fun j : Fin K => decProg (ws ⟨j.val, by omega⟩))).reverse.reverse
    ++ decProg (ws ⟨K, by omega⟩)
      :: List.ofFn (fun j : Fin K => decProg (ws ⟨K + 1 + j.val, by omega⟩)) = _
  rw [List.reverse_reverse]
  refine List.ext_getElem (by simp; omega) ?_
  intro n h₁ h₂
  rw [List.getElem_ofFn]
  rcases lt_trichotomy n K with hn | hn | hn
  · rw [List.getElem_append_left (by simpa using hn), List.getElem_ofFn]
  · subst hn
    rw [List.getElem_append_right (by simp)]
    simp
  · rw [List.getElem_append_right (by simpa using Nat.le_of_lt hn)]
    simp only [List.length_ofFn]
    obtain ⟨d, hd⟩ : ∃ d, n - K = d + 1 := ⟨n - K - 1, by omega⟩
    simp only [hd, List.getElem_cons_succ, List.getElem_ofFn]
    exact congrArg (fun z => decProg (ws z)) (Fin.ext (show K + 1 + d = n by omega))

/-- so the rule reads the window's `j`-th cell where the reconstructed tape has its `j`-th. -/
theorem rd_winTape {K : ℕ} (ws : PalPeg.Local.Window Γm K) (j : Fin (2 * K + 1)) :
    PalPeg.Local.rd (6 : Fin 9) (encTape (winTape ws)) j.val = decProg (ws j) := by
  show (PalPeg.Local.toList (encTape (winTape ws))).getD j.val (6 : Fin 9) = _
  rw [toList_winTape, List.getD_eq_getElem _ _ (by simpa using j.isLt), List.getElem_ofFn]

/-- laying a component's tape out and re-alphabetising it commute. -/
theorem toList_mapTape {Γ₁ : Type} (f : Γ₁ → Γm) (T : STape Γ₁) :
    PalPeg.Local.toList (mapTape f T) = (PalPeg.Local.toList T).map f := by
  show (T.left.map f).reverse ++ f T.focus :: T.right.map f
    = (T.left.reverse ++ T.focus :: T.right).map f
  rw [List.map_append, List.map_reverse, List.map_cons]

/-- **a cell of the padded tape, above the floor, is the component's own cell.** -/
theorem rd_padded (n : ℕ) (t : PalPeg.GalilScaffoldTape.Tape) (p : ℕ) (hp : n + 1 ≤ p) :
    PalPeg.Local.rd blankM (padLeft n (mapTape encProg (encTape t))) p
      = encProg (PalPeg.Local.rd (6 : Fin 9) (encTape t) (p - n - 1)) := by
  show (PalPeg.Local.toList (padLeft n (mapTape encProg (encTape t)))).getD p blankM = _
  rw [toList_padLeft]
  obtain ⟨k, hk⟩ : ∃ k, p = n + (k + 1) := ⟨p - n - 1, by omega⟩
  subst hk
  rw [getD_replicate_append]
  show (bottomM :: PalPeg.Local.toList (mapTape encProg (encTape t))).getD (k + 1) blankM = _
  rw [List.getD_cons_succ, toList_mapTape]
  show ((PalPeg.Local.toList (encTape t)).map encProg).getD k blankM = _
  rw [show (n + (k + 1)) - n - 1 = k from by omega]
  show _ = encProg ((PalPeg.Local.toList (encTape t)).getD k (6 : Fin 9))
  rcases lt_or_ge k (PalPeg.Local.toList (encTape t)).length with hk' | hk'
  · rw [List.getD_eq_getElem _ _ (by simpa using hk'), List.getD_eq_getElem _ _ hk',
      List.getElem_map]
  · rw [List.getD_eq_default _ _ (by simpa using hk'), List.getD_eq_default _ _ hk']
    rfl

@[simp] theorem pos_mapTape {Γ₁ : Type} (f : Γ₁ → Γm) (T : STape Γ₁) :
    PalPeg.Local.pos (mapTape f T) = PalPeg.Local.pos T := by
  show (T.left.map f).length = T.left.length
  simp

/-- **a window on an encoded tape is the encoding of the window.**  Reading is by position and
the encoding does not move anything, so the two commute. -/
theorem readWin_mapTape {Γ₁ : Type} (f : Γ₁ → Γm) {blank₁ : Γ₁} (hblank : f blank₁ = blankM)
    (K : ℕ) (T : STape Γ₁) (i : Fin (2 * K + 1)) :
    PalPeg.Local.readWin blankM K (mapTape f T) i
      = f (PalPeg.Local.readWin blank₁ K T i) := by
  rw [PalPeg.Local.readWin_eq, PalPeg.Local.readWin_eq, pos_mapTape]
  show (PalPeg.Local.toList (mapTape f T)).getD _ blankM
    = f ((PalPeg.Local.toList T).getD _ blank₁)
  rw [toList_mapTape, ← hblank, List.getD_map]

/-- **the cell below a head, on the slot the machine carries it on.**  A head's view sits on the
machine's tapes under `mapTape encCell`, and reading a window commutes with that, so the cell
below the head of the back slot is the encoding of the cell below the top of the back stack. -/
theorem belowRead_backSlot {K : ℕ} {tapes : Slot → STape Γm} (hK1 : 1 ≤ K) (v : Fin 4)
    (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (stack : List (Option (Fin 2)))
    (hslot : tapes (headSlot v PalPeg.ConcreteLocalMachine.backTape)
      = mapTape encCell (viewTapes PalPeg.ConcreteLocalMachine.backTape))
    (hstack : PalPeg.ConcreteLocalMachine.StackTape
      (viewTapes PalPeg.ConcreteLocalMachine.backTape) stack)
    (hmargin : K ≤ stack.length) :
    belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf tapes tape))
        (headSlot v PalPeg.ConcreteLocalMachine.backTape)
      = encCell (PalPeg.CloseoutCoreEnc18.topSym stack.tail) := by
  have hbelow := hstack.belowSym_eq (K := K) hK1 hmargin
  unfold PalPeg.ConcreteLocalMachine.belowSym at hbelow
  have hidx : PalPeg.Local.idx K (K - 1) = (⟨K - 1, by omega⟩ : Fin (2 * K + 1)) := by
    refine Fin.ext ?_
    show min (K - 1) (2 * K) = K - 1
    omega
  rw [hidx] at hbelow
  show PalPeg.Local.readWin blankM K
    (tapesOf tapes (slotIndex (headSlot v PalPeg.ConcreteLocalMachine.backTape)))
    ⟨K - 1, by omega⟩ = _
  rw [tapesOf_apply, hslot,
    readWin_mapTape encCell (show encCell PalPeg.CloseoutCoreStep.blankc = blankM from by
      unfold encCell
      rw [if_pos rfl]), hbelow]

/-- **the symbol under a head, on the slot the machine carries it on.**  The companion of
`belowRead_backSlot`: the centre of the back slot's window is the encoding of the top of the back
stack, which is the view's own focus. -/
theorem centreRead_backSlot {K : ℕ} {tapes : Slot → STape Γm} (v : Fin 4)
    (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (stack : List (Option (Fin 2)))
    (hslot : tapes (headSlot v PalPeg.ConcreteLocalMachine.backTape)
      = mapTape encCell (viewTapes PalPeg.ConcreteLocalMachine.backTape))
    (hstack : PalPeg.ConcreteLocalMachine.StackTape
      (viewTapes PalPeg.ConcreteLocalMachine.backTape) stack)
    (hmargin : K ≤ stack.length) :
    centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf tapes tape))
        (headSlot v PalPeg.ConcreteLocalMachine.backTape)
      = encCell (PalPeg.CloseoutCoreEnc18.topSym stack) := by
  have hcentre := hstack.centreSym_eq (K := K) hmargin
  unfold PalPeg.ConcreteLocalMachine.centreSym at hcentre
  have hidx : PalPeg.Local.idx K K = (⟨K, by omega⟩ : Fin (2 * K + 1)) := by
    refine Fin.ext ?_
    show min K (2 * K) = K
    omega
  rw [hidx] at hcentre
  show PalPeg.Local.readWin blankM K
    (tapesOf tapes (slotIndex (headSlot v PalPeg.ConcreteLocalMachine.backTape)))
    ⟨K, by omega⟩ = _
  rw [tapesOf_apply, hslot,
    readWin_mapTape encCell (show encCell PalPeg.CloseoutCoreStep.blankc = blankM from by
      unfold encCell
      rw [if_pos rfl]), hcentre]

/-- **the symbol under a head's near head, on the slot the machine carries it on.**  The
companion of `centreRead_backSlot` for the other stack. -/
theorem centreRead_nearSlot {K : ℕ} {tapes : Slot → STape Γm} (v : Fin 4)
    (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (stack : List (Option (Fin 2)))
    (hslot : tapes (headSlot v PalPeg.ConcreteLocalMachine.nearTape)
      = mapTape encCell (viewTapes PalPeg.ConcreteLocalMachine.nearTape))
    (hstack : PalPeg.ConcreteLocalMachine.StackTape
      (viewTapes PalPeg.ConcreteLocalMachine.nearTape) stack)
    (hmargin : K ≤ stack.length) :
    centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf tapes tape))
        (headSlot v PalPeg.ConcreteLocalMachine.nearTape)
      = encCell (PalPeg.CloseoutCoreEnc18.topSym stack) := by
  have hcentre := hstack.centreSym_eq (K := K) hmargin
  unfold PalPeg.ConcreteLocalMachine.centreSym at hcentre
  have hidx : PalPeg.Local.idx K K = (⟨K, by omega⟩ : Fin (2 * K + 1)) := by
    refine Fin.ext ?_
    show min K (2 * K) = K
    omega
  rw [hidx] at hcentre
  show PalPeg.Local.readWin blankM K
    (tapesOf tapes (slotIndex (headSlot v PalPeg.ConcreteLocalMachine.nearTape)))
    ⟨K, by omega⟩ = _
  rw [tapesOf_apply, hslot,
    readWin_mapTape encCell (show encCell PalPeg.CloseoutCoreStep.blankc = blankM from by
      unfold encCell
      rw [if_pos rfl]), hcentre]

/-- **the top of a sealed stack of junk is not a letter.**  Which is what the seal is for: the
machine can tell the cells it stored from the debris under them. -/
theorem topSym_sealed (junk : List (Option (Fin 2)))
    (hsealed : PalPeg.ConcreteLocalMachine.Sealed junk) :
    PalPeg.CloseoutCoreEnc18.topSym junk = PalPeg.CloseoutCoreStep.blankc := by
  cases hj : junk with
  | nil => rfl
  | cons c rest =>
    show PalPeg.CloseoutCoreEnc.cellSym c = _
    cases hc : c with
    | none => rfl
    | some a =>
      exfalso
      apply hsealed a
      rw [hj, hc]
      rfl

/-- **a letter of a view is never the machine's blank.**  The encoding sends the blank cell and
the sentinel to the blank symbol and a letter to its own, so a letter is visible as such. -/
theorem encCell_cellSym_some_ne_blank (b : Fin 2) :
    encCell (PalPeg.CloseoutCoreEnc.cellSym (some b)) ≠ blankM := by
  have hne : PalPeg.CloseoutCoreEnc.cellSym (some b) ≠ PalPeg.CloseoutCoreStep.blankc := by
    simp [PalPeg.CloseoutCoreEnc.cellSym, PalPeg.CloseoutCoreStep.blankc,
      PalPeg.GalilVMEncode.blank, PalPeg.GalilVMEncode.sOpt]
  simp [encCell, hne, blankM]

/-- **the symbol under a head's near head says whether the head has a cell to step onto.**  A
view's near stack holds letters and its debris is sealed, so the near head shows a letter exactly
when the stack is not empty — and that is the reading that tells a step right the machine can
take by itself from one it has to wait for the queue for. -/
theorem centreRead_near_ne_blank_iff {margin K : ℕ} {polarity : Fin 16 → Bool}
    {gap : Fin 4 → Bool} {micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl}
    {fppLive dpLive : Bool} {x : State GalilVM} {tapes : Slot → STape Γm}
    (henc : EncTapes margin x polarity gap micro fppLive dpLive tapes) (hK : K ≤ margin)
    (v : Fin 4) (head : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hhead : headOf x v = some head) :
    centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf tapes tape))
        (headSlot v PalPeg.ConcreteLocalMachine.nearTape) ≠ blankM
      ↔ head.head.right ≠ [] := by
  obtain ⟨view, viewTapes, habs, hrep, hslots, hcells, hwf⟩ := henc.heads v head hhead
  have hviewNear : view.near = head.head.right := by
    have hn : (PalPeg.LocalArrival.absHead' view []).head.right = head.head.right := by rw [habs]
    exact hn
  obtain ⟨bottom, hsealed, hbottomLen, hst⟩ := hrep.near
  have hmarginStack : K ≤ (view.near ++ bottom).length := by
    have hlen : (view.near ++ bottom).length = view.near.length + bottom.length := by
      simp
    omega
  have hcentre : centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf tapes tape))
      (headSlot v PalPeg.ConcreteLocalMachine.nearTape)
      = encCell (PalPeg.CloseoutCoreEnc18.topSym (view.near ++ bottom)) :=
    centreRead_nearSlot v viewTapes (view.near ++ bottom)
      (hslots PalPeg.ConcreteLocalMachine.nearTape) hst hmarginStack
  obtain ⟨nearLetters, hnearLetters⟩ := PalPeg.LocalViewCells.near_letters hcells
  rw [hcentre, ← hviewNear]
  cases hn : view.near with
  | nil =>
    rw [List.nil_append, topSym_sealed bottom hsealed]
    simp [encCell]
  | cons c restNear =>
    obtain ⟨b, hb⟩ : ∃ b : Fin 2, c = some b := by
      rw [hn] at hnearLetters
      cases hl : nearLetters with
      | nil =>
        rw [hl] at hnearLetters
        exact absurd hnearLetters (by simp)
      | cons d ds =>
        refine ⟨d, ?_⟩
        rw [hl] at hnearLetters
        exact (List.cons.inj hnearLetters).1
    subst hb
    show ¬ (encCell (PalPeg.CloseoutCoreEnc.cellSym (some b)) = blankM) ↔ _
    simp [encCell_cellSym_some_ne_blank b]

/-- **the symbol under a head's back head says whether the head has anything behind it.**  A
view holds the left sentinel and then letters, so the top of its back stack is the sentinel
exactly when nothing is behind the head — which is the reading that tells the three cases of a
head's step apart. -/
theorem centreRead_head_ne_sentinel_iff {margin K : ℕ} {polarity : Fin 16 → Bool}
    {gap : Fin 4 → Bool} {micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl}
    {fppLive dpLive : Bool} {x : State GalilVM} {tapes : Slot → STape Γm}
    (henc : EncTapes margin x polarity gap micro fppLive dpLive tapes) (hK : K ≤ margin)
    (v : Fin 4) (head : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hhead : headOf x v = some head) :
    centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf tapes tape))
        (headSlot v PalPeg.ConcreteLocalMachine.backTape)
        ≠ encCell (PalPeg.CloseoutCoreEnc.cellSym none)
      ↔ head.head.left ≠ [] := by
  obtain ⟨view, viewTapes, habs, hrep, hslots, hcells, hwf⟩ := henc.heads v head hhead
  have hviewBack : view.back = head.head.left := by
    have hb : (PalPeg.LocalArrival.absHead' view []).head.left = head.head.left := by rw [habs]
    exact hb
  obtain ⟨bottom, hbottomHeight, hstack⟩ := hrep.back
  have hmarginStack : K ≤ (PalPeg.ConcreteLocalMachine.backStack view ++ bottom).length := by
    have hlen : (PalPeg.ConcreteLocalMachine.backStack view ++ bottom).length
        = view.back.length + 1 + bottom.length := by
      show (view.focus :: view.back ++ bottom).length = _
      simp only [List.length_append, List.length_cons]
    omega
  have hcentre : centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf tapes tape))
      (headSlot v PalPeg.ConcreteLocalMachine.backTape)
      = encCell (PalPeg.CloseoutCoreEnc.cellSym view.focus) := by
    rw [centreRead_backSlot v viewTapes (PalPeg.ConcreteLocalMachine.backStack view ++ bottom)
      (hslots PalPeg.ConcreteLocalMachine.backTape) hstack hmarginStack]
    rfl
  have hsentinel : (encCell (PalPeg.CloseoutCoreEnc.cellSym view.focus)
      = encCell (PalPeg.CloseoutCoreEnc.cellSym none)) ↔ view.focus = none := by
    cases hf : view.focus with
    | none => simp
    | some b =>
      simp only [iff_false, reduceCtorEq, iff_false]
      have hne : PalPeg.CloseoutCoreEnc.cellSym (some b) ≠ PalPeg.CloseoutCoreStep.blankc := by
        simp [PalPeg.CloseoutCoreEnc.cellSym, PalPeg.CloseoutCoreStep.blankc,
          PalPeg.GalilVMEncode.blank, PalPeg.GalilVMEncode.sOpt]
      rw [show encCell (PalPeg.CloseoutCoreEnc.cellSym (some b))
          = (.inr (.inl (PalPeg.CloseoutCoreEnc.cellSym (some b))) : Γm) from if_neg hne,
        show encCell (PalPeg.CloseoutCoreEnc.cellSym none) = blankM from by decide]
      simp [blankM]
  rw [hcentre, ← hviewBack]
  constructor
  · intro hne hnil
    exact hne (hsentinel.mpr ((PalPeg.LocalViewCells.back_nil_iff_focus_none hcells).mp hnil))
  · intro hne hEq
    exact hne ((PalPeg.LocalViewCells.back_nil_iff_focus_none hcells).mpr (hsentinel.mp hEq))

/-- **a head's step right, on the slots of the whole machine**, while the cell it steps onto is
on its near stack.  As with the step left, the three actions name only symbols the rule reads off
its own windows: the back stack writes back its own symbol, steps right, and writes the near
stack's symbol where it now stands, and the near stack writes back its own symbol and steps
left. -/
theorem headSlots_rightOn {margin K : ℕ} {polarity : Fin 16 → Bool} {gap : Fin 4 → Bool}
    {micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl} {fppLive dpLive : Bool}
    {x : State GalilVM} {T : Slot → STape Γm}
    (henc : EncTapes margin x polarity gap micro fppLive dpLive T)
    (v : Fin 4) (head : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hhead : headOf x v = some head) (hgap : head.gap = true)
    (a : Option (Fin 2)) (rest : List (Option (Fin 2))) (hnear : head.head.right = a :: rest)
    (newTapes : Slot → STape Γm)
    (hbackSlot : newTapes (headSlot v PalPeg.ConcreteLocalMachine.backTape)
      = PalPeg.CloseoutCoreEnc12.actList blankM
          (T (headSlot v PalPeg.ConcreteLocalMachine.backTape))
          [some ((T (headSlot v PalPeg.ConcreteLocalMachine.backTape)).focus,
              (.right : PalPeg.CloseoutCoreEnc12.MoveC)),
            some ((T (headSlot v PalPeg.ConcreteLocalMachine.nearTape)).focus,
              (.stay : PalPeg.CloseoutCoreEnc12.MoveC))])
    (hnearSlot : newTapes (headSlot v PalPeg.ConcreteLocalMachine.nearTape)
      = PalPeg.CloseoutCoreEnc12.actOnG blankM
          (T (headSlot v PalPeg.ConcreteLocalMachine.nearTape))
          (some ((T (headSlot v PalPeg.ConcreteLocalMachine.nearTape)).focus,
            (.left : PalPeg.CloseoutCoreEnc12.MoveC))))
    (hotherSlot : ∀ t, t ≠ PalPeg.ConcreteLocalMachine.backTape →
      t ≠ PalPeg.ConcreteLocalMachine.nearTape →
      newTapes (headSlot v t) = T (headSlot v t)) :
    ∃ (view : PalPeg.LocalInputView.InputView)
        (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc),
      PalPeg.LocalArrival.absHead' view []
          = PalPeg.GalilScaffoldChainVerifier.right head ∧
        PalPeg.ConcreteLocalMachine.ViewRep margin view false (micro v) viewTapes ∧
        (∀ i, newTapes (headSlot v i) = mapTape encCell (viewTapes i)) ∧
          PalPeg.LocalViewCells.ViewCells view ∧ PalPeg.LocalInputView.WF view := by
  obtain ⟨view, viewTapes, habs, hrep, hold, hcells, hwf⟩ := henc.heads v head hhead
  have hviewNear : view.near = a :: rest := by
    have hn : (PalPeg.LocalArrival.absHead' view []).head.right = head.head.right := by rw [habs]
    rw [← hnear]
    exact hn
  have hviewGap : view.gap = true := by
    have hg : (PalPeg.LocalArrival.absHead' view []).gap = head.gap := by rw [habs]
    rw [← hgap]
    exact hg
  have hgapBit : gap v = true := by rw [hrep.gap, hviewGap]
  have hrep' : PalPeg.ConcreteLocalMachine.ViewRep margin view true (micro v) viewTapes := by
    rw [← hgapBit]
    exact hrep
  have hnearFocus : (viewTapes PalPeg.ConcreteLocalMachine.nearTape).focus
      = PalPeg.CloseoutCoreEnc.cellSym a := by
    obtain ⟨bottom, -, -, hst⟩ := hrep'.near
    have hstack : view.near ++ bottom = a :: (rest ++ bottom) := by
      rw [hviewNear]
      rfl
    rw [hstack] at hst
    rw [stackTape_focus _ _ hst]
    rfl
  have hmapNear : (mapTape encCell (viewTapes PalPeg.ConcreteLocalMachine.nearTape)).focus
      = encCell (PalPeg.CloseoutCoreEnc.cellSym a) := by
    show encCell (viewTapes PalPeg.ConcreteLocalMachine.nearTape).focus = _
    rw [hnearFocus]
  refine ⟨rightViewOn view a rest, rightViewTapes viewTapes a,
    habs.symm ▸ absHead_rightViewOn view hviewGap a rest hviewNear,
    viewRep_rightOn view (micro v) viewTapes (rightViewTapes viewTapes a) a rest hviewNear hrep'
      ?_ ?_ ?_, ?_, viewCells_rightViewOn view a rest hviewNear hcells, hwf⟩
  · unfold rightViewTapes
    rw [if_pos rfl]
  · unfold rightViewTapes
    rw [if_neg (by decide), if_pos rfl]
  · intro t hbackT hnearT
    unfold rightViewTapes
    rw [if_neg hbackT, if_neg hnearT]
  · intro i
    by_cases hb : i = PalPeg.ConcreteLocalMachine.backTape
    · subst hb
      rw [hbackSlot, encCell_rightViewTapes_back,
        hold PalPeg.ConcreteLocalMachine.backTape, hold PalPeg.ConcreteLocalMachine.nearTape,
        hmapNear]
    · by_cases hn : i = PalPeg.ConcreteLocalMachine.nearTape
      · subst hn
        rw [hnearSlot, encCell_rightViewTapes_near,
          hold PalPeg.ConcreteLocalMachine.nearTape, hmapNear]
      · rw [hotherSlot i hb hn, encCell_rightViewTapes_other viewTapes a i hb hn, hold i]

/-- **a head that steps left for free, on the slots of the whole machine.**  Two of the three
cases of a head's step move no tape: the head stands on a gap, or it stands on a letter with
nothing behind it.  The rule tells them from the third by one reading, the symbol under the back
head, and in both of them the twelve tapes it already had represent the head it becomes. -/
theorem headSlots_still {margin K : ℕ} {polarity : Fin 16 → Bool} {gap : Fin 4 → Bool}
    {micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl} {fppLive dpLive : Bool}
    {x : State GalilVM} {tapes : Slot → STape Γm}
    (henc : EncTapes margin x polarity gap micro fppLive dpLive tapes) (hK : K ≤ margin)
    (v : Fin 4) (head : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hhead : headOf x v = some head)
    (hfree : gap v = true ∨
      centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf tapes tape))
          (headSlot v PalPeg.ConcreteLocalMachine.backTape)
        = encCell (PalPeg.CloseoutCoreEnc.cellSym none))
    (newTapes : Slot → STape Γm)
    (hsame : ∀ i, newTapes (headSlot v i) = tapes (headSlot v i)) :
    ∃ (view : PalPeg.LocalInputView.InputView)
        (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc),
      PalPeg.LocalArrival.absHead' view []
          = PalPeg.GalilScaffoldInputHead.left head ∧
        PalPeg.ConcreteLocalMachine.ViewRep margin view (!gap v) (micro v) viewTapes ∧
        (∀ i, newTapes (headSlot v i) = mapTape encCell (viewTapes i)) ∧
          PalPeg.LocalViewCells.ViewCells view ∧ PalPeg.LocalInputView.WF view := by
  obtain ⟨view, viewTapes, habs, hrep, hslots, hcells, hwf⟩ := henc.heads v head hhead
  have hslots' : ∀ i, newTapes (headSlot v i) = mapTape encCell (viewTapes i) := by
    intro i
    rw [hsame i]
    exact hslots i
  cases hgapBit : gap v
  · have hviewGap : view.gap = false := by rw [← hrep.gap, hgapBit]
    have hcentre : centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf tapes tape))
        (headSlot v PalPeg.ConcreteLocalMachine.backTape)
        = encCell (PalPeg.CloseoutCoreEnc.cellSym none) := by
      cases hfree with
      | inl hg => exact absurd (hgapBit ▸ hg) (by simp)
      | inr hc => exact hc
    obtain ⟨bottom, hbottomHeight, hstack⟩ := hrep.back
    have hmarginStack : K ≤ (PalPeg.ConcreteLocalMachine.backStack view ++ bottom).length := by
      have hlen : (PalPeg.ConcreteLocalMachine.backStack view ++ bottom).length
          = view.back.length + 1 + bottom.length := by
        show (view.focus :: view.back ++ bottom).length = _
        simp only [List.length_append, List.length_cons]
      omega
    have hfocus : view.focus = none := by
      have hread : centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf tapes tape))
          (headSlot v PalPeg.ConcreteLocalMachine.backTape)
          = encCell (PalPeg.CloseoutCoreEnc.cellSym view.focus) := by
        rw [centreRead_backSlot v viewTapes (PalPeg.ConcreteLocalMachine.backStack view ++ bottom)
          (hslots PalPeg.ConcreteLocalMachine.backTape) hstack hmarginStack]
        rfl
      rw [hread] at hcentre
      cases hf : view.focus with
      | none => rfl
      | some b =>
        exfalso
        rw [hf] at hcentre
        have hne : PalPeg.CloseoutCoreEnc.cellSym (some b) ≠ PalPeg.CloseoutCoreStep.blankc := by
          simp [PalPeg.CloseoutCoreEnc.cellSym, PalPeg.CloseoutCoreStep.blankc,
            PalPeg.GalilVMEncode.blank, PalPeg.GalilVMEncode.sOpt]
        rw [show encCell (PalPeg.CloseoutCoreEnc.cellSym (some b))
            = (.inr (.inl (PalPeg.CloseoutCoreEnc.cellSym (some b))) : Γm) from if_neg hne,
          show encCell (PalPeg.CloseoutCoreEnc.cellSym none) = blankM from by decide] at hcentre
        simp [blankM] at hcentre
    have hback : view.back = [] := (PalPeg.LocalViewCells.back_nil_iff_focus_none hcells).mpr hfocus
    have hrep' : PalPeg.ConcreteLocalMachine.ViewRep margin view false (micro v) viewTapes := by
      rw [← hgapBit]
      exact hrep
    obtain ⟨habs', hrep''⟩ := headRep_leftEmpty view viewTapes hback hviewGap hrep'
    exact ⟨leftView view, viewTapes, habs.symm ▸ habs', hrep'', hslots',
      by
        rw [show leftView view = {view with gap := true} from by unfold leftView; rw [hback]]
        exact viewCells_setGap view true hcells, wf_leftView view hwf⟩
  · have hviewGap : view.gap = true := by rw [← hrep.gap, hgapBit]
    have hrep' : PalPeg.ConcreteLocalMachine.ViewRep margin view true (micro v) viewTapes := by
      rw [← hgapBit]
      exact hrep
    obtain ⟨habs', hrep''⟩ := headRep_leftGap view viewTapes hviewGap hrep'
    exact ⟨{view with gap := false}, viewTapes, habs.symm ▸ habs', hrep'', hslots',
      viewCells_setGap view false hcells, hwf⟩

/-- **a head's step, from the actions the rule names.**  One guard — the head's own bit, or the
symbol under its back head being the sentinel — tells the step that moves two stacks from the two
that move nothing, and either way what comes out is a view of the head one step left on tapes the
encoding accepts. -/
theorem headSlots_step {margin K : ℕ} {polarity : Fin 16 → Bool} {gap : Fin 4 → Bool}
    {micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl} {fppLive dpLive : Bool}
    {x : State GalilVM} {T : Slot → STape Γm}
    (henc : EncTapes margin x polarity gap micro fppLive dpLive T) (hK : K ≤ margin)
    (v : Fin 4) (head : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hhead : headOf x v = some head) (newTapes : Slot → STape Γm)
    (hslots : ∀ t : Fin 12, newTapes (headSlot v t)
      = PalPeg.CloseoutCoreEnc12.actList blankM (T (headSlot v t))
          (if gap v
                || decide (centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
                    (headSlot v PalPeg.ConcreteLocalMachine.backTape)
                  = encCell (PalPeg.CloseoutCoreEnc.cellSym none)) then []
            else if t = PalPeg.ConcreteLocalMachine.backTape then
              [some (centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
                  (headSlot v PalPeg.ConcreteLocalMachine.backTape),
                (.left : PalPeg.CloseoutCoreEnc12.MoveC))]
            else if t = PalPeg.ConcreteLocalMachine.nearTape then
              [some (centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
                  (headSlot v PalPeg.ConcreteLocalMachine.nearTape),
                  (.right : PalPeg.CloseoutCoreEnc12.MoveC)),
                some (centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
                  (headSlot v PalPeg.ConcreteLocalMachine.backTape),
                  (.stay : PalPeg.CloseoutCoreEnc12.MoveC))]
            else [])) :
    ∃ (view : PalPeg.LocalInputView.InputView)
        (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc),
      PalPeg.LocalArrival.absHead' view []
          = PalPeg.GalilScaffoldInputHead.left head ∧
        PalPeg.ConcreteLocalMachine.ViewRep margin view (!gap v) (micro v) viewTapes ∧
        (∀ i, newTapes (headSlot v i) = mapTape encCell (viewTapes i)) ∧
          PalPeg.LocalViewCells.ViewCells view ∧ PalPeg.LocalInputView.WF view := by
  have hcentreEq : ∀ t : Fin 12,
      centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) (headSlot v t)
        = (T (headSlot v t)).focus :=
    fun t => centreRead_of_margin T (headSlot v t) (le_trans hK (henc.margins _))
  by_cases hguard : (gap v
      || decide (centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (headSlot v PalPeg.ConcreteLocalMachine.backTape)
        = encCell (PalPeg.CloseoutCoreEnc.cellSym none))) = true
  · refine headSlots_still henc hK v head hhead ?_ newTapes (fun i => by
      rw [hslots i, if_pos hguard]
      rfl)
    rcases (Bool.or_eq_true _ _).mp hguard with hg | hc
    · exact Or.inl hg
    · exact Or.inr (of_decide_eq_true hc)
  · have hsplit := Bool.or_eq_false_iff.mp (by
      cases hval : (gap v
          || decide (centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
              (headSlot v PalPeg.ConcreteLocalMachine.backTape)
            = encCell (PalPeg.CloseoutCoreEnc.cellSym none))) with
      | false => rfl
      | true => exact absurd hval hguard)
    have hgapFalse : gap v = false := hsplit.1
    have hnotSentinel : centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
        (headSlot v PalPeg.ConcreteLocalMachine.backTape)
        ≠ encCell (PalPeg.CloseoutCoreEnc.cellSym none) := of_decide_eq_false hsplit.2
    have hleftNe : head.head.left ≠ [] :=
      (centreRead_head_ne_sentinel_iff henc hK v head hhead).mp hnotSentinel
    obtain ⟨a, tail, hleft⟩ : ∃ a tail, head.head.left = a :: tail := by
      cases hl : head.head.left with
      | nil => exact absurd hl hleftNe
      | cons b bs => exact ⟨b, bs, rfl⟩
    have hheadGap : head.gap = false := by
      obtain ⟨view, viewTapes, habs, hrep, -, -⟩ := henc.heads v head hhead
      have hg : (PalPeg.LocalArrival.absHead' view []).gap = head.gap := by rw [habs]
      rw [← hg]
      show view.gap = false
      rw [← hrep.gap]
      exact hgapFalse
    have hres := headSlots_left henc v head hhead hheadGap a tail hleft newTapes
      (by
        rw [hslots PalPeg.ConcreteLocalMachine.backTape, if_neg hguard, if_pos rfl,
          hcentreEq PalPeg.ConcreteLocalMachine.backTape]
        rfl)
      (by
        rw [hslots PalPeg.ConcreteLocalMachine.nearTape, if_neg hguard, if_neg (by decide),
          if_pos rfl, hcentreEq PalPeg.ConcreteLocalMachine.nearTape,
          hcentreEq PalPeg.ConcreteLocalMachine.backTape])
      (fun t hb hn => by
        rw [hslots t, if_neg hguard, if_neg hb, if_neg hn]
        rfl)
    rw [hgapFalse]
    exact hres

/-- the actions one head's step right names on its own two stacks, while the cell it steps onto
is on its near stack.  The guard is the head's own bit together with the reading that says the
near stack is not empty; the case the guard sends to nothing is the free half-step, and the case
where the near stack is empty but the queue is not belongs to the micro-schedule. -/
noncomputable def headRightActs {fppBound dpBound K : ℕ} (q : QPhys fppBound dpBound) (v : Fin 4)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (t : Fin 12) :
    List (PalPeg.CloseoutCoreEnc12.Act Γm) :=
  if !q.gap v
      || decide (centreRead ws (headSlot v PalPeg.ConcreteLocalMachine.nearTape) = blankM) then []
    else if t = PalPeg.ConcreteLocalMachine.backTape then
      [some (centreRead ws (headSlot v PalPeg.ConcreteLocalMachine.backTape),
          (.right : PalPeg.CloseoutCoreEnc12.MoveC)),
        some (centreRead ws (headSlot v PalPeg.ConcreteLocalMachine.nearTape),
          (.stay : PalPeg.CloseoutCoreEnc12.MoveC))]
    else if t = PalPeg.ConcreteLocalMachine.nearTape then
      [some (centreRead ws (headSlot v PalPeg.ConcreteLocalMachine.nearTape),
        (.left : PalPeg.CloseoutCoreEnc12.MoveC))]
    else []

theorem headRightActs_length {fppBound dpBound K : ℕ} (q : QPhys fppBound dpBound) (v : Fin 4)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (t : Fin 12) :
    (headRightActs q v ws t).length ≤ 2 := by
  unfold headRightActs
  split_ifs <;> simp

/-- **a head's step right, from the actions the rule names**, in the two cases the head can take
by itself: it stands on a letter, so only its bit moves, or it stands on a gap with a cell on its
near stack, so two stacks move.  The case where the near stack is empty and the queue is not is
excluded by the hypothesis, and is the micro-schedule's. -/
theorem headSlots_rightStep {margin K : ℕ} {polarity : Fin 16 → Bool} {gap : Fin 4 → Bool}
    {micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl} {fppLive dpLive : Bool}
    {x : State GalilVM} {T : Slot → STape Γm} {fppBound dpBound : ℕ}
    (henc : EncTapes margin x polarity gap micro fppLive dpLive T) (hK : K ≤ margin)
    (q : QPhys fppBound dpBound) (hqgap : q.gap = gap)
    (v : Fin 4) (head : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hhead : headOf x v = some head) (newTapes : Slot → STape Γm)
    (hcase : gap v = false
      ∨ centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (headSlot v PalPeg.ConcreteLocalMachine.nearTape) ≠ blankM)
    (hslots : ∀ t : Fin 12, newTapes (headSlot v t)
      = PalPeg.CloseoutCoreEnc12.actList blankM (T (headSlot v t))
          (headRightActs q v (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) t)) :
    ∃ (view : PalPeg.LocalInputView.InputView)
        (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc),
      PalPeg.LocalArrival.absHead' view []
          = PalPeg.GalilScaffoldChainVerifier.right head ∧
        PalPeg.ConcreteLocalMachine.ViewRep margin view (!gap v) (micro v) viewTapes ∧
        (∀ i, newTapes (headSlot v i) = mapTape encCell (viewTapes i)) ∧
          PalPeg.LocalViewCells.ViewCells view ∧ PalPeg.LocalInputView.WF view := by
  subst hqgap
  have hcentreEq : ∀ t : Fin 12,
      centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) (headSlot v t)
        = (T (headSlot v t)).focus :=
    fun t => centreRead_of_margin T (headSlot v t) (le_trans hK (henc.margins _))
  cases hgapBit : q.gap v
  · obtain ⟨view, viewTapes, habs, hrep, hold, hcells, hwf⟩ := henc.heads v head hhead
    have hviewGap : view.gap = false := by rw [← hrep.gap, hgapBit]
    have hheadGap : head.gap = false := by
      have hg : (PalPeg.LocalArrival.absHead' view []).gap = head.gap := by rw [habs]
      rw [← hg]
      exact hviewGap
    have hrep' : PalPeg.ConcreteLocalMachine.ViewRep margin view false (micro v) viewTapes := by
      rw [← hgapBit]
      exact hrep
    obtain ⟨habs', hrep''⟩ := headRep_rightGap view viewTapes hviewGap hrep'
    refine ⟨{view with gap := true}, viewTapes, habs.symm ▸ habs', ?_, ?_,
      viewCells_setGap view true hcells, hwf⟩
    · exact hrep''
    · intro i
      rw [hslots i, show headRightActs q v _ i = [] from by
        unfold headRightActs
        rw [if_pos (by rw [hgapBit]; simp)]]
      exact hold i
  · have hnotBlank : centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
        (headSlot v PalPeg.ConcreteLocalMachine.nearTape) ≠ blankM := by
      cases hcase with
      | inl hg => exact absurd (hgapBit ▸ hg) (by simp)
      | inr hc => exact hc
    have hnearNe : head.head.right ≠ [] :=
      (centreRead_near_ne_blank_iff henc hK v head hhead).mp hnotBlank
    obtain ⟨a, rest, hnear⟩ : ∃ a rest, head.head.right = a :: rest := by
      cases hl : head.head.right with
      | nil => exact absurd hl hnearNe
      | cons b bs => exact ⟨b, bs, rfl⟩
    have hheadGap : head.gap = true := by
      obtain ⟨view, viewTapes, habs, hrep, -, -⟩ := henc.heads v head hhead
      have hg : (PalPeg.LocalArrival.absHead' view []).gap = head.gap := by rw [habs]
      rw [← hg]
      show view.gap = true
      rw [← hrep.gap]
      exact hgapBit
    have hguard : ∀ t : Fin 12,
        headRightActs q v (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) t
          = (if t = PalPeg.ConcreteLocalMachine.backTape then
              [some ((T (headSlot v PalPeg.ConcreteLocalMachine.backTape)).focus,
                  (.right : PalPeg.CloseoutCoreEnc12.MoveC)),
                some ((T (headSlot v PalPeg.ConcreteLocalMachine.nearTape)).focus,
                  (.stay : PalPeg.CloseoutCoreEnc12.MoveC))]
            else if t = PalPeg.ConcreteLocalMachine.nearTape then
              [some ((T (headSlot v PalPeg.ConcreteLocalMachine.nearTape)).focus,
                (.left : PalPeg.CloseoutCoreEnc12.MoveC))]
            else []) := by
      intro t
      unfold headRightActs
      rw [if_neg (by
          rw [hgapBit]
          simpa using hnotBlank),
        hcentreEq PalPeg.ConcreteLocalMachine.backTape,
        hcentreEq PalPeg.ConcreteLocalMachine.nearTape]
    have hres := headSlots_rightOn (K := K) henc v head hhead hheadGap a rest hnear newTapes
      (by rw [hslots PalPeg.ConcreteLocalMachine.backTape,
        hguard PalPeg.ConcreteLocalMachine.backTape, if_pos rfl])
      (by
        rw [hslots PalPeg.ConcreteLocalMachine.nearTape,
          hguard PalPeg.ConcreteLocalMachine.nearTape, if_neg (by decide), if_pos rfl]
        rfl)
      (fun t hb hn => by
        rw [hslots t, hguard t, if_neg hb, if_neg hn]
        rfl)
    exact hres

/-- **reading a cell back out of the machine's alphabet.**  The machine's alphabet has a summand
for the cells of a view, so a symbol of that summand is a cell and everything else — the
machine's blank included — reads back as the blank cell.  A rule may use this: it is a function
of one symbol, so it is part of reading a window. -/
def decCell (g : Γm) : PalPeg.CloseoutCoreStep.Γc :=
  match g with
  | .inr (.inl c) => c
  | _ => PalPeg.CloseoutCoreStep.blankc

@[simp] theorem decCell_encCell (c : PalPeg.CloseoutCoreStep.Γc) : decCell (encCell c) = c := by
  unfold encCell
  by_cases h : c = PalPeg.CloseoutCoreStep.blankc
  · rw [if_pos h, h]
    rfl
  · rw [if_neg h]
    rfl

/-- **the windows of a head's twelve slots, read in the view's own alphabet.**  The machine keeps
a head's tapes as the encoded tapes of a view, so decoding cell by cell is all it takes to hand
the view layer the windows it expects.

Naming it is what lets the rows that read a head — the actions it names, and the symbol its
cursor is about to reach — be stated against the view layer's own observations. -/
noncomputable def viewWindows {K : ℕ} (v : Fin 4) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) :
    Fin 12 → PalPeg.Local.Window PalPeg.CloseoutCoreStep.Γc K :=
  fun tape i => decCell (ws (slotIndex (headSlot v tape)) i)

/-- **and on encoded tapes those are the view's own windows.** -/
theorem viewWindows_of_encoded {K : ℕ} (v : Fin 4) (T : Slot → STape Γm)
    (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (hold : ∀ t, T (headSlot v t) = mapTape encCell (viewTapes t)) :
    viewWindows v (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = fun tape => PalPeg.Local.readWin PalPeg.CloseoutCoreStep.blankc K (viewTapes tape) := by
  funext tape i
  show decCell (PalPeg.Local.readWin blankM K (tapesOf T (slotIndex (headSlot v tape))) i) = _
  rw [tapesOf_apply, hold tape, readWin_mapTape encCell (by rw [encCell]; rw [if_pos rfl]),
    decCell_encCell]

/-- **the actions the machine names on the twelve slots of a head: the view layer's own, through
the encoding.**  The rule reads the head's own windows, decodes them to cells, asks the view
layer what a view does on this step of the slot under this command, and sends those actions back
through the encoding.  Nothing here is hand-rolled: the case analysis of a head's step — the
half-steps, the stack that moves, the arrival that goes to the queue — is the view layer's. -/
noncomputable def headViewActs {fppBound dpBound K : ℕ} (hK : 2 ≤ K)
    (q : QPhys fppBound dpBound) (v : Fin 4) (slot : Fin 11)
    (command : PalPeg.ConcreteLocalMachine.ViewCommand)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (t : Fin 12) :
    List (PalPeg.CloseoutCoreEnc12.Act Γm) :=
  (PalPeg.ConcreteLocalMachine.viewActs (Fin 2) hK slot command (viewControlOf q v)
    (viewWindows v ws) t).map (encAct encCell)

theorem headViewActs_length {fppBound dpBound K : ℕ} (hK : 2 ≤ K)
    (q : QPhys fppBound dpBound) (v : Fin 4) (slot : Fin 11)
    (command : PalPeg.ConcreteLocalMachine.ViewCommand)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (t : Fin 12) :
    (headViewActs hK q v slot command ws t).length ≤ K := by
  unfold headViewActs
  rw [List.length_map]
  exact PalPeg.ConcreteLocalMachine.viewActs_length (Fin 2) hK slot command _ _ t

/-- **on the encoded tapes of a view, those actions are the view's own actions read off the
view's own windows.**  Decoding what the machine reads off an encoded tape gives back what the
view reads off its own tape, so the rule and the view layer are looking at the same windows. -/
theorem headViewActs_encoded {fppBound dpBound K : ℕ} (hK : 2 ≤ K)
    (q : QPhys fppBound dpBound) (v : Fin 4) (slot : Fin 11)
    (command : PalPeg.ConcreteLocalMachine.ViewCommand)
    (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc) (T : Slot → STape Γm)
    (hold : ∀ t, T (headSlot v t) = mapTape encCell (viewTapes t)) (t : Fin 12) :
    headViewActs hK q v slot command (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) t
      = (PalPeg.ConcreteLocalMachine.viewActs (Fin 2) hK slot command (viewControlOf q v)
          (fun tape => PalPeg.Local.readWin PalPeg.CloseoutCoreStep.blankc K (viewTapes tape))
          t).map (encAct encCell) := by
  unfold headViewActs
  congr 1
  congr 1
  funext tape i
  show decCell (PalPeg.Local.readWin blankM K (tapesOf T (slotIndex (headSlot v tape))) i) = _
  rw [tapesOf_apply, hold tape, readWin_mapTape encCell (by rw [encCell]; rw [if_pos rfl]),
    decCell_encCell]

/-- **a step of the machine on the twelve slots of a head is a step of that head's view.**  The
machine keeps a head's tapes as the encoded tapes of a view, so if the actions the rule names on
those slots are the actions the view layer's own rule names — read off the same windows, through
the encoding — then the slots afterwards are the encoded tapes of the view one step later, and
the view layer's `ViewStep` holds of it.  This is the bridge that lets `viewSlot_sound` speak
about the machine: eleven of these are one command of the view. -/
theorem viewStep_of_encodedActs {K : ℕ} (hK : 2 ≤ K) (slot : Fin 11)
    (command : PalPeg.ConcreteLocalMachine.ViewCommand)
    (control : PalPeg.ConcreteLocalMachine.ViewControl)
    (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (T newTapes : Slot → STape Γm) (embed : Fin 12 → Slot)
    (hold : ∀ t, T (embed t) = mapTape encCell (viewTapes t))
    (hslots : ∀ t, newTapes (embed t)
      = PalPeg.CloseoutCoreEnc12.actList blankM (T (embed t))
          ((PalPeg.ConcreteLocalMachine.viewActs (Fin 2) hK slot command control
            (fun tape => PalPeg.Local.readWin PalPeg.CloseoutCoreStep.blankc K (viewTapes tape))
            t).map (encAct encCell))) :
    ∃ viewTapes' : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc,
      (∀ t, newTapes (embed t) = mapTape encCell (viewTapes' t)) ∧
        PalPeg.ConcreteLocalMachine.ViewStep (Fin 2) hK slot command (control, viewTapes)
          (PalPeg.ConcreteLocalMachine.viewNext (Fin 2) hK slot command control
              (fun tape =>
                PalPeg.Local.readWin PalPeg.CloseoutCoreStep.blankc K (viewTapes tape)),
            viewTapes') := by
  refine ⟨fun t => PalPeg.CloseoutCoreEnc12.actList PalPeg.CloseoutCoreStep.blankc (viewTapes t)
      (PalPeg.ConcreteLocalMachine.viewActs (Fin 2) hK slot command control
        (fun tape => PalPeg.Local.readWin PalPeg.CloseoutCoreStep.blankc K (viewTapes tape)) t),
    fun t => ?_, rfl, fun t _ => ⟨rfl, fun _ => rfl⟩⟩
  rw [hslots t, hold t, ← mapTape_actList encCell (by rw [encCell]; rw [if_pos rfl])]

/-- **one step of a head, from the actions the rule names, is a step of that head's view.**  This
is the composition of the two halves: the rule's actions on a head's slots are the view layer's
own actions read off the view's own windows, and a step that follows them takes the encoded
tapes of a view to the encoded tapes of the view one step later.  Eleven of these, chained
through `viewSlot_sound`, are one command of the view. -/
theorem viewStep_of_headViewActs {fppBound dpBound K : ℕ} (hK : 2 ≤ K)
    (q : QPhys fppBound dpBound) (v : Fin 4) (slot : Fin 11)
    (command : PalPeg.ConcreteLocalMachine.ViewCommand)
    (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc) (T newTapes : Slot → STape Γm)
    (hold : ∀ t, T (headSlot v t) = mapTape encCell (viewTapes t))
    (hslots : ∀ t, newTapes (headSlot v t)
      = PalPeg.CloseoutCoreEnc12.actList blankM (T (headSlot v t))
          (headViewActs hK q v slot command
            (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) t)) :
    ∃ viewTapes' : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc,
      (∀ t, newTapes (headSlot v t) = mapTape encCell (viewTapes' t)) ∧
        PalPeg.ConcreteLocalMachine.ViewStep (Fin 2) hK slot command
          (viewControlOf q v, viewTapes)
          (PalPeg.ConcreteLocalMachine.viewNext (Fin 2) hK slot command (viewControlOf q v)
              (fun tape =>
                PalPeg.Local.readWin PalPeg.CloseoutCoreStep.blankc K (viewTapes tape)),
            viewTapes') :=
  viewStep_of_encodedActs hK slot command (viewControlOf q v) viewTapes T newTapes (headSlot v)
    hold (fun t => by
      rw [hslots t, headViewActs_encoded hK q v slot command viewTapes T hold t])

/-- the control of a view after one step of a slot, as the finite control computes it: the view
layer's own `viewNext`, on the command the control carries for that view and on the windows of
that head's own slots, decoded to cells. -/
noncomputable def viewNextOfHead {fppBound dpBound K : ℕ} (hK : 2 ≤ K)
    (q : QPhys fppBound dpBound) (v : Fin 4) (slot : Fin 11)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) :
    PalPeg.ConcreteLocalMachine.ViewControl :=
  PalPeg.ConcreteLocalMachine.viewNext (Fin 2) hK slot (q.commands v) (viewControlOf q v)
    (fun tape i => decCell (ws (slotIndex (headSlot v tape)) i))

/-- **on the encoded tapes of a view, that is the view layer's own next control**, read off the
view's own windows.  Same reason as for the actions: decoding what the machine reads off an
encoded tape gives back what the view reads off its own tape. -/
theorem viewNextOfHead_encoded {fppBound dpBound K : ℕ} (hK : 2 ≤ K)
    (q : QPhys fppBound dpBound) (v : Fin 4) (slot : Fin 11)
    (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc) (T : Slot → STape Γm)
    (hold : ∀ t, T (headSlot v t) = mapTape encCell (viewTapes t)) :
    viewNextOfHead hK q v slot (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = PalPeg.ConcreteLocalMachine.viewNext (Fin 2) hK slot (q.commands v) (viewControlOf q v)
          (fun tape =>
            PalPeg.Local.readWin PalPeg.CloseoutCoreStep.blankc K (viewTapes tape)) := by
  unfold viewNextOfHead
  congr 1
  funext tape i
  show decCell (PalPeg.Local.readWin blankM K (tapesOf T (slotIndex (headSlot v tape))) i) = _
  rw [tapesOf_apply, hold tape, readWin_mapTape encCell (by rw [encCell]; rw [if_pos rfl]),
    decCell_encCell]

/-- **one step of a slot, on the part of the finite control that belongs to the heads.**  The
three fields a view's control is made of — its gap bit, its queue job and the control of its
micro-schedule — go to what the view layer's own rule says; the micro-operation of the last step
is free, so the field keeps its own. -/
noncomputable def headControlStep {fppBound dpBound K : ℕ} (hK : 2 ≤ K)
    (q : QPhys fppBound dpBound) (slot : Fin 11)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) : QPhys fppBound dpBound :=
  { q with
    gap := fun v => (viewNextOfHead hK q v slot ws).1
    job := fun v => (viewNextOfHead hK q v slot ws).2.1
    micro := fun v => ((q.micro v).1, (viewNextOfHead hK q v slot ws).2.2) }

@[simp] theorem viewControlOf_headControlStep {fppBound dpBound K : ℕ} (hK : 2 ≤ K)
    (q : QPhys fppBound dpBound) (slot : Fin 11)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (v : Fin 4) :
    viewControlOf (headControlStep hK q slot ws) v = viewNextOfHead hK q v slot ws := by
  show (_, _, _) = viewNextOfHead hK q v slot ws
  rfl

/-- **the tapes of a view along the eleven steps of a slot.**  The view layer's own rule decides
them: each step applies the actions it names, read off the view's own windows.  The steps past
the eleventh stand still, so the function is total. -/
noncomputable def viewRunTapes {fppBound dpBound K : ℕ} (hK : 2 ≤ K) (v : Fin 4)
    (qs : ℕ → QPhys fppBound dpBound)
    (commands : ℕ → PalPeg.ConcreteLocalMachine.ViewCommand)
    (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc) :
    ℕ → Fin 12 → STape PalPeg.CloseoutCoreStep.Γc
  | 0 => viewTapes
  | step + 1 => fun t =>
    if h : step < 11 then
      PalPeg.CloseoutCoreEnc12.actList PalPeg.CloseoutCoreStep.blankc
        (viewRunTapes hK v qs commands viewTapes step t)
        (PalPeg.ConcreteLocalMachine.viewActs (Fin 2) hK ⟨step, h⟩ (commands step)
          (viewControlOf (qs step) v)
          (fun tape => PalPeg.Local.readWin PalPeg.CloseoutCoreStep.blankc K
            (viewRunTapes hK v qs commands viewTapes step tape)) t)
    else viewRunTapes hK v qs commands viewTapes step t

/-- **the slots of a head hold the encoded tapes of that view at every step of the slot.**  The
step `0` case is the hypothesis; each step after it follows because the rule names the view's own
actions through the encoding, and a composite step of a component is the same composite step on
the tape the machine keeps. -/
theorem viewRunTapes_encoded {fppBound dpBound K : ℕ} (hK : 2 ≤ K) (v : Fin 4)
    (qs : ℕ → QPhys fppBound dpBound) (Ts : ℕ → Slot → STape Γm)
    (commands : ℕ → PalPeg.ConcreteLocalMachine.ViewCommand)
    (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (hold : ∀ t, Ts 0 (headSlot v t) = mapTape encCell (viewTapes t))
    (hsteps : ∀ (step : ℕ) (h : step < 11) (t : Fin 12),
      Ts (step + 1) (headSlot v t)
        = PalPeg.CloseoutCoreEnc12.actList blankM (Ts step (headSlot v t))
            (headViewActs hK (qs step) v ⟨step, h⟩ (commands step)
              (fun tape => PalPeg.Local.readWin blankM K (tapesOf (Ts step) tape)) t)) :
    ∀ step, step ≤ 11 → ∀ t, Ts step (headSlot v t)
      = mapTape encCell (viewRunTapes hK v qs commands viewTapes step t)
  | 0, _, t => hold t
  | step + 1, hle, t => by
    have hstep : step < 11 := by omega
    have hprevious := viewRunTapes_encoded hK v qs Ts commands viewTapes hold hsteps step
      (by omega)
    rw [hsteps step hstep t,
      headViewActs_encoded hK (qs step) v ⟨step, hstep⟩ (commands step)
        (viewRunTapes hK v qs commands viewTapes step) (Ts step) hprevious t,
      hprevious t, ← mapTape_actList encCell (by rw [encCell]; rw [if_pos rfl])]
    show _ = mapTape encCell (viewRunTapes hK v qs commands viewTapes (step + 1) t)
    rw [show viewRunTapes hK v qs commands viewTapes (step + 1) t
        = PalPeg.CloseoutCoreEnc12.actList PalPeg.CloseoutCoreStep.blankc
            (viewRunTapes hK v qs commands viewTapes step t)
            (PalPeg.ConcreteLocalMachine.viewActs (Fin 2) hK ⟨step, hstep⟩ (commands step)
              (viewControlOf (qs step) v)
              (fun tape => PalPeg.Local.readWin PalPeg.CloseoutCoreStep.blankc K
                (viewRunTapes hK v qs commands viewTapes step tape)) t)
      from by rw [viewRunTapes]; dsimp only; rw [dif_pos hstep]]

/-- **eleven steps of the machine on a head's slots are one command of that head's view.**  The
control hypothesis says the finite control follows the view layer's own `viewNext` on each of the
eleven steps, and the tape hypothesis says the rule names the view layer's own actions through
the encoding.  Then `viewSlot_sound` carries the whole slot: the head's slots afterwards hold the
encoded tapes of the view the command names, nothing is owed, and so slots compose. -/
theorem viewSlot_of_headRun {fppBound dpBound K margin : ℕ} (hK : 2 ≤ K) (hmargin : K ≤ margin)
    (v : Fin 4) (qs : ℕ → QPhys fppBound dpBound) (Ts : ℕ → Slot → STape Γm)
    (commands : ℕ → PalPeg.ConcreteLocalMachine.ViewCommand)
    (view : PalPeg.LocalInputView.InputView) (hwf : PalPeg.LocalInputView.WF view)
    (hcells : PalPeg.LocalViewCells.ViewCells view)
    (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (hold : ∀ t, Ts 0 (headSlot v t) = mapTape encCell (viewTapes t))
    (hrep : PalPeg.ConcreteLocalMachine.ViewRep margin view ((qs 0).gap v) ((qs 0).micro v)
      viewTapes)
    (howed : ((qs 0).micro v).2.2.2 = 0)
    (hctl : ∀ (step : ℕ) (h : step < 11),
      viewControlOf (qs (step + 1)) v
        = PalPeg.ConcreteLocalMachine.viewNext (Fin 2) hK ⟨step, h⟩ (commands step)
            (viewControlOf (qs step) v)
            (fun tape => PalPeg.Local.readWin PalPeg.CloseoutCoreStep.blankc K
              (viewRunTapes hK v qs commands viewTapes step tape)))
    (hsteps : ∀ (step : ℕ) (h : step < 11) (t : Fin 12),
      Ts (step + 1) (headSlot v t)
        = PalPeg.CloseoutCoreEnc12.actList blankM (Ts step (headSlot v t))
            (headViewActs hK (qs step) v ⟨step, h⟩ (commands step)
              (fun tape => PalPeg.Local.readWin blankM K (tapesOf (Ts step) tape)) t)) :
    PalPeg.ConcreteLocalMachine.ViewRep margin
        (PalPeg.ConcreteLocalMachine.viewApply (commands 0) view) ((qs 11).gap v)
        ((qs 11).micro v) (viewRunTapes hK v qs commands viewTapes 11) ∧
      (((qs 11).micro v).2.2.2.val = 0 ∧
        ∀ t, Ts 11 (headSlot v t)
          = mapTape encCell (viewRunTapes hK v qs commands viewTapes 11 t)) := by
  have hsound := PalPeg.ConcreteLocalMachine.viewSlot_sound (Fin 2) hK hmargin hwf hcells
    commands (fun step => (viewControlOf (qs step) v,
      viewRunTapes hK v qs commands viewTapes step))
    (fun step hstep => ⟨hctl step hstep, fun t _ => by
      refine ⟨?_, fun _ => ?_⟩ <;> dsimp only <;>
        rw [show viewRunTapes hK v qs commands viewTapes (step + 1) t
            = PalPeg.CloseoutCoreEnc12.actList PalPeg.CloseoutCoreStep.blankc
                (viewRunTapes hK v qs commands viewTapes step t)
                (PalPeg.ConcreteLocalMachine.viewActs (Fin 2) hK ⟨step, hstep⟩ (commands step)
                  (viewControlOf (qs step) v)
                  (fun tape => PalPeg.Local.readWin PalPeg.CloseoutCoreStep.blankc K
                    (viewRunTapes hK v qs commands viewTapes step tape)) t)
          from by rw [viewRunTapes]; dsimp only; rw [dif_pos hstep]]⟩)
    (first := ((qs 0).micro v).1) hrep howed (((qs 11).micro v).1)
  exact ⟨hsound.1, hsound.2,
    viewRunTapes_encoded hK v qs Ts commands viewTapes hold hsteps 11 le_rfl⟩

/-- **a machine that takes the head control step and names the view's actions carries out the
command the control holds.**  This is `viewSlot_of_headRun` with both of its hypotheses supplied
by the rule itself: the control goes to `headControlStep`, so it follows `viewNext` on each of
the eleven steps, and the slots follow `headViewActs`, so the rule names the view's own actions.
What is left over is what the encoding asks of a head after a tick. -/
theorem viewSlot_of_headRule {fppBound dpBound K margin : ℕ} (hK : 2 ≤ K) (hmargin : K ≤ margin)
    (v : Fin 4) (qs : ℕ → QPhys fppBound dpBound) (Ts : ℕ → Slot → STape Γm)
    (view : PalPeg.LocalInputView.InputView) (hwf : PalPeg.LocalInputView.WF view)
    (hcells : PalPeg.LocalViewCells.ViewCells view)
    (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (hold : ∀ t, Ts 0 (headSlot v t) = mapTape encCell (viewTapes t))
    (hrep : PalPeg.ConcreteLocalMachine.ViewRep margin view ((qs 0).gap v) ((qs 0).micro v)
      viewTapes)
    (howed : ((qs 0).micro v).2.2.2 = 0)
    (hq : ∀ (step : ℕ) (h : step < 11), viewControlOf (qs (step + 1)) v
      = viewNextOfHead hK (qs step) v ⟨step, h⟩
          (fun tape => PalPeg.Local.readWin blankM K (tapesOf (Ts step) tape)))
    (hsteps : ∀ (step : ℕ) (h : step < 11) (t : Fin 12),
      Ts (step + 1) (headSlot v t)
        = PalPeg.CloseoutCoreEnc12.actList blankM (Ts step (headSlot v t))
            (headViewActs hK (qs step) v ⟨step, h⟩ ((qs step).commands v)
              (fun tape => PalPeg.Local.readWin blankM K (tapesOf (Ts step) tape)) t)) :
    PalPeg.ConcreteLocalMachine.ViewRep margin
        (PalPeg.ConcreteLocalMachine.viewApply ((qs 0).commands v) view) ((qs 11).gap v)
        ((qs 11).micro v)
        (viewRunTapes hK v qs (fun step => (qs step).commands v) viewTapes 11) ∧
      (((qs 11).micro v).2.2.2.val = 0 ∧
        ∀ t, Ts 11 (headSlot v t)
          = mapTape encCell
              (viewRunTapes hK v qs (fun step => (qs step).commands v) viewTapes 11 t)) :=
  viewSlot_of_headRun hK hmargin v qs Ts (fun step => (qs step).commands v) view hwf hcells
    viewTapes hold hrep howed
    (fun step h => by
      rw [hq step h,
        viewNextOfHead_encoded hK (qs step) v ⟨step, h⟩
          (viewRunTapes hK v qs (fun step => (qs step).commands v) viewTapes step) (Ts step)
          (viewRunTapes_encoded hK v qs Ts (fun step => (qs step).commands v) viewTapes hold
            hsteps step (by omega))])
    hsteps

/-- **twelve steps of the machine are one command of every head's view.**  The first step is the
one that decides the commands: it leaves a head's slots and a view's own three control fields
alone, so a view sees nothing of it, and the eleven steps after it are the slot that carries the
command out.  This is why the tick is twelve steps — the command has to be in the control before
the slot starts, and the slot has no step to spare. -/
theorem viewSlot_of_headTick {fppBound dpBound K margin : ℕ} (hK : 2 ≤ K) (hmargin : K ≤ margin)
    (v : Fin 4) (qs : ℕ → QPhys fppBound dpBound) (Ts : ℕ → Slot → STape Γm)
    (view : PalPeg.LocalInputView.InputView) (hwf : PalPeg.LocalInputView.WF view)
    (hcells : PalPeg.LocalViewCells.ViewCells view)
    (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (hold : ∀ t, Ts 0 (headSlot v t) = mapTape encCell (viewTapes t))
    (hrep : PalPeg.ConcreteLocalMachine.ViewRep margin view ((qs 0).gap v) ((qs 0).micro v)
      viewTapes)
    (howed : ((qs 0).micro v).2.2.2 = 0)
    (hfirstTapes : ∀ t, Ts 1 (headSlot v t) = Ts 0 (headSlot v t))
    (hfirstGap : (qs 1).gap v = (qs 0).gap v)
    (hfirstMicro : (qs 1).micro v = (qs 0).micro v)
    (hq : ∀ (step : ℕ) (h : step < 11), viewControlOf (qs (step + 2)) v
      = viewNextOfHead hK (qs (step + 1)) v ⟨step, h⟩
          (fun tape => PalPeg.Local.readWin blankM K (tapesOf (Ts (step + 1)) tape)))
    (hsteps : ∀ (step : ℕ) (h : step < 11) (t : Fin 12),
      Ts (step + 2) (headSlot v t)
        = PalPeg.CloseoutCoreEnc12.actList blankM (Ts (step + 1) (headSlot v t))
            (headViewActs hK (qs (step + 1)) v ⟨step, h⟩ ((qs (step + 1)).commands v)
              (fun tape => PalPeg.Local.readWin blankM K (tapesOf (Ts (step + 1)) tape)) t)) :
    PalPeg.ConcreteLocalMachine.ViewRep margin
        (PalPeg.ConcreteLocalMachine.viewApply ((qs 1).commands v) view) ((qs 12).gap v)
        ((qs 12).micro v)
        (viewRunTapes hK v (fun step => qs (step + 1))
          (fun step => (qs (step + 1)).commands v) viewTapes 11) ∧
      (((qs 12).micro v).2.2.2.val = 0 ∧
        ∀ t, Ts 12 (headSlot v t)
          = mapTape encCell
              (viewRunTapes hK v (fun step => qs (step + 1))
                (fun step => (qs (step + 1)).commands v) viewTapes 11 t)) :=
  viewSlot_of_headRule hK hmargin v (fun step => qs (step + 1)) (fun step => Ts (step + 1)) view
    hwf hcells viewTapes (fun t => (hfirstTapes t).trans (hold t))
    (by rw [hfirstGap, hfirstMicro]; exact hrep) (by rw [hfirstMicro]; exact howed) hq hsteps

/-- **the step counter along the ideal run of a tick.**  The rule advances it by one while it is
below eleven, so the state after `step` steps is on step `step` of the tick. -/
theorem slot_idealRun {fppBound dpBound K : ℕ}
    (R : PalPeg.CloseoutCoreEnc12.ActRule (Fin 2) (QPhys fppBound dpBound) Γm tapeCountM K)
    (x : QPhys fppBound dpBound × (Fin tapeCountM → STape Γm)) (input : Option (Fin 2))
    (hslot0 : x.1.slot.val = 0)
    (hadvance : ∀ q i ws, q.slot.val < 11 →
      (R.nq q i ws).slot.val = q.slot.val + 1) :
    ∀ step, step ≤ 11 →
      (PalPeg.LocalStepFusion.idealRun R blankM x input step).1.slot.val = step
  | 0, _ => hslot0
  | step + 1, hle => by
    have hprevious := slot_idealRun R x input hslot0 hadvance step (by omega)
    rw [PalPeg.LocalStepFusion.idealRun_step]
    show (R.nq (PalPeg.LocalStepFusion.idealRun R blankM x input step).1 _ _).slot.val = step + 1
    rw [hadvance _ _ _ (by rw [hprevious]; omega), hprevious]

/-- **a tick of a rule that agrees with the view layer on a head's slots is one command of that
head's view.**  The rule has only to promise four things about that head, each of them about one
step and about the fields of one view: step `0` leaves the head alone, the eleven steps after it
take the view's three control fields to `viewNext` and name the view's own actions on the head's
twelve slots, and the step counter advances.  Everything else the rule does — counters, program
tapes, the other heads — is free. -/
theorem headTick_of_rule {fppBound dpBound K margin : ℕ} (hK : 2 ≤ K) (hmargin : K ≤ margin)
    (R : PalPeg.CloseoutCoreEnc12.ActRule (Fin 2) (QPhys fppBound dpBound) Γm tapeCountM K)
    (v : Fin 4)
    (hadvance : ∀ q i ws, q.slot.val < 11 → (R.nq q i ws).slot.val = q.slot.val + 1)
    (hfirstGap : ∀ q i ws, q.slot.val = 0 → (R.nq q i ws).gap v = q.gap v)
    (hfirstMicro : ∀ q i ws, q.slot.val = 0 → (R.nq q i ws).micro v = q.micro v)
    (hfirstActs : ∀ q i ws (t : Fin 12), q.slot.val = 0 →
      R.acts q i ws (slotIndex (headSlot v t)) = [])
    (hnqHead : ∀ q ws (k : ℕ) (hk : k < 11), q.slot.val = k + 1 →
      viewControlOf (R.nq q none ws) v = viewNextOfHead hK q v ⟨k, hk⟩ ws)
    (hactsHead : ∀ q ws (k : ℕ) (hk : k < 11) (t : Fin 12), q.slot.val = k + 1 →
      R.acts q none ws (slotIndex (headSlot v t))
        = headViewActs hK q v ⟨k, hk⟩ (q.commands v) ws t)
    (x : QPhys fppBound dpBound × (Fin tapeCountM → STape Γm)) (input : Option (Fin 2))
    (hslot0 : x.1.slot.val = 0)
    (qs : ℕ → QPhys fppBound dpBound) (Ts : ℕ → Slot → STape Γm)
    (hqs : ∀ step, qs step = (PalPeg.LocalStepFusion.idealRun R blankM x input step).1)
    (hTs : ∀ step slot, Ts step slot
      = (PalPeg.LocalStepFusion.idealRun R blankM x input step).2 (slotIndex slot))
    (view : PalPeg.LocalInputView.InputView) (hwf : PalPeg.LocalInputView.WF view)
    (hcells : PalPeg.LocalViewCells.ViewCells view)
    (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (hold : ∀ t, Ts 0 (headSlot v t) = mapTape encCell (viewTapes t))
    (hrep : PalPeg.ConcreteLocalMachine.ViewRep margin view ((qs 0).gap v) ((qs 0).micro v)
      viewTapes)
    (howed : ((qs 0).micro v).2.2.2 = 0) :
    PalPeg.ConcreteLocalMachine.ViewRep margin
        (PalPeg.ConcreteLocalMachine.viewApply ((qs 1).commands v) view) ((qs 12).gap v)
        ((qs 12).micro v)
        (viewRunTapes hK v (fun step => qs (step + 1))
          (fun step => (qs (step + 1)).commands v) viewTapes 11) ∧
      (((qs 12).micro v).2.2.2.val = 0 ∧
        ∀ t, Ts 12 (headSlot v t)
          = mapTape encCell
              (viewRunTapes hK v (fun step => qs (step + 1))
                (fun step => (qs (step + 1)).commands v) viewTapes 11 t)) := by
  have hslotRun : ∀ step, step ≤ 11 → (qs step).slot.val = step := fun step hle => by
    rw [hqs step]
    exact slot_idealRun R x input hslot0 hadvance step hle
  have hwindows : ∀ step, tapesOf (Ts step)
      = (PalPeg.LocalStepFusion.idealRun R blankM x input step).2 := fun step => by
    funext j
    rw [show tapesOf (Ts step) j = Ts step (slotIndex.symm j) from rfl, hTs,
      Equiv.apply_symm_apply]
  have hstepRun : ∀ step, PalPeg.LocalStepFusion.idealRun R blankM x input (step + 1 + 1)
      = PalPeg.LocalStepFusion.idealStep R blankM
          (PalPeg.LocalStepFusion.idealRun R blankM x input (step + 1)) none := fun step => by
    rw [PalPeg.LocalStepFusion.idealRun_step, if_neg (by omega)]
  refine viewSlot_of_headTick hK hmargin v qs Ts view hwf hcells viewTapes hold hrep howed
    (fun t => ?_) ?_ ?_ (fun step h => ?_) (fun step h t => ?_)
  · rw [hTs 1, hTs 0, PalPeg.LocalStepFusion.idealRun_step, if_pos rfl]
    show PalPeg.CloseoutCoreEnc12.actList blankM _
        (R.acts (PalPeg.LocalStepFusion.idealRun R blankM x input 0).1 input _
          (slotIndex (headSlot v t))) = _
    rw [hfirstActs _ _ _ t (by rw [← hqs 0]; exact hslotRun 0 (by omega))]
    rfl
  · rw [hqs 1, hqs 0, PalPeg.LocalStepFusion.idealRun_step, if_pos rfl]
    exact hfirstGap _ _ _ (by rw [← hqs 0]; exact hslotRun 0 (by omega))
  · rw [hqs 1, hqs 0, PalPeg.LocalStepFusion.idealRun_step, if_pos rfl]
    exact hfirstMicro _ _ _ (by rw [← hqs 0]; exact hslotRun 0 (by omega))
  · rw [hqs (step + 2), hqs (step + 1), hstepRun step, hwindows (step + 1)]
    show viewControlOf (R.nq _ none _) v = _
    rw [hnqHead _ _ step h (by rw [← hqs (step + 1)]; exact hslotRun (step + 1) (by omega))]
  · rw [hTs (step + 2), hTs (step + 1), hstepRun step, hwindows (step + 1), hqs (step + 1)]
    show PalPeg.CloseoutCoreEnc12.actList blankM _
        (R.acts _ none _ (slotIndex (headSlot v t))) = _
    rw [hactsHead _ _ step h t (by rw [← hqs (step + 1)]; exact hslotRun (step + 1) (by omega))]

/-- the next of the twelve steps of a tick. -/
def slotAdvance (s : Fin 12) : Fin 12 :=
  if h : s.val + 1 < 12 then ⟨s.val + 1, h⟩ else 0

@[simp] theorem slotAdvance_val {s : Fin 12} (h : s.val < 11) :
    (slotAdvance s).val = s.val + 1 := by
  unfold slotAdvance
  rw [dif_pos (by omega)]

/-- **the rule of the machine, as the division of labour inside a tick.**  Step `0` reads the
letter and does everything that is not a head: it moves the counters, the program tapes and the
period tapes as the mode of the state says, and it writes into the control which command each of
the four heads is to carry out.  The eleven steps after it are the slot that carries those
commands out, and they touch nothing but the heads.

So a mode's branch never names a head's tapes again: it names counters and four commands.  The
case analysis of a head's step is the view layer's, once, for all modes. -/
noncomputable def tickRule {fppBound dpBound K : ℕ} (hK : 2 ≤ K)
    (base : QPhys fppBound dpBound → Option (Fin 2) →
      (Fin tapeCountM → PalPeg.Local.Window Γm K) → QPhys fppBound dpBound)
    (commandsOf : QPhys fppBound dpBound → Option (Fin 2) →
      (Fin tapeCountM → PalPeg.Local.Window Γm K) → Fin 4 →
      PalPeg.ConcreteLocalMachine.ViewCommand)
    (baseActs : QPhys fppBound dpBound → Option (Fin 2) →
      (Fin tapeCountM → PalPeg.Local.Window Γm K) → Fin tapeCountM →
      List (PalPeg.CloseoutCoreEnc12.Act Γm))
    (baseLen : ∀ q i ws j, (baseActs q i ws j).length ≤ K) :
    PalPeg.CloseoutCoreEnc12.ActRule (Fin 2) (QPhys fppBound dpBound) Γm tapeCountM K where
  nq := fun q i ws =>
    if q.slot.val = 0 then
      { base q i ws with
        slot := slotAdvance q.slot
        gap := q.gap
        job := q.job
        micro := q.micro
        commands := commandsOf q i ws }
    else
      { headControlStep hK q ⟨q.slot.val - 1, by have := q.slot.isLt; omega⟩ ws with
        slot := slotAdvance q.slot }
  acts := fun q i ws j =>
    if q.slot.val = 0 then
      (if (slotIndex.symm j).isLeft then [] else baseActs q i ws j)
    else
      match hj : slotIndex.symm j with
      | .inl p => headViewActs hK q p.1 ⟨q.slot.val - 1, by have := q.slot.isLt; omega⟩
          (q.commands p.1) ws p.2
      | .inr _ => []
  len_le := fun q i ws j => by
    by_cases hslot : q.slot.val = 0
    · rw [if_pos hslot]
      split
      · simp
      · exact baseLen q i ws j
    · rw [if_neg hslot]
      match hj : slotIndex.symm j with
      | .inl p => exact headViewActs_length hK q p.1 _ (q.commands p.1) ws p.2
      | .inr _ => simp

/-- **the four promises of `headTick_of_rule`, for the rule built that way.**  Each of them is
the division of labour read off the definition: the step counter advances, step `0` is not a
head's step, and the steps after it are nothing but. -/
theorem tickRule_advance {fppBound dpBound K : ℕ} (hK : 2 ≤ K) (base commandsOf baseActs)
    (baseLen : ∀ q i ws j, (baseActs q i ws j).length ≤ K)
    (q : QPhys fppBound dpBound) (i : Option (Fin 2))
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (h : q.slot.val < 11) :
    ((tickRule hK base commandsOf baseActs baseLen).nq q i ws).slot.val = q.slot.val + 1 := by
  show (if q.slot.val = 0 then _ else _ : QPhys fppBound dpBound).slot.val = _
  by_cases hslot : q.slot.val = 0
  · rw [if_pos hslot]
    exact slotAdvance_val h
  · rw [if_neg hslot]
    exact slotAdvance_val h

theorem tickRule_firstGap {fppBound dpBound K : ℕ} (hK : 2 ≤ K) (base commandsOf baseActs)
    (baseLen : ∀ q i ws j, (baseActs q i ws j).length ≤ K)
    (q : QPhys fppBound dpBound) (i : Option (Fin 2))
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (hslot : q.slot.val = 0) (v : Fin 4) :
    ((tickRule hK base commandsOf baseActs baseLen).nq q i ws).gap v = q.gap v := by
  show (if q.slot.val = 0 then _ else _ : QPhys fppBound dpBound).gap v = _
  rw [if_pos hslot]

theorem tickRule_firstMicro {fppBound dpBound K : ℕ} (hK : 2 ≤ K) (base commandsOf baseActs)
    (baseLen : ∀ q i ws j, (baseActs q i ws j).length ≤ K)
    (q : QPhys fppBound dpBound) (i : Option (Fin 2))
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (hslot : q.slot.val = 0) (v : Fin 4) :
    ((tickRule hK base commandsOf baseActs baseLen).nq q i ws).micro v = q.micro v := by
  show (if q.slot.val = 0 then _ else _ : QPhys fppBound dpBound).micro v = _
  rw [if_pos hslot]

theorem tickRule_firstActs {fppBound dpBound K : ℕ} (hK : 2 ≤ K) (base commandsOf baseActs)
    (baseLen : ∀ q i ws j, (baseActs q i ws j).length ≤ K)
    (q : QPhys fppBound dpBound) (i : Option (Fin 2))
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (v : Fin 4) (t : Fin 12)
    (hslot : q.slot.val = 0) :
    (tickRule hK base commandsOf baseActs baseLen).acts q i ws (slotIndex (headSlot v t)) = [] := by
  show (if q.slot.val = 0 then _ else _) = _
  rw [if_pos hslot, if_pos (by rw [Equiv.symm_apply_apply]; rfl)]

theorem tickRule_nqHead {fppBound dpBound K : ℕ} (hK : 2 ≤ K) (base commandsOf baseActs)
    (baseLen : ∀ q i ws j, (baseActs q i ws j).length ≤ K)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (k : ℕ) (hk : k < 11) (hslot : q.slot.val = k + 1) (v : Fin 4) :
    viewControlOf ((tickRule hK base commandsOf baseActs baseLen).nq q none ws) v
      = viewNextOfHead hK q v ⟨k, hk⟩ ws := by
  have hne : ¬ q.slot.val = 0 := by omega
  have hfin : (⟨q.slot.val - 1, by have := q.slot.isLt; omega⟩ : Fin 11) = ⟨k, hk⟩ :=
    Fin.ext (show q.slot.val - 1 = k by omega)
  show viewControlOf (if q.slot.val = 0 then _ else _ : QPhys fppBound dpBound) v = _
  rw [if_neg hne]
  show viewControlOf { headControlStep hK q _ ws with slot := slotAdvance q.slot } v = _
  rw [show viewControlOf { headControlStep hK q
        (⟨q.slot.val - 1, by have := q.slot.isLt; omega⟩ : Fin 11) ws with
          slot := slotAdvance q.slot } v
      = viewControlOf (headControlStep hK q
          (⟨q.slot.val - 1, by have := q.slot.isLt; omega⟩ : Fin 11) ws) v from rfl,
    viewControlOf_headControlStep, hfin]

theorem tickRule_actsHead {fppBound dpBound K : ℕ} (hK : 2 ≤ K) (base commandsOf baseActs)
    (baseLen : ∀ q i ws j, (baseActs q i ws j).length ≤ K)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (k : ℕ) (hk : k < 11) (hslot : q.slot.val = k + 1) (v : Fin 4) (t : Fin 12) :
    (tickRule hK base commandsOf baseActs baseLen).acts q none ws (slotIndex (headSlot v t))
      = headViewActs hK q v ⟨k, hk⟩ (q.commands v) ws t := by
  have hne : ¬ q.slot.val = 0 := by omega
  have hfin : (⟨q.slot.val - 1, by have := q.slot.isLt; omega⟩ : Fin 11) = ⟨k, hk⟩ :=
    Fin.ext (show q.slot.val - 1 = k by omega)
  show (if q.slot.val = 0 then _ else _) = _
  rw [if_neg hne]
  show (match hj : slotIndex.symm (slotIndex (headSlot v t)) with
      | .inl p => headViewActs hK q p.1 _ (q.commands p.1) ws p.2
      | .inr _ => []) = _
  rw [Equiv.symm_apply_apply]
  show headViewActs hK q v _ (q.commands v) ws t = _
  rw [hfin]

/-- **a tick of the machine is one command of every head's view, whatever the rest of the rule
does.**  The four promises of `headTick_of_rule` are all read off the division of labour, so the
head side of a tick is closed once and for all: what remains of a mode's branch is to name the
counters, the program tapes and the four commands. -/
theorem headTick_of_tickRule {fppBound dpBound K margin : ℕ} (hK : 2 ≤ K) (hmargin : K ≤ margin)
    (base commandsOf baseActs) (baseLen : ∀ q i ws j, (baseActs q i ws j).length ≤ K) (v : Fin 4)
    (x : QPhys fppBound dpBound × (Fin tapeCountM → STape Γm)) (input : Option (Fin 2))
    (hslot0 : x.1.slot.val = 0)
    (qs : ℕ → QPhys fppBound dpBound) (Ts : ℕ → Slot → STape Γm)
    (hqs : ∀ step, qs step
      = (PalPeg.LocalStepFusion.idealRun (tickRule hK base commandsOf baseActs baseLen) blankM x input
          step).1)
    (hTs : ∀ step slot, Ts step slot
      = (PalPeg.LocalStepFusion.idealRun (tickRule hK base commandsOf baseActs baseLen) blankM x input
          step).2 (slotIndex slot))
    (view : PalPeg.LocalInputView.InputView) (hwf : PalPeg.LocalInputView.WF view)
    (hcells : PalPeg.LocalViewCells.ViewCells view)
    (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (hold : ∀ t, Ts 0 (headSlot v t) = mapTape encCell (viewTapes t))
    (hrep : PalPeg.ConcreteLocalMachine.ViewRep margin view ((qs 0).gap v) ((qs 0).micro v)
      viewTapes)
    (howed : ((qs 0).micro v).2.2.2 = 0) :
    PalPeg.ConcreteLocalMachine.ViewRep margin
        (PalPeg.ConcreteLocalMachine.viewApply ((qs 1).commands v) view) ((qs 12).gap v)
        ((qs 12).micro v)
        (viewRunTapes hK v (fun step => qs (step + 1))
          (fun step => (qs (step + 1)).commands v) viewTapes 11) ∧
      (((qs 12).micro v).2.2.2.val = 0 ∧
        ∀ t, Ts 12 (headSlot v t)
          = mapTape encCell
              (viewRunTapes hK v (fun step => qs (step + 1))
                (fun step => (qs (step + 1)).commands v) viewTapes 11 t)) :=
  headTick_of_rule hK hmargin (tickRule hK base commandsOf baseActs baseLen) v
    (fun q i ws h => tickRule_advance hK base commandsOf baseActs baseLen q i ws h)
    (fun q i ws hslot => tickRule_firstGap hK base commandsOf baseActs baseLen q i ws hslot v)
    (fun q i ws hslot => tickRule_firstMicro hK base commandsOf baseActs baseLen q i ws hslot v)
    (fun q i ws t hslot => tickRule_firstActs hK base commandsOf baseActs baseLen q i ws v t hslot)
    (fun q ws k hk hslot => tickRule_nqHead hK base commandsOf baseActs baseLen q ws k hk hslot v)
    (fun q ws k hk t hslot => tickRule_actsHead hK base commandsOf baseActs baseLen q ws k hk hslot v t)
    x input hslot0 qs Ts hqs hTs view hwf hcells viewTapes hold hrep howed

/-- **a view's step left realizes the abstract head's step left, with the arrivals still
invisible.**  The view layer proves this for `absHead`, which puts the queue on the stack; the
encoding uses `absHead'`, which leaves the queue as incoming, so the same fact has to be said of
that abstraction.  It holds with no side condition: a half-step only flips the bit, and a full
step pops the back stack, which is what the abstract head does to its own left stack. -/
theorem absHead'_moveLeftV (v : PalPeg.LocalInputView.InputView) (q : List (Fin 2)) :
    PalPeg.LocalArrival.absHead' (PalPeg.LocalInputView.moveLeftV v) q
      = PalPeg.GalilScaffoldInputHead.left (PalPeg.LocalArrival.absHead' v q) := by
  rcases v with ⟨back, focus, near, far, gap⟩
  cases gap
  · cases back with
    | nil => rfl
    | cons c rest => rfl
  · rfl

/-- **a view's step right realizes the abstract head's step right** exactly when the cell it
needs has already arrived.  The view layer proves the three cases apart; this is the one
statement a mode's branch can use.

The hypothesis cannot be weakened to `Ahead`, which allows the queue to be empty when nothing is
pending: there the view writes the blank that has not arrived and the abstract head does not, so
the two sides really differ.  A step right of a head is the one command that is not free.
-/
theorem absHead'_moveRight {v : PalPeg.LocalInputView.InputView}
    (hwf : PalPeg.LocalInputView.WF v) (q : List (Fin 2))
    (hready : v.gap = true → v.near = [] → PalPeg.RTQueue.toList v.far ≠ []) :
    PalPeg.LocalArrival.absHead' (PalPeg.LocalInputView.moveRight v) q
      = PalPeg.GalilScaffoldChainVerifier.right (PalPeg.LocalArrival.absHead' v q) := by
  by_cases hgap : v.gap = false
  · exact PalPeg.LocalArrival.absHead'_moveRight_gap hgap q
  · have hgapTrue : v.gap = true := by
      cases hg : v.gap with
      | false => exact absurd hg hgap
      | true => rfl
    by_cases hnear : v.near = []
    · exact PalPeg.LocalArrival.absHead'_moveRight_far hwf hnear (hready hgapTrue hnear) q
    · exact PalPeg.LocalArrival.absHead'_moveRight_near hnear q

/-- the operation on the abstract head that a command carries out, for the three commands that
move a head on its own: standing still, the step left and the step right.  The arrival is not
here because it is not an operation on the head alone — it puts a letter into the pending list —
and the two reposition steps are the halves of a step, which a mode names in pairs. -/
def headOp : PalPeg.ConcreteLocalMachine.ViewCommand →
    Option (PalPeg.GalilScaffoldInputHead.PlaceHead → PalPeg.GalilScaffoldInputHead.PlaceHead)
  | .stay => some id
  | .moveLeft => some PalPeg.GalilScaffoldInputHead.left
  | .moveRight => some PalPeg.GalilScaffoldChainVerifier.right
  | _ => none

/-- **the one entry point a mode's branch uses: the command it names is the operation the
abstract tick does to that head.**  The step right carries the arrival condition; the other two
are free. -/
theorem absHead'_viewApply {v : PalPeg.LocalInputView.InputView}
    (hwf : PalPeg.LocalInputView.WF v) (q : List (Fin 2))
    (command : PalPeg.ConcreteLocalMachine.ViewCommand)
    (hready : command = .moveRight →
      v.gap = true → v.near = [] → PalPeg.RTQueue.toList v.far ≠ [])
    (f : PalPeg.GalilScaffoldInputHead.PlaceHead → PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hf : headOp command = some f) :
    PalPeg.LocalArrival.absHead' (PalPeg.ConcreteLocalMachine.viewApply command v) q
      = f (PalPeg.LocalArrival.absHead' v q) := by
  cases command with
  | stay =>
    rw [show f = id from (Option.some.inj hf).symm]
    rfl
  | arrive a => exact absurd hf (by simp [headOp])
  | moveRight =>
    rw [show f = PalPeg.GalilScaffoldChainVerifier.right from (Option.some.inj hf).symm]
    exact absHead'_moveRight hwf q (hready rfl)
  | moveLeft =>
    rw [show f = PalPeg.GalilScaffoldInputHead.left from (Option.some.inj hf).symm]
    exact absHead'_moveLeftV v q
  | stepRight => exact absurd hf (by simp [headOp])
  | stepLeft => exact absurd hf (by simp [headOp])

/-- **a view's step left does not change what it holds.**  A half-step moves only the bit and a
full step moves the boundary between the two stacks, so the cells are the same list. -/
theorem cells_moveLeftV (v : PalPeg.LocalInputView.InputView) :
    PalPeg.LocalInputView.cells (PalPeg.LocalInputView.moveLeftV v)
      = PalPeg.LocalInputView.cells v := by
  rcases v with ⟨back, focus, near, far, gap⟩
  cases gap
  · cases back with
    | nil => rfl
    | cons c rest =>
      simp [PalPeg.LocalInputView.cells, PalPeg.LocalInputView.absRight,
        PalPeg.LocalInputView.farList, PalPeg.LocalInputView.moveLeftV,
        PalPeg.LocalInputView.stepLeft]
  · rfl

/-- **a view's step right does not change what it holds either**, when the cell it needs has
arrived: it moves the boundary, and a cell that comes out of the queue was already counted among
what the view holds. -/
theorem cells_moveRight {v : PalPeg.LocalInputView.InputView}
    (hwf : PalPeg.LocalInputView.WF v)
    (hready : v.gap = true → v.near = [] → PalPeg.RTQueue.toList v.far ≠ []) :
    PalPeg.LocalInputView.cells (PalPeg.LocalInputView.moveRight v)
      = PalPeg.LocalInputView.cells v := by
  rcases v with ⟨back, focus, near, far, gap⟩
  cases gap
  · rfl
  · cases near with
    | cons c rest =>
      simp [PalPeg.LocalInputView.cells, PalPeg.LocalInputView.absRight,
        PalPeg.LocalInputView.farList, PalPeg.LocalInputView.moveRight,
        PalPeg.LocalInputView.stepRight]
    | nil =>
      have hfar : PalPeg.RTQueue.toList far ≠ [] := hready rfl rfl
      obtain ⟨a, rest, hlist⟩ : ∃ a rest, PalPeg.RTQueue.toList far = a :: rest := by
        cases hl : PalPeg.RTQueue.toList far with
        | nil => exact absurd hl hfar
        | cons b bs => exact ⟨b, bs, rfl⟩
      have hhead : PalPeg.RTQueue.head? far = some a := by
        rw [PalPeg.RTQueue.head?_eq (hwf : PalPeg.RTQueue.Inv far), hlist]
        rfl
      have htail : PalPeg.RTQueue.toList (PalPeg.RTQueue.tail far) = rest := by
        rw [PalPeg.RTQueue.toList_tail (hwf : PalPeg.RTQueue.Inv far), hlist]
        rfl
      simp [PalPeg.LocalInputView.cells, PalPeg.LocalInputView.absRight,
        PalPeg.LocalInputView.farList, PalPeg.LocalInputView.moveRight,
        PalPeg.LocalInputView.stepRight, hhead, htail, hlist]

/-- **a view's step right keeps the queue's invariant**, because all it does to the queue is take
its tail. -/
theorem wf_moveRight {v : PalPeg.LocalInputView.InputView} (hwf : PalPeg.LocalInputView.WF v) :
    PalPeg.LocalInputView.WF (PalPeg.LocalInputView.moveRight v) := by
  rcases v with ⟨back, focus, near, far, gap⟩
  cases gap
  · exact hwf
  · cases near with
    | cons c rest => exact hwf
    | nil =>
      show PalPeg.RTQueue.Inv (PalPeg.LocalInputView.stepRight _).far
      cases hhead : PalPeg.RTQueue.head? far with
      | none =>
        rw [show (PalPeg.LocalInputView.stepRight
              (⟨back, focus, [], far, true⟩ : PalPeg.LocalInputView.InputView)).far = far from by
          simp [PalPeg.LocalInputView.stepRight, hhead]]
        exact hwf
      | some a =>
        rw [show (PalPeg.LocalInputView.stepRight
              (⟨back, focus, [], far, true⟩ : PalPeg.LocalInputView.InputView)).far
            = PalPeg.RTQueue.tail far from by
          simp [PalPeg.LocalInputView.stepRight, hhead]]
        exact PalPeg.RTQueue.inv_tail (hwf : PalPeg.RTQueue.Inv far)

/-- **what a view holds, and its queue's invariant, survive the command a mode names.**  These
are the two side facts `EncTapes.heads` carries about a view, so a mode's branch gets them back
from the same dispatch that gives it the abstract head. -/
theorem viewCells_viewApply {v : PalPeg.LocalInputView.InputView}
    (hwf : PalPeg.LocalInputView.WF v) (command : PalPeg.ConcreteLocalMachine.ViewCommand)
    (hready : command = .moveRight →
      v.gap = true → v.near = [] → PalPeg.RTQueue.toList v.far ≠ [])
    (hcells : PalPeg.LocalViewCells.ViewCells v)
    (f : PalPeg.GalilScaffoldInputHead.PlaceHead → PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hf : headOp command = some f) :
    PalPeg.LocalViewCells.ViewCells (PalPeg.ConcreteLocalMachine.viewApply command v) := by
  obtain ⟨letters, hletters⟩ := hcells
  cases command with
  | stay => exact ⟨letters, hletters⟩
  | arrive a => exact absurd hf (by simp [headOp])
  | moveRight =>
    exact ⟨letters, by
      show PalPeg.LocalInputView.cells (PalPeg.LocalInputView.moveRight v) = _
      rw [cells_moveRight hwf (hready rfl), hletters]⟩
  | moveLeft =>
    exact ⟨letters, by
      show PalPeg.LocalInputView.cells (PalPeg.LocalInputView.moveLeftV v) = _
      rw [cells_moveLeftV v, hletters]⟩
  | stepRight => exact absurd hf (by simp [headOp])
  | stepLeft => exact absurd hf (by simp [headOp])

theorem wf_viewApply {v : PalPeg.LocalInputView.InputView} (hwf : PalPeg.LocalInputView.WF v)
    (command : PalPeg.ConcreteLocalMachine.ViewCommand)
    (f : PalPeg.GalilScaffoldInputHead.PlaceHead → PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hf : headOp command = some f) :
    PalPeg.LocalInputView.WF (PalPeg.ConcreteLocalMachine.viewApply command v) := by
  cases command with
  | stay => exact hwf
  | arrive a => exact absurd hf (by simp [headOp])
  | moveRight => exact wf_moveRight hwf
  | moveLeft =>
    show PalPeg.LocalInputView.WF (PalPeg.LocalInputView.moveLeftV v)
    have hfar : (PalPeg.LocalInputView.moveLeftV v).far = v.far := by
      rcases v with ⟨back, focus, near, far, gap⟩
      cases gap
      · cases back with
        | nil => rfl
        | cons c rest => rfl
      · rfl
    show PalPeg.RTQueue.Inv (PalPeg.LocalInputView.moveLeftV v).far
    rw [hfar]
    exact hwf
  | stepRight => exact absurd hf (by simp [headOp])
  | stepLeft => exact absurd hf (by simp [headOp])

/-- **the heads of the encoding after a tick.**  Everything the encoding asks about a head is
put back together here, for one head, out of the two halves that are now proved: the machine's
twelve steps carry out the command the control holds, and the command is the operation the
abstract tick does to that head.

The hypotheses are what a mode's branch has to say about that head and nothing else: what the
head becomes, that the command names that operation, and — only for a step right — that the cell
the head needs has arrived. -/
theorem heads_afterTick {fppBound dpBound K margin : ℕ} (hK : 2 ≤ K) (hmargin : K ≤ margin)
    (base commandsOf baseActs) (baseLen : ∀ q i ws j, (baseActs q i ws j).length ≤ K) (v : Fin 4)
    (x : QPhys fppBound dpBound × (Fin tapeCountM → STape Γm)) (input : Option (Fin 2))
    (hslot0 : x.1.slot.val = 0)
    (qs : ℕ → QPhys fppBound dpBound) (Ts : ℕ → Slot → STape Γm)
    (hqs : ∀ step, qs step
      = (PalPeg.LocalStepFusion.idealRun (tickRule hK base commandsOf baseActs baseLen) blankM x input
          step).1)
    (hTs : ∀ step slot, Ts step slot
      = (PalPeg.LocalStepFusion.idealRun (tickRule hK base commandsOf baseActs baseLen) blankM x input
          step).2 (slotIndex slot))
    (view : PalPeg.LocalInputView.InputView) (hwf : PalPeg.LocalInputView.WF view)
    (hcells : PalPeg.LocalViewCells.ViewCells view)
    (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (hold : ∀ t, Ts 0 (headSlot v t) = mapTape encCell (viewTapes t))
    (hrep : PalPeg.ConcreteLocalMachine.ViewRep margin view ((qs 0).gap v) ((qs 0).micro v)
      viewTapes)
    (howed : ((qs 0).micro v).2.2.2 = 0)
    (head head' : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (habs : PalPeg.LocalArrival.absHead' view [] = head)
    (f : PalPeg.GalilScaffoldInputHead.PlaceHead → PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hf : headOp ((qs 1).commands v) = some f) (hhead' : head' = f head)
    (hready : (qs 1).commands v = .moveRight →
      view.gap = true → view.near = [] → PalPeg.RTQueue.toList view.far ≠ []) :
    ∃ (view' : PalPeg.LocalInputView.InputView)
        (viewTapes' : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc),
      PalPeg.LocalArrival.absHead' view' [] = head' ∧
        PalPeg.ConcreteLocalMachine.ViewRep margin view' ((qs 12).gap v) ((qs 12).micro v)
            viewTapes' ∧
          (∀ i, Ts 12 (headSlot v i) = mapTape encCell (viewTapes' i)) ∧
            PalPeg.LocalViewCells.ViewCells view' ∧ PalPeg.LocalInputView.WF view' := by
  obtain ⟨hrep', howed', hslots'⟩ := headTick_of_tickRule hK hmargin base commandsOf baseActs baseLen v x
    input hslot0 qs Ts hqs hTs view hwf hcells viewTapes hold hrep howed
  exact ⟨PalPeg.ConcreteLocalMachine.viewApply ((qs 1).commands v) view, _,
    by rw [hhead', ← habs]; exact absHead'_viewApply hwf [] _ hready f hf,
    hrep', hslots', viewCells_viewApply hwf _ hready hcells f hf, wf_viewApply hwf _ f hf⟩

/-- **one ideal step of the fused rule is the ideal run of the twelve steps.**  The consumer of
the local realization asks for one ideal step of one rule per abstract tick; the twelve steps of
a tick are that one step of the rule fused twelve times, and the two halves of the bridge are
already in the fusion.  The margin is the fused radius, which the encoding's own margins give. -/
theorem idealStep_fused {Q : Type} {K : ℕ}
    (R : PalPeg.CloseoutCoreEnc12.ActRule (Fin 2) Q Γm tapeCountM K)
    (x : Q × (Fin tapeCountM → STape Γm)) (input : Option (Fin 2))
    (hmargin : ∀ tape, PalPeg.LocalStepFusion.iterRadius K 12 ≤ PalPeg.Local.pos (x.2 tape)) :
    PalPeg.LocalStepFusion.idealStep (PalPeg.LocalStepFusion.iterRule R 12) blankM x input
      = PalPeg.LocalStepFusion.idealRun R blankM x input 12 :=
  (PalPeg.LocalStepFusion.iterRule_ideal blankM R 12 x input hmargin).trans
    (PalPeg.LocalStepFusion.idealIter_eq_idealRun R blankM 12 x input)

/-- **the heads of the encoding after one ideal step of the fused rule.**  This is
`heads_afterTick` on the step the consumer actually takes: one step of the rule fused twelve
times, whose control and tapes are those of the twelfth state of the run. -/
theorem heads_afterFusedStep {fppBound dpBound K margin : ℕ} (hK : 2 ≤ K) (hmargin : K ≤ margin)
    (base commandsOf baseActs) (baseLen : ∀ q i ws j, (baseActs q i ws j).length ≤ K) (v : Fin 4)
    (x : QPhys fppBound dpBound × (Fin tapeCountM → STape Γm)) (input : Option (Fin 2))
    (hslot0 : x.1.slot.val = 0)
    (hfused : ∀ tape, PalPeg.LocalStepFusion.iterRadius K 12 ≤ PalPeg.Local.pos (x.2 tape))
    (view : PalPeg.LocalInputView.InputView) (hwf : PalPeg.LocalInputView.WF view)
    (hcells : PalPeg.LocalViewCells.ViewCells view)
    (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (hold : ∀ t, x.2 (slotIndex (headSlot v t)) = mapTape encCell (viewTapes t))
    (hrep : PalPeg.ConcreteLocalMachine.ViewRep margin view (x.1.gap v) (x.1.micro v) viewTapes)
    (howed : (x.1.micro v).2.2.2 = 0)
    (head head' : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (habs : PalPeg.LocalArrival.absHead' view [] = head)
    (f : PalPeg.GalilScaffoldInputHead.PlaceHead → PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hf : headOp ((PalPeg.LocalStepFusion.idealRun (tickRule hK base commandsOf baseActs baseLen) blankM x
      input 1).1.commands v) = some f)
    (hhead' : head' = f head)
    (hready : (PalPeg.LocalStepFusion.idealRun (tickRule hK base commandsOf baseActs baseLen) blankM x input
        1).1.commands v = .moveRight →
      view.gap = true → view.near = [] → PalPeg.RTQueue.toList view.far ≠ []) :
    ∃ (view' : PalPeg.LocalInputView.InputView)
        (viewTapes' : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc),
      PalPeg.LocalArrival.absHead' view' [] = head' ∧
        PalPeg.ConcreteLocalMachine.ViewRep margin view'
            ((PalPeg.LocalStepFusion.idealStep
              (PalPeg.LocalStepFusion.iterRule (tickRule hK base commandsOf baseActs baseLen) 12) blankM x
                input).1.gap v)
            ((PalPeg.LocalStepFusion.idealStep
              (PalPeg.LocalStepFusion.iterRule (tickRule hK base commandsOf baseActs baseLen) 12) blankM x
                input).1.micro v) viewTapes' ∧
          (∀ i, (PalPeg.LocalStepFusion.idealStep
              (PalPeg.LocalStepFusion.iterRule (tickRule hK base commandsOf baseActs baseLen) 12) blankM x
                input).2 (slotIndex (headSlot v i)) = mapTape encCell (viewTapes' i)) ∧
            PalPeg.LocalViewCells.ViewCells view' ∧ PalPeg.LocalInputView.WF view' := by
  rw [idealStep_fused (tickRule hK base commandsOf baseActs baseLen) x input hfused]
  exact heads_afterTick hK hmargin base commandsOf baseActs baseLen v x input hslot0
    (fun step => (PalPeg.LocalStepFusion.idealRun (tickRule hK base commandsOf baseActs baseLen) blankM x
      input step).1)
    (fun step slot => (PalPeg.LocalStepFusion.idealRun (tickRule hK base commandsOf baseActs baseLen) blankM
      x input step).2 (slotIndex slot))
    (fun _ => rfl) (fun _ _ => rfl) view hwf hcells viewTapes hold hrep howed head head' habs f hf
    hhead' hready

/-- the fields of the control that do not belong to a view.  The eleven steps of a slot move a
view's gap bit, its queue job and its micro-schedule, and the step counter; everything else in
the control is settled at step `0` and then stands still, and this tuple is what stands still.

`headControlStep` writes only the three fields of a view, so it leaves this tuple alone by
definition, which is what the induction below leans on. -/
def headFreeFields {fppBound dpBound : ℕ} (q : QPhys fppBound dpBound) :
    CtlPhys × ChainTag × Fin 5 × Bool × Bool ×
      PalPeg.GalilScaffoldChainInputSupply.FppControl.Mode × Bool × PcPhys fppBound × Bool ×
      PcPhys dpBound × Bool × PalPeg.GalilScaffoldSearchFinish.Mode × Bool × Fin 4 × Bool ×
      (Fin 3 → Bool) × Bool × Bool × (Fin 16 → Bool) × Bool × Bool :=
  (q.ctl, q.chainTag, q.chainPhase, q.chainForward, q.chainBroken, q.fppMode, q.fppFinalStage,
    q.fppPc, q.fppDone, q.dpPc, q.dpDone, q.searchMode, q.searchFinalStage, q.searchQuarter,
    q.periodOnly, q.placeGap, q.onLetterBit, q.leftFirstBit, q.polarity, q.fppLive, q.dpLive)

/-- **after step `0`, a tick changes nothing but the heads.**  The slots that are not a head's
are not written again, and the fields of the control that are not a view's are not changed again,
so whatever a mode's branch settles at step `0` is what the tick leaves behind.

This is what lets the branches that are already proved stand as the `base` of the rule: they
speak of counters, program tapes, period tapes and the answer, and the eleven steps after them
do not touch any of it. -/
theorem tickRule_still {fppBound dpBound K : ℕ} (hK : 2 ≤ K) (base commandsOf baseActs)
    (baseLen : ∀ q i ws j, (baseActs q i ws j).length ≤ K)
    (x : QPhys fppBound dpBound × (Fin tapeCountM → STape Γm)) (input : Option (Fin 2))
    (hslot0 : x.1.slot.val = 0) :
    ∀ step, 1 ≤ step → step ≤ 12 →
      (∀ j : Fin tapeCountM, (slotIndex.symm j).isLeft = false →
          (PalPeg.LocalStepFusion.idealRun (tickRule hK base commandsOf baseActs baseLen) blankM x input
            step).2 j
            = (PalPeg.LocalStepFusion.idealRun (tickRule hK base commandsOf baseActs baseLen) blankM x input
              1).2 j) ∧
        headFreeFields (PalPeg.LocalStepFusion.idealRun (tickRule hK base commandsOf baseActs baseLen)
            blankM x input step).1
          = headFreeFields (PalPeg.LocalStepFusion.idealRun (tickRule hK base commandsOf baseActs baseLen)
            blankM x input 1).1
  | 1, _, _ => ⟨fun _ _ => rfl, rfl⟩
  | step + 2, _, hle => by
    have hstep : 1 ≤ step + 1 := by omega
    have hslotLt : step + 1 ≤ 11 := by omega
    obtain ⟨htapes, hfields⟩ := tickRule_still hK base commandsOf baseActs baseLen x input hslot0 (step + 1)
      hstep (by omega)
    have hslotVal : (PalPeg.LocalStepFusion.idealRun (tickRule hK base commandsOf baseActs baseLen) blankM x
        input (step + 1)).1.slot.val = step + 1 :=
      slot_idealRun (tickRule hK base commandsOf baseActs baseLen) x input hslot0
        (fun q i ws h => tickRule_advance hK base commandsOf baseActs baseLen q i ws h) (step + 1) hslotLt
    have hne : ¬ (PalPeg.LocalStepFusion.idealRun (tickRule hK base commandsOf baseActs baseLen) blankM x
        input (step + 1)).1.slot.val = 0 := by omega
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [PalPeg.LocalStepFusion.idealRun_step, PalPeg.LocalStepFusion.idealStep]
      show PalPeg.CloseoutCoreEnc12.actList blankM _
          ((tickRule hK base commandsOf baseActs baseLen).acts _ _ _ j) = _
      rw [show (tickRule hK base commandsOf baseActs baseLen).acts
            (PalPeg.LocalStepFusion.idealRun (tickRule hK base commandsOf baseActs baseLen) blankM x input
              (step + 1)).1 _ _ j = [] from by
        show (if _ = 0 then _ else _) = _
        rw [if_neg hne]
        match hjm : slotIndex.symm j with
        | .inl p => exact absurd (by rw [hjm] at hj; exact hj) (by simp)
        | .inr r => rfl]
      exact htapes j hj
    · rw [PalPeg.LocalStepFusion.idealRun_step, PalPeg.LocalStepFusion.idealStep]
      show headFreeFields ((tickRule hK base commandsOf baseActs baseLen).nq _ _ _) = _
      rw [show (tickRule hK base commandsOf baseActs baseLen).nq
            (PalPeg.LocalStepFusion.idealRun (tickRule hK base commandsOf baseActs baseLen) blankM x input
              (step + 1)).1 _ _
          = { headControlStep hK (PalPeg.LocalStepFusion.idealRun
                (tickRule hK base commandsOf baseActs baseLen) blankM x input (step + 1)).1
                ⟨(PalPeg.LocalStepFusion.idealRun (tickRule hK base commandsOf baseActs baseLen) blankM x
                  input (step + 1)).1.slot.val - 1, by omega⟩
                (fun tape => PalPeg.Local.readWin blankM K
                  ((PalPeg.LocalStepFusion.idealRun (tickRule hK base commandsOf baseActs baseLen) blankM x
                    input (step + 1)).2 tape)) with
              slot := slotAdvance (PalPeg.LocalStepFusion.idealRun
                (tickRule hK base commandsOf baseActs baseLen) blankM x input (step + 1)).1.slot } from by
        show (if _ = 0 then _ else _) = _
        rw [if_neg hne]]
      exact hfields

/-- **the command each head carries out is the one the table names at step `0`.**  A mode's
branch names four commands, read off the windows of the state the tick starts from, and that is
what the eleven steps after it carry out. -/
theorem commands_afterFirstStep {fppBound dpBound K : ℕ} (hK : 2 ≤ K)
    (base commandsOf baseActs) (baseLen : ∀ q i ws j, (baseActs q i ws j).length ≤ K)
    (x : QPhys fppBound dpBound × (Fin tapeCountM → STape Γm)) (input : Option (Fin 2))
    (hslot0 : x.1.slot.val = 0) (v : Fin 4) :
    (PalPeg.LocalStepFusion.idealRun (tickRule hK base commandsOf baseActs baseLen) blankM x input
        1).1.commands v
      = commandsOf x.1 input (fun tape => PalPeg.Local.readWin blankM K (x.2 tape)) v := by
  rw [PalPeg.LocalStepFusion.idealRun_step, if_pos rfl]
  show ((tickRule hK base commandsOf baseActs baseLen).nq x.1 input _).commands v = _
  show (if x.1.slot.val = 0 then _ else _ : QPhys fppBound dpBound).commands v = _
  rw [if_pos hslot0]
  rfl

/-- the row of the command table for a mode in which no head moves. -/
def stayCommands : Fin 4 → PalPeg.ConcreteLocalMachine.ViewCommand := fun _ => .stay

/-- the row of the command table for the rewind.  Its branch walks the left cursor — and, on a
paired rewind, the centre with it — one cell to the left, and under the division of labour that
motion is a command, read off the same window the branch reads: the rewind is over when the
program's own tape shows the first instruction again, and then nothing moves.

`rewindOneActs` and `rewindPairActs` are the witnesses that these are the right heads and the
right direction: the one walks head `0`, the pair walks heads `0` and `1`, and both do it with
`headStepActs`, the step left. -/
noncomputable def rewindCommands {fppBound dpBound K : ℕ} (first : Fin 9) (live : Bool)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) :
    Fin 4 → PalPeg.ConcreteLocalMachine.ViewCommand :=
  if centreRead ws (progSlot live 8) = encProg first then stayCommands
  else if q.ctl.pair then fun v => if v = 0 ∨ v = 1 then .moveLeft else .stay
    else fun v => if v = 0 then .moveLeft else .stay

/-- the token a cell of the period tape carries, read back.  The inverse of `encToken` on the
token summand; a cell of any other kind reads as the blank, which carries no symbol. -/
def decToken (c : Γm) : Token :=
  match c with
  | .inr (.inr (.inr (.inl t))) => t
  | _ => Token.blank

theorem decToken_encToken (t : Token) : decToken (encToken t) = t := by
  unfold encToken decToken
  by_cases h : t = Token.blank
  · rw [if_pos h, h]; rfl
  · rw [if_neg h]

/-- **when a scan tick steps the chain's verifier.**  A chain steps its verifier in exactly one
shape — the watching one — and then only when it has lag to spend and its period tape offers a
symbol to compare.  Both verdicts move the verifier right: a match consumes the letter, and a
mismatch breaks the chain on the letter it has already moved to.  So the row is decided without
reading the verdict, which is what keeps it inside the window.

The three readings are the tag the control already holds, the sign and zero test of the lag
counter, and the centre cell of the period tape. -/
noncomputable def chainConsumesTest {fppBound dpBound K : ℕ} (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) : Bool :=
  decide (q.chainTag = ChainTag.watchers)
    && (q.polarity 11 && decide (belowRead ws (counterSlot 11) = encSeg PalPeg.LocalCounter.mark))
    && (PalPeg.GalilScaffoldChainConsume.symbol (decToken (centreRead ws periodSlot))).isSome

/-- **the scan's row.**  The three input cursors stand still through a background tick — the
scan reads the input through its comparison, not by walking — and the fourth moves exactly when
the chain consumes. -/
noncomputable def scanCommands {fppBound dpBound K : ℕ} (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) :
    Fin 4 → PalPeg.ConcreteLocalMachine.ViewCommand :=
  fun v => if v = 3 then (if chainConsumesTest q ws then .moveRight else .stay) else .stay

/-- **the letter a cursor is about to reach is a reading of its view.**  Stepping the abstract
head right and reading it is stepping the view right and reading that, so the letter the chain's
verdict compares against is named by the view alone — and the view is what the twelve head slots
hold.

This is the reading the scan's row still owes: the row knows where the cursor goes without the
verdict, but the control's new chain tag does need it. -/
theorem read_right_absHead' {v : PalPeg.LocalInputView.InputView} (q : List (Fin 2))
    (hwf : PalPeg.LocalInputView.WF v)
    (hready : v.gap = true → v.near = [] → PalPeg.RTQueue.toList v.far ≠ []) :
    PalPeg.GalilScaffoldInputHead.read
        (PalPeg.GalilScaffoldChainVerifier.right (PalPeg.LocalArrival.absHead' v q))
      = PalPeg.LocalChain.readV (PalPeg.LocalInputView.moveRight v) := by
  rw [← absHead'_moveRight hwf q hready]
  rfl

/-- **and that reading splits on the parity of the cursor.**  The input head alternates between
a letter and the gap between letters, so a cursor standing on a letter reaches the gap and reads
the gap symbol, and one standing on a gap reaches the next cell of its view.

The gap bit is in the control — `QPhys.gap` — so this first half of the reading costs the machine
nothing.  What the second half still owes is the focus of the stepped view in terms of the three
symbols `viewTopsOfWindows` shows, and that one needs the cursor to have somewhere to go. -/
theorem readV_moveRight (v : PalPeg.LocalInputView.InputView) :
    PalPeg.LocalChain.readV (PalPeg.LocalInputView.moveRight v)
      = if v.gap then
          (PalPeg.LocalInputView.stepRight v).focus.map PalPeg.GalilScaffoldPlace.letter
        else v.focus.map (fun _ => (2 : Fin 3)) := by
  unfold PalPeg.LocalInputView.moveRight
  by_cases hgap : v.gap = true
  · rw [if_pos hgap, if_pos hgap]
    rfl
  · rw [if_neg hgap, if_neg hgap]
    rfl

/-- **the cursor's next cell, when its near stack still has one.**  The step pops the near stack,
so the cell it lands on is the top of that stack — and the top of the near stack is the symbol
`viewTopsOfWindows` reads out of the near tape's window. -/
theorem stepRight_focus_of_near (v : PalPeg.LocalInputView.InputView) (a : Option (Fin 2))
    (rest : List (Option (Fin 2))) (hnear : v.near = a :: rest) :
    (PalPeg.LocalInputView.stepRight v).focus = a := by
  unfold PalPeg.LocalInputView.stepRight
  rw [hnear]

/-- **and when the near stack is spent, the front of the queue.**  The queue is where the letters
that have arrived but not yet been walked over wait, and the readiness condition the view layer
carries says the queue is not empty exactly when the cursor is asked to step with nothing near.

With `stepRight_focus_of_near` this is the second half of the reading the scan's row owes: both
cells the cursor can land on are symbols the windows show. -/
theorem stepRight_focus_of_queue (v : PalPeg.LocalInputView.InputView)
    (hnear : v.near = []) (hinv : PalPeg.RTQueue.Inv v.far)
    (hready : PalPeg.RTQueue.toList v.far ≠ []) :
    (PalPeg.LocalInputView.stepRight v).focus = PalPeg.RTQueue.head? v.far := by
  have hhead : PalPeg.RTQueue.head? v.far = (PalPeg.RTQueue.toList v.far).head? :=
    PalPeg.RTQueue.head?_eq hinv
  unfold PalPeg.LocalInputView.stepRight
  rw [hnear]
  cases hq : PalPeg.RTQueue.head? v.far with
  | none =>
      refine absurd ?_ hready
      rw [hq] at hhead
      cases hl : PalPeg.RTQueue.toList v.far with
      | nil => rfl
      | cons c tail => rw [hl] at hhead; exact absurd hhead (by simp)
  | some a => rfl

/-- **the letter a cursor is about to reach, as the machine reads it.**  The gap bit is in the
control: a cursor on a letter reaches the gap and reads the gap symbol, and one on a gap reaches
the next cell — the top of its near stack, or the front of its queue when the near stack is
spent.  All three are symbols `viewTopsOfWindows` shows.

This is the one reading the chain's verdict needs that is not already a field of the control. -/
noncomputable def landingLetter {fppBound dpBound K : ℕ} (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (v : Fin 4) : Option (Fin 3) :=
  if q.gap v then
    (match (PalPeg.ConcreteLocalMachine.viewTopsOfWindows (q.micro v).2.1
        (viewWindows v ws)).near with
      | some c => some c
      | none => (PalPeg.ConcreteLocalMachine.viewTopsOfWindows (q.micro v).2.1
          (viewWindows v ws)).front).map PalPeg.GalilScaffoldPlace.letter
  else (PalPeg.ConcreteLocalMachine.viewTopsOfWindows (q.micro v).2.1
    (viewWindows v ws)).focus.map (fun _ => (2 : Fin 3))

/-- **and that reading is the letter the cursor really reaches.**  The three symbols the windows
show are the view's own three, the near stack of a represented view carries letters and never a
gap, and the readiness the view layer carries is what says the queue has one when the near stack
does not. -/
theorem landingLetter_eq {fppBound dpBound K : ℕ} (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (v : Fin 4)
    (view : PalPeg.LocalInputView.InputView)
    (htops : PalPeg.ConcreteLocalMachine.viewTopsOfWindows (q.micro v).2.1 (viewWindows v ws)
      = PalPeg.ConcreteLocalMachine.viewTops view)
    (hgap : q.gap v = view.gap) (hcells : PalPeg.LocalViewCells.ViewCells view)
    (hinv : PalPeg.RTQueue.Inv view.far)
    (hready : view.gap = true → view.near = [] → PalPeg.RTQueue.toList view.far ≠ []) :
    landingLetter q ws v = PalPeg.LocalChain.readV (PalPeg.LocalInputView.moveRight view) := by
  unfold landingLetter
  rw [htops, hgap, readV_moveRight view]
  by_cases hg : view.gap = true
  · rw [if_pos hg, if_pos hg]
    congr 1
    obtain ⟨nearLetters, hnl⟩ := PalPeg.LocalViewCells.near_letters hcells
    cases nearLetters with
    | nil =>
        have hnear : view.near = [] := by rw [hnl]; rfl
        rw [stepRight_focus_of_queue view hnear hinv (hready hg hnear)]
        show (match (PalPeg.ConcreteLocalMachine.viewTops view).near with
          | some c => some c
          | none => (PalPeg.ConcreteLocalMachine.viewTops view).front) = _
        unfold PalPeg.ConcreteLocalMachine.viewTops
        rw [hnear]
        rfl
    | cons a rest =>
        have hnear : view.near = some a :: rest.map some := by rw [hnl]; rfl
        rw [stepRight_focus_of_near view (some a) (rest.map some) hnear]
        show (match (PalPeg.ConcreteLocalMachine.viewTops view).near with
          | some c => some c
          | none => (PalPeg.ConcreteLocalMachine.viewTops view).front) = _
        unfold PalPeg.ConcreteLocalMachine.viewTops
        rw [hnear]
        rfl
  · rw [if_neg hg, if_neg hg]
    rfl

/-- **the letter the verifier reaches, from the windows of its view.**  Its view is what the
twelve head slots hold, so the reading the chain's verdict compares against is the machine's
own `landingLetter`. -/
theorem landingLetter_of_verifier {fppBound dpBound K : ℕ} (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (v : Fin 4)
    (view : PalPeg.LocalInputView.InputView) (junk : List (Fin 2))
    (htops : PalPeg.ConcreteLocalMachine.viewTopsOfWindows (q.micro v).2.1 (viewWindows v ws)
      = PalPeg.ConcreteLocalMachine.viewTops view)
    (hgap : q.gap v = view.gap) (hcells : PalPeg.LocalViewCells.ViewCells view)
    (hwf : PalPeg.LocalInputView.WF view) (hinv : PalPeg.RTQueue.Inv view.far)
    (hready : view.gap = true → view.near = [] → PalPeg.RTQueue.toList view.far ≠ []) :
    landingLetter q ws v
      = PalPeg.GalilScaffoldInputHead.read
          (PalPeg.GalilScaffoldChainVerifier.right (PalPeg.LocalArrival.absHead' view junk)) := by
  rw [landingLetter_eq q ws v view htops hgap hcells hinv hready,
    read_right_absHead' junk hwf (fun hg hn => hready hg hn)]

/-- **the chain's verdict, as the machine decides it.**  The period tape offers a symbol or it
does not; if it does, the verdict is whether the letter the verifier reaches is that symbol.
Both readings are in the window: the period tape's centre cell, and the view of the fourth
cursor. -/
noncomputable def watchVerdictTest {fppBound dpBound K : ℕ} (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) : Option Bool :=
  match PalPeg.GalilScaffoldChainConsume.symbol (decToken (centreRead ws periodSlot)) with
  | some a => some (decide (landingLetter q ws 3 = some a))
  | none => none

/-- **and it is the verdict.**  Given the two readings — the symbol the period tape offers and
the letter the verifier reaches — the machine's decision is the chain's. -/
theorem watchVerdictTest_eq {fppBound dpBound K : ℕ} (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (wm : PalPeg.GalilScaffoldChainWatch.State)
    (hsymbol : PalPeg.GalilScaffoldChainConsume.symbol (decToken (centreRead ws periodSlot))
      = PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus)
    (hlanding : landingLetter q ws 3
      = PalPeg.GalilScaffoldInputHead.read
          (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier)) :
    watchVerdictTest q ws = PalPeg.GalilScaffoldChainInputSupply.watchVerdict wm := by
  unfold watchVerdictTest PalPeg.GalilScaffoldChainInputSupply.watchVerdict
  rw [hsymbol, hlanding]
  rfl

/-- **the period tape's symbol is the centre cell of its slot, decoded.**  Which is the first of
the two readings the verdict needs. -/
theorem symbol_centreRead_periodSlot {margin K : ℕ} {x : State GalilVM} {polarity : Fin 16 → Bool}
    {gap : Fin 4 → Bool} {micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl}
    {fppLive dpLive : Bool} {T : Slot → STape Γm}
    (henc : EncTapes margin x polarity gap micro fppLive dpLive T) (hK : K ≤ margin)
    (tape : PalPeg.GalilScaffoldChainPeriod.Tape) (hperiod : periodOf x = some tape) :
    PalPeg.GalilScaffoldChainConsume.symbol
        (decToken (centreRead (fun t => PalPeg.Local.readWin blankM K (tapesOf T t)) periodSlot))
      = PalPeg.GalilScaffoldChainConsume.symbol tape.focus := by
  rw [centreRead_periodSlot henc hK tape hperiod, decToken_encToken]
  rfl

/-- **the control after a watching chain consumes.**  A match keeps the chain watching and hands
its control one letter: the period tape's focus decides whether this letter closes a block, and
that is what moves the phase and the direction.  A mismatch leaves the control exactly as it was
and breaks the chain — the broken chain carries the control it had, on the letter it has already
moved to.

Both arms are decided from two readings of the window, the period tape's centre cell and the view
of the fourth cursor, and from fields the control already holds. -/
noncomputable def scanConsumeNext {fppBound dpBound K : ℕ} (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) : QPhys fppBound dpBound :=
  match watchVerdictTest q ws with
  | some true =>
      { q with
        chainPhase :=
          if PalPeg.GalilScaffoldChainPeriod.isFirst (decToken (centreRead ws periodSlot))
              || PalPeg.GalilScaffoldChainConsume.isLast (decToken (centreRead ws periodSlot)) then
            PalPeg.GalilScaffoldChainConsume.advancePhase q.chainPhase
          else q.chainPhase,
        chainForward :=
          if PalPeg.GalilScaffoldChainPeriod.isFirst (decToken (centreRead ws periodSlot))
              || PalPeg.GalilScaffoldChainConsume.isLast (decToken (centreRead ws periodSlot)) then
            PalPeg.GalilScaffoldChainPeriod.isFirst (decToken (centreRead ws periodSlot))
          else q.chainForward,
        polarity := Function.update
          (Function.update q.polarity 11 (decSignAt (q.polarity 11) (counterSlot 11) ws))
          13 (incSign q.polarity 13 ws) }
  | some false => { q with chainTag := ChainTag.broken }
  | none => q

/-- **the actions a consuming tick names.**  A match spends one unit of the chain's lag, counts
one more letter of its distance, and steps the period tape the way the control says to walk it.
A mismatch spends nothing: the broken chain carries the lag, the margin and the control it had,
and the only thing that moves is the verifier, which the view layer walks.

The two counters a boundary event renames — the block boundary and the one before it — are not
here.  Their renaming is `alias` in the spec of record, and on tapes it is the segment the
counter's own `resetSeg` leaves behind; that representation is not in `counterOf` yet, so the
tick that closes a block is not among the branches this table is proved for. -/
noncomputable def scanConsumeActs {fppBound dpBound K : ℕ} (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) :
    Fin tapeCountM → List (PalPeg.CloseoutCoreEnc12.Act Γm) :=
  fun j =>
    if chainConsumesTest q ws then
      if watchVerdictTest q ws = some true then
        if j = slotIndex (counterSlot 11) then [decAct q 11 ws]
        else if j = slotIndex (counterSlot 13) then [incAct q 13 ws]
        else if j = slotIndex periodSlot then
          [some (centreRead ws periodSlot,
            if (scanConsumeNext q ws).chainForward then
              (.right : PalPeg.CloseoutCoreEnc12.MoveC)
            else (.left : PalPeg.CloseoutCoreEnc12.MoveC))]
        else []
      else []
    else []

/-- **the lag's slot, in a tick that consumes on a match.** -/
theorem scanConsumeActs_lag {fppBound dpBound K : ℕ} (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hconsume : chainConsumesTest q ws = true)
    (hmatch : watchVerdictTest q ws = some true) :
    scanConsumeActs q ws (slotIndex (counterSlot 11)) = [decAct q 11 ws] := by
  unfold scanConsumeActs
  rw [if_pos hconsume, if_pos hmatch, if_pos rfl]

/-- **the distance's slot.** -/
theorem scanConsumeActs_distance {fppBound dpBound K : ℕ} (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hconsume : chainConsumesTest q ws = true)
    (hmatch : watchVerdictTest q ws = some true) :
    scanConsumeActs q ws (slotIndex (counterSlot 13)) = [incAct q 13 ws] := by
  unfold scanConsumeActs
  rw [if_pos hconsume, if_pos hmatch,
    if_neg (fun h => by simpa using slotIndex.injective h), if_pos rfl]

/-- **the period tape's slot.** -/
theorem scanConsumeActs_period {fppBound dpBound K : ℕ} (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hconsume : chainConsumesTest q ws = true)
    (hmatch : watchVerdictTest q ws = some true) :
    scanConsumeActs q ws (slotIndex periodSlot)
      = [some (centreRead ws periodSlot,
          if (scanConsumeNext q ws).chainForward then
            (.right : PalPeg.CloseoutCoreEnc12.MoveC)
          else (.left : PalPeg.CloseoutCoreEnc12.MoveC))] := by
  unfold scanConsumeActs
  rw [if_pos hconsume, if_pos hmatch,
    if_neg (fun h => by simpa [counterSlot, periodSlot] using slotIndex.injective h),
    if_neg (fun h => by simpa [counterSlot, periodSlot] using slotIndex.injective h),
    if_pos rfl]

/-- **and every other slot is left alone.** -/
theorem scanConsumeActs_off {fppBound dpBound K : ℕ} (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (slot : Slot)
    (h11 : slot ≠ counterSlot 11) (h13 : slot ≠ counterSlot 13) (hp : slot ≠ periodSlot) :
    scanConsumeActs q ws (slotIndex slot) = [] := by
  unfold scanConsumeActs
  split_ifs with hc hm h1 h2 h3
  · exact absurd (slotIndex.injective h1) h11
  · exact absurd (slotIndex.injective h2) h13
  · exact absurd (slotIndex.injective h3) hp
  · rfl
  · rfl
  · rfl

theorem scanConsumeActs_length {fppBound dpBound K : ℕ} (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (j : Fin tapeCountM) :
    (scanConsumeActs q ws j).length ≤ 1 := by
  unfold scanConsumeActs
  split_ifs <;> simp

/-- **a tick that does not consume names no action.**  Which is what lets the arm of the scan
that stands still keep the tapes it had. -/
theorem scanConsumeActs_of_quiet {fppBound dpBound K : ℕ} (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hquiet : chainConsumesTest q ws = false) : scanConsumeActs q ws = fun _ => [] := by
  funext j
  unfold scanConsumeActs
  rw [if_neg (by rw [hquiet]; exact Bool.false_ne_true)]

/-- **the command table, as far as the branches that are proved reach.**  Five of them — the end
mark, the walk home, the back half of the choice, the preparation program and the fallback copy —
name nothing but counters, program tapes and period tapes, so every head stands still through
their ticks; the rewind walks one or two cursors left, and the scan moves the chain's verifier
when the chain is consuming.  The rest of the table is a parameter, so filling a row in later
cannot disturb these. -/
noncomputable def modeCommands {fppBound dpBound K : ℕ} (first : Fin 9)
    (rest : QPhys fppBound dpBound → Option (Fin 2) →
      (Fin tapeCountM → PalPeg.Local.Window Γm K) → Fin 4 →
      PalPeg.ConcreteLocalMachine.ViewCommand)
    (q : QPhys fppBound dpBound) (i : Option (Fin 2))
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) :
    Fin 4 → PalPeg.ConcreteLocalMachine.ViewCommand :=
  match q.ctl.mode with
  | PalPeg.GalilScaffoldController.Mode.markEnd => stayCommands
  | PalPeg.GalilScaffoldController.Mode.home => stayCommands
  | PalPeg.GalilScaffoldController.Mode.choose => stayCommands
  | PalPeg.GalilScaffoldController.Mode.fpp => stayCommands
  | PalPeg.GalilScaffoldController.Mode.copy => stayCommands
  | PalPeg.GalilScaffoldController.Mode.rewind => rewindCommands first q.fppLive q ws
  | PalPeg.GalilScaffoldController.Mode.shift =>
      if remainsTest q.polarity ws then rest q i ws else stayCommands
  | PalPeg.GalilScaffoldController.Mode.scan => scanCommands q ws
  | _ => rest q i ws

/-- **the scan's row of the command table.** -/
theorem modeCommands_scan {fppBound dpBound K : ℕ} (first : Fin 9) (rest)
    (q : QPhys fppBound dpBound) (i : Option (Fin 2))
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.scan) :
    modeCommands first rest q i ws = scanCommands q ws := by
  unfold modeCommands
  rw [hmode]

/-- **the operation each of the scan's commands names.**  Three cursors stay where they are and
the fourth steps right exactly when the chain consumes. -/
theorem headOp_scanCommands {fppBound dpBound K : ℕ} (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (v : Fin 4) :
    headOp (scanCommands q ws v)
      = some (if v = 3 ∧ chainConsumesTest q ws then
          PalPeg.GalilScaffoldChainVerifier.right else id) := by
  unfold scanCommands
  by_cases hv : v = 3
  · rw [if_pos hv]
    by_cases hc : chainConsumesTest q ws
    · rw [if_pos hc, if_pos ⟨hv, hc⟩]
      rfl
    · rw [if_neg hc, if_neg (fun h => hc h.2)]
      rfl
  · rw [if_neg hv, if_neg (fun h => hv h.1)]
    rfl

/-- **the shift's row, once the shift is over.**  Nothing moves in the tick that leaves the
shift: the machine's whole state is carried over and only the controller's word changes. -/
theorem modeCommands_shiftExit {fppBound dpBound K : ℕ} (first : Fin 9) (rest)
    (q : QPhys fppBound dpBound) (i : Option (Fin 2))
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.shift)
    (hdone : remainsTest q.polarity ws = false) :
    modeCommands first rest q i ws = stayCommands := by
  unfold modeCommands
  rw [hmode]
  dsimp only
  rw [if_neg (by rw [hdone]; simp)]

/-- **in those five modes the table's row is standing still.**  One statement for the five, since
the reason is the same one in each: the row is written as `stayCommands`. -/
theorem modeCommands_eq_stay {fppBound dpBound K : ℕ} (first : Fin 9) (rest)
    (q : QPhys fppBound dpBound)
    (i : Option (Fin 2)) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd
      ∨ q.ctl.mode = PalPeg.GalilScaffoldController.Mode.home
      ∨ q.ctl.mode = PalPeg.GalilScaffoldController.Mode.choose
      ∨ q.ctl.mode = PalPeg.GalilScaffoldController.Mode.fpp
      ∨ q.ctl.mode = PalPeg.GalilScaffoldController.Mode.copy) :
    modeCommands first rest q i ws = stayCommands := by
  unfold modeCommands
  rcases hmode with h | h | h | h | h <;> rw [h]

/-- **the rewind's row, and the two heads it names.**  In the rewind the table gives the left
cursor a step left, and the centre one too when the rewind is paired; the other cursors stand
still, and nothing moves at all once the program's tape shows the first instruction. -/
theorem modeCommands_rewind {fppBound dpBound K : ℕ} (first : Fin 9) (rest)
    (q : QPhys fppBound dpBound) (i : Option (Fin 2))
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind) :
    modeCommands first rest q i ws = rewindCommands first q.fppLive q ws := by
  unfold modeCommands
  rw [hmode]

theorem rewindCommands_atFirst {fppBound dpBound K : ℕ} (first : Fin 9) (live : Bool)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hat : centreRead ws (progSlot live 8) = encProg first) :
    rewindCommands first live q ws = stayCommands := by
  unfold rewindCommands
  rw [if_pos hat]

theorem rewindCommands_walks {fppBound dpBound K : ℕ} (first : Fin 9) (live : Bool)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hnot : ¬ centreRead ws (progSlot live 8) = encProg first) (v : Fin 4)
    (hv : v = 0 ∨ (q.ctl.pair = true ∧ v = 1)) :
    rewindCommands first live q ws v = .moveLeft := by
  unfold rewindCommands
  rw [if_neg hnot]
  cases hpair : q.ctl.pair
  · rw [if_neg (by decide)]
    cases hv with
    | inl h => rw [if_pos h]
    | inr h => exact absurd (hpair.symm.trans h.1) (by simp)
  · rw [if_pos rfl]
    cases hv with
    | inl h => rw [if_pos (Or.inl h)]
    | inr h => rw [if_pos (Or.inr h.2)]

theorem rewindCommands_still {fppBound dpBound K : ℕ} (first : Fin 9) (live : Bool)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (v : Fin 4)
    (hv : v ≠ 0) (hv1 : q.ctl.pair = true → v ≠ 1) :
    rewindCommands first live q ws v = .stay := by
  unfold rewindCommands
  split
  · rfl
  · cases hpair : q.ctl.pair
    · rw [if_neg (by decide), if_neg hv]
    · rw [if_pos rfl,
        if_neg (fun h => by cases h with
          | inl h0 => exact hv h0
          | inr h1 => exact hv1 hpair h1)]


/-- **the heads of the encoding after a tick, from the command the table names.**  This is the
head side of a tick in the form a mode's branch meets it: the branch names a row of the command
table, the row names this head's command, and the command names the operation the abstract tick
does to this head.  The head's tapes, the twelve steps and the view layer are all behind it.

A row that stands still gives `head' = head` and asks nothing; a row that names a step left asks
nothing either; only a step right carries the arrival condition. -/
theorem heads_afterTableTick {fppBound dpBound K margin : ℕ} (hK : 2 ≤ K) (hmargin : K ≤ margin)
    (base commandsOf baseActs) (baseLen : ∀ q i ws j, (baseActs q i ws j).length ≤ K) (v : Fin 4)
    (x : QPhys fppBound dpBound × (Fin tapeCountM → STape Γm)) (input : Option (Fin 2))
    (hslot0 : x.1.slot.val = 0)
    (command : PalPeg.ConcreteLocalMachine.ViewCommand)
    (hrow : commandsOf x.1 input (fun tape => PalPeg.Local.readWin blankM K (x.2 tape)) v
      = command)
    (hfused : ∀ tape, PalPeg.LocalStepFusion.iterRadius K 12 ≤ PalPeg.Local.pos (x.2 tape))
    (view : PalPeg.LocalInputView.InputView) (hwf : PalPeg.LocalInputView.WF view)
    (hcells : PalPeg.LocalViewCells.ViewCells view)
    (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (hold : ∀ t, x.2 (slotIndex (headSlot v t)) = mapTape encCell (viewTapes t))
    (hrep : PalPeg.ConcreteLocalMachine.ViewRep margin view (x.1.gap v) (x.1.micro v) viewTapes)
    (howed : (x.1.micro v).2.2.2 = 0)
    (head head' : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (habs : PalPeg.LocalArrival.absHead' view [] = head)
    (f : PalPeg.GalilScaffoldInputHead.PlaceHead → PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hf : headOp command = some f) (hhead' : head' = f head)
    (hready : command = .moveRight →
      view.gap = true → view.near = [] → PalPeg.RTQueue.toList view.far ≠ []) :
    ∃ (view' : PalPeg.LocalInputView.InputView)
        (viewTapes' : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc),
      PalPeg.LocalArrival.absHead' view' [] = head' ∧
        PalPeg.ConcreteLocalMachine.ViewRep margin view'
            ((PalPeg.LocalStepFusion.idealStep
              (PalPeg.LocalStepFusion.iterRule
                (tickRule hK base commandsOf baseActs baseLen) 12) blankM x input).1.gap v)
            ((PalPeg.LocalStepFusion.idealStep
              (PalPeg.LocalStepFusion.iterRule
                (tickRule hK base commandsOf baseActs baseLen) 12) blankM x input).1.micro v)
            viewTapes' ∧
          (∀ i, (PalPeg.LocalStepFusion.idealStep
              (PalPeg.LocalStepFusion.iterRule
                (tickRule hK base commandsOf baseActs baseLen) 12) blankM x input).2
                (slotIndex (headSlot v i)) = mapTape encCell (viewTapes' i)) ∧
            PalPeg.LocalViewCells.ViewCells view' ∧ PalPeg.LocalInputView.WF view' := by
  have hcommand : (PalPeg.LocalStepFusion.idealRun
      (tickRule hK base commandsOf baseActs baseLen) blankM x input 1).1.commands v = command := by
    rw [commands_afterFirstStep hK base commandsOf baseActs baseLen x input hslot0 v, hrow]
  exact heads_afterFusedStep hK hmargin base commandsOf baseActs baseLen v x input hslot0 hfused
    view hwf hcells viewTapes hold hrep howed head head' habs f (by rw [hcommand]; exact hf)
    hhead' (fun hmove => hready (hcommand.symm.trans hmove))

/-- **a tick in which no head moves keeps the heads of the encoding.**  Every mode whose branch
touches only counters, program tapes and period tapes gets its head obligations from here with no
work of its own: the row is `stayCommands`, and standing still is the identity on the abstract
head. -/
theorem heads_afterStillTick {fppBound dpBound K margin : ℕ} (hK : 2 ≤ K) (hmargin : K ≤ margin)
    (base commandsOf baseActs) (baseLen : ∀ q i ws j, (baseActs q i ws j).length ≤ K) (v : Fin 4)
    (x : QPhys fppBound dpBound × (Fin tapeCountM → STape Γm)) (input : Option (Fin 2))
    (hslot0 : x.1.slot.val = 0)
    (hstay : commandsOf x.1 input (fun tape => PalPeg.Local.readWin blankM K (x.2 tape))
      = stayCommands)
    (hfused : ∀ tape, PalPeg.LocalStepFusion.iterRadius K 12 ≤ PalPeg.Local.pos (x.2 tape))
    (view : PalPeg.LocalInputView.InputView) (hwf : PalPeg.LocalInputView.WF view)
    (hcells : PalPeg.LocalViewCells.ViewCells view)
    (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (hold : ∀ t, x.2 (slotIndex (headSlot v t)) = mapTape encCell (viewTapes t))
    (hrep : PalPeg.ConcreteLocalMachine.ViewRep margin view (x.1.gap v) (x.1.micro v) viewTapes)
    (howed : (x.1.micro v).2.2.2 = 0)
    (head : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (habs : PalPeg.LocalArrival.absHead' view [] = head) :
    ∃ (view' : PalPeg.LocalInputView.InputView)
        (viewTapes' : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc),
      PalPeg.LocalArrival.absHead' view' [] = head ∧
        PalPeg.ConcreteLocalMachine.ViewRep margin view'
            ((PalPeg.LocalStepFusion.idealStep
              (PalPeg.LocalStepFusion.iterRule
                (tickRule hK base commandsOf baseActs baseLen) 12) blankM x input).1.gap v)
            ((PalPeg.LocalStepFusion.idealStep
              (PalPeg.LocalStepFusion.iterRule
                (tickRule hK base commandsOf baseActs baseLen) 12) blankM x input).1.micro v)
            viewTapes' ∧
          (∀ i, (PalPeg.LocalStepFusion.idealStep
              (PalPeg.LocalStepFusion.iterRule
                (tickRule hK base commandsOf baseActs baseLen) 12) blankM x input).2
                (slotIndex (headSlot v i)) = mapTape encCell (viewTapes' i)) ∧
            PalPeg.LocalViewCells.ViewCells view' ∧ PalPeg.LocalInputView.WF view' :=
  heads_afterTableTick hK hmargin base commandsOf baseActs baseLen v x input hslot0 .stay
    (by rw [hstay]; rfl) hfused view hwf hcells viewTapes hold hrep howed head head habs id rfl rfl
    (fun h => absurd h (by simp))

/-- **a tick whose row walks this head one cell left keeps the heads of the encoding, with that
head stepped left.**  The step left asks nothing of the head: a half-step moves only its bit and
a full step pops its back stack, which is what the abstract cursor does. -/
theorem heads_afterLeftTick {fppBound dpBound K margin : ℕ} (hK : 2 ≤ K) (hmargin : K ≤ margin)
    (base commandsOf baseActs) (baseLen : ∀ q i ws j, (baseActs q i ws j).length ≤ K) (v : Fin 4)
    (x : QPhys fppBound dpBound × (Fin tapeCountM → STape Γm)) (input : Option (Fin 2))
    (hslot0 : x.1.slot.val = 0)
    (hleft : commandsOf x.1 input (fun tape => PalPeg.Local.readWin blankM K (x.2 tape)) v
      = .moveLeft)
    (hfused : ∀ tape, PalPeg.LocalStepFusion.iterRadius K 12 ≤ PalPeg.Local.pos (x.2 tape))
    (view : PalPeg.LocalInputView.InputView) (hwf : PalPeg.LocalInputView.WF view)
    (hcells : PalPeg.LocalViewCells.ViewCells view)
    (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (hold : ∀ t, x.2 (slotIndex (headSlot v t)) = mapTape encCell (viewTapes t))
    (hrep : PalPeg.ConcreteLocalMachine.ViewRep margin view (x.1.gap v) (x.1.micro v) viewTapes)
    (howed : (x.1.micro v).2.2.2 = 0)
    (head : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (habs : PalPeg.LocalArrival.absHead' view [] = head) :
    ∃ (view' : PalPeg.LocalInputView.InputView)
        (viewTapes' : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc),
      PalPeg.LocalArrival.absHead' view' []
          = PalPeg.GalilScaffoldInputHead.left head ∧
        PalPeg.ConcreteLocalMachine.ViewRep margin view'
            ((PalPeg.LocalStepFusion.idealStep
              (PalPeg.LocalStepFusion.iterRule
                (tickRule hK base commandsOf baseActs baseLen) 12) blankM x input).1.gap v)
            ((PalPeg.LocalStepFusion.idealStep
              (PalPeg.LocalStepFusion.iterRule
                (tickRule hK base commandsOf baseActs baseLen) 12) blankM x input).1.micro v)
            viewTapes' ∧
          (∀ i, (PalPeg.LocalStepFusion.idealStep
              (PalPeg.LocalStepFusion.iterRule
                (tickRule hK base commandsOf baseActs baseLen) 12) blankM x input).2
                (slotIndex (headSlot v i)) = mapTape encCell (viewTapes' i)) ∧
            PalPeg.LocalViewCells.ViewCells view' ∧ PalPeg.LocalInputView.WF view' :=
  heads_afterTableTick hK hmargin base commandsOf baseActs baseLen v x input hslot0 .moveLeft
    hleft hfused view hwf hcells viewTapes hold hrep howed head
    (PalPeg.GalilScaffoldInputHead.left head) habs PalPeg.GalilScaffoldInputHead.left rfl rfl
    (fun h => absurd h (by simp))

/-- **two tapes that a sweep cannot tell apart give the same window.**  `TEqG` says the head
stands in the same place and every cell reads the same, and a window is nothing but readings
around the head — which is why the rule cannot tell a swept tape from the ideal one, and why the
encoding may be taken up to `TEqG` at all. -/
theorem readWin_congr_teqG {Γ : Type} {blank : Γ} {K : ℕ} {T T' : PalPeg.Program.STape Γ}
    (h : PalPeg.CloseoutCoreEnc12.TEqG blank T T') :
    PalPeg.Local.readWin blank K T = PalPeg.Local.readWin blank K T' := by
  funext i
  rw [PalPeg.Local.readWin_eq, PalPeg.Local.readWin_eq, h.1, h.2]

/-- **one action does not tell two tapes a sweep cannot tell apart apart either.**  Where the
head lands is fixed by where it stood, and what each cell reads afterwards is fixed by what it
read before and by the symbol written under the head — both of which `TEqG` already gives. -/
theorem teqG_applyAction {Γ : Type} (blank : Γ) {T T' : PalPeg.Program.STape Γ}
    (h : PalPeg.CloseoutCoreEnc12.TEqG blank T T')
    (sm : Γ × PegSeparation.RealTimeTM.Move) :
    PalPeg.CloseoutCoreEnc12.TEqG blank (T.applyAction blank sm) (T'.applyAction blank sm) := by
  obtain ⟨written, move⟩ := sm
  refine ⟨?_, fun p => ?_⟩
  · rw [PalPeg.Local.pos_applyAction, PalPeg.Local.pos_applyAction, h.1]
  · rw [PalPeg.Local.rd_applyAction, PalPeg.Local.rd_applyAction, h.1, h.2]

theorem teqG_actOnG {Γ : Type} (blank : Γ) {T T' : PalPeg.Program.STape Γ}
    (h : PalPeg.CloseoutCoreEnc12.TEqG blank T T') (a : PalPeg.CloseoutCoreEnc12.Act Γ) :
    PalPeg.CloseoutCoreEnc12.TEqG blank (PalPeg.CloseoutCoreEnc12.actOnG blank T a)
      (PalPeg.CloseoutCoreEnc12.actOnG blank T' a) := by
  cases a with
  | none => exact h
  | some sm => exact teqG_applyAction blank h sm

/-- **and neither does a whole composite step.**  So the ideal step of a rule on a swept tape is
the ideal step on the tape it was swept from, up to the same equality — which is what lets a
tick's obligation be stated on the sweep closure of the encoding. -/
theorem teqG_actList {Γ : Type} (blank : Γ) :
    ∀ (as : List (PalPeg.CloseoutCoreEnc12.Act Γ)) {T T' : PalPeg.Program.STape Γ},
      PalPeg.CloseoutCoreEnc12.TEqG blank T T' →
      PalPeg.CloseoutCoreEnc12.TEqG blank (PalPeg.CloseoutCoreEnc12.actList blank T as)
        (PalPeg.CloseoutCoreEnc12.actList blank T' as)
  | [], _, _, h => h
  | a :: rest, T, T', h => by
    rw [PalPeg.CloseoutCoreEnc12.actList_cons, PalPeg.CloseoutCoreEnc12.actList_cons]
    exact teqG_actList blank rest (teqG_actOnG blank h a)

/-- **the ideal step of a rule does not see a sweep.**  The control it reaches is the same, and
the tapes it leaves are the same up to the equality a sweep respects: the rule reads only
windows, and a composite step carries the equality. -/
theorem idealStep_congr_teqG {Q Γ : Type} {t K : ℕ}
    (R : PalPeg.CloseoutCoreEnc12.ActRule (Fin 2) Q Γ t K) (blank : Γ) (q : Q)
    (T T' : Fin t → PalPeg.Program.STape Γ)
    (h : ∀ tape, PalPeg.CloseoutCoreEnc12.TEqG blank (T tape) (T' tape))
    (input : Option (Fin 2)) :
    (PalPeg.LocalStepFusion.idealStep R blank (q, T) input).1
        = (PalPeg.LocalStepFusion.idealStep R blank (q, T') input).1 ∧
      ∀ tape, PalPeg.CloseoutCoreEnc12.TEqG blank
        ((PalPeg.LocalStepFusion.idealStep R blank (q, T) input).2 tape)
        ((PalPeg.LocalStepFusion.idealStep R blank (q, T') input).2 tape) := by
  have hwin : (fun tape => PalPeg.Local.readWin blank K (T tape))
      = fun tape => PalPeg.Local.readWin blank K (T' tape) := by
    funext tape
    exact readWin_congr_teqG (h tape)
  refine ⟨?_, fun tape => ?_⟩
  · show R.nq q input (fun tape => PalPeg.Local.readWin blank K (T tape)) = _
    rw [hwin]
    rfl
  · show PalPeg.CloseoutCoreEnc12.TEqG blank
      (PalPeg.CloseoutCoreEnc12.actList blank (T tape)
        (R.acts q input (fun tape => PalPeg.Local.readWin blank K (T tape)) tape)) _
    rw [hwin]
    exact teqG_actList blank _ (h tape)

/-- **and so a tick's obligation on the encoding gives the obligation on its sweep closure.**
The consumer of the local realization asks for the closure, because what a machine's tape really
holds after a sweep is only the ideal tape up to `TEqG`; this is where that gap is crossed, once.
-/
theorem sweepClosure_afterStep {Q Γ : Type} {t K : ℕ}
    (R : PalPeg.CloseoutCoreEnc12.ActRule (Fin 2) Q Γ t K) (blank : Γ)
    (Enc0 : State GalilVM → Q × (Fin t → PalPeg.Program.STape Γ) → Prop)
    (x y : State GalilVM) (q : Q) (T : Fin t → PalPeg.Program.STape Γ)
    (hstep : ∀ ideal, Enc0 x (q, ideal) →
      Enc0 y (PalPeg.LocalStepFusion.idealStep R blank (q, ideal) none))
    (h : PalPeg.MachineStep.sweepClosure blank Enc0 x (q, T)) :
    PalPeg.MachineStep.sweepClosure blank Enc0 y
      (PalPeg.LocalStepFusion.idealStep R blank (q, T) none) := by
  obtain ⟨ideal, henc, hteq⟩ := h
  obtain ⟨hnq, htapes⟩ := idealStep_congr_teqG R blank q ideal T hteq none
  exact ⟨(PalPeg.LocalStepFusion.idealStep R blank (q, ideal) none).2,
    by rw [← hnq]; exact hstep ideal henc, htapes⟩

/-- **a slot that is not a head's holds, after the tick, exactly what the mode's branch wrote at
step `0`.**  Step `0` gives it the branch's own actions and the eleven steps after it give it
none, so whatever the branch is already proved to leave there is what the tick leaves there. -/
theorem tickRule_otherSlots {fppBound dpBound K : ℕ} (hK : 2 ≤ K) (base commandsOf baseActs)
    (baseLen : ∀ q i ws j, (baseActs q i ws j).length ≤ K)
    (x : QPhys fppBound dpBound × (Fin tapeCountM → STape Γm)) (input : Option (Fin 2))
    (hslot0 : x.1.slot.val = 0) (j : Fin tapeCountM) (hj : (slotIndex.symm j).isLeft = false) :
    (PalPeg.LocalStepFusion.idealRun (tickRule hK base commandsOf baseActs baseLen) blankM x input
        12).2 j
      = PalPeg.CloseoutCoreEnc12.actList blankM (x.2 j)
          (baseActs x.1 input (fun tape => PalPeg.Local.readWin blankM K (x.2 tape)) j) := by
  rw [(tickRule_still hK base commandsOf baseActs baseLen x input hslot0 12 (by omega)
      (by omega)).1 j hj,
    PalPeg.LocalStepFusion.idealRun_step, if_pos rfl]
  show PalPeg.CloseoutCoreEnc12.actList blankM _
      ((tickRule hK base commandsOf baseActs baseLen).acts x.1 input _ j) = _
  rw [show (tickRule hK base commandsOf baseActs baseLen).acts x.1 input
        (fun tape => PalPeg.Local.readWin blankM K
          ((PalPeg.LocalStepFusion.idealRun (tickRule hK base commandsOf baseActs baseLen) blankM
            x input 0).2 tape)) j
      = baseActs x.1 input (fun tape => PalPeg.Local.readWin blankM K (x.2 tape)) j from by
    show (if x.1.slot.val = 0 then _ else _) = _
    rw [if_pos hslot0, if_neg (by rw [hj]; simp)]
    rfl]
  rfl

/-- **the fields of the control that are not a view's hold, after the tick, exactly what the
mode's branch put there at step `0`.**  Same reason: step `0` is the branch and the eleven steps
after it write only a view's own three fields. -/
theorem tickRule_headFree {fppBound dpBound K : ℕ} (hK : 2 ≤ K) (base commandsOf baseActs)
    (baseLen : ∀ q i ws j, (baseActs q i ws j).length ≤ K)
    (x : QPhys fppBound dpBound × (Fin tapeCountM → STape Γm)) (input : Option (Fin 2))
    (hslot0 : x.1.slot.val = 0) :
    headFreeFields (PalPeg.LocalStepFusion.idealRun
        (tickRule hK base commandsOf baseActs baseLen) blankM x input 12).1
      = headFreeFields
          (base x.1 input (fun tape => PalPeg.Local.readWin blankM K (x.2 tape))) := by
  rw [(tickRule_still hK base commandsOf baseActs baseLen x input hslot0 12 (by omega)
      (by omega)).2,
    PalPeg.LocalStepFusion.idealRun_step, if_pos rfl]
  show headFreeFields ((tickRule hK base commandsOf baseActs baseLen).nq x.1 input _) = _
  show headFreeFields (if x.1.slot.val = 0 then _ else _ : QPhys fppBound dpBound) = _
  rw [if_pos hslot0]
  rfl

/-- **what the finite control says about the state depends only on the fields that are not a
view's.**  Every one of the eighteen fields of `EncControl` speaks of the mode, the chain, the
two programs, the search, the cursors' half-steps or the two bits about the input heads' places —
and all of those are in `headFreeFields`.  None of them speaks of a view's gap bit, its queue job
or its micro-schedule.

So a tick carries `EncControl` across for free: by `tickRule_headFree` the tick leaves those
fields exactly as the mode's branch put them, and the branch is already proved to put them right.
-/
theorem encControl_congr {fppBound dpBound : ℕ} {w : List (Fin 2)} {x : State GalilVM}
    {q q' : QPhys fppBound dpBound} (hfree : headFreeFields q = headFreeFields q')
    (h : EncControl w x q) : EncControl w x q' := by
  simp only [headFreeFields, Prod.mk.injEq] at hfree
  obtain ⟨hctl, hchainTag, hchainPhase, hchainForward, hchainBroken, hfppMode, hfppFinalStage,
    hfppPc, hfppDone, hdpPc, hdpDone, hsearchMode, hsearchFinalStage, hsearchQuarter,
    hperiodOnly, hplaceGap, honLetter, hleftFirst, -, -, -⟩ := hfree
  exact
    { ctl := by rw [← hctl]; exact h.ctl
      chainTag := by rw [← hchainTag]; exact h.chainTag
      chainPhase := by rw [← hchainPhase]; exact h.chainPhase
      chainForward := by rw [← hchainForward]; exact h.chainForward
      chainBroken := by rw [← hchainBroken]; exact h.chainBroken
      fppMode := by rw [← hfppMode]; exact h.fppMode
      fppFinalStage := by rw [← hfppFinalStage]; exact h.fppFinalStage
      fppPc := by rw [← hfppPc]; exact h.fppPc
      fppDone := by rw [← hfppDone]; exact h.fppDone
      dpPc := by rw [← hdpPc]; exact h.dpPc
      dpDone := by rw [← hdpDone]; exact h.dpDone
      searchMode := by rw [← hsearchMode]; exact h.searchMode
      searchFinalStage := by rw [← hsearchFinalStage]; exact h.searchFinalStage
      searchQuarter := by rw [← hsearchQuarter]; exact h.searchQuarter
      periodOnly := by rw [← hperiodOnly]; exact h.periodOnly
      placeGap := fun i place hp => by rw [← hplaceGap]; exact h.placeGap i place hp
      onLetter := by rw [← honLetter]; exact h.onLetter
      leftFirst := by rw [← hleftFirst]; exact h.leftFirst }

/-- **the tapes of a tick whose cursors moved, from the tapes of its step.**  The step's table
writes the counters, the programs and the chain's own tapes; the twelve slots of each cursor are
written afterwards by the view layer.  So the encoding after a tick is assembled from two
different states: everything but the cursors is read off the state the step reached, and the
cursors are read off the state the tick reached.

`encTapes_replaceHeads` is the case in which those two states are the same, which is every branch
whose cursors move left or stand still — a left step is one action, so the step's own table can
write it.  A step right is not one action: it is eleven slots of the view layer.  This is the
theorem that lets such a branch be assembled. -/
theorem encTapes_replaceHeadsOfState {margin : ℕ} {z y : State GalilVM}
    {polarity polarity' : Fin 16 → Bool} {gap gap' : Fin 4 → Bool}
    {micro micro' : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl}
    {fppLive dpLive fppLive' dpLive' : Bool} {T T' : Slot → STape Γm}
    (h : EncTapes margin z polarity gap micro fppLive dpLive T)
    (hfpp : ∀ i, y.vm.fpp.program.config.tapes i = z.vm.fpp.program.config.tapes i)
    (hdp : ∀ i, y.vm.dp.config.tapes i = z.vm.dp.config.tapes i)
    (hcounters : counterOf y = counterOf z) (hplaces : placeOf y = placeOf z)
    (hperiod : periodOf y = periodOf z) (hanswer : answerOf y = answerOf z)
    (hother : ∀ slot : Slot, (∀ v i, slot ≠ headSlot v i) → T' slot = T slot)
    (hmargins : ∀ (v : Fin 4) (i : Fin 12), margin ≤ PalPeg.Local.pos (T' (headSlot v i)))
    (hpolarity : polarity' = polarity) (hfppLive : fppLive' = fppLive)
    (hdpLive : dpLive' = dpLive)
    (hheads : ∀ (v : Fin 4) head, headOf y v = some head →
      ∃ (view : PalPeg.LocalInputView.InputView)
          (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc),
        PalPeg.LocalArrival.absHead' view [] = head ∧
          PalPeg.ConcreteLocalMachine.ViewRep margin view (gap' v) (micro' v) viewTapes ∧
          (∀ i, T' (headSlot v i) = mapTape encCell (viewTapes i)) ∧
            PalPeg.LocalViewCells.ViewCells view ∧ PalPeg.LocalInputView.WF view)
    (hidleHead : headOf y 3 = none → HeadSlotsRep margin gap' micro' T' 3) :
    EncTapes margin y polarity' gap' micro' fppLive' dpLive' T' := by
  subst hpolarity
  subst hfppLive
  subst hdpLive
  refine
    { margins := fun slot => ?_
      heads := hheads
      idleHead := hidleHead
      fpp := fun i => ?_
      dp := fun i => ?_
      idleShape := fun i => ?_
      counters := fun c value hc => ?_
      places := fun i place hp => ?_
      mirrors := fun m value hm => ?_
      period := fun tape hp => ?_
      answer := fun tape ha => ?_ }
  · match slot with
    | .inl p => exact hmargins p.1 p.2
    | .inr r =>
      rw [hother (Sum.inr r) (by intro v i hEq; exact absurd hEq (by simp [headSlot]))]
      exact h.margins _
  · rw [hother _ (by intro v t hEq; exact absurd hEq (progSlotOf_ne_headSlot _ _ v t)), hfpp i]
    exact h.fpp i
  · rw [hother _ (by intro v t hEq; exact absurd hEq (dpSlotOf_ne_headSlot _ _ v t)), hdp i]
    exact h.dp i
  · obtain ⟨raw, hraw⟩ := h.idleShape i
    exact ⟨raw, by
      rw [hother _ (by intro v t hEq; exact absurd hEq (progSlotOf_ne_headSlot _ _ v t))]
      exact hraw⟩
  · obtain ⟨seg, hseg, hslot⟩ := h.counters c value (by rw [← congrFun hcounters c]; exact hc)
    exact ⟨seg, hseg, by
      rw [hother _ (by intro v i hEq; exact absurd hEq (by simp [counterSlot, headSlot]))]
      exact hslot⟩
  · obtain ⟨stack, junk, hsealed, hjunk, hstack, hslot⟩ :=
      h.places i place (by rw [← congrFun hplaces i]; exact hp)
    exact ⟨stack, junk, hsealed, hjunk, hstack, by
      rw [hother _ (by intro v i hEq; exact absurd hEq (by simp [placeSlot, headSlot]))]
      exact hslot⟩
  · obtain ⟨seg, hseg, hslot⟩ :=
      h.mirrors m value (by rw [← congrFun hcounters _]; exact hm)
    exact ⟨seg, hseg, by
      rw [hother _ (by intro v i hEq; exact absurd hEq (by simp [mirrorSlot, headSlot]))]
      exact hslot⟩
  · rw [hother _ (by intro v t hEq; exact absurd hEq (by simp [headSlot]))]
    exact h.period tape (by rw [← hperiod]; exact hp)
  · rw [hother _ (by intro v t hEq; exact absurd hEq (by simp [headSlot]))]
    exact h.answer tape (by rw [← hanswer]; exact ha)

/-- **what the tapes of the encoding say, with the heads replaced.**  Every field of `EncTapes`
but `heads` and `margins` names a slot that is not a head's — the two programs, the counter bank,
the mirrors, the cursors, the period tape, the answer — so a tick that leaves those slots as the
mode's branch wrote them carries all of those fields across, and the heads are supplied on their
own.  The margins are needed of every slot, the heads' included, which is what the last
hypothesis is for.

This is the other half of `encControl_congr`: between them, a tick's whole obligation is the
mode's branch on the slots that are not a head's, plus the heads. -/
theorem encTapes_replaceHeads {margin : ℕ} {x : State GalilVM} {polarity polarity' : Fin 16 → Bool}
    {gap gap' : Fin 4 → Bool}
    {micro micro' : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl}
    {fppLive dpLive fppLive' dpLive' : Bool} {T T' : Slot → STape Γm}
    (h : EncTapes margin x polarity gap micro fppLive dpLive T)
    (hother : ∀ slot : Slot, (∀ v i, slot ≠ headSlot v i) → T' slot = T slot)
    (hmargins : ∀ (v : Fin 4) (i : Fin 12), margin ≤ PalPeg.Local.pos (T' (headSlot v i)))
    (hpolarity : polarity' = polarity) (hfppLive : fppLive' = fppLive)
    (hdpLive : dpLive' = dpLive)
    (hheads : ∀ (v : Fin 4) head, headOf x v = some head →
      ∃ (view : PalPeg.LocalInputView.InputView)
          (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc),
        PalPeg.LocalArrival.absHead' view [] = head ∧
          PalPeg.ConcreteLocalMachine.ViewRep margin view (gap' v) (micro' v) viewTapes ∧
          (∀ i, T' (headSlot v i) = mapTape encCell (viewTapes i)) ∧
            PalPeg.LocalViewCells.ViewCells view ∧ PalPeg.LocalInputView.WF view)
    (hidleHead : headOf x 3 = none → HeadSlotsRep margin gap' micro' T' 3) :
    EncTapes margin x polarity' gap' micro' fppLive' dpLive' T' := by
  subst hpolarity
  subst hfppLive
  subst hdpLive
  refine
    { margins := fun slot => ?_
      heads := hheads
      idleHead := hidleHead
      fpp := fun i => ?_
      dp := fun i => ?_
      idleShape := fun i => ?_
      counters := fun c value hc => ?_
      places := fun i place hp => ?_
      mirrors := fun m value hm => ?_
      period := fun tape hperiod => ?_
      answer := fun tape hanswer => ?_ }
  · match slot with
    | .inl p => exact hmargins p.1 p.2
    | .inr r =>
      rw [hother (Sum.inr r) (by intro v i hEq; exact absurd hEq (by simp [headSlot]))]
      exact h.margins _
  · rw [hother _ (by intro v t hEq; exact absurd hEq (progSlotOf_ne_headSlot _ _ v t))]
    exact h.fpp i
  · rw [hother _ (by intro v t hEq; exact absurd hEq (dpSlotOf_ne_headSlot _ _ v t))]
    exact h.dp i
  · obtain ⟨raw, hraw⟩ := h.idleShape i
    exact ⟨raw, by
      rw [hother _ (by intro v t hEq; exact absurd hEq (progSlotOf_ne_headSlot _ _ v t))]
      exact hraw⟩
  · obtain ⟨seg, hseg, hslot⟩ := h.counters c value hc
    exact ⟨seg, hseg, by
      rw [hother _ (by intro v i hEq; exact absurd hEq (by simp [counterSlot, headSlot]))]
      exact hslot⟩
  · obtain ⟨stack, junk, hsealed, hjunk, hstack, hslot⟩ := h.places i place hp
    exact ⟨stack, junk, hsealed, hjunk, hstack, by
      rw [hother _ (by intro v i hEq; exact absurd hEq (by simp [placeSlot, headSlot]))]
      exact hslot⟩
  · obtain ⟨seg, hseg, hslot⟩ := h.mirrors m value hm
    exact ⟨seg, hseg, by
      rw [hother _ (by intro v i hEq; exact absurd hEq (by simp [mirrorSlot, headSlot]))]
      exact hslot⟩
  · rw [hother _ (by intro v t hEq; exact absurd hEq (by simp [headSlot]))]
    exact h.period tape hperiod
  · rw [hother _ (by intro v t hEq; exact absurd hEq (by simp [headSlot]))]
    exact h.answer tape hanswer

/-- **a mirror stays a mirror.**  If the fourth cursor's view abstracts to the centre and the
row names for it whatever it names for the centre, then after the tick it abstracts to the centre
again — because the command names the operation the tick does to a cursor, and the same command
names the same operation.

This is the maintenance the mirror costs, and it is one rewrite: the whole of the argument is
that `absHead'_viewApply` does not care which cursor it is talking about. -/
theorem absHead'_mirror_afterCommand {view : PalPeg.LocalInputView.InputView}
    (hwf : PalPeg.LocalInputView.WF view) (command : PalPeg.ConcreteLocalMachine.ViewCommand)
    (f : PalPeg.GalilScaffoldInputHead.PlaceHead → PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hf : headOp command = some f)
    (hready : command = .moveRight →
      view.gap = true → view.near = [] → PalPeg.RTQueue.toList view.far ≠ [])
    {centre : PalPeg.GalilScaffoldInputHead.PlaceHead}
    (hmirror : PalPeg.LocalArrival.absHead' view [] = centre) :
    PalPeg.LocalArrival.absHead' (PalPeg.ConcreteLocalMachine.viewApply command view) []
      = f centre := by
  rw [absHead'_viewApply hwf [] command hready f hf, hmirror]

/-- **the ten modes, as the dispatch of a tick's obligation sees them.**  A tick's obligation has
to be met in every mode, so the work of meeting it is exactly this list, and what is left of it
is measurable: the branches carried through the division of labour so far are the end mark, the
walk home, the back half of the choice, the preparation program, the fallback copy and the three
branches of the rewind. -/
theorem ctlPhys_mode_cases (c : CtlPhys) :
    c.mode = PalPeg.GalilScaffoldController.Mode.init
      ∨ c.mode = PalPeg.GalilScaffoldController.Mode.scan
      ∨ c.mode = PalPeg.GalilScaffoldController.Mode.shift
      ∨ c.mode = PalPeg.GalilScaffoldController.Mode.copy
      ∨ c.mode = PalPeg.GalilScaffoldController.Mode.home
      ∨ c.mode = PalPeg.GalilScaffoldController.Mode.fpp
      ∨ c.mode = PalPeg.GalilScaffoldController.Mode.markEnd
      ∨ c.mode = PalPeg.GalilScaffoldController.Mode.choose
      ∨ c.mode = PalPeg.GalilScaffoldController.Mode.rewind
      ∨ c.mode = PalPeg.GalilScaffoldController.Mode.replayStart := by
  cases h : c.mode <;> simp [h]

/-- **and the five that are carried, as one hypothesis to discharge.**  Given a state whose mode
is one of these five, the still rows of the command table apply and the branch theorems are in
hand; the other five — the scan, the shift, the start, the replay's start and the half of the
choice that starts a chain — are what remains of a tick's obligation. -/
def StillMode (c : CtlPhys) : Prop :=
  c.mode = PalPeg.GalilScaffoldController.Mode.markEnd
    ∨ c.mode = PalPeg.GalilScaffoldController.Mode.home
    ∨ c.mode = PalPeg.GalilScaffoldController.Mode.choose
    ∨ c.mode = PalPeg.GalilScaffoldController.Mode.fpp
    ∨ c.mode = PalPeg.GalilScaffoldController.Mode.copy

theorem not_stillMode_cases {c : CtlPhys} (h : ¬ StillMode c) :
    c.mode = PalPeg.GalilScaffoldController.Mode.init
      ∨ c.mode = PalPeg.GalilScaffoldController.Mode.scan
      ∨ c.mode = PalPeg.GalilScaffoldController.Mode.shift
      ∨ c.mode = PalPeg.GalilScaffoldController.Mode.rewind
      ∨ c.mode = PalPeg.GalilScaffoldController.Mode.replayStart := by
  unfold StillMode at h
  rcases ctlPhys_mode_cases c with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    simp [hm] at h ⊢

/-- **the bit for the first letter, after a head steps left, is a reading of the window.**  The
head stands on the first letter afterwards exactly when three things hold: it stood on a gap,
which is a bit the control carries; the symbol under its back head is a letter rather than the
sentinel, so there is a letter to step back onto; and the cell below its back head is the
sentinel, so that letter is the first one.  All three are in hand where the rule stands. -/
theorem leftFirst_after_step_iff {margin K : ℕ} {polarity : Fin 16 → Bool} {gap : Fin 4 → Bool}
    {micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl} {fppLive dpLive : Bool}
    {x : State GalilVM} {tapes : Slot → STape Γm}
    (henc : EncTapes margin x polarity gap micro fppLive dpLive tapes) (hK1 : 1 ≤ K)
    (hK : K ≤ margin)
    (v : Fin 4) (head : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hhead : headOf x v = some head) :
    PalPeg.GalilScaffoldChainInputSupply.position
        (PalPeg.GalilScaffoldInputHead.left head) = 1
      ↔ (gap v = true ∧
          centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf tapes tape))
              (headSlot v PalPeg.ConcreteLocalMachine.backTape)
            ≠ encCell (PalPeg.CloseoutCoreEnc.cellSym none) ∧
          belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf tapes tape))
              (headSlot v PalPeg.ConcreteLocalMachine.backTape)
            = encCell (PalPeg.CloseoutCoreEnc.cellSym none)) := by
  obtain ⟨view, viewTapes, habs, hrep, hslots, hcells, hwf⟩ := henc.heads v head hhead
  have hviewBack : view.back = head.head.left := by
    have hb : (PalPeg.LocalArrival.absHead' view []).head.left = head.head.left := by rw [habs]
    exact hb
  have hgapBit : gap v = head.gap := by
    have hg : (PalPeg.LocalArrival.absHead' view []).gap = head.gap := by rw [habs]
    rw [hrep.gap]
    exact hg
  obtain ⟨bottom, hbottomHeight, hstack⟩ := hrep.back
  have hmarginStack : K ≤ (PalPeg.ConcreteLocalMachine.backStack view ++ bottom).length := by
    have hlen : (PalPeg.ConcreteLocalMachine.backStack view ++ bottom).length
        = view.back.length + 1 + bottom.length := by
      show (view.focus :: view.back ++ bottom).length = _
      simp only [List.length_append, List.length_cons]
    omega
  have hcentre : centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf tapes tape))
      (headSlot v PalPeg.ConcreteLocalMachine.backTape)
      = encCell (PalPeg.CloseoutCoreEnc.cellSym view.focus) := by
    rw [centreRead_backSlot v viewTapes (PalPeg.ConcreteLocalMachine.backStack view ++ bottom)
      (hslots PalPeg.ConcreteLocalMachine.backTape) hstack hmarginStack]
    rfl
  have hsentinel : ∀ cell : Option (Fin 2),
      (encCell (PalPeg.CloseoutCoreEnc.cellSym cell)
        = encCell (PalPeg.CloseoutCoreEnc.cellSym none)) ↔ cell = none := by
    intro cell
    cases cell with
    | none => simp
    | some b =>
      simp only [iff_false, reduceCtorEq, iff_false]
      show ¬ (encCell (PalPeg.CloseoutCoreEnc.cellSym (some b)) = blankM)
      have hne : PalPeg.CloseoutCoreEnc.cellSym (some b) ≠ PalPeg.CloseoutCoreStep.blankc := by
        simp [PalPeg.CloseoutCoreEnc.cellSym, PalPeg.CloseoutCoreStep.blankc,
          PalPeg.GalilVMEncode.blank, PalPeg.GalilVMEncode.sOpt]
      simp [encCell, hne, blankM]
  rw [leftFirst_after_left head, hcentre, hgapBit, ← hviewBack]
  cases hback : view.back with
  | nil =>
    have hfocus : view.focus = none :=
      (PalPeg.LocalViewCells.back_nil_iff_focus_none hcells).mp hback
    rw [hfocus]
    simp
  | cons a tail =>
    have hfocus : view.focus ≠ none := by
      intro hnone
      rw [(PalPeg.LocalViewCells.back_nil_iff_focus_none hcells).mpr hnone] at hback
      simp at hback
    have hbelow : belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf tapes tape))
        (headSlot v PalPeg.ConcreteLocalMachine.backTape)
        = encCell (PalPeg.CloseoutCoreEnc.cellSym a) := by
      rw [belowRead_backSlot hK1 v viewTapes
        (PalPeg.ConcreteLocalMachine.backStack view ++ bottom)
        (hslots PalPeg.ConcreteLocalMachine.backTape) hstack hmarginStack]
      congr 1
      show PalPeg.CloseoutCoreEnc18.topSym (view.back ++ bottom) = _
      rw [hback]
      rfl
    have hsplit := back_singleton_iff_sentinel view hcells a tail hback
    rw [hbelow]
    constructor
    · rintro ⟨hg, hlen⟩
      refine ⟨hg, ?_, ?_⟩
      · intro hEq
        exact hfocus ((hsentinel view.focus).mp hEq)
      · rw [hsentinel a]
        exact hsplit.mp (by simpa using hlen)
    · rintro ⟨hg, -, ha⟩
      refine ⟨hg, ?_⟩
      rw [hsplit.mpr ((hsentinel a).mp ha)]
      simp

/-- **one step of the rewind, rule and encoding together.**  The marks tape steps left, the
length counter counts the step, and the left head takes whichever of its three steps its own bit
and one reading of its window say.  Nothing here is asked of the abstraction. -/
theorem rewind_one_of_rule {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (R : PalPeg.CloseoutCoreEnc12.ActRule (Fin 2) (QPhys fppBound dpBound) Γm tapeCountM K)
    (hnq : R.nq q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) = rewindOneNext q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)))
    (hacts : R.acts q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) = withErase q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) (rewindOneActs q.fppLive q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))))
    (hK1 : 1 ≤ K) (hK : K ≤ margin) (hmargin2 : 2 ≤ margin)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind)
    (hnotFirst : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).atFirst x.vm
      = false)
    (hpair : x.ctl.pair = false)
    (hfloor : (x.vm.fpp.program.config.tapes 8).left ≠ [])
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2
          (slotIndex i)) := by
  have hq : (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).1
      = rewindOneNext q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) := by
    show R.nq q none _ = _
    rw [hnq]
  have hstep := idealStep_withErase R q T q.fppLive _ hacts
  obtain ⟨segments, habsLen, hslotLen⟩ := henc.2.counters 3 x.vm.length rfl
  obtain ⟨segments', habsInc, hcountTape⟩ :=
    counter_inc_at (margin := margin) q.polarity 3
      (incSign q.polarity 3 (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)))
      segments x.vm.length habsLen
      (incSign_eq hK1 (by omega) q.polarity 3 T segments hslotLen)
      (T (counterSlot 3)) hslotLen
  have hheads := headSlots_step henc.2 hK 0 x.vm.left rfl
    (fun slot => (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2 (slotIndex slot))
    (fun t => by
      rw [hstep (headSlot 0 t) (fun k => (progSlot_ne_headSlot (!q.fppLive) k 0 t).symm),
        rewindOneActs_head]
      rfl)
  obtain ⟨view, viewTapes, habsView, hrepView, hslotsView, hcellsView⟩ := hheads
  rw [hq]
  refine rewind_one margin centre place entry entryQ first w F delay x q T
    (fun slot => (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2 (slotIndex slot))
    (Function.update q.polarity 3 (incSign q.polarity 3 (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))))
    (Function.update q.gap 0 (!q.gap 0)) _ hmode hnotFirst hpair ?_ henc
    ⟨view, viewTapes, habsView, by rwa [Function.update_self], hslotsView, hcellsView⟩
    (fun v hv => Function.update_of_ne hv _ _) (fun c hc => Function.update_of_ne hc _ _)
    segments' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Bool.eq_iff_iff, decide_eq_true_eq,
      leftFirst_after_step_iff henc.2 hK1 hK 0 x.vm.left rfl]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact and_assoc
  · rw [Function.update_self]
    exact habsInc
  · rw [hstep (counterSlot 3) (fun k => (progSlot_ne_counterSlot (!q.fppLive) k 3).symm),
      rewindOneActs_counter]
    exact hcountTape
  · intro m hsrc
    obtain ⟨segMir, habsMir, hslotMir⟩ :=
      henc.2.mirrors m x.vm.length (by rw [hsrc]; rfl)
    have habsMir3 : absCtr segMir (q.polarity 3) = x.vm.length := by
      rw [← hsrc]; exact habsMir
    obtain ⟨segMir', habsMirInc, hmirTape⟩ :=
      counter_inc_at (margin := margin) q.polarity 3
        (incSign q.polarity 3 (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)))
        segMir x.vm.length habsMir3
        (by
          rw [incSign_eq hK1 (by omega) q.polarity 3 T segments hslotLen]
          congr 1
          rw [← PalPeg.LocalCounter.zero_iff segments (q.polarity 3),
            ← PalPeg.LocalCounter.zero_iff segMir (q.polarity 3), habsLen, habsMir3])
        (T (mirrorSlot m)) hslotMir
    refine ⟨segMir', ?_, ?_⟩
    · rw [Function.update_self]
      exact habsMirInc
    · rw [hstep (mirrorSlot m) (fun k => (progSlot_ne_mirrorSlot (!q.fppLive) k m).symm),
        rewindOneActs_mirror _ _ _ m hsrc]
      exact hmirTape
  · refine progSlot_after_moveLeft (newTapes := fun slot =>
      (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2 (slotIndex slot))
      henc.2 hK 8 hfloor ?_
    rw [hstep _ (fun k => progSlotOf_ne_flip q.fppLive 8 k), rewindOneActs_prog]
  · intro j hj
    rw [hstep _ (fun k => progSlotOf_ne_flip q.fppLive j k), rewindOneActs_progOther _ _ _ j hj]
    rfl
  · intro slot hprog hcounter hmirror hhead hidle
    rw [hstep slot hidle, rewindOneActs_off q.fppLive q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) slot hprog hcounter hmirror hhead]
    rfl
  · intro i
    rw [hslotsView i, pos_mapTape]
    exact hrepView.margin_le_pos (by omega) (le_refl margin) i
  · exact fun k => idle_shape_after_erase margin hK1 (by omega) R q T q.fppLive _ hacts
      (fun k => rewindOneActs_off q.fppLive q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) (progSlotOf (!q.fppLive) k)
        (fun j => (progSlotOf_ne_flip q.fppLive j k).symm)
        (progSlot_ne_counterSlot (!q.fppLive) k 3)
        (fun m _ => progSlot_ne_mirrorSlot (!q.fppLive) k m)
        (fun t => progSlot_ne_headSlot (!q.fppLive) k 0 t))
      henc.2.idleShape k

/-- **the paired step of the rewind, rule and encoding together.**  Both heads step, both
counters count, and the radius's three mirrors are written with the counter's own sign bit —
which is the right bit for them because they stand for the same value. -/
theorem rewind_pair_of_rule {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (R : PalPeg.CloseoutCoreEnc12.ActRule (Fin 2) (QPhys fppBound dpBound) Γm tapeCountM K)
    (hnq : R.nq q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) = rewindPairNext q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)))
    (hacts : R.acts q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) = withErase q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) (rewindPairActs q.fppLive q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))))
    (hK1 : 1 ≤ K) (hK : K ≤ margin) (hmargin2 : 2 ≤ margin)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind)
    (hnotFirst : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).atFirst x.vm
      = false)
    (hpair : x.ctl.pair = true)
    (hfloor : (x.vm.fpp.program.config.tapes 8).left ≠ [])
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2
          (slotIndex i)) := by
  have hq : (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).1
      = rewindPairNext q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) := by
    show R.nq q none _ = _
    rw [hnq]
  have hstep := idealStep_withErase R q T q.fppLive _ hacts
  obtain ⟨segLenOld, habsLen, hslotLen⟩ := henc.2.counters 3 x.vm.length rfl
  obtain ⟨segLen, habsIncLen, hcountLenTape⟩ :=
    counter_inc_at (margin := margin) q.polarity 3 (incSign q.polarity 3 (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))) segLenOld
      x.vm.length habsLen (incSign_eq hK1 (by omega) q.polarity 3 T segLenOld hslotLen)
      (T (counterSlot 3)) hslotLen
  obtain ⟨segRadOld, habsRad, hslotRad⟩ := henc.2.counters 2 x.vm.radius rfl
  have hbitRad : incSign q.polarity 2 (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = (q.polarity 2 || decide (PalPeg.LocalCounter.val segRadOld = 0)) :=
    incSign_eq hK1 (by omega) q.polarity 2 T segRadOld hslotRad
  obtain ⟨segRad, habsIncRad, hcountRadTape⟩ :=
    counter_inc_at (margin := margin) q.polarity 2 (incSign q.polarity 2 (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))) segRadOld
      x.vm.radius habsRad hbitRad (T (counterSlot 2)) hslotRad
  obtain ⟨viewL, viewTapesL, habsL, hrepL, hslotsL, hcellsL, hwfL⟩ :=
    headSlots_step henc.2 hK 0 x.vm.left rfl (fun slot => (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2 (slotIndex slot))
      (fun t => by
        rw [hstep (headSlot 0 t) (fun k => (progSlot_ne_headSlot (!q.fppLive) k 0 t).symm),
          rewindPairActs_head q.fppLive q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) 0 (Or.inl rfl) t]
        rfl)
  obtain ⟨viewC, viewTapesC, habsC, hrepC, hslotsC, hcellsC, hwfC⟩ :=
    headSlots_step henc.2 hK 1 x.vm.center rfl (fun slot => (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2 (slotIndex slot))
      (fun t => by
        rw [hstep (headSlot 1 t) (fun k => (progSlot_ne_headSlot (!q.fppLive) k 1 t).symm),
          rewindPairActs_head q.fppLive q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) 1 (Or.inr rfl) t]
        rfl)
  rw [hq]
  refine rewind_pair margin centre place entry entryQ first w F delay x q T (fun slot => (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2 (slotIndex slot))
    (Function.update (Function.update q.polarity 3 (incSign q.polarity 3 (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)))) 2
      (incSign q.polarity 2 (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))))
    (Function.update (Function.update q.gap 0 (!q.gap 0)) 1 (!q.gap 1)) _ hmode hnotFirst hpair
    ?_ henc viewL viewTapesL habsL ?_ hslotsL hcellsL hwfL viewC viewTapesC habsC ?_ hslotsC
    hcellsC hwfC
    ?_ ?_ segLen ?_ ?_ ?_ segRad ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Bool.eq_iff_iff, decide_eq_true_eq,
      leftFirst_after_step_iff henc.2 hK1 hK 0 x.vm.left rfl]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact and_assoc
  · rw [Function.update_of_ne (by decide), Function.update_self]
    exact hrepL
  · rw [Function.update_self]
    exact hrepC
  · intro v hv0 hv1
    rw [Function.update_of_ne hv1, Function.update_of_ne hv0]
  · intro c hc3 hc2
    rw [Function.update_of_ne hc2, Function.update_of_ne hc3]
  · rw [Function.update_of_ne (by decide), Function.update_self]
    exact habsIncLen
  · rw [hstep (counterSlot 3) (fun k => (progSlot_ne_counterSlot (!q.fppLive) k 3).symm),
      rewindPairActs_counterLen]
    exact hcountLenTape
  · intro m hsrc
    obtain ⟨segM, habsM, hslotM⟩ := henc.2.mirrors m x.vm.length (by rw [hsrc]; rfl)
    rw [hsrc] at habsM
    have hvalM : PalPeg.LocalCounter.val segM = PalPeg.LocalCounter.val segLenOld :=
      val_eq_of_absCtr_eq (habsM.trans habsLen.symm)
    obtain ⟨segM', habsM', htapeM'⟩ :=
      counter_inc_at (margin := margin) q.polarity 3
        (incSign q.polarity 3 (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))) segM
        x.vm.length habsM
        (by
          rw [incSign_eq hK1 (by omega) q.polarity 3 T segLenOld hslotLen, hvalM])
        (T (mirrorSlot m)) hslotM
    refine ⟨segM', by rw [Function.update_of_ne (by decide), Function.update_self]; exact habsM', ?_⟩
    rw [hstep (mirrorSlot m) (fun k => (progSlot_ne_mirrorSlot (!q.fppLive) k m).symm),
      rewindPairActs_mirrorLen _ _ _ m hsrc]
    exact htapeM'
  · rw [Function.update_self]
    exact habsIncRad
  · rw [hstep (counterSlot 2) (fun k => (progSlot_ne_counterSlot (!q.fppLive) k 2).symm),
      rewindPairActs_counterRad]
    exact hcountRadTape
  · intro m hsrc
    obtain ⟨segM, habsM, hslotM⟩ := henc.2.mirrors m x.vm.radius (by rw [hsrc]; rfl)
    rw [hsrc] at habsM
    have hvalM : PalPeg.LocalCounter.val segM = PalPeg.LocalCounter.val segRadOld :=
      val_eq_of_absCtr_eq (habsM.trans habsRad.symm)
    obtain ⟨segM', habsM', htapeM'⟩ :=
      counter_inc_at (margin := margin) q.polarity 2 (incSign q.polarity 2 (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))) segM
        x.vm.radius habsM (by rw [hbitRad, hvalM]) (T (mirrorSlot m)) hslotM
    refine ⟨segM', by rw [Function.update_self]; exact habsM', ?_⟩
    rw [hstep (mirrorSlot m) (fun k => (progSlot_ne_mirrorSlot (!q.fppLive) k m).symm),
      rewindPairActs_mirror q.fppLive q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) m hsrc]
    exact htapeM'
  · refine progSlot_after_moveLeft (newTapes := (fun slot => (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2 (slotIndex slot))) henc.2 hK 8 hfloor ?_
    rw [hstep _ (fun k => progSlotOf_ne_flip q.fppLive 8 k), rewindPairActs_prog]
  · intro j hj
    rw [hstep _ (fun k => progSlotOf_ne_flip q.fppLive j k),
      rewindPairActs_progOther q.fppLive q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) j hj]
    rfl
  · intro slot hprog hlen hrad hmirror hmirrorLen hhead0 hhead1 hidle
    rw [hstep slot hidle,
      rewindPairActs_off q.fppLive q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) slot hprog hlen hrad hmirrorLen hmirror hhead0 hhead1]
    rfl
  · intro i
    rw [hslotsL i, pos_mapTape]
    exact hrepL.margin_le_pos (by omega) (le_refl margin) i
  · intro i
    rw [hslotsC i, pos_mapTape]
    exact hrepC.margin_le_pos (by omega) (le_refl margin) i
  · exact fun k => idle_shape_after_erase margin hK1 (by omega) R q T q.fppLive _ hacts
      (fun k => rewindPairActs_off q.fppLive q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) (progSlotOf (!q.fppLive) k)
        (fun j => (progSlotOf_ne_flip q.fppLive j k).symm)
        (progSlot_ne_counterSlot (!q.fppLive) k 3)
        (progSlot_ne_counterSlot (!q.fppLive) k 2)
        (fun m _ => progSlot_ne_mirrorSlot (!q.fppLive) k m)
        (fun m _ => progSlot_ne_mirrorSlot (!q.fppLive) k m)
        (fun t => progSlot_ne_headSlot (!q.fppLive) k 0 t)
        (fun t => progSlot_ne_headSlot (!q.fppLive) k 1 t))
      henc.2.idleShape k

/-- **the reconstructed tape is the component's tape, shifted.**  Cell `j` of the one is cell
`pos - K + j` of the other, so long as the component's head stands at least `K` cells from its own
left end — below that the window shows the padding instead, which is what the floor sentinel is
for. -/
theorem rd_winTape_of_padded {K margin : ℕ} (t : PalPeg.GalilScaffoldTape.Tape)
    (hK : K ≤ PalPeg.Local.pos (encTape t)) (j : Fin (2 * K + 1)) :
    PalPeg.Local.rd (6 : Fin 9)
        (encTape (winTape (PalPeg.Local.readWin blankM K
          (padLeft margin (mapTape encProg (encTape t)))))) j.val
      = PalPeg.Local.rd (6 : Fin 9) (encTape t)
          (PalPeg.Local.pos (encTape t) - K + j.val) := by
  rw [rd_winTape, PalPeg.Local.readWin_eq, pos_padLeft, pos_mapTape,
    rd_padded margin t (PalPeg.Local.pos (encTape t) + margin + 1 - K + j.val) (by omega),
    decProg_encProg]
  congr 1
  omega

/-- **the finite control of a call is decided by what the machine can see, too.**  Two machines
agreeing on the halting bit, the program counter and the symbols under the heads leave the call
with the same halting bit and the same program counter — the only thing an instruction consults
beyond those is the symbol it reads. -/
theorem tickFun_control_congr (code : List (Instruction 9))
    (m m' : PalPeg.GalilScaffoldControl.Machine 9)
    (hdone : m.done = m'.done) (hpc : m.config.pc = m'.config.pc)
    (hfocus : ∀ t : Fin 9, (m.config.tapes t).focus = (m'.config.tapes t).focus) :
    (PalPeg.ProgramFunction.tickFun code true m).config.pc
        = (PalPeg.ProgramFunction.tickFun code true m').config.pc
      ∧ (PalPeg.ProgramFunction.tickFun code true m).done
        = (PalPeg.ProgramFunction.tickFun code true m').done := by
  unfold PalPeg.ProgramFunction.tickFun
  rw [hdone, hpc]
  cases hd : m'.done
  · rw [if_neg (by simp [hd]), if_neg (by simp [hd])]
    match hcode : code[m'.config.pc]? with
    | none => exact ⟨hpc, hdone⟩
    | some .halt => exact ⟨hpc, rfl⟩
    | some (.read t cs) =>
        simp only [hcode]
        show (PalPeg.ProgramFunction.executeFun (.read t cs) m.config).pc
          = (PalPeg.ProgramFunction.executeFun (.read t cs) m'.config).pc ∧ _
        unfold PalPeg.ProgramFunction.executeFun
        simp only [hfocus t]
        cases hfind : (cs.find? (fun choice => choice.1 = (m'.config.tapes t).focus)) with
        | none => simp [hfind]; exact hpc
        | some choice => simp [hfind]
    | some (.write t sym pc) => simp only [hcode]; exact ⟨rfl, by first | rfl | trivial⟩
    | some (.move t dir pc) =>
        cases dir <;> (simp only [hcode]; exact ⟨rfl, by first | rfl | trivial⟩)
  · rw [if_pos (by simp [hd]), if_pos (by simp [hd])]
    exact ⟨hpc, hdone⟩

/-! ### the branch that runs the preparation program

The rule does not need to shrink its windows as the quantum proceeds: `winMachine` hands it whole
tapes, and the quantum runs on those.  What it names for a slot is what that run performs there. -/

/-- **the actions the `fpp` branch names.**  On each tape of the live half, the actions the
quantum performs there; on every other slot, none. -/
noncomputable def fppActs {K : ℕ} (code : List (Instruction 9)) (quantum : ℕ) (live : Bool)
    (pc : ℕ) (done : Bool) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) :
    Fin tapeCountM → List (PalPeg.CloseoutCoreEnc12.Act Γm) :=
  fun j =>
    match slotIndex.symm j with
    | .inr (.inl i) =>
        if live then [] else progRunActs code quantum (winMachine pc done ws live) i
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))) =>
        if live then progRunActs code quantum (winMachine pc done ws live) i else []
    | _ => []

theorem fppActs_length {K : ℕ} (code : List (Instruction 9)) (quantum : ℕ) (live : Bool)
    (pc : ℕ) (done : Bool) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (j : Fin tapeCountM) : (fppActs code quantum live pc done ws j).length ≤ quantum := by
  unfold fppActs
  split
  · split
    · simp
    · exact progRunActs_length code quantum _ _
  · split
    · exact progRunActs_length code quantum _ _
    · simp
  · simp

/-- **the branch names nothing outside the live half's program slots.**  This is what lets the
erasure own every other slot, and it is the side condition the ideal step asks for. -/
theorem fppActs_off_live {K : ℕ} (code : List (Instruction 9)) (quantum : ℕ) (live : Bool)
    (pc : ℕ) (done : Bool) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (slot : Slot) (hslot : ∀ j : Fin 9, slot ≠ progSlotOf live j) :
    fppActs code quantum live pc done ws (slotIndex slot) = [] := by
  unfold fppActs
  rw [Equiv.symm_apply_apply]
  cases live
  · match slot, hslot with
    | .inr (.inl i), hslot => exact absurd (progSlotOf_false i).symm (hslot i)
    | .inl _, _ => rfl
    | .inr (.inr (.inl _)), _ => rfl
    | .inr (.inr (.inr (.inl _))), _ => rfl
    | .inr (.inr (.inr (.inr (.inl _)))), _ => rfl
    | .inr (.inr (.inr (.inr (.inr (.inl _))))), _ => rfl
    | .inr (.inr (.inr (.inr (.inr (.inr (.inl _)))))), _ => rfl
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl _))))))), _ => rfl
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl _)))))))), _ => rfl
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr _)))))))), _ => rfl
  · match slot, hslot with
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))), hslot =>
        exact absurd (progSlotOf_true i).symm (hslot i)
    | .inl _, _ => rfl
    | .inr (.inl _), _ => rfl
    | .inr (.inr (.inl _)), _ => rfl
    | .inr (.inr (.inr (.inl _))), _ => rfl
    | .inr (.inr (.inr (.inr (.inl _)))), _ => rfl
    | .inr (.inr (.inr (.inr (.inr (.inl _))))), _ => rfl
    | .inr (.inr (.inr (.inr (.inr (.inr (.inl _)))))), _ => rfl
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl _))))))), _ => rfl
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr _)))))))), _ => rfl

/-- **and on the live half it is exactly the quantum's own actions.** -/
theorem fppActs_at_live {K : ℕ} (code : List (Instruction 9)) (quantum : ℕ) (live : Bool)
    (pc : ℕ) (done : Bool) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (i : Fin 9) :
    fppActs code quantum live pc done ws (slotIndex (progSlotOf live i))
      = progRunActs code quantum (winMachine pc done ws live) i := by
  unfold fppActs
  cases live
  · rw [progSlotOf_false, Equiv.symm_apply_apply]
    rfl
  · rw [progSlotOf_true, Equiv.symm_apply_apply]
    rfl

/-! ### the rule itself

The tables above are assembled into one `ActRule` by dispatching on the controller's mode.  The
modes not yet given a table stand still; each one is replaced as its branch is proved, and the
branch lemmas then apply to this rule with their `hnq` and `hacts` discharged by a mode lemma
instead of assumed. -/

theorem markEndActs_length {K : ℕ} (live : Bool) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (j : Fin tapeCountM) : (markEndActs live ws j).length ≤ 1 := by
  unfold markEndActs
  split
  · split
    · exact actsAt_length _ _ (by simp) j
    · exact actsAt_length _ _ (by simp) j
  · exact actsAt_length _ _ (by simp) j

theorem homeActs_length {K : ℕ} (live : Bool) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (j : Fin tapeCountM) : (homeActs live ws j).length ≤ 1 := by
  unfold homeActs
  split
  · exact actsAt_length _ _ (by simp) j
  · split
    · exact actsAt_length _ _ (by simp) j
    · exact actsAt_length _ _ (by simp) j

theorem chooseBackActs_length {K : ℕ} (live : Bool) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (j : Fin tapeCountM) : (chooseBackActs live ws j).length ≤ 1 := by
  unfold chooseBackActs
  split
  · exact actsAt_length _ _ (by simp) j
  · exact actsAt_length _ _ (by simp) j

/-- the program counter the finite control carries, as a number. -/
def pcOf {fppBound dpBound : ℕ} (q : QPhys fppBound dpBound) : ℕ :=
  match q.fppPc with
  | some k => k.val
  | none => 0

/-- **the counter the finite state holds is the program's own, while it fits.**  `EncPc` reads a
missing counter as "past the bound", so this is the whole of what the bound buys: inside it the
state knows the counter exactly, and `pcOf` reads it back. -/
theorem pcOf_of_enc {fppBound dpBound : ℕ} {w : List (Fin 2)} {x : State GalilVM} {q : QPhys fppBound dpBound}
    (henc : EncControl w x q) (hin : x.vm.fpp.program.config.pc < fppBound) :
    x.vm.fpp.program.config.pc = pcOf q := by
  have hpc := henc.fppPc
  unfold pcOf
  cases hq : q.fppPc with
  | none =>
    rw [hq] at hpc
    have hge : fppBound ≤ x.vm.fpp.program.config.pc := hpc
    omega
  | some k =>
    rw [hq] at hpc
    exact hpc.symm

/-- the program counter as the finite control can hold it: the number itself while it fits in the
bound, and otherwise the mark that says it does not.  `EncPc` accepts both readings, so this is a
total inverse of `pcOf` as far as the encoding is concerned. -/
def pcPhysOf (bound : ℕ) (pc : ℕ) : PcPhys bound :=
  if h : pc < bound then some ⟨pc, h⟩ else none

@[simp] theorem encPc_pcPhysOf (bound : ℕ) (pc : ℕ) : EncPc (pcPhysOf bound pc) pc := by
  unfold pcPhysOf
  by_cases h : pc < bound
  · rw [dif_pos h]
    rfl
  · rw [dif_neg h]
    exact Nat.le_of_not_lt h

/-- **the machine a quantum leaves behind, as the rule computes it.**  The rule never sees the
tapes; it sees the windows, and `winMachine` is the machine those windows stand for. -/
noncomputable def winRun {K : ℕ} (code : List (Instruction 9)) (quantum : ℕ) (live : Bool)
    (pc : ℕ) (done : Bool) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) :
    PalPeg.GalilScaffoldControl.Machine 9 :=
  PalPeg.ProgramFunction.runFun code (List.replicate quantum true) (winMachine pc done ws live)

/-- **the control after a quantum of the preparation program.**  The program counter and the
halting bit are the run's own; a run that halts hands the machine to the mark walk, which is what
the tick does in its `doneVm` branch. -/
noncomputable def fppNext {fppBound dpBound K : ℕ} (quantum : ℕ) (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) : QPhys fppBound dpBound :=
  if (winRun PalPeg.GalilFppMarkedCode.code quantum q.fppLive (pcOf q) q.fppDone ws).done then
    {q with ctl := {q.ctl with mode := PalPeg.GalilScaffoldController.Mode.markEnd}, fppPc := pcPhysOf fppBound (winRun PalPeg.GalilFppMarkedCode.code quantum q.fppLive (pcOf q) q.fppDone ws).config.pc, fppDone := true}
  else
    {q with fppPc := pcPhysOf fppBound (winRun PalPeg.GalilFppMarkedCode.code quantum q.fppLive (pcOf q) q.fppDone ws).config.pc, fppDone := false}

/-- the control of the wipe: the live bit flips, the program counter goes home and the halting
flag is set.  The test is the marks tape's own symbol. -/
noncomputable def rewindNext {fppBound dpBound K : ℕ} (first : Fin 9) (hbound : 320 < fppBound)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) :
    QPhys fppBound dpBound :=
  if centreRead ws (progSlot q.fppLive 8) = encProg first then
    {q with ctl := {q.ctl with mode := PalPeg.GalilScaffoldController.Mode.replayStart}, fppPc := some ⟨320, hbound⟩, fppDone := true, fppLive := !q.fppLive}
  else if q.ctl.pair then rewindPairNext q ws
  else rewindOneNext q ws

/-- **the action table of the rewind.**  The tick that finds the first letter names no action at
all — the nine tapes the abstraction blanks are the nine the machine stops looking at — and the
other two ticks are the single and the paired step. -/
noncomputable def rewindActs {fppBound dpBound K : ℕ} (first : Fin 9) (live : Bool)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) :
    Fin tapeCountM → List (PalPeg.CloseoutCoreEnc12.Act Γm) :=
  if centreRead ws (progSlot live 8) = encProg first then fun _ => []
  else if q.ctl.pair then rewindPairActs live q ws
  else rewindOneActs live q ws

theorem rewindActs_length {fppBound dpBound K : ℕ} (first : Fin 9) (live : Bool)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (j : Fin tapeCountM) : (rewindActs first live q ws j).length ≤ 2 := by
  unfold rewindActs
  split_ifs
  · simp
  · exact rewindPairActs_length live q ws j
  · exact rewindOneActs_length live q ws j

theorem rewindActs_atFirst {fppBound dpBound K : ℕ} (first : Fin 9) (live : Bool)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hatMark : centreRead ws (progSlot live 8) = encProg first) (j : Fin tapeCountM) :
    rewindActs first live q ws j = [] := by
  unfold rewindActs
  rw [if_pos hatMark]

/-- the letter a cursor shows, as the rule decodes the centre of its window. -/
noncomputable def placeLetter (c : Γm) : Fin 3 :=
  if c = encCell (PalPeg.CloseoutCoreEnc.cellSym (some 0)) then 0 else 1

theorem placeLetter_encCell (a : Fin 2) :
    placeLetter (encCell (PalPeg.CloseoutCoreEnc.cellSym (some a)))
      = PalPeg.GalilScaffoldPlace.letter a := by
  revert a
  decide

/-- **the symbol the fallback copy writes.**  A cursor standing on the gap beside a letter
copies the gap symbol; one standing on a letter copies that letter.  The first is the cursor's
own bit of the finite control, the second the centre of its window. -/
noncomputable def copySymbol {K : ℕ} (gapBit : Bool)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) : Fin 3 :=
  if gapBit then 2 else placeLetter (centreRead ws (placeSlot 1))

/-- **the control table of the fallback copy.**  A tick that still has work flips the cursor's
half-step bit and moves the sign of the work counter if the decrement crossed zero; a tick that
has none hands the machine to the walk home, recording whether the cursor ran out. -/
noncomputable def copyNext {fppBound dpBound K : ℕ} (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) : QPhys fppBound dpBound :=
  if remainsTest q.polarity ws then
    (if centreRead ws (placeSlot 1) = blankM then q
      else {q with placeGap := Function.update q.placeGap 1 (!q.placeGap 1), polarity := Function.update q.polarity 9 (workPositive q.polarity ws)})
  else {q with ctl := {q.ctl with mode := PalPeg.GalilScaffoldController.Mode.home}, fppMode := PalPeg.GalilScaffoldChainInputSupply.FppControl.Mode.home, fppFinalStage := decide (centreRead ws (placeSlot 1) = blankM)}

/-- **the action table of the fallback copy.**  A tick that still has work writes one symbol on
the program's copy tape and steps right, decrements the work counter, and pops the cursor unless
it was standing on a gap; a tick that has none writes the end mark where it stands. -/
noncomputable def copyActs {fppBound dpBound K : ℕ} (live : Bool) (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) :
    Fin tapeCountM → List (PalPeg.CloseoutCoreEnc12.Act Γm) :=
  if remainsTest q.polarity ws then
    (if centreRead ws (placeSlot 1) = blankM then fun _ => []
      else fun j =>
        if j = slotIndex (progSlot live 7) then
          [some (encProg (PalPeg.GalilFppPreparation.symbol (copySymbol (q.placeGap 1) ws)),
            (.right : PalPeg.CloseoutCoreEnc12.MoveC))]
        else if j = slotIndex (counterSlot 9) then
          [if workPositive q.polarity ws then
              some (blankM, (.left : PalPeg.CloseoutCoreEnc12.MoveC))
            else some (encSeg PalPeg.LocalCounter.mark, (.right : PalPeg.CloseoutCoreEnc12.MoveC))]
        else if j = slotIndex (placeSlot 1) then
          (if q.placeGap 1 then []
            else [some (centreRead ws (placeSlot 1), (.left : PalPeg.CloseoutCoreEnc12.MoveC))])
        else [])
  else
    actsAt (slotIndex (progSlot live 7))
      [some (encProg 5, (.stay : PalPeg.CloseoutCoreEnc12.MoveC))]

theorem copyActs_length {fppBound dpBound K : ℕ} (live : Bool) (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (j : Fin tapeCountM) :
    (copyActs live q ws j).length ≤ 1 := by
  unfold copyActs actsAt
  split_ifs <;> (try dsimp only) <;> (try split_ifs) <;> simp

/-- the control of the machine, mode by mode. -/
noncomputable def ruleNext {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9) (hbound : 320 < fppBound)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) :
    QPhys fppBound dpBound :=
  match q.ctl.mode with
  | PalPeg.GalilScaffoldController.Mode.markEnd => markEndNext q.fppLive q ws
  | PalPeg.GalilScaffoldController.Mode.home => homeNext q.fppLive hbound q ws
  | PalPeg.GalilScaffoldController.Mode.choose => chooseBackNext q
  | PalPeg.GalilScaffoldController.Mode.rewind => rewindNext first hbound q ws
  | PalPeg.GalilScaffoldController.Mode.fpp => fppNext entryQ q ws
  | PalPeg.GalilScaffoldController.Mode.copy => copyNext q ws
  | PalPeg.GalilScaffoldController.Mode.shift =>
      if remainsTest q.polarity ws then q else shiftExitNext q
  | PalPeg.GalilScaffoldController.Mode.scan =>
      if chainConsumesTest q ws then scanConsumeNext q ws else q
  | _ => q

/-- **the two actions that mark a new block.**  `markNew` steps the marks tape right, writes the
component's own label and steps right again; writing and then stepping is one action, so the whole
of it is two.  The symbol the first action writes back is the one already under the head after the
quantum, which the rule knows through `runFun_focus_of_agree`. -/
noncomputable def markNewActs {K : ℕ} (code : List (Instruction 9)) (quantum : ℕ) (live : Bool)
    (first : Fin 9) (pc : ℕ) (done : Bool)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) :
    List (PalPeg.CloseoutCoreEnc12.Act Γm) :=
  [some (encProg ((winRun code quantum live pc done ws).config.tapes 8).focus,
      (.right : PalPeg.CloseoutCoreEnc12.MoveC)),
    some (encProg first, (.right : PalPeg.CloseoutCoreEnc12.MoveC))]

theorem markNewActs_length {K : ℕ} (code : List (Instruction 9)) (quantum : ℕ) (live : Bool)
    (first : Fin 9) (pc : ℕ) (done : Bool)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) :
    (markNewActs code quantum live first pc done ws).length = 2 := rfl

/-- **the whole action table of the branch that runs the preparation program.**  A quantum that
does not reach the halt performs its own actions and no others; one that does also marks the new
block, on the marks tape of the live half. -/
noncomputable def fppBranchActs {K : ℕ} (code : List (Instruction 9)) (quantum : ℕ) (live : Bool)
    (first : Fin 9) (pc : ℕ) (done : Bool)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) :
    Fin tapeCountM → List (PalPeg.CloseoutCoreEnc12.Act Γm) :=
  if (winRun code quantum live pc done ws).done then
    fun j => fppActs code quantum live pc done ws j
      ++ (if j = slotIndex (progSlotOf live 8)
            then markNewActs code quantum live first pc done ws else [])
  else fppActs code quantum live pc done ws

theorem fppBranchActs_of_running {K : ℕ} (code : List (Instruction 9)) (quantum : ℕ) (live : Bool)
    (first : Fin 9) (pc : ℕ) (done : Bool)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hrun : (winRun code quantum live pc done ws).done = false) :
    fppBranchActs code quantum live first pc done ws = fppActs code quantum live pc done ws := by
  unfold fppBranchActs
  rw [if_neg (by simp [hrun])]

theorem fppBranchActs_length {K : ℕ} (code : List (Instruction 9)) (quantum : ℕ) (live : Bool)
    (first : Fin 9) (pc : ℕ) (done : Bool)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (j : Fin tapeCountM) :
    (fppBranchActs code quantum live first pc done ws j).length ≤ quantum + 2 := by
  unfold fppBranchActs
  split
  · show (fppActs code quantum live pc done ws j ++ _).length ≤ quantum + 2
    rw [List.length_append]
    have hbase := fppActs_length code quantum live pc done ws j
    by_cases hj : j = slotIndex (progSlotOf live 8)
    · rw [if_pos hj, markNewActs_length]
      omega
    · rw [if_neg hj]
      simp only [List.length_nil]
      omega
  · have := fppActs_length code quantum live pc done ws j
    omega

theorem fppBranchActs_off_live {K : ℕ} (code : List (Instruction 9)) (quantum : ℕ) (live : Bool)
    (first : Fin 9) (pc : ℕ) (done : Bool)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (slot : Slot) (hslot : ∀ j : Fin 9, slot ≠ progSlotOf live j) :
    fppBranchActs code quantum live first pc done ws (slotIndex slot) = [] := by
  unfold fppBranchActs
  split
  · show fppActs code quantum live pc done ws (slotIndex slot)
      ++ (if slotIndex slot = slotIndex (progSlotOf live 8)
            then markNewActs code quantum live first pc done ws else []) = []
    rw [fppActs_off_live code quantum live pc done ws slot hslot,
      if_neg (fun h => hslot 8 (slotIndex.injective h))]
    rfl
  · exact fppActs_off_live code quantum live pc done ws slot hslot

/-- the actions of the machine, mode by mode. -/
noncomputable def ruleActs {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9)
    (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) :
    Fin tapeCountM → List (PalPeg.CloseoutCoreEnc12.Act Γm) :=
  match q.ctl.mode with
  | PalPeg.GalilScaffoldController.Mode.markEnd => withErase q.fppLive ws (markEndActs q.fppLive ws)
  | PalPeg.GalilScaffoldController.Mode.home => withErase q.fppLive ws (homeActs q.fppLive ws)
  | PalPeg.GalilScaffoldController.Mode.choose => withErase q.fppLive ws (chooseBackActs q.fppLive ws)
  | PalPeg.GalilScaffoldController.Mode.rewind =>
      withErase q.fppLive ws (rewindActs first q.fppLive q ws)
  | PalPeg.GalilScaffoldController.Mode.fpp =>
      withErase q.fppLive ws
        (fppBranchActs PalPeg.GalilFppMarkedCode.code entryQ q.fppLive first (pcOf q) q.fppDone ws)
  | PalPeg.GalilScaffoldController.Mode.copy =>
      withErase q.fppLive ws (copyActs q.fppLive q ws)
  | PalPeg.GalilScaffoldController.Mode.scan =>
      withErase q.fppLive ws (scanConsumeActs q ws)
  | _ => withErase q.fppLive ws (fun _ => [])

theorem ruleActs_length {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9)
    (hK : entryQ + 3 ≤ K) (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (j : Fin tapeCountM) :
    (ruleActs entryQ first q ws j).length ≤ K := by
  unfold ruleActs
  cases hm : q.ctl.mode
  all_goals
    simp only [hm]
  all_goals
    first
      | exact withErase_length (b := 1) (by omega) q.fppLive ws _
          (fun j => markEndActs_length q.fppLive ws j) j
      | exact withErase_length (b := 1) (by omega) q.fppLive ws _
          (fun j => homeActs_length q.fppLive ws j) j
      | exact withErase_length (b := 1) (by omega) q.fppLive ws _
          (fun j => chooseBackActs_length q.fppLive ws j) j
      | exact withErase_length (b := entryQ + 2) (by omega) q.fppLive ws _
          (fun j => fppBranchActs_length PalPeg.GalilFppMarkedCode.code entryQ q.fppLive first
            (pcOf q) q.fppDone ws j) j
      | exact withErase_length (b := 2) (by omega) q.fppLive ws _
          (fun j => rewindActs_length first q.fppLive q ws j) j
      | exact withErase_length (b := 1) (by omega) q.fppLive ws (fun _ => [])
          (fun j => by simp) j
      | exact withErase_length (b := 1) (by omega) q.fppLive ws _
          (fun j => copyActs_length q.fppLive q ws j) j
      | exact withErase_length (b := 1) (by omega) q.fppLive ws _
          (fun j => scanConsumeActs_length q ws j) j

/-- **the rule of the physical machine**, so far as its branches are proved. -/
noncomputable def physRule {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9) (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K) :
    PalPeg.CloseoutCoreEnc12.ActRule (Fin 2) (QPhys fppBound dpBound) Γm tapeCountM K where
  nq := fun q _ ws => ruleNext entryQ first hbound q ws
  acts := fun q _ ws => ruleActs entryQ first q ws
  len_le := fun q _ ws j => ruleActs_length entryQ first hK q ws j

/-- **the rule of the machine, with every table it dispatches on put in.**  The base is the mode
table that was already proved branch by branch — it names counters, program tapes, period tapes
and the answer — the command table is the one written above, and the division of labour inside a
tick is `tickRule`.  The rows of the command table that are not written yet are the parameter
`rest`, so nothing here claims anything about the modes whose branches are still missing. -/
noncomputable def tickPhysRule {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9)
    (hbound : 320 < fppBound) (hKq : entryQ + 3 ≤ K) (hK : 2 ≤ K)
    (rest : QPhys fppBound dpBound → Option (Fin 2) →
      (Fin tapeCountM → PalPeg.Local.Window Γm K) → Fin 4 →
      PalPeg.ConcreteLocalMachine.ViewCommand) :
    PalPeg.CloseoutCoreEnc12.ActRule (Fin 2) (QPhys fppBound dpBound) Γm tapeCountM K :=
  tickRule hK (fun q _ ws => ruleNext entryQ first hbound q ws) (modeCommands first rest)
    (fun q _ ws => ruleActs entryQ first q ws)
    (fun q _ ws j => ruleActs_length entryQ first hKq q ws j)

/-- the rule of the machine is that instance of the division of labour, by definition.  Stating
it costs nothing and saves every consumer from unfolding a rule whose tables are this big. -/
theorem tickPhysRule_eq {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9)
    (hbound : 320 < fppBound) (hKq : entryQ + 3 ≤ K) (hK : 2 ≤ K)
    (rest : QPhys fppBound dpBound → Option (Fin 2) →
      (Fin tapeCountM → PalPeg.Local.Window Γm K) → Fin 4 →
      PalPeg.ConcreteLocalMachine.ViewCommand) :
    tickPhysRule entryQ first hbound hKq hK rest
      = tickRule hK (fun q _ ws => ruleNext entryQ first hbound q ws) (modeCommands first rest)
          (fun q _ ws => ruleActs entryQ first q ws)
          (fun q _ ws j => ruleActs_length entryQ first hKq q ws j) := rfl

/-- **the heads of the encoding after a tick of the machine, from the row the table names.**
This is the head side of a tick with the rule of the machine and its real tables in place of the
abstract ones: a mode's branch names a row, the row names this head's command, and the command
names the operation the abstract tick does to this head.

Stated on the twelve steps themselves rather than on the one fused step.  The two are the same
thing by `idealStep_fused`, but putting a rule with tables this big inside `iterRule` sends the
elaborator's `whnf` past a million heartbeats, so the fusion is done once, where the tick is
assembled, and not in every corollary. -/
theorem tickPhysRule_heads {fppBound dpBound K margin : ℕ} (entryQ : ℕ) (first : Fin 9)
    (hbound : 320 < fppBound) (hKq : entryQ + 3 ≤ K) (hK : 2 ≤ K) (hmargin : K ≤ margin)
    (rest : QPhys fppBound dpBound → Option (Fin 2) →
      (Fin tapeCountM → PalPeg.Local.Window Γm K) → Fin 4 →
      PalPeg.ConcreteLocalMachine.ViewCommand)
    (v : Fin 4) (x : QPhys fppBound dpBound × (Fin tapeCountM → STape Γm))
    (input : Option (Fin 2)) (hslot0 : x.1.slot.val = 0)
    (command : PalPeg.ConcreteLocalMachine.ViewCommand)
    (hrow : modeCommands first rest x.1 input
      (fun tape => PalPeg.Local.readWin blankM K (x.2 tape)) v = command)
    (view : PalPeg.LocalInputView.InputView) (hwf : PalPeg.LocalInputView.WF view)
    (hcells : PalPeg.LocalViewCells.ViewCells view)
    (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (hold : ∀ t, x.2 (slotIndex (headSlot v t)) = mapTape encCell (viewTapes t))
    (hrep : PalPeg.ConcreteLocalMachine.ViewRep margin view (x.1.gap v) (x.1.micro v) viewTapes)
    (howed : (x.1.micro v).2.2.2 = 0)
    (head head' : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (habs : PalPeg.LocalArrival.absHead' view [] = head)
    (f : PalPeg.GalilScaffoldInputHead.PlaceHead → PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hf : headOp command = some f) (hhead' : head' = f head)
    (hready : command = .moveRight →
      view.gap = true → view.near = [] → PalPeg.RTQueue.toList view.far ≠ []) :
    ∃ (view' : PalPeg.LocalInputView.InputView)
        (viewTapes' : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc),
      PalPeg.LocalArrival.absHead' view' [] = head' ∧
        PalPeg.ConcreteLocalMachine.ViewRep margin view'
            ((PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hKq hK rest)
              blankM x input 12).1.gap v)
            ((PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hKq hK rest)
              blankM x input 12).1.micro v) viewTapes' ∧
          (∀ i, (PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hKq hK rest)
              blankM x input 12).2 (slotIndex (headSlot v i))
                = mapTape encCell (viewTapes' i)) ∧
            PalPeg.LocalViewCells.ViewCells view' ∧ PalPeg.LocalInputView.WF view' := by
  rw [tickPhysRule_eq entryQ first hbound hKq hK rest]
  have hcommand : (PalPeg.LocalStepFusion.idealRun
      (tickRule hK (fun q _ ws => ruleNext entryQ first hbound q ws) (modeCommands first rest)
        (fun q _ ws => ruleActs entryQ first q ws)
        (fun q _ ws j => ruleActs_length entryQ first hKq q ws j)) blankM x input
        1).1.commands v = command := by
    rw [commands_afterFirstStep hK (fun q _ ws => ruleNext entryQ first hbound q ws)
      (modeCommands first rest) (fun q _ ws => ruleActs entryQ first q ws)
      (fun q _ ws j => ruleActs_length entryQ first hKq q ws j) x input hslot0 v]
    exact hrow
  exact heads_afterTick hK hmargin
    (fun q _ ws => ruleNext entryQ first hbound q ws) (modeCommands first rest)
    (fun q _ ws => ruleActs entryQ first q ws)
    (fun q _ ws j => ruleActs_length entryQ first hKq q ws j) v x input hslot0
    (fun step => (PalPeg.LocalStepFusion.idealRun
      (tickRule hK (fun q _ ws => ruleNext entryQ first hbound q ws) (modeCommands first rest)
        (fun q _ ws => ruleActs entryQ first q ws)
        (fun q _ ws j => ruleActs_length entryQ first hKq q ws j)) blankM x input step).1)
    (fun step slot => (PalPeg.LocalStepFusion.idealRun
      (tickRule hK (fun q _ ws => ruleNext entryQ first hbound q ws) (modeCommands first rest)
        (fun q _ ws => ruleActs entryQ first q ws)
        (fun q _ ws j => ruleActs_length entryQ first hKq q ws j)) blankM x input step).2
      (slotIndex slot))
    (fun _ => rfl) (fun _ _ => rfl) view hwf hcells viewTapes hold hrep howed head head' habs f
    (by rw [hcommand]; exact hf) hhead'
    (fun hmove => hready (hcommand.symm.trans hmove))

/-- **in the five modes whose branches move no head, every head stands still.**  The end mark,
the walk home, the back half of the choice, the preparation program and the fallback copy each
get the whole head side of their tick from here, with no work of their own. -/
theorem tickPhysRule_heads_still {fppBound dpBound K margin : ℕ} (entryQ : ℕ) (first : Fin 9)
    (hbound : 320 < fppBound) (hKq : entryQ + 3 ≤ K) (hK : 2 ≤ K) (hmargin : K ≤ margin)
    (rest : QPhys fppBound dpBound → Option (Fin 2) →
      (Fin tapeCountM → PalPeg.Local.Window Γm K) → Fin 4 →
      PalPeg.ConcreteLocalMachine.ViewCommand)
    (v : Fin 4) (x : QPhys fppBound dpBound × (Fin tapeCountM → STape Γm))
    (input : Option (Fin 2)) (hslot0 : x.1.slot.val = 0)
    (hmode : x.1.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd
      ∨ x.1.ctl.mode = PalPeg.GalilScaffoldController.Mode.home
      ∨ x.1.ctl.mode = PalPeg.GalilScaffoldController.Mode.choose
      ∨ x.1.ctl.mode = PalPeg.GalilScaffoldController.Mode.fpp
      ∨ x.1.ctl.mode = PalPeg.GalilScaffoldController.Mode.copy)
    (view : PalPeg.LocalInputView.InputView) (hwf : PalPeg.LocalInputView.WF view)
    (hcells : PalPeg.LocalViewCells.ViewCells view)
    (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (hold : ∀ t, x.2 (slotIndex (headSlot v t)) = mapTape encCell (viewTapes t))
    (hrep : PalPeg.ConcreteLocalMachine.ViewRep margin view (x.1.gap v) (x.1.micro v) viewTapes)
    (howed : (x.1.micro v).2.2.2 = 0)
    (head : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (habs : PalPeg.LocalArrival.absHead' view [] = head) :
    ∃ (view' : PalPeg.LocalInputView.InputView)
        (viewTapes' : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc),
      PalPeg.LocalArrival.absHead' view' [] = head ∧
        PalPeg.ConcreteLocalMachine.ViewRep margin view'
            ((PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hKq hK rest)
              blankM x input 12).1.gap v)
            ((PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hKq hK rest)
              blankM x input 12).1.micro v) viewTapes' ∧
          (∀ i, (PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hKq hK rest)
              blankM x input 12).2 (slotIndex (headSlot v i))
                = mapTape encCell (viewTapes' i)) ∧
            PalPeg.LocalViewCells.ViewCells view' ∧ PalPeg.LocalInputView.WF view' :=
  tickPhysRule_heads entryQ first hbound hKq hK hmargin rest v x input hslot0 .stay
    (by rw [modeCommands_eq_stay first rest x.1 input _ hmode]; rfl) view hwf hcells viewTapes
    hold hrep howed head head habs id rfl rfl (fun h => absurd h (by simp))

/-- **in the rewind, the left cursor walks one cell left, and the centre with it when the rewind
is paired.**  The other cursors stand still, and nothing moves at all once the program's own tape
shows the first instruction again. -/
theorem tickPhysRule_heads_rewind {fppBound dpBound K margin : ℕ} (entryQ : ℕ) (first : Fin 9)
    (hbound : 320 < fppBound) (hKq : entryQ + 3 ≤ K) (hK : 2 ≤ K) (hmargin : K ≤ margin)
    (rest : QPhys fppBound dpBound → Option (Fin 2) →
      (Fin tapeCountM → PalPeg.Local.Window Γm K) → Fin 4 →
      PalPeg.ConcreteLocalMachine.ViewCommand)
    (v : Fin 4) (x : QPhys fppBound dpBound × (Fin tapeCountM → STape Γm))
    (input : Option (Fin 2)) (hslot0 : x.1.slot.val = 0)
    (hmode : x.1.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind)
    (hnot : ¬ centreRead (fun tape => PalPeg.Local.readWin blankM K (x.2 tape))
      (progSlot x.1.fppLive 8) = encProg first)
    (hv : v = 0 ∨ (x.1.ctl.pair = true ∧ v = 1))
    (view : PalPeg.LocalInputView.InputView) (hwf : PalPeg.LocalInputView.WF view)
    (hcells : PalPeg.LocalViewCells.ViewCells view)
    (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (hold : ∀ t, x.2 (slotIndex (headSlot v t)) = mapTape encCell (viewTapes t))
    (hrep : PalPeg.ConcreteLocalMachine.ViewRep margin view (x.1.gap v) (x.1.micro v) viewTapes)
    (howed : (x.1.micro v).2.2.2 = 0)
    (head : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (habs : PalPeg.LocalArrival.absHead' view [] = head) :
    ∃ (view' : PalPeg.LocalInputView.InputView)
        (viewTapes' : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc),
      PalPeg.LocalArrival.absHead' view' []
          = PalPeg.GalilScaffoldInputHead.left head ∧
        PalPeg.ConcreteLocalMachine.ViewRep margin view'
            ((PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hKq hK rest)
              blankM x input 12).1.gap v)
            ((PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hKq hK rest)
              blankM x input 12).1.micro v) viewTapes' ∧
          (∀ i, (PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hKq hK rest)
              blankM x input 12).2 (slotIndex (headSlot v i))
                = mapTape encCell (viewTapes' i)) ∧
            PalPeg.LocalViewCells.ViewCells view' ∧ PalPeg.LocalInputView.WF view' :=
  tickPhysRule_heads entryQ first hbound hKq hK hmargin rest v x input hslot0 .moveLeft
    (by
      rw [modeCommands_rewind first rest x.1 input _ hmode]
      exact rewindCommands_walks first x.1.fppLive x.1 _ hnot v hv)
    view hwf hcells viewTapes hold hrep howed head
    (PalPeg.GalilScaffoldInputHead.left head) habs PalPeg.GalilScaffoldInputHead.left rfl rfl
    (fun h => absurd h (by simp))

/-- a slot that is no head's is a slot of the right-hand summand, which is how the rule tells the
two apart. -/
theorem isLeft_eq_false_of_ne_headSlot {slot : Slot} (h : ∀ v i, slot ≠ headSlot v i) :
    (slotIndex.symm (slotIndex slot)).isLeft = false := by
  rw [Equiv.symm_apply_apply]
  match slot with
  | .inl p => exact absurd rfl (h p.1 p.2)
  | .inr r => rfl

/-- **the control side of the encoding after a tick of the machine, from what the branch is
already proved to leave behind.**  The hypothesis is the control half of the branch theorems'
conclusion as they stand, and the conclusion is the same of the tick: the tick leaves every field
that is not a view's exactly as the branch put it, and those are the only fields `EncControl`
speaks of. -/
theorem encControl_afterTick {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9)
    (hbound : 320 < fppBound) (hKq : entryQ + 3 ≤ K) (hK : 2 ≤ K)
    (rest : QPhys fppBound dpBound → Option (Fin 2) →
      (Fin tapeCountM → PalPeg.Local.Window Γm K) → Fin 4 →
      PalPeg.ConcreteLocalMachine.ViewCommand)
    (w : List (Fin 2)) (y : State GalilVM) (q : QPhys fppBound dpBound)
    (T : Slot → STape Γm) (input : Option (Fin 2)) (hslot0 : q.slot.val = 0)
    (hstep : EncControl w y (ruleNext entryQ first hbound q
      (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)))) :
    EncControl w y (PalPeg.LocalStepFusion.idealRun
      (tickPhysRule entryQ first hbound hKq hK rest) blankM (q, tapesOf T) input 12).1 :=
  encControl_congr
    (by
      rw [tickPhysRule_eq entryQ first hbound hKq hK rest]
      exact (tickRule_headFree hK (fun q _ ws => ruleNext entryQ first hbound q ws)
        (modeCommands first rest) (fun q _ ws => ruleActs entryQ first q ws)
        (fun q _ ws j => ruleActs_length entryQ first hKq q ws j) (q, tapesOf T) input
        hslot0).symm)
    hstep

/-- **the tape side of the encoding after a tick of the machine, away from the heads, from what
the branch is already proved to leave behind.**  The hypothesis is the tape half of the branch
theorems' conclusion as they stand — the branch's own actions applied to the tapes — and what it
gives is every field but `heads`; the heads and the margins of their slots come in as the last
two hypotheses.

Both halves are stated on the branch tables `ruleNext` and `ruleActs` rather than on one step of
the one-step rule.  The two are the same by `physRule_nq_*` and `physRule_acts_*`, but asking the
elaborator to see it here makes its `whnf` diverge on a rule whose tables are this big. -/
theorem encTapes_afterTickOfState {fppBound dpBound K : ℕ} (margin : ℕ) (entryQ : ℕ) (first : Fin 9)
    (hbound : 320 < fppBound) (hKq : entryQ + 3 ≤ K) (hK : 2 ≤ K)
    (rest : QPhys fppBound dpBound → Option (Fin 2) →
      (Fin tapeCountM → PalPeg.Local.Window Γm K) → Fin 4 →
      PalPeg.ConcreteLocalMachine.ViewCommand)
    (y : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (input : Option (Fin 2)) (hslot0 : q.slot.val = 0)
    {z : State GalilVM}
    (hfppOf : ∀ i, y.vm.fpp.program.config.tapes i = z.vm.fpp.program.config.tapes i)
    (hdpOf : ∀ i, y.vm.dp.config.tapes i = z.vm.dp.config.tapes i)
    (hcountersOf : counterOf y = counterOf z) (hplacesOf : placeOf y = placeOf z)
    (hperiodOf : periodOf y = periodOf z) (hanswerOf : answerOf y = answerOf z)
    {polarity : Fin 16 → Bool} {gap : Fin 4 → Bool}
    {micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl} {fppLive dpLive : Bool}
    (hstep : EncTapes margin z polarity gap micro fppLive dpLive
      (fun slot => PalPeg.CloseoutCoreEnc12.actList blankM (T slot)
        (ruleActs entryQ first q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (slotIndex slot))))
    {polarity' : Fin 16 → Bool} {gap' : Fin 4 → Bool}
    {micro' : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl} {fppLive' dpLive' : Bool}
    (hpolarity : polarity' = polarity) (hfppLive : fppLive' = fppLive)
    (hdpLive : dpLive' = dpLive)
    (hmargins : ∀ (v : Fin 4) (i : Fin 12), margin ≤ PalPeg.Local.pos
      ((PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hKq hK rest) blankM
        (q, tapesOf T) input 12).2 (slotIndex (headSlot v i))))
    (hheads : ∀ (v : Fin 4) head, headOf y v = some head →
      ∃ (view : PalPeg.LocalInputView.InputView)
          (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc),
        PalPeg.LocalArrival.absHead' view [] = head ∧
          PalPeg.ConcreteLocalMachine.ViewRep margin view (gap' v) (micro' v) viewTapes ∧
          (∀ i, (PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hKq hK rest)
              blankM (q, tapesOf T) input 12).2 (slotIndex (headSlot v i))
                = mapTape encCell (viewTapes i)) ∧
            PalPeg.LocalViewCells.ViewCells view ∧ PalPeg.LocalInputView.WF view)
    (hidleHead : headOf y 3 = none → HeadSlotsRep margin gap' micro'
      (fun slot => (PalPeg.LocalStepFusion.idealRun
        (tickPhysRule entryQ first hbound hKq hK rest) blankM (q, tapesOf T) input 12).2
          (slotIndex slot)) 3) :
    EncTapes margin y polarity' gap' micro' fppLive' dpLive'
      (fun slot => (PalPeg.LocalStepFusion.idealRun
        (tickPhysRule entryQ first hbound hKq hK rest) blankM (q, tapesOf T) input 12).2
          (slotIndex slot)) :=
  encTapes_replaceHeadsOfState hstep hfppOf hdpOf hcountersOf hplacesOf hperiodOf hanswerOf
    (fun slot hne => by
      rw [tickPhysRule_eq entryQ first hbound hKq hK rest,
        tickRule_otherSlots hK (fun q _ ws => ruleNext entryQ first hbound q ws)
          (modeCommands first rest) (fun q _ ws => ruleActs entryQ first q ws)
          (fun q _ ws j => ruleActs_length entryQ first hKq q ws j) (q, tapesOf T) input hslot0
          (slotIndex slot) (isLeft_eq_false_of_ne_headSlot hne)]
      show PalPeg.CloseoutCoreEnc12.actList blankM (tapesOf T (slotIndex slot)) _ = _
      rw [tapesOf_apply])
    hmargins hpolarity hfppLive hdpLive hheads hidleHead

/-- **the control knows whether the chain's verifier exists.**  `headOf x 3` is `none` exactly
when the chain is idle, and the encoding's own `chainTag` field is that, so a row of the command
table may ask "is the fourth cursor there?" and be answered from the finite control alone — which
is what it needs to mirror the centre only while there is nothing else to mirror. -/
theorem headOf_three_eq_none_iff {fppBound dpBound : ℕ} {w : List (Fin 2)} {x : State GalilVM}
    {q : QPhys fppBound dpBound} (h : EncControl w x q) :
    headOf x 3 = none ↔ q.chainTag = ChainTag.idle := by
  rw [h.chainTag]
  show (match x.vm.chain with
    | .idle => none
    | .copy _ _ _ _ _ _ verifier => some verifier
    | .back _ _ _ _ verifier => some verifier
    | .watch wm => some wm.machine.verifier
    | .broken wm => some wm.machine.verifier) = none ↔ _
  cases x.vm.chain <;> simp [chainTagOf]

/-- **a cursor the abstraction names has it.** -/
theorem headSlotsRep_of_heads {margin : ℕ} {x : State GalilVM} {polarity : Fin 16 → Bool}
    {gap : Fin 4 → Bool} {micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl}
    {fppLive dpLive : Bool} {tapes : Slot → STape Γm}
    (h : EncTapes margin x polarity gap micro fppLive dpLive tapes) (v : Fin 4)
    (head : PalPeg.GalilScaffoldInputHead.PlaceHead) (hhead : headOf x v = some head) :
    HeadSlotsRep margin gap micro tapes v := by
  obtain ⟨view, viewTapes, -, hrep, hslots, hcells, hwf⟩ := h.heads v head hhead
  exact ⟨view, viewTapes, hrep, hslots, hcells, hwf⟩

/-- **every cursor of the machine holds a view**, whether or not the abstraction names it.  Three
of the four always have an abstract head; the fourth has one unless the chain is idle, and then
the encoding's own field gives it. -/
theorem headSlotsRep_all {margin : ℕ} {x : State GalilVM} {polarity : Fin 16 → Bool}
    {gap : Fin 4 → Bool} {micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl}
    {fppLive dpLive : Bool} {tapes : Slot → STape Γm}
    (h : EncTapes margin x polarity gap micro fppLive dpLive tapes) (v : Fin 4) :
    HeadSlotsRep margin gap micro tapes v := by
  match hv : headOf x v with
  | some head => exact headSlotsRep_of_heads h v head hv
  | none =>
    have hv3 : v = 3 := by
      fin_cases v
      · exact absurd hv (by simp [headOf])
      · exact absurd hv (by simp [headOf])
      · exact absurd hv (by simp [headOf])
      · rfl
    subst hv3
    exact h.idleHead hv

/-- **and it gives the margin of that cursor's twelve slots.**  A view's own tapes stand clear of
the left edge, and the change of alphabet does not move a head. -/
theorem margin_le_pos_headSlot {margin K : ℕ} (hK : 2 ≤ K) (hmargin : K ≤ margin)
    {gap : Fin 4 → Bool} {micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl}
    {tapes : Slot → STape Γm} {v : Fin 4} (h : HeadSlotsRep margin gap micro tapes v)
    (i : Fin 12) : margin ≤ PalPeg.Local.pos (tapes (headSlot v i)) := by
  obtain ⟨view, viewTapes, hrep, hslots, -, -⟩ := h
  rw [hslots i, pos_mapTape]
  exact PalPeg.ConcreteLocalMachine.ViewRep.margin_le_pos hK hmargin hrep i

/-- **and a tick carries it, whether or not the abstraction names that cursor.**  The twelve
steps ask nothing of the abstract head: they carry out the command the control holds, and the
view they leave behind is the view that command names.  What the command has to be is a command
of a cursor — standing still, a step left or a step right — which is what the rows of the table
name; the step right carries its arrival condition as usual. -/
theorem headSlotsRep_afterTick {fppBound dpBound K margin : ℕ} (hK : 2 ≤ K) (hmargin : K ≤ margin)
    (base commandsOf baseActs) (baseLen : ∀ q i ws j, (baseActs q i ws j).length ≤ K) (v : Fin 4)
    (x : QPhys fppBound dpBound × (Fin tapeCountM → STape Γm)) (input : Option (Fin 2))
    (hslot0 : x.1.slot.val = 0) (howed : (x.1.micro v).2.2.2 = 0)
    (view : PalPeg.LocalInputView.InputView)
    (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (hrep : PalPeg.ConcreteLocalMachine.ViewRep margin view (x.1.gap v) (x.1.micro v) viewTapes)
    (hslots : ∀ i, x.2 (slotIndex (headSlot v i)) = mapTape encCell (viewTapes i))
    (hcells : PalPeg.LocalViewCells.ViewCells view) (hwf : PalPeg.LocalInputView.WF view)
    (command : PalPeg.ConcreteLocalMachine.ViewCommand)
    (hrow : commandsOf x.1 input (fun tape => PalPeg.Local.readWin blankM K (x.2 tape)) v
      = command)
    (f : PalPeg.GalilScaffoldInputHead.PlaceHead → PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hf : headOp command = some f)
    (hready : command = .moveRight →
      view.gap = true → view.near = [] → PalPeg.RTQueue.toList view.far ≠ []) :
    HeadSlotsRep margin
        (PalPeg.LocalStepFusion.idealRun (tickRule hK base commandsOf baseActs baseLen) blankM x
          input 12).1.gap
        (PalPeg.LocalStepFusion.idealRun (tickRule hK base commandsOf baseActs baseLen) blankM x
          input 12).1.micro
        (fun slot => (PalPeg.LocalStepFusion.idealRun
          (tickRule hK base commandsOf baseActs baseLen) blankM x input 12).2 (slotIndex slot))
        v := by
  have hcommand : (PalPeg.LocalStepFusion.idealRun
      (tickRule hK base commandsOf baseActs baseLen) blankM x input 1).1.commands v = command := by
    rw [commands_afterFirstStep hK base commandsOf baseActs baseLen x input hslot0 v, hrow]
  obtain ⟨hrep', howed', hslots'⟩ := headTick_of_tickRule hK hmargin base commandsOf baseActs
    baseLen v x input hslot0
    (fun step => (PalPeg.LocalStepFusion.idealRun
      (tickRule hK base commandsOf baseActs baseLen) blankM x input step).1)
    (fun step slot => (PalPeg.LocalStepFusion.idealRun
      (tickRule hK base commandsOf baseActs baseLen) blankM x input step).2 (slotIndex slot))
    (fun _ => rfl) (fun _ _ => rfl) view hwf hcells viewTapes hslots hrep howed
  rw [hcommand] at hrep'
  exact ⟨PalPeg.ConcreteLocalMachine.viewApply command view, _, hrep', hslots',
    viewCells_viewApply hwf command (fun h => hready h) hcells f hf,
    wf_viewApply hwf command f hf⟩

/-- **the three bits of the control a tick leaves as the branch put them**, named so that the
transports can be given them without digging into a twenty-one-fold tuple.  All three are in
`headFreeFields`, so this is `tickRule_headFree` read component by component. -/
theorem tickPhysRule_bits {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9)
    (hbound : 320 < fppBound) (hKq : entryQ + 3 ≤ K) (hK : 2 ≤ K)
    (rest : QPhys fppBound dpBound → Option (Fin 2) →
      (Fin tapeCountM → PalPeg.Local.Window Γm K) → Fin 4 →
      PalPeg.ConcreteLocalMachine.ViewCommand)
    (q : QPhys fppBound dpBound) (T : Slot → STape Γm) (input : Option (Fin 2))
    (hslot0 : q.slot.val = 0) :
    (PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hKq hK rest) blankM
        (q, tapesOf T) input 12).1.polarity
      = (ruleNext entryQ first hbound q
          (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).polarity ∧
    (PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hKq hK rest) blankM
        (q, tapesOf T) input 12).1.fppLive
      = (ruleNext entryQ first hbound q
          (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).fppLive ∧
    (PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hKq hK rest) blankM
        (q, tapesOf T) input 12).1.dpLive
      = (ruleNext entryQ first hbound q
          (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).dpLive := by
  have hfree : headFreeFields (PalPeg.LocalStepFusion.idealRun
      (tickPhysRule entryQ first hbound hKq hK rest) blankM (q, tapesOf T) input 12).1
      = headFreeFields (ruleNext entryQ first hbound q
          (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))) := by
    rw [tickPhysRule_eq entryQ first hbound hKq hK rest]
    exact tickRule_headFree hK (fun q _ ws => ruleNext entryQ first hbound q ws)
      (modeCommands first rest) (fun q _ ws => ruleActs entryQ first q ws)
      (fun q _ ws j => ruleActs_length entryQ first hKq q ws j) (q, tapesOf T) input hslot0
  simp only [headFreeFields, Prod.mk.injEq] at hfree
  exact ⟨hfree.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hfree.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hfree.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- **after a tick, every cursor still holds a view**, whatever command the table names for it.
Which is what the margins of all four cursors' slots come from, the chain's verifier included,
whether or not the abstraction names it. -/
theorem tickPhysRule_headSlotsRep {fppBound dpBound K margin : ℕ} (entryQ : ℕ)
    (first : Fin 9) (hbound : 320 < fppBound) (hKq : entryQ + 3 ≤ K) (hK : 2 ≤ K)
    (hmargin : K ≤ margin)
    (rest : QPhys fppBound dpBound → Option (Fin 2) →
      (Fin tapeCountM → PalPeg.Local.Window Γm K) → Fin 4 →
      PalPeg.ConcreteLocalMachine.ViewCommand)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (input : Option (Fin 2)) (hslot0 : q.slot.val = 0)
    (howed : ∀ v, (q.micro v).2.2.2 = 0)
    (henc : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T) (v : Fin 4)
    (command : PalPeg.ConcreteLocalMachine.ViewCommand)
    (hrow : modeCommands first rest q input
      (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) v = command)
    (f : PalPeg.GalilScaffoldInputHead.PlaceHead → PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hf : headOp command = some f)
    (hready : ∀ view : PalPeg.LocalInputView.InputView,
      HeadSlotsRepAt margin q.gap q.micro T v view → command = .moveRight →
        view.gap = true → view.near = [] → PalPeg.RTQueue.toList view.far ≠ []) :
    HeadSlotsRep margin
        (PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hKq hK rest) blankM
          (q, tapesOf T) input 12).1.gap
        (PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hKq hK rest) blankM
          (q, tapesOf T) input 12).1.micro
        (fun slot => (PalPeg.LocalStepFusion.idealRun
          (tickPhysRule entryQ first hbound hKq hK rest) blankM (q, tapesOf T) input 12).2
            (slotIndex slot)) v := by
  obtain ⟨view, viewTapes, hrep, hslots, hcells, hwf⟩ := headSlotsRep_all henc v
  rw [tickPhysRule_eq entryQ first hbound hKq hK rest]
  exact headSlotsRep_afterTick hK hmargin (fun q _ ws => ruleNext entryQ first hbound q ws)
    (modeCommands first rest) (fun q _ ws => ruleActs entryQ first q ws)
    (fun q _ ws j => ruleActs_length entryQ first hKq q ws j) v (q, tapesOf T) input hslot0
    (howed v) view viewTapes hrep
    (fun i => by
      show tapesOf T (slotIndex (headSlot v i)) = _
      rw [tapesOf_apply]
      exact hslots i) hcells hwf command hrow f hf
    (hready view ⟨viewTapes, hrep, hslots, hcells, hwf⟩)

/-- **after a tick of one of the five still modes, every cursor still holds a view.** -/
theorem tickPhysRule_headSlotsRep_still {fppBound dpBound K margin : ℕ} (entryQ : ℕ)
    (first : Fin 9) (hbound : 320 < fppBound) (hKq : entryQ + 3 ≤ K) (hK : 2 ≤ K)
    (hmargin : K ≤ margin)
    (rest : QPhys fppBound dpBound → Option (Fin 2) →
      (Fin tapeCountM → PalPeg.Local.Window Γm K) → Fin 4 →
      PalPeg.ConcreteLocalMachine.ViewCommand)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (input : Option (Fin 2)) (hslot0 : q.slot.val = 0)
    (hmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd
      ∨ q.ctl.mode = PalPeg.GalilScaffoldController.Mode.home
      ∨ q.ctl.mode = PalPeg.GalilScaffoldController.Mode.choose
      ∨ q.ctl.mode = PalPeg.GalilScaffoldController.Mode.fpp
      ∨ q.ctl.mode = PalPeg.GalilScaffoldController.Mode.copy)
    (howed : ∀ v, (q.micro v).2.2.2 = 0)
    (henc : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T) (v : Fin 4) :
    HeadSlotsRep margin
        (PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hKq hK rest) blankM
          (q, tapesOf T) input 12).1.gap
        (PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hKq hK rest) blankM
          (q, tapesOf T) input 12).1.micro
        (fun slot => (PalPeg.LocalStepFusion.idealRun
          (tickPhysRule entryQ first hbound hKq hK rest) blankM (q, tapesOf T) input 12).2
            (slotIndex slot)) v :=
  tickPhysRule_headSlotsRep entryQ first hbound hKq hK hmargin rest x q T input hslot0 howed henc v
    .stay (by rw [modeCommands_eq_stay first rest q input _ hmode]; rfl) id rfl
    (fun _ _ h => absurd h (by simp))

/-- **the whole obligation of a tick.**  The hypotheses are what a mode's branch is already
proved to leave behind, said of the branch tables — the control it writes and the tapes its own
actions make — together with what its row of the command table says each cursor does and what
the abstract tick does to that cursor.  The conclusion is the encoding of the abstract successor
by the state the machine is in twelve steps later, which is one tick.

Everything else is assembled from what is proved: the control side is head-free, the tape side
away from the heads is the branch's own actions, the heads come from the view layer with the row's
own command, and the margins of all four cursors' slots come from the views those slots hold. -/
theorem enc_afterTickOfState {fppBound dpBound K : ℕ} (margin entryQ : ℕ) (first : Fin 9)
    (hbound : 320 < fppBound) (hKq : entryQ + 3 ≤ K) (hK : 2 ≤ K) (hmargin : K ≤ margin)
    (rest : QPhys fppBound dpBound → Option (Fin 2) →
      (Fin tapeCountM → PalPeg.Local.Window Γm K) → Fin 4 →
      PalPeg.ConcreteLocalMachine.ViewCommand)
    (w : List (Fin 2)) (x y : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (input : Option (Fin 2)) (hslot0 : q.slot.val = 0)
    (howed : ∀ v, (q.micro v).2.2.2 = 0)
    (commands : Fin 4 → PalPeg.ConcreteLocalMachine.ViewCommand)
    (hrow : ∀ v, modeCommands first rest q input
      (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) v = commands v)
    (fs : Fin 4 → PalPeg.GalilScaffoldInputHead.PlaceHead →
      PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hf : ∀ v, headOp (commands v) = some (fs v))
    (hheadSome : ∀ v, (headOf x v).isSome = (headOf y v).isSome)
    (hheadMap : ∀ v head, headOf x v = some head → headOf y v = some (fs v head))
    (hready : ∀ v view, HeadSlotsRepAt margin q.gap q.micro T v view →
      commands v = .moveRight → view.gap = true → view.near = [] →
        PalPeg.RTQueue.toList view.far ≠ [])
    (henc : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T)
    (hctl : EncControl w y (ruleNext entryQ first hbound q
      (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))))
    {z : State GalilVM}
    (hfppOf : ∀ i, y.vm.fpp.program.config.tapes i = z.vm.fpp.program.config.tapes i)
    (hdpOf : ∀ i, y.vm.dp.config.tapes i = z.vm.dp.config.tapes i)
    (hcountersOf : counterOf y = counterOf z) (hplacesOf : placeOf y = placeOf z)
    (hperiodOf : periodOf y = periodOf z) (hanswerOf : answerOf y = answerOf z)
    (htapes : EncTapes margin z
      (ruleNext entryQ first hbound q
        (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).polarity
      (ruleNext entryQ first hbound q
        (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).gap
      (ruleNext entryQ first hbound q
        (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).micro
      (ruleNext entryQ first hbound q
        (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).fppLive
      (ruleNext entryQ first hbound q
        (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).dpLive
      (fun slot => PalPeg.CloseoutCoreEnc12.actList blankM (T slot)
        (ruleActs entryQ first q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (slotIndex slot)))) :
    Enc w margin y
      ((PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hKq hK rest) blankM
          (q, tapesOf T) input 12).1,
        fun i => (PalPeg.LocalStepFusion.idealRun
          (tickPhysRule entryQ first hbound hKq hK rest) blankM (q, tapesOf T) input 12).2
            (slotIndex i)) := by
  obtain ⟨hpol, hfpp, hdp⟩ := tickPhysRule_bits entryQ first hbound hKq hK rest q T input hslot0
  have hcursor : ∀ v, HeadSlotsRep margin
      (PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hKq hK rest) blankM
        (q, tapesOf T) input 12).1.gap
      (PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hKq hK rest) blankM
        (q, tapesOf T) input 12).1.micro
      (fun slot => (PalPeg.LocalStepFusion.idealRun
        (tickPhysRule entryQ first hbound hKq hK rest) blankM (q, tapesOf T) input 12).2
          (slotIndex slot)) v := fun v =>
    tickPhysRule_headSlotsRep entryQ first hbound hKq hK hmargin rest x q T input hslot0 howed
      henc v (commands v) (hrow v) (fs v) (hf v) (hready v)
  have hcontrol := encControl_afterTick entryQ first hbound hKq hK rest w y q T input hslot0 hctl
  have htape := encTapes_afterTickOfState margin entryQ first hbound hKq hK rest y q T input
    hslot0 hfppOf hdpOf hcountersOf hplacesOf hperiodOf hanswerOf htapes hpol hfpp hdp
    (fun v i => margin_le_pos_headSlot hK hmargin (hcursor v) i)
    (fun v head hhead => by
      have hsome : (headOf x v).isSome = true := by rw [hheadSome v, hhead]; rfl
      obtain ⟨headx, hheadx⟩ : ∃ headx, headOf x v = some headx := by
        cases hx : headOf x v with
        | none => rw [hx] at hsome; exact absurd hsome (by simp)
        | some a => exact ⟨a, rfl⟩
      have heq : head = fs v headx :=
        Option.some.inj ((hhead.symm.trans (hheadMap v headx hheadx)))
      obtain ⟨view, viewTapes, habs, hrep, hslots, hcells, hwf⟩ := henc.heads v headx hheadx
      exact tickPhysRule_heads entryQ first hbound hKq hK hmargin rest v (q, tapesOf T) input
        hslot0 (commands v) (hrow v) view hwf hcells viewTapes
        (fun t => by
          show tapesOf T (slotIndex (headSlot v t)) = _
          rw [tapesOf_apply]
          exact hslots t)
        hrep (howed v) headx head habs (fs v) (hf v) heq
        (hready v view ⟨viewTapes, hrep, hslots, hcells, hwf⟩))
    (fun _ => hcursor 3)
  unfold Enc
  dsimp only
  refine And.intro ?_ ?_
  · exact hcontrol
  · exact htape

/-- **the whole obligation of a tick, in the five modes that move no head.**  Their row of the
command table is standing still, and standing still is the identity on the abstract head. -/
theorem enc_afterStillTick {fppBound dpBound K : ℕ} (margin entryQ : ℕ) (first : Fin 9)
    (hbound : 320 < fppBound) (hKq : entryQ + 3 ≤ K) (hK : 2 ≤ K) (hmargin : K ≤ margin)
    (rest : QPhys fppBound dpBound → Option (Fin 2) →
      (Fin tapeCountM → PalPeg.Local.Window Γm K) → Fin 4 →
      PalPeg.ConcreteLocalMachine.ViewCommand)
    (w : List (Fin 2)) (x y : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (input : Option (Fin 2)) (hslot0 : q.slot.val = 0)
    (hstay : modeCommands first rest q input
      (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) = stayCommands)
    (howed : ∀ v, (q.micro v).2.2.2 = 0) (hheadsSame : ∀ v, headOf y v = headOf x v)
    (henc : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T)
    (hctl : EncControl w y (ruleNext entryQ first hbound q
      (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))))
    (htapes : EncTapes margin y
      (ruleNext entryQ first hbound q
        (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).polarity
      (ruleNext entryQ first hbound q
        (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).gap
      (ruleNext entryQ first hbound q
        (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).micro
      (ruleNext entryQ first hbound q
        (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).fppLive
      (ruleNext entryQ first hbound q
        (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).dpLive
      (fun slot => PalPeg.CloseoutCoreEnc12.actList blankM (T slot)
        (ruleActs entryQ first q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (slotIndex slot)))) :
    Enc w margin y
      ((PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hKq hK rest) blankM
          (q, tapesOf T) input 12).1,
        fun i => (PalPeg.LocalStepFusion.idealRun
          (tickPhysRule entryQ first hbound hKq hK rest) blankM (q, tapesOf T) input 12).2
            (slotIndex i)) :=
  enc_afterTickOfState margin entryQ first hbound hKq hK hmargin rest w x y q T input hslot0 howed
    (fun _ => .stay) (fun _ => by rw [hstay]; rfl)
    (fun _ => id) (fun _ => rfl) (fun v => by rw [hheadsSame v])
    (fun v head hhead => by rw [hheadsSame v]; exact hhead)
    (fun _ _ _ h => absurd h (by simp)) henc hctl
    (fun i => rfl) (fun i => rfl) rfl rfl rfl rfl htapes

/-- **one step of the one-step rule, written out.**  Its control is the mode table's and its
tapes are the action table's own actions, by definition; saying so once lets the branch theorems
be read as facts about those two tables, which is the form the tick needs them in. -/
theorem idealStep_physRule {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9)
    (hbound : 320 < fppBound) (hKq : entryQ + 3 ≤ K) (q : QPhys fppBound dpBound)
    (T : Slot → STape Γm) :
    PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hKq)
        blankM (q, tapesOf T) none
      = (ruleNext entryQ first hbound q
            (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)),
          fun j => PalPeg.CloseoutCoreEnc12.actList blankM (tapesOf T j)
            (ruleActs entryQ first q
              (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) j)) := rfl

/-- **a branch theorem's conclusion, in the two pieces the tick asks for.**  The branch theorems
conclude `Enc` of one step of the one-step rule; the tick asks for the control the mode table
writes and the tapes the action table's own actions make.  They are the same thing, and this is
where that is said, once, so that no statement about a tick has to mention the one-step rule. -/
theorem enc_step_pieces {fppBound dpBound K : ℕ} (margin : ℕ) (entryQ : ℕ) (first : Fin 9)
    (hbound : 320 < fppBound) (hKq : entryQ + 3 ≤ K) (w : List (Fin 2)) (y : State GalilVM)
    (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (h : Enc w margin y
      ((PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hKq)
          blankM (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep
          (physRule (dpBound := dpBound) entryQ first hbound hKq) blankM (q, tapesOf T) none).2
            (slotIndex i))) :
    EncControl w y (ruleNext entryQ first hbound q
        (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))) ∧
      EncTapes margin y
        (ruleNext entryQ first hbound q
          (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).polarity
        (ruleNext entryQ first hbound q
          (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).gap
        (ruleNext entryQ first hbound q
          (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).micro
        (ruleNext entryQ first hbound q
          (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).fppLive
        (ruleNext entryQ first hbound q
          (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).dpLive
        (fun slot => PalPeg.CloseoutCoreEnc12.actList blankM (T slot)
          (ruleActs entryQ first q
            (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) (slotIndex slot))) := by
  rw [idealStep_physRule entryQ first hbound hKq q T] at h
  unfold Enc at h
  dsimp only at h
  refine ⟨h.1, ?_⟩
  have htapes : (fun slot : Slot => PalPeg.CloseoutCoreEnc12.actList blankM
      (tapesOf T (slotIndex slot))
      (ruleActs entryQ first q
        (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) (slotIndex slot)))
      = fun slot : Slot => PalPeg.CloseoutCoreEnc12.actList blankM (T slot)
        (ruleActs entryQ first q
          (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) (slotIndex slot)) := by
    funext slot
    rw [tapesOf_apply]
  rw [← htapes]
  exact h.2

theorem physRule_nq_shift {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9)
    (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K) (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hm : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.shift)
    (hdone : remainsTest q.polarity ws = false) :
    (physRule (dpBound := dpBound) entryQ first hbound hK).nq q none ws = shiftExitNext q := by
  show ruleNext entryQ first hbound q ws = _
  unfold ruleNext
  rw [hm]
  dsimp only
  rw [if_neg (by rw [hdone]; simp)]

theorem physRule_acts_shift {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9)
    (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K) (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hm : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.shift) :
    (physRule (dpBound := dpBound) entryQ first hbound hK).acts q none ws
      = withErase q.fppLive ws (fun _ => []) := by
  show ruleActs entryQ first q ws = _
  unfold ruleActs
  rw [hm]

theorem physRule_nq_markEnd {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9) (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hm : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd) :
    (physRule (dpBound := dpBound) entryQ first hbound hK).nq q none ws = markEndNext q.fppLive q ws := by
  show ruleNext entryQ first hbound q ws = _
  unfold ruleNext
  rw [hm]

theorem physRule_acts_markEnd {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9) (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hm : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd) :
    (physRule (dpBound := dpBound) entryQ first hbound hK).acts q none ws = withErase q.fppLive ws (markEndActs q.fppLive ws) := by
  show ruleActs entryQ first q ws = _
  unfold ruleActs
  rw [hm]

theorem physRule_nq_home {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9) (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hm : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.home) :
    (physRule (dpBound := dpBound) entryQ first hbound hK).nq q none ws = homeNext q.fppLive hbound q ws := by
  show ruleNext entryQ first hbound q ws = _
  unfold ruleNext
  rw [hm]

theorem physRule_acts_home {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9) (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hm : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.home) :
    (physRule (dpBound := dpBound) entryQ first hbound hK).acts q none ws = withErase q.fppLive ws (homeActs q.fppLive ws) := by
  show ruleActs entryQ first q ws = _
  unfold ruleActs
  rw [hm]

theorem physRule_nq_choose {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9) (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hm : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.choose) :
    (physRule (dpBound := dpBound) entryQ first hbound hK).nq q none ws = chooseBackNext q := by
  show ruleNext entryQ first hbound q ws = _
  unfold ruleNext
  rw [hm]

theorem physRule_acts_choose {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9) (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hm : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.choose) :
    (physRule (dpBound := dpBound) entryQ first hbound hK).acts q none ws = withErase q.fppLive ws (chooseBackActs q.fppLive ws) := by
  show ruleActs entryQ first q ws = _
  unfold ruleActs
  rw [hm]

/-- **the three slots one tick of the fallback copy writes on**, named once so that the branch
can read each of them off.  The program's copy tape takes the symbol and steps right, the work
counter is popped or pushed according to its sign, and the walker is popped unless it stands on a
gap. -/
noncomputable def copyOneBase {K : ℕ} (live gapBit : Bool) (polarity : Fin 16 → Bool) (a : Fin 3)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) :
    Fin tapeCountM → List (PalPeg.CloseoutCoreEnc12.Act Γm) :=
  fun j =>
    if j = slotIndex (progSlot live 7) then
      [some (encProg (PalPeg.GalilFppPreparation.symbol a),
        (.right : PalPeg.CloseoutCoreEnc12.MoveC))]
    else if j = slotIndex (counterSlot 9) then
      [if workPositive polarity ws then some (blankM, (.left : PalPeg.CloseoutCoreEnc12.MoveC))
        else some (encSeg PalPeg.LocalCounter.mark, (.right : PalPeg.CloseoutCoreEnc12.MoveC))]
    else if j = slotIndex (placeSlot 1) then
      (if gapBit then []
        else [some (centreRead ws (placeSlot 1), (.left : PalPeg.CloseoutCoreEnc12.MoveC))])
    else []

@[simp] theorem copyOneBase_prog {K : ℕ} (live gapBit : Bool) (polarity : Fin 16 → Bool)
    (a : Fin 3) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) :
    copyOneBase live gapBit polarity a ws (slotIndex (progSlot live 7))
      = [some (encProg (PalPeg.GalilFppPreparation.symbol a),
          (.right : PalPeg.CloseoutCoreEnc12.MoveC))] := by
  unfold copyOneBase
  rw [if_pos rfl]

@[simp] theorem copyOneBase_counter {K : ℕ} (live gapBit : Bool) (polarity : Fin 16 → Bool)
    (a : Fin 3) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) :
    copyOneBase live gapBit polarity a ws (slotIndex (counterSlot 9))
      = [if workPositive polarity ws then
            some (blankM, (.left : PalPeg.CloseoutCoreEnc12.MoveC))
          else some (encSeg PalPeg.LocalCounter.mark,
            (.right : PalPeg.CloseoutCoreEnc12.MoveC))] := by
  unfold copyOneBase
  rw [if_neg (fun h => (progSlot_ne_counterSlot live 7 9) (slotIndex.injective h).symm),
    if_pos rfl]

@[simp] theorem copyOneBase_place {K : ℕ} (live gapBit : Bool) (polarity : Fin 16 → Bool)
    (a : Fin 3) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) :
    copyOneBase live gapBit polarity a ws (slotIndex (placeSlot 1))
      = (if gapBit then []
          else [some (centreRead ws (placeSlot 1),
            (.left : PalPeg.CloseoutCoreEnc12.MoveC))]) := by
  unfold copyOneBase
  rw [if_neg (fun h => (progSlot_ne_placeSlot live 7 1) (slotIndex.injective h).symm),
    if_neg (fun h => (counterSlot_ne_placeSlot 9 1) (slotIndex.injective h).symm), if_pos rfl]

theorem copyOneBase_progOther {K : ℕ} (live gapBit : Bool) (polarity : Fin 16 → Bool)
    (a : Fin 3) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (j : Fin 9) (hj : j ≠ 7) :
    copyOneBase live gapBit polarity a ws (slotIndex (progSlot live j)) = [] := by
  unfold copyOneBase
  rw [if_neg (fun h => hj (progSlotOf_injective live (slotIndex.injective h))),
    if_neg (fun h => (progSlot_ne_counterSlot live j 9) (slotIndex.injective h)),
    if_neg (fun h => (progSlot_ne_placeSlot live j 1) (slotIndex.injective h))]

theorem copyOneBase_off {K : ℕ} (live gapBit : Bool) (polarity : Fin 16 → Bool)
    (a : Fin 3) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (slot : Slot)
    (hprog : ∀ j : Fin 9, slot ≠ progSlot live j) (hcounter : slot ≠ counterSlot 9)
    (hplace : slot ≠ placeSlot 1) :
    copyOneBase live gapBit polarity a ws (slotIndex slot) = [] := by
  unfold copyOneBase
  rw [if_neg (fun h => hprog 7 (slotIndex.injective h)),
    if_neg (fun h => hcounter (slotIndex.injective h)),
    if_neg (fun h => hplace (slotIndex.injective h))]

/-- **the symbol the rule copies is the symbol the abstraction copies.**  The cursor's own bit
says whether it stands on a gap, and the centre of its window says which letter it stands on, so
the rule computes `GalilScaffoldPlace.read` without asking for it. -/
theorem copySymbol_eq {margin K : ℕ} (hK : K ≤ margin)
    (tapes : Slot → STape Γm) (walker : PalPeg.GalilScaffoldPlace.Place)
    (gapBit : Bool) (hgap : gapBit = walker.gap)
    (a : Fin 3) (hread : PalPeg.GalilScaffoldPlace.read walker = some a)
    (stackTape : STape PalPeg.CloseoutCoreStep.Γc) (junk : List (Option (Fin 2)))
    (hstack : PalPeg.ConcreteLocalMachine.StackTape stackTape
      (walker.letters.map (fun letter => some letter) ++ junk))
    (hslot : tapes (placeSlot 1) = padLeft margin (mapTape encCell stackTape)) :
    copySymbol gapBit (fun tape => PalPeg.Local.readWin blankM K (tapesOf tapes tape)) = a := by
  obtain ⟨letter, rest, hletters⟩ : ∃ letter rest, walker.letters = letter :: rest := by
    cases hl : walker.letters with
    | nil =>
      exfalso
      rw [show PalPeg.GalilScaffoldPlace.read walker = none from by
        unfold PalPeg.GalilScaffoldPlace.read
        rw [hl]] at hread
      simp at hread
    | cons b bs => exact ⟨b, bs, rfl⟩
  have ha : (if walker.gap then (2 : Fin 3) else PalPeg.GalilScaffoldPlace.letter letter) = a := by
    have hr : PalPeg.GalilScaffoldPlace.read walker
        = some (if walker.gap then 2 else PalPeg.GalilScaffoldPlace.letter letter) := by
      unfold PalPeg.GalilScaffoldPlace.read
      rw [hletters]
    exact Option.some.inj (hr.symm.trans hread)
  unfold copySymbol
  rw [hgap, ← ha]
  by_cases hg : walker.gap = true
  · rw [if_pos hg, if_pos hg]
  · rw [if_neg hg, if_neg hg]
    have hmargin : K ≤ PalPeg.Local.pos (tapes (placeSlot 1)) := by
      rw [hslot, pos_padLeft]
      omega
    have hcentre : centreRead
        (fun tape => PalPeg.Local.readWin blankM K (tapesOf tapes tape)) (placeSlot 1)
        = encCell (PalPeg.CloseoutCoreEnc.cellSym (some letter)) := by
      rw [centreRead_of_margin tapes (placeSlot 1) hmargin, hslot]
      show encCell stackTape.focus = _
      rw [stackTape_focus stackTape _ hstack, hletters]
      rfl
    rw [hcentre, placeLetter_encCell]

/-- the action table of the fallback copy, once the window has said the copy still has work and
the walker still has a letter. -/
theorem copyActs_eq_copyOneBase {fppBound dpBound K : ℕ} (live : Bool)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (a : Fin 3)
    (hremains : remainsTest q.polarity ws = true)
    (hnotBlank : ¬ (centreRead ws (placeSlot 1) = blankM))
    (hsym : copySymbol (q.placeGap 1) ws = a) :
    copyActs live q ws = copyOneBase live (q.placeGap 1) q.polarity a ws := by
  unfold copyActs copyOneBase
  rw [if_pos hremains, if_neg hnotBlank]
  simp only [hsym]

/-- **what it takes for a tick to move no input head.**  `headOf` reads four things and nothing
else: the three input cursors and the chain.  A tick that leaves those four alone moves no head,
whatever else it does to the counters, the programs or the period tapes — which is the criterion
each still mode discharges, and the reason its branch has nothing to say about a head. -/
theorem headOf_congr_of_vm {x y : State GalilVM} (hleft : y.vm.left = x.vm.left)
    (hcentre : y.vm.center = x.vm.center) (hright : y.vm.right = x.vm.right)
    (hchain : y.vm.chain = x.vm.chain) (v : Fin 4) : headOf y v = headOf x v := by
  fin_cases v
  · show some y.vm.left = some x.vm.left
    rw [hleft]
  · show some y.vm.center = some x.vm.center
    rw [hcentre]
  · show some y.vm.right = some x.vm.right
    rw [hright]
  · show (match y.vm.chain with
      | .idle => none
      | .copy _ _ _ _ _ _ verifier => some verifier
      | .back _ _ _ _ verifier => some verifier
      | .watch w => some w.machine.verifier
      | .broken w => some w.machine.verifier) = _
    rw [hchain]
    rfl

/-- what a rewind does to each cursor: the left one steps left, and the centre with it when the
rewind is paired; the right cursor and the chain's verifier stand still. -/
def rewindHeadOps (pair : Bool) :
    Fin 4 → PalPeg.GalilScaffoldInputHead.PlaceHead → PalPeg.GalilScaffoldInputHead.PlaceHead
  | 0 => PalPeg.GalilScaffoldInputHead.left
  | 1 => if pair then PalPeg.GalilScaffoldInputHead.left else id
  | _ => id

/-- **and it leaves the chain's verifier where it was**, whether or not the abstraction names
it — which is what the encoding needs of the fourth cursor when the chain is idle. -/
theorem headOf_tickFun_rewind_chain (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind)
    (hnotFirst : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).atFirst
      x.vm = false) :
    headOf (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x) 3
      = headOf x 3 := by
  have hstep : PalPeg.GalilScaffoldTop.tickFun
      (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x
      = if x.ctl.pair then
          ⟨{x.ctl with pair := false},
            (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).rewindPair x.vm⟩
        else
          ⟨{x.ctl with pair := true},
            (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).rewindOne
              x.vm⟩ := by
    unfold PalPeg.GalilScaffoldTop.tickFun
    rw [hmode]
    dsimp only
    rw [if_neg (by rw [hnotFirst]; simp)]
  rw [hstep]
  cases hpair : x.ctl.pair <;> dsimp only <;> rfl

/-- **a tick of the rewind that is not yet at the first instruction does exactly that.**  Its two
frame functions say so: `rewindOne` steps the left cursor, `rewindPair` steps the centre with it,
and neither touches the right cursor or the chain. -/
theorem headOf_tickFun_rewind (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind)
    (hnotFirst : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).atFirst
      x.vm = false)
    (v : Fin 4) (head : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hhead : headOf x v = some head) :
    headOf (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x) v
      = some (rewindHeadOps x.ctl.pair v head) := by
  have hstep : PalPeg.GalilScaffoldTop.tickFun
      (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x
      = if x.ctl.pair then
          ⟨{x.ctl with pair := false},
            (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).rewindPair x.vm⟩
        else
          ⟨{x.ctl with pair := true},
            (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).rewindOne
              x.vm⟩ := by
    unfold PalPeg.GalilScaffoldTop.tickFun
    rw [hmode]
    dsimp only
    rw [if_neg (by rw [hnotFirst]; simp)]
  rw [hstep]
  cases hpair : x.ctl.pair <;> dsimp only <;> fin_cases v
  · show some (PalPeg.GalilScaffoldInputHead.left x.vm.left) = _
    rw [show head = x.vm.left from Option.some.inj hhead.symm]
    rfl
  · show some x.vm.center = _
    rw [show head = x.vm.center from Option.some.inj hhead.symm]
    rfl
  · show some x.vm.right = _
    rw [show head = x.vm.right from Option.some.inj hhead.symm]
    rfl
  · show (match x.vm.chain with
      | .idle => none
      | .copy _ _ _ _ _ _ verifier => some verifier
      | .back _ _ _ _ verifier => some verifier
      | .watch wm => some wm.machine.verifier
      | .broken wm => some wm.machine.verifier) = _
    exact hhead
  · show some (PalPeg.GalilScaffoldInputHead.left x.vm.left) = _
    rw [show head = x.vm.left from Option.some.inj hhead.symm]
    rfl
  · show some (PalPeg.GalilScaffoldInputHead.left x.vm.center) = _
    rw [show head = x.vm.center from Option.some.inj hhead.symm]
    rfl
  · show some x.vm.right = _
    rw [show head = x.vm.right from Option.some.inj hhead.symm]
    rfl
  · show (match x.vm.chain with
      | .idle => none
      | .copy _ _ _ _ _ _ verifier => some verifier
      | .back _ _ _ _ verifier => some verifier
      | .watch wm => some wm.machine.verifier
      | .broken wm => some wm.machine.verifier) = _
    exact hhead

/-- **a branch theorem, carried to the machine of twelve steps.**  Everything a mode whose branch
moves no head has to do is name its branch theorem and say that its tick moves no input head.
Written once here, so that each such mode is one line and not four.

The five modes that qualify are the end mark, the walk home, the back half of the choice, the
preparation program and the fallback copy: their branches name counters, program tapes and
period tapes, and nothing of a head. -/
theorem enc_ofBranchStep_stay {fppBound dpBound K : ℕ} (margin : ℕ) (entryQ : ℕ) (first : Fin 9)
    (hbound : 320 < fppBound) (hKq : entryQ + 3 ≤ K) (hK2 : 2 ≤ K) (hmargin : K ≤ margin)
    (rest : QPhys fppBound dpBound → Option (Fin 2) →
      (Fin tapeCountM → PalPeg.Local.Window Γm K) → Fin 4 →
      PalPeg.ConcreteLocalMachine.ViewCommand)
    (w : List (Fin 2)) (x y : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (input : Option (Fin 2)) (hslot0 : q.slot.val = 0)
    (hstay : modeCommands first rest q input
      (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) = stayCommands)
    (howed : ∀ v, (q.micro v).2.2.2 = 0) (hheadsSame : ∀ v, headOf y v = headOf x v)
    (henc : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T)
    (hbranch : Enc w margin y
      ((PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hKq)
          blankM (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep
          (physRule (dpBound := dpBound) entryQ first hbound hKq) blankM (q, tapesOf T) none).2
            (slotIndex i))) :
    Enc w margin y
      ((PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hKq hK2 rest) blankM
          (q, tapesOf T) input 12).1,
        fun i => (PalPeg.LocalStepFusion.idealRun
          (tickPhysRule entryQ first hbound hKq hK2 rest) blankM (q, tapesOf T) input 12).2
            (slotIndex i)) := by
  obtain ⟨hctl, htapes⟩ := enc_step_pieces margin entryQ first hbound hKq w y q T hbranch
  exact enc_afterStillTick margin entryQ first hbound hKq hK2 hmargin rest w x y q T input hslot0
    hstay howed hheadsSame henc hctl htapes

/-- **the five still modes are the case of that in which the mode alone decides the row.** -/
theorem enc_ofBranchStep_still {fppBound dpBound K : ℕ} (margin : ℕ) (entryQ : ℕ) (first : Fin 9)
    (hbound : 320 < fppBound) (hKq : entryQ + 3 ≤ K) (hK2 : 2 ≤ K) (hmargin : K ≤ margin)
    (rest : QPhys fppBound dpBound → Option (Fin 2) →
      (Fin tapeCountM → PalPeg.Local.Window Γm K) → Fin 4 →
      PalPeg.ConcreteLocalMachine.ViewCommand)
    (w : List (Fin 2)) (x y : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (input : Option (Fin 2)) (hslot0 : q.slot.val = 0)
    (hmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd
      ∨ q.ctl.mode = PalPeg.GalilScaffoldController.Mode.home
      ∨ q.ctl.mode = PalPeg.GalilScaffoldController.Mode.choose
      ∨ q.ctl.mode = PalPeg.GalilScaffoldController.Mode.fpp
      ∨ q.ctl.mode = PalPeg.GalilScaffoldController.Mode.copy)
    (howed : ∀ v, (q.micro v).2.2.2 = 0) (hheadsSame : ∀ v, headOf y v = headOf x v)
    (henc : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T)
    (hbranch : Enc w margin y
      ((PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hKq)
          blankM (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep
          (physRule (dpBound := dpBound) entryQ first hbound hKq) blankM (q, tapesOf T) none).2
            (slotIndex i))) :
    Enc w margin y
      ((PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hKq hK2 rest) blankM
          (q, tapesOf T) input 12).1,
        fun i => (PalPeg.LocalStepFusion.idealRun
          (tickPhysRule entryQ first hbound hKq hK2 rest) blankM (q, tapesOf T) input 12).2
            (slotIndex i)) := by
  exact enc_ofBranchStep_stay margin entryQ first hbound hKq hK2 hmargin rest w x y q T input
    hslot0 (modeCommands_eq_stay first rest q input _ hmode) howed hheadsSame henc hbranch

/-- **a tick of any of the five still modes moves no input head.**  Their frame functions all
have the shape `{s with fpp := …}`: the end mark, the walk home, the back half of the choice, the
preparation program and the fallback copy work inside the preparation's own state, so the three
input cursors and the chain are where they were.

The choice has a second branch, the one that starts a chain, and that one is excluded by the
guard — it is the branch that moves a cursor, and it is not among the five. -/
theorem headOf_tickFun_still (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd
      ∨ x.ctl.mode = PalPeg.GalilScaffoldController.Mode.home
      ∨ x.ctl.mode = PalPeg.GalilScaffoldController.Mode.fpp
      ∨ x.ctl.mode = PalPeg.GalilScaffoldController.Mode.copy)
    (v : Fin 4) :
    headOf (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x) v
      = headOf x v := by
  refine headOf_congr_of_vm ?_ ?_ ?_ ?_ v <;>
    (unfold PalPeg.GalilScaffoldTop.tickFun
     rcases hmode with h | h | h | h <;> rw [h] <;> dsimp only <;> split <;> rfl)

/-- **and so does the back half of the choice**, the branch that keeps looking. -/
theorem headOf_tickFun_chooseBack (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.choose)
    (hkeep : (x.ctl.odd &&
      (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).markSet x.vm)
        = false)
    (v : Fin 4) :
    headOf (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x) v
      = headOf x v := by
  refine headOf_congr_of_vm ?_ ?_ ?_ ?_ v <;>
    (unfold PalPeg.GalilScaffoldTop.tickFun
     rw [hmode]
     dsimp only
     rw [if_neg (by rw [hkeep]; simp)]
     rfl)

/-- **a tick of the fallback copy that still has work, rule and encoding together.**  Everything
the rule needs is in the window: whether the copy still has work, whether the walker still has a
letter, which letter that is, and whether the work counter can be decremented without crossing
zero. -/
theorem copy_one_of_rule {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (R : PalPeg.CloseoutCoreEnc12.ActRule (Fin 2) (QPhys fppBound dpBound) Γm tapeCountM K)
    (hnq : R.nq q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = copyNext q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)))
    (hacts : R.acts q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = withErase q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (copyActs q.fppLive q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))))
    (hK1 : 1 ≤ K) (hK : K ≤ margin)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.copy)
    (hremains : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).remainingPos x.vm
      = true)
    (a : Fin 3) (hread : PalPeg.GalilScaffoldPlace.read x.vm.fpp.walker = some a)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2
          (slotIndex i)) := by
  obtain ⟨stackTape, junk, hsealed, hjunk, hstack, hslotPlace⟩ :=
    henc.2.places 1 x.vm.fpp.walker rfl
  have hgapBit : q.placeGap 1 = x.vm.fpp.walker.gap := henc.1.placeGap 1 x.vm.fpp.walker rfl
  have hsym := copySymbol_eq hK T x.vm.fpp.walker (q.placeGap 1) hgapBit a hread stackTape junk
    hstack hslotPlace
  have hbit : remainsTest q.polarity
      (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) = true := by
    rw [remainsTest_eq henc.2 hK1 hK centre place entry entryQ first w, hremains]
  have hnotBlank : ¬ (centreRead
      (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) (placeSlot 1) = blankM) := by
    intro hblank
    have hnone := (placeRead_isNone_iff_centre henc.2 hK 1 x.vm.fpp.walker rfl).mpr hblank
    rw [hread] at hnone
    simp at hnone
  have hq : (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).1
      = {q with placeGap := Function.update q.placeGap 1 (!q.placeGap 1), polarity := Function.update q.polarity 9 (workPositive q.polarity (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)))} := by
    show R.nq q none _ = _
    rw [hnq]
    unfold copyNext
    rw [if_pos hbit, if_neg hnotBlank]
  have hacts' : R.acts q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = withErase q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (copyOneBase q.fppLive (q.placeGap 1) q.polarity a
            (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))) := by
    rw [hacts]
    congr 1
    exact copyActs_eq_copyOneBase q.fppLive q _ a hbit hnotBlank hsym
  have hstep := idealStep_withErase R q T q.fppLive _ hacts'
  have hidleOff : ∀ k : Fin 9,
      copyOneBase q.fppLive (q.placeGap 1) q.polarity a
          (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (slotIndex (progSlotOf (!q.fppLive) k)) = [] :=
    fun k => copyOneBase_off q.fppLive (q.placeGap 1) q.polarity a _
      (progSlotOf (!q.fppLive) k) (fun j => (progSlotOf_ne_flip q.fppLive j k).symm)
      (by simpa using (progSlot_ne_counterSlot (!q.fppLive) k 9))
      (by simpa using (progSlot_ne_placeSlot (!q.fppLive) k 1))
  rw [hq]
  exact copy_one margin K centre place entry entryQ first w F delay x q T
    (fun slot => (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2 (slotIndex slot))
    a hK1 hK hmode hremains hread henc
    (by rw [hstep _ (fun k => progSlotOf_ne_flip q.fppLive 7 k), copyOneBase_prog])
    (by
      rw [hstep (counterSlot 9)
        (fun k => (progSlot_ne_counterSlot (!q.fppLive) k 9).symm), copyOneBase_counter])
    (by
      rw [hstep (placeSlot 1)
        (fun k => (progSlot_ne_placeSlot (!q.fppLive) k 1).symm), copyOneBase_place])
    (fun j hj => by
      rw [hstep _ (fun k => progSlotOf_ne_flip q.fppLive j k),
        copyOneBase_progOther q.fppLive (q.placeGap 1) q.polarity a _ j hj]
      rfl)
    (fun slot hprog hcounter hplace hidle => by
      rw [hstep slot hidle,
        copyOneBase_off q.fppLive (q.placeGap 1) q.polarity a _ slot hprog hcounter hplace]
      rfl)
    (fun k => idle_shape_after_erase margin hK1 (by omega) R q T q.fppLive _ hacts'
      hidleOff henc.2.idleShape k)

/-- **the last tick of the fallback copy, rule and encoding together.**  The window says the
copy has nothing left to move, so the rule stamps the end mark where the head stands and reads
off the cursor to set the final-stage flag. -/
theorem copy_end_of_rule {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (R : PalPeg.CloseoutCoreEnc12.ActRule (Fin 2) (QPhys fppBound dpBound) Γm tapeCountM K)
    (hnq : R.nq q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = copyNext q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)))
    (hacts : R.acts q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = withErase q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (copyActs q.fppLive q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))))
    (hK1 : 1 ≤ K) (hK : K ≤ margin)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.copy)
    (hdone : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).remainingPos x.vm
      = false)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2
          (slotIndex i)) := by
  have hwalker := placeRead_isNone_iff_centre henc.2 hK 1 x.vm.fpp.walker rfl
  have hbit : remainsTest q.polarity
      (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) = false := by
    rw [remainsTest_eq henc.2 hK1 hK centre place entry entryQ first w, hdone]
  have hq : (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).1
      = {q with ctl := {q.ctl with mode := PalPeg.GalilScaffoldController.Mode.home}, fppMode := PalPeg.GalilScaffoldChainInputSupply.FppControl.Mode.home, fppFinalStage := decide (centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) (placeSlot 1) = blankM)} := by
    show R.nq q none _ = _
    rw [hnq]
    unfold copyNext
    rw [if_neg (by simp [hbit])]
  have hacts' : R.acts q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = withErase q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (actsAt (slotIndex (progSlot q.fppLive 7))
            [some (encProg 5, (.stay : PalPeg.CloseoutCoreEnc12.MoveC))]) := by
    rw [hacts]
    congr 1
    unfold copyActs
    rw [if_neg (by simp [hbit])]
  obtain ⟨hmoved, hkept⟩ := idealStep_atLiveSlot R q T q.fppLive 7 _ hacts'
  rw [hq]
  exact copy_end margin centre place entry entryQ first w F delay x q T
    (fun slot => (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2 (slotIndex slot))
    _ hmode hdone
    (by rw [Bool.eq_iff_iff, hwalker]; simp)
    henc hmoved hkept
    (idle_shape_after_erase margin hK1 (by omega) R q T q.fppLive _ hacts'
      (offLive_offIdle (actsAt_off_live q.fppLive 7 _)) henc.2.idleShape)

theorem physRule_nq_copy {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9) (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hm : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.copy) :
    (physRule (dpBound := dpBound) entryQ first hbound hK).nq q none ws = copyNext q ws := by
  show ruleNext entryQ first hbound q ws = _
  unfold ruleNext
  rw [hm]

theorem physRule_acts_copy {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9) (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hm : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.copy) :
    (physRule (dpBound := dpBound) entryQ first hbound hK).acts q none ws
      = withErase q.fppLive ws (copyActs q.fppLive q ws) := by
  show ruleActs entryQ first q ws = _
  unfold ruleActs
  rw [hm]

theorem physRule_nq_fpp {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9) (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hm : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.fpp) :
    (physRule (dpBound := dpBound) entryQ first hbound hK).nq q none ws = fppNext entryQ q ws := by
  show ruleNext entryQ first hbound q ws = _
  unfold ruleNext
  rw [hm]

theorem physRule_acts_fpp {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9) (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hm : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.fpp) :
    (physRule (dpBound := dpBound) entryQ first hbound hK).acts q none ws
      = withErase q.fppLive ws
          (fppBranchActs PalPeg.GalilFppMarkedCode.code entryQ q.fppLive first
            (pcOf q) q.fppDone ws) := by
  show ruleActs entryQ first q ws = _
  unfold ruleActs
  rw [hm]

/-- **the mark walk of the machine itself.**  The same statement as `markEnd_forward_of_rule`,
with its two hypotheses about the rule discharged: this is the rule the machine runs, not one
assumed to exist. -/
theorem physRule_markEnd_forward {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K)
    (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i))
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd)
    (hnotEnd : (x.vm.fpp.program.config.tapes 8).focus ≠ 5)
    (hnotMark : (T (progSlot q.fppLive 8)).focus ≠ encProg 5)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hK) blankM
          (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hK) blankM
          (q, tapesOf T) none).2 (slotIndex i)) :=
  markEnd_forward_of_rule margin centre place entry entryQ first w F delay x q T
    (physRule entryQ first hbound hK)
    (physRule_nq_markEnd entryQ first hbound hK q _ hqmode) (physRule_acts_markEnd entryQ first hbound hK q _ hqmode)
    hmargin hK1 hKn hmode hnotEnd hnotMark henc

theorem physRule_nq_rewind {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9) (hbound : 320 < fppBound)
    (hK : entryQ + 3 ≤ K) (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hm : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind) :
    (physRule (dpBound := dpBound) entryQ first hbound hK).nq q none ws = rewindNext first hbound q ws := by
  show ruleNext entryQ first hbound q ws = _
  unfold ruleNext
  rw [hm]

theorem physRule_acts_rewind {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9) (hbound : 320 < fppBound)
    (hK : entryQ + 3 ≤ K) (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hm : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind) :
    (physRule (dpBound := dpBound) entryQ first hbound hK).acts q none ws
      = withErase q.fppLive ws (rewindActs first q.fppLive q ws) := by
  show ruleActs entryQ first q ws = _
  unfold ruleActs
  rw [hm]

/-- **the wipe of the machine itself.**  The rule is the one the machine runs, and it names no
action at all; the nine tapes the abstraction blanks are the nine the machine stops looking at,
and the half that becomes live is the one the background erasure kept blank. -/
theorem physRule_rewind_fppReset {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K)
    (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i))
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind)
    (hatFirst : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).atFirst
      x.vm = true)
    (hatMark : (T (progSlot q.fppLive 8)).focus = encProg first)
    (henc : Enc w margin x (q, T))
    (hidle : ∀ i : Fin 9, T (progSlotOf (!q.fppLive) i)
      = padLeft margin (mapTape encProg (encTape PalPeg.GalilScaffoldTape.reset))) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hK) blankM
          (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hK)
          blankM (q, tapesOf T) none).2 (slotIndex i)) := by
  have hread : centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot q.fppLive 8) = (T (progSlot q.fppLive 8)).focus :=
    centreRead_of_margin T (progSlot q.fppLive 8) (hmargin _)
  have hq : (PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hK)
        blankM (q, tapesOf T) none).1
      = {q with ctl := {q.ctl with mode := PalPeg.GalilScaffoldController.Mode.replayStart}, fppPc := some ⟨320, hbound⟩, fppDone := true, fppLive := !q.fppLive} := by
    show (physRule (dpBound := dpBound) entryQ first hbound hK).nq q none _ = _
    rw [physRule_nq_rewind entryQ first hbound hK q _ hqmode]
    unfold rewindNext
    rw [hread, if_pos hatMark]
  have hsame : (fun i => (PalPeg.LocalStepFusion.idealStep
      (physRule (dpBound := dpBound) entryQ first hbound hK) blankM (q, tapesOf T) none).2
        (slotIndex i)) = T := by
    funext i
    rw [idealStep_tapes, physRule_acts_rewind entryQ first hbound hK q _ hqmode, tapesOf_apply]
    by_cases hid : ∃ k : Fin 9, i = progSlotOf (!q.fppLive) k
    · obtain ⟨k, hk⟩ := hid
      subst hk
      rw [show withErase q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (rewindActs first q.fppLive q
            (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)))
          (slotIndex (progSlotOf (!q.fppLive) k))
          = eraseOf q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
              (slotIndex (progSlotOf (!q.fppLive) k)) from by
        unfold withErase
        rw [rewindActs_atFirst first q.fppLive q _ (by rw [hread]; exact hatMark), List.nil_append]]
      show PalPeg.CloseoutCoreEnc12.actList blankM _
        (eraseOf q.fppLive _ (slotIndex (progSlotOf (!q.fppLive) k))) = _
      rw [show eraseOf q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (slotIndex (progSlotOf (!q.fppLive) k)) = [] from by
        unfold eraseOf eraseAct
        rw [if_pos ⟨k, rfl⟩, if_pos ?_]
        show PalPeg.Local.readWin blankM K
          (tapesOf T (slotIndex (progSlotOf (!q.fppLive) k))) ⟨K - 1, by omega⟩ = bottomM
        rw [tapesOf_apply, hidle k, window_below margin K
          (mapTape encProg (encTape PalPeg.GalilScaffoldTape.reset)) hK1 hKn]
        rfl]
      rfl
    · rw [withErase_at_other q.fppLive _ _ i (fun k hk => hid ⟨k, hk⟩),
        rewindActs_atFirst first q.fppLive q _ (by rw [hread]; exact hatMark)]
      rfl
  rw [hq, hsame]
  exact rewind_fppReset margin centre place entry entryQ first w F delay x q T hbound hmode
    hatFirst henc hidle

theorem physRule_nq_rewind_one {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9)
    (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K) (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hm : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind)
    (hnotMark : centreRead ws (progSlot q.fppLive 8) ≠ encProg first)
    (hpair : q.ctl.pair = false) :
    (physRule (dpBound := dpBound) entryQ first hbound hK).nq q none ws = rewindOneNext q ws := by
  rw [physRule_nq_rewind entryQ first hbound hK q ws hm]
  unfold rewindNext
  rw [if_neg hnotMark, if_neg (by simp [hpair])]

theorem physRule_acts_rewind_one {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9)
    (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K) (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hm : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind)
    (hnotMark : centreRead ws (progSlot q.fppLive 8) ≠ encProg first)
    (hpair : q.ctl.pair = false) :
    (physRule (dpBound := dpBound) entryQ first hbound hK).acts q none ws
      = withErase q.fppLive ws (rewindOneActs q.fppLive q ws) := by
  rw [physRule_acts_rewind entryQ first hbound hK q ws hm]
  congr 1
  unfold rewindActs
  rw [if_neg hnotMark, if_neg (by simp [hpair])]

theorem physRule_nq_rewind_pair {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9)
    (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K) (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hm : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind)
    (hnotMark : centreRead ws (progSlot q.fppLive 8) ≠ encProg first)
    (hpair : q.ctl.pair = true) :
    (physRule (dpBound := dpBound) entryQ first hbound hK).nq q none ws = rewindPairNext q ws := by
  rw [physRule_nq_rewind entryQ first hbound hK q ws hm]
  unfold rewindNext
  rw [if_neg hnotMark, if_pos (by simp [hpair])]

theorem physRule_acts_rewind_pair {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9)
    (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K) (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hm : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind)
    (hnotMark : centreRead ws (progSlot q.fppLive 8) ≠ encProg first)
    (hpair : q.ctl.pair = true) :
    (physRule (dpBound := dpBound) entryQ first hbound hK).acts q none ws
      = withErase q.fppLive ws (rewindPairActs q.fppLive q ws) := by
  rw [physRule_acts_rewind entryQ first hbound hK q ws hm]
  congr 1
  unfold rewindActs
  rw [if_neg hnotMark, if_pos (by simp [hpair])]

/-- **the single step of the rewind, of the machine itself.** -/
theorem physRule_rewind_one {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (hbound : 320 < fppBound) (hKb : entryQ + 3 ≤ K)
    (hK1 : 1 ≤ K) (hK : K ≤ margin) (hmargin2 : 2 ≤ margin)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind)
    (hnotFirst : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).atFirst x.vm
      = false)
    (hqpair : q.ctl.pair = false) (hpair : x.ctl.pair = false)
    (hnotMark : centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot q.fppLive 8) ≠ encProg first)
    (hfloor : (x.vm.fpp.program.config.tapes 8).left ≠ [])
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hKb) blankM
          (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hKb)
          blankM (q, tapesOf T) none).2 (slotIndex i)) :=
  rewind_one_of_rule margin centre place entry entryQ first w F delay x q T
    (physRule entryQ first hbound hKb)
    (physRule_nq_rewind_one entryQ first hbound hKb q _ hqmode hnotMark hqpair)
    (physRule_acts_rewind_one entryQ first hbound hKb q _ hqmode hnotMark hqpair)
    hK1 hK hmargin2 hmode hnotFirst hpair hfloor henc

/-- **the paired step of the rewind, of the machine itself.** -/
theorem physRule_rewind_pair {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (hbound : 320 < fppBound) (hKb : entryQ + 3 ≤ K)
    (hK1 : 1 ≤ K) (hK : K ≤ margin) (hmargin2 : 2 ≤ margin)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind)
    (hnotFirst : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).atFirst x.vm
      = false)
    (hqpair : q.ctl.pair = true) (hpair : x.ctl.pair = true)
    (hnotMark : centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot q.fppLive 8) ≠ encProg first)
    (hfloor : (x.vm.fpp.program.config.tapes 8).left ≠ [])
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hKb) blankM
          (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hKb)
          blankM (q, tapesOf T) none).2 (slotIndex i)) :=
  rewind_pair_of_rule margin centre place entry entryQ first w F delay x q T
    (physRule entryQ first hbound hKb)
    (physRule_nq_rewind_pair entryQ first hbound hKb q _ hqmode hnotMark hqpair)
    (physRule_acts_rewind_pair entryQ first hbound hKb q _ hqmode hnotMark hqpair)
    hK1 hK hmargin2 hmode hnotFirst hpair hfloor henc

/-- **the mark walk back, of the machine itself.**  The step that finds the end mark, with
nothing assumed about the rule. -/
theorem physRule_markEnd_back {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K)
    (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i))
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd)
    (hatEnd : (x.vm.fpp.program.config.tapes 8).focus = 5)
    (hfloor : (x.vm.fpp.program.config.tapes 8).left ≠ [])
    (hatMark : (T (progSlot q.fppLive 8)).focus = encProg 5)
    (hnotFloor : belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot q.fppLive 8) ≠ bottomM)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hK) blankM
          (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hK)
          blankM (q, tapesOf T) none).2 (slotIndex i)) :=
  markEnd_back_of_rule margin centre place entry entryQ first w F delay x q T
    (physRule entryQ first hbound hK)
    (physRule_nq_markEnd entryQ first hbound hK q _ hqmode) (physRule_acts_markEnd entryQ first hbound hK q _ hqmode)
    hmargin hK1 hKn hmode hatEnd hfloor hatMark hnotFloor henc

/-- **the walk home, of the machine itself.** -/
theorem physRule_home_step {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K)
    (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i))
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.home)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.home)
    (hnotLeft : (x.vm.fpp.program.config.tapes 7).focus ≠ 4)
    (hfloor : (x.vm.fpp.program.config.tapes 7).left ≠ [])
    (hnotMark : (T (progSlot q.fppLive 7)).focus ≠ encProg 4)
    (hnotFloor : belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot q.fppLive 7) ≠ bottomM)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hK) blankM
          (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hK)
          blankM (q, tapesOf T) none).2 (slotIndex i)) :=
  home_step_of_rule margin centre place entry entryQ first w F delay x q T
    (physRule entryQ first hbound hK) hbound
    (physRule_nq_home entryQ first hbound hK q _ hqmode) (physRule_acts_home entryQ first hbound hK q _ hqmode)
    hmargin hK1 hKn hmode hnotLeft hfloor hnotMark hnotFloor henc

/-- **the start of the preparation program, of the machine itself.** -/
theorem physRule_home_fppStart {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K)
    (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i))
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.home)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.home)
    (hatLeft : (x.vm.fpp.program.config.tapes 7).focus = 4)
    (hatMark : (T (progSlot q.fppLive 7)).focus = encProg 4)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hK) blankM
          (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hK)
          blankM (q, tapesOf T) none).2 (slotIndex i)) :=
  home_fppStart_of_rule margin centre place entry entryQ first w F delay x q T
    (physRule entryQ first hbound hK) hbound
    (physRule_nq_home entryQ first hbound hK q _ hqmode) (physRule_acts_home entryQ first hbound hK q _ hqmode)
    hmargin hK1 hKn hmode hatLeft hatMark henc

/-- **a tick of the fallback copy that still has work, of the machine itself.** -/
theorem physRule_copy_one {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (hbound : 320 < fppBound) (hKb : entryQ + 3 ≤ K)
    (hK1 : 1 ≤ K) (hK : K ≤ margin)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.copy)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.copy)
    (hremains : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).remainingPos x.vm
      = true)
    (a : Fin 3) (hread : PalPeg.GalilScaffoldPlace.read x.vm.fpp.walker = some a)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hKb) blankM
          (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hKb)
          blankM (q, tapesOf T) none).2 (slotIndex i)) :=
  copy_one_of_rule margin centre place entry entryQ first w F delay x q T
    (physRule entryQ first hbound hKb)
    (physRule_nq_copy entryQ first hbound hKb q _ hqmode)
    (physRule_acts_copy entryQ first hbound hKb q _ hqmode)
    hK1 hK hmode hremains a hread henc


/-- **a tick of the fallback copy, on the machine of twelve steps.**  The branch was already
proved of one step of the one-step rule; this is the same branch on the machine as it really
runs, with the head side coming from the view layer and everything else from the branch.

This is the first mode carried all the way through the division of labour, and the four other
still modes are the same four lines with their own branch theorem in place of this one. -/
theorem copy_one_of_tick {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (rest : QPhys fppBound dpBound → Option (Fin 2) →
      (Fin tapeCountM → PalPeg.Local.Window Γm K) → Fin 4 →
      PalPeg.ConcreteLocalMachine.ViewCommand)
    (input : Option (Fin 2))
    (hbound : 320 < fppBound) (hKb : entryQ + 3 ≤ K) (hK2 : 2 ≤ K) (hK1 : 1 ≤ K)
    (hK : K ≤ margin) (hslot0 : q.slot.val = 0) (howed : ∀ v, (q.micro v).2.2.2 = 0)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.copy)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.copy)
    (hremains : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).remainingPos
      x.vm = true)
    (a : Fin 3) (hread : PalPeg.GalilScaffoldPlace.read x.vm.fpp.walker = some a)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hKb hK2 rest) blankM
          (q, tapesOf T) input 12).1,
        fun i => (PalPeg.LocalStepFusion.idealRun
          (tickPhysRule entryQ first hbound hKb hK2 rest) blankM (q, tapesOf T) input 12).2
            (slotIndex i)) := by
  exact enc_ofBranchStep_still margin entryQ first hbound hKb hK2 hK rest w x
    (PalPeg.GalilScaffoldTop.tickFun
      (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x) q T input
    hslot0 (Or.inr (Or.inr (Or.inr (Or.inr hqmode)))) howed
    (headOf_tickFun_still centre place entry entryQ first w F delay x
      (Or.inr (Or.inr (Or.inr hmode))))
    henc.2
    (physRule_copy_one margin centre place entry entryQ first w F delay x q T hbound hKb hK1 hK
      hqmode hmode hremains a hread henc)


/-- **the last tick of the fallback copy, of the machine itself.** -/
theorem physRule_copy_end {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (hbound : 320 < fppBound) (hKb : entryQ + 3 ≤ K)
    (hK1 : 1 ≤ K) (hK : K ≤ margin)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.copy)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.copy)
    (hdone : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).remainingPos x.vm
      = false)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hKb) blankM
          (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hKb)
          blankM (q, tapesOf T) none).2 (slotIndex i)) :=
  copy_end_of_rule margin centre place entry entryQ first w F delay x q T
    (physRule entryQ first hbound hKb)
    (physRule_nq_copy entryQ first hbound hKb q _ hqmode)
    (physRule_acts_copy entryQ first hbound hKb q _ hqmode)
    hK1 hK hmode hdone henc

/-- **the parity walk, of the machine itself.** -/
theorem physRule_choose_back {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K)
    (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i))
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.choose)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.choose)
    (hkeep : (x.ctl.odd && (decide ((x.vm.fpp.program.config.tapes 8).focus = 8)
        || decide ((x.vm.fpp.program.config.tapes 8).focus = first))) = false)
    (hfloor : (x.vm.fpp.program.config.tapes 8).left ≠ [])
    (hnotFloor : belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot q.fppLive 8) ≠ bottomM)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hK) blankM
          (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hK)
          blankM (q, tapesOf T) none).2 (slotIndex i)) :=
  choose_back_of_rule margin centre place entry entryQ first w F delay x q T
    (physRule entryQ first hbound hK)
    (physRule_nq_choose entryQ first hbound hK q _ hqmode) (physRule_acts_choose entryQ first hbound hK q _ hqmode)
    hmargin hK1 hKn hmode hkeep hfloor hnotFloor henc

/-- **the mark walk back on the floor, of the machine itself.** -/
theorem physRule_markEnd_back_atFloor {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K)
    (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i))
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd)
    (hatEnd : (x.vm.fpp.program.config.tapes 8).focus = 5)
    (hfloor : (x.vm.fpp.program.config.tapes 8).left = [])
    (hatMark : (T (progSlot q.fppLive 8)).focus = encProg 5)
    (hisFloor : belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot q.fppLive 8) = bottomM)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hK) blankM
          (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hK)
          blankM (q, tapesOf T) none).2 (slotIndex i)) :=
  markEnd_back_of_rule_atFloor margin centre place entry entryQ first w F delay x q T
    (physRule entryQ first hbound hK)
    (physRule_nq_markEnd entryQ first hbound hK q _ hqmode) (physRule_acts_markEnd entryQ first hbound hK q _ hqmode)
    hK1 hKn hmode hatEnd hfloor hatMark hmargin hisFloor henc

/-- **the walk home on the floor, of the machine itself.** -/
theorem physRule_home_step_atFloor {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K)
    (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i))
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.home)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.home)
    (hnotLeft : (x.vm.fpp.program.config.tapes 7).focus ≠ 4)
    (hfloor : (x.vm.fpp.program.config.tapes 7).left = [])
    (hnotMark : (T (progSlot q.fppLive 7)).focus ≠ encProg 4)
    (hisFloor : belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot q.fppLive 7) = bottomM)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hK) blankM
          (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hK)
          blankM (q, tapesOf T) none).2 (slotIndex i)) :=
  home_step_of_rule_atFloor margin centre place entry entryQ first w F delay x q T
    (physRule entryQ first hbound hK) hbound
    (physRule_nq_home entryQ first hbound hK q _ hqmode) (physRule_acts_home entryQ first hbound hK q _ hqmode)
    hK1 hKn hmode hnotLeft hfloor hnotMark hmargin hisFloor henc

/-- **the parity walk on the floor, of the machine itself.** -/
theorem physRule_choose_back_atFloor {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K)
    (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i))
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.choose)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.choose)
    (hkeep : (x.ctl.odd && (decide ((x.vm.fpp.program.config.tapes 8).focus = 8)
        || decide ((x.vm.fpp.program.config.tapes 8).focus = first))) = false)
    (hfloor : (x.vm.fpp.program.config.tapes 8).left = [])
    (hisFloor : belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot q.fppLive 8) = bottomM)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hK) blankM
          (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hK)
          blankM (q, tapesOf T) none).2 (slotIndex i)) :=
  choose_back_of_rule_atFloor margin centre place entry entryQ first w F delay x q T
    (physRule entryQ first hbound hK)
    (physRule_nq_choose entryQ first hbound hK q _ hqmode) (physRule_acts_choose entryQ first hbound hK q _ hqmode)
    hK1 hKn hmode hkeep hfloor hmargin hisFloor henc

/-! ### a whole mode at once

With the two readings identified, a mode's branches can be put together into one statement that
mentions only the abstract state: whatever the marks tape holds and wherever its head stands, the
machine's own rule carries the encoding across the tick. -/

/-- **the mark walk, whatever it finds.**  The first mode of the controller proved entire against
the rule the machine runs. -/
theorem physRule_markEnd {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K)
    (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i))
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hK) blankM
          (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hK)
          blankM (q, tapesOf T) none).2 (slotIndex i)) := by
  by_cases hend : (x.vm.fpp.program.config.tapes 8).focus = 5
  · by_cases hfloor : (x.vm.fpp.program.config.tapes 8).left = []
    · exact physRule_markEnd_back_atFloor margin centre place entry entryQ first w F delay x q T
        hbound hK hmargin hK1 hKn hqmode hmode hend hfloor
        ((focus_iff_of_enc (K := K) henc 8 5).mpr hend)
        ((floor_iff_of_enc henc hK1 hKn 8).mpr hfloor) henc
    · exact physRule_markEnd_back margin centre place entry entryQ first w F delay x q T
        hbound hK hmargin hK1 hKn hqmode hmode hend hfloor
        ((focus_iff_of_enc (K := K) henc 8 5).mpr hend)
        (fun h => hfloor ((floor_iff_of_enc henc hK1 hKn 8).mp h)) henc
  · exact physRule_markEnd_forward margin centre place entry entryQ first w F delay x q T
      hbound hK hmargin hK1 hKn hqmode hmode hend
      (fun h => hend ((focus_iff_of_enc (K := K) henc 8 5).mp h)) henc

/-- **the walk home, wherever it stands.**  Either the head is on the left mark and the
preparation program starts, or the tape walks one cell left, or it is already on its own first
cell and nothing moves. -/
theorem physRule_home {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K)
    (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i))
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.home)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.home)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hK) blankM
          (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hK)
          blankM (q, tapesOf T) none).2 (slotIndex i)) := by
  by_cases hleft : (x.vm.fpp.program.config.tapes 7).focus = 4
  · exact physRule_home_fppStart margin centre place entry entryQ first w F delay x q T
      hbound hK hmargin hK1 hKn hqmode hmode hleft
      ((focus_iff_of_enc (K := K) henc 7 4).mpr hleft) henc
  · by_cases hfloor : (x.vm.fpp.program.config.tapes 7).left = []
    · exact physRule_home_step_atFloor margin centre place entry entryQ first w F delay x q T
        hbound hK hmargin hK1 hKn hqmode hmode hleft hfloor
        (fun h => hleft ((focus_iff_of_enc (K := K) henc 7 4).mp h))
        ((floor_iff_of_enc henc hK1 hKn 7).mpr hfloor) henc
    · exact physRule_home_step margin centre place entry entryQ first w F delay x q T
        hbound hK hmargin hK1 hKn hqmode hmode hleft hfloor
        (fun h => hleft ((focus_iff_of_enc (K := K) henc 7 4).mp h))
        (fun h => hfloor ((floor_iff_of_enc henc hK1 hKn 7).mp h)) henc

/-- **the parity walk, wherever it stands.**  The branch that stops looking moves a cursor, so it
is not yet here; this is the one that keeps looking, on a cell or on the floor. -/
theorem physRule_choose {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K)
    (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i))
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.choose)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.choose)
    (hkeep : (x.ctl.odd && (decide ((x.vm.fpp.program.config.tapes 8).focus = 8)
        || decide ((x.vm.fpp.program.config.tapes 8).focus = first))) = false)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hK) blankM
          (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hK)
          blankM (q, tapesOf T) none).2 (slotIndex i)) := by
  by_cases hfloor : (x.vm.fpp.program.config.tapes 8).left = []
  · exact physRule_choose_back_atFloor margin centre place entry entryQ first w F delay x q T
      hbound hK hmargin hK1 hKn hqmode hmode hkeep hfloor
      ((floor_iff_of_enc henc hK1 hKn 8).mpr hfloor) henc
  · exact physRule_choose_back margin centre place entry entryQ first w F delay x q T
      hbound hK hmargin hK1 hKn hqmode hmode hkeep hfloor
      (fun h => hfloor ((floor_iff_of_enc henc hK1 hKn 8).mp h)) henc

/-! ### how far two program machines have to agree

A call consults the halting bit, the program counter and the symbols under the heads.  A quantum
of `n` calls can walk a head `n` cells, so `n` is how far the tapes have to agree for the whole
quantum to run the same way. -/

/-- two program machines agreeing to radius `n`. -/
structure MachineAgree (n : ℕ) (m m' : PalPeg.GalilScaffoldControl.Machine 9) : Prop where
  done : m.done = m'.done
  pc : m.config.pc = m'.config.pc
  margin : ∀ t : Fin 9, n ≤ PalPeg.Local.pos (encTape (m.config.tapes t))
  margin' : ∀ t : Fin 9, n ≤ PalPeg.Local.pos (encTape (m'.config.tapes t))
  window : ∀ t : Fin 9, PalPeg.Local.readWin (6 : Fin 9) n (encTape (m.config.tapes t))
    = PalPeg.Local.readWin (6 : Fin 9) n (encTape (m'.config.tapes t))

/-- **agreeing at all means agreeing under the heads.** -/
theorem machineAgree_focus {n : ℕ} {m m' : PalPeg.GalilScaffoldControl.Machine 9}
    (h : MachineAgree n m m') (t : Fin 9) :
    (m.config.tapes t).focus = (m'.config.tapes t).focus := by
  have hm := h.margin t
  have hm' := h.margin' t
  have hw := congrFun (h.window t) ⟨n, by omega⟩
  rw [PalPeg.Local.readWin_eq, PalPeg.Local.readWin_eq] at hw
  rw [show PalPeg.Local.pos (encTape (m.config.tapes t)) - n + n
      = PalPeg.Local.pos (encTape (m.config.tapes t)) from by omega] at hw
  rw [show PalPeg.Local.pos (encTape (m'.config.tapes t)) - n + n
      = PalPeg.Local.pos (encTape (m'.config.tapes t)) from by omega] at hw
  rwa [PalPeg.Local.rd_pos, PalPeg.Local.rd_pos] at hw

/-- **so the two name the same action and leave with the same control.** -/
theorem progActOf_of_agree {n : ℕ} (code : List (Instruction 9))
    {m m' : PalPeg.GalilScaffoldControl.Machine 9} (h : MachineAgree n m m') (i : Fin 9) :
    progActOf code m i = progActOf code m' i :=
  progActOf_congr code m m' h.done h.pc (machineAgree_focus h) i

theorem tickFun_control_of_agree {n : ℕ} (code : List (Instruction 9))
    {m m' : PalPeg.GalilScaffoldControl.Machine 9} (h : MachineAgree n m m') :
    (PalPeg.ProgramFunction.tickFun code true m).config.pc
        = (PalPeg.ProgramFunction.tickFun code true m').config.pc
      ∧ (PalPeg.ProgramFunction.tickFun code true m).done
        = (PalPeg.ProgramFunction.tickFun code true m').done :=
  tickFun_control_congr code m m' h.done h.pc (machineAgree_focus h)

/-- the action one call performs on a slot, in the component's own alphabet. -/
def progActRaw (code : List (Instruction 9)) (m : PalPeg.GalilScaffoldControl.Machine 9)
    (i : Fin 9) : List (PalPeg.CloseoutCoreEnc12.Act (Fin 9)) :=
  if m.done then []
  else
    match code[m.config.pc]? with
    | some (.move t true _) => if i = t then [some ((m.config.tapes t).focus, .right)] else []
    | some (.move t false _) => if i = t then [some ((m.config.tapes t).focus, .left)] else []
    | some (.write t sym _) => if i = t then [some (sym, .stay)] else []
    | _ => []

theorem progActRaw_length (code : List (Instruction 9))
    (m : PalPeg.GalilScaffoldControl.Machine 9) (i : Fin 9) :
    (progActRaw code m i).length ≤ 1 := by
  unfold progActRaw
  split
  · simp
  · split
    · split <;> simp
    · split <;> simp
    · split <;> simp
    · simp

/-- **a call performs exactly that action on the component's tape.** -/
theorem tapes_after_call (code : List (Instruction 9))
    (m : PalPeg.GalilScaffoldControl.Machine 9) (i : Fin 9) :
    encTape ((PalPeg.ProgramFunction.tickFun code true m).config.tapes i)
      = PalPeg.CloseoutCoreEnc12.actList (6 : Fin 9) (encTape (m.config.tapes i))
          (progActRaw code m i) := by
  rw [progTickFun_tapes code m]
  unfold progActRaw progStepTapes
  cases hdone : m.done
  · simp only [Bool.false_eq_true, if_false]
    match hcode : code[m.config.pc]? with
    | none => simp [hcode]
    | some .halt => simp [hcode]
    | some (.read t cs) => simp [hcode]
    | some (.write t sym pc) =>
        simp only [hcode]
        by_cases hit : i = t
        · subst hit
          rw [if_pos rfl, Function.update_self]
          obtain ⟨left, focus, right⟩ := m.config.tapes i
          rfl
        · rw [if_neg hit, Function.update_of_ne hit]
          rfl
    | some (.move t dir pc) =>
        cases dir
        · simp only [hcode]
          by_cases hit : i = t
          · subst hit
            rw [if_pos rfl, Function.update_self]
            obtain ⟨left, focus, right⟩ := m.config.tapes i
            cases left <;> rfl
          · rw [if_neg hit, Function.update_of_ne hit]
            rfl
        · simp only [hcode]
          by_cases hit : i = t
          · subst hit
            rw [if_pos rfl, Function.update_self]
            obtain ⟨left, focus, right⟩ := m.config.tapes i
            cases right <;> rfl
          · rw [if_neg hit, Function.update_of_ne hit]
            rfl
  · simp [hdone]

/-- one action moves a head by at most one cell, so it costs at most one of the margin. -/
theorem pos_applyAction_ge {Γ : Type} (blank : Γ) (T : STape Γ) (a : Γ × PalPeg.CloseoutCoreEnc12.MoveC) :
    PalPeg.Local.pos T - 1 ≤ PalPeg.Local.pos (T.applyAction blank a) := by
  obtain ⟨left, focus, right⟩ := T
  obtain ⟨sym, move⟩ := a
  cases move <;> cases left <;> cases right <;>
    simp [STape.applyAction, PalPeg.Local.pos] <;> omega

theorem pos_actList_ge {Γ : Type} (blank : Γ) (T : STape Γ)
    (l : List (PalPeg.CloseoutCoreEnc12.Act Γ)) (hl : l.length ≤ 1) :
    PalPeg.Local.pos T - 1 ≤ PalPeg.Local.pos (PalPeg.CloseoutCoreEnc12.actList blank T l) := by
  match l with
  | [] => exact Nat.sub_le _ _
  | [none] => exact Nat.sub_le _ _
  | [some a] => exact pos_applyAction_ge blank T a
  | _ :: _ :: _ => simp at hl

/-- the raw action of a call is decided by what the machine can see, just as the encoded one is. -/
theorem progActRaw_congr (code : List (Instruction 9))
    (m m' : PalPeg.GalilScaffoldControl.Machine 9)
    (hdone : m.done = m'.done) (hpc : m.config.pc = m'.config.pc)
    (hfocus : ∀ t : Fin 9, (m.config.tapes t).focus = (m'.config.tapes t).focus) (i : Fin 9) :
    progActRaw code m i = progActRaw code m' i := by
  unfold progActRaw
  rw [hdone, hpc]
  cases hd : m'.done
  · simp only [Bool.false_eq_true, if_false]
    match hcode : code[m'.config.pc]? with
    | none => simp [hcode]
    | some .halt => simp [hcode]
    | some (.read t cs) => simp [hcode]
    | some (.write t sym pc) => simp [hcode]
    | some (.move t dir pc) => cases dir <;> simp only [hcode, hfocus t]
  · simp

/-- **a call spends one of the agreement.**  Machines agreeing to radius `n + 1` leave a call
agreeing to radius `n`: the action they perform is the same, so the new windows are the same
function of the old ones, and a head that was `n + 1` from its left end is still `n`. -/
theorem machineAgree_tick {n : ℕ} (code : List (Instruction 9))
    {m m' : PalPeg.GalilScaffoldControl.Machine 9} (h : MachineAgree (n + 1) m m') :
    MachineAgree n (PalPeg.ProgramFunction.tickFun code true m)
      (PalPeg.ProgramFunction.tickFun code true m') where
  done := (tickFun_control_of_agree code h).2
  pc := (tickFun_control_of_agree code h).1
  margin := fun t => by
    rw [tapes_after_call]
    have hstep := pos_actList_ge (6 : Fin 9) (encTape (m.config.tapes t)) (progActRaw code m t)
      (progActRaw_length code m t)
    have hm := h.margin t
    omega
  margin' := fun t => by
    rw [tapes_after_call]
    have hstep := pos_actList_ge (6 : Fin 9) (encTape (m'.config.tapes t)) (progActRaw code m' t)
      (progActRaw_length code m' t)
    have hm := h.margin' t
    omega
  window := fun t => by
    rw [tapes_after_call, tapes_after_call,
      ← PalPeg.LocalStepFusion.windowAfter_readWin (6 : Fin 9) (encTape (m.config.tapes t))
        (progActRaw code m t)
        (by have := progActRaw_length code m t; omega) (h.margin t),
      ← PalPeg.LocalStepFusion.windowAfter_readWin (6 : Fin 9) (encTape (m'.config.tapes t))
        (progActRaw code m' t)
        (by have := progActRaw_length code m' t; omega) (h.margin' t),
      h.window t, progActRaw_congr code m m' h.done h.pc (machineAgree_focus h) t]

/-- **a quantum of `n` calls cannot tell apart two machines agreeing to radius `n`.**  This is
what lets the rule name the `fpp` branch's actions from its windows: the machine it runs in its
head agrees with the abstraction's exactly as far as the quantum can look. -/
theorem progRunActs_of_agree (code : List (Instruction 9)) :
    ∀ (n : ℕ) (m m' : PalPeg.GalilScaffoldControl.Machine 9), MachineAgree n m m' →
      ∀ i : Fin 9, progRunActs code n m i = progRunActs code n m' i := by
  intro n
  induction n with
  | zero => intro m m' _ i; rfl
  | succ n ih =>
      intro m m' h i
      show progActOf code m i ++ progRunActs code n (PalPeg.ProgramFunction.tickFun code true m) i
        = progActOf code m' i
          ++ progRunActs code n (PalPeg.ProgramFunction.tickFun code true m') i
      rw [progActOf_of_agree code h i,
        ih (PalPeg.ProgramFunction.tickFun code true m)
          (PalPeg.ProgramFunction.tickFun code true m') (machineAgree_tick code h) i]

/-- **a quantum cannot tell the control of two machines apart either.**  Each call spends one of
the radius the machines agree on, so after `n` of them the two runs carry the same program counter
and the same halting bit.  This is the control-side twin of `progRunActs_of_agree`. -/
theorem machineAgree_run (code : List (Instruction 9)) :
    ∀ (n : ℕ) (m m' : PalPeg.GalilScaffoldControl.Machine 9), MachineAgree n m m' →
      MachineAgree 0 (PalPeg.ProgramFunction.runFun code (List.replicate n true) m)
        (PalPeg.ProgramFunction.runFun code (List.replicate n true) m')
  | 0, _, _, h => h
  | n + 1, m, m', h => by
      rw [List.replicate_succ]
      exact machineAgree_run code n _ _ (machineAgree_tick code h)

/-- the control is part of what survives, and it is the part the finite state carries. -/
theorem runFun_control_of_agree (code : List (Instruction 9)) (n : ℕ)
    (m m' : PalPeg.GalilScaffoldControl.Machine 9) (h : MachineAgree n m m') :
      (PalPeg.ProgramFunction.runFun code (List.replicate n true) m).config.pc
          = (PalPeg.ProgramFunction.runFun code (List.replicate n true) m').config.pc
        ∧ (PalPeg.ProgramFunction.runFun code (List.replicate n true) m).done
          = (PalPeg.ProgramFunction.runFun code (List.replicate n true) m').done :=
  ⟨(machineAgree_run code n m m' h).pc, (machineAgree_run code n m m' h).done⟩

/-- **and so is the symbol under each head**, which is what the branch that marks the new block
needs: the rule must write beside a cell it can only know through its windows. -/
theorem runFun_focus_of_agree (code : List (Instruction 9)) (n : ℕ)
    (m m' : PalPeg.GalilScaffoldControl.Machine 9) (h : MachineAgree n m m') (t : Fin 9) :
    ((PalPeg.ProgramFunction.runFun code (List.replicate n true) m).config.tapes t).focus
      = ((PalPeg.ProgramFunction.runFun code (List.replicate n true) m').config.tapes t).focus :=
  machineAgree_focus (machineAgree_run code n m m' h) t

/-- **the machine the rule runs in its head agrees with the abstraction's, as far as a quantum of
`K` calls can look.**  Its heads sit at the centre of their windows by construction, and each of
its cells is the component's own by `rd_winTape_of_padded`. -/
theorem machineAgree_winMachine {fppBound dpBound K : ℕ} {margin : ℕ} {w : List (Fin 2)} {x : State GalilVM}
    {q : QPhys fppBound dpBound} {T : Slot → STape Γm} (henc : Enc w margin x (q, T))
    (hcomp : ∀ t : Fin 9, K ≤ PalPeg.Local.pos (encTape (x.vm.fpp.program.config.tapes t)))
    (pc : ℕ) (done : Bool) (hpc : x.vm.fpp.program.config.pc = pc)
    (hdone : x.vm.fpp.program.done = done) :
    MachineAgree K
      (winMachine pc done (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) q.fppLive)
      x.vm.fpp.program where
  done := by rw [winMachine_done, hdone]
  pc := by rw [winMachine_pc, hpc]
  margin := fun t => by
    show K ≤ PalPeg.Local.pos (encTape (winTape (PalPeg.Local.readWin blankM K
      (tapesOf T (slotIndex (progSlotOf q.fppLive t))))))
    rw [winTape_pos]
  margin' := hcomp
  window := fun t => by
    funext i
    have hfpp : tapesOf T (slotIndex (progSlotOf q.fppLive t))
        = padLeft margin (mapTape encProg (encTape (x.vm.fpp.program.config.tapes t))) := by
      rw [tapesOf_apply]
      exact henc.2.fpp t
    show PalPeg.Local.readWin (6 : Fin 9) K (encTape (winTape (PalPeg.Local.readWin blankM K
      (tapesOf T (slotIndex (progSlotOf q.fppLive t)))))) i = _
    rw [hfpp, PalPeg.Local.readWin_eq, PalPeg.Local.readWin_eq, winTape_pos,
      show K - K + (i : ℕ) = (i : ℕ) from by omega]
    exact rd_winTape_of_padded (x.vm.fpp.program.config.tapes t) (hcomp t) i

/-- agreeing far enough is agreeing near enough. -/
theorem machineAgree_mono {n K : ℕ} (hn : n ≤ K)
    {m m' : PalPeg.GalilScaffoldControl.Machine 9} (h : MachineAgree K m m') :
    MachineAgree n m m' where
  done := h.done
  pc := h.pc
  margin := fun t => le_trans hn (h.margin t)
  margin' := fun t => le_trans hn (h.margin' t)
  window := fun t => by
    have h₁ := PalPeg.LocalStepFusion.windowAfter_readWin (6 : Fin 9)
      (encTape (m.config.tapes t)) [] (by simpa using hn) (h.margin t)
    have h₂ := PalPeg.LocalStepFusion.windowAfter_readWin (6 : Fin 9)
      (encTape (m'.config.tapes t)) [] (by simpa using hn) (h.margin' t)
    rw [PalPeg.CloseoutCoreEnc12.actList_nil] at h₁ h₂
    rw [← h₁, ← h₂, h.window t]

/-- **the actions the `fpp` branch names are the quantum's own.**  The rule reads them off its
windows, running the program on the tapes those stand for; the quantum is short enough that it
never looks past them. -/
theorem fppActs_eq {fppBound dpBound K : ℕ} {margin : ℕ} {w : List (Fin 2)} {x : State GalilVM}
    {q : QPhys fppBound dpBound} {T : Slot → STape Γm} (code : List (Instruction 9))
    (quantum : ℕ) (hq : quantum ≤ K) (henc : Enc w margin x (q, T))
    (hcomp : ∀ t : Fin 9, K ≤ PalPeg.Local.pos (encTape (x.vm.fpp.program.config.tapes t)))
    (pc : ℕ) (done : Bool) (hpc : x.vm.fpp.program.config.pc = pc)
    (hdone : x.vm.fpp.program.done = done) (i : Fin 9) :
    fppActs code quantum q.fppLive pc done
        (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
        (slotIndex (progSlotOf q.fppLive i))
      = progRunActs code quantum x.vm.fpp.program i := by
  rw [fppActs_at_live]
  exact progRunActs_of_agree code quantum _ _
    (machineAgree_mono hq (machineAgree_winMachine henc hcomp pc done hpc hdone)) i

/-- **the `fpp` branch carries a program slot across the quantum.**  What the rule names there is
the quantum's own actions, and applying them to the encoded tape lands on the encoding of the tape
the run leaves behind. -/
theorem fpp_slot_after {fppBound dpBound K : ℕ} {margin : ℕ} {w : List (Fin 2)} {x : State GalilVM}
    {q : QPhys fppBound dpBound} {T : Slot → STape Γm} (code : List (Instruction 9))
    (quantum : ℕ) (hq : quantum ≤ K) (henc : Enc w margin x (q, T))
    (hcomp : ∀ t : Fin 9, K ≤ PalPeg.Local.pos (encTape (x.vm.fpp.program.config.tapes t)))
    (hfloorRun : ∀ k, ∀ t : Fin 9, ((PalPeg.ProgramFunction.runFun code
      (List.replicate k true) x.vm.fpp.program).config.tapes t).left ≠ [])
    (pc : ℕ) (done : Bool) (hpc : x.vm.fpp.program.config.pc = pc)
    (hdone : x.vm.fpp.program.done = done) (i : Fin 9) :
    PalPeg.CloseoutCoreEnc12.actList blankM (T (progSlot q.fppLive i))
        (fppActs code quantum q.fppLive pc done
          (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (slotIndex (progSlot q.fppLive i)))
      = padLeft margin (mapTape encProg (encTape
          ((PalPeg.ProgramFunction.runFun code (List.replicate quantum true)
            x.vm.fpp.program).config.tapes i))) := by
  have hfpp : T (progSlot q.fppLive i)
      = padLeft margin (mapTape encProg (encTape (x.vm.fpp.program.config.tapes i))) :=
    henc.2.fpp i
  rw [fppActs_eq code quantum hq henc hcomp pc done hpc hdone i, hfpp,
    padded_progRun margin code quantum x.vm.fpp.program i hfloorRun]

/-! ### the branch that runs the preparation program, rule and encoding together

The quantum is the one branch whose actions the rule cannot read off a single cell: it has to run
the program in its head.  `fppActs` is that run, `fpp_slot_after` says the actions land on the
encoding of the tapes the real run leaves, and `runFun_control_of_agree` says the control the rule
installs is the control the tick installs.  Nothing here assumes the rule; it is proved for any
rule whose table at this state is the one the branch names. -/

theorem fpp_slice_of_rule {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (R : PalPeg.CloseoutCoreEnc12.ActRule (Fin 2) (QPhys fppBound dpBound) Γm tapeCountM K)
    (hnq : R.nq q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) = fppNext entryQ q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)))
    (hacts : R.acts q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = withErase q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (fppActs PalPeg.GalilFppMarkedCode.code entryQ q.fppLive (pcOf q) q.fppDone (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))))
    (hq : entryQ ≤ K) (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hcomp : ∀ t : Fin 9, K ≤ PalPeg.Local.pos (encTape (x.vm.fpp.program.config.tapes t)))
    (hfloorRun : ∀ k, ∀ t : Fin 9, ((PalPeg.ProgramFunction.runFun PalPeg.GalilFppMarkedCode.code
      (List.replicate k true) x.vm.fpp.program).config.tapes t).left ≠ [])
    (hpc : x.vm.fpp.program.config.pc = pcOf q)
    (hdone : x.vm.fpp.program.done = q.fppDone)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.fpp)
    (hnothalt : (PalPeg.ProgramFunction.fppRunFun entryQ x.vm.fpp.program).done = false)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2
          (slotIndex i)) := by
  have hagree : MachineAgree entryQ
      (winMachine (pcOf q) q.fppDone (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) q.fppLive) x.vm.fpp.program :=
    machineAgree_mono hq (machineAgree_winMachine henc hcomp (pcOf q) q.fppDone hpc hdone)
  obtain ⟨hpcRun, hdoneRun⟩ := runFun_control_of_agree PalPeg.GalilFppMarkedCode.code entryQ _ _ hagree
  have hrunDone : (winRun PalPeg.GalilFppMarkedCode.code entryQ q.fppLive (pcOf q) q.fppDone (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).done = false := by
    show (PalPeg.ProgramFunction.runFun PalPeg.GalilFppMarkedCode.code (List.replicate entryQ true)
      (winMachine (pcOf q) q.fppDone (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) q.fppLive)).done = false
    rw [hdoneRun]
    exact hnothalt
  have hstate : (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).1
      = {q with fppPc := pcPhysOf fppBound (winRun PalPeg.GalilFppMarkedCode.code entryQ q.fppLive (pcOf q) q.fppDone (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).config.pc, fppDone := false} := by
    show R.nq q none _ = _
    rw [hnq]
    unfold fppNext
    rw [if_neg (by simp [hrunDone])]
  have htick : PalPeg.GalilScaffoldTop.tickFun
      (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x
      = (⟨x.ctl, {x.vm with fpp := {x.vm.fpp with
          program := PalPeg.ProgramFunction.fppRunFun entryQ x.vm.fpp.program}}⟩ :
            State GalilVM) := by
    simp only [PalPeg.GalilScaffoldTop.tickFun, hmode, frameFun_fppHalts, frameFun_fppSlice]
    rw [if_neg (by simp [hnothalt])]
  obtain ⟨hmoved, hkept⟩ :=
    idealStep_offBase R q T q.fppLive _ hacts
      (fppActs_off_live PalPeg.GalilFppMarkedCode.code entryQ q.fppLive (pcOf q) q.fppDone (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)))
  rw [htick, hstate]
  refine ⟨?_, ?_⟩
  · exact
      { ctl := henc.1.ctl
        chainTag := henc.1.chainTag
        chainPhase := henc.1.chainPhase
        chainForward := henc.1.chainForward
        chainBroken := henc.1.chainBroken
        fppMode := henc.1.fppMode
        fppFinalStage := henc.1.fppFinalStage
        fppPc := by
          rw [fppRunFun_eq_runFun, ← hpcRun]
          exact encPc_pcPhysOf _ _
        fppDone := hnothalt.symm
        dpPc := henc.1.dpPc
        dpDone := henc.1.dpDone
        searchMode := henc.1.searchMode
        searchFinalStage := henc.1.searchFinalStage
        searchQuarter := henc.1.searchQuarter
        periodOnly := henc.1.periodOnly
        placeGap := henc.1.placeGap
        onLetter := henc.1.onLetter
        leftFirst := henc.1.leftFirst }
  · exact encTapes_fppTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T
      (fun slot => (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2
        (slotIndex slot))
      henc.2 (PalPeg.ProgramFunction.fppRunFun entryQ x.vm.fpp.program) x.ctl
      (fun j => by
        rw [hmoved j, fppRunFun_eq_runFun]
        exact fpp_slot_after PalPeg.GalilFppMarkedCode.code entryQ hq henc hcomp hfloorRun (pcOf q) q.fppDone hpc hdone j)
      (fun slot hs hidle => hkept slot hs hidle)
      (fun k => idle_shape_after_erase margin hK1 hKn R q T q.fppLive _ hacts
        (offLive_offIdle (fppActs_off_live PalPeg.GalilFppMarkedCode.code entryQ q.fppLive (pcOf q) q.fppDone (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))))
        henc.2.idleShape k)

/-- **the quantum of the machine itself.**  The two hypotheses about the rule are discharged
against the rule the machine runs. -/
theorem physRule_fpp_running {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K)
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hcomp : ∀ t : Fin 9, K ≤ PalPeg.Local.pos (encTape (x.vm.fpp.program.config.tapes t)))
    (hfloorRun : ∀ k, ∀ t : Fin 9, ((PalPeg.ProgramFunction.runFun PalPeg.GalilFppMarkedCode.code
      (List.replicate k true) x.vm.fpp.program).config.tapes t).left ≠ [])
    (hin : x.vm.fpp.program.config.pc < fppBound)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.fpp)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.fpp)
    (hnothalt : (PalPeg.ProgramFunction.fppRunFun entryQ x.vm.fpp.program).done = false)
    (hwinRun : (winRun PalPeg.GalilFppMarkedCode.code entryQ q.fppLive (pcOf q) q.fppDone
      (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).done = false)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hK)
          blankM (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first
          hbound hK) blankM (q, tapesOf T) none).2 (slotIndex i)) :=
  fpp_slice_of_rule margin centre place entry entryQ first w F delay x q T
    (physRule entryQ first hbound hK)
    (physRule_nq_fpp entryQ first hbound hK q _ hqmode)
    (by
      rw [physRule_acts_fpp entryQ first hbound hK q _ hqmode,
        fppBranchActs_of_running PalPeg.GalilFppMarkedCode.code entryQ q.fppLive first
          (pcOf q) q.fppDone _ hwinRun])
    (by omega) hK1 hKn hcomp hfloorRun (pcOf_of_enc henc.1 hin) henc.1.fppDone.symm hmode hnothalt henc

/-- **the quantum that reaches the halt, rule and encoding together.**  The run's tapes land on
the live half as before, the marks tape takes two more actions, and the controller goes to the
mark walk. -/
theorem fpp_done_of_rule {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (R : PalPeg.CloseoutCoreEnc12.ActRule (Fin 2) (QPhys fppBound dpBound) Γm tapeCountM K)
    (hnq : R.nq q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) = fppNext entryQ q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)))
    (hacts : R.acts q none (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = withErase q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (fppBranchActs PalPeg.GalilFppMarkedCode.code entryQ q.fppLive first (pcOf q) q.fppDone (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))))
    (hq : entryQ ≤ K) (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hcomp : ∀ t : Fin 9, K ≤ PalPeg.Local.pos (encTape (x.vm.fpp.program.config.tapes t)))
    (hfloorRun : ∀ k, ∀ t : Fin 9, ((PalPeg.ProgramFunction.runFun PalPeg.GalilFppMarkedCode.code
      (List.replicate k true) x.vm.fpp.program).config.tapes t).left ≠ [])
    (hpc : x.vm.fpp.program.config.pc = pcOf q)
    (hdone : x.vm.fpp.program.done = q.fppDone)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.fpp)
    (hhalt : (PalPeg.ProgramFunction.fppRunFun entryQ x.vm.fpp.program).done = true)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2
          (slotIndex i)) := by
  have hagree : MachineAgree entryQ
      (winMachine (pcOf q) q.fppDone (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) q.fppLive) x.vm.fpp.program :=
    machineAgree_mono hq (machineAgree_winMachine henc hcomp (pcOf q) q.fppDone hpc hdone)
  obtain ⟨hpcRun, hdoneRun⟩ := runFun_control_of_agree PalPeg.GalilFppMarkedCode.code entryQ _ _ hagree
  have hfocusRun := runFun_focus_of_agree PalPeg.GalilFppMarkedCode.code entryQ _ _ hagree 8
  have hwinDone : (winRun PalPeg.GalilFppMarkedCode.code entryQ q.fppLive (pcOf q) q.fppDone (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).done = true := by
    show (PalPeg.ProgramFunction.runFun PalPeg.GalilFppMarkedCode.code (List.replicate entryQ true)
      (winMachine (pcOf q) q.fppDone (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) q.fppLive)).done = true
    rw [hdoneRun]
    exact hhalt
  have hctl : ctlAbs {q.ctl with mode := PalPeg.GalilScaffoldController.Mode.markEnd} = {x.ctl with mode := PalPeg.GalilScaffoldController.Mode.markEnd} := by
    rw [← henc.1.ctl]
    rfl
  have hstate : (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).1
      = {q with ctl := {q.ctl with mode := PalPeg.GalilScaffoldController.Mode.markEnd}, fppPc := pcPhysOf fppBound (winRun PalPeg.GalilFppMarkedCode.code entryQ q.fppLive (pcOf q) q.fppDone (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).config.pc, fppDone := true} := by
    show R.nq q none _ = _
    rw [hnq]
    unfold fppNext
    rw [if_pos (by simp [hwinDone])]
  have htick : PalPeg.GalilScaffoldTop.tickFun
      (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x
      = (⟨{x.ctl with mode := PalPeg.GalilScaffoldController.Mode.markEnd},
          {x.vm with fpp := {x.vm.fpp with program := PalPeg.GalilScaffoldChainInputSupply.markNew (PalPeg.ProgramFunction.fppRunFun entryQ x.vm.fpp.program) first}}⟩ : State GalilVM) := by
    simp only [PalPeg.GalilScaffoldTop.tickFun, hmode, frameFun_fppHalts, frameFun_fppDone]
    rw [if_pos (by simp [hhalt])]
  have htable : fppBranchActs PalPeg.GalilFppMarkedCode.code entryQ q.fppLive first (pcOf q) q.fppDone (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = fun j => fppActs PalPeg.GalilFppMarkedCode.code entryQ q.fppLive (pcOf q) q.fppDone (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) j
          ++ (if j = slotIndex (progSlotOf q.fppLive 8)
                then markNewActs PalPeg.GalilFppMarkedCode.code entryQ q.fppLive first (pcOf q) q.fppDone (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) else []) := by
    unfold fppBranchActs
    rw [if_pos (by simp [hwinDone])]
  obtain ⟨hmoved, hkept⟩ :=
    idealStep_offBase R q T q.fppLive _ hacts
      (fppBranchActs_off_live PalPeg.GalilFppMarkedCode.code entryQ q.fppLive first (pcOf q) q.fppDone (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)))
  have hslot : ∀ j : Fin 9,
      (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2
          (slotIndex (progSlotOf q.fppLive j))
        = padLeft margin (mapTape encProg (encTape ((PalPeg.GalilScaffoldChainInputSupply.markNew (PalPeg.ProgramFunction.fppRunFun entryQ x.vm.fpp.program) first).config.tapes j))) := by
    intro j
    rw [hmoved j, htable]
    by_cases hj : j = 8
    · subst hj
      show PalPeg.CloseoutCoreEnc12.actList blankM (T (progSlotOf q.fppLive 8))
        (fppActs PalPeg.GalilFppMarkedCode.code entryQ q.fppLive (pcOf q) q.fppDone (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
            (slotIndex (progSlotOf q.fppLive 8))
          ++ (if slotIndex (progSlotOf q.fppLive 8) = slotIndex (progSlotOf q.fppLive 8)
                then markNewActs PalPeg.GalilFppMarkedCode.code entryQ q.fppLive first (pcOf q) q.fppDone (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) else [])) = _
      rw [if_pos rfl, actList_append,
        fpp_slot_after PalPeg.GalilFppMarkedCode.code entryQ hq henc hcomp hfloorRun (pcOf q) q.fppDone hpc hdone 8]
      show PalPeg.CloseoutCoreEnc12.actList blankM
          (padLeft margin (mapTape encProg (encTape ((PalPeg.ProgramFunction.runFun PalPeg.GalilFppMarkedCode.code (List.replicate entryQ true) x.vm.fpp.program).config.tapes 8))))
          [some (encProg ((winRun PalPeg.GalilFppMarkedCode.code entryQ q.fppLive (pcOf q) q.fppDone (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).config.tapes 8).focus,
              (.right : PalPeg.CloseoutCoreEnc12.MoveC)),
            some (encProg first, (.right : PalPeg.CloseoutCoreEnc12.MoveC))] = _
      rw [show ((winRun PalPeg.GalilFppMarkedCode.code entryQ q.fppLive (pcOf q) q.fppDone (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).config.tapes 8).focus = ((PalPeg.ProgramFunction.runFun PalPeg.GalilFppMarkedCode.code (List.replicate entryQ true) x.vm.fpp.program).config.tapes 8).focus from hfocusRun]
      rw [padded_markNew margin ((PalPeg.ProgramFunction.runFun PalPeg.GalilFppMarkedCode.code (List.replicate entryQ true) x.vm.fpp.program).config.tapes 8) first]
      rfl
    · show PalPeg.CloseoutCoreEnc12.actList blankM (T (progSlotOf q.fppLive j))
        (fppActs PalPeg.GalilFppMarkedCode.code entryQ q.fppLive (pcOf q) q.fppDone (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
            (slotIndex (progSlotOf q.fppLive j))
          ++ (if slotIndex (progSlotOf q.fppLive j) = slotIndex (progSlotOf q.fppLive 8)
                then markNewActs PalPeg.GalilFppMarkedCode.code entryQ q.fppLive first (pcOf q) q.fppDone (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) else [])) = _
      rw [if_neg (fun h => hj (progSlotOf_injective q.fppLive (slotIndex.injective h))), List.append_nil,
        fpp_slot_after PalPeg.GalilFppMarkedCode.code entryQ hq henc hcomp hfloorRun (pcOf q) q.fppDone hpc hdone j]
      show _ = padLeft margin (mapTape encProg (encTape
        (Function.update (PalPeg.ProgramFunction.fppRunFun entryQ x.vm.fpp.program).config.tapes 8
          (PalPeg.GalilScaffoldTape.moveRight (PalPeg.GalilScaffoldTape.write
            (PalPeg.GalilScaffoldTape.moveRight
              ((PalPeg.ProgramFunction.fppRunFun entryQ x.vm.fpp.program).config.tapes 8))
            first)) j)))
      rw [Function.update_of_ne hj]
      rfl
  rw [htick, hstate]
  refine ⟨?_, ?_⟩
  · exact
      { ctl := hctl
        chainTag := henc.1.chainTag
        chainPhase := henc.1.chainPhase
        chainForward := henc.1.chainForward
        chainBroken := henc.1.chainBroken
        fppMode := henc.1.fppMode
        fppFinalStage := henc.1.fppFinalStage
        fppPc := by
          show EncPc (pcPhysOf fppBound (winRun PalPeg.GalilFppMarkedCode.code entryQ q.fppLive (pcOf q) q.fppDone (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).config.pc)
            (PalPeg.ProgramFunction.fppRunFun entryQ x.vm.fpp.program).config.pc
          rw [fppRunFun_eq_runFun, ← hpcRun]
          exact encPc_pcPhysOf _ _
        fppDone := hhalt.symm
        dpPc := henc.1.dpPc
        dpDone := henc.1.dpDone
        searchMode := henc.1.searchMode
        searchFinalStage := henc.1.searchFinalStage
        searchQuarter := henc.1.searchQuarter
        periodOnly := henc.1.periodOnly
        placeGap := henc.1.placeGap
        onLetter := henc.1.onLetter
        leftFirst := henc.1.leftFirst }
  · exact encTapes_fppTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T
      (fun slot => (PalPeg.LocalStepFusion.idealStep R blankM (q, tapesOf T) none).2
        (slotIndex slot))
      henc.2 (PalPeg.GalilScaffoldChainInputSupply.markNew (PalPeg.ProgramFunction.fppRunFun entryQ x.vm.fpp.program) first) {x.ctl with mode := PalPeg.GalilScaffoldController.Mode.markEnd} hslot
      (fun slot hs hidle => hkept slot hs hidle)
      (fun k => idle_shape_after_erase margin hK1 hKn R q T q.fppLive _ hacts
        (offLive_offIdle (fppBranchActs_off_live PalPeg.GalilFppMarkedCode.code entryQ q.fppLive first (pcOf q) q.fppDone (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))))
        henc.2.idleShape k)

/-- **the quantum that halts, for the machine's own rule.** -/
theorem physRule_fpp_done {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K)
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hcomp : ∀ t : Fin 9, K ≤ PalPeg.Local.pos (encTape (x.vm.fpp.program.config.tapes t)))
    (hfloorRun : ∀ k, ∀ t : Fin 9, ((PalPeg.ProgramFunction.runFun PalPeg.GalilFppMarkedCode.code
      (List.replicate k true) x.vm.fpp.program).config.tapes t).left ≠ [])
    (hin : x.vm.fpp.program.config.pc < fppBound)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.fpp)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.fpp)
    (hhalt : (PalPeg.ProgramFunction.fppRunFun entryQ x.vm.fpp.program).done = true)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hK)
          blankM (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first
          hbound hK) blankM (q, tapesOf T) none).2 (slotIndex i)) :=
  fpp_done_of_rule margin centre place entry entryQ first w F delay x q T
    (physRule entryQ first hbound hK)
    (physRule_nq_fpp entryQ first hbound hK q _ hqmode)
    (physRule_acts_fpp entryQ first hbound hK q _ hqmode)
    (by omega) hK1 hKn hcomp hfloorRun (pcOf_of_enc henc.1 hin) henc.1.fppDone.symm hmode hhalt henc

/-- **the whole of the `fpp` mode.**  Whether or not the quantum reaches the halt, the tick and
the rule's ideal step land on the same encoded state; which of the two it is, the rule decides
from its windows, and `runFun_control_of_agree` says that decision is the right one. -/
theorem physRule_fpp {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K)
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hcomp : ∀ t : Fin 9, K ≤ PalPeg.Local.pos (encTape (x.vm.fpp.program.config.tapes t)))
    (hfloorRun : ∀ k, ∀ t : Fin 9, ((PalPeg.ProgramFunction.runFun PalPeg.GalilFppMarkedCode.code
      (List.replicate k true) x.vm.fpp.program).config.tapes t).left ≠ [])
    (hin : x.vm.fpp.program.config.pc < fppBound)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.fpp)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.fpp)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hK)
          blankM (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first
          hbound hK) blankM (q, tapesOf T) none).2 (slotIndex i)) := by
  have hagree : MachineAgree entryQ
      (winMachine (pcOf q) q.fppDone (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) q.fppLive) x.vm.fpp.program :=
    machineAgree_mono (by omega) (machineAgree_winMachine henc hcomp (pcOf q) q.fppDone
      (pcOf_of_enc henc.1 hin) henc.1.fppDone.symm)
  obtain ⟨-, hdoneRun⟩ := runFun_control_of_agree PalPeg.GalilFppMarkedCode.code entryQ _ _ hagree
  cases hhalt : (PalPeg.ProgramFunction.fppRunFun entryQ x.vm.fpp.program).done with
  | true =>
      exact physRule_fpp_done margin centre place entry entryQ first w F delay x q T hbound hK
        hK1 hKn hcomp hfloorRun hin hqmode hmode hhalt henc
  | false =>
      refine physRule_fpp_running margin centre place entry entryQ first w F delay x q T hbound hK
        hK1 hKn hcomp hfloorRun hin hqmode hmode hhalt ?_ henc
      show (PalPeg.ProgramFunction.runFun PalPeg.GalilFppMarkedCode.code (List.replicate entryQ true)
        (winMachine (pcOf q) q.fppDone (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) q.fppLive)).done = false
      rw [hdoneRun]
      exact hhalt

-- the machine's alphabet must be finite and decidable, as the physical machine demands
#synth Fintype Γm
#synth DecidableEq Γm
#synth Fintype Slot
#synth DecidableEq Slot
#synth Fintype CtlPhys
#synth DecidableEq CtlPhys
#synth Fintype ChainTag
#synth DecidableEq ChainTag

/-- **markEnd, on the machine of twelve steps.** -/
theorem markEnd_of_tick {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (rest : QPhys fppBound dpBound → Option (Fin 2) →
      (Fin tapeCountM → PalPeg.Local.Window Γm K) → Fin 4 →
      PalPeg.ConcreteLocalMachine.ViewCommand)
    (input : Option (Fin 2))
    (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K) (hK2 : 2 ≤ K) (hK1 : 1 ≤ K)
    (hmargin : K ≤ margin) (hKn : K ≤ margin + 1)
    (hslot0 : q.slot.val = 0) (howed : ∀ v, (q.micro v).2.2.2 = 0)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hK hK2 rest) blankM
          (q, tapesOf T) input 12).1,
        fun i => (PalPeg.LocalStepFusion.idealRun
          (tickPhysRule entryQ first hbound hK hK2 rest) blankM (q, tapesOf T) input 12).2
            (slotIndex i)) :=
  enc_ofBranchStep_still margin entryQ first hbound hK hK2 hmargin rest w x
    (PalPeg.GalilScaffoldTop.tickFun
      (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x) q T input
    hslot0 (Or.inl hqmode) howed
    (headOf_tickFun_still centre place entry entryQ first w F delay x (Or.inl hmode))
    henc.2
    (physRule_markEnd margin centre place entry entryQ first w F delay x q T hbound hK
      (fun i => hmargin.trans (henc.2.margins i)) hK1 hKn hqmode hmode
      henc)


/-- **home, on the machine of twelve steps.** -/
theorem home_of_tick {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (rest : QPhys fppBound dpBound → Option (Fin 2) →
      (Fin tapeCountM → PalPeg.Local.Window Γm K) → Fin 4 →
      PalPeg.ConcreteLocalMachine.ViewCommand)
    (input : Option (Fin 2))
    (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K) (hK2 : 2 ≤ K) (hK1 : 1 ≤ K)
    (hmargin : K ≤ margin) (hKn : K ≤ margin + 1)
    (hslot0 : q.slot.val = 0) (howed : ∀ v, (q.micro v).2.2.2 = 0)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.home)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.home)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hK hK2 rest) blankM
          (q, tapesOf T) input 12).1,
        fun i => (PalPeg.LocalStepFusion.idealRun
          (tickPhysRule entryQ first hbound hK hK2 rest) blankM (q, tapesOf T) input 12).2
            (slotIndex i)) :=
  enc_ofBranchStep_still margin entryQ first hbound hK hK2 hmargin rest w x
    (PalPeg.GalilScaffoldTop.tickFun
      (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x) q T input
    hslot0 (Or.inr (Or.inl hqmode)) howed
    (headOf_tickFun_still centre place entry entryQ first w F delay x (Or.inr (Or.inl hmode)))
    henc.2
    (physRule_home margin centre place entry entryQ first w F delay x q T hbound hK
      (fun i => hmargin.trans (henc.2.margins i)) hK1 hKn hqmode hmode
      henc)



/-- **the parity walk that keeps looking, on the machine of twelve steps.** -/
theorem choose_back_of_tick {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (rest : QPhys fppBound dpBound → Option (Fin 2) →
      (Fin tapeCountM → PalPeg.Local.Window Γm K) → Fin 4 →
      PalPeg.ConcreteLocalMachine.ViewCommand)
    (input : Option (Fin 2))
    (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K) (hK2 : 2 ≤ K) (hK1 : 1 ≤ K)
    (hmargin : K ≤ margin) (hKn : K ≤ margin + 1)
    (hslot0 : q.slot.val = 0) (howed : ∀ v, (q.micro v).2.2.2 = 0)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.choose)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.choose)
    (hkeep : (x.ctl.odd && (decide ((x.vm.fpp.program.config.tapes 8).focus = 8)
        || decide ((x.vm.fpp.program.config.tapes 8).focus = first))) = false)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hK hK2 rest) blankM
          (q, tapesOf T) input 12).1,
        fun i => (PalPeg.LocalStepFusion.idealRun
          (tickPhysRule entryQ first hbound hK hK2 rest) blankM (q, tapesOf T) input 12).2
            (slotIndex i)) :=
  enc_ofBranchStep_still margin entryQ first hbound hK hK2 hmargin rest w x
    (PalPeg.GalilScaffoldTop.tickFun
      (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x) q T input
    hslot0 (Or.inr (Or.inr (Or.inl hqmode))) howed
    (headOf_tickFun_chooseBack centre place entry entryQ first w F delay x hmode hkeep)
    henc.2
    (physRule_choose margin centre place entry entryQ first w F delay x q T hbound hK
      (fun i => hmargin.trans (henc.2.margins i)) hK1 hKn hqmode hmode hkeep henc)

/-- **the preparation program's own tick, on the machine of twelve steps.**  Its branch carries
the three facts about the program that the preparation needs; they are passed through. -/
theorem fpp_of_tick {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (rest : QPhys fppBound dpBound → Option (Fin 2) →
      (Fin tapeCountM → PalPeg.Local.Window Γm K) → Fin 4 →
      PalPeg.ConcreteLocalMachine.ViewCommand)
    (input : Option (Fin 2))
    (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K) (hK2 : 2 ≤ K) (hK1 : 1 ≤ K)
    (hmargin : K ≤ margin) (hKn : K ≤ margin + 1)
    (hcomp : ∀ t : Fin 9, K ≤ PalPeg.Local.pos (encTape (x.vm.fpp.program.config.tapes t)))
    (hfloorRun : ∀ k, ∀ t : Fin 9, ((PalPeg.ProgramFunction.runFun PalPeg.GalilFppMarkedCode.code
      (List.replicate k true) x.vm.fpp.program).config.tapes t).left ≠ [])
    (hin : x.vm.fpp.program.config.pc < fppBound)
    (hslot0 : q.slot.val = 0) (howed : ∀ v, (q.micro v).2.2.2 = 0)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.fpp)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.fpp)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hK hK2 rest) blankM
          (q, tapesOf T) input 12).1,
        fun i => (PalPeg.LocalStepFusion.idealRun
          (tickPhysRule entryQ first hbound hK hK2 rest) blankM (q, tapesOf T) input 12).2
            (slotIndex i)) :=
  enc_ofBranchStep_still margin entryQ first hbound hK hK2 hmargin rest w x
    (PalPeg.GalilScaffoldTop.tickFun
      (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x) q T input
    hslot0 (Or.inr (Or.inr (Or.inr (Or.inl hqmode)))) howed
    (headOf_tickFun_still centre place entry entryQ first w F delay x
      (Or.inr (Or.inr (Or.inl hmode))))
    henc.2
    (physRule_fpp margin centre place entry entryQ first w F delay x q T hbound hK hK1 hKn hcomp
      hfloorRun hin hqmode hmode henc)


/-- **the rewind's row names, for each cursor, the operation the tick does to it.** -/
theorem headOp_rewindCommands {fppBound dpBound K : ℕ} (first : Fin 9)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hnot : ¬ centreRead ws (progSlot q.fppLive 8) = encProg first) (v : Fin 4) :
    headOp (rewindCommands first q.fppLive q ws v) = some (rewindHeadOps q.ctl.pair v) := by
  match v with
  | 0 =>
    rw [rewindCommands_walks first q.fppLive q ws hnot 0 (Or.inl rfl)]
    rfl
  | 1 =>
    cases hp : q.ctl.pair
    · rw [rewindCommands_still first q.fppLive q ws 1 (by decide)
        (fun h => absurd (hp.symm.trans h) (by simp))]
      rfl
    · rw [rewindCommands_walks first q.fppLive q ws hnot 1 (Or.inr ⟨hp, rfl⟩)]
      rfl
  | 2 =>
    rw [rewindCommands_still first q.fppLive q ws 2 (by decide) (fun _ => by decide)]
    rfl
  | 3 =>
    rw [rewindCommands_still first q.fppLive q ws 3 (by decide) (fun _ => by decide)]
    rfl

/-- **a tick of the rewind that has reached the first instruction moves no input head either.**
It wipes the preparation program, which is inside the preparation's own state. -/
theorem headOf_tickFun_rewindReset (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind)
    (hatFirst : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).atFirst
      x.vm = true) (v : Fin 4) :
    headOf (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x) v
      = headOf x v := by
  refine headOf_congr_of_vm ?_ ?_ ?_ ?_ v <;>
    (unfold PalPeg.GalilScaffoldTop.tickFun
     rw [hmode]
     dsimp only
     rw [if_pos hatFirst]
     rfl)

/-- **the tick that leaves the shift moves no input head.**  It carries the whole machine state
over and changes only the controller's word. -/
theorem headOf_tickFun_shiftExit (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.shift)
    (hdone : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).remainingPos
      x.vm = false) (v : Fin 4) :
    headOf (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x) v
      = headOf x v := by
  refine headOf_congr_of_vm ?_ ?_ ?_ ?_ v <;>
    (unfold PalPeg.GalilScaffoldTop.tickFun
     rw [hmode]
     dsimp only
     rw [if_neg (by rw [hdone]; simp)])

/-- **what the start does to the cursors.**  `FrameFunction.initFun` steps the right cursor and
makes the other two equal to it, and it idles the chain.  So the start is not three copies of a
cursor but one step of three cursors that are already the same — which is why it costs the
machine nothing beyond a step right on each, provided their slots already hold the same view.

At the start they do: the machine begins with every tape blank, so every cursor's twelve slots
hold the same view. -/
theorem headOf_tickFun_init (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.init) :
    headOf (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x) 0
        = some (PalPeg.GalilScaffoldChainVerifier.right x.vm.right) ∧
      headOf (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x) 1
        = some (PalPeg.GalilScaffoldChainVerifier.right x.vm.right) ∧
      headOf (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x) 2
        = some (PalPeg.GalilScaffoldChainVerifier.right x.vm.right) ∧
      headOf (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x) 3
        = none := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (unfold PalPeg.GalilScaffoldTop.tickFun
     rw [hmode]
     dsimp only
     rfl)

/-- **the background quantum of the scan leaves the three input cursors where they are.**  It
runs the search, steps the preparation's machinery and writes the chain; the left, the centre and
the right cursor are carried through.

So the only cursor a background tick can move is the chain's verifier, and the only way it moves
is by the chain being born — which is where the mirror of the centre pays for itself. -/
theorem backgroundFun_cursors (P : PalPeg.GalilScaffoldChainInputSupply.Shared) (s : GalilVM) :
    (PalPeg.GalilScaffoldChainInputSupply.backgroundFun P s).left = s.left
      ∧ (PalPeg.GalilScaffoldChainInputSupply.backgroundFun P s).center = s.center
      ∧ (PalPeg.GalilScaffoldChainInputSupply.backgroundFun P s).right = s.right := by
  refine ⟨?_, ?_, ?_⟩
  · unfold PalPeg.GalilScaffoldChainInputSupply.backgroundFun
    rw [PalPeg.GalilScaffoldChainInputSupply.afterBirth_left]
    rfl
  · unfold PalPeg.GalilScaffoldChainInputSupply.backgroundFun
    rw [PalPeg.GalilScaffoldChainInputSupply.afterBirth_center]
    rfl
  · unfold PalPeg.GalilScaffoldChainInputSupply.backgroundFun
    rw [PalPeg.GalilScaffoldChainInputSupply.afterBirth_right]
    rfl

/-- **and while the chain stays idle it leaves the fourth cursor absent.**  `chainAtFun` starts a
chain only when the search reports its period found; until then an idle chain stays idle, so the
background tick has no fourth cursor to move and none to encode.

With `backgroundFun_cursors` this pins the head side of a background tick down to one case: the
tick in which the chain is born.  That case is `heads_atChainBirth`, and the mirror pays for it.
-/
theorem backgroundFun_chain_stillIdle (P : PalPeg.GalilScaffoldChainInputSupply.Shared)
    (s : GalilVM) (hidle : s.chain = PalPeg.GalilScaffoldChainInputSupply.ChainVM.idle)
    (hnotFound : ¬ (PalPeg.GalilScaffoldChainInputSupply.searchEffectFun P false s).search.mode
      = PalPeg.GalilScaffoldSearchFinish.Mode.found) :
    (PalPeg.GalilScaffoldChainInputSupply.backgroundFun P s).chain
      = PalPeg.GalilScaffoldChainInputSupply.ChainVM.idle := by
  unfold PalPeg.GalilScaffoldChainInputSupply.backgroundFun
  rw [PalPeg.GalilScaffoldChainInputSupply.afterBirth_chain]
  show PalPeg.GalilScaffoldChainInputSupply.chainAtFun false
    (decide ((PalPeg.GalilScaffoldChainInputSupply.searchEffectFun P false s).search.mode
      = PalPeg.GalilScaffoldSearchFinish.Mode.found)) _ _ _ _ _ s.chain = _
  rw [hidle]
  show (if decide ((PalPeg.GalilScaffoldChainInputSupply.searchEffectFun P false s).search.mode
      = PalPeg.GalilScaffoldSearchFinish.Mode.found) = true then _ else
    PalPeg.GalilScaffoldChainInputSupply.ChainVM.idle) = _
  rw [if_neg (by simpa using hnotFound)]

/-- **a chain that is not idle is handed to the chain's own step by the background.**  So
the fourth cursor's fate in a background tick is decided in one place, and the row of the
command table has one thing to say about it: whatever that step does to the verifier.

Together with the idle case and with `backgroundFun_cursors`, this is the whole head side
of a background tick, split into its three cases and each localised. -/
theorem backgroundFun_chain_active (P : PalPeg.GalilScaffoldChainInputSupply.Shared)
    (s : GalilVM) (hactive : ¬ s.chain = PalPeg.GalilScaffoldChainInputSupply.ChainVM.idle) :
    (PalPeg.GalilScaffoldChainInputSupply.backgroundFun P s).chain
      = PalPeg.GalilScaffoldChainInputSupply.chainTickFun false s.chain := by
  unfold PalPeg.GalilScaffoldChainInputSupply.backgroundFun
  rw [PalPeg.GalilScaffoldChainInputSupply.afterBirth_chain]
  show PalPeg.GalilScaffoldChainInputSupply.chainAtFun false _ _ _ _ _ _ s.chain = _
  cases hc : s.chain with
  | idle => exact absurd hc hactive
  | copy a b c d e f g => rfl
  | back a b c d e => rfl
  | watch wm => rfl
  | broken wm => rfl

/-- **what a background tick leaves in the search, the preparation's dynamic program, the
lower bound and the preparation's cursor.**  The background writes all four through one
lens and the birth wrapper touches none of them, so each is the corresponding field of
one quantum of the search applied to the state the tick started from.

These are the atoms the non-head side of a background tick is built from.  Naming them
separately is what lets the branch be stated against the tables already proved about the
search and the dynamic program, instead of against a lens. -/
theorem backgroundFun_searchSide (P : PalPeg.GalilScaffoldChainInputSupply.Shared)
    (s : GalilVM) :
    (PalPeg.GalilScaffoldChainInputSupply.backgroundFun P s).search
        = (PalPeg.GalilScaffoldChainInputSupply.searchEffectFun P false s).search
      ∧ (PalPeg.GalilScaffoldChainInputSupply.backgroundFun P s).dp
        = (PalPeg.GalilScaffoldChainInputSupply.searchEffectFun P false s).dp
      ∧ (PalPeg.GalilScaffoldChainInputSupply.backgroundFun P s).lower
        = (PalPeg.GalilScaffoldChainInputSupply.searchEffectFun P false s).lower
      ∧ (PalPeg.GalilScaffoldChainInputSupply.backgroundFun P s).walker
        = (PalPeg.GalilScaffoldChainInputSupply.searchEffectFun P false s).walker := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold PalPeg.GalilScaffoldChainInputSupply.backgroundFun
    rw [PalPeg.GalilScaffoldChainInputSupply.afterBirth_search]
    rfl
  · unfold PalPeg.GalilScaffoldChainInputSupply.backgroundFun
    rw [PalPeg.GalilScaffoldChainInputSupply.afterBirth_dp]
    rfl
  · unfold PalPeg.GalilScaffoldChainInputSupply.backgroundFun
    rw [PalPeg.GalilScaffoldChainInputSupply.afterBirth_lower]
    rfl
  · unfold PalPeg.GalilScaffoldChainInputSupply.backgroundFun
    rw [PalPeg.GalilScaffoldChainInputSupply.afterBirth_walker]
    rfl

/-- **both background arms of a scan tick leave the same machine.**  The two arms differ in
the controller — the clock arm spends one unit of the clock — but the machine they leave is one
background quantum either way, whether the tick was taken because the input cursor has nothing
to read or because the clock still has time on it.

Naming that machine once is what lets the two arms share every lemma below them: the head side,
the counters, and the encoding of the search. -/
theorem tickFun_scan_background_vm (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.scan)
    (hnorestart : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).restartGuard
      x.vm = false)
    (hbackground : (!x.ctl.replaying
        && !(PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).available x.vm)
        = true
      ∨ 1 < x.ctl.clock) :
    (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x).vm
      = PalPeg.GalilScaffoldChainInputSupply.backgroundFun
          (PalPeg.GalilRunSkeleton.PofC centre place entry w) x.vm := by
  unfold PalPeg.GalilScaffoldTop.tickFun
  rw [hmode]
  dsimp only
  rw [if_neg (by rw [hnorestart]; exact Bool.false_ne_true)]
  split
  · rfl
  · rename_i hquiet
    rw [if_pos (hbackground.resolve_left hquiet)]
    rfl

/-- **while the chain stays idle a background tick moves no cursor at all.**  The three input
cursors are the ones `backgroundFun_cursors` leaves alone; the fourth is absent before and after
by `backgroundFun_chain_stillIdle`.

So this arm of the scan is a still tick of the heads, and the twelve head slots carry it with the
same slot machinery as `markEnd`, `home`, `choose` and `copy`. -/
theorem headOf_tickFun_background_stillIdle (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.scan)
    (hnorestart : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).restartGuard
      x.vm = false)
    (hbackground : (!x.ctl.replaying
        && !(PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).available x.vm)
        = true
      ∨ 1 < x.ctl.clock)
    (hidle : x.vm.chain = PalPeg.GalilScaffoldChainInputSupply.ChainVM.idle)
    (hnotFound : ¬ (PalPeg.GalilScaffoldChainInputSupply.searchEffectFun
      (PalPeg.GalilRunSkeleton.PofC centre place entry w) false x.vm).search.mode
        = PalPeg.GalilScaffoldSearchFinish.Mode.found)
    (v : Fin 4) :
    headOf (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x) v
      = headOf x v := by
  have hvm := tickFun_scan_background_vm centre place entry entryQ first w F delay x hmode
    hnorestart hbackground
  refine headOf_congr_of_vm (x := x)
    (y := PalPeg.GalilScaffoldTop.tickFun
      (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
    ?_ ?_ ?_ ?_ v
  · rw [hvm]
    exact (backgroundFun_cursors (PalPeg.GalilRunSkeleton.PofC centre place entry w) x.vm).1
  · rw [hvm]
    exact (backgroundFun_cursors (PalPeg.GalilRunSkeleton.PofC centre place entry w) x.vm).2.1
  · rw [hvm]
    exact (backgroundFun_cursors (PalPeg.GalilRunSkeleton.PofC centre place entry w) x.vm).2.2
  · rw [hvm, backgroundFun_chain_stillIdle (PalPeg.GalilRunSkeleton.PofC centre place entry w) x.vm
      hidle hnotFound, hidle]

/-- **a background tick over a chain that is running touches nothing but the chain.**  The
search takes a quantum only over an idle chain, so over a running chain the search, the
preparation's dynamic program, the lower bound and the preparation's cursor are the ones
the tick started from.

With `backgroundFun_cursors` and `backgroundFun_chain_active` this is the whole of such a
tick: three cursors still, four search fields still, and one chain step.  It is the arm in
which the machine has no program to run — the opposite trade from the idle arm, where the
cursors stand still and the search advances. -/
theorem backgroundFun_searchSide_active (P : PalPeg.GalilScaffoldChainInputSupply.Shared)
    (s : GalilVM) (hactive : ¬ s.chain = PalPeg.GalilScaffoldChainInputSupply.ChainVM.idle) :
    (PalPeg.GalilScaffoldChainInputSupply.backgroundFun P s).search = s.search
      ∧ (PalPeg.GalilScaffoldChainInputSupply.backgroundFun P s).dp = s.dp
      ∧ (PalPeg.GalilScaffoldChainInputSupply.backgroundFun P s).lower = s.lower
      ∧ (PalPeg.GalilScaffoldChainInputSupply.backgroundFun P s).walker = s.walker := by
  have hquiet : PalPeg.GalilScaffoldChainInputSupply.searchEffectFun P false s
      = PalPeg.GalilScaffoldChainInputSupply.searchLens.get s := by
    unfold PalPeg.GalilScaffoldChainInputSupply.searchEffectFun
    cases hc : s.chain with
    | idle => exact absurd hc hactive
    | copy a b c d e f g => rfl
    | back a b c d e => rfl
    | watch wm => rfl
    | broken wm => rfl
  obtain ⟨hsearch, hdp, hlower, hwalker⟩ := backgroundFun_searchSide P s
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsearch, hquiet]; rfl
  · rw [hdp, hquiet]; rfl
  · rw [hlower, hquiet]; rfl
  · rw [hwalker, hquiet]; rfl

/-- **and it leaves the preparation program, the centre and the radius alone in either arm.**
The background writes through two lenses only — the scan's three fields and the search's four —
and the birth wrapper touches neither of these three. -/
theorem backgroundFun_prepSide (P : PalPeg.GalilScaffoldChainInputSupply.Shared) (s : GalilVM) :
    (PalPeg.GalilScaffoldChainInputSupply.backgroundFun P s).fpp = s.fpp
      ∧ (PalPeg.GalilScaffoldChainInputSupply.backgroundFun P s).center = s.center
      ∧ (PalPeg.GalilScaffoldChainInputSupply.backgroundFun P s).radius = s.radius := by
  refine ⟨?_, ?_, ?_⟩
  · unfold PalPeg.GalilScaffoldChainInputSupply.backgroundFun
    rw [PalPeg.GalilScaffoldChainInputSupply.afterBirth_fpp]
    rfl
  · unfold PalPeg.GalilScaffoldChainInputSupply.backgroundFun
    rw [PalPeg.GalilScaffoldChainInputSupply.afterBirth_center]
    rfl
  · unfold PalPeg.GalilScaffoldChainInputSupply.backgroundFun
    rw [PalPeg.GalilScaffoldChainInputSupply.afterBirth_radius]
    rfl

/-- **a comparison hands a running chain to the chain's own step.**  The birth arm of the
table is reached only from an idle chain, so on every other chain the table is one step of
the chain and the answer tape, the centre and the radius it was handed go unread. -/
theorem chainAtFun_of_active (found : Bool) (answer : PalPeg.GalilScaffoldTape.Tape)
    (c : Fin 3) (walker : PalPeg.GalilScaffoldPlace.Place)
    (ver : PalPeg.GalilScaffoldInputHead.PlaceHead) (radius : PalPeg.GalilScaffoldCounter.Counter)
    (x : PalPeg.GalilScaffoldChainInputSupply.ChainVM)
    (hactive : ¬ x = PalPeg.GalilScaffoldChainInputSupply.ChainVM.idle) :
    PalPeg.GalilScaffoldChainInputSupply.chainAtFun false found answer c walker ver radius x
      = PalPeg.GalilScaffoldChainInputSupply.chainStepFun x := by
  cases x with
  | idle => exact absurd rfl hactive
  | copy a b d e f g h => rfl
  | back a b d e f => rfl
  | watch wm => rfl
  | broken wm => rfl

/-- **a background tick that finds the chain standing is the identity.**  Over a running chain
the search takes no quantum and the background writes back the three scan fields it read; so if
the chain's own step leaves the chain where it was, the tick leaves the whole machine where it
was.

This covers the watching chain with no lag to spend and the one whose verdict the period tape
withholds, and every copy step the answer tape refuses.  For the encoding it is the cheapest
branch there is: the machine's scan row does nothing either. -/
theorem backgroundFun_id_of_chainFixed (P : PalPeg.GalilScaffoldChainInputSupply.Shared)
    (s : GalilVM) (hactive : ¬ s.chain = PalPeg.GalilScaffoldChainInputSupply.ChainVM.idle)
    (hfixed : PalPeg.GalilScaffoldChainInputSupply.chainStepFun s.chain = s.chain) :
    PalPeg.GalilScaffoldChainInputSupply.backgroundFun P s = s := by
  have hget : PalPeg.GalilScaffoldChainInputSupply.searchEffectFun P false s
      = PalPeg.GalilScaffoldChainInputSupply.searchLens.get s := by
    unfold PalPeg.GalilScaffoldChainInputSupply.searchEffectFun
    cases hc : s.chain with
    | idle => exact absurd hc hactive
    | copy a b d e f g h => rfl
    | back a b d e f => rfl
    | watch wm => rfl
    | broken wm => rfl
  unfold PalPeg.GalilScaffoldChainInputSupply.backgroundFun
  rw [PalPeg.GalilScaffoldChainInputSupply.afterBirth_of_ne_idle (s := s) hactive,
    chainAtFun_of_active _ _ _ _ _ _ s.chain hactive, hfixed]
  show PalPeg.GalilScaffoldChainInputSupply.searchLens.set
    (PalPeg.GalilScaffoldChainInputSupply.scanLens.set s
      (PalPeg.GalilScaffoldChainInputSupply.scanLens.get s))
    (PalPeg.GalilScaffoldChainInputSupply.searchEffectFun P false s) = s
  rw [hget, PalPeg.GalilScaffoldChainInputSupply.scanLens.set_get]
  exact PalPeg.GalilScaffoldChainInputSupply.searchLens.set_get s

/-- **a chain in any other shape does not consume.**  The tag alone decides it, and the control
holds the tag, so this needs nothing from the tapes. -/
theorem chainConsumesTest_of_tag_ne {fppBound dpBound K : ℕ} (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (htag : ¬ q.chainTag = ChainTag.watchers) : chainConsumesTest q ws = false := by
  unfold chainConsumesTest
  rw [decide_eq_false htag]
  rfl

/-- **and a watching chain with no lag to spend does not consume either.**  The lag is the
eleventh counter, so the reading that decides it is the sign bit the control holds together with
the cell below that counter's head. -/
theorem chainConsumesTest_of_lag_zero {margin K fppBound dpBound : ℕ} {x : State GalilVM}
    {q : QPhys fppBound dpBound} {T : Slot → STape Γm}
    (henc : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T)
    (hK1 : 1 ≤ K) (hK : K ≤ margin)
    (wm : PalPeg.GalilScaffoldChainWatch.State)
    (hchain : x.vm.chain = PalPeg.GalilScaffoldChainInputSupply.ChainVM.watch wm)
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = false) :
    chainConsumesTest q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) = false := by
  have hvalue : counterOf x 11 = some wm.lag := by
    show (match x.vm.chain with
      | .copy _ _ _ _ lag _ _ => some lag
      | .back _ _ lag _ _ => some lag
      | .watch w => some w.lag
      | .broken w => some w.lag
      | _ => none) = some wm.lag
    rw [hchain]
  have hiff := counterPositive_iff_belowRead henc hK1 hK 11 wm.lag hvalue
  have hnot : ¬ (q.polarity 11 = true
      ∧ belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) (counterSlot 11)
          = encSeg PalPeg.LocalCounter.mark) := by
    intro hboth
    rw [hiff.mpr hboth] at hlag
    exact Bool.noConfusion hlag
  unfold chainConsumesTest
  rcases hpol : q.polarity 11 with _ | _
  · simp
  · have hbelow : ¬ belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
        (counterSlot 11) = encSeg PalPeg.LocalCounter.mark := fun h => hnot ⟨hpol, h⟩
    rw [decide_eq_false hbelow]
    simp

/-- **and then the scan's row is the row that moves nothing.**  Which is what lets the branch be
carried by the same slot machinery as the five still modes. -/
theorem scanCommands_eq_stay {fppBound dpBound K : ℕ} (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hquiet : chainConsumesTest q ws = false) : scanCommands q ws = stayCommands := by
  unfold scanCommands
  funext v
  rw [hquiet]
  split <;> rfl

/-- **the machine's scan row writes nothing and changes no word.**  The scan reads the input
through its comparison, so the branch that stands still leaves the control where it was and
spends the tick on the background erasure of the idle program half. -/
theorem physRule_nq_scan {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9)
    (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K) (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hm : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.scan)
    (hquiet : chainConsumesTest q ws = false) :
    (physRule (dpBound := dpBound) entryQ first hbound hK).nq q none ws = q := by
  show ruleNext entryQ first hbound q ws = _
  unfold ruleNext
  rw [hm]
  dsimp only
  rw [if_neg (by rw [hquiet]; exact Bool.false_ne_true)]

theorem physRule_acts_scan {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9)
    (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K) (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hm : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.scan)
    (hquiet : chainConsumesTest q ws = false) :
    (physRule (dpBound := dpBound) entryQ first hbound hK).acts q none ws
      = withErase q.fppLive ws (fun _ => []) := by
  show ruleActs entryQ first q ws = _
  unfold ruleActs
  rw [hm]
  dsimp only
  rw [scanConsumeActs_of_quiet q ws hquiet]

/-- **the quiet arm of the scan, as a state.**  The arm taken because the input cursor has
nothing left to read keeps the controller's whole word, clock included. -/
theorem tickFun_scan_background_quiet (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.scan)
    (hnorestart : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).restartGuard
      x.vm = false)
    (hquiet : (!x.ctl.replaying
      && !(PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).available x.vm)
        = true) :
    PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x
      = ⟨x.ctl, PalPeg.GalilScaffoldChainInputSupply.backgroundFun
          (PalPeg.GalilRunSkeleton.PofC centre place entry w) x.vm⟩ := by
  unfold PalPeg.GalilScaffoldTop.tickFun
  rw [hmode]
  dsimp only
  rw [if_neg (by rw [hnorestart]; exact Bool.false_ne_true), if_pos hquiet]
  rfl

/-- **the quiet scan tick over a standing chain, of the machine itself.**  Nothing in the
abstract state moves, and the machine answers with the erasure and no other action, so the
encoding after the step is the encoding before it with the idle program half walked back. -/
theorem physRule_background_still {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K) (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.scan)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.scan)
    (hnorestart : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).restartGuard
      x.vm = false)
    (hquiet : (!x.ctl.replaying
      && !(PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).available x.vm)
        = true)
    (hid : PalPeg.GalilScaffoldChainInputSupply.backgroundFun
      (PalPeg.GalilRunSkeleton.PofC centre place entry w) x.vm = x.vm)
    (hnoconsume : chainConsumesTest q
      (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) = false)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hK) blankM
          (q, tapesOf T) none).1,
        fun i => (PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hK)
          blankM (q, tapesOf T) none).2 (slotIndex i)) := by
  have htick : PalPeg.GalilScaffoldTop.tickFun
      (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x = x := by
    rw [tickFun_scan_background_quiet centre place entry entryQ first w F delay x hmode hnorestart
      hquiet, hid]
  have hacts : (physRule (dpBound := dpBound) entryQ first hbound hK).acts q none
      (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      = withErase q.fppLive (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (fun _ => []) :=
    physRule_acts_scan entryQ first hbound hK q _ hqmode hnoconsume
  have hkeptAll : ∀ slot : Slot, (∀ k : Fin 9, slot ≠ progSlotOf (!q.fppLive) k) →
      (PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hK)
          blankM (q, tapesOf T) none).2 (slotIndex slot) = T slot := by
    intro slot hslot
    rw [idealStep_withErase (physRule (dpBound := dpBound) entryQ first hbound hK) q T q.fppLive
      _ hacts slot hslot]
    rfl
  have hq : (PalPeg.LocalStepFusion.idealStep (physRule (dpBound := dpBound) entryQ first hbound hK)
      blankM (q, tapesOf T) none).1 = q :=
    physRule_nq_scan entryQ first hbound hK q _ hqmode hnoconsume
  rw [htick, hq]
  exact ⟨henc.1, encTapes_idleOnly margin x q.polarity q.gap q.micro q.fppLive q.dpLive T _
    henc.2 hkeptAll
    (idle_shape_after_erase margin hK1 hKn (physRule (dpBound := dpBound) entryQ first hbound hK)
      q T q.fppLive _ hacts (fun _ => rfl) henc.2.idleShape)⟩

/-- **the quiet scan tick over a standing chain, carried through the twelve slots.**  Nothing in
the abstract state moves: the input cursor has nothing to read, the chain's own step leaves it
where it was, and the search takes no quantum over a running chain.  The row the command table
gives that tick is the row that moves nothing, so the twelve slots carry it with the same
machinery as the five still modes.

This is the first arm of the scan to be carried end to end.  What it costs the machine is the
background erasure of the idle program half and nothing else.

Two ways a tick can stand still feed it: `backgroundFun_id_of_chainFixed`, a running chain whose
own step leaves it where it was, and `backgroundFun_id_of_searchAtRest`, an idle chain with the
search stopped. -/
theorem background_still_of_tick {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (rest : QPhys fppBound dpBound → Option (Fin 2) →
      (Fin tapeCountM → PalPeg.Local.Window Γm K) → Fin 4 →
      PalPeg.ConcreteLocalMachine.ViewCommand)
    (input : Option (Fin 2))
    (hbound : 320 < fppBound) (hKb : entryQ + 3 ≤ K) (hK2 : 2 ≤ K) (hK1 : 1 ≤ K)
    (hK : K ≤ margin) (hslot0 : q.slot.val = 0) (howed : ∀ v, (q.micro v).2.2.2 = 0)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.scan)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.scan)
    (hnorestart : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).restartGuard
      x.vm = false)
    (hquiet : (!x.ctl.replaying
      && !(PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).available x.vm)
        = true)
    (hid : PalPeg.GalilScaffoldChainInputSupply.backgroundFun
      (PalPeg.GalilRunSkeleton.PofC centre place entry w) x.vm = x.vm)
    (hnoconsume : chainConsumesTest q
      (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) = false)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hKb hK2 rest) blankM
          (q, tapesOf T) input 12).1,
        fun i => (PalPeg.LocalStepFusion.idealRun
          (tickPhysRule entryQ first hbound hKb hK2 rest) blankM (q, tapesOf T) input 12).2
            (slotIndex i)) := by
  have htick : PalPeg.GalilScaffoldTop.tickFun
      (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x = x := by
    rw [tickFun_scan_background_quiet centre place entry entryQ first w F delay x hmode hnorestart
      hquiet, hid]
  exact enc_ofBranchStep_stay margin entryQ first hbound hKb hK2 hK rest w x
    (PalPeg.GalilScaffoldTop.tickFun
      (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x) q T input
    hslot0
    (by
      unfold modeCommands
      rw [hqmode]
      exact scanCommands_eq_stay q _ hnoconsume)
    howed (fun v => by rw [htick]) henc.2
    (physRule_background_still margin centre place entry entryQ first w F delay x q T hbound hKb
      hK1 (by omega) hqmode hmode hnorestart hquiet hid hnoconsume henc)

/-- **a background tick with the search at rest and no chain to run is the identity too.**  The
search steps only in the seven modes that are looking for the period; in the three that have
stopped — before it starts, when it has found one, and when it has given up — the quantum is the
identity, and with an idle chain there is nothing else for the tick to do.

Two of those three are branches of the scan: the one before the search starts and the one after
it has given up.  The third is the tick that gives birth to a chain, and that one moves. -/
theorem backgroundFun_id_of_searchAtRest (P : PalPeg.GalilScaffoldChainInputSupply.Shared)
    (s : GalilVM) (hidle : s.chain = PalPeg.GalilScaffoldChainInputSupply.ChainVM.idle)
    (hrest : s.search.mode = PalPeg.GalilScaffoldSearchFinish.Mode.idle
      ∨ s.search.mode = PalPeg.GalilScaffoldSearchFinish.Mode.missed) :
    PalPeg.GalilScaffoldChainInputSupply.backgroundFun P s = s := by
  have hmode : (PalPeg.GalilScaffoldChainInputSupply.searchLens.get s).search.mode
      = s.search.mode := rfl
  have hstep : PalPeg.GalilScaffoldChainInputSupply.searchEffectFun P false s
      = PalPeg.GalilScaffoldChainInputSupply.searchLens.get s := by
    unfold PalPeg.GalilScaffoldChainInputSupply.searchEffectFun
    rw [hidle]
    show PalPeg.GalilScaffoldChainInputSupply.searchStepFun (P.place s) false
      (PalPeg.GalilScaffoldChainInputSupply.searchLens.get s) = _
    unfold PalPeg.GalilScaffoldChainInputSupply.searchStepFun
    rw [hmode]
    rcases hrest with h | h <;> rw [h]
  have hnotFound : ¬ (PalPeg.GalilScaffoldChainInputSupply.searchEffectFun P false s).search.mode
      = PalPeg.GalilScaffoldSearchFinish.Mode.found := by
    rw [hstep, hmode]
    rcases hrest with h | h <;> rw [h] <;> exact fun hEq => by cases hEq
  unfold PalPeg.GalilScaffoldChainInputSupply.backgroundFun
  rw [show PalPeg.GalilScaffoldChainInputSupply.chainBorn
      (decide ((PalPeg.GalilScaffoldChainInputSupply.searchEffectFun P false s).search.mode
        = PalPeg.GalilScaffoldSearchFinish.Mode.found)) s.chain = false by
    unfold PalPeg.GalilScaffoldChainInputSupply.chainBorn
    rw [decide_eq_false hnotFound]
    exact Bool.and_false _,
    PalPeg.GalilScaffoldChainInputSupply.afterBirth_false]
  show PalPeg.GalilScaffoldChainInputSupply.searchLens.set
    (PalPeg.GalilScaffoldChainInputSupply.scanLens.set s
      ⟨s.left, s.right, PalPeg.GalilScaffoldChainInputSupply.chainAtFun false
        (decide ((PalPeg.GalilScaffoldChainInputSupply.searchEffectFun P false s).search.mode
          = PalPeg.GalilScaffoldSearchFinish.Mode.found))
        ((PalPeg.GalilScaffoldChainInputSupply.searchEffectFun P false s).dp.config.tapes 11)
        (P.centre s) (P.place s) s.center s.radius s.chain⟩)
    (PalPeg.GalilScaffoldChainInputSupply.searchEffectFun P false s) = s
  rw [decide_eq_false hnotFound, hidle]
  show PalPeg.GalilScaffoldChainInputSupply.searchLens.set
    (PalPeg.GalilScaffoldChainInputSupply.scanLens.set s
      ⟨s.left, s.right, PalPeg.GalilScaffoldChainInputSupply.ChainVM.idle⟩)
    (PalPeg.GalilScaffoldChainInputSupply.searchEffectFun P false s) = s
  rw [hstep, ← hidle]
  show PalPeg.GalilScaffoldChainInputSupply.searchLens.set
    (PalPeg.GalilScaffoldChainInputSupply.scanLens.set s
      (PalPeg.GalilScaffoldChainInputSupply.scanLens.get s))
    (PalPeg.GalilScaffoldChainInputSupply.searchLens.get s) = s
  rw [PalPeg.GalilScaffoldChainInputSupply.scanLens.set_get]
  exact PalPeg.GalilScaffoldChainInputSupply.searchLens.set_get s

/-- **a watching chain that consumes steps its verifier right, whichever way the verdict goes.**
A match consumes the letter the verifier has moved to and a mismatch breaks the chain on it, so
the two arms leave the cursor in the same place and differ only in the chain's shape.

This is why the scan's row can be decided without reading the verdict: the row says where the
cursor goes, and both verdicts send it to the same place. -/
theorem headOf_three_of_watchConsume {y : State GalilVM}
    (wm : PalPeg.GalilScaffoldChainWatch.State)
    (hchain : y.vm.chain = PalPeg.GalilScaffoldChainInputSupply.chainStepFun
      (PalPeg.GalilScaffoldChainInputSupply.ChainVM.watch wm))
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = true) (b : Bool)
    (hverdict : PalPeg.GalilScaffoldChainInputSupply.watchVerdict wm = some b) :
    headOf y 3 = some (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) := by
  show (match y.vm.chain with
    | .idle => none
    | .copy _ _ _ _ _ _ verifier => some verifier
    | .back _ _ _ _ verifier => some verifier
    | .watch v => some v.machine.verifier
    | .broken v => some v.machine.verifier) = _
  rw [hchain]
  simp only [PalPeg.GalilScaffoldChainInputSupply.chainStepFun]
  rw [if_pos hlag, hverdict]
  cases b with
  | true => rfl
  | false => rfl

/-- **a match keeps the chain watching and hands its control one letter.**  The period tape's
focus decides whether that letter closes a block, and that is the whole of what moves in the
control word: the phase advances and the direction is reset on a boundary, and the broken bit
stays down.

The machine reads that focus as the centre cell of the period slot, so the row writes the same
word the chain does. -/
theorem scanConsumeNext_of_match {fppBound dpBound K : ℕ} (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (wm : PalPeg.GalilScaffoldChainWatch.State)
    (htest : watchVerdictTest q ws = PalPeg.GalilScaffoldChainInputSupply.watchVerdict wm)
    (hverdict : PalPeg.GalilScaffoldChainInputSupply.watchVerdict wm = some true)
    (htag : q.chainTag = ChainTag.watchers)
    (htoken : decToken (centreRead ws periodSlot) = wm.machine.control.period.focus)
    (hphase : q.chainPhase = wm.machine.control.phase)
    (hforward : q.chainForward = wm.machine.control.forward)
    (hbroken : q.chainBroken = wm.machine.control.broken)
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = true) :
    (scanConsumeNext q ws).chainTag
        = chainTagOf (PalPeg.GalilScaffoldChainInputSupply.chainStepFun
            (PalPeg.GalilScaffoldChainInputSupply.ChainVM.watch wm))
      ∧ chainConsumeOf (PalPeg.GalilScaffoldChainInputSupply.chainStepFun
            (PalPeg.GalilScaffoldChainInputSupply.ChainVM.watch wm))
          = ((scanConsumeNext q ws).chainPhase, (scanConsumeNext q ws).chainForward,
            (scanConsumeNext q ws).chainBroken) := by
  have hsame : (match PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus with
      | none => false
      | some a => decide (PalPeg.GalilScaffoldInputHead.read
          (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) = some a)) = true := by
    unfold PalPeg.GalilScaffoldChainInputSupply.watchVerdict at hverdict
    cases hs : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus with
    | none => rw [hs] at hverdict; exact absurd hverdict (by simp)
    | some a =>
        rw [hs] at hverdict
        exact Option.some.inj hverdict
  have hstep : PalPeg.GalilScaffoldChainInputSupply.chainStepFun
      (PalPeg.GalilScaffoldChainInputSupply.ChainVM.watch wm)
      = PalPeg.GalilScaffoldChainInputSupply.ChainVM.watch
          (PalPeg.GalilScaffoldChainWatch.caught wm) := by
    simp only [PalPeg.GalilScaffoldChainInputSupply.chainStepFun]
    rw [if_pos hlag, hverdict]
  have hcontrol : (PalPeg.GalilScaffoldChainWatch.caught wm).machine.control
      = PalPeg.GalilScaffoldChainConsume.consume wm.machine.control
          (PalPeg.GalilScaffoldInputHead.read
            (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier)) := rfl
  have hnext : scanConsumeNext q ws
      = { q with
          chainPhase :=
            if PalPeg.GalilScaffoldChainPeriod.isFirst wm.machine.control.period.focus
                || PalPeg.GalilScaffoldChainConsume.isLast wm.machine.control.period.focus then
              PalPeg.GalilScaffoldChainConsume.advancePhase q.chainPhase
            else q.chainPhase,
          chainForward :=
            if PalPeg.GalilScaffoldChainPeriod.isFirst wm.machine.control.period.focus
                || PalPeg.GalilScaffoldChainConsume.isLast wm.machine.control.period.focus then
              PalPeg.GalilScaffoldChainPeriod.isFirst wm.machine.control.period.focus
            else q.chainForward,
          polarity := Function.update
            (Function.update q.polarity 11 (decSignAt (q.polarity 11) (counterSlot 11) ws))
            13 (incSign q.polarity 13 ws) } := by
    unfold scanConsumeNext
    rw [htest, hverdict, htoken]
  refine ⟨?_, ?_⟩
  · rw [hnext, hstep, htag]
    rfl
  · rw [hnext, hstep]
    show chainConsumeOf (PalPeg.GalilScaffoldChainInputSupply.ChainVM.watch
      (PalPeg.GalilScaffoldChainWatch.caught wm)) = _
    simp only [chainConsumeOf]
    rw [hcontrol]
    cases hs : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus with
    | none =>
        rw [hs] at hsame
        exact absurd hsame (by simp)
    | some a =>
        rw [hs] at hsame
        simp only [PalPeg.GalilScaffoldChainConsume.consume, hs]
        rw [if_pos hsame, hphase, hforward, hbroken]

/-- **a mismatch breaks the chain and leaves its control alone.**  The broken chain carries the
control it had, on the letter the verifier has already moved to, so the only field of the control
word that changes is the tag. -/
theorem scanConsumeNext_of_mismatch {fppBound dpBound K : ℕ} (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (wm : PalPeg.GalilScaffoldChainWatch.State)
    (htest : watchVerdictTest q ws = PalPeg.GalilScaffoldChainInputSupply.watchVerdict wm)
    (hverdict : PalPeg.GalilScaffoldChainInputSupply.watchVerdict wm = some false)
    (hphase : q.chainPhase = wm.machine.control.phase)
    (hforward : q.chainForward = wm.machine.control.forward)
    (hbroken : q.chainBroken = wm.machine.control.broken)
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = true) :
    (scanConsumeNext q ws).chainTag
        = chainTagOf (PalPeg.GalilScaffoldChainInputSupply.chainStepFun
            (PalPeg.GalilScaffoldChainInputSupply.ChainVM.watch wm))
      ∧ chainConsumeOf (PalPeg.GalilScaffoldChainInputSupply.chainStepFun
            (PalPeg.GalilScaffoldChainInputSupply.ChainVM.watch wm))
          = ((scanConsumeNext q ws).chainPhase, (scanConsumeNext q ws).chainForward,
            (scanConsumeNext q ws).chainBroken) := by
  have hstep : PalPeg.GalilScaffoldChainInputSupply.chainStepFun
      (PalPeg.GalilScaffoldChainInputSupply.ChainVM.watch wm)
      = PalPeg.GalilScaffoldChainInputSupply.ChainVM.broken
          ⟨⟨PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier, wm.machine.control⟩,
            wm.lag, wm.margin⟩ := by
    simp only [PalPeg.GalilScaffoldChainInputSupply.chainStepFun]
    rw [if_pos hlag, hverdict]
  have hnext : scanConsumeNext q ws = { q with chainTag := ChainTag.broken } := by
    unfold scanConsumeNext
    rw [htest, hverdict]
  refine ⟨?_, ?_⟩
  · rw [hnext, hstep]
    rfl
  · rw [hnext, hstep, hphase, hforward, hbroken]
    rfl

/-- the blank of the period tape is the blank of the machine. -/
theorem encToken_blank : encToken Token.blank = blankM := if_pos rfl

/-- **a step right on the period tape is one action.**  The symbol written back is the one the
head already carries, so the action moves the head and changes nothing. -/
theorem padded_token_right (n : ℕ) (tokens : STape Token) (written : Token) :
    padLeft n (mapTape encToken (STape.applyAction Token.blank tokens (written, .right)))
      = (padLeft n (mapTape encToken tokens)).applyAction blankM (encToken written, .right) := by
  rw [mapTape_applyAction encToken encToken_blank tokens written .right,
    padLeft_applyAction_right]

/-- **and the chain's own step right is that action.**  The period tape is a zipper that pads
with its blank on the right, which is what the machine's tape does too. -/
theorem encPeriod_moveRight (t : PalPeg.GalilScaffoldChainPeriod.Tape) :
    encPeriod (PalPeg.GalilScaffoldChainPeriod.moveRight t)
      = STape.applyAction Token.blank (encPeriod t) (t.focus, .right) := by
  unfold PalPeg.GalilScaffoldChainPeriod.moveRight encPeriod
  cases hr : t.right with
  | nil => rfl
  | cons a rs => rfl

/-- **what a consuming scan tick does to the four cursors.**  The three input cursors stand
still — a background tick never walks them — and the fourth steps right, whichever way the
verdict goes.

This is the head side of the consuming arm, in the form the tick's slot machinery asks for: one
command per cursor, and for the fourth the place it lands. -/
theorem headOf_tickFun_scan_consume (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.scan)
    (hnorestart : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).restartGuard
      x.vm = false)
    (hbackground : (!x.ctl.replaying
        && !(PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).available x.vm)
        = true
      ∨ 1 < x.ctl.clock)
    (wm : PalPeg.GalilScaffoldChainWatch.State)
    (hchain : x.vm.chain = PalPeg.GalilScaffoldChainInputSupply.ChainVM.watch wm)
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = true) (b : Bool)
    (hverdict : PalPeg.GalilScaffoldChainInputSupply.watchVerdict wm = some b) :
    (∀ v : Fin 4, v ≠ 3 → headOf (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x) v
          = headOf x v)
      ∧ headOf (PalPeg.GalilScaffoldTop.tickFun
          (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x) 3
        = some (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) := by
  have hvm := tickFun_scan_background_vm centre place entry entryQ first w F delay x hmode
    hnorestart hbackground
  have hactive : ¬ x.vm.chain = PalPeg.GalilScaffoldChainInputSupply.ChainVM.idle := by
    rw [hchain]
    exact fun h => PalPeg.GalilScaffoldChainInputSupply.ChainVM.noConfusion h
  obtain ⟨hleft, hcentre, hright⟩ :=
    backgroundFun_cursors (PalPeg.GalilRunSkeleton.PofC centre place entry w) x.vm
  refine ⟨?_, ?_⟩
  · intro v hv
    fin_cases v
    · show some _ = some _
      rw [hvm, hleft]
    · show some _ = some _
      rw [hvm, hcentre]
    · show some _ = some _
      rw [hvm, hright]
    · exact absurd rfl hv
  · refine headOf_three_of_watchConsume wm ?_ hlag b hverdict
    rw [hvm, backgroundFun_chain_active (PalPeg.GalilRunSkeleton.PofC centre place entry w) x.vm
      hactive, hchain]
    rfl

/-- **the chain with its verifier put back where it was.**  The state the step reaches, for a
tick in which the chain consumes: everything the step's table writes is already here — the lag it
spent, the distance it counted, the period tape it walked — and only the cursor is still where it
started.  The tick reaches this state's cursor one slot-run later.

This is the second state `enc_afterTickOfState` asks for, and it is the chain's own shape with
one field replaced, so every reading but the cursor agrees with the tick's state by definition. -/
def chainVerifierBack (c : PalPeg.GalilScaffoldChainInputSupply.ChainVM)
    (ver : PalPeg.GalilScaffoldInputHead.PlaceHead) :
    PalPeg.GalilScaffoldChainInputSupply.ChainVM :=
  match c with
  | .watch w => .watch ⟨⟨ver, w.machine.control⟩, w.lag, w.margin⟩
  | .broken w => .broken ⟨⟨ver, w.machine.control⟩, w.lag, w.margin⟩
  | other => other

/-- the state the step reaches, written out. -/
def stepState (y : State GalilVM) (ver : PalPeg.GalilScaffoldInputHead.PlaceHead) :
    State GalilVM :=
  ⟨y.ctl, {y.vm with chain := chainVerifierBack y.vm.chain ver}⟩

/-- **putting the verifier back changes nothing the counters see.**  The lag, the margin and the
chain's three block counters live in the control and in the watch's own fields, and the cursor is
neither. -/
theorem counterOf_stepState (y : State GalilVM)
    (ver : PalPeg.GalilScaffoldInputHead.PlaceHead) :
    counterOf y = counterOf (stepState y ver) := by
  funext c
  cases hc : y.vm.chain <;> fin_cases c <;>
    simp [counterOf, stepState, chainVerifierBack, hc]

theorem periodOf_stepState (y : State GalilVM)
    (ver : PalPeg.GalilScaffoldInputHead.PlaceHead) :
    periodOf y = periodOf (stepState y ver) := by
  cases hc : y.vm.chain <;> simp [periodOf, stepState, chainVerifierBack, hc]

theorem answerOf_stepState (y : State GalilVM)
    (ver : PalPeg.GalilScaffoldInputHead.PlaceHead) :
    answerOf y = answerOf (stepState y ver) := by
  cases hc : y.vm.chain <;> simp [answerOf, stepState, chainVerifierBack, hc]

theorem placeOf_stepState (y : State GalilVM)
    (ver : PalPeg.GalilScaffoldInputHead.PlaceHead) :
    placeOf y = placeOf (stepState y ver) := by
  funext i
  cases hc : y.vm.chain <;> fin_cases i <;>
    simp [placeOf, stepState, chainVerifierBack, hc]

/-- **and the cursor is exactly the one put back.**  Which is the whole of what the two states
differ in. -/
theorem headOf_stepState_three (y : State GalilVM)
    (ver : PalPeg.GalilScaffoldInputHead.PlaceHead) (wm : PalPeg.GalilScaffoldChainWatch.State)
    (hchain : y.vm.chain = PalPeg.GalilScaffoldChainInputSupply.ChainVM.watch wm) :
    headOf (stepState y ver) 3 = some ver := by
  show (match (stepState y ver).vm.chain with
    | .idle => none
    | .copy _ _ _ _ _ _ verifier => some verifier
    | .back _ _ _ _ verifier => some verifier
    | .watch v => some v.machine.verifier
    | .broken v => some v.machine.verifier) = _
  show (match chainVerifierBack y.vm.chain ver with
    | .idle => none
    | .copy _ _ _ _ _ _ verifier => some verifier
    | .back _ _ _ _ verifier => some verifier
    | .watch v => some v.machine.verifier
    | .broken v => some v.machine.verifier) = _
  rw [hchain]
  rfl

/-- **the lag's tape after a consuming tick.**  The step's table pops the chain's lag, and the
bit it branches on is the one the counter's own window gives — so the tape it leaves holds one
less than it did, under the sign the control now carries. -/
theorem scanConsume_lagTape {fppBound dpBound K : ℕ} (margin entryQ : ℕ) (first : Fin 9)
    (hbound : 320 < fppBound) (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.scan)
    (hconsume : chainConsumesTest q
      (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) = true)
    (hmatch : watchVerdictTest q
      (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) = some true)
    (lag : PalPeg.GalilScaffoldCounter.Counter) (hlag : counterOf x 11 = some lag)
    (henc : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T) :
    ∃ seg : STape Seg,
      absCtr seg (decSignAt (q.polarity 11) (counterSlot 11)
          (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)))
        = PalPeg.GalilScaffoldCounter.dec lag
      ∧ PalPeg.CloseoutCoreEnc12.actList blankM (T (counterSlot 11))
          (ruleActs entryQ first q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
            (slotIndex (counterSlot 11)))
        = padLeft margin (mapTape encSeg seg) := by
  obtain ⟨segments, habs, hslot⟩ := henc.counters 11 lag hlag
  obtain ⟨seg, habsDec, htape⟩ :=
    counter_dec_at (margin := margin) q.polarity 11
      (decSignAt (q.polarity 11) (counterSlot 11)
        (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)))
      segments lag habs
      (decSignAt_eq hK1 hKn (q.polarity 11) 11 T segments hslot)
      (T (counterSlot 11)) hslot
  refine ⟨seg, habsDec, ?_⟩
  have hacts : ruleActs entryQ first q
      (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (slotIndex (counterSlot 11))
      = [decAct q 11 (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))] := by
    unfold ruleActs
    rw [hqmode]
    dsimp only
    rw [withErase_at_other q.fppLive _ _ (counterSlot 11)
      (by intro k; cases q.fppLive <;> simp [progSlotOf, counterSlot]),
      scanConsumeActs_lag q _ hconsume hmatch]
  rw [hacts]
  exact htape

/-- **the distance's tape after a consuming tick.**  One more letter of the block, counted the
way every increment is counted. -/
theorem scanConsume_distanceTape {fppBound dpBound K : ℕ} (margin entryQ : ℕ) (first : Fin 9)
    (hbound : 320 < fppBound) (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.scan)
    (hconsume : chainConsumesTest q
      (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) = true)
    (hmatch : watchVerdictTest q
      (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) = some true)
    (dist : PalPeg.GalilScaffoldCounter.Counter) (hdist : counterOf x 13 = some dist)
    (henc : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T) :
    ∃ seg : STape Seg,
      absCtr seg (incSign q.polarity 13
          (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)))
        = PalPeg.GalilScaffoldCounter.inc dist
      ∧ PalPeg.CloseoutCoreEnc12.actList blankM (T (counterSlot 13))
          (ruleActs entryQ first q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
            (slotIndex (counterSlot 13)))
        = padLeft margin (mapTape encSeg seg) := by
  obtain ⟨segments, habs, hslot⟩ := henc.counters 13 dist hdist
  obtain ⟨seg, habsInc, htape⟩ :=
    counter_inc_at (margin := margin) q.polarity 13
      (incSign q.polarity 13 (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)))
      segments dist habs
      (incSign_eq hK1 hKn q.polarity 13 T segments hslot)
      (T (counterSlot 13)) hslot
  refine ⟨seg, habsInc, ?_⟩
  have hacts : ruleActs entryQ first q
      (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (slotIndex (counterSlot 13))
      = [incAct q 13 (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))] := by
    unfold ruleActs
    rw [hqmode]
    dsimp only
    rw [withErase_at_other q.fppLive _ _ (counterSlot 13)
      (by intro k; cases q.fppLive <;> simp [progSlotOf, counterSlot]),
      scanConsumeActs_distance q _ hconsume hmatch]
  rw [hacts]
  exact htape

/-- **the period tape after a consuming tick, when the chain walks it right.**  The action writes
back the symbol already under the head and steps, which is what the chain's own step does. -/
theorem scanConsume_periodTape {fppBound dpBound K : ℕ} (margin entryQ : ℕ) (first : Fin 9)
    (hbound : 320 < fppBound) (hK : K ≤ margin)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.scan)
    (hconsume : chainConsumesTest q
      (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) = true)
    (hmatch : watchVerdictTest q
      (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) = some true)
    (hforward : (scanConsumeNext q
      (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).chainForward = true)
    (tape : PalPeg.GalilScaffoldChainPeriod.Tape) (hperiod : periodOf x = some tape)
    (henc : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T) :
    PalPeg.CloseoutCoreEnc12.actList blankM (T periodSlot)
        (ruleActs entryQ first q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (slotIndex periodSlot))
      = padLeft margin (mapTape encToken
          (encPeriod (PalPeg.GalilScaffoldChainPeriod.moveRight tape))) := by
  have hslot : T periodSlot = padLeft margin (mapTape encToken (encPeriod tape)) :=
    henc.period tape hperiod
  have hcentre : centreRead (fun t => PalPeg.Local.readWin blankM K (tapesOf T t)) periodSlot
      = encToken (encPeriod tape).focus := centreRead_periodSlot henc hK tape hperiod
  have hacts : ruleActs entryQ first q
      (fun t => PalPeg.Local.readWin blankM K (tapesOf T t)) (slotIndex periodSlot)
      = [some (encToken (encPeriod tape).focus, (.right : PalPeg.CloseoutCoreEnc12.MoveC))] := by
    unfold ruleActs
    rw [hqmode]
    dsimp only
    rw [withErase_at_other q.fppLive _ _ periodSlot
      (by intro k; cases q.fppLive <;> simp [progSlotOf, periodSlot]),
      scanConsumeActs_period q _ hconsume hmatch, hcentre, hforward, if_pos rfl]
  rw [hacts, encPeriod_moveRight, padded_token_right, ← hslot]
  rfl

/-- **the consumed control, when the letter is a plain one of the block.**  A letter that does
not close a block leaves the phase, the direction and the two block boundaries where they were;
the distance counts one more and the period tape takes a step the direction chooses. -/
theorem caught_control_of_plain (wm : PalPeg.GalilScaffoldChainWatch.State) (a : Fin 3)
    (htok : wm.machine.control.period.focus = PalPeg.GalilScaffoldChainPeriod.Token.plain a)
    (hseen : PalPeg.GalilScaffoldInputHead.read
      (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) = some a)
    (hforward : wm.machine.control.forward = true) :
    (PalPeg.GalilScaffoldChainWatch.caught wm).machine.control
      = {wm.machine.control with
          distance := PalPeg.GalilScaffoldCounter.inc wm.machine.control.distance,
          period := PalPeg.GalilScaffoldChainPeriod.moveRight wm.machine.control.period} := by
  show PalPeg.GalilScaffoldChainConsume.consume wm.machine.control
      (PalPeg.GalilScaffoldInputHead.read
        (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier)) = _
  rw [hseen, PalPeg.GalilScaffoldChainConsume.plain wm.machine.control a htok, if_pos hforward]

/-- **the lag and the margin a consuming tick leaves.** -/
theorem caught_lag_margin (wm : PalPeg.GalilScaffoldChainWatch.State) :
    (PalPeg.GalilScaffoldChainWatch.caught wm).lag
        = PalPeg.GalilScaffoldCounter.dec wm.lag
      ∧ (PalPeg.GalilScaffoldChainWatch.caught wm).margin = wm.margin := ⟨rfl, rfl⟩

/-- **the tapes after a consuming tick, of the machine itself.**  The chain spends one unit of
its lag, counts one more letter of its distance and walks its period tape one step; the step's
table writes those three slots and erases one cell of the idle program half, and nothing else it
writes is read by the encoding.

The cursor is not here: the chain's verifier moves too, but a step right is eleven slots of the
view layer, so this is the encoding of `stepState` — the tick's state with the cursor put back. -/
theorem physRule_scan_consume {fppBound dpBound K : ℕ} (margin entryQ : ℕ) (first : Fin 9)
    (hbound : 320 < fppBound) (hKq : entryQ + 3 ≤ K) (hK1 : 1 ≤ K) (hK : K ≤ margin)
    (hKn : K ≤ margin + 1)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.scan)
    (hconsume : chainConsumesTest q
      (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) = true)
    (hmatch : watchVerdictTest q
      (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) = some true)
    (hfwdBit : (scanConsumeNext q
      (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).chainForward = true)
    (wm : PalPeg.GalilScaffoldChainWatch.State)
    (hchain : x.vm.chain = PalPeg.GalilScaffoldChainInputSupply.ChainVM.watch wm) (a : Fin 3)
    (htok : wm.machine.control.period.focus = PalPeg.GalilScaffoldChainPeriod.Token.plain a)
    (hseen : PalPeg.GalilScaffoldInputHead.read
      (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) = some a)
    (hforward : wm.machine.control.forward = true)
    (henc : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T) :
    EncTapes margin
      (stepState ⟨x.ctl, {x.vm with
        chain := PalPeg.GalilScaffoldChainInputSupply.ChainVM.watch
          (PalPeg.GalilScaffoldChainWatch.caught wm)}⟩ wm.machine.verifier)
      (scanConsumeNext q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).polarity
      q.gap q.micro q.fppLive q.dpLive
      (fun slot => PalPeg.CloseoutCoreEnc12.actList blankM (T slot)
        (ruleActs entryQ first q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (slotIndex slot))) := by
  have hcontrol := caught_control_of_plain wm a htok hseen hforward
  have hlagx : counterOf x 11 = some wm.lag := by simp only [counterOf, hchain]
  have hdistx : counterOf x 13 = some wm.machine.control.distance := by
    simp only [counterOf, hchain]
  have hperiodx : periodOf x = some wm.machine.control.period := by
    simp only [periodOf, hchain]
  obtain ⟨segLag, habsLag, htapeLag⟩ :=
    scanConsume_lagTape margin entryQ first hbound hK1 hKn x q T hqmode hconsume hmatch
      wm.lag hlagx henc
  obtain ⟨segDist, habsDist, htapeDist⟩ :=
    scanConsume_distanceTape margin entryQ first hbound hK1 hKn x q T hqmode hconsume hmatch
      wm.machine.control.distance hdistx henc
  have htapePeriod :=
    scanConsume_periodTape margin entryQ first hbound hK x q T hqmode hconsume hmatch hfwdBit
      wm.machine.control.period hperiodx henc
  have hzc : (stepState ⟨x.ctl, {x.vm with
      chain := PalPeg.GalilScaffoldChainInputSupply.ChainVM.watch
        (PalPeg.GalilScaffoldChainWatch.caught wm)}⟩ wm.machine.verifier).vm.chain
      = PalPeg.GalilScaffoldChainInputSupply.ChainVM.watch
          ⟨⟨wm.machine.verifier, (PalPeg.GalilScaffoldChainWatch.caught wm).machine.control⟩,
            (PalPeg.GalilScaffoldChainWatch.caught wm).lag,
            (PalPeg.GalilScaffoldChainWatch.caught wm).margin⟩ := rfl
  refine encTapes_chainConsume margin x _ q.polarity _ q.gap q.micro q.fppLive q.dpLive T _ henc
    ?_ ?_ (fun i => rfl) (fun i => rfl) ?_ ?_ ?_
    (PalPeg.GalilScaffoldCounter.dec wm.lag) ?_ segLag ?_ ?_
    (PalPeg.GalilScaffoldCounter.inc wm.machine.control.distance) ?_ segDist ?_ ?_
    (PalPeg.GalilScaffoldChainPeriod.moveRight wm.machine.control.period) ?_ ?_ ?_ ?_
  · funext v
    fin_cases v <;> simp only [headOf, hzc, hchain] <;> rfl
  · funext i
    fin_cases i <;> simp only [placeOf, hzc, hchain] <;> rfl
  · simp only [answerOf, hzc, hchain]
  · intro c h11 h13
    fin_cases c <;> first
      | exact absurd rfl h11
      | exact absurd rfl h13
      | (simp only [counterOf, hzc, hchain, hcontrol]; rfl)
      | (simp only [counterOf, hzc, hchain, hcontrol])
  · intro c h11 h13
    simp only [scanConsumeNext, hmatch]
    rw [Function.update_of_ne h13, Function.update_of_ne h11]
  · simp only [counterOf, hzc]
    rfl
  · rw [show (scanConsumeNext q
      (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).polarity 11
        = decSignAt (q.polarity 11) (counterSlot 11)
          (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) from by
      simp only [scanConsumeNext, hmatch]
      rw [Function.update_of_ne (by decide), Function.update_self]]
    exact habsLag
  · exact htapeLag
  · simp only [counterOf, hzc, hcontrol]
  · rw [show (scanConsumeNext q
      (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).polarity 13
        = incSign q.polarity 13
          (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) from by
      simp only [scanConsumeNext, hmatch]
      rw [Function.update_self]]
    exact habsDist
  · exact htapeDist
  · simp only [periodOf, hzc, hcontrol]
  · exact htapePeriod
  · intro k
    obtain ⟨raw, hraw⟩ :=
      idle_shape_after_erase margin hK1 hKn (physRule entryQ first hbound hKq) q T q.fppLive _
        (by
          show ruleActs entryQ first q _ = _
          unfold ruleActs
          rw [hqmode])
        (fun k' => scanConsumeActs_off q _ (progSlotOf (!q.fppLive) k')
          (by cases q.fppLive <;> simp [progSlotOf, counterSlot])
          (by cases q.fppLive <;> simp [progSlotOf, counterSlot])
          (by cases q.fppLive <;> simp [progSlotOf, periodSlot]))
        henc.idleShape k
    refine ⟨raw, ?_⟩
    rw [← hraw, idealStep_physRule]
    dsimp only
    rw [tapesOf_apply]
  · intro slot h11 h13 hp hidle
    rw [show ruleActs entryQ first q
        (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) (slotIndex slot) = [] from by
      unfold ruleActs
      rw [hqmode]
      dsimp only
      rw [withErase_at_other q.fppLive _ _ slot hidle, scanConsumeActs_off q _ slot h11 h13 hp]]
    rfl

/-- **the rewind never asks a cursor to step right**, so its row carries no arrival condition:
every cursor either steps left or stands still. -/
theorem rewindCommands_ne_moveRight {fppBound dpBound K : ℕ} (first : Fin 9) (live : Bool)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (v : Fin 4) :
    rewindCommands first live q ws v ≠ .moveRight := by
  intro hEq
  unfold rewindCommands at hEq
  split_ifs at hEq with h1 h2
  · exact absurd hEq (by simp [stayCommands])
  · dsimp only at hEq
    split_ifs at hEq <;> simp at hEq
  · dsimp only at hEq
    split_ifs at hEq <;> simp at hEq

/-- **one step of the rewind, on the machine of twelve steps.**  The first mode whose row moves a
cursor: its row names a step left for the left cursor and, on a paired rewind, for the centre,
and the abstract tick does exactly that to them.  Everything else is `enc_afterTick`. -/
theorem rewind_one_of_tick {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (rest : QPhys fppBound dpBound → Option (Fin 2) →
      (Fin tapeCountM → PalPeg.Local.Window Γm K) → Fin 4 →
      PalPeg.ConcreteLocalMachine.ViewCommand)
    (input : Option (Fin 2))
    (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K) (hK2 : 2 ≤ K) (hmargin : K ≤ margin)
    (hslot0 : q.slot.val = 0) (howed : ∀ v, (q.micro v).2.2.2 = 0)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind)
    (hnotFirst : ¬ (x.vm.fpp.program.config.tapes 8).focus = first)
    (henc : Enc w margin x (q, T))
    (hctl : EncControl w
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      (ruleNext entryQ first hbound q
        (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))))
    (htapes : EncTapes margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      (ruleNext entryQ first hbound q
        (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).polarity
      (ruleNext entryQ first hbound q
        (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).gap
      (ruleNext entryQ first hbound q
        (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).micro
      (ruleNext entryQ first hbound q
        (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).fppLive
      (ruleNext entryQ first hbound q
        (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))).dpLive
      (fun slot => PalPeg.CloseoutCoreEnc12.actList blankM (T slot)
        (ruleActs entryQ first q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
          (slotIndex slot)))) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hK hK2 rest) blankM
          (q, tapesOf T) input 12).1,
        fun i => (PalPeg.LocalStepFusion.idealRun
          (tickPhysRule entryQ first hbound hK hK2 rest) blankM (q, tapesOf T) input 12).2
            (slotIndex i)) := by
  have hwin : ¬ centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot q.fppLive 8) = encProg first := by
    intro hEq
    exact hnotFirst ((focus_iff_of_enc (K := K) henc 8 first).mp
      (by rw [← hEq]; exact (centreRead_of_margin T (progSlot q.fppLive 8)
        (le_trans hmargin (henc.2.margins _))).symm))
  have hctlPair : x.ctl.pair = q.ctl.pair :=
    congrArg (fun c => c.pair) henc.1.ctl.symm
  have hatFirst : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).atFirst
      x.vm = false := by
    rw [frameFun_atFirst]
    exact decide_eq_false hnotFirst
  have hxmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind :=
    (congrArg (fun c => c.mode) henc.1.ctl.symm).trans hqmode
  exact enc_afterTickOfState margin entryQ first hbound hK hK2 hmargin rest w x _ q T input hslot0 howed
    (rewindCommands first q.fppLive q
      (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)))
    (fun v => modeCommands_rewind first rest q input _ hqmode ▸ rfl)
    (rewindHeadOps x.ctl.pair)
    (fun v => hctlPair ▸ headOp_rewindCommands first q _ hwin v)
    (fun v => by
      cases hx : headOf x v with
      | none =>
        have h3 : v = 3 := by
          fin_cases v
          · exact absurd hx (by simp [headOf])
          · exact absurd hx (by simp [headOf])
          · exact absurd hx (by simp [headOf])
          · rfl
        subst h3
        have hnone : headOf (PalPeg.GalilScaffoldTop.tickFun
            (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x) 3
            = none := by
          rw [headOf_tickFun_rewind_chain centre place entry entryQ first w F delay x hxmode
            hatFirst]
          exact hx
        rw [hnone]
      | some head =>
        rw [headOf_tickFun_rewind centre place entry entryQ first w F delay x hxmode hatFirst
          v head hx]
        rfl)
    (fun v head hhead =>
      headOf_tickFun_rewind centre place entry entryQ first w F delay x hxmode hatFirst v head
        hhead)
    (fun v _ _ hmove =>
      absurd hmove (rewindCommands_ne_moveRight first q.fppLive q _ v))
    henc.2 hctl
    (fun i => rfl) (fun i => rfl) rfl rfl rfl rfl htapes


/-- **the rewind that has reached the first instruction, on the machine of twelve steps.**  Its
row is standing still — the rewind is over — and the tick wipes the preparation program, which
moves no cursor. -/
theorem rewind_reset_of_tick {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (rest : QPhys fppBound dpBound → Option (Fin 2) →
      (Fin tapeCountM → PalPeg.Local.Window Γm K) → Fin 4 →
      PalPeg.ConcreteLocalMachine.ViewCommand)
    (input : Option (Fin 2))
    (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K) (hK2 : 2 ≤ K) (hK1 : 1 ≤ K)
    (hmargin : K ≤ margin) (hKn : K ≤ margin + 1)
    (hslot0 : q.slot.val = 0) (howed : ∀ v, (q.micro v).2.2.2 = 0)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind)
    (hatFirst : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).atFirst
      x.vm = true)
    (hatMark : (T (progSlot q.fppLive 8)).focus = encProg first)
    (henc : Enc w margin x (q, T))
    (hidle : ∀ i : Fin 9, T (progSlotOf (!q.fppLive) i)
      = padLeft margin (mapTape encProg (encTape PalPeg.GalilScaffoldTape.reset))) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hK hK2 rest) blankM
          (q, tapesOf T) input 12).1,
        fun i => (PalPeg.LocalStepFusion.idealRun
          (tickPhysRule entryQ first hbound hK hK2 rest) blankM (q, tapesOf T) input 12).2
            (slotIndex i)) := by
  have hwin : centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot q.fppLive 8) = encProg first := by
    rw [centreRead_of_margin T (progSlot q.fppLive 8) (le_trans hmargin (henc.2.margins _))]
    exact hatMark
  have hrow : ∀ v, modeCommands first rest q input
      (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) v = .stay := fun v => by
    rw [modeCommands_rewind first rest q input _ hqmode,
      rewindCommands_atFirst first q.fppLive q _ hwin]
    rfl
  obtain ⟨hctl, htapes⟩ := enc_step_pieces margin entryQ first hbound hK w
    (PalPeg.GalilScaffoldTop.tickFun
      (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x) q T
    (physRule_rewind_fppReset margin centre place entry entryQ first w F delay x q T hbound hK
      (fun i => hmargin.trans (henc.2.margins i)) hK1 hKn hqmode hmode hatFirst hatMark henc hidle)
  exact enc_afterTickOfState margin entryQ first hbound hK hK2 hmargin rest w x _ q T input hslot0 howed
    (fun _ => .stay) hrow (fun _ => id) (fun _ => rfl)
    (fun v => by
      rw [headOf_tickFun_rewindReset centre place entry entryQ first w F delay x hmode hatFirst v])
    (fun v head hhead => by
      rw [headOf_tickFun_rewindReset centre place entry entryQ first w F delay x hmode hatFirst v]
      exact hhead)
    (fun _ _ _ h => absurd h (by simp)) henc.2 hctl
    (fun i => rfl) (fun i => rfl) rfl rfl rfl rfl htapes


/-- **the unpaired step of the rewind, on the machine of twelve steps.**  The branch theorem goes
in and the encoding of the tick comes out; what the row says about each cursor, and what the tick
does to it, are `rewind_one_of_tick`'s. -/
theorem rewind_one_of_tick_branch {fppBound dpBound K : ℕ} (margin : ℕ)
    (centre : GalilVM → Fin 3) (place : GalilVM → PalPeg.GalilScaffoldPlace.Place)
    (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (rest : QPhys fppBound dpBound → Option (Fin 2) →
      (Fin tapeCountM → PalPeg.Local.Window Γm K) → Fin 4 →
      PalPeg.ConcreteLocalMachine.ViewCommand)
    (input : Option (Fin 2))
    (hbound : 320 < fppBound) (hKb : entryQ + 3 ≤ K) (hK2 : 2 ≤ K) (hK1 : 1 ≤ K)
    (hK : K ≤ margin) (hmargin2 : 2 ≤ margin)
    (hslot0 : q.slot.val = 0) (howed : ∀ v, (q.micro v).2.2.2 = 0)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind)
    (hnotFirst : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).atFirst
      x.vm = false)
    (hqpair : q.ctl.pair = false) (hpair : x.ctl.pair = false)
    (hnotMark : centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot q.fppLive 8) ≠ encProg first)
    (hfloor : (x.vm.fpp.program.config.tapes 8).left ≠ [])
    (hnotFocus : ¬ (x.vm.fpp.program.config.tapes 8).focus = first)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hKb hK2 rest) blankM
          (q, tapesOf T) input 12).1,
        fun i => (PalPeg.LocalStepFusion.idealRun
          (tickPhysRule entryQ first hbound hKb hK2 rest) blankM (q, tapesOf T) input 12).2
            (slotIndex i)) := by
  obtain ⟨hctl, htapes⟩ := enc_step_pieces margin entryQ first hbound hKb w
    (PalPeg.GalilScaffoldTop.tickFun
      (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x) q T
    (physRule_rewind_one margin centre place entry entryQ first w F delay x q T hbound hKb hK1 hK
      hmargin2 hqmode hmode hnotFirst hqpair hpair hnotMark hfloor henc)
  exact rewind_one_of_tick margin centre place entry entryQ first w F delay x q T rest input
    hbound hKb hK2 hK hslot0 howed hqmode hnotFocus henc hctl htapes


/-- **the paired step of the rewind, on the machine of twelve steps.**  The same layer with the
paired branch theorem: the row walks the centre with the left cursor, and the tick does too. -/
theorem rewind_pair_of_tick_branch {fppBound dpBound K : ℕ} (margin : ℕ)
    (centre : GalilVM → Fin 3) (place : GalilVM → PalPeg.GalilScaffoldPlace.Place)
    (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (rest : QPhys fppBound dpBound → Option (Fin 2) →
      (Fin tapeCountM → PalPeg.Local.Window Γm K) → Fin 4 →
      PalPeg.ConcreteLocalMachine.ViewCommand)
    (input : Option (Fin 2))
    (hbound : 320 < fppBound) (hKb : entryQ + 3 ≤ K) (hK2 : 2 ≤ K) (hK1 : 1 ≤ K)
    (hK : K ≤ margin) (hmargin2 : 2 ≤ margin)
    (hslot0 : q.slot.val = 0) (howed : ∀ v, (q.micro v).2.2.2 = 0)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind)
    (hnotFirst : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).atFirst
      x.vm = false)
    (hqpair : q.ctl.pair = true) (hpair : x.ctl.pair = true)
    (hnotMark : centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot q.fppLive 8) ≠ encProg first)
    (hfloor : (x.vm.fpp.program.config.tapes 8).left ≠ [])
    (hnotFocus : ¬ (x.vm.fpp.program.config.tapes 8).focus = first)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hKb hK2 rest) blankM
          (q, tapesOf T) input 12).1,
        fun i => (PalPeg.LocalStepFusion.idealRun
          (tickPhysRule entryQ first hbound hKb hK2 rest) blankM (q, tapesOf T) input 12).2
            (slotIndex i)) := by
  obtain ⟨hctl, htapes⟩ := enc_step_pieces margin entryQ first hbound hKb w
    (PalPeg.GalilScaffoldTop.tickFun
      (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x) q T
    (physRule_rewind_pair margin centre place entry entryQ first w F delay x q T hbound hKb hK1 hK
      hmargin2 hqmode hmode hnotFirst hqpair hpair hnotMark hfloor henc)
  exact rewind_one_of_tick margin centre place entry entryQ first w F delay x q T rest input
    hbound hKb hK2 hK hslot0 howed hqmode hnotFocus henc hctl htapes


/-- **the tick that leaves the shift, on the machine of twelve steps.**  Its row is standing
still and its branch was proved long ago; what was missing was an arm in the mode table. -/
theorem shift_exit_of_tick {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (rest : QPhys fppBound dpBound → Option (Fin 2) →
      (Fin tapeCountM → PalPeg.Local.Window Γm K) → Fin 4 →
      PalPeg.ConcreteLocalMachine.ViewCommand)
    (input : Option (Fin 2))
    (hbound : 320 < fppBound) (hK : entryQ + 3 ≤ K) (hK2 : 2 ≤ K) (hK1 : 1 ≤ K)
    (hmargin : K ≤ margin) (hKn : K ≤ margin + 1)
    (hslot0 : q.slot.val = 0) (howed : ∀ v, (q.micro v).2.2.2 = 0)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.shift)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.shift)
    (hdoneQ : remainsTest q.polarity
      (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) = false)
    (hdone : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).remainingPos
      x.vm = false)
    (henc : Enc w margin x (q, T)) :
    Enc w margin
      (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x)
      ((PalPeg.LocalStepFusion.idealRun (tickPhysRule entryQ first hbound hK hK2 rest) blankM
          (q, tapesOf T) input 12).1,
        fun i => (PalPeg.LocalStepFusion.idealRun
          (tickPhysRule entryQ first hbound hK hK2 rest) blankM (q, tapesOf T) input 12).2
            (slotIndex i)) := by
  obtain ⟨hctl, htapes⟩ := enc_step_pieces margin entryQ first hbound hK w
    (PalPeg.GalilScaffoldTop.tickFun
      (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w) F delay x) q T
    (shift_exit_of_rule margin centre place entry entryQ first w F delay x q T
      (physRule entryQ first hbound hK)
      (physRule_nq_shift entryQ first hbound hK q _ hqmode hdoneQ)
      (physRule_acts_shift entryQ first hbound hK q _ hqmode) hK1 hKn hmode hdone henc)
  exact enc_afterTickOfState margin entryQ first hbound hK hK2 hmargin rest w x _ q T input hslot0 howed
    (fun _ => .stay)
    (fun _ => by rw [modeCommands_shiftExit first rest q input _ hqmode hdoneQ]; rfl)
    (fun _ => id) (fun _ => rfl)
    (fun v => by
      rw [headOf_tickFun_shiftExit centre place entry entryQ first w F delay x hmode hdone v])
    (fun v head hhead => by
      rw [headOf_tickFun_shiftExit centre place entry entryQ first w F delay x hmode hdone v]
      exact hhead)
    (fun _ _ _ h => absurd h (by simp)) henc.2 hctl
    (fun i => rfl) (fun i => rfl) rfl rfl rfl rfl htapes

end PalPeg.PhysicalEncoding

#print axioms PalPeg.PhysicalEncoding.padded_write
#print axioms PalPeg.PhysicalEncoding.prog_slots_after_write
#print axioms PalPeg.PhysicalEncoding.prog_slots_after_right
#print axioms PalPeg.PhysicalEncoding.prog_slots_after_left
#print axioms PalPeg.PhysicalEncoding.prog_slots_at_floor
#print axioms PalPeg.PhysicalEncoding.fppTape_tapes
#print axioms PalPeg.PhysicalEncoding.encTapes_fppTapes
#print axioms PalPeg.PhysicalEncoding.encTapes_fppStep
#print axioms PalPeg.PhysicalEncoding.encControl_fppStep
#print axioms PalPeg.PhysicalEncoding.encControl_ctl
#print axioms PalPeg.PhysicalEncoding.encTapes_congr
#print axioms PalPeg.PhysicalEncoding.frameFun_atEnd
#print axioms PalPeg.PhysicalEncoding.frameFun_markForward
#print axioms PalPeg.PhysicalEncoding.frameFun_markBack
#print axioms PalPeg.PhysicalEncoding.markEnd_forward
#print axioms PalPeg.PhysicalEncoding.markEnd_back
#print axioms PalPeg.PhysicalEncoding.markEnd_back_atFloor
#print axioms PalPeg.PhysicalEncoding.encControl_fppStart
#print axioms PalPeg.PhysicalEncoding.home_step
#print axioms PalPeg.PhysicalEncoding.home_step_atFloor
#print axioms PalPeg.PhysicalEncoding.home_fppStart
#print axioms PalPeg.PhysicalEncoding.frameFun_markSet
#print axioms PalPeg.PhysicalEncoding.choose_back
#print axioms PalPeg.PhysicalEncoding.choose_back_atFloor
#print axioms PalPeg.PhysicalEncoding.bufEnc_resetL
#print axioms PalPeg.PhysicalEncoding.bufEnc_live_clearTick
#print axioms PalPeg.PhysicalEncoding.bufEnc_stepRight
#print axioms PalPeg.PhysicalEncoding.abs_stepL
#print axioms PalPeg.PhysicalEncoding.vml_markEnd_forward
#print axioms PalPeg.PhysicalEncoding.vml_markEnd_back
#print axioms PalPeg.PhysicalEncoding.vml_home_step
#print axioms PalPeg.PhysicalEncoding.vml_choose_back
#print axioms PalPeg.PhysicalEncoding.vml_home_fppStart
#print axioms PalPeg.PhysicalEncoding.vml_rewind_fppReset
#print axioms PalPeg.PhysicalEncoding.vml_copy_end
#print axioms PalPeg.PhysicalEncoding.absR_congr
#print axioms PalPeg.PhysicalEncoding.rval_bankTick
#print axioms PalPeg.PhysicalEncoding.vml_copy_one
#print axioms PalPeg.PhysicalEncoding.progTickFun_tapes
#print axioms PalPeg.PhysicalEncoding.abs_fppRunBuf
#print axioms PalPeg.PhysicalEncoding.vml_fpp_slice
#print axioms PalPeg.PhysicalEncoding.vml_rewind_one
#print axioms PalPeg.PhysicalEncoding.vml_rewind_pair
#print axioms PalPeg.PhysicalEncoding.vml_choose_select
#print axioms PalPeg.PhysicalEncoding.vml_fpp_done
#print axioms PalPeg.PhysicalEncoding.vml_shift_exit
#print axioms PalPeg.PhysicalEncoding.vml_shift_one
#print axioms PalPeg.PhysicalEncoding.actsAt_length
#print axioms PalPeg.PhysicalEncoding.idealStep_oneAct
#print axioms PalPeg.PhysicalEncoding.card_slot
#print axioms PalPeg.PhysicalEncoding.idealStep_oneSlot
#print axioms PalPeg.PhysicalEncoding.markEnd_forward_of_rule
#print axioms PalPeg.PhysicalEncoding.markEnd_back_of_rule
#print axioms PalPeg.PhysicalEncoding.home_fppStart_of_rule
#print axioms PalPeg.PhysicalEncoding.home_step_of_rule
#print axioms PalPeg.PhysicalEncoding.choose_back_of_rule
#print axioms PalPeg.PhysicalEncoding.markEnd_back_of_rule_atFloor
#print axioms PalPeg.PhysicalEncoding.home_step_of_rule_atFloor
#print axioms PalPeg.PhysicalEncoding.choose_back_of_rule_atFloor
#print axioms PalPeg.PhysicalEncoding.physRule_acts_markEnd
#print axioms PalPeg.PhysicalEncoding.physRule_acts_home
#print axioms PalPeg.PhysicalEncoding.physRule_acts_choose
#print axioms PalPeg.PhysicalEncoding.physRule_markEnd_forward
#print axioms PalPeg.PhysicalEncoding.physRule_markEnd_back
#print axioms PalPeg.PhysicalEncoding.physRule_home_step
#print axioms PalPeg.PhysicalEncoding.physRule_home_fppStart
#print axioms PalPeg.PhysicalEncoding.physRule_choose_back
#print axioms PalPeg.PhysicalEncoding.physRule_markEnd_back_atFloor
#print axioms PalPeg.PhysicalEncoding.physRule_home_step_atFloor
#print axioms PalPeg.PhysicalEncoding.physRule_choose_back_atFloor
#print axioms PalPeg.PhysicalEncoding.focus_iff_of_enc
#print axioms PalPeg.PhysicalEncoding.floor_iff_of_enc
#print axioms PalPeg.PhysicalEncoding.physRule_markEnd
#print axioms PalPeg.PhysicalEncoding.physRule_home
#print axioms PalPeg.PhysicalEncoding.physRule_choose
#print axioms PalPeg.PhysicalEncoding.progRunActs_length
#print axioms PalPeg.PhysicalEncoding.decProg_encProg
#print axioms PalPeg.PhysicalEncoding.decProg_centreRead
#print axioms PalPeg.PhysicalEncoding.winMachine_focus
#print axioms PalPeg.PhysicalEncoding.progActOf_winMachine
#print axioms PalPeg.PhysicalEncoding.winTape_pos
#print axioms PalPeg.PhysicalEncoding.rd_winTape
#print axioms PalPeg.PhysicalEncoding.rd_padded
#print axioms PalPeg.PhysicalEncoding.rd_winTape_of_padded
#print axioms PalPeg.PhysicalEncoding.tickFun_control_congr
#print axioms PalPeg.PhysicalEncoding.fppActs_length
#print axioms PalPeg.PhysicalEncoding.fppActs_at_live
#print axioms PalPeg.PhysicalEncoding.machineAgree_focus
#print axioms PalPeg.PhysicalEncoding.tapes_after_call
#print axioms PalPeg.PhysicalEncoding.pos_actList_ge
#print axioms PalPeg.PhysicalEncoding.progActRaw_congr
#print axioms PalPeg.PhysicalEncoding.machineAgree_tick
#print axioms PalPeg.PhysicalEncoding.progRunActs_of_agree
#print axioms PalPeg.PhysicalEncoding.machineAgree_winMachine
#print axioms PalPeg.PhysicalEncoding.fppActs_eq
#print axioms PalPeg.PhysicalEncoding.fpp_slot_after
#print axioms PalPeg.PhysicalEncoding.fpp_slice_of_rule
#print axioms PalPeg.PhysicalEncoding.fpp_done_of_rule
#print axioms PalPeg.PhysicalEncoding.physRule_fpp_running
#print axioms PalPeg.PhysicalEncoding.physRule_fpp
#print axioms PalPeg.PhysicalEncoding.physRule_fpp_done
#print axioms PalPeg.PhysicalEncoding.padded_push
#print axioms PalPeg.PhysicalEncoding.padded_pop
#print axioms PalPeg.PhysicalEncoding.padded_resetSeg
#print axioms PalPeg.PhysicalEncoding.idealStep_tapes
#print axioms PalPeg.PhysicalEncoding.idealStep_pair
#print axioms PalPeg.PhysicalEncoding.padded_progStep
#print axioms PalPeg.PhysicalEncoding.padded_progRun
#print axioms PalPeg.PhysicalEncoding.progActOf_congr
#print axioms PalPeg.PhysicalEncoding.rewind_fppReset
#print axioms PalPeg.PhysicalEncoding.physRule_rewind_fppReset
#print axioms PalPeg.PhysicalEncoding.idle_blank_of_oneSlot
#print axioms PalPeg.PhysicalEncoding.eraseOf_live
#print axioms PalPeg.PhysicalEncoding.eraseOf_other
#print axioms PalPeg.PhysicalEncoding.withErase_length
#print axioms PalPeg.PhysicalEncoding.withErase_at_live
#print axioms PalPeg.PhysicalEncoding.idealStep_withErase
#print axioms PalPeg.PhysicalEncoding.idealStep_atLiveSlot
#print axioms PalPeg.PhysicalEncoding.erase_preserves_shape
#print axioms PalPeg.PhysicalEncoding.idle_shape_after_erase
#print axioms PalPeg.PhysicalEncoding.encTapes_idleOnly
#print axioms PalPeg.PhysicalEncoding.progSlotOf_ne
#print axioms PalPeg.PhysicalEncoding.encTapes_progRight
#print axioms PalPeg.PhysicalEncoding.encTapes_progLeft
#print axioms PalPeg.PhysicalEncoding.encTapes_progLeftAtFloor
#print axioms PalPeg.PhysicalEncoding.window_below
#print axioms PalPeg.PhysicalEncoding.window_centre
#print axioms PalPeg.PhysicalEncoding.encProg_eq_iff
#print axioms PalPeg.PhysicalEncoding.padded_moveLeft
#print axioms PalPeg.PhysicalEncoding.margin_le_pos
#print axioms PalPeg.PhysicalEncoding.padded_moveRight
#print axioms PalPeg.PhysicalEncoding.EncTapes
