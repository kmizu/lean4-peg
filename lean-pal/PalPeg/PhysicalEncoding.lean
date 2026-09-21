import PalPeg.CloseoutCoreStep
import PalPeg.FrameFunction
import PalPeg.LocalCounter
import PalPeg.GalilScaffoldChainPeriod
import PalPeg.LocalStepRealize
import PalPeg.LocalViewLayout
import PalPeg.LocalArrival
import PalPeg.LocalQueueMachine
import PalPeg.LocalBuffers
import PalPeg.LocalReplayParked
import PalPeg.LocalTick3
import PalPeg.LocalStepFusion
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Prod

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
  (Fin 4 × Fin 12) ⊕ Fin 9 ⊕ Fin 12 ⊕ Unit ⊕ Unit ⊕ Fin 3 ⊕ Fin 16 ⊕ Fin 5 ⊕ Fin 9 ⊕ Fin 12

/-- the number of tapes the machine keeps: the four views, **both halves** of each of the two
program machines, the two mirrors, the three places, the counter bank and the answer. -/
abbrev tapeCountM : ℕ := 116

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

/-- a program tape's cells are told apart by their encodings, so a rule testing the
window against `encProg r` is testing the cell against `r`. -/
theorem encProg_eq_iff (s r : Fin 9) : encProg s = encProg r ↔ s = r := by
  unfold encProg blankM
  split <;> split <;> simp_all <;> omega

/-- **writing a cell without moving is one action too.**  Every branch that stamps a
symbol on a program tape — the end marker the copy leaves, the letters the preparation lays down
— is this one. -/
theorem padded_write (n : ℕ) (t : PalPeg.GalilScaffoldTape.Tape) (symbol : Fin 9) :
    padLeft n (mapTape encProg (encTape (PalPeg.GalilScaffoldTape.write t symbol)))
      = (padLeft n (mapTape encProg (encTape t))).applyAction blankM (encProg symbol, .stay) := by
  obtain ⟨left, focus, right⟩ := t
  rfl

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

/-- **which counter each spare copy is kept in step with.**  Three of `radius`, for the
`lag` and `margin` a chain is born with and for the negated `debt` a restart starts from; one of
`lower`, for the `work` a preparation starts from; one of `span`, for the `work` the doubling
enters with.  Handing one over is a move of the finite control and costs no action
(`LocalMirror.take`), and the opposite polarity bit hands over the negated copy
(`LocalMirror.negate_via_pol`). -/
def mirrorSource : Fin 5 → Fin 16
  | 0 => 2
  | 1 => 2
  | 2 => 2
  | 3 => 5
  | _ => 6

/-! ### what the tapes hold -/

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
        ∀ i, tapes (.inl (v, i)) = mapTape encCell (viewTapes i)
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
  mirrors : ∀ (m : Fin 5) value, counterOf x (mirrorSource m) = some value →
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
    obtain ⟨view, viewTapes, habs, hrep, hslots⟩ := henc.heads v head hhead
    exact ⟨view, viewTapes, habs, hrep, fun j => by
      rw [hkept _ (by intro j; cases fppLive <;> cases dpLive <;> simp [progSlotOf, dpSlotOf]) (by intro k; cases fppLive <;> cases dpLive <;> simp [progSlotOf, dpSlotOf]), hslots j]⟩
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

def EncPc {bound : ℕ} (held : PcPhys bound) (pc : ℕ) : Prop :=
  match held with
  | some i => (i : ℕ) = pc
  | none => bound ≤ pc

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
  polarity : Fin 16 → Bool
  gap : Fin 4 → Bool
  micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl
  /-- which half of each double buffer the encoding speaks about.  The bit is physical only:
  the abstraction cannot see it, and a wipe of a program machine is its flip.  The encoding's
  own fields still address the `false` half; moving them onto this bit is the next step. -/
  fppLive : Bool
  dpLive : Bool

/-- **what the finite control says about the state.**  Each field is read off the state;
nothing here mentions a tape. -/
structure EncControl {fppBound dpBound : ℕ} (x : State GalilVM)
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

/-- **a step of a program's tapes leaves the finite control where it was.**  The
counter and the halting flag of the program sit beside its tapes, and putting a tape back changes
neither. -/
theorem encControl_fppStep {fppBound dpBound : ℕ} (x : State GalilVM)
    (q : QPhys fppBound dpBound) (henc : EncControl x q)
    (f : PalPeg.GalilScaffoldTape.Tape → PalPeg.GalilScaffoldTape.Tape) (i : Fin 9) :
    EncControl ⟨x.ctl, {x.vm with fpp := {x.vm.fpp with program := PalPeg.GalilScaffoldChainInputSupply.FppControl.tape x.vm.fpp i f}}⟩ q where
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

/-- **and a change of the control word is the same change on both sides**, whenever the
new word reads as the new controller.  Every branch discharges that by computation: the reading
takes each field across unchanged and only widens the clock. -/
theorem encControl_ctl {fppBound dpBound : ℕ} (x : State GalilVM)
    (q : QPhys fppBound dpBound) (henc : EncControl x q) (c : CtlPhys)
    (a : PalPeg.GalilScaffoldController.Control) (hc : ctlAbs c = a) :
    EncControl ⟨a, x.vm⟩ {q with ctl := c} where
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
def Enc {fppBound dpBound : ℕ} (margin : ℕ) (x : State GalilVM)
    (p : QPhys fppBound dpBound × (Slot → STape Γm)) : Prop :=
  EncControl x p.1 ∧ EncTapes margin x p.1.polarity p.1.gap p.1.micro p.1.fppLive p.1.dpLive p.2

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
    (henc : Enc margin x (q, tapes))
    (hmoved : newTapes (progSlotOf q.fppLive 8)
      = PalPeg.CloseoutCoreEnc12.actList blankM (tapes (progSlotOf q.fppLive 8))
          [some ((tapes (progSlotOf q.fppLive 8)).focus, .right)])
    (hkept : ∀ slot, slot ≠ (progSlotOf q.fppLive 8) →
      (∀ k : Fin 9, slot ≠ progSlotOf (!q.fppLive) k) → newTapes slot = tapes slot)
    (hidleShape : ∀ k : Fin 9, ∃ raw : STape (Fin 9),
      newTapes (progSlotOf (!q.fppLive) k) = padLeft margin (mapTape encProg raw)) :
    Enc margin
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
    (henc : Enc margin x (q, tapes))
    (hmoved : newTapes (progSlotOf q.fppLive 8)
      = PalPeg.CloseoutCoreEnc12.actList blankM (tapes (progSlotOf q.fppLive 8))
          [some ((tapes (progSlotOf q.fppLive 8)).focus, .left)])
    (hkept : ∀ slot, slot ≠ (progSlotOf q.fppLive 8) →
      (∀ k : Fin 9, slot ≠ progSlotOf (!q.fppLive) k) → newTapes slot = tapes slot)
    (hidleShape : ∀ k : Fin 9, ∃ raw : STape (Fin 9),
      newTapes (progSlotOf (!q.fppLive) k) = padLeft margin (mapTape encProg raw)) :
    Enc margin
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
    (henc : Enc margin x (q, tapes)) :
    Enc margin
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

/-- and the finite control makes exactly those three changes. -/
theorem encControl_fppStart {fppBound dpBound : ℕ} (x : State GalilVM)
    (q : QPhys fppBound dpBound) (henc : EncControl x q) (hbound : 320 < fppBound)
    (c : CtlPhys) (a : PalPeg.GalilScaffoldController.Control) (hc : ctlAbs c = a) :
    EncControl ⟨a, {x.vm with fpp := {x.vm.fpp with program := PalPeg.GalilScaffoldControl.start 320 x.vm.fpp.program, mode := .run}}⟩
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

/-- **the walk home, both sides at once**, while the seventh tape still has a cell below
its head. -/
theorem home_step {fppBound dpBound : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (tapes newTapes : Slot → STape Γm)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.home)
    (hnotLeft : (x.vm.fpp.program.config.tapes 7).focus ≠ 4)
    (hfloor : (x.vm.fpp.program.config.tapes 7).left ≠ [])
    (henc : Enc margin x (q, tapes))
    (hmoved : newTapes (progSlotOf q.fppLive 7)
      = PalPeg.CloseoutCoreEnc12.actList blankM (tapes (progSlotOf q.fppLive 7))
          [some ((tapes (progSlotOf q.fppLive 7)).focus, .left)])
    (hkept : ∀ slot, slot ≠ (progSlotOf q.fppLive 7) →
      (∀ k : Fin 9, slot ≠ progSlotOf (!q.fppLive) k) → newTapes slot = tapes slot)
    (hidleShape : ∀ k : Fin 9, ∃ raw : STape (Fin 9),
      newTapes (progSlotOf (!q.fppLive) k) = padLeft margin (mapTape encProg raw)) :
    Enc margin
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
    (henc : Enc margin x (q, tapes)) :
    Enc margin
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
    (henc : Enc margin x (q, tapes)) :
    Enc margin
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
    (henc : Enc margin x (q, tapes))
    (hmoved : newTapes (progSlotOf q.fppLive 8)
      = PalPeg.CloseoutCoreEnc12.actList blankM (tapes (progSlotOf q.fppLive 8))
          [some ((tapes (progSlotOf q.fppLive 8)).focus, .left)])
    (hkept : ∀ slot, slot ≠ (progSlotOf q.fppLive 8) →
      (∀ k : Fin 9, slot ≠ progSlotOf (!q.fppLive) k) → newTapes slot = tapes slot)
    (hidleShape : ∀ k : Fin 9, ∃ raw : STape (Fin 9),
      newTapes (progSlotOf (!q.fppLive) k) = padLeft margin (mapTape encProg raw)) :
    Enc margin
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
    (henc : Enc margin x (q, tapes)) :
    Enc margin
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

/-- **the ideal step of a branch that also erases.**  At its own slot the branch's action list is
applied; at every slot the encoding speaks about other than that one, nothing happens.  The idle
half is deliberately left out: that is where the erasure writes. -/
theorem idealStep_withErase {Q : Type} {K : ℕ}
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
  · rw [idealStep_tapes, hacts, withErase_at_live, tapesOf_apply]
  · intro slot hs hidle
    rw [idealStep_tapes, hacts, withErase_at_other live _ _ slot hidle, tapesOf_apply,
      hbase slot hs]
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
    idealStep_withErase R q T live _ hacts (actsAt_off_live live i l)
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
    (hbase : ∀ slot : Slot, (∀ j : Fin 9, slot ≠ progSlotOf live j) →
      base (slotIndex slot) = [])
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
    rw [hbase (progSlotOf (!live) k) (fun j => (progSlotOf_ne_flip live j k).symm)]
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
    obtain ⟨view, viewTapes, habs, hrep, hslots⟩ := henc.heads v head hhead
    exact ⟨view, viewTapes, habs, hrep, fun j => by
      rw [hkept _ (by intro k; cases fppLive <;> simp [progSlotOf]), hslots j]⟩
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

/-- the slot of the preparation program's `i`-th tape. -/
abbrev progSlot (live : Bool) (i : Fin 9) : Slot := progSlotOf live i

/-- the symbol under the head of a slot, as the rule reads it from the window. -/
noncomputable def centreRead {K : ℕ} (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (i : Slot) : Γm :=
  ws (slotIndex i) ⟨K, by omega⟩

theorem centreRead_of_margin {K : ℕ} (T : Slot → STape Γm) (i : Slot)
    (hm : K ≤ PalPeg.Local.pos (T i)) :
    centreRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) i = (T i).focus := by
  show PalPeg.Local.readWin blankM K (tapesOf T (slotIndex i)) ⟨K, by omega⟩ = _
  rw [tapesOf_apply]
  exact window_centre K (T i) hm

/-- the symbol one cell below the head of a slot, as the rule reads it from the window. -/
noncomputable def belowRead {K : ℕ} (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (i : Slot) : Γm :=
  ws (slotIndex i) ⟨K - 1, by omega⟩

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
    (henc : Enc margin x (q, T)) :
    Enc margin
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
      (actsAt_off_live q.fppLive 8 _) henc.2.idleShape)

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
    (henc : Enc margin x (q, T)) :
    Enc margin
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
      (actsAt_off_live q.fppLive 8 _) henc.2.idleShape)

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
    (henc : Enc margin x (q, T)) :
    Enc margin
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
      (actsAt_off_live q.fppLive 7 _) henc.2.idleShape)⟩

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
    (henc : Enc margin x (q, T)) :
    Enc margin
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
      (actsAt_off_live q.fppLive 7 _) henc.2.idleShape)

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
    (henc : Enc margin x (q, T)) :
    Enc margin
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
      (actsAt_off_live q.fppLive 8 _) henc.2.idleShape)

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
    (henc : Enc margin x (q, T)) :
    Enc margin
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
      (actsAt_off_live q.fppLive 8 _)
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
    (henc : Enc margin x (q, T)) :
    Enc margin
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
      (actsAt_off_live q.fppLive 7 _)
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
    (henc : Enc margin x (q, T)) :
    Enc margin
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
      (actsAt_off_live q.fppLive 8 _)
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

theorem encControl_fppReset {fppBound dpBound : ℕ} (x : State GalilVM)
    (q : QPhys fppBound dpBound) (henc : EncControl x q) (hbound : 320 < fppBound)
    (c : CtlPhys) (a : PalPeg.GalilScaffoldController.Control) (hc : ctlAbs c = a) :
    EncControl ⟨a, {x.vm with fpp := {x.vm.fpp with program := PalPeg.GalilScaffoldControl.reset 320 x.vm.fpp.program}}⟩
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
    (henc : Enc margin x (q, tapes))
    (hidle : ∀ i : Fin 9, tapes (progSlotOf (!q.fppLive) i)
      = padLeft margin (mapTape encProg (encTape PalPeg.GalilScaffoldTape.reset))) :
    Enc margin
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
theorem focus_iff_of_enc {fppBound dpBound K : ℕ} {margin : ℕ} {x : State GalilVM}
    {q : QPhys fppBound dpBound} {T : Slot → STape Γm} (henc : Enc margin x (q, T))
    (i : Fin 9) (sym : Fin 9) :
    (T (progSlot q.fppLive i)).focus = encProg sym
      ↔ (x.vm.fpp.program.config.tapes i).focus = sym := by
  have hfpp : T (progSlot q.fppLive i)
      = padLeft margin (mapTape encProg (encTape (x.vm.fpp.program.config.tapes i))) :=
    henc.2.fpp i
  rw [hfpp, focus_padded]
  exact encProg_eq_iff _ _

/-- **the sentinel below the head means the component is on its first cell.** -/
theorem floor_iff_of_enc {fppBound dpBound K : ℕ} {margin : ℕ} {x : State GalilVM}
    {q : QPhys fppBound dpBound} {T : Slot → STape Γm} (henc : Enc margin x (q, T))
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
theorem decProg_centreRead {fppBound dpBound K : ℕ} {margin : ℕ} {x : State GalilVM}
    {q : QPhys fppBound dpBound} {T : Slot → STape Γm} (henc : Enc margin x (q, T))
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
theorem winMachine_focus {fppBound dpBound K : ℕ} {margin : ℕ} {x : State GalilVM}
    {q : QPhys fppBound dpBound} {T : Slot → STape Γm} (henc : Enc margin x (q, T))
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
theorem progActOf_winMachine {fppBound dpBound K : ℕ} {margin : ℕ} {x : State GalilVM}
    {q : QPhys fppBound dpBound} {T : Slot → STape Γm} (code : List (Instruction 9))
    (henc : Enc margin x (q, T)) (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i))
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
  else q

/-- the actions of the wipe: none.  The nine tapes the abstraction blanks are the nine the
machine stops looking at. -/
def rewindActs : Fin tapeCountM → List (PalPeg.CloseoutCoreEnc12.Act Γm) := fun _ => []

theorem rewindActs_length {K : ℕ} (j : Fin tapeCountM) : (rewindActs j).length ≤ K :=
  Nat.zero_le K

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
  | _ => q

/-- the actions of the machine, mode by mode. -/
noncomputable def ruleActs {fppBound dpBound K : ℕ} (entryQ : ℕ) (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) :
    Fin tapeCountM → List (PalPeg.CloseoutCoreEnc12.Act Γm) :=
  match q.ctl.mode with
  | PalPeg.GalilScaffoldController.Mode.markEnd => withErase q.fppLive ws (markEndActs q.fppLive ws)
  | PalPeg.GalilScaffoldController.Mode.home => withErase q.fppLive ws (homeActs q.fppLive ws)
  | PalPeg.GalilScaffoldController.Mode.choose => withErase q.fppLive ws (chooseBackActs q.fppLive ws)
  | PalPeg.GalilScaffoldController.Mode.rewind => withErase q.fppLive ws rewindActs
  | PalPeg.GalilScaffoldController.Mode.fpp =>
      withErase q.fppLive ws (fppActs PalPeg.GalilFppMarkedCode.code entryQ q.fppLive (pcOf q) q.fppDone ws)
  | _ => withErase q.fppLive ws (fun _ => [])

theorem ruleActs_length {fppBound dpBound K : ℕ} (entryQ : ℕ) (hK : entryQ + 2 ≤ K)
    (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (j : Fin tapeCountM) :
    (ruleActs entryQ q ws j).length ≤ K := by
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
      | exact withErase_length (b := entryQ) (by omega) q.fppLive ws _
          (fun j => fppActs_length PalPeg.GalilFppMarkedCode.code entryQ q.fppLive (pcOf q)
            q.fppDone ws j) j
      | exact withErase_length (b := 1) (by omega) q.fppLive ws _ (fun j => by simp [rewindActs]) j

/-- **the rule of the physical machine**, so far as its branches are proved. -/
noncomputable def physRule {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9) (hbound : 320 < fppBound) (hK : entryQ + 2 ≤ K) :
    PalPeg.CloseoutCoreEnc12.ActRule (Fin 2) (QPhys fppBound dpBound) Γm tapeCountM K where
  nq := fun q _ ws => ruleNext entryQ first hbound q ws
  acts := fun q _ ws => ruleActs entryQ q ws
  len_le := fun q _ ws j => ruleActs_length entryQ hK q ws j

theorem physRule_nq_markEnd {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9) (hbound : 320 < fppBound) (hK : entryQ + 2 ≤ K)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hm : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd) :
    (physRule (dpBound := dpBound) entryQ first hbound hK).nq q none ws = markEndNext q.fppLive q ws := by
  show ruleNext entryQ first hbound q ws = _
  unfold ruleNext
  rw [hm]

theorem physRule_acts_markEnd {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9) (hbound : 320 < fppBound) (hK : entryQ + 2 ≤ K)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hm : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd) :
    (physRule (dpBound := dpBound) entryQ first hbound hK).acts q none ws = withErase q.fppLive ws (markEndActs q.fppLive ws) := by
  show ruleActs entryQ q ws = _
  unfold ruleActs
  rw [hm]

theorem physRule_nq_home {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9) (hbound : 320 < fppBound) (hK : entryQ + 2 ≤ K)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hm : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.home) :
    (physRule (dpBound := dpBound) entryQ first hbound hK).nq q none ws = homeNext q.fppLive hbound q ws := by
  show ruleNext entryQ first hbound q ws = _
  unfold ruleNext
  rw [hm]

theorem physRule_acts_home {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9) (hbound : 320 < fppBound) (hK : entryQ + 2 ≤ K)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hm : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.home) :
    (physRule (dpBound := dpBound) entryQ first hbound hK).acts q none ws = withErase q.fppLive ws (homeActs q.fppLive ws) := by
  show ruleActs entryQ q ws = _
  unfold ruleActs
  rw [hm]

theorem physRule_nq_choose {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9) (hbound : 320 < fppBound) (hK : entryQ + 2 ≤ K)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hm : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.choose) :
    (physRule (dpBound := dpBound) entryQ first hbound hK).nq q none ws = chooseBackNext q := by
  show ruleNext entryQ first hbound q ws = _
  unfold ruleNext
  rw [hm]

theorem physRule_acts_choose {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9) (hbound : 320 < fppBound) (hK : entryQ + 2 ≤ K)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hm : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.choose) :
    (physRule (dpBound := dpBound) entryQ first hbound hK).acts q none ws = withErase q.fppLive ws (chooseBackActs q.fppLive ws) := by
  show ruleActs entryQ q ws = _
  unfold ruleActs
  rw [hm]

theorem physRule_nq_fpp {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9) (hbound : 320 < fppBound) (hK : entryQ + 2 ≤ K)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hm : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.fpp) :
    (physRule (dpBound := dpBound) entryQ first hbound hK).nq q none ws = fppNext entryQ q ws := by
  show ruleNext entryQ first hbound q ws = _
  unfold ruleNext
  rw [hm]

theorem physRule_acts_fpp {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9) (hbound : 320 < fppBound) (hK : entryQ + 2 ≤ K)
    (q : QPhys fppBound dpBound) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hm : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.fpp) :
    (physRule (dpBound := dpBound) entryQ first hbound hK).acts q none ws
      = withErase q.fppLive ws
          (fppActs PalPeg.GalilFppMarkedCode.code entryQ q.fppLive (pcOf q) q.fppDone ws) := by
  show ruleActs entryQ q ws = _
  unfold ruleActs
  rw [hm]

/-- **the mark walk of the machine itself.**  The same statement as `markEnd_forward_of_rule`,
with its two hypotheses about the rule discharged: this is the rule the machine runs, not one
assumed to exist. -/
theorem physRule_markEnd_forward {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (hbound : 320 < fppBound) (hK : entryQ + 2 ≤ K)
    (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i))
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd)
    (hnotEnd : (x.vm.fpp.program.config.tapes 8).focus ≠ 5)
    (hnotMark : (T (progSlot q.fppLive 8)).focus ≠ encProg 5)
    (henc : Enc margin x (q, T)) :
    Enc margin
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
    (hK : entryQ + 2 ≤ K) (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hm : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind) :
    (physRule (dpBound := dpBound) entryQ first hbound hK).nq q none ws = rewindNext first hbound q ws := by
  show ruleNext entryQ first hbound q ws = _
  unfold ruleNext
  rw [hm]

theorem physRule_acts_rewind {fppBound dpBound K : ℕ} (entryQ : ℕ) (first : Fin 9) (hbound : 320 < fppBound)
    (hK : entryQ + 2 ≤ K) (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (hm : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind) :
    (physRule (dpBound := dpBound) entryQ first hbound hK).acts q none ws = withErase q.fppLive ws rewindActs := by
  show ruleActs entryQ q ws = _
  unfold ruleActs
  rw [hm]

/-- **the wipe of the machine itself.**  The rule is the one the machine runs, and it names no
action at all; the nine tapes the abstraction blanks are the nine the machine stops looking at,
and the half that becomes live is the one the background erasure kept blank. -/
theorem physRule_rewind_fppReset {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (hbound : 320 < fppBound) (hK : entryQ + 2 ≤ K)
    (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i))
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.rewind)
    (hatFirst : (PalPeg.FrameFunction.galilFrameFun centre place entry entryQ first w).atFirst
      x.vm = true)
    (hatMark : (T (progSlot q.fppLive 8)).focus = encProg first)
    (henc : Enc margin x (q, T))
    (hidle : ∀ i : Fin 9, T (progSlotOf (!q.fppLive) i)
      = padLeft margin (mapTape encProg (encTape PalPeg.GalilScaffoldTape.reset))) :
    Enc margin
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
      show PalPeg.CloseoutCoreEnc12.actList blankM _
        (rewindActs (slotIndex (progSlotOf (!q.fppLive) k))
          ++ eraseOf q.fppLive _ (slotIndex (progSlotOf (!q.fppLive) k))) = _
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
    · rw [withErase_at_other q.fppLive _ _ i (fun k hk => hid ⟨k, hk⟩)]
      rfl
  rw [hq, hsame]
  exact rewind_fppReset margin centre place entry entryQ first w F delay x q T hbound hmode
    hatFirst henc hidle

/-- **the mark walk back, of the machine itself.**  The step that finds the end mark, with
nothing assumed about the rule. -/
theorem physRule_markEnd_back {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (hbound : 320 < fppBound) (hK : entryQ + 2 ≤ K)
    (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i))
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd)
    (hatEnd : (x.vm.fpp.program.config.tapes 8).focus = 5)
    (hfloor : (x.vm.fpp.program.config.tapes 8).left ≠ [])
    (hatMark : (T (progSlot q.fppLive 8)).focus = encProg 5)
    (hnotFloor : belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot q.fppLive 8) ≠ bottomM)
    (henc : Enc margin x (q, T)) :
    Enc margin
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
    (hbound : 320 < fppBound) (hK : entryQ + 2 ≤ K)
    (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i))
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.home)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.home)
    (hnotLeft : (x.vm.fpp.program.config.tapes 7).focus ≠ 4)
    (hfloor : (x.vm.fpp.program.config.tapes 7).left ≠ [])
    (hnotMark : (T (progSlot q.fppLive 7)).focus ≠ encProg 4)
    (hnotFloor : belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot q.fppLive 7) ≠ bottomM)
    (henc : Enc margin x (q, T)) :
    Enc margin
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
    (hbound : 320 < fppBound) (hK : entryQ + 2 ≤ K)
    (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i))
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.home)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.home)
    (hatLeft : (x.vm.fpp.program.config.tapes 7).focus = 4)
    (hatMark : (T (progSlot q.fppLive 7)).focus = encProg 4)
    (henc : Enc margin x (q, T)) :
    Enc margin
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

/-- **the parity walk, of the machine itself.** -/
theorem physRule_choose_back {fppBound dpBound K : ℕ} (margin : ℕ) (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry entryQ : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (q : QPhys fppBound dpBound) (T : Slot → STape Γm)
    (hbound : 320 < fppBound) (hK : entryQ + 2 ≤ K)
    (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i))
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.choose)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.choose)
    (hkeep : (x.ctl.odd && (decide ((x.vm.fpp.program.config.tapes 8).focus = 8)
        || decide ((x.vm.fpp.program.config.tapes 8).focus = first))) = false)
    (hfloor : (x.vm.fpp.program.config.tapes 8).left ≠ [])
    (hnotFloor : belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot q.fppLive 8) ≠ bottomM)
    (henc : Enc margin x (q, T)) :
    Enc margin
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
    (hbound : 320 < fppBound) (hK : entryQ + 2 ≤ K)
    (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i))
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd)
    (hatEnd : (x.vm.fpp.program.config.tapes 8).focus = 5)
    (hfloor : (x.vm.fpp.program.config.tapes 8).left = [])
    (hatMark : (T (progSlot q.fppLive 8)).focus = encProg 5)
    (hisFloor : belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot q.fppLive 8) = bottomM)
    (henc : Enc margin x (q, T)) :
    Enc margin
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
    (hbound : 320 < fppBound) (hK : entryQ + 2 ≤ K)
    (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i))
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.home)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.home)
    (hnotLeft : (x.vm.fpp.program.config.tapes 7).focus ≠ 4)
    (hfloor : (x.vm.fpp.program.config.tapes 7).left = [])
    (hnotMark : (T (progSlot q.fppLive 7)).focus ≠ encProg 4)
    (hisFloor : belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot q.fppLive 7) = bottomM)
    (henc : Enc margin x (q, T)) :
    Enc margin
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
    (hbound : 320 < fppBound) (hK : entryQ + 2 ≤ K)
    (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i))
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.choose)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.choose)
    (hkeep : (x.ctl.odd && (decide ((x.vm.fpp.program.config.tapes 8).focus = 8)
        || decide ((x.vm.fpp.program.config.tapes 8).focus = first))) = false)
    (hfloor : (x.vm.fpp.program.config.tapes 8).left = [])
    (hisFloor : belowRead (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape))
      (progSlot q.fppLive 8) = bottomM)
    (henc : Enc margin x (q, T)) :
    Enc margin
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
    (hbound : 320 < fppBound) (hK : entryQ + 2 ≤ K)
    (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i))
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.markEnd)
    (henc : Enc margin x (q, T)) :
    Enc margin
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
    (hbound : 320 < fppBound) (hK : entryQ + 2 ≤ K)
    (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i))
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.home)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.home)
    (henc : Enc margin x (q, T)) :
    Enc margin
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
    (hbound : 320 < fppBound) (hK : entryQ + 2 ≤ K)
    (hmargin : ∀ i : Slot, K ≤ PalPeg.Local.pos (T i))
    (hK1 : 1 ≤ K) (hKn : K ≤ margin + 1)
    (hqmode : q.ctl.mode = PalPeg.GalilScaffoldController.Mode.choose)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.choose)
    (hkeep : (x.ctl.odd && (decide ((x.vm.fpp.program.config.tapes 8).focus = 8)
        || decide ((x.vm.fpp.program.config.tapes 8).focus = first))) = false)
    (henc : Enc margin x (q, T)) :
    Enc margin
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
theorem runFun_control_of_agree (code : List (Instruction 9)) :
    ∀ (n : ℕ) (m m' : PalPeg.GalilScaffoldControl.Machine 9), MachineAgree n m m' →
      (PalPeg.ProgramFunction.runFun code (List.replicate n true) m).config.pc
          = (PalPeg.ProgramFunction.runFun code (List.replicate n true) m').config.pc
        ∧ (PalPeg.ProgramFunction.runFun code (List.replicate n true) m).done
          = (PalPeg.ProgramFunction.runFun code (List.replicate n true) m').done
  | 0, _, _, h => ⟨h.pc, h.done⟩
  | n + 1, m, m', h => by
      rw [List.replicate_succ]
      exact runFun_control_of_agree code n _ _ (machineAgree_tick code h)

/-- **the machine the rule runs in its head agrees with the abstraction's, as far as a quantum of
`K` calls can look.**  Its heads sit at the centre of their windows by construction, and each of
its cells is the component's own by `rd_winTape_of_padded`. -/
theorem machineAgree_winMachine {fppBound dpBound K : ℕ} {margin : ℕ} {x : State GalilVM}
    {q : QPhys fppBound dpBound} {T : Slot → STape Γm} (henc : Enc margin x (q, T))
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
theorem fppActs_eq {fppBound dpBound K : ℕ} {margin : ℕ} {x : State GalilVM}
    {q : QPhys fppBound dpBound} {T : Slot → STape Γm} (code : List (Instruction 9))
    (quantum : ℕ) (hq : quantum ≤ K) (henc : Enc margin x (q, T))
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
theorem fpp_slot_after {fppBound dpBound K : ℕ} {margin : ℕ} {x : State GalilVM}
    {q : QPhys fppBound dpBound} {T : Slot → STape Γm} (code : List (Instruction 9))
    (quantum : ℕ) (hq : quantum ≤ K) (henc : Enc margin x (q, T))
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

-- the machine's alphabet must be finite and decidable, as the physical machine demands
#synth Fintype Γm
#synth DecidableEq Γm
#synth Fintype Slot
#synth DecidableEq Slot
#synth Fintype CtlPhys
#synth DecidableEq CtlPhys
#synth Fintype ChainTag
#synth DecidableEq ChainTag

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
