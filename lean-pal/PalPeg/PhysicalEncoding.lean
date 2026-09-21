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
  (Fin 4 × Fin 12) ⊕ Fin 9 ⊕ Fin 12 ⊕ Unit ⊕ Unit ⊕ Fin 3 ⊕ Fin 16 ⊕ Fin 5

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
    (tapes : Slot → STape Γm) : Prop where
  margins : ∀ slot, margin ≤ PalPeg.Local.pos (tapes slot)
  heads : ∀ (v : Fin 4) head, headOf x v = some head →
    ∃ (view : PalPeg.LocalInputView.InputView) (viewTapes : Fin 12 → STape Γc),
      PalPeg.LocalArrival.absHead' view [] = head ∧
        PalPeg.ConcreteLocalMachine.ViewRep margin view (gap v) (micro v) viewTapes ∧
        ∀ i, tapes (.inl (v, i)) = mapTape encCell (viewTapes i)
  fpp : ∀ i : Fin 9,
    tapes (.inr (.inl i)) = padLeft margin (mapTape encProg (encTape (x.vm.fpp.program.config.tapes i)))
  dp : ∀ i : Fin 12, tapes (.inr (.inr (.inl i))) = padLeft margin (mapTape encProg (encTape (x.vm.dp.config.tapes i)))
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
      tapes (.inr (.inr (.inr (.inr (.inr (.inr (.inr m))))))) = padLeft margin (mapTape encSeg segments)
  period : ∀ tape, periodOf x = some tape →
    tapes (.inr (.inr (.inr (.inr (.inl ()))))) = padLeft margin (mapTape encToken (encPeriod tape))
  answer : ∀ tape, answerOf x = some tape →
    tapes (.inr (.inr (.inr (.inl ())))) = padLeft margin (mapTape encProg (encTape tape))

/-- **every head of the machine stands clear of the left edge**, which is what the
sweep of `compStep` asks of a rule with window radius `K ≤ margin`. -/
theorem margin_le_pos {margin : ℕ} {x : State GalilVM} {polarity : Fin 16 → Bool}
    {gap : Fin 4 → Bool} {micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl}
    {tapes : Slot → STape Γm} (henc : EncTapes margin x polarity gap micro tapes)
    {K : ℕ} (hK : K ≤ margin) (slot : Slot) : K ≤ PalPeg.Local.pos (tapes slot) :=
  hK.trans (henc.margins slot)

/-- **the encoding of the tapes reads seven things and nothing else**: the two program
bundles' tapes, the sixteen counters, the four heads, the three cursors, and the chain's period
and answer tapes.  Two states that agree on those are encoded by the same tapes.  In particular
the control word does not appear, and neither does a program's counter or its halting flag. -/
theorem encTapes_congr (margin : ℕ) (x y : State GalilVM) (polarity : Fin 16 → Bool)
    (gap : Fin 4 → Bool) (micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl)
    (tapes : Slot → STape Γm)
    (hfpp : ∀ i, y.vm.fpp.program.config.tapes i = x.vm.fpp.program.config.tapes i)
    (hdp : ∀ i, y.vm.dp.config.tapes i = x.vm.dp.config.tapes i)
    (hcounters : counterOf y = counterOf x) (hheads : headOf y = headOf x)
    (hplaces : placeOf y = placeOf x) (hperiod : periodOf y = periodOf x)
    (hanswer : answerOf y = answerOf x)
    (h : EncTapes margin x polarity gap micro tapes) :
    EncTapes margin y polarity gap micro tapes where
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
theorem encTapes_fppStep (margin : ℕ) (x : State GalilVM) (polarity : Fin 16 → Bool)
    (gap : Fin 4 → Bool) (micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl)
    (tapes newTapes : Slot → STape Γm)
    (henc : EncTapes margin x polarity gap micro tapes)
    (i : Fin 9) (f : PalPeg.GalilScaffoldTape.Tape → PalPeg.GalilScaffoldTape.Tape)
    (ctl : PalPeg.GalilScaffoldController.Control)
    (hmoved : newTapes (.inr (.inl i))
      = padLeft margin (mapTape encProg (encTape (f (x.vm.fpp.program.config.tapes i)))))
    (hkept : ∀ slot, slot ≠ (.inr (.inl i) : Slot) → newTapes slot = tapes slot) :
    EncTapes margin
      ⟨ctl, {x.vm with fpp := {x.vm.fpp with program := PalPeg.GalilScaffoldChainInputSupply.FppControl.tape x.vm.fpp i f}}⟩
      polarity gap micro newTapes where
  margins := by
    intro slot
    by_cases hs : slot = (.inr (.inl i) : Slot)
    · rw [hs, hmoved, pos_padLeft]
      omega
    · rw [hkept slot hs]
      exact henc.margins slot
  heads := by
    intro v head hhead
    obtain ⟨view, viewTapes, habs, hrep, hslots⟩ := henc.heads v head hhead
    exact ⟨view, viewTapes, habs, hrep, fun j => by
      rw [hkept _ (by simp), hslots j]⟩
  fpp := by
    intro j
    rw [fppTape_tapes, Function.update_apply]
    by_cases hji : j = i
    · subst hji
      rw [if_pos rfl, hmoved]
    · rw [if_neg hji, hkept _ (by simp [hji])]
      exact henc.fpp j
  dp := by
    intro j
    rw [hkept _ (by simp)]
    exact henc.dp j
  counters := by
    intro c value hvalue
    obtain ⟨segments, habs, hslot⟩ := henc.counters c value hvalue
    exact ⟨segments, habs, by rw [hkept _ (by simp), hslot]⟩
  mirrors := by
    intro m value hvalue
    obtain ⟨segments, habs, hslot⟩ := henc.mirrors m value hvalue
    exact ⟨segments, habs, by rw [hkept _ (by simp), hslot]⟩
  places := by
    intro j place hplace
    obtain ⟨stackTape, junk, hsealed, hlen, hstack, hslot⟩ := henc.places j place hplace
    exact ⟨stackTape, junk, hsealed, hlen, hstack, by rw [hkept _ (by simp), hslot]⟩
  period := by
    intro tape htape
    rw [hkept _ (by simp)]
    exact henc.period tape htape
  answer := by
    intro tape htape
    rw [hkept _ (by simp)]
    exact henc.answer tape htape

/-! ### the mark walk, both directions -/

/-- **the rule that moves the marks tape forward realizes `markForward`.**  It names one
action, at the slot of the preparation machine's eighth tape: write back what the window shows at
its centre, and move right. -/
theorem encTapes_progRight (margin : ℕ) (x : State GalilVM) (polarity : Fin 16 → Bool)
    (gap : Fin 4 → Bool) (micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl)
    (tapes newTapes : Slot → STape Γm)
    (henc : EncTapes margin x polarity gap micro tapes)
    (ctl : PalPeg.GalilScaffoldController.Control) (i : Fin 9)
    (hmoved : newTapes (.inr (.inl i))
      = PalPeg.CloseoutCoreEnc12.actList blankM (tapes (.inr (.inl i)))
          [some ((tapes (.inr (.inl i))).focus, .right)])
    (hkept : ∀ slot, slot ≠ (.inr (.inl i) : Slot) → newTapes slot = tapes slot) :
    EncTapes margin
      ⟨ctl, {x.vm with fpp := {x.vm.fpp with program := PalPeg.GalilScaffoldChainInputSupply.FppControl.tape x.vm.fpp i PalPeg.GalilScaffoldTape.moveRight}}⟩
      polarity gap micro newTapes := by
  refine encTapes_fppStep margin x polarity gap micro tapes newTapes henc i
    PalPeg.GalilScaffoldTape.moveRight ctl ?_ hkept
  rw [hmoved, henc.fpp i, focus_padded]
  show (padLeft margin (mapTape encProg (encTape (x.vm.fpp.program.config.tapes i)))).applyAction
      blankM (encProg (x.vm.fpp.program.config.tapes i).focus, .right) = _
  rw [padded_moveRight]

/-- **and the rule that moves it back realizes `markBack`, when the tape still has a
cell below its head.**  The window's cell below the head says which case this is. -/
theorem encTapes_progLeft (margin : ℕ) (x : State GalilVM) (polarity : Fin 16 → Bool)
    (gap : Fin 4 → Bool) (micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl)
    (tapes newTapes : Slot → STape Γm)
    (henc : EncTapes margin x polarity gap micro tapes)
    (ctl : PalPeg.GalilScaffoldController.Control) (i : Fin 9)
    (hfloor : (x.vm.fpp.program.config.tapes i).left ≠ [])
    (hmoved : newTapes (.inr (.inl i))
      = PalPeg.CloseoutCoreEnc12.actList blankM (tapes (.inr (.inl i)))
          [some ((tapes (.inr (.inl i))).focus, .left)])
    (hkept : ∀ slot, slot ≠ (.inr (.inl i) : Slot) → newTapes slot = tapes slot) :
    EncTapes margin
      ⟨ctl, {x.vm with fpp := {x.vm.fpp with program := PalPeg.GalilScaffoldChainInputSupply.FppControl.tape x.vm.fpp i PalPeg.GalilScaffoldTape.moveLeft}}⟩
      polarity gap micro newTapes := by
  refine encTapes_fppStep margin x polarity gap micro tapes newTapes henc i
    PalPeg.GalilScaffoldTape.moveLeft ctl ?_ hkept
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
    (gap : Fin 4 → Bool) (micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl)
    (tapes : Slot → STape Γm)
    (henc : EncTapes margin x polarity gap micro tapes)
    (ctl : PalPeg.GalilScaffoldController.Control) (i : Fin 9)
    (hfloor : (x.vm.fpp.program.config.tapes i).left = []) :
    EncTapes margin
      ⟨ctl, {x.vm with fpp := {x.vm.fpp with program := PalPeg.GalilScaffoldChainInputSupply.FppControl.tape x.vm.fpp i PalPeg.GalilScaffoldTape.moveLeft}}⟩
      polarity gap micro tapes := by
  have hstep : {x.vm.fpp with program := PalPeg.GalilScaffoldChainInputSupply.FppControl.tape x.vm.fpp i PalPeg.GalilScaffoldTape.moveLeft} = x.vm.fpp := by
    rw [fppStep_fixed x.vm.fpp i PalPeg.GalilScaffoldTape.moveLeft
      (moveLeft_atFloor (x.vm.fpp.program.config.tapes i) hfloor)]
  rw [hstep]
  exact encTapes_congr margin x ⟨ctl, x.vm⟩ polarity gap micro tapes (fun i => rfl) (fun i => rfl) rfl rfl rfl rfl rfl henc

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
  EncControl x p.1 ∧ EncTapes margin x p.1.polarity p.1.gap p.1.micro p.2

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
    (hmoved : newTapes (.inr (.inl 8))
      = PalPeg.CloseoutCoreEnc12.actList blankM (tapes (.inr (.inl 8)))
          [some ((tapes (.inr (.inl 8))).focus, .right)])
    (hkept : ∀ slot, slot ≠ (.inr (.inl 8) : Slot) → newTapes slot = tapes slot) :
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
    encTapes_progRight margin x q.polarity q.gap q.micro tapes newTapes henc.2 x.ctl 8 hmoved hkept⟩

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
    (hmoved : newTapes (.inr (.inl 8))
      = PalPeg.CloseoutCoreEnc12.actList blankM (tapes (.inr (.inl 8)))
          [some ((tapes (.inr (.inl 8))).focus, .left)])
    (hkept : ∀ slot, slot ≠ (.inr (.inl 8) : Slot) → newTapes slot = tapes slot) :
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
  exact encTapes_progLeft margin x q.polarity q.gap q.micro tapes newTapes henc.2 _ 8 hfloor hmoved hkept

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
  exact encTapes_progLeftAtFloor margin x q.polarity q.gap q.micro tapes henc.2 _ 8 hfloor

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
    (hmoved : newTapes (.inr (.inl 7))
      = PalPeg.CloseoutCoreEnc12.actList blankM (tapes (.inr (.inl 7)))
          [some ((tapes (.inr (.inl 7))).focus, .left)])
    (hkept : ∀ slot, slot ≠ (.inr (.inl 7) : Slot) → newTapes slot = tapes slot) :
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
    encTapes_progLeft margin x q.polarity q.gap q.micro tapes newTapes henc.2 x.ctl 7 hfloor hmoved hkept⟩

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
    encTapes_progLeftAtFloor margin x q.polarity q.gap q.micro tapes henc.2 x.ctl 7 hfloor⟩

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
  exact encTapes_congr margin x _ q.polarity q.gap q.micro tapes
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
    (hmoved : newTapes (.inr (.inl 8))
      = PalPeg.CloseoutCoreEnc12.actList blankM (tapes (.inr (.inl 8)))
          [some ((tapes (.inr (.inl 8))).focus, .left)])
    (hkept : ∀ slot, slot ≠ (.inr (.inl 8) : Slot) → newTapes slot = tapes slot) :
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
  exact encTapes_progLeft margin x q.polarity q.gap q.micro tapes newTapes henc.2 _ 8 hfloor hmoved hkept

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
  exact encTapes_progLeftAtFloor margin x q.polarity q.gap q.micro tapes henc.2 _ 8 hfloor

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
