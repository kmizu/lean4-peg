import MacroPeg.CBV.PrefixClockGrammar
import MacroPeg.CBV.PrefixTupleSearch
import MacroPeg.CBV.PrefixSpans
import MacroPeg.CBV.Indexed
import MacroPeg.CBVtoCBN.CompilerLayout
import Complexity.StepSem

namespace Shallot.MacroPeg.CBV.ParTableau

open PrefixCounters RootObservation
open CBVtoCBN (paramsFrom paramsFrom_firstOrder)
open Complexity (TM Move)

inductive Node (k : Nat) where
  | state (q : Nat)
  | head (tape : Fin k)
  | cell (tape : Fin k) (symbol : Nat)
  | read (tape : Fin k) (symbol : Nat)
  | incHead (tape : Fin k)
  | decHead (tape : Fin k)
  deriving DecidableEq

def nodes {k : Nat} (M : TM k) : List (Node k) :=
  (List.range M.nq).map Node.state ++ (List.finRange k).map Node.head ++
    (List.finRange k).flatMap (fun i => (List.range M.na).map (Node.cell i)) ++
    (List.finRange k).flatMap (fun i => (List.range M.na).map (Node.read i)) ++
    (List.finRange k).map Node.incHead ++ (List.finRange k).map Node.decHead

def slotSize (digits : Nat) : Nat := 4 + 2 * digits

def address {k : Nat} (M : TM k) (digits : Nat) (node : Node k) : Nat :=
  2 + slotSize digits * (nodes M).idxOf node

def width (digits : Nat) : Nat := 1 + 2 * digits
def allRefs (digits : Nat) : List MExp := paramsFrom 0 (width digits)
def timeRefs (digits : Nat) : List MExp := paramsFrom 1 digits
def posRefs (digits : Nat) : List MExp := paramsFrom (1 + digits) digits
def swappedRefs (digits : Nat) : List MExp := .param 0 :: (posRefs digits ++ timeRefs digits)

def truth (b : Bool) : MExp := if b then .eps else MExp.failAlways

def conjunction : List MExp → MExp
  | [] => .eps
  | a :: as => .seq a (conjunction as)

def zeroDigits (ds : List MExp) : MExp :=
  conjunction (ds.map (fun a => .call 0 [a, .lit []]))

def lowDigit (digits : Nat) : MExp := if digits = 0 then .lit [] else .param 0

/-- The initial tape reads the original characters directly. Character 'b'
is bit true; every other character is bit false. No position code is added. -/
def initialCell (digits : Nat) (symbol : Nat) : MExp :=
  let highZero := zeroDigits (paramsFrom 1 (digits - 1))
  let low := lowDigit digits
  if symbol = 0 then .alt (.notP highZero) (atEnd low)
  else if symbol = 1 then
    .seq highZero (atPosition low (.seq (.notP (.chr 'b')) .any))
  else if symbol = 2 then .seq highZero (atPosition low (.chr 'b'))
  else MExp.failAlways

def zeroBody {k : Nat} (digits : Nat) : Node k → MExp
  | .state q => truth (q == 2)
  | .head _ => zeroDigits (paramsFrom 0 digits)
  | .cell i s => if i.val = 0 then initialCell digits s else truth (s == 0)
  | _ => MExp.failAlways

def caseTest {k : Nat} (M : TM k) (digits q : Nat) (r : Fin k → Nat) : MExp :=
  conjunction (.call (address M digits (.state q)) (allRefs digits) ::
    (List.finRange k).map (fun i => .call (address M digits (.read i (r i))) (allRefs digits)))

def movedHead {k : Nat} (M : TM k) (digits : Nat) (i : Fin k) : Move → MExp
  | .S => .call (address M digits (.head i)) (allRefs digits)
  | .R => .call (address M digits (.decHead i)) (swappedRefs digits)
  | .L =>
    .alt (.call (address M digits (.incHead i)) (swappedRefs digits))
      (.seq (zeroDigits (posRefs digits)) (.call (address M digits (.head i)) (allRefs digits)))

/-- These are precisely the finite transition cases of the source TM.
All query calls in this expression refer to the preceding time. -/
def nextBody {k : Nat} (M : TM k) (digits : Nat) : Node k → MExp
  | .state q =>
    alternatives (((Complexity.combos M).filter
      (fun p => Complexity.nextState M p.1 p.2 == q)).map (fun p => caseTest M digits p.1 p.2))
  | .head i =>
    alternatives ((Complexity.combos M).map (fun p =>
      .seq (caseTest M digits p.1 p.2) (movedHead M digits i (Complexity.moveOf M p.1 p.2 i))))
  | .cell i s =>
    let head := .call (address M digits (.head i)) (allRefs digits)
    .alt (.seq (.notP head) (.call (address M digits (.cell i s)) (allRefs digits)))
      (.seq head (alternatives (((Complexity.combos M).filter
        (fun p => Complexity.writeSym M p.1 p.2 i == s)).map (fun p => caseTest M digits p.1 p.2))))
  | _ => MExp.failAlways

def zeroSlot (digits : Nat) : Nat := 1 + 2 * digits
def nextSlot (digits : Nat) : Nat := 2 + 2 * digits

def timeRules {k : Nat} (M : TM k) (digits base : Nat) (node : Node k) : List MRule :=
  clockBlock base 0 (base + nextSlot digits) (base + zeroSlot digits) digits digits ++
    [⟨digits, zeroBody digits node⟩, ⟨width digits, nextBody M digits node⟩]

/-- Arithmetic helpers receive [N, position digits, time digits]. -/
def headAdapter {k : Nat} (M : TM k) (digits : Nat) (i : Fin k) : MExp :=
  .call (address M digits (.head i)) (swappedRefs digits)

/-- A tuple-search leaf receives [position digits, N, time digits]. -/
def readLeaf {k : Nat} (M : TM k) (digits : Nat) (i : Fin k) (s : Nat) : MExp :=
  let args := .param digits :: (paramsFrom (digits + 1) digits ++ paramsFrom 0 digits)
  .seq (.call (address M digits (.head i)) args) (.call (address M digits (.cell i s)) args)

def rawRules {k : Nat} (M : TM k) (digits base : Nat) (node : Node k) : List MRule :=
  match node with
  | .state _ | .head _ | .cell _ _ => timeRules M digits base node
  | .incHead i =>
    [⟨width digits, successorBody 0 (base + 1) 1 digits digits⟩,
      ⟨width digits, headAdapter M digits i⟩]
  | .decHead i =>
    clockBlock base 0 (base + zeroSlot digits) 1 digits digits ++
      [⟨width digits, headAdapter M digits i⟩]
  | .read i s =>
    [⟨width digits, tupleSearch (base + 1) (base + zeroSlot digits) digits
      (.param 0 :: timeRefs digits)⟩] ++
      tupleRules (base + 1) (base + zeroSlot digits) digits (1 + digits) ++
        [⟨width digits, readLeaf M digits i s⟩]

def failRule : MRule := ⟨0, MExp.failAlways⟩

/-- Every node owns a fixed-width slot; unused addresses explicitly fail. -/
def nodeRules {k : Nat} (M : TM k) (digits base : Nat) (node : Node k) : List MRule :=
  (List.range (slotSize digits)).map (fun j => ((rawRules M digits base node)[j]?).getD failRule)

def generatedRules {k : Nat} (M : TM k) (digits : Nat) : List MRule :=
  (nodes M).flatMap (fun node => nodeRules M digits (address M digits node) node)

def compile {k : Nat} (M : TM k) (digits : Nat) : MGrammar :=
  ⟨⟨2, equalBody 0⟩ :: ⟨digits, MExp.failAlways⟩ :: generatedRules M digits⟩

/-- Query the accepting state at time (n+1)^digits-1, then consume the
original input. Empty-input time is zero and needs a separate P wrapper. -/
def start {k : Nat} (M : TM k) (digits : Nat) : MExp :=
  .seq (.andP (.call (address M digits (.state 0))
    (.star .any :: (List.replicate digits (.star .any) ++ List.replicate digits (.lit [])))))
      (.star .any)

end Shallot.MacroPeg.CBV.ParTableau
