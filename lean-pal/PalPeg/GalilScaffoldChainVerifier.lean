import PalPeg.GalilScaffoldChainConsume
import PalPeg.GalilScaffoldInputTrace

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainVerifier
open GalilScaffoldInputHead

/-- Decoded FIFO semantics: right stack wins over incoming queue.
The empty/empty branch is excluded by canRight when movement is enabled. -/
abbrev headRight := GalilScaffoldInputTrace.moveRight

def canRight (p : PlaceHead) : Prop :=
  p.gap = false ∨ p.head.right ≠ [] ∨ p.head.incoming ≠ []

def right (p : PlaceHead) : PlaceHead :=
  ⟨if p.gap then headRight p.head else p.head,!p.gap⟩

inductive HeadRight : Head → Head → Prop
  | stack (f ls a rs qs) : HeadRight ⟨f,ls,a :: rs,qs⟩ ⟨a,f :: ls,rs,qs⟩
  | queue (f ls a qs) : HeadRight ⟨f,ls,[],a :: qs⟩ ⟨some a,f :: ls,[],qs⟩

inductive Right : PlaceHead → PlaceHead → Prop
  | gap (h) : Right ⟨h,false⟩ ⟨h,true⟩
  | letter {h k} (hr : HeadRight h k) : Right ⟨h,true⟩ ⟨k,false⟩

theorem right_realize (p : PlaceHead) (hp : canRight p) : Right p (right p) := by
  rcases p with ⟨⟨f,ls,rs,qs⟩,g⟩
  cases g with
  | false => exact Right.gap _
  | true =>
    cases rs with
    | cons a rs => exact Right.letter (HeadRight.stack f ls a rs qs)
    | nil =>
      cases qs with
      | nil => simp [canRight] at hp
      | cons a qs => exact Right.letter (HeadRight.queue f ls a qs)

theorem stack_read (f : Option (Fin 2)) (ls rs : List (Option (Fin 2)))
    (qs : List (Fin 2)) (a : Option (Fin 2)) :
    read (right ⟨⟨f,ls,a :: rs,qs⟩,true⟩) = a.map GalilScaffoldPlace.letter := rfl

theorem queue_read (f : Option (Fin 2)) (ls : List (Option (Fin 2)))
    (qs : List (Fin 2)) (a : Fin 2) :
    read (right ⟨⟨f,ls,[],a :: qs⟩,true⟩) = some (GalilScaffoldPlace.letter a) := rfl

theorem gap_read (h : Head) :
    read (right ⟨h,false⟩) = h.focus.map (fun _ => (2 : Fin 3)) := rfl

/-- A legal left step creates exactly the stack entry consumed on return. -/
theorem right_left (p : PlaceHead) (hp : p.gap = false → p.head.left ≠ []) :
    right (GalilScaffoldInputHead.left p) = p := by
  rcases p with ⟨⟨f,ls,rs,qs⟩,g⟩
  cases g with
  | true => rfl
  | false =>
    cases ls with
    | nil => simp at hp
    | cons a ls => rfl

structure State where
  verifier : PlaceHead
  control : GalilScaffoldChainConsume.State

def consume (s : State) : State :=
  let p := right s.verifier
  ⟨p,GalilScaffoldChainConsume.consume s.control (read p)⟩

/-- The character is no longer an independent input: the same moved
verifier supplies it to the control transition. -/
theorem consume_realize (s : State) (hp : canRight s.verifier) :
    Right s.verifier (consume s).verifier ∧
    (consume s).control = GalilScaffoldChainConsume.consume s.control
      (read (consume s).verifier) :=
  ⟨right_realize s.verifier hp,rfl⟩

theorem consume_mismatch (s : State) (a : Fin 3)
    (ht : GalilScaffoldChainConsume.symbol s.control.period.focus = some a)
    (hne : read (right s.verifier) ≠ some a) :
    (consume s).control = {s.control with broken := true} :=
  GalilScaffoldChainConsume.mismatch s.control a _ ht hne

theorem consume_agrees (s : State) (a : Fin 3)
    (ht : GalilScaffoldChainConsume.symbol s.control.period.focus = some a)
    (hr : read (right s.verifier) = some a) :
    GalilScaffoldCounter.value (consume s).control.distance =
      GalilScaffoldCounter.value s.control.distance+1 ∧
    (consume s).control.broken = s.control.broken := by
  simp [consume, GalilScaffoldChainConsume.consume, ht, hr, GalilScaffoldCounter.inc_value]

/-- On a letter center, right movement reads a gap without touching any
stack/queue, so a gap prediction is discharged from the actual head. -/
theorem consume_gap (control : GalilScaffoldChainConsume.State)
    (h : Head) (a : Fin 2) (hf : h.focus = some a)
    (ht : GalilScaffoldChainConsume.symbol control.period.focus = some 2) :
    let s : State := ⟨⟨h,false⟩,control⟩
    Right s.verifier (consume s).verifier ∧
    GalilScaffoldCounter.value (consume s).control.distance =
      GalilScaffoldCounter.value control.distance+1 ∧
    (consume s).control.broken = control.broken := by
  dsimp only
  refine ⟨right_realize _ (Or.inl rfl), ?_⟩
  apply consume_agrees _ 2 ht
  simp [gap_read, hf]

#print axioms consume_gap
#print axioms consume_agrees
#print axioms consume_realize
#print axioms right_left
#print axioms consume_mismatch
end PalPeg.GalilScaffoldChainVerifier
