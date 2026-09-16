import PalPeg.ProgramMachine
import PalPeg.ProgLang

/-! A two-tape finite clock controller. Thirty sweeps form one generation;
the last sixteen sweeps grow the next interval. All decisions read tape
focuses and finite phase registers, never an unbounded round number. -/
set_option autoImplicit false
namespace PalPeg.SlotClock
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang

inductive Symbol | blank | edge | tick
  deriving DecidableEq, Fintype

abbrev Ctrl := Bool × Fin 30
def slot (b : Bool) : Fin 2 := if b then 1 else 0

def advance (c : Ctrl) (σ : Fin 2 → Symbol) : Fin 2 → Symbol × Move := fun j =>
  if j = slot c.1 then (σ j, if c.2.val % 2 = 0 then .left else .right)
  else if 14 ≤ c.2.val then
    (if c.2 = 14 ∧ σ (slot c.1) = .edge then .edge else .tick, .right)
  else (σ j, .stay)

def finish (c : Ctrl) (σ : Fin 2 → Symbol) : Ctrl × (Fin 2 → Symbol × Move) :=
  if σ (slot c.1) = .edge then
    if c.2 = 29 then
      ((!c.1, 0), fun j => (if j = slot (!c.1) then .edge else σ j, .stay))
    else ((c.1, nextPhase c.2), fun j => (σ j, .stay))
  else (c, fun j => (σ j, .stay))

def body : PhaseBody Unit Ctrl Symbol 2 2 := fun c _ ph σ =>
  if ph = 0 then (c, advance c σ) else finish c σ

/-- This component expects initialized clock tapes. All-blank startup and
alignment to the four global slot generations are separate obligations. -/
def machine : StructuredMachine Unit (Ctrl × Fin 2) Symbol 2 2 :=
  ofPhases (by decide) (by decide) .blank (false, 0) (fun _ => false) body

def moved (c : Ctrl) (T : Fin 2 → STape Symbol) : Fin 2 → STape Symbol :=
  fun j => (T j).applyAction .blank (advance c (fun j => (T j).focus) j)

def roundState (c : Ctrl) (T : Fin 2 → STape Symbol) : SConfig (Ctrl × Fin 2) Symbol 2 :=
  let U := moved c T
  let r := finish c (fun j => (U j).focus)
  ⟨(r.1, 0), fun j => (U j).applyAction .blank (r.2 j)⟩

theorem round (c : Ctrl) (T : Fin 2 → STape Symbol) :
    machine.sRound ⟨(c, 0), T⟩ () = roundState c T := by
  refine (ofPhases_round (by decide : 0 < 2) (by decide : 0 < 2) Symbol.blank
    (false, 0) (fun _ => false) body c T ()).trans ?_
  simp only [PalPeg.Speedup.MultiStepMachine.roundInputs, Nat.reduceSub,
    List.replicate_succ, List.replicate_zero, phaseRun_cons, phaseRun_nil,
    bodyStep, body, nextPhase, Fin.zero_eta, Fin.isValue, ↓reduceIte]
  rfl

/-- Real generation handoff at phase 29. The old interval ends on its
right boundary; the next interval acquires its right boundary in place.
No traversal proportional to n occurs during this transition. -/
theorem rollover (active : Bool) (l junk : List Symbol) (s : Symbol) (n : ℕ) :
    let T : Fin 2 → STape Symbol := fun j =>
      if j = slot active then ⟨l, s, [.edge]⟩
      else ⟨List.replicate n .tick ++ .edge :: junk, .blank, []⟩
    (machine.sRound ⟨((active, 29), 0), T⟩ ()).state = ((!active, 0), 0) ∧
    (machine.sRound ⟨((active, 29), 0), T⟩ ()).tape (slot (!active)) =
      ⟨List.replicate (n + 1) .tick ++ .edge :: junk, .edge, []⟩ ∧
    (machine.sRound ⟨((active, 29), 0), T⟩ ()).tape (slot active) = ⟨s :: l, .edge, []⟩ := by
  cases active <;>
    simp [round, roundState, moved, advance, finish, slot, STape.applyAction, List.replicate_succ]

def seed (q : ℕ) : Fin 2 → STape Symbol := fun j =>
  if j = 0 then ⟨List.replicate (q - 1) .tick ++ [.edge], .edge, []⟩
  else STape.blankTape .blank

set_option maxRecDepth 4096 in
/-- Kernel-checked execution of a complete first generation. This checks
the concrete controller, but is not the arbitrary-generation invariant. -/
theorem first_generation :
    let y := (List.replicate 30 ()).foldl machine.sRound ⟨((false, 0), 0), seed 1⟩
    y.state = ((true, 0), 0) ∧
      (y.tape 1).left = List.replicate 15 .tick ++ [.edge] ∧
      (y.tape 1).focus = .edge ∧ (y.tape 1).right = [] := by
  decide

/-- info: 'PalPeg.SlotClock.round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms round
/-- info: 'PalPeg.SlotClock.rollover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rollover
/-- info: 'PalPeg.SlotClock.first_generation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms first_generation
end PalPeg.SlotClock
