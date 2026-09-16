import Mathlib

set_option autoImplicit false
namespace PalPeg.GalilFppInstruction

/-- Symbol indices: a,b,s,#,^,$,_,0,1. Tape indices agree with Scala A..FRONT. -/
inductive Instruction
  | halt
  | emit (next : ℕ)
  | move (tape : Fin 7) (right : Bool) (next : ℕ)
  | write (tape : Fin 7) (symbol : Fin 9) (next : ℕ)
  | read (tape : Fin 7) (choices : List (Fin 9 × ℕ))
  deriving DecidableEq, Inhabited

def successors : Instruction → List ℕ
  | .halt => []
  | .emit n | .move _ _ n | .write _ _ n => [n]
  | .read _ choices => choices.map Prod.snd

def charged : Instruction → Bool
  | .halt | .emit _ | .move _ _ _ => true
  | .read t _ => t == 6
  | .write _ _ _ => false

def projection (i : Instruction) := (charged i, successors i)

/-- Reference tape semantics, with nonnegative heads as in FppFinite.Execution.
These proof-level functions are not extra runtime registers. -/
structure Config where
  pc : ℕ
  tape : Fin 7 → ℕ → Fin 9
  pos : Fin 7 → ℕ
  output : List ℕ

/-- Successful non-halt instructions. Undefined reads and left-end
crossings have no transition, matching the Scala exceptions. -/
inductive Execute : Instruction → Config → Config → Prop
  | emit (x : Config) (n : ℕ) : Execute (.emit n) x
      { x with pc := n, output := x.output ++ [x.pos 0] }
  | right (x : Config) (t : Fin 7) (n : ℕ) : Execute (.move t true n) x
      { x with pc := n, pos := Function.update x.pos t (x.pos t + 1) }
  | left (x : Config) (t : Fin 7) (n : ℕ) (h : 0 < x.pos t) : Execute (.move t false n) x
      { x with pc := n, pos := Function.update x.pos t (x.pos t - 1) }
  | write (x : Config) (t : Fin 7) (s : Fin 9) (n : ℕ) : Execute (.write t s n) x
      { x with pc := n, tape := Function.update x.tape t (Function.update (x.tape t) (x.pos t) s) }
  | read (x : Config) (t : Fin 7) (choices : List (Fin 9 × ℕ)) (n : ℕ)
      (h : (x.tape t (x.pos t), n) ∈ choices) : Execute (.read t choices) x { x with pc := n }

theorem execute_successor {i : Instruction} {x y : Config} (h : Execute i x y) :
    y.pc ∈ successors i := by
  cases h with
  | emit => simp [successors]
  | right => simp [successors]
  | left => simp [successors]
  | write => simp [successors]
  | read x t choices n h => exact List.mem_map.mpr ⟨_, h, rfl⟩

/-- Any finite prefix of successful instructions; no eventual halt is assumed. -/
inductive Steps (code : List Instruction) : Config → List ℕ → Config → Prop
  | nil (x : Config) : Steps code x [] x
  | step (x y z : Config) (i : Instruction) (qs : List ℕ)
      (hi : code[x.pc]? = some i) (hstep : Execute i x y) (rest : Steps code y qs z) :
      Steps code x (x.pc :: qs) z

/-- A terminating tape execution records every instruction, including halt. -/
inductive Completed (code : List Instruction) : Config → List ℕ → Config → Prop
  | halt (x : Config) (h : code[x.pc]? = some .halt) : Completed code x [x.pc] x
  | step (x y z : Config) (i : Instruction) (qs : List ℕ)
      (hi : code[x.pc]? = some i) (hstep : Execute i x y) (rest : Completed code y qs z) :
      Completed code x (x.pc :: qs) z

end PalPeg.GalilFppInstruction
