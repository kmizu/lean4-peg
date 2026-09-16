import PalPeg.GalilFppInstruction

set_option autoImplicit false
namespace PalPeg.GalilFppWide

/-- The same finite-tape instruction semantics, with a variable tape count.
Marked FPP uses nine tapes and DP uses twelve. Output is written on tapes,
so there is no observer-level emit instruction in this language. -/
inductive Instruction (tapes : ℕ)
  | halt
  | move (tape : Fin tapes) (right : Bool) (next : ℕ)
  | write (tape : Fin tapes) (symbol : Fin 9) (next : ℕ)
  | read (tape : Fin tapes) (choices : List (Fin 9 × ℕ))
  deriving DecidableEq, Inhabited

structure Config (tapes : ℕ) where
  pc : ℕ
  tape : Fin tapes → ℕ → Fin 9
  pos : Fin tapes → ℕ

inductive Execute {tapes : ℕ} : Instruction tapes → Config tapes → Config tapes → Prop
  | right (x : Config tapes) (t : Fin tapes) (n : ℕ) : Execute (.move t true n) x
      { x with pc := n, pos := Function.update x.pos t (x.pos t+1) }
  | left (x : Config tapes) (t : Fin tapes) (n : ℕ) (h : 0 < x.pos t) : Execute (.move t false n) x
      { x with pc := n, pos := Function.update x.pos t (x.pos t-1) }
  | write (x : Config tapes) (t : Fin tapes) (s : Fin 9) (n : ℕ) : Execute (.write t s n) x
      { x with pc := n, tape := Function.update x.tape t (Function.update (x.tape t) (x.pos t) s) }
  | read (x : Config tapes) (t : Fin tapes) (cs : List (Fin 9 × ℕ)) (n : ℕ)
      (h : (x.tape t (x.pos t), n) ∈ cs) : Execute (.read t cs) x { x with pc := n }

inductive Steps {tapes : ℕ} (code : List (Instruction tapes)) :
    Config tapes → List ℕ → Config tapes → Prop
  | nil (x : Config tapes) : Steps code x [] x
  | step (x y z : Config tapes) (i : Instruction tapes) (qs : List ℕ)
      (hi : code[x.pc]? = some i) (he : Execute i x y) (rest : Steps code y qs z) :
      Steps code x (x.pc :: qs) z

theorem steps_append {tapes : ℕ} {code : List (Instruction tapes)}
    {x y z : Config tapes} {qs rs : List ℕ} (hs : Steps code x qs y) (hr : Steps code y rs z) :
    Steps code x (qs ++ rs) z := by
  induction hs with
  | nil => exact hr
  | step x y z i qs hi he hs ih => exact .step _ _ _ _ _ hi he (ih hr)

inductive Completed {tapes : ℕ} (code : List (Instruction tapes)) :
    Config tapes → List ℕ → Config tapes → Prop
  | halt (x : Config tapes) (h : code[x.pc]? = some .halt) : Completed code x [x.pc] x
  | step (x y z : Config tapes) (i : Instruction tapes) (qs : List ℕ)
      (hi : code[x.pc]? = some i) (he : Execute i x y) (rest : Completed code y qs z) :
      Completed code x (x.pc :: qs) z

end PalPeg.GalilFppWide
