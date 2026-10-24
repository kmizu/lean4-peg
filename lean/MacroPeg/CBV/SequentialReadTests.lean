import MacroPeg.CBV.SequentialTokenInputMachine

/-! Fixed symbol guards for all successful reading primitives and zero-width
value primitives. Literal characters stay in the finite source program. -/
namespace Shallot.MacroPeg.CBV.SequentialReadTests
open Complexity
open SequentialCaptureCopyMachine (character)
open SequentialTokenMatchMachine (Test runTests)

inductive Read where
  | eps
  | any
  | chr (c : Char)
  | range (lo hi : Char)
  | lit (word : List Char)
  | dbg (body : MExp)
  | lam (arity : Nat) (body : MExp)

def expr : Read → MExp
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range lo hi => .range lo hi
  | .lit w => .lit w
  | .dbg e => .dbg e
  | .lam a e => .lam a e

def literal (w : List Char) : List Test := w.map (fun c => symIs (character c))
def tests : Read → List Test
  | .eps | .dbg _ | .lam _ _ => []
  | .any => [fun _ => true]
  | .chr c => [symIs (character c)]
  | .range lo hi => [fun s => decide (lo.toNat ≤ s-5 ∧ s-5 ≤ hi.toNat)]
  | .lit w => literal w

theorem literal_run (w X : List Char) : runTests (literal w) X=Shallot.stripPrefix? w X := by
  induction w generalizing X with
  | nil => rfl
  | cons c w ih => cases X with
    | nil => rfl
    | cons d X =>
      change (if symIs (character c) (character d+4) then runTests (literal w) X else none) =
        (if Shallot.beqChar c d then Shallot.stripPrefix? w X else none)
      rw [ih]
      by_cases he : c.toNat=d.toNat
      · simp [symIs,character,Shallot.beqChar,he]
      · simp [symIs,character,Shallot.beqChar,he,Ne.symm he]

theorem atom_result (read : Read) (x : List Char) (E : SequentialSharedWords.CaptureEnv)
    (p : Nat) (hp : p ≤ x.length) :
    SequentialSharedWords.atom x E (expr read) p =
      some ((runTests (tests read) (sfx x p)).map List.length) := by
  cases read with
  | eps => simp [expr,tests,runTests,SequentialSharedWords.atom,length_sfx x hp]
  | dbg e => simp [expr,tests,runTests,SequentialSharedWords.atom,length_sfx x hp]
  | lam a e => simp [expr,tests,runTests,SequentialSharedWords.atom,length_sfx x hp]
  | lit w =>
    simp only [expr,tests,literal_run,SequentialSharedWords.atom]
    cases Shallot.stripPrefix? w (sfx x p) <;> rfl
  | any => cases h : sfx x p <;> simp [expr,tests,runTests,SequentialSharedWords.atom,h]
  | chr c => cases h : sfx x p with
    | nil => simp [expr,tests,runTests,SequentialSharedWords.atom,h]
    | cons d X =>
      by_cases he : c.toNat=d.toNat
      · simp [expr,tests,runTests,SequentialSharedWords.atom,h,symIs,character,Shallot.beqChar,he]
      · simp [expr,tests,runTests,SequentialSharedWords.atom,h,symIs,character,Shallot.beqChar,he,Ne.symm he]
  | range lo hi => cases h : sfx x p with
    | nil => simp [expr,tests,runTests,SequentialSharedWords.atom,h]
    | cons d X =>
      by_cases he : lo.toNat ≤ d.toNat ∧ d.toNat ≤ hi.toNat <;>
        simp [expr,tests,runTests,SequentialSharedWords.atom,h,character,Shallot.leChar,Nat.add_assoc,he]

end Shallot.MacroPeg.CBV.SequentialReadTests
