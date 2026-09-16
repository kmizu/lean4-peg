import PalPeg.GalilFppFallbackBits

set_option autoImplicit false
namespace PalPeg.GalilFppCompare
open GalilFppInstruction GalilFppCode GalilFppFallbackBits

/-- Four input letters and the right-end marker. -/
def symbol (a : Fin 5) : Fin 9 := if h : a.val < 4 then ⟨a.val, by omega⟩ else 5
def branch (j : Fin 4) (a : Fin 5) : ℕ := if a.val = j.val then 62 else 106+offset j
def choices (j : Fin 4) : List (Fin 9 × ℕ) := List.ofFn (fun a : Fin 5 => (symbol a, branch j a))

theorem compare_code : ∀ j : Fin 4, code[67+offset j]? = some (.read 0 (choices j)) := by decide

/-- The actual retry advances A to the compared character, then branches
to matched or failed exactly according to that character. -/
theorem retry_compare (j : Fin 4) (a : Fin 5) (x : Config)
    (hp : x.pc = 68+offset j) (hc : x.tape 0 (x.pos 0+1) = symbol a) :
    Steps code x [68+offset j,67+offset j]
      { x with pc := branch j a, pos := Function.update x.pos 0 (x.pos 0+1) } := by
  let y : Config := { x with pc := 67+offset j, pos := Function.update x.pos 0 (x.pos 0+1) }
  have hi : code[x.pc]? = some (.move 0 true (67+offset j)) := by rw [hp]; fin_cases j <;> rfl
  have he : Execute (.read 0 (choices j)) y
      { x with pc := branch j a, pos := Function.update x.pos 0 (x.pos 0+1) } := by
    apply Execute.read
    change (x.tape 0 (x.pos 0+1), branch j a) ∈ choices j
    rw [hc]
    exact List.mem_ofFn.mpr ⟨a, rfl⟩
  simpa only [hp] using Steps.step x y _ _ _ hi (.right _ _ _)
    (.step y _ _ _ [] (compare_code j) he (.nil _))

def previousSymbol : Option (Fin 4) → Fin 9
  | none => 4
  | some a => ⟨a.val, by omega⟩

/-- After a mismatch, A returns to the old candidate. The marker chooses
failedAtLeft; a letter chooses copySToT for the same input-letter instance. -/
theorem mismatch (j : Fin 4) (a : Option (Fin 4)) (x : Config)
    (hp : x.pc = 106+offset j) (hpos : 0 < x.pos 0)
    (hc : x.tape 0 (x.pos 0-1) = previousSymbol a) :
    Steps code x [106+offset j,105+offset j]
      { x with
        pc := if a.isNone then 66 else 97+offset j
        pos := Function.update x.pos 0 (x.pos 0-1) } := by
  let y : Config := { x with pc := 105+offset j, pos := Function.update x.pos 0 (x.pos 0-1) }
  have hi : code[x.pc]? = some (.move 0 false (105+offset j)) := by rw [hp]; fin_cases j <;> rfl
  have hi' : code[y.pc]? = some (.read 0 [(4,66),(0,97+offset j),(1,97+offset j),(2,97+offset j),(3,97+offset j)]) := by
    fin_cases j <;> rfl
  have he : Execute (.read 0 [(4,66),(0,97+offset j),(1,97+offset j),(2,97+offset j),(3,97+offset j)]) y
      { x with
        pc := if a.isNone then 66 else 97+offset j
        pos := Function.update x.pos 0 (x.pos 0-1) } := by
    apply Execute.read
    change (x.tape 0 (x.pos 0-1), _) ∈ _
    rw [hc]
    cases a with
    | none => simp [previousSymbol]
    | some a => fin_cases a <;> simp [previousSymbol]
  simpa only [hp] using Steps.step x y _ _ _ hi (.left _ _ _ hpos)
    (.step y _ _ _ [] hi' he (.nil _))

/-- Combining the two dispatches restores A exactly on a failed comparison. -/
theorem retry_mismatch (j : Fin 4) (a : Fin 5) (old : Option (Fin 4)) (x : Config)
    (hp : x.pc = 68+offset j) (ha : a.val ≠ j.val)
    (hc : x.tape 0 (x.pos 0+1) = symbol a) (hold : x.tape 0 (x.pos 0) = previousSymbol old) :
    Steps code x [68+offset j,67+offset j,106+offset j,105+offset j]
      { x with pc := if old.isNone then 66 else 97+offset j } := by
  have hr := retry_compare j a x hp hc
  let y : Config := { x with pc := branch j a, pos := Function.update x.pos 0 (x.pos 0+1) }
  have hm := mismatch j old y (by simp [y, branch, ha]) (by simp [y]) (by simpa [y] using hold)
  have hs := GalilFppCopy.steps_append hr hm
  simpa [y] using hs

theorem retry_hit (j : Fin 4) (x : Config) (hp : x.pc = 68+offset j)
    (hc : x.tape 0 (x.pos 0+1) = (⟨j.val, by omega⟩ : Fin 9)) :
    Steps code x [68+offset j,67+offset j]
      { x with pc := 62, pos := Function.update x.pos 0 (x.pos 0+1) } := by
  let a : Fin 5 := ⟨j.val, by omega⟩
  have hs : symbol a = (⟨j.val, by omega⟩ : Fin 9) := by simp [symbol, a, j.isLt]
  have hr := retry_compare j a x hp (hc.trans hs.symm)
  simpa [branch, a] using hr

def tapeUntouched (t : Fin 7) : Instruction → Bool
  | .write u _ _ => u != t
  | _ => true

/-- All actual instructions preserve both input copies A and B. -/
theorem input_immutable : code.all (fun i => tapeUntouched 0 i && tapeUntouched 1 i) = true := by decide

theorem execute_tape {i : Instruction} {x y : Config} (he : Execute i x y) (t : Fin 7)
    (ht : tapeUntouched t i = true) : y.tape t = x.tape t := by
  cases he with
  | write x u s k =>
    have hn : u ≠ t := by simpa [tapeUntouched] using ht
    simp [Function.update_of_ne (Ne.symm hn)]
  | _ => rfl

theorem input_tapes {x y : Config} {qs : List ℕ} (hs : Steps code x qs y) :
    y.tape 0 = x.tape 0 ∧ y.tape 1 = x.tape 1 := by
  induction hs with
  | nil => exact ⟨rfl, rfl⟩
  | step x y z i qs hi he hs ih =>
    have hc := List.all_eq_true.mp input_immutable i (List.mem_of_getElem? hi)
    have hh : tapeUntouched 0 i = true ∧ tapeUntouched 1 i = true := by simpa using hc
    exact ⟨ih.1.trans (execute_tape he 0 hh.1), ih.2.trans (execute_tape he 1 hh.2)⟩

#print axioms input_tapes
#print axioms retry_mismatch
end PalPeg.GalilFppCompare
