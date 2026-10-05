import Complexity.ListMachine

/-!
# Input and output for list programs

* `initP`: from the machine's initial tapes (input bits on tape `0`), build the representation of the lists
  `initLists w`: list `1` holds the input bits (`false ↦ 0`, `true ↦ 1`), every other list is empty.
* `finishP o`: when list `0` is empty and list `o` holds bits, write them on tape `0` from cell `0` (as `bitSym`), a
  blank after them, and halt accepting — the output convention of `PolyTimeComputable`.
-/

namespace Complexity

variable {k : Nat}

def bitElem (b : Bool) : Nat := if b then 1 else 0

def initLists (k : Nat) (w : List Bool) : Lists k := fun j => if j.val = 1 then w.map bitElem else []

section
variable (h1 : 1 < k)

def t0 : Fin k := ⟨0, by omega⟩
def t1 : Fin k := ⟨1, h1⟩

/-- Step A: markers on tapes `1 …`, tape `1` moves right. -/
def initA : Action k := fun r =>
  (fun j => if j.val = 0 then r j else 3, fun j => if j.val = 1 then .R else .S)

/-- Step B (while tape `0` is not blank): move the input symbol to tape `1` as an element, blank tape `0`. -/
def initB : Action k := fun r =>
  (fun j => if j.val = 0 then 0 else if j.val = 1 then r (t0 h1) + 3 else r j,
   fun j => if j.val = 0 ∨ j.val = 1 then .R else .S)

/-- Step C (while tape `1` is not on the marker): both heads left. -/
def initC : Action k := fun r => (r, fun j => if j.val = 0 ∨ j.val = 1 then .L else .S)

/-- Step D: the marker on tape `0`. -/
def initD : Action k := fun r => (fun j => if j.val = 0 then 3 else r j, fun _ => .S)

def initP : Prog k :=
  .seq (.act initA) (.seq (.loop (fun r => r (t0 h1) != 0) (.act (initB h1)))
    (.seq (.loop (fun r => r (t1 h1) != 3) (.act initC)) (.act initD)))

end

section
variable (h0 : 0 < k) (o : Fin k)

/-- Blank cell `0` of tape `0`, move head `o` onto the first element. -/
def finA : Action k := fun r => (fun j => if j.val = 0 then 0 else r j, fun j => if j = o then .R else .S)

/-- Write the bit under head `o` on tape `0`, move both right. -/
def finB : Action k := fun r =>
  (fun j => if j.val = 0 then r o - 3 else r j, fun j => if j.val = 0 ∨ j = o then .R else .S)

def finishP : Prog k :=
  .seq (.act (finA o)) (.seq (.loop (fun r => r o != 0) (.act (finB o))) (.halt true))

end

end Complexity
