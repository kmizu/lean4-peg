import MacroPeg.CBV.ParTableau.Recognition
open Complexity
open Shallot.MacroPeg
open Shallot.MacroPeg.CBV.ParTableau

private def constantMachine (accept : Bool) : TM 0 where
  nq := 4
  na := 3
  delta := fun q _ => (if q = 2 then 3 else if accept then 0 else 1,
    (fun i => Fin.elim0 i), (fun i => Fin.elim0 i))
  three_le_nq := by decide
  three_le_na := by decide
  delta_state := by
    intro q r hq hr
    dsimp
    split
    · omega
    · split <;> omega
  delta_sym := by intro q r hq hr i; exact Fin.elim0 i

private def accepts (out : Option MOutcome) : Option Bool :=
  out.map (fun o => match o with | .ok _ [] => true | _ => false)

def main : IO Unit := do
  let mut checked := 0
  for expected in [false, true] do
    let M := constantMachine expected
    let c := 2
    let degree := 0
    let g := compile M (polynomialDigits c degree)
    let entry := polynomialStart M c degree
    for input in ["", "a", "b", "ab", "xyz", "λb"] do
      let out := accepts (mpegRun g .callByValuePar 2000 entry input.toList)
      if out != some expected then
        throw (IO.userError s!"recognition mismatch: accept={expected}, input={input}, observed={out}")
      checked := checked + 1
  IO.println s!"Par polynomial recognition: {checked} acceptance/rejection checks passed, including empty and Unicode input"
