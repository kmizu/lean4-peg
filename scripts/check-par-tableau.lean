import MacroPeg.CBV.ParTableau.Compiler
open Complexity
open Shallot.MacroPeg
open Shallot.MacroPeg.CBV
open Shallot.MacroPeg.CBV.ParTableau

private def machine : TM 1 where
  nq := 4
  na := 3
  delta := fun q r =>
    (if r 0 = 0 then (if q = 3 then 1 else 0) else (if q = 3 ∨ r 0 = 1 then 3 else 2),
      (fun _ => 2), (fun _ => .R))
  three_le_nq := by decide
  three_le_na := by decide
  delta_state := by intro q r hq hr; dsimp; split <;> split <;> omega
  delta_sym := by intro q r hq hr i; change 2 < 3; decide

private def digitsOf (base width value : Nat) : List Nat :=
  (List.range width).map (fun j => value / base ^ j % base)
private def check (g : MGrammar) (x : List Char) (e : MExp) (expected : Bool) (label : String) : IO Unit := do
  let actual := (mpegRun g .callByValuePar 1000 e x).map MOutcome.restOf
  let want := some (if expected then some x else none)
  if actual != want then throw (IO.userError s!"mismatch {label}; input={String.ofList x}")

private def leftMachine : TM 1 where
  nq := 4
  na := 3
  delta := fun q _ => (if q = 2 then 3 else 2,
    (fun _ => if q = 2 then 2 else 1), (fun _ => if q = 2 then .L else .R))
  three_le_nq := by decide
  three_le_na := by decide
  delta_state := by intro q r hq hr; dsimp; split <;> omega
  delta_sym := by intro q r hq hr i; dsimp; split <;> omega

private def twoTape : TM 2 where
  nq := 4
  na := 3
  delta := fun q r => (if q = 3 then 0 else 3,
    (fun i => if i.val = 0 then r 1 else r 0), (fun i => if i.val = 0 then .R else .L))
  three_le_nq := by decide
  three_le_na := by decide
  delta_state := by intro q r hq hr; dsimp; split <;> omega
  delta_sym := by intro q r hq hr i; dsimp; split; exact hr 1; exact hr 0

private def extraChecks {k : Nat} (M : TM k) (label input : String) (d times positions : Nat) : IO Nat := do
  let x := input.toList
  let g := compile M d
  let mut checked := 0
  for t in List.range times do
    let c := M.run (initCfg k (x.map (· == 'b'))) t
    for p in List.range positions do
      let args := PrefixCounters.prefixValues x (x.length ::
        (digitsOf (x.length+1) d t ++ digitsOf (x.length+1) d p))
      for q in List.range M.nq do
        check g x (.call (address M d (.state q)) args) (c.state == q) s!"{label} state t={t} p={p} q={q}"
        checked := checked + 1
      for i in List.finRange k do
        check g x (.call (address M d (.head i)) args) (c.pos i == p) s!"{label} head t={t} p={p} tape={i}"
        checked := checked + 1
        for sym in List.range M.na do
          check g x (.call (address M d (.cell i sym)) args) (c.cells i p == sym) s!"{label} cell t={t} p={p} sym={sym}"
          check g x (.call (address M d (.read i sym)) args) (c.read i == sym) s!"{label} read t={t} p={p} sym={sym}"
          checked := checked + 2
  return checked

def main : IO Unit := do
  let mut checked := 0
  for input in ["", "a", "b", "ab", "bb"] do
    let x := input.toList
    let bits := x.map (· == 'b')
    for d in [1, 2] do
      let g := compile machine d
      let cap := (x.length + 1)^d
      for t in List.range (min cap 3) do
        let c := machine.run (initCfg 1 bits) t
        for p in List.range (min cap 3) do
          let args := PrefixCounters.prefixValues x (x.length :: (digitsOf (x.length+1) d t ++ digitsOf (x.length+1) d p))
          for q in List.range machine.nq do
            check g x (.call (address machine d (.state q)) args) (c.state == q) s!"state d={d} t={t} p={p} q={q}"
            checked := checked + 1
          check g x (.call (address machine d (.head 0)) args) (c.pos 0 == p) s!"head d={d} t={t} p={p}"
          checked := checked + 1
          for s in List.range machine.na do
            check g x (.call (address machine d (.cell 0 s)) args) (c.cells 0 p == s) s!"cell d={d} t={t} p={p} s={s}"
            check g x (.call (address machine d (.read 0 s)) args) (c.read 0 == s) s!"read d={d} t={t} p={p} s={s}"
            checked := checked + 2
  checked := checked + (← extraChecks leftMachine "left-clamp" "b" 2 3 3)
  checked := checked + (← extraChecks twoTape "two-tape" "ab" 1 2 2)
  IO.println s!"Par tableau: {checked} state/head/cell/read queries match TM.run"
