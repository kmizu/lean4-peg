import PalPeg.GalilRunSkeleton

/-!
# The concrete boot VM

`PalPeg.GalilRunSkeleton.H_run_of_oracle{,G}` take the initial machine state as
a parameter `boot : List (Fin 2) → GalilVM`, constrained only by the five
hypotheses that `inv_init` consumes.  This module closes that gap: it defines
one concrete `initVM0` — every head on the first place of the encoded input,
every counter empty, the chain idle, the search idle, both program views reset
and halted, no period-only continuation — and discharges the five hypotheses,
all definitionally.

`H_run_of_oracle_boot` is then `H_run_of_oracleG` with `boot := initVM0`, i.e.
`H_run` with no boot parameter left.
-/

set_option autoImplicit false

namespace PalPeg.GalilBootVM

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead

/-- The empty logical place: no letters, focus on a letter cell. -/
def emptyPlace : GalilScaffoldPlace.Place := ⟨[], false⟩

/-- A halted program view with the program counter at `0` and every tape blank.
Both the nine-tape fpp view and the twelve-tape DP view start here. -/
def haltedMachine (n : ℕ) : GalilScaffoldControl.Machine n :=
  ⟨⟨0, fun _ => GalilScaffoldTape.reset⟩, true⟩

/-- **The boot VM.**  `ScaffoldGalil`'s state right after construction, before
the first `init` tick: R/L/C all on the first place of `encoded w`, the five
counters empty, the chain idle, the search idle, the fpp and DP programs reset
and halted, `periodOnly = false`. -/
def initVM0 (w : List (Fin 2)) : GalilVM where
  left := initialHead w
  center := initialHead w
  right := initialHead w
  chain := .idle
  cycle := reset
  remaining := reset
  radius := reset
  length := reset
  replay := reset
  fpp :=
    { mode := .run
      program := haltedMachine 9
      work := reset
      walker := emptyPlace
      finalStage := false }
  search :=
    { mode := .idle
      finalStage := false
      span := reset
      work := reset
      debt := reset
      quarter := 0 }
  dp := haltedMachine 12
  lower := reset
  periodOnly := false
  walker := emptyPlace

/-! ## The five hypotheses of `inv_init` -/

theorem initVM0_right (w : List (Fin 2)) : (initVM0 w).right = initialHead w := rfl

theorem initVM0_radius (w : List (Fin 2)) : (initVM0 w).radius = reset := rfl

theorem initVM0_length (w : List (Fin 2)) : (initVM0 w).length = reset := rfl

theorem initVM0_replay (w : List (Fin 2)) : (initVM0 w).replay = reset := rfl

theorem initVM0_shiftIdle (w : List (Fin 2)) : ShiftIdle (initVM0 w) :=
  (shiftIdle_iff (initVM0 w)).2 rfl

/-! ## `H_run` with the boot parameter closed -/

open PalPeg.GalilRunSkeleton PalPeg.GalilStructuredSkeleton

/-- **`H_run` from the global oracle, booted.**  `H_run_of_oracleG` at
`boot := initVM0`: the machine reaches a refreshed report point on every
nonempty input, given only the cycle oracle. -/
theorem H_run_of_oracle_boot (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (hor : ∀ w : List (Fin 2), CycleOracleG centre place entry q first w) :
    ∀ w : List (Fin 2), 0 < w.length →
      ∃ y : State GalilVM,
        ScaffoldRun (PofC centre place entry) (fun _ => q) (fun _ => first) 2048 w y ∧
        ReportPoint w y ∧ Refreshed (PofC centre place entry w) q first y :=
  H_run_of_oracleG centre place entry q first initVM0
    initVM0_right initVM0_radius initVM0_length initVM0_replay initVM0_shiftIdle hor

#print axioms initVM0_right
#print axioms initVM0_radius
#print axioms initVM0_length
#print axioms initVM0_replay
#print axioms initVM0_shiftIdle
#print axioms H_run_of_oracle_boot

end PalPeg.GalilBootVM
