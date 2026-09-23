import PalPeg.ScaWindowPal
import PalPeg.ScaWindowWorker
import PalPeg.ScaGsTables

/-!
# The window PAL controller instantiated with the real GS workers

Definitions only (no proofs). `WindowPAL` (ScaffoldWindowPal.scala:80-89)
builds two matchers with `ScaffoldWindowWorkers.matcher(circuit, "match$i",
rates.matching)` and two flag workers with `ScaffoldWindowWorkers.flags(circuit,
"flag$i", rates.flags)`, where `rates = GsBatchClock.DEFAULT_BATCH`
(`matching = 2048`, `flags = 32768`, `GsBatchClock.VERIFIED_BATCH`). `ScaffoldWindowWorkers.matcher`/`flags`
(ScaffoldWindowWorkers.scala:184-188) compile `GsMatchHeads.compileMatcher(unit =
false)` over `MATCH_HEADS` and `GsDualFlags.compileDualFlags(unit = false)` over
`DUAL_HEADS` (`isFlags = true`); these are `ScaGsTables.matcherWorker` /
`flagsWorker`. The worker prefix only names circuit keys and is not modelled.
Both copies of each worker start from the same initial state.
-/

set_option autoImplicit false

namespace PalPeg.ScaWindowInstance

open PalPeg.ScaWindowWorker

/-- The abstract `WindowWorkerLike` interface of a `ScaWindowWorker.Worker`. -/
def opsOf (w : Worker) : ScaWindowPal.WorkerOps WorkerState where
  arrive := ScaWindowWorker.arrive w
  resetFlags := ScaWindowWorker.resetFlags w
  start := ScaWindowWorker.start w
  mark := ScaWindowWorker.mark w
  service := ScaWindowWorker.service w
  output := ScaWindowWorker.output
  modeDone := ScaWindowWorker.modeDone
  flags := ScaWindowWorker.flags
  faulted := fun s => s.fault

/-- `ScaffoldWindowWorkers.matcher(_, _, 2048)` (ScaffoldWindowWorkers.scala:184-185). -/
def matcher : Worker := Worker.ofSpec ScaGsTables.matcherWorker

/-- `ScaffoldWindowWorkers.flags(_, _, 32768)` (ScaffoldWindowWorkers.scala:187-188). -/
def flagsW : Worker := Worker.ofSpec ScaGsTables.flagsWorker

def matcherOps : ScaWindowPal.WorkerOps WorkerState := opsOf matcher

def flagsOps : ScaWindowPal.WorkerOps WorkerState := opsOf flagsW

/-- Initial matcher state (`circuit.get(PREVIOUS, …)` defaults). -/
def matcherInit : WorkerState := WorkerState.initial ScaGsTables.matcherWorker

/-- Initial flag-worker state. -/
def flagsInit : WorkerState := WorkerState.initial ScaGsTables.flagsWorker

/-- Run of the instantiated controller over `w`. -/
def windowRun (w : List (Fin 2)) : ScaWindowPal.PalState WorkerState WorkerState :=
  ScaWindowPal.run matcherOps flagsOps matcherInit flagsInit w

/-- Global fault of the instantiated controller after reading `w`. -/
def windowFault (w : List (Fin 2)) : Bool :=
  ScaWindowPal.globalFault matcherOps flagsOps (windowRun w)

/-- Acceptance of `WindowPAL` with the real workers. -/
def windowAccepts (w : List (Fin 2)) : Bool :=
  ScaWindowPal.accepts matcherOps flagsOps matcherInit flagsInit w

end PalPeg.ScaWindowInstance
