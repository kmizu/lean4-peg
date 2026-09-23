import Mathlib

/-!
# GS head-program instruction set (mirror of the Scala `pal` sources)

Data-only mirror of `scala/pal/src/main/scala/pal/GsProgram.scala` (the finite
instruction table `Program` of a GS head controller) together with the
metadata `WindowWorker` (`ScaffoldWindowWorkers.scala`) derives from it.
Head names are kept as `String`, exactly as in Scala. No semantics, no proofs.
The concrete programs live in `PalPeg.ScaGsTables` (generated).
-/

set_option autoImplicit false

namespace PalPeg.ScaGsProgram

/-- `Event.Movement` (`GsProgram.scala:47`): move `head` by `delta` cells. -/
structure Movement where
  head : String
  delta : Int
  deriving DecidableEq, Repr

/-- `Event` (`GsProgram.scala:12-44`): one instruction of the head table.
The tests (`equal`, `less`, `symbols`, `available`) have two successors ordered
false/true; every other instruction has one (`halt`: none). -/
inductive Event where
  /-- `Move(moves)` (`GsProgram.scala:17`): a batch of head moves applied simultaneously. -/
  | move (moves : List Movement)
  /-- `Copy(target, source)` (`GsProgram.scala:20`): `target := source`. -/
  | copy (target source : String)
  /-- `Equal(left, right)` (`GsProgram.scala:22`): test. -/
  | equal (left right : String)
  /-- `Less(left, right)` (`GsProgram.scala:24`): test. -/
  | less (left right : String)
  /-- `Symbols(left, right)` (`GsProgram.scala:27`): compare the symbols under two heads (test). -/
  | symbols (left right : String)
  /-- `Border(head)` (`GsProgram.scala:30`): report a head coordinate. -/
  | border (head : String)
  /-- `Flag(value)` (`GsProgram.scala:33`): emit one palindrome-prefix flag bit. -/
  | flag (value : Bool)
  /-- `Available(head)` (`GsProgram.scala:36`): has the cell under `head` arrived (test). -/
  | available (head : String)
  /-- `AssertEqual(left, right)` (`GsProgram.scala:39`): verifier deadline check. -/
  | assertEqual (left right : String)
  /-- `Match(head)` (`GsProgram.scala:42`): report a positive match ending at `head`. -/
  | «match» (head : String)
  /-- `Halt` (`GsProgram.scala:44`). -/
  | halt
  deriving DecidableEq, Repr

namespace Event

/-- `Event.op` (`GsProgram.scala:10`): the Python opcode string. -/
def op : Event → String
  | .move _ => "move"
  | .copy _ _ => "copy"
  | .equal _ _ => "equal"
  | .less _ _ => "less"
  | .symbols _ _ => "symbols"
  | .border _ => "border"
  | .flag _ => "flag"
  | .available _ => "available"
  | .assertEqual _ _ => "assert_equal"
  | .«match» _ => "match"
  | .halt => "halt"

end Event

/-- `Row(event, targets)` (`GsProgram.scala:62`): successors of a test are ordered false/true. -/
structure Row where
  event : Event
  targets : List Nat
  deriving DecidableEq, Repr

/-- `Program(code, start, k, constructionStates)` (`GsProgram.scala:69`).
State `0` is the halting sink introduced by `compileController`
(`GsProgram.scala:153-155`, returned generators map to `0`). -/
structure Program where
  code : List Row
  start : Nat
  k : Nat
  constructionStates : Nat := 0
  deriving DecidableEq, Repr

/-- `GsHeads.TESTS` (`GsHeads.scala:32`). -/
def tests : List String := ["equal", "less", "symbols"]

/-- `GsMatchHeads.MATCH_TESTS` (`GsMatchHeads.scala:21`): `TESTS + "available"`. -/
def matchTests : List String := ["equal", "less", "symbols", "available"]

/-- `ReaderLiveness.colors` / `registers` (`GsHeadLiveness.scala:28-31`) of
`GsHeadLiveness.analyzeReaders program` (`GsHeadLiveness.scala:144`): the
register assigned to each symbol-reading head. `WindowWorker` names register
`i` as `prefix ++ ".data" ++ toString i` (`ScaffoldWindowWorkers.scala:33`). -/
structure ReaderColors where
  colors : List (String × Nat)
  registers : Nat
  deriving DecidableEq, Repr

/-- `Liveness.colors` / `registers` (`GsHeadLiveness.scala:8-11`) of
`GsHeadLiveness.analyze program names (observePositions := false)
(availabilityDistance := false)` as called by `WindowLiveDistances`
(`ScaffoldWindowLive.scala:10`): the signed register assigned to each live
head-difference pair. -/
structure DistanceColors where
  colors : List ((String × String) × Nat)
  registers : Nat
  deriving DecidableEq, Repr

/-- The static data a `WindowWorker` (`ScaffoldWindowWorkers.scala:27-29`) is
built from: the program, the head names, the service quantum, whether it is a
flag worker, plus the derived reader/distance registers and the maximal batch
movement `movement` (`ScaffoldWindowWorkers.scala:34-39`, `maxOption.getOrElse 1`). -/
structure WorkerSpec where
  program : Program
  names : List String
  quantum : Nat
  isFlags : Bool
  readers : ReaderColors
  distances : DistanceColors
  movement : Nat
  deriving DecidableEq, Repr

end PalPeg.ScaGsProgram
