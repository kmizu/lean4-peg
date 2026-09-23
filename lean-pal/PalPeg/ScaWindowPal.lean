import Mathlib

/-!
# The Scala window PAL controller, transcribed at the abstract level

Definitions only (no proofs). This mirrors
`scala/pal/src/main/scala/pal/ScaffoldWindowPal.scala` (classes `WindowStage`
and `WindowPAL`) at the level of *meaning*, not bit encoding:

* A persistent `Stack` whose cells carry no payload (`history`, `power`,
  `nextBirth`, and each stage's `half` / `clock`; all live in the same
  unit-payload `historyPool`, ScaffoldWindowPal.scala:90) is its depth `ℕ`:
  `push` = `+1`, `drop` = `pred` (dropping an empty stack keeps it empty,
  ScaffoldCircuitStructs.scala:109-114), `copyFrom` = assignment,
  `empty` = `= 0`.
* A `FlagStack` (ScaffoldFlagPackets.scala:55) is a `List Bool` with its top at
  the head: packets written by one `PacketWriter` are consecutive pushes, and
  `pop` at a packet boundary follows the back pointer to the previous root
  (ScaffoldFlagPackets.scala:77-86). Popping an empty stack raises a
  `require` violation, returns `false`, and leaves the stack empty.
* `circuit.require(cond, enabled)` sets the sticky circuit fault
  (ScaffoldCircuit.scala:317-322). Acceptance is `output ∧ ¬fault`, and the
  empty word is accepted (`initialAccepting = true`,
  ScaffoldCircuit.scala:324-343, ScaffoldWindowPal.scala:160).
* The GS workers (`WindowWorker`, ScaffoldWindowWorkers.scala) are abstracted
  as `WorkerOps`. Their own `require` violations are carried by the worker as a
  sticky bit `faulted`; since the Scala fault is one global disjunction, the
  global fault is the controller's `fault` or any worker's `faulted`.
-/

set_option autoImplicit false

namespace PalPeg.ScaWindowPal

/-- Abstract GS worker (`WindowWorkerLike`, ScaffoldWindowWorkers.scala:14-25).

`arrive` takes the current input letter explicitly: in Scala the worker's
`WindowStream` records `circuit.input()` for the current node at construction
(ScaffoldWindowStream.scala:259) and `arrive` moves the `end` head over it
(ScaffoldWindowWorkers.scala:65-69). `faulted` is the worker's sticky share of
the global circuit fault (requires in `start`, `service`, head motion). -/
structure WorkerOps (W : Type) where
  /-- `arrive()`, ScaffoldWindowWorkers.scala:65. -/
  arrive : Fin 2 → W → W
  /-- `resetFlags(enabled)`, ScaffoldWindowWorkers.scala:77 (flag workers only). -/
  resetFlags : Bool → W → W
  /-- `start(enabled)`, ScaffoldWindowWorkers.scala:86. -/
  start : Bool → W → W
  /-- `mark(enabled)`, ScaffoldWindowWorkers.scala:109. -/
  mark : Bool → W → W
  /-- `service()`: `quantum` program steps, ScaffoldWindowWorkers.scala:121. -/
  service : W → W
  /-- `output` (matcher: some `match` step fired in this tick's service),
  ScaffoldWindowWorkers.scala:61, 145. -/
  output : W → Bool
  /-- `mode.eqTo("done")`, ScaffoldWindowWorkers.scala:60, 163. -/
  modeDone : W → Bool
  /-- The worker's output `FlagStack`, abstractly, ScaffoldWindowWorkers.scala:63. -/
  flags : W → List Bool
  /-- Sticky: some `require` inside this worker has been violated. -/
  faulted : W → Bool

/-- `interval.map(n => math.min(n + 1, 6))`, ScaffoldWindowPal.scala:31. -/
def incInterval (n : Fin 7) : Fin 7 := ⟨min 6 (n.val + 1), by omega⟩

/-- `interval.map(n => math.max(0, math.min(3, n - 1)))`, ScaffoldWindowPal.scala:35
(`ℕ` subtraction truncates at `0`, which is the `max 0`). -/
def batchOfInterval (n : Fin 7) : Fin 4 := ⟨min 3 (n.val - 1), by omega⟩

/-- `small.map(n => math.min(4, n + 1))`, ScaffoldWindowPal.scala:104. -/
def incSmall (n : Fin 5) : Fin 5 := ⟨min 4 (n.val + 1), by omega⟩

/-- `FlagStack.pop(enabled)`, ScaffoldFlagPackets.scala:77-86:
returns `(bit, rest, violation)`. -/
def popFlag (enabled : Bool) (xs : List Bool) : Bool × List Bool × Bool :=
  match xs with
  | [] => (false, [], enabled)
  | b :: rest => (b, if enabled then rest else b :: rest, false)

/-- State of one `WindowStage`, ScaffoldWindowPal.scala:7-23. `birth`,
`release`, `middle` are per-tick temporaries (reset to `FALSE` at construction
and always rewritten in `advance` / `consume` before use). -/
structure StageState where
  half : ℕ
  clock : ℕ
  alive : Bool
  interval : Fin 7
  pending : Bool
  batch : Fin 4
  results : Fin 4 → List Bool
  birth : Bool
  release : Bool
  middle : Bool

/-- Initial (default) stage state, ScaffoldWindowPal.scala:13-23. -/
def StageState.initial : StageState where
  half := 0
  clock := 0
  alive := false
  interval := 0
  pending := false
  batch := 0
  results := fun _ => []
  birth := false
  release := false
  middle := false

/-- `answering()`: `alive ∧ interval ∈ {2,…,5}`, ScaffoldWindowPal.scala:26. -/
def answering (st : StageState) : Bool :=
  st.alive && (st.interval.val == 2 || st.interval.val == 3 ||
    st.interval.val == 4 || st.interval.val == 5)

/-- `advance(newBirth, sourceHalf)`, ScaffoldWindowPal.scala:27-44.
Returns the new stage and whether its `require(¬pending, newRelease)` failed. -/
def advance (st : StageState) (newBirth : Bool) (sourceHalf : ℕ) : StageState × Bool :=
  -- clock.drop(alive)
  let clock := if st.alive then st.clock.pred else st.clock
  let boundary := st.alive && clock == 0
  let interval := if boundary then incInterval st.interval else st.interval
  let clock := if boundary then st.half else clock
  let newRelease := boundary && (interval.val == 1 || interval.val == 2 ||
    interval.val == 3 || interval.val == 4)
  -- circuit.require(neg(pending), newRelease)
  let violation := newRelease && st.pending
  let batch := if newRelease then batchOfInterval interval else st.batch
  let alive := st.alive && !(boundary && interval.val == 6)
  let half := if newBirth then sourceHalf else st.half
  let clock := if newBirth then sourceHalf else clock
  let interval := if newBirth then (0 : Fin 7) else interval
  let alive := alive || newBirth
  let results := fun r => if newBirth then [] else st.results r
  ({ half := half, clock := clock, alive := alive, interval := interval,
     pending := st.pending && !newBirth, batch := batch, results := results,
     birth := newBirth, release := newRelease && !newBirth, middle := st.middle },
   violation)

/-- `consume()`, ScaffoldWindowPal.scala:46-58: when answering, pop the result
packet selected by `interval - 2`. Returns the stage and the pop's violation. -/
def consume (st : StageState) : StageState × Bool :=
  let active := answering st
  -- `selected` starts EMPTY and copies `results(r)` when `interval = r + 2`;
  -- when not active, `interval` may be outside 2..5 and `selected` stays empty.
  let sel? : Option (Fin 4) :=
    if h : 2 ≤ st.interval.val ∧ st.interval.val ≤ 5 then
      some ⟨st.interval.val - 2, by omega⟩
    else none
  let selected : List Bool := match sel? with
    | some r => st.results r
    | none => []
  let (bit, rest, violation) := popFlag active selected
  let results := fun r =>
    if active && sel? == some r then rest else st.results r
  ({ st with middle := active && bit, results := results }, violation)

/-- `capture()`, ScaffoldWindowPal.scala:60-67, given the stage worker's
`mode.eqTo("done")` and its output flag stack. -/
def capture (st : StageState) (workerDone : Bool) (workerFlags : List Bool) : StageState :=
  let pending := st.pending || st.release
  let done := pending && workerDone
  let results := fun r => if done && st.batch == r then workerFlags else st.results r
  { st with pending := pending && !done, results := results }

/-- State of `WindowPAL`, ScaffoldWindowPal.scala:80-99. The four workers are
`matchers(i)` and `flags(i)`; stage `i`'s `worker` is `flags(i)`
(ScaffoldWindowPal.scala:94). -/
structure PalState (Wm Wf : Type) where
  matchers : Fin 2 → Wm
  flags : Fin 2 → Wf
  history : ℕ
  power : ℕ
  nextBirth : ℕ
  stages : Fin 2 → StageState
  powerReady : Bool
  slot : Fin 2
  small : Fin 5
  first : Bool
  /-- Controller-level sticky `circuit.fault` (ScaffoldCircuit.scala:255). -/
  fault : Bool
  /-- `var output: Expr = TRUE`, ScaffoldWindowPal.scala:99. -/
  output : Bool

variable {Wm Wf : Type}

/-- Initial state: all declared defaults, ScaffoldWindowPal.scala:88-99. -/
def initial (m0 : Wm) (f0 : Wf) : PalState Wm Wf where
  matchers := fun _ => m0
  flags := fun _ => f0
  history := 0
  power := 0
  nextBirth := 0
  stages := fun _ => StageState.initial
  powerReady := false
  slot := 0
  small := 0
  first := false
  fault := false
  output := true

/-- One iteration of the per-stage loop in `tick`, ScaffoldWindowPal.scala:117-128:
arrive, arrive, resetFlags, start, start, mark, consume, service, service, capture. -/
def stageRound (mOps : WorkerOps Wm) (fOps : WorkerOps Wf) (a : Fin 2) (i : Fin 2)
    (s : PalState Wm Wf) : PalState Wm Wf :=
  let st := s.stages i
  let m := mOps.arrive a (s.matchers i)
  let f := fOps.arrive a (s.flags i)
  let f := fOps.resetFlags st.birth f
  let m := mOps.start st.birth m
  let f := fOps.start st.release f
  let f := fOps.mark st.release f
  let (st, violation) := consume st
  let m := mOps.service m
  let f := fOps.service f
  let st := capture st (fOps.modeDone f) (fOps.flags f)
  { s with
    matchers := Function.update s.matchers i m
    flags := Function.update s.flags i f
    stages := Function.update s.stages i st
    fault := s.fault || violation }

/-- `tick()`, ScaffoldWindowPal.scala:101-138, in Scala statement order.
Letter `0 ↦ 'a'`, `1 ↦ 'b'` (alphabet `"ab"`, ScaffoldWindowPal.scala:156). -/
def tick (mOps : WorkerOps Wm) (fOps : WorkerOps Wf) (s : PalState Wm Wf) (a : Fin 2) :
    PalState Wm Wf :=
  let current : Bool := a == 1
  let first := if s.small.val == 0 then current else s.first
  let small := incSmall s.small
  let history := s.history + 1
  let firstRound := !s.powerReady
  let nextBirth := if s.powerReady then s.nextBirth.pred else s.nextBirth
  let birth := s.powerReady && nextBirth == 0
  -- stage.advance(AND(birth, slot.eqTo(stageIndex)), power), stages 0 then 1
  let (st0, v0) := advance (s.stages 0) (birth && s.slot == 0) s.power
  let (st1, v1) := advance (s.stages 1) (birth && s.slot == 1) s.power
  let power := if firstRound || birth then history else s.power
  let nextBirth := if firstRound || birth then history else nextBirth
  let slot := if birth then s.slot + 1 else s.slot
  let s1 : PalState Wm Wf :=
    { s with
      first := first, small := small, history := history, power := power,
      nextBirth := nextBirth, powerReady := true, slot := slot,
      stages := fun i => if i = 0 then st0 else st1,
      fault := s.fault || v0 || v1 }
  let s2 := stageRound mOps fOps a 1 (stageRound mOps fOps a 0 s1)
  let active0 := answering (s2.stages 0)
  let active1 := answering (s2.stages 1)
  -- circuit.require(exactly one stage answering, small.eqTo(4))
  let violation := small.val == 4 && !((active0 || active1) && !(active0 && active1))
  let ordinary :=
    (active0 && (s2.stages 0).middle && mOps.output (s2.matchers 0)) ||
    (active1 && (s2.stages 1).middle && mOps.output (s2.matchers 1))
  let short := small.val == 1 ||
    ((small.val == 2 || small.val == 3) && (if current then first else !first))
  { s2 with
    fault := s2.fault || violation
    output := if small.val == 4 then ordinary else short }

/-- Run the controller over an input word from the initial state
(`commit()` is state carry-over, ScaffoldWindowPal.scala:140-151). -/
def run (mOps : WorkerOps Wm) (fOps : WorkerOps Wf) (m0 : Wm) (f0 : Wf)
    (w : List (Fin 2)) : PalState Wm Wf :=
  w.foldl (tick mOps fOps) (initial m0 f0)

/-- Global sticky fault: the controller's plus every worker's. -/
def globalFault (mOps : WorkerOps Wm) (fOps : WorkerOps Wf) (s : PalState Wm Wf) : Bool :=
  s.fault || mOps.faulted (s.matchers 0) || mOps.faulted (s.matchers 1) ||
    fOps.faulted (s.flags 0) || fOps.faulted (s.flags 1)

/-- Acceptance label `output ∧ ¬fault`, ScaffoldCircuit.scala:324-330; the empty
word is accepted since `initial.output = true` and nothing has faulted
(`initialAccepting = true`, ScaffoldWindowPal.scala:160). -/
def accepts (mOps : WorkerOps Wm) (fOps : WorkerOps Wf) (m0 : Wm) (f0 : Wf)
    (w : List (Fin 2)) : Bool :=
  let s := run mOps fOps m0 f0 w
  if w.isEmpty then true else s.output && !globalFault mOps fOps s

/-- `Accepts` as a proposition. -/
def Accepts (mOps : WorkerOps Wm) (fOps : WorkerOps Wf) (m0 : Wm) (f0 : Wf)
    (w : List (Fin 2)) : Prop :=
  accepts mOps fOps m0 f0 w = true

end PalPeg.ScaWindowPal
