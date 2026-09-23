import PalPeg.ScaHeap

/-!
# The window-pal input stream and flag packets at the pointer level

Definitions only (no proofs). This file transcribes, one scaffold node per input
character, the data structures that let the window-pal workers move their heads
by thousands of cells per character while every node reads only a bounded
neighbourhood of older nodes:

* `WindowStream` / `WindowHead` / `BlockState`
  (`scala/pal/src/main/scala/pal/ScaffoldWindowStream.scala`), built from the
  persistent stacks, unary counters and seven-stack real-time queue of
  `ScaffoldCircuitStructs.scala` (`Stack`, `Counter`, `Queue`);
* `FlagPackets` / `FlagStack` / `PacketWriter`
  (`scala/pal/src/main/scala/pal/ScaffoldFlagPackets.scala`).

Intended meaning: `docs/palindromes-in-peg/WINDOW_ROUNDS.md` ("Input heads",
"Flag output") and `SCA_INPUT_HEADS.md` (block zipper = focus, left stack,
right stack, incoming queue).

## Representation

The heap is a list of `StreamNode`s; the address of a node is its index. Node
`0` is the initial scaffold node (every `circuit.get(PREVIOUS, …)` default);
the node at address `i + 1` is created while reading `text[i]`. Old nodes are
never changed. A node carries

* finite fields: the input letter, the block phase, per head the `live` bit,
  the queue phase and the low `width` bits of the offset;
* pointer fields: the block-endpoint pointer `focus` and, per head, the roots
  of the left/right stacks, the seven queue stacks and the two queue counters
  (a root is a `ScaHeap.Ptr` = node address + cell slot tag, exactly Scala's
  `(Ref, tag)` pair), and the `O(log B)` predecessor jumps `stream.back<d>`;
* stack cells in finitely many slots (`StreamTag`), each with a `below` pointer
  (`ScaHeap.Cell.below`) and a `value` pointer to a block endpoint
  (`ScaHeap.Cell.data`). Scala's `data` payload of these pools is the constant
  `None` (`StackPool(…, payloadValues = Vector(None))`) and is dropped.

The abstract model (`PalPeg/ScaWindowWorker.lean`) has heads as natural-number
cursors into `text` and the flag output as a `List Bool`. The representation
invariants below (`HeadRep`, `RoundHeadRep`, `FlagStackRep`, …) state how the
pointer structures denote those values; nothing here proves them.

The in-round work of Scala is symbolic (circuit equations). Here it is run on
concrete booleans: a Scala guard `Expr` becomes a `Bool`, `Ref.select` becomes
`if`, and `circuit.require(c, enabled)` sets a `fault` bit.
-/

set_option autoImplicit false

namespace PalPeg.ScaWindowStream

open PalPeg.ScaHeap

/-! ## Construction constants of window-pal -/

/-- `GsBatchClock.DEFAULT_BATCH.k` (`GsBatchClock.scala:39`; `ScaGsTables.batchK`). -/
def batchK : ℕ := 8

/-- `GsBatchClock.DEFAULT_BATCH.matching`, the matcher service quantum
(`ScaffoldWindowPal.scala:88`; `ScaGsTables.matchingQuantum`). -/
def matchingQuantum : ℕ := 512

/-- `GsBatchClock.DEFAULT_BATCH.flags`, the flag-worker service quantum
(`ScaffoldWindowPal.scala:89`; `ScaGsTables.flagsQuantum`). -/
def flagsQuantum : ℕ := 1024

/-- `movement` of `WindowWorker` (`ScaffoldWindowWorkers.scala:36-41`): the largest
`|delta|` of a `Move` in the program. Both window-pal programs have `8`
(`ScaGsTables.matcherWorker.movement`, `flagsWorker.movement`). -/
def windowPalMovement : ℕ := 8

/-- The `radius` argument of the worker's `WindowStream`
(`ScaffoldWindowWorkers.scala:48-50`): `3 + quantum * movement`. -/
def workerStreamRadius (quantum movement : ℕ) : ℕ := 3 + quantum * movement

/-- `WindowStream.width = max(1, radius.bitLength)` (`ScaffoldWindowStream.scala:252`). -/
def streamWidth (radius : ℕ) : ℕ := if radius = 0 then 1 else Nat.log2 radius + 1

/-- `WindowStream.base = 2^width` (`ScaffoldWindowStream.scala:253`). This is the
block length `B`: the phase is a `width`-bit counter and a block completes when
the old phase is all ones (`ScaffoldWindowStream.scala:256-258`). -/
def blockLength (radius : ℕ) : ℕ := 2 ^ streamWidth radius

/-- The matcher streams' block length: radius `3 + 512·8 = 4099`, width 13. -/
def matcherBlockLength : ℕ := blockLength (workerStreamRadius matchingQuantum windowPalMovement)

/-- The flag workers' block length: radius `3 + 1024·8 = 8195`, width 14. -/
def flagsBlockLength : ℕ := blockLength (workerStreamRadius flagsQuantum windowPalMovement)

#guard streamWidth (workerStreamRadius matchingQuantum windowPalMovement) = 13
#guard matcherBlockLength = 8192
#guard streamWidth (workerStreamRadius flagsQuantum windowPalMovement) = 14
#guard flagsBlockLength = 16384

/-- `FlagPackets(circuit, quantum, …)` capacity of a flag worker
(`ScaffoldWindowWorkers.scala:62`): one slot per service step. -/
def flagPacketCapacity : ℕ := flagsQuantum

/-- Stream heads of a matcher worker: `begin`, `end` and 6 reader registers
(`ScaffoldWindowWorkers.scala:35,48-49`; `matcherWorker.readers.registers = 6`). -/
def matcherHeadCount : ℕ := 2 + 6

/-- Stream heads of a flag worker: `begin`, `end` and 7 reader registers
(`flagsWorker.readers.registers = 7`). -/
def flagsHeadCount : ℕ := 2 + 7

/-! ## Cell slots -/

/-- A node address. -/
abbrev Addr := ℕ

/-- The allocation names of the stream's pools (`ScaffoldWindowStream.scala:260-270`),
per head `h`: `h.left`, `h.right` (pool `cells`), `h.incoming.B`, `.B2` (rear pool),
`.Br` (front pool), `.Fr` (reverse pool), and the counter sides `m.pos`, `m.neg`,
`c.pos`, `c.neg`. The queue stacks `F`, `WF`, `WB` only alias other roots and
never allocate. -/
inductive Role where
  | left | right | qB | qB2 | qBr | qFr | mPos | mNeg | cPos | cNeg
  deriving DecidableEq, Repr

/-- The finite layout (`ScaffoldWindowStream.scala:260,264-270`). -/
def Role.capacity : Role → ℕ
  | .left => 1 | .right => 1 | .qB => 1 | .qB2 => 1 | .qBr => 12 | .qFr => 6
  | .mPos => 6 | .mNeg => 8 | .cPos => 12 | .cNeg => 2

/-- Scala's `CellTag = (allocationName, slot)` (`ScaffoldCircuitStructs.scala:21`). -/
structure StreamTag (H : Type) where
  head : H
  role : Role
  slot : ℕ
  deriving DecidableEq

/-- The slot lies in the finite layout (Scala throws at construction otherwise,
`ScaffoldCircuitStructs.scala:72`). -/
def StreamTag.InLayout {H : Type} (t : StreamTag H) : Prop := t.slot < t.role.capacity

/-- The `value` field of a stack cell: a block endpoint (`Ref`), `none` = `EMPTY`. -/
abbrev CellData := Option Addr

/-- A stack root: Scala's `(top : Ref, tag)` (`ScaffoldCircuitStructs.scala:93-94`). -/
abbrev Root (H : Type) := Option (Ptr (StreamTag H))

/-! ## Per-node record -/

/-- The two counters of a queue (`Queue.m`, `Queue.c`, `ScaffoldCircuitStructs.scala:305-306`). -/
inductive CounterKind where
  | m | c
  deriving DecidableEq, Repr

def CounterKind.posRole : CounterKind → Role
  | .m => .mPos | .c => .cPos

def CounterKind.negRole : CounterKind → Role
  | .m => .mNeg | .c => .cNeg

/-- `Counter` roots: `positiveStack`, `negativeStack` (`ScaffoldCircuitStructs.scala:230-275`). -/
structure CounterRoots (H : Type) where
  pos : Root H := none
  neg : Root H := none

/-- `Queue.phase` (`ScaffoldCircuitStructs.scala:308`). -/
inductive QPhase where
  | idle | rev | copy
  deriving DecidableEq, Repr

/-- `Queue` roots (`ScaffoldCircuitStructs.scala:292-405`): seven stacks, two
counters, phase. -/
structure QueueRoots (H : Type) where
  F : Root H := none
  B : Root H := none
  Fr : Root H := none
  Br : Root H := none
  WF : Root H := none
  WB : Root H := none
  B2 : Root H := none
  m : CounterRoots H := {}
  c : CounterRoots H := {}
  phase : QPhase := .idle

/-- `BlockState` (`ScaffoldWindowStream.scala:66-122`): the block zipper of a head.
`focus` is the endpoint node of the current block (`name.block_end`), `live`
says the current block is the unfinished last one (`name.live`, default `true`). -/
structure BlockFields (H : Type) where
  focus : Option Addr := none
  live : Bool := true
  left : Root H := none
  right : Root H := none
  queue : QueueRoots H := {}

/-- The stored fields of one `WindowHead`: its zipper and `name.offset`, the low
`width` bits of the offset (`ScaffoldWindowStream.scala:128,238`). -/
structure HeadFields (H : Type) where
  block : BlockFields H := {}
  offset : ℕ := 0

/-- **One scaffold node of a `WindowStream`.** `input` is `stream.input`
(`ScaffoldWindowStream.scala:259`; `none` on the initial node, where Scala stores
the default `alphabet.head`), `phase` is `stream.phase`, `jumps` the materialized
`stream.back<d>` pointer fields (`jumpSet`), `heads` the per-head fields and
`cells` the stack cells allocated by this node. -/
structure StreamNode (H A : Type) where
  input : Option A
  phase : ℕ
  jumps : List (ℕ × Option Addr)
  heads : H → HeadFields H
  cells : Node (StreamTag H) CellData

/-- The initial scaffold node (all `PREVIOUS` defaults). -/
def initialNode {H A : Type} : StreamNode H A :=
  { input := none, phase := 0, jumps := [], heads := fun _ => {}, cells := fun _ => none }

/-- The stack-cell heap of `ScaHeap`. -/
def cellHeap {H A : Type} (heap : List (StreamNode H A)) : Heap (StreamTag H) CellData :=
  heap.map (·.cells)

/-- The static parameters of a `WindowStream` (`ScaffoldWindowStream.scala:248`). -/
structure StreamParams (H : Type) where
  names : List H
  radius : ℕ

def StreamParams.width {H : Type} (P : StreamParams H) : ℕ := streamWidth P.radius

def StreamParams.blockLength {H : Type} (P : StreamParams H) : ℕ := PalPeg.ScaWindowStream.blockLength P.radius

/-! ## Predecessor jumps (`ScaffoldWindowStream.scala:286-305`) -/

/-- `jump(d)`'s path from the previous node (`ScaffoldWindowStream.scala:292-297`):
`back1` is the previous node; `back(2h+1) = back h ∘ back h` and
`back(2h) = back(h-1) ∘ back h` from the previous node. -/
def jumpPath (d : ℕ) : List ℕ :=
  if d ≤ 1 then []
  else if d % 2 = 1 then [d / 2, d / 2]
  else if d / 2 > 1 then [d / 2, d / 2 - 1] else [d / 2]

/-- Worklist closure of `jumpPath`; `fuel` only makes the recursion structural. -/
def jumpClosure : ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, acc => acc
  | _ + 1, [], acc => acc
  | f + 1, d :: todo, acc =>
    if d = 0 ∨ d ∈ acc then jumpClosure f todo acc
    else jumpClosure f (jumpPath d ++ todo) (acc ++ [d])

/-- The jump distances `read` registers: hops by `2^i` (`i < width`) use `jump(2^i)`
from an old node and `jump(2^i - 1)` from the new one
(`ScaffoldWindowStream.scala:221-224,302-305`), closed under `jumpPath`. -/
def jumpSet (width : ℕ) : List ℕ :=
  jumpClosure (64 * (width + 1) * (width + 1))
    ((List.range width).flatMap fun i => [2 ^ i, 2 ^ i - 1]) []

def lookupJump (jumps : List (ℕ × Option Addr)) (d : ℕ) : Option Addr :=
  ((jumps.find? (·.1 == d)).map (·.2)).join

/-- `edge(target, jump(d))`: the `back<d>` field of the old node `target`. -/
def followJump {H A : Type} (heap : List (StreamNode H A)) (target : Option Addr) (d : ℕ) :
    Option Addr :=
  target.bind fun a => (heap[a]?).bind fun n => lookupJump n.jumps d

/-- The previous node of the node being created. -/
def prevAddr {H A : Type} (heap : List (StreamNode H A)) : Option Addr :=
  if heap.length = 0 then none else some (heap.length - 1)

/-- The new node's `back<d>` field: follow `jumpPath d` from the previous node. -/
def newJump {H A : Type} (heap : List (StreamNode H A)) (d : ℕ) : Option Addr :=
  (jumpPath d).foldl (followJump heap) (prevAddr heap)

def newJumps {H A : Type} (heap : List (StreamNode H A)) (width : ℕ) : List (ℕ × Option Addr) :=
  (jumpSet width).map fun d => (d, newJump heap d)

/-- A `Ref` during a transition: the node being created, or an old node. -/
inductive Endpoint where
  | new
  | old (a : Option Addr)

/-- `hop(target, d)` (`ScaffoldWindowStream.scala:302-305`). -/
def hop {H A : Type} (heap : List (StreamNode H A)) (jumps' : List (ℕ × Option Addr)) :
    Endpoint → ℕ → Endpoint
  | .new, d => .old (if d = 1 then prevAddr heap else lookupJump jumps' (d - 1))
  | .old a, d => .old (followJump heap a d)

/-! ## The per-transition builder (Scala's `Circuit` of one tick) -/

/-- The state of one transition: the old heap (read only), the cells of the node
being created (`currentRefs`/`currentValues` of the pools), the next static slot
per allocation name (`StackPool.used`), and the accumulated `require` faults. -/
structure Build (H A : Type) where
  heap : List (StreamNode H A)
  cells : Node (StreamTag H) CellData
  used : H → Role → ℕ
  fault : Bool

abbrev BuildM (H A : Type) := StateM (Build H A)

section Build

variable {H A : Type} [DecidableEq H]

/-- Read a cell of an old node, or of the node being created (`SELF`). -/
def Build.cellAt (b : Build H A) (p : Ptr (StreamTag H)) : Option (Cell (StreamTag H) CellData) :=
  if p.1 = b.heap.length then b.cells p.2 else ScaHeap.cellAt (cellHeap b.heap) p

/-- The cell heap including the node being created. -/
def Build.cellsWithNew (b : Build H A) : Heap (StreamTag H) CellData :=
  cellHeap b.heap ++ [b.cells]

/-- `circuit.require(cond, enabled)`. -/
def require (cond enabled : Bool) : BuildM H A Unit :=
  modify fun b => { b with fault := b.fault || (enabled && !cond) }

/-- `Stack.peek` (`ScaffoldCircuitStructs.scala:98-100`) with the `below` pointer
`drop` reads: `(value, below)`; `EMPTY` reads `EMPTY`. -/
def stackPeek (root : Root H) : BuildM H A (CellData × Root H) := do
  let b ← get
  match root with
  | none => return (none, none)
  | some p =>
    match b.cellAt p with
    | none => return (none, none)
    | some c => return (c.data, c.below)

/-- `Stack.pop(enabled)` (`ScaffoldCircuitStructs.scala:102-113`). -/
def stackPop (root : Root H) (enabled : Bool) : BuildM H A (CellData × Root H) := do
  let (v, below) ← stackPeek root
  return (v, if enabled then below else root)

/-- `Stack.push(value, enabled)` via `StackPool.allocate`
(`ScaffoldCircuitStructs.scala:70-84,115-122`): write the next static slot of the
allocation name `(h, role)` in the new node, with `below` = old root.
Scala skips the allocation only when `enabled` is the constant `FALSE`; here a
slot is consumed on every call (the symbolic worst case Scala sizes for). -/
def stackPush (h : H) (role : Role) (root : Root H) (value : CellData) (enabled : Bool) :
    BuildM H A (Root H) := do
  let b ← get
  let tag : StreamTag H := ⟨h, role, b.used h role⟩
  set { b with
    cells := if enabled then Function.update b.cells tag (some ⟨root, value⟩) else b.cells
    used := Function.update b.used h (Function.update (b.used h) role (b.used h role + 1)) }
  return if enabled then some (b.heap.length, tag) else root

/-! ### Counters (`ScaffoldCircuitStructs.scala:230-275`) -/

namespace CounterRoots

def zero (c : CounterRoots H) : Bool := c.pos.isNone && c.neg.isNone
def positive (c : CounterRoots H) : Bool := c.pos.isSome
def negative (c : CounterRoots H) : Bool := c.neg.isSome

/-- `Counter.inc`. -/
def inc (h : H) (k : CounterKind) (c : CounterRoots H) (enabled : Bool) :
    BuildM H A (CounterRoots H) := do
  let empty := c.neg.isNone
  let (_, neg) ← stackPop c.neg (enabled && !empty)
  let pos ← stackPush h k.posRole c.pos none (enabled && empty)
  return { pos, neg }

/-- `Counter.dec`. -/
def dec (h : H) (k : CounterKind) (c : CounterRoots H) (enabled : Bool) :
    BuildM H A (CounterRoots H) := do
  let empty := c.pos.isNone
  let (_, pos) ← stackPop c.pos (enabled && !empty)
  let neg ← stackPush h k.negRole c.neg none (enabled && empty)
  return { pos, neg }

end CounterRoots

/-! ### The real-time queue (`ScaffoldCircuitStructs.scala:292-405`) -/

namespace QueueRoots

/-- `Queue.empty()`. -/
def isEmpty (q : QueueRoots H) : Bool :=
  q.F.isNone && q.B.isNone && decide (q.phase = .idle)

/-- `Queue.push`. -/
def push (h : H) (q : QueueRoots H) (value : CellData) (enabled : Bool) :
    BuildM H A (QueueRoots H) := do
  let idle := decide (q.phase = .idle)
  let B ← stackPush h .qB q.B value (enabled && idle)
  let B2 ← stackPush h .qB2 q.B2 value (enabled && !idle)
  let c ← q.c.dec h .c enabled
  return { q with B, B2, c }

/-- `Queue.maybeFinish`. -/
def maybeFinish (q : QueueRoots H) (enabled : Bool) : QueueRoots H :=
  if enabled && decide (q.phase = .copy) && q.m.zero then
    { q with F := q.Br, B := q.B2, Br := none, B2 := none, Fr := none, phase := .idle }
  else q

/-- `Queue.start`. -/
def start (q : QueueRoots H) (enabled : Bool) : QueueRoots H :=
  if enabled then
    { q with WF := q.F, WB := q.B, Fr := none, Br := none, B2 := none, m := {}, phase := .rev }
  else q

/-- `Queue.pop`. -/
def pop (h : H) (q : QueueRoots H) (enabled : Bool) : BuildM H A (CellData × QueueRoots H) := do
  require q.F.isSome enabled
  let (v, F) ← stackPop q.F enabled
  let c ← q.c.dec h .c enabled
  let rotating := enabled && !decide (q.phase = .idle)
  let m ← q.m.dec h .m rotating
  return (v, maybeFinish { q with F, c, m } rotating)

/-- `Queue.unit`: one rotation instruction. `copy` is read before the reversal may
switch the phase, as in Scala. -/
def unit (h : H) (q : QueueRoots H) (enabled : Bool) : BuildM H A (QueueRoots H) := do
  let reverse := enabled && decide (q.phase = .rev)
  let copy := enabled && decide (q.phase = .copy)
  let rear := reverse && q.WB.isSome
  let front := reverse && q.WF.isSome
  let (rearValue, WB) ← stackPop q.WB rear
  let Br ← stackPush h .qBr q.Br rearValue rear
  let c ← q.c.inc h .c rear
  let c ← c.inc h .c rear
  let (frontValue, WF) ← stackPop q.WF front
  let Fr ← stackPush h .qFr q.Fr frontValue front
  let m ← q.m.inc h .m front
  let q := { q with WB, Br, c, WF, Fr, m }
  let finishedReversal := reverse && !(rear || front)
  let q := if finishedReversal then { q with phase := .copy } else q
  let q := maybeFinish q finishedReversal
  let copying := copy && q.m.positive && q.Fr.isSome
  let (copyValue, Fr) ← stackPop q.Fr copying
  let Br ← stackPush h .qBr q.Br copyValue copying
  let m ← q.m.dec h .m copying
  return maybeFinish { q with Fr, Br, m } copy

/-- `Queue.workUnit`. -/
def workUnit (h : H) (q : QueueRoots H) (enabled : Bool) : BuildM H A (QueueRoots H) :=
  let q := start q (enabled && decide (q.phase = .idle) && q.c.negative)
  unit h q (enabled && !decide (q.phase = .idle))

/-- `Queue.work`: three rotation units. -/
def work (h : H) (q : QueueRoots H) (enabled : Bool) : BuildM H A (QueueRoots H) := do
  let q ← workUnit h q enabled
  let q ← workUnit h q enabled
  workUnit h q enabled

end QueueRoots

/-! ### Block zippers (`BlockState`, `ScaffoldWindowStream.scala:66-122`) -/

namespace BlockFields

/-- `completeBlock(completed)` (`ScaffoldWindowStream.scala:84-89`): a finished
block's endpoint is the node being created; a live head moves its focus onto it,
any other head enqueues it. -/
def completeBlock (h : H) (s : BlockFields H) (completed : Bool) : BuildM H A (BlockFields H) := do
  let newAddr := (← get).heap.length
  let queue ← s.queue.push h (some newAddr) (completed && !s.live)
  let queue ← queue.work h completed
  return { s with queue,
                  focus := if completed && s.live then some newAddr else s.focus,
                  live := s.live && !completed }

/-- `moveLeft(enabled)` (`ScaffoldWindowStream.scala:90-96`): a live block is not
pushed on the right stack. -/
def moveLeft (h : H) (s : BlockFields H) (enabled : Bool) : BuildM H A (BlockFields H) := do
  let right ← stackPush h .right s.right s.focus (enabled && !s.live)
  let (prior, left) ← stackPop s.left enabled
  return { s with right, left,
                  focus := if enabled then prior else s.focus,
                  live := s.live && !enabled }

/-- `moveRight(enabled)` (`ScaffoldWindowStream.scala:97-107`): next block from the
right stack, else from the incoming queue, else the live block. -/
def moveRight (h : H) (s : BlockFields H) (enabled : Bool) : BuildM H A (BlockFields H) := do
  let left ← stackPush h .left s.left s.focus enabled
  let stacked := s.right.isSome
  let queued := !s.queue.isEmpty
  let fromQueue := enabled && !stacked && queued
  let (a, right) ← stackPop s.right (enabled && stacked)
  let (bv, queue) ← s.queue.pop h fromQueue
  let queue ← queue.work h fromQueue
  return { left, right, queue,
           focus := if enabled then (if stacked then a else bv) else s.focus,
           live := if enabled then !stacked && !queued else s.live }

/-- `copyFrom(other, enabled)` (`ScaffoldWindowStream.scala:108-114`). -/
def copyFrom (s other : BlockFields H) (enabled : Bool) : BlockFields H :=
  if enabled then other else s

end BlockFields

/-- The prepared neighbourhood of one old head (`WindowStream.neighbors`,
`ScaffoldWindowStream.scala:274-284`): the current block after completion, and
its left/right neighbours with their validity. -/
structure Prepared (H : Type) where
  center : BlockFields H
  before : BlockFields H
  after : BlockFields H
  canLeft : Bool
  canRight : Bool

def prepareHead (h : H) (s : BlockFields H) (completed : Bool) : BuildM H A (Prepared H) := do
  let center ← s.completeBlock h completed
  let canLeft := center.left.isSome
  let canRight := !center.live
  let before ← center.moveLeft h canLeft
  let after ← center.moveRight h canRight
  return { center, before, after, canLeft, canRight }

/-- **Round preparation**: every head, in `names` order. All cells of the new
node are allocated here; the round itself allocates nothing. -/
def prepareAll (names : List H) (heads : H → HeadFields H) (completed : Bool) :
    BuildM H A (H → Option (Prepared H)) :=
  names.foldlM (fun acc h => do
    let p ← prepareHead h (heads h).block completed
    return Function.update acc h (some p)) (fun _ => none)

end Build

/-! ## The round: heads as origin selector + extended offset -/

/-- A `WindowHead` during a round (`ScaffoldWindowStream.scala:124-125`): the old
head whose prepared neighbourhood it uses, and the offset. Scala keeps `offset`
in `width + 2` two's-complement bits (low bits, `high`, `sign`); the construction
check `radius + |amount| < base` keeps it in `[-B, 2B)`, so an integer is used. -/
structure RoundHead (H : Type) where
  origin : H
  offset : ℤ

/-- The requested head operations of a round. `moveSelected` with the runtime
choice `δ` is `move δ` (`ScaffoldWindowStream.scala:199-211`); reads are
observations (`roundRead`) and are not listed. -/
inductive HeadOp (H : Type) where
  | move (head : H) (amount : ℤ) (enabled : Bool)
  | copyFrom (target source : H) (enabled : Bool)

section Round

variable {H A : Type} [DecidableEq H]

/-- `variants`' direction guards (`ScaffoldWindowStream.scala:131-134`): `-1` on
`[-B, 0)`, `0` on `[0, B)`, `1` on `[B, 2B)`; no variant otherwise. -/
def direction (blockLen : ℕ) (offset : ℤ) : Option ℤ :=
  if -(blockLen : ℤ) ≤ offset ∧ offset < 0 then some (-1)
  else if 0 ≤ offset ∧ offset < blockLen then some 0
  else if (blockLen : ℤ) ≤ offset ∧ offset < 2 * blockLen then some 1
  else none

/-- The low `width` bits of the offset. -/
def lowOffset (blockLen : ℕ) (offset : ℤ) : ℕ := (offset % (blockLen : ℤ)).toNat

def Prepared.neighbor (p : Prepared H) (d : ℤ) : Option (BlockFields H × Bool) :=
  if d = -1 then some (p.before, p.canLeft)
  else if d = 0 then some (p.center, true)
  else if d = 1 then some (p.after, p.canRight)
  else none

/-- The selected prepared zipper and its validity. -/
def variant (blockLen : ℕ) (prep : H → Option (Prepared H)) (rh : RoundHead H) :
    Option (BlockFields H × Bool) :=
  match prep rh.origin, direction blockLen rh.offset with
  | some p, some d => p.neighbor d
  | _, _ => none

/-- `locationFlags` (`ScaffoldWindowStream.scala:159-167`): `(live, valid)`. -/
def locationFlags (blockLen : ℕ) (prep : H → Option (Prepared H)) (rh : RoundHead H) :
    Bool × Bool :=
  match variant blockLen prep rh with
  | some (s, v) => (s.live, v)
  | none => (false, false)

/-- `available()` (`ScaffoldWindowStream.scala:168-172`); `phase` is the new phase. -/
def available (blockLen phase : ℕ) (prep : H → Option (Prepared H)) (rh : RoundHead H) : Bool :=
  let (live, valid) := locationFlags blockLen prep rh
  valid && (!live || decide (lowOffset blockLen rh.offset < phase))

/-- `canMove(amount)` (`ScaffoldWindowStream.scala:173-178`). -/
def canMove (blockLen phase : ℕ) (prep : H → Option (Prepared H)) (rh : RoundHead H)
    (amount : ℤ) : Bool :=
  let cand : RoundHead H := { rh with offset := rh.offset + amount }
  let (live, valid) := locationFlags blockLen prep cand
  valid && (!live || decide (lowOffset blockLen cand.offset ≤ phase))

/-- Round state: every head's selector/offset and the `require` faults. -/
structure Round (H : Type) where
  heads : H → RoundHead H
  fault : Bool

/-- The heads at the start of a round: own origin, stored low offset
(`WindowHead` auxiliary constructor, `ScaffoldWindowStream.scala:126-129`). -/
def initialRound (heads : H → HeadFields H) : Round H :=
  { heads := fun h => { origin := h, offset := (heads h).offset }, fault := false }

/-- `move` / `moveSelected` / `copyFrom` (`ScaffoldWindowStream.scala:179-211`):
only finite fields change. -/
def applyOp (blockLen phase : ℕ) (prep : H → Option (Prepared H)) (st : Round H) :
    HeadOp H → Round H
  | .move h amount enabled =>
    if enabled && amount != 0 then
      let rh := st.heads h
      { heads := Function.update st.heads h { rh with offset := rh.offset + amount },
        fault := st.fault || !canMove blockLen phase prep rh amount }
    else st
  | .copyFrom target source enabled =>
    if enabled then { st with heads := Function.update st.heads target (st.heads source) } else st

def runOps (blockLen phase : ℕ) (prep : H → Option (Prepared H)) (st : Round H)
    (ops : List (HeadOp H)) : Round H :=
  ops.foldl (applyOp blockLen phase prep) st

/-- `read()` (`ScaffoldWindowStream.scala:212-227`) of a round head: from the live
end (the new node) back `phase - low - 1`, or from the block endpoint back
`B - 1 - low`, one `hop` by `2^i` per set distance bit. `none` when unavailable. -/
def roundRead (heap : List (StreamNode H A)) (width blockLen phase : ℕ)
    (jumps' : List (ℕ × Option Addr)) (letter : A) (prep : H → Option (Prepared H))
    (rh : RoundHead H) : Option A :=
  if !available blockLen phase prep rh then none else
  match variant blockLen prep rh with
  | none => none
  | some (s, _) =>
    let low := lowOffset blockLen rh.offset
    let distance := if s.live then phase - low - 1 else blockLen - 1 - low
    let start : Endpoint := if s.live then .new else .old s.focus
    let final := (List.range width).foldl
      (fun e bit => if distance.testBit bit then hop heap jumps' e (2 ^ bit) else e) start
    match final with
    | .new => some letter
    | .old a => a.bind fun a => (heap[a]?).bind (·.input)

/-- `WindowHead.commit` (`ScaffoldWindowStream.scala:232-240`): store the selected
zipper into the head's own state (its `center`) and the low offset. The boolean
is the `require(valid, guard)`; no variant selected means no copy and no
requirement, as in Scala. -/
def commitHead (blockLen : ℕ) (prep : H → Option (Prepared H)) (prev : HeadFields H)
    (h : H) (rh : RoundHead H) : HeadFields H × Bool :=
  let center := match prep h with
    | some p => p.center
    | none => prev.block
  match variant blockLen prep rh with
  | some (s, valid) => ({ block := s, offset := lowOffset blockLen rh.offset }, valid)
  | none => ({ block := center, offset := lowOffset blockLen rh.offset }, true)

/-- The last node of the heap (the previous node of the one being created). -/
def lastNode (heap : List (StreamNode H A)) : StreamNode H A := heap.getLast?.getD initialNode

/-- **The per-character update** of a `WindowStream`: from the old heap, the current
input letter and the round's head operations to the new node, plus the fault bit.
Order as in Scala: the phase advances (`ScaffoldWindowStream.scala:256-259`), every
old head's neighbourhood is prepared (all cell allocation), the operations change
only selectors and offsets, and `commit` stores roots, offsets and the phase
(`ScaffoldWindowStream.scala:313-316`). -/
def stepNode (P : StreamParams H) (heap : List (StreamNode H A)) (letter : A)
    (ops : List (HeadOp H)) : StreamNode H A × Bool :=
  let prev := lastNode heap
  let blockLen := P.blockLength
  let completed := decide (prev.phase = blockLen - 1)
  let phase := (prev.phase + 1) % blockLen
  let b0 : Build H A := { heap, cells := fun _ => none, used := fun _ _ => 0, fault := false }
  let r := Id.run ((prepareAll P.names prev.heads completed).run b0)
  let prep := r.1
  let b := r.2
  let round := runOps blockLen phase prep (initialRound prev.heads) ops
  let committed := fun h => commitHead blockLen prep (prev.heads h) h (round.heads h)
  let heads' := fun h => if h ∈ P.names then (committed h).1 else prev.heads h
  let fault := b.fault || round.fault || P.names.any (fun h => !(committed h).2)
  ({ input := some letter, phase, jumps := newJumps heap P.width, heads := heads',
     cells := b.cells }, fault)

end Round

/-! ## Flag packets (`ScaffoldFlagPackets.scala`) -/

/-- One packet slot (`prefix.<slot>.bit`, `prefix.<slot>.previous_index`,
`ScaffoldFlagPackets.scala:34-36`); `previousIndex = none` is Scala's `-1`. -/
structure FlagSlot where
  bit : Bool := false
  previousIndex : Option ℕ := none

/-- **The flag packet of one node** (`FlagPackets`, `ScaffoldFlagPackets.scala:12-53`):
`back`/`backIndex` (`prefix.previous`, `prefix.previous_index`) are the stack root
when the node's writer was created; `slots` are the `capacity` slots in push order. -/
structure FlagPacket where
  back : Option Addr := none
  backIndex : Option ℕ := none
  slots : List FlagSlot := []

/-- A `FlagStack` root (`name.root`, `name.index`, `ScaffoldFlagPackets.scala:55-60`):
a packet node and a slot in it; `index = none` is `-1`. -/
structure FlagRoot where
  root : Option Addr := none
  index : Option ℕ := none

/-- The per-node flag fields of a flag worker: its packet and the `output` stack
root (`ScaffoldWindowWorkers.scala:62-63`). -/
structure FlagNode where
  packet : FlagPacket
  output : FlagRoot

namespace FlagRoot

def empty (r : FlagRoot) : Bool := r.root.isNone

/-- `FlagStack.clear`. -/
def clear (r : FlagRoot) (enabled : Bool) : FlagRoot := if enabled then {} else r

/-- `FlagStack.copyFrom`. -/
def copyFrom (r other : FlagRoot) (enabled : Bool) : FlagRoot := if enabled then other else r

/-- `FlagPackets.read` (`ScaffoldFlagPackets.scala:38-52`). -/
def readSlot (pk : FlagPacket) (index : Option ℕ) : Bool × Option ℕ :=
  match index.bind fun s => pk.slots[s]? with
  | some sl => (sl.bit, sl.previousIndex)
  | none => (false, none)

/-- `FlagStack.pop` (`ScaffoldFlagPackets.scala:77-86`): `(bit, root', fault)`; a
slot without predecessor crosses to the previous packet. -/
def pop (packetAt : Addr → Option FlagPacket) (r : FlagRoot) (enabled : Bool) :
    Bool × FlagRoot × Bool :=
  let pk := (r.root.bind packetAt).getD {}
  let (bit, previous) := readSlot pk r.index
  let boundary := previous.isNone
  (bit,
   { root := if enabled && boundary then pk.back else r.root,
     index := if enabled then (if boundary then pk.backIndex else previous) else r.index },
   enabled && r.empty)

end FlagRoot

/-- `PacketWriter` (`ScaffoldFlagPackets.scala:95-122`): one per pool and node. -/
structure PacketWriter where
  packet : FlagPacket
  stack : FlagRoot
  started : Bool
  nextSlot : ℕ

/-- Writer creation records the current root as the packet's back link. -/
def PacketWriter.create (stack : FlagRoot) : PacketWriter :=
  { packet := { back := stack.root, backIndex := stack.index, slots := [] },
    stack, started := false, nextSlot := 0 }

/-- `PacketWriter.push(bit, enabled)`: the next static slot always stores `bit` and
the previous valid slot of this packet (`-1` before the first valid push); an
enabled push makes it the root. -/
def PacketWriter.push (newAddr : Addr) (w : PacketWriter) (bit enabled : Bool) : PacketWriter :=
  let previous := if w.started then w.stack.index else none
  { packet := { w.packet with slots := w.packet.slots ++ [{ bit, previousIndex := previous }] },
    stack := if enabled then { root := some newAddr, index := some w.nextSlot } else w.stack,
    started := w.started || enabled,
    nextSlot := w.nextSlot + 1 }

/-- Flag-stack operations before the writer is created (`clear`, `pop`). -/
inductive FlagOp where
  | clear (enabled : Bool)
  | pop (enabled : Bool)

/-- **The per-character flag update**: the pre-writer operations on the old root,
then the writer with the round's `(bit, enabled)` pushes in slot order (one per
service step, `ScaffoldWindowWorkers.scala:121-127`). Returns the new node's flag
fields, the popped bits, and the fault bit. -/
def flagStep (packetAt : Addr → Option FlagPacket) (newAddr : Addr) (old : FlagRoot)
    (ops : List FlagOp) (pushes : List (Bool × Bool)) : FlagNode × List Bool × Bool :=
  let (r, popped, fault) := ops.foldl (fun (acc : FlagRoot × List Bool × Bool) op =>
    let (r, popped, fault) := acc
    match op with
    | .clear en => (r.clear en, popped, fault)
    | .pop en =>
      let (bit, r', f) := r.pop packetAt en
      (r', if en then popped ++ [bit] else popped, fault || f)) (old, [], false)
  let w := pushes.foldl (fun w (bit, en) => w.push newAddr bit en) (PacketWriter.create r)
  ({ packet := w.packet, output := w.stack }, popped, fault)

/-! ## Representation invariants (statements only)

Positions: text position `p` lives in node `p + 1`. Block `i` (0-based) covers
positions `[i·B, (i+1)·B)`; its endpoint is node `(i+1)·B`, the node created
when the phase wraps to `0` (`completed`, `ScaffoldWindowStream.scala:257`). At
node `n`, `n / B` blocks are complete and the block `n / B` is live.
-/

section Invariants

variable {H A : Type}

/-- The endpoint node of block `i`. -/
def blockEnd (blockLen i : ℕ) : Addr := (i + 1) * blockLen

/-- Endpoints of blocks `lo, …, hi - 1`, ascending. -/
def blockEnds (blockLen lo hi : ℕ) : List Addr :=
  (List.range' lo (hi - lo)).map (blockEnd blockLen)

/-- The stream's letters: node `i + 1` carries `text[i]`. -/
def InputRep (heap : List (StreamNode H A)) (text : List A) : Prop :=
  heap.length = text.length + 1 ∧ heap.head? = some initialNode ∧
  ∀ i (hi : i < text.length), (heap[i + 1]?).bind (·.input) = some text[i]

/-- `stream.phase` counts nodes modulo `B`. -/
def PhaseRep (blockLen : ℕ) (heap : List (StreamNode H A)) : Prop :=
  ∀ a node, heap[a]? = some node → node.phase = a % blockLen

/-- Every materialized jump of node `n` points `d` nodes back (to `none` before
node `0`): `back<d>(n) = n - d`, the shared-equation contract of
`WINDOW_ROUNDS.md` ("Fixed predecessor jumps"). -/
def JumpRep (width : ℕ) (heap : List (StreamNode H A)) : Prop :=
  ∀ n node, heap[n]? = some node → ∀ d ∈ jumpSet width,
    lookupJump node.jumps d = if d ≤ n then some (n - d) else none

/-- A unary counter denotes an integer: one side holds `|z|` cells, the other is empty. -/
def CounterRep (heap : Heap (StreamTag H) CellData) (c : CounterRoots H) (z : ℤ) : Prop :=
  (∃ k : ℕ, Rep heap c.pos (List.replicate k none) ∧ c.neg = none ∧ z = k) ∨
  (∃ k : ℕ, c.pos = none ∧ Rep heap c.neg (List.replicate k none) ∧ z = -(k : ℤ))

/-- **The real-time queue denotes the list `xs`** (front first). Front `F` is
authoritative in every phase; the rear is `B` when idle, and during a rotation the
old rear is split between `WB` (still to reverse) and `Br` (reversed), while new
pushes go to `B2`. In the copy phase the top `|F| - m` cells of `Br` are copies
of `F`'s suffix. `isEmpty` is exact (the rotation schedule keeps `F` nonempty
while rotating). The scheduling potential `c` is not part of the denotation. -/
def QueueRep (heap : Heap (StreamTag H) CellData) (q : QueueRoots H) (xs : List Addr) : Prop :=
  (q.isEmpty = true ↔ xs = []) ∧
  match q.phase with
  | .idle => ∃ fs bs : List Addr,
      Rep heap q.F (fs.map some) ∧ Rep heap q.B (bs.map some) ∧ xs = fs ++ bs.reverse
  | .rev => ∃ fs wb br b2 : List Addr,
      Rep heap q.F (fs.map some) ∧ Rep heap q.WB (wb.map some) ∧ Rep heap q.Br (br.map some) ∧
      Rep heap q.B2 (b2.map some) ∧ xs = fs ++ wb.reverse ++ br ++ b2.reverse
  | .copy => ∃ (fs br b2 : List Addr) (k : ℕ),
      Rep heap q.F (fs.map some) ∧ Rep heap q.Br (br.map some) ∧ Rep heap q.B2 (b2.map some) ∧
      CounterRep heap q.m k ∧ k ≤ fs.length ∧
      xs = fs ++ br.drop (fs.length - k) ++ b2.reverse

/-- **A block zipper stands at block `j`** when `complete` blocks have finished:
the left stack holds the endpoints of blocks `j-1, …, 0` (top first); `live` iff
`j` is the unfinished block, and then the right stack and queue are empty; else
`focus` is block `j`'s endpoint and right stack ++ queue list the endpoints of the
complete blocks `j+1, …, complete-1`. The live block itself is never stored on the
right (`ScaffoldWindowStream.scala:91`); it is implicit after an empty right side. -/
def BlockRep (heap : Heap (StreamTag H) CellData) (blockLen complete : ℕ) (s : BlockFields H)
    (j : ℕ) : Prop :=
  j ≤ complete ∧ (s.live = true ↔ j = complete) ∧
  Rep heap s.left ((blockEnds blockLen 0 j).reverse.map some) ∧
  (s.live = true → s.right = none ∧ QueueRep heap s.queue []) ∧
  (s.live = false → s.focus = some (blockEnd blockLen j) ∧
    ∃ rs qs : List Addr, Rep heap s.right (rs.map some) ∧ QueueRep heap s.queue qs ∧
      rs ++ qs = blockEnds blockLen (j + 1) complete)

/-- **The stored head `h` of node `addr` denotes position `pos`**: its zipper stands
at block `j`, the stored offset is a low offset, and `pos = j·B + offset ≤ addr`
(`addr` = number of letters read). This is `WorkerState.begin` / `end` /
`data[i]` of `ScaWindowWorker.WorkerState` for the heads `prefix.begin`,
`prefix.end`, `prefix.data i`. -/
def HeadRep (blockLen : ℕ) (heap : List (StreamNode H A)) (addr : Addr) (h : H) (pos : ℕ) : Prop :=
  ∃ (node : StreamNode H A) (j : ℕ), heap[addr]? = some node ∧
    BlockRep (cellHeap heap) blockLen (addr / blockLen) (node.heads h).block j ∧
    (node.heads h).offset < blockLen ∧ pos = j * blockLen + (node.heads h).offset ∧ pos ≤ addr

/-- The whole stream after reading `text`, with head positions `pos`. -/
def StreamRep (P : StreamParams H) (heap : List (StreamNode H A)) (text : List A)
    (pos : H → ℕ) : Prop :=
  InputRep heap text ∧ PhaseRep P.blockLength heap ∧ JumpRep P.width heap ∧
  ∀ h ∈ P.names, HeadRep P.blockLength heap text.length h (pos h)

/-- The prepared neighbourhood of a head at block `j`, over the heap including the
new node (`Build.cellsWithNew`) and the new count `complete` of finished blocks:
`before` is block `j-1` exactly when `canLeft`, `after` is block `j+1` exactly when
`canRight`. -/
def PreparedRep (heap : Heap (StreamTag H) CellData) (blockLen complete : ℕ) (p : Prepared H)
    (j : ℕ) : Prop :=
  BlockRep heap blockLen complete p.center j ∧
  (p.canLeft = true ↔ 0 < j) ∧ (p.canLeft = true → BlockRep heap blockLen complete p.before (j - 1)) ∧
  (p.canRight = true ↔ j < complete) ∧
  (p.canRight = true → BlockRep heap blockLen complete p.after (j + 1))

/-- **A round head denotes position `pos`**: its origin's prepared centre stands at
block `j` and `pos = j·B + offset`. Under this and `-B ≤ offset < 2B`,
`available` is `pos < text.length`, `canMove δ` is `0 ≤ pos + δ ≤ text.length`
(`ScaWindowWorker.WorkerState.availableAt` / `canMoveTo`) and `roundRead` returns
`text[pos]`. -/
def RoundHeadRep (heap : Heap (StreamTag H) CellData) (blockLen complete : ℕ)
    (prep : H → Option (Prepared H)) (rh : RoundHead H) (pos : ℕ) : Prop :=
  ∃ (p : Prepared H) (j : ℕ), prep rh.origin = some p ∧ PreparedRep heap blockLen complete p j ∧
    (pos : ℤ) = (j * blockLen : ℕ) + rh.offset

/-- The offset stays inside the prepared window (Scala's construction check
`radius + |amount| < base`, `ScaffoldWindowStream.scala:181,201`). -/
def InWindow (blockLen : ℕ) (rh : RoundHead H) : Prop :=
  -(blockLen : ℤ) ≤ rh.offset ∧ rh.offset < 2 * blockLen

/-- The packet after the flag root: the next root from a slot. -/
def FlagSlot.next (a : Addr) (pk : FlagPacket) (sl : FlagSlot) : FlagRoot :=
  match sl.previousIndex with
  | some s => { root := some a, index := some s }
  | none => { root := pk.back, index := pk.backIndex }

/-- **A flag root denotes the bit list** (top first), the `flags` of
`ScaWindowWorker.WorkerState` (`flags := bit :: flags` on a push). -/
inductive FlagStackRep (packetAt : Addr → Option FlagPacket) : FlagRoot → List Bool → Prop
  | nil (index : Option ℕ) : FlagStackRep packetAt { root := none, index } []
  | cons {a : Addr} {s : ℕ} {pk : FlagPacket} {sl : FlagSlot} {rest : List Bool}
      (hpk : packetAt a = some pk) (hsl : pk.slots[s]? = some sl)
      (hrest : FlagStackRep packetAt (FlagSlot.next a pk sl) rest) :
      FlagStackRep packetAt { root := some a, index := some s } (sl.bit :: rest)

/-- Every packet has at most `capacity` slots (Scala's construction check,
`ScaffoldFlagPackets.scala:109-111`). -/
def PacketsInCapacity (capacity : ℕ) (packetAt : Addr → Option FlagPacket) : Prop :=
  ∀ a pk, packetAt a = some pk → pk.slots.length ≤ capacity

end Invariants

end PalPeg.ScaWindowStream
