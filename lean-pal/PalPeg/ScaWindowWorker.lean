import PalPeg.ScaGsProgram

/-!
# The window-pal head-program worker, abstract level (mirror of `WindowWorker`)

Definitions only (no proofs). This is the *meaning* of the circuit built by
`scala/pal/src/main/scala/pal/ScaffoldWindowWorkers.scala` (`class WindowWorker`),
not its bit encoding:

* Heads (`begin`, `end`, the reader data registers) are natural-number cursors
  into the input read so far, `text`. A forward head at `p` reads `text[p]`; a
  reversed head reads just left of its cursor, `text[p-1]`
  (`ScaffoldWindowWorkers.scala:115-119`). A cell is available when it has
  arrived, `p < text.length` (`ScaffoldWindowStream.scala:168-172`,
  `WindowHead.available`: the live block's low offset is below the phase).
  A head may move to any `0 ≤ p + δ ≤ text.length`
  (`WindowHead.canMove`, `ScaffoldWindowStream.scala:173-178`).
* Distance registers (`WindowLiveDistances`, `ScaffoldWindowLive.scala`) are
  unbounded integers. The windowed `WindowRegisters` encoding (quotient origin +
  orientation + low digits, `ScaffoldWindowRegisters.scala`) denotes exactly one
  integer; we keep that integer and Scala's register-transfer semantics
  (they are *not* replaced by head-position differences).
* Circuit `require`s are accumulated into `fault`.
* Construction-time checks (`require(radius + … < base)`, ROM/domain checks,
  `initializeValues` key-set check, packet capacity) are encoding artifacts of
  the finite window and are not modelled.

The ROM fields (`ScaffoldRom.controllerTable`, batched, augmented by
`WindowLiveDistances.augmentRows`) need the liveness sets `after(state)` of
`GsHeadLiveness`; `WorkerSpec` only carries the colors, so the backward
liveness fixpoints are transcribed here too (`liveDistances`, `liveReaders`).
-/

set_option autoImplicit false

namespace PalPeg.ScaWindowWorker

open PalPeg.ScaGsProgram

abbrev Pair := String × String

/-! ## Small list helpers -/

/-- Set-union on lists (keeps the left list's order, appends new elements). -/
def union {α : Type} [DecidableEq α] (xs ys : List α) : List α :=
  ys.foldl (fun acc y => if y ∈ acc then acc else acc ++ [y]) xs

/-- Set equality of two duplicate-free lists. -/
def setEq {α : Type} [DecidableEq α] (xs ys : List α) : Bool :=
  xs.all (· ∈ ys) && ys.all (· ∈ xs)

/-- `Iterable.toMap` lookup: the *last* binding wins, as in Scala's `toMap`. -/
def lookupLast {α β : Type} [DecidableEq α] (a : α) (xs : List (α × β)) : Option β :=
  (xs.reverse.find? (·.1 = a)).map (·.2)

/-- `List.lookup` with `DecidableEq` (first binding; colors are keys of a `VectorMap`). -/
def lookupFirst {α β : Type} [DecidableEq α] (a : α) (xs : List (α × β)) : Option β :=
  (xs.find? (·.1 = a)).map (·.2)

/-! ## Liveness (`GsHeadLiveness.scala`) -/

/-- `pair(left, right)` inside `GsHeadLiveness.analyze` (`GsHeadLiveness.scala:82-93`):
the canonical ordered pair by rank in `names`; `none` for a head against itself.
(Unknown heads throw in Scala; here they rank `names.length`.) -/
def pairOf (names : List String) (left right : String) : Option Pair :=
  if left = right then none
  else if names.idxOf left < names.idxOf right then some (left, right)
  else some (right, left)

/-- `Liveness.canonical` (`GsHeadLiveness.scala:16-24`): canonical pair and the
sign of `left - right` relative to it. -/
def canonical (names : List String) (left right : String) : Option Pair × Int :=
  if left = right then (none, 1)
  else if names.idxOf left < names.idxOf right then (some (left, right), 1)
  else (some (right, left), -1)

/-- `successorsUnion` (`GsHeadLiveness.scala:71-73`). -/
def successorsUnion {α : Type} [DecidableEq α] (before : Array (List α))
    (targets : List Nat) : List α :=
  targets.foldl (fun live t => union live (before.getD t [])) []

/-- One reverse Gauss–Seidel sweep of `fixpoint` (`GsHeadLiveness.scala:124-139`):
states visited from `size-1` down to `0`, updated in place; returns whether
anything changed. -/
def sweep {α : Type} [DecidableEq α] (code : List Row)
    (transfer : Row → List α → List α) (before : Array (List α)) :
    Array (List α) × Bool :=
  (List.range code.length).reverse.foldl
    (fun (acc : Array (List α) × Bool) state =>
      let (bs, changed) := acc
      match code[state]? with
      | none => acc
      | some row =>
        let live := transfer row (successorsUnion bs row.targets)
        if setEq live (bs.getD state []) then (bs, changed)
        else (bs.set! state live, true))
    (before, false)

/-- `fixpoint` (`GsHeadLiveness.scala:124-139`). Scala iterates `while (changed)`;
`fuel` only makes termination structural. The transfer functions are monotone and
the iteration starts from `∅`, so each changing sweep grows the table by at least
one element: `fuel := code.length * height + 1` (the lattice height) suffices. -/
def fixpoint {α : Type} [DecidableEq α] (code : List Row)
    (transfer : Row → List α → List α) (fuel : Nat) : Array (List α) :=
  let rec go : Nat → Array (List α) → Array (List α)
    | 0, bs => bs
    | n + 1, bs =>
      let (bs', changed) := sweep code transfer bs
      if changed then go n bs' else bs'
  go fuel (Array.replicate code.length [])

/-- `liveBefore` of `analyze` with `observePositions = false`,
`availabilityDistance = false` (the `WindowLiveDistances` call,
`ScaffoldWindowLive.scala:10`; `GsHeadLiveness.scala:95-112`). -/
def distanceTransfer (names : List String) (row : Row) (succ : List Pair) : List Pair :=
  let substituted : List Pair :=
    match row.event with
    | .copy target source =>
      succ.foldl (fun acc p =>
        match pairOf names (if p.1 = target then source else p.1)
                            (if p.2 = target then source else p.2) with
        | some q => union acc [q]
        | none => acc) []
    | _ => succ
  let addPair (l r : String) : List Pair :=
    match pairOf names l r with
    | some q => union substituted [q]
    | none => substituted
  match row.event with
  | .less l r => addPair l r
  | .equal l r => addPair l r
  | .assertEqual l r => addPair l r
  | _ => substituted

/-- `liveBefore` of `analyzeReaders` (`GsHeadLiveness.scala:145-155`). -/
def readerTransfer (row : Row) (succ : List String) : List String :=
  let substituted : List String :=
    match row.event with
    | .copy target source =>
      if target ∈ succ then union (succ.filter (· ≠ target)) [source] else succ
    | _ => succ
  match row.event with
  | .symbols l r => union substituted [l, r]
  | .available h => union substituted [h]
  | _ => substituted

/-- `Liveness.before` of the distance analysis. -/
def liveDistances (spec : WorkerSpec) : Array (List Pair) :=
  fixpoint spec.program.code (distanceTransfer spec.names)
    (spec.program.code.length * spec.names.length * spec.names.length + 1)

/-- `ReaderLiveness.before`. -/
def liveReaders (spec : WorkerSpec) : Array (List String) :=
  fixpoint spec.program.code readerTransfer
    (spec.program.code.length * spec.names.length + 1)

/-! ## Decoded ROM row (`ScaffoldRom.controllerTable` + `augmentRows`) -/

/-- Register-transfer columns of one distance key `r_i`
(`ScaffoldWindowLive.scala:21-25`): `r_i := ±(old source) + delta`.
`source = none` is Scala's `None` source (exact zero). -/
structure RegUpdate where
  source : Option Nat
  reverse : Bool
  delta : Int
  deriving DecidableEq, Repr

/-- The ROM fields a row exposes (`ScaffoldRom.scala:78-145`,
`ScaffoldWindowLive.scala:19-63`). Reader register names
`prefix.data i` are represented by their index `i`; distance keys
`prefix.distance.r i` by `i`. -/
structure Fields where
  /-- `op` (kept as the whole event; only its opcode is used). -/
  event : Event
  /-- `bit` (`Flag(bit)`). -/
  bit : Bool
  yes : Nat
  no : Nat
  /-- `data_left` / `data_right` / `data_target` / `data_source`. -/
  dataLeft : Option Nat
  dataRight : Option Nat
  dataTarget : Option Nat
  dataSource : Option Nat
  /-- `data_delta.<name>` for each reader register (index = register). -/
  dataDelta : List Int
  /-- `r_i.source` / `r_i.reverse` / `r_i.delta` for each distance key. -/
  regs : List RegUpdate
  /-- `distance.test` (`none` = Scala `None`: a head compared with itself). -/
  distanceTest : Option Nat
  /-- `distance.reverse`. -/
  distanceReverse : Bool
  deriving Repr

/-- Tests with two successors (`ScaffoldRom.scala:82`). -/
def isTest : Event → Bool
  | .equal _ _ | .less _ _ | .symbols _ _ | .available _ => true
  | _ => false

/-- Decode row `state` (`controllerTable(program, names, Some(readers),
readerNames, batched = true, augment = Some(distances.augmentRows))`,
`ScaffoldWindowWorkers.scala:46-47`). -/
def fieldsAt (spec : WorkerSpec) (readerBefore : Array (List String))
    (distanceBefore : Array (List Pair)) (state : Nat) (row : Row) : Fields :=
  let next := row.targets.headD state
  let yes := if isTest row.event then row.targets.getD 1 next else next
  let bit := match row.event with | .flag b => b | _ => false
  -- readers (`ScaffoldRom.scala:108-125`)
  let readerAfter := successorsUnion readerBefore row.targets
  let color (h : String) : Option Nat := lookupFirst h spec.readers.colors
  let (dl, dr, dt, ds) : Option Nat × Option Nat × Option Nat × Option Nat :=
    match row.event with
    | .symbols l r => (color l, color r, none, none)
    | .available h => (color h, none, none, none)
    | .copy target source =>
      if target ∈ readerAfter then (none, none, color target, color source)
      else (none, none, none, none)
    | _ => (none, none, none, none)
  let dataDelta : List Int :=
    (List.range spec.readers.registers).map fun i =>
      match row.event with
      | .move moves =>
        (moves.filter (fun m => m.head ∈ readerAfter ∧ color m.head = some i)).foldl
          (fun acc m => acc + m.delta) 0
      | _ => 0
  -- distances (`ScaffoldWindowLive.scala:19-63`)
  let distanceAfter := successorsUnion distanceBefore row.targets
  let dcolor (p : Pair) : Option Nat := lookupFirst p spec.distances.colors
  let regs : List RegUpdate :=
    (List.range spec.distances.registers).map fun i =>
      let default : RegUpdate := { source := some i, reverse := false, delta := 0 }
      match row.event with
      | .move moves =>
        let deltas := moves.map (fun m => (m.head, m.delta))
        distanceAfter.foldl (fun u p =>
          if dcolor p = some i then
            { u with delta := (lookupLast p.1 deltas).getD 0 - (lookupLast p.2 deltas).getD 0 }
          else u) default
      | .copy target source =>
        distanceAfter.foldl (fun u p =>
          if (p.1 = target ∨ p.2 = target) ∧ dcolor p = some i then
            let (original, sign) := canonical spec.names
              (if p.1 = target then source else p.1) (if p.2 = target then source else p.2)
            { u with source := original.bind dcolor, reverse := decide (sign = -1) }
          else u) default
      | _ => default
  let comparison : Option (String × String) :=
    match row.event with
    | .less a b | .equal a b | .assertEqual a b => some (a, b)
    | _ => none
  let (test, rev) : Option Nat × Bool :=
    match comparison with
    | some (a, b) =>
      let (pair, sign) := canonical spec.names a b
      (pair.bind dcolor, decide (sign = -1))
    | none => (some 0, false)   -- `row("distance.test") = keys.head`
  { event := row.event, bit, yes, no := next,
    dataLeft := dl, dataRight := dr, dataTarget := dt, dataSource := ds,
    dataDelta, regs, distanceTest := test, distanceReverse := rev }

/-- A worker: its static data and the decoded ROM. -/
structure Worker where
  spec : WorkerSpec
  table : Array Fields

/-- Build the ROM once (`ScaffoldWindowWorkers.scala:34-47`). -/
def Worker.ofSpec (spec : WorkerSpec) : Worker :=
  let rb := liveReaders spec
  let db := liveDistances spec
  { spec,
    table := (spec.program.code.zipIdx.map fun (row, state) =>
      fieldsAt spec rb db state row).toArray }

/-- `table.read(pc.bits)` (`ScaffoldWindowWorkers.scala:130`). Addresses past the
table read the padding rows, which are copies of row `0` (`ScaffoldRom.scala:49`).
An empty program has no ROM in Scala; here it reads a halting dummy row. -/
def Worker.fields (w : Worker) (pc : Nat) : Fields :=
  let dummy : Fields :=
    { event := .halt, bit := false, yes := 0, no := 0, dataLeft := none, dataRight := none,
      dataTarget := none, dataSource := none, dataDelta := [], regs := [],
      distanceTest := none, distanceReverse := false }
  w.table.getD pc (w.table.getD 0 dummy)

/-! ## State -/

/-- `mode` (`ScaffoldWindowWorkers.scala:60`). -/
inductive Mode where
  | idle | run | done
  deriving DecidableEq, Repr

/-- Keys of `WindowLiveDistances.values` (`ScaffoldWindowLive.scala:11-13`):
`prefix.distance.r i`, `lengthKey`, and (flag workers) `hKey`
(`ScaffoldWindowWorkers.scala:42-45`). -/
inductive DistKey where
  | reg (i : Nat)
  | length
  | h
  deriving DecidableEq, Repr

/-- Worker state. -/
structure WorkerState where
  /-- The input stream read so far (one letter per `arrive`). -/
  text : List (Fin 2)
  /-- `prefix.begin` / `prefix.end` cursors. -/
  begin : Nat
  «end» : Nat
  /-- Reader data heads `prefix.data i`, by register index. -/
  data : List Nat
  /-- `prefix.data i.reverse`. -/
  reverse : List Bool
  /-- Distance keys `r i`. -/
  regs : List Int
  /-- `lengthKey`. -/
  length : Int
  /-- `hKey` (flag workers only). -/
  h : Int
  pc : Nat
  mode : Mode
  /-- `output` of the current circuit tick (matcher). -/
  output : Bool
  /-- `FlagStack` contents, top first (flag workers). -/
  flags : List Bool
  /-- Accumulated `circuit.require` violations. -/
  fault : Bool
  deriving Repr

/-- The state before the first tick: every `circuit.get(PREVIOUS, …)` default
(`ScaffoldWindowWorkers.scala:54-60`), zero offsets and registers, empty flags. -/
def WorkerState.initial (spec : WorkerSpec) : WorkerState :=
  { text := [], begin := 0, «end» := 0,
    data := List.replicate spec.readers.registers 0,
    reverse := List.replicate spec.readers.registers false,
    regs := List.replicate spec.distances.registers 0,
    length := 0, h := 0, pc := spec.program.start, mode := .idle,
    output := false, flags := [], fault := false }

namespace WorkerState

def getDist (s : WorkerState) : DistKey → Int
  | .reg i => s.regs.getD i 0
  | .length => s.length
  | .h => s.h

def setDist (s : WorkerState) (k : DistKey) (v : Int) : WorkerState :=
  match k with
  | .reg i => { s with regs := s.regs.set i v }
  | .length => { s with length := v }
  | .h => { s with h := v }

/-- `WindowHead.canMove` (`ScaffoldWindowStream.scala:173-178`). -/
def canMoveTo (s : WorkerState) (p : Nat) (δ : Int) : Bool :=
  decide (0 ≤ (p : Int) + δ) && decide ((p : Int) + δ ≤ s.text.length)

/-- `WindowHead.available` (`ScaffoldWindowStream.scala:168-172`) of an unadjusted
cursor; `none` (no register selected) is never available (invalid origin). -/
def availableAt (s : WorkerState) : Option Nat → Bool
  | none => false
  | some i => decide (s.data.getD i 0 < s.text.length)

/-- `read(which, enabled)` (`ScaffoldWindowWorkers.scala:115-119`, then
`WindowHead.read`, `ScaffoldWindowStream.scala:212-227`): a reversed head reads at
`offset - 1`. Returns the value (`None` when unavailable) and the availability
that `read` requires. -/
def readAt (s : WorkerState) : Option Nat → Option (Fin 2) × Bool
  | none => (none, false)
  | some i =>
    let p := s.data.getD i 0
    if s.reverse.getD i false then
      if p = 0 then (none, false)
      else if p - 1 < s.text.length then (s.text[p - 1]?, true) else (none, false)
    else if p < s.text.length then (s.text[p]?, true) else (none, false)

end WorkerState

/-! ## Distance operations (`ScaffoldWindowLive.scala`, `ScaffoldWindowRegisters.scala`) -/

/-- `values.select(which, registers)` on a key register (`ScaffoldWindowRegisters.scala:35-44`):
`None` selects nothing, i.e. the exact zero. -/
def selectReg (regs : List Int) : Option Nat → Int
  | none => 0
  | some i => regs.getD i 0

/-- `WindowLiveDistances.compare` (`ScaffoldWindowLive.scala:85-89`) with
`compareZero` (`ScaffoldWindowRegisters.scala:84-95`), read as integers:
`(v = 0, if distance.reverse then v > 0 else v < 0)`. -/
def compare (f : Fields) (s : WorkerState) : Bool × Bool :=
  let v := selectReg s.regs f.distanceTest
  (decide (v = 0), if f.distanceReverse then decide (0 < v) else decide (v < 0))

/-- `WindowLiveDistances.execute` (`ScaffoldWindowLive.scala:90-97`): every key
simultaneously from the snapshot, `r_i := (±snapshot(source)) + delta`. -/
def execute (f : Fields) (enabled : Bool) (s : WorkerState) : WorkerState :=
  if enabled then
    { s with regs := s.regs.mapIdx fun i old =>
        match f.regs[i]? with
        | none => old
        | some u =>
          let v := selectReg s.regs u.source
          (if u.reverse then -v else v) + u.delta }
  else s

/-- `WindowLiveDistances.initializeValues` (`ScaffoldWindowLive.scala:74-83`):
sequential assignments, `None` resets, `Some (key, sign)` assigns `sign • key`.
(The Scala key-set check against `before(start)` is a construction check.) -/
def initializeValues (spec : WorkerSpec)
    (mapping : List (Pair × Option (DistKey × Int))) (enabled : Bool)
    (s : WorkerState) : WorkerState :=
  if enabled then
    mapping.foldl (fun s (pair, value) =>
      match lookupFirst pair spec.distances.colors with
      | none => s
      | some i =>
        match value with
        | none => s.setDist (.reg i) 0
        | some (k, sign) =>
          let v := s.getDist k
          s.setDist (.reg i) (if sign = -1 then -v else v)) s
  else s

/-! ## The worker operations (`ScaffoldWindowWorkers.scala`) -/

variable (w : Worker)

/-- `arrive()` (`ScaffoldWindowWorkers.scala:65-69`) with the new input letter:
`end.move(1)`, `lengthKey += 1`, and `hKey += 1` for flag workers.
Scala constructs a fresh `WindowWorker` every circuit tick, whose `output` starts
`FALSE` (`ScaffoldWindowWorkers.scala:61`); `arrive` is the first worker call of a
tick (`ScaffoldWindowPal.scala:118-119`), so the per-tick reset of `output` is
done here. -/
def arrive (c : Fin 2) (s : WorkerState) : WorkerState :=
  let s := { s with text := s.text ++ [c], output := false }
  let s := { s with fault := s.fault || !s.canMoveTo s.end 1, «end» := s.end + 1,
                    length := s.length + 1 }
  if w.spec.isFlags then { s with h := s.h + 1 } else s

/-- `rawStart(head, source, reversed, enabled)` (`ScaffoldWindowWorkers.scala:71-75`). -/
def rawStart (head : String) (source : Nat) (reversed : Bool) (enabled : Bool)
    (s : WorkerState) : WorkerState :=
  match lookupFirst head w.spec.readers.colors with
  | none => s
  | some i =>
    if enabled then { s with data := s.data.set i source, reverse := s.reverse.set i reversed }
    else s

/-- `resetFlags(enabled)` (`ScaffoldWindowWorkers.scala:77-84`). Only flag workers
have one (Scala throws otherwise; not modelled). -/
def resetFlags (_w : Worker) (enabled : Bool) (s : WorkerState) : WorkerState :=
  if enabled then
    { s with begin := s.end, length := 0, h := 0, flags := [], mode := .idle }
  else s

/-- `start(enabled)` (`ScaffoldWindowWorkers.scala:86-107`). -/
def start (enabled : Bool) (s : WorkerState) : WorkerState :=
  let s :=
    if w.spec.isFlags then
      let s := { s with fault := s.fault || (enabled && decide (s.mode = .run)) }
      let b := s.begin
      let e := s.end
      let s := rawStart w "Origin" b false enabled s
      let s := rawStart w "TextOrigin" e true enabled s
      let s := rawStart w "OriginalEnd" b true enabled s
      let s := initializeValues w.spec
        [(("Lower", "Upper"), some (.h, -1)),
         (("Origin", "OriginalEnd"), some (.length, -1)),
         (("Origin", "Upper"), some (.length, -1)),
         (("OriginalEnd", "Lower"), some (.h, 1)),
         (("OriginalEnd", "TextOrigin"), some (.length, 1)),
         (("OriginalEnd", "Upper"), none)] enabled s
      if enabled then { s with flags := [] } else s
    else
      let e := s.end
      let s := rawStart w "Origin" e true enabled s
      let s := rawStart w "Tail" e false enabled s
      initializeValues w.spec [(("Origin", "Tail"), some (.length, -1))] enabled s
  if enabled then { s with pc := w.spec.program.start, mode := .run } else s

/-- `mark(enabled)` (`ScaffoldWindowWorkers.scala:109`): `hKey := 0`
(flag workers; the matcher has no `hKey` register). -/
def mark (_w : Worker) (enabled : Bool) (s : WorkerState) : WorkerState :=
  if enabled then { s with h := 0 } else s

/-- The opcode tests of `step`. -/
def isOp (e : Event) (op : String) : Bool := e.op == op

/-- `step(active, writer)` (`ScaffoldWindowWorkers.scala:129-168`), in Scala
statement order. -/
def step (active : Bool) (s : WorkerState) : WorkerState :=
  let f := w.fields s.pc
  let e := f.event
  -- 132: distance comparison on the current registers
  let (equal, less) := compare f s
  -- 133-136: symbol reads and availability
  let symbolTest := active && isOp e "symbols"
  let (a, okA) := s.readAt f.dataLeft
  let (b, okB) := s.readAt f.dataRight
  let available := s.availableAt f.dataLeft
  let decision :=
    if isOp e "equal" then equal
    else if isOp e "less" then less
    else if isOp e "available" then available
    else decide (a = b)
  let fault := s.fault || (symbolTest && !okA) || (symbolTest && !okB)
  -- 140: assert_equal
  let fault := fault || (active && isOp e "assert_equal" && !equal)
  -- 141-146: match (matcher only)
  let (fault, output) :=
    if w.spec.isFlags then (fault, s.output)
    else
      let matched := active && isOp e "match"
      let bReg := lookupFirst "B" w.spec.readers.colors
      (fault || (matched && s.availableAt bReg), s.output || matched)
  let s := { s with fault, output }
  -- 147: distances
  let s := execute f active s
  -- 148-160: head moves and copies; the copy source is a snapshot
  let srcPos := f.dataSource.map fun j => s.data.getD j 0
  let srcRev := f.dataSource.map fun j => s.reverse.getD j false
  let s := (List.range w.spec.readers.registers).foldl (fun s i =>
    let p := s.data.getD i 0
    let r := s.reverse.getD i false
    let raw := f.dataDelta.getD i 0
    let δ := if r then -raw else raw
    let moving := active && δ ≠ 0
    let s := { s with fault := s.fault || (moving && !s.canMoveTo p δ),
                      data := if moving then s.data.set i ((p : Int) + δ).toNat else s.data }
    let copying := active && isOp e "copy" && f.dataTarget = some i
    match copying, srcPos, srcRev with
    | true, some q, some rv => { s with data := s.data.set i q, reverse := s.reverse.set i rv }
    | _, _, _ => s) s
  -- 161-166: flag push / halt
  let s :=
    if w.spec.isFlags then
      let s := if active && isOp e "flag" then { s with flags := f.bit :: s.flags } else s
      if active && isOp e "halt" then { s with mode := .done } else s
    else { s with fault := s.fault || (active && isOp e "halt") }
  -- 167: next pc
  if active then { s with pc := if decision then f.yes else f.no } else s

/-- `service()` (`ScaffoldWindowWorkers.scala:121-127`): `quantum` steps, each with
`active := mode = run` read afresh. -/
def service (s : WorkerState) : WorkerState :=
  (List.range w.spec.quantum).foldl (fun s _ => step w (decide (s.mode = .run)) s) s

/-- `output` (`ScaffoldWindowWorkers.scala:61,145`). -/
def output (s : WorkerState) : Bool := s.output

/-- `mode.eqTo("done")`. -/
def modeDone (s : WorkerState) : Bool := decide (s.mode = .done)

/-- `flags` (the `FlagStack`, top first). -/
def flags (s : WorkerState) : List Bool := s.flags

end PalPeg.ScaWindowWorker
