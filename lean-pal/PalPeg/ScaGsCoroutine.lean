import PalPeg.ScaGsProgram
import PalPeg.ScaGsTables
import Std.Data.HashMap

/-!
# GS head programs at the coroutine level (mirror of the Scala generators)

The GS head programs of window-pal are written in Scala as coroutines (ports
of the Python generators of `gs_heads.py` / `gs_match_heads.py` /
`gs_flag_heads.py` / `gs_dual_flags.py`) and then *compiled* by
`GsProgram.compileController` (`GsProgram.scala:295-346`) into the finite
tables of `PalPeg.ScaGsTables`. This file transcribes the coroutine level as
an explicit, total, finite-state step function, so that a later proof can check
row by row that a compiled table is the coroutine's transition system.

## Representation

* `Frame` — one suspended generator frame, exactly Scala's
  `Coroutine.Frame(name, site, locals)` (`Coroutine.scala:37`): one constructor
  per generator class, carrying its locals (`Generator.locals`) and its `site`
  (the index of the textual `yield`/`yield from`, numbered as in Scala).
* `Config` — the `yield from` chain, outermost first (`Generator.frames`,
  `Coroutine.scala:155-158`).
* `stepFrame` — one frame's `step` (the `site match` of each class), returning
  an `Action` (`Coroutine.scala:53-65`): `emit` (`emitAt`), `call` (`callAt`)
  or `ret` (`Return`).
* `next` — the driver `Generator.send` (`Coroutine.scala:114-150`): resume the
  innermost delegate, pop returned delegates, run to the next `yield`.

**Convention for `yield from` results.** In Scala a parent resumed after its
child returned is stepped with `response = None` and reads `child.result`
(e.g. `GsHeads.scala:350`). Here the child's return value is passed as the
parent's `input` instead (a `Unit` child returns `none`). Since the parent site
following a `yield from` never reads `response`, this is the same computation.

**Failures.** Scala's `response.get` on `None`, `Option.get` on an unset local,
and `requireK` throw. Here they make `stepFrame` return `none`; so do fuel
exhaustion of `advance` (never reached by these programs; see the check below).

## Rows ↔ configurations

`compileController` (`GsProgram.scala:295-346`) runs a BFS over *construction
states*: state `0` is the halting sink (every `Returned` maps to it,
`GsProgram.scala:324`), state `1` is the first yield, and a new state is created
for every new key `(pending event, frames)` (`GsProgram.scala:326-337`),
exploring responses `false` then `true` after tests, `None` after commands, in
cursor order. `constructionStates = code.size` (`GsProgram.scala:344`) counts
the sink plus the keys. `compileMatcher(unit = false)` and
`compileDualFlags(unit = false)` still apply `minimize` (`reduce` defaults to
`true`, `GsProgram.scala:295`, `GsMatchHeads.scala:201`,
`GsDualFlags.scala:319`). So **a table row is a bisimulation class of
configurations, not a configuration**: 875 → 294 rows (matcher),
1176 → 492 rows (flags).

`minimize` (`GsProgram.scala:236-257`) numbers the classes of its final (stable)
refinement by first occurrence in construction-state order. Hence

* every reachable configuration determines its row (`explore` computes this
  map and checks it is functional and event-preserving);
* row `r ≥ 1` has a canonical representative: the configuration of the first
  construction state whose class is `r` (`rowConfig`). This is recoverable from
  the exported table alone, because the BFS order is reproduced here
  (`explore`) and the check `firstOccurrenceOk` confirms that the classes
  appear in the order `1, 2, 3, …`.

No extra export is needed. (An export of `compileController(reduce = false)`
plus the `groups` vector of `minimize` would make the class map a literal
table instead of a computed one.)
-/

set_option autoImplicit false

namespace PalPeg.ScaGsCoroutine
open PalPeg.ScaGsProgram

/-- `Event.move(Movement(h, d)*)` (`GsProgram.scala:57`). -/
def mv (moves : List (String × Int)) : Event :=
  .move (moves.map fun (head, delta) => { head, delta })

/-- A generator's return value: `none` for `Unit` generators (`Return(())`),
`some b` for `Boolean` ones. -/
abbrev Value := Option Bool

/-- One suspended generator frame: Scala's `Coroutine.Frame(name, site, locals)`
(`Coroutine.scala:37`). The constructor is the generator class (its Python
`co_name`); the fields are its `locals` (`Generator.locals`), then `site`.
Generator objects held in Scala `var`s (`Decompose.first`, …) are not locals:
they live in the delegate chain (`Config`). -/
inductive Frame where
  /-- `Initialize(k)`, name `_initialize` (`GsHeads.scala:47-68`); locals `k`. -/
  | initialize (k : Nat) (site : Nat)
  /-- `ResetShift(k, search)`, name `_reset_shift` (`GsHeads.scala:73-148`);
  locals `k`, `search`, `phase`, and `nonempty` once assigned. -/
  | resetShift (k : Nat) (search : Bool) (phase : Nat) (nonempty : Option Bool) (site : Nat)
  /-- `PeriodShift(k, search)`, name `_period_shift` (`GsHeads.scala:153-180`). -/
  | periodShift (k : Nat) (search : Bool) (site : Nat)
  /-- `First(k, bounded)`, name `_first` (`GsHeads.scala:186-246`). -/
  | first (k : Nat) (bounded : Bool) (site : Nat)
  /-- `Second(k)`, name `_second` (`GsHeads.scala:251-314`). -/
  | second (k : Nat) (site : Nat)
  /-- `Decompose(k)`, name `_decompose` (`GsHeads.scala:320-403`). -/
  | decompose (k : Nat) (site : Nat)
  /-- `Report(flags)`, name `_report` (`GsHeads.scala:409-455`). -/
  | report (flags : Bool) (site : Nat)
  /-- `FinishFlags`, name `_finish_flags` (`GsHeads.scala:460-488`); no locals. -/
  | finishFlags (site : Nat)
  /-- `BorderController(k, flags, tailOrigin)`, name `border_controller`
  (`GsHeads.scala:496-732`); locals `k`, `flags`, `tail_origin`, `first_stage`,
  and `period_exists` once assigned. -/
  | borderController (k : Nat) (flags : Bool) (tailOrigin : String) (firstStage : Bool)
      (periodExists : Option Bool) (site : Nat)
  /-- `MatcherController(k)`, name `matcher_controller` (`GsMatchHeads.scala:29-196`);
  locals `k`, and `period_exists`, `phase`, `prefix_ok` once assigned. -/
  | matcherController (k : Nat) (periodExists : Option Bool) (prefixOk : Option Bool)
      (phase : Option Nat) (site : Nat)
  /-- `FlagController(k, name, tailOrigin)` (`GsFlagHeads.scala:425-448`), also
  `DualFlagController` (`GsDualFlags.scala:314`, name `dual_flag_controller`,
  `tailOrigin = "TextOrigin"`). Scala's `locals` is only `k`; `name` is the
  frame name and `tailOrigin` a constant of the program. -/
  | flagController (name : String) (k : Nat) (tailOrigin : String) (site : Nat)
  deriving DecidableEq, Hashable, Repr

/-- The suspended `yield from` chain, outermost first (`Generator.frames`,
`Coroutine.scala:155-158`). -/
abbrev Config := List Frame

/-- `Action` (`Coroutine.scala:53-65`). `emit e f` is `emitAt(site, e)` with `f`
the frame at the new site; `call f c` is `callAt(site, c)` with `f` the parent
at the new site and `c` the fresh child; `ret v` is `Return(v)`. -/
inductive Action where
  | emit (event : Event) (self : Frame)
  | call (self : Frame) (child : Frame)
  | ret (value : Value)
  deriving DecidableEq, Repr

/-- A fresh `ResetShift(k, search)` (`phase = 0`, `nonempty = None`, site 0). -/
def freshResetShift (k : Nat) (search : Bool) : Frame := .resetShift k search 0 none 0

/-- A fresh `BorderController(k, flags, tailOrigin)` (`firstStage = true`,
`periodExists = None`, `GsHeads.scala:498-499`). -/
def freshBorder (k : Nat) (flags : Bool) (tailOrigin : String) : Frame :=
  .borderController k flags tailOrigin true none 0

/-- `Initialize.step` (`GsHeads.scala:50-67`). -/
def stepInitialize (k site : Nat) : Option Action :=
  let atSite := Frame.initialize k
  match site with
  | 0 => some (.emit (.copy "A" "Cut") (atSite 1))
  | 1 => some (.emit (.copy "P" "Cut") (atSite 2))
  | 2 => some (.emit (mv [("P", 1)]) (atSite 3))
  | 3 => some (.emit (.copy "B" "P") (atSite 4))
  | 4 => some (.emit (.copy "KP" "Cut") (atSite 5))
  | 5 => some (.emit (mv [("KP", (k : Int))]) (atSite 6))
  | _ => some (.ret none)

/-- `ResetShift.step` (`GsHeads.scala:108-147`), with `shiftEvent`, `loopHead`,
`afterLoop`, `tail` (`GsHeads.scala:82-106`). -/
def stepResetShift (k : Nat) (search : Bool) (phase : Nat) (nonempty : Option Bool)
    (site : Nat) (input : Option Bool) : Option Action :=
  let atSite := Frame.resetShift k search
  let shiftEvent : Event :=
    if search then mv [("P", 1), ("B", 1), ("KP", -1)] else mv [("P", 1), ("KP", (k : Int))]
  let loopHead := fun (ph : Nat) (ne : Option Bool) => Action.emit (.equal "A" "Cut") (atSite ph ne 2)
  let tail := fun (ph : Nat) (ne : Option Bool) =>
    if !search then Action.emit (.copy "B" "P") (atSite ph ne 9) else Action.ret none
  let afterLoop := fun (ph : Nat) (ne : Option Bool) => do
    let n ← ne
    if !n || ph != 0 then pure (Action.emit shiftEvent (atSite ph ne (if search then 7 else 8)))
    else pure (tail ph ne)
  match site with
  | 0 => some (.emit (.equal "A" "Cut") (atSite 0 nonempty 1))
  | 1 => do
    let b ← input
    pure (loopHead phase (some (!b)))
  | 2 => do
    let b ← input
    if b then afterLoop phase nonempty
    else if search then pure (.emit (mv [("A", -1), ("B", -1)]) (atSite phase nonempty 3))
    else pure (.emit (mv [("A", -1)]) (atSite phase nonempty 4))
  | 3 | 4 =>
    let ph := phase + 1
    if ph == k then some (.emit shiftEvent (atSite ph nonempty (if search then 5 else 6)))
    else some (loopHead ph nonempty)
  | 5 | 6 => some (loopHead 0 nonempty)
  | 7 | 8 => some (tail phase nonempty)
  | _ => some (.ret none)

/-- `PeriodShift.step` (`GsHeads.scala:158-179`). -/
def stepPeriodShift (k : Nat) (search : Bool) (site : Nat) (input : Option Bool) : Option Action :=
  let atSite := Frame.periodShift k search
  let loopHead := Action.emit (.less "Walk" "First") (atSite 2)
  match site with
  | 0 => some (.emit (.copy "Walk" "Cut") (atSite 1))
  | 1 => some loopHead
  | 2 => do
    let b ← input
    if b then
      if search then pure (.emit (mv [("Walk", 1), ("A", -1), ("P", 1), ("KP", -1)]) (atSite 3))
      else pure (.emit (mv [("Walk", 1), ("A", -1), ("P", 1), ("KP", (k : Int))]) (atSite 4))
    else pure (.ret none)
  | _ => some loopHead

/-- `First.step` (`GsHeads.scala:195-245`). -/
def stepFirst (k : Nat) (bounded : Bool) (site : Nat) (input : Option Bool) : Option Action :=
  let atSite := Frame.first k bounded
  let outerHead := Action.emit (.less "P" "End") (atSite 2)
  let innerHead := Action.emit (.less "B" "End") (atSite 4)
  let afterInner := Action.emit (.equal "B" "KP") (atSite 8)
  match site with
  | 0 => some (.call (atSite 1) (.initialize k 0))
  | 1 => some outerHead
  | 2 => do
    let b ← input
    if !b then pure (.ret (some false))
    else if bounded then pure (.emit (.less "P" "Second") (atSite 3))
    else pure innerHead
  | 3 => do
    let b ← input
    pure (if b then innerHead else .ret (some false))
  | 4 => do
    let b ← input
    pure (if b then .emit (.less "B" "KP") (atSite 5) else afterInner)
  | 5 => do
    let b ← input
    pure (if b then .emit (.symbols "A" "B") (atSite 6) else afterInner)
  | 6 => do
    let b ← input
    pure (if b then .emit (mv [("A", 1), ("B", 1)]) (atSite 7) else afterInner)
  | 7 => some innerHead
  | 8 => do
    let b ← input
    pure (if b then .ret (some true) else .call (atSite 9) (freshResetShift k false))
  | _ => some outerHead

/-- `Second.step` (`GsHeads.scala:262-313`). -/
def stepSecond (k site : Nat) (input : Option Bool) : Option Action :=
  let atSite := Frame.second k
  let outerHead := Action.emit (.less "P" "End") (atSite 2)
  let innerHead := Action.emit (.less "B" "End") (atSite 3)
  let afterInner := Action.emit (.less "A" "KFirst") (atSite 8)
  let resetShift := Action.call (atSite 11) (freshResetShift k false)
  match site with
  | 0 => some (.call (atSite 1) (.initialize k 0))
  | 1 => some outerHead
  | 2 => do
    let b ← input
    pure (if b then innerHead else .ret (some false))
  | 3 => do
    let b ← input
    pure (if b then .emit (.symbols "A" "B") (atSite 4) else afterInner)
  | 4 => do
    let b ← input
    pure (if b then .emit (mv [("A", 1), ("B", 1)]) (atSite 5) else afterInner)
  | 5 => some (.emit (.less "Reach" "B") (atSite 6))
  | 6 => do
    let b ← input
    pure (if b then .emit (.less "B" "KP") (atSite 7) else innerHead)
  | 7 => do
    let b ← input
    pure (if b then innerHead else .ret (some true))
  | 8 => do
    let b ← input
    pure (if b then resetShift else .emit (.less "Reach" "A") (atSite 9))
  | 9 => do
    let b ← input
    pure (if b then resetShift else .call (atSite 10) (.periodShift k false 0))
  | _ => some outerHead

/-- `Decompose.step` (`GsHeads.scala:342-402`). Sites 2, 9, 11 follow a
`yield from`: `input` is `first.result` / `second.result`. -/
def stepDecompose (k site : Nat) (input : Option Bool) : Option Action :=
  let atSite := Frame.decompose k
  let outer := Action.call (atSite 2) (.first k false 0)
  let extendHead := Action.emit (.less "B" "End") (atSite 5)
  let afterExtend := Action.emit (.copy "Reach" "B") (atSite 8)
  let boundedHead := Action.call (atSite 11) (.first k true 0)
  let cutHead := Action.emit (.less "Cut" "P") (atSite 12)
  match site with
  | 0 => some (.emit (.copy "Cut" "Origin") (atSite 1))
  | 1 => some outer
  | 2 => do
    let r ← input
    pure (if !r then .ret (some false) else .emit (.copy "First" "P") (atSite 3))
  | 3 => some (.emit (.copy "KFirst" "B") (atSite 4))
  | 4 => some extendHead
  | 5 => do
    let b ← input
    pure (if b then .emit (.symbols "A" "B") (atSite 6) else afterExtend)
  | 6 => do
    let b ← input
    pure (if b then .emit (mv [("A", 1), ("B", 1)]) (atSite 7) else afterExtend)
  | 7 => some extendHead
  | 8 => some (.call (atSite 9) (.second k 0))
  | 9 => do
    let r ← input
    pure (if !r then .ret (some true) else .emit (.copy "Second" "P") (atSite 10))
  | 10 => some boundedHead
  | 11 => do
    let r ← input
    pure (if r then cutHead else outer)
  | 12 => do
    let b ← input
    pure (if b then .emit (mv [("Cut", 1), ("Second", 1)]) (atSite 13) else boundedHead)
  | _ => some cutHead

/-- `Report.step` (`GsHeads.scala:416-454`). -/
def stepReport (flags : Bool) (site : Nat) (input : Option Bool) : Option Action :=
  let atSite := Frame.report flags
  let fillHead := Action.emit (.less "KP" "Cursor") (atSite 4)
  let finalTest := Action.emit (.less "Cursor" "Lower") (atSite 9)
  match site with
  | 0 => some (if !flags then .emit (.border "KP") (atSite 1) else .emit (.less "KP" "Lower") (atSite 2))
  | 1 => some (.ret (some false))
  | 2 => do
    let b ← input
    pure (if b then .ret (some true) else .emit (.less "Cursor" "KP") (atSite 3))
  | 3 => do
    let b ← input
    pure (if b then finalTest else fillHead)
  | 4 => do
    let b ← input
    pure (if b then .emit (.flag false) (atSite 5) else .emit (.flag true) (atSite 7))
  | 5 => some (.emit (mv [("Cursor", -1)]) (atSite 6))
  | 6 => some fillHead
  | 7 => some (.emit (mv [("Cursor", -1)]) (atSite 8))
  | 8 => some finalTest
  | _ => do
    let b ← input
    pure (.ret (some b))

/-- `FinishFlags.step` (`GsHeads.scala:463-487`). -/
def stepFinishFlags (site : Nat) (input : Option Bool) : Option Action :=
  let atSite := Frame.finishFlags
  let head := Action.emit (.less "Cursor" "Lower") (atSite 1)
  match site with
  | 0 => some head
  | 1 => do
    let b ← input
    pure (if b then .ret none else .emit (.equal "Cursor" "Origin") (atSite 2))
  | 2 => do
    let b ← input
    pure (if b then .emit (.flag true) (atSite 3) else .emit (.flag false) (atSite 4))
  | 3 | 4 => some (.emit (mv [("Cursor", -1)]) (atSite 5))
  | _ => some head

/-- `BorderController.step` (`GsHeads.scala:548-731`), with the helpers of
`GsHeads.scala:509-546`. Sites 6 and 29 follow a `yield from` whose result is
read (`decompose.result`, `report.result`); sites 5, 30, 34, 35, 44 follow a
`Unit` child. `requireK` (`GsHeads.scala:40-44`) fails as `none`. -/
def stepBorderController (k : Nat) (flags : Bool) (tailOrigin : String) (firstStage : Bool)
    (periodExists : Option Bool) (site : Nat) (input : Option Bool) : Option Action :=
  let atSite := fun (fs : Bool) (pe : Option Bool) (s : Nat) =>
    Frame.borderController k flags tailOrigin fs pe s
  let here := atSite firstStage periodExists
  let stageHead := fun (fs : Bool) => Action.emit (.less "Origin" "End") (atSite fs periodExists 3)
  let finish := fun (nextSite : Nat) => Action.call (here nextSite) (.finishFlags 0)
  let startDecomposition := Action.call (here 6) (.decompose k 0)
  let offsetHead := Action.emit (.less "Walk" "Cut") (here 14)
  let matchHead := Action.emit (.less "Second" "P") (here 18)
  let scanHead := Action.emit (.less "B" "OriginalEnd") (here 19)
  let endTest := Action.emit (.equal "B" "OriginalEnd") (here 22)
  let prefixHead := Action.emit (.less "Walk" "Cut") (here 25)
  let prefixDone := Action.emit (.equal "Walk" "Cut") (here 28)
  let restoreB := Action.emit (.copy "B" "OriginalEnd") (here 31)
  let resetShift := Action.call (here 35) (freshResetShift k true)
  let shiftDecision : Option Action := do
    let pe ← periodExists
    pure (if pe then .emit (.less "A" "KFirst") (here 32) else resetShift)
  let shrinkStart := Action.emit (.copy "Second" "Origin") (here 36)
  let shrinkWalk := Action.emit (.less "Walk" "Cut") (here 38)
  let shrinkEnd := Action.emit (.less "Second" "End") (here 42)
  match site with
  | 0 => if k < 4 then none else some (.emit (.copy "End" "OriginalEnd") (atSite true periodExists 1))
  | 1 => some (.emit (.copy "Tail" tailOrigin) (here 2))
  | 2 => some (stageHead firstStage)
  | 3 => do
    let b ← input
    if !b then pure (if flags then finish 44 else .ret none)
    else if flags && tailOrigin != "Origin" then pure (.emit (.less "End" "Lower") (here 4))
    else pure startDecomposition
  | 4 => do
    let b ← input
    pure (if b then finish 5 else startDecomposition)
  | 5 => some (.ret none)
  | 6 => do
    let r ← input
    pure (.emit (.copy "P" "Tail") (atSite firstStage (some r) 7))
  | 7 => some (.emit (.copy "KP" "End") (here 8))
  | 8 => some (if firstStage then .emit (mv [("P", 1), ("KP", -1)]) (here 9)
               else .emit (.copy "A" "Cut") (here 10))
  | 9 => some (.emit (.copy "A" "Cut") (here 10))
  | 10 => some (.emit (.copy "B" "P") (here 11))
  | 11 => some (.emit (.copy "Second" "OriginalEnd") (here 12))
  | 12 => some (.emit (.copy "Walk" "Origin") (here 13))
  | 13 => some offsetHead
  | 14 => do
    let b ← input
    pure (if b then .emit (mv [("Walk", 1), ("B", 1), ("Second", -2)]) (here 15)
          else .emit (.equal "Cut" "Origin") (here 16))
  | 15 => some offsetHead
  | 16 => do
    let b ← input
    pure (if b then .emit (mv [("Second", -1)]) (here 17) else matchHead)
  | 17 => some matchHead
  | 18 => do
    let b ← input
    pure (if b then shrinkStart else scanHead)
  | 19 => do
    let b ← input
    pure (if b then .emit (.symbols "A" "B") (here 20) else endTest)
  | 20 => do
    let b ← input
    pure (if b then .emit (mv [("A", 1), ("B", 1)]) (here 21) else endTest)
  | 21 => some scanHead
  | 22 => do
    let b ← input
    if b then pure (.emit (.copy "Walk" "Origin") (here 23)) else shiftDecision
  | 23 => some (.emit (.copy "B" "P") (here 24))
  | 24 => some prefixHead
  | 25 => do
    let b ← input
    pure (if b then .emit (.symbols "Walk" "B") (here 26) else prefixDone)
  | 26 => do
    let b ← input
    pure (if b then .emit (mv [("Walk", 1), ("B", 1)]) (here 27) else prefixDone)
  | 27 => some prefixHead
  | 28 => do
    let b ← input
    pure (if b then .call (here 29) (.report flags 0) else restoreB)
  | 29 => do
    let r ← input
    pure (if r then finish 30 else restoreB)
  | 30 => some (.ret none)
  | 31 => shiftDecision
  | 32 => do
    let b ← input
    pure (if b then resetShift else .emit (.less "Reach" "A") (here 33))
  | 33 => do
    let b ← input
    pure (if b then resetShift else .call (here 34) (.periodShift k true 0))
  | 34 | 35 => some matchHead
  | 36 => some (.emit (.copy "Walk" "Origin") (here 37))
  | 37 => some shrinkWalk
  | 38 => do
    let b ← input
    pure (if b then .emit (mv [("Walk", 1), ("Second", 2)]) (here 39)
          else .emit (.equal "Cut" "Origin") (here 40))
  | 39 => some shrinkWalk
  | 40 => do
    let b ← input
    pure (if !b then .emit (mv [("Second", -1)]) (here 41) else shrinkEnd)
  | 41 => some shrinkEnd
  | 42 => do
    let b ← input
    pure (if b then .emit (mv [("End", -1), ("Tail", 1)]) (here 43) else stageHead false)
  | 43 => some shrinkEnd
  | _ => some (.ret none)

/-- `MatcherController.step` (`GsMatchHeads.scala:69-195`), with the helpers of
`GsMatchHeads.scala:42-67`. Site 2 follows `yield from _decompose(k)`. The
check `k < 4` (`GsMatchHeads.scala:74`) fails as `none`. -/
def stepMatcherController (k : Nat) (periodExists prefixOk : Option Bool) (phase : Option Nat)
    (site : Nat) (input : Option Bool) : Option Action :=
  let atSite := Frame.matcherController k
  let here := atSite periodExists prefixOk phase
  let offsetHead := Action.emit (.less "Walk" "Cut") (here 8)
  let outerLoop := Action.emit (.copy "Walk" "Origin") (here 11)
  let matchHead := fun (ok : Option Bool) => Action.emit (.available "B") (atSite periodExists ok phase 13)
  let afterFor := fun (ok : Option Bool) (ph : Option Nat) =>
    Action.emit (.equal "A" "End") (atSite periodExists ok ph 19)
  let forBody := fun (ph : Option Nat) => do
    let ok ← prefixOk
    pure (if !ok then afterFor prefixOk ph else Action.emit (.less "Walk" "Cut") (atSite periodExists prefixOk ph 16))
  let resetShift := Action.call (here 25) (freshResetShift k true)
  let shiftDecision : Option Action := do
    let pe ← periodExists
    pure (if pe then .emit (.less "A" "KFirst") (here 22) else resetShift)
  match site with
  | 0 => if k < 4 then none else some (.emit (.copy "End" "Tail") (here 1))
  | 1 => some (.call (here 2) (.decompose k 0))
  | 2 => do
    let r ← input
    pure (.emit (.copy "P" "Tail") (atSite (some r) prefixOk phase 3))
  | 3 => some (.emit (.copy "KP" "End") (here 4))
  | 4 => some (.emit (.copy "A" "Cut") (here 5))
  | 5 => some (.emit (.copy "B" "P") (here 6))
  | 6 => some (.emit (.copy "Walk" "Origin") (here 7))
  | 7 => some offsetHead
  | 8 => do
    let b ← input
    pure (if b then .emit (.available "B") (here 9) else outerLoop)
  | 9 => do
    let b ← input
    pure (if b then .emit (mv [("Walk", 1), ("B", 1)]) (here 10) else .emit (.available "B") (here 9))
  | 10 => some offsetHead
  | 11 => some (.emit (.copy "U" "P") (here 12))
  | 12 => some (matchHead (some true))
  | 13 => do
    let b ← input
    pure (if b then .emit (.symbols "A" "B") (here 14) else matchHead prefixOk)
  | 14 => do
    let b ← input
    if b then pure (.emit (mv [("A", 1), ("B", 1)]) (here 15)) else shiftDecision
  | 15 => forBody (some 0)
  | 16 => do
    let b ← input
    pure (if b then .emit (.symbols "Walk" "U") (here 17) else afterFor prefixOk phase)
  | 17 => do
    let b ← input
    pure (if b then .emit (mv [("Walk", 1), ("U", 1)]) (here 18) else afterFor (some false) phase)
  | 18 => if phase == some 0 then forBody (some 1) else some (afterFor prefixOk phase)
  | 19 => do
    let b ← input
    if b then do
      let ok ← prefixOk
      if ok then pure (.emit (.assertEqual "Walk" "Cut") (here 20)) else shiftDecision
    else pure (matchHead prefixOk)
  | 20 => some (.emit (.«match» "B") (here 21))
  | 21 => shiftDecision
  | 22 => do
    let b ← input
    pure (if b then resetShift else .emit (.less "Reach" "A") (here 23))
  | 23 => do
    let b ← input
    pure (if b then resetShift else .call (here 24) (.periodShift k true 0))
  | _ => some outerLoop

/-- `FlagController.step` (`GsFlagHeads.scala:429-447`); the child at site 4 is
`borderController(k, flags = true, tailOrigin)`. -/
def stepFlagController (name : String) (k : Nat) (tailOrigin : String) (site : Nat)
    (input : Option Bool) : Option Action :=
  let atSite := Frame.flagController name k tailOrigin
  match site with
  | 0 => some (.emit (.copy "Cursor" "Upper") (atSite 1))
  | 1 => some (.emit (mv [("Cursor", -1)]) (atSite 2))
  | 2 => some (.emit (.less "Cursor" "Lower") (atSite 3))
  | 3 => do
    let b ← input
    pure (if !b then .call (atSite 4) (freshBorder k true tailOrigin) else .ret none)
  | _ => some (.ret none)

/-- One frame's `step(response)` (`Coroutine.scala:99`). `input` is the test
response after an `emit`, or the child's return value after a `call` (see the
module docstring). `none` = Scala exception. -/
def stepFrame : Frame → Option Bool → Option Action
  | .initialize k site, _ => stepInitialize k site
  | .resetShift k search phase nonempty site, input => stepResetShift k search phase nonempty site input
  | .periodShift k search site, input => stepPeriodShift k search site input
  | .first k bounded site, input => stepFirst k bounded site input
  | .second k site, input => stepSecond k site input
  | .decompose k site, input => stepDecompose k site input
  | .report flags site, input => stepReport flags site input
  | .finishFlags site, input => stepFinishFlags site input
  | .borderController k flags tailOrigin firstStage periodExists site, input =>
    stepBorderController k flags tailOrigin firstStage periodExists site input
  | .matcherController k periodExists prefixOk phase site, input =>
    stepMatcherController k periodExists prefixOk phase site input
  | .flagController name k tailOrigin site, input => stepFlagController name k tailOrigin site input

/-- `Step` (`Coroutine.scala:41-47`): `Yielded(event)` with the new frame chain,
or `Returned(value)`. -/
inductive Outcome where
  | yielded (event : Event) (config : Config)
  | returned (value : Value)
  deriving DecidableEq, Repr

/-- `Generator.advance` (`Coroutine.scala:135-150`) of a frame without delegate:
step it; on `Call(child)` start the child with `send(None)` and, if the child
returned at once, step the parent again with the child's result. `fuel` bounds
the (tail-recursive in Scala) chain of immediately returning calls. -/
def advance : Nat → Frame → Option Bool → Option Outcome
  | 0, _, _ => none
  | fuel + 1, f, input => do
    match ← stepFrame f input with
    | .emit e f' => pure (.yielded e [f'])
    | .ret v => pure (.returned v)
    | .call f' child =>
      match ← advance fuel child none with
      | .yielded e cs => pure (.yielded e (f' :: cs))
      | .returned v => advance fuel f' v

/-- `Generator.send` (`Coroutine.scala:114-125`) on a frame chain: resume the
delegate (the tail) first; when it returns, drop it and advance this frame with
its result. -/
def send (fuel : Nat) : Config → Option Bool → Option Outcome
  | [], _ => none
  | [f], response => advance fuel f response
  | f :: rest, response => do
    match ← send fuel rest response with
    | .yielded e cs => pure (.yielded e (f :: cs))
    | .returned v => advance fuel f v

/-- Fuel for `advance`; the programs here nest at most 4 generators deep. -/
def defaultFuel : Nat := 64

/-- The coroutine step: given the response to the last emitted test (`none`
after a command, or on the first activation of a fresh configuration), produce
the next emitted event and configuration, or the return value. `none` =
Scala exception (or fuel exhaustion). -/
def next (c : Config) (response : Option Bool) : Option Outcome :=
  send defaultFuel c response

/-- `GsMatchHeads.matcherController(k)` as started by
`compileMatcher(unit = false)` (`GsMatchHeads.scala:198-202`): a fresh frame at
site 0. The table's `start` row is `next matcherInitial none`. -/
def matcherInitial (k : Nat := 8) : Config := [.matcherController k none none none 0]

/-- `GsDualFlags.dualFlagController(k)` as started by
`compileDualFlags(unit = false)` (`GsDualFlags.scala:314-320`). -/
def flagsInitial (k : Nat := 8) : Config := [.flagController "dual_flag_controller" k "TextOrigin" 0]

/-! ## Replaying `compileController` against an exported table -/

/-- One construction state: its pending event, configuration, and the table row
(class) it belongs to. -/
structure Visit where
  event : Event
  config : Config
  row : Nat
  deriving Repr

instance : Inhabited Visit := ⟨⟨.halt, [], 0⟩⟩

/-- The responses `compileController` explores after `event`
(`GsProgram.scala:320`). -/
def responsesFor (tests : List String) (event : Event) : List (Option Bool) :=
  if tests.contains event.op then [some false, some true] else [none]

/-- Reproduce the BFS of `compileController` (`GsProgram.scala:311-343`) from
`initial`, walking `program` alongside: construction state `i + 1` is
`order[i]`, paired with the row reached by the same response path. Fails if the
coroutine and the table disagree on an event, on a return (↦ row `0`), or if a
configuration would have to belong to two rows. -/
def explore (program : Program) (tests : List String) (initial : Config)
    (maxStates : Nat := 10000) : Except String (Array Visit) := do
  let firstVisit ← match next initial none with
    | some (.yielded e c) => pure (Visit.mk e c program.start)
    | _ => throw "the controller does not yield"
  let mut order : Array Visit := #[firstVisit]
  let mut index : Std.HashMap Config Nat := (∅ : Std.HashMap Config Nat).insert firstVisit.config 0
  let mut cursor := 0
  for _ in [0:maxStates] do
    if cursor < order.size then
      let v := order[cursor]!
      let some row := program.code[v.row]? | throw s!"row {v.row} missing"
      if row.event != v.event then
        throw s!"state {cursor + 1}: coroutine emits {repr v.event}, row {v.row} has {repr row.event}"
      let rs := responsesFor tests v.event
      if rs.length != row.targets.length then throw s!"row {v.row}: arity mismatch"
      for (r, t) in rs.zip row.targets do
        match next v.config r with
        | none => throw s!"state {cursor + 1}: the coroutine failed on {repr r}"
        | some (.returned _) =>
          if t != 0 then throw s!"state {cursor + 1}: returned but row target is {t}"
        | some (.yielded e c) =>
          match index[c]? with
          | some j =>
            let w := order[j]!
            if w.event != e || w.row != t then
              throw s!"state {cursor + 1}: configuration of state {j + 1} reached as row {t}, was row {w.row}"
          | none =>
            index := index.insert c order.size
            order := order.push ⟨e, c, t⟩
      cursor := cursor + 1
  if cursor < order.size then throw "watchdog exceeded"
  return order

/-- The rows in order of first occurrence along the construction states. -/
def firstOccurrences (order : Array Visit) : List Nat :=
  (order.foldl (fun (acc : Array Nat) v => if acc.contains v.row then acc else acc.push v.row) #[]).toList

/-- `minimize` numbers classes by first occurrence (`GsProgram.scala:240-244`):
the rows first appear in the order `1, 2, …, code.length - 1`. -/
def firstOccurrenceOk (program : Program) (order : Array Visit) : Bool :=
  firstOccurrences order == List.range' 1 (program.code.length - 1)

/-- The canonical representative configuration of row `r`: the configuration of
the first construction state in class `r` (`none` for the sink `0`). -/
def rowConfig (order : Array Visit) (r : Nat) : Option Config :=
  (order.find? (·.row == r)).map (·.config)

/-- Summary: number of construction states (sink included, i.e. the Scala
`constructionStates`), and whether the first-occurrence numbering holds. -/
def summary (program : Program) (tests : List String) (initial : Config) : Except String (Nat × Bool) := do
  let order ← explore program tests initial
  return (order.size + 1, firstOccurrenceOk program order)

open PalPeg.ScaGsTables in
/-- info: Except.ok (875, true) -/
#guard_msgs in
#eval summary matcherProgram matchTests matcherInitial

open PalPeg.ScaGsTables in
/-- info: Except.ok (1176, true) -/
#guard_msgs in
#eval summary flagsProgram tests flagsInitial

end PalPeg.ScaGsCoroutine
