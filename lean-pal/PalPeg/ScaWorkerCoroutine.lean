import PalPeg.ScaWindowWorker
import PalPeg.ScaGsCert

/-!
# The window worker run by its coroutine instead of its table

`ScaWindowWorker.step` fetches the ROM row at `pc`, applies its effect to the heads, registers,
flags and faults, and jumps to `yes`/`no` on the row's decision. `ScaGsCert` shows (by
certificate) that the compiled table simulates the head-program coroutine row by row. This file
lifts that simulation to the worker.

* `step_eq`: the table step is `effect` (everything except the control) followed by the pc update
  on `decision`. Both are copies of `step`'s code; the equation is `rfl`.
* `CoWorker`: the same worker with its control replaced by a coroutine configuration and its
  pending event (`Ctl`). Its step applies the same `effect`, then resumes the coroutine with
  `next`, answering a test with the same `decision`.
* `rel_step` / `rel_service` / `rel_start` / `rel_arrive` / `rel_resetFlags` / `rel_mark`:
  under a certified coroutine worker, the relation `Rel` (all non-control fields equal, control
  `Sim`-related to the row) is preserved by every worker operation.

**What the control does not determine.** A table row carries more than its event: `fieldsAt`
(`ScaWindowWorker.lean:202-258`) decodes reader colours, move deltas, copy suppression and the
distance-register transfers from the liveness sets of the row's successors, and the fall-through
target `row.targets.headD state` from the row index itself. These are functions of the row, not
of the coroutine's `(config, event)`. So the coroutine worker reads its `Fields` from a ROM
indexed by its own control (`CoWorker.rom`), and `Certified` requires that ROM to agree with the
table on every `Sim`-related pair. `certRom` builds such a ROM from a certificate; it agrees when
the certificate is functional (`certFunctional`, not checked by `certOk`).
-/

set_option autoImplicit false

namespace PalPeg.ScaWorkerCoroutine

open PalPeg.ScaGsProgram PalPeg.ScaGsCoroutine PalPeg.ScaGsCert PalPeg.ScaWindowWorker

/-! ## The table step, factored into a decision, a non-control effect, and the pc update -/

/-- The branch decision of `step` (`ScaWindowWorker.lean:490-500`), read from the pre-state. -/
def decision (f : Fields) (s : WorkerState) : Bool :=
  let e := f.event
  let (equal, less) := compare f s
  let (a, _okA) := s.readAt f.dataLeft
  let (b, _okB) := s.readAt f.dataRight
  let available := s.availableAt f.dataLeft
  if isOp e "equal" then equal
  else if isOp e "less" then less
  else if isOp e "available" then available
  else decide (a = b)

/-- Read/assert faults and the matcher's output (`ScaWindowWorker.lean:489-511`). -/
def checks (spec : WorkerSpec) (f : Fields) (active : Bool) (s : WorkerState) : WorkerState :=
  let e := f.event
  let (equal, _less) := compare f s
  let symbolTest := active && isOp e "symbols"
  let (_a, okA) := s.readAt f.dataLeft
  let (_b, okB) := s.readAt f.dataRight
  let fault := s.fault || (symbolTest && !okA) || (symbolTest && !okB)
  let fault := fault || (active && isOp e "assert_equal" && !equal)
  let (fault, output) :=
    if spec.isFlags then (fault, s.output)
    else
      let matched := active && isOp e "match"
      let bReg := lookupFirst "B" spec.readers.colors
      (fault || (matched && s.availableAt bReg), s.output || matched)
  { s with fault, output }

/-- One reader register of the move/copy loop (`ScaWindowWorker.lean:517-528`). -/
def moveReg (f : Fields) (active : Bool) (srcPos : Option Nat) (srcRev : Option Bool)
    (s : WorkerState) (i : Nat) : WorkerState :=
  let p := s.data.getD i 0
  let r := s.reverse.getD i false
  let raw := f.dataDelta.getD i 0
  let δ := if r then -raw else raw
  let moving := active && δ ≠ 0
  let s := { s with fault := s.fault || (moving && !s.canMoveTo p δ),
                    data := if moving then s.data.set i ((p : Int) + δ).toNat else s.data }
  let copying := active && isOp f.event "copy" && f.dataTarget = some i
  match copying, srcPos, srcRev with
  | true, some q, some rv => { s with data := s.data.set i q, reverse := s.reverse.set i rv }
  | _, _, _ => s

/-- Head moves and copies (`ScaWindowWorker.lean:515-528`); the copy source is a snapshot. -/
def moves (spec : WorkerSpec) (f : Fields) (active : Bool) (s : WorkerState) : WorkerState :=
  let srcPos := f.dataSource.map fun j => s.data.getD j 0
  let srcRev := f.dataSource.map fun j => s.reverse.getD j false
  (List.range spec.readers.registers).foldl (moveReg f active srcPos srcRev) s

/-- Flag push / halt (`ScaWindowWorker.lean:530-534`). -/
def finish (spec : WorkerSpec) (f : Fields) (active : Bool) (s : WorkerState) : WorkerState :=
  if spec.isFlags then
    let s := if active && isOp f.event "flag" then { s with flags := f.bit :: s.flags } else s
    if active && isOp f.event "halt" then { s with mode := .done } else s
  else { s with fault := s.fault || (active && isOp f.event "halt") }

/-- Everything `step` does besides reading and writing `pc`. -/
def effect (spec : WorkerSpec) (f : Fields) (active : Bool) (s : WorkerState) : WorkerState :=
  finish spec f active (moves spec f active (execute f active (checks spec f active s)))

/-- `step` is: fetch the row at `pc`, apply `effect`, then (if active) jump on `decision`. -/
theorem step_eq (w : Worker) (active : Bool) (s : WorkerState) :
    step w active s =
      (let f := w.fields s.pc
       let s' := effect w.spec f active s
       if active then { s' with pc := if decision f s then f.yes else f.no } else s') :=
  rfl

/-- The `start` mapping of a flag worker (`ScaWindowWorker.lean:462-467`). -/
def flagsStartMapping : List (Pair × Option (DistKey × Int)) :=
  [(("Lower", "Upper"), some (.h, -1)),
   (("Origin", "OriginalEnd"), some (.length, -1)),
   (("Origin", "Upper"), some (.length, -1)),
   (("OriginalEnd", "Lower"), some (.h, 1)),
   (("OriginalEnd", "TextOrigin"), some (.length, 1)),
   (("OriginalEnd", "Upper"), none)]

/-- The `start` mapping of a matcher (`ScaWindowWorker.lean:473`). -/
def matcherStartMapping : List (Pair × Option (DistKey × Int)) :=
  [(("Origin", "Tail"), some (.length, -1))]

/-- Everything `start` does besides setting `pc` and `mode` (`ScaWindowWorker.lean:453-473`). -/
def startBody (w : Worker) (enabled : Bool) (s : WorkerState) : WorkerState :=
  if w.spec.isFlags then
    let s := { s with fault := s.fault || (enabled && decide (s.mode = .run)) }
    let b := s.begin
    let e := s.end
    let s := rawStart w "Origin" b false enabled s
    let s := rawStart w "TextOrigin" e true enabled s
    let s := rawStart w "OriginalEnd" b true enabled s
    let s := initializeValues w.spec flagsStartMapping enabled s
    if enabled then { s with flags := [] } else s
  else
    let e := s.end
    let s := rawStart w "Origin" e true enabled s
    let s := rawStart w "Tail" e false enabled s
    initializeValues w.spec matcherStartMapping enabled s

/-- `start` is `startBody`, then (if enabled) `pc := program.start` and `mode := run`. -/
theorem start_eq (w : Worker) (enabled : Bool) (s : WorkerState) :
    start w enabled s =
      (let s' := startBody w enabled s
       if enabled then { s' with pc := w.spec.program.start, mode := .run } else s') :=
  rfl

/-! ## The effects neither read nor write `pc` -/

/-- `g` commutes with overwriting `pc`: it does not read `pc`, and leaves it unchanged. -/
def PcFree (g : WorkerState → WorkerState) : Prop :=
  ∀ s p, g { s with pc := p } = { g s with pc := p }

theorem PcFree.comp {g h : WorkerState → WorkerState} (hg : PcFree g) (hh : PcFree h) :
    PcFree (fun s => g (h s)) := by
  intro s p
  simp only [hh s p, hg (h s) p]

/-- `g` reads a value `r s` that does not depend on `pc`, then acts by a pc-free map. -/
theorem PcFree.read {β : Type} (r : WorkerState → β) (hr : ∀ s p, r { s with pc := p } = r s)
    (g : β → WorkerState → WorkerState) (hg : ∀ b, PcFree (g b)) :
    PcFree (fun s => g (r s) s) := by
  intro s p
  simp only [hr s p, hg (r s) s p]

theorem foldl_pcFree {α : Type} (g : WorkerState → α → WorkerState)
    (hg : ∀ a, PcFree (fun s => g s a)) (l : List α) : PcFree (fun s => l.foldl g s) := by
  induction l with
  | nil => intro s p; rfl
  | cons a l ih =>
    intro s p
    have hstep : g { s with pc := p } a = { g s a with pc := p } := hg a s p
    simp only [List.foldl_cons, hstep]
    exact ih (g s a) p

theorem decision_setPc (f : Fields) (s : WorkerState) (p : Nat) :
    decision f { s with pc := p } = decision f s := rfl

theorem checks_pcFree (spec : WorkerSpec) (f : Fields) (active : Bool) :
    PcFree (checks spec f active) := fun _ _ => rfl

theorem execute_pcFree (f : Fields) (enabled : Bool) : PcFree (execute f enabled) := by
  intro s p; cases enabled <;> rfl

theorem moveReg_pcFree (f : Fields) (active : Bool) (srcPos : Option Nat) (srcRev : Option Bool)
    (i : Nat) : PcFree (fun s => moveReg f active srcPos srcRev s i) := by
  intro s p
  simp only [moveReg]
  split <;> rfl

theorem moves_pcFree (spec : WorkerSpec) (f : Fields) (active : Bool) :
    PcFree (moves spec f active) := by
  intro s p
  exact foldl_pcFree
    (moveReg f active (f.dataSource.map fun j => s.data.getD j 0)
      (f.dataSource.map fun j => s.reverse.getD j false))
    (fun i => moveReg_pcFree _ _ _ _ i) (List.range spec.readers.registers) s p

theorem finish_pcFree (spec : WorkerSpec) (f : Fields) (active : Bool) :
    PcFree (finish spec f active) := by
  intro s p
  simp only [finish]
  split <;> (try split) <;> (try split) <;> rfl

theorem effect_pcFree (spec : WorkerSpec) (f : Fields) (active : Bool) :
    PcFree (effect spec f active) :=
  (finish_pcFree spec f active).comp
    ((moves_pcFree spec f active).comp
      ((execute_pcFree f active).comp (checks_pcFree spec f active)))

theorem rawStart_pcFree (w : Worker) (head : String) (source : Nat) (reversed enabled : Bool) :
    PcFree (rawStart w head source reversed enabled) := by
  intro s p
  simp only [rawStart]
  split <;> (try split) <;> rfl

theorem initializeValues_pcFree (spec : WorkerSpec)
    (mapping : List (Pair × Option (DistKey × Int))) (enabled : Bool) :
    PcFree (initializeValues spec mapping enabled) := by
  intro s p
  cases enabled
  · rfl
  · refine foldl_pcFree _ (fun a => ?_) mapping s p
    intro s p
    obtain ⟨pair, value⟩ := a
    rcases value with _ | ⟨key, sign⟩
    · simp only
      split <;> rfl
    · simp only
      split <;> rfl

theorem startBody_pcFree (w : Worker) (enabled : Bool) : PcFree (startBody w enabled) := by
  intro s p
  cases hflags : w.spec.isFlags
  · have hpipe : PcFree (fun s : WorkerState =>
        (fun e s => initializeValues w.spec matcherStartMapping enabled
          (rawStart w "Tail" e false enabled (rawStart w "Origin" e true enabled s))) s.end s) :=
      PcFree.read (fun s => s.end) (fun _ _ => rfl)
        (fun e s => initializeValues w.spec matcherStartMapping enabled
          (rawStart w "Tail" e false enabled (rawStart w "Origin" e true enabled s))) fun e =>
        (initializeValues_pcFree _ _ _).comp
          ((rawStart_pcFree _ _ _ _ _).comp (rawStart_pcFree _ _ _ _ _))
    unfold startBody
    rw [hflags]
    exact hpipe s p
  · have hfinal : PcFree (fun s : WorkerState => if enabled then { s with flags := [] } else s) := by
      intro s p; cases enabled <;> rfl
    have hfault : PcFree (fun s : WorkerState =>
        { s with fault := s.fault || (enabled && decide (s.mode = .run)) }) := fun _ _ => rfl
    have hpipe : PcFree (fun s : WorkerState =>
        (fun (be : Nat × Nat) s =>
          (fun s : WorkerState => if enabled then { s with flags := [] } else s)
            (initializeValues w.spec flagsStartMapping enabled
              (rawStart w "OriginalEnd" be.1 true enabled
                (rawStart w "TextOrigin" be.2 true enabled
                  (rawStart w "Origin" be.1 false enabled s))))) (s.begin, s.end) s) :=
      PcFree.read (fun s => (s.begin, s.end)) (fun _ _ => rfl)
        (fun (be : Nat × Nat) s =>
          (fun s : WorkerState => if enabled then { s with flags := [] } else s)
            (initializeValues w.spec flagsStartMapping enabled
              (rawStart w "OriginalEnd" be.1 true enabled
                (rawStart w "TextOrigin" be.2 true enabled
                  (rawStart w "Origin" be.1 false enabled s))))) fun be =>
        hfinal.comp ((initializeValues_pcFree _ _ _).comp ((rawStart_pcFree _ _ _ _ _).comp
          ((rawStart_pcFree _ _ _ _ _).comp (rawStart_pcFree _ _ _ _ _))))
    unfold startBody
    rw [hflags]
    exact (hpipe.comp hfault) s p

theorem arrive_pcFree (w : Worker) (c : Fin 2) : PcFree (arrive w c) := by
  intro s p
  simp only [arrive]
  split <;> rfl

theorem resetFlags_pcFree (w : Worker) (enabled : Bool) : PcFree (resetFlags w enabled) := by
  intro s p; cases enabled <;> rfl

theorem mark_pcFree (w : Worker) (enabled : Bool) : PcFree (mark w enabled) := by
  intro s p; cases enabled <;> rfl

/-- The table step on a state whose `pc` is `r`: the effect of row `r`, then the jump. -/
theorem step_setPc (w : Worker) (active : Bool) (b : WorkerState) (r : Nat) :
    step w active { b with pc := r } =
      { effect w.spec (w.fields r) active b with
        pc := if active then (if decision (w.fields r) b then (w.fields r).yes else (w.fields r).no)
              else r } := by
  have heffect := effect_pcFree w.spec (w.fields r) active b r
  cases active
  · exact heffect
  · calc step w true { b with pc := r }
        = { effect w.spec (w.fields r) true { b with pc := r } with
            pc := if decision (w.fields r) b then (w.fields r).yes else (w.fields r).no } := rfl
      _ = _ := by rw [heffect]; rfl

/-! ## The coroutine worker -/

/-- The control of the coroutine worker, in place of the table's `pc`. -/
inductive Ctl where
  /-- Suspended at `config` after emitting `event`: the instruction executed next. -/
  | pending (config : Config) (event : Event)
  /-- The coroutine returned `value` (the table sits in its sink row `0`). -/
  | returned (value : Value)
  /-- `next` failed (a Scala exception, or fuel exhaustion). -/
  | failed
  deriving DecidableEq, Repr

/-- The control after one coroutine step. -/
def Ctl.ofOutcome : Option Outcome → Ctl
  | some (.yielded e c) => .pending c e
  | some (.returned v) => .returned v
  | none => .failed

/-- The response the coroutine is resumed with after emitting `e`: the decision when `e` is a
test (in the sense of `tests`, as `compileController` explores it), `none` after a command. -/
def respond (tests : List String) (e : Event) (decided : Bool) : Option Bool :=
  if tests.contains e.op then some decided else none

/-- Resume a pending coroutine with the answer to its event. A returned or failed coroutine
stays where it is. -/
def Ctl.resume (tests : List String) (decided : Bool) : Ctl → Ctl
  | .pending c e => Ctl.ofOutcome (next c (respond tests e decided))
  | k => k

/-- A worker whose control is a coroutine. `rom` gives the decoded row fields executed at each
control (see the module docstring for why they are not a function of the event alone). -/
structure CoWorker where
  spec : WorkerSpec
  tests : List String
  initial : Config
  rom : Ctl → Fields

/-- A coroutine worker's state: the table worker's non-control fields, and the control.
`body.pc` is never read and never written (`PcFree`); it is `0` initially. -/
structure CoState where
  body : WorkerState
  ctl : Ctl

/-- A worker with no ROM, for the operations that only read `spec` (`arrive`, `start`, …). -/
def specWorker (spec : WorkerSpec) : Worker := { spec, table := #[] }

namespace CoWorker

variable (cw : CoWorker)

/-- The initial state: the table worker's initial fields, the coroutine at its first yield. -/
def initialState : CoState :=
  { body := { WorkerState.initial cw.spec with pc := 0 },
    ctl := Ctl.ofOutcome (next cw.initial none) }

/-- One step: the table's `effect` for the current control, then resume on the `decision`. -/
def step (active : Bool) (t : CoState) : CoState :=
  let f := cw.rom t.ctl
  let body := effect cw.spec f active t.body
  if active then { body, ctl := t.ctl.resume cw.tests (decision f t.body) }
  else { body, ctl := t.ctl }

/-- `quantum` steps, each with `active := mode = run` read afresh (as `ScaWindowWorker.service`). -/
def service (t : CoState) : CoState :=
  (List.range cw.spec.quantum).foldl (fun t _ => cw.step (decide (t.body.mode = .run)) t) t

def arrive (c : Fin 2) (t : CoState) : CoState :=
  { t with body := ScaWindowWorker.arrive (specWorker cw.spec) c t.body }

def resetFlags (enabled : Bool) (t : CoState) : CoState :=
  { t with body := ScaWindowWorker.resetFlags (specWorker cw.spec) enabled t.body }

def mark (enabled : Bool) (t : CoState) : CoState :=
  { t with body := ScaWindowWorker.mark (specWorker cw.spec) enabled t.body }

/-- `start`: the table's `startBody`; if enabled, `mode := run` and the coroutine restarts. -/
def start (enabled : Bool) (t : CoState) : CoState :=
  let body := startBody (specWorker cw.spec) enabled t.body
  if enabled then { body := { body with mode := .run }, ctl := Ctl.ofOutcome (next cw.initial none) }
  else { body, ctl := t.ctl }

theorem step_body (active : Bool) (t : CoState) :
    (cw.step active t).body = effect cw.spec (cw.rom t.ctl) active t.body := by
  cases active <;> rfl

theorem step_ctl (active : Bool) (t : CoState) :
    (cw.step active t).ctl =
      if active then t.ctl.resume cw.tests (decision (cw.rom t.ctl) t.body) else t.ctl := by
  cases active <;> rfl

end CoWorker

/-! ## The simulation relation and its hypotheses -/

/-- The coroutine control is simulated by table row `r`. A returned coroutine is simulated by the
sink row `0` only; a failed one by no row. -/
def SimCtl (vs : List Entry) : Ctl → Nat → Prop
  | .pending c e, r => Sim vs c e r
  | .returned _, r => r = 0
  | .failed, _ => False

/-- The table state `s` and the coroutine state `t` agree on every field but the control, and
the controls are simulated. -/
structure Rel (vs : List Entry) (s : WorkerState) (t : CoState) : Prop where
  agree : s = { t.body with pc := s.pc }
  sim : SimCtl vs t.ctl s.pc

/-- The coroutine worker `cw` runs the coroutine that `certificate` certifies against the table
of `spec`. -/
structure Certified (spec : WorkerSpec) (cw : CoWorker) (certificate : List Entry) : Prop where
  specEq : cw.spec = spec
  certOk : certOk spec.program cw.tests cw.initial certificate = true
  /-- A test for the coroutine is a two-way test for the table (`isTest`). The converse is not
  needed: a table test with one successor jumps there on both answers. -/
  coroutineTestsAreTableTests : ∀ e : Event, cw.tests.contains e.op = true → isTest e = true
  romAtPending : ∀ c e r, Sim certificate c e r → cw.rom (.pending c e) = (Worker.ofSpec spec).fields r
  romAtReturned : ∀ v, cw.rom (.returned v) = (Worker.ofSpec spec).fields 0
  /-- Row `0` (the sink of returned coroutines) has no successor, so the table stays there. -/
  sinkRowHasNoTargets : ∀ row, spec.program.code[0]? = some row → row.targets = []

theorem Rel.mode_eq {vs : List Entry} {s : WorkerState} {t : CoState} (hrel : Rel vs s t) :
    s.mode = t.body.mode := by
  have hmode := congrArg WorkerState.mode hrel.agree
  exact hmode

/-- Every observer of `WorkerOps` agrees. -/
theorem Rel.observers_eq {vs : List Entry} {s : WorkerState} {t : CoState} (hrel : Rel vs s t) :
    s.output = t.body.output ∧ s.mode = t.body.mode ∧ s.flags = t.body.flags ∧
      s.fault = t.body.fault := by
  have houtput := congrArg WorkerState.output hrel.agree
  have hmode := congrArg WorkerState.mode hrel.agree
  have hflags := congrArg WorkerState.flags hrel.agree
  have hfault := congrArg WorkerState.fault hrel.agree
  exact ⟨houtput, hmode, hflags, hfault⟩

/-- A pc-free operation applied to both sides preserves `Rel`. -/
theorem Rel.bodyOp {vs : List Entry} {s : WorkerState} {t : CoState} (hrel : Rel vs s t)
    {g : WorkerState → WorkerState} (hg : PcFree g) : Rel vs (g s) { t with body := g t.body } := by
  have hkey : g s = { g t.body with pc := s.pc } :=
    (congrArg g hrel.agree).trans (hg t.body s.pc)
  have hpc : (g s).pc = s.pc := by rw [hkey]
  exact ⟨by rw [hpc]; exact hkey, by rw [hpc]; exact hrel.sim⟩

/-! ## The table's rows, targets and sink -/

theorem ofSpec_spec (spec : WorkerSpec) : (Worker.ofSpec spec).spec = spec := rfl

/-- The ROM of `Worker.ofSpec` at a row of the program. -/
theorem fields_ofSpec (spec : WorkerSpec) {r : Nat} {row : Row}
    (hrow : spec.program.code[r]? = some row) :
    (Worker.ofSpec spec).fields r = fieldsAt spec (liveReaders spec) (liveDistances spec) r row := by
  simp [Worker.fields, Worker.ofSpec, List.getElem?_zipIdx, hrow]

/-- The table's jump targets are the row's successors (`fieldsAt`, `ScaWindowWorker.lean:204-205`). -/
theorem fieldsAt_yes (spec : WorkerSpec) (rb : Array (List String)) (db : Array (List Pair))
    (r : Nat) (row : Row) :
    (fieldsAt spec rb db r row).yes =
      if isTest row.event then row.targets.getD 1 (row.targets.headD r) else row.targets.headD r :=
  rfl

theorem fieldsAt_no (spec : WorkerSpec) (rb : Array (List String)) (db : Array (List Pair))
    (r : Nat) (row : Row) : (fieldsAt spec rb db r row).no = row.targets.headD r :=
  rfl

theorem fieldsAt_event (spec : WorkerSpec) (rb : Array (List String)) (db : Array (List Pair))
    (r : Nat) (row : Row) : (fieldsAt spec rb db r row).event = row.event :=
  rfl

/-- The sink row jumps to itself. -/
theorem sink_targets (spec : WorkerSpec)
    (hsink : ∀ row, spec.program.code[0]? = some row → row.targets = []) (decided : Bool) :
    (if decided then ((Worker.ofSpec spec).fields 0).yes else ((Worker.ofSpec spec).fields 0).no)
      = 0 := by
  cases hcode : spec.program.code[0]? with
  | some row =>
    rw [fields_ofSpec spec hcode, fieldsAt_yes, fieldsAt_no, hsink row hcode]
    cases decided <;> simp
  | none =>
    have hnil : spec.program.code = [] := by
      simpa [List.getElem?_eq_none_iff] using hcode
    cases decided <;> simp [Worker.fields, Worker.ofSpec, hnil]

/-- One response of a certified configuration: the coroutine's successor is simulated by the
table's target on that response. -/
theorem simCtl_response {program : Program} {tests : List String} {initial : Config}
    {vs : List Entry} (hcert : certOk program tests initial vs = true)
    {c : Config} {e : Event} {r : Nat} (hsim : Sim vs c e r) {row : Row}
    (hrow : program.code[r]? = some row) {k : Nat} (hk : k < (responsesFor tests e).length) :
    SimCtl vs (Ctl.ofOutcome (next c ((responsesFor tests e).getD k none))) (row.targets.getD k 0) := by
  obtain ⟨row', hrow', -, -, hresp⟩ := sim_step hcert hsim
  rw [hrow] at hrow'
  cases hrow'
  rcases hresp k hk with ⟨v, hret, hzero⟩ | ⟨e', c', hyield, hsim'⟩
  · rw [hret, hzero]; rfl
  · rw [hyield]; exact hsim'

/-- **The control step.** From a certified configuration, resuming the coroutine with the
table's decision lands on a configuration simulated by the row the table jumps to. -/
theorem resume_sim {spec : WorkerSpec} {tests : List String} {initial : Config}
    {vs : List Entry} (hcert : certOk spec.program tests initial vs = true)
    (htests : ∀ e : Event, tests.contains e.op = true → isTest e = true)
    {c : Config} {e : Event} {r : Nat} (hsim : Sim vs c e r) (decided : Bool) :
    SimCtl vs ((Ctl.pending c e).resume tests decided)
      (if decided then ((Worker.ofSpec spec).fields r).yes
       else ((Worker.ofSpec spec).fields r).no) := by
  obtain ⟨row, hrow, hevent, hlen, -⟩ := sim_step hcert hsim
  rw [fields_ofSpec spec hrow, fieldsAt_yes, fieldsAt_no, hevent]
  simp only [Ctl.resume]
  unfold respond
  by_cases htest : tests.contains e.op = true
  · have hisTest : isTest e = true := htests e htest
    have hresp : responsesFor tests e = [some false, some true] := by
      unfold responsesFor; rw [if_pos htest]
    rw [hresp] at hlen
    obtain ⟨t0, t1, htargets⟩ := List.length_eq_two.mp hlen.symm
    have hk0 := simCtl_response hcert hsim hrow (k := 0) (by rw [hresp]; decide)
    have hk1 := simCtl_response hcert hsim hrow (k := 1) (by rw [hresp]; decide)
    rw [hresp, htargets] at hk0 hk1
    rw [if_pos htest, htargets, hisTest]
    cases decided
    · exact hk0
    · exact hk1
  · have hresp : responsesFor tests e = [none] := by
      unfold responsesFor; rw [if_neg htest]
    rw [hresp] at hlen
    obtain ⟨t0, htargets⟩ := List.length_eq_one_iff.mp hlen.symm
    have hk0 := simCtl_response hcert hsim hrow (k := 0) (by rw [hresp]; decide)
    rw [hresp, htargets] at hk0
    rw [if_neg htest, htargets]
    cases decided <;> cases isTest e <;> exact hk0

/-- The ROM of a certified coroutine worker executes the table's row. -/
theorem Certified.rom_eq {spec : WorkerSpec} {cw : CoWorker} {vs : List Entry}
    (hcw : Certified spec cw vs) {k : Ctl} {r : Nat} (hsim : SimCtl vs k r) :
    cw.rom k = (Worker.ofSpec spec).fields r := by
  cases k with
  | pending c e => exact hcw.romAtPending c e r hsim
  | returned v =>
    have hr : r = 0 := hsim
    rw [hr]; exact hcw.romAtReturned v
  | failed => exact hsim.elim

/-! ## The simulation -/

section Simulation

variable {spec : WorkerSpec} {cw : CoWorker} {vs : List Entry}

/-- **One step.** In every mode (`active` or not), the table step and the coroutine step keep
the non-control fields equal and the controls simulated. When `active` and the control is
`pending`, this is `resume_sim`; when the coroutine has returned, the table stays in row `0`. -/
theorem rel_step (hcw : Certified spec cw vs) {s : WorkerState} {t : CoState}
    (hrel : Rel vs s t) (active : Bool) :
    Rel vs (ScaWindowWorker.step (Worker.ofSpec spec) active s) (cw.step active t) := by
  obtain ⟨hagree, hsim⟩ := hrel
  obtain ⟨body, ctl⟩ := t
  have hrom : cw.rom ctl = (Worker.ofSpec spec).fields s.pc := hcw.rom_eq hsim
  generalize hr : s.pc = r at hagree hsim hrom
  subst hagree
  rw [step_setPc]
  refine ⟨?_, ?_⟩
  · rw [CoWorker.step_body, hrom, hcw.specEq]
    rfl
  · rw [CoWorker.step_ctl, hrom]
    show SimCtl vs (if active then ctl.resume cw.tests (decision _ body) else ctl)
      (if active then _ else r)
    cases active
    · exact hsim
    · simp only [if_true]
      cases ctl with
      | pending c e =>
        exact resume_sim hcw.certOk hcw.coroutineTestsAreTableTests hsim _
      | returned v =>
        have hr0 : r = 0 := hsim
        subst hr0
        exact sink_targets spec hcw.sinkRowHasNoTargets _
      | failed => exact hsim.elim

/-- **One service quantum.** -/
theorem rel_service (hcw : Certified spec cw vs) {s : WorkerState} {t : CoState}
    (hrel : Rel vs s t) :
    Rel vs (ScaWindowWorker.service (Worker.ofSpec spec) s) (cw.service t) := by
  unfold ScaWindowWorker.service CoWorker.service
  rw [hcw.specEq, ofSpec_spec]
  generalize List.range spec.quantum = steps
  induction steps generalizing s t with
  | nil => exact hrel
  | cons _ steps ih =>
    simp only [List.foldl_cons]
    apply ih
    rw [hrel.mode_eq]
    exact rel_step hcw hrel _

theorem rel_arrive (hcw : Certified spec cw vs) {s : WorkerState} {t : CoState}
    (hrel : Rel vs s t) (c : Fin 2) :
    Rel vs (ScaWindowWorker.arrive (Worker.ofSpec spec) c s) (cw.arrive c t) := by
  unfold CoWorker.arrive
  rw [hcw.specEq]
  exact hrel.bodyOp (arrive_pcFree (Worker.ofSpec spec) c)

theorem rel_resetFlags (hcw : Certified spec cw vs) {s : WorkerState} {t : CoState}
    (hrel : Rel vs s t) (enabled : Bool) :
    Rel vs (ScaWindowWorker.resetFlags (Worker.ofSpec spec) enabled s) (cw.resetFlags enabled t) := by
  unfold CoWorker.resetFlags
  rw [hcw.specEq]
  exact hrel.bodyOp (resetFlags_pcFree (Worker.ofSpec spec) enabled)

theorem rel_mark (hcw : Certified spec cw vs) {s : WorkerState} {t : CoState}
    (hrel : Rel vs s t) (enabled : Bool) :
    Rel vs (ScaWindowWorker.mark (Worker.ofSpec spec) enabled s) (cw.mark enabled t) := by
  unfold CoWorker.mark
  rw [hcw.specEq]
  exact hrel.bodyOp (mark_pcFree (Worker.ofSpec spec) enabled)

/-- The coroutine's first yield is simulated by the table's `start` row (`sim_start`). -/
theorem simCtl_start (hcw : Certified spec cw vs) :
    SimCtl vs (Ctl.ofOutcome (next cw.initial none)) spec.program.start := by
  obtain ⟨e, c, hnext, hsim⟩ := sim_start hcw.certOk
  rw [hnext]
  exact hsim

/-- **`start`.** The table sets `pc := program.start`; the coroutine restarts from its initial
configuration. -/
theorem rel_start (hcw : Certified spec cw vs) {s : WorkerState} {t : CoState}
    (hrel : Rel vs s t) (enabled : Bool) :
    Rel vs (ScaWindowWorker.start (Worker.ofSpec spec) enabled s) (cw.start enabled t) := by
  have hbody : startBody (Worker.ofSpec spec) enabled s =
      { startBody (Worker.ofSpec spec) enabled t.body with pc := s.pc } :=
    (congrArg _ hrel.agree).trans (startBody_pcFree _ enabled t.body s.pc)
  rw [start_eq]
  unfold CoWorker.start
  rw [hcw.specEq]
  cases enabled
  · simp only [Bool.false_eq_true, if_false]
    have hpc : (startBody (Worker.ofSpec spec) false s).pc = s.pc := by rw [hbody]
    refine ⟨?_, ?_⟩
    · rw [hpc]; exact hbody
    · rw [hpc]; exact hrel.sim
  · simp only [if_true]
    refine ⟨?_, ?_⟩
    · rw [hbody]; rfl
    · exact simCtl_start hcw

/-- The initial states are related. -/
theorem rel_initial (hcw : Certified spec cw vs) :
    Rel vs (WorkerState.initial spec) cw.initialState := by
  refine ⟨?_, ?_⟩
  · unfold CoWorker.initialState
    rw [hcw.specEq]
  · exact simCtl_start hcw

/-- The sink, precisely: once the coroutine has returned, the table sits in row `0`, and an
active step there keeps it in row `0` and executes row `0`'s event. When that row is `halt`
(as in `matcherProgram` and `flagsProgram`), a flag worker becomes `done` and a matcher
faults. -/
theorem step_sink (hsinkRow : spec.program.code[0]? = some { event := .halt, targets := [] })
    (s : WorkerState) (hpc : s.pc = 0) :
    (ScaWindowWorker.step (Worker.ofSpec spec) true s).pc = 0 ∧
      (spec.isFlags = true → (ScaWindowWorker.step (Worker.ofSpec spec) true s).mode = .done) ∧
      (spec.isFlags = false → (ScaWindowWorker.step (Worker.ofSpec spec) true s).fault = true) := by
  have hs : s = { s with pc := 0 } := by rw [← hpc]
  rw [hs, step_setPc, fields_ofSpec spec hsinkRow, ofSpec_spec]
  refine ⟨?_, ?_, ?_⟩
  · simp [fieldsAt_yes, fieldsAt_no]
  · intro hflags
    simp [effect, finish, hflags, fieldsAt_event, isOp, Event.op]
  · intro hflags
    simp [effect, finish, hflags, fieldsAt_event, isOp, Event.op]

end Simulation

/-! ## A ROM read off a certificate -/

/-- The fields of the row the certificate assigns to a pending configuration (its first entry
with that configuration and event); the sink row otherwise. -/
def certRom (w : Worker) (vs : List Entry) : Ctl → Fields
  | .pending c e =>
    match vs.find? (fun v => v.config == c && v.event == e) with
    | some v => w.fields v.row
    | none => w.fields 0
  | _ => w.fields 0

/-- Every configuration and event has one row in the certificate. `certOk` does not check this;
the certificates generated from `explore` have pairwise distinct configurations. -/
def certFunctional (vs : List Entry) : Bool :=
  vs.all fun v => vs.all fun v' =>
    !(v.config == v'.config && v.event == v'.event) || v.row == v'.row

/-- The coroutine worker of a certificate. -/
def certWorker (spec : WorkerSpec) (tests : List String) (initial : Config) (vs : List Entry) :
    CoWorker :=
  { spec, tests, initial, rom := certRom (Worker.ofSpec spec) vs }

theorem certRom_pending {w : Worker} {vs : List Entry} (hfunctional : certFunctional vs = true)
    {c : Config} {e : Event} {r : Nat} (hsim : Sim vs c e r) :
    certRom w vs (.pending c e) = w.fields r := by
  obtain ⟨v, hv, hconfig, hevent, hrow⟩ := hsim
  have hfound : (vs.find? (fun v => v.config == c && v.event == e)).isSome := by
    rw [List.find?_isSome]
    exact ⟨v, hv, by simp [hconfig, hevent]⟩
  obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.mp hfound
  have hmatch := List.find?_some hv'
  have hmem := List.mem_of_find?_eq_some hv'
  simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
  simp only [certFunctional, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq, beq_iff_eq] at hfunctional
  have hsame : v'.row = v.row := by
    rcases hfunctional v' hmem v hv with (hne | hne) | heq
    · exact absurd (hmatch.1.trans hconfig.symm) hne
    · exact absurd (hmatch.2.trans hevent.symm) hne
    · exact heq
  simp only [certRom, hv', hsame, hrow]

theorem certified_certWorker {spec : WorkerSpec} {tests : List String} {initial : Config}
    {vs : List Entry} (hcert : certOk spec.program tests initial vs = true)
    (hfunctional : certFunctional vs = true)
    (htests : ∀ e : Event, tests.contains e.op = true → isTest e = true)
    (hsink : ∀ row, spec.program.code[0]? = some row → row.targets = []) :
    Certified spec (certWorker spec tests initial vs) vs where
  specEq := rfl
  certOk := hcert
  coroutineTestsAreTableTests := htests
  romAtPending := fun _ _ _ hsim => certRom_pending hfunctional hsim
  romAtReturned := fun _ => rfl
  sinkRowHasNoTargets := hsink

/-! ## The concrete GS workers -/

theorem tests_areTableTests :
    ∀ e : Event, ScaGsProgram.tests.contains e.op = true → isTest e = true := by
  intro e
  cases e <;> simp [ScaGsProgram.tests, Event.op, isTest]

theorem matchTests_areTableTests :
    ∀ e : Event, matchTests.contains e.op = true → isTest e = true := by
  intro e
  cases e <;> simp [matchTests, Event.op, isTest]

theorem matcherWorker_sinkRow :
    ScaGsTables.matcherWorker.program.code[0]? = some { event := .halt, targets := [] } := rfl

theorem flagsWorker_sinkRow :
    ScaGsTables.flagsWorker.program.code[0]? = some { event := .halt, targets := [] } := rfl

theorem sinkRowHasNoTargets_of {spec : WorkerSpec}
    (hsinkRow : spec.program.code[0]? = some { event := .halt, targets := [] }) :
    ∀ row, spec.program.code[0]? = some row → row.targets = [] := by
  intro row hrow
  rw [hsinkRow] at hrow
  cases hrow
  rfl

end PalPeg.ScaWorkerCoroutine
