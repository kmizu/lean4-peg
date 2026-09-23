import PalPeg.ScaHeadVM
import PalPeg.ScaWorkerRegs
import PalPeg.ScaGsCertFunctional
import PalPeg.ScaWindowInstance

/-!
# The real flag worker, operation by operation, as `DualFlagVM`

`ScaHeadVM.flags_step_certified` relates *one* active step of the coroutine flag worker to one
`stepFlags` of the logical head VM. This file lifts it to the operations the window controller
applies to the real table worker `ScaWindowInstance.flagsW` (`flagsOps`), so that later proofs
reason about `stepFlags` alone.

## The link

`Link bg b s v` (the real worker state `s` encodes `DualFlagVM` `v` on the segment
`[bg, bg + b)`) bundles

* a coroutine state `t` with `Rel flagsCert s t` (the certified table ↔ coroutine simulation,
  `ScaWorkerCoroutine`) and `FlagRel` for the readers live at the table row `s.pc`
  (`ScaHeadVM`);
* the distance-register invariant `ScaWorkerRegs.Inv` whose ghost positions **are** the VM
  positions `v.pos` (this discharges the register hypothesis `hregs` of every step);
* `end = |text|`, and the mode: running, or done with the VM halted.

`Base s` is what holds of the worker at every time (`Rel`, some register invariant, register
lengths, `end = |text|`).

## Results

* `step_pending`, `step_returned`, `step_inactive`: one worker step.
* `service_link` / `service_modeDone` (1): a service quantum from a linked state runs the VM
  `n ≤ 32768` steps (`iterFlags n v = some v'`), keeps the link with `v'`, keeps the fault, and the
  worker is done iff it was done or `n < 32768` (then `v'` is `flagsDone`); the flag stack is
  `v'.flags.reverse`. So `n = min 32768 (steps to halt)`. The one boundary: a VM that halts at
  exactly step `32768` is `flagsDone` while the worker is still running; its halt row runs as the
  first step of the next quantum. The only run hypothesis is `RunsFor 32768 v`: the VM does not
  get stuck before halting (`∀ i < 32768, iterFlags i v = some u → ¬ u.flagsDone →
  (stepFlags u).isSome`).
* `arrive_link`, `mark_link`, `start_link`, `release_link` (2): `start true` then `mark true`
  from any `Base` state links the worker to `releaseVM s = flagsInitialVM (flagWord text begin b)
  (b - h) b ctl0` with `b = end - begin` and `h` the worker's `hKey` before the release
  (`Upper = b`, `Lower = b - h`, `SCA_GS_MAPPING.md` §0); `resetFlags_base`, `arrive_base`, …:
  `Base` is kept.
* `stageRound_flags` / `tick_release`, `tick_running`, `tick_birth`, `tick_idle` (3): the flag
  worker's share of `ScaWindowPal.stageRound` (arrive, resetFlags, start, mark, service), in the
  four cases the controller produces (`advance` never sets `birth` and `release` together).

Proved on the way, with no hypothesis: no reader is live at the sink row (`live_zero`); no move
batch of the flag table moves a head twice (`flags_moveNodup_rows`, by the kernel), so the
ghost's `headStep` is the VM's `movePos`; the certificate gives one row per control
(`simCtl_unique`).

## Hypotheses that remain

* `ReaderFacts`: facts of the reader liveness `liveReaders` and the reader colouring at the rows
  the certificate reaches (post-fixpoint, colouring proper on after-sets, live heads coloured,
  the start row's live readers among `Origin`/`TextOrigin`/`OriginalEnd`). These are finite facts
  of the table. Evaluated (`#eval`, not a proof) they hold at all 492 rows, and the start row's
  live readers are exactly those three. Unlike the distance facts
  (`ScaWorkerRegs.flags_tableFacts`) they are not yet checked by a certificate; the same route
  applies (`ScaWorkerRegs.fixpoint_spec` with a reader certificate).
* The run hypothesis `RunsFor` above.
-/

set_option autoImplicit false

namespace PalPeg.ScaFlagsLink

open PalPeg.ScaGsProgram PalPeg.ScaGsCoroutine PalPeg.ScaGsCert PalPeg.ScaWindowWorker
  PalPeg.ScaWorkerCoroutine PalPeg.ScaHeadVM PalPeg.ScaGsCertData PalPeg.ScaGsCertFunctional
  PalPeg.ScaWindowInstance

/-! ## The flag worker's constants -/

/-- The flag worker's table data (`ScaGsTables.flagsWorker`). -/
abbrev fspec : WorkerSpec := ScaGsTables.flagsWorker

/-- The coroutine flag worker certified against the table (`flags_certified`). -/
abbrev fcw : CoWorker := certWorker ScaGsTables.flagsWorker tests flagsInitial flagsCert

/-- The readers live before table row `r` (`GsHeadLiveness.analyzeReaders`). -/
abbrev live (r : Nat) : List String := (liveReaders ScaGsTables.flagsWorker).getD r []

/-- The control the coroutine starts from (`CoWorker.start`). -/
abbrev ctl0 : Ctl := Ctl.ofOutcome (next flagsInitial none)

/-- The flags quantum, `32768` (`GsBatchClock.DEFAULT_BATCH.flags`). -/
abbrev quantum : Nat := ScaGsTables.flagsWorker.quantum

theorem quantum_eq : quantum = 32768 := rfl

theorem flagsW_eq : flagsW = Worker.ofSpec fspec := rfl

/-! ## `n` steps of `DualFlagVM` -/

/-- `n` steps of the flags head VM (as `ScaHeadGen.iterStep` for the matcher). -/
def iterFlags : ℕ → HVM → Option HVM
  | 0, v => some v
  | n + 1, v => (stepFlags v).bind (iterFlags n)

theorem iterFlags_add (m n : ℕ) (v : HVM) :
    iterFlags (m + n) v = (iterFlags m v).bind (iterFlags n) := by
  induction m generalizing v with
  | zero => simp [iterFlags]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega]
    simp only [iterFlags]
    cases stepFlags v with
    | none => rfl
    | some w => simp [ih]

theorem iterFlags_succ_of_step {v v' : HVM} (hstep : stepFlags v = some v') (n : ℕ) :
    iterFlags (n + 1) v = iterFlags n v' := by
  simp only [iterFlags, hstep, Option.bind_some]

/-! ## Constant facts of the flag table -/

theorem color_origin : color fspec "Origin" = some 1 := rfl
theorem color_textOrigin : color fspec "TextOrigin" = some 2 := rfl
theorem color_originalEnd : color fspec "OriginalEnd" = some 0 := rfl

theorem fspec_isFlags : fspec.isFlags = true := rfl
theorem fspec_registers : fspec.readers.registers = 7 := rfl

theorem mem_colors_of_color {h : String} {i : Nat} (hc : color fspec h = some i) :
    (h, i) ∈ fspec.readers.colors := by
  unfold color lookupFirst at hc
  obtain ⟨p, hp, hpi⟩ := Option.map_eq_some_iff.mp hc
  have hmem := List.mem_of_find?_eq_some hp
  have hph := List.find?_some hp
  simp only [decide_eq_true_eq] at hph
  rw [← hph, ← hpi]
  exact hmem

theorem colorsBound : ColorsBound fspec := by
  intro h i hc
  have hall : ∀ p ∈ fspec.readers.colors, p.2 < fspec.readers.registers := by decide
  exact hall _ (mem_colors_of_color hc)

theorem readersNotBlind : ReadersNotBlind fspec flagBlind := by
  intro h i hc
  have hall : ∀ p ∈ fspec.readers.colors, p.1 ∉ flagBlind := by decide
  exact hall _ (mem_colors_of_color hc)

/-- The certificate assigns one row to a control (`flags_certFunctional`). -/
theorem simCtl_unique {k : Ctl} {r r' : Nat} (h : SimCtl flagsCert k r)
    (h' : SimCtl flagsCert k r') : r = r' := by
  cases k with
  | pending c e =>
    obtain ⟨v, hv, hc, he, hr⟩ := h
    obtain ⟨v', hv', hc', he', hr'⟩ := h'
    have hfun := flags_certFunctional
    simp only [certFunctional, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq, beq_iff_eq] at hfun
    rcases hfun v hv v' hv' with (hne | hne) | heq
    · exact absurd (hc.trans hc'.symm) hne
    · exact absurd (he.trans he'.symm) hne
    · rw [← hr, ← hr', heq]
  | returned val =>
    have h0 : r = 0 := h
    have h0' : r' = 0 := h'
    rw [h0, h0']
  | failed => exact h.elim

/-! ## The sink row has no live reader -/

section Sink

variable {α : Type} [DecidableEq α] (code : List Row) (transfer : Row → List α → List α)

/-- A sweep keeps the entry of a target-less row `0` whose transfer of `[]` is `[]` empty. -/
theorem sweepStep_zero (hrow0 : ∀ row, code[0]? = some row → row.targets = [] ∧ transfer row [] = [])
    (acc : Array (List α) × Bool) (hsize : acc.1.size = code.length)
    (hzero : acc.1.getD 0 [] = []) (state : Nat) :
    (ScaWorkerRegs.sweepStep code transfer acc state).1.size = code.length ∧
      (ScaWorkerRegs.sweepStep code transfer acc state).1.getD 0 [] = [] := by
  obtain ⟨bs, ch⟩ := acc
  dsimp only at hsize hzero
  unfold ScaWorkerRegs.sweepStep
  cases hrow : code[state]? with
  | none => exact ⟨hsize, hzero⟩
  | some row =>
    have hlt : state < bs.size := by
      rw [hsize]; exact (List.getElem?_eq_some_iff.mp hrow).1
    by_cases hset : setEq (transfer row (successorsUnion bs row.targets)) (bs.getD state []) = true
    · simp only [hset, if_true]
      exact ⟨hsize, hzero⟩
    · simp only [hset, Bool.false_eq_true, if_false]
      refine ⟨by simp [hsize], ?_⟩
      rw [ScaWorkerRegs.getD_set! bs hlt _ 0]
      split
      · rename_i h0
        subst h0
        obtain ⟨htargets, htransfer⟩ := hrow0 row hrow
        rw [htargets]
        exact htransfer
      · exact hzero

theorem sweep_zero (hrow0 : ∀ row, code[0]? = some row → row.targets = [] ∧ transfer row [] = [])
    (bs : Array (List α)) (hsize : bs.size = code.length) (hzero : bs.getD 0 [] = []) :
    (sweep code transfer bs).1.size = code.length ∧ (sweep code transfer bs).1.getD 0 [] = [] := by
  rw [ScaWorkerRegs.sweep_eq_foldl]
  generalize (List.range code.length).reverse = states
  suffices h : ∀ (states : List Nat) (acc : Array (List α) × Bool), acc.1.size = code.length →
      acc.1.getD 0 [] = [] →
      (states.foldl (ScaWorkerRegs.sweepStep code transfer) acc).1.size = code.length ∧
        (states.foldl (ScaWorkerRegs.sweepStep code transfer) acc).1.getD 0 [] = [] from
    h states (bs, false) hsize hzero
  intro states
  induction states with
  | nil => intro acc hs hz; exact ⟨hs, hz⟩
  | cons st sts ih =>
    intro acc hs hz
    obtain ⟨hs', hz'⟩ := sweepStep_zero code transfer hrow0 acc hs hz st
    exact ih _ hs' hz'

theorem fixpoint_zero (hrow0 : ∀ row, code[0]? = some row → row.targets = [] ∧ transfer row [] = [])
    (fuel : Nat) : (fixpoint code transfer fuel).getD 0 [] = [] := by
  suffices h : ∀ (n : Nat) (bs : Array (List α)), bs.size = code.length → bs.getD 0 [] = [] →
      (fixpoint.go code transfer n bs).getD 0 [] = [] by
    apply h
    · simp
    · simp [Array.getElem?_replicate]
      split <;> rfl
  intro n
  induction n with
  | zero => intro bs _ hz; exact hz
  | succ n ih =>
    intro bs hs hz
    obtain ⟨hs', hz'⟩ := sweep_zero code transfer hrow0 bs hs hz
    rw [fixpoint.go]
    generalize hsw : sweep code transfer bs = res at hs' hz'
    obtain ⟨bs', ch⟩ := res
    cases ch
    · exact hz'
    · exact ih bs' hs' hz'

end Sink

/-- No reader is live at the sink row `0`. -/
theorem live_zero : live 0 = [] := by
  show (fixpoint fspec.program.code readerTransfer _).getD 0 [] = []
  apply fixpoint_zero
  intro row hrow
  rw [flagsWorker_sinkRow] at hrow
  cases hrow
  exact ⟨rfl, rfl⟩

/-! ## Inactive steps change nothing -/

theorem cellStep_inactive (f : Fields) (sp : Option Nat) (sr : Option Bool) (n i p : Nat)
    (r : Bool) : cellStep f false sp sr n i p r = (p, r, false) := by
  unfold cellStep
  simp

theorem moveReg_inactive (f : Fields) (sp : Option Nat) (sr : Option Bool) (s : WorkerState)
    (i : Nat) : moveReg f false sp sr s i = s := by
  rw [moveReg_eq]
  simp only [cellStep_inactive, set_getD_self, Bool.or_false]

theorem step_inactive (w : Worker) (s : WorkerState) : step w false s = s := by
  rw [step_eq]
  simp only [Bool.false_eq_true, if_false]
  have hchecks : checks w.spec (w.fields s.pc) false s = s := by
    unfold checks
    split
    all_goals simp
  have hmoves : ∀ (l : List Nat) (sp : Option Nat) (sr : Option Bool) (s : WorkerState),
      l.foldl (moveReg (w.fields s.pc) false sp sr) s = s := by
    intro l sp sr
    induction l with
    | nil => intro s; rfl
    | cons i l ih =>
      intro s
      rw [List.foldl_cons, moveReg_inactive]
      exact ih s
  have hfinish : finish w.spec (w.fields s.pc) false s = s := by
    unfold finish
    split <;> simp
  unfold effect moves
  rw [hchecks]
  show finish w.spec (w.fields s.pc) false
    ((List.range w.spec.readers.registers).foldl (moveReg (w.fields s.pc) false _ _) s) = s
  rw [hmoves, hfinish]

/-- A worker that is not running is left alone by `service`. -/
theorem fold_notRun (w : Worker) (l : List Nat) (s : WorkerState) (hmode : s.mode ≠ .run) :
    l.foldl (fun s _ => step w (decide (s.mode = .run)) s) s = s := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.foldl_cons]
    have hstep : step w (decide (s.mode = .run)) s = s := by
      rw [decide_eq_false hmode]
      exact step_inactive w s
    rw [hstep]
    exact ih

theorem service_notRun (s : WorkerState) (hmode : s.mode ≠ .run) : service flagsW s = s :=
  fold_notRun flagsW _ s hmode

/-! ## Move batches: the ghost's `headStep` is the VM's `movePos` -/

/-- A move batch moves each head at most once. -/
def MoveNodup : Event → Prop
  | .move ms => (ms.map (·.head)).Nodup
  | _ => True

instance (e : Event) : Decidable (MoveNodup e) := by
  cases e <;> unfold MoveNodup <;> infer_instance

theorem moveDelta_eq_sumDelta :
    ∀ (ms : List Movement), (ms.map (·.head)).Nodup → ∀ h,
      ScaWorkerRegs.moveDelta ms h = sumDelta ms h
  | [], _, h => rfl
  | m :: ms, hnd, h => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have ih := moveDelta_eq_sumDelta ms hnd.2 h
    rw [sumDelta_cons]
    unfold ScaWorkerRegs.moveDelta lookupLast at ih ⊢
    rw [List.map_cons, List.reverse_cons, List.find?_append, Option.map_or]
    by_cases hm : m.head = h
    · -- no later movement of `h`
      have hnone : (List.map (fun m => (m.head, m.delta)) ms).reverse.find?
          (fun p => decide (p.1 = h)) = none := by
        rw [List.find?_eq_none]
        intro p hp
        rw [List.mem_reverse, List.mem_map] at hp
        obtain ⟨m', hm', rfl⟩ := hp
        simp only [decide_eq_true_eq]
        intro hm'h
        exact hnd.1 (List.mem_map.mpr ⟨m', hm', hm'h.trans hm.symm⟩)
      have hzero : sumDelta ms h = 0 := by
        by_contra hne
        obtain ⟨m', hm', hm'h⟩ := exists_of_sumDelta_ne hne
        exact hnd.1 (List.mem_map.mpr ⟨m', hm', hm'h.trans hm.symm⟩)
      rw [hnone, hzero]
      simp [hm]
    · rw [← ih]
      cases (List.map (fun m => (m.head, m.delta)) ms).reverse.find? (fun p => decide (p.1 = h)) with
      | none => simp [hm]
      | some p => simp [hm]

theorem headStep_eq_movePos {e : Event} (hnd : MoveNodup e) (pos : String → ℤ) :
    ScaWorkerRegs.headStep e pos = movePos e pos := by
  cases e with
  | move ms =>
    funext h
    show pos h + ScaWorkerRegs.moveDelta ms h = pos h + sumDelta ms h
    rw [moveDelta_eq_sumDelta ms hnd h]
  | copy t s =>
    funext h
    show (if h = t then pos s else pos h) = Function.update pos t (pos s) h
    rw [Function.update_apply]
  | _ => rfl

/-- Every row of the flag table moves each head at most once (checked by the kernel). -/
theorem flags_moveNodup_rows :
    (fspec.program.code.all fun row => decide (MoveNodup row.event)) = true := by
  decide +kernel

theorem moveNodup_of_row {r : Nat} {row : Row} (hrow : fspec.program.code[r]? = some row) :
    MoveNodup row.event := by
  have hall := List.all_eq_true.mp flags_moveNodup_rows row (List.mem_of_getElem? hrow)
  exact of_decide_eq_true hall

/-! ## Reader-table facts, the link, the base invariant -/

/-- Facts of the reader liveness (`liveReaders`) and the reader colouring at the rows the
certificate reaches, as `flags_step_certified` and `flags_start` use them. Finite facts of the
flag table, not yet checked by a certificate. -/
structure ReaderFacts : Prop where
  /-- `liveReaders` is a post-fixpoint of `readerTransfer` at the row. -/
  fix : ∀ c e r row, Sim flagsCert c e r → fspec.program.code[r]? = some row →
    ∀ x ∈ readerTransfer row (successorsUnion (liveReaders fspec) row.targets), x ∈ live r
  /-- The colouring is proper on the readers live after the row. -/
  proper : ∀ c e r row, Sim flagsCert c e r → fspec.program.code[r]? = some row →
    Proper fspec (successorsUnion (liveReaders fspec) row.targets)
  /-- The readers live before the row have registers. -/
  colored : ∀ c e r, Sim flagsCert c e r → Colored fspec (live r)
  /-- At the start row only `Origin`, `TextOrigin`, `OriginalEnd` are live. -/
  startLive : ∀ h ∈ live fspec.program.start,
    h = "Origin" ∨ h = "TextOrigin" ∨ h = "OriginalEnd"

/-- **The link.** The real flag worker `s` encodes `DualFlagVM` `v` on the segment
`[bg, bg + b)`: through a coroutine state `t` (`Rel`, `FlagRel` for the readers live at row
`s.pc`), with distance registers tracking the VM positions, and the worker running or done with
the VM halted. -/
structure Link (bg b : Nat) (s : WorkerState) (v : HVM) : Prop where
  co : ∃ t, Rel flagsCert s t ∧ FlagRel fspec (live s.pc) bg b t v
  regs : ∃ m, ScaWorkerRegs.Inv fspec ⟨v.pos, m⟩ s
  endEq : s.end = s.text.length
  mode : s.mode = .run ∨ (s.mode = .done ∧ v.flagsDone)

/-- What holds of the real flag worker at every time. -/
structure Base (s : WorkerState) : Prop where
  co : ∃ t, Rel flagsCert s t
  regs : ∃ g, ScaWorkerRegs.Inv fspec g s
  dataLen : s.data.length = fspec.readers.registers
  revLen : s.reverse.length = fspec.readers.registers
  endEq : s.end = s.text.length

theorem Link.base {bg b : Nat} {s : WorkerState} {v : HVM} (h : Link bg b s v) : Base s := by
  obtain ⟨⟨t, hrel, hfr⟩, ⟨m, hinv⟩, hend, -⟩ := h
  have hd : s.data = t.body.data := (congrArg WorkerState.data hrel.agree).trans rfl
  have hr : s.reverse = t.body.reverse := (congrArg WorkerState.reverse hrel.agree).trans rfl
  exact ⟨⟨t, hrel⟩, ⟨_, hinv⟩, hd ▸ hfr.dataLen, hr ▸ hfr.revLen, hend⟩

/-- The worker's flag stack (top first) is the VM's `flags` (append order) reversed. -/
theorem Link.flags_eq {bg b : Nat} {s : WorkerState} {v : HVM} (h : Link bg b s v) :
    s.flags = v.flags.reverse := by
  obtain ⟨⟨t, hrel, hfr⟩, -, -, -⟩ := h
  exact (hrel.observers_eq.2.2.1).trans hfr.flags

/-- A done worker holds a halted VM. -/
theorem Link.done {bg b : Nat} {s : WorkerState} {v : HVM} (h : Link bg b s v)
    (hdone : modeDone s = true) : v.flagsDone := by
  rcases h.mode with hrun | ⟨-, hv⟩
  · simp [modeDone, hrun] at hdone
  · exact hv

theorem base_initial : Base flagsInit := by
  refine ⟨⟨fcw.initialState, rel_initial flags_certified⟩,
    ⟨_, ScaWorkerRegs.initial_inv ScaWorkerRegs.flags_tableFacts⟩, ?_, ?_, rfl⟩
  · simp [flagsInit, WorkerState.initial]
  · simp [flagsInit, WorkerState.initial]

/-! ## The register hypothesis from the register invariant -/

/-- At a comparison row, the register the row selects holds the difference of the ghost
positions (the value behind `ScaWorkerRegs.compare_eq`). -/
theorem regsValue_of_regInv {pos : String → ℤ} {s : WorkerState}
    (hinv : ScaWorkerRegs.RegInv fspec pos s) {row : Row}
    (hrow : fspec.program.code[s.pc]? = some row) :
    RegsValue ((Worker.ofSpec fspec).fields s.pc) s pos row.event := by
  intro a b hcmp
  rw [fields_ofSpec fspec hrow]
  obtain ⟨event, targets⟩ := row
  have hcompare : event = .less a b ∨ event = .equal a b ∨ event = .assertEqual a b := by
    rcases hcmp with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  obtain ⟨htest, hreverse⟩ := ScaWorkerRegs.fieldsAt_test (spec := fspec) (liveReaders fspec)
    (liveDistances fspec) s.pc targets hcompare
  have hlive : ∀ {q : Pair}, pairOf fspec.names a b = some q →
      ScaWorkerRegs.Tracks fspec pos s.regs q :=
    fun hpair => hinv.live _ (ScaWorkerRegs.flags_tableFacts.transferLive s.pc _ hrow _
      (ScaWorkerRegs.mem_transfer_compare hcompare hpair))
  rw [htest, hreverse]
  rcases ScaWorkerRegs.canonical_cases fspec.names a b with
    ⟨hsame, hcan, _⟩ | ⟨hcan, hpair⟩ | ⟨hcan, hpair⟩
  · rw [hcan, hsame]
    simp [selectReg]
  · obtain ⟨j, hj, hval⟩ := hlive hpair
    rw [hcan]
    simp only [Option.bind_some, hj, selectReg, hval]
    simp
  · obtain ⟨j, hj, hval⟩ := hlive hpair
    rw [hcan]
    simp only [Option.bind_some, hj, selectReg, hval]
    simp

/-! ## One step -/

theorem step_text_end (w : Worker) (act : Bool) (s : WorkerState) :
    (step w act s).text = s.text ∧ (step w act s).end = s.end := by
  cases act
  · rw [step_inactive]; exact ⟨rfl, rfl⟩
  · have ht := (effect_data w.spec (w.fields s.pc) s).1
    have hc := (ScaWorkerRegs.effect_counters w.spec (w.fields s.pc) true s).1
    simp only [ScaWorkerRegs.counters, Prod.mk.injEq] at hc
    exact ⟨ht, hc.2.1⟩

/-- **A pending step.** From a linked running worker whose VM is pending, one active step of
the real worker is one `stepFlags`: the link moves to the VM's successor, the fault and the
mode stay. -/
theorem step_pending (hfacts : ReaderFacts) {bg b : Nat} {s : WorkerState} {v v' : HVM}
    {c : Config} {e : Event} (hlink : Link bg b s v) (hrun : s.mode = .run)
    (hctl : v.ctl = .pending c e) (hstep : stepFlags v = some v') :
    Link bg b (step flagsW true s) v' ∧ (step flagsW true s).fault = s.fault ∧
      (step flagsW true s).mode = .run := by
  obtain ⟨⟨t, hrel, hfr⟩, ⟨m, hinv⟩, hend, -⟩ := hlink
  have htctl : t.ctl = .pending c e := hfr.ctl.trans hctl
  have hsim : Sim flagsCert c e s.pc := by
    have h := hrel.sim
    rw [htctl] at h
    exact h
  obtain ⟨row, hrow, hevent, -, -⟩ := sim_step flags_certified.certOk hsim
  have hrom : fcw.rom t.ctl = (Worker.ofSpec fspec).fields s.pc := flags_certified.rom_eq hrel.sim
  have hregsEq : s.regs = t.body.regs := (congrArg WorkerState.regs hrel.agree).trans rfl
  have hregs : RegsValue (fcw.rom t.ctl) t.body v.pos e := by
    intro a b' hcmp
    have h := regsValue_of_regInv hinv.regs hrow a b' (by rw [hevent]; exact hcmp)
    rw [hrom, ← hregsEq]
    exact h
  obtain ⟨r', hsim', hfr', hfault, hmode⟩ := flags_step_certified flags_certified rfl rfl hsim
    htctl hrow hfr (hfacts.fix c e s.pc row hsim hrow) (hfacts.proper c e s.pc row hsim hrow)
    (hfacts.colored c e s.pc hsim) colorsBound readersNotBlind hregs hstep
  have hrel' : Rel flagsCert (step flagsW true s) (fcw.step true t) :=
    rel_step flags_certified hrel true
  have hr' : r' = (step flagsW true s).pc := simCtl_unique hsim' hrel'.sim
  obtain ⟨-, hmo, -, hfa⟩ := hrel'.observers_eq
  have hmodeT : t.body.mode = s.mode := ((congrArg WorkerState.mode hrel.agree).trans rfl).symm
  have hfaultT : t.body.fault = s.fault := ((congrArg WorkerState.fault hrel.agree).trans rfl).symm
  have hinv' := ScaWorkerRegs.step_inv ScaWorkerRegs.flags_tableFacts hinv true
  have hev : ((Worker.ofSpec fspec).fields s.pc).event = e := by
    rw [fields_ofSpec fspec hrow, fieldsAt_event, hevent]
  obtain ⟨-, hv'⟩ := stepFlags_some hctl hstep
  have hpos : v'.pos = movePos e v.pos := by rw [hv']
  have hnd : MoveNodup e := hevent ▸ moveNodup_of_row hrow
  have hghost : ScaWorkerRegs.ghostStep fspec true s ⟨v.pos, m⟩ = ⟨v'.pos, m⟩ := by
    show (⟨ScaWorkerRegs.headStep ((Worker.ofSpec fspec).fields s.pc).event v.pos, m⟩ :
      ScaWorkerRegs.Ghost) = ⟨v'.pos, m⟩
    rw [hev, hpos, headStep_eq_movePos hnd]
  obtain ⟨htext', hend'⟩ := step_text_end flagsW true s
  refine ⟨⟨⟨fcw.step true t, hrel', ?_⟩, ⟨m, ?_⟩, ?_, Or.inl ?_⟩, ?_, ?_⟩
  · rw [← hr']; exact hfr'
  · rw [← hghost]; exact hinv'
  · rw [htext', hend']; exact hend
  · rw [hmo, hmode, hmodeT, hrun]
  · rw [hfa, hfault, hfaultT]
  · rw [hmo, hmode, hmodeT, hrun]

/-- **The halting step.** From a linked running worker whose VM has returned, one active step
of the real worker executes the sink row: the worker is done, the VM stays (it is
`flagsDone`), the fault stays. -/
theorem step_returned {bg b : Nat} {s : WorkerState} {v : HVM} {val : Value}
    (hlink : Link bg b s v) (hctl : v.ctl = .returned val) :
    Link bg b (step flagsW true s) v ∧ (step flagsW true s).fault = s.fault ∧
      (step flagsW true s).mode = .done := by
  obtain ⟨⟨t, hrel, hfr⟩, ⟨m, hinv⟩, hend, -⟩ := hlink
  have htctl : t.ctl = .returned val := hfr.ctl.trans hctl
  have hpc : s.pc = 0 := by
    have h := hrel.sim
    rw [htctl] at h
    exact h
  have hfr0 : FlagRel fspec [] bg b t v := by
    have h := hfr
    rw [hpc, live_zero] at h
    exact h
  have hrom : fcw.rom t.ctl = (Worker.ofSpec fspec).fields 0 := by
    rw [htctl]; exact flags_certified.romAtReturned val
  have hdec : Decodes fspec [] .halt (fcw.rom t.ctl) := by
    rw [hrom, fields_ofSpec fspec flagsWorker_sinkRow]
    exact decodes_fieldsAt fspec (liveReaders fspec) (liveDistances fspec) 0 ⟨.halt, []⟩
  have hproper : Proper fspec [] := fun _ hh => absurd hh List.not_mem_nil
  have hcolored : Colored fspec [] := fun _ hh => absurd hh List.not_mem_nil
  obtain ⟨hdone, -, hfr', hmode, hfault⟩ :=
    flags_step_returned (cw := fcw) rfl rfl hfr0 htctl hdec hproper hcolored colorsBound
  have hrel' : Rel flagsCert (step flagsW true s) (fcw.step true t) :=
    rel_step flags_certified hrel true
  have hctl' : (fcw.step true t).ctl = .returned val := by
    rw [CoWorker.step_ctl, htctl]; rfl
  have hpc' : (step flagsW true s).pc = 0 := by
    have h := hrel'.sim
    rw [hctl'] at h
    exact h
  obtain ⟨-, hmo, -, hfa⟩ := hrel'.observers_eq
  have hfaultT : t.body.fault = s.fault := ((congrArg WorkerState.fault hrel.agree).trans rfl).symm
  have hinv' := ScaWorkerRegs.step_inv ScaWorkerRegs.flags_tableFacts hinv true
  have hev : ((Worker.ofSpec fspec).fields s.pc).event = .halt := by
    rw [hpc, fields_ofSpec fspec flagsWorker_sinkRow]; rfl
  have hghost : ScaWorkerRegs.ghostStep fspec true s ⟨v.pos, m⟩ = ⟨v.pos, m⟩ := by
    show (⟨ScaWorkerRegs.headStep ((Worker.ofSpec fspec).fields s.pc).event v.pos, m⟩ :
      ScaWorkerRegs.Ghost) = ⟨v.pos, m⟩
    rw [hev]; rfl
  obtain ⟨htext', hend'⟩ := step_text_end flagsW true s
  refine ⟨⟨⟨fcw.step true t, hrel', ?_⟩, ⟨m, ?_⟩, ?_, Or.inr ⟨?_, hdone⟩⟩, ?_, ?_⟩
  · rw [hpc', live_zero]; exact hfr'
  · rw [← hghost]; exact hinv'
  · rw [htext', hend']; exact hend
  · rw [hmo, hmode]
  · rw [hfa, hfault, hfaultT]
  · rw [hmo, hmode]

/-! ## (1) The service quantum -/

/-- The run hypothesis: within `k` steps, the VM does not get stuck before halting. -/
def RunsFor (k : ℕ) (v : HVM) : Prop :=
  ∀ i < k, ∀ u, iterFlags i v = some u → ¬ u.flagsDone → (stepFlags u).isSome

theorem RunsFor.tail {k : ℕ} {v v1 : HVM} (hrun : RunsFor (k + 1) v)
    (hstep : stepFlags v = some v1) : RunsFor k v1 := by
  intro i hi u hu hnu
  exact hrun (i + 1) (by omega) u (by rw [iterFlags_succ_of_step hstep]; exact hu) hnu

theorem fold_link (hfacts : ReaderFacts) {bg b : Nat} :
    ∀ (l : List Nat) (s : WorkerState) (v : HVM), Link bg b s v → RunsFor l.length v →
      ∃ n v', n ≤ l.length ∧ iterFlags n v = some v' ∧
        Link bg b (l.foldl (fun s _ => step flagsW (decide (s.mode = .run)) s) s) v' ∧
        (l.foldl (fun s _ => step flagsW (decide (s.mode = .run)) s) s).fault = s.fault ∧
        ((l.foldl (fun s _ => step flagsW (decide (s.mode = .run)) s) s).mode = .done ↔
          (s.mode = .done ∨ n < l.length)) ∧
        (n < l.length → v'.flagsDone)
  | [], s, v, hlink, _ =>
    ⟨0, v, le_refl _, rfl, hlink, rfl, by simp, fun h => absurd h (by simp)⟩
  | x :: l, s, v, hlink, hrun => by
    rcases hlink.mode with hmr | ⟨hmd, hvd⟩
    · rw [List.foldl_cons]
      have hstepT : step flagsW (decide (s.mode = .run)) s = step flagsW true s := by
        rw [hmr]; rfl
      rw [hstepT]
      cases hc : v.ctl with
      | pending c e =>
        have hnd : ¬ v.flagsDone := by
          rintro ⟨val, hval⟩
          rw [hc] at hval
          cases hval
        obtain ⟨v1, hv1⟩ := Option.isSome_iff_exists.mp (hrun 0 (by simp) v rfl hnd)
        obtain ⟨hlink1, hfault1, hmode1⟩ := step_pending hfacts hlink hmr hc hv1
        have hrun1 : RunsFor l.length v1 := RunsFor.tail (by simpa using hrun) hv1
        obtain ⟨n, v', hn, hiter, hlink', hfault', hmode', hdone'⟩ :=
          fold_link hfacts l _ v1 hlink1 hrun1
        refine ⟨n + 1, v', by simp; omega, by rw [iterFlags_succ_of_step hv1]; exact hiter,
          hlink', hfault'.trans hfault1, ?_, ?_⟩
        · rw [hmode', hmode1, hmr]
          simp
        · intro hlt
          exact hdone' (by simp at hlt; omega)
      | returned val =>
        obtain ⟨hlink1, hfault1, hmode1⟩ := step_returned hlink hc
        rw [fold_notRun flagsW l _ (by rw [hmode1]; decide)]
        refine ⟨0, v, by simp, rfl, hlink1, hfault1, ?_, fun _ => ⟨val, hc⟩⟩
        rw [hmode1]
        simp
      | failed =>
        exfalso
        obtain ⟨t, hrel, hfr⟩ := hlink.co
        have h := hrel.sim
        rw [hfr.ctl, hc] at h
        exact h.elim
    · have hnr : s.mode ≠ .run := by rw [hmd]; decide
      rw [fold_notRun flagsW (x :: l) s hnr]
      exact ⟨0, v, by simp, rfl, hlink, rfl, by simp [hmd], fun _ => hvd⟩

/-- **(1) One service quantum.** From a linked worker (running, or done with a halted VM), if
the VM does not get stuck before halting within `32768` steps, `service` runs the VM `n ≤ 32768`
steps to `v'` and keeps the link with `v'`; the fault stays; the worker is done iff it was
done or `n < 32768` (the halt row ran within the quantum), and then `v'` is `flagsDone`; the flag
stack is `v'.flags` reversed. -/
theorem service_link (hfacts : ReaderFacts) {bg b : Nat} {s : WorkerState} {v : HVM}
    (hlink : Link bg b s v) (hrun : RunsFor quantum v) :
    ∃ n v', n ≤ quantum ∧ iterFlags n v = some v' ∧ Link bg b (service flagsW s) v' ∧
      (service flagsW s).fault = s.fault ∧
      ((service flagsW s).mode = .done ↔ (s.mode = .done ∨ n < quantum)) ∧
      (n < quantum → v'.flagsDone) ∧ (service flagsW s).flags = v'.flags.reverse := by
  have h := fold_link hfacts (List.range quantum) s v hlink (by simpa using hrun)
  rw [List.length_range] at h
  obtain ⟨n, v', hn, hiter, hlink', hfault, hmode, hdone⟩ := h
  exact ⟨n, v', hn, hiter, hlink', hfault, hmode, hdone, hlink'.flags_eq⟩

/-- `modeDone` after a quantum started running: done iff the VM halted within the quantum
(`n < 32768`; if it halts at exactly `32768` steps the halt row runs at the next quantum). -/
theorem service_modeDone (hfacts : ReaderFacts) {bg b : Nat} {s : WorkerState} {v : HVM}
    (hlink : Link bg b s v) (hrunning : s.mode = .run) (hrun : RunsFor quantum v) :
    ∃ n v', n ≤ quantum ∧ iterFlags n v = some v' ∧ Link bg b (service flagsW s) v' ∧
      (service flagsW s).fault = s.fault ∧
      (modeDone (service flagsW s) = true ↔ n < quantum) ∧
      (modeDone (service flagsW s) = true → v'.flagsDone) ∧
      (service flagsW s).flags = v'.flags.reverse := by
  obtain ⟨n, v', hn, hiter, hlink', hfault, hmode, hdone, hflags⟩ := service_link hfacts hlink hrun
  refine ⟨n, v', hn, hiter, hlink', hfault, ?_, hlink'.done, hflags⟩
  rw [modeDone, decide_eq_true_iff, hmode, hrunning]
  simp

/-! ## (2) `arrive`, `resetFlags`, `mark`, `start` -/

theorem arrive_pc (w : Worker) (c : Fin 2) (s : WorkerState) : (arrive w c s).pc = s.pc := by
  unfold arrive; split <;> rfl

theorem arrive_end (w : Worker) (c : Fin 2) (s : WorkerState) :
    (arrive w c s).end = s.end + 1 := by
  unfold arrive; split <;> rfl

theorem arrive_begin (w : Worker) (c : Fin 2) (s : WorkerState) :
    (arrive w c s).begin = s.begin := by
  unfold arrive; split <;> rfl

/-- A flag worker's `hKey` counts the arrival. -/
theorem arrive_h (c : Fin 2) (s : WorkerState) : (arrive flagsW c s).h = s.h + 1 := rfl

/-- With `end = |text|` the `end` head can always move onto the new letter. -/
theorem arrive_fault (w : Worker) (c : Fin 2) {s : WorkerState} (hend : s.end = s.text.length) :
    (arrive w c s).fault = s.fault := by
  unfold arrive
  split <;> simp [WorkerState.canMoveTo, hend] <;> intro h <;> omega

theorem arrive_base {s : WorkerState} (h : Base s) (c : Fin 2) : Base (arrive flagsW c s) := by
  obtain ⟨⟨t, hrel⟩, ⟨g, hinv⟩, hdl, hrl, hend⟩ := h
  obtain ⟨hd, hr, ht, -, -, -⟩ := arrive_proj flagsW c s
  refine ⟨⟨fcw.arrive c t, rel_arrive flags_certified hrel c⟩,
    ⟨g, ScaWorkerRegs.arrive_inv hinv c⟩, ?_, ?_, ?_⟩
  · rw [hd]; exact hdl
  · rw [hr]; exact hrl
  · rw [arrive_end, ht, List.length_append, hend]; rfl

/-- **`arrive`** keeps the link: the segment has already arrived. -/
theorem arrive_link {bg b : Nat} {s : WorkerState} {v : HVM} (h : Link bg b s v) (c : Fin 2) :
    Link bg b (arrive flagsW c s) v ∧ (arrive flagsW c s).fault = s.fault := by
  obtain ⟨⟨t, hrel, hfr⟩, ⟨m, hinv⟩, hend, hmode⟩ := h
  obtain ⟨-, -, ht, -, -, hmo⟩ := arrive_proj flagsW c s
  refine ⟨⟨⟨fcw.arrive c t, rel_arrive flags_certified hrel c, ?_⟩,
    ⟨m, ScaWorkerRegs.arrive_inv hinv c⟩, ?_, ?_⟩, arrive_fault flagsW c hend⟩
  · rw [arrive_pc]; exact flags_arrive hfr c
  · rw [arrive_end, ht, List.length_append, hend]; rfl
  · rw [hmo]; exact hmode

theorem resetFlags_true (s : WorkerState) :
    resetFlags flagsW true s =
      { s with begin := s.end, length := 0, h := 0, flags := [], mode := .idle } := rfl

theorem resetFlags_base {s : WorkerState} (h : Base s) (en : Bool) :
    Base (resetFlags flagsW en s) := by
  obtain ⟨⟨t, hrel⟩, ⟨g, hinv⟩, hdl, hrl, hend⟩ := h
  refine ⟨⟨fcw.resetFlags en t, rel_resetFlags flags_certified hrel en⟩,
    ⟨_, ScaWorkerRegs.resetFlags_inv hinv en⟩, ?_, ?_, ?_⟩ <;> cases en <;> assumption

theorem mark_base {s : WorkerState} (h : Base s) (en : Bool) : Base (mark flagsW en s) := by
  obtain ⟨⟨t, hrel⟩, ⟨g, hinv⟩, hdl, hrl, hend⟩ := h
  refine ⟨⟨fcw.mark en t, rel_mark flags_certified hrel en⟩,
    ⟨_, ScaWorkerRegs.mark_inv hinv en⟩, ?_, ?_, ?_⟩ <;> cases en <;> assumption

/-- **`mark`** keeps the link (it only clears `hKey`). -/
theorem mark_link {bg b : Nat} {s : WorkerState} {v : HVM} (h : Link bg b s v) (en : Bool) :
    Link bg b (mark flagsW en s) v := by
  obtain ⟨⟨t, hrel, hfr⟩, ⟨m, hinv⟩, hend, hmode⟩ := h
  cases en
  · exact ⟨⟨t, hrel, hfr⟩, ⟨m, hinv⟩, hend, hmode⟩
  · refine ⟨⟨fcw.mark true t, rel_mark flags_certified hrel true, ?_⟩,
      ⟨s.end, ScaWorkerRegs.mark_inv hinv true⟩, hend, hmode⟩
    exact ⟨hfr.ctl, hfr.dataLen, hfr.revLen, hfr.frontier, hfr.word, hfr.heads, hfr.orient,
      hfr.flags⟩

theorem mark_true (s : WorkerState) : mark flagsW true s = { s with h := 0 } := rfl

/-! ### `start` -/

/-- The fields `start` must not disturb. -/
def outer (s : WorkerState) : Bool × List (Fin 2) × Nat × Nat := (s.fault, s.text, s.begin, s.end)

theorem rawStart_outer (w : Worker) (hd : String) (src : Nat) (r en : Bool) (s : WorkerState) :
    outer (rawStart w hd src r en s) = outer s := by
  unfold rawStart
  split
  · rfl
  · split <;> rfl

theorem initializeValues_outer (M : List (Pair × Option (DistKey × Int))) (en : Bool)
    (s : WorkerState) : outer (initializeValues fspec M en s) = outer s := by
  cases en
  · rfl
  · rw [ScaWorkerRegs.initializeValues_true]
    induction M generalizing s with
    | nil => rfl
    | cons e M ih =>
      rw [List.foldl_cons, ih]
      unfold ScaWorkerRegs.initStep
      split
      · rfl
      · split <;> rfl

theorem startBody_flags_eq (s : WorkerState) :
    startBody flagsW true s =
      { initializeValues fspec flagsStartMapping true
          (rawStart flagsW "OriginalEnd" s.begin true true
            (rawStart flagsW "TextOrigin" s.end true true
              (rawStart flagsW "Origin" s.begin false true
                { s with fault := s.fault || decide (s.mode = .run) }))) with
        flags := [] } := by
  unfold startBody
  have hf : flagsW.spec.isFlags = true := rfl
  simp only [hf, if_true, Bool.true_and]
  rfl

theorem start_outer (s : WorkerState) :
    outer (start flagsW true s) = ((s.fault || decide (s.mode = .run)), s.text, s.begin, s.end) := by
  have e1 : outer (start flagsW true s) = outer (startBody flagsW true s) := rfl
  rw [e1, startBody_flags_eq]
  have e2 : ∀ y : WorkerState, outer { y with flags := [] } = outer y := fun _ => rfl
  rw [e2, initializeValues_outer, rawStart_outer, rawStart_outer, rawStart_outer]
  rfl

theorem start_false (s : WorkerState) : start flagsW false s = s := by
  have h : start flagsW false s = { s with fault := s.fault || false } := rfl
  rw [h, Bool.or_false]

/-- The VM a release starts on the worker state `s`: `DualFlagVM(y, b - h, b)` on the segment
`y = text[begin, end)`, `b = end - begin`, `h = hKey` (the arrivals since the last mark);
`Upper = b`, `Lower = b - h` (`SCA_GS_MAPPING.md` §0). -/
def releaseVM (s : WorkerState) : HVM :=
  flagsInitialVM (flagWord s.text s.begin (s.end - s.begin))
    (((s.end - s.begin : ℕ) : ℤ) - s.h) ((s.end - s.begin : ℕ) : ℤ) ctl0

/-- **`start true` is `DualFlagVM(y, b - h, b)`.** From any base state, `start true` links the
worker to `releaseVM s` on the segment `[begin, end)`; it faults iff the worker was running. -/
theorem start_link (hfacts : ReaderFacts) {s : WorkerState} (hbase : Base s) :
    Link s.begin (s.end - s.begin) (start flagsW true s) (releaseVM s) ∧
      (start flagsW true s).fault = (s.fault || decide (s.mode = .run)) ∧
      (start flagsW true s).mode = .run := by
  obtain ⟨⟨t, hrel⟩, ⟨g, hinv⟩, hdl, hrl, hend⟩ := hbase
  have hsb : s.begin = t.body.begin := (congrArg WorkerState.begin hrel.agree).trans rfl
  have hse : s.end = t.body.end := (congrArg WorkerState.end hrel.agree).trans rfl
  have hst : s.text = t.body.text := (congrArg WorkerState.text hrel.agree).trans rfl
  have hsd : s.data = t.body.data := (congrArg WorkerState.data hrel.agree).trans rfl
  have hsr : s.reverse = t.body.reverse := (congrArg WorkerState.reverse hrel.agree).trans rfl
  have hbe : s.begin ≤ s.end := le_trans hinv.keys.beginLeMark hinv.keys.markLeEnd
  have hfr := flags_start (cw := fcw) (L := live fspec.program.start) rfl rfl
    (by rw [← hsd]; exact hdl) (by rw [← hsr]; exact hrl) (by rw [← hsb, ← hse]; exact hbe)
    (by rw [← hse, ← hst]; exact hend.le) color_origin color_textOrigin color_originalEnd
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hfacts.startLive
    (((s.end - s.begin : ℕ) : ℤ) - s.h) ((s.end - s.begin : ℕ) : ℤ)
  rw [← hsb, ← hse, ← hst] at hfr
  have hc0 : (fcw.start true t).ctl = ctl0 := rfl
  rw [hc0] at hfr
  have hpc : (start flagsW true s).pc = fspec.program.start := rfl
  have hinv' := ScaWorkerRegs.start_inv ScaWorkerRegs.flags_tableFacts hinv true
  have hlen : s.length = ((s.end - s.begin : ℕ) : ℤ) := by
    rw [hinv.keys.lengthEq]; omega
  have hwlen : (flagWord s.text s.begin (s.end - s.begin)).length = s.end - s.begin :=
    flagWord_length (by omega)
  have hpos : ScaWorkerRegs.startPos fspec s.length s.h = (releaseVM s).pos := by
    funext hd
    simp only [ScaWorkerRegs.startPos, releaseVM, flagsInitialVM, fspec_isFlags, if_true, hwlen,
      hlen]
    by_cases h1 : hd = "OriginalEnd"
    · subst h1; simp
    · by_cases h2 : hd = "Upper"
      · subst h2; simp
      · by_cases h3 : hd = "Lower"
        · subst h3; simp
        · simp [h1, h2, h3]
  have hghost : ScaWorkerRegs.ghostStart fspec true s g = ⟨(releaseVM s).pos, g.markEnd⟩ := by
    show (⟨ScaWorkerRegs.startPos fspec s.length s.h, g.markEnd⟩ : ScaWorkerRegs.Ghost) = _
    rw [hpos]
  have houter := start_outer s
  simp only [outer, Prod.mk.injEq] at houter
  obtain ⟨hfault0, htext0, -, hend0⟩ := houter
  refine ⟨⟨⟨fcw.start true t, rel_start flags_certified hrel true, ?_⟩, ⟨g.markEnd, ?_⟩, ?_,
    Or.inl rfl⟩, hfault0, rfl⟩
  · rw [hpc]; exact hfr
  · rw [← hghost]; exact hinv'
  · rw [htext0, hend0]; exact hend

/-- **(2) The release** (`start true`, then `mark true`, as in `stageRound`): the worker is
linked to `releaseVM s`, running, with `hKey = 0`; it faults iff it was running. -/
theorem release_link (hfacts : ReaderFacts) {s : WorkerState} (hbase : Base s) :
    Link s.begin (s.end - s.begin) (mark flagsW true (start flagsW true s)) (releaseVM s) ∧
      (mark flagsW true (start flagsW true s)).fault = (s.fault || decide (s.mode = .run)) ∧
      (mark flagsW true (start flagsW true s)).mode = .run ∧
      (mark flagsW true (start flagsW true s)).h = 0 := by
  obtain ⟨hlink, hfault, hmode⟩ := start_link hfacts hbase
  exact ⟨mark_link hlink true, hfault, hmode, rfl⟩

/-! ## (3) One tick of the flag worker inside `stageRound` -/

/-- The flag worker's share of `ScaWindowPal.stageRound` (`ScaWindowPal.lean:201-218`): arrive,
`resetFlags birth`, `start release`, `mark release`, `service`. -/
def flagTick (a : Fin 2) (birth release : Bool) (s : WorkerState) : WorkerState :=
  flagsOps.service (flagsOps.mark release (flagsOps.start release
    (flagsOps.resetFlags birth (flagsOps.arrive a s))))

theorem flagTick_eq (a : Fin 2) (birth release : Bool) (s : WorkerState) :
    flagTick a birth release s =
      service flagsW (mark flagsW release (start flagsW release
        (resetFlags flagsW birth (arrive flagsW a s)))) := by
  simp only [flagTick, flagsOps, opsOf]

theorem resetFlags_false (s : WorkerState) : resetFlags flagsW false s = s := rfl

theorem mark_false (s : WorkerState) : mark flagsW false s = s := rfl

/-- `stageRound` applies `flagTick` to stage `i`'s flag worker. -/
theorem stageRound_flags {Wm : Type} (mOps : ScaWindowPal.WorkerOps Wm) (a i : Fin 2)
    (S : ScaWindowPal.PalState Wm WorkerState) :
    (ScaWindowPal.stageRound mOps flagsOps a i S).flags i =
      flagTick a (S.stages i).birth (S.stages i).release (S.flags i) := by
  unfold ScaWindowPal.stageRound
  simp only [Function.update_self]
  rfl

/-- **A release tick** (`birth = false`, `release = true`): the worker is linked to the VM
`releaseVM (arrive a s)` started on `[begin, end + 1)` and runs one quantum of it. -/
theorem tick_release (hfacts : ReaderFacts) {s : WorkerState} (hbase : Base s) (a : Fin 2)
    (hrun : RunsFor quantum (releaseVM (arrive flagsW a s))) :
    ∃ n v', n ≤ quantum ∧ iterFlags n (releaseVM (arrive flagsW a s)) = some v' ∧
      Link s.begin (s.end + 1 - s.begin) (flagTick a false true s) v' ∧
      (flagTick a false true s).fault = (s.fault || decide (s.mode = .run)) ∧
      (modeDone (flagTick a false true s) = true ↔ n < quantum) ∧
      (modeDone (flagTick a false true s) = true → v'.flagsDone) ∧
      (flagTick a false true s).flags = v'.flags.reverse := by
  have hbase1 := arrive_base hbase a
  have hfault1 : (arrive flagsW a s).fault = s.fault := arrive_fault flagsW a hbase.endEq
  have hmode1 : (arrive flagsW a s).mode = s.mode := (arrive_proj flagsW a s).2.2.2.2.2
  obtain ⟨hlink, hfault2, hmode2, -⟩ := release_link hfacts hbase1
  rw [arrive_begin, arrive_end] at hlink
  obtain ⟨n, v', hn, hiter, hlink', hfault', hdone, hdone', hflags⟩ :=
    service_modeDone hfacts hlink hmode2 hrun
  rw [flagTick_eq, resetFlags_false]
  refine ⟨n, v', hn, hiter, hlink', ?_, hdone, hdone', hflags⟩
  rw [hfault', hfault2, hfault1, hmode1]

/-- **A tick of a linked worker** (`birth = release = false`, the worker running or done with a
halted VM): `arrive`, then one quantum of the VM. -/
theorem tick_running (hfacts : ReaderFacts) {bg b : Nat} {s : WorkerState} {v : HVM}
    (hlink : Link bg b s v) (a : Fin 2) (hrun : RunsFor quantum v) :
    ∃ n v', n ≤ quantum ∧ iterFlags n v = some v' ∧ Link bg b (flagTick a false false s) v' ∧
      (flagTick a false false s).fault = s.fault ∧
      ((flagTick a false false s).mode = .done ↔ (s.mode = .done ∨ n < quantum)) ∧
      (n < quantum → v'.flagsDone) ∧ (flagTick a false false s).flags = v'.flags.reverse := by
  obtain ⟨hlink1, hfault1⟩ := arrive_link hlink a
  have hmode1 : (arrive flagsW a s).mode = s.mode := (arrive_proj flagsW a s).2.2.2.2.2
  have htick : flagTick a false false s = service flagsW (arrive flagsW a s) := by
    rw [flagTick_eq, resetFlags_false, start_false, mark_false]
  obtain ⟨n, v', hn, hiter, hlink', hfault', hmode', hdone, hflags⟩ :=
    service_link hfacts hlink1 hrun
  rw [htick]
  refine ⟨n, v', hn, hiter, hlink', hfault'.trans hfault1, ?_, hdone, hflags⟩
  rw [← hmode1]
  exact hmode'

/-- **A birth tick** (`birth = true`, `release = false`): the worker is reset on the new
segment start `begin = end` and idles (no service step runs). -/
theorem tick_birth {s : WorkerState} (hbase : Base s) (a : Fin 2) :
    flagTick a true false s = resetFlags flagsW true (arrive flagsW a s) ∧
      Base (flagTick a true false s) ∧ (flagTick a true false s).fault = s.fault ∧
      (flagTick a true false s).mode = .idle ∧ (flagTick a true false s).flags = [] ∧
      (flagTick a true false s).begin = s.end + 1 ∧ (flagTick a true false s).h = 0 := by
  have htick : flagTick a true false s = resetFlags flagsW true (arrive flagsW a s) := by
    rw [flagTick_eq, start_false, mark_false]
    exact service_notRun _ (by rw [resetFlags_true]; intro h; cases h)
  rw [htick]
  refine ⟨rfl, resetFlags_base (arrive_base hbase a) true, ?_, rfl, rfl, ?_, rfl⟩
  · rw [resetFlags_true]; exact arrive_fault flagsW a hbase.endEq
  · rw [resetFlags_true]; exact arrive_end flagsW a s

/-- **An idle tick** (`birth = release = false`, the worker not running): only the letter
arrives. -/
theorem tick_idle {s : WorkerState} (hbase : Base s) (hmode : s.mode ≠ .run) (a : Fin 2) :
    flagTick a false false s = arrive flagsW a s ∧ Base (flagTick a false false s) ∧
      (flagTick a false false s).fault = s.fault ∧ (flagTick a false false s).mode = s.mode ∧
      (flagTick a false false s).flags = s.flags := by
  have hmode1 : (arrive flagsW a s).mode = s.mode := (arrive_proj flagsW a s).2.2.2.2.2
  have htick : flagTick a false false s = arrive flagsW a s := by
    rw [flagTick_eq, resetFlags_false, start_false, mark_false]
    exact service_notRun _ (by rw [hmode1]; exact hmode)
  rw [htick]
  exact ⟨rfl, arrive_base hbase a, arrive_fault flagsW a hbase.endEq, hmode1,
    (arrive_proj flagsW a s).2.2.2.2.1⟩

end PalPeg.ScaFlagsLink
