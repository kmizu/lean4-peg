import PalPeg.LocalViewStep

/-!
# One slot of a view: eleven steps

A command to a view takes one slot of eleven steps.  Step `0` is the decision step
(`LocalViewStep`): the two stack tapes move, the job of the queue goes into the control, and the
queue tapes are left alone.  Steps `1`–`10` run the job on the queue tapes (`slotTail`), padded
with increments of the length counter, which do nothing when nothing is owed.
-/

set_option autoImplicit false

namespace PalPeg.ConcreteLocalMachine

open PalPeg
open PalPeg.RTQueue (Queue)
open PalPeg.CloseoutCoreStep (Γc blankc)
open PalPeg.Program (STape)
open PalPeg.LocalInputView
open PalPeg.LocalViewCells
open PalPeg.CloseoutCoreEnc12 (Act actList TEqG ActRule compStep teq_sweep_actList)
open PalPeg.CloseoutCoreEnc25 (RTag)
open PalPeg.Local (Window readWin pos sweep)

/-- The micro-operations of steps `1`–`10` of a slot. -/
def slotTail : Option QueueJob → List MicroOp
  | none => List.replicate 10 .incLength
  | some (.snoc a) => snocProgram a ++ List.replicate 1 .incLength
  | some .tail => tailProgram

theorem slotTail_length (job : Option QueueJob) : (slotTail job).length = 10 := by
  cases job with
  | none => rfl
  | some job => cases job <;> rfl

section QueueSide

variable {K : ℕ} {Terminal : Type}

theorem microRun_append (hK : 2 ≤ K) (input : Option Terminal) :
    ∀ (first second : List MicroOp) (state final : MicroState),
      MicroRun hK input (first ++ second) state final →
      ∃ middle, MicroRun hK input first state middle ∧ MicroRun hK input second middle final
  | [], _, state, _, hrun => ⟨state, MicroRun.nil _, hrun⟩
  | micro :: rest, second, state, final, hrun => by
    cases hrun with
    | cons hstep hrest =>
      obtain ⟨middle, hfirst, hsecond⟩ := microRun_append hK input rest second _ final hrest
      exact ⟨middle, MicroRun.cons hstep hfirst, hsecond⟩

/-- Increments of the length counter with nothing owed leave the represented queue as it is. -/
theorem idleRun_sound (hK : 2 ≤ K) {margin : ℕ} (hmarginLe : K ≤ margin) (input : Option Terminal) :
    ∀ (count : ℕ) {q : Queue (Fin 2)} {state final : MicroState} {first : MicroOp},
      MicroRun hK input (List.replicate count .incLength) state final →
      MicroRep margin q (first, state.1) state.2 → state.1.2.2 = 0 →
      ∀ last : MicroOp, MicroRep margin q (last, final.1) final.2 ∧ final.1.2.2.val = 0
  | 0, q, state, final, first, hrun, hrep, howed, last => by
    cases hrun
    exact ⟨hrep, by rw [howed]; rfl⟩
  | count + 1, q, state, final, first, hrun, hrep, howed, last => by
    cases hrun with
    | cons hstep hrest =>
      rename_i middle
      have hone := microRun_sound hK hmarginLe input [.incLength] q state middle first .incLength
        (MicroRun.cons hstep (MicroRun.nil _)) hrep
        (by rw [howed]; exact (rfl : (0 - 1 : ℕ) = 0))
        ⟨microPremises_trivial _ (by simp) (by simp), trivial⟩
      exact idleRun_sound hK hmarginLe input count hrest hone.1 (Fin.ext hone.2) last

/-- **Steps `1`–`10` of a slot perform the job on the queue.** -/
theorem slotTailRun_sound (hK : 2 ≤ K) {margin : ℕ} (hmarginLe : K ≤ margin)
    (input : Option Terminal) {q : Queue (Fin 2)}
    (hq : RTQueue.Inv q) (job : Option QueueJob) (hfront : job = some .tail → q.front ≠ [])
    {state final : MicroState} {first : MicroOp}
    (hrun : MicroRun hK input (slotTail job) state final)
    (hrep : MicroRep margin q (first, state.1) state.2) (howed : state.1.2.2 = 0) (last : MicroOp) :
    MicroRep margin (jobApply job q) (last, final.1) final.2 ∧ final.1.2.2.val = 0 := by
  cases job with
  | none => exact idleRun_sound hK hmarginLe input 10 hrun hrep howed last
  | some job =>
    cases job with
    | tail => exact tailRun_sound hK hmarginLe input hq (hfront rfl) hrun hrep howed last
    | snoc a =>
      obtain ⟨middle, hsnoc, hidle⟩ := microRun_append hK input _ _ _ _ hrun
      have hmiddle := snocRun_sound hK hmarginLe input hq a hsnoc hrep howed .incLength
      exact idleRun_sound hK hmarginLe input 1 hidle hmiddle.1 (Fin.ext hmiddle.2) last

#print axioms slotTailRun_sound

end QueueSide

/-! ## The rule of a view -/

/-- The control of a view: the gap bit, the job of the queue, the control of the queue. -/
abbrev ViewControl : Type := Bool × Option QueueJob × RTag × RotationPhase × Fin 3

abbrev ViewState : Type := ViewControl × (Fin 12 → STape Γc)

/-- The micro-operation of the queue at a step of the slot. -/
def slotMicroOp (slot : Fin 11) (job : Option QueueJob) : MicroOp :=
  match slot.val with
  | 0 => .incLength
  | step + 1 => (slotTail job).getD step .incLength

theorem slotMicroOp_zero {slot : Fin 11} (hslot : slot.val = 0) (job : Option QueueJob) :
    slotMicroOp slot job = .incLength := by
  unfold slotMicroOp
  rw [hslot]

/-- The queue part of a state of a view. -/
def microStateOf (state : ViewState) : MicroState :=
  (state.1.2.2, fun tape => state.2 (queueTapeOfView tape))

section ViewRule

variable {K : ℕ}

def queueWindowsOfView (windows : Fin 12 → Window Γc K) : Fin 10 → Window Γc K :=
  fun tape => windows (queueTapeOfView tape)

/-- **The next control of a view.**  At step `0` the gap bit and the job are decided from the
windows; at every step the queue control is that of `microRule`. -/
def viewNext (Terminal : Type) (hK : 2 ≤ K) (slot : Fin 11) (command : ViewCommand)
    (control : ViewControl) (windows : Fin 12 → Window Γc K) : ViewControl :=
  if slot.val = 0 then
    ((headMoveOf command control.1).2,
      queueJobOfWindows command control.1 control.2.2.1 windows,
      ((microRule Terminal hK).nq (slotMicroOp slot control.2.1, control.2.2) none
        (queueWindowsOfView windows)).2)
  else
    (control.1, control.2.1,
      ((microRule Terminal hK).nq (slotMicroOp slot control.2.1, control.2.2) none
        (queueWindowsOfView windows)).2)

/-- **The tape actions of a view.**  The ten queue tapes follow `microRule`; the two stack tapes
move at step `0` only. -/
def viewActs (Terminal : Type) (hK : 2 ≤ K) (slot : Fin 11) (command : ViewCommand)
    (control : ViewControl) (windows : Fin 12 → Window Γc K) (tape : Fin 12) : List (Act Γc) :=
  if h : tape.val < 10 then
    (microRule Terminal hK).acts (slotMicroOp slot control.2.1, control.2.2) none
      (queueWindowsOfView windows) ⟨tape.val, h⟩
  else if slot.val = 0 then
    if tape = backTape then backActsOfWindows command control.1 control.2.2.1 windows
    else nearActsOfWindows command control.1 control.2.2.1 windows
  else []

theorem viewActs_length (Terminal : Type) (hK : 2 ≤ K) (slot : Fin 11) (command : ViewCommand)
    (control : ViewControl) (windows : Fin 12 → Window Γc K) (tape : Fin 12) :
    (viewActs Terminal hK slot command control windows tape).length ≤ K := by
  unfold viewActs
  split
  · exact (microRule Terminal hK).len_le _ _ _ _
  · split
    · split
      · exact (cellActsOfTop_length _ _ _).trans hK
      · exact (cellActsOfTop_length _ _ _).trans hK
    · simp

theorem viewActs_queue (Terminal : Type) (hK : 2 ≤ K) (slot : Fin 11) (command : ViewCommand)
    (control : ViewControl) (windows : Fin 12 → Window Γc K) (tape : Fin 10) :
    viewActs Terminal hK slot command control windows (queueTapeOfView tape)
      = (microRule Terminal hK).acts (slotMicroOp slot control.2.1, control.2.2) none
          (queueWindowsOfView windows) tape := by
  have hqueue : (queueTapeOfView tape).val < 10 := tape.isLt
  unfold viewActs
  rw [dif_pos hqueue]
  rfl

theorem viewActs_back (Terminal : Type) (hK : 2 ≤ K) {slot : Fin 11} (hslot : slot.val = 0)
    (command : ViewCommand) (control : ViewControl) (windows : Fin 12 → Window Γc K) :
    viewActs Terminal hK slot command control windows backTape
      = backActsOfWindows command control.1 control.2.2.1 windows := by
  unfold viewActs
  rw [dif_neg (by decide), if_pos hslot, if_pos rfl]

theorem viewActs_near (Terminal : Type) (hK : 2 ≤ K) {slot : Fin 11} (hslot : slot.val = 0)
    (command : ViewCommand) (control : ViewControl) (windows : Fin 12 → Window Γc K) :
    viewActs Terminal hK slot command control windows nearTape
      = nearActsOfWindows command control.1 control.2.2.1 windows := by
  unfold viewActs
  rw [dif_neg (by decide), if_pos hslot, if_neg (by decide)]

theorem viewActs_stack_quiet (Terminal : Type) (hK : 2 ≤ K) {slot : Fin 11}
    (hslot : slot.val ≠ 0) (command : ViewCommand) (control : ViewControl)
    (windows : Fin 12 → Window Γc K) {tape : Fin 12} (hstack : ¬ tape.val < 10) :
    viewActs Terminal hK slot command control windows tape = [] := by
  unfold viewActs
  rw [dif_neg hstack, if_neg hslot]

/-- One step of a view: the next control, and each tape with the margin of `compStep_apply` up
to `TEqG`. -/
def ViewStep (Terminal : Type) (hK : 2 ≤ K) (slot : Fin 11) (command : ViewCommand)
    (state state' : ViewState) : Prop :=
  state'.1 = viewNext Terminal hK slot command state.1
      (fun tape => readWin blankc K (state.2 tape)) ∧
    ∀ tape, K ≤ pos (state.2 tape) → TEqG blankc
      (actList blankc (state.2 tape)
        (viewActs Terminal hK slot command state.1
          (fun tape => readWin blankc K (state.2 tape)) tape))
      (state'.2 tape)

/-- Every tape of a view has the margin. -/
theorem viewMargin (hK : 2 ≤ K) {margin : ℕ} (hmarginLe : K ≤ margin)
    {q : Queue (Fin 2)} {micro : MicroControl}
    {tapes : Fin 12 → STape Γc} {backFull nearFull : List (Option (Fin 2))}
    (hqueue : MicroRep margin q micro (fun tape => tapes (queueTapeOfView tape)))
    (hback : StackTape (tapes backTape) backFull) (hbackLength : K ≤ backFull.length)
    (hnear : StackTape (tapes nearTape) nearFull) (hnearLength : K ≤ nearFull.length) :
    ∀ tape, K ≤ pos (tapes tape) := by
  intro tape
  by_cases hqueueTape : tape.val < 10
  · have htape : tape = queueTapeOfView ⟨tape.val, hqueueTape⟩ := Fin.ext rfl
    have hqueue' : MicroRep margin q (MicroOp.incLength, micro.2)
        (fun tape => tapes (queueTapeOfView tape)) := hqueue
    have hmargin := (microRule_sound (Terminal := Unit) hK hmarginLe hqueue' none
      (fun h => by cases h) (fun h => by cases h) (fun h => by cases h)
      (fun hne => absurd rfl hne) (fun h => by cases h)).1 ⟨tape.val, hqueueTape⟩
    rw [htape]
    exact hmarginLe.trans hmargin
  · have hlt := tape.isLt
    rcases (by omega : tape.val = 10 ∨ tape.val = 11) with hval | hval
    · have htape : tape = backTape := Fin.ext hval
      rw [htape, hback.pos_eq]
      exact hbackLength
    · have htape : tape = nearTape := Fin.ext hval
      rw [htape, hnear.pos_eq]
      exact hnearLength

/-- A dequeue is chosen only when the queue has a head. -/
theorem front_ne_nil_of_tailJob {command : ViewCommand} {move : HeadMove} {v : InputView}
    (htail : queueJobOf command move (viewTops v) = some .tail) : v.far.front ≠ [] := by
  intro hnil
  have hhead : RTQueue.head? v.far = none := by
    unfold RTQueue.head?
    rw [hnil]
    rfl
  have hnoTail : ∀ near : Option (Fin 2),
      queueJobOf command move ⟨v.focus, near, none⟩ ≠ some .tail := by
    intro near
    cases command <;> cases move <;> cases near <;> simp [queueJobOf]
  unfold viewTops at htail
  rw [hhead] at htail
  exact hnoTail _ htail

/-- A view between the decision step and the end of its slot: the gap bit, the job and the two
stacks are settled. -/
structure QuietView (gap : Bool) (job : Option QueueJob)
    (backFull nearFull : List (Option (Fin 2))) (state : ViewState) : Prop where
  gap : state.1.1 = gap
  job : state.1.2.1 = job
  back : StackTape (state.2 backTape) backFull
  near : StackTape (state.2 nearTape) nearFull

/-- A step after the decision step keeps the settled part and is a `MicroStep` of the queue. -/
theorem viewQuietStep (Terminal : Type) (hK : 2 ≤ K) {slot : Fin 11} (hslot : slot.val ≠ 0)
    {command : ViewCommand} {state state' : ViewState}
    (hstep : ViewStep Terminal hK slot command state state')
    {gap : Bool} {job : Option QueueJob} {backFull nearFull : List (Option (Fin 2))}
    (hquiet : QuietView gap job backFull nearFull state)
    (hbackLength : K ≤ backFull.length) (hnearLength : K ≤ nearFull.length) :
    QuietView gap job backFull nearFull state' ∧
      MicroStep hK (none : Option Terminal) (slotMicroOp slot job)
        (microStateOf state) (microStateOf state') := by
  obtain ⟨hcontrol, htapes⟩ := hstep
  unfold viewNext at hcontrol
  rw [if_neg hslot] at hcontrol
  have hbackTape := htapes backTape (by rw [hquiet.back.pos_eq]; exact hbackLength)
  have hnearTape := htapes nearTape (by rw [hquiet.near.pos_eq]; exact hnearLength)
  rw [viewActs_stack_quiet Terminal hK hslot _ _ _ (by decide)] at hbackTape hnearTape
  refine ⟨⟨?_, ?_, hquiet.back.of_teqG hbackTape, hquiet.near.of_teqG hnearTape⟩, ?_, ?_⟩
  · rw [hcontrol]
    exact hquiet.gap
  · rw [hcontrol]
    exact hquiet.job
  · show ((microRule Terminal hK).nq (slotMicroOp slot job, state.1.2.2) none _).2 = state'.1.2.2
    rw [hcontrol, hquiet.job]
    rfl
  · intro hmargin tape
    have htape := htapes (queueTapeOfView tape) (hmargin tape)
    rw [viewActs_queue, hquiet.job] at htape
    exact htape

/-- **The decision step.**  From a represented view the step settles the gap bit, the job and
the two stacks of `viewApply command v`, and is an idle `MicroStep` of the queue. -/
theorem viewDecisionStep (Terminal : Type) (hK : 2 ≤ K) {margin : ℕ} (hmarginLe : K ≤ margin)
    {slot : Fin 11} (hslot : slot.val = 0)
    {command : ViewCommand} {state state' : ViewState}
    (hstep : ViewStep Terminal hK slot command state state')
    {v : InputView} {first : MicroOp} (hcells : ViewCells v)
    (hrep : ViewRep margin v state.1.1 (first, state.1.2.2) state.2) :
    ∃ (job : Option QueueJob) (backBottom nearBottom : List (Option (Fin 2))),
      margin ≤ backBottom.length + 1 ∧ Sealed nearBottom ∧ margin ≤ nearBottom.length ∧
      QuietView (viewApply command v).gap job
        (backStack (viewApply command v) ++ backBottom)
        ((viewApply command v).near ++ nearBottom) state' ∧
      (viewApply command v).far = jobApply job v.far ∧
      (job = some .tail → v.far.front ≠ []) ∧
      MicroStep hK (none : Option Terminal) .incLength (microStateOf state)
        (microStateOf state') := by
  obtain ⟨hcontrol, htapes⟩ := hstep
  unfold viewNext at hcontrol
  rw [if_pos hslot] at hcontrol
  obtain ⟨backBottom0, hbackHeight0, hbackStack0⟩ := hrep.back
  obtain ⟨nearBottom0, -, hnearHeight0, hnearStack0⟩ := hrep.near
  have hmargin := viewMargin hK hmarginLe hrep.queue hbackStack0
    (by simp only [backStack, List.length_append, List.length_cons]; omega) hnearStack0
    (by simp only [List.length_append]; omega)
  have hbackTape := htapes backTape (hmargin backTape)
  have hnearTape := htapes nearTape (hmargin nearTape)
  rw [viewActs_back Terminal hK hslot] at hbackTape
  rw [viewActs_near Terminal hK hslot] at hnearTape
  obtain ⟨⟨backBottom, hbackHeight, hback⟩, ⟨nearBottom, hnearSealed, hnearHeight, hnear⟩,
    hfar, hgap⟩ := viewDecision_sound hmarginLe hcells hrep command hbackTape hnearTape
  refine ⟨_, backBottom, nearBottom, hbackHeight, hnearSealed, hnearHeight,
    ⟨?_, ?_, hback, hnear⟩, hfar, ?_, ?_, ?_⟩
  · rw [hcontrol]
    exact hgap.symm
  · rw [hcontrol]
  · intro htail hnil
    unfold queueJobOfWindows at htail
    rw [viewTopsOfWindows_eq hmarginLe hcells hrep] at htail
    exact front_ne_nil_of_tailJob htail hnil
  · show ((microRule Terminal hK).nq (MicroOp.incLength, state.1.2.2) none _).2 = state'.1.2.2
    rw [hcontrol, slotMicroOp_zero hslot]
    rfl
  · intro hqueueMargin tape
    have htape := htapes (queueTapeOfView tape) (hqueueMargin tape)
    rw [viewActs_queue, slotMicroOp_zero hslot] at htape
    exact htape

/-- Steps `start + 1`–`10` of a slot are a `MicroRun` of the queue along the rest of the job. -/
theorem viewQuietRun (Terminal : Type) (hK : 2 ≤ K) (commands : ℕ → ViewCommand)
    (states : ℕ → ViewState)
    (hsteps : ∀ (step : ℕ) (hstep : step < 11),
      ViewStep Terminal hK ⟨step, hstep⟩ (commands step) (states step) (states (step + 1)))
    {gap : Bool} {job : Option QueueJob} {backFull nearFull : List (Option (Fin 2))}
    (hbackLength : K ≤ backFull.length) (hnearLength : K ≤ nearFull.length) :
    ∀ (count start : ℕ), start + count = 10 →
      QuietView gap job backFull nearFull (states (start + 1)) →
      MicroRun hK (none : Option Terminal) ((slotTail job).drop start)
          (microStateOf (states (start + 1))) (microStateOf (states 11)) ∧
        QuietView gap job backFull nearFull (states 11)
  | 0, start, hstart, hquiet => by
    obtain rfl : start = 10 := by omega
    rw [List.drop_eq_nil_of_le (by rw [slotTail_length])]
    exact ⟨MicroRun.nil _, hquiet⟩
  | count + 1, start, hstart, hquiet => by
    have hslot : start + 1 < 11 := by omega
    obtain ⟨hquiet', hmicro⟩ := viewQuietStep Terminal hK (slot := ⟨start + 1, hslot⟩)
      (by simp) (hsteps (start + 1) hslot) hquiet hbackLength hnearLength
    obtain ⟨hrun, hfinal⟩ := viewQuietRun Terminal hK commands states hsteps hbackLength
      hnearLength count (start + 1) (by omega) hquiet'
    have hlt : start < (slotTail job).length := by rw [slotTail_length]; omega
    have hop : slotMicroOp ⟨start + 1, hslot⟩ job = (slotTail job)[start] := by
      show (slotTail job).getD start .incLength = _
      rw [List.getD_eq_getElem _ _ hlt]
    rw [List.drop_eq_getElem_cons hlt, ← hop]
    exact ⟨MicroRun.cons hmicro hrun, hfinal⟩

/-- **One slot of a view.**  Eleven steps of the rule take a representation of `v` to a
representation of `viewApply (commands 0) v`: only the command of step `0` is used, so the
commands of the later steps are free.  Nothing is owed at the end, so slots compose. -/
theorem viewSlot_sound (Terminal : Type) (hK : 2 ≤ K) {margin : ℕ} (hmarginLe : K ≤ margin)
    {v : InputView} (hwf : WF v)
    (hcells : ViewCells v) (commands : ℕ → ViewCommand) (states : ℕ → ViewState)
    (hsteps : ∀ (step : ℕ) (hstep : step < 11),
      ViewStep Terminal hK ⟨step, hstep⟩ (commands step) (states step) (states (step + 1)))
    {first : MicroOp}
    (hrep : ViewRep margin v (states 0).1.1 (first, (states 0).1.2.2) (states 0).2)
    (howed : (states 0).1.2.2.2.2 = 0) (last : MicroOp) :
    ViewRep margin (viewApply (commands 0) v) (states 11).1.1 (last, (states 11).1.2.2)
        (states 11).2 ∧
      (states 11).1.2.2.2.2.val = 0 := by
  obtain ⟨job, backBottom, nearBottom, hbackHeight, hnearSealed, hnearHeight, hquiet, hfar,
    hfront, hidle⟩ := viewDecisionStep Terminal hK hmarginLe (slot := ⟨0, by omega⟩) rfl
      (hsteps 0 (by omega)) hcells hrep
  have hbackLength : K ≤ (backStack (viewApply (commands 0) v) ++ backBottom).length := by
    simp only [backStack, List.length_append, List.length_cons]; omega
  have hnearLength : K ≤ ((viewApply (commands 0) v).near ++ nearBottom).length := by
    simp only [List.length_append]; omega
  obtain ⟨hrun, hfinal⟩ := viewQuietRun Terminal hK commands states hsteps hbackLength
    hnearLength 10 0 (by omega) hquiet
  have hone := idleRun_sound hK hmarginLe (none : Option Terminal) 1
    (MicroRun.cons hidle (MicroRun.nil _)) hrep.queue howed .incLength
  have hqueue := slotTailRun_sound hK hmarginLe (none : Option Terminal) hwf job hfront hrun hone.1
    (Fin.ext hone.2) last
  refine ⟨⟨hfinal.gap, ?_, ⟨backBottom, hbackHeight, hfinal.back⟩,
    ⟨nearBottom, hnearSealed, hnearHeight, hfinal.near⟩⟩, hqueue.2⟩
  rw [hfar]
  exact hqueue.1

#print axioms viewSlot_sound

/-! ## A view inside a larger machine -/

/-- `compStep_apply`, one tape at a time: a tape with the margin follows its actions, whatever
the other tapes do. -/
theorem compStep_apply_tape {Terminal Q : Type} {tapeCount : ℕ}
    (R : ActRule Terminal Q Γc tapeCount K) (x : Q × (Fin tapeCount → STape Γc))
    (input : Option Terminal) (tape : Fin tapeCount) (hmargin : K ≤ pos (x.2 tape)) :
    TEqG blankc
      (actList blankc (x.2 tape)
        (R.acts x.1 input (fun tape => readWin blankc K (x.2 tape)) tape))
      (((compStep R).apply blankc x input).2 tape) := by
  show TEqG blankc _ (sweep blankc K (x.2 tape) _ _)
  exact teq_sweep_actList blankc K (x.2 tape) _ (R.len_le _ _ _ _) hmargin

/-- **A real step of a larger machine is a `ViewStep` of each view it contains**: twelve of its
tapes (`embed`) and a part of its control (`project`) on which the rule agrees with
`viewNext` / `viewActs`. -/
theorem viewStep_of_apply {Terminal Q : Type} {tapeCount : ℕ} (ViewTerminal : Type)
    (hK : 2 ≤ K) (R : ActRule Terminal Q Γc tapeCount K) (embed : Fin 12 → Fin tapeCount)
    (project : Q → ViewControl) (slot : Fin 11) (command : ViewCommand)
    (x : Q × (Fin tapeCount → STape Γc)) (input : Option Terminal)
    (hnq : project (R.nq x.1 input (fun tape => readWin blankc K (x.2 tape)))
      = viewNext ViewTerminal hK slot command (project x.1)
          (fun tape => readWin blankc K (x.2 (embed tape))))
    (hacts : ∀ tape, R.acts x.1 input (fun tape => readWin blankc K (x.2 tape)) (embed tape)
      = viewActs ViewTerminal hK slot command (project x.1)
          (fun tape => readWin blankc K (x.2 (embed tape))) tape) :
    ViewStep ViewTerminal hK slot command (project x.1, fun tape => x.2 (embed tape))
      (project ((compStep R).apply blankc x input).1,
        fun tape => ((compStep R).apply blankc x input).2 (embed tape)) := by
  refine ⟨?_, fun tape hmargin => ?_⟩
  · exact hnq
  · show TEqG blankc (actList blankc (x.2 (embed tape)) _) _
    rw [← hacts tape]
    exact compStep_apply_tape R x input (embed tape) hmargin

#print axioms viewStep_of_apply

end ViewRule

end PalPeg.ConcreteLocalMachine
