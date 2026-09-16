import PalPeg.TextFeedPipelineOutputBudget
import PalPeg.TextFeedUnpadded
import PalPeg.TextFeedPipelineDirection

/-! A fresh 39-tape pipeline uses only an already-arrived pattern and
constant initialization. Future-length padding belongs to its proof model. -/
set_option autoImplicit false
namespace PalPeg.TextFeedPipelineOutputBirth
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.TextFeedControl
open PalPeg.PatternTapes PalPeg.PatternProg
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.TextFeedInit
open PalPeg.TextFeedPipelineBank PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelinePrepInput
open PalPeg.TextFeedPipelineOutputPrepFinish (Config finishAt)
open PalPeg.TextFeedPipelineOutputBudget

variable {k : ℕ} {Terminal : Type}
noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

noncomputable def seed (e : Env k) (leftSym : Fin k) (w : List (Fin k)) (L padding : ℕ) :
    Fin 39 → STape (Fin k) :=
  extend prepSlot (TSg (StageBirth.birthTapes e.blank e.mark leftSym w L padding))
    (extend DualQueueShared.pairSlot (DualQueueInput.tapes (DualQueue.blankPair e.blank) e.blank)
      (blankBundle e.blank 39))

theorem seed_take (e : Env k) (leftSym : Fin k) (w : List (Fin k)) (L padding : ℕ) :
    seed e leftSym w L padding = seed e leftSym (w.take L) L padding := by
  have ht : StageBirth.birthTapes e.blank e.mark leftSym w L padding =
      StageBirth.birthTapes e.blank e.mark leftSym (w.take L) L padding := by
    funext j
    simp only [StageBirth.birthTapes, StageBirth.copyTape, List.take_take, Nat.min_self]
  unfold seed
  rw [ht]

theorem seed_prep (e : Env k) (leftSym : Fin k) (w : List (Fin k)) (L padding : ℕ) :
    prepView (seed e leftSym w L padding) = TSg (StageBirth.birthTapes e.blank e.mark leftSym w L padding) := by
  funext j
  exact extend_ι prepSlot _ _ j

theorem seed_queues (e : Env k) (leftSym : Fin k) (w : List (Fin k)) (L padding : ℕ) :
    QueuesAt e true (seed e leftSym w L padding) empty empty e.blank := by
  refine ⟨rfl, rfl, ?_⟩
  exact (TextFeedPipelineArrival.prep_preserves_inputs _ _).trans (pairView_extend _ _)

theorem seed_blankEq (e : Env k) (leftSym : Fin k) (w : List (Fin k)) (L padding : ℕ) :
    ∀ j, STape.BlankEq e.blank (seed e leftSym w L 0 j) (seed e leftSym w L padding j) := by
  intro j
  have hh := TextFeedPrepare.birthTapes_blankEq e.blank e.mark leftSym w L padding
  unfold seed extend
  cases hp : proj prepSlot j with
  | none => exact STape.BlankEq.refl _ _
  | some i => exact hh i

noncomputable def start (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (w : List (Fin k)) (L padding : ℕ) : Config e leftSym R rate :=
  ⟨((TextFeedPipelineOutput.initial e leftSym R rate, 0), 0), seed e leftSym w L padding⟩

theorem seed_cell (e : Env k) (leftSym : Fin k) (w : List (Fin k)) (L padding : ℕ) :
    TextFeedPipelineDirection.Cell (seed e leftSym w L padding 38) := by
  simp only [seed, extend, TextFeedPipelineDirection.prep_omits,
    DualQueueShared.reserved_omitted (j := 38) (Or.inr rfl)]
  exact ⟨e.blank, rfl⟩

theorem finishAt_dir (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k)
    (R rate J : ℕ) (hJ : J ≤ R) (w : List (Fin k)) (L padding : ℕ)
    (word : List Terminal) (a : Terminal) :
    ((finishAt e leftSym enc R rate word a J (start e leftSym R rate w L padding)).tape 38).applyAction
      e.blank (e.mark, .stay) = GSVProgZLoop.dirTape e.blank e.mark true 0 :=
  TextFeedPipelineDirection.finishAt_dir e leftSym enc R rate J hJ
    (TextFeedPipelineOutput.initial e leftSym R rate) (seed e leftSym w L padding)
    (seed_cell e leftSym w L padding) word a

theorem step_safe (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (x : TextFeedPipelineOutput.State e leftSym R rate × (Fin 39 → STape (Fin k)))
    (h : TextFeedPipelineSourceSafety.SourceSafe e leftSym rate x.1.1.1.2.2) :
    TextFeedPipelineSourceSafety.SourceSafe e leftSym rate
      (TextFeedPipelineOutput.step (Terminal := Terminal) e leftSym R rate x).1.1.1.2.2 := by
  have hh := TextFeedPipelineSourceSafety.run_safe (Terminal := Terminal) e leftSym R rate (x.1.1, x.2) h
  simp only [TextFeedPipelineOutput.step, TextFeedPipelineOutput.sample]
  split <;> exact hh

theorem steps_safe (e : Env k) (leftSym : Fin k) (R rate N : ℕ)
    (x : TextFeedPipelineOutput.State e leftSym R rate × (Fin 39 → STape (Fin k)))
    (h : TextFeedPipelineSourceSafety.SourceSafe e leftSym rate x.1.1.1.2.2) :
    TextFeedPipelineSourceSafety.SourceSafe e leftSym rate
      ((TextFeedPipelineOutput.step (Terminal := Terminal) e leftSym R rate)^[N] x).1.1.1.2.2 := by
  induction N with
  | zero => exact h
  | succ N ih =>
    rw [Function.iterate_succ_apply']
    exact step_safe e leftSym R rate _ ih

theorem rounds_safe (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ)
    (word : List Terminal) (q : TextFeedPipelineOutput.State e leftSym R rate)
    (T : Fin 39 → STape (Fin k))
    (h : TextFeedPipelineSourceSafety.SourceSafe e leftSym rate q.1.1.2.2) :
    let y := word.foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sRound ⟨((q, 0), 0), T⟩
    y.state.1.2 = 0 ∧ y.state.2 = 0 ∧
      TextFeedPipelineSourceSafety.SourceSafe e leftSym rate y.state.1.1.1.1.2.2 := by
  induction word generalizing q T with
  | nil => exact ⟨rfl, rfl, h⟩
  | cons a word ih =>
    simp only [List.foldl_cons, TextFeedPipelineOutput.machine_round]
    exact ih _ _ (steps_safe e leftSym R rate (R + 1) _ h)

/-- The actual partial-frame preparation endpoint inherits source safety
from the fixed initial control, independently of padding or input length. -/
theorem finishAt_safe (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k)
    (R rate J : ℕ) (hJ : J ≤ R) (w : List (Fin k)) (L padding : ℕ)
    (word : List Terminal) (a : Terminal) :
    TextFeedPipelineSourceSafety.SourceSafe e leftSym rate
      (finishAt e leftSym enc R rate word a J (start e leftSym R rate w L padding)).state.1.1.1.1.2.2 := by
  let y := word.foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sRound
    (start e leftSym R rate w L padding)
  obtain ⟨h₁, h₂, hs⟩ := rounds_safe e leftSym enc R rate word
    (TextFeedPipelineOutput.initial e leftSym R rate) (seed e leftSym w L padding)
    (TextFeedPipelineSourceSafety.start_safe e leftSym rate)
  have hy : y = ⟨((y.state.1.1, 0), 0), y.tape⟩ := by
    have he : y.state = ((y.state.1.1, 0), 0) := Prod.ext (Prod.ext rfl h₁) h₂
    rw [← he]
  change TextFeedPipelineSourceSafety.SourceSafe e leftSym rate
    ((some a :: List.replicate ((J + 1) * 96) none).foldl
      (TextFeedPipelineOutput.machine e leftSym enc R rate).sMicroStep y).state.1.1.1.1.2.2
  rw [hy, TextFeedPipelineOutputPrepFinish.machine_partial e leftSym enc R rate J hJ]
  exact steps_safe e leftSym R rate (J + 1) _ hs

/-- All future input rounds and partial microstep executions have exactly
the same finite control, including output and clocks, with or without padding. -/
theorem future_blankEq (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ)
    (w : List (Fin k)) (L padding : ℕ) (word : List Terminal) (ops : List (Option Terminal)) :
    ConfigBlankEq e.blank
      (ops.foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sMicroStep
        (word.foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sRound (start e leftSym R rate w L 0)))
      (ops.foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sMicroStep
        (word.foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sRound (start e leftSym R rate w L padding))) := by
  apply StructuredMachine.microSteps_blankEq
  apply StructuredMachine.runFrom_blankEq
  exact ⟨rfl, seed_blankEq e leftSym w L padding⟩

theorem finishAt_blankEq (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate J : ℕ)
    (w : List (Fin k)) (L padding : ℕ) (word : List Terminal) (a : Terminal) :
    ConfigBlankEq e.blank
      (finishAt e leftSym enc R rate word a J (start e leftSym R rate w L 0))
      (finishAt e leftSym enc R rate word a J (start e leftSym R rate w L padding)) :=
  future_blankEq e leftSym enc R rate w L padding word (some a :: List.replicate ((J + 1) * 96) none)

def ObservedReady (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ)
    (u v Text : List (Fin k)) (p r : ℕ) (word : List Terminal) (x : Config e leftSym R rate) : Prop :=
  ∃ before a after J y, word = before ++ a :: after ∧ J ≤ R ∧
    ConfigBlankEq e.blank (finishAt e leftSym enc R rate before a J x) y ∧
    TextFeedPipelinePrefixFedPhysical.Complete e leftSym R rate u v Text rate p r
      (before.length + 1) (y.state.1.1.1, y.tape) ∧
    (rate + 1) * (before.length + 1 + 4) ≤ (rate + 1) * u.length + rate * v.length ∧
    TextFeedPipelineSourceSafety.SourceSafe e leftSym rate y.state.1.1.1.1.2.2 ∧
    (y.tape 38).applyAction e.blank (e.mark, .stay) = GSVProgZLoop.dirTape e.blank e.mark true 0

theorem ready_unpadded {e : Env k} {leftSym : Fin k} {R rate L padding p r : ℕ}
    (enc : Terminal → Fin k) (w u v Text : List (Fin k)) (word : List Terminal)
    (h : ReadyToBoot e leftSym enc R rate u v Text p r 0 word (start e leftSym R rate w L padding)) :
    ObservedReady e leftSym enc R rate u v Text p r word (start e leftSym R rate w L 0) := by
  obtain ⟨before, a, after, J, he, hJ, hcomplete, hcredit⟩ := h
  refine ⟨before, a, after, J, _, he, hJ,
    finishAt_blankEq e leftSym enc R rate J w L padding before a, ?_, ?_,
    finishAt_safe e leftSym enc R rate J hJ w L padding before a,
    finishAt_dir e leftSym enc R rate J hJ w L padding before a⟩
  · simpa only [Nat.zero_add] using hcomplete
  · simpa only [Nat.zero_add] using hcredit

/-- A fresh unpadded pipeline gets the prep and empty-FIFO premises from
its concrete seed. Text.length selects only a proof representative, never
an actual initial tape, program, rate or input symbol. -/
theorem seed_timed {e : Env k} (leftSym : Fin k) (enc : Terminal → Fin k) (rate : ℕ)
    (w Text : List (Fin k)) (L : ℕ) (hrate : 2 ≤ rate) (hL : 32 ≤ L) (hw : L ≤ w.length)
    (hfresh : leftSym ∉ w)
    (h : TextFeedPipelinePrefixWindow.Safe e (PrepInstances.stagePat w L) Text) :
    let d := PrepInstances.prepRes w L
    ∃ cost, cost ≤ TextFeedStartupBudget.slope rate * L + TextFeedStartupBudget.offset rate ∧
      ∀ (before : List Terminal) (a : Terminal), before.length = cost / workerRate rate →
        TextFeedPrefixDeadline.Valid Text 0 ((before ++ [a]).map enc) →
        ∀ (waitWord runWord : List Terminal),
          waitWord.length = waiting (workerRate rate) cost d.1 0 →
          runWord.length = windows (workerRate rate) (5 * d.1 + 2) →
          before.length + 1 + waitWord.length + runWord.length ≤ Text.length →
          (∀ j b, waitWord[j]? = some b → Text[before.length + 1 + j]? = some (enc b)) →
          (∀ j b, runWord[j]? = some b →
            Text[before.length + 1 + waitWord.length + j]? = some (enc b)) →
          ObservedReady e leftSym enc (workerRate rate) rate
            ((w.take L).reverse.take d.1) ((w.take L).reverse.drop d.1) Text d.2.1 d.2.2
            (before ++ a :: (waitWord ++ runWord)) (start e leftSym (workerRate rate) rate w L 0) := by
  dsimp only
  have hpre := StageBirth.birthTapes_prepPre (blank := e.blank) (mark := e.mark)
    (Text := Text) (by omega : 0 < L) hw hfresh (Nat.le_refl Text.length)
  obtain ⟨cost, hcost, hready⟩ := setup_timed leftSym enc rate
    (TextFeedPipelineOutput.initial e leftSym (workerRate rate) rate).1
    (seed e leftSym w L Text.length) (initialBank_boundary _) rfl
    (seed_queues e leftSym w L Text.length) rfl (seed_prep e leftSym w L Text.length)
    hpre h inv_empty (by simp [toList_empty]) inv_empty (by simp [toList_empty])
    .front false hrate hL hw (by omega : 0 ≤ L / 8)
  simp only [Nat.zero_add] at hready
  refine ⟨cost, hcost, ?_⟩
  intro before a hbefore hvalid waitWord runWord hwait hrun hlen hwa hra
  apply ready_unpadded (padding := Text.length) enc w
  exact hready before a hbefore hvalid waitWord runWord hwait hrun hlen hwa hra

/-- info: 'PalPeg.TextFeedPipelineOutputBirth.seed_timed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms seed_timed
/-- info: 'PalPeg.TextFeedPipelineOutputBirth.finishAt_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finishAt_safe
/-- info: 'PalPeg.TextFeedPipelineOutputBirth.finishAt_blankEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finishAt_blankEq
/-- info: 'PalPeg.TextFeedPipelineOutputBirth.seed_queues' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms seed_queues
end PalPeg.TextFeedPipelineOutputBirth
