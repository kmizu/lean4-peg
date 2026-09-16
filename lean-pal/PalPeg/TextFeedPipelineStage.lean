import PalPeg.TextFeedPipelineParameters

/-! A single-stage execution from preparation through startup and ordinary
matching rounds. No Complete, Macro, or GS invariant is a caller premise. -/
set_option autoImplicit false
namespace PalPeg.TextFeedPipelineStage
open PalPeg.Program PalPeg.TextFeedControl
open PalPeg.TextFeedPipelineOutputBudget
open PalPeg.TextFeedPipelineOutputBirth
open PalPeg.TextFeedPipelineOutputPrepFinish (finishAt)
variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (TextFeedPipelineControl.TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineControl.TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (TextFeedPipelineControl.Outer e leftSym R rate) := Classical.decEq _

def Running (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k)
    (w Text : List (Fin k)) (L : ℕ) (word tail : List Terminal) : Prop :=
  ∃ before a after J, ∃ (ops : List (Option Terminal)), ∃ pre post N,
    word = before ++ a :: after ∧ J ≤ workerRate 8 ∧ ops.length ≤ 775 ∧ pre.length ≤ 4 ∧
    after ++ tail = pre ++ post ∧ ops.filterMap id = pre ∧ N ≤ workerRate 8 ∧
    ∀ (as : List Terminal), as ≠ [] → before.length + 1 + pre.length + as.length ≤ Text.length →
      (∀ j c, as[j]? = some c → Text[before.length + 1 + pre.length + j]? = some (enc c)) →
      ((TextFeedPipelineOutput.machine e leftSym enc (workerRate 8) 8).accepting
        (as.foldl (TextFeedPipelineOutput.machine e leftSym enc (workerRate 8) 8).sRound
          ((List.replicate (N * 96) none).foldl
            (TextFeedPipelineOutput.machine e leftSym enc (workerRate 8) 8).sMicroStep
            (ops.foldl (TextFeedPipelineOutput.machine e leftSym enc (workerRate 8) 8).sMicroStep
              (finishAt e leftSym enc (workerRate 8) 8 before a J
                (start e leftSym (workerRate 8) 8 w L 0))))).state = true ↔
        ∃ i, i + L = before.length + 1 + pre.length + as.length ∧
          OccAt (PrepInstances.stagePat w L) Text i)

theorem ready_running (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k)
    (w Text : List (Fin k)) (L : ℕ) (hL : 0 < L) (hw : L ≤ w.length)
    (h : TextFeedPipelinePrefixWindow.Safe e (PrepInstances.stagePat w L) Text)
    (word tail : List Terminal)
    (hready : ObservedReady e leftSym enc (workerRate 8) 8
      ((PrepInstances.stagePat w L).take (PrepInstances.prepRes w L).1)
      ((PrepInstances.stagePat w L).drop (PrepInstances.prepRes w L).1) Text
      (PrepInstances.prepRes w L).2.1 (PrepInstances.prepRes w L).2.2 word
      (start e leftSym (workerRate 8) 8 w L 0))
    (htail : 4 ≤ tail.length) (hlen : (word ++ tail).length ≤ Text.length)
    (ha : ∀ (j : ℕ) a, (word ++ tail)[j]? = some a → Text[j]? = some (enc a)) :
    Running e leftSym enc w Text L word tail := by
  obtain ⟨before, a, after, J, ops, pre, post, y, he, hJ, hsize, hpre, hsplit, hinput,
    hsim, m, hp, hq, hz, hev, hcredit, hfirst⟩ :=
    TextFeedPipelineOutputBoot.ready_boot h.code (workerRate_pos 8) enc h.mark_blank h.blank_text h.mark_text
      word tail (start e leftSym (workerRate 8) 8 w L 0) rfl rfl rfl hready htail hlen ha
  let N := TextFeedPipelinePrefixResume.remaining (TextFeedPipelineObserved.project y)
  have hN : N ≤ workerRate 8 := by
    change (if y.1.1.1.1 = 0 then 0 else workerRate 8 + 1 - y.1.1.1.1.val) ≤ workerRate 8
    by_cases heq : y.1.1.1.1 = 0
    · simp only [if_pos heq, Nat.zero_le]
    · simp only [if_neg heq]
      have hv : y.1.1.1.1.val ≠ 0 := fun hh => heq (Fin.ext hh)
      omega
  refine ⟨before, a, after, J, ops, pre, post, N, he, hJ, hsize, hpre, hsplit, hinput, hN, ?_⟩
  intro as hne hn has
  have hh := TextFeedPipelineParameters.stage_resumed_iff e leftSym enc w Text L
    (before.length + 1 + pre.length) hL hw h (TextFeedPipelineObserved.project y) m hp hq hz
    as hne hn has hfirst hcredit y.1.2.1 y.1.2.2 _ hsim
  simpa only [PrepInstances.stagePat_length hw] using hh

/-- From the concrete unpadded preparation seed to suffix recognition on
every subsequent nonempty valid input prefix. The caller supplies only
input slices, size/symbol conditions, not intermediate machine invariants. -/
theorem prepared_running (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k)
    (w Text : List (Fin k)) (L : ℕ) (hL : 32 ≤ L) (hw : L ≤ w.length)
    (hfresh : leftSym ∉ w)
    (h : TextFeedPipelinePrefixWindow.Safe e (PrepInstances.stagePat w L) Text) :
    let d := PrepInstances.prepRes w L
    ∃ cost, cost ≤ TextFeedStartupBudget.slope 8 * L + TextFeedStartupBudget.offset 8 ∧
      ∀ (before : List Terminal) (a : Terminal), before.length = cost / workerRate 8 →
        TextFeedPrefixDeadline.Valid Text 0 ((before ++ [a]).map enc) →
        ∀ (waitWord runWord : List Terminal),
          waitWord.length = waiting (workerRate 8) cost d.1 0 →
          runWord.length = windows (workerRate 8) (5 * d.1 + 2) →
          before.length + 1 + waitWord.length + runWord.length ≤ Text.length →
          (∀ j b, waitWord[j]? = some b → Text[before.length + 1 + j]? = some (enc b)) →
          (∀ j b, runWord[j]? = some b → Text[before.length + 1 + waitWord.length + j]? = some (enc b)) →
          ∀ (tail : List Terminal), 4 ≤ tail.length →
            ((before ++ a :: (waitWord ++ runWord)) ++ tail).length ≤ Text.length →
            (∀ (j : ℕ) b, ((before ++ a :: (waitWord ++ runWord)) ++ tail)[j]? = some b → Text[j]? = some (enc b)) →
            Running e leftSym enc w Text L (before ++ a :: (waitWord ++ runWord)) tail := by
  obtain ⟨cost, hcost, hr⟩ := seed_timed leftSym enc 8 w Text L (by decide) hL hw hfresh h
  refine ⟨cost, hcost, ?_⟩
  intro before a hbefore hvalid waitWord runWord hwait hrun hlen hwa hra tail htail htotal hinput
  exact ready_running e leftSym enc w Text L (by omega) hw h _ tail
    (hr before a hbefore hvalid waitWord runWord hwait hrun hlen hwa hra) htail htotal hinput

/-- info: 'PalPeg.TextFeedPipelineStage.prepared_running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prepared_running
end PalPeg.TextFeedPipelineStage
