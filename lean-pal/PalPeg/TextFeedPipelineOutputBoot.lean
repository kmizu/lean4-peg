import PalPeg.TextFeedPipelineOutputBirth

/-! Preparation and verifier startup share the same real machine, clocks,
and input stream. Padding is retained only in a simulated representative. -/
set_option autoImplicit false
namespace PalPeg.TextFeedPipelineOutputBoot
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.TextFeedControl PalPeg.TextFeedPipelineOutputBirth
open PalPeg.TextFeedPipelineOutputPrepFinish (Config finishAt)
open PalPeg.TextFeedPipelineOutputClock (embed)
variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (TextFeedPipelineControl.TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineControl.TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (TextFeedPipelineControl.Outer e leftSym R rate) := Classical.decEq _

theorem ready_boot {e : Env k} (hc : Function.Injective e.code)
    {leftSym : Fin k} {R rate p r : ℕ} (hR : 0 < R) (enc : Terminal → Fin k)
    {u v Text : List (Fin k)} (hmb : e.mark ≠ e.blank) (hb : e.blank ∉ Text) (hm : e.mark ∉ Text)
    (word tail : List Terminal) (x : Config e leftSym R rate)
    (hz : x.state.1.1.1.1.1 = 0) (h96 : x.state.1.2 = 0) (hout : x.state.2 = 0)
    (hready : ObservedReady e leftSym enc R rate u v Text p r word x)
    (htail : 4 ≤ tail.length) (hlen : (word ++ tail).length ≤ Text.length)
    (ha : ∀ (j : ℕ) a, (word ++ tail)[j]? = some a → Text[j]? = some (enc a)) :
    ∃ before a after J, ∃ (ops : List (Option Terminal)), ∃ pre post y,
      word = before ++ a :: after ∧ J ≤ R ∧ ops.length ≤ 775 ∧ pre.length ≤ 4 ∧
      after ++ tail = pre ++ post ∧ ops.filterMap id = pre ∧
      ConfigBlankEq e.blank
        (ops.foldl (TextFeedPipelineOutput.machine e leftSym enc R rate).sMicroStep
          (finishAt e leftSym enc R rate before a J x)) (embed y) ∧
      ∃ m : TextFeedPipelineService.Macro e leftSym R rate Text u v p r
          (before.length + 1 + pre.length) (TextFeedPipelineObserved.project y),
        m.z.1.pos = u.length ∧ m.z.1.q = 0 ∧ m.z.2 = ⟨0, 0, 0, true⟩ ∧
        m.events = [] ∧ TextFeedPipelineService.target rate v (before.length + 1 + pre.length) ≤ m.score ∧
        y.1.1.1.2.1 = false := by
  obtain ⟨before, a, after, J, z, he, hJ, hsim, hcomplete, hcredit, hs, hd⟩ := hready
  have hclock := TextFeedPipelineOutputClock.finishAt_embed e leftSym enc R rate J hJ x hz h96 hout before a
  have hzembed : z = embed (z.state.1.1, z.tape) := by
    have hstate := congrArg SConfig.state hclock
    rw [hsim.1] at hstate
    change z.state = ((z.state.1.1, 0), TextFeedPipelineOutputClock.clock z.state.1.1.1.1.1) at hstate
    change z = ⟨((z.state.1.1, 0), TextFeedPipelineOutputClock.clock z.state.1.1.1.1.1), z.tape⟩
    rw [← hstate]
  have hn : before.length + 1 + (after ++ tail).length ≤ Text.length := by
    rw [he] at hlen
    simp only [List.length_append, List.length_cons] at hlen ⊢
    omega
  have hfuture : ∀ j b, (after ++ tail)[j]? = some b →
      Text[before.length + 1 + j]? = some (enc b) := by
    intro j b hj
    apply ha (before.length + 1 + j) b
    rw [he]
    have hidx : before.length + 1 + j - before.length = j + 1 := by omega
    simpa only [List.cons_append, List.append_assoc, List.getElem?_append_right
      (by omega : before.length ≤ before.length + 1 + j),
      hidx, List.getElem?_cons_succ] using hj
  obtain ⟨ops, pre, post, y, hsize, hpre, hsplit, hinput, hrun, m, hpos, hq, hmz, hev, hscore, hf⟩ :=
    TextFeedPipelineOutputClock.boot_any_phase hc hR enc (z.state.1.1, z.tape)
      hcomplete hs hmb hb hm hd (after ++ tail) (by simp only [List.length_append]; omega) hn hfuture hcredit
  refine ⟨before, a, after, J, ops, pre, post, y, he, hJ, hsize, hpre, hsplit, hinput, ?_,
    m, hpos, hq, hmz, hev, hscore, hf⟩
  have hh := StructuredMachine.microSteps_blankEq
    (TextFeedPipelineOutput.machine e leftSym enc R rate) ops hsim
  rw [hzembed, hrun] at hh
  exact hh

/-- info: 'PalPeg.TextFeedPipelineOutputBoot.ready_boot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ready_boot
end PalPeg.TextFeedPipelineOutputBoot
