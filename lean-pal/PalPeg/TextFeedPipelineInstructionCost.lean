import PalPeg.TextFeedPipelineMacroResult
import PalPeg.TextFeedPipelineFrameCost

/-! Every coupled instruction is a real GS trace action. Its count is
bounded by the existing terminating program's cost, even before return. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineInstructionCost
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.TextFeedControl
open PalPeg.TextFeedPipelineFrames PalPeg.TextFeedPipelineCoupled PalPeg.TextFeedPipelineIdealEngine
open PalPeg.TextFeedPipelineFrameCost
variable {k : ℕ}

theorem follows_trace_length (e : Env k) {u v : Snapshot k} {ws : List Event}
    (h : Follows e u ws v) :
    (trace (engine e) e.blank (semanticInputs ws) (erase u.frames, bundle u.ideal u.dir)).length =
      (semanticInputs ws).length := by
  induction h with
  | nil => rfl
  | stutter hf hi hd _ ih => simpa only [hf, hi, hd] using ih
  | @step u v z w ws had ht ih =>
    cases w with
    | instruction a =>
      have hc : stepStack (PalPeg.TextFeedPipelineGuardAgreement.idealEval e u.ideal u.dir)
          (erase u.frames) = (erase v.frames, some a) :=
        (ProgLangControlSteps.selected_iff _ _ _ _).mpr had.control
      rw [semanticInputs, trace_cons, eval_bundle, hc, instruction_step e a had]
      simp only [List.length_append, List.length_cons, List.length_nil, ih]
      omega
    | feed1 | feed2 | idle | halt =>
      have hs := silent_step e _ (by intro a ha; cases ha) had
      change (trace (engine e) e.blank (semanticInputs ws)
        (erase u.frames, bundle u.ideal u.dir)).length = (semanticInputs ws).length
      rw [trace_congr hs.2, hs.1]
      exact ih

theorem trace_bound {e : Env k} {p : GSVProgZLoop.DProg}
    {T U : Fin 11 → STape (Fin k)} {cost : ℕ}
    (hr : GSVProgZLoop.RunsTo (engine e) e.blank p T U cost) (N : ℕ) :
    (trace (engine e) e.blank (List.replicate N none) ([p], T)).length ≤ cost := by
  obtain ⟨acts, he, _, hcost⟩ := hr
  obtain ⟨ha, s, hs, heq⟩ := he [] (List.replicate cost none)
    (by simp only [List.length_replicate, hcost])
  simp only [List.append_nil] at ha hs heq
  have htotal : trace (engine e) e.blank (List.replicate (N + cost) none) ([p], T) = acts := by
    rw [Nat.add_comm N cost, List.replicate_add, trace_append, ha, hs, trace_congr heq]
    simp
  have hprefix : (trace (engine e) e.blank (List.replicate N none) ([p], T)).length ≤
      (trace (engine e) e.blank (List.replicate (N + cost) none) ([p], T)).length := by
    rw [List.replicate_add, trace_append, List.length_append]
    omega
  simpa only [htotal, hcost] using hprefix

theorem follows_bound {e : Env k} {u v : Snapshot k} {ws : List Event}
    {p : GSVProgZLoop.DProg} {U : Fin 11 → STape (Fin k)} {cost : ℕ}
    (h : Follows e u ws v) (hc : erase u.frames = [p])
    (hr : GSVProgZLoop.RunsTo (engine e) e.blank p (bundle u.ideal u.dir) U cost) :
    (semanticInputs ws).length ≤ cost := by
  rw [← follows_trace_length e h, hc, semanticInputs_replicate]
  exact trace_bound hr _

theorem step_bound {e : Env k} {u v : Snapshot k} {ws : List Event}
    {pattern Word : List (Fin k)} {rate p r : ℕ} {st : ScanState}
    (h : Follows e u ws v) (hrate : 0 < rate) (hmb : e.mark ≠ e.blank)
    (hstart : e.startSym ∉ pattern)
    (hE : GSTapes.Encodes' e.blank e.startSym e.endSym e.mark pattern Word rate p r u.ideal.1 st)
    (hq : st.q ≤ pattern.length) (up : Bool)
    (hdir : u.dir = GSVProgZLoop.dirTape e.blank e.mark up 0)
    (hcode : u.frames = [.code (GSVProgZLoop.stepProg rate)]) :
    (semanticInputs ws).length ≤
      (GSVTapesZ.vprogramZ' e.blank e.startSym e.endSym e.mark rate up u.ideal).length + 1 := by
  have hr := GSVProgZLoop.stepProg_runsTo (Terminal := Unit) hrate hmb hstart hE hq up
  have hc : erase u.frames = [GSVProgZLoop.stepProg rate] := by
    simp only [hcode, erase, eraseFrame, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  apply follows_bound h hc
  rw [hdir]
  exact hr

theorem semantic_count (ws : List Event) : (ws.map instructions).sum = (semanticInputs ws).length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    cases w <;> simp [instructions, semanticInputs, ih]
    omega

theorem follows_idle {e : Env k} {u v : Snapshot k} {ws : List Event}
    (h : Follows e u ws v) :
    (ws.map idles).sum + debt u.frames ≤ (ws.map instructions).sum + debt v.frames := by
  induction h with
  | nil => simp
  | stutter hf _ _ _ ih => simpa only [hf] using ih
  | @step u v z w ws had ht ih =>
    obtain ⟨ev, he⟩ := had.dispatch
    have hc := idle_charge ev he
    simp only [List.map_cons, List.sum_cons]
    omega

def feeds : Event → ℕ
  | .feed1 | .feed2 => 1
  | _ => 0

theorem event_partition {w : Event} (h : w ≠ .halt) : instructions w + idles w + feeds w = 1 := by
  cases w <;> simp_all [instructions, idles, feeds]

theorem follows_partition {e : Env k} {u v : Snapshot k} {ws : List Event}
    (h : Follows e u ws v) :
    ws.length = (ws.map instructions).sum + (ws.map idles).sum + (ws.map feeds).sum := by
  induction h with
  | nil => rfl
  | stutter _ _ _ _ ih => exact ih
  | step had _ ih =>
    have hp := event_partition had.nonhalt
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

/-- All non-feed overhead is bounded by GS work. Input starvation may
still create feed events, and is deliberately not hidden in this bound. -/
theorem worker_bound {e : Env k} {u v : Snapshot k} {ws : List Event}
    {p : GSVProgZLoop.DProg} {U : Fin 11 → STape (Fin k)} {cost : ℕ}
    (h : Follows e u ws v) (hc : erase u.frames = [p])
    (hr : GSVProgZLoop.RunsTo (engine e) e.blank p (bundle u.ideal u.dir) U cost) :
    ws.length ≤ 2 * cost + 1 + (ws.map feeds).sum := by
  have hi := follows_bound h hc hr
  have hd := follows_idle h
  have hp := follows_partition h
  have hlast := debt_le v.frames
  rw [semantic_count] at hd hp
  omega

/-- The existing GS potential pays for every instruction and loop-commit
idle in a real compiled prefix. Only actual supply events remain separate. -/
theorem amortized_worker {e : Env k} {u v : Snapshot k} {ws : List Event}
    {leftPat rightPat Word : List (Fin k)} {rate p r : ℕ} {z : GSVerifierZ.VStateZ}
    (h : Follows e u ws v) (hrate : 0 < rate) (hmb : e.mark ≠ e.blank)
    (hstart : e.startSym ∉ rightPat) (hend : e.endSym ∉ rightPat)
    (hE : GSVTapesZ.VEncodesZ' e.blank e.startSym e.endSym e.mark leftPat rightPat Word
      rate p r u.ideal z) (hq : z.1.q ≤ rightPat.length)
    (hdir : u.dir = GSVProgZLoop.dirTape e.blank e.mark z.2.up 0)
    (hcode : u.frames = [.code (GSVProgZLoop.stepProg rate)]) :
    ws.length ≤ 2 * (GSVTapesZ.zA rate *
      (Phi rate (scanStep rightPat rate p r Word z.1) - Phi rate z.1) + GSVTapesZ.zB + 1) +
      1 + (ws.map feeds).sum := by
  have hr := GSVProgZLoop.stepProg_runsTo (Terminal := Unit) hrate hmb hstart hE.scan hq z.2.up
  have hc : erase u.frames = [GSVProgZLoop.stepProg rate] := by
    simp only [hcode, erase, eraseFrame, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hinit : GSVProgZLoop.tapes e.blank e.mark u.ideal z.2.up = bundle u.ideal u.dir := by
    rw [hdir]
    rfl
  rw [hinit] at hr
  have hw := worker_bound h hc hr
  have hp := GSVTapesZ.vprogramZ'_cost hrate hmb hend hE hq
  omega

/-- info: 'PalPeg.TextFeedPipelineInstructionCost.amortized_worker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms amortized_worker

/-- info: 'PalPeg.TextFeedPipelineInstructionCost.worker_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms worker_bound

/-- info: 'PalPeg.TextFeedPipelineInstructionCost.step_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step_bound

end PalPeg.TextFeedPipelineInstructionCost
