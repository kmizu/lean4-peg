import PalPeg.TextFeedPipelineVerifier

/-! Productive preparation windows in the actual pipeline. Structural
control equivalence also admits the unexpanded initial sequential task. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelinePrepWindow
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangPersist2 PalPeg.ProgLangBank PalPeg.TextFeedControl PalPeg.PrepInstance
open PalPeg.TextFeedPipelineBank PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelineHandoff
open PalPeg.TextFeedPrepResume (source sourceStep)

variable {k : ℕ} {Terminal : Type}

def ControlEq (actual : Stack (TaskAct k) (TaskCond k))
    (s : Stack (PrepAct k) (PrepCond k)) (r : Stack (TaskAct k) (TaskCond k)) : Prop :=
  ∀ ev, stepStack ev actual = stepStack ev (s.map liftPrep ++ r)

theorem control_initial (e : Env k) (leftSym : Fin k) (rate : ℕ) :
    ControlEq [task e leftSym rate]
      [finitePrepSetup e.blank e.startSym e.endSym leftSym e.mark rate] [afterPrep rate] := by
  intro ev
  rw [task, stepStack_seq]
  rfl

theorem prepView_extend (P : Fin 15 → STape (Fin k)) (T : Fin 39 → STape (Fin k)) :
    prepView (extend prepSlot P T) = P := by
  funext j
  exact extend_ι prepSlot P T j

theorem extend_twice (P Q : Fin 15 → STape (Fin k)) (T : Fin 39 → STape (Fin k)) :
    extend prepSlot P (extend prepSlot Q T) = extend prepSlot P T := by
  funext j
  cases hp : proj prepSlot j <;> simp only [extend, hp]

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

/-- N ordinary calls execute exactly N source preparation actions, even
from the initial task wrapper. No FIFO or input tape is modified. -/
theorem run_window (e : Env k) (leftSym : Fin k) (R rate N : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1)
    (s : Stack (PrepAct k) (PrepCond k)) (r : Stack (TaskAct k) (TaskCond k))
    (P : Fin 15 → STape (Fin k)) (hv : prepView x.2 = P)
    (hs : ControlEq x.1.1.2.2.val s r)
    (htrace : (trace (source e) e.blank (List.replicate N none) (s, P)).length = N)
    (hpos : N ≠ 0 → 0 < x.1.1.1.val) (hlen : x.1.1.1.val + N ≤ R + 1) :
    let y := (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[N] x
    let z := runInputs (source e) e.blank (List.replicate N none) (s, P)
    y.2 = extend prepSlot z.2 x.2 ∧ AtBoundary (programs e) y.1.2.2.1 ∧ ControlEq y.1.1.2.2.val z.1 r := by
  induction N generalizing x s P with
  | zero =>
    refine ⟨?_, hb, hs⟩
    change x.2 = extend prepSlot P x.2
    rw [← hv]
    exact (TextFeedStartupSafety.extend_restrict prepSlot x.2).symm
  | succ N ih =>
    have hsome : ∃ a, (stepStack (evalConds (source e) (fun j => (P j).focus)) s).2 = some a := by
      cases hw : (stepStack (evalConds (source e) (fun j => (P j).focus)) s).2 with
      | some a => exact ⟨a, rfl⟩
      | none =>
        have hle := trace_length_le (source e) e.blank (List.replicate N none) (sourceStep e s P)
        rw [List.replicate_succ, trace_cons, hw] at htrace
        simp only [List.nil_append, List.length_replicate] at htrace hle
        change (trace (source e) e.blank (List.replicate N none) (sourceStep e s P)).length = N + 1 at htrace
        omega
    obtain ⟨a, ha⟩ := hsome
    have hz : x.1.1.1 ≠ 0 := by
      have hh := hpos (Nat.succ_ne_zero N)
      intro hz
      rw [hz] at hh
      simp at hh
    have ha' : (stepStack (evalConds (source e) (fun j => (prepView x.2 j).focus)) s).2 = some a := by
      rw [hv]
      exact ha
    obtain ⟨ht, hb', hs'⟩ := run_prep_step (Terminal := Terminal) e leftSym R rate x hb hz s r (hs _) a ha'
    rw [hv] at ht hs'
    have hv' : prepView (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x).2 = (sourceStep e s P).2 := by
      rw [ht, prepView_extend]
    have hc' : ControlEq (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x).1.1.2.2.val
        (sourceStep e s P).1 r := by intro ev; rw [hs']
    have htrace' : (trace (source e) e.blank (List.replicate N none) (sourceStep e s P)).length = N := by
      rw [List.replicate_succ, trace_cons, ha] at htrace
      simpa only [List.singleton_append, List.length_cons, Nat.succ.injEq, sourceStep] using htrace
    have hnext (hn : N ≠ 0) : x.1.1.1.val + 1 < R + 1 := by omega
    have hp' : N ≠ 0 → 0 < (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x).1.1.1.val := by
      intro hn
      rw [run_counter]
      simp only [nextPhase, dif_pos (hnext hn)]
      omega
    have hl' : (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x).1.1.1.val + N ≤ R + 1 := by
      by_cases hn : N = 0
      · have hlt := (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x).1.1.1.isLt
        omega
      · rw [run_counter]
        simp only [nextPhase, dif_pos (hnext hn)]
        omega
    obtain ⟨ht', hb'', hs''⟩ := ih (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x) hb'
      (sourceStep e s P).1 (sourceStep e s P).2 hv' hc' htrace' hp' hl'
    rw [ht, extend_twice] at ht'
    simpa only [Function.iterate_succ_apply, List.replicate_succ, runInputs_cons,
      sourceStep, Prod.mk.eta] using And.intro ht' (And.intro hb'' hs'')

/-- info: 'PalPeg.TextFeedPipelinePrepWindow.run_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_window

end PalPeg.TextFeedPipelinePrepWindow
