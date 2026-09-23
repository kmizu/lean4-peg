import PalPeg.ScaWindowEncode
import PalPeg.ScaWindowTop

/-!
# The whole tick as one stack program, and `PAL ∈ PEG` from worker encodings

`ScaWindowEncode` gives the representation `Rep` and the programs for the pieces of `tick`
(`headP`, `roundP`, `finishP`), each simulating its piece as long as no worker faults. This file
chains them into one program per letter (`letterProg`), proves that it simulates `tick`
(`sim_tick`), and assembles `PAL ∈ PEG` through `ScaEncode.pal_in_peg`. The simulation is used
only on reachable states, where "no worker faults" is the `hworkers` obligation.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace PalPeg.ScaWindowEncode
open PalPeg.ScaLocal PalPeg.ScaProg PalPeg.ScaProgEmbed PalPeg.ScaWindowPal

section Top
variable {Wm Wf Γm Γf Cm Cf : Type} [Inhabited Γm] [Inhabited Γf] {Km Kf D : ℕ}
  {mOps : WorkerOps Wm} {fOps : WorkerOps Wf}
  (mE : WorkerEnc Wm mOps Γm Cm Km D) (fE : WorkerEnc Wf fOps Γf Cf Kf D)

theorem sim_finish (a : Fin 2) :
    Sim mE fE (finishS mOps a) (finishP (Γf := Γf) (Cf := Cf) (Kf := Kf) mE a) :=
  sim_ctlOnly mE fE _ (ctlOnly_finishP mE a) _ (fun _ => rfl) (fun _ => rfl)
    fun s c st h => crep_finish mE fE a s c st h

/-- **The program for one letter**: the prefix, the two stage rounds, the output. -/
def letterProg (a : Fin 2) : Prog (Γm ⊕ Γf) (Ctrl Cm Cf) (KK Km Kf) :=
  .seq (.seq (.seq (headP a) (roundP mE fE a 0)) (roundP mE fE a 1)) (finishP mE a)

omit [Inhabited Γm] [Inhabited Γf] in
theorem tick_eq_rounds (s : PalState Wm Wf) (a : Fin 2) :
    tick mOps fOps s a =
      finishS mOps a (roundS mOps fOps a 1 (roundS mOps fOps a 0 (preS s a))) := by
  rw [tick_eq_preTick, stageRound_eq, stageRound_eq, ← preS_eq]

/-- **The letter program simulates `tick`** whenever the tick leaves no worker faulted. -/
theorem sim_tick (hD : 1 ≤ D) (a : Fin 2) :
    Sim mE fE (fun s => tick mOps fOps s a) (letterProg mE fE a) := by
  have hfin : Keeps mOps fOps (finishS mOps a) := Keeps.of_workers _ (fun _ => rfl) (fun _ => rfl)
  have hs := Sim.seq mE fE
    (Sim.seq mE fE (Sim.seq mE fE (sim_head mE fE hD a) (sim_round mE fE hD a 0)
      (keeps_roundS mE fE a 0)) (sim_round mE fE hD a 1) (keeps_roundS mE fE a 1))
    (sim_finish mE fE a) hfin
  intro s c st h hnf
  have e := tick_eq_rounds (mOps := mOps) (fOps := fOps) s a
  simp only [e] at hnf ⊢
  exact hs s c st h hnf

/-- Acceptance, read off the control: the output bit and no fault anywhere. -/
def acceptC (c : Ctrl Cm Cf) : Bool :=
  c.1.output && !(c.1.fault || mE.faulted (c.2.1 0) || mE.faulted (c.2.1 1) ||
    fE.faulted (c.2.2 0) || fE.faulted (c.2.2 1))

theorem acc_eq {s : PalState Wm Wf} {c : Ctrl Cm Cf} {st : Fin (KK Km Kf) → List (Γm ⊕ Γf)}
    (h : Rep mE fE s c st) :
    (s.output && !globalFault mOps fOps s) = acceptC mE fE c := by
  have h0 := mE.rep_faulted _ _ _ (h.mat 0).1
  have h1 := mE.rep_faulted _ _ _ (h.mat 1).1
  have h2 := fE.rep_faulted _ _ _ (h.flg 0).1
  have h3 := fE.rep_faulted _ _ _ (h.flg 1).1
  simp only [globalFault, acceptC, ← h.ctl.output, ← h.ctl.fault]
  rw [h0, h1, h2, h3]
  rfl

/-- The letter programs, from the workers' initial controls. -/
def letters (cm0 : Cm) (cf0 : Cf) : ScaEncode.LetterProgs (Γm ⊕ Γf) (Ctrl Cm Cf) (KK Km Kf) where
  peek := D
  prog := letterProg mE fE
  init := (Ctl.initial, fun _ => cm0, fun _ => cf0)
  accept := acceptC mE fE

/-- The initial state is represented by the initial control and empty stacks. -/
theorem rep_initial (m0 : Wm) (f0 : Wf) (cm0 : Cm) (cf0 : Cf)
    (hm0 : mE.Rep m0 cm0 fun _ => []) (hf0 : fE.Rep f0 cf0 fun _ => []) :
    Rep mE fE (initial m0 f0) (Ctl.initial, fun _ => cm0, fun _ => cf0) (fun _ => []) where
  ctl := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩⟩
  mat i := ⟨by rw [proj_nil]; exact hm0, pure_nil _⟩
  flg i := ⟨by rw [proj_nil]; exact hf0, pure_nil _⟩

/-- **`PAL ∈ PEG`** from stack-program encodings of the two worker kinds, the controller's
correctness (`hpal`, from `ScaWindowTop.accepts_iff_pal`) and "no worker ever faults". -/
theorem pal_in_peg [Finite Γm] [Finite Γf] [Finite Cm] [Finite Cf] (hD : 1 ≤ D)
    (m0 : Wm) (f0 : Wf) (cm0 : Cm) (cf0 : Cf)
    (hm0 : mE.Rep m0 cm0 fun _ => []) (hf0 : fE.Rep f0 cf0 fun _ => [])
    (hworkers : ∀ (w : List (Fin 2)) (i : Fin 2),
      mOps.faulted ((run mOps fOps m0 f0 w).matchers i) = false ∧
        fOps.faulted ((run mOps fOps m0 f0 w).flags i) = false)
    (hpal : ∀ w, Accepts mOps fOps m0 f0 w ↔ w ∈ PalPeg.PAL) :
    PegSeparation.RecognizedByTotalPEG PalPeg.PAL := by
  refine ScaEncode.pal_in_peg (letters mE fE cm0 cf0) (initial m0 f0) (tick mOps fOps)
    (fun s => s.output && !globalFault mOps fOps s)
    (fun s c st => (∃ u, s = run mOps fOps m0 f0 u) ∧ Rep mE fE s c st)
    ⟨⟨[], rfl⟩, rep_initial mE fE m0 f0 cm0 cf0 hm0 hf0⟩ ?_ ?_ ?_
  · rintro s c st a ⟨⟨u, rfl⟩, h⟩
    have happ : run mOps fOps m0 f0 (u ++ [a]) = tick mOps fOps (run mOps fOps m0 f0 u) a := by
      simp [run, List.foldl_append]
    refine ⟨⟨u ++ [a], happ.symm⟩, sim_tick mE fE hD a _ c st h ?_⟩
    intro i
    beta_reduce
    rw [← happ]
    exact hworkers _ i
  · rintro s c st ⟨_, h⟩
    exact acc_eq mE fE h
  · intro w
    rw [← hpal w]
    unfold Accepts accepts
    cases w with
    | nil =>
      have h0 := hworkers [] 0
      simp only [run, List.foldl_nil, initial] at h0
      simp [initial, globalFault, h0]
    | cons b w => simp [run]

/-- **`PAL ∈ PEG` from the workers alone**: stack encodings of the two worker kinds, and the four
worker obligations of `ScaWindowTop` (the answering matcher's output, the answering stage's
middle bit, no controller violation, no worker fault). No automaton is assumed. -/
theorem pal_in_peg_of_workers [Finite Γm] [Finite Γf] [Finite Cm] [Finite Cf] (hD : 1 ≤ D)
    (m0 : Wm) (f0 : Wf) (cm0 : Cm) (cf0 : Cf)
    (hm0 : mE.Rep m0 cm0 fun _ => []) (hf0 : fE.Rep f0 cf0 fun _ => [])
    (hmatch : ∀ w : List (Fin 2), 4 ≤ w.length →
      (mOps.output ((run mOps fOps m0 f0 w).matchers
          (ScaWindowSchedule.idx (Nat.log 2 w.length))) = true ↔
        occursAt (w.take (stageOf w.length)).reverse w))
    (hmiddle : ∀ w : List (Fin 2), 4 ≤ w.length →
      (((run mOps fOps m0 f0 w).stages (ScaWindowSchedule.idx (Nat.log 2 w.length))).middle = true ↔
        IsPal ((w.drop (stageOf w.length)).take (w.length - 2 * stageOf w.length))))
    (hclean : ∀ u : List (Fin 2), ScaWindowFault.ctlViolation (run mOps fOps m0 f0 u) = false)
    (hworkers : ∀ (w : List (Fin 2)) (i : Fin 2),
      mOps.faulted ((run mOps fOps m0 f0 w).matchers i) = false ∧
        fOps.faulted ((run mOps fOps m0 f0 w).flags i) = false) :
    PegSeparation.RecognizedByTotalPEG PalPeg.PAL :=
  pal_in_peg mE fE hD m0 f0 cm0 cf0 hm0 hf0 hworkers
    (ScaWindowTop.accepts_iff_pal mOps fOps m0 f0 hmatch hmiddle (fun u _ => hclean u) hworkers)

end Top

/-- info: 'PalPeg.ScaWindowEncode.pal_in_peg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pal_in_peg

/-- info: 'PalPeg.ScaWindowEncode.pal_in_peg_of_workers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pal_in_peg_of_workers

end PalPeg.ScaWindowEncode
