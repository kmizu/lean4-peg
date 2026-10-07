import MacroPeg.HigherOrder.KExp.Lay
import MacroPeg.HigherOrder.KExp.Extract
import Complexity.Comp.HaltSim
import Complexity.Comp.NDecide
import Complexity.Univ.Growth

/-!
# Decidable languages are closed under computable reductions

A stage lays out the table of a machine on the input and simulates it until it halts (`haltStage_runs`).
A decider's stage followed by a test of the state decides the machine's language on the stacks (`decP_halts`), so a
stack program computing `f` followed by it decides `L` when `L w ↔ L' (f w)` (`tmDecidable_of_nreduce`). A
Turing machine computing `f` gives such a program: its stage, then its output read back as a fresh input
(`tmDecidable_of_reduce`).
-/

namespace Complexity

open Complexity.Univ
open Shallot.MacroPeg.KExp

/-- Lay out the table on the input (dropping the step count) and run it until it halts. -/
def haltStage (T : TTable) : NProg UK := .seq (layTP T 0 0 0) (.seq (.prim (.pop CNT)) haltSimP)

theorem haltStage_runs (T : TTable) (hT : RowsOK T) (w : List Bool) {t : Nat}
    (hh : (frun T (finit T.k w) t).state = 0 ∨ (frun T (finit T.k w) t).state = 1) :
    ∃ S n, NRuns (haltStage T) (nInit UK w) S n ∧ S ST = [(frun T (finit T.k w) t).state] ∧
      S TP = encTapes (frun T (finit T.k w) t).tapes ∧ S CNT = [] ∧ UScratch S := by
  obtain ⟨S₁, x₁, hS₁, hN, hs⟩ := layP_runs T 0 0 0 w
  have p := nruns_pop CNT S₁ (l := []) (v := _) hN
  have hS₂ := simSt_setCNT hS₁ []
  have hs₂ := uScratch_setCNT hs []
  obtain ⟨n, x₃⟩ := haltSimP_runs T hT (finit T.k w) (finit_cfgOK T w) (S₁.set CNT []) hS₂ (by simp) hs₂ hh
  refine ⟨_, _, x₁.seq (p.seq x₃), ?_, ?_, ?_, uScratch_putCfg hs₂ _⟩
  · simp only [putCfg]; lat
  · simp only [putCfg]; lat
  · rw [putCfg_CNT]; simp

/-- Accept when the state is 0. -/
def stAccP : NProg UK := .ite ST .zero (.halt true) (.halt false)

/-- The decider's stage, then its answer. -/
def decP (T : TTable) : NProg UK := .seq (haltStage T) stAccP

theorem decP_halts {k : Nat} {N : TM k} {L : Lang} (hN : N.Decides L) (u : List Bool) :
    ∃ n b S, NHalts (decP (tableOf N)) (nInit UK u) b S n ∧ (b = true ↔ L u) := by
  obtain ⟨t, hh, hs⟩ := hN u
  have hst : (frun (tableOf N) (finit (tableOf N).k u) t).state = (N.run (initCfg k u) t).state :=
    frun_state N u t
  obtain ⟨S, n, x, hST, _, _, _⟩ := haltStage_runs (tableOf N) (tableOf_rowsOK N) u (t := t)
    (by rw [hst]; exact hh)
  rw [hst] at hST
  by_cases h0 : (N.run (initCfg k u) t).state = 0
  · have x₄ : NHalts stAccP S true S 2 := NHalts.iteT (by rw [hST, h0]; rfl) (nhalts_halt true _)
    exact ⟨_, true, S, x.seqH x₄, by simp only [true_iff]; exact hs.1 h0⟩
  · have x₄ : NHalts stAccP S false S 2 := NHalts.iteF (by
      rw [hST]; simp only [NTest.eval, List.getLast?_singleton]; simpa using h0) (nhalts_halt false _)
    exact ⟨_, false, S, x.seqH x₄, by
      simp only [Bool.false_eq_true, false_iff]; exact fun hl => h0 (hs.2 hl)⟩

/-- A stack program computes `f` when it turns the input stacks of `w` into the input stacks of `f w`. -/
def NComputes (p : NProg Complexity.Univ.UK) (f : List Bool → List Bool) : Prop :=
  ∀ w, ∃ c, NRuns p (nInit Complexity.Univ.UK w) (nInit Complexity.Univ.UK (f w)) c

/-- **Reductions by stack programs keep decidability.** -/
theorem tmDecidable_of_nreduce {L L' : Lang} {p : NProg Complexity.Univ.UK} {f : List Bool → List Bool}
    (hL' : TMDecidable L') (hp : NComputes p f) (h : ∀ w, L w ↔ L' (f w)) : TMDecidable L := by
  obtain ⟨kN, N, hN⟩ := hL'
  refine tmDecidable_of_nprog (K := UK) (by decide) (.seq p (decP (tableOf N))) L (fun w => ?_)
  obtain ⟨c, x₁⟩ := hp w
  obtain ⟨n, b, S, x₂, hb⟩ := decP_halts hN (f w)
  obtain ⟨u, _, hx⟩ := x₁.seqH x₂
  exact ⟨u, b, S, hx, by rw [hb, h w]⟩

/-- A machine computing `f` gives a stack program computing `f`: its stage, then its output as a fresh input. -/
theorem nComputes_of_tm {f : List Bool → List Bool} (hf : TMComputable f) :
    ∃ p, NComputes p f := by
  obtain ⟨kR, hkR, R, hR⟩ := hf
  refine ⟨.seq (haltStage (tableOf R)) extractP, fun w => ?_⟩
  obtain ⟨t, hst, hout⟩ := hR w
  have hs : (frun (tableOf R) (finit (tableOf R).k w) t).state = (R.run (initCfg kR w) t).state :=
    frun_state R w t
  obtain ⟨S, n, x₁, _, hTP, hC, hsc⟩ := haltStage_runs (tableOf R) (tableOf_rowsOK R) w (t := t)
    (by rw [hs, hst]; exact .inl rfl)
  have x₂ := extractP_runs S _ hTP hC hsc
  have hfo : readOut ((frun (tableOf R) (finit (tableOf R).k w) t).tapes.getD 0 []) = f w :=
    frun_output hkR R w (Nat.le_refl t) hst hout
  rw [hfo] at x₂
  exact ⟨_, x₁.seq x₂⟩

/-- **Computable many-one reductions keep decidability.** -/
theorem tmDecidable_of_reduce {L L' : Lang} {f : List Bool → List Bool} (hL' : TMDecidable L') (hf : TMComputable f)
    (h : ∀ w, L w ↔ L' (f w)) : TMDecidable L :=
  let ⟨_, hp⟩ := nComputes_of_tm hf
  tmDecidable_of_nreduce hL' hp h

end Complexity
