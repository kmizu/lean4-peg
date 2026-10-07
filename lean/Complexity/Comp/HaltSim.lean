import Complexity.Univ.SimRun

/-!
# Simulating a table until it halts

`haltSimP` runs the one-step program `stepP` while the simulated state is neither `0` nor `1`: the flag on `CNT` is
the state minus one, positive exactly when the configuration has not halted. If the table halts after some number
`t` of steps, the simulator ends with the configuration `frun T c t` (`haltSimP_runs`).
-/

namespace Complexity

open Complexity.Univ

/-- Put the state minus one on `CNT`. -/
def flagP : NProg UK := .seq (.prim (.dup ST CNT (by decide))) (.prim (.dec CNT))

def hloopP : NProg UK := .loop CNT .pos (.seq (.prim (.pop CNT)) (.seq stepP flagP))

/-- Run the table on the stacks until it halts. -/
def haltSimP : NProg UK := .seq flagP (.seq hloopP (.prim (.pop CNT)))

theorem set_self_of {S : Lists UK} {i : Fin UK} (h : S i = []) : S.set i [] = S := by
  rw [← h, Lists.set_get_self]

theorem flagP_runs {S : Lists UK} {T : TTable} {c : FCfg} (hS : SimSt S T c) (hC : S CNT = []) :
    NRuns flagP S (S.set CNT [c.state - 1]) 2 := by
  have d₁ := nruns_dup ST CNT (by decide) S (l := []) (v := c.state) hS.2.2.2.1
  rw [hC, List.nil_append] at d₁
  have d₂ := nruns_dec CNT (S.set CNT [c.state]) (l := []) (v := c.state) (by simp)
  rw [Lists.set_set_u] at d₂
  exact d₁.seq d₂

theorem frun_succ' (T : TTable) : ∀ (c : FCfg) (t : Nat), frun T c (t + 1) = frun T (fstep T c) t := by
  intro c t
  induction t with
  | zero => rfl
  | succ t ih => show fstep T (frun T c (t + 1)) = fstep T (frun T (fstep T c) t); rw [ih]

theorem frun_fix {T : TTable} {c : FCfg} (h : c.state = 0 ∨ c.state = 1) : ∀ t, frun T c t = c
  | 0 => rfl
  | t + 1 => by show fstep T (frun T c t) = c; rw [frun_fix h t, fstep_halted h]

theorem putCfg_CNT (S : Lists UK) (c : FCfg) : (putCfg S c) CNT = S CNT := by
  simp only [putCfg]; lat

theorem hloop_runs (T : TTable) (hT : RowsOK T) : ∀ (t : Nat) (c : FCfg) (S : Lists UK), CfgOK T c →
    SimSt S T c → S CNT = [] → UScratch S → ((frun T c t).state = 0 ∨ (frun T c t).state = 1) →
    ∃ n, NRuns hloopP (S.set CNT [c.state - 1]) ((putCfg S (frun T c t)).set CNT [(frun T c t).state - 1]) n := by
  intro t
  induction t with
  | zero =>
    intro c S _ hS _ _ hh
    refine ⟨1, ?_⟩
    have e : putCfg S (frun T c 0) = S := putCfg_self hS
    rw [e]
    have h0 : c.state - 1 = 0 := by simp only [frun] at hh; omega
    exact nruns_loop_exit (by simp only [h0, Lists.set_same]; rfl)
  | succ t ih =>
    intro c S hc hS hC hs hh
    by_cases hq : c.state = 0 ∨ c.state = 1
    · refine ⟨1, ?_⟩
      rw [frun_fix hq, putCfg_self hS]
      have h0 : c.state - 1 = 0 := by omega
      exact nruns_loop_exit (by simp only [h0, Lists.set_same]; rfl)
    · -- one step, then the rest
      have p₁ := nruns_pop CNT (S.set CNT [c.state - 1]) (l := []) (v := c.state - 1) (by simp)
      rw [Lists.set_set_u, set_self_of hC] at p₁
      have st := stepP_runs T hT c hc S hS hs
      have hS' := simSt_putCfg hS (fstep T c)
      have hC' : (putCfg S (fstep T c)) CNT = [] := by rw [putCfg_CNT, hC]
      have fl := flagP_runs hS' hC'
      obtain ⟨t₁, ht₁, x₁⟩ := p₁.seq (st.seq fl)
      rw [frun_succ'] at hh ⊢
      obtain ⟨n, t₂, ht₂, x₂⟩ := ih (fstep T c) (putCfg S (fstep T c)) (fstep_ok hT hc) hS' hC'
        (uScratch_putCfg hs _) hh
      rw [putCfg_putCfg] at x₂
      refine ⟨t₁ + 1 + t₂, t₁ + 1 + t₂, Nat.le_refl _, .loopC trivial ?_ x₁ x₂⟩
      simp only [Lists.set_same]
      rw [show c.state - 1 = (c.state - 2) + 1 by omega]; rfl

/-- **The simulator runs the table until it halts.** -/
theorem haltSimP_runs (T : TTable) (hT : RowsOK T) (c : FCfg) (hc : CfgOK T c) (S : Lists UK) (hS : SimSt S T c)
    (hC : S CNT = []) (hs : UScratch S) {t : Nat} (hh : (frun T c t).state = 0 ∨ (frun T c t).state = 1) :
    ∃ n, NRuns haltSimP S (putCfg S (frun T c t)) n := by
  have f := flagP_runs hS hC
  obtain ⟨n, l⟩ := hloop_runs T hT t c S hc hS hC hs hh
  have p := nruns_pop CNT ((putCfg S (frun T c t)).set CNT [(frun T c t).state - 1]) (l := [])
    (v := (frun T c t).state - 1) (by simp)
  rw [Lists.set_set_u, set_self_of (by rw [putCfg_CNT, hC])] at p
  exact ⟨_, f.seq (l.seq p)⟩

end Complexity
