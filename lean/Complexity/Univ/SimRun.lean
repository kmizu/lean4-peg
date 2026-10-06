import Complexity.Univ.SimStep

/-!
# The simulator

`simP` runs `stepP` as many times as the number on `CNT` says, then pops it (`simP_runs`).
-/

namespace Complexity.Univ

open Complexity

def simP : NProg UK := .seq (.loop CNT .pos (.seq (.prim (.dec CNT)) stepP)) (.prim (.pop CNT))

theorem putCfg_putCfg (S : Lists UK) (c c' : FCfg) : putCfg (putCfg S c) c' = putCfg S c' := by
  simp only [putCfg]; leq

theorem simSt_putCfg {S : Lists UK} {T : TTable} {c : FCfg} (h : SimSt S T c) (c' : FCfg) :
    SimSt (putCfg S c') T c' := by
  obtain ⟨h₁, h₂, h₃, _, _, _⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (simp only [putCfg]; lat)

theorem uScratch_putCfg {S : Lists UK} (h : UScratch S) (c : FCfg) : UScratch (putCfg S c) := by
  intro x hx
  have h₁ : x ≠ ST := by intro e; subst e; exact absurd hx (by decide)
  have h₂ : x ≠ POS := by intro e; subst e; exact absurd hx (by decide)
  have h₃ : x ≠ TP := by intro e; subst e; exact absurd hx (by decide)
  simp only [putCfg, Lists.set, h₁, h₂, h₃, if_false]
  exact h x hx

theorem simSt_setCNT {S : Lists UK} {T : TTable} {c : FCfg} (h : SimSt S T c) (v : List Nat) :
    SimSt (S.set CNT v) T c := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> lat

theorem uScratch_setCNT {S : Lists UK} (h : UScratch S) (v : List Nat) : UScratch (S.set CNT v) := by
  intro x hx
  have : x ≠ CNT := by intro e; subst e; exact absurd hx (by decide)
  simp only [Lists.set, this, if_false]; exact h x hx

theorem cfgOK_frun {T : TTable} (hT : RowsOK T) {c : FCfg} (hc : CfgOK T c) : ∀ m, CfgOK T (frun T c m)
  | 0 => hc
  | m + 1 => fstep_ok hT (cfgOK_frun hT hc m)

theorem simCost_mono (T : TTable) (c : FCfg) {m n : Nat} (h : m ≤ n) : simCost T c m ≤ simCost T c n := by
  induction n with
  | zero => rw [Nat.le_zero.1 h]; exact Nat.le_refl _
  | succ n ih =>
    by_cases hm : m = n + 1
    · rw [hm]; exact Nat.le_refl _
    · have := ih (by omega); simp only [simCost]; omega

theorem ten_le_simCost (T : TTable) (c : FCfg) (n : Nat) : 10 ≤ simCost T c n := simCost_mono T c (Nat.zero_le n)

/-- The step bound fits in `stepCost`. -/
theorem step_fits (T : TTable) (c : FCfg) : 800 * cu (nB T c) + 5 + 2 ≤ stepCost T c := by
  have h1 : 1 ≤ nB T c := by simp only [nB]; omega
  have := cu_le_qu h1
  have := Nat.le_trans (Nat.le_trans (n_le_sq h1) (sq_le_cu h1)) (cu_le_qu h1)
  have e : stepCost T c = 1000 * qu (nB T c) := by
    simp only [stepCost, qu, nB, Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
  omega

/-- The loop, from `m` steps done. -/
theorem simLoop (T : TTable) (hT : RowsOK T) (c : FCfg) (hc : CfgOK T c) (B : Nat) (S : Lists UK)
    (hS : SimSt S T c) (hs : UScratch S) :
    ∀ r m, m + r = B → NRuns (.loop CNT .pos (.seq (.prim (.dec CNT)) stepP))
      ((putCfg S (frun T c m)).set CNT [B - m]) ((putCfg S (frun T c B)).set CNT [0])
      (simCost T c B - simCost T c m + 1)
  | 0, m, h => by
    obtain rfl : m = B := by omega
    rw [Nat.sub_self, Nat.sub_self]
    exact nruns_loop_exit (by simp only [Lists.set_same]; rfl)
  | r + 1, m, h => by
    have ih := simLoop T hT c hc B S hS hs r (m + 1) (by omega)
    have d₁ := nruns_dec CNT ((putCfg S (frun T c m)).set CNT [B - m]) (l := []) (v := B - m) (by simp)
    rw [Lists.set_set_u, show B - m - 1 = B - (m + 1) by omega] at d₁
    have st := stepP_runs T hT (frun T c m) (cfgOK_frun hT hc m) ((putCfg S (frun T c m)).set CNT [B - (m + 1)])
      (simSt_setCNT (simSt_putCfg hS _) _) (uScratch_setCNT (uScratch_putCfg hs _) _)
    have e : putCfg ((putCfg S (frun T c m)).set CNT [B - (m + 1)]) (fstep T (frun T c m)) =
        (putCfg S (frun T c (m + 1))).set CNT [B - (m + 1)] := by
      simp only [putCfg, frun]; leq
    rw [e] at st
    obtain ⟨t₁, ht₁, x₁⟩ := d₁.seq st
    obtain ⟨t₂, ht₂, x₂⟩ := ih
    refine ⟨t₁ + 1 + t₂, ?_, .loopC trivial ?_ x₁ x₂⟩
    · have f := step_fits T (frun T c m)
      have hm : simCost T c (m + 1) = simCost T c m + stepCost T (frun T c m) := rfl
      have := simCost_mono T c (show m + 1 ≤ B by omega)
      omega
    · simp only [Lists.set_same]; rw [show B - m = (B - m - 1) + 1 by omega]; rfl

/-- **The simulator runs `fstep T` `B` times.** -/
theorem simP_runs (T : TTable) (hT : RowsOK T) (c : FCfg) (hc : CfgOK T c) (B : Nat) (S : Lists UK)
    (hS : SimSt S T c) (hN : S CNT = [B]) (hs : UScratch S) :
    NRuns simP S ((putCfg S (frun T c B)).set CNT []) (simCost T c B) := by
  have l := simLoop T hT c hc B S hS hs B 0 (by omega)
  have e : (putCfg S (frun T c 0)).set CNT [B - 0] = S := by
    simp only [frun, putCfg_self hS, Nat.sub_zero]; rw [← hN, Lists.set_get_self]
  rw [e] at l
  have p := nruns_pop CNT ((putCfg S (frun T c B)).set CNT [0]) (l := []) (v := 0) (by simp)
  rw [Lists.set_set_u] at p
  refine (l.seq p).mono ?_
  have := ten_le_simCost T c B
  have h0 : simCost T c 0 = 10 := rfl
  omega

end Complexity.Univ
