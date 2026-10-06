import Complexity.Univ.Growth

/-!
# A closed bound on the steps of the simulator

Every simulated step costs at most `stepCost` of a configuration of size at most `csz c + B·growth T`
(`frun_csz`), so `B` steps cost at most `10 + B · 1000 · (tsz T + csz c + B·growth T + 2)^4` (`simCost_le`).
-/

namespace Complexity.Univ

/-- The closed bound on `B` simulated steps. -/
def simBound (T : TTable) (c : FCfg) (B : Nat) : Nat := 10 + B * (1000 * (tsz T + csz c + B * growth T + 2) ^ 4)

theorem simCost_le_aux {T : TTable} (hT : RowsOK T) {c : FCfg} (hc : CfgOK T c) (hn : Nice c) (B : Nat) :
    ∀ b, b ≤ B → simCost T c b ≤ 10 + b * (1000 * (tsz T + csz c + B * growth T + 2) ^ 4)
  | 0, _ => by simp [simCost]
  | b + 1, hb => by
    have ih := simCost_le_aux hT hc hn B b (by omega)
    have hs := (frun_csz hT hc hn b).1
    have hb' : b * growth T ≤ B * growth T := Nat.mul_le_mul_right _ (by omega)
    have hstep : stepCost T (frun T c b) ≤ 1000 * (tsz T + csz c + B * growth T + 2) ^ 4 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    simp only [simCost]
    rw [Nat.succ_mul]
    omega

/-- **The steps of `B` simulated steps.** -/
theorem simCost_le {T : TTable} (hT : RowsOK T) {c : FCfg} (hc : CfgOK T c) (hn : Nice c) (B : Nat) :
    simCost T c B ≤ simBound T c B :=
  simCost_le_aux hT hc hn B B (Nat.le_refl _)

end Complexity.Univ
