import MacroPeg.HigherOrder.Mach.MainEval
import MacroPeg.HigherOrder.Mach.FinalRead
import MacroPeg.HigherOrder.Mach.DecideT

/-!
# The whole decision on stacks

`mainP j` reads the bits, checks the orders, builds the tables and evaluates. From the bits `w` it halts with
`numDecideT j w` (`mainP_halts`), which decides the uniform problem of order `j`.
-/

namespace Shallot.MacroPeg.Mach

open Complexity

/-- The decision of the uniform problem of order `j` on stacks. -/
def mainP (j : Nat) : NProg NK := .seq readStageP (.seq (ordStageP j) (evalStageP j))

/-- The steps of the whole decision on the bits `w`. -/
def mainCost (j : Nat) (w : List Bool) : Nat :=
  readStageCost w + ordStageCost j (capOf w) (finalSt (ofBits w)) + evalStageCost j (capOf w) (finalSt (ofBits w))

theorem finalSt_minv (tk : List Nat) : MInv (finalSt tk) := minv_pruns (minv_pinit tk) _

/-- **The decision on stacks halts with `numDecideT j w`.** -/
theorem mainP_halts (j : Nat) (w : List Bool) :
    ∃ S', NHalts (mainP j) (nInit NK w) (numDecideT j w) S' (mainCost j w) := by
  cases hok : (finalSt (ofBits w)).ok
  · -- the reading fails
    obtain ⟨S', x₁⟩ := readStage_fail w hok
    have hv : numDecideT j w = false := by simp [numDecideT, hok]
    exact ⟨S', hv ▸ (NHalts.seq x₁).mono (by unfold mainCost; omega)⟩
  · obtain ⟨R, bis, is, x, hr⟩ := final_readOK hok
    have hi := finalSt_minv (ofBits w)
    have x₁ : NRuns readStageP (nInit NK w) (baseSt (finalSt (ofBits w)) (capOf w)) (readStageCost w) :=
      readStage_ok w hok
    obtain ⟨h₁, hT, hF⟩ := ordStage_first j (capOf w) hi hr
    cases ho : ordOK j (finalSt (ofBits w))
    · -- an order is too high
      obtain ⟨S', x₂⟩ := hF ho
      have hv : numDecideT j w = false := by simp [numDecideT, hok, ho]
      refine ⟨S', hv ▸ (x₁.seqH (NHalts.seq (h₁.seqH (NHalts.seq x₂)))).mono ?_⟩
      unfold mainCost ordStageCost; omega
    · -- the tables and the evaluation
      have x₂ := ordStage_rest (cap := capOf w) hi
      obtain ⟨S', x₃⟩ := evalStage_halts j (capOf w) hi hr
      have hv : numDecideT j w = (startCodeT j (capOf w) ((finalSt (ofBits w)).x.map Char.ofNat)
          (finalSt (ofBits w)).tt (finalSt (ofBits w)).ct (finalSt (ofBits w)).lt (finalSt (ofBits w)).rt
          (finalSt (ofBits w)).bodies (finalSt (ofBits w)).start == 2) := by
        simp [numDecideT, hok, ho]
      refine ⟨S', hv ▸ (x₁.seqH ((h₁.seq ((hT ho).seq x₂)).seqH x₃)).mono ?_⟩
      unfold mainCost ordStageCost; omega

end Shallot.MacroPeg.Mach
