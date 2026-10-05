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

/-- Steps of three stages, where the second runs when `ok` and the third when also `ord`. -/
def stagesCost (ok ord : Bool) (a b c : Nat) : Nat := a + (if ok then b + (if ord then c else 0) else 0)

theorem stagesCost_fail (ord : Bool) (a b c : Nat) : stagesCost false ord a b c = a := by simp [stagesCost]
theorem stagesCost_high (a b c : Nat) : stagesCost true false a b c = a + b := by simp [stagesCost]
theorem stagesCost_all (a b c : Nat) : stagesCost true true a b c = a + b + c := by simp [stagesCost]; omega

/-- The steps of the whole decision on the bits `w`: only the stages that run are counted. -/
def mainCost (j : Nat) (w : List Bool) : Nat :=
  stagesCost (finalSt (ofBits w)).ok (ordOK j (finalSt (ofBits w))) (readStageCost w)
    (ordStageCost j (capOf w) (finalSt (ofBits w))) (evalStageCost j (capOf w) (finalSt (ofBits w)))

theorem finalSt_minv (tk : List Nat) : MInv (finalSt tk) := minv_pruns (minv_pinit tk) _

/-- **The decision on stacks halts with `numDecideT j w`.** -/
theorem mainP_halts (j : Nat) (w : List Bool) :
    ∃ S', NHalts (mainP j) (nInit NK w) (numDecideT j w) S' (mainCost j w) := by
  cases hok : (finalSt (ofBits w)).ok
  · -- the reading fails
    obtain ⟨S', x₁⟩ := readStage_fail w hok
    have hv : numDecideT j w = false := by simp [numDecideT, hok]
    exact ⟨S', hv ▸ (NHalts.seq x₁).mono (by rw [mainCost, hok, stagesCost_fail]; exact Nat.le_refl _)⟩
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
      rw [mainCost, hok, ho, stagesCost_high]; unfold ordStageCost; omega
    · -- the tables and the evaluation
      have x₂ := ordStage_rest (cap := capOf w) hi
      obtain ⟨S', x₃⟩ := evalStage_halts j (capOf w) hi hr
      have hv : numDecideT j w = (startCodeT j (capOf w) ((finalSt (ofBits w)).x.map Char.ofNat)
          (finalSt (ofBits w)).tt (finalSt (ofBits w)).ct (finalSt (ofBits w)).lt (finalSt (ofBits w)).rt
          (finalSt (ofBits w)).bodies (finalSt (ofBits w)).start == 2) := by
        simp [numDecideT, hok, ho]
      refine ⟨S', hv ▸ (x₁.seqH ((h₁.seq ((hT ho).seq x₂)).seqH x₃)).mono ?_⟩
      rw [mainCost, hok, ho, stagesCost_all]; unfold ordStageCost; omega

end Shallot.MacroPeg.Mach
