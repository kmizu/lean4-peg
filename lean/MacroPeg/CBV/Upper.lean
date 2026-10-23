import MacroPeg.CBV.InputMachine
import Shallot.Peg.Separation.Upper

namespace Shallot.MacroPeg.CBV

open Complexity Shallot.MacroPeg.KExp

/-- The same four-bit character decoding used for the fixed CBN witness. -/
def encodedLanguage (g : MGrammar) (s : Strategy) (e : MExp) : Lang :=
  fun w => SObs g s e (Shallot.PegSeparation.tokenWord w) (some [])

/-- Every fixed first-order CBV grammar, for either strategy, is recognized in polynomial time
by an actual TM starting at the encoded bit input. Dictionary construction and every table access are charged. -/
theorem language_in_P (g : MGrammar) (s : Strategy) (e : MExp)
    (hg : g.FirstOrder) (hs : s ≠ .callByName) (he : e.FirstOrder) : KEXP 0 (encodedLanguage g s e) := by
  have hcost : IsPoly (fun n => 2 + setupCost n + loadedCost g e n) :=
    isPoly_add (isPoly_add (isPoly_const 2) setupCost_poly) (loadedCost_poly g e)
  obtain ⟨c, d, hcd⟩ := hcost
  let budget := fun N => 220 * (N + 1) + c * (N + 1) ^ d
  have hbudget : IsPoly budget := isPoly_add
    (isPoly_mul (isPoly_const 220) (isPoly_add isPoly_id (isPoly_const 1)))
    (isPoly_mul (isPoly_const c) (isPoly_pow (isPoly_add isPoly_id (isPoly_const 1)) d))
  apply Shallot.PegSeparation.nprog_in_P (by decide) (inputProgram g s e) (encodedLanguage g s e) budget hbudget
  intro w
  obtain ⟨b, S', hr, hb⟩ := inputProgram_halts g s e w
  have hn : (Shallot.PegSeparation.tokenWord w).length ≤ w.length := by
    simpa only [Shallot.PegSeparation.tokenWord, List.length_map] using ofBits_length_le w
  have hc := hcd (Shallot.PegSeparation.tokenWord w).length
  dsimp only at hc
  have hm := Nat.mul_le_mul_left c (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) d)
  refine ⟨b, S', hr.mono (by dsimp only [budget]; omega), ?_⟩
  exact hb.trans (numericAccept_iff hg hs he _)

end Shallot.MacroPeg.CBV
