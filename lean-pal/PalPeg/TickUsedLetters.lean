import PalPeg.GalilLookRefined

/-!
# The letters used by the target of a tick

A truncated tick is legitimate when the letters used by its source and by its target, and the
lookahead of its source, have arrived (`GalilLookRefined.tick_trunc'`).  The starvation test of
the local layer reads the source only, so the letters used by the target have to be bounded by
the source.  Here: a background tick keeps the three heads, and its chain either ticks (within
its refined lookahead, `chainTick_used'`), stays idle, or is born on the centre head.
-/

set_option autoImplicit false

namespace PalPeg.TickUsedLetters

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilThrottledRun (usedPH usedChain usedVM)
open PalPeg.GalilTruncTick (usedVM_left usedVM_center usedVM_right)
open PalPeg.GalilLookRefined (lookChain' chainTick_used')

/-- **The letters used after a background tick**: those used before, or the refined lookahead of
the chain. -/
theorem usedVM_background_le (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    {s s' : GalilVM} (hbackground : (galilFrameS P q first).background s s') :
    usedVM raw s' ≤ max (usedVM raw s) (lookChain' raw.length s.chain) := by
  obtain ⟨hleft, hright, hchain, hcenter, -⟩ := backgroundS_fields P q first hbackground
  have hchainBound : usedChain raw.length s'.chain
      ≤ max (usedVM raw s) (lookChain' raw.length s.chain) := by
    rcases hchain with ⟨_, htick⟩ | ⟨_, _, hidle⟩ | ⟨_, _, hborn⟩
    · exact le_trans (chainTick_used' raw.length htick) (le_max_right _ _)
    · rw [hidle]
      exact Nat.zero_le _
    · simp only [Bool.false_eq_true, if_false] at hborn
      rw [hborn]
      exact le_trans (usedVM_center raw s) (le_max_left _ _)
  have hl := usedVM_left raw s
  have hc := usedVM_center raw s
  have hr := usedVM_right raw s
  show max (max (usedPH raw.length s'.left) (usedPH raw.length s'.center))
      (max (usedPH raw.length s'.right) (usedChain raw.length s'.chain)) ≤ _
  rw [hleft, hcenter, hright]
  omega

#print axioms usedVM_background_le

end PalPeg.TickUsedLetters
