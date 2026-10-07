import Complexity.Undec.K1Defs
import Complexity.OneTape.Main

/-!
# A one-tape machine accepting its own code is undecidable

No Turing machine decides `K1` (`k1_undecidable`): a decider can be made one-tape (`oneTape_decides`), and swapping
its accepting and rejecting states (`TM.decides_compl`) gives a one-tape machine deciding the complement; on its own
code it accepts exactly when it does not.
-/

namespace Complexity

/-- **No Turing machine decides whether a one-tape table accepts its own code.** -/
theorem k1_undecidable : ¬ TMDecidable K1 := by
  rintro ⟨k, M, hM⟩
  obtain ⟨M₁, h₁⟩ := oneTape_decides M K1 hM
  obtain ⟨D, hD⟩ := TM.decides_compl h₁
  have e₁ := accepts_iff hD (code1 D)
  have e₂ := k1_code D
  have : K1 (code1 D) ↔ ¬ K1 (code1 D) := e₂.trans e₁
  have np : ¬ K1 (code1 D) := fun p => this.1 p p
  exact np (this.2 np)

end Complexity
