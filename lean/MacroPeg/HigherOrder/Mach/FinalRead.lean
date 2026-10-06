import MacroPeg.HigherOrder.Mach.Decide

/-!
# An accepted final state is a correct reading

When the reading machine ends with `ok`, its final state is a reading of an instance that reads back and types
(`final_readOK`).
-/

namespace Shallot.MacroPeg.Mach

open Shallot.MacroPeg.HO
open Shallot.MacroPeg.Flat

/-- **The final state of an accepted reading is a correct reading.** -/
theorem final_readOK {tk : List Nat} (hok : (finalSt tk).ok = true) :
    ∃ R bis is x, ReadOK (finalSt tk) R bis is x := by
  by_cases h : ∃ g s₀ x bis is, deser tk = some (g, s₀, x) ∧ checkRules g = some bis ∧
      inferE g.types [] s₀ = some (.p, is)
  · obtain ⟨g, s₀, x, bis, is, hd, hcr, hinf⟩ := h
    obtain ⟨n, st, hreach, hr, hn⟩ := read_ok hd hcr hinf
    have hfin : finalSt tk = st := final_of_reach hreach hr.ctl (by omega)
    exact ⟨g.types, bis, is, x, hfin ▸ hr⟩
  · have hf := final_of_fails (read_fail (fun g s₀ x bis is h₁ h₂ h₃ => h ⟨g, s₀, x, bis, is, h₁, h₂, h₃⟩))
    rw [hok] at hf
    cases hf

end Shallot.MacroPeg.Mach
