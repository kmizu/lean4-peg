import MacroPeg.HigherOrder.Mach.Order
import MacroPeg.HigherOrder.Mach.Halt

/-!
# The decision from the reading machine

Read the tokens with the reading machine; if it accepts, check the orders (`ordOK`) and compute the answer from its
tables (`startCodeM`): `numDecide`. It is the packed procedure (`numDecide_eq`), so it decides the uniform problem
(`numDecide_iff`).
-/

namespace Shallot.MacroPeg.Mach

open Shallot.MacroPeg.HO
open Shallot.MacroPeg.Flat

/-- The decision from the final state of the reading machine. -/
def numDecide (j : Nat) (bits : List Bool) : Bool :=
  let st := finalSt (Complexity.ofBits bits)
  st.ok && ordOK j st && (startCodeM (st.x.map Char.ofNat) st.tt st.ct st.lt st.rt st.bodies st.start == 2)

theorem codes_chars (x : List Char) : (x.map Char.toNat).map Char.ofNat = x := by
  induction x with
  | nil => rfl
  | cons c x ih => simp only [List.map_cons, ih, Char.ofNat_toNat]

theorem final_ok_false {j : Nat} {bits : List Bool}
    (h : ∀ g s₀ x bis is, deser (Complexity.ofBits bits) = some (g, s₀, x) → checkRules g = some bis →
      inferE g.types [] s₀ = some (.p, is) → False) :
    numDecide j bits = false := by
  have := final_of_fails (read_fail h)
  simp [numDecide, this]

theorem numDecide_eq (j : Nat) (bits : List Bool) : numDecide j bits = flatDecideP j bits := by
  unfold flatDecideP
  rcases hd : deser (Complexity.ofBits bits) with _ | ⟨g, s, x⟩
  · exact final_ok_false (fun _ _ _ _ _ h => by rw [hd] at h; cases h)
  · dsimp only
    rcases hcr : checkRules g with _ | bis
    · exact final_ok_false (fun _ _ _ _ _ h₁ h₂ => by
        rw [hd] at h₁; cases h₁; rw [hcr] at h₂; cases h₂)
    · rcases hinf : inferE g.types [] s with _ | ⟨_ | ⟨a, b⟩, is⟩
      · exact final_ok_false (fun _ _ _ _ _ h₁ _ h₃ => by
          rw [hd] at h₁; cases h₁; rw [hinf] at h₃; cases h₃)
      · obtain ⟨n, st, hreach, hr, hn⟩ := read_ok hd hcr hinf
        have hfin : finalSt (Complexity.ofBits bits) = st := final_of_reach hreach hr.ctl (by omega)
        dsimp only
        simp only [numDecide, hfin, hr.ok, Bool.true_and, hr.x, codes_chars, startCodeM_eq hr]
        congr 1
        exact Bool.eq_iff_iff.2 (by rw [ordOK_iff j hr hcr hinf]; exact decide_eq_true_iff.symm)
      · exact final_ok_false (fun _ _ _ _ _ h₁ h₂ h₃ => by
          rw [hd] at h₁; cases h₁; rw [hinf] at h₃; cases h₃)

/-- **The decision from the reading machine decides the uniform problem.** -/
theorem numDecide_iff (j : Nat) (bits : List Bool) : numDecide j bits = true ↔ KExp.UMPEG j bits := by
  rw [numDecide_eq]; exact flatDecideP_iff j bits

end Shallot.MacroPeg.Mach
