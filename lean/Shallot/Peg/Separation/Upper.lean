import Shallot.Peg.Separation.Decider

/-!
# The diagonal language is in P on actual Turing machines

`KEXP 0` is the existing machine-based class with polynomial time bounds.
The concrete diagonal stack program has a polynomial budget; the verified
translations preserve polynomial time, with space obtained from time.
-/

namespace Shallot.PegSeparation

open Complexity Complexity.Univ Shallot.MacroPeg.KExp Shallot.MacroPeg.HO

/-- A concretely bounded polynomial-time stack decider gives a polynomial-time TM. -/
theorem nprog_in_P {K : Nat} (hK : 1 < K) (p : NProg K) (L : Lang) (T : Nat → Nat) (hT : IsPoly T)
    (h : ∀ w, ∃ b S', NHalts p (nInit K w) b S' (T w.length) ∧ (b = true ↔ L w)) : KEXP 0 L := by
  let B : Nat → Nat := fun n => 2 * n + T n * (T n + 2) + 2
  let S : Nat → Nat := fun n => B n + (2 * n + 2)
  let U : Nat → Nat := fun n => (n + 1) * 5 + T n * ncost (S n)
  have hruns : ∀ w, ∃ t b L', t ≤ U w.length ∧
      LExec (LenOK (S w.length)) (.seq (importP hK) p.compile) (initLists (K + 1) w) t (.stop b L') ∧
      (b = true ↔ L w) := by
    intro w
    obtain ⟨b, S', ⟨t, ht, hx⟩, hb⟩ := h w
    have hx₁ : NExec (NFits (B w.length)) p (nInit K w) t (.stop b S') :=
      (nexec_space hx 1 (2 * w.length) (bnd_nInit w)).2 _ (by
        have hg : grow 1 t ≤ T w.length * (T w.length + 2) := Nat.mul_le_mul ht (by omega)
        simp only [B]; omega)
    obtain ⟨t', ht', hx'⟩ := nprog_lexec hK p w (B := S w.length) (by simp only [S, B]; omega)
      (hx₁.mono (fun _ hS => hS.mono (by simp only [S]; omega)))
    refine ⟨t', b, _, ?_, hx', hb⟩
    have hm := Nat.mul_le_mul_right (ncost (S w.length)) ht
    simp only [U]; omega
  have hB : IsPoly B := isPoly_add (isPoly_add (isPoly_mul (isPoly_const 2) isPoly_id)
    (isPoly_mul hT (isPoly_add hT (isPoly_const 2)))) (isPoly_const 2)
  have hS : IsPoly S := isPoly_add hB (isPoly_add (isPoly_mul (isPoly_const 2) isPoly_id) (isPoly_const 2))
  have hU : IsPoly U := isPoly_add (isPoly_mul (isPoly_add isPoly_id (isPoly_const 1)) (isPoly_const 5))
    (isPoly_mul hT (isPoly_add (isPoly_mul (isPoly_const 8) hS) (isPoly_const 16)))
  have hTM : IsPoly (lmTime S U) := isPoly_add
    (isPoly_add (isPoly_mul (isPoly_const 4) isPoly_id) (isPoly_const 8))
    (isPoly_mul hU (isPoly_add (isPoly_mul (isPoly_const 8)
      (isPoly_add hS (isPoly_add isPoly_id (isPoly_const 2)))) (isPoly_const 20)))
  obtain ⟨M, hdec, hh⟩ := lm_time (by omega) (.seq (importP hK) p.compile) 3 (by decide)
    (nprog_constOK hK p) L S U hruns
  obtain ⟨c, d, hcd⟩ := hTM
  exact ⟨K + 1, M, lmTime S U, c, d, by simpa only [tower_zero] using hcd, hdec, hh⟩

/-- The concrete fixed-degree diagonal language is decidable in polynomial time. -/
theorem polyDiag_in_P (p : Nat) : KEXP 0 (PolyDiag p) :=
  nprog_in_P (by decide) (polyDiagP p) (PolyDiag p) (polyDiagBound p) (polyDiagBound_poly p) (polyDiagP_halts p)

end Shallot.PegSeparation
