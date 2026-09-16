import PalPeg.GalilLiveCentreReplay
import PalPeg.GalilScaffoldTopOutputSound

/-!
# Output completeness at a report point

`refresh_sound` (in `PalPeg.GalilScaffoldTopOutput`) shows that a refreshed
output `true` at a letter place means the prefix is a palindrome. The converse
is not a local fact: it needs the global Galil invariant that the tracked
centre really is the leftmost live centre. `MInv` is exactly that invariant, so
here we upgrade soundness to an equivalence at report points.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- At a report point (right head on the `k`-th letter, not replaying), with the centre
invariant, the left head stands on the first letter exactly when the first `k` letters are a
palindrome. -/
theorem leftFirst_iff_pal {raw : List (Fin 2)} {c : Control} {s : GalilVM} {r k : ℕ}
    (hi : ScanInvariant raw (position s.center) r s.left s.right) (hM : MInv raw c s)
    (hr : c.replaying = false) (hk : 0 < k) (hk2 : k ≤ raw.length) (hpos : position s.right = 2*k-1) :
    leftFirstVM s ↔ IsPal (raw.take k) := by
  have hL : Leftmost raw (2*k-1) (position s.center) := by
    have h := minv_leftmost hM hr
    rw [hpos] at h
    exact h
  have hrep := leftmost_report hk hk2 hL
  have hl := hi.leftPos
  have hrt := hi.rightPos
  rw [hpos] at hrt
  constructor
  · intro hf
    refine hrep.2 ?_
    simp only [leftFirstVM] at hf
    omega
  · intro hp
    have hC := hrep.1 hp
    simp only [leftFirstVM]
    omega

/-- The refreshed output at a report point is exactly the palindrome flag. -/
theorem refresh_exact (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9) {c : Control} {s : GalilVM} {r k : ℕ}
    (hi : ScanInvariant raw (position s.center) r s.left s.right) (hM : MInv raw c s)
    (hr : c.replaying = false) (hk : 0 < k) (hk2 : k ≤ raw.length) (hpos : position s.right = 2*k-1)
    (old o : Bool) (ho : refresh (galilFrame P q first) s old o) :
    o = true ↔ IsPal (raw.take k) := by
  simp only [refresh, galilFrame] at ho
  rw [hP, hP'] at ho
  have hon : onLetterVM raw s := ⟨k, hk, hk2, hpos⟩
  exact (ho.1 hon).trans (leftFirst_iff_pal hi hM hr hk hk2 hpos)

#print axioms leftFirst_iff_pal
#print axioms refresh_exact

end PalPeg.GalilScaffoldChainInputSupply
