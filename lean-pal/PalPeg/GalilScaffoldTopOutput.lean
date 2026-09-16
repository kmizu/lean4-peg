import PalPeg.GalilScaffoldTopBranches

/-!
# Output soundness on the unified VM

Scala refreshes `output = left.isFirst` whenever R stands on a letter. With
`leftFirst s := position s.left = 1` and `onLetter s` := R on the `k`-th
letter (encoded position `2k-1`), a refreshed output `true` under the scan
invariant means the first `k` letters form a palindrome (`scan_output`).
Completeness — output `true` whenever the prefix is a palindrome — is the
global Galil invariant that the current centre is the right one, and is not
a local fact.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController

def leftFirstVM (s : GalilVM) : Prop := position s.left = 1

def onLetterVM (raw : List (Fin 2)) (s : GalilVM) : Prop :=
  ∃ k, 0 < k ∧ k ≤ raw.length ∧ position s.right = 2*k-1

/-- A refreshed output under the scan invariant is sound. -/
theorem output_sound (raw : List (Fin 2)) (s : GalilVM) (old o : Bool) {c r : ℕ}
    (hi : ScanInvariant raw c r s.left s.right) (k : ℕ) (hk : 0 < k) (hk2 : k ≤ raw.length)
    (hr : position s.right = 2*k-1)
    (ho : (onLetterVM raw s → (o = true ↔ leftFirstVM s)) ∧ (¬ onLetterVM raw s → o = old))
    (hout : o = true) : IsPal (raw.take k) := by
  have hon : onLetterVM raw s := ⟨k, hk, hk2, hr⟩
  have hl : leftFirstVM s := (ho.1 hon).1 hout
  exact scan_output hi k hk hk2 hl hr

/-- The same through the frame's `refresh`. -/
theorem refresh_sound (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9) (s : GalilVM) (old o : Bool) {c r : ℕ}
    (hi : ScanInvariant raw c r s.left s.right) (k : ℕ) (hk : 0 < k) (hk2 : k ≤ raw.length)
    (hr : position s.right = 2*k-1)
    (ho : refresh (galilFrame P q first) s old o) (hout : o = true) : IsPal (raw.take k) := by
  apply output_sound raw s old o hi k hk hk2 hr _ hout
  simp only [refresh, galilFrame] at ho
  rw [hP, hP'] at ho
  exact ho

#print axioms output_sound
#print axioms refresh_sound

end PalPeg.GalilScaffoldChainInputSupply
