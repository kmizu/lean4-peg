import PalPeg.GalilScaffoldChainFallback

/-!
# The leftmost live centre (the completeness invariant)

At right place `n` a centre `c` is *live* when the places `2c-n .. n` form
a palindrome centred at `c`. Galil's machine keeps its centre `C` at the
leftmost live centre. A matched comparison keeps `C` live and leftmost;
when `C` dies at the next place, the fallback's choice — the largest
radius `r` with a palindrome `(n+1-r .. n+1)` inside the candidate window —
is again the leftmost live centre, provided the window covers every radius
below the old one. At a letter place `2k-1` the prefix `raw.take k` is a
palindrome exactly when the leftmost live centre is `k`.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open Manacher GalilScaffoldInputHead GalilScaffoldChainVerifier

/-- `c` is a live centre at right place `n`. -/
def Live (raw : List (Fin 2)) (n c : ℕ) : Prop := c ≤ n ∧ n < 2*c ∧ PalAt (encoded raw) c (n - c)

/-- `C` is the leftmost live centre at right place `n`. -/
def Leftmost (raw : List (Fin 2)) (n C : ℕ) : Prop := Live raw n C ∧ ∀ c, Live raw n c → C ≤ c

theorem live_pred {raw : List (Fin 2)} {n c : ℕ} (h : Live raw (n+1) c) (hc : c ≤ n) : Live raw n c :=
  ⟨hc, by have := h.2.1; omega, h.2.2.mono (by omega)⟩

/-- The live centre at `n` given by the scan invariant. -/
theorem live_of_scanInvariant {raw : List (Fin 2)} {cen rad : ℕ} {l r : PlaceHead}
    (hi : ScanInvariant raw cen rad l r) : Live raw (position r) cen := by
  have hp := hi.rightPos
  have hlp := hi.leftPos
  have hl1 : 1 ≤ position l := by
    have h0 := (represented_position l.head raw hi.leftRep hi.leftPresent).1
    unfold position
    split <;> omega
  refine ⟨by omega, by omega, ?_⟩
  have e : position r - cen = rad := by omega
  rw [e]; exact hi.palindrome

/-- A matched comparison keeps the leftmost live centre. -/
theorem leftmost_match {raw : List (Fin 2)} {n C : ℕ} (h : Leftmost raw n C) (hl : Live raw (n+1) C) :
    Leftmost raw (n+1) C := by
  refine ⟨hl, fun c hc => ?_⟩
  by_cases hcn : c ≤ n
  · exact h.2 c (live_pred hc hcn)
  · have h1 := hc.1
    have h2 := h.1.1
    omega

/-- When the centre dies at `n+1`, the fallback's largest radius inside a
window covering every radius below the old one gives the new leftmost live
centre `n+1-r`. -/
theorem leftmost_fallback {raw : List (Fin 2)} {n C W r : ℕ} (h : Leftmost raw n C)
    (hdead : ¬ Live raw (n+1) C) (hW : 2*(n - C) + 1 ≤ W)
    (hrn : 2*r < n+1) (hpal : PalAt (encoded raw) (n+1-r) r)
    (hmax : ∀ r', 2*r'+1 ≤ W → PalAt (encoded raw) (n+1-r') r' → r' ≤ r) :
    Leftmost raw (n+1) (n+1-r) := by
  have hr : r ≤ n+1-r := hpal.1
  refine ⟨⟨by omega, by omega, ?_⟩, fun c hc => ?_⟩
  · have e : n+1-(n+1-r) = r := by omega
    rw [e]; exact hpal
  · by_cases hcn : c ≤ n
    · have hlive := live_pred hc hcn
      have hCc := h.2 c hlive
      have hne : c ≠ C := fun e => hdead (e ▸ hc)
      have hlt : C < c := Nat.lt_of_le_of_ne hCc (fun e => hne e.symm)
      have e : n+1-(n+1-c) = c := by omega
      have hc2 : PalAt (encoded raw) (n+1-(n+1-c)) (n+1-c) := by
        rw [e]
        exact hc.2.2
      have hr'' := hmax (n+1-c) (by omega) hc2
      omega
    · omega

/-- At the letter place `2k-1` the prefix of `k` letters is a palindrome
exactly when the leftmost live centre is `k`. -/
theorem leftmost_report {raw : List (Fin 2)} {k C : ℕ} (hk : 0 < k) (hk2 : k ≤ raw.length)
    (h : Leftmost raw (2*k-1) C) : IsPal (raw.take k) ↔ C = k := by
  constructor
  · intro hp
    have hl : Live raw (2*k-1) k := by
      refine ⟨by omega, by omega, ?_⟩
      have e : 2*k-1-k = k-1 := by omega
      rw [e]; exact encoded_of_prefix_palindrome raw k hk hk2 hp
    have h1 := h.2 k hl
    have h2 : 2*k-1-C ≤ C := h.1.2.2.1
    omega
  · intro hC
    rw [hC] at h
    have hp := h.1.2.2
    have e : 2*k-1-k = k-1 := by omega
    rw [e] at hp
    exact prefix_palindrome_of_encoded raw k hk hk2 hp

#print axioms leftmost_fallback
#print axioms leftmost_report

end PalPeg.GalilScaffoldChainInputSupply
