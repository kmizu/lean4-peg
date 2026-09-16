import PalPeg.GalilLiveCentreReplay
import PalPeg.Chain

/-!
# The centre sequence of a word

`Cw w m` is the leftmost live centre at the letter place `2m-1`, defined
from the word alone (through `Lw`, the leftmost live centre at any place,
defaulting to the place itself when no centre is live). It is at least `m`,
monotone in `m`, equals `|w|` at the end exactly for palindromes, and agrees
with the controller's centre whenever the centre invariant holds.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldInputHead GalilScaffoldChainVerifier

open Classical in
/-- The leftmost live centre at place `n` (or `n` when none is live). -/
noncomputable def Lw (w : List (Fin 2)) (n : ℕ) : ℕ :=
  if h : ∃ c, Live w n c then Nat.find h else n

/-- The leftmost live centre at the letter place `2m-1`. -/
noncomputable def Cw (w : List (Fin 2)) (m : ℕ) : ℕ := Lw w (2*m-1)

theorem live_self {w : List (Fin 2)} {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 2 * w.length) : Live w n n := by
  refine ⟨le_refl n, by omega, ?_⟩
  have hl : (encoded w).length = 2 * w.length + 1 := by
    simp [encoded, pairs_length]
  refine ⟨by omega, by omega, fun i hi => ?_⟩
  have : i = 0 := by omega
  subst this; rfl

theorem lw_leftmost {w : List (Fin 2)} {n : ℕ} (h : ∃ c, Live w n c) : Leftmost w n (Lw w n) := by
  classical
  unfold Lw
  rw [dif_pos h]
  exact ⟨Nat.find_spec h, fun c hc => Nat.find_min' h hc⟩

theorem lw_le (w : List (Fin 2)) (n : ℕ) : Lw w n ≤ n := by
  classical
  by_cases h : ∃ c, Live w n c
  · exact (lw_leftmost h).1.1
  · unfold Lw; rw [dif_neg h]

theorem lw_mono (w : List (Fin 2)) (n : ℕ) : Lw w n ≤ Lw w (n+1) := by
  classical
  by_cases h : ∃ c, Live w (n+1) c
  · have hL := lw_leftmost h
    by_cases hc : Lw w (n+1) ≤ n
    · have hl := live_pred hL.1 hc
      exact (lw_leftmost ⟨_, hl⟩).2 _ hl
    · have := lw_le w n
      omega
  · have e : Lw w (n+1) = n+1 := by unfold Lw; rw [dif_neg h]
    have := lw_le w n
    omega

theorem cw_leftmost {w : List (Fin 2)} {m : ℕ} (h1 : 1 ≤ m) (h2 : m ≤ w.length) :
    Leftmost w (2*m-1) (Cw w m) :=
  lw_leftmost ⟨_, live_self (by omega) (by omega)⟩

theorem cw_ge (w : List (Fin 2)) (m : ℕ) : m ≤ Cw w m := by
  classical
  unfold Cw
  by_cases h : ∃ c, Live w (2*m-1) c
  · have := (lw_leftmost h).1.2.1
    omega
  · unfold Lw; rw [dif_neg h]; omega

theorem cw_mono (w : List (Fin 2)) (m : ℕ) : Cw w m ≤ Cw w (m+1) := by
  unfold Cw
  by_cases hm : m = 0
  · subst hm
    have := lw_le w (2*0-1)
    omega
  · have e : 2*(m+1)-1 = (2*m-1) + 1 + 1 := by omega
    rw [e]
    exact le_trans (lw_mono w _) (lw_mono w _)

theorem cw_pal {w : List (Fin 2)} (hw : 0 < w.length) (hp : w ∈ PAL) : Cw w w.length = w.length := by
  have hL := cw_leftmost (w := w) (m := w.length) (by omega) (le_refl _)
  have hp' : IsPal (w.take w.length) := by
    rw [List.take_length]; exact (mem_PAL_iff_isPal w).1 hp
  exact (leftmost_report hw (le_refl _) hL).1 hp'

theorem leftmost_unique {w : List (Fin 2)} {n C C' : ℕ} (h : Leftmost w n C) (h' : Leftmost w n C') :
    C = C' :=
  Nat.le_antisymm (h.2 _ h'.1) (h'.2 _ h.1)

theorem cw_eq_of_minv {w : List (Fin 2)} {c : Control} {s : GalilVM} {m : ℕ} (h : MInv w c s)
    (hr : c.replaying = false) (hpos : position s.right = 2*m-1) : position s.center = Cw w m := by
  have hL := minv_leftmost h hr
  rw [hpos] at hL
  exact leftmost_unique hL (lw_leftmost ⟨_, hL.1⟩)

#print axioms cw_leftmost
#print axioms cw_ge
#print axioms cw_mono
#print axioms cw_pal
#print axioms cw_eq_of_minv

end PalPeg.GalilScaffoldChainInputSupply
