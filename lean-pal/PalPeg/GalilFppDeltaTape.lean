import PalPeg.GalilFppDelta
import PalPeg.GalilFppFallbackLoop
import PalPeg.GalilFppFrontier

set_option autoImplicit false
namespace PalPeg.GalilFppDeltaTape
open GalilFppDelta GalilFppInstruction GalilFppCode GalilFppMaterialize GalilFppFallbackBits GalilFppFallbackLoop

/-- Delimiter positions in the tape 0 (1^delta(0) 0) (1^delta(1) 0) ... . -/
def position (f : ℕ → ℕ) (n : ℕ) : ℕ := n + deltaSum f 0 n

theorem position_step (f : ℕ → ℕ) (n : ℕ) :
    position f (n+1) = position f n + delta f n + 1 := by
  have hh := deltaSum_add f 0 n 1
  simp only [Nat.zero_add] at hh
  have hsingle : deltaSum f n 1 = delta f n := by simp [deltaSum]
  rw [hsingle] at hh
  unfold position
  omega

/-- A finite, physical C-tape specification with explicit delimiters. -/
def Tape (t : ℕ → Fin 9) (f : ℕ → ℕ) (upto : ℕ) : Prop :=
  (∀ n, n ≤ upto → t (position f n) = 7) ∧
  (∀ n, n < upto → ∀ k, k < delta f n → t (position f n + 1 + k) = 8)

theorem tape_mono {t : ℕ → Fin 9} {f : ℕ → ℕ} {m n : ℕ}
    (ht : Tape t f n) (hm : m ≤ n) : Tape t f m := by
  exact ⟨fun k hk => ht.1 k (by omega), fun k hk => ht.2 k (by omega)⟩

/-- Delta values in exactly the order used by a leftward fallback. -/
def backwards (f : ℕ → ℕ) (lo : ℕ) : ℕ → List ℕ
  | 0 => []
  | n+1 => delta f (lo+n) :: backwards f lo n

theorem backwards_length (f : ℕ → ℕ) (lo n : ℕ) : (backwards f lo n).length = n := by
  induction n <;> simp_all [backwards]

theorem backwards_sum (f : ℕ → ℕ) (lo n : ℕ) : (backwards f lo n).sum = deltaSum f lo n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hh := deltaSum_add f lo n 1
    have hsingle : deltaSum f (lo+n) 1 = delta f (lo+n) := by simp [deltaSum]
    rw [hsingle] at hh
    simp only [backwards, List.sum_cons, ih]
    omega

theorem position_span (f : ℕ → ℕ) (lo n : ℕ) :
    position f (lo+n) = position f lo + (backwards f lo n).sum + n := by
  have hh := deltaSum_add f 0 lo n
  rw [backwards_sum]
  simp only [Nat.zero_add] at hh
  unfold position
  omega

/-- A correctly encoded C tape supplies every concrete bit premise of the
actual fallback loop; callers no longer supply a separate Blocks witness. -/
theorem tape_blocks (t : ℕ → Fin 9) (f : ℕ → ℕ) (upto lo n : ℕ)
    (ht : Tape t f upto) (hn : lo+n ≤ upto) :
    Blocks t (position f (lo+n)) (backwards f lo n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    have hp := position_step f (lo+n)
    have he : lo+(n+1) = lo+n+1 := by omega
    rw [he, backwards]
    have hsub : position f (lo+n+1) - (delta f (lo+n)+1) = position f (lo+n) := by omega
    refine ⟨by omega, ?_, ?_, ?_⟩
    · intro k hk
      have hindex : position f (lo+n+1) - (k+1) =
          position f (lo+n) + 1 + (delta f (lo+n)-1-k) := by omega
      rw [hindex]
      exact ht.2 (lo+n) (by omega) _ (by omega)
    · rw [hsub]
      exact ht.1 (lo+n) (by omega)
    · rw [hsub]
      exact ih (by omega)

variable {α : Type} [DecidableEq α]

theorem delta_zero (w : List α) : delta (failure w) 0 = 1 := by
  have hf := failure_le w 1
  have hf₁ : failure w 1 = 0 := by omega
  simp [delta, failure_zero, hf₁]

/-- Scala's initial C=010 is the initial delimiter followed by delta(0).
Thus the tape representation includes the initialization case as well. -/
theorem initial_tape (w : List α) : Tape GalilFppFrontier.initialC (failure w) 1 := by
  constructor
  · intro n hn
    interval_cases n <;> simp [position, deltaSum, delta_zero, GalilFppFrontier.initialC]
  · intro n hn k hk
    have hn₀ : n = 0 := by omega
    subst n
    rw [delta_zero] at hk
    have hk₀ : k = 0 := by omega
    subst k
    simp [position, deltaSum, GalilFppFrontier.initialC]

/-- Full actual append-distance fallback agrees with the mathematical
failure link, given a correctly encoded C prefix and the unary S gap.
The delta sum bound and all concrete loop-bit premises are derived here. -/
theorem fallback_failure (j : Fin 4) (w : List α) (p : ℕ) (x : Config) (q : List (Fin 2))
    (hp : x.pc = 97+offset j) (hA : x.pos 0 = p)
    (hT : StackAt (x.tape 4) (x.pos 4) [])
    (hS : x.pos 3 = p - failure w p) (hsleft : x.tape 3 0 = 4)
    (hsend : ∀ k, p - failure w p < k → x.tape 3 k = 6)
    (hsones : ∀ k, 1 ≤ k → k ≤ p - failure w p → x.tape 3 k = 8)
    (hC : x.pos 2 = position (failure w) p)
    (htape : Tape (x.tape 2) (failure w) p) (hq : QueueAt x q) :
    ∃ y qs, Steps code x qs y ∧ qs.length ≤ 20*(p-failure w p)+5 ∧
      y.pc = 68+offset j ∧ y.pos 0 = failure w p ∧
      y.pos 3 = failure w p - failure w (failure w p) ∧
      y.pos 2 = position (failure w) (failure w p) ∧ y.tape 2 = x.tape 2 ∧
      StackAt (y.tape 4) (y.pos 4) [] ∧ QueueAt y (q ++ List.replicate (p-failure w p) 1) ∧
      Unary (y.tape 3) (y.pos 3) ∧ Tape (y.tape 2) (failure w) (failure w p) ∧
      y.pos 1 = x.pos 1 := by
  let ds := backwards (failure w) (failure w p) (p-failure w p)
  have hlen : ds.length = p-failure w p := backwards_length _ _ _
  have hsum : ds.sum = deltaSum (failure w) (failure w p) (p-failure w p) := backwards_sum _ _ _
  have hf := failure_le w p
  have hjoin : failure w p + (p-failure w p) = p := by omega
  have hbits : Blocks (x.tape 2) (x.pos 2) ds := by
    rw [hC]
    have hh := tape_blocks (x.tape 2) (failure w) p (failure w p) (p-failure w p) htape (by omega)
    simpa only [hjoin] using hh
  have hbound : ds.sum ≤ ds.length := by rw [hsum, hlen]; exact crossed_ones_le w p
  obtain ⟨y, qs, hs, hl, hypc, hyA, hyS, hyC, hyt, hyT, hyq, hyu, hyB⟩ :=
    fallback j ds x q hp (by rw [hlen, hA]; omega) hT (by simpa [hlen] using hS)
      hsleft (by simpa [hlen] using hsend) (by simpa [hlen] using hsones) hbound hbits hq
  have hgap := fallback_gap w p
  have hspan := position_span (failure w) (failure w p) (p-failure w p)
  rw [hjoin] at hspan
  refine ⟨y, qs, hs, ?_, hypc, ?_, ?_, ?_, hyt, hyT, ?_, hyu, ?_, hyB⟩
  · rw [hlen] at hbound hl; omega
  · rw [hA, hlen] at hyA; omega
  · rw [hlen, hsum] at hyS; omega
  · rw [hC, hlen] at hyC
    change position (failure w) p = position (failure w) (failure w p) + ds.sum + (p-failure w p) at hspan
    omega
  · simpa [hlen] using hyq
  · rw [hyt]
    exact tape_mono htape (by omega)

#print axioms initial_tape
#print axioms fallback_failure
end PalPeg.GalilFppDeltaTape
