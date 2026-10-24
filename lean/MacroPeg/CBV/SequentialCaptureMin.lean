import Complexity.NShrinkingCompare
import MacroPeg.CBV.SequentialSeqReturn

/-! Select the end of a captured interval from the saved and returned positions.
Original positions and both payload prefixes are preserved. -/
namespace Shallot.MacroPeg.CBV.SequentialCaptureMin
open Complexity SequentialSeqReturn

def select : NProg 4 :=
  .ite 2 .empty (.prim (.dup 1 2 (by decide)))
    (.seq (.prim (.pop 2)) (.prim (.dup 0 2 (by decide))))

def program : NProg 4 :=
  .seq (NShrinkingCompare.program 2 3)
    (.seq select (.seq (.prim (.pop 3)) (.prim (.dup 1 2 (by decide)))))

theorem fits_replace {B : Nat} {S : Lists 4} (h : NFits B S) (i : Fin 4) (l : List Nat)
    (hl : (encS l).length + 2 ≤ B) : NFits B (S.set i l) := by
  refine ⟨h.1, fun j => ?_⟩
  by_cases hj : j = i
  · subst j; simpa using hl
  · rw [Lists.set_ne _ _ hj]; exact h.2 j

theorem prim_to {B : Nat} {S S' : Lists 4} (p : NPrim 4)
    (he : p.apply S = S') (h : NFits B S) (h' : NFits B S') :
    NExec (NFits B) (.prim p) S 1 (.cont S') := by
  rw [← he] at h' ⊢
  exact .prim h h'

theorem exec {B : Nat} (D E L : List Nat) (a b : Nat)
    (h : NFits B (st (D ++ [a]) (E ++ [b]) [a] (L ++ [b])))
    (hspace : 2 * max a b + 4 ≤ B) :
    ∃ t, t ≤ 4 * a + 7 ∧ NExec (NFits B) program
      (st (D ++ [a]) (E ++ [b]) [a] (L ++ [b])) t
      (.cont (st (D ++ [a]) (E ++ [b]) [min a b, b] L)) := by
  let S := st (D ++ [a]) (E ++ [b]) [a] (L ++ [b])
  let R := st (D ++ [a]) (E ++ [b]) (if a ≤ b then [0] else []) (L ++ [b-a])
  let M := st (D ++ [a]) (E ++ [b]) [min a b] (L ++ [b-a])
  let P := st (D ++ [a]) (E ++ [b]) [min a b] L
  let F := st (D ++ [a]) (E ++ [b]) [min a b, b] L
  obtain ⟨t, ht, he⟩ := NShrinkingCompare.exec (B := B) 2 3 (by decide) a b S L rfl rfl h
  have hr : NShrinkingCompare.result S 2 3 L a b = R := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;> simp [NShrinkingCompare.result, S, R, st, Lists.set]
  rw [hr] at he
  have hR : NFits B R := by
    have h₁ := NShrinkingCompare.fits_set h 2 (if a ≤ b then [0] else []) (by
      by_cases hab : a ≤ b <;> simp [st, hab, encS, encN])
    have h₂ := NShrinkingCompare.fits_set h₁ 3 (L ++ [b-a]) (by
      simp only [Lists.set, show (3 : Fin 4) ≠ 2 by decide, ↓reduceIte, st]
      simp only [show (3 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 1 by decide, ↓reduceIte]
      rw [length_encS_snoc, length_encS_snoc]; omega)
    change NFits B (NShrinkingCompare.result S 2 3 L a b) at h₂
    rwa [hr] at h₂
  have hmin : min a b ≤ max a b := Nat.le_trans (Nat.min_le_left _ _) (Nat.le_max_left _ _)
  have hb : b ≤ max a b := Nat.le_max_right _ _
  have hM : NFits B M := by
    have hm := fits_replace hR 2 [min a b] (by simp [encS, encN]; omega)
    have heq : R.set 2 [min a b] = M := by
      funext i
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi with rfl | rfl | rfl | rfl <;> simp [M, R, st, Lists.set]
    rwa [heq] at hm
  have hs : ∃ u, u ≤ 3 ∧ NExec (NFits B) select R u (.cont M) := by
    by_cases hab : a ≤ b
    · let Z := R.set 2 []
      have hZ : NFits B Z := fits_replace hR 2 [] (by simpa [encS] using hR.1)
      have hp : (NPrim.pop 2).apply R = Z := by simp [NPrim.apply, R, st, hab, Z]
      have hd : (NPrim.dup 0 2 (by decide)).apply Z = M := by
        funext i
        have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
        rcases hi with rfl | rfl | rfl | rfl <;> simp [NPrim.apply, Z, R, M, st, hab, Nat.min_eq_left hab, Lists.set]
      exact ⟨3, by omega, .iteF hR (by simp [R, st, hab, NTest.eval])
        (.seqC (prim_to _ hp hR hZ) (prim_to _ hd hZ hM))⟩
    · have hd : (NPrim.dup 1 2 (by decide)).apply R = M := by
        funext i
        have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
        rcases hi with rfl | rfl | rfl | rfl <;> simp [NPrim.apply, R, M, st, hab, Nat.min_eq_right (by omega : b ≤ a), Lists.set]
      exact ⟨2, by omega, .iteT hR (by simp [R, st, hab, NTest.eval]) (prim_to _ hd hR hM)⟩
  have hp : (NPrim.pop 3).apply M = P := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;> simp [NPrim.apply, M, P, st, Lists.set]
  have hP : NFits B P := by
    rw [← hp]; exact NShrinkingCompare.fits_pop hM 3
  have hd : (NPrim.dup 1 2 (by decide)).apply P = F := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;> simp [NPrim.apply, P, F, st, Lists.set]
  have hF : NFits B F := by
    have hf := fits_replace hP 2 [min a b, b] (by simp [encS, encN]; omega)
    have heq : P.set 2 [min a b, b] = F := by
      funext i
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi with rfl | rfl | rfl | rfl <;> simp [F, P, st, Lists.set]
    rwa [heq] at hf
  obtain ⟨u, hu, hs⟩ := hs
  exact ⟨t + (u + (1 + 1)), by omega, .seqC he (.seqC hs
    (.seqC (prim_to _ hp hM hP) (prim_to _ hd hP hF)))⟩

theorem compiled_runs {B : Nat} (D E L : List Nat) (a b : Nat)
    (h : NFits B (st (D ++ [a]) (E ++ [b]) [a] (L ++ [b])))
    (hspace : 2 * max a b + 4 ≤ B) :
    Runs (LenOK B) program.compile
      (encL (st (D ++ [a]) (E ++ [b]) [a] (L ++ [b])))
      (encL (st (D ++ [a]) (E ++ [b]) [min a b, b] L))
      ((4 * a + 7) * ncost B) := by
  obtain ⟨t, ht, he⟩ := exec D E L a b h hspace
  obtain ⟨t', ht', he'⟩ := nexec_compile (fun _ h => h) he
  exact ⟨t', Nat.le_trans ht' (Nat.mul_le_mul_right _ ht), he'⟩

end Shallot.MacroPeg.CBV.SequentialCaptureMin
