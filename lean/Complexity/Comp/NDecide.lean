import Complexity.ListTime
import Complexity.NStackIO
import Complexity.NSpace
import Complexity.Comp.Basic

/-!
# Stack machines that halt on every input decide languages

`tmDecidable_of_nprog`: if on every input the stack program halts with the right answer, the language is decided by
a Turing machine. The time bound needed by `lm_time` is the largest halting time over the (finitely many) inputs
of each length (`maxOver`); the space bound follows from the time (`nexec_space`).
-/

namespace Complexity

/-- All bit strings of length `n`. -/
def allW : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allW n).flatMap fun w => [false :: w, true :: w]

theorem mem_allW : ∀ w : List Bool, w ∈ allW w.length
  | [] => by simp [allW]
  | b :: w => by
    simp only [List.length_cons, allW, List.mem_flatMap]
    exact ⟨w, mem_allW w, by cases b <;> simp⟩

/-- The largest value of `f` on the strings of length `n`. -/
def maxOver (f : List Bool → Nat) (n : Nat) : Nat := ((allW n).map f).foldr max 0

theorem le_foldr_max : ∀ {l : List Nat} {x : Nat}, x ∈ l → x ≤ l.foldr max 0
  | a :: l, x, h => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (le_foldr_max h) (Nat.le_max_right _ _)

theorem le_maxOver (f : List Bool → Nat) (w : List Bool) : f w ≤ maxOver f w.length :=
  le_foldr_max (List.mem_map_of_mem (mem_allW w))

/-- **A stack program that halts on every input with the answer decides the language.** -/
theorem tmDecidable_of_nprog {K : Nat} (hK : 1 < K) (p : NProg K) (L : Lang)
    (h : ∀ w, ∃ t b S', NExec (fun _ => True) p (nInit K w) t (.stop b S') ∧ (b = true ↔ L w)) :
    TMDecidable L := by
  let tw : List Bool → Nat := fun w => Classical.choose (h w)
  have htw : ∀ w, ∃ b S', NExec (fun _ => True) p (nInit K w) (tw w) (.stop b S') ∧ (b = true ↔ L w) :=
    fun w => Classical.choose_spec (h w)
  let T : Nat → Nat := maxOver tw
  let B : Nat → Nat := fun n => 2 * n + T n * (1 + T n + 1) + 2
  let B' : Nat → Nat := fun n => B n + (2 * n + 2)
  let T' : Nat → Nat := fun n => (n + 1) * 5 + T n * ncost (B' n)
  have hrun : ∀ w, ∃ t b L', t ≤ T' w.length ∧
      LExec (LenOK (B' w.length)) (.seq (importP hK) p.compile) (initLists (K + 1) w) t (.stop b L') ∧
      (b = true ↔ L w) := by
    intro w
    obtain ⟨b, S', hx, hb⟩ := htw w
    have ht : tw w ≤ T w.length := le_maxOver tw w
    have hx₁ : NExec (NFits (B w.length)) p (nInit K w) (tw w) (.stop b S') :=
      (nexec_space hx 1 (2 * w.length) (bnd_nInit w)).2 _ (by
        have : grow 1 (tw w) ≤ T w.length * (1 + T w.length + 1) := Nat.mul_le_mul ht (by omega)
        simp only [B]; omega)
    obtain ⟨t', ht', hx'⟩ := nprog_lexec hK p w (B := B' w.length) (by simp only [B']; omega)
      (hx₁.mono (fun _ hS => hS.mono (by simp only [B']; omega)))
    refine ⟨t', b, _, ?_, hx', hb⟩
    have : tw w * ncost (B' w.length) ≤ T w.length * ncost (B' w.length) := Nat.mul_le_mul_right _ ht
    simp only [T']; omega
  obtain ⟨M, hdec, _⟩ := lm_time (k := K + 1) (by omega) (.seq (importP hK) p.compile) 3 (by decide)
    (nprog_constOK hK p) L B' T' hrun
  exact ⟨K + 1, M, hdec⟩

end Complexity
