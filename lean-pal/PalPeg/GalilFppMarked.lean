import PalPeg.GalilFppChain

set_option autoImplicit false
namespace PalPeg.GalilFppMarked
open GalilFppChain GalilFppDelta

/-- The A/B word built by FppSubroutine.buildMarkedProgram("abs"). -/
def prepared (w : List (Fin 4)) : List (Fin 4) := w ++ [3] ++ w.reverse

theorem prepared_length (w : List (Fin 4)) : (prepared w).length = 2*w.length+1 := by
  simp [prepared]; omega

/-- Within the source range, a border of the prepared word is precisely
a palindromic source prefix. This is the meaning of each MARKS cell. -/
theorem prepared_border (w : List (Fin 4)) (b : ℕ) (hb : b ≤ w.length) :
    IsBorder (prepared w) b ↔ (w.take b).reverse = w.take b := by
  have htake : (prepared w).take b = w.take b := by
    simp only [prepared, List.append_assoc]
    exact List.take_append_of_le_length hb
  have hdrop : (prepared w).drop ((prepared w).length-b) = (w.take b).reverse := by
    rw [prepared_length]
    have he : 2*w.length+1-b = (w ++ [3]).length+(w.length-b) := by simp; omega
    rw [he]
    change ((w ++ [3]) ++ w.reverse).drop ((w ++ [3]).length+(w.length-b)) = _
    rw [← List.drop_drop, List.drop_append_length, List.drop_reverse, Nat.sub_sub_self hb]
  unfold IsBorder
  rw [htake, hdrop]
  have hlen : b ≤ (prepared w).length := by rw [prepared_length]; omega
  simp only [hlen, true_and, eq_comm]

theorem separator_unique (w : List (Fin 4)) (hsep : (3 : Fin 4) ∉ w) (i : ℕ) :
    (prepared w)[i]? = some 3 ↔ i = w.length := by
  have hrev : (3 : Fin 4) ∉ w.reverse := by simpa using hsep
  unfold prepared
  rw [List.append_assoc, List.getElem?_append]
  by_cases hi : i < w.length
  · rw [if_pos hi]
    constructor
    · intro h; exact (hsep (List.mem_of_getElem? h)).elim
    · intro h; omega
  · rw [if_neg hi]
    by_cases he : i = w.length
    · subst i; simp
    · have hd : i-w.length = (i-w.length-1)+1 := by omega
      rw [hd]
      simp only [List.singleton_append, List.getElem?_cons_succ]
      constructor
      · intro h; exact (hrev (List.mem_of_getElem? h)).elim
      · exact fun h => (he h).elim

/-- The private separator excludes every oversized proper border; hence
the transformed kernel never marks beyond the source-length range. -/
theorem proper_border_bound (w : List (Fin 4)) (hsep : (3 : Fin 4) ∉ w)
    (b : ℕ) (hb : b < (prepared w).length) (hborder : IsBorder (prepared w) b) :
    b ≤ w.length := by
  by_contra hn
  have hn' : w.length < b := by omega
  have he := congrArg (fun l : List (Fin 4) => l[w.length]?) hborder.2
  rw [List.getElem?_take_of_lt hn', List.getElem?_drop] at he
  have hs := (separator_unique w hsep w.length).mpr rfl
  rw [hs] at he
  have hi := (separator_unique w hsep ((prepared w).length-b+w.length)).mp he.symm
  omega

/-- The proved seven-tape kernel, on the actual prepared word, emits a
source-range length iff that source prefix is palindromic. The nine-tape
preparation and emit-to-mark instruction transformation are still separate. -/
theorem prepared_kernel (w : List (Fin 4)) :
    ∃ y qs, GalilFppInstruction.Completed GalilFppCode.code
      (GalilFppGeneration.initial (prepared w)) qs y ∧
      ∀ b, b ≤ w.length → (b ∈ y.output ↔ 0 < b ∧ (w.take b).reverse = w.take b) := by
  obtain ⟨y, qs, hs, hout, _, _⟩ := initial_completed (prepared w)
  refine ⟨y, qs, hs, ?_⟩
  intro b hb
  rw [hout, mem_initial_output, prepared_border w b hb]
  have hlt : b < (prepared w).length := by rw [prepared_length]; omega
  simp only [hlt, true_and]

/-- With Scala's fresh separator, the entire emitted set is exactly the
positive palindromic prefix lengths, including exclusion of oversized marks. -/
theorem prepared_kernel_exact (w : List (Fin 4)) (hsep : (3 : Fin 4) ∉ w) :
    ∃ y qs, GalilFppInstruction.Completed GalilFppCode.code
      (GalilFppGeneration.initial (prepared w)) qs y ∧
      y.pos 0 = 0 ∧ y.pc = 0 ∧
      ∀ b, b ∈ y.output ↔ 0 < b ∧ b ≤ w.length ∧ (w.take b).reverse = w.take b := by
  obtain ⟨y, qs, hs, hout, hpos, hpc⟩ := initial_completed (prepared w)
  refine ⟨y, qs, hs, hpos, hpc, ?_⟩
  intro b
  rw [hout, mem_initial_output]
  constructor
  · rintro ⟨hb, hbl, hborder⟩
    have hbound := proper_border_bound w hsep b hbl hborder
    exact ⟨hb, hbound, (prepared_border w b hbound).mp hborder⟩
  · rintro ⟨hb, hbound, hpal⟩
    refine ⟨hb, ?_, (prepared_border w b hbound).mpr hpal⟩
    rw [prepared_length]; omega

#print axioms prepared_kernel_exact
#print axioms proper_border_bound
#print axioms prepared_kernel
end PalPeg.GalilFppMarked
