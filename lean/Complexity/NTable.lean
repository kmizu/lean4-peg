import Complexity.NArith

/-!
# Tables on stacks of numbers

A stack holds a table with entry `0` at the bottom.

* `moveN c i j`: pop the top `n` of `c` and move `n` numbers from `i` to `j`;
* `peekAt i T c o`: pop the top `k` of `c` and push entry `k` of `i` on `o` (`T` is scratch, empty before and
  after).
-/

namespace Complexity

variable {K : Nat}

/-! ## Counted moves -/

def moveN (c i j : Fin K) (hij : i ≠ j) : NProg K :=
  .seq (.loop c .pos (.seq (.prim (.dec c)) (nmv i j hij))) (.prim (.pop c))

theorem nruns_moveN (c i j : Fin K) (hij : i ≠ j) (hci : c ≠ i) (hcj : c ≠ j) (S : Lists K) {lc : List Nat}
    {n : Nat} (hc : S c = lc ++ [n]) {l seg : List Nat} (hi : S i = l ++ seg) (hseg : seg.length = n) :
    NRuns (moveN c i j hij) S (((S.set c lc).set i l).set j (S j ++ seg.reverse)) (4 * n + 2) := by
  let F : Nat → Lists K := fun m =>
    ((S.set c (lc ++ [n - m])).set i (l ++ seg.take (n - m))).set j (S j ++ (seg.drop (n - m)).reverse)
  have h0 : F 0 = S := by
    simp only [F, Nat.sub_zero, ← hseg, List.take_length, List.drop_length, List.reverse_nil, List.append_nil]
    rw [hseg, ← hc, ← hi]; lists_eq
  have hFc : ∀ m, F m c = lc ++ [n - m] := fun m => by simp only [F]; lists_at
  have hFi : ∀ m, F m i = l ++ seg.take (n - m) := fun m => by simp only [F]; lists_at
  have hFj : ∀ m, F m j = S j ++ (seg.drop (n - m)).reverse := fun m => by simp only [F]; lists_at
  have hl := nruns_family_const (i := c) (c := .pos) (p := .seq (.prim (.dec c)) (nmv i j hij)) F n 3
    (fun m hm => by rw [hFc, show n - m = (n - m - 1) + 1 by omega]; simp)
    (by rw [hFc, Nat.sub_self]; simp)
    (fun m hm => by
      obtain ⟨r, hr⟩ : ∃ r, n - m = r + 1 := ⟨n - m - 1, by omega⟩
      have hrl : r < seg.length := by omega
      have d₁ := nruns_dec c (F m) (hFc m)
      have ht : seg.take (r + 1) = seg.take r ++ [seg[r]] := List.take_succ_eq_append_getElem hrl
      have d₂ := nruns_mv i j hij ((F m).set c (lc ++ [n - m - 1])) (l := l ++ seg.take r) (v := seg[r])
        (by rw [Lists.set_ne _ _ (Ne.symm hci), hFi, hr, ht, List.append_assoc])
      have hd : seg.drop r = seg[r] :: seg.drop (r + 1) := List.drop_eq_getElem_cons hrl
      have e : ((((F m).set c (lc ++ [n - m - 1])).set j (((F m).set c (lc ++ [n - m - 1])) j ++ [seg[r]])).set i
          (l ++ seg.take r)) = F (m + 1) := by
        have hm1 : n - (m + 1) = r := by omega
        have hj' : ((F m).set c (lc ++ [n - m - 1])) j = S j ++ (seg.drop (r + 1)).reverse := by
          rw [Lists.set_ne _ _ (Ne.symm hcj), hFj, hr]
        rw [hj']
        simp only [F, hm1, hd, List.reverse_cons, List.append_assoc]
        rw [show n - m - 1 = r by omega]
        lists_eq
      rw [e] at d₂
      exact (d₁.seq d₂).mono (by omega))
  rw [h0] at hl
  have hp := nruns_pop c (F n) (l := lc) (v := 0) (by rw [hFc, Nat.sub_self])
  have e : (F n).set c lc = ((S.set c lc).set i l).set j (S j ++ seg.reverse) := by
    simp only [F, Nat.sub_self, List.take_zero, List.drop_zero, List.append_nil]; lists_eq
  rw [e] at hp
  exact (hl.seq hp).mono (by omega)

/-! ## Reading an entry -/

/-- Push entry `k` (the popped top of `c`) of the table `i` on `o`. -/
def peekAt (i T c o : Fin K) (hiT : i ≠ T) (hTo : T ≠ o) : NProg K :=
  .seq (nmvAll i T hiT) (.seq (moveN c T i (Ne.symm hiT)) (.seq (.prim (.dup T o hTo)) (nmvAll T i (Ne.symm hiT))))

theorem nruns_peekAt (i T c o : Fin K) (hiT : i ≠ T) (hTo : T ≠ o) (hd : [i, T, c, o].Nodup) (S : Lists K)
    (hT : S T = []) {lc : List Nat} {k : Nat} (hc : S c = lc ++ [k]) (hk : k < (S i).length) :
    NRuns (peekAt i T c o hiT hTo) S ((S.set c lc).set o (S o ++ [(S i)[k]]))
      (6 * (S i).length + 4 * k + 6) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd
  obtain ⟨⟨_, hic, hio⟩, ⟨hTc, _⟩, hco, _⟩ := hd
  let l := S i
  have x₁ := nruns_mvAll i T hiT S
  rw [hT, List.nil_append] at x₁
  let S₁ := (S.set T l.reverse).set i []
  have hsplit : l.reverse = (l.drop k).reverse ++ (l.take k).reverse := by
    rw [← List.reverse_append, List.take_append_drop]
  have x₂ := nruns_moveN c T i (Ne.symm hiT) (Ne.symm hTc) (Ne.symm hic) S₁ (lc := lc) (n := k)
    (by simp only [S₁]; lists_at)
    (l := (l.drop k).reverse) (seg := (l.take k).reverse)
    (by simp only [S₁]; rw [Lists.set_ne _ _ (Ne.symm hiT), Lists.set_same]; exact hsplit)
    (by simp only [List.length_reverse, List.length_take, l]; omega)
  have hS₁i : S₁ i = [] := by simp [S₁]
  rw [hS₁i, List.nil_append, List.reverse_reverse] at x₂
  let S₂ := ((S₁.set c lc).set T (l.drop k).reverse).set i (l.take k)
  have hd : l.drop k = l[k] :: l.drop (k + 1) := List.drop_eq_getElem_cons hk
  have hS₂T : S₂ T = (l.drop (k + 1)).reverse ++ [l[k]] := by
    simp only [S₂]; rw [Lists.set_ne _ _ (Ne.symm hiT), Lists.set_same, hd, List.reverse_cons]
  have x₃ := nruns_dup T o hTo S₂ hS₂T
  clear hd hsplit hS₂T
  have hi₂ : (S₂.set o (S₂ o ++ [l[k]])) i = l.take k := by simp only [S₂]; lists_at
  have hT₂ : (S₂.set o (S₂ o ++ [l[k]])) T = (l.drop k).reverse := by simp only [S₂]; lists_at
  have ho₂ : S₂ o = S o := by simp only [S₂, S₁]; lists_at
  have x₄ := nruns_mvAll T i (Ne.symm hiT) (S₂.set o (S₂ o ++ [l[k]]))
  rw [hi₂, hT₂, List.reverse_reverse, List.take_append_drop] at x₄
  have e : ((S₂.set o (S₂ o ++ [l[k]])).set i l).set T [] = (S.set c lc).set o (S o ++ [l[k]]) := by
    rw [ho₂]
    simp only [S₂, S₁]
    funext x
    simp only [Lists.set]
    repeat' split
    all_goals (try subst_vars)
    all_goals (try simp_all)
    all_goals (try rfl)
  rw [e] at x₄
  refine (x₁.seq (x₂.seq (x₃.seq x₄))).mono ?_
  simp only [List.length_reverse, List.length_drop]
  have : l.length = (S i).length := rfl
  omega

end Complexity
