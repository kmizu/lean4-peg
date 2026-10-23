import MacroPeg.CBV.Spans
import MacroPeg.HigherOrder.Mach.Intern

namespace Shallot.MacroPeg.CBV

open Complexity Shallot.MacroPeg.Mach

/-- The existing pair lookup uses the same first-index convention as CBV dictionaries. -/
theorem indexIn_idxOf (a : Nat × Nat) (xs : List (Nat × Nat)) : indexIn a xs = xs.idxOf a := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    by_cases he : b = a
    · subst b; simp [indexIn]
    · have hb : (b == a) = false := Bool.eq_false_iff.mpr (fun hb => he (eq_of_beq hb))
      simp [indexIn, List.idxOf_cons, he, hb, ih]

theorem spans_bound {n : Nat} : ∀ q ∈ spans n, q.1 ≤ n ∧ q.2 ≤ n := by
  intro q hq
  obtain ⟨p, hp, hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
  have := List.mem_range.mp hp
  have := List.mem_range.mp hj
  exact ⟨by dsimp; omega, by dsimp; omega⟩

section Machine
variable {K : Nat}

/-- Obtain an interval's existing zero-based identifier; the span dictionary is preserved. -/
def spanLookupP (tt ntt w sa sb d idx fnd t u zc f f2 z : Fin K)
    (htw : tt ≠ w) (htt : tt ≠ t) (hsa : sa ≠ u) (hsb : sb ≠ u) (hif : idx ≠ fnd)
    (hfd : fnd ≠ d) (hsat : sa ≠ tt) (hsbt : sb ≠ tt) (hnd : ntt ≠ d) : NProg K :=
  .seq (internP tt ntt w sa sb d idx fnd t u zc f f2 z htw htt hsa hsb hif hfd hsat hsbt hnd)
    (.prim (.dec d))

/-- The actual stack program looks up a span in polynomially bounded time. -/
theorem spanLookup_runs (tt ntt w sa sb d idx fnd t u zc f f2 z : Fin K)
    (htw : tt ≠ w) (htt : tt ≠ t) (hsa : sa ≠ u) (hsb : sb ≠ u) (hif : idx ≠ fnd)
    (hfd : fnd ≠ d) (hsat : sa ≠ tt) (hsbt : sb ≠ tt) (hnd : ntt ≠ d)
    (hd : InternStacks tt ntt w sa sb d idx fnd t u zc f f2 z) (S : Lists K)
    {n p j : Nat} {la lb : List Nat} (hp : p ≤ n) (hj : j ≤ p)
    (hP : S tt = encPairs (spans n)) (hw : S w = [])
    (ha : S sa = la ++ [p]) (hb : S sb = lb ++ [j]) (hn : S ntt = [(spans n).length]) :
    NRuns (spanLookupP tt ntt w sa sb d idx fnd t u zc f f2 z htw htt hsa hsb hif hfd hsat hsbt hnd)
      S (S.set d (S d ++ [spanId n p j])) (internCost (spans n).length n + 1) := by
  have hmem : (p, j) ∈ spans n := by simpa [Nat.min_eq_left hj] using (span_mem (j := j) hp)
  have hi := internP_runs tt ntt w sa sb d idx fnd t u zc f f2 z htw htt hsa hsb hif hfd hsat hsbt hnd hd S (ln := [])
    hP hw ha hb hn spans_bound hp (Nat.le_trans hj hp)
  have hid : indexIn (p, j) (spans n) = spanId n p j := by
    rw [indexIn_idxOf]
    simp [spanId, Nat.min_eq_left hj]
  simp only [intern, if_pos hmem, hid, List.nil_append] at hi
  have he : ((S.set tt (encPairs (spans n))).set ntt [(spans n).length]).set d
      (S d ++ [spanId n p j + 1]) = S.set d (S d ++ [spanId n p j + 1]) := by
    rw [← hP, Lists.set_get_self, ← hn, Lists.set_get_self]
  rw [he] at hi
  have hx := nruns_dec d (S.set d (S d ++ [spanId n p j + 1]))
    (l := S d) (v := spanId n p j + 1) (by simp)
  simp only [Nat.add_sub_cancel, Lists.set_set_u] at hx
  exact hi.seq hx
end Machine

end Shallot.MacroPeg.CBV
