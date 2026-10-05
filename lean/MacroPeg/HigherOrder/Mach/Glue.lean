import MacroPeg.HigherOrder.Mach.EvalStacks

/-!
# Small programs between the stages

`countP i o T`: put the length of stack `i` on `o`, moving `i` to the scratch stack `T` and back (`countP_runs`).
-/

namespace Shallot.MacroPeg.Mach

open Complexity

variable {K : Nat}

/-- Count stack `i` onto `o`. -/
def countP (i o T : Fin K) (hiT : i ≠ T) : NProg K :=
  .seq (.prim (.pushZ o)) (.seq (.loop i .nonempty (.seq (nmv i T hiT) (.prim (.inc o)))) (nmvAll T i (Ne.symm hiT)))

theorem countP_runs (i o T : Fin K) (hiT : i ≠ T) (hio : i ≠ o) (hoT : o ≠ T) (S : Lists K) (hO : S o = [])
    (hT : S T = []) : NRuns (countP i o T hiT) S (S.set o [(S i).length]) (8 * (S i).length + 4) := by
  have x₁ := nruns_pushZ o S
  rw [hO, List.nil_append] at x₁
  let l := S i
  let F : Nat → Lists K := fun m =>
    ((S.set o [m]).set i (l.take (l.length - m))).set T (l.drop (l.length - m)).reverse
  have hF0 : F 0 = S.set o [0] := by
    simp only [F, Nat.sub_zero, List.take_length, List.drop_length, List.reverse_nil]
    funext y
    by_cases h1 : y = T
    · subst h1; simp [Lists.set, Ne.symm hoT, hT]
    · by_cases h2 : y = i
      · subst h2; simp [Lists.set, h1, hio, l]
      · simp [Lists.set, h1, h2]
  have hFi : ∀ m, F m i = l.take (l.length - m) := fun m => by simp [F, Lists.set, hiT]
  have hFT : ∀ m, F m T = (l.drop (l.length - m)).reverse := fun m => by simp [F, Lists.set]
  have hFo : ∀ m, F m o = [m] := fun m => by simp [F, Lists.set, hoT, Ne.symm hio]
  have hl := nruns_family_const (i := i) (c := .nonempty) (p := .seq (nmv i T hiT) (.prim (.inc o))) F l.length 3
    (fun m hm => by rw [hFi]; exact eval_nonempty_ne (List.ne_nil_of_length_pos (by simp; omega)))
    (by rw [hFi, Nat.sub_self]; rfl)
    (fun m hm => by
      obtain ⟨r, hr⟩ : ∃ r, l.length - m = r + 1 := ⟨l.length - m - 1, by omega⟩
      have hrl : r < l.length := by omega
      have htake : l.take (r + 1) = l.take r ++ [l[r]] := List.take_succ_eq_append_getElem hrl
      have d₁ := nruns_mv i T hiT (F m) (l := l.take r) (v := l[r]) (by rw [hFi, hr, htake])
      have hdrop : l.drop r = l[r] :: l.drop (r + 1) := List.drop_eq_getElem_cons hrl
      let G := ((F m).set T ((F m) T ++ [l[r]])).set i (l.take r)
      have hGo : G o = [] ++ [m] := by simp [G, Lists.set, hFo, hoT, Ne.symm hio]
      have i₁ := nruns_inc o G hGo
      have e : G.set o ([] ++ [m + 1]) = F (m + 1) := by
        have hm1 : l.length - (m + 1) = r := by omega
        simp only [G, F, hm1, hFT, hr, hdrop, List.reverse_cons]
        funext y
        by_cases h1 : y = o
        · subst h1; simp [Lists.set, hoT, Ne.symm hio]
        · by_cases h2 : y = i
          · subst h2; simp [Lists.set, h1, hiT]
          · by_cases h3 : y = T
            · subst h3; simp [Lists.set, h1, h2]
            · simp [Lists.set, h1, h2, h3]
      rw [e] at i₁
      exact (d₁.seq i₁).mono (by omega))
  rw [hF0] at hl
  have x₃ := nruns_mvAll T i (Ne.symm hiT) (F l.length)
  have e : ((F l.length).set i ((F l.length) i ++ ((F l.length) T).reverse)).set T [] = S.set o [l.length] := by
    rw [hFi, hFT, Nat.sub_self]
    simp only [List.take_zero, List.drop_zero, List.reverse_reverse, List.nil_append, F, Nat.sub_self]
    funext y
    by_cases h1 : y = T
    · subst h1; simp [Lists.set, hT, Ne.symm hoT]
    · by_cases h2 : y = i
      · subst h2; simp [Lists.set, h1, hio, l]
      · simp [Lists.set, h1, h2]
  rw [e] at x₃
  refine (x₁.seq (hl.seq x₃)).mono ?_
  have : ((F l.length) T).length = l.length := by rw [hFT, Nat.sub_self]; simp
  have hlen : l.length = (S i).length := rfl
  rw [this, hlen]; omega

end Shallot.MacroPeg.Mach
