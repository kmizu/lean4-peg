import MacroPeg.HigherOrder.Mach.EvalStacks
import MacroPeg.HigherOrder.Mach.DecideT
import Complexity.NStackIO

/-!
# The cap from the input

`capP`: count the bits of the input (stack `0`), moving them to a scratch stack and back, and put
`capOf w = 3 · |w| + 2` on `CAP` (`capP_runs`).
-/

namespace Shallot.MacroPeg.Mach

open Complexity

abbrev CB : Fin NK := 18

/-- Count the bits three times each, starting from `2`. -/
def capP : NProg NK :=
  .seq (npushC CAP 2)
    (.seq (.loop 0 .nonempty (.seq (nmv 0 CB (by decide))
        (.seq (.prim (.inc CAP)) (.seq (.prim (.inc CAP)) (.prim (.inc CAP))))))
      (nmvAll CB 0 (by decide)))

theorem nInit_zero (w : List Bool) : nInit NK w 0 = (w.map bitElem).reverse := by simp [nInit]
theorem nInit_other (w : List Bool) (i : Fin NK) (h : i.val ≠ 0) : nInit NK w i = [] := by simp [nInit, h]

/-- **The cap on its stack.** -/
theorem capP_runs (w : List Bool) :
    NRuns capP (nInit NK w) ((nInit NK w).set CAP [capOf w]) (20 * (w.length + 1)) := by
  let S := nInit NK w
  let B := (w.map bitElem).reverse
  have hS0 : S 0 = B := nInit_zero w
  have hSC : S CAP = [] := nInit_other w CAP (by decide)
  have hSB : S CB = [] := nInit_other w CB (by decide)
  have n₁ : (0 : Fin NK) ≠ CAP := by decide
  have n₂ : (0 : Fin NK) ≠ CB := by decide
  have n₃ : (CB : Fin NK) ≠ CAP := by decide
  have n₄ : (CAP : Fin NK) ≠ CB := by decide
  have n₅ : (CAP : Fin NK) ≠ 0 := by decide
  have n₆ : (CB : Fin NK) ≠ 0 := by decide
  have x₁ := nruns_pushC CAP S 2
  rw [hSC, List.nil_append] at x₁
  -- after moving `m` bits
  let F : Nat → Lists NK := fun m =>
    ((S.set 0 (B.take (B.length - m))).set CB (B.drop (B.length - m)).reverse).set CAP [2 + 3 * m]
  have hF0 : F 0 = S.set CAP [2] := by
    simp only [F, Nat.sub_zero, List.take_length, List.drop_length, List.reverse_nil, Nat.mul_zero, Nat.add_zero]
    rw [← hS0, ← hSB, Lists.set_get_self, Lists.set_get_self]
  have hF0' : ∀ m, F m 0 = B.take (B.length - m) := fun m => by simp only [F]; simp [Lists.set, n₁, n₂]
  have hFB : ∀ m, F m CB = (B.drop (B.length - m)).reverse := fun m => by simp only [F]; simp [Lists.set, n₃]
  have hFC : ∀ m, F m CAP = [2 + 3 * m] := fun m => by simp only [F]; simp [Lists.set]
  have hl := nruns_family_const (i := 0) (c := .nonempty)
    (p := .seq (nmv 0 CB (by decide)) (.seq (.prim (.inc CAP)) (.seq (.prim (.inc CAP)) (.prim (.inc CAP)))))
    F B.length 5
    (fun m hm => by rw [hF0']; exact eval_nonempty_ne (List.ne_nil_of_length_pos (by simp; omega)))
    (by rw [hF0', Nat.sub_self]; rfl)
    (fun m hm => by
      obtain ⟨r, hr⟩ : ∃ r, B.length - m = r + 1 := ⟨B.length - m - 1, by omega⟩
      have hrl : r < B.length := by omega
      have htake : B.take (r + 1) = B.take r ++ [B[r]] := List.take_succ_eq_append_getElem hrl
      have d₁ := nruns_mv 0 CB (by decide) (F m) (l := B.take r) (v := B[r]) (by rw [hF0', hr, htake])
      have hdrop : B.drop r = B[r] :: B.drop (r + 1) := List.drop_eq_getElem_cons hrl
      let G := ((F m).set CB ((F m) CB ++ [B[r]])).set 0 (B.take r)
      have hGC : G CAP = [] ++ [2 + 3 * m] := by simp only [G]; simp [Lists.set, hFC, n₄, n₅]
      have i₁ := nruns_inc CAP G hGC
      have i₂ := nruns_inc CAP (G.set CAP ([] ++ [2 + 3 * m + 1])) (l := []) (v := 2 + 3 * m + 1) (by simp)
      rw [Lists.set_set_u] at i₂
      have i₃ := nruns_inc CAP (G.set CAP ([] ++ [2 + 3 * m + 1 + 1])) (l := []) (v := 2 + 3 * m + 1 + 1)
        (by simp)
      rw [Lists.set_set_u] at i₃
      have e : G.set CAP ([] ++ [2 + 3 * m + 1 + 1 + 1]) = F (m + 1) := by
        have hm1 : B.length - (m + 1) = r := by omega
        simp only [G, F, hm1, hFB, hr, hdrop, List.reverse_cons]
        funext y
        by_cases h1 : y = CAP
        · subst h1; simp [Lists.set, n₄, n₅]; omega
        · by_cases h2 : y = 0
          · subst h2; simp [Lists.set, h1, n₁, n₂]
          · by_cases h3 : y = CB
            · subst h3; simp [Lists.set, h1, h2, n₃, n₆]
            · simp [Lists.set, h1, h2, h3]
      rw [e] at i₃
      exact (d₁.seq (i₁.seq (i₂.seq i₃))).mono (by omega))
  rw [hF0] at hl
  have x₃ := nruns_mvAll CB 0 (by decide) (F B.length)
  have hfin : ((F B.length).set 0 ((F B.length) 0 ++ ((F B.length) CB).reverse)).set CB [] =
      S.set CAP [capOf w] := by
    rw [hF0', hFB, Nat.sub_self]
    simp only [List.take_zero, List.drop_zero, List.reverse_reverse, List.nil_append, F, Nat.sub_self]
    funext y
    by_cases h1 : y = CB
    · subst h1; simp [Lists.set, hSB, n₃, n₆]
    · by_cases h2 : y = 0
      · subst h2; simp [Lists.set, h1, hS0, n₁, n₂]
      · by_cases h3 : y = CAP
        · subst h3; simp [Lists.set, capOf, B, n₄, n₅]; omega
        · simp [Lists.set, h1, h2, h3]
  rw [hfin] at x₃
  refine (x₁.seq (hl.seq x₃)).mono ?_
  have hB : B.length = w.length := by simp [B]
  have hl3 : ((F B.length) CB).length = w.length := by rw [hFB, Nat.sub_self]; simp [B]
  rw [hl3, hB]
  omega

end Shallot.MacroPeg.Mach
