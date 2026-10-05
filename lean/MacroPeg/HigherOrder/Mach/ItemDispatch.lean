import MacroPeg.HigherOrder.Mach.EvalSpec

/-!
# Dispatching on the tag of an item

`itemP`: copy the tag (the bottom of `IT`) to a scratch stack and branch on it (`caseTop`): leaves (`0`–`4`), the
parser operators (`5`–`8`), variables, rules, lambdas, applications; other tags leave the stack as it is. Given
programs for each kind, `itemP` does every item's step within `itemCost` plus `100` steps (`itemP_runs`).
-/

namespace Shallot.MacroPeg.Mach

open Complexity

abbrev DT : Fin NK := 18
abbrev DC : Fin NK := 19
abbrev DO : Fin NK := 20

/-- Dispatch on the tag. -/
def itemP (leafP seqP altP starP notP varP ruleP lamP appP : NProg NK) : NProg NK :=
  .seq (.seq (.prim (.pushZ DC)) (peekAt IT DT DC DO (by decide) (by decide)))
    (caseTop DO [leafP, leafP, leafP, leafP, leafP, seqP, altP, starP, notP, varP, ruleP, lamP, appP]
      (.prim (.pop DO)))

/-- Beyond the branches, the default runs with the top lowered by the number of branches. -/
theorem caseTop_default_runs {K : Nat} (i : Fin K) : ∀ (ps : List (NProg K)) (q : NProg K) (v : Nat) (S : Lists K)
    (l : List Nat), S i = l ++ [v + ps.length] → ∀ (S' : Lists K) (T : Nat),
      NRuns q (S.set i (l ++ [v])) S' T → NRuns (caseTop i ps q) S S' (T + 2 * ps.length)
  | [], q, v, S, l, hS, S', T, h => by
    simp only [List.length_nil, Nat.add_zero] at hS ⊢
    rw [← hS, Lists.set_get_self] at h; exact h
  | p :: ps, q, v, S, l, hS, S', T, h => by
    simp only [List.length_cons] at hS ⊢
    have hS' : S i = l ++ [(v + ps.length) + 1] := by rw [hS]; congr 2
    have h₁ := nruns_dec i S hS'
    simp only [Nat.add_sub_cancel] at h₁
    have h₂ := caseTop_default_runs i ps q v (S.set i (l ++ [v + ps.length])) l (by simp) S' T
      (by rw [Lists.set_set_u]; exact h)
    exact ((h₁.seq h₂).iteF (by rw [hS']; simp)).mono (by omega)

theorem stepT_other {j cap : Nat} {x : List Char} {tt ct : List (Nat × Nat)} {lt Tf : List (List Nat)} {it : MItem}
    (h : 13 ≤ it.tag) (vs : List (List Nat)) : stepT j cap x tt ct lt Tf it vs = vs := by
  have hop : opOf tt lt it = none := by
    unfold opOf; split <;> first | rfl | omega
  unfold stepT
  split <;> first | omega | (simp only [hop])

section

variable {leafP seqP altP starP notP varP ruleP lamP appP : NProg NK} {j cap : Nat} {st : PSt}
  {Tf : List (List Nat)} {it : MItem}

/-- After copying the tag: the stacks with the tag on `DO`. -/
theorem itemP_peek (S : Lists NK) (hE : EvalEnv S j cap st Tf) (hI : S IT = encItem it) :
    NRuns (.seq (.prim (.pushZ DC)) (peekAt IT DT DC DO (by decide) (by decide))) S (S.set DO [it.tag]) 32 := by
  have hs := hE.scratch
  have hDC : S DC = [] := hs DC (by decide) (by decide)
  have hDT : S DT = [] := hs DT (by decide) (by decide)
  have hDO : S DO = [] := hs DO (by decide) (by decide)
  have x₁ := nruns_pushZ DC S
  rw [hDC, List.nil_append] at x₁
  have x₂ := nruns_peekAt IT DT DC DO (by decide) (by decide) (by decide) (S.set DC [0])
    (by rw [Lists.set_ne _ _ (by decide)]; exact hDT) (lc := []) (k := 0) (by simp)
    (by rw [Lists.set_ne _ _ (by decide), hI]; simp [encItem])
  have e : ((S.set DC [0]).set DC []).set DO ((S.set DC [0]) DO ++ [((S.set DC [0]) IT)[0]'(by
      rw [Lists.set_ne _ _ (by decide), hI]; simp [encItem])]) = S.set DO [it.tag] := by
    have n₁ : (DO : Fin NK) ≠ DC := by decide
    have n₂ : (IT : Fin NK) ≠ DC := by decide
    have n₃ : (DC : Fin NK) ≠ DO := by decide
    funext y
    by_cases h1 : y = DO
    · subst h1; simp [Lists.set, hDO, hI, encItem, n₁, n₂]
    · by_cases h2 : y = DC
      · subst h2; simp [Lists.set, hDC, n₃]
      · simp [Lists.set, h1, h2]
  rw [e] at x₂
  refine (x₁.seq x₂).mono ?_
  rw [Lists.set_ne _ _ (by decide), hI]; simp [encItem]

/-- **Dispatching on the tag.** -/
theorem itemP_runs (hleaf : it.tag ≤ 4 → ItemRuns leafP j cap st Tf it)
    (h5 : it.tag = 5 → ItemRuns seqP j cap st Tf it) (h6 : it.tag = 6 → ItemRuns altP j cap st Tf it)
    (h7 : it.tag = 7 → ItemRuns starP j cap st Tf it) (h8 : it.tag = 8 → ItemRuns notP j cap st Tf it)
    (h9 : it.tag = 9 → ItemRuns varP j cap st Tf it) (h10 : it.tag = 10 → ItemRuns ruleP j cap st Tf it)
    (h11 : it.tag = 11 → ItemRuns lamP j cap st Tf it) (h12 : it.tag = 12 → ItemRuns appP j cap st Tf it) :
    ItemRunsC (itemP leafP seqP altP starP notP varP ruleP lamP appP) j cap st Tf it 100 := by
  intro S vs hE hI hV hL
  have x₁ := itemP_peek S hE hI
  have hDO : S DO = [] := hE.scratch DO (by decide) (by decide)
  have hback : (S.set DO [it.tag]).set DO [] = S := by rw [Lists.set_set_u, ← hDO, Lists.set_get_self]
  have hS1 : (S.set DO [it.tag]) DO = [] ++ [it.tag] := by simp
  let ps := [leafP, leafP, leafP, leafP, leafP, seqP, altP, starP, notP, varP, ruleP, lamP, appP]
  by_cases hlt : it.tag < 13
  · have hsub : ItemRuns ps[it.tag] j cap st Tf it := by
      match ht : it.tag, hlt with
      | 0, _ => exact hleaf (by omega)
      | 1, _ => exact hleaf (by omega)
      | 2, _ => exact hleaf (by omega)
      | 3, _ => exact hleaf (by omega)
      | 4, _ => exact hleaf (by omega)
      | 5, _ => exact h5 ht
      | 6, _ => exact h6 ht
      | 7, _ => exact h7 ht
      | 8, _ => exact h8 ht
      | 9, _ => exact h9 ht
      | 10, _ => exact h10 ht
      | 11, _ => exact h11 ht
      | 12, _ => exact h12 ht
    have x₂ := caseTop_runs DO ps (.prim (.pop DO)) it.tag (by simp [ps]; omega) _ [] hS1 _ _
      (by rw [hback]; exact hsub S vs hE hI hV hL)
    exact (x₁.seq x₂).mono (by omega)
  · have hs := stepT_other (j := j) (cap := cap) (x := st.x.map Char.ofNat) (tt := st.tt) (ct := st.ct)
      (lt := st.lt) (Tf := Tf) (by omega : 13 ≤ it.tag) vs
    rw [hs, ← hV, ← hL, Lists.set_get_self, Lists.set_get_self]
    have hS1' : (S.set DO [it.tag]) DO = [] ++ [(it.tag - 13) + ps.length] := by simp [ps]; omega
    have hpop := nruns_pop DO ((S.set DO [it.tag]).set DO ([] ++ [it.tag - 13])) (l := []) (v := it.tag - 13)
      (by simp)
    have hb2 : ((S.set DO [it.tag]).set DO ([] ++ [it.tag - 13])).set DO [] = S := by
      funext y; by_cases h : y = DO <;> simp [Lists.set, h, hDO]
    rw [hb2] at hpop
    have x₂ := caseTop_default_runs DO ps (.prim (.pop DO)) (it.tag - 13) _ [] hS1' _ _ hpop
    exact (x₁.seq x₂).mono (by simp [itemCost, ps])

end

end Shallot.MacroPeg.Mach
