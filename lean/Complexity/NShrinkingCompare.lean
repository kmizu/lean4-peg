import Complexity.NMacros

/-! Destructive comparison with no increase in intermediate unary stack space.
The first operand occupies a dedicated stack; the second may have a saved prefix. -/
namespace Complexity.NShrinkingCompare
open Complexity
variable {K B : Nat}

theorem fits_set {S : Lists K} (h : NFits B S) (i : Fin K) (l : List Nat)
    (hl : (encS l).length ≤ (encS (S i)).length) : NFits B (S.set i l) := by
  refine ⟨h.1, fun j => ?_⟩
  by_cases hj : j = i
  · subst j; rw [Lists.set_same]; have := h.2 i; omega
  · rw [Lists.set_ne _ _ hj]; exact h.2 j

theorem fits_dec {S : Lists K} (h : NFits B S) (i : Fin K) :
    NFits B ((NPrim.dec i).apply S) := by
  apply fits_set h
  rcases List.eq_nil_or_concat (S i) with he | ⟨l, v, he⟩
  · simp [he, mapTop]
  · rw [he, List.concat_eq_append, mapTop_snoc, length_encS_snoc, length_encS_snoc]
    omega

theorem fits_pop {S : Lists K} (h : NFits B S) (i : Fin K) :
    NFits B ((NPrim.pop i).apply S) := fits_set h i _ (length_encS_dropLast_le _)

/-- Dispatch a bounded tag while preserving the same intermediate space bound. -/
theorem caseTop_exec (i : Fin K) : ∀ (ps : List (NProg K)) (q : NProg K) (v : Nat)
    (hv : v < ps.length) (S : Lists K) (l : List Nat), S i = l ++ [v] → NFits B S →
    ∀ (S' : Lists K) (T : Nat),
    (∃ t, t ≤ T ∧ NExec (NFits B) ps[v] (S.set i l) t (.cont S')) →
    ∃ t, t ≤ T + 2 * v + 2 ∧ NExec (NFits B) (caseTop i ps q) S t (.cont S')
  | [], _, v, hv, _, _, _, _, _, _, _ => by simp at hv
  | p :: ps, q, 0, _, S, l, hi, hS, S', T, hr => by
    obtain ⟨t, ht, he⟩ := hr
    have hp : (NPrim.pop i).apply S = S.set i l := by simp [NPrim.apply,hi]
    have hx : NExec (NFits B) (.prim (.pop i)) S 1 (.cont (S.set i l)) := by
      rw [← hp]; exact .prim hS (fits_pop hS i)
    exact ⟨1+t+1, by omega, .iteT hS (by simp [hi,NTest.eval]) (.seqC hx he)⟩
  | p :: ps, q, v+1, hv, S, l, hi, hS, S', T, hr => by
    let R := S.set i (l ++ [v])
    have hd : (NPrim.dec i).apply S = R := by simp [NPrim.apply,hi,mapTop_snoc,R]
    have hR : NFits B R := by rw [← hd]; exact fits_dec hS i
    have hx : NExec (NFits B) (.prim (.dec i)) S 1 (.cont R) := by
      rw [← hd]; exact .prim hS (fits_dec hS i)
    obtain ⟨t, ht, he⟩ := caseTop_exec i ps q v (by simpa using hv) R l (by simp [R]) hR S' T (by
      simpa [R,Lists.set_set_u] using hr)
    exact ⟨1+t+1, by omega, .iteF hS (by simp [hi,NTest.eval]) (.seqC hx he)⟩

def body (i j : Fin K) : NProg K :=
  .ite j .pos (.seq (.prim (.dec i)) (.prim (.dec j))) (.prim (.pop i))
def program (i j : Fin K) : NProg K := .loop i .pos (body i j)
def result (S : Lists K) (i j : Fin K) (l : List Nat) (a b : Nat) : Lists K :=
  (S.set i (if a ≤ b then [0] else [])).set j (l ++ [b - a])

theorem exec (i j : Fin K) (hij : i ≠ j) (a b : Nat) (S : Lists K) (l : List Nat)
    (hi : S i = [a]) (hj : S j = l ++ [b]) (hS : NFits B S) :
    ∃ t, t ≤ 4 * a + 1 ∧ NExec (NFits B) (program i j) S t (.cont (result S i j l a b)) := by
  induction a generalizing b S with
  | zero =>
    have hr : result S i j l 0 b = S := by
      funext x
      by_cases hx : x = i
      · subst x; simp [result, Lists.set, hij, hi]
      · by_cases hy : x = j
        · subst x; simp [result, Lists.set, hj]
        · simp [result, Lists.set, hx, hy]
    rw [hr]
    exact ⟨1, by omega, .loopF hS (by simp [NTest.eval, hi])⟩
  | succ a ih =>
    cases b with
    | zero =>
      let S' := (NPrim.pop i).apply S
      have hS' : NFits B S' := fits_pop hS i
      have hi' : S' i = [] := by simp [S', NPrim.apply, hi]
      have hr : result S i j l (a + 1) 0 = S' := by
        funext x
        by_cases hx : x = i
        · subst x; simp [result, S', NPrim.apply, Lists.set, hij, hi]
        · by_cases hy : x = j
          · subst x; simp [result, S', NPrim.apply, Lists.set, Ne.symm hij, hj]
          · simp [result, S', NPrim.apply, Lists.set, hx, hy]
      rw [hr]
      refine ⟨4, by omega, .loopC hS (by simp [NTest.eval, hi]) ?_ (.loopF hS' ?_)⟩
      · exact .iteF hS (by simp [NTest.eval, hj]) (.prim hS hS')
      · simp [NTest.eval, hi']
    | succ b =>
      let S₁ := (NPrim.dec i).apply S
      let S₂ := (NPrim.dec j).apply S₁
      have h₁ : NFits B S₁ := fits_dec hS i
      have h₂ : NFits B S₂ := fits_dec h₁ j
      have hi₂ : S₂ i = [a] := by
        simp [S₂, S₁, NPrim.apply, Lists.set, hij, hi, mapTop]
      have hj₂ : S₂ j = l ++ [b] := by
        simp [S₂, S₁, NPrim.apply, Lists.set, Ne.symm hij, hj, mapTop_snoc]
      obtain ⟨t, ht, he⟩ := ih b S₂ hi₂ hj₂ h₂
      have hr : result S₂ i j l a b = result S i j l (a + 1) (b + 1) := by
        funext x
        by_cases hx : x = i
        · subst x; simp [result, Lists.set, hij]
        · by_cases hy : x = j
          · subst x; simp [result, Lists.set]
          · simp [result, S₂, S₁, NPrim.apply, Lists.set, hx, hy]
      rw [hr] at he
      refine ⟨3 + 1 + t, by omega, .loopC hS (by simp [NTest.eval, hi]) ?_ he⟩
      exact .iteT hS (by simp [NTest.eval, hj]) (.seqC (.prim hS h₁) (.prim h₁ h₂))

theorem empty_iff (S : Lists K) (i j : Fin K) (hij : i ≠ j) (l : List Nat) (a b : Nat) :
    NTest.empty.eval (result S i j l a b i) = decide (b < a) := by
  by_cases h : a ≤ b <;> simp [result, Lists.set, hij, h, NTest.eval] <;> omega

theorem positive_iff (S : Lists K) (i j : Fin K) (l : List Nat) (a b : Nat) :
    NTest.pos.eval (result S i j l a b j) = decide (a < b) := by
  simp only [result, Lists.set_same, NTest.eval, List.getLast?_concat]
  cases h : b - a with
  | zero =>
    have hn : ¬ a < b := by omega
    simp [hn]
  | succ n =>
    have hn : a < b := by omega
    simp [hn]

theorem compiled_runs (i j : Fin K) (hij : i ≠ j) (a b : Nat) (S : Lists K) (l : List Nat)
    (hi : S i = [a]) (hj : S j = l ++ [b]) (hS : NFits B S) :
    Runs (LenOK B) (program i j).compile (encL S)
      (encL (result S i j l a b)) ((4 * a + 1) * ncost B) := by
  obtain ⟨t, ht, he⟩ := exec i j hij a b S l hi hj hS
  obtain ⟨t', ht', he'⟩ := nexec_compile (fun _ h => h) he
  exact ⟨t', Nat.le_trans ht' (Nat.mul_le_mul_right _ ht), he'⟩
end Complexity.NShrinkingCompare
