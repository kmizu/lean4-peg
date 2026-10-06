import MacroPeg.HigherOrder.KExp.DiagArith

/-!
# Counting in chunks

`chunkLoop s o c r` moves stack `s` onto `o` (reversing it) while a counter on `c` runs down from the top `R` of
`r` and restarts: after `m` numbers the counter is `ccR R m`, which is `0` exactly when `R + 1` divides `m`
(`ccR_zero_iff`).
-/

namespace Shallot.MacroPeg.KExp

open Complexity

variable {K : Nat}

/-- The counter after `m` numbers. -/
def ccR (R : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => if ccR R m = 0 then R else ccR R m - 1

theorem ccR_inv (R : Nat) : ∀ m, ccR R m ≤ R ∧ (m + ccR R m) % (R + 1) = 0
  | 0 => by simp [ccR]
  | m + 1 => by
    obtain ⟨h₁, h₂⟩ := ccR_inv R m
    simp only [ccR]
    by_cases h : ccR R m = 0
    · rw [if_pos h]
      refine ⟨Nat.le_refl _, ?_⟩
      rw [h, Nat.add_zero] at h₂
      rw [show m + 1 + R = m + (R + 1) by omega, Nat.add_mod_right]; exact h₂
    · rw [if_neg h]
      refine ⟨by omega, ?_⟩
      rw [show m + 1 + (ccR R m - 1) = m + ccR R m by omega]; exact h₂

theorem ccR_zero_iff (R m : Nat) : ccR R m = 0 ↔ m % (R + 1) = 0 := by
  obtain ⟨h₁, h₂⟩ := ccR_inv R m
  constructor
  · intro h; rw [h, Nat.add_zero] at h₂; exact h₂
  · intro h
    rcases Nat.eq_zero_or_pos (ccR R m) with h0 | hp
    · exact h0
    · exfalso
      have : (m + ccR R m) % (R + 1) = (m % (R + 1) + ccR R m % (R + 1)) % (R + 1) := Nat.add_mod _ _ _
      rw [h, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (show ccR R m < R + 1 by omega)] at this
      omega

def chunkBody (s o c r : Fin K) (hso : s ≠ o) (hrc : r ≠ c) : NProg K :=
  .seq (.ite c .zero (.seq (.prim (.pop c)) (.prim (.dup r c hrc))) (.prim (.dec c))) (nmv s o hso)

def chunkLoop (s o c r : Fin K) (hso : s ≠ o) (hrc : r ≠ c) : NProg K := .loop s .nonempty (chunkBody s o c r hso hrc)

theorem nruns_chunkLoop (s o c r : Fin K) (hso : s ≠ o) (hrc : r ≠ c) (hsc : s ≠ c) (hsr : s ≠ r) (hoc : o ≠ c)
    (hor : o ≠ r) (S : Lists K) {l lc lr : List Nat} {R : Nat} (hs : S s = l) (ho : S o = [])
    (hc : S c = lc ++ [0]) (hr : S r = lr ++ [R]) :
    NRuns (chunkLoop s o c r hso hrc) S (((S.set s []).set o l.reverse).set c (lc ++ [ccR R l.length]))
      (6 * l.length + 1) := by
  let L := l.length
  let F : Nat → Lists K := fun m => ((S.set s (l.take (L - m))).set o (l.drop (L - m)).reverse).set c
    (lc ++ [ccR R m])
  have hFs : ∀ m, F m s = l.take (L - m) := fun m => by
    simp only [F]; rw [Lists.set_ne _ _ hsc, Lists.set_ne _ _ hso, Lists.set_same]
  have hFo : ∀ m, F m o = (l.drop (L - m)).reverse := fun m => by
    simp only [F]; rw [Lists.set_ne _ _ hoc, Lists.set_same]
  have hFc : ∀ m, F m c = lc ++ [ccR R m] := fun m => by simp only [F, Lists.set_same]
  have hFr : ∀ m, F m r = lr ++ [R] := fun m => by
    simp only [F]; rw [Lists.set_ne _ _ hrc, Lists.set_ne _ _ (Ne.symm hor), Lists.set_ne _ _ (Ne.symm hsr), hr]
  have h0 : F 0 = S := by
    funext q
    by_cases q1 : q = c
    · rw [q1, hFc, hc]; rfl
    · by_cases q2 : q = o
      · rw [q2, hFo, ho]; simp [L]
      · by_cases q3 : q = s
        · rw [q3, hFs, hs]; simp [L]
        · simp only [F]; rw [Lists.set_ne _ _ q1, Lists.set_ne _ _ q2, Lists.set_ne _ _ q3]
  have hl := nruns_family_const (i := s) (c := .nonempty) (p := chunkBody s o c r hso hrc) F L 5
    (fun m hm => by rw [hFs]; exact eval_nonempty_ne (List.ne_nil_of_length_pos (by simp [L]; omega)))
    (by rw [hFs, Nat.sub_self]; rfl)
    (fun m hm => by
      obtain ⟨u, hu⟩ : ∃ u, L - m = u + 1 := ⟨L - m - 1, by omega⟩
      have hul : u < l.length := by omega
      -- the counter
      have hcnt : NRuns (.ite c .zero (.seq (.prim (.pop c)) (.prim (.dup r c hrc))) (.prim (.dec c))) (F m)
          ((F m).set c (lc ++ [ccR R (m + 1)])) 3 := by
        by_cases h : ccR R m = 0
        · have e₁ := nruns_pop c (F m) (hFc m)
          have e₂ := nruns_dup r c hrc ((F m).set c lc) (by rw [Lists.set_ne _ _ hrc, hFr])
          rw [Lists.set_same, Lists.set_set_u (F m) c lc (lc ++ [R])] at e₂
          have hn : ccR R (m + 1) = R := by simp only [ccR]; rw [if_pos h]
          rw [hn]
          have x := (e₁.seq e₂).iteT (i := c) (c := .zero) (q := .prim (.dec c)) (by rw [hFc, h]; simp)
          exact x.mono (by omega)
        · obtain ⟨v, hv⟩ : ∃ v, ccR R m = v + 1 := ⟨ccR R m - 1, by omega⟩
          have e₁ := nruns_dec c (F m) (hFc m)
          have hn : ccR R (m + 1) = ccR R m - 1 := by simp only [ccR]; rw [if_neg h]
          rw [hn]
          have x := e₁.iteF (i := c) (c := .zero) (p := .seq (.prim (.pop c)) (.prim (.dup r c hrc)))
            (by rw [hFc, hv]; simp)
          exact x.mono (by omega)
      have htake : l.take (u + 1) = l.take u ++ [l[u]] := List.take_succ_eq_append_getElem hul
      have hmv := nruns_mv s o hso ((F m).set c (lc ++ [ccR R (m + 1)])) (l := l.take u) (v := l[u])
        (by rw [Lists.set_ne _ _ hsc, hFs, hu, htake])
      have hdrop : l.drop u = l[u] :: l.drop (u + 1) := List.drop_eq_getElem_cons hul
      have e : ((((F m).set c (lc ++ [ccR R (m + 1)])).set o (((F m).set c (lc ++ [ccR R (m + 1)])) o ++ [l[u]])).set s
          (l.take u)) = F (m + 1) := by
        rw [Lists.set_ne _ _ hoc, hFo, hu]
        have hm1 : L - (m + 1) = u := by omega
        simp only [F, hm1, hdrop, List.reverse_cons]
        funext q
        by_cases q1 : q = s
        · simp [Lists.set, q1, hsc, hso]
        · by_cases q2 : q = o
          · simp [Lists.set, q2, Ne.symm hso, hoc]
          · by_cases q3 : q = c
            · simp [Lists.set, q3, Ne.symm hsc, Ne.symm hoc]
            · simp [Lists.set, q1, q2, q3]
      rw [e] at hmv
      exact (hcnt.seq hmv).mono (by omega))
  rw [h0] at hl
  have e : F L = ((S.set s []).set o l.reverse).set c (lc ++ [ccR R l.length]) := by
    simp only [F, L, Nat.sub_self, List.take_zero, List.drop_zero]
  rw [e] at hl
  exact hl.mono (by omega)

end Shallot.MacroPeg.KExp
