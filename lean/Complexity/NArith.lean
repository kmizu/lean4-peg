import Complexity.NMacros

/-!
# Arithmetic and counted moves on stacks of numbers

* `addTo i j`: pop the top `a` of `i` and add it to the top of `j`;
* `moveN c i j`: pop the top `n` of `c` and move `n` numbers from `i` to `j` (reversing them);
* `eqFlag i j t f`: compare the tops of `i` and `j` (kept), pushing `1` on `f` if they are equal and `0` otherwise
  (`t` is scratch, left as it was).
-/

namespace Complexity

variable {K : Nat}

/-! ## Adding -/

def addTo (i j : Fin K) : NProg K := .seq (.loop i .pos (.seq (.prim (.dec i)) (.prim (.inc j)))) (.prim (.pop i))

theorem nruns_addTo (i j : Fin K) (hij : i ≠ j) (S : Lists K) {l l' : List Nat} {a b : Nat}
    (hi : S i = l ++ [a]) (hj : S j = l' ++ [b]) :
    NRuns (addTo i j) S ((S.set i l).set j (l' ++ [b + a])) (3 * a + 2) := by
  let F : Nat → Lists K := fun m => (S.set i (l ++ [a - m])).set j (l' ++ [b + m])
  have h0 : F 0 = S := by
    simp only [F, Nat.sub_zero, Nat.add_zero, ← hi, ← hj, Lists.set_get_self]
  have hFi : ∀ m, F m i = l ++ [a - m] := fun m => by simp only [F]; rw [Lists.set_ne _ _ hij, Lists.set_same]
  have hFj : ∀ m, F m j = l' ++ [b + m] := fun m => by simp only [F, Lists.set_same]
  have hl := nruns_family_const (i := i) (c := .pos) (p := .seq (.prim (.dec i)) (.prim (.inc j))) F a 2
    (fun m hm => by rw [hFi, show a - m = (a - m - 1) + 1 by omega]; simp)
    (by rw [hFi, Nat.sub_self]; simp)
    (fun m hm => by
      have h₁ := nruns_dec i (F m) (hFi m)
      have h₂ := nruns_inc j ((F m).set i (l ++ [a - m - 1])) (l := l') (v := b + m)
        (by rw [Lists.set_ne _ _ (Ne.symm hij)]; exact hFj m)
      have e : ((F m).set i (l ++ [a - m - 1])).set j (l' ++ [b + m + 1]) = F (m + 1) := by
        simp only [F]; lists_eq
      rw [e] at h₂; exact h₁.seq h₂)
  rw [h0] at hl
  have hp := nruns_pop i (F a) (l := l) (v := 0) (by rw [hFi, Nat.sub_self])
  have e : (F a).set i l = (S.set i l).set j (l' ++ [b + a]) := by
    simp only [F]; lists_eq
  rw [e] at hp
  exact (hl.seq hp).mono (by omega)

/-! ## Lowering to zero -/

/-- Lower the top of `i` to `0`. -/
def toZero (i : Fin K) : NProg K := .loop i .pos (.prim (.dec i))

theorem nruns_toZero (i : Fin K) (S : Lists K) {l : List Nat} {a : Nat} (h : S i = l ++ [a]) :
    NRuns (toZero i) S (S.set i (l ++ [0])) (2 * a + 1) := by
  let F : Nat → Lists K := fun m => S.set i (l ++ [a - m])
  have h0 : F 0 = S := by simp only [F, Nat.sub_zero, ← h, Lists.set_get_self]
  have hl := nruns_family_const (i := i) (c := .pos) (p := .prim (.dec i)) F a 1
    (fun m hm => by simp only [F, Lists.set_same]; rw [show a - m = (a - m - 1) + 1 by omega]; simp)
    (by simp [F])
    (fun m hm => by
      have := nruns_dec i (F m) (l := l) (v := a - m) (by simp [F])
      rw [show (F m).set i (l ++ [a - m - 1]) = F (m + 1) by simp only [F, Lists.set_set_u]; congr 3] at this
      exact this)
  rw [h0, show F a = S.set i (l ++ [0]) by simp [F]] at hl
  exact hl.mono (by omega)

/-! ## Comparing -/

/-- The loop body of `cmpTop`: lower both copies, or (when the second is `0` first) clear the first and mark. -/
def cmpBody (t u g : Fin K) : NProg K :=
  .ite u .pos (.seq (.prim (.dec t)) (.prim (.dec u))) (.seq (toZero t) (.prim (.inc g)))

/-- Compare the tops `a` of `i` and `b` of `j`: push `0` on `f` if `a < b`, `1` if `a = b`, `2` if `a > b`. -/
def cmpTop (i j t u g f : Fin K) (hit : i ≠ t) (hju : j ≠ u) : NProg K :=
  .seq (.prim (.dup i t hit)) (.seq (.prim (.dup j u hju)) (.seq (.prim (.pushZ g))
    (.seq (.loop t .pos (cmpBody t u g))
      (.seq (.ite g .pos (npushC f 2) (.ite u .zero (npushC f 1) (npushC f 0)))
        (.seq (.prim (.pop t)) (.seq (.prim (.pop u)) (.prim (.pop g))))))))

/-- The result of comparing. -/
def cmpRes (a b : Nat) : Nat := if a < b then 0 else if a = b then 1 else 2

theorem nruns_cmpTop (i j t u g f : Fin K) (hit : i ≠ t) (hju : j ≠ u) (hd : [i, j, t, u, g, f].Nodup)
    (S : Lists K) {li lj : List Nat} {a b : Nat} (hi : S i = li ++ [a]) (hj : S j = lj ++ [b]) :
    NRuns (cmpTop i j t u g f hit hju) S (S.set f (S f ++ [cmpRes a b])) ((a + b + 1) * (2 * a + 6) + 20) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd
  obtain ⟨⟨_, _, _, _, _⟩, ⟨_, _, _, _⟩, ⟨htu, htg, htf⟩, ⟨hug, huf⟩, hgf⟩ := hd
  -- both copies lowered by `m`
  let reg : Nat → Lists K := fun m => ((S.set t (S t ++ [a - m])).set u (S u ++ [b - m])).set g (S g ++ [0])
  have x₁ := nruns_dup i t hit S hi
  have x₂ := nruns_dup j u hju (S.set t (S t ++ [a])) (l := lj) (v := b) (by rw [Lists.set_ne]; exact hj; assumption)
  have x₃ := nruns_pushZ g ((S.set t (S t ++ [a])).set u ((S.set t (S t ++ [a])) u ++ [b]))
  have e₀ : ((S.set t (S t ++ [a])).set u ((S.set t (S t ++ [a])) u ++ [b])).set g
      (((S.set t (S t ++ [a])).set u ((S.set t (S t ++ [a])) u ++ [b])) g ++ [0]) = reg 0 := by
    simp only [reg]; lists_eq
  rw [e₀] at x₃
  have hrt : ∀ m, reg m t = S t ++ [a - m] := fun m => by simp only [reg]; lists_at
  have hru : ∀ m, reg m u = S u ++ [b - m] := fun m => by simp only [reg]; lists_at
  have hrg : ∀ m, reg m g = S g ++ [0] := fun m => by simp only [reg]; lists_at
  -- the end: pop the copies and the mark
  have finish : ∀ (St : Lists K) (r vt vu vg : Nat), St = ((S.set t (S t ++ [vt])).set u (S u ++ [vu])).set g
      (S g ++ [vg]) → NRuns (.seq (.prim (.pop t)) (.seq (.prim (.pop u)) (.prim (.pop g))))
        (St.set f (S f ++ [r])) (S.set f (S f ++ [r])) 3 := by
    intro St r vt vu vg hSt
    have p₁ := nruns_pop t (St.set f (S f ++ [r])) (l := S t) (v := vt) (by rw [hSt]; lists_at)
    have p₂ := nruns_pop u ((St.set f (S f ++ [r])).set t (S t)) (l := S u) (v := vu) (by rw [hSt]; lists_at)
    have p₃ := nruns_pop g (((St.set f (S f ++ [r])).set t (S t)).set u (S u)) (l := S g) (v := vg)
      (by rw [hSt]; lists_at)
    have e : ((((St.set f (S f ++ [r])).set t (S t)).set u (S u)).set g (S g)) = S.set f (S f ++ [r]) := by
      rw [hSt]; lists_eq
    rw [e] at p₃
    exact p₁.seq (p₂.seq p₃)
  by_cases hab : a ≤ b
  · -- the first copy reaches zero first (or both together)
    have hl := nruns_family_const (i := t) (c := .pos) (p := cmpBody t u g) reg a 3
      (fun m hm => by rw [hrt, show a - m = (a - m - 1) + 1 by omega]; simp)
      (by rw [hrt, Nat.sub_self]; simp)
      (fun m hm => by
        have d₁ := nruns_dec t (reg m) (hrt m)
        have d₂ := nruns_dec u ((reg m).set t (S t ++ [a - m - 1])) (l := S u) (v := b - m)
          (by rw [Lists.set_ne _ _ (Ne.symm htu)]; exact hru m)
        have e : ((reg m).set t (S t ++ [a - m - 1])).set u (S u ++ [b - m - 1]) = reg (m + 1) := by
          simp only [reg]; lists_eq
        rw [e] at d₂
        exact ((d₁.seq d₂).iteT (by rw [hru, show b - m = (b - m - 1) + 1 by omega]; simp)).mono (by omega))
    by_cases heq : a = b
    · subst heq
      have hc : cmpRes a a = 1 := by simp [cmpRes]
      have pc := nruns_pushC f (reg a) 1
      have hit' := (pc.iteT (i := u) (c := .zero) (q := npushC f 0) (by rw [hru, Nat.sub_self]; simp)).iteF
        (i := g) (c := .pos) (p := npushC f 2) (by rw [hrg]; simp)
      have hfin := finish (reg a) 1 0 0 0 (by simp only [reg, Nat.sub_self])
      rw [show (reg a) f = S f by simp only [reg]; lists_at] at hit'
      rw [hc]
      refine (x₁.seq (x₂.seq (x₃.seq (hl.seq (hit'.seq hfin))))).mono ?_
      have : a * (3 + 1) + 1 ≤ (a + a + 1) * (2 * a + 6) := by
        have := Nat.mul_le_mul (show a + a + 1 ≥ a + 1 by omega) (show 2 * a + 6 ≥ 4 by omega); omega
      omega
    · have hlt : a < b := by omega
      have hc : cmpRes a b = 0 := by simp [cmpRes, hlt]
      have pc := nruns_pushC f (reg a) 0
      have hit' := (pc.iteF (i := u) (c := .zero) (p := npushC f 1)
        (by rw [hru, show b - a = (b - a - 1) + 1 by omega]; simp)).iteF
        (i := g) (c := .pos) (p := npushC f 2) (by rw [hrg]; simp)
      have hfin := finish (reg a) 0 0 (b - a) 0 (by simp only [reg, Nat.sub_self])
      rw [show (reg a) f = S f by simp only [reg]; lists_at] at hit'
      rw [hc]
      refine (x₁.seq (x₂.seq (x₃.seq (hl.seq (hit'.seq hfin))))).mono ?_
      have : a * (3 + 1) + 1 ≤ (a + b + 1) * (2 * a + 6) := by
        have := Nat.mul_le_mul (show a + b + 1 ≥ a + 1 by omega) (show 2 * a + 6 ≥ 4 by omega); omega
      omega
  · -- the second copy reaches zero first: clear the first, mark
    have hba : b < a := by omega
    let mk : Lists K := ((S.set t (S t ++ [0])).set u (S u ++ [0])).set g (S g ++ [1])
    let F : Nat → Lists K := fun m => if m ≤ b then reg m else mk
    have hFt : ∀ m, m ≤ b → F m t = S t ++ [a - m] := fun m hm => by simp only [F, hm, if_true]; exact hrt m
    have hl := nruns_family_const (i := t) (c := .pos) (p := cmpBody t u g) F (b + 1) (2 * a + 4)
      (fun m hm => by rw [hFt m (by omega), show a - m = (a - m - 1) + 1 by omega]; simp)
      (by simp only [F, show ¬ b + 1 ≤ b by omega, if_false, mk]; rw [show ((((S.set t (S t ++ [0])).set u
          (S u ++ [0])).set g (S g ++ [1])) t) = S t ++ [0] by lists_at]; simp)
      (fun m hm => by
        by_cases hmb : m < b
        · have hF : F m = reg m := by simp only [F, show m ≤ b by omega, if_true]
          have hF' : F (m + 1) = reg (m + 1) := by simp only [F, show m + 1 ≤ b by omega, if_true]
          rw [hF, hF']
          have d₁ := nruns_dec t (reg m) (hrt m)
          have d₂ := nruns_dec u ((reg m).set t (S t ++ [a - m - 1])) (l := S u) (v := b - m)
            (by rw [Lists.set_ne _ _ (Ne.symm htu)]; exact hru m)
          have e : ((reg m).set t (S t ++ [a - m - 1])).set u (S u ++ [b - m - 1]) = reg (m + 1) := by
            simp only [reg]; lists_eq
          rw [e] at d₂
          exact ((d₁.seq d₂).iteT (by rw [hru, show b - m = (b - m - 1) + 1 by omega]; simp)).mono (by omega)
        · obtain rfl : m = b := by omega
          have hF : F m = reg m := by simp only [F, Nat.le_refl, if_true]
          have hF' : F (m + 1) = mk := by simp only [F, show ¬ m + 1 ≤ m by omega, if_false]
          rw [hF, hF']
          have z := nruns_toZero t (reg m) (hrt m)
          have ig := nruns_inc g ((reg m).set t (S t ++ [0])) (l := S g) (v := 0)
            (by rw [Lists.set_ne _ _ (Ne.symm htg)]; exact hrg m)
          have e : ((reg m).set t (S t ++ [0])).set g (S g ++ [0 + 1]) = mk := by simp only [reg, mk]; lists_eq
          rw [e] at ig
          exact ((z.seq ig).iteF (by rw [hru, Nat.sub_self]; simp)).mono (by omega))
    have hF0 : F 0 = reg 0 := by simp [F]
    rw [hF0, show F (b + 1) = mk by simp only [F, show ¬ b + 1 ≤ b by omega, if_false]] at hl
    have hc : cmpRes a b = 2 := by simp [cmpRes, show ¬ a < b by omega, show a ≠ b by omega]
    have pc := nruns_pushC f mk 2
    have hit' := pc.iteT (i := g) (c := .pos) (q := .ite u .zero (npushC f 1) (npushC f 0))
      (by rw [show mk g = S g ++ [1] by simp only [mk]; lists_at]; simp)
    have hfin := finish mk 2 0 0 1 rfl
    rw [show mk f = S f by simp only [mk]; lists_at] at hit'
    rw [hc]
    refine (x₁.seq (x₂.seq (x₃.seq (hl.seq (hit'.seq hfin))))).mono ?_
    have h1 : (b + 1) * (2 * a + 6) ≤ (a + b + 1) * (2 * a + 6) := Nat.mul_le_mul_right _ (by omega)
    have h2 : (b + 1) * (2 * a + 6) = (b + 1) * (2 * a + 4 + 1) + (b + 1) := by
      rw [show 2 * a + 6 = (2 * a + 4 + 1) + 1 by omega, Nat.mul_succ]
    omega

end Complexity
