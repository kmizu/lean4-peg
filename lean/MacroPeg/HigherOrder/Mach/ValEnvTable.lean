import MacroPeg.HigherOrder.Mach.EvalStacks

/-!
# The tables of value lengths and environment counts on stacks

`valTableP` builds `valTable` on `VALT`: entry `0` is `N + 1` (read from `NX`), and entry `k + 1` is
`(entry a of CNT) · (entry b of VALT)` for the arrow `tt[k] = (a, b)`. `envTableP` builds `envTable` on `ENVT`:
entry `0` is `1`, and entry `k + 1` is `(entry par of ENVT) · (entry t of CNT)` for `ct[k] = (par, t)`.

Both share one loop (`ve_loop`): the pair table (`TTs` or `CTs`) is moved, reversed, onto the scratch stack `ve_W`;
each round moves one pair back (restoring the table), reads the two entries with `peekAt`, and pushes their product
(`ve_mul`, repeated addition) on the table being built.
-/

namespace Shallot.MacroPeg.Mach

open Complexity

/-! ## Multiplying -/

section Mul

variable {K : Nat}

/-- Pop `x` (top of `a`) and `y` (top of `b`) and push `x * y` on `d`; `t` is scratch (empty before and after). -/
def ve_mul (a b t d : Fin K) (hbt : b ≠ t) : NProg K :=
  .seq (.prim (.pushZ d))
    (.seq (.loop a .pos (.seq (.prim (.dec a)) (.seq (.prim (.dup b t hbt)) (addTo t d))))
      (.seq (.prim (.pop a)) (.prim (.pop b))))

theorem ve_mul_runs (a b t d : Fin K) (hbt : b ≠ t) (hab : a ≠ b) (hat : a ≠ t) (had : a ≠ d) (hbd : b ≠ d)
    (htd : t ≠ d) (S : Lists K) {la lb : List Nat} {x y : Nat} (ha : S a = la ++ [x]) (hb : S b = lb ++ [y])
    (ht : S t = []) :
    NRuns (ve_mul a b t d hbt) S (((S.set a la).set b lb).set d (S d ++ [x * y])) (x * (3 * y + 5) + 4) := by
  have x₀ := nruns_pushZ d S
  let F : Nat → Lists K := fun m => (S.set a (la ++ [x - m])).set d (S d ++ [m * y])
  have h0 : F 0 = S.set d (S d ++ [0]) := by
    simp only [F, Nat.sub_zero, Nat.zero_mul, ← ha, Lists.set_get_self]
  have hFa : ∀ m, F m a = la ++ [x - m] := fun m => by
    simp only [F]; rw [Lists.set_ne _ _ had, Lists.set_same]
  have hFb : ∀ m, F m b = lb ++ [y] := fun m => by
    simp only [F]; rw [Lists.set_ne _ _ hbd, Lists.set_ne _ _ (Ne.symm hab), hb]
  have hFt : ∀ m, F m t = [] := fun m => by
    simp only [F]; rw [Lists.set_ne _ _ htd, Lists.set_ne _ _ (Ne.symm hat), ht]
  have hFd : ∀ m, F m d = S d ++ [m * y] := fun m => by simp only [F, Lists.set_same]
  have hl := nruns_family_const (i := a) (c := .pos)
    (p := .seq (.prim (.dec a)) (.seq (.prim (.dup b t hbt)) (addTo t d))) F x (3 * y + 4)
    (fun m hm => by rw [hFa, show x - m = (x - m - 1) + 1 by omega]; simp)
    (by rw [hFa, Nat.sub_self]; simp)
    (fun m hm => by
      have d₁ := nruns_dec a (F m) (hFa m)
      let G := (F m).set a (la ++ [x - m - 1])
      have d₂ := nruns_dup b t hbt G (l := lb) (v := y) (by
        simp only [G]; rw [Lists.set_ne _ _ (Ne.symm hab), hFb])
      have hGt : G t = [] := by simp only [G]; rw [Lists.set_ne _ _ (Ne.symm hat), hFt]
      rw [hGt, List.nil_append] at d₂
      have d₃ := nruns_addTo t d htd (G.set t [y]) (l := []) (l' := S d) (a := y) (b := m * y)
        (by rw [Lists.set_same]; rfl)
        (by rw [Lists.set_ne _ _ (Ne.symm htd)]; simp only [G]; rw [Lists.set_ne _ _ (Ne.symm had), hFd])
      have e : ((G.set t [y]).set t []).set d (S d ++ [m * y + y]) = F (m + 1) := by
        rw [Lists.set_set_u]
        have hz : G.set t [] = G := by rw [← hGt, Lists.set_get_self]
        rw [hz]
        simp only [G, F]
        rw [show x - (m + 1) = x - m - 1 by omega, Nat.succ_mul]
        funext z
        simp only [Lists.set]
        by_cases hzd : z = d
        · simp [hzd]
        · by_cases hza : z = a
          · simp [hza, had]
          · simp [hzd, hza]
      rw [e] at d₃
      exact (d₁.seq (d₂.seq d₃)).mono (by omega))
  rw [h0] at hl
  have hp₁ := nruns_pop a (F x) (hFa x)
  have hp₂ := nruns_pop b ((F x).set a la) (l := lb) (v := y) (by
    rw [Lists.set_ne _ _ (Ne.symm hab), hFb])
  have e : (((F x).set a la).set b lb) = ((S.set a la).set b lb).set d (S d ++ [x * y]) := by
    simp only [F]
    funext z
    simp only [Lists.set]
    by_cases hzd : z = d
    · simp [hzd, Ne.symm hbd, Ne.symm had]
    · by_cases hza : z = a
      · simp [hza, hab, had]
      · simp [hzd, hza]
  rw [e] at hp₂
  refine (x₀.seq (hl.seq (hp₁.seq hp₂))).mono ?_
  rw [Nat.mul_succ]
  omega

end Mul

/-! ## Scratch stacks -/

/-- The pair table, reversed (its first entry on top). -/
abbrev ve_W : Fin NK := 18
/-- The two components of the current pair. -/
abbrev ve_CA : Fin NK := 19
abbrev ve_CB : Fin NK := 20
/-- The two entries read. -/
abbrev ve_OA : Fin NK := 21
abbrev ve_OB : Fin NK := 22
/-- Scratch of `peekAt` and of `ve_mul`. -/
abbrev ve_T : Fin NK := 23
abbrev ve_U : Fin NK := 24

/-- A stack outside the scratch range. -/
def ve_out (i : Fin NK) : Prop := i.val < 18 ∨ 33 < i.val

theorem ve_ne {i : Fin NK} (hi : ve_out i) (s : Fin NK) (hs : 18 ≤ s.val ∧ s.val ≤ 33 := by decide) : i ≠ s := by
  intro h; subst h; unfold ve_out at hi; omega

/-- A stack outside the scratch range differs from every scratch stack of a round. -/
theorem ve_ne7 {i : Fin NK} (hi : ve_out i) :
    i ≠ ve_W ∧ i ≠ ve_CA ∧ i ≠ ve_CB ∧ i ≠ ve_OA ∧ i ≠ ve_OB ∧ i ≠ ve_T ∧ i ≠ ve_U :=
  ⟨ve_ne hi _, ve_ne hi _, ve_ne hi _, ve_ne hi _, ve_ne hi _, ve_ne hi _, ve_ne hi _⟩

/-! ## One round -/

/-- Move the next pair `(p, q)` back from `ve_W` to `Src`, read entry `p` of `X` and entry `q` of `Y`, and push their
product on `D`. -/
def ve_round (Src X Y D : Fin NK) (hS : ve_out Src) (hX : ve_out X) (hY : ve_out Y) : NProg NK :=
  .seq (.prim (.dup ve_W Src (ve_ne hS ve_W).symm)) (.seq (nmv ve_W ve_CA (by decide))
    (.seq (.prim (.dup ve_W Src (ve_ne hS ve_W).symm)) (.seq (nmv ve_W ve_CB (by decide))
      (.seq (peekAt X ve_T ve_CA ve_OA (ve_ne hX ve_T) (by decide))
        (.seq (peekAt Y ve_T ve_CB ve_OB (ve_ne hY ve_T) (by decide)) (ve_mul ve_OA ve_OB ve_U D (by decide)))))))

/-- The scratch stacks of a round are empty. -/
def ve_clean (St : Lists NK) : Prop :=
  St ve_CA = [] ∧ St ve_CB = [] ∧ St ve_OA = [] ∧ St ve_OB = [] ∧ St ve_T = [] ∧ St ve_U = []

theorem ve_round_runs (Src X Y D : Fin NK) (hS : ve_out Src) (hX : ve_out X) (hY : ve_out Y) (hD : ve_out D)
    (hSD : Src ≠ D) (hXS : X ≠ Src) (hYS : Y ≠ Src) (St : Lists NK) {rest : List Nat} {p q : Nat}
    (hW : St ve_W = rest ++ [q, p]) (hc : ve_clean St) (hp : p < (St X).length) (hq : q < (St Y).length) :
    NRuns (ve_round Src X Y D hS hX hY) St
      (((St.set ve_W rest).set Src (St Src ++ [p, q])).set D (St D ++ [(St X)[p] * (St Y)[q]]))
      (6 * (St X).length + 4 * p + 6 * (St Y).length + 4 * q + (St X)[p] * (3 * (St Y)[q] + 5) + 22) := by
  obtain ⟨hCA, hCB, hOA, hOB, hT, hU⟩ := hc
  obtain ⟨sW, sCA, sCB, sOA, sOB, sT, sU⟩ := ve_ne7 hS
  obtain ⟨xW, xCA, xCB, xOA, xOB, xT, xU⟩ := ve_ne7 hX
  obtain ⟨yW, yCA, yCB, yOA, yOB, yT, yU⟩ := ve_ne7 hY
  obtain ⟨dW, dCA, dCB, dOA, dOB, dT, dU⟩ := ve_ne7 hD
  have x₁ := nruns_dup ve_W Src sW.symm St (l := rest ++ [q]) (v := p) (by rw [hW]; simp)
  let S₁ := St.set Src (St Src ++ [p])
  have x₂ := nruns_mv ve_W ve_CA (by decide) S₁ (l := rest ++ [q]) (v := p)
    (by simp only [S₁]; rw [Lists.set_ne _ _ sW.symm, hW]; simp)
  let S₂ := (S₁.set ve_CA (S₁ ve_CA ++ [p])).set ve_W (rest ++ [q])
  have x₃ := nruns_dup ve_W Src sW.symm S₂ (l := rest) (v := q) (by simp [S₂])
  let S₃ := S₂.set Src (S₂ Src ++ [q])
  have x₄ := nruns_mv ve_W ve_CB (by decide) S₃ (l := rest) (v := q)
    (by simp only [S₃]; rw [Lists.set_ne _ _ sW.symm]; simp [S₂])
  let S₄ := (S₃.set ve_CB (S₃ ve_CB ++ [q])).set ve_W rest
  have h₄X : S₄ X = St X := by
    simp only [S₄, S₃, S₂, S₁]
    rw [Lists.set_ne _ _ xW, Lists.set_ne _ _ xCB, Lists.set_ne _ _ hXS, Lists.set_ne _ _ xW, Lists.set_ne _ _ xCA,
      Lists.set_ne _ _ hXS]
  have h₄CA : S₄ ve_CA = [] ++ [p] := by
    simp only [S₄, S₃, S₂, S₁]
    rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide), Lists.set_ne _ _ sCA.symm,
      Lists.set_ne _ _ (by decide), Lists.set_same, Lists.set_ne _ _ sCA.symm, hCA]
  have h₄T : S₄ ve_T = [] := by
    simp only [S₄, S₃, S₂, S₁]
    rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide), Lists.set_ne _ _ sT.symm,
      Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide), Lists.set_ne _ _ sT.symm, hT]
  have x₅ := nruns_peekAt X ve_T ve_CA ve_OA xT (by decide) (by simp [xT, xCA, xOA]; decide) S₄ h₄T h₄CA (k := p)
    (by rw [h₄X]; exact hp)
  have hx : (S₄ X)[p]'(by rw [h₄X]; exact hp) = (St X)[p] := by simp only [h₄X]
  rw [hx] at x₅
  have h₄OA : S₄ ve_OA = [] := by
    simp only [S₄, S₃, S₂, S₁]
    rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide), Lists.set_ne _ _ sOA.symm,
      Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide), Lists.set_ne _ _ sOA.symm, hOA]
  rw [h₄OA, List.nil_append] at x₅
  let S₅ := (S₄.set ve_CA []).set ve_OA [(St X)[p]]
  have h₅Y : S₅ Y = St Y := by
    simp only [S₅, S₄, S₃, S₂, S₁]
    rw [Lists.set_ne _ _ yOA, Lists.set_ne _ _ yCA, Lists.set_ne _ _ yW, Lists.set_ne _ _ yCB, Lists.set_ne _ _ hYS,
      Lists.set_ne _ _ yW, Lists.set_ne _ _ yCA, Lists.set_ne _ _ hYS]
  have h₅CB : S₅ ve_CB = [] ++ [q] := by
    simp only [S₅, S₄, S₃, S₂, S₁]
    rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide), Lists.set_same,
      Lists.set_ne _ _ sCB.symm, Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide),
      Lists.set_ne _ _ sCB.symm, hCB]
  have h₅T : S₅ ve_T = [] := by
    simp only [S₅]
    rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide), h₄T]
  have x₆ := nruns_peekAt Y ve_T ve_CB ve_OB yT (by decide) (by simp [yT, yCB, yOB]; decide) S₅ h₅T h₅CB (k := q)
    (by rw [h₅Y]; exact hq)
  have hy : (S₅ Y)[q]'(by rw [h₅Y]; exact hq) = (St Y)[q] := by simp only [h₅Y]
  rw [hy] at x₆
  have h₅OB : S₅ ve_OB = [] := by
    simp only [S₅, S₄, S₃, S₂, S₁]
    rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide),
      Lists.set_ne _ _ (by decide), Lists.set_ne _ _ sOB.symm, Lists.set_ne _ _ (by decide),
      Lists.set_ne _ _ (by decide), Lists.set_ne _ _ sOB.symm, hOB]
  rw [h₅OB, List.nil_append] at x₆
  let S₆ := (S₅.set ve_CB []).set ve_OB [(St Y)[q]]
  have x₇ := ve_mul_runs ve_OA ve_OB ve_U D (by decide) (by decide) (by decide) dOA.symm dOB.symm dU.symm S₆
    (la := []) (lb := []) (x := (St X)[p]) (y := (St Y)[q])
    (by simp only [S₆, S₅]; rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide), Lists.set_same]; rfl)
    (by simp only [S₆, Lists.set_same]; rfl)
    (by
      simp only [S₆, S₅, S₄, S₃, S₂, S₁]
      rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide),
        Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide),
        Lists.set_ne _ _ sU.symm, Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide),
        Lists.set_ne _ _ sU.symm, hU])
  have h₆D : S₆ D = St D := by
    simp only [S₆, S₅, S₄, S₃, S₂, S₁]
    rw [Lists.set_ne _ _ dOB, Lists.set_ne _ _ dCB, Lists.set_ne _ _ dOA, Lists.set_ne _ _ dCA, Lists.set_ne _ _ dW,
      Lists.set_ne _ _ dCB, Lists.set_ne _ _ hSD.symm, Lists.set_ne _ _ dW, Lists.set_ne _ _ dCA,
      Lists.set_ne _ _ hSD.symm]
  rw [h₆D] at x₇
  have e : ((S₆.set ve_OA []).set ve_OB []).set D (St D ++ [(St X)[p] * (St Y)[q]]) =
      ((St.set ve_W rest).set Src (St Src ++ [p, q])).set D (St D ++ [(St X)[p] * (St Y)[q]]) := by
    clear x₁ x₂ x₃ x₄ x₅ x₆ x₇ hx hy
    funext z
    by_cases hzD : z = D
    · subst hzD; rw [Lists.set_same, Lists.set_same]
    rw [Lists.set_ne _ _ hzD, Lists.set_ne _ _ hzD]
    simp only [S₆, S₅, S₄, S₃, S₂, S₁]
    by_cases hzS : z = Src
    · subst hzS
      simp (config := {decide := true}) only [Lists.set, sW, sCA, sCB, sOA, sOB, ite_true, ite_false,
        List.append_assoc, List.cons_append, List.nil_append]
    by_cases hzW : z = ve_W
    · subst hzW
      simp (config := {decide := true}) only [Lists.set, sW.symm, ite_true, ite_false]
    by_cases hzA : z = ve_CA
    · subst hzA
      simp (config := {decide := true}) only [Lists.set, sCA.symm, ite_true, ite_false, hCA]
    by_cases hzB : z = ve_CB
    · subst hzB
      simp (config := {decide := true}) only [Lists.set, sCB.symm, ite_true, ite_false, hCB]
    by_cases hzOA : z = ve_OA
    · subst hzOA
      simp (config := {decide := true}) only [Lists.set, sOA.symm, ite_true, ite_false, hOA]
    by_cases hzOB : z = ve_OB
    · subst hzOB
      simp (config := {decide := true}) only [Lists.set, sOB.symm, ite_true, ite_false, hOB]
    simp only [Lists.set, hzS, hzW, hzA, hzB, hzOA, hzOB, ite_false]
  rw [e] at x₇
  refine (x₁.seq (x₂.seq (x₃.seq (x₄.seq (x₅.seq (x₆.seq x₇)))))).mono ?_
  rw [h₄X, h₅Y]
  omega

/-! ## The loop over the pairs -/

/-- The first `m + 1` entries of a table. -/
def ve_tab (f : Nat → Nat) (m : Nat) : List Nat := (List.range (m + 1)).map f

theorem ve_tab_succ (f : Nat → Nat) (m : Nat) : ve_tab f (m + 1) = ve_tab f m ++ [f (m + 1)] := by
  simp only [ve_tab]; rw [List.range_succ, List.map_append]; rfl

theorem ve_tab_length (f : Nat → Nat) (m : Nat) : (ve_tab f m).length = m + 1 := by simp [ve_tab]

theorem ve_tab_get (f : Nat → Nat) (m a : Nat) (h : a < (ve_tab f m).length) : (ve_tab f m)[a] = f a := by
  simp [ve_tab]

theorem ve_encPairs_take {P : List (Nat × Nat)} {m : Nat} (hm : m < P.length) :
    encPairs (P.take (m + 1)) = encPairs (P.take m) ++ [P[m].1, P[m].2] := by
  rw [List.take_succ_eq_append_getElem hm]; simp only [encPairs, List.flatMap_append]; rfl

theorem ve_encPairs_drop {P : List (Nat × Nat)} {m : Nat} (hm : m < P.length) :
    (encPairs (P.drop m)).reverse = (encPairs (P.drop (m + 1))).reverse ++ [P[m].2, P[m].1] := by
  rw [List.drop_eq_getElem_cons hm]; simp only [encPairs, List.flatMap_cons]; simp

/-- The stacks after `m` rounds: `m` pairs moved back to `Src`, the rest (reversed) on `ve_W`, entries `0 … m` of the
table on `D`. -/
def ve_st (S : Lists NK) (Src D : Fin NK) (P : List (Nat × Nat)) (f : Nat → Nat) (m : Nat) : Lists NK :=
  ((S.set Src (encPairs (P.take m))).set ve_W (encPairs (P.drop m)).reverse).set D (ve_tab f m)

/-- The rounds, while pairs remain on `ve_W`. -/
def ve_loop (Src X Y D : Fin NK) (hS : ve_out Src) (hX : ve_out X) (hY : ve_out Y) : NProg NK :=
  .loop ve_W .nonempty (ve_round Src X Y D hS hX hY)

/-- The cost of one round. -/
def ve_roundCost (lx p ly q x y : Nat) : Nat := 6 * lx + 4 * p + 6 * ly + 4 * q + x * (3 * y + 5) + 22

theorem ve_loop_runs (Src X Y D : Fin NK) (hS : ve_out Src) (hX : ve_out X) (hY : ve_out Y) (hD : ve_out D)
    (hSD : Src ≠ D) (hXS : X ≠ Src) (hYS : Y ≠ Src) (S : Lists NK) (hc : ve_clean S) (P : List (Nat × Nat))
    (f : Nat → Nat) (T : Nat)
    (hstep : ∀ m (hm : m < P.length), ∃ (hp : P[m].1 < (ve_st S Src D P f m X).length)
      (hq : P[m].2 < (ve_st S Src D P f m Y).length),
      (ve_st S Src D P f m X)[P[m].1] * (ve_st S Src D P f m Y)[P[m].2] = f (m + 1) ∧
      ve_roundCost (ve_st S Src D P f m X).length P[m].1 (ve_st S Src D P f m Y).length P[m].2
        (ve_st S Src D P f m X)[P[m].1] (ve_st S Src D P f m Y)[P[m].2] ≤ T) :
    NRuns (ve_loop Src X Y D hS hX hY) (ve_st S Src D P f 0) (ve_st S Src D P f P.length)
      (P.length * (T + 1) + 1) := by
  obtain ⟨sW, sCA, sCB, sOA, sOB, sT, sU⟩ := ve_ne7 hS
  obtain ⟨dW, dCA, dCB, dOA, dOB, dT, dU⟩ := ve_ne7 hD
  have hW : ∀ m, ve_st S Src D P f m ve_W = (encPairs (P.drop m)).reverse := fun m => by
    simp only [ve_st]; rw [Lists.set_ne _ _ dW.symm, Lists.set_same]
  have hSrc : ∀ m, ve_st S Src D P f m Src = encPairs (P.take m) := fun m => by
    simp only [ve_st]; rw [Lists.set_ne _ _ hSD, Lists.set_ne _ _ sW, Lists.set_same]
  have hDm : ∀ m, ve_st S Src D P f m D = ve_tab f m := fun m => by simp only [ve_st, Lists.set_same]
  have hclean : ∀ m, ve_clean (ve_st S Src D P f m) := fun m => by
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hc
    simp only [ve_clean, ve_st]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Lists.set_ne _ _ dCA.symm, Lists.set_ne _ _ (by decide), Lists.set_ne _ _ sCA.symm, h₁]
    · rw [Lists.set_ne _ _ dCB.symm, Lists.set_ne _ _ (by decide), Lists.set_ne _ _ sCB.symm, h₂]
    · rw [Lists.set_ne _ _ dOA.symm, Lists.set_ne _ _ (by decide), Lists.set_ne _ _ sOA.symm, h₃]
    · rw [Lists.set_ne _ _ dOB.symm, Lists.set_ne _ _ (by decide), Lists.set_ne _ _ sOB.symm, h₄]
    · rw [Lists.set_ne _ _ dT.symm, Lists.set_ne _ _ (by decide), Lists.set_ne _ _ sT.symm, h₅]
    · rw [Lists.set_ne _ _ dU.symm, Lists.set_ne _ _ (by decide), Lists.set_ne _ _ sU.symm, h₆]
  refine nruns_family_const (ve_st S Src D P f) P.length T
    (fun m hm => by rw [hW, ve_encPairs_drop hm]; exact eval_nonempty_ne (by simp))
    (by rw [hW, List.drop_length]; rfl)
    (fun m hm => ?_)
  obtain ⟨hp, hq, hval, hcost⟩ := hstep m hm
  have r := ve_round_runs Src X Y D hS hX hY hD hSD hXS hYS (ve_st S Src D P f m)
    (rest := (encPairs (P.drop (m + 1))).reverse) (by rw [hW, ve_encPairs_drop hm]) (hclean m) hp hq
  rw [hval] at r
  have e : (((ve_st S Src D P f m).set ve_W (encPairs (P.drop (m + 1))).reverse).set Src
      (ve_st S Src D P f m Src ++ [P[m].1, P[m].2])).set D (ve_st S Src D P f m D ++ [f (m + 1)]) =
      ve_st S Src D P f (m + 1) := by
    rw [hSrc, hDm, ← ve_encPairs_take hm, ← ve_tab_succ]
    funext z
    simp only [ve_st, Lists.set]
    by_cases hzD : z = D
    · simp [hzD]
    by_cases hzS : z = Src
    · simp [hzS, hSD, sW]
    by_cases hzW : z = ve_W
    · simp [hzW, sW.symm, dW.symm]
    simp [hzD, hzS, hzW]
  rw [e] at r
  exact r.mono hcost

/-! ## Costs -/

/-- An entry of a list of numbers is at most its sum. -/
theorem ve_get_le_sum : ∀ (l : List Nat) (i : Nat) (h : i < l.length), l[i] ≤ l.sum
  | [], _, h => absurd h (by simp)
  | a :: l, 0, _ => by simp
  | a :: l, i + 1, h => by
    have := ve_get_le_sum l i (by simpa using h)
    simp only [List.getElem_cons_succ, List.sum_cons]; omega

theorem ve_round_le {M lx p ly q x y : Nat} (h2 : 2 ≤ M) (hlx : lx ≤ M) (hp : p ≤ M) (hly : ly ≤ M) (hq : q ≤ M)
    (hx : x ≤ M) (hy : y ≤ M) : ve_roundCost lx p ly q x y ≤ 30 * (M * M) := by
  have h₁ : x * (3 * y + 5) ≤ M * (3 * M + 5) := Nat.mul_le_mul hx (by omega)
  have h₂ : M * (3 * M + 5) = 3 * (M * M) + 5 * M := by rw [Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm M 5]
  have h₃ : 2 * M ≤ M * M := Nat.mul_le_mul_right M h2
  unfold ve_roundCost
  omega

theorem ve_total_le {M L A : Nat} (h2 : 2 ≤ M) (hL : L ≤ M) (hA : A ≤ 3) :
    A + (3 * (2 * L) + 1) + (L * (30 * (M * M) + 1) + 1) ≤ 1000 * M ^ 3 := by
  have h₁ : L * (30 * (M * M) + 1) ≤ M * (30 * (M * M) + 1) := Nat.mul_le_mul_right _ hL
  have h₂ : M * (30 * (M * M) + 1) = 30 * (M * (M * M)) + M := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]
  have h₃ : 2 * M ≤ M * M := Nat.mul_le_mul_right M h2
  have h₄ : 2 * (M * M) ≤ M * (M * M) := Nat.mul_le_mul_right (M * M) h2
  have h₅ : M ^ 3 = M * (M * M) := by rw [Nat.pow_succ, Nat.pow_two, Nat.mul_comm]
  rw [h₅]
  omega

/-! ## Facts about the tables -/

theorem ve_valT_succ {j cap N : Nat} {tt : List (Nat × Nat)} (hw : TTWF tt) (k : Nat) (hk : k < tt.length) :
    valT j cap N tt (k + 1) = (rowsT j cap N tt tt[k].1).length * valT j cap N tt tt[k].2 := by
  have hab := hw.2 k hk
  rw [valT]
  simp only [List.getElem?_eq_getElem hk]
  rw [if_pos hab]

theorem ve_envT_succ {j cap N : Nat} {tt ct : List (Nat × Nat)} (hc : CTWF tt ct) (k : Nat) (hk : k < ct.length) :
    envT j cap N tt ct (k + 1) = envT j cap N tt ct ct[k].1 * (rowsT j cap N tt ct[k].2).length := by
  have hp := (hc k hk).1
  rw [envT]
  simp only [List.getElem?_eq_getElem hk]
  rw [if_pos hp]

theorem ve_cnt_length (j cap N : Nat) (tt : List (Nat × Nat)) : (cntTable j cap N tt).length = tt.length + 1 := by
  simp [cntTable, typeTable]

theorem ve_cnt_get {j cap N : Nat} {tt : List (Nat × Nat)} (a : Nat) (h : a < (cntTable j cap N tt).length) :
    (cntTable j cap N tt)[a] = (rowsT j cap N tt a).length := by
  simp [cntTable, typeTable]

theorem ve_clean_of {S : Lists NK} (hs : ScratchEmpty S) : ve_clean S :=
  ⟨hs _ (by decide) (by decide), hs _ (by decide) (by decide), hs _ (by decide) (by decide),
    hs _ (by decide) (by decide), hs _ (by decide) (by decide), hs _ (by decide) (by decide)⟩

/-! ## The table of value lengths -/

theorem ve_out_TTs : ve_out TTs := by unfold ve_out; decide
theorem ve_out_CTs : ve_out CTs := by unfold ve_out; decide
theorem ve_out_CNT : ve_out CNT := by unfold ve_out; decide
theorem ve_out_VALT : ve_out VALT := by unfold ve_out; decide
theorem ve_out_ENVT : ve_out ENVT := by unfold ve_out; decide

/-- Build `valTable` on `VALT`: push `N + 1`, then one round per arrow. -/
def valTableP : NProg NK :=
  .seq (.prim (.dup NX VALT (by decide))) (.seq (.prim (.inc VALT))
    (.seq (nmvAll TTs ve_W (by decide)) (ve_loop TTs CNT VALT VALT ve_out_TTs ve_out_CNT ve_out_VALT)))

def valCost (j cap N : Nat) (tt : List (Nat × Nat)) : Nat :=
  1000 * (2 + N + tt.length + (valTable j cap N tt).sum + (cntTable j cap N tt).sum) ^ 3

theorem valTableP_runs (j cap N : Nat) (S : Lists NK) {tt : List (Nat × Nat)} (hw : TTWF tt)
    (hT : S TTs = encPairs tt) (hN : S NTT = [tt.length]) (hcnt : S CNT = cntTable j cap N tt) (hX : S NX = [N])
    (hV : S VALT = []) (hs : ScratchEmpty S) :
    NRuns valTableP S (S.set VALT (valTable j cap N tt)) (valCost j cap N tt) := by
  let f := valT j cap N tt
  let M := 2 + N + tt.length + (valTable j cap N tt).sum + (cntTable j cap N tt).sum
  have hW : S ve_W = [] := hs ve_W (by decide) (by decide)
  have x₁ := nruns_dup NX VALT (by decide) S (l := []) (v := N) (by rw [hX]; rfl)
  rw [hV, List.nil_append] at x₁
  have x₂ := nruns_inc VALT (S.set VALT [N]) (l := []) (v := N) (by rw [Lists.set_same]; rfl)
  rw [Lists.set_set_u] at x₂
  have x₃ := nruns_mvAll TTs ve_W (by decide) (S.set VALT ([] ++ [N + 1]))
  have e₀ : (((S.set VALT ([] ++ [N + 1])).set ve_W ((S.set VALT ([] ++ [N + 1])) ve_W ++
      ((S.set VALT ([] ++ [N + 1])) TTs).reverse)).set TTs []) = ve_st S TTs VALT tt f 0 := by
    have hf0 : f 0 = N + 1 := by simp only [f]; rw [valT]
    rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide), hW, hT]
    simp only [ve_st, List.take_zero, List.drop_zero]
    funext z
    simp only [Lists.set]
    by_cases h₁ : z = VALT
    · subst h₁; simp (config := {decide := true}) [ve_tab, hf0]
    by_cases h₂ : z = ve_W
    · subst h₂; simp (config := {decide := true})
    by_cases h₃ : z = TTs
    · subst h₃; simp (config := {decide := true}) [encPairs]
    simp [h₁, h₂, h₃]
  rw [e₀, Lists.set_ne _ _ (by decide), hT, encPairs_length] at x₃
  have hM2 : 2 ≤ M := by simp only [M]; omega
  have hLM : tt.length ≤ M := by simp only [M]; omega
  have x₄ := ve_loop_runs TTs CNT VALT VALT ve_out_TTs ve_out_CNT ve_out_VALT ve_out_VALT (by decide) (by decide)
    (by decide) S (ve_clean_of hs) tt f (30 * (M * M)) (fun m hm => by
      have hab := hw.2 m hm
      have hC : ve_st S TTs VALT tt f m CNT = cntTable j cap N tt := by
        simp only [ve_st]; rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide),
          Lists.set_ne _ _ (by decide), hcnt]
      have hVm : ve_st S TTs VALT tt f m VALT = ve_tab f m := by simp only [ve_st, Lists.set_same]
      have hp : tt[m].1 < (ve_st S TTs VALT tt f m CNT).length := by rw [hC, ve_cnt_length]; omega
      have hq : tt[m].2 < (ve_st S TTs VALT tt f m VALT).length := by rw [hVm, ve_tab_length]; omega
      refine ⟨hp, hq, ?_⟩
      have gx : (ve_st S TTs VALT tt f m CNT)[tt[m].1] = (rowsT j cap N tt tt[m].1).length := by
        simp only [hC]; exact ve_cnt_get _ _
      have gy : (ve_st S TTs VALT tt f m VALT)[tt[m].2] = f tt[m].2 := by
        simp only [hVm]; exact ve_tab_get _ _ _ _
      rw [gx, gy]
      refine ⟨(ve_valT_succ hw m hm).symm, ?_⟩
      have bx : (rowsT j cap N tt tt[m].1).length ≤ M := by
        have := ve_get_le_sum (cntTable j cap N tt) tt[m].1 (by rw [ve_cnt_length]; omega)
        rw [ve_cnt_get] at this
        simp only [M]; omega
      have by' : f tt[m].2 ≤ M := by
        have := ve_get_le_sum (valTable j cap N tt) tt[m].2 (by simp [valTable, typeTable]; omega)
        simp only [valTable, typeTable, List.getElem_map, List.getElem_range] at this
        simp only [M, f, valTable, typeTable] at this ⊢; omega
      rw [hC, hVm, ve_cnt_length, ve_tab_length]
      exact ve_round_le hM2 (by omega) (by omega) (by omega) (by omega) bx by')
  have e₁ : ve_st S TTs VALT tt f tt.length = S.set VALT (valTable j cap N tt) := by
    simp only [ve_st, List.take_length, List.drop_length]
    rw [← hT]
    have : (encPairs ([] : List (Nat × Nat))).reverse = S ve_W := by rw [hW]; rfl
    rw [this, Lists.set_get_self, Lists.set_get_self]
    rfl
  rw [e₁] at x₄
  refine (x₁.seq (x₂.seq (x₃.seq x₄))).mono ?_
  have := ve_total_le (A := 2) hM2 hLM (by omega)
  have hc : valCost j cap N tt = 1000 * M ^ 3 := rfl
  rw [hc]
  omega

/-! ## The table of environment counts

The requested bound `1000 * (2 + ct.length + (envTable …).sum + (cntTable …).sum) ^ 3` does not hold for any
program: reading entry `t` of `CNT` needs about `tt.length - t` steps (only the tops of stacks are visible), and
`tt.length` is not bounded by that expression (take `ct = [(0, 0)]` and `tt` long, with all counts but entry `0`
zero). The bound below adds `tt.length`.
-/

/-- Build `envTable` on `ENVT`: push `1`, then one round per context entry. -/
def envTableP : NProg NK :=
  .seq (npushC ENVT 1)
    (.seq (nmvAll CTs ve_W (by decide)) (ve_loop CTs ENVT CNT ENVT ve_out_CTs ve_out_ENVT ve_out_CNT))

/-- The cost of `envTableP`, with the length of the arrow table. -/
def envCostL (j cap N : Nat) (tt ct : List (Nat × Nat)) : Nat :=
  1000 * (2 + tt.length + ct.length + (envTable j cap N tt ct).sum + (cntTable j cap N tt).sum) ^ 3

theorem envTableP_runsL (j cap N : Nat) (S : Lists NK) {tt ct : List (Nat × Nat)} (hc : CTWF tt ct)
    (hC : S CTs = encPairs ct) (hN : S NCT = [ct.length]) (hcnt : S CNT = cntTable j cap N tt)
    (hE : S ENVT = []) (hs : ScratchEmpty S) :
    NRuns envTableP S (S.set ENVT (envTable j cap N tt ct)) (envCostL j cap N tt ct) := by
  let f := envT j cap N tt ct
  let M := 2 + tt.length + ct.length + (envTable j cap N tt ct).sum + (cntTable j cap N tt).sum
  have hW : S ve_W = [] := hs ve_W (by decide) (by decide)
  have x₁ := nruns_pushC ENVT S 1
  rw [hE, List.nil_append] at x₁
  have x₃ := nruns_mvAll CTs ve_W (by decide) (S.set ENVT [1])
  have e₀ : (((S.set ENVT [1]).set ve_W ((S.set ENVT [1]) ve_W ++
      ((S.set ENVT [1]) CTs).reverse)).set CTs []) = ve_st S CTs ENVT ct f 0 := by
    have hf0 : f 0 = 1 := by simp only [f]; rw [envT]
    rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide), hW, hC]
    simp only [ve_st, List.take_zero, List.drop_zero]
    funext z
    simp only [Lists.set]
    by_cases h₁ : z = ENVT
    · subst h₁; simp (config := {decide := true}) [ve_tab, hf0]
    by_cases h₂ : z = ve_W
    · subst h₂; simp (config := {decide := true})
    by_cases h₃ : z = CTs
    · subst h₃; simp (config := {decide := true}) [encPairs]
    simp [h₁, h₂, h₃]
  rw [e₀, Lists.set_ne _ _ (by decide), hC, encPairs_length] at x₃
  have hM2 : 2 ≤ M := by simp only [M]; omega
  have hLM : ct.length ≤ M := by simp only [M]; omega
  have x₄ := ve_loop_runs CTs ENVT CNT ENVT ve_out_CTs ve_out_ENVT ve_out_CNT ve_out_ENVT (by decide) (by decide)
    (by decide) S (ve_clean_of hs) ct f (30 * (M * M)) (fun m hm => by
      have hpt := hc m hm
      have hCm : ve_st S CTs ENVT ct f m CNT = cntTable j cap N tt := by
        simp only [ve_st]; rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide),
          Lists.set_ne _ _ (by decide), hcnt]
      have hEm : ve_st S CTs ENVT ct f m ENVT = ve_tab f m := by simp only [ve_st, Lists.set_same]
      have hp : ct[m].1 < (ve_st S CTs ENVT ct f m ENVT).length := by rw [hEm, ve_tab_length]; omega
      have hq : ct[m].2 < (ve_st S CTs ENVT ct f m CNT).length := by rw [hCm, ve_cnt_length]; omega
      refine ⟨hp, hq, ?_⟩
      have gx : (ve_st S CTs ENVT ct f m ENVT)[ct[m].1] = f ct[m].1 := by
        simp only [hEm]; exact ve_tab_get _ _ _ _
      have gy : (ve_st S CTs ENVT ct f m CNT)[ct[m].2] = (rowsT j cap N tt ct[m].2).length := by
        simp only [hCm]; exact ve_cnt_get _ _
      rw [gx, gy]
      refine ⟨(ve_envT_succ hc m hm).symm, ?_⟩
      have by' : (rowsT j cap N tt ct[m].2).length ≤ M := by
        have := ve_get_le_sum (cntTable j cap N tt) ct[m].2 (by rw [ve_cnt_length]; omega)
        rw [ve_cnt_get] at this
        simp only [M]; omega
      have bx : f ct[m].1 ≤ M := by
        have := ve_get_le_sum (envTable j cap N tt ct) ct[m].1 (by simp [envTable]; omega)
        simp only [envTable, List.getElem_map, List.getElem_range] at this
        simp only [M, f, envTable] at this ⊢; omega
      rw [hCm, hEm, ve_cnt_length, ve_tab_length]
      exact ve_round_le hM2 (by omega) (by omega) (by omega) (by omega) bx by')
  have e₁ : ve_st S CTs ENVT ct f ct.length = S.set ENVT (envTable j cap N tt ct) := by
    simp only [ve_st, List.take_length, List.drop_length]
    rw [← hC]
    have : (encPairs ([] : List (Nat × Nat))).reverse = S ve_W := by rw [hW]; rfl
    rw [this, Lists.set_get_self, Lists.set_get_self]
    rfl
  rw [e₁] at x₄
  refine (x₁.seq (x₃.seq x₄)).mono ?_
  have := ve_total_le (A := 2) hM2 hLM (by omega)
  have hc' : envCostL j cap N tt ct = 1000 * M ^ 3 := rfl
  rw [hc']
  omega

end Shallot.MacroPeg.Mach
