import MacroPeg.HigherOrder.Mach.EvalTables
import MacroPeg.HigherOrder.Mach.StepSimple
import MacroPeg.HigherOrder.Mach.EvalStacks

/-!
# The order and size tables on stacks

`ordTableP` builds the order table (`ordNum` of every type number) on `ORD`, `sizeTableP` the capped size table
(`sizeNum`) on `SZ`. Both stream the arrow table `TTs` through a scratch stack (restoring it on the way) and compute
entry `k + 1` from the entries of its two components, read back from the table being built (`peekAt`).
-/

namespace Shallot.MacroPeg.Mach

open Complexity

/-- The order table: entry `k` is `ordNum tt k`, for `k ≤ tt.length`. -/
def ordTable (tt : List (Nat × Nat)) : List Nat := (List.range (tt.length + 1)).map (ordNum tt)
/-- The size table, capped at `cap`. -/
def sizeTable (cap : Nat) (tt : List (Nat × Nat)) : List Nat := (List.range (tt.length + 1)).map (sizeNum cap tt)

/-! ## Scratch stacks -/

/-- The arrow table, reversed (its first entry on top). -/
abbrev ot_W : Fin NK := 18
abbrev ot_CA : Fin NK := 19
abbrev ot_CB : Fin NK := 20
abbrev ot_OA : Fin NK := 21
abbrev ot_OB : Fin NK := 22
/-- Scratch of `peekAt`. -/
abbrev ot_T : Fin NK := 23
abbrev ot_t : Fin NK := 24
abbrev ot_u : Fin NK := 25
abbrev ot_g : Fin NK := 26
/-- The result of a comparison. -/
abbrev ot_F : Fin NK := 27

/-! ## Facts about the numbers -/

theorem ot_ordNum_le (tt : List (Nat × Nat)) : ∀ k, ordNum tt k ≤ k
  | 0 => by rw [ordNum]; exact Nat.le_refl 0
  | k + 1 => by
    rw [ordNum]
    split
    · rename_i a b _
      split
      · rename_i hab
        have h₁ := ot_ordNum_le tt a
        have h₂ := ot_ordNum_le tt b
        omega
      · omega
    · omega
termination_by k => k
decreasing_by all_goals omega

theorem ot_sizeNum_le (cap : Nat) (tt : List (Nat × Nat)) (k : Nat) : sizeNum cap tt k ≤ cap + 1 := by
  cases k with
  | zero => rw [sizeNum]; omega
  | succ k =>
    rw [sizeNum]
    split
    · split
      · exact Nat.le_trans (Nat.min_le_left _ _) (by omega)
      · omega
    · omega

theorem ot_ordNum_succ {tt : List (Nat × Nat)} (hw : TTWF tt) (k : Nat) (hk : k < tt.length) :
    ordNum tt (k + 1) = max (ordNum tt tt[k].1 + 1) (ordNum tt tt[k].2) := by
  have hab := hw.2 k hk
  rw [ordNum]
  simp only [List.getElem?_eq_getElem hk]
  rw [if_pos hab]

theorem ot_sizeNum_succ {cap : Nat} {tt : List (Nat × Nat)} (hw : TTWF tt) (k : Nat) (hk : k < tt.length) :
    sizeNum cap tt (k + 1) = min cap (sizeNum cap tt tt[k].1 + sizeNum cap tt tt[k].2 + 1) := by
  have hab := hw.2 k hk
  rw [sizeNum]
  simp only [List.getElem?_eq_getElem hk]
  rw [if_pos hab]

/-! ## Lists -/

theorem ot_encPairs_take {tt : List (Nat × Nat)} {m : Nat} (hm : m < tt.length) :
    encPairs (tt.take (m + 1)) = encPairs (tt.take m) ++ [tt[m].1, tt[m].2] := by
  rw [List.take_succ_eq_append_getElem hm]; simp only [encPairs, List.flatMap_append]; rfl

theorem ot_encPairs_drop {tt : List (Nat × Nat)} {m : Nat} (hm : m < tt.length) :
    (encPairs (tt.drop m)).reverse = (encPairs (tt.drop (m + 1))).reverse ++ [tt[m].2, tt[m].1] := by
  rw [List.drop_eq_getElem_cons hm]; simp only [encPairs, List.flatMap_cons]; simp

/-- The first `m + 1` entries of a table. -/
def ot_tab (g : Nat → Nat) (m : Nat) : List Nat := (List.range (m + 1)).map g

theorem ot_tab_succ (g : Nat → Nat) (m : Nat) : ot_tab g (m + 1) = ot_tab g m ++ [g (m + 1)] := by
  simp only [ot_tab]; rw [List.range_succ, List.map_append]; rfl

theorem ot_tab_length (g : Nat → Nat) (m : Nat) : (ot_tab g m).length = m + 1 := by simp [ot_tab]

theorem ot_tab_get (g : Nat → Nat) (m a : Nat) (h : a < (ot_tab g m).length) : (ot_tab g m)[a] = g a := by
  simp [ot_tab]


/-! ## The states while building a table -/

/-- The stacks while building table `D`: the named stacks given, the rest as in `S`. -/
def ot_st (S : Lists NK) (D : Fin NK) (tts w ca cb oa ob d : List Nat) : Lists NK := fun i =>
  if i = D then d else if i = TTs then tts else if i = ot_W then w else if i = ot_CA then ca else
  if i = ot_CB then cb else if i = ot_OA then oa else if i = ot_OB then ob else S i

section St

variable {S : Lists NK} {D : Fin NK} {tts w ca cb oa ob d : List Nat}

theorem ot_ne {D i : Fin NK} (hD : 34 ≤ D.val) (hi : i.val < 34) : i ≠ D := fun h => by
  rw [h] at hi; omega

theorem ot_st_D : ot_st S D tts w ca cb oa ob d D = d := by simp [ot_st]

theorem ot_ne' {D i : Fin NK} (hD : 34 ≤ D.val) (hi : i.val < 34) : D ≠ i := (ot_ne hD hi).symm

theorem ot_st_other {i : Fin NK} (h₁ : i ≠ D) (h₂ : i.val ≠ 6) (h₃ : i.val < 18 ∨ 22 < i.val) :
    ot_st S D tts w ca cb oa ob d i = S i := by
  have n₂ : i ≠ TTs := fun e => h₂ (by rw [e]; rfl)
  have n₃ : i ≠ ot_W := fun e => by subst e; exact absurd h₃ (by decide)
  have n₄ : i ≠ ot_CA := fun e => by subst e; exact absurd h₃ (by decide)
  have n₅ : i ≠ ot_CB := fun e => by subst e; exact absurd h₃ (by decide)
  have n₆ : i ≠ ot_OA := fun e => by subst e; exact absurd h₃ (by decide)
  have n₇ : i ≠ ot_OB := fun e => by subst e; exact absurd h₃ (by decide)
  simp [ot_st, h₁, n₂, n₃, n₄, n₅, n₆, n₇]

theorem ot_st_self : ot_st S D (S TTs) (S ot_W) (S ot_CA) (S ot_CB) (S ot_OA) (S ot_OB) (S D) = S := by
  funext i
  simp only [ot_st]
  repeat' split
  all_goals (subst_vars; rfl)

theorem ot_st_TTs (hD : 34 ≤ D.val) : ot_st S D tts w ca cb oa ob d TTs = tts := by
  simp (config := { decide := true }) [ot_st, ot_ne hD (by decide : (TTs : Fin NK).val < 34)]

theorem ot_st_W (hD : 34 ≤ D.val) : ot_st S D tts w ca cb oa ob d ot_W = w := by
  simp (config := { decide := true }) [ot_st, ot_ne hD (by decide : (ot_W : Fin NK).val < 34)]

theorem ot_st_CA (hD : 34 ≤ D.val) : ot_st S D tts w ca cb oa ob d ot_CA = ca := by
  simp (config := { decide := true }) [ot_st, ot_ne hD (by decide : (ot_CA : Fin NK).val < 34)]

theorem ot_st_CB (hD : 34 ≤ D.val) : ot_st S D tts w ca cb oa ob d ot_CB = cb := by
  simp (config := { decide := true }) [ot_st, ot_ne hD (by decide : (ot_CB : Fin NK).val < 34)]

theorem ot_st_OA (hD : 34 ≤ D.val) : ot_st S D tts w ca cb oa ob d ot_OA = oa := by
  simp (config := { decide := true }) [ot_st, ot_ne hD (by decide : (ot_OA : Fin NK).val < 34)]

theorem ot_st_OB (hD : 34 ≤ D.val) : ot_st S D tts w ca cb oa ob d ot_OB = ob := by
  simp (config := { decide := true }) [ot_st, ot_ne hD (by decide : (ot_OB : Fin NK).val < 34)]

theorem ot_st_set_TTs (hD : 34 ≤ D.val) (v : List Nat) :
    (ot_st S D tts w ca cb oa ob d).set TTs v = ot_st S D v w ca cb oa ob d := by
  funext i; by_cases h : i = TTs
  · subst h; simp (config := { decide := true }) [Lists.set, ot_st, ot_ne hD (by decide : (TTs : Fin NK).val < 34)]
  · simp [Lists.set, ot_st, h]

theorem ot_st_set_W (hD : 34 ≤ D.val) (v : List Nat) :
    (ot_st S D tts w ca cb oa ob d).set ot_W v = ot_st S D tts v ca cb oa ob d := by
  funext i; by_cases h : i = ot_W
  · subst h; simp (config := { decide := true }) [Lists.set, ot_st, ot_ne hD (by decide : (ot_W : Fin NK).val < 34)]
  · simp [Lists.set, ot_st, h]

theorem ot_st_set_CA (hD : 34 ≤ D.val) (v : List Nat) :
    (ot_st S D tts w ca cb oa ob d).set ot_CA v = ot_st S D tts w v cb oa ob d := by
  funext i; by_cases h : i = ot_CA
  · subst h; simp (config := { decide := true }) [Lists.set, ot_st, ot_ne hD (by decide : (ot_CA : Fin NK).val < 34)]
  · simp [Lists.set, ot_st, h]

theorem ot_st_set_CB (hD : 34 ≤ D.val) (v : List Nat) :
    (ot_st S D tts w ca cb oa ob d).set ot_CB v = ot_st S D tts w ca v oa ob d := by
  funext i; by_cases h : i = ot_CB
  · subst h; simp (config := { decide := true }) [Lists.set, ot_st, ot_ne hD (by decide : (ot_CB : Fin NK).val < 34)]
  · simp [Lists.set, ot_st, h]

theorem ot_st_set_OA (hD : 34 ≤ D.val) (v : List Nat) :
    (ot_st S D tts w ca cb oa ob d).set ot_OA v = ot_st S D tts w ca cb v ob d := by
  funext i; by_cases h : i = ot_OA
  · subst h; simp (config := { decide := true }) [Lists.set, ot_st, ot_ne hD (by decide : (ot_OA : Fin NK).val < 34)]
  · simp [Lists.set, ot_st, h]

theorem ot_st_set_OB (hD : 34 ≤ D.val) (v : List Nat) :
    (ot_st S D tts w ca cb oa ob d).set ot_OB v = ot_st S D tts w ca cb oa v d := by
  funext i; by_cases h : i = ot_OB
  · subst h; simp (config := { decide := true }) [Lists.set, ot_st, ot_ne hD (by decide : (ot_OB : Fin NK).val < 34)]
  · simp [Lists.set, ot_st, h]

theorem ot_st_set_D (v : List Nat) :
    (ot_st S D tts w ca cb oa ob d).set D v = ot_st S D tts w ca cb oa ob v := by
  funext i; by_cases h : i = D <;> simp [Lists.set, ot_st, h]

end St

/-! ## Building a table -/

/-- One entry: take the next arrow `(a, b)` off `ot_W` (restoring it on `TTs`), read entries `a` and `b` of the table
`D` onto `ot_OA`, `ot_OB`, and combine them (`comb` pushes the new entry). -/
def ot_body (D : Fin NK) (hDT : D ≠ ot_T) (comb : NProg NK) : NProg NK :=
  .seq (.prim (.dup ot_W TTs (by decide))) (.seq (nmv ot_W ot_CA (by decide))
    (.seq (.prim (.dup ot_W TTs (by decide))) (.seq (nmv ot_W ot_CB (by decide))
      (.seq (peekAt D ot_T ot_CA ot_OA hDT (by decide)) (.seq (peekAt D ot_T ot_CB ot_OB hDT (by decide)) comb)))))

/-- Push entry `0` (the constant `c`), move the arrows to `ot_W`, and build entry after entry. -/
def ot_build (D : Fin NK) (hDT : D ≠ ot_T) (c : Nat) (comb : NProg NK) : NProg NK :=
  .seq (npushC D c) (.seq (nmvAll TTs ot_W (by decide)) (.loop ot_W .nonempty (ot_body D hDT comb)))

theorem ot_nodup {D : Fin NK} (hD : 34 ≤ D.val) (c o : Fin NK) (hc : c.val < 34) (ho : o.val < 34)
    (h : [ot_T, c, o].Nodup) : [D, ot_T, c, o].Nodup := by
  refine List.nodup_cons.2 ⟨?_, h⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨ot_ne' hD (by decide), ot_ne' hD hc, ot_ne' hD ho⟩

theorem ot_body_runs (D : Fin NK) (hDT : D ≠ ot_T) (hD : 34 ≤ D.val) (comb : NProg NK) (S : Lists NK)
    (hTe : S ot_T = []) (P R tb : List Nat) (a b z C : Nat) (ha : a < tb.length) (hb : b < tb.length)
    (hcomb : NRuns comb (ot_st S D (P ++ [a, b]) R [] [] [tb[a]] [tb[b]] tb)
      (ot_st S D (P ++ [a, b]) R [] [] [] [] (tb ++ [z])) C) :
    NRuns (ot_body D hDT comb) (ot_st S D P (R ++ [b, a]) [] [] [] [] tb)
      (ot_st S D (P ++ [a, b]) R [] [] [] [] (tb ++ [z])) (12 * tb.length + 4 * a + 4 * b + 18 + C) := by
  have x₁ := nruns_dup ot_W TTs (by decide) (ot_st S D P (R ++ [b, a]) [] [] [] [] tb) (l := R ++ [b]) (v := a)
    (by rw [ot_st_W hD]; simp)
  rw [ot_st_TTs hD, ot_st_set_TTs hD] at x₁
  have x₂ := nruns_mv ot_W ot_CA (by decide) (ot_st S D (P ++ [a]) (R ++ [b, a]) [] [] [] [] tb) (l := R ++ [b])
    (v := a) (by rw [ot_st_W hD]; simp)
  rw [ot_st_CA hD, ot_st_set_CA hD, ot_st_set_W hD] at x₂
  have x₃ := nruns_dup ot_W TTs (by decide) (ot_st S D (P ++ [a]) (R ++ [b]) [a] [] [] [] tb) (l := R) (v := b)
    (by rw [ot_st_W hD])
  rw [ot_st_TTs hD, ot_st_set_TTs hD] at x₃
  have x₄ := nruns_mv ot_W ot_CB (by decide) (ot_st S D (P ++ [a] ++ [b]) (R ++ [b]) [a] [] [] [] tb) (l := R)
    (v := b) (by rw [ot_st_W hD])
  rw [ot_st_CB hD, ot_st_set_CB hD, ot_st_set_W hD] at x₄
  have e : P ++ [a] ++ [b] = P ++ [a, b] := by simp
  rw [e] at x₃ x₄
  have hT : ∀ tts w ca cb oa ob, ot_st S D tts w ca cb oa ob tb ot_T = [] := fun _ _ _ _ _ _ => by
    rw [ot_st_other (ot_ne hD (by decide)) (by decide) (by decide)]; exact hTe
  have x₅ := nruns_peekAt D ot_T ot_CA ot_OA hDT (by decide) (ot_nodup hD _ _ (by decide) (by decide) (by decide))
    (ot_st S D (P ++ [a, b]) R [a] [b] [] [] tb) (hT _ _ _ _ _ _) (lc := []) (k := a) (by rw [ot_st_CA hD]; rfl)
    (by rw [ot_st_D]; exact ha)
  simp only [ot_st_D, ot_st_OA hD, ot_st_set_CA hD, ot_st_set_OA hD, List.nil_append] at x₅
  have x₆ := nruns_peekAt D ot_T ot_CB ot_OB hDT (by decide) (ot_nodup hD _ _ (by decide) (by decide) (by decide))
    (ot_st S D (P ++ [a, b]) R [] [b] [tb[a]] [] tb) (hT _ _ _ _ _ _) (lc := []) (k := b)
    (by rw [ot_st_CB hD]; rfl) (by rw [ot_st_D]; exact hb)
  simp only [ot_st_D, ot_st_OB hD, ot_st_set_CB hD, ot_st_set_OB hD, List.nil_append] at x₆
  have := (x₁.seq (x₂.seq (x₃.seq (x₄.seq (x₅.seq (x₆.seq hcomb))))))
  exact this.mono (by omega)

/-- **Building a table** `D` whose entry `k + 1` is `f` of the entries of the components of arrow `k`. -/
theorem ot_build_runs (D : Fin NK) (hDT : D ≠ ot_T) (hD : 34 ≤ D.val) (hDC : D ≠ CAP) (c : Nat) (comb : NProg NK)
    (g : Nat → Nat) (f : Nat → Nat → Nat) (M C : Nat) (S : Lists NK) {tt : List (Nat × Nat)} (hw : TTWF tt)
    (hT : S TTs = encPairs tt) (hDe : S D = []) (hs : ScratchEmpty S) (hg0 : g 0 = c)
    (hg : ∀ k (h : k < tt.length), g (k + 1) = f (g tt[k].1) (g tt[k].2)) (hM : ∀ k, k ≤ tt.length → g k ≤ M)
    (hcomb : ∀ (S' : Lists NK) (x y : Nat), x ≤ M → y ≤ M → S' ot_OA = [x] → S' ot_OB = [y] → S' ot_F = [] →
      S' CAP = S CAP → NRuns comb S' (((S'.set ot_OA []).set ot_OB []).set D (S' D ++ [f x y])) C) :
    NRuns (ot_build D hDT c comb) S (S.set D ((List.range (tt.length + 1)).map g))
      (c + 6 * tt.length + 4 + tt.length * (20 * tt.length + 19 + C)) := by
  have hDT' : D ≠ TTs := ot_ne' hD (by decide)
  have hS : S = ot_st S D (encPairs tt) [] [] [] [] [] [] := by
    have h := (ot_st_self (S := S) (D := D)).symm
    rwa [hT, hDe, hs ot_W (by decide) (by decide), hs ot_CA (by decide) (by decide), hs ot_CB (by decide) (by decide),
      hs ot_OA (by decide) (by decide), hs ot_OB (by decide) (by decide)] at h
  -- the start
  have x₁ := nruns_pushC D S c
  rw [hDe, List.nil_append] at x₁
  have e₁ : S.set D [c] = ot_st S D (encPairs tt) [] [] [] [] [] [c] := by
    conv => lhs; rw [hS]
    rw [ot_st_set_D]
  rw [e₁] at x₁
  have x₂ := nruns_mvAll TTs ot_W (by decide) (ot_st S D (encPairs tt) [] [] [] [] [] [c])
  rw [ot_st_TTs hD, ot_st_W hD, ot_st_set_W hD, ot_st_set_TTs hD, List.nil_append, encPairs_length] at x₂
  -- the loop
  let n := tt.length
  let F : Nat → Lists NK := fun m =>
    ot_st S D (encPairs (tt.take m)) (encPairs (tt.drop m)).reverse [] [] [] [] (ot_tab g m)
  have hF0 : F 0 = ot_st S D [] (encPairs tt).reverse [] [] [] [] [c] := by
    simp only [F, List.take_zero, List.drop_zero, ot_tab, Nat.zero_add, List.range_one, List.map_cons,
      List.map_nil, hg0]
    rfl
  have hFn : F n = S.set D ((List.range (tt.length + 1)).map g) := by
    simp only [F, n, List.take_length, List.drop_length]
    conv => rhs; rw [hS]
    rw [ot_st_set_D]; rfl
  have hl := nruns_family_const (i := ot_W) (c := .nonempty) (p := ot_body D hDT comb) F n
    (20 * n + 18 + C)
    (fun m hm => by
      simp only [F]; rw [ot_st_W hD, ot_encPairs_drop hm]
      exact eval_nonempty_ne (by simp))
    (by simp only [F, n]; rw [ot_st_W hD, List.drop_length]; rfl)
    (fun m hm => by
      have hab := hw.2 m hm
      have hl : (ot_tab g m).length = m + 1 := ot_tab_length g m
      have hb := ot_body_runs D hDT hD comb S (hs ot_T (by decide) (by decide)) (encPairs (tt.take m))
        (encPairs (tt.drop (m + 1))).reverse (ot_tab g m) tt[m].1 tt[m].2 (g (m + 1)) C (by omega) (by omega)
        (by
          have hc := hcomb (ot_st S D (encPairs (tt.take m) ++ [tt[m].1, tt[m].2]) (encPairs (tt.drop (m + 1))).reverse
            [] [] [(ot_tab g m)[tt[m].1]'(by omega)] [(ot_tab g m)[tt[m].2]'(by omega)] (ot_tab g m))
            ((ot_tab g m)[tt[m].1]'(by omega)) ((ot_tab g m)[tt[m].2]'(by omega))
            (by rw [ot_tab_get]; exact hM _ (by omega)) (by rw [ot_tab_get]; exact hM _ (by omega))
            (ot_st_OA hD) (ot_st_OB hD)
            (by rw [ot_st_other (ot_ne hD (by decide)) (by decide) (by decide)]; exact hs ot_F (by decide) (by decide))
            (ot_st_other (Ne.symm hDC) (by decide) (by decide))
          rw [ot_st_set_OA hD, ot_st_set_OB hD, ot_st_D, ot_st_set_D] at hc
          rw [hg m hm]
          simpa only [ot_tab_get] using hc)
      have eF : F (m + 1) = ot_st S D (encPairs (tt.take m) ++ [tt[m].1, tt[m].2]) (encPairs (tt.drop (m + 1))).reverse
          [] [] [] [] (ot_tab g m ++ [g (m + 1)]) := by
        simp only [F]; rw [ot_encPairs_take hm, ot_tab_succ]
      have eF0 : F m = ot_st S D (encPairs (tt.take m)) ((encPairs (tt.drop (m + 1))).reverse ++ [tt[m].2, tt[m].1])
          [] [] [] [] (ot_tab g m) := by
        simp only [F]; rw [ot_encPairs_drop hm]
      rw [eF, eF0]
      refine hb.mono ?_
      rw [hl]
      have : m + 1 ≤ n := hm
      omega)
  rw [hF0, hFn] at hl
  refine (x₁.seq (x₂.seq hl)).mono ?_
  simp only [n]
  rw [show 20 * tt.length + 18 + C + 1 = 20 * tt.length + 19 + C by omega]
  omega

/-! ## Combining two entries -/

/-- Equalities between stacks updated at a few named places. -/
macro "ot_lists" : tactic =>
  `(tactic| (funext i; simp only [Lists.set]; repeat' split
             all_goals (try subst_vars)
             all_goals (simp_all (config := { decide := true }))))

/-- Push the top of `ot_OA` on `D` if the comparison result on `ot_F` is `0`, else the top of `ot_OB`; then clear the
three stacks. -/
def ot_tail (D : Fin NK) (hA : ot_OA ≠ D) (hB : ot_OB ≠ D) : NProg NK :=
  .seq (.ite ot_F .zero (.prim (.dup ot_OA D hA)) (.prim (.dup ot_OB D hB)))
    (.seq (.prim (.pop ot_F)) (.seq (.prim (.pop ot_OA)) (.prim (.pop ot_OB))))

theorem ot_tail_runs (D : Fin NK) (hA : ot_OA ≠ D) (hB : ot_OB ≠ D) (hF : ot_F ≠ D) (S : Lists NK) (p q r : Nat)
    (hp : S ot_OA = [p]) (hq : S ot_OB = [q]) (hr : S ot_F = [r]) :
    NRuns (ot_tail D hA hB) S ((((S.set ot_F []).set ot_OA []).set ot_OB []).set D (S D ++ [if r = 0 then p else q]))
      5 := by
  have finish : ∀ v, NRuns (.seq (.prim (.pop ot_F)) (.seq (.prim (.pop ot_OA)) (.prim (.pop ot_OB))))
      (S.set D (S D ++ [v])) ((((S.set ot_F []).set ot_OA []).set ot_OB []).set D (S D ++ [v])) 3 := by
    intro v
    have y₁ := nruns_pop ot_F (S.set D (S D ++ [v])) (l := []) (v := r) (by rw [Lists.set_ne _ _ hF]; exact hr)
    have y₂ := nruns_pop ot_OA ((S.set D (S D ++ [v])).set ot_F []) (l := []) (v := p)
      (by rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ hA]; exact hp)
    have y₃ := nruns_pop ot_OB (((S.set D (S D ++ [v])).set ot_F []).set ot_OA []) (l := []) (v := q)
      (by rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide), Lists.set_ne _ _ hB]; exact hq)
    have e : (((S.set D (S D ++ [v])).set ot_F []).set ot_OA []).set ot_OB [] =
        (((S.set ot_F []).set ot_OA []).set ot_OB []).set D (S D ++ [v]) := by
      rw [Lists.set_comm (Ne.symm hF), Lists.set_comm (Ne.symm hA), Lists.set_comm (Ne.symm hB)]
    rw [e] at y₃
    exact y₁.seq (y₂.seq y₃)
  by_cases h0 : r = 0
  · subst h0
    have y := nruns_dup ot_OA D hA S (l := []) (v := p) hp
    exact ((y.iteT (by rw [hr]; rfl)).seq (finish _)).mono (by omega)
  · have y := nruns_dup ot_OB D hB S (l := []) (v := q) hq
    rw [if_neg h0]
    exact ((y.iteF (by rw [hr]; obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩; rfl)).seq
      (finish _)).mono (by omega)

/-- Entry `max (x + 1) y` from the order entries `x`, `y` of the components. -/
def ot_ordComb : NProg NK :=
  .seq (.prim (.inc ot_OA)) (.seq (cmpTop ot_OB ot_OA ot_t ot_u ot_g ot_F (by decide) (by decide))
    (ot_tail ORD (by decide) (by decide)))

/-- The steps of `ot_ordComb` on entries at most `M`. -/
def ot_ordCost (M : Nat) : Nat := (2 * M + 2) * (2 * M + 6) + 26

theorem ot_ordComb_runs (S : Lists NK) (x y M : Nat) (hx : x ≤ M) (hy : y ≤ M) (hA : S ot_OA = [x])
    (hB : S ot_OB = [y]) (hF : S ot_F = []) :
    NRuns ot_ordComb S (((S.set ot_OA []).set ot_OB []).set ORD (S ORD ++ [max (x + 1) y])) (ot_ordCost M) := by
  have y₁ := nruns_inc ot_OA S (l := []) (v := x) (by rw [hA]; rfl)
  have y₂ := nruns_cmpTop ot_OB ot_OA ot_t ot_u ot_g ot_F (by decide) (by decide) (by decide)
    (S.set ot_OA ([] ++ [x + 1])) (li := []) (lj := []) (a := y) (b := x + 1)
    (by rw [Lists.set_ne _ _ (by decide)]; rw [hB]; rfl) (by rw [Lists.set_same])
  have y₃ := ot_tail_runs ORD (by decide) (by decide) (by decide)
    ((S.set ot_OA ([] ++ [x + 1])).set ot_F ((S.set ot_OA ([] ++ [x + 1])) ot_F ++ [cmpRes y (x + 1)]))
    (x + 1) y (cmpRes y (x + 1)) (by simp (config := { decide := true }) [Lists.set])
    (by simp (config := { decide := true }) [Lists.set, hB]) (by simp (config := { decide := true }) [Lists.set, hF])
  have hv : (if cmpRes y (x + 1) = 0 then x + 1 else y) = max (x + 1) y := by
    unfold cmpRes
    by_cases h₁ : y < x + 1 <;> by_cases h₂ : y = x + 1 <;> simp [h₁, h₂] <;> omega
  have e : ((((((S.set ot_OA ([] ++ [x + 1])).set ot_F ((S.set ot_OA ([] ++ [x + 1])) ot_F ++ [cmpRes y (x + 1)])).set
      ot_F []).set ot_OA []).set ot_OB []).set ORD (((S.set ot_OA ([] ++ [x + 1])).set ot_F
        ((S.set ot_OA ([] ++ [x + 1])) ot_F ++ [cmpRes y (x + 1)])) ORD ++ [max (x + 1) y])) =
      ((S.set ot_OA []).set ot_OB []).set ORD (S ORD ++ [max (x + 1) y]) := by
    ot_lists
  rw [hv, e] at y₃
  refine (y₁.seq (y₂.seq y₃)).mono ?_
  have : (y + (x + 1) + 1) * (2 * y + 6) ≤ (2 * M + 2) * (2 * M + 6) := Nat.mul_le_mul (by omega) (by omega)
  unfold ot_ordCost
  omega

/-- Entry `min cap (x + y + 1)` from the size entries `x`, `y` of the components (the cap on `CAP`). -/
def ot_sizeComb : NProg NK :=
  .seq (addTo ot_OB ot_OA) (.seq (.prim (.inc ot_OA)) (.seq (.prim (.dup CAP ot_OB (by decide)))
    (.seq (cmpTop ot_OA ot_OB ot_t ot_u ot_g ot_F (by decide) (by decide)) (ot_tail SZ (by decide) (by decide)))))

/-- The steps of `ot_sizeComb` on entries at most `M`. -/
def ot_sizeCost (M cap : Nat) : Nat := (2 * M + cap + 2) * (4 * M + 8) + 3 * M + 29

theorem ot_sizeComb_runs (S : Lists NK) (x y M cap : Nat) (hx : x ≤ M) (hy : y ≤ M) (hA : S ot_OA = [x])
    (hB : S ot_OB = [y]) (hF : S ot_F = []) (hC : S CAP = [cap]) :
    NRuns ot_sizeComb S (((S.set ot_OA []).set ot_OB []).set SZ (S SZ ++ [min cap (x + y + 1)]))
      (ot_sizeCost M cap) := by
  have y₁ := nruns_addTo ot_OB ot_OA (by decide) S (l := []) (l' := []) (a := y) (b := x) (by rw [hB]; rfl)
    (by rw [hA]; rfl)
  have y₂ := nruns_inc ot_OA ((S.set ot_OB []).set ot_OA ([] ++ [x + y])) (l := []) (v := x + y)
    (by rw [Lists.set_same])
  rw [Lists.set_set_u] at y₂
  have y₃ := nruns_dup CAP ot_OB (by decide) ((S.set ot_OB []).set ot_OA ([] ++ [x + y + 1])) (l := []) (v := cap)
    (by simp (config := { decide := true }) [Lists.set, hC])
  have y₄ := nruns_cmpTop ot_OA ot_OB ot_t ot_u ot_g ot_F (by decide) (by decide) (by decide)
    (((S.set ot_OB []).set ot_OA ([] ++ [x + y + 1])).set ot_OB
      (((S.set ot_OB []).set ot_OA ([] ++ [x + y + 1])) ot_OB ++ [cap]))
    (li := []) (lj := []) (a := x + y + 1) (b := cap)
    (by simp (config := { decide := true }) [Lists.set]) (by simp (config := { decide := true }) [Lists.set])
  have y₅ := ot_tail_runs SZ (by decide) (by decide) (by decide)
    ((((S.set ot_OB []).set ot_OA ([] ++ [x + y + 1])).set ot_OB
      (((S.set ot_OB []).set ot_OA ([] ++ [x + y + 1])) ot_OB ++ [cap])).set ot_F
      ((((S.set ot_OB []).set ot_OA ([] ++ [x + y + 1])).set ot_OB
      (((S.set ot_OB []).set ot_OA ([] ++ [x + y + 1])) ot_OB ++ [cap])) ot_F ++ [cmpRes (x + y + 1) cap]))
    (x + y + 1) cap (cmpRes (x + y + 1) cap) (by simp (config := { decide := true }) [Lists.set])
    (by simp (config := { decide := true }) [Lists.set]) (by simp (config := { decide := true }) [Lists.set, hF])
  have hv : (if cmpRes (x + y + 1) cap = 0 then x + y + 1 else cap) = min cap (x + y + 1) := by
    unfold cmpRes
    by_cases h₁ : x + y + 1 < cap <;> by_cases h₂ : x + y + 1 = cap <;> simp [h₁, h₂] <;> omega
  rw [hv] at y₅
  have e : ∀ T : Lists NK, T = (((S.set ot_OB []).set ot_OA ([] ++ [x + y + 1])).set ot_OB
      (((S.set ot_OB []).set ot_OA ([] ++ [x + y + 1])) ot_OB ++ [cap])) →
      ((((T.set ot_F (T ot_F ++ [cmpRes (x + y + 1) cap])).set ot_F []).set ot_OA []).set ot_OB []).set SZ
        ((T.set ot_F (T ot_F ++ [cmpRes (x + y + 1) cap])) SZ ++ [min cap (x + y + 1)]) =
      ((S.set ot_OA []).set ot_OB []).set SZ (S SZ ++ [min cap (x + y + 1)]) := by
    intro T hT; subst hT; ot_lists
  rw [e _ rfl] at y₅
  refine (y₁.seq (y₂.seq (y₃.seq (y₄.seq y₅)))).mono ?_
  have : (x + y + 1 + cap + 1) * (2 * (x + y + 1) + 6) ≤ (2 * M + cap + 2) * (4 * M + 8) :=
    Nat.mul_le_mul (by omega) (by omega)
  unfold ot_sizeCost
  omega

/-! ## The two tables -/

/-- A cubic bound on the steps of building a table. -/
theorem ot_cube (n N A c : Nat) (hn : n + 1 ≤ N) (hc : c ≤ 1) (hA : A ≤ 200 * N * N) :
    c + 6 * n + 4 + n * A ≤ 1000 * N * N * N := by
  have h₁ : n * A ≤ N * (200 * N * N) := Nat.mul_le_mul (by omega) hA
  have e₁ : N * (200 * N * N) = 200 * (N * N * N) := by
    rw [Nat.mul_assoc 200, Nat.mul_left_comm, Nat.mul_assoc N N N]
  have e₂ : 1000 * N * N * N = 1000 * (N * N * N) := by simp only [Nat.mul_assoc]
  have h₂ : N ≤ N * N * N := by
    have := Nat.mul_le_mul (Nat.mul_le_mul (show 1 ≤ N by omega) (show 1 ≤ N by omega)) (Nat.le_refl N)
    simpa using this
  rw [e₂]
  rw [e₁] at h₁
  generalize N * N * N = P at *
  omega

/-- The order table on `ORD`. -/
def ordTableP : NProg NK := ot_build ORD (by decide) 0 ot_ordComb

/-- The size table on `SZ`. -/
def sizeTableP : NProg NK := ot_build SZ (by decide) 1 ot_sizeComb

theorem ordTableP_runs (S : Lists NK) {tt : List (Nat × Nat)} (hw : TTWF tt) (hT : S TTs = encPairs tt)
    (hN : S NTT = [tt.length]) (hO : S ORD = []) (hs : ScratchEmpty S) :
    NRuns ordTableP S (S.set ORD (ordTable tt)) (1000 * (tt.length + 1) * (tt.length + 1) * (tt.length + 1)) := by
  have _ := hN -- the number of arrows is not needed: the loop runs until the streamed arrows are used up
  have h := ot_build_runs ORD (by decide) (by decide) (by decide) 0 ot_ordComb (ordNum tt)
    (fun x y => max (x + 1) y) tt.length (ot_ordCost tt.length) S hw hT hO hs (by rw [ordNum])
    (fun k hk => ot_ordNum_succ hw k hk) (fun k hk => Nat.le_trans (ot_ordNum_le tt k) hk)
    (fun S' x y hx hy hA hB hF _ => ot_ordComb_runs S' x y _ hx hy hA hB hF)
  refine h.mono (ot_cube _ _ _ _ (Nat.le_refl _) (by omega) ?_)
  clear h hw hT hN hO hs
  have h₁ : (2 * tt.length + 2) * (2 * tt.length + 6) ≤ (2 * (tt.length + 1)) * (6 * (tt.length + 1)) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e : (2 * (tt.length + 1)) * (6 * (tt.length + 1)) = 12 * ((tt.length + 1) * (tt.length + 1)) := by
    rw [Nat.mul_mul_mul_comm]
  have h₂ : tt.length + 1 ≤ (tt.length + 1) * (tt.length + 1) := Nat.le_mul_self _
  have e₂ : 200 * (tt.length + 1) * (tt.length + 1) = 200 * ((tt.length + 1) * (tt.length + 1)) := Nat.mul_assoc _ _ _
  unfold ot_ordCost
  rw [e₂]
  rw [e] at h₁
  generalize (tt.length + 1) * (tt.length + 1) = Q at *
  generalize (2 * tt.length + 2) * (2 * tt.length + 6) = R at *
  omega

theorem sizeTableP_runs (S : Lists NK) {tt : List (Nat × Nat)} {cap : Nat} (hw : TTWF tt)
    (hT : S TTs = encPairs tt) (hN : S NTT = [tt.length]) (hC : S CAP = [cap]) (hZ : S SZ = []) (hs : ScratchEmpty S) :
    NRuns sizeTableP S (S.set SZ (sizeTable cap tt))
      (1000 * (tt.length + cap + 1) * (tt.length + cap + 1) * (tt.length + cap + 1)) := by
  have _ := hN -- the number of arrows is not needed: the loop runs until the streamed arrows are used up
  have h := ot_build_runs SZ (by decide) (by decide) (by decide) 1 ot_sizeComb (sizeNum cap tt)
    (fun x y => min cap (x + y + 1)) (cap + 1) (ot_sizeCost (cap + 1) cap) S hw hT hZ hs (by rw [sizeNum])
    (fun k hk => ot_sizeNum_succ hw k hk) (fun k _ => ot_sizeNum_le cap tt k)
    (fun S' x y hx hy hA hB hF hC' => ot_sizeComb_runs S' x y _ cap hx hy hA hB hF (by rw [hC']; exact hC))
  refine h.mono (ot_cube _ _ _ _ (by omega) (Nat.le_refl _) ?_)
  clear h hw hT hN hC hZ hs
  have h₁ : (2 * (cap + 1) + cap + 2) * (4 * (cap + 1) + 8) ≤
      (4 * (tt.length + cap + 1)) * (12 * (tt.length + cap + 1)) := Nat.mul_le_mul (by omega) (by omega)
  have e : (4 * (tt.length + cap + 1)) * (12 * (tt.length + cap + 1)) =
      48 * ((tt.length + cap + 1) * (tt.length + cap + 1)) := by
    rw [Nat.mul_mul_mul_comm]
  have h₂ : tt.length + cap + 1 ≤ (tt.length + cap + 1) * (tt.length + cap + 1) := Nat.le_mul_self _
  have e₂ : 200 * (tt.length + cap + 1) * (tt.length + cap + 1) =
      200 * ((tt.length + cap + 1) * (tt.length + cap + 1)) := Nat.mul_assoc _ _ _
  unfold ot_sizeCost
  rw [e₂]
  rw [e] at h₁
  generalize (tt.length + cap + 1) * (tt.length + cap + 1) = Q at *
  omega

/-! ## The order check: scanning a stack unit by unit -/

/-- The stacks while scanning stack `X`: `X`, `ot_W`, `ot_CA`, `ot_CB` given, the rest as in `S`. -/
def ck_st (S : Lists NK) (X : Fin NK) (x w ca cb : List Nat) : Lists NK := fun i =>
  if i = X then x else if i = ot_W then w else if i = ot_CA then ca else if i = ot_CB then cb else S i

section Ck

variable {S : Lists NK} {X : Fin NK} {x w ca cb : List Nat}

theorem ck_ne {X i : Fin NK} (hX : X.val < 18) (hi : 18 ≤ i.val) : i ≠ X := fun h => by rw [h] at hi; omega

/-- Equality with a scanning state, stack by stack. -/
theorem ck_eq (hX : X.val < 18) {L : Lists NK} (h₁ : L X = x) (h₂ : L ot_W = w) (h₃ : L ot_CA = ca)
    (h₄ : L ot_CB = cb) (h₅ : ∀ i, i ≠ X → i ≠ ot_W → i ≠ ot_CA → i ≠ ot_CB → L i = S i) :
    L = ck_st S X x w ca cb := by
  funext i
  by_cases a : i = X
  · subst a; simp [ck_st, h₁]
  by_cases b : i = ot_W
  · subst b; simp [ck_st, ck_ne hX (by decide : 18 ≤ (ot_W : Fin NK).val), h₂]
  by_cases c : i = ot_CA
  · subst c; simp (config := { decide := true }) [ck_st, ck_ne hX (by decide : 18 ≤ (ot_CA : Fin NK).val), h₃]
  by_cases d : i = ot_CB
  · subst d; simp (config := { decide := true }) [ck_st, ck_ne hX (by decide : 18 ≤ (ot_CB : Fin NK).val), h₄]
  simp [ck_st, a, b, c, d, h₅ i a b c d]

theorem ck_X : ck_st S X x w ca cb X = x := by simp [ck_st]
theorem ck_W (hX : X.val < 18) : ck_st S X x w ca cb ot_W = w := by
  simp [ck_st, ck_ne hX (by decide : 18 ≤ (ot_W : Fin NK).val)]
theorem ck_CA (hX : X.val < 18) : ck_st S X x w ca cb ot_CA = ca := by
  simp (config := { decide := true }) [ck_st, ck_ne hX (by decide : 18 ≤ (ot_CA : Fin NK).val)]
theorem ck_CB (hX : X.val < 18) : ck_st S X x w ca cb ot_CB = cb := by
  simp (config := { decide := true }) [ck_st, ck_ne hX (by decide : 18 ≤ (ot_CB : Fin NK).val)]
theorem ck_other {i : Fin NK} (h₁ : i ≠ X) (h₂ : i ≠ ot_W) (h₃ : i ≠ ot_CA) (h₄ : i ≠ ot_CB) :
    ck_st S X x w ca cb i = S i := by
  simp [ck_st, h₁, h₂, h₃, h₄]

/-- Reading a stack of a scanning state at index `i` at least `21`. -/
theorem ck_hi (hX : X.val < 18) {i : Fin NK} (hi : 21 ≤ i.val) : ck_st S X x w ca cb i = S i :=
  ck_other (ck_ne hX (by omega)) (fun e => by subst e; exact absurd hi (by decide))
    (fun e => by subst e; exact absurd hi (by decide)) (fun e => by subst e; exact absurd hi (by decide))

theorem ck_set_X (hX : X.val < 18) (v : List Nat) : (ck_st S X x w ca cb).set X v = ck_st S X v w ca cb :=
  ck_eq hX (by simp) (by rw [Lists.set_ne _ _ (ck_ne hX (by decide)), ck_W hX])
    (by rw [Lists.set_ne _ _ (ck_ne hX (by decide)), ck_CA hX]) (by rw [Lists.set_ne _ _ (ck_ne hX (by decide)), ck_CB hX])
    (fun i a b c d => by rw [Lists.set_ne _ _ a, ck_other a b c d])
theorem ck_set_W (hX : X.val < 18) (v : List Nat) : (ck_st S X x w ca cb).set ot_W v = ck_st S X x v ca cb :=
  ck_eq hX (by rw [Lists.set_ne _ _ (ck_ne hX (by decide)).symm, ck_X]) (by simp)
    (by rw [Lists.set_ne _ _ (by decide), ck_CA hX]) (by rw [Lists.set_ne _ _ (by decide), ck_CB hX])
    (fun i a b c d => by rw [Lists.set_ne _ _ b, ck_other a b c d])
theorem ck_set_CA (hX : X.val < 18) (v : List Nat) : (ck_st S X x w ca cb).set ot_CA v = ck_st S X x w v cb :=
  ck_eq hX (by rw [Lists.set_ne _ _ (ck_ne hX (by decide)).symm, ck_X]) (by rw [Lists.set_ne _ _ (by decide), ck_W hX])
    (by simp) (by rw [Lists.set_ne _ _ (by decide), ck_CB hX])
    (fun i a b c d => by rw [Lists.set_ne _ _ c, ck_other a b c d])
theorem ck_set_CB (hX : X.val < 18) (v : List Nat) : (ck_st S X x w ca cb).set ot_CB v = ck_st S X x w ca v :=
  ck_eq hX (by rw [Lists.set_ne _ _ (ck_ne hX (by decide)).symm, ck_X]) (by rw [Lists.set_ne _ _ (by decide), ck_W hX])
    (by rw [Lists.set_ne _ _ (by decide), ck_CA hX]) (by simp)
    (fun i a b c d => by rw [Lists.set_ne _ _ d, ck_other a b c d])

/-- Setting a stack at index at least `21` to what it holds in `S`, after changing it. -/
theorem ck_set_hi_back (hX : X.val < 18) {i : Fin NK} (hi : 21 ≤ i.val) (v : List Nat) :
    ((ck_st S X x w ca cb).set i v).set i (S i) = ck_st S X x w ca cb := by
  rw [Lists.set_set_u, ← ck_hi hX hi (S := S) (x := x) (w := w) (ca := ca) (cb := cb), Lists.set_get_self]

end Ck

theorem ot_flatten_drop {us : List (List Nat)} {m : Nat} (h : m < us.length) :
    (us.drop m).flatten = us[m] ++ (us.drop (m + 1)).flatten := by
  rw [List.drop_eq_getElem_cons h, List.flatten_cons]

theorem ot_flatten_take {us : List (List Nat)} {m : Nat} (h : m < us.length) :
    (us.take (m + 1)).flatten = (us.take m).flatten ++ us[m] := by
  rw [List.take_succ_eq_append_getElem h, List.flatten_append]; simp

/-- The first element failing a test. -/
theorem ot_first_bad {α : Type} (p : α → Bool) : ∀ (l : List α), l.all p = false →
    ∃ k, ∃ h : k < l.length, p l[k] = false ∧ ∀ i (hi : i < k), p (l[i]'(by omega)) = true
  | [], h => by simp at h
  | a :: l, h => by
    by_cases ha : p a = true
    · have hl : l.all p = false := by simpa [ha] using h
      obtain ⟨k, hk, hp, hall⟩ := ot_first_bad p l hl
      refine ⟨k + 1, by simp; omega, by simpa using hp, fun i hi => ?_⟩
      cases i with
      | zero => simpa using ha
      | succ i => simpa using hall i (by omega)
    · exact ⟨0, by simp, by simpa using ha, fun i hi => absurd hi (by omega)⟩

/-- Scan stack `X`: move it onto `ot_W` and run `step` while `ot_W` is not empty. -/
def ot_scan (X : Fin NK) (hX : X ≠ ot_W) (step : NProg NK) : NProg NK :=
  .seq (nmvAll X ot_W hX) (.loop ot_W .nonempty step)

/-- **Scanning** a stack made of units `us`: each step moves one unit back and checks it with `gd`. -/
theorem ot_scan_ok (X : Fin NK) (hXW : X ≠ ot_W) (hX : X.val < 18) (step : NProg NK) (S : Lists NK)
    (us : List (List Nat)) (gd : List Nat → Bool) (T : Nat) (hXS : S X = us.flatten) (hs : ScratchEmpty S)
    (hne : ∀ u ∈ us, u ≠ [])
    (hstep : ∀ u ∈ us, ∀ P R : List Nat,
      (gd u = true → NRuns step (ck_st S X P (R ++ u.reverse) [] []) (ck_st S X (P ++ u) R [] []) T) ∧
      (gd u = false → ∃ S', NHalts step (ck_st S X P (R ++ u.reverse) [] []) false S' T)) :
    (us.all gd = true → NRuns (ot_scan X hXW step) S S (3 * us.flatten.length + 2 + us.length * (T + 1))) ∧
      (us.all gd = false → ∃ S', NHalts (ot_scan X hXW step) S false S'
        (3 * us.flatten.length + 2 + us.length * (T + 1))) := by
  have hW : S ot_W = [] := hs ot_W (by decide) (by decide)
  have x₁ := nruns_mvAll X ot_W hXW S
  have e₁ : (S.set ot_W (S ot_W ++ (S X).reverse)).set X [] = ck_st S X [] us.flatten.reverse [] [] := by
    refine ck_eq hX (by simp) ?_ ?_ ?_ ?_
    · rw [Lists.set_ne _ _ hXW.symm, Lists.set_same, hW, hXS]; rfl
    · rw [Lists.set_ne _ _ (ck_ne hX (by decide)), Lists.set_ne _ _ (by decide)]
      exact hs _ (by decide) (by decide)
    · rw [Lists.set_ne _ _ (ck_ne hX (by decide)), Lists.set_ne _ _ (by decide)]
      exact hs _ (by decide) (by decide)
    · intro i a b _ _; rw [Lists.set_ne _ _ a, Lists.set_ne _ _ b]
  rw [e₁, hXS] at x₁
  let F : Nat → Lists NK := fun m => ck_st S X (us.take m).flatten (us.drop m).flatten.reverse [] []
  have hF0 : F 0 = ck_st S X [] us.flatten.reverse [] [] := by simp [F]
  have hFn : F us.length = S := by
    simp only [F, List.take_length, List.drop_length, List.flatten_nil, List.reverse_nil]
    exact (ck_eq hX hXS hW (hs _ (by decide) (by decide)) (hs _ (by decide) (by decide)) (fun _ _ _ _ _ => rfl)).symm
  have hstepF : ∀ m (h : m < us.length),
      (gd us[m] = true → NRuns step (F m) (F (m + 1)) T) ∧ (gd us[m] = false → ∃ S', NHalts step (F m) false S' T) := by
    intro m h
    have hs' := hstep us[m] (List.getElem_mem h) (us.take m).flatten (us.drop (m + 1)).flatten.reverse
    have e₀ : F m = ck_st S X (us.take m).flatten ((us.drop (m + 1)).flatten.reverse ++ us[m].reverse) [] [] := by
      simp only [F]; rw [ot_flatten_drop h, List.reverse_append]
    have e₁ : F (m + 1) = ck_st S X ((us.take m).flatten ++ us[m]) (us.drop (m + 1)).flatten.reverse [] [] := by
      simp only [F]; rw [ot_flatten_take h]
    rw [e₀, e₁]; exact hs'
  have htest : ∀ m, m < us.length → NTest.nonempty.eval (F m ot_W) = true := fun m h => by
    simp only [F]; rw [ck_W hX, ot_flatten_drop h]
    exact eval_nonempty_ne (by simp [hne _ (List.getElem_mem h)])
  constructor
  · intro hall
    have hl := nruns_family_const (i := ot_W) (c := .nonempty) (p := step) F us.length T htest
      (by simp only [F]; rw [ck_W hX]; simp)
      (fun m h => (hstepF m h).1 (List.all_eq_true.1 hall _ (List.getElem_mem h)))
    rw [hF0, hFn] at hl
    exact (x₁.seq hl).mono (by omega)
  · intro hbad
    obtain ⟨k, hk, hp, hgood⟩ := ot_first_bad gd us hbad
    obtain ⟨S', hlast⟩ := (hstepF k hk).2 hp
    have hl := nhalts_family (i := ot_W) (c := .nonempty) (p := step) F k T
      (fun m hm => htest m (by omega)) (fun m hm => (hstepF m (by omega)).1 (hgood m hm)) hlast k 0 (by omega)
    rw [hF0] at hl
    refine ⟨S', (x₁.seqH hl).mono ?_⟩
    have : (k + 1) * (T + 1) ≤ us.length * (T + 1) := Nat.mul_le_mul_right _ hk
    omega

/-! ## Checking a number against `j` -/

/-- Pop the top `v` of `ot_OA` if `v ≤ j`; stop rejecting if `v > j`. -/
def ot_leP (j : Nat) : NProg NK :=
  .seq (npushC ot_OB j) (.seq (cmpTop ot_OB ot_OA ot_t ot_u ot_g ot_F (by decide) (by decide))
    (.ite ot_F .zero (.halt false) (.seq (.prim (.pop ot_F)) (.seq (.prim (.pop ot_OA)) (.prim (.pop ot_OB))))))

/-- The steps of `ot_leP j` on `v`. -/
def ot_leCost (j v : Nat) : Nat := (j + v + 1) * (2 * j + 6) + j + 25

theorem ot_leP_ok (j : Nat) (S : Lists NK) (v : Nat) (hA : S ot_OA = [v]) (hB : S ot_OB = []) (hF : S ot_F = []) :
    (v ≤ j → NRuns (ot_leP j) S (S.set ot_OA []) (ot_leCost j v)) ∧
      (j < v → ∃ S', NHalts (ot_leP j) S false S' (ot_leCost j v)) := by
  have x₁ := nruns_pushC ot_OB S j
  rw [hB, List.nil_append] at x₁
  have x₂ := nruns_cmpTop ot_OB ot_OA ot_t ot_u ot_g ot_F (by decide) (by decide) (by decide) (S.set ot_OB [j])
    (li := []) (lj := []) (a := j) (b := v) (by simp) (by rw [Lists.set_ne _ _ (by decide), hA]; rfl)
  have hF₂ : (S.set ot_OB [j]) ot_F = [] := by rw [Lists.set_ne _ _ (by decide), hF]
  rw [hF₂, List.nil_append] at x₂
  let S₂ := (S.set ot_OB [j]).set ot_F [cmpRes j v]
  constructor
  · intro hv
    obtain ⟨r, hr⟩ : ∃ r, cmpRes j v = r + 1 := by
      unfold cmpRes
      by_cases h₁ : j < v
      · omega
      · by_cases h₂ : j = v
        · exact ⟨0, by simp [h₂]⟩
        · exact ⟨1, by simp [h₁, h₂]⟩
    have y₁ := nruns_pop ot_F S₂ (l := []) (v := cmpRes j v) (by simp [S₂])
    have y₂ := nruns_pop ot_OA (S₂.set ot_F []) (l := []) (v := v)
      (by simp only [S₂]; rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide), hA]; rfl)
    have y₃ := nruns_pop ot_OB ((S₂.set ot_F []).set ot_OA []) (l := []) (v := j)
      (by simp only [S₂]; rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide),
        Lists.set_same]; rfl)
    have e : ((S₂.set ot_F []).set ot_OA []).set ot_OB [] = S.set ot_OA [] := by
      simp only [S₂]; ot_lists
    rw [e] at y₃
    refine (x₁.seq (x₂.seq ((y₁.seq (y₂.seq y₃)).iteF (by simp [hr]; rfl)))).mono ?_
    unfold ot_leCost; omega
  · intro hv
    have hr : cmpRes j v = 0 := by simp [cmpRes, hv]
    refine ⟨_, (x₁.seqH (x₂.seqH ((nhalts_halt false _).iteT (by simp [hr]; rfl)))).mono ?_⟩
    unfold ot_leCost; omega

/-- Beyond the branches of `caseTop`, running: the default, with the top lowered. -/
theorem ot_caseTop_default_runs (i : Fin NK) : ∀ (ps : List (NProg NK)) (q : NProg NK) (v : Nat) (S : Lists NK)
    (l : List Nat), S i = l ++ [v + ps.length] → ∀ (S' : Lists NK) (T : Nat),
      NRuns q (S.set i (l ++ [v])) S' T → NRuns (caseTop i ps q) S S' (T + 2 * ps.length)
  | [], q, v, S, l, hS, S', T, h => by
    simp only [List.length_nil, Nat.add_zero] at hS ⊢
    rw [← hS, Lists.set_get_self] at h; exact h
  | p :: ps, q, v, S, l, hS, S', T, h => by
    simp only [List.length_cons] at hS ⊢
    have hS' : S i = l ++ [(v + ps.length) + 1] := by rw [hS]; congr 2
    have h₁ := nruns_dec i S hS'
    simp only [Nat.add_sub_cancel] at h₁
    have h₂ := ot_caseTop_default_runs i ps q v (S.set i (l ++ [v + ps.length])) l (by simp) S' T
      (by rw [Lists.set_set_u]; exact h)
    exact ((h₁.seq h₂).iteF (by rw [hS']; simp)).mono (by omega)

/-! ## Reading an order and checking it -/

/-- Read entry `a` (popped from `ot_CB`) of the order table onto `ot_OA`. -/
def ot_peek : NProg NK := peekAt ORD ot_T ot_CB ot_OA (by decide) (by decide)

theorem ot_peek_runs {S : Lists NK} {X : Fin NK} (hX : X.val < 18) {tt : List (Nat × Nat)} (hs : ScratchEmpty S)
    (hO : S ORD = ordTable tt) (x w ca : List Nat) {a : Nat} (ha : a ≤ tt.length) :
    NRuns ot_peek (ck_st S X x w ca [a]) ((ck_st S X x w ca []).set ot_OA [ordNum tt a]) (10 * tt.length + 12) := by
  have hL : ck_st S X x w ca [a] ORD = ordTable tt := by rw [ck_hi hX (by decide), hO]
  have hlen : (ordTable tt).length = tt.length + 1 := by simp [ordTable]
  have x₁ := nruns_peekAt ORD ot_T ot_CB ot_OA (by decide) (by decide) (by decide) (ck_st S X x w ca [a])
    (by rw [ck_hi hX (by decide)]; exact hs _ (by decide) (by decide)) (lc := []) (k := a) (by rw [ck_CB hX]; rfl)
    (by rw [hL, hlen]; omega)
  have hv : (ck_st S X x w ca [a] ORD)[a]'(by rw [hL, hlen]; omega) = ordNum tt a := by
    simp only [hL, ordTable, List.getElem_map, List.getElem_range]
  rw [hv, ck_set_CB hX, ck_hi hX (by decide), hs ot_OA (by decide) (by decide), List.nil_append, hL, hlen] at x₁
  exact x₁.mono (by omega)

/-- After the read: check `ordNum a ≤ j` and clear `ot_OA`. -/
theorem ot_le_ck {S : Lists NK} {X : Fin NK} (hX : X.val < 18) (hs : ScratchEmpty S) (j v : Nat) (x w : List Nat) :
    (v ≤ j → NRuns (ot_leP j) ((ck_st S X x w [] []).set ot_OA [v]) (ck_st S X x w [] []) (ot_leCost j v)) ∧
      (j < v → ∃ S', NHalts (ot_leP j) ((ck_st S X x w [] []).set ot_OA [v]) false S' (ot_leCost j v)) := by
  have h := ot_leP_ok j ((ck_st S X x w [] []).set ot_OA [v]) v (by simp)
    (by rw [Lists.set_ne _ _ (by decide), ck_hi hX (by decide)]; exact hs _ (by decide) (by decide))
    (by rw [Lists.set_ne _ _ (by decide), ck_hi hX (by decide)]; exact hs _ (by decide) (by decide))
  have e : ((ck_st S X x w [] []).set ot_OA [v]).set ot_OA [] = ck_st S X x w [] [] := by
    have := ck_set_hi_back hX (i := ot_OA) (by decide) [v] (S := S) (x := x) (w := w) (ca := []) (cb := [])
    rwa [hs ot_OA (by decide) (by decide)] at this
  rw [e] at h
  exact h

theorem ot_leCost_mono (j : Nat) {v v' : Nat} (h : v ≤ v') : ot_leCost j v ≤ ot_leCost j v' := by
  unfold ot_leCost
  have : (j + v + 1) * (2 * j + 6) ≤ (j + v' + 1) * (2 * j + 6) := Nat.mul_le_mul_right _ (by omega)
  omega

/-! ## The rule types -/

/-- One rule type: move it back to `RTs`, read its order, check it is at most `j`. -/
def ot_rtStep (j : Nat) : NProg NK :=
  .seq (.prim (.dup ot_W RTs (by decide))) (.seq (nmv ot_W ot_CB (by decide)) (.seq ot_peek (ot_leP j)))

/-- The steps of a unit of the scan, with `L` arrows. -/
def ot_unitCost (j L : Nat) : Nat := 10 * L + 60 + ot_leCost j (L + 1)

theorem ot_rtStep_ok (j : Nat) {S : Lists NK} {tt : List (Nat × Nat)} (hs : ScratchEmpty S)
    (hO : S ORD = ordTable tt) {t : Nat} (ht : t ≤ tt.length) (P R : List Nat) :
    (decide (ordNum tt t ≤ j) = true → NRuns (ot_rtStep j) (ck_st S RTs P (R ++ [t]) [] [])
      (ck_st S RTs (P ++ [t]) R [] []) (ot_unitCost j tt.length)) ∧
    (decide (ordNum tt t ≤ j) = false → ∃ S', NHalts (ot_rtStep j) (ck_st S RTs P (R ++ [t]) [] []) false S'
      (ot_unitCost j tt.length)) := by
  have hX : (RTs : Fin NK).val < 18 := by decide
  have x₁ := nruns_dup ot_W RTs (by decide) (ck_st S RTs P (R ++ [t]) [] []) (l := R) (v := t) (by rw [ck_W hX])
  rw [ck_X, ck_set_X hX] at x₁
  have x₂ := nruns_mv ot_W ot_CB (by decide) (ck_st S RTs (P ++ [t]) (R ++ [t]) [] []) (l := R) (v := t)
    (by rw [ck_W hX])
  rw [ck_CB hX, ck_set_CB hX, ck_set_W hX, List.nil_append] at x₂
  have x₃ := ot_peek_runs hX hs hO (P ++ [t]) R [] ht
  have hc := ot_le_ck hX hs j (ordNum tt t) (P ++ [t]) R
  have hm := ot_leCost_mono j (show ordNum tt t ≤ tt.length + 1 by have := ot_ordNum_le tt t; omega)
  constructor
  · intro hg
    exact (x₁.seq (x₂.seq (x₃.seq (hc.1 (of_decide_eq_true hg))))).mono (by unfold ot_unitCost; omega)
  · intro hb
    obtain ⟨S', h⟩ := hc.2 (by have := of_decide_eq_false hb; omega)
    exact ⟨S', (x₁.seqH (x₂.seqH (x₃.seqH h))).mono (by unfold ot_unitCost; omega)⟩

/-! ## Items -/

/-- Move the four numbers of an item back onto `X`, keeping its tag on `ot_CA` and its `a` on `ot_CB`. -/
def ot_fetch (X : Fin NK) (hX : X ≠ ot_W) : NProg NK :=
  .seq (.prim (.dup ot_W X hX.symm)) (.seq (nmv ot_W ot_CA (by decide))
    (.seq (.prim (.dup ot_W X hX.symm)) (.seq (nmv ot_W ot_CB (by decide))
      (.seq (.prim (.dup ot_W X hX.symm)) (.seq (.prim (.pop ot_W))
        (.seq (.prim (.dup ot_W X hX.symm)) (.prim (.pop ot_W))))))))

theorem ot_fetch_runs {S : Lists NK} {X : Fin NK} (hXW : X ≠ ot_W) (hX : X.val < 18) (P R : List Nat)
    (tag a b c : Nat) :
    NRuns (ot_fetch X hXW) (ck_st S X P (R ++ [c, b, a, tag]) [] [])
      (ck_st S X (P ++ [tag, a, b, c]) R [tag] [a]) 10 := by
  have x₁ := nruns_dup ot_W X hXW.symm (ck_st S X P (R ++ [c, b, a, tag]) [] []) (l := R ++ [c, b, a]) (v := tag)
    (by rw [ck_W hX]; simp)
  rw [ck_X, ck_set_X hX] at x₁
  have x₂ := nruns_mv ot_W ot_CA (by decide) (ck_st S X (P ++ [tag]) (R ++ [c, b, a, tag]) [] [])
    (l := R ++ [c, b, a]) (v := tag) (by rw [ck_W hX]; simp)
  rw [ck_CA hX, ck_set_CA hX, ck_set_W hX, List.nil_append] at x₂
  have x₃ := nruns_dup ot_W X hXW.symm (ck_st S X (P ++ [tag]) (R ++ [c, b, a]) [tag] []) (l := R ++ [c, b]) (v := a)
    (by rw [ck_W hX]; simp)
  rw [ck_X, ck_set_X hX] at x₃
  have x₄ := nruns_mv ot_W ot_CB (by decide) (ck_st S X (P ++ [tag] ++ [a]) (R ++ [c, b, a]) [tag] [])
    (l := R ++ [c, b]) (v := a) (by rw [ck_W hX]; simp)
  rw [ck_CB hX, ck_set_CB hX, ck_set_W hX, List.nil_append] at x₄
  have x₅ := nruns_dup ot_W X hXW.symm (ck_st S X (P ++ [tag] ++ [a]) (R ++ [c, b]) [tag] [a]) (l := R ++ [c])
    (v := b) (by rw [ck_W hX]; simp)
  rw [ck_X, ck_set_X hX] at x₅
  have x₆ := nruns_pop ot_W (ck_st S X (P ++ [tag] ++ [a] ++ [b]) (R ++ [c, b]) [tag] [a]) (l := R ++ [c]) (v := b)
    (by rw [ck_W hX]; simp)
  rw [ck_set_W hX] at x₆
  have x₇ := nruns_dup ot_W X hXW.symm (ck_st S X (P ++ [tag] ++ [a] ++ [b]) (R ++ [c]) [tag] [a]) (l := R)
    (v := c) (by rw [ck_W hX])
  rw [ck_X, ck_set_X hX] at x₇
  have x₈ := nruns_pop ot_W (ck_st S X (P ++ [tag] ++ [a] ++ [b] ++ [c]) (R ++ [c]) [tag] [a]) (l := R) (v := c)
    (by rw [ck_W hX])
  rw [ck_set_W hX] at x₈
  have e : P ++ [tag] ++ [a] ++ [b] ++ [c] = P ++ [tag, a, b, c] := by simp
  rw [e] at x₇ x₈
  exact x₁.seq (x₂.seq (x₃.seq (x₄.seq (x₅.seq (x₆.seq (x₇.seq x₈))))))

/-- Read the order of `a` (popped from `ot_CB`) and check `ordNum a + 1 ≤ j`. -/
def ot_check1 (j : Nat) : NProg NK := .seq ot_peek (.seq (.prim (.inc ot_OA)) (ot_leP j))

/-- The branches on the tag: `11` checks, any other tag only clears `ot_CB`. -/
def ot_tagBranches (j : Nat) : List (NProg NK) := List.replicate 11 (.prim (.pop ot_CB)) ++ [ot_check1 j]

/-- Check an item on `ot_CA` (tag), `ot_CB` (`a`). -/
def ot_itemTest (j : Nat) : NProg NK :=
  caseTop ot_CA (ot_tagBranches j) (.seq (.prim (.pop ot_CA)) (.prim (.pop ot_CB)))

/-- One item: move it back onto `X` and check it. -/
def ot_itemStep (X : Fin NK) (hX : X ≠ ot_W) (j : Nat) : NProg NK := .seq (ot_fetch X hX) (ot_itemTest j)

/-- The test on the four numbers of an item. -/
def ot_gdI (j : Nat) (tt : List (Nat × Nat)) : List Nat → Bool
  | [tag, a, _, _] => tag != 11 || decide (ordNum tt a + 1 ≤ j)
  | _ => true

theorem ot_tagBranches_lt (j v : Nat) (h : v < 11) :
    (ot_tagBranches j)[v]'(by simp [ot_tagBranches]; omega) = .prim (.pop ot_CB) := by
  simp only [ot_tagBranches]
  rw [List.getElem_append_left (by simp; omega), List.getElem_replicate]

theorem ot_tagBranches_11 (j : Nat) : (ot_tagBranches j)[11]'(by simp [ot_tagBranches]) = ot_check1 j := by
  simp [ot_tagBranches]

theorem ot_itemStep_ok {S : Lists NK} {X : Fin NK} (hXW : X ≠ ot_W) (hX : X.val < 18) (j : Nat)
    {tt : List (Nat × Nat)} (hs : ScratchEmpty S) (hO : S ORD = ordTable tt) (tag a b c : Nat)
    (ha : tag = 11 → a ≤ tt.length) (P R : List Nat) :
    (ot_gdI j tt [tag, a, b, c] = true → NRuns (ot_itemStep X hXW j) (ck_st S X P (R ++ [c, b, a, tag]) [] [])
      (ck_st S X (P ++ [tag, a, b, c]) R [] []) (ot_unitCost j tt.length)) ∧
    (ot_gdI j tt [tag, a, b, c] = false → ∃ S', NHalts (ot_itemStep X hXW j) (ck_st S X P (R ++ [c, b, a, tag]) [] [])
      false S' (ot_unitCost j tt.length)) := by
  have x₁ := ot_fetch_runs (S := S) hXW hX P R tag a b c
  let L := ck_st S X (P ++ [tag, a, b, c]) R [tag] [a]
  have hLCA : L ot_CA = [] ++ [tag] := by simp only [L]; rw [ck_CA hX]; rfl
  have hLset : L.set ot_CA [] = ck_st S X (P ++ [tag, a, b, c]) R [] [a] := by simp only [L]; rw [ck_set_CA hX]
  have hlen : (ot_tagBranches j).length = 12 := by simp [ot_tagBranches]
  have hpop : NRuns (.prim (.pop ot_CB)) (ck_st S X (P ++ [tag, a, b, c]) R [] [a])
      (ck_st S X (P ++ [tag, a, b, c]) R [] []) 1 := by
    have := nruns_pop ot_CB (ck_st S X (P ++ [tag, a, b, c]) R [] [a]) (l := []) (v := a) (by rw [ck_CB hX]; rfl)
    rwa [ck_set_CB hX] at this
  have hu : ot_unitCost j tt.length ≥ 10 * tt.length + 60 + ot_leCost j (tt.length + 1) := by
    unfold ot_unitCost; omega
  by_cases h11 : tag = 11
  · subst h11
    have hal := ha rfl
    have x₂ := ot_peek_runs hX hs hO (P ++ [11, a, b, c]) R [] hal
    have x₃ := nruns_inc ot_OA ((ck_st S X (P ++ [11, a, b, c]) R [] []).set ot_OA [ordNum tt a]) (l := [])
      (v := ordNum tt a) (by simp)
    rw [Lists.set_set_u, List.nil_append] at x₃
    have hc := ot_le_ck hX hs j (ordNum tt a + 1) (P ++ [11, a, b, c]) R
    have hm := ot_leCost_mono j (show ordNum tt a + 1 ≤ tt.length + 1 by have := ot_ordNum_le tt a; omega)
    have hg : ot_gdI j tt [11, a, b, c] = decide (ordNum tt a + 1 ≤ j) := by simp [ot_gdI]
    rw [hg]
    constructor
    · intro hgd
      have y := caseTop_runs ot_CA (ot_tagBranches j) (.seq (.prim (.pop ot_CA)) (.prim (.pop ot_CB))) 11 (by rw [hlen]; omega) L [] hLCA _ _
        (by rw [hLset, ot_tagBranches_11]; exact x₂.seq (x₃.seq (hc.1 (of_decide_eq_true hgd))))
      exact (x₁.seq y).mono (by omega)
    · intro hbd
      obtain ⟨S', h⟩ := hc.2 (by have := of_decide_eq_false hbd; omega)
      have y := caseTop_halts ot_CA (ot_tagBranches j) (.seq (.prim (.pop ot_CA)) (.prim (.pop ot_CB))) 11 (by rw [hlen]; omega) L [] hLCA false S' _
        (by rw [hLset, ot_tagBranches_11]; exact x₂.seqH (x₃.seqH h))
      exact ⟨S', (x₁.seqH y).mono (by omega)⟩
  · have hg : ot_gdI j tt [tag, a, b, c] = true := by simp [ot_gdI, h11]
    refine ⟨fun _ => ?_, fun h => absurd h (by rw [hg]; simp)⟩
    by_cases hlt : tag < 11
    · have y := caseTop_runs ot_CA (ot_tagBranches j) (.seq (.prim (.pop ot_CA)) (.prim (.pop ot_CB))) tag (by rw [hlen]; omega) L [] hLCA _ _
        (by rw [hLset, ot_tagBranches_lt j tag hlt]; exact hpop)
      exact (x₁.seq y).mono (by omega)
    · obtain ⟨v, rfl⟩ : ∃ v, tag = v + 12 := ⟨tag - 12, by omega⟩
      have hp₁ := nruns_pop ot_CA (L.set ot_CA ([] ++ [v])) (l := []) (v := v) (by simp)
      rw [Lists.set_set_u, hLset] at hp₁
      have y := ot_caseTop_default_runs ot_CA (ot_tagBranches j) (.seq (.prim (.pop ot_CA)) (.prim (.pop ot_CB)))
        v L [] (by rw [hlen]; exact hLCA) _ _ (hp₁.seq hpop)
      exact (x₁.seq y).mono (by rw [hlen]; omega)

/-! ## Bodies: items and separators -/

/-- A separator `13`: move it back onto `BOD`. -/
def ot_sep : NProg NK := .seq (.prim (.dup ot_W BOD (by decide))) (.prim (.pop ot_W))

/-- The branches on the top of `ot_W` in a body: tags `0`–`12` start an item, `13` is a separator. -/
def ot_bodBranches (j : Nat) : List (NProg NK) := List.replicate 13 (ot_itemStep BOD (by decide) j) ++ [ot_sep]

/-- One unit of the bodies: an item or a separator. -/
def ot_bodStep (j : Nat) : NProg NK :=
  .seq (.prim (.dup ot_W ot_CA (by decide))) (caseTop ot_CA (ot_bodBranches j) (.halt false))

theorem ot_bodBranches_lt (j v : Nat) (h : v < 13) :
    (ot_bodBranches j)[v]'(by simp [ot_bodBranches]; omega) = ot_itemStep BOD (by decide) j := by
  simp only [ot_bodBranches]
  rw [List.getElem_append_left (by simp; omega), List.getElem_replicate]

theorem ot_bodBranches_13 (j : Nat) : (ot_bodBranches j)[13]'(by simp [ot_bodBranches]) = ot_sep := by
  simp [ot_bodBranches]

theorem ot_bodStep_item (j : Nat) {S : Lists NK} {tt : List (Nat × Nat)} (hs : ScratchEmpty S)
    (hO : S ORD = ordTable tt) (tag a b c : Nat) (htag : tag ≤ 12) (ha : tag = 11 → a ≤ tt.length) (P R : List Nat) :
    (ot_gdI j tt [tag, a, b, c] = true → NRuns (ot_bodStep j) (ck_st S BOD P (R ++ [c, b, a, tag]) [] [])
      (ck_st S BOD (P ++ [tag, a, b, c]) R [] []) (ot_unitCost j tt.length + 30)) ∧
    (ot_gdI j tt [tag, a, b, c] = false → ∃ S', NHalts (ot_bodStep j) (ck_st S BOD P (R ++ [c, b, a, tag]) [] [])
      false S' (ot_unitCost j tt.length + 30)) := by
  have hX : (BOD : Fin NK).val < 18 := by decide
  have x₁ := nruns_dup ot_W ot_CA (by decide) (ck_st S BOD P (R ++ [c, b, a, tag]) [] []) (l := R ++ [c, b, a])
    (v := tag) (by rw [ck_W hX]; simp)
  rw [ck_CA hX, ck_set_CA hX] at x₁
  have hL : (ck_st S BOD P (R ++ [c, b, a, tag]) ([] ++ [tag]) []).set ot_CA [] =
      ck_st S BOD P (R ++ [c, b, a, tag]) [] [] := ck_set_CA hX []
  have hlen : (ot_bodBranches j).length = 14 := by simp [ot_bodBranches]
  have hi := ot_itemStep_ok (S := S) (X := BOD) (by decide) hX j hs hO tag a b c ha P R
  constructor
  · intro hg
    have y := caseTop_runs ot_CA (ot_bodBranches j) (.halt false) tag (by rw [hlen]; omega) (ck_st S BOD P (R ++ [c, b, a, tag]) ([] ++ [tag]) []) [] (by rw [ck_CA hX]) _ _
      (by rw [hL, ot_bodBranches_lt j tag (by omega)]; exact hi.1 hg)
    exact (x₁.seq y).mono (by omega)
  · intro hb
    obtain ⟨S', h⟩ := hi.2 hb
    have y := caseTop_halts ot_CA (ot_bodBranches j) (.halt false) tag (by rw [hlen]; omega) (ck_st S BOD P (R ++ [c, b, a, tag]) ([] ++ [tag]) []) [] (by rw [ck_CA hX])
      false S' _ (by rw [hL, ot_bodBranches_lt j tag (by omega)]; exact h)
    exact ⟨S', (x₁.seqH y).mono (by omega)⟩

theorem ot_bodStep_sep (j : Nat) {S : Lists NK} (P R : List Nat) :
    NRuns (ot_bodStep j) (ck_st S BOD P (R ++ [13]) [] []) (ck_st S BOD (P ++ [13]) R [] []) 31 := by
  have hX : (BOD : Fin NK).val < 18 := by decide
  have x₁ := nruns_dup ot_W ot_CA (by decide) (ck_st S BOD P (R ++ [13]) [] []) (l := R) (v := 13) (by rw [ck_W hX])
  rw [ck_CA hX, ck_set_CA hX] at x₁
  have hL : (ck_st S BOD P (R ++ [13]) ([] ++ [13]) []).set ot_CA [] = ck_st S BOD P (R ++ [13]) [] [] :=
    ck_set_CA hX []
  have y₁ := nruns_dup ot_W BOD (by decide) (ck_st S BOD P (R ++ [13]) [] []) (l := R) (v := 13) (by rw [ck_W hX])
  rw [ck_X, ck_set_X hX] at y₁
  have y₂ := nruns_pop ot_W (ck_st S BOD (P ++ [13]) (R ++ [13]) [] []) (l := R) (v := 13) (by rw [ck_W hX])
  rw [ck_set_W hX] at y₂
  have hlen : (ot_bodBranches j).length = 14 := by simp [ot_bodBranches]
  have y := caseTop_runs ot_CA (ot_bodBranches j) (.halt false) 13 (by rw [hlen]; omega) (ck_st S BOD P (R ++ [13]) ([] ++ [13]) []) [] (by rw [ck_CA hX]) _ _
    (by rw [hL, ot_bodBranches_13]; exact y₁.seq y₂)
  exact (x₁.seq y).mono (by omega)

/-! ## The units of the three stacks -/

/-- The test on a rule type. -/
def ot_gdR (j : Nat) (tt : List (Nat × Nat)) : List Nat → Bool
  | [t] => decide (ordNum tt t ≤ j)
  | _ => true

def ot_rtUnits (rt : List Nat) : List (List Nat) := rt.map (fun t => [t])
def ot_itemUnits (l : List MItem) : List (List Nat) := l.map encItem
def ot_bodUnits (bs : List (List MItem)) : List (List Nat) := bs.flatMap (fun b => b.map encItem ++ [[13]])

theorem ot_rtUnits_flatten (rt : List Nat) : (ot_rtUnits rt).flatten = rt := by
  induction rt with
  | nil => rfl
  | cons t rt ih => simp only [ot_rtUnits, List.map_cons, List.flatten_cons] at ih ⊢; rw [ih]; rfl

theorem ot_itemUnits_flatten (l : List MItem) : (ot_itemUnits l).flatten = encItems l := by
  simp [ot_itemUnits, encItems, List.flatMap]

theorem ot_bodUnits_flatten (bs : List (List MItem)) : (ot_bodUnits bs).flatten = encBodies bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [ot_bodUnits, encBodies, List.flatMap_cons, List.flatten_append] at ih ⊢
    rw [ih]; simp [encItems, List.flatMap]

theorem ot_rtUnits_all (j : Nat) (tt : List (Nat × Nat)) (rt : List Nat) :
    (ot_rtUnits rt).all (ot_gdR j tt) = rt.all (fun t => decide (ordNum tt t ≤ j)) := by
  simp only [ot_rtUnits, List.all_map]; rfl

theorem ot_gdI_enc (j : Nat) (tt : List (Nat × Nat)) (it : MItem) : ot_gdI j tt (encItem it) = itemCheck j tt it := by
  simp [encItem, ot_gdI, itemCheck]

theorem ot_itemUnits_all (j : Nat) (tt : List (Nat × Nat)) (l : List MItem) :
    (ot_itemUnits l).all (ot_gdI j tt) = l.all (itemCheck j tt) := by
  simp only [ot_itemUnits, List.all_map]; congr 1

theorem ot_bodUnits_all (j : Nat) (tt : List (Nat × Nat)) (bs : List (List MItem)) :
    (ot_bodUnits bs).all (ot_gdI j tt) = bs.flatten.all (itemCheck j tt) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [ot_bodUnits, List.flatMap_cons, List.all_append, List.flatten_cons] at ih ⊢
    rw [ih, List.all_map]
    have e : (ot_gdI j tt ∘ encItem) = itemCheck j tt := by funext it; exact ot_gdI_enc j tt it
    rw [e]; simp [ot_gdI]

theorem ot_mem_bodUnits {bs : List (List MItem)} {u : List Nat} (h : u ∈ ot_bodUnits bs) :
    (∃ it ∈ bs.flatten, u = encItem it) ∨ u = [13] := by
  simp only [ot_bodUnits, List.mem_flatMap, List.mem_append, List.mem_map, List.mem_singleton] at h
  obtain ⟨b, hb, ⟨it, hit, rfl⟩ | rfl⟩ := h
  · exact Or.inl ⟨it, List.mem_flatten.2 ⟨b, hb, hit⟩, rfl⟩
  · exact Or.inr rfl

theorem ot_length_le_flatten {us : List (List Nat)} (h : ∀ u ∈ us, u ≠ []) : us.length ≤ us.flatten.length := by
  induction us with
  | nil => simp
  | cons u us ih =>
    have hu := h u List.mem_cons_self
    have := ih (fun v hv => h v (List.mem_cons_of_mem _ hv))
    have : 1 ≤ u.length := List.length_pos_iff.2 hu
    simp only [List.length_cons, List.flatten_cons, List.length_append]; omega

/-! ## The order check -/

/-- The order check: every rule type has order `≤ j`, every lambda item of the bodies and the start binds a type of
order `< j`. The three stacks are scanned unit by unit and restored. -/
def ordCheckP (j : Nat) : NProg NK :=
  .seq (ot_scan RTs (by decide) (ot_rtStep j))
    (.seq (ot_scan BOD (by decide) (ot_bodStep j)) (ot_scan STA (by decide) (ot_itemStep STA (by decide) j)))

/-- The steps of the order check. -/
def ordCheckCost (j : Nat) (st : PSt) : Nat :=
  1000 * (j + st.tt.length + st.rt.length + (encBodies st.bodies).length + (encItems st.start).length + 1) *
    (j + st.tt.length + st.rt.length + (encBodies st.bodies).length + (encItems st.start).length + 1) *
    (j + st.tt.length + st.rt.length + (encBodies st.bodies).length + (encItems st.start).length + 1)

/-- The three scans fit in `ordCheckCost`. -/
theorem ot_checkCost_le (j L r eb es nr nb ns : Nat) (h₁ : nr ≤ r) (h₂ : nb ≤ eb) (h₃ : ns ≤ es) :
    (3 * r + 2 + nr * (ot_unitCost j L + 30 + 1)) + (3 * eb + 2 + nb * (ot_unitCost j L + 30 + 1)) +
      (3 * es + 2 + ns * (ot_unitCost j L + 30 + 1)) ≤
      1000 * (j + L + r + eb + es + 1) * (j + L + r + eb + es + 1) * (j + L + r + eb + es + 1) := by
  generalize hN : j + L + r + eb + es + 1 = N
  have hm : (j + L + 2) * (2 * j + 6) ≤ (2 * N) * (6 * N) := Nat.mul_le_mul (by omega) (by omega)
  rw [Nat.mul_mul_mul_comm] at hm
  have hNN : N ≤ N * N := Nat.le_mul_self N
  have hT : ot_unitCost j L + 30 + 1 ≤ 139 * (N * N) := by
    unfold ot_unitCost ot_leCost
    have : L + 1 + 1 = L + 2 := rfl
    rw [show j + (L + 1) + 1 = j + L + 2 by omega]
    omega
  have hb : ∀ n, n ≤ N → n * (ot_unitCost j L + 30 + 1) ≤ 139 * (N * N * N) := fun n hn => by
    have := Nat.mul_le_mul hn hT
    have e : N * (139 * (N * N)) = 139 * (N * N * N) := by rw [Nat.mul_left_comm, ← Nat.mul_assoc N N N]
    rw [e] at this
    exact this
  have hNNN : N ≤ N * N * N := Nat.le_trans hNN (Nat.le_mul_of_pos_right _ (by omega))
  have e : 1000 * N * N * N = 1000 * (N * N * N) := by simp only [Nat.mul_assoc]
  have b₁ := hb nr (by omega)
  have b₂ := hb nb (by omega)
  have b₃ := hb ns (by omega)
  rw [e]
  generalize N * N * N = P at *
  omega

theorem ordCheckP_ok (j : Nat) (S : Lists NK) (st : PSt) (hw : TTWF st.tt) (hO : S ORD = ordTable st.tt)
    (hR : S RTs = st.rt) (hB : S BOD = encBodies st.bodies) (hA : S STA = encItems st.start) (hs : ScratchEmpty S)
    (hrt : ∀ t ∈ st.rt, t ≤ st.tt.length) (hit : ∀ it ∈ st.bodies.flatten ++ st.start, it.tag = 11 → it.a ≤ st.tt.length)
    (htag : ∀ it ∈ st.bodies.flatten, it.tag ≤ 12) :
    (ordOK j st = true → NRuns (ordCheckP j) S S (ordCheckCost j st)) ∧
      (ordOK j st = false → ∃ S', NHalts (ordCheckP j) S false S' (ordCheckCost j st)) := by
  have _ := hw
  let T := ot_unitCost j st.tt.length + 30
  -- the rule types
  have sR := ot_scan_ok RTs (by decide) (by decide) (ot_rtStep j) S (ot_rtUnits st.rt) (ot_gdR j st.tt) T
    (by rw [ot_rtUnits_flatten, hR]) hs
    (fun u hu => by simp only [ot_rtUnits, List.mem_map] at hu; obtain ⟨t, _, rfl⟩ := hu; simp)
    (fun u hu P R => by
      simp only [ot_rtUnits, List.mem_map] at hu
      obtain ⟨t, ht, rfl⟩ := hu
      have h := ot_rtStep_ok j hs hO (hrt t ht) P R
      exact ⟨fun g => (h.1 g).mono (by omega), fun g => let ⟨S', x⟩ := h.2 g; ⟨S', x.mono (by omega)⟩⟩)
  -- the bodies
  have sB := ot_scan_ok BOD (by decide) (by decide) (ot_bodStep j) S (ot_bodUnits st.bodies) (ot_gdI j st.tt) T
    (by rw [ot_bodUnits_flatten, hB]) hs
    (fun u hu => by rcases ot_mem_bodUnits hu with ⟨it, _, rfl⟩ | rfl <;> simp [encItem])
    (fun u hu P R => by
      rcases ot_mem_bodUnits hu with ⟨it, hmem, rfl⟩ | rfl
      · have h := ot_bodStep_item j hs hO it.tag it.a it.b it.ctx (htag it hmem)
          (hit it (List.mem_append_left _ hmem)) P R
        exact ⟨fun g => (h.1 g).mono (by omega), fun g => let ⟨S', x⟩ := h.2 g; ⟨S', x.mono (by omega)⟩⟩
      · refine ⟨fun _ => (ot_bodStep_sep j P R).mono ?_, fun g => absurd g (by simp [ot_gdI])⟩
        simp only [T, ot_unitCost]; omega)
  -- the start
  have sA := ot_scan_ok STA (by decide) (by decide) (ot_itemStep STA (by decide) j) S (ot_itemUnits st.start)
    (ot_gdI j st.tt) T (by rw [ot_itemUnits_flatten, hA]) hs
    (fun u hu => by simp only [ot_itemUnits, List.mem_map] at hu; obtain ⟨it, _, rfl⟩ := hu; simp [encItem])
    (fun u hu P R => by
      simp only [ot_itemUnits, List.mem_map] at hu
      obtain ⟨it, hmem, rfl⟩ := hu
      have h := ot_itemStep_ok (S := S) (X := STA) (by decide) (by decide) j hs hO it.tag it.a it.b it.ctx
        (hit it (List.mem_append_right _ hmem)) P R
      exact ⟨fun g => (h.1 g).mono (by omega), fun g => let ⟨S', x⟩ := h.2 g; ⟨S', x.mono (by omega)⟩⟩)
  -- the costs
  have nR : (ot_rtUnits st.rt).length ≤ st.rt.length := by simp [ot_rtUnits]
  have nB : (ot_bodUnits st.bodies).length ≤ (encBodies st.bodies).length := by
    have := ot_length_le_flatten (us := ot_bodUnits st.bodies)
      (fun u hu => by rcases ot_mem_bodUnits hu with ⟨it, _, rfl⟩ | rfl <;> simp [encItem])
    rwa [ot_bodUnits_flatten] at this
  have nA : (ot_itemUnits st.start).length ≤ (encItems st.start).length := by
    have := ot_length_le_flatten (us := ot_itemUnits st.start)
      (fun u hu => by simp only [ot_itemUnits, List.mem_map] at hu; obtain ⟨it, _, rfl⟩ := hu; simp [encItem])
    rwa [ot_itemUnits_flatten] at this
  have hc := ot_checkCost_le j st.tt.length st.rt.length (encBodies st.bodies).length (encItems st.start).length
    _ _ _ nR nB nA
  rw [ot_rtUnits_flatten] at sR
  rw [ot_bodUnits_flatten] at sB
  rw [ot_itemUnits_flatten] at sA
  have hcost : ordCheckCost j st = 1000 * (j + st.tt.length + st.rt.length + (encBodies st.bodies).length +
      (encItems st.start).length + 1) * (j + st.tt.length + st.rt.length + (encBodies st.bodies).length +
      (encItems st.start).length + 1) * (j + st.tt.length + st.rt.length + (encBodies st.bodies).length +
      (encItems st.start).length + 1) := rfl
  rw [← hcost] at hc
  have hT : T = ot_unitCost j st.tt.length + 30 := rfl
  rw [← hT] at hc
  -- the answer
  have hdef : ordOK j st = ((ot_rtUnits st.rt).all (ot_gdR j st.tt) &&
      ((ot_bodUnits st.bodies).all (ot_gdI j st.tt) && (ot_itemUnits st.start).all (ot_gdI j st.tt))) := by
    rw [ot_rtUnits_all, ot_bodUnits_all, ot_itemUnits_all]
    simp only [ordOK, List.all_append]; rfl
  rw [hdef]
  constructor
  · intro h
    simp only [Bool.and_eq_true] at h
    exact ((sR.1 h.1).seq ((sB.1 h.2.1).seq (sA.1 h.2.2))).mono (by omega)
  · intro h
    cases h₁ : (ot_rtUnits st.rt).all (ot_gdR j st.tt)
    · obtain ⟨S', x⟩ := sR.2 h₁
      exact ⟨S', x.seq.mono (by omega)⟩
    · cases h₂ : (ot_bodUnits st.bodies).all (ot_gdI j st.tt)
      · obtain ⟨S', x⟩ := sB.2 h₂
        exact ⟨S', ((sR.1 h₁).seqH x.seq).mono (by omega)⟩
      · have h₃ : (ot_itemUnits st.start).all (ot_gdI j st.tt) = false := by
          rw [h₁, h₂] at h; simpa using h
        obtain ⟨S', x⟩ := sA.2 h₃
        exact ⟨S', ((sR.1 h₁).seqH ((sB.1 h₂).seqH x)).mono (by omega)⟩

end Shallot.MacroPeg.Mach
