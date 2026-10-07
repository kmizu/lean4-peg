import Complexity.Undec.TMSRStep

/-!
# One-tape tables as string rewriting systems: rewrites match steps

- forward (`fwd_step`): the word of a configuration rewrites to the word of its successor; a head just past the end
  first reads a blank with the end rule;
- backward (`back_step`): a rewrite of the word of a configuration whose state is not `0` gives the word of the
  successor or the same configuration with one more trailing blank. The word has exactly one state symbol, so a rule
  can only apply around it (`zw_split`).
-/

namespace Complexity.Undec

open Complexity

variable {T : TTable}

/-! ## Forward -/

/-- The rewrite of one step reading a symbol on the tape. -/
theorem fwd_cell (hT : Univ.RowsOK T) (hk : T.k = 1) {q a : Nat} {L R' : List Nat} {r : Row} (hq : q < bnd T)
    (ha : a < bnd T) (hL : ∀ z ∈ L, z < bnd T) (h0 : q ≠ 0) (h1 : q ≠ 1) (hr : T.rows[T.idx q [a]]? = some r) :
    SRStep (tmSRS T) (zw T q L (a :: R')) (cword T (fstep T (mk q L.length (L ++ a :: R')))) := by
  cases hm : mv r with
  | R =>
    rw [res_R hT hk h0 h1 hr hm]
    exact step_of (l := [stS T q, a]) (r := [wr r, stS T r.1]) (cell_mem hq ha h0 h1 hr (by rw [cellRules_R hm]; simp))
      (u := lbS T :: L) (v := R' ++ [rbS T]) (by simp [zw]) (by simp [zw])
  | S =>
    rw [res_S hT hk h0 h1 hr hm]
    exact step_of (l := [stS T q, a]) (r := [stS T r.1, wr r]) (cell_mem hq ha h0 h1 hr (by rw [cellRules_S hm]; simp))
      (u := lbS T :: L) (v := R' ++ [rbS T]) (by simp [zw]) (by simp [zw])
  | L =>
    rcases nil_or_snoc L with rfl | ⟨L', c, rfl⟩
    · rw [res_L0 hT hk h0 h1 hr hm]
      exact step_of (l := [lbS T, stS T q, a]) (r := [lbS T, stS T r.1, wr r]) (cell_mem hq ha h0 h1 hr (by rw [cellRules_L hm]; simp))
        (u := []) (v := R' ++ [rbS T]) (by simp [zw]) (by simp [zw])
    · rw [res_L1 hT hk h0 h1 hr hm L' c]
      have hc : c < bnd T := hL c (by simp)
      exact step_of (l := [c, stS T q, a]) (r := [stS T r.1, c, wr r])
        (cell_mem hq ha h0 h1 hr (by rw [cellRules_L hm]; simp [hc]))
        (u := lbS T :: L') (v := R' ++ [rbS T]) (by simp [zw]) (by simp [zw])

/-- The rewrites of one step of a configuration split at its head. -/
theorem fwd_zip (hT : Univ.RowsOK T) (hk : T.k = 1) {q : Nat} {L R : List Nat} (hq : q < bnd T)
    (hL : ∀ z ∈ L, z < bnd T) (hR : ∀ z ∈ R, z < bnd T) :
    SRStar (tmSRS T) (zw T q L R) (cword T (fstep T (mk q L.length (L ++ R)))) := by
  by_cases h01 : q = 0 ∨ q = 1
  · rw [fstep_halt T _ _ h01, cword_mk]; exact SRStar.refl _
  · have h0 : q ≠ 0 := fun e => h01 (Or.inl e)
    have h1 : q ≠ 1 := fun e => h01 (Or.inr e)
    cases R with
    | cons a R' =>
      cases hr : T.rows[T.idx q [a]]? with
      | none =>
        have hg : (L ++ a :: R').getD L.length 0 = a := by simp
        rw [fstep_none T h0 h1 (by rw [hg]; exact hr), cword_mk]; exact SRStar.refl _
      | some r => exact SRStar.step (fwd_cell hT hk hq (hR a (by simp)) hL h0 h1 hr) (SRStar.refl _)
    | nil =>
      have hg : (L ++ []).getD L.length 0 = 0 := by simp
      cases hr : T.rows[T.idx q [0]]? with
      | none =>
        rw [fstep_none T h0 h1 (by rw [hg]; exact hr), cword_mk]; exact SRStar.refl _
      | some r =>
        have e : fstep T (mk q L.length (L ++ [])) = fstep T (mk q L.length (L ++ [0])) := by
          rw [fstep_some hT hk h0 h1 (by rw [hg]; exact hr), fstep_cell hT hk h0 h1 hr]
          unfold writeAt; simp
        rw [e]
        refine SRStar.step (step_of (end_mem hq h0 h1) (u := lbS T :: L) (v := []) (y := zw T q L [0]) ?_ ?_)
          (SRStar.step (fwd_cell hT hk hq (by unfold bnd; omega) hL h0 h1 hr) (SRStar.refl _))
        · simp [zw]
        · simp [zw]

/-- **Forward**: the word of a configuration rewrites to the word of its successor. -/
theorem fwd_step (hT : Univ.RowsOK T) (hk : T.k = 1) {c : FCfg} (hc : Good T c) :
    SRStar (tmSRS T) (cword T c) (cword T (fstep T c)) := by
  obtain ⟨q, p, t, rfl, hp, ht, hq⟩ := hc
  rw [mk_split q p t hp, cword_mk]
  exact fwd_zip hT hk hq (fun z hz => ht z (List.mem_of_mem_take hz)) (fun z hz => ht z (List.mem_of_mem_drop hz))

/-! ## Backward -/

/-- **Backward**, at a split: the rewrites of the word of a configuration whose state is not `0`. -/
theorem back_core (hT : Univ.RowsOK T) (hk : T.k = 1) {q : Nat} {L R : List Nat} (hq0 : q ≠ 0)
    (hL : ∀ z ∈ L, z < bnd T) (hR : ∀ z ∈ R, z < bnd T) {u l r v : Word} (hp : (l, r) ∈ tmSRS T)
    (he : u ++ l ++ v = zw T q L R) :
    u ++ r ++ v = cword T (fstep T (mk q L.length (L ++ R))) ∨
      u ++ r ++ v = cword T (mk q L.length (L ++ R ++ [0])) := by
  rcases mem_tmSRS hp with ⟨q'', a, rr, _, ha, h0, h1, hrow, hc⟩ | ⟨q'', _, h0, h1, he'⟩ | ⟨x, _, he' | he'⟩
  · have har : a ≠ rbS T := by unfold rbS; omega
    cases hm : mv rr with
    | R =>
      rw [cellRules_R hm] at hc
      simp only [List.mem_singleton, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨hu, rfl, hv⟩ := zw_split hL hR (q' := q'') (c := u) (d := a :: v) (by rw [← he]; simp)
      obtain ⟨R', rfl, rfl⟩ := head_split hv har
      left; rw [res_R hT hk h0 h1 hrow hm, ← hu]; simp [zw]
    | S =>
      rw [cellRules_S hm] at hc
      simp only [List.mem_singleton, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨hu, rfl, hv⟩ := zw_split hL hR (q' := q'') (c := u) (d := a :: v) (by rw [← he]; simp)
      obtain ⟨R', rfl, rfl⟩ := head_split hv har
      left; rw [res_S hT hk h0 h1 hrow hm, ← hu]; simp [zw]
    | L =>
      rw [cellRules_L hm] at hc
      simp only [List.mem_cons, List.mem_map, List.mem_range, Prod.mk.injEq] at hc
      rcases hc with ⟨rfl, rfl⟩ | ⟨c, hc, rfl, rfl⟩
      · obtain ⟨hu, rfl, hv⟩ := zw_split hL hR (q' := q'') (c := u ++ [lbS T]) (d := a :: v) (by rw [← he]; simp)
        obtain ⟨R', rfl, rfl⟩ := head_split hv har
        rcases nil_or_snoc L with rfl | ⟨L', c', rfl⟩
        · have : u = [] := by simpa using hu
          subst this
          left; rw [res_L0 hT hk h0 h1 hrow hm]; simp [zw]
        · exfalso
          have h2 := (List.append_inj' (s₁ := lbS T :: L') (t₁ := [c']) (s₂ := u) (t₂ := [lbS T]) (by simpa using hu) rfl).2
          have := hL c' (by simp)
          simp only [List.cons.injEq, and_true] at h2
          rw [h2] at this; unfold lbS at this; omega
      · obtain ⟨hu, rfl, hv⟩ := zw_split hL hR (q' := q'') (c := u ++ [c]) (d := a :: v) (by rw [← he]; simp)
        obtain ⟨R', rfl, rfl⟩ := head_split hv har
        rcases nil_or_snoc L with rfl | ⟨L', c', rfl⟩
        · exfalso
          have h2 := (List.append_inj' (s₁ := []) (t₁ := [lbS T]) (s₂ := u) (t₂ := [c]) (by simpa using hu) rfl).2
          simp only [List.cons.injEq, and_true] at h2
          rw [← h2] at hc; unfold lbS at hc; omega
        · have h2 := List.append_inj' (s₁ := lbS T :: L') (t₁ := [c']) (s₂ := u) (t₂ := [c]) (by simpa using hu) rfl
          obtain ⟨rfl, h3⟩ := h2
          simp only [List.cons.injEq, and_true] at h3
          subst h3
          left; rw [res_L1 hT hk h0 h1 hrow hm L' c']; simp [zw]
  · simp only [endRule, Prod.mk.injEq] at he'
    obtain ⟨rfl, rfl⟩ := he'
    obtain ⟨hu, rfl, hv⟩ := zw_split hL hR (q' := q'') (c := u) (d := rbS T :: v) (by rw [← he]; simp)
    cases R with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, true_and] at hv
      subst hv
      right; rw [show L ++ [] ++ [0] = L ++ [0] by simp, cword_mk, ← hu]; simp [zw]
    | cons r0 R' =>
      exfalso
      simp only [List.cons_append, List.cons.injEq] at hv
      have := hR r0 (by simp)
      rw [hv.1] at this; unfold rbS at this; omega
  · simp only [Prod.mk.injEq] at he'
    obtain ⟨rfl, rfl⟩ := he'
    exfalso
    exact hq0 (zw_split hL hR (q' := 0) (c := u ++ [x]) (d := v) (by rw [← he]; simp)).2.1
  · simp only [Prod.mk.injEq] at he'
    obtain ⟨rfl, rfl⟩ := he'
    exfalso
    exact hq0 (zw_split hL hR (q' := 0) (c := u) (d := x :: v) (by rw [← he]; simp)).2.1

/-- **Backward**: a rewrite of the word of a configuration whose state is not `0` gives the word of its successor
or of the same configuration with one more trailing blank. -/
theorem back_step (hT : Univ.RowsOK T) (hk : T.k = 1) {q p : Nat} {t : List Nat} (hq0 : q ≠ 0)
    (hp : p ≤ t.length) (ht : ∀ z ∈ t, z < bnd T) {x y : Word} (h : SRStep (tmSRS T) x y)
    (hx : x = cword T (mk q p t)) :
    y = cword T (fstep T (mk q p t)) ∨ y = cword T (mk q p (t ++ [0])) := by
  obtain ⟨L, R, rfl, rfl⟩ : ∃ L R, t = L ++ R ∧ p = L.length :=
    ⟨t.take p, t.drop p, (List.take_append_drop p t).symm, by simp; omega⟩
  cases h with
  | rw u v l r hr =>
    rw [cword_mk] at hx
    exact back_core hT hk hq0 (fun z hz => ht z (by simp [hz])) (fun z hz => ht z (by simp [hz])) hr hx

end Complexity.Undec
