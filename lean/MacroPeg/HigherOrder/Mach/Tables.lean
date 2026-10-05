import MacroPeg.HigherOrder.Flat.Decider

/-!
# Types and contexts as numbers

The machine names types by numbers: `0` is `p`, `k + 1` is the arrow `tt[k] = (a, b)`, an arrow between two types with
smaller numbers. Arrows are registered without repetition (`intern`), so equal types have equal numbers
(`tyOf_inj`). Contexts are numbers too: `0` is the empty context, `k + 1` extends context `ct[k].1` by the type
`ct[k].2`, innermost first.
-/

namespace Shallot.MacroPeg.Mach

open Shallot.MacroPeg.HO

/-! ## Types -/

/-- The type with number `i` (if the table is well formed). -/
def tyOf (tt : List (Nat × Nat)) : Nat → Option HO.Ty
  | 0 => some .p
  | k + 1 =>
    match tt[k]? with
    | some (a, b) =>
      if a ≤ k ∧ b ≤ k then
        match tyOf tt a, tyOf tt b with
        | some σ, some τ => some (σ ⇒ τ)
        | _, _ => none
      else none
    | none => none
termination_by i => i
decreasing_by all_goals omega

/-- Register the arrow `a ⇒ b`: its number, and the table. -/
def intern (tt : List (Nat × Nat)) (a b : Nat) : List (Nat × Nat) × Nat :=
  if (a, b) ∈ tt then (tt, indexIn (a, b) tt + 1) else (tt ++ [(a, b)], tt.length + 1)

/-- A well-formed table: every arrow refers to smaller numbers, nothing is repeated, every entry decodes. -/
def TTWF (tt : List (Nat × Nat)) : Prop :=
  tt.Nodup ∧ ∀ k (h : k < tt.length), tt[k].1 ≤ k ∧ tt[k].2 ≤ k

theorem tyOf_getElem? {tt : List (Nat × Nat)} {k a b : Nat} (h : tt[k]? = some (a, b)) (ha : a ≤ k) (hb : b ≤ k) :
    tyOf tt (k + 1) = match tyOf tt a, tyOf tt b with
      | some σ, some τ => some (σ ⇒ τ)
      | _, _ => none := by
  rw [tyOf]; simp only [h, ha, hb, and_self, if_true]

/-- Every number below the table's end decodes. -/
theorem tyOf_some {tt : List (Nat × Nat)} (hw : TTWF tt) : ∀ i, i ≤ tt.length → ∃ τ, tyOf tt i = some τ
  | 0, _ => ⟨.p, by rw [tyOf]⟩
  | k + 1, hk => by
    have hlt : k < tt.length := by omega
    obtain ⟨ha, hb⟩ := hw.2 k hlt
    obtain ⟨σ, hσ⟩ := tyOf_some hw tt[k].1 (by omega)
    obtain ⟨τ, hτ⟩ := tyOf_some hw tt[k].2 (by omega)
    refine ⟨σ ⇒ τ, ?_⟩
    rw [tyOf_getElem? (a := tt[k].1) (b := tt[k].2) (by simp [hlt]) ha hb, hσ, hτ]

/-- Extending the table keeps the old numbers. -/
theorem tyOf_append {tt : List (Nat × Nat)} (hw : TTWF tt) (e : List (Nat × Nat)) :
    ∀ i, i ≤ tt.length → tyOf (tt ++ e) i = tyOf tt i
  | 0, _ => by rw [tyOf, tyOf]
  | k + 1, hk => by
    have hlt : k < tt.length := by omega
    obtain ⟨ha, hb⟩ := hw.2 k hlt
    have hg : (tt ++ e)[k]? = some (tt[k].1, tt[k].2) := by
      rw [List.getElem?_append_left hlt]; simp [hlt]
    rw [tyOf_getElem? hg ha hb, tyOf_getElem? (a := tt[k].1) (b := tt[k].2) (by simp [hlt]) ha hb,
      tyOf_append hw e tt[k].1 (by omega), tyOf_append hw e tt[k].2 (by omega)]

/-- **Equal types have equal numbers.** -/
theorem tyOf_inj {tt : List (Nat × Nat)} (hw : TTWF tt) :
    ∀ n i i', i + i' ≤ n → i ≤ tt.length → i' ≤ tt.length → ∀ τ, tyOf tt i = some τ → tyOf tt i' = some τ → i = i'
  | _, 0, 0, _, _, _, _, _, _ => rfl
  | _, 0, k + 1, _, _, hk, τ, h, h' => by
    have hlt : k < tt.length := by omega
    obtain ⟨ha, hb⟩ := hw.2 k hlt
    rw [tyOf] at h
    rw [tyOf_getElem? (a := tt[k].1) (b := tt[k].2) (by simp [hlt]) ha hb] at h'
    cases h
    split at h' <;> simp at h'
  | _, k + 1, 0, _, hk, _, τ, h, h' => by
    have hlt : k < tt.length := by omega
    obtain ⟨ha, hb⟩ := hw.2 k hlt
    rw [tyOf] at h'
    rw [tyOf_getElem? (a := tt[k].1) (b := tt[k].2) (by simp [hlt]) ha hb] at h
    cases h'
    split at h <;> simp at h
  | n + 1, k + 1, k' + 1, hn, hk, hk', τ, h, h' => by
    have hlt : k < tt.length := by omega
    have hlt' : k' < tt.length := by omega
    obtain ⟨ha, hb⟩ := hw.2 k hlt
    obtain ⟨ha', hb'⟩ := hw.2 k' hlt'
    rw [tyOf_getElem? (a := tt[k].1) (b := tt[k].2) (by simp [hlt]) ha hb] at h
    rw [tyOf_getElem? (a := tt[k'].1) (b := tt[k'].2) (by simp [hlt']) ha' hb'] at h'
    split at h
    · rename_i σ ρ hσ hρ
      split at h'
      · rename_i σ' ρ' hσ' hρ'
        simp only [Option.some.injEq] at h h'
        rw [← h'] at h
        obtain ⟨rfl, rfl⟩ := HO.Ty.arr.inj h
        have e₁ := tyOf_inj hw n _ _ (by omega) (by omega) (by omega) σ hσ hσ'
        have e₂ := tyOf_inj hw n _ _ (by omega) (by omega) (by omega) ρ hρ hρ'
        have : tt[k] = tt[k'] := Prod.ext e₁ e₂
        have i₁ := Shallot.MacroPeg.Flat.indexIn_getElem hw.1 k hlt
        have i₂ := Shallot.MacroPeg.Flat.indexIn_getElem hw.1 k' hlt'
        rw [this] at i₁
        omega
      · cases h'
    · cases h

theorem intern_snd_le (tt : List (Nat × Nat)) (a b : Nat) : (intern tt a b).2 ≤ (intern tt a b).1.length := by
  unfold intern
  split
  · rename_i hm; simp only; have := Shallot.MacroPeg.Flat.indexIn_lt (a, b) tt hm; omega
  · simp

theorem intern_wf {tt : List (Nat × Nat)} (hw : TTWF tt) {a b : Nat} (ha : a ≤ tt.length) (hb : b ≤ tt.length) :
    TTWF (intern tt a b).1 := by
  unfold intern
  split
  · exact hw
  · rename_i hm
    refine ⟨List.nodup_append.2 ⟨hw.1, by simp, fun x hx y hy e => by simp at hy; subst hy; exact hm (e ▸ hx)⟩,
      fun k hk => ?_⟩
    by_cases hkl : k < tt.length
    · rw [List.getElem_append_left hkl]; exact hw.2 k hkl
    · simp at hk
      have : k = tt.length := by omega
      subst this
      simp; omega

theorem intern_prefix (tt : List (Nat × Nat)) (a b : Nat) : ∃ e, (intern tt a b).1 = tt ++ e := by
  unfold intern
  split
  · exact ⟨[], by simp⟩
  · exact ⟨[(a, b)], rfl⟩

/-- **The registered number names the arrow.** -/
theorem tyOf_intern {tt : List (Nat × Nat)} (hw : TTWF tt) {a b : Nat} (ha : a ≤ tt.length) (hb : b ≤ tt.length)
    {σ τ : HO.Ty} (hσ : tyOf tt a = some σ) (hτ : tyOf tt b = some τ) :
    tyOf (intern tt a b).1 (intern tt a b).2 = some (σ ⇒ τ) := by
  unfold intern
  split
  · rename_i hm
    simp only
    have hk := Shallot.MacroPeg.Flat.indexIn_lt (a, b) tt hm
    have hg : tt[indexIn (a, b) tt]? = some (a, b) := getElem?_indexIn _ _ hm
    have hle := hw.2 _ hk
    rw [List.getElem?_eq_getElem hk, Option.some.injEq] at hg
    rw [hg] at hle
    rw [tyOf_getElem? (getElem?_indexIn _ _ hm) hle.1 hle.2, hσ, hτ]
  · simp only
    have hg : (tt ++ [(a, b)])[tt.length]? = some (a, b) := by simp
    rw [tyOf_getElem? hg ha hb, tyOf_append hw _ a ha, tyOf_append hw _ b hb, hσ, hτ]

/-! ## Contexts -/

/-- The context with number `c`, innermost first. -/
def ctxOf (tt : List (Nat × Nat)) (ct : List (Nat × Nat)) : Nat → Option (List HO.Ty)
  | 0 => some []
  | k + 1 =>
    match ct[k]? with
    | some (par, t) =>
      if par ≤ k then
        match tyOf tt t, ctxOf tt ct par with
        | some τ, some Γ => some (τ :: Γ)
        | _, _ => none
      else none
    | none => none
termination_by c => c
decreasing_by omega

end Shallot.MacroPeg.Mach
