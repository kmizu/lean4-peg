import MacroPeg.HigherOrder.Flat.Iterate

/-!
# Type inference that also writes the items

`inferE R Γ e` computes the type of `e` (types are unique: a lambda carries its binder type, an application takes its
argument type from the function) together with the items of the typed term.

* `inferE_sound`: a success gives a typed term with that erasure and those items;
* `inferE_complete`: a typable expression is inferred.
-/

namespace Shallot.MacroPeg.Flat

open Shallot.MacroPeg.HO

variable (R : List HO.Ty)

/-- The type of `e` in context `Γ`, and the items of its typed term. -/
def inferE : List HO.Ty → HExp → Option (HO.Ty × List Item)
  | Γ, .eps => some (.p, [⟨.leaf .eps, Γ⟩])
  | Γ, .any => some (.p, [⟨.leaf .any, Γ⟩])
  | Γ, .chr c => some (.p, [⟨.leaf (.chr c), Γ⟩])
  | Γ, .range lo hi => some (.p, [⟨.leaf (.range lo hi), Γ⟩])
  | Γ, .lit s => some (.p, [⟨.leaf (.lit s), Γ⟩])
  | Γ, .seq a b =>
    match inferE Γ a, inferE Γ b with
    | some (.p, ia), some (.p, ib) => some (.p, ia ++ ib ++ [⟨.seq, Γ⟩])
    | _, _ => none
  | Γ, .alt a b =>
    match inferE Γ a, inferE Γ b with
    | some (.p, ia), some (.p, ib) => some (.p, ia ++ ib ++ [⟨.alt, Γ⟩])
    | _, _ => none
  | Γ, .star a =>
    match inferE Γ a with
    | some (.p, ia) => some (.p, ia ++ [⟨.star, Γ⟩])
    | _ => none
  | Γ, .notP a =>
    match inferE Γ a with
    | some (.p, ia) => some (.p, ia ++ [⟨.notP, Γ⟩])
    | _ => none
  | Γ, .var i => (Γ[i]?).map (fun τ => (τ, [⟨.var i, Γ⟩]))
  | Γ, .rule i => (R[i]?).map (fun τ => (τ, [⟨.rule i, Γ⟩]))
  | Γ, .lam τ body =>
    match inferE (τ :: Γ) body with
    | some (σ, ib) => some (τ ⇒ σ, ib ++ [⟨.lam τ σ, Γ⟩])
    | none => none
  | Γ, .app f y =>
    match inferE Γ f, inferE Γ y with
    | some (.arr a b, i_f), some (a', iy) => if a = a' then some (b, i_f ++ iy ++ [⟨.app a b, Γ⟩]) else none
    | _, _ => none

variable {R}

/-- **Soundness**: an inferred expression is the erasure of a typed term with the inferred items. -/
theorem inferE_sound : ∀ (e : HExp) {Γ : List HO.Ty} {τ : HO.Ty} {is : List Item},
    inferE R Γ e = some (τ, is) → ∃ t : Tm R Γ τ, t.erase = e ∧ items t = is
  | .eps, _, _, _, h => by
    simp only [inferE, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨.eps, rfl, rfl⟩
  | .any, _, _, _, h => by
    simp only [inferE, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨.any, rfl, rfl⟩
  | .chr c, _, _, _, h => by
    simp only [inferE, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨.chr c, rfl, rfl⟩
  | .range lo hi, _, _, _, h => by
    simp only [inferE, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨.range lo hi, rfl, rfl⟩
  | .lit l, _, _, _, h => by
    simp only [inferE, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨.lit l, rfl, rfl⟩
  | .seq a b, Γ, τ, is, h | .alt a b, Γ, τ, is, h => by
    simp only [inferE] at h
    split at h
    · rename_i ia ib ha hb
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨ta, rfl, rfl⟩ := inferE_sound a ha
      obtain ⟨tb, rfl, rfl⟩ := inferE_sound b hb
      first
        | exact ⟨.seq ta tb, rfl, rfl⟩
        | exact ⟨.alt ta tb, rfl, rfl⟩
    · cases h
  | .star a, Γ, τ, is, h | .notP a, Γ, τ, is, h => by
    simp only [inferE] at h
    split at h
    · rename_i ia ha
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨ta, rfl, rfl⟩ := inferE_sound a ha
      first
        | exact ⟨.star ta, rfl, rfl⟩
        | exact ⟨.notP ta, rfl, rfl⟩
    · cases h
  | .var i, Γ, τ, is, h => by
    simp only [inferE, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨σ, hσ, rfl, rfl⟩ := h
    exact ⟨.var i hσ, rfl, rfl⟩
  | .rule i, Γ, τ, is, h => by
    simp only [inferE, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨σ, hσ, rfl, rfl⟩ := h
    exact ⟨.rule i hσ, rfl, rfl⟩
  | .lam a body, Γ, τ, is, h => by
    simp only [inferE] at h
    split at h
    · rename_i σ ib hb
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨tb, rfl, rfl⟩ := inferE_sound body hb
      exact ⟨.lam tb, rfl, rfl⟩
    · cases h
  | .app f y, Γ, τ, is, h => by
    simp only [inferE] at h
    split at h
    · rename_i a b i_f a' iy hf hy
      split at h
      · rename_i hab
        subst hab
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨tf, rfl, rfl⟩ := inferE_sound f hf
        obtain ⟨ty, rfl, rfl⟩ := inferE_sound y hy
        exact ⟨.app tf ty, rfl, rfl⟩
      · cases h
    · cases h

/-- **Completeness**: a typable expression is inferred, with its type. -/
theorem inferE_complete {Γ : List HO.Ty} {e : HExp} {τ : HO.Ty} (h : HasTy R Γ e τ) :
    ∃ is, inferE R Γ e = some (τ, is) := by
  induction h with
  | eps | any | chr | range | lit => exact ⟨_, rfl⟩
  | @seq Γ _ _ _ _ iha ihb =>
    obtain ⟨ia, ha⟩ := iha
    obtain ⟨ib, hb⟩ := ihb
    exact ⟨ia ++ ib ++ [⟨.seq, Γ⟩], by simp [inferE, ha, hb]⟩
  | @alt Γ _ _ _ _ iha ihb =>
    obtain ⟨ia, ha⟩ := iha
    obtain ⟨ib, hb⟩ := ihb
    exact ⟨ia ++ ib ++ [⟨.alt, Γ⟩], by simp [inferE, ha, hb]⟩
  | @star Γ _ _ ih =>
    obtain ⟨ia, ha⟩ := ih
    exact ⟨ia ++ [⟨.star, Γ⟩], by simp [inferE, ha]⟩
  | @notP Γ _ _ ih =>
    obtain ⟨ia, ha⟩ := ih
    exact ⟨ia ++ [⟨.notP, Γ⟩], by simp [inferE, ha]⟩
  | @var Γ i _ h => exact ⟨[⟨.var i, Γ⟩], by simp [inferE, h]⟩
  | @rule Γ i _ h => exact ⟨[⟨.rule i, Γ⟩], by simp [inferE, h]⟩
  | @lam Γ a σ _ _ ih =>
    obtain ⟨ib, hb⟩ := ih
    exact ⟨ib ++ [⟨.lam a σ, Γ⟩], by simp [inferE, hb]⟩
  | @app Γ a b _ _ _ _ ihf ihy =>
    obtain ⟨i_f, hf⟩ := ihf
    obtain ⟨iy, hy⟩ := ihy
    exact ⟨i_f ++ iy ++ [⟨.app a b, Γ⟩], by simp [inferE, hf, hy]⟩

end Shallot.MacroPeg.Flat
