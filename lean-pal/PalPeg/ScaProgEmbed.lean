import PalPeg.ScaProg

/-!
# Embedding a component's stack program

A component works on its own stacks (`Fin K₁`, symbols `Γ₁`) and its own part of the control
(`C₁`). Placing it into the whole machine — stacks by an injective index map, symbols by an
injection with a left inverse, control by a lens — gives a program on the whole machine that
acts on the component's stacks and control exactly as the component does, and leaves everything
else alone. Components are then proved one at a time and assembled.
-/
set_option autoImplicit false
namespace PalPeg.ScaProgEmbed
open PalPeg.ScaLocal PalPeg.ScaProg

/-- Where a component lives in the whole machine. -/
structure Embed (Γ₁ C₁ Γ C : Type) (K₁ K : ℕ) where
  idx : Fin K₁ → Fin K
  idx_inj : Function.Injective idx
  sym : Γ₁ → Γ
  unsym : Γ → Γ₁
  unsym_sym : ∀ x, unsym (sym x) = x
  get : C → C₁
  set : C → C₁ → C
  get_set : ∀ c c₁, get (set c c₁) = c₁

variable {Γ₁ C₁ Γ C : Type} {K₁ K : ℕ} (e : Embed Γ₁ C₁ Γ C K₁ K)

/-- The component's stacks, read out of the whole machine. -/
def proj (st : Fin K → List Γ) : Fin K₁ → List Γ₁ := fun k => (st (e.idx k)).map e.unsym

theorem proj_view (D : ℕ) (st : Fin K → List Γ) : proj e (view D st) = view D (proj e st) := by
  funext k
  simp [proj, view, List.map_take]

/-- The component program placed into the whole machine. -/
def embed : Prog Γ₁ C₁ K₁ → Prog Γ C K
  | .skip => .skip
  | .ctl g => .ctl fun c v => e.set c (g (e.get c) (proj e v))
  | .push k x => .push (e.idx k) fun c v => e.sym (x (e.get c) (proj e v))
  | .pop k => .pop (e.idx k)
  | .copy s d => .copy (e.idx s) (e.idx d)
  | .clear k => .clear (e.idx k)
  | .seq p q => .seq (embed p) (embed q)
  | .ite b p q => .ite (fun c v => b (e.get c) (proj e v)) (embed p) (embed q)

theorem proj_update_idx (st : Fin K → List Γ) (k : Fin K₁) (l : List Γ) :
    proj e (Function.update st (e.idx k) l) = Function.update (proj e st) k (l.map e.unsym) := by
  funext j
  by_cases hj : j = k
  · subst hj; simp [proj]
  · have : e.idx j ≠ e.idx k := fun h => hj (e.idx_inj h)
    simp [proj, Function.update_of_ne hj, Function.update_of_ne this]

/-- **The embedded program acts on the component as the component does.** -/
theorem eval_embed (peek : ℕ) :
    ∀ (p : Prog Γ₁ C₁ K₁) (c : C) (st : Fin K → List Γ),
      e.get ((embed e p).eval peek c st).1 = (p.eval peek (e.get c) (proj e st)).1 ∧
      proj e ((embed e p).eval peek c st).2 = (p.eval peek (e.get c) (proj e st)).2
  | .skip, c, st => ⟨rfl, rfl⟩
  | .ctl g, c, st => by
    refine ⟨?_, rfl⟩
    simp [embed, Prog.eval, e.get_set, proj_view]
  | .push k x, c, st => by
    refine ⟨rfl, ?_⟩
    simp only [embed, Prog.eval]
    rw [proj_update_idx]
    simp [e.unsym_sym, proj_view, proj]
  | .pop k, c, st => by
    refine ⟨rfl, ?_⟩
    simp only [embed, Prog.eval]
    rw [proj_update_idx]
    simp [proj, List.map_tail]
  | .copy s d, c, st => by
    refine ⟨rfl, ?_⟩
    simp only [embed, Prog.eval]
    rw [proj_update_idx]
    rfl
  | .clear k, c, st => by
    refine ⟨rfl, ?_⟩
    simp only [embed, Prog.eval]
    rw [proj_update_idx]
    rfl
  | .seq p q, c, st => by
    obtain ⟨h1, h2⟩ := eval_embed peek p c st
    obtain ⟨h3, h4⟩ := eval_embed peek q ((embed e p).eval peek c st).1
      ((embed e p).eval peek c st).2
    simp only [embed, Prog.eval]
    rw [h3, h4, h1, h2]
    exact ⟨rfl, rfl⟩
  | .ite b p q, c, st => by
    simp only [embed, Prog.eval, proj_view]
    split
    · exact eval_embed peek p c st
    · exact eval_embed peek q c st

/-- **The embedded program leaves the other stacks alone.** -/
theorem eval_embed_other (peek : ℕ) :
    ∀ (p : Prog Γ₁ C₁ K₁) (c : C) (st : Fin K → List Γ) (j : Fin K), (∀ k, e.idx k ≠ j) →
      ((embed e p).eval peek c st).2 j = st j
  | .skip, _, _, _, _ => rfl
  | .ctl _, _, _, _, _ => rfl
  | .push k _, _, _, j, hj => by simp [embed, Prog.eval, Function.update_of_ne (hj k).symm]
  | .pop k, _, _, j, hj => by simp [embed, Prog.eval, Function.update_of_ne (hj k).symm]
  | .copy _ d, _, _, j, hj => by simp [embed, Prog.eval, Function.update_of_ne (hj d).symm]
  | .clear k, _, _, j, hj => by simp [embed, Prog.eval, Function.update_of_ne (hj k).symm]
  | .seq p q, c, st, j, hj => by
    simp only [embed, Prog.eval]
    rw [eval_embed_other peek q _ _ j hj, eval_embed_other peek p c st j hj]
  | .ite b p q, c, st, j, hj => by
    simp only [embed, Prog.eval]
    split
    · exact eval_embed_other peek p c st j hj
    · exact eval_embed_other peek q c st j hj

/-- **An embedded program does not disturb another, disjoint component.** -/
theorem eval_embed_frame {Γ₂ C₂ : Type} {K₂ : ℕ} (e₂ : Embed Γ₂ C₂ Γ C K₂ K) (peek : ℕ)
    (hidx : ∀ k₁ k₂, e.idx k₁ ≠ e₂.idx k₂) (hctl : ∀ c x, e₂.get (e.set c x) = e₂.get c) :
    ∀ (p : Prog Γ₁ C₁ K₁) (c : C) (st : Fin K → List Γ),
      e₂.get ((embed e p).eval peek c st).1 = e₂.get c ∧
      proj e₂ ((embed e p).eval peek c st).2 = proj e₂ st := by
  intro p c st
  refine ⟨?_, ?_⟩
  · induction p generalizing c st with
    | skip => rfl
    | ctl g => exact hctl _ _
    | push => rfl
    | pop => rfl
    | copy => rfl
    | clear => rfl
    | seq p q ihp ihq =>
      simp only [embed, Prog.eval]
      rw [ihq, ihp]
    | ite b p q ihp ihq =>
      simp only [embed, Prog.eval]
      split
      · exact ihp c st
      · exact ihq c st
  · funext k
    simp only [proj]
    rw [eval_embed_other e peek p c st (e₂.idx k) (fun k₁ => hidx k₁ k)]

end PalPeg.ScaProgEmbed
