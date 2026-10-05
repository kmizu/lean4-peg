import MacroPeg.HigherOrder.Typed

/-!
# Closing substitutions

To relate the meaning of an open term to runs, its free variables are replaced by closed terms. `substC σ k e`
replaces the free variable `var (k + j)` (free under `k` binders) by `σ[j]`. The one fact needed about the operational
semantics' substitution `inst` is the β-step (`inst_substC`): putting a closed `a` in for the variable bound by
`λ. substC σ 1 b` is substituting `a :: σ`.
-/

namespace Shallot.MacroPeg.HO

/-- Every variable of `e` is bound or below `k`. -/
def HExp.Cl : Nat → HExp → Prop
  | k, .var i => i < k
  | k, .lam _ b => HExp.Cl (k + 1) b
  | k, .app f a => HExp.Cl k f ∧ HExp.Cl k a
  | k, .seq a b => HExp.Cl k a ∧ HExp.Cl k b
  | k, .alt a b => HExp.Cl k a ∧ HExp.Cl k b
  | k, .star a => HExp.Cl k a
  | k, .notP a => HExp.Cl k a
  | _, _ => True

/-- Replace the free variables `var (k + j)` by `σ[j]`. -/
def HExp.substC (σ : List HExp) : Nat → HExp → HExp
  | k, .var i => if i < k then .var i else σ.getD (i - k) (.var i)
  | k, .lam τ b => .lam τ (HExp.substC σ (k + 1) b)
  | k, .app f a => .app (HExp.substC σ k f) (HExp.substC σ k a)
  | k, .seq a b => .seq (HExp.substC σ k a) (HExp.substC σ k b)
  | k, .alt a b => .alt (HExp.substC σ k a) (HExp.substC σ k b)
  | k, .star a => .star (HExp.substC σ k a)
  | k, .notP a => .notP (HExp.substC σ k a)
  | _, e => e

/-- All terms of `σ` are closed. -/
def AllClosed (σ : List HExp) : Prop := ∀ c ∈ σ, HExp.Cl 0 c

theorem HExp.Cl.mono : ∀ {k k' : Nat} {e : HExp}, HExp.Cl k e → k ≤ k' → HExp.Cl k' e
  | _, _, .var _, h, hk => by simp only [HExp.Cl] at h ⊢; omega
  | _, _, .lam _ b, h, hk => HExp.Cl.mono (e := b) h (by omega)
  | _, _, .app f a, h, hk | _, _, .seq f a, h, hk | _, _, .alt f a, h, hk =>
    ⟨HExp.Cl.mono (e := f) h.1 hk, HExp.Cl.mono (e := a) h.2 hk⟩
  | _, _, .star a, h, hk | _, _, .notP a, h, hk => HExp.Cl.mono (e := a) h hk
  | _, _, .eps, _, _ | _, _, .any, _, _ | _, _, .chr _, _, _ | _, _, .range _ _, _, _ | _, _, .lit _, _, _
  | _, _, .rule _, _, _ => trivial

/-- Substitution leaves a term alone when all its variables are bound or below `k`. -/
theorem inst_of_cl (a : HExp) : ∀ {m k : Nat} {e : HExp}, HExp.Cl m e → m ≤ k → HExp.inst a k e = e
  | _, _, .var i, h, hk => by simp only [HExp.Cl] at h; simp only [HExp.inst]; split <;> first | omega | rfl
  | m, k, .lam _ b, h, hk => by simp only [HExp.inst, inst_of_cl a (m := m + 1) (k := k + 1) (e := b) h (by omega)]
  | _, _, .app f c, h, hk => by simp only [HExp.inst, inst_of_cl a (e := f) h.1 hk, inst_of_cl a (e := c) h.2 hk]
  | _, _, .seq f c, h, hk => by simp only [HExp.inst, inst_of_cl a (e := f) h.1 hk, inst_of_cl a (e := c) h.2 hk]
  | _, _, .alt f c, h, hk => by simp only [HExp.inst, inst_of_cl a (e := f) h.1 hk, inst_of_cl a (e := c) h.2 hk]
  | _, _, .star c, h, hk => by simp only [HExp.inst, inst_of_cl a (e := c) h hk]
  | _, _, .notP c, h, hk => by simp only [HExp.inst, inst_of_cl a (e := c) h hk]
  | _, _, .eps, _, _ | _, _, .any, _, _ | _, _, .chr _, _, _ | _, _, .range _ _, _, _ | _, _, .lit _, _, _
  | _, _, .rule _, _, _ => rfl

/-- The empty substitution does nothing. -/
theorem substC_nil : ∀ (k : Nat) (e : HExp), HExp.substC [] k e = e
  | k, .var i => by simp only [HExp.substC]; split <;> simp
  | k, .lam _ b => by simp only [HExp.substC, substC_nil (k + 1) b]
  | k, .app f a | k, .seq f a | k, .alt f a => by simp only [HExp.substC, substC_nil k f, substC_nil k a]
  | k, .star a | k, .notP a => by simp only [HExp.substC, substC_nil k a]
  | _, .eps | _, .any | _, .chr _ | _, .range _ _ | _, .lit _ | _, .rule _ => rfl

/-- **The β-step**: putting the closed `a` in for the variable bound `k` binders up commutes with closing. -/
theorem inst_substC {a : HExp} (ha : HExp.Cl 0 a) {σ : List HExp} (hσ : AllClosed σ) :
    ∀ (k : Nat) (b : HExp), HExp.inst a k (HExp.substC σ (k + 1) b) = HExp.substC (a :: σ) k b
  | k, .var i => by
    simp only [HExp.substC]
    by_cases h₁ : i < k
    · have : i < k + 1 := by omega
      simp only [this, h₁, ↓reduceIte, HExp.inst, show i ≠ k by omega]
    · by_cases h₂ : i = k
      · subst h₂; simp [HExp.inst]
      · have hn : ¬ i < k + 1 := by omega
        simp only [hn, h₁, ↓reduceIte]
        rw [show i - k = (i - (k + 1)) + 1 by omega, List.getD_cons_succ]
        cases hc : σ[i - (k + 1)]? with
        | none =>
          rw [List.getD_eq_getElem?_getD, hc]
          simp only [Option.getD_none, HExp.inst, h₂, ↓reduceIte]
        | some c =>
          rw [List.getD_eq_getElem?_getD, hc, Option.getD_some]
          exact inst_of_cl a (hσ c (List.mem_of_getElem? hc)) (Nat.zero_le k)
  | k, .lam _ b => by simp only [HExp.substC, HExp.inst, inst_substC ha hσ (k + 1) b]
  | k, .app f c | k, .seq f c | k, .alt f c => by
    simp only [HExp.substC, HExp.inst, inst_substC ha hσ k f, inst_substC ha hσ k c]
  | k, .star c | k, .notP c => by simp only [HExp.substC, HExp.inst, inst_substC ha hσ k c]
  | _, .eps | _, .any | _, .chr _ | _, .range _ _ | _, .lit _ | _, .rule _ => rfl

/-- Closing a term whose free variables are covered by `σ` gives a closed term. -/
theorem cl_substC {σ : List HExp} (hσ : AllClosed σ) :
    ∀ (k : Nat) (e : HExp), HExp.Cl (k + σ.length) e → HExp.Cl k (HExp.substC σ k e)
  | k, .var i, h => by
    simp only [HExp.Cl] at h
    simp only [HExp.substC]
    split
    · simp only [HExp.Cl]; assumption
    · rename_i hik
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact HExp.Cl.mono (hσ _ (List.getElem_mem _)) (Nat.zero_le k)
  | k, .lam _ b, h => cl_substC hσ (k + 1) b (by simp only [HExp.Cl] at h; rwa [Nat.add_right_comm])
  | k, .app f a, h | k, .seq f a, h | k, .alt f a, h => ⟨cl_substC hσ k f h.1, cl_substC hσ k a h.2⟩
  | k, .star a, h | k, .notP a, h => cl_substC hσ k a h
  | _, .eps, _ | _, .any, _ | _, .chr _, _ | _, .range _ _, _ | _, .lit _, _ | _, .rule _, _ => trivial

/-- A typed term's free variables are those of its context. -/
theorem Tm.cl_erase {R : List Ty} : ∀ {Γ : List Ty} {τ : Ty} (t : Tm R Γ τ), HExp.Cl Γ.length t.erase
  | _, _, .var _ h => by
    simp only [Tm.erase, HExp.Cl]
    exact (List.getElem?_eq_some_iff.1 h).1
  | _, _, .lam body => body.cl_erase
  | _, _, .app f y => ⟨f.cl_erase, y.cl_erase⟩
  | _, _, .seq a b => ⟨a.cl_erase, b.cl_erase⟩
  | _, _, .alt a b => ⟨a.cl_erase, b.cl_erase⟩
  | _, _, .star a => a.cl_erase
  | _, _, .notP a => a.cl_erase
  | _, _, .eps | _, _, .any | _, _, .chr _ | _, _, .range _ _ | _, _, .lit _ | _, _, .rule _ _ => trivial

end Shallot.MacroPeg.HO
