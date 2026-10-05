import MacroPeg.HigherOrder.Adequacy

/-!
# Completeness: the fixpoint gives the result of every run

Let `T*` be the stopped iterate (`iter_fix`). A run with fuel `n` that ends is matched by `T*`: the logical relation
`RelB τ n` — "every run with fuel `n` ends with the result the value gives" at `p`, and arguments related at every
`m ≤ n` give related applications at `a ⇒ b` — holds between every term and its meaning (`fundB`) and between every
rule and its `T*`-value (`rulesRelB_fix`). The fuel index makes the circular rule case well founded: a rule related at
`n` gives a body related at `n`, hence the rule related at `n + 1` (`relB_expand`).
-/

namespace Shallot.MacroPeg.HO

section Completeness

variable (x : List Char) (g : HGrammar)

/-- Runs of `e` with fuel `n` end with the results that `d` gives. -/
def RelB : (τ : Ty) → Nat → HExp → Dom τ → Prop
  | .p, n, e, d => ∀ q ≤ x.length, ∀ r, hrun g n e (sfx x q) = some r → atq d q = some (r.map List.length)
  | .arr a b, n, e, f => ∀ m ≤ n, ∀ e' d', HExp.Cl 0 e' → d' ∈ elems x.length a → RelB a m e' d' →
      RelB b m (.app e e') (Dom.app (N := x.length) f d')

def EnvRelB (n : Nat) : (Γ : List Ty) → List HExp → Env Γ → Prop
  | [], [], _ => True
  | τ :: Γ, c :: σ, (d, ρ) => RelB x g τ n c d ∧ EnvRelB n Γ σ ρ
  | _, _, _ => False

variable {x g}

theorem sfx_length {q : Nat} (hq : q ≤ x.length) : (sfx x q).length = q := by simp [sfx]; omega

theorem relB_zero : ∀ (τ : Ty) (e : HExp) (d : Dom τ), RelB x g τ 0 e d
  | .p, _, _ => fun q _ r h => by simp [hrun] at h
  | .arr _ b, _, _ => fun m hm _ _ _ _ _ => by
    rw [Nat.le_zero.1 hm]; exact relB_zero b _ _

theorem relB_down : ∀ (τ : Ty) {n m : Nat}, m ≤ n → ∀ {e : HExp} {d : Dom τ}, RelB x g τ n e d → RelB x g τ m e d
  | .p, _, _, hm, _, _, h => fun q hq r hr => h q hq r (hrun_mono_le hr hm)
  | .arr _ _, _, _, _hm, _, _, h => fun m' hm' => h m' (by omega)

/-- A head-reducible term is related at `n + 1` to whatever its reduct is related to at `n`. -/
theorem relB_expand : ∀ (τ : Ty) (n : Nat) {e e' : HExp} {d : Dom τ}, (∀ σ b, e ≠ .lam σ b) →
    step g e = some e' → RelB x g τ n e' d → RelB x g τ (n + 1) e d
  | .p, n, _, _, _, _, hs, h => fun q hq r hr => h q hq r (by rwa [hrun_expand hs] at hr)
  | .arr a b, n, _, _, _, hl, hs, h => fun m hm e'' d'' hc hd hrel => by
    cases m with
    | zero => exact relB_zero b _ _
    | succ k =>
      exact relB_expand b k (fun _ _ h' => by cases h') (step_app_head e'' hl hs)
        (h k (by omega) e'' d'' hc hd (relB_down a (Nat.le_succ k) hrel))

theorem EnvRelB.down {n m : Nat} (hm : m ≤ n) : ∀ {Γ : List Ty} {σ : List HExp} {ρ : Env Γ},
    EnvRelB x g n Γ σ ρ → EnvRelB x g m Γ σ ρ
  | [], [], _, _ => trivial
  | τ :: _, _ :: _, (_, _), h => ⟨relB_down τ hm h.1, EnvRelB.down hm h.2⟩
  | [], _ :: _, _, h | _ :: _, [], _, h => absurd h id

theorem EnvRelB.length {n : Nat} : ∀ {Γ : List Ty} {σ : List HExp} {ρ : Env Γ}, EnvRelB x g n Γ σ ρ →
    σ.length = Γ.length
  | [], [], _, _ => rfl
  | _ :: _, _ :: _, (_, _), h => by simp [EnvRelB.length h.2]
  | [], _ :: _, _, h | _ :: _, [], _, h => absurd h id

theorem EnvRelB.get {n : Nat} : ∀ {Γ : List Ty} {σ : List HExp} {ρ : Env Γ}, EnvRelB x g n Γ σ ρ → ∀ (i : Nat)
    {τ : Ty} (h : Γ[i]? = some τ), RelB x g τ n (σ.getD i (.var i)) (Env.get ρ i h)
  | [], _, _, _, _, _, h => absurd h (by simp)
  | _ :: _, _ :: _, (_, _), hr, 0, _, h => by cases Option.some.inj h; exact hr.1
  | _ :: Γ, _ :: σ, (_, _), hr, i + 1, _, h => by
    have := EnvRelB.get hr.2 i h
    simp only [List.getD_cons_succ]
    have hl := EnvRelB.length hr.2
    have hi : i < σ.length := by have := (List.getElem?_eq_some_iff.1 h).1; simp at this; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at this ⊢
    exact this
  | _ :: _, [], _, hr, _, _, _ => absurd hr id

/-! ## Leaves and PEG operators -/

/-- A success leaves a position. -/
theorem sfx_rest {q : Nat} (_hq : q ≤ x.length) {y : List Char} (h : ∃ p, sfx x q = p ++ y) :
    y = sfx x y.length ∧ y.length ≤ x.length := by
  have hy := suffix_trans (sfx_suffix q) h
  refine ⟨(sfx_of_suffix hy).symm, ?_⟩
  obtain ⟨p, hp⟩ := hy
  have := congrArg List.length hp
  simp at this; omega

theorem relB_leaf {e : HExp} (he : e = .eps ∨ e = .any ∨ (∃ c, e = .chr c) ∨ (∃ lo hi, e = .range lo hi) ∨
    (∃ s, e = .lit s)) (n : Nat) : RelB x g .p n e (baseVec x (leafRes x e)) := by
  intro q hq r h
  rw [atq_baseVec hq]
  cases n with
  | zero => simp [hrun] at h
  | succ n => rw [hrun_leaf he ⟨[]⟩ n] at h; simp [leafRes, h]

theorem relB_seq {n : Nat} {A B : HExp} {da db : Dom .p} (ha : RelB x g .p n A da) (hb : RelB x g .p n B db) :
    RelB x g .p n (.seq A B) (baseVec x (seqRes da db)) := by
  intro q hq r h
  rw [atq_baseVec hq]
  cases n with
  | zero => simp [hrun] at h
  | succ k =>
    rw [hrun_seq] at h
    unfold seqRes
    cases hA : hrun g k A (sfx x q) with
    | none => rw [hA] at h; cases h
    | some ra =>
      rw [ha q hq ra (hrun_mono hA)]
      rw [hA] at h
      cases ra with
      | none => cases h; rfl
      | some y =>
        obtain ⟨hy, hyl⟩ := sfx_rest hq (hrun_suffix hA)
        rw [hy] at h
        exact hb _ hyl r (hrun_mono h)

theorem relB_alt {n : Nat} {A B : HExp} {da db : Dom .p} (ha : RelB x g .p n A da) (hb : RelB x g .p n B db) :
    RelB x g .p n (.alt A B) (baseVec x (altRes da db)) := by
  intro q hq r h
  rw [atq_baseVec hq]
  cases n with
  | zero => simp [hrun] at h
  | succ k =>
    rw [hrun_alt] at h
    unfold altRes
    cases hA : hrun g k A (sfx x q) with
    | none => rw [hA] at h; cases h
    | some ra =>
      rw [ha q hq ra (hrun_mono hA)]
      rw [hA] at h
      cases ra with
      | none => exact hb q hq r (hrun_mono h)
      | some y => cases h; rfl

theorem relB_notP {n : Nat} {A : HExp} {da : Dom .p} (ha : RelB x g .p n A da) :
    RelB x g .p n (.notP A) (baseVec x (notRes da)) := by
  intro q hq r h
  rw [atq_baseVec hq]
  cases n with
  | zero => simp [hrun] at h
  | succ k =>
    rw [hrun_notP] at h
    unfold notRes
    cases hA : hrun g k A (sfx x q) with
    | none => rw [hA] at h; cases h
    | some ra =>
      rw [ha q hq ra (hrun_mono hA)]
      rw [hA] at h
      cases ra with
      | none => cases h; simp [sfx_length hq]
      | some y => cases h; rfl

theorem relB_star {n : Nat} {A : HExp} {da : Dom .p} (ha : RelB x g .p n A da) :
    RelB x g .p n (.star A) (baseVec x (starRes da)) := by
  intro q hq r h
  rw [atq_baseVec hq]
  -- induction on the fuel of the run of the star
  have key : ∀ k ≤ n, ∀ q ≤ x.length, ∀ r, hrun g k (.star A) (sfx x q) = some r →
      starRes da q = some (r.map List.length) := by
    intro k
    induction k with
    | zero => intro _ q _ r h; simp [hrun] at h
    | succ k ih =>
      intro hk q hq r h
      rw [hrun_star] at h
      cases hA : hrun g k A (sfx x q) with
      | none => rw [hA] at h; cases h
      | some ra =>
        have hda := ha q hq ra (hrun_mono_le hA (by omega))
        rw [hA] at h
        rw [starRes, hda]
        cases ra with
        | none => cases h; simp [sfx_length hq]
        | some y =>
          obtain ⟨hy, hyl⟩ := sfx_rest hq (hrun_suffix hA)
          have hyq : y.length ≤ q := by
            obtain ⟨p, hp⟩ := hrun_suffix hA
            have := congrArg List.length hp
            rw [sfx_length hq] at this; simp at this; omega
          rw [hy] at h
          have hrec := ih (by omega) _ hyl r h
          simp only [Option.map_some]
          by_cases hlt : y.length < q
          · simp only [hlt, ↓reduceIte]; exact hrec
          · -- a zero-width success loops: the star's value at `q` is undefined, contradicting `hrec`
            have heq : y.length = q := by omega
            rw [heq, starRes, hda] at hrec
            simp [heq] at hrec
  exact key n (Nat.le_refl _) q hq r h

variable {R : List Ty}

def RulesRelB (x : List Char) (g : HGrammar) (n : Nat) (T : Env R) : Prop :=
  ∀ (i : Nat) {τ : Ty} (h : R[i]? = some τ), RelB x g τ n (.rule i) (Env.get T i h)

theorem RulesRelB.down {n m : Nat} (hm : m ≤ n) {T : Env R} (h : RulesRelB x g n T) : RulesRelB x g m T :=
  fun i _ hi => relB_down _ hm (h i hi)

/-- **The fundamental lemma of completeness.** -/
theorem fundB {T : Env R} (hT : Env.Mem x.length T) : ∀ (n : Nat), RulesRelB x g n T →
    ∀ {Γ : List Ty} {τ : Ty} (t : Tm R Γ τ) (σ : List HExp) (ρ : Env Γ), AllClosed σ → Env.Mem x.length ρ →
      EnvRelB x g n Γ σ ρ → RelB x g τ n (HExp.substC σ 0 t.erase) (den x t T ρ)
  | n, _, _, _, .eps, _, _, _, _, _ => relB_leaf (.inl rfl) n
  | n, _, _, _, .any, _, _, _, _, _ => relB_leaf (.inr (.inl rfl)) n
  | n, _, _, _, .chr c, _, _, _, _, _ => relB_leaf (.inr (.inr (.inl ⟨c, rfl⟩))) n
  | n, _, _, _, .range lo hi, _, _, _, _, _ => relB_leaf (.inr (.inr (.inr (.inl ⟨lo, hi, rfl⟩)))) n
  | n, _, _, _, .lit s, _, _, _, _, _ => relB_leaf (.inr (.inr (.inr (.inr ⟨s, rfl⟩)))) n
  | n, hR, _, _, .seq a b, σ, ρ, hσ, hρ, he =>
    relB_seq (fundB hT n hR a σ ρ hσ hρ he) (fundB hT n hR b σ ρ hσ hρ he)
  | n, hR, _, _, .alt a b, σ, ρ, hσ, hρ, he =>
    relB_alt (fundB hT n hR a σ ρ hσ hρ he) (fundB hT n hR b σ ρ hσ hρ he)
  | n, hR, _, _, .star a, σ, ρ, hσ, hρ, he => relB_star (fundB hT n hR a σ ρ hσ hρ he)
  | n, hR, _, _, .notP a, σ, ρ, hσ, hρ, he => relB_notP (fundB hT n hR a σ ρ hσ hρ he)
  | _, _, _, _, .var i h, _, _, _, _, he => by
    simp only [Tm.erase, HExp.substC, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
    exact he.get i h
  | _, hR, _, _, .rule i h, _, _, _, _, _ => hR i h
  | n, hR, _, _, @Tm.lam _ _ a b body, σ, ρ, hσ, hρ, he => by
    intro m hm e' d' hc hd hrel
    simp only [den]
    rw [app_tab _ hd]
    cases m with
    | zero => exact relB_zero b _ _
    | succ k =>
      apply relB_expand b k (fun _ _ h' => by cases h') (e' := HExp.inst e' 0 (HExp.substC σ (0 + 1) body.erase)) rfl
      rw [inst_substC hc hσ 0]
      exact fundB hT k (hR.down (by omega)) body (e' :: σ) (d', ρ)
        (fun c hcm => by
          rcases List.mem_cons.1 hcm with rfl | hcm
          · exact hc
          · exact hσ c hcm)
        ⟨hd, hρ⟩ ⟨relB_down a (Nat.le_succ k) hrel, he.down (by omega)⟩
  | n, hR, _, _, .app f y, σ, ρ, hσ, hρ, he => by
    have hf := fundB hT n hR f σ ρ hσ hρ he
    have hy := fundB hT n hR y σ ρ hσ hρ he
    have hcl : HExp.Cl 0 (HExp.substC σ 0 y.erase) :=
      cl_substC hσ 0 _ (by rw [Nat.zero_add, EnvRelB.length he]; exact y.cl_erase)
    exact hf n (Nat.le_refl _) _ _ hcl (den_mono x y hT hT (Env.le_refl T) hρ hρ (Env.le_refl ρ)).1 hy

variable (G : TGrammar R)

/-- Every rule is related at every fuel to its value in the stopped iterate. -/
theorem rulesRelB_fix : ∀ n, RulesRelB x G.erase n (iter x G (maxEnv x.length R))
  | 0 => fun _ _ _ => relB_zero _ _ _
  | n + 1 => fun i τ h => by
    have hfix := iter_fix x G
    rw [show Env.get (iter x G (maxEnv x.length R)) i h = _ from
      (congrArg (fun E => Env.get E i h) hfix).symm, TBodies.den_get]
    apply relB_expand τ n (fun _ _ h' => by cases h') (step_rule G h)
    have := fundB (iter_mem x G _) n (rulesRelB_fix n) (G.bodies.get i h) [] () (by simp [AllClosed]) trivial trivial
    rwa [substC_nil] at this

/-- **Completeness**: the result of a run is the stopped iterate's value at the full input. -/
theorem complete_fix (t : Tm R [] .p) {n : Nat} {r : Option (List Char)} (h : hrun G.erase n t.erase x = some r) :
    atq (den x t (iter x G (maxEnv x.length R)) ()) x.length = some (r.map List.length) := by
  have := fundB (iter_mem x G _) n (rulesRelB_fix G n) t [] () (by simp [AllClosed]) trivial trivial
  rw [substC_nil] at this
  exact this x.length (Nat.le_refl _) r (by rw [sfx_full]; exact h)

end Completeness

end Shallot.MacroPeg.HO
