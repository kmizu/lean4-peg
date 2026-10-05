import MacroPeg.HigherOrder.Denote
import MacroPeg.HigherOrder.Subst
import MacroPeg.HigherOrder.Embed

/-!
# The finite model agrees with the runs

Fix a typed grammar `G` and an input `x`; `g = G.erase` is the untyped grammar that `hrun` runs.

* **Soundness** (`sound_iter`): a result that an iterate gives a closed parser `t` at the full input is a result of a
  run of `t.erase`. Proof: the logical relation `RelA` — "every result the value has is a result of a run" at `p`,
  and related arguments give related applications at `a ⇒ b` — holds between every term (closed by related terms) and
  its meaning (`fundA`), and between every rule and its iterate (`rulesRelA_iter`).
* **Completeness** (`complete_fix`, in `Complete.lean`): a run's result is given by the fixpoint.

Both use that the run of a head-reducible term is the run of its reduct (`hobs_expand`), the β-lemma of `Subst.lean`,
and the position-wise operators of `Denote.lean`.
-/

namespace Shallot.MacroPeg.HO

/-! ## Rule bodies -/

section Bodies

variable {R : List Ty}

/-- The body of rule `i`. -/
def TBodies.get : {S : List Ty} → TBodies R S → (i : Nat) → {τ : Ty} → S[i]? = some τ → Tm R [] τ
  | [], _, _, _, h => absurd h (by simp)
  | _ :: _, (t, _), 0, _, h => (Option.some.inj h) ▸ t
  | _ :: _, (_, ts), i + 1, _, h => TBodies.get ts i h

theorem TBodies.den_get (x : List Char) (T : Env R) : ∀ {S : List Ty} (ts : TBodies R S) (i : Nat) {τ : Ty}
    (h : S[i]? = some τ), Env.get (ts.den x T) i h = HO.den x (ts.get i h) T ()
  | [], _, _, _, h => absurd h (by simp)
  | _ :: _, (_, _), 0, _, h => by cases Option.some.inj h; rfl
  | _ :: _, (_, ts), i + 1, _, h => TBodies.den_get x T ts i h

theorem TBodies.rule_get : ∀ {S : List Ty} (ts : TBodies R S) (i : Nat) {τ : Ty} (h : S[i]? = some τ),
    (List.zipWith (fun τ b => (⟨τ, b⟩ : HRule)) S ts.erase)[i]? = some ⟨τ, (ts.get i h).erase⟩
  | [], _, _, _, h => absurd h (by simp)
  | _ :: _, (_, _), 0, _, h => by cases Option.some.inj h; rfl
  | _ :: _, (_, ts), i + 1, _, h => by
    simp only [TBodies.erase, List.zipWith_cons_cons, List.getElem?_cons_succ]
    exact TBodies.rule_get ts i h

/-- A rule reduces to its body. -/
theorem step_rule (G : TGrammar R) {i : Nat} {τ : Ty} (h : R[i]? = some τ) :
    step G.erase (.rule i) = some (G.bodies.get i h).erase := by
  simp [step, TGrammar.erase, TBodies.rule_get _ i h]

theorem Env.get_bot (N : Nat) : ∀ {Γ : List Ty} (i : Nat) {τ : Ty} (h : Γ[i]? = some τ),
    Env.get (Env.bot N Γ) i h = HO.bot N τ
  | [], _, _, h => absurd h (by simp)
  | _ :: _, 0, _, h => by cases Option.some.inj h; rfl
  | _ :: _, i + 1, _, h => Env.get_bot N i h

end Bodies

/-! ## Runs: head expansion and the PEG operators -/

section Runs

variable {g : HGrammar} {y : List Char}

theorem isHead_of_step {e e' : HExp} (h : step g e = some e') : e.isHead = true := by
  cases e <;> simp_all [step, HExp.isHead]

/-- A head-reducible term runs as its reduct. -/
theorem hrun_expand {e e' : HExp} (hs : step g e = some e') (n : Nat) : hrun g (n + 1) e y = hrun g n e' y := by
  rw [hrun_head (isHead_of_step hs), hs]

theorem hobs_expand {e e' : HExp} {r : Option (List Char)} (hs : step g e = some e') (h : HObs g e' y r) :
    HObs g e y r := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, by rw [hrun_expand hs]; exact hn⟩

theorem step_app_head {e e' : HExp} (a : HExp) (hl : ∀ τ b, e ≠ .lam τ b) (hs : step g e = some e') :
    step g (.app e a) = some (.app e' a) := step_app a hs hl

/-- Two runs, with the fuel of the longer. -/
theorem hobs_max {A B : HExp} {y₁ y₂ : List Char} {r₁ r₂ : Option (List Char)} (h₁ : HObs g A y₁ r₁)
    (h₂ : HObs g B y₂ r₂) : ∃ n, hrun g n A y₁ = some r₁ ∧ hrun g n B y₂ = some r₂ := by
  obtain ⟨n₁, e₁⟩ := h₁
  obtain ⟨n₂, e₂⟩ := h₂
  exact ⟨max n₁ n₂, hrun_mono_le e₁ (Nat.le_max_left _ _), hrun_mono_le e₂ (Nat.le_max_right _ _)⟩

theorem hobs_seq_ok {A B : HExp} {y' : List Char} {r : Option (List Char)} (hA : HObs g A y (some y'))
    (hB : HObs g B y' r) : HObs g (.seq A B) y r := by
  obtain ⟨n, h₁, h₂⟩ := hobs_max hA hB
  exact ⟨n + 1, by rw [hrun_seq, h₁]; exact h₂⟩

theorem hobs_seq_fail {A B : HExp} (hA : HObs g A y none) : HObs g (.seq A B) y none := by
  obtain ⟨n, h⟩ := hA
  exact ⟨n + 1, by rw [hrun_seq, h]⟩

theorem hobs_alt_ok {A B : HExp} {y' : List Char} (hA : HObs g A y (some y')) : HObs g (.alt A B) y (some y') := by
  obtain ⟨n, h⟩ := hA
  exact ⟨n + 1, by rw [hrun_alt, h]⟩

theorem hobs_alt_fail {A B : HExp} {r : Option (List Char)} (hA : HObs g A y none) (hB : HObs g B y r) :
    HObs g (.alt A B) y r := by
  obtain ⟨n, h₁, h₂⟩ := hobs_max hA hB
  exact ⟨n + 1, by rw [hrun_alt, h₁]; exact h₂⟩

theorem hobs_not_ok {A : HExp} {y' : List Char} (hA : HObs g A y (some y')) : HObs g (.notP A) y none := by
  obtain ⟨n, h⟩ := hA
  exact ⟨n + 1, by rw [hrun_notP, h]⟩

theorem hobs_not_fail {A : HExp} (hA : HObs g A y none) : HObs g (.notP A) y (some y) := by
  obtain ⟨n, h⟩ := hA
  exact ⟨n + 1, by rw [hrun_notP, h]⟩

theorem hobs_star_fail {A : HExp} (hA : HObs g A y none) : HObs g (.star A) y (some y) := by
  obtain ⟨n, h⟩ := hA
  exact ⟨n + 1, by rw [hrun_star, h]⟩

theorem hobs_star_ok {A : HExp} {y' : List Char} {r : Option (List Char)} (hA : HObs g A y (some y'))
    (hS : HObs g (.star A) y' r) : HObs g (.star A) y r := by
  obtain ⟨n, h₁, h₂⟩ := hobs_max hA hS
  exact ⟨n + 1, by rw [hrun_star, h₁]; exact h₂⟩

/-- Leaves do not depend on the grammar or on more fuel. -/
theorem hrun_leaf {e : HExp} (he : e = .eps ∨ e = .any ∨ (∃ c, e = .chr c) ∨ (∃ lo hi, e = .range lo hi) ∨
    (∃ s, e = .lit s)) (g' : HGrammar) (n : Nat) : hrun g (n + 1) e y = hrun g' 1 e y := by
  rcases he with rfl | rfl | ⟨c, rfl⟩ | ⟨lo, hi, rfl⟩ | ⟨s, rfl⟩ <;> rw [hrun.eq_def, hrun.eq_def]

end Runs

/-! ## Suffixes of the input -/

section Suffixes

variable {x : List Char}

theorem sfx_suffix (q : Nat) : ∃ p, x = p ++ sfx x q := ⟨x.take (x.length - q), by simp [sfx]⟩

theorem sfx_of_suffix {r : List Char} (h : ∃ p, x = p ++ r) : sfx x r.length = r := by
  obtain ⟨p, rfl⟩ := h
  simp [sfx]

theorem sfx_full : sfx x x.length = x := by simp [sfx]

theorem suffix_trans {a b c : List Char} (h₁ : ∃ p, a = p ++ b) (h₂ : ∃ p, b = p ++ c) : ∃ p, a = p ++ c := by
  obtain ⟨p₁, rfl⟩ := h₁
  obtain ⟨p₂, rfl⟩ := h₂
  exact ⟨p₁ ++ p₂, by simp⟩

theorem atq_baseVec {f : Nat → Res} {q : Nat} (hq : q ≤ x.length) : atq (baseVec x f) q = f q := by
  simp only [atq, baseVec, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (show q < x.length + 1 by omega), Option.map_some, Option.getD_some]

theorem atq_bot (N q : Nat) : atq (HO.bot N .p) q = none := by
  simp only [atq, HO.bot, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

/-- A result at a position that is a well-formed success is a position again. -/
theorem atq_ok_le {d : Dom .p} (hd : d ∈ elems x.length .p) {q j : Nat} (h : atq d q = some (some j)) :
    j ≤ x.length := by
  have := atq_mem hd q
  rw [h] at this
  rcases mem_resElems.1 this with h' | h' | ⟨j', hj', h'⟩
  · cases h'
  · cases h'
  · cases h'; exact hj'

end Suffixes

/-! ## Soundness: the iterates only give results of runs -/

section Soundness

variable (x : List Char) (g : HGrammar)

/-- `d` only promises results that runs of `e` deliver; at a function type, related arguments give related
applications. -/
def RelA : (τ : Ty) → HExp → Dom τ → Prop
  | .p, e, d => ∀ q ≤ x.length, ∀ r, atq d q = some r → HObs g e (sfx x q) (r.map (sfx x))
  | .arr a b, e, f => ∀ e' d', HExp.Cl 0 e' → d' ∈ elems x.length a → RelA a e' d' →
      RelA b (.app e e') (Dom.app (N := x.length) f d')

/-- Closing terms related to the values of the variables. -/
def EnvRelA : (Γ : List Ty) → List HExp → Env Γ → Prop
  | [], [], _ => True
  | τ :: Γ, c :: σ, (d, ρ) => RelA x g τ c d ∧ EnvRelA Γ σ ρ
  | _, _, _ => False

variable {x g}

theorem relA_bot : ∀ (τ : Ty) (e : HExp), RelA x g τ e (HO.bot x.length τ)
  | .p, _ => fun q _ r h => by rw [atq_bot] at h; cases h
  | .arr _ b, _ => fun _ _ _ _ _ => by rw [app_bot]; exact relA_bot b _

/-- A head-reducible term is related to whatever its reduct is related to. -/
theorem relA_expand : ∀ (τ : Ty) {e e' : HExp} {d : Dom τ}, (∀ σ b, e ≠ .lam σ b) → step g e = some e' →
    RelA x g τ e' d → RelA x g τ e d
  | .p, _, _, _, _, hs, h => fun q hq r hr => hobs_expand hs (h q hq r hr)
  | .arr _ b, _, _, _, hl, hs, h => fun e'' d'' hc hd hrel =>
    relA_expand b (fun _ _ h' => by cases h') (step_app_head e'' hl hs) (h e'' d'' hc hd hrel)

theorem EnvRelA.length : ∀ {Γ : List Ty} {σ : List HExp} {ρ : Env Γ}, EnvRelA x g Γ σ ρ → σ.length = Γ.length
  | [], [], _, _ => rfl
  | _ :: _, _ :: _, (_, _), h => by simp [EnvRelA.length h.2]
  | [], _ :: _, _, h | _ :: _, [], _, h => absurd h id

theorem EnvRelA.get : ∀ {Γ : List Ty} {σ : List HExp} {ρ : Env Γ}, EnvRelA x g Γ σ ρ → ∀ (i : Nat) {τ : Ty}
    (h : Γ[i]? = some τ), RelA x g τ (σ.getD i (.var i)) (Env.get ρ i h)
  | [], _, _, _, _, _, h => absurd h (by simp)
  | _ :: _, _ :: _, (_, _), hr, 0, _, h => by cases Option.some.inj h; exact hr.1
  | _ :: Γ, _ :: σ, (_, _), hr, i + 1, _, h => by
    have := EnvRelA.get hr.2 i h
    simp only [List.getD_cons_succ]
    -- the default only matters out of range, which `h` excludes
    have hl := EnvRelA.length hr.2
    have hi : i < σ.length := by have := (List.getElem?_eq_some_iff.1 h).1; simp at this; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at this ⊢
    exact this
  | _ :: _, [], _, hr, _, _, _ => absurd hr id

/-- A leaf is related to its position-wise results. -/
theorem relA_leaf {e : HExp} (he : e = .eps ∨ e = .any ∨ (∃ c, e = .chr c) ∨ (∃ lo hi, e = .range lo hi) ∨
    (∃ s, e = .lit s)) : RelA x g .p e (baseVec x (leafRes x e)) := by
  intro q hq r h
  rw [atq_baseVec hq] at h
  unfold leafRes at h
  cases hr : hrun ⟨[]⟩ 1 e (sfx x q) with
  | none => rw [hr] at h; cases h
  | some r₀ =>
    rw [hr] at h
    cases h
    refine ⟨1, ?_⟩
    rw [hrun_leaf he ⟨[]⟩ 0, hr]
    congr 1
    cases r₀ with
    | none => rfl
    | some rest =>
      simp only [Option.map_some]
      exact congrArg some (sfx_of_suffix (suffix_trans (sfx_suffix q) (hrun_suffix hr))).symm

/-- The run of a PEG operator, from the runs of the operands. -/
theorem relA_seq {A B : HExp} {da db : Dom .p} (hda : da ∈ elems x.length .p) (ha : RelA x g .p A da)
    (hb : RelA x g .p B db) : RelA x g .p (.seq A B) (baseVec x (seqRes da db)) := by
  intro q hq r h
  rw [atq_baseVec hq] at h
  unfold seqRes at h
  cases hA : atq da q with
  | none => rw [hA] at h; cases h
  | some ra =>
    cases ra with
    | none => rw [hA] at h; cases h; exact hobs_seq_fail (ha q hq none hA)
    | some j =>
      rw [hA] at h
      exact hobs_seq_ok (ha q hq (some j) hA) (hb j (atq_ok_le hda hA) r h)

theorem relA_alt {A B : HExp} {da db : Dom .p} (ha : RelA x g .p A da) (hb : RelA x g .p B db) :
    RelA x g .p (.alt A B) (baseVec x (altRes da db)) := by
  intro q hq r h
  rw [atq_baseVec hq] at h
  unfold altRes at h
  cases hA : atq da q with
  | none => rw [hA] at h; cases h
  | some ra =>
    cases ra with
    | none => rw [hA] at h; exact hobs_alt_fail (ha q hq none hA) (hb q hq r h)
    | some j => rw [hA] at h; cases h; exact hobs_alt_ok (ha q hq (some j) hA)

theorem relA_notP {A : HExp} {da : Dom .p} (ha : RelA x g .p A da) :
    RelA x g .p (.notP A) (baseVec x (notRes da)) := by
  intro q hq r h
  rw [atq_baseVec hq] at h
  unfold notRes at h
  cases hA : atq da q with
  | none => rw [hA] at h; cases h
  | some ra =>
    cases ra with
    | none => rw [hA] at h; cases h; exact hobs_not_fail (ha q hq none hA)
    | some j => rw [hA] at h; cases h; exact hobs_not_ok (ha q hq (some j) hA)

theorem relA_star {A : HExp} {da : Dom .p} (ha : RelA x g .p A da) :
    RelA x g .p (.star A) (baseVec x (starRes da)) := by
  intro q hq r h
  rw [atq_baseVec hq] at h
  induction q using Nat.strongRecOn generalizing r with
  | _ q ih =>
    rw [starRes] at h
    cases hA : atq da q with
    | none => rw [hA] at h; cases h
    | some ra =>
      cases ra with
      | none => rw [hA] at h; cases h; exact hobs_star_fail (ha q hq none hA)
      | some j =>
        rw [hA] at h
        dsimp only at h
        split at h
        · rename_i hj
          exact hobs_star_ok (ha q hq (some j) hA) (ih j hj (by omega) r h)
        · cases h

variable {R : List Ty}

/-- Every rule is related to its value. -/
def RulesRelA (x : List Char) (g : HGrammar) (T : Env R) : Prop :=
  ∀ (i : Nat) {τ : Ty} (h : R[i]? = some τ), RelA x g τ (.rule i) (Env.get T i h)

/-- **The fundamental lemma of soundness**: a term, closed by related terms, is related to its meaning. -/
theorem fundA {T : Env R} (hT : Env.Mem x.length T) (hR : RulesRelA x g T) :
    ∀ {Γ : List Ty} {τ : Ty} (t : Tm R Γ τ) (σ : List HExp) (ρ : Env Γ), AllClosed σ → Env.Mem x.length ρ →
      EnvRelA x g Γ σ ρ → RelA x g τ (HExp.substC σ 0 t.erase) (den x t T ρ)
  | _, _, .eps, _, _, _, _, _ => relA_leaf (.inl rfl)
  | _, _, .any, _, _, _, _, _ => relA_leaf (.inr (.inl rfl))
  | _, _, .chr c, _, _, _, _, _ => relA_leaf (.inr (.inr (.inl ⟨c, rfl⟩)))
  | _, _, .range lo hi, _, _, _, _, _ => relA_leaf (.inr (.inr (.inr (.inl ⟨lo, hi, rfl⟩))))
  | _, _, .lit s, _, _, _, _, _ => relA_leaf (.inr (.inr (.inr (.inr ⟨s, rfl⟩))))
  | _, _, .seq a b, σ, ρ, hσ, hρ, he =>
    relA_seq (den_mono x a hT hT (Env.le_refl T) hρ hρ (Env.le_refl ρ)).1
      (fundA hT hR a σ ρ hσ hρ he) (fundA hT hR b σ ρ hσ hρ he)
  | _, _, .alt a b, σ, ρ, hσ, hρ, he => relA_alt (fundA hT hR a σ ρ hσ hρ he) (fundA hT hR b σ ρ hσ hρ he)
  | _, _, .star a, σ, ρ, hσ, hρ, he => relA_star (fundA hT hR a σ ρ hσ hρ he)
  | _, _, .notP a, σ, ρ, hσ, hρ, he => relA_notP (fundA hT hR a σ ρ hσ hρ he)
  | _, _, .var i h, σ, ρ, _, _, he => by
    simp only [Tm.erase, HExp.substC, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
    exact he.get i h
  | _, _, .rule i h, _, _, _, _, _ => hR i h
  | _, _, @Tm.lam _ _ a b body, σ, ρ, hσ, hρ, he => by
    intro e' d' hc hd hrel
    simp only [den]
    rw [app_tab _ hd]
    apply relA_expand b (fun _ _ h' => by cases h') (e' := HExp.inst e' 0 (HExp.substC σ (0 + 1) body.erase)) rfl
    rw [inst_substC hc hσ 0]
    exact fundA hT hR body (e' :: σ) (d', ρ)
      (fun c hcm => by
        rcases List.mem_cons.1 hcm with rfl | hcm
        · exact hc
        · exact hσ c hcm) ⟨hd, hρ⟩ ⟨hrel, he⟩
  | _, _, .app f y, σ, ρ, hσ, hρ, he => by
    have hf := fundA hT hR f σ ρ hσ hρ he
    have hy := fundA hT hR y σ ρ hσ hρ he
    have hcl : HExp.Cl 0 (HExp.substC σ 0 y.erase) :=
      cl_substC hσ 0 _ (by rw [Nat.zero_add, EnvRelA.length he]; exact y.cl_erase)
    exact hf _ _ hcl (den_mono x y hT hT (Env.le_refl T) hρ hρ (Env.le_refl ρ)).1 hy

variable (G : TGrammar R)

/-- Every rule is related to every iterate of its value. -/
theorem rulesRelA_iter : ∀ m, RulesRelA x G.erase (iter x G m)
  | 0 => fun i _ h => by
    show RelA x G.erase _ (.rule i) (Env.get (Env.bot x.length R) i h)
    rw [Env.get_bot]; exact relA_bot _ _
  | m + 1 => fun i τ h => by
    show RelA x G.erase τ (.rule i) (Env.get (G.bodies.den x (iter x G m)) i h)
    rw [TBodies.den_get]
    apply relA_expand τ (fun _ _ h' => by cases h') (step_rule G h)
    have := fundA (iter_mem x G m) (rulesRelA_iter m) (G.bodies.get i h) [] () (by simp [AllClosed]) trivial trivial
    rwa [substC_nil] at this

/-- **Soundness**: a result of an iterate at the full input is the result of a run. -/
theorem sound_iter (t : Tm R [] .p) (m : Nat) {r : Option Nat}
    (h : atq (den x t (iter x G m) ()) x.length = some r) : HObs G.erase t.erase x (r.map (sfx x)) := by
  have := fundA (iter_mem x G m) (rulesRelA_iter G m) t [] () (by simp [AllClosed]) trivial trivial
  rw [substC_nil] at this
  have := this x.length (Nat.le_refl _) r h
  rwa [sfx_full] at this

end Soundness

end Shallot.MacroPeg.HO
