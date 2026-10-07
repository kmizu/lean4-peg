import Cfg.Greibach.GNFUnit

/-!
# Greibach normal form: the left-corner decomposition

For a grammar `G`, `LeftCorner G A C v` says that `A` derives `C v` with `C` the leftmost symbol of a chain of
leftmost expansions `A = D₀ → D₁ α₁, …, Dₖ₋₁ → C αₖ` and `v` a word of `αₖ ⋯ α₁`.

`gen_decomp`: in an `EpsFree` grammar every word of `E` is `a u v` for a side `F → a β` with `β ⇒ u` and
`LeftCorner G E F v`; conversely (`gen_of_leftCorner`) such words are words of `E`. This is the whole
semantic content of the Greibach construction in `Cfg/Greibach/GNFMain.lean`.
-/

namespace Shallot.Cfg

/-- `A` derives `C v` through leftmost expansions, `v` the word of the pending suffixes. -/
inductive LeftCorner (G : CFGrammar) (A : Nat) : Nat → List Char → Prop
  | refl : LeftCorner G A A []
  | step {C D : Nat} {α : List Sym} {u v : List Char} (hrule : (.nt C :: α) ∈ altsOf G D)
      (hu : SemRhs (Gen G) α u) (hv : LeftCorner G A D v) : LeftCorner G A C (u ++ v)

/-- One rule application through `altsOf`. -/
theorem gen_of_altsOf {G : CFGrammar} {i : Nat} {rhs : Rhs} {w : List Char} (h : rhs ∈ altsOf G i)
    (hw : SemRhs (Gen G) rhs w) : Gen G i w := by
  obtain ⟨a, ha, hra⟩ := altsAt_of_mem_altsOf h
  exact gen_of_rule ha hra hw

/-- A member of `altsOf` lies in the rule list. -/
theorem mem_rules_of_mem_altsOf {G : CFGrammar} {i : Nat} {rhs : Rhs} (h : rhs ∈ altsOf G i) :
    ∃ a ∈ G.rules, rhs ∈ a := by
  obtain ⟨a, ha, hra⟩ := altsAt_of_mem_altsOf h
  exact ⟨a, altsAt_some_mem ha, hra⟩

/-- A nonterminal with an alternative is in range. -/
theorem lt_of_mem_altsOf {G : CFGrammar} {i : Nat} {rhs : Rhs} (h : rhs ∈ altsOf G i) :
    i < G.rules.length := by
  obtain ⟨a, ha, _⟩ := altsAt_of_mem_altsOf h
  exact altsAt_some_lt ha

/-- The alternatives of a defined index, through `altsOf`. -/
theorem mem_altsOf {G : CFGrammar} {i : Nat} {alts : List Rhs} {rhs : Rhs}
    (halts : altsAt G.rules i = some alts) (h : rhs ∈ alts) : rhs ∈ altsOf G i := by
  simp only [altsOf, halts, Option.getD_some]; exact h

/-- Extending a left-corner chain at the top by a side `E → C α`. -/
theorem leftCorner_extend {G : CFGrammar} {C F : Nat} {v : List Char} (h : LeftCorner G C F v)
    {E : Nat} {α : List Sym} {w₂ : List Char} (hr : (.nt C :: α) ∈ altsOf G E)
    (hw : SemRhs (Gen G) α w₂) : LeftCorner G E F (v ++ w₂) := by
  induction h with
  | refl =>
      have := LeftCorner.step (u := w₂) hr hw (LeftCorner.refl (G := G) (A := E))
      rw [List.append_nil] at this; rw [List.nil_append]; exact this
  | step hrule hu _ ih =>
      rw [List.append_assoc]
      exact LeftCorner.step hrule hu ih

/-- A left-corner chain turns words of the corner into words of the top. -/
theorem gen_of_leftCorner {G : CFGrammar} {E C : Nat} {v : List Char} (h : LeftCorner G E C v) :
    ∀ {x : List Char}, Gen G C x → Gen G E (x ++ v) := by
  induction h with
  | refl => intro x hx; rw [List.append_nil]; exact hx
  | step hrule hu _ ih =>
      intro x hx
      rw [← List.append_assoc]
      exact ih (gen_of_altsOf hrule ⟨x, _, rfl, hx, hu⟩)

/-- **The left-corner decomposition** of the words of an `EpsFree` grammar. -/
theorem gen_decomp {G : CFGrammar} (hε : EpsFree G) {E : Nat} {w : List Char} (h : Gen G E w) :
    ∃ F a β u v, (.t a :: β) ∈ altsOf G F ∧ SemRhs (Gen G) β u ∧ LeftCorner G E F v ∧
      w = a :: (u ++ v) := by
  have key := gen_sound (g := G) (fun E w => Gen G E w ∧ ∃ F a β u v, (.t a :: β) ∈ altsOf G F ∧
      SemRhs (Gen G) β u ∧ LeftCorner G E F v ∧ w = a :: (u ++ v))
    (fun E alts rhs w halts hmem hr => by
      refine ⟨gen_of_rule halts hmem (semRhs_mono rhs w (fun _ _ _ h => h.1) hr), ?_⟩
      match rhs, hr with
      | [], _ => exact absurd rfl (hε alts (altsAt_some_mem halts) [] hmem)
      | .t a :: β, ⟨w', hw', hr'⟩ =>
          refine ⟨E, a, β, w', [], mem_altsOf halts hmem, semRhs_mono β w' (fun _ _ _ h => h.1) hr',
            .refl, ?_⟩
          rw [hw', List.append_nil]
      | .nt C :: α, ⟨w₁, w₂, hw, ⟨_, F, a, β, u, v, hF, hu, hv, hw₁⟩, h₂⟩ =>
          refine ⟨F, a, β, u, v ++ w₂, hF, hu,
            leftCorner_extend hv (mem_altsOf halts hmem) (semRhs_mono α w₂ (fun _ _ _ h => h.1) h₂), ?_⟩
          rw [hw, hw₁, List.cons_append, List.append_assoc]) h
  exact key.2

/-- In an `EpsFree`, `UnitFree` grammar a chain with empty suffix word is trivial. -/
theorem leftCorner_nil {G : CFGrammar} (hε : EpsFree G) (hu : UnitFree G) {A D : Nat}
    {w : List Char} (h : LeftCorner G A D w) (hw : w = []) : D = A := by
  cases h with
  | refl => rfl
  | @step _ _ α u v hrule hα _ =>
      obtain ⟨a, ha, hra⟩ := mem_rules_of_mem_altsOf hrule
      have hne : α ≠ [] := by
        intro he; subst he
        have := hu a ha _ hra
        simp only [isUnitRhs] at this
        exact Bool.noConfusion this
      have := semRhs_ne_nil (fun _ _ h => gen_ne_nil hε h) α u hne hα
      exact absurd (List.append_eq_nil_iff.mp hw).1 this

end Shallot.Cfg
