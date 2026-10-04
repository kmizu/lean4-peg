import MacroPeg.Properties.SpecializeCorrect

/-!
# Reachable specialization (instructions.md §8, option 3)

Instead of every admissible pair, specialize only the pairs reachable from the entry `(A, ks)` through calls.
`F.reach A ks` is computed by iterating "add the call targets of the current pairs" (`stage`), each stage a filter of
`F.specs`; after `|specs| + 1` rounds it is a fixpoint (pigeonhole on the stage lengths), hence closed under calls.
So it is a `SpecSet`, and `finite_specialization_on` gives the same observation-level correctness as the full
construction (`reachable_specialization`). Its nonterminal count is at most the full count (`reach_length_le`), and
strictly smaller in examples. The construction reads no input.
-/

namespace Shallot.MacroPeg

open Shallot (PExp Grammar)

/-- The call targets of `e` under the constant vector `v`. -/
def FExp.callTargets (v : List Nat) : FExp → List (Nat × List Nat)
  | .call B as => [(B, as.map (FArg.resolve v))]
  | .seq e₁ e₂ => FExp.callTargets v e₁ ++ FExp.callTargets v e₂
  | .alt e₁ e₂ => FExp.callTargets v e₁ ++ FExp.callTargets v e₂
  | .star e => FExp.callTargets v e
  | .notP e => FExp.callTargets v e
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ | .env _ => []

theorem FExp.callsIn_iff (S : List (Nat × List Nat)) (v : List Nat) :
    ∀ e : FExp, e.CallsIn S v ↔ ∀ q ∈ e.callTargets v, q ∈ S
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ | .env _ => by
    simp [FExp.CallsIn, FExp.callTargets]
  | .call B as => by simp [FExp.CallsIn, FExp.callTargets]
  | .seq a b => by
    simp only [FExp.CallsIn, FExp.callTargets, List.mem_append, FExp.callsIn_iff S v a, FExp.callsIn_iff S v b]
    constructor
    · rintro ⟨ha, hb⟩ q (hq | hq)
      · exact ha q hq
      · exact hb q hq
    · intro h; exact ⟨fun q hq => h q (Or.inl hq), fun q hq => h q (Or.inr hq)⟩
  | .alt a b => by
    simp only [FExp.CallsIn, FExp.callTargets, List.mem_append, FExp.callsIn_iff S v a, FExp.callsIn_iff S v b]
    constructor
    · rintro ⟨ha, hb⟩ q (hq | hq)
      · exact ha q hq
      · exact hb q hq
    · intro h; exact ⟨fun q hq => h q (Or.inl hq), fun q hq => h q (Or.inr hq)⟩
  | .star a => FExp.callsIn_iff S v a
  | .notP a => FExp.callsIn_iff S v a

/-- The call targets of a pair's specialized body. -/
def FGrammar.succs (F : FGrammar) (q : Nat × List Nat) : List (Nat × List Nat) :=
  match F.rules[q.1]? with
  | some r => r.body.callTargets q.2
  | none => []

/-- Membership predicate of the `n`-th stage. -/
def FGrammar.stagePred (F : FGrammar) (A : Nat) (ks : List Nat) : Nat → (Nat × List Nat) → Bool
  | 0 => fun q => decide (q = (A, ks))
  | n + 1 => fun q =>
    decide (q ∈ F.specs.filter (F.stagePred A ks n) ∨ ∃ q' ∈ F.specs.filter (F.stagePred A ks n), q ∈ F.succs q')

def FGrammar.stage (F : FGrammar) (A : Nat) (ks : List Nat) (n : Nat) : List (Nat × List Nat) :=
  F.specs.filter (F.stagePred A ks n)

/-- The pairs reachable from `(A, ks)`, in `specs` order. -/
def FGrammar.reach (F : FGrammar) (A : Nat) (ks : List Nat) : List (Nat × List Nat) :=
  F.stage A ks (F.specs.length + 1)

/-! ## Filters of one list -/

theorem filter_length_le_of_imp {α : Type} (P Q : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, P x = true → Q x = true) → (l.filter P).length ≤ (l.filter Q).length
  | [], _ => by simp
  | x :: xs, h => by
    have ih := filter_length_le_of_imp P Q xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
    cases hp : P x <;> cases hq : Q x <;> simp [hp, hq] <;> try omega
    exact absurd (h x List.mem_cons_self hp) (by simp [hq])

theorem filter_eq_of_imp {α : Type} (P Q : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, P x = true → Q x = true) → (l.filter P).length = (l.filter Q).length →
      l.filter P = l.filter Q
  | [], _, _ => rfl
  | x :: xs, h, hl => by
    have h' : ∀ y ∈ xs, P y = true → Q y = true := fun y hy => h y (List.mem_cons_of_mem _ hy)
    have hle := filter_length_le_of_imp P Q xs h'
    cases hp : P x <;> cases hq : Q x <;> simp only [List.filter_cons, hp, hq] at hl ⊢
    · exact filter_eq_of_imp P Q xs h' hl
    · simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons] at hl; omega
    · exact absurd (h x List.mem_cons_self hp) (by simp [hq])
    · simp only [↓reduceIte, List.length_cons, Nat.add_right_cancel_iff] at hl
      rw [filter_eq_of_imp P Q xs h' hl]

/-! ## Stages grow and stabilize -/

theorem FGrammar.stagePred_mono (F : FGrammar) (A : Nat) (ks : List Nat) (n : Nat) :
    ∀ q ∈ F.specs, F.stagePred A ks n q = true → F.stagePred A ks (n + 1) q = true := by
  intro q hq hp
  simp only [FGrammar.stagePred, decide_eq_true_eq]
  exact Or.inl (List.mem_filter.2 ⟨hq, hp⟩)

theorem FGrammar.stage_length_mono (F : FGrammar) (A : Nat) (ks : List Nat) (n : Nat) :
    (F.stage A ks n).length ≤ (F.stage A ks (n + 1)).length :=
  filter_length_le_of_imp _ _ _ (F.stagePred_mono A ks n)

theorem FGrammar.stage_length_le (F : FGrammar) (A : Nat) (ks : List Nat) (n : Nat) :
    (F.stage A ks n).length ≤ F.specs.length :=
  List.length_filter_le _ _

theorem FGrammar.stagePred_succ (F : FGrammar) (A : Nat) (ks : List Nat) (n : Nat) :
    F.stagePred A ks (n + 1) = fun q =>
      decide (q ∈ F.specs.filter (F.stagePred A ks n) ∨ ∃ q' ∈ F.specs.filter (F.stagePred A ks n), q ∈ F.succs q') :=
  rfl

theorem FGrammar.stage_succ_eq (F : FGrammar) (A : Nat) (ks : List Nat) {n : Nat}
    (h : F.stage A ks (n + 1) = F.stage A ks n) : F.stage A ks (n + 2) = F.stage A ks (n + 1) := by
  unfold FGrammar.stage at h ⊢
  have : F.stagePred A ks (n + 2) = F.stagePred A ks (n + 1) := by
    rw [F.stagePred_succ A ks (n + 1), h, F.stagePred_succ A ks n]
  rw [this]

theorem FGrammar.stage_step_eq (F : FGrammar) (A : Nat) (ks : List Nat) {n : Nat}
    (h : F.stage A ks (n + 1) = F.stage A ks n) : ∀ k, F.stage A ks (n + k + 1) = F.stage A ks (n + k)
  | 0 => h
  | k + 1 => F.stage_succ_eq A ks (F.stage_step_eq A ks h k)

theorem FGrammar.stage_stable (F : FGrammar) (A : Nat) (ks : List Nat) {n : Nat}
    (h : F.stage A ks (n + 1) = F.stage A ks n) : ∀ k, F.stage A ks (n + k) = F.stage A ks n := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [← Nat.add_assoc, F.stage_step_eq A ks h k, ih]

/-- Pigeonhole: some stage among the first `|specs| + 1` repeats. -/
theorem FGrammar.stage_fix_exists (F : FGrammar) (A : Nat) (ks : List Nat) :
    ∃ n, n ≤ F.specs.length ∧ F.stage A ks (n + 1) = F.stage A ks n := by
  refine Classical.byContradiction fun hne => ?_
  have hlt : ∀ n, n ≤ F.specs.length → (F.stage A ks n).length < (F.stage A ks (n + 1)).length := by
    intro n hn
    have hle := F.stage_length_mono A ks n
    refine Nat.lt_of_le_of_ne hle fun heq => hne ⟨n, hn, ?_⟩
    exact (filter_eq_of_imp _ _ _ (F.stagePred_mono A ks n) heq).symm
  have hgrow : ∀ n, n ≤ F.specs.length + 1 → n ≤ (F.stage A ks n).length := by
    intro n
    induction n with
    | zero => intro _; exact Nat.zero_le _
    | succ n ih =>
      intro hn
      have := hlt n (by omega)
      have := ih (by omega)
      omega
  have := hgrow (F.specs.length + 1) (Nat.le_refl _)
  have := F.stage_length_le A ks (F.specs.length + 1)
  omega

theorem FGrammar.reach_fix (F : FGrammar) (A : Nat) (ks : List Nat) :
    F.stage A ks (F.specs.length + 2) = F.reach A ks := by
  obtain ⟨n, hn, hfix⟩ := F.stage_fix_exists A ks
  have h1 := F.stage_stable A ks hfix (F.specs.length + 2 - n)
  have h2 := F.stage_stable A ks hfix (F.specs.length + 1 - n)
  unfold FGrammar.reach
  rw [show F.specs.length + 2 = n + (F.specs.length + 2 - n) by omega, h1,
    show F.specs.length + 1 = n + (F.specs.length + 1 - n) by omega, h2]

/-! ## The reachable set is a `SpecSet` -/

theorem FGrammar.reach_subset (F : FGrammar) (A : Nat) (ks : List Nat) : ∀ q ∈ F.reach A ks, q ∈ F.specs :=
  fun _ hq => (List.mem_filter.1 hq).1

theorem FGrammar.entry_mem_stage (F : FGrammar) {A : Nat} {ks : List Nat} (hv : F.ValidVec A ks) :
    ∀ n, (A, ks) ∈ F.stage A ks n
  | 0 => List.mem_filter.2 ⟨(F.mem_specs A ks).2 hv, by simp [FGrammar.stagePred]⟩
  | n + 1 =>
    List.mem_filter.2 ⟨(F.mem_specs A ks).2 hv, F.stagePred_mono A ks n _ ((F.mem_specs A ks).2 hv)
      (List.mem_filter.1 (F.entry_mem_stage hv n)).2⟩

theorem FGrammar.entry_mem_reach (F : FGrammar) {A : Nat} {ks : List Nat} (hv : F.ValidVec A ks) :
    (A, ks) ∈ F.reach A ks :=
  F.entry_mem_stage hv _

theorem FGrammar.reach_specSet (F : FGrammar) (hF : F.WF) (A : Nat) (ks : List Nat) : F.SpecSet (F.reach A ks) := by
  refine ⟨fun q hq => (F.mem_specs q.1 q.2).1 (F.reach_subset A ks q hq), ?_⟩
  intro B w r hm hr
  rw [FExp.callsIn_iff]
  intro q hq
  -- `q` is a call target of an admissible pair, hence admissible, hence in the next stage, which is `reach` again
  have hBw := (F.mem_specs B w).1 (F.reach_subset A ks _ hm)
  obtain ⟨r', hr', hl, hk⟩ := hBw
  rw [hr] at hr'; cases hr'
  have hspecs : q ∈ F.specs :=
    (FExp.callsIn_iff F.specs w r.body).1
      (FExp.callsIn_specs F hl hk r.body (hF.2.2 r (List.mem_of_getElem? hr))) q hq
  rw [← F.reach_fix A ks]
  refine List.mem_filter.2 ⟨hspecs, ?_⟩
  simp only [FGrammar.stagePred, decide_eq_true_eq]
  refine Or.inr ⟨(B, w), hm, ?_⟩
  simp only [FGrammar.succs, hr]
  exact hq

/-! ## Correctness and size -/

/-- **Reachable specialization.** Same statement as `finite_specialization_cbn`, for the grammar built from the
reachable pairs only. -/
theorem reachable_specialization (F : FGrammar) (hF : F.WF) {A : Nat} {ks : List Nat} (hv : F.ValidVec A ks)
    (x : List Char) (r : Option (List Char)) :
    MacroObs F.toMacro (F.entry A ks) x r ↔
      PegObs (F.specializeOn (F.reach A ks) A ks) (.nt (F.specializeOn (F.reach A ks) A ks).start) x r :=
  finite_specialization_on F hF (F.reach_specSet hF A ks) (F.entry_mem_reach hv) x r

/-- The reachable construction never has more rules than the full one. -/
theorem reach_length_le (F : FGrammar) (A : Nat) (ks : List Nat) :
    (F.specializeOn (F.reach A ks) A ks).rules.length ≤ (F.specialize A ks).rules.length := by
  rw [F.specializeOn_size, FGrammar.specialize, F.specializeOn_size]
  have := F.stage_length_le A ks (F.specs.length + 1)
  unfold FGrammar.reach
  omega

theorem reach_selfContained (F : FGrammar) (hF : F.WF) (A : Nat) (ks : List Nat) :
    ∀ p ∈ (F.specializeOn (F.reach A ks) A ks).rules,
      p.NtBounded (F.specializeOn (F.reach A ks) A ks).rules.length :=
  F.specializeOn_selfContained hF (F.reach_specSet hF A ks) A ks

end Shallot.MacroPeg
