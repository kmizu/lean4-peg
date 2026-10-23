import MacroPeg.CBVtoCBN.CompilerBasics

namespace Shallot.MacroPeg.CBVtoCBN

/-- A generated fragment occupies exactly these consecutive rule addresses. -/
def RulesAt (g : MGrammar) (base : Nat) (rules : List MRule) : Prop :=
  ∀ j, j < rules.length → ruleAtM g.rules (base + j) = ruleAtM rules j

theorem compilerFragmentAt_block (before : CompileFragments) (offset : Nat) (rules : List MRule)
    (after : CompileFragments) (j : Nat) (hj : j < rules.length)
    (hsep : ∀ f ∈ before, f.1 + f.2.length ≤ offset ∨ offset + rules.length ≤ f.1) :
    compilerFragmentAt (before ++ (offset, rules) :: after) (offset + j) = (rules[j]?).getD compilerFailRule := by
  induction before with
  | nil => simp [compilerFragmentAt, hj]
  | cons f before ih =>
    have hs := hsep f (by simp)
    have hm : ¬(f.1 ≤ offset + j ∧ offset + j - f.1 < f.2.length) := by omega
    simp only [List.cons_append, compilerFragmentAt, if_neg hm]
    exact ih (fun a ha => hsep a (List.mem_cons_of_mem _ ha))

/-- A fragment's placement certificate derives all its actual lookup equations from the compiled grammar. -/
theorem CompilerConfig.block_at (c : CompilerConfig) (node : CompileNode) (hn : node ∈ c.nodes)
    (before : CompileFragments) (offset : Nat) (rules : List MRule) (after : CompileFragments)
    (hplan : compilerFragments c.source c.strategy c.nodes c.digits (c.address node) node = before ++ (offset, rules) :: after)
    (hbound : offset + rules.length ≤ compilerSlotSize c.digits)
    (hsep : ∀ f ∈ before, f.1 + f.2.length ≤ offset ∨ offset + rules.length ≤ f.1) :
    RulesAt c.target (c.address node + offset) rules := by
  intro j hj
  have h := c.at node hn (offset + j) (by omega)
  rw [hplan, compilerFragmentAt_block before offset rules after j hj hsep] at h
  simpa only [Nat.add_assoc, ruleAtM_eq_getElem?, List.getElem?_eq_getElem hj, Option.getD_some] using h

private theorem prefix_of_queries (segment whole : List MRule)
    (hq : ∀ j, j < segment.length → whole[j]? = segment[j]?) : ∃ tail, whole = segment ++ tail := by
  induction segment generalizing whole with
  | nil => exact ⟨whole, rfl⟩
  | cons rule rules ih =>
    have h0 := hq 0 (by simp)
    cases whole with
    | nil => simp at h0
    | cons a whole =>
      have he : a = rule := Option.some.inj h0
      subst a
      have ht : ∀ j, j < rules.length → whole[j]? = rules[j]? := by
        intro j hj
        simpa only [List.getElem?_cons_succ] using hq (j + 1) (by simp only [List.length_cons]; omega)
      obtain ⟨tail, he⟩ := ih whole ht
      exact ⟨tail, congrArg (List.cons rule) he⟩

/-- Exact lookup equations recover the literal sublist used by the existing fragment semantics. -/
theorem RulesAt.split {g : MGrammar} {base : Nat} {rules : List MRule}
    (h : RulesAt g base rules) (hne : rules ≠ []) :
    ∃ pre tail, pre.length = base ∧ g = ⟨pre ++ (rules ++ tail)⟩ := by
  cases rules with
  | nil => exact False.elim (hne rfl)
  | cons rule rules =>
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, ruleAtM, ruleAtM_eq_getElem?] at h0
    have hb : base < g.rules.length := (List.getElem?_eq_some_iff.mp h0).choose
    have hd : ∀ j, j < (rule :: rules).length → (g.rules.drop base)[j]? = (rule :: rules)[j]? := by
      intro j hj
      rw [List.getElem?_drop, ← ruleAtM_eq_getElem?, ← ruleAtM_eq_getElem?]
      exact h j hj
    obtain ⟨tail, htail⟩ := prefix_of_queries (rule :: rules) (g.rules.drop base) hd
    refine ⟨g.rules.take base, tail, ?_, ?_⟩
    · simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hb)]
    · have heq : g.rules = g.rules.take base ++ ((rule :: rules) ++ tail) := by
        rw [← htail]
        exact (List.take_append_drop _ _).symm
      exact congrArg MGrammar.mk heq

/-- Source-sequence success semantics transported to any actual generated block. -/
theorem RulesAt.sequenceSuccess_test {g : MGrammar} {entry left right : Nat} (rest : List MExp)
    (h : RulesAt g entry (sequenceSuccessBlock entry left right rest.length))
    (x : List Char) (p q : Nat) (a : Res) (b : Nat → Res) (ha : OkR x.length a)
    (hl : ∀ j, j ≤ x.length → RootTest g
      (.call left (skipN p :: skipN (x.length - p) :: skipN j :: skipN (x.length - j) :: rest)) x (a = some (some j)))
    (hr : ∀ j, j ≤ x.length → RootTest g
      (.call right (skipN j :: skipN (x.length - j) :: skipN q :: skipN (x.length - q) :: rest)) x (b j = some (some q))) :
    RootTest g (.call entry (.eps :: skipN p :: skipN (x.length - p) :: skipN q :: skipN (x.length - q) :: rest)) x
      (seqResult a b = some (some q)) := by
  obtain ⟨pre, tail, hpre, hg⟩ := h.split (by simp [sequenceSuccessBlock, pairSearchBlock])
  have h0 := sequenceSuccessBlock_test pre tail left right rest x p q a b ha
    (by simpa only [hpre, ← hg] using hl) (by simpa only [hpre, ← hg] using hr)
  simpa only [hpre, ← hg] using h0

/-- Source-sequence explicit failure semantics transported to the real compiler output. -/
theorem RulesAt.sequenceFailure_test {g : MGrammar} {entry leftOk leftFail rightFail : Nat} (rest : List MExp)
    (h : RulesAt g entry (sequenceFailureBlock entry leftOk leftFail rightFail rest.length))
    (x : List Char) (p : Nat) (a : Res) (b : Nat → Res) (ha : OkR x.length a)
    (hl : ∀ j, j ≤ x.length → RootTest g
      (.call leftOk (skipN p :: skipN (x.length - p) :: skipN j :: skipN (x.length - j) :: rest)) x (a = some (some j)))
    (hf : RootTest g (.call leftFail (skipN p :: skipN (x.length - p) :: rest)) x (a = some none))
    (hr : ∀ j, j ≤ x.length → RootTest g
      (.call rightFail (skipN j :: skipN (x.length - j) :: rest)) x (b j = some none)) :
    RootTest g (.call entry (skipN p :: skipN (x.length - p) :: rest)) x (seqResult a b = some none) := by
  obtain ⟨pre, tail, hpre, hg⟩ := h.split (by simp [sequenceFailureBlock])
  have h0 := sequenceFailureBlock_test pre tail leftOk leftFail rightFail rest x p a b ha
    (by simpa only [hpre, ← hg] using hl) (by simpa only [hpre, ← hg] using hf) (by simpa only [hpre, ← hg] using hr)
  simpa only [hpre, ← hg] using h0

end Shallot.MacroPeg.CBVtoCBN
