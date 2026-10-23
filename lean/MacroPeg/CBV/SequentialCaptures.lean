import MacroPeg.CBVtoCBN.SpanValues

namespace Shallot.MacroPeg.CBV.SequentialCaptures

/-! Seq arguments partition the prefix consumed before entry to the body.
These statements constrain a calling convention, rather than a language class.
The strategy of the argument subderivations is arbitrary. -/

/-- Every successful Seq argument list produces consecutive, disjoint captures. -/
theorem partition {g : MGrammar} {s : Strategy} {input final : List Char}
    {args vals : List MExp} (h : DerivesArgsSeq g s input args vals final) :
    ∃ words : List (List Char), vals = words.map MExp.lit ∧
      words.length = args.length ∧ input = words.flatten ++ final := by
  induction args generalizing input vals with
  | nil =>
    cases h
    exact ⟨[], rfl, rfl, rfl⟩
  | cons a args ih =>
    cases h with
    | cons _ _ input p rest final t vs hd hp ht =>
      obtain ⟨words, hv, hn, hx⟩ := ih ht
      refine ⟨p :: words, by simp [hv], by simp [hn], ?_⟩
      simpa [hx, List.append_assoc] using hp

/-- The total capture length is exactly the input consumed by the arguments. -/
theorem length_accounting {g : MGrammar} {s : Strategy} {input final : List Char}
    {args vals : List MExp} (h : DerivesArgsSeq g s input args vals final) :
    ∃ words : List (List Char), vals = words.map MExp.lit ∧
      words.length = args.length ∧
      input.length = (words.map List.length).sum + final.length := by
  obtain ⟨words, hv, hn, hx⟩ := partition h
  refine ⟨words, hv, hn, ?_⟩
  rw [hx, List.length_append, List.length_flatten]

/-- Keeping the caller's input position forces every new captured value empty. -/
theorem stationary {g : MGrammar} {s : Strategy} {input : List Char}
    {args vals : List MExp} (h : DerivesArgsSeq g s input args vals input) :
    vals = List.replicate args.length (.lit []) := by
  induction args generalizing input vals with
  | nil => cases h; rfl
  | cons a args ih =>
    cases h with
    | cons _ _ input p rest _ t vs hd hp ht =>
      obtain ⟨words, hv, hn, hx⟩ := partition ht
      have hl := congrArg List.length hp
      have hr := congrArg List.length hx
      simp only [List.length_append] at hl hr
      have hp0 : p = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst p
      simp only [List.nil_append] at hp
      have ht' : DerivesArgsSeq g s input args vs input := by
        simpa only [← hp] using ht
      simp [List.replicate_succ, ih ht']

/-- Forwarding captured literals succeeds exactly when their concatenation
occurs again at the current position; the callee starts after that occurrence. -/
theorem forward_iff (g : MGrammar) (s : Strategy) (words : List (List Char))
    (input final : List Char) (vals : List MExp) :
    DerivesArgsSeq g s input (words.map MExp.lit) vals final ↔
      vals = words.map MExp.lit ∧ input = words.flatten ++ final := by
  induction words generalizing input vals with
  | nil =>
    constructor
    · intro h; cases h; exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩; exact .nil _
  | cons w words ih =>
    constructor
    · intro h
      cases h with
      | cons _ _ input p rest final t vs hd hp ht =>
        cases hd with
        | litOk _ _ _ hs =>
          have hw := (CBVtoCBN.stripPrefix_exact w input rest).mp hs
          have hwp : w = p := List.append_cancel_right (hw.symm.trans hp)
          obtain ⟨hv, hx⟩ := ih rest vs |>.mp ht
          exact ⟨by simp [← hwp, hv], by simpa [hx, List.append_assoc] using hw⟩
    · rintro ⟨rfl, rfl⟩
      have ht := (ih (words.flatten ++ final) (words.map MExp.lit)).mpr ⟨rfl, rfl⟩
      apply DerivesArgsSeq.cons (.lit w) (words.map MExp.lit)
        _ w (words.flatten ++ final) final (.leaf w) (words.map MExp.lit)
      · apply MDerives.litOk
        apply (CBVtoCBN.stripPrefix_exact _ _ _).mpr
        simp [List.append_assoc]
      · simp [List.append_assoc]
      · exact ht

/-- Any nonempty capture forces strict progress before entering a Seq body. -/
theorem strict_progress {g : MGrammar} {s : Strategy} {input final : List Char}
    {args vals : List MExp} (h : DerivesArgsSeq g s input args vals final)
    (hne : vals ≠ List.replicate args.length (.lit [])) :
    final.length < input.length := by
  obtain ⟨words, hv, hn, hx⟩ := partition h
  have hl := congrArg List.length hx
  simp only [List.length_append] at hl
  by_cases hh : final.length < input.length
  · exact hh
  have hz : words.flatten = [] := List.eq_nil_of_length_eq_zero (by omega)
  have he : input = final := by simpa [hz] using hx
  exact False.elim (hne (stationary (he ▸ h)))

end Shallot.MacroPeg.CBV.SequentialCaptures
