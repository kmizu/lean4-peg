import Shallot.Peg.Undecidable.Ford

/-!
# The language of Ford's grammar is nonempty iff the instance has a solution

`fordG C` has the rules `D ← &. &(A !.) B !.` (rule 0, the start), `A` (rule 1, the tops) and `B` (rule 2, the
bottoms). `D` accepts a string exactly when it is nonempty and both sides eat all of it, i.e. when it is the
common string of a nonempty index list on both sides (`fordG_accepts`). So **`L(fordG C)` is nonempty iff `C` has
a solution** (`ford_iff`), for an instance whose strings are all nonempty.
-/

namespace Shallot

/-- The start rule `D ← &. &(A !.) B !.`. -/
def fordD : PExp := .seq (PExp.andP .any) (.seq (PExp.andP (.seq (.nt 1) (.notP .any))) (.seq (.nt 2) (.notP .any)))

/-- **Ford's grammar** for an instance `C`. -/
def fordG (C : PCP) : Grammar where
  rules := [fordD, sideAlts C.top 1 (List.range C.length), sideAlts C.bot 2 (List.range C.length)]
  start := 0

/-- The language of a grammar: the strings its start rule eats completely. -/
def Accepts (g : Grammar) (w : List Char) : Prop := ∃ t, Derives g (.nt g.start) w (.ok t [])

/-! ## Predicates -/

theorem notAny_ok {g : Grammar} {u r : List Char} {t : PTree} (h : Derives g (.notP .any) u (.ok t r)) :
    u = [] ∧ r = u := by
  cases h with
  | notFail _ _ h => cases h with
    | anyFail => exact ⟨rfl, rfl⟩

theorem andP_ok {g : Grammar} {e : PExp} {u r : List Char} {t : PTree} (h : Derives g (PExp.andP e) u (.ok t r)) :
    (∃ t' r', Derives g e u (.ok t' r')) ∧ r = u := by
  unfold PExp.andP at h
  cases h with
  | notFail _ _ h => cases h with
    | notOk _ _ r' t' h => exact ⟨⟨t', r', h⟩, rfl⟩

theorem andP_of {g : Grammar} {e : PExp} {u r : List Char} {t : PTree} (h : Derives g e u (.ok t r)) :
    Derives g (PExp.andP e) u (.ok .notT u) :=
  .notFail _ _ (.notOk _ _ _ _ h)

/-! ## The sides -/

section Sides

variable {C : PCP} (hC : C.NonemptyPairs)

theorem top_ne (hC : C.NonemptyPairs) : ∀ i, i < C.length → C.top i ≠ [] := fun i hi => by
  have := (hC _ (List.getElem_mem hi)).1
  simpa [PCP.top, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using this

theorem bot_ne (hC : C.NonemptyPairs) : ∀ i, i < C.length → C.bot i ≠ [] := fun i hi => by
  have := (hC _ (List.getElem_mem hi)).2
  simpa [PCP.bot, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using this

theorem fordG_rule1 : ruleAt (fordG C).rules 1 = some (sideAlts C.top 1 (List.range C.length)) := rfl
theorem fordG_rule2 : ruleAt (fordG C).rules 2 = some (sideAlts C.bot 2 (List.range C.length)) := rfl

end Sides

/-- The markers of two index lists agree only for the same list. -/
theorem marks_inj {I J : List Nat} (h : marks I = marks J) : I = J := by
  have := blocks_prefix I.reverse J.reverse [] [] (by simpa [marks] using h)
  have hnil : ∀ R : List Nat, (R.map mark).flatten = [] → R = [] := fun R hR => by
    cases R with
    | nil => rfl
    | cons r R => simp [mark] at hR
  rcases this with ⟨R, hR, hr⟩ | ⟨R, hR, ht⟩
  · have := hnil R (by simpa using hr.symm)
    subst this
    simpa using hR.symm
  · have := hnil R (by simpa using ht.symm)
    subst this
    simpa using hR

/-- **What Ford's grammar accepts**: the common strings of nonempty index lists. -/
theorem fordG_accepts {C : PCP} (hC : C.NonemptyPairs) (w : List Char) :
    Accepts (fordG C) w ↔ ∃ I, I ≠ [] ∧ C.Valid I ∧ w = encS C.top I ∧ w = encS C.bot I := by
  constructor
  · rintro ⟨t, h⟩
    cases h with
    | ntOk _ e _ _ _ hr hd =>
      cases hr
      cases hd with
      | seqOk _ _ _ r₁ _ _ _ h₁ h₂ =>
        obtain ⟨⟨_, _, hany⟩, rfl⟩ := andP_ok h₁
        cases h₂ with
        | seqOk _ _ _ r₂ _ _ _ h₃ h₄ =>
          obtain ⟨⟨_, _, hA⟩, rfl⟩ := andP_ok h₃
          cases hA with
          | seqOk _ _ _ rA _ _ _ hA₁ hA₂ =>
            obtain ⟨rfl, -⟩ := notAny_ok hA₂
            cases h₄ with
            | seqOk _ _ _ rB _ _ _ hB₁ hB₂ =>
              obtain ⟨rfl, -⟩ := notAny_ok hB₂
              obtain ⟨I, hI, hIw⟩ := side_sound (fordG_rule1 (C := C)) (top_ne hC) hA₁
              obtain ⟨J, hJ, hJw⟩ := side_sound (fordG_rule2 (C := C)) (bot_ne hC) hB₁
              rw [List.append_nil] at hIw hJw
              have hw := hIw.symm.trans hJw
              have hm := (word_hash (marks_head I) (marks_head J) (by simpa [encS] using hw)).2
              have hIJ := marks_inj hm
              subst hIJ
              have hne : I ≠ [] := by
                rintro rfl
                cases hany with
                | anyOk c rest => simp [encS, cat, marks, word] at hIw
              exact ⟨I, hne, hI, hIw, hJw⟩
  · rintro ⟨I, hne, hI, hwt, hwb⟩
    obtain ⟨tA, hA⟩ := side_complete (fordG_rule1 (C := C)) (top_ne hC) I hI [] (.inl rfl)
    obtain ⟨tB, hB⟩ := side_complete (fordG_rule2 (C := C)) (bot_ne hC) I hI [] (.inl rfl)
    rw [List.append_nil, ← hwt] at hA
    rw [List.append_nil, ← hwb] at hB
    have hnot : Derives (fordG C) (.notP .any) [] (.ok .notT []) := .notFail _ _ .anyFail
    have hm : marks I ≠ [] := by
      cases hr : I.reverse with
      | nil => exact absurd (List.reverse_eq_nil_iff.1 hr) hne
      | cons i J => simp [marks, hr, mark]
    have hw0 : w ≠ [] := by
      rw [hwt]; simp [encS, hm]
    obtain ⟨c, w', rfl⟩ := List.exists_cons_of_ne_nil hw0
    refine ⟨.nodeNT 0 (.seq .notT (.seq .notT (.seq tB .notT))), .ntOk _ fordD _ _ _ rfl ?_⟩
    exact .seqOk _ _ _ _ _ .notT (.seq .notT (.seq tB .notT)) (andP_of (.anyOk c w'))
      (.seqOk _ _ _ _ _ .notT (.seq tB .notT) (andP_of (.seqOk _ _ _ _ _ tA .notT hA hnot))
        (.seqOk _ _ _ _ _ tB .notT hB hnot))

/-- **Ford's reduction**: the language of `fordG C` is nonempty iff `C` has a solution. -/
theorem ford_iff {C : PCP} (hC : C.NonemptyPairs) : (∃ w, Accepts (fordG C) w) ↔ PCPSol C := by
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨I, hne, hI, hwt, hwb⟩ := (fordG_accepts hC w).1 hw
    have := (word_hash (marks_head I) (marks_head I) (by simpa [encS] using hwt.symm.trans hwb)).1
    exact ⟨I, hne, hI, this⟩
  · rintro ⟨I, hne, hI, hcat⟩
    exact ⟨encS C.top I, (fordG_accepts hC _).2 ⟨I, hne, hI, rfl, by simp [encS, hcat]⟩⟩

end Shallot
