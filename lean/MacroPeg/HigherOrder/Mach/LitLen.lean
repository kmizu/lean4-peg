import MacroPeg.HigherOrder.Mach.ReadSizes

/-!
# Literals are no longer than the input

A literal is read from the remaining tokens (`pstep_lt_len`), which never grow, so every literal of the final
state has at most as many codes as there were tokens (`finalSt_lit_len`).
-/

namespace Shallot.MacroPeg.Mach

theorem readExpr_lt_len (s : PSt) (K : List Nat) :
    (readExpr s K).lt = s.lt ∨
      ∃ str : List Char, str.length ≤ s.tk.length ∧ (readExpr s K).lt = s.lt ++ [str.map Char.toNat] := by
  unfold readExpr
  split
  next r h => exact .inl rfl
  next r h => exact .inl rfl
  next r h => split <;> exact .inl rfl
  next r h => repeat' split
              all_goals exact .inl rfl
  next r h =>
    split
    next str r₁ h₁ =>
      right
      refine ⟨str, ?_, rfl⟩
      have := parseStr_len h₁
      rw [h]; simp; omega
    next => exact .inl rfl
  all_goals first
    | exact .inl rfl
    | (repeat' split
       all_goals exact .inl rfl)

theorem pstep_lt_len (s : PSt) :
    (pstep s).lt = s.lt ∨ ∃ str : List Char, str.length ≤ s.tk.length ∧ (pstep s).lt = s.lt ++ [str.map Char.toNat] := by
  unfold pstep
  split
  next => exact .inl rfl
  next K hc => exact readExpr_lt_len s K
  all_goals (try unfold readType)
  all_goals (try unfold binDone)
  all_goals (try unfold unDone)
  all_goals (repeat' split)
  all_goals exact .inl rfl

/-- Every literal is at most `L` codes long. -/
def LitLen (L : Nat) (s : PSt) : Prop := ∀ l ∈ s.lt, l.length ≤ L

theorem pruns_litLen {L : Nat} : ∀ (n : Nat) (s : PSt), s.tk.length ≤ L → LitLen L s → LitLen L (pruns s n)
  | 0, _, _, h => h
  | n + 1, s, htk, h => by
    rw [pruns_succ]
    refine pruns_litLen n (pstep s) (Nat.le_trans (rs_pstep_tk s) htk) ?_
    rcases pstep_lt_len s with he | ⟨str, hlen, he⟩
    · rw [LitLen, he]; exact h
    · intro l hl
      rw [he] at hl
      rcases List.mem_append.1 hl with hl | hl
      · exact h l hl
      · rw [List.mem_singleton.1 hl]; simp; omega

theorem finalSt_lit_len (tk : List Nat) : ∀ l ∈ (finalSt tk).lt, l.length ≤ tk.length :=
  pruns_litLen _ (pinit tk) (by simp [pinit]) (fun l hl => by simp [pinit] at hl)

end Shallot.MacroPeg.Mach
