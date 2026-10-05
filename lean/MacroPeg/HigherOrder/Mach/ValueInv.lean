import MacroPeg.HigherOrder.Mach.Halt

/-!
# Character codes are below `1114112`

The codes of a character are below `1114112` (`toNat_lt`). The reading machine only adds literals written as such
codes (`pstep_lt`), so every literal code of every state it reaches is below `1114112` (`finalSt_ltOK`).
-/

namespace Shallot.MacroPeg.Mach

theorem toNat_lt (c : Char) : c.toNat < 1114112 := by
  have h := c.valid
  simp only [UInt32.isValidChar, Nat.isValidChar] at h
  simp only [Char.toNat]
  omega

/-- The literal codes are character codes. -/
def LtOK (s : PSt) : Prop := ∀ l ∈ s.lt, ∀ c ∈ l, c < 1114112

theorem pstep_lt (s : PSt) : (pstep s).lt = s.lt ∨ ∃ str : List Char, (pstep s).lt = s.lt ++ [str.map Char.toNat] := by
  unfold pstep readExpr readType binDone unDone
  repeat' split
  all_goals first
    | (left; rfl)
    | (right; exact ⟨_, rfl⟩)
    | (left; simp [PSt.fail, PSt.leaf])
    | (simp [PSt.fail, PSt.leaf])

theorem pstep_ltOK {s : PSt} (h : LtOK s) : LtOK (pstep s) := by
  rcases pstep_lt s with he | ⟨str, he⟩
  · rw [LtOK, he]; exact h
  · intro l hl c hc
    rw [he] at hl
    rcases List.mem_append.1 hl with hl | hl
    · exact h l hl c hc
    · rw [List.mem_singleton.1 hl] at hc
      obtain ⟨d, _, rfl⟩ := List.mem_map.1 hc
      exact toNat_lt d

theorem pruns_ltOK {s : PSt} (h : LtOK s) : ∀ n, LtOK (pruns s n)
  | 0 => h
  | n + 1 => by rw [pruns_succ]; exact pruns_ltOK (pstep_ltOK h) n

theorem finalSt_ltOK (tk : List Nat) : LtOK (finalSt tk) :=
  pruns_ltOK (fun l hl => by simp [pinit] at hl) _

end Shallot.MacroPeg.Mach
