import MacroPeg.CBV.RecursiveArgumentCorrespondence

/-! Unshifted replay accepts nonperiodic captures and preserves empty-entry
recursive divergence. -/
namespace Shallot.MacroPeg.CBV.EmptyReplayExamples
open RecursiveArgumentCompiler
open RecursiveArgumentCorrespondence (observations_iff)
abbrev Arg := RecursiveArgumentCompiler.Expr

def users : List User := [⟨[],.seq (.lit ['#']) (.param 0)⟩]
def entry : Arg := .user 0 (.lit "abac".toList)
def input : List Char := "abac#abac".toList

theorem users_valid : UsersValid [] users := by simp [UsersValid,users,Valid]
theorem source_execution :
    evV (parGrammar [] users) input .callByValuePar (tblV (parGrammar [] users) input .callByValuePar 4) []
      (parRender [] users entry) input.length=some (some 0) := by
  decide +kernel

theorem translated_observation :
    SObs (seqGrammar [] users) .callByValueSeq (plain [] users [] entry) input (some []) := by
  apply (observations_iff [] (by simp [RegularCaptureProduct.Valid]) users users_valid entry
    (by simp [Valid,users,entry]) input (some [])).mp
  obtain ⟨o,hd,ho⟩ := evV_derives (par_firstOrder [] users) (by decide)
    (parRender_firstOrder [] users entry) 4 (Nat.le_refl input.length) source_execution
  rw [sfx_self] at hd
  obtain ⟨t,rest,rfl,hlen⟩ := obsR_ok ho
  have hr : rest=[] := List.length_eq_zero_iff.mp hlen
  subst rest
  exact ⟨_,hd,rfl⟩

def cycleUsers : List User := [⟨[],.user 0 (.lit [])⟩]
abbrev cycleGrammar := parGrammar [] cycleUsers
def cycleEntry : Arg := .user 0 (.lit [])

theorem cycle_valid : UsersValid [] cycleUsers := by simp [UsersValid,cycleUsers,Valid]

theorem cycle_row (k : Nat) : valAt (tblV cycleGrammar [] .callByValuePar k 0 [[]]) 0=none := by
  have hrule : ruleAtM cycleGrammar.rules 0=some ⟨1,.seq (.seq (.lit []) (.param 0)) (.call 0 [.lit []])⟩ := rfl
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [valAt_tblV_succ hrule [[]] (by decide)]
    have hprefix : evV cycleGrammar [] .callByValuePar (tblV cycleGrammar [] .callByValuePar k)
      [[]] (.seq (.lit []) (.param 0)) 0=some (some 0) := rfl
    have hlit : evV cycleGrammar [] .callByValuePar (tblV cycleGrammar [] .callByValuePar k)
      [[]] (.lit []) 0=some (some 0) := rfl
    rw [evV_seq_ok hprefix,evV_call_par hrule rfl (by decide)]
    simpa only [evParArgs,hlit,pre,Nat.sub_self,List.take_zero] using ih

theorem source_cycle (k : Nat) :
    evV cycleGrammar [] .callByValuePar (tblV cycleGrammar [] .callByValuePar k) []
      (parRender [] cycleUsers cycleEntry) 0=none := by
  have hrule : ruleAtM cycleGrammar.rules 0=some ⟨1,.seq (.seq (.lit []) (.param 0)) (.call 0 [.lit []])⟩ := rfl
  change evV cycleGrammar [] .callByValuePar (tblV cycleGrammar [] .callByValuePar k) [] (.call 0 [.lit []]) 0=none
  rw [evV_call_par hrule rfl (by decide)]
  have hlit : evV cycleGrammar [] .callByValuePar (tblV cycleGrammar [] .callByValuePar k) [] (.lit []) 0=some (some 0) := rfl
  simpa only [evParArgs,hlit,pre,Nat.sub_self,List.take_zero] using cycle_row k

theorem target_cycle (rest : Option (List Char)) :
    ¬SObs (seqGrammar [] cycleUsers) .callByValueSeq (plain [] cycleUsers [] cycleEntry) [] rest := by
  rw [←observations_iff [] (by simp [RegularCaptureProduct.Valid]) cycleUsers cycle_valid cycleEntry
    (by simp [Valid,cycleUsers,cycleEntry]) [] rest]
  intro h
  have he := (decideObsV_iff (par_firstOrder [] cycleUsers) (by decide)
    (parRender_firstOrder [] cycleUsers cycleEntry) [] rest).mpr h
  unfold decideObsV at he
  simp only [List.length_nil] at he
  rw [source_cycle] at he
  cases he

end Shallot.MacroPeg.CBV.EmptyReplayExamples
