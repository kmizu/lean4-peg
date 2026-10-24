import MacroPeg.CBV.SequentialArgConsReturnMachine
import MacroPeg.CBV.SequentialCallReturnMachine

/-! Compose interval insertion with call return: the captured head argument
is inserted before the other arguments, then passed to the grammar query. -/

namespace Shallot.MacroPeg.CBV.SequentialArgumentBind

open Complexity Complexity.BinaryWord SequentialStack SequentialStackCodec SequentialStackBinary CBVtoCBN

def program : LProg 11 := .seq SequentialArgConsReturnMachine.program SequentialCallReturnMachine.program

noncomputable def space (g : MGrammar) (x : List Char) (e : MExp) (r : ArgsResult)
    (a b m i : Nat) (K : List SequentialStack.Frame) : Nat :=
  SequentialArgConsReturnMachine.space g x e (SequentialArgConsReturnMachine.before r a b (.call m i :: K)) +
    SequentialCallReturnMachine.space g x e
      (SequentialCallReturnMachine.before (SequentialArgConsReturn.prependResult r a b) m i K)

theorem space_bound (g : MGrammar) (x : List Char) (e : MExp) (r : ArgsResult) (a b m i : Nat)
    (K : List SequentialStack.Frame)
    (h : SequentialStack.Runs g x (initial g x e) (SequentialArgConsReturnMachine.before r a b (.call m i :: K))) :
    let A := SequentialStackPayload.arityBudget g
    let C := SequentialSeqReturn.cellBound A + SequentialSeqReturn.stepBound A
    let D := SequentialSeqReturn.cellBound A + SequentialSeqReturn.stepBound A * (SequentialSeqReturn.stepBound A + 1) + 2
    let F := (((13 + 6 * A + 4) * (numberCoefficient g e + 1) + 8) +
      (C * numberCoefficient g e + D)) * (x.length + 1) +
      (cellCoefficient g e * (x.length + 1)) *
        ((x.length + 1).log2 + (numberCoefficient g e).log2 + 2)
    space g x e r a b m i K ≤ 2 * F := by
  have hs := SequentialArgConsReturn.original_step g x r a b (.call m i :: K)
  have hmid := h.trans (SequentialStack.Runs.single hs)
  have h1 := SequentialSeqReturnMachine.space_bound g x e
    (SequentialArgConsReturnMachine.before r a b (.call m i :: K)) h
  have h2 := SequentialSeqReturnMachine.space_bound g x e
    (SequentialCallReturnMachine.before (SequentialArgConsReturn.prependResult r a b) m i K) hmid
  simpa only [space, Nat.two_mul] using Nat.add_le_add h1 h2

/-- Execute both actual transitions. On successful arguments this produces
`query m i ((a,b)::W) q` with the original captured-argument order. -/
theorem bind_runs (g : MGrammar) (x : List Char) (e : MExp) (r : ArgsResult) (a b m i : Nat)
    (K : List SequentialStack.Frame)
    (h : SequentialStack.Runs g x (initial g x e) (SequentialArgConsReturnMachine.before r a b (.call m i :: K))) :
    ∃ T, Complexity.Runs (LenOK (space g x e r a b m i K)) program
      (SequentialFieldFetch.start (width g x e)
        (encode (compilerNodes g e) (SequentialArgConsReturnMachine.before r a b (.call m i :: K))) [] [] 0 [])
      (SequentialFieldFetch.start (width g x e)
        (encode (compilerNodes g e) (SequentialCallReturnMachine.next (SequentialArgConsReturn.prependResult r a b) m i K)) [] [] 0 []) T := by
  let c := SequentialArgConsReturnMachine.before r a b (.call m i :: K)
  let mid := SequentialCallReturnMachine.before (SequentialArgConsReturn.prependResult r a b) m i K
  have hs : step g x c = some mid := SequentialArgConsReturn.original_step g x r a b (.call m i :: K)
  have hmid := h.trans (SequentialStack.Runs.single hs)
  obtain ⟨T1, hr1⟩ := SequentialArgConsReturnMachine.transition_runs g x e r a b (.call m i :: K) h
  obtain ⟨T2, hr2⟩ := SequentialCallReturnMachine.transition_runs g x e (SequentialArgConsReturn.prependResult r a b) m i K hmid
  have hb1 : SequentialArgConsReturnMachine.space g x e c ≤ space g x e r a b m i K := by
    unfold space; change _ ≤ SequentialArgConsReturnMachine.space g x e c + _; omega
  have hb2 : SequentialCallReturnMachine.space g x e mid ≤ space g x e r a b m i K := by
    unfold space; change _ ≤ _ + SequentialCallReturnMachine.space g x e mid; omega
  have hr1' := hr1.weaken (fun _ hh j => Nat.le_trans (hh j) hb1)
  have hr2' := hr2.weaken (fun _ hh j => Nat.le_trans (hh j) hb2)
  exact ⟨T1 + T2, hr1'.seq hr2'⟩

theorem bind_tape (g : MGrammar) (x : List Char) (e : MExp) (r : ArgsResult) (a b m i : Nat)
    (K : List SequentialStack.Frame)
    (h : SequentialStack.Runs g x (initial g x e) (SequentialArgConsReturnMachine.before r a b (.call m i :: K)))
    (τ : Tapes 11)
    (hτ : Rep (SequentialFieldFetch.start (width g x e)
      (encode (compilerNodes g e) (SequentialArgConsReturnMachine.before r a b (.call m i :: K))) [] [] 0 []) τ) :
    ∃ t τ', Exec (TFits (space g x e r a b m i K)) program.compile τ t (.cont τ') ∧
      Rep (SequentialFieldFetch.start (width g x e)
        (encode (compilerNodes g e) (SequentialCallReturnMachine.next (SequentialArgConsReturn.prependResult r a b) m i K)) [] [] 0 []) τ' := by
  obtain ⟨_, hr⟩ := bind_runs g x e r a b m i K h
  obtain ⟨t, τ', _, he, hr'⟩ := runs_tape hr τ hτ
  exact ⟨t, τ', he, hr'⟩

end Shallot.MacroPeg.CBV.SequentialArgumentBind
