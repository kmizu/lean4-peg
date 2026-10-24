import MacroPeg.CBV.SequentialArgConsReturn
import MacroPeg.CBV.SequentialSeqReturnMachine

namespace Shallot.MacroPeg.CBV.SequentialArgConsReturnMachine

open Complexity Complexity.BinaryWord SequentialStack SequentialStackCodec
open SequentialStackBinary SequentialStackCodecBound SequentialStackPayload CBVtoCBN SequentialArgConsReturn
open SequentialFrontRead (locals frontSpace)
open SequentialCallReturn (envFields)

def before (r : ArgsResult) (a b : Nat) (K : List SequentialStack.Frame) : Config :=
  ⟨.value (.args r), .argCons (a, b) :: K⟩
def next (r : ArgsResult) (a b : Nat) (K : List SequentialStack.Frame) : Config := ⟨.value (.args (prependResult r a b)), K⟩
def program : LProg 11 := SequentialLocalPipeline.program localProgram

noncomputable abbrev space := SequentialSeqReturnMachine.space

/-- Prepend the captured interval to the actual argument environment, including
its length header and argument order, by executing the local program. -/
theorem transition_runs (g : MGrammar) (x : List Char) (e : MExp) (r : ArgsResult) (a b : Nat)
    (K : List SequentialStack.Frame)
    (h : SequentialStack.Runs g x (initial g x e) (before r a b K)) :
    ∃ T, Complexity.Runs (LenOK (space g x e (before r a b K))) program
      (SequentialFieldFetch.start (width g x e) (encode (compilerNodes g e) (before r a b K)) [] [] 0 [])
      (SequentialFieldFetch.start (width g x e) (encode (compilerNodes g e) (next r a b K)) [] [] 0 []) T := by
  let c := before r a b K
  let d := next r a b K
  let localNext : Config := ⟨.value (.args (prependResult r a b)), []⟩
  let N := numberBound g x e
  let B := space g x e c
  let P := inputFields r K.length a b
  let P' := outputFields r K.length a b
  let S := SequentialFront.suffixCode (compilerNodes g e) K
  have hP : SequentialFront.prefixCode (compilerNodes g e) (SequentialFront.tail c) (SequentialFront.front c) = P := by
    simpa [c, before, SequentialFront.front, SequentialFront.tail] using input_prefix (compilerNodes g e) r a b K
  have hP' : SequentialFront.prefixCode (compilerNodes g e) (SequentialFront.tail c) localNext = P' := by
    simpa [localNext, c, before, SequentialFront.tail] using output_prefix (compilerNodes g e) r a b K
  have hS : SequentialFront.suffixCode (compilerNodes g e) (SequentialFront.tail c) = S := rfl
  have hs : step g x c = some d := original_step g x r a b K
  have hd : d = SequentialFront.attach (SequentialFront.tail c) localNext := rfl
  have hcode : encode (compilerNodes g e) c = P ++ S := by
    simpa only [hP, hS] using SequentialFront.encode_front (compilerNodes g e) c
  have hcode' : encode (compilerNodes g e) d = P' ++ S := by
    rw [hd, SequentialFront.encode_attach, hP', hS]
  have hb : ∀ v ∈ P, v ≤ N := by
    intro v hv
    apply reachable_numbers g x e c h v
    rw [hcode]
    exact List.mem_append_left _ hv
  have henv : (envFields r).length ≤ 1 + 2 * arityBudget g := by
    have hh := (reachable_payload_bounds g x e c h).1.1.2
    cases r <;> (try (rename_i rr; cases rr)) <;> (try (rename_i pair; cases pair)) <;>
      simp [envFields, env_length, c, before, taskCaptures] at hh ⊢ <;> omega
  have hfront : frontSpace g x e c ≤ B := by dsimp [B, space, SequentialSeqReturnMachine.space]; omega
  have hscratch : SequentialSeqReturn.scratchSpace (arityBudget g) N ≤ B := by
    dsimp [B, N, space, SequentialSeqReturnMachine.space]; omega
  have hnum : N + 3 ≤ B := by
    have hh : N + 3 ≤ SequentialSeqReturn.scratchSpace (arityBudget g) N := by
      unfold SequentialSeqReturn.scratchSpace SequentialSeqReturn.cellBound
      rw [Nat.add_mul]
      omega
    omega
  have hlen : P'.length ≤ P.length := by
    cases r <;> (try (rename_i rr; cases rr)) <;> (try (rename_i pair; cases pair)) <;>
      simp [P, P', inputFields, outputFields, writeArgsRes, prependResult, env_length] <;> omega
  have hfinal : (encodeBits (compilerNodes g e) (width g x e) d).length + 2 ≤ B := by
    have hR : (encodeBits (compilerNodes g e) (width g x e) c).length + 2 ≤ frontSpace g x e c := by
      unfold frontSpace; omega
    have hm := Nat.mul_le_mul_right (width g x e) hlen
    simp only [encodeBits, hcode, hcode', SequentialStackBinary.pack_length, List.length_append, Nat.add_mul] at hR ⊢
    omega
  apply SequentialLocalPipeline.transition_runs g x e c d localNext h hs hd localProgram B hfront hnum hfinal
  intro held hR
  have hr := local_runs r K.length a b (width := width g x e)
    (SequentialStackBinary.pack (width g x e) (SequentialFront.suffixCode (compilerNodes g e) (SequentialFront.tail c)))
    henv hb hscratch (by simpa only [hP] using hR)
  exact ⟨_, by simpa only [hP, hP'] using hr⟩

theorem transition_tape (g : MGrammar) (x : List Char) (e : MExp) (r : ArgsResult) (a b : Nat)
    (K : List SequentialStack.Frame)
    (h : SequentialStack.Runs g x (initial g x e) (before r a b K)) (τ : Tapes 11)
    (hτ : Rep (SequentialFieldFetch.start (width g x e) (encode (compilerNodes g e) (before r a b K)) [] [] 0 []) τ) :
    ∃ t τ', Exec (TFits (space g x e (before r a b K))) program.compile τ t (.cont τ') ∧
      Rep (SequentialFieldFetch.start (width g x e) (encode (compilerNodes g e) (next r a b K)) [] [] 0 []) τ' := by
  obtain ⟨_, hr⟩ := transition_runs g x e r a b K h
  obtain ⟨t, τ', _, he, hr'⟩ := runs_tape hr τ hτ
  exact ⟨t, τ', he, hr'⟩

end Shallot.MacroPeg.CBV.SequentialArgConsReturnMachine
