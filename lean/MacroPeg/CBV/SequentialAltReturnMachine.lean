import MacroPeg.CBV.SequentialAltReturn
import MacroPeg.CBV.SequentialLocalPipeline

namespace Shallot.MacroPeg.CBV.SequentialAltReturnMachine

open Complexity Complexity.BinaryWord SequentialStack SequentialStackCodec
open SequentialStackBinary SequentialStackCodecBound SequentialStackPayload CBVtoCBN SequentialAltReturn
open SequentialFrontRead (locals frontSpace)

def before (r : Res) (m p : Nat) (E : CaptureEnv) (b : MExp) (K : List SequentialStack.Frame) : Config :=
  ⟨.value (.expr r), .alt m E b p :: K⟩
def next (r : Res) (m p : Nat) (E : CaptureEnv) (b : MExp) (K : List SequentialStack.Frame) : Config :=
  ⟨nextTask r m E b p, K⟩
def program : LProg 11 := SequentialLocalPipeline.program localProgram

noncomputable def space (g : MGrammar) (x : List Char) (e : MExp) (c : Config) : Nat :=
  frontSpace g x e c + scratchSpace (arityBudget g) (numberBound g x e)

theorem space_bound (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : SequentialStack.Runs g x (initial g x e) c) :
    let A := arityBudget g
    let C := cellBound A + stepBound A
    let D := cellBound A + stepBound A * (stepBound A + 1) + 2
    space g x e c ≤
      (((13 + 6 * A + 4) * (numberCoefficient g e + 1) + 8) +
        (C * numberCoefficient g e + D)) * (x.length + 1) +
      (cellCoefficient g e * (x.length + 1)) *
        ((x.length + 1).log2 + (numberCoefficient g e).log2 + 2) := by
  dsimp only
  let C := cellBound (arityBudget g) + stepBound (arityBudget g)
  let D := cellBound (arityBudget g) + stepBound (arityBudget g) * (stepBound (arityBudget g) + 1) + 2
  have hf := SequentialFrontRead.frontSpace_bound g x e c h
  have hn := numberBound_linear g x e
  have hm := Nat.mul_le_mul_left C hn
  have hc : D ≤ D * (x.length + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hs : scratchSpace (arityBudget g) (numberBound g x e) ≤
      (C * numberCoefficient g e + D) * (x.length + 1) := by
    rw [scratchSpace_linear]
    change C * numberBound g x e + D ≤ (C * numberCoefficient g e + D) * (x.length + 1)
    have heq : (C * numberCoefficient g e + D) * (x.length + 1) =
        C * (numberCoefficient g e * (x.length + 1)) + D * (x.length + 1) := by
      rw [Nat.add_mul, Nat.mul_assoc]
    rw [heq]
    omega
  have hh := Nat.add_le_add hf hs
  unfold space
  rw [Nat.add_mul]
  change frontSpace g x e c + scratchSpace (arityBudget g) (numberBound g x e) ≤
    ((13 + 6 * arityBudget g + 4) * (numberCoefficient g e + 1) + 8) * (x.length + 1) +
      (C * numberCoefficient g e + D) * (x.length + 1) +
      (cellCoefficient g e * (x.length + 1)) * ((x.length + 1).log2 + (numberCoefficient g e).log2 + 2)
  omega

/-- A complete ordered-choice return, restoring the saved position and captured
environment only on failure of the left branch. -/
theorem transition_runs (g : MGrammar) (x : List Char) (e : MExp) (r : Res) (m p : Nat)
    (E : CaptureEnv) (b : MExp) (K : List SequentialStack.Frame)
    (h : SequentialStack.Runs g x (initial g x e) (before r m p E b K)) :
    ∃ T, Complexity.Runs (LenOK (space g x e (before r m p E b K))) program
      (SequentialFieldFetch.start (width g x e) (encode (compilerNodes g e) (before r m p E b K)) [] [] 0 [])
      (SequentialFieldFetch.start (width g x e) (encode (compilerNodes g e) (next r m p E b K)) [] [] 0 []) T := by
  let c := before r m p E b K
  let d := next r m p E b K
  let localNext : Config := ⟨nextTask r m E b p, []⟩
  let N := numberBound g x e
  let B := space g x e c
  let P := inputFields r K.length m p (exprId (compilerNodes g e) b) (writeEnv E)
  let P' := outputFields r K.length m p (exprId (compilerNodes g e) b) (writeEnv E)
  let S := SequentialFront.suffixCode (compilerNodes g e) K
  have hP : SequentialFront.prefixCode (compilerNodes g e) (SequentialFront.tail c) (SequentialFront.front c) = P := by
    simpa [c, before, SequentialFront.front, SequentialFront.tail] using input_prefix (compilerNodes g e) r m p E b K
  have hP' : SequentialFront.prefixCode (compilerNodes g e) (SequentialFront.tail c) localNext = P' := by
    simpa [localNext, c, before, SequentialFront.tail] using output_prefix (compilerNodes g e) r m p E b K
  have hS : SequentialFront.suffixCode (compilerNodes g e) (SequentialFront.tail c) = S := rfl
  have hs : step g x c = some d := original_step g x r m p E b K
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
  have henv : E.length ≤ arityBudget g := by
    have hh := (reachable_payload_bounds g x e c h).2 (.alt m E b p) (by simp [c, before])
    exact hh.1.2
  have hE : (writeEnv E).length ≤ 1 + 2 * arityBudget g := by
    rw [env_length]; omega
  have hfront : frontSpace g x e c ≤ B := by dsimp [B, space]; omega
  have hscratch : scratchSpace (arityBudget g) N ≤ B := by dsimp [B, N, space]; omega
  have hnum : N + 3 ≤ B := by
    have hh : N + 3 ≤ scratchSpace (arityBudget g) N := by
      unfold scratchSpace SequentialNumericBlock.scratchSpace cellBound
      rw [Nat.add_mul]
      omega
    omega
  have hlen : P'.length ≤ P.length := by
    cases r <;> (try (rename_i rr; cases rr)) <;> simp [P, P', inputFields, outputFields] <;> omega
  have hfinal : (encodeBits (compilerNodes g e) (width g x e) d).length + 2 ≤ B := by
    have hR : (encodeBits (compilerNodes g e) (width g x e) c).length + 2 ≤ frontSpace g x e c := by
      unfold frontSpace; omega
    have hm := Nat.mul_le_mul_right (width g x e) hlen
    simp only [encodeBits, hcode, hcode', SequentialStackBinary.pack_length, List.length_append, Nat.add_mul] at hR ⊢
    omega
  apply SequentialLocalPipeline.transition_runs g x e c d localNext h hs hd localProgram B hfront hnum hfinal
  intro held hR
  have hr := local_runs r K.length m p (exprId (compilerNodes g e) b) (writeEnv E)
    (width := width g x e)
    (SequentialStackBinary.pack (width g x e) (SequentialFront.suffixCode (compilerNodes g e) (SequentialFront.tail c)))
    hE hb hscratch (by simpa only [hP] using hR)
  exact ⟨_, by simpa only [hP, hP'] using hr⟩

theorem transition_tape (g : MGrammar) (x : List Char) (e : MExp) (r : Res) (m p : Nat)
    (E : CaptureEnv) (b : MExp) (K : List SequentialStack.Frame)
    (h : SequentialStack.Runs g x (initial g x e) (before r m p E b K)) (τ : Tapes 11)
    (hτ : Rep (SequentialFieldFetch.start (width g x e) (encode (compilerNodes g e) (before r m p E b K)) [] [] 0 []) τ) :
    ∃ t τ', Exec (TFits (space g x e (before r m p E b K))) program.compile τ t (.cont τ') ∧
      Rep (SequentialFieldFetch.start (width g x e) (encode (compilerNodes g e) (next r m p E b K)) [] [] 0 []) τ' := by
  obtain ⟨_, hr⟩ := transition_runs g x e r m p E b K h
  obtain ⟨t, τ', _, he, hr'⟩ := runs_tape hr τ hτ
  exact ⟨t, τ', he, hr'⟩

end Shallot.MacroPeg.CBV.SequentialAltReturnMachine
