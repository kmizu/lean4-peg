import MacroPeg.CBV.SequentialStarDispatch
import MacroPeg.CBV.SequentialLocalPipeline

namespace Shallot.MacroPeg.CBV.SequentialStarReturnMachine

open Complexity Complexity.BinaryWord SequentialStack SequentialStackCodec
open SequentialStackBinary SequentialStackCodecBound SequentialStackPayload CBVtoCBN SequentialStarDispatch
open SequentialStarReturn (cellBound stepBound scratchSpace scratchSpace_linear successFields)
open SequentialStackPool
open SequentialFrontRead (locals frontSpace)

def before (r : Res) (m p : Nat) (E : CaptureEnv) (a : MExp) (K : List SequentialStack.Frame) : Config :=
  ⟨.value (.expr r), .star m E a p :: K⟩
def next (r : Res) (m p : Nat) (E : CaptureEnv) (a : MExp) (K : List SequentialStack.Frame) : Config :=
  SequentialFront.attach K (localNext r m p E a)
def program (ns : List CompileNode) : LProg 11 := SequentialLocalPipeline.program (localProgram ns)

noncomputable def space (g : MGrammar) (x : List Char) (e : MExp) (c : Config) : Nat :=
  frontSpace g x e c + scratchSpace (arityBudget g) (exprPool (compilerNodes g e)).length (numberBound g x e)

theorem space_bound (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : SequentialStack.Runs g x (initial g x e) c) :
    let A := arityBudget g
    let H := (exprPool (compilerNodes g e)).length
    let C := cellBound A + stepBound A H
    let D := cellBound A + stepBound A H * (stepBound A H + 1) + 2
    space g x e c ≤
      (((13 + 6 * A + 4) * (numberCoefficient g e + 1) + 8) +
        (C * numberCoefficient g e + D)) * (x.length + 1) +
      (cellCoefficient g e * (x.length + 1)) *
        ((x.length + 1).log2 + (numberCoefficient g e).log2 + 2) := by
  dsimp only
  let C := cellBound (arityBudget g) + stepBound (arityBudget g) (exprPool (compilerNodes g e)).length
  let D := cellBound (arityBudget g) + stepBound (arityBudget g) (exprPool (compilerNodes g e)).length * (stepBound (arityBudget g) (exprPool (compilerNodes g e)).length + 1) + 2
  have hf := SequentialFrontRead.frontSpace_bound g x e c h
  have hn := numberBound_linear g x e
  have hm := Nat.mul_le_mul_left C hn
  have hc : D ≤ D * (x.length + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hs : scratchSpace (arityBudget g) (exprPool (compilerNodes g e)).length (numberBound g x e) ≤
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
  change frontSpace g x e c + scratchSpace (arityBudget g) (exprPool (compilerNodes g e)).length (numberBound g x e) ≤
    ((13 + 6 * arityBudget g + 4) * (numberCoefficient g e + 1) + 8) * (x.length + 1) +
      (C * numberCoefficient g e + D) * (x.length + 1) +
      (cellCoefficient g e * (x.length + 1)) * ((x.length + 1).log2 + (numberCoefficient g e).log2 + 2)
  omega

/-- Execute every repetition return, restarting only on strict progress. -/
theorem transition_runs (g : MGrammar) (x : List Char) (e : MExp) (r : Res) (m p : Nat)
    (E : CaptureEnv) (a : MExp) (K : List SequentialStack.Frame)
    (h : SequentialStack.Runs g x (initial g x e) (before r m p E a K)) :
    ∃ T, Complexity.Runs (LenOK (space g x e (before r m p E a K))) (program (compilerNodes g e))
      (SequentialFieldFetch.start (width g x e) (encode (compilerNodes g e) (before r m p E a K)) [] [] 0 [])
      (SequentialFieldFetch.start (width g x e) (encode (compilerNodes g e) (next r m p E a K)) [] [] 0 []) T := by
  let c := before r m p E a K
  let d := next r m p E a K
  let localResult : Config := localNext r m p E a
  let N := numberBound g x e
  let B := space g x e c
  let P := inputFields r K.length m p (exprId (compilerNodes g e) a) (writeEnv E)
  let P' := outputFields (compilerNodes g e) a r K.length m p (writeEnv E)
  let S := SequentialFront.suffixCode (compilerNodes g e) K
  have hP : SequentialFront.prefixCode (compilerNodes g e) (SequentialFront.tail c) (SequentialFront.front c) = P := by
    simpa [c, before, SequentialFront.front, SequentialFront.tail] using input_prefix (compilerNodes g e) r m p E a K
  have hP' : SequentialFront.prefixCode (compilerNodes g e) (SequentialFront.tail c) localResult = P' := by
    simpa [localResult, c, before, SequentialFront.tail] using output_prefix (compilerNodes g e) r m p E a K
  have hS : SequentialFront.suffixCode (compilerNodes g e) (SequentialFront.tail c) = S := rfl
  have hs : step g x c = some d := original_step g x r m p E a K
  have hd : d = SequentialFront.attach (SequentialFront.tail c) localResult := rfl
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
    have hh := (reachable_payload_bounds g x e c h).2 (.star m E a p) (by simp [c,before])
    exact hh.1.2
  have hE : (writeEnv E).length ≤ 1 + 2 * arityBudget g := by rw [env_length]; omega
  have hstar : ExprOK (compilerNodes g e) (.star a) :=
    (SequentialStackPool.reachable_ok g x e c h).2 (.star m E a p) (by simp [c,before])
  have hfront : frontSpace g x e c ≤ B := by dsimp [B, space]; omega
  have hscratch : scratchSpace (arityBudget g) (exprPool (compilerNodes g e)).length N ≤ B := by dsimp [B, N, space]; omega
  have hnum : N + 3 ≤ B := by
    have hh : N + 3 ≤ scratchSpace (arityBudget g) (exprPool (compilerNodes g e)).length N := by
      unfold scratchSpace SequentialNumericBlock.scratchSpace cellBound
      rw [Nat.add_mul]
      omega
    omega
  have hlen : P'.length ≤ P.length := by
    cases r with
    | none => simp [P,P',inputFields,outputFields,writeRes]
    | some r => cases r with
      | none => simp [P,P',inputFields,outputFields,writeRes]
      | some q => by_cases hq : q < p <;> simp [P,P',inputFields,outputFields,successFields,writeRes,hq] <;> omega
  have hfinal : (encodeBits (compilerNodes g e) (width g x e) d).length + 2 ≤ B := by
    have hR : (encodeBits (compilerNodes g e) (width g x e) c).length + 2 ≤ frontSpace g x e c := by
      unfold frontSpace; omega
    have hm := Nat.mul_le_mul_right (width g x e) hlen
    simp only [encodeBits, hcode, hcode', SequentialStackBinary.pack_length, List.length_append, Nat.add_mul] at hR ⊢
    omega
  apply SequentialLocalPipeline.transition_runs g x e c d localResult h hs hd (localProgram (compilerNodes g e)) B hfront hnum hfinal
  intro held hR
  have hr := local_runs (compilerNodes g e) a hstar.star r K.length m p (writeEnv E)
    (width := width g x e)
    (SequentialStackBinary.pack (width g x e) (SequentialFront.suffixCode (compilerNodes g e) (SequentialFront.tail c)))
    hE hb hscratch (by simpa only [hP] using hR)
  exact ⟨_, by simpa only [hP, hP'] using hr⟩

theorem transition_tape (g : MGrammar) (x : List Char) (e : MExp) (r : Res) (m p : Nat)
    (E : CaptureEnv) (a : MExp) (K : List SequentialStack.Frame)
    (h : SequentialStack.Runs g x (initial g x e) (before r m p E a K)) (τ : Tapes 11)
    (hτ : Rep (SequentialFieldFetch.start (width g x e) (encode (compilerNodes g e) (before r m p E a K)) [] [] 0 []) τ) :
    ∃ t τ', Exec (TFits (space g x e (before r m p E a K))) (program (compilerNodes g e)).compile τ t (.cont τ') ∧
      Rep (SequentialFieldFetch.start (width g x e) (encode (compilerNodes g e) (next r m p E a K)) [] [] 0 []) τ' := by
  obtain ⟨_, hr⟩ := transition_runs g x e r m p E a K h
  obtain ⟨t, τ', _, he, hr'⟩ := runs_tape hr τ hτ
  exact ⟨t, τ', he, hr'⟩

end Shallot.MacroPeg.CBV.SequentialStarReturnMachine
