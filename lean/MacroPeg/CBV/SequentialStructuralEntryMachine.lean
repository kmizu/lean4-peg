import MacroPeg.CBV.SequentialStructuralEntry
import MacroPeg.CBV.SequentialLocalPipeline

namespace Shallot.MacroPeg.CBV.SequentialStructuralEntryMachine
open Complexity Complexity.BinaryWord SequentialStack SequentialStackCodec SequentialStackCodecBound
open SequentialStackBinary SequentialStackPayload CBVtoCBN SequentialStructuralEntry
open SequentialFrameBuild (Mode)
open SequentialFrontRead (locals frontSpace)

def before (mode : Mode) (m p : Nat) (E : CaptureEnv) (a b : MExp) (K : List SequentialStack.Frame) : Config :=
  ⟨.expr m E (source mode a b) p,K⟩
def next (mode : Mode) (m p : Nat) (E : CaptureEnv) (a b : MExp) (K : List SequentialStack.Frame) : Config :=
  localNext mode m p E a b K
def program (ns : List CompileNode) : LProg 11 := SequentialLocalPipeline.program (localProgram ns)

noncomputable def space (g : MGrammar) (x : List Char) (e : MExp) (c : Config) : Nat :=
  frontSpace g x e c + (19 + 9 * arityBudget g) * (numberBound g x e + 1) +
    scratchSpace (arityBudget g) (SequentialStackPool.exprPool (compilerNodes g e)).length (numberBound g x e)

def slope (A H : Nat) : Nat := 19 + 9*A + cellBound A + stepBound A H
def offset (A H : Nat) : Nat := 19 + 9*A + cellBound A + stepBound A H * (stepBound A H + 1) + 2

theorem space_eq (g : MGrammar) (x : List Char) (e : MExp) (c : Config) :
    space g x e c = frontSpace g x e c + slope (arityBudget g) (SequentialStackPool.exprPool (compilerNodes g e)).length * numberBound g x e + offset (arityBudget g) (SequentialStackPool.exprPool (compilerNodes g e)).length := by
  unfold space
  rw [scratchSpace_linear]
  simp only [slope,offset,Nat.add_mul,Nat.mul_add,Nat.mul_one]
  omega

theorem space_bound (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : SequentialStack.Runs g x (initial g x e) c) :
    let A := arityBudget g
    let H := (SequentialStackPool.exprPool (compilerNodes g e)).length
    let C := slope A H
    let D := offset A H
    space g x e c ≤
      (((13 + 6*A + 4) * (numberCoefficient g e + 1) + 8) +
        (C * numberCoefficient g e + D)) * (x.length+1) +
      (cellCoefficient g e * (x.length+1)) *
        ((x.length+1).log2 + (numberCoefficient g e).log2 + 2) := by
  dsimp only
  let C := slope (arityBudget g) (SequentialStackPool.exprPool (compilerNodes g e)).length
  let D := offset (arityBudget g) (SequentialStackPool.exprPool (compilerNodes g e)).length
  have hf := SequentialFrontRead.frontSpace_bound g x e c h
  have hn := numberBound_linear g x e
  have hm := Nat.mul_le_mul_left C hn
  have hd : D ≤ D * (x.length+1) := Nat.le_mul_of_pos_right _ (by omega)
  have hs : C * numberBound g x e + D ≤ (C * numberCoefficient g e + D) * (x.length+1) := by
    have heq : (C * numberCoefficient g e + D) * (x.length+1) =
        C * (numberCoefficient g e * (x.length+1)) + D * (x.length+1) := by
      rw [Nat.add_mul,Nat.mul_assoc]
    rw [heq]
    omega
  let F := (13 + 6*arityBudget g + 4) * (numberCoefficient g e + 1) + 8
  let L := (cellCoefficient g e * (x.length+1)) *
    ((x.length+1).log2 + (numberCoefficient g e).log2 + 2)
  have hf' : frontSpace g x e c ≤ F * (x.length+1) + L := hf
  have hh := Nat.add_le_add hf' hs
  rw [space_eq]
  change frontSpace g x e c + C * numberBound g x e + D ≤
    (F + (C * numberCoefficient g e + D)) * (x.length+1) + L
  rw [Nat.add_mul]
  omega

theorem transition_runs (g : MGrammar) (x : List Char) (e : MExp) (mode : Mode) (m p : Nat) (E : CaptureEnv)
    (a b : MExp) (K : List SequentialStack.Frame)
    (h : SequentialStack.Runs g x (initial g x e) (before mode m p E a b K)) :
    ∃ T, Complexity.Runs (LenOK (space g x e (before mode m p E a b K))) (program (compilerNodes g e))
      (SequentialFieldFetch.start (width g x e) (encode (compilerNodes g e) (before mode m p E a b K)) [] [] 0 [])
      (SequentialFieldFetch.start (width g x e) (encode (compilerNodes g e) (next mode m p E a b K)) [] [] 0 []) T := by
  let c := before mode m p E a b K
  let d := next mode m p E a b K
  let lc := localNext mode m p E a b (K.take 1)
  let N := numberBound g x e
  let B := space g x e c
  let F := SequentialFront.suffixCode (compilerNodes g e) (K.take 1)
  let k := (K.take 1).length + (K.drop 1).length
  let P := inputFields m p (exprId (compilerNodes g e) (source mode a b)) k E F
  let P' := outputFields mode m p (exprId (compilerNodes g e) a) (secondId (compilerNodes g e) mode a b) k E F
  let S := SequentialFront.suffixCode (compilerNodes g e) (SequentialFront.tail c)
  have hP : SequentialFront.prefixCode (compilerNodes g e) (SequentialFront.tail c) (SequentialFront.front c) = P :=
    input_prefix _ mode m p E a b _ _
  have hP' : SequentialFront.prefixCode (compilerNodes g e) (SequentialFront.tail c) lc = P' :=
    output_prefix _ mode m p E a b _ _
  have hs : step g x c = some d := original_step g x mode m p E a b K
  have hsl : step g x (SequentialFront.front c) = some lc := original_step g x mode m p E a b (K.take 1)
  have hd : d = SequentialFront.attach (SequentialFront.tail c) lc := by
    cases K <;> simp [d,next,c,before,lc,localNext,SequentialFront.attach,SequentialFront.tail]
  have hcode : encode (compilerNodes g e) c = P ++ S := by
    simpa only [hP] using SequentialFront.encode_front (compilerNodes g e) c
  have hcode' : encode (compilerNodes g e) d = P' ++ S := by
    rw [hd,SequentialFront.encode_attach,hP']
  have hb : ∀ v ∈ P, v ≤ N := by
    intro v hv
    apply reachable_numbers g x e c h v
    rw [hcode]
    exact List.mem_append_left _ hv
  have hE : E.length ≤ arityBudget g := by
    obtain ⟨kind,ht,hK⟩ := reachable_typed g x e c h
    change TaskTyped x.length (arityBudget g) (SequentialClock.positionClock g x.length)
      (.expr m E (source mode a b) p) kind at ht
    cases ht with
    | expr _ _ _ _ hm hE hp => exact hE.2
  have hpool : SequentialStackPool.ExprOK (compilerNodes g e) (source mode a b) :=
    (SequentialStackPool.reachable_ok g x e c h).1
  have hF : F.length ≤ 6 + 3 * arityBudget g := by
    obtain ⟨kind,ht,hK⟩ := reachable_typed g x e c h
    have hframes := frames_length (compilerNodes g e) hK
    cases K with
    | nil => simp [F,SequentialFront.suffixCode]
    | cons f K =>
      have hh := hframes f (by simp [c,before])
      simpa [F,SequentialFront.suffixCode] using hh
  have hfront : frontSpace g x e c ≤ B := by dsimp [B,space]; omega
  have hscratch : scratchSpace (arityBudget g) (SequentialStackPool.exprPool (compilerNodes g e)).length N ≤ B := by dsimp [B,N,space]; omega
  have hnum : N+3 ≤ B := by
    have hh : N+3 ≤ scratchSpace (arityBudget g) (SequentialStackPool.exprPool (compilerNodes g e)).length N := by
      unfold scratchSpace SequentialNumericFive.scratchSpace cellBound
      rw [Nat.add_mul]; omega
    omega
  have hlen : P'.length ≤ 19 + 9 * arityBudget g := by
    obtain ⟨other,he,_,_,hlen⟩ := SequentialFront.reachable_step_prefix g x e c d h hs
    have heq : other = lc := Option.some.inj (he.symm.trans hsl)
    subst other
    rwa [hP'] at hlen
  have hwidth : width g x e ≤ N+1 := by
    have hh := Nat.log2_le_self N
    change N.log2+1 ≤ N+1
    omega
  have hm := Nat.mul_le_mul hlen hwidth
  have hsource : (encodeBits (compilerNodes g e) (width g x e) c).length + 2 ≤ frontSpace g x e c := by
    unfold frontSpace; omega
  have hfinal : (encodeBits (compilerNodes g e) (width g x e) d).length + 2 ≤ B := by
    simp only [encodeBits,hcode,hcode',SequentialStackBinary.pack_length,List.length_append,Nat.add_mul] at hsource ⊢
    have hcap : frontSpace g x e c + (19 + 9 * arityBudget g) * (N+1) ≤ B := by dsimp [B,space,N]; omega
    omega
  apply SequentialLocalPipeline.transition_runs g x e c d lc h hs hd (localProgram (compilerNodes g e)) B hfront hnum hfinal
  intro held hR
  have hr := local_runs (compilerNodes g e) mode a b hpool m p k E F (width := width g x e)
    (SequentialStackBinary.pack (width g x e) S) hE hF hb hscratch
    (by simpa only [hP] using hR)
  exact ⟨_,by simpa only [hP,hP'] using hr⟩

theorem transition_tape (g : MGrammar) (x : List Char) (e : MExp) (mode : Mode) (m p : Nat) (E : CaptureEnv)
    (a b : MExp) (K : List SequentialStack.Frame)
    (h : SequentialStack.Runs g x (initial g x e) (before mode m p E a b K)) (τ : Tapes 11)
    (hτ : Rep (SequentialFieldFetch.start (width g x e) (encode (compilerNodes g e) (before mode m p E a b K)) [] [] 0 []) τ) :
    ∃ t τ', Exec (TFits (space g x e (before mode m p E a b K))) (program (compilerNodes g e)).compile τ t (.cont τ') ∧
      Rep (SequentialFieldFetch.start (width g x e) (encode (compilerNodes g e) (next mode m p E a b K)) [] [] 0 []) τ' := by
  obtain ⟨_,hr⟩ := transition_runs g x e mode m p E a b K h
  obtain ⟨t,τ',_,he,hr'⟩ := runs_tape hr τ hτ
  exact ⟨t,τ',he,hr'⟩
end Shallot.MacroPeg.CBV.SequentialStructuralEntryMachine
