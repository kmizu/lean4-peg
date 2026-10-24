import Complexity.NBoundedConstant
import MacroPeg.CBV.SequentialAtomCodec
import MacroPeg.CBV.SequentialParamMachine
import MacroPeg.CBV.SequentialLiteralRead

/-! Convert the common successful-read marker and cursor into the evaluator's
ordinary value-task encoding, preserving the original input and frame fields. -/
namespace Shallot.MacroPeg.CBV.SequentialAtomResult
open Complexity Complexity.NBoundedTransfer

/-- The common thirteen-register return layout: input, optional source cursor,
target position, marker/status, following fields, and encoded output. -/
def state (X S Q H R D : List Nat) : Lists 13 := fun i =>
  if i=0 then X else if i=7 then S else if i=8 then Q else if i=9 then H else
  if i=11 then R else if i=12 then D else []

def result (q : Nat) (b : Bool) : Res := some (if b then some q else none)

def input (X S : List Nat) (q : Nat) (b : Bool) (R : List Nat) : Lists 13 :=
  state X S [q] (if b then [0] else []) R []
def ready (X : List Nat) (q : Nat) (b : Bool) (R : List Nat) : Lists 13 :=
  state X [] [q] [if b then 2 else 1] R []
def output (X D : List Nat) : Lists 13 := state X [] [] [] [] D

def reg (i : Fin 5) : Fin 13 :=
  if i=0 then 12 else if i=1 then 11 else if i=2 then 9 else if i=3 then 8 else 10

theorem reg_injective : Function.Injective reg := by unfold Function.Injective; decide

private theorem set9 (X S Q H R D L : List Nat) :
    (state X S Q H R D).set 9 L = state X S Q L R D := by
  funext i
  by_cases hi : i=9
  · subst i; simp [state,Lists.set]
  · simp [state,Lists.set,hi]

def normalize : NProg 13 := .seq (.prim (.pop 7))
  (.ite 9 .zero (.seq (.prim (.pop 9)) (npushC 9 2)) (npushC 9 1))

theorem normalize_runs (X S R : List Nat) (q : Nat) (b : Bool) {B : Nat}
    (hS : S.length ≤ 1) (hR : NFits B (input X S q b R)) (hB : 5 ≤ B) :
    FitsRuns B normalize (input X S q b R) (ready X q b R) 6 := by
  let A := state X [] [q] (if b then [0] else []) R []
  let Z := state X [] [q] [] R []
  have hdrop : S.dropLast = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp only [List.length_dropLast]
    omega
  have heA : (NPrim.pop (K := 13) 7).apply (input X S q b R) = A := by
    funext i
    by_cases hi : i=7
    · subst i; simp [NPrim.apply,input,state,A,Lists.set,hdrop]
    · simp [NPrim.apply,input,state,A,Lists.set,hi]
  have hA : NFits B A := by
    have hh := NShrinkingCompare.fits_pop hR 7
    rwa [heA] at hh
  have hp : FitsRuns B (.prim (.pop 7)) (input X S q b R) A 1 := by
    refine ⟨1,by omega,?_⟩
    rw [← heA]
    exact .prim hR (by rwa [heA])
  have hb : FitsRuns B (.ite 9 .zero (.seq (.prim (.pop 9)) (npushC 9 2)) (npushC 9 1))
      A (ready X q b R) 5 := by
    cases b with
    | false =>
      have hh := NBoundedConstant.push_runs (K := 13) 9 A (by simp [A,state]) hA 1 (by omega)
      have he : A.set 9 [1] = ready X q false R := by simp [A,ready,set9]
      rw [he] at hh
      obtain ⟨t,ht,he⟩ := hh
      exact ⟨t+1,by omega,.iteF hA (by simp [A,state,NTest.eval]) he⟩
    | true =>
      have heZ : (NPrim.pop (K := 13) 9).apply A = Z := by simp [A,Z,NPrim.apply,state,set9]
      have hZ : NFits B Z := by
        have hh := NShrinkingCompare.fits_pop hA 9
        rwa [heZ] at hh
      have hc : FitsRuns B (.prim (.pop 9)) A Z 1 := by
        refine ⟨1,by omega,?_⟩
        rw [← heZ]
        exact .prim hA (by rwa [heZ])
      have hh := NBoundedConstant.push_runs (K := 13) 9 Z (by simp [Z,state]) hZ 2 (by omega)
      have he : Z.set 9 [2] = ready X q true R := by simp [Z,ready,set9]
      rw [he] at hh
      obtain ⟨t,ht,he⟩ := hc.seq hh
      exact ⟨t+1,by omega,.iteT hA (by simp [A,state,NTest.eval]) he⟩
  exact hp.seq hb

private theorem frame_output (X : List Nat) (q : Nat) (b : Bool) (R D : List Nat) :
    (SequentialNumericFive.st D [] [] [] []).frame reg (ready X q b R) = output X D := by
  funext j
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 := by omega
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | simpa [reg,output,state] using Lists.frame_get reg_injective (ready X q b R) (SequentialNumericFive.st D [] [] [] []) 0
    | simpa [reg,output,state] using Lists.frame_get reg_injective (ready X q b R) (SequentialNumericFive.st D [] [] [] []) 1
    | simpa [reg,output,state] using Lists.frame_get reg_injective (ready X q b R) (SequentialNumericFive.st D [] [] [] []) 2
    | simpa [reg,output,state] using Lists.frame_get reg_injective (ready X q b R) (SequentialNumericFive.st D [] [] [] []) 3
    | simpa [reg,output,state] using Lists.frame_get reg_injective (ready X q b R) (SequentialNumericFive.st D [] [] [] []) 4
    | exact (Lists.frame_outside (ρ := reg) _ _ _ (by decide)).trans (by rfl)

def program : NProg 13 := .seq normalize (SequentialAtomCodec.finish.rename reg reg_injective)

theorem result_runs (X S : List Nat) (q k : Nat) (b : Bool) (F : List Nat) {B M N e : Nat}
    (hS : S.length ≤ 1) (hR : NFits B (input X S q b ([k] ++ F).reverse)) (h5 : 5 ≤ B)
    (hF : F.length ≤ M)
    (hbound : Bnd N e (SequentialNumericFive.st [] ([k] ++ F).reverse
      [SequentialAtomCodec.status (result q b)] [q] []))
    (hB : e+grow N (3*M+30)+2 ≤ B) :
    FitsRuns B program (input X S q b ([k] ++ F).reverse)
      (output X (SequentialAtomCodec.outputFields (result q b) k F)) (3*M+36) := by
  have hn := normalize_runs X S ([k] ++ F).reverse q b hS hR h5
  have hQ : NFits B (ready X q b ([k] ++ F).reverse) := by obtain ⟨_,_,he⟩ := hn; exact he.post
  have hpos : SequentialAtomCodec.position (result q b) q = q := by cases b <;> rfl
  have hs : SequentialAtomCodec.status (result q b) = if b then 2 else 1 := by cases b <;> rfl
  have hh := SequentialAtomCodec.finish_fits (result q b) q k F hF (by simpa only [hpos] using hbound) hB
  rw [hpos] at hh
  have hproj : ∀ i, ready X q b ([k] ++ F).reverse (reg i) =
      SequentialNumericFive.st [] ([k] ++ F).reverse [SequentialAtomCodec.status (result q b)] [q] [] i := by
    intro i
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp [ready,state,reg,hs]
  have hf := hh.rename_frame reg_injective _ hQ
  rw [Lists.frame_eq reg_injective _ _ hproj,frame_output] at hf
  obtain ⟨t,ht,he⟩ := hn.seq hf
  exact ⟨t,by omega,he⟩

def cells (M N : Nat) : Nat := (M+3)*(N+1)
def space (M N : Nat) : Nat := cells M N+grow N (3*M+30)+2

theorem space_linear (M N : Nat) :
    space M N = ((M+3)+(3*M+30))*N + ((M+3)+(3*M+30)*(3*M+31)+2) := by
  simp only [space,cells,grow,Nat.mul_add,Nat.add_mul,Nat.mul_one]
  omega

private theorem fields_bound (q k : Nat) (b : Bool) (F : List Nat) {M N : Nat}
    (h2 : 2 ≤ N) (hq : q ≤ N) (hk : k ≤ N) (hF : F.length ≤ M) (hFb : ∀ v ∈ F, v ≤ N) :
    Bnd N (cells M N) (SequentialNumericFive.st [] ([k] ++ F).reverse
      [SequentialAtomCodec.status (result q b)] [q] []) := by
  have ht : SequentialAtomCodec.status (result q b) ≤ N := by cases b <;> simp [result,SequentialAtomCodec.status] <;> omega
  have hr : ∀ v ∈ [k] ++ F, v ≤ N := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · have he : v=k := List.mem_singleton.mp hv
      simpa only [he] using hk
    · exact hFb v hv
  have hc : (Complexity.encS ([k] ++ F)).length ≤ cells M N := by
    have hh := SequentialFrontRead.locals_length ([k] ++ F) N hr
    change (Complexity.encS ([k] ++ F)).length ≤ ([k] ++ F).length*(N+1) at hh
    have hlen : ([k] ++ F).length ≤ M+3 := by simp; omega
    exact Nat.le_trans hh (Nat.mul_le_mul_right (N+1) hlen)
  have hN : N+1 ≤ cells M N := by
    simpa only [Nat.one_mul,cells] using Nat.mul_le_mul_right (N+1) (show 1 ≤ M+3 by omega)
  constructor
  · intro i v hv
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · simp at hv
    · exact hr v (by simpa [List.mem_append,or_comm] using hv)
    · have he : v=SequentialAtomCodec.status (result q b) := by simpa using hv
      subst v; exact ht
    · have he : v=q := by simpa using hv
      subst v; exact hq
    · simp at hv
  · intro i
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · simp [Complexity.encS]
    · change (Complexity.encS (([k] ++ F).reverse)).length ≤ cells M N
      rw [NBoundedTransfer.reverse_length]
      exact hc
    · simp [Complexity.encS,encN]; omega
    · simp [Complexity.encS,encN]; omega
    · simp [Complexity.encS]

theorem bounded_result_runs (X S : List Nat) (q k : Nat) (b : Bool) (F : List Nat) {B M N : Nat}
    (hS : S.length ≤ 1) (hR : NFits B (input X S q b ([k] ++ F).reverse))
    (h2 : 2 ≤ N) (hq : q ≤ N) (hk : k ≤ N) (hF : F.length ≤ M) (hFb : ∀ v ∈ F, v ≤ N)
    (hB : space M N ≤ B) :
    FitsRuns B program (input X S q b ([k] ++ F).reverse)
      (output X (SequentialAtomCodec.outputFields (result q b) k F)) (3*M+36) := by
  have h5 : 5 ≤ B := by
    have hh := Nat.mul_le_mul_right (N+1) (show 3 ≤ M+3 by omega)
    change 3*(N+1) ≤ cells M N at hh
    unfold space at hB
    omega
  exact result_runs X S q k b F hS hR h5 hF (fields_bound q k b F h2 hq hk hF hFb) hB

theorem input_fits (X R : List Nat) (q : Nat) {B : Nat}
    (hX : (Complexity.encS X).length+2 ≤ B) (hR : (Complexity.encS R).length+2 ≤ B)
    (hq : q+3 ≤ B) : NFits B (input X [] q false R) := by
  refine ⟨by omega,fun i => ?_⟩
  by_cases hi0 : i=0
  · subst i; exact hX
  · by_cases hi8 : i=8
    · subst i; simpa [input,state,Complexity.encS,encN] using hq
    · by_cases hi11 : i=11
      · subst i; exact hR
      · simp [input,state,hi0,hi8,hi11,Complexity.encS]
        omega

theorem frame_size (k : Nat) (F : List Nat) {M N : Nat}
    (hk : k ≤ N) (hF : F.length ≤ M) (hFb : ∀ v ∈ F, v ≤ N) :
    (Complexity.encS (([k] ++ F).reverse)).length+2 ≤ space M N := by
  have hv : ∀ v ∈ [k] ++ F, v ≤ N := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · have he : v=k := List.mem_singleton.mp hv; simpa only [he] using hk
    · exact hFb v hv
  have hh := SequentialFrontRead.locals_length ([k] ++ F) N hv
  change (Complexity.encS ([k] ++ F)).length ≤ ([k] ++ F).length*(N+1) at hh
  have hlen : ([k] ++ F).length ≤ M+3 := by simp; omega
  have hc := Nat.le_trans hh (Nat.mul_le_mul_right (N+1) hlen)
  rw [NBoundedTransfer.reverse_length]
  unfold space cells
  omega

end Shallot.MacroPeg.CBV.SequentialAtomResult
