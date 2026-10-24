import Complexity.ListAppend
import MacroPeg.CBV.SequentialInitializationNumbers

/-! Assemble the six initial fields and emit the complete binary initial stack.
The unary length and clock are consumed, while the original input is retained. -/
namespace Shallot.MacroPeg.CBV.SequentialInitializationFields
open Complexity Complexity.BinaryWord SequentialInputHost SequentialStackCodec SequentialStackCodecBound CBVtoCBN
open SequentialFrontRead (locals)
open SequentialStackBinary

def source (n m w : Nat) (X : List Nat) : Lists 20 :=
  ((SequentialInitializationNumbers.seed n X).set 8 (List.replicate w 1)).set 3 (List.replicate m 1)

def fields (k m n : Nat) : List Nat := [0,m,n,k,0,0]

def assemble (k : Nat) : LProg 20 :=
  .seq (appendP 9 [2,2]) (.seq (moveAll 3 9)
    (.seq (appendP 9 [2]) (.seq (moveAll 13 9)
      (.seq (appendP 9 ([2] ++ List.replicate k 1 ++ [2,2])) (appendP 4 [1,1])))))

def capacity (n m w k : Nat) (X : List Nat) : Nat := n+m+w+k+X.length+20

theorem assemble_runs (n m w k : Nat) (X : List Nat) :
    ∃ T, Complexity.Runs (LenOK (capacity n m w k X)) (assemble k) (source n m w X)
      (extend (SequentialFieldFetch.start w [] [] (locals (fields k m n)) 0 []) X) T := by
  let B := capacity n m w k X
  let S := source n m w X
  have hS : LenOK B S := by
    intro i
    by_cases h3 : i=3 <;> by_cases h8 : i=8 <;> by_cases h11 : i=11 <;> by_cases h13 : i=13 <;>
      simp_all [S,source,SequentialInitializationNumbers.seed,Lists.set,B,capacity] <;> omega
  have h1 := append_runs (9 : Fin 20) [2,2] hS (by simp [S,source,Lists.set,SequentialInitializationNumbers.seed,B,capacity] <;> omega)
  let A := S.set 9 [2,2]
  have heA : S.set 9 (S 9 ++ [2,2]) = A := by simp [A,S,source,Lists.set,SequentialInitializationNumbers.seed]
  rw [heA] at h1
  have hA : LenOK B A := by obtain ⟨_,_,he⟩ := h1; exact he.q_end _ (Or.inl rfl)
  have h2 := moveAll_runs_bounded (src := (3 : Fin 20)) (dst := 9) (by decide) hA (by
    simp [A,S,source,Lists.set,B,capacity] <;> omega)
  let C := (A.set 9 ([2,2] ++ List.replicate m 1)).set 3 []
  have heC : (A.set 9 (A 9 ++ (A 3).reverse)).set 3 [] = C := by
    simp [C,A,S,source,Lists.set]
  rw [heC] at h2
  have hC : LenOK B C := by obtain ⟨_,_,he⟩ := h2; exact he.q_end _ (Or.inl rfl)
  have h3 := append_runs (9 : Fin 20) [2] hC (by
    simp [C,A,Lists.set,B,capacity] <;> omega)
  let D := C.set 9 ([2,2] ++ List.replicate m 1 ++ [2])
  have heD : C.set 9 (C 9 ++ [2]) = D := by simp [D,C,Lists.set]
  rw [heD] at h3
  have hD : LenOK B D := by obtain ⟨_,_,he⟩ := h3; exact he.q_end _ (Or.inl rfl)
  have h4 := moveAll_runs_bounded (src := (13 : Fin 20)) (dst := 9) (by decide) hD (by
    simp [D,C,A,S,source,Lists.set,SequentialInitializationNumbers.seed,B,capacity] <;> omega)
  let E := (D.set 9 ([2,2] ++ List.replicate m 1 ++ [2] ++ List.replicate n 1)).set 13 []
  have heE : (D.set 9 (D 9 ++ (D 13).reverse)).set 13 [] = E := by
    simp [E,D,C,A,S,source,Lists.set,SequentialInitializationNumbers.seed]
  rw [heE] at h4
  have hE : LenOK B E := by obtain ⟨_,_,he⟩ := h4; exact he.q_end _ (Or.inl rfl)
  have h5 := append_runs (9 : Fin 20) ([2] ++ List.replicate k 1 ++ [2,2]) hE (by
    simp [E,D,Lists.set,B,capacity] <;> omega)
  let F := E.set 9 (locals (fields k m n))
  have heF : E.set 9 (E 9 ++ ([2] ++ List.replicate k 1 ++ [2,2])) = F := by
    simp [F,E,Lists.set,locals,fields,List.append_assoc]
  rw [heF] at h5
  have hF : LenOK B F := by obtain ⟨_,_,he⟩ := h5; exact he.q_end _ (Or.inl rfl)
  have h6 := append_runs (4 : Fin 20) [1,1] hF (by
    simp [F,E,D,C,A,S,source,Lists.set,SequentialInitializationNumbers.seed,B,capacity] <;> omega)
  have heout : F.set 4 (F 4 ++ [1,1]) =
      extend (SequentialFieldFetch.start w [] [] (locals (fields k m n)) 0 []) X := by
    funext i
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rfl
  rw [heout] at h6
  exact ⟨_,h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))⟩

theorem initial_fields (g : MGrammar) (x : List Char) (e : MExp) :
    fields (exprId (compilerNodes g e) e) (SequentialClock.positionClock g x.length) x.length =
      encode (compilerNodes g e) (SequentialStack.initial g x e) := by
  simp [fields,encode,SequentialStack.initial,writeTask,writeExpr,writeEnv,writeList]

noncomputable def program (g : MGrammar) (e : MExp) : LProg 20 :=
  .seq (assemble (exprId (compilerNodes g e) e)) (SequentialFrontWrite.writeFront.rename old)

noncomputable def space (g : MGrammar) (x : List Char) (e : MExp) : Nat :=
  capacity x.length (SequentialClock.positionClock g x.length) (width g x e) (exprId (compilerNodes g e) e)
    (Complexity.encS (SequentialInputRead.codes x)) + numberBound g x e + 6*width g x e+10

theorem runs (g : MGrammar) (x : List Char) (e : MExp) :
    ∃ T, Complexity.Runs (LenOK (space g x e)) (program g e)
      (SequentialInitializationNumbers.ready g e x.length (Complexity.encS (SequentialInputRead.codes x)))
      (SequentialStepMachine.state g x e (SequentialStack.initial g x e)) T := by
  let vs := encode (compilerNodes g e) (SequentialStack.initial g x e)
  let X := Complexity.encS (SequentialInputRead.codes x)
  let B := space g x e
  have hcap : capacity x.length (SequentialClock.positionClock g x.length) (width g x e)
      (exprId (compilerNodes g e) e) X ≤ B := by unfold B space X; omega
  obtain ⟨Ta,ha⟩ := assemble_runs x.length (SequentialClock.positionClock g x.length) (width g x e)
    (exprId (compilerNodes g e) e) X
  have has := ha.weaken (fun _ hh i => Nat.le_trans (hh i) hcap)
  have heSource : source x.length (SequentialClock.positionClock g x.length) (width g x e) X =
      SequentialInitializationNumbers.ready g e x.length X := by
    simp [source,SequentialInitializationNumbers.ready,width,SequentialInitializationNumbers.bound_eq]
  rw [heSource,initial_fields] at has
  have hstate : LenOK B (extend (SequentialFieldFetch.start (width g x e) [] [] (locals vs) 0 []) X) := by
    obtain ⟨_,_,he⟩ := has; exact he.q_end _ (Or.inl rfl)
  have hnum := reachable_numbers g x e (SequentialStack.initial g x e) (.refl _)
  have hv : ∀ v ∈ vs, v < 2^(width g x e) := by
    intro v hv
    exact Nat.lt_of_le_of_lt (hnum v hv) Nat.lt_log2_self
  have hval : ∀ v ∈ vs, v+3 ≤ B := by
    intro v hv
    have hh := hnum v hv
    unfold B space; omega
  have hlen : vs.length = 6 := by
    dsimp [vs]
    rw [← initial_fields]
    rfl
  obtain ⟨Tw,hw⟩ := SequentialFrontWrite.write_runs vs [] [] hv hval (extend_project hstate) (by
    simp only [List.length_nil,hlen, Nat.zero_add]
    unfold B space; omega)
  have hh := old_runs _ _ _ X hw (by unfold B space capacity X; omega)
  exact ⟨_,has.seq hh⟩

/-- Assembly and fixed-width emission add only linear workspace. -/
theorem space_linear (g : MGrammar) (e : MExp) :
    ∃ C, ∀ x : List Char, space g x e ≤ C*(x.length+1) := by
  refine ⟨1+(g.rules.length+1)+8*numberCoefficient g e+exprId (compilerNodes g e) e+(2^32+1)+37,?_⟩
  intro x
  have hN := numberBound_linear g x e
  have hw : width g x e ≤ numberCoefficient g e*(x.length+1)+1 := by
    have hh := Nat.log2_le_self (numberBound g x e)
    unfold width
    omega
  have h7 := Nat.mul_le_mul_left 7 hw
  simp only [Nat.mul_add,Nat.mul_one] at h7
  have hk := Nat.le_mul_of_pos_right (exprId (compilerNodes g e) e) (show 0 < x.length+1 by omega)
  have hX := SequentialInputRead.encoded_length x
  have hX' := Nat.le_trans hX (Nat.mul_le_mul_left (2^32+1) (show x.length ≤ x.length+1 by omega))
  have hc : SequentialClock.positionClock g x.length = (g.rules.length+1)*(x.length+1) := rfl
  have h37 : 37 ≤ 37*(x.length+1) := Nat.le_mul_of_pos_right _ (by omega)
  unfold space capacity
  rw [hc]
  simp only [Nat.add_mul,Nat.one_mul,Nat.mul_assoc]
  omega

end Shallot.MacroPeg.CBV.SequentialInitializationFields
