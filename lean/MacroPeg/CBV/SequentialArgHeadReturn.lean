import MacroPeg.CBV.SequentialCaptureMin
import MacroPeg.CBV.SequentialNumericBlock

/-! Return from evaluating an argument: preserve the environment and remaining
arguments, and replace the head frame by the computed capture interval. -/
namespace Shallot.MacroPeg.CBV.SequentialArgHeadReturn
open Complexity SequentialStack SequentialStackCodec CBVtoCBN
open SequentialNotReturn (prepend applied prepend_runs constants)
open SequentialSeqReturn (st reg)

def inputFields (q k m p : Nat) (E : List Nat) : List Nat :=
  [3, 0, 2, q, k + 1, 4, m, p] ++ E

def outputFields (q k m p : Nat) (E : List Nat) : List Nat :=
  [1, m, q] ++ E ++ [k + 1, 5, p, min q p]

def prepareOps : List (NPrim 4) :=
  [.pop 1, .pop 1, .pop 1, .dup 1 2 (by decide), .pop 1,
    .dup 1 3 (by decide), .pop 1, .pop 1] ++ constants 0 1 ++
  [.dup 1 0 (by decide), .pop 1, .dup 2 0 (by decide)]
def prepare : NProg 4 := .seq (nmvAll 0 1 (by decide))
  (prepend prepareOps (.prim (.dup 1 3 (by decide))))

def finishOps : List (NPrim 4) :=
  [.dup 3 0 (by decide)] ++ constants 0 5 ++
  [.dup 2 0 (by decide), .pop 2, .dup 2 0 (by decide), .pop 2]
def finish : NProg 4 := .seq (.prim (.pop 1))
  (.seq (nmvAll 1 0 (by decide)) (prepend finishOps (.prim (.pop 3))))
def numeric : NProg 4 := .seq prepare (.seq SequentialCaptureMin.program finish)
def localProgram : LProg 11 := numeric.compile.rename reg

theorem prepare_runs (q k m p : Nat) (E : List Nat) :
    NRuns prepare (st (inputFields q k m p E) [] [] [])
      (st [1,m,q] (E.reverse ++ [p]) [q] [k+1,p]) (3 * E.length + 40) := by
  let S := st (inputFields q k m p E) [] [] []
  let R := (S.set 1 (S 1 ++ (S 0).reverse)).set 0 []
  have hr := nruns_mvAll 0 1 (by decide : (0 : Fin 4) ≠ 1) S
  have hp := prepend_runs prepareOps (.prim (.dup 1 3 (by decide))) R _ 1 (nruns_prim _ _)
  have he : (NPrim.dup 1 3 (by decide)).apply (applied prepareOps R) =
      st [1,m,q] (E.reverse ++ [p]) [q] [k+1,p] := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp [R,S,st,inputFields,prepareOps,constants,applied,NPrim.apply,mapTop,Lists.set,List.append_assoc]
  rw [he] at hp
  exact (hr.seq hp).mono (by simp [prepareOps, constants, S, st, inputFields]; omega)

theorem mapTop_pair (f : Nat → Nat) (D : List Nat) (a b : Nat) :
    mapTop f (D ++ [a,b]) = D ++ [a,f b] := by
  have he : D ++ [a,b] = (D ++ [a]) ++ [b] := by simp
  rw [he, mapTop_snoc]
  simp

theorem finishOps_apply (D : List Nat) (q k p : Nat) :
    (NPrim.pop 3).apply (applied finishOps (st D [] [min q p,p] [k+1])) =
      st (D ++ [k+1,5,p,min q p]) [] [] [] := by
  funext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;>
    simp [st,finishOps,constants,applied,NPrim.apply,Lists.set,mapTop_pair]

theorem finish_runs (q k m p : Nat) (E : List Nat) :
    NRuns finish (st [1,m,q] (E.reverse ++ [p]) [min q p,p] [k+1])
      (st (outputFields q k m p E) [] [] []) (3 * E.length + 30) := by
  let S := st [1,m,q] (E.reverse ++ [p]) [min q p,p] [k+1]
  let A := st [1,m,q] E.reverse [min q p,p] [k+1]
  let R := st ([1,m,q] ++ E) [] [min q p,p] [k+1]
  have hp := nruns_pop 1 S (l := E.reverse) (v := p) rfl
  have hpop : S.set 1 E.reverse = A := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;> simp [S,A,st,Lists.set]
  rw [hpop] at hp
  have hm := nruns_mvAll 1 0 (by decide : (1 : Fin 4) ≠ 0) A
  have hmove : (A.set 0 (A 0 ++ (A 1).reverse)).set 1 [] = R := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;> simp [A,R,st,Lists.set]
  rw [hmove] at hm
  have hf := prepend_runs finishOps (.prim (.pop 3)) R _ 1 (nruns_prim _ _)
  have he : (NPrim.pop 3).apply (applied finishOps R) = st (outputFields q k m p E) [] [] [] := by
    simpa [R, outputFields, List.append_assoc] using finishOps_apply ([1,m,q] ++ E) q k p
  rw [he] at hf
  exact (hp.seq (hm.seq hf)).mono (by simp [finishOps,constants,A,st]; omega)

def cellBound (A : Nat) : Nat := 14 + 3 * A
def stepBound (A : Nat) : Nat := 18 * A + 120
def scratchSpace (A N : Nat) : Nat := SequentialNumericBlock.scratchSpace (cellBound A) (stepBound A) N

theorem scratchSpace_linear (A N : Nat) :
    scratchSpace A N = (cellBound A + stepBound A) * N +
      (cellBound A + stepBound A * (stepBound A + 1) + 2) :=
  SequentialNumericBlock.scratchSpace_linear _ _ _

theorem bnd_cells (S : Lists 4) {M N : Nat}
    (hlen : ∀ i, (S i).length ≤ M) (hb : ∀ i v, v ∈ S i → v ≤ N) :
    Bnd N (M * (N + 1)) S := by
  refine ⟨hb, fun i => ?_⟩
  exact Nat.le_trans (SequentialFrontRead.locals_length (S i) N (hb i))
    (Nat.mul_le_mul_right _ (hlen i))

theorem annotate {p : NProg 4} {S S' : Lists 4} {M N T B : Nat}
    (hr : NRuns p S S' T) (hb : Bnd N (M * (N + 1)) S)
    (hspace : SequentialNumericBlock.scratchSpace M T N ≤ B) :
    ∃ t, t ≤ T ∧ NExec (NFits B) p S t (.cont S') := by
  obtain ⟨t, ht, he⟩ := hr
  refine ⟨t, ht, (nexec_space he N (M * (N + 1)) hb).2 B ?_⟩
  have hg := grow_mono (m := N) ht
  unfold SequentialNumericBlock.scratchSpace at hspace
  omega

theorem end_fits {B : Nat} {p : NProg 4} {S : Lists 4} {t : Nat} {o : LOutcome 4}
    (h : NExec (NFits B) p S t o) : NFits B o.state := by
  induction h with
  | prim _ h => exact h
  | halt h => exact h
  | seqC _ _ _ ih => exact ih
  | seqS _ ih => exact ih
  | iteT _ _ _ ih => exact ih
  | iteF _ _ _ ih => exact ih
  | loopF h _ => exact h
  | loopC _ _ _ _ _ ih => exact ih
  | loopS _ _ _ ih => exact ih

theorem numeric_exec (q k m p : Nat) (E : List Nat) {A N B : Nat}
    (hE : E.length ≤ 2 + 3 * A) (hb : ∀ v ∈ inputFields q k m p E, v ≤ N)
    (hspace : scratchSpace A N ≤ B) :
    ∃ t, t ≤ 2 * stepBound A + (4 * q + 7) ∧ NExec (NFits B) numeric
      (st (inputFields q k m p E) [] [] []) t
      (.cont (st (outputFields q k m p E) [] [] [])) := by
  have hq : q ≤ N := hb q (by simp [inputFields])
  have hp : p ≤ N := hb p (by simp [inputFields])
  have hm : m ≤ N := hb m (by simp [inputFields])
  have hk : k+1 ≤ N := hb (k+1) (by simp [inputFields])
  have hn : 4 ≤ N := hb 4 (by simp [inputFields])
  have henv : ∀ v ∈ E, v ≤ N := fun v hv => hb v (by simp [inputFields,hv])
  have hb₀ : Bnd N (cellBound A * (N + 1)) (st (inputFields q k m p E) [] [] []) := by
    apply bnd_cells
    · intro i
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi with rfl | rfl | rfl | rfl <;> simp [st,inputFields,cellBound] <;> omega
    · intro i v hv
      by_cases hi : i = 0
      · exact hb v (by simpa [st,hi] using hv)
      · simp [st,hi] at hv
  have hr := (prepare_runs q k m p E).mono (show 3 * E.length + 40 ≤ stepBound A by unfold stepBound; omega)
  obtain ⟨t₁, ht₁, he₁⟩ := annotate hr hb₀ hspace
  have hmid := end_fits he₁
  have hcmp : 2 * max q p + 4 ≤ B := by
    have hx := Nat.mul_le_mul_right (N+1) (show 2 ≤ cellBound A by unfold cellBound; omega)
    have hmax : max q p ≤ N := Nat.max_le.mpr ⟨hq,hp⟩
    unfold scratchSpace SequentialNumericBlock.scratchSpace at hspace
    omega
  obtain ⟨t₂, ht₂, he₂⟩ := SequentialCaptureMin.exec [1,m] E.reverse [k+1] q p hmid hcmp
  have hb₁ : Bnd N (cellBound A * (N + 1))
      (st [1,m,q] (E.reverse ++ [p]) [min q p,p] [k+1]) := by
    apply bnd_cells
    · intro i
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi with rfl | rfl | rfl | rfl <;> simp [st,cellBound] <;> omega
    · intro i v hv
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      have hmin : min q p ≤ N := Nat.le_trans (Nat.min_le_left _ _) hq
      rcases hi with rfl | rfl | rfl | rfl
      · simp [st] at hv
        rcases hv with rfl | rfl | rfl <;> omega
      · simp [st] at hv
        rcases hv with hv | rfl
        · exact henv v hv
        · exact hp
      · simp [st] at hv
        rcases hv with rfl | rfl <;> omega
      · simp [st] at hv
        subst v; exact hk
  have hf := (finish_runs q k m p E).mono (show 3 * E.length + 30 ≤ stepBound A by unfold stepBound; omega)
  obtain ⟨t₃, ht₃, he₃⟩ := annotate hf hb₁ hspace
  exact ⟨t₁ + (t₂ + t₃), by omega, .seqC he₁ (.seqC he₂ he₃)⟩

theorem local_runs (q k m p : Nat) (E : List Nat) {A N B width held : Nat} (tail : List Bool)
    (hE : E.length ≤ 2 + 3 * A) (hb : ∀ v ∈ inputFields q k m p E, v ≤ N)
    (hspace : scratchSpace A N ≤ B)
    (hR : LenOK B (SequentialFieldFetch.start width [] tail (SequentialFrontRead.locals (inputFields q k m p E)) held [])) :
    Complexity.Runs (LenOK B) localProgram
      (SequentialFieldFetch.start width [] tail (SequentialFrontRead.locals (inputFields q k m p E)) held [])
      (SequentialFieldFetch.start width [] tail (SequentialFrontRead.locals (outputFields q k m p E)) held [])
      ((2 * stepBound A + (4 * q + 7)) * ncost B) :=
  SequentialNumericBlock.annotated_local_runs numeric _ _ tail (numeric_exec q k m p E hE hb hspace) hR

theorem original_step (g : MGrammar) (x : List Char) (q m p : Nat) (E : CaptureEnv)
    (es : List MExp) (K : List SequentialStack.Frame) :
    step g x ⟨.value (.expr (some (some q))), .argHead m E es p :: K⟩ =
      some ⟨.args m E es q, .argCons (p, min q p) :: K⟩ := rfl

theorem input_prefix (ns : List CompileNode) (q m p : Nat) (E : CaptureEnv) (es : List MExp)
    (K : List SequentialStack.Frame) :
    SequentialFront.prefixCode ns K ⟨.value (.expr (some (some q))), [.argHead m E es p]⟩ =
      inputFields q K.length m p (writeEnv E ++ writeExprs ns es) := by
  simp [SequentialFront.prefixCode, SequentialFront.suffixCode, inputFields, writeTask, writeValue,
    writeRes, writeFrame, Nat.add_comm]

theorem output_prefix (ns : List CompileNode) (q m p : Nat) (E : CaptureEnv) (es : List MExp)
    (K : List SequentialStack.Frame) :
    SequentialFront.prefixCode ns K ⟨.args m E es q, [.argCons (p, min q p)]⟩ =
      outputFields q K.length m p (writeEnv E ++ writeExprs ns es) := by
  simp [SequentialFront.prefixCode, SequentialFront.suffixCode, outputFields, writeTask,
    writeFrame, Nat.add_comm, List.append_assoc]

end Shallot.MacroPeg.CBV.SequentialArgHeadReturn
