import MacroPeg.CBV.SequentialStarReturn

namespace Shallot.MacroPeg.CBV.SequentialStarDispatch
open Complexity SequentialStack SequentialStackCodec SequentialStackPool CBVtoCBN SequentialStarReturn
open SequentialNotReturn (prepend applied prepend_runs constants tag)
open SequentialSeqReturn (st reg)
open SequentialArgHeadReturn (bnd_cells annotate end_fits)

def inputFields (r : Res) (k m p a : Nat) (E : List Nat) : List Nat :=
  [3,0] ++ writeRes r ++ [k+1,3,m,p,a] ++ E

def outputFields (ns : List CompileNode) (a : MExp) (r : Res) (k m p : Nat) (E : List Nat) : List Nat :=
  match r with
  | none => [3,0,0,k]
  | some none => [3,0,2,p,k]
  | some (some q) => successFields ns a q k m p E

def remaining (r : Res) (k m p a : Nat) (E : List Nat) : List Nat :=
  match r with
  | none | some none => E.reverse ++ [a,p,m,3,k+1]
  | some (some q) => E.reverse ++ [a,p,m,3,k+1,q]

def branches (ns : List CompileNode) : List (NProg 4) := [baseProgram false,baseProgram true,successCore ns]
def readStatus : NProg 4 := .seq (nmvAll 0 1 (by decide))
  (prepend [.pop 1] (.prim (.pop 1)))
def numeric (ns : List CompileNode) : NProg 4 := .seq readStatus (caseTop 1 (branches ns) (.halt false))
def localProgram (ns : List CompileNode) : LProg 11 := (numeric ns).compile.rename reg

theorem readStatus_runs (r : Res) (k m p a : Nat) (E : List Nat) :
    NRuns readStatus (st (inputFields r k m p a E) [] [] [])
      (st [] (remaining r k m p a E ++ [tag r]) [] []) (3 * E.length + 30) := by
  let S := st (inputFields r k m p a E) [] [] []
  let R := (S.set 1 (S 1 ++ (S 0).reverse)).set 0 []
  have hr := nruns_mvAll 0 1 (by decide : (0 : Fin 4) ≠ 1) S
  have hp := prepend_runs [.pop 1] (.prim (.pop 1)) R _ 1 (nruns_prim _ _)
  have he : (NPrim.pop 1).apply (applied [.pop 1] R) =
      st [] (remaining r k m p a E ++ [tag r]) [] [] := by
    cases r <;> (try (rename_i rr; cases rr))
    all_goals
      funext i
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi with rfl | rfl | rfl | rfl <;>
        simp [R,S,st,inputFields,remaining,tag,writeRes,applied,NPrim.apply,Lists.set,List.append_assoc]
  rw [he] at hp
  exact (hr.seq hp).mono (by cases r <;> (try (rename_i rr; cases rr)) <;>
    simp [S,st,inputFields,writeRes] <;> omega)


theorem numeric_exec (ns : List CompileNode) (a : MExp) (ha : ExprOK ns a) (r : Res) (k m p : Nat) (E : List Nat) {A N B : Nat}
    (hE : E.length ≤ 1 + 2 * A) (hb : ∀ v ∈ inputFields r k m p (exprId ns a) E, v ≤ N)
    (hspace : scratchSpace A (exprPool ns).length N ≤ B) :
    ∃ t, t ≤ 3 * stepBound A (exprPool ns).length + 4 * N + 13 ∧ NExec (NFits B) (numeric ns)
      (st (inputFields r k m p (exprId ns a) E) [] [] []) t
      (.cont (st (outputFields ns a r k m p E) [] [] [])) := by
  have hb₀ : Bnd N (cellBound A * (N+1)) (st (inputFields r k m p (exprId ns a) E) [] [] []) := by
    apply bnd_cells
    · intro i
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi with rfl | rfl | rfl | rfl
      all_goals cases r <;> (try (rename_i rr; cases rr)) <;>
        simp [st,inputFields,writeRes,cellBound] <;> omega
    · intro i v hv
      by_cases hi : i = 0
      · exact hb v (by simpa [st,hi] using hv)
      · simp [st,hi] at hv
  have hr := (readStatus_runs r k m p (exprId ns a) E).mono
    (show 3 * E.length + 30 ≤ stepBound A (exprPool ns).length by unfold stepBound; omega)
  obtain ⟨t₁,ht₁,he₁⟩ := annotate hr hb₀ hspace
  let R := st [] (remaining r k m p (exprId ns a) E ++ [tag r]) [] []
  let F := st (outputFields ns a r k m p E) [] [] []
  have hR : NFits B R := end_fits he₁
  have hpop : R.set 1 (remaining r k m p (exprId ns a) E) = st [] (remaining r k m p (exprId ns a) E) [] [] := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;> simp [R,st,Lists.set]
  have hb₁ : Bnd N (cellBound A * (N+1)) (st [] (remaining r k m p (exprId ns a) E) [] []) := by
    have hrem : ∀ v ∈ remaining r k m p (exprId ns a) E, v ≤ N := by
      intro v hv
      apply hb v
      cases r <;> (try (rename_i rr; cases rr)) <;>
        simp [inputFields,remaining,writeRes] at hv ⊢
      all_goals
        rcases hv with hv | hv
        · simp [hv]
        · omega
    apply bnd_cells
    · intro i
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi with rfl | rfl | rfl | rfl
      all_goals cases r <;> (try (rename_i rr; cases rr)) <;>
        simp [st,remaining,cellBound] <;> omega
    · intro i v hv
      by_cases hi : i = 1
      · exact hrem v (by simpa [st,hi] using hv)
      · simp [st,hi] at hv
  have hbranch : ∃ t, t ≤ 2 * stepBound A (exprPool ns).length + 4 * N + 7 ∧
      NExec (NFits B) ((branches ns)[tag r]'(by
        cases r <;> (try (rename_i rr; cases rr)) <;> simp [branches,tag]))
        (R.set 1 (remaining r k m p (exprId ns a) E)) t (.cont F) := by
    rw [hpop]
    cases r with
    | none =>
      have hf := (base_runs false k m p (exprId ns a) E).mono
        (show 3 * E.length + 40 ≤ stepBound A (exprPool ns).length by unfold stepBound; omega)
      obtain ⟨t,ht,he⟩ := annotate hf hb₁ hspace
      exact ⟨t,by omega,he⟩
    | some r => cases r with
      | none =>
        have hf := (base_runs true k m p (exprId ns a) E).mono
          (show 3 * E.length + 40 ≤ stepBound A (exprPool ns).length by unfold stepBound; omega)
        obtain ⟨t,ht,he⟩ := annotate hf hb₁ hspace
        exact ⟨t,by omega,he⟩
      | some q =>
        have hq : q ≤ N := hb q (by simp [inputFields,writeRes])
        have hbq : ∀ v ∈ E.reverse ++ [exprId ns a,p,m,3,k+1,q], v ≤ N := by
          intro v hv
          apply hb v
          simp [List.mem_append,List.mem_reverse] at hv
          rcases hv with hv | hv
          · simp [inputFields,writeRes,hv]
          · simp [inputFields,writeRes]
            omega
        obtain ⟨t,ht,he⟩ := core_exec ns a ha q k m p E hE hbq hspace
        exact ⟨t,by omega,he⟩
  obtain ⟨t₂,ht₂,he₂⟩ := NShrinkingCompare.caseTop_exec 1 (branches ns) (.halt false) (tag r)
    (by cases r <;> (try (rename_i rr; cases rr)) <;> simp [branches,tag])
    R (remaining r k m p (exprId ns a) E) rfl hR F (2 * stepBound A (exprPool ns).length + 4 * N + 7) hbranch
  have htag : tag r ≤ 2 := by cases r <;> (try (rename_i rr; cases rr)) <;> simp [tag]
  exact ⟨t₁+t₂,by omega,.seqC he₁ he₂⟩

theorem local_runs (ns : List CompileNode) (a : MExp) (ha : ExprOK ns a) (r : Res) (k m p : Nat) (E : List Nat) {A N B width held : Nat} (tail : List Bool)
    (hE : E.length ≤ 1 + 2 * A) (hb : ∀ v ∈ inputFields r k m p (exprId ns a) E, v ≤ N)
    (hspace : scratchSpace A (exprPool ns).length N ≤ B)
    (hR : LenOK B (SequentialFieldFetch.start width [] tail (SequentialFrontRead.locals (inputFields r k m p (exprId ns a) E)) held [])) :
    Complexity.Runs (LenOK B) (localProgram ns)
      (SequentialFieldFetch.start width [] tail (SequentialFrontRead.locals (inputFields r k m p (exprId ns a) E)) held [])
      (SequentialFieldFetch.start width [] tail (SequentialFrontRead.locals (outputFields ns a r k m p E)) held [])
      ((3 * stepBound A (exprPool ns).length + 4 * N + 13) * ncost B) :=
  SequentialNumericBlock.annotated_local_runs (numeric ns) _ _ tail (numeric_exec ns a ha r k m p E hE hb hspace) hR


def localNext (r : Res) (m p : Nat) (E : CaptureEnv) (a : MExp) : Config :=
  match r with
  | none => ⟨.value (.expr none), []⟩
  | some none => ⟨.value (.expr (some (some p))), []⟩
  | some (some q) =>
    if q < p then ⟨.expr m E (.star a) q, []⟩ else ⟨.value (.expr none), []⟩

theorem original_step (g : MGrammar) (x : List Char) (r : Res) (m p : Nat) (E : CaptureEnv)
    (a : MExp) (K : List SequentialStack.Frame) :
    step g x ⟨.value (.expr r), .star m E a p :: K⟩ =
      some (SequentialFront.attach K (localNext r m p E a)) := by
  cases r with
  | none => rfl
  | some r => cases r with
    | none => rfl
    | some q => by_cases hq : q < p <;> simp [step,localNext,hq,SequentialFront.attach]

theorem input_prefix (ns : List CompileNode) (r : Res) (m p : Nat) (E : CaptureEnv) (a : MExp)
    (K : List SequentialStack.Frame) :
    SequentialFront.prefixCode ns K ⟨.value (.expr r), [.star m E a p]⟩ =
      inputFields r K.length m p (exprId ns a) (writeEnv E) := by
  cases r <;> (try (rename_i rr; cases rr)) <;>
    simp [SequentialFront.prefixCode, SequentialFront.suffixCode, inputFields, writeTask, writeValue,
      writeRes, writeFrame, writeExpr, Nat.add_comm]

theorem output_prefix (ns : List CompileNode) (r : Res) (m p : Nat) (E : CaptureEnv) (a : MExp)
    (K : List SequentialStack.Frame) :
    SequentialFront.prefixCode ns K (localNext r m p E a) =
      outputFields ns a r K.length m p (writeEnv E) := by
  cases r with
  | none => simp [SequentialFront.prefixCode,SequentialFront.suffixCode,localNext,outputFields,writeTask,writeValue,writeRes]
  | some r => cases r with
    | none => simp [SequentialFront.prefixCode,SequentialFront.suffixCode,localNext,outputFields,writeTask,writeValue,writeRes]
    | some q =>
      by_cases hq : q < p <;>
        simp [SequentialFront.prefixCode,SequentialFront.suffixCode,localNext,outputFields,successFields,hq,
          writeTask,writeValue,writeRes,writeExpr]

end Shallot.MacroPeg.CBV.SequentialStarDispatch
