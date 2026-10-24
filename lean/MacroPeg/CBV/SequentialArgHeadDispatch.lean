import MacroPeg.CBV.SequentialArgHeadReturn

/-! One input-driven program for all three outcomes of an argument head. -/
namespace Shallot.MacroPeg.CBV.SequentialArgHeadDispatch
open Complexity SequentialStack SequentialStackCodec CBVtoCBN SequentialArgHeadReturn
open SequentialNotReturn (prepend applied prepend_runs constants tag)
open SequentialSeqReturn (st reg)

def headProgram : NProg 4 := prepend (prepareOps.drop 3) (.prim (.dup 1 3 (by decide)))
def successCore : NProg 4 := .seq headProgram (.seq SequentialCaptureMin.program finish)

theorem head_runs (q k m p : Nat) (E : List Nat) :
    NRuns headProgram (st [] (E.reverse ++ [p,m,4,k+1,q]) [] [])
      (st [1,m,q] (E.reverse ++ [p]) [q] [k+1,p]) (3 * E.length + 40) := by
  have hp := prepend_runs (prepareOps.drop 3) (.prim (.dup 1 3 (by decide)))
    (st [] (E.reverse ++ [p,m,4,k+1,q]) [] []) _ 1 (nruns_prim _ _)
  have he : (NPrim.dup 1 3 (by decide)).apply
      (applied (prepareOps.drop 3) (st [] (E.reverse ++ [p,m,4,k+1,q]) [] [])) =
      st [1,m,q] (E.reverse ++ [p]) [q] [k+1,p] := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp [st,prepareOps,constants,applied,NPrim.apply,mapTop,Lists.set]
  rw [he] at hp
  exact hp.mono (by simp [prepareOps,constants] <;> omega)

theorem core_exec (q k m p : Nat) (E : List Nat) {A N B : Nat}
    (hE : E.length ≤ 2 + 3 * A) (hb : ∀ v ∈ inputFields q k m p E, v ≤ N)
    (hspace : scratchSpace A N ≤ B) :
    ∃ t, t ≤ 2 * stepBound A + (4 * q + 7) ∧ NExec (NFits B) successCore
      (st [] (E.reverse ++ [p,m,4,k+1,q]) [] []) t
      (.cont (st (outputFields q k m p E) [] [] [])) := by
  have hq : q ≤ N := hb q (by simp [inputFields])
  have hp : p ≤ N := hb p (by simp [inputFields])
  have hm : m ≤ N := hb m (by simp [inputFields])
  have hk : k+1 ≤ N := hb (k+1) (by simp [inputFields])
  have hn : 4 ≤ N := hb 4 (by simp [inputFields])
  have henv : ∀ v ∈ E, v ≤ N := fun v hv => hb v (by simp [inputFields,hv])
  have hb₀ : Bnd N (cellBound A * (N + 1)) (st [] (E.reverse ++ [p,m,4,k+1,q]) [] []) := by
    apply bnd_cells
    · intro i
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi with rfl | rfl | rfl | rfl <;> simp [st,cellBound] <;> omega
    · intro i v hv
      by_cases hi : i = 1
      · simp [st,hi] at hv
        rcases hv with hv | rfl | rfl | rfl | rfl | rfl
        · exact henv v hv
        all_goals omega
      · simp [st,hi] at hv
  have hr := (head_runs q k m p E).mono (show 3 * E.length + 40 ≤ stepBound A by unfold stepBound; omega)
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

def inputFields (r : Res) (k m p : Nat) (E : List Nat) : List Nat :=
  [3,0] ++ writeRes r ++ [k+1,4,m,p] ++ E

def outputFields (r : Res) (k m p : Nat) (E : List Nat) : List Nat :=
  match r with
  | none => [3,1,0,k]
  | some none => [3,1,1,k]
  | some (some q) => SequentialArgHeadReturn.outputFields q k m p E

def remaining (r : Res) (k m p : Nat) (E : List Nat) : List Nat :=
  match r with
  | none | some none => E.reverse ++ [p,m,4,k+1]
  | some (some q) => E.reverse ++ [p,m,4,k+1,q]

def failFinish (s : Bool) : List (NPrim 4) :=
  constants 0 3 ++ constants 0 1 ++ constants 0 (if s then 1 else 0) ++ [.dup 3 0 (by decide)]
def failProgram (s : Bool) : NProg 4 := prepend SequentialSeqReturn.failPre
  (.seq (nclr 1) (prepend (failFinish s) (.prim (.pop 3))))

theorem fail_runs (s : Bool) (k m p : Nat) (E : List Nat) :
    NRuns (failProgram s) (st [] (E.reverse ++ [p,m,4,k+1]) [] [])
      (st [3,1,if s then 1 else 0,k] [] [] []) (3 * E.length + 30) := by
  let S := st [] (E.reverse ++ [p,m,4,k+1]) [] []
  let A := st [] (E.reverse ++ [p,m,4]) [] [k]
  let R := st [] [] [] [k]
  have hp : applied SequentialSeqReturn.failPre S = A := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp [S,A,st,SequentialSeqReturn.failPre,applied,NPrim.apply,mapTop,Lists.set]
  have hc := nruns_clr 1 A
  have he : A.set 1 [] = R := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;> simp [A,R,st,Lists.set]
  rw [he] at hc
  have hf := prepend_runs (failFinish s) (.prim (.pop 3)) R _ 1 (nruns_prim _ _)
  have he' : (NPrim.pop 3).apply (applied (failFinish s) R) = st [3,1,if s then 1 else 0,k] [] [] [] := by
    cases s <;> funext i
    all_goals
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi with rfl | rfl | rfl | rfl <;>
        simp [R,st,failFinish,constants,applied,NPrim.apply,mapTop,Lists.set]
  rw [he'] at hf
  have hall := prepend_runs SequentialSeqReturn.failPre _ S _ _ (by rw [hp]; exact hc.seq hf)
  exact hall.mono (by cases s <;> simp [SequentialSeqReturn.failPre,failFinish,constants,A,st] <;> omega)

def branches : List (NProg 4) := [failProgram false,failProgram true,successCore]
def readStatus : NProg 4 := .seq (nmvAll 0 1 (by decide))
  (prepend [.pop 1] (.prim (.pop 1)))
def numeric : NProg 4 := .seq readStatus (caseTop 1 branches (.halt false))
def localProgram : LProg 11 := numeric.compile.rename reg

theorem readStatus_runs (r : Res) (k m p : Nat) (E : List Nat) :
    NRuns readStatus (st (inputFields r k m p E) [] [] [])
      (st [] (remaining r k m p E ++ [tag r]) [] []) (3 * E.length + 30) := by
  let S := st (inputFields r k m p E) [] [] []
  let R := (S.set 1 (S 1 ++ (S 0).reverse)).set 0 []
  have hr := nruns_mvAll 0 1 (by decide : (0 : Fin 4) ≠ 1) S
  have hp := prepend_runs [.pop 1] (.prim (.pop 1)) R _ 1 (nruns_prim _ _)
  have he : (NPrim.pop 1).apply (applied [.pop 1] R) =
      st [] (remaining r k m p E ++ [tag r]) [] [] := by
    cases r <;> (try (rename_i rr; cases rr))
    all_goals
      funext i
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi with rfl | rfl | rfl | rfl <;>
        simp [R,S,st,inputFields,remaining,tag,writeRes,applied,NPrim.apply,Lists.set,List.append_assoc]
  rw [he] at hp
  exact (hr.seq hp).mono (by cases r <;> (try (rename_i rr; cases rr)) <;>
    simp [S,st,inputFields,writeRes] <;> omega)


theorem numeric_exec (r : Res) (k m p : Nat) (E : List Nat) {A N B : Nat}
    (hE : E.length ≤ 2 + 3 * A) (hb : ∀ v ∈ inputFields r k m p E, v ≤ N)
    (hspace : scratchSpace A N ≤ B) :
    ∃ t, t ≤ 3 * stepBound A + 4 * N + 13 ∧ NExec (NFits B) numeric
      (st (inputFields r k m p E) [] [] []) t
      (.cont (st (outputFields r k m p E) [] [] [])) := by
  have hb₀ : Bnd N (cellBound A * (N+1)) (st (inputFields r k m p E) [] [] []) := by
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
  have hr := (readStatus_runs r k m p E).mono
    (show 3 * E.length + 30 ≤ stepBound A by unfold stepBound; omega)
  obtain ⟨t₁,ht₁,he₁⟩ := annotate hr hb₀ hspace
  let R := st [] (remaining r k m p E ++ [tag r]) [] []
  let F := st (outputFields r k m p E) [] [] []
  have hR : NFits B R := end_fits he₁
  have hpop : R.set 1 (remaining r k m p E) = st [] (remaining r k m p E) [] [] := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;> simp [R,st,Lists.set]
  have hb₁ : Bnd N (cellBound A * (N+1)) (st [] (remaining r k m p E) [] []) := by
    have hrem : ∀ v ∈ remaining r k m p E, v ≤ N := by
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
  have hbranch : ∃ t, t ≤ 2 * stepBound A + 4 * N + 7 ∧
      NExec (NFits B) (branches[tag r]'(by
        cases r <;> (try (rename_i rr; cases rr)) <;> simp [branches,tag]))
        (R.set 1 (remaining r k m p E)) t (.cont F) := by
    rw [hpop]
    cases r with
    | none =>
      have hf := (fail_runs false k m p E).mono
        (show 3 * E.length + 30 ≤ stepBound A by unfold stepBound; omega)
      obtain ⟨t,ht,he⟩ := annotate hf hb₁ hspace
      exact ⟨t,by omega,he⟩
    | some r => cases r with
      | none =>
        have hf := (fail_runs true k m p E).mono
          (show 3 * E.length + 30 ≤ stepBound A by unfold stepBound; omega)
        obtain ⟨t,ht,he⟩ := annotate hf hb₁ hspace
        exact ⟨t,by omega,he⟩
      | some q =>
        have hq : q ≤ N := hb q (by simp [inputFields,writeRes])
        have hbq : ∀ v ∈ SequentialArgHeadReturn.inputFields q k m p E, v ≤ N := by
          simpa [inputFields,SequentialArgHeadReturn.inputFields,writeRes] using hb
        obtain ⟨t,ht,he⟩ := core_exec q k m p E hE hbq hspace
        exact ⟨t,by omega,he⟩
  obtain ⟨t₂,ht₂,he₂⟩ := NShrinkingCompare.caseTop_exec 1 branches (.halt false) (tag r)
    (by cases r <;> (try (rename_i rr; cases rr)) <;> simp [branches,tag])
    R (remaining r k m p E) rfl hR F (2 * stepBound A + 4 * N + 7) hbranch
  have htag : tag r ≤ 2 := by cases r <;> (try (rename_i rr; cases rr)) <;> simp [tag]
  exact ⟨t₁+t₂,by omega,.seqC he₁ he₂⟩

theorem local_runs (r : Res) (k m p : Nat) (E : List Nat) {A N B width held : Nat} (tail : List Bool)
    (hE : E.length ≤ 2 + 3 * A) (hb : ∀ v ∈ inputFields r k m p E, v ≤ N)
    (hspace : scratchSpace A N ≤ B)
    (hR : LenOK B (SequentialFieldFetch.start width [] tail (SequentialFrontRead.locals (inputFields r k m p E)) held [])) :
    Complexity.Runs (LenOK B) localProgram
      (SequentialFieldFetch.start width [] tail (SequentialFrontRead.locals (inputFields r k m p E)) held [])
      (SequentialFieldFetch.start width [] tail (SequentialFrontRead.locals (outputFields r k m p E)) held [])
      ((3 * stepBound A + 4 * N + 13) * ncost B) :=
  SequentialNumericBlock.annotated_local_runs numeric _ _ tail (numeric_exec r k m p E hE hb hspace) hR


def localNext (r : Res) (m p : Nat) (E : CaptureEnv) (es : List MExp) : Config :=
  match r with
  | none => ⟨.value (.args none), []⟩
  | some none => ⟨.value (.args (some none)), []⟩
  | some (some q) => ⟨.args m E es q, [.argCons (p,min q p)]⟩

theorem original_step (g : MGrammar) (x : List Char) (r : Res) (m p : Nat) (E : CaptureEnv)
    (es : List MExp) (K : List SequentialStack.Frame) :
    step g x ⟨.value (.expr r), .argHead m E es p :: K⟩ =
      some (SequentialFront.attach K (localNext r m p E es)) := by
  cases r <;> (try (rename_i rr; cases rr)) <;> rfl

theorem input_prefix (ns : List CompileNode) (r : Res) (m p : Nat) (E : CaptureEnv) (es : List MExp)
    (K : List SequentialStack.Frame) :
    SequentialFront.prefixCode ns K ⟨.value (.expr r), [.argHead m E es p]⟩ =
      inputFields r K.length m p (writeEnv E ++ writeExprs ns es) := by
  cases r <;> (try (rename_i rr; cases rr)) <;>
    simp [SequentialFront.prefixCode, SequentialFront.suffixCode, inputFields, writeTask, writeValue,
      writeRes, writeFrame, Nat.add_comm]

theorem output_prefix (ns : List CompileNode) (r : Res) (m p : Nat) (E : CaptureEnv) (es : List MExp)
    (K : List SequentialStack.Frame) :
    SequentialFront.prefixCode ns K (localNext r m p E es) =
      outputFields r K.length m p (writeEnv E ++ writeExprs ns es) := by
  cases r <;> (try (rename_i rr; cases rr)) <;>
    simp [SequentialFront.prefixCode, SequentialFront.suffixCode, outputFields, localNext,
      SequentialArgHeadReturn.outputFields, writeTask, writeValue, writeArgsRes, writeFrame,
      Nat.add_comm,List.append_assoc]

end Shallot.MacroPeg.CBV.SequentialArgHeadDispatch
