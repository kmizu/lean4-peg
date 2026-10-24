import MacroPeg.CBV.SequentialNumericBlock

/-! Ordered-choice return: restart the right branch at the saved position
only after failure; keep a successful or undefined result unchanged. -/

namespace Shallot.MacroPeg.CBV.SequentialAltReturn

open Complexity SequentialStack SequentialStackCodec CBVtoCBN
open SequentialNotReturn (prepend applied prepend_runs constants tag)
open SequentialSeqReturn (st ops result ops_runs failPre failFinish resumeFinish reg)

def inputFields (r : Res) (k m p b : Nat) (E : List Nat) : List Nat :=
  match r with
  | none => [3, 0, 0, k + 1, 1, m, p, b] ++ E
  | some none => [3, 0, 1, k + 1, 1, m, p, b] ++ E
  | some (some q) => [3, 0, 2, q, k + 1, 1, m, p, b] ++ E

def outputFields (r : Res) (k m p b : Nat) (E : List Nat) : List Nat :=
  match r with
  | none => [3, 0, 0, k]
  | some none => [0, m, p, b] ++ E ++ [k]
  | some (some q) => [3, 0, 2, q, k]

def remaining (r : Res) (k m p b : Nat) (E : List Nat) : List Nat :=
  match r with
  | none | some none => E.reverse ++ [b, p, m, 1, k + 1]
  | some (some q) => E.reverse ++ [b, p, m, 1, k + 1, q]

def undefinedProgram : NProg 4 := prepend failPre (.seq (nclr 1) (ops (failFinish false)))

def resumePre : List (NPrim 4) :=
  [.dup 1 3 (by decide), .pop 1, .dec 3, .pop 1, .pushZ 0,
    .dup 1 0 (by decide), .pop 1, .dup 1 0 (by decide), .pop 1,
    .dup 1 0 (by decide), .pop 1]
def resumeProgram : NProg 4 := prepend resumePre (.seq (nmvAll 1 0 (by decide)) (ops resumeFinish))

def successPre : List (NPrim 4) :=
  [.dup 1 2 (by decide), .pop 1, .dup 1 3 (by decide), .pop 1, .dec 3]
def successFinish : List (NPrim 4) := constants 0 3 ++ constants 0 0 ++ constants 0 2 ++
  [.dup 2 0 (by decide), .dup 3 0 (by decide), .pop 2, .pop 3]
def successProgram : NProg 4 := prepend successPre (.seq (nclr 1) (ops successFinish))

theorem undefined_runs (k m p b : Nat) (E : List Nat) :
    NRuns undefinedProgram (st [] (E.reverse ++ [b, p, m, 1, k + 1]) [] [])
      (st [3, 0, 0, k] [] [] []) (3 * E.length + 40) := by
  let S := st [] (E.reverse ++ [b, p, m, 1, k + 1]) [] []
  let A := st [] (E.reverse ++ [b, p, m, 1]) [] [k]
  let B := st [] [] [] [k]
  have hpre : applied failPre S = A := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp [applied, failPre, S, A, st, NPrim.apply, mapTop, Lists.set]
  have hc := nruns_clr 1 A
  have hclear : A.set 1 [] = B := by
    funext i
    by_cases hi : i = 1 <;> simp_all [A, B, st, Lists.set]
  rw [hclear] at hc
  have hf := ops_runs (failFinish false) B
  have hfinish : result (failFinish false) B = st [3, 0, 0, k] [] [] [] := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp [result, applied, failFinish, constants, B, st, NPrim.apply, mapTop, Lists.set]
  rw [hfinish] at hf
  have hall := prepend_runs failPre _ S _ _ (by rw [hpre]; exact hc.seq hf)
  exact hall.mono (by simp [failPre, failFinish, constants, A, st]; omega)

theorem resume_runs (k m p b : Nat) (E : List Nat) :
    NRuns resumeProgram (st [] (E.reverse ++ [b, p, m, 1, k + 1]) [] [])
      (st ([0, m, p, b] ++ E ++ [k]) [] [] []) (3 * E.length + 40) := by
  let S := st [] (E.reverse ++ [b, p, m, 1, k + 1]) [] []
  let A := st [0, m, p, b] E.reverse [] [k]
  let B := st ([0, m, p, b] ++ E) [] [] [k]
  have hpre : applied resumePre S = A := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp [applied, resumePre, S, A, st, NPrim.apply, mapTop, Lists.set]
  have hm := nruns_mvAll 1 0 (by decide : (1 : Fin 4) ≠ 0) A
  have hmove : (A.set 0 (A 0 ++ (A 1).reverse)).set 1 [] = B := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;> simp [A, B, st, Lists.set]
  rw [hmove] at hm
  have hf := ops_runs resumeFinish B
  have hfinish : result resumeFinish B = st ([0, m, p, b] ++ E ++ [k]) [] [] [] := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp [result, applied, resumeFinish, B, st, NPrim.apply, mapTop, Lists.set]
  rw [hfinish] at hf
  have hall := prepend_runs resumePre _ S _ _ (by rw [hpre]; exact hm.seq hf)
  exact hall.mono (by simp [resumePre, resumeFinish, A, st]; omega)

theorem success_runs (q k m p b : Nat) (E : List Nat) :
    NRuns successProgram (st [] (E.reverse ++ [b, p, m, 1, k + 1, q]) [] [])
      (st [3, 0, 2, q, k] [] [] []) (3 * E.length + 40) := by
  let S := st [] (E.reverse ++ [b, p, m, 1, k + 1, q]) [] []
  let A := st [] (E.reverse ++ [b, p, m, 1]) [q] [k]
  let B := st [] [] [q] [k]
  have hpre : applied successPre S = A := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp [applied, successPre, S, A, st, NPrim.apply, mapTop, Lists.set]
  have hc := nruns_clr 1 A
  have hclear : A.set 1 [] = B := by
    funext i
    by_cases hi : i = 1 <;> simp_all [A, B, st, Lists.set]
  rw [hclear] at hc
  have hf := ops_runs successFinish B
  have hfinish : result successFinish B = st [3, 0, 2, q, k] [] [] [] := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp [result, applied, successFinish, constants, B, st, NPrim.apply, mapTop, Lists.set]
  rw [hfinish] at hf
  have hall := prepend_runs successPre _ S _ _ (by rw [hpre]; exact hc.seq hf)
  exact hall.mono (by simp [successPre, successFinish, constants, A, st]; omega)

def branches : List (NProg 4) := [undefinedProgram, resumeProgram, successProgram]
def numeric : NProg 4 := .seq (nmvAll 0 1 (by decide))
  (prepend [.pop 1, .pop 1] (caseTop 1 branches (.halt false)))

theorem numeric_runs (r : Res) (k m p b : Nat) (E : List Nat) :
    NRuns numeric (st (inputFields r k m p b E) [] [] [])
      (st (outputFields r k m p b E) [] [] []) (6 * E.length + 90) := by
  let S := st (inputFields r k m p b E) [] [] []
  let R := (S.set 1 (S 1 ++ (S 0).reverse)).set 0 []
  have hrev := nruns_mvAll 0 1 (by decide : (0 : Fin 4) ≠ 1) S
  let H := applied [.pop 1, .pop 1] R
  have hH : H = st [] (remaining r k m p b E ++ [tag r]) [] [] := by
    cases r <;> (try (rename_i rr; cases rr))
    all_goals
      funext i
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi with rfl | rfl | rfl | rfl <;>
        simp [H, R, S, applied, st, inputFields, remaining, tag, NPrim.apply, Lists.set, List.append_assoc]
  have hpop : H.set 1 (remaining r k m p b E) = st [] (remaining r k m p b E) [] [] := by
    rw [hH]
    funext i
    by_cases hi : i = 1 <;> simp_all [st, Lists.set]
  have hh := caseTop_runs 1 branches (.halt false) (tag r)
    (by cases r <;> (try (rename_i rr; cases rr)) <;> simp [tag, branches])
    H (remaining r k m p b E) (by rw [hH]; simp [st]) (st (outputFields r k m p b E) [] [] [])
    (3 * E.length + 40) (by
      rw [hpop]
      cases r with
      | none => exact undefined_runs k m p b E
      | some r => cases r with
        | none => exact resume_runs k m p b E
        | some q => exact success_runs q k m p b E)
  have hall := hrev.seq (prepend_runs [.pop 1, .pop 1] _ R _ _ hh)
  have hlen : (S 0).length ≤ E.length + 9 := by
    cases r <;> (try (rename_i rr; cases rr)) <;> simp [S, st, inputFields] <;> omega
  have ht : tag r ≤ 2 := by cases r <;> (try (rename_i rr; cases rr)) <;> simp [tag]
  exact hall.mono (by simp; omega)

def stepBound (A : Nat) : Nat := 12 * A + 110
def cellBound (A : Nat) : Nat := 10 + 2 * A
def scratchSpace (A N : Nat) : Nat := SequentialNumericBlock.scratchSpace (cellBound A) (stepBound A) N
def localProgram : LProg 11 := numeric.compile.rename reg

theorem scratchSpace_linear (A N : Nat) :
    scratchSpace A N = (cellBound A + stepBound A) * N +
      (cellBound A + stepBound A * (stepBound A + 1) + 2) :=
  SequentialNumericBlock.scratchSpace_linear _ _ _

theorem local_runs (r : Res) (k m p b : Nat) (E : List Nat) {A N B width held : Nat} (tail : List Bool)
    (hE : E.length ≤ 1 + 2 * A) (hb : ∀ v ∈ inputFields r k m p b E, v ≤ N)
    (hspace : scratchSpace A N ≤ B)
    (hR : LenOK B (SequentialFieldFetch.start width [] tail (SequentialFrontRead.locals (inputFields r k m p b E)) held [])) :
    Complexity.Runs (LenOK B) localProgram
      (SequentialFieldFetch.start width [] tail (SequentialFrontRead.locals (inputFields r k m p b E)) held [])
      (SequentialFieldFetch.start width [] tail (SequentialFrontRead.locals (outputFields r k m p b E)) held [])
      (stepBound A * ncost B) := by
  have hlen : (inputFields r k m p b E).length ≤ cellBound A := by
    cases r <;> (try (rename_i rr; cases rr)) <;> simp [inputFields, cellBound] <;> omega
  have hr := (numeric_runs r k m p b E).mono (show 6 * E.length + 90 ≤ stepBound A by unfold stepBound; omega)
  exact SequentialNumericBlock.local_runs numeric _ _ tail hr hlen hb hspace hR

def nextTask (r : Res) (m : Nat) (E : CaptureEnv) (b : MExp) (p : Nat) : Task :=
  match r with
  | some none => .expr m E b p
  | r => .value (.expr r)

theorem original_step (g : MGrammar) (x : List Char) (r : Res) (m p : Nat) (E : CaptureEnv)
    (b : MExp) (K : List SequentialStack.Frame) :
    step g x ⟨.value (.expr r), .alt m E b p :: K⟩ = some ⟨nextTask r m E b p, K⟩ := by
  cases r <;> (try (rename_i rr; cases rr)) <;> rfl

theorem input_prefix (ns : List CompileNode) (r : Res) (m p : Nat) (E : CaptureEnv) (b : MExp)
    (K : List SequentialStack.Frame) :
    SequentialFront.prefixCode ns K ⟨.value (.expr r), [.alt m E b p]⟩ =
      inputFields r K.length m p (exprId ns b) (writeEnv E) := by
  cases r <;> (try (rename_i rr; cases rr)) <;>
    simp [SequentialFront.prefixCode, SequentialFront.suffixCode, inputFields, writeTask, writeValue,
      writeRes, writeFrame, writeExpr, Nat.add_comm]

theorem output_prefix (ns : List CompileNode) (r : Res) (m p : Nat) (E : CaptureEnv) (b : MExp)
    (K : List SequentialStack.Frame) :
    SequentialFront.prefixCode ns K ⟨nextTask r m E b p, []⟩ =
      outputFields r K.length m p (exprId ns b) (writeEnv E) := by
  cases r <;> (try (rename_i rr; cases rr)) <;>
    simp [SequentialFront.prefixCode, SequentialFront.suffixCode, outputFields, nextTask, writeTask,
      writeValue, writeRes, writeExpr, Nat.add_comm]

end Shallot.MacroPeg.CBV.SequentialAltReturn
