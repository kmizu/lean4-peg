import MacroPeg.CBV.SequentialCallReturn

/-! Prepend one captured interval to the returned argument environment,
preserving the argument order and the result position. -/

namespace Shallot.MacroPeg.CBV.SequentialArgConsReturn

open Complexity SequentialStack SequentialStackCodec CBVtoCBN
open SequentialNotReturn (prepend applied prepend_runs constants)
open SequentialSeqReturn (st ops result ops_runs resumeFinish reg stepBound cellBound scratchSpace)
open SequentialCallReturn (taskFields envFields remaining tag footer)

def inputFields (r : ArgsResult) (k a b : Nat) : List Nat := [3, 1] ++ writeArgsRes r ++ [k + 1, 5, a, b]
def prependResult (r : ArgsResult) (a b : Nat) : ArgsResult :=
  match r with
  | some (some (W, q)) => some (some ((a, b) :: W, q))
  | r => r
def outputFields (r : ArgsResult) (k a b : Nat) : List Nat :=
  [3, 1] ++ writeArgsRes (prependResult r a b) ++ [k]

def failureFinish (s : Bool) : List (NPrim 4) := constants 0 3 ++ constants 0 1 ++
  constants 0 (if s then 1 else 0) ++ [.dup 3 0 (by decide), .pop 3]
def failureProgram (s : Bool) : NProg 4 := .seq (nclr 2) (ops (failureFinish s))

def successPre : List (NPrim 4) := constants 0 3 ++ constants 0 1 ++ constants 0 2 ++
  [.dup 1 0 (by decide), .pop 1, .dup 1 0 (by decide), .pop 1, .inc 0,
    .dup 2 0 (by decide), .pop 2, .dup 2 0 (by decide), .pop 2]
def successProgram : NProg 4 := prepend successPre (.seq (nmvAll 1 0 (by decide)) (ops resumeFinish))

theorem failure_runs (s : Bool) (k a b : Nat) :
    NRuns (failureProgram s) (st [] [] [b, a] [k]) (st [3, 1, if s then 1 else 0, k] [] [] []) 30 := by
  let S := st [] [] [b, a] [k]
  let A := st [] [] [] [k]
  have hc := nruns_clr 2 S
  have hclear : S.set 2 [] = A := by
    funext j
    have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hj with rfl | rfl | rfl | rfl <;> simp [S, A, st, Lists.set]
  rw [hclear] at hc
  have hf := ops_runs (failureFinish s) A
  have hfinish : result (failureFinish s) A = st [3, 1, if s then 1 else 0, k] [] [] [] := by
    cases s <;> funext j
    all_goals
      have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases hj with rfl | rfl | rfl | rfl <;>
        simp [result, applied, failureFinish, constants, A, st, NPrim.apply, mapTop, Lists.set]
  rw [hfinish] at hf
  exact (hc.seq hf).mono (by cases s <;> simp [S, st, failureFinish, constants])

theorem success_runs (q k a b n : Nat) (E : List Nat) :
    NRuns successProgram (st [] ((n :: E).reverse ++ [q]) [b, a] [k])
      (st ([3, 1, 2, q, n + 1, a, b] ++ E ++ [k]) [] [] []) (3 * (n :: E).length + 40) := by
  let S := st [] ((n :: E).reverse ++ [q]) [b, a] [k]
  let A := st [3, 1, 2, q, n + 1, a, b] E.reverse [] [k]
  let B := st ([3, 1, 2, q, n + 1, a, b] ++ E) [] [] [k]
  have hpre : applied successPre S = A := by
    funext j
    have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hj with rfl | rfl | rfl | rfl <;>
      simp [applied, successPre, constants, S, A, st, NPrim.apply, mapTop, Lists.set, List.append_assoc]
  have hm := nruns_mvAll 1 0 (by decide : (1 : Fin 4) ≠ 0) A
  have hmove : (A.set 0 (A 0 ++ (A 1).reverse)).set 1 [] = B := by
    funext j
    have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hj with rfl | rfl | rfl | rfl <;> simp [A, B, st, Lists.set]
  rw [hmove] at hm
  have hf := ops_runs resumeFinish B
  have hfinish : result resumeFinish B = st ([3, 1, 2, q, n + 1, a, b] ++ E ++ [k]) [] [] [] := by
    funext j
    have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hj with rfl | rfl | rfl | rfl <;>
      simp [result, applied, resumeFinish, B, st, NPrim.apply, mapTop, Lists.set]
  rw [hfinish] at hf
  have hall := prepend_runs successPre _ S _ _ (by rw [hpre]; exact hm.seq hf)
  exact hall.mono (by simp [successPre, constants, resumeFinish, A, st]; omega)

def branches : List (NProg 4) := [failureProgram false, failureProgram true, successProgram]
def numeric : NProg 4 := prepend footer (.seq (nmvAll 0 1 (by decide))
  (prepend [.pop 1, .pop 1] (caseTop 1 branches (.halt false))))

theorem numeric_runs (r : ArgsResult) (k a b : Nat) :
    NRuns numeric (st (inputFields r k a b) [] [] [])
      (st (outputFields r k a b) [] [] []) (6 * (envFields r).length + 90) := by
  let S := st (inputFields r k a b) [] [] []
  let F := st (taskFields r) [] [b, a] [k]
  have hfmt : inputFields r k a b = taskFields r ++ [k + 1, 5, a, b] := rfl
  have hfooter : applied footer S = F := by
    funext j
    have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hj with rfl | rfl | rfl | rfl <;>
      simp [applied, footer, S, F, hfmt, st, NPrim.apply, mapTop, Lists.set]
  let R := (F.set 1 (F 1 ++ (F 0).reverse)).set 0 []
  have hrev := nruns_mvAll 0 1 (by decide : (0 : Fin 4) ≠ 1) F
  let H := applied [.pop 1, .pop 1] R
  have hH : H = st [] (remaining r ++ [tag r]) [b, a] [k] := by
    cases r <;> (try (rename_i rr; cases rr)) <;> (try (rename_i pair; cases pair))
    all_goals
      funext j
      have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases hj with rfl | rfl | rfl | rfl <;>
        simp [H, R, F, applied, taskFields, writeArgsRes, remaining, tag, st, NPrim.apply, Lists.set, List.append_assoc]
  have hpop : H.set 1 (remaining r) = st [] (remaining r) [b, a] [k] := by
    rw [hH]
    funext j
    by_cases hj : j = 1 <;> simp_all [st, Lists.set]
  have hh := caseTop_runs 1 branches (.halt false) (tag r)
    (by cases r <;> (try (rename_i rr; cases rr)) <;> simp [tag, branches])
    H (remaining r) (by rw [hH]; simp [st]) (st (outputFields r k a b) [] [] [])
    (3 * (envFields r).length + 40) (by
      rw [hpop]
      cases r with
      | none => exact (failure_runs false k a b).mono (by simp [envFields])
      | some r => cases r with
        | none => exact (failure_runs true k a b).mono (by simp [envFields])
        | some Wq =>
          obtain ⟨W, q⟩ := Wq
          simpa [writeEnv, writeList, writePair, writeArgsRes, branches, tag, outputFields, prependResult, remaining, envFields, List.append_assoc]
            using success_runs q k a b W.length (W.flatMap writePair))
  have hbody := hrev.seq (prepend_runs [.pop 1, .pop 1] _ R _ _ hh)
  have hall := prepend_runs footer _ S _ _ (by rw [hfooter]; exact hbody)
  have hlen : (F 0).length ≤ (envFields r).length + 4 := by
    cases r <;> (try (rename_i rr; cases rr)) <;> (try (rename_i pair; cases pair)) <;>
      simp [F, st, taskFields, writeArgsRes, envFields] <;> omega
  have ht : tag r ≤ 2 := by cases r <;> (try (rename_i rr; cases rr)) <;> simp [tag]
  exact hall.mono (by simp [footer]; omega)

def localProgram : LProg 11 := numeric.compile.rename reg

theorem local_runs (r : ArgsResult) (k a b : Nat) {A N B width held : Nat} (tail : List Bool)
    (hE : (envFields r).length ≤ 1 + 2 * A) (hb : ∀ v ∈ inputFields r k a b, v ≤ N)
    (hspace : scratchSpace A N ≤ B)
    (hR : LenOK B (SequentialFieldFetch.start width [] tail (SequentialFrontRead.locals (inputFields r k a b)) held [])) :
    Complexity.Runs (LenOK B) localProgram
      (SequentialFieldFetch.start width [] tail (SequentialFrontRead.locals (inputFields r k a b)) held [])
      (SequentialFieldFetch.start width [] tail (SequentialFrontRead.locals (outputFields r k a b)) held [])
      (stepBound A * ncost B) := by
  have hlen : (inputFields r k a b).length ≤ cellBound A := by
    cases r <;> (try (rename_i rr; cases rr)) <;> (try (rename_i pair; cases pair)) <;>
      simp [inputFields, writeArgsRes, envFields, cellBound] at hE ⊢ <;> omega
  have hr := (numeric_runs r k a b).mono (show 6 * (envFields r).length + 90 ≤ stepBound A by unfold stepBound; omega)
  exact SequentialNumericBlock.local_runs numeric _ _ tail hr hlen hb hspace hR

theorem original_step (g : MGrammar) (x : List Char) (r : ArgsResult) (a b : Nat)
    (K : List SequentialStack.Frame) :
    step g x ⟨.value (.args r), .argCons (a, b) :: K⟩ = some ⟨.value (.args (prependResult r a b)), K⟩ := by
  cases r <;> (try (rename_i rr; cases rr)) <;> (try (rename_i pair; cases pair)) <;> rfl

theorem input_prefix (ns : List CompileNode) (r : ArgsResult) (a b : Nat) (K : List SequentialStack.Frame) :
    SequentialFront.prefixCode ns K ⟨.value (.args r), [.argCons (a, b)]⟩ = inputFields r K.length a b := by
  simp [SequentialFront.prefixCode, SequentialFront.suffixCode, writeTask, writeValue, writeFrame, inputFields,
    Nat.add_comm]

theorem output_prefix (ns : List CompileNode) (r : ArgsResult) (a b : Nat) (K : List SequentialStack.Frame) :
    SequentialFront.prefixCode ns K ⟨.value (.args (prependResult r a b)), []⟩ = outputFields r K.length a b := by
  simp [SequentialFront.prefixCode, SequentialFront.suffixCode, outputFields, writeTask, writeValue, Nat.add_comm]

end Shallot.MacroPeg.CBV.SequentialArgConsReturn
