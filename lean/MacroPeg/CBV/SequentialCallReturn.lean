import MacroPeg.CBV.SequentialNumericBlock

/-! Return from sequential argument evaluation into a grammar query. The
captured environment is copied in its original order on successful arguments. -/

namespace Shallot.MacroPeg.CBV.SequentialCallReturn

open Complexity SequentialStack SequentialStackCodec CBVtoCBN
open SequentialNotReturn (prepend applied prepend_runs constants)
open SequentialSeqReturn (st ops result ops_runs failFinish resumeFinish reg stepBound cellBound scratchSpace)

def inputFields (r : ArgsResult) (k m i : Nat) : List Nat := [3, 1] ++ writeArgsRes r ++ [k + 1, 6, m, i]
def outputFields (r : ArgsResult) (k m i : Nat) : List Nat :=
  match r with
  | none => [3, 0, 0, k]
  | some none => [3, 0, 1, k]
  | some (some (W, q)) => [2, m, i, q] ++ writeEnv W ++ [k]

def taskFields (r : ArgsResult) : List Nat := [3, 1] ++ writeArgsRes r
def envFields : ArgsResult → List Nat
  | some (some (W, _)) => writeEnv W
  | _ => []
def remaining : ArgsResult → List Nat
  | some (some (W, q)) => (writeEnv W).reverse ++ [q]
  | _ => []
def tag : ArgsResult → Nat
  | none => 0
  | some none => 1
  | some (some _) => 2

/-- Remove the call footer, retaining the clock, rule and decremented stack
length separately from the argument-result fields. -/
def footer : List (NPrim 4) :=
  [.dup 0 2 (by decide), .pop 0, .dup 0 2 (by decide), .pop 0, .pop 0,
    .dup 0 3 (by decide), .pop 0, .dec 3]

def failureProgram (s : Bool) : NProg 4 := .seq (nclr 2) (ops (failFinish s))
def successPre : List (NPrim 4) := constants 0 2 ++
  [.dup 2 0 (by decide), .pop 2, .dup 2 0 (by decide), .pop 2, .dup 1 0 (by decide), .pop 1]
def successProgram : NProg 4 := prepend successPre (.seq (nmvAll 1 0 (by decide)) (ops resumeFinish))

theorem failure_runs (s : Bool) (k m i : Nat) :
    NRuns (failureProgram s) (st [] [] [i, m] [k]) (st [3, 0, if s then 1 else 0, k] [] [] []) 30 := by
  let S := st [] [] [i, m] [k]
  let A := st [] [] [] [k]
  have hc := nruns_clr 2 S
  have hclear : S.set 2 [] = A := by
    funext j
    have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hj with rfl | rfl | rfl | rfl <;> simp [S, A, st, Lists.set]
  rw [hclear] at hc
  have hf := ops_runs (failFinish s) A
  have hfinish : result (failFinish s) A = st [3, 0, if s then 1 else 0, k] [] [] [] := by
    cases s <;> funext j
    all_goals
      have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases hj with rfl | rfl | rfl | rfl <;>
        simp [result, applied, failFinish, constants, A, st, NPrim.apply, mapTop, Lists.set]
  rw [hfinish] at hf
  exact (hc.seq hf).mono (by cases s <;> simp [S, st, failFinish, constants])

theorem success_runs (q k m i : Nat) (E : List Nat) :
    NRuns successProgram (st [] (E.reverse ++ [q]) [i, m] [k])
      (st ([2, m, i, q] ++ E ++ [k]) [] [] []) (3 * E.length + 30) := by
  let S := st [] (E.reverse ++ [q]) [i, m] [k]
  let A := st [2, m, i, q] E.reverse [] [k]
  let B := st ([2, m, i, q] ++ E) [] [] [k]
  have hpre : applied successPre S = A := by
    funext j
    have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hj with rfl | rfl | rfl | rfl <;>
      simp [applied, successPre, constants, S, A, st, NPrim.apply, mapTop, Lists.set]
  have hm := nruns_mvAll 1 0 (by decide : (1 : Fin 4) ≠ 0) A
  have hmove : (A.set 0 (A 0 ++ (A 1).reverse)).set 1 [] = B := by
    funext j
    have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hj with rfl | rfl | rfl | rfl <;> simp [A, B, st, Lists.set]
  rw [hmove] at hm
  have hf := ops_runs resumeFinish B
  have hfinish : result resumeFinish B = st ([2, m, i, q] ++ E ++ [k]) [] [] [] := by
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

theorem numeric_runs (r : ArgsResult) (k m i : Nat) :
    NRuns numeric (st (inputFields r k m i) [] [] [])
      (st (outputFields r k m i) [] [] []) (6 * (envFields r).length + 90) := by
  let S := st (inputFields r k m i) [] [] []
  let F := st (taskFields r) [] [i, m] [k]
  have hfmt : inputFields r k m i = taskFields r ++ [k + 1, 6, m, i] := rfl
  have hfooter : applied footer S = F := by
    funext j
    have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hj with rfl | rfl | rfl | rfl <;>
      simp [applied, footer, S, F, hfmt, st, NPrim.apply, mapTop, Lists.set]
  let R := (F.set 1 (F 1 ++ (F 0).reverse)).set 0 []
  have hrev := nruns_mvAll 0 1 (by decide : (0 : Fin 4) ≠ 1) F
  let H := applied [.pop 1, .pop 1] R
  have hH : H = st [] (remaining r ++ [tag r]) [i, m] [k] := by
    cases r <;> (try (rename_i rr; cases rr)) <;> (try (rename_i pair; cases pair))
    all_goals
      funext j
      have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases hj with rfl | rfl | rfl | rfl <;>
        simp [H, R, F, applied, taskFields, writeArgsRes, remaining, tag, st, NPrim.apply, Lists.set, List.append_assoc]
  have hpop : H.set 1 (remaining r) = st [] (remaining r) [i, m] [k] := by
    rw [hH]
    funext j
    by_cases hj : j = 1 <;> simp_all [st, Lists.set]
  have hh := caseTop_runs 1 branches (.halt false) (tag r)
    (by cases r <;> (try (rename_i rr; cases rr)) <;> simp [tag, branches])
    H (remaining r) (by rw [hH]; simp [st]) (st (outputFields r k m i) [] [] [])
    (3 * (envFields r).length + 30) (by
      rw [hpop]
      cases r with
      | none => exact failure_runs false k m i
      | some r => cases r with
        | none => exact failure_runs true k m i
        | some Wq => obtain ⟨W, q⟩ := Wq; exact success_runs q k m i (writeEnv W))
  have hbody := hrev.seq (prepend_runs [.pop 1, .pop 1] _ R _ _ hh)
  have hall := prepend_runs footer _ S _ _ (by rw [hfooter]; exact hbody)
  have hlen : (F 0).length ≤ (envFields r).length + 4 := by
    cases r <;> (try (rename_i rr; cases rr)) <;> (try (rename_i pair; cases pair)) <;>
      simp [F, st, taskFields, writeArgsRes, envFields] <;> omega
  have ht : tag r ≤ 2 := by cases r <;> (try (rename_i rr; cases rr)) <;> simp [tag]
  exact hall.mono (by simp [footer]; omega)

def localProgram : LProg 11 := numeric.compile.rename reg

theorem local_runs (r : ArgsResult) (k m i : Nat) {A N B width held : Nat} (tail : List Bool)
    (hE : (envFields r).length ≤ 1 + 2 * A) (hb : ∀ v ∈ inputFields r k m i, v ≤ N)
    (hspace : scratchSpace A N ≤ B)
    (hR : LenOK B (SequentialFieldFetch.start width [] tail (SequentialFrontRead.locals (inputFields r k m i)) held [])) :
    Complexity.Runs (LenOK B) localProgram
      (SequentialFieldFetch.start width [] tail (SequentialFrontRead.locals (inputFields r k m i)) held [])
      (SequentialFieldFetch.start width [] tail (SequentialFrontRead.locals (outputFields r k m i)) held [])
      (stepBound A * ncost B) := by
  have hlen : (inputFields r k m i).length ≤ cellBound A := by
    cases r <;> (try (rename_i rr; cases rr)) <;> (try (rename_i pair; cases pair)) <;>
      simp [inputFields, writeArgsRes, envFields, cellBound] at hE ⊢ <;> omega
  have hr := (numeric_runs r k m i).mono (show 6 * (envFields r).length + 90 ≤ stepBound A by unfold stepBound; omega)
  exact SequentialNumericBlock.local_runs numeric _ _ tail hr hlen hb hspace hR

def nextTask (r : ArgsResult) (m i : Nat) : Task :=
  match r with
  | none => .value (.expr none)
  | some none => .value (.expr (some none))
  | some (some (W, q)) => .query m i W q

theorem original_step (g : MGrammar) (x : List Char) (r : ArgsResult) (m i : Nat)
    (K : List SequentialStack.Frame) :
    step g x ⟨.value (.args r), .call m i :: K⟩ = some ⟨nextTask r m i, K⟩ := by
  cases r <;> (try (rename_i rr; cases rr)) <;> (try (rename_i pair; cases pair)) <;> rfl

theorem input_prefix (ns : List CompileNode) (r : ArgsResult) (m i : Nat) (K : List SequentialStack.Frame) :
    SequentialFront.prefixCode ns K ⟨.value (.args r), [.call m i]⟩ = inputFields r K.length m i := by
  simp [SequentialFront.prefixCode, SequentialFront.suffixCode, writeTask, writeValue, writeFrame, inputFields,
    Nat.add_comm]

theorem output_prefix (ns : List CompileNode) (r : ArgsResult) (m i : Nat) (K : List SequentialStack.Frame) :
    SequentialFront.prefixCode ns K ⟨nextTask r m i, []⟩ = outputFields r K.length m i := by
  cases r <;> (try (rename_i rr; cases rr)) <;> (try (rename_i pair; cases pair)) <;>
    simp [SequentialFront.prefixCode, SequentialFront.suffixCode, outputFields, nextTask,
      writeTask, writeValue, writeRes, Nat.add_comm]

end Shallot.MacroPeg.CBV.SequentialCallReturn
