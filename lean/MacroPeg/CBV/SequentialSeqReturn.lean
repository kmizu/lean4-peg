import MacroPeg.CBV.SequentialNotReturn

/-! Return through a sequence frame, including preservation of all captured
intervals on success. The local program is independent of the environment. -/

namespace Shallot.MacroPeg.CBV.SequentialSeqReturn

open Complexity SequentialStack SequentialStackCodec CBVtoCBN
open SequentialNotReturn (prepend applied prepend_runs constants tag)

def st (D R Q K : List Nat) : Lists 4 := fun i =>
  if i = 0 then D else if i = 1 then R else if i = 2 then Q else K

def inputFields (r : Res) (k m b : Nat) (E : List Nat) : List Nat :=
  match r with
  | none => [3, 0, 0, k + 1, 0, m, b] ++ E
  | some none => [3, 0, 1, k + 1, 0, m, b] ++ E
  | some (some q) => [3, 0, 2, q, k + 1, 0, m, b] ++ E

def outputFields (r : Res) (k m b : Nat) (E : List Nat) : List Nat :=
  match r with
  | none => [3, 0, 0, k]
  | some none => [3, 0, 1, k]
  | some (some q) => [0, m, q, b] ++ E ++ [k]

def remaining (r : Res) (k m b : Nat) (E : List Nat) : List Nat :=
  match r with
  | none | some none => E.reverse ++ [b, m, 0, k + 1]
  | some (some q) => E.reverse ++ [b, m, 0, k + 1, q]

def ops (xs : List (NPrim 4)) : NProg 4 := prepend xs (.prim (.dec 3))
def result (xs : List (NPrim 4)) (S : Lists 4) : Lists 4 := (NPrim.dec 3).apply (applied xs S)

theorem ops_runs (xs : List (NPrim 4)) (S : Lists 4) : NRuns (ops xs) S (result xs S) (xs.length + 1) :=
  prepend_runs xs _ S _ 1 (nruns_prim _ _)

def failPre : List (NPrim 4) := [.dup 1 3 (by decide), .pop 1, .dec 3]
def failFinish (s : Bool) : List (NPrim 4) := constants 0 3 ++ constants 0 0 ++
  constants 0 (if s then 1 else 0) ++ [.dup 3 0 (by decide), .pop 3]
def failProgram (s : Bool) : NProg 4 := prepend failPre (.seq (nclr 1) (ops (failFinish s)))

def resumePre : List (NPrim 4) :=
  [.dup 1 2 (by decide), .pop 1, .dup 1 3 (by decide), .pop 1, .dec 3, .pop 1,
    .pushZ 0, .dup 1 0 (by decide), .pop 1, .dup 2 0 (by decide), .pop 2,
    .dup 1 0 (by decide), .pop 1]
def resumeFinish : List (NPrim 4) := [.dup 3 0 (by decide), .pop 3]
def resumeProgram : NProg 4 := prepend resumePre (.seq (nmvAll 1 0 (by decide)) (ops resumeFinish))

theorem fail_runs (s : Bool) (k m b : Nat) (E : List Nat) :
    NRuns (failProgram s) (st [] (E.reverse ++ [b, m, 0, k + 1]) [] [])
      (st [3, 0, if s then 1 else 0, k] [] [] []) (3 * E.length + 30) := by
  let S := st [] (E.reverse ++ [b, m, 0, k + 1]) [] []
  let A := st [] (E.reverse ++ [b, m, 0]) [] [k]
  have hpre : applied failPre S = A := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp [applied, failPre, S, A, st, NPrim.apply, mapTop, Lists.set]
  have hc := nruns_clr 1 A
  let B := st [] [] [] [k]
  have hclear : A.set 1 [] = B := by
    funext i
    by_cases hi : i = 1 <;> simp_all [A, B, st, Lists.set]
  rw [hclear] at hc
  have hf := ops_runs (failFinish s) B
  have hfinish : result (failFinish s) B = st [3, 0, if s then 1 else 0, k] [] [] [] := by
    cases s <;> funext i
    all_goals
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi with rfl | rfl | rfl | rfl <;>
        simp [result, applied, failFinish, constants, B, st, NPrim.apply, mapTop, Lists.set]
  rw [hfinish] at hf
  have hall := prepend_runs failPre _ S _ _ (by rw [hpre]; exact hc.seq hf)
  refine hall.mono ?_
  cases s <;> simp [failPre, failFinish, constants, A, st] <;> omega

theorem resume_runs (q k m b : Nat) (E : List Nat) :
    NRuns resumeProgram (st [] (E.reverse ++ [b, m, 0, k + 1, q]) [] [])
      (st ([0, m, q, b] ++ E ++ [k]) [] [] []) (3 * E.length + 30) := by
  let S := st [] (E.reverse ++ [b, m, 0, k + 1, q]) [] []
  let A := st [0, m, q, b] E.reverse [] [k]
  have hpre : applied resumePre S = A := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp [applied, resumePre, S, A, st, NPrim.apply, mapTop, Lists.set]
  have hm := nruns_mvAll 1 0 (by decide : (1 : Fin 4) ≠ 0) A
  let B := st ([0, m, q, b] ++ E) [] [] [k]
  have hmove : (A.set 0 (A 0 ++ (A 1).reverse)).set 1 [] = B := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;> simp [A, B, st, Lists.set]
  rw [hmove] at hm
  have hf := ops_runs resumeFinish B
  have hfinish : result resumeFinish B = st ([0, m, q, b] ++ E ++ [k]) [] [] [] := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp [result, applied, resumeFinish, B, st, NPrim.apply, mapTop, Lists.set]
  rw [hfinish] at hf
  have hall := prepend_runs resumePre _ S _ _ (by rw [hpre]; exact hm.seq hf)
  exact hall.mono (by simp [resumePre, resumeFinish, A, st]; omega)

def branches : List (NProg 4) := [failProgram false, failProgram true, resumeProgram]
def numeric : NProg 4 := .seq (nmvAll 0 1 (by decide))
  (prepend [.pop 1, .pop 1] (caseTop 1 branches (.halt false)))

theorem numeric_runs (r : Res) (k m b : Nat) (E : List Nat) :
    NRuns numeric (st (inputFields r k m b E) [] [] [])
      (st (outputFields r k m b E) [] [] []) (6 * E.length + 80) := by
  let S := st (inputFields r k m b E) [] [] []
  let R := (S.set 1 (S 1 ++ (S 0).reverse)).set 0 []
  have hrev := nruns_mvAll 0 1 (by decide : (0 : Fin 4) ≠ 1) S
  let H := applied [.pop 1, .pop 1] R
  have hH : H = st [] (remaining r k m b E ++ [tag r]) [] [] := by
    cases r <;> (try (rename_i rr; cases rr))
    all_goals
      funext i
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi with rfl | rfl | rfl | rfl <;>
        simp [H, R, S, applied, st, inputFields, remaining, tag, NPrim.apply, Lists.set, List.append_assoc]
  have hpop : H.set 1 (remaining r k m b E) = st [] (remaining r k m b E) [] [] := by
    rw [hH]
    funext i
    by_cases hi : i = 1 <;> simp_all [st, Lists.set]
  have hh := caseTop_runs 1 branches (.halt false) (tag r)
    (by cases r <;> (try (rename_i rr; cases rr)) <;> simp [tag, branches])
    H (remaining r k m b E) (by rw [hH]; simp [st]) (st (outputFields r k m b E) [] [] [])
    (3 * E.length + 30) (by
      rw [hpop]
      cases r with
      | none => exact fail_runs false k m b E
      | some r => cases r with
        | none => exact fail_runs true k m b E
        | some q => exact resume_runs q k m b E)
  have hpre := prepend_runs [.pop 1, .pop 1] _ R _ _ hh
  have hall := hrev.seq hpre
  have hlen : (S 0).length ≤ E.length + 8 := by
    cases r <;> (try (rename_i rr; cases rr)) <;> simp [S, st, inputFields] <;> omega
  have ht : tag r ≤ 2 := by cases r <;> (try (rename_i rr; cases rr)) <;> simp [tag]
  exact hall.mono (by simp; omega)

def stepBound (A : Nat) : Nat := 12 * A + 100
def cellBound (A : Nat) : Nat := 9 + 2 * A
def scratchSpace (A N : Nat) : Nat := cellBound A * (N + 1) + grow N (stepBound A) + 2

theorem scratchSpace_linear (A N : Nat) :
    scratchSpace A N = (cellBound A + stepBound A) * N +
      (cellBound A + stepBound A * (stepBound A + 1) + 2) := by
  simp only [scratchSpace, grow, Nat.mul_add, Nat.add_mul, Nat.mul_one]
  omega

theorem compiled_runs (r : Res) (k m b : Nat) (E : List Nat) {A N B : Nat}
    (hE : E.length ≤ 1 + 2 * A) (hb : ∀ v ∈ inputFields r k m b E, v ≤ N)
    (hspace : scratchSpace A N ≤ B) :
    Complexity.Runs (LenOK B) numeric.compile (encL (st (inputFields r k m b E) [] [] []))
      (encL (st (outputFields r k m b E) [] [] [])) (stepBound A * ncost B) := by
  have hlen : (inputFields r k m b E).length ≤ cellBound A := by
    cases r <;> (try (rename_i rr; cases rr)) <;> simp [inputFields, cellBound] <;> omega
  have hcells : (encS (inputFields r k m b E)).length ≤ cellBound A * (N + 1) :=
    Nat.le_trans (SequentialFrontRead.locals_length _ N hb) (Nat.mul_le_mul_right _ hlen)
  have hBnd : Bnd N (cellBound A * (N + 1)) (st (inputFields r k m b E) [] [] []) := by
    constructor
    · intro i v hv
      by_cases hi : i = 0
      · exact hb v (by simpa [st, hi] using hv)
      · simp [st, hi] at hv
    · intro i
      by_cases hi : i = 0
      · simpa [st, hi] using hcells
      · simp [st, hi, encS]
  have hr := (numeric_runs r k m b E).mono (show 6 * E.length + 80 ≤ stepBound A by unfold stepBound; omega)
  obtain ⟨t, ht, hx⟩ := hr
  have hxB := (nexec_space hx N (cellBound A * (N + 1)) hBnd).2 B (by
    have hg := grow_mono (m := N) ht
    unfold scratchSpace at hspace
    omega)
  obtain ⟨t', ht', he⟩ := nexec_compile (fun _ h => h) hxB
  exact ⟨t', Nat.le_trans ht' (Nat.mul_le_mul_right _ ht), he⟩

def reg (i : Fin 5) : Fin 11 :=
  if i = 0 then 9 else if i = 1 then 10 else if i = 2 then 5 else if i = 3 then 6 else 7
theorem reg_injective : Function.Injective reg := by unfold Function.Injective; decide
def localProgram : LProg 11 := numeric.compile.rename reg

theorem local_runs (r : Res) (k m b : Nat) (E : List Nat) {A N B width held : Nat} (tail : List Bool)
    (hE : E.length ≤ 1 + 2 * A) (hb : ∀ v ∈ inputFields r k m b E, v ≤ N)
    (hspace : scratchSpace A N ≤ B)
    (hR : LenOK B (SequentialFieldFetch.start width [] tail (SequentialFrontRead.locals (inputFields r k m b E)) held [])) :
    Complexity.Runs (LenOK B) localProgram
      (SequentialFieldFetch.start width [] tail (SequentialFrontRead.locals (inputFields r k m b E)) held [])
      (SequentialFieldFetch.start width [] tail (SequentialFrontRead.locals (outputFields r k m b E)) held [])
      (stepBound A * ncost B) := by
  let R := SequentialFieldFetch.start width [] tail (SequentialFrontRead.locals (inputFields r k m b E)) held []
  let R' := SequentialFieldFetch.start width [] tail (SequentialFrontRead.locals (outputFields r k m b E)) held []
  have hproj : ∀ i, R (reg i) = encL (st (inputFields r k m b E) [] [] []) i := by
    intro i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      simp [R, reg, SequentialFieldFetch.start, encL, encS, st, SequentialFrontRead.locals] <;> rfl
  obtain ⟨t, ht, hx⟩ := compiled_runs r k m b E hE hb hspace
  have he := hx.rename_frame reg_injective R hR
  rw [Lists.frame_eq reg_injective R _ hproj] at he
  have hout : (encL (st (outputFields r k m b E) [] [] [])).frame reg R = R' := by
    funext j
    by_cases hj : ∃ i, reg i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [Lists.frame_get reg_injective]
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
      rcases hi with rfl | rfl | rfl | rfl | rfl <;>
        simp [R', reg, SequentialFieldFetch.start, encL, encS, st, SequentialFrontRead.locals] <;> rfl
    · rw [Lists.frame_outside R _ j hj]
      have h9 : j ≠ 9 := by intro hh; subst j; exact hj ⟨0, rfl⟩
      simp [R, R', SequentialFieldFetch.start, h9]
  change LExec (LenOK B) localProgram R t (.cont ((encL (st (outputFields r k m b E) [] [] [])).frame reg R)) at he
  rw [hout] at he
  exact ⟨t, ht, he⟩

def nextTask (r : Res) (m : Nat) (E : CaptureEnv) (b : MExp) : Task :=
  match r with
  | some (some q) => .expr m E b q
  | r => .value (.expr r)

theorem original_step (g : MGrammar) (x : List Char) (r : Res) (m : Nat) (E : CaptureEnv)
    (b : MExp) (K : List SequentialStack.Frame) :
    step g x ⟨.value (.expr r), .seq m E b :: K⟩ = some ⟨nextTask r m E b, K⟩ := by
  cases r <;> (try (rename_i rr; cases rr)) <;> rfl

theorem input_prefix (ns : List CompileNode) (r : Res) (m : Nat) (E : CaptureEnv) (b : MExp)
    (K : List SequentialStack.Frame) :
    SequentialFront.prefixCode ns K ⟨.value (.expr r), [.seq m E b]⟩ =
      inputFields r K.length m (exprId ns b) (writeEnv E) := by
  cases r <;> (try (rename_i rr; cases rr)) <;>
    simp [SequentialFront.prefixCode, SequentialFront.suffixCode, inputFields, writeTask, writeValue,
      writeRes, writeFrame, writeExpr, Nat.add_comm]

theorem output_prefix (ns : List CompileNode) (r : Res) (m : Nat) (E : CaptureEnv) (b : MExp)
    (K : List SequentialStack.Frame) :
    SequentialFront.prefixCode ns K ⟨nextTask r m E b, []⟩ =
      outputFields r K.length m (exprId ns b) (writeEnv E) := by
  cases r <;> (try (rename_i rr; cases rr)) <;>
    simp [SequentialFront.prefixCode, SequentialFront.suffixCode, outputFields, nextTask, writeTask,
      writeValue, writeRes, writeExpr, Nat.add_comm]

end Shallot.MacroPeg.CBV.SequentialSeqReturn
