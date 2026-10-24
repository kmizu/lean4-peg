import MacroPeg.CBV.SequentialFrontRoundtrip
import Complexity.NMacros
import Complexity.ListRename

/-! An actual local Seq state update: return through a negative-lookahead
frame. All three expression outcomes are handled by one fixed program. -/

namespace Shallot.MacroPeg.CBV.SequentialNotReturn

open Complexity SequentialStack SequentialStackCodec CBVtoCBN

def neg (r : Res) (p : Nat) : Res :=
  match r with
  | none => none
  | some none => some (some p)
  | some (some _) => some none

def inputFields (r : Res) (k p : Nat) : List Nat :=
  match r with
  | none => [3, 0, 0, k + 1, 2, p]
  | some none => [3, 0, 1, k + 1, 2, p]
  | some (some q) => [3, 0, 2, q, k + 1, 2, p]

def outputFields (r : Res) (k p : Nat) : List Nat :=
  match r with
  | none => [3, 0, 0, k]
  | some none => [3, 0, 2, p, k]
  | some (some _) => [3, 0, 1, k]

def dataState (vs : List Nat) : Lists 3 := fun i => if i = 0 then vs else []
def revState (vs : List Nat) : Lists 3 := fun i => if i = 1 then vs else []

def prepend (ops : List (NPrim 3)) (next : NProg 3) : NProg 3 :=
  ops.foldr (fun op next => .seq (.prim op) next) next

def applied (ops : List (NPrim 3)) (S : Lists 3) : Lists 3 :=
  ops.foldl (fun S op => op.apply S) S

theorem prepend_runs (ops : List (NPrim 3)) (next : NProg 3) (S S' : Lists 3) (T : Nat)
    (h : NRuns next (applied ops S) S' T) : NRuns (prepend ops next) S S' (ops.length + T) := by
  induction ops generalizing S with
  | nil => simpa [prepend, applied] using h
  | cons op ops ih =>
    have hh := (nruns_prim op S).seq (ih (op.apply S) h)
    exact hh.mono (by simp; omega)

def runOps (ops : List (NPrim 3)) : NProg 3 := prepend ops (.prim (.dec 2))
def opsResult (ops : List (NPrim 3)) (S : Lists 3) : Lists 3 := (NPrim.dec 2).apply (applied ops S)

theorem runOps_runs (ops : List (NPrim 3)) (S : Lists 3) :
    NRuns (runOps ops) S (opsResult ops S) (ops.length + 1) :=
  prepend_runs ops _ S _ 1 (nruns_prim _ _)

def constants (i : Fin 3) (n : Nat) : List (NPrim 3) := .pushZ i :: List.replicate n (.inc i)

def common (tag : Nat) (savePos : Bool) : List (NPrim 3) :=
  [.dup 1 2 (by decide), .pop 1, .dec 2, .pop 1] ++
    constants 0 3 ++ constants 0 0 ++ constants 0 tag ++
    (if savePos then [.dup 1 0 (by decide)] else []) ++
    [.dup 2 0 (by decide), .pop 1, .pop 2]

def branchOps : Res → List (NPrim 3)
  | none => common 0 false
  | some none => common 2 true
  | some (some _) => .pop 1 :: common 1 false

def remaining (r : Res) (k p : Nat) : List Nat :=
  match r with
  | none | some none => [p, 2, k + 1]
  | some (some q) => [p, 2, k + 1, q]

def tag : Res → Nat
  | none => 0
  | some none => 1
  | some (some _) => 2

def branches : List (NProg 3) := [runOps (common 0 false), runOps (common 2 true), runOps (.pop 1 :: common 1 false)]

def numeric : NProg 3 := .seq (nmvAll 0 1 (by decide))
  (prepend [.pop 1, .pop 1] (caseTop 1 branches (.halt false)))

theorem branch_runs (r : Res) (k p : Nat) :
    NRuns (runOps (branchOps r)) (revState (remaining r k p)) (dataState (outputFields r k p)) 20 := by
  have h := runOps_runs (branchOps r) (revState (remaining r k p))
  have he : opsResult (branchOps r) (revState (remaining r k p)) = dataState (outputFields r k p) := by
    cases r <;> (try (rename_i rr; cases rr))
    all_goals
      funext i
      have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases hi with rfl | rfl | rfl <;>
        simp [opsResult, applied, branchOps, common, constants, remaining, outputFields,
          revState, dataState, NPrim.apply, mapTop, Lists.set]
  have hlen : (branchOps r).length + 1 ≤ 20 := by
    cases r <;> (try (rename_i rr; cases rr)) <;> simp [branchOps, common, constants]
  rw [he] at h
  exact h.mono hlen

theorem numeric_runs (r : Res) (k p : Nat) :
    NRuns numeric (dataState (inputFields r k p)) (dataState (outputFields r k p)) 50 := by
  let S := dataState (inputFields r k p)
  let R := (S.set 1 (S 1 ++ (S 0).reverse)).set 0 []
  have hrev := nruns_mvAll 0 1 (by decide : (0 : Fin 3) ≠ 1) S
  let H := applied [.pop 1, .pop 1] R
  have hH : H = revState (remaining r k p ++ [tag r]) := by
    cases r <;> (try (rename_i rr; cases rr))
    all_goals
      funext i
      have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases hi with rfl | rfl | rfl <;>
        simp [H, R, S, dataState, revState, applied, inputFields, remaining, tag, NPrim.apply, Lists.set]
  have hpop : H.set 1 (remaining r k p) = revState (remaining r k p) := by
    rw [hH]
    funext i
    by_cases hi : i = 1 <;> simp_all [revState, Lists.set]
  have hh := caseTop_runs 1 branches (.halt false) (tag r)
    (by cases r <;> (try (rename_i rr; cases rr)) <;> simp [tag, branches])
    H (remaining r k p) (by rw [hH]; simp [revState]) (dataState (outputFields r k p)) 20 (by
      rw [hpop]
      have hb := branch_runs r k p
      cases r with
      | none => exact hb
      | some r => cases r <;> exact hb)
  have hpre := prepend_runs [.pop 1, .pop 1] _ R _ _ hh
  have hall := hrev.seq hpre
  have hlen : (S 0).length ≤ 7 := by
    cases r with
    | none => simp [S, dataState, inputFields]
    | some r => cases r <;> simp [S, dataState, inputFields]
  have ht : tag r ≤ 2 := by cases r <;> (try (rename_i rr; cases rr)) <;> simp [tag]
  exact hall.mono (by simp; omega)

theorem original_step (g : MGrammar) (x : List Char) (r : Res) (p : Nat) (K : List SequentialStack.Frame) :
    step g x ⟨.value (.expr r), .notP p :: K⟩ = some ⟨.value (.expr (neg r p)), K⟩ := by
  cases r <;> (try (rename_i rr; cases rr)) <;> simp [step, neg]

theorem input_prefix (ns : List CompileNode) (r : Res) (p : Nat) (K : List SequentialStack.Frame) :
    SequentialFront.prefixCode ns K ⟨.value (.expr r), [.notP p]⟩ = inputFields r K.length p := by
  cases r <;> (try (rename_i rr; cases rr)) <;>
    simp [SequentialFront.prefixCode, SequentialFront.suffixCode, inputFields,
      writeTask, writeValue, writeRes, writeFrame, Nat.add_comm]

theorem output_prefix (ns : List CompileNode) (r : Res) (p : Nat) (K : List SequentialStack.Frame) :
    SequentialFront.prefixCode ns K ⟨.value (.expr (neg r p)), []⟩ = outputFields r K.length p := by
  cases r <;> (try (rename_i rr; cases rr)) <;>
    simp [SequentialFront.prefixCode, SequentialFront.suffixCode, outputFields,
      writeTask, writeValue, writeRes, neg, Nat.add_comm]

def scratchSpace (N : Nat) : Nat := 7 * (N + 1) + grow N 50 + 2

theorem scratchSpace_linear (N : Nat) : scratchSpace N = 57 * N + 2559 := by
  simp [scratchSpace, grow, Nat.mul_add]
  omega

theorem compiled_runs (r : Res) (k p : Nat) {N B : Nat}
    (hb : ∀ v ∈ inputFields r k p, v ≤ N) (hspace : scratchSpace N ≤ B) :
    Complexity.Runs (LenOK B) numeric.compile (encL (dataState (inputFields r k p)))
      (encL (dataState (outputFields r k p))) (50 * ncost B) := by
  have hlen : (inputFields r k p).length ≤ 7 := by
    cases r <;> (try (rename_i rr; cases rr)) <;> simp [inputFields]
  have hcells : (encS (inputFields r k p)).length ≤ 7 * (N + 1) := by
    have hh := SequentialFrontRead.locals_length (inputFields r k p) N hb
    have hm := Nat.mul_le_mul_right (N + 1) hlen
    exact Nat.le_trans hh hm
  have hBnd : Bnd N (7 * (N + 1)) (dataState (inputFields r k p)) := by
    constructor
    · intro i v hv
      by_cases hi : i = 0
      · simpa [dataState, hi] using hb v (by simpa [dataState, hi] using hv)
      · simp [dataState, hi] at hv
    · intro i
      by_cases hi : i = 0
      · simpa [dataState, hi] using hcells
      · simp [dataState, hi, encS]
  obtain ⟨t, ht, hx⟩ := numeric_runs r k p
  have hxB := (nexec_space hx N (7 * (N + 1)) hBnd).2 B (by
    have hg := grow_mono (m := N) ht
    unfold scratchSpace at hspace
    omega)
  obtain ⟨t', ht', he⟩ := nexec_compile (fun _ h => h) hxB
  exact ⟨t', Nat.le_trans ht' (Nat.mul_le_mul_right _ ht), he⟩

/-- The compiler's three numeric stacks and scratch use local registers only. -/
def reg (i : Fin 4) : Fin 11 :=
  if i = 0 then 9 else if i = 1 then 10 else if i = 2 then 5 else 7

theorem reg_injective : Function.Injective reg := by unfold Function.Injective; decide

def localProgram : LProg 11 := numeric.compile.rename reg

/-- The local operation changes the prefix fields and leaves the binary tail,
width, and parser's held value untouched. No computation of the next prefix
is supplied as an assumption. -/
theorem local_runs (r : Res) (k p : Nat) {N B width held : Nat} (tail : List Bool)
    (hb : ∀ v ∈ inputFields r k p, v ≤ N) (hspace : scratchSpace N ≤ B)
    (hR : LenOK B (SequentialFieldFetch.start width [] tail (SequentialFrontRead.locals (inputFields r k p)) held [])) :
    Complexity.Runs (LenOK B) localProgram
      (SequentialFieldFetch.start width [] tail (SequentialFrontRead.locals (inputFields r k p)) held [])
      (SequentialFieldFetch.start width [] tail (SequentialFrontRead.locals (outputFields r k p)) held [])
      (50 * ncost B) := by
  let R := SequentialFieldFetch.start width [] tail (SequentialFrontRead.locals (inputFields r k p)) held []
  let R' := SequentialFieldFetch.start width [] tail (SequentialFrontRead.locals (outputFields r k p)) held []
  have hproj : ∀ i, R (reg i) = encL (dataState (inputFields r k p)) i := by
    intro i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp [R, reg, SequentialFieldFetch.start, encL, encS, dataState, SequentialFrontRead.locals] <;> rfl
  obtain ⟨t, ht, hx⟩ := compiled_runs r k p hb hspace
  have he := hx.rename_frame reg_injective R hR
  rw [Lists.frame_eq reg_injective R _ hproj] at he
  have hout : (encL (dataState (outputFields r k p))).frame reg R = R' := by
    funext j
    by_cases hj : ∃ i, reg i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [Lists.frame_get reg_injective]
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi with rfl | rfl | rfl | rfl <;>
        simp [R', reg, SequentialFieldFetch.start, encL, encS, dataState, SequentialFrontRead.locals] <;> rfl
    · rw [Lists.frame_outside R _ j hj]
      have h9 : j ≠ 9 := by intro hh; subst j; exact hj ⟨0, rfl⟩
      simp [R, R', SequentialFieldFetch.start, h9]
  change LExec (LenOK B) localProgram R t (.cont ((encL (dataState (outputFields r k p))).frame reg R)) at he
  rw [hout] at he
  exact ⟨t, ht, he⟩

end Shallot.MacroPeg.CBV.SequentialNotReturn
