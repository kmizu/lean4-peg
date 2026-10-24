import MacroPeg.CBV.SequentialCodeTest
import MacroPeg.CBV.SequentialInputPair

/-! One-character atoms reread the original input, test the returned code,
and advance the saved suffix position exactly on success. -/
namespace Shallot.MacroPeg.CBV.SequentialCharacterMachine
open Complexity Complexity.NBoundedTransfer
open SequentialCodeTest (Kind)
open SequentialInputRead (codes result)
open SequentialInputPair (state)

def testReg (i : Fin 5) : Fin 7 :=
  if i=0 then 3 else if i=1 then 4 else if i=2 then 6 else if i=3 then 1 else 2

theorem testReg_injective : Function.Injective testReg := by unfold Function.Injective; decide

def input (x : List Char) (p : Nat) : Lists 7 := state (codes x) [] [] [p] []
def output (k : Kind) (x : List Char) (p : Nat) : Lists 7 :=
  state (codes x) [] [] [if k.accepts (result x p) then p-1 else p]
    (if k.accepts (result x p) then [0] else [])

def program (k : Kind) : NProg 7 := .seq (.prim (.dup 5 2 (by decide)))
  (.seq (SequentialInputRead.program.rename SequentialInputPair.left SequentialInputPair.left_injective)
    (.seq ((SequentialCodeTest.program k).rename testReg testReg_injective)
      (.ite 6 .zero (.prim (.dec 5)) (.prim (.pop 2)))))

def capacity (k : Kind) (n : Nat) : Nat := SequentialInputRead.space n + SequentialCodeTest.capacity k

theorem capacity_linear (k : Kind) (n : Nat) :
    capacity k n = (2^32+2)*n + (3+SequentialCodeTest.capacity k) := by
  unfold capacity SequentialInputRead.space
  omega

private theorem test_frame (k : Kind) (x : List Char) (p : Nat) :
    (SequentialNumericFive.st [] [] (if k.accepts (result x p) then [0] else []) [] []).frame testReg
      (state (codes x) [] [result x p] [p] []) =
    state (codes x) [] [] [p] (if k.accepts (result x p) then [0] else []) := by
  funext j
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | simpa [testReg,state] using Lists.frame_get testReg_injective
        (state (codes x) [] [result x p] [p] [])
        (SequentialNumericFive.st [] [] (if k.accepts (result x p) then [0] else []) [] []) 0
    | simpa [testReg,state] using Lists.frame_get testReg_injective
        (state (codes x) [] [result x p] [p] [])
        (SequentialNumericFive.st [] [] (if k.accepts (result x p) then [0] else []) [] []) 1
    | simpa [testReg,state] using Lists.frame_get testReg_injective
        (state (codes x) [] [result x p] [p] [])
        (SequentialNumericFive.st [] [] (if k.accepts (result x p) then [0] else []) [] []) 2
    | simpa [testReg,state] using Lists.frame_get testReg_injective
        (state (codes x) [] [result x p] [p] [])
        (SequentialNumericFive.st [] [] (if k.accepts (result x p) then [0] else []) [] []) 3
    | simpa [testReg,state] using Lists.frame_get testReg_injective
        (state (codes x) [] [result x p] [p] [])
        (SequentialNumericFive.st [] [] (if k.accepts (result x p) then [0] else []) [] []) 4
    | exact (Lists.frame_outside (ρ := testReg) _ _ _ (by decide)).trans (by rfl)

private theorem input_fits (k : Kind) (x : List Char) (p : Nat) (hp : p ≤ x.length) :
    NFits (capacity k x.length) (input x p) := by
  have hh := SequentialInputRead.encoded_length x
  refine ⟨by unfold capacity SequentialInputRead.space; omega,fun i => ?_⟩
  by_cases hi : i=0
  · subst i
    change (Complexity.encS (codes x)).length+2 ≤ capacity k x.length
    unfold capacity SequentialInputRead.space
    omega
  · have hi' : i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by omega
    rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [input,state,Complexity.encS,encN] <;>
      unfold capacity SequentialInputRead.space <;> omega

private theorem result_bound (x : List Char) (p : Nat) : result x p ≤ 2^32 := by
  cases hs : sfx x p with
  | nil => simp [result,hs]
  | cons c cs => simpa only [result,hs] using SequentialInputRead.code_bound c

theorem character_runs (k : Kind) (x : List Char) (p : Nat) (hp : p ≤ x.length) :
    FitsRuns (capacity k x.length) (program k) (input x p) (output k x p)
      (8*p+SequentialCodeTest.cost k+13) := by
  let S := input x p
  let A := state (codes x) [p] [] [p] []
  let R := state (codes x) [] [result x p] [p] []
  let D := state (codes x) [] [] [p] (if k.accepts (result x p) then [0] else [])
  have hS := input_fits k x p hp
  have heA : (input x p).set 2 [p] = A := by
    funext i
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [input,A,state,Lists.set]
  have hA : NFits (capacity k x.length) A := by
    rw [← heA]
    exact replace hS 2 [p] (hS.2 5)
  have hprep : FitsRuns (capacity k x.length) (.prim (.dup 5 2 (by decide))) S A 1 := by
    have he : (NPrim.dup (K := 7) 5 2 (by decide)).apply S = A := by
      simpa [S,NPrim.apply,input,state] using heA
    refine ⟨1,by omega,?_⟩
    rw [← he]
    exact .prim (a := .dup 5 2 (by decide)) hS (by rwa [he])
  have hr := SequentialInputPair.read_into SequentialInputPair.left SequentialInputPair.left_injective
    A hA x p hp (by
      intro i
      have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp [A,SequentialInputPair.left,state])
    (by unfold capacity SequentialInputRead.space; omega)
  have heR : (A.set (SequentialInputPair.left 2) []).set (SequentialInputPair.left 3) [result x p] = R := by
    funext i
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [A,R,SequentialInputPair.left,state,Lists.set]
  rw [heR] at hr
  have hR : NFits (capacity k x.length) R := by obtain ⟨_,_,he⟩ := hr; exact he.post
  have hproj : ∀ i, R (testReg i) = SequentialNumericFive.st [result x p] [] [] [] [] i := by
    intro i
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp [R,state,testReg]
  have ht := ((SequentialCodeTest.predicate_fits k (result x p) (result_bound x p)).mono_space
    (show SequentialCodeTest.capacity k ≤ capacity k x.length by unfold capacity; omega)).rename_frame
      testReg_injective R hR
  rw [Lists.frame_eq testReg_injective R _ hproj] at ht
  change FitsRuns _ _ R ((SequentialNumericFive.st [] [] (if k.accepts (result x p) then [0] else []) [] []).frame
    testReg (state (codes x) [] [result x p] [p] [])) _ at ht
  rw [test_frame] at ht
  have hD : NFits (capacity k x.length) D := by obtain ⟨_,_,he⟩ := ht; exact he.post
  have hf : FitsRuns (capacity k x.length) (.ite 6 .zero (.prim (.dec 5)) (.prim (.pop 2)))
      D (output k x p) 2 := by
    by_cases ha : k.accepts (result x p)
    · have he : (NPrim.dec (K := 7) 5).apply D = output k x p := by
        funext i
        have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by omega
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [D,output,state,NPrim.apply,Lists.set,mapTop,ha]
      have hh : NExec (NFits (capacity k x.length)) (.prim (.dec 5)) D 1 (.cont (output k x p)) := by
        rw [← he]
        exact .prim hD (NShrinkingCompare.fits_dec hD 5)
      exact ⟨2,by omega,.iteT hD (by simp [D,state,NTest.eval,ha]) hh⟩
    · have he : (NPrim.pop (K := 7) 2).apply D = output k x p := by
        funext i
        have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by omega
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [D,output,state,NPrim.apply,Lists.set,ha]
      have hh : NExec (NFits (capacity k x.length)) (.prim (.pop 2)) D 1 (.cont (output k x p)) := by
        rw [← he]
        exact .prim hD (NShrinkingCompare.fits_pop hD 2)
      exact ⟨2,by omega,.iteF hD (by simp [D,state,NTest.eval,ha]) hh⟩
  obtain ⟨t,ht,he⟩ := hprep.seq (hr.seq (ht.seq hf))
  exact ⟨t,by omega,he⟩

def value (S : Lists 7) : Option Nat := if NTest.zero.eval (S 6) then (S 5).getLast? else none

theorem value_output (k : Kind) (x : List Char) (p : Nat) :
    value (output k x p) = if k.accepts (result x p) then some (p-1) else none := by
  by_cases ha : k.accepts (result x p) <;> simp [value,output,state,ha,NTest.eval]

theorem character_value (k : Kind) (x : List Char) (p : Nat) (E : SequentialStack.CaptureEnv)
    (hp : p ≤ x.length) :
    some (value (output k x p)) = SequentialStack.atom x E k.exp p := by
  rw [value_output]
  have hlen := length_sfx x hp
  cases hs : sfx x p with
  | nil =>
    cases k with
    | any => simp [Kind.accepts,result,hs,Kind.exp,SequentialStack.atom]
    | chr c => simp [Kind.accepts,result,hs,Kind.exp,SequentialStack.atom,SequentialInputRead.code]
    | range lo hi => simp [Kind.accepts,result,hs,Kind.exp,SequentialStack.atom,SequentialInputRead.code]
  | cons d ds =>
    rw [hs] at hlen
    have ht : p-1=ds.length := by simp only [List.length_cons] at hlen; omega
    cases k with
    | any => simp [Kind.accepts,result,hs,Kind.exp,SequentialStack.atom,SequentialInputRead.code,ht]
    | chr c =>
      by_cases hc : c.toNat = d.toNat <;>
        simp [Kind.accepts,result,hs,Kind.exp,SequentialStack.atom,SequentialInputRead.code,ht,Shallot.beqChar,hc]
    | range lo hi =>
      by_cases hl : lo.toNat ≤ d.toNat <;> by_cases hh : d.toNat ≤ hi.toNat <;>
        simp [Kind.accepts,result,hs,Kind.exp,SequentialStack.atom,SequentialInputRead.code,ht,Shallot.leChar,hl,hh]

theorem compiled_character (k : Kind) (x : List Char) (p : Nat) (hp : p ≤ x.length) :
    Runs (LenOK (capacity k x.length)) (program k).compile (encL (input x p)) (encL (output k x p))
      ((8*p+SequentialCodeTest.cost k+13)*ncost (capacity k x.length)) := by
  obtain ⟨t,ht,he⟩ := character_runs k x p hp
  obtain ⟨u,hu,h⟩ := nexec_compile (fun _ h => h) he
  exact ⟨u,Nat.le_trans hu (Nat.mul_le_mul_right _ ht),h⟩

theorem character_tape (k : Kind) (x : List Char) (p : Nat) (E : SequentialStack.CaptureEnv)
    (hp : p ≤ x.length) (τ : Tapes 8) (hτ : Rep (encL (input x p)) τ) :
    ∃ t τ', Exec (TFits (capacity k x.length)) (program k).compile.compile τ t (.cont τ') ∧
      Rep (encL (output k x p)) τ' ∧ some (value (output k x p)) = SequentialStack.atom x E k.exp p := by
  obtain ⟨t,τ',_,he,hr⟩ := Complexity.BinaryWord.runs_tape (compiled_character k x p hp) τ hτ
  exact ⟨t,τ',he,hr,character_value k x p E hp⟩

end Shallot.MacroPeg.CBV.SequentialCharacterMachine
