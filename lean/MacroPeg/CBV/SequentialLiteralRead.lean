import MacroPeg.CBV.SequentialCharacterMachine

/-! A fixed literal is a finite composition of original-input character reads.
The first failed character stops the composition without copying any input. -/
namespace Shallot.MacroPeg.CBV.SequentialLiteralRead
open Complexity Complexity.NBoundedTransfer
open SequentialInputRead (codes result)
open SequentialInputPair (state)
open SequentialCharacterMachine (input value)

def program : List Char → NProg 7
  | [] => .prim (.pushZ 6)
  | c::cs => .seq (SequentialCharacterMachine.program (.chr c))
      (.ite 6 .zero (.seq (.prim (.pop 6)) (program cs)) (.prim (.pop 2)))

def reserve : List Char → Nat
  | [] => 3
  | c::cs => SequentialCodeTest.capacity (.chr c) + reserve cs

def capacity (w : List Char) (n : Nat) : Nat := SequentialInputRead.space n + reserve w

def time : List Char → Nat → Nat
  | [],_ => 1
  | c::cs,n => 8*n+SequentialCodeTest.cost (.chr c)+16+time cs n

def scan (x : List Char) : List Char → Nat → Nat × Bool
  | [],p => (p,true)
  | c::cs,p => if SequentialInputRead.code c = result x p then scan x cs (p-1) else (p,false)

def final (x : List Char) (v : Nat × Bool) : Lists 7 :=
  state (codes x) [] [] [v.1] (if v.2 then [0] else [])

theorem capacity_linear (w : List Char) (n : Nat) :
    capacity w n = (2^32+2)*n + (3+reserve w) := by
  unfold capacity SequentialInputRead.space
  omega

private theorem input_fits (w : List Char) (x : List Char) (p : Nat) (hp : p ≤ x.length)
    {B : Nat} (hB : capacity w x.length ≤ B) : NFits B (input x p) := by
  have hh := SequentialInputRead.encoded_length x
  refine ⟨by unfold capacity SequentialInputRead.space at hB; omega,fun i => ?_⟩
  by_cases hi : i=0
  · subst i
    change (Complexity.encS (codes x)).length+2 ≤ B
    unfold capacity SequentialInputRead.space at hB
    omega
  · have hi' : i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by omega
    rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [SequentialCharacterMachine.input,state,Complexity.encS,encN] <;>
      unfold capacity SequentialInputRead.space at hB <;> omega

theorem literal_runs (w : List Char) (x : List Char) (p : Nat) (hp : p ≤ x.length)
    {B : Nat} (hB : capacity w x.length ≤ B) :
    FitsRuns B (program w) (input x p) (final x (scan x w p)) (time w x.length) := by
  induction w generalizing p with
  | nil =>
    have hS := input_fits [] x p hp hB
    have he : (NPrim.pushZ (K := 7) 6).apply (input x p) = final x (scan x [] p) := by
      funext i
      have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by omega
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [SequentialCharacterMachine.input,final,scan,state,NPrim.apply,Lists.set]
    have hF : NFits B ((NPrim.pushZ (K := 7) 6).apply (input x p)) := by
      have hh := replace hS 6 [0] (by simp [Complexity.encS,encN]; unfold capacity SequentialInputRead.space at hB; omega)
      simpa [NPrim.apply,SequentialCharacterMachine.input,state] using hh
    exact ⟨1,by simp [time],by simpa only [program,he] using NExec.prim hS hF⟩
  | cons c cs ih =>
    have hchar := (SequentialCharacterMachine.character_runs (.chr c) x p hp).mono_space
      (show SequentialCharacterMachine.capacity (.chr c) x.length ≤ B by
        simp only [capacity,reserve,SequentialCharacterMachine.capacity] at hB ⊢
        omega)
    have hO : NFits B (SequentialCharacterMachine.output (.chr c) x p) := by
      obtain ⟨_,_,he⟩ := hchar
      exact he.post
    by_cases hc : SequentialInputRead.code c = result x p
    · have htail := ih (p-1) (by omega) (by simp only [capacity,reserve] at hB ⊢; omega)
      have he : (NPrim.pop (K := 7) 6).apply (SequentialCharacterMachine.output (.chr c) x p) = input x (p-1) := by
        funext i
        have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by omega
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [SequentialCharacterMachine.input,SequentialCharacterMachine.output,
            SequentialCodeTest.Kind.accepts,state,NPrim.apply,Lists.set,hc]
      have hpop : FitsRuns B (.prim (.pop 6)) (SequentialCharacterMachine.output (.chr c) x p) (input x (p-1)) 1 := by
        refine ⟨1,by omega,?_⟩
        rw [← he]
        exact .prim hO (NShrinkingCompare.fits_pop hO 6)
      obtain ⟨t,ht,heT⟩ := hpop.seq htail
      have hbranch : FitsRuns B (.ite 6 .zero (.seq (.prim (.pop 6)) (program cs)) (.prim (.pop 2)))
          (SequentialCharacterMachine.output (.chr c) x p) (final x (scan x cs (p-1))) (1+time cs x.length+1) :=
        ⟨t+1,by omega,.iteT hO (by
          simp [SequentialCharacterMachine.output,state,SequentialCodeTest.Kind.accepts,hc,NTest.eval]) heT⟩
      obtain ⟨t,ht,heT⟩ := hchar.seq hbranch
      exact ⟨t,by simp only [time]; omega,by simpa only [program,scan,if_pos hc] using heT⟩
    · have he : (NPrim.pop (K := 7) 2).apply (SequentialCharacterMachine.output (.chr c) x p) = final x (p,false) := by
        funext i
        have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by omega
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [final,SequentialCharacterMachine.output,state,SequentialCodeTest.Kind.accepts,hc,NPrim.apply,Lists.set]
      have hpop : FitsRuns B (.prim (.pop 2)) (SequentialCharacterMachine.output (.chr c) x p) (final x (p,false)) 1 := by
        refine ⟨1,by omega,?_⟩
        rw [← he]
        exact .prim hO (NShrinkingCompare.fits_pop hO 2)
      obtain ⟨t,ht,heT⟩ := hpop
      have hbranch : FitsRuns B (.ite 6 .zero (.seq (.prim (.pop 6)) (program cs)) (.prim (.pop 2)))
          (SequentialCharacterMachine.output (.chr c) x p) (final x (p,false)) 2 :=
        ⟨t+1,by omega,.iteF hO (by
          simp [SequentialCharacterMachine.output,state,SequentialCodeTest.Kind.accepts,hc,NTest.eval]) heT⟩
      obtain ⟨t,ht,heT⟩ := hchar.seq hbranch
      exact ⟨t,by simp only [time]; omega,by simpa only [program,scan,if_neg hc] using heT⟩

theorem scan_correct (w : List Char) (x : List Char) (p : Nat) (hp : p ≤ x.length) :
    (if (scan x w p).2 then some (scan x w p).1 else none) =
      (Shallot.stripPrefix? w (sfx x p)).map List.length := by
  induction w generalizing p with
  | nil => simp [scan,Shallot.stripPrefix?,length_sfx x hp]
  | cons c cs ih =>
    cases hs : sfx x p with
    | nil => simp [scan,result,hs,SequentialInputRead.code,Shallot.stripPrefix?]
    | cons d ds =>
      have ht := sfx_tail hp hs
      have hh := ih (p-1) (by omega)
      rw [ht] at hh
      by_cases he : c.toNat = d.toNat
      · simpa [scan,result,hs,SequentialInputRead.code,Shallot.stripPrefix?,Shallot.beqChar,he] using hh
      · simp [scan,result,hs,SequentialInputRead.code,Shallot.stripPrefix?,Shallot.beqChar,he]

theorem value_final (x : List Char) (v : Nat × Bool) :
    value (final x v) = if v.2 then some v.1 else none := by
  obtain ⟨p,b⟩ := v
  cases b <;> simp [value,final,state,NTest.eval]

theorem literal_value (w : List Char) (x : List Char) (p : Nat) (E : SequentialStack.CaptureEnv)
    (hp : p ≤ x.length) :
    some (value (final x (scan x w p))) = SequentialStack.atom x E (.lit w) p := by
  rw [value_final,scan_correct w x p hp]
  simp only [SequentialStack.atom]
  cases Shallot.stripPrefix? w (sfx x p) <;> rfl

theorem compiled_literal (w : List Char) (x : List Char) (p : Nat) (hp : p ≤ x.length) :
    Runs (LenOK (capacity w x.length)) (program w).compile (encL (input x p)) (encL (final x (scan x w p)))
      (time w x.length*ncost (capacity w x.length)) := by
  obtain ⟨t,ht,he⟩ := literal_runs w x p hp (Nat.le_refl _)
  obtain ⟨u,hu,h⟩ := nexec_compile (fun _ h => h) he
  exact ⟨u,Nat.le_trans hu (Nat.mul_le_mul_right _ ht),h⟩

theorem literal_tape (w : List Char) (x : List Char) (p : Nat) (E : SequentialStack.CaptureEnv)
    (hp : p ≤ x.length) (τ : Tapes 8) (hτ : Rep (encL (input x p)) τ) :
    ∃ t τ', Exec (TFits (capacity w x.length)) (program w).compile.compile τ t (.cont τ') ∧
      Rep (encL (final x (scan x w p))) τ' ∧
      some (value (final x (scan x w p))) = SequentialStack.atom x E (.lit w) p := by
  obtain ⟨t,τ',_,he,hr⟩ := Complexity.BinaryWord.runs_tape (compiled_literal w x p hp) τ hτ
  exact ⟨t,τ',he,hr,literal_value w x p E hp⟩

end Shallot.MacroPeg.CBV.SequentialLiteralRead
