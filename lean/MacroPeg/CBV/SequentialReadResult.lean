import MacroPeg.CBV.SequentialParamResult

/-! Character and literal readers share a return layout and the same value-task
assembler. The caller has already removed the capture environment. -/
namespace Shallot.MacroPeg.CBV.SequentialReadResult
open Complexity Complexity.NBoundedTransfer SequentialStack
open SequentialInputRead (codes)

def reg (i : Fin 7) : Fin 13 :=
  if i=0 then 0 else if i=1 then 1 else if i=2 then 2 else if i=3 then 3 else if i=4 then 4 else if i=5 then 8 else 9

theorem reg_injective : Function.Injective reg := by unfold Function.Injective; decide

private theorem frame_output (x : List Char) (p q : Nat) (b : Bool) (R : List Nat) :
    (SequentialLiteralRead.final x (q,b)).frame reg (SequentialAtomResult.input (codes x) [] p false R) =
      SequentialAtomResult.input (codes x) [] q b R := by
  funext j
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 := by omega
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | simpa [reg,SequentialLiteralRead.final,SequentialInputPair.state,SequentialAtomResult.input,SequentialAtomResult.state] using
        Lists.frame_get reg_injective (SequentialAtomResult.input (codes x) [] p false R) (SequentialLiteralRead.final x (q,b)) 0
    | simpa [reg,SequentialLiteralRead.final,SequentialInputPair.state,SequentialAtomResult.input,SequentialAtomResult.state] using
        Lists.frame_get reg_injective (SequentialAtomResult.input (codes x) [] p false R) (SequentialLiteralRead.final x (q,b)) 1
    | simpa [reg,SequentialLiteralRead.final,SequentialInputPair.state,SequentialAtomResult.input,SequentialAtomResult.state] using
        Lists.frame_get reg_injective (SequentialAtomResult.input (codes x) [] p false R) (SequentialLiteralRead.final x (q,b)) 2
    | simpa [reg,SequentialLiteralRead.final,SequentialInputPair.state,SequentialAtomResult.input,SequentialAtomResult.state] using
        Lists.frame_get reg_injective (SequentialAtomResult.input (codes x) [] p false R) (SequentialLiteralRead.final x (q,b)) 3
    | simpa [reg,SequentialLiteralRead.final,SequentialInputPair.state,SequentialAtomResult.input,SequentialAtomResult.state] using
        Lists.frame_get reg_injective (SequentialAtomResult.input (codes x) [] p false R) (SequentialLiteralRead.final x (q,b)) 4
    | simpa [reg,SequentialLiteralRead.final,SequentialInputPair.state,SequentialAtomResult.input,SequentialAtomResult.state] using
        Lists.frame_get reg_injective (SequentialAtomResult.input (codes x) [] p false R) (SequentialLiteralRead.final x (q,b)) 5
    | simpa [reg,SequentialLiteralRead.final,SequentialInputPair.state,SequentialAtomResult.input,SequentialAtomResult.state] using
        Lists.frame_get reg_injective (SequentialAtomResult.input (codes x) [] p false R) (SequentialLiteralRead.final x (q,b)) 6
    | exact (Lists.frame_outside (ρ := reg) _ _ _ (by decide)).trans (by rfl)

def program (reader : NProg 7) : NProg 13 := .seq (reader.rename reg reg_injective) SequentialAtomResult.program

theorem return_runs (reader : NProg 7) (x : List Char) (p q k : Nat) (b : Bool) (F : List Nat)
    {B M N T : Nat} (hR : NFits B (SequentialAtomResult.input (codes x) [] p false ([k] ++ F).reverse))
    (hread : FitsRuns B reader (SequentialCharacterMachine.input x p) (SequentialLiteralRead.final x (q,b)) T)
    (h2 : 2 ≤ N) (hq : q ≤ N) (hk : k ≤ N) (hF : F.length ≤ M) (hFb : ∀ v ∈ F, v ≤ N)
    (hB : SequentialAtomResult.space M N ≤ B) :
    FitsRuns B (program reader) (SequentialAtomResult.input (codes x) [] p false ([k] ++ F).reverse)
      (SequentialAtomResult.output (codes x) (SequentialAtomCodec.outputFields (SequentialAtomResult.result q b) k F))
      (T+3*M+36) := by
  let R := SequentialAtomResult.input (codes x) [] p false ([k] ++ F).reverse
  have hp : ∀ i, R (reg i) = SequentialCharacterMachine.input x p i := by
    intro i
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have hr := hread.rename_frame reg_injective R hR
  rw [Lists.frame_eq reg_injective R _ hp,frame_output] at hr
  have hQ : NFits B (SequentialAtomResult.input (codes x) [] q b ([k] ++ F).reverse) := by
    obtain ⟨_,_,he⟩ := hr
    exact he.post
  have hf := SequentialAtomResult.bounded_result_runs (codes x) [] q k b F (by simp) hQ h2 hq hk hF hFb hB
  obtain ⟨t,ht,he⟩ := hr.seq hf
  exact ⟨t,by omega,he⟩

private theorem initial_fits (x : List Char) (p k : Nat) (F : List Nat) {B M N : Nat}
    (hp : p ≤ x.length) (hk : k ≤ N) (hF : F.length ≤ M) (hFb : ∀ v ∈ F, v ≤ N)
    (hinput : SequentialInputRead.space x.length ≤ B) (hframe : SequentialAtomResult.space M N ≤ B) :
    NFits B (SequentialAtomResult.input (codes x) [] p false ([k] ++ F).reverse) := by
  apply SequentialAtomResult.input_fits
  · have hh := SequentialInputRead.encoded_length x
    unfold SequentialInputRead.space at hinput
    omega
  · exact Nat.le_trans (SequentialAtomResult.frame_size k F hk hF hFb) hframe
  · unfold SequentialInputRead.space at hinput
    omega

def characterSpace (kind : SequentialCodeTest.Kind) (M N n : Nat) : Nat :=
  SequentialCharacterMachine.capacity kind n + SequentialAtomResult.space M N

theorem character_runs (kind : SequentialCodeTest.Kind) (x : List Char) (E : CaptureEnv)
    (p k : Nat) (F : List Nat) {M N : Nat} (hp : p ≤ x.length) (hn : x.length ≤ N)
    (h2 : 2 ≤ N) (hk : k ≤ N) (hF : F.length ≤ M) (hFb : ∀ v ∈ F, v ≤ N) :
    FitsRuns (characterSpace kind M N x.length) (program (SequentialCharacterMachine.program kind))
      (SequentialAtomResult.input (codes x) [] p false ([k] ++ F).reverse)
      (SequentialAtomResult.output (codes x) (SequentialAtomCodec.outputFields (atom x E kind.exp p) k F))
      (8*p+SequentialCodeTest.cost kind+13+3*M+36) := by
  let q := if kind.accepts (SequentialInputRead.result x p) then p-1 else p
  let b := decide (kind.accepts (SequentialInputRead.result x p))
  have hq : q ≤ N := by unfold q; split <;> omega
  have ho : SequentialCharacterMachine.output kind x p = SequentialLiteralRead.final x (q,b) := by
    by_cases ha : kind.accepts (SequentialInputRead.result x p) <;>
      simp [q,b,SequentialCharacterMachine.output,SequentialLiteralRead.final,ha]
  have hr := (SequentialCharacterMachine.character_runs kind x p hp).mono_space
    (show SequentialCharacterMachine.capacity kind x.length ≤ characterSpace kind M N x.length by unfold characterSpace; omega)
  rw [ho] at hr
  have hf := return_runs (SequentialCharacterMachine.program kind) x p q k b F
    (initial_fits x p k F hp hk hF hFb
      (show SequentialInputRead.space x.length ≤ characterSpace kind M N x.length by
        unfold characterSpace SequentialCharacterMachine.capacity; omega)
      (show SequentialAtomResult.space M N ≤ characterSpace kind M N x.length by unfold characterSpace; omega))
    hr h2 hq hk hF hFb (show SequentialAtomResult.space M N ≤ characterSpace kind M N x.length by unfold characterSpace; omega)
  have hs : SequentialAtomResult.result q b = atom x E kind.exp p := by
    have hh := SequentialCharacterMachine.character_value kind x p E hp
    rw [ho,SequentialLiteralRead.value_final] at hh
    exact hh
  rwa [hs] at hf

theorem literal_scan_bound (w : List Char) (x : List Char) (p : Nat) : (SequentialLiteralRead.scan x w p).1 ≤ p := by
  induction w generalizing p with
  | nil => simp [SequentialLiteralRead.scan]
  | cons c cs ih =>
    simp only [SequentialLiteralRead.scan]
    split
    · have hh := ih (p-1); omega
    · exact Nat.le_refl _

def literalSpace (w : List Char) (M N n : Nat) : Nat :=
  SequentialLiteralRead.capacity w n + SequentialAtomResult.space M N

theorem literal_runs (w : List Char) (x : List Char) (E : CaptureEnv) (p k : Nat) (F : List Nat)
    {M N : Nat} (hp : p ≤ x.length) (hn : x.length ≤ N) (h2 : 2 ≤ N)
    (hk : k ≤ N) (hF : F.length ≤ M) (hFb : ∀ v ∈ F, v ≤ N) :
    FitsRuns (literalSpace w M N x.length) (program (SequentialLiteralRead.program w))
      (SequentialAtomResult.input (codes x) [] p false ([k] ++ F).reverse)
      (SequentialAtomResult.output (codes x) (SequentialAtomCodec.outputFields (atom x E (.lit w) p) k F))
      (SequentialLiteralRead.time w x.length+3*M+36) := by
  have hr := SequentialLiteralRead.literal_runs w x p hp
    (show SequentialLiteralRead.capacity w x.length ≤ literalSpace w M N x.length by unfold literalSpace; omega)
  have hq : (SequentialLiteralRead.scan x w p).1 ≤ N := by have hh := literal_scan_bound w x p; omega
  have hf := return_runs (SequentialLiteralRead.program w) x p (SequentialLiteralRead.scan x w p).1 k
    (SequentialLiteralRead.scan x w p).2 F
    (initial_fits x p k F hp hk hF hFb
      (show SequentialInputRead.space x.length ≤ literalSpace w M N x.length by
        unfold literalSpace SequentialLiteralRead.capacity; omega)
      (show SequentialAtomResult.space M N ≤ literalSpace w M N x.length by unfold literalSpace; omega))
    hr h2 hq hk hF hFb (show SequentialAtomResult.space M N ≤ literalSpace w M N x.length by unfold literalSpace; omega)
  have hs : SequentialAtomResult.result (SequentialLiteralRead.scan x w p).1 (SequentialLiteralRead.scan x w p).2 =
      atom x E (.lit w) p := by
    have hh := SequentialLiteralRead.literal_value w x p E hp
    rw [SequentialLiteralRead.value_final] at hh
    exact hh
  rwa [hs] at hf

theorem characterSpace_linear (kind : SequentialCodeTest.Kind) (M N n : Nat) :
    characterSpace kind M N n = (2^32+2)*n + ((M+3)+(3*M+30))*N +
      (3+SequentialCodeTest.capacity kind+((M+3)+(3*M+30)*(3*M+31)+2)) := by
  rw [characterSpace,SequentialCharacterMachine.capacity_linear,SequentialAtomResult.space_linear]
  omega

theorem literalSpace_linear (w : List Char) (M N n : Nat) :
    literalSpace w M N n = (2^32+2)*n + ((M+3)+(3*M+30))*N +
      (3+SequentialLiteralRead.reserve w+((M+3)+(3*M+30)*(3*M+31)+2)) := by
  rw [literalSpace,SequentialLiteralRead.capacity_linear,SequentialAtomResult.space_linear]
  omega

theorem compiled_character (kind : SequentialCodeTest.Kind) (x : List Char) (E : CaptureEnv)
    (p k : Nat) (F : List Nat) {M N : Nat} (hp : p ≤ x.length) (hn : x.length ≤ N)
    (h2 : 2 ≤ N) (hk : k ≤ N) (hF : F.length ≤ M) (hFb : ∀ v ∈ F, v ≤ N) :
    Runs (LenOK (characterSpace kind M N x.length)) (program (SequentialCharacterMachine.program kind)).compile
      (encL (SequentialAtomResult.input (codes x) [] p false ([k] ++ F).reverse))
      (encL (SequentialAtomResult.output (codes x) (SequentialAtomCodec.outputFields (atom x E kind.exp p) k F)))
      ((8*p+SequentialCodeTest.cost kind+13+3*M+36)*ncost (characterSpace kind M N x.length)) := by
  obtain ⟨t,ht,he⟩ := character_runs kind x E p k F hp hn h2 hk hF hFb
  obtain ⟨u,hu,h⟩ := nexec_compile (fun _ h => h) he
  exact ⟨u,Nat.le_trans hu (Nat.mul_le_mul_right _ ht),h⟩

theorem compiled_literal (w : List Char) (x : List Char) (E : CaptureEnv) (p k : Nat) (F : List Nat)
    {M N : Nat} (hp : p ≤ x.length) (hn : x.length ≤ N) (h2 : 2 ≤ N)
    (hk : k ≤ N) (hF : F.length ≤ M) (hFb : ∀ v ∈ F, v ≤ N) :
    Runs (LenOK (literalSpace w M N x.length)) (program (SequentialLiteralRead.program w)).compile
      (encL (SequentialAtomResult.input (codes x) [] p false ([k] ++ F).reverse))
      (encL (SequentialAtomResult.output (codes x) (SequentialAtomCodec.outputFields (atom x E (.lit w) p) k F)))
      ((SequentialLiteralRead.time w x.length+3*M+36)*ncost (literalSpace w M N x.length)) := by
  obtain ⟨t,ht,he⟩ := literal_runs w x E p k F hp hn h2 hk hF hFb
  obtain ⟨u,hu,h⟩ := nexec_compile (fun _ h => h) he
  exact ⟨u,Nat.le_trans hu (Nat.mul_le_mul_right _ ht),h⟩

theorem character_tape (kind : SequentialCodeTest.Kind) (x : List Char) (E : CaptureEnv)
    (p k : Nat) (F : List Nat) {M N : Nat} (hp : p ≤ x.length) (hn : x.length ≤ N)
    (h2 : 2 ≤ N) (hk : k ≤ N) (hF : F.length ≤ M) (hFb : ∀ v ∈ F, v ≤ N)
    (τ : Tapes 14) (hτ : Rep (encL (SequentialAtomResult.input (codes x) [] p false ([k] ++ F).reverse)) τ) :
    ∃ t τ', Exec (TFits (characterSpace kind M N x.length))
        (program (SequentialCharacterMachine.program kind)).compile.compile τ t (.cont τ') ∧
      Rep (encL (SequentialAtomResult.output (codes x) (SequentialAtomCodec.outputFields (atom x E kind.exp p) k F))) τ' := by
  obtain ⟨t,τ',_,he,hr⟩ := Complexity.BinaryWord.runs_tape
    (compiled_character kind x E p k F hp hn h2 hk hF hFb) τ hτ
  exact ⟨t,τ',he,hr⟩

theorem literal_tape (w : List Char) (x : List Char) (E : CaptureEnv) (p k : Nat) (F : List Nat)
    {M N : Nat} (hp : p ≤ x.length) (hn : x.length ≤ N) (h2 : 2 ≤ N)
    (hk : k ≤ N) (hF : F.length ≤ M) (hFb : ∀ v ∈ F, v ≤ N)
    (τ : Tapes 14) (hτ : Rep (encL (SequentialAtomResult.input (codes x) [] p false ([k] ++ F).reverse)) τ) :
    ∃ t τ', Exec (TFits (literalSpace w M N x.length)) (program (SequentialLiteralRead.program w)).compile.compile τ t (.cont τ') ∧
      Rep (encL (SequentialAtomResult.output (codes x) (SequentialAtomCodec.outputFields (atom x E (.lit w) p) k F))) τ' := by
  obtain ⟨t,τ',_,he,hr⟩ := Complexity.BinaryWord.runs_tape
    (compiled_literal w x E p k F hp hn h2 hk hF hFb) τ hτ
  exact ⟨t,τ',he,hr⟩

end Shallot.MacroPeg.CBV.SequentialReadResult
