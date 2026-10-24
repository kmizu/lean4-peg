import MacroPeg.CBV.SequentialAtomResult

/-! A parameter lookup and original-input span comparison now return the
ordinary encoded value task, preserving input and following frame fields. -/
namespace Shallot.MacroPeg.CBV.SequentialParamResult
open Complexity Complexity.NBoundedTransfer SequentialStack
open SequentialInputRead (codes)

theorem scan_bounds (x : List Char) (k a p : Nat) :
    (SequentialSpanMachine.scan x k a p).1 ≤ a ∧ (SequentialSpanMachine.scan x k a p).2.1 ≤ p := by
  induction k generalizing a p with
  | zero => simp [SequentialSpanMachine.scan]
  | succ k ih =>
    simp only [SequentialSpanMachine.scan]
    split
    · have hh := ih (a-1) (p-1); omega
    · exact ⟨Nat.le_refl _,Nat.le_refl _⟩

def view (x : List Char) (p : Nat) : Option (Nat × Nat) → List Nat × Nat × Bool
  | none => ([],p,false)
  | some (a,b) =>
    let v := SequentialSpanMachine.scan x (a-b) a p
    ([v.1],v.2.1,v.2.2)

theorem final_view (x : List Char) (p : Nat) (F : List Nat) (r : Option (Nat × Nat)) :
    SequentialParamMachine.final x p F r = SequentialAtomResult.input (codes x)
      (view x p r).1 (view x p r).2.1 (view x p r).2.2 F.reverse := by
  cases r with
  | none =>
    funext i
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  | some r =>
    obtain ⟨a,b⟩ := r
    funext i
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem view_bounds (x : List Char) (p : Nat) (r : Option (Nat × Nat)) :
    (view x p r).1.length ≤ 1 ∧ (view x p r).2.1 ≤ p := by
  cases r with
  | none => simp [view]
  | some r =>
    obtain ⟨a,b⟩ := r
    exact ⟨by simp [view],(scan_bounds x (a-b) a p).2⟩

private theorem value_input (X S R : List Nat) (q : Nat) (b : Bool) :
    some (SequentialParamMachine.value (SequentialAtomResult.input X S q b R)) = SequentialAtomResult.result q b := by
  cases b <;> simp [SequentialParamMachine.value,SequentialAtomResult.input,
    SequentialAtomResult.state,SequentialAtomResult.result,NTest.eval]

def program (index : Nat) : NProg 13 := .seq (SequentialParamMachine.program index) SequentialAtomResult.program

def capacity (A M N n : Nat) : Nat := SequentialParamMachine.capacity A (M+1) N n + SequentialAtomResult.space M N

theorem capacity_linear (A M N n : Nat) :
    capacity A M N n = (2^32+2)*n +
      (((1+2*A+(M+1))+(8*A+10))+((M+3)+(3*M+30)))*N +
      ((1+2*A+(M+1))+(8*A+10)*((8*A+10)+1)+5 + ((M+3)+(3*M+30)*(3*M+31)+2)) := by
  rw [capacity,SequentialParamMachine.capacity_linear,SequentialAtomResult.space_linear]
  simp only [Nat.add_mul]
  omega

theorem param_runs (index : Nat) (x : List Char) (p k : Nat) (E : CaptureEnv) (F : List Nat)
    {A M N : Nat} (hE : E.length ≤ A) (hvalid : SequentialSpanRecompute.ValidEnv x.length E)
    (hp : p ≤ x.length) (hn : x.length ≤ N) (hA : A ≤ N) (h2 : 2 ≤ N)
    (hk : k ≤ N) (hF : F.length ≤ M) (hFb : ∀ v ∈ F, v ≤ N) :
    FitsRuns (capacity A M N x.length) (program index) (SequentialParamMachine.input x p E ([k] ++ F))
      (SequentialAtomResult.output (codes x) (SequentialAtomCodec.outputFields (atom x E (.param index) p) k F))
      (SequentialParamMachine.time A x+3*M+36) := by
  have htail : ∀ v ∈ [k] ++ F, v ≤ N := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · have he : v=k := List.mem_singleton.mp hv; simpa only [he] using hk
    · exact hFb v hv
  have hparam := (SequentialParamMachine.linear_param_runs index x p E ([k] ++ F) hE hvalid hp hn hA
    (show ([k] ++ F).length ≤ M+1 by simp; omega) htail).mono_space
      (show SequentialParamMachine.capacity A (M+1) N x.length ≤ capacity A M N x.length by unfold capacity; omega)
  have hR : NFits (capacity A M N x.length) (SequentialParamMachine.final x p ([k] ++ F) E[index]?) := by
    obtain ⟨_,_,he⟩ := hparam
    exact he.post
  rw [final_view] at hR hparam
  have hb := view_bounds x p E[index]?
  have hf := SequentialAtomResult.bounded_result_runs (codes x) (view x p E[index]?).1
    (view x p E[index]?).2.1 k (view x p E[index]?).2.2 F hb.1 hR h2 (by omega) hk hF hFb
    (show SequentialAtomResult.space M N ≤ capacity A M N x.length by unfold capacity; omega)
  have hsem : SequentialAtomResult.result (view x p E[index]?).2.1 (view x p E[index]?).2.2 =
      atom x E (.param index) p := by
    have hh := SequentialParamMachine.param_value index x p E ([k] ++ F) hp hvalid
    rw [final_view,value_input] at hh
    exact hh
  rw [hsem] at hf
  obtain ⟨t,ht,he⟩ := hparam.seq hf
  exact ⟨t,by omega,he⟩

theorem compiled_param (index : Nat) (x : List Char) (p k : Nat) (E : CaptureEnv) (F : List Nat)
    {A M N : Nat} (hE : E.length ≤ A) (hvalid : SequentialSpanRecompute.ValidEnv x.length E)
    (hp : p ≤ x.length) (hn : x.length ≤ N) (hA : A ≤ N) (h2 : 2 ≤ N)
    (hk : k ≤ N) (hF : F.length ≤ M) (hFb : ∀ v ∈ F, v ≤ N) :
    Runs (LenOK (capacity A M N x.length)) (program index).compile
      (encL (SequentialParamMachine.input x p E ([k] ++ F)))
      (encL (SequentialAtomResult.output (codes x) (SequentialAtomCodec.outputFields (atom x E (.param index) p) k F)))
      ((SequentialParamMachine.time A x+3*M+36)*ncost (capacity A M N x.length)) := by
  obtain ⟨t,ht,he⟩ := param_runs index x p k E F hE hvalid hp hn hA h2 hk hF hFb
  obtain ⟨u,hu,h⟩ := nexec_compile (fun _ h => h) he
  exact ⟨u,Nat.le_trans hu (Nat.mul_le_mul_right _ ht),h⟩

theorem param_tape (index : Nat) (x : List Char) (p k : Nat) (E : CaptureEnv) (F : List Nat)
    {A M N : Nat} (hE : E.length ≤ A) (hvalid : SequentialSpanRecompute.ValidEnv x.length E)
    (hp : p ≤ x.length) (hn : x.length ≤ N) (hA : A ≤ N) (h2 : 2 ≤ N)
    (hk : k ≤ N) (hF : F.length ≤ M) (hFb : ∀ v ∈ F, v ≤ N) (τ : Tapes 14)
    (hτ : Rep (encL (SequentialParamMachine.input x p E ([k] ++ F))) τ) :
    ∃ t τ', Exec (TFits (capacity A M N x.length)) (program index).compile.compile τ t (.cont τ') ∧
      Rep (encL (SequentialAtomResult.output (codes x)
        (SequentialAtomCodec.outputFields (atom x E (.param index) p) k F))) τ' := by
  obtain ⟨t,τ',_,he,hr⟩ := Complexity.BinaryWord.runs_tape
    (compiled_param index x p k E F hE hvalid hp hn hA h2 hk hF hFb) τ hτ
  exact ⟨t,τ',he,hr⟩

end Shallot.MacroPeg.CBV.SequentialParamResult
