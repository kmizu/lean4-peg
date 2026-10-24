import MacroPeg.CBV.SequentialEnvLookup

/-! Obtain a capture from its runtime environment, then compare its original
input interval. The original input and following frame fields are preserved. -/
namespace Shallot.MacroPeg.CBV.SequentialParamMachine
open Complexity Complexity.NBoundedTransfer SequentialStack SequentialStackCodec
open SequentialInputRead (codes)

/-- A separate environment source and its two scratch registers accompany the
span machine. -/
def host (S : Lists 10) (F : List Nat) : Lists 13 := fun i =>
  if i=0 then S 0 else if i=1 then S 1 else if i=2 then S 2 else
  if i=3 then S 3 else if i=4 then S 4 else if i=5 then S 5 else
  if i=6 then S 6 else if i=7 then S 7 else if i=8 then S 8 else
  if i=9 then S 9 else if i=11 then F else []
def spanReg (i : Fin 10) : Fin 13 := ⟨i.val,by omega⟩
def envReg (i : Fin 5) : Fin 13 :=
  if i=0 then 11 else if i=1 then 12 else if i=2 then 10 else if i=3 then 7 else 9

theorem spanReg_injective : Function.Injective spanReg := by
  intro a b h; apply Fin.ext; exact congrArg (fun i : Fin 13 => i.val) h

theorem envReg_injective : Function.Injective envReg := by unfold Function.Injective; decide

def empty (x : List Char) (p : Nat) : Lists 10 :=
  ((SequentialSpanMachine.start x 0 p 0).set 7 []).set 9 []

def chosen (x : List Char) (p : Nat) : Option (Nat × Nat) → Lists 10
  | none => empty x p
  | some (a,b) => SequentialSpanMachine.start x a p b

def input (x : List Char) (p : Nat) (E : CaptureEnv) (F : List Nat) : Lists 13 :=
  host (empty x p) ((writeEnv E ++ F).reverse)

def final (x : List Char) (p : Nat) (F : List Nat) : Option (Nat × Nat) → Lists 13
  | none => host (empty x p) F.reverse
  | some (a,b) => host (SequentialSpanMachine.output x (SequentialSpanMachine.scan x (a-b) a p)) F.reverse

private theorem host_get (S : Lists 10) (F : List Nat) (i : Fin 10) :
    host S F (spanReg i) = S i := by
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem span_frame (S S' : Lists 10) (F : List Nat) :
    S'.frame spanReg (host S F) = host S' F := by
  funext j
  by_cases hj : j.val < 10
  · let i : Fin 10 := ⟨j.val,hj⟩
    have he : spanReg i = j := rfl
    rw [← he,Lists.frame_get spanReg_injective,host_get]
  · rw [Lists.frame_outside _ _ j (by
      intro ⟨i,hi⟩
      have hh := congrArg Fin.val hi
      simp only [spanReg] at hh
      omega)]
    have hi : j=10 ∨ j=11 ∨ j=12 := by omega
    rcases hi with rfl | rfl | rfl <;> simp [host]

private theorem env_frame (x : List Char) (p : Nat) (D F : List Nat) (r : Option (Nat × Nat)) :
    (SequentialEnvLookup.done F r).frame envReg (host (empty x p) D) = host (chosen x p r) F.reverse := by
  cases r with
  | none =>
    funext j
    have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 := by omega
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | simpa [host,envReg,chosen,empty,SequentialSpanMachine.start,SequentialSpanMachine.state,
          SequentialEnvLookup.done,Lists.set] using Lists.frame_get envReg_injective (host (empty x p) D) (SequentialEnvLookup.done F none) 0
      | simpa [host,envReg,chosen,empty,SequentialSpanMachine.start,SequentialSpanMachine.state,
          SequentialEnvLookup.done,Lists.set] using Lists.frame_get envReg_injective (host (empty x p) D) (SequentialEnvLookup.done F none) 1
      | simpa [host,envReg,chosen,empty,SequentialSpanMachine.start,SequentialSpanMachine.state,
          SequentialEnvLookup.done,Lists.set] using Lists.frame_get envReg_injective (host (empty x p) D) (SequentialEnvLookup.done F none) 2
      | simpa [host,envReg,chosen,empty,SequentialSpanMachine.start,SequentialSpanMachine.state,
          SequentialEnvLookup.done,Lists.set] using Lists.frame_get envReg_injective (host (empty x p) D) (SequentialEnvLookup.done F none) 3
      | simpa [host,envReg,chosen,empty,SequentialSpanMachine.start,SequentialSpanMachine.state,
          SequentialEnvLookup.done,Lists.set] using Lists.frame_get envReg_injective (host (empty x p) D) (SequentialEnvLookup.done F none) 4
      | exact Lists.frame_outside (ρ := envReg) _ _ _ (by decide)
  | some pair =>
    obtain ⟨a,b⟩ := pair
    funext j
    have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 := by omega
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | simpa [host,envReg,chosen,empty,SequentialSpanMachine.start,SequentialSpanMachine.state,
          SequentialEnvLookup.done,Lists.set] using Lists.frame_get envReg_injective (host (empty x p) D) (SequentialEnvLookup.done F (some (a,b))) 0
      | simpa [host,envReg,chosen,empty,SequentialSpanMachine.start,SequentialSpanMachine.state,
          SequentialEnvLookup.done,Lists.set] using Lists.frame_get envReg_injective (host (empty x p) D) (SequentialEnvLookup.done F (some (a,b))) 1
      | simpa [host,envReg,chosen,empty,SequentialSpanMachine.start,SequentialSpanMachine.state,
          SequentialEnvLookup.done,Lists.set] using Lists.frame_get envReg_injective (host (empty x p) D) (SequentialEnvLookup.done F (some (a,b))) 2
      | simpa [host,envReg,chosen,empty,SequentialSpanMachine.start,SequentialSpanMachine.state,
          SequentialEnvLookup.done,Lists.set] using Lists.frame_get envReg_injective (host (empty x p) D) (SequentialEnvLookup.done F (some (a,b))) 3
      | simpa [host,envReg,chosen,empty,SequentialSpanMachine.start,SequentialSpanMachine.state,
          SequentialEnvLookup.done,Lists.set] using Lists.frame_get envReg_injective (host (empty x p) D) (SequentialEnvLookup.done F (some (a,b))) 4
      | exact (Lists.frame_outside (ρ := envReg) (host (empty x p) D)
          (SequentialEnvLookup.done F (some (a,b))) _ (by decide)).trans (by rfl)

def program (k : Nat) : NProg 13 := .seq (SequentialEnvLookup.program k |>.rename envReg envReg_injective)
  (.ite 7 .nonempty (SequentialSpanMachine.spanProgram.rename spanReg spanReg_injective) (.prim (.pop 10)))

def time (A : Nat) (x : List Char) : Nat :=
  8*A+10+1+(4*x.length+6+x.length*SequentialSpanMachine.stepTime x)

theorem param_runs (k : Nat) (x : List Char) (p : Nat) (E : CaptureEnv) (F : List Nat)
    {A N e B : Nat} (hE : E.length ≤ A) (hvalid : SequentialSpanRecompute.ValidEnv x.length E)
    (hp : p ≤ x.length) (hR : NFits B (input x p E F))
    (hS : Bnd N e (SequentialNumericFive.st ((writeEnv E ++ F).reverse) [] [] [] []))
    (hB : e+grow N (8*A+10)+2 ≤ B) (hspace : SequentialSpanMachine.space x ≤ B) :
    FitsRuns B (program k) (input x p E F) (final x p F E[k]?) (time A x) := by
  let R := input x p E F
  have hproj : ∀ i, R (envReg i) = SequentialNumericFive.st ((writeEnv E ++ F).reverse) [] [] [] [] i := by
    intro i
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hl := (SequentialEnvLookup.lookup_fits k E F hE hS hB).rename_frame envReg_injective R hR
  rw [Lists.frame_eq envReg_injective R _ hproj] at hl
  change FitsRuns B _ R ((SequentialEnvLookup.done F E[k]?).frame envReg
    (host (empty x p) ((writeEnv E ++ F).reverse))) _ at hl
  rw [env_frame] at hl
  have hC : NFits B (host (chosen x p E[k]?) F.reverse) := by
    obtain ⟨_,_,he⟩ := hl
    exact he.post
  cases hs : E[k]? with
  | none =>
    rw [hs] at hl hC
    have hepop : (NPrim.pop (K := 13) 10).apply (host (empty x p) F.reverse) = host (empty x p) F.reverse := by
      funext i
      by_cases hi : i=10
      · subst i; simp [NPrim.apply,host,Lists.set]
      · simp [NPrim.apply,Lists.set_ne _ _ hi]
    have hr : FitsRuns B (.prim (.pop 10)) (host (empty x p) F.reverse) (host (empty x p) F.reverse) 1 := by
      refine ⟨1,by omega,?_⟩
      have hh := NExec.prim (a := NPrim.pop (K := 13) 10) (S := host (empty x p) F.reverse) hC (by rwa [hepop])
      simpa only [hepop] using hh
    obtain ⟨t,ht,he⟩ := hr
    have htst : NTest.nonempty.eval (host (empty x p) F.reverse 7) = false := by
      simp [host,empty,Lists.set,NTest.eval]
    have hx : FitsRuns B (.ite 7 .nonempty (SequentialSpanMachine.spanProgram.rename spanReg spanReg_injective)
        (.prim (.pop 10))) (host (empty x p) F.reverse) (host (empty x p) F.reverse) 2 :=
      ⟨t+1,by omega,.iteF hC htst he⟩
    obtain ⟨u,hu,huE⟩ := hl.seq hx
    exact ⟨u,by unfold time; omega,by simpa only [program,hs,final] using huE⟩
  | some pair =>
    obtain ⟨a,b⟩ := pair
    have hv := hvalid (a,b) (List.mem_of_getElem? hs)
    rw [hs] at hl hC
    have hr := ((SequentialSpanMachine.span_runs x a b p hv.1 hv.2 hp).mono_space hspace).rename_frame
      spanReg_injective (host (SequentialSpanMachine.start x a p b) F.reverse) hC
    rw [span_frame,span_frame] at hr
    obtain ⟨t,ht,he⟩ := hr
    have htst : NTest.nonempty.eval (host (SequentialSpanMachine.start x a p b) F.reverse 7) = true := by
      simp [host,SequentialSpanMachine.start,SequentialSpanMachine.state,NTest.eval]
    have hx : FitsRuns B (.ite 7 .nonempty (SequentialSpanMachine.spanProgram.rename spanReg spanReg_injective)
        (.prim (.pop 10))) (host (SequentialSpanMachine.start x a p b) F.reverse)
        (host (SequentialSpanMachine.output x (SequentialSpanMachine.scan x (a-b) a p)) F.reverse)
        (4*x.length+6+x.length*SequentialSpanMachine.stepTime x+1) := by
      refine ⟨t+1,?_,.iteT hC htst he⟩
      have hm := Nat.mul_le_mul_right (SequentialSpanMachine.stepTime x) (show a-b ≤ x.length by omega)
      omega
    obtain ⟨u,hu,huE⟩ := hl.seq hx
    exact ⟨u,by unfold time; omega,by simpa only [program,hs,final] using huE⟩

def value (S : Lists 13) : Option Nat := if NTest.zero.eval (S 9) then (S 8).getLast? else none

theorem param_value (k : Nat) (x : List Char) (p : Nat) (E : CaptureEnv) (F : List Nat)
    (hp : p ≤ x.length) (hvalid : SequentialSpanRecompute.ValidEnv x.length E) :
    some (value (final x p F E[k]?)) = SequentialStack.atom x E (.param k) p := by
  cases hs : E[k]? with
  | none => simp [SequentialStack.atom,hs,final,value,host,empty,Lists.set,NTest.eval]
  | some pair =>
    obtain ⟨a,b⟩ := pair
    have ha := (hvalid (a,b) (List.mem_of_getElem? hs)).2
    change some (SequentialSpanMachine.value (SequentialSpanMachine.output x
      (SequentialSpanMachine.scan x (a-b) a p))) = _
    rw [SequentialSpanMachine.span_value x a b p ha hp]
    simp only [SequentialStack.atom,hs]

def fieldCells (A M N : Nat) : Nat := (1+2*A+M)*(N+1)

def capacity (A M N n : Nat) : Nat :=
  SequentialInputRead.space n + fieldCells A M N + grow N (8*A+10) + 2

theorem capacity_linear (A M N n : Nat) :
    capacity A M N n = (2^32+2)*n + ((1+2*A+M)+(8*A+10))*N +
      ((1+2*A+M)+(8*A+10)*((8*A+10)+1)+5) := by
  simp only [capacity,SequentialInputRead.space,fieldCells,grow,Nat.mul_add,Nat.add_mul,Nat.mul_one]
  omega

private theorem fields_bound (x : List Char) (E : CaptureEnv) (F : List Nat) {A M N : Nat}
    (hE : E.length ≤ A) (hvalid : SequentialSpanRecompute.ValidEnv x.length E)
    (hn : x.length ≤ N) (hA : A ≤ N) (hF : F.length ≤ M) (hFb : ∀ v ∈ F, v ≤ N) :
    Bnd N (fieldCells A M N) (SequentialNumericFive.st ((writeEnv E ++ F).reverse) [] [] [] []) := by
  have henv := SequentialStackCodecBound.env_bounded ⟨hvalid,hE⟩ hn hA
  have hvs : ∀ v ∈ writeEnv E ++ F, v ≤ N := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact henv v hv
    · exact hFb v hv
  have hlen : (writeEnv E ++ F).length ≤ 1+2*A+M := by
    rw [List.length_append,SequentialStackCodecBound.env_length]
    omega
  have hc : (Complexity.encS (writeEnv E ++ F)).length ≤ fieldCells A M N := by
    have hh := SequentialFrontRead.locals_length (writeEnv E ++ F) N hvs
    have he : SequentialFrontRead.locals (writeEnv E ++ F) = Complexity.encS (writeEnv E ++ F) := rfl
    rw [he] at hh
    exact Nat.le_trans hh (Nat.mul_le_mul_right (N+1) hlen)
  constructor
  · intro i v hv
    by_cases hi : i=0
    · exact hvs v (by simpa [SequentialNumericFive.st,hi,List.mem_append,or_comm] using hv)
    · simp [SequentialNumericFive.st,hi] at hv
  · intro i
    by_cases hi : i=0
    · subst i
      change (Complexity.encS ((writeEnv E ++ F).reverse)).length ≤ fieldCells A M N
      rw [NBoundedTransfer.reverse_length]
      exact hc
    · simp [SequentialNumericFive.st,hi,Complexity.encS]

private theorem input_fits (x : List Char) (p : Nat) (E : CaptureEnv) (F : List Nat)
    {A M N : Nat} (hp : p ≤ x.length)
    (hb : Bnd N (fieldCells A M N) (SequentialNumericFive.st ((writeEnv E ++ F).reverse) [] [] [] [])) :
    NFits (capacity A M N x.length) (input x p E F) := by
  have hinput := SequentialInputRead.encoded_length x
  have hfields := hb.2 0
  have hB : SequentialInputRead.space x.length ≤ capacity A M N x.length := by unfold capacity; omega
  refine ⟨by unfold SequentialInputRead.space at hB; omega,fun i => ?_⟩
  by_cases hi0 : i=0
  · subst i
    change (Complexity.encS (codes x)).length+2 ≤ capacity A M N x.length
    unfold SequentialInputRead.space at hB
    omega
  · by_cases hi11 : i=11
    · subst i
      change (Complexity.encS ((writeEnv E ++ F).reverse)).length+2 ≤ capacity A M N x.length
      change (Complexity.encS ((writeEnv E ++ F).reverse)).length ≤ fieldCells A M N at hfields
      unfold capacity
      omega
    · by_cases hi8 : i=8
      · subst i
        change (Complexity.encS [p]).length+2 ≤ capacity A M N x.length
        simp only [Complexity.encS,encN,List.flatMap_cons,List.flatMap_nil,List.append_nil,
          List.length_cons,List.length_replicate]
        unfold SequentialInputRead.space at hB
        omega
      · have hi : i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=9 ∨ i=10 ∨ i=12 := by omega
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [input,host,empty,SequentialSpanMachine.start,SequentialSpanMachine.state,
            SequentialSpanMachine.blank,SequentialInputPair.state,Lists.set,Complexity.encS] <;>
          unfold SequentialInputRead.space at hB <;> omega

theorem linear_param_runs (k : Nat) (x : List Char) (p : Nat) (E : CaptureEnv) (F : List Nat)
    {A M N : Nat} (hE : E.length ≤ A) (hvalid : SequentialSpanRecompute.ValidEnv x.length E)
    (hp : p ≤ x.length) (hn : x.length ≤ N) (hA : A ≤ N)
    (hF : F.length ≤ M) (hFb : ∀ v ∈ F, v ≤ N) :
    FitsRuns (capacity A M N x.length) (program k) (input x p E F) (final x p F E[k]?) (time A x) := by
  have hb := fields_bound x E F hE hvalid hn hA hF hFb
  exact param_runs k x p E F hE hvalid hp (input_fits x p E F hp hb) hb
    (by unfold capacity; omega) (by unfold capacity SequentialSpanMachine.space; omega)

theorem compiled_param (k : Nat) (x : List Char) (p : Nat) (E : CaptureEnv) (F : List Nat)
    {A M N : Nat} (hE : E.length ≤ A) (hvalid : SequentialSpanRecompute.ValidEnv x.length E)
    (hp : p ≤ x.length) (hn : x.length ≤ N) (hA : A ≤ N)
    (hF : F.length ≤ M) (hFb : ∀ v ∈ F, v ≤ N) :
    Runs (LenOK (capacity A M N x.length)) (program k).compile (encL (input x p E F))
      (encL (final x p F E[k]?)) (time A x * ncost (capacity A M N x.length)) := by
  obtain ⟨t,ht,he⟩ := linear_param_runs k x p E F hE hvalid hp hn hA hF hFb
  obtain ⟨u,hu,h⟩ := nexec_compile (fun _ h => h) he
  exact ⟨u,Nat.le_trans hu (Nat.mul_le_mul_right _ ht),h⟩

theorem param_tape (k : Nat) (x : List Char) (p : Nat) (E : CaptureEnv) (F : List Nat)
    {A M N : Nat} (hE : E.length ≤ A) (hvalid : SequentialSpanRecompute.ValidEnv x.length E)
    (hp : p ≤ x.length) (hn : x.length ≤ N) (hA : A ≤ N)
    (hF : F.length ≤ M) (hFb : ∀ v ∈ F, v ≤ N) (τ : Tapes 14)
    (hτ : Rep (encL (input x p E F)) τ) :
    ∃ t τ', Exec (TFits (capacity A M N x.length)) (program k).compile.compile τ t (.cont τ') ∧
      Rep (encL (final x p F E[k]?)) τ' ∧
      some (value (final x p F E[k]?)) = SequentialStack.atom x E (.param k) p := by
  obtain ⟨t,τ',_,he,hr⟩ := Complexity.BinaryWord.runs_tape
    (compiled_param k x p E F hE hvalid hp hn hA hF hFb) τ hτ
  exact ⟨t,τ',he,hr,param_value k x p E F hp hvalid⟩

end Shallot.MacroPeg.CBV.SequentialParamMachine
