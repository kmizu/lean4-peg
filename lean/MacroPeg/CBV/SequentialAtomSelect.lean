import MacroPeg.CBV.SequentialAtomBranch

/-! Select every atomic transition using the source ID read from its encoded
task. Original-input readers and non-reading atoms share one fixed program. -/
namespace Shallot.MacroPeg.CBV.SequentialAtomSelect
open Complexity Complexity.NBoundedTransfer SequentialStack SequentialStackCodec SequentialStackPool CBVtoCBN
open SequentialNumericFive (st)
open SequentialInputRead (codes)

def state (X D R Q I : List Nat) : Lists 15 := fun i =>
  if i=0 then X else if i=8 then Q else if i=11 then R else if i=12 then D else if i=14 then I else []
def raw (x : List Char) : Lists 15 := state (codes x) [] [] [] []
def prepReg (i : Fin 5) : Fin 15 :=
  if i=0 then 12 else if i=1 then 11 else if i=2 then 14 else if i=3 then 8 else 10
def branchReg (i : Fin 13) : Fin 15 := ⟨i.val,by omega⟩

theorem prepReg_injective : Function.Injective prepReg := by unfold Function.Injective; decide

theorem branchReg_injective : Function.Injective branchReg := by
  intro a b h; apply Fin.ext; exact congrArg (fun i : Fin 15 => i.val) h

private theorem prep_frame (x : List Char) (D R I Q : List Nat) :
    (st D R I Q []).frame prepReg (raw x) = state (codes x) D R Q I := by
  funext j
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 := by omega
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | simpa [prepReg,state] using Lists.frame_get prepReg_injective (raw x) (st D R I Q []) 0
    | simpa [prepReg,state] using Lists.frame_get prepReg_injective (raw x) (st D R I Q []) 1
    | simpa [prepReg,state] using Lists.frame_get prepReg_injective (raw x) (st D R I Q []) 2
    | simpa [prepReg,state] using Lists.frame_get prepReg_injective (raw x) (st D R I Q []) 3
    | simpa [prepReg,state] using Lists.frame_get prepReg_injective (raw x) (st D R I Q []) 4
    | exact (Lists.frame_outside (ρ := prepReg) _ _ _ (by decide)).trans (by rfl)

private theorem branch_frame (X Q R D : List Nat) :
    (SequentialAtomResult.state X [] Q [] R D).frame branchReg (fun _ => []) = state X D R Q [] := by
  funext j
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 := by omega
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact Lists.frame_get branchReg_injective _ _ 0
    | exact Lists.frame_get branchReg_injective _ _ 1
    | exact Lists.frame_get branchReg_injective _ _ 2
    | exact Lists.frame_get branchReg_injective _ _ 3
    | exact Lists.frame_get branchReg_injective _ _ 4
    | exact Lists.frame_get branchReg_injective _ _ 5
    | exact Lists.frame_get branchReg_injective _ _ 6
    | exact Lists.frame_get branchReg_injective _ _ 7
    | exact Lists.frame_get branchReg_injective _ _ 8
    | exact Lists.frame_get branchReg_injective _ _ 9
    | exact Lists.frame_get branchReg_injective _ _ 10
    | exact Lists.frame_get branchReg_injective _ _ 11
    | exact Lists.frame_get branchReg_injective _ _ 12
    | exact Lists.frame_outside (ρ := branchReg) _ _ _ (by decide)

private theorem branch_input (x : List Char) (p k : Nat) (E : CaptureEnv) (F : List Nat) :
    SequentialParamMachine.input x p E ([k] ++ F) =
      SequentialAtomResult.state (codes x) [] [p] [] (writeEnv E ++ [k] ++ F).reverse [] := by
  funext i
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try rfl
  simp [SequentialParamMachine.input,SequentialParamMachine.host,SequentialAtomResult.state,List.append_assoc]

def prepTime (A M : Nat) : Nat := 6*A+3*M+50

def space (ns : List CompileNode) (A M N e n : Nat) : Nat :=
  SequentialInputRead.space n + (e+grow N (prepTime A M)+2) +
    SequentialAtomBranch.localSpace A M N (e+N+1) +
    ((exprPool ns).map (fun src => SequentialAtomBranch.reserve src A M N n)).sum

def time (ns : List CompileNode) (A M n : Nat) : Nat :=
  prepTime A M + ((exprPool ns).map (fun src => SequentialAtomBranch.time src A M n)).sum +
    2*(exprPool ns).length+2

private theorem member_le_sum {α : Type} (f : α → Nat) (xs : List α) (a : α) (ha : a ∈ xs) :
    f a ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    simp only [List.map_cons,List.sum_cons]
    rcases List.mem_cons.mp ha with he | hm
    · subst a; omega
    · have hh := ih hm; omega

private theorem normalized_bound (m p eid k : Nat) (E : CaptureEnv) (F : List Nat) {N e : Nat}
    (hb : Bnd N e (st (SequentialStructuralEntry.inputFields m p eid k E F) [] [] [] [])) :
    Bnd N (e+N+1) (st [] (writeEnv E ++ [k] ++ F).reverse [] [p] []) := by
  let W := writeEnv E ++ [k] ++ F
  have he : SequentialStructuralEntry.inputFields m p eid k E F = [0,m,p,eid] ++ W := by
    simp [SequentialStructuralEntry.inputFields,W,List.append_assoc]
  have hfull : ∀ v ∈ [0,m,p,eid] ++ W, v ≤ N := by simpa [he,SequentialNumericFive.st] using hb.1 0
  have hp : p ≤ N := hfull p (by simp)
  have hW : ∀ v ∈ W, v ≤ N := fun v hv => hfull v (List.mem_append_right _ hv)
  have hc : (Complexity.encS W).length ≤ e := by
    have hh := hb.2 0
    change (Complexity.encS (SequentialStructuralEntry.inputFields m p eid k E F)).length ≤ e at hh
    rw [he,length_encS_append] at hh
    omega
  constructor
  · intro i v hv
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · simp at hv
    · change v ∈ W.reverse at hv
      exact hW v (List.mem_reverse.mp hv)
    · simp at hv
    · have hvp : v=p := by simpa using hv
      subst v; exact hp
    · simp at hv
  · intro i
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · simp [Complexity.encS]
    · change (Complexity.encS W.reverse).length ≤ e+N+1
      rw [NBoundedTransfer.reverse_length]
      omega
    · simp [Complexity.encS]
    · simp [Complexity.encS,encN]; omega
    · simp [Complexity.encS]

private theorem raw_fits (x : List Char) {B : Nat} (hB : SequentialInputRead.space x.length ≤ B) : NFits B (raw x) := by
  have hh := SequentialInputRead.encoded_length x
  refine ⟨by unfold SequentialInputRead.space at hB; omega,fun i => ?_⟩
  by_cases hi : i=0
  · subst i
    change (Complexity.encS (codes x)).length+2 ≤ B
    unfold SequentialInputRead.space at hB
    omega
  · simp [raw,state,hi,Complexity.encS]
    unfold SequentialInputRead.space at hB
    omega

def branch (src : MExp) : NProg 15 := (SequentialAtomBranch.program src).rename branchReg branchReg_injective

def program (ns : List CompileNode) : NProg 15 := SequentialAtomCodec.select ns prepReg prepReg_injective branch

def input (ns : List CompileNode) (x : List Char) (m p k : Nat) (src : MExp) (E : CaptureEnv) (F : List Nat) : Lists 15 :=
  state (codes x) (SequentialStructuralEntry.inputFields m p (exprId ns src) k E F) [] [] []
def output (x : List Char) (r : Res) (k : Nat) (F : List Nat) : Lists 15 :=
  state (codes x) (SequentialAtomCodec.outputFields r k F) [] [] []

theorem selected_runs (ns : List CompileNode) (src : MExp) (hs : ExprOK ns src)
    (hatom : SequentialAtomCodec.Atomic src) (x : List Char) (m p k : Nat) (E : CaptureEnv) (F : List Nat)
    {A M N e : Nat} (hE : E.length ≤ A) (hvalid : SequentialSpanRecompute.ValidEnv x.length E)
    (hp : p ≤ x.length) (hn : x.length ≤ N) (hA : A ≤ N) (h2 : 2 ≤ N)
    (hk : k ≤ N) (hF : F.length ≤ M) (hFb : ∀ v ∈ F, v ≤ N)
    (hb : Bnd N e (st (SequentialStructuralEntry.inputFields m p (exprId ns src) k E F) [] [] [] [])) :
    FitsRuns (space ns A M N e x.length) (program ns) (input ns x m p k src E F)
      (output x (atom x E src p) k F) (time ns A M x.length) := by
  let B := space ns A M N e x.length
  have hraw : SequentialInputRead.space x.length ≤ B := by unfold B space; omega
  have hlocal : SequentialAtomBranch.localSpace A M N (e+N+1) ≤ B := by unfold B space; omega
  have hreserve : SequentialAtomBranch.reserve src A M N x.length ≤ B := by
    have hh := member_le_sum (fun s => SequentialAtomBranch.reserve s A M N x.length) (exprPool ns) src hs.mem
    unfold B space
    omega
  have hc := SequentialAtomBranch.branch_runs src hatom x p k E F hE hvalid hp hn hA h2 hk hF hFb
    (normalized_bound m p (exprId ns src) k E F hb) hlocal hraw hreserve
  have hblank : NFits B (fun _ : Fin 15 => []) := by
    refine ⟨by unfold SequentialInputRead.space at hraw; omega,fun _ => ?_⟩
    simp [Complexity.encS]
    unfold SequentialInputRead.space at hraw
    omega
  have hbranch := hc.rename_frame branchReg_injective (fun _ : Fin 15 => []) hblank
  rw [branch_input,branch_frame,SequentialAtomResult.output,branch_frame] at hbranch
  have hbranch' : FitsRuns B (branch src)
      ((st [] (writeEnv E ++ [k] ++ F).reverse [] [p] []).frame prepReg (raw x))
      (output x (atom x E src p) k F) (SequentialAtomBranch.time src A M x.length) := by
    rw [prep_frame]
    exact hbranch
  have hpB : e+grow N (6*A+3*M+50)+2 ≤ B := by unfold B space prepTime; omega
  have hall := SequentialAtomCodec.selected_runs ns prepReg prepReg_injective branch src hs m p k E F hE hF
    (raw x) (raw_fits x hraw) hb hpB _ hbranch'
  rw [prep_frame] at hall
  obtain ⟨t,ht,he⟩ := hall
  have htB := member_le_sum (fun s => SequentialAtomBranch.time s A M x.length) (exprPool ns) src hs.mem
  exact ⟨t,by unfold time prepTime; omega,he⟩

private theorem reserves_affine (es : List MExp) (A M : Nat) :
    ∃ a b c, ∀ N n, (es.map (fun src => SequentialAtomBranch.reserve src A M N n)).sum = a*n+b*N+c := by
  induction es with
  | nil => exact ⟨0,0,0,by intro N n; simp⟩
  | cons src es ih =>
    obtain ⟨a,b,c,h⟩ := SequentialAtomBranch.reserve_affine src A M
    obtain ⟨a',b',c',h'⟩ := ih
    refine ⟨a+a',b+b',c+c',?_⟩
    intro N n
    simp only [List.map_cons,List.sum_cons,h,h',Nat.add_mul]
    omega

theorem space_affine (ns : List CompileNode) (A M : Nat) :
    ∃ a b c, ∀ N e n, space ns A M N e n = a*n+b*N+2*e+c := by
  obtain ⟨a,b,c,h⟩ := reserves_affine (exprPool ns) A M
  let P := prepTime A M
  let L := SequentialAtomBranch.localTime A M
  refine ⟨(2^32+2)+a,P+L+1+b,P*(P+1)+L*(L+1)+c+8,?_⟩
  intro N e n
  unfold space
  rw [h]
  change SequentialInputRead.space n+(e+grow N P+2)+
    (e+N+1+grow N L+2)+(a*n+b*N+c) = _
  simp only [SequentialInputRead.space,grow,Nat.mul_add,Nat.add_mul,Nat.mul_one]
  omega

def frontCells (A M N : Nat) : Nat := (6+2*A+M)*(N+1)

private theorem input_bound (ns : List CompileNode) (src : MExp) (m p k : Nat) (E : CaptureEnv) (F : List Nat)
    {A M N : Nat} (hE : E.length ≤ A) (hvalid : SequentialSpanRecompute.ValidEnv N E)
    (hm : m ≤ N) (hp : p ≤ N) (hi : exprId ns src ≤ N) (hk : k ≤ N) (hA : A ≤ N)
    (hF : F.length ≤ M) (hFb : ∀ v ∈ F, v ≤ N) :
    Bnd N (frontCells A M N) (st (SequentialStructuralEntry.inputFields m p (exprId ns src) k E F) [] [] [] []) := by
  have henv := SequentialStackCodecBound.env_bounded ⟨hvalid,hE⟩ (Nat.le_refl N) hA
  let vs := SequentialStructuralEntry.inputFields m p (exprId ns src) k E F
  have hv : ∀ v ∈ vs, v ≤ N := by
    intro v hv
    simp only [vs,SequentialStructuralEntry.inputFields,List.mem_append] at hv
    rcases hv with ((hv | hv) | hv) | hv
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> omega
    · exact henv v hv
    · have he : v=k := List.mem_singleton.mp hv; simpa only [he] using hk
    · exact hFb v hv
  have hlen : vs.length ≤ 6+2*A+M := by
    simp only [vs,SequentialStructuralEntry.inputFields,List.length_append,SequentialStackCodecBound.env_length,
      List.length_cons,List.length_nil]
    omega
  have hc := SequentialFrontRead.locals_length vs N hv
  change (Complexity.encS vs).length ≤ vs.length*(N+1) at hc
  have hc' := Nat.le_trans hc (Nat.mul_le_mul_right (N+1) hlen)
  constructor
  · intro i v hvi
    by_cases hi : i=0
    · exact hv v (by simpa [vs,SequentialNumericFive.st,hi] using hvi)
    · simp [SequentialNumericFive.st,hi] at hvi
  · intro i
    by_cases hi : i=0
    · subst i; exact hc'
    · simp [SequentialNumericFive.st,hi,Complexity.encS]

def capacity (ns : List CompileNode) (A M N n : Nat) : Nat := space ns A M N (frontCells A M N) n

theorem capacity_affine (ns : List CompileNode) (A M : Nat) :
    ∃ a b c, ∀ N n, capacity ns A M N n = a*n+b*N+c := by
  obtain ⟨a,b,c,h⟩ := space_affine ns A M
  refine ⟨a,b+2*(6+2*A+M),c+2*(6+2*A+M),?_⟩
  intro N n
  rw [capacity,h]
  simp only [frontCells,Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.mul_assoc]
  omega

theorem bounded_selected_runs (ns : List CompileNode) (src : MExp) (hs : ExprOK ns src)
    (hatom : SequentialAtomCodec.Atomic src) (x : List Char) (m p k : Nat) (E : CaptureEnv) (F : List Nat)
    {A M N : Nat} (hE : E.length ≤ A) (hvalid : SequentialSpanRecompute.ValidEnv x.length E)
    (hp : p ≤ x.length) (hn : x.length ≤ N) (hA : A ≤ N) (h2 : 2 ≤ N)
    (hm : m ≤ N) (hH : (exprPool ns).length ≤ N) (hk : k ≤ N)
    (hF : F.length ≤ M) (hFb : ∀ v ∈ F, v ≤ N) :
    FitsRuns (capacity ns A M N x.length) (program ns) (input ns x m p k src E F)
      (output x (atom x E src p) k F) (time ns A M x.length) := by
  have hvalid' : SequentialSpanRecompute.ValidEnv N E := by
    intro span hspan
    have hh := hvalid span hspan
    exact ⟨hh.1,by omega⟩
  have hi : exprId ns src ≤ N := Nat.le_trans List.idxOf_le_length hH
  exact selected_runs ns src hs hatom x m p k E F hE hvalid hp hn hA h2 hk hF hFb
    (input_bound ns src m p k E F hE hvalid' hm (by omega) hi hk hA hF hFb)

theorem compiled_selected (ns : List CompileNode) (src : MExp) (hs : ExprOK ns src)
    (hatom : SequentialAtomCodec.Atomic src) (x : List Char) (m p k : Nat) (E : CaptureEnv) (F : List Nat)
    {A M N : Nat} (hE : E.length ≤ A) (hvalid : SequentialSpanRecompute.ValidEnv x.length E)
    (hp : p ≤ x.length) (hn : x.length ≤ N) (hA : A ≤ N) (h2 : 2 ≤ N)
    (hm : m ≤ N) (hH : (exprPool ns).length ≤ N) (hk : k ≤ N)
    (hF : F.length ≤ M) (hFb : ∀ v ∈ F, v ≤ N) :
    Runs (LenOK (capacity ns A M N x.length)) (program ns).compile
      (encL (input ns x m p k src E F)) (encL (output x (atom x E src p) k F))
      (time ns A M x.length*ncost (capacity ns A M N x.length)) := by
  obtain ⟨t,ht,he⟩ := bounded_selected_runs ns src hs hatom x m p k E F hE hvalid hp hn hA h2 hm hH hk hF hFb
  obtain ⟨u,hu,h⟩ := nexec_compile (fun _ h => h) he
  exact ⟨u,Nat.le_trans hu (Nat.mul_le_mul_right _ ht),h⟩

theorem selected_tape (ns : List CompileNode) (src : MExp) (hs : ExprOK ns src)
    (hatom : SequentialAtomCodec.Atomic src) (x : List Char) (m p k : Nat) (E : CaptureEnv) (F : List Nat)
    {A M N : Nat} (hE : E.length ≤ A) (hvalid : SequentialSpanRecompute.ValidEnv x.length E)
    (hp : p ≤ x.length) (hn : x.length ≤ N) (hA : A ≤ N) (h2 : 2 ≤ N)
    (hm : m ≤ N) (hH : (exprPool ns).length ≤ N) (hk : k ≤ N)
    (hF : F.length ≤ M) (hFb : ∀ v ∈ F, v ≤ N) (τ : Tapes 16)
    (hτ : Rep (encL (input ns x m p k src E F)) τ) :
    ∃ t τ', Exec (TFits (capacity ns A M N x.length)) (program ns).compile.compile τ t (.cont τ') ∧
      Rep (encL (output x (atom x E src p) k F)) τ' := by
  obtain ⟨t,τ',_,he,hr⟩ := Complexity.BinaryWord.runs_tape
    (compiled_selected ns src hs hatom x m p k E F hE hvalid hp hn hA h2 hm hH hk hF hFb) τ hτ
  exact ⟨t,τ',he,hr⟩

end Shallot.MacroPeg.CBV.SequentialAtomSelect
