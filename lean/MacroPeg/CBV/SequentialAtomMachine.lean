import MacroPeg.CBV.SequentialInputPipeline

/-! All actual atomic stack transitions, including input-preserving character,
literal, and capture matching, between complete binary evaluator states. -/
namespace Shallot.MacroPeg.CBV.SequentialAtomMachine
open Complexity Complexity.BinaryWord SequentialStack SequentialStackCodec SequentialStackCodecBound
open SequentialStackBinary SequentialStackPayload CBVtoCBN
open SequentialFrontRead (locals frontSpace)
open SequentialInputHost (extend)

def before (m p : Nat) (E : CaptureEnv) (src : MExp) (K : List SequentialStack.Frame) : Config :=
  ⟨.expr m E src p,K⟩
def after (x : List Char) (p : Nat) (E : CaptureEnv) (src : MExp) (K : List SequentialStack.Frame) : Config :=
  ⟨.value (.expr (atom x E src p)),K⟩

def program (ns : List CompileNode) : LProg 20 := SequentialInputPipeline.program
  ((SequentialAtomSelect.program ns).compile.rename SequentialInputHost.atomReg)

noncomputable def space (g : MGrammar) (x : List Char) (e : MExp) (c : Config) : Nat :=
  frontSpace g x e c + (19+9*arityBudget g)*(numberBound g x e+1) +
    SequentialAtomSelect.capacity (compilerNodes g e) (arityBudget g) (6+3*arityBudget g)
      (numberBound g x e) x.length + numberBound g x e+3

theorem transition_runs (g : MGrammar) (x : List Char) (e : MExp) (m p : Nat) (E : CaptureEnv)
    (src : MExp) (hatom : SequentialAtomCodec.Atomic src) (K : List SequentialStack.Frame)
    (h : SequentialStack.Runs g x (initial g x e) (before m p E src K)) :
    ∃ T, Complexity.Runs (LenOK (space g x e (before m p E src K))) (program (compilerNodes g e))
      (extend (SequentialFieldFetch.start (width g x e) (encode (compilerNodes g e) (before m p E src K)) [] [] 0 [])
        (Complexity.encS (SequentialInputRead.codes x)))
      (extend (SequentialFieldFetch.start (width g x e) (encode (compilerNodes g e) (after x p E src K)) [] [] 0 [])
        (Complexity.encS (SequentialInputRead.codes x))) T := by
  let ns := compilerNodes g e
  let A := arityBudget g
  let N := numberBound g x e
  let c := before m p E src K
  let d := after x p E src K
  let lc := after x p E src (K.take 1)
  let B := space g x e c
  let F := SequentialFront.suffixCode ns (K.take 1)
  let k := (K.take 1).length+(K.drop 1).length
  let P := SequentialStructuralEntry.inputFields m p (exprId ns src) k E F
  let P' := SequentialAtomCodec.outputFields (atom x E src p) k F
  let S := SequentialFront.suffixCode ns (SequentialFront.tail c)
  have hP : SequentialFront.prefixCode ns (SequentialFront.tail c) (SequentialFront.front c) = P :=
    SequentialAtomCodec.input_prefix _ m p E src _ _
  have hP' : SequentialFront.prefixCode ns (SequentialFront.tail c) lc = P' :=
    SequentialAtomCodec.output_prefix _ (atom x E src p) _ _
  have hs : step g x c = some d := SequentialAtomCodec.original_step g x m p E src hatom K
  have hsl : step g x (SequentialFront.front c) = some lc :=
    SequentialAtomCodec.original_step g x m p E src hatom (K.take 1)
  have hd : d = SequentialFront.attach (SequentialFront.tail c) lc := by cases K <;> rfl
  have hcode : encode ns c = P ++ S := by
    simpa only [hP] using SequentialFront.encode_front ns c
  have hcode' : encode ns d = P' ++ S := by rw [hd,SequentialFront.encode_attach,hP']
  have hb : ∀ v ∈ P, v ≤ N := by
    intro v hv
    apply reachable_numbers g x e c h v
    rw [hcode]
    exact List.mem_append_left _ hv
  have hm : m ≤ N := hb m (by simp [P,SequentialStructuralEntry.inputFields])
  have hk : k ≤ N := hb k (by simp [P,SequentialStructuralEntry.inputFields])
  have hFb : ∀ v ∈ F, v ≤ N := by
    intro v hv
    apply hb v
    simp only [P,SequentialStructuralEntry.inputFields,List.mem_append]
    exact Or.inr hv
  have hpool : SequentialStackPool.ExprOK ns src := (SequentialStackPool.reachable_ok g x e c h).1
  have htyped : EnvOK x.length A E ∧ p ≤ x.length := by
    obtain ⟨kind,ht,hK⟩ := reachable_typed g x e c h
    change TaskTyped x.length A (SequentialClock.positionClock g x.length) (.expr m E src p) kind at ht
    cases ht with | expr _ _ _ _ hm hE hp => exact ⟨hE,hp⟩
  have hF : F.length ≤ 6+3*A := by
    obtain ⟨kind,ht,hK⟩ := reachable_typed g x e c h
    have hframes := frames_length ns hK
    cases K with
    | nil => simp [F,SequentialFront.suffixCode]
    | cons f K =>
      have hh := hframes f (by simp [c,before])
      simpa [F,SequentialFront.suffixCode] using hh
  have hn : x.length ≤ N := by unfold N numberBound; omega
  have hA : A ≤ N := by unfold A N numberBound; omega
  have h2 : 2 ≤ N := by unfold N numberBound; omega
  have hH : (SequentialStackPool.exprPool ns).length ≤ N := by unfold ns N numberBound; omega
  have hfront : frontSpace g x e c ≤ B := by unfold B space; omega
  have hcap : SequentialAtomSelect.capacity ns A (6+3*A) N x.length ≤ B := by unfold B space ns A N; omega
  have hnum : N+3 ≤ B := by unfold B space N; omega
  have hraw : SequentialInputRead.space x.length ≤ B := by
    unfold SequentialAtomSelect.capacity SequentialAtomSelect.space at hcap
    omega
  have hX : (Complexity.encS (SequentialInputRead.codes x)).length+2 ≤ B := by
    have hh := SequentialInputRead.encoded_length x
    unfold SequentialInputRead.space at hraw
    omega
  have hlen : P'.length ≤ 19+9*A := by
    obtain ⟨other,he,_,_,hlen⟩ := SequentialFront.reachable_step_prefix g x e c d h hs
    have heq : other=lc := Option.some.inj (he.symm.trans hsl)
    subst other
    rwa [hP'] at hlen
  have hwidth : width g x e ≤ N+1 := by
    have hh := Nat.log2_le_self N
    change N.log2+1 ≤ N+1
    omega
  have hprod := Nat.mul_le_mul hlen hwidth
  have hsource : (encodeBits ns (width g x e) c).length+2 ≤ frontSpace g x e c := by
    change (encodeBits (compilerNodes g e) (width g x e) c).length+2 ≤ frontSpace g x e c
    unfold frontSpace
    omega
  have hfinal : (encodeBits ns (width g x e) d).length+2 ≤ B := by
    simp only [encodeBits,hcode,hcode',SequentialStackBinary.pack_length,List.length_append,Nat.add_mul] at hsource ⊢
    have hcap' : frontSpace g x e c+(19+9*A)*(N+1) ≤ B := by unfold B space A N; omega
    omega
  apply SequentialInputPipeline.transition_runs g x e c d lc h hs hd
    ((SequentialAtomSelect.program ns).compile.rename SequentialInputHost.atomReg)
    (Complexity.encS (SequentialInputRead.codes x)) B hfront hnum hX hfinal
  intro held hR
  change LenOK B (extend (SequentialFieldFetch.start (width g x e) [] (SequentialStackBinary.pack (width g x e) S)
    (locals (SequentialFront.prefixCode ns (SequentialFront.tail c) (SequentialFront.front c))) held [])
    (Complexity.encS (SequentialInputRead.codes x))) at hR
  rw [hP] at hR
  have hc := SequentialAtomSelect.compiled_selected ns src hpool hatom x m p k E F htyped.1.2 htyped.1.1
    htyped.2 hn hA h2 hm hH hk hF hFb
  have hc' := hc.weaken (fun _ hh i => Nat.le_trans (hh i) hcap)
  have hr := SequentialInputHost.atom_runs (SequentialAtomSelect.program ns) (SequentialInputRead.codes x)
    P P' (width g x e) held (SequentialStackBinary.pack (width g x e) S) hc'
    hR
  change ∃ T, Complexity.Runs (LenOK B) _
    (extend (SequentialFieldFetch.start (width g x e) [] (SequentialStackBinary.pack (width g x e) S)
      (locals (SequentialFront.prefixCode ns (SequentialFront.tail c) (SequentialFront.front c))) held [])
      (Complexity.encS (SequentialInputRead.codes x)))
    (extend (SequentialFieldFetch.start (width g x e) [] (SequentialStackBinary.pack (width g x e) S)
      (locals (SequentialFront.prefixCode ns (SequentialFront.tail c) lc)) held [])
      (Complexity.encS (SequentialInputRead.codes x))) T
  rw [hP,hP']
  exact ⟨_,hr⟩

theorem transition_tape (g : MGrammar) (x : List Char) (e : MExp) (m p : Nat) (E : CaptureEnv)
    (src : MExp) (hatom : SequentialAtomCodec.Atomic src) (K : List SequentialStack.Frame)
    (h : SequentialStack.Runs g x (initial g x e) (before m p E src K)) (τ : Tapes 20)
    (hτ : Rep (extend (SequentialFieldFetch.start (width g x e)
      (encode (compilerNodes g e) (before m p E src K)) [] [] 0 [])
      (Complexity.encS (SequentialInputRead.codes x))) τ) :
    ∃ t τ', Exec (TFits (space g x e (before m p E src K))) (program (compilerNodes g e)).compile τ t (.cont τ') ∧
      Rep (extend (SequentialFieldFetch.start (width g x e)
        (encode (compilerNodes g e) (after x p E src K)) [] [] 0 [])
        (Complexity.encS (SequentialInputRead.codes x))) τ' := by
  obtain ⟨_,hr⟩ := transition_runs g x e m p E src hatom K h
  obtain ⟨t,τ',_,he,hr'⟩ := runs_tape hr τ hτ
  exact ⟨t,τ',he,hr'⟩

theorem space_eq (g : MGrammar) (e : MExp) :
    ∃ a b d, ∀ x c, space g x e c = frontSpace g x e c+a*x.length+b*numberBound g x e+d := by
  obtain ⟨a,b,d,hcap⟩ := SequentialAtomSelect.capacity_affine (compilerNodes g e) (arityBudget g) (6+3*arityBudget g)
  refine ⟨a,b+(19+9*arityBudget g)+1,d+(19+9*arityBudget g)+3,?_⟩
  intro x c
  unfold space
  rw [hcap]
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one]
  omega

/-- The entire parser/atom/writer transition has the same input-size order as
the bounded binary state: a linear term plus its n log n storage term. -/
theorem space_bound (g : MGrammar) (e : MExp) :
    ∃ C, ∀ x c, SequentialStack.Runs g x (initial g x e) c →
      space g x e c ≤ C*(x.length+1) + (cellCoefficient g e*(x.length+1))*
        ((x.length+1).log2+(numberCoefficient g e).log2+2) := by
  obtain ⟨a,b,d,heq⟩ := space_eq g e
  let F := (13+6*arityBudget g+4)*(numberCoefficient g e+1)+8
  refine ⟨F+(a+b*numberCoefficient g e+d),?_⟩
  intro x c hc
  have hf := SequentialFrontRead.frontSpace_bound g x e c hc
  have hn := numberBound_linear g x e
  have hb := Nat.mul_le_mul_left b hn
  have ha : a*x.length ≤ a*(x.length+1) := Nat.mul_le_mul_left a (by omega)
  have hd : d ≤ d*(x.length+1) := Nat.le_mul_of_pos_right _ (by omega)
  have hnum : a*x.length+b*numberBound g x e+d ≤ (a+b*numberCoefficient g e+d)*(x.length+1) := by
    rw [Nat.add_mul,Nat.add_mul,Nat.mul_assoc]
    omega
  rw [heq]
  rw [Nat.add_mul]
  change frontSpace g x e c+a*x.length+b*numberBound g x e+d ≤
    F*(x.length+1)+(a+b*numberCoefficient g e+d)*(x.length+1)+_
  change frontSpace g x e c ≤ F*(x.length+1)+_ at hf
  omega

end Shallot.MacroPeg.CBV.SequentialAtomMachine
