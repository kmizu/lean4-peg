import MacroPeg.CBV.SequentialReadResult
import MacroPeg.CBV.SequentialSimpleAtom

/-! All atomic constructors share the same original-input/environment layout
and return the ordinary encoded value task. -/
namespace Shallot.MacroPeg.CBV.SequentialAtomBranch
open Complexity Complexity.NBoundedTransfer SequentialStack SequentialStackCodec
open SequentialNumericFive (st)
open SequentialInputRead (codes)

/-- The input is outside the registers used by local environment/codec work. -/
def background (x : List Char) : Lists 13 := fun i => if i=0 then codes x else []

private theorem pack (x : List Char) (D R H Q : List Nat) :
    (st D R H Q []).frame SequentialAtomResult.reg (background x) =
      SequentialAtomResult.state (codes x) [] Q H R D := by
  funext j
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 := by omega
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | simpa [SequentialAtomResult.reg,SequentialAtomResult.state] using Lists.frame_get
        SequentialAtomResult.reg_injective (background x) (st D R H Q []) 0
    | simpa [SequentialAtomResult.reg,SequentialAtomResult.state] using Lists.frame_get
        SequentialAtomResult.reg_injective (background x) (st D R H Q []) 1
    | simpa [SequentialAtomResult.reg,SequentialAtomResult.state] using Lists.frame_get
        SequentialAtomResult.reg_injective (background x) (st D R H Q []) 2
    | simpa [SequentialAtomResult.reg,SequentialAtomResult.state] using Lists.frame_get
        SequentialAtomResult.reg_injective (background x) (st D R H Q []) 3
    | simpa [SequentialAtomResult.reg,SequentialAtomResult.state] using Lists.frame_get
        SequentialAtomResult.reg_injective (background x) (st D R H Q []) 4
    | exact (Lists.frame_outside (ρ := SequentialAtomResult.reg) _ _ _ (by decide)).trans (by rfl)

private theorem input_pack (x : List Char) (p k : Nat) (E : CaptureEnv) (F : List Nat) :
    (st [] (writeEnv E ++ [k] ++ F).reverse [] [p] []).frame SequentialAtomResult.reg (background x) =
      SequentialParamMachine.input x p E ([k] ++ F) := by
  rw [pack]
  funext i
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try rfl
  simp [SequentialAtomResult.state,SequentialParamMachine.input,SequentialParamMachine.host,List.append_assoc]

def localTime (A M : Nat) : Nat := 12*A+3*M+40
def localSpace (A M N e : Nat) : Nat := e+grow N (localTime A M)+2

private theorem background_fits (x : List Char) {B : Nat} (hB : SequentialInputRead.space x.length ≤ B) :
    NFits B (background x) := by
  have hh := SequentialInputRead.encoded_length x
  refine ⟨by unfold SequentialInputRead.space at hB; omega,fun i => ?_⟩
  by_cases hi : i=0
  · subst i
    change (Complexity.encS (codes x)).length+2 ≤ B
    unfold SequentialInputRead.space at hB
    omega
  · simp [background,hi,Complexity.encS]
    unfold SequentialInputRead.space at hB
    omega

private theorem local_runs (prog : NProg 5) (L L' : Lists 5) (T : Nat) (x : List Char)
    {A M N e B : Nat} (hr : NRuns prog L L' T) (hT : T ≤ localTime A M)
    (hL : Bnd N e L) (hB : localSpace A M N e ≤ B) (hinput : SequentialInputRead.space x.length ≤ B) :
    FitsRuns B (prog.rename SequentialAtomResult.reg SequentialAtomResult.reg_injective)
      (L.frame SequentialAtomResult.reg (background x)) (L'.frame SequentialAtomResult.reg (background x))
      (localTime A M) := by
  obtain ⟨t,ht,he⟩ := hr
  have ht' : t ≤ localTime A M := Nat.le_trans ht hT
  have hx := (nexec_space he N e hL).2 B (by
    have hh := grow_mono (m := N) ht'
    unfold localSpace at hB
    omega)
  exact (show FitsRuns B prog L L' (localTime A M) from ⟨t,ht',hx⟩).rename_frame
    SequentialAtomResult.reg_injective (background x) (background_fits x hinput)

def discard : NProg 13 := SequentialSimpleAtom.drainEnv.rename SequentialAtomResult.reg SequentialAtomResult.reg_injective

theorem discard_runs (x : List Char) (p k : Nat) (E : CaptureEnv) (F : List Nat) {A M N e B : Nat}
    (hE : E.length ≤ A)
    (hL : Bnd N e (st [] (writeEnv E ++ [k] ++ F).reverse [] [p] []))
    (hB : localSpace A M N e ≤ B) (hinput : SequentialInputRead.space x.length ≤ B) :
    FitsRuns B discard (SequentialParamMachine.input x p E ([k] ++ F))
      (SequentialAtomResult.input (codes x) [] p false ([k] ++ F).reverse) (localTime A M) := by
  have hh := local_runs _ _ _ _ x (SequentialSimpleAtom.drain_runs E p k F)
    (show 12*E.length+5 ≤ localTime A M by unfold localTime; omega) hL hB hinput
  rw [input_pack,pack] at hh
  exact hh

def character (kind : SequentialCodeTest.Kind) : NProg 13 :=
  .seq discard (SequentialReadResult.program (SequentialCharacterMachine.program kind))
def literal (w : List Char) : NProg 13 := .seq discard (SequentialReadResult.program (SequentialLiteralRead.program w))
def simple (mode : SequentialSimpleAtom.Mode) : NProg 13 :=
  (SequentialSimpleAtom.body mode).rename SequentialAtomResult.reg SequentialAtomResult.reg_injective

def program : MExp → NProg 13
  | .any => character .any
  | .chr c => character (.chr c)
  | .range lo hi => character (.range lo hi)
  | .lit w => literal w
  | .param i => SequentialParamResult.program i
  | .eps | .dbg _ | .lam _ _ => simple .success
  | .callParam _ _ => simple .failure
  | .invoke _ _ _ => simple .undefined
  | _ => .halt false

def reserve (src : MExp) (A M N n : Nat) : Nat :=
  match src with
  | .any => SequentialReadResult.characterSpace .any M N n
  | .chr c => SequentialReadResult.characterSpace (.chr c) M N n
  | .range lo hi => SequentialReadResult.characterSpace (.range lo hi) M N n
  | .lit w => SequentialReadResult.literalSpace w M N n
  | .param _ => SequentialParamResult.capacity A M N n
  | _ => 0

def time (src : MExp) (A M n : Nat) : Nat :=
  match src with
  | .any => localTime A M+8*n+SequentialCodeTest.cost .any+13+3*M+36
  | .chr c => localTime A M+8*n+SequentialCodeTest.cost (.chr c)+13+3*M+36
  | .range lo hi => localTime A M+8*n+SequentialCodeTest.cost (.range lo hi)+13+3*M+36
  | .lit w => localTime A M+SequentialLiteralRead.time w n+3*M+36
  | .param _ => 8*A+10+1+(4*n+6+n*(16*n+4*2^32+31))+3*M+36
  | _ => localTime A M

private theorem character_runs (kind : SequentialCodeTest.Kind) (x : List Char) (p k : Nat)
    (E : CaptureEnv) (F : List Nat) {A M N e B : Nat}
    (hE : E.length ≤ A) (hp : p ≤ x.length) (hn : x.length ≤ N) (h2 : 2 ≤ N)
    (hk : k ≤ N) (hF : F.length ≤ M) (hFb : ∀ v ∈ F, v ≤ N)
    (hL : Bnd N e (st [] (writeEnv E ++ [k] ++ F).reverse [] [p] []))
    (hB : localSpace A M N e ≤ B) (hinput : SequentialInputRead.space x.length ≤ B)
    (hr : SequentialReadResult.characterSpace kind M N x.length ≤ B) :
    FitsRuns B (character kind) (SequentialParamMachine.input x p E ([k] ++ F))
      (SequentialAtomResult.output (codes x) (SequentialAtomCodec.outputFields (atom x E kind.exp p) k F))
      (localTime A M+8*x.length+SequentialCodeTest.cost kind+13+3*M+36) := by
  have hd := discard_runs x p k E F hE hL hB hinput
  have hc := (SequentialReadResult.character_runs kind x E p k F hp hn h2 hk hF hFb).mono_space hr
  obtain ⟨t,ht,he⟩ := hd.seq hc
  exact ⟨t,by omega,he⟩

private theorem literal_runs (w : List Char) (x : List Char) (p k : Nat)
    (E : CaptureEnv) (F : List Nat) {A M N e B : Nat}
    (hE : E.length ≤ A) (hp : p ≤ x.length) (hn : x.length ≤ N) (h2 : 2 ≤ N)
    (hk : k ≤ N) (hF : F.length ≤ M) (hFb : ∀ v ∈ F, v ≤ N)
    (hL : Bnd N e (st [] (writeEnv E ++ [k] ++ F).reverse [] [p] []))
    (hB : localSpace A M N e ≤ B) (hinput : SequentialInputRead.space x.length ≤ B)
    (hr : SequentialReadResult.literalSpace w M N x.length ≤ B) :
    FitsRuns B (literal w) (SequentialParamMachine.input x p E ([k] ++ F))
      (SequentialAtomResult.output (codes x) (SequentialAtomCodec.outputFields (atom x E (.lit w) p) k F))
      (localTime A M+SequentialLiteralRead.time w x.length+3*M+36) := by
  have hd := discard_runs x p k E F hE hL hB hinput
  obtain ⟨t,ht,he⟩ := hd.seq ((SequentialReadResult.literal_runs w x E p k F hp hn h2 hk hF hFb).mono_space hr)
  exact ⟨t,by omega,he⟩

private theorem simple_runs (mode : SequentialSimpleAtom.Mode) (x : List Char) (p k : Nat)
    (E : CaptureEnv) (F : List Nat) {A M N e B : Nat} (hE : E.length ≤ A) (hF : F.length ≤ M)
    (hL : Bnd N e (st [] (writeEnv E ++ [k] ++ F).reverse [] [p] []))
    (hB : localSpace A M N e ≤ B) (hinput : SequentialInputRead.space x.length ≤ B) :
    FitsRuns B (simple mode) (SequentialParamMachine.input x p E ([k] ++ F))
      (SequentialAtomResult.output (codes x) (SequentialAtomCodec.outputFields (mode.result p) k F)) (localTime A M) := by
  have hh := local_runs _ _ _ _ x (SequentialSimpleAtom.body_runs mode E p k F)
    (show 12*E.length+3*F.length+40 ≤ localTime A M by unfold localTime; omega) hL hB hinput
  rw [input_pack,pack] at hh
  exact hh

theorem branch_runs (src : MExp) (hatom : SequentialAtomCodec.Atomic src) (x : List Char)
    (p k : Nat) (E : CaptureEnv) (F : List Nat) {A M N e B : Nat}
    (hE : E.length ≤ A) (hvalid : SequentialSpanRecompute.ValidEnv x.length E)
    (hp : p ≤ x.length) (hn : x.length ≤ N) (hA : A ≤ N) (h2 : 2 ≤ N)
    (hk : k ≤ N) (hF : F.length ≤ M) (hFb : ∀ v ∈ F, v ≤ N)
    (hL : Bnd N e (st [] (writeEnv E ++ [k] ++ F).reverse [] [p] []))
    (hB : localSpace A M N e ≤ B) (hinput : SequentialInputRead.space x.length ≤ B)
    (hr : reserve src A M N x.length ≤ B) :
    FitsRuns B (program src) (SequentialParamMachine.input x p E ([k] ++ F))
      (SequentialAtomResult.output (codes x) (SequentialAtomCodec.outputFields (atom x E src p) k F))
      (time src A M x.length) := by
  cases src with
  | any => exact character_runs .any x p k E F hE hp hn h2 hk hF hFb hL hB hinput hr
  | chr c => exact character_runs (.chr c) x p k E F hE hp hn h2 hk hF hFb hL hB hinput hr
  | range lo hi => exact character_runs (.range lo hi) x p k E F hE hp hn h2 hk hF hFb hL hB hinput hr
  | lit w => exact literal_runs w x p k E F hE hp hn h2 hk hF hFb hL hB hinput hr
  | param i => exact (SequentialParamResult.param_runs i x p k E F hE hvalid hp hn hA h2 hk hF hFb).mono_space hr
  | eps => exact simple_runs .success x p k E F hE hF hL hB hinput
  | dbg _ => exact simple_runs .success x p k E F hE hF hL hB hinput
  | lam _ _ => exact simple_runs .success x p k E F hE hF hL hB hinput
  | callParam _ _ => exact simple_runs .failure x p k E F hE hF hL hB hinput
  | invoke _ _ _ => exact simple_runs .undefined x p k E F hE hF hL hB hinput
  | seq _ _ | alt _ _ | notP _ | star _ | call _ _ => contradiction

private theorem character_affine (kind : SequentialCodeTest.Kind) (M : Nat) :
    ∃ a b c, ∀ N n, SequentialReadResult.characterSpace kind M N n = a*n+b*N+c := by
  refine ⟨2^32+2,(M+3)+(3*M+30),3+SequentialCodeTest.capacity kind+((M+3)+(3*M+30)*(3*M+31)+2),?_⟩
  intro N n
  exact SequentialReadResult.characterSpace_linear kind M N n

theorem reserve_affine (src : MExp) (A M : Nat) :
    ∃ a b c, ∀ N n, reserve src A M N n = a*n+b*N+c := by
  cases src with
  | any => exact character_affine .any M
  | chr c => exact character_affine (.chr c) M
  | range lo hi => exact character_affine (.range lo hi) M
  | lit w =>
    refine ⟨2^32+2,(M+3)+(3*M+30),3+SequentialLiteralRead.reserve w+((M+3)+(3*M+30)*(3*M+31)+2),?_⟩
    intro N n
    exact SequentialReadResult.literalSpace_linear w M N n
  | param _ =>
    refine ⟨2^32+2,((1+2*A+(M+1))+(8*A+10))+((M+3)+(3*M+30)),
      (1+2*A+(M+1))+(8*A+10)*((8*A+10)+1)+5+((M+3)+(3*M+30)*(3*M+31)+2),?_⟩
    intro N n
    exact SequentialParamResult.capacity_linear A M N n
  | eps | dbg _ | lam _ _ | callParam _ _ | invoke _ _ _ | seq _ _ | alt _ _ | notP _ | star _ | call _ _ =>
    exact ⟨0,0,0,by intro N n; simp [reserve]⟩

end Shallot.MacroPeg.CBV.SequentialAtomBranch
