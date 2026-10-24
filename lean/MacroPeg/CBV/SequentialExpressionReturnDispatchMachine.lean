import MacroPeg.CBV.SequentialReturnFields

/-! Select every defined expression-result return from the actual frame tag
and saved syntax. This includes all result forms and scope restoration. -/
namespace Shallot.MacroPeg.CBV.SequentialExpressionReturnDispatchMachine
open Complexity SequentialCursorEditMachine
open SequentialSharedWords (Config CaptureEnv Runs initial)
open SequentialSharedStateCodec (encode)
open SequentialCaptureCopyMachine (withInput)

def branches (ns : List CBVtoCBN.CompileNode) (bound tag : Nat) : LProg 8 :=
  if tag=0 then SequentialRefReturnDispatchMachine.program ns .seq
  else if tag=1 then SequentialRefReturnDispatchMachine.program ns .alt
  else if tag=2 then SequentialEightTapeMachine.program (SequentialReturnPackedMachine.program ns .notP)
  else if tag=3 then SequentialRefReturnDispatchMachine.program ns .star
  else if tag=4 then SequentialArgHeadDispatchMachine.program ns bound
  else if tag=7 then SequentialScopePackedMachine.program
  else skipP 2

def program (ns : List CBVtoCBN.CompileNode) (bound : Nat) : LProg 8 :=
  SequentialReturnFields.program 4 (branches ns bound)

theorem branch_runs (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E : CaptureEnv)
    (r : Res) (f : SequentialSharedWords.Frame) (K : List SequentialSharedWords.Frame) (next : Config)
    (h : Runs g x (initial g x e) (SequentialReturnFields.before m E (.expr r) f K))
    (hs : SequentialSharedWords.step g x (SequentialReturnFields.before m E (.expr r) f K)=some next) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (branches (CBVtoCBN.compilerNodes g e) (SequentialStackCode.programBudget g e) (SequentialReturnFields.frameTag f))
      (withInput (encode (CBVtoCBN.compilerNodes g e) (SequentialReturnFields.before m E (.expr r) f K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) next) x) T := by
  cases f with
  | seq a => exact SequentialRefReturnDispatchMachine.transition_runs g x e .seq a m E 0 r K next h hs
  | alt a p => exact SequentialRefReturnDispatchMachine.transition_runs g x e .alt a m E p r K next h hs
  | star a p => exact SequentialRefReturnDispatchMachine.transition_runs g x e .star a m E p r K next h hs
  | argHead es p => exact SequentialArgHeadDispatchMachine.transition_runs g x e m E es p r K next h hs
  | notP p =>
    have he := Option.some.inj (hs.symm.trans (SequentialReturnPackedMachine.actual_step g x .notP m E p r K))
    rw [he]
    exact SequentialEightTapeMachine.return_runs g x e .notP m E p r K h
  | scope S =>
    have he := Option.some.inj (hs.symm.trans (SequentialScopePackedMachine.actual_step g x m E S (.expr r) K))
    rw [he]
    exact SequentialScopePackedMachine.transition_runs g x e m E S (.expr r) K h
  | argCons w => simp [SequentialReturnFields.before,SequentialSharedWords.step] at hs
  | call i => simp [SequentialReturnFields.before,SequentialSharedWords.step] at hs

/-- The saved frame is chosen from its actual control tag, then its syntax or
argument tail is selected from actual encoded fields. No frame is supplied. -/
theorem transition_runs (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E : CaptureEnv)
    (r : Res) (f : SequentialSharedWords.Frame) (K : List SequentialSharedWords.Frame) (next : Config)
    (h : Runs g x (initial g x e) (SequentialReturnFields.before m E (.expr r) f K))
    (hs : SequentialSharedWords.step g x (SequentialReturnFields.before m E (.expr r) f K)=some next) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (program (CBVtoCBN.compilerNodes g e) (SequentialStackCode.programBudget g e))
      (withInput (encode (CBVtoCBN.compilerNodes g e) (SequentialReturnFields.before m E (.expr r) f K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) next) x) T := by
  let ns := CBVtoCBN.compilerNodes g e
  let bound := SequentialStackCode.programBudget g e
  let L := withInput (encode ns (SequentialReturnFields.before m E (.expr r) f K)) x
  let target := withInput (encode ns next) x
  let B := (SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3
  obtain ⟨T,ht⟩ := branch_runs g x e m E r f K next h hs
  have hb : Complexity.Runs (LenOK B) (branches ns bound (SequentialReturnFields.frameTag f)) L target T := ht
  have hL : LenOK B L := by obtain ⟨t,ht,hx⟩ := hb; exact hx.q_start
  exact SequentialReturnFields.dispatch_runs (branches ns bound) (SequentialReturnFields.frameTag f)
    (SequentialReturnFields.frame_tag_bound f) [E.length,K.length+1,3,SequentialReturnPackedMachine.tag r]
    (SequentialReturnFields.payload ns f) (SequentialCursorEdit.blocks (SequentialSharedStateCodec.writeFrames ns K).control)
    L target (SequentialReturnFields.before_control ns x m E (.expr r) f K) rfl hL hb

theorem transition_tape (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E : CaptureEnv)
    (r : Res) (f : SequentialSharedWords.Frame) (K : List SequentialSharedWords.Frame) (next : Config)
    (h : Runs g x (initial g x e) (SequentialReturnFields.before m E (.expr r) f K))
    (hs : SequentialSharedWords.step g x (SequentialReturnFields.before m E (.expr r) f K)=some next)
    (tau : Tapes 8) (hrep : Rep (withInput (encode (CBVtoCBN.compilerNodes g e)
      (SequentialReturnFields.before m E (.expr r) f K)) x) tau) :
    ∃ t tau', Exec (TFits ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (program (CBVtoCBN.compilerNodes g e) (SequentialStackCode.programBudget g e)).compile tau t (.cont tau') ∧
      Rep (withInput (encode (CBVtoCBN.compilerNodes g e) next) x) tau' := by
  obtain ⟨T,hr⟩ := transition_runs g x e m E r f K next h hs
  exact tape_runs hr tau hrep

theorem finite_alphabet (ns : List CBVtoCBN.CompileNode) (bound : Nat) :
    ∃ E, 0x110001 ≤ E ∧ (program ns bound).compile.SymOK (E+4) := by
  obtain ⟨E,_hE,hc⟩ := LProg.exists_constOK (program ns bound)
  exact ⟨max E 0x110001,Nat.le_max_right _ _,compile_symOK _ _
    (LProg.ConstOK.mono (Nat.le_max_left E 0x110001) hc)⟩

end Shallot.MacroPeg.CBV.SequentialExpressionReturnDispatchMachine
