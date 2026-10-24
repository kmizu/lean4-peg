import MacroPeg.CBV.SequentialActiveDispatchMachine

/-! Read the actual argument-tail syntax retained by an argument-head frame.
The runtime result tag and captured words remain for the complete return code. -/
namespace Shallot.MacroPeg.CBV.SequentialArgHeadDispatchMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialControlEditMachine
open SequentialSharedWords (Config CaptureEnv Runs initial)
open SequentialSharedStateCodec (encode writeFrames)
open SequentialCaptureCopyMachine (withInput)
open SequentialReturnPackedMachine (tag)

def program (ns : List CBVtoCBN.CompileNode) (bound : Nat) : LProg 8 :=
  SequentialSyntaxListDispatchMachine.program ns 5 bound (SequentialArgHeadPackedMachine.program ns)

theorem transition_runs (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E : CaptureEnv)
    (es : List MExp) (p : Nat) (r : Res) (K : List SequentialSharedWords.Frame) (next : Config)
    (h : Runs g x (initial g x e) (SequentialArgHeadPackedMachine.before m E es p r K))
    (hs : SequentialSharedWords.step g x (SequentialArgHeadPackedMachine.before m E es p r K)=some next) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (program (CBVtoCBN.compilerNodes g e) (SequentialStackCode.programBudget g e))
      (withInput (encode (CBVtoCBN.compilerNodes g e) (SequentialArgHeadPackedMachine.before m E es p r K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) next) x) T := by
  let ns := CBVtoCBN.compilerNodes g e
  let L := withInput (encode ns (SequentialArgHeadPackedMachine.before m E es p r K)) x
  let target := withInput (encode ns next) x
  let B := (SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3
  have he := Option.some.inj (hs.symm.trans (SequentialArgHeadPackedMachine.actual_step g x m E es p r K))
  obtain ⟨T,ht⟩ := SequentialArgHeadPackedMachine.transition_runs g x e m E es p r K h
  rw [← he] at ht
  have hb : Complexity.Runs (LenOK B) (SequentialArgHeadPackedMachine.program ns es) L target T := ht
  have hL : LenOK B L := by obtain ⟨t,ht,hx⟩ := hb; exact hx.q_start
  have hok : SequentialStackPool.ArgsOK ns es := (SequentialSharedPool.reachable_ok g x e _ h).2
    (.argHead es p) (by simp [SequentialArgHeadPackedMachine.before])
  have hfit : sizeOf es ≤ SequentialStackCode.programBudget g e :=
    (SequentialSharedStateBound.reachable_fits g x e _ h).2 (.argHead es p)
      (by simp [SequentialArgHeadPackedMachine.before])
  have hlen := Nat.le_trans (SequentialSharedStateBound.exprs_length_size es) hfit
  have hctrl : L 2=blocks (writeFrames ns K).control ++ blocks ([E.length,K.length+1,3,tag r,4] ++
      [es.length] ++ es.map (SequentialStackCodec.exprId ns)) := by
    change withInput (encode ns (SequentialArgHeadPackedMachine.before m E es p r K)) x 2 = _
    rw [SequentialArgHeadPackedMachine.before_control]
    simp only [SequentialArgHeadPackedMachine.oldFields,SequentialArgumentsDispatchMachine.writeExprs_eq,
      blocks_append,blocks_cons,show blocks []=[] from rfl,List.nil_append,List.singleton_append,List.append_assoc]
  exact SequentialSyntaxListDispatchMachine.program_runs ns (SequentialStackCode.programBudget g e)
    (SequentialArgHeadPackedMachine.program ns) es [E.length,K.length+1,3,tag r,4]
    (blocks (writeFrames ns K).control) L target hlen hok.mem hctrl rfl hL hb

theorem finite_alphabet (ns : List CBVtoCBN.CompileNode) (bound : Nat) :
    ∃ E, 0x110001 ≤ E ∧ (program ns bound).compile.SymOK (E+4) := by
  obtain ⟨E,_hE,hc⟩ := LProg.exists_constOK (program ns bound)
  exact ⟨max E 0x110001,Nat.le_max_right _ _,compile_symOK _ _
    (LProg.ConstOK.mono (Nat.le_max_left E 0x110001) hc)⟩

end Shallot.MacroPeg.CBV.SequentialArgHeadDispatchMachine
