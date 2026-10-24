import MacroPeg.CBV.SequentialArgumentsReturnDispatchMachine

/-! A single fixed eight-tape program for every defined reachable Seq step.
Task kind, result form, frame kind, rule id, and syntax payloads are all read
from the actual source streams and restored before their instruction runs. -/
namespace Shallot.MacroPeg.CBV.SequentialStepDispatchMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialControlEditMachine
open SequentialSharedWords (Config CaptureEnv Task Runs initial)
open SequentialSharedStateCodec (encode write writeTask writeFrames Input)
open SequentialCaptureCopyMachine (withInput)

def taskTag : Task → Nat
  | .expr _ _ => 0
  | .args _ _ => 1
  | .query _ _ _ => 2
  | .value (.expr _) => 3
  | .value (.args _) => 4

def payload (ns : List CBVtoCBN.CompileNode) (task : Task) : List Nat := (writeTask ns task).control.tail

theorem task_fields (ns : List CBVtoCBN.CompileNode) (task : Task) :
    (writeTask ns task).control=taskTag task :: payload ns task := by
  cases task with
  | expr a p => rfl
  | args es p => rfl
  | query i W p => rfl
  | value v => cases v with
    | expr r => cases r with
      | none => rfl
      | some v => cases v <;> rfl
    | args r => cases r with
      | none => rfl
      | some v => cases v with
        | none => rfl
        | some Wq => cases Wq; rfl

theorem task_tag_bound (task : Task) : taskTag task ≤ 4 := by
  cases task with
  | expr a p => simp [taskTag]
  | args es p => simp [taskTag]
  | query i W p => simp [taskTag]
  | value v => cases v <;> simp [taskTag]

def branches (ns : List CBVtoCBN.CompileNode) (g : MGrammar) (bound tag : Nat) : LProg 8 :=
  if tag=3 then SequentialExpressionReturnDispatchMachine.program ns bound
  else if tag=4 then SequentialArgumentsReturnDispatchMachine.program g.rules.length
  else SequentialActiveDispatchMachine.program ns g bound

def program (ns : List CBVtoCBN.CompileNode) (g : MGrammar) (bound : Nat) : LProg 8 :=
  SequentialTagDispatchMachine.program 2 1 2 4 (branches ns g bound)

theorem control_fields (ns : List CBVtoCBN.CompileNode) (x : List Char) (c : Config) :
    withInput (encode ns c) x 2=blocks (writeFrames ns c.stack).control ++
      blocks (taskTag c.task :: payload ns c.task) ++ blocks [c.env.length,c.stack.length] := by
  change SequentialCursorEntryMachine.layout (encode ns c) 2 = _
  rw [SequentialAnyPackedMachine.layout_control]
  have he : (write ns c).control=[c.env.length,c.stack.length] ++ (writeTask ns c.task).control ++
      (writeFrames ns c.stack).control := by
    simp [write,Input.append,SequentialSharedStateCodec.putControl,SequentialSharedStateCodec.putWords]
  rw [he,task_fields,blocks_append,blocks_append]
  simp only [List.append_assoc]

theorem branch_runs (g : MGrammar) (x : List Char) (e : MExp) (c next : Config)
    (h : Runs g x (initial g x e) c) (hs : SequentialSharedWords.step g x c=some next) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (branches (CBVtoCBN.compilerNodes g e) g (SequentialStackCode.programBudget g e) (taskTag c.task))
      (withInput (encode (CBVtoCBN.compilerNodes g e) c) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) next) x) T := by
  cases c with
  | mk m task E K => cases task with
    | expr a p => exact SequentialActiveDispatchMachine.transition_runs g x e _ next h hs trivial
    | args es p => exact SequentialActiveDispatchMachine.transition_runs g x e _ next h hs trivial
    | query i W p => exact SequentialActiveDispatchMachine.transition_runs g x e _ next h hs trivial
    | value v => cases K with
      | nil => simp [SequentialSharedWords.step] at hs
      | cons f K => cases v with
        | expr r => exact SequentialExpressionReturnDispatchMachine.transition_runs g x e m E r f K next h hs
        | args r => exact SequentialArgumentsReturnDispatchMachine.transition_runs g x e m E r f K next h hs

/-- Complete fixed-program simulation of every defined transition from an
initialized reachable state, including every expression and argument return. -/
theorem transition_runs (g : MGrammar) (x : List Char) (e : MExp) (c next : Config)
    (h : Runs g x (initial g x e) c) (hs : SequentialSharedWords.step g x c=some next) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (program (CBVtoCBN.compilerNodes g e) g (SequentialStackCode.programBudget g e))
      (withInput (encode (CBVtoCBN.compilerNodes g e) c) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) next) x) T := by
  let ns := CBVtoCBN.compilerNodes g e
  let bound := SequentialStackCode.programBudget g e
  let L := withInput (encode ns c) x
  let target := withInput (encode ns next) x
  let B := (SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3
  obtain ⟨T,ht⟩ := branch_runs g x e c next h hs
  have hb : Complexity.Runs (LenOK B) (branches ns g bound (taskTag c.task)) L target T := ht
  have hL : LenOK B L := by obtain ⟨t,ht,hx⟩ := hb; exact hx.q_start
  let C := (blocks (writeFrames ns c.stack).control ++ blocks (payload ns c.task)) ++ [0]
  have hsrc : L 2=C ++ unary (taskTag c.task) ++ blocks [c.env.length,c.stack.length] := by
    rw [show L 2=withInput (encode ns c) x 2 from rfl,control_fields,blocks_cons]
    simp only [C,List.append_assoc]
  exact SequentialTagDispatchMachine.dispatch_runs (src := (2 : Fin 8)) (tmp := 1) (by decide)
    [c.env.length,c.stack.length] 4 (taskTag c.task) (task_tag_bound c.task) C (branches ns g bound)
    L target hsrc (by rw [lastSym_append]; rfl) rfl hL hb

theorem transition_tape (g : MGrammar) (x : List Char) (e : MExp) (c next : Config)
    (h : Runs g x (initial g x e) c) (hs : SequentialSharedWords.step g x c=some next)
    (tau : Tapes 8) (hrep : Rep (withInput (encode (CBVtoCBN.compilerNodes g e) c) x) tau) :
    ∃ t tau', Exec (TFits ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (program (CBVtoCBN.compilerNodes g e) g (SequentialStackCode.programBudget g e)).compile tau t (.cont tau') ∧
      Rep (withInput (encode (CBVtoCBN.compilerNodes g e) next) x) tau' := by
  obtain ⟨T,hr⟩ := transition_runs g x e c next h hs
  exact tape_runs hr tau hrep

theorem finite_alphabet (ns : List CBVtoCBN.CompileNode) (g : MGrammar) (bound : Nat) :
    ∃ E, 0x110001 ≤ E ∧ (program ns g bound).compile.SymOK (E+4) := by
  obtain ⟨E,_hE,hc⟩ := LProg.exists_constOK (program ns g bound)
  exact ⟨max E 0x110001,Nat.le_max_right _ _,compile_symOK _ _
    (LProg.ConstOK.mono (Nat.le_max_left E 0x110001) hc)⟩

end Shallot.MacroPeg.CBV.SequentialStepDispatchMachine
