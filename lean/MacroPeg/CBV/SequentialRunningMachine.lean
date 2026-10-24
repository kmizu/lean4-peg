import MacroPeg.CBV.SequentialFieldPresenceMachine

/-! Decide whether a packed state still has work. Tape 7 receives one flag;
all control, data, input, and other scratch tapes are preserved. -/
namespace Shallot.MacroPeg.CBV.SequentialRunningMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialControlEditMachine
open SequentialSharedWords (Config)
open SequentialSharedStateCodec (encode writeTask writeFrames)
open SequentialCaptureCopyMachine (withInput)
open SequentialStepDispatchMachine (taskTag payload)

def running (c : Config) : Bool := !(c.stack.isEmpty && decide (3 ≤ taskTag c.task))
def flag (c : Config) : Nat := if running c then 1 else 0

def byKind (kind : Nat) : LProg 8 := .push 7 (if kind<3 then 1 else 0)
def emptyStack : LProg 8 := SequentialTagDispatchMachine.program 2 1 2 4 byKind
def program : LProg 8 := SequentialFieldPresenceMachine.program 1 (.push 7 1) emptyStack

theorem step_running (g : MGrammar) (x : List Char) (c next : Config)
    (hs : SequentialSharedWords.step g x c=some next) : running c=true := by
  cases c with
  | mk m task E K => cases K with
    | cons f K => simp [running]
    | nil => cases task with
      | expr a p => simp [running,taskTag]
      | args es p => simp [running,taskTag]
      | query i W p => simp [running,taskTag]
      | value v => simp [SequentialSharedWords.step] at hs

theorem flag_fits (c : Config) (x : List Char) (ns : List CBVtoCBN.CompileNode) {B : Nat}
    (hL : LenOK B (withInput (encode ns c) x)) (hB : 3 ≤ B) :
    LenOK B ((withInput (encode ns c) x).set 7 [flag c]) :=
  lenOK_set hL 7 (by simpa using hB)

theorem running_runs (ns : List CBVtoCBN.CompileNode) (x : List Char) (c : Config) {B : Nat}
    (hL : LenOK B (withInput (encode ns c) x)) (hB : 3 ≤ B) :
    ∃ T, Runs (LenOK B) program (withInput (encode ns c) x)
      ((withInput (encode ns c) x).set 7 [flag c]) T := by
  let L := withInput (encode ns c) x
  have h7 : L 7=[] := rfl
  have hp (value : Nat) : Runs (LenOK B) (.push 7 value) L (L.set 7 [value]) 1 := by
    have hr : Runs (LenOK B) (.push 7 value) L (L.set 7 (L 7 ++ [value])) 1 :=
      runs_push (i := (7 : Fin 8)) (e := value) hL (by apply lenOK_set hL 7; exact hB)
    simpa only [h7,List.nil_append] using hr
  have he : ∃ T, Runs (LenOK B) (if 0<c.stack.length then .push 7 1 else emptyStack)
      L (L.set 7 [flag c]) T := by
    by_cases hk : c.stack=[]
    · have hflag : flag c=(if taskTag c.task<3 then 1 else 0) := by
        simp [flag,running,hk]
      have hpush : Runs (LenOK B) (byKind (taskTag c.task)) L (L.set 7 [flag c]) 1 := by
        simpa only [byKind,hflag] using hp (if taskTag c.task<3 then 1 else 0)
      let C := (blocks (writeFrames ns c.stack).control ++ blocks (payload ns c.task)) ++ [0]
      have hsrc : L 2=C ++ unary (taskTag c.task) ++ blocks [c.env.length,c.stack.length] := by
        rw [show L 2=withInput (encode ns c) x 2 from rfl,SequentialStepDispatchMachine.control_fields,blocks_cons]
        simp only [C,List.append_assoc]
      obtain ⟨T,ht⟩ := SequentialTagDispatchMachine.dispatch_runs (src := (2 : Fin 8)) (tmp := 1) (by decide)
        [c.env.length,c.stack.length] 4 (taskTag c.task) (SequentialStepDispatchMachine.task_tag_bound c.task)
        C byKind L _ hsrc (by rw [lastSym_append]; rfl) rfl hL hpush
      exact ⟨T,by simpa [emptyStack,hk] using ht⟩
    · have hn : 0<c.stack.length := List.length_pos_iff.mpr hk
      have hflag : flag c=1 := by simp [flag,running,hk]
      exact ⟨1,by simpa only [if_pos hn,hflag] using hp 1⟩
  obtain ⟨T,ht⟩ := he
  let C := (blocks (writeFrames ns c.stack).control ++ blocks (writeTask ns c.task).control) ++ [0]
  have hsrc : L 2=C ++ unary c.stack.length ++ blocks [c.env.length] := by
    change withInput (encode ns c) x 2 = _
    rw [SequentialStepDispatchMachine.control_fields,← SequentialStepDispatchMachine.task_fields]
    simp only [C,blocks_cons,show blocks []=[] from rfl,List.nil_append,List.append_assoc]
  exact SequentialFieldPresenceMachine.dispatch_runs [c.env.length] c.stack.length C (.push 7 1) emptyStack
    L _ hsrc (by rw [lastSym_append]; rfl) rfl hL ht

end Shallot.MacroPeg.CBV.SequentialRunningMachine
