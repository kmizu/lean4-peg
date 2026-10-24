import MacroPeg.CBV.SequentialArgHeadDispatchMachine

/-! Select the actual saved expression of sequence, choice, and repetition
continuations from the fixed syntax pool. -/
namespace Shallot.MacroPeg.CBV.SequentialRefReturnDispatchMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialControlEditMachine
open SequentialSharedWords (Config CaptureEnv Runs initial)
open SequentialSharedStateCodec (encode write writeTask writeFrames Input)
open SequentialCaptureCopyMachine (withInput)
open SequentialReturnPackedMachine (tag)

inductive Ref where
  | seq
  | alt
  | star

def frame (ref : Ref) (a : MExp) (p : Nat) : SequentialSharedWords.Frame := match ref with
  | .seq => .seq a
  | .alt => .alt a p
  | .star => .star a p

def frameTag : Ref → Nat
  | .seq => 0
  | .alt => 1
  | .star => 3

def before (ref : Ref) (a : MExp) (m : Nat) (E : CaptureEnv) (p : Nat) (r : Res)
    (K : List SequentialSharedWords.Frame) : Config := ⟨m,.value (.expr r),E,frame ref a p :: K⟩

def execute (ns : List CBVtoCBN.CompileNode) (ref : Ref) (a : MExp) : LProg 8 := match ref with
  | .seq => SequentialEightTapeMachine.program (SequentialReturnPackedMachine.program ns (.seq a))
  | .alt => SequentialEightTapeMachine.program (SequentialReturnPackedMachine.program ns (.alt a))
  | .star => SequentialStarPackedMachine.program ns a

def branch (ns : List CBVtoCBN.CompileNode) (ref : Ref) (id : Nat) : LProg 8 :=
  match (SequentialStackPool.exprPool ns)[id]? with
  | some a => execute ns ref a
  | none => skipP 2

def program (ns : List CBVtoCBN.CompileNode) (ref : Ref) : LProg 8 :=
  SequentialTagDispatchMachine.program 2 1 5 (SequentialStackPool.exprPool ns).length (branch ns ref)

private theorem return_runs (g : MGrammar) (x : List Char) (e : MExp) (ret : SequentialReturnPackedMachine.Return)
    (m : Nat) (E : CaptureEnv) (p : Nat) (r : Res) (K : List SequentialSharedWords.Frame) (next : Config)
    (h : Runs g x (initial g x e) (SequentialReturnPackedMachine.before ret m E p r K))
    (hs : SequentialSharedWords.step g x (SequentialReturnPackedMachine.before ret m E p r K)=some next) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (SequentialEightTapeMachine.program (SequentialReturnPackedMachine.program (CBVtoCBN.compilerNodes g e) ret))
      (withInput (encode (CBVtoCBN.compilerNodes g e) (SequentialReturnPackedMachine.before ret m E p r K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) next) x) T := by
  have he := Option.some.inj (hs.symm.trans (SequentialReturnPackedMachine.actual_step g x ret m E p r K))
  rw [he]
  exact SequentialEightTapeMachine.return_runs g x e ret m E p r K h

theorem execute_runs (g : MGrammar) (x : List Char) (e : MExp) (ref : Ref) (a : MExp) (m : Nat)
    (E : CaptureEnv) (p : Nat) (r : Res) (K : List SequentialSharedWords.Frame) (next : Config)
    (h : Runs g x (initial g x e) (before ref a m E p r K))
    (hs : SequentialSharedWords.step g x (before ref a m E p r K)=some next) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (execute (CBVtoCBN.compilerNodes g e) ref a)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (before ref a m E p r K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) next) x) T := by
  cases ref with
  | seq => exact return_runs g x e (.seq a) m E p r K next h hs
  | alt => exact return_runs g x e (.alt a) m E p r K next h hs
  | star =>
    have he := Option.some.inj (hs.symm.trans (SequentialStarPackedMachine.actual_step g x a m E p r K))
    rw [he]
    exact SequentialStarPackedMachine.transition_runs g x e a m E p r K h

theorem before_control (ns : List CBVtoCBN.CompileNode) (ref : Ref) (a : MExp) (m : Nat)
    (E : CaptureEnv) (p : Nat) (r : Res) (K : List SequentialSharedWords.Frame) :
    withInput (encode ns (before ref a m E p r K)) [] 2=blocks (writeFrames ns K).control ++
      blocks [E.length,K.length+1,3,tag r,frameTag ref,SequentialStackCodec.exprId ns a] := by
  change SequentialCursorEntryMachine.layout (encode ns (before ref a m E p r K)) 2 = _
  rw [SequentialAnyPackedMachine.layout_control]
  have he : (write ns (before ref a m E p r K)).control=
      [E.length,K.length+1,3,tag r,frameTag ref,SequentialStackCodec.exprId ns a] ++ (writeFrames ns K).control := by
    cases ref <;> cases r with
    | none => simp [write,before,frame,frameTag,tag,writeTask,writeFrames,SequentialSharedStateCodec.writeFrame,
        Input.append,SequentialSharedStateCodec.putControl,SequentialSharedStateCodec.putWords,
        SequentialSharedStateCodec.putCursor,SequentialSharedStateCodec.putExpr,SequentialStackCodec.writeExpr]
    | some v => cases v <;> simp [write,before,frame,frameTag,tag,writeTask,writeFrames,SequentialSharedStateCodec.writeFrame,
        Input.append,SequentialSharedStateCodec.putControl,SequentialSharedStateCodec.putWords,
        SequentialSharedStateCodec.putCursor,SequentialSharedStateCodec.putExpr,SequentialStackCodec.writeExpr]
  rw [he,blocks_append]

theorem transition_runs (g : MGrammar) (x : List Char) (e : MExp) (ref : Ref) (a : MExp) (m : Nat)
    (E : CaptureEnv) (p : Nat) (r : Res) (K : List SequentialSharedWords.Frame) (next : Config)
    (h : Runs g x (initial g x e) (before ref a m E p r K))
    (hs : SequentialSharedWords.step g x (before ref a m E p r K)=some next) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (program (CBVtoCBN.compilerNodes g e) ref)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (before ref a m E p r K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) next) x) T := by
  let ns := CBVtoCBN.compilerNodes g e
  let L := withInput (encode ns (before ref a m E p r K)) x
  let target := withInput (encode ns next) x
  let B := (SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3
  have hok := (SequentialSharedPool.reachable_ok g x e _ h).2 (frame ref a p) (by simp [before])
  have hmem : a ∈ SequentialStackPool.exprPool ns := by
    cases ref with
    | seq => exact hok.mem
    | alt => exact hok.mem
    | star => exact hok.star.mem
  have hget : (SequentialStackPool.exprPool ns)[SequentialStackCodec.exprId ns a]?=some a := get_idxOf hmem
  obtain ⟨T,ht⟩ := execute_runs g x e ref a m E p r K next h hs
  have hb : Complexity.Runs (LenOK B) (branch ns ref (SequentialStackCodec.exprId ns a)) L target T := by
    simpa only [branch,hget] using ht
  have hL : LenOK B L := by obtain ⟨t,ht,hx⟩ := hb; exact hx.q_start
  let C := blocks (writeFrames ns K).control ++ [0]
  have hsrc : L 2=C ++ unary (SequentialStackCodec.exprId ns a) ++ blocks [E.length,K.length+1,3,tag r,frameTag ref] := by
    change withInput (encode ns (before ref a m E p r K)) [] 2 = _
    rw [before_control]
    simp only [C,blocks_cons,show blocks []=[] from rfl,List.nil_append,List.append_assoc]
  exact SequentialTagDispatchMachine.dispatch_runs (src := (2 : Fin 8)) (tmp := 1) (by decide)
    [E.length,K.length+1,3,tag r,frameTag ref] (SequentialStackPool.exprPool ns).length (SequentialStackCodec.exprId ns a)
    (Nat.le_of_lt (List.idxOf_lt_length_of_mem hmem)) C (branch ns ref) L target hsrc
    (by rw [lastSym_append]; rfl) rfl hL hb

theorem finite_alphabet (ns : List CBVtoCBN.CompileNode) (ref : Ref) :
    ∃ E, 0x110001 ≤ E ∧ (program ns ref).compile.SymOK (E+4) := by
  obtain ⟨E,_hE,hc⟩ := LProg.exists_constOK (program ns ref)
  exact ⟨max E 0x110001,Nat.le_max_right _ _,compile_symOK _ _
    (LProg.ConstOK.mono (Nat.le_max_left E 0x110001) hc)⟩

end Shallot.MacroPeg.CBV.SequentialRefReturnDispatchMachine
