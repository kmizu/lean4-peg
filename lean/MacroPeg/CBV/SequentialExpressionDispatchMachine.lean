import MacroPeg.CBV.SequentialStarPackedMachine
import Complexity.ListFiniteAlphabet

/-! Select every expression instruction from its actual fixed-pool code
identifier, restoring all source fields before entering the chosen program. -/
namespace Shallot.MacroPeg.CBV.SequentialExpressionDispatchMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialControlEditMachine
open SequentialSharedWords (Config CaptureEnv Runs initial)
open SequentialSharedStateCodec (encode write writeTask writeFrames Input)
open SequentialCaptureCopyMachine (withInput)

def before (a : MExp) (m : Nat) (E : CaptureEnv) (p : Nat)
    (K : List SequentialSharedWords.Frame) : Config := ⟨m,.expr a p,E,K⟩

def execute (ns : List CBVtoCBN.CompileNode) (g : MGrammar) : MExp → LProg 8
  | .eps => SequentialReadPackedMachine.program .eps
  | .any => SequentialReadPackedMachine.program .any
  | .chr c => SequentialReadPackedMachine.program (.chr c)
  | .range lo hi => SequentialReadPackedMachine.program (.range lo hi)
  | .lit w => SequentialReadPackedMachine.program (.lit w)
  | .dbg a => SequentialReadPackedMachine.program (.dbg a)
  | .lam arity a => SequentialReadPackedMachine.program (.lam arity a)
  | .param k => SequentialParamPackedMachine.program k
  | .seq a b => SequentialStaticPackedMachine.program ns g (.seq a b)
  | .call i args => SequentialStaticPackedMachine.program ns g (.call i args)
  | .callParam k args => SequentialStaticPackedMachine.program ns g (.callParam k args)
  | .invoke arity a args => SequentialStaticPackedMachine.program ns g (.invoke arity a args)
  | .alt a b => SequentialEightTapeMachine.program (SequentialEntryPackedMachine.program ns (.alt a b))
  | .notP a => SequentialEightTapeMachine.program (SequentialEntryPackedMachine.program ns (.notP a))
  | .star a => SequentialEightTapeMachine.program (SequentialEntryPackedMachine.program ns (.star a))

def branch (ns : List CBVtoCBN.CompileNode) (g : MGrammar) (id : Nat) : LProg 8 :=
  match (SequentialStackPool.exprPool ns)[id]? with
  | some a => execute ns g a
  | none => skipP 2

def program (ns : List CBVtoCBN.CompileNode) (g : MGrammar) : LProg 8 :=
  SequentialTagDispatchMachine.program 2 1 3 (SequentialStackPool.exprPool ns).length (branch ns g)

private theorem read_runs (g : MGrammar) (x : List Char) (e : MExp) (read : SequentialReadTests.Read)
    (m : Nat) (E : CaptureEnv) (p : Nat) (K : List SequentialSharedWords.Frame) (next : Config)
    (h : Runs g x (initial g x e) (SequentialReadPackedMachine.before read m E p K))
    (hs : SequentialSharedWords.step g x (SequentialReadPackedMachine.before read m E p K)=some next) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (SequentialReadPackedMachine.program read)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (SequentialReadPackedMachine.before read m E p K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) next) x) T := by
  have hc := SequentialSharedCursors.reachable_chain g x e _ h
  change SequentialCursorChain.Chain 0 (p :: K.filterMap SequentialSharedCursors.frameCursor) x.length at hc
  cases hc with
  | cons hz ht =>
    have he := Option.some.inj (hs.symm.trans (SequentialReadPackedMachine.actual_step g x read m E p K ht.bound))
    rw [he]
    exact SequentialReadPackedMachine.transition_runs g x e read m E p K h

private theorem static_runs (g : MGrammar) (x : List Char) (e : MExp) (entry : SequentialStaticPackedMachine.Entry)
    (m : Nat) (E : CaptureEnv) (p : Nat) (K : List SequentialSharedWords.Frame) (next : Config)
    (h : Runs g x (initial g x e) (SequentialStaticPackedMachine.before entry m E p K))
    (hs : SequentialSharedWords.step g x (SequentialStaticPackedMachine.before entry m E p K)=some next) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (SequentialStaticPackedMachine.program (CBVtoCBN.compilerNodes g e) g entry)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (SequentialStaticPackedMachine.before entry m E p K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) next) x) T := by
  have he := Option.some.inj (hs.symm.trans (SequentialStaticPackedMachine.actual_step g x entry m E p K))
  rw [he]
  exact SequentialStaticPackedMachine.transition_runs g x e entry m E p K h

private theorem entry_runs (g : MGrammar) (x : List Char) (e : MExp) (entry : SequentialCursorEntryMachine.Entry)
    (m : Nat) (E : CaptureEnv) (p : Nat) (K : List SequentialSharedWords.Frame) (next : Config)
    (h : Runs g x (initial g x e) (SequentialCursorEntryMachine.before entry m E p K))
    (hs : SequentialSharedWords.step g x (SequentialCursorEntryMachine.before entry m E p K)=some next) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (SequentialEightTapeMachine.program (SequentialEntryPackedMachine.program (CBVtoCBN.compilerNodes g e) entry))
      (withInput (encode (CBVtoCBN.compilerNodes g e) (SequentialCursorEntryMachine.before entry m E p K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) next) x) T := by
  have he := Option.some.inj (hs.symm.trans (SequentialCursorEntryMachine.actual_step g x entry m E p K))
  rw [he]
  exact SequentialEightTapeMachine.entry_runs g x e entry m E p K h

/-- Exhaustive instruction templates for every source expression constructor. -/
theorem execute_runs (g : MGrammar) (x : List Char) (e a : MExp) (m : Nat) (E : CaptureEnv)
    (p : Nat) (K : List SequentialSharedWords.Frame) (next : Config)
    (h : Runs g x (initial g x e) (before a m E p K))
    (hs : SequentialSharedWords.step g x (before a m E p K)=some next) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (execute (CBVtoCBN.compilerNodes g e) g a)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (before a m E p K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) next) x) T := by
  cases a with
  | eps => exact read_runs g x e .eps m E p K next h hs
  | any => exact read_runs g x e .any m E p K next h hs
  | chr c => exact read_runs g x e (.chr c) m E p K next h hs
  | range lo hi => exact read_runs g x e (.range lo hi) m E p K next h hs
  | lit w => exact read_runs g x e (.lit w) m E p K next h hs
  | dbg a => exact read_runs g x e (.dbg a) m E p K next h hs
  | lam arity a => exact read_runs g x e (.lam arity a) m E p K next h hs
  | seq a b => exact static_runs g x e (.seq a b) m E p K next h hs
  | call i args => exact static_runs g x e (.call i args) m E p K next h hs
  | callParam k args => exact static_runs g x e (.callParam k args) m E p K next h hs
  | invoke arity a args => exact static_runs g x e (.invoke arity a args) m E p K next h hs
  | alt a b => exact entry_runs g x e (.alt a b) m E p K next h hs
  | notP a => exact entry_runs g x e (.notP a) m E p K next h hs
  | star a => exact entry_runs g x e (.star a) m E p K next h hs
  | param k =>
    have he := Option.some.inj (hs.symm.trans (SequentialParamPackedMachine.actual_step g x k m E p K))
    rw [he]
    exact SequentialParamPackedMachine.transition_runs g x e k m E p K h

theorem before_control (ns : List CBVtoCBN.CompileNode) (a : MExp) (m : Nat) (E : CaptureEnv)
    (p : Nat) (K : List SequentialSharedWords.Frame) :
    withInput (encode ns (before a m E p K)) [] 2=blocks (writeFrames ns K).control ++
      blocks [0,SequentialStackCodec.exprId ns a] ++ blocks [E.length,K.length] := by
  change SequentialCursorEntryMachine.layout (encode ns (before a m E p K)) 2 = _
  rw [SequentialAnyPackedMachine.layout_control]
  have he : (write ns (before a m E p K)).control=[E.length,K.length] ++
      [0,SequentialStackCodec.exprId ns a] ++ (writeFrames ns K).control := by
    simp [write,before,writeTask,Input.append,SequentialSharedStateCodec.putControl,
      SequentialSharedStateCodec.putWords,SequentialSharedStateCodec.putCursor,
      SequentialSharedStateCodec.putExpr,SequentialStackCodec.writeExpr]
  rw [he,blocks_append,blocks_append]
  simp only [List.append_assoc]

/-- One fixed program handles all reachable expression tasks of the source
program. Its instruction selector reads the actual encoded expression id. -/
theorem transition_runs (g : MGrammar) (x : List Char) (e a : MExp) (m : Nat) (E : CaptureEnv)
    (p : Nat) (K : List SequentialSharedWords.Frame) (next : Config)
    (h : Runs g x (initial g x e) (before a m E p K))
    (hs : SequentialSharedWords.step g x (before a m E p K)=some next) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (program (CBVtoCBN.compilerNodes g e) g)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (before a m E p K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) next) x) T := by
  let ns := CBVtoCBN.compilerNodes g e
  let L := withInput (encode ns (before a m E p K)) x
  let target := withInput (encode ns next) x
  let B := (SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3
  have hok : SequentialStackPool.ExprOK ns a := (SequentialSharedPool.reachable_ok g x e _ h).1
  have hget : (SequentialStackPool.exprPool ns)[SequentialStackCodec.exprId ns a]?=some a := get_idxOf hok.mem
  have hid : SequentialStackCodec.exprId ns a ≤ (SequentialStackPool.exprPool ns).length := by
    exact Nat.le_of_lt (List.idxOf_lt_length_of_mem hok.mem)
  obtain ⟨T,ht⟩ := execute_runs g x e a m E p K next h hs
  have hb : Complexity.Runs (LenOK B) (branch ns g (SequentialStackCodec.exprId ns a)) L target T := by
    simpa only [branch,hget] using ht
  have hL : LenOK B L := by obtain ⟨t,ht,hx⟩ := hb; exact hx.q_start
  let C := blocks (writeFrames ns K).control ++ [0]
  have hsrc : L 2=C ++ unary (SequentialStackCodec.exprId ns a) ++ blocks [E.length,K.length,0] := by
    change withInput (encode ns (before a m E p K)) [] 2 = _
    rw [before_control]
    simp only [C,blocks_cons,show blocks []=[] from rfl,List.nil_append,List.replicate_zero,List.append_nil,
      List.append_assoc]
  exact SequentialTagDispatchMachine.dispatch_runs (src := (2 : Fin 8)) (tmp := 1) (by decide)
    [E.length,K.length,0] (SequentialStackPool.exprPool ns).length (SequentialStackCodec.exprId ns a) hid C
    (branch ns g) L target hsrc (by rw [lastSym_append]; rfl) rfl hL hb

theorem transition_tape (g : MGrammar) (x : List Char) (e a : MExp) (m : Nat) (E : CaptureEnv)
    (p : Nat) (K : List SequentialSharedWords.Frame) (next : Config)
    (h : Runs g x (initial g x e) (before a m E p K))
    (hs : SequentialSharedWords.step g x (before a m E p K)=some next) (tau : Tapes 8)
    (hrep : Rep (withInput (encode (CBVtoCBN.compilerNodes g e) (before a m E p K)) x) tau) :
    ∃ t tau', Exec (TFits ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (program (CBVtoCBN.compilerNodes g e) g).compile tau t (.cont tau') ∧
      Rep (withInput (encode (CBVtoCBN.compilerNodes g e) next) x) tau' := by
  obtain ⟨T,hr⟩ := transition_runs g x e a m E p K next h hs
  exact tape_runs hr tau hrep

theorem finite_alphabet (ns : List CBVtoCBN.CompileNode) (g : MGrammar) :
    ∃ E, 0x110001 ≤ E ∧ (program ns g).compile.SymOK (E+4) := by
  obtain ⟨E,_hE,hc⟩ := LProg.exists_constOK (program ns g)
  exact ⟨max E 0x110001,Nat.le_max_right _ _,compile_symOK _ _
    (LProg.ConstOK.mono (Nat.le_max_left E 0x110001) hc)⟩

end Shallot.MacroPeg.CBV.SequentialExpressionDispatchMachine
