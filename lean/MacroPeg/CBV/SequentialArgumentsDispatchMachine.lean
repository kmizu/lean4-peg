import MacroPeg.CBV.SequentialExpressionDispatchMachine

/-! Decode the actual argument-list code through finite source-fixed branches.
Each unary field is restored before the next decision or instruction runs. -/
namespace Shallot.MacroPeg.CBV.SequentialArgumentsDispatchMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialControlEditMachine
open SequentialSharedWords (Config CaptureEnv Runs initial)
open SequentialSharedStateCodec (encode write writeTask writeFrames Input)
open SequentialCaptureCopyMachine (withInput)

def before (es : List MExp) (m : Nat) (E : CaptureEnv) (p : Nat)
    (K : List SequentialSharedWords.Frame) : Config := ⟨m,.args es p,E,K⟩

def execute (ns : List CBVtoCBN.CompileNode) (g : MGrammar) : List MExp → LProg 8
  | [] => SequentialStaticPackedMachine.program ns g .argsNil
  | a :: es => SequentialEightTapeMachine.program (SequentialEntryPackedMachine.program ns (.args a es))

def parse (ns : List CBVtoCBN.CompileNode) (g : MGrammar) : Nat → List MExp → LProg 8
  | 0,done => execute ns g done
  | fuel+1,done => SequentialTagDispatchMachine.program 2 1 (4+done.length)
      (SequentialStackPool.exprPool ns).length (fun id => match (SequentialStackPool.exprPool ns)[id]? with
        | some a => parse ns g fuel (done ++ [a])
        | none => skipP 2)

def program (ns : List CBVtoCBN.CompileNode) (g : MGrammar) (bound : Nat) : LProg 8 :=
  SequentialTagDispatchMachine.program 2 1 3 bound (fun n => parse ns g n [])

theorem writeExprs_eq (ns : List CBVtoCBN.CompileNode) (es : List MExp) :
    SequentialStackCodec.writeExprs ns es=es.length :: es.map (SequentialStackCodec.exprId ns) := by
  simp only [SequentialStackCodec.writeExprs,SequentialStackCodec.writeList]
  congr 1
  induction es with
  | nil => rfl
  | cons a es ih => simp [SequentialStackCodec.writeExpr,ih]

theorem before_control (ns : List CBVtoCBN.CompileNode) (es : List MExp) (m : Nat) (E : CaptureEnv)
    (p : Nat) (K : List SequentialSharedWords.Frame) :
    withInput (encode ns (before es m E p K)) [] 2=blocks (writeFrames ns K).control ++
      blocks (SequentialStackCodec.writeExprs ns es) ++ blocks [E.length,K.length,1] := by
  change SequentialCursorEntryMachine.layout (encode ns (before es m E p K)) 2 = _
  rw [SequentialAnyPackedMachine.layout_control]
  have he : (write ns (before es m E p K)).control=[E.length,K.length,1] ++
      SequentialStackCodec.writeExprs ns es ++ (writeFrames ns K).control := by
    simp [write,before,writeTask,Input.append,SequentialSharedStateCodec.putControl,
      SequentialSharedStateCodec.putWords,SequentialSharedStateCodec.putCursor,SequentialSharedStateCodec.putExprs]
  rw [he,blocks_append,blocks_append]
  simp only [List.append_assoc]

theorem execute_runs (g : MGrammar) (x : List Char) (e : MExp) (es : List MExp) (m : Nat)
    (E : CaptureEnv) (p : Nat) (K : List SequentialSharedWords.Frame) (next : Config)
    (h : Runs g x (initial g x e) (before es m E p K))
    (hs : SequentialSharedWords.step g x (before es m E p K)=some next) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (execute (CBVtoCBN.compilerNodes g e) g es)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (before es m E p K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) next) x) T := by
  cases es with
  | nil =>
    have he := Option.some.inj (hs.symm.trans (SequentialStaticPackedMachine.actual_step g x .argsNil m E p K))
    rw [he]
    exact SequentialStaticPackedMachine.transition_runs g x e .argsNil m E p K h
  | cons a es =>
    have he := Option.some.inj (hs.symm.trans (SequentialCursorEntryMachine.actual_step g x (.args a es) m E p K))
    rw [he]
    exact SequentialEightTapeMachine.entry_runs g x e (.args a es) m E p K h

/-- The prefix `done` is a code-generation parameter. Runtime choices of its
entries are the branches reading actual expression ids from the source tape. -/
theorem parse_runs (g : MGrammar) (x : List Char) (e : MExp) (done es : List MExp) (m : Nat)
    (E : CaptureEnv) (p : Nat) (K : List SequentialSharedWords.Frame) (next : Config)
    (h : Runs g x (initial g x e) (before (done ++ es) m E p K))
    (hs : SequentialSharedWords.step g x (before (done ++ es) m E p K)=some next) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (parse (CBVtoCBN.compilerNodes g e) g es.length done)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (before (done ++ es) m E p K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) next) x) T := by
  induction es generalizing done with
  | nil =>
    simpa only [List.append_nil,List.length_nil,parse] using execute_runs g x e done m E p K next
      (by simpa only [List.append_nil] using h) (by simpa only [List.append_nil] using hs)
  | cons a es ih =>
    let ns := CBVtoCBN.compilerNodes g e
    let L := withInput (encode ns (before (done ++ a :: es) m E p K)) x
    let target := withInput (encode ns next) x
    let B := (SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3
    have he : (done ++ [a]) ++ es=done ++ a :: es := by simp only [List.append_assoc,List.singleton_append]
    obtain ⟨T,ht⟩ := ih (done ++ [a]) (by simpa only [he] using h) (by simpa only [he] using hs)
    rw [he] at ht
    have hok : SequentialStackPool.ArgsOK ns (done ++ a :: es) := (SequentialSharedPool.reachable_ok g x e _ h).1
    have ha : a ∈ SequentialStackPool.exprPool ns := hok.mem a (by simp)
    have hget : (SequentialStackPool.exprPool ns)[SequentialStackCodec.exprId ns a]?=some a := get_idxOf ha
    let nextBranch := fun (id : Nat) => match (SequentialStackPool.exprPool ns)[id]? with
      | some b => parse ns g es.length (done ++ [b])
      | none => skipP 2
    have hb : Complexity.Runs (LenOK B) (nextBranch (SequentialStackCodec.exprId ns a)) L target T := by
      simpa only [nextBranch,hget] using ht
    have hL : LenOK B L := by obtain ⟨t,ht,hx⟩ := hb; exact hx.q_start
    let saved := [E.length,K.length,1,(done ++ a :: es).length] ++ done.map (SequentialStackCodec.exprId ns)
    let C := (blocks (writeFrames ns K).control ++ blocks (es.map (SequentialStackCodec.exprId ns))) ++ [0]
    have hsrc : L 2=C ++ unary (SequentialStackCodec.exprId ns a) ++ blocks saved := by
      change withInput (encode ns (before (done ++ a :: es) m E p K)) [] 2 = _
      rw [before_control,writeExprs_eq]
      simp only [saved,C,List.map_append,List.map_cons,blocks_append,blocks_cons,
        show blocks []=[] from rfl,List.nil_append,List.append_assoc]
    have hid : SequentialStackCodec.exprId ns a ≤ (SequentialStackPool.exprPool ns).length :=
      Nat.le_of_lt (List.idxOf_lt_length_of_mem ha)
    obtain ⟨U,hu⟩ := SequentialTagDispatchMachine.dispatch_runs (src := (2 : Fin 8)) (tmp := 1) (by decide)
      saved (SequentialStackPool.exprPool ns).length (SequentialStackCodec.exprId ns a) hid C nextBranch
      L target hsrc (by rw [lastSym_append]; rfl) rfl hL hb
    have hlen : saved.length=4+done.length := by
      simp [saved]
      omega
    rw [hlen] at hu
    refine ⟨U,?_⟩
    simpa only [parse,List.length_cons] using hu

/-- One fixed source program reads the runtime argument-list length and each
actual syntax id before executing its complete argument-start instruction. -/
theorem transition_runs (g : MGrammar) (x : List Char) (e : MExp) (es : List MExp) (m : Nat)
    (E : CaptureEnv) (p : Nat) (K : List SequentialSharedWords.Frame) (next : Config)
    (h : Runs g x (initial g x e) (before es m E p K))
    (hs : SequentialSharedWords.step g x (before es m E p K)=some next) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (program (CBVtoCBN.compilerNodes g e) g (SequentialStackCode.programBudget g e))
      (withInput (encode (CBVtoCBN.compilerNodes g e) (before es m E p K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) next) x) T := by
  let ns := CBVtoCBN.compilerNodes g e
  let L := withInput (encode ns (before es m E p K)) x
  let target := withInput (encode ns next) x
  let B := (SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3
  obtain ⟨T,ht⟩ := parse_runs g x e [] es m E p K next h hs
  have hb : Complexity.Runs (LenOK B) (parse ns g es.length []) L target T := ht
  have hL : LenOK B L := by obtain ⟨t,ht,hx⟩ := hb; exact hx.q_start
  have hfit : sizeOf es ≤ SequentialStackCode.programBudget g e :=
    (SequentialSharedStateBound.reachable_fits g x e _ h).1
  have hlen : es.length ≤ SequentialStackCode.programBudget g e :=
    Nat.le_trans (SequentialSharedStateBound.exprs_length_size es) hfit
  let C := (blocks (writeFrames ns K).control ++ blocks (es.map (SequentialStackCodec.exprId ns))) ++ [0]
  have hsrc : L 2=C ++ unary es.length ++ blocks [E.length,K.length,1] := by
    change withInput (encode ns (before es m E p K)) [] 2 = _
    rw [before_control,writeExprs_eq,blocks_cons]
    simp only [C,List.append_assoc]
  exact SequentialTagDispatchMachine.dispatch_runs (src := (2 : Fin 8)) (tmp := 1) (by decide)
    [E.length,K.length,1] (SequentialStackCode.programBudget g e) es.length hlen C (fun n => parse ns g n [])
    L target hsrc (by rw [lastSym_append]; rfl) rfl hL hb

theorem finite_alphabet (ns : List CBVtoCBN.CompileNode) (g : MGrammar) (bound : Nat) :
    ∃ E, 0x110001 ≤ E ∧ (program ns g bound).compile.SymOK (E+4) := by
  obtain ⟨E,_hE,hc⟩ := LProg.exists_constOK (program ns g bound)
  exact ⟨max E 0x110001,Nat.le_max_right _ _,compile_symOK _ _
    (LProg.ConstOK.mono (Nat.le_max_left E 0x110001) hc)⟩

end Shallot.MacroPeg.CBV.SequentialArgumentsDispatchMachine
