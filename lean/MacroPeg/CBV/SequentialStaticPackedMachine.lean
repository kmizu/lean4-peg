import MacroPeg.CBV.SequentialReadPackedMachine

/-! Remaining source-fixed entries: sequence, checked named calls, empty
argument lists, and unsupported higher-order forms. Dynamic data stay on tapes. -/
namespace Shallot.MacroPeg.CBV.SequentialStaticPackedMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialControlEditMachine
open SequentialSharedWords (Config CaptureEnv Runs initial)
open SequentialSharedStateCodec (encode write writeTask writeFrames Input)
open SequentialCaptureCopyMachine (withInput)

private theorem blocks_nil : blocks [] = [] := rfl

inductive Entry where
  | seq (a b : MExp)
  | call (i : Nat) (args : List MExp)
  | argsNil
  | callParam (k : Nat) (args : List MExp)
  | invoke (arity : Nat) (body : MExp) (args : List MExp)

def validCall (g : MGrammar) (i : Nat) (args : List MExp) : Bool :=
  match ruleAtM g.rules i with
  | some rule => decide (rule.arity=args.length)
  | none => false

def beforeTask : Entry → Nat → SequentialSharedWords.Task
  | .seq a b,p => .expr (.seq a b) p
  | .call i args,p => .expr (.call i args) p
  | .argsNil,p => .args [] p
  | .callParam k args,p => .expr (.callParam k args) p
  | .invoke arity body args,p => .expr (.invoke arity body args) p

def nextTask (g : MGrammar) : Entry → Nat → SequentialSharedWords.Task
  | .seq a _,p => .expr a p
  | .call i args,p => if validCall g i args then .args args p else .value (.expr (some none))
  | .argsNil,p => .value (.args (some (some ([],p))))
  | .callParam _ _,_ => .value (.expr (some none))
  | .invoke _ _ _,_ => .value (.expr none)

def newFrame (g : MGrammar) : Entry → Option SequentialSharedWords.Frame
  | .seq _ b => some (.seq b)
  | .call i args => if validCall g i args then some (.call i) else none
  | _ => none

def drops (g : MGrammar) : Entry → Bool
  | .seq _ _ | .argsNil => false
  | .call i args => !(validCall g i args)
  | _ => true

def before (entry : Entry) (m : Nat) (E : CaptureEnv) (p : Nat)
    (K : List SequentialSharedWords.Frame) : Config := ⟨m,beforeTask entry p,E,K⟩
def after (g : MGrammar) (entry : Entry) (m : Nat) (E : CaptureEnv) (p : Nat)
    (K : List SequentialSharedWords.Frame) : Config :=
  ⟨m,nextTask g entry p,E,(newFrame g entry).toList ++ K⟩

theorem actual_step (g : MGrammar) (x : List Char) (entry : Entry) (m : Nat) (E : CaptureEnv)
    (p : Nat) (K : List SequentialSharedWords.Frame) :
    SequentialSharedWords.step g x (before entry m E p K)=some (after g entry m E p K) := by
  cases entry with
  | call i args =>
    cases hr : ruleAtM g.rules i with
    | none => simp [before,after,beforeTask,nextTask,newFrame,validCall,SequentialSharedWords.step,hr]
    | some rule => by_cases ha : rule.arity=args.length <;>
        simp [before,after,beforeTask,nextTask,newFrame,validCall,SequentialSharedWords.step,hr,ha]
  | _ => rfl

def oldFields (ns : List CBVtoCBN.CompileNode) (entry : Entry) : List Nat :=
  (writeTask ns (beforeTask entry 0)).control

def freshFields (ns : List CBVtoCBN.CompileNode) (g : MGrammar) (entry : Entry) : List Nat :=
  (writeTask ns (nextTask g entry 0)).control ++ (writeFrames ns (newFrame g entry).toList).control

def count (g : MGrammar) (entry : Entry) : Bool := (newFrame g entry).isSome

def countProgram (inc : Bool) : LProg 8 := if inc then incrementSecond 2 1 else skipP 2

def program (ns : List CBVtoCBN.CompileNode) (g : MGrammar) (entry : Entry) : LProg 8 :=
  .seq (if drops g entry then dropBlock 0 1 else skipP 0)
    (.seq (countProgram (count g entry)) (replace 2 1 2 (oldFields ns entry).length (freshFields ns g entry)))

/-- Static entry edits preserve word ownership; the only saved-frame changes
are cursor-free sequence and call frames. -/
theorem fields (ns : List CBVtoCBN.CompileNode) (g : MGrammar) (entry : Entry) (m : Nat)
    (E : CaptureEnv) (p : Nat) (K : List SequentialSharedWords.Frame) :
    withInput (encode ns (before entry m E p K)) [] 2 = blocks (writeFrames ns K).control ++
      blocks (oldFields ns entry) ++ blocks [E.length,K.length] ∧
    withInput (encode ns (after g entry m E p K)) [] 2 = blocks (writeFrames ns K).control ++
      blocks (freshFields ns g entry) ++ blocks [E.length,K.length+if count g entry then 1 else 0] := by
  have hb (c : Config) := SequentialAnyPackedMachine.layout_control ns c
  change SequentialCursorEntryMachine.layout (encode ns (before entry m E p K)) 2 = _ ∧
    SequentialCursorEntryMachine.layout (encode ns (after g entry m E p K)) 2 = _
  rw [hb,hb]
  have hctrl : ∀ (c : Config), blocks (write ns c).control =
      blocks (writeFrames ns c.stack).control ++ blocks (writeTask ns c.task).control ++
        blocks [c.env.length,c.stack.length] := by
    intro c
    change blocks ([c.env.length,c.stack.length] ++ (writeTask ns c.task).control ++
      (writeFrames ns c.stack).control) = _
    simp only [blocks_append,List.append_assoc]
  rw [hctrl,hctrl]
  cases entry with
  | call i args =>
    cases hv : validCall g i args <;>
      simp [hv,before,after,oldFields,freshFields,beforeTask,nextTask,newFrame,count,writeTask,writeFrames,
    SequentialSharedStateCodec.writeFrame,Input.append,Input.empty,SequentialSharedStateCodec.putControl,
    SequentialSharedStateCodec.putCursor,
    SequentialSharedStateCodec.putExpr,SequentialSharedStateCodec.putExprs,
    SequentialStackCodec.writeExpr,blocks_nil,blocks_cons,blocks_append,List.append_assoc]
  | _ => simp [before,after,oldFields,freshFields,beforeTask,nextTask,newFrame,count,writeTask,writeFrames,
    SequentialSharedStateCodec.writeFrame,Input.append,Input.empty,SequentialSharedStateCodec.putControl,
    SequentialSharedStateCodec.putCursor,
    SequentialSharedStateCodec.putExpr,SequentialSharedStateCodec.putExprs,
    SequentialStackCodec.writeExpr,blocks_nil,blocks_cons,List.append_assoc]

theorem unchanged_streams (ns : List CBVtoCBN.CompileNode) (g : MGrammar) (entry : Entry)
    (m : Nat) (E : CaptureEnv) (p : Nat) (K : List SequentialSharedWords.Frame) :
    (encode ns (before entry m E p K)).words=(encode ns (after g entry m E p K)).words ∧
    SequentialSharedCursors.positions (before entry m E p K)=p :: K.filterMap SequentialSharedCursors.frameCursor ∧
    SequentialSharedCursors.positions (after g entry m E p K)=
      (if drops g entry then [] else [p]) ++ K.filterMap SequentialSharedCursors.frameCursor := by
  cases entry with
  | call i args =>
    cases hv : validCall g i args <;>
      simp [hv,encode,SequentialSharedStateCodec.write_words,before,after,beforeTask,nextTask,newFrame,drops,
    SequentialSharedWordSpace.retainedWords,SequentialSharedWordSpace.taskWords,
    SequentialSharedWordSpace.frameWords,SequentialSharedCursors.positions,
    SequentialSharedCursors.taskCursor,SequentialSharedCursors.frameCursor]
  | _ => simp [encode,SequentialSharedStateCodec.write_words,before,after,beforeTask,nextTask,newFrame,drops,
    SequentialSharedWordSpace.retainedWords,SequentialSharedWordSpace.taskWords,
    SequentialSharedWordSpace.frameWords,SequentialSharedCursors.positions,
    SequentialSharedCursors.taskCursor,SequentialSharedCursors.frameCursor]

theorem count_runs (inc : Bool) (a b : Nat) (C : List Nat) (L : Lists 8) {B : Nat}
    (hsrc : L 2=C ++ blocks [a,b]) (h1 : L 1=[]) (hL : LenOK B L)
    (hcap : (L 2).length+3 ≤ B) :
    ∃ T, Complexity.Runs (LenOK B) (countProgram inc) L
      (L.set 2 (C ++ blocks [a,b+if inc then 1 else 0])) T := by
  cases inc with
  | false =>
    have he : L.set 2 (C ++ blocks [a,b+0])=L := by rw [Nat.add_zero,← hsrc,Lists.set_get_self]
    simp only [Bool.false_eq_true,if_false]
    rw [he]
    exact ⟨1,runs_skip 2 hL⟩
  | true =>
    apply incrementSecond_runs (src := (2 : Fin 8)) (tmp := 1) (by decide) a b C L hsrc h1 hL
    rw [hsrc] at hcap
    simp only [blocks_cons,List.length_append,List.length_replicate,List.length_singleton] at hcap ⊢
    omega

private theorem next_reachable {g : MGrammar} {x : List Char} {a b c : Config}
    (h : Runs g x a b) (hs : SequentialSharedWords.step g x b=some c) : Runs g x a c := by
  induction h with
  | refl => exact .cons hs (.refl _)
  | cons hh ht ih => exact .cons hh (ih hs)

theorem transition_runs (g : MGrammar) (x : List Char) (e : MExp) (entry : Entry) (m : Nat)
    (E : CaptureEnv) (p : Nat) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before entry m E p K)) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (program (CBVtoCBN.compilerNodes g e) g entry)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (before entry m E p K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (after g entry m E p K)) x) T := by
  let ns := CBVtoCBN.compilerNodes g e
  let B := (SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3
  let L := withInput (encode ns (before entry m E p K)) x
  let target := withInput (encode ns (after g entry m E p K)) x
  let ps := K.filterMap SequentialSharedCursors.frameCursor
  have hb := SequentialSharedStateBound.encoded_state_linear g x e _ h
  change (encode ns (before entry m E p K)).length ≤ _ at hb
  have hi : x.length+2 ≤ B := by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega
  have hL : LenOK B L := SequentialCaptureCopyMachine.withInput_fits _ x
    (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega) hi
  have hLmore : LenOK (B-1) L := SequentialCaptureCopyMachine.withInput_fits _ x
    (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega)
    (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega)
  have hs := next_reachable h (actual_step g x entry m E p K)
  have hba := SequentialSharedStateBound.encoded_state_linear g x e _ hs
  change (encode ns (after g entry m E p K)).length ≤ _ at hba
  have htarget : LenOK B target := SequentialCaptureCopyMachine.withInput_fits _ x
    (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega) hi
  obtain ⟨hw,hpos,hapos⟩ := unchanged_streams ns g entry m E p K
  have hcur : L 0=cursors (p :: ps) := by
    change SequentialCursorEntryMachine.layout (encode ns (before entry m E p K)) 0 = _
    rw [SequentialCursorEntryMachine.layout_cursors,hpos]
  have hc := SequentialSharedCursors.reachable_chain g x e _ h
  rw [hpos] at hc
  cases hc with
  | cons hz hc =>
    let qs := if drops g entry then ps else p :: ps
    let M := L.set 0 (cursors qs)
    have hd : ∃ T, Complexity.Runs (LenOK B) (if drops g entry then dropBlock 0 1 else skipP 0) L M T := by
      cases hh : drops g entry with
      | true => simpa [M,qs,hh] using drop_current_runs (src := (0 : Fin 8)) (tmp := 1) (by decide) hc L hcur rfl hL
      | false =>
        have he : M=L := by dsimp [M,qs]; rw [hh]; simp only [Bool.false_eq_true,if_false,← hcur,Lists.set_get_self]
        rw [he]
        exact ⟨1,runs_skip 0 hL⟩
    obtain ⟨Td,hd⟩ := hd
    have hctrl : M 2=blocks (writeFrames ns K).control ++ blocks (oldFields ns entry) ++ blocks [E.length,K.length] :=
      (fields ns g entry m E p K).1
    obtain ⟨Tc,hc⟩ := count_runs (count g entry) E.length K.length
      (blocks (writeFrames ns K).control ++ blocks (oldFields ns entry)) M hctrl rfl (end_fits hd)
      (by have hh := hLmore 2; simpa [M,Lists.set] using (show (L 2).length+3 ≤ B by omega))
    let N := M.set 2 (blocks (writeFrames ns K).control ++ blocks (oldFields ns entry) ++
      blocks [E.length,K.length+if count g entry then 1 else 0])
    obtain ⟨Tr,hr⟩ := replace_runs (src := (2 : Fin 8)) (tmp := 1) (by decide)
      [E.length,K.length+if count g entry then 1 else 0] (oldFields ns entry) (freshFields ns g entry)
      (blocks (writeFrames ns K).control) N rfl rfl (end_fits hc) (by
        rw [← (fields ns g entry m E p K).2]
        exact htarget 2)
    have he2 : blocks (writeFrames ns K).control ++ blocks (freshFields ns g entry) ++
        blocks [E.length,K.length+if count g entry then 1 else 0]=target 2 := (fields ns g entry m E p K).2.symm
    have he0 : cursors qs=target 0 := by
      change _=SequentialCursorEntryMachine.layout (encode ns (after g entry m E p K)) 0
      rw [SequentialCursorEntryMachine.layout_cursors,hapos]
      cases hh : drops g entry <;> simp [qs,ps,hh]
    have he4 : L 4=target 4 := by
      change ((encode ns (before entry m E p K)).words.map SequentialCaptureCopyMachine.wordSymbol).reverse =
        ((encode ns (after g entry m E p K)).words.map SequentialCaptureCopyMachine.wordSymbol).reverse
      rw [hw]
    have hu := SequentialArgCapturePackedMachine.withInput_update (encode ns (before entry m E p K))
      (encode ns (after g entry m E p K)) x (by rfl)
    change ((L.set 4 (target 4)).set 0 (target 0)).set 2 (target 2)=target at hu
    rw [← he4,Lists.set_get_self] at hu
    have he : N.set 2 (blocks (writeFrames ns K).control ++ blocks (freshFields ns g entry) ++
        blocks [E.length,K.length+if count g entry then 1 else 0])=target := by
      simpa only [N,M,Lists.set_set_u,he2,he0] using hu
    rw [he] at hr
    exact ⟨_,hd.seq (hc.seq hr)⟩

theorem transition_tape (g : MGrammar) (x : List Char) (e : MExp) (entry : Entry) (m : Nat)
    (E : CaptureEnv) (p : Nat) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before entry m E p K)) (tau : Tapes 8)
    (hrep : Rep (withInput (encode (CBVtoCBN.compilerNodes g e) (before entry m E p K)) x) tau) :
    ∃ t tau', Exec (TFits ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (program (CBVtoCBN.compilerNodes g e) g entry).compile tau t (.cont tau') ∧
      Rep (withInput (encode (CBVtoCBN.compilerNodes g e) (after g entry m E p K)) x) tau' := by
  obtain ⟨T,hr⟩ := transition_runs g x e entry m E p K h
  exact tape_runs hr tau hrep

theorem finite_alphabet (ns : List CBVtoCBN.CompileNode) (g : MGrammar) (entry : Entry)
    (E : Nat) (hE : 2 ≤ E) : (program ns g entry).compile.SymOK (E+4) := by
  apply compile_symOK E
  have hd : (dropBlock (0 : Fin 8) 1).ConstOK E := by simp [dropBlock,scan,moveTop,moveAll,clearP,LProg.ConstOK]
  have hc : (countProgram (count g entry)).ConstOK E := by
    unfold countProgram
    split
    · exact incrementSecond_constOK hE _ _
    · trivial
  refine ⟨?_,hc,replace_constOK hE _ _ _ _ _⟩
  split
  · exact hd
  · trivial

end Shallot.MacroPeg.CBV.SequentialStaticPackedMachine
