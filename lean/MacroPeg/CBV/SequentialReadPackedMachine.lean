import MacroPeg.CBV.SequentialReadTests

/-! Complete compressed transitions for source-fixed reads, including literal
strings of arbitrary source-fixed length and all Unicode character ranges. -/
namespace Shallot.MacroPeg.CBV.SequentialReadPackedMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialControlEditMachine
open SequentialSharedWords (Config CaptureEnv Runs initial)
open SequentialSharedStateCodec (encode write writeTask writeFrames Input)
open SequentialCaptureCopyMachine (withInput)
open SequentialReadTests (Read expr tests)

def matched (read : Read) (x : List Char) (p : Nat) : Option (List Char) :=
  SequentialTokenMatchMachine.runTests (tests read) (sfx x p)

def before (read : Read) (m : Nat) (E : CaptureEnv) (p : Nat)
    (K : List SequentialSharedWords.Frame) : Config := ⟨m,.expr (expr read) p,E,K⟩

def after (x : List Char) (read : Read) (m : Nat) (E : CaptureEnv) (p : Nat)
    (K : List SequentialSharedWords.Frame) : Config :=
  ⟨m,.value (.expr (some ((matched read x p).map List.length))),E,K⟩

abbrev tag := SequentialParamPackedMachine.tag

theorem actual_step (g : MGrammar) (x : List Char) (read : Read) (m : Nat) (E : CaptureEnv)
    (p : Nat) (K : List SequentialSharedWords.Frame) (hp : p ≤ x.length) :
    SequentialSharedWords.step g x (before read m E p K) = some (after x read m E p K) := by
  have ha := SequentialReadTests.atom_result read x E p hp
  cases read <;> simpa only [before,after,SequentialReadTests.expr,SequentialSharedWords.step,matched] using
    congrArg (fun r => some (⟨m,.value (.expr r),E,K⟩ : Config)) ha

def program (read : Read) : LProg 8 := .seq (SequentialTokenInputMachine.program (tests read))
  SequentialParamPackedMachine.finish

theorem before_control (ns : List CBVtoCBN.CompileNode) (read : Read) (m : Nat) (E : CaptureEnv) (p : Nat)
    (K : List SequentialSharedWords.Frame) :
    withInput (encode ns (before read m E p K)) [] 2 =
      blocks (writeFrames ns K).control ++ blocks [0,SequentialStackCodec.exprId ns (expr read)] ++
        blocks [E.length,K.length] := by
  change SequentialCursorEntryMachine.layout (encode ns (before read m E p K)) 2 = _
  rw [SequentialAnyPackedMachine.layout_control]
  have hw : (write ns (before read m E p K)).control =
      [E.length,K.length] ++ [0,SequentialStackCodec.exprId ns (expr read)] ++ (writeFrames ns K).control := by
    simp [write,before,writeTask,Input.append,SequentialSharedStateCodec.putControl,
      SequentialSharedStateCodec.putWords,SequentialSharedStateCodec.putExpr,
      SequentialSharedStateCodec.putCursor,SequentialStackCodec.writeExpr]
  rw [hw,blocks_append,blocks_append]
  simp only [List.append_assoc]

theorem after_control (ns : List CBVtoCBN.CompileNode) (x : List Char) (read : Read) (m : Nat)
    (E : CaptureEnv) (p : Nat) (K : List SequentialSharedWords.Frame) :
    withInput (encode ns (after x read m E p K)) x 2 =
      blocks (writeFrames ns K).control ++ blocks [3,tag (matched read x p)] ++ blocks [E.length,K.length] := by
  change SequentialCursorEntryMachine.layout (encode ns (after x read m E p K)) 2 = _
  rw [SequentialAnyPackedMachine.layout_control]
  have hw : (write ns (after x read m E p K)).control =
      [E.length,K.length] ++ [3,tag (matched read x p)] ++ (writeFrames ns K).control := by
    cases hr : matched read x p <;>
      simp [write,after,writeTask,Input.append,SequentialSharedStateCodec.putControl,
        SequentialSharedStateCodec.putWords,SequentialSharedStateCodec.putCursor,hr,tag,SequentialParamPackedMachine.tag]
  rw [hw,blocks_append,blocks_append]
  simp only [List.append_assoc]

private theorem next_reachable {g : MGrammar} {x : List Char} {a b c : Config}
    (h : Runs g x a b) (hs : SequentialSharedWords.step g x b = some c) : Runs g x a c := by
  induction h with
  | refl => exact .cons hs (.refl _)
  | cons hh ht ih => exact .cons hh (ih hs)

/-- Execute an actual initialized reachable reading-primitive task through its
complete encoded successor, preserving clock, environments, and original input. -/
theorem transition_runs (g : MGrammar) (x : List Char) (e : MExp) (read : Read) (m : Nat)
    (E : CaptureEnv) (p : Nat) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before read m E p K)) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (program read) (withInput (encode (CBVtoCBN.compilerNodes g e) (before read m E p K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (after x read m E p K)) x) T := by
  let ns := CBVtoCBN.compilerNodes g e
  let B := (SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3
  let L := withInput (encode ns (before read m E p K)) x
  let target := withInput (encode ns (after x read m E p K)) x
  let ps := K.filterMap SequentialSharedCursors.frameCursor
  let r := matched read x p
  have hb := SequentialSharedStateBound.encoded_state_linear g x e _ h
  change (encode ns (before read m E p K)).length ≤ _ at hb
  have hi : x.length+2 ≤ B := by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega
  have hL : LenOK B L := SequentialCaptureCopyMachine.withInput_fits _ x
    (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega) hi
  have hLmore : LenOK (B-1) L := SequentialCaptureCopyMachine.withInput_fits _ x
    (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega)
    (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega)
  have hchain := SequentialSharedCursors.reachable_chain g x e _ h
  have hpos : SequentialSharedCursors.positions (before read m E p K)=p :: ps := rfl
  rw [hpos] at hchain
  cases hchain with
  | cons hz hc =>
    have hcur : L 0=cursors (p :: ps) := by
      change SequentialCursorEntryMachine.layout (encode ns (before read m E p K)) 0 = _
      rw [SequentialCursorEntryMachine.layout_cursors,hpos]
    obtain ⟨Tm,hm⟩ := SequentialTokenInputMachine.original_input_runs (tests read) x p ps hc hc.bound L
      hcur rfl rfl rfl hL (by have hh := hLmore 2; omega)
    let M := SequentialParamMatchMachine.result L ps r
    have hM : LenOK B M := end_fits hm
    have hs := next_reachable h (actual_step g x read m E p K hc.bound)
    have hba := SequentialSharedStateBound.encoded_state_linear g x e _ hs
    change (encode ns (after x read m E p K)).length ≤ _ at hba
    have htarget : LenOK B target := SequentialCaptureCopyMachine.withInput_fits _ x
      (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega) hi
    have hsrc : M 2=(blocks (writeFrames ns K).control ++
        blocks [0,SequentialStackCodec.exprId ns (expr read)] ++ blocks [E.length,K.length]) ++
          [if r.isSome then 1 else 0] := by
      change L 2 ++ _ = _
      change withInput (encode ns (before read m E p K)) [] 2 ++ _ = _
      rw [before_control]
    obtain ⟨Tf,hf⟩ := SequentialParamPackedMachine.finish_runs r [E.length,K.length] (SequentialStackCodec.exprId ns (expr read))
      (blocks (writeFrames ns K).control) M hsrc rfl rfl hM (by
        rw [← after_control ns x read m E p K]
        exact htarget 2)
    have he2 : blocks (writeFrames ns K).control ++ blocks [3,tag r] ++ blocks [E.length,K.length] = target 2 :=
      (after_control ns x read m E p K).symm
    have he0 : cursors ((r.map List.length).toList ++ ps)=target 0 := by
      change _=SequentialCursorEntryMachine.layout (encode ns (after x read m E p K)) 0
      rw [SequentialCursorEntryMachine.layout_cursors]
      cases hr : matched read x p <;>
        simp [r,after,SequentialSharedCursors.positions,SequentialSharedCursors.taskCursor,hr,ps]
    have he4 : L 4=target 4 := by
      change ( (encode ns (before read m E p K)).words.map SequentialCaptureCopyMachine.wordSymbol).reverse =
        ((encode ns (after x read m E p K)).words.map SequentialCaptureCopyMachine.wordSymbol).reverse
      have hw : (encode ns (before read m E p K)).words=(encode ns (after x read m E p K)).words := by
        cases hr : matched read x p <;>
          simp [encode,SequentialSharedStateCodec.write_words,before,after,hr,
            SequentialSharedWordSpace.retainedWords,SequentialSharedWordSpace.taskWords]
      rw [hw]
    have hu := SequentialArgCapturePackedMachine.withInput_update (encode ns (before read m E p K))
      (encode ns (after x read m E p K)) x (by rfl)
    change ((L.set 4 (target 4)).set 0 (target 0)).set 2 (target 2)=target at hu
    rw [← he4,Lists.set_get_self] at hu
    have he : M.set 2 (blocks (writeFrames ns K).control ++ blocks [3,tag r] ++ blocks [E.length,K.length])=target := by
      rw [he2]
      have hh : M.set 2 (target 2)=(L.set 0 (target 0)).set 2 (target 2) := by
        funext j
        by_cases h0 : j=0 <;> by_cases h2 : j=2 <;>
          simp [M,SequentialParamMatchMachine.result,Lists.set,h0,h2,he0]
      rw [hh]
      exact hu
    rw [he] at hf
    exact ⟨_,hm.seq hf⟩

theorem transition_tape (g : MGrammar) (x : List Char) (e : MExp) (read : Read) (m : Nat)
    (E : CaptureEnv) (p : Nat) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before read m E p K)) (tau : Tapes 8)
    (hrep : Rep (withInput (encode (CBVtoCBN.compilerNodes g e) (before read m E p K)) x) tau) :
    ∃ t tau', Exec (TFits ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (program read).compile tau t (.cont tau') ∧
      Rep (withInput (encode (CBVtoCBN.compilerNodes g e) (after x read m E p K)) x) tau' := by
  obtain ⟨T,hr⟩ := transition_runs g x e read m E p K h
  exact tape_runs hr tau hrep

theorem finite_alphabet (read : Read) (E : Nat) (hE : 2 ≤ E) : (program read).compile.SymOK (E+4) := by
  apply compile_symOK E
  have hb (t : Nat) : (SequentialParamPackedMachine.finishBranch t).ConstOK E :=
    ⟨trivial,replace_constOK hE _ _ _ _ _⟩
  exact ⟨SequentialTokenInputMachine.constOK (tests read) E hE,hb 2,hb 1⟩

end Shallot.MacroPeg.CBV.SequentialReadPackedMachine
