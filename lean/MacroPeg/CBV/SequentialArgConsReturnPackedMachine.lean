import MacroPeg.CBV.SequentialArgConsPackedMachine

/-! Complete runtime-dispatched capture-cons returns on eight packed tapes. -/
namespace Shallot.MacroPeg.CBV.SequentialArgConsReturnPackedMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialControlEditMachine
open SequentialReturnControlMachine
open SequentialSharedWords (Config CaptureEnv ArgsResult Runs initial)
open SequentialSharedStateCodec (encode write writeTask writeFrames Input)
open SequentialCaptureCopyMachine (withInput wordTape wordCode)
open SequentialArgHeadPackedMachine (bad badTag)

def before (m : Nat) (E : CaptureEnv) (w : List Char) (r : ArgsResult)
    (K : List SequentialSharedWords.Frame) : Config := ⟨m,.value (.args r),E,.argCons w :: K⟩

def after (m : Nat) (E : CaptureEnv) (w : List Char) (r : ArgsResult)
    (K : List SequentialSharedWords.Frame) : Config :=
  ⟨m,.value (.args (match r with | some (some (W,q)) => some (some (w :: W,q)) | r => r)),E,K⟩

def resultTag : ArgsResult → Nat
  | none => 0
  | some none => 1
  | some (some _) => 2

def extraFields : ArgsResult → List Nat
  | some (some (W,_)) => [W.length]
  | _ => []

theorem actual_step (g : MGrammar) (x : List Char) (m : Nat) (E : CaptureEnv)
    (w : List Char) (r : ArgsResult) (K : List SequentialSharedWords.Frame) :
    SequentialSharedWords.step g x (before m E w r K) = some (after m E w r K) := rfl

def badAfter (failure : Bool) (m : Nat) (E : CaptureEnv) (K : List SequentialSharedWords.Frame) : Config :=
  ⟨m,.value (.args (bad failure)),E,K⟩

def badProgram : LProg 8 := .seq SequentialWordRotateMachine.discard
  (.seq (decrementSecond 2 1) (replace 2 1 4 1 []))

def program : LProg 8 := dispatch 2 1 3 badProgram badProgram SequentialArgConsPackedMachine.program

theorem before_control (ns : List CBVtoCBN.CompileNode) (x : List Char) (m : Nat) (E : CaptureEnv)
    (w : List Char) (r : ArgsResult) (K : List SequentialSharedWords.Frame) :
    withInput (encode ns (before m E w r K)) x 2 =
      (blocks (writeFrames ns K).control ++ blocks [5] ++ blocks (extraFields r)) ++
        blocks [resultTag r] ++ blocks [E.length,K.length+1,4] := by
  change SequentialCursorEntryMachine.layout (encode ns (before m E w r K)) 2 = _
  rw [SequentialAnyPackedMachine.layout_control]
  have he : (write ns (before m E w r K)).control =
      [E.length,K.length+1,4] ++ [resultTag r] ++ extraFields r ++ [5] ++ (writeFrames ns K).control := by
    cases r with
    | none => simp [write,before,resultTag,extraFields,writeTask,writeFrames,SequentialSharedStateCodec.writeFrame,
        Input.append,SequentialSharedStateCodec.putControl,SequentialSharedStateCodec.putWords]
    | some v => cases v with
      | none => simp [write,before,resultTag,extraFields,writeTask,writeFrames,SequentialSharedStateCodec.writeFrame,
          Input.append,SequentialSharedStateCodec.putControl,SequentialSharedStateCodec.putWords]
      | some Wq => rcases Wq with ⟨W,q⟩; simp [write,before,resultTag,extraFields,writeTask,writeFrames,
          SequentialSharedStateCodec.writeFrame,Input.append,SequentialSharedStateCodec.putControl,
          SequentialSharedStateCodec.putWords,SequentialSharedStateCodec.putCursor]
  rw [he,blocks_append,blocks_append,blocks_append,blocks_append]
  simp only [List.append_assoc]

theorem bad_before_control (ns : List CBVtoCBN.CompileNode) (x : List Char) (failure : Bool)
    (m : Nat) (E : CaptureEnv) (w : List Char) (K : List SequentialSharedWords.Frame) :
    withInput (encode ns (before m E w (bad failure) K)) x 2 =
      blocks (writeFrames ns K).control ++ blocks [5] ++ blocks [E.length,K.length+1,4,badTag failure] := by
  rw [before_control]
  cases failure <;> simp [bad,badTag,resultTag,extraFields,blocks,bits,
    SequentialCursorChain.encodeDeltas,List.append_assoc]

theorem bad_after_control (ns : List CBVtoCBN.CompileNode) (x : List Char) (failure : Bool)
    (m : Nat) (E : CaptureEnv) (K : List SequentialSharedWords.Frame) :
    withInput (encode ns (badAfter failure m E K)) x 2 =
      blocks (writeFrames ns K).control ++ blocks [E.length,K.length,4,badTag failure] := by
  change SequentialCursorEntryMachine.layout (encode ns (badAfter failure m E K)) 2 = _
  rw [SequentialAnyPackedMachine.layout_control]
  have he : (write ns (badAfter failure m E K)).control =
      [E.length,K.length,4,badTag failure] ++ (writeFrames ns K).control := by
    cases failure <;> simp [write,badAfter,bad,badTag,writeTask,Input.append,
      SequentialSharedStateCodec.putControl,SequentialSharedStateCodec.putWords]
  rw [he,blocks_append]

theorem bad_words (ns : List CBVtoCBN.CompileNode) (x : List Char) (failure : Bool)
    (m : Nat) (E : CaptureEnv) (w : List Char) (K : List SequentialSharedWords.Frame) :
    withInput (encode ns (before m E w (bad failure) K)) x 4 =
      wordTape (K.flatMap SequentialSharedWordSpace.frameWords) ++ wordCode w ++ wordTape E ∧
    withInput (encode ns (badAfter failure m E K)) x 4 =
      wordTape (K.flatMap SequentialSharedWordSpace.frameWords) ++ wordTape E := by
  have hb : (encode ns (before m E w (bad failure) K)).words =
      SequentialSharedWordSpace.encodeWords (E ++ w :: K.flatMap SequentialSharedWordSpace.frameWords) := by
    cases failure <;> simp [encode,SequentialSharedStateCodec.write_words,before,bad,
      SequentialSharedWordSpace.retainedWords,SequentialSharedWordSpace.taskWords,SequentialSharedWordSpace.frameWords]
  have ha : (encode ns (badAfter failure m E K)).words =
      SequentialSharedWordSpace.encodeWords (E ++ K.flatMap SequentialSharedWordSpace.frameWords) := by
    cases failure <;> simp [encode,SequentialSharedStateCodec.write_words,badAfter,bad,
      SequentialSharedWordSpace.retainedWords,SequentialSharedWordSpace.taskWords]
  constructor
  · change ((encode ns (before m E w (bad failure) K)).words.map SequentialCaptureCopyMachine.wordSymbol).reverse = _
    rw [hb]
    change wordTape (E ++ w :: K.flatMap SequentialSharedWordSpace.frameWords) = _
    rw [SequentialCaptureCopyMachine.wordTape_append,SequentialCaptureSpliceMachine.wordTape_cons]
  · change ((encode ns (badAfter failure m E K)).words.map SequentialCaptureCopyMachine.wordSymbol).reverse = _
    rw [ha]
    exact SequentialCaptureCopyMachine.wordTape_append E _

private theorem next_reachable {g : MGrammar} {x : List Char} {a b c : Config}
    (h : Runs g x a b) (hs : SequentialSharedWords.step g x b = some c) : Runs g x a c := by
  induction h with
  | refl => exact .cons hs (.refl _)
  | cons hh ht ih => exact .cons hh (ih hs)

theorem bad_runs (g : MGrammar) (x : List Char) (e : MExp) (failure : Bool) (m : Nat)
    (E : CaptureEnv) (w : List Char) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before m E w (bad failure) K)) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      badProgram (withInput (encode (CBVtoCBN.compilerNodes g e) (before m E w (bad failure) K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (badAfter failure m E K)) x) T := by
  let ns := CBVtoCBN.compilerNodes g e
  let B := (SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3
  let L := withInput (encode ns (before m E w (bad failure) K)) x
  let target := withInput (encode ns (badAfter failure m E K)) x
  have hb := SequentialSharedStateBound.encoded_state_linear g x e _ h
  change (encode ns (before m E w (bad failure) K)).length ≤ _ at hb
  have hx : x.length+2 ≤ B := by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega
  have hL : LenOK B L := SequentialCaptureCopyMachine.withInput_fits _ x
    (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega) hx
  have hs : SequentialSharedWords.step g x (before m E w (bad failure) K) = some (badAfter failure m E K) := by
    cases failure <;> rfl
  have ha := next_reachable h hs
  have hba := SequentialSharedStateBound.encoded_state_linear g x e _ ha
  change (encode ns (badAfter failure m E K)).length ≤ _ at hba
  have htarget : LenOK B target := SequentialCaptureCopyMachine.withInput_fits _ x
    (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega) hx
  let C := (blocks (writeFrames ns K).control ++ blocks [5] ++ blocks [K.length+1,4,badTag failure]) ++ [0]
  have hcontrol : L 2 = C ++ unary E.length := by
    dsimp only [L]
    rw [bad_before_control,blocks_cons E.length [K.length+1,4,badTag failure]]
    simp only [C,List.append_assoc]
  obtain ⟨Tw,hw⟩ := SequentialWordRotateMachine.discard_runs E w C
    (wordTape (K.flatMap SequentialSharedWordSpace.frameWords)) L hcontrol
    (by rw [lastSym_append]; rfl) (bad_words ns x failure m E w K).1 rfl rfl rfl hL
  let M := L.set 4 (wordTape (K.flatMap SequentialSharedWordSpace.frameWords) ++ wordTape E)
  have hm2 : M 2 = (blocks (writeFrames ns K).control ++ blocks [5] ++ blocks [4,badTag failure]) ++
      blocks [E.length,K.length+1] := by
    change withInput (encode ns (before m E w (bad failure) K)) x 2 = _
    rw [bad_before_control]
    rw [show [E.length,K.length+1,4,badTag failure] = [E.length,K.length+1] ++ [4,badTag failure] from rfl,blocks_append]
    simp only [List.append_assoc]
  obtain ⟨Td,hd⟩ := decrementSecond_runs (src := (2 : Fin 8)) (tmp := 1) (by decide) E.length K.length
    (blocks (writeFrames ns K).control ++ blocks [5] ++ blocks [4,badTag failure]) M hm2 rfl (end_fits hw)
  let N := M.set 2 ((blocks (writeFrames ns K).control ++ blocks [5] ++ blocks [4,badTag failure]) ++
    blocks [E.length,K.length])
  have hn2 : N 2 = blocks (writeFrames ns K).control ++ blocks [5] ++ blocks [E.length,K.length,4,badTag failure] := by
    simp only [N,Lists.set_same]
    rw [show [E.length,K.length,4,badTag failure] = [E.length,K.length] ++ [4,badTag failure] from rfl,blocks_append]
    simp only [List.append_assoc]
  have hcap : (blocks (writeFrames ns K).control ++ blocks [] ++ blocks [E.length,K.length,4,badTag failure]).length+2 ≤ B := by
    have he : blocks (writeFrames ns K).control ++ blocks [] ++ blocks [E.length,K.length,4,badTag failure] = target 2 := by
      dsimp only [target]
      rw [bad_after_control]
      simp [blocks,bits,SequentialCursorChain.encodeDeltas]
    rw [he]; exact htarget 2
  obtain ⟨Tr,hr⟩ := replace_runs (src := (2 : Fin 8)) (tmp := 1) (by decide)
    [E.length,K.length,4,badTag failure] [5] [] (blocks (writeFrames ns K).control) N hn2 rfl (end_fits hd) hcap
  have he : N.set 2 (blocks (writeFrames ns K).control ++ blocks [] ++ blocks [E.length,K.length,4,badTag failure]) = target := by
    have hectrl : blocks (writeFrames ns K).control ++ blocks [] ++ blocks [E.length,K.length,4,badTag failure] = target 2 := by
      dsimp only [target]; rw [bad_after_control]; simp [blocks,bits,SequentialCursorChain.encodeDeltas]
    have hew : wordTape (K.flatMap SequentialSharedWordSpace.frameWords) ++ wordTape E = target 4 :=
      (bad_words ns x failure m E w K).2.symm
    have hec : (L.set 4 (target 4)) 0 = target 0 := by
      change SequentialCursorEntryMachine.layout (encode ns (before m E w (bad failure) K)) 0 =
        SequentialCursorEntryMachine.layout (encode ns (badAfter failure m E K)) 0
      rw [SequentialCursorEntryMachine.layout_cursors,SequentialCursorEntryMachine.layout_cursors]
      cases failure <;> rfl
    dsimp only [N]
    rw [Lists.set_set_u,hectrl]
    dsimp only [M]
    rw [hew]
    have hu := SequentialArgCapturePackedMachine.withInput_update (encode ns (before m E w (bad failure) K))
      (encode ns (badAfter failure m E K)) x rfl
    change (((L.set 4 (target 4)).set 0 (target 0)).set 2 (target 2)) = target at hu
    rwa [← hec,Lists.set_get_self] at hu
  rw [he] at hr
  exact ⟨_,hw.seq (hd.seq hr)⟩

theorem transition_runs (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E : CaptureEnv)
    (w : List Char) (r : ArgsResult) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before m E w r K)) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      program (withInput (encode (CBVtoCBN.compilerNodes g e) (before m E w r K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (after m E w r K)) x) T := by
  let ns := CBVtoCBN.compilerNodes g e
  let B := (SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3
  let L := withInput (encode ns (before m E w r K)) x
  let target := withInput (encode ns (after m E w r K)) x
  obtain ⟨T,hr⟩ : ∃ T, Complexity.Runs (LenOK B)
      (select (resultTag r) badProgram badProgram SequentialArgConsPackedMachine.program) L target T := by
    cases r with
    | none => simpa [select,resultTag,bad,badAfter,after,L,target,ns,B] using bad_runs g x e false m E w K h
    | some v => cases v with
      | none => simpa [select,resultTag,bad,badAfter,after,L,target,ns,B] using bad_runs g x e true m E w K h
      | some Wq => rcases Wq with ⟨W,q⟩
                   simpa [select,resultTag,before,after,SequentialArgConsPackedMachine.before,
                     SequentialArgConsPackedMachine.after,L,target,ns,B] using
                     SequentialArgConsPackedMachine.transition_runs g x e m E W w q K h
  have hb := SequentialSharedStateBound.encoded_state_linear g x e _ h
  change (encode ns (before m E w r K)).length ≤ _ at hb
  have hL : LenOK B L := SequentialCaptureCopyMachine.withInput_fits _ x
    (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega)
    (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega)
  have htag : resultTag r ≤ 2 := by cases r with
    | none => decide
    | some v => cases v <;> simp [resultTag]
  exact dispatch_runs (src := (2 : Fin 8)) (tmp := 1) (by decide) [E.length,K.length+1,4]
    (resultTag r) htag (blocks (writeFrames ns K).control ++ blocks [5] ++ blocks (extraFields r))
    badProgram badProgram SequentialArgConsPackedMachine.program L target
    (before_control ns x m E w r K) rfl hL hr

theorem transition_tape (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E : CaptureEnv)
    (w : List Char) (r : ArgsResult) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before m E w r K)) (τ : Tapes 8)
    (hrep : Rep (withInput (encode (CBVtoCBN.compilerNodes g e) (before m E w r K)) x) τ) :
    ∃ t τ', Exec (TFits ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      program.compile τ t (.cont τ') ∧
      Rep (withInput (encode (CBVtoCBN.compilerNodes g e) (after m E w r K)) x) τ' := by
  obtain ⟨T,hr⟩ := transition_runs g x e m E w r K h
  exact tape_runs hr τ hrep

theorem finite_alphabet (E : Nat) (hE : 2 ≤ E) : program.compile.SymOK (E+4) := by
  apply compile_symOK E
  have hb : badProgram.ConstOK E :=
    ⟨SequentialWordRotateMachine.discard_constOK E,decrementSecond_constOK E _ _,replace_constOK hE _ _ _ _ _⟩
  exact dispatch_constOK E _ _ _ _ _ _ hb hb (SequentialArgConsPackedMachine.constOK E hE)

end Shallot.MacroPeg.CBV.SequentialArgConsReturnPackedMachine
