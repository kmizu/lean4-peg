import MacroPeg.CBV.SequentialScopeWordMachine

/-! Complete scope returns for both expression and argument values. The
program reads their task and result tags and preserves task-owned captures. -/
namespace Shallot.MacroPeg.CBV.SequentialScopePackedMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialControlEditMachine
open SequentialSharedWords (Config CaptureEnv Runs initial)
abbrev ReturnValue := SequentialSharedWords.Value
open SequentialSharedStateCodec (Packed encode write writeTask writeFrames Input)
open SequentialCaptureCopyMachine (withInput wordTape)
open SequentialScopeWordMachine (resultFields resultWords wordProgram)

private theorem blocks_nil : blocks [] = [] := rfl

def before (m : Nat) (E S : CaptureEnv) (v : ReturnValue) (K : List SequentialSharedWords.Frame) : Config :=
  ⟨m,.value v,E,.scope S :: K⟩

def after (m : Nat) (S : CaptureEnv) (v : ReturnValue) (K : List SequentialSharedWords.Frame) : Config :=
  ⟨m+1,.value v,S,K⟩

theorem actual_step (g : MGrammar) (x : List Char) (m : Nat) (E S : CaptureEnv)
    (v : ReturnValue) (K : List SequentialSharedWords.Frame) :
    SequentialSharedWords.step g x (before m E S v K) = some (after m S v K) := by cases v <;> rfl

private theorem fields_write (ns : List CBVtoCBN.CompileNode) (v : ReturnValue) :
    (writeTask ns (.value v)).control = resultFields v := by
  cases v with
  | expr r => cases r with
    | none => rfl
    | some value => cases value <;> rfl
  | args r => cases r with
    | none => rfl
    | some value => cases value with
      | none => rfl
      | some Vq => rcases Vq with ⟨V,q⟩; rfl

theorem before_control (ns : List CBVtoCBN.CompileNode) (x : List Char) (m : Nat) (E S : CaptureEnv)
    (v : ReturnValue) (K : List SequentialSharedWords.Frame) :
    withInput (encode ns (before m E S v K)) x 2 = blocks (writeFrames ns K).control ++
      blocks [7,S.length] ++ blocks (resultFields v) ++ blocks [E.length,K.length+1] := by
  change SequentialCursorEntryMachine.layout (encode ns (before m E S v K)) 2 = _
  rw [SequentialAnyPackedMachine.layout_control]
  have he : (write ns (before m E S v K)).control =
      [E.length,K.length+1] ++ resultFields v ++ [7,S.length] ++ (writeFrames ns K).control := by
    simp [write,before,writeFrames,SequentialSharedStateCodec.writeFrame,fields_write,Input.append,
      SequentialSharedStateCodec.putControl,SequentialSharedStateCodec.putWords,List.append_assoc]
  rw [he,blocks_append,blocks_append,blocks_append]
  simp only [List.append_assoc]

theorem after_control (ns : List CBVtoCBN.CompileNode) (x : List Char) (m : Nat) (S : CaptureEnv)
    (v : ReturnValue) (K : List SequentialSharedWords.Frame) :
    withInput (encode ns (after m S v K)) x 2 =
      blocks (writeFrames ns K).control ++ blocks ([S.length,K.length] ++ resultFields v) := by
  change SequentialCursorEntryMachine.layout (encode ns (after m S v K)) 2 = _
  rw [SequentialAnyPackedMachine.layout_control]
  have he : (write ns (after m S v K)).control =
      ([S.length,K.length] ++ resultFields v) ++ (writeFrames ns K).control := by
    simp [write,after,fields_write,Input.append,SequentialSharedStateCodec.putControl,
      SequentialSharedStateCodec.putWords]
  rw [he,blocks_append]

theorem word_streams (ns : List CBVtoCBN.CompileNode) (x : List Char) (m : Nat) (E S : CaptureEnv)
    (v : ReturnValue) (K : List SequentialSharedWords.Frame) :
    withInput (encode ns (before m E S v K)) x 4 = wordTape (S ++ K.flatMap SequentialSharedWordSpace.frameWords) ++
      wordTape E ++ wordTape (resultWords v) ∧
    withInput (encode ns (after m S v K)) x 4 = wordTape (S ++ K.flatMap SequentialSharedWordSpace.frameWords) ++
      wordTape (resultWords v) := by
  have hb : (encode ns (before m E S v K)).words = SequentialSharedWordSpace.encodeWords
      (resultWords v ++ (E ++ (S ++ K.flatMap SequentialSharedWordSpace.frameWords))) := by
    simp [encode,SequentialSharedStateCodec.write_words,before,SequentialSharedWordSpace.retainedWords,
      SequentialSharedWordSpace.frameWords,resultWords,List.append_assoc]
  have ha : (encode ns (after m S v K)).words = SequentialSharedWordSpace.encodeWords
      (resultWords v ++ (S ++ K.flatMap SequentialSharedWordSpace.frameWords)) := by
    simp [encode,SequentialSharedStateCodec.write_words,after,SequentialSharedWordSpace.retainedWords,resultWords]
  constructor
  · change ((encode ns (before m E S v K)).words.map SequentialCaptureCopyMachine.wordSymbol).reverse = _
    rw [hb]
    change wordTape (resultWords v ++ (E ++ (S ++ K.flatMap SequentialSharedWordSpace.frameWords))) = _
    rw [SequentialCaptureCopyMachine.wordTape_append,SequentialCaptureCopyMachine.wordTape_append]
  · change ((encode ns (after m S v K)).words.map SequentialCaptureCopyMachine.wordSymbol).reverse = _
    rw [ha]
    exact SequentialCaptureCopyMachine.wordTape_append (resultWords v) _

theorem cursor_stream (ns : List CBVtoCBN.CompileNode) (m : Nat) (E S : CaptureEnv)
    (v : ReturnValue) (K : List SequentialSharedWords.Frame) :
    (encode ns (before m E S v K)).cursors = (encode ns (after m S v K)).cursors := by
  simp [encode,SequentialSharedStateCodec.write_cursors,before,after,SequentialSharedCursors.positions,
    SequentialSharedCursors.frameCursor]

theorem clock_push (ns : List CBVtoCBN.CompileNode) (x : List Char) (m : Nat) (E S : CaptureEnv)
    (v : ReturnValue) (K : List SequentialSharedWords.Frame) :
    withInput (encode ns (before m E S v K)) x 3 ++ [1] = withInput (encode ns (after m S v K)) x 3 := by
  change blocks [m] ++ [1] = blocks [m+1]
  simp [blocks_cons,blocks_nil,List.replicate_succ']

def branch (v : ReturnValue) : LProg 8 := .seq (wordProgram v)
  (.seq (SequentialScopeControlMachine.program (resultFields v).length) (.push 3 1))

theorem all_changed_streams (a b : Packed) (x : List Char) (hp : a.cursors=b.cursors) :
    (((withInput a x).set 4 (withInput b x 4)).set 2 (withInput b x 2)).set 3 (withInput b x 3) = withInput b x := by
  funext j
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 := by omega
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | (change bits a.cursors = bits b.cursors; rw [hp])

private theorem next_reachable {g : MGrammar} {x : List Char} {a b c : Config}
    (h : Runs g x a b) (hs : SequentialSharedWords.step g x b = some c) : Runs g x a c := by
  induction h with
  | refl => exact .cons hs (.refl _)
  | cons hh ht ih => exact .cons hh (ih hs)

theorem branch_runs (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E S : CaptureEnv)
    (v : ReturnValue) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before m E S v K)) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (branch v) (withInput (encode (CBVtoCBN.compilerNodes g e) (before m E S v K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (after m S v K)) x) T := by
  let ns := CBVtoCBN.compilerNodes g e
  let B := (SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3
  let L := withInput (encode ns (before m E S v K)) x
  let target := withInput (encode ns (after m S v K)) x
  let tail := wordTape (S ++ K.flatMap SequentialSharedWordSpace.frameWords)
  have hb := SequentialSharedStateBound.encoded_state_linear g x e _ h
  change (encode ns (before m E S v K)).length ≤ _ at hb
  have hx : x.length+2 ≤ B := by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega
  have hL : LenOK B L := SequentialCaptureCopyMachine.withInput_fits _ x
    (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega) hx
  have ha := next_reachable h (actual_step g x m E S v K)
  have hba := SequentialSharedStateBound.encoded_state_linear g x e _ ha
  change (encode ns (after m S v K)).length ≤ _ at hba
  have htarget : LenOK B target := SequentialCaptureCopyMachine.withInput_fits _ x
    (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega) hx
  obtain ⟨Tw,hw⟩ := SequentialScopeWordMachine.result_words_runs v E (K.length+1)
    (blocks (writeFrames ns K).control ++ blocks [7,S.length]) tail L
    (before_control ns x m E S v K) (word_streams ns x m E S v K).1 rfl rfl rfl hL
  let N := L.set 4 (tail ++ wordTape (resultWords v))
  obtain ⟨Tc,hc⟩ := SequentialScopeControlMachine.restore_runs E.length K.length S.length (resultFields v)
    (blocks (writeFrames ns K).control) N (before_control ns x m E S v K) rfl rfl rfl (end_fits hw)
  let M := N.set 2 (blocks (writeFrames ns K).control ++ blocks ([S.length,K.length] ++ resultFields v))
  have hM : LenOK B M := end_fits hc
  have hclk : M 3 ++ [1] = target 3 := clock_push ns x m E S v K
  have hclockcap : (M 3 ++ [1]).length+2 ≤ B := by rw [hclk]; exact htarget 3
  have hpush := runs_push (i := (3 : Fin 8)) (e := 1) hM (lenOK_set hM 3 hclockcap)
  have he : M.set 3 (M 3 ++ [1]) = target := by
    have hw' : tail ++ wordTape (resultWords v) = target 4 := (word_streams ns x m E S v K).2.symm
    have hc' : blocks (writeFrames ns K).control ++ blocks ([S.length,K.length] ++ resultFields v) = target 2 :=
      (after_control ns x m S v K).symm
    rw [hclk]
    dsimp only [M,N]
    rw [hw',hc']
    exact all_changed_streams _ _ x (cursor_stream ns m E S v K)
  rw [he] at hpush
  exact ⟨_,hw.seq (hc.seq hpush)⟩

/-- These are fixed code templates, not functions of a runtime return value. -/
def plain : LProg 8 := .seq SequentialScopeWordMachine.discardCurrent
  (.seq (SequentialScopeControlMachine.program 2) (.push 3 1))

def argsSuccess : LProg 8 := .seq SequentialScopeWordMachine.preserveReturnWords
  (.seq (SequentialScopeControlMachine.program 3) (.push 3 1))

def argsProgram : LProg 8 := SequentialReturnControlMachine.dispatch 2 1 3 plain plain argsSuccess

def branches (tag : Nat) : LProg 8 := if tag=3 then plain else if tag=4 then argsProgram else skipP 2

def program : LProg 8 := SequentialTagDispatchMachine.program 2 1 2 4 branches

def kind : ReturnValue → Nat | .expr _ => 3 | .args _ => 4

def trailing (v : ReturnValue) : List Nat := (resultFields v).tail

theorem fields_split (v : ReturnValue) : resultFields v = [kind v] ++ trailing v := by cases v <;> rfl

theorem args_runs (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E S : CaptureEnv)
    (r : SequentialSharedWords.ArgsResult) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before m E S (.args r) K)) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      argsProgram (withInput (encode (CBVtoCBN.compilerNodes g e) (before m E S (.args r) K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (after m S (.args r) K)) x) T := by
  let ns := CBVtoCBN.compilerNodes g e
  let B := (SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3
  let L := withInput (encode ns (before m E S (.args r) K)) x
  let target := withInput (encode ns (after m S (.args r) K)) x
  obtain ⟨T,hr⟩ := branch_runs g x e m E S (.args r) K h
  have hs : Complexity.Runs (LenOK B) (SequentialReturnControlMachine.select
      (SequentialArgConsReturnPackedMachine.resultTag r) plain plain argsSuccess) L target T := by
    cases r with
    | none => simpa [SequentialReturnControlMachine.select,SequentialArgConsReturnPackedMachine.resultTag,
        branch,plain,wordProgram,resultFields,SequentialArgConsReturnPackedMachine.extraFields] using hr
    | some value => cases value with
      | none => simpa [SequentialReturnControlMachine.select,SequentialArgConsReturnPackedMachine.resultTag,
          branch,plain,wordProgram,resultFields,SequentialArgConsReturnPackedMachine.extraFields] using hr
      | some Vq => rcases Vq with ⟨V,q⟩
                   simpa [SequentialReturnControlMachine.select,SequentialArgConsReturnPackedMachine.resultTag,
                     branch,argsSuccess,wordProgram,resultFields,SequentialArgConsReturnPackedMachine.extraFields] using hr
  have hL : LenOK B L := by
    have hb := SequentialSharedStateBound.encoded_state_linear g x e _ h
    change (encode ns (before m E S (.args r) K)).length ≤ _ at hb
    apply SequentialCaptureCopyMachine.withInput_fits
    · dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega
    · dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega
  have hsrc : L 2 = (blocks (writeFrames ns K).control ++ blocks [7,S.length] ++
      blocks (SequentialArgConsReturnPackedMachine.extraFields r)) ++
      blocks [SequentialArgConsReturnPackedMachine.resultTag r] ++ blocks [E.length,K.length+1,4] := by
    dsimp only [L]
    rw [before_control]
    simp only [resultFields,SequentialControlEditMachine.blocks_append]
    rw [show [4,SequentialArgConsReturnPackedMachine.resultTag r] = [4] ++ [SequentialArgConsReturnPackedMachine.resultTag r] from rfl,
      SequentialControlEditMachine.blocks_append]
    rw [show [E.length,K.length+1,4] = [E.length,K.length+1] ++ [4] from rfl,SequentialControlEditMachine.blocks_append]
    simp only [List.append_assoc]
  have ht : SequentialArgConsReturnPackedMachine.resultTag r ≤ 2 := by
    cases r with | none => decide | some value => cases value <;> simp [SequentialArgConsReturnPackedMachine.resultTag]
  exact SequentialReturnControlMachine.dispatch_runs (src := (2 : Fin 8)) (tmp := 1) (by decide)
    [E.length,K.length+1,4] _ ht (blocks (writeFrames ns K).control ++ blocks [7,S.length] ++
      blocks (SequentialArgConsReturnPackedMachine.extraFields r)) plain plain argsSuccess L target hsrc rfl hL hs

theorem transition_runs (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E S : CaptureEnv)
    (v : ReturnValue) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before m E S v K)) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      program (withInput (encode (CBVtoCBN.compilerNodes g e) (before m E S v K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (after m S v K)) x) T := by
  let ns := CBVtoCBN.compilerNodes g e
  let B := (SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3
  let L := withInput (encode ns (before m E S v K)) x
  let target := withInput (encode ns (after m S v K)) x
  obtain ⟨T,hr⟩ : ∃ T, Complexity.Runs (LenOK B) (branches (kind v)) L target T := by
    cases v with
    | expr r => simpa [branches,kind,plain,branch,wordProgram,resultFields] using branch_runs g x e m E S (.expr r) K h
    | args r => simpa [branches,kind] using args_runs g x e m E S r K h
  have hb := SequentialSharedStateBound.encoded_state_linear g x e _ h
  change (encode ns (before m E S v K)).length ≤ _ at hb
  have hL : LenOK B L := SequentialCaptureCopyMachine.withInput_fits _ x
    (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega)
    (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega)
  let C := (blocks (writeFrames ns K).control ++ blocks [7,S.length] ++ blocks (trailing v)) ++ [0]
  have hsrc : L 2 = C ++ unary (kind v) ++ blocks [E.length,K.length+1] := by
    dsimp only [L]
    rw [before_control,fields_split,SequentialControlEditMachine.blocks_append,blocks_cons (kind v) [],blocks_nil]
    simp only [C,List.nil_append,List.append_assoc]
  have htag : kind v ≤ 4 := by cases v <;> simp [kind]
  exact SequentialTagDispatchMachine.dispatch_runs (src := (2 : Fin 8)) (tmp := 1) (by decide)
    [E.length,K.length+1] 4 (kind v) htag C branches L target hsrc (by rw [lastSym_append]; rfl) rfl hL hr

theorem transition_tape (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E S : CaptureEnv)
    (v : ReturnValue) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before m E S v K)) (tau : Tapes 8)
    (hrep : Rep (withInput (encode (CBVtoCBN.compilerNodes g e) (before m E S v K)) x) tau) :
    ∃ t tau', Exec (TFits ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      program.compile tau t (.cont tau') ∧ Rep
      (withInput (encode (CBVtoCBN.compilerNodes g e) (after m S v K)) x) tau' := by
  obtain ⟨T,hr⟩ := transition_runs g x e m E S v K h
  exact tape_runs hr tau hrep

theorem finite_alphabet (E : Nat) (hE : 2 ≤ E) : program.compile.SymOK (E+4) := by
  apply compile_symOK E
  have hp : plain.ConstOK E := ⟨SequentialScopeWordMachine.discardCurrent_constOK E,
    SequentialScopeControlMachine.constOK 2 E,by change 1 < E; omega⟩
  have hs : argsSuccess.ConstOK E := ⟨SequentialScopeWordMachine.preserveReturnWords_constOK E,
    SequentialScopeControlMachine.constOK 3 E,by change 1 < E; omega⟩
  have ha : argsProgram.ConstOK E := SequentialReturnControlMachine.dispatch_constOK E _ _ _ _ _ _ hp hp hs
  apply SequentialTagDispatchMachine.constOK E _ _ _ _ branches
  intro tag
  unfold branches
  split
  · exact hp
  · split
    · exact ha
    · trivial

end Shallot.MacroPeg.CBV.SequentialScopePackedMachine
