import MacroPeg.CBV.SequentialWordRotateMachine

/-! Assemble an actual captured word into the successful argument environment
on the compressed machine. All program templates here are source-independent. -/
namespace Shallot.MacroPeg.CBV.SequentialArgConsPackedMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialControlEditMachine
open SequentialReturnControlMachine SequentialWordRotateMachine
open SequentialCaptureSpliceMachine (wordTape_cons)
open SequentialSharedWords (Config CaptureEnv Runs initial)
open SequentialSharedStateCodec (encode write writeTask writeFrames Input)
open SequentialCaptureCopyMachine (withInput wordTape wordCode)

def before (m : Nat) (E W : CaptureEnv) (w : List Char) (q : Nat)
    (K : List SequentialSharedWords.Frame) : Config :=
  ⟨m,.value (.args (some (some (W,q)))),E,.argCons w :: K⟩

def after (m : Nat) (E W : CaptureEnv) (w : List Char) (q : Nat)
    (K : List SequentialSharedWords.Frame) : Config :=
  ⟨m,.value (.args (some (some (w :: W,q)))),E,K⟩

theorem actual_step (g : MGrammar) (x : List Char) (m : Nat) (E W : CaptureEnv)
    (w : List Char) (q : Nat) (K : List SequentialSharedWords.Frame) :
    SequentialSharedWords.step g x (before m E W w q K) = some (after m E W w q K) := rfl

def program : LProg 8 := .seq SequentialWordRotateMachine.program
  (.seq (incrementAfter 4) (.seq (decrementSecond 2 1) (replace 2 1 5 1 [])))

theorem before_control (ns : List CBVtoCBN.CompileNode) (x : List Char) (m : Nat)
    (E W : CaptureEnv) (w : List Char) (q : Nat) (K : List SequentialSharedWords.Frame) :
    withInput (encode ns (before m E W w q K)) x 2 =
      blocks (writeFrames ns K).control ++ blocks [5] ++ blocks [W.length] ++
        blocks [E.length,K.length+1,4,2] := by
  change SequentialCursorEntryMachine.layout (encode ns (before m E W w q K)) 2 = _
  rw [SequentialAnyPackedMachine.layout_control]
  have he : (write ns (before m E W w q K)).control =
      [E.length,K.length+1,4,2] ++ [W.length] ++ [5] ++ (writeFrames ns K).control := by
    simp [write,before,writeTask,writeFrames,SequentialSharedStateCodec.writeFrame,Input.append,
      SequentialSharedStateCodec.putControl,SequentialSharedStateCodec.putWords,SequentialSharedStateCodec.putCursor]
  rw [he,blocks_append,blocks_append,blocks_append]
  simp only [List.append_assoc]

theorem after_control (ns : List CBVtoCBN.CompileNode) (x : List Char) (m : Nat)
    (E W : CaptureEnv) (w : List Char) (q : Nat) (K : List SequentialSharedWords.Frame) :
    withInput (encode ns (after m E W w q K)) x 2 =
      blocks (writeFrames ns K).control ++ blocks [W.length+1] ++ blocks [E.length,K.length,4,2] := by
  change SequentialCursorEntryMachine.layout (encode ns (after m E W w q K)) 2 = _
  rw [SequentialAnyPackedMachine.layout_control]
  have he : (write ns (after m E W w q K)).control =
      [E.length,K.length,4,2] ++ [W.length+1] ++ (writeFrames ns K).control := by
    simp [write,after,writeTask,Input.append,SequentialSharedStateCodec.putControl,
      SequentialSharedStateCodec.putWords,SequentialSharedStateCodec.putCursor]
  rw [he,blocks_append,blocks_append]
  simp only [List.append_assoc]

theorem before_words (ns : List CBVtoCBN.CompileNode) (x : List Char) (m : Nat)
    (E W : CaptureEnv) (w : List Char) (q : Nat) (K : List SequentialSharedWords.Frame) :
    withInput (encode ns (before m E W w q K)) x 4 =
      wordTape (K.flatMap SequentialSharedWordSpace.frameWords) ++ wordCode w ++ wordTape E ++ wordTape W := by
  change ((encode ns (before m E W w q K)).words.map SequentialCaptureCopyMachine.wordSymbol).reverse = _
  have he : (encode ns (before m E W w q K)).words =
      SequentialSharedWordSpace.encodeWords (W ++ E ++ w :: K.flatMap SequentialSharedWordSpace.frameWords) := by
    simp [encode,SequentialSharedStateCodec.write_words,before,SequentialSharedWordSpace.retainedWords,
      SequentialSharedWordSpace.taskWords,SequentialSharedWordSpace.frameWords,List.append_assoc]
  rw [he]
  change wordTape (W ++ E ++ w :: K.flatMap SequentialSharedWordSpace.frameWords) = _
  rw [SequentialCaptureCopyMachine.wordTape_append,SequentialCaptureCopyMachine.wordTape_append,wordTape_cons]
  simp only [List.append_assoc]

theorem after_words (ns : List CBVtoCBN.CompileNode) (x : List Char) (m : Nat)
    (E W : CaptureEnv) (w : List Char) (q : Nat) (K : List SequentialSharedWords.Frame) :
    withInput (encode ns (after m E W w q K)) x 4 =
      wordTape (K.flatMap SequentialSharedWordSpace.frameWords) ++ wordTape E ++ wordTape W ++ wordCode w := by
  change ((encode ns (after m E W w q K)).words.map SequentialCaptureCopyMachine.wordSymbol).reverse = _
  have he : (encode ns (after m E W w q K)).words =
      SequentialSharedWordSpace.encodeWords ((w :: W) ++ E ++ K.flatMap SequentialSharedWordSpace.frameWords) := by
    simp [encode,SequentialSharedStateCodec.write_words,after,SequentialSharedWordSpace.retainedWords,
      SequentialSharedWordSpace.taskWords,List.append_assoc]
  rw [he]
  change wordTape ((w :: W) ++ E ++ K.flatMap SequentialSharedWordSpace.frameWords) = _
  rw [SequentialCaptureCopyMachine.wordTape_append,SequentialCaptureCopyMachine.wordTape_append,wordTape_cons]
  simp only [List.append_assoc]

private theorem next_reachable {g : MGrammar} {x : List Char} {a b c : Config}
    (h : Runs g x a b) (hs : SequentialSharedWords.step g x b = some c) : Runs g x a c := by
  induction h with
  | refl => exact .cons hs (.refl _)
  | cons hh ht ih => exact .cons hh (ih hs)

/-- The fixed program rotates the captured word, increases the argument count,
decreases the stack count, and removes the old capture frame. -/
theorem transition_runs (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E W : CaptureEnv)
    (w : List Char) (q : Nat) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before m E W w q K)) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      program (withInput (encode (CBVtoCBN.compilerNodes g e) (before m E W w q K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (after m E W w q K)) x) T := by
  let ns := CBVtoCBN.compilerNodes g e
  let B := (SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3
  let L := withInput (encode ns (before m E W w q K)) x
  let target := withInput (encode ns (after m E W w q K)) x
  let C := blocks (writeFrames ns K).control ++ blocks [5] ++ [0]
  have hb := SequentialSharedStateBound.encoded_state_linear g x e _ h
  change (encode ns (before m E W w q K)).length ≤ _ at hb
  have hx : x.length+2 ≤ B := by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega
  have hL : LenOK B L := SequentialCaptureCopyMachine.withInput_fits _ x
    (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega) hx
  have ha := next_reachable h (actual_step g x m E W w q K)
  have hba := SequentialSharedStateBound.encoded_state_linear g x e _ ha
  change (encode ns (after m E W w q K)).length ≤ _ at hba
  have htarget : LenOK B target := SequentialCaptureCopyMachine.withInput_fits _ x
    (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega) hx
  have hctrl : L 2 = C ++ unary W.length ++ blocks [E.length,K.length+1,4,2] := by
    dsimp only [L]
    rw [before_control]
    simp only [C,blocks_cons]
    simp [blocks,bits,SequentialCursorChain.encodeDeltas,List.append_assoc]
  obtain ⟨Tw,hw⟩ := rotate_runs E W w (K.length+1) (blocks (writeFrames ns K).control ++ blocks [5])
    (wordTape (K.flatMap SequentialSharedWordSpace.frameWords)) L hctrl
    (before_words ns x m E W w q K) rfl rfl rfl hL
  let M := L.set 4 (wordTape (K.flatMap SequentialSharedWordSpace.frameWords) ++ wordTape E ++ wordTape W ++ wordCode w)
  have hM : LenOK B M := end_fits hw
  have hM2 : M 2 = C ++ unary W.length ++ blocks [E.length,K.length+1,4,2] := hctrl
  have hinc : (C ++ unary (W.length+1) ++ blocks [E.length,K.length+1,4,2]).length+2 ≤ B := by
    have hc : (L 2).length ≤ (encode ns (before m E W w q K)).length := by
      change (SequentialCursorEntryMachine.layout _ 2).length ≤ _
      simp [SequentialCursorEntryMachine.layout,bits_length]
      unfold SequentialSharedStateCodec.Packed.length
      omega
    rw [hctrl] at hc
    simp only [List.length_append,List.length_replicate] at hc ⊢
    dsimp [B]
    rw [Nat.add_mul,Nat.one_mul]
    omega
  obtain ⟨Ti,hi⟩ := incrementAfter_runs [E.length,K.length+1,4,2] W.length C M hM2 rfl hM hinc
  let N := M.set 2 (C ++ unary (W.length+1) ++ blocks [E.length,K.length+1,4,2])
  have hn2 : N 2 = (blocks (writeFrames ns K).control ++ blocks [5] ++ blocks [4,2,W.length+1]) ++
      blocks [E.length,K.length+1] := by
    simp only [N,Lists.set_same,C,blocks_cons]
    simp [blocks,bits,SequentialCursorChain.encodeDeltas,List.append_assoc]
  obtain ⟨Td,hd⟩ := decrementSecond_runs (src := (2 : Fin 8)) (tmp := 1) (by decide)
    E.length K.length (blocks (writeFrames ns K).control ++ blocks [5] ++ blocks [4,2,W.length+1])
    N hn2 rfl (end_fits hi)
  let R := N.set 2 ((blocks (writeFrames ns K).control ++ blocks [5] ++ blocks [4,2,W.length+1]) ++
    blocks [E.length,K.length])
  have hr2 : R 2 = blocks (writeFrames ns K).control ++ blocks [5] ++ blocks [E.length,K.length,4,2,W.length+1] := by
    simp only [R,Lists.set_same]
    rw [show [E.length,K.length,4,2,W.length+1] = [E.length,K.length] ++ [4,2,W.length+1] from rfl,blocks_append]
    simp only [List.append_assoc]
  have hcap : (blocks (writeFrames ns K).control ++ blocks [] ++ blocks [E.length,K.length,4,2,W.length+1]).length+2 ≤ B := by
    have he : blocks (writeFrames ns K).control ++ blocks [] ++ blocks [E.length,K.length,4,2,W.length+1] = target 2 := by
      dsimp only [target]
      rw [after_control]
      rw [show [E.length,K.length,4,2,W.length+1] = [E.length,K.length,4,2] ++ [W.length+1] from rfl,blocks_append]
      simp [blocks,bits,SequentialCursorChain.encodeDeltas,List.append_assoc]
    rw [he]
    exact htarget 2
  obtain ⟨Tr,ht⟩ := replace_runs (src := (2 : Fin 8)) (tmp := 1) (by decide)
    [E.length,K.length,4,2,W.length+1] [5] [] (blocks (writeFrames ns K).control) R hr2 rfl (end_fits hd) hcap
  have he : R.set 2 (blocks (writeFrames ns K).control ++ blocks [] ++ blocks [E.length,K.length,4,2,W.length+1]) = target := by
    have hectrl : blocks (writeFrames ns K).control ++ blocks [] ++ blocks [E.length,K.length,4,2,W.length+1] = target 2 := by
      dsimp only [target]
      rw [after_control]
      rw [show [E.length,K.length,4,2,W.length+1] = [E.length,K.length,4,2] ++ [W.length+1] from rfl,blocks_append]
      simp [blocks,bits,SequentialCursorChain.encodeDeltas,List.append_assoc]
    have hew : wordTape (K.flatMap SequentialSharedWordSpace.frameWords) ++ wordTape E ++ wordTape W ++ wordCode w = target 4 :=
      (after_words ns x m E W w q K).symm
    have hec : (L.set 4 (target 4)) 0 = target 0 := by
      change SequentialCursorEntryMachine.layout (encode ns (before m E W w q K)) 0 =
        SequentialCursorEntryMachine.layout (encode ns (after m E W w q K)) 0
      rw [SequentialCursorEntryMachine.layout_cursors,SequentialCursorEntryMachine.layout_cursors]
      rfl
    dsimp only [R,N]
    rw [Lists.set_set_u,Lists.set_set_u,hectrl]
    dsimp only [M]
    rw [hew]
    have hu := SequentialArgCapturePackedMachine.withInput_update (encode ns (before m E W w q K))
      (encode ns (after m E W w q K)) x rfl
    change (((L.set 4 (target 4)).set 0 (target 0)).set 2 (target 2)) = target at hu
    rwa [← hec,Lists.set_get_self] at hu
  rw [he] at ht
  exact ⟨_,hw.seq (hi.seq (hd.seq ht))⟩

theorem transition_tape (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E W : CaptureEnv)
    (w : List Char) (q : Nat) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before m E W w q K)) (τ : Tapes 8)
    (hrep : Rep (withInput (encode (CBVtoCBN.compilerNodes g e) (before m E W w q K)) x) τ) :
    ∃ t τ', Exec (TFits ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      program.compile τ t (.cont τ') ∧
      Rep (withInput (encode (CBVtoCBN.compilerNodes g e) (after m E W w q K)) x) τ' := by
  obtain ⟨T,hr⟩ := transition_runs g x e m E W w q K h
  exact tape_runs hr τ hrep

theorem constOK (E : Nat) (hE : 2 ≤ E) : program.ConstOK E := by
  exact ⟨SequentialWordRotateMachine.constOK E,incrementAfter_constOK E 4 hE,
    decrementSecond_constOK E _ _,replace_constOK hE _ _ _ _ _⟩

theorem finite_alphabet (E : Nat) (hE : 2 ≤ E) : program.compile.SymOK (E+4) :=
  compile_symOK E program (constOK E hE)

end Shallot.MacroPeg.CBV.SequentialArgConsPackedMachine
