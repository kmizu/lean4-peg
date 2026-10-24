import MacroPeg.CBV.SequentialAnyPackedMachine

/-! Complete compressed structural entries. Templates depend only on source
syntax; environment and stack lengths remain unary streams at runtime. -/
namespace Shallot.MacroPeg.CBV.SequentialEntryPackedMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialControlEditMachine
open SequentialSharedWords (Config CaptureEnv Runs initial)
open SequentialSharedStateCodec (encode write writeTask writeFrames Input)
open SequentialCursorEntryMachine (Entry before after layout layout_fits layout_cursors)

def erased (ns : List CBVtoCBN.CompileNode) (entry : Entry) : List Nat :=
  (writeTask ns (before entry 0 [] 0 []).task).control

def fresh (ns : List CBVtoCBN.CompileNode) (entry : Entry) : List Nat :=
  (writeTask ns (after entry 0 [] 0 []).task).control ++
    (writeFrames ns (after entry 0 [] 0 []).stack).control

def rewrite (ns : List CBVtoCBN.CompileNode) (entry : Entry) : LProg 6 :=
  .seq (replace 2 1 2 (erased ns entry).length (fresh ns entry)) (incrementSecond 2 1)

def program (ns : List CBVtoCBN.CompileNode) (entry : Entry) : LProg 6 :=
  .seq (duplicate 0 1) (rewrite ns entry)

theorem before_control (ns : List CBVtoCBN.CompileNode) (entry : Entry) (m : Nat)
    (E : CaptureEnv) (p : Nat) (K : List SequentialSharedWords.Frame) :
    layout (encode ns (before entry m E p K)) 2 =
      blocks (writeFrames ns K).control ++ blocks (erased ns entry) ++ blocks [E.length,K.length] := by
  rw [SequentialAnyPackedMachine.layout_control]
  have he : (write ns (before entry m E p K)).control =
      [E.length,K.length] ++ erased ns entry ++ (writeFrames ns K).control := by
    cases entry <;> simp [write,before,erased,writeTask,Input.append,
      SequentialSharedStateCodec.putControl,SequentialSharedStateCodec.putWords,
      SequentialSharedStateCodec.putExpr,SequentialSharedStateCodec.putExprs,
      SequentialSharedStateCodec.putCursor]
  rw [he,blocks_append,blocks_append]
  simp only [List.append_assoc]

theorem after_control (ns : List CBVtoCBN.CompileNode) (entry : Entry) (m : Nat)
    (E : CaptureEnv) (p : Nat) (K : List SequentialSharedWords.Frame) :
    layout (encode ns (after entry m E p K)) 2 =
      blocks (writeFrames ns K).control ++ blocks (fresh ns entry) ++ blocks [E.length,K.length+1] := by
  rw [SequentialAnyPackedMachine.layout_control]
  have he : (write ns (after entry m E p K)).control =
      [E.length,K.length+1] ++ fresh ns entry ++ (writeFrames ns K).control := by
    cases entry <;> simp [write,after,fresh,writeTask,writeFrames,
      SequentialSharedStateCodec.writeFrame,Input.append,Input.empty,
      SequentialSharedStateCodec.putControl,SequentialSharedStateCodec.putWords,
      SequentialSharedStateCodec.putExpr,SequentialSharedStateCodec.putExprs,
      SequentialSharedStateCodec.putCursor,List.append_assoc]
  rw [he,blocks_append,blocks_append]
  simp only [List.append_assoc]

theorem after_layout (ns : List CBVtoCBN.CompileNode) (entry : Entry) (m : Nat)
    (E : CaptureEnv) (p : Nat) (K : List SequentialSharedWords.Frame) :
    ((layout (encode ns (before entry m E p K))).set 0
      (cursors (SequentialSharedCursors.positions (after entry m E p K)))).set 2
        (layout (encode ns (after entry m E p K)) 2) =
      layout (encode ns (after entry m E p K)) := by
  have hw : (encode ns (before entry m E p K)).words =
      (encode ns (after entry m E p K)).words := by
    cases entry <;> simp [encode,SequentialSharedStateCodec.write_words,before,after,
      SequentialSharedWordSpace.retainedWords,SequentialSharedWordSpace.taskWords,
      SequentialSharedWordSpace.frameWords]
  have hm : (encode ns (before entry m E p K)).clock =
      (encode ns (after entry m E p K)).clock := by cases entry <;> rfl
  funext i
  by_cases h0 : i=0
  · subst i
    simp only [Lists.set_same,Lists.set_ne _ _ (by decide : (0 : Fin 6) ≠ 2)]
    exact (layout_cursors ns (after entry m E p K)).symm
  · by_cases h2 : i=2
    · subst i; simp
    · simp only [Lists.set,if_neg h0,if_neg h2]
      simp only [layout,if_neg h0,if_neg h2]
      rw [hw,hm]

private theorem next_reachable {g : MGrammar} {x : List Char} {a b c : Config}
    (h : Runs g x a b) (hs : SequentialSharedWords.step g x b = some c) : Runs g x a c := by
  induction h with
  | refl => exact .cons hs (.refl _)
  | cons hh ht ih => exact .cons hh (ih hs)

private theorem blocks_headers_length (a b : Nat) :
    (blocks [a,b+1]).length = (blocks [a,b]).length+1 := by
  simp [blocks,bits,SequentialCursorChain.encodeDeltas]
  omega

/-- Construct all successor fields, including the incremented stack header.
No successor configuration is passed to the program. -/
theorem transition_runs (g : MGrammar) (x : List Char) (e : MExp) (entry : Entry)
    (m : Nat) (E : CaptureEnv) (p : Nat) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before entry m E p K)) :
    ∃ T, Complexity.Runs
      (LenOK (SequentialSharedStateBound.linearFactor g e * (x.length+1)+3))
      (program (CBVtoCBN.compilerNodes g e) entry)
      (layout (encode (CBVtoCBN.compilerNodes g e) (before entry m E p K)))
      (layout (encode (CBVtoCBN.compilerNodes g e) (after entry m E p K))) T := by
  let ns := CBVtoCBN.compilerNodes g e
  let B := SequentialSharedStateBound.linearFactor g e * (x.length+1)+3
  let L := (layout (encode ns (before entry m E p K))).set 0
    (cursors (SequentialSharedCursors.positions (after entry m E p K)))
  obtain ⟨T1,hd⟩ := SequentialCursorEntryMachine.cursor_update g x e entry m E p K h
  have hL : LenOK B L := end_fits hd
  have ha := next_reachable h (SequentialCursorEntryMachine.actual_step g x entry m E p K)
  have hb := SequentialSharedStateBound.encoded_state_linear g x e _ ha
  have hl := layout_fits (encode ns (after entry m E p K))
    (B := B) (by change (encode ns (after entry m E p K)).length ≤ _ at hb; dsimp [B]; omega)
  have hfinal : (blocks (writeFrames ns K).control ++ blocks (fresh ns entry) ++
      blocks [E.length,K.length+1]).length+2 ≤ B := by
    rw [← after_control ns entry m E p K]
    exact hl 2
  have hsrc : L 2 = blocks (writeFrames ns K).control ++ blocks (erased ns entry) ++
      blocks [E.length,K.length] := by
    simp only [L,Lists.set_ne _ _ (by decide : (2 : Fin 6) ≠ 0),before_control]
  have htmp : L 1 = [] := rfl
  have hmid : (blocks (writeFrames ns K).control ++ blocks (fresh ns entry) ++
      blocks [E.length,K.length]).length+2 ≤ B := by
    simp only [List.length_append] at hfinal ⊢
    rw [blocks_headers_length] at hfinal
    omega
  obtain ⟨T2,hr⟩ := replace_runs (src := (2 : Fin 6)) (tmp := 1) (by decide)
    [E.length,K.length] (erased ns entry) (fresh ns entry) (blocks (writeFrames ns K).control)
    L hsrc htmp hL hmid
  let M := L.set 2 (blocks (writeFrames ns K).control ++ blocks (fresh ns entry) ++
    blocks [E.length,K.length])
  obtain ⟨T3,hi⟩ := incrementSecond_runs (src := (2 : Fin 6)) (tmp := 1) (by decide)
    E.length K.length (blocks (writeFrames ns K).control ++ blocks (fresh ns entry)) M
    (by simp [M]) (by simp [M,L,layout,Lists.set]) (end_fits hr) hfinal
  have hout : M.set 2 (blocks (writeFrames ns K).control ++ blocks (fresh ns entry) ++
      blocks [E.length,K.length+1]) = layout (encode ns (after entry m E p K)) := by
    simp only [M,Lists.set_set_u]
    rw [← after_control ns entry m E p K]
    exact after_layout ns entry m E p K
  rw [hout] at hi
  exact ⟨_,hd.seq (hr.seq hi)⟩

theorem transition_tape (g : MGrammar) (x : List Char) (e : MExp) (entry : Entry)
    (m : Nat) (E : CaptureEnv) (p : Nat) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before entry m E p K)) (τ : Tapes 6)
    (hrep : Rep (layout (encode (CBVtoCBN.compilerNodes g e) (before entry m E p K))) τ) :
    ∃ t τ', Exec (TFits (SequentialSharedStateBound.linearFactor g e * (x.length+1)+3))
      (program (CBVtoCBN.compilerNodes g e) entry).compile τ t (.cont τ') ∧
      Rep (layout (encode (CBVtoCBN.compilerNodes g e) (after entry m E p K))) τ' := by
  obtain ⟨T,hr⟩ := transition_runs g x e entry m E p K h
  exact tape_runs hr τ hrep

theorem finite_alphabet (ns : List CBVtoCBN.CompileNode) (entry : Entry)
    (E : Nat) (hE : 2 ≤ E) : (program ns entry).compile.SymOK (E+4) := by
  apply compile_symOK E
  refine ⟨?_,replace_constOK hE _ _ _ _ _,incrementSecond_constOK hE _ _⟩
  simp [duplicate,scan,moveTop,moveAll,LProg.ConstOK]
  omega

end Shallot.MacroPeg.CBV.SequentialEntryPackedMachine
