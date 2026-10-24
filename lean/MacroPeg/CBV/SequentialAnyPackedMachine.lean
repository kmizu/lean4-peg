import MacroPeg.CBV.SequentialControlEditMachine

/-! A complete compressed-state transition for `any`. No decoded state or
new control prefix is supplied to the program. All four packed streams and
both empty scratch tapes are accounted for at every program point. -/
namespace Shallot.MacroPeg.CBV.SequentialAnyPackedMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialCursorDecreaseMachine
open SequentialControlEditMachine
open SequentialSharedWords (Config CaptureEnv Runs initial)
open SequentialSharedStateCodec (Packed encode write writeTask writeFrames Input)
open SequentialCursorEntryMachine (layout layout_fits layout_cursors)
open SequentialAnyCursorMachine (before after before_positions actual_step)

abbrev resultTag : Nat → Nat
  | 0 => 1
  | _+1 => 2

def rewriteTask (tag : Nat) : LProg 6 := replace 2 1 2 2 [3,tag]

def program : LProg 6 := .ite 0 (symIs 1)
  (.seq (decrement 0 1) (rewriteTask 2))
  (.seq (dropBlock 0 1) (rewriteTask 1))

theorem layout_control (ns : List CBVtoCBN.CompileNode) (c : Config) :
    layout (encode ns c) 2 = blocks (write ns c).control := by
  simp [layout,encode,blocks]

private theorem control_length (packed : Packed) : (layout packed 2).length ≤ packed.length := by
  simp [layout,bits_length]
  unfold Packed.length
  omega

theorem before_control (ns : List CBVtoCBN.CompileNode) (m : Nat) (E : CaptureEnv) (p : Nat)
    (K : List SequentialSharedWords.Frame) :
    layout (encode ns (before m E p K)) 2 =
      blocks (writeFrames ns K).control ++ blocks [0,SequentialStackCodec.exprId ns .any] ++
        blocks [E.length,K.length] := by
  rw [layout_control]
  have hw : (write ns (before m E p K)).control =
      [E.length,K.length] ++ [0,SequentialStackCodec.exprId ns .any] ++ (writeFrames ns K).control := by
    simp [write,before,writeTask,Input.append,SequentialSharedStateCodec.putControl,
      SequentialSharedStateCodec.putWords,SequentialSharedStateCodec.putExpr,
      SequentialSharedStateCodec.putCursor,SequentialStackCodec.writeExpr]
  rw [hw,blocks_append,blocks_append]
  simp only [List.append_assoc]

theorem after_control (ns : List CBVtoCBN.CompileNode) (m : Nat) (E : CaptureEnv) (p : Nat)
    (K : List SequentialSharedWords.Frame) :
    layout (encode ns (after m E p K)) 2 =
      blocks (writeFrames ns K).control ++ blocks [3,resultTag p] ++ blocks [E.length,K.length] := by
  rw [layout_control]
  have hw : (write ns (after m E p K)).control =
      [E.length,K.length] ++ [3,resultTag p] ++ (writeFrames ns K).control := by
    cases p <;> simp [write,after,writeTask,Input.append,SequentialSharedStateCodec.putControl,
      SequentialSharedStateCodec.putWords,SequentialSharedStateCodec.putCursor,resultTag]
  rw [hw,blocks_append,blocks_append]
  simp only [List.append_assoc]

theorem after_layout (ns : List CBVtoCBN.CompileNode) (m : Nat) (E : CaptureEnv) (p : Nat)
    (K : List SequentialSharedWords.Frame) :
    ((layout (encode ns (before m E p K))).set 0
      (cursors (SequentialSharedCursors.positions (after m E p K)))).set 2
        (layout (encode ns (after m E p K)) 2) = layout (encode ns (after m E p K)) := by
  have hw : (encode ns (before m E p K)).words = (encode ns (after m E p K)).words := by
    cases p <;> simp only [encode,SequentialSharedStateCodec.write_words,before,after,
      SequentialSharedWordSpace.retainedWords,SequentialSharedWordSpace.taskWords]
  have hm : (encode ns (before m E p K)).clock = (encode ns (after m E p K)).clock := rfl
  funext i
  by_cases h0 : i=0
  · subst i
    simp only [Lists.set_same,Lists.set_ne _ _ (by decide : (0 : Fin 6) ≠ 2)]
    exact (layout_cursors ns (after m E p K)).symm
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

/-- The cursor component has already been updated. Now replace the task's
control fields and recover the *complete* encoded successor configuration. -/
theorem control_update (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E : CaptureEnv)
    (p : Nat) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before m E p K))
    (hL : LenOK (SequentialSharedStateBound.linearFactor g e * (x.length+1)+2)
      ((layout (encode (CBVtoCBN.compilerNodes g e) (before m E p K))).set 0
        (cursors (SequentialSharedCursors.positions (after m E p K))))) :
    ∃ T, Complexity.Runs
      (LenOK (SequentialSharedStateBound.linearFactor g e * (x.length+1)+2)) (rewriteTask (resultTag p))
      ((layout (encode (CBVtoCBN.compilerNodes g e) (before m E p K))).set 0
        (cursors (SequentialSharedCursors.positions (after m E p K))))
      (layout (encode (CBVtoCBN.compilerNodes g e) (after m E p K))) T := by
  let ns := CBVtoCBN.compilerNodes g e
  let L := (layout (encode ns (before m E p K))).set 0
    (cursors (SequentialSharedCursors.positions (after m E p K)))
  have hs := (SequentialAnyCursorMachine.cursor_update g x e m E p K h).1
  have ha := next_reachable h hs
  have hb := SequentialSharedStateBound.encoded_state_linear g x e _ ha
  change (encode ns (after m E p K)).length ≤ _ at hb
  have hc := control_length (encode ns (after m E p K))
  have hf : (blocks (writeFrames ns K).control ++ blocks [3,resultTag p] ++
      blocks [E.length,K.length]).length+2 ≤ SequentialSharedStateBound.linearFactor g e * (x.length+1)+2 := by
    rw [← after_control ns m E p K]
    omega
  have hsrc : L 2 = blocks (writeFrames ns K).control ++
      blocks [0,SequentialStackCodec.exprId ns .any] ++ blocks [E.length,K.length] := by
    simp only [L,Lists.set_ne _ _ (by decide : (2 : Fin 6) ≠ 0),before_control]
  have htmp : L 1 = [] := rfl
  obtain ⟨T,hr⟩ := replace_runs (src := (2 : Fin 6)) (tmp := 1) (by decide)
    [E.length,K.length] [0,SequentialStackCodec.exprId ns .any] [3,resultTag p]
    (blocks (writeFrames ns K).control) L hsrc htmp hL hf
  have he : L.set 2 (blocks (writeFrames ns K).control ++ blocks [3,resultTag p] ++
      blocks [E.length,K.length]) = layout (encode ns (after m E p K)) := by
    rw [← after_control ns m E p K]
    exact after_layout ns m E p K
  rw [he] at hr
  exact ⟨T,hr⟩

/-- A complete Seq step from the old packed state to the actual packed
successor, including control, cursor, clock, words, and cleared scratch. -/
theorem transition_runs (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E : CaptureEnv)
    (p : Nat) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before m E p K)) :
    SequentialSharedWords.step g x (before m E p K) = some (after m E p K) ∧
    ∃ T, Complexity.Runs
      (LenOK (SequentialSharedStateBound.linearFactor g e * (x.length+1)+2)) program
      (layout (encode (CBVtoCBN.compilerNodes g e) (before m E p K)))
      (layout (encode (CBVtoCBN.compilerNodes g e) (after m E p K))) T := by
  refine ⟨(SequentialAnyCursorMachine.cursor_update g x e m E p K h).1,?_⟩
  have hchain := SequentialSharedCursors.reachable_chain g x e (before m E p K) h
  rw [before_positions] at hchain
  cases hchain with
  | cons hz ht =>
    let packed := encode (CBVtoCBN.compilerNodes g e) (before m E p K)
    have hb := SequentialSharedStateBound.encoded_state_linear g x e _ h
    change packed.length ≤ _ at hb
    have hL := layout_fits packed
      (B := SequentialSharedStateBound.linearFactor g e * (x.length+1)+2) (by omega)
    have hs : layout packed 0 = cursors (p :: K.filterMap SequentialSharedCursors.frameCursor) := by
      rw [layout_cursors,before_positions]
    have htmp : layout packed 1 = [] := rfl
    cases p with
    | zero =>
      obtain ⟨T1,hr⟩ := drop_current_runs (src := (0 : Fin 6)) (tmp := 1) (by decide)
        ht (layout packed) hs htmp hL
      obtain ⟨T2,hc⟩ := control_update g x e m E 0 K h (end_fits hr)
      have hcond : symIs 1 (lastSym (layout packed 0)) = false := by
        simp [hs,cursors_cons,lastSym_append,symIs]
      exact ⟨_,(hr.seq hc).iteF hL hcond⟩
    | succ p =>
      obtain ⟨T1,hr⟩ := decrement_current_runs (src := (0 : Fin 6)) (tmp := 1) (by decide)
        ht (layout packed) hs htmp hL
      obtain ⟨T2,hc⟩ := control_update g x e m E (p+1) K h (end_fits hr)
      have hcond : symIs 1 (lastSym (layout packed 0)) = true := by
        have he : unary (p+1) = unary p ++ [1] := List.replicate_succ'
        rw [hs,cursors_cons,he,← List.append_assoc,lastSym_append]
        decide
      exact ⟨_,(hr.seq hc).iteT hL hcond⟩

/-- The compiled transition satisfies the same bound at every visited tape
state and returns the representation of the complete successor configuration. -/
theorem transition_tape (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E : CaptureEnv)
    (p : Nat) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before m E p K)) (τ : Tapes 6)
    (hrep : Rep (layout (encode (CBVtoCBN.compilerNodes g e) (before m E p K))) τ) :
    ∃ t τ', Exec (TFits (SequentialSharedStateBound.linearFactor g e * (x.length+1)+2))
      program.compile τ t (.cont τ') ∧
      Rep (layout (encode (CBVtoCBN.compilerNodes g e) (after m E p K))) τ' := by
  obtain ⟨hs,T,hr⟩ := transition_runs g x e m E p K h
  exact tape_runs hr τ hrep


/-- The complete transition uses a fixed pushed-symbol alphabet, independent
of the source grammar, input length, and values of the saved headers. -/
theorem finite_alphabet (E : Nat) (hE : 2 ≤ E) : program.compile.SymOK (E+4) := by
  apply compile_symOK E
  refine ⟨⟨decrement_constOK hE _ _,replace_constOK hE _ _ _ _ _⟩,?_,replace_constOK hE _ _ _ _ _⟩
  simp [dropBlock,scan,moveTop,moveAll,clearP,LProg.ConstOK]

end Shallot.MacroPeg.CBV.SequentialAnyPackedMachine
