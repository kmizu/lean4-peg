import MacroPeg.CBV.SequentialCaptureSpliceMachine

/-! Complete successful argument-head returns on the compressed word machine.
The actual capture is copied from the same original input and spliced beneath
the current environment before cursor and control edits are performed. -/
namespace Shallot.MacroPeg.CBV.SequentialArgCapturePackedMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialControlEditMachine
open SequentialSharedWords (Config CaptureEnv Runs initial)
open SequentialSharedStateCodec (Packed encode write writeTask writeFrames Input)
open SequentialCaptureCopyMachine (withInput wordTape wordCode)

def before (m : Nat) (E : CaptureEnv) (es : List MExp) (p q : Nat)
    (K : List SequentialSharedWords.Frame) : Config :=
  ⟨m,.value (.expr (some (some q))),E,.argHead es p :: K⟩

def after (x : List Char) (m : Nat) (E : CaptureEnv) (es : List MExp) (p q : Nat)
    (K : List SequentialSharedWords.Frame) : Config :=
  ⟨m,.args es q,E,.argCons (pre x p q) :: K⟩

theorem actual_step (g : MGrammar) (x : List Char) (m : Nat) (E : CaptureEnv)
    (es : List MExp) (p q : Nat) (K : List SequentialSharedWords.Frame) :
    SequentialSharedWords.step g x (before m E es p q K) = some (after x m E es p q K) := rfl

def oldFields (ns : List CBVtoCBN.CompileNode) (es : List MExp) : List Nat :=
  [3,2,4] ++ SequentialStackCodec.writeExprs ns es

def newFields (ns : List CBVtoCBN.CompileNode) (es : List MExp) : List Nat :=
  [1] ++ SequentialStackCodec.writeExprs ns es ++ [5]

def program (ns : List CBVtoCBN.CompileNode) (es : List MExp) : LProg 8 :=
  .seq SequentialCaptureSpliceMachine.program (.seq (dropSaved 0 7 1)
    (replace 2 1 2 (oldFields ns es).length (newFields ns es)))

theorem before_control (ns : List CBVtoCBN.CompileNode) (m : Nat) (E : CaptureEnv)
    (es : List MExp) (p q : Nat) (K : List SequentialSharedWords.Frame) :
    withInput (encode ns (before m E es p q K)) [] 2 =
      blocks (writeFrames ns K).control ++ blocks (oldFields ns es) ++ blocks [E.length,K.length+1] := by
  change SequentialCursorEntryMachine.layout (encode ns (before m E es p q K)) 2 = _
  rw [SequentialAnyPackedMachine.layout_control]
  have he : (write ns (before m E es p q K)).control =
      [E.length,K.length+1] ++ oldFields ns es ++ (writeFrames ns K).control := by
    simp [write,before,oldFields,writeTask,writeFrames,SequentialSharedStateCodec.writeFrame,
      Input.append,SequentialSharedStateCodec.putControl,SequentialSharedStateCodec.putWords,
      SequentialSharedStateCodec.putExprs,SequentialSharedStateCodec.putCursor]
  rw [he,blocks_append,blocks_append]
  simp only [List.append_assoc]

theorem after_control (ns : List CBVtoCBN.CompileNode) (x : List Char) (m : Nat) (E : CaptureEnv)
    (es : List MExp) (p q : Nat) (K : List SequentialSharedWords.Frame) :
    withInput (encode ns (after x m E es p q K)) x 2 =
      blocks (writeFrames ns K).control ++ blocks (newFields ns es) ++ blocks [E.length,K.length+1] := by
  change SequentialCursorEntryMachine.layout (encode ns (after x m E es p q K)) 2 = _
  rw [SequentialAnyPackedMachine.layout_control]
  have he : (write ns (after x m E es p q K)).control =
      [E.length,K.length+1] ++ newFields ns es ++ (writeFrames ns K).control := by
    simp [write,after,newFields,writeTask,writeFrames,SequentialSharedStateCodec.writeFrame,
      Input.append,SequentialSharedStateCodec.putControl,SequentialSharedStateCodec.putWords,
      SequentialSharedStateCodec.putExprs,SequentialSharedStateCodec.putCursor,List.append_assoc]
  rw [he,blocks_append,blocks_append]
  simp only [List.append_assoc]

theorem before_words (ns : List CBVtoCBN.CompileNode) (x : List Char) (m : Nat) (E : CaptureEnv)
    (es : List MExp) (p q : Nat) (K : List SequentialSharedWords.Frame) :
    withInput (encode ns (before m E es p q K)) x 4 =
      wordTape (K.flatMap SequentialSharedWordSpace.frameWords) ++ wordTape E := by
  change ((encode ns (before m E es p q K)).words.map SequentialCaptureCopyMachine.wordSymbol).reverse = _
  have he : (encode ns (before m E es p q K)).words =
      SequentialSharedWordSpace.encodeWords (E ++ K.flatMap SequentialSharedWordSpace.frameWords) := by
    simp [encode,SequentialSharedStateCodec.write_words,before,
      SequentialSharedWordSpace.retainedWords,SequentialSharedWordSpace.taskWords,
      SequentialSharedWordSpace.frameWords]
  rw [he]
  exact SequentialCaptureCopyMachine.wordTape_append E _

theorem after_words (ns : List CBVtoCBN.CompileNode) (x : List Char) (m : Nat) (E : CaptureEnv)
    (es : List MExp) (p q : Nat) (K : List SequentialSharedWords.Frame) :
    withInput (encode ns (after x m E es p q K)) x 4 =
      wordTape (K.flatMap SequentialSharedWordSpace.frameWords) ++ wordCode (pre x p q) ++ wordTape E := by
  exact SequentialCaptureCopyMachine.argHead_word_target ns x m p q E es K

/-- Only cursor, control, and retained words change in this return. -/
theorem withInput_update (a b : Packed) (x : List Char) (hclock : a.clock=b.clock) :
    (((withInput a x).set 4 (withInput b x 4)).set 0 (withInput b x 0)).set 2 (withInput b x 2) =
      withInput b x := by
  funext i
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | (change bits a.clock = bits b.clock; rw [hclock])

private theorem next_reachable {g : MGrammar} {x : List Char} {a b c : Config}
    (h : Runs g x a b) (hs : SequentialSharedWords.step g x b = some c) : Runs g x a c := by
  induction h with
  | refl => exact .cons hs (.refl _)
  | cons hh ht ih => exact .cons hh (ih hs)

/-- Execute the complete successful capture return, rather than just its word
component. The copied word, new argument task, continuation frame, all saved
positions, original input, and cleared scratch agree with the actual successor. -/
theorem transition_runs (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E : CaptureEnv)
    (es : List MExp) (p q : Nat) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before m E es p q K)) :
    ∃ T, Complexity.Runs
      (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (program (CBVtoCBN.compilerNodes g e) es)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (before m E es p q K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (after x m E es p q K)) x) T := by
  let ns := CBVtoCBN.compilerNodes g e
  let B := (SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3
  let L := withInput (encode ns (before m E es p q K)) x
  let target := withInput (encode ns (after x m E es p q K)) x
  let tail := wordTape (K.flatMap SequentialSharedWordSpace.frameWords)
  have hb := SequentialSharedStateBound.encoded_state_linear g x e _ h
  change (encode ns (before m E es p q K)).length ≤ _ at hb
  have hx : x.length+2 ≤ B := by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega
  have hL : LenOK B L := SequentialCaptureCopyMachine.withInput_fits _ x
    (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega) hx
  have ha := next_reachable h (actual_step g x m E es p q K)
  have hba := SequentialSharedStateBound.encoded_state_linear g x e _ ha
  change (encode ns (after x m E es p q K)).length ≤ _ at hba
  have htarget : LenOK B target := SequentialCaptureCopyMachine.withInput_fits _ x
    (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega) hx
  have hchain := SequentialSharedCursors.reachable_chain g x e (before m E es p q K) h
  change SequentialCursorChain.Chain 0 (q :: p :: K.filterMap SequentialSharedCursors.frameCursor) x.length at hchain
  cases hchain with
  | cons hz ht => cases ht with
    | cons hqp htail =>
      have hp : p ≤ x.length := htail.bound
      have hcursor : L 0 = cursors (q :: p :: K.filterMap SequentialSharedCursors.frameCursor) := by
        change SequentialCursorEntryMachine.layout (encode ns (before m E es p q K)) 0 = _
        rw [SequentialCursorEntryMachine.layout_cursors]
        rfl
      let C := (blocks (writeFrames ns K).control ++ blocks (oldFields ns es) ++ blocks [K.length+1]) ++ [0]
      have hcount : L 2 = C ++ unary E.length := by
        change withInput (encode ns (before m E es p q K)) [] 2 = _
        rw [before_control,blocks_cons]
        simp only [C,List.append_assoc]
      have hstop : symIs 1 (lastSym C) = false := by rw [lastSym_append]; rfl
      have hword : L 4 = tail ++ wordTape E := before_words ns x m E es p q K
      have hfinal : (tail ++ wordCode (pre x p q) ++ wordTape E).length+2 ≤ B := by
        rw [← after_words ns x m E es p q K]
        exact htarget 4
      obtain ⟨Tw,hw⟩ := SequentialCaptureSpliceMachine.splice_runs x p q
        (K.filterMap SequentialSharedCursors.frameCursor) E C tail L hp hqp hcursor rfl
        hcount hstop hword rfl rfl rfl hL hfinal
      let M := L.set 4 (tail ++ wordCode (pre x p q) ++ wordTape E)
      have hM : LenOK B M := end_fits hw
      obtain ⟨Tc,hc⟩ := drop_saved_runs (src := (0 : Fin 8)) (saved := 7) (tmp := 1)
        (by decide) (by decide) (by decide) hqp htail M
        (by simpa [M,Lists.set] using hcursor) (by rfl) (by rfl) hM
      let N := M.set 0 (cursors (q :: K.filterMap SequentialSharedCursors.frameCursor))
      have hN : LenOK B N := end_fits hc
      have hsrc : N 2 = blocks (writeFrames ns K).control ++ blocks (oldFields ns es) ++
          blocks [E.length,K.length+1] := by
        change withInput (encode ns (before m E es p q K)) [] 2 = _
        exact before_control ns m E es p q K
      have hctrl : (blocks (writeFrames ns K).control ++ blocks (newFields ns es) ++
          blocks [E.length,K.length+1]).length+2 ≤ B := by
        rw [← after_control ns x m E es p q K]
        exact htarget 2
      obtain ⟨Tr,hr⟩ := replace_runs (src := (2 : Fin 8)) (tmp := 1) (by decide)
        [E.length,K.length+1] (oldFields ns es) (newFields ns es) (blocks (writeFrames ns K).control)
        N hsrc (by rfl) hN hctrl
      have he : N.set 2 (blocks (writeFrames ns K).control ++ blocks (newFields ns es) ++
          blocks [E.length,K.length+1]) = target := by
        have hew : tail ++ wordCode (pre x p q) ++ wordTape E = target 4 :=
          (after_words ns x m E es p q K).symm
        have hec : cursors (q :: K.filterMap SequentialSharedCursors.frameCursor) = target 0 := by
          change _ = SequentialCursorEntryMachine.layout (encode ns (after x m E es p q K)) 0
          rw [SequentialCursorEntryMachine.layout_cursors]
          rfl
        have hectrl : blocks (writeFrames ns K).control ++ blocks (newFields ns es) ++
            blocks [E.length,K.length+1] = target 2 := (after_control ns x m E es p q K).symm
        dsimp only [N,M]
        rw [hew,hec,hectrl]
        exact withInput_update _ _ x rfl
      rw [he] at hr
      exact ⟨_,hw.seq (hc.seq hr)⟩

theorem transition_tape (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E : CaptureEnv)
    (es : List MExp) (p q : Nat) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before m E es p q K)) (τ : Tapes 8)
    (hrep : Rep (withInput (encode (CBVtoCBN.compilerNodes g e) (before m E es p q K)) x) τ) :
    ∃ t τ', Exec (TFits ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (program (CBVtoCBN.compilerNodes g e) es).compile τ t (.cont τ') ∧
      Rep (withInput (encode (CBVtoCBN.compilerNodes g e) (after x m E es p q K)) x) τ' := by
  obtain ⟨T,hr⟩ := transition_runs g x e m E es p q K h
  exact tape_runs hr τ hrep

theorem constOK (ns : List CBVtoCBN.CompileNode) (es : List MExp)
    (E : Nat) (hE : 2 ≤ E) : (program ns es).ConstOK E := by
  refine ⟨SequentialCaptureSpliceMachine.constOK E hE,?_,replace_constOK hE _ _ _ _ _⟩
  simp [dropSaved,dropBlock,scan,moveTop,moveAll,clearP,LProg.ConstOK]

theorem finite_alphabet (ns : List CBVtoCBN.CompileNode) (es : List MExp)
    (E : Nat) (hE : 2 ≤ E) : (program ns es).compile.SymOK (E+4) :=
  compile_symOK E (program ns es) (constOK ns es E hE)

end Shallot.MacroPeg.CBV.SequentialArgCapturePackedMachine
