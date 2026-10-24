import MacroPeg.CBV.SequentialQueryEnterPackedMachine

/-! Complete query execution with an actual clock test, including zero clock
and absent rules. Arguments remain actual words, never origin pairs. -/
namespace Shallot.MacroPeg.CBV.SequentialQueryPackedMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialControlEditMachine
open SequentialSharedWords (Config CaptureEnv Runs initial)
open SequentialSharedStateCodec (encode write writeTask writeFrames Input)
open SequentialCaptureCopyMachine (withInput wordTape)

private theorem blocks_nil : blocks [] = [] := rfl
private theorem blocks_length (ns : List Nat) : (blocks ns).length = ns.sum+ns.length := by
  rw [blocks,bits_length,SequentialCursorChain.encodeDeltas_length]

def before (m : Nat) (E W : CaptureEnv) (i p : Nat) (K : List SequentialSharedWords.Frame) : Config :=
  ⟨m,.query i W p,E,K⟩

def aborted (m : Nat) (E : CaptureEnv) (K : List SequentialSharedWords.Frame) : Config :=
  ⟨m,.value (.expr none),E,K⟩

def after (g : MGrammar) (m : Nat) (E W : CaptureEnv) (i p : Nat)
    (K : List SequentialSharedWords.Frame) : Config := match m,ruleAtM g.rules i with
  | 0,_ => aborted 0 E K
  | m+1,none => aborted (m+1) E K
  | m+1,some rule => SequentialQueryEnterPackedMachine.after m E W rule.body p K

theorem actual_step (g : MGrammar) (x : List Char) (m : Nat) (E W : CaptureEnv) (i p : Nat)
    (K : List SequentialSharedWords.Frame) (hp : p ≤ x.length) :
    SequentialSharedWords.step g x (before m E W i p K) = some (after g m E W i p K) := by
  cases m with
  | zero => rfl
  | succ m => cases hr : ruleAtM g.rules i <;>
      simp [SequentialSharedWords.step,before,after,aborted,hp,hr,SequentialQueryEnterPackedMachine.after]

theorem reachable_step (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E W : CaptureEnv)
    (i p : Nat) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before m E W i p K)) :
    SequentialSharedWords.step g x (before m E W i p K) = some (after g m E W i p K) := by
  apply actual_step
  have hc := SequentialSharedCursors.reachable_chain g x e _ h
  change SequentialCursorChain.Chain 0 (p :: K.filterMap SequentialSharedCursors.frameCursor) x.length at hc
  cases hc with | cons hz ht => exact ht.bound

def abort : LProg 8 := .seq (SequentialWordRotateMachine.stashAfter 4)
  (.seq (clearP 7) (.seq (dropBlock 0 1) (replace 2 1 2 3 [3,0])))

def program (ns : List CBVtoCBN.CompileNode) (g : MGrammar) (i : Nat) : LProg 8 :=
  match ruleAtM g.rules i with
  | none => abort
  | some rule => .ite 3 (symIs 1)
      (SequentialQueryEnterPackedMachine.program (SequentialStackCodec.exprId ns rule.body)) abort

theorem before_control (ns : List CBVtoCBN.CompileNode) (x : List Char) (m : Nat) (E W : CaptureEnv)
    (i p : Nat) (K : List SequentialSharedWords.Frame) :
    withInput (encode ns (before m E W i p K)) x 2 =
      blocks (writeFrames ns K).control ++ blocks [E.length,K.length,2,i,W.length] := by
  change SequentialCursorEntryMachine.layout (encode ns (before m E W i p K)) 2 = _
  rw [SequentialAnyPackedMachine.layout_control]
  have he : (write ns (before m E W i p K)).control =
      [E.length,K.length,2,i,W.length] ++ (writeFrames ns K).control := by
    simp [write,before,writeTask,Input.append,SequentialSharedStateCodec.putControl,
      SequentialSharedStateCodec.putWords,SequentialSharedStateCodec.putCursor]
  rw [he,blocks_append]

theorem aborted_control (ns : List CBVtoCBN.CompileNode) (x : List Char) (m : Nat)
    (E : CaptureEnv) (K : List SequentialSharedWords.Frame) :
    withInput (encode ns (aborted m E K)) x 2 =
      blocks (writeFrames ns K).control ++ blocks [3,0] ++ blocks [E.length,K.length] := by
  change SequentialCursorEntryMachine.layout (encode ns (aborted m E K)) 2 = _
  rw [SequentialAnyPackedMachine.layout_control]
  have he : (write ns (aborted m E K)).control =
      [E.length,K.length] ++ [3,0] ++ (writeFrames ns K).control := by
    simp [write,aborted,writeTask,Input.append,SequentialSharedStateCodec.putControl,SequentialSharedStateCodec.putWords]
  rw [he,blocks_append,blocks_append]
  simp only [List.append_assoc]

theorem word_streams (ns : List CBVtoCBN.CompileNode) (x : List Char) (m : Nat)
    (E W : CaptureEnv) (i p : Nat) (K : List SequentialSharedWords.Frame) :
    withInput (encode ns (before m E W i p K)) x 4 =
      wordTape (E ++ K.flatMap SequentialSharedWordSpace.frameWords) ++ wordTape W ∧
    withInput (encode ns (aborted m E K)) x 4 =
      wordTape (E ++ K.flatMap SequentialSharedWordSpace.frameWords) := by
  have hb : (encode ns (before m E W i p K)).words =
      SequentialSharedWordSpace.encodeWords (W ++ (E ++ K.flatMap SequentialSharedWordSpace.frameWords)) := by
    simp [encode,SequentialSharedStateCodec.write_words,before,SequentialSharedWordSpace.retainedWords,
      SequentialSharedWordSpace.taskWords]
  have ha : (encode ns (aborted m E K)).words =
      SequentialSharedWordSpace.encodeWords (E ++ K.flatMap SequentialSharedWordSpace.frameWords) := by
    simp [encode,SequentialSharedStateCodec.write_words,aborted,SequentialSharedWordSpace.retainedWords,
      SequentialSharedWordSpace.taskWords]
  constructor
  · change ((encode ns (before m E W i p K)).words.map SequentialCaptureCopyMachine.wordSymbol).reverse = _
    rw [hb]
    exact SequentialCaptureCopyMachine.wordTape_append W _
  · change ((encode ns (aborted m E K)).words.map SequentialCaptureCopyMachine.wordSymbol).reverse = _
    rw [ha]; rfl

/-- This abort subroutine is also specified independently of the branch cause.
The complete query program below invokes it only for zero clock or no rule. -/
theorem abort_runs (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E W : CaptureEnv)
    (i p : Nat) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before m E W i p K)) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      abort (withInput (encode (CBVtoCBN.compilerNodes g e) (before m E W i p K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (aborted m E K)) x) T := by
  let ns := CBVtoCBN.compilerNodes g e
  let B := (SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3
  let L := withInput (encode ns (before m E W i p K)) x
  let target := withInput (encode ns (aborted m E K)) x
  let C := blocks (writeFrames ns K).control ++ [0]
  let tail := wordTape (E ++ K.flatMap SequentialSharedWordSpace.frameWords)
  have hb := SequentialSharedStateBound.encoded_state_linear g x e _ h
  change (encode ns (before m E W i p K)).length ≤ _ at hb
  have hL : LenOK B L := SequentialCaptureCopyMachine.withInput_fits _ x
    (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega)
    (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega)
  have hctrl : L 2 = C ++ unary W.length ++ blocks [E.length,K.length,2,i] := by
    dsimp only [L]
    rw [before_control]
    rw [show [E.length,K.length,2,i,W.length] = [E.length,K.length,2,i] ++ [W.length] from rfl,blocks_append]
    simp [C,blocks_cons,blocks_nil,List.append_assoc]
  have hs := hL 4
  dsimp only [L] at hs
  rw [(word_streams ns x m E W i p K).1] at hs
  obtain ⟨T1,hr⟩ := SequentialWordRotateMachine.stashAfter_runs [E.length,K.length,2,i] W C tail L
    hctrl (by rw [lastSym_append]; rfl) (word_streams ns x m E W i p K).1 rfl hL
    (by change 0+(wordTape W).length+2 ≤ B; simp only [List.length_append] at hs; omega)
  let N := (L.set 4 tail).set 7 (L 7 ++ (wordTape W).reverse)
  have hc := clear_runs (tmp := (7 : Fin 8)) N (end_fits hr)
  let M := N.set 7 []
  have hchain := SequentialSharedCursors.reachable_chain g x e _ h
  change SequentialCursorChain.Chain 0 (p :: K.filterMap SequentialSharedCursors.frameCursor) x.length at hchain
  cases hchain with
  | cons hz ht =>
    have hcursor : M 0 = cursors (p :: K.filterMap SequentialSharedCursors.frameCursor) := by
      change SequentialCursorEntryMachine.layout (encode ns (before m E W i p K)) 0 = _
      rw [SequentialCursorEntryMachine.layout_cursors]; rfl
    obtain ⟨T2,hd⟩ := drop_current_runs (src := (0 : Fin 8)) (tmp := 1) (by decide) ht M hcursor rfl (end_fits hc)
    let R := M.set 0 (cursors (K.filterMap SequentialSharedCursors.frameCursor))
    have hsrc : R 2 = (blocks (writeFrames ns K).control) ++ blocks [2,i,W.length] ++ blocks [E.length,K.length] := by
      change withInput (encode ns (before m E W i p K)) x 2 = _
      rw [before_control]
      rw [show [E.length,K.length,2,i,W.length] = [E.length,K.length] ++ [2,i,W.length] from rfl,blocks_append]
      simp only [List.append_assoc]
    have hcap : (blocks (writeFrames ns K).control ++ blocks [3,0] ++ blocks [E.length,K.length]).length+2 ≤ B := by
      have hh := hL 2
      change (withInput (encode ns (before m E W i p K)) x 2).length+2 ≤ B at hh
      rw [before_control] at hh
      simp [List.length_append,blocks_length] at hh ⊢
      omega
    obtain ⟨T3,hu⟩ := replace_runs (src := (2 : Fin 8)) (tmp := 1) (by decide)
      [E.length,K.length] [2,i,W.length] [3,0] (blocks (writeFrames ns K).control) R hsrc rfl (end_fits hd) hcap
    have he : R.set 2 (blocks (writeFrames ns K).control ++ blocks [3,0] ++ blocks [E.length,K.length]) = target := by
      have hw : tail = target 4 := (word_streams ns x m E W i p K).2.symm
      have hp : cursors (K.filterMap SequentialSharedCursors.frameCursor) = target 0 := by
        change _ = SequentialCursorEntryMachine.layout (encode ns (aborted m E K)) 0
        rw [SequentialCursorEntryMachine.layout_cursors]; rfl
      have hct : blocks (writeFrames ns K).control ++ blocks [3,0] ++ blocks [E.length,K.length] = target 2 :=
        (aborted_control ns x m E K).symm
      have hbase : M = L.set 4 tail := by
        simp only [M,N,Lists.set_set_u]
        have h7 : (L.set 4 tail) 7 = [] := rfl
        rw [← h7,Lists.set_get_self]
      dsimp only [R]
      rw [hbase,hw,hp,hct]
      exact SequentialArgCapturePackedMachine.withInput_update _ _ x rfl
    rw [he] at hu
    exact ⟨_,hr.seq (hc.seq (hd.seq hu))⟩

/-- The rule option is fixed by the grammar; the clock branch is read from
its actual unary tape, with no external validity or clock flag. -/
theorem transition_runs (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E W : CaptureEnv)
    (i p : Nat) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before m E W i p K)) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (program (CBVtoCBN.compilerNodes g e) g i)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (before m E W i p K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (after g m E W i p K)) x) T := by
  let ns := CBVtoCBN.compilerNodes g e
  let B := (SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3
  let L := withInput (encode ns (before m E W i p K)) x
  have hb := SequentialSharedStateBound.encoded_state_linear g x e _ h
  change (encode ns (before m E W i p K)).length ≤ _ at hb
  have hL : LenOK B L := SequentialCaptureCopyMachine.withInput_fits _ x
    (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega)
    (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega)
  cases hrule : ruleAtM g.rules i with
  | none =>
    have he : after g m E W i p K = aborted m E K := by cases m <;> simp [after,hrule]
    rw [he]
    simpa only [program,hrule] using abort_runs g x e m E W i p K h
  | some rule =>
    cases m with
    | zero =>
      obtain ⟨T,hr⟩ := abort_runs g x e 0 E W i p K h
      have hcond : symIs 1 (lastSym (L 3)) = false := by
        change symIs 1 (lastSym (blocks [0])) = false
        rfl
      exact ⟨_,by simpa only [program,hrule,after] using hr.iteF hL hcond⟩
    | succ m =>
      obtain ⟨T,hr⟩ := SequentialQueryEnterPackedMachine.transition_runs g x e m E W i p K rule hrule h
      have hcond : symIs 1 (lastSym (L 3)) = true := by
        change symIs 1 (lastSym (blocks [m+1])) = true
        have he : blocks [m+1] = blocks [m] ++ [1] := by simp [blocks_cons,blocks_nil,List.replicate_succ']
        rw [he,lastSym_append]; rfl
      exact ⟨_,by simpa only [program,hrule,after] using hr.iteT hL hcond⟩

theorem transition_tape (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E W : CaptureEnv)
    (i p : Nat) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before m E W i p K)) (τ : Tapes 8)
    (hrep : Rep (withInput (encode (CBVtoCBN.compilerNodes g e) (before m E W i p K)) x) τ) :
    ∃ t τ', Exec (TFits ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (program (CBVtoCBN.compilerNodes g e) g i).compile τ t (.cont τ') ∧
      Rep (withInput (encode (CBVtoCBN.compilerNodes g e) (after g m E W i p K)) x) τ' := by
  obtain ⟨T,hr⟩ := transition_runs g x e m E W i p K h
  exact tape_runs hr τ hrep

theorem finite_alphabet (ns : List CBVtoCBN.CompileNode) (g : MGrammar) (i E : Nat) (hE : 2 ≤ E) :
    (program ns g i).compile.SymOK (E+4) := by
  apply compile_symOK E
  have ha : abort.ConstOK E := by
    refine ⟨SequentialWordRotateMachine.stashAfter_constOK E 4,?_,?_,replace_constOK hE _ _ _ _ _⟩
    · simp [clearP,LProg.ConstOK]
    · simp [dropBlock,scan,moveTop,moveAll,clearP,LProg.ConstOK]
  cases hr : ruleAtM g.rules i with
  | none => simpa only [program,hr] using ha
  | some rule => simp only [program,hr,LProg.ConstOK]; exact ⟨SequentialQueryEnterPackedMachine.constOK _ E hE,ha⟩

end Shallot.MacroPeg.CBV.SequentialQueryPackedMachine
