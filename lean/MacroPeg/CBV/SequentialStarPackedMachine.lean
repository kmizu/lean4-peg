import MacroPeg.CBV.SequentialCursorProgressMachine

/-! Complete compressed repetition returns. Progress is tested on the actual
cursor-difference tape before choosing reentry or undefined termination. -/
namespace Shallot.MacroPeg.CBV.SequentialStarPackedMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialControlEditMachine
open SequentialReturnControlMachine
open SequentialSharedWords (Config CaptureEnv Runs initial)
open SequentialSharedStateCodec (encode write writeTask writeFrames Input)
open SequentialCaptureCopyMachine (withInput)
open SequentialReturnPackedMachine (tag)

inductive Mode where
  | undefined
  | done
  | again
  | stalled

def chosen (p : Nat) : Res → Mode
  | none => .undefined
  | some none => .done
  | some (some q) => if q<p then .again else .stalled

def before (a : MExp) (m : Nat) (E : CaptureEnv) (p : Nat) (r : Res)
    (K : List SequentialSharedWords.Frame) : Config := ⟨m,.value (.expr r),E,.star a p :: K⟩

def after (a : MExp) (m : Nat) (E : CaptureEnv) (p : Nat) (r : Res)
    (K : List SequentialSharedWords.Frame) : Config :=
  ⟨m,match r with
    | none => .value (.expr none)
    | some none => .value (.expr (some (some p)))
    | some (some q) => if q<p then .expr (.star a) q else .value (.expr none),E,K⟩

theorem actual_step (g : MGrammar) (x : List Char) (a : MExp) (m : Nat) (E : CaptureEnv)
    (p : Nat) (r : Res) (K : List SequentialSharedWords.Frame) :
    SequentialSharedWords.step g x (before a m E p r K)=some (after a m E p r K) := by
  cases r with
  | none => rfl
  | some v => cases v with
    | none => rfl
    | some q => by_cases hq : q<p <;> simp [before,after,SequentialSharedWords.step,hq]

def oldFields (ns : List CBVtoCBN.CompileNode) (a : MExp) (t : Nat) : List Nat :=
  [3,t,3,SequentialStackCodec.exprId ns a]

def freshFields (ns : List CBVtoCBN.CompileNode) (a : MExp) : Mode → List Nat
  | .again => [0,SequentialStackCodec.exprId ns (.star a)]
  | .done => [3,2]
  | _ => [3,0]

def cursorProgram : Mode → LProg 8
  | .done => skipP 0
  | .again => dropSaved 0 5 1
  | .stalled => .seq (dropBlock 0 1) (dropBlock 0 1)
  | .undefined => dropBlock 0 1

def branch (ns : List CBVtoCBN.CompileNode) (a : MExp) (t : Nat) (mode : Mode) : LProg 8 :=
  .seq (cursorProgram mode) (.seq (decrementSecond 2 1)
    (replace 2 1 2 (oldFields ns a t).length (freshFields ns a mode)))

def success (ns : List CBVtoCBN.CompileNode) (a : MExp) : LProg 8 :=
  SequentialCursorProgressMachine.program (branch ns a 2 .again) (branch ns a 2 .stalled)

def program (ns : List CBVtoCBN.CompileNode) (a : MExp) : LProg 8 :=
  dispatch 2 1 3 (branch ns a 0 .undefined) (branch ns a 1 .done) (success ns a)

def nextPositions (p : Nat) (r : Res) (ps : List Nat) : List Nat := match r with
  | none => ps
  | some none => p :: ps
  | some (some q) => if q<p then q :: ps else ps

theorem before_control (ns : List CBVtoCBN.CompileNode) (a : MExp) (m : Nat) (E : CaptureEnv)
    (p : Nat) (r : Res) (K : List SequentialSharedWords.Frame) :
    withInput (encode ns (before a m E p r K)) [] 2 = blocks (writeFrames ns K).control ++
      blocks (oldFields ns a (tag r)) ++ blocks [E.length,K.length+1] := by
  change SequentialCursorEntryMachine.layout (encode ns (before a m E p r K)) 2 = _
  rw [SequentialAnyPackedMachine.layout_control]
  have he : (write ns (before a m E p r K)).control =
      [E.length,K.length+1] ++ oldFields ns a (tag r) ++ (writeFrames ns K).control := by
    cases r with
    | none => simp [write,before,oldFields,tag,writeTask,writeFrames,SequentialSharedStateCodec.writeFrame,
        Input.append,SequentialSharedStateCodec.putControl,SequentialSharedStateCodec.putWords,
        SequentialSharedStateCodec.putCursor,SequentialSharedStateCodec.putExpr,SequentialStackCodec.writeExpr]
    | some v => cases v <;> simp [write,before,oldFields,tag,writeTask,writeFrames,SequentialSharedStateCodec.writeFrame,
        Input.append,SequentialSharedStateCodec.putControl,SequentialSharedStateCodec.putWords,
        SequentialSharedStateCodec.putCursor,SequentialSharedStateCodec.putExpr,SequentialStackCodec.writeExpr]
  rw [he,blocks_append,blocks_append]
  simp only [List.append_assoc]

theorem after_control (ns : List CBVtoCBN.CompileNode) (a : MExp) (m : Nat) (E : CaptureEnv)
    (p : Nat) (r : Res) (K : List SequentialSharedWords.Frame) :
    withInput (encode ns (after a m E p r K)) [] 2 = blocks (writeFrames ns K).control ++
      blocks (freshFields ns a (chosen p r)) ++ blocks [E.length,K.length] := by
  change SequentialCursorEntryMachine.layout (encode ns (after a m E p r K)) 2 = _
  rw [SequentialAnyPackedMachine.layout_control]
  have aux (r : Res) (kind : Mode) (task : SequentialSharedWords.Task)
      (he : (after a m E p r K).task=task) (hf : (writeTask ns task).control=freshFields ns a kind) :
      blocks (write ns (after a m E p r K)).control = blocks (writeFrames ns K).control ++
        blocks (freshFields ns a kind) ++ blocks [E.length,K.length] := by
    change blocks ([E.length,K.length] ++ (writeTask ns (after a m E p r K).task).control ++
      (writeFrames ns K).control) = _
    rw [he,hf,blocks_append,blocks_append]
    simp only [List.append_assoc]
  cases r with
  | none => exact aux none .undefined _ rfl rfl
  | some v => cases v with
    | none => exact aux (some none) .done _ rfl rfl
    | some q =>
      by_cases hq : q<p
      · simpa only [chosen,if_pos hq] using aux (some (some q)) .again (.expr (.star a) q)
          (by simp [after,hq]) rfl
      · simpa only [chosen,if_neg hq] using aux (some (some q)) .stalled (.value (.expr none))
          (by simp [after,hq]) rfl

theorem before_positions (a : MExp) (m : Nat) (E : CaptureEnv) (p : Nat) (r : Res)
    (K : List SequentialSharedWords.Frame) : SequentialSharedCursors.positions (before a m E p r K)=
      (r.bind id).toList ++ p :: K.filterMap SequentialSharedCursors.frameCursor := by
  cases r with
  | none => rfl
  | some v => cases v <;> rfl

theorem after_positions (a : MExp) (m : Nat) (E : CaptureEnv) (p : Nat) (r : Res)
    (K : List SequentialSharedWords.Frame) : SequentialSharedCursors.positions (after a m E p r K)=
      nextPositions p r (K.filterMap SequentialSharedCursors.frameCursor) := by
  cases r with
  | none => rfl
  | some v => cases v with
    | none => rfl
    | some q => by_cases hq : q<p <;> simp [after,nextPositions,hq,SequentialSharedCursors.positions,
        SequentialSharedCursors.taskCursor]

/-- Cursor editing includes the undefined, successful termination, progress,
and zero-progress branches. The scratch buffers are restored each time. -/
theorem cursor_runs (p : Nat) (r : Res) (ps : List Nat) (n : Nat)
    (hchain : SequentialCursorChain.Chain 0 ((r.bind id).toList ++ p :: ps) n)
    (L : Lists 8) {B : Nat} (hcur : L 0=cursors ((r.bind id).toList ++ p :: ps))
    (h1 : L 1=[]) (h5 : L 5=[]) (hL : LenOK B L) :
    ∃ T, Complexity.Runs (LenOK B) (cursorProgram (chosen p r)) L
      (L.set 0 (cursors (nextPositions p r ps))) T := by
  cases r with
  | none =>
    cases hchain with
    | cons hp ht => exact drop_current_runs (src := (0 : Fin 8)) (tmp := 1) (by decide) ht L hcur h1 hL
  | some v => cases v with
    | none =>
      change L 0=cursors (p :: ps) at hcur
      have he : L.set 0 (cursors (p :: ps))=L := by rw [← hcur,Lists.set_get_self]
      change ∃ T, Complexity.Runs (LenOK B) (skipP 0) L (L.set 0 (cursors (p :: ps))) T
      rw [he]
      exact ⟨1,runs_skip 0 hL⟩
    | some q =>
      cases hchain with
      | cons hq htq => cases htq with
        | cons hqp htp =>
          by_cases hl : q<p
          · simpa only [chosen,nextPositions,cursorProgram,if_pos hl] using drop_saved_runs (src := (0 : Fin 8))
              (saved := 5) (tmp := 1) (by decide) (by decide) (by decide) hqp htp L hcur h5 h1 hL
          · obtain ⟨T1,hfirst⟩ := drop_current_runs (src := (0 : Fin 8)) (tmp := 1) (by decide)
              (.cons hqp htp) L hcur h1 hL
            let N := L.set 0 (cursors (p :: ps))
            obtain ⟨T2,hsecond⟩ := drop_current_runs (src := (0 : Fin 8)) (tmp := 1) (by decide) htp N rfl
              (by simpa [N,Lists.set] using h1) (end_fits hfirst)
            have he : N.set 0 (cursors ps)=L.set 0 (cursors ps) := by simp only [N,Lists.set_set_u]
            rw [he] at hsecond
            exact ⟨_,by simpa only [chosen,nextPositions,cursorProgram,if_neg hl] using hfirst.seq hsecond⟩


theorem complete_update (ns : List CBVtoCBN.CompileNode) (x : List Char) (a : MExp) (m : Nat)
    (E : CaptureEnv) (p : Nat) (r : Res) (K : List SequentialSharedWords.Frame) :
    ((withInput (encode ns (before a m E p r K)) x).set 0
      (cursors (nextPositions p r (K.filterMap SequentialSharedCursors.frameCursor)))).set 2
        (withInput (encode ns (after a m E p r K)) x 2) = withInput (encode ns (after a m E p r K)) x := by
  let L := withInput (encode ns (before a m E p r K)) x
  let target := withInput (encode ns (after a m E p r K)) x
  have hw : (encode ns (before a m E p r K)).words=(encode ns (after a m E p r K)).words := by
    cases r with
    | none => rfl
    | some v => cases v with
      | none => rfl
      | some q => by_cases hq : q<p <;>
          simp [encode,SequentialSharedStateCodec.write_words,before,after,hq,
            SequentialSharedWordSpace.retainedWords,SequentialSharedWordSpace.taskWords,
            SequentialSharedWordSpace.frameWords]
  have he4 : L 4=target 4 := by
    change ((encode ns (before a m E p r K)).words.map SequentialCaptureCopyMachine.wordSymbol).reverse =
      ((encode ns (after a m E p r K)).words.map SequentialCaptureCopyMachine.wordSymbol).reverse
    rw [hw]
  have he0 : cursors (nextPositions p r (K.filterMap SequentialSharedCursors.frameCursor))=target 0 := by
    change _=SequentialCursorEntryMachine.layout (encode ns (after a m E p r K)) 0
    rw [SequentialCursorEntryMachine.layout_cursors,after_positions]
  have hu := SequentialArgCapturePackedMachine.withInput_update (encode ns (before a m E p r K))
    (encode ns (after a m E p r K)) x (by rfl)
  change ((L.set 4 (target 4)).set 0 (target 0)).set 2 (target 2)=target at hu
  rw [← he4,Lists.set_get_self] at hu
  simpa only [he0] using hu

private theorem next_reachable {g : MGrammar} {x : List Char} {a b c : Config}
    (h : Runs g x a b) (hs : SequentialSharedWords.step g x b=some c) : Runs g x a c := by
  induction h with
  | refl => exact .cons hs (.refl _)
  | cons hh ht ih => exact .cons hh (ih hs)

theorem branch_runs (g : MGrammar) (x : List Char) (e a : MExp) (m : Nat) (E : CaptureEnv)
    (p : Nat) (r : Res) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before a m E p r K)) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (branch (CBVtoCBN.compilerNodes g e) a (tag r) (chosen p r))
      (withInput (encode (CBVtoCBN.compilerNodes g e) (before a m E p r K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (after a m E p r K)) x) T := by
  let ns := CBVtoCBN.compilerNodes g e
  let B := (SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3
  let L := withInput (encode ns (before a m E p r K)) x
  let target := withInput (encode ns (after a m E p r K)) x
  have hb := SequentialSharedStateBound.encoded_state_linear g x e _ h
  change (encode ns (before a m E p r K)).length ≤ _ at hb
  have hi : x.length+2 ≤ B := by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega
  have hL : LenOK B L := SequentialCaptureCopyMachine.withInput_fits _ x
    (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega) hi
  have hc := SequentialSharedCursors.reachable_chain g x e _ h
  rw [before_positions] at hc
  have hcur : L 0=cursors ((r.bind id).toList ++ p :: K.filterMap SequentialSharedCursors.frameCursor) := by
    change SequentialCursorEntryMachine.layout (encode ns (before a m E p r K)) 0 = _
    rw [SequentialCursorEntryMachine.layout_cursors,before_positions]
  obtain ⟨Tc,hc⟩ := cursor_runs p r (K.filterMap SequentialSharedCursors.frameCursor) x.length hc L hcur rfl rfl hL
  let M := L.set 0 (cursors (nextPositions p r (K.filterMap SequentialSharedCursors.frameCursor)))
  have hctrl : M 2=blocks (writeFrames ns K).control ++ blocks (oldFields ns a (tag r)) ++ blocks [E.length,K.length+1] :=
    before_control ns a m E p r K
  obtain ⟨Td,hd⟩ := decrementSecond_runs (src := (2 : Fin 8)) (tmp := 1) (by decide) E.length K.length
    (blocks (writeFrames ns K).control ++ blocks (oldFields ns a (tag r))) M hctrl rfl (end_fits hc)
  let N := M.set 2 (blocks (writeFrames ns K).control ++ blocks (oldFields ns a (tag r)) ++ blocks [E.length,K.length])
  have hs := next_reachable h (actual_step g x a m E p r K)
  have hba := SequentialSharedStateBound.encoded_state_linear g x e _ hs
  change (encode ns (after a m E p r K)).length ≤ _ at hba
  have htarget : LenOK B target := SequentialCaptureCopyMachine.withInput_fits _ x
    (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega) hi
  obtain ⟨Tr,hr⟩ := replace_runs (src := (2 : Fin 8)) (tmp := 1) (by decide) [E.length,K.length]
    (oldFields ns a (tag r)) (freshFields ns a (chosen p r)) (blocks (writeFrames ns K).control)
    N rfl rfl (end_fits hd) (by
      rw [← after_control ns a m E p r K]
      exact htarget 2)
  have he : N.set 2 (blocks (writeFrames ns K).control ++ blocks (freshFields ns a (chosen p r)) ++
      blocks [E.length,K.length])=target := by
    simp only [N,Lists.set_set_u]
    rw [← after_control ns a m E p r K]
    exact complete_update ns x a m E p r K
  rw [he] at hr
  exact ⟨_,hc.seq (hd.seq hr)⟩

/-- Both the result tag and the progress comparison are read from the actual
source state. No decoded result or externally computed progress bit is given. -/
theorem transition_runs (g : MGrammar) (x : List Char) (e a : MExp) (m : Nat) (E : CaptureEnv)
    (p : Nat) (r : Res) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before a m E p r K)) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (program (CBVtoCBN.compilerNodes g e) a)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (before a m E p r K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (after a m E p r K)) x) T := by
  let ns := CBVtoCBN.compilerNodes g e
  let B := (SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3
  let L := withInput (encode ns (before a m E p r K)) x
  let target := withInput (encode ns (after a m E p r K)) x
  obtain ⟨Tb,hb⟩ := branch_runs g x e a m E p r K h
  have hL : LenOK B L := by
    obtain ⟨t,ht,hx⟩ := hb
    exact hx.q_start
  have hr : ∃ T, Complexity.Runs (LenOK B)
      (select (tag r) (branch ns a 0 .undefined) (branch ns a 1 .done) (success ns a)) L target T := by
    cases r with
    | none => exact ⟨Tb,hb⟩
    | some v => cases v with
      | none => exact ⟨Tb,hb⟩
      | some q =>
        have hc := SequentialSharedCursors.reachable_chain g x e _ h
        rw [before_positions] at hc
        cases hc with
        | cons hq htq => cases htq with
          | cons hqp htp =>
            have hcur : L 0=cursors (q :: p :: K.filterMap SequentialSharedCursors.frameCursor) := by
              change SequentialCursorEntryMachine.layout (encode ns (before a m E p (some (some q)) K)) 0 = _
              rw [SequentialCursorEntryMachine.layout_cursors,before_positions]
              rfl
            have hh : Complexity.Runs (LenOK B)
                (if q<p then branch ns a 2 .again else branch ns a 2 .stalled) L target Tb := by
              by_cases hl : q<p <;> simpa [chosen,tag,hl] using hb
            exact SequentialCursorProgressMachine.dispatch_runs _ _ q p _ L target hcur rfl hL hh
  obtain ⟨Tr,hr⟩ := hr
  have hsrc : L 2=blocks (writeFrames ns K).control ++ blocks [3,SequentialStackCodec.exprId ns a] ++
      blocks [tag r] ++ blocks [E.length,K.length+1,3] := by
    change withInput (encode ns (before a m E p r K)) [] 2 = _
    rw [before_control]
    simp only [oldFields,show [3,tag r,3,SequentialStackCodec.exprId ns a] =
      [3,tag r] ++ [3,SequentialStackCodec.exprId ns a] from rfl,blocks_append]
    simp only [blocks_cons,show blocks []=[] from rfl,List.nil_append,List.append_assoc]
  have htag : tag r ≤ 2 := by cases r with
    | none => decide
    | some v => cases v <;> simp [tag]
  exact dispatch_runs (src := (2 : Fin 8)) (tmp := 1) (by decide) [E.length,K.length+1,3]
    (tag r) htag (blocks (writeFrames ns K).control ++ blocks [3,SequentialStackCodec.exprId ns a])
    (branch ns a 0 .undefined) (branch ns a 1 .done) (success ns a) L target hsrc rfl hL hr

theorem transition_tape (g : MGrammar) (x : List Char) (e a : MExp) (m : Nat) (E : CaptureEnv)
    (p : Nat) (r : Res) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before a m E p r K)) (tau : Tapes 8)
    (hrep : Rep (withInput (encode (CBVtoCBN.compilerNodes g e) (before a m E p r K)) x) tau) :
    ∃ t tau', Exec (TFits ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (program (CBVtoCBN.compilerNodes g e) a).compile tau t (.cont tau') ∧
      Rep (withInput (encode (CBVtoCBN.compilerNodes g e) (after a m E p r K)) x) tau' := by
  obtain ⟨T,hr⟩ := transition_runs g x e a m E p r K h
  exact tape_runs hr tau hrep

theorem cursor_constOK (mode : Mode) (E : Nat) : (cursorProgram mode).ConstOK E := by
  cases mode <;> simp [cursorProgram,dropSaved,dropBlock,scan,moveTop,moveAll,clearP,skipP,LProg.ConstOK]

theorem branch_constOK (ns : List CBVtoCBN.CompileNode) (a : MExp) (t : Nat) (mode : Mode)
    (E : Nat) (hE : 2 ≤ E) : (branch ns a t mode).ConstOK E :=
  ⟨cursor_constOK mode E,decrementSecond_constOK E _ _,replace_constOK hE _ _ _ _ _⟩

theorem finite_alphabet (ns : List CBVtoCBN.CompileNode) (a : MExp) (E : Nat) (hE : 2 ≤ E) :
    (program ns a).compile.SymOK (E+4) := by
  apply compile_symOK E
  apply dispatch_constOK E _ _ _ _ _ _
  · exact branch_constOK ns a 0 .undefined E hE
  · exact branch_constOK ns a 1 .done E hE
  · exact SequentialCursorProgressMachine.constOK _ _ E (branch_constOK ns a 2 .again E hE)
      (branch_constOK ns a 2 .stalled E hE)

end Shallot.MacroPeg.CBV.SequentialStarPackedMachine
