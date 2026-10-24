import MacroPeg.CBV.SequentialReturnControlMachine

/-! Complete compressed returns for sequence, ordered choice, and negation.
The result tag is selected by the actual control-stream dispatcher. -/
namespace Shallot.MacroPeg.CBV.SequentialReturnPackedMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialControlEditMachine
open SequentialReturnControlMachine
open SequentialSharedWords (Config CaptureEnv Runs initial)
open SequentialSharedStateCodec (encode write writeTask writeFrames Input)
open SequentialCursorEntryMachine (layout layout_fits layout_cursors)

inductive Return where
  | seq (b : MExp)
  | alt (b : MExp)
  | notP

def tag : Res → Nat
  | none => 0
  | some none => 1
  | some (some _) => 2

def frame (ret : Return) (p : Nat) : SequentialSharedWords.Frame :=
  match ret with
  | .seq b => .seq b
  | .alt b => .alt b p
  | .notP => .notP p

def before (ret : Return) (m : Nat) (E : CaptureEnv) (p : Nat) (r : Res)
    (K : List SequentialSharedWords.Frame) : Config :=
  ⟨m,.value (.expr r),E,frame ret p :: K⟩

def after (ret : Return) (m : Nat) (E : CaptureEnv) (p : Nat) (r : Res)
    (K : List SequentialSharedWords.Frame) : Config :=
  ⟨m,match ret,r with
    | .seq b,some (some q) => .expr b q
    | .seq _,r => .value (.expr r)
    | .alt b,some none => .expr b p
    | .alt _,r => .value (.expr r)
    | .notP,none => .value (.expr none)
    | .notP,some none => .value (.expr (some (some p)))
    | .notP,some (some _) => .value (.expr (some none)),E,K⟩

theorem actual_step (g : MGrammar) (x : List Char) (ret : Return) (m : Nat)
    (E : CaptureEnv) (p : Nat) (r : Res) (K : List SequentialSharedWords.Frame) :
    SequentialSharedWords.step g x (before ret m E p r K) = some (after ret m E p r K) := by
  cases ret <;> cases r with
  | none => rfl
  | some v => cases v <;> rfl

def erased (ns : List CBVtoCBN.CompileNode) (ret : Return) (t : Nat) : List Nat :=
  [3,t] ++ (writeFrames ns [frame ret 0]).control

def fresh (ns : List CBVtoCBN.CompileNode) (ret : Return) (t : Nat) : List Nat :=
  match ret,t with
  | .seq b,2 | .alt b,1 => [0,SequentialStackCodec.exprId ns b]
  | .notP,1 => [3,2]
  | .notP,2 => [3,1]
  | _,t => [3,t]

def cursorProgram (ret : Return) (t : Nat) : LProg 6 :=
  match ret,t with
  | .seq _,_ | .alt _,1 | .notP,1 => skipP 0
  | .alt _,2 => dropSaved 0 5 1
  | .notP,2 => .seq (dropBlock 0 1) (dropBlock 0 1)
  | _,_ => dropBlock 0 1

def branch (ns : List CBVtoCBN.CompileNode) (ret : Return) (t : Nat) : LProg 6 :=
  .seq (cursorProgram ret t) (.seq (decrementSecond 2 1)
    (replace 2 1 2 (erased ns ret t).length (fresh ns ret t)))

def program (ns : List CBVtoCBN.CompileNode) (ret : Return) : LProg 6 :=
  dispatch 2 1 3 (branch ns ret 0) (branch ns ret 1) (branch ns ret 2)

theorem before_control (ns : List CBVtoCBN.CompileNode) (ret : Return) (m : Nat)
    (E : CaptureEnv) (p : Nat) (r : Res) (K : List SequentialSharedWords.Frame) :
    layout (encode ns (before ret m E p r K)) 2 =
      blocks (writeFrames ns K).control ++ blocks (erased ns ret (tag r)) ++
        blocks [E.length,K.length+1] := by
  rw [SequentialAnyPackedMachine.layout_control]
  have he : (write ns (before ret m E p r K)).control =
      [E.length,K.length+1] ++ erased ns ret (tag r) ++ (writeFrames ns K).control := by
    cases ret <;> cases r with
    | none => simp [write,before,frame,erased,tag,writeTask,writeFrames,
        SequentialSharedStateCodec.writeFrame,Input.append,Input.empty,
        SequentialSharedStateCodec.putControl,SequentialSharedStateCodec.putWords,
        SequentialSharedStateCodec.putExpr,SequentialSharedStateCodec.putCursor]
    | some v => cases v <;> simp [write,before,frame,erased,tag,writeTask,writeFrames,
        SequentialSharedStateCodec.writeFrame,Input.append,Input.empty,
        SequentialSharedStateCodec.putControl,SequentialSharedStateCodec.putWords,
        SequentialSharedStateCodec.putExpr,SequentialSharedStateCodec.putCursor]
  rw [he,blocks_append,blocks_append]
  simp only [List.append_assoc]

theorem after_control (ns : List CBVtoCBN.CompileNode) (ret : Return) (m : Nat)
    (E : CaptureEnv) (p : Nat) (r : Res) (K : List SequentialSharedWords.Frame) :
    layout (encode ns (after ret m E p r K)) 2 =
      blocks (writeFrames ns K).control ++ blocks (fresh ns ret (tag r)) ++ blocks [E.length,K.length] := by
  rw [SequentialAnyPackedMachine.layout_control]
  have he : (write ns (after ret m E p r K)).control =
      [E.length,K.length] ++ fresh ns ret (tag r) ++ (writeFrames ns K).control := by
    cases ret <;> cases r with
    | none => simp [write,after,fresh,tag,writeTask,Input.append,
        SequentialSharedStateCodec.putControl,SequentialSharedStateCodec.putWords]
    | some v => cases v <;> simp [write,after,fresh,tag,writeTask,Input.append,
        SequentialSharedStateCodec.putControl,SequentialSharedStateCodec.putWords,
        SequentialSharedStateCodec.putExpr,SequentialSharedStateCodec.putCursor,
        SequentialStackCodec.writeExpr]
  rw [he,blocks_append,blocks_append]
  simp only [List.append_assoc]

theorem after_layout (ns : List CBVtoCBN.CompileNode) (ret : Return) (m : Nat)
    (E : CaptureEnv) (p : Nat) (r : Res) (K : List SequentialSharedWords.Frame) :
    ((layout (encode ns (before ret m E p r K))).set 0
      (cursors (SequentialSharedCursors.positions (after ret m E p r K)))).set 2
        (layout (encode ns (after ret m E p r K)) 2) =
      layout (encode ns (after ret m E p r K)) := by
  have hw : (encode ns (before ret m E p r K)).words =
      (encode ns (after ret m E p r K)).words := by
    cases ret <;> cases r with
    | none => rfl
    | some v => cases v <;> rfl
  have hm : (encode ns (before ret m E p r K)).clock =
      (encode ns (after ret m E p r K)).clock := rfl
  funext i
  by_cases h0 : i=0
  · subst i
    simp only [Lists.set_same,Lists.set_ne _ _ (by decide : (0 : Fin 6) ≠ 2)]
    exact (layout_cursors ns (after ret m E p r K)).symm
  · by_cases h2 : i=2
    · subst i; simp
    · simp only [Lists.set,if_neg h0,if_neg h2]
      simp only [layout,if_neg h0,if_neg h2]
      rw [hw,hm]

/-- Both current and saved positions are handled by streaming cursor edits. -/
theorem cursor_update (ns : List CBVtoCBN.CompileNode) (ret : Return) (m : Nat)
    (E : CaptureEnv) (p : Nat) (r : Res) (K : List SequentialSharedWords.Frame)
    {n B : Nat} (hchain : SequentialCursorChain.Chain 0
      (SequentialSharedCursors.positions (before ret m E p r K)) n)
    (hL : LenOK B (layout (encode ns (before ret m E p r K)))) :
    ∃ T, Complexity.Runs (LenOK B) (cursorProgram ret (tag r))
      (layout (encode ns (before ret m E p r K)))
      ((layout (encode ns (before ret m E p r K))).set 0
        (cursors (SequentialSharedCursors.positions (after ret m E p r K)))) T := by
  let L := layout (encode ns (before ret m E p r K))
  have htmp : L 1 = [] := rfl
  have hsave : L 5 = [] := rfl
  have hsrc := layout_cursors ns (before ret m E p r K)
  cases ret with
  | seq b =>
    have he : SequentialSharedCursors.positions (after (.seq b) m E p r K) =
        SequentialSharedCursors.positions (before (.seq b) m E p r K) := by
      cases r with
      | none => rfl
      | some v => cases v <;> rfl
    rw [he,← hsrc,Lists.set_get_self]
    exact ⟨1,runs_skip 0 hL⟩
  | alt b =>
    cases r with
    | none =>
      change SequentialCursorChain.Chain 0 (p :: K.filterMap SequentialSharedCursors.frameCursor) n at hchain
      cases hchain with
      | cons hz ht => exact drop_current_runs (by decide : (0 : Fin 6) ≠ 1) ht L hsrc htmp hL
    | some v => cases v with
      | none =>
        have he : SequentialSharedCursors.positions (after (.alt b) m E p (some none) K) =
            SequentialSharedCursors.positions (before (.alt b) m E p (some none) K) := rfl
        rw [he,← hsrc,Lists.set_get_self]
        exact ⟨1,runs_skip 0 hL⟩
      | some q =>
        change SequentialCursorChain.Chain 0 (q :: p :: K.filterMap SequentialSharedCursors.frameCursor) n at hchain
        cases hchain with
        | cons hz ht => cases ht with
          | cons hqp htail =>
            exact drop_saved_runs (by decide : (0 : Fin 6) ≠ 5) (by decide : (0 : Fin 6) ≠ 1)
              (by decide : (5 : Fin 6) ≠ 1) hqp htail L hsrc hsave htmp hL
  | notP =>
    cases r with
    | none =>
      change SequentialCursorChain.Chain 0 (p :: K.filterMap SequentialSharedCursors.frameCursor) n at hchain
      cases hchain with
      | cons hz ht => exact drop_current_runs (by decide : (0 : Fin 6) ≠ 1) ht L hsrc htmp hL
    | some v => cases v with
      | none =>
        have he : SequentialSharedCursors.positions (after .notP m E p (some none) K) =
            SequentialSharedCursors.positions (before .notP m E p (some none) K) := rfl
        rw [he,← hsrc,Lists.set_get_self]
        exact ⟨1,runs_skip 0 hL⟩
      | some q =>
        change SequentialCursorChain.Chain 0 (q :: p :: K.filterMap SequentialSharedCursors.frameCursor) n at hchain
        cases hchain with
        | cons hz ht =>
          obtain ⟨T1,hr⟩ := drop_current_runs (by decide : (0 : Fin 6) ≠ 1) ht L hsrc htmp hL
          cases ht with
          | cons hqp htail =>
            obtain ⟨T2,hr2⟩ := drop_current_runs (by decide : (0 : Fin 6) ≠ 1) htail
              (L.set 0 (cursors (p :: K.filterMap SequentialSharedCursors.frameCursor)))
              (by simp) (by simp [L,layout,Lists.set]) (end_fits hr)
            simpa only [Lists.set_set_u,cursorProgram,tag,after,SequentialSharedCursors.positions,
              SequentialSharedCursors.taskCursor,Option.toList_none,List.nil_append,L] using (show ∃ T, Complexity.Runs (LenOK B) _ _ _ T from ⟨_,hr.seq hr2⟩)

private theorem next_reachable {g : MGrammar} {x : List Char} {a b c : Config}
    (h : Runs g x a b) (hs : SequentialSharedWords.step g x b = some c) : Runs g x a c := by
  induction h with
  | refl => exact .cons hs (.refl _)
  | cons hh ht ih => exact .cons hh (ih hs)

theorem control_update (g : MGrammar) (x : List Char) (e : MExp) (ret : Return)
    (m : Nat) (E : CaptureEnv) (p : Nat) (r : Res) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before ret m E p r K))
    (hL : LenOK (SequentialSharedStateBound.linearFactor g e * (x.length+1)+2)
      ((layout (encode (CBVtoCBN.compilerNodes g e) (before ret m E p r K))).set 0
        (cursors (SequentialSharedCursors.positions (after ret m E p r K))))) :
    ∃ T, Complexity.Runs (LenOK (SequentialSharedStateBound.linearFactor g e * (x.length+1)+2))
      (.seq (decrementSecond 2 1)
        (replace 2 1 2 (erased (CBVtoCBN.compilerNodes g e) ret (tag r)).length
          (fresh (CBVtoCBN.compilerNodes g e) ret (tag r))))
      ((layout (encode (CBVtoCBN.compilerNodes g e) (before ret m E p r K))).set 0
        (cursors (SequentialSharedCursors.positions (after ret m E p r K))))
      (layout (encode (CBVtoCBN.compilerNodes g e) (after ret m E p r K))) T := by
  let ns := CBVtoCBN.compilerNodes g e
  let B := SequentialSharedStateBound.linearFactor g e * (x.length+1)+2
  let L := (layout (encode ns (before ret m E p r K))).set 0
    (cursors (SequentialSharedCursors.positions (after ret m E p r K)))
  have hsrc : L 2 = blocks (writeFrames ns K).control ++ blocks (erased ns ret (tag r)) ++
      blocks [E.length,K.length+1] := by
    simp only [L,Lists.set_ne _ _ (by decide : (2 : Fin 6) ≠ 0),before_control]
  have htmp : L 1 = [] := rfl
  obtain ⟨T1,hd⟩ := decrementSecond_runs (src := (2 : Fin 6)) (tmp := 1) (by decide)
    E.length K.length (blocks (writeFrames ns K).control ++ blocks (erased ns ret (tag r)))
    L hsrc htmp hL
  let N := L.set 2 (blocks (writeFrames ns K).control ++ blocks (erased ns ret (tag r)) ++
    blocks [E.length,K.length])
  have hN : LenOK B N := end_fits hd
  have ha := next_reachable h (actual_step g x ret m E p r K)
  have hb := SequentialSharedStateBound.encoded_state_linear g x e _ ha
  have hl := layout_fits (encode ns (after ret m E p r K)) (B := B)
    (by change (encode ns (after ret m E p r K)).length ≤ _ at hb; dsimp [B]; omega)
  have hfinal : (blocks (writeFrames ns K).control ++ blocks (fresh ns ret (tag r)) ++
      blocks [E.length,K.length]).length+2 ≤ B := by
    rw [← after_control ns ret m E p r K]
    exact hl 2
  obtain ⟨T2,hr⟩ := replace_runs (src := (2 : Fin 6)) (tmp := 1) (by decide)
    [E.length,K.length] (erased ns ret (tag r)) (fresh ns ret (tag r))
    (blocks (writeFrames ns K).control) N (by simp [N])
    (by simp [N,L,layout,Lists.set]) hN hfinal
  have hout : N.set 2 (blocks (writeFrames ns K).control ++ blocks (fresh ns ret (tag r)) ++
      blocks [E.length,K.length]) = layout (encode ns (after ret m E p r K)) := by
    simp only [N,Lists.set_set_u]
    rw [← after_control ns ret m E p r K]
    exact after_layout ns ret m E p r K
  rw [hout] at hr
  exact ⟨_,hd.seq hr⟩

/-- The fixed return program reads its own result tag before executing the
appropriate cursor and control edits; it receives no decoded result flag. -/
theorem transition_runs (g : MGrammar) (x : List Char) (e : MExp) (ret : Return)
    (m : Nat) (E : CaptureEnv) (p : Nat) (r : Res) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before ret m E p r K)) :
    ∃ T, Complexity.Runs (LenOK (SequentialSharedStateBound.linearFactor g e * (x.length+1)+2))
      (program (CBVtoCBN.compilerNodes g e) ret)
      (layout (encode (CBVtoCBN.compilerNodes g e) (before ret m E p r K)))
      (layout (encode (CBVtoCBN.compilerNodes g e) (after ret m E p r K))) T := by
  let ns := CBVtoCBN.compilerNodes g e
  let B := SequentialSharedStateBound.linearFactor g e * (x.length+1)+2
  let L := layout (encode ns (before ret m E p r K))
  have hb := SequentialSharedStateBound.encoded_state_linear g x e _ h
  have hL := layout_fits (encode ns (before ret m E p r K)) (B := B)
    (by change (encode ns (before ret m E p r K)).length ≤ _ at hb; dsimp [B]; omega)
  have hc := SequentialSharedCursors.reachable_chain g x e (before ret m E p r K) h
  obtain ⟨T1,hr⟩ := cursor_update ns ret m E p r K hc hL
  obtain ⟨T2,ht⟩ := control_update g x e ret m E p r K h (end_fits hr)
  have hbranch : Complexity.Runs (LenOK B)
      (select (tag r) (branch ns ret 0) (branch ns ret 1) (branch ns ret 2)) L
      (layout (encode ns (after ret m E p r K))) (T1+T2) := by
    have he : select (tag r) (branch ns ret 0) (branch ns ret 1) (branch ns ret 2) =
        branch ns ret (tag r) := by
      cases r with
      | none => simp [select,tag]
      | some v => cases v <;> simp [select,tag]
    rw [he]
    exact hr.seq ht
  have hsrc : L 2 = (blocks (writeFrames ns K).control ++
      blocks (writeFrames ns [frame ret 0]).control) ++ blocks [tag r] ++
        blocks [E.length,K.length+1,3] := by
    dsimp only [L]
    rw [before_control]
    simp only [erased,blocks_append]
    rw [show blocks [3,tag r] = blocks [tag r] ++ blocks [3] from blocks_append [3] [tag r]]
    rw [show blocks [E.length,K.length+1,3] = blocks [3] ++ blocks [E.length,K.length+1]
      from blocks_append [E.length,K.length+1] [3]]
    simp only [List.append_assoc]
  have htag : tag r ≤ 2 := by cases r with
    | none => decide
    | some v => cases v <;> simp [tag]
  exact dispatch_runs (src := (2 : Fin 6)) (tmp := 1) (by decide)
    [E.length,K.length+1,3] (tag r) htag
    (blocks (writeFrames ns K).control ++ blocks (writeFrames ns [frame ret 0]).control)
    (branch ns ret 0) (branch ns ret 1) (branch ns ret 2) L _ hsrc (by rfl) hL hbranch

theorem transition_tape (g : MGrammar) (x : List Char) (e : MExp) (ret : Return)
    (m : Nat) (E : CaptureEnv) (p : Nat) (r : Res) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before ret m E p r K)) (τ : Tapes 6)
    (hrep : Rep (layout (encode (CBVtoCBN.compilerNodes g e) (before ret m E p r K))) τ) :
    ∃ t τ', Exec (TFits (SequentialSharedStateBound.linearFactor g e * (x.length+1)+2))
      (program (CBVtoCBN.compilerNodes g e) ret).compile τ t (.cont τ') ∧
      Rep (layout (encode (CBVtoCBN.compilerNodes g e) (after ret m E p r K))) τ' := by
  obtain ⟨T,hr⟩ := transition_runs g x e ret m E p r K h
  exact tape_runs hr τ hrep

theorem cursorProgram_constOK (ret : Return) (t E : Nat) :
    (cursorProgram ret t).ConstOK E := by
  unfold cursorProgram
  split <;> simp [skipP,dropSaved,dropBlock,scan,moveTop,moveAll,clearP,LProg.ConstOK]

theorem finite_alphabet (ns : List CBVtoCBN.CompileNode) (ret : Return)
    (E : Nat) (hE : 2 ≤ E) : (program ns ret).compile.SymOK (E+4) := by
  apply compile_symOK E
  have hb : ∀ t, (branch ns ret t).ConstOK E := by
    intro t
    exact ⟨cursorProgram_constOK ret t E,decrementSecond_constOK E _ _,
      replace_constOK hE _ _ _ _ _⟩
  exact dispatch_constOK E _ _ _ _ _ _ (hb 0) (hb 1) (hb 2)

end Shallot.MacroPeg.CBV.SequentialReturnPackedMachine
