import MacroPeg.CBV.SequentialQueryInstallMachine

/-! Complete positive-clock query entry: install the actual argument words,
save the caller environment, enter the rule body, and lower the shared clock. -/
namespace Shallot.MacroPeg.CBV.SequentialQueryEnterPackedMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialControlEditMachine
open SequentialSharedWords (Config CaptureEnv Runs initial)
open SequentialSharedStateCodec (Packed encode write writeTask writeFrames Input)
open SequentialCaptureCopyMachine (withInput)

private theorem blocks_nil : blocks [] = [] := rfl

def before (m : Nat) (E W : CaptureEnv) (i p : Nat) (K : List SequentialSharedWords.Frame) : Config :=
  ⟨m+1,.query i W p,E,K⟩

def after (m : Nat) (E W : CaptureEnv) (body : MExp) (p : Nat) (K : List SequentialSharedWords.Frame) : Config :=
  ⟨m,.expr body p,W,.scope E :: K⟩

theorem actual_step (g : MGrammar) (x : List Char) (m : Nat) (E W : CaptureEnv)
    (i p : Nat) (K : List SequentialSharedWords.Frame) (rule : MRule)
    (hrule : ruleAtM g.rules i = some rule) (hp : p ≤ x.length) :
    SequentialSharedWords.step g x (before m E W i p K) = some (after m E W rule.body p K) := by
  simp [SequentialSharedWords.step,before,after,hp,hrule]

def program (body : Nat) : LProg 8 := .seq (SequentialQueryInstallMachine.program body) (.pop 3)

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

theorem after_control (ns : List CBVtoCBN.CompileNode) (x : List Char) (m : Nat) (E W : CaptureEnv)
    (body : MExp) (p : Nat) (K : List SequentialSharedWords.Frame) :
    withInput (encode ns (after m E W body p K)) x 2 =
      blocks (writeFrames ns K).control ++
        blocks [W.length,K.length+1,0,SequentialStackCodec.exprId ns body,7,E.length] := by
  change SequentialCursorEntryMachine.layout (encode ns (after m E W body p K)) 2 = _
  rw [SequentialAnyPackedMachine.layout_control]
  have he : (write ns (after m E W body p K)).control =
      [W.length,K.length+1,0,SequentialStackCodec.exprId ns body,7,E.length] ++ (writeFrames ns K).control := by
    simp [write,after,writeTask,writeFrames,SequentialSharedStateCodec.writeFrame,Input.append,
      SequentialSharedStateCodec.putControl,SequentialSharedStateCodec.putWords,SequentialSharedStateCodec.putExpr,
      SequentialSharedStateCodec.putCursor,SequentialStackCodec.writeExpr]
  rw [he,blocks_append]

theorem other_streams (ns : List CBVtoCBN.CompileNode) (m : Nat) (E W : CaptureEnv)
    (i p : Nat) (body : MExp) (K : List SequentialSharedWords.Frame) :
    (encode ns (before m E W i p K)).cursors = (encode ns (after m E W body p K)).cursors ∧
    (encode ns (before m E W i p K)).words = (encode ns (after m E W body p K)).words := by
  constructor
  · simp [encode,SequentialSharedStateCodec.write_cursors,before,after,SequentialSharedCursors.positions,
      SequentialSharedCursors.taskCursor,SequentialSharedCursors.frameCursor]
  · simp [encode,SequentialSharedStateCodec.write_words,before,after,SequentialSharedWordSpace.retainedWords,
      SequentialSharedWordSpace.taskWords,SequentialSharedWordSpace.frameWords,List.append_assoc]

theorem clock_pop (ns : List CBVtoCBN.CompileNode) (x : List Char) (m : Nat) (E W : CaptureEnv)
    (i p : Nat) (body : MExp) (K : List SequentialSharedWords.Frame) :
    (withInput (encode ns (before m E W i p K)) x 3).dropLast =
      withInput (encode ns (after m E W body p K)) x 3 := by
  change (blocks [m+1]).dropLast = blocks [m]
  have he : blocks [m+1] = blocks [m] ++ [1] := by
    simp [blocks_cons,blocks_nil,List.replicate_succ']
  rw [he,List.dropLast_concat]

theorem control_clock_update (a b : Packed) (x : List Char)
    (hp : a.cursors=b.cursors) (hw : a.words=b.words) :
    ((withInput a x).set 2 (withInput b x 2)).set 3 (withInput b x 3) = withInput b x := by
  funext j
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 := by omega
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | (change bits a.cursors = bits b.cursors; rw [hp]) |
    (change (a.words.map SequentialCaptureCopyMachine.wordSymbol).reverse =
      (b.words.map SequentialCaptureCopyMachine.wordSymbol).reverse; rw [hw])

private theorem next_reachable {g : MGrammar} {x : List Char} {a b c : Config}
    (h : Runs g x a b) (hs : SequentialSharedWords.step g x b = some c) : Runs g x a c := by
  induction h with
  | refl => exact .cons hs (.refl _)
  | cons hh ht ih => exact .cons hh (ih hs)

theorem transition_runs (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E W : CaptureEnv)
    (i p : Nat) (K : List SequentialSharedWords.Frame) (rule : MRule)
    (hrule : ruleAtM g.rules i = some rule)
    (h : Runs g x (initial g x e) (before m E W i p K)) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (program (SequentialStackCodec.exprId (CBVtoCBN.compilerNodes g e) rule.body))
      (withInput (encode (CBVtoCBN.compilerNodes g e) (before m E W i p K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (after m E W rule.body p K)) x) T := by
  let ns := CBVtoCBN.compilerNodes g e
  let B := (SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3
  let L := withInput (encode ns (before m E W i p K)) x
  let target := withInput (encode ns (after m E W rule.body p K)) x
  have hp : p ≤ x.length := by
    have hc := SequentialSharedCursors.reachable_chain g x e _ h
    change SequentialCursorChain.Chain 0 (p :: K.filterMap SequentialSharedCursors.frameCursor) x.length at hc
    cases hc with | cons hz ht => exact ht.bound
  have hb := SequentialSharedStateBound.encoded_state_linear g x e _ h
  change (encode ns (before m E W i p K)).length ≤ _ at hb
  have hx : x.length+2 ≤ B := by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega
  have hL : LenOK B L := SequentialCaptureCopyMachine.withInput_fits _ x
    (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega) hx
  have ha := next_reachable h (actual_step g x m E W i p K rule hrule hp)
  have hba := SequentialSharedStateBound.encoded_state_linear g x e _ ha
  change (encode ns (after m E W rule.body p K)).length ≤ _ at hba
  have htarget : LenOK B target := SequentialCaptureCopyMachine.withInput_fits _ x
    (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega) hx
  have hsrc : L 2 = blocks (writeFrames ns K).control ++ blocks [E.length,K.length,2,i,W.length] :=
    before_control ns x m E W i p K
  have hcap : (blocks (writeFrames ns K).control ++
      blocks [W.length,K.length+1,0,SequentialStackCodec.exprId ns rule.body,7,E.length]).length+2 ≤ B := by
    rw [← after_control ns x m E W rule.body p K]
    exact htarget 2
  obtain ⟨T1,hr⟩ := SequentialQueryInstallMachine.install_runs (SequentialStackCodec.exprId ns rule.body)
    E.length K.length i W.length (blocks (writeFrames ns K).control) L hsrc rfl rfl rfl hL hcap
  let M := L.set 2 (blocks (writeFrames ns K).control ++
    blocks [W.length,K.length+1,0,SequentialStackCodec.exprId ns rule.body,7,E.length])
  have hM : LenOK B M := end_fits hr
  have hpop := runs_pop (i := (3 : Fin 8)) hM (by
    apply lenOK_set hM 3
    have hh := hM 3
    simp only [List.length_dropLast]
    omega)
  have hctrl : blocks (writeFrames ns K).control ++
      blocks [W.length,K.length+1,0,SequentialStackCodec.exprId ns rule.body,7,E.length] = target 2 :=
    (after_control ns x m E W rule.body p K).symm
  have hclock : (M 3).dropLast = target 3 := clock_pop ns x m E W i p rule.body K
  have he : M.set 3 (M 3).dropLast = target := by
    rw [hclock]
    dsimp only [M]
    rw [hctrl]
    have ho := other_streams ns m E W i p rule.body K
    exact control_clock_update _ _ x ho.1 ho.2
  rw [he] at hpop
  exact ⟨_,hr.seq hpop⟩

theorem transition_tape (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E W : CaptureEnv)
    (i p : Nat) (K : List SequentialSharedWords.Frame) (rule : MRule)
    (hrule : ruleAtM g.rules i = some rule)
    (h : Runs g x (initial g x e) (before m E W i p K)) (τ : Tapes 8)
    (hrep : Rep (withInput (encode (CBVtoCBN.compilerNodes g e) (before m E W i p K)) x) τ) :
    ∃ t τ', Exec (TFits ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (program (SequentialStackCodec.exprId (CBVtoCBN.compilerNodes g e) rule.body)).compile τ t (.cont τ') ∧
      Rep (withInput (encode (CBVtoCBN.compilerNodes g e) (after m E W rule.body p K)) x) τ' := by
  obtain ⟨T,hr⟩ := transition_runs g x e m E W i p K rule hrule h
  exact tape_runs hr τ hrep

theorem constOK (body E : Nat) (hE : 2 ≤ E) : (program body).ConstOK E :=
  ⟨SequentialQueryInstallMachine.constOK body E hE,trivial⟩

theorem finite_alphabet (body E : Nat) (hE : 2 ≤ E) : (program body).compile.SymOK (E+4) :=
  compile_symOK E (program body) (constOK body E hE)

end Shallot.MacroPeg.CBV.SequentialQueryEnterPackedMachine
