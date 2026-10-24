import MacroPeg.CBV.SequentialParamMatchMachine

/-! Complete compressed Seq parameter transitions, with actual environment
lookup and original-input matching. -/
namespace Shallot.MacroPeg.CBV.SequentialParamPackedMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialControlEditMachine
open SequentialSharedWords (Config CaptureEnv Runs initial)
open SequentialSharedStateCodec (encode write writeTask writeFrames Input)
open SequentialCaptureCopyMachine (withInput wordTape)

def matched (x : List Char) (E : CaptureEnv) (k p : Nat) : Option (List Char) :=
  E[k]?.bind (fun w => Shallot.stripPrefix? w (sfx x p))

def before (k m : Nat) (E : CaptureEnv) (p : Nat) (K : List SequentialSharedWords.Frame) : Config :=
  ⟨m,.expr (.param k) p,E,K⟩

def after (x : List Char) (k m : Nat) (E : CaptureEnv) (p : Nat)
    (K : List SequentialSharedWords.Frame) : Config :=
  ⟨m,.value (.expr (some ((matched x E k p).map List.length))),E,K⟩

def tag (r : Option (List Char)) : Nat := if r.isSome then 2 else 1

theorem actual_step (g : MGrammar) (x : List Char) (k m : Nat) (E : CaptureEnv) (p : Nat)
    (K : List SequentialSharedWords.Frame) :
    SequentialSharedWords.step g x (before k m E p K) = some (after x k m E p K) := by
  simp only [before,after,SequentialSharedWords.step,SequentialSharedWords.atom,matched]
  cases he : E[k]? with
  | none => rfl
  | some w => cases hr : Shallot.stripPrefix? w (sfx x p) <;> simp [hr]

def finishBranch (t : Nat) : LProg 8 := .seq (.pop 2) (replace 2 1 2 2 [3,t])
def finish : LProg 8 := .ite 2 (symIs 1) (finishBranch 2) (finishBranch 1)
def program (k : Nat) : LProg 8 := .seq (SequentialParamMatchMachine.program k) finish

theorem before_control (ns : List CBVtoCBN.CompileNode) (k m : Nat) (E : CaptureEnv) (p : Nat)
    (K : List SequentialSharedWords.Frame) :
    withInput (encode ns (before k m E p K)) [] 2 =
      blocks (writeFrames ns K).control ++ blocks [0,SequentialStackCodec.exprId ns (.param k)] ++
        blocks [E.length,K.length] := by
  change SequentialCursorEntryMachine.layout (encode ns (before k m E p K)) 2 = _
  rw [SequentialAnyPackedMachine.layout_control]
  have hw : (write ns (before k m E p K)).control =
      [E.length,K.length] ++ [0,SequentialStackCodec.exprId ns (.param k)] ++ (writeFrames ns K).control := by
    simp [write,before,writeTask,Input.append,SequentialSharedStateCodec.putControl,
      SequentialSharedStateCodec.putWords,SequentialSharedStateCodec.putExpr,
      SequentialSharedStateCodec.putCursor,SequentialStackCodec.writeExpr]
  rw [hw,blocks_append,blocks_append]
  simp only [List.append_assoc]

theorem after_control (ns : List CBVtoCBN.CompileNode) (x : List Char) (k m : Nat)
    (E : CaptureEnv) (p : Nat) (K : List SequentialSharedWords.Frame) :
    withInput (encode ns (after x k m E p K)) x 2 =
      blocks (writeFrames ns K).control ++ blocks [3,tag (matched x E k p)] ++ blocks [E.length,K.length] := by
  change SequentialCursorEntryMachine.layout (encode ns (after x k m E p K)) 2 = _
  rw [SequentialAnyPackedMachine.layout_control]
  have hw : (write ns (after x k m E p K)).control =
      [E.length,K.length] ++ [3,tag (matched x E k p)] ++ (writeFrames ns K).control := by
    cases hr : matched x E k p <;>
      simp [write,after,writeTask,Input.append,SequentialSharedStateCodec.putControl,
        SequentialSharedStateCodec.putWords,SequentialSharedStateCodec.putCursor,hr,tag]
  rw [hw,blocks_append,blocks_append]
  simp only [List.append_assoc]

theorem finish_runs (r : Option (List Char)) (saved : List Nat) (id : Nat) (C : List Nat)
    (L : Lists 8) {B : Nat} (hsrc : L 2=(C ++ blocks [0,id] ++ blocks saved) ++ [if r.isSome then 1 else 0])
    (hsaved : saved.length=2) (h1 : L 1=[]) (hL : LenOK B L)
    (hcap : (C ++ blocks [3,tag r] ++ blocks saved).length+2 ≤ B) :
    ∃ T, Complexity.Runs (LenOK B) finish L
      (L.set 2 (C ++ blocks [3,tag r] ++ blocks saved)) T := by
  have hn : LenOK B (L.set 2 (C ++ blocks [0,id] ++ blocks saved)) := by
    apply lenOK_set hL 2
    have hh := hL 2
    rw [hsrc] at hh
    simp only [List.length_append,List.length_singleton] at hh ⊢
    omega
  have hp := runs_pop (i := (2 : Fin 8)) hL (by simpa only [hsrc,List.dropLast_concat] using hn)
  simp only [hsrc,List.dropLast_concat] at hp
  let N := L.set 2 (C ++ blocks [0,id] ++ blocks saved)
  obtain ⟨Tr,hr⟩ := replace_runs (src := (2 : Fin 8)) (tmp := 1) (by decide) saved [0,id]
    [3,tag r] C N rfl (by simpa [N,Lists.set] using h1) hn hcap
  rw [hsaved] at hr
  have hb : Complexity.Runs (LenOK B) (finishBranch (tag r)) L
      (L.set 2 (C ++ blocks [3,tag r] ++ blocks saved)) (1+Tr) := by
    simpa only [finishBranch,N,List.length_cons,List.length_nil,Lists.set_set_u] using hp.seq hr
  have hc : lastSym (L 2)=(if r.isSome then 1 else 0)+4 := by rw [hsrc,lastSym_append]
  cases r with
  | none => exact ⟨_,hb.iteF hL (by simp [hc,symIs])⟩
  | some rest => exact ⟨_,hb.iteT hL (by simp [hc,symIs])⟩

private theorem next_reachable {g : MGrammar} {x : List Char} {a b c : Config}
    (h : Runs g x a b) (hs : SequentialSharedWords.step g x b = some c) : Runs g x a c := by
  induction h with
  | refl => exact .cons hs (.refl _)
  | cons hh ht ih => exact .cons hh (ih hs)

/-- Execute an actual initialized reachable parameter task through its
complete encoded successor, preserving clock, environments, and original input. -/
theorem transition_runs (g : MGrammar) (x : List Char) (e : MExp) (k m : Nat)
    (E : CaptureEnv) (p : Nat) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before k m E p K)) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (program k) (withInput (encode (CBVtoCBN.compilerNodes g e) (before k m E p K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (after x k m E p K)) x) T := by
  let ns := CBVtoCBN.compilerNodes g e
  let B := (SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3
  let L := withInput (encode ns (before k m E p K)) x
  let target := withInput (encode ns (after x k m E p K)) x
  let ps := K.filterMap SequentialSharedCursors.frameCursor
  let r := matched x E k p
  have hb := SequentialSharedStateBound.encoded_state_linear g x e _ h
  change (encode ns (before k m E p K)).length ≤ _ at hb
  have hi : x.length+2 ≤ B := by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega
  have hL : LenOK B L := SequentialCaptureCopyMachine.withInput_fits _ x
    (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega) hi
  have hLmore : LenOK (B-1) L := SequentialCaptureCopyMachine.withInput_fits _ x
    (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega)
    (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega)
  have hchain := SequentialSharedCursors.reachable_chain g x e _ h
  have hpos : SequentialSharedCursors.positions (before k m E p K)=p :: ps := rfl
  rw [hpos] at hchain
  cases hchain with
  | cons hz hc =>
    have hcur : L 0=cursors (p :: ps) := by
      change SequentialCursorEntryMachine.layout (encode ns (before k m E p K)) 0 = _
      rw [SequentialCursorEntryMachine.layout_cursors,hpos]
    have hword : L 4=wordTape (K.flatMap SequentialSharedWordSpace.frameWords) ++ wordTape E := by
      change ((encode ns (before k m E p K)).words.map SequentialCaptureCopyMachine.wordSymbol).reverse = _
      simp only [encode,SequentialSharedStateCodec.write_words]
      change wordTape (SequentialSharedWordSpace.retainedWords (before k m E p K)) = _
      change wordTape (E ++ K.flatMap SequentialSharedWordSpace.frameWords) = _
      exact SequentialCaptureCopyMachine.wordTape_append E _
    let C := (blocks (writeFrames ns K).control ++ blocks [0,SequentialStackCodec.exprId ns (.param k)] ++
      blocks [K.length]) ++ [0]
    have hctrl : L 2=C ++ unary E.length := by
      change withInput (encode ns (before k m E p K)) [] 2 = _
      rw [before_control,blocks_cons E.length [K.length]]
      simp only [C,List.append_assoc]
    obtain ⟨Tm,hm⟩ := SequentialParamMatchMachine.match_runs k E x p ps hc hc.bound C
      (wordTape (K.flatMap SequentialSharedWordSpace.frameWords)) L hctrl
      (by rw [lastSym_append]; rfl) hcur hword rfl rfl rfl rfl hL (by have hh := hLmore 2; omega)
    let M := SequentialParamMatchMachine.result L ps r
    have hM : LenOK B M := end_fits hm
    have hs := next_reachable h (actual_step g x k m E p K)
    have hba := SequentialSharedStateBound.encoded_state_linear g x e _ hs
    change (encode ns (after x k m E p K)).length ≤ _ at hba
    have htarget : LenOK B target := SequentialCaptureCopyMachine.withInput_fits _ x
      (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega) hi
    have hsrc : M 2=(blocks (writeFrames ns K).control ++
        blocks [0,SequentialStackCodec.exprId ns (.param k)] ++ blocks [E.length,K.length]) ++
          [if r.isSome then 1 else 0] := by
      change L 2 ++ _ = _
      change withInput (encode ns (before k m E p K)) [] 2 ++ _ = _
      rw [before_control]
    obtain ⟨Tf,hf⟩ := finish_runs r [E.length,K.length] (SequentialStackCodec.exprId ns (.param k))
      (blocks (writeFrames ns K).control) M hsrc rfl rfl hM (by
        rw [← after_control ns x k m E p K]
        exact htarget 2)
    have he2 : blocks (writeFrames ns K).control ++ blocks [3,tag r] ++ blocks [E.length,K.length] = target 2 :=
      (after_control ns x k m E p K).symm
    have he0 : cursors ((r.map List.length).toList ++ ps)=target 0 := by
      change _=SequentialCursorEntryMachine.layout (encode ns (after x k m E p K)) 0
      rw [SequentialCursorEntryMachine.layout_cursors]
      cases hr : matched x E k p <;>
        simp [r,after,SequentialSharedCursors.positions,SequentialSharedCursors.taskCursor,hr,ps]
    have he4 : L 4=target 4 := by
      change ( (encode ns (before k m E p K)).words.map SequentialCaptureCopyMachine.wordSymbol).reverse =
        ((encode ns (after x k m E p K)).words.map SequentialCaptureCopyMachine.wordSymbol).reverse
      have hw : (encode ns (before k m E p K)).words=(encode ns (after x k m E p K)).words := by
        cases hr : matched x E k p <;>
          simp [encode,SequentialSharedStateCodec.write_words,before,after,hr,
            SequentialSharedWordSpace.retainedWords,SequentialSharedWordSpace.taskWords]
      rw [hw]
    have hu := SequentialArgCapturePackedMachine.withInput_update (encode ns (before k m E p K))
      (encode ns (after x k m E p K)) x (by rfl)
    change ((L.set 4 (target 4)).set 0 (target 0)).set 2 (target 2)=target at hu
    rw [← he4,Lists.set_get_self] at hu
    have he : M.set 2 (blocks (writeFrames ns K).control ++ blocks [3,tag r] ++ blocks [E.length,K.length])=target := by
      rw [he2]
      have hh : M.set 2 (target 2)=(L.set 0 (target 0)).set 2 (target 2) := by
        funext j
        by_cases h0 : j=0 <;> by_cases h2 : j=2 <;>
          simp [M,SequentialParamMatchMachine.result,Lists.set,h0,h2,he0]
      rw [hh]
      exact hu
    rw [he] at hf
    exact ⟨_,hm.seq hf⟩

theorem transition_tape (g : MGrammar) (x : List Char) (e : MExp) (k m : Nat)
    (E : CaptureEnv) (p : Nat) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before k m E p K)) (tau : Tapes 8)
    (hrep : Rep (withInput (encode (CBVtoCBN.compilerNodes g e) (before k m E p K)) x) tau) :
    ∃ t tau', Exec (TFits ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (program k).compile tau t (.cont tau') ∧
      Rep (withInput (encode (CBVtoCBN.compilerNodes g e) (after x k m E p K)) x) tau' := by
  obtain ⟨T,hr⟩ := transition_runs g x e k m E p K h
  exact tape_runs hr tau hrep

theorem finite_alphabet (k E : Nat) (hE : 2 ≤ E) : (program k).compile.SymOK (E+4) := by
  apply compile_symOK E
  have hb (t : Nat) : (finishBranch t).ConstOK E := ⟨trivial,replace_constOK hE _ _ _ _ _⟩
  exact ⟨SequentialParamMatchMachine.constOK k E hE,hb 2,hb 1⟩

end Shallot.MacroPeg.CBV.SequentialParamPackedMachine
