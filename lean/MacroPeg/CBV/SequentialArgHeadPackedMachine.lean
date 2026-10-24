import MacroPeg.CBV.SequentialArgCapturePackedMachine

/-! A complete argument-head return with runtime result-tag dispatch. -/
namespace Shallot.MacroPeg.CBV.SequentialArgHeadPackedMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialControlEditMachine
open SequentialReturnControlMachine
open SequentialSharedWords (Config CaptureEnv Runs initial)
open SequentialSharedStateCodec (encode write writeTask writeFrames Input)
open SequentialCaptureCopyMachine (withInput)
open SequentialReturnPackedMachine (tag)

/-- Undefined and failure, polymorphically for expression and argument results. -/
def bad {α : Type} (failure : Bool) : Option (Option α) := if failure then some none else none

def badTag (failure : Bool) : Nat := if failure then 1 else 0

def before (m : Nat) (E : CaptureEnv) (es : List MExp) (p : Nat) (r : Res)
    (K : List SequentialSharedWords.Frame) : Config := ⟨m,.value (.expr r),E,.argHead es p :: K⟩

def after (x : List Char) (m : Nat) (E : CaptureEnv) (es : List MExp) (p : Nat) (r : Res)
    (K : List SequentialSharedWords.Frame) : Config := match r with
  | none => ⟨m,.value (.args none),E,K⟩
  | some none => ⟨m,.value (.args (some none)),E,K⟩
  | some (some q) => SequentialArgCapturePackedMachine.after x m E es p q K

theorem actual_step (g : MGrammar) (x : List Char) (m : Nat) (E : CaptureEnv)
    (es : List MExp) (p : Nat) (r : Res) (K : List SequentialSharedWords.Frame) :
    SequentialSharedWords.step g x (before m E es p r K) = some (after x m E es p r K) := by
  cases r with
  | none => rfl
  | some v => cases v <;> rfl

def oldFields (ns : List CBVtoCBN.CompileNode) (es : List MExp) (t : Nat) : List Nat :=
  [3,t,4] ++ SequentialStackCodec.writeExprs ns es

def badBranch (ns : List CBVtoCBN.CompileNode) (es : List MExp) (t : Nat) : LProg 8 :=
  .seq (dropBlock 0 1) (.seq (decrementSecond 2 1)
    (replace 2 1 2 (oldFields ns es t).length [4,t]))

def program (ns : List CBVtoCBN.CompileNode) (es : List MExp) : LProg 8 :=
  dispatch 2 1 3 (badBranch ns es 0) (badBranch ns es 1) (SequentialArgCapturePackedMachine.program ns es)

theorem before_control (ns : List CBVtoCBN.CompileNode) (x : List Char) (m : Nat)
    (E : CaptureEnv) (es : List MExp) (p : Nat) (r : Res) (K : List SequentialSharedWords.Frame) :
    withInput (encode ns (before m E es p r K)) x 2 =
      blocks (writeFrames ns K).control ++ blocks (oldFields ns es (tag r)) ++ blocks [E.length,K.length+1] := by
  change SequentialCursorEntryMachine.layout (encode ns (before m E es p r K)) 2 = _
  rw [SequentialAnyPackedMachine.layout_control]
  have he : (write ns (before m E es p r K)).control =
      [E.length,K.length+1] ++ oldFields ns es (tag r) ++ (writeFrames ns K).control := by
    cases r with
    | none => simp [write,before,oldFields,tag,writeTask,writeFrames,SequentialSharedStateCodec.writeFrame,
        Input.append,SequentialSharedStateCodec.putControl,SequentialSharedStateCodec.putWords,
        SequentialSharedStateCodec.putExprs,SequentialSharedStateCodec.putCursor]
    | some v => cases v <;> simp [write,before,oldFields,tag,writeTask,writeFrames,SequentialSharedStateCodec.writeFrame,
        Input.append,SequentialSharedStateCodec.putControl,SequentialSharedStateCodec.putWords,
        SequentialSharedStateCodec.putExprs,SequentialSharedStateCodec.putCursor]
  rw [he,blocks_append,blocks_append]
  simp only [List.append_assoc]

def badAfter (failure : Bool) (m : Nat) (E : CaptureEnv) (K : List SequentialSharedWords.Frame) : Config :=
  ⟨m,.value (.args (bad failure)),E,K⟩

theorem bad_after_control (ns : List CBVtoCBN.CompileNode) (x : List Char)
    (failure : Bool) (m : Nat) (E : CaptureEnv) (K : List SequentialSharedWords.Frame) :
    withInput (encode ns (badAfter failure m E K)) x 2 =
      blocks (writeFrames ns K).control ++ blocks [4,badTag failure] ++ blocks [E.length,K.length] := by
  change SequentialCursorEntryMachine.layout (encode ns (badAfter failure m E K)) 2 = _
  rw [SequentialAnyPackedMachine.layout_control]
  have he : (write ns (badAfter failure m E K)).control =
      [E.length,K.length] ++ [4,badTag failure] ++ (writeFrames ns K).control := by
    cases failure <;> simp [write,badAfter,bad,badTag,writeTask,Input.append,
      SequentialSharedStateCodec.putControl,SequentialSharedStateCodec.putWords]
  rw [he,blocks_append,blocks_append]
  simp only [List.append_assoc]

private theorem next_reachable {g : MGrammar} {x : List Char} {a b c : Config}
    (h : Runs g x a b) (hs : SequentialSharedWords.step g x b = some c) : Runs g x a c := by
  induction h with
  | refl => exact .cons hs (.refl _)
  | cons hh ht ih => exact .cons hh (ih hs)

theorem bad_runs (g : MGrammar) (x : List Char) (e : MExp) (failure : Bool)
    (m : Nat) (E : CaptureEnv) (es : List MExp) (p : Nat) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before m E es p (bad failure) K)) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (badBranch (CBVtoCBN.compilerNodes g e) es (badTag failure))
      (withInput (encode (CBVtoCBN.compilerNodes g e) (before m E es p (bad failure) K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (badAfter failure m E K)) x) T := by
  let ns := CBVtoCBN.compilerNodes g e
  let B := (SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3
  let L := withInput (encode ns (before m E es p (bad failure) K)) x
  let target := withInput (encode ns (badAfter failure m E K)) x
  have hb := SequentialSharedStateBound.encoded_state_linear g x e _ h
  change (encode ns (before m E es p (bad failure) K)).length ≤ _ at hb
  have hx : x.length+2 ≤ B := by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega
  have hL : LenOK B L := SequentialCaptureCopyMachine.withInput_fits _ x
    (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega) hx
  have hs : SequentialSharedWords.step g x (before m E es p (bad failure) K) =
      some (badAfter failure m E K) := by cases failure <;> rfl
  have ha := next_reachable h hs
  have hba := SequentialSharedStateBound.encoded_state_linear g x e _ ha
  change (encode ns (badAfter failure m E K)).length ≤ _ at hba
  have htarget : LenOK B target := SequentialCaptureCopyMachine.withInput_fits _ x
    (by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega) hx
  have hc := SequentialSharedCursors.reachable_chain g x e _ h
  have hpos : SequentialSharedCursors.positions (before m E es p (bad failure) K) =
      p :: K.filterMap SequentialSharedCursors.frameCursor := by cases failure <;> rfl
  rw [hpos] at hc
  cases hc with
  | cons hz ht =>
    have hcursor : L 0 = cursors (p :: K.filterMap SequentialSharedCursors.frameCursor) := by
      change SequentialCursorEntryMachine.layout (encode ns (before m E es p (bad failure) K)) 0 = _
      rw [SequentialCursorEntryMachine.layout_cursors,hpos]
    obtain ⟨Tc,hr⟩ := drop_current_runs (src := (0 : Fin 8)) (tmp := 1) (by decide) ht L hcursor rfl hL
    let M := L.set 0 (cursors (K.filterMap SequentialSharedCursors.frameCursor))
    have hsrc : M 2 = blocks (writeFrames ns K).control ++ blocks (oldFields ns es (badTag failure)) ++
        blocks [E.length,K.length+1] := by
      have he : tag (bad (α := Nat) failure) = badTag failure := by cases failure <;> rfl
      change withInput (encode ns (before m E es p (bad failure) K)) x 2 = _
      rw [before_control,he]
    obtain ⟨Td,hd⟩ := decrementSecond_runs (src := (2 : Fin 8)) (tmp := 1) (by decide)
      E.length K.length (blocks (writeFrames ns K).control ++ blocks (oldFields ns es (badTag failure)))
      M hsrc rfl (end_fits hr)
    let N := M.set 2 (blocks (writeFrames ns K).control ++ blocks (oldFields ns es (badTag failure)) ++
      blocks [E.length,K.length])
    have hcap : (blocks (writeFrames ns K).control ++ blocks [4,badTag failure] ++
        blocks [E.length,K.length]).length+2 ≤ B := by
      rw [← bad_after_control ns x failure m E K]
      exact htarget 2
    obtain ⟨Tr,ht⟩ := replace_runs (src := (2 : Fin 8)) (tmp := 1) (by decide)
      [E.length,K.length] (oldFields ns es (badTag failure)) [4,badTag failure]
      (blocks (writeFrames ns K).control) N (by rfl) rfl (end_fits hd) hcap
    have he : N.set 2 (blocks (writeFrames ns K).control ++ blocks [4,badTag failure] ++
        blocks [E.length,K.length]) = target := by
      have hw : L 4 = target 4 := by cases failure <;> rfl
      have hew : L.set 4 (target 4) = L := by rw [← hw,Lists.set_get_self]
      have hec : cursors (K.filterMap SequentialSharedCursors.frameCursor) = target 0 := by
        change _ = SequentialCursorEntryMachine.layout (encode ns (badAfter failure m E K)) 0
        rw [SequentialCursorEntryMachine.layout_cursors]
        cases failure <;> rfl
      have hectrl : blocks (writeFrames ns K).control ++ blocks [4,badTag failure] ++
          blocks [E.length,K.length] = target 2 := (bad_after_control ns x failure m E K).symm
      dsimp only [N]
      rw [Lists.set_set_u,hectrl]
      change (L.set 0 _).set 2 (target 2) = target
      rw [hec,← hew]
      exact SequentialArgCapturePackedMachine.withInput_update _ _ x rfl
    rw [he] at ht
    exact ⟨_,hr.seq (hd.seq ht)⟩

/-- All expression outcomes enter the same fixed program. It reads their tag
from the old control stream before selecting the appropriate actual return. -/
theorem transition_runs (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E : CaptureEnv)
    (es : List MExp) (p : Nat) (r : Res) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before m E es p r K)) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (program (CBVtoCBN.compilerNodes g e) es)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (before m E es p r K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (after x m E es p r K)) x) T := by
  let ns := CBVtoCBN.compilerNodes g e
  let B := (SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3
  let L := withInput (encode ns (before m E es p r K)) x
  let target := withInput (encode ns (after x m E es p r K)) x
  obtain ⟨T,hr⟩ : ∃ T, Complexity.Runs (LenOK B)
      (select (tag r) (badBranch ns es 0) (badBranch ns es 1) (SequentialArgCapturePackedMachine.program ns es))
      L target T := by
    cases r with
    | none => simpa [select,tag,badTag,bad,badAfter,after,L,target,ns,B] using bad_runs g x e false m E es p K h
    | some v => cases v with
      | none => simpa [select,tag,badTag,bad,badAfter,after,L,target,ns,B] using bad_runs g x e true m E es p K h
      | some q => simpa [select,tag,after,before,SequentialArgCapturePackedMachine.before,L,target,ns,B] using SequentialArgCapturePackedMachine.transition_runs g x e m E es p q K h
  have hL : LenOK B L := by
    have hb := SequentialSharedStateBound.encoded_state_linear g x e _ h
    change (encode ns (before m E es p r K)).length ≤ _ at hb
    apply SequentialCaptureCopyMachine.withInput_fits
    · dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega
    · dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega
  have hsrc : L 2 = (blocks (writeFrames ns K).control ++ blocks ([4] ++ SequentialStackCodec.writeExprs ns es)) ++
      blocks [tag r] ++ blocks [E.length,K.length+1,3] := by
    change withInput (encode ns (before m E es p r K)) x 2 = _
    rw [before_control]
    have ho : oldFields ns es (tag r) = [3] ++ [tag r] ++ ([4] ++ SequentialStackCodec.writeExprs ns es) := rfl
    rw [ho,blocks_append,blocks_append]
    rw [show blocks [E.length,K.length+1,3] = blocks [3] ++ blocks [E.length,K.length+1]
      from blocks_append [E.length,K.length+1] [3]]
    simp only [blocks_append,List.append_assoc]
  have htag : tag r ≤ 2 := by
    cases r with
    | none => decide
    | some v => cases v <;> simp [tag]
  exact dispatch_runs (src := (2 : Fin 8)) (tmp := 1) (by decide)
    [E.length,K.length+1,3] (tag r) htag
    (blocks (writeFrames ns K).control ++ blocks ([4] ++ SequentialStackCodec.writeExprs ns es))
    (badBranch ns es 0) (badBranch ns es 1) (SequentialArgCapturePackedMachine.program ns es)
    L target hsrc rfl hL hr

theorem transition_tape (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E : CaptureEnv)
    (es : List MExp) (p : Nat) (r : Res) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before m E es p r K)) (τ : Tapes 8)
    (hrep : Rep (withInput (encode (CBVtoCBN.compilerNodes g e) (before m E es p r K)) x) τ) :
    ∃ t τ', Exec (TFits ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (program (CBVtoCBN.compilerNodes g e) es).compile τ t (.cont τ') ∧
      Rep (withInput (encode (CBVtoCBN.compilerNodes g e) (after x m E es p r K)) x) τ' := by
  obtain ⟨T,hr⟩ := transition_runs g x e m E es p r K h
  exact tape_runs hr τ hrep

theorem finite_alphabet (ns : List CBVtoCBN.CompileNode) (es : List MExp)
    (E : Nat) (hE : 2 ≤ E) : (program ns es).compile.SymOK (E+4) := by
  apply compile_symOK E
  have hb : ∀ t, (badBranch ns es t).ConstOK E := by
    intro t
    refine ⟨?_,decrementSecond_constOK E _ _,replace_constOK hE _ _ _ _ _⟩
    simp [dropBlock,scan,moveTop,moveAll,clearP,LProg.ConstOK]
  exact dispatch_constOK E _ _ _ _ _ _ (hb 0) (hb 1) (SequentialArgCapturePackedMachine.constOK ns es E hE)

end Shallot.MacroPeg.CBV.SequentialArgHeadPackedMachine
