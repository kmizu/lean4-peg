import MacroPeg.CBV.SequentialPackedInitMachine

/-! Decide acceptance from the actual final result tag and compressed cursor,
then halt with that decision. No decoded result is an input to the program. -/
namespace Shallot.MacroPeg.CBV.SequentialPackedHaltMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialControlEditMachine
open SequentialSharedStateCodec (encode writeTask writeFrames)
open SequentialCaptureCopyMachine (characters)
open SequentialReturnPackedMachine (tag)

def accept (r : Res) : Bool := decide (r=some (some 0))

def resultTest : LProg 8 := .ite 2 (symIs 1)
  (.seq (moveTop 2 1) (.ite 2 (symIs 1) (.ite 0 (symIs 1) (.halt false) (.halt true)) (.halt false))) (.halt false)

def program : LProg 8 := .seq (saveMany 2 1 3) resultTest

private theorem blocks_nil : blocks []=[] := rfl

theorem halt_runs (r : Res) (L : Lists 8) {B : Nat}
    (hctrl : L 2=blocks [tag r] ++ blocks [0,0,3]) (hcur : L 0=cursors (r.bind id).toList)
    (h1 : L 1=[]) (hL : LenOK B L) :
    ∃ M T, Halts (LenOK B) program L (accept r) M T := by
  have hsize := hL 2
  rw [hctrl] at hsize
  simp only [List.length_append] at hsize
  obtain ⟨Ts,hs⟩ := saveMany_runs (src := (2 : Fin 8)) (tmp := 1) (by decide) [0,0,3] (blocks [tag r]) L hctrl hL
    (by simp only [h1,List.length_nil]; omega)
  let N := (L.set 2 (blocks [tag r])).set 1 (blocks [0,0,3]).reverse
  have heN : (L.set 2 (blocks [tag r])).set 1 (L 1 ++ (blocks [0,0,3]).reverse)=N := by simp [N,h1]
  rw [heN] at hs
  have hN : LenOK B N := end_fits hs
  cases r with
  | none =>
    have hh : Halts (LenOK B) resultTest N false N 2 := (halts_halt hN).iteF hN (by
      simp [N,Lists.set,tag,blocks_cons,blocks_nil,lastSym,unary,symIs])
    exact ⟨_,_,hs.seqH hh⟩
  | some v => cases v with
    | none =>
      have hsrc : N 2=blocks [0] ++ [1] := by simp [N,Lists.set,tag,blocks_cons,blocks_nil,unary]
      have hm := SequentialCaptureSpliceMachine.moveLast_runs (src := (2 : Fin 8)) (tmp := 1) (by decide)
        (blocks [0]) 1 N hsrc hN (by
          simp [N,blocks_cons,blocks_nil]
          simp [tag,blocks_cons,blocks_nil,unary] at hsize
          omega)
      let M := (N.set 2 (blocks [0])).set 1 (N 1 ++ [1])
      have hM : LenOK B M := end_fits hm
      have hf : Halts (LenOK B) (.ite 2 (symIs 1) (.ite 0 (symIs 1) (.halt false) (.halt true)) (.halt false))
          M false M 2 := (halts_halt hM).iteF hM (by simp [M,N,Lists.set,blocks_cons,blocks_nil,lastSym,unary,symIs])
      have hh : Halts (LenOK B) resultTest N false M (2+2+1) := (hm.seqH hf).iteT hN (by
        rw [hsrc,lastSym_append]; rfl)
      exact ⟨_,_,hs.seqH hh⟩
    | some q =>
      have hsrc : N 2=blocks [1] ++ [1] := by simp [N,Lists.set,tag,blocks_cons,blocks_nil,unary]
      have hm := SequentialCaptureSpliceMachine.moveLast_runs (src := (2 : Fin 8)) (tmp := 1) (by decide)
        (blocks [1]) 1 N hsrc hN (by
          simp [N,blocks_cons,blocks_nil]
          simp [tag,blocks_cons,blocks_nil,unary] at hsize
          omega)
      let M := (N.set 2 (blocks [1])).set 1 (N 1 ++ [1])
      have hM : LenOK B M := end_fits hm
      have hpos : symIs 1 (lastSym (M 0))=decide (0<q) := by
        have h0 : M 0=cursors [q] := by simpa [M,N,Lists.set] using hcur
        rw [h0]
        have he : cursors [q]=blocks [q] := by simp [cursors,blocks,SequentialCursorChain.encode,SequentialCursorChain.deltas]
        rw [he]
        exact SequentialCursorProgressMachine.gap_test q []
      have hf : Halts (LenOK B) (.ite 0 (symIs 1) (.halt false) (.halt true)) M (accept (some (some q))) M 2 := by
        cases q with
        | zero => exact (halts_halt hM).iteF hM (by simpa using hpos)
        | succ q => exact (halts_halt hM).iteT hM (by simpa using hpos)
      have hg : Halts (LenOK B) (.ite 2 (symIs 1) (.ite 0 (symIs 1) (.halt false) (.halt true)) (.halt false))
          M (accept (some (some q))) M 3 := hf.iteT hM (by
            simp [M,N,Lists.set,blocks_cons,blocks_nil,lastSym,unary,symIs])
      have hh : Halts (LenOK B) resultTest N (accept (some (some q))) M (2+3+1) := (hm.seqH hg).iteT hN (by
        rw [hsrc,lastSym_append]; rfl)
      exact ⟨_,_,hs.seqH hh⟩

theorem final_halts (g : MGrammar) (x : List Char) (e : MExp) :
    ∃ M T, Halts (LenOK (SequentialPackedLoopMachine.capacity g e x.length)) program
      (SequentialPackedLoopMachine.state g x e (SequentialPackedLoopMachine.final g x e))
      (accept (SequentialSpanRecompute.run g x e)) M T := by
  let ns := CBVtoCBN.compilerNodes g e
  let c := SequentialPackedLoopMachine.final g x e
  let L := SequentialPackedLoopMachine.state g x e c
  have hL := SequentialPackedLoopMachine.reachable_fits g x e c (SequentialSharedWords.initial_runs g x e)
  apply halt_runs _ L ?_ ?_ rfl hL
  · change SequentialCaptureCopyMachine.withInput (encode ns c) x 2 = _
    rw [SequentialStepDispatchMachine.control_fields,← SequentialStepDispatchMachine.task_fields]
    have he : (writeTask ns c.task).control=[3,tag (SequentialSpanRecompute.run g x e)] := by
      cases hr : SequentialSpanRecompute.run g x e with
      | none => simp [c,SequentialPackedLoopMachine.final,hr,writeTask,tag,SequentialSharedStateCodec.putControl,SequentialSharedStateCodec.Input.append]
      | some v => cases v <;> simp [c,SequentialPackedLoopMachine.final,hr,writeTask,tag,SequentialSharedStateCodec.putControl,SequentialSharedStateCodec.putCursor,SequentialSharedStateCodec.Input.append]
    rw [he]
    change blocks [] ++ blocks [3,tag (SequentialSpanRecompute.run g x e)] ++ blocks [0,0] = _
    rw [blocks_nil,List.nil_append]
    simp only [blocks_cons,blocks_nil,List.nil_append,List.append_assoc]

  · change SequentialCursorEntryMachine.layout (encode ns c) 0 = _
    rw [SequentialCursorEntryMachine.layout_cursors]
    cases hr : SequentialSpanRecompute.run g x e with
    | none => simp [c,SequentialPackedLoopMachine.final,hr,SequentialSharedCursors.positions,SequentialSharedCursors.taskCursor]
    | some v => cases v <;> simp [c,SequentialPackedLoopMachine.final,hr,SequentialSharedCursors.positions,SequentialSharedCursors.taskCursor]

noncomputable def recognize (g : MGrammar) (e : MExp) : LProg 8 := .seq (SequentialPackedInitMachine.initProgram g e)
  (.seq (SequentialPackedLoopMachine.program (CBVtoCBN.compilerNodes g e) g (SequentialStackCode.programBudget g e)) program)

/-- Initialize from the original input characters, evaluate every step, and
halt with the actual full-match decision under one linear workspace bound. -/
theorem recognize_halts (g : MGrammar) (x : List Char) (e : MExp) :
    ∃ M T, Halts (LenOK (SequentialPackedLoopMachine.capacity g e x.length)) (recognize g e)
      (SequentialPackedInitMachine.input (characters x)) (accept (SequentialSpanRecompute.run g x e)) M T := by
  obtain ⟨Ti,hi⟩ := SequentialPackedInitMachine.initialize_runs g x e
  obtain ⟨Tl,hl⟩ := SequentialPackedLoopMachine.evaluate_runs g x e
  obtain ⟨M,Th,hh⟩ := final_halts g x e
  exact ⟨M,_,hi.seqH (hl.seqH hh)⟩

theorem answer_iff {g : MGrammar} (hg : g.FirstOrder) {e : MExp} (he : e.FirstOrder) (x : List Char) :
    accept (SequentialSpanRecompute.run g x e)=true ↔ SObs g .callByValueSeq e x (some []) := by
  rw [accept,decide_eq_true_eq]
  exact SequentialSpanRecompute.run_accepts_iff hg he x

end Shallot.MacroPeg.CBV.SequentialPackedHaltMachine
