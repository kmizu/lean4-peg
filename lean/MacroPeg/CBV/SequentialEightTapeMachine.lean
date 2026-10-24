import MacroPeg.CBV.SequentialStaticPackedMachine
import Complexity.ListRename

/-! Put the existing six-tape subroutines on the common eight-tape layout,
preserving the original-input tape and the additional word scratch tape. -/
namespace Shallot.MacroPeg.CBV.SequentialEightTapeMachine
open Complexity SequentialCursorEditMachine
open SequentialSharedWords (CaptureEnv Runs initial)
open SequentialSharedStateCodec (Packed encode)
open SequentialCaptureCopyMachine (withInput)
open SequentialCursorEntryMachine (layout)

def registers (i : Fin 6) : Fin 8 := ⟨i.val,by omega⟩

theorem registers_injective : Function.Injective registers := by
  intro a b he
  have hv := congrArg (fun j : Fin 8 => j.val) he
  exact Fin.ext hv

def program (p : LProg 6) : LProg 8 := p.rename registers

private theorem weaken {k : Nat} {P Q : Lists k → Prop} (hPQ : ∀ L, P L → Q L)
    {p : LProg k} {L : Lists k} {t : Nat} {o : LOutcome k} (h : LExec P p L t o) : LExec Q p L t o := by
  induction h with
  | push h1 h2 => exact .push (hPQ _ h1) (hPQ _ h2)
  | pop h1 h2 => exact .pop (hPQ _ h1) (hPQ _ h2)
  | copy hd h1 h2 => exact .copy hd (hPQ _ h1) (hPQ _ h2)
  | halt h1 => exact .halt (hPQ _ h1)
  | seqC _ _ ih1 ih2 => exact .seqC ih1 ih2
  | seqS _ ih => exact .seqS ih
  | iteT h1 h2 _ ih => exact .iteT (hPQ _ h1) h2 ih
  | iteF h1 h2 _ ih => exact .iteF (hPQ _ h1) h2 ih
  | loopF h1 h2 => exact .loopF (hPQ _ h1) h2
  | loopC h1 h2 _ _ ih1 ih2 => exact .loopC (hPQ _ h1) h2 ih1 ih2
  | loopS h1 h2 _ ih => exact .loopS (hPQ _ h1) h2 ih

private theorem framed (a b : Packed) (x : List Char) :
    (layout b).frame registers (withInput a x)=withInput b x := by
  funext j
  by_cases hj : j.val<6
  · let i : Fin 6 := ⟨j.val,hj⟩
    have he : registers i=j := Fin.ext rfl
    rw [← he,Lists.frame_get registers_injective]
    simp only [withInput,registers,dif_pos i.isLt]
  · rw [Lists.frame_outside]
    · simp [withInput,hj]
    · intro ⟨i,hi⟩
      have hv := congrArg Fin.val hi
      simp only [registers] at hv
      omega

theorem lift_runs {B C T : Nat} (hBC : B ≤ C) (a b : Packed) (x : List Char) (p : LProg 6)
    (hL : LenOK C (withInput a x)) (h : Complexity.Runs (LenOK B) p (layout a) (layout b) T) :
    Complexity.Runs (LenOK C) (program p) (withInput a x) (withInput b x) T := by
  obtain ⟨t,ht,hx⟩ := h
  have hw := weaken (fun _ hh j => Nat.le_trans (hh j) hBC) hx
  have hr := hw.rename_frame registers_injective (withInput a x) hL
  refine ⟨t,ht,?_⟩
  simpa only [program,LOutcome.frame,framed] using hr

/-- The four cursor-saving structural entries now have the same eight-tape
interface as actual parameter, query, call, and capture-return instructions. -/
theorem entry_runs (g : MGrammar) (x : List Char) (e : MExp) (entry : SequentialCursorEntryMachine.Entry)
    (m : Nat) (E : CaptureEnv) (p : Nat) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (SequentialCursorEntryMachine.before entry m E p K)) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (program (SequentialEntryPackedMachine.program (CBVtoCBN.compilerNodes g e) entry))
      (withInput (encode (CBVtoCBN.compilerNodes g e) (SequentialCursorEntryMachine.before entry m E p K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (SequentialCursorEntryMachine.after entry m E p K)) x) T := by
  obtain ⟨T,hr⟩ := SequentialEntryPackedMachine.transition_runs g x e entry m E p K h
  have hb := SequentialSharedStateBound.encoded_state_linear g x e _ h
  refine ⟨T,lift_runs (by rw [Nat.add_mul,Nat.one_mul]; omega) _ _ x _ ?_ hr⟩
  apply SequentialCaptureCopyMachine.withInput_fits
  · rw [Nat.add_mul,Nat.one_mul]; omega
  · rw [Nat.add_mul,Nat.one_mul]; omega

theorem return_runs (g : MGrammar) (x : List Char) (e : MExp) (ret : SequentialReturnPackedMachine.Return)
    (m : Nat) (E : CaptureEnv) (p : Nat) (r : Res) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (SequentialReturnPackedMachine.before ret m E p r K)) :
    ∃ T, Complexity.Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      (program (SequentialReturnPackedMachine.program (CBVtoCBN.compilerNodes g e) ret))
      (withInput (encode (CBVtoCBN.compilerNodes g e) (SequentialReturnPackedMachine.before ret m E p r K)) x)
      (withInput (encode (CBVtoCBN.compilerNodes g e) (SequentialReturnPackedMachine.after ret m E p r K)) x) T := by
  obtain ⟨T,hr⟩ := SequentialReturnPackedMachine.transition_runs g x e ret m E p r K h
  have hb := SequentialSharedStateBound.encoded_state_linear g x e _ h
  refine ⟨T,lift_runs (by rw [Nat.add_mul,Nat.one_mul]; omega) _ _ x _ ?_ hr⟩
  apply SequentialCaptureCopyMachine.withInput_fits
  · rw [Nat.add_mul,Nat.one_mul]; omega
  · rw [Nat.add_mul,Nat.one_mul]; omega

theorem constOK (p : LProg 6) (E : Nat) (hp : p.ConstOK E) : (program p).ConstOK E := by
  induction p <;> simp_all [program,LProg.rename,LProg.ConstOK]

end Shallot.MacroPeg.CBV.SequentialEightTapeMachine
