import MacroPeg.CBV.SequentialRecursiveScanner
import MacroPeg.CBV.SequentialRecursiveObserverExamples

namespace Shallot.MacroPeg.CBV.SequentialRecursiveScannerExamples
open SequentialRecursiveObserver (render source)
open SequentialRecursiveScanner
open StatefulScannerProduct (left right)
abbrev bodies := SequentialRecursiveObserverExamples.bodies
abbrev inner := SequentialRecursiveObserverExamples.inner
abbrev input := SequentialRecursiveObserverExamples.input
abbrev w := SequentialRecursiveObserverExamples.w

def M : StatefulScanner.Machine 2 := ⟨fun q =>
  [('a',q),('b',⟨1-q.val,by omega⟩),('c',q),('!',q)]⟩
def g := grammar M bodies []
def K (t : Fin (2*(D M).width)) : MExp :=
  if (left (valid M).1 t).val=0 ∧ (right (valid M).1 t).val=1 then
    .seq (.lit ['?']) (.param 0) else MExp.failAlways

theorem checked : ParameterizedCaptureSafety.grammarCheck M (source bodies)=true ∧
    ParameterizedCaptureSafety.check M (source bodies).rules.length (render inner)=true ∧
    TotalCaptureSafety.Environment M [['a']] := by
  refine ⟨by decide +kernel,by decide +kernel,?_⟩
  intro v hv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
  subst v
  intro q
  simp [StatefulScanner.advance,M,StatefulScanner.next,Shallot.beqChar]

theorem capture_states :
    DynamicScannerBinding.resume (CaptureTransitionProfile.profile (D M) w) (0 : Fin 2)=some 1 ∧
    (state M (CaptureTransitionProfile.profile (D M) w) (1 : Fin 3)).val=0 := by decide +kernel

/-- Actual recursive argument evaluation is unchanged by installing both
its recursive observer products and the relocated observed scanner blocks. -/
theorem inner_actual (clock : Nat) (hclock : 4≤clock) :
    evV g input .callByValueSeq (tblV g input .callByValueSeq clock) [['a']] (render inner) input.length=
      some (some (input.length-w.length)) := by
  have hs := evV_lift hclock SequentialRecursiveObserverExamples.source_parent_return.1
  exact (SequentialRecursiveObserver.ambient_original_eval (D M) bodies g (installed M bodies [])
    SequentialRecursiveObserverExamples.checked.1 input clock inner SequentialRecursiveObserverExamples.checked.2.1
    [['a']] input.length (Nat.le_refl _)).symm.trans hs

/-- The shared scanner consumes w!w, then the original parent's a is reused.
The generated capture-first expression reaches the same actual acceptance. -/
theorem physical_fusion :
    evV g input .callByValueSeq (tblV g input .callByValueSeq (input.length+1)) [['a']]
      (origin M bodies inner (0 : Fin 2) (1 : Fin 3) K) input.length=some (some 0) ∧
    evV g input .callByValueSeq (tblV g input .callByValueSeq (input.length+1)) [['a']]
      (fused M bodies [[0,1,2]] inner (0 : Fin 2) (1 : Fin 3) K) input.length=some (some 0) := by
  have hi := inner_actual (input.length+1) (by decide +kernel)
  have ho : evV g input .callByValueSeq (tblV g input .callByValueSeq (input.length+1)) [['a']]
      (origin M bodies inner (0 : Fin 2) (1 : Fin 3) K) input.length=some (some 0) := by
    have hd := ObservedScannerDispatch.dispatch_result M (D M) (valid M) (before M bodies) []
      (0 : Fin 2) (1 : Fin 3) K input .callByValueSeq [['a']] input.length (input.length+1) (Nat.le_refl _) (Nat.le_refl _)
    have hor : evV g input .callByValueSeq (tblV g input .callByValueSeq (input.length+1)) [['a']]
        (origin M bodies inner (0 : Fin 2) (1 : Fin 3) K) input.length=
        evV g input .callByValueSeq (tblV g input .callByValueSeq (input.length+1)) [['a']]
          (ObservedScannerDispatch.dispatch (before M bodies).length (0 : Fin 2) (1 : Fin 3) K) input.length := by
      simp only [origin,MExp.andP,evV,hi]
    exact hor.trans (hd.trans (by decide +kernel))
  refine ⟨ho,?_⟩
  have hf := fusion_correct M bodies [] (by intro r hr; cases hr)
    SequentialRecursiveObserverExamples.checked.1 checked.1 inner SequentialRecursiveObserverExamples.checked.2.1
    checked.2.1 input (input.length+1) [['a']] checked.2.2 input.length (Nat.le_refl _) (Nat.le_refl _)
    (0 : Fin 2) (1 : Fin 3) K
  exact hf.trans ho

/-- Nullable divergence happens before scanning, on every input and clock
where the scanner blocks are available; it remains undefined after fusion. -/
theorem nullable_before_scan (x : List Char) (clock : Nat) (E : List (List Char))
    (hE : TotalCaptureSafety.Environment M E) (p : Nat) (hp : p≤x.length) (hclock : p+1≤clock) :
    evV g x .callByValueSeq (tblV g x .callByValueSeq clock) E
      (fused M bodies (E.map (CaptureTransitionProfile.profile (D M)))
        SequentialRecursiveObserverExamples.loopArgument (0 : Fin 2) (1 : Fin 3) K) p=none := by
  refine (fusion_correct M bodies [] (by intro r hr; cases hr) SequentialRecursiveObserverExamples.checked.1 checked.1
    SequentialRecursiveObserverExamples.loopArgument (by decide +kernel) (by decide +kernel) x clock E hE p hp hclock
    (0 : Fin 2) (1 : Fin 3) K).trans ?_
  change evV g x .callByValueSeq (tblV g x .callByValueSeq clock) E
    (origin M bodies SequentialRecursiveObserverExamples.loopArgument (0 : Fin 2) (1 : Fin 3) K) p=none
  have hs : evV (source bodies) x .callByValueSeq (tblV (source bodies) x .callByValueSeq clock) E
      (render SequentialRecursiveObserverExamples.loopArgument) p=none := by
    have he : evV (source bodies) x .callByValueSeq (tblV (source bodies) x .callByValueSeq clock) E (.star (.lit [])) p=none := by
      exact evStar_stuck (show evV (source bodies) x .callByValueSeq (tblV (source bodies) x .callByValueSeq clock) E (.lit []) p=some (some p) from by
        simp [evV,Shallot.stripPrefix?,length_sfx x hp]) (Nat.not_lt.mpr (Nat.le_refl _))
    rw [show render SequentialRecursiveObserverExamples.loopArgument=.call 0 [.star (.lit [])] from rfl,
      evV_call_seq (SequentialRecursiveObserver.source_rule bodies 0 bodies[0] (by rfl)) rfl]
    simp only [evSeqArgs,he]
  have hi := (SequentialRecursiveObserver.ambient_original_eval (D M) bodies g (installed M bodies [])
    SequentialRecursiveObserverExamples.checked.1 x clock _ (by decide +kernel) E p hp).symm.trans hs
  simp only [origin,MExp.andP,evV,hi]

end Shallot.MacroPeg.CBV.SequentialRecursiveScannerExamples
