import MacroPeg.CBV.FutureCapturePruning

namespace Shallot.MacroPeg.CBV.FutureCaptureExamples
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def words (n : Nat) : List (List Char) := [List.replicate (n+4) 'a',['a'],[]]
def input (n : Nat) : List Char := List.replicate (n+4) 'a'++"!aaa".toList

theorem masked_shape (n : Nat) : FutureCapturePruning.mask 3 (words n)=[[],['a'],[]] := by
  simp [FutureCapturePruning.mask,words]

theorem view_shape (n : Nat) : FutureCapturePruning.views 3 (words n)=
    [MExp.failAlways,.param 1,.param 2] := by
  simp [FutureCapturePruning.views,FutureCapturePruning.selectFrom,words]

/-- Arbitrarily large common-origin words can be removed at the later cut.
The remaining short/empty values and all recursive actuals remain observable. -/
theorem every_body_every_clock (g : MGrammar) (hg : g.FirstOrder) (s : Strategy)
    (hs : s≠.callByName) (k n : Nat) (e : MExp) (he : e.FirstOrder) (p : Nat) (hp : p≤3) :
    evV g (input n) s (tblV g (input n) s k) [[],['a'],[]]
      (MExp.subst [MExp.failAlways,.param 1,.param 2] e) p=
      evV g (input n) s (tblV g (input n) s k) (words n) e p := by
  have hb : 3≤(input n).length := by simp [input]
  simpa only [masked_shape,view_shape] using
    FutureCapturePruning.physical g hg (input n) s hs k 3 hb (words n) e he p hp

def recursive : MGrammar := ⟨[⟨1,.alt (.seq (.param 0) (.call 0 [.param 0])) .eps⟩]⟩
def continuation : MExp := .call 0 [.seq (.notP (.param 0)) (.param 1)]

theorem recursive_actuals_preserved :
    evV recursive (input 0) .callByValuePar (tblV recursive (input 0) .callByValuePar 5) (words 0) continuation 3=some (some 1) ∧
    evV recursive (input 0) .callByValuePar (tblV recursive (input 0) .callByValuePar 5) [[],['a'],[]]
      (MExp.subst [MExp.failAlways,.param 1,.param 2] continuation) 3=some (some 1) ∧
    evV recursive (input 0) .callByValueSeq (tblV recursive (input 0) .callByValueSeq 5) (words 0) continuation 3=some (some 0) ∧
    evV recursive (input 0) .callByValueSeq (tblV recursive (input 0) .callByValueSeq 5) [[],['a'],[]]
      (MExp.subst [MExp.failAlways,.param 1,.param 2] continuation) 3=some (some 0) := by decide +kernel

theorem bare_mask_changes_failure_to_success :
    evV recursive (input 0) .callByValueSeq (tblV recursive (input 0) .callByValueSeq 0) (words 0) (.param 0) 3=some none ∧
    evV recursive (input 0) .callByValueSeq (tblV recursive (input 0) .callByValueSeq 0) [[],['a'],[]] (.param 0) 3=some (some 3) := by decide +kernel

theorem pruning_cannot_be_used_before_the_cut :
    evV recursive (input 0) .callByValuePar (tblV recursive (input 0) .callByValuePar 0) (words 0) (.param 0) (input 0).length=some (some 4) ∧
    evV recursive (input 0) .callByValuePar (tblV recursive (input 0) .callByValuePar 0) [[],['a'],[]]
      (MExp.subst [MExp.failAlways,.param 1,.param 2] (.param 0)) (input 0).length=some none := by decide +kernel

theorem empty_value_must_remain_observable :
    evV recursive (input 0) .callByValuePar (tblV recursive (input 0) .callByValuePar 0) (words 0) (.star (.param 2)) 3=none ∧
    evV recursive (input 0) .callByValuePar (tblV recursive (input 0) .callByValuePar 0) [[],['a'],[]]
      (MExp.subst [MExp.failAlways,.param 1,.param 2] (.star (.param 2))) 3=none ∧
    evV recursive (input 0) .callByValuePar (tblV recursive (input 0) .callByValuePar 0) [] (.star (.param 2)) 3=some (some 3) := by decide +kernel

theorem exact_dead_check_sees_contents :
    FutureCapturePruning.deadCheck "abac".toList 2 [['a','b']]=true ∧
    FutureCapturePruning.deadCheck "abac".toList 2 [['a']]=false ∧
    FutureCapturePruning.deadCheck "abac".toList 2 [[]]=false := by decide +kernel

theorem all_long_values_forgotten (g : MGrammar) (hg : g.FirstOrder) (s : Strategy)
    (hs : s≠.callByName) (k n : Nat) (e : MExp) (he : e.FirstOrder) :
    evV g (input n) s (tblV g (input n) s k) [] e 3=
      evV g (input n) s (tblV g (input n) s k) [List.replicate (n+4) 'a'] e 3 := by
  apply FutureCapturePruning.forget_all g (input n) s _ hs (tblV_sound hg hs k) 3
    (by simp [input]) _ _ e he 3 (Nat.le_refl _)
  intro w hw
  have hw : w=List.replicate (n+4) 'a' := by simpa using hw
  subst w; simp

def rollback : MExp := .alt
  (.seq (.lit "aaaa!".toList) (.seq (.notP (.param 0)) (.chr 'Z'))) (.param 0)

/-- Death inside a branch does not license deleting the old binding from
an enclosing choice frame, which can retry before that branch's cut. -/
theorem outer_backtracking_needs_original_values :
    evV ⟨[]⟩ (input 0) .callByValuePar (tblV ⟨[]⟩ (input 0) .callByValuePar 0) (words 0) rollback (input 0).length=some (some 4) ∧
    evV ⟨[]⟩ (input 0) .callByValuePar (tblV ⟨[]⟩ (input 0) .callByValuePar 0) [[],['a'],[]]
      (MExp.subst [MExp.failAlways,.param 1,.param 2] rollback) (input 0).length=some none := by decide +kernel

end Shallot.MacroPeg.CBV.FutureCaptureExamples
