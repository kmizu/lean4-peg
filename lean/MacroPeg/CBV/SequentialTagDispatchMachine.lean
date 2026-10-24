import MacroPeg.CBV.SequentialQueryPackedMachine

/-! Bounded unary-tag dispatch, restoring the complete source before a branch.
The bound and branch programs are fixed code; the tag is read from its tape. -/
namespace Shallot.MacroPeg.CBV.SequentialTagDispatchMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialControlEditMachine
open SequentialCaptureSpliceMachine (moveLast_runs)
variable {k : Nat}

def casesFrom (src tmp : Fin k) (done : Nat) : Nat → (Nat → LProg k) → LProg k
  | 0,next => .seq (moveAll tmp src) (next done)
  | fuel+1,next => .ite src (symIs 1)
      (.seq (moveTop src tmp) (casesFrom src tmp (done+1) fuel next))
      (.seq (moveAll tmp src) (next done))

private def staged (src tmp : Fin k) (L : Lists k) (C P : List Nat) (done tag : Nat) : Lists k :=
  (L.set src (C ++ unary tag)).set tmp (P.reverse ++ unary done)

private theorem cases_runs {src tmp : Fin k} (hd : src ≠ tmp) (fuel : Nat)
    (done tag : Nat) (htag : tag ≤ fuel) (C P : List Nat) (next : Nat → LProg k)
    (L M : Lists k) {B T : Nat} (hsrc : L src = C ++ unary (done+tag) ++ P)
    (hstop : symIs 1 (lastSym C)=false) (htmp : L tmp = []) (hL : LenOK B L)
    (hp : Runs (LenOK B) (next (done+tag)) L M T) :
    ∃ U, Runs (LenOK B) (casesFrom src tmp done fuel next)
      (staged src tmp L C P done tag) M U := by
  have hh := hL src
  rw [hsrc] at hh
  simp only [List.length_append,List.length_replicate] at hh
  have hN : LenOK B (staged src tmp L C P done tag) := by
    apply lenOK_set (lenOK_set hL src (by simp; omega)) tmp
    simp
    omega
  induction fuel generalizing done tag with
  | zero =>
    have hz : tag=0 := by omega
    subst tag
    have hc : ((staged src tmp L C P done 0) src).length+
        ((staged src tmp L C P done 0) tmp).length+2 ≤ B := by
      simp [staged,Lists.set,hd]
      omega
    have hr := moveAll_runs_bounded (Ne.symm hd) hN hc
    have he : (((staged src tmp L C P done 0).set src
        ((staged src tmp L C P done 0) src ++ ((staged src tmp L C P done 0) tmp).reverse)).set tmp []) = L := by
      funext j
      by_cases hs : j=src <;> by_cases ht : j=tmp <;>
        simp_all [staged,Lists.set,List.reverse_append,List.append_assoc]
    rw [he] at hr
    exact ⟨_,hr.seq (by simpa using hp)⟩
  | succ fuel ih =>
    cases tag with
    | zero =>
      have hc : ((staged src tmp L C P done 0) src).length+
          ((staged src tmp L C P done 0) tmp).length+2 ≤ B := by
        simp [staged,Lists.set,hd]
        omega
      have hr := moveAll_runs_bounded (Ne.symm hd) hN hc
      have he : (((staged src tmp L C P done 0).set src
          ((staged src tmp L C P done 0) src ++ ((staged src tmp L C P done 0) tmp).reverse)).set tmp []) = L := by
        funext j
        by_cases hs : j=src <;> by_cases ht : j=tmp <;>
          simp_all [staged,Lists.set,List.reverse_append,List.append_assoc]
      rw [he] at hr
      have hcnd : symIs 1 (lastSym ((staged src tmp L C P done 0) src)) = false := by
        simpa [staged,Lists.set,hd] using hstop
      exact ⟨_,(hr.seq (by simpa using hp)).iteF hN hcnd⟩
    | succ tag =>
      let N := staged src tmp L C P done (tag+1)
      have hs : N src = (C ++ unary tag) ++ [1] := by
        simp [N,staged,Lists.set,hd,List.replicate_succ',List.append_assoc]
      have hc : (N tmp).length+3 ≤ B := by simp [N,staged]; omega
      have hr := moveLast_runs hd (C ++ unary tag) 1 N hs hN hc
      have he : (N.set src (C ++ unary tag)).set tmp (N tmp ++ [1]) =
          staged src tmp L C P (done+1) tag := by
        funext j
        by_cases hjs : j=src <;> by_cases hjt : j=tmp <;>
          simp_all [N,staged,Lists.set,List.replicate_succ',List.append_assoc]
      rw [he] at hr
      have hsum : done+(tag+1) = (done+1)+tag := by omega
      have hsrc' : L src = C ++ unary ((done+1)+tag) ++ P := by rwa [← hsum]
      have hp' : Runs (LenOK B) (next ((done+1)+tag)) L M T := by rwa [← hsum]
      obtain ⟨U,hu⟩ := ih (done+1) tag (by omega) hsrc' hp' (by omega) (end_fits hr)
      have hcnd : symIs 1 (lastSym (N src)) = true := by rw [hs,lastSym_append]; rfl
      exact ⟨_,(hr.seq hu).iteT hN hcnd⟩

def program (src tmp : Fin k) (saved maxTag : Nat) (next : Nat → LProg k) : LProg k :=
  .seq (saveMany src tmp saved) (casesFrom src tmp 0 maxTag next)

theorem dispatch_runs {src tmp : Fin k} (hd : src ≠ tmp) (saved : List Nat)
    (maxTag tag : Nat) (htag : tag ≤ maxTag) (C : List Nat) (next : Nat → LProg k)
    (L M : Lists k) {B T : Nat} (hsrc : L src = C ++ unary tag ++ blocks saved)
    (hstop : symIs 1 (lastSym C)=false) (htmp : L tmp = []) (hL : LenOK B L)
    (hp : Runs (LenOK B) (next tag) L M T) :
    ∃ U, Runs (LenOK B) (program src tmp saved.length maxTag next) L M U := by
  have hh := hL src
  rw [hsrc] at hh
  simp only [List.length_append,List.length_replicate] at hh
  obtain ⟨Ts,hs⟩ := saveMany_runs hd saved (C ++ unary tag) L hsrc hL
    (by simp only [htmp,List.length_nil]; omega)
  obtain ⟨U,hu⟩ := cases_runs hd maxTag 0 tag htag C (blocks saved) next L M
    (by simpa using hsrc) hstop htmp hL (by simpa using hp)
  have he : (L.set src (C ++ unary tag)).set tmp (L tmp ++ (blocks saved).reverse) =
      staged src tmp L C (blocks saved) 0 tag := by simp [staged,htmp]
  rw [he] at hs
  exact ⟨_,hs.seq hu⟩

theorem constOK (E : Nat) (src tmp : Fin k) (saved maxTag : Nat) (next : Nat → LProg k)
    (hn : ∀ tag, (next tag).ConstOK E) : (program src tmp saved maxTag next).ConstOK E := by
  have hs : (saveMany src tmp saved).ConstOK E := by
    induction saved with
    | zero => trivial
    | succ n ih => exact ⟨by simp [moveBlock,scan,moveTop,LProg.ConstOK],ih⟩
  have hc (fuel done : Nat) : (casesFrom src tmp done fuel next).ConstOK E := by
    induction fuel generalizing done with
    | zero => simp [casesFrom,moveAll,moveTop,LProg.ConstOK,hn]
    | succ n ih => simp [casesFrom,moveTop,moveAll,LProg.ConstOK,hn,ih]
  exact ⟨hs,hc maxTag 0⟩

end Shallot.MacroPeg.CBV.SequentialTagDispatchMachine
