import MacroPeg.CBV.SequentialEntryPackedMachine

/-! Streaming header decrement and dispatch on a saved expression-result tag.
The dispatcher restores its source before entering the selected continuation. -/
namespace Shallot.MacroPeg.CBV.SequentialReturnControlMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialControlEditMachine
variable {k : Nat}

private theorem blocks_nil : blocks [] = [] := rfl

def decrementSecond (src tmp : Fin k) : LProg k :=
  .seq (saveMany src tmp 1) (.seq (.pop src) (moveAll tmp src))

theorem decrementSecond_runs {src tmp : Fin k} (hd : src ≠ tmp) (first second : Nat)
    (rest : List Nat) (L : Lists k) {B : Nat}
    (hsrc : L src = rest ++ blocks [first,second+1]) (htmp : L tmp = []) (hL : LenOK B L) :
    ∃ T, Runs (LenOK B) (decrementSecond src tmp) L
      (L.set src (rest ++ blocks [first,second])) T := by
  have hh := hL src
  rw [hsrc] at hh
  have hc : (L tmp).length+(blocks [first]).length+2 ≤ B := by
    simp only [htmp,List.length_nil,blocks_cons,blocks_nil,List.length_append,
      List.length_cons,List.length_nil,List.length_replicate] at hh ⊢
    omega
  have hsplit : blocks [first,second+1] = blocks [second+1] ++ blocks [first] :=
    blocks_append [first] [second+1]
  have hs : L src = (rest ++ blocks [second+1]) ++ blocks [first] := by
    simpa only [hsplit,List.append_assoc] using hsrc
  obtain ⟨T1,hr⟩ := saveMany_runs hd [first] (rest ++ blocks [second+1]) L hs hL hc
  let N := (L.set src (rest ++ blocks [second+1])).set tmp ((blocks [first]).reverse)
  have hn : (L.set src (rest ++ blocks [second+1])).set tmp (L tmp ++ (blocks [first]).reverse) = N := by
    simp [N,htmp]
  rw [hn] at hr
  have hN : LenOK B N := end_fits hr
  have hblock : blocks [second+1] = blocks [second] ++ [1] := by
    simp [blocks_cons,blocks_nil,List.replicate_succ']
  let M := N.set src (rest ++ blocks [second])
  have hM : LenOK B M := by
    apply lenOK_set hN src
    have hsize := hN src
    simp only [N,Lists.set_ne _ _ hd,Lists.set_same,hblock,List.length_append,
      List.length_singleton] at hsize
    simp only [List.length_append]
    omega
  have hepop : N.set src (N src).dropLast = M := by simp [M,N,Lists.set,hd,hblock]
  have hp := runs_pop (i := src) hN (by rw [hepop]; exact hM)
  rw [hepop] at hp
  have hrestore : (M src).length+(M tmp).length+2 ≤ B := by
    simp only [M,N,Lists.set_same,Lists.set_ne _ _ (Ne.symm hd),
      List.length_append,List.length_reverse]
    simp only [hsplit,List.length_append,hblock,List.length_singleton] at hh
    omega
  have ht := moveAll_runs_bounded (Ne.symm hd) hM hrestore
  have hout : (M.set src (M src ++ (M tmp).reverse)).set tmp [] =
      L.set src (rest ++ blocks [first,second]) := by
    rw [show blocks [first,second] = blocks [second] ++ blocks [first] from blocks_append [first] [second]]
    funext i
    by_cases hi : i=src <;> by_cases hj : i=tmp <;>
      simp [M,N,Lists.set,hi,hj,hd,Ne.symm hd,htmp,List.append_assoc]
  rw [hout] at ht
  exact ⟨_,hr.seq (hp.seq ht)⟩

theorem decrementSecond_constOK (E : Nat) (src tmp : Fin k) :
    (decrementSecond src tmp).ConstOK E := by
  simp [decrementSecond,saveMany,moveBlock,scan,moveTop,moveAll,skipP,LProg.ConstOK]

def select (tag : Nat) (p0 p1 p2 : LProg k) : LProg k :=
  if tag=0 then p0 else if tag=1 then p1 else p2

def dispatch (src tmp : Fin k) (saved : Nat) (p0 p1 p2 : LProg k) : LProg k :=
  .seq (saveMany src tmp saved) (.ite src (symIs 1)
    (.seq (moveTop src tmp) (.ite src (symIs 1)
      (.seq (moveAll tmp src) p2) (.seq (moveAll tmp src) p1)))
    (.seq (moveAll tmp src) p0))

/-- Undo a partial prefix transfer, restoring both original tapes. -/
private theorem restore_prefix {src tmp : Fin k} (hd : src ≠ tmp) (S P : List Nat)
    (L : Lists k) {B : Nat} (hsrc : L src = S ++ P) (htmp : L tmp = []) (hL : LenOK B L)
    (hN : LenOK B ((L.set src S).set tmp P.reverse)) :
    ∃ T, Runs (LenOK B) (moveAll tmp src) ((L.set src S).set tmp P.reverse) L T := by
  let N := (L.set src S).set tmp P.reverse
  have hh := hL src
  rw [hsrc] at hh
  have hc : (N src).length+(N tmp).length+2 ≤ B := by
    simpa [N,Lists.set,hd] using hh
  have hr := moveAll_runs_bounded (Ne.symm hd) hN hc
  have he : (N.set src (N src ++ (N tmp).reverse)).set tmp [] = L := by
    funext i
    by_cases hi : i=src <;> by_cases hj : i=tmp <;>
      simp_all [N,Lists.set]
  rw [he] at hr
  exact ⟨_,hr⟩

/-- Dispatch reads tag 0/1/2 directly from the stream after saving a fixed
number of headers. The branch starts with exactly the original configuration. -/
theorem dispatch_runs {src tmp : Fin k} (hd : src ≠ tmp) (saved : List Nat)
    (tag : Nat) (htag : tag ≤ 2) (rest : List Nat) (p0 p1 p2 : LProg k)
    (L M : Lists k) {B T : Nat}
    (hsrc : L src = rest ++ blocks [tag] ++ blocks saved) (htmp : L tmp = [])
    (hL : LenOK B L) (hp : Runs (LenOK B) (select tag p0 p1 p2) L M T) :
    ∃ U, Runs (LenOK B) (dispatch src tmp saved.length p0 p1 p2) L M U := by
  have hh := hL src
  rw [hsrc] at hh
  have hc : (L tmp).length+(blocks saved).length+2 ≤ B := by
    simp only [htmp,List.length_nil,List.length_append] at hh ⊢
    omega
  obtain ⟨Ts,hs⟩ := saveMany_runs hd saved (rest ++ blocks [tag]) L hsrc hL hc
  let N := (L.set src (rest ++ blocks [tag])).set tmp ((blocks saved).reverse)
  have hn : (L.set src (rest ++ blocks [tag])).set tmp (L tmp ++ (blocks saved).reverse) = N := by
    simp [N,htmp]
  rw [hn] at hs
  have hN : LenOK B N := end_fits hs
  by_cases hz : tag=0
  · subst tag
    obtain ⟨Tr,hr⟩ := restore_prefix hd (rest ++ blocks [0]) (blocks saved) L hsrc htmp hL hN
    have hcond : symIs 1 (lastSym (N src)) = false := by
      simp [N,Lists.set,hd,blocks_cons,blocks_nil,lastSym_append,symIs]
    have hbranch : Runs (LenOK B) p0 L M T := by simpa [select] using hp
    exact ⟨_,hs.seq ((hr.seq hbranch).iteF hN hcond)⟩
  · have hpos : 0 < tag := by omega
    have ht : ∃ d, tag=d+1 := ⟨tag-1,by omega⟩
    obtain ⟨d,rfl⟩ := ht
    have hblock : blocks [d+1] = blocks [d] ++ [1] := by
      simp [blocks_cons,blocks_nil,List.replicate_succ']
    have hcond : symIs 1 (lastSym (N src)) = true := by
      simp [N,Lists.set,hd,hblock,← List.append_assoc,lastSym_append,symIs]
    have hcap : (N tmp).length+3 ≤ B := by
      simp [N]
      simp only [List.length_append,blocks_cons,blocks_nil,List.length_cons,
        List.length_nil,List.length_replicate] at hh ⊢
      omega
    obtain ⟨hq,hD⟩ := lenOK_moveTop hN hd hcap
    have hm := runs_moveTop hd hN hq hD
    let D := (L.set src (rest ++ blocks [d])).set tmp ((blocks saved).reverse ++ [1])
    have heD : N.moveTop src tmp = D := by
      funext i
      by_cases hi : i=src <;> by_cases hj : i=tmp <;>
        simp_all [N,D,Lists.moveTop,Lists.set,List.append_assoc]
    rw [heD] at hm hD
    have hprefix : L src = (rest ++ blocks [d]) ++ ([1] ++ blocks saved) := by
      simpa only [hblock,List.append_assoc] using hsrc
    have hde : (L.set src (rest ++ blocks [d])).set tmp ([1] ++ blocks saved).reverse = D := by
      simp [D]
    have hdf : LenOK B ((L.set src (rest ++ blocks [d])).set tmp ([1] ++ blocks saved).reverse) := by
      rw [hde]; exact hD
    obtain ⟨Tr,hr⟩ := restore_prefix hd (rest ++ blocks [d]) ([1] ++ blocks saved) L hprefix htmp hL hdf
    rw [hde] at hr
    have hd01 : d=0 ∨ d=1 := by omega
    rcases hd01 with rfl | rfl
    · have htest : symIs 1 (lastSym (D src)) = false := by
        simp [D,Lists.set,hd,blocks_cons,blocks_nil,lastSym_append,symIs]
      have hbranch : Runs (LenOK B) p1 L M T := by simpa [select] using hp
      exact ⟨_,hs.seq ((hm.seq ((hr.seq hbranch).iteF hD htest)).iteT hN hcond)⟩
    · have htest : symIs 1 (lastSym (D src)) = true := by
        simp only [D,Lists.set_ne _ _ hd,Lists.set_same]
        change symIs 1 (lastSym (rest ++ [0,1])) = true
        rw [show rest ++ [0,1] = (rest ++ [0]) ++ [1] by simp]
        rw [lastSym_append]
        rfl
      have hbranch : Runs (LenOK B) p2 L M T := by simpa [select] using hp
      exact ⟨_,hs.seq ((hm.seq ((hr.seq hbranch).iteT hD htest)).iteT hN hcond)⟩

theorem dispatch_constOK (E : Nat) (src tmp : Fin k) (saved : Nat) (p0 p1 p2 : LProg k)
    (h0 : p0.ConstOK E) (h1 : p1.ConstOK E) (h2 : p2.ConstOK E) :
    (dispatch src tmp saved p0 p1 p2).ConstOK E := by
  have hs : (saveMany src tmp saved).ConstOK E := by
    induction saved with
    | zero => trivial
    | succ n ih => exact ⟨by simp [moveBlock,scan,moveTop,LProg.ConstOK],ih⟩
  simp [dispatch,LProg.ConstOK,moveTop,moveAll,hs,h0,h1,h2]

end Shallot.MacroPeg.CBV.SequentialReturnControlMachine
