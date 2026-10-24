import MacroPeg.CBV.SequentialAnyCursorMachine

/-! Streaming replacement of control fields. A fixed number of unary fields
is saved or discarded without constructing a list of decoded integers. -/
namespace Shallot.MacroPeg.CBV.SequentialControlEditMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine

variable {k : Nat}

theorem blocks_append (a b : List Nat) : blocks (a ++ b) = blocks b ++ blocks a := by
  induction a with
  | nil => simp [blocks,bits,SequentialCursorChain.encodeDeltas]
  | cons d ds ih => simp only [List.cons_append,blocks_cons,ih,List.append_assoc]

def moveBlock (src tmp : Fin k) : LProg k := .seq (scan src tmp) (moveTop src tmp)

theorem moveBlock_runs {src tmp : Fin k} (hd : src ≠ tmp) (d : Nat) (rest : List Nat)
    (L : Lists k) {B : Nat} (hsrc : L src = rest ++ [0] ++ unary d) (hL : LenOK B L)
    (hcap : (L tmp).length+d+3 ≤ B) :
    ∃ T, Runs (LenOK B) (moveBlock src tmp) L
      ((L.set src rest).set tmp (L tmp ++ unary d ++ [0])) T := by
  have hs := scan_runs hd d (rest ++ [0]) L hsrc (by simp [lastSym_append,symIs]) hL (by omega)
  let N := (L.set src (rest ++ [0])).set tmp (L tmp ++ unary d)
  have hN : LenOK B N := end_fits hs
  have hc : (N tmp).length+3 ≤ B := by simp [N]; omega
  obtain ⟨hq,hm⟩ := lenOK_moveTop hN hd hc
  have hp := runs_moveTop hd hN hq hm
  have he : N.moveTop src tmp = (L.set src rest).set tmp (L tmp ++ unary d ++ [0]) := by
    funext i
    by_cases hi : i=src <;> by_cases hj : i=tmp <;>
      simp_all [N,Lists.moveTop,Lists.set,List.append_assoc]
  rw [he] at hp
  exact ⟨_,hs.seq hp⟩

def discardHead (src : Fin k) : LProg k := .loop src (symIs 1) (.pop src)

theorem discardHead_runs (src : Fin k) (d : Nat) (S : List Nat) (L : Lists k) {B : Nat}
    (hsrc : L src = S ++ unary d) (hstop : symIs 1 (lastSym S) = false) (hL : LenOK B L) :
    Runs (LenOK B) (discardHead src) L (L.set src S) ((d+1)*2) := by
  induction d generalizing L with
  | zero =>
    have he : L.set src S = L := by
      simp only [List.replicate_zero,List.append_nil] at hsrc
      rw [← hsrc,Lists.set_get_self]
    rw [he]
    exact ⟨1,by omega,.loopF hL (by simpa only [hsrc,List.replicate_zero,List.append_nil] using hstop)⟩
  | succ d ih =>
    have hs : L src = (S ++ unary d) ++ [1] := by
      simpa only [List.replicate_succ',List.append_assoc] using hsrc
    let M := L.set src (S ++ unary d)
    have hM : LenOK B M := by
      apply lenOK_set hL src
      have hh := hL src
      rw [hs] at hh
      simp only [List.length_append,List.length_singleton] at hh ⊢
      omega
    have hepop : L.set src (L src).dropLast = M := by
      rw [hs]
      simp only [List.dropLast_append_cons,List.dropLast_singleton,List.append_nil]
      rfl
    have hp := runs_pop (i := src) hL (by rw [hepop]; exact hM)
    rw [hepop] at hp
    have ht := ih M (by simp [M]) hM
    have he : M.set src S = L.set src S := by simp [M,Lists.set_set_u]
    rw [he] at ht
    obtain ⟨t1,ht1,hx1⟩ := hp
    obtain ⟨t2,ht2,hx2⟩ := ht
    exact ⟨t1+1+t2,by omega,.loopC hL (by simp only [hs,lastSym_append,symIs]; decide) hx1 hx2⟩

def discardBlock (src : Fin k) : LProg k := .seq (discardHead src) (.pop src)

theorem discardBlock_runs (src : Fin k) (d : Nat) (rest : List Nat) (L : Lists k) {B : Nat}
    (hsrc : L src = rest ++ [0] ++ unary d) (hL : LenOK B L) :
    ∃ T, Runs (LenOK B) (discardBlock src) L (L.set src rest) T := by
  have hh := hL src
  rw [hsrc] at hh
  simp only [List.length_append,List.length_cons,List.length_nil,List.length_replicate] at hh
  have hs := discardHead_runs src d (rest ++ [0]) L hsrc (by simp [lastSym_append,symIs]) hL
  let N := L.set src (rest ++ [0])
  have hN : LenOK B N := end_fits hs
  have hp := runs_pop (i := src) hN (by
    apply lenOK_set hN src
    simp [N]
    omega)
  have he : N.set src (N src).dropLast = L.set src rest := by simp [N,Lists.set_set_u]
  rw [he] at hp
  exact ⟨_,hs.seq hp⟩

def saveMany (src tmp : Fin k) : Nat → LProg k
  | 0 => skipP src
  | n+1 => .seq (moveBlock src tmp) (saveMany src tmp n)

def discardMany (src : Fin k) : Nat → LProg k
  | 0 => skipP src
  | n+1 => .seq (discardBlock src) (discardMany src n)

theorem saveMany_runs {src tmp : Fin k} (hd : src ≠ tmp) (fields : List Nat) (rest : List Nat)
    (L : Lists k) {B : Nat} (hsrc : L src = rest ++ blocks fields) (hL : LenOK B L)
    (hcap : (L tmp).length+(blocks fields).length+2 ≤ B) :
    ∃ T, Runs (LenOK B) (saveMany src tmp fields.length) L
      ((L.set src rest).set tmp (L tmp ++ (blocks fields).reverse)) T := by
  induction fields generalizing L with
  | nil =>
    have he : (L.set src rest).set tmp (L tmp ++ (blocks []).reverse) = L := by
      have hs : L src = rest := by simpa [blocks,bits,SequentialCursorChain.encodeDeltas] using hsrc
      simp [blocks,bits,SequentialCursorChain.encodeDeltas,← hs,Lists.set_get_self]
    rw [he]
    exact ⟨1,runs_skip src hL⟩
  | cons d fields ih =>
    have hsz : (blocks (d :: fields)).length = (blocks fields).length+1+d := by
      simp only [blocks_cons,List.length_append,List.length_cons,List.length_nil,List.length_replicate] <;> omega
    have hs : L src = (rest ++ blocks fields) ++ [0] ++ unary d := by
      simpa only [blocks_cons,List.append_assoc] using hsrc
    obtain ⟨T1,hr⟩ := moveBlock_runs hd d (rest ++ blocks fields) L hs hL (by rw [hsz] at hcap; omega)
    let N := (L.set src (rest ++ blocks fields)).set tmp (L tmp ++ unary d ++ [0])
    have hN : LenOK B N := end_fits hr
    have hns : N src = rest ++ blocks fields := by simp [N,Lists.set,hd]
    have hnc : (N tmp).length+(blocks fields).length+2 ≤ B := by
      simp [N]
      rw [hsz] at hcap
      omega
    obtain ⟨T2,ht⟩ := ih N hns hN hnc
    have he : (N.set src rest).set tmp (N tmp ++ (blocks fields).reverse) =
        (L.set src rest).set tmp (L tmp ++ (blocks (d :: fields)).reverse) := by
      funext i
      by_cases hi : i=src <;> by_cases hj : i=tmp <;>
        simp_all [N,Lists.set,blocks_cons,List.reverse_append,List.append_assoc]
    rw [he] at ht
    exact ⟨_,hr.seq ht⟩

theorem discardMany_runs (src : Fin k) (fields : List Nat) (rest : List Nat)
    (L : Lists k) {B : Nat} (hsrc : L src = rest ++ blocks fields) (hL : LenOK B L) :
    ∃ T, Runs (LenOK B) (discardMany src fields.length) L (L.set src rest) T := by
  induction fields generalizing L with
  | nil =>
    have hs : L src = rest := by simpa [blocks,bits,SequentialCursorChain.encodeDeltas] using hsrc
    rw [← hs,Lists.set_get_self]
    exact ⟨1,runs_skip src hL⟩
  | cons d fields ih =>
    have hs : L src = (rest ++ blocks fields) ++ [0] ++ unary d := by
      simpa only [blocks_cons,List.append_assoc] using hsrc
    obtain ⟨T1,hr⟩ := discardBlock_runs src d (rest ++ blocks fields) L hs hL
    let N := L.set src (rest ++ blocks fields)
    have hN : LenOK B N := end_fits hr
    obtain ⟨T2,ht⟩ := ih N (by simp [N]) hN
    have he : N.set src rest = L.set src rest := by simp [N,Lists.set_set_u]
    rw [he] at ht
    exact ⟨_,hr.seq ht⟩

/-- The field counts are fixed by the calling instruction. Field values are
read from the stream, never passed as an integer array to this program. -/
def replace (src tmp : Fin k) (saved erased : Nat) (fresh : List Nat) : LProg k :=
  .seq (saveMany src tmp saved) (.seq (discardMany src erased)
    (.seq (appendP src (blocks fresh)) (moveAll tmp src)))

/-- Capacity covers the initial state and complete replacement. Each partial
copy, discard, append, and restoration also fits, including the saved headers. -/
theorem replace_runs {src tmp : Fin k} (hd : src ≠ tmp) (saved erased fresh : List Nat)
    (rest : List Nat) (L : Lists k) {B : Nat}
    (hsrc : L src = rest ++ blocks erased ++ blocks saved) (htmp : L tmp = [])
    (hL : LenOK B L) (hfinal : (rest ++ blocks fresh ++ blocks saved).length+2 ≤ B) :
    ∃ T, Runs (LenOK B) (replace src tmp saved.length erased.length fresh) L
      (L.set src (rest ++ blocks fresh ++ blocks saved)) T := by
  have hsize := hL src
  rw [hsrc] at hsize
  simp only [List.length_append] at hsize hfinal
  have hcap : (L tmp).length+(blocks saved).length+2 ≤ B := by
    simp only [htmp,List.length_nil]
    omega
  obtain ⟨T1,hs⟩ := saveMany_runs hd saved (rest ++ blocks erased) L hsrc hL hcap
  let N := (L.set src (rest ++ blocks erased)).set tmp ((blocks saved).reverse)
  have heN : (L.set src (rest ++ blocks erased)).set tmp (L tmp ++ (blocks saved).reverse) = N := by
    simp [N,htmp]
  rw [heN] at hs
  have hN := end_fits hs
  have hns : N src = rest ++ blocks erased := by simp [N,Lists.set,hd]
  obtain ⟨T2,he⟩ := discardMany_runs src erased rest N hns hN
  let D := N.set src rest
  have hD : LenOK B D := end_fits he
  have ha := append_runs src (blocks fresh) hD (by simp [D]; omega)
  let M := D.set src (rest ++ blocks fresh)
  have heM : D.set src (D src ++ blocks fresh) = M := by simp [M,D]
  rw [heM] at ha
  have hM : LenOK B M := end_fits ha
  have hrestore : (M src).length+(M tmp).length+2 ≤ B := by
    simp [M,D,N,Lists.set,Ne.symm hd]
    omega
  have hr := moveAll_runs_bounded (Ne.symm hd) hM hrestore
  have hout : (M.set src (M src ++ (M tmp).reverse)).set tmp [] =
      L.set src (rest ++ blocks fresh ++ blocks saved) := by
    funext i
    by_cases hi : i=src <;> by_cases hj : i=tmp <;>
      simp_all [M,D,N,Lists.set,Ne.symm hd,List.append_assoc]
  rw [hout] at hr
  exact ⟨_,hs.seq (he.seq (ha.seq hr))⟩


private theorem bit_symbol (bs : List Bool) (v : Nat) (h : v ∈ bits bs) : v < 2 := by
  simp only [bits,List.mem_reverse,List.mem_map] at h
  obtain ⟨b,hb,rfl⟩ := h
  cases b <;> decide

private theorem append_constOK {E : Nat} (src : Fin k) (vs : List Nat)
    (h : ∀ v ∈ vs, v < E) : (appendP src vs).ConstOK E := by
  induction vs with
  | nil => trivial
  | cons v vs ih => exact ⟨h v List.mem_cons_self,ih (fun w hw => h w (List.mem_cons_of_mem v hw))⟩

private theorem save_constOK (E : Nat) (src tmp : Fin k) (n : Nat) :
    (saveMany src tmp n).ConstOK E := by
  induction n with
  | zero => trivial
  | succ n ih =>
    exact ⟨by simp [moveBlock,scan,moveTop,LProg.ConstOK],ih⟩

private theorem discard_constOK (E : Nat) (src : Fin k) (n : Nat) :
    (discardMany src n).ConstOK E := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨⟨trivial,trivial⟩,ih⟩

/-- Field values do not enlarge the pushed-symbol alphabet: their unary
encoding writes only the two fixed bit symbols. -/
theorem replace_constOK {E : Nat} (hE : 2 ≤ E) (src tmp : Fin k) (saved erased : Nat)
    (fresh : List Nat) : (replace src tmp saved erased fresh).ConstOK E := by
  refine ⟨save_constOK E src tmp saved,discard_constOK E src erased,?_,trivial,trivial⟩
  apply append_constOK
  intro v hv
  exact Nat.lt_of_lt_of_le (bit_symbol _ v hv) hE

private theorem blocks_nil : blocks [] = [] := rfl

/-- Increment the second unary header, retaining the first header on scratch.
No header value is decoded or supplied as a runtime counter. -/
def incrementSecond (src tmp : Fin k) : LProg k :=
  .seq (saveMany src tmp 1) (.seq (.push src 1) (moveAll tmp src))

theorem incrementSecond_runs {src tmp : Fin k} (hd : src ≠ tmp) (first second : Nat)
    (rest : List Nat) (L : Lists k) {B : Nat}
    (hsrc : L src = rest ++ blocks [first,second]) (htmp : L tmp = [])
    (hL : LenOK B L) (hcap : (rest ++ blocks [first,second+1]).length+2 ≤ B) :
    ∃ T, Runs (LenOK B) (incrementSecond src tmp) L
      (L.set src (rest ++ blocks [first,second+1])) T := by
  have hc : (L tmp).length+(blocks [first]).length+2 ≤ B := by
    have hh := hL src
    rw [hsrc] at hh
    simp only [htmp,List.length_nil,blocks_cons,blocks_nil,List.length_append,
      List.length_cons,List.length_nil,List.length_replicate] at hh ⊢
    omega
  have hs : L src = (rest ++ blocks [second]) ++ blocks [first] := by
    rw [show blocks [first,second] = blocks [second] ++ blocks [first] from blocks_append [first] [second]] at hsrc
    simpa only [List.append_assoc] using hsrc
  obtain ⟨T1,hr⟩ := saveMany_runs hd [first] (rest ++ blocks [second]) L hs hL hc
  let N := (L.set src (rest ++ blocks [second])).set tmp ((blocks [first]).reverse)
  have hn : (L.set src (rest ++ blocks [second])).set tmp (L tmp ++ (blocks [first]).reverse) = N := by
    simp [N,htmp]
  rw [hn] at hr
  have hN : LenOK B N := end_fits hr
  have hblock : blocks [second+1] = blocks [second] ++ [1] := by
    simp [blocks_cons,blocks_nil,List.replicate_succ']
  have hM : LenOK B (N.set src (N src ++ [1])) := by
    apply lenOK_set hN src
    have hh := hcap
    simp only [blocks_cons,blocks_nil,List.length_append,List.length_cons,
      List.length_nil,List.length_replicate] at hh
    simp [N,Lists.set,hd]
    simp only [blocks_cons,blocks_nil,List.length_append,List.length_cons,
      List.length_nil,List.length_replicate]
    omega
  have hp := runs_push (i := src) (e := 1) hN hM
  let M := N.set src (N src ++ [1])
  have hrestore : (M src).length+(M tmp).length+2 ≤ B := by
    simp only [M,N,Lists.set_same,Lists.set_ne _ _ hd,Lists.set_ne _ _ (Ne.symm hd),List.length_append,List.length_singleton,List.length_reverse]
    simp only [blocks_cons,blocks_nil,List.length_append,List.length_cons,
      List.length_nil,List.length_replicate] at hcap ⊢
    omega
  have ht := moveAll_runs_bounded (Ne.symm hd) hM hrestore
  have hout : (M.set src (M src ++ (M tmp).reverse)).set tmp [] =
      L.set src (rest ++ blocks [first,second+1]) := by
    have hsplit : blocks [first,second+1] = blocks [second+1] ++ blocks [first] := by
      simpa using blocks_append [first] [second+1]
    rw [hsplit,hblock]
    funext i
    by_cases hi : i=src <;> by_cases hj : i=tmp <;>
      simp [M,N,Lists.set,hi,hj,hd,Ne.symm hd,htmp,List.append_assoc]
  rw [hout] at ht
  exact ⟨_,hr.seq (hp.seq ht)⟩

theorem incrementSecond_constOK {E : Nat} (hE : 2 ≤ E) (src tmp : Fin k) :
    (incrementSecond src tmp).ConstOK E := by
  change (saveMany src tmp 1).ConstOK E ∧ 1 < E ∧ True ∧ True
  exact ⟨save_constOK E src tmp 1,by omega,trivial,trivial⟩

end Shallot.MacroPeg.CBV.SequentialControlEditMachine
