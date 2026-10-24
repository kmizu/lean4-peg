import MacroPeg.CBV.SequentialCountGuardMachine

/-! Select the actual parameter word using a source-fixed index, guard the
runtime environment length, match against the original input, and restore
all words. The only temporary output is a success bit on the control tape. -/
namespace Shallot.MacroPeg.CBV.SequentialParamMatchMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine
open SequentialCaptureCopyMachine (characters wordCode wordTape)
open SequentialSharedWords (CaptureEnv)

def skipWords : Nat → LProg 8
  | 0 => skipP 4
  | k+1 => .seq (SequentialCaptureSpliceMachine.moveWord 4 7) (skipWords k)

theorem skipWords_runs (D : CaptureEnv) (tail : List Nat) (L : Lists 8) {B : Nat}
    (hw : L 4=tail ++ wordTape D) (hL : LenOK B L)
    (hcap : (L 7).length+(wordTape D).length+2 ≤ B) :
    ∃ T, Runs (LenOK B) (skipWords D.length) L
      ((L.set 4 tail).set 7 (L 7 ++ (wordTape D).reverse)) T := by
  induction D generalizing tail L with
  | nil =>
    have hn : wordTape []=[] := rfl
    simp only [hn,List.reverse_nil,List.append_nil] at hw ⊢
    have he : (L.set 4 tail).set 7 (L 7) = L := by rw [← hw,Lists.set_get_self,Lists.set_get_self]
    rw [he]
    exact ⟨1,runs_skip 4 hL⟩
  | cons w D ih =>
    have hw' : L 4=(tail ++ wordTape D) ++ wordCode w := by
      simpa only [SequentialCaptureSpliceMachine.wordTape_cons,List.append_assoc] using hw
    obtain ⟨Tm,hm⟩ := SequentialCaptureSpliceMachine.moveWord_runs
      (src := (4 : Fin 8)) (tmp := 7) (by decide) w (tail ++ wordTape D) L hw' hL (by
        simp only [SequentialCaptureSpliceMachine.wordTape_cons,List.length_append,wordCode,
          characters,List.length_reverse,List.length_map,List.length_singleton] at hcap
        omega)
    let N := (L.set 4 (tail ++ wordTape D)).set 7 (L 7 ++ characters w ++ [0])
    obtain ⟨Ti,hi⟩ := ih tail N rfl (end_fits hm) (by
      simp only [SequentialCaptureSpliceMachine.wordTape_cons,List.length_append,wordCode,
        characters,List.length_reverse,List.length_map,List.length_singleton] at hcap
      simpa [N,Lists.set,characters,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hcap)
    have he : (N.set 4 tail).set 7 (N 7 ++ (wordTape D).reverse) =
        (L.set 4 tail).set 7 (L 7 ++ (wordTape (w :: D)).reverse) := by
      funext j
      by_cases h4 : j=4 <;> by_cases h7 : j=7 <;>
        simp [N,Lists.set,h4,h7,SequentialCaptureSpliceMachine.wordTape_cons,wordCode,
          List.reverse_append,List.append_assoc]
    rw [he] at hi
    exact ⟨_,hm.seq hi⟩

def present (k : Nat) : LProg 8 := .seq (skipWords k)
  (.seq (.push 2 1) SequentialWordInputMachine.program)
def missing : LProg 8 := .seq (dropBlock 0 1) (.push 2 0)
def program (k : Nat) : LProg 8 := SequentialCountGuardMachine.program (present k) missing (k+1)

def result (L : Lists 8) (ps : List Nat) (r : Option (List Char)) : Lists 8 :=
  (L.set 2 (L 2 ++ [if r.isSome then 1 else 0])).set 0 (cursors ((r.map List.length).toList ++ ps))

theorem present_runs (D R : CaptureEnv) (w x : List Char) (p : Nat) (ps : List Nat)
    (hchain : SequentialCursorChain.Chain p ps x.length) (hp : p ≤ x.length)
    (tail : List Nat) (L : Lists 8) {B : Nat}
    (hcur : L 0=cursors (p :: ps)) (hw : L 4=tail ++ wordTape (D ++ w :: R))
    (hx : L 6=characters x) (h1 : L 1=[]) (h5 : L 5=[]) (h7 : L 7=[]) (hL : LenOK B L)
    (hctrl : (L 2).length+3 ≤ B) :
    ∃ T, Runs (LenOK B) (present D.length) L
      (result L ps (Shallot.stripPrefix? w (sfx x p))) T := by
  have hword := hL 4
  rw [hw,SequentialCaptureCopyMachine.wordTape_append,
    SequentialCaptureSpliceMachine.wordTape_cons] at hword
  simp only [List.length_append,wordCode,characters,List.length_reverse,List.length_map,
    List.length_singleton] at hword
  let rest := tail ++ wordTape R
  have hwords : L 4=(rest ++ wordCode w) ++ wordTape D := by
    simpa only [rest,SequentialCaptureCopyMachine.wordTape_append,
      SequentialCaptureSpliceMachine.wordTape_cons,List.append_assoc] using hw
  obtain ⟨Ts,hs⟩ := skipWords_runs D (rest ++ wordCode w) L hwords hL (by
    simp only [h7,List.length_nil]; omega)
  let N := (L.set 4 (rest ++ wordCode w)).set 7 (wordTape D).reverse
  have heN : (L.set 4 (rest ++ wordCode w)).set 7 (L 7 ++ (wordTape D).reverse)=N := by simp [N,h7]
  rw [heN] at hs
  have hN := end_fits hs
  have hh := runs_push (i := (2 : Fin 8)) (e := 1) hN (by
    apply lenOK_set hN 2
    simpa [N,Lists.set] using hctrl)
  let M := N.set 2 (L 2 ++ [1])
  obtain ⟨Tm,hm⟩ := SequentialWordInputMachine.original_input_runs x w p ps hchain hp
    (L 2) rest (wordTape D).reverse M rfl
    (by simpa [M,N,Lists.set] using hcur) (by simp [M,N,Lists.set,wordCode,List.append_assoc])
    (by simpa [M,N,Lists.set] using hx) rfl
    (by simpa [M,N,Lists.set] using h1) (by simpa [M,N,Lists.set] using h5) (end_fits hh)
    (by simpa [rest,Nat.add_assoc] using hword)
  have he : SequentialWordInputMachine.result M (L 2) rest (wordTape D).reverse ps w x
      (Shallot.stripPrefix? w (sfx x p)) = result L ps (Shallot.stripPrefix? w (sfx x p)) := by
    funext j
    by_cases h0 : j=0 <;> by_cases h2 : j=2 <;> by_cases h4 : j=4 <;>
      by_cases h5j : j=5 <;> by_cases h6 : j=6 <;> by_cases h7j : j=7 <;>
      simp [SequentialWordInputMachine.result,result,M,N,rest,Lists.set,h0,h2,h4,h5j,h6,h7j,
        h5,h7,hx,hw,SequentialCaptureCopyMachine.wordTape_append,
        SequentialCaptureSpliceMachine.wordTape_cons,wordCode,List.append_assoc]
  rw [he] at hm
  exact ⟨_,hs.seq (hh.seq hm)⟩

theorem missing_runs (x : List Char) (p : Nat) (ps : List Nat)
    (hchain : SequentialCursorChain.Chain p ps x.length) (L : Lists 8) {B : Nat}
    (hcur : L 0=cursors (p :: ps)) (h1 : L 1=[]) (hL : LenOK B L) (hctrl : (L 2).length+3 ≤ B) :
    ∃ T, Runs (LenOK B) missing L (result L ps none) T := by
  obtain ⟨Td,hd⟩ := drop_current_runs (src := (0 : Fin 8)) (tmp := 1) (by decide) hchain L hcur h1 hL
  let M := L.set 0 (cursors ps)
  have hp := runs_push (i := (2 : Fin 8)) (e := 0) (end_fits hd) (by
    apply lenOK_set (end_fits hd) 2
    simpa [M,Lists.set] using hctrl)
  have he : M.set 2 (M 2 ++ [0]) = result L ps none := by
    funext j
    by_cases h0 : j=0 <;> by_cases h2 : j=2 <;> simp [result,M,Lists.set,h0,h2]
  rw [he] at hp
  exact ⟨_,hd.seq hp⟩

/-- Missing parameters and actual word mismatches both return failure. The
runtime length guard prevents reading a continuation's word as an argument. -/
theorem match_runs (k : Nat) (E : CaptureEnv) (x : List Char) (p : Nat) (ps : List Nat)
    (hchain : SequentialCursorChain.Chain p ps x.length) (hp : p ≤ x.length)
    (C tail : List Nat) (L : Lists 8) {B : Nat}
    (hctrl : L 2=C ++ unary E.length) (hstop : symIs 1 (lastSym C)=false)
    (hcur : L 0=cursors (p :: ps)) (hw : L 4=tail ++ wordTape E) (hx : L 6=characters x)
    (h1 : L 1=[]) (h5 : L 5=[]) (h7 : L 7=[]) (hL : LenOK B L) (hcap : (L 2).length+3 ≤ B) :
    ∃ T, Runs (LenOK B) (program k) L
      (result L ps (E[k]?.bind (fun w => Shallot.stripPrefix? w (sfx x p)))) T := by
  have hb : ∃ T, Runs (LenOK B) (if k+1≤E.length then present k else missing) L
      (result L ps (E[k]?.bind (fun w => Shallot.stripPrefix? w (sfx x p)))) T := by
    by_cases hk : k<E.length
    · have he : E=E.take k ++ E[k] :: E.drop (k+1) := by
        rw [← List.drop_eq_getElem_cons hk]
        exact (List.take_append_drop k E).symm
      have hlen : (E.take k).length=k := by simp [Nat.min_eq_left (Nat.le_of_lt hk)]
      have hr := present_runs (E.take k) (E.drop (k+1)) E[k] x p ps hchain hp tail L hcur
        (by simpa only [← he] using hw) hx h1 h5 h7 hL hcap
      simpa only [hlen,if_pos (show k+1≤E.length by omega),List.getElem?_eq_getElem hk,Option.bind_some] using hr
    · have hn : E[k]?=none := List.getElem?_eq_none_iff.mpr (by omega)
      simpa only [if_neg (show ¬k+1≤E.length by omega),hn,Option.bind_none] using
        missing_runs x p ps hchain L hcur h1 hL hcap
  obtain ⟨T,ht⟩ := hb
  exact SequentialCountGuardMachine.guard_runs (present k) missing (k+1) E.length C L _ hctrl h1 hstop hL ht


theorem constOK (k E : Nat) (hE : 2 ≤ E) : (program k).ConstOK E := by
  have hs : (skipWords k).ConstOK E := by
    induction k with
    | zero => trivial
    | succ k ih => exact ⟨by simp [SequentialCaptureSpliceMachine.moveWord,
        SequentialCaptureSpliceMachine.scanWord,moveTop,LProg.ConstOK],ih⟩
  have hp : (present k).ConstOK E := ⟨hs,by change 1 < E; omega,SequentialWordInputMachine.constOK E hE⟩
  have hm : missing.ConstOK E := by
    simp [missing,dropBlock,scan,moveTop,moveAll,clearP,LProg.ConstOK]
    omega
  exact SequentialCountGuardMachine.constOK (present k) missing (k+1) E hp hm

end Shallot.MacroPeg.CBV.SequentialParamMatchMachine
