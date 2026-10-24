import MacroPeg.CBV.SequentialCursorEdit
import Complexity.ListCompile

/-! Actual list-machine subroutines for local cursor edits. Every visited
state obeys the supplied per-tape capacity; the untouched tapes are retained. -/
namespace Shallot.MacroPeg.CBV.SequentialCursorEditMachine
open Complexity SequentialCursorEdit

variable {k : Nat}

def scan (src tmp : Fin k) : LProg k := .loop src (symIs 1) (moveTop src tmp)

/-- Move only the unary head block, stopping at its terminator. Neither a
cursor count nor a decoded list of cursor integers is provided to the program. -/
theorem scan_runs {src tmp : Fin k} (hd : src ≠ tmp) (p : Nat) (S : List Nat)
    (L : Lists k) {B : Nat} (hsrc : L src = S ++ unary p)
    (hstop : symIs 1 (lastSym S) = false) (hL : LenOK B L)
    (hcap : (L tmp).length + p + 2 ≤ B) :
    Runs (LenOK B) (scan src tmp) L
      ((L.set src S).set tmp (L tmp ++ unary p)) ((p+1)*3) := by
  induction p generalizing L with
  | zero =>
    have he : ((L.set src S).set tmp (L tmp ++ unary 0)) = L := by
      simp only [List.replicate_zero,List.append_nil] at hsrc ⊢
      rw [← hsrc,Lists.set_get_self,Lists.set_get_self]
    rw [he]
    exact ⟨1,by omega,.loopF hL (by simpa only [hsrc,List.replicate_zero,List.append_nil] using hstop)⟩
  | succ p ih =>
    have hs : L src = (S ++ unary p) ++ [1] := by
      simpa only [List.replicate_succ',List.append_assoc] using hsrc
    have hb : (L tmp).length + 3 ≤ B := by omega
    obtain ⟨hcopy,hm⟩ := lenOK_moveTop hL hd hb
    have hr := runs_moveTop hd hL hcopy hm
    have hsource : (L.moveTop src tmp) src = S ++ unary p := by
      simp only [moveTop_i,hs,List.dropLast_append_cons,List.dropLast_singleton,List.append_nil]
    have hdest : (L.moveTop src tmp) tmp = L tmp ++ [1] := by
      simp [moveTop_j hd,hs]
    have ht := ih (L.moveTop src tmp) hsource hm (by rw [hdest]; simp; omega)
    have he : (((L.moveTop src tmp).set src S).set tmp ((L.moveTop src tmp) tmp ++ unary p)) =
        (L.set src S).set tmp (L tmp ++ unary (p+1)) := by
      funext i
      by_cases hi : i = src
      · subst i; simp [Lists.set,hd]
      · by_cases hj : i = tmp
        · subst i
          simp only [Lists.set_same,hdest]
          rw [List.append_assoc]
          rfl
        · simp [Lists.set,hi,hj,moveTop_other hi hj]
    rw [he] at ht
    obtain ⟨t1,ht1,hx1⟩ := hr
    obtain ⟨t2,ht2,hx2⟩ := ht
    exact ⟨t1+1+t2,by omega,.loopC hL (by simp only [hs,lastSym_append,symIs]; decide) hx1 hx2⟩


theorem end_fits {B : Nat} {p : LProg k} {L M : Lists k} {T : Nat}
    (h : Runs (LenOK B) p L M T) : LenOK B M := by
  obtain ⟨t,ht,hx⟩ := h
  exact hx.q_end _ (Or.inl rfl)

theorem restore_runs {src tmp : Fin k} (hd : src ≠ tmp) (p : Nat) (L : Lists k)
    {B : Nat} (htmp : L tmp = unary p) (hL : LenOK B L)
    (hcap : (L src).length + p + 2 ≤ B) :
    Runs (LenOK B) (moveAll tmp src) L
      ((L.set src (L src ++ unary p)).set tmp []) ((p+1)*3) := by
  simpa only [htmp,List.length_replicate,List.reverse_replicate] using
    moveAll_runs_bounded (Ne.symm hd) hL (by simpa only [htmp,List.length_replicate] using hcap)

theorem clear_runs {tmp : Fin k} (L : Lists k) {B : Nat} (hL : LenOK B L) :
    Runs (LenOK B) (clearP tmp) L (L.set tmp []) (((L tmp).length+1)*2) := by
  apply clearP_spec
  intro n hn
  apply lenOK_set hL tmp
  have hh := hL tmp
  simp only [List.length_take]
  omega

def dropBlock (src tmp : Fin k) : LProg k := .seq (scan src tmp)
  (.seq (.pop src) (.ite src nonEmpty (moveAll tmp src) (clearP tmp)))

/-- Remove one delimiter and merge the adjacent difference blocks, clearing
all scratch. The suffix is preserved without decoding any of its cursors. -/
theorem dropBlock_runs {src tmp : Fin k} (hd : src ≠ tmp) (p : Nat) (rest : List Nat)
    (L : Lists k) {B : Nat} (hsrc : L src = rest ++ [0] ++ unary p)
    (htmp : L tmp = []) (hL : LenOK B L) :
    ∃ T, Runs (LenOK B) (dropBlock src tmp) L (L.set src (dropResult p rest)) T := by
  have hsize := hL src
  rw [hsrc] at hsize
  simp only [List.length_append,List.length_cons,List.length_nil,List.length_replicate] at hsize
  have hs := scan_runs hd p (rest ++ [0]) L hsrc
    (by simp [lastSym_append,symIs]) hL (by simp only [htmp,List.length_nil]; omega)
  let N := (L.set src (rest ++ [0])).set tmp (unary p)
  have heN : ((L.set src (rest ++ [0])).set tmp (L tmp ++ unary p)) = N := by simp [N,htmp]
  rw [heN] at hs
  have hN := end_fits hs
  let M := (L.set src rest).set tmp (unary p)
  have hM : LenOK B M := lenOK_set (lenOK_set hL src (by omega)) tmp (by simp; omega)
  have hepop : N.set src (N src).dropLast = M := by
    funext i
    by_cases hi : i=src <;> by_cases hj : i=tmp <;> simp_all [N,M,Lists.set]
  have hp := runs_pop (i := src) hN (by rw [hepop]; exact hM)
  rw [hepop] at hp
  have hbranch : ∃ T, Runs (LenOK B)
      (.ite src nonEmpty (moveAll tmp src) (clearP tmp)) M (L.set src (dropResult p rest)) T := by
    by_cases hr : rest = []
    · have hc := clear_runs (tmp := tmp) M hM
      have he : M.set tmp [] = L.set src (dropResult p rest) := by
        funext i
        by_cases hi : i=src <;> by_cases hj : i=tmp <;>
          simp_all [M,dropResult,Lists.set]
      rw [he] at hc
      exact ⟨_,hc.iteF hM (by simp [M,Lists.set,hd,hr,nonEmpty,lastSym])⟩
    · have hm : M tmp = unary p := by simp [M]
      have hc := restore_runs hd p M hm hM (by simp [M,Lists.set,hd]; omega)
      have he : (M.set src (M src ++ unary p)).set tmp [] = L.set src (dropResult p rest) := by
        funext i
        by_cases hi : i=src <;> by_cases hj : i=tmp <;>
          simp_all [M,dropResult,Lists.set]
      rw [he] at hc
      have hnon : nonEmpty (lastSym (M src)) = true := by
        have hh : lastSym rest ≠ 3 := fun he => hr (lastSym_eq_three.mp he)
        simpa [M,Lists.set,hd,nonEmpty] using hh
      exact ⟨_,hc.iteT hM hnon⟩
  obtain ⟨T,hb⟩ := hbranch
  exact ⟨_,hs.seq (hp.seq hb)⟩

def duplicate (src tmp : Fin k) : LProg k :=
  .seq (scan src tmp) (.seq (.push src 0) (moveAll tmp src))

/-- Insert a zero difference after the first cursor. One extra cell is
sufficient on every visited tape; all other tapes and the empty scratch survive. -/
theorem duplicate_runs {src tmp : Fin k} (hd : src ≠ tmp) (p : Nat) (rest : List Nat)
    (L : Lists k) {B : Nat} (hsrc : L src = rest ++ [0] ++ unary p)
    (htmp : L tmp = []) (hL : LenOK B L) (hcap : (L src).length+3 ≤ B) :
    ∃ T, Runs (LenOK B) (duplicate src tmp) L (L.set src (rest ++ [0,0] ++ unary p)) T := by
  have hsize := hcap
  rw [hsrc] at hsize
  simp only [List.length_append,List.length_cons,List.length_nil,List.length_replicate] at hsize
  have hs := scan_runs hd p (rest ++ [0]) L hsrc
    (by simp [lastSym_append,symIs]) hL (by simp only [htmp,List.length_nil]; omega)
  let N := (L.set src (rest ++ [0])).set tmp (unary p)
  have heN : ((L.set src (rest ++ [0])).set tmp (L tmp ++ unary p)) = N := by simp [N,htmp]
  rw [heN] at hs
  have hN := end_fits hs
  let M := (L.set src (rest ++ [0,0])).set tmp (unary p)
  have hM : LenOK B M := lenOK_set (lenOK_set hL src (by simp; omega)) tmp (by simp; omega)
  have hepush : N.set src (N src ++ [0]) = M := by
    funext i
    by_cases hi : i=src <;> by_cases hj : i=tmp <;>
      simp_all [N,M,Lists.set,List.append_assoc]
  have hp := runs_push (i := src) (e := 0) hN (by rw [hepush]; exact hM)
  rw [hepush] at hp
  have hm : M tmp = unary p := by simp [M]
  have hr := restore_runs hd p M hm hM (by simp [M,Lists.set,hd]; omega)
  have he : (M.set src (M src ++ unary p)).set tmp [] = L.set src (rest ++ [0,0] ++ unary p) := by
    funext i
    by_cases hi : i=src <;> by_cases hj : i=tmp <;> simp_all [M,Lists.set]
  rw [he] at hr
  exact ⟨_,hs.seq (hp.seq hr)⟩


def dropSaved (src saved tmp : Fin k) : LProg k :=
  .seq (scan src saved) (.seq (moveTop src saved)
    (.seq (dropBlock src tmp) (moveAll saved src)))

/-- Remove the second cursor while preserving the first cursor and the full
encoded suffix. Three distinct tapes suffice, and scratch is restored empty. -/
theorem dropSaved_runs {src saved tmp : Fin k} (hds : src ≠ saved) (hdt : src ≠ tmp)
    (hst : saved ≠ tmp) (p d : Nat) (rest : List Nat) (L : Lists k) {B : Nat}
    (hsrc : L src = rest ++ [0] ++ unary d ++ [0] ++ unary p)
    (hsaved : L saved = []) (htmp : L tmp = []) (hL : LenOK B L) :
    ∃ T, Runs (LenOK B) (dropSaved src saved tmp) L
      (L.set src (dropResult d rest ++ [0] ++ unary p)) T := by
  have hsize := hL src
  rw [hsrc] at hsize
  simp only [List.length_append,List.length_cons,List.length_nil,List.length_replicate] at hsize
  let tail := rest ++ [0] ++ unary d
  have hs := scan_runs hds p (tail ++ [0]) L hsrc
    (by simp [lastSym_append,symIs]) hL (by simp only [hsaved,List.length_nil]; omega)
  let N := (L.set src (tail ++ [0])).set saved (unary p)
  have heN : ((L.set src (tail ++ [0])).set saved (L saved ++ unary p)) = N := by simp [N,hsaved]
  rw [heN] at hs
  have hN := end_fits hs
  let M := (L.set src tail).set saved (unary p ++ [0])
  have hb : (N saved).length + 3 ≤ B := by simp [N]; omega
  obtain ⟨hc,hMraw⟩ := lenOK_moveTop hN hds hb
  have hp := runs_moveTop hds hN hc hMraw
  have heM : N.moveTop src saved = M := by
    funext i
    by_cases hi : i=src <;> by_cases hj : i=saved <;>
      simp_all [N,M,Lists.moveTop,Lists.set,List.append_assoc]
  rw [heM] at hp hMraw
  have hmt : M tmp = [] := by simp [M,Lists.set,Ne.symm hdt,Ne.symm hst,htmp]
  have hms : M src = rest ++ [0] ++ unary d := by simp [M,tail,Lists.set,hds]
  obtain ⟨Td,hrd⟩ := dropBlock_runs hdt d rest M hms hmt hMraw
  let D := M.set src (dropResult d rest)
  have hD : LenOK B D := end_fits hrd
  have hbound := dropResult_length d rest
  have hcap : (D src).length + (D saved).length + 2 ≤ B := by
    simp [D,M,Lists.set,Ne.symm hds]
    omega
  have hr := moveAll_runs_bounded (Ne.symm hds) hD hcap
  have he : (D.set src (D src ++ (D saved).reverse)).set saved [] =
      L.set src (dropResult d rest ++ [0] ++ unary p) := by
    funext i
    by_cases hi : i=src <;> by_cases hj : i=saved <;>
      simp_all [D,M,Lists.set,Ne.symm hds,List.append_assoc]
  rw [he] at hr
  exact ⟨_,hs.seq (hp.seq (hrd.seq hr))⟩

theorem drop_current_runs {src tmp : Fin k} (hd : src ≠ tmp) {p n : Nat} {ps : List Nat}
    (hchain : SequentialCursorChain.Chain p ps n) (L : Lists k) {B : Nat}
    (hsrc : L src = cursors (p :: ps)) (htmp : L tmp = []) (hL : LenOK B L) :
    ∃ T, Runs (LenOK B) (dropBlock src tmp) L (L.set src (cursors ps)) T := by
  rw [cursors_cons] at hsrc
  simpa only [drop_current hchain] using dropBlock_runs hd p _ L hsrc htmp hL

theorem duplicate_current_runs {src tmp : Fin k} (hd : src ≠ tmp) (p : Nat) (ps : List Nat)
    (L : Lists k) {B : Nat} (hsrc : L src = cursors (p :: ps)) (htmp : L tmp = [])
    (hL : LenOK B L) (hcap : (L src).length+3 ≤ B) :
    ∃ T, Runs (LenOK B) (duplicate src tmp) L (L.set src (cursors (p :: p :: ps))) T := by
  rw [cursors_cons] at hsrc
  simpa only [duplicate_current p ps] using duplicate_runs hd p _ L hsrc htmp hL hcap

theorem drop_saved_runs {src saved tmp : Fin k} (hds : src ≠ saved) (hdt : src ≠ tmp)
    (hst : saved ≠ tmp) {p q n : Nat} {ps : List Nat} (hpq : p ≤ q)
    (hchain : SequentialCursorChain.Chain q ps n) (L : Lists k) {B : Nat}
    (hsrc : L src = cursors (p :: q :: ps)) (hsaved : L saved = []) (htmp : L tmp = [])
    (hL : LenOK B L) :
    ∃ T, Runs (LenOK B) (dropSaved src saved tmp) L (L.set src (cursors (p :: ps))) T := by
  rw [cursors_cons] at hsrc
  simp only [SequentialCursorChain.deltas,blocks_cons] at hsrc
  simpa only [drop_saved hpq hchain] using dropSaved_runs hds hdt hst p (q-p) _ L hsrc hsaved htmp hL

/-- Reuse the established list-to-tape compiler. This theorem bounds every
intermediate tape state of each compiled subroutine, rather than its endpoints. -/
theorem tape_runs {B : Nat} {p : LProg k} {L M : Lists k} {T : Nat}
    (h : Runs (LenOK B) p L M T) (τ : Tapes k) (hrep : Rep L τ) :
    ∃ t τ', Exec (TFits B) p.compile τ t (.cont τ') ∧ Rep M τ' := by
  obtain ⟨tt,htt,hx⟩ := h
  obtain ⟨t,o,_,he,hr⟩ := (compile_exec (fun _ hh => hh) hx).1 τ hrep
  cases o with
  | stop b τ' => exact False.elim hr
  | cont τ' => exact ⟨t,τ',he,hr⟩

end Shallot.MacroPeg.CBV.SequentialCursorEditMachine
