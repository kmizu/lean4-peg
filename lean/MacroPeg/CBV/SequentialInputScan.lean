import MacroPeg.CBV.SequentialStepScan
import MacroPeg.CBV.SequentialInputHost

/-! Compile labelled front scans with arbitrary continuations in the expanded
input-preserving host, without allocating a selector outside the parsed stream. -/
namespace Shallot.MacroPeg.CBV.SequentialInputScan
open Complexity Complexity.BinaryWord SequentialFieldFetch
open SequentialReturnScan (Plan Trace)
open SequentialFrontRead (locals)
open SequentialInputHost (extend old old_runs extend_project)

def readMany (stride : Nat) : LProg 11 := .seq (copyLenP 3 10 7) (countedFetch stride)

def compile (leaf : Nat → LProg 20) : Plan → LProg 20
  | .done key => leaf key
  | .fail => .halt false
  | .word next => .seq (fetch.rename old) (compile leaf next)
  | .branch a b => .ite (old 3) nonEmpty (.seq (.pop (old 3)) (compile leaf b)) (compile leaf a)
  | .many stride next => .seq ((readMany stride).rename old) (compile leaf next)

theorem compile_trace (leaf : Nat → LProg 20) {p : Plan} {held out key : Nat} {vs : List Nat}
    (ht : Trace p held vs out key) {B width : Nat} (rest : List Nat) (tail : List Bool) (D X : List Nat)
    (hv : ∀ v ∈ vs, v < 2^width) (hval : ∀ v ∈ vs, 3*v+4 ≤ B)
    (hB : LenOK B (extend (start width (vs ++ rest) tail D held []) X))
    (hloc : D.length+(locals vs).length+2 ≤ B) (target : Lists 20)
    (hfinish : LenOK B (extend (start width rest tail (D ++ locals vs) out []) X) →
      ∃ T, Complexity.Runs (LenOK B) (leaf key)
        (extend (start width rest tail (D ++ locals vs) out []) X) target T) :
    ∃ T, Complexity.Runs (LenOK B) (compile leaf p)
      (extend (start width (vs ++ rest) tail D held []) X) target T := by
  induction ht generalizing D with
  | done key h =>
    change ∃ T, Complexity.Runs (LenOK B) (leaf key) _ target T
    simpa [locals] using hfinish (by simpa [locals] using hB)
  | @word next v vs out held key ht ih =>
    have hspace : D.length+(v+1)+(locals vs).length+2 ≤ B := by
      simpa [locals,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hloc
    have hX : X.length+2 ≤ B := hB 11
    obtain ⟨T1,hr1⟩ := fetch_runs (vs ++ rest) tail D [] (hv v (by simp)) (extend_project hB)
      (hval v (by simp)) (by omega)
    have hp := old_runs _ _ _ X hr1 hX
    have hnext : LenOK B (extend (start width (vs ++ rest) tail (D ++ 2 :: List.replicate v 1) v []) X) := by
      obtain ⟨_,_,he⟩ := hp
      exact he.q_end _ (Or.inl rfl)
    have he : (D ++ 2 :: List.replicate v 1) ++ locals vs = D ++ locals (v :: vs) := by
      simp [locals,List.append_assoc]
    obtain ⟨T2,hr2⟩ := ih (D := D ++ 2 :: List.replicate v 1)
      (fun n hn => hv n (by simp [hn])) (fun n hn => hval n (by simp [hn])) hnext
      (by simp; omega) (by simpa only [he] using hfinish)
    exact ⟨T1+T2,hp.seq hr2⟩
  | @zero a b vs out key ht ih =>
    obtain ⟨T,hr⟩ := ih D hv hval hB hloc hfinish
    have hz : nonEmpty (lastSym (extend (start width (vs ++ rest) tail D 0 []) X (old 3))) = false := by
      rw [SequentialInputHost.extend_get]
      simp [start,nonEmpty,lastSym]
    exact ⟨T+1,hr.iteF hB hz⟩
  | @positive a b n vs out key ht ih =>
    have hX : X.length+2 ≤ B := hB 11
    have hp := pop_unary (n := n) (i := (3 : Fin 11))
      (L := start width (vs ++ rest) tail D (n+1) []) (by simp [start]) (extend_project hB)
    have he : (start width (vs ++ rest) tail D (n+1) []).set 3 (List.replicate n 1) =
        start width (vs ++ rest) tail D n [] := by
      funext i
      by_cases hi : i=3 <;> simp_all [start,Lists.set]
    rw [he] at hp
    have hp20 := old_runs _ _ _ X hp hX
    have hnext : LenOK B (extend (start width (vs ++ rest) tail D n []) X) := by
      obtain ⟨_,_,he⟩ := hp20
      exact he.q_end _ (Or.inl rfl)
    obtain ⟨T,hr⟩ := ih D hv hval hnext hloc hfinish
    have hz : nonEmpty (lastSym (extend (start width (vs ++ rest) tail D (n+1) []) X (old 3))) = true := by
      rw [SequentialInputHost.extend_get]
      exact unary_nonEmpty (i := 3) (n := n) (by simp [start])
    exact ⟨_,(hp20.seq hr).iteT hB hz⟩
  | @many stride next n chunk vs out key hlen ht ih =>
    let L := start width ((chunk ++ vs) ++ rest) tail D n []
    have hspace : D.length+(locals chunk).length+(locals vs).length+2 ≤ B := by
      simpa [locals,List.flatMap_append,Nat.add_assoc] using hloc
    have hX : X.length+2 ≤ B := hB 11
    have hL : LenOK B L := extend_project hB
    have hcount : n+2 ≤ B := by simpa [L,start] using hL 3
    have hc := copyLen_spec (by decide : ([3,10,7] : List (Fin 11)).Nodup)
      (L := L) (B := B) (by simp [L,start]) hL (by simp [L,start]; exact hcount)
    have he : L.set 10 (L 10 ++ List.replicate (L 3).length 1) =
        start width (chunk ++ (vs ++ rest)) tail D n (List.replicate n 1) := by
      funext i
      by_cases hi : i=10 <;> simp_all [L,start,Lists.set,List.append_assoc]
    rw [he] at hc
    have hloop : LenOK B (start width (chunk ++ (vs ++ rest)) tail D n (List.replicate n 1)) := by
      obtain ⟨_,_,he⟩ := hc
      exact he.q_end _ (Or.inl rfl)
    obtain ⟨T1,hr1⟩ := counted_fetch_runs chunk (vs ++ rest) tail D hlen
      (fun v hm => hv v (by simp [hm])) (fun v hm => hval v (by simp [hm])) hloop (by omega)
    have hp := old_runs _ _ _ X (hc.seq hr1) hX
    have hnext : LenOK B (extend (start width (vs ++ rest) tail (D ++ locals chunk) (after n chunk) []) X) := by
      obtain ⟨_,_,he⟩ := hp
      exact he.q_end _ (Or.inl rfl)
    have heout : (D ++ locals chunk) ++ locals vs = D ++ locals (chunk ++ vs) := by
      simp [locals,List.flatMap_append,List.append_assoc]
    obtain ⟨T2,hr2⟩ := ih (D := D ++ locals chunk)
      (fun v hm => hv v (by simp [hm])) (fun v hm => hval v (by simp [hm])) hnext
      (by simp; omega) (by simpa only [heout] using hfinish)
    exact ⟨_,by simpa [compile,readMany,L,List.append_assoc,LProg.rename] using hp.seq hr2⟩

end Shallot.MacroPeg.CBV.SequentialInputScan
