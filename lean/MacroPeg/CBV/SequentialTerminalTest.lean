import MacroPeg.CBV.SequentialAtomCodec

/-! Inspect a terminal expression value in the ordinary numeric word encoding.
Only success at remaining position zero produces the acceptance marker. -/
namespace Shallot.MacroPeg.CBV.SequentialTerminalTest
open Complexity SequentialStack SequentialStackCodec
open SequentialNumericFive (st)
open SequentialNotReturn (prepend applied prepend_runs)

def accept (r : Res) : Bool := decide (r=some (some 0))
def word (r : Res) : List Nat := SequentialAtomCodec.outputFields r 0 []
def rest (r : Res) : List Nat := match r with | some (some q) => [0,q] | _ => [0]

def check : NProg 5 := .ite 1 .zero (.seq (.prim (.pushZ 2)) (nclr 1)) (nclr 1)
def program : NProg 5 := .seq (nmvAll 0 1 (by decide))
  (prepend [.pop 1,.pop 1] (caseTop 1 [nclr 1,nclr 1,check] (.halt false)))

private theorem check_runs (q : Nat) :
    NRuns check (st [] [0,q] [] [] []) (st [] [] (if q=0 then [0] else []) [] []) 7 := by
  cases q with
  | zero =>
    have hp := nruns_pushZ 2 (st [] [0,0] [] [] [])
    have hc := nruns_clr 1 (st [] [0,0] [0] [] [])
    have hp' : NRuns (.prim (.pushZ (K := 5) 2)) (st [] [0,0] [] [] []) (st [] [0,0] [0] [] []) 1 := by simpa using hp
    have hc' : NRuns (nclr (K := 5) 1) (st [] [0,0] [0] [] []) (st [] [] [0] [] []) 5 := by simpa using hc
    simpa [check] using (hp'.seq hc').iteT (i := 1) (c := .zero) (by simp [NTest.eval]) (q := nclr 1)
  | succ q =>
    have hc : NRuns (nclr (K := 5) 1) (st [] [0,q+1] [] [] []) (st [] [] [] [] []) 5 := by
      simpa using nruns_clr 1 (st [] [0,q+1] [] [] [])
    have hh := hc.iteF (i := 1) (c := .zero) (by simp [NTest.eval]) (p := .seq (.prim (.pushZ 2)) (nclr 1))
    simpa [check] using hh.mono (by omega)

theorem numeric_runs (r : Res) :
    NRuns program (st (word r) [] [] [] []) (st [] [] (if accept r then [0] else []) [] []) 100 := by
  let R := (writeRes r ++ [0]).reverse
  let S := st [] (word r).reverse [] [] []
  let A := st [] R [] [] []
  have hm := nruns_mvAll 0 1 (by decide : (0 : Fin 5) ≠ 1) (st (word r) [] [] [] [])
  have heS : ((st (word r) [] [] [] []).set 1 ([] ++ (word r).reverse)).set 0 [] = S := by simp [S]
  change NRuns _ (st (word r) [] [] [] [])
    (((st (word r) [] [] [] []).set 1 ([] ++ (word r).reverse)).set 0 []) (3*(word r).length+1) at hm
  rw [heS] at hm
  have hp : applied [.pop (K := 5) 1,.pop 1] S = A := by
    have he : S=st [] (R ++ [0,3]) [] [] [] := by
      simp [S,R,word,SequentialAtomCodec.outputFields,List.reverse_append,List.append_assoc]
    rw [he]
    simp [applied,NPrim.apply,A]
  have hR : R=rest r ++ [SequentialAtomCodec.status r] := by
    cases r with
    | none => rfl
    | some rr => cases rr <;> rfl
  have hi : SequentialAtomCodec.status r < [nclr (K := 5) 1,nclr 1,check].length := by
    cases r with | none => decide | some rr => cases rr <;> simp [SequentialAtomCodec.status]
  have hc := caseTop_runs 1 [nclr (K := 5) 1,nclr 1,check] (.halt false) (SequentialAtomCodec.status r) hi A (rest r)
    (by simp [A,hR]) (st [] [] (if accept r then [0] else []) [] []) 7 (by
      have heA : A.set 1 (rest r) = st [] (rest r) [] [] [] := by simp [A]
      rw [heA]
      cases r with
      | none => simpa [SequentialAtomCodec.status,rest,accept] using (nruns_clr 1 (st [] [0] [] [] [])).mono (by simp)
      | some rr =>
        cases rr with
        | none => simpa [SequentialAtomCodec.status,rest,accept] using (nruns_clr 1 (st [] [0] [] [] [])).mono (by simp)
        | some q => simpa [SequentialAtomCodec.status,rest,accept] using check_runs q)
  have hh := hm.seq (prepend_runs [.pop (K := 5) 1,.pop 1] _ S _ _ (by rw [hp]; exact hc))
  have hw : (word r).length ≤ 5 := by
    cases r with | none => decide | some rr => cases rr <;> simp [word,SequentialAtomCodec.outputFields,writeRes]
  have hs : SequentialAtomCodec.status r ≤ 2 := by
    cases r with | none => decide | some rr => cases rr <;> simp [SequentialAtomCodec.status]
  exact hh.mono (by simp; omega)

def space (N : Nat) : Nat := 5*(N+1)+grow N 100+2

theorem compiled_runs (r : Res) {N : Nat} (hN : 3 ≤ N) (hq : ∀ q, r=some (some q) → q ≤ N) :
    Runs (LenOK (space N)) program.compile (encL (st (word r) [] [] [] []))
      (encL (st [] [] (if accept r then [0] else []) [] [])) (100*ncost (space N)) := by
  have hv : ∀ v ∈ word r, v ≤ N := by
    cases r with
    | none => simp [word,SequentialAtomCodec.outputFields,writeRes]; omega
    | some rr =>
      cases rr with
      | none => simp [word,SequentialAtomCodec.outputFields,writeRes]; omega
      | some q => have hh := hq q rfl; simp [word,SequentialAtomCodec.outputFields,writeRes]; omega
  have hlen : (word r).length ≤ 5 := by
    cases r with | none => decide | some rr => cases rr <;> simp [word,SequentialAtomCodec.outputFields,writeRes]
  have hc := SequentialFrontRead.locals_length (word r) N hv
  change (Complexity.encS (word r)).length ≤ (word r).length*(N+1) at hc
  have hc' := Nat.le_trans hc (Nat.mul_le_mul_right (N+1) hlen)
  have hb : Bnd N (5*(N+1)) (st (word r) [] [] [] []) := by
    constructor
    · intro i v hvi
      by_cases hi : i=0
      · exact hv v (by simpa [SequentialNumericFive.st,hi] using hvi)
      · simp [SequentialNumericFive.st,hi] at hvi
    · intro i
      by_cases hi : i=0
      · subst i; exact hc'
      · simp [SequentialNumericFive.st,hi,Complexity.encS]
  obtain ⟨t,ht,he⟩ := numeric_runs r
  have hx := (nexec_space he N (5*(N+1)) hb).2 (space N)
    (by have hh := grow_mono (m := N) ht; unfold space; omega)
  obtain ⟨u,hu,h⟩ := nexec_compile (fun _ h => h) hx
  exact ⟨u,Nat.le_trans hu (Nat.mul_le_mul_right _ ht),h⟩

theorem space_linear (N : Nat) : space N=105*N+10107 := by unfold space grow; omega

end Shallot.MacroPeg.CBV.SequentialTerminalTest
