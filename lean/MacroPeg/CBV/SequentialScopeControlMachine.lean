import MacroPeg.CBV.SequentialTagDispatchMachine

/-! Restore a saved environment header after a scope return, retaining all
runtime result fields. The only program parameter is their fixed field count. -/
namespace Shallot.MacroPeg.CBV.SequentialScopeControlMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialControlEditMachine

private theorem blocks_nil : blocks [] = [] := rfl
private theorem blocks_length (ns : List Nat) : (blocks ns).length = ns.sum+ns.length := by
  rw [blocks,bits_length,SequentialCursorChain.encodeDeltas_length]

def program (fields : Nat) : LProg 8 := .seq (discardBlock 2)
  (.seq (moveBlock 2 5) (.seq (saveMany 2 1 fields) (.seq (discardBlock 2)
    (.seq (moveBlock 2 7) (.seq (moveAll 1 2) (.seq (moveAll 5 2)
      (.seq (.pop 2) (moveAll 7 2))))))))

theorem restore_runs (a k b : Nat) (fields tail : List Nat) (L : Lists 8) {B : Nat}
    (hsrc : L 2 = tail ++ blocks [7,b] ++ blocks fields ++ blocks [a,k+1])
    (h1 : L 1 = []) (h5 : L 5 = []) (h7 : L 7 = []) (hL : LenOK B L) :
    ∃ T, Runs (LenOK B) (program fields.length) L (L.set 2 (tail ++ blocks ([b,k] ++ fields))) T := by
  have hc := hL 2
  rw [hsrc] at hc
  simp [List.length_append,blocks_length] at hc
  let D := tail ++ blocks [7,b] ++ blocks fields
  have hs1 : L 2 = (D ++ blocks [k+1]) ++ [0] ++ unary a := by
    rw [hsrc,blocks_cons a [k+1]]
    simp only [D,List.append_assoc]
  obtain ⟨T1,hr1⟩ := discardBlock_runs (src := (2 : Fin 8)) a (D ++ blocks [k+1]) L hs1 hL
  let N1 := L.set 2 (D ++ blocks [k+1])
  have hs2 : N1 2 = D ++ [0] ++ unary (k+1) := by simp [N1,blocks_cons,blocks_nil]
  obtain ⟨T2,hr2⟩ := moveBlock_runs (src := (2 : Fin 8)) (tmp := 5) (by decide) (k+1) D N1 hs2
    (end_fits hr1) (by simp [N1,Lists.set,h5]; omega)
  let N2 := (N1.set 2 D).set 5 (N1 5 ++ unary (k+1) ++ [0])
  obtain ⟨T3,hr3⟩ := saveMany_runs (src := (2 : Fin 8)) (tmp := 1) (by decide) fields
    (tail ++ blocks [7,b]) N2 (by simp [N2,Lists.set,D]) (end_fits hr2)
    (by simp [N2,N1,Lists.set,h1,blocks_length]; omega)
  let N3 := (N2.set 2 (tail ++ blocks [7,b])).set 1 (N2 1 ++ (blocks fields).reverse)
  have hs4 : N3 2 = (tail ++ blocks [b]) ++ [0] ++ unary 7 := by simp [N3,Lists.set,blocks_cons,List.append_assoc]
  obtain ⟨T4,hr4⟩ := discardBlock_runs (src := (2 : Fin 8)) 7 (tail ++ blocks [b]) N3 hs4 (end_fits hr3)
  let N4 := N3.set 2 (tail ++ blocks [b])
  have hs5 : N4 2 = tail ++ [0] ++ unary b := by simp [N4,blocks_cons,blocks_nil]
  obtain ⟨T5,hr5⟩ := moveBlock_runs (src := (2 : Fin 8)) (tmp := 7) (by decide) b tail N4 hs5
    (end_fits hr4) (by simp [N4,N3,N2,N1,Lists.set,h7]; omega)
  let N5 := (N4.set 2 tail).set 7 (N4 7 ++ unary b ++ [0])
  have cap6 : (N5 2).length+(N5 1).length+2 ≤ B := by
    simp [N5,N4,N3,N2,N1,Lists.set,h1,blocks_length]
    omega
  have hr6 := moveAll_runs_bounded (by decide : (1 : Fin 8) ≠ 2) (end_fits hr5) cap6
  let N6 := (N5.set 2 (N5 2 ++ (N5 1).reverse)).set 1 []
  have cap7 : (N6 2).length+(N6 5).length+2 ≤ B := by
    simp [N6,N5,N4,N3,N2,N1,Lists.set,h1,h5,blocks_length]
    omega
  have hr7 := moveAll_runs_bounded (by decide : (5 : Fin 8) ≠ 2) (end_fits hr6) cap7
  let N7 := (N6.set 2 (N6 2 ++ (N6 5).reverse)).set 5 []
  have hN7 : LenOK B N7 := end_fits hr7
  have hs8 : N7 2 = (tail ++ blocks fields ++ blocks [k]) ++ [1] := by
    simp [N7,N6,N5,N4,N3,N2,N1,Lists.set,h1,h5,blocks_cons,blocks_nil,
      List.reverse_append,List.replicate_succ',List.append_assoc]
    rw [← List.replicate_succ,List.replicate_succ']
  let N8 := N7.set 2 (tail ++ blocks fields ++ blocks [k])
  have hN8 : LenOK B N8 := by
    apply lenOK_set hN7 2
    have hh := hN7 2
    rw [hs8] at hh
    simp only [List.length_append,List.length_singleton] at hh
    simp only [List.length_append]
    omega
  have hpop : N7.set 2 (N7 2).dropLast = N8 := by rw [hs8,List.dropLast_concat]
  have hr8 := runs_pop (i := (2 : Fin 8)) hN7 (by rw [hpop]; exact hN8)
  rw [hpop] at hr8
  have cap9 : (N8 2).length+(N8 7).length+2 ≤ B := by
    simp [N8,N7,N6,N5,N4,N3,N2,N1,Lists.set,h7,blocks_length]
    omega
  have hr9 := moveAll_runs_bounded (by decide : (7 : Fin 8) ≠ 2) hN8 cap9
  have hout : (N8.set 2 (N8 2 ++ (N8 7).reverse)).set 7 [] =
      L.set 2 (tail ++ blocks ([b,k] ++ fields)) := by
    funext j
    by_cases h2 : j=2 <;> by_cases h1j : j=1 <;> by_cases h5j : j=5 <;> by_cases h7j : j=7 <;>
      simp [N8,N7,N6,N5,N4,N3,N2,N1,Lists.set,h2,h1j,h5j,h7j,h1,h5,h7,blocks_cons,blocks_nil,
        List.reverse_append,List.append_assoc]
  rw [hout] at hr9
  exact ⟨_,hr1.seq (hr2.seq (hr3.seq (hr4.seq (hr5.seq (hr6.seq (hr7.seq (hr8.seq hr9)))))))⟩

theorem constOK (fields E : Nat) : (program fields).ConstOK E := by
  have hs : (saveMany (2 : Fin 8) 1 fields).ConstOK E := by
    induction fields with
    | zero => trivial
    | succ n ih => exact ⟨by simp [moveBlock,scan,moveTop,LProg.ConstOK],ih⟩
  simp [program,discardBlock,discardHead,moveBlock,scan,moveTop,moveAll,hs,LProg.ConstOK]

end Shallot.MacroPeg.CBV.SequentialScopeControlMachine
