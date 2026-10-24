import MacroPeg.CBV.SequentialCallPackedMachine

/-! Stream the query's runtime environment lengths into their new headers.
No decoded environment length or replacement control prefix is supplied. -/
namespace Shallot.MacroPeg.CBV.SequentialQueryInstallMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialControlEditMachine

private theorem blocks_nil : blocks [] = [] := rfl
private theorem blocks_length (ns : List Nat) : (blocks ns).length = ns.sum+ns.length := by
  rw [blocks,bits_length,SequentialCursorChain.encodeDeltas_length]

def program (body : Nat) : LProg 8 := .seq (moveBlock 2 1)
  (.seq (moveBlock 2 5) (.seq (discardMany 2 2) (.seq (moveBlock 2 7)
    (.seq (moveAll 1 2) (.seq (appendP 2 (blocks [7]))
      (.seq (appendP 2 (blocks [0,body])) (.seq (moveAll 5 2)
        (.seq (.push 2 1) (moveAll 7 2)))))))))

/-- The first header becomes a saved-scope field, the query's word count
becomes the current environment header, and the stack count increases by one. -/
theorem install_runs (body a k i w : Nat) (tail : List Nat) (L : Lists 8) {B : Nat}
    (hsrc : L 2 = tail ++ blocks [a,k,2,i,w])
    (h1 : L 1 = []) (h5 : L 5 = []) (h7 : L 7 = []) (hL : LenOK B L)
    (hfinal : (tail ++ blocks [w,k+1,0,body,7,a]).length+2 ≤ B) :
    ∃ T, Runs (LenOK B) (program body) L (L.set 2 (tail ++ blocks [w,k+1,0,body,7,a])) T := by
  have hc := hL 2
  rw [hsrc] at hc
  simp [List.length_append,blocks_length] at hc hfinal
  have hs1 : L 2 = (tail ++ blocks [k,2,i,w]) ++ [0] ++ unary a := by
    rw [hsrc,blocks_cons]
    simp only [List.append_assoc]
  obtain ⟨T1,hr1⟩ := moveBlock_runs (src := (2 : Fin 8)) (tmp := 1) (by decide) a
    (tail ++ blocks [k,2,i,w]) L hs1 hL (by simp only [h1,List.length_nil]; omega)
  let N1 := (L.set 2 (tail ++ blocks [k,2,i,w])).set 1 (L 1 ++ unary a ++ [0])
  have hN1 : LenOK B N1 := end_fits hr1
  have hs2 : N1 2 = (tail ++ blocks [2,i,w]) ++ [0] ++ unary k := by
    simp [N1,Lists.set,blocks_cons,List.append_assoc]
  obtain ⟨T2,hr2⟩ := moveBlock_runs (src := (2 : Fin 8)) (tmp := 5) (by decide) k
    (tail ++ blocks [2,i,w]) N1 hs2 hN1 (by simp [N1,Lists.set,h5]; omega)
  let N2 := (N1.set 2 (tail ++ blocks [2,i,w])).set 5 (N1 5 ++ unary k ++ [0])
  have hN2 : LenOK B N2 := end_fits hr2
  have hs3 : N2 2 = (tail ++ blocks [w]) ++ blocks [2,i] := by
    simp only [N2,Lists.set_ne _ _ (by decide : (2 : Fin 8) ≠ 5),Lists.set_same]
    rw [show [2,i,w] = [2,i] ++ [w] from rfl,blocks_append]
    simp only [List.append_assoc]
  obtain ⟨T3,hr3⟩ := discardMany_runs (src := (2 : Fin 8)) [2,i] (tail ++ blocks [w]) N2 hs3 hN2
  let N3 := N2.set 2 (tail ++ blocks [w])
  have hN3 : LenOK B N3 := end_fits hr3
  have hs4 : N3 2 = tail ++ [0] ++ unary w := by simp [N3,blocks_cons,blocks_nil]
  obtain ⟨T4,hr4⟩ := moveBlock_runs (src := (2 : Fin 8)) (tmp := 7) (by decide) w tail N3 hs4 hN3
    (by simp [N3,N2,N1,Lists.set,h7]; omega)
  let N4 := (N3.set 2 tail).set 7 (N3 7 ++ unary w ++ [0])
  have hN4 : LenOK B N4 := end_fits hr4
  have cap5 : (N4 2).length+(N4 1).length+2 ≤ B := by
    simp [N4,N3,N2,N1,Lists.set,h1]
    omega
  have hr5 := moveAll_runs_bounded (by decide : (1 : Fin 8) ≠ 2) hN4 cap5
  let N5 := (N4.set 2 (N4 2 ++ (N4 1).reverse)).set 1 []
  have hN5 : LenOK B N5 := end_fits hr5
  have cap6 : (N5 2).length+(blocks [7]).length+2 ≤ B := by
    simp [N5,N4,N3,N2,N1,Lists.set,h1,blocks_length]
    omega
  have hr6 := append_runs (2 : Fin 8) (blocks [7]) hN5 cap6
  let N6 := N5.set 2 (N5 2 ++ blocks [7])
  have hN6 : LenOK B N6 := end_fits hr6
  have cap7 : (N6 2).length+(blocks [0,body]).length+2 ≤ B := by
    simp [N6,N5,N4,N3,N2,N1,Lists.set,h1,blocks_length]
    omega
  have hr7 := append_runs (2 : Fin 8) (blocks [0,body]) hN6 cap7
  let N7 := N6.set 2 (N6 2 ++ blocks [0,body])
  have hN7 : LenOK B N7 := end_fits hr7
  have cap8 : (N7 2).length+(N7 5).length+2 ≤ B := by
    simp [N7,N6,N5,N4,N3,N2,N1,Lists.set,h1,h5,blocks_length]
    omega
  have hr8 := moveAll_runs_bounded (by decide : (5 : Fin 8) ≠ 2) hN7 cap8
  let N8 := (N7.set 2 (N7 2 ++ (N7 5).reverse)).set 5 []
  have hN8 : LenOK B N8 := end_fits hr8
  have hpush : LenOK B (N8.set 2 (N8 2 ++ [1])) := by
    apply lenOK_set hN8 2
    simp [N8,N7,N6,N5,N4,N3,N2,N1,Lists.set,h1,h5,blocks_length]
    omega
  have hr9 := runs_push (i := (2 : Fin 8)) (e := 1) hN8 hpush
  let N9 := N8.set 2 (N8 2 ++ [1])
  have hN9 : LenOK B N9 := end_fits hr9
  have cap10 : (N9 2).length+(N9 7).length+2 ≤ B := by
    simp [N9,N8,N7,N6,N5,N4,N3,N2,N1,Lists.set,h1,h5,h7,blocks_length]
    omega
  have hr10 := moveAll_runs_bounded (by decide : (7 : Fin 8) ≠ 2) hN9 cap10
  have hout : (N9.set 2 (N9 2 ++ (N9 7).reverse)).set 7 [] =
      L.set 2 (tail ++ blocks [w,k+1,0,body,7,a]) := by
    funext j
    by_cases h2 : j=2 <;> by_cases h1j : j=1 <;> by_cases h5j : j=5 <;> by_cases h7j : j=7 <;>
      simp [N9,N8,N7,N6,N5,N4,N3,N2,N1,Lists.set,h2,h1j,h5j,h7j,h1,h5,h7,blocks_cons,blocks_nil,
        List.reverse_append,List.replicate_succ',List.append_assoc]
  rw [hout] at hr10
  exact ⟨_,hr1.seq (hr2.seq (hr3.seq (hr4.seq (hr5.seq (hr6.seq (hr7.seq (hr8.seq (hr9.seq hr10))))))))⟩

theorem constOK (body E : Nat) (hE : 2 ≤ E) : (program body).ConstOK E := by
  have ha (fields : List Nat) : (appendP (2 : Fin 8) (blocks fields)).ConstOK E :=
    (replace_constOK hE (2 : Fin 8) 1 0 0 fields).2.2.1
  simp [program,moveBlock,scan,discardMany,discardBlock,discardHead,skipP,moveTop,moveAll,ha,LProg.ConstOK]
  omega

theorem finite_alphabet (body E : Nat) (hE : 2 ≤ E) : (program body).compile.SymOK (E+4) :=
  compile_symOK E (program body) (constOK body E hE)

end Shallot.MacroPeg.CBV.SequentialQueryInstallMachine
