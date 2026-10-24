import MacroPeg.CBV.SequentialArgHeadReturn
import MacroPeg.CBV.SequentialStarLookup

/-! Strict-progress return through a repetition frame. -/
namespace Shallot.MacroPeg.CBV.SequentialStarReturn
open Complexity SequentialStack SequentialStackCodec SequentialStackPool CBVtoCBN
open SequentialNotReturn (prepend applied prepend_runs constants)
open SequentialSeqReturn (st reg)
open SequentialArgHeadReturn (bnd_cells annotate end_fits)

def prepareOps : List (NPrim 4) :=
  [.dup 1 2 (by decide), .pop 1, .dup 1 3 (by decide), .pop 1, .dec 3,
    .pop 1, .pushZ 0, .dup 1 0 (by decide), .pop 1, .dup 2 0 (by decide),
    .dup 1 3 (by decide)]
def prepare : NProg 4 := prepend prepareOps (.prim (.pop 1))

theorem prepare_runs (q k m p a : Nat) (E : List Nat) :
    NRuns prepare (st [] (E.reverse ++ [a,p,m,3,k+1,q]) [] [])
      (st [0,m,q] (E.reverse ++ [a]) [q] [k,p]) 12 := by
  have hr := prepend_runs prepareOps (.prim (.pop 1))
    (st [] (E.reverse ++ [a,p,m,3,k+1,q]) [] []) _ 1 (nruns_prim _ _)
  have he : (NPrim.pop 1).apply (applied prepareOps (st [] (E.reverse ++ [a,p,m,3,k+1,q]) [] [])) =
      st [0,m,q] (E.reverse ++ [a]) [q] [k,p] := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp [st,prepareOps,applied,NPrim.apply,mapTop,Lists.set]
  rw [he] at hr
  exact hr

def resumeFinish : List (NPrim 4) := [.dup 3 0 (by decide)]
def resume (ns : List CompileNode) : NProg 4 :=
  .seq (nclr 2) (.seq (.prim (.pop 3)) (.seq (SequentialStarLookup.program 1 ns)
    (.seq (nmv 1 0 (by decide)) (.seq (nmvAll 1 0 (by decide))
      (prepend resumeFinish (.prim (.pop 3)))))))

theorem resume_runs (ns : List CompileNode) (a : MExp) (ha : ExprOK ns a)
    (q k m r : Nat) (Q E : List Nat) (hQ : Q.length ≤ 1) :
    NRuns (resume ns) (st [0,m,q] (E.reverse ++ [exprId ns a]) Q [k,r])
      (st ([0,m,q,exprId ns (.star a)] ++ E ++ [k]) [] [] [])
      (3 * E.length + 3 * (exprPool ns).length + 20) := by
  let S := st [0,m,q] (E.reverse ++ [exprId ns a]) Q [k,r]
  let A := st [0,m,q] (E.reverse ++ [exprId ns a]) [] [k,r]
  let B := st [0,m,q] (E.reverse ++ [exprId ns a]) [] [k]
  let C := st [0,m,q] (E.reverse ++ [exprId ns (.star a)]) [] [k]
  let D := st [0,m,q,exprId ns (.star a)] E.reverse [] [k]
  let R := st ([0,m,q,exprId ns (.star a)] ++ E) [] [] [k]
  have hc := nruns_clr 2 S
  have heA : S.set 2 [] = A := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;> simp [S,A,st,Lists.set]
  rw [heA] at hc
  have hp := nruns_pop 3 A (l := [k]) (v := r) rfl
  have heB : A.set 3 [k] = B := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;> simp [A,B,st,Lists.set]
  rw [heB] at hp
  have hl := SequentialStarLookup.runs 1 ns a ha B E.reverse rfl
  have heC : B.set 1 (E.reverse ++ [exprId ns (.star a)]) = C := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;> simp [B,C,st,Lists.set]
  rw [heC] at hl
  have hv := nruns_mv 1 0 (by decide : (1 : Fin 4) ≠ 0) C (l := E.reverse) (v := exprId ns (.star a)) rfl
  have heD : (C.set 0 (C 0 ++ [exprId ns (.star a)])).set 1 E.reverse = D := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;> simp [C,D,st,Lists.set]
  rw [heD] at hv
  have hm := nruns_mvAll 1 0 (by decide : (1 : Fin 4) ≠ 0) D
  have heR : (D.set 0 (D 0 ++ (D 1).reverse)).set 1 [] = R := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;> simp [D,R,st,Lists.set]
  rw [heR] at hm
  have hf := prepend_runs resumeFinish (.prim (.pop 3)) R _ 1 (nruns_prim _ _)
  have heF : (NPrim.pop 3).apply (applied resumeFinish R) =
      st ([0,m,q,exprId ns (.star a)] ++ E ++ [k]) [] [] [] := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp [resumeFinish,applied,NPrim.apply,R,st,Lists.set]
  rw [heF] at hf
  exact (hc.seq (hp.seq (hl.seq (hv.seq (hm.seq hf))))).mono (by
    simp [S,D,st,resumeFinish]; omega)

def stopFinish : List (NPrim 4) := constants 0 3 ++ constants 0 0 ++ constants 0 0 ++ [.dup 3 0 (by decide)]
def stop : NProg 4 := .seq (nclr 2) (.seq (.prim (.pop 3))
  (.seq (nclr 0) (.seq (nclr 1) (prepend stopFinish (.prim (.pop 3))))))

theorem stop_runs (q k m r a : Nat) (Q E : List Nat) (hQ : Q.length ≤ 1) :
    NRuns stop (st [0,m,q] (E.reverse ++ [a]) Q [k,r])
      (st [3,0,0,k] [] [] []) (3 * E.length + 25) := by
  let S := st [0,m,q] (E.reverse ++ [a]) Q [k,r]
  let A := st [0,m,q] (E.reverse ++ [a]) [] [k,r]
  let B := st [0,m,q] (E.reverse ++ [a]) [] [k]
  let C := st [] (E.reverse ++ [a]) [] [k]
  let R := st [] [] [] [k]
  have hc := nruns_clr 2 S
  have heA : S.set 2 [] = A := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;> simp [S,A,st,Lists.set]
  rw [heA] at hc
  have hp := nruns_pop 3 A (l := [k]) (v := r) rfl
  have heB : A.set 3 [k] = B := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;> simp [A,B,st,Lists.set]
  rw [heB] at hp
  have hd := nruns_clr 0 B
  have heC : B.set 0 [] = C := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;> simp [B,C,st,Lists.set]
  rw [heC] at hd
  have hr := nruns_clr 1 C
  have heR : C.set 1 [] = R := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;> simp [C,R,st,Lists.set]
  rw [heR] at hr
  have hf := prepend_runs stopFinish (.prim (.pop 3)) R _ 1 (nruns_prim _ _)
  have heF : (NPrim.pop 3).apply (applied stopFinish R) = st [3,0,0,k] [] [] [] := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp [stopFinish,constants,applied,NPrim.apply,R,st,Lists.set,mapTop]
  rw [heF] at hf
  exact (hc.seq (hp.seq (hd.seq (hr.seq hf)))).mono (by simp [S,B,C,st,stopFinish,constants]; omega)

def cellBound (A : Nat) : Nat := 12 + 2 * A
def stepBound (A H : Nat) : Nat := 12 * A + 3 * H + 100
def scratchSpace (A H N : Nat) : Nat := SequentialNumericBlock.scratchSpace (cellBound A) (stepBound A H) N

theorem scratchSpace_linear (A H N : Nat) :
    scratchSpace A H N = (cellBound A + stepBound A H) * N +
      (cellBound A + stepBound A H * (stepBound A H + 1) + 2) :=
  SequentialNumericBlock.scratchSpace_linear _ _ _

def successFields (ns : List CompileNode) (a : MExp) (q k m p : Nat) (E : List Nat) : List Nat :=
  if q < p then [0,m,q,exprId ns (.star a)] ++ E ++ [k] else [3,0,0,k]
def successCore (ns : List CompileNode) : NProg 4 := .seq prepare
  (.seq (NShrinkingCompare.program 2 3) (.ite 3 .pos (resume ns) stop))

theorem core_exec (ns : List CompileNode) (a : MExp) (ha : ExprOK ns a)
    (q k m p : Nat) (E : List Nat) {A N B : Nat}
    (hE : E.length ≤ 1 + 2 * A)
    (hb : ∀ v ∈ E.reverse ++ [exprId ns a,p,m,3,k+1,q], v ≤ N)
    (hspace : scratchSpace A (exprPool ns).length N ≤ B) :
    ∃ t, t ≤ 2 * stepBound A (exprPool ns).length + 4 * q + 2 ∧
      NExec (NFits B) (successCore ns)
        (st [] (E.reverse ++ [exprId ns a,p,m,3,k+1,q]) [] []) t
        (.cont (st (successFields ns a q k m p E) [] [] [])) := by
  have hq : q ≤ N := hb q (by simp)
  have hp : p ≤ N := hb p (by simp)
  have hm : m ≤ N := hb m (by simp)
  have hk : k+1 ≤ N := hb (k+1) (by simp)
  have hi : exprId ns a ≤ N := hb (exprId ns a) (by simp)
  have hn : 3 ≤ N := hb 3 (by simp)
  have henv : ∀ v ∈ E, v ≤ N := fun v hv => hb v (by simp [hv])
  have hb₀ : Bnd N (cellBound A * (N+1))
      (st [] (E.reverse ++ [exprId ns a,p,m,3,k+1,q]) [] []) := by
    apply bnd_cells
    · intro i
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi with rfl | rfl | rfl | rfl <;> simp [st,cellBound] <;> omega
    · intro i v hv
      by_cases hi : i = 1
      · exact hb v (by simpa [st,hi] using hv)
      · simp [st,hi] at hv
  have hr := (prepare_runs q k m p (exprId ns a) E).mono
    (show 12 ≤ stepBound A (exprPool ns).length by unfold stepBound; omega)
  obtain ⟨t₁,ht₁,he₁⟩ := annotate hr hb₀ hspace
  let S := st [0,m,q] (E.reverse ++ [exprId ns a]) [q] [k,p]
  let R := st [0,m,q] (E.reverse ++ [exprId ns a]) (if q ≤ p then [0] else []) [k,p-q]
  obtain ⟨t₂,ht₂,he₂⟩ := NShrinkingCompare.exec 2 3 (by decide) q p S [k] rfl rfl (end_fits he₁)
  have heq : NShrinkingCompare.result S 2 3 [k] q p = R := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;> simp [NShrinkingCompare.result,S,R,st,Lists.set]
  rw [heq] at he₂
  have hR : NFits B R := end_fits he₂
  have htest : NTest.pos.eval (R 3) = decide (q < p) := by
    simpa only [heq] using NShrinkingCompare.positive_iff S 2 3 [k] q p
  have hb₁ : Bnd N (cellBound A * (N+1)) R := by
    apply bnd_cells
    · intro i
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi with rfl | rfl | rfl | rfl <;>
        (by_cases hqp : q ≤ p) <;> simp [R,st,hqp,cellBound] <;> omega
    · intro i v hv
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi with rfl | rfl | rfl | rfl
      · simp [R,st] at hv
        rcases hv with rfl | rfl | rfl <;> omega
      · simp [R,st] at hv
        rcases hv with hv | rfl
        · exact henv v hv
        · exact hb (exprId ns a) (by simp)
      · by_cases hqp : q ≤ p <;> simp [R,st,hqp] at hv
        subst v; omega
      · simp [R,st] at hv
        rcases hv with rfl | rfl <;> omega
  have hQ : (if q ≤ p then [0] else ([] : List Nat)).length ≤ 1 := by split <;> simp
  by_cases hqp : q < p
  · have hr := (resume_runs ns a ha q k m (p-q) (if q ≤ p then [0] else []) E hQ).mono
      (show 3 * E.length + 3 * (exprPool ns).length + 20 ≤ stepBound A (exprPool ns).length by
        unfold stepBound; omega)
    obtain ⟨t₃,ht₃,he₃⟩ := annotate hr hb₁ hspace
    refine ⟨t₁+(t₂+(t₃+1)),by omega,.seqC he₁ (.seqC he₂ ?_)⟩
    simpa only [successFields,if_pos hqp] using NExec.iteT hR (by simpa [hqp] using htest) he₃
  · have hr := (stop_runs q k m (p-q) (exprId ns a) (if q ≤ p then [0] else []) E hQ).mono
      (show 3 * E.length + 25 ≤ stepBound A (exprPool ns).length by unfold stepBound; omega)
    obtain ⟨t₃,ht₃,he₃⟩ := annotate hr hb₁ hspace
    refine ⟨t₁+(t₂+(t₃+1)),by omega,.seqC he₁ (.seqC he₂ ?_)⟩
    simpa only [successFields,if_neg hqp] using NExec.iteF hR (by simpa [hqp] using htest) he₃

def basePre : List (NPrim 4) :=
  [.dup 1 3 (by decide), .pop 1, .dec 3, .pop 1, .pop 1,
    .dup 1 2 (by decide), .pop 1]
def baseFinish (s : Bool) : List (NPrim 4) := constants 0 3 ++ constants 0 0 ++
  constants 0 (if s then 2 else 0) ++ (if s then [.dup 2 0 (by decide)] else []) ++
  [.dup 3 0 (by decide), .pop 2]
def baseProgram (s : Bool) : NProg 4 := prepend basePre
  (.seq (nclr 1) (prepend (baseFinish s) (.prim (.pop 3))))

theorem base_runs (s : Bool) (k m p a : Nat) (E : List Nat) :
    NRuns (baseProgram s) (st [] (E.reverse ++ [a,p,m,3,k+1]) [] [])
      (st (if s then [3,0,2,p,k] else [3,0,0,k]) [] [] []) (3 * E.length + 40) := by
  let S := st [] (E.reverse ++ [a,p,m,3,k+1]) [] []
  let A := st [] (E.reverse ++ [a]) [p] [k]
  let R := st [] [] [p] [k]
  have hp : applied basePre S = A := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp [S,A,st,basePre,applied,NPrim.apply,mapTop,Lists.set]
  have hc := nruns_clr 1 A
  have he : A.set 1 [] = R := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;> simp [A,R,st,Lists.set]
  rw [he] at hc
  have hf := prepend_runs (baseFinish s) (.prim (.pop 3)) R _ 1 (nruns_prim _ _)
  have heF : (NPrim.pop 3).apply (applied (baseFinish s) R) =
      st (if s then [3,0,2,p,k] else [3,0,0,k]) [] [] [] := by
    cases s <;> funext i
    all_goals
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi with rfl | rfl | rfl | rfl <;>
        simp [baseFinish,constants,applied,NPrim.apply,R,st,Lists.set,mapTop]
  rw [heF] at hf
  have hall := prepend_runs basePre _ S _ _ (by rw [hp]; exact hc.seq hf)
  exact hall.mono (by cases s <;> simp [basePre,baseFinish,constants,A,st] <;> omega)

end Shallot.MacroPeg.CBV.SequentialStarReturn
