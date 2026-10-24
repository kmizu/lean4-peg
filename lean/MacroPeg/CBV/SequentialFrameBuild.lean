import MacroPeg.CBV.SequentialNumericFive

/-! Build a continuation frame while preserving the surrounding field stream. -/
namespace Shallot.MacroPeg.CBV.SequentialFrameBuild
open Complexity
open SequentialNotReturn (prepend applied prepend_runs)
open SequentialNumericFive (st)

inductive Mode where | seq | alt | notP | star

def tag : Mode → Nat | .seq => 0 | .alt => 1 | .notP => 2 | .star => 3

def tailFields (mode : Mode) (m p b : Nat) (env : List Nat) : List Nat :=
  match mode with
  | .seq => [m,b] ++ env
  | .alt | .star => [m,p,b] ++ env
  | .notP => [p]
def fields (mode : Mode) (m p b : Nat) (env : List Nat) : List Nat := tag mode :: tailFields mode m p b env

def keepEnv : NProg 5 := .seq (nmvAll 2 4 (by decide))
  (.seq (nmvAll 4 0 (by decide)) (nmvAll 1 0 (by decide)))

theorem keepEnv_runs (D env F : List Nat) :
    NRuns keepEnv (st D F.reverse env [] []) (st (D ++ env ++ F) [] [] [] [])
      (6 * env.length + 3 * F.length + 3) := by
  let S := st D F.reverse env [] []
  let A := st D F.reverse [] [] env.reverse
  let B := st (D ++ env) F.reverse [] [] []
  have h₁ := nruns_mvAll 2 4 (by decide : (2 : Fin 5) ≠ 4) S
  have hA : (S.set 4 (S 4 ++ (S 2).reverse)).set 2 [] = A := by simp [S,A]
  rw [hA] at h₁
  have h₂ := nruns_mvAll 4 0 (by decide : (4 : Fin 5) ≠ 0) A
  have hB : (A.set 0 (A 0 ++ (A 4).reverse)).set 4 [] = B := by simp [A,B]
  rw [hB] at h₂
  have h₃ := nruns_mvAll 1 0 (by decide : (1 : Fin 5) ≠ 0) B
  have hF : (B.set 0 (B 0 ++ (B 1).reverse)).set 1 [] = st (D ++ env ++ F) [] [] [] [] := by simp [B]
  rw [hF] at h₃
  exact (h₁.seq (h₂.seq h₃)).mono (by simp [S,A,B]; omega)

def seqPre : List (NPrim 5) := [.pop 3, .dup 3 0 (by decide), .pop 3]
def seqProgram (b : Nat) : NProg 5 := prepend seqPre (.seq (npushC 0 b) keepEnv)
def bothProgram (b : Nat) : NProg 5 := .seq (nmvAll 3 4 (by decide))
  (.seq (nmvAll 4 0 (by decide)) (.seq (npushC 0 b) keepEnv))
def notProgram : NProg 5 := .seq (.prim (.dup 3 0 (by decide)))
  (.seq (nclr 3) (.seq (nclr 2) (nmvAll 1 0 (by decide))))

theorem seq_runs (m p b : Nat) (D env F : List Nat) :
    NRuns (seqProgram b) (st D F.reverse env [m,p] [])
      (st (D ++ [m,b] ++ env ++ F) [] [] [] []) (6 * env.length + 3 * F.length + b + 10) := by
  let S := st D F.reverse env [m,p] []
  let A := st (D ++ [m]) F.reverse env [] []
  have hp : applied seqPre S = A := by simp [S,A,seqPre,applied,NPrim.apply]
  have hc := nruns_pushC 0 A b
  have hB : A.set 0 (A 0 ++ [b]) = st (D ++ [m,b]) F.reverse env [] [] := by simp [A]
  rw [hB] at hc
  have hall := prepend_runs seqPre _ S _ _ (by rw [hp]; exact hc.seq (keepEnv_runs (D ++ [m,b]) env F))
  exact hall.mono (by simp [seqPre]; omega)

theorem both_runs (m p b : Nat) (D env F : List Nat) :
    NRuns (bothProgram b) (st D F.reverse env [m,p] [])
      (st (D ++ [m,p,b] ++ env ++ F) [] [] [] []) (6 * env.length + 3 * F.length + b + 20) := by
  let S := st D F.reverse env [m,p] []
  let A := st D F.reverse env [] [p,m]
  let B := st (D ++ [m,p]) F.reverse env [] []
  have h₁ := nruns_mvAll 3 4 (by decide : (3 : Fin 5) ≠ 4) S
  have hA : (S.set 4 (S 4 ++ (S 3).reverse)).set 3 [] = A := by simp [S,A]
  rw [hA] at h₁
  have h₂ := nruns_mvAll 4 0 (by decide : (4 : Fin 5) ≠ 0) A
  have hB : (A.set 0 (A 0 ++ (A 4).reverse)).set 4 [] = B := by simp [A,B]
  rw [hB] at h₂
  have hc := nruns_pushC 0 B b
  have hC : B.set 0 (B 0 ++ [b]) = st (D ++ [m,p,b]) F.reverse env [] [] := by simp [B]
  rw [hC] at hc
  exact (h₁.seq (h₂.seq (hc.seq (keepEnv_runs (D ++ [m,p,b]) env F)))).mono (by simp [S,A]; omega)

theorem not_runs (m p : Nat) (D env F : List Nat) :
    NRuns notProgram (st D F.reverse env [m,p] [])
      (st (D ++ [p] ++ F) [] [] [] []) (2 * env.length + 3 * F.length + 10) := by
  let S := st D F.reverse env [m,p] []
  let A := st (D ++ [p]) F.reverse env [m,p] []
  let B := st (D ++ [p]) F.reverse env [] []
  let C := st (D ++ [p]) F.reverse [] [] []
  have hp := nruns_dup 3 0 (by decide : (3 : Fin 5) ≠ 0) S (l := [m]) (v := p) rfl
  have hA : S.set 0 (S 0 ++ [p]) = A := by simp [S,A]
  rw [hA] at hp
  have h₁ := nruns_clr 3 A
  have hB : A.set 3 [] = B := by simp [A,B]
  rw [hB] at h₁
  have h₂ := nruns_clr 2 B
  have hC : B.set 2 [] = C := by simp [B,C]
  rw [hC] at h₂
  have hm := nruns_mvAll 1 0 (by decide : (1 : Fin 5) ≠ 0) C
  have hF : (C.set 0 (C 0 ++ (C 1).reverse)).set 1 [] = st (D ++ [p] ++ F) [] [] [] [] := by simp [C]
  rw [hF] at hm
  exact (hp.seq (h₁.seq (h₂.seq hm))).mono (by simp [A,B,C]; omega)

def body (mode : Mode) (b : Nat) : NProg 5 :=
  match mode with | .seq => seqProgram b | .alt | .star => bothProgram b | .notP => notProgram

def program (mode : Mode) (b : Nat) : NProg 5 := .seq (npushC 0 (tag mode)) (body mode b)

theorem runs (mode : Mode) (m p b : Nat) (D env F : List Nat) :
    NRuns (program mode b) (st D F.reverse env [m,p] [])
      (st (D ++ fields mode m p b env ++ F) [] [] [] [])
      (8 * env.length + 3 * F.length + 2*b + 50) := by
  have hp := nruns_pushC 0 (st D F.reverse env [m,p] []) (tag mode)
  have hA : (st D F.reverse env [m,p] []).set 0 ((st D F.reverse env [m,p] []) 0 ++ [tag mode]) =
      st (D ++ [tag mode]) F.reverse env [m,p] [] := by simp
  rw [hA] at hp
  cases mode with
  | seq => simpa [program,body,fields,tailFields,tag,List.append_assoc] using
      (hp.seq (seq_runs m p b (D ++ [0]) env F)).mono (by simp [tag]; omega)
  | alt => simpa [program,body,fields,tailFields,tag,List.append_assoc] using
      (hp.seq (both_runs m p b (D ++ [1]) env F)).mono (by simp [tag]; omega)
  | notP => simpa [program,body,fields,tailFields,tag,List.append_assoc] using
      (hp.seq (not_runs m p (D ++ [2]) env F)).mono (by simp [tag]; omega)
  | star => simpa [program,body,fields,tailFields,tag,List.append_assoc] using
      (hp.seq (both_runs m p b (D ++ [3]) env F)).mono (by simp [tag]; omega)
end Shallot.MacroPeg.CBV.SequentialFrameBuild
