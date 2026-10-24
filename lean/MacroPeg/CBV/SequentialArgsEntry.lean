import Complexity.NCountedTransfer
import MacroPeg.CBV.SequentialNumericFive
import MacroPeg.CBV.SequentialArgHeadReturn

/-! Enter evaluation of an argument list, preserving capture environments. -/
namespace Shallot.MacroPeg.CBV.SequentialArgsEntry
open Complexity SequentialStack SequentialStackCodec CBVtoCBN
open SequentialNotReturn (prepend applied prepend_runs constants)
open SequentialNumericFive (st reg)

def inputFields (m p k : Nat) (E : CaptureEnv) (args F : List Nat) : List Nat :=
  [1,m,p] ++ writeEnv E ++ (args.length :: args) ++ [k] ++ F

def prepareOps : List (NPrim 5) :=
  [.pop 1, .pushZ 0, .dup 1 0 (by decide), .dup 1 3 (by decide), .pop 1,
    .dup 1 0 (by decide), .dup 1 3 (by decide), .pop 1,
    .dup 1 4 (by decide), .dup 1 2 (by decide), .pop 1]

def prepare : NProg 5 := .seq (nmvAll 0 1 (by decide))
  (prepend prepareOps (.seq (NCountedTransfer.counted 1 2 4 (by decide) 2) (.prim (.pop 4))))

theorem prepareOps_apply (D : List Nat) (n m p : Nat) :
    applied prepareOps (st [] (D ++ [n,p,m,1]) [] [] []) = st [0,m,p] D [n] [m,p] [n] := by
  funext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    simp [st,prepareOps,applied,NPrim.apply]

theorem prepare_runs (m p k : Nat) (E : CaptureEnv) (args F : List Nat) :
    NRuns prepare (st (inputFields m p k E args F) [] [] [] [])
      (st [0,m,p] ((args.length :: args) ++ [k] ++ F).reverse (writeEnv E) [m,p] [])
      (14 * E.length + 3 * args.length + 3 * F.length + 40) := by
  let tail := (args.length :: args) ++ [k] ++ F
  let S := st (inputFields m p k E args F) [] [] [] []
  let R := (S.set 1 (S 1 ++ (S 0).reverse)).set 0 []
  let A := st [0,m,p] (tail.reverse ++ (E.flatMap writePair).reverse) [E.length] [m,p] [E.length]
  let B := st [0,m,p] tail.reverse (writeEnv E) [m,p] [0]
  let C := st [0,m,p] tail.reverse (writeEnv E) [m,p] []
  have hr := nruns_mvAll 0 1 (by decide : (0 : Fin 5) ≠ 1) S
  have hp : applied prepareOps R = A := by
    have hR : R = st [] ((tail.reverse ++ (E.flatMap writePair).reverse) ++ [E.length,p,m,1]) [] [] [] := by
      funext i
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
      rcases hi with rfl | rfl | rfl | rfl | rfl <;>
        simp [R,S,tail,st,inputFields,writeEnv,writeList,List.reverse_append,List.append_assoc]
    rw [hR]
    exact prepareOps_apply _ _ _ _
  have hflat : ∀ es : CaptureEnv, (es.map writePair).flatten = es.flatMap writePair := by
    intro es
    induction es with
    | nil => rfl
    | cons span E ih => simp [ih]
  have hm := NCountedTransfer.counted_runs (K := 5) 1 2 4 (by decide) (by decide) (by decide)
    2 (E.map writePair) (by intro pair h; obtain ⟨span,_,rfl⟩ := List.mem_map.mp h; cases span; rfl)
    tail.reverse [E.length] [] A (by simp [A,hflat]) (by simp [A]) (by simp [A])
  have he : ((A.set 1 tail.reverse).set 2 ([E.length] ++ (E.map writePair).flatten)).set 4 [0] = B := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp [A,B,writeEnv,writeList,Lists.set,hflat]
  simp only [List.length_map,List.nil_append] at hm
  rw [he] at hm
  have hf := nruns_pop 4 B (l := []) (v := 0) rfl
  have heF : B.set 4 [] = C := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp [B,C,Lists.set]
  rw [heF] at hf
  have hall := hr.seq (prepend_runs prepareOps _ R C _ (by rw [hp]; exact hm.seq hf))
  exact hall.mono (by simp [prepareOps,S,inputFields,SequentialStackCodecBound.env_length]; omega)

def consPre : List (NPrim 5) := [.dup 1 3 (by decide), .pop 1, .dup 1 0 (by decide), .pop 1]
def startCons : NProg 5 := prepend consPre (.seq (nmvAll 2 4 (by decide))
  (NCountedTransfer.copyAll 4 0 2 (by decide) (by decide)))

theorem startCons_runs (m p k a : Nat) (env rest F : List Nat) :
    NRuns startCons (st [0,m,p] (((rest.length+1) :: a :: rest) ++ [k] ++ F).reverse env [m,p] [])
      (st ([0,m,p,a] ++ env) (rest ++ [k] ++ F).reverse env [m,p,rest.length+1] [])
      (7 * env.length + 6) := by
  let R := (rest ++ [k] ++ F).reverse
  let S := st [0,m,p] (R ++ [a,rest.length+1]) env [m,p] []
  let A := st [0,m,p,a] R env [m,p,rest.length+1] []
  let B := st [0,m,p,a] R [] [m,p,rest.length+1] env.reverse
  have hp : applied consPre S = A := by
    simp [S,A,consPre,applied,NPrim.apply]
  have hm := nruns_mvAll 2 4 (by decide : (2 : Fin 5) ≠ 4) A
  have heB : (A.set 4 (A 4 ++ (A 2).reverse)).set 2 [] = B := by simp [A,B]
  rw [heB] at hm
  have hc := NCountedTransfer.copyAll_runs 4 0 2 (by decide) (by decide) (by decide)
    env [0,m,p,a] [] B rfl rfl rfl
  have heF : ((B.set 4 []).set 0 ([0,m,p,a] ++ env)).set 2 ([] ++ env) =
      st ([0,m,p,a] ++ env) R env [m,p,rest.length+1] [] := by simp [B]
  rw [heF] at hc
  have hall := prepend_runs consPre _ S _ _ (by rw [hp]; exact hm.seq hc)
  simpa [startCons,S,R,consPre,List.reverse_append,List.append_assoc] using hall.mono (show consPre.length + (3 * (A 2).length + 1 + (4 * env.length + 1)) ≤ 7 * env.length + 6 by simp [consPre,A]; omega)

def scanCons : NProg 5 := prepend [.dec 3, .dup 3 2 (by decide)]
  (.seq (NCountedTransfer.counted 1 2 3 (by decide) 1) (.prim (.pop 3)))

theorem scanCons_runs (m p k : Nat) (D env rest F : List Nat) :
    NRuns scanCons (st D (rest ++ [k] ++ F).reverse env [m,p,rest.length+1] [])
      (st D ([k] ++ F).reverse (env ++ rest.length :: rest) [m,p] []) (6 * rest.length + 4) := by
  let S := st D (rest ++ [k] ++ F).reverse env [m,p,rest.length+1] []
  let A := st D (rest ++ [k] ++ F).reverse (env ++ [rest.length]) [m,p,rest.length] []
  let B := st D ([k] ++ F).reverse (env ++ rest.length :: rest) [m,p,0] []
  have hp : applied [.dec 3, .dup 3 2 (by decide)] S = A := by simp [S,A,applied,NPrim.apply,mapTop]
  have hflat : ∀ xs : List Nat, (xs.map (fun v => [v])).flatten = xs := by
    intro xs; induction xs with
    | nil => rfl
    | cons v xs ih => simp [ih]
  have hm := NCountedTransfer.counted_runs (K := 5) 1 2 3 (by decide) (by decide) (by decide)
    1 (rest.map (fun v => [v])) (by intro chunk h; obtain ⟨v,_,rfl⟩ := List.mem_map.mp h; rfl)
    ([k] ++ F).reverse (env ++ [rest.length]) [m,p] A
    (by simp [A,hflat,List.reverse_append,List.append_assoc]) (by simp [A]) (by simp [A])
  have heB : ((A.set 1 ([k] ++ F).reverse).set 2 ((env ++ [rest.length]) ++ (rest.map (fun v => [v])).flatten)).set 3 ([m,p] ++ [0]) = B := by
    simp [A,B,hflat,List.append_assoc]
  simp only [List.length_map] at hm
  rw [heB] at hm
  have hf := nruns_pop 3 B (l := [m,p]) (v := 0) rfl
  have heF : B.set 3 [m,p] = st D ([k] ++ F).reverse (env ++ rest.length :: rest) [m,p] [] := by simp [B]
  rw [heF] at hf
  have hall := prepend_runs [.dec 3, .dup 3 2 (by decide)] _ S _ _ (by rw [hp]; exact hm.seq hf)
  exact hall.mono (by simp; omega)


theorem mapTop_singleton (f : Nat → Nat) (v : Nat) : mapTop f [v] = [f v] := by simp [mapTop]

def finishConsPre : List (NPrim 5) :=
  [.dup 1 4 (by decide), .pop 1, .inc 4, .dup 4 0 (by decide), .pop 4] ++ constants 0 4
def finishCons : NProg 5 := prepend finishConsPre
  (.seq (nmvAll 3 4 (by decide)) (.seq (nmvAll 4 0 (by decide))
    (.seq (nmvAll 2 3 (by decide)) (.seq (nmvAll 3 0 (by decide)) (nmvAll 1 0 (by decide))))))

theorem finishCons_runs (m p k : Nat) (D env rest F : List Nat) :
    NRuns finishCons (st D ([k] ++ F).reverse (env ++ rest.length :: rest) [m,p] [])
      (st (D ++ [k+1,4,m,p] ++ env ++ (rest.length :: rest) ++ F) [] [] [] [])
      (6 * env.length + 6 * rest.length + 3 * F.length + 40) := by
  let Q := env ++ rest.length :: rest
  let S := st D ([k] ++ F).reverse Q [m,p] []
  let A := st (D ++ [k+1,4]) F.reverse Q [m,p] []
  let B := st (D ++ [k+1,4]) F.reverse Q [] [p,m]
  let C := st (D ++ [k+1,4,m,p]) F.reverse Q [] []
  let R := st (D ++ [k+1,4,m,p]) F.reverse [] Q.reverse []
  let V := st (D ++ [k+1,4,m,p] ++ Q) F.reverse [] [] []
  have hp : applied finishConsPre S = A := by
    simp [S,A,finishConsPre,constants,applied,NPrim.apply,mapTop_singleton,SequentialArgHeadReturn.mapTop_pair]
  have h₁ := nruns_mvAll 3 4 (by decide : (3 : Fin 5) ≠ 4) A
  have heB : (A.set 4 (A 4 ++ (A 3).reverse)).set 3 [] = B := by simp [A,B]
  rw [heB] at h₁
  have h₂ := nruns_mvAll 4 0 (by decide : (4 : Fin 5) ≠ 0) B
  have heC : (B.set 0 (B 0 ++ (B 4).reverse)).set 4 [] = C := by simp [B,C]
  rw [heC] at h₂
  have h₃ := nruns_mvAll 2 3 (by decide : (2 : Fin 5) ≠ 3) C
  have heR : (C.set 3 (C 3 ++ (C 2).reverse)).set 2 [] = R := by simp [C,R]
  rw [heR] at h₃
  have h₄ := nruns_mvAll 3 0 (by decide : (3 : Fin 5) ≠ 0) R
  have heV : (R.set 0 (R 0 ++ (R 3).reverse)).set 3 [] = V := by simp [R,V]
  rw [heV] at h₄
  have h₅ := nruns_mvAll 1 0 (by decide : (1 : Fin 5) ≠ 0) V
  have heF : (V.set 0 (V 0 ++ (V 1).reverse)).set 1 [] =
      st (D ++ [k+1,4,m,p] ++ env ++ (rest.length :: rest) ++ F) [] [] [] [] := by simp [V,Q,List.append_assoc]
  rw [heF] at h₅
  have hall := prepend_runs finishConsPre _ S _ _ (by rw [hp]; exact h₁.seq (h₂.seq (h₃.seq (h₄.seq h₅))))
  exact hall.mono (by simp [finishConsPre,constants,A,B,C,R,V,Q]; omega)

def nilOps : List (NPrim 5) := [.pop 1] ++ constants 0 3 ++ constants 0 1 ++ constants 0 2 ++
  [.dup 3 0 (by decide), .pop 3, .pop 3, .pushZ 0, .dup 1 0 (by decide), .pop 1]
def nilProgram : NProg 5 := .seq (nclr 0) (.seq (nclr 2) (prepend nilOps (nmvAll 1 0 (by decide))))

theorem nil_runs (m p k : Nat) (env F : List Nat) :
    NRuns nilProgram (st [0,m,p] ([0,k] ++ F).reverse env [m,p] [])
      (st ([3,1,2,p,0,k] ++ F) [] [] [] []) (2 * env.length + 3 * F.length + 40) := by
  let S := st [0,m,p] ([0,k] ++ F).reverse env [m,p] []
  let A := st [] ([0,k] ++ F).reverse env [m,p] []
  let B := st [] ([0,k] ++ F).reverse [] [m,p] []
  let C := st [3,1,2,p,0,k] F.reverse [] [] []
  have h₁ := nruns_clr 0 S
  have heA : S.set 0 [] = A := by simp [S,A]
  rw [heA] at h₁
  have h₂ := nruns_clr 2 A
  have heB : A.set 2 [] = B := by simp [A,B]
  rw [heB] at h₂
  have hp : applied nilOps B = C := by
    simp [B,C,nilOps,constants,applied,NPrim.apply,mapTop]
  have hm := nruns_mvAll 1 0 (by decide : (1 : Fin 5) ≠ 0) C
  have heF : (C.set 0 (C 0 ++ (C 1).reverse)).set 1 [] = st ([3,1,2,p,0,k] ++ F) [] [] [] [] := by simp [C]
  rw [heF] at hm
  have hall := h₁.seq (h₂.seq (prepend_runs nilOps _ B _ _ (by rw [hp]; exact hm)))
  exact hall.mono (by simp [S,A,C,nilOps,constants]; omega)


def outputFields (m p k : Nat) (E : CaptureEnv) (args F : List Nat) : List Nat :=
  match args with
  | [] => [3,1,2,p,0,k] ++ F
  | a :: rest => [0,m,p,a] ++ writeEnv E ++ [k+1,4,m,p] ++ writeEnv E ++ (rest.length :: rest) ++ F

def numeric : NProg 5 := .seq prepare
  (.ite 1 .zero nilProgram (.seq startCons (.seq scanCons finishCons)))
def localProgram : LProg 11 := numeric.compile.rename reg

theorem numeric_runs (m p k : Nat) (E : CaptureEnv) (args F : List Nat) :
    NRuns numeric (st (inputFields m p k E args F) [] [] [] [])
      (st (outputFields m p k E args F) [] [] [] [])
      (40 * E.length + 18 * args.length + 6 * F.length + 150) := by
  have hp := prepare_runs m p k E args F
  cases args with
  | nil =>
    have hn := (nil_runs m p k (writeEnv E) F).iteT
      (i := 1) (c := .zero) (p := nilProgram) (q := .seq startCons (.seq scanCons finishCons))
      (by simp [NTest.eval])
    exact (hp.seq hn).mono (by simp [SequentialStackCodecBound.env_length]; omega)
  | cons a rest =>
    have h₁ := startCons_runs m p k a (writeEnv E) rest F
    have h₂ := scanCons_runs m p k ([0,m,p,a] ++ writeEnv E) (writeEnv E) rest F
    have h₃ := finishCons_runs m p k ([0,m,p,a] ++ writeEnv E) (writeEnv E) rest F
    have hseq := h₁.seq (h₂.seq h₃)
    have hn := hseq.iteF (i := 1) (c := .zero) (p := nilProgram) (by
      change NTest.zero.eval (((rest.length+1) :: a :: rest) ++ [k] ++ F).reverse = false
      have ht : (((rest.length+1) :: a :: rest) ++ [k] ++ F).reverse =
          ((rest ++ [k] ++ F).reverse ++ [a]) ++ [rest.length+1] := by
        simp [List.reverse_append,List.append_assoc]
      rw [ht]
      simp only [NTest.eval,List.getLast?_concat]
      simp)
    have hr := hp.seq hn
    have he : (([0,m,p,a] ++ writeEnv E) ++ [k+1,4,m,p] ++ writeEnv E ++ (rest.length :: rest) ++ F) =
        outputFields m p k E (a :: rest) F := by simp [outputFields,List.append_assoc]
    rw [he] at hr
    exact hr.mono (by simp [SequentialStackCodecBound.env_length]; omega)

def cellBound (A : Nat) : Nat := 13 + 6 * A
def stepBound (A : Nat) : Nat := 80 * A + 200
def scratchSpace (A N : Nat) : Nat := SequentialNumericFive.scratchSpace (cellBound A) (stepBound A) N

theorem scratchSpace_linear (A N : Nat) :
    scratchSpace A N = (cellBound A + stepBound A) * N +
      (cellBound A + stepBound A * (stepBound A + 1) + 2) :=
  SequentialNumericFive.scratchSpace_linear _ _ _

theorem local_runs (m p k : Nat) (E : CaptureEnv) (args F : List Nat) {A N B width held : Nat} (tail : List Bool)
    (hE : E.length ≤ A) (ha : args.length ≤ A) (hF : F.length ≤ 6 + 3 * A)
    (hb : ∀ v ∈ inputFields m p k E args F, v ≤ N) (hspace : scratchSpace A N ≤ B)
    (hR : LenOK B (SequentialFieldFetch.start width [] tail
      (SequentialFrontRead.locals (inputFields m p k E args F)) held [])) :
    Complexity.Runs (LenOK B) localProgram
      (SequentialFieldFetch.start width [] tail (SequentialFrontRead.locals (inputFields m p k E args F)) held [])
      (SequentialFieldFetch.start width [] tail (SequentialFrontRead.locals (outputFields m p k E args F)) held [])
      (stepBound A * ncost B) := by
  have hlen : (inputFields m p k E args F).length ≤ cellBound A := by
    simp [inputFields,SequentialStackCodecBound.env_length,cellBound]; omega
  have hr := (numeric_runs m p k E args F).mono (show
    40 * E.length + 18 * args.length + 6 * F.length + 150 ≤ stepBound A by unfold stepBound; omega)
  exact SequentialNumericFive.local_runs numeric _ _ tail hr hlen hb hspace hR


theorem exprs_code (ns : List CompileNode) (es : List MExp) :
    writeExprs ns es = es.length :: es.map (exprId ns) := by
  induction es with
  | nil => rfl
  | cons a es ih => simp_all [writeExprs,writeList,writeExpr]

def localNext (m p : Nat) (E : CaptureEnv) (es : List MExp) (frames : List SequentialStack.Frame) : Config :=
  match es with
  | [] => ⟨.value (.args (some (some ([],p)))),frames⟩
  | a :: es => ⟨.expr m E a p,.argHead m E es p :: frames⟩

theorem original_step (g : MGrammar) (x : List Char) (m p : Nat) (E : CaptureEnv) (es : List MExp)
    (K : List SequentialStack.Frame) :
    step g x ⟨.args m E es p,K⟩ = some (localNext m p E es K) := by cases es <;> rfl

theorem input_prefix (ns : List CompileNode) (m p : Nat) (E : CaptureEnv) (es : List MExp)
    (K frames : List SequentialStack.Frame) :
    SequentialFront.prefixCode ns K ⟨.args m E es p,frames⟩ =
      inputFields m p (frames.length + K.length) E (es.map (exprId ns))
        (SequentialFront.suffixCode ns frames) := by
  simp [SequentialFront.prefixCode,inputFields,writeTask,exprs_code,List.append_assoc]

theorem output_prefix (ns : List CompileNode) (m p : Nat) (E : CaptureEnv) (es : List MExp)
    (K frames : List SequentialStack.Frame) :
    SequentialFront.prefixCode ns K (localNext m p E es frames) =
      outputFields m p (frames.length + K.length) E (es.map (exprId ns))
        (SequentialFront.suffixCode ns frames) := by
  cases es <;> simp [SequentialFront.prefixCode,SequentialFront.suffixCode,outputFields,
    localNext,writeTask,writeValue,writeArgsRes,writeEnv,writeList,writeFrame,exprs_code,writeExpr,List.append_assoc,Nat.add_assoc,Nat.add_comm]

end Shallot.MacroPeg.CBV.SequentialArgsEntry
