import MacroPeg.CBV.SequentialArgsEntry
import MacroPeg.CBV.SequentialRuleLookup

/-! Enter a rule body with a decremented clock, preserving captures and position. -/
namespace Shallot.MacroPeg.CBV.SequentialQueryEntry
open Complexity SequentialStack SequentialStackCodec SequentialStackPool CBVtoCBN
open SequentialNotReturn (prepend applied prepend_runs constants)
open SequentialNumericFive (st reg)

def inputFields (m i p k : Nat) (E : CaptureEnv) (F : List Nat) : List Nat :=
  [2,m,i,p] ++ writeEnv E ++ [k] ++ F

def prepareOps : List (NPrim 5) :=
  [.pop 1, .dup 1 3 (by decide), .pop 1, .dup 1 3 (by decide), .pop 1,
    .dup 1 3 (by decide), .pop 1, .dup 1 4 (by decide), .dup 1 2 (by decide), .pop 1]

def prepare : NProg 5 := .seq (nmvAll 0 1 (by decide))
  (prepend prepareOps (.seq (NCountedTransfer.counted 1 2 4 (by decide) 2) (.seq (.prim (.pop 4)) (nmvAll 3 4 (by decide)))))

theorem prepareOps_apply (D : List Nat) (n m i p : Nat) :
    applied prepareOps (st [] (D ++ [n,p,i,m,2]) [] [] []) = st [] D [n] [m,i,p] [n] := by
  funext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    simp [st,prepareOps,applied,NPrim.apply]

theorem prepare_runs (m i p k : Nat) (E : CaptureEnv) (F : List Nat) :
    NRuns prepare (st (inputFields m i p k E F) [] [] [] [])
      (st [] ([k] ++ F).reverse (writeEnv E) [] [p,i,m])
      (14 * E.length + 3 * F.length + 50) := by
  let tail := [k] ++ F
  let S := st (inputFields m i p k E F) [] [] [] []
  let R := (S.set 1 (S 1 ++ (S 0).reverse)).set 0 []
  let A := st [] (tail.reverse ++ (E.flatMap writePair).reverse) [E.length] [m,i,p] [E.length]
  let B := st [] tail.reverse (writeEnv E) [m,i,p] [0]
  let C := st [] tail.reverse (writeEnv E) [m,i,p] []
  have hr := nruns_mvAll 0 1 (by decide : (0 : Fin 5) ≠ 1) S
  have hp : applied prepareOps R = A := by
    have hR : R = st [] ((tail.reverse ++ (E.flatMap writePair).reverse) ++ [E.length,p,i,m,2]) [] [] [] := by
      funext i
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
      rcases hi with rfl | rfl | rfl | rfl | rfl <;>
        simp [R,S,tail,st,inputFields,writeEnv,writeList,List.reverse_append,List.append_assoc]
    rw [hR]
    exact prepareOps_apply _ _ _ _ _
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
  have hmeta := nruns_mvAll 3 4 (by decide : (3 : Fin 5) ≠ 4) C
  have heV : (C.set 4 (C 4 ++ (C 3).reverse)).set 3 [] =
      st [] tail.reverse (writeEnv E) [] [p,i,m] := by simp [C]
  rw [heV] at hmeta
  have hall := hr.seq (prepend_runs prepareOps _ R _ _ (by rw [hp]; exact hm.seq (hf.seq hmeta)))
  exact hall.mono (by simp [prepareOps,S,C,inputFields,SequentialStackCodecBound.env_length]; omega)

def resumePre : List (NPrim 5) := [.dec 4, .pushZ 0, .dup 4 0 (by decide), .pop 4]
def resumePost : List (NPrim 5) :=
  [.dup 4 3 (by decide), .pop 4, .dup 4 0 (by decide), .pop 4, .dup 3 0 (by decide), .pop 3]
def finishPre : List (NPrim 5) := [.dup 1 0 (by decide), .pop 1]
def resume (ns : List CompileNode) (g : MGrammar) : NProg 5 := prepend resumePre
  (.seq (SequentialRuleLookup.program 4 ns g) (prepend resumePost
    (.seq (nmvAll 2 3 (by decide)) (.seq (nmvAll 3 0 (by decide))
      (prepend finishPre (nmvAll 1 0 (by decide)))))))

theorem resume_runs (ns : List CompileNode) (g : MGrammar) (i : Nat) (r : MRule)
    (hr : ruleAtM g.rules i = some r) (m p k : Nat) (env F : List Nat) :
    NRuns (resume ns g) (st [] ([k] ++ F).reverse env [] [p,i,m+1])
      (st ([0,m,p,exprId ns r.body] ++ env ++ [k] ++ F) [] [] [] [])
      (6 * env.length + 3 * F.length + 2 * g.rules.length + (exprPool ns).length + 30) := by
  let S := st [] ([k] ++ F).reverse env [] [p,i,m+1]
  let A := st [0,m] ([k] ++ F).reverse env [] [p,i]
  let B := st [0,m] ([k] ++ F).reverse env [] [p,exprId ns r.body]
  let C := st [0,m,p,exprId ns r.body] ([k] ++ F).reverse env [] []
  let R := st [0,m,p,exprId ns r.body] ([k] ++ F).reverse [] env.reverse []
  let V := st ([0,m,p,exprId ns r.body] ++ env) ([k] ++ F).reverse [] [] []
  let W := st ([0,m,p,exprId ns r.body] ++ env ++ [k]) F.reverse [] [] []
  have hp : applied resumePre S = A := by simp [S,A,resumePre,applied,NPrim.apply,mapTop]
  have hl := SequentialRuleLookup.runs 4 ns g i r hr A [p] rfl
  have heB : A.set 4 ([p] ++ [exprId ns r.body]) = B := by simp [A,B]
  rw [heB] at hl
  have hpost : applied resumePost B = C := by simp [B,C,resumePost,applied,NPrim.apply]
  have h₁ := nruns_mvAll 2 3 (by decide : (2 : Fin 5) ≠ 3) C
  have heR : (C.set 3 (C 3 ++ (C 2).reverse)).set 2 [] = R := by simp [C,R]
  rw [heR] at h₁
  have h₂ := nruns_mvAll 3 0 (by decide : (3 : Fin 5) ≠ 0) R
  have heV : (R.set 0 (R 0 ++ (R 3).reverse)).set 3 [] = V := by simp [R,V]
  rw [heV] at h₂
  have hfinish : applied finishPre V = W := by
    simp [V,W,finishPre,applied,NPrim.apply]
  have h₃ := nruns_mvAll 1 0 (by decide : (1 : Fin 5) ≠ 0) W
  have heF : (W.set 0 (W 0 ++ (W 1).reverse)).set 1 [] =
      st ([0,m,p,exprId ns r.body] ++ env ++ [k] ++ F) [] [] [] [] := by simp [W,List.append_assoc]
  rw [heF] at h₃
  have htail := prepend_runs resumePost _ B _ _ (by
    rw [hpost]
    exact h₁.seq (h₂.seq (prepend_runs finishPre _ V _ _ (by rw [hfinish]; exact h₃))))
  have hall := prepend_runs resumePre _ S _ _ (by rw [hp]; exact hl.seq htail)
  exact hall.mono (by simp [resumePre,resumePost,finishPre,C,R,W]; omega)

def nilOps : List (NPrim 5) := constants 0 3 ++ constants 0 0 ++ constants 0 0 ++
  [.dup 1 0 (by decide), .pop 1]
def nilProgram : NProg 5 := .seq (nclr 4) (.seq (nclr 2) (prepend nilOps (nmvAll 1 0 (by decide))))

theorem nil_runs (i p k : Nat) (env F : List Nat) :
    NRuns nilProgram (st [] ([k] ++ F).reverse env [] [p,i,0])
      (st ([3,0,0,k] ++ F) [] [] [] []) (2 * env.length + 3 * F.length + 30) := by
  let S := st [] ([k] ++ F).reverse env [] [p,i,0]
  let A := st [] ([k] ++ F).reverse env [] []
  let B := st [] ([k] ++ F).reverse [] [] []
  let C := st [3,0,0,k] F.reverse [] [] []
  have h₁ := nruns_clr 4 S
  have heA : S.set 4 [] = A := by simp [S,A]
  rw [heA] at h₁
  have h₂ := nruns_clr 2 A
  have heB : A.set 2 [] = B := by simp [A,B]
  rw [heB] at h₂
  have hp : applied nilOps B = C := by simp [B,C,nilOps,constants,applied,NPrim.apply,mapTop]
  have hm := nruns_mvAll 1 0 (by decide : (1 : Fin 5) ≠ 0) C
  have heF : (C.set 0 (C 0 ++ (C 1).reverse)).set 1 [] = st ([3,0,0,k] ++ F) [] [] [] [] := by simp [C]
  rw [heF] at hm
  have hall := h₁.seq (h₂.seq (prepend_runs nilOps _ B _ _ (by rw [hp]; exact hm)))
  exact hall.mono (by simp [S,A,C,nilOps,constants]; omega)

def outputFields (ns : List CompileNode) (r : MRule) (m p k : Nat) (E : CaptureEnv) (F : List Nat) : List Nat :=
  match m with
  | 0 => [3,0,0,k] ++ F
  | m+1 => [0,m,p,exprId ns r.body] ++ writeEnv E ++ [k] ++ F

def numeric (ns : List CompileNode) (g : MGrammar) : NProg 5 :=
  .seq prepare (.ite 4 .zero nilProgram (resume ns g))
def localProgram (ns : List CompileNode) (g : MGrammar) : LProg 11 := (numeric ns g).compile.rename reg

theorem numeric_runs (ns : List CompileNode) (g : MGrammar) (i : Nat) (r : MRule)
    (hr : ruleAtM g.rules i = some r) (m p k : Nat) (E : CaptureEnv) (F : List Nat) :
    NRuns (numeric ns g) (st (inputFields m i p k E F) [] [] [] [])
      (st (outputFields ns r m p k E F) [] [] [] [])
      (30 * E.length + 6 * F.length + 2 * g.rules.length + (exprPool ns).length + 100) := by
  have hp := prepare_runs m i p k E F
  cases m with
  | zero =>
    have hn := (nil_runs i p k (writeEnv E) F).iteT (i := 4) (c := .zero) (p := nilProgram) (q := resume ns g)
      (by simp [NTest.eval])
    exact (hp.seq hn).mono (by simp [SequentialStackCodecBound.env_length]; omega)
  | succ m =>
    have hn := (resume_runs ns g i r hr m p k (writeEnv E) F).iteF (i := 4) (c := .zero) (p := nilProgram)
      (by simp [NTest.eval])
    exact (hp.seq hn).mono (by simp [SequentialStackCodecBound.env_length]; omega)

def cellBound (A : Nat) : Nat := 13 + 6*A
def stepBound (A R H : Nat) : Nat := 60*A + 3*R + H + 200
def scratchSpace (A R H N : Nat) : Nat := SequentialNumericFive.scratchSpace (cellBound A) (stepBound A R H) N

theorem scratchSpace_linear (A R H N : Nat) :
    scratchSpace A R H N = (cellBound A + stepBound A R H) * N +
      (cellBound A + stepBound A R H * (stepBound A R H + 1) + 2) :=
  SequentialNumericFive.scratchSpace_linear _ _ _

theorem local_runs (ns : List CompileNode) (g : MGrammar) (i : Nat) (r : MRule)
    (hr : ruleAtM g.rules i = some r) (m p k : Nat) (E : CaptureEnv) (F : List Nat)
    {A N B width held : Nat} (tail : List Bool) (hE : E.length ≤ A) (hF : F.length ≤ 6+3*A)
    (hb : ∀ v ∈ inputFields m i p k E F, v ≤ N) (hspace : scratchSpace A g.rules.length (exprPool ns).length N ≤ B)
    (hR : LenOK B (SequentialFieldFetch.start width [] tail (SequentialFrontRead.locals (inputFields m i p k E F)) held [])) :
    Complexity.Runs (LenOK B) (localProgram ns g)
      (SequentialFieldFetch.start width [] tail (SequentialFrontRead.locals (inputFields m i p k E F)) held [])
      (SequentialFieldFetch.start width [] tail (SequentialFrontRead.locals (outputFields ns r m p k E F)) held [])
      (stepBound A g.rules.length (exprPool ns).length * ncost B) := by
  have hlen : (inputFields m i p k E F).length ≤ cellBound A := by
    simp [inputFields,SequentialStackCodecBound.env_length,cellBound]; omega
  have hrun := (numeric_runs ns g i r hr m p k E F).mono (show
    30*E.length + 6*F.length + 2*g.rules.length + (exprPool ns).length + 100 ≤
      stepBound A g.rules.length (exprPool ns).length by unfold stepBound; omega)
  exact SequentialNumericFive.local_runs (numeric ns g) _ _ tail hrun hlen hb hspace hR

def nextTask (g : MGrammar) (m i p : Nat) (E : CaptureEnv) : Task :=
  match m with
  | 0 => .value (.expr none)
  | m+1 => match ruleAtM g.rules i with
    | none => .value (.expr none)
    | some r => .expr m E r.body p

def localNext (g : MGrammar) (m i p : Nat) (E : CaptureEnv) (frames : List SequentialStack.Frame) : Config :=
  ⟨nextTask g m i p E,frames⟩

theorem original_step (g : MGrammar) (x : List Char) (m i p : Nat) (E : CaptureEnv)
    (K : List SequentialStack.Frame) (hp : p ≤ x.length) :
    step g x ⟨.query m i E p,K⟩ = some (localNext g m i p E K) := by
  cases m with
  | zero => rfl
  | succ m => cases hr : ruleAtM g.rules i <;> simp [step,localNext,nextTask,hp,hr]

theorem input_prefix (ns : List CompileNode) (m i p : Nat) (E : CaptureEnv)
    (K frames : List SequentialStack.Frame) :
    SequentialFront.prefixCode ns K ⟨.query m i E p,frames⟩ =
      inputFields m i p (frames.length + K.length) E (SequentialFront.suffixCode ns frames) := by
  simp [SequentialFront.prefixCode,inputFields,writeTask,List.append_assoc]

theorem output_prefix (ns : List CompileNode) (g : MGrammar) (i : Nat) (r : MRule)
    (hr : ruleAtM g.rules i = some r) (m p : Nat) (E : CaptureEnv)
    (K frames : List SequentialStack.Frame) :
    SequentialFront.prefixCode ns K (localNext g m i p E frames) =
      outputFields ns r m p (frames.length + K.length) E (SequentialFront.suffixCode ns frames) := by
  cases m <;> simp [SequentialFront.prefixCode,outputFields,localNext,nextTask,hr,
    writeTask,writeValue,writeRes,writeExpr,List.append_assoc]

end Shallot.MacroPeg.CBV.SequentialQueryEntry
