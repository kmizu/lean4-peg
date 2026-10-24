import MacroPeg.CBV.SequentialFrameBuild
import MacroPeg.CBV.SequentialArgsEntry

/-! Enter sequence, choice, lookahead and repetition from source expression IDs. -/
namespace Shallot.MacroPeg.CBV.SequentialStructuralEntry
open Complexity SequentialStack SequentialStackCodec SequentialStackPool CBVtoCBN
open SequentialNotReturn (prepend applied prepend_runs)
open SequentialNumericFive (st reg)
open SequentialFrameBuild (Mode)

def inputFields (m p eid k : Nat) (E : CaptureEnv) (F : List Nat) : List Nat :=
  [0,m,p,eid] ++ writeEnv E ++ [k] ++ F

def headOps : List (NPrim 5) := [.pop 1,.pushZ 0,.dup 1 0 (by decide),.dup 1 3 (by decide),.pop 1,
  .dup 1 0 (by decide),.dup 1 3 (by decide),.pop 1]
def readHead : NProg 5 := .seq (nmvAll 0 1 (by decide)) (prepend headOps (nskip 4))

theorem headOps_apply (D : List Nat) (m p eid : Nat) :
    applied headOps (st [] (D ++ [eid,p,m,0]) [] [] []) = st [0,m,p] (D ++ [eid]) [] [m,p] [] := by
  simp [headOps,applied,NPrim.apply]

theorem readHead_runs (m p eid k : Nat) (E : CaptureEnv) (F : List Nat) :
    NRuns readHead (st (inputFields m p eid k E F) [] [] [] [])
      (st [0,m,p] ((writeEnv E ++ [k] ++ F).reverse ++ [eid]) [] [m,p] [])
      (6*E.length + 3*F.length + 35) := by
  let S := st (inputFields m p eid k E F) [] [] [] []
  let R := (S.set 1 (S 1 ++ (S 0).reverse)).set 0 []
  let A := st [0,m,p] ((writeEnv E ++ [k] ++ F).reverse ++ [eid]) [] [m,p] []
  have hr := nruns_mvAll 0 1 (by decide : (0 : Fin 5) ≠ 1) S
  have hp : applied headOps R = A := by
    have he : R = st [] ((writeEnv E ++ [k] ++ F).reverse ++ [eid,p,m,0]) [] [] [] := by
      simp [R,S,inputFields,List.reverse_append,List.append_assoc]
    rw [he]
    exact headOps_apply _ _ _ _
  have hall := hr.seq (prepend_runs headOps _ R A 2 (by rw [hp]; exact nruns_skip 4 A))
  exact hall.mono (by simp [headOps,S,inputFields,SequentialStackCodecBound.env_length]; omega)

def capturePre : List (NPrim 5) := [.dup 1 4 (by decide),.dup 1 2 (by decide),.pop 1]
def capture : NProg 5 := prepend capturePre
  (.seq (NCountedTransfer.counted 1 2 4 (by decide) 2) (.seq (.prim (.pop 4))
    (.seq (nmvAll 2 4 (by decide)) (NCountedTransfer.copyAll 4 0 2 (by decide) (by decide)))))

theorem capture_runs (m p k : Nat) (D : List Nat) (E : CaptureEnv) (F : List Nat) :
    NRuns capture (st D (writeEnv E ++ [k] ++ F).reverse [] [m,p] [])
      (st (D ++ writeEnv E) ([k] ++ F).reverse (writeEnv E) [m,p] [])
      (8*E.length + 7*(writeEnv E).length + 10) := by
  let R := ([k] ++ F).reverse
  let S := st D (writeEnv E ++ [k] ++ F).reverse [] [m,p] []
  let A := st D (R ++ (E.flatMap writePair).reverse) [E.length] [m,p] [E.length]
  let B := st D R (writeEnv E) [m,p] [0]
  let C := st D R (writeEnv E) [m,p] []
  let V := st D R [] [m,p] (writeEnv E).reverse
  have hflat : ∀ es : CaptureEnv, (es.map writePair).flatten = es.flatMap writePair := by
    intro es; induction es with
    | nil => rfl
    | cons span es ih => simp [ih]
  have hp : applied capturePre S = A := by
    have he : S = st D ((R ++ (E.flatMap writePair).reverse) ++ [E.length]) [] [m,p] [] := by
      simp [S,R,writeEnv,writeList,List.reverse_append,List.append_assoc]
    rw [he]
    simp [A,capturePre,applied,NPrim.apply,List.append_assoc]
  have hc := NCountedTransfer.counted_runs (K := 5) 1 2 4 (by decide) (by decide) (by decide)
    2 (E.map writePair) (by intro chunk h; obtain ⟨span,_,rfl⟩ := List.mem_map.mp h; cases span; rfl)
    R [E.length] [] A (by simp [A,hflat]) (by simp [A]) (by simp [A])
  have heB : ((A.set 1 R).set 2 ([E.length] ++ (E.map writePair).flatten)).set 4 ([] ++ [0]) = B := by
    simp [A,B,writeEnv,writeList,hflat]
  rw [heB] at hc
  have hpop := nruns_pop 4 B (l := []) (v := 0) rfl
  have heC : B.set 4 [] = C := by simp [B,C]
  rw [heC] at hpop
  have hm := nruns_mvAll 2 4 (by decide : (2 : Fin 5) ≠ 4) C
  have heV : (C.set 4 (C 4 ++ (C 2).reverse)).set 2 [] = V := by simp [C,V]
  rw [heV] at hm
  have hcopy := NCountedTransfer.copyAll_runs 4 0 2 (by decide) (by decide) (by decide)
    (writeEnv E) D [] V rfl rfl rfl
  have heF : ((V.set 4 []).set 0 (D ++ writeEnv E)).set 2 ([] ++ writeEnv E) =
      st (D ++ writeEnv E) R (writeEnv E) [m,p] [] := by simp [V]
  rw [heF] at hcopy
  have hall := prepend_runs capturePre _ S _ _ (by rw [hp]; exact hc.seq (hpop.seq (hm.seq hcopy)))
  exact hall.mono (by simp [capturePre,C]; omega)

def headerOps : List (NPrim 5) := [.dup 1 4 (by decide),.pop 1,.inc 4,.dup 4 0 (by decide),.pop 4]
def header : NProg 5 := prepend headerOps (nskip 4)

theorem header_runs (m p k : Nat) (D env F : List Nat) :
    NRuns header (st D ([k] ++ F).reverse env [m,p] [])
      (st (D ++ [k+1]) F.reverse env [m,p] []) 7 := by
  let S := st D ([k] ++ F).reverse env [m,p] []
  let A := st (D ++ [k+1]) F.reverse env [m,p] []
  have hp : applied headerOps S = A := by simp [S,A,headerOps,applied,NPrim.apply,SequentialArgsEntry.mapTop_singleton]
  exact prepend_runs headerOps _ S A 2 (by rw [hp]; exact nruns_skip 4 A)

def body (mode : Mode) (a b : Nat) : NProg 5 := .seq (npushC 0 a)
  (.seq capture (.seq header (SequentialFrameBuild.program mode b)))

def outputFields (mode : Mode) (m p a b k : Nat) (E : CaptureEnv) (F : List Nat) : List Nat :=
  [0,m,p,a] ++ writeEnv E ++ [k+1] ++ SequentialFrameBuild.fields mode m p b (writeEnv E) ++ F

theorem body_runs (mode : Mode) (m p a b k : Nat) (E : CaptureEnv) (F : List Nat) :
    NRuns (body mode a b) (st [0,m,p] (writeEnv E ++ [k] ++ F).reverse [] [m,p] [])
      (st (outputFields mode m p a b k E F) [] [] [] [])
      (40*E.length + 3*F.length + a + 2*b + 100) := by
  let S := st [0,m,p] (writeEnv E ++ [k] ++ F).reverse [] [m,p] []
  have ha := nruns_pushC 0 S a
  have heA : S.set 0 (S 0 ++ [a]) = st [0,m,p,a] (writeEnv E ++ [k] ++ F).reverse [] [m,p] [] := by simp [S]
  rw [heA] at ha
  have hc := capture_runs m p k [0,m,p,a] E F
  have hh := header_runs m p k ([0,m,p,a] ++ writeEnv E) (writeEnv E) F
  have hf := SequentialFrameBuild.runs mode m p b (([0,m,p,a] ++ writeEnv E) ++ [k+1]) (writeEnv E) F
  have heF : (([0,m,p,a] ++ writeEnv E) ++ [k+1]) ++ SequentialFrameBuild.fields mode m p b (writeEnv E) ++ F =
      outputFields mode m p a b k E F := by simp [outputFields,List.append_assoc]
  rw [heF] at hf
  exact (ha.seq (hc.seq (hh.seq hf))).mono (by simp [SequentialStackCodecBound.env_length]; omega)
def source (mode : Mode) (a b : MExp) : MExp :=
  match mode with | .seq => .seq a b | .alt => .alt a b | .notP => .notP a | .star => .star a

def secondId (ns : List CompileNode) (mode : Mode) (a b : MExp) : Nat :=
  match mode with | .seq | .alt => exprId ns b | .notP => 0 | .star => exprId ns a

def branch (ns : List CompileNode) : MExp → NProg 5
  | .seq a b => body .seq (exprId ns a) (exprId ns b)
  | .alt a b => body .alt (exprId ns a) (exprId ns b)
  | .notP a => body .notP (exprId ns a) 0
  | .star a => body .star (exprId ns a) (exprId ns a)
  | _ => .halt false

def numeric (ns : List CompileNode) : NProg 5 := .seq readHead
  (caseTop 1 ((exprPool ns).map (branch ns)) (.halt false))
def localProgram (ns : List CompileNode) : LProg 11 := (numeric ns).compile.rename reg

theorem numeric_runs (ns : List CompileNode) (mode : Mode) (a b : MExp)
    (hs : ExprOK ns (source mode a b)) (m p k : Nat) (E : CaptureEnv) (F : List Nat) :
    NRuns (numeric ns) (st (inputFields m p (exprId ns (source mode a b)) k E F) [] [] [] [])
      (st (outputFields mode m p (exprId ns a) (secondId ns mode a b) k E F) [] [] [] [])
      (50*E.length + 6*F.length + 6*(exprPool ns).length + 150) := by
  let eid := exprId ns (source mode a b)
  let ps := (exprPool ns).map (branch ns)
  let R := (writeEnv E ++ [k] ++ F).reverse
  let S := st [0,m,p] (R ++ [eid]) [] [m,p] []
  have hi : eid < (exprPool ns).length := List.idxOf_lt_length_iff.mpr hs.mem
  have hip : eid < ps.length := by simpa [ps] using hi
  have hget : (exprPool ns)[eid]'hi = source mode a b := by
    apply Option.some.inj
    rw [← List.getElem?_eq_getElem hi]
    exact get_idxOf hs.mem
  have ht : ps[eid]'hip = body mode (exprId ns a) (secondId ns mode a b) := by
    simp only [ps,List.getElem_map,hget]
    cases mode <;> rfl
  have hp : S.set 1 R = st [0,m,p] R [] [m,p] [] := by simp [S]
  have hc := caseTop_runs 1 ps (.halt false) eid hip S R (by simp [S])
    (st (outputFields mode m p (exprId ns a) (secondId ns mode a b) k E F) [] [] [] [])
    (40*E.length + 3*F.length + exprId ns a + 2*secondId ns mode a b + 100) (by
      rw [ht,hp]
      exact body_runs mode m p (exprId ns a) (secondId ns mode a b) k E F)
  have hr := (readHead_runs m p eid k E F).seq hc
  have ha : exprId ns a ≤ (exprPool ns).length := List.idxOf_le_length
  have hb : secondId ns mode a b ≤ (exprPool ns).length := by
    cases mode <;> first | exact List.idxOf_le_length | exact Nat.zero_le _
  exact hr.mono (by omega)

def cellBound (A : Nat) : Nat := 13 + 6*A
def stepBound (A H : Nat) : Nat := 80*A + 8*H + 250
def scratchSpace (A H N : Nat) : Nat := SequentialNumericFive.scratchSpace (cellBound A) (stepBound A H) N

theorem scratchSpace_linear (A H N : Nat) :
    scratchSpace A H N = (cellBound A + stepBound A H) * N +
      (cellBound A + stepBound A H * (stepBound A H + 1) + 2) :=
  SequentialNumericFive.scratchSpace_linear _ _ _

theorem local_runs (ns : List CompileNode) (mode : Mode) (a b : MExp) (hs : ExprOK ns (source mode a b))
    (m p k : Nat) (E : CaptureEnv) (F : List Nat) {A N B width held : Nat} (tail : List Bool)
    (hE : E.length ≤ A) (hF : F.length ≤ 6+3*A)
    (hb : ∀ v ∈ inputFields m p (exprId ns (source mode a b)) k E F, v ≤ N)
    (hspace : scratchSpace A (exprPool ns).length N ≤ B)
    (hR : LenOK B (SequentialFieldFetch.start width [] tail
      (SequentialFrontRead.locals (inputFields m p (exprId ns (source mode a b)) k E F)) held [])) :
    Complexity.Runs (LenOK B) (localProgram ns)
      (SequentialFieldFetch.start width [] tail
        (SequentialFrontRead.locals (inputFields m p (exprId ns (source mode a b)) k E F)) held [])
      (SequentialFieldFetch.start width [] tail
        (SequentialFrontRead.locals (outputFields mode m p (exprId ns a) (secondId ns mode a b) k E F)) held [])
      (stepBound A (exprPool ns).length * ncost B) := by
  have hlen : (inputFields m p (exprId ns (source mode a b)) k E F).length ≤ cellBound A := by
    simp [inputFields,SequentialStackCodecBound.env_length,cellBound]; omega
  have hr := (numeric_runs ns mode a b hs m p k E F).mono (show
    50*E.length + 6*F.length + 6*(exprPool ns).length + 150 ≤ stepBound A (exprPool ns).length by
      unfold stepBound; omega)
  exact SequentialNumericFive.local_runs (numeric ns) _ _ tail hr hlen hb hspace hR

def newFrame (mode : Mode) (m p : Nat) (E : CaptureEnv) (a b : MExp) : SequentialStack.Frame :=
  match mode with
  | .seq => .seq m E b
  | .alt => .alt m E b p
  | .notP => .notP p
  | .star => .star m E a p

def localNext (mode : Mode) (m p : Nat) (E : CaptureEnv) (a b : MExp)
    (frames : List SequentialStack.Frame) : Config := ⟨.expr m E a p,newFrame mode m p E a b :: frames⟩

theorem original_step (g : MGrammar) (x : List Char) (mode : Mode) (m p : Nat) (E : CaptureEnv)
    (a b : MExp) (K : List SequentialStack.Frame) :
    step g x ⟨.expr m E (source mode a b) p,K⟩ = some (localNext mode m p E a b K) := by cases mode <;> rfl

theorem input_prefix (ns : List CompileNode) (mode : Mode) (m p : Nat) (E : CaptureEnv) (a b : MExp)
    (K frames : List SequentialStack.Frame) :
    SequentialFront.prefixCode ns K ⟨.expr m E (source mode a b) p,frames⟩ =
      inputFields m p (exprId ns (source mode a b)) (frames.length + K.length) E (SequentialFront.suffixCode ns frames) := by
  simp [SequentialFront.prefixCode,inputFields,writeTask,writeExpr,List.append_assoc]

theorem output_prefix (ns : List CompileNode) (mode : Mode) (m p : Nat) (E : CaptureEnv) (a b : MExp)
    (K frames : List SequentialStack.Frame) :
    SequentialFront.prefixCode ns K (localNext mode m p E a b frames) =
      outputFields mode m p (exprId ns a) (secondId ns mode a b) (frames.length + K.length) E
        (SequentialFront.suffixCode ns frames) := by
  cases mode <;> simp [SequentialFront.prefixCode,SequentialFront.suffixCode,localNext,newFrame,outputFields,
    secondId,SequentialFrameBuild.fields,SequentialFrameBuild.tailFields,SequentialFrameBuild.tag,
    writeTask,writeExpr,writeFrame,List.append_assoc,Nat.add_assoc,Nat.add_comm]

end Shallot.MacroPeg.CBV.SequentialStructuralEntry
