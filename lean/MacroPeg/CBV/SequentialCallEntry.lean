import Complexity.NPushFields
import MacroPeg.CBV.SequentialStructuralEntry

/-! Enter a call only when its fixed rule and argument count agree. -/
namespace Shallot.MacroPeg.CBV.SequentialCallEntry
open Complexity SequentialStack SequentialStackCodec SequentialStackPool SequentialStackPayload CBVtoCBN
open SequentialNotReturn (prepend applied prepend_runs constants)
open SequentialNumericFive (st reg)
open SequentialStructuralEntry (inputFields readHead readHead_runs capture capture_runs header header_runs)

def allowed (g : MGrammar) (i : Nat) (es : List MExp) : Bool :=
  match ruleAtM g.rules i with | none => false | some r => decide (r.arity = es.length)

theorem allowed_bounds (g : MGrammar) (i : Nat) (es : List MExp) (h : allowed g i es = true) :
    es.length ≤ arityBudget g ∧ i < g.rules.length := by
  cases hr : ruleAtM g.rules i with
  | none => simp [allowed,hr] at h
  | some r =>
    have ha : r.arity = es.length := by simpa [allowed,hr] using h
    have hb := arityBudget_spec g r (ruleAtM_mem hr)
    exact ⟨by omega,CBV.ruleAtM_lt hr⟩

def copyMeta : List (NPrim 5) := [.dup 4 0 (by decide),.dup 4 3 (by decide),.pop 4,
  .dup 4 0 (by decide),.dup 4 3 (by decide),.pop 4]
def startArgs : NProg 5 := .seq (nclr 0) (.seq (npushC 0 1)
  (.seq (nmvAll 3 4 (by decide)) (prepend copyMeta (nskip 4))))

theorem startArgs_runs (m p : Nat) (R : List Nat) :
    NRuns startArgs (st [0,m,p] R [] [m,p] []) (st [1,m,p] R [] [m,p] []) 30 := by
  let S := st [0,m,p] R [] [m,p] []
  let A := st [] R [] [m,p] []
  let B := st [1] R [] [m,p] []
  let C := st [1] R [] [] [p,m]
  have h₁ := nruns_clr 0 S
  have hA : S.set 0 [] = A := by simp [S,A]
  rw [hA] at h₁
  have h₂ := nruns_pushC 0 A 1
  have hB : A.set 0 (A 0 ++ [1]) = B := by simp [A,B]
  rw [hB] at h₂
  have h₃ := nruns_mvAll 3 4 (by decide : (3 : Fin 5) ≠ 4) B
  have hC : (B.set 4 (B 4 ++ (B 3).reverse)).set 3 [] = C := by simp [B,C]
  rw [hC] at h₃
  have hp : applied copyMeta C = st [1,m,p] R [] [m,p] [] := by simp [C,copyMeta,applied,NPrim.apply]
  have hf := prepend_runs copyMeta (nskip 4) C _ 2 (by rw [hp]; exact nruns_skip 4 _)
  exact (h₁.seq (h₂.seq (h₃.seq hf))).mono (by simp [S,B,copyMeta] <;> omega)

def finishPre : List (NPrim 5) := [.pop 3,.dup 3 0 (by decide),.pop 3]
def finishCall (i : Nat) : NProg 5 := .seq (npushC 0 6)
  (prepend finishPre (.seq (npushC 0 i) (.seq (nclr 2) (nmvAll 1 0 (by decide)))))

theorem finishCall_runs (m p i : Nat) (D env F : List Nat) :
    NRuns (finishCall i) (st D F.reverse env [m,p] [])
      (st (D ++ [6,m,i] ++ F) [] [] [] []) (2*env.length + 3*F.length + i + 20) := by
  let S := st D F.reverse env [m,p] []
  let A := st (D ++ [6]) F.reverse env [m,p] []
  let B := st (D ++ [6,m]) F.reverse env [] []
  let C := st (D ++ [6,m,i]) F.reverse env [] []
  let R := st (D ++ [6,m,i]) F.reverse [] [] []
  have h₁ := nruns_pushC 0 S 6
  have hA : S.set 0 (S 0 ++ [6]) = A := by simp [S,A]
  rw [hA] at h₁
  have hp : applied finishPre A = B := by simp [A,B,finishPre,applied,NPrim.apply]
  have h₂ := nruns_pushC 0 B i
  have hC : B.set 0 (B 0 ++ [i]) = C := by simp [B,C]
  rw [hC] at h₂
  have h₃ := nruns_clr 2 C
  have hR : C.set 2 [] = R := by simp [C,R]
  rw [hR] at h₃
  have hm := nruns_mvAll 1 0 (by decide : (1 : Fin 5) ≠ 0) R
  have hF : (R.set 0 (R 0 ++ (R 1).reverse)).set 1 [] = st (D ++ [6,m,i] ++ F) [] [] [] [] := by simp [R]
  rw [hF] at hm
  have hall := h₁.seq (prepend_runs finishPre _ A _ _ (by rw [hp]; exact h₂.seq (h₃.seq hm)))
  exact hall.mono (by simp [finishPre,C,R]; omega)

def pushBound (A H : Nat) : Nat := (A+1)*(A+H+2)+2

def validProgram (i : Nat) (args : List Nat) : NProg 5 := .seq startArgs
  (.seq capture (.seq (NPushFields.program 0 4 (args.length :: args)) (.seq header (finishCall i))))

theorem valid_runs (m p k i : Nat) (E : CaptureEnv) (args F : List Nat) {A H : Nat}
    (hlen : args.length ≤ A) (hb : ∀ v ∈ args, v ≤ H) :
    NRuns (validProgram i args) (st [0,m,p] (writeEnv E ++ [k] ++ F).reverse [] [m,p] [])
      (st ([1,m,p] ++ writeEnv E ++ (args.length :: args) ++ [k+1,6,m,i] ++ F) [] [] [] [])
      (30*E.length + 3*F.length + i + pushBound A H + 100) := by
  have hs := startArgs_runs m p (writeEnv E ++ [k] ++ F).reverse
  have hc := capture_runs m p k [1,m,p] E F
  let S := st ([1,m,p] ++ writeEnv E) ([k] ++ F).reverse (writeEnv E) [m,p] []
  let D := [1,m,p] ++ writeEnv E ++ (args.length :: args)
  have hp := NPushFields.runs 0 4 (args.length :: args) S (A+H+1) (by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · omega
    · have hh := hb v hv; omega)
  have heD : S.set 0 (S 0 ++ args.length :: args) = st D ([k] ++ F).reverse (writeEnv E) [m,p] [] := by simp [S,D]
  rw [heD] at hp
  have ht : (args.length :: args).length * (A+H+1+1)+2 ≤ pushBound A H := by
    have hh := Nat.mul_le_mul_right (A+H+2) (show args.length+1 ≤ A+1 by omega)
    simpa [pushBound,Nat.add_assoc] using Nat.add_le_add_right hh 2
  have hp' := hp.mono ht
  have hh := header_runs m p k D (writeEnv E) F
  have hf := finishCall_runs m p i (D ++ [k+1]) (writeEnv E) F
  have heF : (D ++ [k+1]) ++ [6,m,i] ++ F = [1,m,p] ++ writeEnv E ++ (args.length :: args) ++ [k+1,6,m,i] ++ F := by
    simp [D,List.append_assoc]
  rw [heF] at hf
  exact (hs.seq (hc.seq (hp'.seq (hh.seq hf)))).mono (by simp [SequentialStackCodecBound.env_length]; omega)
def failOps : List (NPrim 5) := constants 0 3 ++ constants 0 0 ++ constants 0 1 ++
  [.dup 1 0 (by decide),.pop 1]
def invalidProgram : NProg 5 := .seq capture (.seq (nclr 0) (.seq (nclr 2) (.seq (nclr 3)
  (prepend failOps (nmvAll 1 0 (by decide))))))

theorem invalid_runs (m p k : Nat) (E : CaptureEnv) (F : List Nat) :
    NRuns invalidProgram (st [0,m,p] (writeEnv E ++ [k] ++ F).reverse [] [m,p] [])
      (st ([3,0,1,k] ++ F) [] [] [] []) (40*E.length + 3*F.length + 60) := by
  let S := st ([0,m,p] ++ writeEnv E) ([k] ++ F).reverse (writeEnv E) [m,p] []
  let A := st [] ([k] ++ F).reverse (writeEnv E) [m,p] []
  let B := st [] ([k] ++ F).reverse [] [m,p] []
  let C := st [] ([k] ++ F).reverse [] [] []
  let R := st [3,0,1,k] F.reverse [] [] []
  have hc := capture_runs m p k [0,m,p] E F
  have h₁ := nruns_clr 0 S
  have hA : S.set 0 [] = A := by simp [S,A]
  rw [hA] at h₁
  have h₂ := nruns_clr 2 A
  have hB : A.set 2 [] = B := by simp [A,B]
  rw [hB] at h₂
  have h₃ := nruns_clr 3 B
  have hC : B.set 3 [] = C := by simp [B,C]
  rw [hC] at h₃
  have hp : applied failOps C = R := by simp [C,R,failOps,constants,applied,NPrim.apply,mapTop]
  have hm := nruns_mvAll 1 0 (by decide : (1 : Fin 5) ≠ 0) R
  have hF : (R.set 0 (R 0 ++ (R 1).reverse)).set 1 [] = st ([3,0,1,k] ++ F) [] [] [] [] := by simp [R]
  rw [hF] at hm
  have hall := hc.seq (h₁.seq (h₂.seq (h₃.seq (prepend_runs failOps _ C _ _ (by rw [hp]; exact hm)))))
  exact hall.mono (by simp [S,A,B,R,failOps,constants,SequentialStackCodecBound.env_length]; omega)

def outputFields (ns : List CompileNode) (g : MGrammar) (i : Nat) (es : List MExp)
    (m p k : Nat) (E : CaptureEnv) (F : List Nat) : List Nat :=
  if allowed g i es then [1,m,p] ++ writeEnv E ++ writeExprs ns es ++ [k+1,6,m,i] ++ F else [3,0,1,k] ++ F

def branch (ns : List CompileNode) (g : MGrammar) : MExp → NProg 5
  | .call i es => if allowed g i es then validProgram i (es.map (exprId ns)) else invalidProgram
  | _ => .halt false

def numeric (ns : List CompileNode) (g : MGrammar) : NProg 5 := .seq readHead
  (caseTop 1 ((exprPool ns).map (branch ns g)) (.halt false))
def localProgram (ns : List CompileNode) (g : MGrammar) : LProg 11 := (numeric ns g).compile.rename reg

theorem numeric_runs (ns : List CompileNode) (g : MGrammar) (i : Nat) (es : List MExp)
    (hs : ExprOK ns (.call i es)) (m p k : Nat) (E : CaptureEnv) (F : List Nat) :
    NRuns (numeric ns g) (st (inputFields m p (exprId ns (.call i es)) k E F) [] [] [] [])
      (st (outputFields ns g i es m p k E F) [] [] [] [])
      (50*E.length + 6*F.length + g.rules.length + pushBound (arityBudget g) (exprPool ns).length +
        3*(exprPool ns).length + 150) := by
  let eid := exprId ns (.call i es)
  let ps := (exprPool ns).map (branch ns g)
  let R := (writeEnv E ++ [k] ++ F).reverse
  let S := st [0,m,p] (R ++ [eid]) [] [m,p] []
  have hi : eid < (exprPool ns).length := List.idxOf_lt_length_iff.mpr hs.mem
  have hip : eid < ps.length := by simpa [ps] using hi
  have hget : (exprPool ns)[eid]'hi = .call i es := by
    apply Option.some.inj
    rw [← List.getElem?_eq_getElem hi]
    exact get_idxOf hs.mem
  have ht : ps[eid]'hip = branch ns g (.call i es) := by simp [ps,hget]
  have hp : S.set 1 R = st [0,m,p] R [] [m,p] [] := by simp [S]
  have hbr : NRuns (branch ns g (.call i es)) (S.set 1 R)
      (st (outputFields ns g i es m p k E F) [] [] [] [])
      (40*E.length + 3*F.length + g.rules.length + pushBound (arityBudget g) (exprPool ns).length + 100) := by
    rw [hp]
    by_cases hv : allowed g i es = true
    · have hbounds := allowed_bounds g i es hv
      have hr := valid_runs m p k i E (es.map (exprId ns)) F (A := arityBudget g) (H := (exprPool ns).length)
        (by simpa using hbounds.1) (by
          intro v h
          obtain ⟨a,_,rfl⟩ := List.mem_map.mp h
          exact List.idxOf_le_length)
      have hr' := hr.mono (show 30*E.length + 3*F.length + i + pushBound (arityBudget g) (exprPool ns).length + 100 ≤ 40*E.length + 3*F.length + g.rules.length + pushBound (arityBudget g) (exprPool ns).length + 100 by omega)
      simpa [R,branch,outputFields,hv,SequentialArgsEntry.exprs_code] using hr'
    · have hr := (invalid_runs m p k E F).mono (show 40*E.length + 3*F.length + 60 ≤ 40*E.length + 3*F.length + g.rules.length + pushBound (arityBudget g) (exprPool ns).length + 100 by omega)
      simpa [R,branch,outputFields,hv] using hr
  have hc := caseTop_runs 1 ps (.halt false) eid hip S R (by simp [S])
    (st (outputFields ns g i es m p k E F) [] [] [] [])
    (40*E.length + 3*F.length + g.rules.length + pushBound (arityBudget g) (exprPool ns).length + 100)
    (by rw [ht]; exact hbr)
  exact ((readHead_runs m p eid k E F).seq hc).mono (by omega)

def cellBound (A : Nat) : Nat := 13+6*A
def stepBound (A R H : Nat) : Nat := 80*A + 2*R + 2*pushBound A H + 8*H + 250
def scratchSpace (A R H N : Nat) : Nat := SequentialNumericFive.scratchSpace (cellBound A) (stepBound A R H) N

theorem scratchSpace_linear (A R H N : Nat) :
    scratchSpace A R H N = (cellBound A + stepBound A R H) * N +
      (cellBound A + stepBound A R H * (stepBound A R H + 1) + 2) :=
  SequentialNumericFive.scratchSpace_linear _ _ _

theorem local_runs (ns : List CompileNode) (g : MGrammar) (i : Nat) (es : List MExp)
    (hs : ExprOK ns (.call i es)) (m p k : Nat) (E : CaptureEnv) (F : List Nat) {A N B width held : Nat}
    (tail : List Bool) (hA : A = arityBudget g) (hE : E.length ≤ A) (hF : F.length ≤ 6+3*A)
    (hb : ∀ v ∈ inputFields m p (exprId ns (.call i es)) k E F, v ≤ N)
    (hspace : scratchSpace A g.rules.length (exprPool ns).length N ≤ B)
    (hR : LenOK B (SequentialFieldFetch.start width [] tail
      (SequentialFrontRead.locals (inputFields m p (exprId ns (.call i es)) k E F)) held [])) :
    Complexity.Runs (LenOK B) (localProgram ns g)
      (SequentialFieldFetch.start width [] tail
        (SequentialFrontRead.locals (inputFields m p (exprId ns (.call i es)) k E F)) held [])
      (SequentialFieldFetch.start width [] tail
        (SequentialFrontRead.locals (outputFields ns g i es m p k E F)) held [])
      (stepBound A g.rules.length (exprPool ns).length * ncost B) := by
  subst A
  have hlen : (inputFields m p (exprId ns (.call i es)) k E F).length ≤ cellBound (arityBudget g) := by
    simp [inputFields,SequentialStackCodecBound.env_length,cellBound]; omega
  have hr := (numeric_runs ns g i es hs m p k E F).mono (show
    50*E.length + 6*F.length + g.rules.length + pushBound (arityBudget g) (exprPool ns).length +
      3*(exprPool ns).length + 150 ≤ stepBound (arityBudget g) g.rules.length (exprPool ns).length by
        unfold stepBound; omega)
  exact SequentialNumericFive.local_runs (numeric ns g) _ _ tail hr hlen hb hspace hR

def localNext (g : MGrammar) (i : Nat) (es : List MExp) (m p : Nat) (E : CaptureEnv)
    (frames : List SequentialStack.Frame) : Config :=
  if allowed g i es then ⟨.args m E es p,.call m i :: frames⟩ else ⟨.value (.expr (some none)),frames⟩

theorem original_step (g : MGrammar) (x : List Char) (i : Nat) (es : List MExp) (m p : Nat)
    (E : CaptureEnv) (K : List SequentialStack.Frame) :
    step g x ⟨.expr m E (.call i es) p,K⟩ = some (localNext g i es m p E K) := by
  cases hr : ruleAtM g.rules i with
  | none => simp [step,localNext,allowed,hr]
  | some r => by_cases ha : r.arity = es.length <;> simp [step,localNext,allowed,hr,ha]

theorem input_prefix (ns : List CompileNode) (i : Nat) (es : List MExp) (m p : Nat) (E : CaptureEnv)
    (K frames : List SequentialStack.Frame) :
    SequentialFront.prefixCode ns K ⟨.expr m E (.call i es) p,frames⟩ =
      inputFields m p (exprId ns (.call i es)) (frames.length + K.length) E (SequentialFront.suffixCode ns frames) := by
  simp [SequentialFront.prefixCode,inputFields,writeTask,writeExpr,List.append_assoc]

theorem output_prefix (ns : List CompileNode) (g : MGrammar) (i : Nat) (es : List MExp)
    (m p : Nat) (E : CaptureEnv) (K frames : List SequentialStack.Frame) :
    SequentialFront.prefixCode ns K (localNext g i es m p E frames) =
      outputFields ns g i es m p (frames.length + K.length) E (SequentialFront.suffixCode ns frames) := by
  by_cases hv : allowed g i es = true <;>
    simp [SequentialFront.prefixCode,SequentialFront.suffixCode,localNext,outputFields,hv,
      writeTask,writeValue,writeRes,writeFrame,List.append_assoc,Nat.add_assoc,Nat.add_comm]

end Shallot.MacroPeg.CBV.SequentialCallEntry
