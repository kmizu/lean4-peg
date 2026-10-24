import MacroPeg.CBV.SequentialStructuralEntry
import Complexity.NRename

/-! Normalize an encoded expression task for source-ID dispatch and assemble
an atom result back into the existing value-task and continuation encoding. -/
namespace Shallot.MacroPeg.CBV.SequentialAtomCodec
open Complexity SequentialStack SequentialStackCodec SequentialStackPool CBVtoCBN
open SequentialNumericFive (st)
open SequentialNotReturn (prepend applied prepend_runs constants)
open SequentialStructuralEntry (inputFields)

def prepareTail : NProg 5 := .seq (nclr 0) (.seq (nmv 1 2 (by decide))
  (prepend [.dup 3 4 (by decide),.pop 3,.pop 3] (nmv 4 3 (by decide))))
def prepare : NProg 5 := .seq SequentialStructuralEntry.readHead prepareTail

theorem prepareTail_runs (m p eid : Nat) (R : List Nat) :
    NRuns prepareTail (st [0,m,p] (R ++ [eid]) [] [m,p] []) (st [] R [eid] [p] []) 14 := by
  let S := st [0,m,p] (R ++ [eid]) [] [m,p] []
  let A := st [] (R ++ [eid]) [] [m,p] []
  let D := st [] R [eid] [m,p] []
  let E := st [] R [eid] [] [p]
  have h₁ := nruns_clr 0 S
  have heA : S.set 0 [] = A := by simp [S,A]
  rw [heA] at h₁
  have h₂ := nruns_mv 1 2 (by decide : (1 : Fin 5) ≠ 2) A (l := R) (v := eid) (by simp [A])
  have heD : (A.set 2 (A 2 ++ [eid])).set 1 R = D := by simp [A,D]
  rw [heD] at h₂
  have heE : applied [.dup (K := 5) 3 4 (by decide),.pop 3,.pop 3] D = E := by
    simp [D,E,applied,NPrim.apply]
  have h₃ := nruns_mv 4 3 (by decide : (4 : Fin 5) ≠ 3) E (l := []) (v := p) (by simp [E])
  have heF : (E.set 3 (E 3 ++ [p])).set 4 [] = st [] R [eid] [p] [] := by simp [E]
  rw [heF] at h₃
  have hh := h₁.seq (h₂.seq (prepend_runs [.dup 3 4 (by decide),.pop 3,.pop 3] _ D _ _
    (by rw [heE]; exact h₃)))
  exact hh.mono (by simp [S])

theorem prepare_runs (m p eid k : Nat) (E : CaptureEnv) (F : List Nat) :
    NRuns prepare (st (inputFields m p eid k E F) [] [] [] [])
      (st [] (writeEnv E ++ [k] ++ F).reverse [eid] [p] [])
      (6*E.length+3*F.length+50) := by
  exact ((SequentialStructuralEntry.readHead_runs m p eid k E F).seq
    (prepareTail_runs m p eid (writeEnv E ++ [k] ++ F).reverse)).mono (by omega)

def status : Res → Nat
  | none => 0
  | some none => 1
  | some (some _) => 2

def position (r : Res) (d : Nat) : Nat :=
  match r with | some (some q) => q | _ => d

def outputFields (r : Res) (k : Nat) (F : List Nat) : List Nat :=
  [3,0] ++ writeRes r ++ [k] ++ F

def branch (tag : Nat) : NProg 5 := .seq (npushC 0 tag)
  (.seq (if tag=2 then nmv 3 0 (by decide) else .prim (.pop 3)) (nmvAll 1 0 (by decide)))

private theorem save_runs (D R : List Nat) (q : Nat) (save : Bool) :
    NRuns (if save then nmv 3 0 (by decide) else .prim (.pop 3))
      (st D R [] [q] []) (st (D ++ if save then [q] else []) R [] [] []) 2 := by
  cases save with
  | false =>
    have hh := nruns_pop 3 (st D R [] [q] []) (l := []) (v := q) (by simp)
    simpa using hh.mono (by omega)
  | true =>
    have hh := nruns_mv 3 0 (by decide : (3 : Fin 5) ≠ 0) (st D R [] [q] [])
      (l := []) (v := q) (by simp)
    simpa using hh

private theorem branch_runs (tag q k : Nat) (F : List Nat) :
    NRuns (branch tag) (st [3,0] ([k] ++ F).reverse [] [q] [])
      (st ([3,0,tag] ++ (if tag=2 then [q] else []) ++ [k] ++ F) [] [] [] [])
      (3*F.length+tag+7) := by
  let R := ([k] ++ F).reverse
  let D := [3,0,tag] ++ if tag=2 then [q] else []
  have h₁ := nruns_pushC 0 (st [3,0] R [] [q] []) tag
  simp at h₁
  have h₂ : NRuns (if tag=2 then nmv 3 0 (by decide) else .prim (.pop 3))
      (st [3,0,tag] R [] [q] []) (st D R [] [] []) 2 := by
    simpa only [decide_eq_true_eq] using save_runs [3,0,tag] R q (decide (tag=2))
  have h₃ := nruns_mvAll 1 0 (by decide : (1 : Fin 5) ≠ 0) (st D R [] [] [])
  have he : ((st D R [] [] []).set 0 (D ++ R.reverse)).set 1 [] =
      st ([3,0,tag] ++ (if tag=2 then [q] else []) ++ [k] ++ F) [] [] [] [] := by
    simp [D,R,List.append_assoc]
  change NRuns _ (st D R [] [] []) (((st D R [] [] []).set 0 (D ++ R.reverse)).set 1 [])
    (3*R.length+1) at h₃
  rw [he] at h₃
  have hh := h₁.seq (h₂.seq h₃)
  exact hh.mono (by simp [R]; omega)

def headOps : List (NPrim 5) := constants 0 3 ++ constants 0 0

def finish : NProg 5 := prepend headOps (caseTop 2 ([0,1,2].map branch) (.halt false))

theorem finish_runs (r : Res) (d k : Nat) (F : List Nat) :
    NRuns finish (st [] ([k] ++ F).reverse [status r] [position r d] [])
      (st (outputFields r k F) [] [] [] []) (3*F.length+30) := by
  let S := st [3,0] ([k] ++ F).reverse [status r] [position r d] []
  have hp : applied headOps (st [] ([k] ++ F).reverse [status r] [position r d] []) = S := by
    simp [headOps,constants,applied,NPrim.apply,mapTop,S]
  have hi : status r < ([0,1,2].map branch).length := by
    cases r with
    | none => decide
    | some r => cases r <;> simp [status]
  have hc := caseTop_runs 2 ([0,1,2].map branch) (.halt false) (status r) hi S [] (by simp [S])
    (st (outputFields r k F) [] [] [] []) (3*F.length+10) (by
      have he : S.set 2 [] = st [3,0] ([k] ++ F).reverse [] [position r d] [] := by simp [S]
      rw [he]
      cases r with
      | none => simpa [status,position,outputFields,writeRes,branch] using (branch_runs 0 d k F).mono (by omega)
      | some rr =>
        cases rr with
        | none => simpa [status,position,outputFields,writeRes,branch] using (branch_runs 1 d k F).mono (by omega)
        | some q => simpa [status,position,outputFields,writeRes,branch] using (branch_runs 2 q k F).mono (by omega))
  have hh := prepend_runs headOps _ (st [] ([k] ++ F).reverse [status r] [position r d] []) _ _
    (by rw [hp]; exact hc)
  exact hh.mono (by
    have ht : status r ≤ 2 := by cases r with | none => decide | some rr => cases rr <;> simp [status]
    simp [headOps,constants]
    omega)

theorem prepare_fits (m p eid k : Nat) (E : CaptureEnv) (F : List Nat) {A M N e B : Nat}
    (hE : E.length ≤ A) (hF : F.length ≤ M)
    (hS : Bnd N e (st (inputFields m p eid k E F) [] [] [] []))
    (hB : e+grow N (6*A+3*M+50)+2 ≤ B) :
    NBoundedTransfer.FitsRuns B prepare (st (inputFields m p eid k E F) [] [] [] [])
      (st [] (writeEnv E ++ [k] ++ F).reverse [eid] [p] []) (6*A+3*M+50) := by
  obtain ⟨t,ht,he⟩ := prepare_runs m p eid k E F
  have ht' : t ≤ 6*A+3*M+50 := by omega
  exact ⟨t,ht',(nexec_space he N e hS).2 B (by have hh := grow_mono (m := N) ht'; omega)⟩

theorem finish_fits (r : Res) (d k : Nat) (F : List Nat) {M N e B : Nat} (hF : F.length ≤ M)
    (hS : Bnd N e (st [] ([k] ++ F).reverse [status r] [position r d] []))
    (hB : e+grow N (3*M+30)+2 ≤ B) :
    NBoundedTransfer.FitsRuns B finish (st [] ([k] ++ F).reverse [status r] [position r d] [])
      (st (outputFields r k F) [] [] [] []) (3*M+30) := by
  obtain ⟨t,ht,he⟩ := finish_runs r d k F
  have ht' : t ≤ 3*M+30 := by omega
  exact ⟨t,ht',(nexec_space he N e hS).2 B (by have hh := grow_mono (m := N) ht'; omega)⟩

/-- The branch table is fixed by the source pool. It can use the ambient
registers, including the original input register outside the normalization map. -/
def select {K : Nat} (ns : List CompileNode) (ρ : Fin 5 → Fin K) (hi : Function.Injective ρ)
    (branches : MExp → NProg K) : NProg K :=
  .seq (prepare.rename ρ hi) (caseTop (ρ 2) ((exprPool ns).map branches) (.halt false))

theorem selected_runs {K : Nat} (ns : List CompileNode) (ρ : Fin 5 → Fin K) (hi : Function.Injective ρ)
    (branches : MExp → NProg K) (src : MExp) (hs : ExprOK ns src)
    (m p k : Nat) (E : CaptureEnv) (F : List Nat) {A M N e B T : Nat}
    (hE : E.length ≤ A) (hF : F.length ≤ M) (R : Lists K) (hR : NFits B R)
    (hS : Bnd N e (st (inputFields m p (exprId ns src) k E F) [] [] [] []))
    (hB : e+grow N (6*A+3*M+50)+2 ≤ B) (S' : Lists K)
    (hbranch : NBoundedTransfer.FitsRuns B (branches src)
      ((st [] (writeEnv E ++ [k] ++ F).reverse [] [p] []).frame ρ R) S' T) :
    NBoundedTransfer.FitsRuns B (select ns ρ hi branches)
      ((st (inputFields m p (exprId ns src) k E F) [] [] [] []).frame ρ R) S'
      (6*A+3*M+50+T+2*(exprPool ns).length+2) := by
  let eid := exprId ns src
  let Q := st [] (writeEnv E ++ [k] ++ F).reverse [eid] [p] []
  let ps := (exprPool ns).map branches
  have hprep := (prepare_fits m p eid k E F hE hF hS hB).rename_frame hi R hR
  have hQ : NFits B (Q.frame ρ R) := by obtain ⟨_,_,he⟩ := hprep; exact he.post
  have hid : eid < (exprPool ns).length := List.idxOf_lt_length_iff.mpr hs.mem
  have hip : eid < ps.length := by simpa [ps] using hid
  have hget : (exprPool ns)[eid]'hid = src := by
    apply Option.some.inj
    rw [← List.getElem?_eq_getElem hid]
    exact get_idxOf hs.mem
  have hp : ps[eid]'hip = branches src := by simp only [ps,List.getElem_map,hget]
  have hset : (Q.frame ρ R).set (ρ 2) [] = (st [] (writeEnv E ++ [k] ++ F).reverse [] [p] []).frame ρ R := by
    rw [← Lists.frame_set hi]
    simp [Q]
  have hd := NShrinkingCompare.caseTop_exec (ρ 2) ps (.halt false) eid hip (Q.frame ρ R) []
    (by rw [Lists.frame_get hi]; simp [Q]) hQ S' T (by rw [hp,hset]; exact hbranch)
  obtain ⟨t,ht,he⟩ := hprep.seq hd
  exact ⟨t,by omega,he⟩

def Atomic : MExp → Prop
  | .seq _ _ | .alt _ _ | .notP _ | .star _ | .call _ _ => False
  | _ => True

theorem original_step (g : MGrammar) (x : List Char) (m p : Nat) (E : CaptureEnv)
    (src : MExp) (hsrc : Atomic src) (frames : List SequentialStack.Frame) :
    step g x ⟨.expr m E src p,frames⟩ = some ⟨.value (.expr (atom x E src p)),frames⟩ := by
  cases src <;> simp only [Atomic] at hsrc <;> first | contradiction | rfl

theorem input_prefix (ns : List CompileNode) (m p : Nat) (E : CaptureEnv) (src : MExp)
    (K frames : List SequentialStack.Frame) :
    SequentialFront.prefixCode ns K ⟨.expr m E src p,frames⟩ =
      inputFields m p (exprId ns src) (frames.length+K.length) E (SequentialFront.suffixCode ns frames) := by
  simp [SequentialFront.prefixCode,inputFields,writeTask,writeExpr,List.append_assoc]

theorem output_prefix (ns : List CompileNode) (r : Res) (K frames : List SequentialStack.Frame) :
    SequentialFront.prefixCode ns K ⟨.value (.expr r),frames⟩ =
      outputFields r (frames.length+K.length) (SequentialFront.suffixCode ns frames) := by
  simp [SequentialFront.prefixCode,outputFields,writeTask,writeValue,List.append_assoc]

end Shallot.MacroPeg.CBV.SequentialAtomCodec
