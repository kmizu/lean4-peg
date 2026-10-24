import MacroPeg.CBV.SequentialAtomCodec

/-! Source-selected atoms that do not read input. They still consume the
counted capture environment and return through the ordinary value-task codec. -/
namespace Shallot.MacroPeg.CBV.SequentialSimpleAtom
open Complexity SequentialStack SequentialStackCodec SequentialStackPool CBVtoCBN
open SequentialNumericFive (st)
open SequentialNotReturn (prepend applied prepend_runs)

inductive Mode where | success | failure | undefined

def Mode.result : Mode → Nat → Res
  | .success,p => some (some p)
  | .failure,_ => some none
  | .undefined,_ => none

def classify : MExp → Option Mode
  | .eps | .dbg _ | .lam _ _ => some .success
  | .callParam _ _ => some .failure
  | .invoke _ _ _ => some .undefined
  | _ => none

def drainEnv : NProg 5 := prepend [.dup 1 2 (by decide),.pop 1]
  (.seq (NCountedTransfer.counted 1 4 2 (by decide) 2)
    (.seq (.prim (.pop 2)) (nclr 4)))

theorem drain_runs (E : CaptureEnv) (p k : Nat) (F : List Nat) :
    NRuns drainEnv (st [] (writeEnv E ++ [k] ++ F).reverse [] [p] [])
      (st [] ([k] ++ F).reverse [] [p] []) (12*E.length+5) := by
  let R := ([k] ++ F).reverse
  let S := st [] (writeEnv E ++ [k] ++ F).reverse [] [p] []
  let A := st [] (R ++ (E.flatMap writePair).reverse) [E.length] [p] []
  let D := st [] R [0] [p] (E.flatMap writePair)
  have hp : applied [.dup (K := 5) 1 2 (by decide),.pop 1] S = A := by
    have he : S = st [] ((R ++ (E.flatMap writePair).reverse) ++ [E.length]) [] [p] [] := by
      simp [S,R,writeEnv,writeList,List.reverse_append,List.append_assoc]
    rw [he]
    simp [applied,NPrim.apply,A,List.append_assoc]
  have hflat : ∀ es : CaptureEnv, (es.map writePair).flatten = es.flatMap writePair := by
    intro es
    induction es with
    | nil => rfl
    | cons a es ih => simp [ih]
  have hm := NCountedTransfer.counted_runs (K := 5) 1 4 2 (by decide) (by decide) (by decide)
    2 (E.map writePair) (by
      intro vs hv
      obtain ⟨pair,_,rfl⟩ := List.mem_map.mp hv
      cases pair
      rfl) R [] [] A (by simp [A,hflat E]) (by simp [A]) (by simp [A])
  have heD : ((A.set 1 R).set 4 ([] ++ (E.map writePair).flatten)).set 2 ([] ++ [0]) = D := by
    simp [A,D,hflat E]
  rw [heD] at hm
  have hpop := nruns_pop 2 D (l := []) (v := 0) (by simp [D])
  have heC : D.set 2 [] = st [] R [] [p] (E.flatMap writePair) := by simp [D]
  rw [heC] at hpop
  have hclr := nruns_clr 4 (st [] R [] [p] (E.flatMap writePair))
  have heF : (st [] R [] [p] (E.flatMap writePair)).set 4 [] = st [] R [] [p] [] := by simp
  rw [heF] at hclr
  have hlen : (E.flatMap writePair).length = 2*E.length := by
    have hh := SequentialStackCodecBound.env_length E
    simp only [writeEnv,writeList,List.length_cons] at hh
    omega
  have hh := prepend_runs [.dup (K := 5) 1 2 (by decide),.pop 1] _ S _ _
    (by rw [hp]; exact hm.seq (hpop.seq hclr))
  exact hh.mono (by simp [hlen]; omega)

def body (mode : Mode) : NProg 5 := .seq drainEnv
  (.seq (npushC 2 (SequentialAtomCodec.status (mode.result 0))) SequentialAtomCodec.finish)

theorem body_runs (mode : Mode) (E : CaptureEnv) (p k : Nat) (F : List Nat) :
    NRuns (body mode) (st [] (writeEnv E ++ [k] ++ F).reverse [] [p] [])
      (st (SequentialAtomCodec.outputFields (mode.result p) k F) [] [] [] [])
      (12*E.length+3*F.length+40) := by
  have hd := drain_runs E p k F
  have hp := nruns_pushC 2 (st [] ([k] ++ F).reverse [] [p] [])
    (SequentialAtomCodec.status (mode.result 0))
  have hp' : NRuns (npushC 2 (SequentialAtomCodec.status (mode.result 0)))
      (st [] ([k] ++ F).reverse [] [p] [])
      (st [] ([k] ++ F).reverse [SequentialAtomCodec.status (mode.result 0)] [p] [])
      (SequentialAtomCodec.status (mode.result 0)+1) := by simpa using hp
  have he : SequentialAtomCodec.status (mode.result 0) = SequentialAtomCodec.status (mode.result p) := by
    cases mode <;> rfl
  rw [he] at hp'
  have hf := SequentialAtomCodec.finish_runs (mode.result p) p k F
  have hpos : SequentialAtomCodec.position (mode.result p) p = p := by cases mode <;> rfl
  rw [hpos] at hf
  have hh := hd.seq (hp'.seq hf)
  have ht : (12*E.length+5)+(SequentialAtomCodec.status (mode.result p)+1+(3*F.length+30)) ≤
      12*E.length+3*F.length+40 := by
    cases mode <;> simp [Mode.result,SequentialAtomCodec.status] <;> omega
  simpa only [body,he] using hh.mono ht

def branch (src : MExp) : NProg 5 :=
  match classify src with | some mode => body mode | none => .halt false

def numeric (ns : List CompileNode) : NProg 5 := .seq SequentialAtomCodec.prepare
  (caseTop 2 ((exprPool ns).map branch) (.halt false))

theorem numeric_runs (ns : List CompileNode) (src : MExp) (hs : ExprOK ns src)
    (mode : Mode) (hclass : classify src = some mode) (m p k : Nat) (E : CaptureEnv) (F : List Nat) :
    NRuns (numeric ns) (st (SequentialStructuralEntry.inputFields m p (exprId ns src) k E F) [] [] [] [])
      (st (SequentialAtomCodec.outputFields (mode.result p) k F) [] [] [] [])
      (18*E.length+6*F.length+2*(exprPool ns).length+100) := by
  let eid := exprId ns src
  let S := st [] (writeEnv E ++ [k] ++ F).reverse [eid] [p] []
  let ps := (exprPool ns).map branch
  have hid : eid < (exprPool ns).length := List.idxOf_lt_length_iff.mpr hs.mem
  have hip : eid < ps.length := by simpa [ps] using hid
  have hget : (exprPool ns)[eid]'hid = src := by
    apply Option.some.inj
    rw [← List.getElem?_eq_getElem hid]
    exact get_idxOf hs.mem
  have hc := caseTop_runs 2 ps (.halt false) eid hip S [] (by simp [S])
    (st (SequentialAtomCodec.outputFields (mode.result p) k F) [] [] [] [])
    (12*E.length+3*F.length+40) (by
      simp only [ps,List.getElem_map,hget,branch,hclass]
      have he : S.set 2 [] = st [] (writeEnv E ++ [k] ++ F).reverse [] [p] [] := by simp [S]
      rw [he]
      exact body_runs mode E p k F)
  exact ((SequentialAtomCodec.prepare_runs m p eid k E F).seq hc).mono (by omega)

theorem atom_eq (src : MExp) (mode : Mode) (hclass : classify src = some mode)
    (x : List Char) (E : CaptureEnv) (p : Nat) : atom x E src p = mode.result p := by
  cases src <;> simp only [classify] at hclass
  all_goals first | contradiction | (cases hclass; rfl)

def budget (ns : List CompileNode) (A M : Nat) : Nat := 18*A+6*M+2*(exprPool ns).length+100

def space (ns : List CompileNode) (A M N e : Nat) : Nat := e+grow N (budget ns A M)+2

theorem space_linear (ns : List CompileNode) (A M N e : Nat) :
    space ns A M N e = e+budget ns A M*N+budget ns A M*(budget ns A M+1)+2 := by
  simp only [space,grow,Nat.mul_add]
  omega

theorem compiled_numeric (ns : List CompileNode) (src : MExp) (hs : ExprOK ns src)
    (mode : Mode) (hclass : classify src = some mode) (m p k : Nat) (E : CaptureEnv) (F : List Nat)
    {A M N e : Nat} (hE : E.length ≤ A) (hF : F.length ≤ M)
    (hS : Bnd N e (st (SequentialStructuralEntry.inputFields m p (exprId ns src) k E F) [] [] [] [])) :
    Runs (LenOK (space ns A M N e)) (numeric ns).compile
      (encL (st (SequentialStructuralEntry.inputFields m p (exprId ns src) k E F) [] [] [] []))
      (encL (st (SequentialAtomCodec.outputFields (mode.result p) k F) [] [] [] []))
      (budget ns A M*ncost (space ns A M N e)) := by
  obtain ⟨t,ht,he⟩ := numeric_runs ns src hs mode hclass m p k E F
  have ht' : t ≤ budget ns A M := by unfold budget; omega
  have hx := (nexec_space he N e hS).2 (space ns A M N e)
    (by have hh := grow_mono (m := N) ht'; unfold space; omega)
  obtain ⟨u,hu,h⟩ := nexec_compile (fun _ h => h) hx
  exact ⟨u,Nat.le_trans hu (Nat.mul_le_mul_right _ ht'),h⟩

theorem numeric_tape (ns : List CompileNode) (src : MExp) (hs : ExprOK ns src)
    (mode : Mode) (hclass : classify src = some mode) (x : List Char) (m p k : Nat)
    (E : CaptureEnv) (F : List Nat) {A M N e : Nat} (hE : E.length ≤ A) (hF : F.length ≤ M)
    (hS : Bnd N e (st (SequentialStructuralEntry.inputFields m p (exprId ns src) k E F) [] [] [] []))
    (τ : Tapes 6) (hτ : Rep (encL (st (SequentialStructuralEntry.inputFields m p (exprId ns src) k E F) [] [] [] [])) τ) :
    ∃ t τ', Exec (TFits (space ns A M N e)) (numeric ns).compile.compile τ t (.cont τ') ∧
      Rep (encL (st (SequentialAtomCodec.outputFields (atom x E src p) k F) [] [] [] [])) τ' := by
  obtain ⟨t,τ',_,he,hr⟩ := Complexity.BinaryWord.runs_tape
    (compiled_numeric ns src hs mode hclass m p k E F hE hF hS) τ hτ
  rw [← atom_eq src mode hclass x E p] at hr
  exact ⟨t,τ',he,hr⟩

end Shallot.MacroPeg.CBV.SequentialSimpleAtom
