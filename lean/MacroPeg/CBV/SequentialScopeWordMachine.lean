import MacroPeg.CBV.SequentialScopeControlMachine
import Complexity.ListRename

/-! Delete the callee environment while retaining any words in a return value. -/
namespace Shallot.MacroPeg.CBV.SequentialScopeWordMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine
open SequentialCaptureCopyMachine (wordTape)
open SequentialSharedWords (CaptureEnv)

def swap (j : Fin 8) : Fin 8 := if j=5 then 7 else if j=7 then 5 else j

theorem swap_twice (j : Fin 8) : swap (swap j) = j := by
  by_cases h5 : j=5 <;> by_cases h7 : j=7 <;> simp_all [swap]

theorem swap_injective : Function.Injective swap := by
  intro a b h
  have hh := congrArg swap h
  simpa only [swap_twice] using hh

def stashReturnWords : LProg 8 := (SequentialWordRotateMachine.stashAfter 4).rename swap

theorem stashReturnWords_runs (saved : List Nat) (W : CaptureEnv) (C tail : List Nat) (L : Lists 8)
    {B : Nat} (hsaved : saved.length=4) (hsrc : L 2 = C ++ unary W.length ++ blocks saved)
    (hstop : symIs 1 (lastSym C)=false) (hword : L 4 = tail ++ wordTape W)
    (h1 : L 1 = []) (hL : LenOK B L) (hcap : (L 5).length+(wordTape W).length+2 ≤ B) :
    ∃ T, Runs (LenOK B) stashReturnWords L
      ((L.set 4 tail).set 5 (L 5 ++ (wordTape W).reverse)) T := by
  let P : Lists 8 := fun j => L (swap j)
  have hP : LenOK B P := fun j => hL (swap j)
  obtain ⟨T,hr⟩ := SequentialWordRotateMachine.stashAfter_runs saved W C tail P
    hsrc hstop hword h1 hP hcap
  rw [hsaved] at hr
  obtain ⟨t,ht,hx⟩ := hr
  have hx' := hx.rename_frame swap_injective L hL
  have hframe : P.frame swap L = L := Lists.frame_eq swap_injective L P (fun _ => rfl)
  have hout : ((P.set 4 tail).set 7 (P 7 ++ (wordTape W).reverse)).frame swap L =
      (L.set 4 tail).set 5 (L 5 ++ (wordTape W).reverse) := by
    rw [Lists.frame_set swap_injective,Lists.frame_set swap_injective,hframe]
    rfl
  refine ⟨T,t,ht,?_⟩
  simpa only [stashReturnWords,LOutcome.frame,hframe,hout] using hx'

/-- The environment-length field is left intact after its words are freed. -/
def discardCurrent : LProg 8 := .seq (SequentialWordRotateMachine.stashAfter 0) (clearP 7)

theorem discardCurrent_runs (E : CaptureEnv) (C tail : List Nat) (L : Lists 8) {B : Nat}
    (hsrc : L 2 = C ++ unary E.length) (hstop : symIs 1 (lastSym C)=false)
    (hword : L 4 = tail ++ wordTape E) (h1 : L 1 = []) (h7 : L 7 = []) (hL : LenOK B L) :
    ∃ T, Runs (LenOK B) discardCurrent L (L.set 4 tail) T := by
  have hw := hL 4
  rw [hword] at hw
  simp only [List.length_append] at hw
  obtain ⟨T,hr⟩ := SequentialWordRotateMachine.stashAfter_runs [] E C tail L
    (by simpa [blocks,bits,SequentialCursorChain.encodeDeltas] using hsrc) hstop hword h1 hL
    (by simp only [h7,List.length_nil]; omega)
  let N := (L.set 4 tail).set 7 (L 7 ++ (wordTape E).reverse)
  have hc := clear_runs (tmp := (7 : Fin 8)) N (end_fits hr)
  have he : N.set 7 [] = L.set 4 tail := by
    simp only [N,Lists.set_set_u]
    have hh : (L.set 4 tail) 7 = [] := by simpa only [Lists.set_ne _ _ (by decide : (7 : Fin 8) ≠ 4)] using h7
    rw [← hh,Lists.set_get_self]
  rw [he] at hc
  exact ⟨_,hr.seq hc⟩

def preserveReturnWords : LProg 8 := .seq stashReturnWords (.seq discardCurrent (moveAll 5 4))

theorem preserveReturnWords_runs (E V : CaptureEnv) (stack : Nat) (C tail : List Nat)
    (L : Lists 8) {B : Nat}
    (hsrc : L 2 = C ++ [0] ++ unary V.length ++ blocks [E.length,stack,4,2])
    (hword : L 4 = tail ++ wordTape E ++ wordTape V)
    (h1 : L 1 = []) (h5 : L 5 = []) (h7 : L 7 = []) (hL : LenOK B L) :
    ∃ T, Runs (LenOK B) preserveReturnWords L (L.set 4 (tail ++ wordTape V)) T := by
  have hw := hL 4
  rw [hword] at hw
  simp only [List.length_append] at hw
  obtain ⟨T1,hr⟩ := stashReturnWords_runs [E.length,stack,4,2] V (C ++ [0])
    (tail ++ wordTape E) L rfl hsrc (by rw [lastSym_append]; rfl) hword h1 hL
    (by simp only [h5,List.length_nil]; omega)
  let N := (L.set 4 (tail ++ wordTape E)).set 5 (L 5 ++ (wordTape V).reverse)
  let D := (C ++ [0] ++ unary V.length ++ blocks [stack,4,2]) ++ [0]
  have hn2 : N 2 = D ++ unary E.length := by
    change L 2 = _
    rw [hsrc,SequentialCursorEdit.blocks_cons]
    simp only [D,List.append_assoc]
  obtain ⟨T2,hc⟩ := discardCurrent_runs E D tail N hn2 (by rw [lastSym_append]; rfl) rfl
    (by simpa [N,Lists.set] using h1) (by simpa [N,Lists.set] using h7) (end_fits hr)
  let M := N.set 4 tail
  have cap : (M 4).length+(M 5).length+2 ≤ B := by simp [M,N,Lists.set,h5]; omega
  have ht := moveAll_runs_bounded (by decide : (5 : Fin 8) ≠ 4) (end_fits hc) cap
  have he : (M.set 4 (M 4 ++ (M 5).reverse)).set 5 [] = L.set 4 (tail ++ wordTape V) := by
    funext j
    by_cases h4 : j=4 <;> by_cases h5j : j=5 <;>
      simp [M,N,Lists.set,h4,h5j,h5]
  rw [he] at ht
  exact ⟨_,hr.seq (hc.seq ht)⟩

private theorem rename_constOK {k m E : Nat} (p : LProg k) (rho : Fin k → Fin m)
    (h : p.ConstOK E) : (p.rename rho).ConstOK E := by
  induction p <;> simp_all [LProg.rename,LProg.ConstOK]

theorem discardCurrent_constOK (E : Nat) : discardCurrent.ConstOK E := by
  exact ⟨SequentialWordRotateMachine.stashAfter_constOK E 0,by simp [clearP,LProg.ConstOK]⟩

theorem preserveReturnWords_constOK (E : Nat) : preserveReturnWords.ConstOK E := by
  exact ⟨rename_constOK _ swap (SequentialWordRotateMachine.stashAfter_constOK E 4),
    discardCurrent_constOK E,by simp [moveAll,moveTop,LProg.ConstOK]⟩

def resultFields : SequentialSharedWords.Value → List Nat
  | .expr r => [3,SequentialReturnPackedMachine.tag r]
  | .args r => [4,SequentialArgConsReturnPackedMachine.resultTag r] ++ SequentialArgConsReturnPackedMachine.extraFields r

def resultWords (v : SequentialSharedWords.Value) : CaptureEnv :=
  SequentialSharedWordSpace.taskWords (.value v)

def wordProgram : SequentialSharedWords.Value → LProg 8
  | .args (some (some _)) => preserveReturnWords
  | _ => discardCurrent

theorem result_words_runs (v : SequentialSharedWords.Value) (E : CaptureEnv) (stack : Nat)
    (controlTail tail : List Nat) (L : Lists 8) {B : Nat}
    (hctrl : L 2 = controlTail ++ blocks (resultFields v) ++ blocks [E.length,stack])
    (hword : L 4 = tail ++ wordTape E ++ wordTape (resultWords v))
    (h1 : L 1 = []) (h5 : L 5 = []) (h7 : L 7 = []) (hL : LenOK B L) :
    ∃ T, Runs (LenOK B) (wordProgram v) L (L.set 4 (tail ++ wordTape (resultWords v))) T := by
  let C := (controlTail ++ blocks (resultFields v) ++ blocks [stack]) ++ [0]
  have hcount : L 2 = C ++ unary E.length := by
    rw [hctrl,blocks_cons E.length [stack]]
    simp only [C,List.append_assoc]
  have hstop : symIs 1 (lastSym C)=false := by rw [lastSym_append]; rfl
  have plain (hn : resultWords v = []) (hp : wordProgram v = discardCurrent) :
      ∃ T, Runs (LenOK B) (wordProgram v) L (L.set 4 (tail ++ wordTape (resultWords v))) T := by
    have he : wordTape (resultWords v) = [] := by rw [hn]; rfl
    rw [hp,he]
    rw [he] at hword
    simp only [List.append_nil] at hword ⊢
    exact discardCurrent_runs E C tail L hcount hstop hword h1 h7 hL
  cases v with
  | expr r => exact plain rfl rfl
  | args r => cases r with
    | none => exact plain rfl rfl
    | some value => cases value with
      | none => exact plain rfl rfl
      | some Vq =>
        rcases Vq with ⟨V,q⟩
        have hc : L 2 = controlTail ++ [0] ++ unary V.length ++ blocks [E.length,stack,4,2] := by
          rw [hctrl]
          change controlTail ++ blocks [4,2,V.length] ++ blocks [E.length,stack] = _
          rw [show [4,2,V.length] = [4,2] ++ [V.length] from rfl,SequentialControlEditMachine.blocks_append]
          rw [show [E.length,stack,4,2] = [E.length,stack] ++ [4,2] from rfl,SequentialControlEditMachine.blocks_append]
          rw [blocks_cons V.length []]
          have hb0 : blocks [] = [] := rfl
          simp only [hb0,List.nil_append,List.append_assoc]
        exact preserveReturnWords_runs E V stack controlTail tail L hc hword h1 h5 h7 hL

theorem wordProgram_constOK (v : SequentialSharedWords.Value) (E : Nat) : (wordProgram v).ConstOK E := by
  cases v with
  | expr _ => exact discardCurrent_constOK E
  | args r => cases r with
    | none => exact discardCurrent_constOK E
    | some value => cases value with
      | none => exact discardCurrent_constOK E
      | some _ => exact preserveReturnWords_constOK E

end Shallot.MacroPeg.CBV.SequentialScopeWordMachine
