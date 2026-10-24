import MacroPeg.CBV.SequentialArgHeadPackedMachine

/-! Runtime word-prefix rotation for assembling captured arguments. -/
namespace Shallot.MacroPeg.CBV.SequentialWordRotateMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialControlEditMachine
open SequentialCaptureSpliceMachine
open SequentialCaptureCopyMachine (wordTape wordCode characters)
open SequentialSharedWords (CaptureEnv)

/-- Skip a source-fixed number of control fields, use the next unary field
to save complete words, and restore every control field. -/
def stashAfter (saved : Nat) : LProg 8 :=
  .seq (saveMany 2 1 saved) (.seq saveEnv (moveAll 1 2))

theorem stashAfter_runs (saved : List Nat) (W : CaptureEnv) (C tail : List Nat) (L : Lists 8)
    {B : Nat} (hsrc : L 2 = C ++ unary W.length ++ blocks saved)
    (hstop : symIs 1 (lastSym C)=false) (hword : L 4 = tail ++ wordTape W)
    (h1 : L 1 = []) (hL : LenOK B L) (hcap : (L 7).length+(wordTape W).length+2 ≤ B) :
    ∃ T, Runs (LenOK B) (stashAfter saved.length) L
      ((L.set 4 tail).set 7 (L 7 ++ (wordTape W).reverse)) T := by
  have hc := hL 2
  rw [hsrc] at hc
  simp only [List.length_append,List.length_replicate] at hc
  obtain ⟨T1,hr⟩ := saveMany_runs (src := (2 : Fin 8)) (tmp := 1) (by decide) saved
    (C ++ unary W.length) L hsrc hL (by simp only [h1,List.length_nil]; omega)
  let N := (L.set 2 (C ++ unary W.length)).set 1 (blocks saved).reverse
  have hn : (L.set 2 (C ++ unary W.length)).set 1 (L 1 ++ (blocks saved).reverse) = N := by simp [N,h1]
  rw [hn] at hr
  have hN := end_fits hr
  obtain ⟨T2,hs⟩ := saveEnv_runs W C tail N (by rfl) hstop
    (by simpa [N,Lists.set] using hword) hN
    (by simp [N]; omega) (by simpa [N,Lists.set] using hcap)
  let M := (((N.set 2 C).set 1 (N 1 ++ unary W.length)).set 4 tail).set 7
    (N 7 ++ (wordTape W).reverse)
  have hM : LenOK B M := end_fits hs
  have hb : (M 2).length+(M 1).length+2 ≤ B := by simp [M,N,Lists.set]; omega
  have ht := moveAll_runs_bounded (by decide : (1 : Fin 8) ≠ 2) hM hb
  have he : (M.set 2 (M 2 ++ (M 1).reverse)).set 1 [] =
      (L.set 4 tail).set 7 (L 7 ++ (wordTape W).reverse) := by
    funext i
    by_cases h2 : i=2 <;> by_cases h1i : i=1 <;> by_cases h4 : i=4 <;> by_cases h7 : i=7 <;>
      simp_all [M,N,Lists.set,List.reverse_append,List.append_assoc]
  rw [he] at ht
  exact ⟨_,hr.seq (hs.seq ht)⟩

/-- Increment a unary field below a fixed number of saved control fields. -/
def incrementAfter (saved : Nat) : LProg 8 :=
  .seq (saveMany 2 1 saved) (.seq (.push 2 1) (moveAll 1 2))

theorem incrementAfter_runs (saved : List Nat) (n : Nat) (C : List Nat) (L : Lists 8)
    {B : Nat} (hsrc : L 2 = C ++ unary n ++ blocks saved) (h1 : L 1 = []) (hL : LenOK B L)
    (hcap : (C ++ unary (n+1) ++ blocks saved).length+2 ≤ B) :
    ∃ T, Runs (LenOK B) (incrementAfter saved.length) L
      (L.set 2 (C ++ unary (n+1) ++ blocks saved)) T := by
  have hc := hL 2
  rw [hsrc] at hc
  simp only [List.length_append,List.length_replicate] at hc hcap
  obtain ⟨T1,hr⟩ := saveMany_runs (src := (2 : Fin 8)) (tmp := 1) (by decide) saved
    (C ++ unary n) L hsrc hL (by simp only [h1,List.length_nil]; omega)
  let N := (L.set 2 (C ++ unary n)).set 1 (blocks saved).reverse
  have hn : (L.set 2 (C ++ unary n)).set 1 (L 1 ++ (blocks saved).reverse) = N := by simp [N,h1]
  rw [hn] at hr
  have hN := end_fits hr
  have hp := runs_push (i := (2 : Fin 8)) (e := 1) hN (by
    apply lenOK_set hN 2
    simp [N,Lists.set]
    omega)
  let M := N.set 2 (N 2 ++ [1])
  have hM : LenOK B M := end_fits hp
  have hb : (M 2).length+(M 1).length+2 ≤ B := by simp [M,N,Lists.set]; omega
  have ht := moveAll_runs_bounded (by decide : (1 : Fin 8) ≠ 2) hM hb
  have he : (M.set 2 (M 2 ++ (M 1).reverse)).set 1 [] =
      L.set 2 (C ++ unary (n+1) ++ blocks saved) := by
    funext i
    by_cases h2 : i=2 <;> by_cases h1i : i=1 <;>
      simp_all [M,N,Lists.set,List.replicate_succ',List.append_assoc]
  rw [he] at ht
  exact ⟨_,hr.seq (hp.seq ht)⟩

private theorem code_length (w : List Char) : (wordCode w).length = w.length+1 := by
  simp [wordCode,characters]

def program : LProg 8 := .seq (stashAfter 4) (.seq (stashAfter 0)
  (.seq (moveWord 4 5) (.seq (moveAll 7 4) (moveAll 5 4))))

/-- Rotate the actual captured word above both environments, preserving the
input, cursor, control stream, and all scratch. No environment size is decoded. -/
theorem rotate_runs (E W : CaptureEnv) (w : List Char) (stack : Nat) (C tail : List Nat)
    (L : Lists 8) {B : Nat}
    (hcontrol : L 2 = C ++ [0] ++ unary W.length ++ blocks [E.length,stack,4,2])
    (hword : L 4 = tail ++ wordCode w ++ wordTape E ++ wordTape W)
    (h1 : L 1 = []) (h5 : L 5 = []) (h7 : L 7 = []) (hL : LenOK B L) :
    ∃ T, Runs (LenOK B) program L
      (L.set 4 (tail ++ wordTape E ++ wordTape W ++ wordCode w)) T := by
  have hw := hL 4
  rw [hword] at hw
  simp only [List.length_append,code_length] at hw
  obtain ⟨T1,hr⟩ := stashAfter_runs [E.length,stack,4,2] W (C ++ [0])
    (tail ++ wordCode w ++ wordTape E) L hcontrol (by simp [lastSym_append,symIs])
    hword h1 hL (by simp only [h7,List.length_nil]; omega)
  let N := (L.set 4 (tail ++ wordCode w ++ wordTape E)).set 7 (wordTape W).reverse
  have hn : (L.set 4 (tail ++ wordCode w ++ wordTape E)).set 7 (L 7 ++ (wordTape W).reverse) = N := by simp [N,h7]
  rw [hn] at hr
  have hN := end_fits hr
  let D := (C ++ [0] ++ unary W.length ++ blocks [stack,4,2]) ++ [0]
  have hn2 : N 2 = D ++ unary E.length ++ blocks [] := by
    change L 2 = _
    rw [hcontrol,blocks_cons]
    simp [D,blocks,bits,SequentialCursorChain.encodeDeltas,List.append_assoc]
  obtain ⟨T2,he⟩ := stashAfter_runs [] E D (tail ++ wordCode w) N hn2
    (by rw [lastSym_append]; rfl) (by rfl) (by simpa [N,Lists.set] using h1) hN
    (by simp [N]; omega)
  let M := (N.set 4 (tail ++ wordCode w)).set 7 (N 7 ++ (wordTape E).reverse)
  have hM : LenOK B M := end_fits he
  obtain ⟨T3,hm⟩ := moveWord_runs (src := (4 : Fin 8)) (tmp := 5) (by decide) w tail M rfl hM
    (by simp [M,N,Lists.set,h5]; omega)
  let R := (M.set 4 tail).set 5 (M 5 ++ characters w ++ [0])
  have hR : LenOK B R := end_fits hm
  have hb : (R 4).length+(R 7).length+2 ≤ B := by simp [R,M,N,Lists.set]; omega
  have ht := moveAll_runs_bounded (by decide : (7 : Fin 8) ≠ 4) hR hb
  let F := (R.set 4 (R 4 ++ (R 7).reverse)).set 7 []
  have hF : LenOK B F := end_fits ht
  have hf : (F 4).length+(F 5).length+2 ≤ B := by
    simp [F,R,M,N,Lists.set,h5,characters]
    omega
  have ht2 := moveAll_runs_bounded (by decide : (5 : Fin 8) ≠ 4) hF hf
  have hout : (F.set 4 (F 4 ++ (F 5).reverse)).set 5 [] =
      L.set 4 (tail ++ wordTape E ++ wordTape W ++ wordCode w) := by
    funext i
    by_cases h4 : i=4 <;> by_cases h5i : i=5 <;> by_cases h7i : i=7 <;>
      simp_all [F,R,M,N,Lists.set,wordCode,List.reverse_append,List.append_assoc]
  rw [hout] at ht2
  exact ⟨_,hr.seq (he.seq (hm.seq (ht.seq ht2)))⟩

/-- On a failed argument computation the pending captured word is discarded. -/
def discard : LProg 8 := .seq (stashAfter 0) (.seq (moveWord 4 5)
  (.seq (clearP 5) (moveAll 7 4)))

theorem discard_runs (E : CaptureEnv) (w : List Char) (C tail : List Nat) (L : Lists 8)
    {B : Nat} (hcontrol : L 2 = C ++ unary E.length)
    (hstop : symIs 1 (lastSym C)=false) (hword : L 4 = tail ++ wordCode w ++ wordTape E)
    (h1 : L 1 = []) (h5 : L 5 = []) (h7 : L 7 = []) (hL : LenOK B L) :
    ∃ T, Runs (LenOK B) discard L (L.set 4 (tail ++ wordTape E)) T := by
  have hw := hL 4
  rw [hword] at hw
  simp only [List.length_append,code_length] at hw
  obtain ⟨T1,hr⟩ := stashAfter_runs [] E C (tail ++ wordCode w) L
    (by simpa [blocks,bits,SequentialCursorChain.encodeDeltas] using hcontrol) hstop hword h1 hL
    (by simp only [h7,List.length_nil]; omega)
  let N := (L.set 4 (tail ++ wordCode w)).set 7 (wordTape E).reverse
  have hn : (L.set 4 (tail ++ wordCode w)).set 7 (L 7 ++ (wordTape E).reverse) = N := by simp [N,h7]
  rw [hn] at hr
  obtain ⟨T2,hm⟩ := moveWord_runs (src := (4 : Fin 8)) (tmp := 5) (by decide) w tail N rfl
    (end_fits hr) (by simp [N,Lists.set,h5]; omega)
  let M := (N.set 4 tail).set 5 (N 5 ++ characters w ++ [0])
  have hc := clear_runs (tmp := (5 : Fin 8)) M (end_fits hm)
  let R := M.set 5 []
  have hb : (R 4).length+(R 7).length+2 ≤ B := by simp [R,M,N,Lists.set]; omega
  have ht := moveAll_runs_bounded (by decide : (7 : Fin 8) ≠ 4) (end_fits hc) hb
  have he : (R.set 4 (R 4 ++ (R 7).reverse)).set 7 [] = L.set 4 (tail ++ wordTape E) := by
    funext i
    by_cases h4 : i=4 <;> by_cases h5i : i=5 <;> by_cases h7i : i=7 <;>
      simp_all [R,M,N,Lists.set]
  rw [he] at ht
  exact ⟨_,hr.seq (hm.seq (hc.seq ht))⟩

theorem stashAfter_constOK (E saved : Nat) : (stashAfter saved).ConstOK E := by
  have hs : (saveMany (2 : Fin 8) 1 saved).ConstOK E := by
    induction saved with
    | zero => trivial
    | succ n ih => exact ⟨by simp [moveBlock,scan,moveTop,LProg.ConstOK],ih⟩
  simp [stashAfter,hs,saveEnv,moveWord,scanWord,moveTop,moveAll,LProg.ConstOK]

theorem incrementAfter_constOK (E saved : Nat) (hE : 2 ≤ E) : (incrementAfter saved).ConstOK E := by
  have hs : (saveMany (2 : Fin 8) 1 saved).ConstOK E := by
    induction saved with
    | zero => trivial
    | succ n ih => exact ⟨by simp [moveBlock,scan,moveTop,LProg.ConstOK],ih⟩
  change (saveMany (2 : Fin 8) 1 saved).ConstOK E ∧ 1 < E ∧ True ∧ True
  exact ⟨hs,by omega,trivial,trivial⟩

theorem constOK (E : Nat) : program.ConstOK E := by
  simp [program,stashAfter_constOK,moveWord,scanWord,moveTop,moveAll,LProg.ConstOK]

theorem discard_constOK (E : Nat) : discard.ConstOK E := by
  simp [discard,stashAfter_constOK,moveWord,scanWord,moveTop,moveAll,clearP,LProg.ConstOK]

end Shallot.MacroPeg.CBV.SequentialWordRotateMachine
