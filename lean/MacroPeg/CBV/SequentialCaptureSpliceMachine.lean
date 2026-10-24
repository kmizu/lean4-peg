import MacroPeg.CBV.SequentialCaptureCopyMachine

/-! Save the current environment by reading its unary length header, create
an actual capture from the original input, and restore the environment above
that capture. The header and all scratch are restored without decoding. -/
namespace Shallot.MacroPeg.CBV.SequentialCaptureSpliceMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine
open SequentialCaptureCopyMachine (characters character wordCode wordTape)

variable {k : Nat}

theorem moveLast_runs {src tmp : Fin k} (hd : src ≠ tmp) (S : List Nat) (v : Nat)
    (L : Lists k) {B : Nat} (hsrc : L src = S ++ [v]) (hL : LenOK B L)
    (hcap : (L tmp).length+3 ≤ B) :
    Runs (LenOK B) (moveTop src tmp) L ((L.set src S).set tmp (L tmp ++ [v])) 2 := by
  obtain ⟨hq,hm⟩ := lenOK_moveTop hL hd hcap
  have hr := runs_moveTop hd hL hq hm
  have he : L.moveTop src tmp = (L.set src S).set tmp (L tmp ++ [v]) := by
    simp only [Lists.moveTop,hsrc,List.getLast?_concat,Option.toList_some,List.dropLast_concat]
    funext i
    by_cases hi : i=src <;> by_cases hj : i=tmp <;> simp_all [Lists.set]
  rwa [he] at hr

def isWordChar (s : Nat) : Bool := decide (s ≠ 4)

def scanWord (src tmp : Fin k) : LProg k := .loop src isWordChar (moveTop src tmp)

theorem scanWord_runs {src tmp : Fin k} (hd : src ≠ tmp) (w : List Char) (tail : List Nat)
    (L : Lists k) {B : Nat} (hsrc : L src = tail ++ [0] ++ (characters w).reverse)
    (hL : LenOK B L) (hcap : (L tmp).length+w.length+2 ≤ B) :
    ∃ T, Runs (LenOK B) (scanWord src tmp) L
      ((L.set src (tail ++ [0])).set tmp (L tmp ++ characters w)) T := by
  induction w generalizing L with
  | nil =>
    have he : (L.set src (tail ++ [0])).set tmp (L tmp ++ characters []) = L := by
      have hs : L src = tail ++ [0] := by simpa [characters] using hsrc
      simp [characters,← hs,Lists.set_get_self]
    rw [he]
    exact ⟨1,1,by omega,.loopF hL (by simp [hsrc,characters,lastSym_append,isWordChar])⟩
  | cons c w ih =>
    have hs : L src = (tail ++ [0] ++ (characters w).reverse) ++ [character c] := by
      simpa only [characters,List.map_cons,List.reverse_cons,List.append_assoc] using hsrc
    have hr := moveLast_runs hd _ (character c) L hs hL (by simp only [List.length_cons] at hcap; omega)
    let M := (L.set src (tail ++ [0] ++ (characters w).reverse)).set tmp (L tmp ++ [character c])
    have hM : LenOK B M := end_fits hr
    have hms : M src = tail ++ [0] ++ (characters w).reverse := by simp [M,Lists.set,hd]
    have hmc : (M tmp).length+w.length+2 ≤ B := by
      simp only [M,Lists.set_same,List.length_append,List.length_singleton]
      simp only [List.length_cons] at hcap
      omega
    obtain ⟨T,ht⟩ := ih M hms hM hmc
    have he : (M.set src (tail ++ [0])).set tmp (M tmp ++ characters w) =
        (L.set src (tail ++ [0])).set tmp (L tmp ++ characters (c :: w)) := by
      funext i
      by_cases hi : i=src <;> by_cases hj : i=tmp <;>
        simp_all [M,Lists.set,characters,List.append_assoc]
    rw [he] at ht
    obtain ⟨t1,ht1,hx1⟩ := hr
    obtain ⟨t2,ht2,hx2⟩ := ht
    have hcond : isWordChar (lastSym (L src)) = true := by
      rw [hs,lastSym_append]
      simp [isWordChar,character]
    exact ⟨t1+1+t2,t1+1+t2,by omega,.loopC hL hcond hx1 hx2⟩

def moveWord (src tmp : Fin k) : LProg k := .seq (scanWord src tmp) (moveTop src tmp)

theorem moveWord_runs {src tmp : Fin k} (hd : src ≠ tmp) (w : List Char) (tail : List Nat)
    (L : Lists k) {B : Nat} (hsrc : L src = tail ++ wordCode w)
    (hL : LenOK B L) (hcap : (L tmp).length+w.length+3 ≤ B) :
    ∃ T, Runs (LenOK B) (moveWord src tmp) L
      ((L.set src tail).set tmp (L tmp ++ characters w ++ [0])) T := by
  have hs : L src = tail ++ [0] ++ (characters w).reverse := by
    simpa only [wordCode,List.append_assoc] using hsrc
  obtain ⟨T,hr⟩ := scanWord_runs hd w tail L hs hL (by omega)
  let N := (L.set src (tail ++ [0])).set tmp (L tmp ++ characters w)
  have hN : LenOK B N := end_fits hr
  have hn : N src = tail ++ [0] := by simp [N,Lists.set,hd]
  have hc : (N tmp).length+3 ≤ B := by simpa [N,characters,Nat.add_assoc] using hcap
  have ht := moveLast_runs hd tail 0 N hn hN hc
  have he : (N.set src tail).set tmp (N tmp ++ [0]) =
      (L.set src tail).set tmp (L tmp ++ characters w ++ [0]) := by
    funext i
    by_cases hi : i=src <;> by_cases hj : i=tmp <;> simp_all [N,Lists.set]
  rw [he] at ht
  exact ⟨_,hr.seq ht⟩

theorem wordTape_cons (w : List Char) (E : SequentialSharedWords.CaptureEnv) :
    wordTape (w :: E) = wordTape E ++ wordCode w := SequentialCaptureCopyMachine.wordCode_encode w E

private theorem wordCode_length (w : List Char) : (wordCode w).length = w.length+1 := by
  simp [wordCode,characters]

/-- The control field's unary bits count words, including empty words. Each
word is found from its delimiter; no lengths or words are runtime parameters. -/
def saveEnv : LProg 8 := .loop 2 (symIs 1) (.seq (moveTop 2 1) (moveWord 4 7))

theorem saveEnv_runs (E : SequentialSharedWords.CaptureEnv) (C tail : List Nat) (L : Lists 8)
    {B : Nat} (hcount : L 2 = C ++ unary E.length) (hstop : symIs 1 (lastSym C)=false)
    (hword : L 4 = tail ++ wordTape E) (hL : LenOK B L)
    (hc : (L 1).length+E.length+2 ≤ B) (hw : (L 7).length+(wordTape E).length+2 ≤ B) :
    ∃ T, Runs (LenOK B) saveEnv L
      ((((L.set 2 C).set 1 (L 1 ++ unary E.length)).set 4 tail).set 7
        (L 7 ++ (wordTape E).reverse)) T := by
  induction E generalizing L with
  | nil =>
    have he : (((L.set 2 C).set 1 (L 1 ++ unary 0)).set 4 tail).set 7
        (L 7 ++ (wordTape []).reverse) = L := by
      have hs : L 2 = C := by simpa using hcount
      have ht : L 4 = tail := by simpa [wordTape,SequentialSharedWordSpace.encodeWords] using hword
      simp [wordTape,SequentialSharedWordSpace.encodeWords,← hs,← ht,Lists.set_get_self]
    simp only [List.length_nil]
    rw [he]
    exact ⟨1,1,by omega,.loopF hL (by simpa [hcount] using hstop)⟩
  | cons w E ih =>
    have hs : L 2 = (C ++ unary E.length) ++ [1] := by
      simpa only [List.length_cons,List.replicate_succ',List.append_assoc] using hcount
    have hr := moveLast_runs (by decide : (2 : Fin 8) ≠ 1) _ 1 L hs hL
      (by simp only [List.length_cons] at hc; omega)
    let N := (L.set 2 (C ++ unary E.length)).set 1 (L 1 ++ [1])
    have hN : LenOK B N := end_fits hr
    have hn4 : N 4 = (tail ++ wordTape E) ++ wordCode w := by
      simpa only [N,Lists.set_ne _ _ (by decide : (4 : Fin 8) ≠ 1),
        Lists.set_ne _ _ (by decide : (4 : Fin 8) ≠ 2),wordTape_cons,List.append_assoc] using hword
    have hcap : (N 7).length+w.length+3 ≤ B := by
      have hh := hw
      rw [wordTape_cons,List.length_append,wordCode_length] at hh
      simp [N,Lists.set]
      omega
    obtain ⟨Tw,hm⟩ := moveWord_runs (by decide : (4 : Fin 8) ≠ 7) w (tail ++ wordTape E) N hn4 hN hcap
    let M := (N.set 4 (tail ++ wordTape E)).set 7 (N 7 ++ characters w ++ [0])
    have hM : LenOK B M := end_fits hm
    have hm2 : M 2 = C ++ unary E.length := rfl
    have hm4 : M 4 = tail ++ wordTape E := rfl
    have hm1 : M 1 = L 1 ++ [1] := rfl
    have hm7 : M 7 = L 7 ++ characters w ++ [0] := rfl
    have hmc : (M 1).length+E.length+2 ≤ B := by
      rw [hm1]
      simp only [List.length_append,List.length_cons,List.length_nil] at hc ⊢
      omega
    have hmw : (M 7).length+(wordTape E).length+2 ≤ B := by
      rw [hm7]
      rw [wordTape_cons,List.length_append,wordCode_length] at hw
      simp only [List.length_append,List.length_singleton,characters,List.length_map]
      omega
    obtain ⟨Ti,ht⟩ := ih M hm2 hm4 hM hmc hmw
    have he : (((M.set 2 C).set 1 (M 1 ++ unary E.length)).set 4 tail).set 7
        (M 7 ++ (wordTape E).reverse) =
      (((L.set 2 C).set 1 (L 1 ++ unary (w :: E).length)).set 4 tail).set 7
        (L 7 ++ (wordTape (w :: E)).reverse) := by
      funext i
      by_cases h2 : i=2 <;> by_cases h1 : i=1 <;> by_cases h4 : i=4 <;> by_cases h7 : i=7 <;>
        simp_all [M,N,Lists.set,wordTape_cons,wordCode,characters,
          List.reverse_append,List.replicate_succ,List.append_assoc]
    rw [he] at ht
    obtain ⟨t1,ht1,hx1⟩ := hr.seq hm
    obtain ⟨t2,ht2,hx2⟩ := ht
    exact ⟨t1+1+t2,t1+1+t2,by omega,.loopC hL (by rw [hs,lastSym_append]; rfl) hx1 hx2⟩

def stash : LProg 8 := .seq saveEnv (moveAll 1 2)

theorem stash_runs (E : SequentialSharedWords.CaptureEnv) (C tail : List Nat) (L : Lists 8)
    {B : Nat} (hcount : L 2 = C ++ unary E.length) (hstop : symIs 1 (lastSym C)=false)
    (hword : L 4 = tail ++ wordTape E) (h1 : L 1 = []) (h7 : L 7 = []) (hL : LenOK B L) :
    ∃ T, Runs (LenOK B) stash L ((L.set 4 tail).set 7 (wordTape E).reverse) T := by
  have hc := hL 2
  rw [hcount] at hc
  simp only [List.length_append,List.length_replicate] at hc
  have hw := hL 4
  rw [hword] at hw
  simp only [List.length_append] at hw
  obtain ⟨T1,hr⟩ := saveEnv_runs E C tail L hcount hstop hword hL
    (by simp only [h1,List.length_nil]; omega) (by simp only [h7,List.length_nil]; omega)
  let N := (((L.set 2 C).set 1 (unary E.length)).set 4 tail).set 7 (wordTape E).reverse
  have hn : (((L.set 2 C).set 1 (L 1 ++ unary E.length)).set 4 tail).set 7
      (L 7 ++ (wordTape E).reverse) = N := by simp [N,h1,h7]
  rw [hn] at hr
  have hN := end_fits hr
  have hcap : (N 2).length+(N 1).length+2 ≤ B := by simp [N,Lists.set]; omega
  have ht := moveAll_runs_bounded (by decide : (1 : Fin 8) ≠ 2) hN hcap
  have he : (N.set 2 (N 2 ++ (N 1).reverse)).set 1 [] = (L.set 4 tail).set 7 (wordTape E).reverse := by
    funext i
    by_cases h2 : i=2 <;> by_cases h1i : i=1 <;> by_cases h4 : i=4 <;> by_cases h7i : i=7 <;>
      simp_all [N,Lists.set]
  rw [he] at ht
  exact ⟨_,hr.seq ht⟩

def program : LProg 8 := .seq stash
  (.seq SequentialCaptureCopyMachine.program (moveAll 7 4))

/-- Create the capture beneath the current environment, retaining that
environment's exact words and grouping. The unary header drives the save loop. -/
theorem splice_runs (x : List Char) (p q : Nat) (ps : List Nat)
    (E : SequentialSharedWords.CaptureEnv) (C tail : List Nat) (L : Lists 8) {B : Nat}
    (hp : p ≤ x.length) (hqp : q ≤ p)
    (hcursor : L 0 = cursors (q :: p :: ps)) (hinput : L 6 = characters x)
    (hcount : L 2 = C ++ unary E.length) (hstop : symIs 1 (lastSym C)=false)
    (hword : L 4 = tail ++ wordTape E) (h1 : L 1 = []) (h5 : L 5 = []) (h7 : L 7 = [])
    (hL : LenOK B L) (hfinal : (tail ++ wordCode (pre x p q) ++ wordTape E).length+2 ≤ B) :
    ∃ T, Runs (LenOK B) program L
      (L.set 4 (tail ++ wordCode (pre x p q) ++ wordTape E)) T := by
  obtain ⟨T1,hr⟩ := stash_runs E C tail L hcount hstop hword h1 h7 hL
  let N := (L.set 4 tail).set 7 (wordTape E).reverse
  have hN : LenOK B N := end_fits hr
  have hn0 : N 0 = cursors (q :: p :: ps) := by simp [N,Lists.set,hcursor]
  have hn6 : N 6 = characters x := by simp [N,Lists.set,hinput]
  have hn1 : N 1 = [] := by simp [N,Lists.set,h1]
  have hn5 : N 5 = [] := by simp [N,Lists.set,h5]
  have hcap : (N 4).length+(pre x p q).length+3 ≤ B := by
    simp [N,Lists.set]
    simp only [List.length_append,wordCode_length] at hfinal
    omega
  obtain ⟨T2,hc⟩ := SequentialCaptureCopyMachine.original_input_runs x p q ps hp hqp N hn0 hn6 hn1 hn5 hN hcap
  let M := N.set 4 (N 4 ++ wordCode (pre x p q))
  have hM : LenOK B M := end_fits hc
  have hrestore : (M 4).length+(M 7).length+2 ≤ B := by
    simpa [M,N,Lists.set,List.length_append,Nat.add_assoc] using hfinal
  have ht := moveAll_runs_bounded (by decide : (7 : Fin 8) ≠ 4) hM hrestore
  have he : (M.set 4 (M 4 ++ (M 7).reverse)).set 7 [] =
      L.set 4 (tail ++ wordCode (pre x p q) ++ wordTape E) := by
    funext i
    by_cases h4 : i=4 <;> by_cases h7i : i=7 <;> simp_all [M,N,Lists.set]
  rw [he] at ht
  exact ⟨_,hr.seq (hc.seq ht)⟩

theorem splice_tape (x : List Char) (p q : Nat) (ps : List Nat)
    (E : SequentialSharedWords.CaptureEnv) (C tail : List Nat) (L : Lists 8) {B : Nat}
    (hp : p ≤ x.length) (hqp : q ≤ p)
    (hcursor : L 0 = cursors (q :: p :: ps)) (hinput : L 6 = characters x)
    (hcount : L 2 = C ++ unary E.length) (hstop : symIs 1 (lastSym C)=false)
    (hword : L 4 = tail ++ wordTape E) (h1 : L 1 = []) (h5 : L 5 = []) (h7 : L 7 = [])
    (hL : LenOK B L) (hfinal : (tail ++ wordCode (pre x p q) ++ wordTape E).length+2 ≤ B)
    (τ : Tapes 8) (hrep : Rep L τ) :
    ∃ t τ', Exec (TFits B) program.compile τ t (.cont τ') ∧
      Rep (L.set 4 (tail ++ wordCode (pre x p q) ++ wordTape E)) τ' := by
  obtain ⟨T,hr⟩ := splice_runs x p q ps E C tail L hp hqp hcursor hinput hcount hstop hword h1 h5 h7 hL hfinal
  exact tape_runs hr τ hrep

theorem constOK (E : Nat) (hE : 2 ≤ E) : program.ConstOK E := by
  simp [program,stash,saveEnv,moveWord,scanWord,moveTop,moveAll,
    SequentialCaptureCopyMachine.program,SequentialCaptureCopyMachine.transfer,
    SequentialCaptureCopyMachine.transferBody,skipP,LProg.ConstOK]
  omega

theorem finite_alphabet (E : Nat) (hE : 2 ≤ E) : program.compile.SymOK (E+4) :=
  compile_symOK E program (constOK E hE)

end Shallot.MacroPeg.CBV.SequentialCaptureSpliceMachine
