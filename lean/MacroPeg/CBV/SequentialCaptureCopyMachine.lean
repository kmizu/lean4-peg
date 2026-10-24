import MacroPeg.CBV.SequentialReturnPackedMachine
import MacroPeg.CBVtoCBN.SpanValues

/-! Read a captured substring from the original input using the compressed
cursor stream itself as the counter. No decoded position or substring is
provided to the program. Input and cursor streams are restored afterwards. -/
namespace Shallot.MacroPeg.CBV.SequentialCaptureCopyMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine

/-- Input characters live on tape 6 in their original order, encoded by
positive symbols; tape 5 temporarily holds the traversed input suffix. -/
def destination (copy : Bool) (D U : List Nat) : List Nat :=
  if copy then D ++ U.reverse else D

def transferBody (copy : Bool) : LProg 8 :=
  .seq (moveTop 0 1) (.seq (if copy then .copy 6 4 else skipP 4) (moveTop 6 5))

def transfer (copy : Bool) : LProg 8 := .loop 0 (symIs 1) (transferBody copy)

private theorem one_runs (copy : Bool) (C S : List Nat) (v : Nat) (L : Lists 8)
    {B : Nat} (hcount : L 0 = C ++ [1]) (hinput : L 6 = S ++ [v]) (hL : LenOK B L)
    (hc : (L 1).length+3 ≤ B) (hi : (L 5).length+3 ≤ B)
    (hw : copy=true → (L 4).length+3 ≤ B) :
    ∃ T, Runs (LenOK B) (transferBody copy) L
      (((((L.set 0 C).set 1 (L 1 ++ [1])).set 6 S).set 5 (L 5 ++ [v])).set 4
        (destination copy (L 4) [v])) T := by
  obtain ⟨hq,hN⟩ := lenOK_moveTop hL (by decide : (0 : Fin 8) ≠ 1) hc
  have hr := runs_moveTop (by decide : (0 : Fin 8) ≠ 1) hL hq hN
  let N := (L.set 0 C).set 1 (L 1 ++ [1])
  have heN : L.moveTop 0 1 = N := by
    funext i
    by_cases h0 : i=0 <;> by_cases h1 : i=1 <;>
      simp_all [N,Lists.moveTop,Lists.set]
  rw [heN] at hr hN
  let M := N.set 4 (destination copy (L 4) [v])
  have hm : ∃ T, Runs (LenOK B) (if copy then .copy 6 4 else skipP 4) N M T := by
    cases copy with
    | false =>
      have he : M=N := by
        have hh : N 4 = L 4 := rfl
        simpa only [M,destination,Bool.false_eq_true,if_false,← hh] using Lists.set_get_self N 4
      rw [he]
      exact ⟨1,runs_skip 4 hN⟩
    | true =>
      have hM : LenOK B M := by
        apply lenOK_set hN 4
        simpa [destination] using hw rfl
      have hp := runs_copy (i := (6 : Fin 8)) (j := 4) (by decide) hN (by
        have he : N.set 4 (N 4 ++ (N 6).getLast?.toList) = M := by
          simp [N,M,destination,Lists.set,hinput]
        rw [he]; exact hM)
      have he : N.set 4 (N 4 ++ (N 6).getLast?.toList) = M := by
        simp [N,M,destination,Lists.set,hinput]
      rw [he] at hp
      exact ⟨1,hp⟩
  obtain ⟨Tm,hm⟩ := hm
  have hM := end_fits hm
  have hm5 : M 5 = L 5 := rfl
  obtain ⟨hrq,hR⟩ := lenOK_moveTop hM (by decide : (6 : Fin 8) ≠ 5) (by simpa [hm5] using hi)
  have ht := runs_moveTop (by decide : (6 : Fin 8) ≠ 5) hM hrq hR
  have he : M.moveTop 6 5 =
      (((((L.set 0 C).set 1 (L 1 ++ [1])).set 6 S).set 5 (L 5 ++ [v])).set 4
        (destination copy (L 4) [v])) := by
    funext i
    by_cases h0 : i=0 <;> by_cases h1 : i=1 <;> by_cases h6 : i=6 <;>
      by_cases h5 : i=5 <;> by_cases h4 : i=4 <;>
      simp_all [M,N,Lists.moveTop,Lists.set]
  rw [he] at ht
  exact ⟨_,hr.seq (hm.seq ht)⟩

private theorem reverse_induction {P : List Nat → Prop} (nil : P [])
    (snoc : ∀ U v, P U → P (U ++ [v])) (U : List Nat) : P U := by
  have h : ∀ V : List Nat, P V.reverse := by
    intro V
    induction V with
    | nil => exact nil
    | cons v V ih => simpa only [List.reverse_cons] using snoc V.reverse v ih
  simpa only [List.reverse_reverse] using h U.reverse

/-- Transfer one source character per unary counter bit. With `copy=true`,
also append it to the word tape. The loop count is read from the cursor tape. -/
theorem transfer_runs (copy : Bool) (C S U : List Nat) (L : Lists 8) {B : Nat}
    (hcount : L 0 = C ++ unary U.length) (hstop : symIs 1 (lastSym C)=false)
    (hinput : L 6 = S ++ U) (hL : LenOK B L)
    (hc : (L 1).length+U.length+2 ≤ B) (hi : (L 5).length+U.length+2 ≤ B)
    (hw : copy=true → (L 4).length+U.length+2 ≤ B) :
    ∃ T, Runs (LenOK B) (transfer copy) L
      (((((L.set 0 C).set 1 (L 1 ++ unary U.length)).set 6 S).set 5 (L 5 ++ U.reverse)).set 4
        (destination copy (L 4) U)) T := by
  induction U using reverse_induction generalizing L with
  | nil =>
    have he : (((((L.set 0 C).set 1 (L 1 ++ unary 0)).set 6 S).set 5
        (L 5 ++ [].reverse)).set 4 (destination copy (L 4) [])) = L := by
      simp only [List.length_nil,List.replicate_zero,List.append_nil,List.reverse_nil] at *
      rw [← hcount,Lists.set_get_self,Lists.set_get_self,← hinput,Lists.set_get_self,
        Lists.set_get_self]
      cases copy <;> simp [destination,Lists.set_get_self]
    simp only [List.length_nil]
    rw [he]
    exact ⟨1,1,by omega,.loopF hL (by simpa [hcount] using hstop)⟩
  | snoc U v ih =>
    have hcounter : L 0 = (C ++ unary U.length) ++ [1] := by
      simpa only [List.length_append,List.length_singleton,List.replicate_succ',List.append_assoc] using hcount
    have hsource : L 6 = (S ++ U) ++ [v] := by simpa only [List.append_assoc] using hinput
    obtain ⟨Tb,hb⟩ := one_runs copy (C ++ unary U.length) (S ++ U) v L hcounter hsource hL
      (by simp only [List.length_append,List.length_singleton] at hc; omega)
      (by simp only [List.length_append,List.length_singleton] at hi; omega)
      (by intro ht; have hh := hw ht; simp only [List.length_append,List.length_singleton] at hh; omega)
    let M := (((((L.set 0 (C ++ unary U.length)).set 1 (L 1 ++ [1])).set 6 (S ++ U)).set 5
      (L 5 ++ [v])).set 4 (destination copy (L 4) [v]))
    have hM : LenOK B M := end_fits hb
    have hm0 : M 0 = C ++ unary U.length := rfl
    have hm6 : M 6 = S ++ U := rfl
    have hm1 : M 1 = L 1 ++ [1] := rfl
    have hm5 : M 5 = L 5 ++ [v] := rfl
    have hm4 : M 4 = destination copy (L 4) [v] := rfl
    obtain ⟨Ti,ht⟩ := ih M hm0 hm6 hM
      (by rw [hm1]; simp only [List.length_append,List.length_singleton] at hc ⊢; omega)
      (by rw [hm5]; simp only [List.length_append,List.length_singleton] at hi ⊢; omega)
      (by intro hh; rw [hm4]; have hhw := hw hh
          simp only [hh,destination,if_true,List.length_append,List.length_singleton,
            List.length_reverse] at hhw ⊢; omega)
    have he : (((((M.set 0 C).set 1 (M 1 ++ unary U.length)).set 6 S).set 5 (M 5 ++ U.reverse)).set 4
        (destination copy (M 4) U)) =
      (((((L.set 0 C).set 1 (L 1 ++ unary (U ++ [v]).length)).set 6 S).set 5
        (L 5 ++ (U ++ [v]).reverse)).set 4 (destination copy (L 4) (U ++ [v]))) := by
      funext i
      by_cases h0 : i=0 <;> by_cases h1 : i=1 <;> by_cases h6 : i=6 <;>
        by_cases h5 : i=5 <;> by_cases h4 : i=4 <;> cases copy <;>
        simp_all [M,Lists.set,destination,List.reverse_append,List.replicate_succ,List.append_assoc]
    rw [he] at ht
    obtain ⟨t1,ht1,hx1⟩ := hb
    obtain ⟨t2,ht2,hx2⟩ := ht
    exact ⟨t1+1+t2,t1+1+t2,by omega,.loopC hL (by rw [hcounter,lastSym_append]; rfl) hx1 hx2⟩

/-- Skip the current suffix, copy the preceding consumed interval as one
terminated word, and restore both the original input and cursor streams. -/
def program : LProg 8 := .seq (transfer false) (.seq (moveTop 0 1)
  (.seq (.push 4 0) (.seq (transfer true) (.seq (moveAll 1 0) (moveAll 5 6)))))

/-- The input decomposition is only a specification of the actual symbols on
tape 6. The same fixed program handles every length and every character list. -/
theorem capture_runs (A U Q rest : List Nat) (L : Lists 8) {B : Nat}
    (hcursor : L 0 = rest ++ [0] ++ unary U.length ++ [0] ++ unary Q.length)
    (hinput : L 6 = (A ++ U) ++ Q) (h1 : L 1 = []) (h5 : L 5 = []) (hL : LenOK B L)
    (hword : (L 4).length+U.length+3 ≤ B) :
    ∃ T, Runs (LenOK B) program L (L.set 4 (L 4 ++ [0] ++ U.reverse)) T := by
  have hc := hL 0
  rw [hcursor] at hc
  simp only [List.length_append,List.length_singleton,List.length_replicate] at hc
  have hi := hL 6
  rw [hinput] at hi
  simp only [List.length_append] at hi
  have hs : L 0 = (rest ++ [0] ++ unary U.length ++ [0]) ++ unary Q.length := hcursor
  obtain ⟨T1,hr⟩ := transfer_runs false (rest ++ [0] ++ unary U.length ++ [0]) (A ++ U) Q L
    hs (by rw [lastSym_append]; rfl) hinput hL
    (by simp only [h1,List.length_nil]; omega)
    (by simp only [h5,List.length_nil]; omega) (by intro hh; contradiction)
  let N := (((((L.set 0 (rest ++ [0] ++ unary U.length ++ [0])).set 1 (unary Q.length)).set 6
    (A ++ U)).set 5 Q.reverse).set 4 (L 4))
  have heN : (((((L.set 0 (rest ++ [0] ++ unary U.length ++ [0])).set 1
      (L 1 ++ unary Q.length)).set 6 (A ++ U)).set 5 (L 5 ++ Q.reverse)).set 4
        (destination false (L 4) Q)) = N := by simp [N,h1,h5,destination]
  rw [heN] at hr
  have hN := end_fits hr
  obtain ⟨hq,hM⟩ := lenOK_moveTop hN (by decide : (0 : Fin 8) ≠ 1)
    (by simp [N,Lists.set]; omega)
  have hm := runs_moveTop (by decide : (0 : Fin 8) ≠ 1) hN hq hM
  let M := (N.set 0 (rest ++ [0] ++ unary U.length)).set 1 (unary Q.length ++ [0])
  have hn0 : N 0 = (rest ++ [0] ++ unary U.length) ++ [0] := rfl
  have hn1 : N 1 = unary Q.length := rfl
  have heM : N.moveTop 0 1 = M := by
    simp only [Lists.moveTop,hn0,List.getLast?_concat,Option.toList_some,List.dropLast_concat]
    funext i
    by_cases h0 : i=0 <;> by_cases h1i : i=1 <;>
      simp_all [M,Lists.set]

  rw [heM] at hm hM
  let D := M.set 4 (L 4 ++ [0])
  have hD : LenOK B D := by
    apply lenOK_set hM 4
    simp only [List.length_append,List.length_singleton]
    omega
  have hp := runs_push (i := (4 : Fin 8)) (e := 0) hM (by
    change LenOK B (M.set 4 (M 4 ++ [0])); exact hD)
  have heD : M.set 4 (M 4 ++ [0]) = D := rfl
  rw [heD] at hp
  have hd0 : D 0 = (rest ++ [0]) ++ unary U.length := rfl
  have hd6 : D 6 = A ++ U := rfl
  obtain ⟨T2,hw⟩ := transfer_runs true (rest ++ [0]) A U D hd0
    (by simp [lastSym_append,symIs]) hd6 hD
    (by simp [D,M,N,Lists.set]; omega)
    (by simp [D,M,N,Lists.set]; omega)
    (by intro _; simp only [D,Lists.set_same,List.length_append,List.length_singleton]; omega)
  let R := (((((D.set 0 (rest ++ [0])).set 1 (D 1 ++ unary U.length)).set 6 A).set 5
    (D 5 ++ U.reverse)).set 4 (destination true (D 4) U))
  have hR : LenOK B R := end_fits hw
  have hbound0 : (R 0).length+(R 1).length+2 ≤ B := by
    simp [R,D,M,N,Lists.set]
    omega
  have hr0 := moveAll_runs_bounded (by decide : (1 : Fin 8) ≠ 0) hR hbound0
  let F := (R.set 0 (R 0 ++ (R 1).reverse)).set 1 []
  have hF : LenOK B F := end_fits hr0
  have hbound6 : (F 6).length+(F 5).length+2 ≤ B := by
    simp [F,R,D,M,N,Lists.set]
    omega
  have hr6 := moveAll_runs_bounded (by decide : (5 : Fin 8) ≠ 6) hF hbound6
  have hout : (F.set 6 (F 6 ++ (F 5).reverse)).set 5 [] =
      L.set 4 (L 4 ++ [0] ++ U.reverse) := by
    funext i
    by_cases h0 : i=0 <;> by_cases h1i : i=1 <;> by_cases h6 : i=6 <;>
      by_cases h5i : i=5 <;> by_cases h4 : i=4 <;>
      simp_all [F,R,D,M,N,Lists.set,destination,List.reverse_append,List.append_assoc]
  rw [hout] at hr6
  exact ⟨_,hr.seq (hm.seq (hp.seq (hw.seq (hr0.seq hr6))))⟩

def character (c : Char) : Nat := c.toNat+1

def characters (w : List Char) : List Nat := w.map character

def wordCode (w : List Char) : List Nat := [0] ++ (characters w).reverse

def wordSymbol : Option Char → Nat
  | none => 0
  | some c => character c

/-- The word produced by the copier is exactly one word of the existing
retained-word codec, including its delimiter and character order. -/
theorem wordCode_encode (w : List Char) (W : SequentialSharedWords.CaptureEnv) :
    ((SequentialSharedWordSpace.encodeWords (w :: W)).map wordSymbol).reverse =
      ((SequentialSharedWordSpace.encodeWords W).map wordSymbol).reverse ++ wordCode w := by
  simp [SequentialSharedWordSpace.encodeWords,wordCode,characters,wordSymbol,
    List.reverse_append,List.map_map,Function.comp_def,List.append_assoc]

theorem pre_length (x : List Char) {p q : Nat} (hp : p ≤ x.length) :
    (pre x p q).length = p-q := by
  rw [pre,List.length_take,length_sfx x hp,Nat.min_eq_left (Nat.sub_le p q)]

/-- A single fixed program extracts the exact original-input capture, using
only the first two difference-encoded cursor blocks as runtime counts. -/
theorem original_input_runs (x : List Char) (p q : Nat) (ps : List Nat) (hp : p ≤ x.length)
    (hqp : q ≤ p) (L : Lists 8) {B : Nat}
    (hcursor : L 0 = cursors (q :: p :: ps)) (hinput : L 6 = characters x)
    (h1 : L 1 = []) (h5 : L 5 = []) (hL : LenOK B L)
    (hword : (L 4).length+(pre x p q).length+3 ≤ B) :
    ∃ T, Runs (LenOK B) program L (L.set 4 (L 4 ++ wordCode (pre x p q))) T := by
  have hq : q ≤ x.length := by omega
  let A := characters (x.take (x.length-p))
  let U := characters (pre x p q)
  let Q := characters (sfx x q)
  have hU : U.length = p-q := by simpa [U,characters] using pre_length x hp
  have hQ : Q.length = q := by simp [Q,characters,length_sfx x hq]
  have hx : x = (x.take (x.length-p) ++ pre x p q) ++ sfx x q := by
    have hh := List.take_append_drop (x.length-p) x
    change x.take (x.length-p) ++ sfx x p = x at hh
    rw [CBVtoCBN.pre_suffix_split x p q hp hqp] at hh
    simpa only [List.append_assoc] using hh.symm
  have hin : L 6 = (A ++ U) ++ Q := by
    rw [hinput]
    dsimp only [A,U,Q,characters]
    rw [← List.map_append,← List.map_append,← hx]
  have hcur : L 0 = blocks (SequentialCursorChain.deltas p ps) ++ [0] ++ unary U.length ++
      [0] ++ unary Q.length := by
    rw [hcursor,cursors_cons,hU,hQ]
    simp only [SequentialCursorChain.deltas,blocks_cons,List.append_assoc]
  obtain ⟨T,hr⟩ := capture_runs A U Q (blocks (SequentialCursorChain.deltas p ps)) L
    hcur hin h1 h5 hL (by simpa [U,characters] using hword)
  exact ⟨T,by simpa only [U,wordCode,List.append_assoc] using hr⟩

/-- Covers the underlying compiled tape execution, including all temporary
copies of the traversed suffix and both restored source streams. -/
theorem original_input_tape (x : List Char) (p q : Nat) (ps : List Nat)
    (hp : p ≤ x.length) (hqp : q ≤ p) (L : Lists 8) {B : Nat}
    (hcursor : L 0 = cursors (q :: p :: ps)) (hinput : L 6 = characters x)
    (h1 : L 1 = []) (h5 : L 5 = []) (hL : LenOK B L)
    (hword : (L 4).length+(pre x p q).length+3 ≤ B)
    (τ : Tapes 8) (hrep : Rep L τ) :
    ∃ t τ', Exec (TFits B) program.compile τ t (.cont τ') ∧
      Rep (L.set 4 (L 4 ++ wordCode (pre x p q))) τ' := by
  obtain ⟨T,hr⟩ := original_input_runs x p q ps hp hqp L hcursor hinput h1 h5 hL hword
  exact tape_runs hr τ hrep

theorem finite_alphabet (E : Nat) (hE : 2 ≤ E) : program.compile.SymOK (E+4) := by
  apply compile_symOK E
  simp [program,transfer,transferBody,skipP,moveTop,moveAll,LProg.ConstOK]
  omega

/-- Add the unchanged original input to the six packed-state tapes. Tape 7
is reserved for the environment prefix needed by the eventual splice. -/
def withInput (packed : SequentialSharedStateCodec.Packed) (x : List Char) : Lists 8 := fun i =>
  if h : i.val < 6 then SequentialCursorEntryMachine.layout packed ⟨i.val,h⟩
  else if i=6 then characters x else []

theorem withInput_fits (packed : SequentialSharedStateCodec.Packed) (x : List Char) {B : Nat}
    (hp : packed.length+2 ≤ B) (hx : x.length+2 ≤ B) : LenOK B (withInput packed x) := by
  have hl := SequentialCursorEntryMachine.layout_fits packed hp
  intro i
  unfold withInput
  split
  · exact hl _
  · split
    · simpa [characters] using hx
    · simp; omega

private theorem layout_word_length (packed : SequentialSharedStateCodec.Packed) :
    (SequentialCursorEntryMachine.layout packed 4).length ≤ packed.length := by
  simp [SequentialCursorEntryMachine.layout]
  unfold SequentialSharedStateCodec.Packed.length
  omega

/-- A reachable encoded state plus its original input supplies all runtime
counts. The temporary capture buffer and all source copies use linear space.
This appends the word to the word tape; relocating it below the current
environment is a separate splice obligation, not a claim of a full Seq step. -/
theorem reachable_buffer_runs (g : MGrammar) (x : List Char) (e : MExp)
    (c : SequentialSharedWords.Config) (h : SequentialSharedWords.Runs g x
      (SequentialSharedWords.initial g x e) c)
    (p q : Nat) (ps : List Nat) (hpos : SequentialSharedCursors.positions c = q :: p :: ps) :
    ∃ T, Runs (LenOK ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3)) program
      (withInput (SequentialSharedStateCodec.encode (CBVtoCBN.compilerNodes g e) c) x)
      ((withInput (SequentialSharedStateCodec.encode (CBVtoCBN.compilerNodes g e) c) x).set 4
        (withInput (SequentialSharedStateCodec.encode (CBVtoCBN.compilerNodes g e) c) x 4 ++
          wordCode (pre x p q))) T := by
  let packed := SequentialSharedStateCodec.encode (CBVtoCBN.compilerNodes g e) c
  let B := (SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3
  have hb := SequentialSharedStateBound.encoded_state_linear g x e c h
  change packed.length ≤ _ at hb
  have hc := SequentialSharedCursors.reachable_chain g x e c h
  rw [hpos] at hc
  cases hc with
  | cons hz ht => cases ht with
    | cons hqp htail =>
      have hp : p ≤ x.length := htail.bound
      have hp' : packed.length+2 ≤ B := by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega
      have hx : x.length+2 ≤ B := by dsimp [B]; rw [Nat.add_mul,Nat.one_mul]; omega
      have hL := withInput_fits packed x hp' hx
      have hcursor : withInput packed x 0 = cursors (q :: p :: ps) := by
        change SequentialCursorEntryMachine.layout packed 0 = _
        rw [SequentialCursorEntryMachine.layout_cursors,hpos]
      have hw := layout_word_length packed
      have hpre : (pre x p q).length ≤ x.length := by rw [pre_length x hp]; omega
      have hword : (withInput packed x 4).length+(pre x p q).length+3 ≤ B := by
        change (SequentialCursorEntryMachine.layout packed 4).length+_+3 ≤ B
        dsimp [B]
        rw [Nat.add_mul,Nat.one_mul]
        omega
      exact original_input_runs x p q ps hp hqp (withInput packed x) hcursor rfl rfl rfl hL hword

theorem reachable_buffer_tape (g : MGrammar) (x : List Char) (e : MExp)
    (c : SequentialSharedWords.Config) (h : SequentialSharedWords.Runs g x
      (SequentialSharedWords.initial g x e) c)
    (p q : Nat) (ps : List Nat) (hpos : SequentialSharedCursors.positions c = q :: p :: ps)
    (τ : Tapes 8) (hrep : Rep
      (withInput (SequentialSharedStateCodec.encode (CBVtoCBN.compilerNodes g e) c) x) τ) :
    ∃ t τ', Exec (TFits ((SequentialSharedStateBound.linearFactor g e+1)*(x.length+1)+3))
      program.compile τ t (.cont τ') ∧ Rep
      ((withInput (SequentialSharedStateCodec.encode (CBVtoCBN.compilerNodes g e) c) x).set 4
        (withInput (SequentialSharedStateCodec.encode (CBVtoCBN.compilerNodes g e) c) x 4 ++
          wordCode (pre x p q))) τ' := by
  obtain ⟨T,hr⟩ := reachable_buffer_runs g x e c h p q ps hpos
  exact tape_runs hr τ hrep

def wordTape (W : SequentialSharedWords.CaptureEnv) : List Nat :=
  ((SequentialSharedWordSpace.encodeWords W).map wordSymbol).reverse

theorem wordTape_append (E W : SequentialSharedWords.CaptureEnv) :
    wordTape (E ++ W) = wordTape W ++ wordTape E := by
  have he : SequentialSharedWordSpace.encodeWords (E ++ W) =
      SequentialSharedWordSpace.encodeWords E ++ SequentialSharedWordSpace.encodeWords W := by
    induction E with
    | nil => rfl
    | cons w E ih => simp [SequentialSharedWordSpace.encodeWords,ih,List.append_assoc]
  simp only [wordTape,he,List.map_append,List.reverse_append]

/-- The complete argument-head successor requires insertion *below* the
current environment. This identifies the remaining splice precisely. -/
theorem argHead_word_target (ns : List CBVtoCBN.CompileNode) (x : List Char) (m p q : Nat)
    (E : SequentialSharedWords.CaptureEnv) (es : List MExp) (K : List SequentialSharedWords.Frame) :
    SequentialCursorEntryMachine.layout (SequentialSharedStateCodec.encode ns
      ⟨m,.args es q,E,.argCons (pre x p q) :: K⟩) 4 =
      wordTape (K.flatMap SequentialSharedWordSpace.frameWords) ++ wordCode (pre x p q) ++ wordTape E := by
  change ((SequentialSharedStateCodec.encode ns
    ⟨m,.args es q,E,.argCons (pre x p q) :: K⟩).words.map wordSymbol).reverse = _
  have he : (SequentialSharedStateCodec.encode ns
      ⟨m,.args es q,E,.argCons (pre x p q) :: K⟩).words =
      SequentialSharedWordSpace.encodeWords (E ++ pre x p q :: K.flatMap SequentialSharedWordSpace.frameWords) := by
    simp [SequentialSharedStateCodec.encode,SequentialSharedStateCodec.write_words,
      SequentialSharedWordSpace.retainedWords,SequentialSharedWordSpace.taskWords,
      SequentialSharedWordSpace.frameWords]
  rw [he]
  change wordTape (E ++ pre x p q :: K.flatMap SequentialSharedWordSpace.frameWords) = _
  rw [wordTape_append]
  simp only [wordTape,wordCode_encode,List.append_assoc]

theorem character_bound (c : Char) : character c < 0x110001 := by
  have hc := c.valid
  change c.toNat < 0xd800 ∨ (0xdfff < c.toNat ∧ c.toNat < 0x110000) at hc
  unfold character
  omega

end Shallot.MacroPeg.CBV.SequentialCaptureCopyMachine
