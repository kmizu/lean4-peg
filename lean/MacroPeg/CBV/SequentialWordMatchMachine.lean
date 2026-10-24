import MacroPeg.CBV.SequentialSymbolDispatchMachine

/-! Runtime prefix matching of an actual captured word against the prepared
original-input suffix. Matching advances the difference-encoded cursor. -/
namespace Shallot.MacroPeg.CBV.SequentialWordMatchMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialCursorDecreaseMachine
open SequentialCaptureSpliceMachine (moveLast_runs)
open SequentialCaptureCopyMachine (characters character)

inductive Trace : List Char → List Char → List Char → List Char → List Char → Prop where
  | nil (X) : Trace [] X [] [] X
  | empty (c w) : Trace (c :: w) [] [] (c :: w) []
  | mismatch (c d w X) (hne : c ≠ d) : Trace (c :: w) (d :: X) [] (c :: w) (d :: X)
  | cons (c) {w X U wr xr} (tail : Trace w X U wr xr) : Trace (c :: w) (c :: X) (c :: U) wr xr

theorem trace_exists (w X : List Char) : ∃ U wr xr, Trace w X U wr xr := by
  induction w generalizing X with
  | nil => exact ⟨[],[],X,.nil X⟩
  | cons c w ih => cases X with
    | nil => exact ⟨[],c :: w,[],.empty c w⟩
    | cons d X =>
      by_cases he : c=d
      · subst d
        obtain ⟨U,wr,xr,ht⟩ := ih X
        exact ⟨c :: U,wr,xr,.cons c ht⟩
      · exact ⟨[],c :: w,d :: X,.mismatch c d w X he⟩

theorem Trace.split {w X U wr xr} (h : Trace w X U wr xr) : w=U++wr ∧ X=U++xr := by
  induction h <;> simp_all

theorem Trace.stripPrefix {w X U wr xr} (h : Trace w X U wr xr) :
    Shallot.stripPrefix? w X = if wr=[] then some xr else none := by
  induction h with
  | nil => rfl
  | empty => rfl
  | mismatch c d w X hne => simp [Shallot.stripPrefix?,Shallot.beqChar,Char.toNat_inj,hne]
  | cons c ht ih => simpa [Shallot.stripPrefix?,Shallot.beqChar] using ih

def stop : LProg 8 := .seq (.pop 2) (.push 2 0)

def advance : LProg 8 := .seq (moveTop 4 7) (.seq (moveTop 5 6) (decrement 0 1))

def body : LProg 8 := .ite 4 (symIs 0) stop (.ite 5 nonEmpty
  (SequentialSymbolDispatchMachine.program 4 5 advance stop 0x110001) stop)

def program : LProg 8 := .loop 2 (symIs 1) body

def output (L : Lists 8) (C tail A P : List Nat) (ps : List Nat) (U wr xr : List Char) : Lists 8 :=
  ((((((L.set 2 (C ++ [0])).set 0 (cursors (xr.length :: ps))).set 4
    (tail ++ [0] ++ (characters wr).reverse)).set 7 (P ++ characters U)).set 5
      (characters xr).reverse).set 6 (A ++ characters U))

theorem stop_runs (C : List Nat) (L : Lists 8) {B : Nat} (hflag : L 2 = C ++ [1]) (hL : LenOK B L) :
    Runs (LenOK B) stop L (L.set 2 (C ++ [0])) 2 := by
  have hh := hL 2
  rw [hflag] at hh
  simp only [List.length_append,List.length_singleton] at hh
  have hp := runs_pop (i := (2 : Fin 8)) hL (by
    apply lenOK_set hL 2
    rw [hflag,List.dropLast_concat]
    omega)
  have he : L.set 2 (L 2).dropLast = L.set 2 C := by rw [hflag,List.dropLast_concat]
  rw [he] at hp
  have hs := runs_push (i := (2 : Fin 8)) (e := 0) (end_fits hp) (by
    apply lenOK_set (end_fits hp) 2
    simp
    omega)
  simpa only [stop,Lists.set_same,Lists.set_set_u] using hp.seq hs

theorem advance_runs (c : Char) (w X : List Char) (ps : List Nat) (n : Nat)
    (hchain : SequentialCursorChain.Chain (X.length+1) ps n) (tail A P : List Nat) (L : Lists 8)
    {B : Nat} (hw : L 4 = tail ++ [0] ++ (characters (c :: w)).reverse)
    (hx : L 5 = (characters (c :: X)).reverse) (ha : L 6 = A) (hp : L 7 = P)
    (hcur : L 0 = cursors ((X.length+1) :: ps)) (h1 : L 1 = []) (hL : LenOK B L)
    (hword : P.length+w.length+3 ≤ B) (hinput : A.length+X.length+3 ≤ B) :
    ∃ T, Runs (LenOK B) advance L
      (((((L.set 4 (tail ++ [0] ++ (characters w).reverse)).set 7 (P ++ [character c])).set 5
        (characters X).reverse).set 6 (A ++ [character c])).set 0 (cursors (X.length :: ps))) T := by
  have h4 : L 4 = (tail ++ [0] ++ (characters w).reverse) ++ [character c] := by
    simpa only [characters,List.map_cons,List.reverse_cons,List.append_assoc] using hw
  have hr1 := moveLast_runs (by decide : (4 : Fin 8) ≠ 7) _ (character c) L h4 hL (by rw [hp]; omega)
  let N := (L.set 4 (tail ++ [0] ++ (characters w).reverse)).set 7 (L 7 ++ [character c])
  have hn5 : N 5 = (characters X).reverse ++ [character c] := by
    simpa only [N,Lists.set_ne _ _ (by decide : (5 : Fin 8) ≠ 7),
      Lists.set_ne _ _ (by decide : (5 : Fin 8) ≠ 4),characters,List.map_cons,List.reverse_cons] using hx
  have hr2 := moveLast_runs (by decide : (5 : Fin 8) ≠ 6) _ (character c) N hn5 (end_fits hr1)
    (by simp [N,Lists.set,ha]; omega)
  let M := (N.set 5 (characters X).reverse).set 6 (N 6 ++ [character c])
  obtain ⟨Td,hd⟩ := decrement_current_runs (src := (0 : Fin 8)) (tmp := 1) (by decide) hchain M
    (by simpa [M,N,Lists.set] using hcur) (by simpa [M,N,Lists.set] using h1) (end_fits hr2)
  have he : M.set 0 (cursors (X.length :: ps)) =
      (((((L.set 4 (tail ++ [0] ++ (characters w).reverse)).set 7 (P ++ [character c])).set 5
        (characters X).reverse).set 6 (A ++ [character c])).set 0 (cursors (X.length :: ps))) := by
    simp [M,N,Lists.set,hp,ha]
  rw [he] at hd
  exact ⟨_,hr1.seq (hr2.seq hd)⟩

private theorem exit_loop {L M : Lists 8} {B T : Nat} (h : Runs (LenOK B) body L M T)
    (hstart : symIs 1 (lastSym (L 2))=true) (hend : symIs 1 (lastSym (M 2))=false) :
    ∃ U, Runs (LenOK B) program L M U := by
  obtain ⟨t,ht,hx⟩ := h
  exact ⟨t+2,t+2,by omega,.loopC hx.q_start hstart hx (.loopF (end_fits ⟨t,ht,hx⟩) hend)⟩

private theorem character_injective : Function.Injective character := by
  intro a b h
  have hh : a.toNat=b.toNat := by unfold character at h; omega
  exact Char.toNat_inj.mp hh

private theorem initial_output (C tail A P : List Nat) (ps : List Nat) (w X : List Char) (L : Lists 8)
    (hcur : L 0 = cursors (X.length :: ps)) (hw : L 4 = tail ++ [0] ++ (characters w).reverse)
    (hx : L 5 = (characters X).reverse) (ha : L 6 = A) (hp : L 7 = P) :
    output L C tail A P ps [] w X = L.set 2 (C ++ [0]) := by
  funext j
  by_cases h0 : j=0 <;> by_cases h2 : j=2 <;> by_cases h4 : j=4 <;>
    by_cases h5 : j=5 <;> by_cases h6 : j=6 <;> by_cases h7 : j=7 <;>
    simp [output,Lists.set,h0,h2,h4,h5,h6,h7,hcur,hw,hx,ha,hp,characters]

/-- The loop reads the captured word and input symbols themselves, and its
only persistent position update is the direct compressed-cursor decrement. -/
theorem loop_runs {w X U wr xr : List Char} (trace : Trace w X U wr xr)
    (ps : List Nat) (n : Nat) (hchain : SequentialCursorChain.Chain X.length ps n)
    (C tail A P : List Nat) (L : Lists 8) {B : Nat}
    (hflag : L 2 = C ++ [1]) (hcur : L 0 = cursors (X.length :: ps))
    (hw : L 4 = tail ++ [0] ++ (characters w).reverse) (hx : L 5 = (characters X).reverse)
    (ha : L 6 = A) (hp : L 7 = P) (h1 : L 1 = []) (hL : LenOK B L)
    (hWcap : P.length+w.length+2 ≤ B) (hXcap : A.length+X.length+2 ≤ B) :
    ∃ T, Runs (LenOK B) program L (output L C tail A P ps U wr xr) T := by
  have hstart : symIs 1 (lastSym (L 2))=true := by rw [hflag,lastSym_append]; rfl
  have hstop : symIs 1 (lastSym ((L.set 2 (C ++ [0])) 2))=false := by
    simp only [Lists.set_same,lastSym_append]
    rfl
  induction trace generalizing L A P with
  | nil X =>
    have hr := stop_runs C L hflag hL
    have hb : Runs (LenOK B) body L (L.set 2 (C ++ [0])) 3 := by
      apply Runs.iteT hL
      · simpa only [hw,characters,List.map_nil,List.reverse_nil,List.append_nil,lastSym_append] using (by decide : symIs 0 4=true)
      · exact hr
    obtain ⟨T,ht⟩ := exit_loop hb hstart hstop
    rw [initial_output C tail A P ps [] X L hcur hw hx ha hp]
    exact ⟨T,ht⟩
  | empty c w =>
    have hr := stop_runs C L hflag hL
    have hword : symIs 0 (lastSym (L 4))=false := by
      rw [hw]
      simp only [characters,List.map_cons,List.reverse_cons,← List.append_assoc,lastSym_append]
      simp [symIs,character]
    have hinput : nonEmpty (lastSym (L 5))=false := by simp [hx,characters,nonEmpty,lastSym]
    have hb : Runs (LenOK B) body L (L.set 2 (C ++ [0])) 4 := (hr.iteF hL hinput).iteF hL hword
    obtain ⟨T,ht⟩ := exit_loop hb hstart hstop
    rw [initial_output C tail A P ps (c :: w) [] L hcur hw hx ha hp]
    exact ⟨T,ht⟩
  | mismatch c d w X hne =>
    have hr := stop_runs C L hflag hL
    have h4 : lastSym (L 4)=character c+4 := by
      rw [hw]
      simp only [characters,List.map_cons,List.reverse_cons,← List.append_assoc,lastSym_append]
    have h5 : lastSym (L 5)=character d+4 := by
      rw [hx]
      simp only [characters,List.map_cons,List.reverse_cons,lastSym_append]
    have hchar : character c ≠ character d := fun h => hne (character_injective h)
    obtain ⟨Tb,hb⟩ := SequentialSymbolDispatchMachine.compare_runs (4 : Fin 8) 5 advance stop
      0x110001 (character c) (character d) (SequentialCaptureCopyMachine.character_bound c)
      L (L.set 2 (C ++ [0])) h4 h5 hL (by simpa only [if_neg hchar] using hr)
    have hword : symIs 0 (lastSym (L 4))=false := by simp [h4,symIs,character]
    have hinput : nonEmpty (lastSym (L 5))=true := by simp [h5,nonEmpty,character]
    have hbody : Runs (LenOK B) body L (L.set 2 (C ++ [0])) (Tb+1+1) := (hb.iteT hL hinput).iteF hL hword
    obtain ⟨T,ht⟩ := exit_loop hbody hstart hstop
    rw [initial_output C tail A P ps (c :: w) (d :: X) L hcur hw hx ha hp]
    exact ⟨T,ht⟩
  | @cons c w X U wr xr trace ih =>
    have h4 : lastSym (L 4)=character c+4 := by
      rw [hw]
      simp only [characters,List.map_cons,List.reverse_cons,← List.append_assoc,lastSym_append]
    have h5 : lastSym (L 5)=character c+4 := by
      rw [hx]
      simp only [characters,List.map_cons,List.reverse_cons,lastSym_append]
    obtain ⟨Ta,had⟩ := advance_runs c w X ps n hchain tail A P L hw hx ha hp hcur h1 hL
      (by simp only [List.length_cons] at hWcap; omega)
      (by simp only [List.length_cons] at hXcap; omega)
    let N := (((((L.set 4 (tail ++ [0] ++ (characters w).reverse)).set 7 (P ++ [character c])).set 5
      (characters X).reverse).set 6 (A ++ [character c])).set 0 (cursors (X.length :: ps)))
    have hN : LenOK B N := end_fits had
    obtain ⟨Tb,hb⟩ := SequentialSymbolDispatchMachine.compare_runs (4 : Fin 8) 5 advance stop
      0x110001 (character c) (character c) (SequentialCaptureCopyMachine.character_bound c)
      L N h4 h5 hL (by simpa [N] using had)
    have hword : symIs 0 (lastSym (L 4))=false := by simp [h4,symIs,character]
    have hinput : nonEmpty (lastSym (L 5))=true := by simp [h5,nonEmpty,character]
    have hbody : Runs (LenOK B) body L N (Tb+1+1) := (hb.iteT hL hinput).iteF hL hword
    obtain ⟨Ti,hi⟩ := ih (hchain := hchain.lower (Nat.le_succ X.length))
      (A := A ++ [character c]) (P := P ++ [character c]) (L := N)
      (by simpa [N,Lists.set] using hflag) rfl rfl rfl rfl rfl
      (by simpa [N,Lists.set] using h1) hN
      (by simp only [List.length_cons,List.length_append,List.length_nil] at hWcap ⊢; omega)
      (by simp only [List.length_cons,List.length_append,List.length_nil] at hXcap ⊢; omega)
      (by simpa [N,Lists.set] using hstart)
      (by simp only [Lists.set_same,lastSym_append]; rfl)
    have hout : output N C tail (A ++ [character c]) (P ++ [character c]) ps U wr xr =
        output L C tail A P ps (c :: U) wr xr := by
      funext j
      by_cases h0 : j=0 <;> by_cases h2 : j=2 <;> by_cases h4j : j=4 <;>
        by_cases h5j : j=5 <;> by_cases h6 : j=6 <;> by_cases h7 : j=7 <;>
        simp [output,N,Lists.set,h0,h2,h4j,h5j,h6,h7,characters,List.append_assoc]
    rw [hout] at hi
    obtain ⟨t1,ht1,hx1⟩ := hbody
    obtain ⟨t2,ht2,hx2⟩ := hi
    exact ⟨t1+1+t2,t1+1+t2,by omega,.loopC hL hstart hx1 hx2⟩


theorem constOK (E : Nat) (hE : 2 ≤ E) : program.ConstOK E := by
  have hs : stop.ConstOK E := by simp [stop,LProg.ConstOK]; omega
  have ha : advance.ConstOK E := ⟨by simp [moveTop,LProg.ConstOK],
    by simp [moveTop,LProg.ConstOK],SequentialCursorDecreaseMachine.decrement_constOK hE 0 1⟩
  exact ⟨hs,SequentialSymbolDispatchMachine.constOK 4 5 advance stop 0x110001 E ha hs,hs⟩

end Shallot.MacroPeg.CBV.SequentialWordMatchMachine
