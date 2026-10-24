import MacroPeg.CBV.SequentialFrontScanMachine

/-! A front parser with a selected continuation at each leaf. The field reads,
including variable-length capture environments, are the existing parser's reads. -/
namespace Shallot.MacroPeg.CBV.SequentialReturnScan
open Complexity Complexity.BinaryWord SequentialFieldFetch
open SequentialFrontRead (locals)
open SequentialStack SequentialStackCodec CBVtoCBN

inductive Plan where
  | done (key : Nat)
  | fail
  | word (next : Plan)
  | branch (zero positive : Plan)
  | many (stride : Nat) (next : Plan)

def compile (leaf : Nat → LProg 11) : Plan → LProg 11
  | .done key => leaf key
  | .fail => .halt false
  | .word next => .seq fetch (compile leaf next)
  | .branch zero positive => .ite 3 nonEmpty (.seq (.pop 3) (compile leaf positive)) (compile leaf zero)
  | .many stride next => .seq (copyLenP 3 10 7)
      (.seq (.loop 10 nonEmpty (.seq (repeatP 3 fetch stride) (.pop 10))) (compile leaf next))

def lift : SequentialFrontScan.Plan → Plan → Plan
  | .done, next => next
  | .fail, _ => .fail
  | .word p, next => .word (lift p next)
  | .branch a b, next => .branch (lift a next) (lift b next)
  | .many n p, next => .many n (lift p next)

inductive Trace : Plan → Nat → List Nat → Nat → Nat → Prop where
  | done (key held) : Trace (.done key) held [] held key
  | word {next v vs out held key} (h : Trace next v vs out key) : Trace (.word next) held (v :: vs) out key
  | zero {a b vs out key} (h : Trace a 0 vs out key) : Trace (.branch a b) 0 vs out key
  | positive {a b n vs out key} (h : Trace b n vs out key) : Trace (.branch a b) (n+1) vs out key
  | many {stride next n chunk vs out key} (hlen : chunk.length = n * stride)
      (h : Trace next (after n chunk) vs out key) : Trace (.many stride next) n (chunk ++ vs) out key

theorem lift_trace {p : SequentialFrontScan.Plan} {held mid : Nat} {vs : List Nat}
    (h : SequentialFrontScanMachine.Trace p held vs mid) {next : Plan} {ws : List Nat} {out key : Nat}
    (hn : Trace next mid ws out key) : Trace (lift p next) held (vs ++ ws) out key := by
  induction h with
  | done _ => exact hn
  | word _ ih => simpa [lift] using Trace.word (ih hn)
  | zero _ ih => exact .zero (ih hn)
  | positive _ ih => exact .positive (ih hn)
  | many hl _ ih => simpa [lift,List.append_assoc] using Trace.many hl (ih hn)

def dispatch : List Plan → Plan
  | [] => .fail
  | p :: ps => .branch p (dispatch ps)
def tagged (ps : List Plan) : Plan := .word (dispatch ps)

theorem dispatch_trace (ps : List Plan) (i : Nat) (p : Plan) (hp : ps[i]? = some p)
    {vs : List Nat} {out key : Nat} (h : Trace p 0 vs out key) : Trace (dispatch ps) i vs out key := by
  induction ps generalizing i with
  | nil => simp at hp
  | cons a ps ih =>
    cases i with
    | zero => simp at hp; subst p; exact .zero h
    | succ i => exact .positive (ih i (by simpa using hp))

def frame : Plan := tagged [
  lift (SequentialFrontScan.skipWords 2 (SequentialFrontScan.env .done)) (.done 0),
  lift (SequentialFrontScan.skipWords 3 (SequentialFrontScan.env .done)) (.done 1),
  lift (.word .done) (.done 2),
  lift (SequentialFrontScan.skipWords 3 (SequentialFrontScan.env .done)) (.done 3),
  lift (SequentialFrontScan.skipWords 2 (SequentialFrontScan.env (SequentialFrontScan.exprs .done))) (.done 4),
  lift (SequentialFrontScan.skipWords 2 .done) (.done 5),
  lift (SequentialFrontScan.skipWords 2 .done) (.done 6)]

def parser : Plan := tagged [.fail,.fail,.fail,
  lift (SequentialFrontScan.val .done) (.word (.branch .fail frame))]

def frameKey : SequentialStack.Frame → Nat
  | .seq _ _ _ => 0
  | .alt _ _ _ _ => 1
  | .notP _ => 2
  | .star _ _ _ _ => 3
  | .argHead _ _ _ _ => 4
  | .argCons _ => 5
  | .call _ _ => 6

theorem frame_trace (ns : List CompileNode) (f : SequentialStack.Frame) (held : Nat) :
    ∃ out, Trace frame held (writeFrame ns f) out (frameKey f) := by
  have make (p : SequentialFrontScan.Plan) (vs : List Nat) (key : Nat)
      (he : SequentialFrontScan.eval p 0 vs = some []) :
      ∃ out, Trace (lift p (.done key)) 0 vs out key := by
    obtain ⟨xs,out,hh,ht⟩ := SequentialFrontScanMachine.eval_trace p 0 vs [] he
    simp only [List.append_nil] at hh
    subst xs
    exact ⟨out, by simpa using lift_trace ht (Trace.done key out)⟩
  cases f with
  | seq m E b =>
    obtain ⟨out,ht⟩ := make (SequentialFrontScan.skipWords 2 (SequentialFrontScan.env .done))
      ([m,exprId ns b] ++ writeEnv E) 0 (SequentialFrontScan.skip_correct [m,exprId ns b] _ 0 _ []
        (fun h => by simpa using SequentialFrontScan.env_correct E .done h [] [] (fun _ => rfl)))
    exact ⟨out, by simpa [frame,tagged,frameKey,lift,writeFrame,writeExpr] using Trace.word (dispatch_trace _ 0 _ rfl ht)⟩
  | alt m E b p =>
    obtain ⟨out,ht⟩ := make (SequentialFrontScan.skipWords 3 (SequentialFrontScan.env .done))
      ([m,p,exprId ns b] ++ writeEnv E) 1 (SequentialFrontScan.skip_correct [m,p,exprId ns b] _ 0 _ []
        (fun h => by simpa using SequentialFrontScan.env_correct E .done h [] [] (fun _ => rfl)))
    exact ⟨out, by simpa [frame,tagged,frameKey,lift,writeFrame,writeExpr] using Trace.word (dispatch_trace _ 1 _ rfl ht)⟩
  | notP p =>
    exact ⟨p, by simpa [frame,tagged,frameKey,lift,writeFrame] using Trace.word (dispatch_trace _ 2 _ rfl (Trace.word (Trace.done 2 p)))⟩
  | star m E a p =>
    obtain ⟨out,ht⟩ := make (SequentialFrontScan.skipWords 3 (SequentialFrontScan.env .done))
      ([m,p,exprId ns a] ++ writeEnv E) 3 (SequentialFrontScan.skip_correct [m,p,exprId ns a] _ 0 _ []
        (fun h => by simpa using SequentialFrontScan.env_correct E .done h [] [] (fun _ => rfl)))
    exact ⟨out, by simpa [frame,tagged,frameKey,lift,writeFrame,writeExpr] using Trace.word (dispatch_trace _ 3 _ rfl ht)⟩
  | argHead m E es p =>
    obtain ⟨out,ht⟩ := make
      (SequentialFrontScan.skipWords 2 (SequentialFrontScan.env (SequentialFrontScan.exprs .done)))
      ([m,p] ++ writeEnv E ++ writeExprs ns es) 4 (by
        simpa [List.append_assoc] using SequentialFrontScan.skip_correct [m,p] _ 0 _ []
          (fun h => SequentialFrontScan.env_correct E _ h _ []
            (fun h => SequentialFrontScan.exprs_correct ns es .done h [] [] (fun _ => rfl))))
    exact ⟨out, by simpa [frame,tagged,frameKey,lift,writeFrame,List.append_assoc] using Trace.word (dispatch_trace _ 4 _ rfl ht)⟩
  | argCons span =>
    obtain ⟨a,b⟩ := span
    exact ⟨b, by simpa [frame,tagged,frameKey,lift,writeFrame,writePair,SequentialFrontScan.skipWords] using Trace.word (dispatch_trace _ 5 _ rfl (Trace.word (Trace.word (Trace.done 5 b))))⟩
  | call m i =>
    exact ⟨i, by simpa [frame,tagged,frameKey,lift,writeFrame,SequentialFrontScan.skipWords] using Trace.word (dispatch_trace _ 6 _ rfl (Trace.word (Trace.word (Trace.done 6 i))))⟩

theorem parser_trace (ns : List CompileNode) (v : SequentialStack.Value) (f : SequentialStack.Frame)
    (K : List SequentialStack.Frame) (held : Nat) :
    ∃ out, Trace parser held (SequentialFront.prefixCode ns K ⟨.value v,[f]⟩) out (frameKey f) := by
  obtain ⟨out,hf⟩ := frame_trace ns f K.length
  have he := SequentialFrontScan.val_correct v .done 0 [] [] (fun _ => rfl)
  obtain ⟨vs,mid,hh,hv⟩ := SequentialFrontScanMachine.eval_trace (SequentialFrontScan.val .done) 0 (writeValue v) [] (by simpa using he)
  simp only [List.append_nil] at hh
  subst vs
  have hk' : Trace (.word (.branch .fail frame)) mid ((K.length+1) :: writeFrame ns f) out (frameKey f) :=
    .word (.positive hf)
  have hv' := lift_trace hv hk'
  exact ⟨out, by
    simpa [parser,tagged,SequentialFront.prefixCode,SequentialFront.suffixCode,writeTask,Nat.add_comm]
      using Trace.word (dispatch_trace _ 3 _ rfl hv')⟩
theorem compile_trace (leaf : Nat → LProg 11) {p : Plan} {held out key : Nat} {vs : List Nat} (ht : Trace p held vs out key)
    {B width : Nat} (rest : List Nat) (tail : List Bool) (D : List Nat)
    (hv : ∀ v ∈ vs, v < 2 ^ width) (hval : ∀ v ∈ vs, 3 * v + 4 ≤ B)
    (hB : LenOK B (start width (vs ++ rest) tail D held []))
    (hloc : D.length + (locals vs).length + 2 ≤ B) (target : Lists 11)
    (hfinish : LenOK B (start width rest tail (D ++ locals vs) out []) →
      ∃ T, Complexity.Runs (LenOK B) (leaf key)
        (start width rest tail (D ++ locals vs) out []) target T) :
    ∃ T, Complexity.Runs (LenOK B) (compile leaf p) (start width (vs ++ rest) tail D held [])
      target T := by
  induction ht generalizing D with
  | done key h =>
    change ∃ T, Complexity.Runs (LenOK B) (leaf key) _ target T
    simpa [compile, SequentialFrontRead.locals] using hfinish (by simpa [SequentialFrontRead.locals] using hB)
  | @word next v vs out held key ht ih =>
    have hspace : D.length + (v + 1) + (locals vs).length + 2 ≤ B := by
      simpa [SequentialFrontRead.locals, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hloc
    obtain ⟨T1, hr1⟩ := fetch_runs (vs ++ rest) tail D [] (hv v (by simp)) hB
      (hval v (by simp)) (by omega)
    have hnext : LenOK B (start width (vs ++ rest) tail (D ++ 2 :: List.replicate v 1) v []) := by
      obtain ⟨_, _, hx⟩ := hr1
      exact hx.q_end _ (Or.inl rfl)
    have he : (D ++ 2 :: List.replicate v 1) ++ locals vs = D ++ locals (v :: vs) := by
      simp [SequentialFrontRead.locals, List.append_assoc]
    obtain ⟨T2, hr2⟩ := ih (D := D ++ 2 :: List.replicate v 1)
      (fun n hn => hv n (by simp [hn])) (fun n hn => hval n (by simp [hn])) hnext (by simp; omega) (by simpa only [he] using hfinish)

    exact ⟨T1 + T2, hr1.seq hr2⟩
  | @zero a b vs out key ht ih =>
    obtain ⟨T, hr⟩ := ih D hv hval hB hloc hfinish
    exact ⟨T + 1, hr.iteF hB (by simp [start, nonEmpty, lastSym])⟩
  | @positive a b n vs out key ht ih =>
    have hp := pop_unary (n := n) (i := (3 : Fin 11))
      (L := start width (vs ++ rest) tail D (n + 1) []) (by simp [start]) hB
    have he : (start width (vs ++ rest) tail D (n + 1) []).set 3 (List.replicate n 1) =
        start width (vs ++ rest) tail D n [] := by
      funext i
      by_cases hi : i = 3 <;> simp_all [start, Lists.set]
    rw [he] at hp
    have hnext : LenOK B (start width (vs ++ rest) tail D n []) := by
      obtain ⟨_, _, hx⟩ := hp
      exact hx.q_end _ (Or.inl rfl)
    obtain ⟨T, hr⟩ := ih D hv hval hnext hloc hfinish
    exact ⟨_, (hp.seq hr).iteT hB (unary_nonEmpty (i := 3) (n := n) (by simp [start]))⟩
  | @many stride next n chunk vs out key hlen ht ih =>
    let L := start width ((chunk ++ vs) ++ rest) tail D n []
    have hspace : D.length + (locals chunk).length + (locals vs).length + 2 ≤ B := by
      simpa [SequentialFrontRead.locals, List.flatMap_append, Nat.add_assoc] using hloc
    have hcount : n + 2 ≤ B := by simpa [L, start] using hB 3
    have hc := copyLen_spec (by decide : ([3, 10, 7] : List (Fin 11)).Nodup)
      (L := L) (B := B) (by simp [L, start]) hB (by simp [L, start]; exact hcount)
    have he : L.set 10 (L 10 ++ List.replicate (L 3).length 1) =
        start width (chunk ++ (vs ++ rest)) tail D n (List.replicate n 1) := by
      funext i
      by_cases hi : i = 10 <;> simp_all [L, start, Lists.set, List.append_assoc]
    rw [he] at hc
    have hloop : LenOK B (start width (chunk ++ (vs ++ rest)) tail D n (List.replicate n 1)) := by
      obtain ⟨_, _, hx⟩ := hc
      exact hx.q_end _ (Or.inl rfl)
    obtain ⟨T1, hr1⟩ := counted_fetch_runs chunk (vs ++ rest) tail D hlen
      (fun v hm => hv v (by simp [hm])) (fun v hm => hval v (by simp [hm])) hloop (by omega)
    have hnext : LenOK B (start width (vs ++ rest) tail (D ++ locals chunk) (after n chunk) []) := by
      obtain ⟨_, _, hx⟩ := hr1
      exact hx.q_end _ (Or.inl rfl)
    have heout : (D ++ locals chunk) ++ locals vs = D ++ locals (chunk ++ vs) := by
      simp [SequentialFrontRead.locals, List.flatMap_append, List.append_assoc]
    obtain ⟨T2, hr2⟩ := ih (D := D ++ locals chunk)
      (fun v hm => hv v (by simp [hm])) (fun v hm => hval v (by simp [hm])) hnext (by simp; omega) (by simpa only [heout] using hfinish)

    exact ⟨_, hc.seq (hr1.seq hr2)⟩

end Shallot.MacroPeg.CBV.SequentialReturnScan
