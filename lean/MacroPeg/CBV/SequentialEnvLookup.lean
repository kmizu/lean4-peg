import MacroPeg.CBV.SequentialNumericFive
import MacroPeg.CBV.SequentialSpanMachine

/-! Look up a capture interval in the existing header-counted environment
encoding. The header prevents an absent parameter from reading frame fields. -/
namespace Shallot.MacroPeg.CBV.SequentialEnvLookup
open Complexity SequentialStack SequentialStackCodec
open SequentialNumericFive (st)
open SequentialNotReturn (prepend applied prepend_runs)

def fields (E : CaptureEnv) : List Nat := E.flatMap writePair

def work (E : CaptureEnv) (F A B : List Nat) : Lists 5 :=
  st (F.reverse ++ (fields E).reverse) [] [E.length] A B

def done (F : List Nat) (r : Option (Nat × Nat)) : Lists 5 :=
  st F.reverse [] [] (r.map Prod.fst).toList (r.map Prod.snd).toList

def dropBody : NProg 5 := prepend [.pop 0,.pop 0] (.prim (.dec 2))
def drainLoop : NProg 5 := .loop 2 .pos dropBody
def drain : NProg 5 := .seq drainLoop (.prim (.pop 2))

private theorem drop_runs (a b : Nat) (E : CaptureEnv) (F A B : List Nat) :
    NRuns dropBody (work ((a,b)::E) F A B) (work E F A B) 3 := by
  have h := prepend_runs [.pop (K := 5) 0,.pop 0] (.prim (.dec 2))
    (work ((a,b)::E) F A B) _ 1 (nruns_prim (.dec 2) _)
  have he : (NPrim.dec 2).apply (applied [.pop (K := 5) 0,.pop 0] (work ((a,b)::E) F A B)) =
      work E F A B := by
    simp [work,fields,writePair,applied,NPrim.apply,List.append_assoc,mapTop]
  rw [he] at h
  exact h

private theorem drainLoop_runs (E : CaptureEnv) (F A B : List Nat) :
    NRuns drainLoop (work E F A B) (st F.reverse [] [0] A B) (4*E.length+1) := by
  induction E with
  | nil =>
    refine ⟨1,by simp,?_⟩
    simpa [drainLoop,work,fields] using NExec.loopF (Q := NTrue) (i := 2) (c := .pos) (p := dropBody)
      (S := work [] F A B) trivial (by simp [work,NTest.eval])
  | cons pair E ih =>
    obtain ⟨a,b⟩ := pair
    obtain ⟨t,ht,he⟩ := drop_runs a b E F A B
    obtain ⟨u,hu,huE⟩ := ih
    exact ⟨t+1+u,by simp; omega,.loopC trivial (by simp [work,NTest.eval]) he huE⟩

theorem drain_runs (E : CaptureEnv) (F A B : List Nat) :
    NRuns drain (work E F A B) (st F.reverse [] [] A B) (4*E.length+2) := by
  have hh := (drainLoop_runs E F A B).seq (nruns_pop 2 (st F.reverse [] [0] A B)
    (l := []) (v := 0) (by simp))
  simpa [drain] using hh

def selectOps : List (NPrim 5) :=
  [.dup 0 3 (by decide),.pop 0,.dup 0 4 (by decide),.pop 0,.dec 2]

def search : Nat → NProg 5
  | 0 => .ite 2 .pos (prepend selectOps drain) drain
  | k+1 => .ite 2 .pos (.seq dropBody (search k)) drain

/-- The source environment can be consumed when an atomic expression returns.
Only its following frame fields are retained. No field past the counted
environment is inspected as a capture, even when k exceeds its length. -/
theorem search_runs (k : Nat) (E : CaptureEnv) (F : List Nat) :
    NRuns (search k) (work E F [] []) (done F E[k]?) (8*E.length+8) := by
  induction k generalizing E with
  | zero =>
    cases E with
    | nil =>
      have hh := (drain_runs [] F [] []).iteF (i := 2) (c := .pos)
        (by simp [work,NTest.eval]) (p := prepend selectOps drain)
      simpa [search,done] using hh.mono (by simp)
    | cons pair E =>
      obtain ⟨a,b⟩ := pair
      have he : applied selectOps (work ((a,b)::E) F [] []) = work E F [a] [b] := by
        simp [selectOps,work,fields,writePair,applied,NPrim.apply,List.append_assoc,mapTop]
      have hh := prepend_runs selectOps drain (work ((a,b)::E) F [] [])
        (st F.reverse [] [] [a] [b]) _ (by rw [he]; exact drain_runs E F [a] [b])
      have hx := hh.iteT (i := 2) (c := .pos) (by simp [work,NTest.eval]) (q := drain)
      simpa only [search,List.getElem?_cons_zero,done,Option.map_some,Option.toList_some] using
        hx.mono (by simp [selectOps]; omega)
  | succ k ih =>
    cases E with
    | nil =>
      have hh := (drain_runs [] F [] []).iteF (i := 2) (c := .pos)
        (by simp [work,NTest.eval]) (p := .seq dropBody (search k))
      simpa [search,done] using hh.mono (by simp)
    | cons pair E =>
      obtain ⟨a,b⟩ := pair
      have hh := ((drop_runs a b E F [] []).seq (ih E)).iteT (i := 2) (c := .pos)
        (by simp [work,NTest.eval]) (q := drain)
      simpa only [search,List.getElem?_cons_succ] using hh.mono (by simp; omega)

def headerOps : List (NPrim 5) := [.dup 0 2 (by decide),.pop 0]
def program (k : Nat) : NProg 5 := prepend headerOps (search k)

theorem lookup_runs (k : Nat) (E : CaptureEnv) (F : List Nat) :
    NRuns (program k) (st ((writeEnv E ++ F).reverse) [] [] [] []) (done F E[k]?)
      (8*E.length+10) := by
  have he : applied headerOps (st ((writeEnv E ++ F).reverse) [] [] [] []) = work E F [] [] := by
    simp [headerOps,work,fields,writeEnv,writeList,applied,NPrim.apply,List.reverse_append,List.append_assoc]
  have hh := prepend_runs headerOps (search k) (st ((writeEnv E ++ F).reverse) [] [] [] [])
    _ _ (by rw [he]; exact search_runs k E F)
  exact hh.mono (by simp [headerOps]; omega)

/-- The environment length has a fixed grammar bound A. Its lookup time can
therefore be converted to a workspace bound linear in the numeric field bound,
independently of the potentially long input traversals used by span matching. -/
theorem lookup_fits (k : Nat) (E : CaptureEnv) (F : List Nat) {A N e B : Nat}
    (hE : E.length ≤ A) (hS : Bnd N e (st ((writeEnv E ++ F).reverse) [] [] [] []))
    (hB : e + grow N (8*A+10) + 2 ≤ B) :
    NBoundedTransfer.FitsRuns B (program k)
      (st ((writeEnv E ++ F).reverse) [] [] [] []) (done F E[k]?) (8*A+10) := by
  obtain ⟨t,ht,he⟩ := lookup_runs k E F
  have ht' : t ≤ 8*A+10 := by omega
  exact ⟨t,ht',(nexec_space he N e hS).2 B (by have hh := grow_mono (m := N) ht'; omega)⟩

end Shallot.MacroPeg.CBV.SequentialEnvLookup
