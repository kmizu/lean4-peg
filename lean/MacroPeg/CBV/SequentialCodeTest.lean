import Complexity.NRename
import MacroPeg.CBV.SequentialNumericFive
import MacroPeg.CBV.SequentialInputRead

/-! Fixed character predicates on the numeric code returned by input reads.
Zero is EOF; every original character, including NUL, has a positive code. -/
namespace Shallot.MacroPeg.CBV.SequentialCodeTest
open Complexity
open SequentialNumericFive (st)
open SequentialNotReturn (prepend applied prepend_runs)

def finish : NProg 5 := .ite 0 .zero
  (prepend [.pushZ 2,.pop 0] (.prim (.pop 1)))
  (.seq (.prim (.pop 0)) (.prim (.pop 1)))

private theorem finish_runs (a b : Nat) :
    NRuns finish (st (if a ≤ b then [0] else []) [b-a] [] [] [])
      (st [] [] (if a ≤ b then [0] else []) [] []) 4 := by
  by_cases h : a ≤ b
  · simp only [if_pos h]
    have hh := prepend_runs [.pushZ (K := 5) 2,.pop 0] (.prim (.pop 1))
      (st [0] [b-a] [] [] []) _ 1 (nruns_prim (.pop 1) _)
    have he : (NPrim.pop 1).apply (applied [.pushZ (K := 5) 2,.pop 0] (st [0] [b-a] [] [] [])) =
        st [] [] [0] [] [] := by simp [applied,NPrim.apply]
    rw [he] at hh
    exact hh.iteT (i := 0) (c := .zero) (by simp [NTest.eval])
  · simp only [if_neg h]
    have hh := (nruns_prim (.pop (K := 5) 0) (st [] [b-a] [] [] [])).seq
      (nruns_prim (.pop 1) _)
    have he : (NPrim.pop 1).apply ((NPrim.pop (K := 5) 0).apply (st [] [b-a] [] [] [])) =
        st [] [] [] [] [] := by simp [NPrim.apply]
    rw [he] at hh
    exact (hh.iteF (i := 0) (c := .zero) (by simp [NTest.eval])).mono (by omega)

def upper (h : Nat) : NProg 5 := .seq (.prim (.pop 1))
  (.seq (npushC 1 h) (.seq (NShrinkingCompare.program 0 1) finish))

private theorem upper_runs (v h : Nat) :
    NRuns (upper h) (st [v] [0] [] [] []) (st [] [] (if v ≤ h then [0] else []) [] [])
      (h+4*v+7) := by
  have h₁ := nruns_pop 1 (st [v] [0] [] [] []) (l := []) (v := 0) (by simp)
  have h₂ := nruns_pushC 1 (st [v] [] [] [] []) h
  simp at h₁ h₂
  have hS : NFits (v+h+3) (st [v] [h] [] [] []) := by
    refine ⟨by omega,fun i => ?_⟩
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp [Complexity.encS,encN] <;> omega
  obtain ⟨t,ht,he⟩ := NShrinkingCompare.exec (K := 5) 0 1 (by decide) v h (st [v] [h] [] [] []) []
    (by simp) (by simp) hS
  have hcmp : NRuns (NShrinkingCompare.program 0 1) (st [v] [h] [] [] [])
      (st (if v ≤ h then [0] else []) [h-v] [] [] []) (4*v+1) := by
    refine ⟨t,ht,?_⟩
    simpa [NShrinkingCompare.result] using he.weaken (fun _ _ => trivial)
  obtain ⟨t,ht,he⟩ := h₁.seq (h₂.seq (hcmp.seq (finish_runs v h)))
  exact ⟨t,by omega,he⟩

def interval (lo hi : Nat) : NProg 5 :=
  if lo ≤ hi then .seq (npushC 1 lo) (.seq (NShrinkingCompare.program 1 0)
    (.ite 1 .zero (upper (hi-lo)) (.seq (.prim (.pop 0)) (.prim (.pop 1)))))
  else .prim (.pop 0)

theorem interval_runs (lo hi v : Nat) :
    NRuns (interval lo hi) (st [v] [] [] [] [])
      (st [] [] (if lo ≤ v ∧ v ≤ hi then [0] else []) [] []) (10*(lo+hi+v+1)+20) := by
  by_cases hlohi : lo ≤ hi
  · rw [interval,if_pos hlohi]
    have h₁ := nruns_pushC 1 (st [v] [] [] [] []) lo
    simp at h₁
    have hS : NFits (v+lo+3) (st [v] [lo] [] [] []) := by
      refine ⟨by omega,fun i => ?_⟩
      have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp [Complexity.encS,encN] <;> omega
    obtain ⟨t,ht,he⟩ := NShrinkingCompare.exec (K := 5) 1 0 (by decide) lo v
      (st [v] [lo] [] [] []) [] (by simp) (by simp) hS
    have hcmp : NRuns (NShrinkingCompare.program 1 0) (st [v] [lo] [] [] [])
        (st [v-lo] (if lo ≤ v then [0] else []) [] [] []) (4*lo+1) := by
      refine ⟨t,ht,?_⟩
      simpa [NShrinkingCompare.result] using he.weaken (fun _ _ => trivial)
    by_cases hlov : lo ≤ v
    · simp only [if_pos hlov] at hcmp
      have heq : v-lo ≤ hi-lo ↔ lo ≤ v ∧ v ≤ hi := by omega
      have hh := (upper_runs (v-lo) (hi-lo)).iteT (i := 1) (c := .zero) (by simp [NTest.eval])
        (q := .seq (.prim (.pop 0)) (.prim (.pop 1)))
      obtain ⟨t,ht,he⟩ := h₁.seq (hcmp.seq hh)
      exact ⟨t,by omega,by simpa only [heq] using he⟩
    · simp only [if_neg hlov] at hcmp
      have hh := (nruns_prim (.pop (K := 5) 0) (st [v-lo] [] [] [] [])).seq (nruns_prim (.pop 1) _)
      have hh' : NRuns (.seq (.prim (.pop (K := 5) 0)) (.prim (.pop 1)))
          (st [v-lo] [] [] [] []) (st [] [] [] [] []) 2 := by simpa [NPrim.apply] using hh
      obtain ⟨t,ht,he⟩ := h₁.seq (hcmp.seq (hh'.iteF (i := 1) (c := .zero) (by simp [NTest.eval])
        (p := upper (hi-lo))))
      exact ⟨t,by omega,by simpa [hlov] using he⟩
  · have hn : ¬ (lo ≤ v ∧ v ≤ hi) := by omega
    have hh := nruns_prim (.pop (K := 5) 0) (st [v] [] [] [] [])
    simpa [interval,hlohi,hn,NPrim.apply] using hh.mono (by omega)

inductive Kind where
  | any
  | chr (c : Char)
  | range (lo hi : Char)

def Kind.exp : Kind → MExp
  | .any => .any
  | .chr c => .chr c
  | .range lo hi => .range lo hi

def Kind.accepts : Kind → Nat → Prop
  | .any,v => 0 < v
  | .chr c,v => SequentialInputRead.code c = v
  | .range lo hi,v => SequentialInputRead.code lo ≤ v ∧ v ≤ SequentialInputRead.code hi

instance (k : Kind) (v : Nat) : Decidable (k.accepts v) := by cases k <;> unfold Kind.accepts <;> infer_instance

def positive : NProg 5 := .ite 0 .pos (.seq (.prim (.pop 0)) (.prim (.pushZ 2))) (.prim (.pop 0))
def program : Kind → NProg 5
  | .any => positive
  | .chr c => interval (SequentialInputRead.code c) (SequentialInputRead.code c)
  | .range lo hi => interval (SequentialInputRead.code lo) (SequentialInputRead.code hi)

def cost : Kind → Nat
  | .any => 4
  | .chr c => 10*(SequentialInputRead.code c+SequentialInputRead.code c+2^32+1)+20
  | .range lo hi => 10*(SequentialInputRead.code lo+SequentialInputRead.code hi+2^32+1)+20

theorem predicate_runs (k : Kind) (v : Nat) (hv : v ≤ 2^32) :
    NRuns (program k) (st [v] [] [] [] [])
      (st [] [] (if k.accepts v then [0] else []) [] []) (cost k) := by
  cases k with
  | any =>
    cases v with
    | zero =>
      have hh := (nruns_prim (.pop (K := 5) 0) (st [0] [] [] [] [])).iteF (i := 0) (c := .pos)
        (by simp [NTest.eval]) (p := .seq (.prim (.pop 0)) (.prim (.pushZ 2)))
      simpa [program,positive,Kind.accepts,cost,NPrim.apply] using hh.mono (by omega)
    | succ v =>
      have hh := ((nruns_prim (.pop (K := 5) 0) (st [v+1] [] [] [] [])).seq
        (nruns_prim (.pushZ 2) _)).iteT (i := 0) (c := .pos) (by simp [NTest.eval]) (q := .prim (.pop 0))
      simpa [program,positive,Kind.accepts,cost,NPrim.apply] using hh.mono (by omega)
  | chr c =>
    have hh := interval_runs (SequentialInputRead.code c) (SequentialInputRead.code c) v
    have hx := hh.mono (show _ ≤ cost (.chr c) by simp only [cost]; omega)
    by_cases hc : SequentialInputRead.code c = v
    · simpa [program,Kind.accepts,hc] using hx
    · have hn : ¬ (SequentialInputRead.code c ≤ v ∧ v ≤ SequentialInputRead.code c) := by omega
      simpa [program,Kind.accepts,hc,hn] using hx
  | range lo hi =>
    exact (interval_runs _ _ v).mono (by simp only [cost]; omega)

def capacity (k : Kind) : Nat := 2^32+1+grow (2^32) (cost k)+2

theorem predicate_fits (k : Kind) (v : Nat) (hv : v ≤ 2^32) :
    NBoundedTransfer.FitsRuns (capacity k) (program k) (st [v] [] [] [] [])
      (st [] [] (if k.accepts v then [0] else []) [] []) (cost k) := by
  have hb : Bnd (2^32) (2^32+1) (st [v] [] [] [] []) := by
    constructor
    · intro i w hw
      by_cases hi : i=0
      · have he : w=v := by simpa [SequentialNumericFive.st,hi] using hw
        subst w
        exact hv
      · simp [SequentialNumericFive.st,hi] at hw
    · intro i
      by_cases hi : i=0
      · simp [SequentialNumericFive.st,hi,Complexity.encS,encN]; omega
      · simp [SequentialNumericFive.st,hi,Complexity.encS]
  obtain ⟨t,ht,he⟩ := predicate_runs k v hv
  exact ⟨t,ht,(nexec_space he (2^32) (2^32+1) hb).2 (capacity k)
    (by have hh := grow_mono (m := 2^32) ht; unfold capacity; omega)⟩

end Shallot.MacroPeg.CBV.SequentialCodeTest
