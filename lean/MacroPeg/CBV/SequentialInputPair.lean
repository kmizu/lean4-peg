import Complexity.NRename
import MacroPeg.CBV.SequentialInputRead
import MacroPeg.CBV.Mirror

/-! Two original-input reads retain both character codes, with neither a
substring buffer nor an input copy. The same capacity bounds every intermediate
state, including the ambient numeric registers. -/
namespace Shallot.MacroPeg.CBV.SequentialInputPair
open Complexity Complexity.NBoundedTransfer
open SequentialNumericFive (st)
open SequentialInputRead (codes result)

theorem read_into {K B : Nat} (ρ : Fin 5 → Fin K) (hi : Function.Injective ρ)
    (R : Lists K) (hR : NFits B R) (x : List Char) (p : Nat) (hp : p ≤ x.length)
    (hproj : ∀ i, R (ρ i) = st (codes x) [] [p] [] [] i) (hpos : p+3 ≤ B) :
    FitsRuns B (SequentialInputRead.program.rename ρ hi) R
      ((R.set (ρ 2) []).set (ρ 3) [result x p]) (8*p+10) := by
  have hsize : (Complexity.encS (codes x)).length+2 ≤ B := by
    have hh := hR.2 (ρ 0)
    simpa [hproj,st] using hh
  have hh := (SequentialInputRead.read_runs x p hp hsize hpos).rename_frame hi R hR
  rw [Lists.frame_eq hi R _ hproj] at hh
  have he : st (codes x) [] [] [result x p] [] =
      ((st (codes x) [] [p] [] []).set 2 []).set 3 [result x p] := by simp
  rw [he,Lists.frame_set hi,Lists.frame_set hi,Lists.frame_eq hi R _ hproj] at hh
  exact hh

def left (i : Fin 5) : Fin 7 :=
  if i=0 then 0 else if i=1 then 1 else if i=2 then 2 else if i=3 then 3 else 4
def right (i : Fin 5) : Fin 7 :=
  if i=2 then 5 else if i=3 then 6 else left i

theorem left_injective : Function.Injective left := by
  unfold Function.Injective
  decide

theorem right_injective : Function.Injective right := by unfold Function.Injective; decide

def state (X C A P D : List Nat) : Lists 7 := fun i =>
  if i=0 then X else if i=2 then C else if i=3 then A else if i=5 then P else if i=6 then D else []

def program : NProg 7 := .seq (SequentialInputRead.program.rename left left_injective)
  (SequentialInputRead.program.rename right right_injective)

theorem pair_runs (x : List Char) (a p : Nat) (ha : a ≤ x.length) (hp : p ≤ x.length)
    {B : Nat} (hR : NFits B (state (codes x) [a] [] [p] []))
    (haB : a+3 ≤ B) (hpB : p+3 ≤ B) :
    FitsRuns B program (state (codes x) [a] [] [p] [])
      (state (codes x) [] [result x a] [] [result x p]) (8*a+8*p+20) := by
  let S := state (codes x) [a] [] [p] []
  let A := state (codes x) [] [result x a] [p] []
  let V := state (codes x) [] [result x a] [] [result x p]
  have heA : (S.set (left 2) []).set (left 3) [result x a] = A := by
    funext i
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [S,A,state,left,Lists.set]
  have h₁ := read_into left left_injective S hR x a ha (by
    intro i
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp [S,state,left,st]) haB
  rw [heA] at h₁
  have hA : NFits B A := by obtain ⟨_,_,he⟩ := h₁; exact he.post
  have heV : (A.set (right 2) []).set (right 3) [result x p] = V := by
    funext i
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [A,V,state,right,Lists.set]
  have h₂ := read_into right right_injective A hA x p hp (by
    intro i
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp [A,state,right,left,st]) hpB
  rw [heV] at h₂
  obtain ⟨t,ht,he⟩ := h₁.seq h₂
  exact ⟨t,by omega,he⟩

/-- The two reads fit the same linear capacity as a single read. -/
theorem linear_pair_runs (x : List Char) (a p : Nat) (ha : a ≤ x.length) (hp : p ≤ x.length) :
    FitsRuns (SequentialInputRead.space x.length) program
      (state (codes x) [a] [] [p] [])
      (state (codes x) [] [result x a] [] [result x p]) (8*a+8*p+20) := by
  have hsize := SequentialInputRead.encoded_length x
  have haB : a+3 ≤ SequentialInputRead.space x.length := by unfold SequentialInputRead.space; omega
  have hpB : p+3 ≤ SequentialInputRead.space x.length := by unfold SequentialInputRead.space; omega
  apply pair_runs x a p ha hp _ haB hpB
  refine ⟨by unfold SequentialInputRead.space; omega,fun i => ?_⟩
  by_cases hi0 : i=0
  · subst i
    change (Complexity.encS (codes x)).length+2 ≤ SequentialInputRead.space x.length
    unfold SequentialInputRead.space
    omega
  · simp only [state,hi0,if_false]
    split <;> (try split) <;> (try split) <;> (try split) <;>
      simp [Complexity.encS,encN] <;> unfold SequentialInputRead.space <;> omega

/-- Compare the two codes after the input has been restored. The two comparison
registers are zero exactly when the codes agree. -/
def compare : NProg 7 := .seq program (NShrinkingCompare.program 3 6)

def compared (x : List Char) (a p : Nat) : Lists 7 :=
  NShrinkingCompare.result (state (codes x) [] [result x a] [] [result x p])
    3 6 [] (result x a) (result x p)

def equalTest (S : Lists 7) : Bool := NTest.zero.eval (S 3) && NTest.zero.eval (S 6)

theorem equalTest_compared (x : List Char) (a p : Nat) :
    equalTest (compared x a p) = decide (result x a = result x p) := by
  by_cases h : result x a ≤ result x p
  · by_cases heq : result x a = result x p
    · simp [equalTest,compared,NShrinkingCompare.result,Lists.set,NTest.eval,heq]
    · have hz : result x p - result x a ≠ 0 := by omega
      simp [equalTest,compared,NShrinkingCompare.result,Lists.set,h,NTest.eval,heq,hz]
  · have he : result x a ≠ result x p := by omega
    simp [equalTest,compared,NShrinkingCompare.result,Lists.set,h,NTest.eval,he]

theorem compare_runs (x : List Char) (a p : Nat) (ha : a ≤ x.length) (hp : p ≤ x.length) :
    FitsRuns (SequentialInputRead.space x.length) compare
      (state (codes x) [a] [] [p] []) (compared x a p)
      (8*a+8*p+4*result x a+21) := by
  have hpair := linear_pair_runs x a p ha hp
  have hS : NFits (SequentialInputRead.space x.length)
      (state (codes x) [] [result x a] [] [result x p]) := by
    obtain ⟨_,_,he⟩ := hpair
    exact he.post
  have hcmp := NShrinkingCompare.exec (K := 7) 3 6 (by decide)
    (result x a) (result x p) (state (codes x) [] [result x a] [] [result x p]) []
    (by simp [state]) (by simp [state]) hS
  obtain ⟨t,ht,he⟩ := hpair.seq hcmp
  exact ⟨t,by omega,he⟩

theorem compiled_compare (x : List Char) (a p : Nat) (ha : a ≤ x.length) (hp : p ≤ x.length) :
    Runs (LenOK (SequentialInputRead.space x.length)) compare.compile
      (encL (state (codes x) [a] [] [p] [])) (encL (compared x a p))
      ((8*a+8*p+4*result x a+21)*ncost (SequentialInputRead.space x.length)) := by
  obtain ⟨t,ht,he⟩ := compare_runs x a p ha hp
  obtain ⟨u,hu,h⟩ := nexec_compile (fun _ h => h) he
  exact ⟨u,Nat.le_trans hu (Nat.mul_le_mul_right _ ht),h⟩

theorem compare_tape (x : List Char) (a p : Nat) (ha : a ≤ x.length) (hp : p ≤ x.length)
    (τ : Tapes 8) (hτ : Rep (encL (state (codes x) [a] [] [p] [])) τ) :
    ∃ t τ', Exec (TFits (SequentialInputRead.space x.length)) compare.compile.compile τ t (.cont τ') ∧
      Rep (encL (compared x a p)) τ' := by
  obtain ⟨t,τ',_,he,hr⟩ := Complexity.BinaryWord.runs_tape (compiled_compare x a p ha hp) τ hτ
  exact ⟨t,τ',he,hr⟩

theorem code_eq_test (c d : Char) :
    decide (SequentialInputRead.code c = SequentialInputRead.code d) = Shallot.beqChar c d := by
  by_cases h : c.toNat = d.toNat <;> simp [SequentialInputRead.code,Shallot.beqChar,h]

/-- The machine comparison is precisely the next-character guard in the
existing capture matcher, including failure when the target reaches EOF. -/
theorem matchCount_step (x : List Char) (a p k : Nat) (ha : a ≤ x.length)
    (hp : p ≤ x.length) (hk : k+1 ≤ a) :
    SequentialSpanRecompute.matchCount (k+1) (sfx x a) (sfx x p) =
      if equalTest (compared x a p) then
        SequentialSpanRecompute.matchCount k (sfx x (a-1)) (sfx x (p-1)) else none := by
  have hlen := length_sfx x ha
  cases hs : sfx x a with
  | nil => simp only [hs,List.length_nil] at hlen; omega
  | cons c cs =>
    have htail := sfx_tail ha hs
    cases ht : sfx x p with
    | nil =>
      have hc := SequentialInputRead.code_positive c
      simp [SequentialSpanRecompute.matchCount,equalTest_compared,result,hs,ht,show SequentialInputRead.code c ≠ 0 by omega]
    | cons d ds =>
      have htarget := sfx_tail hp ht
      simp only [SequentialSpanRecompute.matchCount,equalTest_compared,result,hs,ht,
        code_eq_test,htail,htarget]

end Shallot.MacroPeg.CBV.SequentialInputPair
