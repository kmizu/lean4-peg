import Complexity.NBoundedTransfer
import MacroPeg.CBV.SequentialNumericFive
import MacroPeg.CBV.SequentialStack

/-! Read the first character at a suffix position while restoring the original
input. Numeric characters remain in a separate input stack. -/
namespace Shallot.MacroPeg.CBV.SequentialInputRead
open Complexity Complexity.NBoundedTransfer
open SequentialNumericFive (st)

private theorem fits {B : Nat} (X T C O P : List Nat)
    (hX : (encS X).length+2 ≤ B) (hT : (encS T).length+2 ≤ B)
    (hC : (encS C).length+2 ≤ B) (hO : (encS O).length+2 ≤ B)
    (hP : (encS P).length+2 ≤ B) : NFits B (st X T C O P) := by
  refine ⟨by omega,fun i => ?_⟩
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> simpa using (by assumption)

private theorem prim_runs {B : Nat} (p : NPrim 5) (S S' : Lists 5)
    (he : p.apply S = S') (hS : NFits B S) (hS' : NFits B S') :
    FitsRuns B (.prim p) S S' 1 := by
  refine ⟨1,Nat.le_refl _,?_⟩
  have hh : NFits B (p.apply S) := by rwa [he]
  simpa only [he] using NExec.prim hS hh

def positive : NProg 5 := .seq (.prim (.dup 2 4 (by decide))) (.seq (.prim (.dec 2))
  (.seq (moveCount 0 1 2 (by decide)) (.seq (.prim (.dup 0 3 (by decide)))
    (.seq (.prim (.dec 4)) (.seq (moveCount 1 0 4 (by decide))
      (.seq (.prim (.pop 2)) (.prim (.pop 4))))))))

def program : NProg 5 := .ite 2 .zero (.seq (.prim (.pop 2)) (.prim (.pushZ 3))) positive

theorem positive_runs (pre suffix : List Nat) (c : Nat) {B : Nat}
    (hsize : (encS (pre ++ [c] ++ suffix)).length+2 ≤ B)
    (hpos : suffix.length+4 ≤ B) :
    FitsRuns B program (st (pre ++ [c] ++ suffix) [] [suffix.length+1] [] [])
      (st (pre ++ [c] ++ suffix) [] [] [c] []) (8*(suffix.length+1)+10) := by
  let X := pre ++ [c] ++ suffix
  let S := st X [] [suffix.length+1] [] []
  let A := st X [] [suffix.length+1] [] [suffix.length+1]
  let D := st X [] [suffix.length] [] [suffix.length+1]
  let F := st (pre ++ [c]) suffix.reverse [0] [] [suffix.length+1]
  let G := st (pre ++ [c]) suffix.reverse [0] [c] [suffix.length+1]
  let H := st (pre ++ [c]) suffix.reverse [0] [c] [suffix.length]
  let I := st X [] [0] [c] [0]
  let J := st X [] [] [c] [0]
  let V := st X [] [] [c] []
  have hblank : (encS ([] : List Nat)).length+2 ≤ B := by simp [encS]; omega
  have hzero : (encS [0]).length+2 ≤ B := by simp [encS,encN]; omega
  have hnum : (encS [suffix.length]).length+2 ≤ B := by simp [encS,encN]; omega
  have hnum' : (encS [suffix.length+1]).length+2 ≤ B := by simpa [encS,encN] using hpos
  have hprefix : (encS (pre ++ [c])).length+2 ≤ B := by
    rw [length_encS_append] at hsize
    omega
  have hsuffix : (encS suffix.reverse).length+2 ≤ B := by
    rw [reverse_length]
    rw [length_encS_append] at hsize
    omega
  have hchar : (encS [c]).length+2 ≤ B := by
    rw [length_encS_append] at hprefix
    omega
  have hS : NFits B S := fits _ _ _ _ _ hsize hblank hnum' hblank hblank
  have hA : NFits B A := fits _ _ _ _ _ hsize hblank hnum' hblank hnum'
  have hD : NFits B D := fits _ _ _ _ _ hsize hblank hnum hblank hnum'
  have hF : NFits B F := fits _ _ _ _ _ hprefix hsuffix hzero hblank hnum'
  have hG : NFits B G := fits _ _ _ _ _ hprefix hsuffix hzero hchar hnum'
  have hH : NFits B H := fits _ _ _ _ _ hprefix hsuffix hzero hchar hnum
  have hI : NFits B I := fits _ _ _ _ _ hsize hblank hzero hchar hzero
  have hJ : NFits B J := fits _ _ _ _ _ hsize hblank hblank hchar hzero
  have hV : NFits B V := fits _ _ _ _ _ hsize hblank hblank hchar hblank
  have h₁ := prim_runs (.dup 2 4 (by decide)) S A (by simp [S,A,NPrim.apply]) hS hA
  have h₂ := prim_runs (.dec 2) A D (by simp [A,D,NPrim.apply,mapTop]) hA hD
  have hscan := counted_runs (K := 5) 0 1 2 (by decide) (by decide) (by decide)
    suffix.reverse (pre ++ [c]) [] [] D (by simp [D,X,List.append_assoc]) (by simp [D])
    (by simp [D]) hD (by simpa [D,F] using hF)
  have heF : ((D.set 0 (pre ++ [c])).set 1 ([] ++ suffix.reverse)).set 2 ([] ++ [0]) = F := by simp [D,F]
  rw [heF] at hscan
  have h₃ := prim_runs (.dup 0 3 (by decide)) F G (by simp [F,G,NPrim.apply]) hF hG
  have h₄ := prim_runs (.dec 4) G H (by simp [G,H,NPrim.apply,mapTop]) hG hH
  have hrestore := counted_runs (K := 5) 1 0 4 (by decide) (by decide) (by decide)
    suffix [] (pre ++ [c]) [] H (by simp [H]) (by simp [H]) (by simp [H]) hH
    (by simpa [H,I,X] using hI)
  have heI : ((H.set 1 []).set 0 ((pre ++ [c]) ++ suffix)).set 4 ([] ++ [0]) = I := by simp [H,I,X]
  rw [heI] at hrestore
  have h₅ := prim_runs (.pop 2) I J (by simp [I,J,NPrim.apply]) hI hJ
  have h₆ := prim_runs (.pop 4) J V (by simp [J,V,NPrim.apply]) hJ hV
  obtain ⟨t,ht,he⟩ := h₁.seq (h₂.seq (hscan.seq (h₃.seq (h₄.seq (hrestore.seq (h₅.seq h₆))))))
  exact ⟨t+1,by simp at ht; omega,.iteF hS (by simp [NTest.eval]) he⟩

theorem zero_runs (X : List Nat) {B : Nat} (hsize : (encS X).length+2 ≤ B) (hB : 3 ≤ B) :
    FitsRuns B program (st X [] [0] [] []) (st X [] [] [0] []) 10 := by
  let S := st X [] [0] [] []
  let A := st X [] [] [] []
  let V := st X [] [] [0] []
  have he : (encS ([] : List Nat)).length+2 ≤ B := by simp [encS]; omega
  have hz : (encS [0]).length+2 ≤ B := by simpa [encS,encN] using hB
  have hS : NFits B S := fits _ _ _ _ _ hsize he hz he he
  have hA : NFits B A := fits _ _ _ _ _ hsize he he he he
  have hV : NFits B V := fits _ _ _ _ _ hsize he he hz he
  have hp := prim_runs (.pop 2) S A (by simp [S,A,NPrim.apply]) hS hA
  have hq := prim_runs (.pushZ 3) A V (by simp [A,V,NPrim.apply]) hA hV
  obtain ⟨t,ht,h⟩ := hp.seq hq
  exact ⟨t+1,by omega,.iteT hS (by simp [NTest.eval]) h⟩
def code (c : Char) : Nat := c.toNat+1
def codes (x : List Char) : List Nat := x.map code

def result (x : List Char) (p : Nat) : Nat :=
  match sfx x p with | [] => 0 | c :: _ => code c

theorem code_positive (c : Char) : 0 < code c := by unfold code; omega

theorem code_injective : Function.Injective code := by
  intro c d h
  apply Char.toNat_inj.mp
  unfold code at h
  omega

theorem code_bound (c : Char) : code c ≤ 2^32 := by
  have hh := UInt32.toNat_lt c.val
  change c.val.toNat+1 ≤ 2^32
  omega

theorem encoded_length (x : List Char) : (encS (codes x)).length ≤ (2^32+1)*x.length := by
  induction x with
  | nil => simp [codes,encS]
  | cons c x ih =>
    have hc := code_bound c
    have he : encS (codes (c :: x)) = encN (code c) ++ encS (codes x) := rfl
    rw [he,List.length_append]
    simp only [encN,List.length_cons,List.length_replicate,List.length_cons,Nat.mul_succ]
    omega

theorem read_runs (x : List Char) (p : Nat) (hp : p ≤ x.length) {B : Nat}
    (hsize : (encS (codes x)).length+2 ≤ B) (hpos : p+3 ≤ B) :
    FitsRuns B program (st (codes x) [] [p] [] [])
      (st (codes x) [] [] [result x p] []) (8*p+10) := by
  have hlen := length_sfx x hp
  cases hr : sfx x p with
  | nil =>
    have hp0 : p=0 := by rw [hr] at hlen; simpa using hlen.symm
    subst p
    simpa only [result,hr] using zero_runs (codes x) hsize (by omega)
  | cons c tail =>
    have hlen' : p=tail.length+1 := by rw [hr] at hlen; simpa using hlen.symm
    let pre := x.take (x.length-p)
    have he : x = pre ++ c :: tail := by
      have hh : x.drop (x.length-p) = c :: tail := hr
      rw [← hh]
      exact (List.take_append_drop _ _).symm
    have heCode : codes x = (codes pre ++ [code c]) ++ codes tail := by
      rw [he]
      simp [codes,List.map_append]
    have hlenCode : (codes tail).length+1 = p := by simp only [codes,List.length_map]; omega
    have hrun := positive_runs (codes pre) (codes tail) (code c)
      (B := B) (by rwa [← heCode]) (by omega)
    rw [← heCode,hlenCode] at hrun
    simpa only [result,hr] using hrun

theorem result_zero_iff (x : List Char) (p : Nat) (hp : p ≤ x.length) : result x p = 0 ↔ p=0 := by
  have hlen := length_sfx x hp
  cases hr : sfx x p with
  | nil =>
    have hp0 : p=0 := by rw [hr] at hlen; simpa using hlen.symm
    simp only [result,hr]
    simp [hp0]
  | cons c tail =>
    have hc := code_positive c
    rw [hr] at hlen
    simp only [List.length_cons] at hlen
    simp only [result,hr]
    omega

/-- A linear workspace capacity for arbitrary original character strings. -/
def space (n : Nat) : Nat := (2^32+2)*n+3

theorem compiled_runs (x : List Char) (p : Nat) (hp : p ≤ x.length) :
    Runs (LenOK (space x.length)) program.compile (encL (st (codes x) [] [p] [] []))
      (encL (st (codes x) [] [] [result x p] [])) ((8*p+10)*ncost (space x.length)) := by
  obtain ⟨t,ht,he⟩ := read_runs x p hp (B := space x.length)
    (by have hh := encoded_length x; unfold space; omega) (by unfold space; omega)
  obtain ⟨u,hu,h⟩ := nexec_compile (fun _ h => h) he
  exact ⟨u,Nat.le_trans hu (Nat.mul_le_mul_right _ ht),h⟩

theorem read_tape (x : List Char) (p : Nat) (hp : p ≤ x.length) (τ : Tapes 6)
    (hτ : Rep (encL (st (codes x) [] [p] [] [])) τ) :
    ∃ t τ', Exec (TFits (space x.length)) program.compile.compile τ t (.cont τ') ∧
      Rep (encL (st (codes x) [] [] [result x p] [])) τ' := by
  obtain ⟨t,τ',_,he,hr⟩ := Complexity.BinaryWord.runs_tape (compiled_runs x p hp) τ hτ
  exact ⟨t,τ',he,hr⟩

end Shallot.MacroPeg.CBV.SequentialInputRead
