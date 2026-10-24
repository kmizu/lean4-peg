import Complexity.BinaryWidth
import Complexity.UnaryAffine
import MacroPeg.CBV.SequentialEvaluationMachine

/-! Compute the initial clock and binary field width from a runtime unary input
length. No precomputed clock, numeric bound, or width is an input to this stage. -/
namespace Shallot.MacroPeg.CBV.SequentialInitializationNumbers
open Complexity Complexity.BinaryWord SequentialStackCodecBound SequentialStackBinary CBVtoCBN

noncomputable def slope (g : MGrammar) : Nat :=
  (g.rules.length+1)*SequentialStackRank.codeBudget g+(g.rules.length+1)+1

noncomputable def intercept (g : MGrammar) (e : MExp) : Nat :=
  (g.rules.length+1)*SequentialStackRank.codeBudget g+sizeOf e+(g.rules.length+1)+
    SequentialStackPayload.arityBudget g+(SequentialStackPool.exprPool (compilerNodes g e)).length+
    g.rules.length+8

noncomputable def bound (g : MGrammar) (e : MExp) (n : Nat) : Nat := slope g*n+intercept g e

theorem bound_eq (g : MGrammar) (x : List Char) (e : MExp) :
    bound g e x.length = numberBound g x e := by
  unfold bound slope intercept numberBound SequentialStackRank.initialCap SequentialClock.positionClock
  simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one,Nat.one_mul,Nat.mul_assoc,Nat.mul_comm]
  omega

def seed (n : Nat) (X : List Nat) : Lists 20 := fun i =>
  if i=11 then X else if i=13 then List.replicate n 1 else []

noncomputable def ready (g : MGrammar) (e : MExp) (n : Nat) (X : List Nat) : Lists 20 :=
  ((seed n X).set 8 (List.replicate ((bound g e n).log2+1) 1)).set 3
    (List.replicate (SequentialClock.positionClock g n) 1)

noncomputable def program (g : MGrammar) (e : MExp) : LProg 20 :=
  .seq (affineP 13 9 10 (slope g) (intercept g e))
    (.seq (widthP 9 10 12 8) (affineP 13 3 10 (g.rules.length+1) (g.rules.length+1)))

noncomputable def space (g : MGrammar) (e : MExp) (n : Nat) (X : List Nat) : Nat :=
  bound g e n+SequentialClock.positionClock g n+n+X.length+10

theorem runs (g : MGrammar) (e : MExp) (n : Nat) (X : List Nat) :
    ∃ T, Complexity.Runs (LenOK (space g e n X)) (program g e) (seed n X) (ready g e n X) T := by
  let B := space g e n X
  let N := bound g e n
  let S := seed n X
  have hN : 0 < N := by unfold N bound intercept; omega
  have hB : LenOK B S := by
    intro i
    by_cases h11 : i=11 <;> by_cases h13 : i=13 <;> simp [S,seed,h11,h13,B,space] <;> omega
  have hnum := affine_runs (src := (13 : Fin 20)) (dst := 9) (tmp := 10) (by decide)
    (slope g) (intercept g e) (L := S) (by rfl) hB (by
      simp [S,seed]
      unfold B space bound; omega)
  let A := S.set 9 (List.replicate N 1)
  have hAeq : S.set 9 (S 9 ++ List.replicate (slope g*(S 13).length+intercept g e) 1) = A := by
    simp [A,S,seed,N,bound]
  rw [hAeq] at hnum
  have hA : LenOK B A := by obtain ⟨_,_,he⟩ := hnum; exact he.q_end _ (Or.inl rfl)
  obtain ⟨Tw,hw⟩ := positive_width_runs (a := (9 : Fin 20)) (q := 10) (flag := 12) (out := 8)
    (by decide) hN (L := A) (by simp [A]) (by simp [A,S,seed,Lists.set]) (by simp [A,S,seed,Lists.set])
    (by simp [A,S,seed,Lists.set]) hA (by unfold B space N; omega)
  let W := S.set 8 (List.replicate (N.log2+1) 1)
  have hWeq : (((A.set 9 []).set 10 []).set 12 []).set 8 (List.replicate (N.log2+1) 1) = W := by
    funext i
    by_cases h9 : i=9 <;> by_cases h10 : i=10 <;> by_cases h12 : i=12 <;> by_cases h8 : i=8 <;>
      simp_all [A,W,S,seed,Lists.set]
  rw [hWeq] at hw
  have hW : LenOK B W := by obtain ⟨_,_,he⟩ := hw; exact he.q_end _ (Or.inl rfl)
  have hclock := affine_runs (src := (13 : Fin 20)) (dst := 3) (tmp := 10) (by decide)
    (g.rules.length+1) (g.rules.length+1) (L := W) (by simp [W,S,seed,Lists.set]) hW (by
      simp [W,S,seed,Lists.set]
      change (g.rules.length+1)*n+(g.rules.length+1)+2 ≤ B
      unfold B space SequentialClock.positionClock
      rw [Nat.mul_add,Nat.mul_one]
      omega)
  have hready : W.set 3 (W 3 ++ List.replicate ((g.rules.length+1)*(W 13).length+(g.rules.length+1)) 1) =
      ready g e n X := by
    simp [W,S,seed,ready,N,Lists.set,SequentialClock.positionClock,Nat.mul_add,Nat.mul_one]
  rw [hready] at hclock
  exact ⟨_,hnum.seq (hw.seq hclock)⟩

theorem tape (g : MGrammar) (e : MExp) (n : Nat) (X : List Nat) (τ : Tapes 20)
    (hτ : Rep (seed n X) τ) :
    ∃ t τ', Exec (TFits (space g e n X)) (program g e).compile τ t (.cont τ') ∧
      Rep (ready g e n X) τ' := by
  obtain ⟨T,hr⟩ := runs g e n X
  obtain ⟨t,τ',_,he,hrep⟩ := runs_tape hr τ hτ
  exact ⟨t,τ',he,hrep⟩

/-- The numeric initialization adds only linear workspace in the original
input length, with a constant fixed by the source grammar and expression. -/
theorem space_linear (g : MGrammar) (e : MExp) :
    ∃ C, ∀ x : List Char, space g e x.length (Complexity.encS (SequentialInputRead.codes x)) ≤ C*(x.length+1) := by
  refine ⟨numberCoefficient g e+(g.rules.length+1)+1+(2^32+1)+10,?_⟩
  intro x
  have hN := numberBound_linear g x e
  have hX := SequentialInputRead.encoded_length x
  have hX' := Nat.le_trans hX (Nat.mul_le_mul_left (2^32+1) (show x.length ≤ x.length+1 by omega))
  have hc : SequentialClock.positionClock g x.length = (g.rules.length+1)*(x.length+1) := rfl
  have h10 : 10 ≤ 10*(x.length+1) := Nat.le_mul_of_pos_right _ (by omega)
  unfold space
  rw [bound_eq,hc]
  simp only [Nat.add_mul,Nat.one_mul]
  omega

end Shallot.MacroPeg.CBV.SequentialInitializationNumbers
