import Lean
import Complexity.Univ.SimSpec
import Complexity.NTable
import Complexity.NFrame

/-!
# Tools for the stack simulator of tables

* `leq`: equalities of stacks updated at a few places (case on every index that is set, one at a time);
* the scratch stacks of the simulator;
* `subTo i j`: pop the top `a` of `i` and lower the top of `j` by `a` (truncated);
* `cnt i z o`: move everything from `i` onto `z` (reversing) and raise the top of `o` by the number moved;
* `sq`, `cu`: squares and cubes, as atoms for `omega`.
-/

namespace Complexity.Univ

open Complexity

open Lean Elab Tactic Meta in
/-- Case on the first condition of an `if` in the goal. A condition on the index `x` of the equality: settle the
positive case by evaluating the other conditions, and go on with the negative case. A closed condition: drop the
branch it rules out. -/
partial def lsolveCore : TacticM Unit := withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  match t.find? (fun e => e.isAppOfArity ``ite 5) with
  | none => evalTactic (← `(tactic| first | rfl | assumption | exact Eq.symm ‹_› | simp_all))
  | some e =>
    let c := e.getArg! 1
    let stx ← Lean.PrettyPrinter.delab c
    evalTactic (← `(tactic| by_cases hlc : $stx))
    let gs ← getGoals
    match gs with
    | g₁ :: g₂ :: rest =>
      if c.hasFVar then
        setGoals [g₁]
        evalTactic (← `(tactic| (subst hlc; ((try simp (disch := decide) only [if_pos, if_neg]) <;>
          first | rfl | assumption | exact Eq.symm ‹_› | simp_all))))
        setGoals [g₂]
        evalTactic (← `(tactic| (try simp only [hlc, if_false, ite_false])))
        let gs' ← getGoals
        unless gs'.isEmpty do lsolveCore
      else
        for g in [g₁, g₂] do
          setGoals [g]
          let closed ← (do evalTactic (← `(tactic| exact absurd hlc (by decide))); pure true) <|> pure false
          unless closed do
            evalTactic (← `(tactic| (try simp only [hlc, if_true, if_false, ite_true, ite_false])))
            let gs' ← getGoals
            unless gs'.isEmpty do lsolveCore
      setGoals rest
    | _ => throwError "lsolve: by_cases failed"

open Lean Elab Tactic in
elab "lsolve" : tactic => lsolveCore

/-- Equalities of stacks updated at a few places. -/
macro "leq" : tactic => `(tactic| (funext x; simp only [Lists.set]; lsolve))

/-- The value of stacks updated at a few places, at a fixed index. -/
macro "lat" : tactic => `(tactic| ((try simp (disch := decide) only [Lists.set_same, Lists.set, if_pos, if_neg]) <;>
  first | rfl | assumption | exact Eq.symm ‹_› | simp_all))

/-! ## Scratch stacks -/

abbrev sW : Fin UK := 7
abbrev sPW : Fin UK := 8
abbrev sTT : Fin UK := 9
abbrev sP : Fin UK := 10
abbrev sLEN : Fin UK := 11
abbrev sLN : Fin UK := 12
abbrev sTT2 : Fin UK := 13
abbrev sRD : Fin UK := 14
abbrev sCC : Fin UK := 15
abbrev sV : Fin UK := 16
abbrev sRM : Fin UK := 17
abbrev sCN : Fin UK := 18
abbrev sX : Fin UK := 19
abbrev sT1 : Fin UK := 20
abbrev sT2 : Fin UK := 21
abbrev sT3 : Fin UK := 22
abbrev sF : Fin UK := 23
abbrev sPT : Fin UK := 24
abbrev sIW : Fin UK := 25
abbrev sIM : Fin UK := 26
abbrev sA : Fin UK := 27
abbrev sMV : Fin UK := 28
abbrev sZ : Fin UK := 29
abbrev sC : Fin UK := 30
abbrev sD : Fin UK := 31
abbrev sQN : Fin UK := 32
abbrev sOF : Fin UK := 33

/-- Name the final stacks of a run. -/
theorem NRuns.named {K : Nat} {p : NProg K} {S S' : Lists K} {T : Nat} (h : NRuns p S S' T) :
    ∃ U, U = S' ∧ NRuns p S U T := ⟨_, rfl, h⟩

/-- `peekAt`, with the entry read by `getD`. -/
theorem nruns_peekAt' {K : Nat} (i T c o : Fin K) (hiT : i ≠ T) (hTo : T ≠ o) (hd : [i, T, c, o].Nodup)
    (S : Lists K) (hT : S T = []) {lc : List Nat} {k : Nat} (hc : S c = lc ++ [k]) (hk : k < (S i).length) :
    NRuns (peekAt i T c o hiT hTo) S ((S.set c lc).set o (S o ++ [(S i).getD k 0]))
      (6 * (S i).length + 4 * k + 6) := by
  have := nruns_peekAt i T c o hiT hTo hd S hT hc hk
  rw [List.getElem_eq_getD 0] at this
  exact this

/-! ## Subtracting -/

/-- Pop the top `a` of `i` and lower the top of `j` by `a`. -/
def subTo {K : Nat} (i j : Fin K) : NProg K :=
  .seq (.loop i .pos (.seq (.prim (.dec i)) (.prim (.dec j)))) (.prim (.pop i))

theorem nruns_subTo {K : Nat} (i j : Fin K) (hij : i ≠ j) (S : Lists K) {l l' : List Nat} {a b : Nat}
    (hi : S i = l ++ [a]) (hj : S j = l' ++ [b]) :
    NRuns (subTo i j) S ((S.set i l).set j (l' ++ [b - a])) (3 * a + 2) := by
  let F : Nat → Lists K := fun m => (S.set i (l ++ [a - m])).set j (l' ++ [b - m])
  have h0 : F 0 = S := by
    simp only [F, Nat.sub_zero, ← hi, ← hj, Lists.set_get_self]
  have hFi : ∀ m, F m i = l ++ [a - m] := fun m => by simp only [F]; rw [Lists.set_ne _ _ hij, Lists.set_same]
  have hFj : ∀ m, F m j = l' ++ [b - m] := fun m => by simp only [F, Lists.set_same]
  have hl := nruns_family_const (i := i) (c := .pos) (p := .seq (.prim (.dec i)) (.prim (.dec j))) F a 2
    (fun m hm => by rw [hFi, show a - m = (a - m - 1) + 1 by omega]; simp)
    (by rw [hFi, Nat.sub_self]; simp)
    (fun m hm => by
      have h₁ := nruns_dec i (F m) (hFi m)
      have h₂ := nruns_dec j ((F m).set i (l ++ [a - m - 1])) (l := l') (v := b - m)
        (by rw [Lists.set_ne _ _ (Ne.symm hij)]; exact hFj m)
      have e : ((F m).set i (l ++ [a - m - 1])).set j (l' ++ [b - m - 1]) = F (m + 1) := by
        simp only [F]; lists_eq
      rw [e] at h₂; exact h₁.seq h₂)
  rw [h0] at hl
  have hp := nruns_pop i (F a) (l := l) (v := 0) (by rw [hFi, Nat.sub_self])
  have e : (F a).set i l = (S.set i l).set j (l' ++ [b - a]) := by
    simp only [F]; lists_eq
  rw [e] at hp
  exact (hl.seq hp).mono (by omega)

/-! ## Counting while moving -/

/-- Move everything from `i` onto `z` (reversing), raising the top of `o` by the number moved. -/
def cnt {K : Nat} (i z o : Fin K) (hiz : i ≠ z) : NProg K :=
  .loop i .nonempty (.seq (nmv i z hiz) (.prim (.inc o)))

theorem nruns_cnt {K : Nat} (i z o : Fin K) (hiz : i ≠ z) (hio : i ≠ o) (hzo : z ≠ o) (S : Lists K)
    {lo : List Nat} {b : Nat} (ho : S o = lo ++ [b]) :
    NRuns (cnt i z o hiz) S (((S.set z (S z ++ (S i).reverse)).set i []).set o (lo ++ [b + (S i).length]))
      (4 * (S i).length + 1) := by
  let n := (S i).length
  let F : Nat → Lists K := fun m =>
    ((S.set z (S z ++ ((S i).drop (n - m)).reverse)).set i ((S i).take (n - m))).set o (lo ++ [b + m])
  have h0 : F 0 = S := by
    simp only [F, Nat.sub_zero, n, List.take_length, List.drop_length, List.reverse_nil, List.append_nil,
      Nat.add_zero, ← ho]
    rw [Lists.set_get_self, Lists.set_get_self, Lists.set_get_self]
  have hn : F n = ((S.set z (S z ++ (S i).reverse)).set i []).set o (lo ++ [b + (S i).length]) := by
    simp [F, n]
  have hFi : ∀ m, F m i = (S i).take (n - m) := fun m => by
    simp only [F]; rw [Lists.set_ne _ _ hio, Lists.set_same]
  have := nruns_family_const (i := i) (c := .nonempty) (p := .seq (nmv i z hiz) (.prim (.inc o))) F n 3
    (fun m hm => by rw [hFi]; exact eval_nonempty_ne (List.ne_nil_of_length_pos (by simp; omega)))
    (by rw [hFi]; simp)
    (fun m hm => by
      obtain ⟨r, hr⟩ : ∃ r, n - m = r + 1 := ⟨n - m - 1, by omega⟩
      have hrl : r < (S i).length := by simp [n] at hr; omega
      have hl : (S i).take (r + 1) = (S i).take r ++ [(S i)[r]] := List.take_succ_eq_append_getElem hrl
      have hFi' : F m i = (S i).take r ++ [(S i)[r]] := by rw [hFi, hr, hl]
      have h₁ := nruns_mv i z hiz (F m) hFi'
      have hFo : (((F m).set z (F m z ++ [(S i)[r]])).set i ((S i).take r)) o = lo ++ [b + m] := by
        rw [Lists.set_ne _ _ (Ne.symm hio), Lists.set_ne _ _ (Ne.symm hzo)]
        simp only [F, Lists.set_same]
      have h₂ := nruns_inc o (((F m).set z (F m z ++ [(S i)[r]])).set i ((S i).take r)) hFo
      have hd : (S i).drop r = (S i)[r] :: (S i).drop (r + 1) := List.drop_eq_getElem_cons hrl
      have hFz : F m z = S z ++ ((S i).drop (r + 1)).reverse := by
        simp only [F]; rw [Lists.set_ne _ _ hzo, Lists.set_ne _ _ (Ne.symm hiz), Lists.set_same, hr]
      have e : (((F m).set z (F m z ++ [(S i)[r]])).set i ((S i).take r)).set o (lo ++ [b + m + 1]) =
          F (m + 1) := by
        have hm1 : n - (m + 1) = r := by omega
        rw [hFz]
        simp only [F, hm1, hd, List.reverse_cons, List.append_assoc, Nat.add_assoc]
        funext x
        simp only [Lists.set]
        by_cases hxo : x = o
        · simp [hxo]
        · by_cases hxi : x = i
          · simp [hxo, hxi]
          · by_cases hxz : x = z
            · simp [hxo, hxi, hxz]
            · simp [hxo, hxi, hxz]
      rw [e] at h₂
      exact h₁.seq h₂)
  rw [h0, hn] at this
  exact this.mono (by omega)

theorem drop_getD {α : Type} {l : List α} {i : Nat} (d : α) (h : i < l.length) :
    l.drop i = l.getD i d :: l.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons h, ← List.getElem_eq_getD d]

theorem take_getD {α : Type} {l : List α} {i : Nat} (d : α) (h : i < l.length) :
    l.take (i + 1) = l.take i ++ [l.getD i d] := by
  rw [List.take_succ_eq_append_getElem h, ← List.getElem_eq_getD d]

/-! ## Powers as atoms -/

def sq (n : Nat) : Nat := n * n
def cu (n : Nat) : Nat := n * n * n
def qu (n : Nat) : Nat := n * n * n * n

theorem le_sq {a b n : Nat} (ha : a ≤ n) (hb : b ≤ n) : a * b ≤ sq n := Nat.mul_le_mul ha hb

theorem mul_le_sq {a b n x y : Nat} (ha : a ≤ x * n) (hb : b ≤ y * n) : a * b ≤ x * y * sq n := by
  have := Nat.mul_le_mul ha hb
  simp only [sq]
  rw [Nat.mul_mul_mul_comm] at this; exact this

theorem mul_le_cu {a b n x y : Nat} (ha : a ≤ x * n) (hb : b ≤ y * sq n) : a * b ≤ x * y * cu n := by
  have := Nat.mul_le_mul ha hb
  simp only [cu, sq] at *
  rw [Nat.mul_mul_mul_comm] at this; simpa only [Nat.mul_assoc] using this

theorem mul_le_qu {a b n x y : Nat} (ha : a ≤ x * n) (hb : b ≤ y * cu n) : a * b ≤ x * y * qu n := by
  have := Nat.mul_le_mul ha hb
  simp only [cu, qu] at *
  rw [Nat.mul_mul_mul_comm] at this; simpa only [Nat.mul_assoc] using this

theorem n_le_sq {n : Nat} (h : 1 ≤ n) : n ≤ sq n := by
  have := Nat.mul_le_mul (Nat.le_refl n) h; simp only [sq]; omega

theorem sq_le_cu {n : Nat} (h : 1 ≤ n) : sq n ≤ cu n := by
  have := Nat.mul_le_mul (Nat.le_refl (n * n)) h; simp only [sq, cu]; omega

theorem cu_le_qu {n : Nat} (h : 1 ≤ n) : cu n ≤ qu n := by
  have := Nat.mul_le_mul (Nat.le_refl (n * n * n)) h; simp only [cu, qu]; omega

theorem le_cu_of {k X N a : Nat} (hk : k ≤ N) (hX : X ≤ a * sq N) : k * X ≤ a * cu N := by
  have := Nat.mul_le_mul hk hX
  have e : N * (a * sq N) = a * cu N := by
    simp only [sq, cu]; rw [Nat.mul_left_comm, Nat.mul_comm N (N * N)]
  omega

theorem le_qu_of {k X N a : Nat} (hk : k ≤ N) (hX : X ≤ a * cu N) : k * X ≤ a * qu N := by
  have := Nat.mul_le_mul hk hX
  have e : N * (a * cu N) = a * qu N := by
    simp only [cu, qu]; rw [Nat.mul_left_comm, Nat.mul_comm N (N * N * N)]
  omega

theorem one_le_sq {n : Nat} (h : 1 ≤ n) : 1 ≤ sq n := Nat.le_trans h (n_le_sq h)

end Complexity.Univ
