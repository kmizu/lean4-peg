import MacroPeg.HigherOrder.Mach.Enc
import Complexity.NTable

/-!
# Reading tokens on stacks

The tokens are on a stack with the next token on top. `parseNatP tk a`: read `1ⁿ0` and push `n` on `a`, or stop
rejecting — exactly as `parseNat` (`parseNatP_ok`, `parseNatP_fail`).
-/

namespace Shallot.MacroPeg.Mach

open Complexity
open Shallot.MacroPeg.Flat
open Shallot.MacroPeg.KExp

variable {K : Nat}

/-- Read a number in unary. -/
def parseNatP (tk a : Fin K) : NProg K :=
  .seq (.prim (.pushZ a))
    (.seq (.loop tk .pos (.seq (.prim (.dec tk)) (.ite tk .zero (.seq (.prim (.pop tk)) (.prim (.inc a))) (.halt false))))
      (.ite tk .zero (.prim (.pop tk)) (.halt false)))

theorem serNat_reverse (n : Nat) : (serNat n).reverse = 0 :: List.replicate n 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [serNat, ih, List.replicate_succ']

theorem rep_snoc (A : List Nat) (k : Nat) : A ++ List.replicate (k + 1) 1 = (A ++ List.replicate k 1) ++ [0 + 1] := by
  rw [List.replicate_succ', ← List.append_assoc]

theorem parseNatP_ok (tk a : Fin K) (h : tk ≠ a) (S : Lists K) {n : Nat} {r : List Nat}
    (hS : S tk = r.reverse ++ (serNat n).reverse) :
    NRuns (parseNatP tk a) S ((S.set tk r.reverse).set a (S a ++ [n])) (6 * n + 5) := by
  rw [serNat_reverse] at hS
  have x₁ := nruns_pushZ a S
  let A := r.reverse ++ [0]
  let F : Nat → Lists K := fun m => (S.set tk (A ++ List.replicate (n - m) 1)).set a (S a ++ [m])
  have hF0 : F 0 = S.set a (S a ++ [0]) := by
    simp only [F, Nat.sub_zero]
    rw [show A ++ List.replicate n 1 = S tk by rw [hS]; simp [A], Lists.set_get_self]
  have hFt : ∀ m, F m tk = A ++ List.replicate (n - m) 1 := fun m => by simp only [F]; lists_at
  have hFa : ∀ m, F m a = S a ++ [m] := fun m => by simp only [F]; lists_at
  have hl := nruns_family_const (i := tk) (c := .pos)
    (p := .seq (.prim (.dec tk)) (.ite tk .zero (.seq (.prim (.pop tk)) (.prim (.inc a))) (.halt false))) F n 5
    (fun m hm => by rw [hFt, show n - m = (n - m - 1) + 1 by omega, rep_snoc]; exact eval_pos_succ _ 0)
    (by rw [hFt, Nat.sub_self, List.replicate_zero, List.append_nil]; exact eval_pos_zero _)
    (fun m hm => by
      have hrep : F m tk = (A ++ List.replicate (n - m - 1) 1) ++ [0 + 1] := by
        rw [hFt, show n - m = (n - m - 1) + 1 by omega, rep_snoc, Nat.add_sub_cancel]
      have d₁ := nruns_dec tk (F m) hrep
      have p₁ := nruns_pop tk ((F m).set tk ((A ++ List.replicate (n - m - 1) 1) ++ [0 + 1 - 1]))
        (l := A ++ List.replicate (n - m - 1) 1) (v := 0) (by rw [Lists.set_same])
      have i₁ := nruns_inc a (((F m).set tk ((A ++ List.replicate (n - m - 1) 1) ++ [0 + 1 - 1])).set tk
        (A ++ List.replicate (n - m - 1) 1)) (l := S a) (v := m) (by
          rw [Lists.set_ne _ _ (Ne.symm h), Lists.set_ne _ _ (Ne.symm h), hFa])
      have e : ((((F m).set tk ((A ++ List.replicate (n - m - 1) 1) ++ [0 + 1 - 1])).set tk
          (A ++ List.replicate (n - m - 1) 1)).set a (S a ++ [m + 1])) = F (m + 1) := by
        simp only [F, show n - (m + 1) = n - m - 1 by omega]; lists_eq
      rw [e] at i₁
      exact (d₁.seq ((p₁.seq i₁).iteT (by rw [Lists.set_same]; exact eval_zero_zero _))).mono (by omega))
  rw [hF0] at hl
  have hp := nruns_pop tk (F n) (l := r.reverse) (v := 0) (by rw [hFt, Nat.sub_self]; simp [A])
  have e : (F n).set tk r.reverse = (S.set tk r.reverse).set a (S a ++ [n]) := by simp only [F]; lists_eq
  rw [e] at hp
  refine (x₁.seq (hl.seq (hp.iteT (by rw [hFt, Nat.sub_self]; simp [A])))).mono ?_
  omega

/-- Where `parseNat` fails: after the leading ones, nothing or a token `≥ 2`. -/
theorem parseNat_none : ∀ {l : List Nat}, parseNat l = none →
    ∃ m rest, l = List.replicate m 1 ++ rest ∧ (rest = [] ∨ ∃ t r', rest = t :: r' ∧ 2 ≤ t)
  | [], _ => ⟨0, [], rfl, .inl rfl⟩
  | 0 :: _, h => by simp [parseNat] at h
  | 1 :: l, h => by
    simp only [parseNat, Option.map_eq_none_iff] at h
    obtain ⟨m, rest, rfl, hr⟩ := parseNat_none h
    exact ⟨m + 1, rest, by simp [List.replicate_succ], hr⟩
  | (t + 2) :: l, _ => ⟨0, (t + 2) :: l, rfl, .inr ⟨t + 2, l, rfl, by omega⟩⟩

theorem parseNatP_fail (tk a : Fin K) (h : tk ≠ a) (S : Lists K) {l : List Nat} (hS : S tk = l.reverse)
    (hn : parseNat l = none) : ∃ S', NHalts (parseNatP tk a) S false S' (6 * l.length + 6) := by
  obtain ⟨m, rest, rfl, hr⟩ := parseNat_none hn
  have x₁ := nruns_pushZ a S
  let A := rest.reverse
  let F : Nat → Lists K := fun k => (S.set tk (A ++ List.replicate (m - k) 1)).set a (S a ++ [k])
  have hF0 : F 0 = S.set a (S a ++ [0]) := by
    simp only [F, Nat.sub_zero]
    rw [show A ++ List.replicate m 1 = S tk by rw [hS]; simp [A], Lists.set_get_self]
  have hFt : ∀ k, F k tk = A ++ List.replicate (m - k) 1 := fun k => by simp only [F]; lists_at
  have hFa : ∀ k, F k a = S a ++ [k] := fun k => by simp only [F]; lists_at
  have hbody : ∀ k, k < m → NRuns (.seq (.prim (.dec tk)) (.ite tk .zero (.seq (.prim (.pop tk)) (.prim (.inc a)))
      (.halt false))) (F k) (F (k + 1)) 5 := fun k hk => by
    have hrep : F k tk = (A ++ List.replicate (m - k - 1) 1) ++ [0 + 1] := by
      rw [hFt, show m - k = (m - k - 1) + 1 by omega, rep_snoc, Nat.add_sub_cancel]
    have d₁ := nruns_dec tk (F k) hrep
    have p₁ := nruns_pop tk ((F k).set tk ((A ++ List.replicate (m - k - 1) 1) ++ [0 + 1 - 1]))
      (l := A ++ List.replicate (m - k - 1) 1) (v := 0) (by rw [Lists.set_same])
    have i₁ := nruns_inc a (((F k).set tk ((A ++ List.replicate (m - k - 1) 1) ++ [0 + 1 - 1])).set tk
      (A ++ List.replicate (m - k - 1) 1)) (l := S a) (v := k) (by
        rw [Lists.set_ne _ _ (Ne.symm h), Lists.set_ne _ _ (Ne.symm h), hFa])
    have e : ((((F k).set tk ((A ++ List.replicate (m - k - 1) 1) ++ [0 + 1 - 1])).set tk
        (A ++ List.replicate (m - k - 1) 1)).set a (S a ++ [k + 1])) = F (k + 1) := by
      simp only [F, show m - (k + 1) = m - k - 1 by omega]; lists_eq
    rw [e] at i₁
    exact (d₁.seq ((p₁.seq i₁).iteT (by rw [Lists.set_same]; exact eval_zero_zero _))).mono (by omega)
  have hlen : (List.replicate m 1 ++ rest).length = m + rest.length := by simp
  rcases hr with rfl | ⟨t, r', rfl, ht⟩
  · -- the tokens run out
    have hl := nruns_family_const (i := tk) (c := .pos) F m 5
      (fun k hk => by rw [hFt, show m - k = (m - k - 1) + 1 by omega, rep_snoc]; exact eval_pos_succ _ 0)
      (by rw [hFt, Nat.sub_self]; simp [A]) hbody
    rw [hF0] at hl
    have hFm : F m tk = [] := by rw [hFt, Nat.sub_self]; simp [A]
    refine ⟨F m, (x₁.seqH (hl.seqH ((nhalts_halt false (F m)).iteF (by rw [hFm]; rfl)))).mono ?_⟩
    rw [hlen]; simp; omega
  · -- a token `≥ 2`
    have hFm : F m tk = r'.reverse ++ [(t - 2) + 1 + 1] := by
      rw [hFt, Nat.sub_self]; simp [A]; omega
    have hlast : NHalts (.seq (.prim (.dec tk)) (.ite tk .zero (.seq (.prim (.pop tk)) (.prim (.inc a)))
        (.halt false))) (F m) false ((F m).set tk (r'.reverse ++ [(t - 2) + 1 + 1 - 1])) 5 := by
      have d₁ := nruns_dec tk (F m) hFm
      exact (d₁.seqH ((nhalts_halt false _).iteF (by rw [Lists.set_same]; exact eval_zero_succ _ _))).mono
        (by omega)
    have hl := nhalts_family (i := tk) (c := .pos) F m 5
      (fun k hk => by
        by_cases hkm : k < m
        · rw [hFt, show m - k = (m - k - 1) + 1 by omega, rep_snoc]; exact eval_pos_succ _ 0
        · obtain rfl : k = m := by omega
          rw [hFm]; exact eval_pos_succ _ _) hbody hlast m 0 (by omega)
    rw [hF0] at hl
    refine ⟨_, (x₁.seqH hl.seq).mono ?_⟩
    rw [hlen]; simp; omega

end Shallot.MacroPeg.Mach
