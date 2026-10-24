import MacroPeg.CBV.ParTableau.Sim
import MacroPeg.CBV.ParSimulation.Recognition
import MacroPeg.HigherOrder.KExp.Hard

namespace Shallot.MacroPeg.CBV.ParTableau

open PrefixCounters RootObservation
open CBVtoCBN (clockValue fullClock_value)
open Complexity (TM Cfg)

theorem capture_full_args (g : MGrammar) (x : List Char) (d : Nat) :
    DerivesArgsPar g .callByValuePar x
      (.star .any :: (List.replicate d (.star .any) ++ List.replicate d (.lit [])))
      (prefixValues x (x.length :: (List.replicate d x.length ++ List.replicate d 0))) := by
  obtain ⟨t, ht⟩ := ParSimulation.star_any_derives g .callByValuePar x
  have hrepeat : ∀ m, DerivesArgsPar g .callByValuePar x
      (List.replicate m (.star .any) ++ List.replicate d (.lit []))
      (List.replicate m (.lit x) ++ List.replicate d (.lit [])) := by
    intro m
    induction m with
    | zero =>
      simpa only [List.replicate_zero, List.nil_append, prefixValues_replicate, List.take_zero] using
        prefixValues_args g x (List.replicate d 0)
    | succ m ih => exact .cons _ _ _ _ _ _ _ ht (by simp) ih
  have hh : DerivesArgsPar g .callByValuePar x
      (.star .any :: (List.replicate d (.star .any) ++ List.replicate d (.lit [])))
      (.lit x :: (List.replicate d (.lit x) ++ List.replicate d (.lit []))) :=
    .cons _ _ _ _ _ _ _ ht (by simp) (hrepeat d)
  simpa only [prefixValues, prefixValues_append, prefixValues_replicate, List.take_length, List.take_zero] using hh

def horizon (n d : Nat) : Nat := (n + 1) ^ d - 1

theorem start_test {k : Nat} (M : TM k) (d : Nat) (x : List Char) :
    SObs (compile M d) .callByValuePar (start M d) x
      (if (cfg M x (horizon x.length d)).state = 0 then some [] else none) := by
  let time := List.replicate d x.length
  let position := List.replicate d 0
  let b := (cfg M x (horizon x.length d)).state == 0
  have he : clockValue x.length time = horizon x.length d := by
    have hh := fullClock_value x.length d
    dsimp [time, horizon]; omega
  have hgood := tableau_sim M d x time (by simp [time]) (by simp [time])
  have hstate := hgood position (by simp [position]) (by simp [position]) (.state 0)
    (by have := M.three_le_nq; exact Nat.lt_of_lt_of_le (by decide : 0 < 3) this)
  rw [he] at hstate
  have hboot : Test (compile M d) .callByValuePar
      (.call (address M d (.state 0))
        (.star .any :: (List.replicate d (.star .any) ++ List.replicate d (.lit [])))) x b := by
    apply (par_prefix_args_iff (capture_full_args (compile M d) x d) _).mpr
    exact hstate
  have hpeek := test_not (test_not hboot)
  have hpeek' : Test (compile M d) .callByValuePar
      (.andP (.call (address M d (.state 0))
        (.star .any :: (List.replicate d (.star .any) ++ List.replicate d (.lit []))))) x b := by
    simpa only [MExp.andP, Bool.not_not] using hpeek
  obtain ⟨t, ht⟩ := ParSimulation.star_any_derives (compile M d) .callByValuePar x
  cases hb : b with
  | false =>
    have hh := seq_fail (b := .star .any) (by simpa only [hb, Test, Bool.false_eq_true, if_false] using hpeek')
    have hn : (cfg M x (horizon x.length d)).state ≠ 0 := by
      intro he
      have ht : b = true := by simp only [b, he, beq_self_eq_true]
      rw [hb] at ht
      cases ht
    simpa only [start, if_neg hn] using hh
  | true =>
    have hh := seq_ok (b := .star .any)
      (by simpa only [hb, Test, Bool.true_eq, if_true] using hpeek') (show SObs (compile M d) .callByValuePar
        (.star .any) x (some []) from ⟨_, ht, rfl⟩)
    have hn : (cfg M x (horizon x.length d)).state = 0 := eq_of_beq hb
    simpa only [start, if_pos hn] using hh

theorem start_recognizes {k : Nat} (M : TM k) (d : Nat) (x : List Char) :
    SObs (compile M d) .callByValuePar (start M d) x (some []) ↔
      (cfg M x (horizon x.length d)).state = 0 := by
  rw [unique_iff (start_test M d x)]
  split <;> simp_all

def polynomialDigits (coefficient degree : Nat) : Nat := degree + coefficient + 1

theorem polynomial_horizon (c degree n : Nat) (hn : 0 < n) :
    c * (n + 1) ^ degree ≤ horizon n (polynomialDigits c degree) := by
  have hc : c < (n + 1) ^ (c + 1) :=
    Nat.lt_of_lt_of_le (by have := Nat.lt_two_pow_self (n := c + 1); omega)
      (Nat.pow_le_pow_left (by omega : 2 ≤ n + 1) (c + 1))
  have hh := Nat.mul_lt_mul_of_pos_right hc (Nat.pow_pos (by omega : 0 < n + 1) (n := degree))
  rw [← Nat.pow_add] at hh
  have he : c + 1 + degree = polynomialDigits c degree := by unfold polynomialDigits; omega
  rw [he] at hh
  unfold horizon
  omega

def polynomialTest {k : Nat} (M : TM k) (c degree : Nat) : MExp :=
  branch (.notP .any) (truth ((M.run (Complexity.initCfg k []) c).state == 0))
    (.andP (start M (polynomialDigits c degree)))

def polynomialStart {k : Nat} (M : TM k) (c degree : Nat) : MExp :=
  .seq (polynomialTest M c degree) (.star .any)

theorem polynomialStart_firstOrder {k : Nat} (M : TM k) (c degree : Nat) :
    (polynomialStart M c degree).FirstOrder := by
  have ht := truth_firstOrder ((M.run (Complexity.initCfg k []) c).state == 0)
  have hs := start_firstOrder M (polynomialDigits c degree)
  simp only [polynomialStart, polynomialTest, branch, MExp.FirstOrder, MExp.andP]
  exact ⟨⟨⟨trivial, ht⟩, trivial, hs⟩, trivial⟩

theorem run_accepts_iff {k : Nat} {M : TM k} {L : Complexity.Lang} {T : Nat → Nat}
    (hdec : M.Decides L) (htb : KExp.TimeBounded M T) (w : List Bool) (u : Nat) (hu : T w.length ≤ u) :
    (M.run (Complexity.initCfg k w) u).state = 0 ↔ L w := by
  obtain ⟨t, ht, hiff⟩ := hdec w
  rw [TM.run_stays M _ hu (htb w), KExp.halted_state M _ (htb w) ht]
  exact hiff

/-- Every polynomial-time TM yields one fixed first-order Par grammar on
the original input. The empty input is handled by a source-dependent constant. -/
theorem polynomial_recognizes {k : Nat} {M : TM k} {L : Complexity.Lang} {T : Nat → Nat}
    (c degree : Nat) (hT : ∀ n, T n ≤ c * (n + 1) ^ degree)
    (hdec : M.Decides L) (htb : KExp.TimeBounded M T) (x : List Char) :
    SObs (compile M (polynomialDigits c degree)) .callByValuePar (polynomialStart M c degree) x (some []) ↔
      L (inputBits x) := by
  let g := compile M (polynomialDigits c degree)
  have htest : Predicate g .callByValuePar (polynomialTest M c degree) x (L (inputBits x)) := by
    cases x with
    | nil =>
      have he : SObs g .callByValuePar (.notP .any) [] (some []) := ⟨_, .notFail _ _ .anyFail, rfl⟩
      have hh := truth_test g [] ((M.run (Complexity.initCfg k []) c).state == 0)
      have hb : Test g .callByValuePar (polynomialTest M c degree) []
          ((M.run (Complexity.initCfg k []) c).state == 0) := (branch_true_iff he _).mpr hh
      have hp := Predicate.of_obs hb
      apply hp.congr
      rw [beq_iff_eq]
      exact run_accepts_iff hdec htb [] c (by have := hT 0; simpa using this)
    | cons a xs =>
      have he : SObs g .callByValuePar (.notP .any) (a :: xs) none :=
        ⟨_, .notOk _ _ _ _ (.anyOk a xs), rfl⟩
      have hh := start_test M (polynomialDigits c degree) (a :: xs)
      have hpeek : Test g .callByValuePar (.andP (start M (polynomialDigits c degree))) (a :: xs)
          ((cfg M (a :: xs) (horizon (a :: xs).length (polynomialDigits c degree))).state == 0) := by
        by_cases hb : (cfg M (a :: xs) (horizon (a :: xs).length (polynomialDigits c degree))).state = 0
        · simpa only [Test, beq_iff_eq, if_pos hb, Bool.true_eq, if_true] using peek_success (by simpa only [if_pos hb] using hh)
        · simpa only [Test, beq_iff_eq, if_neg hb, Bool.false_eq_true, if_false] using peek_failure (by simpa only [if_neg hb] using hh)
      have hb : Test g .callByValuePar (polynomialTest M c degree) (a :: xs)
          ((cfg M (a :: xs) (horizon (a :: xs).length (polynomialDigits c degree))).state == 0) :=
        (branch_false_iff he _).mpr hpeek
      have hp := Predicate.of_obs hb
      apply hp.congr
      rw [beq_iff_eq]
      exact run_accepts_iff hdec htb (inputBits (a :: xs)) _ (by
        have hh := Nat.le_trans (hT (a :: xs).length)
          (polynomial_horizon c degree (a :: xs).length (by simp))
        simpa only [inputBits, List.length_map] using hh)
  exact ParSimulation.Predicate.consume_iff htest

end Shallot.MacroPeg.CBV.ParTableau
