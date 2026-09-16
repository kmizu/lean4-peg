import PalPeg.GalilFppDelta

set_option autoImplicit false
namespace PalPeg.GalilFppFailure
open GalilFppDelta
variable {α : Type} [DecidableEq α]

omit [DecidableEq α] in
theorem proper_iff (w : List α) (p b : ℕ) (hp : p ≤ w.length) (hb : b < p) :
    MatchAt w ((w.take p).drop 1) b ↔ IsBorder (w.take p) b := by
  have hlen : (w.take p).length = p := by simp [List.length_take, Nat.min_eq_left hp]
  have htake : (w.take p).take b = w.take b := by
    rw [List.take_take, Nat.min_eq_left (by omega : b ≤ p)]
  have hdrop : ((w.take p).drop 1).drop (((w.take p).drop 1).length - b) =
      (w.take p).drop (p - b) := by
    rw [List.length_drop, hlen, List.drop_drop]
    congr 1
    omega
  unfold MatchAt IsBorder
  rw [hdrop, hlen, htake, List.length_drop, hlen]
  constructor
  · rintro ⟨_, _, he⟩; exact ⟨by omega, he⟩
  · rintro ⟨_, he⟩; exact ⟨by omega, by omega, he⟩

theorem failure_border (w : List α) (p : ℕ) (hp : p ≤ w.length) (hpos : 0 < p) :
    IsBorder (w.take p) (failure w p) := by
  have hf := failure_le w p
  exact (proper_iff w p (failure w p) hp (by omega)).mp (matchState_spec _ _)

theorem proper_le_failure (w : List α) (p b : ℕ) (hp : p ≤ w.length)
    (hb : b < p) (hborder : IsBorder (w.take p) b) : b ≤ failure w p := by
  exact ((proper_iff w p b hp hb).mpr hborder).le_matchState

/-- Dropping from p to failure(p) retains every smaller viable match.
This rules out skipping a successful candidate during fallback. -/
theorem fallback_complete (w T : List α) (p : ℕ) (hm : MatchAt w T p) (hp : 0 < p) :
    MatchAt w T (failure w p) ∧
    ∀ b, b < p → MatchAt w T b → b ≤ failure w p := by
  have hf := failure_le w p
  constructor
  · exact (matchAt_iff_isBorder hm (by omega)).mpr (failure_border w p hm.1 hp)
  · intro b hb hmatch
    exact proper_le_failure w p b hm.1 hb ((matchAt_iff_isBorder hm (by omega)).mp hmatch)

/-- Reference form of Scala's compare / fallback / failedAtLeft control. -/
def seek (w : List α) (a : α) (p : ℕ) : ℕ :=
  if w[p]? = some a then p + 1
  else if p = 0 then 0 else seek w a (failure w p)
termination_by p
decreasing_by have := failure_le w p; omega

/-- Candidate invariant: p is a match and no matching character can be
found above p. Failed comparisons preserve this invariant at failure(p). -/
theorem seek_correct (w T : List α) (a : α) (p : ℕ)
    (hm : MatchAt w T p)
    (hmax : ∀ b, MatchAt w T b → w[b]? = some a → b ≤ p) :
    seek w a p = matchState w (T ++ [a]) := by
  induction p using Nat.strong_induction_on with
  | h p ih =>
    rw [seek]
    split
    · rename_i hhit
      apply le_antisymm
      · exact ((matchAt_snoc_succ w T a p).mpr ⟨hm, hhit⟩).le_matchState
      · have hnew := matchState_spec w (T ++ [a])
        cases hn : matchState w (T ++ [a]) with
        | zero => omega
        | succ b =>
          rw [hn] at hnew
          obtain ⟨hb, hc⟩ := (matchAt_snoc_succ w T a b).mp hnew
          have := hmax b hb hc
          omega
    · rename_i hmiss
      split
      · rename_i hz
        subst p
        apply le_antisymm (Nat.zero_le _)
        have hnew := matchState_spec w (T ++ [a])
        cases hn : matchState w (T ++ [a]) with
        | zero => omega
        | succ b =>
          rw [hn] at hnew
          obtain ⟨hb, hc⟩ := (matchAt_snoc_succ w T a b).mp hnew
          have hz := hmax b hb hc
          have he : b = 0 := by omega
          exact False.elim (hmiss (he ▸ hc))
      · rename_i hz
        obtain ⟨hnext, hcomplete⟩ := fallback_complete w T p hm (by omega)
        have hf := failure_le w p
        apply ih (failure w p) (by omega) hnext
        intro b hb hc
        have hbp := hmax b hb hc
        have hne : b ≠ p := by intro he; subst b; exact hmiss hc
        exact hcomplete b (by omega) hb

theorem seek_from_max (w T : List α) (a : α) :
    seek w a (matchState w T) = matchState w (T ++ [a]) := by
  exact seek_correct w T a _ (matchState_spec _ _) (fun b hb _ => hb.le_matchState)

/-- For nonempty processed prefixes, the compare/fallback result is the
next proper-border length. The first input symbol is handled by initialization. -/
theorem failure_step (w : List α) (n : ℕ) (hn : 0 < n) (hw : n < w.length) :
    seek w w[n] (failure w n) = failure w (n + 1) := by
  have he : w.take (n + 1) = w.take n ++ [w[n]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hw]
    rfl
  have hl : 1 ≤ (w.take n).length := by simp only [List.length_take]; omega
  unfold GalilFppDelta.failure
  rw [seek_from_max, he, List.drop_append_of_le_length hl]

/-- The number of ones emitted by Scala's reference branches: none on a
hit, one at the left-end miss, and the traversed distance on each fallback. -/
def emittedOnes (w : List α) (a : α) (p : ℕ) : ℕ :=
  if w[p]? = some a then 0
  else if p = 0 then 1 else (p - failure w p) + emittedOnes w a (failure w p)
termination_by p
decreasing_by have := failure_le w p; omega

theorem emission_balance (w : List α) (a : α) (p : ℕ) :
    emittedOnes w a p + seek w a p = p + 1 := by
  induction p using Nat.strong_induction_on with
  | h p ih =>
    rw [emittedOnes, seek]
    by_cases hh : w[p]? = some a
    · simp [hh]
    · simp only [hh, ↓reduceIte]
      by_cases hz : p = 0
      · simp [hz]
      · simp only [hz, ↓reduceIte]
        have hf := failure_le w p
        have hr := ih (failure w p) (by omega)
        omega

/-- The emitted unary block has exactly the mathematical delta value,
including multiple failed candidates and a possible left-end failure. -/
theorem emitted_delta (w : List α) (n : ℕ) (hn : 0 < n) (hw : n < w.length) :
    emittedOnes w w[n] (failure w n) = delta (failure w) n := by
  have hb := emission_balance w w[n] (failure w n)
  rw [failure_step w n hn hw] at hb
  unfold delta
  omega

theorem emitted_block (w : List α) (n : ℕ) (hn : 0 < n) (hw : n < w.length) :
    List.replicate (emittedOnes w w[n] (failure w n)) (1 : Fin 2) ++ [0] =
      block (delta (failure w) n) := by
  rw [emitted_delta w n hn hw]
  rfl

#print axioms emitted_delta
#print axioms seek_from_max
#print axioms fallback_complete
end PalPeg.GalilFppFailure
