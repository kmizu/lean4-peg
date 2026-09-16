import PalPeg.Matching

set_option autoImplicit false
namespace PalPeg.GalilFppDelta
variable {α : Type} [DecidableEq α]

/-- Proper-border length of the n-symbol prefix. Dropping its first symbol
excludes the full prefix; this reuses the proved matching specification. -/
def failure (w : List α) (n : ℕ) : ℕ := matchState w ((w.take n).drop 1)

theorem failure_le (w : List α) (n : ℕ) : failure w n ≤ n - 1 := by
  have h := matchState_le_text w ((w.take n).drop 1)
  simp only [List.length_drop, List.length_take] at h
  dsimp only [failure]
  omega

theorem failure_zero (w : List α) : failure w 0 = 0 := by
  have h := failure_le w 0
  omega

theorem failure_grows (w : List α) (n : ℕ) : failure w (n + 1) ≤ failure w n + 1 := by
  by_cases hn : n = 0
  · subst n
    have h := failure_le w 1
    simp only [Nat.zero_add]
    omega
  by_cases hw : n < w.length
  · have he : w.take (n + 1) = w.take n ++ [w[n]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hw]
      rfl
    have hl : 1 ≤ (w.take n).length := by simp only [List.length_take]; omega
    unfold failure
    rw [he, List.drop_append_of_le_length hl]
    exact matchState_snoc_le w _ _
  · have h₀ : w.length ≤ n := by omega
    simp only [failure, List.take_of_length_le h₀, List.take_of_length_le (show w.length ≤ n + 1 by omega)]
    omega

def delta (f : ℕ → ℕ) (i : ℕ) := 1 + f i - f (i + 1)
def deltaSum (f : ℕ → ℕ) (lo : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => delta f lo + deltaSum f (lo + 1) n

theorem delta_telescope (f : ℕ → ℕ) (hg : ∀ i, f (i + 1) ≤ f i + 1) (lo n : ℕ) :
    deltaSum f lo n + f (lo + n) = n + f lo := by
  induction n generalizing lo with
  | zero => simp [deltaSum]
  | succ n ih =>
    have hh := ih (lo + 1)
    have hd : delta f lo + f (lo + 1) = 1 + f lo := by
      have hg' := hg lo
      unfold delta
      omega
    simp only [deltaSum]
    have he : lo + 1 + n = lo + (n + 1) := by omega
    rw [he] at hh
    omega

theorem deltaSum_add (f : ℕ → ℕ) (lo n m : ℕ) :
    deltaSum f lo (n + m) = deltaSum f lo n + deltaSum f (lo + n) m := by
  induction n generalizing lo with
  | zero => simp [deltaSum]
  | succ n ih =>
    simp only [Nat.succ_add, deltaSum, ih]
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The crossed delta ones fit in the old unary counter exactly; the
remaining counter is the next proper-border gap, not an arbitrary number. -/
theorem fallback_gap (w : List α) (p : ℕ) :
    deltaSum (failure w) (failure w p) (p - failure w p) +
      (failure w p - failure w (failure w p)) = p - failure w p := by
  have hp := failure_le w p
  have hb := failure_le w (failure w p)
  have ht := delta_telescope (failure w) (failure_grows w) (failure w p) (p - failure w p)
  have he : failure w p + (p - failure w p) = p := by omega
  rw [he] at ht
  omega

theorem crossed_ones_le (w : List α) (p : ℕ) :
    deltaSum (failure w) (failure w p) (p - failure w p) ≤ p - failure w p := by
  have h := fallback_gap w p
  omega

/-- Every partial traversal is safe, not just the completed fallback.
This is the arithmetic obligation behind each unary S decrement. -/
theorem partial_crossing_le (w : List α) (p k : ℕ) (hk : k ≤ p - failure w p) :
    deltaSum (failure w) (failure w p) k ≤ p - failure w p := by
  have ht := crossed_ones_le w p
  have he := deltaSum_add (failure w) (failure w p) k (p - failure w p - k)
  have hn : k + (p - failure w p - k) = p - failure w p := by omega
  rw [hn] at he
  omega

/-- If another encoded one remains in the current traversal, its pop
cannot occur at unary zero. -/
theorem pop_positive (w : List α) (p used : ℕ)
    (hu : used < deltaSum (failure w) (failure w p) (p - failure w p)) :
    0 < p - failure w p - used := by
  have ht := crossed_ones_le w p
  omega

theorem next_gap_positive (w : List α) (p : ℕ) (h : 0 < failure w p) :
    0 < failure w p - failure w (failure w p) := by
  have hb := failure_le w (failure w p)
  omega

/-- Total encoded ones are bounded by the input prefix length. -/
theorem total_ones_le (w : List α) (n : ℕ) : deltaSum (failure w) 0 n ≤ n := by
  have h := delta_telescope (failure w) (failure_grows w) 0 n
  rw [failure_zero] at h
  omega

/-- Each delta is represented by that many ones followed by a zero. -/
def block (d : ℕ) : List (Fin 2) := List.replicate d 1 ++ [0]

def encoded (f : ℕ → ℕ) (lo : ℕ) : ℕ → List (Fin 2)
  | 0 => []
  | n + 1 => block (delta f lo) ++ encoded f (lo + 1) n

theorem encoded_ones (f : ℕ → ℕ) (lo n : ℕ) :
    (encoded f lo n).count 1 = deltaSum f lo n := by
  induction n generalizing lo with
  | zero => simp [encoded, deltaSum]
  | succ n ih => simp [encoded, block, deltaSum, ih]

theorem encoded_zeros (f : ℕ → ℕ) (lo n : ℕ) :
    (encoded f lo n).count 0 = n := by
  induction n generalizing lo with
  | zero => simp [encoded]
  | succ n ih => simp [encoded, block, ih, List.count_replicate]

theorem encoded_length (f : ℕ → ℕ) (lo n : ℕ) :
    (encoded f lo n).length = deltaSum f lo n + n := by
  induction n generalizing lo with
  | zero => simp [encoded, deltaSum]
  | succ n ih => simp [encoded, block, deltaSum, ih]; omega

/-- The reference delta tape occupies at most twice the input length. -/
theorem encoded_length_le (w : List α) (n : ℕ) :
    (encoded (failure w) 0 n).length ≤ 2 * n := by
  rw [encoded_length]
  have := total_ones_le w n
  omega

/-- A fallback scans leftwards: zeros pop T and ones pop S.
Every prefix of that reversed bit stream fits both original counters. -/
theorem fallback_bit_prefix (w : List α) (p : ℕ) (pre post : List (Fin 2))
    (he : (encoded (failure w) (failure w p) (p - failure w p)).reverse = pre ++ post) :
    pre.count 1 ≤ p - failure w p ∧ pre.count 0 ≤ p - failure w p ∧
    (post.count 1 > 0 → pre.count 1 < p - failure w p) ∧
    (post.count 0 > 0 → pre.count 0 < p - failure w p) := by
  have h₁ := congrArg (List.count (1 : Fin 2)) he
  have h₀ := congrArg (List.count (0 : Fin 2)) he
  simp only [List.count_reverse, List.count_append, encoded_ones, encoded_zeros] at h₁ h₀
  have hh := crossed_ones_le w p
  omega

/-- Consuming the entire reverse encoding leaves exactly the next S gap
and empties the copied T counter. -/
theorem fallback_bit_result (w : List α) (p : ℕ) :
    let bits := (encoded (failure w) (failure w p) (p - failure w p)).reverse
    (p - failure w p - bits.count 1 = failure w p - failure w (failure w p)) ∧
    (p - failure w p - bits.count 0 = 0) := by
  dsimp only
  simp only [List.count_reverse, encoded_ones, encoded_zeros, Nat.sub_self, and_true]
  have := fallback_gap w p
  omega

#print axioms fallback_bit_prefix
#print axioms fallback_bit_result
#print axioms fallback_gap
end PalPeg.GalilFppDelta
