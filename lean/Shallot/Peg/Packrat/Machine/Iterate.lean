import Shallot.Peg.Packrat.Machine.Round

/-!
# Bounded iteration of the concrete table machine

The literal cursor stack carries an outer counter. Literal cells preserve
its previous contents, so the counter survives every whole-table round.
The bound is computed from the input length and the fixed domain size.
-/

namespace Shallot.Packrat.Machine

open Complexity

/-- Add `k` copies of input length plus one to the counter top. -/
def addLengths (g : Grammar) : Nat → NProg (NK g)
  | 0 => nskip (idxR g)
  | k + 1 => .seq (.prim (.dup (lenR g) (idxR g) (by packrat_regs)))
      (.seq (.prim (.inc (idxR g))) (.seq (addTo (idxR g) (curR g)) (addLengths g k)))

theorem nruns_addLengths (g : Grammar) (k N : Nat) (S : Lists (NK g))
    {ll lc : List Nat} {a : Nat} (hl : S (lenR g) = ll ++ [N]) (hc : S (curR g) = lc ++ [a]) :
    NRuns (addLengths g k) S (S.set (curR g) (lc ++ [a + k * (N + 1)])) (k * (3 * N + 7) + 2) := by
  induction k generalizing S a with
  | zero => simpa only [addLengths, Nat.zero_mul, Nat.add_zero, ← hc, Lists.set_get_self] using nruns_skip (idxR g) S
  | succ k ih =>
    have hci : curR g ≠ idxR g := by packrat_regs
    have hlc : lenR g ≠ curR g := by packrat_regs
    have cp := nruns_dup (lenR g) (idxR g) (by packrat_regs) S hl
    let S₁ := S.set (idxR g) (S (idxR g) ++ [N])
    have ic := nruns_inc (idxR g) S₁ (l := S (idxR g)) (v := N) (by simp [S₁])
    let S₂ := S₁.set (idxR g) (S (idxR g) ++ [N + 1])
    have ad := nruns_addTo (idxR g) (curR g) (by packrat_regs) S₂
      (l := S (idxR g)) (l' := lc) (a := N + 1) (b := a) (by simp [S₂])
      (by simp only [S₂, S₁, Lists.set_ne _ _ hci]; exact hc)
    have he : (S₂.set (idxR g) (S (idxR g))).set (curR g) (lc ++ [a + (N + 1)]) =
        S.set (curR g) (lc ++ [a + (N + 1)]) := by
      simp only [S₂, S₁, Lists.set_set_u, Lists.set_get_self]
    rw [he] at ad
    let S₃ := S.set (curR g) (lc ++ [a + (N + 1)])
    have tx := ih S₃ (a := a + (N + 1))
      (by simp only [S₃, Lists.set_ne _ _ hlc]; exact hl) (by simp [S₃])
    have he' : S₃.set (curR g) (lc ++ [a + (N + 1) + k * (N + 1)]) =
        S.set (curR g) (lc ++ [a + (k + 1) * (N + 1)]) := by
      simp only [S₃, Lists.set_set_u, Nat.succ_mul]; congr 3; omega
    rw [he'] at tx
    exact (cp.seq (ic.seq (ad.seq tx))).mono (by rw [Nat.succ_mul k (3 * N + 7)]; omega)

/-- Push precisely the finite iteration bound. -/
def boundCounter (g : Grammar) : NProg (NK g) :=
  .seq (npushC (curR g) 1) (addLengths g (dom g).length)

def counterCost (g : Grammar) (N : Nat) : Nat := (dom g).length * (3 * N + 7) + 4

theorem nruns_boundCounter (g : Grammar) (x : List Char) (S : Lists (NK g))
    (hl : S (lenR g) = [x.length]) :
    NRuns (boundCounter g) S (S.set (curR g) (S (curR g) ++ [bound g x])) (counterCost g x.length) := by
  have pc := nruns_pushC (curR g) S 1
  let S₁ := S.set (curR g) (S (curR g) ++ [1])
  have ad := nruns_addLengths g (dom g).length x.length S₁ (ll := []) (lc := S (curR g)) (a := 1)
    (by simp only [S₁, Lists.set_ne _ _ (show lenR g ≠ curR g by packrat_regs)]; exact hl) (by simp [S₁])
  have he : S₁.set (curR g) (S (curR g) ++ [1 + (dom g).length * (x.length + 1)]) =
      S.set (curR g) (S (curR g) ++ [bound g x]) := by
    simp only [S₁, Lists.set_set_u, bound]; congr 3; omega
  rw [he] at ad
  exact (pc.seq ad).mono (by unfold counterCost; omega)

/-- Run rounds until the counter reaches zero. -/
def iterations (g : Grammar) : NProg (NK g) :=
  .loop (curR g) .pos (.seq (.prim (.dec (curR g))) (roundP g))

/-- The counted loop advances the table by exactly its initial counter. -/
theorem nruns_iterations (g : Grammar) (x : List Char) (r n : Nat) (S : Lists (NK g))
    (h : Ready g x n S) {lc : List Nat} (hc : S (curR g) = lc ++ [r]) :
    ∃ S', NRuns (iterations g) S S' (r * (roundCost g x.length + 2) + 1) ∧
      Ready g x (n + r) S' ∧ S' (curR g) = lc ++ [0] := by
  induction r generalizing S n with
  | zero =>
    refine ⟨S, ?_, by simpa only [Nat.add_zero] using h, hc⟩
    simpa only [iterations, Nat.zero_mul, Nat.zero_add] using
      (nruns_loop_exit (i := curR g) (c := .pos)
        (p := .seq (.prim (.dec (curR g))) (roundP g)) (S := S) (by rw [hc]; simp))
  | succ r ih =>
    have dc := nruns_dec (curR g) S hc
    simp only [Nat.add_one_sub_one] at dc
    let S₁ := S.set (curR g) (lc ++ [r])
    obtain ⟨S₂, rx, hh, hf⟩ := nruns_roundP g x n S₁ (h.set_cur _)
    have hc₂ : S₂ (curR g) = lc ++ [r] := by
      rw [hf _ (fun j => by constructor <;> packrat_regs)]
      exact Lists.set_same _ _ _
    obtain ⟨S₃, tx, h₃, hc₃⟩ := ih (n + 1) S₂ hh hc₂
    obtain ⟨t₁, ht₁, ex₁⟩ := dc.seq rx
    obtain ⟨t₂, ht₂, ex₂⟩ := tx
    refine ⟨S₃, ⟨t₁ + 1 + t₂, ?_, NExec.loopC trivial (by rw [hc]; simp) ex₁ ex₂⟩,
      ?_, hc₃⟩
    · rw [Nat.succ_mul]; omega
    · simpa only [Nat.add_assoc, Nat.add_comm 1 r] using h₃

/-- Prepare the bound, iterate the table, and remove the outer counter. -/
def iterateBound (g : Grammar) : NProg (NK g) :=
  .seq (boundCounter g) (.seq (iterations g) (.prim (.pop (curR g))))

def iterateCost (g : Grammar) (N : Nat) : Nat :=
  counterCost g N + ((dom g).length * (N + 1) + 1) * (roundCost g N + 2) + 2

/-- The concrete machine reaches the proved finite bound. -/
theorem nruns_iterateBound (g : Grammar) (x : List Char) (n : Nat) (S : Lists (NK g))
    (h : Ready g x n S) :
    ∃ S', NRuns (iterateBound g) S S' (iterateCost g x.length) ∧
      Ready g x (n + bound g x) S' ∧ S' (curR g) = S (curR g) := by
  have bc := nruns_boundCounter g x S h.len
  let S₁ := S.set (curR g) (S (curR g) ++ [bound g x])
  obtain ⟨S₂, it, hh, hc⟩ := nruns_iterations g x (bound g x) n S₁ (h.set_cur _) (lc := S (curR g)) (by simp [S₁])
  have pp := nruns_pop (curR g) S₂ hc
  refine ⟨S₂.set (curR g) (S (curR g)), (bc.seq (it.seq pp)).mono ?_, hh.set_cur _, by simp⟩
  unfold iterateCost
  simp only [bound]
  omega

/-- A grammar-dependent coefficient for all bounded rounds. -/
def iterateCoeff (g : Grammar) : Nat :=
  ((dom g).length + 1) * (roundCoeff g + 2) + 7 * (dom g).length + 6

/-- Bounded table iteration uses at most a cubic number of stack steps. -/
theorem iterateCost_le (g : Grammar) (N : Nat) : iterateCost g N ≤ iterateCoeff g * (N + 1) ^ 3 := by
  have hsq : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow 2 (N + 1) (by omega)
  have hcu : N + 1 ≤ (N + 1) ^ 3 := by
    simpa only [Nat.pow_succ, Nat.pow_two, Nat.pow_zero, Nat.mul_one, Nat.one_mul, Nat.mul_assoc] using
      Nat.mul_le_mul_right (N + 1) hsq
  have hb : (dom g).length * (N + 1) + 1 ≤ ((dom g).length + 1) * (N + 1) := by
    rw [Nat.add_mul, Nat.one_mul]; omega
  have hr : roundCost g N + 2 ≤ (roundCoeff g + 2) * (N + 1) ^ 2 := by
    have h := roundCost_le g N
    rw [Nat.add_mul (roundCoeff g) 2 ((N + 1) ^ 2)]
    omega
  have hm := Nat.mul_le_mul hb hr
  have he : (((dom g).length + 1) * (N + 1)) * ((roundCoeff g + 2) * (N + 1) ^ 2) =
      (((dom g).length + 1) * (roundCoeff g + 2)) * (N + 1) ^ 3 := by
    simp only [Nat.pow_succ, Nat.pow_zero, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  rw [he] at hm
  have hc : 3 * N + 7 ≤ 7 * (N + 1) ^ 3 := by omega
  have hc' := Nat.mul_le_mul_left (dom g).length hc
  have he' : (dom g).length * (7 * (N + 1) ^ 3) = (7 * (dom g).length) * (N + 1) ^ 3 := by
    rw [← Nat.mul_assoc, Nat.mul_comm (dom g).length 7]
  rw [he'] at hc'
  unfold iterateCost counterCost iterateCoeff
  rw [Nat.add_mul (((dom g).length + 1) * (roundCoeff g + 2) + 7 * (dom g).length) 6 ((N + 1) ^ 3),
    Nat.add_mul (((dom g).length + 1) * (roundCoeff g + 2)) (7 * (dom g).length) ((N + 1) ^ 3)]
  omega

end Shallot.Packrat.Machine
