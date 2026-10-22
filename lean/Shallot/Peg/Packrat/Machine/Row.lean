import Shallot.Peg.Packrat.Machine.Cell

/-!
# Fill a whole row with a counted loop

For every input position through EOF, execute the compiled cell and append
its result to the next row. The position and loop-counter stacks are
restored after the loop. Its step budget is quadratic in input length.
-/

namespace Shallot.Packrat.Machine

open Complexity

theorem Rows.set_count {g : Grammar} {x : List Char} {n : Nat} {S : Lists (NK g)}
    (h : Rows g x n S) (l : List Nat) : Rows g x n (S.set (countR g) l) := by
  intro e he
  rw [Lists.set_ne _ _ (show oldR g (nodeIdx g e he) ≠ countR g by packrat_regs)]
  exact h e he

theorem Rows.set_pos {g : Grammar} {x : List Char} {n : Nat} {S : Lists (NK g)}
    (h : Rows g x n S) (l : List Nat) : Rows g x n (S.set (posR g) l) := by
  intro e he
  rw [Lists.set_ne _ _ (show oldR g (nodeIdx g e he) ≠ posR g by packrat_regs)]
  exact h e he

theorem Rows.set_next {g : Grammar} {x : List Char} {n : Nat} {S : Lists (NK g)}
    (h : Rows g x n S) (j : Node g) (l : List Nat) : Rows g x n (S.set (nextR g j) l) := by
  intro e he
  rw [Lists.set_ne _ _ (show oldR g (nodeIdx g e he) ≠ nextR g j by packrat_regs)]
  exact h e he

/-- Fill the next row `j` with values for expression `e`, preserving all other stacks. -/
def fillRow (g : Grammar) (e : PExp) (he : e ∈ dom g) (j : Node g) : NProg (NK g) :=
  .seq (.prim (.dup (lenR g) (countR g) (by packrat_regs)))
    (.seq (.prim (.inc (countR g)))
      (.seq (.prim (.pushZ (posR g)))
        (.seq (.loop (countR g) .pos
          (.seq (.prim (.dec (countR g))) (.seq (compileCell g e he j) (.prim (.inc (posR g))))))
          (.seq (.prim (.pop (countR g))) (.prim (.pop (posR g)))))))

/-- Explicit stack-step budget of a whole row. -/
def rowCost (e : PExp) (N : Nat) : Nat := (N + 1) * (cellCoeff e * (N + 1) + 3) + 6

/-- The counted loop appends exactly the next-round row, including the EOF cell. -/
theorem nruns_fillRow (g : Grammar) (x : List Char) (n : Nat) (e : PExp)
    (he : e ∈ dom g) (j : Node g) (S : Lists (NK g)) (hrows : Rows g x n S)
    (hinput : S (inpR g) = inputRow x) (htmp : S (tmpR g) = [])
    {ll : List Nat} (hlen : S (lenR g) = ll ++ [x.length]) :
    NRuns (fillRow g e he j) S
      (S.set (nextR g j) (S (nextR g j) ++ row (iter g x (n + 1)) e x.length))
      (rowCost e x.length) := by
  let N := x.length
  let R := row (iter g x (n + 1)) e N
  let F : Nat → Lists (NK g) := fun m =>
    ((S.set (countR g) (S (countR g) ++ [N + 1 - m])).set (posR g) (S (posR g) ++ [m])).set
      (nextR g j) (S (nextR g j) ++ R.take m)
  have hpc : posR g ≠ countR g := by packrat_regs
  have hpn : posR g ≠ nextR g j := by packrat_regs
  have hcn : countR g ≠ nextR g j := by packrat_regs
  have hlc : lenR g ≠ countR g := by packrat_regs
  have hFc : ∀ m, F m (countR g) = S (countR g) ++ [N + 1 - m] := fun m => by
    simp only [F]; lists_at
  have hFp : ∀ m, F m (posR g) = S (posR g) ++ [m] := fun m => by
    simp only [F]; lists_at
  have hFn : ∀ m, F m (nextR g j) = S (nextR g j) ++ R.take m := fun m => by simp [F]
  have hFi : ∀ m, F m (inpR g) = inputRow x := fun m => by
    simp only [F]
    rw [Lists.set_ne _ _ (by packrat_regs), Lists.set_ne _ _ (by packrat_regs),
      Lists.set_ne _ _ (by packrat_regs)]
    exact hinput
  have hFt : ∀ m, F m (tmpR g) = [] := fun m => by
    simp only [F]
    rw [Lists.set_ne _ _ (by packrat_regs), Lists.set_ne _ _ (by packrat_regs),
      Lists.set_ne _ _ (by packrat_regs)]
    exact htmp
  have hFr : ∀ m, Rows g x n (F m) := fun m =>
    ((hrows.set_count _).set_pos _).set_next _ _
  have loopRun := nruns_family_const (i := countR g) (c := .pos)
    (p := .seq (.prim (.dec (countR g))) (.seq (compileCell g e he j) (.prim (.inc (posR g)))))
    F (N + 1) (cellCoeff e * (N + 1) + 2)
    (fun m hm => by rw [hFc, show N + 1 - m = (N - m) + 1 by omega]; simp)
    (by rw [hFc, Nat.sub_self]; simp)
    (fun m hm => by
      have hmN : m ≤ x.length := by change m ≤ N; omega
      have dc := nruns_dec (countR g) (F m) (hFc m)
      let S₁ := (F m).set (countR g) (S (countR g) ++ [N + 1 - m - 1])
      have hp₁ : S₁ (posR g) = S (posR g) ++ [m] := by
        simp only [S₁, Lists.set_ne _ _ hpc]; exact hFp m
      have cx := nruns_compileCell g x n e he j S₁ ((hFr m).set_count _)
        (by simp only [S₁, Lists.set_ne _ _ (show inpR g ≠ countR g by packrat_regs)]; exact hFi m)
        (by simp only [S₁, Lists.set_ne _ _ (show tmpR g ≠ countR g by packrat_regs)]; exact hFt m) hp₁ hmN
      let v := code m (iter g x (n + 1) e m)
      let S₂ := S₁.set (nextR g j) (S₁ (nextR g j) ++ [v])
      have ic := nruns_inc (posR g) S₂ (l := S (posR g)) (v := m)
        (by simp only [S₂, Lists.set_ne _ _ hpn]; exact hp₁)
      have htake : R.take (m + 1) = R.take m ++ [v] := by
        rw [List.take_succ_eq_append_getElem (by simp [R, N]; omega)]
        simp only [R, N, v, row_get _ _ _ _ hmN]
      have hcount : N + 1 - m - 1 = N + 1 - (m + 1) := by omega
      have heq : S₂.set (posR g) (S (posR g) ++ [m + 1]) = F (m + 1) := by
        simp only [S₂, S₁, F, htake, hcount]
        lists_eq
      rw [heq] at ic
      exact (dc.seq (cx.seq ic)).mono (by dsimp only [N]; omega))
  have cp := nruns_dup (lenR g) (countR g) (by packrat_regs) S hlen
  let S₁ := S.set (countR g) (S (countR g) ++ [N])
  have inc := nruns_inc (countR g) S₁ (l := S (countR g)) (v := N) (by simp [S₁])
  let S₂ := S₁.set (countR g) (S (countR g) ++ [N + 1])
  have push := nruns_pushZ (posR g) S₂
  have he₀ : S₂.set (posR g) (S₂ (posR g) ++ [0]) = F 0 := by
    simp only [S₂, S₁, F, Nat.sub_zero, List.take_zero, List.append_nil]
    lists_eq
  rw [he₀] at push
  have pc := nruns_pop (countR g) (F (N + 1)) (l := S (countR g)) (v := 0)
    (by rw [hFc, Nat.sub_self])
  have pp := nruns_pop (posR g) ((F (N + 1)).set (countR g) (S (countR g)))
    (l := S (posR g)) (v := N + 1) (by rw [Lists.set_ne _ _ hpc]; exact hFp _)
  have he₁ : ((F (N + 1)).set (countR g) (S (countR g))).set (posR g) (S (posR g)) =
      S.set (nextR g j) (S (nextR g j) ++ R) := by
    have hlenR : R.length = N + 1 := by simp [R]
    simp only [F, Nat.sub_self, ← hlenR, List.take_length]
    lists_eq
  rw [he₁] at pp
  exact (cp.seq (inc.seq (push.seq (loopRun.seq (pc.seq pp))))).mono (by simp only [rowCost, N, Nat.add_assoc, Nat.reduceAdd]; omega)

end Shallot.Packrat.Machine
