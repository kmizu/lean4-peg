import Shallot.Peg.Packrat.Machine.Iterate

/-!
# Initialize all old rows with unknown entries

The input and its length have already been loaded. A counted loop creates
one zero for each position including EOF, and a generated sequence does
this for every old row. Other registers are preserved.
-/

namespace Shallot.Packrat.Machine

open Complexity

/-- Append an unknown entry at every input position. -/
def zeroRow (g : Grammar) (j : Node g) : NProg (NK g) :=
  .seq (.prim (.dup (lenR g) (countR g) (by packrat_regs)))
    (.seq (.prim (.inc (countR g)))
      (.seq (.loop (countR g) .pos (.seq (.prim (.dec (countR g))) (.prim (.pushZ (oldR g j)))))
        (.prim (.pop (countR g)))))

theorem nruns_zeroRow (g : Grammar) (j : Node g) (N : Nat) (S : Lists (NK g))
    {ll : List Nat} (hl : S (lenR g) = ll ++ [N]) :
    NRuns (zeroRow g j) S (S.set (oldR g j) (S (oldR g j) ++ List.replicate (N + 1) 0)) (3 * N + 7) := by
  have hoc : oldR g j ≠ countR g := by packrat_regs
  let F : Nat → Lists (NK g) := fun m => (S.set (countR g) (S (countR g) ++ [N + 1 - m])).set
    (oldR g j) (S (oldR g j) ++ List.replicate m 0)
  have hFc : ∀ m, F m (countR g) = S (countR g) ++ [N + 1 - m] := fun m => by simp only [F]; lists_at
  have hFo : ∀ m, F m (oldR g j) = S (oldR g j) ++ List.replicate m 0 := fun m => by simp [F]
  have lp := nruns_family_const (i := countR g) (c := .pos)
    (p := .seq (.prim (.dec (countR g))) (.prim (.pushZ (oldR g j)))) F (N + 1) 2
    (fun m hm => by rw [hFc, show N + 1 - m = (N - m) + 1 by omega]; simp)
    (by rw [hFc, Nat.sub_self]; simp)
    (fun m hm => by
      have dc := nruns_dec (countR g) (F m) (hFc m)
      have pz := nruns_pushZ (oldR g j) ((F m).set (countR g) (S (countR g) ++ [N + 1 - m - 1]))
      have he : ((F m).set (countR g) (S (countR g) ++ [N + 1 - m - 1])).set (oldR g j)
          (((F m).set (countR g) (S (countR g) ++ [N + 1 - m - 1])) (oldR g j) ++ [0]) = F (m + 1) := by
        have hc : N + 1 - m - 1 = N + 1 - (m + 1) := by omega
        simp only [F, hc, List.replicate_succ']
        lists_eq
      rw [he] at pz
      exact dc.seq pz)
  have cp := nruns_dup (lenR g) (countR g) (by packrat_regs) S hl
  let S₁ := S.set (countR g) (S (countR g) ++ [N])
  have ic := nruns_inc (countR g) S₁ (l := S (countR g)) (v := N) (by simp [S₁])
  have he₀ : S₁.set (countR g) (S (countR g) ++ [N + 1]) = F 0 := by
    simp only [S₁, F, Nat.sub_zero, List.replicate_zero, List.append_nil]
    lists_eq
  rw [he₀] at ic
  have pp := nruns_pop (countR g) (F (N + 1)) (l := S (countR g)) (v := 0) (by rw [hFc, Nat.sub_self])
  have he₁ : (F (N + 1)).set (countR g) (S (countR g)) =
      S.set (oldR g j) (S (oldR g j) ++ List.replicate (N + 1) 0) := by
    simp only [F]; lists_eq
  rw [he₁] at pp
  exact (cp.seq (ic.seq (lp.seq pp))).mono (by omega)

def seedRows (g : Grammar) : List (Node g) → NProg (NK g)
  | [] => nskip (countR g)
  | j :: js => .seq (zeroRow g j) (seedRows g js)

theorem nruns_seedRows (g : Grammar) (js : List (Node g)) (hn : js.Nodup)
    (N : Nat) (S : Lists (NK g)) (hl : S (lenR g) = [N]) (hz : ∀ j ∈ js, S (oldR g j) = []) :
    ∃ S', NRuns (seedRows g js) S S' (js.length * (3 * N + 7) + 2) ∧
      (∀ j ∈ js, S' (oldR g j) = List.replicate (N + 1) 0) ∧
      (∀ r, (∀ j ∈ js, r ≠ oldR g j) → S' r = S r) := by
  induction js generalizing S with
  | nil =>
    refine ⟨S, ?_, by simp, by simp⟩
    simpa only [seedRows, List.length_nil, Nat.zero_mul, Nat.zero_add] using nruns_skip (countR g) S
  | cons j js ih =>
    obtain ⟨hj, hjs⟩ := List.nodup_cons.mp hn
    have zx := nruns_zeroRow g j N S (ll := []) hl
    rw [hz j List.mem_cons_self, List.nil_append] at zx
    let S₁ := S.set (oldR g j) (List.replicate (N + 1) 0)
    have hne : ∀ k ∈ js, oldR g k ≠ oldR g j := by
      intro k hk he
      exact hj ((oldR_inj g k j).mp he ▸ hk)
    obtain ⟨S₂, tx, ht, hf⟩ := ih hjs S₁
      (by simp only [S₁, Lists.set_ne _ _ (show lenR g ≠ oldR g j by packrat_regs)]; exact hl)
      (fun k hk => by simp only [S₁, Lists.set_ne _ _ (hne k hk)]; exact hz k (List.mem_cons_of_mem _ hk))
    refine ⟨S₂, (zx.seq tx).mono ?_, ?_, ?_⟩
    · simp only [List.length_cons, Nat.succ_mul]; omega
    · intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · rw [hf _ (fun a ha => Ne.symm (hne a ha))]; simp [S₁]
      · exact ht k hk
    · intro r hr
      rw [hf _ (fun a ha => hr a (List.mem_cons_of_mem _ ha))]
      simp only [S₁, Lists.set_ne _ _ (hr j List.mem_cons_self)]

/-- Build the initial unknown table from empty old rows. -/
def initTable (g : Grammar) : NProg (NK g) := seedRows g (List.finRange (dom g).length)

theorem row_zero (g : Grammar) (x : List Char) (e : PExp) :
    row (iter g x 0) e x.length = List.replicate (x.length + 1) 0 := by
  simp [row, iter, code, List.map_const']

theorem nruns_initialize (g : Grammar) (x : List Char) (S : Lists (NK g))
    (hi : S (inpR g) = inputRow x) (hl : S (lenR g) = [x.length]) (hT : S (tmpR g) = [])
    (ho : ∀ j, S (oldR g j) = []) (hn : ∀ j, S (nextR g j) = []) :
    ∃ S', NRuns (initTable g) S S' ((dom g).length * (3 * x.length + 7) + 2) ∧ Ready g x 0 S' := by
  obtain ⟨S', rx, hz, hf⟩ := nruns_seedRows g _ (finRange_nodup _) x.length S hl (fun j _ => ho j)
  refine ⟨S', by simpa only [initTable, List.length_finRange] using rx, ?_⟩
  constructor
  · intro j; rw [row_zero]; exact hz j (List.mem_finRange j)
  · intro j; rw [hf _ (fun k _ => Ne.symm (old_next_ne g k j))]; exact hn j
  · rw [hf _ (fun j _ => by packrat_regs)]; exact hi
  · rw [hf _ (fun j _ => by packrat_regs)]; exact hl
  · rw [hf _ (fun j _ => by packrat_regs)]; exact hT

end Shallot.Packrat.Machine
