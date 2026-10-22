import Shallot.Peg.Packrat.Machine.Initialize

/-!
# Load actual bit input into the character row

The two characters represented by false and true are fixed parameters.
The machine consumes `nInit`'s bits, records their count, creates positive
character codes in input order, and appends the zero end marker.
-/

namespace Shallot.Packrat.Machine

open Complexity

def inputMax (f : Bool → Char) : Nat := max (symbolCode (f false)) (symbolCode (f true))

def inputBody (g : Grammar) (f : Bool → Char) : NProg (NK g) :=
  .seq (.ite (inpR g) .zero
    (.seq (.prim (.pop (inpR g))) (npushC (tmpR g) (symbolCode (f false))))
    (.seq (.prim (.pop (inpR g))) (npushC (tmpR g) (symbolCode (f true)))))
    (.prim (.inc (lenR g)))

def loadInput (g : Grammar) (f : Bool → Char) : NProg (NK g) :=
  .seq (.prim (.pushZ (lenR g)))
    (.seq (.loop (inpR g) .nonempty (inputBody g f))
      (.seq (replaceRow (tmpR g) (inpR g) (workR g) (by packrat_regs) (by packrat_regs))
        (.prim (.pushZ (inpR g)))))

def inputCost (f : Bool → Char) (N : Nat) : Nat := N * (inputMax f + 11) + 6

/-- Convert a stack of bits into an input row, changing only input and length. -/
theorem nruns_loadInput (g : Grammar) (f : Bool → Char) (w : List Bool) (S : Lists (NK g))
    (hi : S (inpR g) = (w.map bitElem).reverse) (hl : S (lenR g) = [])
    (ht : S (tmpR g) = []) (hw : S (workR g) = []) :
    NRuns (loadInput g f) S ((S.set (lenR g) [w.length]).set (inpR g) (inputRow (w.map f)))
      (inputCost f w.length) := by
  have hil : inpR g ≠ lenR g := by packrat_regs
  have hit : inpR g ≠ tmpR g := by packrat_regs
  have hli : lenR g ≠ inpR g := by packrat_regs
  have hlt : lenR g ≠ tmpR g := by packrat_regs
  have htl : tmpR g ≠ lenR g := by packrat_regs
  let sy := fun b => symbolCode (f b)
  let F : Nat → Lists (NK g) := fun m =>
    ((S.set (inpR g) ((w.drop m).map bitElem).reverse).set (tmpR g) ((w.take m).map sy)).set (lenR g) [m]
  have hFi : ∀ m, F m (inpR g) = ((w.drop m).map bitElem).reverse := fun m => by simp only [F]; lists_at
  have hFt : ∀ m, F m (tmpR g) = (w.take m).map sy := fun m => by simp only [F]; lists_at
  have hFl : ∀ m, F m (lenR g) = [m] := fun m => by simp [F]
  have lp := nruns_family_const (i := inpR g) (c := .nonempty) (p := inputBody g f)
    F w.length (inputMax f + 4)
    (fun m hm => by
      rw [hFi]
      apply eval_nonempty_ne
      intro he
      have hh := congrArg List.length he
      simp only [List.length_reverse, List.length_map, List.length_drop, List.length_nil] at hh
      omega)
    (by rw [hFi]; simp)
    (fun m hm => by
      have hd : w.drop m = w[m] :: w.drop (m + 1) := List.drop_eq_getElem_cons hm
      have hp : F m (inpR g) = ((w.drop (m + 1)).map bitElem).reverse ++ [bitElem w[m]] := by
        rw [hFi, hd]; simp only [List.map_cons, List.reverse_cons]
      have pp := nruns_pop (inpR g) (F m) hp
      let S₁ := (F m).set (inpR g) ((w.drop (m + 1)).map bitElem).reverse
      have pc := nruns_pushC (tmpR g) S₁ (sy w[m])
      let S₂ := S₁.set (tmpR g) (S₁ (tmpR g) ++ [sy w[m]])
      have br : NRuns (.ite (inpR g) .zero
          (.seq (.prim (.pop (inpR g))) (npushC (tmpR g) (symbolCode (f false))))
          (.seq (.prim (.pop (inpR g))) (npushC (tmpR g) (symbolCode (f true)))))
          (F m) S₂ (inputMax f + 3) := by
        cases hb : w[m] with
        | false =>
          have hx := (pp.seq pc).iteT (i := inpR g) (c := .zero)
            (q := .seq (.prim (.pop (inpR g))) (npushC (tmpR g) (symbolCode (f true))))
            (by rw [hp, hb]; simp [bitElem])
          have hmax : sy w[m] ≤ inputMax f := by rw [hb]; exact Nat.le_max_left _ _
          simpa only [S₂, sy, hb] using hx.mono (by omega)
        | true =>
          have hx := (pp.seq pc).iteF (i := inpR g) (c := .zero)
            (p := .seq (.prim (.pop (inpR g))) (npushC (tmpR g) (symbolCode (f false))))
            (by rw [hp, hb]; simp [bitElem])
          have hmax : sy w[m] ≤ inputMax f := by rw [hb]; exact Nat.le_max_right _ _
          simpa only [S₂, sy, hb] using hx.mono (by omega)
      have ic := nruns_inc (lenR g) S₂ (l := []) (v := m)
        (by simp only [S₂, S₁, Lists.set_ne _ _ hlt, Lists.set_ne _ _ hli]; exact hFl m)
      have htake : w.take (m + 1) = w.take m ++ [w[m]] := List.take_succ_eq_append_getElem hm
      have he : S₂.set (lenR g) [m + 1] = F (m + 1) := by
        simp only [S₂, S₁, F, htake, List.map_append, List.map_singleton]
        lists_eq
      simp only [List.nil_append] at ic
      rw [he] at ic
      exact br.seq ic)
  have pz := nruns_pushZ (lenR g) S
  have he₀ : S.set (lenR g) (S (lenR g) ++ [0]) = F 0 := by
    simp only [F, List.drop_zero, List.take_zero, List.map_nil, hl, List.nil_append]
    lists_eq
  rw [he₀] at pz
  have hwi : workR g ≠ inpR g := by packrat_regs
  have hwt : workR g ≠ tmpR g := by packrat_regs
  have hwl : workR g ≠ lenR g := by packrat_regs
  have mv := nruns_replaceRow (tmpR g) (inpR g) (workR g) (by packrat_regs) (by packrat_regs)
    (by packrat_regs) (F w.length)
    (by simp only [F, Lists.set_ne _ _ hwl, Lists.set_ne _ _ hwt, Lists.set_ne _ _ hwi]; exact hw)
  let S₁ := ((F w.length).set (inpR g) (F w.length (tmpR g))).set (tmpR g) []
  have ez := nruns_pushZ (inpR g) S₁
  have he₁ : S₁.set (inpR g) (S₁ (inpR g) ++ [0]) =
      (S.set (lenR g) [w.length]).set (inpR g) (inputRow (w.map f)) := by
    simp only [S₁, F, List.drop_length, List.take_length, List.map_nil, List.reverse_nil,
      inputRow, List.map_map, Function.comp_def, sy]
    lists_eq
  rw [he₁] at ez
  have hfLen : (F w.length (tmpR g)).length = w.length := by rw [hFt]; simp
  have heCost : w.length * (inputMax f + 11) = w.length * (inputMax f + 5) + 6 * w.length := by
    rw [show inputMax f + 11 = (inputMax f + 5) + 6 by omega, Nat.mul_add, Nat.mul_comm w.length 6]
  refine (pz.seq (lp.seq (mv.seq ez))).mono ?_
  rw [hFi, hfLen]
  simp only [List.drop_length, List.map_nil, List.reverse_nil, List.length_nil, Nat.mul_zero,
    inputCost, heCost, Nat.add_assoc, Nat.reduceAdd]
  omega

/-- The register state obtained from the actual initial stack-machine input. -/
def loaded (g : Grammar) (f : Bool → Char) (w : List Bool) : Lists (NK g) :=
  ((nInit (NK g) w).set (lenR g) [w.length]).set (inpR g) (inputRow (w.map f))

theorem nruns_load_nInit (g : Grammar) (f : Bool → Char) (w : List Bool) :
    NRuns (loadInput g f) (nInit (NK g) w) (loaded g f w) (inputCost f w.length) := by
  apply nruns_loadInput
  · simp [nInit, inpR]
  · simp [nInit, lenR]
  · simp [nInit, tmpR]
  · simp [nInit, workR]

end Shallot.Packrat.Machine
