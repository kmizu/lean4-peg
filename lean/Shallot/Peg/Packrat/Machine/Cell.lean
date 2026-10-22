import Shallot.Peg.Packrat.Machine.Layout

/-!
# Compile every PEG expression into a cell program

All expression forms use concrete stack programs. The old rows are read
and one value is appended to a specified next row. A grammar-dependent
coefficient bounds the stack steps linearly in input length.
-/

namespace Shallot.Packrat.Machine

open Complexity

/-- The constant coefficient of a cell's linear stack-step budget. -/
def cellCoeff : PExp → Nat
  | .eps => 3
  | .any => 22
  | .chr c => 2 * (chrTest c).flags.length + 20
  | .range lo hi => 2 * (rangeTest lo hi).flags.length + 20
  | .lit s => 10 * s.length + literalCost s 0 + 2
  | .nt _ => 13
  | .seq _ _ => 47
  | .alt _ _ => 34
  | .star _ => 57
  | .notP _ => 20

/-- Compile an expression, reading old rows and appending to next row `j`. -/
def compileCell (g : Grammar) (e : PExp) (he : e ∈ dom g) (j : Node g) : NProg (NK g) :=
  match e with
  | .eps => emptySuccess (posR g) (nextR g j) (by packrat_regs)
  | .any => lexCell (inpR g) (tmpR g) (idxR g) (posR g) (workR g) (nextR g j)
      (by packrat_regs) (by packrat_regs) (by packrat_regs) (by packrat_regs) anyTest
  | .chr c => lexCell (inpR g) (tmpR g) (idxR g) (posR g) (workR g) (nextR g j)
      (by packrat_regs) (by packrat_regs) (by packrat_regs) (by packrat_regs) (chrTest c)
  | .range lo hi => lexCell (inpR g) (tmpR g) (idxR g) (posR g) (workR g) (nextR g j)
      (by packrat_regs) (by packrat_regs) (by packrat_regs) (by packrat_regs) (rangeTest lo hi)
  | .lit s => literalCell (inpR g) (tmpR g) (idxR g) (posR g) (curR g) (workR g) (nextR g j)
      (by packrat_regs) (by packrat_regs) (by packrat_regs) (by packrat_regs) (by packrat_regs) s
  | .nt k => match hr : ruleAt g.rules k with
    | none => npushC (nextR g j) 1
    | some b => readRow (oldR g (nodeIdx g b (dom_rule hr))) (tmpR g) (idxR g) (posR g) (nextR g j)
        (by packrat_regs) (by packrat_regs) (by packrat_regs)
  | .seq a b =>
      let ha := dom_subterm he (show a ∈ subterms (.seq a b) by simp [subterms, mem_subterms_self])
      let hb := dom_subterm he (show b ∈ subterms (.seq a b) by simp [subterms, mem_subterms_self])
      seqCell (oldR g (nodeIdx g a ha)) (oldR g (nodeIdx g b hb)) (tmpR g) (idxR g) (posR g)
        (workR g) (nextR g j) (by packrat_regs) (by packrat_regs) (by packrat_regs)
        (by packrat_regs) (by packrat_regs) (by packrat_regs) (by packrat_regs)
  | .alt a b =>
      let ha := dom_subterm he (show a ∈ subterms (.alt a b) by simp [subterms, mem_subterms_self])
      let hb := dom_subterm he (show b ∈ subterms (.alt a b) by simp [subterms, mem_subterms_self])
      altCell (oldR g (nodeIdx g a ha)) (oldR g (nodeIdx g b hb)) (tmpR g) (idxR g) (posR g)
        (workR g) (nextR g j) (by packrat_regs) (by packrat_regs) (by packrat_regs)
        (by packrat_regs) (by packrat_regs) (by packrat_regs)
  | .star a =>
      let ha := dom_subterm he (show a ∈ subterms (.star a) by simp [subterms, mem_subterms_self])
      starCell (oldR g (nodeIdx g a ha)) (oldR g (nodeIdx g (.star a) he)) (tmpR g) (idxR g) (posR g)
        (workR g) (nextR g j) (by packrat_regs) (by packrat_regs) (by packrat_regs)
        (by packrat_regs) (by packrat_regs) (by packrat_regs) (by packrat_regs) (by packrat_regs)
  | .notP a =>
      let ha := dom_subterm he (show a ∈ subterms (.notP a) by simp [subterms, mem_subterms_self])
      notCell (oldR g (nodeIdx g a ha)) (tmpR g) (idxR g) (posR g) (workR g) (nextR g j)
        (by packrat_regs) (by packrat_regs) (by packrat_regs) (by packrat_regs) (by packrat_regs)

private theorem linear_le (a b n : Nat) (hab : a ≤ b) : a * n + b ≤ b * (n + 1) := by
  rw [Nat.mul_succ]
  have := Nat.mul_le_mul_right n hab
  omega

/-- Every compiled cell realizes one original-table step, changing only its next row. -/
theorem nruns_compileCell (g : Grammar) (x : List Char) (n : Nat) (e : PExp)
    (he : e ∈ dom g) (j : Node g) (S : Lists (NK g)) (hrows : Rows g x n S)
    (hinput : S (inpR g) = inputRow x) (htmp : S (tmpR g) = [])
    {lp : List Nat} {i : Nat} (hp : S (posR g) = lp ++ [i]) (hi : i ≤ x.length) :
    NRuns (compileCell g e he j) S
      (S.set (nextR g j) (S (nextR g j) ++ [code i (iter g x (n + 1) e i)]))
      (cellCoeff e * (x.length + 1)) := by
  cases e with
  | eps =>
    have hx := nruns_emptySuccess (posR g) (nextR g j) (by packrat_regs) S hp
    exact hx.mono (by simp only [cellCoeff]; omega)
  | any =>
    have hx := nruns_lexCell_input x (inpR g) (tmpR g) (idxR g) (posR g) (workR g) (nextR g j)
      (by packrat_regs) (by packrat_regs) (by packrat_regs) (by packrat_regs) (by packrat_regs)
      anyTest S htmp hinput hp hi
    rw [anyValue g x (iter g x n)] at hx
    exact hx.mono (by simp [cellCoeff, anyTest]; omega)
  | chr c =>
    have hx := nruns_lexCell_input x (inpR g) (tmpR g) (idxR g) (posR g) (workR g) (nextR g j)
      (by packrat_regs) (by packrat_regs) (by packrat_regs) (by packrat_regs) (by packrat_regs)
      (chrTest c) S htmp hinput hp hi
    rw [chrValue g x (iter g x n)] at hx
    exact hx.mono (by simpa only [cellCoeff, Nat.add_assoc] using linear_le 10 (2 * (chrTest c).flags.length + 20) x.length (by omega))
  | range lo hi' =>
    have hx := nruns_lexCell_input x (inpR g) (tmpR g) (idxR g) (posR g) (workR g) (nextR g j)
      (by packrat_regs) (by packrat_regs) (by packrat_regs) (by packrat_regs) (by packrat_regs)
      (rangeTest lo hi') S htmp hinput hp hi
    rw [rangeValue g x (iter g x n)] at hx
    exact hx.mono (by simpa only [cellCoeff, Nat.add_assoc] using linear_le 10 (2 * (rangeTest lo hi').flags.length + 20) x.length (by omega))
  | lit s =>
    have hx := nruns_literalCell g x n s (inpR g) (tmpR g) (idxR g) (posR g) (curR g) (workR g)
      (nextR g j) (by packrat_regs) (by packrat_regs) (by packrat_regs) (by packrat_regs)
      (by packrat_regs) (by packrat_regs) S htmp hinput hp hi
    exact hx.mono (literalCost_le s x.length)
  | nt k =>
    simp only [compileCell]
    split
    next hr =>
      have hx := nruns_pushC (nextR g j) S 1
      simpa only [hr, iter, F, code, cellCoeff] using hx.mono
        (show 1 + 1 ≤ 13 * (x.length + 1) by omega)
    next b hr =>
      have hb := dom_rule hr
      have hrow := hrows b hb
      have hv : i < (S (oldR g (nodeIdx g b hb))).length := by simp only [hrow, row_length]; omega
      have hx := nruns_readRow (oldR g (nodeIdx g b hb)) (tmpR g) (idxR g) (posR g) (nextR g j)
        (by packrat_regs) (by packrat_regs) (by packrat_regs) (by packrat_regs) S htmp hp hv
      have heq : (S (oldR g (nodeIdx g b hb)))[i] = code i (iter g x n b i) := by
        simp only [hrow, row_get _ _ _ _ hi]
      rw [heq] at hx
      have ht : 6 * (S (oldR g (nodeIdx g b hb))).length + 4 * i + 7 ≤ 13 * (x.length + 1) := by
        have hl : (S (oldR g (nodeIdx g b hb))).length = x.length + 1 := by simp [hrow]
        omega
      simpa only [hr, iter, F, cellCoeff] using hx.mono ht
  | seq a b =>
    have ha := dom_subterm he (show a ∈ subterms (.seq a b) by simp [subterms, mem_subterms_self])
    have hb := dom_subterm he (show b ∈ subterms (.seq a b) by simp [subterms, mem_subterms_self])
    have hx := nruns_seqCell_round g x n a b (oldR g (nodeIdx g a ha)) (oldR g (nodeIdx g b hb))
      (tmpR g) (idxR g) (posR g) (workR g) (nextR g j)
      (by packrat_regs) (by packrat_regs) (by packrat_regs) (by packrat_regs) (by packrat_regs)
      (by packrat_regs) (by packrat_regs) (by packrat_regs) (by packrat_regs)
      S htmp (hrows a ha) (hrows b hb) hp hi
    exact hx.mono (by simp only [cellCoeff]; omega)
  | alt a b =>
    have ha := dom_subterm he (show a ∈ subterms (.alt a b) by simp [subterms, mem_subterms_self])
    have hb := dom_subterm he (show b ∈ subterms (.alt a b) by simp [subterms, mem_subterms_self])
    have hx := nruns_altCell_round g x n a b (oldR g (nodeIdx g a ha)) (oldR g (nodeIdx g b hb))
      (tmpR g) (idxR g) (posR g) (workR g) (nextR g j)
      (by packrat_regs) (by packrat_regs) (by packrat_regs) (by packrat_regs) (by packrat_regs)
      (by packrat_regs) (by packrat_regs) (by packrat_regs) (by packrat_regs)
      S htmp (hrows a ha) (hrows b hb) hp hi
    exact hx.mono (by simp only [cellCoeff]; omega)
  | star a =>
    have ha := dom_subterm he (show a ∈ subterms (.star a) by simp [subterms, mem_subterms_self])
    have hx := nruns_starCell_round g x n a (oldR g (nodeIdx g a ha)) (oldR g (nodeIdx g (.star a) he))
      (tmpR g) (idxR g) (posR g) (workR g) (nextR g j)
      (by packrat_regs) (by packrat_regs) (by packrat_regs) (by packrat_regs) (by packrat_regs)
      (by packrat_regs) (by packrat_regs) (by packrat_regs) (by packrat_regs) (by packrat_regs)
      S htmp (hrows a ha) (hrows (.star a) he) hp hi
    exact hx.mono (by simp only [cellCoeff]; omega)
  | notP a =>
    have ha := dom_subterm he (show a ∈ subterms (.notP a) by simp [subterms, mem_subterms_self])
    have hx := nruns_notCell_round g x n a (oldR g (nodeIdx g a ha)) (tmpR g) (idxR g) (posR g)
      (workR g) (nextR g j) (by packrat_regs) (by packrat_regs) (by packrat_regs)
      (by packrat_regs) (by packrat_regs) (by packrat_regs) S htmp (hrows a ha) hp hi
    exact hx.mono (by simp only [cellCoeff]; omega)

end Shallot.Packrat.Machine
