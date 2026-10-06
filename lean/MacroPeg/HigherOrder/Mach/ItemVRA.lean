import MacroPeg.HigherOrder.Mach.EvalSpec
import MacroPeg.HigherOrder.Mach.VarTy
import Complexity.NFrame

/-!
# The item programs of variables, rules and applications

The items with tags `9` (a variable), `10` (a rule) and `12` (an application) as programs on the stacks of the
evaluation stage (`itemVarP`, `itemRuleP`, `itemAppP`), each proved to do the item's step (`ItemRuns`).

The programs are built from a few verified pieces (all helpers are prefixed `vra_`):

* `vra_xferP`: move up to `k` numbers from one stack to another, copying them onto a third;
* `vra_sliceP`: append the slice `(L.drop off).take len` of a stack `L` to another stack, counting its length;
* `vra_repeatP`: run a body a counted number of times;
* `vra_sumP`, `vra_mulP`: add up a stack, multiply a top;
* `vra_eqP`: compare two stacks as lists.

Counters and other single numbers live on the tops of stacks whose contents below are left alone; lists live on
the scratch stacks `18`–`33`, empty before and after.
-/

namespace Shallot.MacroPeg.Mach

open Complexity

set_option linter.unusedSimpArgs false

/-! ## Comparing updated stacks -/

/-- Pointwise comparison of stacks updated at the listed places (the variable `x` is the place), with the given
facts. -/
syntax "vra_pt" ident "[" term,* "]" "[" term,* "]" : tactic
macro_rules
  | `(tactic| vra_pt $x [$ts,*] [$hs,*]) => do
    let ts := ts.getElems
    let args ← hs.getElems.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
    if h : 0 < ts.size then
      let t := ts[0]
      let rest := ts.extract 1 ts.size
      `(tactic| (by_cases hx : $x = $t
                 case pos => subst hx; simp [Lists.set, $args,*]
                 case neg => vra_pt $x [$rest,*] [hx, $hs,*]))
    else `(tactic| simp [Lists.set, $args,*])

/-- Two states updated at the listed places are equal (using the given facts). -/
macro "vra_ext" "[" ts:term,* "]" "[" hs:term,* "]" : tactic => `(tactic| (funext y; vra_pt y [$ts,*] [$hs,*]))

section Generic

variable {K : Nat}

/-! ## Loops, one round at a time -/

theorem vra_loop_step {i : Fin K} {c : NTest} {p : NProg K} {S S₁ S₂ : Lists K} {T₁ T₂ : Nat}
    (hc : c.eval (S i) = true) (h₁ : NRuns p S S₁ T₁) (h₂ : NRuns (.loop i c p) S₁ S₂ T₂) :
    NRuns (.loop i c p) S S₂ (T₁ + 1 + T₂) :=
  let ⟨t₁, ht₁, x₁⟩ := h₁; let ⟨t₂, ht₂, x₂⟩ := h₂; ⟨t₁ + 1 + t₂, by omega, .loopC trivial hc x₁ x₂⟩

/-! ## Moving with a copy -/

/-- One round of `vra_xferP`: if `A` is not empty, count `c` down, copy the top of `A` onto `o`, count it on `r`,
and move it onto `B`; otherwise set the count to `0`. -/
def vra_xferBody (c A B o r : Fin K) (hAo : A ≠ o) (hAB : A ≠ B) : NProg K :=
  .ite A .nonempty (.seq (.prim (.dec c)) (.seq (.prim (.dup A o hAo)) (.seq (.prim (.inc r)) (nmv A B hAB))))
    (.seq (.prim (.pop c)) (.prim (.pushZ c)))

/-- Move up to `k` numbers (the popped top of `c`) from `A` onto `B` (reversing them), copying them onto `o` and
adding their number to the top of `r`. -/
def vra_xferP (c A B o r : Fin K) (hAo : A ≠ o) (hAB : A ≠ B) : NProg K :=
  .seq (.loop c .pos (vra_xferBody c A B o r hAo hAB)) (.prim (.pop c))

/-- The stacks of `vra_xferP` are all different. -/
structure VraX (c A B o r : Fin K) : Prop where
  cA : c ≠ A
  cB : c ≠ B
  co : c ≠ o
  cr : c ≠ r
  AB : A ≠ B
  Ao : A ≠ o
  Ar : A ≠ r
  Bo : B ≠ o
  Br : B ≠ r
  or : o ≠ r

theorem vra_xferLoop {c A B o r : Fin K} (hd : VraX c A B o r) :
    ∀ (k : Nat) (S : Lists K) (lc Y Z lr : List Nat) (v : Nat), S c = lc ++ [k] → S A = Y ++ Z →
      S r = lr ++ [v] → Z.length = min k (Y ++ Z).length →
      NRuns (.loop c .pos (vra_xferBody c A B o r hd.Ao hd.AB)) S
        (((((S.set c (lc ++ [0])).set A Y).set B (S B ++ Z.reverse)).set o (S o ++ Z.reverse)).set r
          (lr ++ [v + Z.length])) (8 * Z.length + 5) := by
  have hcA := hd.cA; have hcB := hd.cB; have hco := hd.co; have hcr := hd.cr; have hAB := hd.AB
  have hAo := hd.Ao; have hAr := hd.Ar; have hBo := hd.Bo; have hBr := hd.Br; have hor := hd.or
  intro k
  induction k with
  | zero =>
    intro S lc Y Z lr v hc hA hr hZ
    have hZ0 : Z = [] := List.eq_nil_of_length_eq_zero (by simpa using hZ)
    subst hZ0
    have e : ((((S.set c (lc ++ [0])).set A Y).set B (S B ++ ([] : List Nat).reverse)).set o (S o ++ ([] : List Nat).reverse)).set r
        (lr ++ [v + ([] : List Nat).length]) = S := by
      simp only [List.append_nil] at hA
      vra_ext [c, A, B, o, r] [hcA, hcB, hco, hcr, hAB, hAo, hAr, hBo, hBr, hor, hcA.symm, hcB.symm, hco.symm, hcr.symm, hAB.symm, hAo.symm, hAr.symm, hBo.symm, hBr.symm, hor.symm, hc, hA, hr]
    rw [e]
    exact (nruns_loop_exit (by rw [hc]; simp)).mono (by omega)
  | succ k ih =>
    intro S lc Y Z lr v hc hA hr hZ
    rcases List.eq_nil_or_concat Z with hZ0 | ⟨Z', y, hZ'⟩
    · subst hZ0
      have hY : Y = [] := by
        simp only [List.length_nil, List.append_nil] at hZ
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst hY
      have x₁ := nruns_pop c S hc
      have x₂ := nruns_pushZ c (S.set c lc)
      have x₃ := nruns_loop_exit (i := c) (c := .pos) (p := vra_xferBody c A B o r hAo hAB)
        (S := (S.set c lc).set c ((S.set c lc) c ++ [0])) (by simp)
      have xb := (x₁.seq x₂).iteF (i := A) (c := .nonempty)
        (p := .seq (.prim (.dec c)) (.seq (.prim (.dup A o hAo)) (.seq (.prim (.inc r)) (nmv A B hAB))))
        (by rw [hA]; rfl)
      have e : (S.set c lc).set c ((S.set c lc) c ++ [0]) = ((((S.set c (lc ++ [0])).set A []).set B
          (S B ++ ([] : List Nat).reverse)).set o (S o ++ ([] : List Nat).reverse)).set r
            (lr ++ [v + ([] : List Nat).length]) := by
        simp only [List.nil_append] at hA
        vra_ext [c, A, B, o, r] [hcA, hcB, hco, hcr, hAB, hAo, hAr, hBo, hBr, hor, hcA.symm, hcB.symm, hco.symm, hcr.symm, hAB.symm, hAo.symm, hAr.symm, hBo.symm, hBr.symm, hor.symm, hc, hA, hr]
      have := vra_loop_step (by rw [hc]; simp) xb x₃
      rw [e] at this
      exact this.mono (by simp)
    · simp only [List.concat_eq_append] at hZ'
      subst hZ'
      have x₁ := nruns_dec c S hc
      simp only [Nat.add_sub_cancel] at x₁
      let S₁ := S.set c (lc ++ [k])
      have x₂ := nruns_dup A o hAo S₁ (l := Y ++ Z') (v := y)
        (by simp only [S₁]; rw [Lists.set_ne _ _ (Ne.symm hcA), hA, List.append_assoc])
      let S₂ := S₁.set o (S₁ o ++ [y])
      have x₃ := nruns_inc r S₂ (l := lr) (v := v) (by simp only [S₂, S₁]; simp [Lists.set, hr, hor.symm, hcr.symm])
      let S₃ := S₂.set r (lr ++ [v + 1])
      have x₄ := nruns_mv A B hAB S₃ (l := Y ++ Z') (v := y)
        (by simp only [S₃, S₂, S₁]; simp [Lists.set, hA, hAr, hAo, hcA.symm])
      let S₄ := (S₃.set B (S₃ B ++ [y])).set A (Y ++ Z')
      have hlen : Z'.length = min k (Y ++ Z').length := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hZ ⊢; omega
      have x₅ := ih S₄ lc Y Z' lr (v + 1) (by simp only [S₄, S₃, S₂, S₁]; simp [Lists.set, hcA, hcB, hcr, hco])
        (by simp [S₄]) (by simp only [S₄, S₃, S₂, S₁]; simp [Lists.set, hAr.symm, hBr.symm]) hlen
      have e : ((((S₄.set c (lc ++ [0])).set A Y).set B (S₄ B ++ Z'.reverse)).set o (S₄ o ++ Z'.reverse)).set r
          (lr ++ [v + 1 + Z'.length]) = ((((S.set c (lc ++ [0])).set A Y).set B
            (S B ++ (Z' ++ [y]).reverse)).set o (S o ++ (Z' ++ [y]).reverse)).set r
              (lr ++ [v + (Z' ++ [y]).length]) := by
        have hB4 : S₄ B = S B ++ [y] := by
          simp only [S₄, S₃, S₂, S₁]; simp [Lists.set, hAB.symm, hBr, hBo, hcB.symm]
        have ho4 : S₄ o = S o ++ [y] := by
          simp only [S₄, S₃, S₂, S₁]; simp [Lists.set, hAo.symm, hBo.symm, hor, hco.symm]
        rw [hB4, ho4]
        have e1 : v + 1 + Z'.length = v + (Z' ++ [y]).length := by simp; omega
        rw [e1]
        simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
          List.append_assoc, List.singleton_append]
        simp only [S₄, S₃, S₂, S₁]
        vra_ext [c, A, B, o, r] [hcA, hcB, hco, hcr, hAB, hAo, hAr, hBo, hBr, hor, hcA.symm, hcB.symm, hco.symm, hcr.symm, hAB.symm, hAo.symm, hAr.symm, hBo.symm, hBr.symm, hor.symm]
      rw [e] at x₅
      have xb := (x₁.seq (x₂.seq (x₃.seq x₄))).iteT (i := A) (c := .nonempty)
        (q := .seq (.prim (.pop c)) (.prim (.pushZ c))) (by rw [hA, ← List.append_assoc]; exact eval_nonempty_snoc _ _)
      exact (vra_loop_step (by rw [hc]; simp) xb x₅).mono (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)

theorem vra_xfer {c A B o r : Fin K} (hd : VraX c A B o r) (S : Lists K) {lc Y Z lr : List Nat} {k v : Nat}
    (hc : S c = lc ++ [k]) (hA : S A = Y ++ Z) (hr : S r = lr ++ [v]) (hZ : Z.length = min k (Y ++ Z).length) :
    NRuns (vra_xferP c A B o r hd.Ao hd.AB) S
      ((((((S.set c lc).set A Y).set B (S B ++ Z.reverse)).set o (S o ++ Z.reverse)).set r
        (lr ++ [v + Z.length]))) (8 * Z.length + 6) := by
  have hcA := hd.cA; have hcB := hd.cB; have hco := hd.co; have hcr := hd.cr
  have x₁ := vra_xferLoop hd k S lc Y Z lr v hc hA hr hZ
  have x₂ := nruns_pop c ((((((S.set c (lc ++ [0])).set A Y).set B (S B ++ Z.reverse)).set o
    (S o ++ Z.reverse)).set r (lr ++ [v + Z.length]))) (l := lc) (v := 0)
    (by simp [Lists.set, hcA, hcB, hco, hcr])
  have e : (((((S.set c (lc ++ [0])).set A Y).set B (S B ++ Z.reverse)).set o
      (S o ++ Z.reverse)).set r (lr ++ [v + Z.length])).set c lc = ((((((S.set c lc).set A Y).set B
        (S B ++ Z.reverse)).set o (S o ++ Z.reverse)).set r (lr ++ [v + Z.length]))) := by
    vra_ext [c, A, B, o, r] [hcA, hcB, hco, hcr, hd.AB, hd.Ao, hd.Ar, hd.Bo, hd.Br, hd.or]
  rw [e] at x₂
  exact (x₁.seq x₂).mono (by omega)

/-! ## Slices -/

/-- The stacks of `vra_sliceP` are all different. -/
structure VraS (src dst ctr offS lenS A B D E : Fin K) : Prop where
  nd : [src, dst, ctr, offS, lenS, A, B, D, E].Nodup

theorem VraS.ne {src dst ctr offS lenS A B D E : Fin K} (h : VraS src dst ctr offS lenS A B D E) :
    src ≠ dst ∧ src ≠ ctr ∧ src ≠ offS ∧ src ≠ lenS ∧ src ≠ A ∧ src ≠ B ∧ src ≠ D ∧ src ≠ E ∧
    dst ≠ ctr ∧ dst ≠ offS ∧ dst ≠ lenS ∧ dst ≠ A ∧ dst ≠ B ∧ dst ≠ D ∧ dst ≠ E ∧
    ctr ≠ offS ∧ ctr ≠ lenS ∧ ctr ≠ A ∧ ctr ≠ B ∧ ctr ≠ D ∧ ctr ≠ E ∧
    offS ≠ lenS ∧ offS ≠ A ∧ offS ≠ B ∧ offS ≠ D ∧ offS ≠ E ∧
    lenS ≠ A ∧ lenS ≠ B ∧ lenS ≠ D ∧ lenS ≠ E ∧ A ≠ B ∧ A ≠ D ∧ A ≠ E ∧ B ≠ D ∧ B ≠ E ∧ D ≠ E := by
  have := h.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at this
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, ⟨h9, h10, h11, h12, h13, h14, h15⟩, ⟨h16, h17, h18, h19, h20, h21⟩,
    ⟨h22, h23, h24, h25, h26⟩, ⟨h27, h28, h29, h30⟩, ⟨h31, h32, h33⟩, ⟨h34, h35⟩, h36, -⟩ := this
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23,
    h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36⟩

theorem VraS.x₁ {src dst ctr offS lenS A B D E : Fin K} (h : VraS src dst ctr offS lenS A B D E) :
    VraX offS A B D E := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h23, h24, h25, h26, -, -, -, -,
    h31, h32, h33, h34, h35, h36⟩ := h.ne
  exact ⟨h23, h24, h25, h26, h31, h32, h33, h34, h35, h36⟩

theorem VraS.x₂ {src dst ctr offS lenS A B D E : Fin K} (h : VraS src dst ctr offS lenS A B D E) :
    VraX lenS A B dst ctr := by
  obtain ⟨-, -, -, -, -, -, -, -, h9, -, h11, h12, h13, -, -, -, h17, h18, h19, -, -, -, -, -, -, -,
    h27, h28, -, -, h31, -, -, -, -, -⟩ := h.ne
  exact ⟨h27, h28, Ne.symm h11, Ne.symm h17, h31, Ne.symm h12, Ne.symm h18, Ne.symm h13, Ne.symm h19, h9⟩

/-- Append `(L.drop off).take len` of `src` (holding `L`) to `dst` and add its length to the top of `ctr`; `off`
and `len` are popped from `offS` and `lenS`. Scratch `A B D E` (empty before and after). -/
def vra_sliceP (src dst ctr offS lenS A B D E : Fin K) (h : VraS src dst ctr offS lenS A B D E) : NProg K :=
  .seq (nmvAll src A h.ne.2.2.2.2.1) (.seq (.prim (.pushZ E)) (.seq (vra_xferP offS A B D E h.x₁.Ao h.x₁.AB)
    (.seq (nclr D) (.seq (.prim (.pop E)) (.seq (vra_xferP lenS A B dst ctr h.x₂.Ao h.x₂.AB)
      (.seq (nmvAll B A (Ne.symm h.x₁.AB)) (nmvAll A src (Ne.symm h.ne.2.2.2.2.1))))))))

/-- The cost of a slice of a stack of length `n`. -/
def vra_sliceCost (n : Nat) : Nat := 30 * n + 20

theorem vra_slice {src dst ctr offS lenS A B D E : Fin K} (h : VraS src dst ctr offS lenS A B D E) (S : Lists K)
    {lo ll lr : List Nat} {off len v : Nat} (hA : S A = []) (hB : S B = []) (hD : S D = []) (hE : S E = [])
    (ho : S offS = lo ++ [off]) (hl : S lenS = ll ++ [len]) (hr : S ctr = lr ++ [v]) :
    NRuns (vra_sliceP src dst ctr offS lenS A B D E h) S
      ((((S.set offS lo).set lenS ll).set dst (S dst ++ ((S src).drop off).take len)).set ctr
        (lr ++ [v + (((S src).drop off).take len).length])) (vra_sliceCost (S src).length) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23,
    h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36⟩ := h.ne
  obtain ⟨L, hL⟩ : ∃ L, S src = L := ⟨_, rfl⟩
  rw [hL]
  -- everything onto `A`, reversed
  have x₁ := nruns_mvAll src A h5 S
  rw [hA, List.nil_append, hL] at x₁
  let S₁ := (S.set A L.reverse).set src []
  have x₂ := nruns_pushZ E S₁
  let S₂ := S₁.set E (S₁ E ++ [0])
  have hS₂E : S₂ E = [0] := by simp [S₂, S₁, Lists.set, h8.symm, h33.symm, hE]
  -- skip `off`
  let m₁ := min off L.length
  have hsplit₁ : L.reverse = (L.drop m₁).reverse ++ (L.take m₁).reverse := by
    rw [← List.reverse_append, List.take_append_drop]
  have x₃ := vra_xfer h.x₁ S₂ (lc := lo) (k := off) (lr := []) (v := 0) (Y := (L.drop m₁).reverse)
    (Z := (L.take m₁).reverse) (by simp [S₂, S₁, Lists.set, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, (h1).symm, (h2).symm, (h3).symm, (h4).symm, (h5).symm, (h6).symm, (h7).symm, (h8).symm, (h9).symm, (h10).symm, (h11).symm, (h12).symm, (h13).symm, (h14).symm, (h15).symm, (h16).symm, (h17).symm, (h18).symm, (h19).symm, (h20).symm, (h21).symm, (h22).symm, (h23).symm, (h24).symm, (h25).symm, (h26).symm, (h27).symm, (h28).symm, (h29).symm, (h30).symm, (h31).symm, (h32).symm, (h33).symm, (h34).symm, (h35).symm, (h36).symm, ho])
    (by simp only [S₂, S₁]; rw [Lists.set_ne _ _ h33, Lists.set_ne _ _ h5.symm, Lists.set_same, hsplit₁])
    (by rw [hS₂E]; rfl) (by rw [← hsplit₁]; simp [m₁])
  let S₃ := ((((S₂.set offS lo).set A (L.drop m₁).reverse).set B (S₂ B ++ (L.take m₁).reverse.reverse)).set D
    (S₂ D ++ (L.take m₁).reverse.reverse)).set E ([] ++ [0 + (L.take m₁).reverse.length])
  have hS₃D : S₃ D = L.take m₁ := by simp [S₃, S₂, S₁, Lists.set, hD, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, (h1).symm, (h2).symm, (h3).symm, (h4).symm, (h5).symm, (h6).symm, (h7).symm, (h8).symm, (h9).symm, (h10).symm, (h11).symm, (h12).symm, (h13).symm, (h14).symm, (h15).symm, (h16).symm, (h17).symm, (h18).symm, (h19).symm, (h20).symm, (h21).symm, (h22).symm, (h23).symm, (h24).symm, (h25).symm, (h26).symm, (h27).symm, (h28).symm, (h29).symm, (h30).symm, (h31).symm, (h32).symm, (h33).symm, (h34).symm, (h35).symm, (h36).symm]
  have x₄ := nruns_clr D S₃
  rw [hS₃D] at x₄
  let S₄ := S₃.set D []
  have x₅ := nruns_pop E S₄ (l := []) (v := m₁) (by simp [S₄, S₃, Lists.set, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, (h1).symm, (h2).symm, (h3).symm, (h4).symm, (h5).symm, (h6).symm, (h7).symm, (h8).symm, (h9).symm, (h10).symm, (h11).symm, (h12).symm, (h13).symm, (h14).symm, (h15).symm, (h16).symm, (h17).symm, (h18).symm, (h19).symm, (h20).symm, (h21).symm, (h22).symm, (h23).symm, (h24).symm, (h25).symm, (h26).symm, (h27).symm, (h28).symm, (h29).symm, (h30).symm, (h31).symm, (h32).symm, (h33).symm, (h34).symm, (h35).symm, (h36).symm, m₁])
  let S₅ := S₄.set E []
  -- copy `len`
  let M := L.drop m₁
  let m₂ := min len M.length
  have hsplit₂ : M.reverse = (M.drop m₂).reverse ++ (M.take m₂).reverse := by
    rw [← List.reverse_append, List.take_append_drop]
  have x₆ := vra_xfer h.x₂ S₅ (lc := ll) (k := len) (lr := lr) (v := v) (Y := (M.drop m₂).reverse)
    (Z := (M.take m₂).reverse) (by simp [S₅, S₄, S₃, S₂, S₁, Lists.set, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, (h1).symm, (h2).symm, (h3).symm, (h4).symm, (h5).symm, (h6).symm, (h7).symm, (h8).symm, (h9).symm, (h10).symm, (h11).symm, (h12).symm, (h13).symm, (h14).symm, (h15).symm, (h16).symm, (h17).symm, (h18).symm, (h19).symm, (h20).symm, (h21).symm, (h22).symm, (h23).symm, (h24).symm, (h25).symm, (h26).symm, (h27).symm, (h28).symm, (h29).symm, (h30).symm, (h31).symm, (h32).symm, (h33).symm, (h34).symm, (h35).symm, (h36).symm, hl])
    (by simp only [S₅, S₄, S₃]; simp only [Lists.set, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, (h1).symm, (h2).symm, (h3).symm, (h4).symm, (h5).symm, (h6).symm, (h7).symm, (h8).symm, (h9).symm, (h10).symm, (h11).symm, (h12).symm, (h13).symm, (h14).symm, (h15).symm, (h16).symm, (h17).symm, (h18).symm, (h19).symm, (h20).symm, (h21).symm, (h22).symm, (h23).symm, (h24).symm, (h25).symm, (h26).symm, (h27).symm, (h28).symm, (h29).symm, (h30).symm, (h31).symm, (h32).symm, (h33).symm, (h34).symm, (h35).symm, (h36).symm, if_false, if_true]; simp [hsplit₂, M])
    (by simp [S₅, S₄, S₃, S₂, S₁, Lists.set, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, (h1).symm, (h2).symm, (h3).symm, (h4).symm, (h5).symm, (h6).symm, (h7).symm, (h8).symm, (h9).symm, (h10).symm, (h11).symm, (h12).symm, (h13).symm, (h14).symm, (h15).symm, (h16).symm, (h17).symm, (h18).symm, (h19).symm, (h20).symm, (h21).symm, (h22).symm, (h23).symm, (h24).symm, (h25).symm, (h26).symm, (h27).symm, (h28).symm, (h29).symm, (h30).symm, (h31).symm, (h32).symm, (h33).symm, (h34).symm, (h35).symm, (h36).symm, hr]) (by rw [← hsplit₂]; simp [m₂])
  let S₆ := (((((S₅.set lenS ll).set A (M.drop m₂).reverse).set B (S₅ B ++ (M.take m₂).reverse.reverse)).set dst
    (S₅ dst ++ (M.take m₂).reverse.reverse)).set ctr (lr ++ [v + (M.take m₂).reverse.length]))
  have hS₆B : S₆ B = L.take m₁ ++ M.take m₂ := by simp [S₆, S₅, S₄, S₃, S₂, S₁, Lists.set, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, (h1).symm, (h2).symm, (h3).symm, (h4).symm, (h5).symm, (h6).symm, (h7).symm, (h8).symm, (h9).symm, (h10).symm, (h11).symm, (h12).symm, (h13).symm, (h14).symm, (h15).symm, (h16).symm, (h17).symm, (h18).symm, (h19).symm, (h20).symm, (h21).symm, (h22).symm, (h23).symm, (h24).symm, (h25).symm, (h26).symm, (h27).symm, (h28).symm, (h29).symm, (h30).symm, (h31).symm, (h32).symm, (h33).symm, (h34).symm, (h35).symm, (h36).symm, hB]
  have hS₆A : S₆ A = (M.drop m₂).reverse := by simp [S₆, Lists.set, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, (h1).symm, (h2).symm, (h3).symm, (h4).symm, (h5).symm, (h6).symm, (h7).symm, (h8).symm, (h9).symm, (h10).symm, (h11).symm, (h12).symm, (h13).symm, (h14).symm, (h15).symm, (h16).symm, (h17).symm, (h18).symm, (h19).symm, (h20).symm, (h21).symm, (h22).symm, (h23).symm, (h24).symm, (h25).symm, (h26).symm, (h27).symm, (h28).symm, (h29).symm, (h30).symm, (h31).symm, (h32).symm, (h33).symm, (h34).symm, (h35).symm, (h36).symm]
  have x₇ := nruns_mvAll B A (Ne.symm h31) S₆
  rw [hS₆B, hS₆A] at x₇
  let S₇ := (S₆.set A ((M.drop m₂).reverse ++ (L.take m₁ ++ M.take m₂).reverse)).set B []
  have x₈ := nruns_mvAll A src (Ne.symm h5) S₇
  have hS₇A : S₇ A = (M.drop m₂).reverse ++ (L.take m₁ ++ M.take m₂).reverse := by simp [S₇, Lists.set, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, (h1).symm, (h2).symm, (h3).symm, (h4).symm, (h5).symm, (h6).symm, (h7).symm, (h8).symm, (h9).symm, (h10).symm, (h11).symm, (h12).symm, (h13).symm, (h14).symm, (h15).symm, (h16).symm, (h17).symm, (h18).symm, (h19).symm, (h20).symm, (h21).symm, (h22).symm, (h23).symm, (h24).symm, (h25).symm, (h26).symm, (h27).symm, (h28).symm, (h29).symm, (h30).symm, (h31).symm, (h32).symm, (h33).symm, (h34).symm, (h35).symm, (h36).symm]
  have hS₇s : S₇ src = [] := by simp [S₇, S₆, S₅, S₄, S₃, S₂, S₁, Lists.set, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, (h1).symm, (h2).symm, (h3).symm, (h4).symm, (h5).symm, (h6).symm, (h7).symm, (h8).symm, (h9).symm, (h10).symm, (h11).symm, (h12).symm, (h13).symm, (h14).symm, (h15).symm, (h16).symm, (h17).symm, (h18).symm, (h19).symm, (h20).symm, (h21).symm, (h22).symm, (h23).symm, (h24).symm, (h25).symm, (h26).symm, (h27).symm, (h28).symm, (h29).symm, (h30).symm, (h31).symm, (h32).symm, (h33).symm, (h34).symm, (h35).symm, (h36).symm]
  have hback : (M.drop m₂).reverse ++ (L.take m₁ ++ M.take m₂).reverse = L.reverse := by
    rw [← List.reverse_append, List.append_assoc, List.take_append_drop, List.take_append_drop]
  rw [hS₇A, hS₇s, hback, List.reverse_reverse, List.nil_append] at x₈
  have hW : M.take m₂ = (L.drop off).take len := by
    simp only [M, m₂, m₁]
    rcases Nat.le_total off L.length with ho' | ho'
    · rw [Nat.min_eq_left ho']
      rcases Nat.le_total len (L.drop off).length with hl' | hl'
      · rw [Nat.min_eq_left hl']
      · rw [Nat.min_eq_right hl', List.take_length, List.take_of_length_le hl']
    · rw [Nat.min_eq_right ho']; simp [List.drop_of_length_le ho']
  have e : (S₇.set src L).set A [] = ((((S.set offS lo).set lenS ll).set dst (S dst ++ (L.drop off).take len)).set
      ctr (lr ++ [v + ((L.drop off).take len).length])) := by
    rw [← hW]
    simp only [S₇, S₆, S₅, S₄, S₃, S₂, S₁, List.reverse_reverse, List.length_reverse]
    vra_ext [src, dst, ctr, offS, lenS, A, B, D, E] [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, (h1).symm, (h2).symm, (h3).symm, (h4).symm, (h5).symm, (h6).symm, (h7).symm, (h8).symm, (h9).symm, (h10).symm, (h11).symm, (h12).symm, (h13).symm, (h14).symm, (h15).symm, (h16).symm, (h17).symm, (h18).symm, (h19).symm, (h20).symm, (h21).symm, (h22).symm, (h23).symm, (h24).symm, (h25).symm, (h26).symm, (h27).symm, (h28).symm, (h29).symm, (h30).symm, (h31).symm, (h32).symm, (h33).symm, (h34).symm, (h35).symm, (h36).symm, hA, hB, hD, hE, hL]
  rw [e] at x₈
  refine (x₁.seq (x₂.seq (x₃.seq (x₄.seq (x₅.seq (x₆.seq (x₇.seq x₈))))))).mono ?_
  have hm : m₁ + m₂ ≤ L.length := by simp only [m₂, M, m₁, List.length_drop]; omega
  simp only [vra_sliceCost, List.length_reverse, List.length_take, List.length_append, List.length_drop]
  have : (L.drop m₁).length = L.length - m₁ := List.length_drop
  have h₁ : min m₁ L.length = m₁ := Nat.min_eq_left (Nat.min_le_right _ _)
  have h₂ : min m₂ M.length = m₂ := Nat.min_eq_left (Nat.min_le_right _ _)
  simp only [M] at h₂
  omega


/-- Induction from the top of a stack. -/
theorem vra_rev_ind {α : Type} {P : List α → Prop} (h0 : P []) (hs : ∀ l y, P l → P (l ++ [y])) :
    ∀ l, P l := by
  intro l
  rw [← List.reverse_reverse l]
  induction l.reverse with
  | nil => exact h0
  | cons y r ih => rw [List.reverse_cons]; exact hs _ y ih

/-! ## Repeating -/

/-- Run `body` `n` times, `n` the popped top of `c` (counted down on `c` meanwhile). -/
def vra_repeatP (c : Fin K) (body : NProg K) : NProg K :=
  .seq (.loop c .pos (.seq (.prim (.dec c)) body)) (.prim (.pop c))

/-- **Repeating through a family of states**: round `m` takes `G m` to `G (m + 1)`, with the count `n - m - 1` on
`c`. -/
theorem vra_repeat (c : Fin K) (body : NProg K) (G : Nat → Lists K) (n T : Nat) (lc : List Nat)
    (hbody : ∀ m, m < n → NRuns body ((G m).set c (lc ++ [n - m - 1])) ((G (m + 1)).set c (lc ++ [n - m - 1])) T) :
    NRuns (vra_repeatP c body) ((G 0).set c (lc ++ [n])) ((G n).set c lc) (n * (T + 2) + 2) := by
  let F : Nat → Lists K := fun m => (G m).set c (lc ++ [n - m])
  have hl := nruns_family_const (i := c) (c := .pos) (p := .seq (.prim (.dec c)) body) F n (T + 1)
    (fun m hm => by simp only [F, Lists.set_same]; rw [show n - m = (n - m - 1) + 1 by omega]; simp)
    (by simp [F])
    (fun m hm => by
      have x₁ := nruns_dec c (F m) (l := lc) (v := n - m) (by simp [F])
      have e₁ : (F m).set c (lc ++ [n - m - 1]) = (G m).set c (lc ++ [n - m - 1]) := by
        simp only [F, Lists.set_set_u]
      rw [e₁] at x₁
      have e₂ : (G (m + 1)).set c (lc ++ [n - m - 1]) = F (m + 1) := by
        simp only [F, show n - (m + 1) = n - m - 1 by omega]
      have x₂ := hbody m hm
      rw [e₂] at x₂
      exact (x₁.seq x₂).mono (by omega))
  have x₃ := nruns_pop c (F n) (l := lc) (v := 0) (by simp [F])
  have e₀ : F 0 = (G 0).set c (lc ++ [n]) := by simp [F]
  have e₃ : (F n).set c lc = (G n).set c lc := by simp only [F, Lists.set_set_u]
  rw [e₀] at hl
  rw [e₃] at x₃
  refine (hl.seq x₃).mono ?_
  rw [Nat.mul_succ]; omega

/-! ## Adding up a stack -/

/-- Add all of `X` (emptied) to the top of `o`. -/
def vra_sumP (X o : Fin K) : NProg K := .loop X .nonempty (addTo X o)

theorem vra_sum {X o : Fin K} (hXo : X ≠ o) :
    ∀ (l : List Nat) (S : Lists K) {lo : List Nat} {v : Nat}, S X = l → S o = lo ++ [v] →
      NRuns (vra_sumP X o) S ((S.set X []).set o (lo ++ [v + l.sum])) (3 * l.sum + 3 * l.length + 1) := by
  refine vra_rev_ind ?_ ?_
  · intro S lo v hX ho
    have e : (S.set X []).set o (lo ++ [v + ([] : List Nat).sum]) = S := by
      vra_ext [X, o] [hXo, hXo.symm, hX, ho]
    rw [e]
    exact (nruns_loop_exit (by rw [hX]; rfl)).mono (by omega)
  · intro l y ih S lo v hX ho
    have x₁ := nruns_addTo X o hXo S (l := l) (a := y) (l' := lo) (b := v) hX ho
    have x₂ := ih ((S.set X l).set o (lo ++ [v + y])) (lo := lo) (v := v + y)
      (by simp [Lists.set, hXo]) (by simp)
    have e : ((((S.set X l).set o (lo ++ [v + y])).set X []).set o (lo ++ [v + y + l.sum])) =
        (S.set X []).set o (lo ++ [v + (l ++ [y]).sum]) := by
      have : v + y + l.sum = v + (l ++ [y]).sum := by simp; omega
      rw [this]
      vra_ext [X, o] [hXo, hXo.symm]
    rw [e] at x₂
    refine (vra_loop_step (by rw [hX]; simp) x₁ x₂).mono ?_
    simp; omega

/-! ## Multiplying -/

/-- Multiply the top of `R` by the popped top of `Cn` (scratch tops `U W`). -/
def vra_mulP (R Cn U W : Fin K) (hRU : R ≠ U) (hUW : U ≠ W) : NProg K :=
  .seq (nmv R U hRU) (.seq (.prim (.pushZ R)) (.seq (vra_repeatP Cn (.seq (.prim (.dup U W hUW)) (addTo W R)))
    (.prim (.pop U))))

/-- The stacks of `vra_mulP` are all different. -/
structure VraM (R Cn U W : Fin K) : Prop where
  RC : R ≠ Cn
  RU : R ≠ U
  RW : R ≠ W
  CU : Cn ≠ U
  CW : Cn ≠ W
  UW : U ≠ W

theorem vra_mul {R Cn U W : Fin K} (hd : VraM R Cn U W) (S : Lists K) {lR lC : List Nat} {r c : Nat}
    (hR : S R = lR ++ [r]) (hC : S Cn = lC ++ [c]) :
    NRuns (vra_mulP R Cn U W hd.RU hd.UW) S ((S.set R (lR ++ [r * c])).set Cn lC) (c * (3 * r + 6) + 6) := by
  have h1 := hd.RC; have h2 := hd.RU; have h3 := hd.RW; have h4 := hd.CU; have h5 := hd.CW; have h6 := hd.UW
  have x₁ := nruns_mv R U h2 S hR
  let S₁ := (S.set U (S U ++ [r])).set R lR
  have x₂ := nruns_pushZ R S₁
  let G : Nat → Lists K := fun m => (((S.set U (S U ++ [r])).set R (lR ++ [r * m])))
  have hbody : ∀ m, m < c → NRuns (.seq (.prim (.dup U W h6)) (addTo W R)) ((G m).set Cn (lC ++ [c - m - 1]))
      ((G (m + 1)).set Cn (lC ++ [c - m - 1])) (3 * r + 3) := by
    intro m _
    let Gm := (G m).set Cn (lC ++ [c - m - 1])
    have y₁ := nruns_dup U W h6 Gm (l := S U) (v := r) (by simp [Gm, G, Lists.set, h4.symm, h2.symm])
    have y₂ := nruns_addTo W R (Ne.symm h3) (Gm.set W (Gm W ++ [r])) (l := Gm W) (a := r) (l' := lR) (b := r * m)
      (by simp) (by simp [Gm, G, Lists.set, h3, h1])
    have e : ((Gm.set W (Gm W ++ [r])).set W (Gm W)).set R (lR ++ [r * m + r]) =
        (G (m + 1)).set Cn (lC ++ [c - m - 1]) := by
      simp only [Gm, G, Nat.mul_succ]
      vra_ext [R, Cn, U, W] [h1, h2, h3, h4, h5, h6, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm]
    rw [e] at y₂
    exact (y₁.seq y₂).mono (by omega)
  have x₃ := vra_repeat Cn _ G c (3 * r + 3) lC hbody
  have e₀ : S₁.set R (S₁ R ++ [0]) = (G 0).set Cn (lC ++ [c]) := by
    simp only [S₁, G, Nat.mul_zero]
    vra_ext [R, Cn, U, W] [h1, h2, h3, h4, h5, h6, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, hC]
  rw [e₀] at x₂
  have x₄ := nruns_pop U ((G c).set Cn lC) (l := S U) (v := r) (by simp [G, Lists.set, h4.symm, h2.symm])
  have e₁ : ((G c).set Cn lC).set U (S U) = (S.set R (lR ++ [r * c])).set Cn lC := by
    simp only [G]
    vra_ext [R, Cn, U, W] [h1, h2, h3, h4, h5, h6, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm]
  rw [e₁] at x₄
  refine (x₁.seq (x₂.seq (x₃.seq x₄))).mono ?_
  rw [show 3 * r + 3 + 2 = 3 * r + 5 by omega]
  have : c * (3 * r + 5) ≤ c * (3 * r + 6) := Nat.mul_le_mul_left _ (by omega)
  omega

/-! ## Comparing two stacks -/

/-- Set the top of `G` to `0`. -/
def vra_zeroG (G : Fin K) : NProg K := .seq (.prim (.pop G)) (.prim (.pushZ G))

theorem vra_zero (G : Fin K) (S : Lists K) {lG : List Nat} {b : Nat} (h : S G = lG ++ [b]) :
    NRuns (vra_zeroG G) S (S.set G (lG ++ [0])) 2 := by
  have x₁ := nruns_pop G S h
  have x₂ := nruns_pushZ G (S.set G lG)
  simp only [Lists.set_same, Lists.set_set_u] at x₂
  exact x₁.seq x₂

/-- The stacks of `vra_eqP` are all different. -/
structure VraE (P Q G t u g f : Fin K) : Prop where
  nd : [P, Q, G, t, u, g, f].Nodup

theorem VraE.ne {P Q G t u g f : Fin K} (h : VraE P Q G t u g f) :
    P ≠ Q ∧ P ≠ G ∧ P ≠ t ∧ P ≠ u ∧ P ≠ g ∧ P ≠ f ∧ Q ≠ G ∧ Q ≠ t ∧ Q ≠ u ∧ Q ≠ g ∧ Q ≠ f ∧
    G ≠ t ∧ G ≠ u ∧ G ≠ g ∧ G ≠ f ∧ t ≠ u ∧ t ≠ g ∧ t ≠ f ∧ u ≠ g ∧ u ≠ f ∧ g ≠ f := by
  have := h.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at this
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, ⟨h7, h8, h9, h10, h11⟩, ⟨h12, h13, h14, h15⟩, ⟨h16, h17, h18⟩, ⟨h19, h20⟩,
    h21, -⟩ := this
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩

/-- One round of the comparison: compare and pop the tops of `P` and `Q` (lowering the flag on a difference), or
clear `P` and lower the flag when `Q` is empty. -/
def vra_eqBody (P Q G t u g f : Fin K) (h : VraE P Q G t u g f) : NProg K :=
  .ite Q .nonempty
    (.seq (cmpTop P Q t u g f h.ne.2.2.1 h.ne.2.2.2.2.2.2.2.2.1)
      (.seq (caseTop f [vra_zeroG G, nskip t, vra_zeroG G] (nskip t)) (.seq (.prim (.pop P)) (.prim (.pop Q)))))
    (.seq (vra_zeroG G) (nclr P))

/-- Push `1` on `G` if the stacks `P` and `Q` hold the same list, `0` otherwise; both are emptied. -/
def vra_eqP (P Q G t u g f : Fin K) (h : VraE P Q G t u g f) : NProg K :=
  .seq (npushC G 1) (.seq (.loop P .nonempty (vra_eqBody P Q G t u g f h))
    (.ite Q .nonempty (.seq (vra_zeroG G) (nclr Q)) (nskip t)))

/-- The comparison from the tops: what is left of `Q`, and the flag. -/
def vra_eqR : List Nat → List Nat → Nat → List Nat × Nat
  | [], rq, b => (rq, b)
  | _ :: _, [], _ => ([], 0)
  | x :: rp, y :: rq, b => vra_eqR rp rq (if x = y then b else 0)

theorem vra_eqR_final : ∀ (rp rq : List Nat) (b : Nat),
    (if (vra_eqR rp rq b).1 = [] then (vra_eqR rp rq b).2 else 0) = if rp = rq then b else 0
  | [], [], _ => rfl
  | [], _ :: _, _ => by simp [vra_eqR]
  | _ :: _, [], _ => by simp [vra_eqR]
  | x :: rp, y :: rq, b => by
    rw [vra_eqR, vra_eqR_final rp rq]
    by_cases hx : x = y
    · subst hx; simp
    · simp [hx]

/-- The cost of a round of the comparison, on numbers at most `M`. -/
def vra_eqRound (M : Nat) : Nat := (2 * M + 1) * (2 * M + 6) + 32

theorem vra_eqLoop {P Q G t u g f : Fin K} (h : VraE P Q G t u g f) (M : Nat) :
    ∀ (rp rq : List Nat) (S : Lists K) {lG : List Nat} {b : Nat}, S P = rp.reverse → S Q = rq.reverse →
      S G = lG ++ [b] → (∀ x ∈ rp, x ≤ M) → (∀ y ∈ rq, y ≤ M) →
      NRuns (.loop P .nonempty (vra_eqBody P Q G t u g f h)) S
        (((S.set P []).set Q (vra_eqR rp rq b).1.reverse).set G (lG ++ [(vra_eqR rp rq b).2]))
        ((rp.length + 1) * (vra_eqRound M + 2 * rp.length + 8)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩ := h.ne
  intro rp
  induction rp with
  | nil =>
    intro rq S lG b hP hQ hG _ _
    have e : ((S.set P []).set Q (vra_eqR [] rq b).1.reverse).set G (lG ++ [(vra_eqR [] rq b).2]) = S := by
      simp only [vra_eqR]
      simp only [List.reverse_nil] at hP
      vra_ext [P, Q, G] [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, (h1).symm, (h2).symm, (h3).symm, (h4).symm, (h5).symm, (h6).symm, (h7).symm, (h8).symm, (h9).symm, (h10).symm, (h11).symm, (h12).symm, (h13).symm, (h14).symm, (h15).symm, (h16).symm, (h17).symm, (h18).symm, (h19).symm, (h20).symm, (h21).symm, hP, hQ, hG]
    rw [e]
    exact (nruns_loop_exit (by rw [hP]; rfl)).mono (by simp)
  | cons x rp ih =>
    intro rq S lG b hP hQ hG hMp hMq
    rcases rq with _ | ⟨y, rq⟩
    · -- `Q` is empty: lower the flag, clear `P`
      have x₁ := vra_zero G S hG
      have x₂ := nruns_clr P (S.set G (lG ++ [0]))
      have x₃ := nruns_loop_exit (i := P) (c := .nonempty) (p := vra_eqBody P Q G t u g f h)
        (S := (S.set G (lG ++ [0])).set P []) (by simp)
      have xb := (x₁.seq x₂).iteF (i := Q) (c := .nonempty) (p := .seq (cmpTop P Q t u g f h.ne.2.2.1
        h.ne.2.2.2.2.2.2.2.2.1) (.seq (caseTop f [vra_zeroG G, nskip t, vra_zeroG G] (nskip t))
          (.seq (.prim (.pop P)) (.prim (.pop Q))))) (by rw [hQ]; rfl)
      have := vra_loop_step (by rw [hP]; simp) xb x₃
      have e : (S.set G (lG ++ [0])).set P [] = ((S.set P []).set Q (vra_eqR (x :: rp) [] b).1.reverse).set G
          (lG ++ [(vra_eqR (x :: rp) [] b).2]) := by
        simp only [vra_eqR]
        simp only [List.reverse_nil] at hQ
        vra_ext [P, Q, G] [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, (h1).symm, (h2).symm, (h3).symm, (h4).symm, (h5).symm, (h6).symm, (h7).symm, (h8).symm, (h9).symm, (h10).symm, (h11).symm, (h12).symm, (h13).symm, (h14).symm, (h15).symm, (h16).symm, (h17).symm, (h18).symm, (h19).symm, (h20).symm, (h21).symm, hQ]
      rw [e] at this
      refine this.mono ?_
      have hl : ((S.set G (lG ++ [0])) P).length = rp.length + 1 := by
        rw [Lists.set_ne _ _ h2, hP]; simp
      rw [hl]
      have : 1 * (vra_eqRound M + 2 * (rp.length + 1) + 8) ≤ (rp.length + 1 + 1) *
          (vra_eqRound M + 2 * (rp.length + 1) + 8) := Nat.mul_le_mul_right _ (by omega)
      simp only [List.length_cons]; omega
    · -- compare the tops
      have hPx : S P = rp.reverse ++ [x] := by rw [hP]; simp
      have hQy : S Q = rq.reverse ++ [y] := by rw [hQ]; simp
      have hx : x ≤ M := hMp x (by simp)
      have hy : y ≤ M := hMq y (by simp)
      have x₁ := nruns_cmpTop P Q t u g f h3 h9 (by
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
        exact ⟨⟨h1, h3, h4, h5, h6⟩, ⟨h8, h9, h10, h11⟩, ⟨h16, h17, h18⟩, ⟨h19, h20⟩, ⟨h21, not_false⟩⟩) S hPx hQy
      let S₁ := S.set f (S f ++ [cmpRes x y])
      let b' := if x = y then b else 0
      have x₂ : NRuns (caseTop f [vra_zeroG G, nskip t, vra_zeroG G] (nskip t)) S₁ (S.set G (lG ++ [b'])) 8 := by
        have hfx : S₁ f = S f ++ [cmpRes x y] := by simp [S₁]
        have hS₁f : S₁.set f (S f) = S := by simp only [S₁, Lists.set_set_u, Lists.set_get_self]
        by_cases hxy : x = y
        · subst hxy
          have hc : cmpRes x x = 1 := by simp [cmpRes]
          rw [hc] at hfx
          have hb : b' = b := by simp [b']
          have e : S.set G (lG ++ [b']) = S := by rw [hb, ← hG, Lists.set_get_self]
          rw [e]
          have := caseTop_runs f [vra_zeroG G, nskip t, vra_zeroG G] (nskip t) 1 (by simp) S₁ (S f) hfx S 2
            (by rw [hS₁f]; exact nruns_skip t S)
          exact this.mono (by omega)
        · have hb : b' = 0 := by simp [b', hxy]
          rw [hb]
          have hc : cmpRes x y = 0 ∨ cmpRes x y = 2 := by
            unfold cmpRes; split
            · left; rfl
            · right; simp [hxy]
          rcases hc with hc | hc
          · rw [hc] at hfx
            have := caseTop_runs f [vra_zeroG G, nskip t, vra_zeroG G] (nskip t) 0 (by simp) S₁ (S f) hfx
              (S.set G (lG ++ [0])) 2 (by rw [hS₁f]; exact vra_zero G S hG)
            exact this.mono (by omega)
          · rw [hc] at hfx
            have := caseTop_runs f [vra_zeroG G, nskip t, vra_zeroG G] (nskip t) 2 (by simp) S₁ (S f) hfx
              (S.set G (lG ++ [0])) 2 (by rw [hS₁f]; exact vra_zero G S hG)
            exact this.mono (by omega)
      let S₂ := S.set G (lG ++ [b'])
      have x₃ := nruns_pop P S₂ (l := rp.reverse) (v := x) (by simp [S₂, Lists.set, h2, hPx])
      have x₄ := nruns_pop Q (S₂.set P rp.reverse) (l := rq.reverse) (v := y)
        (by simp [S₂, Lists.set, h7, h1.symm, hQy])
      let S₃ := (S₂.set P rp.reverse).set Q rq.reverse
      have x₅ := ih rq S₃ (lG := lG) (b := b') (by simp [S₃, Lists.set, h1]) (by simp [S₃])
        (by simp [S₃, S₂, Lists.set, h2.symm, h7.symm]) (fun z hz => hMp z (by simp [hz]))
        (fun z hz => hMq z (by simp [hz]))
      have e : ((S₃.set P []).set Q (vra_eqR rp rq b').1.reverse).set G (lG ++ [(vra_eqR rp rq b').2]) =
          ((S.set P []).set Q (vra_eqR (x :: rp) (y :: rq) b).1.reverse).set G
            (lG ++ [(vra_eqR (x :: rp) (y :: rq) b).2]) := by
        simp only [vra_eqR, S₃, S₂, b']
        vra_ext [P, Q, G] [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, (h1).symm, (h2).symm, (h3).symm, (h4).symm, (h5).symm, (h6).symm, (h7).symm, (h8).symm, (h9).symm, (h10).symm, (h11).symm, (h12).symm, (h13).symm, (h14).symm, (h15).symm, (h16).symm, (h17).symm, (h18).symm, (h19).symm, (h20).symm, (h21).symm]
      rw [e] at x₅
      have xb := (x₁.seq (x₂.seq (x₃.seq x₄))).iteT (i := Q) (c := .nonempty)
        (q := .seq (vra_zeroG G) (nclr P)) (by rw [hQy]; simp)
      refine (vra_loop_step (by rw [hPx]; simp) xb x₅).mono ?_
      have hc : (x + y + 1) * (2 * x + 6) + 20 ≤ vra_eqRound M - 12 := by
        have := Nat.mul_le_mul (show x + y + 1 ≤ 2 * M + 1 by omega) (show 2 * x + 6 ≤ 2 * M + 6 by omega)
        unfold vra_eqRound; omega
      have hR : 12 ≤ vra_eqRound M := by unfold vra_eqRound; omega
      have := Nat.mul_le_mul (show rp.length + 1 ≤ rp.length + 1 by omega)
        (show vra_eqRound M + 2 * rp.length + 8 ≤ vra_eqRound M + 2 * (rp.length + 1) + 8 by omega)
      have hsplit : ((x :: rp).length + 1) * (vra_eqRound M + 2 * (x :: rp).length + 8) =
          (rp.length + 1) * (vra_eqRound M + 2 * (rp.length + 1) + 8) +
            (vra_eqRound M + 2 * (rp.length + 1) + 8) := by
        simp only [List.length_cons]; rw [Nat.succ_mul]
      rw [hsplit]
      omega

theorem vra_eqR_length : ∀ (rp rq : List Nat) (b : Nat), (vra_eqR rp rq b).1.length ≤ rq.length
  | [], _, _ => Nat.le_refl _
  | _ :: _, [], _ => Nat.le_refl _
  | _ :: rp, _ :: rq, _ => by rw [vra_eqR]; exact Nat.le_trans (vra_eqR_length rp rq _) (by simp)

/-- The cost of comparing stacks of lengths `p` and `q`, holding numbers at most `M`. -/
def vra_eqCost (M p q : Nat) : Nat := (p + 1) * (vra_eqRound M + 2 * p + 8) + 2 * q + 10

theorem vra_eq {P Q G t u g f : Fin K} (h : VraE P Q G t u g f) (M : Nat) (S : Lists K) {lG : List Nat}
    (hG : S G = lG) (hMp : ∀ x ∈ S P, x ≤ M) (hMq : ∀ y ∈ S Q, y ≤ M) :
    NRuns (vra_eqP P Q G t u g f h) S (((S.set P []).set Q []).set G (lG ++ [if S P = S Q then 1 else 0]))
      (vra_eqCost M (S P).length (S Q).length) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩ := h.ne
  obtain ⟨lp, hP⟩ : ∃ l, S P = l := ⟨_, rfl⟩
  obtain ⟨lq, hQ⟩ : ∃ l, S Q = l := ⟨_, rfl⟩
  rw [hP, hQ]
  rw [hP] at hMp; rw [hQ] at hMq
  have x₁ := nruns_pushC G S 1
  rw [hG] at x₁
  let S₁ := S.set G (lG ++ [1])
  have x₂ := vra_eqLoop h M lp.reverse lq.reverse S₁ (lG := lG) (b := 1)
    (by simp [S₁, Lists.set, h2, hP]) (by simp [S₁, Lists.set, h7, hQ]) (by simp [S₁])
    (fun x hx => hMp x (by simpa using hx)) (fun y hy => hMq y (by simpa using hy))
  let R := vra_eqR lp.reverse lq.reverse 1
  have hfin := vra_eqR_final lp.reverse lq.reverse 1
  simp only [List.reverse_inj] at hfin
  let S₂ := ((S₁.set P []).set Q R.1.reverse).set G (lG ++ [R.2])
  have hRl := vra_eqR_length lp.reverse lq.reverse 1
  rw [List.length_reverse] at hRl
  have x₃ : NRuns (.ite Q .nonempty (.seq (vra_zeroG G) (nclr Q)) (nskip t)) S₂
      (((S.set P []).set Q []).set G (lG ++ [if lp = lq then 1 else 0])) (2 * lq.length + 4) := by
    by_cases hR : R.1 = []
    · have e : ((S.set P []).set Q []).set G (lG ++ [if lp = lq then 1 else 0]) = S₂ := by
        rw [← hfin]
        simp only [S₂, S₁, R] at hR ⊢
        simp only [hR, if_true, List.reverse_nil]
        vra_ext [P, Q, G] [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, (h1).symm, (h2).symm, (h3).symm, (h4).symm, (h5).symm, (h6).symm, (h7).symm, (h8).symm, (h9).symm, (h10).symm, (h11).symm, (h12).symm, (h13).symm, (h14).symm, (h15).symm, (h16).symm, (h17).symm, (h18).symm, (h19).symm, (h20).symm, (h21).symm]
      rw [e]
      exact ((nruns_skip t S₂).iteF (by simp [S₂, R] at hR ⊢; simp [Lists.set, h7, hR])).mono (by omega)
    · have y₁ := vra_zero G S₂ (lG := lG) (b := R.2) (by simp [S₂])
      have y₂ := nruns_clr Q (S₂.set G (lG ++ [0]))
      have hQ2 : (S₂.set G (lG ++ [0])) Q = R.1.reverse := by simp [S₂, Lists.set, h7]
      rw [hQ2, List.length_reverse] at y₂
      have e : ((S₂.set G (lG ++ [0])).set Q []) = ((S.set P []).set Q []).set G
          (lG ++ [if lp = lq then 1 else 0]) := by
        rw [← hfin]
        simp only [S₂, S₁, R] at hR ⊢
        simp only [hR, if_false]
        vra_ext [P, Q, G] [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, (h1).symm, (h2).symm, (h3).symm, (h4).symm, (h5).symm, (h6).symm, (h7).symm, (h8).symm, (h9).symm, (h10).symm, (h11).symm, (h12).symm, (h13).symm, (h14).symm, (h15).symm, (h16).symm, (h17).symm, (h18).symm, (h19).symm, (h20).symm, (h21).symm]
      rw [e] at y₂
      refine ((y₁.seq y₂).iteT (by rw [show S₂ Q = R.1.reverse by simp [S₂, Lists.set, h7]]; simp [NTest.eval, hR])).mono ?_
      simp only [R] at hRl ⊢; omega
  refine (x₁.seq (x₂.seq x₃)).mono ?_
  simp only [vra_eqCost, List.length_reverse]; omega

end Generic

end Shallot.MacroPeg.Mach

namespace Shallot.MacroPeg.Mach

open Complexity

set_option linter.unusedSimpArgs false

/-! ## The stacks of the item programs -/

/-- Programs in sequence. -/
local infixr:30 " ;; " => NProg.seq

abbrev vra_A : Fin NK := 18
abbrev vra_B : Fin NK := 19
abbrev vra_D : Fin NK := 20
abbrev vra_E : Fin NK := 21
abbrev vra_T : Fin NK := 22
abbrev vra_X : Fin NK := 23
abbrev vra_Y : Fin NK := 24
abbrev vra_K1 : Fin NK := 25
abbrev vra_NN : Fin NK := 26
abbrev vra_NA : Fin NK := 27
abbrev vra_OF : Fin NK := 28
abbrev vra_LN : Fin NK := 29
abbrev vra_O1 : Fin NK := 30
abbrev vra_L1 : Fin NK := 31
abbrev vra_P : Fin NK := 32
abbrev vra_Q : Fin NK := 33

attribute [local simp] vra_A vra_B vra_D vra_E vra_T vra_X vra_Y vra_K1 vra_NN vra_NA vra_OF vra_LN vra_O1 vra_L1
  vra_P vra_Q IT RVL RVL2 ROFF NX ENVT EV EVL RV RV2 ORD SZ CNT VALT ROWS CAP TK CTL TY OUT CUR TTs CTs LTs RTs BOD NB
  STA XS NTT NCT NLT NRT

/-! ## Facts on lists -/

theorem vra_le_sum : ∀ {l : List Nat} {x : Nat}, x ∈ l → x ≤ l.sum
  | [], _, h => absurd h (by simp)
  | y :: l, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := vra_le_sum h; simp; omega

/-- A rule value as a slice of all of them. -/
theorem vra_getD_slice : ∀ (Tf : List (List Nat)) (a : Nat),
    Tf.getD a [] = (Tf.flatten.drop ((Tf.map List.length).take a).sum).take
      (((Tf.map List.length).drop a).take 1).sum
  | [], a => by simp
  | v :: Tf, 0 => by simp
  | v :: Tf, a + 1 => by
    rw [List.getD_cons_succ, vra_getD_slice Tf a]
    simp only [List.flatten_cons, List.map_cons, List.take_succ_cons, List.sum_cons, List.drop_succ_cons]
    rw [List.drop_append]
    have hv : ∀ s, v.drop (v.length + s) = [] := fun s => List.drop_eq_nil_of_le (by omega)
    simp [hv]



/-! ## Reading the item and the tables -/

/-- Push entry `ctx` (the item's context) of the table `tbl` on `o`. -/
def vra_readCtxP (tbl o : Fin NK) (h1 : tbl ≠ vra_T) (h2 : vra_T ≠ o) : NProg NK :=
  .prim (.dup IT vra_K1 (by decide)) ;; peekAt tbl vra_T vra_K1 o h1 h2

/-- Push field `f` of the item on `o`. -/
def vra_readITP (f : Nat) (o : Fin NK) (h2 : vra_T ≠ o) : NProg NK :=
  npushC vra_K1 f ;; peekAt IT vra_T vra_K1 o (by decide) h2

theorem vra_readCtx {tbl o : Fin NK} (h : [tbl, vra_T, vra_K1, o].Nodup) (h1 : tbl ≠ vra_T) (h5 : vra_T ≠ o)
    (S : Lists NK) {it : MItem} (hIT : S IT = encItem it) (hT : S vra_T = []) (hk : it.ctx < (S tbl).length) :
    NRuns (vra_readCtxP tbl o h1 h5) S (S.set o (S o ++ [(S tbl)[it.ctx]])) (6 * (S tbl).length + 4 * it.ctx + 7) := by
  have hn := h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hn
  obtain ⟨⟨-, h2, h3⟩, ⟨h4, -⟩, h6, -⟩ := hn
  have x₁ := nruns_dup IT vra_K1 (by decide) S (l := [it.tag, it.a, it.b]) (v := it.ctx) (by rw [hIT]; rfl)
  let S₁ := S.set vra_K1 (S vra_K1 ++ [it.ctx])
  have x₂ := nruns_peekAt tbl vra_T vra_K1 o h1 h5 h S₁
    (by simp [S₁, Lists.set, hT, h4]) (lc := S vra_K1) (k := it.ctx) (by simp [S₁])
    (by simp [S₁, Lists.set, h2]; exact hk)
  have e₁ : S₁ tbl = S tbl := by simp [S₁, Lists.set, h2]
  have e₂ : (S₁.set vra_K1 (S vra_K1)).set o (S₁ o ++ [(S₁ tbl)[it.ctx]'(by rw [e₁]; exact hk)]) =
      S.set o (S o ++ [(S tbl)[it.ctx]]) := by
    have e₃ : S₁ o = S o := by simp [S₁, Lists.set, h6, Ne.symm h6]
    simp only [e₃, e₁]
    simp only [S₁, Lists.set_set_u, Lists.set_get_self]
  rw [e₂, e₁] at x₂
  exact (x₁.seq x₂).mono (by omega)

theorem vra_readIT {o : Fin NK} (h : [IT, vra_T, vra_K1, o].Nodup) (h5 : vra_T ≠ o) (S : Lists NK) {it : MItem}
    (hIT : S IT = encItem it) (hT : S vra_T = []) (f : Nat) (hf : f < 4) :
    NRuns (vra_readITP f o h5) S (S.set o (S o ++ [(encItem it)[f]'(by simp [encItem]; exact hf)])) (5 * f + 31) := by
  have hn := h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hn
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, -⟩, h6, -⟩ := hn
  have x₁ := nruns_pushC vra_K1 S f
  let S₁ := S.set vra_K1 (S vra_K1 ++ [f])
  have x₂ := nruns_peekAt IT vra_T vra_K1 o (by decide) h5 h S₁
    (by simp [S₁, Lists.set, hT, h4]) (lc := S vra_K1) (k := f) (by simp [S₁])
    (by simp [S₁, Lists.set, hIT, encItem]; exact hf)
  have e₁ : S₁ IT = encItem it := by simp [S₁, Lists.set, hIT, h2]
  have e₂ : (S₁.set vra_K1 (S vra_K1)).set o (S₁ o ++ [(S₁ IT)[f]'(by rw [e₁]; simp [encItem]; exact hf)]) =
      S.set o (S o ++ [(encItem it)[f]'(by simp [encItem]; exact hf)]) := by
    have e₃ : S₁ o = S o := by simp [S₁, Lists.set, h6, Ne.symm h6]
    simp only [e₃, e₁]
    simp only [S₁, Lists.set_set_u, Lists.set_get_self]
  rw [e₂, e₁] at x₂
  refine (x₁.seq x₂).mono ?_
  simp [encItem]; omega



/-! ## The rule item -/

/-- Sum up the slice of `RVL` with offset and length pushed by `pO` and `pL`, onto `V`. -/
def vra_sumSliceP (pO pL : NProg NK) (V : Fin NK) (_hV : vra_X ≠ V) : NProg NK :=
  pO ;; pL ;; .prim (.pushZ vra_Y) ;;
  vra_sliceP RVL vra_X vra_Y vra_O1 vra_L1 vra_A vra_B vra_D vra_E ⟨by decide⟩ ;;
  .prim (.pop vra_Y) ;; .prim (.pushZ V) ;; vra_sumP vra_X V

theorem vra_sumSlice (pO pL : NProg NK) (V : Fin NK) (_hV : vra_X ≠ V)
    (hVd : [V, vra_X, vra_Y, vra_O1, vra_L1, vra_A, vra_B, vra_D, vra_E, RVL].Nodup) (S : Lists NK) {o l T₁ T₂ : Nat}
    (hA : S vra_A = []) (hB : S vra_B = []) (hD : S vra_D = []) (hE : S vra_E = []) (hX : S vra_X = [])
    (hY : S vra_Y = []) (hO : S vra_O1 = []) (hL : S vra_L1 = []) (hVe : S V = [])
    (x₁ : NRuns pO S (S.set vra_O1 [o]) T₁) (x₂ : NRuns pL (S.set vra_O1 [o]) ((S.set vra_O1 [o]).set vra_L1 [l]) T₂) :
    NRuns (vra_sumSliceP pO pL V _hV) S (S.set V [(((S RVL).drop o).take l).sum])
      (T₁ + T₂ + vra_sliceCost (S RVL).length + 4 * ((((S RVL).drop o).take l).sum + l) + 6) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hVd
  obtain ⟨⟨v1, v2, v3, v4, v5, v6, v7, v8, v9⟩, -⟩ := hVd
  let W := ((S RVL).drop o).take l
  let S₂ := (S.set vra_O1 [o]).set vra_L1 [l]
  have x₃ := nruns_pushZ vra_Y S₂
  have hY2 : S₂ vra_Y = [] := by simp [S₂, Lists.set, hY]
  rw [hY2, List.nil_append] at x₃
  have x₄ := vra_slice (src := RVL) (dst := vra_X) (ctr := vra_Y) (offS := vra_O1) (lenS := vra_L1)
    (A := vra_A) (B := vra_B) (D := vra_D) (E := vra_E) ⟨by decide⟩ (S₂.set vra_Y [0]) (lo := []) (ll := [])
    (lr := []) (off := o) (len := l) (v := 0) (by simp [S₂, Lists.set, hA]) (by simp [S₂, Lists.set, hB])
    (by simp [S₂, Lists.set, hD]) (by simp [S₂, Lists.set, hE]) (by simp [S₂, Lists.set]) (by simp [S₂, Lists.set])
    (by simp [S₂, Lists.set])
  have hR : (S₂.set vra_Y [0]) RVL = S RVL := by simp [S₂, Lists.set]
  have hX2 : (S₂.set vra_Y [0]) vra_X = [] := by simp [S₂, Lists.set, hX]
  rw [hR, hX2, List.nil_append, Nat.zero_add] at x₄
  let S₄ := (((((S₂.set vra_Y [0]).set vra_O1 []).set vra_L1 []).set vra_X W).set vra_Y [W.length])
  have x₅ := nruns_pop vra_Y S₄ (l := []) (v := W.length) (by simp [S₄])
  have x₆ := nruns_pushZ V (S₄.set vra_Y [])
  have hV4 : (S₄.set vra_Y []) V = [] := by simp [S₄, S₂, Lists.set, hVe, v1, v2, v3, v4, Ne.symm v1, Ne.symm v2,
    Ne.symm v3, Ne.symm v4]
  rw [hV4, List.nil_append] at x₆
  have x₇ := vra_sum _hV W ((S₄.set vra_Y []).set V [0]) (lo := []) (v := 0)
    (by simp [S₄, Lists.set, _hV, Ne.symm _hV]) (by simp)
  have e : ((((S₄.set vra_Y []).set V [0]).set vra_X []).set V ([] ++ [0 + W.sum])) = S.set V [W.sum] := by
    simp only [S₄, S₂, List.nil_append, Nat.zero_add]
    vra_ext [V, vra_X, vra_Y, vra_O1, vra_L1] [v1, v2, v3, v4, Ne.symm v1, Ne.symm v2, Ne.symm v3, Ne.symm v4,
      hX, hY, hO, hL, hVe]
  rw [e] at x₇
  refine (x₁.seq (x₂.seq (x₃.seq (x₄.seq (x₅.seq (x₆.seq x₇)))))).mono ?_
  have hWl : W.length ≤ l := by simp only [W, List.length_take]; exact Nat.min_le_left _ _
  simp only [W] at hWl ⊢
  omega


/-- One copy of the rule value: the offset and the length from `OF` and `LN`, onto `EV`, counted on `EVL`. -/
def vra_ruleBody : NProg NK :=
  .prim (.dup vra_OF vra_O1 (by decide)) ;; .prim (.dup vra_LN vra_L1 (by decide)) ;;
  vra_sliceP RV EV EVL vra_O1 vra_L1 vra_A vra_B vra_D vra_E ⟨by decide⟩

/-- **The rule item**: `n` copies of the value of rule `a` (`n` the number of environments). -/
def itemRuleP : NProg NK :=
  vra_readCtxP ENVT vra_NN (by decide) (by decide) ;;
  vra_readITP 1 vra_NA (by decide) ;;
  vra_sumSliceP (.prim (.pushZ vra_O1)) (.prim (.dup vra_NA vra_L1 (by decide))) vra_OF (by decide) ;;
  vra_sumSliceP (.prim (.dup vra_NA vra_O1 (by decide))) (npushC vra_L1 1) vra_LN (by decide) ;;
  .prim (.pushZ EVL) ;;
  vra_repeatP vra_NN vra_ruleBody ;;
  .prim (.pop vra_OF) ;; .prim (.pop vra_LN) ;; .prim (.pop vra_NA)

theorem vra_take_sum_le : ∀ (l : List Nat) (a : Nat), (l.take a).sum ≤ l.sum
  | [], _ => by simp
  | _ :: _, 0 => by simp
  | x :: l, a + 1 => by simp only [List.take_succ_cons, List.sum_cons]; have := vra_take_sum_le l a; omega

theorem vra_drop_sum_le : ∀ (l : List Nat) (a : Nat), (l.drop a).sum ≤ l.sum
  | [], _ => by simp
  | _ :: _, 0 => by simp
  | x :: l, a + 1 => by simp only [List.drop_succ_cons, List.sum_cons]; have := vra_drop_sum_le l a; omega

/-- The scratch stacks of an environment. -/
theorem vra_scr {S : Lists NK} (h : ScratchEmpty S) (i : Fin NK) (h₁ : 18 ≤ i.val := by decide)
    (h₂ : i.val ≤ 33 := by decide) : S i = [] := h i h₁ h₂

theorem vra_envT_entry (j cap N : Nat) (tt ct : List (Nat × Nat)) (c : Nat) (hc : c ≤ ct.length) :
    (envTable j cap N tt ct)[c]'(by simp [envTable]; omega) = envT j cap N tt ct c := by
  simp [envTable]

theorem vra_envT_le_sum (j cap N : Nat) (tt ct : List (Nat × Nat)) (c : Nat) (hc : c ≤ ct.length) :
    envT j cap N tt ct c ≤ (envTable j cap N tt ct).sum :=
  vra_le_sum (List.mem_map.2 ⟨c, List.mem_range.2 (by omega), rfl⟩)

/-- The rule item, with its exact cost. -/
theorem vra_rule_runs (j cap : Nat) (st : PSt) (Tf : List (List Nat)) (it : MItem)
    (hcur : it.ctx ≤ st.ct.length) (S : Lists NK) (vs : List (List Nat)) (hE : EvalEnv S j cap st Tf)
    (hIT : S IT = encItem it) (hEV : S EV = evFlat vs) (hEVL : S EVL = evLens vs) :
    NRuns itemRuleP S
      ((S.set EV (evFlat vs ++ (List.replicate (envT j cap st.x.length st.tt st.ct it.ctx)
          (Tf.getD it.a [])).flatten)).set EVL
        (evLens vs ++ [envT j cap st.x.length st.tt st.ct it.ctx * (Tf.getD it.a []).length]))
      (6 * (st.ct.length + 1) + 4 * it.ctx + 7 + 36 +
        (2 + vra_sliceCost Tf.length + 4 * (Tf.flatten.length + it.a) + 6) +
        (3 + vra_sliceCost Tf.length + 4 * (Tf.flatten.length + 1) + 6) + 1 +
        (envT j cap st.x.length st.tt st.ct it.ctx * (2 + vra_sliceCost Tf.flatten.length + 2 + 2) + 2) + 3) := by
  have sc := hE.scratch
  have hA := vra_scr sc vra_A; have hB := vra_scr sc vra_B; have hD := vra_scr sc vra_D
  have hEm := vra_scr sc vra_E; have hT := vra_scr sc vra_T; have hX := vra_scr sc vra_X
  have hY := vra_scr sc vra_Y; have hK := vra_scr sc vra_K1; have hNN := vra_scr sc vra_NN
  have hNA := vra_scr sc vra_NA; have hOF := vra_scr sc vra_OF; have hLN := vra_scr sc vra_LN
  have hO1 := vra_scr sc vra_O1; have hL1 := vra_scr sc vra_L1
  have scr : S 18 = [] ∧ S 19 = [] ∧ S 20 = [] ∧ S 21 = [] ∧ S 22 = [] ∧ S 23 = [] ∧ S 24 = [] ∧ S 25 = [] ∧
      S 26 = [] ∧ S 27 = [] ∧ S 28 = [] ∧ S 29 = [] ∧ S 30 = [] ∧ S 31 = [] ∧ S 32 = [] ∧ S 33 = [] :=
    ⟨vra_scr sc 18, vra_scr sc 19, vra_scr sc 20, vra_scr sc 21, vra_scr sc 22, vra_scr sc 23, vra_scr sc 24,
      vra_scr sc 25, vra_scr sc 26, vra_scr sc 27, vra_scr sc 28, vra_scr sc 29, vra_scr sc 30, vra_scr sc 31,
      vra_scr sc 32, vra_scr sc 33⟩
  obtain ⟨n, hn⟩ : ∃ n, envT j cap st.x.length st.tt st.ct it.ctx = n := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, it.a = a := ⟨_, rfl⟩
  obtain ⟨lens, hlens⟩ : ∃ l, Tf.map List.length = l := ⟨_, rfl⟩
  obtain ⟨seg, hseg⟩ : ∃ l, Tf.getD a [] = l := ⟨_, rfl⟩
  rw [hn, ha, hseg]
  -- the number of environments
  have hkE : it.ctx < (S ENVT).length := by rw [hE.envt]; simp [envTable]; omega
  have x₁ := vra_readCtx (tbl := ENVT) (o := vra_NN) (by decide) (by decide) (by decide) S hIT hT hkE
  have hv₁ : (S ENVT)[it.ctx]'hkE = n := by simp only [hE.envt]; rw [← hn]; exact vra_envT_entry _ _ _ _ _ _ hcur
  rw [hv₁, hNN, List.nil_append] at x₁
  have hlE : (S ENVT).length = st.ct.length + 1 := by rw [hE.envt]; simp [envTable]
  rw [hlE] at x₁
  let S₁ := S.set vra_NN [n]
  -- the rule number
  have x₂ := vra_readIT (o := vra_NA) (by decide) (by decide) S₁ (it := it) (by simp [S₁, Lists.set, scr, hIT])
    (by simp [S₁, Lists.set, scr, hT]) 1 (by decide)
  have hv₂ : (encItem it)[1]'(by simp [encItem]) = a := by simp [encItem, ← ha]
  rw [hv₂] at x₂
  have hNA₁ : S₁ vra_NA = [] := by simp [S₁, Lists.set, scr, hNA]
  rw [hNA₁, List.nil_append] at x₂
  let S₂ := S₁.set vra_NA [a]
  -- the offset of rule `a`
  have x₃ := vra_sumSlice (.prim (.pushZ vra_O1)) (.prim (.dup vra_NA vra_L1 (by decide))) vra_OF (by decide)
    (by decide) S₂ (o := 0) (l := a) (by simp [S₂, S₁, Lists.set, scr, hA]) (by simp [S₂, S₁, Lists.set, scr, hB])
    (by simp [S₂, S₁, Lists.set, scr, hD]) (by simp [S₂, S₁, Lists.set, scr, hEm]) (by simp [S₂, S₁, Lists.set, scr, hX])
    (by simp [S₂, S₁, Lists.set, scr, hY]) (by simp [S₂, S₁, Lists.set, scr, hO1]) (by simp [S₂, S₁, Lists.set, scr, hL1])
    (by simp [S₂, S₁, Lists.set, scr, hOF])
    (by have := nruns_pushZ vra_O1 S₂; rwa [show S₂ vra_O1 = [] by simp [S₂, S₁, Lists.set, scr, hO1]] at this)
    (by
      have := nruns_dup vra_NA vra_L1 (by decide) (S₂.set vra_O1 [0]) (l := []) (v := a) (by simp [S₂, Lists.set])
      rwa [show (S₂.set vra_O1 [0]) vra_L1 = [] by simp [S₂, S₁, Lists.set, scr, hL1]] at this)
  have hRVL₂ : S₂ RVL = lens := by simp [S₂, S₁, Lists.set, scr, hE.rvl, ← hlens]
  rw [hRVL₂, List.drop_zero] at x₃
  obtain ⟨s, hs⟩ : ∃ s, (lens.take a).sum = s := ⟨_, rfl⟩
  rw [hs] at x₃
  let S₃ := S₂.set vra_OF [s]
  -- the length of rule `a`
  have x₄ := vra_sumSlice (.prim (.dup vra_NA vra_O1 (by decide))) (npushC vra_L1 1) vra_LN (by decide)
    (by decide) S₃ (o := a) (l := 1) (by simp [S₃, S₂, S₁, Lists.set, scr, hA]) (by simp [S₃, S₂, S₁, Lists.set, scr, hB])
    (by simp [S₃, S₂, S₁, Lists.set, scr, hD]) (by simp [S₃, S₂, S₁, Lists.set, scr, hEm])
    (by simp [S₃, S₂, S₁, Lists.set, scr, hX]) (by simp [S₃, S₂, S₁, Lists.set, scr, hY])
    (by simp [S₃, S₂, S₁, Lists.set, scr, hO1]) (by simp [S₃, S₂, S₁, Lists.set, scr, hL1])
    (by simp [S₃, S₂, S₁, Lists.set, scr, hLN])
    (by
      have := nruns_dup vra_NA vra_O1 (by decide) S₃ (l := []) (v := a) (by simp [S₃, S₂, Lists.set])
      rwa [show S₃ vra_O1 = [] by simp [S₃, S₂, S₁, Lists.set, scr, hO1]] at this)
    (by
      have := nruns_pushC vra_L1 (S₃.set vra_O1 [a]) 1
      rwa [show (S₃.set vra_O1 [a]) vra_L1 = [] by simp [S₃, S₂, S₁, Lists.set, scr, hL1]] at this)
  have hRVL₃ : S₃ RVL = lens := by simp [S₃, S₂, S₁, Lists.set, scr, hE.rvl, ← hlens]
  rw [hRVL₃] at x₄
  obtain ⟨ℓ, hℓ⟩ : ∃ s, ((lens.drop a).take 1).sum = s := ⟨_, rfl⟩
  rw [hℓ] at x₄
  let S₄ := S₃.set vra_LN [ℓ]
  -- the copies
  have x₅ := nruns_pushZ EVL S₄
  have hEVL₄ : S₄ EVL = S EVL := by simp [S₄, S₃, S₂, S₁, Lists.set]
  rw [hEVL₄] at x₅
  have hslice : (Tf.flatten.drop s).take ℓ = seg := by rw [← hseg, vra_getD_slice Tf a, hlens, hs, hℓ]
  let G : Nat → Lists NK := fun m => ((((S.set vra_NA [a]).set vra_OF [s]).set vra_LN [ℓ]).set EV
    (S EV ++ (List.replicate m seg).flatten)).set EVL (S EVL ++ [m * seg.length])
  have hbody : ∀ m, m < n → NRuns vra_ruleBody ((G m).set vra_NN ([] ++ [n - m - 1]))
      ((G (m + 1)).set vra_NN ([] ++ [n - m - 1])) (2 + vra_sliceCost Tf.flatten.length + 2) := by
    intro m _
    let Gm := (G m).set vra_NN ([] ++ [n - m - 1])
    have y₁ := nruns_dup vra_OF vra_O1 (by decide) Gm (l := []) (v := s) (by simp [Gm, G, Lists.set])
    have y₂ := nruns_dup vra_LN vra_L1 (by decide) (Gm.set vra_O1 (Gm vra_O1 ++ [s])) (l := []) (v := ℓ)
      (by simp [Gm, G, Lists.set])
    let Gm₂ := (Gm.set vra_O1 (Gm vra_O1 ++ [s])).set vra_L1 ((Gm.set vra_O1 (Gm vra_O1 ++ [s])) vra_L1 ++ [ℓ])
    have hO : Gm vra_O1 = [] := by simp [Gm, G, Lists.set, scr, hO1]
    have hL : Gm vra_L1 = [] := by simp [Gm, G, Lists.set, scr, hL1]
    have y₃ := vra_slice (src := RV) (dst := EV) (ctr := EVL) (offS := vra_O1) (lenS := vra_L1) (A := vra_A)
      (B := vra_B) (D := vra_D) (E := vra_E) ⟨by decide⟩ Gm₂ (lo := []) (ll := []) (lr := S EVL) (off := s)
      (len := ℓ) (v := m * seg.length) (by simp [Gm₂, Gm, G, Lists.set, scr, hA]) (by simp [Gm₂, Gm, G, Lists.set, scr, hB])
      (by simp [Gm₂, Gm, G, Lists.set, scr, hD]) (by simp [Gm₂, Gm, G, Lists.set, scr, hEm])
      (by simp [Gm₂, Gm, G, Lists.set, scr, hO]) (by simp [Gm₂, Gm, G, Lists.set, scr, hO, hL])
      (by simp [Gm₂, Gm, G, Lists.set])
    have hRV : Gm₂ RV = Tf.flatten := by simp [Gm₂, Gm, G, Lists.set, scr, hE.rv]
    rw [hRV, hslice] at y₃
    have e : ((((Gm₂.set vra_O1 []).set vra_L1 []).set EV (Gm₂ EV ++ seg)).set EVL
        (S EVL ++ [m * seg.length + seg.length])) = (G (m + 1)).set vra_NN ([] ++ [n - m - 1]) := by
      have hEV₂ : Gm₂ EV = S EV ++ (List.replicate m seg).flatten := by simp [Gm₂, Gm, G, Lists.set]
      rw [hEV₂]
      simp only [Gm₂, Gm, G, hO, hL, List.nil_append, List.append_assoc]
      have : (List.replicate (m + 1) seg).flatten = (List.replicate m seg).flatten ++ seg := by
        rw [List.replicate_succ', List.flatten_append]; simp
      rw [this, Nat.succ_mul]
      vra_ext [vra_O1, vra_L1, EV, EVL, vra_NN, vra_NA, vra_OF, vra_LN] [hO1, hL1]
    rw [e] at y₃
    exact (y₁.seq (y₂.seq y₃)).mono (by omega)
  have x₆ := vra_repeat vra_NN vra_ruleBody G n _ [] hbody
  have e₆ : (G 0).set vra_NN ([] ++ [n]) = S₄.set EVL (S EVL ++ [0]) := by
    simp only [G, S₄, S₃, S₂, S₁, List.replicate_zero, List.flatten_nil, List.append_nil, Nat.zero_mul,
      List.nil_append]
    vra_ext [vra_NN, vra_NA, vra_OF, vra_LN, EV, EVL] [hNN]
  rw [e₆] at x₆
  -- clean up
  have x₇ := nruns_pop vra_OF ((G n).set vra_NN []) (l := []) (v := s) (by simp [G, Lists.set])
  have x₈ := nruns_pop vra_LN (((G n).set vra_NN []).set vra_OF []) (l := []) (v := ℓ) (by simp [G, Lists.set])
  have x₉ := nruns_pop vra_NA ((((G n).set vra_NN []).set vra_OF []).set vra_LN []) (l := []) (v := a)
    (by simp [G, Lists.set])
  have e₉ : (((((G n).set vra_NN []).set vra_OF []).set vra_LN []).set vra_NA []) =
      ((S.set EV (evFlat vs ++ (List.replicate n seg).flatten)).set EVL (evLens vs ++ [n * seg.length])) := by
    simp only [G]
    rw [← hEV, ← hEVL]
    vra_ext [vra_NN, vra_NA, vra_OF, vra_LN, EV, EVL] [hNN, hNA, hOF, hLN]
  rw [e₉] at x₉
  refine (x₁.seq (x₂.seq (x₃.seq (x₄.seq (x₅.seq (x₆.seq (x₇.seq (x₈.seq x₉)))))))).mono ?_
  have hsl : s ≤ Tf.flatten.length := by
    rw [← hs, List.length_flatten, hlens]
    exact vra_take_sum_le _ _
  have hℓl : ℓ ≤ Tf.flatten.length := by
    rw [← hℓ, List.length_flatten, hlens]
    exact Nat.le_trans (vra_take_sum_le _ _) (vra_drop_sum_le _ _)
  have hll : lens.length = Tf.length := by rw [← hlens, List.length_map]
  rw [hll]
  omega

/-! ## Costs -/

theorem vra_pow_le {Z : Nat} (h : 1 ≤ Z) : Z * Z ≤ Z * Z * Z * Z * Z := by
  have h₁ : Z * Z * 1 ≤ Z * Z * Z := Nat.mul_le_mul_left _ h
  have h₂ : Z * Z * Z * 1 ≤ Z * Z * Z * Z := Nat.mul_le_mul_left _ h
  have h₃ : Z * Z * Z * Z * 1 ≤ Z * Z * Z * Z * Z := Nat.mul_le_mul_left _ h
  simp only [Nat.mul_one] at h₁ h₂ h₃
  omega

/-- A cost of at most `1000 Z²` is within `itemCost`. -/
theorem vra_le_itemCost {j cap : Nat} {st : PSt} {Tf : List (List Nat)} {it : MItem} {vs : List (List Nat)} {c : Nat}
    (h : c ≤ 1000 * (itemZ j cap st Tf it vs * itemZ j cap st Tf it vs)) : c ≤ itemCost j cap st Tf it vs := by
  have hz : 1 ≤ itemZ j cap st Tf it vs := by unfold itemZ; omega
  have := Nat.mul_le_mul_left 1000 (vra_pow_le hz)
  unfold itemCost; omega

theorem vra_flatten_replicate_length (n : Nat) (l : List Nat) : (List.replicate n l).flatten.length = n * l.length := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, List.length_append, ih, Nat.succ_mul]; omega

theorem vra_stepT_rule (j cap : Nat) (st : PSt) (Tf : List (List Nat)) (it : MItem) (htag : it.tag = 10)
    (vs : List (List Nat)) :
    stepT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt Tf it vs =
      (List.replicate (envT j cap st.x.length st.tt st.ct it.ctx) (Tf.getD it.a [])).flatten :: vs := by
  unfold stepT; rw [htag]; simp

theorem itemRuleP_runs (j cap : Nat) (st : PSt) (Tf : List (List Nat)) (it : MItem) (htag : it.tag = 10)
    (hcur : it.ctx ≤ st.ct.length) : ItemRuns itemRuleP j cap st Tf it := by
  intro S vs hE hIT hEV hEVL
  have x := vra_rule_runs j cap st Tf it hcur S vs hE hIT hEV hEVL
  have hst := vra_stepT_rule j cap st Tf it htag vs
  rw [hst, evFlat_cons, evLens_cons, vra_flatten_replicate_length]
  refine x.mono (vra_le_itemCost ?_)
  -- the sizes involved
  have hn := vra_envT_le_sum j cap st.x.length st.tt st.ct it.ctx hcur
  have hZ : st.ct.length + it.ctx + Tf.length + Tf.flatten.length + it.a +
      (envTable j cap st.x.length st.tt st.ct).sum + 2 ≤ itemZ j cap st Tf it vs := by
    unfold itemZ; omega
  generalize itemZ j cap st Tf it vs = Z at hZ ⊢
  generalize envT j cap st.x.length st.tt st.ct it.ctx = n at hn ⊢
  have hnZ : n ≤ Z := by omega
  have h₁ : n * (2 + vra_sliceCost Tf.flatten.length + 2 + 2) ≤ Z * (30 * Z + 26) := by
    unfold vra_sliceCost; exact Nat.mul_le_mul hnZ (by omega)
  have h₂ : Z * (30 * Z + 26) = 30 * (Z * Z) + 26 * Z := by rw [Nat.mul_add, Nat.mul_comm Z (30 * Z), Nat.mul_assoc]; omega
  have h₃ : 2 * Z ≤ Z * Z := Nat.mul_le_mul_right _ (by omega)
  unfold vra_sliceCost at h₁ ⊢
  omega

/-! ## The rows in the tables -/

theorem vra_flatten_len_const {V : Nat} : ∀ (rows : List (List Nat)), (∀ r ∈ rows, r.length = V) →
    rows.flatten.length = rows.length * V
  | [], _ => by simp
  | r :: rows, h => by
    rw [List.flatten_cons, List.length_append, h r List.mem_cons_self,
      vra_flatten_len_const rows (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))]
    simp [Nat.succ_mul]; omega

/-- Every row of type number `k` has the length of its values. -/
theorem vra_rowsNum_len (N : Nat) (tt : List (Nat × Nat)) :
    ∀ k, ∀ r ∈ rowsNum N tt k, r.length = valNum N tt k := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro r hr
    cases k with
    | zero =>
      rw [rowsNum] at hr
      rw [valNum]
      exact ((Shallot.MacroPeg.HO.mem_allVecs _ _ _).1 hr).1
    | succ k =>
      rw [rowsNum] at hr
      rw [valNum]
      rcases hk : tt[k]? with _ | ⟨a, b⟩
      · rw [hk] at hr; simp at hr
      · rw [hk] at hr
        simp only [] at hr ⊢
        split at hr
        · rename_i hab
          rw [if_pos hab]
          obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hr
          have hv' := ((Shallot.MacroPeg.HO.mem_allVecs _ _ _).1 (List.mem_filter.1 hv).1)
          rw [vra_flatten_len_const v (fun w hw => ih b (by omega) w (hv'.2 w hw)), hv'.1]
        · simp at hr

/-- The tabulated rows have the length of the tabulated values. -/
theorem vra_rowsT_len {j cap N : Nat} {tt : List (Nat × Nat)} {t : Nat} :
    ∀ r ∈ rowsT j cap N tt t, r.length = valT j cap N tt t := by
  intro r hr
  unfold rowsT at hr
  split at hr
  · rename_i hs
    rw [vra_rowsNum_len N tt t r hr, valT_eq t (small_need hs)]
  · simp at hr

/-- A segment of a flattened table. -/
theorem vra_flatten_range (g : Nat → List Nat) (n t : Nat) (ht : t < n) :
    ((List.range n).map g).flatten.drop (((List.range t).map g).flatten.length) =
      g t ++ (((List.range n).map g).flatten.drop (((List.range t).map g).flatten.length + (g t).length)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = t + (m + 1) := ⟨n - t - 1, by omega⟩
  rw [List.range_add, List.map_append, List.flatten_append, List.drop_left, List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, List.flatten_cons, Nat.add_zero, List.drop_append, List.length_append,
    List.length_flatten]
  simp

/-- Row `k` of a list of rows of length `V`, followed by anything. -/
theorem vra_row_slice {V : Nat} : ∀ (rows : List (List Nat)) (rest : List Nat) (k : Nat) (hk : k < rows.length),
    (∀ r ∈ rows, r.length = V) → (((rows.flatten ++ rest).drop (k * V)).take V) = rows[k]
  | [], _, _, hk, _ => absurd hk (by simp)
  | r :: rows, rest, 0, _, h => by
    have := h r List.mem_cons_self
    simp [← this]
  | r :: rows, rest, k + 1, hk, h => by
    have hr := h r List.mem_cons_self
    simp only [List.flatten_cons, List.append_assoc, Nat.succ_mul, List.getElem_cons_succ]
    rw [Nat.add_comm, ← List.drop_drop, List.drop_left' hr]
    exact vra_row_slice rows rest k (by simpa using hk) (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))

theorem vra_typeTable_get (tt : List (Nat × Nat)) (f : Nat → Nat) {t : Nat} (ht : t ≤ tt.length) :
    (typeTable tt f)[t]'(by simp [typeTable]; omega) = f t := by
  simp [typeTable]

/-- **Row `k` of type `t`** as a slice of the table of rows. -/
theorem vra_rowsFlat_slice (j cap N : Nat) (tt : List (Nat × Nat)) {t k : Nat} (ht : t ≤ tt.length)
    (hk : k < (rowsT j cap N tt t).length) :
    (((rowsFlat j cap N tt).drop ((roffTable j cap N tt)[t]'(by simp [roffTable, typeTable]; omega) +
      k * (valTable j cap N tt)[t]'(by simp [valTable, typeTable]; omega))).take
        ((valTable j cap N tt)[t]'(by simp [valTable, typeTable]; omega))) = (rowsT j cap N tt t)[k] := by
  have hv : (valTable j cap N tt)[t]'(by simp [valTable, typeTable]; omega) = valT j cap N tt t :=
    vra_typeTable_get tt _ ht
  have ho : (roffTable j cap N tt)[t]'(by simp [roffTable, typeTable]; omega) =
      (((List.range t).map (fun k' => (rowsT j cap N tt k').flatten)).flatten).length :=
    vra_typeTable_get tt _ ht
  rw [hv, ho, ← List.drop_drop]
  unfold rowsFlat
  rw [vra_flatten_range _ _ _ (by omega)]
  exact vra_row_slice _ _ k hk (fun r hr => vra_rowsT_len r hr)

/-! ## The variable numbers along the walk up the contexts -/

section VarMath

variable (j cap N : Nat) (tt ct : List (Nat × Nat))

/-- The number of rows of the binder type of context `c` (`1` at the empty context). -/
def vra_fac : Nat → Nat
  | 0 => 1
  | c + 1 => (rowsT j cap N tt ((ct[c]?.map Prod.snd).getD 0)).length

/-- The product of the factors of the first `m` contexts of the walk from `c`. -/
def vra_Rf : Nat → Nat → Nat
  | _, 0 => 1
  | c, m + 1 => vra_fac j cap N tt ct c * vra_Rf (upCtx ct c) m

/-- The base of the variable numbers at the end `w` of the walk. -/
def vra_base (w : Nat) : List Nat :=
  (List.replicate (envT j cap N tt ct (upCtx ct w)) (List.range (vra_fac j cap N tt ct w))).flatten

variable {j cap N tt ct}

theorem vra_Rf_succ' : ∀ (m c : Nat), vra_Rf j cap N tt ct c (m + 1) =
    vra_Rf j cap N tt ct c m * vra_fac j cap N tt ct (walkCtx ct c m)
  | 0, c => by simp [vra_Rf, walkCtx]
  | m + 1, c => by
    rw [vra_Rf, vra_Rf_succ' m (upCtx ct c), vra_Rf, walkCtx_succ', Nat.mul_assoc]

theorem vra_envT_up (hc : CTWF tt ct) : ∀ c, c ≤ ct.length →
    envT j cap N tt ct c = vra_fac j cap N tt ct c * envT j cap N tt ct (upCtx ct c)
  | 0, _ => by simp [vra_fac, upCtx, envT]
  | c + 1, h => by
    have hlt : c < ct.length := by omega
    have hpar := (hc c hlt).1
    rw [envT, List.getElem?_eq_getElem hlt]
    simp only [hpar, if_true, vra_fac, upCtx, List.getElem?_eq_getElem hlt, Option.map_some, Option.getD_some]
    rw [Nat.mul_comm]

theorem vra_envT_walk (hc : CTWF tt ct) : ∀ m c, c ≤ ct.length →
    envT j cap N tt ct c = vra_Rf j cap N tt ct c m * envT j cap N tt ct (walkCtx ct c m)
  | 0, c, _ => by simp [vra_Rf, walkCtx]
  | m + 1, c, h => by
    have hup : upCtx ct c ≤ ct.length := by
      have := walkCtx_le hc c h 1; simpa [walkCtx] using this
    rw [vra_envT_up hc c h, vra_envT_walk hc m (upCtx ct c) hup, vra_Rf, walkCtx_succ', Nat.mul_assoc]

theorem vra_flatMap_rep_one (l : List Nat) : l.flatMap (fun v => List.replicate 1 v) = l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, ih]

theorem vra_rep_flatMap (x a b : Nat) :
    (List.replicate a x).flatMap (fun v => List.replicate b v) = List.replicate (b * a) x := by
  induction a with
  | zero => simp
  | succ a iha =>
    rw [List.replicate_succ, List.flatMap_cons, iha, Nat.mul_succ, Nat.add_comm (b * a) b,
      ← List.replicate_append_replicate]

theorem vra_flatMap_rep_rep (l : List Nat) (a b : Nat) :
    (l.flatMap (fun v => List.replicate a v)).flatMap (fun v => List.replicate b v) =
      l.flatMap (fun v => List.replicate (b * a) v) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.flatMap_cons, List.flatMap_append, ih, vra_rep_flatMap]

/-- **The variable numbers in closed form.** -/
theorem vra_varVecT_eq (hc : CTWF tt ct) : ∀ i c, c ≤ ct.length →
    varVecT j cap N tt ct c i = if walkCtx ct c i = 0 then [] else
      (vra_base j cap N tt ct (walkCtx ct c i)).flatMap (fun v => List.replicate (vra_Rf j cap N tt ct c i) v)
  | 0, 0, _ => by simp [varVecT, walkCtx]
  | 0, c + 1, h => by
    have hlt : c < ct.length := by omega
    have hpar := (hc c hlt).1
    rw [varVecT, List.getElem?_eq_getElem hlt]
    simp only [hpar, if_true, walkCtx, Nat.add_one_ne_zero, if_false, vra_Rf, vra_flatMap_rep_one, vra_base,
      vra_fac, upCtx, List.getElem?_eq_getElem hlt, Option.map_some, Option.getD_some]
  | i + 1, 0, _ => by simp [varVecT, walkCtx_zero]
  | i + 1, c + 1, h => by
    have hlt : c < ct.length := by omega
    have hpar := (hc c hlt).1
    rw [varVecT, List.getElem?_eq_getElem hlt]
    simp only [hpar, if_true]
    rw [vra_varVecT_eq hc i ct[c].1 (by omega), walkCtx_succ']
    have hup : upCtx ct (c + 1) = ct[c].1 := by simp [upCtx, List.getElem?_eq_getElem hlt]
    rw [hup]
    split
    · simp
    · rw [vra_flatMap_rep_rep, vra_Rf, hup]
      simp only [vra_fac, List.getElem?_eq_getElem hlt, Option.map_some, Option.getD_some]

/-- Each number repeated `R` times, mapped to lists and flattened. -/
theorem vra_flatMap_rep_map (g : Nat → List Nat) (R : Nat) (l : List Nat) :
    ((l.flatMap (fun v => List.replicate R v)).map g).flatten =
      (l.map (fun k => (List.replicate R (g k)).flatten)).flatten := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.flatMap_cons, List.map_append, List.flatten_append, ih, List.map_replicate,
    List.map_cons, List.flatten_cons]

theorem vra_replicate_map_flatten (h : Nat → List Nat) (E : Nat) (X : List Nat) :
    ((List.replicate E X).flatten.map h).flatten = (List.replicate E (X.map h).flatten).flatten := by
  induction E with
  | zero => rfl
  | succ E ih => simp only [List.replicate_succ, List.flatten_cons, List.map_append, List.flatten_append, ih]

end VarMath

/-! ## The variable item: the copies of the rows -/

/-! Stacks of the variable item. Single numbers may sit on top of stacks the item does not read; they are popped
again. -/
abbrev vra_CC : Fin NK := 23
abbrev vra_II : Fin NK := 24
abbrev vra_RR : Fin NK := 27
abbrev vra_TT : Fin NK := 28
abbrev vra_PP : Fin NK := 29
abbrev vra_CN : Fin NK := 32
abbrev vra_U : Fin NK := 33
abbrev vra_W : Fin NK := 6
abbrev vra_jj : Fin NK := 10
abbrev vra_dd : Fin NK := 11
abbrev vra_EE : Fin NK := 12
abbrev vra_VV : Fin NK := 16
abbrev vra_OO : Fin NK := 8
abbrev vra_OK : Fin NK := 9
abbrev vra_CK : Fin NK := 13
abbrev vra_RK : Fin NK := 1

attribute [local simp] vra_CC vra_II vra_RR vra_TT vra_PP vra_CN vra_U vra_W vra_jj vra_dd vra_EE vra_VV vra_OO vra_OK
  vra_CK vra_RK

/-- Copy the row at offset `OK` (length `VV`) of `ROWS` onto `EV`. -/
def vra_varIn : NProg NK :=
  .prim (.dup vra_OK vra_O1 (by decide)) ;; .prim (.dup vra_VV vra_L1 (by decide)) ;;
  vra_sliceP ROWS EV EVL vra_O1 vra_L1 vra_A vra_B vra_D vra_E ⟨by decide⟩

/-- `RR` copies of the row at offset `OK`, then move `OK` to the next row. -/
def vra_varMid : NProg NK :=
  .prim (.dup vra_RR vra_RK (by decide)) ;; vra_repeatP vra_RK vra_varIn ;;
  .prim (.dup vra_VV vra_W (by decide)) ;; addTo vra_W vra_OK

/-- The rows `0, …, CN - 1` from offset `OO`, each `RR` times. -/
def vra_varOuter : NProg NK :=
  .prim (.dup vra_OO vra_OK (by decide)) ;; .prim (.dup vra_CN vra_CK (by decide)) ;;
  vra_repeatP vra_CK vra_varMid ;; .prim (.pop vra_OK)

/-- The facts the copying relies on. -/
structure VraCopy (St : Lists NK) (rows : List Nat) (lE : List Nat) (V : Nat) : Prop where
  rows : St ROWS = rows
  evl : ∃ v, St EVL = lE ++ [v]
  vv : ∃ l, St vra_VV = l ++ [V]
  a : St vra_A = []
  b : St vra_B = []
  d : St vra_D = []
  e : St vra_E = []
  o1 : St vra_O1 = []
  l1 : St vra_L1 = []

theorem vra_varIn_runs (St : Lists NK) {rows lE lO : List Nat} {V v o : Nat} (hc : VraCopy St rows lE V)
    (hv : St EVL = lE ++ [v]) (ho : St vra_OK = lO ++ [o]) :
    NRuns vra_varIn St ((St.set EV (St EV ++ (rows.drop o).take V)).set EVL
      (lE ++ [v + ((rows.drop o).take V).length])) (2 + vra_sliceCost rows.length) := by
  obtain ⟨lV, hV⟩ := hc.vv
  have x₁ := nruns_dup vra_OK vra_O1 (by decide) St ho
  rw [hc.o1, List.nil_append] at x₁
  have x₂ := nruns_dup vra_VV vra_L1 (by decide) (St.set vra_O1 [o]) (l := lV) (v := V) (by simp [Lists.set, hV])
  have hL : (St.set vra_O1 [o]) vra_L1 = [] := by simp [Lists.set, hc.l1]
  rw [hL, List.nil_append] at x₂
  have x₃ := vra_slice (src := ROWS) (dst := EV) (ctr := EVL) (offS := vra_O1) (lenS := vra_L1) (A := vra_A)
    (B := vra_B) (D := vra_D) (E := vra_E) ⟨by decide⟩ ((St.set vra_O1 [o]).set vra_L1 [V]) (lo := []) (ll := [])
    (lr := lE) (off := o) (len := V) (v := v) (by simp [Lists.set, hc.a]) (by simp [Lists.set, hc.b])
    (by simp [Lists.set, hc.d]) (by simp [Lists.set, hc.e]) (by simp [Lists.set]) (by simp [Lists.set])
    (by simp [Lists.set, hv])
  have hR : ((St.set vra_O1 [o]).set vra_L1 [V]) ROWS = rows := by simp [Lists.set, hc.rows]
  have hEV : ((St.set vra_O1 [o]).set vra_L1 [V]) EV = St EV := by simp [Lists.set]
  rw [hR, hEV] at x₃
  have e : (((((St.set vra_O1 [o]).set vra_L1 [V]).set vra_O1 []).set vra_L1 []).set EV
      (St EV ++ (rows.drop o).take V)).set EVL (lE ++ [v + ((rows.drop o).take V).length]) =
      (St.set EV (St EV ++ (rows.drop o).take V)).set EVL (lE ++ [v + ((rows.drop o).take V).length]) := by
    vra_ext [vra_O1, vra_L1, EV, EVL] [hc.o1, hc.l1]
  rw [e] at x₃
  exact (x₁.seq (x₂.seq x₃)).mono (by omega)

theorem VraCopy.set {St : Lists NK} {rows lE : List Nat} {V : Nat} (hc : VraCopy St rows lE V) {k : Fin NK}
    (x : List Nat) (h : [k, ROWS, EVL, vra_VV, vra_A, vra_B, vra_D, vra_E, vra_O1, vra_L1].Nodup) :
    VraCopy (St.set k x) rows lE V := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at h
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, -⟩ := h
  obtain ⟨v, hv⟩ := hc.evl
  obtain ⟨l, hl⟩ := hc.vv
  exact ⟨by simp [Lists.set, Ne.symm h1, hc.rows], ⟨v, by simp [Lists.set, Ne.symm h2, hv]⟩,
    ⟨l, by simp [Lists.set, Ne.symm h3, hl]⟩, by simp [Lists.set, Ne.symm h4, hc.a],
    by simp [Lists.set, Ne.symm h5, hc.b], by simp [Lists.set, Ne.symm h6, hc.d], by simp [Lists.set, Ne.symm h7, hc.e],
    by simp [Lists.set, Ne.symm h8, hc.o1], by simp [Lists.set, Ne.symm h9, hc.l1]⟩

theorem VraCopy.setEVL {St : Lists NK} {rows lE : List Nat} {V : Nat} (hc : VraCopy St rows lE V) (w : Nat) :
    VraCopy (St.set EVL (lE ++ [w])) rows lE V := by
  obtain ⟨l, hl⟩ := hc.vv
  exact ⟨by simp [Lists.set, hc.rows], ⟨w, by simp⟩, ⟨l, by simp [Lists.set, hl]⟩, by simp [Lists.set, hc.a],
    by simp [Lists.set, hc.b], by simp [Lists.set, hc.d], by simp [Lists.set, hc.e], by simp [Lists.set, hc.o1],
    by simp [Lists.set, hc.l1]⟩

/-- The cost of one row (`vra_varIn`) and of `R` copies of one row (`vra_varMid`). -/
def vra_inCost (n : Nat) : Nat := 2 + vra_sliceCost n
def vra_midCost (n R V : Nat) : Nat := R * (vra_inCost n + 2) + 3 * V + 6

theorem vra_varMid_runs (St : Lists NK) {rows lE lO lR : List Nat} {V v o R : Nat} (hc : VraCopy St rows lE V)
    (hv : St EVL = lE ++ [v]) (ho : St vra_OK = lO ++ [o]) (hR : St vra_RR = lR ++ [R]) :
    NRuns vra_varMid St
      (((St.set EV (St EV ++ (List.replicate R ((rows.drop o).take V)).flatten)).set EVL
        (lE ++ [v + R * ((rows.drop o).take V).length])).set vra_OK (lO ++ [o + V]))
      (vra_midCost rows.length R V) := by
  obtain ⟨lV, hV⟩ := hc.vv
  let row := (rows.drop o).take V
  have x₁ := nruns_dup vra_RR vra_RK (by decide) St hR
  let G : Nat → Lists NK := fun m => (St.set EV (St EV ++ (List.replicate m row).flatten)).set EVL
    (lE ++ [v + m * row.length])
  have hbody : ∀ m, m < R → NRuns vra_varIn ((G m).set vra_RK (St vra_RK ++ [R - m - 1]))
      ((G (m + 1)).set vra_RK (St vra_RK ++ [R - m - 1])) (vra_inCost rows.length) := by
    intro m _
    have hc' : VraCopy ((G m).set vra_RK (St vra_RK ++ [R - m - 1])) rows lE V :=
      ((hc.set _ (k := EV) (by decide)).setEVL _).set _ (by decide)
    have y := vra_varIn_runs ((G m).set vra_RK (St vra_RK ++ [R - m - 1])) hc' (v := v + m * row.length)
      (o := o) (lO := lO) (by simp [G, Lists.set]) (by simp [G, Lists.set, ho])
    have e : ((((G m).set vra_RK (St vra_RK ++ [R - m - 1])).set EV
        (((G m).set vra_RK (St vra_RK ++ [R - m - 1])) EV ++ row)).set EVL (lE ++ [v + m * row.length + row.length]))
        = (G (m + 1)).set vra_RK (St vra_RK ++ [R - m - 1]) := by
      have h1 : ((G m).set vra_RK (St vra_RK ++ [R - m - 1])) EV = St EV ++ (List.replicate m row).flatten := by
        simp [G, Lists.set]
      rw [h1]
      have h2 : (List.replicate (m + 1) row).flatten = (List.replicate m row).flatten ++ row := by
        rw [List.replicate_succ', List.flatten_append]; simp
      simp only [G, h2, List.append_assoc, Nat.succ_mul, Nat.add_assoc]
      vra_ext [EV, EVL, vra_RK] []
    rw [e] at y
    exact y
  have x₂ := vra_repeat vra_RK vra_varIn G R _ (St vra_RK) hbody
  have e₀ : (G 0).set vra_RK (St vra_RK ++ [R]) = St.set vra_RK (St vra_RK ++ [R]) := by
    simp only [G, List.replicate_zero, List.flatten_nil, List.append_nil, Nat.zero_mul, Nat.add_zero]
    vra_ext [EV, EVL, vra_RK] [hv]
  rw [e₀] at x₂
  have x₃ := nruns_dup vra_VV vra_W (by decide) ((G R).set vra_RK (St vra_RK)) (l := lV) (v := V)
    (by simp [G, Lists.set, hV])
  have x₄ := nruns_addTo vra_W vra_OK (by decide)
    (((G R).set vra_RK (St vra_RK)).set vra_W (((G R).set vra_RK (St vra_RK)) vra_W ++ [V]))
    (l := St vra_W) (a := V) (l' := lO) (b := o) (by simp [G, Lists.set]) (by simp [G, Lists.set, ho])
  have e : ((((G R).set vra_RK (St vra_RK)).set vra_W (((G R).set vra_RK (St vra_RK)) vra_W ++ [V])).set vra_W
      (St vra_W)).set vra_OK (lO ++ [o + V]) = ((St.set EV (St EV ++ (List.replicate R row).flatten)).set EVL
        (lE ++ [v + R * row.length])).set vra_OK (lO ++ [o + V]) := by
    simp only [G]
    vra_ext [EV, EVL, vra_RK, vra_W, vra_OK] []
  rw [e] at x₄
  refine (x₁.seq (x₂.seq (x₃.seq x₄))).mono ?_
  unfold vra_midCost; omega

/-- The rows `0, …, C - 1` from offset `O`, each `R` times. -/
def vra_blkRows (rows : List Nat) (O V R C : Nat) : List Nat :=
  ((List.range C).map (fun k => (List.replicate R ((rows.drop (O + k * V)).take V)).flatten)).flatten

def vra_outerCost (n R V C : Nat) : Nat := C * (vra_midCost n R V + 2) + 5

theorem vra_varOuter_runs (St : Lists NK) {rows lE lOO lC lR : List Nat} {V v O C R : Nat}
    (hc : VraCopy St rows lE V) (hv : St EVL = lE ++ [v]) (hO : St vra_OO = lOO ++ [O]) (hC : St vra_CN = lC ++ [C])
    (hR : St vra_RR = lR ++ [R]) :
    NRuns vra_varOuter St ((St.set EV (St EV ++ vra_blkRows rows O V R C)).set EVL
      (lE ++ [v + (vra_blkRows rows O V R C).length])) (vra_outerCost rows.length R V C) := by
  have x₁ := nruns_dup vra_OO vra_OK (by decide) St hO
  have x₂ := nruns_dup vra_CN vra_CK (by decide) (St.set vra_OK (St vra_OK ++ [O])) (l := lC) (v := C)
    (by simp [Lists.set, hC])
  have hCK : (St.set vra_OK (St vra_OK ++ [O])) vra_CK = St vra_CK := by simp [Lists.set]
  rw [hCK] at x₂
  let G : Nat → Lists NK := fun k => ((St.set EV (St EV ++ vra_blkRows rows O V R k)).set EVL
    (lE ++ [v + (vra_blkRows rows O V R k).length])).set vra_OK (St vra_OK ++ [O + k * V])
  have hbody : ∀ k, k < C → NRuns vra_varMid ((G k).set vra_CK (St vra_CK ++ [C - k - 1]))
      ((G (k + 1)).set vra_CK (St vra_CK ++ [C - k - 1])) (vra_midCost rows.length R V) := by
    intro k _
    have hc' : VraCopy ((G k).set vra_CK (St vra_CK ++ [C - k - 1])) rows lE V :=
      ((((hc.set _ (k := EV) (by decide)).setEVL _).set _ (k := vra_OK) (by decide)).set _ (by decide))
    have y := vra_varMid_runs ((G k).set vra_CK (St vra_CK ++ [C - k - 1])) hc'
      (v := v + (vra_blkRows rows O V R k).length) (o := O + k * V) (lO := St vra_OK) (R := R) (lR := lR)
      (by simp [G, Lists.set]) (by simp [G, Lists.set]) (by simp [G, Lists.set, hR])
    have e : ((((G k).set vra_CK (St vra_CK ++ [C - k - 1])).set EV
        (((G k).set vra_CK (St vra_CK ++ [C - k - 1])) EV ++
          (List.replicate R ((rows.drop (O + k * V)).take V)).flatten)).set EVL
        (lE ++ [v + (vra_blkRows rows O V R k).length + R * ((rows.drop (O + k * V)).take V).length])).set vra_OK
        (St vra_OK ++ [O + k * V + V]) = (G (k + 1)).set vra_CK (St vra_CK ++ [C - k - 1]) := by
      have h1 : ((G k).set vra_CK (St vra_CK ++ [C - k - 1])) EV = St EV ++ vra_blkRows rows O V R k := by
        simp [G, Lists.set]
      have h2 : vra_blkRows rows O V R (k + 1) = vra_blkRows rows O V R k ++
          (List.replicate R ((rows.drop (O + k * V)).take V)).flatten := by
        simp [vra_blkRows, List.range_succ]
      have h3 : (vra_blkRows rows O V R (k + 1)).length = (vra_blkRows rows O V R k).length +
          R * ((rows.drop (O + k * V)).take V).length := by
        rw [h2, List.length_append, vra_flatten_replicate_length]
      rw [h1]
      simp only [G, h3, ← h2, List.append_assoc, Nat.succ_mul, Nat.add_assoc]
      vra_ext [EV, EVL, vra_CK, vra_OK] []
    rw [e] at y
    exact y
  have x₃ := vra_repeat vra_CK vra_varMid G C _ (St vra_CK) hbody
  have e₀ : (G 0).set vra_CK (St vra_CK ++ [C]) = (St.set vra_OK (St vra_OK ++ [O])).set vra_CK
      (St vra_CK ++ [C]) := by
    simp only [G, vra_blkRows, List.range_zero, List.map_nil, List.flatten_nil, List.append_nil, Nat.zero_mul,
      Nat.add_zero, List.length_nil]
    vra_ext [EV, EVL, vra_CK, vra_OK] [hv]
  rw [e₀] at x₃
  have x₄ := nruns_pop vra_OK ((G C).set vra_CK (St vra_CK)) (l := St vra_OK) (v := O + C * V)
    (by simp [G, Lists.set])
  have e : ((G C).set vra_CK (St vra_CK)).set vra_OK (St vra_OK) = (St.set EV (St EV ++ vra_blkRows rows O V R C)).set
      EVL (lE ++ [v + (vra_blkRows rows O V R C).length]) := by
    simp only [G]
    vra_ext [EV, EVL, vra_CK, vra_OK] []
  rw [e] at x₄
  refine (x₁.seq (x₂.seq (x₃.seq x₄))).mono ?_
  unfold vra_outerCost; omega

/-! ## The variable item: the walk up the contexts -/

/-- Read the binder of context `c + 1` (the top of `CC`, lowered to `c`): its type onto `TT`, its parent onto `PP`;
`CC` keeps `c`. -/
def vra_binderP : NProg NK :=
  .prim (.dec vra_CC) ;;
  entryP CTs vra_CC vra_jj vra_dd vra_T vra_TT (by decide) (by decide) (by decide) (by decide) true ;;
  entryP CTs vra_CC vra_jj vra_dd vra_T vra_PP (by decide) (by decide) (by decide) (by decide) false

/-- One step up: `CC` becomes the parent, `RR` is multiplied by the number of rows of the binder type. -/
def vra_varUpP : NProg NK :=
  vra_binderP ;; .prim (.pop vra_CC) ;; nmv vra_PP vra_CC (by decide) ;;
  peekAt CNT vra_T vra_TT vra_CN (by decide) (by decide) ;;
  vra_mulP vra_RR vra_CN vra_U vra_W (by decide) (by decide)

theorem vra_binder_runs (St : Lists NK) {ct : List (Nat × Nat)} (hct : St CTs = encPairs ct) (hT : St vra_T = [])
    {lc : List Nat} {w : Nat} (hw : w < ct.length) (hCC : St vra_CC = lc ++ [w + 1]) :
    NRuns vra_binderP St (((St.set vra_CC (lc ++ [w])).set vra_TT (St vra_TT ++ [ct[w].2])).set vra_PP
      (St vra_PP ++ [ct[w].1])) (24 * ct.length + 22 * w + 33) := by
  have x₁ := nruns_dec vra_CC St hCC
  rw [Nat.add_sub_cancel] at x₁
  let S₁ := St.set vra_CC (lc ++ [w])
  have x₂ := entryP_runs CTs vra_CC vra_jj vra_dd vra_T vra_TT (by decide) (by decide) (by decide) (by decide)
    (by decide) true (by decide) S₁ (lc := lc) (c := w) (v := ct[w].2) (by simp [S₁]) (by simp [S₁, Lists.set, hT])
    (by simp only [S₁, cond]; rw [Lists.set_ne _ _ (by decide), hct]; simpa using encPairs_snd ct w hw)
  let S₂ := S₁.set vra_TT (S₁ vra_TT ++ [ct[w].2])
  have x₃ := entryP_runs CTs vra_CC vra_jj vra_dd vra_T vra_PP (by decide) (by decide) (by decide) (by decide)
    (by decide) false (by decide) S₂ (lc := lc) (c := w) (v := ct[w].1) (by simp [S₂, S₁, Lists.set])
    (by simp [S₂, S₁, Lists.set, hT])
    (by simp only [S₂, S₁, cond]; rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide), hct]
        simpa using encPairs_fst ct w hw)
  have hl : (S₁ CTs).length = 2 * ct.length := by simp [S₁, Lists.set, hct, encPairs_length]
  have hl₂ : (S₂ CTs).length = 2 * ct.length := by simp [S₂, S₁, Lists.set, hct, encPairs_length]
  rw [hl] at x₂; rw [hl₂] at x₃
  have e : S₂.set vra_PP (S₂ vra_PP ++ [ct[w].1]) = (((St.set vra_CC (lc ++ [w])).set vra_TT
      (St vra_TT ++ [ct[w].2])).set vra_PP (St vra_PP ++ [ct[w].1])) := by
    simp only [S₂, S₁]
    vra_ext [vra_CC, vra_TT, vra_PP] []
  rw [e] at x₃
  exact (x₁.seq (x₂.seq x₃)).mono (by omega)

/-- The cost of a step up. -/
def vra_upCost (nct ntt r C : Nat) : Nat := 24 * nct + 22 * nct + 6 * (ntt + 1) + 4 * ntt + C * (3 * r + 6) + 60

theorem vra_varUp_runs (St : Lists NK) {j cap N : Nat} {tt ct : List (Nat × Nat)} (hwf : CTWF tt ct)
    (hct : St CTs = encPairs ct) (hcnt : St CNT = cntTable j cap N tt) (hT : St vra_T = [])
    {lc lr : List Nat} {w r : Nat} (hw : w < ct.length) (hCC : St vra_CC = lc ++ [w + 1])
    (hRR : St vra_RR = lr ++ [r]) :
    NRuns vra_varUpP St ((St.set vra_CC (lc ++ [ct[w].1])).set vra_RR
      (lr ++ [r * (rowsT j cap N tt ct[w].2).length]))
      (vra_upCost ct.length tt.length r (rowsT j cap N tt ct[w].2).length) := by
  have ht : ct[w].2 ≤ tt.length := (hwf w hw).2
  have x₁ := vra_binder_runs St hct hT hw hCC
  let S₁ := ((St.set vra_CC (lc ++ [w])).set vra_TT (St vra_TT ++ [ct[w].2])).set vra_PP (St vra_PP ++ [ct[w].1])
  have x₂ := nruns_pop vra_CC S₁ (l := lc) (v := w) (by simp [S₁, Lists.set])
  have x₃ := nruns_mv vra_PP vra_CC (by decide) (S₁.set vra_CC lc) (l := St vra_PP) (v := ct[w].1)
    (by simp [S₁, Lists.set])
  let S₃ := ((S₁.set vra_CC lc).set vra_CC ((S₁.set vra_CC lc) vra_CC ++ [ct[w].1])).set vra_PP (St vra_PP)
  have hk : ct[w].2 < (S₃ CNT).length := by simp [S₃, S₁, Lists.set, hcnt, cntTable, typeTable]; omega
  have x₄ := nruns_peekAt CNT vra_T vra_TT vra_CN (by decide) (by decide) (by decide) S₃ (by simp [S₃, S₁, Lists.set, hT])
    (lc := St vra_TT) (k := ct[w].2) (by simp [S₃, S₁, Lists.set]) hk
  have hv : (S₃ CNT)[ct[w].2]'hk = (rowsT j cap N tt ct[w].2).length := by
    simp only [S₃, S₁, Lists.set_ne _ _ (show CNT ≠ vra_PP by decide), Lists.set_ne _ _ (show CNT ≠ vra_CC by decide),
      Lists.set_ne _ _ (show CNT ≠ vra_TT by decide)]
    simp only [hcnt, cntTable]
    exact vra_typeTable_get tt _ ht
  have hlen : (S₃ CNT).length = tt.length + 1 := by simp [S₃, S₁, Lists.set, hcnt, cntTable, typeTable]
  rw [hv, hlen] at x₄
  let C := (rowsT j cap N tt ct[w].2).length
  let S₄ := (S₃.set vra_TT (St vra_TT)).set vra_CN (S₃ vra_CN ++ [C])
  have x₅ := vra_mul (R := vra_RR) (Cn := vra_CN) (U := vra_U) (W := vra_W) ⟨by decide, by decide, by decide, by decide,
    by decide, by decide⟩ S₄ (lR := lr) (lC := St vra_CN) (r := r) (c := C) (by simp [S₄, S₃, S₁, Lists.set, hRR])
    (by simp [S₄, S₃, S₁, Lists.set])
  have e : (S₄.set vra_RR (lr ++ [r * C])).set vra_CN (St vra_CN) = (St.set vra_CC (lc ++ [ct[w].1])).set vra_RR
      (lr ++ [r * C]) := by
    simp only [S₄, S₃, S₁]
    vra_ext [vra_CC, vra_TT, vra_PP, vra_CN, vra_RR] []
  rw [e] at x₅
  refine (x₁.seq (x₂.seq (x₃.seq (x₄.seq x₅)))).mono ?_
  have hCC' : C * (3 * r + 6) = (rowsT j cap N tt ct[w].2).length * (3 * r + 6) := rfl
  unfold vra_upCost; omega

/-- Walk `a` steps up from the item's context: `CC` ends at the context reached, `RR` at the product of the numbers
of rows of the binder types passed. -/
def vra_varWalkP : NProg NK :=
  .prim (.dup IT vra_CC (by decide)) ;; vra_readITP 1 vra_II (by decide) ;; npushC vra_RR 1 ;;
  .loop vra_II .pos (.prim (.dec vra_II) ;; .ite vra_CC .zero (nskip vra_T) vra_varUpP) ;;
  .prim (.pop vra_II)

theorem vra_cnt_le_sum (j cap N : Nat) (tt : List (Nat × Nat)) {t : Nat} (ht : t ≤ tt.length) :
    (rowsT j cap N tt t).length ≤ (cntTable j cap N tt).sum :=
  vra_le_sum (List.mem_map.2 ⟨t, List.mem_range.2 (by omega), rfl⟩)

theorem vra_fac_le (j cap N : Nat) {tt ct : List (Nat × Nat)} {w : Nat} (hw : w < ct.length) :
    vra_fac j cap N tt ct (w + 1) = (rowsT j cap N tt ct[w].2).length := by
  simp [vra_fac, List.getElem?_eq_getElem hw]

/-- The cost of a round of the walk. -/
def vra_walkRound (nct ntt Bn Bc : Nat) : Nat := 46 * nct + 10 * ntt + 3 * Bn + 6 * Bc + 70

theorem vra_walk_runs (St : Lists NK) {j cap N : Nat} {tt ct : List (Nat × Nat)} (hwf : CTWF tt ct) {it : MItem}
    (hct : St CTs = encPairs ct) (hcnt : St CNT = cntTable j cap N tt) (hIT : St IT = encItem it)
    (hT : St vra_T = []) (hCC : St vra_CC = []) (hII : St vra_II = []) (hRR : St vra_RR = [])
    (hcur : it.ctx ≤ ct.length) (Bn : Nat) (hBn : ∀ m, m < it.a → vra_Rf j cap N tt ct it.ctx (m + 1) ≤ Bn) :
    NRuns vra_varWalkP St ((St.set vra_CC [walkCtx ct it.ctx it.a]).set vra_RR [vra_Rf j cap N tt ct it.ctx it.a])
      (1 + (5 * 1 + 31) + 2 + (it.a * (vra_walkRound ct.length tt.length Bn (cntTable j cap N tt).sum + 1) + 1)
        + 1) := by
  have x₁ := nruns_dup IT vra_CC (by decide) St (l := [it.tag, it.a, it.b]) (v := it.ctx) (by rw [hIT]; rfl)
  rw [hCC, List.nil_append] at x₁
  have x₂ := vra_readIT (o := vra_II) (by decide) (by decide) (St.set vra_CC [it.ctx]) (it := it)
    (by simp [Lists.set, hIT]) (by simp [Lists.set, hT]) 1 (by decide)
  have hv₂ : (encItem it)[1]'(by simp [encItem]) = it.a := by simp [encItem]
  rw [hv₂, show (St.set vra_CC [it.ctx]) vra_II = [] by simp [Lists.set, hII], List.nil_append] at x₂
  have x₃ := nruns_pushC vra_RR ((St.set vra_CC [it.ctx]).set vra_II [it.a]) 1
  rw [show ((St.set vra_CC [it.ctx]).set vra_II [it.a]) vra_RR = [] by simp [Lists.set, hRR], List.nil_append] at x₃
  let F : Nat → Lists NK := fun m => ((St.set vra_CC [walkCtx ct it.ctx m]).set vra_II [it.a - m]).set vra_RR
    [vra_Rf j cap N tt ct it.ctx m]
  have hF0 : ((St.set vra_CC [it.ctx]).set vra_II [it.a]).set vra_RR [1] = F 0 := by simp [F, walkCtx, vra_Rf]
  rw [hF0] at x₃
  have hFI : ∀ m, F m vra_II = [] ++ [it.a - m] := fun m => by simp [F, Lists.set]
  have hl := nruns_family_const (i := vra_II) (c := .pos)
    (p := .prim (.dec vra_II) ;; .ite vra_CC .zero (nskip vra_T) vra_varUpP) F it.a
    (vra_walkRound ct.length tt.length Bn (cntTable j cap N tt).sum)
    (fun m hm => by rw [hFI, show it.a - m = (it.a - m - 1) + 1 by omega]; rfl)
    (by rw [hFI, Nat.sub_self]; rfl)
    (fun m hm => by
      have y₁ := nruns_dec vra_II (F m) (hFI m)
      let G := (F m).set vra_II ([] ++ [it.a - m - 1])
      have hwalk := walkCtx_le hwf it.ctx hcur m
      rcases hz : walkCtx ct it.ctx m with _ | w
      · -- the walk is at the empty context: nothing to do
        have y₂ := nruns_skip vra_T G
        have e : G = F (m + 1) := by
          simp only [G, F]
          rw [walkCtx, hz, vra_Rf_succ', hz, show it.a - (m + 1) = it.a - m - 1 by omega]
          simp only [upCtx, vra_fac, Nat.mul_one, List.nil_append]
          vra_ext [vra_CC, vra_II, vra_RR] []
        have := (y₁.seq (y₂.iteT (i := vra_CC) (c := .zero) (q := vra_varUpP)
          (by simp only [G, F, Lists.set]; simp [hz]; rfl)))
        rw [e] at this
        exact this.mono (by unfold vra_walkRound; omega)
      · -- one step up
        have hw : w < ct.length := by omega
        have y₂ := vra_varUp_runs (j := j) (cap := cap) (N := N) G hwf (by simp [G, F, Lists.set, hct]) (by simp [G, F, Lists.set, hcnt])
          (by simp [G, F, Lists.set, hT]) hw (lc := []) (lr := []) (r := vra_Rf j cap N tt ct it.ctx m)
          (by simp [G, F, Lists.set, hz]) (by simp [G, F, Lists.set])
        have hRf : vra_Rf j cap N tt ct it.ctx (m + 1) =
            vra_Rf j cap N tt ct it.ctx m * (rowsT j cap N tt ct[w].2).length := by
          rw [vra_Rf_succ', hz, vra_fac_le j cap N hw]
        have e : (G.set vra_CC ([] ++ [ct[w].1])).set vra_RR
            ([] ++ [vra_Rf j cap N tt ct it.ctx m * (rowsT j cap N tt ct[w].2).length]) = F (m + 1) := by
          have hup : walkCtx ct it.ctx (m + 1) = ct[w].1 := by
            rw [walkCtx, hz]; simp [upCtx, List.getElem?_eq_getElem hw]
          simp only [G, F, hup, ← hRf, show it.a - (m + 1) = it.a - m - 1 by omega, List.nil_append]
          vra_ext [vra_CC, vra_II, vra_RR] []
        rw [e] at y₂
        have := (y₁.seq (y₂.iteF (i := vra_CC) (c := .zero) (p := nskip vra_T) (by simp only [G, F, Lists.set]; simp [hz]; rfl)))
        refine this.mono ?_
        have ht : ct[w].2 ≤ tt.length := (hwf w hw).2
        have hC := vra_cnt_le_sum j cap N tt ht
        have hB := hBn m hm
        rw [hRf] at hB
        have hmul : (rowsT j cap N tt ct[w].2).length * (3 * vra_Rf j cap N tt ct it.ctx m + 6) =
            3 * (vra_Rf j cap N tt ct it.ctx m * (rowsT j cap N tt ct[w].2).length) +
              6 * (rowsT j cap N tt ct[w].2).length := by
          rw [Nat.mul_add, Nat.mul_comm (rowsT j cap N tt ct[w].2).length, Nat.mul_assoc, Nat.mul_comm 6]
        unfold vra_upCost vra_walkRound
        omega)
  have x₄ := nruns_pop vra_II (F it.a) (l := []) (v := 0) (by rw [hFI, Nat.sub_self])
  have e : (F it.a).set vra_II [] = (St.set vra_CC [walkCtx ct it.ctx it.a]).set vra_RR
      [vra_Rf j cap N tt ct it.ctx it.a] := by
    simp only [F]
    vra_ext [vra_CC, vra_II, vra_RR] [hII]
  rw [e] at x₄
  exact (x₁.seq (x₂.seq (x₃.seq (hl.seq x₄)))).mono (by omega)

/-- At the end of the walk (context `w + 1` on `CC`): read the binder's tables and copy the rows. -/
def vra_varEndP : NProg NK :=
  vra_binderP ;; .prim (.pop vra_CC) ;;
  peekAt ENVT vra_T vra_PP vra_EE (by decide) (by decide) ;;
  .prim (.dup vra_TT vra_jj (by decide)) ;; peekAt CNT vra_T vra_jj vra_CN (by decide) (by decide) ;;
  .prim (.dup vra_TT vra_jj (by decide)) ;; peekAt VALT vra_T vra_jj vra_VV (by decide) (by decide) ;;
  peekAt ROFF vra_T vra_TT vra_OO (by decide) (by decide) ;;
  .prim (.pushZ EVL) ;; vra_repeatP vra_EE vra_varOuter ;;
  .prim (.pop vra_OO) ;; .prim (.pop vra_VV) ;; .prim (.pop vra_CN) ;; .prim (.pop vra_RR)

theorem vra_get_of_some {l : List Nat} {k v : Nat} (h : l[k]? = some v) (hk : k < l.length) : l[k] = v := by
  rw [List.getElem?_eq_getElem hk] at h; exact Option.some.inj h

/-- The cost of the end of the walk. -/
def vra_endCost (nct ntt E R V C nrows : Nat) : Nat :=
  46 * nct + 34 + 6 * (nct + 1) + 4 * nct + 3 * (6 * (ntt + 1) + 4 * ntt + 7) + 1 +
    (E * (vra_outerCost nrows R V C + 2) + 2) + 4

theorem vra_varEnd_runs (St : Lists NK) {j cap N : Nat} {tt ct : List (Nat × Nat)} (hwf : CTWF tt ct)
    (hct : St CTs = encPairs ct) (henv : St ENVT = envTable j cap N tt ct) (hcnt : St CNT = cntTable j cap N tt)
    (hval : St VALT = valTable j cap N tt) (hroff : St ROFF = roffTable j cap N tt)
    (hrows : St ROWS = rowsFlat j cap N tt)
    (hT : St vra_T = []) (hA : St vra_A = []) (hB : St vra_B = []) (hD : St vra_D = []) (hE : St vra_E = [])
    (hO1 : St vra_O1 = []) (hL1 : St vra_L1 = []) (hTT : St vra_TT = []) (hPP : St vra_PP = [])
    (hCN : St vra_CN = []) {w R O V : Nat} (hw : w < ct.length) (hCC : St vra_CC = [w + 1])
    (hRR : St vra_RR = [R]) (hO : (roffTable j cap N tt)[ct[w].2]? = some O)
    (hV : (valTable j cap N tt)[ct[w].2]? = some V) :
    NRuns vra_varEndP St ((((St.set vra_CC []).set vra_RR []).set EV (St EV ++ (List.replicate
        (envT j cap N tt ct ct[w].1) (vra_blkRows (rowsFlat j cap N tt) O V R
          (rowsT j cap N tt ct[w].2).length)).flatten)).set EVL (St EVL ++ [envT j cap N tt ct ct[w].1 *
            (vra_blkRows (rowsFlat j cap N tt) O V R (rowsT j cap N tt ct[w].2).length).length]))
      (vra_endCost ct.length tt.length (envT j cap N tt ct ct[w].1) R V (rowsT j cap N tt ct[w].2).length
        (rowsFlat j cap N tt).length) := by
  have ht : ct[w].2 ≤ tt.length := (hwf w hw).2
  have hp : ct[w].1 ≤ w := (hwf w hw).1
  obtain ⟨t, htd⟩ : ∃ t, ct[w].2 = t := ⟨_, rfl⟩
  obtain ⟨par, hpd⟩ : ∃ p, ct[w].1 = p := ⟨_, rfl⟩
  rw [htd] at ht hO hV ⊢; rw [hpd] at hp ⊢
  obtain ⟨E, hEd⟩ : ∃ E, envT j cap N tt ct par = E := ⟨_, rfl⟩
  obtain ⟨C, hCd⟩ : ∃ C, (rowsT j cap N tt t).length = C := ⟨_, rfl⟩
  rw [hEd, hCd]
  have x₁ := vra_binder_runs St hct hT hw (lc := []) hCC
  rw [hTT, hPP, htd, hpd, List.nil_append, List.nil_append] at x₁
  let S₁ := ((St.set vra_CC [w]).set vra_TT [t]).set vra_PP [par]
  have x₂ := nruns_pop vra_CC S₁ (l := []) (v := w) (by simp [S₁, Lists.set])
  let S₂ := S₁.set vra_CC []
  have hkE : par < (S₂ ENVT).length := by simp [S₂, S₁, Lists.set, henv, envTable]; omega
  have x₃ := nruns_peekAt ENVT vra_T vra_PP vra_EE (by decide) (by decide) (by decide) S₂
    (by simp [S₂, S₁, Lists.set, hT]) (lc := []) (k := par) (by simp [S₂, S₁, Lists.set]) hkE
  have hvE : (S₂ ENVT)[par]'hkE = E := by
    simp only [S₂, S₁, Lists.set_ne _ _ (show ENVT ≠ vra_CC by decide), Lists.set_ne _ _ (show ENVT ≠ vra_PP by decide),
      Lists.set_ne _ _ (show ENVT ≠ vra_TT by decide), henv]
    rw [← hEd]; exact vra_envT_entry _ _ _ _ _ _ (by omega)
  have hlE : (S₂ ENVT).length = ct.length + 1 := by simp [S₂, S₁, Lists.set, henv, envTable]
  rw [hvE, hlE] at x₃
  let S₃ := (S₂.set vra_PP []).set vra_EE (S₂ vra_EE ++ [E])
  have x₄ := nruns_dup vra_TT vra_jj (by decide) S₃ (l := []) (v := t) (by simp [S₃, S₂, S₁, Lists.set])
  let S₄ := S₃.set vra_jj (S₃ vra_jj ++ [t])
  have hkC : t < (S₄ CNT).length := by simp [S₄, S₃, S₂, S₁, Lists.set, hcnt, cntTable, typeTable]; omega
  have x₅ := nruns_peekAt CNT vra_T vra_jj vra_CN (by decide) (by decide) (by decide) S₄
    (by simp [S₄, S₃, S₂, S₁, Lists.set, hT]) (lc := S₃ vra_jj) (k := t) (by simp [S₄]) hkC
  have hvC : (S₄ CNT)[t]'hkC = C := by
    have : S₄ CNT = cntTable j cap N tt := by simp [S₄, S₃, S₂, S₁, Lists.set, hcnt]
    simp only [this, cntTable]; rw [← hCd]; exact vra_typeTable_get tt _ ht
  have hlC : (S₄ CNT).length = tt.length + 1 := by simp [S₄, S₃, S₂, S₁, Lists.set, hcnt, cntTable, typeTable]
  rw [hvC, hlC] at x₅
  let S₅ := (S₄.set vra_jj (S₃ vra_jj)).set vra_CN (S₄ vra_CN ++ [C])
  have x₆ := nruns_dup vra_TT vra_jj (by decide) S₅ (l := []) (v := t) (by simp [S₅, S₄, S₃, S₂, S₁, Lists.set])
  let S₆ := S₅.set vra_jj (S₅ vra_jj ++ [t])
  have hkV : t < (S₆ VALT).length := by simp [S₆, S₅, S₄, S₃, S₂, S₁, Lists.set, hval, valTable, typeTable]; omega
  have x₇ := nruns_peekAt VALT vra_T vra_jj vra_VV (by decide) (by decide) (by decide) S₆
    (by simp [S₆, S₅, S₄, S₃, S₂, S₁, Lists.set, hT]) (lc := S₅ vra_jj) (k := t) (by simp [S₆]) hkV
  have hvV : (S₆ VALT)[t]'hkV = V := by
    have : S₆ VALT = valTable j cap N tt := by simp [S₆, S₅, S₄, S₃, S₂, S₁, Lists.set, hval]
    simp only [this]; exact vra_get_of_some hV _
  have hlV : (S₆ VALT).length = tt.length + 1 := by simp [S₆, S₅, S₄, S₃, S₂, S₁, Lists.set, hval, valTable, typeTable]
  rw [hvV, hlV] at x₇
  let S₇ := (S₆.set vra_jj (S₅ vra_jj)).set vra_VV (S₆ vra_VV ++ [V])
  have hkO : t < (S₇ ROFF).length := by
    simp [S₇, S₆, S₅, S₄, S₃, S₂, S₁, Lists.set, hroff, roffTable, typeTable]; omega
  have x₈ := nruns_peekAt ROFF vra_T vra_TT vra_OO (by decide) (by decide) (by decide) S₇
    (by simp [S₇, S₆, S₅, S₄, S₃, S₂, S₁, Lists.set, hT]) (lc := []) (k := t)
    (by simp [S₇, S₆, S₅, S₄, S₃, S₂, S₁, Lists.set]) hkO
  have hvO : (S₇ ROFF)[t]'hkO = O := by
    have : S₇ ROFF = roffTable j cap N tt := by simp [S₇, S₆, S₅, S₄, S₃, S₂, S₁, Lists.set, hroff]
    simp only [this]; exact vra_get_of_some hO _
  have hlO : (S₇ ROFF).length = tt.length + 1 := by
    simp [S₇, S₆, S₅, S₄, S₃, S₂, S₁, Lists.set, hroff, roffTable, typeTable]
  rw [hvO, hlO] at x₈
  -- the state before the copies, in short
  have e₈ : (S₇.set vra_TT []).set vra_OO (S₇ vra_OO ++ [O]) = ((((((St.set vra_CC []).set vra_RR [R]).set vra_EE (St vra_EE ++ [E])).set vra_CN [C]).set vra_VV
      (St vra_VV ++ [V])).set vra_OO (St vra_OO ++ [O])) := by
    simp only [S₇, S₆, S₅, S₄, S₃, S₂, S₁]
    vra_ext [vra_CC, vra_TT, vra_PP, vra_EE, vra_jj, vra_CN, vra_VV, vra_OO, vra_RR] [hRR, hTT, hPP, hCN]
  rw [e₈] at x₈
  let Sb := ((((((St.set vra_CC []).set vra_RR [R]).set vra_EE (St vra_EE ++ [E])).set vra_CN [C]).set vra_VV
      (St vra_VV ++ [V])).set vra_OO (St vra_OO ++ [O]))
  have x₉ := nruns_pushZ EVL Sb
  have hEVLb : Sb EVL = St EVL := by simp [Sb, Lists.set]
  rw [hEVLb] at x₉
  let blk := vra_blkRows (rowsFlat j cap N tt) O V R C
  let G : Nat → Lists NK := fun e => ((((((St.set vra_CC []).set vra_RR [R]).set vra_CN [C]).set vra_VV
      (St vra_VV ++ [V])).set vra_OO (St vra_OO ++ [O])).set EV (St EV ++ (List.replicate e blk).flatten)).set EVL
      (St EVL ++ [e * blk.length])
  have hbody : ∀ e, e < E → NRuns vra_varOuter ((G e).set vra_EE (St vra_EE ++ [E - e - 1]))
      ((G (e + 1)).set vra_EE (St vra_EE ++ [E - e - 1])) (vra_outerCost (rowsFlat j cap N tt).length R V C) := by
    intro e _
    let Ge := (G e).set vra_EE (St vra_EE ++ [E - e - 1])
    have hc : VraCopy Ge (rowsFlat j cap N tt) (St EVL) V :=
      ⟨by simp [Ge, G, Lists.set, hrows], ⟨e * blk.length, by simp [Ge, G, Lists.set]⟩,
        ⟨St vra_VV, by simp [Ge, G, Lists.set]⟩, by simp [Ge, G, Lists.set, hA], by simp [Ge, G, Lists.set, hB],
        by simp [Ge, G, Lists.set, hD], by simp [Ge, G, Lists.set, hE], by simp [Ge, G, Lists.set, hO1],
        by simp [Ge, G, Lists.set, hL1]⟩
    have y := vra_varOuter_runs Ge hc (v := e * blk.length) (lOO := St vra_OO) (lC := []) (lR := [])
      (O := O) (C := C) (R := R) (by simp [Ge, G, Lists.set]) (by simp [Ge, G, Lists.set])
      (by simp [Ge, G, Lists.set]) (by simp [Ge, G, Lists.set])
    have e₁ : (Ge.set EV (Ge EV ++ blk)).set EVL (St EVL ++ [e * blk.length + blk.length]) =
        (G (e + 1)).set vra_EE (St vra_EE ++ [E - e - 1]) := by
      have h1 : Ge EV = St EV ++ (List.replicate e blk).flatten := by simp [Ge, G, Lists.set]
      have h2 : (List.replicate (e + 1) blk).flatten = (List.replicate e blk).flatten ++ blk := by
        rw [List.replicate_succ', List.flatten_append]; simp
      rw [h1]
      simp only [Ge, G, h2, List.append_assoc, Nat.succ_mul]
      vra_ext [vra_CC, vra_RR, vra_CN, vra_VV, vra_OO, EV, EVL, vra_EE] []
    rw [e₁] at y
    exact y
  have x₁₀ := vra_repeat vra_EE vra_varOuter G E _ (St vra_EE) hbody
  have e₉ : Sb.set EVL (St EVL ++ [0]) = (G 0).set vra_EE (St vra_EE ++ [E]) := by
    simp only [Sb, G, List.replicate_zero, List.flatten_nil, List.append_nil, Nat.zero_mul]
    vra_ext [vra_CC, vra_RR, vra_CN, vra_VV, vra_OO, EV, EVL, vra_EE] []
  rw [e₉] at x₉
  -- clean up
  have x₁₁ := nruns_pop vra_OO ((G E).set vra_EE (St vra_EE)) (l := St vra_OO) (v := O) (by simp [G, Lists.set])
  have x₁₂ := nruns_pop vra_VV (((G E).set vra_EE (St vra_EE)).set vra_OO (St vra_OO)) (l := St vra_VV) (v := V)
    (by simp [G, Lists.set])
  have x₁₃ := nruns_pop vra_CN ((((G E).set vra_EE (St vra_EE)).set vra_OO (St vra_OO)).set vra_VV (St vra_VV))
    (l := []) (v := C) (by simp [G, Lists.set])
  have x₁₄ := nruns_pop vra_RR (((((G E).set vra_EE (St vra_EE)).set vra_OO (St vra_OO)).set vra_VV
    (St vra_VV)).set vra_CN []) (l := []) (v := R) (by simp [G, Lists.set])
  have e₁₄ : (((((G E).set vra_EE (St vra_EE)).set vra_OO (St vra_OO)).set vra_VV (St vra_VV)).set vra_CN []).set
      vra_RR [] = (((St.set vra_CC []).set vra_RR []).set EV (St EV ++ (List.replicate E blk).flatten)).set EVL
        (St EVL ++ [E * blk.length]) := by
    simp only [G]
    vra_ext [vra_CC, vra_RR, vra_CN, vra_VV, vra_OO, EV, EVL, vra_EE] [hCN]
  rw [e₁₄] at x₁₄
  refine (x₁.seq (x₂.seq (x₃.seq (x₄.seq (x₅.seq (x₆.seq (x₇.seq (x₈.seq (x₉.seq (x₁₀.seq (x₁₁.seq (x₁₂.seq
    (x₁₃.seq x₁₄))))))))))))).mono ?_
  unfold vra_endCost
  omega

/-! ## The variable item: what it computes -/

/-- The value of the variable item. -/
def vra_varOut (j cap N : Nat) (tt ct : List (Nat × Nat)) (c a : Nat) : List Nat :=
  ((varVecT j cap N tt ct c a).map (fun k => (rowsT j cap N tt ((varTy ct c a).getD 0)).getD k [])).flatten

theorem vra_stepT_var (j cap : Nat) (st : PSt) (Tf : List (List Nat)) (it : MItem) (htag : it.tag = 9)
    (vs : List (List Nat)) :
    stepT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt Tf it vs =
      vra_varOut j cap st.x.length st.tt st.ct it.ctx it.a :: vs := by
  unfold stepT; rw [htag]; simp [vra_varOut]

section VarOut

variable {j cap N : Nat} {tt ct : List (Nat × Nat)}

theorem vra_varOut_walk0 (hwf : CTWF tt ct) {c a : Nat} (hc : c ≤ ct.length) (h : walkCtx ct c a = 0) :
    vra_varOut j cap N tt ct c a = [] := by
  unfold vra_varOut; rw [vra_varVecT_eq hwf a c hc, if_pos h]; rfl

theorem vra_flatMap_rep_zero (l : List Nat) : l.flatMap (fun v => List.replicate 0 v) = [] := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, ih]

theorem vra_varOut_env0 (hwf : CTWF tt ct) {c a : Nat} (hc : c ≤ ct.length) (h : envT j cap N tt ct c = 0) :
    vra_varOut j cap N tt ct c a = [] := by
  unfold vra_varOut
  rw [vra_varVecT_eq hwf a c hc]
  split
  · rfl
  · rename_i hw
    have hwl := walkCtx_le hwf c hc a
    have e₁ := vra_envT_walk (j := j) (cap := cap) (N := N) hwf a c hc
    have e₂ := vra_envT_up (j := j) (cap := cap) (N := N) hwf (walkCtx ct c a) hwl
    rw [h, e₂] at e₁
    have hz : vra_Rf j cap N tt ct c a = 0 ∨ vra_fac j cap N tt ct (walkCtx ct c a) = 0 ∨
        envT j cap N tt ct (upCtx ct (walkCtx ct c a)) = 0 := by
      rcases Nat.mul_eq_zero.1 e₁.symm with h₁ | h₁
      · exact .inl h₁
      · rcases Nat.mul_eq_zero.1 h₁ with h₂ | h₂
        · exact .inr (.inl h₂)
        · exact .inr (.inr h₂)
    rcases hz with h₁ | h₁ | h₁
    · rw [h₁, vra_flatMap_rep_zero]; rfl
    · simp [vra_base, h₁]
    · simp [vra_base, h₁]

/-- **The value of the variable item at the end `w + 1` of the walk**: the rows of the binder type, from the tables,
each repeated. -/
theorem vra_varOut_end (hwf : CTWF tt ct) {c a w O V : Nat} (hc : c ≤ ct.length) (h : walkCtx ct c a = w + 1)
    (hw : w < ct.length) (hO : (roffTable j cap N tt)[ct[w].2]? = some O)
    (hV : (valTable j cap N tt)[ct[w].2]? = some V) :
    vra_varOut j cap N tt ct c a = (List.replicate (envT j cap N tt ct ct[w].1)
      (vra_blkRows (rowsFlat j cap N tt) O V (vra_Rf j cap N tt ct c a) (rowsT j cap N tt ct[w].2).length)).flatten := by
  have ht : ct[w].2 ≤ tt.length := (hwf w hw).2
  have hty : varTy ct c a = some ct[w].2 := by
    rw [varTy_walk hwf a c hc, h]; simp [List.getElem?_eq_getElem hw]
  unfold vra_varOut
  rw [vra_varVecT_eq hwf a c hc, if_neg (by omega), hty, Option.getD_some, h, vra_flatMap_rep_map]
  have hup : upCtx ct (w + 1) = ct[w].1 := by simp [upCtx, List.getElem?_eq_getElem hw]
  have hfac : vra_fac j cap N tt ct (w + 1) = (rowsT j cap N tt ct[w].2).length := by
    simp [vra_fac, List.getElem?_eq_getElem hw]
  simp only [vra_base, hup, hfac]
  rw [vra_replicate_map_flatten]
  congr 2
  unfold vra_blkRows
  congr 1
  refine List.map_congr_left (fun k hk => ?_)
  have hk' : k < (rowsT j cap N tt ct[w].2).length := List.mem_range.1 hk
  congr 2
  have hs := vra_rowsFlat_slice j cap N tt ht hk'
  rw [vra_get_of_some hO, vra_get_of_some hV] at hs
  rw [hs, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']; rfl

end VarOut

/-! ## The variable item -/

/-- **The variable item**: nothing if the context has no environments; otherwise walk up to the binder and copy its
rows. -/
def itemVarP : NProg NK :=
  vra_readCtxP ENVT vra_NN (by decide) (by decide) ;;
  .ite vra_NN .zero (.prim (.pop vra_NN) ;; .prim (.pushZ EVL))
    (.prim (.pop vra_NN) ;; vra_varWalkP ;;
      .ite vra_CC .zero (.prim (.pop vra_CC) ;; .prim (.pop vra_RR) ;; .prim (.pushZ EVL)) vra_varEndP)

theorem vra_endCost_le {Z nct ntt E R V C nr : Nat} (h1 : nct ≤ Z) (h2 : ntt ≤ Z) (hECR : E * C * R ≤ Z)
    (hEC : E * C ≤ Z) (hE : E ≤ Z) (hV : V ≤ Z) (hr : nr ≤ Z) (hZ : 2 ≤ Z) :
    vra_endCost nct ntt E R V C nr ≤ 200 * (Z * Z) := by
  unfold vra_endCost vra_outerCost vra_midCost vra_inCost vra_sliceCost
  have e : E * (C * (R * (2 + (30 * nr + 20) + 2) + 3 * V + 6 + 2) + 5 + 2) =
      E * C * R * (30 * nr + 24) + E * C * (3 * V + 8) + 7 * E := by
    rw [show 2 + (30 * nr + 20) + 2 = 30 * nr + 24 by omega]
    rw [show R * (30 * nr + 24) + 3 * V + 6 + 2 = R * (30 * nr + 24) + (3 * V + 8) by omega]
    rw [show C * (R * (30 * nr + 24) + (3 * V + 8)) + 5 + 2 = C * (R * (30 * nr + 24) + (3 * V + 8)) + 7 by omega]
    generalize 30 * nr + 24 = X
    generalize 3 * V + 8 = Y
    simp only [Nat.mul_add, Nat.mul_assoc]; omega
  rw [e]
  have k₁ : E * C * R * (30 * nr + 24) ≤ Z * (30 * Z + 24) := Nat.mul_le_mul hECR (by omega)
  have k₂ : E * C * (3 * V + 8) ≤ Z * (3 * Z + 8) := Nat.mul_le_mul hEC (by omega)
  have k₃ : Z * (30 * Z + 24) = 30 * (Z * Z) + 24 * Z := by simp only [Nat.mul_add, Nat.mul_left_comm Z 30]; omega
  have k₄ : Z * (3 * Z + 8) = 3 * (Z * Z) + 8 * Z := by simp only [Nat.mul_add, Nat.mul_left_comm Z 3]; omega
  have k₅ : 2 * Z ≤ Z * Z := Nat.mul_le_mul_right _ hZ
  omega

theorem vra_walkCost_le {Z nct ntt a n Bc : Nat} (h1 : nct ≤ Z) (h2 : ntt ≤ Z) (ha : a ≤ Z) (hn : n ≤ Z)
    (hc : Bc ≤ Z) (hZ : 2 ≤ Z) :
    1 + (5 * 1 + 31) + 2 + (a * (vra_walkRound nct ntt n Bc + 1) + 1) + 1 ≤ 200 * (Z * Z) := by
  unfold vra_walkRound
  have k₁ : a * (46 * nct + 10 * ntt + 3 * n + 6 * Bc + 70 + 1) ≤ Z * (136 * Z) :=
    Nat.mul_le_mul ha (by omega)
  have k₂ : Z * (136 * Z) = 136 * (Z * Z) := by rw [Nat.mul_left_comm]
  have k₅ : 2 * Z ≤ Z * Z := Nat.mul_le_mul_right _ hZ
  omega

theorem itemVarP_runs (j cap : Nat) (st : PSt) (Tf : List (List Nat)) (it : MItem) (htag : it.tag = 9)
    (hc : CTWF st.tt st.ct) (hcur : it.ctx ≤ st.ct.length) : ItemRuns itemVarP j cap st Tf it := by
  intro S vs hE hIT hEV hEVL
  rw [vra_stepT_var j cap st Tf it htag vs, evFlat_cons, evLens_cons]
  have sc := hE.scratch
  have hA := vra_scr sc vra_A; have hB := vra_scr sc vra_B; have hD := vra_scr sc vra_D
  have hEm := vra_scr sc vra_E; have hT := vra_scr sc vra_T; have hNN := vra_scr sc vra_NN
  have hO1 := vra_scr sc vra_O1; have hL1 := vra_scr sc vra_L1; have hCC := vra_scr sc vra_CC
  have hII := vra_scr sc vra_II; have hRR := vra_scr sc vra_RR; have hTT := vra_scr sc vra_TT
  have hPP := vra_scr sc vra_PP; have hCN := vra_scr sc vra_CN
  -- the sizes
  have hZ : st.ct.length + it.ctx + it.a + st.tt.length + (rowsFlat j cap st.x.length st.tt).length +
      (envTable j cap st.x.length st.tt st.ct).sum + (cntTable j cap st.x.length st.tt).sum +
      (valTable j cap st.x.length st.tt).sum + 2 ≤ itemZ j cap st Tf it vs := by
    unfold itemZ; omega
  have hn := vra_envT_le_sum j cap st.x.length st.tt st.ct it.ctx hcur
  -- the number of environments
  have hkE : it.ctx < (S ENVT).length := by rw [hE.envt]; simp [envTable]; omega
  have x₁ := vra_readCtx (tbl := ENVT) (o := vra_NN) (by decide) (by decide) (by decide) S hIT hT hkE
  have hv₁ : (S ENVT)[it.ctx]'hkE = envT j cap st.x.length st.tt st.ct it.ctx := by
    simp only [hE.envt]; exact vra_envT_entry _ _ _ _ _ _ hcur
  have hlE : (S ENVT).length = st.ct.length + 1 := by rw [hE.envt]; simp [envTable]
  rw [hv₁, hNN, List.nil_append, hlE] at x₁
  obtain ⟨n, hnd⟩ : ∃ n, envT j cap st.x.length st.tt st.ct it.ctx = n := ⟨_, rfl⟩
  rw [hnd] at x₁ hn
  have hpop : NRuns (.prim (.pop vra_NN)) (S.set vra_NN [n]) S 1 := by
    have := nruns_pop vra_NN (S.set vra_NN [n]) (l := []) (v := n) (by simp)
    rwa [show (S.set vra_NN [n]).set vra_NN [] = S by vra_ext [vra_NN] [hNN]] at this
  -- the empty vector
  have hempty : (S.set EV (evFlat vs ++ [])).set EVL (evLens vs ++ [([] : List Nat).length]) =
      S.set EVL (S EVL ++ [0]) := by
    rw [← hEV, ← hEVL]; simp only [List.append_nil, List.length_nil]
    vra_ext [EV, EVL] []
  have hcost₀ : 6 * (st.ct.length + 1) + 4 * it.ctx + 7 ≤ 20 * itemZ j cap st Tf it vs := by omega
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- no environments
    subst hn0
    rw [vra_varOut_env0 hc hcur hnd, hempty]
    have y := (hpop.seq (nruns_pushZ EVL S)).iteT (i := vra_NN) (c := .zero)
      (q := .prim (.pop vra_NN) ;; vra_varWalkP ;;
        .ite vra_CC .zero (.prim (.pop vra_CC) ;; .prim (.pop vra_RR) ;; .prim (.pushZ EVL)) vra_varEndP)
      (by simp; rfl)
    refine (x₁.seq y).mono (vra_le_itemCost ?_)
    have : itemZ j cap st Tf it vs ≤ itemZ j cap st Tf it vs * itemZ j cap st Tf it vs :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  · -- walk up
    have hBn : ∀ m, m < it.a → vra_Rf j cap st.x.length st.tt st.ct it.ctx (m + 1) ≤ n := by
      intro m _
      have e := vra_envT_walk (j := j) (cap := cap) (N := st.x.length) hc (m + 1) it.ctx hcur
      rw [hnd] at e
      have : 0 < envT j cap st.x.length st.tt st.ct (walkCtx st.ct it.ctx (m + 1)) := by
        rcases Nat.eq_zero_or_pos (envT j cap st.x.length st.tt st.ct (walkCtx st.ct it.ctx (m + 1))) with h | h
        · rw [h, Nat.mul_zero] at e; omega
        · exact h
      calc vra_Rf j cap st.x.length st.tt st.ct it.ctx (m + 1)
          ≤ vra_Rf j cap st.x.length st.tt st.ct it.ctx (m + 1) *
              envT j cap st.x.length st.tt st.ct (walkCtx st.ct it.ctx (m + 1)) := Nat.le_mul_of_pos_right _ this
        _ = n := e.symm
    have x₂ := vra_walk_runs S hc hE.ct hE.cnt hIT hT hCC hII hRR hcur n hBn
    have hwc := vra_walkCost_le (Z := itemZ j cap st Tf it vs) (nct := st.ct.length) (ntt := st.tt.length)
      (a := it.a) (n := n) (Bc := (cntTable j cap st.x.length st.tt).sum) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
    obtain ⟨R, hRd⟩ : ∃ R, vra_Rf j cap st.x.length st.tt st.ct it.ctx it.a = R := ⟨_, rfl⟩
    rw [hRd] at x₂
    have hwl := walkCtx_le hc it.ctx hcur it.a
    rcases hwk : walkCtx st.ct it.ctx it.a with _ | w
    · -- the walk ran out
      rw [hwk] at x₂
      rw [vra_varOut_walk0 hc hcur hwk, hempty]
      have y₁ := nruns_pop vra_CC ((S.set vra_CC [0]).set vra_RR [R]) (l := []) (v := 0) (by simp [Lists.set])
      have y₂ := nruns_pop vra_RR (((S.set vra_CC [0]).set vra_RR [R]).set vra_CC []) (l := []) (v := R)
        (by simp [Lists.set])
      have e : ((((S.set vra_CC [0]).set vra_RR [R]).set vra_CC []).set vra_RR []) = S := by
        vra_ext [vra_CC, vra_RR] [hCC, hRR]
      rw [e] at y₂
      have y := (y₁.seq (y₂.seq (nruns_pushZ EVL S))).iteT (i := vra_CC) (c := .zero) (q := vra_varEndP)
        (by simp; rfl)
      have z := (hpop.seq (x₂.seq y)).iteF (i := vra_NN) (c := .zero) (p := .prim (.pop vra_NN) ;; .prim (.pushZ EVL))
        (by simp; rw [show n = (n - 1) + 1 by omega]; rfl)
      refine (x₁.seq z).mono (vra_le_itemCost ?_)
      have : itemZ j cap st Tf it vs ≤ itemZ j cap st Tf it vs * itemZ j cap st Tf it vs :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
    · -- the binder at the end of the walk
      have hwlt : w < st.ct.length := by omega
      have ht : st.ct[w].2 ≤ st.tt.length := (hc w hwlt).2
      have hlO : st.ct[w].2 < (roffTable j cap st.x.length st.tt).length := by
        simp [roffTable, typeTable]; omega
      have hlV : st.ct[w].2 < (valTable j cap st.x.length st.tt).length := by
        simp [valTable, typeTable]; omega
      obtain ⟨O, hO⟩ : ∃ O, (roffTable j cap st.x.length st.tt)[st.ct[w].2]? = some O :=
        ⟨_, List.getElem?_eq_getElem hlO⟩
      obtain ⟨V, hV⟩ : ∃ V, (valTable j cap st.x.length st.tt)[st.ct[w].2]? = some V :=
        ⟨_, List.getElem?_eq_getElem hlV⟩
      rw [hwk] at x₂
      have y := vra_varEnd_runs ((S.set vra_CC [w + 1]).set vra_RR [R]) hc (by simp [Lists.set, hE.ct])
        (by simp [Lists.set, hE.envt]) (by simp [Lists.set, hE.cnt]) (by simp [Lists.set, hE.valt])
        (by simp [Lists.set, hE.roff]) (by simp [Lists.set, hE.rows]) (by simp [Lists.set, hT])
        (by simp [Lists.set, hA]) (by simp [Lists.set, hB]) (by simp [Lists.set, hD]) (by simp [Lists.set, hEm])
        (by simp [Lists.set, hO1]) (by simp [Lists.set, hL1]) (by simp [Lists.set, hTT]) (by simp [Lists.set, hPP])
        (by simp [Lists.set, hCN]) (R := R) hwlt (by simp [Lists.set]) (by simp [Lists.set]) hO hV
      rw [vra_varOut_end hc hcur hwk hwlt hO hV, hRd]
      have e : (((((S.set vra_CC [w + 1]).set vra_RR [R]).set vra_CC []).set vra_RR []).set EV
          (((S.set vra_CC [w + 1]).set vra_RR [R]) EV ++ (List.replicate (envT j cap st.x.length st.tt st.ct st.ct[w].1)
            (vra_blkRows (rowsFlat j cap st.x.length st.tt) O V R
              (rowsT j cap st.x.length st.tt st.ct[w].2).length)).flatten)).set EVL
          (((S.set vra_CC [w + 1]).set vra_RR [R]) EVL ++ [envT j cap st.x.length st.tt st.ct st.ct[w].1 *
            (vra_blkRows (rowsFlat j cap st.x.length st.tt) O V R
              (rowsT j cap st.x.length st.tt st.ct[w].2).length).length]) =
          (S.set EV (evFlat vs ++ (List.replicate (envT j cap st.x.length st.tt st.ct st.ct[w].1)
            (vra_blkRows (rowsFlat j cap st.x.length st.tt) O V R
              (rowsT j cap st.x.length st.tt st.ct[w].2).length)).flatten)).set EVL
          (evLens vs ++ [(List.replicate (envT j cap st.x.length st.tt st.ct st.ct[w].1)
            (vra_blkRows (rowsFlat j cap st.x.length st.tt) O V R
              (rowsT j cap st.x.length st.tt st.ct[w].2).length)).flatten.length]) := by
        rw [vra_flatten_replicate_length, ← hEV, ← hEVL]
        vra_ext [vra_CC, vra_RR, EV, EVL] [hCC, hRR]
      rw [e] at y
      have yy := y.iteF (i := vra_CC) (c := .zero) (p := .prim (.pop vra_CC) ;; .prim (.pop vra_RR) ;;
        .prim (.pushZ EVL)) (by simp; rfl)
      have z := (hpop.seq (x₂.seq yy)).iteF (i := vra_NN) (c := .zero) (p := .prim (.pop vra_NN) ;; .prim (.pushZ EVL))
        (by simp; rw [show n = (n - 1) + 1 by omega]; rfl)
      refine (x₁.seq z).mono (vra_le_itemCost ?_)
      -- the sizes at the binder
      have hfac := vra_envT_up (j := j) (cap := cap) (N := st.x.length) hc (w + 1) (by omega)
      have hwalk := vra_envT_walk (j := j) (cap := cap) (N := st.x.length) hc it.a it.ctx hcur
      rw [hwk, hRd, hnd, hfac] at hwalk
      have hup : upCtx st.ct (w + 1) = st.ct[w].1 := by simp [upCtx, List.getElem?_eq_getElem hwlt]
      rw [hup, vra_fac_le j cap st.x.length hwlt] at hwalk
      obtain ⟨E, hEd⟩ : ∃ E, envT j cap st.x.length st.tt st.ct st.ct[w].1 = E := ⟨_, rfl⟩
      obtain ⟨C, hCd⟩ : ∃ C, (rowsT j cap st.x.length st.tt st.ct[w].2).length = C := ⟨_, rfl⟩
      rw [hEd, hCd] at hwalk ⊢
      have hECR : E * C * R ≤ itemZ j cap st Tf it vs := by
        have : E * C * R = n := by rw [hwalk, Nat.mul_comm (E * C) R, Nat.mul_comm E C]
        omega
      have hR1 : 1 ≤ R := by
        rcases Nat.eq_zero_or_pos R with h | h
        · rw [h, Nat.zero_mul] at hwalk; omega
        · exact h
      have hEC : E * C ≤ itemZ j cap st Tf it vs := Nat.le_trans (Nat.le_mul_of_pos_right _ hR1) hECR
      have hEC1 : E ≤ itemZ j cap st Tf it vs := by
        have hC1 : 1 ≤ C := by
          rcases Nat.eq_zero_or_pos C with h | h
          · rw [h, Nat.zero_mul, Nat.mul_zero] at hwalk; omega
          · exact h
        exact Nat.le_trans (Nat.le_mul_of_pos_right _ hC1) hEC
      have hVZ : V ≤ itemZ j cap st Tf it vs := by
        have := vra_le_sum (List.mem_of_getElem? hV); omega
      have hec := vra_endCost_le (Z := itemZ j cap st Tf it vs) (nct := st.ct.length) (ntt := st.tt.length)
        (nr := (rowsFlat j cap st.x.length st.tt).length) (by omega) (by omega) hECR hEC hEC1 hVZ (by omega) (by omega)
      have : itemZ j cap st Tf it vs ≤ itemZ j cap st Tf it vs * itemZ j cap st Tf it vs :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega

/-! ## The application item: what it computes -/

theorem vra_chunksN_eq {α : Type} (k : Nat) : ∀ (n : Nat) (l : List α),
    Shallot.MacroPeg.Flat.chunksN k n l = (List.range n).map (fun e => (l.drop (e * k)).take k)
  | 0, _ => rfl
  | n + 1, l => by
    rw [Shallot.MacroPeg.Flat.chunksN, vra_chunksN_eq k n (l.drop k), List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Nat.zero_mul, List.drop_zero, List.cons.injEq, true_and]
    refine List.map_congr_left (fun e _ => ?_)
    simp only [Function.comp_apply, List.drop_drop, Nat.succ_mul]
    rw [Nat.add_comm]

theorem vra_zipWith_map {α β γ δ : Type} (f : α → β → γ) (g : δ → α) (h : δ → β) :
    ∀ l : List δ, List.zipWith f (l.map g) (l.map h) = l.map (fun x => f (g x) (h x))
  | [] => rfl
  | x :: l => by simp only [List.map_cons, List.zipWith_cons_cons, vra_zipWith_map f g h l]

/-- Where the search stands after `k` rows: found (`1`) with the index, or not yet (`0`) with `k`. -/
def vra_srch (yv : List Nat) (rows : List (List Nat)) (k : Nat) : Nat × Nat :=
  if yv ∈ rows.take k then (1, Shallot.MacroPeg.indexIn yv rows) else (0, k)

theorem vra_indexIn_at : ∀ (rows : List (List Nat)) (yv : List Nat) (k : Nat) (hk : k < rows.length),
    yv ∉ rows.take k → rows[k] = yv → Shallot.MacroPeg.indexIn yv rows = k
  | [], _, _, hk, _, _ => absurd hk (by simp)
  | r :: rows, yv, 0, _, _, h => by simp at h; simp [Shallot.MacroPeg.indexIn, h]
  | r :: rows, yv, k + 1, hk, hn, h => by
    have hr : r ≠ yv := fun e => hn (by simp [e])
    simp only [Shallot.MacroPeg.indexIn, hr, if_false]
    rw [vra_indexIn_at rows yv k (by simpa using hk) (fun hm => hn (by simp [hm])) (by simpa using h)]

theorem vra_indexIn_none : ∀ (rows : List (List Nat)) (yv : List Nat), yv ∉ rows →
    Shallot.MacroPeg.indexIn yv rows = rows.length
  | [], _, _ => rfl
  | r :: rows, yv, h => by
    have hr : r ≠ yv := fun e => h (by simp [e])
    simp only [Shallot.MacroPeg.indexIn, hr, if_false]
    rw [vra_indexIn_none rows yv (fun hm => h (by simp [hm]))]; simp

/-- One round of the search. -/
theorem vra_srch_succ (yv : List Nat) (rows : List (List Nat)) (k : Nat) (hk : k < rows.length) :
    vra_srch yv rows (k + 1) = if (vra_srch yv rows k).1 = 0 then
      (if rows[k] = yv then (1, (vra_srch yv rows k).2) else (0, (vra_srch yv rows k).2 + 1))
      else vra_srch yv rows k := by
  have htk : rows.take (k + 1) = rows.take k ++ [rows[k]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hk]; rfl
  unfold vra_srch
  simp only [htk]
  by_cases hm : yv ∈ rows.take k
  · have : yv ∈ rows.take k ++ [rows[k]] := List.mem_append_left _ hm
    simp [hm]
    rw [htk]; exact this
  · simp only [hm, if_false, List.mem_append, List.mem_singleton, false_or, if_true]
    by_cases he : rows[k] = yv
    · subst he
      simp [vra_indexIn_at rows _ k hk hm rfl]
    · have : ¬ yv = rows[k] := fun e => he e.symm
      simp [he, this]

theorem vra_srch_end (yv : List Nat) (rows : List (List Nat)) :
    (vra_srch yv rows rows.length).2 = Shallot.MacroPeg.indexIn yv rows := by
  unfold vra_srch
  rw [List.take_length]
  split
  · rfl
  · rename_i h; rw [vra_indexIn_none rows yv h]

theorem vra_srch_le (yv : List Nat) (rows : List (List Nat)) (k : Nat) (hk : k ≤ rows.length) :
    (vra_srch yv rows k).2 ≤ rows.length := by
  unfold vra_srch
  split
  · rename_i h
    have := Shallot.MacroPeg.getElem?_indexIn yv rows (List.mem_of_mem_take h)
    exact Nat.le_of_lt (List.getElem?_eq_some_iff.1 this).1
  · exact hk

theorem vra_srch_fst (yv : List Nat) (rows : List (List Nat)) (k : Nat) :
    (vra_srch yv rows k).1 = 0 ∨ (vra_srch yv rows k).1 = 1 := by
  unfold vra_srch; split <;> simp

/-- The value of the application item. -/
theorem vra_stepT_app (j cap : Nat) (st : PSt) (Tf : List (List Nat)) (it : MItem) (htag : it.tag = 12)
    (vy vf : List Nat) (rest : List (List Nat)) :
    stepT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt Tf it (vy :: vf :: rest) =
      ((List.range (envT j cap st.x.length st.tt st.ct it.ctx)).map (fun e =>
        Shallot.MacroPeg.Flat.block (valT j cap st.x.length st.tt it.b)
          (Shallot.MacroPeg.indexIn ((vy.drop (e * valT j cap st.x.length st.tt it.a)).take
            (valT j cap st.x.length st.tt it.a)) (rowsT j cap st.x.length st.tt it.a))
          ((vf.drop (e * ((rowsT j cap st.x.length st.tt it.a).length * valT j cap st.x.length st.tt it.b))).take
            ((rowsT j cap st.x.length st.tt it.a).length * valT j cap st.x.length st.tt it.b)))).flatten :: rest := by
  unfold stepT; rw [htag]
  simp only [List.length_map]
  rw [vra_chunksN_eq, vra_chunksN_eq, vra_zipWith_map]

theorem vra_stepT_app_short (j cap : Nat) (st : PSt) (Tf : List (List Nat)) (it : MItem) (htag : it.tag = 12)
    (vs : List (List Nat)) (h : vs.length < 2) :
    stepT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt Tf it vs = vs := by
  have hop : ∀ e, opOf st.tt st.lt it ≠ some (.leaf e) := by
    intro e; unfold opOf; rw [htag]; simp only []; split <;> simp
  unfold stepT; rw [htag]
  rcases vs with _ | ⟨v, _ | ⟨w, vs⟩⟩
  · simp only []
  · simp only []
  · exact absurd h (by simp)

/-! ## The application item: comparing rows -/

/-! Stacks of the application item. -/
abbrev vra_aYV : Fin NK := 23
abbrev vra_aFV : Fin NK := 24
abbrev vra_aOY : Fin NK := 27
abbrev vra_aOF : Fin NK := 28
abbrev vra_aKC : Fin NK := 29
abbrev vra_aFD : Fin NK := 6
abbrev vra_aOR : Fin NK := 10
abbrev vra_aCK : Fin NK := 11
abbrev vra_aCTR : Fin NK := 12
abbrev vra_aG : Fin NK := 16
abbrev vra_aW : Fin NK := 8
abbrev vra_aU : Fin NK := 9
abbrev vra_aVA : Fin NK := 13
abbrev vra_aCA : Fin NK := 1
abbrev vra_aVB : Fin NK := 34
abbrev vra_aLF : Fin NK := 35
abbrev vra_aRA : Fin NK := 39
abbrev vra_aK2 : Fin NK := 15

attribute [local simp] vra_aYV vra_aFV vra_aOY vra_aOF vra_aKC vra_aFD vra_aOR vra_aCK vra_aCTR vra_aG vra_aW vra_aU
  vra_aVA vra_aCA vra_aVB vra_aLF vra_aRA vra_aK2

/-- Copy the slice of `src` at the offset on top of `offS`, of the length on top of `lenS`, onto `dst`. -/
def vra_cpP (src dst offS lenS : Fin NK) (h : VraS src dst vra_aCTR vra_O1 vra_L1 vra_A vra_B vra_D vra_E)
    (h₁ : offS ≠ vra_O1) (h₂ : lenS ≠ vra_L1) : NProg NK :=
  .prim (.dup offS vra_O1 h₁) ;; .prim (.dup lenS vra_L1 h₂) ;; .prim (.pushZ vra_aCTR) ;;
  vra_sliceP src dst vra_aCTR vra_O1 vra_L1 vra_A vra_B vra_D vra_E h ;; .prim (.pop vra_aCTR)

theorem vra_cp_runs {src dst offS lenS : Fin NK} (h : VraS src dst vra_aCTR vra_O1 vra_L1 vra_A vra_B vra_D vra_E)
    (h₁ : offS ≠ vra_O1) (h₂ : lenS ≠ vra_L1)
    (hd : [src, dst, offS, lenS, vra_aCTR, vra_O1, vra_L1, vra_A, vra_B, vra_D, vra_E].Nodup)
    (St : Lists NK) {lo ll : List Nat} {o len : Nat} (ho : St offS = lo ++ [o]) (hl : St lenS = ll ++ [len])
    (hA : St vra_A = []) (hB : St vra_B = []) (hD : St vra_D = []) (hE : St vra_E = []) (hO1 : St vra_O1 = [])
    (hL1 : St vra_L1 = []) (hdst : St dst = []) :
    NRuns (vra_cpP src dst offS lenS h h₁ h₂) St (St.set dst (((St src).drop o).take len))
      (vra_sliceCost (St src).length + 4) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd
  obtain ⟨⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩,
    ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩, ⟨g1, g2, g3, g4, g5, g6, g7⟩, -⟩ := hd
  simp only [vra_aCTR, vra_O1, vra_L1, vra_A, vra_B, vra_D, vra_E] at d1 d2 d3 d4 d5 d6 d7 d8 d9 d10
  simp only [vra_aCTR, vra_O1, vra_L1, vra_A, vra_B, vra_D, vra_E] at e1 e2 e3 e4 e5 e6 e7 e8 e9 f1 f2 f3 f4
  simp only [vra_aCTR, vra_O1, vra_L1, vra_A, vra_B, vra_D, vra_E] at f5 f6 f7 f8 g1 g2 g3 g4 g5 g6 g7
  simp only [vra_aCTR, vra_O1, vra_L1, vra_A, vra_B, vra_D, vra_E] at hA hB hD hE hO1 hL1
  have x₁ := nruns_dup offS vra_O1 h₁ St ho
  rw [hO1, List.nil_append] at x₁
  have x₂ := nruns_dup lenS vra_L1 h₂ (St.set vra_O1 [o]) (l := ll) (v := len) (by simp [Lists.set, g2, hl])
  rw [show (St.set vra_O1 [o]) vra_L1 = [] by simp [Lists.set, hL1], List.nil_append] at x₂
  have x₃ := nruns_pushZ vra_aCTR ((St.set vra_O1 [o]).set vra_L1 [len])
  have x₄ := vra_slice h (((St.set vra_O1 [o]).set vra_L1 [len]).set vra_aCTR
    (((St.set vra_O1 [o]).set vra_L1 [len]) vra_aCTR ++ [0])) (lo := []) (ll := []) (lr := St vra_aCTR) (off := o)
    (len := len) (v := 0) (by simp [Lists.set, hA]) (by simp [Lists.set, hB]) (by simp [Lists.set, hD])
    (by simp [Lists.set, hE]) (by simp [Lists.set]) (by simp [Lists.set]) (by simp [Lists.set])
  have hsrc : (((St.set vra_O1 [o]).set vra_L1 [len]).set vra_aCTR
      (((St.set vra_O1 [o]).set vra_L1 [len]) vra_aCTR ++ [0])) src = St src := by
    simp [Lists.set, d4, d5, d6]
  have hdst' : (((St.set vra_O1 [o]).set vra_L1 [len]).set vra_aCTR
      (((St.set vra_O1 [o]).set vra_L1 [len]) vra_aCTR ++ [0])) dst = [] := by
    simp [Lists.set, e3, e4, e5, hdst]
  rw [hsrc, hdst', List.nil_append] at x₄
  have x₅ := nruns_pop vra_aCTR (((((((St.set vra_O1 [o]).set vra_L1 [len]).set vra_aCTR
      (((St.set vra_O1 [o]).set vra_L1 [len]) vra_aCTR ++ [0])).set vra_O1 []).set vra_L1 []).set dst
        (((St src).drop o).take len)).set vra_aCTR (St vra_aCTR ++ [0 + (((St src).drop o).take len).length]))
    (l := St vra_aCTR) (v := 0 + (((St src).drop o).take len).length) (by simp)
  have e : ((((((((St.set vra_O1 [o]).set vra_L1 [len]).set vra_aCTR
      (((St.set vra_O1 [o]).set vra_L1 [len]) vra_aCTR ++ [0])).set vra_O1 []).set vra_L1 []).set dst
        (((St src).drop o).take len)).set vra_aCTR (St vra_aCTR ++ [0 + (((St src).drop o).take len).length])).set
          vra_aCTR (St vra_aCTR)) = St.set dst (((St src).drop o).take len) := by
    vra_ext [vra_O1, vra_L1, vra_aCTR, dst] [e3, e4, e5, Ne.symm e3, Ne.symm e4, Ne.symm e5, hO1, hL1]
  rw [e] at x₅
  exact (x₁.seq (x₂.seq (x₃.seq (x₄.seq x₅)))).mono (by omega)

/-- Compare the row at offset `OR` with the argument block at offset `OY` (both of length `VA`): on a match raise
`FD`, otherwise count `KC` up. -/
def vra_appCmpP : NProg NK :=
  vra_cpP ROWS vra_P vra_aOR vra_aVA ⟨by decide⟩ (by decide) (by decide) ;;
  vra_cpP vra_aYV vra_Q vra_aOY vra_aVA ⟨by decide⟩ (by decide) (by decide) ;;
  vra_eqP vra_P vra_Q vra_aG vra_A vra_B vra_D vra_E ⟨by decide⟩ ;;
  .ite vra_aG .zero (.prim (.inc vra_aKC)) (.prim (.inc vra_aFD)) ;; .prim (.pop vra_aG)

theorem vra_eqCost_mono {M p q p' q' : Nat} (hp : p ≤ p') (hq : q ≤ q') : vra_eqCost M p q ≤ vra_eqCost M p' q' := by
  unfold vra_eqCost
  have := Nat.mul_le_mul (show p + 1 ≤ p' + 1 by omega)
    (show vra_eqRound M + 2 * p + 8 ≤ vra_eqRound M + 2 * p' + 8 by omega)
  omega

/-- The cost of a comparison of blocks of length `Va`. -/
def vra_cmpCost (nr ny M Va : Nat) : Nat := vra_sliceCost nr + vra_sliceCost ny + 8 + vra_eqCost M Va Va + 5

theorem vra_appCmp_runs (St : Lists NK) {rows vy lO lY lV lF lK : List Nat} {r oy Va kc M : Nat}
    (hrows : St ROWS = rows) (hyv : St vra_aYV = vy) (hOR : St vra_aOR = lO ++ [r]) (hOY : St vra_aOY = lY ++ [oy])
    (hVA : St vra_aVA = lV ++ [Va]) (hFD : St vra_aFD = lF ++ [0]) (hKC : St vra_aKC = lK ++ [kc])
    (hA : St vra_A = []) (hB : St vra_B = []) (hD : St vra_D = []) (hE : St vra_E = []) (hO1 : St vra_O1 = [])
    (hL1 : St vra_L1 = []) (hP : St vra_P = []) (hQ : St vra_Q = []) (hMr : ∀ x ∈ rows, x ≤ M)
    (hMy : ∀ x ∈ vy, x ≤ M) :
    NRuns vra_appCmpP St (if (rows.drop r).take Va = (vy.drop oy).take Va then St.set vra_aFD (lF ++ [1])
      else St.set vra_aKC (lK ++ [kc + 1])) (vra_cmpCost rows.length vy.length M Va) := by
  have x₁ := vra_cp_runs (src := ROWS) (dst := vra_P) (offS := vra_aOR) (lenS := vra_aVA) ⟨by decide⟩ (by decide)
    (by decide) (by decide) St hOR hVA hA hB hD hE hO1 hL1 hP
  rw [hrows] at x₁
  let row := (rows.drop r).take Va
  let S₁ := St.set vra_P row
  have x₂ := vra_cp_runs (src := vra_aYV) (dst := vra_Q) (offS := vra_aOY) (lenS := vra_aVA) ⟨by decide⟩
    (by decide) (by decide) (by decide) S₁ (lo := lY) (ll := lV) (o := oy) (len := Va) (by simp [S₁, Lists.set, hOY])
    (by simp [S₁, Lists.set, hVA]) (by simp [S₁, Lists.set, hA]) (by simp [S₁, Lists.set, hB])
    (by simp [S₁, Lists.set, hD]) (by simp [S₁, Lists.set, hE]) (by simp [S₁, Lists.set, hO1])
    (by simp [S₁, Lists.set, hL1]) (by simp [S₁, Lists.set, hQ])
  have hy₁ : S₁ vra_aYV = vy := by simp [S₁, Lists.set, hyv]
  rw [hy₁] at x₂
  let yvv := (vy.drop oy).take Va
  let S₂ := S₁.set vra_Q yvv
  have hPm : ∀ x ∈ S₂ vra_P, x ≤ M := by
    intro x hx
    simp only [S₂, S₁, Lists.set_ne _ _ (show vra_P ≠ vra_Q by decide), Lists.set_same] at hx
    exact hMr x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  have hQm : ∀ x ∈ S₂ vra_Q, x ≤ M := by
    intro x hx
    simp only [S₂, Lists.set_same] at hx
    exact hMy x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  have x₃ := vra_eq (P := vra_P) (Q := vra_Q) (G := vra_aG) (t := vra_A) (u := vra_B) (g := vra_D) (f := vra_E)
    ⟨by decide⟩ M S₂ (lG := S₂ vra_aG) rfl hPm hQm
  have hP2 : S₂ vra_P = row := by simp [S₂, S₁, Lists.set]
  have hQ2 : S₂ vra_Q = yvv := by simp [S₂]
  rw [hP2, hQ2] at x₃
  have hG : S₂ vra_aG = St vra_aG := by simp [S₂, S₁, Lists.set]
  rw [hG] at x₃
  let S₃ := ((S₂.set vra_P []).set vra_Q []).set vra_aG (St vra_aG ++ [if row = yvv then 1 else 0])
  have hS₃ : ∀ b : Nat, ((S₂.set vra_P []).set vra_Q []).set vra_aG (St vra_aG ++ [b]) =
      St.set vra_aG (St vra_aG ++ [b]) := by
    intro b; simp only [S₂, S₁]; vra_ext [vra_P, vra_Q, vra_aG] [hP, hQ]
  by_cases hrow : row = yvv
  · -- a match
    have hif : (if row = yvv then 1 else 0) = 1 := by simp [hrow]
    rw [hif, hS₃] at x₃
    have y₁ := nruns_inc vra_aFD (St.set vra_aG (St vra_aG ++ [1])) (l := lF) (v := 0) (by simp [Lists.set, hFD])
    have y₂ := nruns_pop vra_aG ((St.set vra_aG (St vra_aG ++ [1])).set vra_aFD (lF ++ [0 + 1])) (l := St vra_aG)
      (v := 1) (by simp [Lists.set])
    have e : ((St.set vra_aG (St vra_aG ++ [1])).set vra_aFD (lF ++ [0 + 1])).set vra_aG (St vra_aG) =
        St.set vra_aFD (lF ++ [1]) := by vra_ext [vra_aG, vra_aFD] []
    rw [e] at y₂
    have y := (y₁.iteF (i := vra_aG) (c := .zero) (p := .prim (.inc vra_aKC)) (by simp)).seq y₂
    rw [if_pos hrow]
    refine (x₁.seq (x₂.seq (x₃.seq y))).mono ?_
    have hl₁ : row.length ≤ Va := by simp only [row, List.length_take]; exact Nat.min_le_left _ _
    have hl₂ : yvv.length ≤ Va := by simp only [yvv, List.length_take]; exact Nat.min_le_left _ _
    have := vra_eqCost_mono (M := M) hl₁ hl₂
    have hs : (S₁ vra_aYV).length = vy.length := by rw [hy₁]
    unfold vra_cmpCost; omega
  · -- no match
    have hif : (if row = yvv then 1 else 0) = 0 := by simp [hrow]
    rw [hif, hS₃] at x₃
    have y₁ := nruns_inc vra_aKC (St.set vra_aG (St vra_aG ++ [0])) (l := lK) (v := kc) (by simp [Lists.set, hKC])
    have y₂ := nruns_pop vra_aG ((St.set vra_aG (St vra_aG ++ [0])).set vra_aKC (lK ++ [kc + 1])) (l := St vra_aG)
      (v := 0) (by simp [Lists.set])
    have e : ((St.set vra_aG (St vra_aG ++ [0])).set vra_aKC (lK ++ [kc + 1])).set vra_aG (St vra_aG) =
        St.set vra_aKC (lK ++ [kc + 1]) := by vra_ext [vra_aG, vra_aKC] []
    rw [e] at y₂
    have y := (y₁.iteT (i := vra_aG) (c := .zero) (q := .prim (.inc vra_aFD)) (by simp)).seq y₂
    rw [if_neg hrow]
    refine (x₁.seq (x₂.seq (x₃.seq y))).mono ?_
    have hl₁ : row.length ≤ Va := by simp only [row, List.length_take]; exact Nat.min_le_left _ _
    have hl₂ : yvv.length ≤ Va := by simp only [yvv, List.length_take]; exact Nat.min_le_left _ _
    have := vra_eqCost_mono (M := M) hl₁ hl₂
    unfold vra_cmpCost; omega

/-! ## The application item: the search for the argument's row -/

/-- What stays fixed during a round of the application item. -/
structure VraApp (St : Lists NK) (rows vy vf : List Nat) (Va : Nat) : Prop where
  rows : St ROWS = rows
  yv : St vra_aYV = vy
  fv : St vra_aFV = vf
  va : ∃ l, St vra_aVA = l ++ [Va]
  a : St vra_A = []
  b : St vra_B = []
  d : St vra_D = []
  e : St vra_E = []
  o1 : St vra_O1 = []
  l1 : St vra_L1 = []
  p : St vra_P = []
  q : St vra_Q = []
  t : St vra_T = []

theorem VraApp.set {St : Lists NK} {rows vy vf : List Nat} {Va : Nat} (hc : VraApp St rows vy vf Va) {k : Fin NK}
    (x : List Nat) (h : [k, ROWS, vra_aYV, vra_aFV, vra_aVA, vra_A, vra_B, vra_D, vra_E, vra_O1, vra_L1, vra_P, vra_Q,
      vra_T].Nodup) : VraApp (St.set k x) rows vy vf Va := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at h
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩, -⟩ := h
  obtain ⟨l, hl⟩ := hc.va
  exact ⟨by simp [Lists.set, Ne.symm h1, hc.rows], by simp [Lists.set, Ne.symm h2, hc.yv],
    by simp [Lists.set, Ne.symm h3, hc.fv], ⟨l, by simp [Lists.set, Ne.symm h4, hl]⟩,
    by simp [Lists.set, Ne.symm h5, hc.a], by simp [Lists.set, Ne.symm h6, hc.b], by simp [Lists.set, Ne.symm h7, hc.d],
    by simp [Lists.set, Ne.symm h8, hc.e], by simp [Lists.set, Ne.symm h9, hc.o1],
    by simp [Lists.set, Ne.symm h10, hc.l1], by simp [Lists.set, Ne.symm h11, hc.p],
    by simp [Lists.set, Ne.symm h12, hc.q], by simp [Lists.set, Ne.symm h13, hc.t]⟩

/-- One round of the search: compare row `k` unless found, then move to the next row. -/
def vra_appSearchP : NProg NK :=
  .ite vra_aFD .zero vra_appCmpP (nskip vra_T) ;; .prim (.dup vra_aVA vra_aW (by decide)) ;; addTo vra_aW vra_aOR

/-- The search through the rows `rowsA` (found in `rows` from `RA`, of length `Va`) for the block `yvv`. -/
theorem vra_search_runs (St : Lists NK) {rows vy vf lF lK lO lC : List Nat} {Va RA oy M : Nat}
    {rowsA : List (List Nat)} (hc : VraApp St rows vy vf Va) (hOY : ∃ l, St vra_aOY = l ++ [oy])
    (hrow : ∀ k (hk : k < rowsA.length), (rows.drop (RA + k * Va)).take Va = rowsA[k])
    (hMr : ∀ x ∈ rows, x ≤ M) (hMy : ∀ x ∈ vy, x ≤ M) :
    NRuns (vra_repeatP vra_aCK vra_appSearchP)
      ((((St.set vra_aFD (lF ++ [0])).set vra_aKC (lK ++ [0])).set vra_aOR (lO ++ [RA])).set vra_aCK
        (lC ++ [rowsA.length]))
      ((((St.set vra_aFD (lF ++ [(vra_srch ((vy.drop oy).take Va) rowsA rowsA.length).1])).set vra_aKC
        (lK ++ [(vra_srch ((vy.drop oy).take Va) rowsA rowsA.length).2])).set vra_aOR
          (lO ++ [RA + rowsA.length * Va])).set vra_aCK lC)
      (rowsA.length * (vra_cmpCost rows.length vy.length M Va + 3 * Va + 6 + 2) + 2) := by
  obtain ⟨lV, hV⟩ := hc.va
  obtain ⟨lY, hY⟩ := hOY
  let yvv := (vy.drop oy).take Va
  let G : Nat → Lists NK := fun k => ((St.set vra_aFD (lF ++ [(vra_srch yvv rowsA k).1])).set vra_aKC
    (lK ++ [(vra_srch yvv rowsA k).2])).set vra_aOR (lO ++ [RA + k * Va])
  have hbody : ∀ k, k < rowsA.length → NRuns vra_appSearchP ((G k).set vra_aCK (lC ++ [rowsA.length - k - 1]))
      ((G (k + 1)).set vra_aCK (lC ++ [rowsA.length - k - 1])) (vra_cmpCost rows.length vy.length M Va + 3 * Va + 6) := by
    intro k hk
    let Gk := (G k).set vra_aCK (lC ++ [rowsA.length - k - 1])
    have hGk : VraApp Gk rows vy vf Va :=
      (((hc.set _ (k := vra_aFD) (by decide)).set _ (k := vra_aKC) (by decide)).set _ (k := vra_aOR)
        (by decide)).set _ (by decide)
    have hsucc := vra_srch_succ yvv rowsA k hk
    -- the comparison, or nothing
    have x₁ : NRuns (.ite vra_aFD .zero vra_appCmpP (nskip vra_T)) Gk
        ((((Gk.set vra_aFD (lF ++ [(vra_srch yvv rowsA (k + 1)).1])).set vra_aKC
          (lK ++ [(vra_srch yvv rowsA (k + 1)).2])))) (vra_cmpCost rows.length vy.length M Va + 1) := by
      rcases vra_srch_fst yvv rowsA k with h0 | h1
      · have y := vra_appCmp_runs Gk (rows := rows) (vy := vy) (lO := lO) (r := RA + k * Va) (lY := lY) (oy := oy)
          (lV := lV) (Va := Va) (lF := lF) (lK := lK) (kc := (vra_srch yvv rowsA k).2) (M := M) hGk.rows hGk.yv
          (by simp [Gk, G, Lists.set]) (by simp [Gk, G, Lists.set, hY]) (by simp [Gk, G, Lists.set, hV])
          (by simp [Gk, G, Lists.set, h0]) (by simp [Gk, G, Lists.set]) hGk.a hGk.b hGk.d hGk.e hGk.o1 hGk.l1 hGk.p
          hGk.q hMr hMy
        rw [hrow k hk] at y
        rw [h0, if_pos rfl] at hsucc
        have e : (if rowsA[k] = yvv then Gk.set vra_aFD (lF ++ [1]) else Gk.set vra_aKC
            (lK ++ [(vra_srch yvv rowsA k).2 + 1])) = (Gk.set vra_aFD (lF ++ [(vra_srch yvv rowsA (k + 1)).1])).set
              vra_aKC (lK ++ [(vra_srch yvv rowsA (k + 1)).2]) := by
          rw [hsucc]
          by_cases he : rowsA[k] = yvv
          · simp only [he, if_true]
            simp only [Gk, G]
            vra_ext [vra_aFD, vra_aKC, vra_aOR, vra_aCK] []
          · simp only [he, if_false]
            simp only [Gk, G, h0]
            vra_ext [vra_aFD, vra_aKC, vra_aOR, vra_aCK] []
        rw [e] at y
        exact y.iteT (by simp [Gk, G, Lists.set, h0])
      · have y := nruns_skip vra_T Gk
        rw [h1] at hsucc
        simp only [show (1 : Nat) ≠ 0 by decide, if_false] at hsucc
        have e : Gk = (Gk.set vra_aFD (lF ++ [(vra_srch yvv rowsA (k + 1)).1])).set vra_aKC
            (lK ++ [(vra_srch yvv rowsA (k + 1)).2]) := by
          rw [hsucc]; simp only [Gk, G]
          vra_ext [vra_aFD, vra_aKC, vra_aOR, vra_aCK] []
        rw [← e]
        have := y.iteF (i := vra_aFD) (c := .zero) (p := vra_appCmpP) (by simp [Gk, G, Lists.set, h1])
        exact this.mono (by unfold vra_cmpCost; omega)
    let G₁ := ((Gk.set vra_aFD (lF ++ [(vra_srch yvv rowsA (k + 1)).1])).set vra_aKC
      (lK ++ [(vra_srch yvv rowsA (k + 1)).2]))
    have x₂ := nruns_dup vra_aVA vra_aW (by decide) G₁ (l := lV) (v := Va) (by simp [G₁, Gk, G, Lists.set, hV])
    have x₃ := nruns_addTo vra_aW vra_aOR (by decide) (G₁.set vra_aW (G₁ vra_aW ++ [Va])) (l := G₁ vra_aW) (a := Va)
      (l' := lO) (b := RA + k * Va) (by simp) (by simp [G₁, Gk, G, Lists.set])
    have e : ((G₁.set vra_aW (G₁ vra_aW ++ [Va])).set vra_aW (G₁ vra_aW)).set vra_aOR (lO ++ [RA + k * Va + Va]) =
        (G (k + 1)).set vra_aCK (lC ++ [rowsA.length - k - 1]) := by
      simp only [G₁, Gk, G, Nat.succ_mul, Nat.add_assoc]
      vra_ext [vra_aFD, vra_aKC, vra_aOR, vra_aCK, vra_aW] []
    rw [e] at x₃
    exact (x₁.seq (x₂.seq x₃)).mono (by omega)
  have x := vra_repeat vra_aCK vra_appSearchP G rowsA.length _ lC hbody
  have e₀ : (G 0).set vra_aCK (lC ++ [rowsA.length]) = ((((St.set vra_aFD (lF ++ [0])).set vra_aKC
      (lK ++ [0])).set vra_aOR (lO ++ [RA])).set vra_aCK (lC ++ [rowsA.length])) := by
    simp [G, vra_srch]
  rw [e₀] at x
  exact x

/-! ## The application item: one environment -/

/-- One environment: find the argument's row index `k`, then copy block `k` of the function's table. -/
def vra_appFindP : NProg NK :=
  .prim (.pushZ vra_aKC) ;; .prim (.pushZ vra_aFD) ;; .prim (.dup vra_aRA vra_aOR (by decide)) ;;
  .prim (.dup vra_aCA vra_aCK (by decide)) ;;
  vra_repeatP vra_aCK vra_appSearchP ;;
  .prim (.pop vra_aFD) ;; .prim (.pop vra_aOR)

def vra_appCopyP : NProg NK :=
  vra_cpP vra_aFV vra_P vra_aOF vra_aLF ⟨by decide⟩ (by decide) (by decide) ;;
  nmv vra_aKC vra_O1 (by decide) ;; .prim (.dup vra_aVB vra_aK2 (by decide)) ;;
  vra_mulP vra_O1 vra_aK2 vra_aU vra_aW (by decide) (by decide) ;;
  .prim (.dup vra_aVB vra_L1 (by decide)) ;;
  vra_sliceP vra_P EV EVL vra_O1 vra_L1 vra_A vra_B vra_D vra_E ⟨by decide⟩ ;; nclr vra_P ;;
  .prim (.dup vra_aVA vra_aW (by decide)) ;; addTo vra_aW vra_aOY ;;
  .prim (.dup vra_aLF vra_aW (by decide)) ;; addTo vra_aW vra_aOF

def vra_appRoundP : NProg NK := vra_appFindP ;; vra_appCopyP

/-- The value of one environment. -/
def vra_appOut (rowsA : List (List Nat)) (vy vf : List Nat) (Va Vb Lf oy of : Nat) : List Nat :=
  Shallot.MacroPeg.Flat.block Vb (Shallot.MacroPeg.indexIn ((vy.drop oy).take Va) rowsA) ((vf.drop of).take Lf)

/-- The cost of one environment. -/
def vra_roundCost (nr ny nf M Va Vb Ca Lf : Nat) : Nat :=
  4 + (Ca * (vra_cmpCost nr ny M Va + 3 * Va + 6 + 2) + 2) + 2 + (vra_sliceCost nf + 4) + 2 + 1 +
    (Vb * (3 * Ca + 6) + 6) + 1 + vra_sliceCost nf + (2 * nf + 1) + (3 * Va + 3) + (3 * Lf + 3)

theorem vra_appFind_runs (St : Lists NK) {rows vy vf lCA lRA lY : List Nat}
    {Va RA oy M : Nat} {rowsA : List (List Nat)} (hc : VraApp St rows vy vf Va)
    (hrow : ∀ k (hk : k < rowsA.length), (rows.drop (RA + k * Va)).take Va = rowsA[k])
    (hMr : ∀ x ∈ rows, x ≤ M) (hMy : ∀ x ∈ vy, x ≤ M)
    (hCA : St vra_aCA = lCA ++ [rowsA.length]) (hRA : St vra_aRA = lRA ++ [RA]) (hOY : St vra_aOY = lY ++ [oy])
    (hKC : St vra_aKC = []) :
    NRuns vra_appFindP St (St.set vra_aKC [Shallot.MacroPeg.indexIn ((vy.drop oy).take Va) rowsA])
      (4 + (rowsA.length * (vra_cmpCost rows.length vy.length M Va + 3 * Va + 6 + 2) + 2) + 2) := by
  let yvv := (vy.drop oy).take Va
  have x₁ := nruns_pushZ vra_aKC St
  rw [hKC, List.nil_append] at x₁
  have x₂ := nruns_pushZ vra_aFD (St.set vra_aKC [0])
  have x₃ := nruns_dup vra_aRA vra_aOR (by decide) ((St.set vra_aKC [0]).set vra_aFD
    ((St.set vra_aKC [0]) vra_aFD ++ [0])) (l := lRA) (v := RA) (by simp [Lists.set, hRA])
  let S₃ := (((St.set vra_aKC [0]).set vra_aFD ((St.set vra_aKC [0]) vra_aFD ++ [0])).set vra_aOR
    (((St.set vra_aKC [0]).set vra_aFD ((St.set vra_aKC [0]) vra_aFD ++ [0])) vra_aOR ++ [RA]))
  have x₄ := nruns_dup vra_aCA vra_aCK (by decide) S₃ (l := lCA) (v := rowsA.length) (by simp [S₃, Lists.set, hCA])
  have e₄ : S₃.set vra_aCK (S₃ vra_aCK ++ [rowsA.length]) = ((((St.set vra_aFD (St vra_aFD ++ [0])).set vra_aKC ([] ++ [0])).set
      vra_aOR (St vra_aOR ++ [RA])).set vra_aCK (St vra_aCK ++ [rowsA.length])) := by
    simp only [S₃]; vra_ext [vra_aKC, vra_aFD, vra_aOR, vra_aCK] []
  rw [e₄] at x₄
  have x₅ := vra_search_runs St hc ⟨lY, hOY⟩ hrow hMr hMy (lF := St vra_aFD) (lK := []) (lO := St vra_aOR)
    (lC := St vra_aCK)
  rw [vra_srch_end] at x₅
  obtain ⟨k, hkd⟩ : ∃ k, Shallot.MacroPeg.indexIn yvv rowsA = k := ⟨_, rfl⟩
  rw [hkd] at x₅
  let f := (vra_srch yvv rowsA rowsA.length).1
  let S₅ := ((((St.set vra_aFD (St vra_aFD ++ [f])).set vra_aKC ([] ++ [k])).set vra_aOR
    (St vra_aOR ++ [RA + rowsA.length * Va])).set vra_aCK (St vra_aCK))
  have x₆ := nruns_pop vra_aFD S₅ (l := St vra_aFD) (v := f) (by simp [S₅, Lists.set])
  have x₇ := nruns_pop vra_aOR (S₅.set vra_aFD (St vra_aFD)) (l := St vra_aOR) (v := RA + rowsA.length * Va)
    (by simp [S₅, Lists.set])
  have e₇ : (S₅.set vra_aFD (St vra_aFD)).set vra_aOR (St vra_aOR) = St.set vra_aKC [k] := by
    simp only [S₅]; vra_ext [vra_aKC, vra_aFD, vra_aOR, vra_aCK] [hKC]
  rw [e₇] at x₇
  rw [hkd]
  exact (x₁.seq (x₂.seq (x₃.seq (x₄.seq (x₅.seq (x₆.seq x₇)))))).mono (by omega)

theorem vra_appCopy_runs (St : Lists NK) {rows vy vf lE lVB lLF lY lF : List Nat}
    {Va Vb Lf oy of v k : Nat} (hc : VraApp St rows vy vf Va)
    (hVB : St vra_aVB = lVB ++ [Vb]) (hLF : St vra_aLF = lLF ++ [Lf]) (hOY : St vra_aOY = lY ++ [oy])
    (hOF : St vra_aOF = lF ++ [of]) (hEVL : St EVL = lE ++ [v]) (hKC : St vra_aKC = [k]) :
    NRuns vra_appCopyP St
      (((((St.set vra_aKC []).set EV (St EV ++ (((vf.drop of).take Lf).drop (k * Vb)).take Vb)).set EVL
        (lE ++ [v + ((((vf.drop of).take Lf).drop (k * Vb)).take Vb).length])).set vra_aOY (lY ++ [oy + Va])).set
          vra_aOF (lF ++ [of + Lf]))
      ((vra_sliceCost vf.length + 4) + 2 + 1 + (Vb * (3 * k + 6) + 6) + 1 + vra_sliceCost vf.length +
        (2 * vf.length + 1) + (3 * Va + 3) + (3 * Lf + 3)) := by
  obtain ⟨lV, hV⟩ := hc.va
  have x₈ := vra_cp_runs (src := vra_aFV) (dst := vra_P) (offS := vra_aOF) (lenS := vra_aLF) ⟨by decide⟩ (by decide)
    (by decide) (by decide) St (lo := lF) (ll := lLF) (o := of) (len := Lf)
    (by simp [Lists.set, hOF]) (by simp [Lists.set, hLF]) hc.a hc.b hc.d hc.e hc.o1 hc.l1 hc.p
  rw [hc.fv] at x₈
  let fv := (vf.drop of).take Lf
  let S₈ := St.set vra_P fv
  have x₉ := nruns_mv vra_aKC vra_O1 (by decide) S₈ (l := []) (v := k) (by simp [S₈, Lists.set, hKC])
  have hO8 : S₈ vra_O1 = [] := by simp [S₈, Lists.set, hc.o1]
  rw [hO8, List.nil_append] at x₉
  let S₉ := (S₈.set vra_O1 [k]).set vra_aKC []
  have x₁₀ := nruns_dup vra_aVB vra_aK2 (by decide) S₉ (l := lVB) (v := Vb) (by simp [S₉, S₈, Lists.set, hVB])
  let S₁₀ := S₉.set vra_aK2 (S₉ vra_aK2 ++ [Vb])
  have x₁₁ := vra_mul (R := vra_O1) (Cn := vra_aK2) (U := vra_aU) (W := vra_aW) ⟨by decide, by decide, by decide,
    by decide, by decide, by decide⟩ S₁₀ (lR := []) (lC := S₉ vra_aK2) (r := k) (c := Vb) (by simp [S₁₀, S₉, Lists.set])
    (by simp [S₁₀])
  let S₁₁ := (S₁₀.set vra_O1 [k * Vb]).set vra_aK2 (S₉ vra_aK2)
  have x₁₂ := nruns_dup vra_aVB vra_L1 (by decide) S₁₁ (l := lVB) (v := Vb)
    (by simp [S₁₁, S₁₀, S₉, S₈, Lists.set, hVB])
  have hL11 : S₁₁ vra_L1 = [] := by simp [S₁₁, S₁₀, S₉, S₈, Lists.set, hc.l1]
  rw [hL11, List.nil_append] at x₁₂
  let S₁₂ := S₁₁.set vra_L1 [Vb]
  have x₁₃ := vra_slice (src := vra_P) (dst := EV) (ctr := EVL) (offS := vra_O1) (lenS := vra_L1) (A := vra_A)
    (B := vra_B) (D := vra_D) (E := vra_E) ⟨by decide⟩ S₁₂ (lo := []) (ll := []) (lr := lE) (off := k * Vb) (len := Vb)
    (v := v) (by simp [S₁₂, S₁₁, S₁₀, S₉, S₈, Lists.set, hc.a]) (by simp [S₁₂, S₁₁, S₁₀, S₉, S₈, Lists.set, hc.b])
    (by simp [S₁₂, S₁₁, S₁₀, S₉, S₈, Lists.set, hc.d]) (by simp [S₁₂, S₁₁, S₁₀, S₉, S₈, Lists.set, hc.e])
    (by simp [S₁₂, S₁₁, S₁₀, S₉, S₈, Lists.set]) (by simp [S₁₂]) (by simp [S₁₂, S₁₁, S₁₀, S₉, S₈, Lists.set, hEVL])
  have hP12 : S₁₂ vra_P = fv := by simp [S₁₂, S₁₁, S₁₀, S₉, S₈, Lists.set]
  have hEV12 : S₁₂ EV = St EV := by simp [S₁₂, S₁₁, S₁₀, S₉, S₈, Lists.set]
  rw [hP12, hEV12] at x₁₃
  let out := (fv.drop (k * Vb)).take Vb
  let S₁₃ := ((((S₁₂.set vra_O1 []).set vra_L1 []).set EV (St EV ++ out)).set EVL (lE ++ [v + out.length]))
  have x₁₄ := nruns_clr vra_P S₁₃
  have hP13 : S₁₃ vra_P = fv := by simp [S₁₃, S₁₂, S₁₁, S₁₀, S₉, S₈, Lists.set]
  rw [hP13] at x₁₄
  let S₁₄ := S₁₃.set vra_P []
  have x₁₅ := nruns_dup vra_aVA vra_aW (by decide) S₁₄ (l := lV) (v := Va) (by simp [S₁₄, S₁₃, S₁₂, S₁₁, S₁₀, S₉, S₈,
    Lists.set, hV])
  have x₁₆ := nruns_addTo vra_aW vra_aOY (by decide) (S₁₄.set vra_aW (S₁₄ vra_aW ++ [Va])) (l := S₁₄ vra_aW) (a := Va)
    (l' := lY) (b := oy) (by simp) (by simp [S₁₄, S₁₃, S₁₂, S₁₁, S₁₀, S₉, S₈, Lists.set, hOY])
  let S₁₆ := ((S₁₄.set vra_aW (S₁₄ vra_aW ++ [Va])).set vra_aW (S₁₄ vra_aW)).set vra_aOY (lY ++ [oy + Va])
  have x₁₇ := nruns_dup vra_aLF vra_aW (by decide) S₁₆ (l := lLF) (v := Lf) (by simp [S₁₆, S₁₄, S₁₃, S₁₂, S₁₁, S₁₀, S₉,
    S₈, Lists.set, hLF])
  have x₁₈ := nruns_addTo vra_aW vra_aOF (by decide) (S₁₆.set vra_aW (S₁₆ vra_aW ++ [Lf])) (l := S₁₆ vra_aW) (a := Lf)
    (l' := lF) (b := of) (by simp) (by simp [S₁₆, S₁₄, S₁₃, S₁₂, S₁₁, S₁₀, S₉, S₈, Lists.set, hOF])
  have e : ((S₁₆.set vra_aW (S₁₆ vra_aW ++ [Lf])).set vra_aW (S₁₆ vra_aW)).set vra_aOF (lF ++ [of + Lf]) =
      ((((St.set vra_aKC []).set EV (St EV ++ out)).set EVL (lE ++ [v + out.length])).set vra_aOY
        (lY ++ [oy + Va])).set vra_aOF (lF ++ [of + Lf]) := by
    simp only [S₁₆, S₁₄, S₁₃, S₁₂, S₁₁, S₁₀, S₉, S₈]
    vra_ext [vra_aKC, vra_P, vra_O1, vra_L1, vra_aK2, vra_aW, vra_aOY, vra_aOF, EV, EVL] [hc.p, hc.o1, hc.l1]
  rw [e] at x₁₈
  refine (x₈.seq (x₉.seq (x₁₀.seq (x₁₁.seq (x₁₂.seq (x₁₃.seq (x₁₄.seq (x₁₅.seq (x₁₆.seq (x₁₇.seq
    x₁₈)))))))))).mono ?_
  have hfv : fv.length ≤ vf.length := by simp only [fv, List.length_take, List.length_drop]; omega
  have hsf : vra_sliceCost fv.length ≤ vra_sliceCost vf.length := by unfold vra_sliceCost; omega
  have hs₈ : (St vra_aFV).length = vf.length := by rw [hc.fv]
  unfold vra_sliceCost at hsf ⊢
  omega

theorem vra_appRound_runs (St : Lists NK) {rows vy vf lE lCA lRA lVB lLF lY lF : List Nat}
    {Va Vb Lf RA oy of v M : Nat} {rowsA : List (List Nat)} (hc : VraApp St rows vy vf Va)
    (hrow : ∀ k (hk : k < rowsA.length), (rows.drop (RA + k * Va)).take Va = rowsA[k])
    (hMr : ∀ x ∈ rows, x ≤ M) (hMy : ∀ x ∈ vy, x ≤ M)
    (hCA : St vra_aCA = lCA ++ [rowsA.length]) (hRA : St vra_aRA = lRA ++ [RA]) (hVB : St vra_aVB = lVB ++ [Vb])
    (hLF : St vra_aLF = lLF ++ [Lf]) (hOY : St vra_aOY = lY ++ [oy]) (hOF : St vra_aOF = lF ++ [of])
    (hEVL : St EVL = lE ++ [v]) (hKC : St vra_aKC = []) :
    NRuns vra_appRoundP St ((((St.set EV (St EV ++ vra_appOut rowsA vy vf Va Vb Lf oy of)).set EVL
      (lE ++ [v + (vra_appOut rowsA vy vf Va Vb Lf oy of).length])).set vra_aOY (lY ++ [oy + Va])).set vra_aOF
        (lF ++ [of + Lf])) (vra_roundCost rows.length vy.length vf.length M Va Vb rowsA.length Lf) := by
  have x₁ := vra_appFind_runs St hc hrow hMr hMy hCA hRA hOY hKC
  obtain ⟨k, hkd⟩ : ∃ k, Shallot.MacroPeg.indexIn ((vy.drop oy).take Va) rowsA = k := ⟨_, rfl⟩
  rw [hkd] at x₁
  have hc₁ : VraApp (St.set vra_aKC [k]) rows vy vf Va := hc.set _ (by decide)
  have x₂ := vra_appCopy_runs (St.set vra_aKC [k]) hc₁ (Lf := Lf) (Vb := Vb) (oy := oy) (of := of) (k := k) (lVB := lVB) (lLF := lLF) (lY := lY) (lF := lF)
    (lE := lE) (v := v) (by simp [Lists.set, hVB]) (by simp [Lists.set, hLF]) (by simp [Lists.set, hOY])
    (by simp [Lists.set, hOF]) (by simp [Lists.set, hEVL]) (by simp)
  have hout : (((vf.drop of).take Lf).drop (k * Vb)).take Vb = vra_appOut rowsA vy vf Va Vb Lf oy of := by
    simp only [vra_appOut, Shallot.MacroPeg.Flat.block, hkd]
  rw [hout] at x₂
  have e : ((((((St.set vra_aKC [k]).set vra_aKC []).set EV ((St.set vra_aKC [k]) EV ++
      vra_appOut rowsA vy vf Va Vb Lf oy of)).set EVL (lE ++ [v + (vra_appOut rowsA vy vf Va Vb Lf oy of).length])).set
        vra_aOY (lY ++ [oy + Va])).set vra_aOF (lF ++ [of + Lf])) = ((((St.set EV (St EV ++
          vra_appOut rowsA vy vf Va Vb Lf oy of)).set EVL (lE ++ [v + (vra_appOut rowsA vy vf Va Vb Lf oy of).length])).set
            vra_aOY (lY ++ [oy + Va])).set vra_aOF (lF ++ [of + Lf])) := by
    vra_ext [vra_aKC, EV, EVL, vra_aOY, vra_aOF] [hKC]
  rw [e] at x₂
  refine (x₁.seq x₂).mono ?_
  have hk : k ≤ rowsA.length := by rw [← hkd, ← vra_srch_end]; exact vra_srch_le _ _ _ (Nat.le_refl _)
  have hm : Vb * (3 * k + 6) ≤ Vb * (3 * rowsA.length + 6) := Nat.mul_le_mul_left _ (by omega)
  unfold vra_roundCost
  omega

/-! ## The application item: the numbers of the types -/

/-- Push entry `it.(field f)` of the table `tbl` on `o` (through `K2`). -/
def vra_readTblP (f : Nat) (tbl o : Fin NK) (h₁ : tbl ≠ vra_T) (h₂ : vra_T ≠ o) : NProg NK :=
  vra_readITP f vra_aK2 (by decide) ;; peekAt tbl vra_T vra_aK2 o h₁ h₂

theorem vra_readTbl (f : Nat) (hf : f < 4) {tbl o : Fin NK} (h₁ : tbl ≠ vra_T) (h₂ : vra_T ≠ o)
    (hd : [tbl, vra_T, vra_aK2, o, IT, vra_K1].Nodup) (St : Lists NK) {it : MItem} (hIT : St IT = encItem it)
    (hT : St vra_T = []) {x : Nat} (hx : (St tbl)[(encItem it)[f]'(by simp [encItem]; exact hf)]? = some x) :
    NRuns (vra_readTblP f tbl o h₁ h₂) St (St.set o (St o ++ [x])) (5 * f + 37 + 6 * (St tbl).length +
      4 * (encItem it)[f]'(by simp [encItem]; exact hf)) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd
  obtain ⟨⟨d1, d2, d3, d4, d5⟩, ⟨e1, e2, e3, e4⟩, ⟨f1, f2, f3⟩, ⟨g1, g2⟩, h5, -⟩ := hd
  have x₁ := vra_readIT (o := vra_aK2) (by decide) (by decide) St hIT hT f hf
  obtain ⟨v, hv⟩ : ∃ v, (encItem it)[f]'(by simp [encItem]; exact hf) = v := ⟨_, rfl⟩
  rw [hv] at x₁ hx ⊢
  have hk : v < (St tbl).length := (List.getElem?_eq_some_iff.1 hx).1
  let S₁ := St.set vra_aK2 (St vra_aK2 ++ [v])
  have x₂ := nruns_peekAt tbl vra_T vra_aK2 o h₁ h₂ (by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
      exact ⟨⟨d1, d2, d3⟩, ⟨e1, e2⟩, f1, not_false⟩) S₁ (by simp [S₁, Lists.set, hT])
    (lc := St vra_aK2) (k := v) (by simp [S₁]) (by simp [S₁, Lists.set, d2, Ne.symm d2]; exact hk)
  have e₁ : S₁ tbl = St tbl := by simp [S₁, Lists.set, d2]
  have hx' : (S₁ tbl)[v]'(by rw [e₁]; exact hk) = x := by
    simp only [e₁]; exact vra_get_of_some hx hk
  have e₂ : (S₁.set vra_aK2 (St vra_aK2)).set o (S₁ o ++ [(S₁ tbl)[v]'(by rw [e₁]; exact hk)]) =
      St.set o (St o ++ [x]) := by
    rw [hx']
    have : S₁ o = St o := by simp [S₁, Lists.set, f1, Ne.symm f1]
    rw [this]; simp only [S₁, Lists.set_set_u, Lists.set_get_self]
  rw [e₂, e₁] at x₂
  exact (x₁.seq x₂).mono (by omega)

/-- Read the numbers of the application: the environments, the length and the rows of the argument type `a`, the
length of the result type `b`, and the length of a function table. -/
def vra_appSetupP : NProg NK :=
  vra_readCtxP ENVT vra_NN (by decide) (by decide) ;;
  vra_readTblP 1 VALT vra_aVA (by decide) (by decide) ;; vra_readTblP 1 CNT vra_aCA (by decide) (by decide) ;;
  vra_readTblP 1 ROFF vra_aRA (by decide) (by decide) ;; vra_readTblP 2 VALT vra_aVB (by decide) (by decide) ;;
  .prim (.dup vra_aCA vra_aLF (by decide)) ;; .prim (.dup vra_aVB vra_aK2 (by decide)) ;;
  vra_mulP vra_aLF vra_aK2 vra_aU vra_aW (by decide) (by decide)

/-- The state after the setup. -/
def vra_setupSt (St : Lists NK) (n Va Ca RA Vb : Nat) : Lists NK :=
  (((((St.set vra_NN [n]).set vra_aVA (St vra_aVA ++ [Va])).set vra_aCA (St vra_aCA ++ [Ca])).set vra_aRA
    (St vra_aRA ++ [RA])).set vra_aVB (St vra_aVB ++ [Vb])).set vra_aLF (St vra_aLF ++ [Ca * Vb])

theorem vra_appSetup_runs (St : Lists NK) {it : MItem} {n Va Ca RA Vb : Nat} (hIT : St IT = encItem it)
    (hT : St vra_T = []) (hNN : St vra_NN = []) (hk : it.ctx < (St ENVT).length) (hn : (St ENVT)[it.ctx]'hk = n)
    (hVa : (St VALT)[it.a]? = some Va) (hCa : (St CNT)[it.a]? = some Ca) (hRA : (St ROFF)[it.a]? = some RA)
    (hVb : (St VALT)[it.b]? = some Vb) :
    NRuns vra_appSetupP St (vra_setupSt St n Va Ca RA Vb)
      (6 * (St ENVT).length + 4 * it.ctx + 7 + 4 * (5 * 2 + 37 + 6 * ((St VALT).length + (St CNT).length +
        (St ROFF).length) + 4 * (it.a + it.b)) + 2 + (Vb * (3 * Ca + 6) + 6)) := by
  have x₁ := vra_readCtx (tbl := ENVT) (o := vra_NN) (by decide) (by decide) (by decide) St hIT hT hk
  rw [hn, hNN, List.nil_append] at x₁
  let S₁ := St.set vra_NN [n]
  have x₂ := vra_readTbl 1 (by decide) (tbl := VALT) (o := vra_aVA) (by decide) (by decide) (by decide) S₁ (it := it)
    (x := Va) (by simp [S₁, Lists.set, hIT]) (by simp [S₁, Lists.set, hT]) (by simpa [S₁, Lists.set, encItem] using hVa)
  let S₂ := S₁.set vra_aVA (S₁ vra_aVA ++ [Va])
  have x₃ := vra_readTbl 1 (by decide) (tbl := CNT) (o := vra_aCA) (by decide) (by decide) (by decide) S₂ (it := it)
    (x := Ca) (by simp [S₂, S₁, Lists.set, hIT]) (by simp [S₂, S₁, Lists.set, hT])
    (by simpa [S₂, S₁, Lists.set, encItem] using hCa)
  let S₃ := S₂.set vra_aCA (S₂ vra_aCA ++ [Ca])
  have x₄ := vra_readTbl 1 (by decide) (tbl := ROFF) (o := vra_aRA) (by decide) (by decide) (by decide) S₃ (it := it)
    (x := RA) (by simp [S₃, S₂, S₁, Lists.set, hIT]) (by simp [S₃, S₂, S₁, Lists.set, hT])
    (by simpa [S₃, S₂, S₁, Lists.set, encItem, NK] using hRA)
  let S₄ := S₃.set vra_aRA (S₃ vra_aRA ++ [RA])
  have x₅ := vra_readTbl 2 (by decide) (tbl := VALT) (o := vra_aVB) (by decide) (by decide) (by decide) S₄ (it := it)
    (x := Vb) (by simp [S₄, S₃, S₂, S₁, Lists.set, hIT]) (by simp [S₄, S₃, S₂, S₁, Lists.set, hT])
    (by simpa [S₄, S₃, S₂, S₁, Lists.set, encItem] using hVb)
  let S₅ := S₄.set vra_aVB (S₄ vra_aVB ++ [Vb])
  have x₆ := nruns_dup vra_aCA vra_aLF (by decide) S₅ (l := St vra_aCA) (v := Ca) (by simp [S₅, S₄, S₃, S₂, S₁, Lists.set])
  let S₆ := S₅.set vra_aLF (S₅ vra_aLF ++ [Ca])
  have x₇ := nruns_dup vra_aVB vra_aK2 (by decide) S₆ (l := St vra_aVB) (v := Vb)
    (by simp [S₆, S₅, S₄, S₃, S₂, S₁, Lists.set])
  let S₇ := S₆.set vra_aK2 (S₆ vra_aK2 ++ [Vb])
  have x₈ := vra_mul (R := vra_aLF) (Cn := vra_aK2) (U := vra_aU) (W := vra_aW) ⟨by decide, by decide, by decide,
    by decide, by decide, by decide⟩ S₇ (lR := St vra_aLF) (lC := St vra_aK2) (r := Ca) (c := Vb)
    (by simp [S₇, S₆, S₅, S₄, S₃, S₂, S₁, Lists.set]) (by simp [S₇, S₆, S₅, S₄, S₃, S₂, S₁, Lists.set])
  have e : (S₇.set vra_aLF (St vra_aLF ++ [Ca * Vb])).set vra_aK2 (St vra_aK2) = vra_setupSt St n Va Ca RA Vb := by
    simp only [S₇, S₆, S₅, S₄, S₃, S₂, S₁, vra_setupSt]
    vra_ext [vra_NN, vra_aVA, vra_aCA, vra_aRA, vra_aVB, vra_aLF, vra_aK2] []
  rw [e] at x₈
  refine (x₁.seq (x₂.seq (x₃.seq (x₄.seq (x₅.seq (x₆.seq (x₇.seq x₈))))))).mono ?_
  have l₂ : (S₁ VALT).length = (St VALT).length := by simp [S₁, Lists.set]
  have l₃ : (S₂ CNT).length = (St CNT).length := by simp [S₂, S₁, Lists.set]
  have l₄ : (S₃ ROFF).length = (St ROFF).length := by simp [S₃, S₂, S₁, Lists.set, NK]
  have l₅ : (S₄ VALT).length = (St VALT).length := by simp [S₄, S₃, S₂, S₁, Lists.set]
  simp only [encItem] at x₂ x₃ x₄ x₅ ⊢
  simp only [List.getElem_cons_succ, List.getElem_cons_zero] at x₂ x₃ x₄ x₅ ⊢
  omega

/-! ## The application item: the cost of a round -/

theorem vra_mul_step {a b c P Z : Nat} (ha : a ≤ c * P) (hb : b ≤ Z) : a * b ≤ c * (P * Z) := by
  have := Nat.mul_le_mul ha hb
  rw [Nat.mul_assoc] at this; exact this

theorem vra_pow_facts {Z : Nat} (hZ : 2 ≤ Z) :
    4 ≤ Z * Z ∧ 2 * Z ≤ Z * Z ∧ 4 * Z ≤ Z * Z * Z ∧ 8 ≤ Z * Z * Z ∧ 2 * (Z * Z) ≤ Z * Z * Z ∧
      2 * (Z * Z * Z) ≤ Z * Z * Z * Z ∧ 2 * (Z * Z * Z * Z) ≤ Z * Z * Z * Z * Z := by
  have h1 : 2 * Z ≤ Z * Z := Nat.mul_le_mul_right _ hZ
  have h2 : 2 * (Z * Z) ≤ Z * Z * Z := by
    have := Nat.mul_le_mul_left (Z * Z) hZ; rw [Nat.mul_comm] at this; exact this
  have h3 : 2 * (Z * Z * Z) ≤ Z * Z * Z * Z := by
    have := Nat.mul_le_mul_left (Z * Z * Z) hZ; rw [Nat.mul_comm] at this; exact this
  have h4 : 2 * (Z * Z * Z * Z) ≤ Z * Z * Z * Z * Z := by
    have := Nat.mul_le_mul_left (Z * Z * Z * Z) hZ; rw [Nat.mul_comm] at this; exact this
  refine ⟨by omega, h1, by omega, by omega, h2, h3, h4⟩

theorem vra_eqRound_le {M Z : Nat} (hM : M ≤ Z) (hZ : 2 ≤ Z) : vra_eqRound M ≤ 23 * (Z * Z) := by
  obtain ⟨p1, -⟩ := vra_pow_facts hZ
  unfold vra_eqRound
  have h : (2 * M + 1) * (2 * M + 6) ≤ (3 * Z) * (5 * Z) := Nat.mul_le_mul (by omega) (by omega)
  have e : (3 * Z) * (5 * Z) = 15 * (Z * Z) := by rw [Nat.mul_mul_mul_comm]
  omega

theorem vra_eqCost_le {M Va Z : Nat} (hM : M ≤ Z) (hV : Va ≤ Z) (hZ : 2 ≤ Z) :
    vra_eqCost M Va Va ≤ 55 * (Z * Z * Z) := by
  obtain ⟨p1, p2, p3, p4, p5, -⟩ := vra_pow_facts hZ
  have hr := vra_eqRound_le hM hZ
  unfold vra_eqCost
  have h : (Va + 1) * (vra_eqRound M + 2 * Va + 8) ≤ (2 * Z) * (26 * (Z * Z)) := Nat.mul_le_mul (by omega) (by omega)
  have e : (2 * Z) * (26 * (Z * Z)) = 52 * (Z * Z * Z) := by
    rw [Nat.mul_mul_mul_comm, Nat.mul_comm Z (Z * Z)]
  omega

theorem vra_roundCost_le {nr ny nf M Va Vb Ca Lf Z : Nat} (hnr : nr ≤ Z) (hny : ny ≤ Z) (hnf : nf ≤ Z) (hM : M ≤ Z)
    (hVa : Va ≤ Z) (hVb : Vb ≤ Z) (hCa : Ca ≤ Z) (hLf : Lf ≤ Z * Z) (hZ : 2 ≤ Z) :
    vra_roundCost nr ny nf M Va Vb Ca Lf ≤ 130 * (Z * Z * Z * Z) := by
  obtain ⟨p1, p2, p3, p4, p5, p6, -⟩ := vra_pow_facts hZ
  have he := vra_eqCost_le hM hVa hZ
  have hc : vra_cmpCost nr ny M Va + 3 * Va + 6 + 2 ≤ 110 * (Z * Z * Z) := by
    unfold vra_cmpCost vra_sliceCost; omega
  have h₁ : Ca * (vra_cmpCost nr ny M Va + 3 * Va + 6 + 2) ≤ 110 * (Z * Z * Z * Z) := by
    rw [Nat.mul_comm]; exact vra_mul_step hc hCa
  have h₂ : Vb * (3 * Ca + 6) ≤ 9 * (Z * Z) := by
    have := Nat.mul_le_mul hVb (show 3 * Ca + 6 ≤ 9 * Z by omega)
    rw [Nat.mul_left_comm] at this; exact this
  unfold vra_roundCost vra_sliceCost
  omega

/-! ## The application item -/

/-- Take the two top vectors off `EV` (onto `YV` and `FV`), read the numbers, copy the blocks of all environments,
and clean up. -/
def vra_appMainP : NProg NK :=
  moveN EVL EV vra_A (by decide) ;; nmvAll vra_A vra_aYV (by decide) ;;
  moveN EVL EV vra_A (by decide) ;; nmvAll vra_A vra_aFV (by decide) ;;
  vra_appSetupP ;;
  .prim (.pushZ EVL) ;; .prim (.pushZ vra_aOY) ;; .prim (.pushZ vra_aOF) ;;
  vra_repeatP vra_NN vra_appRoundP ;;
  .prim (.pop vra_aOY) ;; .prim (.pop vra_aOF) ;; .prim (.pop vra_aLF) ;; .prim (.pop vra_aVB) ;;
  .prim (.pop vra_aRA) ;; .prim (.pop vra_aCA) ;; .prim (.pop vra_aVA) ;; nclr vra_aYV ;; nclr vra_aFV

/-- **The application item**: with at least two vectors on the stack, apply the functions to the arguments;
otherwise leave the stack alone. -/
def itemAppP : NProg NK :=
  .ite EVL .nonempty
    (nmv EVL vra_aW (by decide) ;;
      .ite EVL .nonempty (nmv vra_aW EVL (by decide) ;; vra_appMainP) (nmv vra_aW EVL (by decide)))
    (nskip vra_T)

/-- The blocks of the environments `0, …, e - 1`. -/
def vra_appOuts (rowsA : List (List Nat)) (vy vf : List Nat) (Va Vb Lf e : Nat) : List Nat :=
  ((List.range e).map (fun i => vra_appOut rowsA vy vf Va Vb Lf (i * Va) (i * Lf))).flatten

/-- The state of the loop over the environments. -/
def vra_appLoopSt (Sb : Lists NK) (lE : List Nat) (rowsA : List (List Nat)) (vy vf : List Nat) (Va Vb Lf e : Nat) :
    Lists NK :=
  (((Sb.set EV (Sb EV ++ vra_appOuts rowsA vy vf Va Vb Lf e)).set EVL
    (lE ++ [(vra_appOuts rowsA vy vf Va Vb Lf e).length])).set vra_aOY [e * Va]).set vra_aOF [e * Lf]

theorem vra_appLoop_runs (Sb : Lists NK) {rows vy vf lE : List Nat} {Va Vb RA n M : Nat}
    {rowsA : List (List Nat)} (hc : VraApp Sb rows vy vf Va)
    (hrow : ∀ k (hk : k < rowsA.length), (rows.drop (RA + k * Va)).take Va = rowsA[k])
    (hMr : ∀ x ∈ rows, x ≤ M) (hMy : ∀ x ∈ vy, x ≤ M)
    (hCA : ∃ l, Sb vra_aCA = l ++ [rowsA.length]) (hRA : ∃ l, Sb vra_aRA = l ++ [RA])
    (hVB : ∃ l, Sb vra_aVB = l ++ [Vb]) (hLF : ∃ l, Sb vra_aLF = l ++ [rowsA.length * Vb])
    (hKC : Sb vra_aKC = []) :
    NRuns (vra_repeatP vra_NN vra_appRoundP)
      ((vra_appLoopSt Sb lE rowsA vy vf Va Vb (rowsA.length * Vb) 0).set vra_NN ([] ++ [n]))
      ((vra_appLoopSt Sb lE rowsA vy vf Va Vb (rowsA.length * Vb) n).set vra_NN [])
      (n * (vra_roundCost rows.length vy.length vf.length M Va Vb rowsA.length (rowsA.length * Vb) + 2) + 2) := by
  obtain ⟨lCA, hCA⟩ := hCA; obtain ⟨lRA, hRA⟩ := hRA; obtain ⟨lVB, hVB⟩ := hVB; obtain ⟨lLF, hLF⟩ := hLF
  apply vra_repeat vra_NN vra_appRoundP (vra_appLoopSt Sb lE rowsA vy vf Va Vb (rowsA.length * Vb)) n _ []
  intro e _
  let Ge := (vra_appLoopSt Sb lE rowsA vy vf Va Vb (rowsA.length * Vb) e).set vra_NN ([] ++ [n - e - 1])
  have hGe : VraApp Ge rows vy vf Va :=
    ((((hc.set _ (k := EV) (by decide)).set _ (k := EVL) (by decide)).set _ (k := vra_aOY) (by decide)).set _
      (k := vra_aOF) (by decide)).set _ (by decide)
  have y := vra_appRound_runs Ge hGe hrow hMr hMy (Lf := rowsA.length * Vb) (Vb := Vb) (lCA := lCA) (lRA := lRA) (lVB := lVB)
    (lLF := lLF) (lY := []) (lF := []) (lE := lE) (oy := e * Va) (of := e * (rowsA.length * Vb))
    (v := (vra_appOuts rowsA vy vf Va Vb (rowsA.length * Vb) e).length)
    (by simp [Ge, vra_appLoopSt, Lists.set, hCA]) (by simp [Ge, vra_appLoopSt, Lists.set, hRA])
    (by simp [Ge, vra_appLoopSt, Lists.set, hVB]) (by simp [Ge, vra_appLoopSt, Lists.set, hLF])
    (by simp [Ge, vra_appLoopSt, Lists.set]) (by simp [Ge, vra_appLoopSt, Lists.set])
    (by simp [Ge, vra_appLoopSt, Lists.set]) (by simp [Ge, vra_appLoopSt, Lists.set, hKC])
  have hout : vra_appOuts rowsA vy vf Va Vb (rowsA.length * Vb) (e + 1) =
      vra_appOuts rowsA vy vf Va Vb (rowsA.length * Vb) e ++
        vra_appOut rowsA vy vf Va Vb (rowsA.length * Vb) (e * Va) (e * (rowsA.length * Vb)) := by
    simp [vra_appOuts, List.range_succ]
  have e₁ : ((((Ge.set EV (Ge EV ++ vra_appOut rowsA vy vf Va Vb (rowsA.length * Vb) (e * Va)
      (e * (rowsA.length * Vb)))).set EVL (lE ++ [(vra_appOuts rowsA vy vf Va Vb (rowsA.length * Vb) e).length +
        (vra_appOut rowsA vy vf Va Vb (rowsA.length * Vb) (e * Va) (e * (rowsA.length * Vb))).length])).set vra_aOY
          ([] ++ [e * Va + Va])).set vra_aOF ([] ++ [e * (rowsA.length * Vb) + rowsA.length * Vb])) =
      (vra_appLoopSt Sb lE rowsA vy vf Va Vb (rowsA.length * Vb) (e + 1)).set vra_NN ([] ++ [n - e - 1]) := by
    have hEV : Ge EV = Sb EV ++ vra_appOuts rowsA vy vf Va Vb (rowsA.length * Vb) e := by
      simp [Ge, vra_appLoopSt, Lists.set]
    rw [hEV]
    simp only [Ge, vra_appLoopSt, hout, List.append_assoc, List.length_append, Nat.succ_mul, List.nil_append]
    vra_ext [EV, EVL, vra_aOY, vra_aOF, vra_NN] []
  rw [e₁] at y
  exact y.mono (Nat.le_refl _)

theorem vra_typeTable_some (tt : List (Nat × Nat)) (f : Nat → Nat) {t : Nat} (ht : t ≤ tt.length) :
    (typeTable tt f)[t]? = some (f t) := by
  simp [typeTable, List.getElem?_map, List.getElem?_range (show t < tt.length + 1 by omega)]

/-- The arithmetic of the cost of `vra_appMain_runs`. -/
theorem vra_appMain_cost (y f c t ctx a b P Q : Nat) :
    4 * y + 2 + (3 * y + 1 + (4 * f + 2 + (3 * f + 1 + (6 * (c + 1) + 4 * ctx + 7 +
      4 * (5 * 2 + 37 + 6 * ((t + 1) + (t + 1) + (t + 1)) + 4 * (a + b)) + 2 + (P + 6) +
      (1 + (1 + (1 + (Q + 2 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 * y + 1 + (2 * f + 1))))))))))))))))) ≤
    7 * y + 3 + (7 * f + 3) + (6 * (c + 1) + 4 * ctx + 7 + 4 * (5 * 2 + 37 + 6 * (3 * (t + 1)) + 4 * (a + b)) +
      2 + (P + 6)) + 3 + (Q + 2) + 7 + (2 * y + 1) + (2 * f + 1) := by
  omega

/-- The application item on two vectors `vy` (the arguments) and `vf` (the functions), with its exact cost. -/
theorem vra_appMain_runs (j cap : Nat) (st : PSt) (Tf : List (List Nat)) (it : MItem) (hcur : it.ctx ≤ st.ct.length)
    (ha : it.a ≤ st.tt.length) (hb : it.b ≤ st.tt.length) (S : Lists NK) (vy vf : List Nat)
    (rest : List (List Nat)) (hE : EvalEnv S j cap st Tf) (hIT : S IT = encItem it)
    (hEV : S EV = evFlat (vy :: vf :: rest)) (hEVL : S EVL = evLens (vy :: vf :: rest)) (M : Nat)
    (hMr : ∀ x ∈ rowsFlat j cap st.x.length st.tt, x ≤ M) (hMy : ∀ x ∈ vy, x ≤ M) :
    NRuns vra_appMainP S ((S.set EV (evFlat rest ++ vra_appOuts (rowsT j cap st.x.length st.tt it.a) vy vf
        (valT j cap st.x.length st.tt it.a) (valT j cap st.x.length st.tt it.b)
        ((rowsT j cap st.x.length st.tt it.a).length * valT j cap st.x.length st.tt it.b)
        (envT j cap st.x.length st.tt st.ct it.ctx))).set EVL (evLens rest ++
      [(vra_appOuts (rowsT j cap st.x.length st.tt it.a) vy vf
        (valT j cap st.x.length st.tt it.a) (valT j cap st.x.length st.tt it.b)
        ((rowsT j cap st.x.length st.tt it.a).length * valT j cap st.x.length st.tt it.b)
        (envT j cap st.x.length st.tt st.ct it.ctx)).length]))
      ((7 * vy.length + 3) + (7 * vf.length + 3) + (6 * (st.ct.length + 1) + 4 * it.ctx + 7 +
        4 * (5 * 2 + 37 + 6 * (3 * (st.tt.length + 1)) + 4 * (it.a + it.b)) + 2 +
        (valT j cap st.x.length st.tt it.b * (3 * (rowsT j cap st.x.length st.tt it.a).length + 6) + 6)) + 3 +
        (envT j cap st.x.length st.tt st.ct it.ctx * (vra_roundCost (rowsFlat j cap st.x.length st.tt).length
          vy.length vf.length M (valT j cap st.x.length st.tt it.a) (valT j cap st.x.length st.tt it.b)
          (rowsT j cap st.x.length st.tt it.a).length
          ((rowsT j cap st.x.length st.tt it.a).length * valT j cap st.x.length st.tt it.b) + 2) + 2) +
        7 + (2 * vy.length + 1) + (2 * vf.length + 1)) := by
  have sc := hE.scratch
  have hA := vra_scr sc vra_A; have hB := vra_scr sc vra_B; have hD := vra_scr sc vra_D
  have hEm := vra_scr sc vra_E; have hT := vra_scr sc vra_T; have hNN := vra_scr sc vra_NN
  have hO1 := vra_scr sc vra_O1; have hL1 := vra_scr sc vra_L1; have hYV := vra_scr sc vra_aYV
  have hFV := vra_scr sc vra_aFV; have hOY := vra_scr sc vra_aOY; have hOF := vra_scr sc vra_aOF
  have hKC := vra_scr sc vra_aKC; have hP := vra_scr sc vra_P; have hQ := vra_scr sc vra_Q
  obtain ⟨n, hn⟩ : ∃ n, envT j cap st.x.length st.tt st.ct it.ctx = n := ⟨_, rfl⟩
  obtain ⟨Va, hVa⟩ : ∃ v, valT j cap st.x.length st.tt it.a = v := ⟨_, rfl⟩
  obtain ⟨Vb, hVb⟩ : ∃ v, valT j cap st.x.length st.tt it.b = v := ⟨_, rfl⟩
  obtain ⟨rowsA, hrA⟩ : ∃ r, rowsT j cap st.x.length st.tt it.a = r := ⟨_, rfl⟩
  rw [hn, hVa, hVb, hrA]
  -- the two vectors off `EV`
  rw [evFlat_cons, evFlat_cons] at hEV
  rw [evLens_cons, evLens_cons] at hEVL
  have x₁ := nruns_moveN EVL EV vra_A (by decide) (by decide) (by decide) S hEVL (l := evFlat rest ++ vf) (seg := vy)
    (by rw [hEV]) rfl
  rw [hA, List.nil_append] at x₁
  let S₁ := ((S.set EVL (evLens rest ++ [vf.length])).set EV (evFlat rest ++ vf)).set vra_A vy.reverse
  have x₂ := nruns_mvAll vra_A vra_aYV (by decide) S₁
  have h₂ : (S₁.set vra_aYV (S₁ vra_aYV ++ (S₁ vra_A).reverse)).set vra_A [] =
      ((S.set EVL (evLens rest ++ [vf.length])).set EV (evFlat rest ++ vf)).set vra_aYV vy := by
    simp only [S₁]; vra_ext [EVL, EV, vra_A, vra_aYV] [hA, hYV]
  rw [h₂] at x₂
  let S₂ := ((S.set EVL (evLens rest ++ [vf.length])).set EV (evFlat rest ++ vf)).set vra_aYV vy
  have x₃ := nruns_moveN EVL EV vra_A (by decide) (by decide) (by decide) S₂ (lc := evLens rest) (n := vf.length)
    (by simp [S₂, Lists.set]) (l := evFlat rest) (seg := vf) (by simp [S₂, Lists.set]) rfl
  have hA₂ : S₂ vra_A = [] := by simp [S₂, Lists.set, hA]
  rw [hA₂, List.nil_append] at x₃
  let S₃ := ((S₂.set EVL (evLens rest)).set EV (evFlat rest)).set vra_A vf.reverse
  have x₄ := nruns_mvAll vra_A vra_aFV (by decide) S₃
  let C₄ := (((S.set EVL (evLens rest)).set EV (evFlat rest)).set vra_aYV vy).set vra_aFV vf
  have h₄ : (S₃.set vra_aFV (S₃ vra_aFV ++ (S₃ vra_A).reverse)).set vra_A [] = C₄ := by
    simp only [S₃, S₂, C₄]; vra_ext [EVL, EV, vra_A, vra_aYV, vra_aFV] [hA, hFV]
  rw [h₄] at x₄
  -- the numbers
  have hkE : it.ctx < (C₄ ENVT).length := by simp [C₄, Lists.set, hE.envt, envTable]; omega
  have hval : C₄ VALT = valTable j cap st.x.length st.tt := by simp [C₄, Lists.set, hE.valt]
  have hcnt : C₄ CNT = cntTable j cap st.x.length st.tt := by simp [C₄, Lists.set, hE.cnt]
  have hroff : C₄ ROFF = roffTable j cap st.x.length st.tt := by simp [C₄, Lists.set, hE.roff, NK]
  obtain ⟨RA, hRA⟩ : ∃ r, (roffTable j cap st.x.length st.tt)[it.a]? = some r :=
    ⟨_, List.getElem?_eq_getElem (by simp [roffTable, typeTable]; omega)⟩
  have x₅ := vra_appSetup_runs C₄ (it := it) (n := n) (Va := Va) (Ca := rowsA.length) (RA := RA) (Vb := Vb)
    (by simp [C₄, Lists.set, hIT]) (by simp [C₄, Lists.set, hT]) (by simp [C₄, Lists.set, hNN]) hkE
    (by simp only [C₄, Lists.set_ne _ _ (show ENVT ≠ vra_aFV by decide), Lists.set_ne _ _ (show ENVT ≠ vra_aYV by decide),
        Lists.set_ne _ _ (show ENVT ≠ EV by decide), Lists.set_ne _ _ (show ENVT ≠ EVL by decide), hE.envt]
        rw [← hn]; exact vra_envT_entry _ _ _ _ _ _ hcur)
    (by rw [hval, ← hVa]; exact vra_typeTable_some _ _ ha)
    (by rw [hcnt, ← hrA]; exact vra_typeTable_some _ _ ha)
    (by rw [hroff]; exact hRA)
    (by rw [hval, ← hVb]; exact vra_typeTable_some _ _ hb)
  have hlens : (C₄ ENVT).length = st.ct.length + 1 ∧ (C₄ VALT).length = st.tt.length + 1 ∧
      (C₄ CNT).length = st.tt.length + 1 ∧ (C₄ ROFF).length = st.tt.length + 1 := by
    refine ⟨by simp [C₄, Lists.set, hE.envt, envTable], by rw [hval]; simp [valTable, typeTable],
      by rw [hcnt]; simp [cntTable, typeTable], by rw [hroff]; simp [roffTable, typeTable]⟩
  -- the loop over the environments
  let Sb := vra_setupSt C₄ n Va rowsA.length RA Vb
  have x₆ := nruns_pushZ EVL Sb
  have x₇ := nruns_pushZ vra_aOY (Sb.set EVL (Sb EVL ++ [0]))
  have x₈ := nruns_pushZ vra_aOF ((Sb.set EVL (Sb EVL ++ [0])).set vra_aOY
    ((Sb.set EVL (Sb EVL ++ [0])) vra_aOY ++ [0]))
  have hSbEVL : Sb EVL = evLens rest := by simp [Sb, vra_setupSt, C₄, Lists.set]
  have e₈ : (((Sb.set EVL (Sb EVL ++ [0])).set vra_aOY ((Sb.set EVL (Sb EVL ++ [0])) vra_aOY ++ [0])).set vra_aOF
      (((Sb.set EVL (Sb EVL ++ [0])).set vra_aOY ((Sb.set EVL (Sb EVL ++ [0])) vra_aOY ++ [0])) vra_aOF ++ [0])) =
      (vra_appLoopSt Sb (evLens rest) rowsA vy vf Va Vb (rowsA.length * Vb) 0).set vra_NN ([] ++ [n]) := by
    rw [hSbEVL]
    simp only [vra_appLoopSt, vra_appOuts, List.range_zero, List.map_nil, List.flatten_nil, List.append_nil,
      List.length_nil, Nat.zero_mul, Sb, vra_setupSt, C₄, List.nil_append]
    vra_ext [EVL, EV, vra_aYV, vra_aFV, vra_NN, vra_aVA, vra_aCA, vra_aRA, vra_aVB, vra_aLF, vra_aOY, vra_aOF]
      [hOY, hOF]
  rw [e₈] at x₈
  have hc : VraApp Sb (rowsFlat j cap st.x.length st.tt) vy vf Va :=
    ⟨by simp [Sb, vra_setupSt, C₄, Lists.set, hE.rows], by simp [Sb, vra_setupSt, C₄, Lists.set],
      by simp [Sb, vra_setupSt, C₄, Lists.set], ⟨S vra_aVA, by simp [Sb, vra_setupSt, C₄, Lists.set]⟩,
      by simp [Sb, vra_setupSt, C₄, Lists.set, hA], by simp [Sb, vra_setupSt, C₄, Lists.set, hB],
      by simp [Sb, vra_setupSt, C₄, Lists.set, hD], by simp [Sb, vra_setupSt, C₄, Lists.set, hEm],
      by simp [Sb, vra_setupSt, C₄, Lists.set, hO1], by simp [Sb, vra_setupSt, C₄, Lists.set, hL1],
      by simp [Sb, vra_setupSt, C₄, Lists.set, hP], by simp [Sb, vra_setupSt, C₄, Lists.set, hQ],
      by simp [Sb, vra_setupSt, C₄, Lists.set, hT]⟩
  have hrow : ∀ k (hk : k < rowsA.length), ((rowsFlat j cap st.x.length st.tt).drop (RA + k * Va)).take Va =
      rowsA[k] := by
    intro k hk
    have hs := vra_rowsFlat_slice j cap st.x.length st.tt ha (k := k) (by rw [hrA]; exact hk)
    rw [vra_get_of_some hRA] at hs
    have hv : (valTable j cap st.x.length st.tt)[it.a]'(by simp [valTable, typeTable]; omega) = Va := by
      rw [← hVa]; exact vra_typeTable_get _ _ ha
    rw [hv] at hs
    simp only [hrA] at hs
    exact hs
  have x₉ := vra_appLoop_runs Sb hc hrow hMr hMy (lE := evLens rest) (n := n) (Vb := Vb)
    ⟨S vra_aCA, by simp [Sb, vra_setupSt, C₄, Lists.set]⟩ ⟨S vra_aRA, by simp [Sb, vra_setupSt, C₄, Lists.set, NK]⟩
    ⟨S vra_aVB, by simp [Sb, vra_setupSt, C₄, Lists.set]⟩ ⟨S vra_aLF, by simp [Sb, vra_setupSt, C₄, Lists.set]⟩
    (by simp [Sb, vra_setupSt, C₄, Lists.set, hKC])
  -- clean up
  let out := vra_appOuts rowsA vy vf Va Vb (rowsA.length * Vb) n
  let F := (vra_appLoopSt Sb (evLens rest) rowsA vy vf Va Vb (rowsA.length * Vb) n).set vra_NN []
  have y₁ := nruns_pop vra_aOY F (l := []) (v := n * Va) (by simp [F, vra_appLoopSt, Lists.set])
  have y₂ := nruns_pop vra_aOF (F.set vra_aOY []) (l := []) (v := n * (rowsA.length * Vb))
    (by simp [F, vra_appLoopSt, Lists.set])
  have y₃ := nruns_pop vra_aLF ((F.set vra_aOY []).set vra_aOF []) (l := S vra_aLF) (v := rowsA.length * Vb)
    (by simp [F, vra_appLoopSt, Sb, vra_setupSt, C₄, Lists.set])
  have y₄ := nruns_pop vra_aVB (((F.set vra_aOY []).set vra_aOF []).set vra_aLF (S vra_aLF)) (l := S vra_aVB) (v := Vb)
    (by simp [F, vra_appLoopSt, Sb, vra_setupSt, C₄, Lists.set])
  have y₅ := nruns_pop vra_aRA ((((F.set vra_aOY []).set vra_aOF []).set vra_aLF (S vra_aLF)).set vra_aVB (S vra_aVB))
    (l := S vra_aRA) (v := RA) (by simp [F, vra_appLoopSt, Sb, vra_setupSt, C₄, Lists.set, NK])
  let F₅ := ((((F.set vra_aOY []).set vra_aOF []).set vra_aLF (S vra_aLF)).set vra_aVB (S vra_aVB)).set vra_aRA
    (S vra_aRA)
  have y₆ := nruns_pop vra_aCA F₅ (l := S vra_aCA) (v := rowsA.length)
    (by simp [F₅, F, vra_appLoopSt, Sb, vra_setupSt, C₄, Lists.set, NK])
  have y₇ := nruns_pop vra_aVA (F₅.set vra_aCA (S vra_aCA)) (l := S vra_aVA) (v := Va)
    (by simp [F₅, F, vra_appLoopSt, Sb, vra_setupSt, C₄, Lists.set, NK])
  let F₇ := (F₅.set vra_aCA (S vra_aCA)).set vra_aVA (S vra_aVA)
  have y₈ := nruns_clr vra_aYV F₇
  have hY7 : F₇ vra_aYV = vy := by simp [F₇, F₅, F, vra_appLoopSt, Sb, vra_setupSt, C₄, Lists.set, NK]
  rw [hY7] at y₈
  have y₉ := nruns_clr vra_aFV (F₇.set vra_aYV [])
  have hF7 : (F₇.set vra_aYV []) vra_aFV = vf := by
    simp [F₇, F₅, F, vra_appLoopSt, Sb, vra_setupSt, C₄, Lists.set, NK]
  rw [hF7] at y₉
  have e₉ : (F₇.set vra_aYV []).set vra_aFV [] = (S.set EV (evFlat rest ++ out)).set EVL
      (evLens rest ++ [out.length]) := by
    have hSbEV : Sb EV = evFlat rest := by simp [Sb, vra_setupSt, C₄, Lists.set]
    simp only [F₇, F₅, F, vra_appLoopSt, hSbEV, out]
    simp only [Sb, vra_setupSt, C₄]
    vra_ext [EVL, EV, vra_aYV, vra_aFV, vra_NN, vra_aVA, vra_aCA, vra_aRA, vra_aVB, vra_aLF, vra_aOY, vra_aOF]
      [hYV, hFV, hNN, hOY, hOF]
  rw [e₉] at y₉
  refine (x₁.seq (x₂.seq (x₃.seq (x₄.seq (x₅.seq (x₆.seq (x₇.seq (x₈.seq (x₉.seq (y₁.seq (y₂.seq (y₃.seq (y₄.seq
    (y₅.seq (y₆.seq (y₇.seq (y₈.seq y₉))))))))))))))))).mono ?_
  have hl₁ : (S₁ vra_A).length = vy.length := by simp [S₁]
  have hl₃ : (S₃ vra_A).length = vf.length := by simp [S₃]
  obtain ⟨l₁, l₂, l₃, l₄⟩ := hlens
  rw [hl₁, hl₃, l₁, l₂, l₃, l₄]
  exact vra_appMain_cost _ _ _ _ _ _ _ _ _

theorem vra_valT_le_sum (j cap N : Nat) (tt : List (Nat × Nat)) {t : Nat} (ht : t ≤ tt.length) :
    valT j cap N tt t ≤ (valTable j cap N tt).sum :=
  vra_le_sum (List.mem_map.2 ⟨t, List.mem_range.2 (by omega), rfl⟩)

theorem vra_mem_le_sum {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ l.sum := vra_le_sum h

theorem itemAppP_runs (j cap : Nat) (st : PSt) (Tf : List (List Nat)) (it : MItem) (htag : it.tag = 12)
    (hcur : it.ctx ≤ st.ct.length) (ha : it.a ≤ st.tt.length) (hb : it.b ≤ st.tt.length) :
    ItemRuns itemAppP j cap st Tf it := by
  intro S vs hE hIT hEV hEVL
  have hT := vra_scr hE.scratch vra_T
  have hZ2 : 2 ≤ itemZ j cap st Tf it vs := by unfold itemZ; omega
  have hsq : itemZ j cap st Tf it vs ≤ itemZ j cap st Tf it vs * itemZ j cap st Tf it vs :=
    Nat.le_mul_of_pos_left _ (by omega)
  rcases vs with _ | ⟨vy, _ | ⟨vf, rest⟩⟩
  · -- no vector
    rw [vra_stepT_app_short j cap st Tf it htag [] (by simp)]
    have e : (S.set EV (evFlat [])).set EVL (evLens []) = S := by
      rw [← hEV, ← hEVL]; vra_ext [EV, EVL] []
    rw [e]
    have := (nruns_skip vra_T S).iteF (i := EVL) (c := .nonempty)
      (p := nmv EVL vra_aW (by decide) ;;
        .ite EVL .nonempty (nmv vra_aW EVL (by decide) ;; vra_appMainP) (nmv vra_aW EVL (by decide)))
      (by rw [hEVL]; rfl)
    exact this.mono (vra_le_itemCost (by omega))
  · -- one vector
    rw [vra_stepT_app_short j cap st Tf it htag [vy] (by simp)]
    have e : (S.set EV (evFlat [vy])).set EVL (evLens [vy]) = S := by
      rw [← hEV, ← hEVL]; vra_ext [EV, EVL] []
    rw [e]
    have hL : S EVL = [] ++ [vy.length] := by rw [hEVL]; rfl
    have x₁ := nruns_mv EVL vra_aW (by decide) S hL
    have x₂ := nruns_mv vra_aW EVL (by decide) ((S.set vra_aW (S vra_aW ++ [vy.length])).set EVL [])
      (l := S vra_aW) (v := vy.length) (by simp [Lists.set])
    have e₂ : ((((S.set vra_aW (S vra_aW ++ [vy.length])).set EVL []).set EVL
        (((S.set vra_aW (S vra_aW ++ [vy.length])).set EVL []) EVL ++ [vy.length])).set vra_aW (S vra_aW)) = S := by
      vra_ext [EVL, vra_aW] [hL]
    rw [e₂] at x₂
    have y := (x₁.seq (x₂.iteF (i := EVL) (c := .nonempty) (p := nmv vra_aW EVL (by decide) ;; vra_appMainP)
      (by simp [Lists.set]))).iteT (i := EVL) (c := .nonempty) (q := nskip vra_T) (by rw [hL]; exact eval_nonempty_snoc _ _)
    exact y.mono (vra_le_itemCost (by omega))
  · -- two vectors or more
    rw [vra_stepT_app j cap st Tf it htag vy vf rest, evFlat_cons, evLens_cons]
    have hL : S EVL = (evLens rest ++ [vf.length]) ++ [vy.length] := by
      rw [hEVL, evLens_cons, evLens_cons]
    have x₁ := nruns_mv EVL vra_aW (by decide) S hL
    have x₂ := nruns_mv vra_aW EVL (by decide) ((S.set vra_aW (S vra_aW ++ [vy.length])).set EVL
      (evLens rest ++ [vf.length])) (l := S vra_aW) (v := vy.length) (by simp [Lists.set])
    have e₂ : ((((S.set vra_aW (S vra_aW ++ [vy.length])).set EVL (evLens rest ++ [vf.length])).set EVL
        (((S.set vra_aW (S vra_aW ++ [vy.length])).set EVL (evLens rest ++ [vf.length])) EVL ++ [vy.length])).set
          vra_aW (S vra_aW)) = S := by
      vra_ext [EVL, vra_aW] [hL]
    rw [e₂] at x₂
    -- the bounds
    have hflat : evFlat (vy :: vf :: rest) = evFlat rest ++ vf ++ vy := by rw [evFlat_cons, evFlat_cons]
    have hZ : (evFlat (vy :: vf :: rest)).length + (evFlat (vy :: vf :: rest)).sum +
        (rowsFlat j cap st.x.length st.tt).length + (rowsFlat j cap st.x.length st.tt).sum + st.ct.length +
        it.ctx + it.a + it.b + st.tt.length + (envTable j cap st.x.length st.tt st.ct).sum +
        (valTable j cap st.x.length st.tt).sum + (cntTable j cap st.x.length st.tt).sum + 2 ≤
        itemZ j cap st Tf it (vy :: vf :: rest) := by
      unfold itemZ; omega
    unfold itemCost
    generalize hZd : itemZ j cap st Tf it (vy :: vf :: rest) = Z at hZ hZ2 hsq ⊢
    have hlen : vy.length + vf.length ≤ (evFlat (vy :: vf :: rest)).length := by
      rw [hflat]; simp; omega
    have hMy : ∀ x ∈ vy, x ≤ Z := by
      intro x hx
      have : x ≤ (evFlat (vy :: vf :: rest)).sum := vra_mem_le_sum (by rw [hflat]; simp [hx])
      omega
    have hMr : ∀ x ∈ rowsFlat j cap st.x.length st.tt, x ≤ Z := fun x hx => by
      have := vra_mem_le_sum hx; omega
    have x₃ := vra_appMain_runs j cap st Tf it hcur ha hb S vy vf rest hE hIT hEV hEVL Z hMr hMy
    have y := (x₁.seq ((x₂.seq x₃).iteT (i := EVL) (c := .nonempty) (q := nmv vra_aW EVL (by decide))
      (by simp [Lists.set]))).iteT (i := EVL) (c := .nonempty) (q := nskip vra_T) (by rw [hL]; exact eval_nonempty_snoc _ _)
    refine y.mono ?_
    -- the cost
    have hn := vra_envT_le_sum j cap st.x.length st.tt st.ct it.ctx hcur
    have hVa := vra_valT_le_sum j cap st.x.length st.tt ha
    have hVb := vra_valT_le_sum j cap st.x.length st.tt hb
    have hCa := vra_cnt_le_sum j cap st.x.length st.tt ha
    have hLf : (rowsT j cap st.x.length st.tt it.a).length * valT j cap st.x.length st.tt it.b ≤ Z * Z :=
      Nat.mul_le_mul (by omega) (by omega)
    have hR := vra_roundCost_le (Z := Z) (nr := (rowsFlat j cap st.x.length st.tt).length) (ny := vy.length)
      (nf := vf.length) (M := Z) (Va := valT j cap st.x.length st.tt it.a) (Vb := valT j cap st.x.length st.tt it.b)
      (Ca := (rowsT j cap st.x.length st.tt it.a).length)
      (Lf := (rowsT j cap st.x.length st.tt it.a).length * valT j cap st.x.length st.tt it.b)
      (by omega) (by omega) (by omega) (Nat.le_refl _) (by omega) (by omega) (by omega) hLf hZ2
    obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := vra_pow_facts hZ2
    have hloop : envT j cap st.x.length st.tt st.ct it.ctx * (vra_roundCost (rowsFlat j cap st.x.length st.tt).length
        vy.length vf.length Z (valT j cap st.x.length st.tt it.a) (valT j cap st.x.length st.tt it.b)
        (rowsT j cap st.x.length st.tt it.a).length
        ((rowsT j cap st.x.length st.tt it.a).length * valT j cap st.x.length st.tt it.b) + 2) ≤
        132 * (Z * Z * Z * Z * Z) := by
      rw [Nat.mul_comm]; exact vra_mul_step (by omega) (by omega)
    have hset : valT j cap st.x.length st.tt it.b * (3 * (rowsT j cap st.x.length st.tt it.a).length + 6) ≤
        9 * (Z * Z) := by
      have := Nat.mul_le_mul (show valT j cap st.x.length st.tt it.b ≤ Z by omega)
        (show 3 * (rowsT j cap st.x.length st.tt it.a).length + 6 ≤ 9 * Z by omega)
      rw [Nat.mul_left_comm] at this; exact this
    omega

end Shallot.MacroPeg.Mach
