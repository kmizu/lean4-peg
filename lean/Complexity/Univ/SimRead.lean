import Complexity.Univ.SimTrav

/-!
# Reading the symbols under the heads

`readP` walks over the tapes and pushes the symbol under every head on `sRD` (tape `0` first), blank `0` past
the end of a tape (`nruns_readP`).
-/

namespace Complexity.Univ

open Complexity

/-- Push the symbol of the tape on `sTT` under the head on `sP` on `sRD`, and pop the length on `sLN`. -/
def rdB : NProg UK :=
  .seq (cmpTop sP sLN sT1 sT2 sT3 sF (by decide) (by decide))
    (.seq (.ite sF .zero (.seq (.prim (.pop sF)) (.seq (.prim (.dup sP sX (by decide)))
        (peekAt sTT sPT sX sRD (by decide) (by decide))))
      (.seq (.prim (.pop sF)) (.prim (.pushZ sRD))))
    (.prim (.pop sLN)))

def readP : NProg UK := travP rdB

/-- The symbols under the heads. -/
def rdl (ps : List Nat) (ts : List (List Nat)) : List Nat := (ps.zip ts).map fun (p, t) => t.getD p 0

theorem rdB_free : TravFree rdB := by unfold TravFree; decide

theorem nruns_rdB (X : Lists UK) {t : List Nat} {p : Nat} (ht : X sTT = t) (hp : X sP = [p])
    (hl : X sLN = [t.length]) (h₁ : X sF = []) (h₂ : X sX = []) (h₃ : X sPT = []) :
    NRuns rdB X ((X.set sRD (X sRD ++ [t.getD p 0])).set sLN [])
      ((p + t.length + 1) * (2 * p + 6) + 6 * t.length + 4 * p + 31) := by
  have c₁ := nruns_cmpTop sP sLN sT1 sT2 sT3 sF (by decide) (by decide) (by decide) X (li := []) (lj := [])
    (a := p) (b := t.length) hp hl
  rw [h₁, List.nil_append] at c₁
  by_cases hpl : p < t.length
  · have hc : cmpRes p t.length = 0 := by simp [cmpRes, hpl]
    rw [hc] at c₁
    obtain ⟨D₁, hD₁, d₁⟩ := NRuns.named (nruns_pop sF (X.set sF [0]) (l := []) (v := 0) (by simp))
    obtain ⟨D₂, hD₂, d₂⟩ := NRuns.named (nruns_dup sP sX (by decide) D₁ (l := []) (v := p) (by rw [hD₁]; lat))
    have hs : D₂ sTT = t := by rw [hD₂, hD₁]; lat
    obtain ⟨D₃, hD₃, d₃⟩ := NRuns.named (nruns_peekAt' sTT sPT sX sRD (by decide) (by decide) (by decide)
      D₂ (by rw [hD₂, hD₁]; lat) (lc := []) (k := p) (by rw [hD₂, hD₁]; lat) (by rw [hs]; exact hpl))
    obtain ⟨D₄, hD₄, d₄⟩ := NRuns.named (nruns_pop sLN D₃ (l := []) (v := t.length) (by rw [hD₃, hD₂, hD₁]; lat))
    have br := (d₁.seq (d₂.seq d₃)).iteT (i := sF) (c := .zero)
      (q := .seq (.prim (.pop sF)) (.prim (.pushZ sRD))) (by rfl)
    have all := c₁.seq (br.seq d₄)
    have e : D₄ = (X.set sRD (X sRD ++ [t.getD p 0])).set sLN [] := by
      have hr : D₂ sRD = X sRD := by rw [hD₂, hD₁]; lat
      rw [hD₄, hD₃, hs, hr, hD₂, hD₁]
      leq
    rw [e] at all
    refine all.mono ?_
    rw [hs]
    omega
  · have hc : cmpRes p t.length ≠ 0 := by unfold cmpRes; split <;> (try split) <;> omega
    obtain ⟨r, hr⟩ : ∃ r, cmpRes p t.length = r + 1 := ⟨cmpRes p t.length - 1, by omega⟩
    rw [hr] at c₁
    obtain ⟨D₁, hD₁, d₁⟩ := NRuns.named (nruns_pop sF (X.set sF [r + 1]) (l := []) (v := r + 1) (by simp))
    obtain ⟨D₂, hD₂, d₂⟩ := NRuns.named (nruns_pushZ sRD D₁)
    obtain ⟨D₄, hD₄, d₄⟩ := NRuns.named (nruns_pop sLN D₂ (l := []) (v := t.length) (by rw [hD₂, hD₁]; lat))
    have br := (d₁.seq d₂).iteF (i := sF) (c := .zero)
      (p := .seq (.prim (.pop sF)) (.seq (.prim (.dup sP sX (by decide)))
        (peekAt sTT sPT sX sRD (by decide) (by decide)))) (by simp [NTest.eval])
    have all := c₁.seq (br.seq d₄)
    have hv : t.getD p 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    have e : D₄ = (X.set sRD (X sRD ++ [t.getD p 0])).set sLN [] := by
      have hr : D₁ sRD = X sRD := by rw [hD₁]; lat
      rw [hD₄, hD₂, hr, hv, hD₁]
      leq
    rw [e] at all
    refine all.mono ?_
    omega

theorem rdl_take_succ {ps : List Nat} {ts : List (List Nat)} {i : Nat} (hp : i < ps.length) (ht : i < ts.length) :
    (rdl ps ts).take (i + 1) = (rdl ps ts).take i ++ [(ts.getD i []).getD (ps.getD i 0) 0] := by
  have hl : i < (rdl ps ts).length := by simp [rdl]; omega
  rw [take_getD 0 hl]
  congr 2
  rw [← List.getElem_eq_getD (h := hl) 0, ← List.getElem_eq_getD (h := hp) 0, ← List.getElem_eq_getD (h := ht) []]
  simp [rdl, List.getElem_zip]

theorem length_rdl {ps : List Nat} {ts : List (List Nat)} {k : Nat} (hp : ps.length = k) (ht : ts.length = k) :
    (rdl ps ts).length = k := by simp [rdl, hp, ht]

/-- **Reading the symbols under the heads.** -/
theorem nruns_readP (S : Lists UK) (ts : List (List Nat)) (ps : List Nat) (k N : Nat) (hts : ts.length = k)
    (hps : ps.length = k) (hTP : S TP = encTapes ts) (hPOS : S POS = ps) (hs : UScratch S) (hN : 1 ≤ N)
    (hk : k ≤ N) (hE : (encTapes ts).length ≤ N)
    (hb : ∀ i, i < k → (ts.getD i []).length ≤ N ∧ ps.getD i 0 ≤ N) :
    NRuns readP S (S.set sRD (rdl ps ts)) (200 * cu N) := by
  have z : ∀ x : Fin UK, 7 ≤ x.val → S x = [] := hs
  have zF := z sF (by decide)
  have zX := z sX (by decide)
  have zPT := z sPT (by decide)
  have zRD := z sRD (by decide)
  let O : Nat → Lists UK := fun i => S.set sRD ((rdl ps ts).take i)
  have body : ∀ i, i < k → NRuns rdB (trIn O ts ps i) (trOut O ts ps i) (100 * sq N) := by
    intro i hi
    have r := nruns_rdB (trIn O ts ps i) (t := ts.getD i []) (p := ps.getD i 0) (by simp only [trIn]; lat)
      (by simp only [trIn]; lat) (by simp only [trIn]; lat) (by simp only [trIn, O]; lat)
      (by simp only [trIn, O]; lat) (by simp only [trIn, O]; lat)
    have e : ((trIn O ts ps i).set sRD ((trIn O ts ps i) sRD ++ [(ts.getD i []).getD (ps.getD i 0) 0])).set sLN [] =
        trOut O ts ps i := by
      have h₁ : (trIn O ts ps i) sRD = (rdl ps ts).take i := by simp only [trIn, O]; lat
      rw [h₁]
      simp only [trIn, trOut, O, rdl_take_succ (show i < ps.length by omega) (show i < ts.length by omega)]
      leq
    rw [e] at r
    refine r.mono ?_
    obtain ⟨hl, hp⟩ := hb i hi
    have m := mul_le_sq (a := ps.getD i 0 + (ts.getD i []).length + 1) (b := 2 * ps.getD i 0 + 6) (n := N)
      (x := 3) (y := 8) (by omega) (by omega)
    have := n_le_sq hN
    omega
  have tr := nruns_travP rdB rdB_free O ts ts ps ps k (100 * sq N) N hts hps hts hps body
    (fun i hi => ⟨(hb i hi).1, (hb i hi).1⟩) S (by simp only [O, List.take_zero]; rw [← zRD, Lists.set_get_self])
    hTP hPOS (z _ (by decide)) (z _ (by decide)) (z _ (by decide)) (z _ (by decide)) (z _ (by decide))
    (z _ (by decide)) (z _ (by decide))
  have e : trF O ts ts ps ps k = S.set sRD (rdl ps ts) := by
    have h₁ : ts.take k = ts := List.take_of_length_le (by omega)
    have h₂ : ps.take k = ps := List.take_of_length_le (by omega)
    have h₃ : ts.drop k = [] := List.drop_eq_nil_of_le (by omega)
    have h₄ : ps.drop k = [] := List.drop_eq_nil_of_le (by omega)
    have h₅ : (rdl ps ts).take k = rdl ps ts := List.take_of_length_le (by rw [length_rdl hps hts]; exact Nat.le_refl _)
    have hW := z sW (by decide)
    have hPW := z sPW (by decide)
    have hTT := z sTT (by decide)
    have hP := z sP (by decide)
    have hLN := z sLN (by decide)
    have hLEN := z sLEN (by decide)
    have hTT2 := z sTT2 (by decide)
    simp only [trF, O, h₁, h₂, h₃, h₄, h₅, ← hTP, ← hPOS]
    have : encTapes [] = [] := rfl
    rw [this]
    leq
  rw [e] at tr
  refine tr.mono ?_
  have c₁ := le_cu_of (k := k) (X := 100 * sq N + 11 * N + 13) (N := N) (a := 124) hk
    (by have := n_le_sq hN; omega)
  have := n_le_sq hN
  have := sq_le_cu hN
  omega

end Complexity.Univ
