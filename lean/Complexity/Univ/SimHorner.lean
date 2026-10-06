import Complexity.Univ.SimKit

/-!
# The number of the row, capped

With `C` the number of numbers in the table (on `sCC`, `cntCP`), `hornP` computes `min C (q·na^k + rcode na rs)`
from the state `q` and the symbols `rs` read (on `sRD`, last tape on top) by Horner's rule, capping every
intermediate value at `C` (`nruns_hornP`, `hsat_eq`); the capped value tells whether the row exists, since the
table has at most `C` rows.
-/

namespace Complexity.Univ

open Complexity

/-! ## The size of the table -/

def cntCP : NProg UK :=
  .seq (.prim (.pushZ sCC)) (.seq (cnt TBL sZ sCC (by decide)) (nmvAll sZ TBL (by decide)))

theorem nruns_cntCP (S : Lists UK) (hC : S sCC = []) (hZ : S sZ = []) :
    NRuns cntCP S (S.set sCC [(S TBL).length]) (7 * (S TBL).length + 3) := by
  obtain ⟨A₁, hA₁, a₁⟩ := NRuns.named (nruns_pushZ sCC S)
  obtain ⟨A₂, hA₂, a₂⟩ := NRuns.named (nruns_cnt TBL sZ sCC (by decide) (by decide) (by decide) A₁ (lo := [])
    (b := 0) (by rw [hA₁, hC]; lat))
  obtain ⟨A₃, hA₃, a₃⟩ := NRuns.named (nruns_mvAll sZ TBL (by decide) A₂)
  have h₁ : A₁ TBL = S TBL := by rw [hA₁]; lat
  have h₂ : A₁ sZ = [] := by rw [hA₁]; lat
  have e : A₃ = S.set sCC [(S TBL).length] := by
    have hA₂' : A₂ = ((A₁.set sZ (S TBL).reverse).set TBL []).set sCC [(S TBL).length] := by
      rw [hA₂, h₁, h₂]; simp
    have h₃ : A₂ sZ = (S TBL).reverse := by rw [hA₂']; lat
    have h₄ : A₂ TBL = [] := by rw [hA₂']; lat
    rw [hA₃, h₃, h₄, List.reverse_reverse, List.nil_append, hA₂', hA₁, hC]
    leq
  rw [e] at a₃
  refine (a₁.seq (a₂.seq a₃)).mono ?_
  have h₃ : A₂ sZ = (S TBL).reverse := by rw [hA₂, h₁, h₂]; lat
  rw [h₃, h₁, List.length_reverse]; omega

/-! ## Repeated subtraction -/

/-- Lower the top of `sRM` by the top of `sV`, as many times as the top of `sCN` says. -/
def repSubP : NProg UK :=
  .loop sCN .pos (.seq (.prim (.dec sCN)) (.seq (.prim (.dup sV sX (by decide))) (subTo sX sRM)))

theorem nruns_repSubP (X : Lists UK) {n v r : Nat} {lv : List Nat} (hN : X sCN = [n]) (hV : X sV = lv ++ [v])
    (hR : X sRM = [r]) (hX : X sX = []) :
    NRuns repSubP X ((X.set sCN [0]).set sRM [r - n * v]) (n * (3 * v + 5) + 1) := by
  let F : Nat → Lists UK := fun j => (X.set sCN [n - j]).set sRM [r - j * v]
  have h0 : F 0 = X := by
    simp only [F, Nat.sub_zero, Nat.zero_mul]
    rw [← hN, ← hR, Lists.set_get_self, Lists.set_get_self]
  have hl := nruns_family_const (i := sCN) (c := .pos) F n (3 * v + 4)
    (p := .seq (.prim (.dec sCN)) (.seq (.prim (.dup sV sX (by decide))) (subTo sX sRM)))
    (fun j hj => by
      simp only [F]; rw [Lists.set_ne _ _ (by decide), Lists.set_same, show n - j = (n - j - 1) + 1 by omega]
      rfl)
    (by simp only [F]; rw [Lists.set_ne _ _ (by decide), Lists.set_same, Nat.sub_self]; rfl)
    (fun j hj => by
      obtain ⟨D₁, hD₁, d₁⟩ := NRuns.named (nruns_dec sCN (F j) (l := []) (v := n - j)
        (by simp only [F]; lat))
      obtain ⟨D₂, hD₂, d₂⟩ := NRuns.named (nruns_dup sV sX (by decide) D₁ (l := lv) (v := v)
        (by rw [hD₁]; simp only [F]; lat))
      obtain ⟨D₃, hD₃, d₃⟩ := NRuns.named (nruns_subTo sX sRM (by decide) D₂ (l := []) (l' := []) (a := v)
        (b := r - j * v) (by rw [hD₂, hD₁]; simp only [F]; lat) (by rw [hD₂, hD₁]; simp only [F]; lat))
      have e : D₃ = F (j + 1) := by
        rw [hD₃, hD₂, hD₁]
        simp only [F, List.nil_append]
        rw [show r - (j + 1) * v = r - j * v - v by rw [Nat.succ_mul, Nat.sub_add_eq],
          show n - (j + 1) = n - j - 1 by omega]
        leq
      rw [e] at d₃
      exact (d₁.seq (d₂.seq d₃)).mono (by omega))
  rw [h0] at hl
  have e : F n = (X.set sCN [0]).set sRM [r - n * v] := by simp only [F, Nat.sub_self]
  rw [e] at hl
  exact hl.mono (by rw [Nat.mul_succ]; omega)

/-! ## Horner's rule, capped -/

/-- One capped Horner step. -/
def hstep (C na v d : Nat) : Nat := C - (C - na * v - d)

/-- Capped Horner's rule. -/
def hsat (C na v : Nat) (ds : List Nat) : Nat := ds.foldl (hstep C na) v

/-- Start: `min C q` on `sV`. -/
def hInitP : NProg UK :=
  .seq (.prim (.dup sCC sRM (by decide))) (.seq (.prim (.dup ST sX (by decide))) (.seq (subTo sX sRM)
    (.seq (.prim (.dup sCC sV (by decide))) (subTo sRM sV))))

/-- One step, with the digit popped off `sRD`. -/
def hStepP : NProg UK :=
  .seq (.prim (.dup sCC sRM (by decide))) (.seq (.prim (.dup NA sCN (by decide))) (.seq repSubP
    (.seq (.prim (.pop sCN)) (.seq (subTo sRD sRM) (.seq (.prim (.pop sV))
      (.seq (.prim (.dup sCC sV (by decide))) (subTo sRM sV)))))))

def hornP : NProg UK := .seq hInitP (.loop sRD .nonempty hStepP)

theorem nruns_hInitP (X : Lists UK) {q C : Nat} (hQ : X ST = [q]) (hC : X sCC = [C]) (hR : X sRM = [])
    (hX : X sX = []) (hV : X sV = []) :
    NRuns hInitP X (X.set sV [C - (C - q)]) (3 * q + 3 * C + 7) := by
  obtain ⟨D₁, hD₁, d₁⟩ := NRuns.named (nruns_dup sCC sRM (by decide) X (l := []) (v := C) hC)
  obtain ⟨D₂, hD₂, d₂⟩ := NRuns.named (nruns_dup ST sX (by decide) D₁ (l := []) (v := q) (by rw [hD₁]; lat))
  obtain ⟨D₃, hD₃, d₃⟩ := NRuns.named (nruns_subTo sX sRM (by decide) D₂ (l := []) (l' := []) (a := q) (b := C)
    (by rw [hD₂, hD₁]; lat) (by rw [hD₂, hD₁]; lat))
  obtain ⟨D₄, hD₄, d₄⟩ := NRuns.named (nruns_dup sCC sV (by decide) D₃ (l := []) (v := C)
    (by rw [hD₃, hD₂, hD₁]; lat))
  obtain ⟨D₅, hD₅, d₅⟩ := NRuns.named (nruns_subTo sRM sV (by decide) D₄ (l := []) (l' := []) (a := C - q) (b := C)
    (by rw [hD₄, hD₃, hD₂, hD₁]; lat) (by rw [hD₄, hD₃, hD₂, hD₁]; lat))
  have e : D₅ = X.set sV [C - (C - q)] := by
    rw [hD₅, hD₄, hD₃, hD₂, hD₁]; simp only [List.nil_append]; leq
  rw [e] at d₅
  exact (d₁.seq (d₂.seq (d₃.seq (d₄.seq d₅)))).mono (by omega)

theorem nruns_hStepP (X : Lists UK) {na C v d : Nat} {lr : List Nat} (hNA : X NA = [na]) (hC : X sCC = [C])
    (hV : X sV = [v]) (hD : X sRD = lr ++ [d]) (hR : X sRM = []) (hX : X sX = []) (hN : X sCN = []) :
    NRuns hStepP X ((X.set sRD lr).set sV [hstep C na v d]) (na * (3 * v + 5) + 3 * d + 3 * C + 14) := by
  obtain ⟨D₁, hD₁, d₁⟩ := NRuns.named (nruns_dup sCC sRM (by decide) X (l := []) (v := C) hC)
  obtain ⟨D₂, hD₂, d₂⟩ := NRuns.named (nruns_dup NA sCN (by decide) D₁ (l := []) (v := na) (by rw [hD₁]; lat))
  obtain ⟨D₃, hD₃, d₃⟩ := NRuns.named (nruns_repSubP D₂ (n := na) (v := v) (r := C) (lv := [])
    (by rw [hD₂, hD₁]; lat) (by rw [hD₂, hD₁]; lat) (by rw [hD₂, hD₁]; lat) (by rw [hD₂, hD₁]; lat))
  obtain ⟨D₄, hD₄, d₄⟩ := NRuns.named (nruns_pop sCN D₃ (l := []) (v := 0) (by rw [hD₃]; lat))
  obtain ⟨D₅, hD₅, d₅⟩ := NRuns.named (nruns_subTo sRD sRM (by decide) D₄ (l := lr) (l' := []) (a := d)
    (b := C - na * v) (by rw [hD₄, hD₃, hD₂, hD₁]; lat) (by rw [hD₄, hD₃]; lat))
  obtain ⟨D₆, hD₆, d₆⟩ := NRuns.named (nruns_pop sV D₅ (l := []) (v := v)
    (by rw [hD₅, hD₄, hD₃, hD₂, hD₁]; lat))
  obtain ⟨D₇, hD₇, d₇⟩ := NRuns.named (nruns_dup sCC sV (by decide) D₆ (l := []) (v := C)
    (by rw [hD₆, hD₅, hD₄, hD₃, hD₂, hD₁]; lat))
  obtain ⟨D₈, hD₈, d₈⟩ := NRuns.named (nruns_subTo sRM sV (by decide) D₇ (l := []) (l' := [])
    (a := C - na * v - d) (b := C) (by rw [hD₇, hD₆, hD₅]; lat) (by rw [hD₇, hD₆]; lat))
  have e : D₈ = (X.set sRD lr).set sV [hstep C na v d] := by
    rw [hD₈, hD₇, hD₆, hD₅, hD₄, hD₃, hD₂, hD₁]; simp only [List.nil_append, hstep]; leq
  rw [e] at d₈
  refine (d₁.seq (d₂.seq (d₃.seq (d₄.seq (d₅.seq (d₆.seq (d₇.seq d₈))))))).mono ?_
  have : C - na * v - d ≤ C := by omega
  omega

theorem hsat_snoc (C na v : Nat) (ds : List Nat) (d : Nat) : hsat C na v (ds ++ [d]) = hstep C na (hsat C na v ds) d := by
  simp [hsat, List.foldl_append]

/-- **Horner's rule on the stacks**: the digits on `sRD` (top first) are taken in. -/
theorem nruns_hornP (S : Lists UK) {q na C : Nat} (rs : List Nat) (N : Nat) (hQ : S ST = [q]) (hNA : S NA = [na])
    (hC : S sCC = [C]) (hD : S sRD = rs) (hR : S sRM = []) (hX : S sX = []) (hV : S sV = []) (hN : S sCN = [])
    (hN1 : 1 ≤ N) (hq : q ≤ N) (hna : na ≤ N) (hCN : C ≤ N) (hk : rs.length ≤ N) (hrs : ∀ d ∈ rs, d ≤ N) :
    NRuns hornP S ((S.set sRD []).set sV [hsat C na (C - (C - q)) rs.reverse]) (50 * cu N) := by
  have i₁ := nruns_hInitP S hQ hC hR hX hV
  let k := rs.length
  let F : Nat → Lists UK := fun j =>
    (S.set sRD (rs.take (k - j))).set sV [hsat C na (C - (C - q)) (rs.reverse.take j)]
  have h0 : F 0 = S.set sV [C - (C - q)] := by
    simp only [F, Nat.sub_zero, List.take_zero, k, List.take_length]
    simp only [hsat, List.foldl_nil]
    rw [← hD]; leq
  have hFD : ∀ j, F j sRD = rs.take (k - j) := fun j => by simp only [F]; lat
  have hl := nruns_family_const (i := sRD) (c := .nonempty) (p := hStepP) F k (14 * sq N + 14)
    (fun j hj => by rw [hFD]; exact eval_nonempty_ne (List.ne_nil_of_length_pos (by simp; omega)))
    (by rw [hFD, Nat.sub_self]; rfl)
    (fun j hj => by
      obtain ⟨r, hr⟩ : ∃ r, k - j = r + 1 := ⟨k - j - 1, by omega⟩
      have hrl : r < rs.length := by omega
      have ht : rs.take (r + 1) = rs.take r ++ [rs[r]] := List.take_succ_eq_append_getElem hrl
      have hv : hsat C na (C - (C - q)) (rs.reverse.take j) ≤ C := by
        cases j with
        | zero => simp only [hsat, List.take_zero, List.foldl_nil]; omega
        | succ j' =>
          have hj' : j' < rs.reverse.length := by simp; omega
          rw [take_getD 0 hj', hsat_snoc]; simp only [hstep]; omega
      have st := nruns_hStepP (F j) (na := na) (C := C) (v := hsat C na (C - (C - q)) (rs.reverse.take j))
        (d := rs[r]) (lr := rs.take r) (by simp only [F]; lat) (by simp only [F]; lat) (by simp only [F]; lat)
        (by rw [hFD, hr, ht]) (by simp only [F]; lat) (by simp only [F]; lat) (by simp only [F]; lat)
      have e : ((F j).set sRD (rs.take r)).set sV [hstep C na (hsat C na (C - (C - q)) (rs.reverse.take j)) rs[r]] =
          F (j + 1) := by
        have hj : j < rs.reverse.length := by simp; omega
        have hrev : rs.reverse.getD j 0 = rs[r] := by
          rw [← List.getElem_eq_getD (h := hj) 0, List.getElem_reverse]; congr 1; omega
        simp only [F, take_getD 0 hj, hsat_snoc, hrev, show k - (j + 1) = r by omega]
        leq
      rw [e] at st
      refine st.mono ?_
      have hd : rs[r] ≤ N := hrs _ (List.getElem_mem hrl)
      have m := mul_le_sq (a := na) (b := 3 * hsat C na (C - (C - q)) (rs.reverse.take j) + 5) (n := N) (x := 1)
        (y := 8) (by omega) (by omega)
      have := n_le_sq hN1
      omega)
  rw [h0] at hl
  have hF : F k = (S.set sRD []).set sV [hsat C na (C - (C - q)) rs.reverse] := by
    simp only [F, Nat.sub_self, List.take_zero, k]
    rw [show rs.length = rs.reverse.length by simp, List.take_length]
  rw [hF] at hl
  refine (i₁.seq hl).mono ?_
  have c₁ := le_cu_of (k := k) (X := 14 * sq N + 14 + 1) (N := N) (a := 29) hk
    (by have := n_le_sq hN1; omega)
  have := n_le_sq hN1
  have := sq_le_cu hN1
  omega

/-! ## The arithmetic -/

/-- Horner's rule without caps. -/
def hexact (na v : Nat) (ds : List Nat) : Nat := ds.foldl (fun v d => na * v + d) v

theorem hstep_min (C na v d : Nat) : hstep C na (min C v) d = min C (na * v + d) := by
  simp only [hstep]
  by_cases hv : v ≤ C
  · rw [Nat.min_eq_right hv]; omega
  · rw [Nat.min_eq_left (by omega)]
    cases na with
    | zero => simp only [Nat.zero_mul, Nat.sub_zero, Nat.min_def]; split <;> omega
    | succ m =>
      have h₁ : (m + 1) * C ≥ C := Nat.le_mul_of_pos_left C (by omega)
      have h₂ : (m + 1) * v ≥ C := Nat.le_trans (by omega) (Nat.le_mul_of_pos_left v (by omega))
      omega

theorem hsat_min (C na : Nat) : ∀ (ds : List Nat) (v : Nat), hsat C na (min C v) ds = min C (hexact na v ds)
  | [], v => by simp [hsat, hexact]
  | d :: ds, v => by
    simp only [hsat, hexact, List.foldl_cons] at *
    rw [hstep_min]
    exact hsat_min C na ds _

theorem hexact_reverse (na q : Nat) : ∀ rs : List Nat, hexact na q rs.reverse = q * na ^ rs.length + rcode na rs
  | [] => by simp [hexact, rcode]
  | a :: rs => by
    have ih := hexact_reverse na q rs
    simp only [hexact] at ih
    simp only [List.reverse_cons, hexact, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih]
    simp only [rcode, List.length_cons, Nat.pow_succ, Nat.mul_add]
    have : na * (q * na ^ rs.length) = q * (na ^ rs.length * na) := by
      rw [Nat.mul_left_comm, Nat.mul_comm na]
    omega

/-- **The capped number of the row.** -/
theorem hsat_eq (C na q : Nat) (rs : List Nat) :
    hsat C na (C - (C - q)) rs.reverse = min C (q * na ^ rs.length + rcode na rs) := by
  rw [show C - (C - q) = min C q by omega, hsat_min, hexact_reverse]

end Complexity.Univ
