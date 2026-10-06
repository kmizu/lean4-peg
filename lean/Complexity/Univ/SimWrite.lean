import Complexity.Univ.SimTrav
import Complexity.Univ.Table

/-!
# Writing a cell and moving a head

The body `wrB` of the walk that carries out a row: it reads the symbol to write and the move from the table
(entries `sIW` and `sIM`, both raised by one for the next tape), writes the symbol under the head (`setB`
inside the tape, `padB` past its end), and moves the head (`moveB`).
-/

namespace Complexity.Univ

open Complexity

/-- Write the top of `sA` at cell `p` (top of `sP`) of the tape on `sTT`, inside the tape (length on `sLN`). -/
def setB : NProg UK :=
  .seq (.prim (.dup sLN sC (by decide))) (.seq (.prim (.dec sC)) (.seq (.prim (.dup sP sD (by decide)))
    (.seq (subTo sD sC) (.seq (moveN sC sTT sZ (by decide)) (.seq (.prim (.pop sTT))
      (.seq (nmv sA sTT (by decide)) (nmvAll sZ sTT (by decide))))))))

/-- Write the top of `sA` at cell `p` past the end of the tape: pad with blanks. -/
def padB : NProg UK :=
  .seq (.prim (.dup sP sC (by decide))) (.seq (.prim (.dup sLN sD (by decide))) (.seq (subTo sD sC)
    (.seq (.loop sC .pos (.seq (.prim (.dec sC)) (.prim (.pushZ sTT)))) (.seq (.prim (.pop sC))
      (nmv sA sTT (by decide))))))

/-- Move the head on `sP` by the move code on `sMV` (popped). -/
def moveB : NProg UK :=
  .ite sMV .zero (.seq (.prim (.pop sMV)) (.prim (.dec sP)))
    (.seq (.prim (.dec sMV)) (.ite sMV .zero (.prim (.pop sMV)) (.seq (.prim (.pop sMV)) (.prim (.inc sP)))))

theorem nruns_setB (X : Lists UK) {t : List Nat} {p a : Nat} (hpl : p < t.length) (ht : X sTT = t)
    (hl : X sLN = [t.length]) (hp : X sP = [p]) (ha : X sA = [a]) (hC : X sC = []) (hD : X sD = [])
    (hZ : X sZ = []) :
    NRuns setB X ((X.set sTT (writeAt t p a)).set sA []) (7 * t.length + 3 * p + 20) := by
  obtain ⟨D₁, hD₁, d₁⟩ := NRuns.named (nruns_dup sLN sC (by decide) X (l := []) (v := t.length) hl)
  obtain ⟨D₂, hD₂, d₂⟩ := NRuns.named (nruns_dec sC D₁ (l := []) (v := t.length) (by rw [hD₁]; lat))
  obtain ⟨D₃, hD₃, d₃⟩ := NRuns.named (nruns_dup sP sD (by decide) D₂ (l := []) (v := p) (by rw [hD₂, hD₁]; lat))
  obtain ⟨D₄, hD₄, d₄⟩ := NRuns.named (nruns_subTo sD sC (by decide) D₃ (l := []) (l' := []) (a := p)
    (b := t.length - 1) (by rw [hD₃, hD₂, hD₁]; lat) (by rw [hD₃, hD₂, hD₁]; lat))
  have hsplit : t = t.take (p + 1) ++ t.drop (p + 1) := (List.take_append_drop _ _).symm
  obtain ⟨D₅, hD₅, d₅⟩ := NRuns.named (nruns_moveN sC sTT sZ (by decide) (by decide) (by decide) D₄ (lc := [])
    (n := t.length - 1 - p) (by rw [hD₄]; lat) (l := t.take (p + 1)) (seg := t.drop (p + 1))
    (by rw [hD₄, hD₃, hD₂, hD₁]; simp only [Lists.set_ne _ _ (show sTT ≠ sC by decide),
      Lists.set_ne _ _ (show sTT ≠ sD by decide), ht]; exact hsplit) (by simp; omega))
  clear hsplit
  have htk : t.take (p + 1) = t.take p ++ [t.getD p 0] := take_getD 0 hpl
  obtain ⟨D₆, hD₆, d₆⟩ := NRuns.named (nruns_pop sTT D₅ (l := t.take p) (v := t.getD p 0)
    (by rw [hD₅, ← htk]; lat))
  obtain ⟨D₇, hD₇, d₇⟩ := NRuns.named (nruns_mv sA sTT (by decide) D₆ (l := []) (v := a)
    (by rw [hD₆, hD₅, hD₄, hD₃, hD₂, hD₁]; lat))
  obtain ⟨D₈, hD₈, d₈⟩ := NRuns.named (nruns_mvAll sZ sTT (by decide) D₇)
  have e : D₈ = (X.set sTT (writeAt t p a)).set sA [] := by
    have hw : writeAt t p a = t.take p ++ [a] ++ t.drop (p + 1) := by
      simp only [writeAt, hpl, if_true, List.set_eq_take_append_cons_drop]; simp
    have h₇ : D₇ sTT = t.take p ++ [a] := by rw [hD₇, hD₆]; lat
    have h₇' : D₇ sZ = (t.drop (p + 1)).reverse := by
      rw [hD₇, hD₆, hD₅, hD₄, hD₃, hD₂, hD₁]; (try simp (disch := decide) only [Lists.set, if_pos, if_neg]); simp only [hZ, List.nil_append]
    rw [hD₈, h₇, h₇', List.reverse_reverse, ← hw, hD₇, hD₆, hD₅, hD₄, hD₃, hD₂, hD₁]
    leq
  rw [e] at d₈
  refine (d₁.seq (d₂.seq (d₃.seq (d₄.seq (d₅.seq (d₆.seq (d₇.seq d₈))))))).mono ?_
  have h₇' : D₇ sZ = (t.drop (p + 1)).reverse := by
      rw [hD₇, hD₆, hD₅, hD₄, hD₃, hD₂, hD₁]; (try simp (disch := decide) only [Lists.set, if_pos, if_neg]); simp only [hZ, List.nil_append]
  rw [h₇', List.length_reverse, List.length_drop]
  omega

theorem nruns_padB (X : Lists UK) {t : List Nat} {p a : Nat} (hpl : t.length ≤ p) (ht : X sTT = t)
    (hl : X sLN = [t.length]) (hp : X sP = [p]) (ha : X sA = [a]) (hC : X sC = []) (hD : X sD = []) :
    NRuns padB X ((X.set sTT (writeAt t p a)).set sA []) (6 * p + 3 * t.length + 12) := by
  obtain ⟨D₁, hD₁, d₁⟩ := NRuns.named (nruns_dup sP sC (by decide) X (l := []) (v := p) hp)
  obtain ⟨D₂, hD₂, d₂⟩ := NRuns.named (nruns_dup sLN sD (by decide) D₁ (l := []) (v := t.length)
    (by rw [hD₁]; lat))
  obtain ⟨D₃, hD₃, d₃⟩ := NRuns.named (nruns_subTo sD sC (by decide) D₂ (l := []) (l' := []) (a := t.length)
    (b := p) (by rw [hD₂, hD₁]; lat) (by rw [hD₂, hD₁]; lat))
  let n := p - t.length
  let F : Nat → Lists UK := fun j => (D₃.set sC [n - j]).set sTT (t ++ List.replicate j 0)
  have h0 : F 0 = D₃ := by
    simp only [F, Nat.sub_zero, List.replicate_zero, List.append_nil]
    have h₁ : D₃ sC = [n] := by rw [hD₃]; lat
    have h₂ : D₃ sTT = t := by rw [hD₃, hD₂, hD₁]; lat
    rw [← h₁, ← h₂, Lists.set_get_self, Lists.set_get_self]
  have hl₁ := nruns_family_const (i := sC) (c := .pos) (p := .seq (.prim (.dec sC)) (.prim (.pushZ sTT))) F n 2
    (fun j hj => by
      simp only [F]; rw [Lists.set_ne _ _ (by decide), Lists.set_same, show n - j = (n - j - 1) + 1 by omega]
      rfl)
    (by simp only [F]; rw [Lists.set_ne _ _ (by decide), Lists.set_same, Nat.sub_self]; rfl)
    (fun j hj => by
      obtain ⟨E₁, hE₁, e₁⟩ := NRuns.named (nruns_dec sC (F j) (l := []) (v := n - j) (by simp only [F]; lat))
      obtain ⟨E₂, hE₂, e₂⟩ := NRuns.named (nruns_pushZ sTT E₁)
      have e : E₂ = F (j + 1) := by
        have : E₁ sTT = t ++ List.replicate j 0 := by rw [hE₁]; simp only [F]; lat
        rw [hE₂, this, hE₁]
        simp only [F, List.nil_append, List.replicate_succ', List.append_assoc,
          show n - (j + 1) = n - j - 1 by omega]
        leq
      rw [e] at e₂
      exact e₁.seq e₂)
  rw [h0] at hl₁
  obtain ⟨D₅, hD₅, d₅⟩ := NRuns.named (nruns_pop sC (F n) (l := []) (v := 0)
    (by simp only [F, Nat.sub_self]; lat))
  obtain ⟨D₆, hD₆, d₆⟩ := NRuns.named (nruns_mv sA sTT (by decide) D₅ (l := []) (v := a)
    (by rw [hD₅]; simp only [F]; rw [hD₃, hD₂, hD₁]; lat))
  have e : D₆ = (X.set sTT (writeAt t p a)).set sA [] := by
    have hw : writeAt t p a = t ++ List.replicate n 0 ++ [a] := by
      simp only [writeAt, show ¬ p < t.length by omega, if_false, n]
    have h₅ : D₅ sTT = t ++ List.replicate n 0 := by rw [hD₅]; simp only [F]; lat
    rw [hD₆, h₅, ← hw, hD₅]
    simp only [F]
    rw [hD₃, hD₂, hD₁]
    leq
  rw [e] at d₆
  exact (d₁.seq (d₂.seq (d₃.seq (hl₁.seq (d₅.seq d₆))))).mono (by omega)

theorem nruns_moveB (X : Lists UK) {p m : Nat} (hp : X sP = [p]) (hm : X sMV = [m]) :
    NRuns moveB X ((X.set sMV []).set sP [(Move.ofCode m).apply p]) 6 := by
  match m with
  | 0 =>
    have d₁ := nruns_pop sMV X (l := []) (v := 0) hm
    have d₂ := nruns_dec sP (X.set sMV []) (l := []) (v := p) (by lat)
    exact ((d₁.seq d₂).iteT (by rw [hm]; rfl)).mono (by omega)
  | 1 =>
    have d₁ := nruns_dec sMV X (l := []) (v := 1) hm
    have d₂ := nruns_pop sMV (X.set sMV [0]) (l := []) (v := 0) (by lat)
    have e : (X.set sMV [0]).set sMV [] = (X.set sMV []).set sP [(Move.ofCode 1).apply p] := by
      simp only [Move.ofCode, Move.apply]; rw [← hp]; leq
    rw [e] at d₂
    exact ((d₁.seq (d₂.iteT (by rfl))).iteF (by rw [hm]; rfl)).mono (by omega)
  | m + 2 =>
    have d₁ := nruns_dec sMV X (l := []) (v := m + 2) hm
    have d₂ := nruns_pop sMV (X.set sMV [m + 2 - 1]) (l := []) (v := m + 2 - 1) (by lat)
    have d₃ := nruns_inc sP ((X.set sMV [m + 2 - 1]).set sMV []) (l := []) (v := p) (by lat)
    have e : ((X.set sMV [m + 2 - 1]).set sMV []).set sP ([] ++ [p + 1]) =
        (X.set sMV []).set sP [(Move.ofCode (m + 2)).apply p] := by
      simp only [Move.ofCode, Move.apply]; leq
    rw [e] at d₃
    exact ((d₁.seq ((d₂.seq d₃).iteF (by simp [NTest.eval]))).iteF (by rw [hm]; simp [NTest.eval])).mono
      (by omega)

/-- Carry out the row on one tape. -/
def wrB : NProg UK :=
  .seq (.prim (.dup sIW sX (by decide))) (.seq (peekAt TBL sPT sX sA (by decide) (by decide))
    (.seq (.prim (.dup sIM sX (by decide))) (.seq (peekAt TBL sPT sX sMV (by decide) (by decide))
      (.seq (.prim (.inc sIW)) (.seq (.prim (.inc sIM))
        (.seq (cmpTop sP sLN sT1 sT2 sT3 sF (by decide) (by decide))
          (.seq (.ite sF .zero (.seq (.prim (.pop sF)) setB) (.seq (.prim (.pop sF)) padB))
            (.seq (.prim (.pop sLN)) moveB))))))))

theorem wrB_free : TravFree wrB := by unfold TravFree; decide

/-- The stacks after the row is carried out on one tape. -/
def wrOut (X : Lists UK) (t : List Nat) (p iw im : Nat) (tb : List Nat) : Lists UK :=
  ((((X.set sTT (writeAt t p (tb.getD iw 0))).set sP [(Move.ofCode (tb.getD im 0)).apply p]).set sLN []).set
    sIW [iw + 1]).set sIM [im + 1]

theorem nruns_wrB (X : Lists UK) {t : List Nat} {p iw im : Nat} (ht : X sTT = t) (hp : X sP = [p])
    (hl : X sLN = [t.length]) (hiw : X sIW = [iw]) (him : X sIM = [im]) (hiwl : iw < (X TBL).length)
    (himl : im < (X TBL).length) (hX : X sX = []) (hPT : X sPT = []) (hA : X sA = []) (hMV : X sMV = [])
    (hF : X sF = []) (hC : X sC = []) (hD : X sD = []) (hZ : X sZ = []) :
    NRuns wrB X (wrOut X t p iw im (X TBL))
      (12 * (X TBL).length + 4 * iw + 4 * im + (p + t.length + 1) * (2 * p + 6) + 9 * t.length + 9 * p + 80) := by
  obtain ⟨D₁, hD₁, d₁⟩ := NRuns.named (nruns_dup sIW sX (by decide) X (l := []) (v := iw) hiw)
  have hT₁ : D₁ TBL = X TBL := by rw [hD₁]; lat
  obtain ⟨D₂, hD₂, d₂⟩ := NRuns.named (nruns_peekAt' TBL sPT sX sA (by decide) (by decide) (by decide) D₁
    (by rw [hD₁]; lat) (lc := []) (k := iw) (by rw [hD₁, hX]; lat) (by rw [hT₁]; exact hiwl))
  have hT₂ : D₂ TBL = X TBL := by rw [hD₂]; lat
  obtain ⟨D₃, hD₃, d₃⟩ := NRuns.named (nruns_dup sIM sX (by decide) D₂ (l := []) (v := im)
    (by rw [hD₂, hD₁]; lat))
  have hT₃ : D₃ TBL = X TBL := by rw [hD₃]; lat
  obtain ⟨D₄, hD₄, d₄⟩ := NRuns.named (nruns_peekAt' TBL sPT sX sMV (by decide) (by decide) (by decide) D₃
    (by rw [hD₃, hD₂, hD₁]; lat) (lc := []) (k := im) (by rw [hD₃, hD₂]; lat)
    (by rw [hT₃]; exact himl))
  obtain ⟨D₅, hD₅, d₅⟩ := NRuns.named (nruns_inc sIW D₄ (l := []) (v := iw) (by rw [hD₄, hD₃, hD₂, hD₁]; lat))
  obtain ⟨D₆, hD₆, d₆⟩ := NRuns.named (nruns_inc sIM D₅ (l := []) (v := im)
    (by rw [hD₅, hD₄, hD₃, hD₂, hD₁]; lat))
  have hD₆P : D₆ sP = [p] := by rw [hD₆, hD₅, hD₄, hD₃, hD₂, hD₁]; lat
  have hD₆L : D₆ sLN = [t.length] := by rw [hD₆, hD₅, hD₄, hD₃, hD₂, hD₁]; lat
  have c₁ := nruns_cmpTop sP sLN sT1 sT2 sT3 sF (by decide) (by decide) (by decide) D₆ (li := []) (lj := [])
    (a := p) (b := t.length) hD₆P hD₆L
  have hD₆F : D₆ sF = [] := by rw [hD₆, hD₅, hD₄, hD₃, hD₂, hD₁]; lat
  rw [hD₆F, List.nil_append] at c₁
  have hG : ∀ r, (D₆.set sF [r]).set sF [] = D₆ := fun r => by rw [Lists.set_set_u, ← hD₆F, Lists.set_get_self]
  have hGt : D₆ sTT = t := by rw [hD₆, hD₅, hD₄, hD₃, hD₂, hD₁]; lat
  have hGa' : D₆ sA = [(X TBL).getD iw 0] := by
    have : D₁ sA = [] := by rw [hD₁]; lat
    rw [hD₆, hD₅, hD₄, hD₃, hD₂, this, ← hT₁]; lat
  have hGC : D₆ sC = [] := by rw [hD₆, hD₅, hD₄, hD₃, hD₂, hD₁]; lat
  have hGD : D₆ sD = [] := by rw [hD₆, hD₅, hD₄, hD₃, hD₂, hD₁]; lat
  have hGZ : D₆ sZ = [] := by rw [hD₆, hD₅, hD₄, hD₃, hD₂, hD₁]; lat
  -- write
  obtain ⟨W, hW, w⟩ : ∃ W, W = (D₆.set sTT (writeAt t p ((X TBL).getD iw 0))).set sA [] ∧
      NRuns (.ite sF .zero (.seq (.prim (.pop sF)) setB) (.seq (.prim (.pop sF)) padB)) (D₆.set sF [cmpRes p t.length])
        W (7 * t.length + 6 * p + 23) := by
    refine ⟨_, rfl, ?_⟩
    by_cases hpl : p < t.length
    · have hc : cmpRes p t.length = 0 := by simp [cmpRes, hpl]
      rw [hc]
      have q₁ := nruns_pop sF (D₆.set sF [0]) (l := []) (v := 0) (by simp)
      rw [hG] at q₁
      have q₂ := nruns_setB D₆ hpl hGt hD₆L hD₆P hGa' hGC hGD hGZ
      exact ((q₁.seq q₂).iteT (by rfl)).mono (by omega)
    · have hc : cmpRes p t.length ≠ 0 := by unfold cmpRes; split <;> (try split) <;> omega
      obtain ⟨r, hr⟩ : ∃ r, cmpRes p t.length = r + 1 := ⟨cmpRes p t.length - 1, by omega⟩
      rw [hr]
      have q₁ := nruns_pop sF (D₆.set sF [r + 1]) (l := []) (v := r + 1) (by simp)
      rw [hG] at q₁
      have q₂ := nruns_padB D₆ (by omega) hGt hD₆L hD₆P hGa' hGC hGD
      exact ((q₁.seq q₂).iteF (by simp [NTest.eval])).mono (by omega)
  obtain ⟨D₈, hD₈, d₈⟩ := NRuns.named (nruns_pop sLN W (l := []) (v := t.length) (by rw [hW]; lat))
  have hMV' : D₈ sMV = [(X TBL).getD im 0] := by
    have : D₃ sMV = [] := by rw [hD₃, hD₂, hD₁]; lat
    rw [hD₈, hW, hD₆, hD₅, hD₄, this, ← hT₃]; lat
  have hP' : D₈ sP = [p] := by rw [hD₈, hW]; lat
  obtain ⟨D₉, hD₉, d₉⟩ := NRuns.named (nruns_moveB D₈ hP' hMV')
  have e : D₉ = wrOut X t p iw im (X TBL) := by
    rw [hD₉, hD₈, hW, hD₆, hD₅, hD₄, hD₃, hD₂, hD₁]
    simp only [wrOut, List.nil_append]
    leq
  rw [e] at d₉
  refine (d₁.seq (d₂.seq (d₃.seq (d₄.seq (d₅.seq (d₆.seq (c₁.seq (w.seq (d₈.seq d₉))))))))).mono ?_
  rw [hT₁, hT₃]
  omega

/-! ## Carrying out a row on all tapes -/

def writeP : NProg UK := travP wrB

/-- The tapes after writing `ws`. -/
def nts (ts : List (List Nat)) (ps : List Nat) (ws : List Nat) : List (List Nat) :=
  ((ts.zip ps).zip ws).map fun ((t, p), a) => writeAt t p a

/-- The heads after the moves `ms`. -/
def nps (ps ms : List Nat) : List Nat := (ps.zip ms).map fun (p, m) => (Move.ofCode m).apply p

theorem length_nts {ts : List (List Nat)} {ps ws : List Nat} {k : Nat} (h₁ : ts.length = k) (h₂ : ps.length = k)
    (h₃ : ws.length = k) : (nts ts ps ws).length = k := by simp [nts, h₁, h₂, h₃]

theorem length_nps {ps ms : List Nat} {k : Nat} (h₁ : ps.length = k) (h₂ : ms.length = k) :
    (nps ps ms).length = k := by simp [nps, h₁, h₂]

theorem nts_getD {ts : List (List Nat)} {ps ws : List Nat} {i : Nat} (h₁ : i < ts.length) (h₂ : i < ps.length)
    (h₃ : i < ws.length) : (nts ts ps ws).getD i [] = writeAt (ts.getD i []) (ps.getD i 0) (ws.getD i 0) := by
  have hl : i < (nts ts ps ws).length := by simp [nts]; omega
  rw [← List.getElem_eq_getD (h := hl), ← List.getElem_eq_getD (h := h₁), ← List.getElem_eq_getD (h := h₂),
    ← List.getElem_eq_getD (h := h₃)]
  simp [nts, List.getElem_zip]

theorem nps_getD {ps ms : List Nat} {i : Nat} (h₁ : i < ps.length) (h₂ : i < ms.length) :
    (nps ps ms).getD i 0 = (Move.ofCode (ms.getD i 0)).apply (ps.getD i 0) := by
  have hl : i < (nps ps ms).length := by simp [nps]; omega
  rw [← List.getElem_eq_getD (h := hl), ← List.getElem_eq_getD (h := h₁), ← List.getElem_eq_getD (h := h₂)]
  simp [nps, List.getElem_zip]

theorem length_writeAt_le (t : List Nat) (p a : Nat) : (writeAt t p a).length ≤ t.length + p + 1 := by
  unfold writeAt; split <;> simp <;> omega

/-- **Carrying out a row**: write `ws` and move by `ms`, reading them from the table from `iw₀` and `im₀`. -/
theorem nruns_writeP (S : Lists UK) (ts : List (List Nat)) (ps ws ms : List Nat) (k N iw₀ im₀ : Nat)
    (hts : ts.length = k) (hps : ps.length = k) (hws : ws.length = k) (hms : ms.length = k)
    (hTP : S TP = encTapes ts) (hPOS : S POS = ps) (hIW : S sIW = [iw₀]) (hIM : S sIM = [im₀])
    (hz : ∀ x : Fin UK, x ∈ [sW, sPW, sTT, sP, sLN, sLEN, sTT2, sX, sPT, sA, sMV, sF, sC, sD, sZ] → S x = [])
    (hwt : ∀ i, i < k → (S TBL).getD (iw₀ + i) 0 = ws.getD i 0)
    (hmt : ∀ i, i < k → (S TBL).getD (im₀ + i) 0 = ms.getD i 0)
    (hiwl : iw₀ + k ≤ (S TBL).length) (himl : im₀ + k ≤ (S TBL).length)
    (hN : 1 ≤ N) (hk : k ≤ N) (hE : (encTapes ts).length ≤ N) (hTB : (S TBL).length ≤ N)
    (hb : ∀ i, i < k → (ts.getD i []).length ≤ N ∧ ps.getD i 0 ≤ N) :
    NRuns writeP S ((((S.set TP (encTapes (nts ts ps ws))).set POS (nps ps ms)).set sIW [iw₀ + k]).set
      sIM [im₀ + k]) (400 * cu N) := by
  let O : Nat → Lists UK := fun i => (S.set sIW [iw₀ + i]).set sIM [im₀ + i]
  have hlen₁ := length_nts hts hps hws
  have hlen₂ := length_nps hps hms
  have body : ∀ i, i < k → NRuns wrB (trIn O ts ps i) (trOut O (nts ts ps ws) (nps ps ms) i) (200 * sq N) := by
    intro i hi
    have hTBi : (trIn O ts ps i) TBL = S TBL := by simp only [trIn, O]; lat
    have r := nruns_wrB (trIn O ts ps i) (t := ts.getD i []) (p := ps.getD i 0) (iw := iw₀ + i) (im := im₀ + i)
      (by simp only [trIn]; lat) (by simp only [trIn]; lat) (by simp only [trIn]; lat)
      (by simp only [trIn, O]; lat) (by simp only [trIn, O]; lat) (by rw [hTBi]; omega) (by rw [hTBi]; omega)
      (by simp only [trIn, O]; rw [← hz sX (by decide)]; lat)
      (by simp only [trIn, O]; rw [← hz sPT (by decide)]; lat)
      (by simp only [trIn, O]; rw [← hz sA (by decide)]; lat)
      (by simp only [trIn, O]; rw [← hz sMV (by decide)]; lat)
      (by simp only [trIn, O]; rw [← hz sF (by decide)]; lat)
      (by simp only [trIn, O]; rw [← hz sC (by decide)]; lat)
      (by simp only [trIn, O]; rw [← hz sD (by decide)]; lat)
      (by simp only [trIn, O]; rw [← hz sZ (by decide)]; lat)
    have e : wrOut (trIn O ts ps i) (ts.getD i []) (ps.getD i 0) (iw₀ + i) (im₀ + i) ((trIn O ts ps i) TBL) =
        trOut O (nts ts ps ws) (nps ps ms) i := by
      rw [hTBi]
      simp only [wrOut]
      rw [hwt i hi, hmt i hi]
      simp only [ trIn, trOut, O, nts_getD (show i < ts.length by omega) (show i < ps.length by omega)
        (show i < ws.length by omega), nps_getD (show i < ps.length by omega) (show i < ms.length by omega),
        Nat.add_assoc]
      leq
    rw [e] at r
    refine r.mono ?_
    rw [hTBi]
    obtain ⟨hl, hp⟩ := hb i hi
    have m := mul_le_sq (a := ps.getD i 0 + (ts.getD i []).length + 1) (b := 2 * ps.getD i 0 + 6) (n := N)
      (x := 3) (y := 8) (by omega) (by omega)
    have := n_le_sq hN
    omega
  have tr := nruns_travP wrB wrB_free O ts (nts ts ps ws) ps (nps ps ms) k (200 * sq N) (2 * N + 1) hts hps
    hlen₁ hlen₂ body
    (fun i hi => by
      refine ⟨by have := (hb i hi).1; omega, ?_⟩
      rw [nts_getD (by omega) (by omega) (by omega)]
      have := length_writeAt_le (ts.getD i []) (ps.getD i 0) (ws.getD i 0)
      have := hb i hi
      omega)
    S (by simp only [O, Nat.add_zero]; rw [← hIW, ← hIM, Lists.set_get_self, Lists.set_get_self])
    hTP hPOS (hz _ (by decide)) (hz _ (by decide)) (hz _ (by decide)) (hz _ (by decide)) (hz _ (by decide))
    (hz _ (by decide)) (hz _ (by decide))
  have e : trF O ts (nts ts ps ws) ps (nps ps ms) k =
      (((S.set TP (encTapes (nts ts ps ws))).set POS (nps ps ms)).set sIW [iw₀ + k]).set sIM [im₀ + k] := by
    have h₁ : (nts ts ps ws).take k = nts ts ps ws := List.take_of_length_le (by omega)
    have h₂ : (nps ps ms).take k = nps ps ms := List.take_of_length_le (by omega)
    have h₃ : ts.drop k = [] := List.drop_eq_nil_of_le (by omega)
    have h₄ : ps.drop k = [] := List.drop_eq_nil_of_le (by omega)
    have hW := hz sW (by decide)
    have hPW := hz sPW (by decide)
    have hTT := hz sTT (by decide)
    have hP := hz sP (by decide)
    have hLN := hz sLN (by decide)
    have hLEN := hz sLEN (by decide)
    have hTT2 := hz sTT2 (by decide)
    simp only [trF, O, h₁, h₂, h₃, h₄]
    have : encTapes [] = [] := rfl
    rw [this]
    leq
  rw [e] at tr
  refine tr.mono ?_
  have c₁ := le_cu_of (k := k) (X := 200 * sq N + 11 * (2 * N + 1) + 13) (N := N) (a := 246) hk
    (by have := n_le_sq hN; omega)
  have := n_le_sq hN
  have := sq_le_cu hN
  omega

end Complexity.Univ
