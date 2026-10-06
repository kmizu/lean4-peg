import Complexity.Univ.SimLook
import Complexity.Univ.SimRead
import Complexity.Univ.SimRows

/-!
# One simulated step

`stepP` carries out `fstep T` on the configuration on the stacks (`stepP_runs`): it leaves halted
configurations alone; otherwise it reads the symbols under the heads (`readP`), computes the number of the row
capped at the size `C` of the table (`cntCP`, `hornP`), checks that the row exists (`offP`), and carries it out
(`rowP`).
-/

namespace Complexity.Univ

open Complexity

def mainP : NProg UK :=
  .seq readP (.seq cntCP (.seq hornP (.seq offP (.seq (.ite sRM .pos rowP (.prim (.pop sRM)))
    (.seq (.prim (.pop sV)) (.prim (.pop sCC)))))))

def stepP : NProg UK :=
  .seq (.prim (.dup ST sX (by decide))) (.ite sX .zero (.prim (.pop sX)) (.seq (.prim (.dec sX))
    (.ite sX .zero (.prim (.pop sX)) (.seq (.prim (.pop sX)) mainP))))

/-- The size bound of a step. -/
def nB (T : TTable) (c : FCfg) : Nat := tsz T + csz c + 2

theorem putCfg_self {S : Lists UK} {T : TTable} {c : FCfg} (h : SimSt S T c) : putCfg S c = S := by
  obtain ⟨_, _, _, h₁, h₂, h₃⟩ := h
  simp only [putCfg]; rw [← h₁, ← h₂, ← h₃, Lists.set_get_self, Lists.set_get_self, Lists.set_get_self]

theorem fstep_halted {T : TTable} {c : FCfg} (h : c.state = 0 ∨ c.state = 1) : fstep T c = c := by
  simp [fstep, h]

theorem fstep_none {T : TTable} {c : FCfg} (h₁ : ¬ (c.state = 0 ∨ c.state = 1))
    (h₂ : T.rows[T.idx c.state c.reads]? = none) : fstep T c = c := by
  simp only [fstep, h₁, if_false, h₂]

theorem fstep_some {T : TTable} {c : FCfg} {r : Row} (h₁ : ¬ (c.state = 0 ∨ c.state = 1))
    (h₂ : T.rows[T.idx c.state c.reads]? = some r) :
    fstep T c = { state := r.1, pos := nps c.pos r.2.2, tapes := nts c.tapes c.pos r.2.1 } := by
  simp only [fstep, h₁, if_false, h₂]; rfl

theorem fstep_ok {T : TTable} (hT : RowsOK T) {c : FCfg} (hc : CfgOK T c) : CfgOK T (fstep T c) := by
  unfold fstep
  split
  · exact hc
  · split
    · exact hc
    · rename_i q ws ms h
      have hr := hT _ (List.mem_of_getElem? h)
      simp only at hr
      constructor
      · simp [hc.1, hr.2]
      · simp [hc.1, hc.2, hr.1]

/-- The stacks a step uses, apart from scratch. -/
theorem tsz_facts (T : TTable) : (encRows T.rows).length ≤ tsz T ∧ T.k ≤ tsz T ∧ T.na ≤ tsz T := by
  simp only [tsz]; omega

theorem mainP_runs (T : TTable) (hT : RowsOK T) (c : FCfg) (hc : CfgOK T c) (S : Lists UK) (hS : SimSt S T c)
    (hs : UScratch S) (hq : ¬ (c.state = 0 ∨ c.state = 1)) :
    NRuns mainP S (putCfg S (fstep T c)) (800 * cu (nB T c)) := by
  obtain ⟨hTBL, hKS, hNA, hST, hPOS, hTP⟩ := hS
  have z : ∀ x : Fin UK, 7 ≤ x.val → S x = [] := hs
  generalize hNdef : nB T c = N
  have hN1 : 1 ≤ N := by rw [← hNdef]; simp only [nB]; omega
  obtain ⟨tf₁, tf₂, tf₃⟩ := tsz_facts T
  have hcN : csz c + tsz T + 2 = N := by rw [← hNdef]; simp only [nB]; omega
  have hqN : c.state ≤ N := by simp only [csz] at hcN; omega
  have hEN : (encTapes c.tapes).length ≤ N := by simp only [csz] at hcN; omega
  have hk : c.tapes.length = T.k := hc.2
  have hkp : c.pos.length = T.k := hc.1
  have hb : ∀ i, i < T.k → (c.tapes.getD i []).length ≤ N ∧ c.pos.getD i 0 ≤ N := fun i hi =>
    ⟨by have := tape_len_le c (i := i) (by omega); omega, by have := pos_le c i; omega⟩
  -- read
  have r₁ := nruns_readP S c.tapes c.pos T.k N hk hkp hTP hPOS hs hN1 (by omega) hEN hb
  generalize hrs : rdl c.pos c.tapes = rs at r₁
  have hrs' : rs = c.reads := by rw [← hrs]; rfl
  -- the size of the table
  have r₂ := nruns_cntCP (S.set sRD rs) (by rw [← z sCC (by decide)]; lat) (by rw [← z sZ (by decide)]; lat)
  have hTB : (S.set sRD rs) TBL = encRows T.rows := by rw [← hTBL]; lat
  rw [hTB] at r₂
  generalize hC : (encRows T.rows).length = C at r₂
  -- the number of the row
  have hlr : rs.length = T.k := by rw [hrs']; exact length_reads hc
  have r₃ := nruns_hornP ((S.set sRD rs).set sCC [C]) (q := c.state) (na := T.na) (C := C) rs N
    (by rw [← hST]; lat) (by rw [← hNA]; lat) (by lat) (by lat) (by rw [← z sRM (by decide)]; lat)
    (by rw [← z sX (by decide)]; lat) (by rw [← z sV (by decide)]; lat) (by rw [← z sCN (by decide)]; lat)
    hN1 hqN (by omega) (by omega) (by omega)
    (fun d hd => by rw [hrs'] at hd; have := reads_le c hd; omega)
  generalize hV : hsat C T.na (C - (C - c.state)) rs.reverse = V at r₃
  have hVi : V = min C (T.idx c.state c.reads) := by
    rw [← hV, hsat_eq, hlr, hrs']; rfl
  -- the offset
  have r₄ := nruns_offP (((S.set sRD rs).set sCC [C]).set sRD [] |>.set sV [V]) (C := C) (k := T.k) (V := V)
    (by lat) (by rw [← hKS]; lat) (by lat) (by rw [← z sRM (by decide)]; lat)
    (by rw [← z sCN (by decide)]; lat) (by rw [← z sX (by decide)]; lat)
  generalize hS₄ : (((((S.set sRD rs).set sCC [C]).set sRD []).set sV [V])).set sRM
    [C - (2 * T.k + 1) * V] = S₄ at r₄
  have hCR : C = T.rows.length * (2 * T.k + 1) := by rw [← hC]; exact length_encRows hT
  have hVle : V ≤ C := by omega
  have hoffN : (2 * T.k + 1) * V ≤ C ∨ C < (2 * T.k + 1) * V := by omega
  -- the end: pop the capped number and the size
  have fin : ∀ (S₅ : Lists UK) (S' : Lists UK), S₅ = (S'.set sV [V]).set sCC [C] →
      NRuns (.seq (.prim (.pop sV)) (.prim (.pop sCC))) S₅ ((S'.set sV []).set sCC []) 2 := by
    intro S₅ S' h
    have p₁ := nruns_pop sV S₅ (l := []) (v := V) (by rw [h]; lat)
    have p₂ := nruns_pop sCC (S₅.set sV []) (l := []) (v := C) (by rw [h]; lat)
    have e : (S₅.set sV []).set sCC [] = (S'.set sV []).set sCC [] := by rw [h]; leq
    rw [e] at p₂
    exact p₁.seq p₂
  have costs : 200 * cu N + (7 * C + 3) + 50 * cu N + ((2 * T.k + 1) * (3 * V + 5) + 3 * T.k + 10) + 1 +
      500 * cu N + 2 ≤ 800 * cu N := by
    have m := mul_le_sq (a := 2 * T.k + 1) (b := 3 * V + 5) (n := N) (x := 3) (y := 8) (by omega) (by omega)
    have := n_le_sq hN1
    have := sq_le_cu hN1
    omega
  by_cases hroom : (2 * T.k + 1) * V < C
  · -- the row exists
    have hVR : V < T.rows.length := by
      apply Nat.lt_of_not_le; intro h
      have := Nat.mul_le_mul_right (2 * T.k + 1) h
      rw [Nat.mul_comm (2 * T.k + 1) V] at hroom; omega
    have hVidx : V = T.idx c.state c.reads := by
      have : V < C := by rw [hCR]; exact Nat.lt_of_lt_of_le hVR (Nat.le_mul_of_pos_right _ (by omega))
      rw [hVi] at this ⊢; omega
    let row := T.rows[V]
    have hrow : T.rows[T.idx c.state c.reads]? = some row := by
      rw [← hVidx]; exact List.getElem?_eq_getElem hVR
    have hmem : row ∈ T.rows := List.getElem_mem hVR
    have hrk := hT row hmem
    rw [fstep_some hq hrow]
    have hV1 : (V + 1) * (2 * T.k + 1) ≤ C := by rw [hCR]; exact Nat.mul_le_mul_right _ hVR
    have hS₄T : S₄ TBL = encRows T.rows := by rw [← hS₄, ← hTBL]; lat
    have rw' := nruns_rowP S₄ c.tapes c.pos row.2.1 row.2.2 (k := T.k) (N := N) (off := V * (2 * T.k + 1))
      (C := C) (q := c.state) (q' := row.1) (by rw [← hS₄]; lat)
      (by rw [← hS₄, Nat.mul_comm V]; lat) (by rw [Nat.mul_comm V]; omega) (by rw [← hS₄, ← hKS]; lat)
      (by rw [← hS₄, ← hST]; lat)
      (by rw [hS₄T, show V * (2 * T.k + 1) = V * (2 * T.k + 1) + 0 by rfl, encRows_getD hT hVR (by omega)]; rfl)
      (fun i hi => by
        rw [hS₄T, show V * (2 * T.k + 1) + 1 + i = V * (2 * T.k + 1) + (1 + i) by omega,
          encRows_getD hT hVR (by omega), rowEnc_getD_ws hT hmem hi])
      (fun i hi => by
        rw [hS₄T, show V * (2 * T.k + 1) + 1 + T.k + i = V * (2 * T.k + 1) + (1 + T.k + i) by omega,
          encRows_getD hT hVR (by omega), rowEnc_getD_ms hT hmem hi])
      (by rw [hS₄T, hC]; rw [Nat.succ_mul] at hV1; omega)
      hk hkp hrk.1 hrk.2 (by rw [← hS₄, ← hTP]; lat) (by rw [← hS₄, ← hPOS]; lat)
      (by
        intro x hx
        have hx' : 7 ≤ x.val ∧ x ≠ sRD ∧ x ≠ sCC ∧ x ≠ sV ∧ x ≠ sRM := by revert x hx; decide
        obtain ⟨h₇, h₁, h₂, h₃, h₄⟩ := hx'
        rw [← hS₄]; simp only [Lists.set, h₁, h₂, h₃, h₄, if_false]; exact z x h₇)
      hN1 (by omega) hEN (by rw [hS₄T]; omega) (by omega) hb
    obtain ⟨S₅, hS₅, r₅⟩ := NRuns.named rw'
    have br := r₅.iteT (i := sRM) (c := .pos) (q := .prim (.pop sRM))
      (by rw [← hS₄]; simp only [Lists.set_same]; rw [show C - (2 * T.k + 1) * V = (C - (2 * T.k + 1) * V - 1) + 1
        by omega]; rfl)
    have z₁ := z sRD (by decide)
    have z₂ := z sRM (by decide)
    have z₃ := z sV (by decide)
    have z₄ := z sCC (by decide)
    have f := fin S₅ ((((S.set sRM []).set ST [row.1]).set POS (nps c.pos row.2.2)).set TP
      (encTapes (nts c.tapes c.pos row.2.1))) (by rw [hS₅, ← hS₄]; leq)
    have e : (((((((S.set sRM []).set ST [row.1]).set POS (nps c.pos row.2.2)).set TP
        (encTapes (nts c.tapes c.pos row.2.1)))).set sV []).set sCC []) =
        putCfg S { state := row.1, pos := nps c.pos row.2.2, tapes := nts c.tapes c.pos row.2.1 } := by
      simp only [putCfg]
      leq
    rw [e] at f
    refine (r₁.seq (r₂.seq (r₃.seq (r₄.seq (br.seq f))))).mono ?_
    omega
  · -- no row
    have hVR : T.rows.length ≤ V := by
      apply Nat.le_of_not_lt; intro h
      have := Nat.mul_le_mul_right (2 * T.k + 1) h
      rw [Nat.succ_mul] at this; rw [Nat.mul_comm] at hroom; omega
    have hnone : T.rows[T.idx c.state c.reads]? = none := by
      apply List.getElem?_eq_none; rw [hVi] at hVR; omega
    rw [fstep_none hq hnone, putCfg_self ⟨hTBL, hKS, hNA, hST, hPOS, hTP⟩]
    have p₁ := nruns_pop sRM S₄ (l := []) (v := C - (2 * T.k + 1) * V) (by rw [← hS₄]; lat)
    have br := p₁.iteF (i := sRM) (c := .pos) (p := rowP)
      (by rw [← hS₄]; simp only [Lists.set_same]; rw [show C - (2 * T.k + 1) * V = 0 by omega]; rfl)
    have z₁ := z sRD (by decide)
    have z₂ := z sRM (by decide)
    have z₃ := z sV (by decide)
    have z₄ := z sCC (by decide)
    have f := fin (S₄.set sRM []) (S.set sRM []) (by rw [← hS₄]; leq)
    have e : (((S.set sRM []).set sV []).set sCC []) = S := by leq
    rw [e] at f
    refine (r₁.seq (r₂.seq (r₃.seq (r₄.seq (br.seq f))))).mono ?_
    have := n_le_sq hN1
    have := sq_le_cu hN1
    omega

/-- **One simulated step.** -/
theorem stepP_runs (T : TTable) (hT : RowsOK T) (c : FCfg) (hc : CfgOK T c) (S : Lists UK) (hS : SimSt S T c)
    (hs : UScratch S) : NRuns stepP S (putCfg S (fstep T c)) (800 * cu (nB T c) + 5) := by
  have hST : S ST = [c.state] := hS.2.2.2.1
  have zX : S sX = [] := hs sX (by decide)
  have d₁ := nruns_dup ST sX (by decide) S (l := []) (v := c.state) hST
  rw [zX, List.nil_append] at d₁
  have hback : ∀ v, (S.set sX [v]).set sX [] = S := fun v => by rw [Lists.set_set_u, ← zX, Lists.set_get_self]
  match hq : c.state with
  | 0 =>
    rw [hq] at d₁
    rw [fstep_halted (by omega), putCfg_self hS]
    have p₁ := nruns_pop sX (S.set sX [0]) (l := []) (v := 0) (by simp)
    rw [hback] at p₁
    exact (d₁.seq (p₁.iteT (by rfl))).mono (by omega)
  | 1 =>
    rw [hq] at d₁
    rw [fstep_halted (by omega), putCfg_self hS]
    have e₁ := nruns_dec sX (S.set sX [1]) (l := []) (v := 1) (by simp)
    rw [Lists.set_set_u] at e₁
    have p₁ := nruns_pop sX (S.set sX [0]) (l := []) (v := 0) (by simp)
    rw [hback] at p₁
    exact (d₁.seq ((e₁.seq (p₁.iteT (by rfl))).iteF (by rfl))).mono (by omega)
  | q + 2 =>
    rw [hq] at d₁
    have e₁ := nruns_dec sX (S.set sX [q + 2]) (l := []) (v := q + 2) (by simp)
    rw [Lists.set_set_u] at e₁
    have p₁ := nruns_pop sX (S.set sX [q + 2 - 1]) (l := []) (v := q + 2 - 1) (by simp)
    rw [hback] at p₁
    have m := mainP_runs T hT c hc S hS hs (by omega)
    exact (d₁.seq ((e₁.seq ((p₁.seq m).iteF (by simp [NTest.eval]))).iteF (by simp [NTest.eval]))).mono
      (by omega)

end Complexity.Univ
