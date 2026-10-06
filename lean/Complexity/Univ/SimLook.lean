import Complexity.Univ.SimHorner
import Complexity.Univ.SimWrite

/-!
# Looking up the row

`offP` lowers `C` by `(2k+1)·V` (`V` the capped number of the row): what is left is positive exactly when the row
exists. `rowP` then reads the new state at offset `(2k+1)·V`, carries out the row on all tapes (`writeP`) and
puts the new state in place.
-/

namespace Complexity.Univ

open Complexity

def offP : NProg UK :=
  .seq (.prim (.dup sCC sRM (by decide))) (.seq (.prim (.dup KS sCN (by decide))) (.seq
    (.prim (.dup KS sX (by decide))) (.seq (addTo sX sCN) (.seq (.prim (.inc sCN)) (.seq repSubP
      (.prim (.pop sCN)))))))

theorem nruns_offP (X : Lists UK) {C k V : Nat} (hC : X sCC = [C]) (hK : X KS = [k]) (hV : X sV = [V])
    (hR : X sRM = []) (hN : X sCN = []) (hX : X sX = []) :
    NRuns offP X (X.set sRM [C - (2 * k + 1) * V]) ((2 * k + 1) * (3 * V + 5) + 3 * k + 10) := by
  obtain ⟨D₁, hD₁, d₁⟩ := NRuns.named (nruns_dup sCC sRM (by decide) X (l := []) (v := C) hC)
  obtain ⟨D₂, hD₂, d₂⟩ := NRuns.named (nruns_dup KS sCN (by decide) D₁ (l := []) (v := k) (by rw [hD₁]; lat))
  obtain ⟨D₃, hD₃, d₃⟩ := NRuns.named (nruns_dup KS sX (by decide) D₂ (l := []) (v := k)
    (by rw [hD₂, hD₁]; lat))
  obtain ⟨D₄, hD₄, d₄⟩ := NRuns.named (nruns_addTo sX sCN (by decide) D₃ (l := []) (l' := []) (a := k) (b := k)
    (by rw [hD₃, hD₂, hD₁]; lat) (by rw [hD₃, hD₂, hD₁]; lat))
  obtain ⟨D₅, hD₅, d₅⟩ := NRuns.named (nruns_inc sCN D₄ (l := []) (v := k + k) (by rw [hD₄]; lat))
  obtain ⟨D₆, hD₆, d₆⟩ := NRuns.named (nruns_repSubP D₅ (n := k + k + 1) (v := V) (r := C) (lv := [])
    (by rw [hD₅]; lat) (by rw [hD₅, hD₄, hD₃, hD₂, hD₁]; lat) (by rw [hD₅, hD₄, hD₃, hD₂, hD₁]; lat)
    (by rw [hD₅, hD₄]; lat))
  obtain ⟨D₇, hD₇, d₇⟩ := NRuns.named (nruns_pop sCN D₆ (l := []) (v := 0) (by rw [hD₆]; lat))
  have e : D₇ = X.set sRM [C - (2 * k + 1) * V] := by
    rw [hD₇, hD₆, hD₅, hD₄, hD₃, hD₂, hD₁, show k + k + 1 = 2 * k + 1 by omega]
    simp only [List.nil_append]
    leq
  rw [e] at d₇
  refine (d₁.seq (d₂.seq (d₃.seq (d₄.seq (d₅.seq (d₆.seq d₇)))))).mono ?_
  rw [show k + k + 1 = 2 * k + 1 by omega]
  omega

def rowP : NProg UK :=
  .seq (.prim (.dup sCC sOF (by decide))) (.seq (subTo sRM sOF) (.seq (.prim (.dup sOF sX (by decide)))
    (.seq (peekAt TBL sPT sX sQN (by decide) (by decide)) (.seq (.prim (.dup sOF sIW (by decide)))
      (.seq (.prim (.inc sIW)) (.seq (.prim (.dup sOF sIM (by decide))) (.seq (.prim (.inc sIM))
        (.seq (.prim (.dup KS sX (by decide))) (.seq (addTo sX sIM) (.seq writeP (.seq (.prim (.pop sIW))
          (.seq (.prim (.pop sIM)) (.seq (.prim (.pop sOF)) (.seq (.prim (.pop ST))
            (nmv sQN ST (by decide))))))))))))))))

/-- The stacks `rowP` needs empty. -/
def RowFree (X : Lists UK) : Prop :=
  ∀ x : Fin UK, x ∈ [sW, sPW, sTT, sP, sLN, sLEN, sTT2, sX, sPT, sA, sMV, sF, sC, sD, sZ, sOF, sIW, sIM, sQN] →
    X x = []

/-- **Carrying out the row at offset `off`.** -/
theorem nruns_rowP (X : Lists UK) (ts : List (List Nat)) (ps ws ms : List Nat) {k N off C q q' : Nat}
    (hC : X sCC = [C]) (hR : X sRM = [C - off]) (hoff : off ≤ C) (hK : X KS = [k]) (hQ : X ST = [q])
    (hq' : (X TBL).getD off 0 = q')
    (hwt : ∀ i, i < k → (X TBL).getD (off + 1 + i) 0 = ws.getD i 0)
    (hmt : ∀ i, i < k → (X TBL).getD (off + 1 + k + i) 0 = ms.getD i 0)
    (hlen : off + 1 + k + k ≤ (X TBL).length)
    (hts : ts.length = k) (hps : ps.length = k) (hws : ws.length = k) (hms : ms.length = k)
    (hTP : X TP = encTapes ts) (hPOS : X POS = ps) (hz : RowFree X)
    (hN : 1 ≤ N) (hk : k ≤ N) (hE : (encTapes ts).length ≤ N) (hTB : (X TBL).length ≤ N) (hCN : C ≤ N)
    (hb : ∀ i, i < k → (ts.getD i []).length ≤ N ∧ ps.getD i 0 ≤ N) :
    NRuns rowP X ((((X.set sRM []).set ST [q']).set POS (nps ps ms)).set TP (encTapes (nts ts ps ws)))
      (500 * cu N) := by
  have z : ∀ x : Fin UK, x ∈ [sW, sPW, sTT, sP, sLN, sLEN, sTT2, sX, sPT, sA, sMV, sF, sC, sD, sZ, sOF, sIW, sIM,
    sQN] → X x = [] := hz
  have zOF := z sOF (by decide)
  have zX := z sX (by decide)
  have zPT := z sPT (by decide)
  have zQN := z sQN (by decide)
  have zIW := z sIW (by decide)
  have zIM := z sIM (by decide)
  obtain ⟨D₁, hD₁, d₁⟩ := NRuns.named (nruns_dup sCC sOF (by decide) X (l := []) (v := C) hC)
  obtain ⟨D₂, hD₂, d₂⟩ := NRuns.named (nruns_subTo sRM sOF (by decide) D₁ (l := []) (l' := []) (a := C - off)
    (b := C) (by rw [hD₁]; lat) (by rw [hD₁]; lat))
  rw [show C - (C - off) = off by omega] at hD₂
  obtain ⟨D₃, hD₃, d₃⟩ := NRuns.named (nruns_dup sOF sX (by decide) D₂ (l := []) (v := off) (by rw [hD₂]; lat))
  have hT₃ : D₃ TBL = X TBL := by rw [hD₃, hD₂, hD₁]; lat
  obtain ⟨D₄, hD₄, d₄⟩ := NRuns.named (nruns_peekAt' TBL sPT sX sQN (by decide) (by decide) (by decide) D₃
    (by rw [hD₃, hD₂, hD₁]; lat) (lc := []) (k := off) (by rw [hD₃, hD₂, hD₁]; lat) (by rw [hT₃]; omega))
  obtain ⟨D₅, hD₅, d₅⟩ := NRuns.named (nruns_dup sOF sIW (by decide) D₄ (l := []) (v := off)
    (by rw [hD₄, hD₃, hD₂]; lat))
  obtain ⟨D₆, hD₆, d₆⟩ := NRuns.named (nruns_inc sIW D₅ (l := []) (v := off)
    (by rw [hD₅, hD₄, hD₃, hD₂, hD₁]; lat))
  obtain ⟨D₇, hD₇, d₇⟩ := NRuns.named (nruns_dup sOF sIM (by decide) D₆ (l := []) (v := off)
    (by rw [hD₆, hD₅, hD₄, hD₃, hD₂]; lat))
  obtain ⟨D₈, hD₈, d₈⟩ := NRuns.named (nruns_inc sIM D₇ (l := []) (v := off)
    (by rw [hD₇, hD₆, hD₅, hD₄, hD₃, hD₂, hD₁]; lat))
  obtain ⟨D₉, hD₉, d₉⟩ := NRuns.named (nruns_dup KS sX (by decide) D₈ (l := []) (v := k)
    (by rw [hD₈, hD₇, hD₆, hD₅, hD₄, hD₃, hD₂, hD₁]; lat))
  obtain ⟨D₁₀, hD₁₀, d₁₀⟩ := NRuns.named (nruns_addTo sX sIM (by decide) D₉ (l := []) (l' := []) (a := k)
    (b := off + 1) (by rw [hD₉, hD₈, hD₇, hD₆, hD₅, hD₄]; lat) (by rw [hD₉, hD₈]; lat))
  -- the stacks before the writing
  let Y : Lists UK := ((((X.set sRM []).set sOF [off]).set sQN [q']).set sIW [off + 1]).set sIM [off + 1 + k]
  have eY : D₁₀ = Y := by
    have hq'' : (D₃ TBL).getD off 0 = q' := by rw [hT₃]; exact hq'
    rw [hD₁₀, hD₉, hD₈, hD₇, hD₆, hD₅, hD₄, hq'', hD₃, hD₂, hD₁]
    simp only [Y, List.nil_append]
    leq
  rw [eY] at d₁₀
  have hYT : Y TBL = X TBL := by simp only [Y]; lat
  have w := nruns_writeP Y ts ps ws ms k N (off + 1) (off + 1 + k) hts hps hws hms
    (by simp only [Y]; rw [← hTP]; lat) (by simp only [Y]; rw [← hPOS]; lat) (by simp only [Y]; lat)
    (by simp only [Y]; lat)
    (by
      intro x hx
      have h := z x (List.mem_append_left [sOF, sIW, sIM, sQN] hx)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (simp only [Y]; lat))
    (by rw [hYT]; intro i hi; rw [show off + 1 + i = off + 1 + i by rfl]; exact hwt i hi)
    (by rw [hYT]; exact hmt) (by rw [hYT]; omega) (by rw [hYT]; omega) hN hk hE (by rw [hYT]; exact hTB) hb
  obtain ⟨W, hW, w'⟩ := NRuns.named w
  obtain ⟨E₁, hE₁, e₁⟩ := NRuns.named (nruns_pop sIW W (l := []) (v := off + 1 + k) (by rw [hW]; lat))
  obtain ⟨E₂, hE₂, e₂⟩ := NRuns.named (nruns_pop sIM E₁ (l := []) (v := off + 1 + k + k) (by rw [hE₁, hW]; lat))
  obtain ⟨E₃, hE₃, e₃⟩ := NRuns.named (nruns_pop sOF E₂ (l := []) (v := off)
    (by rw [hE₂, hE₁, hW]; simp only [Y]; lat))
  obtain ⟨E₄, hE₄, e₄⟩ := NRuns.named (nruns_pop ST E₃ (l := []) (v := q)
    (by rw [hE₃, hE₂, hE₁, hW]; simp only [Y]; lat))
  obtain ⟨E₅, hE₅, e₅⟩ := NRuns.named (nruns_mv sQN ST (by decide) E₄ (l := []) (v := q')
    (by rw [hE₄, hE₃, hE₂, hE₁, hW]; simp only [Y]; lat))
  have e : E₅ = (((X.set sRM []).set ST [q']).set POS (nps ps ms)).set TP (encTapes (nts ts ps ws)) := by
    have h₁ : E₄ ST = [] := by rw [hE₄]; lat
    rw [hE₅, h₁, hE₄, hE₃, hE₂, hE₁, hW]
    simp only [Y, List.nil_append]
    leq
  rw [e] at e₅
  refine (d₁.seq (d₂.seq (d₃.seq (d₄.seq (d₅.seq (d₆.seq (d₇.seq (d₈.seq (d₉.seq (d₁₀.seq
    (w'.seq (e₁.seq (e₂.seq (e₃.seq (e₄.seq e₅))))))))))))))).mono ?_
  rw [hT₃]
  have := n_le_sq hN
  have := sq_le_cu hN
  omega

end Complexity.Univ
