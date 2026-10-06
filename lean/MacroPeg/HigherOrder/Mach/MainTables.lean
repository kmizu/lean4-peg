import MacroPeg.HigherOrder.Mach.MainRead
import MacroPeg.HigherOrder.Mach.OrdTables
import MacroPeg.HigherOrder.Mach.Glue
import MacroPeg.HigherOrder.Mach.Accepted

/-!
# The second stage, first part: the order check and the first tables

From the stacks of an accepted reading with the cap (`baseSt`): the order table, the order check, the size table,
and the length of the string on `NX` (`ordStage_ok`, `ordStage_fail`).
-/

namespace Shallot.MacroPeg.Mach

open Complexity

/-- The stacks after the first stage. -/
def baseSt (st : PSt) (cap : Nat) : Lists NK := (enc st).set CAP [cap]

theorem baseSt_scratch (st : PSt) (cap : Nat) : ScratchEmpty (baseSt st cap) := by
  intro i h₁ h₂
  have hne : i ≠ CAP := fun e => by subst e; exact absurd h₂ (by decide)
  rw [baseSt, Lists.set_ne _ _ hne]; exact enc_scratch st i (by omega)

theorem baseSt_at (st : PSt) (cap : Nat) (i : Fin NK) (h : i ≠ CAP) : baseSt st cap i = enc st i := by
  rw [baseSt, Lists.set_ne _ _ h]

theorem baseSt_free (st : PSt) (cap : Nat) (i : Fin NK) (h₁ : 18 ≤ i.val) (h₂ : i ≠ CAP) : baseSt st cap i = [] := by
  rw [baseSt_at st cap i h₂]; exact enc_scratch st i h₁

/-- The order table and the order check, the size table, the string length on `NX`. -/
def ordStageP (j : Nat) : NProg NK :=
  .seq ordTableP (.seq (ordCheckP j) (.seq sizeTableP (.seq (nclr NX) (countP XS NX 18 (by decide)))))

/-- The stacks after the first part of the second stage. -/
def ordSt (st : PSt) (cap : Nat) : Lists NK :=
  (((baseSt st cap).set ORD (ordTable st.tt)).set SZ (sizeTable cap st.tt)).set NX [st.x.length]

def ordStageCost (j cap : Nat) (st : PSt) : Nat :=
  1000 * (st.tt.length + 1) * (st.tt.length + 1) * (st.tt.length + 1) + ordCheckCost j st +
    1000 * (st.tt.length + cap + 1) * (st.tt.length + cap + 1) * (st.tt.length + cap + 1) +
    (2 * st.tk.length + 1) + (8 * st.x.length + 4)

theorem scratch_set {S : Lists NK} (h : ScratchEmpty S) (i : Fin NK) (hi : i.val < 18 ∨ 33 < i.val) (v : List Nat) :
    ScratchEmpty (S.set i v) := by
  intro k h₁ h₂
  have : k ≠ i := fun e => by subst e; omega
  rw [Lists.set_ne _ _ this]; exact h k h₁ h₂

section Stage

variable (j cap : Nat) {st : PSt} {R : List HO.Ty} {bis : List (List Flat.Item)} {is : List Flat.Item}
  {x : List Char}

/-- The order table, then the check. -/
theorem ordStage_first (hi : MInv st) (hr : ReadOK st R bis is x) :
    NRuns ordTableP (baseSt st cap) ((baseSt st cap).set ORD (ordTable st.tt))
      (1000 * (st.tt.length + 1) * (st.tt.length + 1) * (st.tt.length + 1)) ∧
    (ordOK j st = true →
      NRuns (ordCheckP j) ((baseSt st cap).set ORD (ordTable st.tt)) ((baseSt st cap).set ORD (ordTable st.tt))
        (ordCheckCost j st)) ∧
    (ordOK j st = false →
      ∃ S', NHalts (ordCheckP j) ((baseSt st cap).set ORD (ordTable st.tt)) false S' (ordCheckCost j st)) := by
  have hb := baseSt_scratch st cap
  have h₁ := ordTableP_runs (baseSt st cap) hi.tt (by rw [baseSt_at _ _ _ (by decide)]; rfl)
    (by rw [baseSt_at _ _ _ (by decide)]; rfl) (baseSt_free st cap ORD (by decide) (by decide)) hb
  have htags := read_tags hr
  have h₂ := ordCheckP_ok j ((baseSt st cap).set ORD (ordTable st.tt)) st hi.tt (by simp)
    (by rw [Lists.set_ne _ _ (by decide), baseSt_at _ _ _ (by decide)]; rfl)
    (by rw [Lists.set_ne _ _ (by decide), baseSt_at _ _ _ (by decide)]; rfl)
    (by rw [Lists.set_ne _ _ (by decide), baseSt_at _ _ _ (by decide)]; rfl)
    (scratch_set hb ORD (by decide) _) hi.rt (fun it h => (htags it h).2)
    (fun it h => (htags it (List.mem_append_left _ h)).1)
  exact ⟨h₁, h₂.1, h₂.2⟩

/-- The size table and the string length, after the check. -/
theorem ordStage_rest (hi : MInv st) :
    NRuns (.seq sizeTableP (.seq (nclr NX) (countP XS NX 18 (by decide))))
      ((baseSt st cap).set ORD (ordTable st.tt)) (ordSt st cap)
      (1000 * (st.tt.length + cap + 1) * (st.tt.length + cap + 1) * (st.tt.length + cap + 1) +
        (2 * st.tk.length + 1) + (8 * st.x.length + 4)) := by
  have hb := baseSt_scratch st cap
  let S₁ := (baseSt st cap).set ORD (ordTable st.tt)
  have hs₁ : ScratchEmpty S₁ := scratch_set hb ORD (by decide) _
  have h₃ := sizeTableP_runs (cap := cap) S₁ hi.tt
    (by simp only [S₁]; rw [Lists.set_ne _ _ (by decide), baseSt_at _ _ _ (by decide)]; rfl)
    (by simp only [S₁]; rw [Lists.set_ne _ _ (by decide), baseSt_at _ _ _ (by decide)]; rfl)
    (by simp only [S₁]; rw [Lists.set_ne _ _ (by decide)]; simp [baseSt])
    (by simp only [S₁]; rw [Lists.set_ne _ _ (by decide)]; exact baseSt_free st cap SZ (by decide) (by decide)) hs₁
  let S₂ := S₁.set SZ (sizeTable cap st.tt)
  have h₄ := nruns_clr NX S₂
  have hNX : S₂ NX = st.tk.reverse := by
    simp only [S₂, S₁]; rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide), baseSt_at _ _ _ (by decide)]
    rfl
  rw [hNX, List.length_reverse] at h₄
  have h₅ := countP_runs XS NX 18 (by decide) (by decide) (by decide) (S₂.set NX []) (by simp)
    (by rw [Lists.set_ne _ _ (by decide)]; simp only [S₂, S₁]
        rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide)]
        exact baseSt_free st cap 18 (by decide) (by decide))
  have hXS : (S₂.set NX []) XS = st.x := by
    rw [Lists.set_ne _ _ (by decide)]; simp only [S₂, S₁]
    rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide), baseSt_at _ _ _ (by decide)]; rfl
  rw [hXS, Lists.set_set_u] at h₅
  exact h₃.seq (h₄.seq h₅) |>.mono (by omega)

end Stage

end Shallot.MacroPeg.Mach
