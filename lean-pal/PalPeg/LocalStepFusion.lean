import PalPeg.CloseoutCoreEnc12

/-!
# Fusing several micro-steps into one local step

The consumer of the concrete machine (`LocalLatchRealize.pal_in_peg_of_local_core`, through
`LocalLedgerShift.H_ledger_of_local_oracles`) wants one local step per abstract tick.  A concrete
machine takes several micro-steps per tick, each reading the tape the previous one left.  They
fuse into one local step with a larger window: the later reads are computed from the large
window by running the earlier actions on it.
-/

set_option autoImplicit false

namespace PalPeg.LocalStepFusion

open PalPeg.CloseoutCoreEnc12 (Act actList runA runA_eq runA_shift runA_cur_le runA_le_cur
  cellOfWin)
open PalPeg.Local (Window idx idx_val pos rd readWin readWin_eq)
open PalPeg.Program (STape)

variable {Γ : Type}

/-- The window of radius `inner` around the head after the actions `acts`, computed from a window
of radius `K`. -/
def windowAfter (K inner : ℕ) (window : Window Γ K) (acts : List (Act Γ)) : Window Γ inner :=
  fun i => (runA (cellOfWin K window, K) acts).1
    ((runA (cellOfWin K window, K) acts).2 - inner + (i : ℕ))

/-- **The later read of a fused step is the read of the real tape after the earlier actions.** -/
theorem windowAfter_readWin (blank : Γ) {K inner : ℕ} (tape : STape Γ) (acts : List (Act Γ))
    (hlength : acts.length + inner ≤ K) (hmargin : K ≤ pos tape) :
    windowAfter K inner (readWin blank K tape) acts
      = readWin blank inner (actList blank tape acts) := by
  funext i
  have hshift := runA_shift acts (cellOfWin K (readWin blank K tape)) (rd blank tape) K
    (pos tape - K) (2 * K)
    (fun p hp => by
      show readWin blank K tape (idx K p) = _
      rw [readWin_eq, idx_val hp]
      congr 1
      omega)
    (by omega) (by omega)
  have hpos : K + (pos tape - K) = pos tape := by omega
  rw [hpos, runA_eq blank acts tape] at hshift
  have hlow : K - acts.length ≤ (runA (cellOfWin K (readWin blank K tape), K) acts).2 :=
    runA_le_cur acts (cellOfWin K (readWin blank K tape), K)
  have hhigh : (runA (cellOfWin K (readWin blank K tape), K) acts).2 ≤ K + acts.length :=
    runA_cur_le acts (cellOfWin K (readWin blank K tape), K)
  have hi := i.isLt
  rw [readWin_eq]
  show (runA (cellOfWin K (readWin blank K tape), K) acts).1 _ = _
  rw [hshift.2 _ (by omega)]
  have hposAfter : (runA (cellOfWin K (readWin blank K tape), K) acts).2 + (pos tape - K)
      = pos (actList blank tape acts) := hshift.1
  show rd blank (actList blank tape acts) _ = rd blank (actList blank tape acts) _
  congr 1
  omega

#print axioms windowAfter_readWin

end PalPeg.LocalStepFusion
