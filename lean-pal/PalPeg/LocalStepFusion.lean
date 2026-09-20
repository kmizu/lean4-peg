import PalPeg.CloseoutCoreEnc13

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
  cellOfWin ActRule)
open PalPeg.CloseoutCoreEnc13 (actList_append)
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

/-! ## Two rules in sequence -/

variable {Terminal Q : Type} {tapeCount firstRadius secondRadius : ℕ}

/-- The step a rule prescribes, performed exactly: the next control, and the actions applied to
the tapes as they are (no sweep). -/
def idealStep {K : ℕ} (R : ActRule Terminal Q Γ tapeCount K) (blank : Γ)
    (x : Q × (Fin tapeCount → STape Γ)) (input : Option Terminal) :
    Q × (Fin tapeCount → STape Γ) :=
  (R.nq x.1 input (fun tape => readWin blank K (x.2 tape)),
    fun tape => actList blank (x.2 tape)
      (R.acts x.1 input (fun tape => readWin blank K (x.2 tape)) tape))

/-- The windows the first rule reads: the centre of the large windows. -/
def firstWindows (windows : Fin tapeCount → Window Γ (firstRadius + secondRadius)) :
    Fin tapeCount → Window Γ firstRadius :=
  fun tape => windowAfter (firstRadius + secondRadius) firstRadius (windows tape) []

/-- The windows the second rule reads: the large windows after the actions of the first. -/
def secondWindows (R₁ : ActRule Terminal Q Γ tapeCount firstRadius) (control : Q)
    (input : Option Terminal) (windows : Fin tapeCount → Window Γ (firstRadius + secondRadius)) :
    Fin tapeCount → Window Γ secondRadius :=
  fun tape => windowAfter (firstRadius + secondRadius) secondRadius (windows tape)
    (R₁.acts control input (firstWindows windows) tape)

/-- **Two rules in sequence as one rule**: the first gets the input, the second reads the tapes
the first leaves, computed from the large windows. -/
def seqRule (R₁ : ActRule Terminal Q Γ tapeCount firstRadius)
    (R₂ : ActRule Terminal Q Γ tapeCount secondRadius) :
    ActRule Terminal Q Γ tapeCount (firstRadius + secondRadius) where
  nq := fun control input windows =>
    R₂.nq (R₁.nq control input (firstWindows windows)) none
      (secondWindows R₁ control input windows)
  acts := fun control input windows tape =>
    R₁.acts control input (firstWindows windows) tape
      ++ R₂.acts (R₁.nq control input (firstWindows windows)) none
          (secondWindows R₁ control input windows) tape
  len_le := fun control input windows tape => by
    rw [List.length_append]
    exact Nat.add_le_add (R₁.len_le _ _ _ _) (R₂.len_le _ _ _ _)

theorem firstWindows_readWin (blank : Γ) (tapes : Fin tapeCount → STape Γ)
    (hmargin : ∀ tape, firstRadius + secondRadius ≤ pos (tapes tape)) :
    firstWindows (secondRadius := secondRadius)
        (fun tape => readWin blank (firstRadius + secondRadius) (tapes tape))
      = fun tape => readWin blank firstRadius (tapes tape) := by
  funext tape
  exact windowAfter_readWin blank (tapes tape) [] (by simp) (hmargin tape)

theorem secondWindows_readWin (blank : Γ) (R₁ : ActRule Terminal Q Γ tapeCount firstRadius)
    (control : Q) (input : Option Terminal) (tapes : Fin tapeCount → STape Γ)
    (hmargin : ∀ tape, firstRadius + secondRadius ≤ pos (tapes tape)) :
    secondWindows (secondRadius := secondRadius) R₁ control input
        (fun tape => readWin blank (firstRadius + secondRadius) (tapes tape))
      = fun tape => readWin blank secondRadius
          (actList blank (tapes tape)
            (R₁.acts control input (fun tape => readWin blank firstRadius (tapes tape)) tape)) := by
  funext tape
  unfold secondWindows
  rw [firstWindows_readWin blank tapes hmargin]
  exact windowAfter_readWin blank (tapes tape) _
    (Nat.add_le_add_right (R₁.len_le _ _ _ _) _) (hmargin tape)

/-- **The fused rule prescribes the two ideal steps in sequence.** -/
theorem seqRule_ideal (blank : Γ) (R₁ : ActRule Terminal Q Γ tapeCount firstRadius)
    (R₂ : ActRule Terminal Q Γ tapeCount secondRadius)
    (x : Q × (Fin tapeCount → STape Γ)) (input : Option Terminal)
    (hmargin : ∀ tape, firstRadius + secondRadius ≤ pos (x.2 tape)) :
    idealStep (seqRule R₁ R₂) blank x input
      = idealStep R₂ blank (idealStep R₁ blank x input) none := by
  unfold idealStep seqRule
  simp only [firstWindows_readWin blank x.2 hmargin,
    secondWindows_readWin blank R₁ x.1 input x.2 hmargin, actList_append]

#print axioms seqRule_ideal

end PalPeg.LocalStepFusion
