import PalPeg.CloseoutCoreEnc12

/-!
# The initial blank sweep, for any finite-machine alphabet

Used by `LocalQueueInit` and the physical boot construction. The head starts at
zero; its first sweep has the same result as starting from an all-blank tape at
the rule radius. This introduces no extra machine step or input delay.
-/
set_option autoImplicit false
namespace PalPeg.LocalBlankSweep
open PalPeg.CloseoutCoreEnc12 (ActRule compStep TEqG actList winAfter dAfter)
open PalPeg.Local (Window pos rd readWin readWin_eq sweep pos_cPhase rd_cPhase
  pos_mvLN pos_mvRN rd_mvLN rd_mvRN)
open PalPeg.Program (STape)
variable {Γ : Type} (blank : Γ)

/-- A tape whose cells are all blank. -/
def AllBlank (tape : STape Γ) : Prop := ∀ p, rd blank tape p = blank

theorem allBlank_blankTape : AllBlank blank (STape.blankTape blank) := by
  intro p
  show ([] ++ blank :: ([] : List Γ)).getD p blank = blank
  cases p with
  | zero => rfl
  | succ n => rfl

theorem readWin_allBlank {K : ℕ} {tape : STape Γ} (hblank : AllBlank blank tape)
    (i : Fin (2 * K + 1)) : readWin blank K tape i = blank := by
  rw [readWin_eq]
  exact hblank _

/-- From the left edge of a blank tape the sweep does what it does from a blank tape
whose head stands at `K`. -/
theorem sweep_blank_edge_shifted (K : ℕ) {edge shifted : STape Γ} (hedge : pos edge = 0)
    (hedgeBlank : AllBlank blank edge) (hshifted : pos shifted = K) (hshiftedBlank : AllBlank blank shifted)
    (window : Window Γ K) (displacement : ℤ) :
    TEqG blank (sweep blank K shifted window displacement)
      (sweep blank K edge window displacement) := by
  constructor
  · rw [sweep, sweep, pos_mvRN, pos_cPhase, pos_mvRN, pos_mvLN, pos_mvRN, pos_cPhase, pos_mvRN,
      pos_mvLN, hedge, hshifted]
    omega
  · intro p
    have hmarginEdge : 2 * K ≤ pos ((PalPeg.Local.mvR blank)^[2 * K]
        ((PalPeg.Local.mvL blank)^[K] edge)) := by
      rw [pos_mvRN, pos_mvLN]; omega
    have hmarginShifted : 2 * K ≤ pos ((PalPeg.Local.mvR blank)^[2 * K]
        ((PalPeg.Local.mvL blank)^[K] shifted)) := by
      rw [pos_mvRN, pos_mvLN]; omega
    rw [sweep, sweep, rd_mvRN, rd_cPhase _ _ _ _ hmarginShifted, rd_mvRN, rd_mvLN, rd_mvRN,
      rd_cPhase _ _ _ _ hmarginEdge, rd_mvRN, rd_mvLN]
    simp only [pos_mvRN, pos_mvLN, hedge, hshifted, hedgeBlank p, hshiftedBlank p]
    simp

/-- **The first step needs no margin.**  From blank tapes at the left edge, a step of
`compStep R` is, up to `TEqG`, the rule's actions applied to blank tapes whose heads stand at
`K`; the control is the rule's. -/
theorem compStep_apply_blankEdge {Terminal Q : Type} {tapeCount K : ℕ}
    (R : ActRule Terminal Q Γ tapeCount K) (control : Q) (input : Option Terminal)
    (edge shifted : Fin tapeCount → STape Γ) (hedge : ∀ tape, pos (edge tape) = 0)
    (hedgeBlank : ∀ tape, AllBlank blank (edge tape)) (hshifted : ∀ tape, pos (shifted tape) = K)
    (hshiftedBlank : ∀ tape, AllBlank blank (shifted tape)) :
    ((compStep R).apply blank (control, edge) input).1
        = R.nq control input (fun tape => readWin blank K (shifted tape)) ∧
      ∀ tape, TEqG blank
        (actList blank (shifted tape)
          (R.acts control input (fun tape => readWin blank K (shifted tape)) tape))
        (((compStep R).apply blank (control, edge) input).2 tape) := by
  have hwindows : (fun tape => readWin blank K (edge tape))
      = fun tape => readWin blank K (shifted tape) := by
    funext tape i
    rw [readWin_allBlank blank (hedgeBlank tape), readWin_allBlank blank (hshiftedBlank tape)]
  refine ⟨?_, fun tape => ?_⟩
  · show R.nq control input (fun tape => readWin blank K (edge tape)) = _
    rw [hwindows]
  · have hideal := PalPeg.CloseoutCoreEnc12.teq_sweep_actList blank K (shifted tape)
      (R.acts control input (fun tape => readWin blank K (shifted tape)) tape)
      (R.len_le _ _ _ _) (hshifted tape).ge
    have hsame := sweep_blank_edge_shifted blank K (hedge tape) (hedgeBlank tape) (hshifted tape)
      (hshiftedBlank tape)
      (winAfter K (readWin blank K (shifted tape))
        (R.acts control input (fun tape => readWin blank K (shifted tape)) tape))
      (dAfter K (readWin blank K (shifted tape))
        (R.acts control input (fun tape => readWin blank K (shifted tape)) tape))
    have hgoal : ((compStep R).apply blank (control, edge) input).2 tape
        = sweep blank K (edge tape)
            (winAfter K (readWin blank K (shifted tape))
              (R.acts control input (fun tape => readWin blank K (shifted tape)) tape))
            (dAfter K (readWin blank K (shifted tape))
              (R.acts control input (fun tape => readWin blank K (shifted tape)) tape)) := by
      show sweep blank K (edge tape) _ _ = _
      simp only [hwindows]
      rfl
    rw [hgoal]
    exact ⟨hideal.1.trans hsame.1, fun p => (hideal.2 p).trans (hsame.2 p)⟩

end PalPeg.LocalBlankSweep
