import PalPeg.GSPreprocessProg76
import PalPeg.ProgLangBankTapes

/-!
# Concrete finite preparation under interleaving

All slots run the same input-independent preparation/setup syntax. Each receives
fifteen private tapes and a finite continuation. This theorem accounts for
arbitrary interleaving and surplus ticks, but not for stage birth, recycling, or
streaming input arrivals; those remain separate lifecycle obligations.
-/

set_option autoImplicit false

namespace PalPeg.PrepInstance

open PegSeparation.RealTimeTM PalPeg.Program PalPeg.PatternTapes PalPeg.PatternProg
open PalPeg.PatternProg.Fifteen PalPeg.ProgLang PalPeg.ProgLangPersist PalPeg.ProgLangBank

variable {sc n : ℕ} {Terminal : Type}
  {blank startSym endSym mark leftSym : Fin sc}
  {w Text : List (Fin sc)} {L : ℕ} {S : Tapes sc}

noncomputable def prepBankInterp (blank endSym mark : Fin sc) :
    InterpF Terminal (PrepAct sc) (PrepCond sc) (Fin sc) 15 where
  toInterp := prepInterp blank endSym mark
  flagOf _ := none

theorem finitePrepSetup_interleaved (k : ℕ) (hmb : mark ≠ blank)
    (hpre : StageTapes.PrepPre blank mark leftSym L w Text S)
    (hstart : startSym ∉ PrepInstances.stagePat w L)
    (hend : endSym ∉ PrepInstances.stagePat w L) (hne : startSym ≠ endSym)
    (i : Fin n)
    (x : (Bank (fun _ : Fin n => finitePrepSetup blank startSym endSym leftSym mark k)
      × Bool) × (Fin (n * 15) → STape (Fin sc)))
    (hx : tapeSlice i x.2 = TSg S)
    (hc : (x.1.1 i).val = [finitePrepSetup blank startSym endSym leftSym mark k]) :
    let d := PrepInstances.prepRes w L
    ∃ cost R,
      GSVTapes.VEncodes' blank startSym endSym mark
        ((w.take L).reverse.take d.1) ((w.take L).reverse.drop d.1)
        (TextFeed.padW blank Text 0) k d.2.1 d.2.2
        (toGS R, toVExt R) (⟨0, 0⟩, 0) ∧
      cost ≤ (GSPreProg.preprocessSlope + 25 + 7 * k) * L +
        GSPreProg.preprocessOffset + 37 + 11 * k ∧
      ∀ l : List (Fin n × Option Terminal), cost ≤ (localInputs i l).length →
        tapeSlice i (runInterleaved
          (fun _ : Fin n => finitePrepSetup blank startSym endSym leftSym mark k)
          (fun _ => prepBankInterp blank endSym mark) blank l x).2 = TSg R := by
  obtain ⟨trace, R, he, hr, hv, hlen⟩ :=
    finitePrepSetup_exec (Terminal := Terminal) k hmb hpre hstart hend hne
  refine ⟨trace.length, R, hv, hlen, ?_⟩
  intro l hl
  have he' : Exec (prepBankInterp (Terminal := Terminal) blank endSym mark).toInterp
      blank (finitePrepSetup blank startSym endSym leftSym mark k)
      (tapeSlice i x.2) trace := by
    rw [hx]
    exact he
  rw [runInterleaved_exec_of_le _ (fun _ => prepBankInterp blank endSym mark)
    blank i l x trace hc he' hl, hx]
  exact hr

/-- info: 'PalPeg.PrepInstance.finitePrepSetup_interleaved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finitePrepSetup_interleaved

end PalPeg.PrepInstance
