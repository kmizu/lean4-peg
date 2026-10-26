/-
Run with `lake env lean /absolute/path/to/this/file.lean` from the unpacked
Zenodo artifact https://doi.org/10.5281/zenodo.22099762 (v0.1.0), after building
PegSeparation.CFLNotPEG.Main, PegSeparation.CFLNotPEG.InternalLowerBoundMain,
PegSeparation.Common.Compiler.RealTimeTM.Correctness and
PegSeparation.Common.Compiler.SCAToPEG.Final.
This is an external-model audit, not an import into the project's Lean library
and not a CBV-Seq nonmembership theorem.
-/
import PegSeparation.CFLNotPEG.Assembly
import PegSeparation.CFLNotPEG.InternalLowerBoundMain
import PegSeparation.CFLNotPEG.External.LoffForwardRepaired
import PegSeparation.CFLNotPEG.Reduction.GenericTransfer
import PegSeparation.Common.Compiler.RealTimeTM.Correctness
import PegSeparation.Common.Compiler.SCAToPEG.Final

namespace CbvParSeqExternalAudit

def assumptions : PegSeparation.ExternalAssumptions where
  loffForward := PegSeparation.External.LoffForwardRepaired.loffForwardStatement
  ko2026MultiphaseIPLowerBound := PegSeparation.CFLNotPEG.internalMultiphaseIPLowerBound

theorem separation :
    Language.IsContextFree PegSeparation.CFLNotPEG.WitnessLanguage ∧
      ¬ PegSeparation.CFLNotPEG.RecognizedByTotalPEG
        PegSeparation.CFLNotPEG.WitnessLanguage :=
  PegSeparation.CFLNotPEG.final_separation assumptions

/-- This preserves the original word. It assumes a concrete real-time TM
recognizer for the reversed language; no FIFO-to-TM theorem is assumed here. -/
theorem realTimeReverseToPEG {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
    (L : Language Terminal)
    (h : PegSeparation.RealTimeTM.RecognizedBy (fun x => x.reverse ∈ L)) :
    PegSeparation.RecognizedByTotalPEG L := by
  obtain ⟨states, labels, degree, radius, A, hA⟩ :=
    PegSeparation.RealTimeTM.recognizedBySCA_of_recognizedBy h
  obtain ⟨count, grammar, htotal, hgrammar⟩ := PegSeparation.SCAToPEG.loffBackward A
  refine ⟨count, grammar, htotal, ?_⟩
  intro x
  have hp := hgrammar x.reverse
  have hl := hA x.reverse
  change A.Accepts x.reverse ↔ x.reverse.reverse ∈ L at hl
  simpa only [List.reverse_reverse] using hp.symm.trans hl

end CbvParSeqExternalAudit

/-- info: 'CbvParSeqExternalAudit.separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CbvParSeqExternalAudit.separation

/-- info: 'PegSeparation.Reduction.GenericTransfer.genericTransferTheorem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PegSeparation.Reduction.GenericTransfer.genericTransferTheorem

/-- info: 'CbvParSeqExternalAudit.realTimeReverseToPEG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CbvParSeqExternalAudit.realTimeReverseToPEG
