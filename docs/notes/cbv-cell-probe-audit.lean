/-
Run with `lake env lean /absolute/path/to/this/file.lean` from the unpacked
Zenodo artifact https://doi.org/10.5281/zenodo.22099762 (v0.1.0), after building
PegSeparation.CFLNotPEG.Main and PegSeparation.CFLNotPEG.InternalLowerBoundMain.
This is an external-model audit, not an import into the project's Lean library
and not a CBV-Seq nonmembership theorem.
-/
import PegSeparation.CFLNotPEG.Assembly
import PegSeparation.CFLNotPEG.InternalLowerBoundMain
import PegSeparation.CFLNotPEG.External.LoffForwardRepaired
import PegSeparation.CFLNotPEG.Reduction.GenericTransfer

namespace CbvParSeqExternalAudit

def assumptions : PegSeparation.ExternalAssumptions where
  loffForward := PegSeparation.External.LoffForwardRepaired.loffForwardStatement
  ko2026MultiphaseIPLowerBound := PegSeparation.CFLNotPEG.internalMultiphaseIPLowerBound

theorem separation :
    Language.IsContextFree PegSeparation.CFLNotPEG.WitnessLanguage ∧
      ¬ PegSeparation.CFLNotPEG.RecognizedByTotalPEG
        PegSeparation.CFLNotPEG.WitnessLanguage :=
  PegSeparation.CFLNotPEG.final_separation assumptions

end CbvParSeqExternalAudit

/-- info: 'CbvParSeqExternalAudit.separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CbvParSeqExternalAudit.separation

/-- info: 'PegSeparation.Reduction.GenericTransfer.genericTransferTheorem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PegSeparation.Reduction.GenericTransfer.genericTransferTheorem
