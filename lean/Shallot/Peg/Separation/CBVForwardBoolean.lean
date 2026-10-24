import Shallot.Peg.Separation.CBVStrategies
import MacroPeg.CBV.ForwardBooleanSyntax

/-! An exact language-class witness for runtime forward reference evaluation.
This establishes membership, not a separation or an input-preserving P lower
bound for the complete Seq language class. -/
namespace Shallot.PegSeparation
open Shallot.MacroPeg Shallot.MacroPeg.CBV

theorem forwardBoolean_is_seq :
    IsFirstOrderCBVPEL .callByValueSeq ForwardBooleanSyntax.ProgramLanguage := by
  refine ⟨ForwardBooleanProgram.grammar,ForwardBooleanSyntax.entry,
    ForwardBooleanProgram.grammar_firstOrder,ForwardBooleanSyntax.entry_firstOrder,?_⟩
  intro x
  exact (ForwardBooleanSyntax.language_iff x).symm

theorem forwardBoolean_normalized_is_seq :
    IsFirstOrderCBVPEL .callByValueSeq ForwardBooleanSyntax.ProgramLanguage := by
  refine ⟨ForwardBooleanProgram.normalizedGrammar,ForwardBooleanSyntax.normalizedEntry,
    ForwardBooleanProgram.normalized_firstOrder.1,ForwardBooleanSyntax.normalizedEntry_firstOrder,?_⟩
  intro x
  exact (ForwardBooleanSyntax.normalized_language_iff x).symm

theorem forwardBoolean_is_par :
    IsFirstOrderCBVPEL .callByValuePar ForwardBooleanSyntax.ProgramLanguage :=
  firstOrder_seq_subset_par forwardBoolean_is_seq

end Shallot.PegSeparation
