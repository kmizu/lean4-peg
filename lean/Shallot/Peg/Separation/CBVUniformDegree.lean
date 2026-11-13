import Shallot.Peg.Separation.CBVBinary
import Shallot.Peg.Separation.CBVStrategies
import Shallot.Peg.Separation.Upper

/-! A uniform polynomial degree would suffice for a true Par/Seq language
separation. The bound itself is an explicit, unproved hypothesis. Conversely,
reverse inclusion would force Seq to contain languages beyond every fixed
machine-time degree. No context-grammar translation or Seq upper bound is
asserted here. -/
namespace Shallot.PegSeparation

open Complexity Shallot.MacroPeg

/-- Constants, alphabets and tape counts may depend on the language. Only the
exponent is fixed. The bound is on actual deterministic multitape machines. -/
def FixedDegreeTime (d : Nat) (L : Lang) : Prop :=
  ∃ (k : Nat) (M : TM k) (c : Nat), M.Decides L ∧
    ∀ w, (M.run (initCfg k w) (c*(w.length+1)^d)).halted

/-- This is the existing explicit polynomial diagonal language, on original
characters. On a/b words it is exactly PolyDiag d, without padding. -/
def degreeDiagonalCharacters (d : Nat) : Shallot.Cfg.Language :=
  fun x => PolyDiag d (CBV.ParTableau.inputBits x)

theorem degreeDiagonal_par (d : Nat) :
    IsFirstOrderCBVPEL .callByValuePar (degreeDiagonalCharacters d) :=
  firstOrder_par_contains_P_projection (polyDiag_in_P d)

/-- Supplying one exponent for the whole Seq class gives this concrete
separator. The machine coefficient may still depend on each source grammar. -/
theorem degreeDiagonal_not_seq_of_uniform_bound (d : Nat)
    (hUpper : ∀ L, IsFirstOrderBinaryCBVPEL .callByValueSeq L → FixedDegreeTime d L) :
    ¬IsFirstOrderCBVPEL .callByValueSeq (degreeDiagonalCharacters d) := by
  rintro ⟨g,e,hg,he,hLang⟩
  apply polyDiag_not_time d
  apply hUpper (PolyDiag d)
  refine ⟨g,e,hg,he,?_⟩
  intro w
  simpa only [degreeDiagonalCharacters,inputBits_bitWord] using hLang (bitWord w)

/-- A conditional separation of the unrestricted original-character classes,
not just a difference between two evaluations of one grammar. -/
theorem uniform_seq_degree_separates (d : Nat)
    (hUpper : ∀ L, IsFirstOrderBinaryCBVPEL .callByValueSeq L → FixedDegreeTime d L) :
    (∀ L, IsFirstOrderCBVPEL .callByValueSeq L → IsFirstOrderCBVPEL .callByValuePar L) ∧
      ∃ L, IsFirstOrderCBVPEL .callByValuePar L ∧ ¬IsFirstOrderCBVPEL .callByValueSeq L := by
  exact ⟨fun _ h => firstOrder_seq_subset_par h,degreeDiagonalCharacters d,
    degreeDiagonal_par d,degreeDiagonal_not_seq_of_uniform_bound d hUpper⟩

/-- If reverse inclusion holds, the explicit diagonal family must be available
in Seq, with unbounded intrinsic polynomial-time degrees. This does not say
that any individual Seq grammar needs superpolynomial time. -/
theorem binary_reverse_requires_unbounded_degrees
    (hReverse : ∀ L, IsFirstOrderBinaryCBVPEL .callByValuePar L →
      IsFirstOrderBinaryCBVPEL .callByValueSeq L) (d : Nat) :
    IsFirstOrderBinaryCBVPEL .callByValueSeq (PolyDiag d) ∧
      ¬FixedDegreeTime d (PolyDiag d) := by
  exact ⟨hReverse _ ((binary_par_iff_P _).mpr (polyDiag_in_P d)),polyDiag_not_time d⟩

theorem original_reverse_requires_unbounded_degrees
    (hReverse : ∀ L, IsFirstOrderCBVPEL .callByValuePar L →
      IsFirstOrderCBVPEL .callByValueSeq L) (d : Nat) :
    IsFirstOrderBinaryCBVPEL .callByValueSeq (PolyDiag d) ∧
      ¬FixedDegreeTime d (PolyDiag d) := by
  exact ⟨original_reverse_requires_seq_P hReverse _ (polyDiag_in_P d),polyDiag_not_time d⟩

end Shallot.PegSeparation
