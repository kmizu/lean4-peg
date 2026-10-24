import MacroPeg.CBV.CodewordControlExamples

/-! A retained caller value may select the stopping point itself. Keeping
that context in the local filter is necessary; transporting it to an actual
Seq verifier remains a separate grammar-construction obligation. -/
namespace Shallot.MacroPeg.CBV.CodewordControlEnvironmentExamples
open CodewordControlFilter
open RuntimeShiftFilter (scanner)

def control : CodewordControlFilter.Expr := .star (.seq .token (.notP (.test (.param 1))))
def input : List Char := "a#aa#?".toList
def context : List (List Char) := ["a#".toList,"?".toList]
def grammar : MGrammar := ⟨[]⟩

/-- The parent test stops before an unequal second word. Dropping it changes
both the chosen endpoint and the comparison result. -/
theorem parent_selects_endpoint :
    let T := tblV grammar input .callByValueSeq 0
    evV grammar input .callByValueSeq T context (render scanner control) input.length=some (some 4) ∧
    evV grammar input .callByValueSeq T context (filter scanner control) input.length=some (some 4) ∧
    evV grammar input .callByValueSeq T ["a#".toList] (render scanner control) input.length=some (some 1) ∧
    evV grammar input .callByValueSeq T ["a#".toList] (filter scanner control) input.length=some none := by
  decide +kernel

/-- No result depending only on the input and comparison word can stand
in for this verifier for every caller context. This rules out erasing the
context in the current unary-verifier construction, not arbitrary Seq grammars. -/
theorem no_context_independent_result :
    ¬∃ result, ∀ E : List (List Char),
      evV grammar input .callByValueSeq (tblV grammar input .callByValueSeq 0)
        ("a#".toList::E) (filter scanner control) input.length=result := by
  rintro ⟨result,h⟩
  have ha := h ["?".toList]
  have hb := h []
  have ha' := parent_selects_endpoint.2.1
  have hb' := parent_selects_endpoint.2.2.2
  change evV grammar input .callByValueSeq (tblV grammar input .callByValueSeq 0)
    ["a#".toList,"?".toList] (filter scanner control) input.length=some (some 4) at ha'
  rw [ha'] at ha
  rw [hb'] at hb
  have bad : (some 4 : Option Nat)=none := Option.some.inj (ha.trans hb.symm)
  cases bad

/-- Simply adding the old value as a Seq argument cannot copy it into a
verifier environment: its literal must match the new input position. -/
theorem extra_argument_does_not_copy_context :
    let T := tblV grammar input .callByValueSeq 0
    evSeqArgs grammar input .callByValueSeq T context [scanner,.param 1] input.length=some none ∧
    evV grammar input .callByValueSeq T context (filter scanner control) input.length=some (some 4) := by
  decide +kernel

/-- A retained test can also change a nullable repetition from divergence
to finite failure. Neither outcome may be replaced by the other. -/
theorem parent_controls_nullable_loop :
    let d : CodewordControlFilter.Expr := .star (.test (.param 1))
    let x := "?".toList
    let T := tblV grammar x .callByValueSeq 0
    evV grammar x .callByValueSeq T [[],"?".toList] (render scanner d) 1=none ∧
    evV grammar x .callByValueSeq T [[],"?".toList] (filter scanner d) 1=none ∧
    evV grammar x .callByValueSeq T [[]] (render scanner d) 1=some (some 1) ∧
    evV grammar x .callByValueSeq T [[]] (filter scanner d) 1=some (some 1) := by
  decide +kernel

/-- The comparison theorem applies to every retained environment, not just
these concrete executions, and to arbitrary finite control syntax. -/
theorem scanner_control (g : MGrammar) (x : List Char) (s : Strategy) (hs : s≠.callByName)
    (T : ClockFreezing.Table) (hT : SoundTV g x s T) (hOk : OkTV x.length T)
    (u : List Char) (hu : RuntimePrefixExamples.code u) (E : List (List Char))
    (d : CodewordControlFilter.Expr) (p q : Nat) (hp : p≤x.length)
    (hv : evV g x s T (u::E) (render scanner d) p=some (some q)) :
    ∃ ws : List (List Char), (∀ w∈ws, RuntimePrefixExamples.code w) ∧
      sfx x p=ws.flatten++sfx x q ∧
      evV g x s T (u::E) (filter scanner d) p=
        if ws=List.replicate ws.length u then some (some q) else some none := by
  exact success_environment g x s hs T hT hOk scanner
    (ParserPrefixFusion.pure_firstOrder scanner RuntimePrefixExamples.header.pure)
    RuntimePrefixExamples.code_prefixFree u hu E
    (fun p q hp h => RuntimePrefixExamples.scanner_captured g x s T (u::E) p q hp h)
    d p q hp hv

end Shallot.MacroPeg.CBV.CodewordControlEnvironmentExamples
