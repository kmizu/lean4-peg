import MacroPeg.CBV.RecursiveProducedOrigin
import MacroPeg.CBV.RecursiveProducedExamples

namespace Shallot.MacroPeg.CBV.RecursiveProducedOriginExamples
open RecursiveProducedOrigin
open RecursiveProducedCompiler (Entry conforms)
open ReplayControlFusion (Part)
open RecursiveProducedExamples (word producer producerBody)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def starts : MExp := .alt (.chr 'a') (.chr 'b')
def query : MExp := .alt (.andP starts) (.seq (.notP starts) (.call 3 [.lit []]))
def continuation : MExp := .seq (.chr '!') (.seq (.call 2 [.param 0])
  (.seq (.alt (.seq (.chr '@') (.call 0 [producer])) .eps) (.param 0)))
def ps : List Part := [⟨false,producerBody⟩,⟨false,.call 3 [.lit []]⟩,⟨true,.eps⟩]
def specs : List Entry := [.produced producer continuation,.origin (.leaf 0),
  .origin (.guard (.leaf 1) (.leaf 2)),.growth ⟨9,1,.chr 'X',query⟩]
def entry : MExp := .seq (.call 0 [producer]) (.notP .any)

theorem checked : check ps specs=true := by decide +kernel

theorem root_checked : conforms specs entry=true := by decide +kernel

/-- In this original grammar the zero header is a real sequence, beside
an actual consuming recursive producer. It has no inserted lookahead. -/
theorem actual_origin_header : ruleAtM (source ps specs).rules 2=some
    ⟨1,.seq (.call 3 [.lit []]) (.seq (.param 0) .eps)⟩ := by rfl

theorem actual_consuming_prefix : ruleAtM (source ps specs).rules 0=some ⟨1,.seq producer continuation⟩ := by rfl

theorem fixed_target : (target ps specs).rules.length=27 := by decide +kernel

def simple (w : List Char) := w++['!']++w++w
def nested (w v : List Char) := w++['!']++w++['@']++simple v++w

theorem source_captures : ∀ pair∈[(0,3),(3,0),(1,2)],
    evV (source ps specs) (nested (word pair.1) (word pair.2)) .callByValuePar
      (tblV (source ps specs) (nested (word pair.1) (word pair.2)) .callByValuePar 12) [] entry
      (nested (word pair.1) (word pair.2)).length=some (some 0) := by decide +kernel

theorem target_captures : ∀ pair∈[(0,3),(3,0),(1,2)],
    evV (target ps specs) (nested (word pair.1) (word pair.2)) .callByValueSeq
      (tblV (target ps specs) (nested (word pair.1) (word pair.2)) .callByValueSeq 12) [] (render ps specs entry)
      (nested (word pair.1) (word pair.2)).length=some (some 0) := by decide +kernel

theorem consuming_header_rejected : check (ps.set 1 ⟨false,.chr 'a'⟩) specs=false := by decide +kernel

theorem all_observations (e : MExp) (he : e.FirstOrder) (hc : conforms specs e=true)
    (x : List Char) (rest : Option (List Char)) :
    SObs (source ps specs) .callByValuePar e x rest ↔ SObs (target ps specs) .callByValueSeq (render ps specs e) x rest :=
  observations_iff ps specs checked e he hc x rest

end Shallot.MacroPeg.CBV.RecursiveProducedOriginExamples
