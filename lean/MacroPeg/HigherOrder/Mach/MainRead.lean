import MacroPeg.HigherOrder.Mach.ReadP
import MacroPeg.HigherOrder.Mach.Tokenize
import MacroPeg.HigherOrder.Mach.Cap
import Complexity.NFrame

/-!
# The first stage: the cap, the tokens, the reading

`readStageP`: put the cap on `CAP`, turn the bits into tokens and read them (`readStage_ok`, `readStage_fail`). The
tokenizer and the reading machine do not touch `CAP` (`tokenizeP_cap`, `readP_cap`), so the cap stays.
-/

namespace Shallot.MacroPeg.Mach

open Complexity

theorem npushC_touches {K : Nat} (i k : Fin K) : ∀ c, (npushC i c).touches k = (i == k)
  | 0 => by simp [npushC, NProg.touches, NPrim.touches]
  | c + 1 => by simp [npushC, NProg.touches, NPrim.touches, npushC_touches i k c]

theorem tokenizeP_cap : tokenizeP.touches CAP = false := by decide

set_option linter.unusedSimpArgs false in
theorem readP_cap : readP.touches CAP = false := by
  simp only [addTo, binP, caseTop, charP, checkCharP, cmpBody, cmpRes, cmpTop, emitP, emitV, entryP, exprP, frame0P,
    frame11P, frame13P, frame14P, frame15P, frame16P, frame17P, frame18P, frame1P, frame8P, frame9P, framePs,
    internP, internSt, internStep, leafOutP, leafP, markP, moveN, nclr, nmv, nmvAll, nskip, parseCharP, parseNatP,
    parseStrP, peekAt, push2, pushIfP, readP, readStepP, ruleP, rulesAppendBodyP, rulesCheckBodyP, rulesCopyP,
    rulesCurZeroP, rulesFrame18PrefixP, rulesMoveOutP, rulesPeekP, rulesTokCase, selectP, stepP, strLoopCost,
    strSink, toZero, tok0P, tok10P, tok11P, tok12P, tok1P, tok2P, tok3P, tok4P, tok5P, tok6P, tok7P, tok8P, tok9P,
    tokPs, tokenizeP, tokz_E, tokz_P, tokz_St, tokz_bit, tokz_bits, tokz_consts, tokz_drop, tokz_group, tokz_incs,
    tokz_loop, tokz_rd, tokz_w, types_app11P, types_internP, types_pre11P, unP, varEndP, varTyP, varUpP,
    NProg.touches, NPrim.touches, npushC_touches, caseTop]
  decide

/-- The first stage. -/
def readStageP : NProg NK := .seq capP (.seq tokenizeP readP)

/-- The steps of the first stage. -/
def readStageCost (w : List Bool) : Nat :=
  20 * (w.length + 1) + 100 * (w.length + 1) + readCost (Complexity.ofBits w).length

/-- **The first stage, accepting**: the final reading state, with the cap. -/
theorem readStage_ok (w : List Bool) (hok : (finalSt (Complexity.ofBits w)).ok = true) :
    NRuns readStageP (nInit NK w) ((enc (finalSt (Complexity.ofBits w))).set CAP [capOf w]) (readStageCost w) := by
  have x₁ := capP_runs w
  have x₂ := NRuns.frame tokenizeP_cap [capOf w] (tokenizeP_runs w)
  have x₃ := NRuns.frame readP_cap [capOf w] ((readP_run (Complexity.ofBits w)).1 hok)
  exact (x₁.seq (x₂.seq x₃)).mono (by unfold readStageCost; omega)

/-- **The first stage, rejecting.** -/
theorem readStage_fail (w : List Bool) (hok : (finalSt (Complexity.ofBits w)).ok = false) :
    ∃ S', NHalts readStageP (nInit NK w) false S' (readStageCost w) := by
  have x₁ := capP_runs w
  have x₂ := NRuns.frame tokenizeP_cap [capOf w] (tokenizeP_runs w)
  obtain ⟨S', x₃⟩ := (readP_run (Complexity.ofBits w)).2 hok
  exact ⟨_, (x₁.seqH (x₂.seqH (NHalts.frame readP_cap [capOf w] x₃))).mono (by unfold readStageCost; omega)⟩

end Shallot.MacroPeg.Mach
