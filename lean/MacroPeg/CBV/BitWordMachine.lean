import Shallot.Peg.Separation.BitWordInput
import MacroPeg.CBV.InputMachine

namespace Shallot.MacroPeg.CBV

open Complexity Shallot.Packrat.Machine Shallot.MacroPeg.KExp
open Shallot.PegSeparation (bitWord letterLoaded loadLetters nruns_loadLetters)

theorem moveLetterLength_runs (w : List Bool) :
    NRuns (nmv (machineRegs.get 1) (machineRegs.get 20) (machineRegs.ne (by decide)))
      (letterLoaded loaderGrammar w) (inputState machineRegs (bitWord w)) 2 := by
  let S := letterLoaded loaderGrammar w
  have hi0 : inpR loaderGrammar = machineRegs.get 0 := rfl
  have hi1 : lenR loaderGrammar = machineRegs.get 1 := rfl
  have hlen : S (machineRegs.get 1) = [w.length] := by
    simp [S, letterLoaded, hi0, hi1, Lists.set]
  have xm := nruns_mv (machineRegs.get 1) (machineRegs.get 20) (machineRegs.ne (by decide)) S
    (l := []) (v := w.length) hlen
  have h20 : S (machineRegs.get 20) = [] := by
    simp only [S, letterLoaded, hi0, hi1]
    rw [Lists.set_ne _ _ (machineRegs.ne (by decide)), Lists.set_ne _ _ (machineRegs.ne (by decide))]
    change (if 20 = 0 then _ else []) = []
    rfl
  rw [h20, List.nil_append] at xm
  have he : (S.set (machineRegs.get 20) [w.length]).set (machineRegs.get 1) [] =
      inputState machineRegs (bitWord w) := by
    funext z
    by_cases h0 : z = machineRegs.get 0
    · subst z
      simp [S, letterLoaded, hi0, hi1, inputState, Lists.set]
    by_cases h1 : z = machineRegs.get 1
    · subst z
      simp [inputState, Lists.set, emptyStacks]
    by_cases h20 : z = machineRegs.get 20
    · subst z
      simp [S, inputState, Lists.set, bitWord]
    have hz0 : z.val ≠ 0 := fun hz => h0 (Fin.ext hz)
    simp [S, letterLoaded, hi0, hi1, inputState, Lists.set, h0, h1, h20, emptyStacks, nInit, hz0]
  rw [he] at xm
  exact xm

def bitWordProgram (g : MGrammar) (s : Strategy) (e : MExp) : NProg machineK :=
  .seq (loadLetters loaderGrammar)
    (.seq (nmv (machineRegs.get 1) (machineRegs.get 20) (machineRegs.ne (by decide)))
      (.seq (setupP machineRegs) (loadedProgram machineRegs g s e)))

def bitWordCost (g : MGrammar) (e : MExp) (n : Nat) : Nat :=
  160 * (n + 1) + 2 + setupCost n + loadedCost g e n

theorem bitWordProgram_halts (g : MGrammar) (s : Strategy) (e : MExp) (w : List Bool) :
    ∃ b S', NHalts (bitWordProgram g s e) (nInit machineK w) b S' (bitWordCost g e w.length) ∧
      (b = true ↔ numericDecide s g (bitWord w) e = some (some 0)) := by
  have xl := nruns_loadLetters loaderGrammar w
  have xm := moveLetterLength_runs w
  have xs := setup_runs machineRegs (bitWord w)
  obtain ⟨b, S', hf, hb⟩ := loadedProgram_halts machineRegs g s e (bitWord w)
    (preparedState machineRegs _) (preparedState_ready machineRegs _)
    (by simp [preparedState, Lists.set, emptyStacks])
  refine ⟨b, S', (xl.seqH (xm.seqH (xs.seqH hf))).mono ?_, hb⟩
  simp only [bitWordCost, bitWord, List.length_map]
  omega

theorem bitWordCost_poly (g : MGrammar) (e : MExp) : IsPoly (bitWordCost g e) :=
  isPoly_add (isPoly_add (isPoly_add
    (isPoly_mul (isPoly_const 160) (isPoly_add isPoly_id (isPoly_const 1))) (isPoly_const 2))
      setupCost_poly) (loadedCost_poly g e)

def bitWordLanguage (g : MGrammar) (s : Strategy) (e : MExp) : Lang :=
  fun w => SObs g s e (bitWord w) (some [])

/-- Actual bit-input TM upper bound for ordinary a/b input words, for both
CBV strategies. This does not reuse the four-bit tokenWord language. -/
theorem bitWordLanguage_in_P (g : MGrammar) (s : Strategy) (e : MExp)
    (hg : g.FirstOrder) (hs : s ≠ .callByName) (he : e.FirstOrder) :
    KEXP 0 (bitWordLanguage g s e) := by
  apply Shallot.PegSeparation.nprog_in_P (by decide) (bitWordProgram g s e)
    (bitWordLanguage g s e) (bitWordCost g e) (bitWordCost_poly g e)
  intro w
  obtain ⟨b, S', hr, hb⟩ := bitWordProgram_halts g s e w
  exact ⟨b, S', hr, hb.trans (numericAccept_iff hg hs he _)⟩

end Shallot.MacroPeg.CBV
