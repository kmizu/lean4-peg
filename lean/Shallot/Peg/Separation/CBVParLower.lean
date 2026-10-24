import Shallot.Peg.Separation.CBVStrict
import MacroPeg.CBV.ParTableau.Recognition

namespace Shallot.PegSeparation

open Shallot.MacroPeg

/-- Every polynomial-time bit language, interpreted one bit per original
character ('b' is true), is a first-order Par language. No input padding,
position coding, or grammar depending on the input is used. -/
theorem firstOrder_par_contains_P_projection {L : Complexity.Lang} (hL : KExp.KEXP 0 L) :
    IsFirstOrderCBVPEL .callByValuePar (fun x => L (CBV.ParTableau.inputBits x)) := by
  obtain ⟨k, M, T, c, degree, hT, hdec, htb⟩ := hL
  refine ⟨CBV.ParTableau.compile M (CBV.ParTableau.polynomialDigits c degree),
    CBV.ParTableau.polynomialStart M c degree, CBV.ParTableau.compile_firstOrder M _,
    CBV.ParTableau.polynomialStart_firstOrder M c degree, ?_⟩
  intro x
  exact (CBV.ParTableau.polynomial_recognizes c degree (by intro n; simpa using hT n) hdec htb x).symm

def bitWord (w : List Bool) : List Char := w.map (fun b => if b then 'b' else 'a')

theorem inputBits_bitWord (w : List Bool) : CBV.ParTableau.inputBits (bitWord w) = w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b with
    | false => change false :: CBV.ParTableau.inputBits (bitWord w) = false :: w; rw [ih]
    | true => change true :: CBV.ParTableau.inputBits (bitWord w) = true :: w; rw [ih]

/-- On the ordinary two-character alphabet, one fixed first-order Par
grammar recognizes every given P language, with the original word intact. -/
theorem firstOrder_par_contains_P {L : Complexity.Lang} (hL : KExp.KEXP 0 L) :
    ∃ (g : MGrammar) (e : MExp), g.FirstOrder ∧ e.FirstOrder ∧
      ∀ w, L w ↔ SObs g .callByValuePar e (bitWord w) (some []) := by
  obtain ⟨g, e, hg, he, hLang⟩ := firstOrder_par_contains_P_projection hL
  refine ⟨g, e, hg, he, ?_⟩
  intro w
  simpa only [inputBits_bitWord] using hLang (bitWord w)

end Shallot.PegSeparation
