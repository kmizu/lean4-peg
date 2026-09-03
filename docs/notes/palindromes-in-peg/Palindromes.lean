import PegSeparation.Closure.RegularToPEG
import PegSeparation.Common.Compiler.RealTimeTM.Correctness

/-!
# Palindromes have a PEG, given real-time recognizability

Loff, Moreira and Reis (JCSS 2020, Conjecture 7) conjectured that the even-length
palindromes `{ w wᴿ }` have no PEG, and asked whether the language of all palindromes
does. This file observes that the question is settled by combining three known results:

1. **Galil (JCSS 16(2), 1978), building on Slisenko (1973):** there is a real-time
   deterministic multitape Turing machine that, reading the input one symbol per step,
   determines after each symbol whether the prefix read so far is a palindrome. Hence the
   language of palindromes is recognized by a real-time multitape TM — the model
   `PegSeparation.RealTimeTM.Machine` of this artifact (bidirectional heads, any number of
   tapes, one transition per input symbol). This is the only ingredient not formalized
   here; it enters as the hypothesis `hrt` below.
2. **Real-time TM ⊆ SCA** — `RealTimeTM.recognizedBySCA_of_recognizedBy` (this artifact).
3. **`L ∈ PEG ⇔ Lᴿ ∈ SCA`** (Loff–Moreira–Reis, Theorem 16), the backward direction of
   which is `SCAToPEG.loffBackward`, packaged as `recognizedByTotalPEG_of_accepts`.

Since palindromes are their own reversal, (2)+(3) turn Galil's machine into a total PEG.
The general statement is `recognizedByTotalPEG_of_recognizedBy_of_reverse_eq`: any
reversal-invariant language that is real-time recognizable is a PEG language.
-/

namespace PegSeparation

open RealTimeTM PegSeparation.Closure

/-- The language of palindromes over `Terminal`. -/
def Palindromes (Terminal : Type) : Language Terminal := fun w => w.reverse = w

/-- Even-length palindromes `{ w wᴿ }` — the language of LMR's Conjecture 7. -/
def EvenPalindromes (Terminal : Type) : Language Terminal :=
  fun w => w.reverse = w ∧ Even w.length

theorem mem_palindromes {Terminal : Type} {w : List Terminal} :
    w ∈ Palindromes Terminal ↔ w.reverse = w := Iff.rfl

theorem mem_evenPalindromes {Terminal : Type} {w : List Terminal} :
    w ∈ EvenPalindromes Terminal ↔ w.reverse = w ∧ Even w.length := Iff.rfl

/-- `{ w wᴿ }` really is the set of even-length palindromes. -/
theorem evenPalindromes_eq_ww_reverse {Terminal : Type} (w : List Terminal) :
    w ∈ EvenPalindromes Terminal ↔ ∃ u : List Terminal, w = u ++ u.reverse := by
  constructor
  · rintro ⟨hpal, ⟨k, hk⟩⟩
    have hlen : w.length = k + k := hk
    have hsplit : w.take k ++ w.drop k = w := List.take_append_drop k w
    -- Reverse both sides of the split and compare with `hpal`.
    have hrev : (w.drop k).reverse ++ (w.take k).reverse = w.take k ++ w.drop k := by
      calc (w.drop k).reverse ++ (w.take k).reverse
          = (w.take k ++ w.drop k).reverse := by rw [List.reverse_append]
        _ = w.reverse := by rw [hsplit]
        _ = w := hpal
        _ = w.take k ++ w.drop k := hsplit.symm
    have hlenEq : (w.drop k).reverse.length = (w.take k).length := by
      simp [hlen]
    have hparts := List.append_inj hrev hlenEq
    refine ⟨w.take k, ?_⟩
    calc w = w.take k ++ w.drop k := hsplit.symm
      _ = w.take k ++ (w.take k).reverse := by
          rw [← hparts.1, List.reverse_reverse]
  · rintro ⟨u, rfl⟩
    exact ⟨by simp, ⟨u.length, by simp⟩⟩

theorem palindromes_reverse (Terminal : Type) :
    Language.reverse (Palindromes Terminal) = Palindromes Terminal := by
  ext w
  simp only [Language.mem_reverse, mem_palindromes, List.reverse_reverse]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem evenPalindromes_reverse (Terminal : Type) :
    Language.reverse (EvenPalindromes Terminal) = EvenPalindromes Terminal := by
  ext w
  simp only [Language.mem_reverse, mem_evenPalindromes, List.reverse_reverse, List.length_reverse]
  exact ⟨fun ⟨h, he⟩ => ⟨h.symm, he⟩, fun ⟨h, he⟩ => ⟨h.symm, he⟩⟩

/-- Real-time recognizability of the reversal of `L` gives a total PEG for `L`:
compile the machine to a scaffolding automaton, then apply LMR's characterization. -/
theorem recognizedByTotalPEG_of_recognizedBy_reverse {Terminal : Type} [Fintype Terminal]
    [DecidableEq Terminal] {L : Language Terminal}
    (h : RecognizedBy (Language.reverse L)) : RecognizedByTotalPEG L :=
  recognizedByTotalPEG_of_accepts (recognizedBySCA_of_recognizedBy h)

/-- **A reversal-invariant language that is real-time recognizable is a PEG language.** -/
theorem recognizedByTotalPEG_of_recognizedBy_of_reverse_eq {Terminal : Type} [Fintype Terminal]
    [DecidableEq Terminal] {L : Language Terminal} (hrev : Language.reverse L = L)
    (h : RecognizedBy L) : RecognizedByTotalPEG L :=
  recognizedByTotalPEG_of_recognizedBy_reverse (by rw [hrev]; exact h)

/-- **Palindromes are a PEG language**, given Galil's real-time recognizer (the
hypothesis `hrt`). -/
theorem palindromes_isPEG_of_realTime {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
    (hrt : RecognizedBy (Palindromes Terminal)) : RecognizedByTotalPEG (Palindromes Terminal) :=
  recognizedByTotalPEG_of_recognizedBy_of_reverse_eq (palindromes_reverse Terminal) hrt

/-- **LMR's Conjecture 7 fails**, given a real-time recognizer for `{ w wᴿ }` (Galil's
machine with the input-length parity tracked in the finite control). -/
theorem evenPalindromes_isPEG_of_realTime {Terminal : Type} [Fintype Terminal]
    [DecidableEq Terminal] (hrt : RecognizedBy (EvenPalindromes Terminal)) :
    RecognizedByTotalPEG (EvenPalindromes Terminal) :=
  recognizedByTotalPEG_of_recognizedBy_of_reverse_eq (evenPalindromes_reverse Terminal) hrt

/-- The binary instance LMR state the conjecture for. -/
theorem binary_evenPalindromes_isPEG_of_realTime
    (hrt : RecognizedBy (EvenPalindromes Bool)) : RecognizedByTotalPEG (EvenPalindromes Bool) :=
  evenPalindromes_isPEG_of_realTime hrt

end PegSeparation
