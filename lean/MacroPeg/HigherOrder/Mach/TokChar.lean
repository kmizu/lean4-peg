import MacroPeg.HigherOrder.Mach.Tok

/-!
# Reading characters and strings on stacks

* `parseCharP`: read a character code (`parseNatP`) and check that it names a character (`Nat.isValidChar`:
  below `55296`, or between `57343` and `1114112`), comparing with constants (`cmpTop`); stop rejecting otherwise —
  exactly as `parseChar`.
* `parseStrP`: read `1 c₁ 1 c₂ … 0`, giving each character code to a sink — exactly as `parseStr`.
-/

namespace Shallot.MacroPeg.Mach

open Complexity
open Shallot.MacroPeg.Flat
open Shallot.MacroPeg.KExp

variable {K : Nat}

/-- Check the code on top of `a` (kept): stop rejecting unless it names a character. Scratch: `c t u g f`. -/
def checkCharP (a c t u g f : Fin K) (hat : a ≠ t) (hcu : c ≠ u) : NProg K :=
  .seq (npushC c 55296) (.seq (cmpTop a c t u g f hat hcu) (.seq (.prim (.pop c))
    (.ite f .zero (.prim (.pop f))
      (.seq (.prim (.pop f)) (.seq (npushC c 57343) (.seq (cmpTop a c t u g f hat hcu) (.seq (.prim (.pop c))
        (caseTop f [.halt false, .halt false,
          .seq (npushC c 1114112) (.seq (cmpTop a c t u g f hat hcu) (.seq (.prim (.pop c))
            (.ite f .zero (.prim (.pop f)) (.halt false))))] (.halt false)))))))))

/-- Read a character code onto `a`. -/
def parseCharP (tk a c t u g f : Fin K) (hat : a ≠ t) (hcu : c ≠ u) : NProg K :=
  .seq (parseNatP tk a) (checkCharP a c t u g f hat hcu)

/-- Read a string; `sink` takes each code from the top of `a`. -/
def parseStrP (tk a c t u g f : Fin K) (hat : a ≠ t) (hcu : c ≠ u) (sink : NProg K) : NProg K :=
  .seq (.loop tk .pos (.seq (.prim (.dec tk))
      (.ite tk .zero (.seq (.prim (.pop tk)) (.seq (parseCharP tk a c t u g f hat hcu) sink)) (.halt false))))
    (.ite tk .zero (.prim (.pop tk)) (.halt false))

theorem toNat_ofNat_iff (n : Nat) : (Char.ofNat n).toNat = n ↔ n.isValidChar := by
  unfold Char.ofNat
  split
  · rename_i h; simp [Char.ofNatAux, Char.toNat, h]
  · rename_i h
    constructor
    · intro e
      have : n = 0 := by rw [← e]; rfl
      subst this; exact absurd (Or.inl (by decide)) h
    · intro h'; exact absurd h' h

end Shallot.MacroPeg.Mach
