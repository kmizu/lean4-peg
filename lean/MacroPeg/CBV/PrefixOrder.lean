import MacroPeg.CBV.PrefixSearch

namespace Shallot.MacroPeg.CBV.PrefixCounters

open RootObservation

/-- Search from the first counter upward for the second counter. -/
def leBody (self equal : Nat) : MExp := existsBody self equal 1

theorem leBody_firstOrder (self equal : Nat) : (leBody self equal).FirstOrder :=
  existsBody_firstOrder self equal 1

theorem le_predicate {g : MGrammar} {self equal : Nat}
    (hr : ruleAtM g.rules self = some ⟨2, leBody self equal⟩)
    (he : ruleAtM g.rules equal = some ⟨2, equalBody equal⟩)
    (x : List Char) (a b : Nat) (ha : a ≤ x.length) (hb : b ≤ x.length) :
    Predicate g .callByValuePar (.call self [.lit (x.take a), .lit (x.take b)]) x (a ≤ b) := by
  have ht : ∀ j, j ≤ x.length → Predicate g .callByValuePar
      (.call equal (.lit (x.take j) :: prefixValues x [b])) x (j = b) := by
    intro j hj
    exact Predicate.of_obs (equal_obs he x j b hj hb)
  have h := exists_predicate [b] hr x (fun j => j = b) ht a ha
  apply h.congr
  constructor
  · rintro ⟨j, hj, _, rfl⟩
    exact hj
  · intro hab
    exact ⟨b, hab, hb, rfl⟩

end Shallot.MacroPeg.CBV.PrefixCounters
