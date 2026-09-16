import PalPeg.GalilFallbackLanding

/-!
# `chosenRadius ≤ position`, from the fallback landing's own palindrome fact

`frontier_after_fallback` (`PalPeg/GalilFallbackLanding.lean`) needs
`hle : R ≤ position p` (`p = right s.right`, `R = chosenRadius (window)`) to
conclude `Frontier t` for the landing state `t`.  `fallback_landing` never
exports that inequality on its own, but it *does* export
`hpal : Manacher.PalAt (encoded raw) (position p - R) R`, and `PalAt`'s own
first conjunct (`r ≤ c`) already forces `R ≤ position p - R`, which bounds `R`
by `position p` since `Nat.sub_le` keeps `position p - R ≤ position p`.

`chosenRadius_le_position` extracts exactly that inequality from `hpal`, and
`frontier_after_fallback'` re-exports `frontier_after_fallback` with `hle`
derived that way, so only `fallback_landing`'s own exports are needed at the
call site.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open Manacher GalilScaffoldInputHead GalilScaffoldCounter

/-- **`chosenRadius_le_position`.**  The chosen radius `R` of a landing
palindrome centred at `position p - R` never exceeds `position p`: `PalAt`'s
own `r ≤ c` conjunct gives `R ≤ position p - R`, and `position p - R ≤ position p`
(`Nat.sub_le`) finishes it. -/
theorem chosenRadius_le_position {raw : List (Fin 2)} {p : GalilScaffoldInputHead.PlaceHead}
    {R : ℕ} (hpal : Manacher.PalAt (encoded raw) (position p - R) R) : R ≤ position p := by
  have h1 := hpal.1
  omega

/-- **`frontier_after_fallback'`.**  `frontier_after_fallback` restated with
its rewind-legality hypothesis `hle` derived from the landing palindrome
`hpal` instead of assumed outright, so it takes exactly the shape of facts
`fallback_landing` exports about its witness `t` (`t.right`, `t.replay`, and
the palindrome at `position (right s.right) - R`). -/
theorem frontier_after_fallback' {R : ℕ} {p : GalilScaffoldInputHead.PlaceHead} {t : GalilVM}
    {raw : List (Fin 2)}
    (hR : t.right = GalilScaffoldInputHead.left^[R] p)
    (hrep : t.replay = ofNat R)
    (hpal : Manacher.PalAt (encoded raw) (position p - R) R) :
    Frontier t :=
  frontier_after_fallback hR hrep (chosenRadius_le_position hpal)

#print axioms chosenRadius_le_position
#print axioms frontier_after_fallback'

end PalPeg.GalilScaffoldChainInputSupply
