import PalPeg.GalilOriginPeriod
import PalPeg.GalilPeriodSpan
import PalPeg.GalilMinimalPeriod
import PalPeg.GalilCandidateWindow
import PalPeg.GalilLiveCentreShift
import PalPeg.GalilScaffoldTopOutputLife

/-!
# Minimality of the period at the first terminal comparison

At the terminal comparison of a chain the read origin `org` supplies

* the current palindrome `org.scan.palindrome` (centre `org.center`, radius `org.radius`),
* the resumed palindrome `(entry_scanInvariant he).palindrome`
  (centre `org.center + h`, radius `org.radius + 1 - h`, with `h = org.interior.length + 1`),
* the `2h`-periodicity of the right half that the verifier has already read,
  `org.origin_periodOn_right`.

`hasPeriod_span_of_next` turns those three into `HasPeriod (Span …) (2h)`, and
`no_short_period_of_minimal` (Fine–Wilf) upgrades that to minimality once the DP
search has ruled out candidates strictly between `lower` and `h` and no period
`2δ` with `0 < δ ≤ lower` exists.  `noBelow_first_of_result` is the same statement
with the DP minimality read off a `Result` whose output register holds `h`.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open Manacher GalilScaffoldInputHead GalilScaffoldChainVerifier

/-- At the terminal comparison described by an origin `org` whose centre is the place
`⟨a :: ls, gap⟩`: the span has period `2h` (from the verified right half and the two
palindromes), so DP minimality below `h` and the absence of periods `≤ 2·lower` give
no period below `2h`. -/
theorem noBelow_first (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    (org : ReadOrigin ((a :: ls).reverse ++ rs ++ q))
    (hC : org.center = position (represent ⟨a :: ls,gap⟩ (rs.map some) q))
    {s : OnlyCompareState} (he : Entry ((a :: ls).reverse ++ rs ++ q) org s)
    {lower : ℕ}
    (hcand : ∀ g, lower < g → g < org.interior.length+1 →
      ¬ GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (org.radius+1)) lower g)
    (hlow : ∀ δ, 0 < δ → δ ≤ lower →
      ¬ HasPeriod (Span ((a :: ls).reverse ++ rs ++ q) org.center org.radius) (2*δ)) :
    ∀ p, 0 < p → p < 2*(org.interior.length+1) →
      ¬ HasPeriod (Span ((a :: ls).reverse ++ rs ++ q) org.center org.radius) p := by
  have hh : 0 < org.interior.length+1 := Nat.succ_pos _
  have hk : 2*(org.interior.length+1) ≤ org.radius := org.size
  have h0 := org.scan.palindrome
  have h1 := (entry_scanInvariant he).palindrome
  have hright := org.origin_periodOn_right
  have hper : HasPeriod (Span ((a :: ls).reverse ++ rs ++ q) org.center org.radius)
      (2*(org.interior.length+1)) := by
    unfold Span
    exact hasPeriod_span_of_next hh hk h0 h1 hright
  -- the left end of the span is a genuine place of the stream
  have hpos := represented_position org.left.head ((a :: ls).reverse ++ rs ++ q)
    org.scan.leftRep org.scan.leftPresent
  have hlp : 1 ≤ position org.left := by
    unfold position
    split <;> omega
  have hleftPos := org.scan.leftPos
  have hle : org.radius ≤ org.center := h0.1
  have hkC : org.radius < org.center := by omega
  exact no_short_period_of_minimal a ls rs q gap hC hkC h0 hh hk hper hcand hlow

/-- The same with the DP minimality supplied by the DP result whose output is the origin's
semiperiod. -/
theorem noBelow_first_of_result (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    (org : ReadOrigin ((a :: ls).reverse ++ rs ++ q))
    (hC : org.center = position (represent ⟨a :: ls,gap⟩ (rs.map some) q))
    {s : OnlyCompareState} (he : Entry ((a :: ls).reverse ++ rs ++ q) org s)
    {lower span : ℕ} {y : GalilFppWide.Config 12}
    (hres : GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower 0 y)
    (hy : y.pc = 346) (hout : y.pos 11 = org.interior.length+1)
    (hlow : ∀ δ, 0 < δ → δ ≤ lower →
      ¬ HasPeriod (Span ((a :: ls).reverse ++ rs ++ q) org.center org.radius) (2*δ)) :
    ∀ p, 0 < p → p < 2*(org.interior.length+1) →
      ¬ HasPeriod (Span ((a :: ls).reverse ++ rs ++ q) org.center org.radius) p := by
  refine noBelow_first a ls rs q gap org hC he (lower := lower) ?_ hlow
  intro g _ hgh
  exact no_candidate_below_least (m := org.radius) hres hy g (by rw [hout]; exact hgh)

#print axioms noBelow_first
#print axioms noBelow_first_of_result

end PalPeg.GalilScaffoldChainInputSupply
