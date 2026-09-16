import PalPeg.GalilSpanCounter

/-!
# The fallback lands on the leftmost live centre

`leftmost_fallback` needs the fallback window to cover every radius below the
dying centre's one. The window is `(stream …).take (length+1)`, whose length is
`min (length+1) |stream …|`. Two facts make the cover hold at the mismatch
place `n+1`:

* `span_covers` — the length counter is the span, so `2·(n−C)+1 ≤ length`;
* the scan word at the right head is exactly as long as its place, so
  `|stream …| = n+1`, and `2·(n−C)+1 ≤ n+1` because the scan invariant puts
  the right head at `C+Rad` with `Rad ≤ C`.

Together they give `Leftmost` at the mismatch place for the fallback's centre.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- A represented place is as far right as its scan word is long: the stream of
`⟨a :: xs, g⟩` has exactly `position` many letters. This is
`position_represent` (`PalPeg/GalilScaffoldChainFallback.lean`), restated at
the head of a `PlaceHead` that is known to be a represented place. -/
theorem stream_length_of_place {p : PlaceHead} (a : Fin 2) (xs rs' q' : List (Fin 2))
    (hdec : p = represent ⟨a :: xs,p.gap⟩ (rs'.map some) q') :
    (GalilScaffoldPlace.stream ⟨a :: xs,p.gap⟩).length = position p := by
  rw [← position_represent a xs p.gap (rs'.map some) q', ← hdec]

/-- The fallback lands on the leftmost live centre at the mismatch place. -/
theorem leftmost_after_fallback (raw : List (Fin 2)) {s : GalilVM} {Rad : ℕ}
    (hi : ScanInvariant raw (position s.center) Rad s.left s.right)
    (hR : RadiusRep s.radius Rad) (hs : SpanRep s)
    (hL : Leftmost raw (position s.right) (position s.center))
    (hav : canRight s.right)
    (hdead : ¬ Live raw (position (right s.right)) (position s.center))
    (a : Fin 2) (xs rs' q' : List (Fin 2))
    (hdec : right s.right = represent ⟨a :: xs,(right s.right).gap⟩ (rs'.map some) q')
    (ℓ : ℕ) (hv : value s.length = ℓ)
    (hpal : PalAt (encoded raw)
      (position (right s.right) - chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)))
      (chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))))
    (hmax : ∀ r', 2*r'+1 ≤ ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)).length →
      PalAt (encoded raw) (position (right s.right) - r') r' →
      r' ≤ chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))) :
    Leftmost raw (position (right s.right))
      (position (right s.right) - chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))) := by
  -- the mismatch place is one past the right head
  have hpos : position (right s.right) = position s.right + 1 :=
    right_position s.right hav (represented_position _ raw hi.rightRep hi.rightPresent).1
  -- the scan word is as long as the mismatch place
  have hstream : (GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).length
      = position (right s.right) := stream_length_of_place a xs rs' q' hdec
  -- hence the window length is `min (ℓ+1) (n+1)`
  have hWlen : ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)).length
      = min (ℓ+1) (position s.right + 1) := by
    rw [List.length_take, hstream, hpos]
  have hcov : 2 * (position s.right - position s.center) + 1 ≤ ℓ := span_covers hi hR hs hv
  have hrp : position s.right = position s.center + Rad := hi.rightPos
  have hrad : Rad ≤ position s.center := hi.palindrome.1
  rw [hpos] at hdead hpal hmax ⊢
  refine leftmost_fallback hL hdead ?_ ?_ hpal hmax
  · rw [hWlen]
    omega
  · have hne : (GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1) ≠ [] := by
      apply List.ne_nil_of_length_pos
      rw [hWlen]
      omega
    have hcs := (chosen_spec _ hne).1
    rw [hWlen] at hcs
    omega

#print axioms stream_length_of_place
#print axioms leftmost_after_fallback

end PalPeg.GalilScaffoldChainInputSupply
