import PalPeg.GalilScaffoldTopShiftRound

/-!
# Preservation of the scan invariant at a matched comparison

At a matched comparison (R available, the outer symbols agree) the heads
move outward, the radius counter increments (`radius.inc()`, directly or
inside `advanceMatch`), centre and length are untouched: `ScanInv` holds
again with radius `r+1`. This is the per-tick step of the global invariant
for the comparison of `compareVM`/`compareFound`.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier

theorem afterCompare_center (s : GalilVM) (vs : ScanVM) (vq : SearchVM) : (afterCompare s vs vq).center = s.center := rfl
theorem afterCompare_left (s : GalilVM) (vs : ScanVM) (vq : SearchVM) : (afterCompare s vs vq).left = vs.left := rfl
theorem afterCompare_right (s : GalilVM) (vs : ScanVM) (vq : SearchVM) : (afterCompare s vs vq).right = vs.right := rfl
theorem afterCompare_radius (s : GalilVM) (vs : ScanVM) (vq : SearchVM) : (afterCompare s vs vq).radius = inc s.radius := rfl
theorem afterCompare_length (s : GalilVM) (vs : ScanVM) (vq : SearchVM) : (afterCompare s vs vq).length = inc (inc s.length) := rfl

/-- A matched comparison preserves the scan invariant with radius `r+1`. -/
theorem scanInv_compare_matched {raw : List (Fin 2)} {s : GalilVM} {r : ℕ} (hinv : ScanInv raw s r)
    (vs : ScanVM) (vq : SearchVM) (hl : vs.left = left s.left) (hr : vs.right = right s.right)
    (hav : canRight s.right) (hm : read (left s.left) = read (right s.right)) :
    ScanInv raw (afterCompare s vs vq) (r+1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [afterCompare_center, afterCompare_left, afterCompare_right, hl, hr]
    have he : ScanEvents raw (position s.center) r s.left s.right [true] (left s.left) (right s.right) :=
      .matched _ _ _ hav hm (.stop _ _ _)
    simpa using scan_events_invariant he hinv.scan
  · rw [afterCompare_radius, inc_value, hinv.radius]; push_cast; ring
  · rw [afterCompare_radius]; exact inc_canonical _ hinv.radiusCanon
  · rw [afterCompare_length]; exact inc_canonical _ (inc_canonical _ hinv.lengthCanon)
  · rw [afterCompare_center]; exact hinv.centre

#print axioms scanInv_compare_matched

end PalPeg.GalilScaffoldChainInputSupply
