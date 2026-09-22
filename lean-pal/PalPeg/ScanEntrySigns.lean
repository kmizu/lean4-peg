import PalPeg.GalilFrontier
import PalPeg.GalilSpanCounter
import PalPeg.CloseoutLenNonneg

/-!
# The signs of the counters at the two entries out of `scan`

The local layer reads a counter tape as a natural number with a polarity bit, and the phase steps
of `shift` and of `copy` need the positive polarity of the counters they move.  A successor of a
scan state is built from its abstraction (`GhostSection.ghostOf`), so at the two entries the signs
have to come from the abstract tick: `entrySigns_of_scanTick`.  The source is a scan state with
the span ledger (`SpanRep`) and a nonnegative radius; the comparison raises the radius and does
not lower the length (`compareFound_counters`), `beginShiftVM` sets `remaining` and `cycle` afresh
and adds two to `length`, `beginFallback` sets the fpp work counter to `length + 1`.
-/

set_option autoImplicit false
namespace PalPeg.ScanEntrySigns

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (value inc ofNat reset inc_value)

/-- The comparison of a scan tick raises the radius by one and does not lower the length. -/
theorem compareFound_counters {P : Shared} {q : ℕ} {first : Fin 9} {s s' : GalilVM}
    (hcmp : compareFound P q first s s') :
    value s'.radius = value s.radius + 1 ∧ value s.length ≤ value s'.length := by
  obtain ⟨vs, vq, a, -, -, -, -, -, hteq⟩ := hcmp
  generalize chainBorn (decide (vq.search.mode = .found)) s.chain = born at hteq
  subst hteq
  have hlengthKept : (searchLens.set (scanLens.set s vs) vq).length = s.length := rfl
  cases a <;> cases born <;>
    simp [afterBirth, afterCompare, afterMismatch, radiusAfter, inc_value, hlengthKept] <;> omega

/-- **The signs of the counters at the two entries out of `scan`.**  The source is a scan state
with the span ledger and a nonnegative radius; `shift` sets `remaining` and `cycle` afresh and
adds two to `length`, `copy` sets the fpp work counter to `length + 1`. -/
theorem entrySigns_of_scanTick (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)
    {c c' : Control} {s t : GalilVM} (hscan : c.mode = Mode.scan)
    (hspan : SpanRep s) (hradius : 0 ≤ value s.radius)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) :
    c'.mode ≠ Mode.scan →
      0 ≤ value t.radius ∧ 0 ≤ value t.length ∧
        (c'.mode = Mode.shift → 0 ≤ value t.remaining ∧ 0 ≤ value t.cycle) ∧
        (c'.mode = Mode.copy → 0 ≤ value t.fpp.work) := by
  unfold SpanRep at hspan
  cases h <;> first
    | (intro hnotScan; exfalso; simp_all; done)
    | skip
  case scan_shift =>
    rename_i s' hmt hg hm hc hr hcmp hav hb
    obtain ⟨hrad, hlen⟩ := compareFound_counters hcmp
    obtain ⟨w, -, ht⟩ : beginShiftVM' s' t := hb
    intro _
    subst ht
    refine ⟨?_, ?_, fun _ => ⟨PalPeg.CloseoutLenNonneg.nonneg_ofNat _, ?_⟩,
      fun hland => Mode.noConfusion hland⟩
    · show 0 ≤ value s'.radius
      omega
    · show 0 ≤ value (inc (inc s'.length))
      rw [inc_value, inc_value]; omega
    · show 0 ≤ value reset
      exact PalPeg.CloseoutLenNonneg.nonneg_reset
  case scan_fallback =>
    rename_i s' hmt hm hc hg hr hcmp hav hb
    obtain ⟨hrad, hlen⟩ := compareFound_counters hcmp
    obtain ⟨pl, ht, -⟩ : beginFallbackVM' s' t := hb
    have ht' : t = beginFallbackAt pl s' := ht
    intro _
    subst ht'
    refine ⟨?_, ?_, fun hland => Mode.noConfusion hland, fun _ => ?_⟩
    · show 0 ≤ value s'.radius
      omega
    · show 0 ≤ value s'.length
      omega
    · show 0 ≤ value (inc s'.length)
      rw [inc_value]; omega

#print axioms entrySigns_of_scanTick

end PalPeg.ScanEntrySigns
