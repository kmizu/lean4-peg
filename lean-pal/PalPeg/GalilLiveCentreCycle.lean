import PalPeg.GalilLiveCentreMismatch
import PalPeg.GalilLiveCentreShift

/-!
# The fallback cycle keeps the span and the centre invariants

`cycle_fallback_stepsAll` runs one main-loop cycle through a mismatch: from a
restarted state, an idle segment, the mismatching comparison and the fallback,
back to a restarted state. This file composes that run with the span relation
(`SpanRep`) and the leftmost-centre invariant (`MInv`): the fallback lands on
the leftmost live centre (`leftmost_after_fallback`, whose deadness premise is
`not_live_of_mismatch` at the mismatch), so both invariants are restored at the
end of the cycle.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- One main-loop cycle through a mismatch, carrying the span relation and the
leftmost-centre invariant to the restarted state it ends in. -/
theorem cycle_fallback_minv (onLetter leftFirst : GalilVM → Prop) (rs : GalilVM → GalilVM → Prop)
    (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ)
    (q : ℕ) (hq0 : 0 < q) (first : Fin 9) (h7 : first ≠ 7) (h8 : first ≠ 8) (delay : ℕ)
    {raw : List (Fin 2)}
    -- the restarted state and the idle segment
    {Rad : ℕ} {last : Counter} {r : GalilVM} (hR : Restarted raw r Rad last) (hi0 : ShiftIdle r)
    {c0 : Control}
    {es0 : List Bool} {cF : Control} {sF : GalilVM}
    (hseg0 : WatchSegE (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry)
      q first delay es0 c0 r cF sF)
    -- the mismatching comparison
    (hm : cF.mode = .scan) (hr : cF.replaying = false) (hc : cF.clock = 1) (hav : canRight sF.right)
    (vs : ScanVM) (vq : SearchVM) (hl : vs.left = left sF.left) (hrr : vs.right = right sF.right)
    (hmis : read (left sF.left) ≠ read (right sF.right))
    (hq : searchEffect (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry)
      false sF vq)
    (hch : chainAt false (decide (vq.search.mode = .found)) (vq.dp.config.tapes 11) (centre sF) (place sF)
      sF.center sF.radius sF.chain vs.chain)
    (hg : ¬ shiftGuardVM (afterMismatch sF vs vq))
    (ℓ : ℕ) (hv : value sF.length = ℓ)
    (heven : ∀ (a : Fin 2) (xs rs' q' : List (Fin 2)),
      right sF.right = represent ⟨a :: xs,(right sF.right).gap⟩ (rs'.map some) q' →
      ((GalilScaffoldPlace.stream ⟨a :: xs,(right sF.right).gap⟩).take (ℓ+1)).length % 2 = 0)
    -- the invariants at the start of the cycle
    (hS0 : SpanRep r) (hM0 : MInv raw c0 r) :
    ∃ (a : Fin 2) (xs rs' q' : List (Fin 2)),
      right sF.right = represent ⟨a :: xs,(right sF.right).gap⟩ (rs'.map some) q' ∧
      raw = (a :: xs).reverse ++ rs' ++ q' ∧
      ∃ (n : ℕ) (o : Bool) (t : GalilVM),
        Steps (galilFrameS (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry) q first)
          delay (1 + (n+1)) ⟨cF, sF⟩
          ⟨{cF with mode := .scan, clock := delay, output := o, replaying := decide (0 < chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right sF.right).gap⟩).take (ℓ+1))), odd := oddAt false (((GalilScaffoldPlace.stream ⟨a :: xs,(right sF.right).gap⟩).take (ℓ+1)).length - (2*chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right sF.right).gap⟩).take (ℓ+1))+1)), pair := pairAt (2*chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right sF.right).gap⟩).take (ℓ+1)))}, t⟩ ∧
        Restarted raw t 0 reset ∧ SpanRep t ∧
        MInv raw {cF with mode := .scan, clock := delay, output := o, replaying := decide (0 < chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right sF.right).gap⟩).take (ℓ+1))), odd := oddAt false (((GalilScaffoldPlace.stream ⟨a :: xs,(right sF.right).gap⟩).take (ℓ+1)).length - (2*chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right sF.right).gap⟩).take (ℓ+1))+1)), pair := pairAt (2*chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right sF.right).gap⟩).take (ℓ+1)))} t := by
  have hscan0 := hR.2.2.2.1
  have hRR0 := hR.2.2.2.2.1
  -- the centre invariant travels along the idle segment
  have hMF : MInv raw cF sF :=
    minv_watchSegE raw _ (fun _ => rfl) q first delay hseg0 Rad hscan0 hM0
  have hLF : Leftmost raw (position sF.right) (position sF.center) := minv_leftmost hMF hr
  -- the state at the mismatch
  obtain ⟨hrep, hfoc, hcan, _, hinvF⟩ := segment_mismatch_ready _ q first delay hR hseg0 hav
  have hcen : sF.center = r.center := watchSegE_center _ q first delay hseg0
  have hinvF' : ScanInvariant raw (position sF.center) (Rad + es0.count true) sF.left sF.right := by
    rw [hcen]; exact hinvF
  obtain ⟨_, _, hradv, hradc, _⟩ := watchSegE_heads _ q first delay hseg0
  have hRRF : RadiusRep sF.radius (Rad + es0.count true) := by
    refine ⟨hradc hRR0.1, ?_⟩
    rw [hradv, hRR0.2]; push_cast; ring
  have hSF : SpanRep sF := spanRep_watchSegE _ q first delay hseg0 hS0
  -- the mismatch kills the centre at the next place
  have hrpos : position (right sF.right) = position sF.right + 1 :=
    right_position sF.right hav (represented_position _ raw hinvF'.rightRep hinvF'.rightPresent).1
  have hdead : ¬ Live raw (position (right sF.right)) (position sF.center) := by
    rw [hrpos]; exact not_live_of_mismatch hinvF' hav hmis
  have hiF : ShiftIdle sF := by
    rw [shiftIdle_iff, watchSegE_remaining _ q first delay hseg0]
    exact (shiftIdle_iff r).1 hi0
  obtain ⟨a, xs, rs', q', hdec, hraw, n, o, t, hst, hRst, hrep', hpos, hpal, hmax, hlen⟩ :=
    fallback_restarted onLetter leftFirst rs centre place entry q hq0 first h7 h8 delay cF hm hr hc
      sF hiF hav vs vq hl hrr hmis hq hch hg hrep hfoc hcan ℓ hv heven
  -- the fallback lands on the leftmost live centre
  have hL' := leftmost_after_fallback raw hinvF' hRRF hSF hLF hav hdead a xs rs' q' hdec ℓ hv hpal hmax
  rw [hrpos] at hpos hL'
  refine ⟨a, xs, rs', q', hdec, hraw, n, o, t, hst, hRst, ?_, ?_⟩
  · refine spanRep_of_fallback hlen ?_
    rw [reset_eq_ofNat]
    exact GalilScaffoldChainCatch.canonical_nat _ hRst.2.2.2.2.1.1 0 hRst.2.2.2.2.1.2
  · exact minv_after_fallback hRst hrep' hpos (by rw [hpos]; exact hL') rfl

#print axioms cycle_fallback_minv

end PalPeg.GalilScaffoldChainInputSupply
