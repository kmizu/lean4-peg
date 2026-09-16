import PalPeg.GalilScaffoldTopFallbackRestartAll
import PalPeg.GalilLiveCentreMismatch
import PalPeg.GalilFrontier

/-!
# The fallback cycle's landing state, in one lemma

`ASSEMBLY_PLAN.md`, 「H_run 構成計画」, obligation **L9**: `inv_after_fallback`
(`PalPeg/GalilRunInv.lean`) has to take the leftmost-live-centre fact `hL` and
the shift-idleness `hsiT` of the landing state as *hypotheses*, because
`fallback_restarted_soundNR` existentially quantifies its landing state `t` and
publishes only four facts about it (the run, `Restarted`, `t.replay`,
`position t.center`) — it drops the palindrome `hpal`, the maximality `hmax`
(which `fallback_restarted_All` does export) and everything about `t.remaining`
and `t.chain`.

`fallback_landing` below closes those two gaps: it has exactly the hypotheses of
`fallback_restarted_soundNR` and concludes, about *one* landing state, the
`SoundScanNR` run, `Restarted`, the landing control record verbatim,
`position t.center`, `PalAt`, the maximality, `t.replay`, `ShiftIdle t` and
`t.chain = .idle`.  `leftmost_after_fallback_landing` then turns the exported
`hpal`/`hmax` into the `Leftmost` fact at the landing centre.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-! ## (1) Everything the fallback cycle lands with -/

/-- **`fallback_landing`.**  The hypotheses of `fallback_restarted_soundNR`,
with all of `fallback_restarted_All`'s exports *and* the two residual facts
about the landing VM (`ShiftIdle t`, `t.chain = .idle`) stated about the same
witness `t`. -/
theorem fallback_landing (onLetter leftFirst : GalilVM → Prop) (rs : GalilVM → GalilVM → Prop)
    (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ)
    (q : ℕ) (hq0 : 0 < q) (first : Fin 9) (h7 : first ≠ 7) (h8 : first ≠ 8) (delay : ℕ)
    (c : Control) (hm : c.mode = .scan) (hr : c.replaying = false) (hc : c.clock = 1)
    (s : GalilVM) (hi : ShiftIdle s) (hav : canRight s.right)
    (vs : ScanVM) (vq : SearchVM) (hl : vs.left = left s.left) (hrr : vs.right = right s.right)
    (hmis : read (left s.left) ≠ read (right s.right))
    (hq : searchEffect (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry)
      false s vq)
    (hch : chainAt false (decide (vq.search.mode = .found)) (vq.dp.config.tapes 11) (centre s) (place s)
      s.center s.radius s.chain vs.chain)
    (hg : ¬ shiftGuardVM (afterMismatch s vs vq))
    {raw : List (Fin 2)} (hrep : GalilScaffoldInputTrace.Represents (right s.right).head raw)
    (hfoc : (right s.right).head.focus ≠ none)
    (hcan : Canonical s.length) (ℓ : ℕ) (hv : value s.length = ℓ)
    (heven : ∀ (a : Fin 2) (xs rs' q' : List (Fin 2)),
      right s.right = represent ⟨a :: xs,(right s.right).gap⟩ (rs'.map some) q' →
      ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)).length % 2 = 0)
    (honL : onLetter = onLetterVM raw) (hlF : leftFirst = leftFirstVM) (hout : OutputRel raw c s) :
    ∃ (a : Fin 2) (xs rs' q' : List (Fin 2)),
      right s.right = represent ⟨a :: xs,(right s.right).gap⟩ (rs'.map some) q' ∧
      raw = (a :: xs).reverse ++ rs' ++ q' ∧
      ∃ (n : ℕ) (o : Bool) (t : GalilVM),
        StepsAll (galilFrameS (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry) q first) delay (SoundScanNR raw) (1 + (n+1)) ⟨c, s⟩
          ⟨{c with mode := .scan, clock := delay, output := o, replaying := decide (0 < chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))), odd := oddAt false (((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)).length - (2*chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))+1)), pair := pairAt (2*chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)))}, t⟩ ∧
        Restarted raw t 0 reset ∧
        position t.center = position (right s.right) - chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)) ∧
        Manacher.PalAt (encoded raw) (position (right s.right) - chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)))
          (chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))) ∧
        (∀ r', 2*r'+1 ≤ ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)).length →
          Manacher.PalAt (encoded raw) (position (right s.right) - r') r' →
          r' ≤ chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))) ∧
        t.replay = ofNat (chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))) ∧
        ShiftIdle t ∧ t.chain = .idle ∧
        t.right = GalilScaffoldInputHead.left^[chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))] (right s.right) ∧
        t.center = t.right := by
  -- the fallback's choice on the encoded word
  let w0 : GalilScaffoldChainWatch.State :=
    ⟨⟨right s.right, GalilScaffoldChainConsume.ready 0 [] 0⟩, reset, reset⟩
  obtain ⟨a, xs, rs', q', hdec, hraw, hpal, hmax, h, hmoves, hhrep, hhfoc, hhpos, _⟩ :=
    fallback_replay (⟨s.center, s.left, right s.right, w0, s.cycle, s.radius⟩ : OnlyCompareState)
      hrep hfoc s.length hcan ℓ hv
  refine ⟨a, xs, rs', q', hdec, hraw, ?_⟩
  -- the fallback cycle on the controller
  obtain ⟨n, o, t, hst, hl', hR, hC, hrep', hrad, hlen, hw, hprog, hi', ho, ho0, hsearch, hlower⟩ :=
    scan_fallback_cycle_All onLetter leftFirst rs centre place entry q hq0 first h7 h8 delay c hm hr hc s hi hav
      vs vq hl hrr hmis hq hch hg ⟨a :: xs,(right s.right).gap⟩ hcan ℓ hv (stream_ne_nil _ _ _)
      (heven a xs rs' q' hdec)
  have hh : GalilScaffoldInputHead.left^[chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))]
      (right s.right) = h := (leftMoves_eq hmoves).symm
  -- the landing head positions, kept in their rewind form before `hh` is used
  have hRit : t.right = GalilScaffoldInputHead.left^[chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))] (right s.right) := hR
  have hCR : t.center = t.right := hC.trans hR.symm
  rw [hh] at hl' hR hC
  -- the landing state is restarted
  have hRst : Restarted raw t 0 reset := by
    refine ⟨hw, ?_, ?_, ?_, ?_, ?_, ?_, hlower, ofNat_canonical 0, by rw [reset_eq_ofNat, ofNat_value]; simp⟩
    · rw [hC]; exact hhrep
    · rw [hC]; exact hhfoc
    · rw [hC, hl', hR]; exact scan_initial raw h hhrep hhfoc
    · rw [hrad, reset_eq_ofNat]; exact ⟨ofNat_canonical 0, ofNat_value 0⟩
    · rw [hlen]; exact ofNat_canonical 1
    · rw [hsearch, hrad]
  refine ⟨n, o, t, ?_, hRst, by rw [hC]; exact hhpos, hpal, hmax, hrep', hi', hw, hRit, hCR⟩
  -- the run carries `SoundScanNR`
  refine hst (SoundScanNR raw) (fun st hns hsc => absurd hsc hns) (fun _ _ => hout) ?_
  intro _ hrepl
  have hr0 : chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)) = 0 := by
    simp at hrepl; omega
  obtain ⟨_, _, _, hscan, _⟩ := hRst
  intro hout' k hk hk2 hrk
  refine output_sound raw t c.output o hscan k hk hk2 hrk ?_ hout'
  have := ho0 hr0
  rw [honL, hlF] at this
  exact this

/-! ## (2) The leftmost live centre at the landing state -/

/-- **`leftmost_after_fallback_landing`.**  The landing centre of
`fallback_landing` is the leftmost live centre at the mismatch place.

The window-coverage side condition `hW : 2*(n - C) + 1 ≤ W` of
`leftmost_fallback` (`PalPeg/GalilLiveCentre.lean`) is *not* a hypothesis here:
`W` is the length of the candidate window `((stream ⟨a :: xs, gap⟩).take (ℓ+1))`,
which is `min (ℓ+1) (n+1)` with `ℓ = value s.length`, and `span_covers`
(used inside `leftmost_after_fallback`) derives `2*(n - C) + 1 ≤ ℓ` from the
scan invariant together with `RadiusRep s.radius Rad` and
`SpanRep s : value s.length = 2 * value s.radius + 1`.  So `SpanRep s`
below is exactly the hypothesis that pays for `hW`. -/
theorem leftmost_after_fallback_landing (raw : List (Fin 2)) {c : Control} {s t : GalilVM}
    {Rad : ℕ} (hM : MInv raw c s) (hnr : c.replaying = false)
    (hi : ScanInvariant raw (position s.center) Rad s.left s.right)
    (hRR : RadiusRep s.radius Rad) (hS : SpanRep s) (hav : canRight s.right)
    (hmis : read (left s.left) ≠ read (right s.right))
    (a : Fin 2) (xs rs' q' : List (Fin 2))
    (hdec : right s.right = represent ⟨a :: xs,(right s.right).gap⟩ (rs'.map some) q')
    (ℓ : ℕ) (hv : value s.length = ℓ)
    (hpal : Manacher.PalAt (encoded raw)
      (position (right s.right) - chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)))
      (chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))))
    (hmax : ∀ r', 2*r'+1 ≤ ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)).length →
      Manacher.PalAt (encoded raw) (position (right s.right) - r') r' →
      r' ≤ chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)))
    (hpos : position t.center = position (right s.right) -
      chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))) :
    Leftmost raw (position (right s.right)) (position t.center) := by
  have hL : Leftmost raw (position s.right) (position s.center) := minv_leftmost hM hnr
  have hrpos : position (right s.right) = position s.right + 1 :=
    right_position s.right hav (represented_position _ raw hi.rightRep hi.rightPresent).1
  have hdead : ¬ Live raw (position (right s.right)) (position s.center) := by
    rw [hrpos]; exact not_live_of_mismatch hi hav hmis
  rw [hpos]
  exact leftmost_after_fallback raw hi hRR hS hL hav hdead a xs rs' q' hdec ℓ hv hpal hmax

/-! ## (3) The replay frontier at the landing state -/

/-- **`frontier_after_fallback`.**  The landing state of `fallback_landing`
satisfies `Frontier`.

The landing right head is `R` rewind steps back from the mismatch place
(`hR`, the new conjunct of `fallback_landing`) and the landing replay counter
is exactly `R` (`hrep`, also exported there).  `left_iterate` says those `R`
steps only move *inside* already-arrived material: they cost `R` positions and
leave `arrived` unchanged.  So
`position t.right + R = position p ≤ 2 * arrived p = 2 * arrived t.right`,
the last inequality being `position_le_arrived`.

`hle : R ≤ position p` is the legality of the rewind; at the call site `p` is
`right s.right`, whose `Represents`/`ScanInvariant` data bounds `R` (the chosen
radius of a window ending at `p`) by `position p`. -/
theorem frontier_after_fallback {R : ℕ} {p : GalilScaffoldInputHead.PlaceHead} {t : GalilVM}
    (hR : t.right = GalilScaffoldInputHead.left^[R] p)
    (hrep : t.replay = ofNat R) (hle : R ≤ position p) : Frontier t := by
  intro m hm
  have hmR : m = R := ofNat_inj (hm.symm.trans hrep)
  subst hmR
  obtain ⟨h1, h2⟩ := left_iterate m p hle
  have h3 := position_le_arrived p
  rw [hR]
  omega

#print axioms fallback_landing
#print axioms leftmost_after_fallback_landing
#print axioms frontier_after_fallback

end PalPeg.GalilScaffoldChainInputSupply
