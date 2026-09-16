import PalPeg.GalilOracleLeaves2

/-!
# The `hmismatch` leaf of `GalilOracleLeaves2.h_oracle_of_leaves'`

`GalilGlueBLeaves.fallbackRoute_of_mismatch'` produces the *uncosted*
`FallbackRoute`.  This module produces the **costed** route
`GalilOracleMC2.FallbackRouteMC2` at an `InvLPC` entry, which is what
`cycleOutMC2C_of_fallback` consumes.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace PalPeg.GalilLeafMismatch

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilCheckpoints PalPeg.GalilTraceCost PalPeg.GalilLexMeasure
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleMC
open PalPeg.GalilGlueBLeaves PalPeg.GalilBranchInvariants2 PalPeg.GalilSegmentConstruct
open PalPeg.GalilOracleM PalPeg.GalilOracleMC2 PalPeg.GalilOracleGlueB
open PalPeg.GalilFinalAssembly2
open Manacher

/-- The DP/period pack at a mismatching state: the centre-side decomposition of
the input, the DP result for the centre window, and the period exclusion below
`lower`.  Nothing in the development produces it; it is the residue of
`FppData` that the counters along the segment do not carry. -/
def DpPack (raw : List (Fin 2)) (s : GalilVM) (Rad : ℕ) : Prop :=
  ∃ (a₀ : Fin 2) (ls₀ rs₀ q₀ : List (Fin 2)) (gap₀ : Bool) (lower span : ℕ)
    (y : GalilFppWide.Config 12),
    raw = (a₀ :: ls₀).reverse ++ rs₀ ++ q₀ ∧
    position s.center = position (represent ⟨a₀ :: ls₀,gap₀⟩ (rs₀.map some) q₀) ∧
    Rad ≤ span ∧
    GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a₀ :: ls₀,gap₀⟩).take (span+1)) lower 0 y ∧
    y.pc = 347 ∧
    (∀ δ, 0 < δ → δ ≤ lower → ¬ HasPeriod (Span raw (position s.center) Rad) (2*δ))

/-- **The costed mismatch route.**  `fallback_pack_span` re-run so that the
landing facts `FallbackRouteMC2` needs — the exact tick shape `1 + (n+1)`, the
landing centre (`hland`), `sT.center = sT.right` (`hCR`) — survive, with
`FppData` assembled from the segment counters (`fallbackCounters_of_seg`) and
the two residues `hdp`, `hfb`. -/
theorem fallbackRouteMC2_of_mismatch (entry q : ℕ) (hq0 : 0 < q) (first : Fin 9)
    (h7 : first ≠ 7) (h8 : first ≠ 8)
    (hsearch : ∀ (w : List (Fin 2)) (s : GalilVM), SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centreC placeC entry w) a s v)
    (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM)
    (hIC : InvLPC w c r)
    (hs : SegReachedW centreC placeC entry q first w c r c' t)
    (hnr : c'.replaying = false) (hc1 : c'.clock = 1) (hav : canRight t.right)
    (hmis : read (left t.left) ≠ read (right t.right))
    -- residue 1: the DP/period pack at the mismatch
    (hdp : ∀ Rad : ℕ, ScanInvariant w (position t.center) Rad t.left t.right → DpPack w t Rad)
    -- residue 2: the fallback phase costs at most `1588(ℓ+1)+836` ticks
    (hfb : ∀ (n ℓ : ℕ) (cT : Control) (sT : GalilVM), value t.length = ℓ →
      StepsAll (galilFrameS (PofC centreC placeC entry w) q first) 2048 (SoundScanNR w)
        (1 + (n + 1)) ⟨c', t⟩ ⟨cT, sT⟩ → n + 1 ≤ 1588 * (ℓ + 1) + 836)
    -- residue 3: the mismatch place is still inside the target
    (hpos : position (right t.right) ≤ 2 * m - 1) :
    FallbackRouteMC2 (PofC centreC placeC entry w) q first w m c r c' t := by
  obtain ⟨es, hw⟩ := hs.2
  have hK : FallbackCounters w t :=
    fallbackCounters_of_seg _ q first 2048 hw hs.1.center hIC.1.1.2 hav
  have hT : FallbackTick centreC placeC entry w t :=
    fallbackTick_of_mismatch centreC placeC entry w (hsearch w) t hs.1.idle hs.1.search
  obtain ⟨k0, hrun⟩ := hs.1.run
  have hout : OutputRel w c' t := stepsAll_last hrun hs.1.mode hnr
  obtain ⟨⟨Rad, hscan, hRR, hS⟩, hcan, ℓ, hv, heven⟩ := hK
  obtain ⟨vs, vq, hl, hrr, hqe, hch, hg⟩ := hT.data
  have hrep : GalilScaffoldInputTrace.Represents (right t.right).head w :=
    right_word t.right w hscan.rightRep hav
  have hfoc : (right t.right).head.focus ≠ none :=
    right_present t.right w hscan.rightRep hscan.rightPresent hav
  obtain ⟨a, xs, rs', q', hdec, hraw, n, o, sT, hstA, hRst, hposT, hpal, hmax, hrepT, hsiT, hchT,
      hRit, hCR, hlenT⟩ :=
    fallback_landing_len (onLetterVM w) leftFirstVM (restartVM entry) centreC placeC entry q hq0
      first h7 h8 2048 c' hs.1.mode hnr hc1 t hs.1.shiftIdle hav vs vq hl hrr hmis hqe hch hg
      hrep hfoc hcan ℓ hv heven rfl rfl hout
  obtain ⟨a₀, ls₀, rs₀, q₀, gap₀, lower, span, y, hraw₀, hC₀, hspan, hres, hidle, hlow⟩ :=
    hdp Rad hscan
  have hkC : Rad < position t.center := radius_lt_centre hscan
  have hrpos : position (right t.right) = position t.right + 1 :=
    right_position t.right hav (represented_position _ w hscan.rightRep hscan.rightPresent).1
  have hfbB : n + 1 ≤ 1588 * (ℓ + 1) + 836 := hfb n ℓ _ sT hv hstA
  have mkD : ∀ RR : ℕ,
      RR = chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right t.right).gap⟩).take (ℓ+1)) →
      FppData w t (n+1) RR := by
    intro RR hRR'
    exact ⟨Rad, ℓ, a, xs, rs', q', a₀, ls₀, rs₀, q₀, gap₀, lower, span, y,
      hscan, hRR, hS, hv, hkC, hdec, hraw, hraw₀, hC₀, hspan, hres, hidle, hlow, hRR', hfbB⟩
  have hprog : position t.center < position sT.center :=
    PalPeg.GalilCycleProgress.fallback_progress w hs.1.minv hnr hscan hRR hS hav hmis a xs rs' q'
      hdec ℓ hv hpal hmax hposT
  have hL := leftmost_after_fallback_landing w hs.1.minv hnr hscan hRR hS hav hmis a xs rs' q'
    hdec ℓ hv hpal hmax hposT
  have hSpan : SpanRep sT := spanRep_of_restarted_one hRst hlenT
  rcases Nat.eq_zero_or_pos
      (chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right t.right).gap⟩).take (ℓ+1)))
    with hz | hz
  · refine FallbackRouteMC2.landed (n+1) _ sT hstA (mkD 0 hz.symm) ?_ hCR ?_ hSpan hprog hpos
    · rw [hposT, hz]
    · have htrp : sT.replay = reset := by rw [hrepT, hz]; rfl
      refine inv_of_parts hRst ?_ ⟨rfl, by simp [hz], rfl⟩ (frontier_of_reset htrp)
        (replayRest_of_reset htrp) hsiT
      exact minv_after_fallback hRst hrepT (by rw [hposT, hrpos]) (by rw [← hrpos]; exact hL) rfl
  · refine FallbackRouteMC2.replaying (n+1) _ _ sT hstA (mkD _ rfl) ?_ hSpan hposT hCR hprog hpos
    exact
      { pos := hz
        rest := hRst
        mode := rfl
        clock := rfl
        replaying := by simp [hz]
        replay := hrepT
        minv := minv_after_fallback hRst hrepT (by rw [hposT, hrpos])
          (by rw [← hrpos]; exact hL) rfl
        frontier := frontier_after_fallback' hRit hrepT hpal
        shiftIdle := hsiT }

/-- **The `hmismatch` leaf of `GalilOracleLeaves2.h_oracle_of_leaves'`**, in the
exact shape that theorem expects, from the three residues. -/
theorem hmismatch_of_residues (entry q : ℕ) (hq0 : 0 < q) (first : Fin 9)
    (h7 : first ≠ 7) (h8 : first ≠ 8)
    (hsearch : ∀ (w : List (Fin 2)) (s : GalilVM), SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centreC placeC entry w) a s v)
    (hdp : ∀ (w : List (Fin 2)) (t : GalilVM) (Rad : ℕ),
      ScanInvariant w (position t.center) Rad t.left t.right → DpPack w t Rad)
    (hfb : ∀ (w : List (Fin 2)) (c' : Control) (t : GalilVM) (n ℓ : ℕ) (cT : Control)
        (sT : GalilVM), value t.length = ℓ →
      StepsAll (galilFrameS (PofC centreC placeC entry w) q first) 2048 (SoundScanNR w)
        (1 + (n + 1)) ⟨c', t⟩ ⟨cT, sT⟩ → n + 1 ≤ 1588 * (ℓ + 1) + 836)
    (hpos : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t → canRight t.right →
      position (right t.right) ≤ 2 * m - 1) :
    ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t →
      c'.replaying = false → c'.clock = 1 → canRight t.right →
      read (left t.left) ≠ read (right t.right) →
      FallbackRouteMC2 (PofC centreC placeC entry w) q first w m c r c' t := by
  intro w m c r c' t hm1 hmle hIC hrt hs hnr hc1 hav hmis
  exact fallbackRouteMC2_of_mismatch entry q hq0 first h7 h8 hsearch w m c r c' t hIC hs hnr hc1
    hav hmis (fun Rad hi => hdp w t Rad hi) (fun n ℓ cT sT => hfb w c' t n ℓ cT sT)
    (hpos w m c r c' t hm1 hmle hIC hrt hs hav)

#print axioms DpPack
#print axioms fallbackRouteMC2_of_mismatch
#print axioms hmismatch_of_residues

end PalPeg.GalilLeafMismatch
