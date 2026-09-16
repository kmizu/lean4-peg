import PalPeg.GalilGlueBLeaves
import PalPeg.GalilOracleLocal
import PalPeg.GalilOracleGlueA
import PalPeg.GalilReplaySegment
import PalPeg.GalilFallbackLanding
import PalPeg.GalilFoundLanding
import PalPeg.GalilCycleNoShift
import PalPeg.GalilRunInv

/-!
# `InvLP`: the local recursion state with the entering counters

Closes gaps 1–3 of `PalPeg.GalilGlueBLeaves`.

1. `InvLP := InvL ∧ EntryCounters` holds at every landing:
   `invLP_init` (init sets `length := inc reset`, so `SpanRep` holds: `1 = 2·0+1`),
   `invLP_of_landed` (radius-`0` fallback; `scan_fallback_cycle_All` sets
   `length = ofNat 1`, re-exported by `fallback_landing_len`),
   `invLP_after_replayLanding` (replay: `spanRep_watchSegE`, radius `0 → R`),
   `invLP_of_foundLanding` (found; `SpanRep` travels through the cycle by
   `spanRep_found_shift` / `spanRep_found_noshift`, packaged in
   `foundCycle_step_span`).
2. `SegReachedW := SegReached ∧ WatchSegE`, produced by `segment_of_invLP`
   (`hout` now discharged by `InvL`; `hlive`, `hends` remain named).
3. `fallbackRouteP_of_mismatch''` / `fallbackRoute_of_mismatch''`: the mismatch
   exit from `InvLP` + `SegReachedW`, only `hsearch` remaining.

Gap left: `FoundRouteL` does not carry `SpanRep sT`; the found-route producer has
to return `FoundRouteLP` (the cycle-level fact is `foundCycle_step_span`, but its
landing is not linked to the route's `sT`).
-/

set_option autoImplicit false

namespace PalPeg.GalilInvPlus

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilRunSkeleton
open PalPeg.GalilOracleDischarge PalPeg.GalilOracleGlueB PalPeg.GalilGlueBLeaves
open PalPeg.GalilOracleLocal
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-! ## (1) The pack -/

/-- The local recursion state together with the entering counters. -/
def InvLP (raw : List (Fin 2)) (c : Control) (s : GalilVM) : Prop :=
  InvL raw c s ∧ EntryCounters raw s

theorem invLP_invL {raw : List (Fin 2)} {c : Control} {s : GalilVM} (h : InvLP raw c s) :
    InvL raw c s := h.1

/-- A restart with the span relation carries the entering counters. -/
theorem entryCounters_of_restarted {raw : List (Fin 2)} {r : GalilVM} {Rad : ℕ} {last : Counter}
    (hR : Restarted raw r Rad last) (hS : SpanRep r) : EntryCounters raw r :=
  ⟨Rad, hR.2.2.2.1, hR.2.2.2.2.1, hS, hR.2.2.2.2.2.1⟩

/-- A radius-`0` restart whose span counter reads `1` satisfies `SpanRep`. -/
theorem spanRep_of_restarted_one {raw : List (Fin 2)} {t : GalilVM} {last : Counter}
    (hR : Restarted raw t 0 last) (hlen : t.length = ofNat 1) : SpanRep t := by
  have hv : value t.radius = ((0 : ℕ) : ℤ) := hR.2.2.2.2.1.2
  unfold SpanRep
  rw [hlen, ofNat_value, hv]
  simp

/-! ### The `init` landing -/

/-- `init_restarted` with the span relation of the landing state exported. -/
theorem init_restarted_span (onLetter leftFirst guard : GalilVM → Prop)
    (bs bf rs : GalilVM → GalilVM → Prop)
    (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ)
    (q : ℕ) (first : Fin 9) (delay : ℕ) (c : Control) (hm : c.mode = .init) (s0 : GalilVM)
    (a : Fin 2) (rest : List (Fin 2)) (h0 : s0.right = initialHead (a :: rest))
    (hrad : s0.radius = reset) (hlen : s0.length = reset) :
    ∃ t : GalilVM,
      Tick (galilFrameS (galilShared onLetter leftFirst guard bs bf rs centre place entry) q first)
        delay ⟨c, s0⟩ ⟨{c with mode := .scan, output := true}, t⟩ ∧
      Restarted (a :: rest) t 0 reset ∧ position t.center = 1 ∧
      t.right = t.center ∧ t.remaining = s0.remaining ∧ t.replay = s0.replay ∧
      SpanRep t := by
  obtain ⟨t, ht, hR, hL, hC, hlen', hrad', hrem, hrep, _, _, hchain, hsearch, hlower, _⟩ :=
    init_tick onLetter leftFirst guard bs bf rs centre place entry q first delay c hm s0
  have htS := tick_S_of_tick _ q first delay ht (by rw [hm]; decide)
  have hS : SpanRep t := spanRep_of_init hlen' hrad' hrad hlen
  rw [h0] at hR hL hC
  refine ⟨t, htS, ?_, by rw [hC, initialHead_right_position], by rw [hR, hC], hrem, hrep, hS⟩
  refine ⟨hchain, ?_, ?_, ?_, ?_, ?_, ?_, hlower, ofNat_canonical 0,
    by rw [reset_eq_ofNat, ofNat_value]; simp⟩
  · rw [hC]; exact initialHead_right_represents a rest
  · rw [hC]; exact initialHead_right_focus a rest
  · rw [hL, hR, hC]
    exact scan_initial _ _ (initialHead_right_represents a rest) (initialHead_right_focus a rest)
  · rw [hrad', hrad, reset_eq_ofNat]; exact ⟨ofNat_canonical 0, ofNat_value 0⟩
  · rw [hlen', hlen, reset_eq_ofNat, inc_ofNat]; exact ofNat_canonical 1
  · rw [hsearch, hrad']

/-- **`invLP_init`.**  `inv_init`, with `InvLP` at the landing. -/
theorem invLP_init (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9)
    (s0 : GalilVM) (a : Fin 2) (rest : List (Fin 2))
    (h0 : s0.right = initialHead (a :: rest))
    (hrad : s0.radius = reset) (hlen : s0.length = reset)
    (hrepl : s0.replay = reset) (hsi : ShiftIdle s0) :
    ∃ (c1 : Control) (t : GalilVM),
      StepsAll (galilFrameS (PofC centre place entry (a :: rest)) q first) 2048
        (SoundScanNR (a :: rest)) 1 ⟨initial 2048, s0⟩ ⟨c1, t⟩ ∧
      InvLP (a :: rest) c1 t := by
  obtain ⟨t, ht, hR, hpos, hRt, hrem, hrp, hS⟩ :=
    init_restarted_span (onLetterVM (a :: rest)) leftFirstVM shiftGuardVM beginShiftVM'
      beginFallbackVM' (restartVM entry) centre place entry q first 2048 (initial 2048) rfl s0 a
      rest h0 hrad hlen
  have hst : StepsAll (galilFrameS (PofC centre place entry (a :: rest)) q first) 2048
      (SoundScanNR (a :: rest)) 1 ⟨initial 2048, s0⟩
      ⟨{(initial 2048) with mode := .scan, output := true}, t⟩ :=
    .succ (fun hsc => by cases hsc) ht
      (.zero _ (fun _ _ => outputRel_position_one a rest _ t (by rw [hRt, hpos])))
  have hMt : MInv (a :: rest) {(initial 2048) with mode := .scan, output := true} t := by
    refine minv_of_leftmost ?_ rfl
    rw [hRt, hpos]
    exact leftmost_one a rest
  have htrp : t.replay = reset := by rw [hrp, hrepl]
  have hI : Inv (a :: rest) {(initial 2048) with mode := .scan, output := true} t :=
    inv_of_parts hR hMt ⟨rfl, rfl, rfl⟩ (frontier_of_reset htrp) (replayRest_of_reset htrp)
      (by rw [shiftIdle_iff, hrem]; exact (shiftIdle_iff s0).1 hsi)
  exact ⟨_, t, hst, invL_of_run hst (invS_of_inv hI), entryCounters_of_restarted hR hS⟩

#print axioms invLP_init

/-! ### The radius-`0` fallback landing -/

/-- `fallback_landing` with `t.length = ofNat 1` exported as well. -/
theorem fallback_landing_len (onLetter leftFirst : GalilVM → Prop) (rs : GalilVM → GalilVM → Prop)
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
        t.center = t.right ∧ t.length = ofNat 1 := by
  let w0 : GalilScaffoldChainWatch.State :=
    ⟨⟨right s.right, GalilScaffoldChainConsume.ready 0 [] 0⟩, reset, reset⟩
  obtain ⟨a, xs, rs', q', hdec, hraw, hpal, hmax, h, hmoves, hhrep, hhfoc, hhpos, _⟩ :=
    fallback_replay (⟨s.center, s.left, right s.right, w0, s.cycle, s.radius⟩ : OnlyCompareState)
      hrep hfoc s.length hcan ℓ hv
  refine ⟨a, xs, rs', q', hdec, hraw, ?_⟩
  obtain ⟨n, o, t, hst, hl', hR, hC, hrep', hrad, hlen, hw, hprog, hi', ho, ho0, hsearch, hlower⟩ :=
    scan_fallback_cycle_All onLetter leftFirst rs centre place entry q hq0 first h7 h8 delay c hm hr hc s hi hav
      vs vq hl hrr hmis hq hch hg ⟨a :: xs,(right s.right).gap⟩ hcan ℓ hv (stream_ne_nil _ _ _)
      (heven a xs rs' q' hdec)
  have hh : GalilScaffoldInputHead.left^[chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))]
      (right s.right) = h := (leftMoves_eq hmoves).symm
  have hRit : t.right = GalilScaffoldInputHead.left^[chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))] (right s.right) := hR
  have hCR : t.center = t.right := hC.trans hR.symm
  rw [hh] at hl' hR hC
  have hRst : Restarted raw t 0 reset := by
    refine ⟨hw, ?_, ?_, ?_, ?_, ?_, ?_, hlower, ofNat_canonical 0, by rw [reset_eq_ofNat, ofNat_value]; simp⟩
    · rw [hC]; exact hhrep
    · rw [hC]; exact hhfoc
    · rw [hC, hl', hR]; exact scan_initial raw h hhrep hhfoc
    · rw [hrad, reset_eq_ofNat]; exact ⟨ofNat_canonical 0, ofNat_value 0⟩
    · rw [hlen]; exact ofNat_canonical 1
    · rw [hsearch, hrad]
  refine ⟨n, o, t, ?_, hRst, by rw [hC]; exact hhpos, hpal, hmax, hrep', hi', hw, hRit, hCR, hlen⟩
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

/-- `fallback_pack` with `SpanRep` at the landing. -/
theorem fallback_pack_span (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (hq0 : 0 < q) (first : Fin 9) (h7 : first ≠ 7) (h8 : first ≠ 8)
    (raw : List (Fin 2)) (c : Control) (s : GalilVM)
    (hm : c.mode = .scan) (hr : c.replaying = false) (hc : c.clock = 1)
    (hsi : ShiftIdle s) (hav : canRight s.right)
    (hmis : read (left s.left) ≠ read (right s.right))
    (hM : MInv raw c s) (hK : FallbackCounters raw s)
    (hT : FallbackTick centre place entry raw s)
    (hout : OutputRel raw c s) :
    ∃ (n R : ℕ) (cT : Control) (t : GalilVM),
      StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundScanNR raw)
        (1 + (n + 1)) ⟨c, s⟩ ⟨cT, t⟩ ∧
      position s.center < position t.center ∧
      (R = 0 → Inv raw cT t) ∧
      (0 < R → ReplayLanding raw cT t R) ∧ SpanRep t := by
  obtain ⟨⟨Rad, hscan, hRR, hS⟩, hcan, ℓ, hv, heven⟩ := hK
  obtain ⟨vs, vq, hl, hrr, hq, hch, hg⟩ := hT.data
  have hrep : GalilScaffoldInputTrace.Represents (right s.right).head raw :=
    right_word s.right raw hscan.rightRep hav
  have hfoc : (right s.right).head.focus ≠ none :=
    right_present s.right raw hscan.rightRep hscan.rightPresent hav
  obtain ⟨a, xs, rs', q', hdec, hraw, n, o, t, hstA, hRst, hposT, hpal, hmax, hrepT, hsiT, hchT,
      hRit, hCR, hlenT⟩ :=
    fallback_landing_len (onLetterVM raw) leftFirstVM (restartVM entry) centre place entry q hq0
      first h7 h8 2048 c hm hr hc s hsi hav vs vq hl hrr hmis hq hch hg hrep hfoc hcan
      ℓ hv heven rfl rfl hout
  have hL : Leftmost raw (position (right s.right)) (position t.center) :=
    leftmost_after_fallback_landing raw hM hr hscan hRR hS hav hmis a xs rs' q' hdec
      ℓ hv hpal hmax hposT
  have hrpos : position (right s.right) = position s.right + 1 :=
    right_position s.right hav (represented_position _ raw hscan.rightRep hscan.rightPresent).1
  have hprog : position s.center < position t.center :=
    PalPeg.GalilCycleProgress.fallback_progress raw hM hr hscan hRR hS hav hmis a xs rs' q' hdec
      ℓ hv hpal hmax hposT
  have hMT : MInv raw
      { c with
        mode := .scan, clock := 2048, output := o,
        replaying := decide (0 < chosenRadius
          ((GalilScaffoldPlace.stream ⟨a :: xs, (right s.right).gap⟩).take (ℓ + 1))),
        odd := oddAt false
          (((GalilScaffoldPlace.stream ⟨a :: xs, (right s.right).gap⟩).take
              (ℓ + 1)).length -
            (2 * chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs, (right s.right).gap⟩).take
              (ℓ + 1)) + 1)),
        pair := pairAt (2 * chosenRadius
          ((GalilScaffoldPlace.stream ⟨a :: xs, (right s.right).gap⟩).take
            (ℓ + 1))) } t :=
    minv_after_fallback hRst hrepT (by rw [hposT, hrpos]) (by rw [← hrpos]; exact hL) rfl
  refine ⟨n, chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs, (right s.right).gap⟩).take
      (ℓ + 1)), _, t, hstA, hprog, ?_, ?_, spanRep_of_restarted_one hRst hlenT⟩
  · intro hz
    have htrp : t.replay = reset := by rw [hrepT, hz]; rfl
    exact inv_of_parts hRst hMT ⟨rfl, by simp [hz], rfl⟩ (frontier_of_reset htrp)
      (replayRest_of_reset htrp) hsiT
  · intro hz
    exact
      { pos := hz
        rest := hRst
        mode := rfl
        clock := rfl
        replaying := by simp [hz]
        replay := hrepT
        minv := hMT
        frontier := frontier_after_fallback' hRit hrepT hpal
        shiftIdle := hsiT }

#print axioms fallback_landing_len
#print axioms fallback_pack_span

/-! ### Fallback routes carrying the span relation -/

/-- `FallbackRoute`'s two non-report routes, with `SpanRep` at the landing. -/
inductive FallbackRouteP (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (c : Control) (r : GalilVM) : Prop
  /-- the FPP chose radius `0` -/
  | landed (cT : Control) (sT : GalilVM)
      (hst : ∃ k, StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048
        (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
      (hI : Inv raw cT sT) (hS : SpanRep sT) (hprog : position r.center < position sT.center)
  /-- the FPP chose a positive radius -/
  | replaying (cT : Control) (sT : GalilVM) (R : ℕ)
      (hst : ∃ k, StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048
        (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
      (hL : ReplayLanding raw cT sT R) (hS : SpanRep sT)
      (hprog : position r.center < position sT.center)

theorem FallbackRouteP.toRoute {centre : GalilVM → Fin 3}
    {place : GalilVM → GalilScaffoldPlace.Place} {entry q : ℕ} {first : Fin 9}
    {raw : List (Fin 2)} {c : Control} {r : GalilVM}
    (h : FallbackRouteP centre place entry q first raw c r) :
    FallbackRoute centre place entry q first raw c r := by
  cases h with
  | landed cT sT hst hI _ hprog => exact .landed cT sT hst hI hprog
  | replaying cT sT R hst hL _ hprog => exact .replaying cT sT R hst hL hprog

theorem FallbackRouteP.toRouteL {centre : GalilVM → Fin 3}
    {place : GalilVM → GalilScaffoldPlace.Place} {entry q : ℕ} {first : Fin 9}
    {raw : List (Fin 2)} {c : Control} {r : GalilVM}
    (h : FallbackRouteP centre place entry q first raw c r) :
    FallbackRouteL (PofC centre place entry raw) q first raw c r := by
  cases h with
  | landed cT sT hst hI _ hprog => exact .landed cT sT hst hI hprog
  | replaying cT sT R hst hL _ hprog => exact .replaying cT sT R hst hL hprog

/-- `fallbackRoute_of_mismatch`, with `SpanRep` at the landing. -/
theorem fallbackRouteP_of_mismatch (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (hq0 : 0 < q) (first : Fin 9)
    (h7 : first ≠ 7) (h8 : first ≠ 8) (raw : List (Fin 2))
    (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM)
    (hs : SegReached centre place entry q first raw c r c' t)
    (hnr : c'.replaying = false) (hc1 : c'.clock = 1) (hav : canRight t.right)
    (hmis : read (left t.left) ≠ read (right t.right))
    (hK : FallbackCounters raw t) (hT : FallbackTick centre place entry raw t) :
    FallbackRouteP centre place entry q first raw c r := by
  obtain ⟨k0, hrun⟩ := hs.run
  have hout : OutputRel raw c' t := stepsAll_last hrun hs.mode hnr
  obtain ⟨n, R, cT, sT, hstA, hprog, hz, hp, hS⟩ :=
    fallback_pack_span centre place entry q hq0 first h7 h8 raw c' t hs.mode hnr hc1 hs.shiftIdle
      hav hmis hs.minv hK hT hout
  have hst : ∃ k, StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048
      (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ :=
    ⟨k0 + (1 + (n + 1)), stepsAll_trans hrun hstA⟩
  have hprog' : position r.center < position sT.center := by
    rw [← hs.center]; exact hprog
  rcases Nat.eq_zero_or_pos R with h0 | h0
  · exact .landed cT sT hst (hz h0) hS hprog'
  · exact .replaying cT sT R hst (hp h0) hS hprog'

/-! ## (2) The segment, with its `WatchSegE` derivation kept -/

/-- `SegReached` together with the segment itself. -/
def SegReachedW (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM) : Prop :=
  SegReached centre place entry q first raw c r c' t ∧
    ∃ es, WatchSegE (PofC centre place entry raw) q first 2048 es c r c' t

/-- **`segment_of_invLP`.**  `segment_of_invS` over `InvLP`: `hout` is now
discharged by `InvL`'s `OutputRel`, and the segment derivation is kept.
Remaining named hypotheses: `hlive`, `hends` (as in `segment_of_invS`). -/
theorem segment_of_invLP (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry raw) a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      searchEffect (PofC centre place entry raw) a s v →
      PalPeg.GalilBranchInvariants2.SearchReady v)
    (hlive : ∀ (c : Control) (r : GalilVM), InvLP raw c r → ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry raw) q first) 2048 m ⟨c, r⟩ z →
      CentreLive z.ctl z.vm)
    (hends : ∀ (c : Control) (r : GalilVM), InvLP raw c r → ∃ n : ℕ,
      ∀ (es : List Bool) (c' : Control) (t : GalilVM),
        WatchSegE (PofC centre place entry raw) q first 2048 es c r c' t →
        es.length = n → PalPeg.GalilSegmentConstruct.SegEnd (PofC centre place entry raw) c' t) :
    ∀ (c : Control) (r : GalilVM), InvLP raw c r →
      ∃ (c' : Control) (t : GalilVM),
        SegReachedW centre place entry q first raw c r c' t ∧
        PalPeg.GalilSegmentConstruct.SegEnd (PofC centre place entry raw) c' t := by
  intro c r hIP
  have hI : InvS raw c r := hIP.1.1
  obtain ⟨hm, hclk, hidle, hsr, hM, R, hi, hfr, hrr, hsi⟩ :
      c.mode = Mode.scan ∧ 1 ≤ c.clock ∧ r.chain = ChainVM.idle ∧
      PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get r) ∧ MInv raw c r ∧
      ∃ R : ℕ, ScanInvariant raw (position r.center) R r.left r.right ∧ Frontier r ∧
        ReplayRest c r ∧ ShiftIdle r := by
    rcases hI with h | ⟨k, h⟩
    · obtain ⟨Rad, last, hR⟩ := h.rest
      exact ⟨h.mode.1, by rw [h.mode.2.2]; omega, hR.1, h.search, h.minv, Rad,
        hR.2.2.2.1, h.frontier, h.rest_replay, h.shiftIdle⟩
    · exact ⟨h.mode.1, by rw [h.mode.2.2]; omega, h.chainIdle, h.search, h.minv, k,
        h.scan, h.frontier, h.rest_replay, h.shiftIdle⟩
  obtain ⟨n, hn⟩ := hends c r hIP
  obtain ⟨es, c', t, r', hseg, hm', hclk', hidle', hsrt, hMt, hit, hlen⟩ :=
    PalPeg.GalilSegmentConstruct.watchSegE_construct raw (PofC centre place entry raw) hex q
      first 2048 (by norm_num) hsearch hpres n c r R hm hclk hidle hsr hM hi
  have hEnd : PalPeg.GalilSegmentConstruct.SegEnd (PofC centre place entry raw) c' t := by
    rcases hlen with h0 | h0
    · exact hn es c' t hseg h0
    · exact h0
  obtain ⟨k1, h1⟩ :=
    watchSegE_stepsAll raw (PofC centre place entry raw) rfl rfl q first 2048 hseg
      (position r.center) R hi hIP.1.2
  have hrun : ∃ k, StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048
      (SoundScanNR raw) k ⟨c, r⟩ ⟨c', t⟩ :=
    ⟨k1, stepsAll_mono (fun _ h0 _ _ => h0) h1⟩
  have hsteps : Steps (galilFrameS (PofC centre place entry raw) q first) 2048 es.length
      ⟨c, r⟩ ⟨c', t⟩ := watchSegE_steps_length _ q first 2048 hseg
  have hfrt : Frontier t ∧ ReplayRest c' t :=
    frontier_replayRest_of_scan (onLetterVM raw) leftFirstVM centre place entry q first 2048
      hsteps hm (hlive c r hIP) hfr hrr
  have hsit : ShiftIdle t := by
    rw [shiftIdle_iff, watchSegE_remaining _ q first 2048 hseg]
    exact (shiftIdle_iff r).1 hsi
  exact ⟨c', t,
    ⟨{ run := hrun
       center := watchSegE_center _ q first 2048 hseg
       mode := hm'
       clock := hclk'
       idle := hidle'
       minv := hMt
       search := hsrt
       input := hit.rightRep
       frontier := hfrt.1
       shiftIdle := hsit
       scan := ⟨r', hit⟩ }, es, hseg⟩, hEnd⟩

/-! ## (3) The mismatch exit, with `hseg` and `hE` discharged -/

/-- **`fallbackRouteP_of_mismatch''`.**  The mismatch exit from an `InvLP`
state: the segment comes from `SegReachedW`, the entering counters from
`InvLP`.  Only the oracle's own `hsearch` remains. -/
theorem fallbackRouteP_of_mismatch'' (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (hq0 : 0 < q) (first : Fin 9)
    (h7 : first ≠ 7) (h8 : first ≠ 8) (raw : List (Fin 2))
    (hsearch : ∀ s : GalilVM, PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry raw) a s v)
    (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM)
    (hI : InvLP raw c r)
    (hs : SegReachedW centre place entry q first raw c r c' t)
    (hnr : c'.replaying = false) (hc1 : c'.clock = 1) (hav : canRight t.right)
    (hmis : read (left t.left) ≠ read (right t.right)) :
    FallbackRouteP centre place entry q first raw c r := by
  obtain ⟨hs0, es, hw⟩ := hs
  exact fallbackRouteP_of_mismatch centre place entry q hq0 first h7 h8 raw c r c' t hs0 hnr hc1
    hav hmis (fallbackCounters_of_seg _ q first 2048 hw hs0.center hI.2 hav)
    (fallbackTick_of_mismatch centre place entry raw hsearch t hs0.idle hs0.search)

/-- **`fallbackRoute_of_mismatch''`.**  The same, in `FallbackRoute` form. -/
theorem fallbackRoute_of_mismatch'' (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (hq0 : 0 < q) (first : Fin 9)
    (h7 : first ≠ 7) (h8 : first ≠ 8) (raw : List (Fin 2))
    (hsearch : ∀ s : GalilVM, PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry raw) a s v)
    (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM)
    (hI : InvLP raw c r)
    (hs : SegReachedW centre place entry q first raw c r c' t)
    (hnr : c'.replaying = false) (hc1 : c'.clock = 1) (hav : canRight t.right)
    (hmis : read (left t.left) ≠ read (right t.right)) :
    FallbackRoute centre place entry q first raw c r :=
  (fallbackRouteP_of_mismatch'' centre place entry q hq0 first h7 h8 raw hsearch c r c' t hI hs
    hnr hc1 hav hmis).toRoute

/-! ## (1, cont.) `InvLP` at the fallback landings -/

/-- The radius-`0` landing carries `InvLP`. -/
theorem invLP_of_landed {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {k : ℕ}
    {x : State GalilVM} {cT : Control} {sT : GalilVM}
    (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k x ⟨cT, sT⟩)
    (hI : Inv raw cT sT) (hS : SpanRep sT) : InvLP raw cT sT := by
  obtain ⟨Rad, last, hR⟩ := hI.rest
  exact ⟨invL_of_run hst (invS_of_inv hI), entryCounters_of_restarted hR hS⟩

/-- **The positive-radius landing, replayed, carries `InvLP`.**  The replay
segment keeps `SpanRep` (`spanRep_watchSegE`), moves the radius counter from
`0` to `R` (`radiusRep_watchSegE`, `es.count true = R`) and keeps the length
canonical.  `hout` is `replay_after_fallback`'s own leftover, as in
`cycleOutL_of_replayLanding`. -/
theorem invLP_after_replayLanding (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry raw) a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      searchEffect (PofC centre place entry raw) a s v →
      PalPeg.GalilBranchInvariants2.SearchReady v)
    (hquiet : PalPeg.GalilReplaySegment.SearchQuiet (PofC centre place entry raw))
    (hout : ∀ (c' : Control) (t' : GalilVM) (k : ℕ),
      PalPeg.GalilReplaySegment.InvScan 2048 raw c' t' k → SoundScanNR raw ⟨c', t'⟩)
    (c : Control) (r : GalilVM) (cT : Control) (sT : GalilVM) (R : ℕ)
    (hst : ∃ k, StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048
      (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
    (hL : ReplayLanding raw cT sT R) (hS : SpanRep sT)
    (hprog : position r.center < position sT.center) :
    ∃ (c' : Control) (t' : GalilVM) (k : ℕ),
      StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundScanNR raw) k
        ⟨c, r⟩ ⟨c', t'⟩ ∧
      InvLP raw c' t' ∧ position r.center < position t'.center := by
  obtain ⟨es, c', t', hseg, hrun, _hlen, hcnt, _hrpos, hcen, hIS⟩ :=
    PalPeg.GalilReplaySegment.replay_after_fallback raw (PofC centre place entry raw) q first 2048
      hex (by norm_num) hsearch hpres hquiet R hL.pos cT sT hL.mode hL.clock hL.replaying
      hL.rest hL.replay hL.minv hL.frontier hL.shiftIdle
  obtain ⟨k, hst1⟩ := hst
  have hall := stepsAll_trans hst1 (hrun (hout c' t' R hIS))
  have hRR : RadiusRep t'.radius R := by
    have h0 := radiusRep_watchSegE _ q first 2048 hseg hL.rest.2.2.2.2.1
    rw [hcnt, Nat.zero_add] at h0
    exact h0
  have hE : EntryCounters raw t' :=
    entryCounters_of_invScan hIS hRR (spanRep_watchSegE _ q first 2048 hseg hS)
      (canonical_length_watchSegE _ q first 2048 hseg hL.rest.2.2.2.2.2.1)
  refine ⟨c', t', k + es.length, hall, ⟨invL_of_run hall (Or.inr ⟨R, hIS⟩), hE⟩, ?_⟩
  rw [hcen]
  exact hprog

/-- Every non-report fallback route re-enters the recursion at an `InvLP`
state, with the centre strictly advanced. -/
theorem invLP_of_fallbackRouteP (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry raw) a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      searchEffect (PofC centre place entry raw) a s v →
      PalPeg.GalilBranchInvariants2.SearchReady v)
    (hquiet : PalPeg.GalilReplaySegment.SearchQuiet (PofC centre place entry raw))
    (hout : ∀ (c' : Control) (t' : GalilVM) (k : ℕ),
      PalPeg.GalilReplaySegment.InvScan 2048 raw c' t' k → SoundScanNR raw ⟨c', t'⟩)
    (c : Control) (r : GalilVM) (h : FallbackRouteP centre place entry q first raw c r) :
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ),
      StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundScanNR raw) k
        ⟨c, r⟩ ⟨cT, sT⟩ ∧
      InvLP raw cT sT ∧ position r.center < position sT.center := by
  cases h with
  | landed cT sT hst hI hS hprog =>
    obtain ⟨k, hst⟩ := hst
    exact ⟨cT, sT, k, hst, invLP_of_landed hst hI hS, hprog⟩
  | replaying cT sT R hst hL hS hprog =>
    exact invLP_after_replayLanding centre place entry q first raw hex hsearch hpres hquiet hout
      c r cT sT R hst hL hS hprog

#print axioms FallbackRouteP.toRoute
#print axioms FallbackRouteP.toRouteL
#print axioms fallbackRouteP_of_mismatch
#print axioms segment_of_invLP
#print axioms fallbackRouteP_of_mismatch''
#print axioms fallbackRoute_of_mismatch''
#print axioms invLP_of_landed
#print axioms invLP_after_replayLanding
#print axioms invLP_of_fallbackRouteP

/-! ## (1, cont.) The span relation across the found cycles -/

/-- **The no-shift found cycle keeps `SpanRep`** from the restarted state to
the landing record of `cycle_found_noshift_*`. -/
theorem spanRep_found_noshift (P : Shared) (qq : ℕ) (first : Fin 9) (delay : ℕ)
    {r : GalilVM} {c0 : Control}
    {es0 : List Bool} {cF : Control} {sF : GalilVM} (hseg0 : WatchSegE P qq first delay es0 c0 r cF sF)
    (vq : SearchVM) (ch : ChainVM) (oF : Bool)
    {es : List Bool} {c2 : Control} {s2 : GalilVM}
    (hprepSeg : WatchSegE P qq first delay es {cF with clock := delay, output := oF, replaying := false}
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) c2 s2)
    {c3 : Control} {s3 : GalilVM} (hseg : WatchSeg P qq first delay c2 s2 c3 s3)
    (vs3 : ScanVM) (vq3 : SearchVM) (w3' : GalilScaffoldChainWatch.State) (entry : ℕ)
    (hS0 : SpanRep r) :
    SpanRep {(afterCompare s3 vs3 vq3) with chain := .idle, lower := w3'.machine.control.last, search := GalilScaffoldSearchFinish.begin w3'.machine.control.last (afterCompare s3 vs3 vq3).radius, dp := GalilScaffoldControl.reset entry (afterCompare s3 vs3 vq3).dp} := by
  have h1 := spanRep_watchSegE P qq first delay hseg0 hS0
  have h2 := spanRep_watchSegE P qq first delay hprepSeg
    (spanRep_afterCompare (vs := ⟨left sF.left, right sF.right, ch⟩) (vq := vq) h1)
  have h3 := spanRep_watchSeg P qq first delay hseg h2
  exact spanRep_afterCompare (vs := vs3) (vq := vq3) h3

/-- **The found cycle with a shift keeps `SpanRep`**: idle segment, found
match, preparation, watch, the shift (`spanRep_shift`), the rounds, the final
segment and the breaking match. -/
theorem spanRep_found_shift (P : Shared) (qq : ℕ) (first : Fin 9) (delay : ℕ)
    {r : GalilVM} {c0 : Control}
    {es0 : List Bool} {cF : Control} {sF : GalilVM} (hseg0 : WatchSegE P qq first delay es0 c0 r cF sF)
    (vq : SearchVM) (ch : ChainVM) (oF : Bool)
    {es : List Bool} {c2 : Control} {s2 : GalilVM}
    (hprepSeg : WatchSegE P qq first delay es {cF with clock := delay, output := oF, replaying := false}
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) c2 s2)
    {cM : Control} {sM : GalilVM} (hseg : WatchSeg P qq first delay c2 s2 cM sM)
    (h : ℕ) (w : GalilScaffoldChainWatch.State) (s2' : GalilVM) (t' : ShiftState)
    (v : GalilScaffoldChainWatch.State) (cycle : Counter)
    (hchain : ChainShiftRun ⟨sM.center, left sM.left, ofNat h, inc sM.radius, inc (inc sM.length)⟩
      (GalilScaffoldChainWatch.immediate w) reset h t' v cycle)
    {m : ℕ} {c1 c' : Control} {s' : GalilVM}
    (hrounds : Rounds P qq first delay h m c1 (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c' s')
    {n : ℕ} {c3 : Control} {s3 : GalilVM} (hseg3 : ScanSeg P qq first delay n c' s' c3 s3)
    (vs3 : ScanVM) (vq3 : SearchVM) (w3' : GalilScaffoldChainWatch.State) (entry : ℕ)
    (hS0 : SpanRep r) :
    SpanRep (foundLandingVM (afterCompare s3 vs3 vq3) w3' entry) := by
  have h1 := spanRep_watchSegE P qq first delay hseg0 hS0
  have h2 := spanRep_watchSegE P qq first delay hprepSeg
    (spanRep_afterCompare (vs := ⟨left sF.left, right sF.right, ch⟩) (vq := vq) h1)
  have h3 := spanRep_watchSeg P qq first delay hseg h2
  have h4 := spanRep_shift h s2' hchain h3
  have h5 := spanRep_rounds P qq first delay h hrounds h4
  have h6 := spanRep_scanSeg P qq first delay hseg3 h5
  exact spanRep_afterCompare (vs := vs3) (vq := vq3) h6

/-- **`foundCycle_step_span`.**  `foundCycle_step`, with `SpanRep` and the
controller facts at the landing. -/
theorem foundCycle_step_span (P : Shared) (qq : ℕ) (first : Fin 9) (delay : ℕ)
    (raw : List (Fin 2)) (c0 : Control) (r : GalilVM) (hC : FoundCycle P qq first delay raw c0 r)
    (Rad : ℕ) (last : Counter) (hR : Restarted raw r Rad last) (hM0 : MInv raw c0 r)
    (hS0 : SpanRep r) :
    ∃ (cT : Control) (sT : GalilVM),
      (∃ k, StepsAll (galilFrameS P qq first) delay (SoundScanNR raw) k ⟨c0, r⟩ ⟨cT, sT⟩) ∧
      MInv raw cT sT ∧ (∃ (Rad' : ℕ) (last' : Counter), Restarted raw sT Rad' last') ∧
      SpanRep sT ∧ cT.mode = Mode.scan ∧ cT.replaying = false ∧ cT.clock = delay := by
  obtain ⟨a, ls, rs, q, gap, es0, cF, sF, vq, ch, oF, es, c2, s2, cM, sM, h, w, vs, vq', s2',
    t', v, cycle, o, org, lower, span, m, c', s', n, c3, s3, w3, vs3, vq3, o3, cen3, r3, w3', entry,
    hP, hP', hex, hraw, hout0, hseg0, hmF, hrF, hcF, havF, hidle, hCen, hq, hfound, hmt, hch, hchne,
    hoF, hprepSeg, hseg, hm1, hr1, hc1, hs1, hz, hav, hcmp, hmis, hq', hg, hb, hs2', hi2, hchain,
    ho, hint, he, hoc, hdp, hpc, hposout, hlow, hrounds, hseg3, hm3, hr3, hc3, hs3, hav3, hcmp3,
    hmt3, hq3, ho3, hinv3, hbroken, hmargin, hlast, hlag, hrestart, Rad', hRnext⟩ := hC
  obtain ⟨k, hk⟩ := cycle_found_stepsAll raw P hP hP' qq first delay hR hout0 hseg0 hmF hrF hcF havF
      hidle vq hq hfound hmt ch hch hchne oF hoF hprepSeg hseg h hm1 hr1 hc1 w hs1 hz hav vs vq'
      hcmp hmis hq' hg s2' hb hs2' hi2 hchain o ho org hint he hrounds hseg3 hm3 hr3 hc3 w3 hs3 hav3
      vs3 vq3 hcmp3 hmt3 hq3 o3 ho3 hinv3 w3' hbroken hmargin hlast hlag entry hrestart
  refine ⟨foundLandingControl c3 delay o3, foundLandingVM (afterCompare s3 vs3 vq3) w3' entry,
    ⟨k, hk⟩,
    cycle_found_minv raw P hex qq first delay a ls rs q gap hraw hR hM0 hseg0 hmF hrF hcF havF
      hidle hCen vq hq hfound hmt ch hch hchne oF hoF hprepSeg hseg h hm1 hr1 hc1 w hs1 hz hav vs
      vq' hcmp hmis hq' hg s2' hb hs2' hi2 hchain o ho org hint he hoc hdp hpc hposout hlow hrounds
      hseg3 hm3 hr3 hc3 w3 hs3 hav3 vs3 vq3 hcmp3 hmt3 hq3 o3 ho3 w3' hbroken entry,
    ⟨Rad', _, hRnext⟩,
    spanRep_found_shift P qq first delay hseg0 vq ch oF hprepSeg hseg h w s2' t' v cycle hchain
      hrounds hseg3 vs3 vq3 w3' entry hS0,
    hm3, rfl, rfl⟩

/-! ### Found routes carrying the span relation -/

/-- `FoundRouteL` whose landing routes also carry `SpanRep`. -/
inductive FoundRouteLP (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (c : Control) (r : GalilVM) : Prop
  | report (h : LocalReport P q first raw c r)
  | shift (cT : Control) (sT : GalilVM)
      (hst : ∃ k, StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
      (hM : MInv raw cT sT) (hR : ∃ (Rad : ℕ) (last : Counter), Restarted raw sT Rad last)
      (hres : FoundResidual raw cT sT) (hS : SpanRep sT)
      (hprog : position r.center < position sT.center)
  | noShift (cT : Control) (sT : GalilVM)
      (hst : ∃ k, StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
      (hM : MInv raw cT sT) (hR : ∃ (Rad : ℕ) (last : Counter), Restarted raw sT Rad last)
      (hres : FoundResidual raw cT sT) (hS : SpanRep sT)
      (hprog : position r.center < position sT.center)

theorem FoundRouteLP.toRouteL {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {c : Control} {r : GalilVM} (h : FoundRouteLP P q first raw c r) :
    FoundRouteL P q first raw c r := by
  cases h with
  | report h => exact .report h
  | shift cT sT hst hM hR hres _ hprog => exact .shift cT sT hst hM hR hres hprog
  | noShift cT sT hst hM hR hres _ hprog => exact .noShift cT sT hst hM hR hres hprog

/-- A found landing with `SpanRep` carries `InvLP`. -/
theorem invLP_of_foundLanding {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {k : ℕ}
    {x : State GalilVM} {cT : Control} {sT : GalilVM}
    (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k x ⟨cT, sT⟩)
    (hM : MInv raw cT sT) (hR : ∃ (Rad : ℕ) (last : Counter), Restarted raw sT Rad last)
    (hres : FoundResidual raw cT sT) (hS : SpanRep sT) : InvLP raw cT sT :=
  invLP_of_landed hst (inv_of_residual hM hR hres) hS

/-- Every non-report found route re-enters the recursion at an `InvLP` state. -/
theorem invLP_of_foundRouteLP {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {c : Control} {r : GalilVM} (h : FoundRouteLP P q first raw c r) :
    LocalReport P q first raw c r ∨
      ∃ (cT : Control) (sT : GalilVM) (k : ℕ),
        StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ ∧
        InvLP raw cT sT ∧ position r.center < position sT.center := by
  cases h with
  | report h => exact Or.inl h
  | shift cT sT hst hM hR hres hS hprog =>
    obtain ⟨k, hst⟩ := hst
    exact Or.inr ⟨cT, sT, k, hst, invLP_of_foundLanding hst hM hR hres hS, hprog⟩
  | noShift cT sT hst hM hR hres hS hprog =>
    obtain ⟨k, hst⟩ := hst
    exact Or.inr ⟨cT, sT, k, hst, invLP_of_foundLanding hst hM hR hres hS, hprog⟩

#print axioms spanRep_found_noshift
#print axioms spanRep_found_shift
#print axioms foundCycle_step_span
#print axioms FoundRouteLP.toRouteL
#print axioms invLP_of_foundLanding
#print axioms invLP_of_foundRouteLP

end PalPeg.GalilInvPlus
