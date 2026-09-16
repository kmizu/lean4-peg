import PalPeg.GalilOracleMC2

/-!
# Instantiating the leaves of `GalilOracleMC2.h_oracle_of_leaves`

`PalPeg.GalilOracleMC2.h_oracle_of_leaves` derives `H_oracle` from thirteen
named leaves.  This module discharges the ones the development already proves
and republishes the theorem with the **minimal residual set**
(`h_oracle_of_leaves'`).

## Closed here

* `hex`  — `rfl` on `PofC` (`sharedC`'s `replayExhausted` is literally
  `fun s => zero s.replay`).
* `hsearch` — `GalilBranchInvariants2.searchEffect_exists`.
* `hlive` (the `CentreLive` obligation of the segment construction) —
  `GalilCentreLive.centreLive_of_invLP_run` fed by
  `GalilInvPlus2.hfloor_of_invLP2`, which is unconditional on `InvLP2`.  This is
  what lets the segment be built from an `InvLPC` entry with no liveness leaf.
* `hsegmentM` — `segment_of_invLPC` below, `GalilInvPlus.segment_of_invLP`
  re-run at a *single* `InvLPC` entry state (the `∀`-quantified `hlive` of
  `segment_of_invLP` cannot be discharged, because `InvLP` alone carries no
  copy pack; at one `InvLPC` state it can).  What is left of it is the fuel
  bound `hends`, which is strictly more elementary.

## Residual

See `h_oracle_of_leaves'`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.GalilOracleLeaves2

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilCheckpoints PalPeg.GalilTraceCost PalPeg.GalilLexMeasure
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleMC
open PalPeg.GalilGlueBLeaves PalPeg.GalilBranchInvariants2 PalPeg.GalilSegmentConstruct
open PalPeg.GalilOracleM PalPeg.GalilOracleMC2 PalPeg.GalilFinalAssembly2

/-! ## 1. `hex` -/

/-- **`hex`, closed.**  `sharedC`'s replay-exhaustion test *is* `zero ·.replay`. -/
theorem hex_C (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry : ℕ) (w : List (Fin 2)) (s : GalilVM) :
    (PofC centre place entry w).replayExhausted s = zero s.replay := rfl

/-! ## 2. `hsearch` -/

/-- **`hsearch`, closed.**  `searchEffect_exists`. -/
theorem hsearch_C (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry : ℕ) (w : List (Fin 2)) (s : GalilVM) (h : SearchReady (searchLens.get s)) (a : Bool) :
    ∃ v, searchEffect (PofC centre place entry w) a s v :=
  searchEffect_exists (PofC centre place entry w) a s h

/-! ## 3. `CentreLive` out of an `InvLPC` state -/

/-- **The liveness obligation, closed at an `InvLPC` entry.**  `hfloor` is
unconditional on `InvLP2` (`GalilInvPlus2.hfloor_of_invLP2`), so
`GalilCentreLive.centreLive_of_invLP_run` needs nothing else. -/
theorem hlive_of_invLPC (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    {raw : List (Fin 2)} {c : Control} {r : GalilVM} (hI : InvLPC raw c r) :
    ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry raw) q first) 2048 m ⟨c, r⟩ z →
      CentreLive z.ctl z.vm :=
  PalPeg.GalilCentreLive.centreLive_of_invLP_run centre place entry q first
    ⟨hI.1.1.1, hI.1.1.2⟩ (hfloor_of_invLP2 centre place entry q first hI.1)


/-! ## 4. The segment from an `InvLPC` entry -/

/-- **`GalilInvPlus.segment_of_invLP` at a single `InvLPC` entry.**  Same body,
with the `∀`-quantified `hlive` replaced by `hlive_of_invLPC` at this state.
Only the fuel bound `hends` survives. -/
theorem segment_of_invLPC (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry raw) a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) →
      searchEffect (PofC centre place entry raw) a s v → SearchReady v)
    (c : Control) (r : GalilVM) (hIC : InvLPC raw c r)
    (hends : ∃ n : ℕ, ∀ (es : List Bool) (c' : Control) (t : GalilVM),
      WatchSegE (PofC centre place entry raw) q first 2048 es c r c' t →
      es.length = n → SegEnd (PofC centre place entry raw) c' t) :
    ∃ (c' : Control) (t : GalilVM),
      SegReachedW centre place entry q first raw c r c' t ∧
      SegEnd (PofC centre place entry raw) c' t := by
  have hIP : InvLP raw c r := hIC.1.1
  have hI : InvS raw c r := hIP.1.1
  obtain ⟨hm, hclk, hidle, hsr, hM, R, hi, hfr, hrr, hsi⟩ :
      c.mode = Mode.scan ∧ 1 ≤ c.clock ∧ r.chain = ChainVM.idle ∧
      SearchReady (searchLens.get r) ∧ MInv raw c r ∧
      ∃ R : ℕ, ScanInvariant raw (position r.center) R r.left r.right ∧ Frontier r ∧
        ReplayRest c r ∧ ShiftIdle r := by
    rcases hI with h | ⟨k, h⟩
    · obtain ⟨Rad, last, hR⟩ := h.rest
      exact ⟨h.mode.1, by rw [h.mode.2.2]; omega, hR.1, h.search, h.minv, Rad,
        hR.2.2.2.1, h.frontier, h.rest_replay, h.shiftIdle⟩
    · exact ⟨h.mode.1, by rw [h.mode.2.2]; omega, h.chainIdle, h.search, h.minv, k,
        h.scan, h.frontier, h.rest_replay, h.shiftIdle⟩
  obtain ⟨n, hn⟩ := hends
  obtain ⟨es, c', t, r', hseg, hm', hclk', hidle', hsrt, hMt, hit, hlen⟩ :=
    watchSegE_construct raw (PofC centre place entry raw) hex q first 2048 (by norm_num)
      hsearch hpres n c r R hm hclk hidle hsr hM hi
  have hEnd : SegEnd (PofC centre place entry raw) c' t := by
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
    frontier_replayRest_of_scan (onLetterVM raw) leftFirstVM centre place
      entry q first 2048 hsteps hm (hlive_of_invLPC centre place entry q first hIC) hfr hrr
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


/-! ## 5. `H_oracle` from the residual leaves -/

/-- **`GalilOracleMC2.h_oracle_of_leaves` with `hex`, `hsearch` and `hsegmentM`
discharged.**  `hsegmentM` is replaced by the strictly weaker fuel bound
`hends`: at an `InvLPC` state some segment length forces one of the five
`SegEnd` exits.  Everything else is verbatim.

The residual leaves, and why each is still open:

* `hpres` — `SearchReady` is *not* preserved by a bare `searchEffect`:
  `GalilSearchReadyInv.searchReady_step` needs the stage budget `ReadyRem` and
  the `.run` entry clause `RunEntry`, neither of which `SearchReady` alone
  carries.
* `hquiet` — nothing in the development proves that a ready search never
  reports `found`; it is assumed everywhere it is used.
* `houtReplay` — `GalilReplaySegment.InvScan` records no output, while
  `SoundScanNR` unfolds to `OutputRel` (`output = true → the prefix is a
  palindrome`).
* `hends` — the fuel bound above.
* `hended`, `hlastMatch`, `hlastMismatch` — the three report exits, at the
  costed strength `ReachAtC2` (`GalilOracleLocal.report_of_last_consume_local`
  and `report_after_replay_of_halted_local` give the *uncosted* `LocalReport`).
* `hmismatch` — the costed fallback route (`GalilGlueBLeaves`'s
  `fallbackRoute_of_mismatch'` gives `FallbackRoute`, not `FallbackRouteMC2`).
* `hfound`, `hfoundBg` — the costed found routes; the `broke` constructor is
  `GalilOracleMC2.foundRouteMC_noshift_dC`, whose DP/copy/back inputs have to be
  extracted from the found tick, and whose `hcont` is still open.
* `hstr` — `CycleOracleMC` quantifies over every `InvL` state, boot-reachable or
  not, so the copy pack and the centre head cannot be recovered there.  (The
  boot-side route that avoids it is `GalilOracleMC2.checkpoints_cost2`.) -/
theorem h_oracle_of_leaves' (entry q : ℕ) (first : Fin 9)
    (hpres : ∀ (w : List (Fin 2)) (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) →
      searchEffect (PofC centreC placeC entry w) a s v → SearchReady v)
    (hquiet : ∀ w : List (Fin 2),
      PalPeg.GalilReplaySegment.SearchQuiet (PofC centreC placeC entry w))
    (houtReplay : ∀ (w : List (Fin 2)) (c' : Control) (t' : GalilVM) (k : ℕ),
      PalPeg.GalilReplaySegment.InvScan 2048 w c' t' k → SoundScanNR w ⟨c', t'⟩)
    (hends : ∀ (w : List (Fin 2)) (c : Control) (r : GalilVM), InvLPC w c r →
      ∃ n : ℕ, ∀ (es : List Bool) (c' : Control) (t : GalilVM),
        WatchSegE (PofC centreC placeC entry w) q first 2048 es c r c' t →
        es.length = n → SegEnd (PofC centreC placeC entry w) c' t)
    (hended : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t → ¬ canRight t.right →
      ReachAtC2 (PofC centreC placeC entry w) q first w m c r)
    (hlastMatch : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control)
      (t : GalilVM), 1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t →
      c'.clock = 1 → canRight t.right → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      read (left t.left) = read (right t.right) →
      ReachAtC2 (PofC centreC placeC entry w) q first w m c r)
    (hlastMismatch : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control)
      (t : GalilVM), 1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t →
      c'.clock = 1 → canRight t.right → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      read (left t.left) ≠ read (right t.right) →
      ReachAtC2 (PofC centreC placeC entry w) q first w m c r)
    (hmismatch : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control)
      (t : GalilVM), 1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t →
      c'.replaying = false → c'.clock = 1 → canRight t.right →
      read (left t.left) ≠ read (right t.right) →
      FallbackRouteMC2 (PofC centreC placeC entry w) q first w m c r c' t)
    (hfound : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control)
      (t : GalilVM), 1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t →
      c'.clock = 1 → canRight t.right →
      read (left t.left) = read (right t.right) →
      (∃ vq, searchEffect (PofC centreC placeC entry w) true t vq ∧ vq.search.mode = .found) →
      FoundRouteMC2 (PofC centreC placeC entry w) q first w m c r c' t)
    (hfoundBg : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control)
      (t : GalilVM), 1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t → 1 ≤ c'.clock →
      (∃ vq, searchEffect (PofC centreC placeC entry w) false t vq ∧ vq.search.mode = .found) →
      FoundRouteMC2 (PofC centreC placeC entry w) q first w m c r c r)
    (hstr : ∀ (w : List (Fin 2)) (c : Control) (r : GalilVM), InvL w c r → InvLPC w c r) :
    PalPeg.GalilFinalAssembly.H_oracle centreC placeC entry q first :=
  h_oracle_of_leaves entry q first
    (fun w s => hex_C centreC placeC entry w s)
    (fun w s hs a => hsearch_C centreC placeC entry w s hs a)
    hpres hquiet houtReplay
    (fun w m c r _ _ hIC _ => by
      obtain ⟨c', t, hsW, hEnd⟩ :=
        segment_of_invLPC centreC placeC entry q first w (fun s => hex_C centreC placeC entry w s)
          (fun s hs a => hsearch_C centreC placeC entry w s hs a) (hpres w) c r hIC
          (hends w c r hIC)
      exact ⟨c', t, hsW, Or.inr hEnd⟩)
    hended hlastMatch hlastMismatch hmismatch hfound hfoundBg hstr

#print axioms hex_C
#print axioms hsearch_C
#print axioms hlive_of_invLPC
#print axioms segment_of_invLPC
#print axioms h_oracle_of_leaves'

end PalPeg.GalilOracleLeaves2
