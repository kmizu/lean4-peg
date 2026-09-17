import PalPeg.GalilReplaySegment
import PalPeg.GalilFoundStage

/-!
# `ReplayStage` at the replay landing — the `hsc` re-cut, first step

`H_stageScan` (`CloseoutOracleI2:173`) asks for `ReplayStage` at **every** state
satisfying `InvScan`.  That is false: `InvScan` (`GalilReplaySegment:317`) has
eleven fields and none of them mentions `s.radius`, while `ReplayStage`'s
`Restarted` demands `RadiusRep r.radius Rad`, i.e. `Canonical r.radius`; since
`Counter = ⟨pos neg : List Unit⟩`, replacing only `radius := ⟨[()],[()]⟩` (a
legal non-canonical counter of value `0`) in any `InvScan` inhabitant keeps all
eleven fields and breaks `ReplayStage`.

The repair is the standard re-cut `InvScanS := InvScan ∧ ReplayStage` — the same
move as `InvScan → InvScanO` and `SearchReady → SearchReadyB`.  The producer
already has the data: `replay_after_fallback` returns the `WatchSegE` alongside
`InvScan`, and its own hypotheses carry `Restarted raw t 0 reset` and
`c.clock = delay`; the docstring at `GalilReplaySegment:310` records that the
`stage` field was dropped.  This file picks it back up.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.CloseoutStageScan1

open PalPeg.GalilReplaySegment PalPeg.GalilFoundStage
open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilTickFun2 PalPeg.GalilBranchInvariants2
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead

/-- **`ReplayStage` from a fallback replay segment.**  Everything is already in
hand at the call site: the restart `Restarted raw t 0 reset`, its stage bound
`stageEntry_zero`, the full clock, and the segment itself. -/
theorem replayStage_of_seg {raw : List (Fin 2)} {P : Shared} {q : ℕ} {first : Fin 9}
    {es : List Bool} {c c' : Control} {t t' : GalilVM}
    (hR : Restarted raw t 0 reset) (hc : c.clock = 2048)
    (hseg : WatchSegE P q first 2048 es c t c' t') :
    ReplayStage raw P q first c' t' :=
  ⟨t, 0, reset, es, c, hR, stageEntry_zero reset, hc, hseg⟩

/-- **The landing of `replay_after_fallback` carries `ReplayStage`.**  Same
hypotheses as `replay_after_fallback` at `delay = 2048`; the conclusion adds the
stage field that theorem drops. -/
theorem replayStage_of_replay_after_fallback (raw : List (Fin 2)) (P : Shared) (q : ℕ)
    (first : Fin 9)
    (hex : ∀ s, P.replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) → ∀ a : Bool,
      ∃ v, searchEffect P a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) → searchEffect P a s v → SearchReady v)
    (hquiet : SearchQuiet P)
    (r : ℕ) (hr0 : 0 < r) (c : Control) (t : GalilVM)
    (hm : c.mode = Mode.scan) (hc : c.clock = 2048) (hrpl : c.replaying = true)
    (hR : Restarted raw t 0 reset) (hrep : t.replay = ofNat r)
    (hM : MInv raw c t) (hfr : Frontier t) (hsi : ShiftIdle t) :
    ∃ (es : List Bool) (c' : Control) (t' : GalilVM),
      WatchSegE P q first 2048 es c t c' t' ∧
      (SoundScanNR raw ⟨c', t'⟩ →
        StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) es.length ⟨c, t⟩ ⟨c', t'⟩) ∧
      es.length = r * 2048 ∧ es.count true = r ∧
      position t'.right = position t.right + r ∧ t'.center = t.center ∧
      InvScan 2048 raw c' t' r ∧
      ReplayStage raw P q first c' t' := by
  obtain ⟨es, c', t', hseg, hst, hlen, hcnt, hpos, hcen, hinv⟩ :=
    replay_after_fallback raw P q first 2048 hex (by omega) hsearch hpres hquiet r hr0 c t
      hm hc hrpl hR hrep hM hfr hsi
  exact ⟨es, c', t', hseg, hst, hlen, hcnt, hpos, hcen, hinv,
    replayStage_of_seg hR hc hseg⟩

#print axioms replayStage_of_seg
#print axioms replayStage_of_replay_after_fallback

end PalPeg.CloseoutStageScan1
