import PalPeg.CloseoutOracle5
import PalPeg.CloseoutPreload41

/-!
# `CloseoutOracle6`: the fallback replay off the refuted universal leaf

`CloseoutOracle5.cycleOracleMC2C_of_piecesP` still carried the universal

```
hpresRep : ∀ s a v, SearchReady (searchLens.get s) → searchEffect P a s v → SearchReady v
```

which `GalilLeafPres.hpres_false_at` refutes.  It was consumed at exactly one
place: the fallback replay, through `GalilOracleMC3.cycleOutMC2C_of_fallback'`
→ `invScanO_of_replay_generalR` → `GalilFoundStage.replay_after_fallback_general'''`
→ `GalilReplaySpan.replay_construct3`.

`GalilReplaySpan.HpresRun` (added there) is the same law restricted to the
states of an actual `SoundScanNR` run out of a given state, under the clock
guard the comparison branch really has; it is closed under taking successors
of the run, which is all the three inductions of the construction need.  The
`RP` chain of `GalilReplaySpan` restates the construction over it, this file
restates the four assembly layers above it, and `CloseoutPreload41.HpresRepAt`
— the readiness field along an oracle-shaped run — is exactly `HpresRun` at the
cycle entry, so the refuted leaf disappears from the oracle entirely.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutOracle6

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilCheckpoints PalPeg.GalilTraceCost PalPeg.GalilLexMeasure
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleMC
open PalPeg.GalilGlueBLeaves PalPeg.GalilBranchInvariants2 PalPeg.GalilSegmentConstruct
open PalPeg.GalilOracleM PalPeg.GalilOracleMC2 PalPeg.GalilFinalAssembly2
open PalPeg.GalilLeafOutReplay PalPeg.GalilOracleLeaves2 PalPeg.GalilOracleMC3
open PalPeg.GalilLeafPres PalPeg.GalilLeafEnds PalPeg.GalilSegmentConstructB
open PalPeg.CloseoutOracle5 PalPeg.CloseoutPreload40 PalPeg.CloseoutPreload41
open PalPeg.GalilFoundStage PalPeg.GalilReplaySpan

/-! ## 1. `replay_after_fallback_general'''` over `HpresRun` -/

/-- `GalilFoundStage.replay_after_fallback_general'''` with the universal `hpres`
replaced by `GalilReplaySpan.HpresRun` at the replay entry. -/
theorem replay_after_fallback_general'''RP (raw : List (Fin 2)) (P : Shared)
    (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9)
    (delay : ℕ) (hex : ∀ s, P.replayExhausted s = zero s.replay) (hd : 1 ≤ delay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) → ∀ a : Bool,
      ∃ v, searchEffect P a s v)
    (hshape : GalilWatchOkInst.StartShape P)
    (hbudget : PalPeg.GalilFoundStage.ReplayBudgetR raw P q first delay)
    (hinv : PalPeg.GalilFoundStage.ReplayStageInv raw P q first)
    (hrs : PalPeg.GalilReplaySpan.RestartShape P)
    (r : ℕ) (hr0 : 0 < r) (c : Control) (t : GalilVM)
    (hm : c.mode = Mode.scan) (hc : c.clock = delay) (hrpl : c.replaying = true)
    (hR : Restarted raw t 0 reset) (hrep : t.replay = ofNat r)
    (hM : MInv raw c t) (hfr : Frontier t) (hsi : ShiftIdle t)
    (hpresR : PalPeg.GalilReplaySpan.HpresRun raw P q first delay ⟨c, t⟩) :
    (∃ (es : List Bool) (c' : Control) (t' : GalilVM),
      WatchSegE P q first delay es c t c' t' ∧
      (SoundScanNR raw ⟨c', t'⟩ →
        StepsAll (galilFrameS P q first) delay (SoundScanNR raw) es.length ⟨c, t⟩ ⟨c', t'⟩) ∧
      es.length = r * delay ∧ es.count true = r ∧
      position t'.right = position t.right + r ∧ t'.center = t.center ∧
      PalPeg.GalilReplaySegment.InvScan delay raw c' t' r) ∨
    PalPeg.GalilReplaySpan.ChainEnd raw P q first delay (position t.right + r) c t 0 r ∨
    (PalPeg.GalilReplaySpan.BrokeAndRestarted raw P q first delay c t ∧
      ∃ (n : ℕ) (c' : Control) (t' : GalilVM),
        (SoundScanNR raw ⟨c', t'⟩ →
          StepsAll (galilFrameS P q first) delay (SoundScanNR raw) n ⟨c, t⟩ ⟨c', t'⟩) ∧
        position t'.right = position t.right + r ∧ t'.center = t.center ∧
        PalPeg.GalilReplaySegment.InvScan delay raw c' t' r) :=
  PalPeg.GalilReplaySpan.replay_after_fallback_general''RP raw P hP hP' q first delay hex hd
    hsearch hshape (PalPeg.GalilFoundStage.replayBudget_of_R hbudget hinv) hrs r hr0 c t hm hc hrpl
    hR hrep hM hfr hsi hpresR

#print axioms replay_after_fallback_general'''RP

/-! ## 2. The quiet branch over `HpresRun` -/

theorem invScanO_of_replay_generalR' (raw : List (Fin 2)) (P : Shared)
    (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9)
    (delay : ℕ) (hex : ∀ s, P.replayExhausted s = zero s.replay) (hd : 1 ≤ delay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) → ∀ a : Bool,
      ∃ v, searchEffect P a s v)
    (hshape : PalPeg.GalilWatchOkInst.StartShape P)
    (hbudget : PalPeg.GalilFoundStage.ReplayBudgetR raw P q first delay)
    (hinv : PalPeg.GalilFoundStage.ReplayStageInv raw P q first)
    (hrs : PalPeg.GalilReplaySpan.RestartShape P)
    (r : ℕ) (hr0 : 0 < r) (c : Control) (t : GalilVM)
    (hm : c.mode = Mode.scan) (hc : c.clock = delay) (hrpl : c.replaying = true)
    (hR : Restarted raw t 0 reset) (hrep : t.replay = ofNat r)
    (hM : MInv raw c t) (hfr : Frontier t) (hsi : ShiftIdle t)
    (hpresR : PalPeg.GalilReplaySpan.HpresRun raw P q first delay ⟨c, t⟩) :
    (∃ (es : List Bool) (c' : Control) (t' : GalilVM),
      WatchSegE P q first delay es c t c' t' ∧
      StepsAll (galilFrameS P q first) delay (SoundScanNR raw) es.length ⟨c, t⟩ ⟨c', t'⟩ ∧
      es.length = r * delay ∧ es.count true = r ∧
      position t'.right = position t.right + r ∧ t'.center = t.center ∧
      InvScanO delay raw c' t' r) ∨
    PalPeg.GalilReplaySpan.ChainEnd raw P q first delay (position t.right + r) c t 0 r ∨
    (PalPeg.GalilReplaySpan.BrokeAndRestarted raw P q first delay c t ∧
      ∃ (n : ℕ) (c' : Control) (t' : GalilVM),
        (SoundScanNR raw ⟨c', t'⟩ →
          StepsAll (galilFrameS P q first) delay (SoundScanNR raw) n ⟨c, t⟩ ⟨c', t'⟩) ∧
        position t'.right = position t.right + r ∧ t'.center = t.center ∧
        PalPeg.GalilReplaySegment.InvScan delay raw c' t' r) := by
  rcases replay_after_fallback_general'''RP raw P hP hP' q first delay hex hd
      hsearch hshape hbudget hinv hrs r hr0 c t hm hc hrpl hR hrep hM hfr hsi hpresR with
    ⟨es, c', t', hseg, hst, hlen, hcnt, hpos, hC, hIS⟩ | hEnd | hBr
  · have hout : OutputRel raw c' t' :=
      watchSegE_outputM raw P hP hP' q first delay hseg (position t.center) 0
        (by simpa using hR.2.2.2.1) (Or.inr (by rw [hcnt]; exact hr0))
    exact Or.inl ⟨es, c', t', hseg, hst (fun _ _ => hout), hlen, hcnt, hpos, hC, ⟨hIS, hout⟩⟩
  · exact Or.inr (Or.inl hEnd)
  · exact Or.inr (Or.inr hBr)


#print axioms invScanO_of_replay_generalR'

/-! ## 3. The fallback piece over `HpresRun` -/

/-- `GalilOracleMC3.cycleOutMC2C_of_fallback'` over `HpresRun` at the cycle entry. -/
theorem cycleOutMC2C_of_fallback'R (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ raw.length)
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry raw) a s v)
    (hshape : PalPeg.GalilWatchOkInst.StartShape (PofC centre place entry raw))
    (hbudget : PalPeg.GalilFoundStage.ReplayBudgetR raw (PofC centre place entry raw) q first 2048)
    (hstage : PalPeg.GalilFoundStage.ReplayStageInv raw (PofC centre place entry raw) q first)
    (hrs : PalPeg.GalilReplaySpan.RestartShape (PofC centre place entry raw))
    (hfoundReplay : ∀ (c : Control) (r : GalilVM) (cT : Control) (sT : GalilVM) (R k : ℕ),
      1 ≤ m → m ≤ raw.length → InvLPC raw c r →
      StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundScanNR raw) k
        ⟨c, r⟩ ⟨cT, sT⟩ →
      ReplayLanding raw cT sT R → SpanRep sT →
      position r.center < position sT.center → position sT.right ≤ 2 * m - 1 →
      (PalPeg.GalilReplaySpan.ChainEnd raw (PofC centre place entry raw) q first 2048
          (position sT.right + R) cT sT 0 R ∨
        PalPeg.GalilReplaySpan.BrokeAndRestarted raw (PofC centre place entry raw) q first 2048
          cT sT) →
      FoundInReplayRouteMC2 (PofC centre place entry raw) q first raw m c r)
    {c c' : Control} {r t : GalilVM} {es : List Bool}
    (hpresR : PalPeg.GalilReplaySpan.HpresRun raw (PofC centre place entry raw) q first 2048 ⟨c, r⟩)
    (hIC : InvLPC raw c r)
    (hw : WatchSegE (PofC centre place entry raw) q first 2048 es c r c' t)
    (hcen : t.center = r.center) (hc1 : c'.clock = 1) (hav : canRight t.right)
    (h : FallbackRouteMC2 (PofC centre place entry raw) q first raw m c r c' t) :
    CycleOutMC2C (PofC centre place entry raw) q first raw m c r := by
  have hI : InvL raw c r := invLPC_invL hIC
  obtain ⟨⟨R0, hi0⟩, hc0, -⟩ := invL_entry hI
  have hrun0 := seg_run centre place entry q first raw hI hw
  cases h with
  | report h => exact Or.inl h
  | landed fb cT sT hst hD hland hCR hIT hSpan hprog hpos =>
      obtain ⟨Rad, ℓ, a, xs, rs', q', a₀, ls₀, rs₀, q₀, gap₀, lower, span, y, hi, hRR, hSt, hv, hkC,
        hdec, hraw, hraw₀, hC₀, hspan, hres, hidle, hlow, hR, hfb⟩ := hD
      obtain ⟨L, w, hw', e, hcr, -, -, -, -, -, hr'⟩ :=
        GalilCostedFallback.costedRun_fallback_zero raw (PofC centre place entry raw) q first hw hi0
          hc0 hc1 (t := sT) hi hav hRR hSt ℓ hv hkC a xs rs' q' hdec hraw a₀ ls₀ rs₀ q₀ gap₀ hraw₀
          hC₀ hspan hres hidle hlow fb hR hfb hland hCR
      have hall := stepsAll_trans hrun0 hst
      rw [show es.length + (1 + fb) = es.length + 1 + fb by omega] at hall
      exact cycleOutMC2C_of_centre hIC hall hcr
        (invLPC_of_landed centre place entry q first hIC.1.2 hall hIT hSpan)
        (by rw [← hcen]; exact hprog) (by rw [hr']; exact hpos)
  | replaying fb R cT sT hst hD hL hSpan hland hCR hprog hpos =>
      have hall0 := stepsAll_trans hrun0 hst
      rw [show es.length + (1 + fb) = es.length + 1 + fb by omega] at hall0
      have hprogR : position r.center < position sT.center := by rw [← hcen]; exact hprog
      have hposR : position sT.right ≤ 2 * m - 1 := by
        have h1 : position sT.right = position sT.center := by rw [hCR]
        have h2 : position sT.center = position (right t.right) - R := hland
        omega
      rcases invScanO_of_replay_generalR' raw (PofC centre place entry raw) rfl rfl q first 2048
          hex (by norm_num) hsearch hshape hbudget hstage hrs R hL.pos cT sT hL.mode hL.clock
          hL.replaying hL.rest hL.replay hL.minv hL.frontier hL.shiftIdle
          (PalPeg.GalilReplaySpan.hpresRun_mono hpresR hall0) with
        ⟨esR, c'', t'', hseg, hstR, hlen, hcnt, hrr, hcc, hO⟩ | hEnd | ⟨hBr, -⟩
      · obtain ⟨Rad, ℓ, a, xs, rs', q', a₀, ls₀, rs₀, q₀, gap₀, lower, span, y, hi, hRR, hSt, hv,
          hkC, hdec, hraw, hraw₀, hC₀, hspan, hres, hidle, hlow, hR, hfb⟩ := hD
        obtain ⟨L, w, hw', e, hcr, -, -, -, -, -, hr'⟩ :=
          GalilCostedFallback.costedRun_fallback_replay raw (PofC centre place entry raw) q first hw
            hi0 hc0 hc1 (t := sT) (t' := t'') hi hav hRR hSt ℓ hv hkC a xs rs' q' hdec hraw a₀ ls₀
            rs₀ q₀ gap₀ hraw₀ hC₀ hspan hres hidle hlow fb esR R hR hfb hlen hland hCR hrr hcc
        have hall := stepsAll_trans hall0 hstR
        rw [show es.length + 1 + fb + esR.length = es.length + 1 + fb + esR.length from rfl] at hall
        have hRRt : RadiusRep t''.radius R := by
          have h0 := radiusRep_watchSegE _ q first 2048 hseg hL.rest.2.2.2.2.1
          rw [hcnt, Nat.zero_add] at h0
          exact h0
        have hE : EntryCounters raw t'' :=
          entryCounters_of_invScan hO.1 hRRt (spanRep_watchSegE _ q first 2048 hseg hSpan)
            (canonical_length_watchSegE _ q first 2048 hseg hL.rest.2.2.2.2.2.1)
        have hIL : InvLP raw c'' t'' := ⟨invL_of_run hall (Or.inr ⟨R, hO.1⟩), hE⟩
        exact cycleOutMC2C_of_centre hIC hall hcr
          ⟨invLP2_of_stepsAll centre place entry q first hIC.1.2 hall hIL,
            (invScanC_of_restart hL.rest hcc hO.1).2⟩
          (by rw [hcc]; exact hprogR) (by rw [hr']; exact hpos)
      · exact cycleOutMC2C_of_foundInReplay centre place entry q first raw m hIC
          (hfoundReplay c r cT sT R _ hm1 hmle hIC hall0 hL hSpan hprogR hposR (Or.inl hEnd))
      · exact cycleOutMC2C_of_foundInReplay centre place entry q first raw m hIC
          (hfoundReplay c r cT sT R _ hm1 hmle hIC hall0 hL hSpan hprogR hposR (Or.inr hBr))


#print axioms cycleOutMC2C_of_fallback'R

/-! ## 4. The cycle oracle with the replay leaf reachability-restricted -/

theorem cycleOracleMC2C_of_piecesP' (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry raw) a s v)
    (hpresRepAt : ∀ (c : Control) (r : GalilVM), InvLPC raw c r →
      PalPeg.CloseoutPreload41.HpresRepAt centre place entry q first raw ⟨c, r⟩)
    (hpresT : ∀ (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM), InvLPC raw c r →
      SegReachedW centre place entry q first raw c r c' t → c'.clock = 1 →
      PalPeg.CloseoutPreload40.HpresAt (PofC centre place entry raw) c' t)
    (hshape : PalPeg.GalilWatchOkInst.StartShape (PofC centre place entry raw))
    (hbudget : PalPeg.GalilFoundStage.ReplayBudgetR raw (PofC centre place entry raw) q first 2048)
    (hstage : PalPeg.GalilFoundStage.ReplayStageInv raw (PofC centre place entry raw) q first)
    (hrs : PalPeg.GalilReplaySpan.RestartShape (PofC centre place entry raw))
    (hsegmentM : ∀ (m : ℕ) (c : Control) (r : GalilVM), 1 ≤ m → m ≤ raw.length →
      InvLPC raw c r → position r.right ≤ 2 * m - 1 →
      ∃ (c' : Control) (t : GalilVM),
        SegReachedW centre place entry q first raw c r c' t ∧
        (AtTarget m c' t ∨ SegEnd (PofC centre place entry raw) c' t))
    (hended : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPC raw c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t → ¬ canRight t.right →
      ReachAtC2 (PofC centre place entry raw) q first raw m c r)
    (hlastMatch : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPC raw c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t →
      c'.clock = 1 → canRight t.right → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      read (left t.left) = read (right t.right) →
      ReachAtC2 (PofC centre place entry raw) q first raw m c r)
    (hlastMismatch : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPC raw c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t →
      c'.clock = 1 → canRight t.right → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      read (left t.left) ≠ read (right t.right) →
      ReachAtC2 (PofC centre place entry raw) q first raw m c r)
    (hmismatch : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPC raw c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t →
      c'.replaying = false → c'.clock = 1 → canRight t.right →
      read (left t.left) ≠ read (right t.right) →
      FallbackRouteMC2 (PofC centre place entry raw) q first raw m c r c' t)
    (hfound : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPC raw c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t →
      c'.clock = 1 → canRight t.right →
      read (left t.left) = read (right t.right) →
      (∃ vq, searchEffect (PofC centre place entry raw) true t vq ∧ vq.search.mode = .found) →
      FoundRouteMC2 (PofC centre place entry raw) q first raw m c r c' t)
    (hfoundBg : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPC raw c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t → 1 ≤ c'.clock →
      (∃ vq, searchEffect (PofC centre place entry raw) false t vq ∧ vq.search.mode = .found) →
      FoundRouteMC2 (PofC centre place entry raw) q first raw m c r c r)
    (hfoundReplay : ∀ (m : ℕ) (c : Control) (r : GalilVM) (cT : Control) (sT : GalilVM) (R k : ℕ),
      1 ≤ m → m ≤ raw.length → InvLPC raw c r →
      StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundScanNR raw) k
        ⟨c, r⟩ ⟨cT, sT⟩ →
      ReplayLanding raw cT sT R → SpanRep sT →
      position r.center < position sT.center → position sT.right ≤ 2 * m - 1 →
      (PalPeg.GalilReplaySpan.ChainEnd raw (PofC centre place entry raw) q first 2048
          (position sT.right + R) cT sT 0 R ∨
        PalPeg.GalilReplaySpan.BrokeAndRestarted raw (PofC centre place entry raw) q first 2048
          cT sT) →
      FoundInReplayRouteMC2 (PofC centre place entry raw) q first raw m c r) :
    CycleOracleMC2C (PofC centre place entry raw) q first raw := by
  intro m c r hm1 hmle hIC hp
  obtain ⟨c', t, hsW, hend⟩ := hsegmentM m c r hm1 hmle hIC hp
  obtain ⟨hs, es, hw⟩ := id hsW
  rcases hend with hT | hend
  · obtain ⟨hnr, hc1, hav, -, -⟩ := id hT
    by_cases hmt : read (left t.left) = read (right t.right)
    · obtain ⟨vq, hq⟩ := hsearch t hs.search true
      by_cases hf : vq.search.mode = .found
      · exact cycleOutMC2C_of_found centre place entry q first raw m hIC hw hs.center hav
          (hfound m c r c' t hm1 hmle hIC hp hsW hc1 hav hmt ⟨vq, hq, hf⟩)
      · exact Or.inl (reachAtC2_of_target_matchP centre place entry q first raw m hm1 hmle
          c r c' t (hpresT c r c' t hIC hsW hc1) hIC hsW hT hmt vq hq hf)
    · exact cycleOutMC2C_of_fallback'R centre place entry q first raw m hm1 hmle hex hsearch
        hshape hbudget hstage hrs (hfoundReplay m) (fun k y h hmm => hpresRepAt c r hIC k y h hmm) hIC hw hs.center hc1 hav
        (hmismatch m c r c' t hm1 hmle hIC hp hsW hnr hc1 hav hmt)
  · cases hend with
    | ended hn => exact Or.inl (hended m c r c' t hm1 hmle hIC hp hsW hn)
    | mismatch hr hc hav hne =>
        exact cycleOutMC2C_of_fallback'R centre place entry q first raw m hm1 hmle hex hsearch
          hshape hbudget hstage hrs (hfoundReplay m) (fun k y h hmm => hpresRepAt c r hIC k y h hmm) hIC hw hs.center hc hav
          (hmismatch m c r c' t hm1 hmle hIC hp hsW hr hc hav hne)
    | found hc hav hmt hq =>
        exact cycleOutMC2C_of_found centre place entry q first raw m hIC hw hs.center hav
          (hfound m c r c' t hm1 hmle hIC hp hsW hc hav hmt hq)
    | foundBackground hc hq =>
        exact cycleOutMC2C_of_foundBg centre place entry q first raw m hIC
          (hfoundBg m c r c' t hm1 hmle hIC hp hsW hc hq)
    | lastLetter hc hav hpop hinc =>
        by_cases hmt : read (left t.left) = read (right t.right)
        · exact Or.inl (hlastMatch m c r c' t hm1 hmle hIC hp hsW hc hav hpop hinc hmt)
        · exact Or.inl (hlastMismatch m c r c' t hm1 hmle hIC hp hsW hc hav hpop hinc hmt)

#print axioms cycleOracleMC2C_of_piecesP'

/-! ## 5. `H_oracle` with `hpres` gone -/

theorem h_oracle_of_leaves5 (entry q : ℕ) (first : Fin 9)
    (hreadyB : ∀ (w : List (Fin 2)) (c : Control) (r : GalilVM), InvLPC w c r →
      ∃ Φ : SearchVM → ℕ → ℕ → Prop,
        PalPeg.CloseoutReadyStage.ReadyIface (PofC centreC placeC entry w) Φ ∧
          Φ (searchLens.get r) (headRank r.right * 2048 + c.clock) (2048 - c.clock))
    (hpresRepAt : ∀ (w : List (Fin 2)) (c : Control) (r : GalilVM), InvLPC w c r →
      PalPeg.CloseoutPreload41.HpresRepAt centreC placeC entry q first w ⟨c, r⟩)
    (hpresT : ∀ (w : List (Fin 2)) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      InvLPC w c r → SegReachedW centreC placeC entry q first w c r c' t → c'.clock = 1 →
      PalPeg.CloseoutPreload40.HpresAt (PofC centreC placeC entry w) c' t)
    (hshape : ∀ w : List (Fin 2),
      PalPeg.GalilWatchOkInst.StartShape (PofC centreC placeC entry w))
    (hbudget : ∀ w : List (Fin 2),
      PalPeg.GalilFoundStage.ReplayBudgetR w (PofC centreC placeC entry w) q first 2048)
    (hstage : ∀ w : List (Fin 2),
      PalPeg.GalilFoundStage.ReplayStageInv w (PofC centreC placeC entry w) q first)
    (hrs : ∀ w : List (Fin 2),
      PalPeg.GalilReplaySpan.RestartShape (PofC centreC placeC entry w))
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
    (hfoundReplay : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (cT : Control)
      (sT : GalilVM) (R k : ℕ), 1 ≤ m → m ≤ w.length → InvLPC w c r →
      StepsAll (galilFrameS (PofC centreC placeC entry w) q first) 2048 (SoundScanNR w) k
        ⟨c, r⟩ ⟨cT, sT⟩ →
      ReplayLanding w cT sT R → SpanRep sT →
      position r.center < position sT.center → position sT.right ≤ 2 * m - 1 →
      (PalPeg.GalilReplaySpan.ChainEnd w (PofC centreC placeC entry w) q first 2048
          (position sT.right + R) cT sT 0 R ∨
        PalPeg.GalilReplaySpan.BrokeAndRestarted w (PofC centreC placeC entry w) q first 2048
          cT sT) →
      FoundInReplayRouteMC2 (PofC centreC placeC entry w) q first w m c r)
    (hstr : ∀ (w : List (Fin 2)) (c : Control) (r : GalilVM), InvL w c r → InvLPC w c r) :
    PalPeg.GalilFinalAssembly.H_oracle centreC placeC entry q first :=
  fun w _ => cycleOracleMC_of_MC2C
    (cycleOracleMC2C_of_piecesP' centreC placeC entry q first w
      (fun s => hex_C centreC placeC entry w s)
      (fun s hs a => hsearch_C centreC placeC entry w s hs a)
      (hpresRepAt w) (hpresT w) (hshape w) (hbudget w) (hstage w) (hrs w)
      (fun m c r _ _ hIC _ => by
        obtain ⟨Φ, hiface, hfuel⟩ := hreadyB w c r hIC
        obtain ⟨c', t, hsW, hEnd⟩ :=
          PalPeg.CloseoutReadyStage.segment_of_invLPCS centreC placeC entry q first w
            (fun s => hex_C centreC placeC entry w s)
            (fun s hs a => hsearch_C centreC placeC entry w s hs a) hiface c r hIC
            hfuel
        exact ⟨c', t, hsW, Or.inr hEnd⟩)
      (hended w) (hlastMatch w) (hlastMismatch w) (hmismatch w) (hfound w) (hfoundBg w)
      (hfoundReplay w)) (hstr w)

#print axioms h_oracle_of_leaves4

#print axioms h_oracle_of_leaves5

end PalPeg.CloseoutOracle6
