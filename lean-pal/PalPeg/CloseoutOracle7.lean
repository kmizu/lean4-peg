import PalPeg.CloseoutOracle6
import PalPeg.CloseoutPreload41

/-!
# `CloseoutOracle7`: `hpresT` integrated, `hpresRepAt` still open

`CloseoutOracle6.h_oracle_of_leaves5` carries **two** readiness residues:

* `hpresRepAt` — `CloseoutPreload41.HpresRepAt` at every `InvLPC` origin, i.e.
  `HpresAt` along the whole `SoundScanNR` run out of that origin;
* `hpresT` — `HpresAt` at the **exit** of a `SegReachedW` segment.

The second is a *consequence* of the first and nothing else:
`GalilOracleDischarge.SegReached.run` says the segment is precisely a
`SoundScanNR` run `⟨c, r⟩ ⇒ ⟨c', t⟩`, and `SegReached.mode` says the exit is in
`Mode.scan` — the two inputs `HpresRepAt` asks for.  So `hpresT` disappears
here (`hpresT_of_hpresRepAt`) and `h_oracle_of_leaves6` has one readiness
residue instead of two.

`hpresRepAt` itself is **not** discharged here, and the reason is stated
honestly rather than papered over.  The supplier
`CloseoutPreload41.hpresAt_along_soundScanNR` needs, at the origin `x`,
both `ReadyFieldP4 (n+1) x = ReadyFieldP3 (n+1) x` and
`CloseoutPackRun18.BigPack2M'' … x`.  The oracle quantifies over *arbitrary*
`InvLPC w c r` origins, and `InvLPC = InvLP2 ∧ CentreRep = (InvLP ∧ CopyPack) ∧
CentreRep` carries neither: it fixes no `c.clock = 2048`, no
`Restarted`/`StageEntry`/`CentreLongRun`/`NoReturn`/`EntryDepthG` datum (what
`CloseoutPreload39.readyField3_entry_of_datum` consumes) and no `BigPack2M''`
(no lemma in the tree produces `BigPack2M''` from `InvLPC`).  So
`hpresAt_along_soundScanNR` applies at a **boot/restart origin**, not at a
general `InvLPC` origin; closing `hpresRepAt` requires either a
`BigPack2M'' + ReadyFieldP3` pack transported to every `InvLPC` cycle entry, or
strengthening the oracle's origin predicate to a restart entry.  Faking it
would just rename the obligation, so it stays a named hypothesis.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutOracle7

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
open PalPeg.CloseoutOracle6

/-! ## 1. `hpresT` from `hpresRepAt` -/

/-- **`hpresT` is a consequence of `hpresRepAt`.**  A `SegReachedW` segment is a
`SoundScanNR` run from the origin (`SegReached.run`) whose exit is in `Mode.scan`
(`SegReached.mode`); `HpresRepAt` is exactly `HpresAt` at every such state.  The
`c'.clock = 1` guard is not even needed. -/
theorem hpresT_of_hpresRepAt (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    {w : List (Fin 2)} {c : Control} {r : GalilVM} {c' : Control} {t : GalilVM}
    (hrep : HpresRepAt centre place entry q first w ⟨c, r⟩)
    (hsW : SegReachedW centre place entry q first w c r c' t) :
    HpresAt (PofC centre place entry w) c' t := by
  obtain ⟨hs, -⟩ := id hsW
  obtain ⟨k, hst⟩ := hs.run
  exact hrep k ⟨c', t⟩ hst hs.mode

#print axioms hpresT_of_hpresRepAt

/-! ## 2. The oracle with `hpresT` gone -/

/-- **`h_oracle_of_leaves6`.**  `CloseoutOracle6.h_oracle_of_leaves5` with the
hypothesis `hpresT` removed: it is supplied from `hpresRepAt` by
`hpresT_of_hpresRepAt`.  `hpresRepAt` survives (see the header). -/
theorem h_oracle_of_leaves6 (entry q : ℕ) (first : Fin 9)
    (hreadyB : ∀ (w : List (Fin 2)) (c : Control) (r : GalilVM), InvLPC w c r →
      ∃ Φ : SearchVM → ℕ → ℕ → Prop,
        PalPeg.CloseoutReadyStage.ReadyIface (PofC centreC placeC entry w) Φ ∧
          Φ (searchLens.get r) (headRank r.right * 2048 + c.clock) (2048 - c.clock))
    (hpresRepAt : ∀ (w : List (Fin 2)) (c : Control) (r : GalilVM), InvLPC w c r →
      PalPeg.CloseoutPreload41.HpresRepAt centreC placeC entry q first w ⟨c, r⟩)
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
  h_oracle_of_leaves5 entry q first hreadyB hpresRepAt
    (fun w c r c' t hIC hsW _ =>
      hpresT_of_hpresRepAt centreC placeC entry q first (hpresRepAt w c r hIC) hsW)
    hshape hbudget hstage hrs hended hlastMatch hlastMismatch hmismatch hfound hfoundBg
    hfoundReplay hstr

#print axioms h_oracle_of_leaves6

end PalPeg.CloseoutOracle7
