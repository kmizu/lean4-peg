import PalPeg.CloseoutOracle7
import PalPeg.GalilFoundStageInv

/-!
# `hor`: two more leaves are free

`CloseoutOracle7.h_oracle_of_leaves6` carries thirteen named leaves.  Two of
them are already theorems in the tree, and the reason both were still listed is
that their producers need `Decodes (PofC centreC placeC entry w)` — which is
**not** an obligation either:

```
GalilFinalAssembly2.decodesC (entry) (w) : Decodes (PofC centreC placeC entry w)
```

is proved (`:327`), because `Decodes` only constrains `P.centre` and `P.place`
(`GalilScaffoldTopReadyFound:22`) and `centreC` / `placeC` are concrete
functions of `s.center`.

| leaf | producer |
|---|---|
| `hrs` (`RestartShape`) | `GalilReplaySpan.restartShape_sharedC` — unconditional |
| `hbudget` (`ReplayBudgetR`) | `GalilFoundStageInv.replayBudgetR_of_decodes'` at `decodesC` |

`h_oracle_of_leaves7` below is `h_oracle_of_leaves6` with both discharged, so
`hor`'s leaf count drops from thirteen to eleven.

`hstage` (`ReplayStageInv`) is **not** discharged here, and the reason is in
`GalilFoundStageInv`'s own header: as stated it quantifies over every
`(c, s)` with `MInv` and `SearchReady`, and in that form it is not provable.
That is a reformulation, like `hsc` and `H_advanceT` before it, not a proof
obligation to grind.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutOracle8

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
open PalPeg.CloseoutOracle6 PalPeg.CloseoutOracle7

/-- **`hbudget` is free.**  `replayBudgetR_of_decodes'` at the proved
`decodesC`. -/
theorem hbudget_C (entry q : ℕ) (first : Fin 9) (w : List (Fin 2)) :
    PalPeg.GalilFoundStage.ReplayBudgetR w (PofC centreC placeC entry w) q first 2048 :=
  PalPeg.GalilFoundStageInv.replayBudgetR_of_decodes' (decodesC entry w)

/-- **`hrs` is free.**  `restartShape_sharedC` is unconditional and `PofC` is a
`sharedC`. -/
theorem hrs_C (entry : ℕ) (w : List (Fin 2)) :
    PalPeg.GalilReplaySpan.RestartShape (PofC centreC placeC entry w) :=
  restartShape_sharedC (onLetterVM w) leftFirstVM centreC placeC entry

/-- **`h_oracle_of_leaves6` with `hbudget` and `hrs` gone: eleven leaves.** -/
theorem h_oracle_of_leaves7 (entry q : ℕ) (first : Fin 9)
    (hreadyB : ∀ (w : List (Fin 2)) (c : Control) (r : GalilVM), InvLPC w c r →
      ReadyFuel (searchLens.get r) (headRank r.right * 2048 + c.clock) (headRank r.right))
    (hpresRepAt : ∀ (w : List (Fin 2)) (c : Control) (r : GalilVM), InvLPC w c r →
      PalPeg.CloseoutPreload41.HpresRepAt centreC placeC entry q first w ⟨c, r⟩)
    (hshape : ∀ w : List (Fin 2),
      PalPeg.GalilWatchOkInst.StartShape (PofC centreC placeC entry w))
    (hstage : ∀ w : List (Fin 2),
      PalPeg.GalilFoundStage.ReplayStageInv w (PofC centreC placeC entry w) q first)
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
  h_oracle_of_leaves6 entry q first hreadyB hpresRepAt hshape
    (hbudget_C entry q first) hstage (fun w => hrs_C entry w)
    hended hlastMatch hlastMismatch hmismatch hfound hfoundBg hfoundReplay hstr

#print axioms hbudget_C
#print axioms hrs_C
#print axioms h_oracle_of_leaves7

end PalPeg.CloseoutOracle8
