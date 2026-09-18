import PalPeg.FoundPackRefute
import PalPeg.CloseoutWatchRound10

/-!
# `PrepLanding*` の正しい形（`∀` ではなく `∃`）

`FoundPackRefute` が機械検査したとおり、`CloseoutWatchRound7.PrepLandingWatchC` と
`CloseoutWatchRound5.PrepLandingLiveC` を found 比較直後の `sP` で要求するのは**偽**。
理由は結論が

    ∀ es c2 s2, WatchSegE P q first 2048 es cP sP c2 s2 → （c2 s2 で watch）

という**全称**で、`WatchSegE.stop cP sP` が無条件に存在するため `sP` 自身が watch で
あることを強制するから。ところが誕生直後の chain は `.copy` で、`ChainStep` に
`.copy → .watch` は無い（`chainTick_copy_not_watch`）。

**ここで重要なのは `WatchSegE` の側は壊れていないこと。** その `match` 構成子が
要求するのは `s.chain ≠ .idle` だけで（`GalilScaffoldTopWatchSegE:34`）、
copy 相も back 相も素通しできる。壊れているのは**結論の量化子**。

正しい形は「誕生から watch 相に**到達する**区間がある」という**存在**:

    ReachesWatchPhase P q first cP sP :=
      ∃ es c2 s2, WatchSegE P q first 2048 es cP sP c2 s2 ∧ ∃ w, s2.chain = .watch w

そして `PrepLandingWatchC` はその**到達先**で主張する。そこでは真で、producer も
既にある（`CloseoutWatchRound10.prepLandingWatchC_of_short`）。

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.FoundPackCorrected

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton
open PalPeg.CloseoutWatchRound7 (PrepLandingWatchC)

/-- **(NAMED, 正しい形)** 誕生から watch 相に到達する区間がある。

`PrepLandingWatchC` を `sP` で要求する代わりにこれを要求する。`∀ → ∃` の差が
`FoundPackRefute.hpack_false_of_foundReachable` で反証された誤りの正体。 -/
def ReachesWatchPhase (P : Shared) (q : ℕ) (first : Fin 9) (cP : Control) (sP : GalilVM) : Prop :=
  ∃ (es : List Bool) (c2 : Control) (s2 : GalilVM),
    WatchSegE P q first 2048 es cP sP c2 s2 ∧
      ∃ w : GalilScaffoldChainWatch.State, s2.chain = ChainVM.watch w

/-- **到達先では `PrepLandingWatchC` が正しく成り立つ。**  `CloseoutWatchRound10.
prepLandingWatchC_of_short` は watch 始点 ＋ clock 上界からそれを出すので、
`ReachesWatchPhase` の到達点に当てればよい。 -/
theorem prepLandingWatchC_at_reachedWatch (P : Shared) (q : ℕ) (first : Fin 9)
    {cP : Control} {sP : GalilVM} (hReach : ReachesWatchPhase P q first cP sP)
    (hShort : ∀ (c2 : Control) (s2 : GalilVM),
      (∃ (es : List Bool), WatchSegE P q first 2048 es cP sP c2 s2) →
      ∀ (es' : List Bool) (c3 : Control) (s3 : GalilVM),
        WatchSegE P q first 2048 es' c2 s2 c3 s3 → es'.length < c2.clock) :
    ∃ (es : List Bool) (c2 : Control) (s2 : GalilVM),
      WatchSegE P q first 2048 es cP sP c2 s2 ∧
      PrepLandingWatchC P q first c2 s2 := by
  obtain ⟨es, c2, s2, hSeg, hWatch⟩ := hReach
  exact ⟨es, c2, s2, hSeg,
    PalPeg.CloseoutWatchRound10.prepLandingWatchC_of_short P q first hWatch
      (hShort c2 s2 ⟨es, hSeg⟩)⟩

/-- **誕生直後で `ReachesWatchPhase` は空虚ではない** ことの確認: `WatchSegE` の
`match` 構成子は `s.chain ≠ .idle` しか要求しないので、copy 相も back 相も
区間に載る（`GalilScaffoldTopWatchSegE:34`）。つまり `∀ → ∃` の付け替えは
「要求を空虚に弱めた」のではなく、**量化子の位置を直した**もの。

この補題自体は `WatchSegE` の `match` 構成子が chain の相を見ないことの記録。 -/
theorem watchSegE_match_needs_only_nonIdle (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (c : Control) (s : GalilVM) (vs : ScanVM) (vq : SearchVM) (o : Bool)
    (hm : c.mode = Mode.scan) (hr : c.replaying = false) (ha : canRight s.right)
    (hc : c.clock = 1) (hne : s.chain ≠ ChainVM.idle)
    (hcmp : (galilFrame P q first).compare s (scanLens.set s vs))
    (hmt : (galilFrame P q first).matched (scanLens.set s vs))
    (hq : searchEffect P true s vq)
    (ho : refresh (galilFrame P q first) (afterCompare s vs vq) c.output o) :
    WatchSegE P q first delay [true] c s
      { c with clock := delay, output := o, replaying := false } (afterCompare s vs vq) :=
  .match c s vs vq o hm hr ha hc hne hcmp hmt hq ho (.stop _ _)

#print axioms prepLandingWatchC_at_reachedWatch
#print axioms watchSegE_match_needs_only_nonIdle

end PalPeg.FoundPackCorrected
