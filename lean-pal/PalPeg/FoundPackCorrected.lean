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


/-! ## 節 7（`BreakLandingC`）も同型に直す

`CloseoutWatchRound5.BreakLandingC` は

    ∀ es c2 s2, WatchSegE … cP sP c2 s2 →
      ∃ cen ys b, ys.length + 1 = h ∧ s2.chain = .watch (freshWatch …) ∧ es.count true = 0

で、節 4 とまったく同じ形（`∀` ＋ `WatchSegE.stop` で誕生状態 `sP` に当たる）。
`FoundPackRefute.breakLandingC_false_of_foundCompareCtx` が反証したとおり偽。
正しいのは `∃` 版。 -/

/-- **(NAMED, 正しい形)** `BreakLandingC` の `∃` 版。 -/
def BreakLandingAtReachedWatch (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (h : ℕ) (sF : GalilVM) (cP : Control) (sP : GalilVM) : Prop :=
  ∃ (es : List Bool) (c2 : Control) (s2 : GalilVM),
    WatchSegE (PofC centre place entry raw) qq first 2048 es cP sP c2 s2 ∧
      ∃ (cen : Fin 3) (ys : List (Fin 3)) (b : Fin 3),
        ys.length + 1 = h ∧
        s2.chain = ChainVM.watch
          (PalPeg.GalilNoShiftStage.freshWatch sF.center cen ys b sF.radius) ∧
        es.count true = 0

/-- **節 7 の正しい形は節 4 の正しい形を含意する。**  つまり `ReachesWatchPhase` を
1 本供給すれば両方に効く——束ね直すときに 2 本要らない。 -/
theorem reachesWatchPhase_of_breakLandingAtReachedWatch (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    {raw : List (Fin 2)} {h : ℕ} {sF : GalilVM} {cP : Control} {sP : GalilVM}
    (hBreak : BreakLandingAtReachedWatch centre place entry qq first raw h sF cP sP) :
    ReachesWatchPhase (PofC centre place entry raw) qq first cP sP := by
  obtain ⟨es, c2, s2, hSeg, cen, ys, b, -, hChain, -⟩ := hBreak
  exact ⟨es, c2, s2, hSeg, _, hChain⟩

#print axioms reachesWatchPhase_of_breakLandingAtReachedWatch


/-! ## run 側の選言のうち「shift には行けない」半分

`ReachesWatchPhase` を run から出すには「誕生後 `2h+1` tick 走って watch になる」か
「その前に不一致で fallback に落ちる」かの選言が要る（n119）。そのうち
**「shift には行けない」**部分は構造だけで出る:

`shiftGuardVM s` は `∃ w, s.chain = .watch w` を含む。誕生直後の chain は `.copy` で、
`ChainTick` 1 手では `.watch` に届かない（`FoundPackRefute.chainTick_copy_not_watch`）。
よって比較の行き先で guard は立たず、`Tick.scan_shift` は使えない。

これは「誕生した chain が、周期を写し終える前に shift に使われることはない」という
モデルの忠実性の帰結でもある（Scala の `canShift` は watch 相でしか true にならない）。 -/

/-- **copy 相の chain では shift guard は立たない。** -/
theorem not_shiftGuardVM_of_not_watch {s : GalilVM}
    (hNotWatch : ∀ wv : GalilScaffoldChainWatch.State, s.chain ≠ ChainVM.watch wv) :
    ¬ shiftGuardVM s := by
  rintro ⟨wv, hw, -⟩
  exact hNotWatch wv hw


/-- 具体枠 `PofC` では `shiftGuard = shiftGuardVM` で、watch を要求する。 -/
theorem guardNeedsWatch_PofC (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ) (raw : List (Fin 2)) :
    ∀ u : GalilVM, (PofC centre place entry raw).shiftGuard u →
      ∃ wv : GalilScaffoldChainWatch.State, u.chain = ChainVM.watch wv := by
  intro u hGuard
  obtain ⟨wv, hw, -⟩ : shiftGuardVM u := hGuard
  exact ⟨wv, hw⟩

/-- **誕生直後（`.copy` 相）の scan 状態からは shift に行けない。**
`Tick.scan_shift` の `shiftGuard` が立たないので、不一致が来ても行き先は
`scan_fallback` になる。 -/
theorem no_shift_from_copyChain {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ}
    {x y : State GalilVM}
    {t : GalilScaffoldTape.Tape} {hh : Counter} {pl : GalilScaffoldPlace.Place}
    {v : GalilScaffoldChainPeriod.Tape} {lag margin : Counter} {ver : PlaceHead}
    (hGuardNeedsWatch : ∀ u : GalilVM, P.shiftGuard u →
      ∃ wv : GalilScaffoldChainWatch.State, u.chain = ChainVM.watch wv)
    (hScan : x.ctl.mode = Mode.scan)
    (hCopy : x.vm.chain = ChainVM.copy t hh pl v lag margin ver)
    (hTick : Tick (galilFrameS P q first) delay x y) :
    y.ctl.mode ≠ Mode.shift := by
  cases hTick with
  | scan_shift c0 s0 s0' s0'' hm hav hClock hCompare hNotMatched hr hGuard hBegin =>
    exfalso
    obtain ⟨vs, vq, a, hvl, hvr, hiff, hsearch, hchain, hteq⟩ :
      compareFound P q first s0 s0' := hCompare
    have hNotIdle : s0.chain ≠ ChainVM.idle := by rw [hCopy]; intro h0; cases h0
    have hChainTick : ChainTick a s0.chain vs.chain := by
      rcases hchain with ⟨-, hct⟩ | ⟨hidle, -, -⟩ | ⟨hidle, -, -⟩
      · exact hct
      · exact absurd hidle hNotIdle
      · exact absurd hidle hNotIdle
    rw [hCopy] at hChainTick
    obtain ⟨wv, hw⟩ := hGuardNeedsWatch s0' hGuard
    have hChainEq : s0'.chain = vs.chain := by
      rw [hteq, afterBirth_chain]; split <;> rfl
    rw [hChainEq] at hw
    exact PalPeg.FoundPackRefute.chainTick_copy_not_watch hChainTick wv hw
  | shift_one c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hScan) (by decide)
  | init c0 s0 s0' hm _ => intro hEq; exact Mode.noConfusion hEq
  | scan_wait c0 s0 s0' hm _ _ => rw [hm]; intro hEq; exact Mode.noConfusion hEq
  | scan_count c0 s0 s0' hm _ _ _ => rw [hm]; intro hEq; exact Mode.noConfusion hEq
  | scan_match c0 s0 s0' s0'' o hm _ _ _ _ _ _ => rw [hm]; intro hEq; exact Mode.noConfusion hEq
  | scan_fallback c0 s0 s0' s0'' hm _ _ _ _ _ _ _ => intro hEq; exact Mode.noConfusion hEq
  | shift_done c0 s0 o hm _ _ => intro hEq; exact Mode.noConfusion hEq
  | replayStart c0 s0 s0' o hm _ _ _ => intro hEq; exact Mode.noConfusion hEq
  | restart c0 s0 s0' hm _ => rw [hm]; intro hEq; exact Mode.noConfusion hEq
  | copy_one c0 s0 s0' hm _ _ => rw [hm]; intro hEq; exact Mode.noConfusion hEq
  | copy_done c0 s0 s0' hm _ _ => intro hEq; exact Mode.noConfusion hEq
  | home_start c0 s0 s0' hm _ _ => intro hEq; exact Mode.noConfusion hEq
  | home_step c0 s0 s0' hm _ _ => rw [hm]; intro hEq; exact Mode.noConfusion hEq
  | fpp_slice c0 s0 s0' hm _ => rw [hm]; intro hEq; exact Mode.noConfusion hEq
  | fpp_done c0 s0 s0' hm _ => intro hEq; exact Mode.noConfusion hEq
  | markEnd_step c0 s0 s0' hm _ _ => rw [hm]; intro hEq; exact Mode.noConfusion hEq
  | markEnd_found c0 s0 s0' hm _ _ => intro hEq; exact Mode.noConfusion hEq
  | choose_select c0 s0 s0' hm _ _ _ => intro hEq; exact Mode.noConfusion hEq
  | choose_step c0 s0 s0' hm _ _ => rw [hm]; intro hEq; exact Mode.noConfusion hEq
  | rewind_done c0 s0 s0' hm _ _ => intro hEq; exact Mode.noConfusion hEq
  | rewind_one c0 s0 s0' hm _ _ _ => rw [hm]; intro hEq; exact Mode.noConfusion hEq
  | rewind_pair c0 s0 s0' hm _ _ _ => rw [hm]; intro hEq; exact Mode.noConfusion hEq

#print axioms not_shiftGuardVM_of_not_watch
#print axioms guardNeedsWatch_PofC
#print axioms no_shift_from_copyChain

end PalPeg.FoundPackCorrected
