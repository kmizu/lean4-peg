import PalPeg.MatchedRunSnoc
import PalPeg.CloseoutRoundSeg

/-!
# `RoundHistory` — ラウンドの履歴を状態と一緒に運ぶ

**なぜ状態局所な不変量では閉じないか**（測定済み、n147）。
ラウンド境界（`scan_shift`）で read origin を貼り替えるには
`CompareRounds h (toOnly s w₀) 1 (toOnly s' v)`——**ラウンド 1 周ぶんの履歴**が要る
（`CloseoutRoundSeg.originAt_next_of_roundSeg`）。1 手の `Tick` からは作れない。
だから不変量は履歴を持ち歩く形でないといけない。

`RoundHistory` はその形:「いまの状態は、`OriginAt` が立っているラウンド起点から
`ScanSeg`（scan 相の区間）で到達した」。

* **scan 相の tick で伸びる** — `MatchedRunSnoc.scanSeg_snoc_tick`。
  起点側のデータ（`OriginAt` / `periodOnly` / watch / lag ゼロ）は触らない
* **run に沿って伸びる** — `roundHistory_of_steps`。
  側条件は `MatchedRunSnoc.scanSeg_of_steps` と同じ `hScanWatchAll`
* **ラウンド境界で起点を貼り替える** — `GalilScaffoldTopRoundS.round_next` が
  `CompareRounds` を出し、`CloseoutRoundSeg.originAt_of_roundSeg` が origin を送る
  （このファイルではまだやらない）

**区間抽出（`CloseoutSegment.ScanToScan`）は使っていない。**

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option linter.dupNamespace false

namespace PalPeg.RoundHistory

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton
open PalPeg.CloseoutOriginAt PalPeg.CloseoutRoundSeg PalPeg.MatchedRunSnoc

/-- **(NAMED) ラウンドの履歴。**  いまの状態 `⟨c, s⟩` は、read origin が立っている
ラウンド起点 `⟨c₀, s₀⟩` から scan 相の区間で到達した。

起点側の 6 つ（`OriginAt` / `periodOnly = true` / watch / lag ゼロ /
`Canonical radius` / `Canonical length`）は `GalilScaffoldTopRoundS.round_next` と
`CloseoutOriginRounds.originAt_of_rounds` が要求するものとちょうど同じ。
`Canonical` を起点で持つのは、区間の末尾へは
`GalilScaffoldTopSegmentHeads.scanSeg_counters` が運んでくれるから
（`round_next` の `hlen : Canonical s1.length` がこれ）。 -/
def RoundHistory (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop :=
  ∃ (n : ℕ) (c₀ : Control) (s₀ : GalilVM) (w₀ : GalilScaffoldChainWatch.State),
    ScanSeg P q first delay n c₀ s₀ c s ∧
    OriginAt w s₀ ∧ s₀.periodOnly = true ∧
    s₀.chain = ChainVM.watch w₀ ∧ zero w₀.lag = true ∧
    Canonical s₀.radius ∧ Canonical s₀.length

section
variable {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ} {w : List (Fin 2)}

/-- **ラウンド起点そのものは `RoundHistory`。**  区間が空（`ScanSeg.stop`）。 -/
theorem roundHistory_start {c₀ : Control} {s₀ : GalilVM}
    {w₀ : GalilScaffoldChainWatch.State}
    (hOrigin : OriginAt w s₀) (hPeriodOnly : s₀.periodOnly = true)
    (hChain : s₀.chain = ChainVM.watch w₀) (hLagZero : zero w₀.lag = true)
    (hRadiusCanonical : Canonical s₀.radius) (hLengthCanonical : Canonical s₀.length) :
    RoundHistory P q first delay w c₀ s₀ :=
  ⟨0, c₀, s₀, w₀, ScanSeg.stop c₀ s₀, hOrigin, hPeriodOnly, hChain, hLagZero,
    hRadiusCanonical, hLengthCanonical⟩

/-- **scan 相の 1 tick で伸びる。**  `scanSeg_snoc_tick` の出口 2・3 は
「行き先も scan かつ watch」という呼び手の知識と矛盾するので落ちる。 -/
theorem roundHistory_tick {x y : State GalilVM}
    (hRestartNeedsBroken : ∀ u v : GalilVM, P.restart u v → ∃ wb, u.chain = ChainVM.broken wb)
    (hHistory : RoundHistory P q first delay w x.ctl x.vm)
    (hScan : x.ctl.mode = Mode.scan) (hNotReplaying : x.ctl.replaying = false)
    (hWatching : ∃ wch, x.vm.chain = ChainVM.watch wch)
    (hContinuing : singlePositive x.vm.cycle = false)
    (hTick : Tick (galilFrameS P q first) delay x y)
    (hStayScan : y.ctl.mode = Mode.scan)
    (hStayWatching : ∃ wch, y.vm.chain = ChainVM.watch wch) :
    RoundHistory P q first delay w y.ctl y.vm := by
  obtain ⟨n, c₀, s₀, w₀, hSeg, hOrigin, hPeriodOnly, hChain, hLagZero,
    hRadiusCanonical, hLengthCanonical⟩ := hHistory
  rcases scanSeg_snoc_tick hRestartNeedsBroken hSeg hScan hNotReplaying hWatching
      hContinuing hTick with ⟨m, hNext⟩ | hLeft | hBroke
  · exact ⟨m, c₀, s₀, w₀, hNext, hOrigin, hPeriodOnly, hChain, hLagZero,
      hRadiusCanonical, hLengthCanonical⟩
  · exact absurd hStayScan hLeft
  · obtain ⟨wch, hwch⟩ := hStayWatching
    exact absurd hwch (hBroke wch)

/-- **run に沿って伸びる。**  側条件は `MatchedRunSnoc.scanSeg_of_steps` と同じ
（区間の全点が scan ∧ 非 replay ∧ watch ∧ 周期が終端でない）。 -/
theorem roundHistory_of_steps {k : ℕ} {x y : State GalilVM}
    (hRestartNeedsBroken : ∀ u v : GalilVM, P.restart u v → ∃ wb, u.chain = ChainVM.broken wb)
    (hSteps : Steps (galilFrameS P q first) delay k x y)
    (hHistory : RoundHistory P q first delay w x.ctl x.vm)
    (hScanWatchAll : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS P q first) delay m x z →
      z.ctl.mode = Mode.scan ∧ z.ctl.replaying = false ∧
        (∃ wch, z.vm.chain = ChainVM.watch wch) ∧ singlePositive z.vm.cycle = false) :
    RoundHistory P q first delay w y.ctl y.vm := by
  induction hSteps with
  | zero u => exact hHistory
  | @succ j u z v hTick hRest ih =>
    obtain ⟨hScan, hNotReplaying, hWatching, hContinuing⟩ := hScanWatchAll 0 u (.zero u)
    obtain ⟨hScanZ, -, hWatchingZ, -⟩ := hScanWatchAll 1 z (.succ hTick (.zero z))
    exact ih (roundHistory_tick hRestartNeedsBroken hHistory hScan hNotReplaying hWatching
      hContinuing hTick hScanZ hWatchingZ)
      (fun m' z' hz' => hScanWatchAll (m' + 1) z' (.succ hTick hz'))

/-! ## shift 相は period テープに触らない

`CompareRounds.next` の残り入力（`hprediction` / ラウンド末の `periodLength`）は
どちらも period テープを見る。shift の 1 手 `chainShiftOne`
（`GalilScaffoldChainInputSupply:1478`）が変えるのは `distance` / `boundary` /
`last` / `margin` **だけ**なので、period テープはラウンドを通して不変。

`chain_shift_lag`（`GalilScaffoldTopRounds:19`）と `chain_shift_phase`
（`GalilScaffoldChainReadOrigin:451`）と同じ帰納法。 -/

/-- **shift 相は period テープを変えない。** -/
theorem chain_shift_period {s t : ShiftState} {w v : GalilScaffoldChainWatch.State}
    {cycle finish : Counter} {n : ℕ}
    (hShiftRun : ChainShiftRun s w cycle n t v finish) :
    v.machine.control.period = w.machine.control.period := by
  induction hShiftRun with
  | stop s w cycle => rfl
  | next s w cycle _ _ _ _ _ ih => exact ih

/-- **`periodLength` は shift を通って保存される。** -/
theorem chain_shift_periodLength {s t : ShiftState} {w v : GalilScaffoldChainWatch.State}
    {cycle finish : Counter} {n : ℕ}
    (hShiftRun : ChainShiftRun s w cycle n t v finish) :
    periodLength v = periodLength w := by
  unfold periodLength
  rw [chain_shift_period hShiftRun]

/-- **period テープの焦点記号も shift を通って不変。**  `CompareRounds.next` の
`hprediction` をラウンド境界で読み替えるのに使う。 -/
theorem chain_shift_period_focus {s t : ShiftState} {w v : GalilScaffoldChainWatch.State}
    {cycle finish : Counter} {n : ℕ}
    (hShiftRun : ChainShiftRun s w cycle n t v finish) :
    GalilScaffoldChainConsume.symbol v.machine.control.period.focus =
      GalilScaffoldChainConsume.symbol w.machine.control.period.focus := by
  rw [chain_shift_period hShiftRun]

/-- **履歴から下層の射影を取り出す。**  `CompareRounds.next` の第 1 引数。 -/
theorem onlyMatchedRun_of_roundHistory {c : Control} {s : GalilVM}
    (hHistory : RoundHistory P q first delay w c s) :
    ∃ (n : ℕ) (s₀ : GalilVM) (w₀ wch : GalilScaffoldChainWatch.State),
      OriginAt w s₀ ∧ s₀.periodOnly = true ∧ s₀.chain = ChainVM.watch w₀ ∧
      zero w₀.lag = true ∧ s.chain = ChainVM.watch wch ∧ zero wch.lag = true ∧
      s.periodOnly = true ∧ OnlyMatchedRun (toOnly s₀ w₀) n (toOnly s wch) ∧
      Canonical s.radius ∧ Canonical s.length := by
  obtain ⟨n, c₀, s₀, w₀, hSeg, hOrigin, hPeriodOnly, hChain, hLagZero,
    hRadiusCanonical, hLengthCanonical⟩ := hHistory
  obtain ⟨wch, hwch, hzch, hpoch, hrun⟩ :=
    scanSeg_only P q first delay hSeg w₀ hPeriodOnly hChain hLagZero
  obtain ⟨hRadiusNow, hLengthNow⟩ := scanSeg_counters P q first delay hSeg
  exact ⟨n, s₀, w₀, wch, hOrigin, hPeriodOnly, hChain, hLagZero, hwch, hzch, hpoch, hrun,
    hRadiusNow hRadiusCanonical, hLengthNow hLengthCanonical⟩

end

/-! ## 不一致比較では watch が動かない（lag ゼロのとき）

`round_next` の `hpred : read (right s1.right) = symbol w…period.focus` は
**compare 前**の watch `w` について言う。一方 shift guard は
`afterMismatch s1 vs vq` 上で評価されるので**compare 後**の watch を見る。
この差が埋まるのは lag ゼロのときだけ:

* `Internal` の `take` は `positive lag = true` を要求するので、lag ゼロなら `idle` のみ
  （`GalilScaffoldChainWatch:25-26`）
* 不一致比較の事象は `b = false` で、`Outer s false t` は `idle` のみ
  （`queued` と `immediate` はどちらも `b = true`。`GalilScaffoldChainWatch:31-33`）

よって watch は不変で、**`hpred` は guard からタダ**。 -/

/-- `zero` なら `positive` ではない。 -/
theorem positive_false_of_zero {c : Counter} (hZero : zero c = true) : positive c = false := by
  have hEmpty : c.pos.isEmpty = true := by
    simpa using (Bool.and_eq_true_iff.mp hZero).1
  simp [positive, hEmpty]

/-- **lag ゼロなら `Internal` は恒等。** -/
theorem internal_eq_of_lagZero {a b : GalilScaffoldChainWatch.State}
    (hLagZero : zero a.lag = true)
    (hInternal : GalilScaffoldChainWatch.Internal a b) : b = a := by
  cases hInternal with
  | idle _ => rfl
  | take hPos _ =>
    rw [positive_false_of_zero hLagZero] at hPos
    exact absurd hPos (by decide)

/-- **不一致（`b = false`）なら `Outer` は恒等。** -/
theorem outer_eq_of_false {a b : GalilScaffoldChainWatch.State}
    (hOuter : GalilScaffoldChainWatch.Outer a false b) : b = a := by
  cases hOuter with
  | idle => rfl

/-- **lag ゼロの不一致比較で watch は不変。**  `hpred` を guard から取るための橋。 -/
theorem watch_eq_of_mismatch_lagZero {a b : GalilScaffoldChainWatch.State}
    (hLagZero : zero a.lag = true)
    (hTick : GalilScaffoldChainWatch.Tick a false b) : b = a := by
  cases hTick with
  | step hInternal hOuter =>
    rename_i mid
    have hMid : mid = a := internal_eq_of_lagZero hLagZero hInternal
    subst hMid
    exact outer_eq_of_false hOuter

#print axioms positive_false_of_zero
#print axioms internal_eq_of_lagZero
#print axioms outer_eq_of_false
#print axioms watch_eq_of_mismatch_lagZero

/-! ## ラウンド内で period テープの長さが保たれる

`RoundSeg` の第 1 節は `periodLength wch' = periodLength wch`。ラウンドは
scan 相（`OnlyMatchedRun`）と shift 相（`ChainShiftRun`）でできているので、両方で要る。

* shift 相 → `chain_shift_periodLength`（上、公理ゼロ）
* scan 相 → 下の `periodLength_onlyMatchedRun`

`onlyCompareNext`（`GalilScaffoldChainInputSupply:2426`）は watch に `immediate` を
当てるだけだが、`periodLength_consume`（`GalilChainCoupling:210`）は**無条件ではなく**
`OnBlock m.control.period` を側条件に取る。その `OnBlock` は `consume` で保たれる
（`GalilBranchInvariants.onBlock_verifier_consume`）ので、**起点の 1 点だけ**あればよい。
起点の `WatchBlock` は `ChainPositionInvariantWithShiftPhase.coupled.block`
（`CloseoutRoundReads.blockInv_of_chainPosInv2`）から出る。 -/

/-- **scan 相のラウンドは period テープの長さを変えない**（＋ `WatchBlock` も運ぶ）。 -/
theorem periodLength_onlyMatchedRun {a b : OnlyCompareState} {n : ℕ}
    (hMatchedRun : OnlyMatchedRun a n b)
    (hBlock : PalPeg.GalilBranchInvariants.WatchBlock a.watch) :
    periodLength b.watch = periodLength a.watch ∧
      PalPeg.GalilBranchInvariants.WatchBlock b.watch := by
  induction hMatchedRun with
  | stop u => exact ⟨rfl, hBlock⟩
  | next u _ _ _ _ ih =>
    obtain ⟨hLength, hBlockEnd⟩ :=
      ih (PalPeg.GalilBranchInvariants.onBlock_verifier_consume _ hBlock)
    refine ⟨?_, hBlockEnd⟩
    rw [hLength]
    exact PalPeg.GalilChainCoupling.periodLength_consume u.watch.machine u.watch.lag
      u.watch.margin u.watch.lag (inc u.watch.margin) hBlock

#print axioms periodLength_onlyMatchedRun

/-! ## shift 相を run から集める

ラウンド境界の残りは `ChainShiftRun` 1 個（`PROOF_STACK.md` の入力表）。
`GalilScaffoldChainInputSupply.shift_round` は**順方向**（`ChainShiftRun` から `Steps`）で、
要るのは**逆**（run の shift 相から `ChainShiftRun`）。

`ChainShiftRun` は `next` で前から積む inductive なので、run を歩きながら積むには
後ろから伸ばせないといけない——`OnlyMatchedRun` と同じ問題で、
同じ形（`MatchedRunSnoc.onlyMatchedRun_snoc`）で解く。 -/

/-- **`ChainShiftRun` を後ろから 1 手伸ばす。** -/
theorem chainShiftRun_snoc {s t : ShiftState} {w v : GalilScaffoldChainWatch.State}
    {cycle finish : Counter} {n : ℕ}
    (hShiftRun : ChainShiftRun s w cycle n t v finish)
    (hEnabled : positive t.remaining = true)
    (hCenter : canRight t.center) (hLeft : canRight t.left)
    (hLeftNext : canRight (right t.left)) :
    ChainShiftRun s w cycle (n + 1) (shiftTick t) (chainShiftOne v) (inc (inc finish)) := by
  induction hShiftRun with
  | stop u w0 cyc => exact .next u w0 cyc hEnabled hCenter hLeft hLeftNext (.stop _ _ _)
  | next u w0 cyc he hc hl hl' _ ih =>
    exact .next u w0 cyc he hc hl hl' (ih hEnabled hCenter hLeft hLeftNext)

/-- **`shiftOne` 1 手を `ChainShiftRun` に吸収する。**

`Tick` の 23 構成子を場合分けしないのは、消費者側でどうせ場合分けするから
（`ShiftPhaseDeterminism.tick_shift_det` がその形）。ここは shift 1 手の中身だけを扱う。

`shiftOne` の中身（`GalilScaffoldTopShift:42`）は
`canRight center ∧ canRight left ∧ canRight (right left) ∧
 ∃ w, chain = .watch w ∧ t = ⟨shiftTick shift, .watch (chainShiftOne w), inc (inc cycle)⟩`
で、これは `ChainShiftRun.next` の 1 手そのもの。 -/
theorem chainShiftRun_snoc_shiftOne {P : Shared} {q : ℕ} {first : Fin 9}
    {s : ShiftState} {w : GalilScaffoldChainWatch.State} {cycle : Counter} {n : ℕ}
    {u t : GalilVM} {v : GalilScaffoldChainWatch.State}
    (hShiftRun : ChainShiftRun s w cycle n (shiftLens.get u).shift v (shiftLens.get u).cycle)
    (hChain : u.chain = ChainVM.watch v)
    (hRemaining : positive (shiftLens.get u).shift.remaining = true)
    (hShiftOne : (galilFrameS P q first).shiftOne u t) :
    t.chain = ChainVM.watch (chainShiftOne v) ∧
      ChainShiftRun s w cycle (n + 1) (shiftLens.get t).shift (chainShiftOne v)
        (shiftLens.get t).cycle := by
  obtain ⟨⟨hCenter, hLeft, hLeftNext, w1, hw1, hTarget⟩, -⟩ := hShiftOne
  have hw1v : w1 = v := by
    have hw1' : u.chain = ChainVM.watch w1 := hw1
    rw [hChain] at hw1'; cases hw1'; rfl
  subst hw1v
  refine ⟨congrArg (fun z : ShiftVM => z.chain) hTarget, ?_⟩
  rw [show (shiftLens.get t).shift = shiftTick (shiftLens.get u).shift from
        congrArg (fun z : ShiftVM => z.shift) hTarget,
      show (shiftLens.get t).cycle = inc (inc (shiftLens.get u).cycle) from
        congrArg (fun z : ShiftVM => z.cycle) hTarget]
  exact chainShiftRun_snoc hShiftRun hRemaining hCenter hLeft hLeftNext

/-- **shift 相の 1 tick で `ChainShiftRun` が伸びる。**

shift mode で起きうる `Tick` は `shift_one` と `shift_done` の 2 つだけ
（残り 21 個は mode guard で落ちる）。行き先も shift mode なら `shift_done` も落ちる
（`shift_done` は mode を `.scan` に戻す。`GalilScaffoldTop:136`）。

`hCopyIdle` が要るのは、合併フレームの `remainingPos` が `H ∨ B`
（`GalilScaffoldTopMerge:65`）なので copy 側の選択肢を殺さないといけないから。 -/
theorem chainShiftRun_tick {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ}
    {s : ShiftState} {w : GalilScaffoldChainWatch.State} {cycle : Counter} {n : ℕ}
    {x y : State GalilVM} {v : GalilScaffoldChainWatch.State}
    (hShiftRun : ChainShiftRun s w cycle n (shiftLens.get x.vm).shift v
      (shiftLens.get x.vm).cycle)
    (hChain : x.vm.chain = ChainVM.watch v)
    (hShift : x.ctl.mode = Mode.shift)
    (hCopyIdle : CopyIdle x.vm)
    (hTick : Tick (galilFrameS P q first) delay x y)
    (hStayShift : y.ctl.mode = Mode.shift) :
    ∃ v' : GalilScaffoldChainWatch.State, y.vm.chain = ChainVM.watch v' ∧
      ChainShiftRun s w cycle (n + 1) (shiftLens.get y.vm).shift v'
        (shiftLens.get y.vm).cycle := by
  cases hTick with
  | shift_one c0 s0 s0' hm hRemainingPos hShiftOne =>
    have hRemaining : positive (shiftLens.get s0).shift.remaining = true := by
      rcases hRemainingPos with hp | hp
      · exact hp
      · exact absurd hp hCopyIdle
    obtain ⟨hChainTarget, hRunTarget⟩ :=
      chainShiftRun_snoc_shiftOne hShiftRun hChain hRemaining hShiftOne
    exact ⟨chainShiftOne v, hChainTarget, hRunTarget⟩
  | shift_done c0 s0 o0 hm _ _ => simp at hStayShift
  | init c0 s0 s0' hm _ => exact absurd (hm.symm.trans hShift) (by decide)
  | scan_wait c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hShift) (by decide)
  | scan_count c0 s0 s0' hm _ _ _ => exact absurd (hm.symm.trans hShift) (by decide)
  | scan_match c0 s0 s0' s0'' o0 hm _ _ _ _ _ _ => exact absurd (hm.symm.trans hShift) (by decide)
  | scan_shift c0 s0 s0' s0'' hm _ _ _ _ _ _ _ => exact absurd (hm.symm.trans hShift) (by decide)
  | scan_fallback c0 s0 s0' s0'' hm _ _ _ _ _ _ _ => exact absurd (hm.symm.trans hShift) (by decide)
  | copy_one c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hShift) (by decide)
  | copy_done c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hShift) (by decide)
  | home_start c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hShift) (by decide)
  | home_step c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hShift) (by decide)
  | fpp_slice c0 s0 s0' hm _ => exact absurd (hm.symm.trans hShift) (by decide)
  | fpp_done c0 s0 s0' hm _ => exact absurd (hm.symm.trans hShift) (by decide)
  | markEnd_found c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hShift) (by decide)
  | markEnd_step c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hShift) (by decide)
  | choose_select c0 s0 s0' hm _ _ _ => exact absurd (hm.symm.trans hShift) (by decide)
  | choose_step c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hShift) (by decide)
  | rewind_done c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hShift) (by decide)
  | rewind_one c0 s0 s0' hm _ _ _ => exact absurd (hm.symm.trans hShift) (by decide)
  | rewind_pair c0 s0 s0' hm _ _ _ => exact absurd (hm.symm.trans hShift) (by decide)
  | replayStart c0 s0 s0' o0 hm _ _ _ => exact absurd (hm.symm.trans hShift) (by decide)
  | restart c0 s0 s0' hm _ => exact absurd (hm.symm.trans hShift) (by decide)

/-- **run に沿って `ChainShiftRun` が伸びる。**  側条件は区間の全点が shift mode ∧
`CopyIdle`（`roundHistory_of_steps` と同じ形）。 -/
theorem chainShiftRun_of_steps {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ}
    {s : ShiftState} {w : GalilScaffoldChainWatch.State} {cycle : Counter} {n k : ℕ}
    {x y : State GalilVM} {v : GalilScaffoldChainWatch.State}
    (hSteps : Steps (galilFrameS P q first) delay k x y)
    (hShiftRun : ChainShiftRun s w cycle n (shiftLens.get x.vm).shift v
      (shiftLens.get x.vm).cycle)
    (hChain : x.vm.chain = ChainVM.watch v)
    (hShiftAll : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS P q first) delay m x z →
      z.ctl.mode = Mode.shift ∧ CopyIdle z.vm) :
    ∃ v' : GalilScaffoldChainWatch.State, y.vm.chain = ChainVM.watch v' ∧
      ChainShiftRun s w cycle (n + k) (shiftLens.get y.vm).shift v'
        (shiftLens.get y.vm).cycle := by
  induction hSteps generalizing n v with
  | zero u => exact ⟨v, hChain, hShiftRun⟩
  | @succ j u z t hTick hRest ih =>
    obtain ⟨hShift, hCopyIdle⟩ := hShiftAll 0 u (.zero u)
    obtain ⟨hShiftZ, -⟩ := hShiftAll 1 z (.succ hTick (.zero z))
    obtain ⟨v', hChainZ, hRunZ⟩ :=
      chainShiftRun_tick hShiftRun hChain hShift hCopyIdle hTick hShiftZ
    obtain ⟨v'', hChainT, hRunT⟩ := ih hRunZ hChainZ
      (fun m' z' hz' => hShiftAll (m' + 1) z' (.succ hTick hz'))
    exact ⟨v'', hChainT, by rw [show n + (j + 1) = n + 1 + j from by omega]; exact hRunT⟩

#print axioms chainShiftRun_tick
#print axioms chainShiftRun_of_steps
#print axioms chainShiftRun_snoc
#print axioms chainShiftRun_snoc_shiftOne

#print axioms RoundHistory
#print axioms roundHistory_start
#print axioms roundHistory_tick
#print axioms roundHistory_of_steps
#print axioms onlyMatchedRun_of_roundHistory
#print axioms chain_shift_period
#print axioms chain_shift_periodLength
#print axioms chain_shift_period_focus

end PalPeg.RoundHistory
