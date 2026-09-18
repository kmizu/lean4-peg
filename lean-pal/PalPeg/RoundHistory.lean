import PalPeg.MatchedRunSnoc
import PalPeg.CloseoutRoundSeg
import PalPeg.CloseoutReadsOrigin
import PalPeg.CloseoutWatchRound45
import PalPeg.CloseoutMismatchCompare

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

起点側の 7 つ（`OriginAt` / `periodOnly = true` / watch / lag ゼロ / `WatchBlock` /
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
    PalPeg.GalilBranchInvariants.WatchBlock w₀ ∧
    Canonical s₀.radius ∧ Canonical s₀.length

section
variable {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ} {w : List (Fin 2)}

/-- **ラウンド起点そのものは `RoundHistory`。**  区間が空（`ScanSeg.stop`）。 -/
theorem roundHistory_start {c₀ : Control} {s₀ : GalilVM}
    {w₀ : GalilScaffoldChainWatch.State}
    (hOrigin : OriginAt w s₀) (hPeriodOnly : s₀.periodOnly = true)
    (hChain : s₀.chain = ChainVM.watch w₀) (hLagZero : zero w₀.lag = true)
    (hBlock : PalPeg.GalilBranchInvariants.WatchBlock w₀)
    (hRadiusCanonical : Canonical s₀.radius) (hLengthCanonical : Canonical s₀.length) :
    RoundHistory P q first delay w c₀ s₀ :=
  ⟨0, c₀, s₀, w₀, ScanSeg.stop c₀ s₀, hOrigin, hPeriodOnly, hChain, hLagZero, hBlock,
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
  obtain ⟨n, c₀, s₀, w₀, hSeg, hOrigin, hPeriodOnly, hChain, hLagZero, hBlock,
    hRadiusCanonical, hLengthCanonical⟩ := hHistory
  rcases scanSeg_snoc_tick hRestartNeedsBroken hSeg hScan hNotReplaying hWatching
      hContinuing hTick with ⟨m, hNext⟩ | hLeft | hBroke
  · exact ⟨m, c₀, s₀, w₀, hNext, hOrigin, hPeriodOnly, hChain, hLagZero, hBlock,
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

/-- **履歴から下層の射影を取り出す。**  `CompareRounds.next` の第 1 引数。 -/
theorem onlyMatchedRun_of_roundHistory {c : Control} {s : GalilVM}
    (hHistory : RoundHistory P q first delay w c s) :
    ∃ (n : ℕ) (s₀ : GalilVM) (w₀ wch : GalilScaffoldChainWatch.State),
      OriginAt w s₀ ∧ s₀.periodOnly = true ∧ s₀.chain = ChainVM.watch w₀ ∧
      zero w₀.lag = true ∧ PalPeg.GalilBranchInvariants.WatchBlock w₀ ∧
      s.chain = ChainVM.watch wch ∧ zero wch.lag = true ∧
      s.periodOnly = true ∧ OnlyMatchedRun (toOnly s₀ w₀) n (toOnly s wch) ∧
      Canonical s.radius ∧ Canonical s.length := by
  obtain ⟨n, c₀, s₀, w₀, hSeg, hOrigin, hPeriodOnly, hChain, hLagZero, hBlock,
    hRadiusCanonical, hLengthCanonical⟩ := hHistory
  obtain ⟨wch, hwch, hzch, hpoch, hrun⟩ :=
    scanSeg_only P q first delay hSeg w₀ hPeriodOnly hChain hLagZero
  obtain ⟨hRadiusNow, hLengthNow⟩ := scanSeg_counters P q first delay hSeg
  exact ⟨n, s₀, w₀, wch, hOrigin, hPeriodOnly, hChain, hLagZero, hBlock,
    hwch, hzch, hpoch, hrun, hRadiusNow hRadiusCanonical, hLengthNow hLengthCanonical⟩

end

/-! ## shift 末尾の射影の形

`CompareRounds.next` の `rest` の始点は
`⟨t'.center, t'.left, right t.right, v, cycle, t'.radius⟩` という明示の組
（`GalilScaffoldChainReadOrigin:1008`）。run から `CompareRounds h a 1 b` を作るには
`b = toOnly sEnd v` がこの組と一致しないといけない。

`toOnly s w = ⟨s.center, s.left, s.right, w, s.cycle, s.radius⟩`
（`GalilScaffoldTopOnly:20`）。`shiftLens.get` は
`⟨⟨center, left, remaining, radius, length⟩, chain, cycle⟩` なので
center / left / radius / cycle は `shiftLens` の中、**`right` は外**。
`right` は shift 相では変わらず（`shiftLens_frame_steps`）、
shift 入口の値は比較の `vs.right = right s1.right`。 -/

/-- **shift 末尾の射影は `CompareRounds.next` が期待する組そのもの。** -/
theorem toOnly_shiftEnd_eq {s1 s2 sEnd : GalilVM} {vs : ScanVM} {vq : SearchVM}
    {h : ℕ} {wch v : GalilScaffoldChainWatch.State} {t' : ShiftState} {cyc : Counter}
    (hRight : vs.right = right s1.right)
    (hBeginShift : beginShiftVM h wch (afterMismatch s1 vs vq) s2)
    (hFrame : sEnd = shiftLens.set s2 (shiftLens.get sEnd))
    (hGet : shiftLens.get sEnd = ⟨t', ChainVM.watch v, cyc⟩) :
    toOnly sEnd v = ⟨t'.center, t'.left, right s1.right, v, cyc, t'.radius⟩ := by
  obtain ⟨-, hTarget⟩ := hBeginShift
  have hRightEnd : sEnd.right = right s1.right := by
    rw [hFrame]
    show s2.right = right s1.right
    rw [hTarget]
    simp [afterMismatch, scanLens, searchLens, hRight]
  have hCenter : sEnd.center = t'.center := congrArg (fun z : ShiftVM => z.shift.center) hGet
  have hLeft : sEnd.left = t'.left := congrArg (fun z : ShiftVM => z.shift.left) hGet
  have hRadius : sEnd.radius = t'.radius := congrArg (fun z : ShiftVM => z.shift.radius) hGet
  have hCycle : sEnd.cycle = cyc := congrArg (fun z : ShiftVM => z.cycle) hGet
  simp only [toOnly, hCenter, hLeft, hRightEnd, hRadius, hCycle]

#print axioms toOnly_shiftEnd_eq

/-! ## shift の手数は `remaining` の初期値で決まる

`CompareRounds.next` は shift 相をちょうど `h` 手として要求する。run から呼ぶときは
「shift mode に留まった手数 `k`」しか分からないので、`k = h` が要る。
`GalilScaffoldTopInvariant.shift_run_remaining` は「ちょうど `h` 手なら尽きる」の向きで、
**逆向きは無い**ので作る。

`shiftTick`（`GalilScaffoldChainInputSupply:1442`）は `remaining := dec s.remaining`。
`ChainShiftRun.next` は `positive s.remaining = true` を要求するので、
`remaining` が尽きた時点で止まる手数は初期値で一意。 -/

/-- **`k` 手歩いて `remaining` が尽きたなら `k = h`。** -/
theorem chainShiftRun_length_eq {w : GalilScaffoldChainWatch.State} {cycle : Counter} :
    ∀ {h k : ℕ} {a b : ShiftState} {v : GalilScaffoldChainWatch.State} {finish : Counter},
      a.remaining = ofNat h → ChainShiftRun a w cycle k b v finish →
      positive b.remaining = false → k = h := by
  intro h k
  induction k generalizing h w cycle with
  | zero =>
    intro a b v finish hStart hShiftRun hExhausted
    cases hShiftRun
    rw [hStart, positive_ofNat] at hExhausted
    have hZero : h = 0 := by simpa using hExhausted
    omega
  | succ k ih =>
    intro a b v finish hStart hShiftRun hExhausted
    cases hShiftRun with
    | next _ _ _ hEnabled _ _ _ rest =>
      rw [hStart, positive_ofNat] at hEnabled
      have hPos : 0 < h := by simpa using hEnabled
      obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
      have hNext : (shiftTick a).remaining = ofNat h' := by
        show dec a.remaining = ofNat h'
        rw [hStart, dec_ofNat_succ]
      exact congrArg (· + 1) (ih hNext rest hExhausted)

#print axioms chainShiftRun_length_eq

/-! ## shift 入口の形

`round_next` と `CompareRounds.next` は shift 相の起点を
`⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩`
という**明示の形**で要求する。run から呼ぶにはこれに一致させないといけない。

一次情報で照合した:

* `ScanVM` は `left` / `right` / `chain` の 3 場だけ（`GalilScaffoldTopScan:26`）なので
  `scanLens.set` は center / radius / length を触らない
* `afterMismatch s vs vq = {searchLens.set (scanLens.set s vs) vq with radius := radiusAfter s}`
  （`GalilScaffoldTopSearch:52`）、`radiusAfter s = inc s.radius`（無条件）
* `beginShiftVM h w s t` は `remaining := ofNat h` / `length := inc (inc s.length)` /
  `chain := .watch (immediate w)` / `cycle := reset` / `periodOnly := true` を置く
  （`GalilScaffoldTopShiftCycle:23`）

よって比較の `hLeft : vs.left = left s1.left` だけで形が一致する。 -/

/-- **shift 入口の shift 状態は `round_next` の要求する形そのもの。** -/
theorem shiftEntry_shape {h : ℕ} {s1 s2 : GalilVM} {vs : ScanVM} {vq : SearchVM}
    {wch : GalilScaffoldChainWatch.State}
    (hLeft : vs.left = GalilScaffoldInputHead.left s1.left)
    (hBeginShift : beginShiftVM h wch (afterMismatch s1 vs vq) s2) :
    (shiftLens.get s2).shift
        = ⟨s1.center, GalilScaffoldInputHead.left s1.left, ofNat h, inc s1.radius,
           inc (inc s1.length)⟩ ∧
      (shiftLens.get s2).chain = ChainVM.watch (GalilScaffoldChainWatch.immediate wch) ∧
      (shiftLens.get s2).cycle = reset := by
  obtain ⟨-, hTarget⟩ := hBeginShift
  refine ⟨?_, ?_, ?_⟩ <;> rw [hTarget] <;>
    simp [shiftLens, afterMismatch, scanLens, searchLens, radiusAfter, hLeft]

#print axioms shiftEntry_shape

/-! ## shift 相では `shiftLens` の外は変わらない

`round_next` の結論は状態を `shiftLens.set s2 ⟨t', .watch v, cycle⟩` の形で書く。
run から呼ぶときはその形に合わせないといけない。`shiftOne` は `Lens.rel`
（`GalilScaffoldTopLens:28`：`R (L.get s) (L.get t) ∧ t = L.set s (L.get t)`）なので、
第 2 成分がちょうど「lens の場以外は変わらない」。これを `Steps` に沿って
`Lens.set_set` で合成する。 -/

/-- **1 tick 分。** -/
theorem shiftLens_frame_tick {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ}
    {x y : State GalilVM}
    (hShift : x.ctl.mode = Mode.shift)
    (hTick : Tick (galilFrameS P q first) delay x y)
    (hStayShift : y.ctl.mode = Mode.shift) :
    y.vm = shiftLens.set x.vm (shiftLens.get y.vm) := by
  cases hTick with
  | shift_one c0 s0 s0' hm _ hShiftOne => exact hShiftOne.2
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

/-- **run 全体。** -/
theorem shiftLens_frame_steps {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ}
    {k : ℕ} {x y : State GalilVM}
    (hSteps : Steps (galilFrameS P q first) delay k x y)
    (hShiftAll : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS P q first) delay m x z → z.ctl.mode = Mode.shift) :
    y.vm = shiftLens.set x.vm (shiftLens.get y.vm) := by
  induction hSteps with
  | zero u => exact (shiftLens.set_get u.vm).symm
  | @succ j u z t hTick hRest ih =>
    have hStep : z.vm = shiftLens.set u.vm (shiftLens.get z.vm) :=
      shiftLens_frame_tick (hShiftAll 0 u (.zero u)) hTick
        (hShiftAll 1 z (.succ hTick (.zero z)))
    have hRestEq : t.vm = shiftLens.set z.vm (shiftLens.get t.vm) :=
      ih (fun m' z' hz' => hShiftAll (m' + 1) z' (.succ hTick hz'))
    have hCompose : shiftLens.set z.vm (shiftLens.get t.vm)
        = shiftLens.set u.vm (shiftLens.get t.vm) := by
      conv_lhs => rw [hStep]
      exact shiftLens.set_set _ _ _
    exact hRestEq.trans hCompose

#print axioms shiftLens_frame_tick
#print axioms shiftLens_frame_steps

/-! ## 不一致比較では watch が動かない（lag ゼロのとき）

**ここに 4 本書いたが、全部既存の再発明だったので消した**（コウタの指摘 2026-09-19
「定理ふえすぎてへん？ほんとうに必要？」）:

| 消した自作 | 既にあったもの |
|---|---|
| `positive_false_of_zero` | `GalilMismatchCaught.positive_false_of_zero:67`（文言まで同一） |
| `internal_eq_of_lagZero` | `CloseoutWatchRound4.internal_eq_of_zero:240` |
| `chainStep_watch_eq_of_lagZero` | `CloseoutMismatchCompare.chainStep_watch_of_lagZero:91` |
| `chainTick_false_watch_eq_of_lagZero` | `CloseoutMismatchCompare.chainTick_false_idle:46` |

さらに `CloseoutMismatchCompare.compare_chain_of_mismatch:99` は
「lag ゼロの不一致比較で `vs.chain = .watch w` ∧ `vs.left = left s.left` ∧
`vs.right = right s.right`」を**まとめて**出す。以後はそれを使う。 -/


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

/-! ## 組み立て: ラウンド 1 周を run から

`CompareRounds.next`（`GalilScaffoldChainReadOrigin:996`）を run の材料で埋める。
`rest` は `.stop` なので index は `0+1 = 1`。`PROOF_STACK.md` 手順 7。
**フレーム（`P` / `q` / `first` / `delay`）に依らない**——run から取り出した材料だけで閉じる。 -/

/-- **ラウンド 1 周。**  `CompareRounds (periodLength wch) (toOnly s₀ w₀) 1 (toOnly sEnd v)`。 -/
theorem compareRounds_one_of_run {s₀ s1 s2 sEnd : GalilVM}
    {w₀ wch v : GalilScaffoldChainWatch.State} {n k : ℕ}
    {vs : ScanVM} {vq : SearchVM}
    (hMatchedRun : OnlyMatchedRun (toOnly s₀ w₀) n (toOnly s1 wch))
    (hTerminal : singlePositive s1.cycle = true)
    (hCanRight : canRight s1.right)
    (hPredict : GalilScaffoldInputHead.read (right s1.right) =
      GalilScaffoldChainConsume.symbol wch.machine.control.period.focus)
    (hLengthCanonical : Canonical s1.length)
    (hRight : vs.right = right s1.right)
    (hLeft : vs.left = GalilScaffoldInputHead.left s1.left)
    (hBeginShift : beginShiftVM (periodLength wch) wch (afterMismatch s1 vs vq) s2)
    (hShiftRun : ChainShiftRun (shiftLens.get s2).shift
      (GalilScaffoldChainWatch.immediate wch) (shiftLens.get s2).cycle k
      (shiftLens.get sEnd).shift v (shiftLens.get sEnd).cycle)
    (hExhausted : positive (shiftLens.get sEnd).shift.remaining = false)
    (hFrame : sEnd = shiftLens.set s2 (shiftLens.get sEnd))
    (hChainEnd : sEnd.chain = ChainVM.watch v) :
    CompareRounds (periodLength wch) (toOnly s₀ w₀) 1 (toOnly sEnd v) := by
  obtain ⟨hShape, -, hCycleEntry⟩ := shiftEntry_shape hLeft hBeginShift
  have hStartRemaining : (shiftLens.get s2).shift.remaining = ofNat (periodLength wch) := by
    rw [hShape]
  have hLenEq : k = periodLength wch :=
    chainShiftRun_length_eq hStartRemaining hShiftRun hExhausted
  subst hLenEq
  rw [hShape, hCycleEntry] at hShiftRun
  have hGet : shiftLens.get sEnd
      = ⟨(shiftLens.get sEnd).shift, ChainVM.watch v, (shiftLens.get sEnd).cycle⟩ := by
    rw [← hChainEnd]; rfl
  rw [toOnly_shiftEnd_eq hRight hBeginShift hFrame hGet]
  exact CompareRounds.next (toOnly s₀ w₀) hMatchedRun hTerminal hCanRight hPredict
    (inc_canonical _ (inc_canonical _ hLengthCanonical))
    (shiftRun_of_chain hShiftRun) hShiftRun (.stop _)

#print axioms compareRounds_one_of_run

/-- **`RoundSeg` を run から**（`PROOF_STACK.md` 手順 8）。

第 1 節 `periodLength v = periodLength w₀` は 3 段の合成:

* scan 相 → `periodLength_onlyMatchedRun`
* `immediate` 1 手 → `GalilChainCoupling.periodLength_consume`（側条件は `WatchBlock`、
  これも `periodLength_onlyMatchedRun` が一緒に返す）
* shift 相 → `chain_shift_periodLength`（公理ゼロ） -/
theorem roundSeg_of_run {w : List (Fin 2)} {s₀ s1 s2 sEnd : GalilVM}
    {w₀ wch v : GalilScaffoldChainWatch.State} {n k : ℕ}
    {vs : ScanVM} {vq : SearchVM}
    (hChainStart : s₀.chain = ChainVM.watch w₀)
    (hBlockStart : PalPeg.GalilBranchInvariants.WatchBlock w₀)
    (hMatchedRun : OnlyMatchedRun (toOnly s₀ w₀) n (toOnly s1 wch))
    (hTerminal : singlePositive s1.cycle = true)
    (hCanRight : canRight s1.right)
    (hPredict : GalilScaffoldInputHead.read (right s1.right) =
      GalilScaffoldChainConsume.symbol wch.machine.control.period.focus)
    (hLengthCanonical : Canonical s1.length)
    (hRight : vs.right = right s1.right)
    (hLeft : vs.left = GalilScaffoldInputHead.left s1.left)
    (hBeginShift : beginShiftVM (periodLength wch) wch (afterMismatch s1 vs vq) s2)
    (hShiftRun : ChainShiftRun (shiftLens.get s2).shift
      (GalilScaffoldChainWatch.immediate wch) (shiftLens.get s2).cycle k
      (shiftLens.get sEnd).shift v (shiftLens.get sEnd).cycle)
    (hExhausted : positive (shiftLens.get sEnd).shift.remaining = false)
    (hFrame : sEnd = shiftLens.set s2 (shiftLens.get sEnd))
    (hChainEnd : sEnd.chain = ChainVM.watch v) :
    RoundSeg w s₀ sEnd := by
  intro wchA wchB hChainA hChainB
  have hEqA : wchA = w₀ := by rw [hChainStart] at hChainA; cases hChainA; rfl
  have hEqB : wchB = v := by rw [hChainEnd] at hChainB; cases hChainB; rfl
  rw [hEqA, hEqB]
  obtain ⟨hPeriodScan, hBlockEnd⟩ := periodLength_onlyMatchedRun hMatchedRun hBlockStart
  simp only [toOnly] at hPeriodScan hBlockEnd
  have hPeriodImmediate :
      periodLength (GalilScaffoldChainWatch.immediate wch) = periodLength wch :=
    PalPeg.GalilChainCoupling.periodLength_consume wch.machine wch.lag wch.margin
      wch.lag (inc wch.margin) hBlockEnd
  have hPeriodShift : periodLength v = periodLength (GalilScaffoldChainWatch.immediate wch) :=
    chain_shift_periodLength hShiftRun
  refine ⟨by rw [hPeriodShift, hPeriodImmediate, hPeriodScan], ?_⟩
  rw [← hPeriodScan]
  exact compareRounds_one_of_run hMatchedRun hTerminal hCanRight hPredict hLengthCanonical
    hRight hLeft hBeginShift hShiftRun hExhausted hFrame hChainEnd

#print axioms roundSeg_of_run

/-! ## 手順 9〜11: `OriginAt` の引き継ぎと `H_readsShift`

`roundSeg_of_run` の上に 1 行ずつ乗るだけ。`hsome` はラウンド起点の chain が
watch であることから無償。 -/

section Handoff
variable {w : List (Fin 2)} {s₀ s1 s2 sEnd : GalilVM}
  {w₀ wch v : GalilScaffoldChainWatch.State} {n k : ℕ} {vs : ScanVM} {vq : SearchVM}

/-- **手順 9: 次のラウンド起点の `OriginAt`。** -/
theorem originAt_next_of_run
    (hOrigin : OriginAt w s₀)
    (hChainStart : s₀.chain = ChainVM.watch w₀)
    (hRoundSeg : RoundSeg w s₀ sEnd) :
    OriginAt w sEnd :=
  originAt_of_roundSeg hOrigin hRoundSeg (fun _ _ => ⟨w₀, hChainStart⟩)

end Handoff

#print axioms originAt_next_of_run

/-! ## shift 相の carrier

`RoundHistory` は scan 相しか覆わない（`ScanSeg` が scan 相の区間）。
ラウンドの shift 相を run に沿って運ぶには別の carrier が要る。
中身は `roundSeg_of_run` の仮説を束ねたもの。

* `shiftPhaseHistory_originAt` — `remaining` が尽きた点で `OriginAt`
* `shiftPhaseHistory_readsShift` — 同じ点で `H_readsShift` -/

/-- **(NAMED) shift 相の履歴。**  `roundSeg_of_run` の仮説の束。 -/
def ShiftPhaseHistory (w : List (Fin 2)) (s : GalilVM) : Prop :=
  ∃ (s₀ s1 s2 : GalilVM) (w₀ wch v : GalilScaffoldChainWatch.State) (n k : ℕ)
    (vs : ScanVM) (vq : SearchVM),
    OriginAt w s₀ ∧ s₀.chain = ChainVM.watch w₀ ∧
    PalPeg.GalilBranchInvariants.WatchBlock w₀ ∧
    OnlyMatchedRun (toOnly s₀ w₀) n (toOnly s1 wch) ∧
    zero wch.lag = true ∧ s2.periodOnly = true ∧
    singlePositive s1.cycle = true ∧ canRight s1.right ∧
    GalilScaffoldInputHead.read (right s1.right) =
      GalilScaffoldChainConsume.symbol wch.machine.control.period.focus ∧
    Canonical s1.radius ∧ Canonical s1.length ∧
    vs.right = right s1.right ∧ vs.left = GalilScaffoldInputHead.left s1.left ∧
    beginShiftVM (periodLength wch) wch (afterMismatch s1 vs vq) s2 ∧
    ChainShiftRun (shiftLens.get s2).shift
      (GalilScaffoldChainWatch.immediate wch) (shiftLens.get s2).cycle k
      (shiftLens.get s).shift v (shiftLens.get s).cycle ∧
    s = shiftLens.set s2 (shiftLens.get s) ∧
    s.chain = ChainVM.watch v

/-- **`remaining` が尽きた shift 点では `OriginAt`。**（次のラウンドの起点） -/
theorem shiftPhaseHistory_originAt {w : List (Fin 2)} {s : GalilVM}
    (hHistory : ShiftPhaseHistory w s)
    (hExhausted : positive (shiftLens.get s).shift.remaining = false) :
    OriginAt w s := by
  obtain ⟨s₀, s1, s2, w₀, wch, v, n, k, vs, vq, hOrigin, hChainStart, hBlockStart,
    hMatchedRun, hLagTerminal, hPeriodOnlyEntry, hTerminal, hCanRight, hPredict,
    hRadiusCanonical, hLengthCanonical, hRight, hLeft, hBeginShift, hShiftRun, hFrame,
    hChainEnd⟩ := hHistory
  exact originAt_next_of_run hOrigin hChainStart
    (roundSeg_of_run hChainStart hBlockStart hMatchedRun hTerminal hCanRight hPredict
      hLengthCanonical hRight hLeft hBeginShift hShiftRun hExhausted hFrame hChainEnd)

/-- **同じ点で `H_readsShift`。** -/
theorem shiftPhaseHistory_readsShift {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hHistory : ShiftPhaseHistory w s)
    (hExhausted : positive (shiftLens.get s).shift.remaining = false) :
    PalPeg.CloseoutRoundUnique.H_readsShift w c s :=
  PalPeg.CloseoutReadsOrigin.h_readsShift_of_originAt
    (shiftPhaseHistory_originAt hHistory hExhausted)

#print axioms ShiftPhaseHistory
#print axioms shiftPhaseHistory_originAt
#print axioms shiftPhaseHistory_readsShift

/-- **shift 相の 1 tick で `ShiftPhaseHistory` が伸びる。** -/
theorem shiftPhaseHistory_tick {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ}
    {w : List (Fin 2)} {x y : State GalilVM}
    (hHistory : ShiftPhaseHistory w x.vm)
    (hShift : x.ctl.mode = Mode.shift)
    (hCopyIdle : CopyIdle x.vm)
    (hTick : Tick (galilFrameS P q first) delay x y)
    (hStayShift : y.ctl.mode = Mode.shift) :
    ShiftPhaseHistory w y.vm := by
  obtain ⟨s₀, s1, s2, w₀, wch, v, n, k, vs, vq, hOrigin, hChainStart, hBlockStart,
    hMatchedRun, hLagTerminal, hPeriodOnlyEntry, hTerminal, hCanRight, hPredict,
    hRadiusCanonical, hLengthCanonical, hRight, hLeft, hBeginShift, hShiftRun, hFrame,
    hChainEnd⟩ := hHistory
  cases hTick with
  | shift_one c0 s0 s0' hm hRemainingPos hShiftOne =>
    have hRemaining : positive (shiftLens.get s0).shift.remaining = true := by
      rcases hRemainingPos with hp | hp
      · exact hp
      · exact absurd hp hCopyIdle
    obtain ⟨hChainTarget, hRunTarget⟩ :=
      chainShiftRun_snoc_shiftOne hShiftRun hChainEnd hRemaining hShiftOne
    have hFrameStep : s0' = shiftLens.set s0 (shiftLens.get s0') := hShiftOne.2
    have hFrameHere : s0 = shiftLens.set s2 (shiftLens.get s0) := hFrame
    have hFrameTarget : s0' = shiftLens.set s2 (shiftLens.get s0') := by
      rw [hFrameStep]
      conv_lhs => rw [hFrameHere]
      exact shiftLens.set_set _ _ _
    exact ⟨s₀, s1, s2, w₀, wch, chainShiftOne v, n, k + 1, vs, vq,
      hOrigin, hChainStart, hBlockStart, hMatchedRun, hLagTerminal, hPeriodOnlyEntry,
      hTerminal, hCanRight, hPredict, hRadiusCanonical, hLengthCanonical, hRight, hLeft,
      hBeginShift, hRunTarget, hFrameTarget, hChainTarget⟩
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

#print axioms shiftPhaseHistory_tick

/-- **`shift_done` の遷移**: shift 相が終わると次のラウンドの `RoundHistory` が立つ。

VM は `shift_done` では変わらない（`GalilScaffoldTop:136`）ので、この状態がそのまま
次のラウンドの起点。7 つの場の出どころ:

| 場 | 出どころ |
|---|---|
| `OriginAt w s` | `shiftPhaseHistory_originAt` |
| `s.periodOnly = true` | `beginShiftVM` が置いた値。`shiftLens` の外なので shift 相で不変 |
| `s.chain = .watch v` | `ShiftPhaseHistory` |
| `zero v.lag = true` | `chain_shift_lag`（`immediate` は lag を変えない） |
| `WatchBlock v` | `chain_shift_period` ＋ `onBlock_verifier_consume` |
| `Canonical s.radius` / `Canonical s.length` | `shift_run_canonical` |
 -/
theorem roundHistory_of_shiftDone {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ}
    {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hHistory : ShiftPhaseHistory w s)
    (hExhausted : positive (shiftLens.get s).shift.remaining = false) :
    RoundHistory P q first delay w c s := by
  have hOriginNext : OriginAt w s := shiftPhaseHistory_originAt hHistory hExhausted
  obtain ⟨s₀, s1, s2, w₀, wch, v, n, k, vs, vq, hOrigin, hChainStart, hBlockStart,
    hMatchedRun, hLagTerminal, hPeriodOnlyEntry, hTerminal, hCanRight, hPredict,
    hRadiusCanonical, hLengthCanonical, hRight, hLeft, hBeginShift, hShiftRun, hFrame,
    hChainEnd⟩ := hHistory
  obtain ⟨hShape, -, -⟩ := shiftEntry_shape hLeft hBeginShift
  obtain ⟨-, hBlockEnd⟩ := periodLength_onlyMatchedRun hMatchedRun hBlockStart
  simp only [toOnly] at hBlockEnd
  -- periodOnly は shiftLens の外
  have hPeriodOnly : s.periodOnly = true := by
    rw [hFrame]; exact hPeriodOnlyEntry
  -- lag
  have hLagZero : zero v.lag = true := by
    rw [chain_shift_lag hShiftRun]; exact hLagTerminal
  -- WatchBlock
  have hBlockNext : PalPeg.GalilBranchInvariants.WatchBlock v := by
    show PalPeg.GalilBranchInvariants.OnBlock v.machine.control.period
    rw [chain_shift_period hShiftRun]
    exact PalPeg.GalilBranchInvariants.onBlock_verifier_consume _ hBlockEnd
  -- Canonical
  have hCanonicalNext : ShiftCanonical (shiftLens.get s).shift :=
    shift_run_canonical (shiftRun_of_chain hShiftRun)
      (by rw [hShape]
          exact ⟨ofNat_canonical _, inc_canonical _ hRadiusCanonical,
            inc_canonical _ (inc_canonical _ hLengthCanonical)⟩)
  exact roundHistory_start hOriginNext hPeriodOnly hChainEnd hLagZero hBlockNext
    hCanonicalNext.2.1 hCanonicalNext.2.2

#print axioms roundHistory_of_shiftDone

/-- **`scan_shift` の遷移**（`RoundHistory` → `ShiftPhaseHistory`、`k = 0`）。

guard（`shiftGuardVM`）と `beginShiftVM'` の中身を `PofC` の形で取る。
`P.shiftGuard = shiftGuardVM` / `P.beginShift = beginShiftVM'` は `PofC` では定義通り。 -/
theorem shiftPhaseHistory_of_scanShift {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ}
    {w : List (Fin 2)} {c1 : Control} {s1 s' s2 : GalilVM}
    (hHistory : RoundHistory P q first delay w c1 s1)
    (hCompare : (galilFrameS P q first).compare s1 s')
    (hNotMatched : ¬ (galilFrameS P q first).matched s')
    (hGuard : shiftGuardVM s')
    (hBegin : beginShiftVM' s' s2)
    (hCanRight : canRight s1.right) :
    ShiftPhaseHistory w s2 := by
  obtain ⟨n, s₀, w₀, wch, hOrigin, hPeriodOnlyStart, hChainStart, hLagStart, hBlockStart,
    hChainTerm, hLagTerm, hPeriodOnlyTerm, hMatchedRun, hRadiusTerm, hLengthTerm⟩ :=
    onlyMatchedRun_of_roundHistory hHistory
  obtain ⟨vs, vq, hTargetEq, -, hLeft, hRight, hChainTick, -, -, -⟩ :=
    compare_mismatched_parts hCompare hNotMatched hChainTerm
  have hChainTickWatch : ChainTick false (ChainVM.watch wch) vs.chain := by
    rw [← hChainTerm]; exact hChainTick
  have hChainMid : vs.chain = ChainVM.watch wch :=
    by
      obtain ⟨y, hStep, hEq⟩ := hChainTickWatch
      rw [if_neg (by simp)] at hEq
      rw [hEq]
      exact PalPeg.CloseoutMismatchCompare.chainStep_watch_of_lagZero hLagTerm hStep
  -- `s'` の場を `s1` / `vs` の場で書き換える
  have hMidChain : s'.chain = ChainVM.watch wch := by
    rw [hTargetEq]
    show vs.chain = ChainVM.watch wch
    exact hChainMid
  have hMidRight : s'.right = right s1.right := by
    rw [hTargetEq]
    show vs.right = right s1.right
    exact hRight
  have hMidCycle : s'.cycle = s1.cycle := by rw [hTargetEq]; rfl
  have hMidPeriodOnly : s'.periodOnly = true := by rw [hTargetEq]; exact hPeriodOnlyTerm
  -- guard の中身
  obtain ⟨wG, hChainG, -, -, -, hCycleG, hSymG⟩ := hGuard
  have hEqG : wG = wch := by rw [hMidChain] at hChainG; cases hChainG; rfl
  subst hEqG
  have hTerminal : singlePositive s1.cycle = true := by
    rw [hMidPeriodOnly, if_pos rfl] at hCycleG
    rw [← hMidCycle]; exact hCycleG
  have hPredict : GalilScaffoldInputHead.read (right s1.right) =
      GalilScaffoldChainConsume.symbol wG.machine.control.period.focus := by
    rw [← hMidRight, ← hSymG]
  -- `beginShiftVM'` の中身
  obtain ⟨wB, hBeginVM⟩ := hBegin
  have hEqB : wB = wG := by
    have := hBeginVM.1
    rw [hMidChain] at this; cases this; rfl
  subst hEqB
  have hBeginShift : beginShiftVM (periodLength wB) wB (afterMismatch s1 vs vq) s2 := by
    rw [← hTargetEq]; exact hBeginVM
  obtain ⟨-, hChainEntry, hCycleEntry⟩ := shiftEntry_shape hLeft hBeginShift
  have hChainTarget : s2.chain = ChainVM.watch (GalilScaffoldChainWatch.immediate wB) :=
    hChainEntry
  have hPeriodOnlyEntry : s2.periodOnly = true := by rw [hBeginVM.2]
  exact ⟨s₀, s1, s2, w₀, wB, GalilScaffoldChainWatch.immediate wB, n, 0, vs, vq,
    hOrigin, hChainStart, hBlockStart, hMatchedRun, hLagTerm, hPeriodOnlyEntry,
    hTerminal, hCanRight, hPredict, hRadiusTerm, hLengthTerm, hRight, hLeft,
    hBeginShift, .stop _ _ _, (shiftLens.set_get s2).symm, hChainTarget⟩

#print axioms shiftPhaseHistory_of_scanShift

/-! ## 結合 carrier

ラウンドは scan 相と shift 相を交互に通るので、carrier も mode で分岐する。
4 つの相遷移（`roundHistory_tick` / `shiftPhaseHistory_of_scanShift` /
`shiftPhaseHistory_tick` / `roundHistory_of_shiftDone`）を `Tick` の構成子で
振り分ければ tick 保存になる。

**`scan_fallback` と `restart` では carrier は原理的に保たれない**——そこで chain が
作り直されるので、新しいラウンドの `OriginAt` は
`GalilScaffoldTopFirstRound.first_round`（無条件）が出す。そこが基底。 -/

/-- **(NAMED) ラウンドの carrier。**  mode で分岐する。 -/
def RoundCarrier (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop :=
  (c.mode = Mode.scan → RoundHistory P q first delay w c s) ∧
  (c.mode = Mode.shift → ShiftPhaseHistory w s)

/-- **`H_readsShift` は carrier から出る。**  scan 相では guard（`mode = shift`）で空虚、
shift 相で `remaining` が尽きた点は `shiftPhaseHistory_readsShift`。

**これが目標**: `RoundCarrier` を run / trace の全点で持てれば
`obligation_shiftPalResidues*` の第 1 残差（`H_readsShift`）が公理から外れる。 -/
theorem h_readsShift_of_roundCarrier {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ}
    {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hCarrier : RoundCarrier P q first delay w c s) :
    PalPeg.CloseoutRoundUnique.H_readsShift w c s := by
  intro hMode hNotReplaying hPeriodOnly hExhausted
  exact shiftPhaseHistory_readsShift (hCarrier.2 hMode) hExhausted hMode hNotReplaying
    hPeriodOnly hExhausted

/-- **carrier の shift 半分だけを使う版。**  `OriginShift`（`CloseoutReadsOrigin:84`）と
同じ内容。 -/
theorem originShift_of_roundCarrier {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ}
    {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hCarrier : RoundCarrier P q first delay w c s) :
    PalPeg.CloseoutReadsOrigin.OriginShift w c s := by
  intro hMode _ _ hExhausted
  exact shiftPhaseHistory_originAt (hCarrier.2 hMode) hExhausted

#print axioms h_readsShift_of_roundCarrier
#print axioms originShift_of_roundCarrier

/-! ## tick の振り分けに要るデータ抽出

`scan` 相から `shift` 相へ行く tick は `scan_shift` だけ、`shift` 相から `scan` 相へ
行く tick は `shift_done` だけ。行き先の control（`GalilScaffoldTop:110-172`）を
一次情報で照合した:

| 構成子 | 行き先 mode |
|---|---|
| `scan_wait` / `scan_count` / `scan_match` / `restart` | source と同じ（scan） |
| `scan_shift` | `.shift` |
| `scan_fallback` | `.copy` |
| `shift_one` | source と同じ（shift） |
| `shift_done` | `.scan` |
 -/

/-- **scan → shift の tick は `scan_shift`。** -/
theorem scanShift_parts {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ}
    {x y : State GalilVM}
    (hTick : Tick (galilFrameS P q first) delay x y)
    (hSourceMode : x.ctl.mode = Mode.scan) (hTargetMode : y.ctl.mode = Mode.shift) :
    ∃ u : GalilVM, (galilFrameS P q first).compare x.vm u ∧
      ¬ (galilFrameS P q first).matched u ∧
      (galilFrameS P q first).shiftGuard u ∧
      (galilFrameS P q first).beginShift u y.vm := by
  cases hTick with
  | init c0 s0 s0' hm _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | scan_wait c0 s0 s0' hm _ _ => exact absurd (hSourceMode.symm.trans hTargetMode) (by decide)
  | scan_count c0 s0 s0' hm _ _ _ => exact absurd (hSourceMode.symm.trans hTargetMode) (by decide)
  | scan_match c0 s0 s0' s0'' o0 hm _ _ _ _ _ _ => exact absurd (hSourceMode.symm.trans hTargetMode) (by decide)
  | scan_shift c0 s0 s0' s0'' hm _ _ hcmp hmt _ hg hb => exact ⟨s0', hcmp, hmt, hg, hb⟩
  | scan_fallback c0 s0 s0' s0'' hm _ _ _ _ _ _ _ => simp at hTargetMode
  | shift_one c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | shift_done c0 s0 o0 hm hp _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | copy_one c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | copy_done c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | home_start c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | home_step c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | fpp_slice c0 s0 s0' hm _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | fpp_done c0 s0 s0' hm _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | markEnd_found c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | markEnd_step c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | choose_select c0 s0 s0' hm _ _ _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | choose_step c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | rewind_done c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | rewind_one c0 s0 s0' hm _ _ _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | rewind_pair c0 s0 s0' hm _ _ _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | replayStart c0 s0 s0' o0 hm _ _ _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | restart c0 s0 s0' hm _ => exact absurd (hSourceMode.symm.trans hTargetMode) (by decide)

/-- **shift → scan の tick は `shift_done`**（`remaining` が尽きていて VM は不変）。 -/
theorem shiftDone_parts {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ}
    {x y : State GalilVM}
    (hTick : Tick (galilFrameS P q first) delay x y)
    (hSourceMode : x.ctl.mode = Mode.shift) (hTargetMode : y.ctl.mode = Mode.scan) :
    ¬ (galilFrameS P q first).remainingPos x.vm ∧ y.vm = x.vm := by
  cases hTick with
  | init c0 s0 s0' hm _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | scan_wait c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | scan_count c0 s0 s0' hm _ _ _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | scan_match c0 s0 s0' s0'' o0 hm _ _ _ _ _ _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | scan_shift c0 s0 s0' s0'' hm _ _ hcmp hmt _ hg hb => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | scan_fallback c0 s0 s0' s0'' hm _ _ _ _ _ _ _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | shift_one c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hTargetMode) (by decide)
  | shift_done c0 s0 o0 hm hp _ => exact ⟨hp, rfl⟩
  | copy_one c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | copy_done c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | home_start c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | home_step c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | fpp_slice c0 s0 s0' hm _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | fpp_done c0 s0 s0' hm _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | markEnd_found c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | markEnd_step c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | choose_select c0 s0 s0' hm _ _ _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | choose_step c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | rewind_done c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | rewind_one c0 s0 s0' hm _ _ _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | rewind_pair c0 s0 s0' hm _ _ _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | replayStart c0 s0 s0' o0 hm _ _ _ => exact absurd (hm.symm.trans hSourceMode) (by decide)
  | restart c0 s0 s0' hm _ => exact absurd (hm.symm.trans hSourceMode) (by decide)

#print axioms scanShift_parts
#print axioms shiftDone_parts

/-- **carrier は scan / shift 相の 1 tick で保たれる。**

`Tick` の場合分けは `scanShift_parts` / `shiftDone_parts` に任せて、
4 遷移をそのまま呼ぶ。

**`scan_fallback` と `restart` は含まれない**（`hTargetMode` が scan / shift に限るので）。
そこでは chain が作り直されるので carrier は**原理的に**保たれず、
新しいラウンドの `OriginAt` は `GalilScaffoldTopFirstRound.first_round` が出す。 -/
theorem roundCarrier_tick {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ}
    {w : List (Fin 2)} {x y : State GalilVM}
    (hRestartNeedsBroken : ∀ u v : GalilVM, P.restart u v → ∃ wb, u.chain = ChainVM.broken wb)
    (hShiftGuardVM : ∀ u : GalilVM, (galilFrameS P q first).shiftGuard u → shiftGuardVM u)
    (hBeginShiftVM : ∀ u t : GalilVM,
      (galilFrameS P q first).beginShift u t → beginShiftVM' u t)
    (hCarrier : RoundCarrier P q first delay w x.ctl x.vm)
    (hSourceMode : x.ctl.mode = Mode.scan ∨ x.ctl.mode = Mode.shift)
    (hNotReplaying : x.ctl.mode = Mode.scan → x.ctl.replaying = false)
    (hCopyIdle : x.ctl.mode = Mode.shift → CopyIdle x.vm)
    (hContinuing : x.ctl.mode = Mode.scan → y.ctl.mode = Mode.scan →
      singlePositive x.vm.cycle = false)
    (hCanRightSource : x.ctl.mode = Mode.scan → y.ctl.mode = Mode.shift →
      canRight x.vm.right)
    (hWatchingTarget : x.ctl.mode = Mode.scan → y.ctl.mode = Mode.scan →
      ∃ wch, y.vm.chain = ChainVM.watch wch)
    (hTick : Tick (galilFrameS P q first) delay x y) :
    RoundCarrier P q first delay w y.ctl y.vm := by
  refine ⟨fun hTargetScan => ?_, fun hTargetShift => ?_⟩
  · rcases hSourceMode with hSource | hSource
    · obtain ⟨n, s₀, w₀, wch, -, -, -, -, -, hChainTerm, -, -, -, -, -⟩ :=
        onlyMatchedRun_of_roundHistory (hCarrier.1 hSource)
      exact roundHistory_tick hRestartNeedsBroken (hCarrier.1 hSource) hSource
        (hNotReplaying hSource) ⟨wch, hChainTerm⟩ (hContinuing hSource hTargetScan) hTick
        hTargetScan (hWatchingTarget hSource hTargetScan)
    · obtain ⟨hNotRemaining, hVmEq⟩ := shiftDone_parts hTick hSource hTargetScan
      have hExhausted : positive (shiftLens.get x.vm).shift.remaining = false := by
        by_contra hContra
        simp only [Bool.not_eq_false] at hContra
        exact hNotRemaining (Or.inl hContra)
      rw [hVmEq]
      exact roundHistory_of_shiftDone (hCarrier.2 hSource) hExhausted
  · rcases hSourceMode with hSource | hSource
    · obtain ⟨u, hCompare, hNotMatched, hGuard, hBegin⟩ :=
        scanShift_parts hTick hSource hTargetShift
      exact shiftPhaseHistory_of_scanShift (hCarrier.1 hSource) hCompare hNotMatched
        (hShiftGuardVM u hGuard) (hBeginShiftVM u y.vm hBegin)
        (hCanRightSource hSource hTargetShift)
    · exact shiftPhaseHistory_tick (hCarrier.2 hSource) hSource (hCopyIdle hSource) hTick
        hTargetShift

#print axioms roundCarrier_tick

/-- **carrier は run に沿って保たれる。**  側条件は区間の全点が
scan / shift 相 ∧ 非 replay ∧ `CopyIdle`、かつ scan 点では
周期が終端でない・右ヘッドが読める・chain が watch。 -/
theorem roundCarrier_of_steps {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ}
    {w : List (Fin 2)} {k : ℕ} {x y : State GalilVM}
    (hRestartNeedsBroken : ∀ u v : GalilVM, P.restart u v → ∃ wb, u.chain = ChainVM.broken wb)
    (hShiftGuardVM : ∀ u : GalilVM, (galilFrameS P q first).shiftGuard u → shiftGuardVM u)
    (hBeginShiftVM : ∀ u t : GalilVM,
      (galilFrameS P q first).beginShift u t → beginShiftVM' u t)
    (hSteps : Steps (galilFrameS P q first) delay k x y)
    (hCarrier : RoundCarrier P q first delay w x.ctl x.vm)
    (hSide : ∀ (m : ℕ) (z z' : State GalilVM),
      Steps (galilFrameS P q first) delay m x z →
      Tick (galilFrameS P q first) delay z z' →
      (z.ctl.mode = Mode.scan ∨ z.ctl.mode = Mode.shift) ∧
      (z.ctl.mode = Mode.scan → z.ctl.replaying = false) ∧
      (z.ctl.mode = Mode.shift → CopyIdle z.vm) ∧
      (z.ctl.mode = Mode.scan → z'.ctl.mode = Mode.scan →
        singlePositive z.vm.cycle = false) ∧
      (z.ctl.mode = Mode.scan → z'.ctl.mode = Mode.shift → canRight z.vm.right) ∧
      (z.ctl.mode = Mode.scan → z'.ctl.mode = Mode.scan →
        ∃ wch, z'.vm.chain = ChainVM.watch wch)) :
    RoundCarrier P q first delay w y.ctl y.vm := by
  induction hSteps with
  | zero u => exact hCarrier
  | @succ j u z t hTick hRest ih =>
    obtain ⟨hMode, hNotReplaying, hCopyIdle, hContinuing, hCanRight, hWatchingTarget⟩ :=
      hSide 0 u z (.zero u) hTick
    exact ih (roundCarrier_tick hRestartNeedsBroken hShiftGuardVM hBeginShiftVM hCarrier
        hMode hNotReplaying hCopyIdle hContinuing hCanRight hWatchingTarget hTick)
      (fun m' z' z'' hz' hz'' => hSide (m' + 1) z' z'' (.succ hTick hz') hz'')

/-- **`H_readsShift` を run の全点で**（`PROOF_STACK.md` 手順 1〜11 の結論）。 -/
theorem h_readsShift_alongSteps {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ}
    {w : List (Fin 2)} {k : ℕ} {x y : State GalilVM}
    (hRestartNeedsBroken : ∀ u v : GalilVM, P.restart u v → ∃ wb, u.chain = ChainVM.broken wb)
    (hShiftGuardVM : ∀ u : GalilVM, (galilFrameS P q first).shiftGuard u → shiftGuardVM u)
    (hBeginShiftVM : ∀ u t : GalilVM,
      (galilFrameS P q first).beginShift u t → beginShiftVM' u t)
    (hSteps : Steps (galilFrameS P q first) delay k x y)
    (hCarrier : RoundCarrier P q first delay w x.ctl x.vm)
    (hSide : ∀ (m : ℕ) (z z' : State GalilVM),
      Steps (galilFrameS P q first) delay m x z →
      Tick (galilFrameS P q first) delay z z' →
      (z.ctl.mode = Mode.scan ∨ z.ctl.mode = Mode.shift) ∧
      (z.ctl.mode = Mode.scan → z.ctl.replaying = false) ∧
      (z.ctl.mode = Mode.shift → CopyIdle z.vm) ∧
      (z.ctl.mode = Mode.scan → z'.ctl.mode = Mode.scan →
        singlePositive z.vm.cycle = false) ∧
      (z.ctl.mode = Mode.scan → z'.ctl.mode = Mode.shift → canRight z.vm.right) ∧
      (z.ctl.mode = Mode.scan → z'.ctl.mode = Mode.scan →
        ∃ wch, z'.vm.chain = ChainVM.watch wch)) :
    PalPeg.CloseoutRoundUnique.H_readsShift w y.ctl y.vm :=
  h_readsShift_of_roundCarrier
    (roundCarrier_of_steps hRestartNeedsBroken hShiftGuardVM hBeginShiftVM hSteps hCarrier hSide)

#print axioms roundCarrier_of_steps
#print axioms h_readsShift_alongSteps

/-! ## 基底の橋: 最初の shift 後の `OriginAt`

`GalilScaffoldTopFirstRound.first_round`（**無条件**）は最初の shift の行き先で
`∃ o, Entry raw o (toOnly e v) ∧ o.interior.length+1 = h ∧ …` を出す。
これを `OriginAt` にするには `periodLength v = h` が要る。3 段で出る:

* `chain_shift_periodLength`（shift 相、公理ゼロ）
* `GalilChainCoupling.periodLength_consume`（`immediate` 1 手、側条件 `WatchBlock`）
* `CloseoutWatchRound45.period_of_beginShift`（`beginShiftVM h w` と
  `beginShiftVM'` の `h` が一致する） -/

/-- **shift 後の watch の周期は shift の歩数。** -/
theorem periodLength_after_shift (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ) (raw : List (Fin 2))
    {h n : ℕ} {wch v : GalilScaffoldChainWatch.State} {s t : GalilVM}
    {shiftStart shiftEnd : ShiftState} {cyc fin : Counter}
    (hBegin : (PofC centre place entry raw).beginShift s t)
    (hBeginVM : beginShiftVM h wch s t)
    (hBlock : PalPeg.GalilBranchInvariants.WatchBlock wch)
    (hShiftRun : ChainShiftRun shiftStart (GalilScaffoldChainWatch.immediate wch) cyc n
      shiftEnd v fin) :
    periodLength v = h := by
  refine (chain_shift_periodLength hShiftRun).trans ?_
  refine (PalPeg.GalilChainCoupling.periodLength_consume wch.machine wch.lag wch.margin
    wch.lag (inc wch.margin) hBlock).trans ?_
  exact PalPeg.CloseoutWatchRound45.period_of_beginShift centre place entry raw hBegin hBeginVM

/-- **最初の shift 後の `OriginAt`**（`first_round` の `Entry` から）。 -/
theorem originAt_of_firstShiftEntry {w : List (Fin 2)} {o : ReadOrigin w} {h : ℕ}
    {v : GalilScaffoldChainWatch.State} {e : GalilVM}
    (hChain : e.chain = ChainVM.watch v)
    (hEntry : Entry w o (toOnly e v))
    (hInterior : o.interior.length + 1 = h)
    (hRoom : o.radius + 2 ≤ o.center)
    (hPeriod : periodLength v = h) :
    OriginAt w e :=
  PalPeg.CloseoutOriginRounds.originAt_of_entry hChain hEntry
    (hInterior.trans hPeriod.symm) hRoom

#print axioms periodLength_after_shift
#print axioms originAt_of_firstShiftEntry

#print axioms chainShiftRun_tick
#print axioms chainShiftRun_snoc
#print axioms chainShiftRun_snoc_shiftOne

#print axioms RoundHistory
#print axioms roundHistory_start
#print axioms roundHistory_tick
#print axioms roundHistory_of_steps
#print axioms onlyMatchedRun_of_roundHistory
#print axioms chain_shift_period
#print axioms chain_shift_periodLength

end PalPeg.RoundHistory
