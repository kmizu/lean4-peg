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

起点側の 4 つ（`OriginAt` / `periodOnly = true` / watch / lag ゼロ）は
`GalilScaffoldTopRoundS.round_next` と `CloseoutOriginRounds.originAt_of_rounds` が
要求するものとちょうど同じ。 -/
def RoundHistory (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop :=
  ∃ (n : ℕ) (c₀ : Control) (s₀ : GalilVM) (w₀ : GalilScaffoldChainWatch.State),
    ScanSeg P q first delay n c₀ s₀ c s ∧
    OriginAt w s₀ ∧ s₀.periodOnly = true ∧
    s₀.chain = ChainVM.watch w₀ ∧ zero w₀.lag = true

section
variable {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ} {w : List (Fin 2)}

/-- **ラウンド起点そのものは `RoundHistory`。**  区間が空（`ScanSeg.stop`）。 -/
theorem roundHistory_start {c₀ : Control} {s₀ : GalilVM}
    {w₀ : GalilScaffoldChainWatch.State}
    (hOrigin : OriginAt w s₀) (hPeriodOnly : s₀.periodOnly = true)
    (hChain : s₀.chain = ChainVM.watch w₀) (hLagZero : zero w₀.lag = true) :
    RoundHistory P q first delay w c₀ s₀ :=
  ⟨0, c₀, s₀, w₀, ScanSeg.stop c₀ s₀, hOrigin, hPeriodOnly, hChain, hLagZero⟩

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
  obtain ⟨n, c₀, s₀, w₀, hSeg, hOrigin, hPeriodOnly, hChain, hLagZero⟩ := hHistory
  rcases scanSeg_snoc_tick hRestartNeedsBroken hSeg hScan hNotReplaying hWatching
      hContinuing hTick with ⟨m, hNext⟩ | hLeft | hBroke
  · exact ⟨m, c₀, s₀, w₀, hNext, hOrigin, hPeriodOnly, hChain, hLagZero⟩
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
      s.periodOnly = true ∧ OnlyMatchedRun (toOnly s₀ w₀) n (toOnly s wch) := by
  obtain ⟨n, c₀, s₀, w₀, hSeg, hOrigin, hPeriodOnly, hChain, hLagZero⟩ := hHistory
  obtain ⟨wch, hwch, hzch, hpoch, hrun⟩ :=
    scanSeg_only P q first delay hSeg w₀ hPeriodOnly hChain hLagZero
  exact ⟨n, s₀, w₀, wch, hOrigin, hPeriodOnly, hChain, hLagZero, hwch, hzch, hpoch, hrun⟩

end

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
