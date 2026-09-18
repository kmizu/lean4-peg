import PalPeg.GalilChainTickable

/-!
# 背景 consume の break — モデル欠陥 `M-watchBreak` の修正とその成果

## 何が欠けていたか（2026-09-19 に発見）

Scala 正本 `scala/pal/src/main/scala/pal/ScaffoldChain.scala:136,178`:

```scala
def step(answer: TapeView): Unit = {                    // 背景の 1 量子
  mode match {
    case Mode.Copy  => stepCopy(answer)
    case Mode.Back  => stepBack()
    case Mode.Watch if lag.sign > 0 => if (consume()) { lag.dec() }   // ← ここ
    case Mode.Idle | Mode.Watch | Mode.Broken => ()
  }
}
private def consume(): Boolean = {
  verifier.right()
  val token = period.read()
  if (!verifier.read().contains(token.takeRight(1))) { mode = Mode.Broken; false }
  else { distance.inc(); …; period.move(direction); true }
}
def matched(): Unit = {                                 // 新しい place が合流
  margin.inc(); if (periodOnly) cycle.dec()
  if (mode == Mode.Watch && lag.sign == 0) consume() else lag.inc()
}
```

`consume()` は **`step()`（正 lag）と `matched()`（lag ゼロ）の両方から呼ばれ、
どちらでも不一致なら `Mode.Broken` に落ちる。**

Lean 側は `ChainMatched.breaks`（`BreakStep`、`zero w.lag = true` を要求）で
**lag ゼロ経路だけ**をモデル化しており、`ChainStep` には `.watch → .broken` が無かった。
その結果「正 lag で period と入力が食い違う watch に後続状態が存在しない」という
穴があり、それを埋めるために `WatchOk.good`（正 lag では必ず `Good`、すなわち
**予測は常に当たる**）という偽の仮定が書かれていた
（反証: `PalPeg.WatchOkRefute.watchOk_false`）。
Galil の chain は予測が外れたら壊れる設計で、周期区間の終端検出はまさにその break で
行うので、`WatchOk.good` は設計に正面から反していた。

## 何を入れたか

* `BreakStepPos`（`GalilScaffoldTopChainVM`）— 正 lag 版の break。
  `step()` は break 時に `lag.dec()` も `margin.inc()` もしない
  （`if (consume()) { lag.dec() }`、`margin.inc()` は `matched()` 側）ので
  行き先は `⟨consume machine, lag, margin⟩`。
* `ChainStep.watchBreak (hb : BreakStepPos w w') : ChainStep (.watch w) (.broken w')`
* `ChainMatched.brokenMatched (w) : ChainMatched (.broken w)
  (.broken ⟨w.machine, inc w.lag, inc w.margin⟩)` — `matched()` は mode に関係なく
  `margin.inc()` と `lag.inc()` をする（こちらも欠けていた）。

## 成果

`GalilScaffoldChainInputSupply.chainStep_watch_total_of_symbol` が
**`Good` を仮定せずに**後続状態の存在を与える。必要なのは「verifier が右に動ける」と
「period の焦点が記号を持つ」だけ。これが `ChainTickable`／`hready` の解錠にあたる。

## 修正で偽になったもの（記録）

* `GalilScaffoldTopWatchRun.broken_stays` は `z = .broken w`（状態まで同一）と
  主張していた。`brokenMatched` によりカウンタが動くので
  `∃ w', z = .broken w'` に弱めた。
* `CloseoutTickFalse.step_ne_broken`（「`ChainOk` な chain からの `ChainStep` は
  `.broken` に行かない」）は**偽**になったのでファイルごと削除した。同ファイルの
  `chainOk_tick_false` は `WatchOk` を仮定していたので反証により空虚だった。
* 本ファイルの前身 `ChainStepGap.no_chainStep_at_positive_lag_mismatch`
  （「正 lag ＋ 不一致に後続が無い」）は欠陥の記述だったので、修正により偽になった。
  下の定理がその置き換えである。

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.ChainBackgroundBreak

open PalPeg PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilChainTickable
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier

/-- **修正後の挙動。** 正の lag で period の焦点記号が入力と食い違うとき、背景量子は
chain を壊す（Scala の `consume()` が `false` を返して `mode = Mode.Broken` にするのと同じ）。
lag も margin も動かない。 -/
theorem watchBreak_at_positive_lag_mismatch {w : GalilScaffoldChainWatch.State} {a : Fin 3}
    (hp : positive w.lag = true)
    (hcan : GalilScaffoldChainVerifier.canRight w.machine.verifier)
    (ha : GalilScaffoldChainConsume.symbol w.machine.control.period.focus = some a)
    (hne : GalilScaffoldInputHead.read (right w.machine.verifier) ≠ some a) :
    ChainStep (ChainVM.watch w)
      (ChainVM.broken ⟨GalilScaffoldChainVerifier.consume w.machine, w.lag, w.margin⟩) :=
  .watchBreak _ _ ⟨hp, hcan, a, ha, hne, rfl⟩

/-- **穴は閉じた。** 背景量子（`a = false`）でも後続状態が存在する。必要なのは
`canRight` と period の焦点が記号を持つことだけで、**予測が当たること（`Good`）は要らない**。 -/
theorem chainTick_false_total {w : GalilScaffoldChainWatch.State}
    (hcan : GalilScaffoldChainVerifier.canRight w.machine.verifier)
    (hsym : ∃ a : Fin 3,
      GalilScaffoldChainConsume.symbol w.machine.control.period.focus = some a) :
    ∃ z, ChainTick false (ChainVM.watch w) z := by
  obtain ⟨y, hy⟩ := chainStep_watch_total_of_symbol w hcan hsym
  exact ⟨y, y, hy, rfl⟩

#print axioms watchBreak_at_positive_lag_mismatch
#print axioms chainTick_false_total

end PalPeg.ChainBackgroundBreak
