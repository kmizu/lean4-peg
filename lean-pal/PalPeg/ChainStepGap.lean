import PalPeg.GalilChainTickable

/-!
# モデル欠陥 `M-watchBreak` — 正 lag の背景 consume に break が無い

## Scala 正本（`scala/pal/src/main/scala/pal/ScaffoldChain.scala`）

```scala
def step(answer: TapeView): Unit = {                      // 背景の 1 量子
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

def matched(): Unit = {                                   // 新しい place が合流
  margin.inc()
  if (periodOnly) cycle.dec()
  if (mode == Mode.Watch && lag.sign == 0) consume() else lag.inc()
}
```

`consume()` は **`step()`（正 lag）と `matched()`（lag ゼロ）の両方から呼ばれ、
どちらでも不一致なら `Mode.Broken` に落ちる。**

## Lean 側の現状

```
inductive Internal : State → State → Prop
  | idle (s) (hz : positive s.lag = false) : Internal s s
  | take (s) (hp : positive s.lag = true) (hg : Good s) : Internal s (caught s)

inductive ChainStep : ChainVM → ChainVM → Prop
  …
  | watchStep (w w') (ht : Internal w w') : ChainStep (.watch w) (.watch w')
  -- `.watch` から `.broken` への構成子が無い

inductive ChainMatched : ChainVM → ChainVM → Prop
  …
  | breaks (w w') (hb : BreakStep w w') : ChainMatched (.watch w) (.broken w')

def BreakStep (w w') : Prop :=
  zero w.lag = true ∧ canRight w.machine.verifier ∧ …   -- ← lag ゼロを要求
```

つまり **break は `matched()` 経路（lag ゼロ）だけモデル化されており、
`step()` 経路（正 lag）の break が欠けている。**

## 帰結（下の定理）

現行モデルでは、正の lag を持つ watch で period と入力が食い違っている状態に
**後続状態が存在しない**。Scala ではそこで `Broken` に落ちる。

これが `WatchOk` が偽である根本原因である（`PalPeg.WatchOkRefute.watchOk_false`）。
`ChainStep` が break できないため、正 lag での背景遷移は `Internal.take` しかなく、
それは `Good` を要求する。だから `WatchOk.good` は「正 lag では常に period と入力が
一致する」と主張することになり、それは Galil の chain の設計（予測が外れたら壊れる）
に反する。

## 直し方

`ChainStep` に正 lag 版の break を足す：

```
| watchBreak (w w') (hb : BreakStepPos w w') : ChainStep (.watch w) (.broken w')

def BreakStepPos (w w') : Prop :=
  positive w.lag = true ∧ canRight w.machine.verifier ∧
  ∃ a, symbol w.machine.control.period.focus = some a ∧
    read (right w.machine.verifier) ≠ some a ∧
    w' = ⟨consume w.machine, w.lag, w.margin⟩
```

`step()` は break 時に `lag.dec()` も `margin.inc()` もしない（`if (consume()) { lag.dec() }`、
`margin.inc()` は `matched()` 側）ので lag と margin は据え置き。

影響範囲: `ChainStep` / `ChainMatched` の構成子で分岐する箇所は 202。`M-periodOnly`
修正（300 超）と同規模の機械的作業。

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.ChainStepGap

open PalPeg PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilChainTickable
open GalilScaffoldCounter

/-- **欠陥の形式的な記述。** 正の lag を持ち、period と入力が食い違っている watch は、
現行の `ChainStep` では**行き先が無い**。Scala 正本ではそこで `Broken` に落ちる。 -/
theorem no_chainStep_at_positive_lag_mismatch {w : GalilScaffoldChainWatch.State}
    (hp : positive w.lag = true) (hng : ¬ GalilScaffoldChainWatch.Good w) :
    ¬ ∃ z, ChainStep (ChainVM.watch w) z := by
  rintro ⟨z, hz⟩
  cases hz with
  | watchStep w w' ht =>
    cases ht with
    | idle hzero => rw [hzero] at hp; cases hp
    | take _ hg => exact hng hg

/-- **同じことを `ChainTick` の背景側（`a = false`）で。** `ChainTick false x z` は
`ChainStep x z` に等しいので、背景量子でも行き先が無い。 -/
theorem no_chainTick_false_at_positive_lag_mismatch {w : GalilScaffoldChainWatch.State}
    (hp : positive w.lag = true) (hng : ¬ GalilScaffoldChainWatch.Good w) :
    ¬ ∃ z, ChainTick false (ChainVM.watch w) z := by
  rintro ⟨z, y, hstep, hzy⟩
  exact no_chainStep_at_positive_lag_mismatch hp hng ⟨y, hstep⟩

#print axioms no_chainStep_at_positive_lag_mismatch
#print axioms no_chainTick_false_at_positive_lag_mismatch

end PalPeg.ChainStepGap
