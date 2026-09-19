import PalPeg.GalilWatchOkInst

/-!
# `WatchOk` は偽 — `born` の任意 lag と `good` の一致要求が衝突する

## 経緯（証明を試みて詰まり、障害が偽の形だったので反証に回った）

`GalilReplayChainSeg.ChainTickable` を `ChainOk` 上に載せ替えるには `WatchOk Ok` の
インスタンスが要る。構成を試みたところ `born` で詰まった：

```
born : ∀ (ver : PlaceHead) (v : Period.Tape) (lag margin : Counter),
    canRight ver → OnBlock v → Ok ⟨⟨ver, watchControl v⟩, lag, margin⟩
```

**`lag` と `margin` が任意に量化されている。** これは `ChainOk` の設計が強制している：

```
| .back v _ _ _ ver => OnBlock v ∧ canRight ver      -- lag/margin を無視
```

`ChainStep.backDone` は `.back v h lag margin ver` から
`.watch ⟨⟨ver, watchControl v⟩, lag, margin⟩` へ遷移し lag/margin を継承するので、
`ChainOk` が `.back` の lag/margin を無視する限り、閉性には任意 lag/margin での `Ok` が要る。

一方 `good` は正の lag で `Good` を要求し、

```
Good s := canRight s.machine.verifier ∧
  ∃ a, symbol s.machine.control.period.focus = some a ∧ read (right s.machine.verifier) = some a
```

は **period テープの焦点記号と入力右ヘッドの記号の一致**を要求する。`born` の仮説
（`canRight ver` と `OnBlock v`）はその 2 つを一切関係づけない。よって lag を正に取れば
不一致な `(ver, v)` で矛盾する。

## 証人（カーネル計算、`#eval` で確認済み）

`GalilWatchOkInst` の証人をそのまま使う：

* `bornVer = ⟨⟨some 0, [], [], []⟩, false⟩`、`bornVer_can : canRight bornVer`
* `bornBlock = ⟨[], .first 0, [.last 0]⟩`、`bornBlock_onBlock : OnBlock bornBlock`
* `symbol (moveRight bornBlock).focus = some 0`
* `read (right bornVer) = some 2`

lag は `⟨[0], []⟩`（`positive = true`）。

## 既存の反証との違い

`GalilWatchOkInst.no_watchOk_instance` は `WatchOk Ok` に**加えて**無条件の
`∀ w, Ok w → Good w` を仮定した組を否定する（`born` は `lag = reset` で使う）。
本ファイルは lag を正に取ることで `WatchOk.good` だけを使い、**`WatchOk` 単体**を否定する。

## 帰結

`ChainTickable` を `ChainOk`＋`WatchOk` 上に載せ替える道は閉じた。`hready` を消すには
**`ChainOk` を `.copy`/`.back` で lag/margin を縛る形に再設計し、誕生義務を `.back` の場
として持たせる**必要がある（そうすれば `born` は `WatchOk` の場でなくなる）。

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.WatchOkRefute

open PalPeg PalPeg.GalilWatchOkInst PalPeg.GalilChainTickable
open PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier

/-- 正の lag。 -/
def posLag : Counter := ⟨[0], []⟩

theorem posLag_positive : positive posLag = true := by decide

/-- **`WatchOk` は充足不能。** `born` が任意 lag で `Ok` を与え、`good` がその正 lag で
`Good`（period と入力の一致）を強制するが、`born` の仮説は両者を関係づけない。 -/
theorem watchOk_false {Ok : WState → Prop} (hOk : WatchOk Ok) : False := by
  obtain ⟨-, a, ha1, ha2⟩ :=
    hOk.good ⟨⟨bornVer, watchControl bornBlock⟩, posLag, reset⟩
      (hOk.born bornVer bornBlock posLag reset bornVer_can bornBlock_onBlock)
      posLag_positive
  have h0 : (0 : Fin 3) = a := by
    have : (some (0 : Fin 3)) = some a := ha1
    exact Option.some.inj this
  have h2 : (2 : Fin 3) = a := by
    have : (some (2 : Fin 3)) = some a := ha2
    exact Option.some.inj this
  rw [← h0] at h2
  exact absurd h2 (by decide)

/-- **`WatchOk` のインスタンスは存在しない。** -/
theorem no_watchOk : ¬ ∃ Ok : WState → Prop, WatchOk Ok :=
  fun ⟨_, hOk⟩ => watchOk_false hOk

#print axioms posLag_positive
#print axioms watchOk_false
#print axioms no_watchOk

end PalPeg.WatchOkRefute
