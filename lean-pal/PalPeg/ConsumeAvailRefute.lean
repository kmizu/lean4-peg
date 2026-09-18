import PalPeg.CloseoutPackRun41
import PalPeg.WatchOkRefute

/-!
# `ConsumeAvail` を全状態に量化した前提は偽 — `final31` の `hav`

## 経緯

`CloseoutFinalS2.given_consumeAvailEverywhere_FALSE_HYP` は `H_fourOther` を落とすかわりに

```
(hav : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (i : ℕ),
    ConsumeAvail (st i).vm.chain)
```

を取る。`st` は**無制約な関数**なので、この前提は `∀ z : ChainVM, ConsumeAvail z` と
同値であり、run 上の事実ではない。過剰量化の典型（`over-quantified-named-leaves` の
8 例目）。

## 反証

`ConsumeAvail z := ∀ wch, z = .watch wch → canRight (right wch.machine.verifier)`。
`right p = ⟨if p.gap then headRight p.head else p.head, !p.gap⟩` は gap を反転するので、
`gap = false` で右スタックも incoming も空な verifier では
`canRight (right p) = (true = false) ∨ ([] ≠ []) ∨ ([] ≠ [])` が偽になる。
証人は `GalilWatchOkInst.bornVer = ⟨⟨some 0, [], [], []⟩, false⟩`。

（`bornVer_can : canRight bornVer` は成り立つ——`gap = false` なので第 1 選言。
偽になるのは**一歩進めた後**の `canRight (right bornVer)` である。）

## 帰結

* `given_consumeAvailEverywhere_FALSE_HYP` は偽の前提を取る。**8 → 9 でも 8 → 8 でもなく、無価値。**
  `final36` / `final37` の `hpack` も偽（`CloseoutPackRefute.hpack_false`）なので、
  正直な最上位は依然 `given_globalScanLandings_and_fourOther`（8 前提・反証済みゼロ）。
* 正しい経路は `CloseoutWatchSupply.watchShiftS_of_supply`（`ConsumeAvail` を 4 つの
  局所供給事実に分解）→ `CloseoutVerSide.VerRun`（**run 形**）。

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.ConsumeAvailRefute

open PalPeg PalPeg.GalilWatchOkInst PalPeg.WatchOkRefute
open PalPeg.CloseoutPackRun41 PalPeg.GalilFinalAssembly
open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilScaffoldTop
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier

/-- 右へ一歩も進めない verifier を持つ watch 状態。 -/
def stuckWatch : GalilScaffoldChainWatch.State :=
  ⟨⟨bornVer, watchControl bornBlock⟩, posLag, reset⟩

/-- `bornVer` は `canRight` だが、一歩進めた先は `canRight` でない。 -/
theorem not_canRight_right_bornVer :
    ¬ GalilScaffoldChainVerifier.canRight (GalilScaffoldChainVerifier.right bornVer) := by
  rintro (h | h | h)
  · exact absurd h (by decide)
  · exact h rfl
  · exact h rfl

theorem not_consumeAvail_stuckWatch : ¬ ConsumeAvail (ChainVM.watch stuckWatch) :=
  fun h => not_canRight_right_bornVer (h stuckWatch rfl)

/-- **`ConsumeAvail` は全 chain 状態では成り立たない。** -/
theorem consumeAvail_not_universal : ¬ ∀ z : ChainVM, ConsumeAvail z :=
  fun h => not_consumeAvail_stuckWatch (h _)

/-- **`given_consumeAvailEverywhere_FALSE_HYP` の `hav` は偽**（`st` が無制約なので状態への全称と同値）。 -/
theorem hav_false :
    ¬ ∀ (_w : List (Fin 2)) (st : ℕ → GalilScaffoldTop.State GalilVM) (i : ℕ),
      ConsumeAvail (st i).vm.chain := by
  intro h
  exact not_consumeAvail_stuckWatch
    (h [] (fun _ => ⟨(boot []).ctl,
      { (boot []).vm with chain := ChainVM.watch stuckWatch }⟩) 0)

#print axioms not_canRight_right_bornVer
#print axioms not_consumeAvail_stuckWatch
#print axioms consumeAvail_not_universal
#print axioms hav_false

end PalPeg.ConsumeAvailRefute
