import PalPeg.CloseoutPackRun49

/-!
# `AuxPack` は boot では偽 — `lpackM3_steps` は boot 根では使えない

`GalilChainCoupling.AuxPack` は `FrontPack` を場に持ち、`FrontPack.notInit` は
`c.mode ≠ Mode.init` を言う。boot の制御は
`GalilScaffoldController.initial 2048 = ⟨.init, 2048, false, false, false, false⟩` なので
**`AuxPack (boot w).ctl (boot w).vm` は偽**。

帰結: `CloseoutPackRun49.lpackM3_steps` は

```
(hLv : ∀ i, i ≤ Tc w.length →
  LTickLeavesN … ∧ AuxPack (st i).ctl (st i).vm ∧ LTickLeaves2 … ∧ LTickLeaves3 …)
```

を取るが、`st 0 = boot w`（`PreTrace.start`）なので **`hLv 0` は充足不能**。
つまりこの定理は boot 根の trace には**適用できない**（偽の前提を要求しているのと同じで、
前進として数えられない）。`LPackM3` を運ぶなら

* 添字を `1 ≤ i` に制限する（`mode ≠ init` は `BranchSupply.
  mode_ne_init_alongTrace_afterFirstStep` で 1 手目以降は定理）、または
* `AuxPack` の場を mode で守る、または
* cycle 起点（`InvLPC` の scan 状態）から運ぶ（`packRunR_MW` が実際にやっていること）

のいずれかが必要。**`lpackM3_steps` をそのまま使う経路には乗らない。**

**無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**
-/

set_option autoImplicit false

namespace PalPeg.AuxPackNotAtBoot

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilChainCoupling
open PalPeg.CloseoutPackRun2 PalPeg.GalilFrontMono
open PalPeg.GalilFinalAssembly (boot)

/-- **`AuxPack` は boot では偽**（`FrontPack.notInit` と `initial` の mode が衝突）。 -/
theorem not_auxPack_at_boot (w : List (Fin 2)) :
    ¬ AuxPack (boot w).ctl (boot w).vm :=
  fun hAuxPack => hAuxPack.front.notInit rfl

/-- **`lpackM3_steps` の `hLv` は boot 根では充足不能。** -/
theorem lpackM3_steps_input_unsatisfiable_at_boot
    {w : List (Fin 2)} {st : ℕ → State GalilVM} (hStart : st 0 = boot w) :
    ¬ AuxPack (st 0).ctl (st 0).vm := by
  rw [hStart]; exact not_auxPack_at_boot w

#print axioms not_auxPack_at_boot
#print axioms lpackM3_steps_input_unsatisfiable_at_boot

end PalPeg.AuxPackNotAtBoot
