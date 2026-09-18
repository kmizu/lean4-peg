import PalPeg.CloseoutRunEntriesPaced
import PalPeg.GalilSegmentConstructB

/-!
# `ReadyFuel` は restart 直後の探索で偽（`StageEntryC.fuel` の切り直しを強制する）

`CloseoutContracts.StageEntryC` の 2 つ目の場は

    fuel : ReadyFuel (searchLens.get r) (headRank r.right * 2048 + c.clock) (headRank r.right)

`GalilSegmentConstructB.ReadyFuel v n K := ∀ as, n ≤ as.length → as.count true ≤ K →
SearchReadyB v as` を展開すると `.run` 入口の債務が以後のマッチを**全部**払うことを要求する
（`SearchReadyB` → `RunEntriesAll` → `GalilSearchReadyInv.RunEntry` → `DpSafeRem`、
`DpSafeRem` の第 4 節が `((bs ++ as).count true : ℤ) ≤ value s0.debt`）。

`CloseoutRunEntriesPaced` が確定させた通り、restart 直後の探索は 8 イベントで `.run` に入り
そのときの債務は **2**。`headRank` は `2 * (右の残り) + …`（`GalilLeafEnds:66`）で入力長に
比例するので、`K = headRank r.right` は容易に 3 を超える。

**証人は `CloseoutRunEntriesPaced` のものをそのまま使う**（`v0` / `paced_shape` /
`step1`〜`step8` / `p8_debt` / `rest_count`）。新しい証人は作っていない。

**帰結**: `StageEntryC` は切り直しが要る。正しい通貨は `CloseoutReadyStage.RunEntriesS`
（`DpSafeStage` で stage の終わりで切った版）で、`CloseoutPreload11.runEntriesS_of_restartS2`
が既にそれを出している。

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.ReadyFuelRefute

open PalPeg PalPeg.CloseoutRunEntriesPaced
open PalPeg.GalilScaffoldAdvanceClock (advances)

/-- `CloseoutRunEntriesPaced` の paced イベント列。 -/
def paced : List Bool := advances 2048 2048 (av.map (fun b => (b, true)))

/-- **`ReadyFuel` は restart 直後の探索 `v0` で偽。**

`K` を `paced` 自身のマッチ数に取るので数え上げは要らない（`le_rfl`）。
`GalilSegmentConstructB.readyFuel_mono` は `K' ≤ K` で弱くなる向きなので
**これより大きい `K` でも偽**。 -/
theorem not_readyFuel_v0 (n : ℕ) (hn : n ≤ paced.length) :
    ¬ PalPeg.GalilSegmentConstructB.ReadyFuel v0 n (paced.count true) := by
  intro hfuel
  have h0 := (hfuel paced hn le_rfl).2
  rw [show paced = false :: false :: false :: false :: false :: false :: false :: false :: rest
      from paced_shape] at h0
  have h1 := (h0 ctr (w p1) step1).2
  have h2 := (h1 ctr (w p2) step2).2
  have h3 := (h2 ctr (w p3) step3).2
  have h4 := (h3 ctr (w p4) step4).2
  have h5 := (h4 ctr (w p5) step5).2
  have h6 := (h5 ctr (w p6) step6).2
  have h7 := (h6 ctr (w p7) step7).2
  have h8 := (h7 ctr (w p8) step8).1
  have hdp : PalPeg.GalilSearchReadyInv.DpSafeRem (w p8) rest := h8 step8 p7_not_run p8_run
  have hcnt := PalPeg.CloseoutReadinessAudit.dpSafeRem_count_le hdp
  rw [p8_debt] at hcnt
  have hrest := rest_count
  omega

#print axioms not_readyFuel_v0

end PalPeg.ReadyFuelRefute
