import PalPeg.CloseoutReadyStage

/-!
# `.run` 相では `RunEntriesS` が縮む — `PostRun` を整礎帰納に置き換える第一歩

`CloseoutPreload8.PostRun`

    PostRun := ∀ v as, v.search.mode = .run → DpSafeStage v as → RunEntriesS as v

には **producer が無い**。理由は n187 で割れた: **`∀ v as` が run にも供給条件にも
縛られていない**（消費者 `CloseoutPreload11.StagePrep2` は
`PacedL 2048 0 (bs ++ as)` と `D + dpEvents (m+1) ≤ bs.length + as.length` を持っているのに、
`PostRun` の文はどちらも落としている）。短さで落ちることは既に機械検査済み
（`CloseoutPreload3.not_runEntriesS_eight`、節タイトル
「`RestartEntryS` is false: the paced list may be too short」）。

`runEntriesS_of_stageInv2`（`CloseoutPreload11:296`）が `PostRun` を必要とするのは、
`as` への帰納が **`.run` 入口で縮まない**から: その枝で `hpost v' as hr hsafe` を
同じ `as` に対して使っている。

**しかし `.run` 相でもイベントは消費される。** `RunEntryS` は源の mode が `.run` でない
ことを要求するので、`.run` 相の各手では**空虚**。下の補題はそれを 1 手ぶん切り出したもので、
`RunEntriesS` の帰納を 1 つ縮める原子になる。

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.PostRunInduction

open PalPeg PalPeg.CloseoutReadyStage
open PalPeg.GalilScaffoldSearchFinish (Mode)
open PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop

/-- **`.run` 相の 1 手で `RunEntriesS` は残りに帰着する。**

`RunEntryS center a v v' as := searchStep … → v.search.mode ≠ .run → … → DpSafeStage v' as`
の第 2 仮説が源の mode を `.run` でないと要求するので、源が `.run` なら空虚。
残るのは行き先での `RunEntriesS as v'` だけ。

**これが `PostRun` を整礎帰納に置き換えるための原子**: `.run` 相を歩くあいだ
`as` が 1 つずつ縮む。 -/
theorem runEntriesS_cons_of_run {v : SearchVM} {a : Bool} {as : List Bool}
    (hm : v.search.mode = Mode.run)
    (hnext : ∀ (center : GalilScaffoldPlace.Place) (v' : SearchVM),
      searchStep center a v v' → RunEntriesS as v') :
    RunEntriesS (a :: as) v :=
  fun center v' hs => ⟨fun _ hne _ => absurd hm hne, hnext center v' hs⟩

#print axioms runEntriesS_cons_of_run

end PalPeg.PostRunInduction
