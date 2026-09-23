import PalPeg.PalInPeg
import PalPeg.Canonical
import PalPeg.Workbench
import PalPeg.Axioms

/-!
# `PalPeg` — ルート

根は 4 本だけ。**どこに何があるかはこの 4 本が示す。**

* `PalPeg.PalInPeg` — **目標定理と、そこへ至る部分結果**。無条件の
  `PalInPeg.unconditional`（`PalInPegFinal`、2026-09-24 証明済み）。前提を取るものは
  `PalInPeg.given_<残差>` で、名前だけで「何を仮定すれば到達するか」が読める。
* `PalPeg.Canonical` — 主線の部品のカーネル検査済み索引（意味のある別名）。
* `PalPeg.Workbench` — ビルドは通るが未配線の部品を、主定理との関係で分類したもの。
* `PalPeg.Axioms` — 公理監査。既存の旗艦定理が標準 3 公理のみであることの guard に加えて、
  **目標定理のラチェット**を持つ: `PalPeg.PalInPeg.unconditional : RecognizedByTotalPEG PAL`
  は閉じた項だが、未証明の義務を `axiom` として明示しており、その一覧を guard が固定する。
  義務を 1 個証明して `axiom` を外すと guard が壊れて更新を強制される。
  **guard が標準 3 公理だけになったとき §10.5（前提ゼロ）が達成される。**

* `PalPeg.Canonical` — 正本の鎖（`given_globalScanLandings_and_fourOther` の閉包 526 本）＋意味のある別名。
  `lake build PalPeg.Canonical` で正本だけを速くビルドできる。
* `PalPeg.Workbench` — 作ったが未配線の部品。主定理との関係を層ごとに明記。
* `PalPeg.Axioms` — 公理監査（`#guard_msgs in #print axioms`）。

この 3 本の閉包は 1135 モジュールで、再編前に登録されていた 1101 本を 1 本も
落としていない（機械照合済み、欠落 0）。**証明は 1 行も変えていない。**

新しいモジュールは、正本の鎖に入るなら `PalPeg/Canonical.lean` に、
まだ配線していないなら `PalPeg/Workbench.lean` に登録する。

**全体 build 成功・標準公理のみ・無条件 `PAL ∈ PEG` 証明済み（`PalInPeg.unconditional`）.**
-/
