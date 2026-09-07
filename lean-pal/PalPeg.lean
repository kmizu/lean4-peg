import PalPeg.Basic
import PalPeg.Existence
import PalPeg.EvenLength
import PalPeg.Axioms
import PalPeg.Words
import PalPeg.Chain

/-!
# PalPeg

回文言語 `PAL ⊆ {0,1}*` が PEG 言語であることを、Kim–Park の Lean 成果物
(`PegSeparation`) を経由して**条件付きで**証明する。

* `PalPeg.Basic`     — `PAL` の定義と反転不変性
* `PalPeg.Existence` — 厳密実時間 TM が `PAL` を認識するならば total PEG が `PAL` を認識する
* `PalPeg.EvenLength` — 偶数長への制限（Loff–Moreira–Reis Conjecture 7 の条件付き反駁）
* `PalPeg.Axioms`    — `#print axioms` の guard
* `PalPeg.Words`     — 回文と周期の組合せ論（拡張則・境界・Fine–Wilf・group 補題）
* `PalPeg.Chain`     — 接尾辞回文鎖のオンライン参照算法と `w ∈ PAL ↔ |w| ∈ chain w`
-/
