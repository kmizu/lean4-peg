import PalPeg.GalilPeriodUnion
import PalPeg.GalilPeriodCentre

/-!
# 連鎖の終端比較における周期の全域化

Galil 型の実時間回文照合では、連鎖（chain）の終端で

* 現在の回文 `PalAt x C k`（区間 `[C - k, C + k]`、`2h ≤ k`）
* 次の回文 `PalAt x (C + h) (k + 1 - h)`（区間 `[C + 2h - k - 1, C + k + 1]`）
* 照合器が読んだ右側の `2h` 周期性 `PeriodOn x (2h) (C + 1) (C + k + 1)`

の 3 つが揃う。このとき区間 `[C - k, C + k + 1]` 全体が `2h` 周期になる。

証明は 3 つの場合分けだけで済む。

* `C + 1 ≤ j` — 仮定 `hright` そのもの。
* `j = C` — 次の回文 `h1` に半径 `h` を入れると `x[C]? = x[C + 2h]?`。
* `j < C` — 2 回の鏡映で済む。まず中心 `C` の回文で `x[j]? = x[2C - j]?`、
  次に中心 `C + h` の回文で `x[2C - j]? = x[j + 2h]?`
  （`2C - j` と `j + 2h` は和が `2(C + h)` なので `C + h` について対称）。
  `2h ≤ k` から `2C - j` は必ず `h1` の区間に入る。
-/

set_option autoImplicit false
namespace PalPeg
open Manacher

variable {α : Type}

/-- **終端比較での周期の全域化**。現在の回文 `PalAt x C k`、次の回文
`PalAt x (C + h) (k + 1 - h)`、右側の `2h` 周期性が揃えば、区間
`[C - k, C + k + 1]` の全体で `2h` が周期になる。 -/
theorem periodOn_span_of_next {x : List α} {C k h : ℕ} (hh : 0 < h) (hk : 2*h ≤ k)
    (h0 : PalAt x C k) (h1 : PalAt x (C + h) (k + 1 - h))
    (hright : PeriodOn x (2*h) (C + 1) (C + k + 1)) :
    PeriodOn x (2*h) (C - k) (C + k + 1) := by
  have hkC : k ≤ C := h0.1
  have hlen : C + k < x.length := h0.2.1
  have hrad1 : k + 1 - h ≤ C + h := h1.1
  -- 中心の 1 歩：次の回文に半径 `h` を入れる（`h ≤ k + 1 - h` は `2h ≤ k` から）。
  have key : x[C]? = x[C + 2*h]? := by
    have hstep := h1.2.2 h (by omega)
    rw [show C + h - h = C from by omega, show C + h + h = C + 2*h from by omega] at hstep
    exact hstep
  -- 右側の周期区間を中心 `C` まで 1 歩だけ左へ伸ばす。
  have hR : PeriodOn x (2*h) C (C + k + 1) := by
    intro i hi hib
    rcases Nat.eq_or_lt_of_le hi with hEq | hLt
    · rw [← hEq]; exact key
    · exact hright i (by omega) hib
  intro j hj hjb
  rcases Nat.lt_or_ge j C with hjC | hjC
  · -- 左半分：中心 `C` の鏡映 → 中心 `C + h` の鏡映。
    have hm1 : x[j]? = x[2*C - j]? := mirror_getElem? h0 (by omega) (by omega)
    have hm2 : x[2*C - j]? = x[2*(C + h) - (2*C - j)]? :=
      mirror_getElem? h1 (by omega) (by omega)
    rw [show 2*(C + h) - (2*C - j) = j + 2*h from by omega] at hm2
    rw [hm1, hm2]
  · exact hR j hjC hjb

/-- `periodOn_span_of_next` を区間 `[C - k, C + k]` に制限して、切り出した
スパン `(x.drop (C - k)).take (2k + 1)` の `HasPeriod` に変換した形。 -/
theorem hasPeriod_span_of_next {x : List α} {C k h : ℕ} (hh : 0 < h) (hk : 2*h ≤ k)
    (h0 : PalAt x C k) (h1 : PalAt x (C + h) (k + 1 - h))
    (hright : PeriodOn x (2*h) (C + 1) (C + k + 1)) :
    HasPeriod ((x.drop (C - k)).take (2*k+1)) (2*h) := by
  have hkC : k ≤ C := h0.1
  have hlen : C + k < x.length := h0.2.1
  have hper : PeriodOn x (2*h) (C - k) (C + k) :=
    (periodOn_span_of_next hh hk h0 h1 hright).mono (le_refl (C - k)) (by omega)
  rw [show 2*k+1 = (C + k) + 1 - (C - k) from by omega]
  exact (hasPeriod_slice_iff (x := x) (p := 2*h) hlen (by omega)).mpr hper

#print axioms periodOn_span_of_next
#print axioms hasPeriod_span_of_next

end PalPeg
