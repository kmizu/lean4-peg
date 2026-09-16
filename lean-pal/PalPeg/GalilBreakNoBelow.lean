import PalPeg.GalilPeriodNext
import PalPeg.GalilBreakPeriod

/-!
# 周期破れの後は「下に周期なし」が保たれる

`PalPeg.GalilPeriodNext.noBelow_next` の "chain round をまたぐ最小性の引き継ぎ" と
`PalPeg.GalilBreakPeriod.no_period_of_break` の "1 点の不一致は区間周期を否定する"
を組み合わせる、純粋な語の組合せ論の小補題。

`NoBelow` という名前の定義は `GalilPeriodNext.lean` には存在せず、そこでも
（`noBelow_next` の仮定 `hmin0` のように）`∀ p, 0 < p → p < 2 * h → ¬ PeriodOn x p a b`
という形でインラインに書かれている。ここでもその形をそのまま踏襲する。

* `noBelow_after_break` — 旧区間 `[a, b0]` に `p` 未満の周期が無く、それを
  `b0 ≤ b` へ延ばした新区間 `[a, b]` で周期 `p` そのものが破れているなら、
  新区間には `p` 以下の周期がまったく無い。
-/

set_option autoImplicit false
namespace PalPeg

/-- After a period break: if the span up to `b0` had no period below `p`, and the extended
span up to `b ≥ b0` fails to have period `p`, then it has no period `≤ p` at all.

証明：`q ≤ p` の周期の候補を区間 `[a, b0]` へ制限する（`PeriodOn.mono`／
`periodOn_restrict`）。`q < p` なら `hNB` に矛盾。`q = p` なら仮定
`hbreak`（区間 `[a, b]` 上で周期 `p` が成り立たない）にそのまま矛盾する。 -/
theorem noBelow_after_break {x : List (Fin 3)} {p a b0 b : ℕ}
    (hNB : ∀ q, 0 < q → q < p → ¬ PeriodOn x q a b0) (hb : b0 ≤ b)
    (hbreak : ¬ PeriodOn x p a b) : ∀ q, 0 < q → q ≤ p → ¬ PeriodOn x q a b := by
  intro q hq0 hqp hper
  rcases lt_or_eq_of_le hqp with hlt | heq
  · exact hNB q hq0 hlt (periodOn_restrict hper (le_refl a) hb)
  · subst heq
    exact hbreak hper

/-- **周期破れの具体形との合成**。`GalilBreakPeriod.no_period_of_break` が与える
1 点不一致から `hbreak` を直接組み立てる版。新区間 `[a, b]` 上の位置 `j` で
`x[j]? ≠ x[j + p]?`（`a ≤ j`, `j + p ≤ b`）が成り立てば、それだけで
`noBelow_after_break` の結論が得られる。 -/
theorem noBelow_after_break_of_mismatch {x : List (Fin 3)} {p a b0 b j : ℕ}
    (hNB : ∀ q, 0 < q → q < p → ¬ PeriodOn x q a b0) (hb : b0 ≤ b)
    (hj : a ≤ j) (hjb : j + p ≤ b) (hne : x[j]? ≠ x[j + p]?) :
    ∀ q, 0 < q → q ≤ p → ¬ PeriodOn x q a b :=
  noBelow_after_break hNB hb (GalilBreakPeriod.no_period_of_break hj hjb hne)

#print axioms noBelow_after_break
#print axioms noBelow_after_break_of_mismatch

end PalPeg
