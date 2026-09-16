import PalPeg.GalilScaffoldTimingCost
import PalPeg.LocalBuffers
import PalPeg.GalilSegmentCount

/-!
# `LocalBudget`：局所化された背景ジョブが「次に必要になる時刻」までに終わること

`PalPeg.LocalBuffers` は非局所的な一括リセットを局所化した。その代償として
二つの背景ジョブが走る。

* **遊休プログラム束の消去**：幅 `W` の束を 1 ティック 1 セルで消す。
  `LocalBuffers.clearTick_done` により `W + 1` ティックで完了する。
* **切り離したカウンタ鏡の再構築**：値 `v ≤ radius` の鏡を 1 ティック 1 マークで
  組み直す。`v + c` ティックかかる（`c` は段取り分）。

本ファイルはこの二つが「次に結果が必要になる時刻」までに終わることを、
既存の時間予算から純算術として切り出す。窓の長さの出所は

* 段（stage）の窓 `8 * max k 1`、段の上限ティック数 `63 * (8 * max k 1)`
  — `GalilScaffoldTimingCost.first_stage_ticks` / `GalilScaffoldStagePrepare`
  （`ht : es.length ≤ 63*(8*max r 1)`）、
* 場所クロック `delay = 2048`（1 比較 / 2048 ティック）
  — `GalilScaffoldTimingCost.delay_calibration`、
* 段の障壁 `2 * max k 1` — `GalilLedgerObligations.stage_meets_barrier` の `2*r`。

最後の節で `delay` の side を機械側から取る：`galilFrameS` の走行のうち
モードが `.scan` の区間では、クロックを `1` から `delay` へ張り直すティック
（`scan_match` / `scan_shift` / `scan_fallback`、および `clock = 1` で撃った
`restart`）以外は `radius` を動かさない。そしてクロックは 1 ティックに高々 1 しか
減らないので、`clock = delay` から始まる長さ `n ≤ delay` の走行には張り直しが
高々 1 回しか入らない（`n + 1 ≤ delay` なら 0 回）。これが
「2048 ティックの窓で radius は高々 1 回しか変わらない」の中身である。
-/

set_option autoImplicit false

namespace PalPeg
namespace LocalBudget

/-! ## 1. 遊休プログラム束の消去が段に収まること -/

/-- **消去は段に収まる。**  遊休側の各テープの仕事量が段の窓 `8 * max k 1` に
定数 `c` を足した範囲なら、`LocalBuffers.clearTick_done` が要求する `W + 1`
ティックは段の上限ティック数 `63 * (8 * max k 1)` に収まる。
`c ≤ 495` は `8 + 495 + 1 ≤ 504` から来る余裕であり、`max k 1 ≥ 1` だけを使う。 -/
theorem clear_fits_stage (k W c : ℕ) (hW : W ≤ 8 * max k 1 + c) (hc : c + 1 ≤ 496) :
    W + 1 ≤ 63 * (8 * max k 1) := by
  have hm : 1 ≤ max k 1 := le_max_right _ _
  omega

/-- 同じことを `GalilScaffoldTimingCost.first_stage_ticks` の左辺と並べた形：
段の実コスト（grow + 準備 + 較正済み run 予算）と消去ジョブの両方が
`63 * (8 * max k 1)` に収まる。 -/
theorem clear_and_stage_fit (k W c m : ℕ) (hW : W ≤ 8 * max k 1 + c) (hc : c + 1 ≤ 496)
    (hm : m ≤ 8 * max k 1 + 1) :
    W + 1 ≤ 63 * (8 * max k 1) ∧
      max k 1 + 2 * k + 2 * m + 7 + GalilScaffoldTimingCost.runBudget (8 * max k 1)
        ≤ 63 * (8 * max k 1) :=
  ⟨clear_fits_stage k W c hW hc, GalilScaffoldTimingCost.first_stage_ticks k m hm⟩

/-- **消去は場所クロックの 1 周期に収まる。**  比較は `delay = 2048` ティックに
1 回しか起きない（`delay_calibration`）。リセット直後に立てたジョブは `W + 1`
ティックで終わるので、`W ≤ 2046` なら次の比較より前に遊休側は空白に戻る。 -/
theorem clear_fits_place_clock (W : ℕ) (hW : W ≤ 2046) : W + 1 ≤ 2047 := by omega

/-- `LocalBuffers.clearTick_done` と場所クロックの窓を合わせた実用形：
幅 `W ≤ 2046` の遊休束は、次の比較（`2048` ティック後）より前に完全に空白になる。 -/
theorem clear_done_within_place {n : ℕ} {x : LocalBuffers.Buffered n} {W : ℕ}
    (hj : x.job.isSome) (hWb : ∀ i, LocalBuffers.size (LocalBuffers.idle x i) ≤ W)
    (hW : W ≤ 2046) :
    (∀ i, LocalBuffers.Cleared (LocalBuffers.idle (LocalBuffers.clearTickN (W + 1) x) i)) ∧
      W + 1 ≤ 2047 :=
  ⟨LocalBuffers.clearTick_done hj hWb, clear_fits_place_clock W hW⟩

/-! ## 2. 切り離したカウンタ鏡の再構築 -/

/-- 汎用形：値 `v ≤ rad` の鏡を 1 ティック 1 マークで組み直し、段取りに `c`
ティックかかるとき、窓 `D` に収まる条件は `rad + c ≤ D`。 -/
theorem counter_rebuild_fits (v rad c D : ℕ) (hv : v ≤ rad) (hc : rad + c ≤ D) : v + c ≤ D := by
  omega

/-- **段の窓での再構築（使える形）。**  段の障壁は `2 * max k 1`
（`GalilLedgerObligations.stage_meets_barrier` の `2*r`）なので、そこまでに
書き戻される鏡の値は `rad ≤ 2 * max k 1`。段の窓は `8 * max k 1` あるから、
段取り `c ≤ 6 * max k 1` なら再構築は段の中で終わる。 -/
theorem counter_rebuild_fits_stage (k v rad c : ℕ) (hv : v ≤ rad) (hrad : rad ≤ 2 * max k 1)
    (hc : c ≤ 6 * max k 1) : v + c ≤ 8 * max k 1 := by
  omega

/-- **`lag` / `margin` の「次の使用」＝ `.back` への遷移。**
チェーン検証器の `lag` / `margin` は `.copy` 相では書き換えられるだけで読まれず、
最初に参照されるのは `.back` に入ったあと。`GalilBranchInvariants.copy_run` は
`.copy` から `.back` までがちょうど `n + 1 ≥ h + 1` チェーンステップであることを
与えるので、窓は `h + 1` ティック。

**ギャップ**：この窓に収めるには `rad + c ≤ h` が要るが、既存の補題が与えるのは
`GalilLedgerObligations.verifier_catchup` の `lag0 ≤ 2*h + 2` だけで、
`rad ≤ h` は出てこない。したがって `hrad` はここで名指しする唯一の機械側仮定であり、
これが取れないなら `lag` / `margin` の鏡は `.copy` 相をまたいで切り離せない
（段の窓 `counter_rebuild_fits_stage` まで待つ必要がある）。 -/
theorem counter_rebuild_fits_copy (v rad h c : ℕ) (hv : v ≤ rad) (hrad : rad + c ≤ h) :
    v + c ≤ h + 1 := by
  omega

/-- `verifier_catchup` が実際に与える値の上界 `2*h + 2` では `.copy` 相の窓
`h + 1` に入らない（`h ≥ 1`、段取り `c ≥ 1` のとき）。上の `hrad` が本当に
新しい仮定であることの確認。 -/
theorem copy_window_too_short (h c : ℕ) (hh : 1 ≤ h) (hc : 1 ≤ c) :
    h + 1 < (2 * h + 2) + c := by omega

/-- **`work` には背景再構築の窓がない。**  `GalilScaffoldPrepareControl.Tick` は
`lower` / `copy` の各ティックで `work` を読んで `dec`／`inc` する。つまり次の使用は
「次の 1 ティック」であり、窓は `D = 1`。段取りに 1 ティックでもかかるなら、
収まるのは値 `0` の鏡だけ ―― すなわち `work` は背景で組み直せず、
`LocalBuffers` と同じ O(1) の二重化で持つしかない。 -/
theorem work_rebuild_needs_attached (v c : ℕ) (hfit : v + c ≤ 1) (hc : 1 ≤ c) : v = 0 := by
  omega

end LocalBudget
end PalPeg

/-! ## 3. 機械側：2048 ティックの窓で radius は高々 1 回しか変わらない -/

namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController

/-- クロックは 1 ティックで高々 1 しか減らない（張り直しは `delay` へ上げるだけ）。 -/
theorem tick_clock_succ {σ : Type} (F : Frame σ) (delay : ℕ) {x y : State σ}
    (h : Tick F delay x y) (hb : Bounded delay x.ctl) : x.ctl.clock ≤ y.ctl.clock + 1 := by
  unfold Bounded at hb
  cases h <;> dsimp only at hb ⊢ <;> omega

/-- `.scan` モードの走行で、クロックの張り直し（`1 → delay`）を `k` 回含む長さ `n`
のもの。張り直しティックはちょうど比較ティック `scan_match` / `scan_shift` /
`scan_fallback`（と `clock = 1` で撃った `restart`）であり、`radius` を動かしうる
のはこれだけである。 -/
inductive ScanReload (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) :
    ℕ → ℕ → Control → GalilVM → Control → GalilVM → Prop
  | stop (c : Control) (s : GalilVM) : ScanReload P q first delay 0 0 c s c s
  | reload {n k : ℕ} {c c1 c' : Control} {s s1 t : GalilVM}
      (h : Tick (galilFrameS P q first) delay ⟨c, s⟩ ⟨c1, s1⟩) (hm : c.mode = .scan)
      (hr : c.clock = 1 ∧ c1.clock = delay)
      (hs : ScanReload P q first delay n k c1 s1 c' t) :
      ScanReload P q first delay (n + 1) (k + 1) c s c' t
  | plain {n k : ℕ} {c c1 c' : Control} {s s1 t : GalilVM}
      (h : Tick (galilFrameS P q first) delay ⟨c, s⟩ ⟨c1, s1⟩) (hm : c.mode = .scan)
      (hr : ¬ (c.clock = 1 ∧ c1.clock = delay))
      (hs : ScanReload P q first delay n k c1 s1 c' t) :
      ScanReload P q first delay (n + 1) k c s c' t

/-- `ScanReload` は本物の走行である。 -/
theorem scanReload_steps (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {n k : ℕ}
    {c c' : Control} {s t : GalilVM} (h : ScanReload P q first delay n k c s c' t) :
    Steps (galilFrameS P q first) delay n ⟨c, s⟩ ⟨c', t⟩ := by
  induction h with
  | stop c s => exact .zero _
  | reload h _ _ _ ih => exact .succ h ih
  | plain h _ _ _ ih => exact .succ h ih

theorem scanReload_zero_len (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {k : ℕ}
    {c c' : Control} {s t : GalilVM} (h : ScanReload P q first delay 0 k c s c' t) : k = 0 := by
  cases h; rfl

/-- **張り直しは長さ `< clock` の窓には入らない。**  クロックは 1 ティックに高々 1
しか減らず、張り直しは `clock = 1` を要求する。 -/
theorem scanReload_eq_zero (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {n k : ℕ}
    {c c' : Control} {s t : GalilVM} (h : ScanReload P q first delay n k c s c' t) :
    Bounded delay c → n + 1 ≤ c.clock → k = 0 := by
  induction h with
  | stop c s => intro _ _; rfl
  | reload h hm hr hs ih =>
    intro hb hn
    exfalso
    have h1 := hr.1
    omega
  | plain h hm hr hs ih =>
    intro hb hn
    have hstep := tick_clock_succ (galilFrameS P q first) delay h hb
    have hb' := tick_bounded (galilFrameS P q first) delay h hb
    dsimp only at hstep hb' ⊢
    exact ih hb' (by omega)

/-- **窓が `clock` 以下なら張り直しは高々 1 回。**  1 回起きた時点で残りの長さは
`0` である。 -/
theorem scanReload_le_one (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {n k : ℕ}
    {c c' : Control} {s t : GalilVM} (h : ScanReload P q first delay n k c s c' t) :
    Bounded delay c → n ≤ c.clock → k ≤ 1 := by
  induction h with
  | stop c s => intro _ _; omega
  | reload h hm hr hs ih =>
    intro hb hn
    have h1 := hr.1
    have h2 := hr.2
    have hb1 := tick_bounded (galilFrameS P q first) delay h hb
    unfold Bounded at hb
    have hk := scanReload_eq_zero P q first delay hs hb1 (by omega)
    omega
  | plain h hm hr hs ih =>
    intro hb hn
    have hstep := tick_clock_succ (galilFrameS P q first) delay h hb
    have hb' := tick_bounded (galilFrameS P q first) delay h hb
    dsimp only at hstep hb' ⊢
    exact ih hb' (by omega)

/-- `.scan` の 1 ティックが張り直しでないなら `radius` は動かない。
`scan_wait` / `scan_count` は `backgroundS`（`backgroundS_fields` が
`s'.radius = s.radius` を与える）、比較三種は `clock = 1 → delay` なので除外、
`restart` は `clock ≠ 1` の場合のみ残り、そこは `P.restart` が `radius` を
触らないという唯一の機械側仮定 `hres` で閉じる。 -/
theorem scan_tick_radius (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (hres : ∀ u u' : GalilVM, P.restart u u' → u'.radius = u.radius)
    {c c' : Control} {s t : GalilVM}
    (h : Tick (galilFrameS P q first) delay ⟨c, s⟩ ⟨c', t⟩) (hm : c.mode = .scan)
    (hr : ¬ (c.clock = 1 ∧ c'.clock = delay)) : t.radius = s.radius := by
  cases h
  case scan_wait => exact (backgroundS_fields P q first ‹(galilFrameS P q first).background s t›).2.2.2.2.2.1
  case scan_count => exact (backgroundS_fields P q first ‹(galilFrameS P q first).background s t›).2.2.2.2.2.1
  case scan_match => exact absurd ⟨‹c.clock = 1›, rfl⟩ hr
  case scan_shift => exact absurd ⟨‹c.clock = 1›, rfl⟩ hr
  case scan_fallback => exact absurd ⟨‹c.clock = 1›, rfl⟩ hr
  case restart => exact hres _ _ ‹(galilFrameS P q first).restart s t›
  all_goals (exfalso; simp_all)

/-- **張り直しが 0 回なら `radius` は一定。** -/
theorem scanReload_radius (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (hres : ∀ u u' : GalilVM, P.restart u u' → u'.radius = u.radius) {n k : ℕ}
    {c c' : Control} {s t : GalilVM} (h : ScanReload P q first delay n k c s c' t) :
    k = 0 → t.radius = s.radius := by
  induction h with
  | stop c s => intro _; rfl
  | reload h hm hr hs ih => intro hk; exact absurd hk (by omega)
  | plain h hm hr hs ih =>
    intro hk
    rw [ih hk]
    exact scan_tick_radius P q first delay hres h hm hr

/-! ### `delay = 2048` での具体形 -/

/-- **`radius_changes_slowly`（本題）。**  場所クロック `delay = 2048` で
`clock = 2048` から始まる長さ `n ≤ 2048` の `.scan` 走行には、クロックの張り直し
＝比較ティックが高々 1 回しか入らない。`radius` は比較ティックでしか変わらないので、
2048 ティックの窓で `radius` は高々 1 回しか変わらない。 -/
theorem radius_changes_slowly (P : Shared) (q : ℕ) (first : Fin 9) {n k : ℕ}
    {c c' : Control} {s t : GalilVM} (h : ScanReload P q first 2048 n k c s c' t)
    (hc : c.clock = 2048) (hn : n ≤ 2048) : k ≤ 1 :=
  scanReload_le_one P q first 2048 h (by unfold Bounded; omega) (by omega)

/-- 窓を 1 ティック短くすると張り直しは 0 回になり、`radius` はその間まったく
動かない。背景ジョブ（遊休束の消去・カウンタ鏡の再構築）が
`clear_fits_place_clock` の `2047` ティックに収まる理由がこれである。 -/
theorem radius_stable_within_place (P : Shared) (q : ℕ) (first : Fin 9)
    (hres : ∀ u u' : GalilVM, P.restart u u' → u'.radius = u.radius) {n k : ℕ}
    {c c' : Control} {s t : GalilVM} (h : ScanReload P q first 2048 n k c s c' t)
    (hc : c.clock = 2048) (hn : n ≤ 2047) : k = 0 ∧ t.radius = s.radius := by
  have hk : k = 0 := scanReload_eq_zero P q first 2048 h (by unfold Bounded; omega) (by omega)
  exact ⟨hk, scanReload_radius P q first 2048 hres h hk⟩

end PalPeg.GalilScaffoldChainInputSupply

#print axioms PalPeg.LocalBudget.clear_fits_stage
#print axioms PalPeg.LocalBudget.clear_and_stage_fit
#print axioms PalPeg.LocalBudget.clear_fits_place_clock
#print axioms PalPeg.LocalBudget.clear_done_within_place
#print axioms PalPeg.LocalBudget.counter_rebuild_fits
#print axioms PalPeg.LocalBudget.counter_rebuild_fits_stage
#print axioms PalPeg.LocalBudget.counter_rebuild_fits_copy
#print axioms PalPeg.LocalBudget.copy_window_too_short
#print axioms PalPeg.LocalBudget.work_rebuild_needs_attached
#print axioms PalPeg.GalilScaffoldChainInputSupply.tick_clock_succ
#print axioms PalPeg.GalilScaffoldChainInputSupply.scanReload_steps
#print axioms PalPeg.GalilScaffoldChainInputSupply.scanReload_zero_len
#print axioms PalPeg.GalilScaffoldChainInputSupply.scanReload_eq_zero
#print axioms PalPeg.GalilScaffoldChainInputSupply.scanReload_le_one
#print axioms PalPeg.GalilScaffoldChainInputSupply.scan_tick_radius
#print axioms PalPeg.GalilScaffoldChainInputSupply.scanReload_radius
#print axioms PalPeg.GalilScaffoldChainInputSupply.radius_changes_slowly
#print axioms PalPeg.GalilScaffoldChainInputSupply.radius_stable_within_place
