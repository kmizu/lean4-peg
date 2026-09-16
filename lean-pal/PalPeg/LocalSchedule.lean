import PalPeg.LocalBudget
import PalPeg.LocalBuffers
import PalPeg.LocalMirror
import PalPeg.LocalInputView
import PalPeg.LocalTick2

/-!
# `LocalSchedule`：局所化層の背景ジョブに締切を与える

`LocalTick2` §9 が残した締切義務（deadline obligations）を、ジョブごとに
「コスト ≤ 次に結果が必要になるまでのティック数」の形で明示的に与える。

ジョブは 4 本。

1. **DP 束の消去**（`commitRestart` / `commitReplay` の `resetL` で起動、
   次の `resetL` までに `Cleared` が要る）。
2. **fpp 束の消去**（`commitFallback` の `resetL` で起動、次の fallback まで）。
3. **半径鏡の再構築**（`LocalMirror.take` の後、次の `take` まで）。
4. **ヘッドの再配置**（`replayStartVM` の `right := center`）。

1〜3 は既存の予算（段 `63 * (8 * max k 1)` ティック、場所クロック `2048`
ティック）に素直に収まる。**4 は収まらない。** §5 でその帳尻を正確に計算し、
歩いて追いつく方式が不可能であること（半径が `2049` を超えると最初の比較に
間に合わない）を証明する。§6 が代替案 —— カーソルを「役割の張り替え」で
O(1) に差し替える view 版 `LocalRoles` —— を定式化し、現在の
`LocalState.ViewLocal` ではその差し替えが**表現できない**ことも証明する
（`no_local_jump`）。

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false

namespace PalPeg.LocalSchedule

open PalPeg.LocalInputView (InputView WF cells pos absRight absHead)

/-! ## 0. 二つの窓 -/

/-- 段の窓（比較の予算）：`GalilLedgerObligations.stage_meets_barrier` の `2*r`。 -/
def barrier (k : ℕ) : ℕ := 2 * max k 1

/-- 段の窓（セル数）：`8 * max k 1`。 -/
def stageWindow (k : ℕ) : ℕ := 8 * max k 1

/-- 段の上限ティック数：`GalilScaffoldTimingCost.first_stage_ticks` の右辺。 -/
def stageTicks (k : ℕ) : ℕ := 63 * (8 * max k 1)

/-- 場所クロック：`GalilScaffoldTimingCost.delay_calibration`。 -/
def delay : ℕ := 2048

theorem one_le_max (k : ℕ) : 1 ≤ max k 1 := le_max_right _ _

theorem barrier_le_stageWindow (k : ℕ) : barrier k ≤ stageWindow k := by
  unfold barrier stageWindow; have := one_le_max k; omega

/-! ## 1. 消去ジョブの持続性

`LocalBuffers.clearTick_done` は「`W + 1` ティックちょうど」で `Cleared` を
与える。締切に使うにはそれ以降も `Cleared` のままであることが要る。 -/

theorem clearN_of_cleared (m : ℕ) {t : GalilScaffoldTape.Tape}
    (h : LocalBuffers.Cleared t) : LocalBuffers.Cleared (LocalBuffers.clearN m t) := by
  induction m generalizing t with
  | zero => exact h
  | succ m ih =>
      refine ih ?_
      unfold LocalBuffers.Cleared at h ⊢
      rw [h, LocalBuffers.clearStep_reset]

theorem clearTickN_add {n : ℕ} (a b : ℕ) (x : LocalBuffers.Buffered n) :
    LocalBuffers.clearTickN (a + b) x
      = LocalBuffers.clearTickN b (LocalBuffers.clearTickN a x) := by
  induction a generalizing x with
  | zero => rw [Nat.zero_add]; rfl
  | succ a ih =>
      have h : a + 1 + b = (a + b) + 1 := by omega
      rw [h, LocalBuffers.clearTickN, LocalBuffers.clearTickN, ih (LocalBuffers.clearTick x)]

theorem job_clearTickN {n : ℕ} (m : ℕ) {x : LocalBuffers.Buffered n}
    (h : x.job.isSome) : (LocalBuffers.clearTickN m x).job.isSome := by
  induction m generalizing x with
  | zero => exact h
  | succ m ih => exact ih (LocalBuffers.job_clearTick h)

/-- **消去は締切以降ずっと有効。**  幅 `W` の遊休束は `W + 1` ティックで空白に
なり、そのあと何ティック待っても空白のままである。 -/
theorem cleared_at_deadline {n : ℕ} {x : LocalBuffers.Buffered n} {W D : ℕ}
    (hj : x.job.isSome)
    (hW : ∀ i, LocalBuffers.size (LocalBuffers.idle x i) ≤ W) (hD : W + 1 ≤ D) :
    ∀ i, LocalBuffers.Cleared (LocalBuffers.idle (LocalBuffers.clearTickN D x) i) := by
  intro i
  obtain ⟨m, hm⟩ : ∃ m, D = (W + 1) + m := ⟨D - (W + 1), by omega⟩
  subst hm
  rw [clearTickN_add, LocalBuffers.idle_clearTickN m (job_clearTickN (W + 1) hj)]
  exact clearN_of_cleared m (LocalBuffers.clearTick_done hj hW i)

/-! ## 2. ジョブ 1：DP 束の消去

`commitRestart` / `commitReplay` はどちらも `dpBuf` に `resetL` を撃つ。
結果（`RestartStaged.clean` / `abs_commitReplay` の `hclean`）が次に要るのは
**次の** `resetL` の瞬間であり、リセットは段に高々 1 回しか起きない
（`GalilScaffoldTimingCost.first_stage_ticks` の段構造）。よって窓は
`stageTicks k`。幅は DP 機械の走査域、すなわち段の窓 `8 * max k 1` ＋定数。 -/

/-- DP 束の消去コストは段に収まる（`LocalBudget.clear_fits_stage` の別名）。 -/
theorem dp_clear_cost (k W c : ℕ) (hW : W ≤ stageWindow k + c) (hc : c + 1 ≤ 496) :
    W + 1 ≤ stageTicks k :=
  LocalBudget.clear_fits_stage k W c hW hc

/-- **ジョブ 1 のスケジュール。**  `hnext` が「次のリセットは 1 段以上あと」、
`hW` が幅の上界。結論は、次のリセットの瞬間 `D` に遊休側が `Cleared` であること
——これが `LocalTick2.abs_commitRestart` / `abs_commitReplay` の
`hclean` である。 -/
theorem dp_clear_scheduled {n : ℕ} {x : LocalBuffers.Buffered n} {k W c D : ℕ}
    (hj : x.job.isSome)
    (hWb : ∀ i, LocalBuffers.size (LocalBuffers.idle x i) ≤ W)
    (hW : W ≤ stageWindow k + c) (hc : c + 1 ≤ 496)
    (hnext : stageTicks k ≤ D) :
    ∀ i, LocalBuffers.Cleared (LocalBuffers.idle (LocalBuffers.clearTickN D x) i) :=
  cleared_at_deadline hj hWb (le_trans (dp_clear_cost k W c hW hc) hnext)

/-! ## 3. ジョブ 2：fpp 束の消去

`commitFallback` は `fppBuf` に `resetL` を撃つ。fpp 機械の走査域は fallback
の窓 `ℓ + 1 ≤ 2 * R + 2`（`R` はその時点の半径）。締切は次の fallback。

* **段の窓なら収まる**（`fpp_clear_fits_stage`）：段の障壁で `R ≤ 2 * max k 1`。
* **場所クロック 1 周期（2047 ティック）には一般には収まらない**
  （`fpp_clear_place_fails`）：`R ≥ 1023` で破れる。

したがって「fallback は 1 場所以上あける」では足りず、「fallback は 1 段以上
あける」が要る。これが名前つき仮定 `hnext` の中身。 -/

theorem fpp_clear_fits_stage (k R : ℕ) (hR : R ≤ barrier k) : (2 * R + 2) + 1 ≤ stageTicks k := by
  unfold barrier stageTicks at *
  have := one_le_max k
  omega

theorem fpp_clear_fits_place (R : ℕ) (hR : R ≤ 1022) : (2 * R + 2) + 1 ≤ 2047 := by omega

/-- **場所クロックでは足りない。**  半径が `1023` 以上なら、fallback の窓を
消すジョブは次の比較（`delay = 2048` ティック後）に間に合わない。 -/
theorem fpp_clear_place_fails (R : ℕ) (hR : 1023 ≤ R) : ¬ ((2 * R + 2) + 1 ≤ 2047) := by omega

/-- **ジョブ 2 のスケジュール。**  `hnext` ＝「次の fallback は 1 段以上あと」。 -/
theorem fpp_clear_scheduled {n : ℕ} {x : LocalBuffers.Buffered n} {k R D : ℕ}
    (hj : x.job.isSome)
    (hWb : ∀ i, LocalBuffers.size (LocalBuffers.idle x i) ≤ 2 * R + 2)
    (hR : R ≤ barrier k) (hnext : stageTicks k ≤ D) :
    ∀ i, LocalBuffers.Cleared (LocalBuffers.idle (LocalBuffers.clearTickN D x) i) :=
  cleared_at_deadline hj hWb (le_trans (fpp_clear_fits_stage k R hR) hnext)

/-! ## 4. ジョブ 3：鏡の再構築

`LocalMirror.take` は鏡を 1 本外す。外した枠は `LocalMirror.rebuild_done` に
より `v` ティック（`v` は復元する値）で埋まる。半径鏡の次の `take` は次の
`chainStart` / `initialDebt`、すなわち 1 段あと。段の障壁で `v ≤ R ≤ 2 * max k 1`
だから、段の窓に余裕で収まる。 -/

theorem mirror_rebuild_cost (k v R : ℕ) (hv : v ≤ R) (hR : R ≤ barrier k) : v ≤ stageTicks k := by
  unfold barrier stageTicks at *
  have := one_le_max k
  omega

/-- **ジョブ 3 のスケジュール。**  復元された枠は `SegCtr` の形をしており
（`LocalMirror.shaped_attach` が要求する不変量そのもの）、そのコスト `v` は
次の `take` までの窓 `D` に収まる。 -/
theorem mirror_rebuild_scheduled {r : LocalMirror.Rebuild} {v k R D : ℕ}
    (h : LocalMirror.RebuildInv r v) (hp : r.pending = v)
    (hv : v ≤ R) (hR : R ≤ barrier k) (hnext : stageTicks k ≤ D) :
    LocalCounter.SegCtr (LocalMirror.rebuildRun v r).spare v ∧ v ≤ D :=
  ⟨(LocalMirror.rebuild_done h hp).1, le_trans (mirror_rebuild_cost k v R hv hR) hnext⟩

/-! ## 5. ジョブ 4：ヘッドの再配置 —— 締切に**間に合わない**

`replayStartVM` は `right := center` を要求する。`LocalTick2` はこれを
`repRight` の再配置ジョブに落とし、`repRight_reaches` が
`repDist (pos right) (pos center)` ティックで到達することを与える。
問題はその `repDist` が半径 `R` そのものだということ。

replay 側の需要は場所クロックに従う：`i` 番目の replay 比較は
ティック `i * delay` に起き、そのときヘッドは場所 `centre + i` に居ないと
いけない。ジョブは frontier `centre + R` から 1 ティック 1 セルで左へ歩く
ので、ティック `t` での位置は `centre + (R - t)`。

以下はその帳尻の**正確な**計算である。 -/

/-- 左へ歩く再配置ジョブの、`t` ティック後の位置（目標 `tgt`、開始は `tgt + R`）。 -/
def walkPos (tgt R t : ℕ) : ℕ := max tgt (tgt + R - t)

/-- `i` 番目の replay 比較が要求する場所。 -/
def demand (tgt i : ℕ) : ℕ := tgt + i

/-- `i` 番目の replay 比較が起きるティック。 -/
def cmpTick (i : ℕ) : ℕ := i * delay

/-- ジョブが `i` 番目の比較に間に合っている（＝需要より右に取り残されていない）。 -/
def KeepsAhead (tgt R i : ℕ) : Prop := walkPos tgt R (cmpTick i) ≤ demand tgt i

theorem walkPos_zero (tgt R : ℕ) : walkPos tgt R 0 = tgt + R := by
  unfold walkPos; omega

theorem walkPos_done (tgt R t : ℕ) (h : R ≤ t) : walkPos tgt R t = tgt := by
  unfold walkPos; omega

/-- **帳尻の正体。**  `i` 番目の比較に間に合う条件はちょうど `R ≤ i * 2049`。 -/
theorem keepsAhead_iff (tgt R i : ℕ) : KeepsAhead tgt R i ↔ R ≤ i * 2049 := by
  unfold KeepsAhead walkPos demand cmpTick delay
  rw [Nat.max_le]
  omega

/-- **`i = 0` は不可能。**  最初の比較がティック `0` に起きるなら、ジョブは
`R = 0` のときしか間に合わない（＝再配置が要らないとき）。 -/
theorem keepsAhead_zero_iff (tgt R : ℕ) : KeepsAhead tgt R 0 ↔ R = 0 := by
  rw [keepsAhead_iff]; omega

/-- **最初の比較が `i₀` 番目なら、条件は `R ≤ i₀ * 2049` ちょうど。**
（`i ≥ i₀` の全需要を同時に満たす条件でもある。） -/
theorem walk_schedule_iff (tgt R i₀ : ℕ) :
    (∀ i, i₀ ≤ i → KeepsAhead tgt R i) ↔ R ≤ i₀ * 2049 := by
  constructor
  · intro h
    exact (keepsAhead_iff tgt R i₀).mp (h i₀ le_rfl)
  · intro h i hi
    rw [keepsAhead_iff]
    exact le_trans h (Nat.mul_le_mul_right _ hi)

/-- 最初の比較がティック `delay` に起きる（`i₀ = 1`）ときの条件：`R ≤ 2049`。 -/
theorem walk_schedule_first_place (tgt R : ℕ) :
    (∀ i, 1 ≤ i → KeepsAhead tgt R i) ↔ R ≤ 2049 := by
  rw [walk_schedule_iff]

/-- **歩く方式は破綻する。**  半径が `2050` 以上になった瞬間、最初の replay
比較（`i = 1`、ティック `2048`）にヘッドが間に合わない。`radius` に
`2049` の上界はどこにもない（`GalilLedgerObligations.stage_meets_barrier` の
`2 * max k 1` は `k` とともに伸びる）ので、これは実際に起きうる。 -/
theorem walk_schedule_infeasible (tgt R : ℕ) (hR : 2050 ≤ R) :
    ¬ KeepsAhead tgt R 1 := by
  rw [keepsAhead_iff]; omega

/-- 「最初の比較より前に再配置を**終わらせる**」版の条件（`repRight_reaches`
の `repDist` ティックが 1 場所に収まる条件）：`R ≤ 2047`。 -/
theorem reposition_finishes_within_place (R : ℕ) (hR : R ≤ 2047) : R + 1 ≤ delay := by
  unfold delay; omega

theorem reposition_does_not_finish (R : ℕ) (hR : 2048 ≤ R) : ¬ (R + 1 ≤ delay) := by
  unfold delay; omega

/-- 再配置の所要ティックは距離そのもの：開始位置が `tgt + R` なら `repDist = R`。 -/
theorem repDist_frontier (tgt R : ℕ) : LocalInputView.repDist (tgt + R) tgt = R := by
  unfold LocalInputView.repDist; omega

/-! ## 6. 代替案：カーソルの役割張り替え（O(1) の view swap）

§5 の結論は「`right` を歩かせて `center` に合わせるのは実時間で不可能」。
代替は `LocalRoles` がカウンタに対してやったことを、カーソルに対してやること：
物理 view を `Fin V` で番号づけ、論理カーソル（`left`/`center`/`right`/…）は
**有限制御の中の写像** `cur : Cursor → Fin V` で指す。`right := center` は
`cur` の張り替え 1 回、すなわち 0 ティックになる。

必要なのは、`center` と同期した予備 view `spare` を常に持っておくこと。
同期は「同じ到着を食わせ、`center` と同じ動きを真似る」だけで保たれる
（§6.2）。どちらも 1 ティック 1 アクションなので `ViewLocal` に収まる。

そして §6.4 が、**現在の `LocalState.ViewLocal` ではこの張り替えは表現できない**
ことを示す：1 ステップの `ViewLocal` は `pos` を高々 1 しか動かせない。
つまり swap 案は `GalilVML` の拡張（view バンク＋役割写像）を要求する。 -/

/-! ### 6.1 同期した二つの view -/

/-- 二つの view が「同じ内容・同じ位置・同じ半歩フラグ」であること。 -/
def ViewSync (v w : InputView) : Prop :=
  cells v = cells w ∧ pos v = pos w ∧ v.gap = w.gap

theorem ViewSync.refl (v : InputView) : ViewSync v v := ⟨rfl, rfl, rfl⟩

theorem ViewSync.symm {v w : InputView} (h : ViewSync v w) : ViewSync w v :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

/-- 同期した view は同じ抽象ヘッドを持つ。 -/
theorem ViewSync.absHead {v w : InputView} (h : ViewSync v w) (q : List (Fin 2)) :
    absHead v q = absHead w q :=
  LocalTick2.absHead_congr h.1 h.2.1 h.2.2 q

/-- 同期した view は右側に同じだけの内容を持つ。 -/
theorem ViewSync.absRight_length {v w : InputView} (h : ViewSync v w) :
    (absRight v).length = (absRight w).length := by
  have h1 := LocalInputView.length_cells v
  have h2 := LocalInputView.length_cells w
  rw [h.1] at h1
  have hp := h.2.1
  omega

/-! ### 6.2 同期は 1 アクションずつの追随で保たれる -/

theorem pos_arrive (a : Fin 2) (v : InputView) : pos (LocalInputView.arrive a v) = pos v := rfl

theorem gap_arrive (a : Fin 2) (v : InputView) : (LocalInputView.arrive a v).gap = v.gap := rfl

theorem ViewSync.arrive {v w : InputView} (hv : WF v) (hw : WF w) (h : ViewSync v w) (a : Fin 2) :
    ViewSync (LocalInputView.arrive a v) (LocalInputView.arrive a w) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [LocalInputView.cells_arrive hv, LocalInputView.cells_arrive hw, h.1]
  · exact h.2.1
  · exact h.2.2

theorem ViewSync.stepLeft {v w : InputView} (h : ViewSync v w) :
    ViewSync (LocalInputView.stepLeft v) (LocalInputView.stepLeft w) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [LocalInputView.cells_stepLeft, LocalInputView.cells_stepLeft]; exact h.1
  · rcases v with ⟨bv, fv, nv, qv, gv⟩
    rcases w with ⟨bw, fw, nw, qw, gw⟩
    have hp := h.2.1
    cases bv <;> cases bw <;>
      simp_all [LocalInputView.stepLeft, LocalInputView.pos]
  · rw [LocalInputView.gap_stepLeft, LocalInputView.gap_stepLeft]; exact h.2.2

theorem ViewSync.stepRight {v w : InputView} (hv : WF v) (hw : WF w) (h : ViewSync v w) :
    ViewSync (LocalInputView.stepRight v) (LocalInputView.stepRight w) := by
  have hlen := h.absRight_length
  refine ⟨?_, ?_, ?_⟩
  · rw [LocalInputView.cells_stepRight hv, LocalInputView.cells_stepRight hw]; exact h.1
  · rcases Nat.eq_zero_or_pos (absRight v).length with h0 | hpos
    · have hv0 : absRight v = [] := List.length_eq_zero_iff.mp h0
      have hw0 : absRight w = [] := List.length_eq_zero_iff.mp (by omega)
      rw [LocalInputView.stepRight_nil hv hv0, LocalInputView.stepRight_nil hw hw0]
      exact h.2.1
    · rw [LocalInputView.pos_stepRight hv hpos, LocalInputView.pos_stepRight hw (by omega)]
      rw [h.2.1]
  · rw [LocalInputView.gap_stepRight hv, LocalInputView.gap_stepRight hw]; exact h.2.2

theorem cells_gap_update (v : InputView) (b : Bool) : cells { v with gap := b } = cells v := rfl

theorem pos_gap_update (v : InputView) (b : Bool) : pos { v with gap := b } = pos v := rfl

theorem ViewSync.moveRight {v w : InputView} (hv : WF v) (hw : WF w) (h : ViewSync v w) :
    ViewSync (LocalInputView.moveRight v) (LocalInputView.moveRight w) := by
  unfold LocalInputView.moveRight
  rw [← h.2.2]
  cases hg : v.gap
  · exact ⟨h.1, h.2.1, by simp⟩
  · obtain ⟨c1, c2, _⟩ := h.stepRight hv hw
    exact ⟨c1, c2, by simp⟩

theorem ViewSync.moveLeftV {v w : InputView} (h : ViewSync v w) :
    ViewSync (LocalInputView.moveLeftV v) (LocalInputView.moveLeftV w) := by
  unfold LocalInputView.moveLeftV
  rw [← h.2.2]
  cases hg : v.gap
  · obtain ⟨c1, c2, _⟩ := h.stepLeft
    exact ⟨c1, c2, by simp⟩
  · exact ⟨h.1, h.2.1, by simp⟩

theorem ViewSync.repositionStep {v w : InputView} (hv : WF v) (hw : WF w) (h : ViewSync v w)
    (target : ℕ) :
    ViewSync (LocalInputView.repositionStep target v) (LocalInputView.repositionStep target w) := by
  unfold LocalInputView.repositionStep
  rw [h.2.1]
  by_cases h1 : pos w < target
  · simp only [h1, if_pos]; exact h.stepRight hv hw
  · by_cases h2 : target < pos w
    · simp only [h1, h2, if_pos, ite_false]; exact h.stepLeft
    · simp only [h1, h2, ite_false]; exact h

/-! ### 6.3 view バンクと役割の張り替え -/

/-- `GalilVML` の論理カーソル、＋ swap 用の予備。 -/
inductive Cursor
  | left | center | right | walker | fppWalker | spare
  deriving DecidableEq

/-- 物理 view の束と、論理カーソルからの役割写像（後者は有限制御のデータ）。 -/
structure ViewBank (V : ℕ) where
  views : Fin V → InputView
  cur : Cursor → Fin V

variable {V : ℕ}

/-- バンクの 1 ティック：**各物理 view** が高々 1 アクション。`cur` は有限制御
データなので自由（`LocalState.StepLocal` が `roles` を自由にしているのと同じ）。 -/
def BankLocal (b b' : ViewBank V) : Prop :=
  ∀ j : Fin V, LocalState.ViewLocal (b.views j) (b'.views j)

theorem bankLocal_refl (b : ViewBank V) : BankLocal b b :=
  fun _ => LocalState.viewLocal_refl _

/-- 役割の張り替え。 -/
def swapCur (c d : Cursor) (f : Cursor → Fin V) : Cursor → Fin V :=
  fun e => if e = c then f d else if e = d then f c else f e

theorem swapCur_left (c d : Cursor) (f : Cursor → Fin V) : swapCur c d f c = f d := by
  simp [swapCur]

theorem swapCur_other {c d e : Cursor} (f : Cursor → Fin V) (h1 : e ≠ c) (h2 : e ≠ d) :
    swapCur c d f e = f e := by simp [swapCur, h1, h2]

/-- **O(1) の view swap**：物理 view には一切触らない。 -/
def viewSwap (c d : Cursor) (b : ViewBank V) : ViewBank V := { b with cur := swapCur c d b.cur }

theorem viewSwap_cur_self (c d : Cursor) (b : ViewBank V) :
    (viewSwap c d b).cur c = b.cur d := swapCur_left c d b.cur

theorem viewSwap_cur_other {c d e : Cursor} (b : ViewBank V) (h1 : e ≠ c) (h2 : e ≠ d) :
    (viewSwap c d b).cur e = b.cur e := swapCur_other b.cur h1 h2

theorem bankLocal_viewSwap (c d : Cursor) (b : ViewBank V) : BankLocal b (viewSwap c d b) :=
  fun _ => LocalState.viewLocal_refl _

/-- **代替案の帰結。**  `spare` が `center` と同期していれば、`right` と `spare`
の役割を入れ替えた瞬間に `right` の抽象ヘッドは `center` のそれと一致する。
コストは 0 ティック、動いた view は 0 本。これが `replayStartVM` の
`right := center` の実時間実装である。 -/
theorem viewSwap_immediate (b : ViewBank V)
    (hs : ViewSync (b.views (b.cur .spare)) (b.views (b.cur .center))) (q : List (Fin 2)) :
    absHead ((viewSwap .right .spare b).views ((viewSwap .right .spare b).cur .right)) q
      = absHead ((viewSwap .right .spare b).views ((viewSwap .right .spare b).cur .center)) q := by
  have hr : (viewSwap (V := V) Cursor.right Cursor.spare b).cur Cursor.right = b.cur Cursor.spare :=
    viewSwap_cur_self Cursor.right Cursor.spare b
  have hc : (viewSwap (V := V) Cursor.right Cursor.spare b).cur Cursor.center = b.cur Cursor.center :=
    viewSwap_cur_other (c := Cursor.right) (d := Cursor.spare) b (by decide) (by decide)
  show absHead (b.views ((viewSwap (V := V) Cursor.right Cursor.spare b).cur Cursor.right)) q
      = absHead (b.views ((viewSwap (V := V) Cursor.right Cursor.spare b).cur Cursor.center)) q
  rw [hr, hc]
  exact hs.absHead q

/-! ### 6.4 なぜ `LocalState.ViewLocal` のままでは済まないか -/

theorem pos_stepRight_bounds (v : InputView) :
    pos (LocalInputView.stepRight v) ≤ pos v + 1 ∧ pos v ≤ pos (LocalInputView.stepRight v) := by
  rcases v with ⟨b, f, n, q, g⟩
  cases n with
  | cons c rest => simp [LocalInputView.stepRight, LocalInputView.pos]
  | nil =>
      cases hh : RTQueue.head? q with
      | some a => simp [LocalInputView.stepRight, LocalInputView.pos, hh]
      | none => simp [LocalInputView.stepRight, LocalInputView.pos, hh]

theorem pos_stepLeft_bounds (v : InputView) :
    pos (LocalInputView.stepLeft v) ≤ pos v ∧ pos v ≤ pos (LocalInputView.stepLeft v) + 1 := by
  rcases v with ⟨b, f, n, q, g⟩
  cases b with
  | cons c rest => simp [LocalInputView.stepLeft, LocalInputView.pos]
  | nil => simp [LocalInputView.stepLeft, LocalInputView.pos]

/-- **1 ティックで `pos` は高々 1 しか動かない。** -/
theorem pos_moveRight (v : InputView) :
    pos (LocalInputView.moveRight v) = pos (LocalInputView.stepRight v)
      ∨ pos (LocalInputView.moveRight v) = pos v := by
  unfold LocalInputView.moveRight
  by_cases hg : v.gap = true
  · left; rw [if_pos hg]; rfl
  · right; rw [if_neg hg]; rfl

theorem pos_moveLeftV (v : InputView) :
    pos (LocalInputView.moveLeftV v) = pos v
      ∨ pos (LocalInputView.moveLeftV v) = pos (LocalInputView.stepLeft v) := by
  unfold LocalInputView.moveLeftV
  by_cases hg : v.gap = true
  · left; rw [if_pos hg]; rfl
  · right; rw [if_neg hg]; rfl

theorem pos_viewLocal {v w : InputView} (h : LocalState.ViewLocal v w) :
    pos w ≤ pos v + 1 ∧ pos v ≤ pos w + 1 := by
  rcases h with h | ⟨a, h⟩ | h | h | ⟨target, h⟩
  · subst h; omega
  · subst h; simp [pos_arrive]
  · subst h
    have hb := pos_stepRight_bounds v
    rcases pos_moveRight v with hh | hh <;> rw [hh] <;> omega
  · subst h
    have hb := pos_stepLeft_bounds v
    rcases pos_moveLeftV v with hh | hh <;> rw [hh] <;> omega
  · subst h
    unfold LocalInputView.repositionStep
    by_cases h1 : pos v < target
    · have := pos_stepRight_bounds v
      simp only [h1, if_pos]; omega
    · by_cases h2 : target < pos v
      · have := pos_stepLeft_bounds v
        simp only [h1, h2, if_pos, ite_false]; omega
      · simp only [h1, h2, ite_false]; omega

/-- **`right := center` は 1 ティックの `ViewLocal` にはならない。**  位置が 2
以上離れていれば、いかなる 1 アクションでも届かない。よって swap 案は
`GalilVML` を view バンク＋役割写像へ拡張することを要求する（§6.3）。 -/
theorem no_local_jump {v w : InputView} (h : pos v + 2 ≤ pos w) :
    ¬ LocalState.ViewLocal v w := by
  intro hl
  have := (pos_viewLocal hl).1
  omega

/-! ### 6.5 `GalilVML` の拡張：中心の鏡 view を 1 本持つ包み

`GalilVML` には `centerMirror` に相当する場がないので、包みの record を足す。
`vmViewSwap` は `right` と `centerMirror` を入れ替えるだけ——物理 view は
1 本も動かない（0 ティック）。`abs` の上ではそれがちょうど
`GalilScaffoldTopReplay.replayStartVM` の要求 `t.right = s.center` を与える。 -/

/-- `GalilVML` ＋ `center` と同期した予備 view。 -/
structure MirroredVML (P : ℕ) where
  vm : LocalState.GalilVML P
  centerMirror : InputView

/-- **役割の張り替え（実装版）。**  `right` と `centerMirror` を入れ替える。 -/
def vmViewSwap {P : ℕ} (m : MirroredVML P) : MirroredVML P :=
  { vm := { m.vm with right := m.centerMirror }, centerMirror := m.vm.right }

theorem vmViewSwap_untouched {P : ℕ} (m : MirroredVML P) :
    (vmViewSwap m).vm.center = m.vm.center ∧ (vmViewSwap m).vm.left = m.vm.left ∧
      (vmViewSwap m).vm.pending = m.vm.pending :=
  ⟨rfl, rfl, rfl⟩

theorem abs_right_update {P : ℕ} (x : LocalState.GalilVML P) (v : InputView) :
    LocalState.abs { x with right := v }
      = { LocalState.abs x with right := absHead v x.pending } := rfl

/-- **`viewSwap` の abs 正当性。**  `centerMirror` が `center` と同期していれば、
張り替えた瞬間の抽象状態はちょうど `right := center` を施したものに等しい。
コストは 0 ティック。これが `repRight_reaches`（`repDist` ティックかかる）の
代替であり、§5 で不可能と示された締切を回避する唯一の設計である。 -/
theorem abs_vmViewSwap {P : ℕ} (m : MirroredVML P)
    (hs : ViewSync m.centerMirror m.vm.center) :
    LocalState.abs (vmViewSwap m).vm
      = { LocalState.abs m.vm with right := (LocalState.abs m.vm).center } := by
  show LocalState.abs { m.vm with right := m.centerMirror } = _
  rw [abs_right_update, hs.absHead m.vm.pending]
  rfl

/-- 包みの 1 ティック：通常の局所ステップ（鏡も 1 アクション）か、張り替え 1 回。 -/
def StepLocalM {P : ℕ} (m m' : MirroredVML P) : Prop :=
  (LocalState.StepLocal m.vm m'.vm ∧ LocalState.ViewLocal m.centerMirror m'.centerMirror)
    ∨ m' = vmViewSwap m

theorem stepLocalM_vmViewSwap {P : ℕ} (m : MirroredVML P) : StepLocalM m (vmViewSwap m) :=
  Or.inr rfl

/-- **拡張は不可避。**  鏡が `right` から 2 セル以上離れていれば、張り替えは
もとの `StepLocal` には収まらない。つまり `StepLocalM` の第二枝（＝有限制御が
カーソルの役割を書き換える権利）は本当に新しい力である。 -/
theorem vmViewSwap_not_stepLocal {P : ℕ} (m : MirroredVML P)
    (h : pos m.vm.right + 2 ≤ pos m.centerMirror) :
    ¬ LocalState.StepLocal m.vm (vmViewSwap m).vm := by
  intro hl
  exact no_local_jump h hl.2.2.2.2.2.2.1

/-! ## 7. 残っている名前つき仮定

* `dp_clear_scheduled.hnext` / `fpp_clear_scheduled.hnext` / 
  `mirror_rebuild_scheduled.hnext` —— 「次のリセット（次の fallback、次の
  `take`）は 1 段以上あと」。段の構造（`GalilScaffoldTimingCost` の段分割）から
  出るはずだが、`commitRestart` / `commitReplay` / `commitFallback` を撃つ
  制御側の走行に沿った形ではまだ証明されていない。
* `dp_clear_scheduled.hWb` / `fpp_clear_scheduled.hWb` —— 遊休側の各テープの
  仕事量上界。DP 機械・fpp 機械の走査域が窓を出ないことは
  `GalilDpCost` / `GalilFallbackCost` の領域だが、`LocalBuffers.size` の言葉で
  述べ直されていない。
* `mirror_rebuild_scheduled.hv` —— 復元値が半径以下であること。
* `ViewSync` の維持 —— §6.2 は「同じアクションを真似れば同期が保たれる」ことを
  示すだけで、`center` が実際に受け取るアクション列に `spare` を追随させる
  制御が書かれていない。
* `viewSwap` の `GalilVML` への実装 —— §6.5 の `MirroredVML` は `GalilVML` を
  包んで `centerMirror` を 1 本足し、`abs_vmViewSwap` が abs 正当性
  （`replayStartVM` の `t.right = s.center` が 0 ティックで立つこと）を与える。
  残るのは (a) `LocalStepRealize` を `StepLocalM` の上に張り直すこと、
  (b) 各ティックが `centerMirror` に `center` と同じアクションを流す制御を
  書き、`ViewSync` を不変量として運ぶこと、(c) `GalilVML` 自体を §6.3 の
  バンク＋役割写像へ置き換える（`viewSwap_immediate` はその形の正当性）。
  `vmViewSwap_not_stepLocal` / `no_local_jump` はこの拡張が**必要**である
  ことを示すだけで、拡張後に `LocalStepRealize` が通ることは示していない。
* `abs_vmViewSwap.hs` —— 張り替えの瞬間に `centerMirror` が `center` と
  同期していること。§6.2 の追随補題から出るべきだが、実際の制御に沿った
  維持証明は未着手（上の (b)）。
* `LocalTick2` §9 の残り（`RestartStaged.lowerSrc` / `.workSlot`、
  `beginShiftVM_commitShift.hstaged`、`abs_commitFallback.hwork`、テープ再利用）
  は本ファイルの対象外。

**無条件 PAL ∈ PEG は未完.**
-/

end PalPeg.LocalSchedule

#print axioms PalPeg.LocalSchedule.cleared_at_deadline
#print axioms PalPeg.LocalSchedule.dp_clear_cost
#print axioms PalPeg.LocalSchedule.dp_clear_scheduled
#print axioms PalPeg.LocalSchedule.fpp_clear_fits_stage
#print axioms PalPeg.LocalSchedule.fpp_clear_place_fails
#print axioms PalPeg.LocalSchedule.fpp_clear_scheduled
#print axioms PalPeg.LocalSchedule.mirror_rebuild_cost
#print axioms PalPeg.LocalSchedule.mirror_rebuild_scheduled
#print axioms PalPeg.LocalSchedule.keepsAhead_iff
#print axioms PalPeg.LocalSchedule.keepsAhead_zero_iff
#print axioms PalPeg.LocalSchedule.walk_schedule_iff
#print axioms PalPeg.LocalSchedule.walk_schedule_first_place
#print axioms PalPeg.LocalSchedule.walk_schedule_infeasible
#print axioms PalPeg.LocalSchedule.reposition_does_not_finish
#print axioms PalPeg.LocalSchedule.repDist_frontier
#print axioms PalPeg.LocalSchedule.ViewSync.absHead
#print axioms PalPeg.LocalSchedule.ViewSync.arrive
#print axioms PalPeg.LocalSchedule.ViewSync.moveRight
#print axioms PalPeg.LocalSchedule.ViewSync.moveLeftV
#print axioms PalPeg.LocalSchedule.ViewSync.repositionStep
#print axioms PalPeg.LocalSchedule.viewSwap_cur_self
#print axioms PalPeg.LocalSchedule.viewSwap_cur_other
#print axioms PalPeg.LocalSchedule.bankLocal_viewSwap
#print axioms PalPeg.LocalSchedule.viewSwap_immediate
#print axioms PalPeg.LocalSchedule.pos_moveRight
#print axioms PalPeg.LocalSchedule.pos_moveLeftV
#print axioms PalPeg.LocalSchedule.pos_viewLocal
#print axioms PalPeg.LocalSchedule.no_local_jump
#print axioms PalPeg.LocalSchedule.abs_right_update
#print axioms PalPeg.LocalSchedule.abs_vmViewSwap
#print axioms PalPeg.LocalSchedule.stepLocalM_vmViewSwap
#print axioms PalPeg.LocalSchedule.vmViewSwap_not_stepLocal
