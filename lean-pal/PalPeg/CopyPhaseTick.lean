import PalPeg.GalilBranchInvariants
import PalPeg.GalilSegmentConstruct

/-!
# copy 相の `ChainTick` は一致ビットによらず存在する

n121 / n122 で測ったとおり、`ReachesWatchPhase` に残るのは
**live chain 版の `watchSegE_construct`**（既存 `GalilSegmentConstructB.watchSegE_constructB`
の並行版）で、その帰納の各段で要るのが「chain が 1 手進める」こと。

`GalilBranchInvariants.copy_step_exists` は `CopyInv` から `ChainStep` の存在を出すが、
`WatchSegE` の構成子が要求するのは `ChainTick a`（＝ `ChainStep` ＋ 一致なら
`ChainMatched`）であって `ChainStep` そのものではない。ここではその差を埋める。

`a = false` なら `ChainTick` は `ChainStep` そのもの。`a = true` のときは
`ChainMatched` の行き先が要るが、`.copy` から出る `ChainStep` の行き先は
`.copy` か `.back` のどちらか（`copyBit` / `copyEnd`）で、`ChainMatched` は
その両方に構成子を持つ（`GalilScaffoldTopChainVM:69`）。したがって常に存在する。

**`WatchOk` 経由の `CloseoutTickFalse.chainOk_tick_false` は使えない**
（`WatchOk` は `WatchOkRefute.watchOk_false` で反証済み）。`CopyInv` 経由で行くこと。

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.CopyPhaseTick

open PalPeg PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilScaffoldController
open GalilScaffoldCounter GalilScaffoldChainVerifier GalilScaffoldInputHead
open PalPeg.GalilBranchInvariants

/-- **`.copy` から出る `ChainStep` の行き先は `.copy` か `.back`。** -/
theorem chainStep_copy_shape {t : GalilScaffoldTape.Tape} {h : Counter}
    {p : GalilScaffoldPlace.Place} {v : GalilScaffoldChainPeriod.Tape}
    {lag margin : Counter} {ver : GalilScaffoldInputHead.PlaceHead} {y : ChainVM}
    (hStep : ChainStep (ChainVM.copy t h p v lag margin ver) y) :
    (∃ t' h' p' v' margin', y = ChainVM.copy t' h' p' v' lag margin' ver) ∨
      (∃ v' h' margin', y = ChainVM.back v' h' lag margin' ver) := by
  cases hStep with
  | copyBit _ _ _ _ _ _ _ _ _ _ _ => exact Or.inl ⟨_, _, _, _, _, rfl⟩
  | copyEnd _ _ _ _ _ _ _ _ _ _ _ => exact Or.inr ⟨_, _, _, rfl⟩

/-- **copy 相では `ChainMatched` の行き先が必ずある。** -/
theorem chainMatched_exists_copy_or_back {y : ChainVM} {lag : Counter}
    {ver : GalilScaffoldInputHead.PlaceHead}
    (hShape : (∃ t' h' p' v' margin', y = ChainVM.copy t' h' p' v' lag margin' ver) ∨
      (∃ v' h' margin', y = ChainVM.back v' h' lag margin' ver)) :
    ∃ z : ChainVM, ChainMatched y z := by
  rcases hShape with ⟨t', h', p', v', margin', rfl⟩ | ⟨v', h', margin', rfl⟩
  · exact ⟨_, .copy _ _ _ _ _ _ _⟩
  · exact ⟨_, .back _ _ _ _ _⟩

/-- **copy 相の `ChainTick` は一致ビットによらず存在する。**
`watchSegE_construct` の live chain 版の各段で要るのはこれ。 -/
theorem copyChain_tick_exists {t : GalilScaffoldTape.Tape} {h : Counter}
    {p : GalilScaffoldPlace.Place} {v : GalilScaffoldChainPeriod.Tape} {n : ℕ}
    (hCopyInv : CopyInv t h p v n) (lag margin : Counter)
    (ver : GalilScaffoldInputHead.PlaceHead) (a : Bool) :
    ∃ z : ChainVM, ChainTick a (ChainVM.copy t h p v lag margin ver) z := by
  obtain ⟨y, hStep⟩ := copy_step_exists hCopyInv lag margin ver
  cases a with
  | false => exact ⟨y, y, hStep, rfl⟩
  | true =>
    obtain ⟨z, hMatched⟩ := chainMatched_exists_copy_or_back (chainStep_copy_shape hStep)
    exact ⟨z, y, hStep, hMatched⟩

/-- **その行き先は idle にならない。**  区間に沿って chain が live のままであることの
基本形（`WatchSegE.match` の側条件 `s.chain ≠ .idle` を次の段でも満たす）。 -/
theorem copyChain_tick_not_idle {t : GalilScaffoldTape.Tape} {h : Counter}
    {p : GalilScaffoldPlace.Place} {v : GalilScaffoldChainPeriod.Tape}
    {lag margin : Counter} {ver : GalilScaffoldInputHead.PlaceHead} {z : ChainVM} {a : Bool}
    (hTick : ChainTick a (ChainVM.copy t h p v lag margin ver) z) :
    z ≠ ChainVM.idle := by
  obtain ⟨y, hStep, hAfter⟩ := hTick
  rcases chainStep_copy_shape hStep with hShape | hShape
  · obtain ⟨t', h', p', v', margin', rfl⟩ := hShape
    cases a with
    | false => rw [show z = _ from hAfter]; intro hEq; exact ChainVM.noConfusion hEq
    | true =>
      cases hAfter with
      | copy _ _ _ _ _ _ _ => intro hEq; exact ChainVM.noConfusion hEq
  · obtain ⟨v', h', margin', rfl⟩ := hShape
    cases a with
    | false => rw [show z = _ from hAfter]; intro hEq; exact ChainVM.noConfusion hEq
    | true =>
      cases hAfter with
      | back _ _ _ _ _ => intro hEq; exact ChainVM.noConfusion hEq

#print axioms chainStep_copy_shape
#print axioms chainMatched_exists_copy_or_back
#print axioms copyChain_tick_exists
#print axioms copyChain_tick_not_idle


/-! ## live chain の background 量子は**探索を動かさない**

`searchEffect P a s vq` の定義（`GalilScaffoldTopSearch:179`）は

    (s.chain = .idle ∧ searchStep (P.place s) a (searchLens.get s) vq) ∨
    (s.chain ≠ .idle ∧ vq = searchLens.get s)

で、**chain が live なら探索は完全に不活性**（`vq = searchLens.get s`）。
したがって live chain 版の区間構成は `ReadyFuel` / `SearchReady` の帳簿を
**一切必要としない**——`constructB`（idle 版）より簡単になる。

n121 / n123 に「構造的に並行」と書いたが、実際には**探索側の帳簿が丸ごと消える**ぶん
簡単。`GalilSegmentConstruct.idle_background_exists` の live 版がこれ。 -/

/-- **live chain の background 量子は存在し、探索も heads も動かさない。**
`idle_background_exists` の live 版。chain が非 idle なので `chainBorn` は false で
`afterBirth` は恒等、`searchEffect` は不活性分岐。 -/
theorem live_background_exists (P : Shared) (q : ℕ) (first : Fin 9) (s : GalilVM)
    {z : ChainVM} (hNotIdle : s.chain ≠ ChainVM.idle)
    (hTick : ChainTick false s.chain z) :
    ∃ s', (galilFrameS P q first).background s s' ∧ s'.chain = z ∧
      s'.left = s.left ∧ s'.right = s.right ∧ s'.center = s.center ∧ s'.replay = s.replay ∧
      searchLens.get s' = searchLens.get s := by
  have hSearch : searchEffect P false s (searchLens.get s) := Or.inr ⟨hNotIdle, rfl⟩
  have hBorn : chainBorn
      (decide ((searchLens.get s).search.mode = GalilScaffoldSearchFinish.Mode.found))
      s.chain = false := by
    unfold chainBorn
    cases hc : s.chain with
    | idle => exact absurd hc hNotIdle
    | copy _ _ _ _ _ _ _ => exact Bool.false_and _
    | back _ _ _ _ _ => exact Bool.false_and _
    | watch _ => exact Bool.false_and _
    | broken _ => exact Bool.false_and _
  refine ⟨searchLens.set (scanLens.set s ⟨s.left, s.right, z⟩) (searchLens.get s),
    ?_, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · refine ⟨rfl, rfl, ?_, Or.inl ⟨hNotIdle, ?_⟩, ?_⟩
    · rw [searchLens.get_set]; exact hSearch
    · exact hTick
    · rw [searchLens.get_set, hBorn, afterBirth_false]
      rfl
  · rw [searchLens.get_set]

#print axioms live_background_exists


/-! ## live chain 版区間の 1 手（`wait` / `count`）

`live_background_exists` ＋ `WatchSegE` の構成子 ＋ `.stop` で、長さ 1 の区間が直接出る。
帰納の本体はこれを繋ぐだけになる。 -/

/-- **`wait` 段の 1 手**（右ヘッドが進めない）。 -/
theorem watchSegE_wait_live (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (c : Control) (s : GalilVM)
    (hScan : c.mode = Mode.scan) (hNotReplaying : c.replaying = false)
    (hUnavailable : ¬ canRight s.right)
    {z : ChainVM} (hNotIdle : s.chain ≠ ChainVM.idle)
    (hTick : ChainTick false s.chain z) :
    ∃ s', WatchSegE P q first delay [false] c s c s' ∧ s'.chain = z ∧
      s'.left = s.left ∧ s'.right = s.right ∧ s'.center = s.center ∧ s'.replay = s.replay ∧
      searchLens.get s' = searchLens.get s := by
  obtain ⟨s', hBg, hChain, hL, hR, hC, hRep, hGet⟩ :=
    live_background_exists P q first s hNotIdle hTick
  exact ⟨s', .wait c s s' hScan hNotReplaying hUnavailable hBg (.stop _ _),
    hChain, hL, hR, hC, hRep, hGet⟩

/-- **`count` 段の 1 手**（右ヘッドが進めて clock が 2 以上）。 -/
theorem watchSegE_count_live (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (c : Control) (s : GalilVM)
    (hScan : c.mode = Mode.scan) (hNotReplaying : c.replaying = false)
    (hAvailable : canRight s.right) (hClock : 1 < c.clock)
    {z : ChainVM} (hNotIdle : s.chain ≠ ChainVM.idle)
    (hTick : ChainTick false s.chain z) :
    ∃ s', WatchSegE P q first delay [false] c s { c with clock := c.clock - 1 } s' ∧
      s'.chain = z ∧
      s'.left = s.left ∧ s'.right = s.right ∧ s'.center = s.center ∧ s'.replay = s.replay ∧
      searchLens.get s' = searchLens.get s := by
  obtain ⟨s', hBg, hChain, hL, hR, hC, hRep, hGet⟩ :=
    live_background_exists P q first s hNotIdle hTick
  exact ⟨s', .count c s s' hScan hNotReplaying hAvailable hClock hBg (.stop _ _),
    hChain, hL, hR, hC, hRep, hGet⟩

/-- **copy 相の chain なら、`wait` / `count` のどちらかの 1 手が必ずある。**
`copyChain_tick_exists` が chain の 1 手を、`live_background_exists` が VM の 1 手を出す。
残差は clock の条件だけ。 -/
theorem watchSegE_oneStep_live (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (c : Control) (s : GalilVM)
    {t : GalilScaffoldTape.Tape} {h : Counter} {pl : GalilScaffoldPlace.Place}
    {v : GalilScaffoldChainPeriod.Tape} {lag margin : Counter}
    {ver : GalilScaffoldInputHead.PlaceHead} {m : ℕ}
    (hCopy : s.chain = ChainVM.copy t h pl v lag margin ver)
    (hCopyInv : CopyInv t h pl v m)
    (hScan : c.mode = Mode.scan) (hNotReplaying : c.replaying = false)
    (hClockOrUnavailable : ¬ canRight s.right ∨ 1 < c.clock) :
    ∃ (c' : Control) (s' : GalilVM),
      WatchSegE P q first delay [false] c s c' s' ∧ s'.chain ≠ ChainVM.idle ∧
      s'.left = s.left ∧ s'.right = s.right ∧ s'.center = s.center ∧ s'.replay = s.replay ∧
      searchLens.get s' = searchLens.get s ∧ c'.mode = Mode.scan ∧ c'.replaying = false := by
  obtain ⟨z, hTick⟩ := copyChain_tick_exists hCopyInv lag margin ver false
  have hTick' : ChainTick false s.chain z := by rw [hCopy]; exact hTick
  have hNotIdle : s.chain ≠ ChainVM.idle := by rw [hCopy]; intro h0; cases h0
  have hzNotIdle : z ≠ ChainVM.idle := copyChain_tick_not_idle hTick
  rcases hClockOrUnavailable with hUn | hClk
  · obtain ⟨s', hSeg, hChain, hL, hR, hC, hRep, hGet⟩ :=
      watchSegE_wait_live P q first delay c s hScan hNotReplaying hUn hNotIdle hTick'
    exact ⟨c, s', hSeg, by rw [hChain]; exact hzNotIdle, hL, hR, hC, hRep, hGet, hScan,
      hNotReplaying⟩
  · by_cases hAv : canRight s.right
    · obtain ⟨s', hSeg, hChain, hL, hR, hC, hRep, hGet⟩ :=
        watchSegE_count_live P q first delay c s hScan hNotReplaying hAv hClk hNotIdle hTick'
      exact ⟨_, s', hSeg, by rw [hChain]; exact hzNotIdle, hL, hR, hC, hRep, hGet, hScan,
        hNotReplaying⟩
    · obtain ⟨s', hSeg, hChain, hL, hR, hC, hRep, hGet⟩ :=
        watchSegE_wait_live P q first delay c s hScan hNotReplaying hAv hNotIdle hTick'
      exact ⟨c, s', hSeg, by rw [hChain]; exact hzNotIdle, hL, hR, hC, hRep, hGet, hScan,
        hNotReplaying⟩

#print axioms watchSegE_wait_live
#print axioms watchSegE_count_live
#print axioms watchSegE_oneStep_live


/-! ## `.back` 相も 1 手が必ずある（background 事象なら無条件）

`ChainStep` の `.back` からの構成子は 2 つで、`isFirst v.focus` の真偽で**排他かつ網羅**:

    backStep : isFirst v.focus = false → .back → .back
    backDone : isFirst v.focus = true  → .back → .watch

したがって `.back` 相では前提なしに `ChainStep` がある。行き先は `.back` か `.watch`。

**一致事象（`a = true`）で `.watch` に入る手は無条件ではない**——`ChainMatched` の
`.watch` 構成子は `GalilScaffoldChainWatch.Outer w true w'` を要求する。
だが**そこが到達点**（`ReachesWatchPhase`）なので、構成はそこで止まればよい。
`found_to_watchStart_least` はイベント列の中身を問わないので、
**background だけの区間（全部 `false`）で watch まで届く**。 -/

/-- **`.back` からは前提なしに `ChainStep` がある。** -/
theorem chainStep_back_exists (v : GalilScaffoldChainPeriod.Tape) (h lag margin : Counter)
    (ver : GalilScaffoldInputHead.PlaceHead) :
    ∃ y : ChainVM, ChainStep (ChainVM.back v h lag margin ver) y := by
  cases hf : GalilScaffoldChainPeriod.isFirst v.focus with
  | false => exact ⟨_, .backStep _ _ _ _ _ hf⟩
  | true => exact ⟨_, .backDone _ _ _ _ _ hf⟩

/-- **`.back` から出る `ChainStep` の行き先は `.back` か `.watch`。** -/
theorem chainStep_back_shape {v : GalilScaffoldChainPeriod.Tape} {h lag margin : Counter}
    {ver : GalilScaffoldInputHead.PlaceHead} {y : ChainVM}
    (hStep : ChainStep (ChainVM.back v h lag margin ver) y) :
    (∃ v', y = ChainVM.back v' h lag margin ver) ∨
      (∃ w : GalilScaffoldChainWatch.State, y = ChainVM.watch w) := by
  cases hStep with
  | backStep _ _ _ _ _ _ => exact Or.inl ⟨_, rfl⟩
  | backDone _ _ _ _ _ _ => exact Or.inr ⟨_, rfl⟩

/-- **background 事象なら `.back` 相の `ChainTick` は無条件に存在する。** -/
theorem backChain_tick_false_exists (v : GalilScaffoldChainPeriod.Tape) (h lag margin : Counter)
    (ver : GalilScaffoldInputHead.PlaceHead) :
    ∃ z : ChainVM, ChainTick false (ChainVM.back v h lag margin ver) z := by
  obtain ⟨y, hStep⟩ := chainStep_back_exists v h lag margin ver
  exact ⟨y, y, hStep, rfl⟩

/-- **その行き先は idle にならない。** -/
theorem backChain_tick_false_not_idle {v : GalilScaffoldChainPeriod.Tape}
    {h lag margin : Counter} {ver : GalilScaffoldInputHead.PlaceHead} {z : ChainVM}
    (hTick : ChainTick false (ChainVM.back v h lag margin ver) z) : z ≠ ChainVM.idle := by
  obtain ⟨y, hStep, hAfter⟩ := hTick
  rw [show z = y from hAfter]
  rcases chainStep_back_shape hStep with ⟨v', rfl⟩ | ⟨w, rfl⟩
  · intro hEq; exact ChainVM.noConfusion hEq
  · intro hEq; exact ChainVM.noConfusion hEq

/-- **background 事象では copy 相でも `ChainTick` は無条件**（`CopyInv` は要る）。
`copyChain_tick_exists` の `a = false` 版を名前で置いておく。 -/
theorem copyChain_tick_false_exists {t : GalilScaffoldTape.Tape} {h : Counter}
    {p : GalilScaffoldPlace.Place} {v : GalilScaffoldChainPeriod.Tape} {n : ℕ}
    (hCopyInv : CopyInv t h p v n) (lag margin : Counter)
    (ver : GalilScaffoldInputHead.PlaceHead) :
    ∃ z : ChainVM, ChainTick false (ChainVM.copy t h p v lag margin ver) z :=
  copyChain_tick_exists hCopyInv lag margin ver false

#print axioms chainStep_back_exists
#print axioms chainStep_back_shape
#print axioms backChain_tick_false_exists
#print axioms backChain_tick_false_not_idle
#print axioms copyChain_tick_false_exists


/-! ## 相の不変量 `CopyOrBack` は 1 手で保たれる（watch に着くまで）

帰納の本体を回すには「chain の相が copy（`CopyInv` つき）か back のまま」が要る。
`copyBit` は `t.focus = 8` を要求するが、`CopyInv t h p v 0` は
`AnswerAhead t 0`（＝ `t.focus = 4`、`answerAhead_zero`）を含むので、
**残り 0 のときは `copyBit` が撃てない**。したがって `copyBit` が撃てたなら残りは
`n+1` の形で、`copyInv_step` が行き先の `CopyInv` を与える。 -/

/-- **区間に沿って運ぶ相の不変量。** -/
def CopyOrBack (x : ChainVM) : Prop :=
  (∃ (t : GalilScaffoldTape.Tape) (h : Counter) (p : GalilScaffoldPlace.Place)
      (v : GalilScaffoldChainPeriod.Tape) (lag margin : Counter)
      (ver : GalilScaffoldInputHead.PlaceHead) (m : ℕ),
      x = ChainVM.copy t h p v lag margin ver ∧ CopyInv t h p v m) ∨
  (∃ (v : GalilScaffoldChainPeriod.Tape) (h lag margin : Counter)
      (ver : GalilScaffoldInputHead.PlaceHead), x = ChainVM.back v h lag margin ver)

theorem copyOrBack_not_idle {x : ChainVM} (h : CopyOrBack x) : x ≠ ChainVM.idle := by
  rcases h with ⟨_, _, _, _, _, _, _, _, rfl, -⟩ | ⟨_, _, _, _, _, rfl⟩ <;>
    intro hEq <;> exact ChainVM.noConfusion hEq

/-- **`.copy` の 1 手の行き先は「`CopyInv` つきの `.copy`」か「`.back`」。** -/
theorem copyInv_step_shape {t : GalilScaffoldTape.Tape} {h : Counter}
    {p : GalilScaffoldPlace.Place} {v : GalilScaffoldChainPeriod.Tape} {m : ℕ}
    {lag margin : Counter} {ver : GalilScaffoldInputHead.PlaceHead} {y : ChainVM}
    (hInv : CopyInv t h p v m)
    (hStep : ChainStep (ChainVM.copy t h p v lag margin ver) y) :
    CopyOrBack y := by
  cases hStep with
  | copyBit _ _ _ _ _ _ _ a hOne hLegal hPresent =>
    refine Or.inl ⟨_, _, _, _, _, _, _, ?_, rfl, ?_⟩
    · exact m - 1
    · cases m with
      | zero =>
        exfalso
        have h4 : t.focus = 4 := answerAhead_zero hInv.1
        rw [h4] at hOne
        exact absurd hOne (by decide)
      | succ k => simpa using copyInv_step hInv a
  | copyEnd _ _ _ _ _ _ _ b _ _ _ => exact Or.inr ⟨_, _, _, _, _, rfl⟩

/-- **`CopyOrBack` は background の 1 手で保たれる**——ただし `.back → .watch` の
ときだけ外れる。そこが到達点なので、結論は選言にする。 -/
theorem copyOrBack_tick_false {x z : ChainVM} (hInv : CopyOrBack x)
    (hTick : ChainTick false x z) :
    CopyOrBack z ∨ ∃ w : GalilScaffoldChainWatch.State, z = ChainVM.watch w := by
  obtain ⟨y, hStep, hAfter⟩ := hTick
  have hzy : z = y := hAfter
  subst hzy
  rcases hInv with ⟨t, h, p, v, lag, margin, ver, m, rfl, hCopyInv⟩ | ⟨v, h, lag, margin, ver, rfl⟩
  · exact Or.inl (copyInv_step_shape hCopyInv hStep)
  · rcases chainStep_back_shape hStep with ⟨v', rfl⟩ | ⟨w, rfl⟩
    · exact Or.inl (Or.inr ⟨_, _, _, _, _, rfl⟩)
    · exact Or.inr ⟨w, rfl⟩

/-- **`CopyOrBack` なら background の 1 手が必ずある。** -/
theorem copyOrBack_tick_false_exists {x : ChainVM} (hInv : CopyOrBack x) :
    ∃ z : ChainVM, ChainTick false x z := by
  rcases hInv with ⟨t, h, p, v, lag, margin, ver, m, rfl, hCopyInv⟩ | ⟨v, h, lag, margin, ver, rfl⟩
  · exact copyChain_tick_false_exists hCopyInv lag margin ver
  · exact backChain_tick_false_exists v h lag margin ver

#print axioms copyOrBack_not_idle
#print axioms copyInv_step_shape
#print axioms copyOrBack_tick_false
#print axioms copyOrBack_tick_false_exists


/-! ## 帰納の本体: live chain 版の background 区間構成

`constructB`（idle 版）の live chain 対応物。探索側の帳簿が丸ごと不要になるので
（`searchEffect` が不活性分岐）、必要なのは

* chain の 1 手（`copyOrBack_tick_false_exists`）
* 相の保存（`copyOrBack_tick_false`）
* VM の 1 手（`live_background_exists`）
* clock の余裕（`n < c.clock`）

だけ。結論は**選言**——「watch に着いた（＝ `ReachesWatchPhase` の中身）」か
「`n` 手走り切ってまだ copy/back」。 -/

/-- **live chain 版の background 区間構成。**  `n < c.clock` の間、`wait` / `count` だけで
`n` 手の区間が走る。途中で chain が watch に着いたらそこで止まる。 -/
theorem watchSegE_backgroundRun_live (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) :
    ∀ (n : ℕ) (c : Control) (s : GalilVM),
      c.mode = Mode.scan → c.replaying = false → n < c.clock →
      CopyOrBack s.chain →
      ∃ (es : List Bool) (c' : Control) (s' : GalilVM),
        WatchSegE P q first delay es c s c' s' ∧ es.count true = 0 ∧
        ((∃ w : GalilScaffoldChainWatch.State, s'.chain = ChainVM.watch w) ∨
          (es.length = n ∧ CopyOrBack s'.chain)) := by
  intro n
  induction n with
  | zero =>
    intro c s hScan hNotReplaying _ hInv
    exact ⟨[], c, s, .stop _ _, rfl, Or.inr ⟨rfl, hInv⟩⟩
  | succ n ih =>
    intro c s hScan hNotReplaying hClock hInv
    obtain ⟨z, hTick⟩ := copyOrBack_tick_false_exists hInv
    obtain ⟨s1, hBg, hChain, -, -, -, -, -⟩ :=
      live_background_exists P q first s (copyOrBack_not_idle hInv) hTick
    have hNext : CopyOrBack s1.chain ∨ ∃ w : GalilScaffoldChainWatch.State,
        s1.chain = ChainVM.watch w := by
      rw [hChain]; exact copyOrBack_tick_false hInv hTick
    by_cases hAvailable : canRight s.right
    · have hClockTwo : 1 < c.clock := by omega
      rcases hNext with hInv1 | hWatch
      · obtain ⟨es, c', s', hSeg, hCount, hEnd⟩ :=
          ih { c with clock := c.clock - 1 } s1 hScan hNotReplaying (by simp; omega) hInv1
        refine ⟨false :: es, c', s',
          .count c s s1 hScan hNotReplaying hAvailable hClockTwo hBg hSeg, by simpa using hCount, ?_⟩
        rcases hEnd with hW | ⟨hLen, hI⟩
        · exact Or.inl hW
        · exact Or.inr ⟨by simp [hLen], hI⟩
      · exact ⟨[false], _, s1,
          .count c s s1 hScan hNotReplaying hAvailable hClockTwo hBg (.stop _ _), by simp,
          Or.inl hWatch⟩
    · rcases hNext with hInv1 | hWatch
      · obtain ⟨es, c', s', hSeg, hCount, hEnd⟩ :=
          ih c s1 hScan hNotReplaying (by omega) hInv1
        refine ⟨false :: es, c', s',
          .wait c s s1 hScan hNotReplaying hAvailable hBg hSeg, by simpa using hCount, ?_⟩
        rcases hEnd with hW | ⟨hLen, hI⟩
        · exact Or.inl hW
        · exact Or.inr ⟨by simp [hLen], hI⟩
      · exact ⟨[false], c, s1,
          .wait c s s1 hScan hNotReplaying hAvailable hBg (.stop _ _), by simp, Or.inl hWatch⟩

#print axioms watchSegE_backgroundRun_live

end PalPeg.CopyPhaseTick
