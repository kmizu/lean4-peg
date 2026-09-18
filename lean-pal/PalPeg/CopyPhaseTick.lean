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

end PalPeg.CopyPhaseTick
