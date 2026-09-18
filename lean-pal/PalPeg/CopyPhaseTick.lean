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

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter
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

end PalPeg.CopyPhaseTick
