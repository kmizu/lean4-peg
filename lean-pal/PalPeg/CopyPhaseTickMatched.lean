import PalPeg.CopyPhaseTick

/-!
# 一致事象（`a = true`）でも copy/back 相の `ChainTick` は存在する

`CopyPhaseTick.watchSegE_backgroundRun_live` は `n < c.clock` の間だけ区間を作る。
つまり **`2h+2 < 2048` の準備しか載らない**（`WatchSegE.count` は `1 < c.clock` を
要求し、`.match` は `c.clock = 1` で `delay = 2048` に戻す——一次情報は
`GalilScaffoldTopWatchSegE.lean:26,33`）。半周期 `h` は入力長に比例して伸びるので、
**これは一般には足りない**。準備が入力記号をまたぐときは区間に `.match`（事象 `true`）
が混ざる。

`.match` を載せるには chain が一致事象で 1 手進めること、すなわち
`ChainTick true x z` の存在が要る。ここが以前 `sorry` を書きかけた場所で、
本当の障害は `.back` から `backDone` で生まれた watch に `ChainMatched` を当てる段:

* `ChainMatched.watch` は `Outer w true w'` を要求する。その 2 枝は
  `queued`（`zero w.lag = false`）と `immediate`（`zero w.lag = true` ∧ `Good w`）。
* `Good` は誕生時には出ない（`WatchOkRefute.watchOk_false` が示したとおり、
  `born` は lag/margin と period/入力を関係づけない）。

**しかし誕生した chain の lag は正である**: `chainStart … radius` が
`lag = margin = radius = ofNat (r0+1)` を置き、copy/back の `ChainStep` は lag を
触らず、`ChainMatched` は `inc` するだけ。よって `zero lag = false` が保たれ、
`Outer.queued` が無条件に使える。`Good` は要らない。

同じ正値が `ChainMatched.breaks`（`BreakStep` は `zero w.lag = true` を要求、
`GalilScaffoldTopChainVM:27`）も排除するので、一致事象の行き先は
「copy/back のまま」か「watch」のどちらかに閉じる。

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.CopyPhaseTickMatched

open PalPeg PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilScaffoldController
open GalilScaffoldCounter GalilScaffoldChainVerifier GalilScaffoldInputHead
open PalPeg.GalilBranchInvariants PalPeg.CopyPhaseTick

/-! ## カウンタの正値 -/

/-- 正なら零でない。 -/
theorem zero_false_of_positive {c : Counter} (hPos : positive c = true) : zero c = false := by
  have hEmpty : c.pos.isEmpty = false := by simpa [positive] using hPos
  simp [zero, hEmpty]

/-- `inc` は正値を保つ。**`zero` の否定では保たれない**（`⟨[], [()]⟩` の `inc` は
`reset`）ので、不変量は `positive` で書くこと。 -/
theorem positive_inc {c : Counter} (hPos : positive c = true) : positive (inc c) = true := by
  have hEmpty : c.pos.isEmpty = false := by simpa [positive] using hPos
  cases hNeg : c.neg with
  | nil => simp [inc, positive, hNeg]
  | cons a ns => simp [inc, positive, hNeg, hEmpty]

/-- 誕生時の半径は正。 -/
theorem positive_ofNat_succ (n : ℕ) : positive (ofNat (n + 1)) = true := by
  simp [positive, ofNat]

/-! ## chain の lag が正であること -/

/-- **(NAMED) chain の lag が正**（`.copy` / `.back` 相でだけ内容がある）。 -/
def LagPos : ChainVM → Prop
  | .copy _ _ _ _ lag _ _ => positive lag = true
  | .back _ _ lag _ _ => positive lag = true
  | _ => True

/-- `ChainStep` は lag を触らない（`backDone` の行き先 `.watch` では自明）。 -/
theorem lagPos_chainStep {x y : ChainVM} (hLag : LagPos x) (hStep : ChainStep x y) : LagPos y := by
  cases hStep with
  | idle => trivial
  | brokenIdle _ => trivial
  | copyBit _ _ _ _ _ _ _ _ _ _ _ => exact hLag
  | copyEnd _ _ _ _ _ _ _ _ _ _ _ => exact hLag
  | backStep _ _ _ _ _ _ => exact hLag
  | backDone _ _ _ _ _ _ => trivial
  | watchStep _ _ _ => trivial

/-- `ChainMatched` は lag を `inc` するだけ。 -/
theorem lagPos_chainMatched {x y : ChainVM} (hLag : LagPos x) (hMatched : ChainMatched x y) :
    LagPos y := by
  cases hMatched with
  | idle => trivial
  | copy _ _ _ _ _ _ _ => exact positive_inc hLag
  | back _ _ _ _ _ => exact positive_inc hLag
  | watch _ _ _ => trivial
  | breaks _ _ _ => trivial

/-- **`LagPos` は 1 tick で保たれる**（事象によらず）。 -/
theorem lagPos_tick {a : Bool} {x z : ChainVM} (hLag : LagPos x) (hTick : ChainTick a x z) :
    LagPos z := by
  obtain ⟨y, hStep, hAfter⟩ := hTick
  have hMid : LagPos y := lagPos_chainStep hLag hStep
  cases a with
  | false =>
    have hEq : z = y := hAfter
    rw [hEq]; exact hMid
  | true => exact lagPos_chainMatched hMid hAfter

/-- 誕生した chain の lag は正。 -/
theorem lagPos_chainStart (answer : GalilScaffoldTape.Tape) (cen : Fin 3)
    (walker : GalilScaffoldPlace.Place) (ver : GalilScaffoldInputHead.PlaceHead) (n : ℕ) :
    LagPos (chainStart answer cen walker ver (ofNat (n + 1))) :=
  positive_ofNat_succ n

/-- 誕生の `ChainMatched` 1 歩を経ても正。 -/
theorem lagPos_of_chainMatched_chainStart {answer : GalilScaffoldTape.Tape} {cen : Fin 3}
    {walker : GalilScaffoldPlace.Place} {ver : GalilScaffoldInputHead.PlaceHead} {n : ℕ}
    {ch : ChainVM}
    (hMatched : ChainMatched (chainStart answer cen walker ver (ofNat (n + 1))) ch) :
    LagPos ch :=
  lagPos_chainMatched (lagPos_chainStart answer cen walker ver n) hMatched

#print axioms zero_false_of_positive
#print axioms positive_inc
#print axioms lagPos_tick
#print axioms lagPos_of_chainMatched_chainStart

/-! ## 一致事象の `ChainTick` -/

/-- `.back` の 1 手の行き先は、lag を保った `.back` か、lag を受け継いだ `.watch`。
`CopyPhaseTick.chainStep_back_shape` の lag つき版。 -/
theorem chainStep_back_shape' {v : GalilScaffoldChainPeriod.Tape} {h lag margin : Counter}
    {ver : GalilScaffoldInputHead.PlaceHead} {y : ChainVM}
    (hStep : ChainStep (ChainVM.back v h lag margin ver) y) :
    (∃ v', y = ChainVM.back v' h lag margin ver) ∨
      (∃ w : GalilScaffoldChainWatch.State, y = ChainVM.watch w ∧ w.lag = lag) := by
  cases hStep with
  | backStep _ _ _ _ _ _ => exact Or.inl ⟨_, rfl⟩
  | backDone _ _ _ _ _ _ => exact Or.inr ⟨_, rfl, rfl⟩

/-- **`.back` 相でも一致事象の `ChainTick` は存在する**——lag が正であるかぎり。
`isFirst = true` の枝が `backDone` ＋ `Outer.queued` で、ここだけが lag を使う。 -/
theorem backChain_tick_true_exists (v : GalilScaffoldChainPeriod.Tape) (h lag margin : Counter)
    (ver : GalilScaffoldInputHead.PlaceHead) (hLag : positive lag = true) :
    ∃ z : ChainVM, ChainTick true (ChainVM.back v h lag margin ver) z := by
  cases hFirst : GalilScaffoldChainPeriod.isFirst v.focus with
  | false => exact ⟨_, _, .backStep v h lag margin ver hFirst, .back _ _ _ _ _⟩
  | true =>
    exact ⟨_, _, .backDone v h lag margin ver hFirst,
      .watch _ _ (.queued _ (zero_false_of_positive hLag))⟩

/-- **`CopyOrBack` ＋ lag 正なら、一致事象でも 1 手ある。** -/
theorem copyOrBack_tick_true_exists {x : ChainVM} (hPhase : CopyOrBack x) (hLag : LagPos x) :
    ∃ z : ChainVM, ChainTick true x z := by
  rcases hPhase with ⟨t, h, p, v, lag, margin, ver, m, rfl, hCopyInv⟩ | ⟨v, h, lag, margin, ver, rfl⟩
  · exact copyChain_tick_exists hCopyInv lag margin ver true
  · exact backChain_tick_true_exists v h lag margin ver hLag

/-- copy/back の `ChainMatched` は相を保つ。 -/
theorem copyOrBack_matched {y z : ChainVM} (hPhase : CopyOrBack y) (hMatched : ChainMatched y z) :
    CopyOrBack z := by
  rcases hPhase with ⟨t, h, p, v, lag, margin, ver, m, rfl, hCopyInv⟩ | ⟨v, h, lag, margin, ver, rfl⟩
  · cases hMatched with
    | copy _ _ _ _ _ _ _ => exact Or.inl ⟨_, _, _, _, _, _, _, m, rfl, hCopyInv⟩
  · cases hMatched with
    | back _ _ _ _ _ => exact Or.inr ⟨_, _, _, _, _, rfl⟩

/-- **一致事象でも相は「copy/back のまま」か「watch」に閉じる。**
`ChainMatched.breaks` は `BreakStep` の `zero w.lag = true` で排除される。 -/
theorem copyOrBack_tick_true {x z : ChainVM} (hPhase : CopyOrBack x) (hLag : LagPos x)
    (hTick : ChainTick true x z) :
    CopyOrBack z ∨ ∃ w : GalilScaffoldChainWatch.State, z = ChainVM.watch w := by
  obtain ⟨y, hStep, hAfter⟩ := hTick
  have hMatched : ChainMatched y z := hAfter
  rcases hPhase with ⟨t, h, p, v, lag, margin, ver, m, rfl, hCopyInv⟩ | ⟨v, h, lag, margin, ver, rfl⟩
  · exact Or.inl (copyOrBack_matched (copyInv_step_shape hCopyInv hStep) hMatched)
  · rcases chainStep_back_shape' hStep with ⟨v', rfl⟩ | ⟨wv, rfl, hWatchLag⟩
    · cases hMatched with
      | back _ _ _ _ _ => exact Or.inl (Or.inr ⟨_, _, _, _, _, rfl⟩)
    · cases hMatched with
      | watch _ w' _ => exact Or.inr ⟨w', rfl⟩
      | breaks w w' hBreak =>
        have hZero : zero lag = true := by rw [← hWatchLag]; exact hBreak.1
        rw [zero_false_of_positive hLag] at hZero
        exact absurd hZero (by decide)

#print axioms chainStep_back_shape'
#print axioms backChain_tick_true_exists
#print axioms copyOrBack_tick_true_exists
#print axioms copyOrBack_tick_true

end PalPeg.CopyPhaseTickMatched
