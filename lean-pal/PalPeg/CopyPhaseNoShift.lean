import PalPeg.CopyPhaseTickMatched

/-!
# copy/back 相では不一致の行き先に shift guard が立たない

`CloseoutWatchRound22.WatchMismatchNoShiftC` の 2 節を、watch ラウンドの機械
（`CloseoutWatchRound23.watchMismatchNoShiftC_of_split` ← `TerminalRunFallbackGC`）を
**経由せずに** copy/back 相で直接出す。

| 節 | 材料 |
|---|---|
| `∃ z, ChainTick false s1.chain z` | `CopyPhaseTick.copyOrBack_tick_false_exists` |
| `∀ vs vq, ChainTick false … → ¬ shiftGuardVM (afterMismatch …)` | 下の `not_shiftGuardVM_of_copyOrBack_tick` |

第 2 節の内訳:

* `.copy` から出た 1 手は `.copy` か `.back`（`chainStep_copy_shape`）で **watch ではない**
* `.back` から `backDone` で生まれた watch は **lag をそのまま受け継ぐ**
  （`CopyPhaseTickMatched.chainStep_back_shape'`）。誕生した chain の lag は正なので
  `shiftGuardVM` の `zero w.lag = true` が落ちる

**`≠ idle` だけでは足りない**（n130）: `ChainStep` が `.copy` から出るには `CopyInv` が要る。
`CopyOrBack` はそれを含むので両節とも出る。

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.CopyPhaseNoShift

open PalPeg PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilScaffoldController
open GalilScaffoldCounter GalilScaffoldChainVerifier GalilScaffoldInputHead
open PalPeg.GalilScaffoldTop
open PalPeg.CopyPhaseTick PalPeg.CopyPhaseTickMatched

/-- **copy/back の background 1 手の行き先は、watch でないか、lag が正の watch。** -/
theorem tick_false_not_watch_or_posLag {x z : ChainVM}
    (hPhase : CopyOrBack x) (hLag : LagPos x) (hTick : ChainTick false x z) :
    (∀ w : GalilScaffoldChainWatch.State, z ≠ ChainVM.watch w) ∨
      (∃ w : GalilScaffoldChainWatch.State, z = ChainVM.watch w ∧ zero w.lag = false) := by
  obtain ⟨y, hStep, hAfter⟩ := hTick
  have hzy : z = y := hAfter
  subst hzy
  rcases hPhase with ⟨t, h, p, v, lag, margin, ver, m, rfl, hCopyInv⟩ | ⟨v, h, lag, margin, ver, rfl⟩
  · refine Or.inl (fun w => ?_)
    rcases chainStep_copy_shape hStep with ⟨t', h', p', v', margin', rfl⟩ | ⟨v', h', margin', rfl⟩ <;>
      intro hEq <;> exact ChainVM.noConfusion hEq
  · rcases chainStep_back_shape' hStep with ⟨v', rfl⟩ | ⟨wv, rfl, hWatchLag⟩
    · exact Or.inl (fun w hEq => ChainVM.noConfusion hEq)
    · exact Or.inr ⟨wv, rfl, by rw [hWatchLag]; exact zero_false_of_positive hLag⟩

/-- **copy/back 相では不一致の行き先に shift guard は立たない。**
`WatchMismatchNoShiftC` の第 2 節を watch ラウンドの機械を経由せずに出す。 -/
theorem not_shiftGuardVM_of_copyOrBack_tick {s1 : GalilVM} {vs : ScanVM} {vq : SearchVM}
    (hPhase : CopyOrBack s1.chain) (hLag : LagPos s1.chain)
    (hTick : ChainTick false s1.chain vs.chain) :
    ¬ shiftGuardVM (afterMismatch s1 vs vq) := by
  intro hGuard
  obtain ⟨w, hw, hZeroLag, -, -, -, -⟩ := hGuard
  rw [afterMismatch_chain] at hw
  rcases tick_false_not_watch_or_posLag hPhase hLag hTick with hNot | ⟨w', hEq, hPos⟩
  · exact hNot w hw
  · rw [hw] at hEq
    cases hEq
    rw [hPos] at hZeroLag
    exact absurd hZeroLag (by decide)

/-- **`WatchMismatchNoShiftC` の 2 節が copy/back 相でそろう。** -/
theorem watchMismatchNoShift_parts_of_copyOrBack {s1 : GalilVM}
    (hPhase : CopyOrBack s1.chain) (hLag : LagPos s1.chain) :
    (∃ z : ChainVM, ChainTick false s1.chain z) ∧
      (∀ (vs : ScanVM) (vq : SearchVM), ChainTick false s1.chain vs.chain →
        ¬ shiftGuardVM (afterMismatch s1 vs vq)) :=
  ⟨copyOrBack_tick_false_exists hPhase,
    fun _ _ hTick => not_shiftGuardVM_of_copyOrBack_tick hPhase hLag hTick⟩

#print axioms tick_false_not_watch_or_posLag
#print axioms not_shiftGuardVM_of_copyOrBack_tick
#print axioms watchMismatchNoShift_parts_of_copyOrBack


/-! ## 「tick できる相」 -/

/-- **tick できる相**: lag が正の `CopyOrBack` か、watch。
`≠ idle` では足りない（`ChainStep` が `.copy` から出るには `CopyInv` が要る）。 -/
def TickablePhase (s : GalilVM) : Prop :=
  (CopyOrBack s.chain ∧ LagPos s.chain) ∨
    (∃ w : GalilScaffoldChainWatch.State, s.chain = ChainVM.watch w)

/-- **`LiveScanWatch` を「tick できる相」に広げた版。**  fallback 系の契約はこれで足りる。 -/
def LiveScanTickable (c : Control) (s : GalilVM) : Prop :=
  c.mode = Mode.scan ∧ c.replaying = false ∧ 1 ≤ c.clock ∧ TickablePhase s

theorem liveScanTickable_ne_idle {c : Control} {s : GalilVM} (h : LiveScanTickable c s) :
    s.chain ≠ ChainVM.idle := by
  rcases h.2.2.2 with ⟨hPhase, -⟩ | ⟨w, hw⟩
  · exact copyOrBack_not_idle hPhase
  · rw [hw]; exact ChainVM.noConfusion

#print axioms liveScanTickable_ne_idle

end PalPeg.CopyPhaseNoShift
