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



/-! ## 一致事象でも同じ（`ShiftPal` の `periodOnly = false` 分岐に効く） -/

/-- **copy/back の 1 手の行き先は、watch でないか、lag が正の watch**——事象によらず。

`a = true` の枝: `.back` から `backDone` で生まれた watch に `ChainMatched` を当てると
`Outer.queued`（lag を `inc`、正値を保つ）か `ChainMatched.breaks`（`BreakStep` が
`zero w.lag = true` を要求するので lag 正では不可能）。 -/
theorem tick_not_watch_or_posLag {a : Bool} {x z : ChainVM}
    (hPhase : CopyOrBack x) (hLag : LagPos x) (hTick : ChainTick a x z) :
    (∀ w : GalilScaffoldChainWatch.State, z ≠ ChainVM.watch w) ∨
      (∃ w : GalilScaffoldChainWatch.State, z = ChainVM.watch w ∧ zero w.lag = false) := by
  obtain ⟨y, hStep, hAfter⟩ := hTick
  cases a with
  | false => exact tick_false_not_watch_or_posLag hPhase hLag ⟨y, hStep, hAfter⟩
  | true =>
    have hMatched : ChainMatched y z := hAfter
    rcases hPhase with ⟨t, h, p, v, lag, margin, ver, m, rfl, hCopyInv⟩ |
      ⟨v, h, lag, margin, ver, rfl⟩
    · rcases chainStep_copy_shape hStep with ⟨t', h', p', v', margin', rfl⟩ |
        ⟨v', h', margin', rfl⟩
      · cases hMatched with
        | copy _ _ _ _ _ _ _ => exact Or.inl (fun w hEq => ChainVM.noConfusion hEq)
      · cases hMatched with
        | back _ _ _ _ _ => exact Or.inl (fun w hEq => ChainVM.noConfusion hEq)
    · rcases chainStep_back_shape' hStep with ⟨v', rfl⟩ | ⟨wv, rfl, hWatchLag⟩
      · cases hMatched with
        | back _ _ _ _ _ => exact Or.inl (fun w hEq => ChainVM.noConfusion hEq)
      · have hPosWv : positive wv.lag = true := by rw [hWatchLag]; exact hLag
        have hZeroFalse : zero wv.lag = false := zero_false_of_positive hPosWv
        cases hMatched with
        | watch w w' hOuter =>
          cases hOuter with
          | queued hz => exact Or.inr ⟨_, rfl, zero_false_of_positive (positive_inc hPosWv)⟩
          | immediate hz hg =>
            rw [hZeroFalse] at hz; exact absurd hz (by decide)
        | breaks w w' hBreak =>
          have hz := hBreak.1
          rw [hZeroFalse] at hz; exact absurd hz (by decide)

#print axioms tick_not_watch_or_posLag


/-! ## lag は要らなかった — `phase` で落ちる

`shiftGuardVM` は `w.machine.control.phase = 4` を要求する。
`ChainStep.backDone` で生まれた watch の control は `watchControl v` で、
そのフィールド順は `period, distance, boundary, last, phase, forward, broken`
（`GalilScaffoldChainConsume:15`）なので **`phase = 0`**。

1 tick 後も 4 にならない:
* `Outer.queued` は machine を触らない → phase 0
* `Outer.immediate` は `consume` を通すが、`phase := if boundaryEvent then advancePhase s.phase
  else s.phase` で `advancePhase 0 = ⟨min 4 1, _⟩ = 1`、不一致枝は `broken := true` で phase 不変
* `ChainMatched.breaks` の行き先は `.broken` で watch ではない

**つまり `ShiftPal` の空虚性に lag の正値は要らない**（n134 の `shiftPal_of_copyOrBack` は
`LagPos` を取っていたが、不要だった）。これで「found 時の半径が正」への依存がこの経路から消える。 -/

/-- `phase = 0` から `consume` しても 4 にはならない。 -/
theorem consume_phase_ne_four (c : GalilScaffoldChainConsume.State) (seen : Option (Fin 3))
    (h0 : c.phase = 0) : (GalilScaffoldChainConsume.consume c seen).phase ≠ 4 := by
  have hval : ((GalilScaffoldChainConsume.consume c seen).phase).val ≤ 1 := by
    simp only [GalilScaffoldChainConsume.consume, GalilScaffoldChainConsume.advancePhase, h0]
    repeat' split
    all_goals simp
  intro hEq
  rw [hEq] at hval
  exact absurd hval (by decide)

/-- **`backDone` 生まれの watch は 1 tick 後も phase ≠ 4。** -/
theorem tick_watch_phase_ne_four {a : Bool} {x z : ChainVM}
    (hPhase : CopyOrBack x) (hTick : ChainTick a x z)
    (w : GalilScaffoldChainWatch.State) (hEq : z = ChainVM.watch w) :
    w.machine.control.phase ≠ 4 := by
  obtain ⟨y, hStep, hAfter⟩ := hTick
  rcases hPhase with ⟨t, h, p, v, lag, margin, ver, m, rfl, hCopyInv⟩ |
    ⟨v, h, lag, margin, ver, rfl⟩
  · exfalso
    exact PalPeg.CopyPhaseTick.chainStep_copy_shape hStep |>.elim
      (fun ⟨t', h', p', v', margin', hy⟩ => by
        cases a
        · exact ChainVM.noConfusion (hEq.symm.trans ((hAfter : z = y).trans hy))
        · rw [hy] at hAfter
          cases hAfter with
          | copy _ _ _ _ _ _ _ => exact ChainVM.noConfusion hEq)
      (fun ⟨v', h', margin', hy⟩ => by
        cases a
        · exact ChainVM.noConfusion (hEq.symm.trans ((hAfter : z = y).trans hy))
        · rw [hy] at hAfter
          cases hAfter with
          | back _ _ _ _ _ => exact ChainVM.noConfusion hEq)
  · rcases chainStep_back_shape' hStep with ⟨v', hy⟩ | ⟨wv, hy, hWatchLag⟩
    · exfalso
      cases a
      · exact ChainVM.noConfusion (hEq.symm.trans ((hAfter : z = y).trans hy))
      · rw [hy] at hAfter
        cases hAfter with
        | back _ _ _ _ _ => exact ChainVM.noConfusion hEq
    · have hPhase0 : wv.machine.control.phase = 0 := by
        rw [hy] at hStep
        cases hStep with
        | backDone _ _ _ _ _ _ => rfl
      cases a
      · have : z = ChainVM.watch wv := (hAfter : z = y).trans hy
        rw [this] at hEq
        cases hEq
        exact hPhase0 ▸ (by decide)
      · rw [hy] at hAfter
        cases hAfter with
        | watch w0 w1 hOuter =>
          cases hOuter with
          | queued hz =>
            have : w = GalilScaffoldChainWatch.queued wv := by
              cases hEq; rfl
            rw [this]
            show (wv.machine).control.phase ≠ 4
            rw [hPhase0]; decide
          | immediate hz hg =>
            have : w = GalilScaffoldChainWatch.immediate wv := by
              cases hEq; rfl
            rw [this]
            show (GalilScaffoldChainVerifier.consume wv.machine).control.phase ≠ 4
            exact consume_phase_ne_four _ _ hPhase0
        | breaks w0 w1 hBreak => exact ChainVM.noConfusion hEq

#print axioms consume_phase_ne_four
#print axioms tick_watch_phase_ne_four


/-- **watch でない chain の 1 手の行き先は「watch でない」か「phase ≠ 4 の watch」。**

`CopyOrBack` も `CopyInv` も要らない——純粋に構成子の形だけ。

* `.idle` — 誕生すれば `chainStart` ＝ `.copy`、しなければ `.idle`。どちらも watch でない
* `.copy` — `copyBit` / `copyEnd` で `.copy` / `.back`
* `.back` — `backStep` で `.back`、`backDone` で `watchControl` の watch（`phase = 0`）
* `.broken` — `brokenIdle` で `.broken`（`ChainMatched` に `.broken` の構成子は無いので
  一致事象はそもそも起きない）
-/
theorem tick_watch_phase_ne_four_of_notWatch {a : Bool} {x z : ChainVM}
    (hNotWatch : ∀ wv : GalilScaffoldChainWatch.State, x ≠ ChainVM.watch wv)
    (hTick : ChainTick a x z)
    (w : GalilScaffoldChainWatch.State) (hEq : z = ChainVM.watch w) :
    w.machine.control.phase ≠ 4 := by
  obtain ⟨y, hStep, hAfter⟩ := hTick
  cases hStep with
  | idle =>
    cases a
    · exact absurd ((hAfter : z = ChainVM.idle).symm.trans hEq) (by simp)
    · cases (hAfter : ChainMatched ChainVM.idle z) with
      | idle => exact absurd hEq (by simp)
  | brokenIdle wb =>
    cases a
    · exact absurd ((hAfter : z = ChainVM.broken wb).symm.trans hEq) (by simp)
    · exact (by cases (hAfter : ChainMatched (ChainVM.broken wb) z))
  | copyBit _ _ _ _ _ _ _ _ _ _ _ =>
    cases a
    · exact absurd ((hAfter : z = _).symm.trans hEq) (by simp)
    · cases (hAfter : ChainMatched _ z) with
      | copy _ _ _ _ _ _ _ => exact absurd hEq (by simp)
  | copyEnd _ _ _ _ _ _ _ _ _ _ _ =>
    cases a
    · exact absurd ((hAfter : z = _).symm.trans hEq) (by simp)
    · cases (hAfter : ChainMatched _ z) with
      | back _ _ _ _ _ => exact absurd hEq (by simp)
  | backStep _ _ _ _ _ _ =>
    cases a
    · exact absurd ((hAfter : z = _).symm.trans hEq) (by simp)
    · cases (hAfter : ChainMatched _ z) with
      | back _ _ _ _ _ => exact absurd hEq (by simp)
  | backDone v h lag margin ver hf =>
    have hPhase0 :
        (⟨⟨ver, watchControl v⟩, lag, margin⟩ : GalilScaffoldChainWatch.State).machine.control.phase
          = 0 := rfl
    cases a
    · have hz : z = ChainVM.watch ⟨⟨ver, watchControl v⟩, lag, margin⟩ := hAfter
      rw [hz] at hEq
      cases hEq
      rw [hPhase0]; decide
    · cases (hAfter : ChainMatched (ChainVM.watch ⟨⟨ver, watchControl v⟩, lag, margin⟩) z) with
      | watch w0 w1 hOuter =>
        cases hOuter with
        | queued hzq =>
          have : w = GalilScaffoldChainWatch.queued ⟨⟨ver, watchControl v⟩, lag, margin⟩ := by
            cases hEq; rfl
          rw [this]
          show (⟨⟨ver, watchControl v⟩, lag, margin⟩ :
            GalilScaffoldChainWatch.State).machine.control.phase ≠ 4
          rw [hPhase0]; decide
        | immediate hzi hgi =>
          have : w = GalilScaffoldChainWatch.immediate ⟨⟨ver, watchControl v⟩, lag, margin⟩ := by
            cases hEq; rfl
          rw [this]
          show (GalilScaffoldChainVerifier.consume
            (⟨ver, watchControl v⟩ : GalilScaffoldChainVerifier.State)).control.phase ≠ 4
          exact consume_phase_ne_four _ _ hPhase0
      | breaks w0 w1 hBreak => exact absurd hEq (by simp)
  | watchStep w0 w1 hi => exact absurd rfl (hNotWatch w0)

#print axioms tick_watch_phase_ne_four_of_notWatch

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
