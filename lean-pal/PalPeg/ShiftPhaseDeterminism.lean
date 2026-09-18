import PalPeg.GalilScaffoldTopSearch

/-!
# shift 相は決定的

`GalilScaffoldTopRoundS.round_next` はラウンド 1 周を**構成**して、
`Steps … ⟨c, s⟩ ⟨…, shiftLens.set s2 ⟨t', .watch v, cycle⟩⟩` と
`CompareRounds h (toOnly s w0) 1 (toOnly (shiftLens.set s2 ⟨t', .watch v, cycle⟩) v)` を返す。
`RoundSeg`（したがって `OriginAt` の搬送）に使うには、**構成した着地と run の実際の着地が
同じ状態であること**が要る。

抽象 `Tick` 全体は決定的でない（`GalilTickDet`）が、**shift 相だけは無条件に決定的**:

* `shift_one` は `F.remainingPos s` を要求し、`shiftFrame.shiftOne` は
  `s' = ⟨shiftTick s.shift, .watch (chainShiftOne w), inc (inc s.cycle)⟩` と行き先を一意に決める
  （`w` は `s.chain = .watch w` で決まる）。制御は変わらない。
* `shift_done` は `¬ F.remainingPos s` を要求し、VM を変えず、出力 `o` は
  `refresh` が一意に決める。
* `remainingPos` の有無で 2 つの構成子は排他。

したがって `Fair` を持ち出さずに、shift 相の run は構成と一致する。

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.ShiftPhaseDeterminism

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier

/-- **出力の更新は一意。**  `onLetter` なら `leftFirst` と同値、さもなくば据え置き。 -/
theorem refresh_det {σ : Type} {F : Frame σ} {s : σ} {old o o' : Bool}
    (h1 : refresh F s old o) (h2 : refresh F s old o') : o = o' := by
  by_cases hOnLetter : F.onLetter s
  · have e1 := h1.1 hOnLetter
    have e2 := h2.1 hOnLetter
    cases o <;> cases o' <;> simp_all
  · rw [h1.2 hOnLetter, h2.2 hOnLetter]

/-- **1 単位の shift は行き先を一意に決める。** -/
theorem shiftOne_det {P : Shared} {q : ℕ} {first : Fin 9} {u v v' : GalilVM}
    (h1 : (galilFrameS P q first).shiftOne u v)
    (h2 : (galilFrameS P q first).shiftOne u v') : v = v' := by
  obtain ⟨⟨-, -, -, w, hw, hgv⟩, hset⟩ := h1
  obtain ⟨⟨-, -, -, w', hw', hgv'⟩, hset'⟩ := h2
  have hww : w = w' := by rw [hw] at hw'; cases hw'; rfl
  subst hww
  rw [hset, hset', hgv, hgv']

/-- **shift 相の tick は一意。**  `Fair` を使わない。 -/
theorem tick_shift_det {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ}
    {x y y' : State GalilVM} (hShift : x.ctl.mode = Mode.shift)
    (h1 : Tick (galilFrameS P q first) delay x y)
    (h2 : Tick (galilFrameS P q first) delay x y') : y = y' := by
  cases h1 with
  | shift_one c s s1 hm hp hOne =>
    cases h2 with
    | shift_one c2 s2 s1' hm2 hp2 hOne2 => rw [shiftOne_det hOne hOne2]
    | shift_done c2 s2 o2 hm2 hp2 ho2 => exact absurd hp hp2
    | init c2 s2 s2' hm2 _ => exact absurd (hm2.symm.trans hm) (by decide)
    | scan_wait c2 s2 s2' hm2 _ _ => exact absurd (hm2.symm.trans hm) (by decide)
    | scan_count c2 s2 s2' hm2 _ _ _ => exact absurd (hm2.symm.trans hm) (by decide)
    | scan_match c2 s2 s2' s2'' o2 hm2 _ _ _ _ _ _ =>
      exact absurd (hm2.symm.trans hm) (by decide)
    | scan_shift c2 s2 s2' s2'' hm2 _ _ _ _ _ _ _ =>
      exact absurd (hm2.symm.trans hm) (by decide)
    | scan_fallback c2 s2 s2' s2'' hm2 _ _ _ _ _ _ _ =>
      exact absurd (hm2.symm.trans hm) (by decide)
    | replayStart c2 s2 s2' o2 hm2 _ _ _ => exact absurd (hm2.symm.trans hm) (by decide)
    | restart c2 s2 s2' hm2 _ => exact absurd (hm2.symm.trans hm) (by decide)
    | copy_one c2 s2 s2' hm2 _ _ => exact absurd (hm2.symm.trans hm) (by decide)
    | copy_done c2 s2 s2' hm2 _ _ => exact absurd (hm2.symm.trans hm) (by decide)
    | home_start c2 s2 s2' hm2 _ _ => exact absurd (hm2.symm.trans hm) (by decide)
    | home_step c2 s2 s2' hm2 _ _ => exact absurd (hm2.symm.trans hm) (by decide)
    | fpp_slice c2 s2 s2' hm2 _ => exact absurd (hm2.symm.trans hm) (by decide)
    | fpp_done c2 s2 s2' hm2 _ => exact absurd (hm2.symm.trans hm) (by decide)
    | markEnd_step c2 s2 s2' hm2 _ _ => exact absurd (hm2.symm.trans hm) (by decide)
    | markEnd_found c2 s2 s2' hm2 _ _ => exact absurd (hm2.symm.trans hm) (by decide)
    | choose_select c2 s2 s2' hm2 _ _ _ => exact absurd (hm2.symm.trans hm) (by decide)
    | choose_step c2 s2 s2' hm2 _ _ => exact absurd (hm2.symm.trans hm) (by decide)
    | rewind_done c2 s2 s2' hm2 _ _ => exact absurd (hm2.symm.trans hm) (by decide)
    | rewind_one c2 s2 s2' hm2 _ _ _ => exact absurd (hm2.symm.trans hm) (by decide)
    | rewind_pair c2 s2 s2' hm2 _ _ _ => exact absurd (hm2.symm.trans hm) (by decide)
  | shift_done c s o hm hp ho =>
    cases h2 with
    | shift_done c2 s2 o2 hm2 hp2 ho2 => rw [refresh_det ho ho2]
    | shift_one c2 s2 s1' hm2 hp2 hOne2 => exact absurd hp2 hp
    | init c2 s2 s2' hm2 _ => exact absurd (hm2.symm.trans hm) (by decide)
    | scan_wait c2 s2 s2' hm2 _ _ => exact absurd (hm2.symm.trans hm) (by decide)
    | scan_count c2 s2 s2' hm2 _ _ _ => exact absurd (hm2.symm.trans hm) (by decide)
    | scan_match c2 s2 s2' s2'' o2 hm2 _ _ _ _ _ _ =>
      exact absurd (hm2.symm.trans hm) (by decide)
    | scan_shift c2 s2 s2' s2'' hm2 _ _ _ _ _ _ _ =>
      exact absurd (hm2.symm.trans hm) (by decide)
    | scan_fallback c2 s2 s2' s2'' hm2 _ _ _ _ _ _ _ =>
      exact absurd (hm2.symm.trans hm) (by decide)
    | replayStart c2 s2 s2' o2 hm2 _ _ _ => exact absurd (hm2.symm.trans hm) (by decide)
    | restart c2 s2 s2' hm2 _ => exact absurd (hm2.symm.trans hm) (by decide)
    | copy_one c2 s2 s2' hm2 _ _ => exact absurd (hm2.symm.trans hm) (by decide)
    | copy_done c2 s2 s2' hm2 _ _ => exact absurd (hm2.symm.trans hm) (by decide)
    | home_start c2 s2 s2' hm2 _ _ => exact absurd (hm2.symm.trans hm) (by decide)
    | home_step c2 s2 s2' hm2 _ _ => exact absurd (hm2.symm.trans hm) (by decide)
    | fpp_slice c2 s2 s2' hm2 _ => exact absurd (hm2.symm.trans hm) (by decide)
    | fpp_done c2 s2 s2' hm2 _ => exact absurd (hm2.symm.trans hm) (by decide)
    | markEnd_step c2 s2 s2' hm2 _ _ => exact absurd (hm2.symm.trans hm) (by decide)
    | markEnd_found c2 s2 s2' hm2 _ _ => exact absurd (hm2.symm.trans hm) (by decide)
    | choose_select c2 s2 s2' hm2 _ _ _ => exact absurd (hm2.symm.trans hm) (by decide)
    | choose_step c2 s2 s2' hm2 _ _ => exact absurd (hm2.symm.trans hm) (by decide)
    | rewind_done c2 s2 s2' hm2 _ _ => exact absurd (hm2.symm.trans hm) (by decide)
    | rewind_one c2 s2 s2' hm2 _ _ _ => exact absurd (hm2.symm.trans hm) (by decide)
    | rewind_pair c2 s2 s2' hm2 _ _ _ => exact absurd (hm2.symm.trans hm) (by decide)
  | init c s s' hm _ => exact absurd (hm.symm.trans hShift) (by decide)
  | scan_wait c s s' hm _ _ => exact absurd (hm.symm.trans hShift) (by decide)
  | scan_count c s s' hm _ _ _ => exact absurd (hm.symm.trans hShift) (by decide)
  | scan_match c s s' s'' o hm _ _ _ _ _ _ => exact absurd (hm.symm.trans hShift) (by decide)
  | scan_shift c s s' s'' hm _ _ _ _ _ _ _ => exact absurd (hm.symm.trans hShift) (by decide)
  | scan_fallback c s s' s'' hm _ _ _ _ _ _ _ => exact absurd (hm.symm.trans hShift) (by decide)
  | replayStart c s s' o hm _ _ _ => exact absurd (hm.symm.trans hShift) (by decide)
  | restart c s s' hm _ => exact absurd (hm.symm.trans hShift) (by decide)
  | copy_one c s s' hm _ _ => exact absurd (hm.symm.trans hShift) (by decide)
  | copy_done c s s' hm _ _ => exact absurd (hm.symm.trans hShift) (by decide)
  | home_start c s s' hm _ _ => exact absurd (hm.symm.trans hShift) (by decide)
  | home_step c s s' hm _ _ => exact absurd (hm.symm.trans hShift) (by decide)
  | fpp_slice c s s' hm _ => exact absurd (hm.symm.trans hShift) (by decide)
  | fpp_done c s s' hm _ => exact absurd (hm.symm.trans hShift) (by decide)
  | markEnd_step c s s' hm _ _ => exact absurd (hm.symm.trans hShift) (by decide)
  | markEnd_found c s s' hm _ _ => exact absurd (hm.symm.trans hShift) (by decide)
  | choose_select c s s' hm _ _ _ => exact absurd (hm.symm.trans hShift) (by decide)
  | choose_step c s s' hm _ _ => exact absurd (hm.symm.trans hShift) (by decide)
  | rewind_done c s s' hm _ _ => exact absurd (hm.symm.trans hShift) (by decide)
  | rewind_one c s s' hm _ _ _ => exact absurd (hm.symm.trans hShift) (by decide)
  | rewind_pair c s s' hm _ _ _ => exact absurd (hm.symm.trans hShift) (by decide)

#print axioms refresh_det
#print axioms shiftOne_det
#print axioms tick_shift_det


/-- **shift 相を通る run は着地が一意。**  中間状態（着地を除く）がすべて shift 相なら、
同じ長さの 2 本の run は同じ状態に着く。`Fair` は要らない。 -/
theorem steps_shift_det {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ} :
    ∀ {k : ℕ} {x y y' : State GalilVM},
      (∀ (m : ℕ) (z : State GalilVM),
        Steps (galilFrameS P q first) delay m x z → m < k → z.ctl.mode = Mode.shift) →
      Steps (galilFrameS P q first) delay k x y →
      Steps (galilFrameS P q first) delay k x y' → y = y' := by
  intro k
  induction k with
  | zero =>
    intro x y y' _ h1 h2
    cases h1; cases h2; rfl
  | succ n ih =>
    intro x y y' hShiftBefore h1 h2
    cases h1 with
    | succ hTick1 hRest1 =>
      cases h2 with
      | succ hTick2 hRest2 =>
        have hShiftX : x.ctl.mode = Mode.shift := hShiftBefore 0 x (.zero x) (by omega)
        have hSame := tick_shift_det hShiftX hTick1 hTick2
        subst hSame
        exact ih (fun m z hz hm => hShiftBefore (m + 1) z (.succ hTick1 hz) (by omega))
          hRest1 hRest2

#print axioms steps_shift_det


/-- **shift 相の出口は状態も長さも一意。**  途中がすべて shift 相で、着地が shift 相を
出ているなら、2 本の run は同じ状態に同じ歩数で着く。

これで `round_next` の**構成した着地**と run の**実際の着地**が同一視できる
（`round_next` の shift 部分は `shift_steps_S` で `galilFrameS` の `Steps` になっている）。
長さを仮定しなくてよいのがポイント: 出口の一意性が長さまで決める。 -/
theorem steps_shift_exit_unique {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ} :
    ∀ {k : ℕ} {x y : State GalilVM},
      Steps (galilFrameS P q first) delay k x y →
      (∀ (m : ℕ) (w : State GalilVM),
        Steps (galilFrameS P q first) delay m x w → m < k → w.ctl.mode = Mode.shift) →
      y.ctl.mode ≠ Mode.shift →
      ∀ {k' : ℕ} {z : State GalilVM},
        Steps (galilFrameS P q first) delay k' x z →
        (∀ (m : ℕ) (w : State GalilVM),
          Steps (galilFrameS P q first) delay m x w → m < k' → w.ctl.mode = Mode.shift) →
        z.ctl.mode ≠ Mode.shift →
        y = z ∧ k = k' := by
  intro k x y h1
  induction h1 with
  | zero u =>
    intro _ hExit1 k' z h2 hShiftBefore2 _
    cases h2 with
    | zero _ => exact ⟨rfl, rfl⟩
    | succ hTick2 hRest2 =>
      exact absurd (hShiftBefore2 0 u (.zero u) (by omega)) hExit1
  | @succ n u w1 y hTick1 hRest1 ih =>
    intro hShiftBefore1 hExit1 k' z h2 hShiftBefore2 hExit2
    have hShiftU : u.ctl.mode = Mode.shift := hShiftBefore1 0 u (.zero u) (by omega)
    cases h2 with
    | zero _ => exact absurd hShiftU hExit2
    | @succ n' _ w2 _ hTick2 hRest2 =>
      have hSame : w1 = w2 := tick_shift_det hShiftU hTick1 hTick2
      subst hSame
      obtain ⟨hEq, hLen⟩ :=
        ih (fun m w hw hm => hShiftBefore1 (m + 1) w (.succ hTick1 hw) (by omega)) hExit1
          hRest2 (fun m w hw hm => hShiftBefore2 (m + 1) w (.succ hTick1 hw) (by omega)) hExit2
      exact ⟨hEq, by omega⟩

#print axioms steps_shift_exit_unique

end PalPeg.ShiftPhaseDeterminism
