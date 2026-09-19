import PalPeg.WindowInv

/-!
# `ChainWindowRun` — run 層の窓不変量（VM 遷移ごとの transport）

`obligation_shiftPalResiduesAlongRun` の残差（不一致比較の直前の誕生 anchor 窓）を run に沿って
運ぶための、`State GalilVM` 上の不変量。chain 側は `WindowInv`（`WindowInv.lean`）、ここでは
右ヘッドの位置 `position s.right` を chain の `R` に結び、中心のずれ（scan では
`center = cen₀ + k·h`、shift 中は `center + remaining = cen₀ + (k+1)·h`）を持つ。

VM 遷移ごとの補題（この file で順に埋める）:

* `chainWindowRun_chainStep` — 中心・右ヘッド・`remaining` を動かさない chain 1 歩
  （`backgroundS` の `chainAt false`、scan モード）
* 誕生／一致比較／shift 入口／shift 相／idle 化は次

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false

namespace PalPeg.WindowRun

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilReplayGeneral2 PalPeg.GalilBranchInvariants PalPeg.ShiftPalAlongTrace
open PalPeg.WindowInv PalPeg.GalilRunSkeleton

/-- **run 層の窓不変量。** -/
def ChainWindowRun (raw : List (Fin 2)) (c : Control) (s : GalilVM) : Prop :=
  ∃ (cen₀ : ℕ) (cc : Fin 3),
    (encoded raw)[cen₀]? = some cc ∧
    WindowInv raw cen₀ (position s.right) cc s.chain ∧
    (∀ w, s.chain = ChainVM.watch w →
      (c.mode = Mode.shift → ∃ k r, s.remaining = ofNat r ∧
        position s.center + r = cen₀ + (k + 1) * periodLength w) ∧
      (c.mode ≠ Mode.shift → ∃ k, position s.center = cen₀ + k * periodLength w)) ∧
    (∀ t h p v lag m ver, s.chain = ChainVM.copy t h p v lag m ver → position s.center = cen₀) ∧
    (∀ v h lag m ver, s.chain = ChainVM.back v h lag m ver → position s.center = cen₀)

/-- `encoded raw` の末尾は `2`: idle／broken の chain に anchor の証人を与える。 -/
theorem encoded_witness (raw : List (Fin 2)) : ∃ i : ℕ, (encoded raw)[i]? = some 2 := by
  unfold encoded
  exact ⟨_, List.getElem?_concat_length⟩

theorem chainWindowRun_of_idle {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    (h : s.chain = ChainVM.idle) : ChainWindowRun raw c s := by
  obtain ⟨i, hi⟩ := encoded_witness raw
  exact ⟨i, 2, hi, (by rw [h]; trivial),
    fun _ hw => (by rw [h] at hw; cases hw),
    fun _ _ _ _ _ _ _ hw => (by rw [h] at hw; cases hw),
    fun _ _ _ _ _ hw => (by rw [h] at hw; cases hw)⟩

theorem chainWindowRun_of_broken {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    {w : GalilScaffoldChainWatch.State} (h : s.chain = ChainVM.broken w) :
    ChainWindowRun raw c s := by
  obtain ⟨i, hi⟩ := encoded_witness raw
  exact ⟨i, 2, hi, (by rw [h]; trivial),
    fun _ hw => (by rw [h] at hw; cases hw),
    fun _ _ _ _ _ _ _ hw => (by rw [h] at hw; cases hw),
    fun _ _ _ _ _ hw => (by rw [h] at hw; cases hw)⟩

#print axioms chainWindowRun_of_idle

/-- `periodLength` は `WatchWindow` を保つ遷移で不変（両端で `|xs| + 1`）。 -/
theorem periodLength_step {raw : List (Fin 2)} {cen₀ R R' : ℕ} {cc b : Fin 3} {xs : List (Fin 3)}
    {w w' : GalilScaffoldChainWatch.State}
    (hw : WatchWindow raw cen₀ R cc b xs (ChainVM.watch w))
    (hw' : WatchWindow raw cen₀ R' cc b xs (ChainVM.watch w')) :
    periodLength w' = periodLength w := by
  rw [periodLength_of_coreP hw'.2.2, periodLength_of_coreP hw.2.2]

/-- **中心・右ヘッド・`remaining` を動かさない chain 1 歩（`ChainStep`、scan モード）は不変量を保つ。** -/
theorem chainWindowRun_chainStep {raw : List (Fin 2)} {c c' : Control} {s s' : GalilVM}
    (hscan : c.mode = Mode.scan) (hmode : c'.mode = c.mode)
    (hcenter : s'.center = s.center) (hright : s'.right = s.right)
    (hrem : s'.remaining = s.remaining)
    (hstep : ChainStep s.chain s'.chain) (hx : ChainWindowRun raw c s) :
    ChainWindowRun raw c' s' := by
  obtain ⟨cen₀, cc, hcs, hinv, hwatch, hcopy, hback⟩ := hx
  have hnotShift : c'.mode ≠ Mode.shift := by rw [hmode, hscan]; decide
  have hnotShift₀ : c.mode ≠ Mode.shift := by rw [hscan]; decide
  refine ⟨cen₀, cc, hcs, by rw [hright]; exact windowInv_step hinv hstep, ?_, ?_, ?_⟩
  · intro w hw
    refine ⟨fun hsh => absurd hsh hnotShift, fun _hns => ?_⟩
    rw [hcenter]
    generalize hy : s'.chain = y at hstep hw
    generalize hx' : s.chain = x at hstep hinv hwatch hcopy hback
    cases hstep with
    | idle => cases hw
    | brokenIdle _ => cases hw
    | copyBit _ _ _ _ _ _ _ _ _ _ _ => cases hw
    | copyEnd _ _ _ _ _ _ _ _ _ _ _ => cases hw
    | backStep _ _ _ _ _ _ => cases hw
    | backDone v hh lag margin ver hf =>
      -- the first round of the fresh watch, `k = 0`
      cases hw
      exact ⟨0, by rw [hback _ _ _ _ _ rfl]; ring⟩
    | watchStep w₀ w₁ hi =>
      cases hw
      obtain ⟨b, xs, hw₀⟩ := hinv
      rw [periodLength_step hw₀ (watchWindow_step hw₀ hi)]
      exact (hwatch w₀ rfl).2 hnotShift₀
  · intro t hh p v lag m ver hw
    rw [hcenter]
    generalize hy : s'.chain = y at hstep hw
    generalize hx' : s.chain = x at hstep hinv hwatch hcopy hback
    cases hstep <;> (try cases hw)
    exact hcopy _ _ _ _ _ _ _ rfl
  · intro v hh lag m ver hw
    rw [hcenter]
    generalize hy : s'.chain = y at hstep hw
    generalize hx' : s.chain = x at hstep hinv hwatch hcopy hback
    cases hstep <;> (try cases hw)
    · exact hcopy _ _ _ _ _ _ _ rfl
    · exact hback _ _ _ _ _ rfl

#print axioms chainWindowRun_chainStep


/-- **誕生（`chainStart`）**: idle だった chain が found で始まる。中心ヘッドが verifier、
半径カウンタが lag、窓の anchor は現在の中心、その記号は `P.centre s`。 -/
theorem chainWindowRun_birth {raw : List (Fin 2)} {c' : Control} {s s' : GalilVM} {R' : ℕ}
    {cc : Fin 3} (answer : GalilScaffoldTape.Tape) (walker : GalilScaffoldPlace.Place)
    (hcen : GalilScaffoldInputTrace.Represents s.center.head raw ∧ s.center.head.focus ≠ none)
    (hrad : RadiusRep s.radius R') (hR : position s.right = position s.center + R')
    (hcs : (encoded raw)[position s.center]? = some cc)
    (hcenter : s'.center = s.center) (hright : s'.right = s.right)
    (hchain : s'.chain = chainStart answer cc walker s.center s.radius) :
    ChainWindowRun raw c' s' := by
  refine ⟨position s.center, cc, hcs, ?_, ?_, ?_, ?_⟩
  · rw [hright, hR, hchain]
    exact windowInv_start answer walker ⟨hcen.1, hcen.2, rfl⟩ hrad
  · intro w hw; rw [hchain] at hw; cases hw
  · intro _ _ _ _ _ _ _ _; rw [hcenter]
  · intro _ _ _ _ _ hw; rw [hchain] at hw; cases hw

#print axioms chainWindowRun_birth

/-- **誕生と同じ tick での一致**（`chainAt true` の第 3 選言）: `chainStart` に `ChainMatched`。 -/
theorem chainWindowRun_birth_matched {raw : List (Fin 2)} {c' : Control} {s s' : GalilVM}
    {R' : ℕ} {cc : Fin 3} (answer : GalilScaffoldTape.Tape) (walker : GalilScaffoldPlace.Place)
    (hcen : GalilScaffoldInputTrace.Represents s.center.head raw ∧ s.center.head.focus ≠ none)
    (hrad : RadiusRep s.radius R') (hR : position s.right = position s.center + R')
    (hcs : (encoded raw)[position s.center]? = some cc)
    (hcenter : s'.center = s.center) (hright : position s'.right = position s.right + 1)
    (hm : ChainMatched (chainStart answer cc walker s.center s.radius) s'.chain) :
    ChainWindowRun raw c' s' := by
  refine ⟨position s.center, cc, hcs, ?_, ?_, ?_, ?_⟩
  · rw [hright, hR]
    exact windowInv_matched (windowInv_start answer walker ⟨hcen.1, hcen.2, rfl⟩ hrad) hm
  · intro w hw
    generalize hy : s'.chain = y at hm hw
    cases hm <;> cases hw
  · intro _ _ _ _ _ _ _ _; rw [hcenter]
  · intro _ _ _ _ _ hw
    generalize hy : s'.chain = y at hm hw
    cases hm <;> cases hw

#print axioms chainWindowRun_birth_matched

/-- **一致比較（`ChainTick true`）**: chain 1 歩＋`ChainMatched`、右ヘッド +1。 -/
theorem chainWindowRun_matched {raw : List (Fin 2)} {c c' : Control} {s s' : GalilVM}
    (hscan : c.mode = Mode.scan) (hmode : c'.mode = c.mode)
    (hcenter : s'.center = s.center) (hright : position s'.right = position s.right + 1)
    (hrem : s'.remaining = s.remaining)
    (htick : ChainTick true s.chain s'.chain) (hx : ChainWindowRun raw c s) :
    ChainWindowRun raw c' s' := by
  obtain ⟨y, hstep, hm⟩ := htick
  simp only [↓reduceIte] at hm
  obtain ⟨cen₀, cc, hcs, hinv, hwatch, hcopy, hback⟩ := hx
  have hnotShift : c'.mode ≠ Mode.shift := by rw [hmode, hscan]; decide
  have hnotShift₀ : c.mode ≠ Mode.shift := by rw [hscan]; decide
  have hinv' : WindowInv raw cen₀ (position s'.right) cc s'.chain := by
    rw [hright]; exact windowInv_matched (windowInv_step hinv hstep) hm
  refine ⟨cen₀, cc, hcs, hinv', ?_, ?_, ?_⟩
  · intro w hw
    refine ⟨fun hsh => absurd hsh hnotShift, fun _hns => ?_⟩
    rw [hcenter]
    generalize hz : s'.chain = z at hm hw hinv'
    generalize hx' : s.chain = x at hstep hinv hwatch hcopy hback
    cases hstep with
    | idle => cases hm; cases hw
    | brokenIdle _ => cases hm
    | copyBit _ _ _ _ _ _ _ _ _ _ _ => cases hm <;> cases hw
    | copyEnd _ _ _ _ _ _ _ _ _ _ _ => cases hm <;> cases hw
    | backStep _ _ _ _ _ _ => cases hm <;> cases hw
    | backDone v hh lag margin ver hf =>
      cases hm with
      | watch _ w' ho =>
        cases hw
        exact ⟨0, by rw [hback _ _ _ _ _ rfl]; ring⟩
      | breaks _ _ _ => cases hw
    | watchStep w₀ w₁ hi =>
      cases hm with
      | watch _ w' ho =>
        cases hw
        obtain ⟨b, xs, hw₀⟩ := hinv
        have hw₁ := watchWindow_step hw₀ hi
        rw [periodLength_step hw₀ (watchWindow_outer hw₁ ho)]
        exact (hwatch w₀ rfl).2 hnotShift₀
      | breaks _ _ _ => cases hw
  · intro t hh p v lag m ver hw
    rw [hcenter]
    generalize hz : s'.chain = z at hm hw hinv'
    generalize hx' : s.chain = x at hstep hinv hwatch hcopy hback
    cases hstep with
    | idle => cases hm; cases hw
    | brokenIdle _ => cases hm
    | copyBit _ _ _ _ _ _ _ _ _ _ _ =>
      cases hm with
      | copy _ _ _ _ _ _ _ => exact hcopy _ _ _ _ _ _ _ rfl
    | copyEnd _ _ _ _ _ _ _ _ _ _ _ => cases hm <;> cases hw
    | backStep _ _ _ _ _ _ => cases hm <;> cases hw
    | backDone _ _ _ _ _ _ => cases hm <;> cases hw
    | watchStep _ _ _ => cases hm <;> cases hw
  · intro v hh lag m ver hw
    rw [hcenter]
    generalize hz : s'.chain = z at hm hw hinv'
    generalize hx' : s.chain = x at hstep hinv hwatch hcopy hback
    cases hstep with
    | idle => cases hm; cases hw
    | brokenIdle _ => cases hm
    | copyBit _ _ _ _ _ _ _ _ _ _ _ => cases hm <;> cases hw
    | copyEnd _ _ _ _ _ _ _ _ _ _ _ =>
      cases hm with
      | back _ _ _ _ _ => exact hcopy _ _ _ _ _ _ _ rfl
    | backStep _ _ _ _ _ _ =>
      cases hm with
      | back _ _ _ _ _ => exact hback _ _ _ _ _ rfl
    | backDone _ _ _ _ _ _ => cases hm <;> cases hw
    | watchStep _ _ _ => cases hm <;> cases hw

#print axioms chainWindowRun_matched

/-- **shift 入口**: 不一致比較の chain 1 歩（`ChainTick false`）の後、guard（lag ゼロ・phase 4・
予測一致 `Good`）で `beginShiftVM` が `immediate` を掛ける。右ヘッド +1、`remaining = ofNat h`。 -/
theorem chainWindowRun_shift {raw : List (Fin 2)} {c c' : Control} {s s'' : GalilVM}
    {w : GalilScaffoldChainWatch.State}
    (hscan : c.mode = Mode.scan) (hmode : c'.mode = Mode.shift)
    (hstep : ChainStep s.chain (ChainVM.watch w))
    (hphase : w.machine.control.phase = 4) (hz : zero w.lag = true)
    (hg : GalilScaffoldChainWatch.Good w)
    (hcenter : s''.center = s.center) (hright : position s''.right = position s.right + 1)
    (hrem : s''.remaining = ofNat (periodLength w))
    (hchain : s''.chain = ChainVM.watch (GalilScaffoldChainWatch.immediate w))
    (hx : ChainWindowRun raw c s) :
    ChainWindowRun raw c' s'' := by
  obtain ⟨cen₀, cc, hcs, hinv, hwatch, hcopy, hback⟩ := hx
  have hnotShift₀ : c.mode ≠ Mode.shift := by rw [hscan]; decide
  have hinvW : WindowInv raw cen₀ (position s.right) cc (ChainVM.watch w) :=
    windowInv_step hinv hstep
  refine ⟨cen₀, cc, hcs, ?_, ?_, ?_, ?_⟩
  · rw [hright, hchain]; exact windowInv_immediate hinvW hz hg
  · intro w' hw'
    rw [hchain] at hw'
    cases hw'
    refine ⟨fun _ => ?_, fun hns => absurd hmode hns⟩
    -- `periodLength (immediate w) = periodLength w`
    obtain ⟨b, xs, hwW⟩ := hinvW
    have hplI : periodLength (GalilScaffoldChainWatch.immediate w) = periodLength w :=
      periodLength_step hwW (watchWindow_outer hwW (GalilScaffoldChainWatch.Outer.immediate w hz hg))
    rw [hplI, hrem, hcenter]
    -- the source watch had the same period, and its centre offset
    generalize hx' : s.chain = x at hstep hinv hwatch hcopy hback
    cases hstep with
    | backDone v hh lag margin ver hf =>
      -- a fresh watch has phase `0`, not `4`
      exfalso
      have h0 : (watchControl v).phase = 4 := hphase
      simp [watchControl] at h0
    | watchStep w₀ _ hi =>
      obtain ⟨b₀, xs₀, hw₀⟩ := hinv
      have hpl : periodLength w = periodLength w₀ := periodLength_step hw₀ (watchWindow_step hw₀ hi)
      obtain ⟨k, hk⟩ := (hwatch w₀ rfl).2 hnotShift₀
      refine ⟨k, periodLength w, rfl, ?_⟩
      rw [hk, hpl, add_one_mul]
      omega
  · intro _ _ _ _ _ _ _ hw; rw [hchain] at hw; cases hw
  · intro _ _ _ _ _ hw; rw [hchain] at hw; cases hw

#print axioms chainWindowRun_shift

/-- **shift の 1 歩**: 中心 +1、`remaining` −1、chain は `chainShiftOne`。 -/
theorem chainWindowRun_shiftOne {raw : List (Fin 2)} {c c' : Control} {s s' : GalilVM}
    {w : GalilScaffoldChainWatch.State}
    (hshift : c.mode = Mode.shift) (hmode : c'.mode = Mode.shift)
    (hw : s.chain = ChainVM.watch w) (hchain : s'.chain = ChainVM.watch (chainShiftOne w))
    (hcenter : position s'.center = position s.center + 1) (hright : s'.right = s.right)
    (hrem : s'.remaining = dec s.remaining) (hpos : positive s.remaining = true)
    (hx : ChainWindowRun raw c s) :
    ChainWindowRun raw c' s' := by
  obtain ⟨cen₀, cc, hcs, hinv, hwatch, hcopy, hback⟩ := hx
  refine ⟨cen₀, cc, hcs, ?_, ?_, ?_, ?_⟩
  · rw [hright, hchain]; rw [hw] at hinv; exact windowInv_shiftOne hinv
  · intro w' hw'
    rw [hchain] at hw'
    cases hw'
    refine ⟨fun _ => ?_, fun hns => absurd hmode hns⟩
    obtain ⟨k, r, hr, hk⟩ := (hwatch w hw).1 hshift
    rcases r with _ | r
    · rw [hr] at hpos; exact absurd hpos (by decide)
    · refine ⟨k, r, by rw [hrem, hr, dec_ofNat_succ], ?_⟩
      show position s'.center + r = cen₀ + (k + 1) * periodLength w
      rw [hcenter]; omega
  · intro _ _ _ _ _ _ _ hw'; rw [hchain] at hw'; cases hw'
  · intro _ _ _ _ _ hw'; rw [hchain] at hw'; cases hw'

#print axioms chainWindowRun_shiftOne

/-- **shift の終了**: `remaining` が尽きて scan へ戻る。中心は `cen₀ + (k+1)·h`。 -/
theorem chainWindowRun_shiftDone {raw : List (Fin 2)} {c c' : Control} {s : GalilVM}
    (hshift : c.mode = Mode.shift) (hmode : c'.mode = Mode.scan)
    (hnp : positive s.remaining = false) (hx : ChainWindowRun raw c s) :
    ChainWindowRun raw c' s := by
  obtain ⟨cen₀, cc, hcs, hinv, hwatch, hcopy, hback⟩ := hx
  refine ⟨cen₀, cc, hcs, hinv, ?_, hcopy, hback⟩
  intro w hw
  refine ⟨fun hsh => absurd hsh (by rw [hmode]; decide), fun _ => ?_⟩
  obtain ⟨k, r, hr, hk⟩ := (hwatch w hw).1 hshift
  rcases r with _ | r
  · exact ⟨k + 1, by omega⟩
  · rw [hr] at hnp; exact absurd hnp (by simp [positive, ofNat])

#print axioms chainWindowRun_shiftDone

end PalPeg.WindowRun
