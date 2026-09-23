import PalPeg.PhysicalShift

/-!
# Phase modes that do not touch a counter, on the common invariant

In `home`, `markEnd`, the back half of `choose` and `fpp` the tick moves only program and
mark tapes. The existing rule theorems (`home_of_tick`, …) give the tape encoding of the
successor; here the rest of the common invariant `CoreInv` is carried: the macro boundary,
the counter shapes (no counter slot is written) and the chain cache (the chain is untouched and
no mode here is `shift`).
-/
set_option autoImplicit false
namespace PalPeg.PhysicalPhaseStill
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract PalPeg.PhysicalScanCount
open PalPeg.Program (STape)
open PalPeg.Local (readWin pos)
open PalPeg.CloseoutCoreEnc12 PalPeg.LocalStepFusion
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilFinalAssembly2 (centreC placeC)

/-- The phase modes whose tick writes no counter. -/
def QuietPhase (m : PalPeg.GalilScaffoldController.Mode) : Prop :=
  m = .markEnd ∨ m = .home ∨ m = .fpp ∨ m = .choose

theorem chain_tickFun (w : List (Fin 2)) (x : State GalilVM) (hmode : QuietPhase x.ctl.mode) :
    (tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
      (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x).vm.chain
      = x.vm.chain := by
  unfold PalPeg.GalilScaffoldTop.tickFun
  rcases hmode with h | h | h | h <;> rw [h] <;> dsimp only <;> split <;> rfl

theorem mode_tickFun_ne_shift (w : List (Fin 2)) (x : State GalilVM)
    (hmode : QuietPhase x.ctl.mode) :
    (tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
      (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x).ctl.mode
      ≠ .shift := by
  unfold PalPeg.GalilScaffoldTop.tickFun
  rcases hmode with h | h | h | h <;> rw [h] <;> dsimp only <;> split <;> simp_all

/-- The chain cache reads the chain and whether the mode is `shift`, and two slots. -/
theorem cache_congr {x y : State GalilVM} {bit : Bool} {tape mirror : STape Γm}
    (h : PalPeg.PhysicalCacheInvariant.Cache x bit tape mirror)
    (hchain : y.vm.chain = x.vm.chain) (hx : x.ctl.mode ≠ .shift) (hy : y.ctl.mode ≠ .shift) :
    PalPeg.PhysicalCacheInvariant.Cache y bit tape mirror := by
  unfold PalPeg.PhysicalCacheInvariant.Cache at h ⊢
  rw [hchain]
  unfold PalPeg.PhysicalCacheInvariant.mirrorMagnitude at h ⊢
  simp only [hx, hy, if_false] at h ⊢
  exact h

/-- **The common invariant after a quiet phase tick**, from the tape encoding of the successor:
the counter, spare and mirror slots are not written, the polarity bits and the chain are kept, and
neither the source nor the successor is in `shift`. -/
theorem coreInv_of_ideal (rest : RestCommands) (w : List (Fin 2)) (x y : State GalilVM)
    (p : CoreState) (he : PalPeg.PhysicalCacheInvariant.CoreInv w x p)
    (hencoded : PalPeg.PhysicalEncoding.Enc w margin y
      ((idealRun (workRule rest) blankM p none 12).1,
        fun i => (idealRun (workRule rest) blankM p none 12).2 (slotIndex i)))
    (hacts : ∀ slot : Slot, (∀ v i, slot ≠ headSlot v i) →
      (∀ i, slot ≠ progSlotOf (!p.1.fppLive) i) → (∀ i, slot ≠ progSlot p.1.fppLive i) →
      ruleActs 1 0 p.1 (fun j => readWin blankM microRadius (p.2 j)) (slotIndex slot) = [])
    (hpol : (idealRun (workRule rest) blankM p none 12).1.polarity = p.1.polarity)
    (hchain : y.vm.chain = x.vm.chain) (hx : x.ctl.mode ≠ .shift) (hy : y.ctl.mode ≠ .shift) :
    PalPeg.PhysicalCacheInvariant.CoreInv w y (idealRun (workRule rest) blankM p none 12) := by
  have hcore : CoreEnc w x p := he.1.1
  have hb := PalPeg.PhysicalBoundary.macroBoundary_tickRule
    (fun q _ ws => ruleNext 1 0 fppBound_gt_start q ws) (modeCommands 0 rest)
    (fun q _ ws => ruleActs 1 0 q ws)
    (fun q _ ws j => ruleActs_length 1 0 (by decide : 1+3 ≤ microRadius) q ws j)
    w x p none hcore
  simp only [← tickPhysRule_eq 1 0 fppBound_gt_start (by decide) (by decide) rest,
    ← workRule_eq] at hb
  have hk : ∀ slot : Slot, (∀ v i, slot ≠ headSlot v i) →
      (∀ i, slot ≠ progSlotOf (!p.1.fppLive) i) → (∀ i, slot ≠ progSlot p.1.fppLive i) →
      (idealRun (workRule rest) blankM p none 12).2 (slotIndex slot) = p.2 (slotIndex slot) := by
    intro slot hhead hidle hlive
    rw [PalPeg.PhysicalShift.ideal_other rest p hcore.2.1 slot hhead, hacts slot hhead hidle hlive]
    rfl
  have hkc : ∀ c, (idealRun (workRule rest) blankM p none 12).2 (slotIndex (counterSlot c))
      = p.2 (slotIndex (counterSlot c)) := fun c =>
    hk (counterSlot c) (by intros; simp [counterSlot, headSlot])
      (by intro i; cases p.1.fppLive <;> simp [counterSlot, progSlotOf])
      (by intro i; cases p.1.fppLive <;> simp [counterSlot, progSlot, progSlotOf])
  have hkm : (idealRun (workRule rest) blankM p none 12).2 PalPeg.PhysicalPeriodMirror.mirrorIndex
      = p.2 PalPeg.PhysicalPeriodMirror.mirrorIndex :=
    hk (mirrorSlot 5) (by intros; simp [mirrorSlot, headSlot])
      (by intro i; cases p.1.fppLive <;> simp [mirrorSlot, progSlotOf])
      (by intro i; cases p.1.fppLive <;> simp [mirrorSlot, progSlot, progSlotOf])
  generalize idealRun (workRule rest) blankM p none 12 = result at hencoded hb hkc hkm hpol ⊢
  refine ⟨⟨⟨hencoded, hb⟩, ?_⟩, ?_⟩
  · intro c
    obtain ⟨seg, hs⟩ := he.1.2 c
    refine ⟨seg, ?_⟩
    change result.2 (slotIndex (counterSlot c)) = _
    rw [hkc c]
    exact hs
  · rw [hpol, show result.2 PalPeg.PhysicalSpare.spareIndex = p.2 PalPeg.PhysicalSpare.spareIndex
      from hkc 10, hkm]
    exact cache_congr he.2 hchain hx hy

/-- **The weakest frame for the common invariant.** Counters the VM names (all but the chain's
`10..15`) take their shape from the new encoding; only the chain's counters, the spare mirror and
polarity `10` must be kept. A tick may rewrite any VM-named counter and its sign. -/
theorem coreInv_of_ideal_named (rest : RestCommands) (w : List (Fin 2)) (x y : State GalilVM)
    (p : CoreState) (he : PalPeg.PhysicalCacheInvariant.CoreInv w x p)
    (hencoded : PalPeg.PhysicalEncoding.Enc w margin y
      ((idealRun (workRule rest) blankM p none 12).1,
        fun i => (idealRun (workRule rest) blankM p none 12).2 (slotIndex i)))
    (hkeep : ∀ slot : Slot, (slot = mirrorSlot 5 ∨ ∃ c : Fin 16, 10 ≤ c.val ∧ slot = counterSlot c) →
      (idealRun (workRule rest) blankM p none 12).2 (slotIndex slot) = p.2 (slotIndex slot))
    (hpol : (idealRun (workRule rest) blankM p none 12).1.polarity 10 = p.1.polarity 10)
    (hchain : y.vm.chain = x.vm.chain) (hx : x.ctl.mode ≠ .shift) (hy : y.ctl.mode ≠ .shift) :
    PalPeg.PhysicalCacheInvariant.CoreInv w y (idealRun (workRule rest) blankM p none 12) := by
  have hcore : CoreEnc w x p := he.1.1
  have hshape := he.1.2
  have hb := PalPeg.PhysicalBoundary.macroBoundary_tickRule
    (fun q _ ws => ruleNext 1 0 fppBound_gt_start q ws) (modeCommands 0 rest)
    (fun q _ ws => ruleActs 1 0 q ws)
    (fun q _ ws j => ruleActs_length 1 0 (by decide : 1+3 ≤ microRadius) q ws j)
    w x p none hcore
  simp only [← tickPhysRule_eq 1 0 fppBound_gt_start (by decide) (by decide) rest,
    ← workRule_eq] at hb
  generalize idealRun (workRule rest) blankM p none 12 = result at hencoded hb hkeep hpol ⊢
  refine ⟨⟨⟨hencoded, hb⟩, ?_⟩, ?_⟩
  · intro c
    by_cases hc : 10 ≤ c.val
    · obtain ⟨seg, hs⟩ := hshape c
      refine ⟨seg, ?_⟩
      change result.2 (slotIndex (counterSlot c)) = _
      rw [hkeep _ (.inr ⟨c, hc, rfl⟩)]
      exact hs
    · have hnamed : ∃ v, counterOf y c = some v := by
        fin_cases c <;> first | exact ⟨_, rfl⟩ | exact absurd (by decide) hc
      obtain ⟨v, hv⟩ := hnamed
      obtain ⟨seg, _, hs⟩ := hencoded.2.counters c v hv
      exact ⟨seg, hs⟩
  · rw [hpol, show result.2 PalPeg.PhysicalSpare.spareIndex = p.2 PalPeg.PhysicalSpare.spareIndex
      from hkeep (counterSlot 10) (.inr ⟨10, by decide, rfl⟩),
      show result.2 PalPeg.PhysicalPeriodMirror.mirrorIndex = p.2 PalPeg.PhysicalPeriodMirror.mirrorIndex
      from hkeep (mirrorSlot 5) (.inl rfl)]
    exact cache_congr he.2 hchain hx hy

/-- The acts of a tick that only walks one mark tape: nothing outside that tape. -/
theorem withErase_actsAt_other {K : ℕ} (live : Bool) (ws : Fin tapeCountM → PalPeg.Local.Window Γm K)
    (t : Fin 9) (base : Fin tapeCountM → List (Act Γm))
    (hbase : ∀ j, j ≠ slotIndex (progSlot live t) → base j = []) (slot : Slot)
    (hidle : ∀ i, slot ≠ progSlotOf (!live) i) (hlive : ∀ i, slot ≠ progSlot live i) :
    withErase live ws base (slotIndex slot) = [] := by
  rw [withErase_at_other live ws base slot hidle]
  exact hbase _ (fun h => hlive t (slotIndex.injective h))

section Modes
variable (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)

private theorem hm_of {mode : PalPeg.GalilScaffoldController.Mode}
    (he : PalPeg.PhysicalCacheInvariant.CoreInv w x p) (hmode : x.ctl.mode = mode) :
    p.1.ctl.mode = mode := by
  have hc := congrArg PalPeg.GalilScaffoldController.Control.mode he.1.1.1.1.ctl
  exact hc.trans hmode

/-- **`home` keeps the common invariant.** -/
theorem ideal_home (he : PalPeg.PhysicalCacheInvariant.CoreInv w x p)
    (hmode : x.ctl.mode = .home) :
    PalPeg.PhysicalCacheInvariant.CoreInv w
      (tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
        (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x)
      (idealRun (workRule rest) blankM p none 12) := by
  have hm := hm_of w x p he hmode
  have hcore : CoreEnc w x p := he.1.1
  have hencoded := home_of_tick margin centreC placeC 0 1 0 w
    (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x p.1
    (fun slot => p.2 (slotIndex slot)) rest none
    fppBound_gt_start (by decide : 1+3 ≤ microRadius) (by decide : 2 ≤ microRadius)
    (by decide : 1 ≤ microRadius) micro_le_margin (by decide : microRadius ≤ margin+1)
    hcore.2.1 hcore.2.2 hm hmode hcore.1
  have hT : tapesOf (fun slot => p.2 (slotIndex slot)) = p.2 := by funext j; simp [tapesOf]
  simp only [← workRule_eq, hT, Prod.eta] at hencoded
  have hq : QuietPhase x.ctl.mode := Or.inr (Or.inl hmode)
  refine coreInv_of_ideal rest w x _ p he hencoded (fun slot hhead hidle hlive => ?_) ?_
    (chain_tickFun w x hq) (by rw [hmode]; decide) (mode_tickFun_ne_shift w x hq)
  · simp only [ruleActs, hm]
    refine withErase_actsAt_other p.1.fppLive _ 7 _ (fun j hj => ?_) slot hidle hlive
    unfold homeActs
    split_ifs <;> simp only [actsAt, if_neg hj]
  · have hbits := (tickPhysRule_bits 1 0 fppBound_gt_start (by decide : 1+3 ≤ microRadius)
      (by decide : 2 ≤ microRadius) rest p.1 (fun slot => p.2 (slotIndex slot)) none
      hcore.2.1).1
    simp only [← workRule_eq, hT, Prod.eta] at hbits
    rw [hbits]
    simp only [ruleNext, hm, homeNext]
    split_ifs <;> rfl

/-- **`markEnd` keeps the common invariant.** -/
theorem ideal_markEnd (he : PalPeg.PhysicalCacheInvariant.CoreInv w x p)
    (hmode : x.ctl.mode = .markEnd) :
    PalPeg.PhysicalCacheInvariant.CoreInv w
      (tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
        (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x)
      (idealRun (workRule rest) blankM p none 12) := by
  have hm := hm_of w x p he hmode
  have hcore : CoreEnc w x p := he.1.1
  have hencoded := markEnd_of_tick margin centreC placeC 0 1 0 w
    (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x p.1
    (fun slot => p.2 (slotIndex slot)) rest none
    fppBound_gt_start (by decide : 1+3 ≤ microRadius) (by decide : 2 ≤ microRadius)
    (by decide : 1 ≤ microRadius) micro_le_margin (by decide : microRadius ≤ margin+1)
    hcore.2.1 hcore.2.2 hm hmode hcore.1
  have hT : tapesOf (fun slot => p.2 (slotIndex slot)) = p.2 := by funext j; simp [tapesOf]
  simp only [← workRule_eq, hT, Prod.eta] at hencoded
  have hq : QuietPhase x.ctl.mode := Or.inl hmode
  refine coreInv_of_ideal rest w x _ p he hencoded (fun slot hhead hidle hlive => ?_) ?_
    (chain_tickFun w x hq) (by rw [hmode]; decide) (mode_tickFun_ne_shift w x hq)
  · simp only [ruleActs, hm]
    refine withErase_actsAt_other p.1.fppLive _ 8 _ (fun j hj => ?_) slot hidle hlive
    unfold markEndActs
    split_ifs <;> simp only [actsAt, if_neg hj]
  · have hbits := (tickPhysRule_bits 1 0 fppBound_gt_start (by decide : 1+3 ≤ microRadius)
      (by decide : 2 ≤ microRadius) rest p.1 (fun slot => p.2 (slotIndex slot)) none
      hcore.2.1).1
    simp only [← workRule_eq, hT, Prod.eta] at hbits
    rw [hbits]
    simp only [ruleNext, hm, markEndNext]
    split_ifs <;> rfl

/-- **The back half of `choose` keeps the common invariant.** -/
theorem ideal_chooseBack (he : PalPeg.PhysicalCacheInvariant.CoreInv w x p)
    (hmode : x.ctl.mode = .choose)
    (hkeep : (x.ctl.odd && (decide ((x.vm.fpp.program.config.tapes 8).focus = 8)
        || decide ((x.vm.fpp.program.config.tapes 8).focus = 0))) = false) :
    PalPeg.PhysicalCacheInvariant.CoreInv w
      (tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
        (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x)
      (idealRun (workRule rest) blankM p none 12) := by
  have hm := hm_of w x p he hmode
  have hcore : CoreEnc w x p := he.1.1
  have hencoded := choose_back_of_tick margin centreC placeC 0 1 0 w
    (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x p.1
    (fun slot => p.2 (slotIndex slot)) rest none
    fppBound_gt_start (by decide : 1+3 ≤ microRadius) (by decide : 2 ≤ microRadius)
    (by decide : 1 ≤ microRadius) micro_le_margin (by decide : microRadius ≤ margin+1)
    hcore.2.1 hcore.2.2 hm hmode hkeep hcore.1
  have hT : tapesOf (fun slot => p.2 (slotIndex slot)) = p.2 := by funext j; simp [tapesOf]
  simp only [← workRule_eq, hT, Prod.eta] at hencoded
  have hq : QuietPhase x.ctl.mode := Or.inr (Or.inr (Or.inr hmode))
  refine coreInv_of_ideal rest w x _ p he hencoded (fun slot hhead hidle hlive => ?_) ?_
    (chain_tickFun w x hq) (by rw [hmode]; decide) (mode_tickFun_ne_shift w x hq)
  · simp only [ruleActs, hm]
    refine withErase_actsAt_other p.1.fppLive _ 8 _ (fun j hj => ?_) slot hidle hlive
    unfold chooseBackActs
    split_ifs <;> simp only [actsAt, if_neg hj]
  · have hbits := (tickPhysRule_bits 1 0 fppBound_gt_start (by decide : 1+3 ≤ microRadius)
      (by decide : 2 ≤ microRadius) rest p.1 (fun slot => p.2 (slotIndex slot)) none
      hcore.2.1).1
    simp only [← workRule_eq, hT, Prod.eta] at hbits
    rw [hbits]
    simp only [ruleNext, hm, chooseBackNext]

/-- **`fpp` keeps the common invariant**, given the program run's facts the rule theorem needs. -/
theorem ideal_fpp (he : PalPeg.PhysicalCacheInvariant.CoreInv w x p)
    (hmode : x.ctl.mode = .fpp)
    (hcomp : ∀ t : Fin 9, microRadius ≤ PalPeg.Local.pos (encTape (x.vm.fpp.program.config.tapes t)))
    (hfloorRun : ∀ k, ∀ t : Fin 9, ((PalPeg.ProgramFunction.runFun PalPeg.GalilFppMarkedCode.code
      (List.replicate k true) x.vm.fpp.program).config.tapes t).left ≠ [])
    (hin : x.vm.fpp.program.config.pc < fppBound) :
    PalPeg.PhysicalCacheInvariant.CoreInv w
      (tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
        (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x)
      (idealRun (workRule rest) blankM p none 12) := by
  have hm := hm_of w x p he hmode
  have hcore : CoreEnc w x p := he.1.1
  have hencoded := fpp_of_tick margin centreC placeC 0 1 0 w
    (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x p.1
    (fun slot => p.2 (slotIndex slot)) rest none
    fppBound_gt_start (by decide : 1+3 ≤ microRadius) (by decide : 2 ≤ microRadius)
    (by decide : 1 ≤ microRadius) micro_le_margin (by decide : microRadius ≤ margin+1)
    hcomp hfloorRun hin hcore.2.1 hcore.2.2 hm hmode hcore.1
  have hT : tapesOf (fun slot => p.2 (slotIndex slot)) = p.2 := by funext j; simp [tapesOf]
  simp only [← workRule_eq, hT, Prod.eta] at hencoded
  have hq : QuietPhase x.ctl.mode := Or.inr (Or.inr (Or.inl hmode))
  refine coreInv_of_ideal rest w x _ p he hencoded (fun slot hhead hidle hlive => ?_) ?_
    (chain_tickFun w x hq) (by rw [hmode]; decide) (mode_tickFun_ne_shift w x hq)
  · simp only [ruleActs, hm]
    rw [withErase_at_other p.1.fppLive _ _ slot hidle]
    have hnot8 : slotIndex slot ≠ slotIndex (progSlotOf p.1.fppLive 8) := fun h =>
      hlive 8 (slotIndex.injective h)
    have hf : fppActs PalPeg.GalilFppMarkedCode.code 1 p.1.fppLive (pcOf p.1) p.1.fppDone
        (fun j => readWin blankM microRadius (p.2 j)) (slotIndex slot) = [] := by
      unfold fppActs
      simp only [Equiv.symm_apply_apply]
      split
      · rename_i i
        cases hl : p.1.fppLive
        · exact absurd (show (Sum.inr (Sum.inl i) : Slot) = progSlot p.1.fppLive i by
            rw [hl]; rfl) (hlive i)
        · simp
      · rename_i i
        cases hl : p.1.fppLive
        · simp
        · exact absurd (show (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
              (Sum.inr (Sum.inl i)))))))) : Slot) = progSlot p.1.fppLive i by
            rw [hl]; rfl) (hlive i)
      · rfl
    unfold fppBranchActs
    split_ifs <;> simp only [hf, if_neg hnot8, List.append_nil]
  · have hbits := (tickPhysRule_bits 1 0 fppBound_gt_start (by decide : 1+3 ≤ microRadius)
      (by decide : 2 ≤ microRadius) rest p.1 (fun slot => p.2 (slotIndex slot)) none
      hcore.2.1).1
    simp only [← workRule_eq, hT, Prod.eta] at hbits
    rw [hbits]
    simp only [ruleNext, hm, fppNext]
    split_ifs <;> rfl

/-- **The quiet phase ticks on the fused physical step.** -/
theorem running_quiet (he : PalPeg.PhysicalCacheInvariant.Running w x p)
    (hstep : ∀ T, PalPeg.PhysicalCacheInvariant.CoreInv w x (p.1, T) →
      PalPeg.PhysicalCacheInvariant.CoreInv w
        (tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
          (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x)
        (idealRun (workRule rest) blankM (p.1, T) none 12)) :
    PalPeg.PhysicalCacheInvariant.Running w
      (tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
        (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x)
      ((workStep rest).apply blankM p none) :=
  PalPeg.PhysicalCacheInvariant.running_fused (workRule rest) w x _ p none he hstep

end Modes

/-- info: 'PalPeg.PhysicalPhaseStill.ideal_fpp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ideal_fpp

end PalPeg.PhysicalPhaseStill
