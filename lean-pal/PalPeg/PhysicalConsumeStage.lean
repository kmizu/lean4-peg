import PalPeg.PhysicalCountConsume
import PalPeg.ChainBoundaryCache

/-!
# The consuming step before boundary roles are renamed

The existing physical rule already moves lag, distance, period and verifier.
At a boundary its two snapshot tapes still carry their old values. This module
identifies exactly that intermediate result, in both period directions. It is
an observation of the same physical step, not an additional machine tick.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalConsumeStage
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract PalPeg.PhysicalBoundary
open PalPeg.PhysicalScanCount PalPeg.PhysicalCountConsume
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.Program (STape)
open PalPeg.Local (readWin)
open PalPeg.CloseoutCoreEnc12 PalPeg.LocalStepFusion
open PalPeg.GalilScaffoldChainWatch (caught)
open PalPeg.GalilScaffoldChainPeriod (Token)
open PalPeg.GalilScaffoldChainVerifier (canRight)
open PalPeg.PhysicalCountReady (moveRight_ready)

/-- Keep the old boundary snapshots until the finite role permutation. -/
def stagedWatch (wm : PalPeg.GalilScaffoldChainWatch.State) : PalPeg.GalilScaffoldChainWatch.State :=
  let next := caught wm
  {next with machine := {next.machine with control := {next.machine.control with boundary := wm.machine.control.boundary, last := wm.machine.control.last}}}

def stagedState (x : State GalilVM) (wm : PalPeg.GalilScaffoldChainWatch.State) : State GalilVM :=
  ⟨x.ctl, {x.vm with chain := .watch (stagedWatch wm)}⟩

theorem encControl_staged {w : List (Fin 2)} {x : State GalilVM} {q : CoreControl}
    {wm : PalPeg.GalilScaffoldChainWatch.State}
    (he : EncControl w (caughtState x wm) q) : EncControl w (stagedState x wm) q := by
  exact ⟨he.ctl, he.chainTag, he.chainPhase, he.chainForward, he.chainBroken,
    he.fppMode, he.fppFinalStage, he.fppPc, he.fppDone, he.dpPc, he.dpDone,
    he.searchMode, he.searchFinalStage, he.searchQuarter, he.periodOnly,
    he.placeGap, he.onLetter, he.leftFirst⟩

theorem padded_token_left (n : ℕ) (tokens : STape Token) (written : Token)
    (hleft : tokens.left ≠ []) :
    padLeft n (mapTape encToken (STape.applyAction Token.blank tokens (written, .left))) =
      (padLeft n (mapTape encToken tokens)).applyAction blankM (encToken written, .left) := by
  rw [mapTape_applyAction encToken encToken_blank tokens written .left,
    padLeft_applyAction_left n (mapTape encToken tokens) (encToken written)
      (by cases hl : tokens.left with
          | nil => exact (hleft hl).elim
          | cons a rest => simp [mapTape, hl])]

theorem encPeriod_moveLeft (t : PalPeg.GalilScaffoldChainPeriod.Tape) (hleft : t.left ≠ []) :
    encPeriod (PalPeg.GalilScaffoldChainPeriod.moveLeft t) =
      STape.applyAction Token.blank (encPeriod t) (t.focus, .left) := by
  cases hl : t.left with
  | nil => exact (hleft hl).elim
  | cons a rs => simp only [PalPeg.GalilScaffoldChainPeriod.moveLeft, hl, encPeriod, STape.applyAction]

/-- Both directions of the physical period action, including FIRST/LAST. -/
theorem periodTape (x : State GalilVM) (q : CoreControl) (T : Slot → STape Γm)
    (hconsume : chainConsumesTest q (fun j => readWin blankM microRadius (tapesOf T j)) = true)
    (hmatch : watchVerdictTest q (fun j => readWin blankM microRadius (tapesOf T j)) = some true)
    (tape : PalPeg.GalilScaffoldChainPeriod.Tape) (hperiod : periodOf x = some tape)
    (hleft : (scanConsumeNext q (fun j => readWin blankM microRadius (tapesOf T j))).chainForward = false → tape.left ≠ [])
    (he : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T) :
    actList blankM (T periodSlot)
      (withErase q.fppLive (fun j => readWin blankM microRadius (tapesOf T j))
        (scanConsumeActs q (fun j => readWin blankM microRadius (tapesOf T j))) (slotIndex periodSlot)) =
      padLeft margin (mapTape encToken (encPeriod
        (if (scanConsumeNext q (fun j => readWin blankM microRadius (tapesOf T j))).chainForward then
          PalPeg.GalilScaffoldChainPeriod.moveRight tape else PalPeg.GalilScaffoldChainPeriod.moveLeft tape))) := by
  cases hf : (scanConsumeNext q (fun j => readWin blankM microRadius (tapesOf T j))).chainForward with
  | true =>
    simp only [if_true]
    exact scanConsume_periodTape margin micro_le_margin x q T hconsume hmatch hf tape hperiod he
  | false =>
    simp only [Bool.false_eq_true, if_false]
    have hs := he.period tape hperiod
    have hr := centreRead_periodSlot he micro_le_margin tape hperiod
    rw [withErase_at_other q.fppLive _ _ periodSlot
      (by intro k; cases q.fppLive <;> simp [progSlotOf, periodSlot]),
      scanConsumeActs_period q _ hconsume hmatch, hf, if_neg Bool.false_ne_true, hr,
      encPeriod_moveLeft tape (hleft hf), padded_token_left margin (encPeriod tape) tape.focus (hleft hf), ← hs]
    rfl

theorem stagedTapes
    (x : State GalilVM) (q : CoreControl) (T : Slot → STape Γm)
    (hconsume : chainConsumesTest q
      (fun tape => PalPeg.Local.readWin blankM microRadius (tapesOf T tape)) = true)
    (hmatch : watchVerdictTest q
      (fun tape => PalPeg.Local.readWin blankM microRadius (tapesOf T tape)) = some true)

    (wm : PalPeg.GalilScaffoldChainWatch.State)
    (hchain : x.vm.chain = PalPeg.GalilScaffoldChainInputSupply.ChainVM.watch wm) (a : Fin 3)
    (htok : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
    (hseen : PalPeg.GalilScaffoldInputHead.read
      (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) = some a)
    (hfwdBit : (scanConsumeNext q
      (fun tape => PalPeg.Local.readWin blankM microRadius (tapesOf T tape))).chainForward = (caught wm).machine.control.forward)
    (hleft : (caught wm).machine.control.forward = false → wm.machine.control.period.left ≠ [])
    (henc : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T) :
    EncTapes margin
      (stepState ⟨x.ctl, {x.vm with
        chain := PalPeg.GalilScaffoldChainInputSupply.ChainVM.watch
          (stagedWatch wm)}⟩ wm.machine.verifier)
      (scanConsumeNext q (fun tape => PalPeg.Local.readWin blankM microRadius (tapesOf T tape))).polarity
      q.gap q.micro q.fppLive q.dpLive
      (fun slot => PalPeg.CloseoutCoreEnc12.actList blankM (T slot)
        (withErase q.fppLive (fun tape => PalPeg.Local.readWin blankM microRadius (tapesOf T tape)) (scanConsumeActs q (fun tape => PalPeg.Local.readWin blankM microRadius (tapesOf T tape)))
          (slotIndex slot))) := by
  have hcontrol : (stagedWatch wm).machine.control = {wm.machine.control with distance := PalPeg.GalilScaffoldCounter.inc wm.machine.control.distance, period := if (caught wm).machine.control.forward then PalPeg.GalilScaffoldChainPeriod.moveRight wm.machine.control.period else PalPeg.GalilScaffoldChainPeriod.moveLeft wm.machine.control.period, phase := (caught wm).machine.control.phase, forward := (caught wm).machine.control.forward} := by
    simp [stagedWatch, caught, PalPeg.GalilScaffoldChainVerifier.consume,
      PalPeg.GalilScaffoldChainConsume.consume, hseen, htok]
  have hlagx : counterOf x 11 = some wm.lag := by simp only [counterOf, hchain]
  have hdistx : counterOf x 13 = some wm.machine.control.distance := by
    simp only [counterOf, hchain]
  have hperiodx : periodOf x = some wm.machine.control.period := by
    simp only [periodOf, hchain]
  obtain ⟨segLag, habsLag, htapeLag⟩ :=
    scanConsume_lagTape margin (by decide) (by decide) x q T hconsume hmatch
      wm.lag hlagx henc
  obtain ⟨segDist, habsDist, htapeDist⟩ :=
    scanConsume_distanceTape margin (by decide) (by decide) x q T hconsume hmatch
      wm.machine.control.distance hdistx henc
  have htapePeriod :=
    periodTape x q T hconsume hmatch wm.machine.control.period hperiodx
      (fun hb => hleft (hfwdBit.symm.trans hb)) henc
  have hzc : (stepState ⟨x.ctl, {x.vm with
      chain := PalPeg.GalilScaffoldChainInputSupply.ChainVM.watch
        (stagedWatch wm)}⟩ wm.machine.verifier).vm.chain
      = PalPeg.GalilScaffoldChainInputSupply.ChainVM.watch
          ⟨⟨wm.machine.verifier, (stagedWatch wm).machine.control⟩,
            (stagedWatch wm).lag,
            (stagedWatch wm).margin⟩ := rfl
  refine encTapes_chainConsume margin x _ q.polarity _ q.gap q.micro q.fppLive q.dpLive T _ henc
    ?_ ?_ (fun i => rfl) (fun i => rfl) ?_ ?_ ?_
    (PalPeg.GalilScaffoldCounter.dec wm.lag) ?_ segLag ?_ ?_
    (PalPeg.GalilScaffoldCounter.inc wm.machine.control.distance) ?_ segDist ?_ ?_
    (if (caught wm).machine.control.forward then PalPeg.GalilScaffoldChainPeriod.moveRight wm.machine.control.period else PalPeg.GalilScaffoldChainPeriod.moveLeft wm.machine.control.period) ?_ ?_ ?_ ?_
  · funext v
    fin_cases v <;> simp only [headOf, hzc, hchain] <;> rfl
  · funext i
    fin_cases i <;> simp only [placeOf, hzc, hchain] <;> rfl
  · simp only [answerOf, hzc, hchain]
  · intro c h11 h13
    fin_cases c <;> first
      | exact absurd rfl h11
      | exact absurd rfl h13
      | (simp only [counterOf, hzc, hchain, hcontrol]; rfl)
      | (simp only [counterOf, hzc, hchain, hcontrol])
  · intro c h11 h13
    simp only [scanConsumeNext, hmatch]
    rw [Function.update_of_ne h13, Function.update_of_ne h11]
  · simp only [counterOf, hzc]
    rfl
  · rw [show (scanConsumeNext q
      (fun tape => PalPeg.Local.readWin blankM microRadius (tapesOf T tape))).polarity 11
        = decSignAt (q.polarity 11) (counterSlot 11)
          (fun tape => PalPeg.Local.readWin blankM microRadius (tapesOf T tape)) from by
      simp only [scanConsumeNext, hmatch]
      rw [Function.update_of_ne (by decide), Function.update_self]]
    exact habsLag
  · exact htapeLag
  · simp only [counterOf, hzc, hcontrol]
  · rw [show (scanConsumeNext q
      (fun tape => PalPeg.Local.readWin blankM microRadius (tapesOf T tape))).polarity 13
        = incSign q.polarity 13
          (fun tape => PalPeg.Local.readWin blankM microRadius (tapesOf T tape)) from by
      simp only [scanConsumeNext, hmatch]
      rw [Function.update_self]]
    exact habsDist
  · exact htapeDist
  · simp only [periodOf, hzc, hcontrol]
  · simpa only [hfwdBit] using htapePeriod
  · exact idle_shape_withErase margin (by decide) (by decide) T q.fppLive _
      (fun k => scanConsumeActs_off q _ (progSlotOf (!q.fppLive) k)
        (by cases q.fppLive <;> simp [progSlotOf, counterSlot])
        (by cases q.fppLive <;> simp [progSlotOf, counterSlot])
        (by cases q.fppLive <;> simp [progSlotOf, periodSlot])) henc.idleShape
  · intro slot h11 h13 hp hidle
    rw [show withErase q.fppLive (fun tape => PalPeg.Local.readWin blankM microRadius (tapesOf T tape)) (scanConsumeActs q (fun tape => PalPeg.Local.readWin blankM microRadius (tapesOf T tape))) (slotIndex slot) = [] from by
      rw [withErase_at_other q.fppLive _ _ slot hidle, scanConsumeActs_off q _ slot h11 h13 hp]]
    rfl


theorem core_staged (rest : RestCommands) (w : List (Fin 2))
    (x : State GalilVM) (p : CoreState) (henc : CoreEnc w x p)
    (hmode : p.1.ctl.mode = .scan)
    (hphase : scanPhase p.1 (fun tape => readWin blankM microRadius (p.2 tape)) ≠ .compare)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm) (a : Fin 3)
    (htok : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
    (hseen : PalPeg.GalilScaffoldInputHead.read
      (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) = some a)
    (hleft : (caught wm).machine.control.forward = false → wm.machine.control.period.left ≠ [])
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = true)
    (hcan : canRight wm.machine.verifier) :
    CoreEnc w (stagedState x wm) (idealRun (workRule rest) blankM p none 12) := by
  generalize hrun : idealRun (workRule rest) blankM p none 12 = result
  let T := fun slot => p.2 (slotIndex slot)
  have hT : tapesOf T = p.2 := by funext tape; simp [T, tapesOf]
  let ws := fun tape => readWin blankM microRadius (tapesOf T tape)
  have hbackground : scanPhase p.1 ws ≠ .compare := by
    dsimp only [ws]
    rw [hT]
    exact hphase
  have hx3 : headOf x 3 = some wm.machine.verifier := by simp only [headOf, hchain]
  have hperiod : periodOf x = some wm.machine.control.period := by simp only [periodOf, hchain]
  have htoken : decToken (centreRead ws periodSlot) = wm.machine.control.period.focus := by
    rw [centreRead_periodSlot henc.1.2 micro_le_margin _ hperiod, decToken_encToken]
    rfl
  have htag : p.1.chainTag = .watchers := by rw [henc.1.1.chainTag, hchain]; rfl
  have hpos := (counterPositive_iff_belowRead henc.1.2 (by decide : 1 ≤ microRadius)
    micro_le_margin 11 wm.lag (by simp only [counterOf, hchain])).mp hlag
  have hconsume : chainConsumesTest p.1 ws = true := by
    simpa [chainConsumesTest, htag, htoken, htok] using hpos
  have hverdict : watchVerdict wm = some true := by
    simp [watchVerdict, htok, hseen]
  have htest : watchVerdictTest p.1 ws = watchVerdict wm :=
    watchVerdictTest_eq p.1 ws wm (by rw [htoken])
      (landingLetter_of_encoded henc.1.2 micro_le_margin 3 wm.machine.verifier hx3 hcan)
  have hstep : chainStepFun x.vm.chain = .watch (PalPeg.GalilScaffoldChainWatch.caught wm) := by
    rw [hchain]
    simp only [chainStepFun]
    rw [if_pos hlag, hverdict]
  have hrule : ruleNext 1 0 fppBound_gt_start p.1 ws = scanConsumeNext p.1 ws := by
    unfold ruleNext
    rw [hmode]
    dsimp only
    rw [scanNext_background p.1 ws hbackground, if_pos hconsume]
  have hheadOther : ∀ v : Fin 4, v ≠ 3 → headOf (stagedState x wm) v = headOf x v := by
    intro v hv
    fin_cases v <;> first | rfl | exact (hv rfl).elim
  have hy3 : headOf (stagedState x wm) 3 =
      some (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) := rfl
  have hready : ∀ v view, HeadSlotsRepAt margin p.1.gap p.1.micro T v view →
      HeadReady (scanCommands p.1 ws v) view := by
    intro v view hv
    by_cases hview : v = 3
    · subst v
      have hcmd : scanCommands p.1 ws 3 = .moveRight := by
        simp [scanCommands, hbackground, hconsume]
      rw [hcmd]
      exact moveRight_ready henc.1.2 micro_le_margin 3 wm.machine.verifier hx3 hcan view hv
    · simp only [scanCommands, if_neg hbackground, if_neg hview]
      trivial
  have hencoded : PalPeg.PhysicalEncoding.Enc w margin (stagedState x wm)
      ((idealRun (tickPhysRule 1 0 fppBound_gt_start (by decide : 1 + 3 ≤ microRadius)
        (by decide : 2 ≤ microRadius) rest) blankM (p.1, tapesOf T) none 12).1,
        fun slot => (idealRun (tickPhysRule 1 0 fppBound_gt_start (by decide : 1 + 3 ≤ microRadius)
          (by decide : 2 ≤ microRadius) rest) blankM (p.1, tapesOf T) none 12).2 (slotIndex slot)) := by
    refine enc_afterTickOfState margin 1 0 fppBound_gt_start (by decide) (by decide)
      micro_le_margin rest w x (stagedState x wm) p.1 T none henc.2.1 henc.2.2
      (scanCommands p.1 ws) (fun v => by rw [modeCommands_scan 0 rest p.1 none _ hmode])
      (fun v => if v = 3 ∧ chainConsumesTest p.1 ws then
        PalPeg.GalilScaffoldChainVerifier.right else id)
      (fun v => headOp_scanCommands p.1 ws v hbackground) ?_ ?_ hready henc.1.2 ?_
      (z := stepState (stagedState x wm) wm.machine.verifier)
      (fun _ => rfl) (fun _ => rfl) (counterOf_stepState _ _) (placeOf_stepState _ _)
      (periodOf_stepState _ _) (answerOf_stepState _ _) ?_
    · intro v
      by_cases hv : v = 3
      · subst v
        rw [hx3, hy3]
        rfl
      · rw [hheadOther v hv]
    · intro v head hhead
      by_cases hv : v = 3
      · subst v
        rw [hx3] at hhead
        rw [hy3, ← Option.some.inj hhead, if_pos ⟨rfl, hconsume⟩]
      · rw [hheadOther v hv, hhead, if_neg (fun h => hv h.1)]
        rfl
    · rw [hrule]
      have hc := encControl_scanConsume x p.1 T wm henc.1.1 hconsume htest hverdict htoken
        hchain hlag
      apply encControl_staged
      simpa only [hstep, caughtState] using hc
    · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hgap, hmicro, hfl, hdl⟩ :=
        scanConsumeNext_untouched p.1 ws
      rw [hrule, hgap, hmicro, hfl, hdl]
      have hc := encControl_scanConsume x p.1 T wm henc.1.1 hconsume htest hverdict htoken hchain hlag
      have hfwdBit : (scanConsumeNext p.1 ws).chainForward = (caught wm).machine.control.forward := by
        have hf := hc.chainForward
        simpa only [hstep, chainConsumeOf] using hf
      have ha : ruleActs 1 0 p.1 ws = withErase p.1.fppLive ws (scanConsumeActs p.1 ws) := by
        simp only [ruleActs, hmode]
        rw [scanActs_background p.1 ws hbackground]
      change EncTapes margin (stepState (stagedState x wm) wm.machine.verifier)
        (scanConsumeNext p.1 ws).polarity p.1.gap p.1.micro p.1.fppLive p.1.dpLive
        (fun slot => actList blankM (T slot) (ruleActs 1 0 p.1 ws (slotIndex slot)))
      rw [ha]
      exact
        stagedTapes x p.1 T hconsume (by rw [htest, hverdict]) wm hchain a htok hseen hfwdBit hleft henc.1.2
  constructor
  · simpa only [← workRule_eq, hT, Prod.eta, hrun] using hencoded
  · have hb := macroBoundary_tickRule
      (fun q _ ws => ruleNext 1 0 fppBound_gt_start q ws) (modeCommands 0 rest)
      (fun q _ ws => ruleActs 1 0 q ws)
      (fun q _ ws j => ruleActs_length 1 0 (by decide : 1 + 3 ≤ microRadius) q ws j)
      w x p none henc
    simpa only [← tickPhysRule_eq 1 0 fppBound_gt_start (by decide) (by decide) rest,
      ← workRule_eq, hrun] using hb



/-- The cache cursor supplies left-move readiness at LAST and on the return leg. -/
theorem cursor_left {h age : ℕ} {wm : PalPeg.GalilScaffoldChainWatch.State}
    (hc : PalPeg.ChainBoundaryCache.Cursor h age wm.machine.control.period wm.machine.control.forward)
    (a : Fin 3) (htok : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
    (hseen : PalPeg.GalilScaffoldInputHead.read
      (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) = some a)
    (hback : (caught wm).machine.control.forward = false) : wm.machine.control.period.left ≠ [] := by
  obtain ⟨passed, future, first, last, hp, hlen, hc⟩ := hc
  cases hf : wm.machine.control.forward <;> simp only [hf, Bool.false_eq_true, if_false, if_true] at hc
  · cases future with
    | nil =>
      have hfocus := (List.cons.inj (by simpa using hc.2)).1
      simp only [caught, PalPeg.GalilScaffoldChainVerifier.consume,
        PalPeg.GalilScaffoldChainConsume.consume, hseen, htok, decide_true, if_true] at hback
      simp [hfocus, PalPeg.GalilScaffoldChainPeriod.isFirst] at hback
    | cons b rest =>
      have hleft := (List.cons.inj (by simpa using hc.2)).2
      rw [hleft]
      simp
  · rw [hc.1]
    simp

theorem running_staged (rest : RestCommands) (w : List (Fin 2))
    (x : State GalilVM) (p : CoreState)
    (henc : PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) x p)
    (hmode : x.ctl.mode = .scan) (hstarved : PalPeg.FrameFunction.starvedTest x = false)
    (hclock : 1 < x.ctl.clock)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm) (a : Fin 3)
    (htok : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
    (hseen : PalPeg.GalilScaffoldInputHead.read
      (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) = some a)
    (hleft : (caught wm).machine.control.forward = false → wm.machine.control.period.left ≠ [])
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = true)
    (hcan : canRight wm.machine.verifier) :
    PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) (stagedState x wm)
      ((workStep rest).apply blankM p none) := by
  have hrestart : restartGuardTest x.vm = false := by simp [restartGuardTest, hchain]
  apply running_fused_step (workRule rest) w x (stagedState x wm) p none henc
  intro T hT
  have hqmode := congrArg PalPeg.GalilScaffoldController.Control.mode hT.1.1.ctl
  change p.1.ctl.mode = x.ctl.mode at hqmode
  have hcount := countRead_eq hT.1 (by decide : 1 ≤ microRadius) micro_le_margin
    hmode hstarved hrestart hclock
  have hphase : scanPhase p.1
      (fun tape => readWin blankM microRadius (tapesOf (fun slot => T (slotIndex slot)) tape))
        = .count := of_decide_eq_true (Bool.and_eq_true_iff.mp hcount).2
  have hphaseT : scanPhase p.1 (fun tape => readWin blankM microRadius (T tape)) = .count := by
    simpa only [tapesOf, Equiv.apply_symm_apply] using hphase
  exact core_staged rest w x (p.1, T) hT (hqmode.trans hmode)
    (by rw [hphaseT]; decide) wm hchain a htok hseen hleft hlag hcan

/-- info: 'PalPeg.PhysicalConsumeStage.running_staged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running_staged

end PalPeg.PhysicalConsumeStage
