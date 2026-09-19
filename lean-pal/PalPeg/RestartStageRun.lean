import PalPeg.RestartStageLedger
import PalPeg.WindowPack
import PalPeg.CloseoutCheckW
import PalPeg.GalilTickFair

/-!
# The chain ledger along the ticks of the machine

`RestartStageLedger.ChainLedger` transported over one `Tick` of the concrete frame.  The shift
debt is the `remaining` counter in shift mode and `0` elsewhere.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.RestartStageRun

open PalPeg GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open GalilScaffoldChainInputSupply GalilBranchInvariants
open GalilScaffoldTop GalilScaffoldController GalilRunSkeleton GalilInvPlus3
open PalPeg.WindowPack PalPeg.GalilChainCoupling PalPeg.RestartStageLedger

/-- Unit shifts of the current shift round still to run. -/
def shiftDebt (c : Control) (s : GalilVM) : ℤ :=
  if c.mode = Mode.shift then value s.remaining else 0

/-- The chain ledger at a machine state, in the two modes where a chain can be live. -/
def LedgerAt (c : Control) (s : GalilVM) : Prop :=
  c.mode = Mode.scan ∨ c.mode = Mode.shift → ChainLedger (shiftDebt c s) s.chain

variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

theorem ledgerAt_of_idle {c : Control} {s : GalilVM} (hidle : s.chain = .idle) : LedgerAt c s := by
  intro _
  rw [hidle]
  trivial

/-- The shift entry: one immediate consume, then a debt of one semiperiod. -/
theorem chainLedger_beginShift {w : GalilScaffoldChainWatch.State}
    (hblock : OnBlock w.machine.control.period) (hledger : ChainLedger 0 (.watch w)) :
    ChainLedger ((periodLength w : ℕ) : ℤ) (.watch (GalilScaffoldChainWatch.immediate w)) := by
  intro hunbroken
  obtain ⟨hunbroken0, hdistance, -⟩ := consume_fresh w.machine.control _ hblock hunbroken
  have hw := hledger hunbroken0
  have hbalance : GalilScaffoldChainWatch.balance (GalilScaffoldChainWatch.immediate w)
      = GalilScaffoldChainWatch.balance w := by
    show value (GalilScaffoldChainVerifier.consume w.machine).control.distance + value w.lag
      - value (inc w.margin) = value w.machine.control.distance + value w.lag - value w.margin
    have hd : value (GalilScaffoldChainVerifier.consume w.machine).control.distance
        = value w.machine.control.distance + 1 := hdistance
    rw [hd, inc_value]
    ring
  have hconsumed := hw.consumed hblock w.lag (inc w.margin) hbalance hw.lag hunbroken
  have hlength := periodLength_consume w.machine w.lag w.margin w.lag (inc w.margin) hblock
  refine ⟨?_, hconsumed.balance, hconsumed.lag⟩
  have hlength' : periodLength (GalilScaffoldChainWatch.immediate w) = periodLength w := hlength
  have hmarks : MarkLedger (periodLength (GalilScaffoldChainWatch.immediate w))
      ((periodLength (GalilScaffoldChainWatch.immediate w) : ℕ) : ℤ)
      (GalilScaffoldChainWatch.immediate w).machine.control := hconsumed.marks.beginShift
  rw [hlength'] at hmarks ⊢
  exact hmarks

theorem ledgerAt_tick {raw : List (Fin 2)} {x y : State GalilVM}
    (ht : Tick (galilFrameS (PofC centre place entry raw) q first) 2048 x y)
    (hledger : LedgerAt x.ctl x.vm)
    (hwinX : WindowRunPack raw x.ctl x.vm) : LedgerAt y.ctl y.vm := by
  have hscan : ∀ {c : Control} {s : GalilVM}, x = ⟨c, s⟩ → c.mode = Mode.scan →
      ChainLedger 0 s.chain ∧ BlockInv s.chain ∧ Canonical s.radius ∧ 0 ≤ value s.radius := by
    intro c s hx hm
    subst hx
    obtain ⟨R, hR, -⟩ := hwinX.radiusScan hm
    have h0 := hledger (Or.inl hm)
    simp only [shiftDebt, hm, show (Mode.scan = Mode.shift) = False from by simp, if_false] at h0
    exact ⟨h0, hwinX.coupled.block, hR.1, by rw [hR.2]; positivity⟩
  cases ht with
  | init c s t hm hi =>
    obtain ⟨_,_,_,_,_,_,_,_,_,hch,_⟩ := hi
    exact ledgerAt_of_idle hch
  | scan_wait c s t hm hav hb =>
    obtain ⟨h0, hblock, hradius⟩ := hscan rfl hm
    obtain ⟨-, -, hch, -⟩ := backgroundS_fields (PofC centre place entry raw) q first hb
    intro _
    simp only [shiftDebt, hm, show (Mode.scan = Mode.shift) = False from by simp, if_false]
    exact chainLedger_chainAt hch hradius hblock h0
  | scan_count c s t hm hav hc hb =>
    obtain ⟨h0, hblock, hradius⟩ := hscan rfl hm
    obtain ⟨-, -, hch, -⟩ := backgroundS_fields (PofC centre place entry raw) q first hb
    intro _
    simp only [shiftDebt, hm, show (Mode.scan = Mode.shift) = False from by simp, if_false]
    exact chainLedger_chainAt hch hradius hblock h0
  | scan_match c s s' t o hm hav hc hcmp hmt hpl ho =>
    obtain ⟨h0, hblock, hradius⟩ := hscan rfl hm
    have hcmp' : compareFound (PofC centre place entry raw) q first s s' := hcmp
    obtain ⟨vs, vq, a, -, -, -, -, hch, heq⟩ := hcmp'
    have hchain' : s'.chain = vs.chain := by
      rw [heq, afterBirth_chain]; cases a <;> rfl
    have hchain : t.chain = s'.chain := by rw [hpl]; split <;> rfl
    intro _
    simp only [shiftDebt, hm, show (Mode.scan = Mode.shift) = False from by simp, if_false]
    rw [hchain, hchain']
    exact chainLedger_chainAt hch hradius hblock h0
  | scan_shift c s s' t hm hav hc hcmp hmt hr hg hb =>
    obtain ⟨h0, hblock, hradius⟩ := hscan rfl hm
    have hcmp' : compareFound (PofC centre place entry raw) q first s s' := hcmp
    obtain ⟨vs, vq, a, -, -, -, -, hch, heq⟩ := hcmp'
    have hchain' : s'.chain = vs.chain := by
      rw [heq, afterBirth_chain]; cases a <;> rfl
    have hs' : ChainLedger 0 s'.chain := by
      rw [hchain']; exact chainLedger_chainAt hch hradius hblock h0
    have hblock' : BlockInv s'.chain := by
      rw [hchain']
      rcases hch with ⟨-, y0, hstep, hzy⟩ | ⟨-, -, hz⟩ | ⟨-, -, hz⟩
      · cases a with
        | true =>
          rw [if_pos rfl] at hzy
          exact blockInv_matched hzy (blockInv_step hstep hblock)
        | false =>
          rw [if_neg (by simp)] at hzy
          subst hzy
          exact blockInv_step hstep hblock
      · rw [hz]; trivial
      · cases a with
        | true =>
          rw [if_pos rfl] at hz
          exact blockInv_matched hz (blockInv_chainStart _ _ _ _ _)
        | false =>
          rw [if_neg (by simp)] at hz
          rw [hz]
          exact blockInv_chainStart _ _ _ _ _
    obtain ⟨w, hw, hteq⟩ := hb
    rw [hw] at hs' hblock'
    intro _
    have hdebt : shiftDebt {c with clock := 2048, mode := Mode.shift} t
        = ((periodLength w : ℕ) : ℤ) := by
      simp only [shiftDebt, if_true]
      rw [hteq]
      exact ofNat_value _
    rw [hdebt]
    have htc : t.chain = .watch (GalilScaffoldChainWatch.immediate w) := by rw [hteq]
    rw [htc]
    exact chainLedger_beginShift hblock' hs'
  | scan_fallback c s s' t hm hav hc hcmp hmt hg hr hb =>
    obtain ⟨p, hteq, -⟩ := hb
    exact ledgerAt_of_idle (by rw [hteq])
  | shift_one c s t hm hp hso =>
    obtain ⟨⟨-, -, -, w, hw, hget⟩, hset⟩ := hso
    change s.chain = .watch w at hw
    have hchain : t.chain = .watch (chainShiftOne w) := by rw [hset, hget]; rfl
    have hrem : t.remaining = dec s.remaining := by rw [hset, hget]; rfl
    have h0 := hledger (Or.inr hm)
    simp only [shiftDebt, hm, if_true] at h0
    rw [hw] at h0
    intro _
    simp only [shiftDebt, hm, if_true]
    rw [hchain, hrem, dec_value]
    intro hunbroken
    exact (h0 hunbroken).shiftOne
  | shift_done c s o hm hp ho =>
    have h0 := hledger (Or.inr hm)
    simp only [shiftDebt, hm, if_true] at h0
    obtain ⟨rem, R, hrem, -⟩ := hwinX.radiusShift hm
    have hz : positive s.remaining = false := Bool.eq_false_iff.mpr (fun h => hp (Or.inl h))
    have hzero : value s.remaining = 0 := by
      have hle := value_nonpos_of_not_positive hz
      rw [hrem, ofNat_value] at hle ⊢
      have : (0 : ℤ) ≤ (rem : ℤ) := by positivity
      omega
    rw [hzero] at h0
    intro _
    simpa [shiftDebt] using h0
  | replayStart c s t o hm hr ho ho' =>
    obtain ⟨_,_,_,_,_,_,_,_,_,hch,_,_,_⟩ := hr
    exact ledgerAt_of_idle hch
  | restart c s t hm hr =>
    obtain ⟨_,_,_,_,_,rfl⟩ := hr
    exact ledgerAt_of_idle rfl
  | copy_one _ _ _ hm _ _ | copy_done _ _ _ hm _ _
  | home_start _ _ _ hm _ _ | home_step _ _ _ hm _ _
  | fpp_slice _ _ _ hm _ | fpp_done _ _ _ hm _
  | markEnd_found _ _ _ hm _ _ | markEnd_step _ _ _ hm _ _
  | choose_select _ _ _ hm _ _ _ | choose_step _ _ _ hm _ _
  | rewind_done _ _ _ hm _ _ | rewind_one _ _ _ hm _ _ _
  | rewind_pair _ _ _ hm _ _ _ =>
    intro hmode
    simp [hm] at hmode

/-! ## The broken chain before its restart -/

/-- What a broken chain in scan mode carries for the restart that follows: a canonical
nonnegative lag, and at a restart-guard state the stage bound of the radius against `last`
together with whatever else (`Extra`) the lag-zero break established there. -/
def BrokenStage (Extra : ℕ → GalilScaffoldChainWatch.State → Prop) (c : Control)
    (s : GalilVM) : Prop :=
  (c.mode = Mode.shift → ∃ w, s.chain = .watch w) ∧
  (c.mode = Mode.scan → ∀ w, s.chain = .broken w →
    (Canonical w.lag ∧ 0 ≤ value w.lag) ∧
    (restartGuardVM s → (∃ Rad : ℕ, RadiusRep s.radius Rad ∧
      StageEntry Rad w.machine.control.last ∧ Canonical w.machine.control.last) ∧
        Extra (position s.center) w))

theorem brokenStage_of_not_broken {Extra : ℕ → GalilScaffoldChainWatch.State → Prop}
    {c : Control} {s : GalilVM}
    (hmode : c.mode ≠ Mode.shift) (hnot : ∀ w, s.chain ≠ .broken w) : BrokenStage Extra c s :=
  ⟨fun h => absurd h hmode, fun _ w hw => absurd hw (hnot w)⟩

theorem unbroken_of_step {x : ChainVM} {w1 : GalilScaffoldChainWatch.State}
    (hstep : ChainStep x (.watch w1))
    (hunbroken : ∀ w, x = .watch w → w.machine.control.broken = false) :
    w1.machine.control.broken = false := by
  generalize hy : ChainVM.watch w1 = y at hstep
  cases hstep with
  | backDone v h lag margin ver hf => cases hy; rfl
  | watchStep w w' hinternal =>
    cases hy
    cases hinternal with
    | idle => exact hunbroken _ rfl
    | take hp hg =>
      obtain ⟨-, a, hsymbol, hread⟩ := hg
      exact ((GalilScaffoldChainVerifier.consume_agrees w.machine a hsymbol hread).2).trans
        (hunbroken _ rfl)
  | idle => cases hy
  | brokenIdle => cases hy
  | copyBit => cases hy
  | copyEnd => cases hy
  | backStep => cases hy
  | watchBreak => cases hy

/-- A background chain step into a broken chain: either the chain was already broken, or a
watch broke at a positive lag. -/
theorem brokenLag_of_step {x : ChainVM} {w : GalilScaffoldChainWatch.State}
    (hstep : ChainStep x (.broken w)) (hledger : ChainLedger 0 x)
    (hunbroken : ∀ w0, x = .watch w0 → w0.machine.control.broken = false)
    (hsource : ∀ w0, x = .broken w0 → Canonical w0.lag ∧ 0 ≤ value w0.lag) :
    (Canonical w.lag ∧ 0 ≤ value w.lag) ∧ (x = .broken w ∨ positive w.lag = true) := by
  generalize hy : ChainVM.broken w = y at hstep
  cases hstep with
  | brokenIdle w0 => cases hy; exact ⟨hsource _ rfl, Or.inl rfl⟩
  | watchBreak w0 hb =>
    cases hy
    exact ⟨(hledger (hunbroken _ rfl)).lag, Or.inr hb.1⟩
  | idle => cases hy
  | copyBit => cases hy
  | copyEnd => cases hy
  | backStep => cases hy
  | backDone => cases hy
  | watchStep => cases hy

theorem not_zero_of_positive {x : Counter} (hpositive : positive x = true) : zero x = false := by
  rcases x with ⟨pos, neg⟩
  cases pos <;> simp_all [positive, zero]

theorem not_zero_inc {x : Counter} (hx : Canonical x ∧ 0 ≤ value x) : zero (inc x) = false := by
  cases hz : zero (inc x) with
  | false => rfl
  | true =>
    have := (zero_iff _ (inc_canonical _ hx.1)).mp hz
    rw [inc_value] at this
    have := hx.2
    omega

/-- One tick of the canonical schedule keeps `BrokenStage`.  `hinterior` excludes the one
boundary case of a lag-zero break (`distance = 4h − 1`); `hextra` establishes the extra payload
at the one place a guard state is born, the lag-zero break of a matched comparison. -/
theorem brokenStage_tick {Extra : ℕ → GalilScaffoldChainWatch.State → Prop}
    {raw : List (Fin 2)} {x y : State GalilVM}
    (ht : Tick (galilFrameS (PofC centre place entry raw) q first) 2048 x y)
    (hcanon : PalPeg.GalilTickFair.Canonical entry 2048 x y)
    (hstage : BrokenStage Extra x.ctl x.vm) (hledger : LedgerAt x.ctl x.vm)
    (hwinX : WindowRunPack raw x.ctl x.vm) (hwinY : WindowRunPack raw y.ctl y.vm)
    (hunbroken : ∀ w, x.vm.chain = .watch w → w.machine.control.broken = false)
    (hinterior : ∀ (c : Control) (s s' : GalilVM) w1 w', x = ⟨c, s⟩ → c.mode = Mode.scan →
      (galilFrameS (PofC centre place entry raw) q first).compare s s' →
      (galilFrameS (PofC centre place entry raw) q first).matched s' →
      ChainStep s.chain (.watch w1) → BreakStep w1 w' →
      value w1.machine.control.distance ≠ 4 * (periodLength w1 : ℤ) - 1)
    (hextra : ∀ (c : Control) (s s' : GalilVM) w1 w', x = ⟨c, s⟩ → c.mode = Mode.scan →
      (galilFrameS (PofC centre place entry raw) q first).compare s s' →
      (galilFrameS (PofC centre place entry raw) q first).matched s' →
      ChainStep s.chain (.watch w1) → BreakStep w1 w' → negative w'.margin = false →
      Extra (position s.center) w') :
    BrokenStage Extra y.ctl y.vm := by
  by_cases hguard : x.ctl.mode = Mode.scan ∧ restartGuardVM x.vm
  · obtain ⟨hctl, hrestart⟩ := hcanon.restartFirst hguard.1 hguard.2
    obtain ⟨w0, -, -, -, -, hteq⟩ := hrestart
    exact brokenStage_of_not_broken (by rw [hctl]; simp [hguard.1])
      (fun w hw => by rw [hteq] at hw; cases hw)
  have hscan : ∀ {c : Control} {s : GalilVM}, x = ⟨c, s⟩ → c.mode = Mode.scan →
      ChainLedger 0 s.chain ∧ BlockInv s.chain ∧ SumRel s.chain (value s.radius) ∧
        ¬ restartGuardVM s := by
    intro c s hx hm
    subst hx
    have h0 := hledger (Or.inl hm)
    simp only [shiftDebt, hm, show (Mode.scan = Mode.shift) = False from by simp, if_false] at h0
    exact ⟨h0, hwinX.coupled.block, hwinX.coupled.sum, fun hg => hguard ⟨hm, hg⟩⟩
  have hbackground : ∀ {c c' : Control} {s t : GalilVM}, x = ⟨c, s⟩ → y = ⟨c', t⟩ →
      c.mode = Mode.scan → c'.mode ≠ Mode.shift →
      (galilFrameS (PofC centre place entry raw) q first).background s t →
      BrokenStage Extra c' t := by
    intro c c' s t hx hy hm hmode' hb
    subst hx
    subst hy
    obtain ⟨h0, hblock, -, hnoGuard⟩ := hscan rfl hm
    obtain ⟨-, -, hch, -, -, hradius, -⟩ :=
      backgroundS_fields (PofC centre place entry raw) q first hb
    refine ⟨fun h => absurd h hmode', fun _ w hw => ?_⟩
    rcases hch with ⟨-, y0, hstep, hzy⟩ | ⟨-, -, hz⟩ | ⟨-, -, hz⟩
    · rw [if_neg (by simp)] at hzy
      rw [hzy] at hw
      subst hw
      obtain ⟨hlag, hcase⟩ := brokenLag_of_step hstep h0 hunbroken
        (fun w0 hw0 => (hstage.2 hm w0 hw0).1)
      refine ⟨hlag, fun hg => ?_⟩
      obtain ⟨w2, hw2, hrest⟩ := hg
      rw [hzy] at hw2
      cases hw2
      rcases hcase with hsame | hpositive
      · exact absurd ⟨w, hsame, hrest⟩ hnoGuard
      · rw [not_zero_of_positive hpositive] at hrest
        exact absurd hrest.2.2 (by simp)
    · rw [hz] at hw; cases hw
    · rw [if_neg (by simp)] at hz
      rw [hz] at hw
      cases hw
  cases ht with
  | init c s t hm hi =>
    obtain ⟨_,_,_,_,_,_,_,_,_,hch,_⟩ := hi
    exact brokenStage_of_not_broken (by simp) (fun w hw => by rw [hch] at hw; cases hw)
  | scan_wait c s t hm hav hb => exact hbackground rfl rfl hm (by simp [hm]) hb
  | scan_count c s t hm hav hc hb => exact hbackground rfl rfl hm (by simp [hm]) hb
  | scan_match c s s' t o hm hav hc hcmp hmt hpl ho =>
    obtain ⟨h0, hblock, hsum, hnoGuard⟩ := hscan rfl hm
    have hcmp' : compareFound (PofC centre place entry raw) q first s s' := hcmp
    obtain ⟨vs, vq, a, -, -, hiff, -, hch, heq⟩ := hcmp'
    have hchain' : s'.chain = vs.chain := by
      rw [heq, afterBirth_chain]; cases a <;> rfl
    have hradius' : s'.radius = inc s.radius := by
      rw [heq, afterBirth_radius]; cases a <;> rfl
    have hchain : t.chain = s'.chain := by rw [hpl]; split <;> rfl
    have hradius : t.radius = s'.radius := by rw [hpl]; split <;> rfl
    refine ⟨fun h => by simp [hm] at h, fun hmode w hw => ?_⟩
    have htchain : t.chain = .broken w := hw
    rw [hchain, hchain'] at hw
    have ha : a = true := by
      cases a with
      | true => rfl
      | false =>
        exfalso
        have hm' : read s'.left = read s'.right := hmt
        rw [heq, afterBirth_left, afterBirth_right] at hm'
        exact absurd (hiff.2 hm') (by simp)
    subst ha
    rcases hch with ⟨-, y0, hstep, hzy⟩ | ⟨-, -, hz⟩ | ⟨-, -, hz⟩
    · rw [if_pos rfl] at hzy
      rw [hw] at hzy
      generalize hyz : ChainVM.broken w = z at hzy
      cases hzy with
      | breaks w1 w' hbreak =>
        cases hyz
        have hunbroken1 := unbroken_of_step hstep hunbroken
        have hledger1 : WatchLedger 0 w1 := chainLedger_step hstep hblock h0 hunbroken1
        have hsum1 : SumRel (.watch w1) (value s.radius) :=
          (step_inv hstep (F := True) trivial (O := fun _ => True) hblock hsum
            (fun _ _ _ => Or.inr trivial)).1
        have hd := hsum1 hunbroken1
        rw [value_zero_of_zero hbreak.1, add_zero] at hd
        refine ⟨?_, fun hg => ?_⟩
        · have hlagEq : w.lag = w1.lag := by
            obtain ⟨-, -, -, -, -, hweq⟩ := hbreak
            rw [hweq]
          rw [hlagEq]
          exact hledger1.lag
        · obtain ⟨w2, hw2, hmargin, -, -⟩ := hg
          rw [htchain] at hw2
          cases hw2
          obtain ⟨Rad, hRad, -⟩ := hwinY.radiusScan hmode
          have hRadValue : (Rad : ℤ) = value w1.machine.control.distance + 1 := by
            have hR2 : value t.radius = (Rad : ℤ) := hRad.2
            rw [← hR2, hradius, hradius', inc_value, hd]
          obtain ⟨hentry, hcanonicalLast, -⟩ := hledger1.stageEntry_of_break hbreak hmargin
            (hinterior c s s' w1 w rfl hm hcmp hmt hstep hbreak) hRadValue
          have hcenter : t.center = s.center := by
            have htarget : t.center = s'.center := by rw [hpl]; split <;> rfl
            rw [htarget]
            exact (PalPeg.WindowTick.compare_target_heads heq).2.2.2.1
          refine ⟨⟨Rad, hRad, hentry, hcanonicalLast⟩, ?_⟩
          show Extra (position t.center) w
          rw [hcenter]
          exact hextra c s s' w1 w rfl hm hcmp hmt hstep hbreak hmargin
      | brokenMatched w0 =>
        cases hyz
        obtain ⟨hlag, -⟩ := brokenLag_of_step hstep h0 hunbroken
          (fun w3 hw3 => (hstage.2 hm w3 hw3).1)
        refine ⟨⟨inc_canonical _ hlag.1, by
          show 0 ≤ value (inc w0.lag)
          rw [inc_value]; have := hlag.2; omega⟩, fun hg => ?_⟩
        obtain ⟨w2, hw2, -, -, hzero⟩ := hg
        rw [htchain] at hw2
        cases hw2
        have hnz : zero (inc w0.lag) = false := not_zero_inc hlag
        rw [hnz] at hzero
        cases hzero
      | idle => cases hyz
      | copy => cases hyz
      | back => cases hyz
      | watch => cases hyz
    · rw [hz] at hw; cases hw
    · rw [if_pos rfl] at hz
      rw [hw] at hz
      unfold chainStart at hz
      cases hz
  | scan_shift c s s' t hm hav hc hcmp hmt hr hg hb =>
    obtain ⟨w, -, hteq⟩ := hb
    exact ⟨fun _ => ⟨_, by rw [hteq]⟩, fun h => by simp at h⟩
  | scan_fallback c s s' t hm hav hc hcmp hmt hg hr hb =>
    obtain ⟨p, hteq, -⟩ := hb
    exact brokenStage_of_not_broken (by simp) (fun w0 hw0 => by rw [hteq] at hw0; cases hw0)
  | shift_one c s t hm hp hso =>
    obtain ⟨⟨-, -, -, w, hw, hget⟩, hset⟩ := hso
    exact ⟨fun _ => ⟨chainShiftOne w, by rw [hset, hget]; rfl⟩, fun h => by simp [hm] at h⟩
  | shift_done c s o hm hp ho =>
    obtain ⟨w, hw⟩ := hstage.1 hm
    exact brokenStage_of_not_broken (by simp) (fun w0 hw0 => by rw [hw] at hw0; cases hw0)
  | replayStart c s t o hm hr ho ho' =>
    obtain ⟨_,_,_,_,_,_,_,_,_,hch,_,_,_⟩ := hr
    exact brokenStage_of_not_broken (by simp) (fun w hw => by rw [hch] at hw; cases hw)
  | restart c s t hm hr =>
    obtain ⟨_,_,_,_,_,rfl⟩ := hr
    exact brokenStage_of_not_broken (by simp [hm]) (fun w hw => by cases hw)
  | copy_one _ _ _ hm _ hi | copy_done _ _ _ hm _ hi
  | home_start _ _ _ hm _ hi | home_step _ _ _ hm _ hi
  | fpp_slice _ _ _ hm hi | fpp_done _ _ _ hm hi
  | markEnd_found _ _ _ hm _ hi | markEnd_step _ _ _ hm _ hi
  | choose_select _ _ _ hm _ _ hi | choose_step _ _ _ hm _ hi
  | rewind_done _ _ _ hm _ hi | rewind_one _ _ _ hm _ _ hi
  | rewind_pair _ _ _ hm _ _ hi =>
    have hidle := hwinX.coupled.idleOut (by rw [hm]; decide) (by rw [hm]; decide)
      (by rw [hm]; decide)
    have hchain := (congrArg GalilVM.chain hi.2).trans hidle
    exact brokenStage_of_not_broken (by intro hshift; simp [hm] at hshift)
      (fun w hw => by rw [hchain] at hw; cases hw)

/-- The chain ledger at every point of a packed run out of an `InvLPS` origin. -/
theorem ledgerAt_packed {raw : List (Fin 2)} {c₀ : Control} {r₀ : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    {k : ℕ} {y : State GalilVM}
    (hrun : PalPeg.CloseoutCheckW.StepsIMWC centre place entry q first raw k ⟨c₀,r₀⟩ y) :
    LedgerAt y.ctl y.vm := by
  obtain ⟨g, hg0, hgk, htr, -, hpk⟩ := hrun
  have hiChain : r₀.chain = .idle := by
    rcases hI.1.1.1.1.1 with h | ⟨_, h⟩
    · obtain ⟨_, _, h⟩ := h.rest; exact h.1
    · exact h.chainIdle
  have hall : ∀ i, i ≤ k → LedgerAt (g i).ctl (g i).vm := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [hg0]
      exact ledgerAt_of_idle hiChain
    | succ i ih =>
      intro hik
      exact ledgerAt_tick centre place entry q first (htr.tick i (by omega)) (ih (by omega))
        ((hpk i (by omega)).win hP)
  rw [← hgk]
  exact hall k le_rfl

/-- An unbroken control at every watch of a window-packed state. -/
theorem watch_unbroken_of_window {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    (hwin : WindowRunPack raw c s) :
    ∀ w, s.chain = .watch w → w.machine.control.broken = false := by
  intro w hw
  obtain ⟨cen₀, cc, -, hinv, -⟩ := hwin.window
  rw [hw] at hinv
  obtain ⟨b, xs, hW⟩ := hinv
  exact hW.2.2.2.2.2.1

/-- The boundary case of a lag-zero break, as a statement about the ticks of a packed run:
no matched comparison breaks the chain at `distance = 4h − 1`. -/
def NoBoundaryBreak (raw : List (Fin 2)) (c₀ : Control) (r₀ : GalilVM) : Prop :=
  ∀ (j : ℕ) (c : Control) (s s' : GalilVM),
    PalPeg.CloseoutCheckW.StepsIMWC centre place entry q first raw j ⟨c₀,r₀⟩ ⟨c, s⟩ →
    c.mode = Mode.scan →
    (galilFrameS (PofC centre place entry raw) q first).compare s s' →
    (galilFrameS (PofC centre place entry raw) q first).matched s' →
    ∀ w1 w', ChainStep s.chain (.watch w1) → BreakStep w1 w' →
      value w1.machine.control.distance ≠ 4 * (periodLength w1 : ℤ) - 1

theorem brokenStage_packed {raw : List (Fin 2)} {c₀ : Control} {r₀ : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    (hboundary : NoBoundaryBreak centre place entry q first raw c₀ r₀)
    {k : ℕ} {y : State GalilVM}
    (hrun : PalPeg.CloseoutCheckW.StepsIMWC centre place entry q first raw k ⟨c₀,r₀⟩ y) :
    BrokenStage (fun _ _ => True) y.ctl y.vm := by
  obtain ⟨g, hg0, hgk, htr, hcan, hpk⟩ := hrun
  have hprefix : ∀ i, i ≤ k →
      PalPeg.CloseoutCheckW.StepsIMWC centre place entry q first raw i ⟨c₀,r₀⟩ (g i) := by
    intro i hi
    exact ⟨g, hg0, rfl,
      ⟨fun j hj => htr.tick j (by omega), fun j hj => htr.good j (by omega)⟩,
      fun j hj => hcan j (by omega), fun j hj => hpk j (by omega)⟩
  have hiMode : c₀.mode = Mode.scan := (PalPeg.GalilOracleLocal.invS_mode hI.1.1.1.1.1).1
  have hiChain : r₀.chain = .idle := by
    rcases hI.1.1.1.1.1 with h | ⟨_, h⟩
    · obtain ⟨_, _, h⟩ := h.rest; exact h.1
    · exact h.chainIdle
  have hall : ∀ i, i ≤ k → BrokenStage (fun _ _ => True) (g i).ctl (g i).vm := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [hg0]
      exact brokenStage_of_not_broken (by rw [hiMode]; decide)
        (fun w hw => by rw [hiChain] at hw; cases hw)
    | succ i ih =>
      intro hik
      have hwinX := (hpk i (by omega)).win hP
      exact brokenStage_tick centre place entry q first (htr.tick i (by omega))
        (hcan i (by omega)).canonical (ih (by omega))
        (ledgerAt_packed centre place entry q first hP hI (hprefix i (by omega)))
        hwinX ((hpk (i+1) (by omega)).win hP) (watch_unbroken_of_window hwinX)
        (fun c s s' w1 w' hx hm hcmp hmt hstep hbreak =>
          hboundary i c s s' (hx ▸ hprefix i (by omega)) hm hcmp hmt w1 w' hstep hbreak)
        (fun _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
  rw [← hgk]
  exact hall k le_rfl

/-- **The restart at a guard state of a packed run lands in a stage-entry restart.**  The scan
geometry is an input because a replaying state keeps it outside the pack. -/
theorem restartStage_packed {raw : List (Fin 2)} {c₀ : Control} {r₀ : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    (hboundary : NoBoundaryBreak centre place entry q first raw c₀ r₀)
    {k : ℕ} {y : State GalilVM}
    (hrun : PalPeg.CloseoutCheckW.StepsIMWC centre place entry q first raw k ⟨c₀,r₀⟩ y)
    (hmode : y.ctl.mode = Mode.scan) (hguard : restartGuardVM y.vm)
    {rad : ℕ} (hscanGeom : ScanInvariant raw (position y.vm.center) rad y.vm.left y.vm.right)
    (hlength : Canonical y.vm.length)
    {t : GalilVM} (hrestart : restartVM entry y.vm t) :
    ∃ (Rad : ℕ) (last : Counter), Restarted raw t Rad last ∧ StageEntry Rad last := by
  have hstage := brokenStage_packed centre place entry q first hP hI hboundary hrun
  have hp := PalPeg.CloseoutCheckW.ipackMW_last_of_stepsIMWC centre place entry q first hrun
  have hwin := hp.win hP
  obtain ⟨w, hw, hmargin, hlast, hlag, hteq⟩ := hrestart
  obtain ⟨-, hguarded⟩ := hstage.2 hmode w hw
  obtain ⟨⟨Rad, hRad, hentry, hcanonicalLast⟩, -⟩ := hguarded hguard
  obtain ⟨Rad', hRad', hright⟩ := hwin.radiusScan hmode
  have hRadEq : Rad' = Rad := by
    have h1 : (Rad' : ℤ) = (Rad : ℤ) := by rw [← hRad'.2, ← hRad.2]
    exact_mod_cast h1
  have hrad : rad = Rad := by
    have h1 := hscanGeom.rightPos
    rw [hRadEq] at hright
    omega
  have hcen := hwin.centreRep (Or.inl hmode)
  refine ⟨Rad, w.machine.control.last, ?_, hentry⟩
  subst hteq
  refine ⟨rfl, hcen.1, hcen.2, by rw [← hrad]; exact hscanGeom, hRad, hlength, rfl, rfl,
    hcanonicalLast, ?_⟩
  have := (positive_iff _ hcanonicalLast).mp hlast
  omega

end PalPeg.RestartStageRun
