import PalPeg.RestartStageLedger
import PalPeg.WindowPack
import PalPeg.CloseoutCheckW

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

end PalPeg.RestartStageRun
