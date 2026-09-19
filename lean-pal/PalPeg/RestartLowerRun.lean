import PalPeg.RestartLower
import PalPeg.CloseoutStageBoot
import PalPeg.SearchStageRun
import PalPeg.ChainClock
import PalPeg.BlockText

/-!
# Minimal periods across a broken restart

After a broken restart the search runs with `lower = last ≠ 0`, so the zero-lower budget
(`CanonicalChainMinimal.BudgetMinimal`) says nothing.  What survives is the history the lower bound
stands for: `LowerExcluded`.  It is carried along a packed run together with the minimal-period
payload it feeds (a chain is born minimal because its lower bound is excluded) and the broken
chain that produces it (`RestartLower.lowerExcluded_at_break` needs the minimal period of the chain
that breaks).  The three are mutually dependent, so they are one run invariant.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.RestartLowerRun

open PalPeg GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open GalilScaffoldChainInputSupply GalilBranchInvariants
open PalPeg.CanonicalSearchProgram
open GalilScaffoldTop GalilScaffoldController GalilRunSkeleton GalilInvPlus3
open PalPeg.WindowInv PalPeg.WindowRun PalPeg.WindowPack
open PalPeg.CanonicalChainMinimal PalPeg.RestartStageRun PalPeg.RestartStageLedger
open PalPeg.RestartCertificate PalPeg.RestartLower

/-- The lower bound a restart would install from this broken chain is excluded at `C` on every
span of radius at least `Rad`, the radius the restart sees. -/
def LastExcluded (raw : List (Fin 2)) (C Rad : ℕ) (w : GalilScaffoldChainWatch.State) : Prop :=
  ∀ L : ℕ, value w.machine.control.last = (L : ℤ) →
    Rad ≤ 4 * (L + 1) ∧ LowerExcludedFrom raw C L Rad

/-- While the centre has not moved since the lower bound was installed — the chain is idle, or
it is in its first round (`periodOnly = false`: a birth resets the flag, a shift sets it) — the
lower bound is excluded at the centre on every span from some radius `base` on, which the scan
radius has reached. -/
def LowerAt (raw : List (Fin 2)) (c : Control) (s : GalilVM) : Prop :=
  c.mode = .scan → (s.chain = .idle ∨ s.periodOnly = false) →
    ∀ L : ℕ, value s.lower = (L : ℤ) → ∃ base : ℕ, base ≤ (value s.radius).toNat ∧
      base ≤ 4 * (L + 1) ∧ LowerExcludedFrom raw (position s.center) L base

theorem lowerAt_of_reset {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    (hlower : s.lower = reset) : LowerAt raw c s := by
  intro _ _ L hL
  rw [hlower] at hL
  have hL0 : L = 0 := by
    have hzero : value reset = 0 := rfl
    rw [hzero] at hL
    exact_mod_cast hL.symm
  rw [hL0]
  exact ⟨0, Nat.zero_le _, Nat.zero_le _, lowerExcludedFrom_zero _ _ _⟩

/-- A chain that is idle after a chain tick was idle before it. -/
theorem idle_of_chainAt {a found : Bool} {answer : GalilScaffoldTape.Tape} {cc : Fin 3}
    {walker : GalilScaffoldPlace.Place} {ver : PlaceHead} {radius : Counter} {x : ChainVM}
    (hchain : chainAt a found answer cc walker ver radius x .idle) : x = .idle := by
  rcases hchain with ⟨hne, y0, hstep, hzy⟩ | ⟨hx, -, -⟩ | ⟨-, -, hz⟩
  · have hy0 : y0 = .idle := by
      cases a with
      | false =>
        rw [if_neg (by simp)] at hzy
        exact hzy.symm
      | true =>
        rw [if_pos rfl] at hzy
        cases hzy
        rfl
    subst hy0
    cases hstep
    rfl
  · exact hx
  · exfalso
    cases a with
    | false =>
      rw [if_neg (by simp)] at hz
      unfold chainStart at hz
      cases hz
    | true =>
      rw [if_pos rfl] at hz
      unfold chainStart at hz
      cases hz

theorem isIdle_false_of_ne {x : ChainVM} (hne : x ≠ .idle) : x.isIdle = false := by
  cases x <;> simp_all [ChainVM.isIdle]

/-- The guard of `LowerAt` goes back over a chain tick: a chain that ends idle was idle, and a
non-idle chain is not born, so its `periodOnly` flag is the source's. -/
theorem lowerGuard_source {a found : Bool} {answer : GalilScaffoldTape.Tape} {cc : Fin 3}
    {walker : GalilScaffoldPlace.Place} {ver : PlaceHead} {radius : Counter} {x z : ChainVM}
    {sourceOnly targetOnly : Bool}
    (hchain : chainAt a found answer cc walker ver radius x z)
    (honly : targetOnly = if chainBorn found x then false else sourceOnly)
    (hguard : z = .idle ∨ targetOnly = false) : x = .idle ∨ sourceOnly = false := by
  by_cases hidle : x = .idle
  · exact Or.inl hidle
  · right
    rcases hguard with hz | hfalse
    · rw [hz] at hchain
      exact absurd (idle_of_chainAt hchain) hidle
    · unfold chainBorn at honly
      rw [isIdle_false_of_ne hidle] at honly
      rw [honly] at hfalse
      simpa using hfalse

variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- One tick keeps `LowerAt`: the centre and the lower bound stand still while the chain stays
idle, the two controller entries reset the lower bound, and a restart installs the `last` of a
broken chain at a guard state, which `BrokenStage` has excluded. -/
theorem lowerAt_tick {raw : List (Fin 2)} {x y : State GalilVM}
    (ht : Tick (galilFrameS (PofC centre place entry raw) q first) 2048 x y)
    (hlowerAt : LowerAt raw x.ctl x.vm)
    (hstage : BrokenStage (LastExcluded raw) x.ctl x.vm) :
    LowerAt raw y.ctl y.vm := by
  have hbackground : ∀ {c c' : Control} {s t : GalilVM}, x = ⟨c, s⟩ → y = ⟨c', t⟩ →
      c.mode = .scan → (galilFrameS (PofC centre place entry raw) q first).background s t →
      LowerAt raw c' t := by
    intro c c' s t hx hy hm hb
    subst hx
    subst hy
    obtain ⟨-, -, hch, hcenter, honly, hradius, -, -, -, -, -, hse⟩ :=
      backgroundS_fields (PofC centre place entry raw) q first hb
    intro _ hguard L hL
    have hsourceGuard := lowerGuard_source hch honly hguard
    have hlowerEq : t.lower = s.lower := searchEffect_lower_eq hse
    obtain ⟨base, hbaseRadius, hbaseLower, hexcluded⟩ :=
      hlowerAt hm hsourceGuard L (by rw [← hlowerEq]; exact hL)
    refine ⟨base, ?_, hbaseLower, ?_⟩
    · show base ≤ (value t.radius).toNat
      rw [hradius]
      exact hbaseRadius
    · show LowerExcludedFrom raw (position t.center) L base
      rw [hcenter]
      exact hexcluded
  cases ht with
  | init c s t hm hi =>
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hlower,_⟩ := hi
    exact lowerAt_of_reset hlower
  | scan_wait c s t hm hav hb => exact hbackground rfl rfl hm hb
  | scan_count c s t hm hav hc hb => exact hbackground rfl rfl hm hb
  | scan_match c s s' t o hm hav hc hcmp hmt hpl ho =>
    have hcmp' : compareFound (PofC centre place entry raw) q first s s' := hcmp
    obtain ⟨vs, vq, a, -, -, -, hse, hch, heq⟩ := hcmp'
    obtain ⟨-, -, hchain', hcenter', -⟩ := PalPeg.WindowTick.compare_target_heads heq
    have hchain : t.chain = s'.chain := by rw [hpl]; split <;> rfl
    have hcenter : t.center = s'.center := by rw [hpl]; split <;> rfl
    have honly : t.periodOnly
        = if chainBorn (decide (vq.search.mode = .found)) s.chain then false
          else s.periodOnly := by
      have htarget : t.periodOnly = s'.periodOnly := by rw [hpl]; split <;> rfl
      rw [htarget, heq, afterBirth_periodOnly]
      cases a <;> rfl
    have hlowerEq : t.lower = s.lower := by
      have htarget : t.lower = s'.lower := by rw [hpl]; split <;> rfl
      rw [htarget, heq, afterBirth_lower]
      cases a <;> exact searchEffect_lower_eq hse
    have hradius : t.radius = inc s.radius := by
      have htarget : t.radius = s'.radius := by rw [hpl]; split <;> rfl
      rw [htarget, heq, afterBirth_radius]
      cases a <;> rfl
    intro _ hguard L hL
    have hsourceGuard := lowerGuard_source (z := t.chain) (by rw [hchain, hchain']; exact hch)
      honly hguard
    obtain ⟨base, hbaseRadius, hbaseLower, hexcluded⟩ :=
      hlowerAt hm hsourceGuard L (by rw [← hlowerEq]; exact hL)
    refine ⟨base, ?_, hbaseLower, ?_⟩
    · show base ≤ (value t.radius).toNat
      rw [hradius, inc_value]
      have hsource : base ≤ (value s.radius).toNat := hbaseRadius
      omega
    · show LowerExcludedFrom raw (position t.center) L base
      rw [hcenter, hcenter']
      exact hexcluded
  | scan_shift c s s' t hm hav hc hcmp hmt hr hg hb =>
    intro hmode
    simp at hmode
  | scan_fallback c s s' t hm hav hc hcmp hmt hg hr hb =>
    intro hmode
    simp at hmode
  | shift_one c s t hm hp hso =>
    intro hmode
    simp [hm] at hmode
  | shift_done c s o hm hp ho =>
    obtain ⟨⟨w, hw⟩, honly⟩ := hstage.1 hm
    intro _ hguard
    rcases hguard with hidle | hfalse
    · have hsourceIdle : s.chain = .idle := hidle
      rw [hw] at hsourceIdle
      cases hsourceIdle
    · have hsourceFalse : s.periodOnly = false := hfalse
      rw [honly] at hsourceFalse
      cases hsourceFalse
  | replayStart c s t o hm hr ho ho' =>
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hlower,_⟩ := hr
    exact lowerAt_of_reset hlower
  | restart c s t hm hr =>
    obtain ⟨w, hw, hmargin, hlast, hlag, rfl⟩ := hr
    intro _ _ L hL
    obtain ⟨Rad, hRad, -, -, hlastExcluded⟩ :=
      (hstage.2 hm w hw).2 ⟨w, hw, hmargin, hlast, hlag⟩
    obtain ⟨hbaseLower, hexcluded⟩ := hlastExcluded L hL
    refine ⟨Rad, ?_, hbaseLower, hexcluded⟩
    show Rad ≤ (value s.radius).toNat
    rw [hRad.2]
    simp
  | copy_one _ _ _ hm _ _ | copy_done _ _ _ hm _ _
  | home_start _ _ _ hm _ _ | home_step _ _ _ hm _ _
  | fpp_slice _ _ _ hm _ | fpp_done _ _ _ hm _
  | markEnd_found _ _ _ hm _ _ | markEnd_step _ _ _ hm _ _
  | choose_select _ _ _ hm _ _ _ | choose_step _ _ _ hm _ _
  | rewind_done _ _ _ hm _ _ | rewind_one _ _ _ hm _ _ _
  | rewind_pair _ _ _ hm _ _ _ =>
    intro hmode
    first
      | (simp [hm] at hmode)
      | (simp at hmode)

/-- At a chain-idle scan state no semiperiod up to the lower bound is a period of the scan
span: the `hlow` input of the fallback move inequality. -/
theorem no_lower_period_at_scan {raw : List (Fin 2)} {c : Control} {s : GalilVM} {Rad : ℕ}
    (hlowerAt : LowerAt raw c s) (hm : c.mode = .scan)
    (hguard : s.chain = .idle ∨ s.periodOnly = false)
    (hscan : ScanInvariant raw (position s.center) Rad s.left s.right)
    (hradius : RadiusRep s.radius Rad) :
    ∀ δ, 0 < δ → δ ≤ (value s.lower).toNat →
      ¬ HasPeriod (Span raw (position s.center) Rad) (2*δ) := by
  intro δ hδ0 hδ
  have hnonneg : 0 ≤ value s.lower := by
    by_contra hneg
    have : (value s.lower).toNat = 0 := by omega
    omega
  obtain ⟨base, hbaseRadius, -, hexcluded⟩ :=
    hlowerAt hm hguard (value s.lower).toNat (by omega)
  rw [hradius.2] at hbaseRadius
  exact hexcluded Rad (by simpa using hbaseRadius) (scan_radius_lt hscan) hscan.palindrome δ hδ0 hδ

/-- The move payload of a chain born while the search runs above the lower bound of `s`: the DP
excludes the semiperiods strictly between that bound and the least candidate. -/
def MovePayload (raw : List (Fin 2)) (s : GalilVM) : ℕ → ℕ → Prop :=
  fun C H => MoveAbove raw C (value s.lower).toNat H

/-- The birth payload from the excluded lower bound. -/
theorem birthMinimal_of_lowerAt {raw : List (Fin 2)} {c₀ : Control} {r₀ : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    {k : ℕ} {y : State GalilVM}
    (hrun : CloseoutCheckW.StepsIMWC centre place entry q first raw k ⟨c₀,r₀⟩ y)
    (hm : y.ctl.mode = .scan) (hlowerAt : LowerAt raw y.ctl y.vm) :
    BirthMinimal centre place entry (MovePayload raw y.vm) raw y.vm := by
  intro a vq hidle he hf
  obtain ⟨H, hcopy, hfuture, hmove⟩ :=
    PalPeg.CanonicalSearchHistory.birthMinimals_packed centre place entry q first hP hI hrun hm
      hidle he hf (fun lower hlowerEq => by
        obtain ⟨base, -, hbaseLower, hexcluded⟩ := hlowerAt hm (Or.inl hidle) lower (by
          rw [← searchEffect_lower_eq he, hlowerEq, ofNat_value])
        exact hexcluded.toLowerExcluded hbaseLower)
  rw [searchEffect_lower_eq he] at hmove
  exact ⟨H, hcopy, hfuture, hmove⟩

/-- One tick keeps the minimal-period payload.  The payload reads the lower bound of the state;
the three ticks that change the lower bound (`init`, `replayStart`, `restart`) start from a state
whose payload is empty and land on an idle chain. -/
theorem modeMinimal_tick_lower {raw : List (Fin 2)} {x y : State GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (ht : Tick (galilFrameS (PofC centre place entry raw) q first) 2048 x y)
    (hsource : ModeMinimal (MovePayload raw x.vm) raw x.ctl x.vm)
    (hpackX : PalPeg.CloseoutPackW.IPackMW centre place entry q first raw x)
    (hpackY : PalPeg.CloseoutPackW.IPackMW centre place entry q first raw y)
    (haux : PalPeg.CloseoutPackRun2.AuxPack x.ctl x.vm)
    (hbirth : x.ctl.mode = .scan →
      BirthMinimal centre place entry (MovePayload raw x.vm) raw x.vm) :
    ModeMinimal (MovePayload raw y.vm) raw y.ctl y.vm := by
  by_cases hkeep : y.vm.lower = x.vm.lower
  · have hpayload : MovePayload raw y.vm = MovePayload raw x.vm := by
      unfold MovePayload
      rw [hkeep]
    rw [hpayload]
    exact modeMinimal_tick_packed centre place entry q first hP ht hsource hpackX hpackY haux
      hbirth
  · have hchanged : x.ctl.mode = .init ∨ x.ctl.mode = .replayStart ∨
        (x.ctl.mode = .scan ∧ restartVM entry x.vm y.vm) := by
      by_contra hnone
      push_neg at hnone
      exact hkeep (lower_eq_of_regular_tick centre place entry q first ht hnone.1 hnone.2.1
        (fun hm hr => hnone.2.2 hm hr))
    have hsource' : ModeMinimal (MovePayload raw y.vm) raw x.ctl x.vm := by
      rcases hchanged with h | h | ⟨hm, w, hw, -⟩
      · simp [ModeMinimal, h]
      · simp [ModeMinimal, h]
      · simp [ModeMinimal, hm, ScanMinimal, hw]
    exact modeMinimal_tick_packed centre place entry q first hP ht hsource' hpackX hpackY haux
      (fun hm a vq hidle => by
        rcases hchanged with h | h | ⟨-, w, hw, -⟩
        · rw [h] at hm; cases hm
        · rw [h] at hm; cases hm
        · rw [hw] at hidle; cases hidle)

/-- While the centre has not moved since the chain was born (first round), the chain carries its
birth payload itself, not only the thresholded form that survives a shift. -/
def FirstRoundSem (raw : List (Fin 2)) (c : Control) (s : GalilVM) : Prop :=
  c.mode = .scan → (s.chain = .idle ∨ s.periodOnly = false) →
    Sem (MovePayload raw s) raw (position s.center) s.chain

theorem firstRoundSem_of_idle {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    (hidle : s.chain = .idle) : FirstRoundSem raw c s := by
  intro _ _
  rw [hidle]
  trivial

/-- One tick keeps `FirstRoundSem`: a scan tick is one chain tick at a fixed centre and a fixed
lower bound (`semWith_chainAt`, the birth hook is `BirthMinimal`), every other way into scan mode
lands on an idle chain or after a shift. -/
theorem firstRoundSem_tick {Extra : ℕ → ℕ → GalilScaffoldChainWatch.State → Prop}
    {raw : List (Fin 2)} {x y : State GalilVM}
    (ht : Tick (galilFrameS (PofC centre place entry raw) q first) 2048 x y)
    (hsource : FirstRoundSem raw x.ctl x.vm)
    (hstage : BrokenStage Extra x.ctl x.vm)
    (hbirth : x.ctl.mode = .scan →
      BirthMinimal centre place entry (MovePayload raw x.vm) raw x.vm) :
    FirstRoundSem raw y.ctl y.vm := by
  have hbackground : ∀ {c c' : Control} {s t : GalilVM}, x = ⟨c, s⟩ → y = ⟨c', t⟩ →
      c.mode = .scan → (galilFrameS (PofC centre place entry raw) q first).background s t →
      FirstRoundSem raw c' t := by
    intro c c' s t hx hy hm hb
    subst hx
    subst hy
    obtain ⟨-, -, hch, hcenter, honly, -, -, -, -, -, -, hse⟩ :=
      backgroundS_fields (PofC centre place entry raw) q first hb
    intro _ hguard
    have hsourceGuard := lowerGuard_source hch honly hguard
    have hpayload : MovePayload raw t = MovePayload raw s := by
      unfold MovePayload
      rw [show t.lower = s.lower from searchEffect_lower_eq hse]
    show Sem (MovePayload raw t) raw (position t.center) t.chain
    rw [hpayload, hcenter]
    exact sem_chainAt (hsource hm hsourceGuard)
      (fun hi hf => hbirth hm false _ hi hse (by simpa using hf)) hch
  cases ht with
  | init c s t hm hi =>
    obtain ⟨_,_,_,_,_,_,_,_,_,hch,_⟩ := hi
    exact firstRoundSem_of_idle hch
  | scan_wait c s t hm hav hb => exact hbackground rfl rfl hm hb
  | scan_count c s t hm hav hc hb => exact hbackground rfl rfl hm hb
  | scan_match c s s' t o hm hav hc hcmp hmt hpl ho =>
    have hcmp' : compareFound (PofC centre place entry raw) q first s s' := hcmp
    obtain ⟨vs, vq, a, -, -, -, hse, hch, heq⟩ := hcmp'
    obtain ⟨-, -, hchain', hcenter', -⟩ := PalPeg.WindowTick.compare_target_heads heq
    have hchain : t.chain = s'.chain := by rw [hpl]; split <;> rfl
    have hcenter : t.center = s'.center := by rw [hpl]; split <;> rfl
    have honly : t.periodOnly
        = if chainBorn (decide (vq.search.mode = .found)) s.chain then false
          else s.periodOnly := by
      have htarget : t.periodOnly = s'.periodOnly := by rw [hpl]; split <;> rfl
      rw [htarget, heq, afterBirth_periodOnly]
      cases a <;> rfl
    have hlowerEq : t.lower = s.lower := by
      have htarget : t.lower = s'.lower := by rw [hpl]; split <;> rfl
      rw [htarget, heq, afterBirth_lower]
      cases a <;> exact searchEffect_lower_eq hse
    intro _ hguard
    have hsourceGuard := lowerGuard_source (z := t.chain) (by rw [hchain, hchain']; exact hch)
      honly hguard
    have hpayload : MovePayload raw t = MovePayload raw s := by
      unfold MovePayload
      rw [hlowerEq]
    show Sem (MovePayload raw t) raw (position t.center) t.chain
    rw [hpayload, hcenter, hcenter', hchain, hchain']
    exact sem_chainAt (hsource hm hsourceGuard)
      (fun hi hf => hbirth hm a vq hi hse (by simpa using hf)) hch
  | scan_shift c s s' t hm hav hc hcmp hmt hr hg hb =>
    intro hmode
    simp at hmode
  | scan_fallback c s s' t hm hav hc hcmp hmt hg hr hb =>
    intro hmode
    simp at hmode
  | shift_one c s t hm hp hso =>
    intro hmode
    simp [hm] at hmode
  | shift_done c s o hm hp ho =>
    obtain ⟨⟨w, hw⟩, honly⟩ := hstage.1 hm
    intro _ hguard
    rcases hguard with hidle | hfalse
    · have hsourceIdle : s.chain = .idle := hidle
      rw [hw] at hsourceIdle
      cases hsourceIdle
    · have hsourceFalse : s.periodOnly = false := hfalse
      rw [honly] at hsourceFalse
      cases hsourceFalse
  | replayStart c s t o hm hr ho ho' =>
    obtain ⟨_,_,_,_,_,_,_,_,_,hch,_,_,_⟩ := hr
    exact firstRoundSem_of_idle hch
  | restart c s t hm hr =>
    obtain ⟨_,_,_,_,_,rfl⟩ := hr
    exact firstRoundSem_of_idle rfl
  | copy_one _ _ _ hm _ _ | copy_done _ _ _ hm _ _
  | home_start _ _ _ hm _ _ | home_step _ _ _ hm _ _
  | fpp_slice _ _ _ hm _ | fpp_done _ _ _ hm _
  | markEnd_found _ _ _ hm _ _ | markEnd_step _ _ _ hm _ _
  | choose_select _ _ _ hm _ _ _ | choose_step _ _ _ hm _ _
  | rewind_done _ _ _ hm _ _ | rewind_one _ _ _ hm _ _ _
  | rewind_pair _ _ _ hm _ _ _ =>
    intro hmode
    first
      | (simp [hm] at hmode)
      | (simp at hmode)

/-! ## The clock of a first-round chain along the run -/

open PalPeg.ChainClock PalPeg.SearchStageHistory in
/-- The radius at a birth: within two semiperiods, and the answer tape holds the semiperiod. -/
theorem birth_radius {raw : List (Fin 2)} {clock : ℕ} {s : GalilVM} {a : Bool} {vq : SearchVM}
    (hdata : PalPeg.SearchStageRun.StageData centre place entry raw clock s)
    (hstep : searchStep ((PofC centre place entry raw).place s) a (searchLens.get s) vq)
    (hfound : vq.search.mode = .found) :
    1 ≤ remainingBits (vq.dp.config.tapes 11) ∧
      value s.radius ≤ 2 * (remainingBits (vq.dp.config.tapes 11) : ℤ) := by
  obtain ⟨lower, hbudget, hhistory, hnotFound⟩ := hdata
  have hrun := run_of_found hstep hfound hnotFound
  have hquanta := hstep
  simp only [searchStep, hrun] at hquanta
  obtain ⟨H, hcopy, hpositive, hradius⟩ :=
    found_radius_le hbudget hhistory hrun hquanta.1 hfound ((PofC centre place entry raw).centre s)
  rw [remainingBits_of_answerAhead hcopy.1]
  exact ⟨hpositive, hradius⟩

open PalPeg.ChainClock in
/-- While a first-round chain has work left, the time since the last match and that work fit
into the distance of the radius from four semiperiods. -/
def ClockAt (c : Control) (s : GalilVM) : Prop :=
  c.mode = .scan → s.periodOnly = false → 0 < chainWork s.chain →
    chainWork s.chain + (2048 - (c.clock : ℤ))
      ≤ 2047 * (4 * chainPeriod s.chain - value s.radius)

open PalPeg.ChainClock in
/-- One tick keeps `ClockAt`. -/
theorem clockAt_tick {Extra : ℕ → ℕ → GalilScaffoldChainWatch.State → Prop}
    {raw : List (Fin 2)} {x y : State GalilVM}
    (ht : Tick (galilFrameS (PofC centre place entry raw) q first) 2048 x y)
    (hsource : ClockAt x.ctl x.vm)
    (hclock : 1 ≤ x.ctl.clock ∧ x.ctl.clock ≤ 2048)
    (hwinX : WindowRunPack raw x.ctl x.vm)
    (hledger : LedgerAt x.ctl x.vm)
    (hstage : BrokenStage Extra x.ctl x.vm)
    (hdata : x.ctl.mode = .scan → x.vm.chain = .idle →
      PalPeg.SearchStageRun.StageData centre place entry raw x.ctl.clock x.vm) :
    ClockAt y.ctl y.vm := by
  have hchainTick : ∀ {c : Control} {s : GalilVM} {a found : Bool} {vq : SearchVM} {z : ChainVM}
      {E' R' : ℤ} {targetOnly : Bool}, x = ⟨c, s⟩ → c.mode = .scan →
      searchEffect (PofC centre place entry raw) a s vq → found = decide (vq.search.mode = .found) →
      chainAt a found (vq.dp.config.tapes 11) ((PofC centre place entry raw).centre s)
        ((PofC centre place entry raw).place s) s.center s.radius s.chain z →
      targetOnly = (if chainBorn found s.chain then false else s.periodOnly) →
      (if a then E' + 2047 ≤ 2048 - (c.clock : ℤ) else E' ≤ 2048 - (c.clock : ℤ) + 1) →
      0 ≤ E' ∧ E' ≤ 2047 →
      R' = value s.radius + (if a then 1 else 0) →
      targetOnly = false → 0 < chainWork z → chainWork z + E' ≤ 2047 * (4 * chainPeriod z - R') := by
    intro c s a found vq z E' R' targetOnly hx hm hse hfoundEq hch honly htime hbounds hradius
      htargetFalse
    subst hx
    have hledgerScan := hledger (Or.inl hm)
    simp only [shiftDebt, hm, show (Mode.scan = Mode.shift) = False from by simp,
      if_false] at hledgerScan
    have hclockZ : (1 : ℤ) ≤ (c.clock : ℤ) := by exact_mod_cast hclock.1
    refine clock_chainAt hch hwinX.coupled.block hledgerScan (watch_unbroken_of_window hwinX) rfl
      (fun hwork => ?_) (fun hidle hfound => ?_) htime ⟨hbounds.1, hbounds.2, by omega⟩ hradius
    · have hnotIdle : s.chain ≠ .idle := by
        intro hidle
        rw [hidle] at hwork
        simp [chainWork] at hwork
      have hsourceOnly : s.periodOnly = false := by
        unfold chainBorn at honly
        rw [isIdle_false_of_ne hnotIdle] at honly
        rw [honly] at htargetFalse
        simpa using htargetFalse
      exact hsource hm hsourceOnly hwork
    · have hstep : searchStep ((PofC centre place entry raw).place s) a (searchLens.get s) vq := by
        rcases hse with ⟨-, hh⟩ | ⟨hne, -⟩
        · exact hh
        · exact absurd hidle hne
      have hfoundMode : vq.search.mode = .found := by
        rw [hfoundEq] at hfound
        exact of_decide_eq_true hfound
      exact birth_radius centre place entry (hdata hm hidle) hstep hfoundMode
  have hbackground : ∀ {c c' : Control} {s t : GalilVM}, x = ⟨c, s⟩ → y = ⟨c', t⟩ →
      c.mode = .scan → (galilFrameS (PofC centre place entry raw) q first).background s t →
      ((2048 : ℤ) - (c'.clock : ℤ) ≤ 2048 - (c.clock : ℤ) + 1) →
      (1 ≤ c'.clock ∧ c'.clock ≤ 2048) → ClockAt c' t := by
    intro c c' s t hx hy hm hb htime hbounds
    subst hy
    obtain ⟨-, -, hch, -, honly, hradius, -, -, -, -, -, hse⟩ :=
      backgroundS_fields (PofC centre place entry raw) q first hb
    intro _ htargetFalse hwork
    have hclockZ : (1 : ℤ) ≤ (c'.clock : ℤ) := by exact_mod_cast hbounds.1
    have hclockLe : (c'.clock : ℤ) ≤ 2048 := by exact_mod_cast hbounds.2
    have := hchainTick (a := false) (E' := 2048 - (c'.clock : ℤ)) (R' := value t.radius) hx hm hse
      rfl hch honly (by simpa using htime) ⟨by omega, by omega⟩ (by rw [hradius]; simp)
      htargetFalse hwork
    exact this
  cases ht with
  | init c s t hm hi =>
    obtain ⟨_,_,_,_,_,_,_,_,_,hch,_⟩ := hi
    intro _ _ hwork
    rw [hch] at hwork
    simp [chainWork] at hwork
  | scan_wait c s t hm hav hb =>
    exact hbackground rfl rfl hm hb
      (by show (2048 : ℤ) - (c.clock : ℤ) ≤ 2048 - (c.clock : ℤ) + 1; omega) hclock
  | scan_count c s t hm hav hc hb =>
    have h1 : 1 ≤ c.clock := hclock.1
    have h2 : c.clock ≤ 2048 := hclock.2
    refine hbackground rfl rfl hm hb ?_ ⟨by show 1 ≤ c.clock - 1; omega, by show c.clock - 1 ≤ 2048; omega⟩
    show (2048 : ℤ) - ((c.clock - 1 : ℕ) : ℤ) ≤ 2048 - (c.clock : ℤ) + 1
    omega
  | scan_match c s s' t o hm hav hc hcmp hmt hpl ho =>
    have hcmp' : compareFound (PofC centre place entry raw) q first s s' := hcmp
    obtain ⟨vs, vq, a, -, -, hiff, hse, hch, heq⟩ := hcmp'
    have ha : a = true := by
      cases a with
      | true => rfl
      | false =>
        exfalso
        have hm' : read s'.left = read s'.right := hmt
        rw [heq, afterBirth_left, afterBirth_right] at hm'
        exact absurd (hiff.2 hm') (by simp)
    subst ha
    obtain ⟨-, -, hchain', -, -⟩ := PalPeg.WindowTick.compare_target_heads heq
    have hchain : t.chain = s'.chain := by rw [hpl]; split <;> rfl
    have honly : t.periodOnly
        = if chainBorn (decide (vq.search.mode = .found)) s.chain then false
          else s.periodOnly := by
      have htarget : t.periodOnly = s'.periodOnly := by rw [hpl]; split <;> rfl
      rw [htarget, heq, afterBirth_periodOnly]
      rfl
    have hradius : t.radius = inc s.radius := by
      have htarget : t.radius = s'.radius := by rw [hpl]; split <;> rfl
      rw [htarget, heq, afterBirth_radius]
      rfl
    intro _ htargetFalse hwork
    have hworkChain : 0 < chainWork vs.chain := by
      have : t.chain = vs.chain := hchain.trans hchain'
      rw [← this]
      exact hwork
    have hresult := hchainTick (a := true) (E' := 0) (R' := value t.radius) rfl hm hse rfl hch
      honly (by
        have : (c.clock : ℤ) = 1 := by exact_mod_cast hc
        simp only [if_true]
        omega) ⟨le_refl _, by norm_num⟩ (by rw [hradius, inc_value]; simp) htargetFalse hworkChain
    have htargetChain : t.chain = vs.chain := hchain.trans hchain'
    show chainWork t.chain + (2048 - ((2048 : ℕ) : ℤ)) ≤ 2047 * (4 * chainPeriod t.chain - value t.radius)
    rw [htargetChain]
    push_cast
    simpa using hresult
  | scan_shift c s s' t hm hav hc hcmp hmt hr hg hb =>
    intro hmode
    simp at hmode
  | scan_fallback c s s' t hm hav hc hcmp hmt hg hr hb =>
    intro hmode
    simp at hmode
  | shift_one c s t hm hp hso =>
    intro hmode
    simp [hm] at hmode
  | shift_done c s o hm hp ho =>
    obtain ⟨-, honly⟩ := hstage.1 hm
    intro _ hfalse
    have hsourceFalse : s.periodOnly = false := hfalse
    rw [honly] at hsourceFalse
    cases hsourceFalse
  | replayStart c s t o hm hr ho ho' =>
    obtain ⟨_,_,_,_,_,_,_,_,_,hch,_,_,_⟩ := hr
    intro _ _ hwork
    rw [hch] at hwork
    simp [chainWork] at hwork
  | restart c s t hm hr =>
    obtain ⟨_,_,_,_,_,rfl⟩ := hr
    intro _ _ hwork
    simp [chainWork] at hwork
  | copy_one _ _ _ hm _ _ | copy_done _ _ _ hm _ _
  | home_start _ _ _ hm _ _ | home_step _ _ _ hm _ _
  | fpp_slice _ _ _ hm _ | fpp_done _ _ _ hm _
  | markEnd_found _ _ _ hm _ _ | markEnd_step _ _ _ hm _ _
  | choose_select _ _ _ hm _ _ _ | choose_step _ _ _ hm _ _
  | rewind_done _ _ _ hm _ _ | rewind_one _ _ _ hm _ _ _
  | rewind_pair _ _ _ hm _ _ _ =>
    intro hmode
    first
      | (simp [hm] at hmode)
      | (simp at hmode)

/-! ## The period block against the text, along the run -/

open PalPeg.ChainBlockText in
/-- One chain tick of the machine keeps `BlockText`; a birth starts it at the walker of the
comparison, the place of the centre. -/
theorem blockText_chainAt {a found : Bool} {answer : GalilScaffoldTape.Tape} {cc : Fin 3}
    {walker : GalilScaffoldPlace.Place} {ver : PlaceHead} {radius : Counter} {x z : ChainVM}
    (hchainAt : chainAt a found answer cc walker ver radius x z)
    (hblock : BlockInv x)
    (hsource : x ≠ .idle → ∃ cc', BlockText (GalilScaffoldPlace.stream walker) cc' x) :
    ∃ cc', BlockText (GalilScaffoldPlace.stream walker) cc' z := by
  rcases hchainAt with ⟨hne, y, hstep, hzy⟩ | ⟨-, -, hz⟩ | ⟨-, -, hz⟩
  · obtain ⟨cc', htext⟩ := hsource hne
    have hy := blockText_step htext hblock hstep
    cases a with
    | false =>
      rw [if_neg (by simp)] at hzy
      subst hzy
      exact ⟨cc', hy⟩
    | true =>
      rw [if_pos rfl] at hzy
      exact ⟨cc', blockText_matched hy (blockInv_step hstep hblock) hzy⟩
  · rw [hz]
    exact ⟨cc, trivial⟩
  · have hstart := blockText_chainStart answer cc walker ver radius
    cases a with
    | false =>
      rw [if_neg (by simp)] at hz
      rw [hz]
      exact ⟨cc, hstart⟩
    | true =>
      rw [if_pos rfl] at hz
      exact ⟨cc, blockText_matched hstart (by unfold chainStart; exact onPrefix_start cc) hz⟩

open PalPeg.ChainBlockText in
/-- In the first round of a chain the letters of its period block are the text left of the
centre: the stream of the centre's place. -/
def BlockTextAt (raw : List (Fin 2)) (c : Control) (s : GalilVM) : Prop :=
  c.mode = .scan → s.periodOnly = false →
    ∃ cc, BlockText (GalilScaffoldPlace.stream ((PofC centre place entry raw).place s)) cc s.chain

open PalPeg.ChainBlockText in
/-- One tick keeps `BlockTextAt`. -/
theorem blockTextAt_tick {Extra : ℕ → ℕ → GalilScaffoldChainWatch.State → Prop}
    {raw : List (Fin 2)} {x y : State GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (ht : Tick (galilFrameS (PofC centre place entry raw) q first) 2048 x y)
    (hsource : BlockTextAt centre place entry raw x.ctl x.vm)
    (hwinX : WindowRunPack raw x.ctl x.vm)
    (hstage : BrokenStage Extra x.ctl x.vm) :
    BlockTextAt centre place entry raw y.ctl y.vm := by
  have hchainTick : ∀ {c : Control} {s t : GalilVM} {a found : Bool} {vq : SearchVM},
      x = ⟨c, s⟩ → c.mode = .scan →
      chainAt a found (vq.dp.config.tapes 11) ((PofC centre place entry raw).centre s)
        ((PofC centre place entry raw).place s) s.center s.radius s.chain t.chain →
      t.center = s.center →
      t.periodOnly = (if chainBorn found s.chain then false else s.periodOnly) →
      t.periodOnly = false →
      ∃ cc, BlockText (GalilScaffoldPlace.stream ((PofC centre place entry raw).place t)) cc
        t.chain := by
    intro c s t a found vq hx hm hch hcenter honly htargetFalse
    subst hx
    rw [hP.2 t s hcenter]
    refine blockText_chainAt hch hwinX.coupled.block (fun hne => ?_)
    have hsourceOnly : s.periodOnly = false := by
      unfold chainBorn at honly
      rw [isIdle_false_of_ne hne] at honly
      rw [honly] at htargetFalse
      simpa using htargetFalse
    exact hsource hm hsourceOnly
  cases ht with
  | init c s t hm hi =>
    obtain ⟨_,_,_,_,_,_,_,_,_,hch,_⟩ := hi
    intro _ _
    rw [hch]
    exact ⟨0, trivial⟩
  | scan_wait c s t hm hav hb =>
    obtain ⟨-, -, hch, hcenter, honly, -⟩ :=
      backgroundS_fields (PofC centre place entry raw) q first hb
    intro _ hfalse
    exact hchainTick rfl hm hch hcenter honly hfalse
  | scan_count c s t hm hav hc hb =>
    obtain ⟨-, -, hch, hcenter, honly, -⟩ :=
      backgroundS_fields (PofC centre place entry raw) q first hb
    intro _ hfalse
    exact hchainTick rfl hm hch hcenter honly hfalse
  | scan_match c s s' t o hm hav hc hcmp hmt hpl ho =>
    have hcmp' : compareFound (PofC centre place entry raw) q first s s' := hcmp
    obtain ⟨vs, vq, a, -, -, -, -, hch, heq⟩ := hcmp'
    obtain ⟨-, -, hchain', hcenter', -⟩ := PalPeg.WindowTick.compare_target_heads heq
    have hchain : t.chain = s'.chain := by rw [hpl]; split <;> rfl
    have hcenter : t.center = s'.center := by rw [hpl]; split <;> rfl
    have honly : t.periodOnly
        = if chainBorn (decide (vq.search.mode = .found)) s.chain then false
          else s.periodOnly := by
      have htarget : t.periodOnly = s'.periodOnly := by rw [hpl]; split <;> rfl
      rw [htarget, heq, afterBirth_periodOnly]
      cases a <;> rfl
    intro _ hfalse
    exact hchainTick (a := a) (vq := vq) rfl hm (by rw [hchain, hchain']; exact hch)
      (hcenter.trans hcenter') honly hfalse
  | scan_shift c s s' t hm hav hc hcmp hmt hr hg hb =>
    intro hmode
    simp at hmode
  | scan_fallback c s s' t hm hav hc hcmp hmt hg hr hb =>
    intro hmode
    simp at hmode
  | shift_one c s t hm hp hso =>
    intro hmode
    simp [hm] at hmode
  | shift_done c s o hm hp ho =>
    obtain ⟨-, honly⟩ := hstage.1 hm
    intro _ hfalse
    have hsourceFalse : s.periodOnly = false := hfalse
    rw [honly] at hsourceFalse
    cases hsourceFalse
  | replayStart c s t o hm hr ho ho' =>
    obtain ⟨_,_,_,_,_,_,_,_,_,hch,_,_,_⟩ := hr
    intro _ _
    rw [hch]
    exact ⟨0, trivial⟩
  | restart c s t hm hr =>
    obtain ⟨_,_,_,_,_,rfl⟩ := hr
    intro _ _
    exact ⟨0, trivial⟩
  | copy_one _ _ _ hm _ _ | copy_done _ _ _ hm _ _
  | home_start _ _ _ hm _ _ | home_step _ _ _ hm _ _
  | fpp_slice _ _ _ hm _ | fpp_done _ _ _ hm _
  | markEnd_found _ _ _ hm _ _ | markEnd_step _ _ _ hm _ _
  | choose_select _ _ _ hm _ _ _ | choose_step _ _ _ hm _ _
  | rewind_done _ _ _ hm _ _ | rewind_one _ _ _ hm _ _ _
  | rewind_pair _ _ _ hm _ _ _ =>
    intro hmode
    first
      | (simp [hm] at hmode)
      | (simp at hmode)

/-- The run invariant: the minimal-period payload, the excluded lower bound of the running
search, and the excluded `last` of a broken chain at a restart-guard state. -/
structure MinimalAcrossRestart (raw : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  minimal : ModeMinimal (MovePayload raw s) raw c s
  lowerAt : LowerAt raw c s
  broken : BrokenStage (LastExcluded raw) c s
  firstRound : FirstRoundSem raw c s
  clock : ClockAt c s
  blockText : BlockTextAt centre place entry raw c s

/-- `MinimalAcrossRestart` at every point of a packed run out of an `InvLPS` origin whose own
lower bound is excluded. -/
theorem minimalAcrossRestart_packed {raw : List (Fin 2)} {c₀ : Control} {r₀ : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    (horigin : LowerAt raw c₀ r₀)
    {k : ℕ} {y : State GalilVM}
    (hrun : CloseoutCheckW.StepsIMWC centre place entry q first raw k ⟨c₀,r₀⟩ y) :
    MinimalAcrossRestart centre place entry raw y.ctl y.vm := by
  obtain ⟨g, hg0, hgk, htr, hcan, hpk⟩ := hrun
  have hprefix : ∀ i, i ≤ k →
      CloseoutCheckW.StepsIMWC centre place entry q first raw i ⟨c₀,r₀⟩ (g i) := by
    intro i hi
    exact ⟨g, hg0, rfl,
      ⟨fun j hj => htr.tick j (by omega), fun j hj => htr.good j (by omega)⟩,
      fun j hj => hcan j (by omega), fun j hj => hpk j (by omega)⟩
  have hiMode : c₀.mode = .scan := (PalPeg.GalilOracleLocal.invS_mode hI.1.1.1.1.1).1
  have hiChain : r₀.chain = .idle := by
    rcases hI.1.1.1.1.1 with h | ⟨_, h⟩
    · obtain ⟨_, _, h⟩ := h.rest; exact h.1
    · exact h.chainIdle
  have hlv0 := PalPeg.GalilOracleLeaves2.hlive_of_invLPC centre place entry q first hI.1
  have haux0 : PalPeg.CloseoutPackRun2.AuxPack c₀ r₀ :=
    ⟨PalPeg.CloseoutPackRun.coupled_of_invLPC hI.1,
      PalPeg.CloseoutPackRun.front_of_invLPC hI.1,
      PalPeg.CloseoutPackRun.copyPack_of_invLPC hI.1⟩
  have haux : ∀ i, i ≤ k → PalPeg.CloseoutPackRun2.AuxPack (g i).ctl (g i).vm := by
    intro i hi
    have hs := PalPeg.CloseoutPackRun2.steps_of_trace htr i hi
    rw [hg0] at hs
    exact PalPeg.CloseoutPackRun2.auxPack_steps centre place entry q first hlv0 haux0 hs
  have hboundary := noBoundaryBreak_packed centre place entry q first hP hI
  have hall : ∀ i, i ≤ k → MinimalAcrossRestart centre place entry raw (g i).ctl (g i).vm := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [hg0]
      exact ⟨by simp [ModeMinimal, hiMode, ScanMinimal, hiChain], horigin,
        brokenStage_of_not_broken (by rw [hiMode]; decide)
          (fun w hw => by rw [hiChain] at hw; cases hw),
        firstRoundSem_of_idle hiChain,
        fun _ _ hwork => by
          rw [hiChain] at hwork
          simp [PalPeg.ChainClock.chainWork] at hwork,
        fun _ _ => by rw [hiChain]; exact ⟨0, trivial⟩⟩
    | succ i ih =>
      intro hik
      have hsource := ih (by omega)
      have htick := htr.tick i (by omega)
      have hwinX := (hpk i (by omega)).win hP
      have hbirthSource : (g i).ctl.mode = .scan →
          BirthMinimal centre place entry (MovePayload raw (g i).vm) raw (g i).vm :=
        fun hm => birthMinimal_of_lowerAt centre place entry q first hP hI
          (hprefix i (by omega)) hm hsource.lowerAt
      obtain ⟨hstageSource, hfieldSource⟩ :=
        PalPeg.SearchStageRun.stageAt_field_packed centre place entry q first hP hI
          (hprefix i (by omega))
      refine ⟨?_, lowerAt_tick centre place entry q first htick hsource.lowerAt hsource.broken,
        ?_, firstRoundSem_tick centre place entry q first htick hsource.firstRound
          hsource.broken hbirthSource,
        clockAt_tick centre place entry q first htick hsource.clock
          ⟨hfieldSource.clock_pos, hfieldSource.clock_le⟩ hwinX
          (ledgerAt_packed centre place entry q first hP hI (hprefix i (by omega)))
          hsource.broken hstageSource.scan,
        blockTextAt_tick centre place entry q first hP htick hsource.blockText hwinX
          hsource.broken⟩
      · exact modeMinimal_tick_lower centre place entry q first hP htick hsource.minimal
          (hpk i (by omega)) (hpk (i+1) (by omega)) (haux i (by omega)) hbirthSource
      · refine brokenStage_tick centre place entry q first htick (hcan i (by omega)).canonical
          hsource.broken
          (ledgerAt_packed centre place entry q first hP hI (hprefix i (by omega)))
          hwinX ((hpk (i+1) (by omega)).win hP) (watch_unbroken_of_window hwinX)
          (fun c s s' w1 w' hx hm hcmp hmt hstep hbreak =>
            hboundary i c s s' (hx ▸ hprefix i (by omega)) hm hcmp hmt w1 w' hstep hbreak) ?_
        intro c s s' w1 w' hx hm hcmp hmt hstep hbreak hmargin Rad hRadValue L hL
        have hrunSource : CloseoutCheckW.StepsIMWC centre place entry q first raw i ⟨c₀,r₀⟩
            ⟨c, s⟩ := hx ▸ hprefix i (by omega)
        have hwin : WindowRunPack raw c s :=
          (PalPeg.CloseoutCheckW.ipackMW_last_of_stepsIMWC centre place entry q first
            hrunSource).win hP
        obtain ⟨rad, hscan⟩ := scanInvariant_packed centre place entry q first hrunSource hm
        obtain ⟨R, hR, hright⟩ := hwin.radiusScan hm
        have hrad : rad = R := by
          have h1 : position s.right = position s.center + rad := hscan.rightPos
          have h2 : position s.right = position s.center + R := hright
          omega
        subst hrad
        have hledger := ledgerAt_packed centre place entry q first hP hI hrunSource (Or.inl hm)
        simp only [shiftDebt, hm, show (Mode.scan = Mode.shift) = False from by simp,
          if_false] at hledger
        have hminimal : ScanMinimal (MovePayload raw s) raw s := by
          have hmode := hsource.minimal
          rw [hx] at hmode
          simpa [ModeMinimal, hm] using hmode
        exact lowerExcluded_at_break hwin hm hscan hR hledger hminimal hstep hbreak hmargin
          (hboundary i c s s' hrunSource hm hcmp hmt w1 w' hstep hbreak) hL hRadValue
  rw [← hgk]
  exact hall k le_rfl

/-- **The origin's lower bound is excluded.**  An `InvLPS` origin that the packed run reaches
from boot inherits `LowerAt` from the first tick, where the `init` entry resets the lower bound. -/
theorem lowerAt_of_packedFromBoot {a : Fin 2} {rest : List (Fin 2)} {c₀ : Control} {r₀ : GalilVM}
    (hP : Decodes (PofC centre place entry (a :: rest)))
    (hI : InvLPS (PofC centre place entry (a :: rest)) q first (a :: rest) c₀ r₀)
    (hboot : CloseoutCheckW.PackedFromBoot centre place entry q first (a :: rest) ⟨c₀, r₀⟩) :
    LowerAt (a :: rest) c₀ r₀ := by
  obtain ⟨k, g, hg0, hgk, htr, hcan, hpk⟩ := hboot
  have hiMode : c₀.mode = .scan := (PalPeg.GalilOracleLocal.invS_mode hI.1.1.1.1.1).1
  cases k with
  | zero =>
    exfalso
    rw [hg0] at hgk
    have hmode : (PalPeg.GalilFinalAssembly.boot (a :: rest)).ctl.mode = c₀.mode := by rw [hgk]
    rw [hiMode] at hmode
    have hinit : Mode.init = Mode.scan := hmode
    cases hinit
  | succ k =>
    obtain ⟨c1, t, hsteps, hI1, -, -⟩ :=
      PalPeg.CloseoutStageBoot.invLPS_init centre place entry q first a rest
    obtain ⟨g', hg'0, hg'1, htr'⟩ := PalPeg.GalilCheckpoints.stepsAll_fn hsteps
    have htickBoot := htr'.tick 0 (by omega)
    rw [hg'0, hg'1] at htickBoot
    have htickRun := htr.tick 0 (by omega)
    rw [hg0] at htickRun
    have hcanonRun := (hcan 0 (by omega)).canonical
    rw [hg0] at hcanonRun
    have hfirst : g (0+1) = ⟨c1, t⟩ :=
      PalPeg.GalilTickFair.tick_canonical_unique htickRun hcanonRun htickBoot
        (PalPeg.GalilTickFair.canonical_of_init rfl htickBoot)
    have hlowerFirst : LowerAt (a :: rest) c1 t := by
      have hbootLower : LowerAt (a :: rest) (PalPeg.GalilFinalAssembly.boot (a :: rest)).ctl
          (PalPeg.GalilFinalAssembly.boot (a :: rest)).vm := fun hmode => by
        have hinit : Mode.init = Mode.scan := hmode
        cases hinit
      have hbootStage : BrokenStage (LastExcluded (a :: rest))
          (PalPeg.GalilFinalAssembly.boot (a :: rest)).ctl
          (PalPeg.GalilFinalAssembly.boot (a :: rest)).vm :=
        ⟨fun hmode => (by
            have hinit : Mode.init = Mode.shift := hmode
            cases hinit),
          fun hmode => (by
            have hinit : Mode.init = Mode.scan := hmode
            cases hinit)⟩
      exact lowerAt_tick centre place entry q first
        (x := PalPeg.GalilFinalAssembly.boot (a :: rest)) (y := ⟨c1, t⟩) htickBoot hbootLower
        hbootStage
    have hsuffix : CloseoutCheckW.StepsIMWC centre place entry q first (a :: rest) k ⟨c1, t⟩
        ⟨c₀, r₀⟩ :=
      ⟨fun i => g (i+1), hfirst, hgk,
        ⟨fun i hi => htr.tick (i+1) (by omega), fun i hi => htr.good (i+1) (by omega)⟩,
        fun i hi => hcan (i+1) (by omega), fun i hi => hpk (i+1) (by omega)⟩
    exact (minimalAcrossRestart_packed centre place entry q first hP hI1 hlowerFirst
      hsuffix).lowerAt

/-- **The minimal-period data of a scan state of a packed run whose origin is reached from
boot** — the input of `CanonicalChainMinimal.shiftPeriodMinimal_packed`. -/
theorem scanMinimal_packed {a : Fin 2} {rest : List (Fin 2)} {c₀ : Control} {r₀ : GalilVM}
    (hP : Decodes (PofC centre place entry (a :: rest)))
    (hI : InvLPS (PofC centre place entry (a :: rest)) q first (a :: rest) c₀ r₀)
    (hboot : CloseoutCheckW.PackedFromBoot centre place entry q first (a :: rest) ⟨c₀, r₀⟩)
    {k : ℕ} {c : Control} {s : GalilVM}
    (hrun : CloseoutCheckW.StepsIMWC centre place entry q first (a :: rest) k ⟨c₀,r₀⟩ ⟨c, s⟩)
    (hm : c.mode = .scan) :
    ScanMinimal (MovePayload (a :: rest) s) (a :: rest) s ∧
      BirthMinimal centre place entry (MovePayload (a :: rest) s) (a :: rest) s := by
  have hinvariant := minimalAcrossRestart_packed centre place entry q first hP hI
    (lowerAt_of_packedFromBoot centre place entry q first hP hI hboot) hrun
  exact ⟨by simpa [ModeMinimal, hm] using hinvariant.minimal,
    birthMinimal_of_lowerAt centre place entry q first hP hI hrun hm hinvariant.lowerAt⟩

#print axioms scanMinimal_packed

/-- **The fallback move inequality while the chain is idle**, on a packed run whose origin is
reached from boot.  Below the lower bound `LowerAt` excludes the semiperiods at the current
radius; above it the search does: in the middle of a stage through the candidate-free window of
its history (`SearchStageRun.dpPack_of_stage`), after the final stage through the DP result. -/
theorem move_of_idle {raw : List (Fin 2)} (hraw : raw ≠ []) {c₀ : Control} {r₀ : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    (hboot : CloseoutCheckW.PackedFromBoot centre place entry q first raw ⟨c₀, r₀⟩)
    {k : ℕ} {c : Control} {s : GalilVM} {vq : SearchVM} {z : ChainVM}
    (hrun : CloseoutCheckW.StepsIMWC centre place entry q first raw k ⟨c₀,r₀⟩ ⟨c, s⟩)
    (hm : c.mode = .scan) (hr : c.replaying = false) (hcan : canRight s.right)
    (hidle : s.chain = .idle)
    (hsearch : searchEffect (PofC centre place entry raw) false s vq) :
    let s1 := afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
      (afterMismatch s ⟨left s.left,right s.right,z⟩ vq)
    let ℓ := (value s.length).toNat
    let radius := chosenRadius
      ((GalilScaffoldPlace.stream (PalPeg.GalilTickFair.rightPlace s1)).take (ℓ+1))
    ℓ / 2 ≤ 4 * (ℓ / 2 + 1 - radius) := by
  obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hraw
  have hinvariant := minimalAcrossRestart_packed centre place entry q first hP hI
    (lowerAt_of_packedFromBoot centre place entry q first hP hI hboot) hrun
  have hwin : WindowRunPack (a :: rest) c s :=
    (PalPeg.CloseoutCheckW.ipackMW_last_of_stepsIMWC centre place entry q first hrun).win hP
  have hlow : ∀ Rad, ScanInvariant (a :: rest) (position s.center) Rad s.left s.right →
      (value s.radius = (Rad : ℤ)) ∧ ∀ δ, 0 < δ → δ ≤ (value s.lower).toNat →
        ¬ HasPeriod (Span (a :: rest) (position s.center) Rad) (2*δ) := by
    intro Rad hscan
    obtain ⟨R, hR, hright⟩ := hwin.radiusScan hm
    have hrad : Rad = R := by
      have h1 : position s.right = position s.center + Rad := hscan.rightPos
      have h2 : position s.right = position s.center + R := hright
      omega
    subst hrad
    exact ⟨hR.2, no_lower_period_at_scan hinvariant.lowerAt hm (Or.inl hidle) hscan hR⟩
  have hstage := (PalPeg.SearchStageRun.stageAt_packed centre place entry q first hP hI
    hrun).scan hm hidle
  by_cases hactive : PalPeg.SearchStageHistory.Active (searchLens.get s).search.mode
  · obtain ⟨-, -, rad, hscan, hlen⟩ :=
      PalPeg.CanonicalFallbackInput.counters centre place entry q first hI hrun hm hr
    obtain ⟨hradius, hlowRad⟩ := hlow rad hscan
    have hdp := PalPeg.SearchStageRun.dpPack_of_stage centre place entry hP hstage hactive
      hradius (hwin.centreRep (Or.inl hm)) hlowRad
    exact PalPeg.CanonicalFallbackInput.move_of_dpPack
      (centre := centre) (place := place) (entry := entry) (c := c)
      hP hscan hcan hlen (scan_radius_lt hscan) hdp rfl
  · obtain ⟨lower, -, hhistory, hnotFound⟩ := hstage
    have hmissed : (searchLens.get s).search.mode = .missed := by
      by_contra hne
      exact hactive ⟨hhistory.started, hnotFound, hne⟩
    have hvq : vq = searchLens.get s := by
      rcases hsearch with ⟨-, hstep⟩ | ⟨hne, -⟩
      · simpa [searchStep, hmissed] using hstep
      · exact absurd hidle hne
    exact move_of_idle_missed_packed centre place entry q first hP hI hrun
      (fun Rad hscan => (hlow Rad hscan).2) hm hr hcan hidle hsearch (by rw [hvq]; exact hmissed)

#print axioms move_of_idle

/-- A watch in phase `4` was a watch one internal step before (a watch born by `backDone` is in
phase `0`). -/
theorem watch_source_of_step {x : ChainVM} {w1 : GalilScaffoldChainWatch.State}
    (hstep : ChainStep x (.watch w1)) (hphase : w1.machine.control.phase = 4) :
    ∃ w0, x = .watch w0 ∧ GalilScaffoldChainWatch.Internal w0 w1 := by
  generalize hy : ChainVM.watch w1 = y at hstep
  cases hstep with
  | idle => cases hy
  | brokenIdle => cases hy
  | copyBit => cases hy
  | copyEnd => cases hy
  | backStep => cases hy
  | watchBreak => cases hy
  | backDone v h lag margin ver hf =>
    cases hy
    exact absurd hphase (by simp [watchControl])
  | watchStep w0 w1' hinternal =>
    cases hy
    exact ⟨w0, rfl, hinternal⟩

/-- A chain tick without a match that ends in a watch is one chain step. -/
theorem chainStep_of_chainAt_watch {found : Bool} {answer : GalilScaffoldTape.Tape} {cc : Fin 3}
    {walker : GalilScaffoldPlace.Place} {ver : PlaceHead} {radius : Counter} {x : ChainVM}
    {w1 : GalilScaffoldChainWatch.State}
    (hchainAt : chainAt false found answer cc walker ver radius x (.watch w1)) :
    ChainStep x (.watch w1) := by
  rcases hchainAt with ⟨-, y, hstep, hzy⟩ | ⟨-, -, hidle⟩ | ⟨-, -, hborn⟩
  · rw [if_neg (by simp)] at hzy
    rw [hzy]
    exact hstep
  · cases hidle
  · rw [if_neg (by simp)] at hborn
    unfold chainStart at hborn
    cases hborn

/-- **The fallback move inequality when a caught-up first-round watch is below phase `4`**, on a
packed run whose origin is reached from boot.  The distance is below four semiperiods (mark
ledger), it is the scan radius (lag `0`), and no semiperiod below the chain's is a period of the
span: up to the lower bound by `LowerAt`, above it by the birth payload `MoveAbove`. -/
theorem move_of_watch_short {raw : List (Fin 2)} (hraw : raw ≠ []) {c₀ : Control}
    {r₀ : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    (hboot : CloseoutCheckW.PackedFromBoot centre place entry q first raw ⟨c₀, r₀⟩)
    {k : ℕ} {c : Control} {s : GalilVM} {vq : SearchVM} {w1 : GalilScaffoldChainWatch.State}
    (hrun : CloseoutCheckW.StepsIMWC centre place entry q first raw k ⟨c₀,r₀⟩ ⟨c, s⟩)
    (hm : c.mode = .scan) (hr : c.replaying = false) (hcan : canRight s.right)
    (hchainAt : chainAt false (decide (vq.search.mode = .found)) (vq.dp.config.tapes 11)
      ((PofC centre place entry raw).centre s) ((PofC centre place entry raw).place s)
      s.center s.radius s.chain (.watch w1))
    (hfirstRound : s.periodOnly = false) (hzero : zero w1.lag = true)
    (hphase : w1.machine.control.phase ≠ 4) :
    let s1 := afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
      (afterMismatch s ⟨left s.left,right s.right,ChainVM.watch w1⟩ vq)
    let ℓ := (value s.length).toNat
    let radius := chosenRadius
      ((GalilScaffoldPlace.stream (PalPeg.GalilTickFair.rightPlace s1)).take (ℓ+1))
    ℓ / 2 ≤ 4 * (ℓ / 2 + 1 - radius) := by
  obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hraw
  have hinvariant := minimalAcrossRestart_packed centre place entry q first hP hI
    (lowerAt_of_packedFromBoot centre place entry q first hP hI hboot) hrun
  have hwin : WindowRunPack (a :: rest) c s :=
    (PalPeg.CloseoutCheckW.ipackMW_last_of_stepsIMWC centre place entry q first hrun).win hP
  obtain ⟨-, -, rad, hscan, hlen⟩ :=
    PalPeg.CanonicalFallbackInput.counters centre place entry q first hI hrun hm hr
  obtain ⟨R, hR, hright⟩ := hwin.radiusScan hm
  have hrad : rad = R := by
    have h1 : position s.right = position s.center + rad := hscan.rightPos
    have h2 : position s.right = position s.center + R := hright
    omega
  subst hrad
  have hstep := chainStep_of_chainAt_watch hchainAt
  have hunbroken1 := unbroken_of_step hstep (watch_unbroken_of_window hwin)
  have hnotIdle : s.chain ≠ .idle := by
    intro hidle
    rw [hidle] at hstep
    cases hstep
  -- the radius is the distance, below four semiperiods
  have hsum1 : PalPeg.GalilChainCoupling.SumRel (.watch w1) (value s.radius) :=
    (PalPeg.GalilChainCoupling.step_inv hstep (F := True) trivial (O := fun _ => True)
      hwin.coupled.block hwin.coupled.sum (fun _ _ _ => Or.inr trivial)).1
  have hdistance := hsum1 hunbroken1
  rw [PalPeg.GalilChainCoupling.value_zero_of_zero hzero, add_zero, hR.2] at hdistance
  have hledgerSource := ledgerAt_packed centre place entry q first hP hI hrun (Or.inl hm)
  simp only [shiftDebt, hm, show (Mode.scan = Mode.shift) = False from by simp,
    if_false] at hledgerSource
  have hledger : WatchLedger 0 w1 :=
    chainLedger_step hstep hwin.coupled.block hledgerSource hunbroken1
  have hshort := hledger.distance_lt_four hphase
  rw [hdistance] at hshort
  have hbound : rad ≤ 4 * periodLength w1 := by
    have : (rad : ℤ) < 4 * (periodLength w1 : ℤ) := hshort
    omega
  -- the payload of the stepped watch
  have hsem : Sem (MovePayload (a :: rest) s) (a :: rest) (position s.center) (.watch w1) :=
    sem_chainAt (hinvariant.firstRound hm (Or.inr hfirstRound))
      (fun hidle _ => absurd hidle hnotIdle) hchainAt
  have hpayload : MovePayload (a :: rest) s (position s.center) (periodLength w1) :=
    watch_moveMinimal hsem
  have hmove : MoveAbove (a :: rest) (position s.center) (value s.lower).toNat
      (periodLength w1) := hpayload
  have hlow := no_lower_period_at_scan hinvariant.lowerAt hm (Or.inr hfirstRound) hscan hR
  exact PalPeg.CanonicalFallbackInput.move_of_activeBound (c := c) (vq := vq)
    (z := ChainVM.watch w1) hscan hcan hlen (scan_radius_lt hscan)
    (fun g hg0 hgh hfour => by
      by_cases hle : g ≤ (value s.lower).toNat
      · exact hlow g hg0 hle
      · exact hmove rad (scan_radius_lt hscan) hscan.palindrome g (by omega) hgh hfour)
    hbound rfl

#print axioms move_of_watch_short

include q first in
/-- What a mismatching scan state knows about a first-round watch that comes out of its chain
tick caught up and in phase `4`: it was a watch before, it is unbroken, it has verified four
semiperiods, and its distance is the scan radius. -/
theorem caughtUp_facts {raw : List (Fin 2)} {c : Control} {s : GalilVM} {vq : SearchVM}
    {w1 : GalilScaffoldChainWatch.State}
    (hwin : WindowRunPack raw c s) (hm : c.mode = .scan)
    (hmis : read (left s.left) ≠ read (right s.right))
    (hsearch : searchEffect (PofC centre place entry raw) false s vq)
    (hchainAt : chainAt false (decide (vq.search.mode = .found)) (vq.dp.config.tapes 11)
      ((PofC centre place entry raw).centre s) ((PofC centre place entry raw).place s)
      s.center s.radius s.chain (.watch w1))
    (hfirstRound : s.periodOnly = false) (hzero : zero w1.lag = true)
    (hphase : w1.machine.control.phase = 4) :
    ChainStep s.chain (.watch w1) ∧ w1.machine.control.broken = false ∧
      4 * (periodLength w1 : ℤ) ≤ value w1.machine.control.distance ∧
      value w1.machine.control.distance = value s.radius ∧
      (afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
        (afterMismatch s ⟨left s.left,right s.right,ChainVM.watch w1⟩ vq)).periodOnly = false := by
  have hstep : ChainStep s.chain (.watch w1) := by
    rcases hchainAt with ⟨-, y, hstep, hzy⟩ | ⟨-, -, hidle⟩ | ⟨-, -, hborn⟩
    · rw [if_neg (by simp)] at hzy
      rw [hzy]
      exact hstep
    · cases hidle
    · rw [if_neg (by simp)] at hborn
      unfold chainStart at hborn
      cases hborn
  have hunbroken1 := unbroken_of_step hstep (watch_unbroken_of_window hwin)
  have hnotIdle : s.chain ≠ .idle := by
    intro hidle
    rw [hidle] at hstep
    cases hstep
  obtain ⟨hcmp, hmt⟩ := compare_of_mismatch centre place entry q first hmis hsearch hchainAt
  obtain ⟨-, hperiodOnly, -, -, hmismatchInv⟩ :=
    PalPeg.CloseoutPackRun40.compare'_inv (onLetterVM raw) leftFirstVM centre place entry
      q first hwin.coupled hm hcmp
  obtain ⟨-, -, hsum, hwatchOk⟩ := hmismatchInv hmt
  have htargetChain : (afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
      (afterMismatch s ⟨left s.left,right s.right,ChainVM.watch w1⟩ vq)).chain
        = .watch w1 := by
    rw [afterBirth_chain]
    simp [afterMismatch, searchLens, scanLens]
  rw [htargetChain] at hsum
  have hdistance := hsum hunbroken1
  rw [PalPeg.GalilChainCoupling.value_zero_of_zero hzero, add_zero] at hdistance
  refine ⟨hstep, hunbroken1, ?_, hdistance, (hperiodOnly hnotIdle).trans hfirstRound⟩
  rcases hwatchOk w1 htargetChain hunbroken1 with ⟨-, hfresh⟩ | hother
  · have h4 := PalPeg.WindowPack.four_of_freshC hfresh hphase
    unfold periodLength
    exact h4
  · rw [hfirstRound] at hother
    exact absurd hother.1 (by simp)

/-- **A caught-up first-round watch in phase `4` that predicts the place read passes the shift
guard**: the margin is the distance minus four semiperiods (`WatchLedger.balance`), hence not
negative. -/
theorem shiftGuard_of_caughtUp {raw : List (Fin 2)} {c₀ : Control} {r₀ : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    {k : ℕ} {c : Control} {s : GalilVM} {vq : SearchVM} {w1 : GalilScaffoldChainWatch.State}
    (hrun : CloseoutCheckW.StepsIMWC centre place entry q first raw k ⟨c₀,r₀⟩ ⟨c, s⟩)
    (hm : c.mode = .scan)
    (hmis : read (left s.left) ≠ read (right s.right))
    (hsearch : searchEffect (PofC centre place entry raw) false s vq)
    (hchainAt : chainAt false (decide (vq.search.mode = .found)) (vq.dp.config.tapes 11)
      ((PofC centre place entry raw).centre s) ((PofC centre place entry raw).place s)
      s.center s.radius s.chain (.watch w1))
    (hfirstRound : s.periodOnly = false) (hzero : zero w1.lag = true)
    (hphase : w1.machine.control.phase = 4)
    (hprediction : GalilScaffoldChainConsume.symbol w1.machine.control.period.focus
      = read (right s.right)) :
    shiftGuardVM (afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
      (afterMismatch s ⟨left s.left,right s.right,ChainVM.watch w1⟩ vq)) := by
  have hwin : WindowRunPack raw c s :=
    (PalPeg.CloseoutCheckW.ipackMW_last_of_stepsIMWC centre place entry q first hrun).win hP
  obtain ⟨hstep, hunbroken1, hfour, -, htargetOnly⟩ :=
    caughtUp_facts centre place entry q first hwin hm hmis hsearch hchainAt hfirstRound hzero
      hphase
  have hledgerSource := ledgerAt_packed centre place entry q first hP hI hrun (Or.inl hm)
  simp only [shiftDebt, hm, show (Mode.scan = Mode.shift) = False from by simp,
    if_false] at hledgerSource
  have hledger : WatchLedger 0 w1 :=
    chainLedger_step hstep hwin.coupled.block hledgerSource hunbroken1
  have hbalance := hledger.balance
  simp only [GalilScaffoldChainWatch.balance] at hbalance
  rw [PalPeg.GalilChainCoupling.value_zero_of_zero hzero] at hbalance
  have hmargin : negative w1.margin = false :=
    not_negative_of_nonneg hledger.margin (by linarith)
  refine ⟨w1, ?_, hzero, hphase, hunbroken1, ?_, ?_⟩
  · rw [afterBirth_chain]
    simp [afterMismatch, searchLens, scanLens]
  · rw [htargetOnly]
    simpa using hmargin
  · rw [hprediction]
    simp [afterBirth_right, afterMismatch_right]

/-- **The fallback move inequality when a caught-up first-round watch mispredicts**, on a packed
run whose origin is reached from boot: `phase = 4` gives four verified semiperiods, the run
invariant the minimal period, and `RestartLower.move_of_prediction_break` the inequality. -/
theorem move_of_watch_mispredict {raw : List (Fin 2)} (hraw : raw ≠ []) {c₀ : Control}
    {r₀ : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    (hboot : CloseoutCheckW.PackedFromBoot centre place entry q first raw ⟨c₀, r₀⟩)
    {k : ℕ} {c : Control} {s : GalilVM} {vq : SearchVM} {w1 : GalilScaffoldChainWatch.State}
    (hrun : CloseoutCheckW.StepsIMWC centre place entry q first raw k ⟨c₀,r₀⟩ ⟨c, s⟩)
    (hm : c.mode = .scan) (hr : c.replaying = false) (hcan : canRight s.right)
    (hmis : read (left s.left) ≠ read (right s.right))
    (hsearch : searchEffect (PofC centre place entry raw) false s vq)
    (hchainAt : chainAt false (decide (vq.search.mode = .found)) (vq.dp.config.tapes 11)
      ((PofC centre place entry raw).centre s) ((PofC centre place entry raw).place s)
      s.center s.radius s.chain (.watch w1))
    (hfirstRound : s.periodOnly = false) (hzero : zero w1.lag = true)
    (hphase : w1.machine.control.phase = 4)
    (hprediction : GalilScaffoldChainConsume.symbol w1.machine.control.period.focus
      ≠ read (right s.right)) :
    let s1 := afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
      (afterMismatch s ⟨left s.left,right s.right,ChainVM.watch w1⟩ vq)
    let ℓ := (value s.length).toNat
    let radius := chosenRadius
      ((GalilScaffoldPlace.stream (PalPeg.GalilTickFair.rightPlace s1)).take (ℓ+1))
    ℓ / 2 ≤ 4 * (ℓ / 2 + 1 - radius) := by
  obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hraw
  have hinvariant := minimalAcrossRestart_packed centre place entry q first hP hI
    (lowerAt_of_packedFromBoot centre place entry q first hP hI hboot) hrun
  have hminimal : ScanMinimal (MovePayload (a :: rest) s) (a :: rest) s := by
    simpa [ModeMinimal, hm] using hinvariant.minimal
  have hwin : WindowRunPack (a :: rest) c s :=
    (PalPeg.CloseoutCheckW.ipackMW_last_of_stepsIMWC centre place entry q first hrun).win hP
  obtain ⟨-, -, rad, hscan, hlen⟩ :=
    PalPeg.CanonicalFallbackInput.counters centre place entry q first hI hrun hm hr
  obtain ⟨hstep, -, hfourDistance, hdistance, -⟩ :=
    caughtUp_facts centre place entry q first hwin hm hmis hsearch hchainAt hfirstRound hzero
      hphase
  obtain ⟨R, hR, hright⟩ := hwin.radiusScan hm
  have hrad : rad = R := by
    have h1 : position s.right = position s.center + rad := hscan.rightPos
    have h2 : position s.right = position s.center + R := hright
    omega
  subst hrad
  have hfour : 4 * periodLength w1 ≤ rad := by
    rw [hdistance, hR.2] at hfourDistance
    exact_mod_cast hfourDistance
  obtain ⟨w0, hsource, hinternal⟩ := watch_source_of_step hstep hphase
  exact move_of_prediction_break (vq := vq) (z := ChainVM.watch w1) hwin hm hscan hcan hlen
    hminimal hsource hinternal hzero hfour hprediction

#print axioms move_of_watch_mispredict
#print axioms shiftGuard_of_caughtUp

open PalPeg.ChainClock in
/-- **The fallback move inequality below four semiperiods of a first-round chain**, on a packed
run whose origin is reached from boot: the payload of the chain state `x` (its own semiperiod
`chainPeriod x`) together with `LowerAt` excludes every shorter semiperiod at the current
radius, and the radius is below four semiperiods. -/
theorem move_of_bounded_chain {raw : List (Fin 2)} (hraw : raw ≠ []) {c₀ : Control}
    {r₀ : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    (hboot : CloseoutCheckW.PackedFromBoot centre place entry q first raw ⟨c₀, r₀⟩)
    {k : ℕ} {c : Control} {s : GalilVM} {vq : SearchVM} {z x : ChainVM}
    (hrun : CloseoutCheckW.StepsIMWC centre place entry q first raw k ⟨c₀,r₀⟩ ⟨c, s⟩)
    (hm : c.mode = .scan) (hr : c.replaying = false) (hcan : canRight s.right)
    (hfirstRound : s.periodOnly = false) (hx : x ≠ .idle)
    (hsem : Sem (MovePayload raw s) raw (position s.center) x)
    (hshort : value s.radius < 4 * chainPeriod x) :
    let s1 := afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
      (afterMismatch s ⟨left s.left,right s.right,z⟩ vq)
    let ℓ := (value s.length).toNat
    let radius := chosenRadius
      ((GalilScaffoldPlace.stream (PalPeg.GalilTickFair.rightPlace s1)).take (ℓ+1))
    ℓ / 2 ≤ 4 * (ℓ / 2 + 1 - radius) := by
  obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hraw
  have hinvariant := minimalAcrossRestart_packed centre place entry q first hP hI
    (lowerAt_of_packedFromBoot centre place entry q first hP hI hboot) hrun
  have hwin : WindowRunPack (a :: rest) c s :=
    (PalPeg.CloseoutCheckW.ipackMW_last_of_stepsIMWC centre place entry q first hrun).win hP
  obtain ⟨-, -, rad, hscan, hlen⟩ :=
    PalPeg.CanonicalFallbackInput.counters centre place entry q first hI hrun hm hr
  obtain ⟨R, hR, hright⟩ := hwin.radiusScan hm
  have hrad : rad = R := by
    have h1 : position s.right = position s.center + rad := hscan.rightPos
    have h2 : position s.right = position s.center + R := hright
    omega
  subst hrad
  obtain ⟨H, hperiod, -, hpayload⟩ := period_of_semWith hsem hx
  have hmove : MoveAbove (a :: rest) (position s.center) (value s.lower).toNat H := hpayload
  have hbound : rad ≤ 4 * H := by
    rw [← hperiod, hR.2] at hshort
    omega
  have hlow := no_lower_period_at_scan hinvariant.lowerAt hm (Or.inr hfirstRound) hscan hR
  exact PalPeg.CanonicalFallbackInput.move_of_activeBound (c := c) (vq := vq) (z := z)
    hscan hcan hlen (scan_radius_lt hscan)
    (fun g hg0 hgh hfour => by
      by_cases hle : g ≤ (value s.lower).toNat
      · exact hlow g hg0 hle
      · exact hmove rad (scan_radius_lt hscan) hscan.palindrome g (by omega) hgh hfour)
    hbound rfl

open PalPeg.ChainClock in
/-- **The fallback move inequality while a first-round chain still has work to do** (copying,
walking back, or catching up) after the chain tick of the comparison: the chain clock keeps the
radius below four semiperiods. -/
theorem move_of_working_chain {raw : List (Fin 2)} (hraw : raw ≠ []) {c₀ : Control}
    {r₀ : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    (hboot : CloseoutCheckW.PackedFromBoot centre place entry q first raw ⟨c₀, r₀⟩)
    {k : ℕ} {c : Control} {s : GalilVM} {vq : SearchVM} {z : ChainVM}
    (hrun : CloseoutCheckW.StepsIMWC centre place entry q first raw k ⟨c₀,r₀⟩ ⟨c, s⟩)
    (hm : c.mode = .scan) (hr : c.replaying = false) (hcan : canRight s.right)
    (hchainAt : chainAt false (decide (vq.search.mode = .found)) (vq.dp.config.tapes 11)
      ((PofC centre place entry raw).centre s) ((PofC centre place entry raw).place s)
      s.center s.radius s.chain z)
    (hnotIdle : s.chain ≠ .idle) (hfirstRound : s.periodOnly = false)
    (hwork : 0 < chainWork z) :
    let s1 := afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
      (afterMismatch s ⟨left s.left,right s.right,z⟩ vq)
    let ℓ := (value s.length).toNat
    let radius := chosenRadius
      ((GalilScaffoldPlace.stream (PalPeg.GalilTickFair.rightPlace s1)).take (ℓ+1))
    ℓ / 2 ≤ 4 * (ℓ / 2 + 1 - radius) := by
  obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hraw
  have hinvariant := minimalAcrossRestart_packed centre place entry q first hP hI
    (lowerAt_of_packedFromBoot centre place entry q first hP hI hboot) hrun
  have hwin : WindowRunPack (a :: rest) c s :=
    (PalPeg.CloseoutCheckW.ipackMW_last_of_stepsIMWC centre place entry q first hrun).win hP
  obtain ⟨-, hfield⟩ :=
    PalPeg.SearchStageRun.stageAt_field_packed centre place entry q first hP hI hrun
  have hledgerSource := ledgerAt_packed centre place entry q first hP hI hrun (Or.inl hm)
  simp only [shiftDebt, hm, show (Mode.scan = Mode.shift) = False from by simp,
    if_false] at hledgerSource
  have hclockPos : (1 : ℤ) ≤ (c.clock : ℤ) := by exact_mod_cast hfield.clock_pos
  have hclockLe : (c.clock : ℤ) ≤ 2048 := by exact_mod_cast hfield.clock_le
  have hclock := clock_chainAt (E := 2048 - (c.clock : ℤ)) (E' := 2048 - (c.clock : ℤ))
    (R' := value s.radius) hchainAt hwin.coupled.block hledgerSource
    (watch_unbroken_of_window hwin) rfl (fun hw => hinvariant.clock hm hfirstRound hw)
    (fun hidle _ => absurd hidle hnotIdle) (by simp) ⟨by omega, by omega, by omega⟩ (by simp)
    hwork
  have hzNotIdle : z ≠ .idle := by
    intro hz
    rw [hz] at hwork
    simp [chainWork] at hwork
  have hsem : Sem (MovePayload (a :: rest) s) (a :: rest) (position s.center) z :=
    sem_chainAt (hinvariant.firstRound hm (Or.inr hfirstRound))
      (fun hidle _ => absurd hidle hnotIdle) hchainAt
  exact move_of_bounded_chain centre place entry q first hraw hP hI hboot hrun hm hr hcan
    hfirstRound hzNotIdle hsem (by omega)

#print axioms move_of_working_chain

open PalPeg.ChainClock in
/-- **The fallback move inequality when the chain of the mismatching state itself still has work
to do** — in particular when its chain tick breaks a watch that has not caught up: the clock at
the state keeps the radius below four semiperiods, whatever the chain tick does. -/
theorem move_of_working_source {raw : List (Fin 2)} (hraw : raw ≠ []) {c₀ : Control}
    {r₀ : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    (hboot : CloseoutCheckW.PackedFromBoot centre place entry q first raw ⟨c₀, r₀⟩)
    {k : ℕ} {c : Control} {s : GalilVM} {vq : SearchVM} {z : ChainVM}
    (hrun : CloseoutCheckW.StepsIMWC centre place entry q first raw k ⟨c₀,r₀⟩ ⟨c, s⟩)
    (hm : c.mode = .scan) (hr : c.replaying = false) (hcan : canRight s.right)
    (hfirstRound : s.periodOnly = false) (hwork : 0 < chainWork s.chain) :
    let s1 := afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
      (afterMismatch s ⟨left s.left,right s.right,z⟩ vq)
    let ℓ := (value s.length).toNat
    let radius := chosenRadius
      ((GalilScaffoldPlace.stream (PalPeg.GalilTickFair.rightPlace s1)).take (ℓ+1))
    ℓ / 2 ≤ 4 * (ℓ / 2 + 1 - radius) := by
  obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hraw
  have hinvariant := minimalAcrossRestart_packed centre place entry q first hP hI
    (lowerAt_of_packedFromBoot centre place entry q first hP hI hboot) hrun
  obtain ⟨-, hfield⟩ :=
    PalPeg.SearchStageRun.stageAt_field_packed centre place entry q first hP hI hrun
  have hclockLe : (c.clock : ℤ) ≤ 2048 := by exact_mod_cast hfield.clock_le
  have hclock : chainWork s.chain + (2048 - (c.clock : ℤ))
      ≤ 2047 * (4 * chainPeriod s.chain - value s.radius) :=
    hinvariant.clock hm hfirstRound hwork
  have hnotIdle : s.chain ≠ .idle := by
    intro hidle
    rw [hidle] at hwork
    simp [chainWork] at hwork
  exact move_of_bounded_chain centre place entry q first hraw hP hI hboot hrun hm hr hcan
    hfirstRound hnotIdle (hinvariant.firstRound hm (Or.inr hfirstRound)) (by omega)

#print axioms move_of_working_source

open PalPeg.ChainClock in
/-- What the chain tick of a mismatching comparison does to a non-idle chain: the chain was
already broken, or it had work left (a watch that breaks before it has caught up is one), or it
has work left afterwards, or it ends as a caught-up watch. -/
theorem chainTick_cases {raw : List (Fin 2)} {c₀ : Control} {r₀ : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    {k : ℕ} {c : Control} {s : GalilVM} {found : Bool} {answer : GalilScaffoldTape.Tape}
    {z : ChainVM}
    (hrun : CloseoutCheckW.StepsIMWC centre place entry q first raw k ⟨c₀,r₀⟩ ⟨c, s⟩)
    (hm : c.mode = .scan)
    (hchainAt : chainAt false found answer ((PofC centre place entry raw).centre s)
      ((PofC centre place entry raw).place s) s.center s.radius s.chain z)
    (hnotIdle : s.chain ≠ .idle) :
    (∃ w, s.chain = .broken w) ∨ 0 < chainWork s.chain ∨ 0 < chainWork z ∨
      ∃ w1, z = .watch w1 ∧ zero w1.lag = true := by
  have hwin : WindowRunPack raw c s :=
    (PalPeg.CloseoutCheckW.ipackMW_last_of_stepsIMWC centre place entry q first hrun).win hP
  obtain ⟨R, hR, -⟩ := hwin.radiusScan hm
  have hledgerSource := ledgerAt_packed centre place entry q first hP hI hrun (Or.inl hm)
  simp only [shiftDebt, hm, show (Mode.scan = Mode.shift) = False from by simp,
    if_false] at hledgerSource
  have hledger : ChainLedger 0 z :=
    chainLedger_chainAt hchainAt ⟨hR.1, by rw [hR.2]; exact Int.natCast_nonneg _⟩
      hwin.coupled.block hledgerSource
  cases z with
  | idle => exact absurd (idle_of_chainAt hchainAt) hnotIdle
  | broken wb =>
    have hstep : ChainStep s.chain (.broken wb) := by
      rcases hchainAt with ⟨-, y, hstep, hzy⟩ | ⟨-, -, hidle⟩ | ⟨-, -, hborn⟩
      · rw [if_neg (by simp)] at hzy
        rw [hzy]
        exact hstep
      · cases hidle
      · rw [if_neg (by simp)] at hborn
        unfold chainStart at hborn
        cases hborn
    have hunbrokenSource := watch_unbroken_of_window hwin
    generalize hx : s.chain = x at hstep hledgerSource hunbrokenSource
    generalize hy : ChainVM.broken wb = y at hstep
    cases hstep with
    | brokenIdle w0 => exact Or.inl ⟨w0, rfl⟩
    | watchBreak w0 hb =>
      right; left
      obtain ⟨hcanonical, -⟩ := (hledgerSource (hunbrokenSource w0 rfl)).lag
      have hpositive := (positive_iff _ hcanonical).mp hb.1
      simpa [chainWork] using hpositive
    | idle => cases hy
    | copyBit => cases hy
    | copyEnd => cases hy
    | backStep => cases hy
    | backDone => cases hy
    | watchStep => cases hy
  | copy t h p v lag margin ver =>
    right; right; left
    have hlag : 0 ≤ value lag := hledger.2.2.2
    simp only [chainWork]
    have hcells : 1 ≤ PalPeg.GalilShiftH.cells v := by unfold PalPeg.GalilShiftH.cells; omega
    omega
  | back v h lag margin ver =>
    right; right; left
    have hlag : 0 ≤ value lag := hledger.2.2.2
    simp only [chainWork]
    omega
  | watch w1 =>
    have hstep := chainStep_of_chainAt_watch hchainAt
    have hunbroken1 := unbroken_of_step hstep (watch_unbroken_of_window hwin)
    obtain ⟨hcanonical, hnonneg⟩ := (hledger hunbroken1).lag
    cases hzero : zero w1.lag with
    | true => exact Or.inr (Or.inr (Or.inr ⟨w1, rfl, hzero⟩))
    | false =>
      right; right; left
      have hne : value w1.lag ≠ 0 := fun hvalue => by
        have := (zero_iff _ hcanonical).mpr hvalue
        rw [hzero] at this
        cases this
      simp only [chainWork]
      omega

end PalPeg.RestartLowerRun
