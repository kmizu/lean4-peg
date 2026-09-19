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

/-- The payload of a chain born while the search runs above the lower bound of `s`: the DP
excludes the semiperiods strictly between that bound and the least candidate, and the candidate's
first palindrome is the block palindrome one semiperiod left of the centre. -/
def MovePayload (raw : List (Fin 2)) (s : GalilVM) : ℕ → ℕ → Prop :=
  fun C H => MoveAbove raw C (value s.lower).toNat H ∧
    Manacher.PalAt (encoded raw) (C - H) H

/-- The birth payload from the excluded lower bound. -/
theorem birthMinimal_of_lowerAt {raw : List (Fin 2)} {c₀ : Control} {r₀ : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    {k : ℕ} {y : State GalilVM}
    (hrun : CloseoutCheckW.StepsIMWC centre place entry q first raw k ⟨c₀,r₀⟩ y)
    (hm : y.ctl.mode = .scan) (hlowerAt : LowerAt raw y.ctl y.vm) :
    BirthMinimal centre place entry (MovePayload raw y.vm) raw y.vm := by
  intro a vq hidle he hf
  obtain ⟨H, hcopy, hfuture, hmove, hblockPal⟩ :=
    PalPeg.CanonicalSearchHistory.birthMinimals_packed centre place entry q first hP hI hrun hm
      hidle he hf (fun lower hlowerEq => by
        obtain ⟨base, -, hbaseLower, hexcluded⟩ := hlowerAt hm (Or.inl hidle) lower (by
          rw [← searchEffect_lower_eq he, hlowerEq, ofNat_value])
        exact hexcluded.toLowerExcluded hbaseLower)
  rw [searchEffect_lower_eq he] at hmove
  exact ⟨H, hcopy, hfuture, hmove, hblockPal⟩

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

/-! ## The window of a first-round chain, anchored at the current centre -/

/-- One chain tick keeps the birth-anchored window; a birth anchors it at the verifier handed to
`chainStart`, the centre head. -/
theorem windowInv_chainAt {raw : List (Fin 2)} {a found : Bool} {answer : GalilScaffoldTape.Tape}
    {cc : Fin 3} {walker : GalilScaffoldPlace.Place} {ver : PlaceHead} {radius : Counter}
    {x z : ChainVM} {C R' : ℕ}
    (hchainAt : chainAt a found answer cc walker ver radius x z)
    (hver : PalPeg.GalilReplayGeneral2.VerAt raw C ver) (hradius : RadiusRep radius R')
    (hsource : x ≠ .idle → WindowInv raw C (C + R') cc x) :
    WindowInv raw C (C + R' + if a then 1 else 0) cc z := by
  rcases hchainAt with ⟨hne, y, hstep, hzy⟩ | ⟨-, -, hz⟩ | ⟨-, -, hz⟩
  · have hy := windowInv_step (hsource hne) hstep
    cases a with
    | false =>
      rw [if_neg (by simp)] at hzy
      subst hzy
      simpa using hy
    | true =>
      rw [if_pos rfl] at hzy
      simpa using windowInv_matched hy hzy
  · rw [hz]
    trivial
  · have hstart : WindowInv raw C (C + R') cc (chainStart answer cc walker ver radius) :=
      windowInv_start answer walker hver hradius
    cases a with
    | false =>
      rw [if_neg (by simp)] at hz
      rw [hz]
      simpa using hstart
    | true =>
      rw [if_pos rfl] at hz
      simpa using windowInv_matched hstart hz

/-- In the first round of a chain its window is anchored at the current centre. -/
def FirstRoundWindow (raw : List (Fin 2)) (c : Control) (s : GalilVM) : Prop :=
  c.mode = .scan → s.periodOnly = false → s.chain ≠ .idle →
    ∃ cc, (encoded raw)[position s.center]? = some cc ∧
      WindowInv raw (position s.center) (position s.right) cc s.chain

/-- One tick keeps `FirstRoundWindow`. -/
theorem firstRoundWindow_tick {Extra : ℕ → ℕ → GalilScaffoldChainWatch.State → Prop}
    {raw : List (Fin 2)} {x y : State GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (ht : Tick (galilFrameS (PofC centre place entry raw) q first) 2048 x y)
    (hsource : FirstRoundWindow raw x.ctl x.vm)
    (hwinX : WindowRunPack raw x.ctl x.vm)
    (hstage : BrokenStage Extra x.ctl x.vm)
    (hfront : PalPeg.GalilFrontMono.FrontPack x.ctl x.vm)
    (hrightRep : x.ctl.mode = .scan → GalilScaffoldInputTrace.Represents x.vm.right.head raw)
    (hrightPresent : x.ctl.mode = .scan → x.vm.right.head.focus ≠ none) :
    FirstRoundWindow raw y.ctl y.vm := by
  have hchainTick : ∀ {c : Control} {s t : GalilVM} {a found : Bool} {vq : SearchVM},
      x = ⟨c, s⟩ → c.mode = .scan →
      chainAt a found (vq.dp.config.tapes 11) ((PofC centre place entry raw).centre s)
        ((PofC centre place entry raw).place s) s.center s.radius s.chain t.chain →
      t.center = s.center →
      position t.right = position s.right + (if a then 1 else 0) →
      t.periodOnly = (if chainBorn found s.chain then false else s.periodOnly) →
      t.periodOnly = false →
      ∃ cc, (encoded raw)[position t.center]? = some cc ∧
        WindowInv raw (position t.center) (position t.right) cc t.chain := by
    intro c s t a found vq hx hm hch hcenter hright honly htargetFalse
    subst hx
    have hcen := hwinX.centreRep (Or.inl hm)
    have hsymbol := PalPeg.WindowTick.centreSymbol_of_decodes hP hcen
    obtain ⟨R', hR', hrightPos⟩ := hwinX.radiusScan hm
    have hwindow := windowInv_chainAt (raw := raw) (C := position s.center) hch
      ⟨hcen.1, hcen.2, rfl⟩ hR' (fun hne => by
        have hsourceOnly : s.periodOnly = false := by
          unfold chainBorn at honly
          rw [isIdle_false_of_ne hne] at honly
          rw [honly] at htargetFalse
          simpa using htargetFalse
        obtain ⟨cc', hcc', hinv⟩ := hsource hm hsourceOnly hne
        have hccEq : cc' = (PofC centre place entry raw).centre s := by
          rw [hsymbol] at hcc'
          exact (Option.some.inj hcc').symm
        rw [← hccEq]
        have hright' : position s.right = position s.center + R' := hrightPos
        rw [← hright']
        exact hinv)
    refine ⟨(PofC centre place entry raw).centre s, by rw [hcenter]; exact hsymbol, ?_⟩
    have hright' : position s.right = position s.center + R' := hrightPos
    rw [hcenter, hright, hright']
    exact hwindow
  cases ht with
  | init c s t hm hi =>
    obtain ⟨_,_,_,_,_,_,_,_,_,hch,_⟩ := hi
    intro _ _ hne
    exact absurd hch hne
  | scan_wait c s t hm hav hb =>
    obtain ⟨-, hright, hch, hcenter, honly, -⟩ :=
      backgroundS_fields (PofC centre place entry raw) q first hb
    intro _ hfalse _
    exact hchainTick (a := false) rfl hm hch hcenter (by rw [hright]; simp) honly hfalse
  | scan_count c s t hm hav hc hb =>
    obtain ⟨-, hright, hch, hcenter, honly, -⟩ :=
      backgroundS_fields (PofC centre place entry raw) q first hb
    intro _ hfalse _
    exact hchainTick (a := false) rfl hm hch hcenter (by rw [hright]; simp) honly hfalse
  | scan_match c s s' t o hm hav hc hcmp hmt hpl ho =>
    have hcmp' : compareFound (PofC centre place entry raw) q first s s' := hcmp
    obtain ⟨vs, vq, a, -, hvr, hiff, -, hch, heq⟩ := hcmp'
    have ha : a = true := by
      cases a with
      | true => rfl
      | false =>
        exfalso
        have hm' : read s'.left = read s'.right := hmt
        rw [heq, afterBirth_left, afterBirth_right] at hm'
        exact absurd (hiff.2 hm') (by simp)
    subst ha
    obtain ⟨-, hr', hchain', hcenter', -⟩ := PalPeg.WindowTick.compare_target_heads heq
    have hchain : t.chain = s'.chain := by rw [hpl]; split <;> rfl
    have hcenter : t.center = s'.center := by rw [hpl]; split <;> rfl
    have htright : t.right = s'.right := by rw [hpl]; split <;> rfl
    have honly : t.periodOnly
        = if chainBorn (decide (vq.search.mode = .found)) s.chain then false
          else s.periodOnly := by
      have htarget : t.periodOnly = s'.periodOnly := by rw [hpl]; split <;> rfl
      rw [htarget, heq, afterBirth_periodOnly]
      rfl
    have hcan : canRight s.right := by
      rcases hav with hrp | ha
      · exact PalPeg.CloseoutReplayCanRight.canRight_of_frontPack hfront hrp
      · exact ha
    have hl0 : 0 < s.right.head.left.length :=
      (represented_position _ raw (hrightRep hm) (hrightPresent hm)).1
    have hright : position t.right = position s.right + 1 := by
      rw [htright, hr', hvr, right_position _ hcan hl0]
    intro _ hfalse _
    exact hchainTick (a := true) (vq := vq) rfl hm (by rw [hchain, hchain']; exact hch)
      (hcenter.trans hcenter') (by rw [hright]; simp) honly hfalse
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
    intro _ hfalse _
    have hsourceFalse : s.periodOnly = false := hfalse
    rw [honly] at hsourceFalse
    cases hsourceFalse
  | replayStart c s t o hm hr ho ho' =>
    obtain ⟨_,_,_,_,_,_,_,_,_,hch,_,_,_⟩ := hr
    intro _ _ hne
    exact absurd hch hne
  | restart c s t hm hr =>
    obtain ⟨_,_,_,_,_,rfl⟩ := hr
    intro _ _ hne
    exact absurd rfl hne
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

/-! ## The first round ends at the restart guard -/

/-- In the first round of a chain, a broken chain of a scan state is at the restart guard. -/
def FirstRoundGuard (c : Control) (s : GalilVM) : Prop :=
  c.mode = .scan → s.periodOnly = false → ∀ w, s.chain = .broken w → restartGuardVM s

/-- A lag-zero break after four verified semiperiods lands at the restart guard. -/
theorem restartGuard_of_lateBreak {w1 w' : GalilScaffoldChainWatch.State}
    (hledger : WatchLedger 0 w1) (hbreak : BreakStep w1 w')
    (hfour : 4 * (periodLength w1 : ℤ) ≤ value w1.machine.control.distance) :
    negative w'.margin = false ∧ positive w'.machine.control.last = true ∧
      zero w'.lag = true := by
  obtain ⟨hzero, -, a, hsymbol, hread, rfl⟩ := hbreak
  have hcontrol : (GalilScaffoldChainVerifier.consume w1.machine).control
      = {w1.machine.control with broken := true} :=
    GalilScaffoldChainConsume.mismatch w1.machine.control a _ hsymbol hread
  have hbalance := hledger.balance
  simp only [GalilScaffoldChainWatch.balance] at hbalance
  have hlagZero := PalPeg.GalilChainCoupling.value_zero_of_zero hzero
  obtain ⟨-, hlastHigh⟩ := hledger.last_bounds hfour
  have hperiod : 1 ≤ periodLength w1 := by
    obtain ⟨hsize, hforward, hbackward, -⟩ := hledger.marks
    cases hfw : w1.machine.control.forward with
    | true => have := (hforward hfw).1; omega
    | false => have := (hbackward hfw).1; omega
  have hperiodInt : (1 : ℤ) ≤ (periodLength w1 : ℤ) := by exact_mod_cast hperiod
  refine ⟨not_negative_of_nonneg (inc_canonical _ hledger.margin) ?_, ?_, hzero⟩
  · show 0 ≤ value (inc w1.margin)
    rw [inc_value]
    linarith
  · show positive (GalilScaffoldChainVerifier.consume w1.machine).control.last = true
    rw [hcontrol]
    exact (positive_iff _ hledger.marks.canonical.2.2).mpr (by linarith)

/-- A chain that is not broken and whose watch does not break at a positive lag does not step
into a broken chain. -/
theorem not_step_to_broken {x : ChainVM} {w : GalilScaffoldChainWatch.State}
    (hstep : ChainStep x (.broken w)) (hnotBroken : ∀ w0, x ≠ .broken w0)
    (hnoWatchBreak : ∀ w0, x = .watch w0 → ¬ WatchBreak w0) : False := by
  generalize hy : ChainVM.broken w = y at hstep
  cases hstep with
  | brokenIdle w0 => exact hnotBroken w0 rfl
  | watchBreak w0 hb => exact hnoWatchBreak w0 rfl hb
  | idle => cases hy
  | copyBit => cases hy
  | copyEnd => cases hy
  | backStep => cases hy
  | backDone => cases hy
  | watchStep => cases hy

/-- **A first-round watch predicts the text.**  The watch of a first-round scan state, before or
after its chain step, predicts the letter right of its verifier, as long as that place carries
the letter of its mirror image in the centre and lies within four semiperiods of the centre. -/
theorem firstRound_watch_predicts {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hwin : WindowRunPack raw c s) (hm : c.mode = .scan) (hfirstRound : s.periodOnly = false)
    (hwindowAt : FirstRoundWindow raw c s)
    (htextAt : BlockTextAt centre place entry raw c s)
    (hsemAt : FirstRoundSem raw c s) (hcertAt : CertAt raw c s)
    {w : GalilScaffoldChainWatch.State}
    (hreach : s.chain = .watch w ∨ ChainStep s.chain (.watch w))
    (hcanRight : canRight w.machine.verifier)
    (hroom : position w.machine.verifier + 1 ≤ 2 * position s.center)
    (hmirror : (encoded raw)[position s.center
        - (position w.machine.verifier + 1 - position s.center)]?
      = (encoded raw)[position w.machine.verifier + 1]?)
    (hfour : position w.machine.verifier + 2 ≤ position s.center + 4 * periodLength w) :
    read (right w.machine.verifier)
      = GalilScaffoldChainConsume.symbol w.machine.control.period.focus := by
  have hne : s.chain ≠ .idle := by
    intro hidle
    rcases hreach with h | h
    · rw [hidle] at h; cases h
    · rw [hidle] at h; cases h
  obtain ⟨cc, hcc, hwindow0⟩ := hwindowAt hm hfirstRound hne
  obtain ⟨cc', htext0⟩ := htextAt hm hfirstRound
  have hsem0 := hsemAt hm (Or.inr hfirstRound)
  have hcert0 := hcertAt.1 hm
  have hall : WindowInv raw (position s.center) (position s.right) cc (.watch w) ∧
      PalPeg.ChainBlockText.BlockText
        (GalilScaffoldPlace.stream ((PofC centre place entry raw).place s)) cc' (.watch w) ∧
      Sem (MovePayload raw s) raw (position s.center) (.watch w) ∧
      SemWith (LeftPeriod raw (position s.center)) (.watch w) := by
    rcases hreach with heq | hstep
    · rw [heq] at hwindow0 htext0 hsem0 hcert0
      exact ⟨hwindow0, htext0, hsem0, hcert0⟩
    · exact ⟨windowInv_step hwindow0 hstep,
        PalPeg.ChainBlockText.blockText_step htext0 hwin.coupled.block hstep,
        sem_step hsem0 hstep, sem_step hcert0 hstep⟩
  obtain ⟨hwindowW, htextW, hsemW, hcertW⟩ := hall
  have hpayload : MovePayload raw s (position s.center) (periodLength w) :=
    watch_moveMinimal hsemW
  obtain ⟨H, hH, hleftH⟩ := PalPeg.ChainClock.period_of_semWith hcertW (by simp)
  have hcells := PalPeg.GalilShiftH.periodLength_succ_eq_cells w
  change periodLength w + 1 = PalPeg.GalilShiftH.cellsOf (.watch w) at hcells
  have hHeq : H = periodLength w := by
    have hHvalue : (H : ℤ) = (PalPeg.GalilShiftH.cellsOf (.watch w) : ℤ) - 1 := hH
    omega
  rw [hHeq] at hleftH
  have hcen := hwin.centreRep (Or.inl hm)
  obtain ⟨a, ys, rs, q', hdec, hraw⟩ := represents_decompose s.center raw hcen.1 hcen.2
  have hplace : (PofC centre place entry raw).place s = ⟨a :: ys, s.center.gap⟩ :=
    (hP.1 s a ys rs q' s.center.gap hdec).2
  have hstreamLength := stream_length_of_place a ys rs q' hdec
  rw [hplace] at htextW
  have hprediction := PalPeg.ChainBlockText.prediction_eq_text_of_window hwindowW htextW hcc
    (fun i hi => by
      have hindex := stream_index a ys rs q' s.center.gap i hi
      rw [hstreamLength, ← hraw] at hindex
      exact hindex)
    hstreamLength hpayload.2 hleftH hroom hmirror hfour
  obtain ⟨b, xs, -, -, hcore⟩ := hwindowW
  have hrep := hcore.2.1
  have hpresent := hcore.2.2.1
  have hleft0 : 0 < w.machine.verifier.head.left.length :=
    (represented_position _ raw hrep hpresent).1
  rw [represented_read _ raw (right_word _ raw hrep hcanRight)
    (right_present _ raw hrep hpresent hcanRight), right_position _ hcanRight hleft0]
  exact hprediction.symm

#print axioms firstRound_watch_predicts

open PalPeg.ChainClock in
/-- **No first-round watch breaks at a positive lag**: the chain clock keeps the scan radius
below four semiperiods while the watch is behind, so the place it verifies is predicted. -/
theorem no_watchBreak_firstRound {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hwin : WindowRunPack raw c s) (hm : c.mode = .scan) (hfirstRound : s.periodOnly = false)
    (hwindowAt : FirstRoundWindow raw c s)
    (htextAt : BlockTextAt centre place entry raw c s)
    (hsemAt : FirstRoundSem raw c s) (hcertAt : CertAt raw c s)
    (hclockAt : ClockAt c s) (hclockLe : c.clock ≤ 2048)
    {R : ℕ} (hscan : ScanInvariant raw (position s.center) R s.left s.right)
    (hradius : RadiusRep s.radius R)
    {w0 : GalilScaffoldChainWatch.State} (hchain : s.chain = .watch w0) :
    ¬ WatchBreak w0 := by
  rintro ⟨hpositive, hcanRight, a, hsymbol, hread⟩
  have hne : s.chain ≠ .idle := by rw [hchain]; simp
  obtain ⟨cc, -, hwindow0⟩ := hwindowAt hm hfirstRound hne
  rw [hchain] at hwindow0
  obtain ⟨b, xs, ⟨hlagNeg, hlagPosition⟩, -, hcore⟩ := hwindow0
  obtain ⟨-, -, -, -, pre, -, -, hindex⟩ := hcore
  have hlagLength : 1 ≤ w0.lag.pos.length := by
    rcases hw : w0.lag with ⟨pos, neg⟩
    rw [hw] at hpositive
    cases pos with
    | nil => simp [positive] at hpositive
    | cons _ _ => simp
  have hlagValue : value w0.lag = (w0.lag.pos.length : ℤ) := by
    unfold value
    rw [hlagNeg]
    simp
  have hwork : 0 < chainWork (.watch w0) := by
    show 0 < value w0.lag
    rw [hlagValue]
    exact_mod_cast hlagLength
  have hclock := hclockAt hm hfirstRound (by rw [hchain]; exact hwork)
  rw [hchain] at hclock
  have hperiodValue : chainPeriod (.watch w0) = (periodLength w0 : ℤ) := by
    have hcells := PalPeg.GalilShiftH.periodLength_succ_eq_cells w0
    change periodLength w0 + 1 = PalPeg.GalilShiftH.cellsOf (.watch w0) at hcells
    show (PalPeg.GalilShiftH.cellsOf (.watch w0) : ℤ) - 1 = _
    omega
  have hradiusValue : value s.radius = (R : ℤ) := hradius.2
  have hclockLeInt : (c.clock : ℤ) ≤ 2048 := by exact_mod_cast hclockLe
  have hRlt : R < 4 * periodLength w0 := by
    rw [hperiodValue, hradiusValue] at hclock
    have hgap : (0 : ℤ) < 4 * (periodLength w0 : ℤ) - (R : ℤ) := by linarith
    omega
  have hrightPos := hscan.rightPos
  have hpal := hscan.palindrome
  have hmirror := hpal.2.2 (position w0.machine.verifier + 1 - position s.center) (by omega)
  have hprediction := firstRound_watch_predicts centre place entry hP hwin hm hfirstRound
    hwindowAt htextAt hsemAt hcertAt (Or.inl hchain) hcanRight (by have := hpal.1; omega)
    (by rw [hmirror]; congr 1; omega) (by omega)
  exact hread (hprediction.trans hsymbol)

#print axioms no_watchBreak_firstRound

/-- **A first-round lag-zero break comes after four verified semiperiods**: before that the
matched letter is predicted (`firstRound_watch_predicts`), and the boundary `4h − 1` is the
left certificate's (`distance_ne_boundary`). -/
theorem lateBreak_firstRound {raw : List (Fin 2)} {c : Control} {s s' : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hwin : WindowRunPack raw c s) (hm : c.mode = .scan) (hfirstRound : s.periodOnly = false)
    (hwindowAt : FirstRoundWindow raw c s)
    (htextAt : BlockTextAt centre place entry raw c s)
    (hsemAt : FirstRoundSem raw c s) (hcertAt : CertAt raw c s)
    {R : ℕ} (hscan : ScanInvariant raw (position s.center) R s.left s.right)
    (hradius : RadiusRep s.radius R) (hrightCan : canRight s.right)
    (hcmp : (galilFrameS (PofC centre place entry raw) q first).compare s s')
    (hmt : (galilFrameS (PofC centre place entry raw) q first).matched s')
    {w1 w' : GalilScaffoldChainWatch.State}
    (hstep : ChainStep s.chain (.watch w1)) (hbreak : BreakStep w1 w')
    (hboundary : value w1.machine.control.distance ≠ 4 * (periodLength w1 : ℤ) - 1) :
    4 * (periodLength w1 : ℤ) ≤ value w1.machine.control.distance := by
  by_contra hshort
  have hne : s.chain ≠ .idle := by
    intro hidle
    rw [hidle] at hstep
    cases hstep
  have hunbroken1 := unbroken_of_step hstep (watch_unbroken_of_window hwin)
  have hsum1 : PalPeg.GalilChainCoupling.SumRel (.watch w1) (value s.radius) :=
    (PalPeg.GalilChainCoupling.step_inv hstep (F := True) trivial (O := fun _ => True)
      hwin.coupled.block hwin.coupled.sum (fun _ _ _ => Or.inr trivial)).1
  have hdistance := hsum1 hunbroken1
  rw [PalPeg.GalilChainCoupling.value_zero_of_zero hbreak.1, add_zero, hradius.2] at hdistance
  obtain ⟨cc, -, hwindow0⟩ := hwindowAt hm hfirstRound hne
  obtain ⟨b, xs, ⟨-, hlagPosition⟩, -, -⟩ := windowInv_step hwindow0 hstep
  have hlagEmpty : w1.lag.pos = [] := by
    have hz := hbreak.1
    rcases hw : w1.lag with ⟨pos, neg⟩
    rw [hw] at hz
    simp only [zero, Bool.and_eq_true, List.isEmpty_iff] at hz
    exact hz.1
  rw [hlagEmpty] at hlagPosition
  have hverifier : position w1.machine.verifier = position s.right := by
    simpa using hlagPosition
  have hRC := scan_radius_lt hscan
  have hrightPos := hscan.rightPos
  have hmatched := PalPeg.RestartBoundary.matched_text centre place entry q first hscan hcmp hmt
    hrightCan
  obtain ⟨-, hcanRight, a, hsymbol, hread, -⟩ := hbreak
  have hprediction := firstRound_watch_predicts centre place entry hP hwin hm hfirstRound
    hwindowAt htextAt hsemAt hcertAt (Or.inr hstep) hcanRight (by omega)
    (by rw [hverifier, ← hmatched]; congr 1; omega) (by omega)
  exact hread (hprediction.trans hsymbol)

#print axioms lateBreak_firstRound

/-- One tick of the canonical schedule keeps `FirstRoundGuard`.  A broken chain is born by a
positive-lag break of a background step (`hnoWatchBreak` excludes it in the first round) or by a
lag-zero break of a matched comparison (`hlateBreak` puts it after four semiperiods, where the
ledger gives the restart guard); a broken chain without the guard does not exist at the source. -/
theorem firstRoundGuard_tick {Extra : ℕ → ℕ → GalilScaffoldChainWatch.State → Prop}
    {raw : List (Fin 2)} {x y : State GalilVM}
    (ht : Tick (galilFrameS (PofC centre place entry raw) q first) 2048 x y)
    (hcanon : PalPeg.GalilTickFair.Canonical entry 2048 x y)
    (hsource : FirstRoundGuard x.ctl x.vm)
    (hstage : BrokenStage Extra x.ctl x.vm) (hledger : LedgerAt x.ctl x.vm)
    (hwinX : WindowRunPack raw x.ctl x.vm)
    (hfront : PalPeg.GalilFrontMono.FrontPack x.ctl x.vm)
    (hnoWatchBreak : ∀ (c : Control) (s : GalilVM) w0, x = ⟨c, s⟩ → c.mode = Mode.scan →
      s.periodOnly = false → s.chain = .watch w0 → ¬ WatchBreak w0)
    (hlateBreak : ∀ (c : Control) (s s' : GalilVM) w1 w', x = ⟨c, s⟩ → c.mode = Mode.scan →
      s.periodOnly = false → canRight s.right →
      (galilFrameS (PofC centre place entry raw) q first).compare s s' →
      (galilFrameS (PofC centre place entry raw) q first).matched s' →
      ChainStep s.chain (.watch w1) → BreakStep w1 w' →
      4 * (periodLength w1 : ℤ) ≤ value w1.machine.control.distance) :
    FirstRoundGuard y.ctl y.vm := by
  by_cases hguard : x.ctl.mode = Mode.scan ∧ restartGuardVM x.vm
  · obtain ⟨hctl, hrestart⟩ := hcanon.restartFirst hguard.1 hguard.2
    obtain ⟨w0, -, -, -, -, hteq⟩ := hrestart
    intro _ _ w hw
    rw [hteq] at hw
    cases hw
  have hsourceOnly : ∀ {s t : GalilVM} {found : Bool},
      t.periodOnly = (if chainBorn found s.chain then false else s.periodOnly) →
      t.periodOnly = false → s.chain ≠ .idle → s.periodOnly = false := by
    intro s t found honly htargetFalse hne
    unfold chainBorn at honly
    rw [isIdle_false_of_ne hne] at honly
    rw [honly] at htargetFalse
    simpa using htargetFalse
  have hstepBroken : ∀ {c : Control} {s : GalilVM} {w : GalilScaffoldChainWatch.State},
      x = ⟨c, s⟩ → c.mode = .scan → (s.chain ≠ .idle → s.periodOnly = false) →
      ChainStep s.chain (.broken w) → False := by
    intro c s w hx hm honlySource hstep
    subst hx
    exact not_step_to_broken hstep
      (fun w0 hw0 => hguard ⟨hm, hsource hm (honlySource (by rw [hw0]; simp)) w0 hw0⟩)
      (fun w0 hw0 => hnoWatchBreak c s w0 rfl hm (honlySource (by rw [hw0]; simp)) hw0)
  have hbackground : ∀ {c : Control} {s t : GalilVM} {w : GalilScaffoldChainWatch.State},
      x = ⟨c, s⟩ → c.mode = .scan →
      (galilFrameS (PofC centre place entry raw) q first).background s t →
      t.periodOnly = false → t.chain = .broken w → False := by
    intro c s t w hx hm hb hfalse hw
    obtain ⟨-, -, hch, -, honly, -⟩ :=
      backgroundS_fields (PofC centre place entry raw) q first hb
    rcases hch with ⟨-, y0, hstep, hzy⟩ | ⟨-, -, hz⟩ | ⟨-, -, hz⟩
    · rw [if_neg (by simp)] at hzy
      rw [hzy] at hw
      subst hw
      exact hstepBroken hx hm (hsourceOnly honly hfalse) hstep
    · rw [hz] at hw; cases hw
    · rw [if_neg (by simp)] at hz
      rw [hz] at hw
      cases hw
  cases ht with
  | init c s t hm hi =>
    obtain ⟨_,_,_,_,_,_,_,_,_,hch,_⟩ := hi
    intro _ _ w hw
    rw [hch] at hw
    cases hw
  | scan_wait c s t hm hav hb =>
    intro _ hfalse w hw
    exact (hbackground rfl hm hb hfalse hw).elim
  | scan_count c s t hm hav hc hb =>
    intro _ hfalse w hw
    exact (hbackground rfl hm hb hfalse hw).elim
  | scan_match c s s' t o hm hav hc hcmp hmt hpl ho =>
    have hcmp' : compareFound (PofC centre place entry raw) q first s s' := hcmp
    obtain ⟨vs, vq, a, -, -, hiff, -, hch, heq⟩ := hcmp'
    have ha : a = true := by
      cases a with
      | true => rfl
      | false =>
        exfalso
        have hm' : read s'.left = read s'.right := hmt
        rw [heq, afterBirth_left, afterBirth_right] at hm'
        exact absurd (hiff.2 hm') (by simp)
    subst ha
    have hchain' : s'.chain = vs.chain := by
      rw [heq, afterBirth_chain]; rfl
    have hchain : t.chain = s'.chain := by rw [hpl]; split <;> rfl
    have honly : t.periodOnly
        = if chainBorn (decide (vq.search.mode = .found)) s.chain then false
          else s.periodOnly := by
      have htarget : t.periodOnly = s'.periodOnly := by rw [hpl]; split <;> rfl
      rw [htarget, heq, afterBirth_periodOnly]
      rfl
    have hrightCan : canRight s.right := by
      rcases hav with hrp | hcan
      · exact PalPeg.CloseoutReplayCanRight.canRight_of_frontPack hfront hrp
      · exact hcan
    intro _ hfalse w hw
    have htchain : t.chain = .broken w := hw
    rw [hchain, hchain'] at hw
    rcases hch with ⟨-, y0, hstep, hzy⟩ | ⟨-, -, hz⟩ | ⟨-, -, hz⟩
    · rw [if_pos rfl] at hzy
      rw [hw] at hzy
      generalize hyz : ChainVM.broken w = z at hzy
      cases hzy with
      | breaks w1 w' hbreak =>
        cases hyz
        have hne : s.chain ≠ .idle := by
          intro hidle
          rw [hidle] at hstep
          cases hstep
        have hledger0 := hledger (Or.inl hm)
        simp only [shiftDebt, hm, show (Mode.scan = Mode.shift) = False from by simp,
          if_false] at hledger0
        have hledger1 : WatchLedger 0 w1 :=
          chainLedger_step hstep hwinX.coupled.block hledger0
            (unbroken_of_step hstep (watch_unbroken_of_window hwinX))
        exact ⟨w, htchain, restartGuard_of_lateBreak hledger1 hbreak
          (hlateBreak c s s' w1 w rfl hm (hsourceOnly honly hfalse hne) hrightCan hcmp hmt
            hstep hbreak)⟩
      | brokenMatched w0 =>
        cases hyz
        exact (hstepBroken rfl hm (hsourceOnly honly hfalse) hstep).elim
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
    intro _ hfalse _ _
    have hsourceFalse : s.periodOnly = false := hfalse
    rw [honly] at hsourceFalse
    cases hsourceFalse
  | replayStart c s t o hm hr ho ho' =>
    obtain ⟨_,_,_,_,_,_,_,_,_,hch,_,_,_⟩ := hr
    intro _ _ w hw
    rw [hch] at hw
    cases hw
  | restart c s t hm hr =>
    obtain ⟨_,_,_,_,_,rfl⟩ := hr
    intro _ _ w hw
    cases hw
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

#print axioms firstRoundGuard_tick

/-! ## After a shift the minimality is the thresholded one -/

/-- In a round after a shift (`periodOnly = true`) the chain carries no birth payload: its
minimality is the thresholded `TailMinimal` (`ScanMinimal` with the empty payload, whose `Sem`
side is `False` for a watch). -/
def TailRound (raw : List (Fin 2)) (c : Control) (s : GalilVM) : Prop :=
  c.mode = .scan → s.periodOnly = true → ScanMinimal (fun _ _ => False) raw s

/-- One tick keeps `TailRound`.  A scan tick that keeps `periodOnly = true` has no birth, so an
idle chain stays idle and a live chain ticks under the payload-free `modeMinimal_tick_packed`
(its birth hook is vacuous); the end of a shift hands over `ShiftMinimal`. -/
theorem tailRound_tick {Move : ℕ → ℕ → Prop} {raw : List (Fin 2)} {x y : State GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (ht : Tick (galilFrameS (PofC centre place entry raw) q first) 2048 x y)
    (hsource : TailRound raw x.ctl x.vm)
    (hminimal : ModeMinimal Move raw x.ctl x.vm)
    (hpackX : PalPeg.CloseoutPackW.IPackMW centre place entry q first raw x)
    (hpackY : PalPeg.CloseoutPackW.IPackMW centre place entry q first raw y)
    (haux : PalPeg.CloseoutPackRun2.AuxPack x.ctl x.vm) :
    TailRound raw y.ctl y.vm := by
  intro hmodeY honlyY
  have hgeneric : ModeMinimal (fun _ _ => False) raw x.ctl x.vm → x.vm.chain ≠ .idle →
      ScanMinimal (fun _ _ => False) raw y.vm := by
    intro hx hne
    have hy := modeMinimal_tick_packed centre place entry q first hP ht hx hpackX hpackY haux
      (fun _ a vq hidle => absurd hidle hne)
    simpa [ModeMinimal, hmodeY] using hy
  have hscanTick : ∀ {c : Control} {s t : GalilVM} {a found : Bool}
      {answer : GalilScaffoldTape.Tape} {cc : Fin 3} {walker : GalilScaffoldPlace.Place}
      {ver : PlaceHead} {radius : Counter} {z : ChainVM},
      c.mode = .scan → TailRound raw c s →
      chainAt a found answer cc walker ver radius s.chain z → t.chain = z →
      t.periodOnly = (if chainBorn found s.chain then false else s.periodOnly) →
      t.periodOnly = true →
      (ModeMinimal (fun _ _ => False) raw c s → s.chain ≠ .idle →
        ScanMinimal (fun _ _ => False) raw t) →
      ScanMinimal (fun _ _ => False) raw t := by
    intro c s t a found answer cc walker ver radius z hm hround hch htz honly htrue hgen
    by_cases hidle : s.chain = .idle
    · rcases hch with ⟨hne, -⟩ | ⟨-, -, hz⟩ | ⟨-, hfound, -⟩
      · exact absurd hidle hne
      · simp [ScanMinimal, htz, hz]
      · rw [hidle, hfound] at honly
        rw [honly] at htrue
        simp [chainBorn, ChainVM.isIdle] at htrue
    · have hsourceOnly : s.periodOnly = true := by
        unfold chainBorn at honly
        rw [isIdle_false_of_ne hidle] at honly
        rw [honly] at htrue
        simpa using htrue
      exact hgen (by simpa [ModeMinimal, hm] using hround hm hsourceOnly) hidle
  cases ht with
  | init c s t hm hi =>
    obtain ⟨_,_,_,_,_,_,_,_,_,hch,_⟩ := hi
    simp [ScanMinimal, hch]
  | scan_wait c s t hm hav hb =>
    obtain ⟨-, -, hch, -, honly, -⟩ :=
      backgroundS_fields (PofC centre place entry raw) q first hb
    exact hscanTick hm hsource hch rfl honly honlyY hgeneric
  | scan_count c s t hm hav hc hb =>
    obtain ⟨-, -, hch, -, honly, -⟩ :=
      backgroundS_fields (PofC centre place entry raw) q first hb
    exact hscanTick hm hsource hch rfl honly honlyY hgeneric
  | scan_match c s s' t o hm hav hc hcmp hmt hpl ho =>
    have hcmp' : compareFound (PofC centre place entry raw) q first s s' := hcmp
    obtain ⟨vs, vq, a, -, -, -, -, hch, heq⟩ := hcmp'
    have hchain' : s'.chain = vs.chain := by
      rw [heq, afterBirth_chain]; cases a <;> rfl
    have hchain : t.chain = s'.chain := by rw [hpl]; split <;> rfl
    have honly : t.periodOnly
        = if chainBorn (decide (vq.search.mode = .found)) s.chain then false
          else s.periodOnly := by
      have htarget : t.periodOnly = s'.periodOnly := by rw [hpl]; split <;> rfl
      rw [htarget, heq, afterBirth_periodOnly]
      cases a <;> rfl
    exact hscanTick hm hsource hch (hchain.trans hchain') honly honlyY hgeneric
  | scan_shift c s s' t hm hav hc hcmp hmt hr hg hb =>
    simp at hmodeY
  | scan_fallback c s s' t hm hav hc hcmp hmt hg hr hb =>
    simp at hmodeY
  | shift_one c s t hm hp hso =>
    simp [hm] at hmodeY
  | shift_done c s o hm hp ho =>
    have hshift : ShiftMinimal raw s := by simpa [ModeMinimal, hm] using hminimal
    obtain ⟨w, _, _, hchainWatch, _⟩ := hshift
    exact hgeneric (by simpa [ModeMinimal, hm] using hminimal)
      (by rw [hchainWatch]; simp)
  | replayStart c s t o hm hr ho ho' =>
    obtain ⟨_,_,_,_,_,_,_,_,_,hch,_,_,_⟩ := hr
    simp [ScanMinimal, hch]
  | restart c s t hm hr =>
    obtain ⟨_,_,_,_,_,rfl⟩ := hr
    simp [ScanMinimal]
  | copy_one _ _ _ hm _ _ | copy_done _ _ _ hm _ _
  | home_start _ _ _ hm _ _ | home_step _ _ _ hm _ _
  | fpp_slice _ _ _ hm _ | fpp_done _ _ _ hm _
  | markEnd_found _ _ _ hm _ _ | markEnd_step _ _ _ hm _ _
  | choose_select _ _ _ hm _ _ _ | choose_step _ _ _ hm _ _
  | rewind_done _ _ _ hm _ _ | rewind_one _ _ _ hm _ _ _
  | rewind_pair _ _ _ hm _ _ _ =>
    first
      | (simp [hm] at hmodeY)
      | (simp at hmodeY)

#print axioms tailRound_tick

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

/-! ## The continuation of a round after a shift -/

/-- A chain tick into a watch, from a chain without birth payload, starts at a watch of the same
semiperiod (a copy or back chain carries its birth payload). -/
theorem watch_source_of_tailRound {raw : List (Fin 2)} {s : GalilVM} {a : Bool}
    {w' : GalilScaffoldChainWatch.State}
    (hminimal : ScanMinimal (fun _ _ => False) raw s) (hblock : BlockInv s.chain)
    (htick : ChainTick a s.chain (.watch w')) :
    ∃ w0, s.chain = .watch w0 ∧ periodLength w' = periodLength w0 := by
  cases hs : s.chain with
  | idle =>
    rw [hs] at htick
    obtain ⟨z, hz, ha⟩ := htick
    cases hz
    cases a with
    | false => simp at ha
    | true => cases ha
  | broken wb =>
    rw [hs] at htick
    obtain ⟨z, hz, ha⟩ := htick
    cases hz
    cases a with
    | false => simp at ha
    | true => cases ha
  | copy t h p v lag margin ver =>
    simp only [ScanMinimal, hs] at hminimal
    obtain ⟨H, n, -, -, -, hfalse⟩ := hminimal
    exact hfalse.elim
  | back v h lag margin ver =>
    simp only [ScanMinimal, hs] at hminimal
    obtain ⟨-, H, -, -, -, hfalse⟩ := hminimal
    exact hfalse.elim
  | watch w0 =>
    rw [hs] at htick hblock
    refine ⟨w0, rfl, ?_⟩
    have hcells := (PalPeg.GalilShiftH.settled_tick htick (by trivial) hblock).2
    have hp := PalPeg.GalilShiftH.periodLength_succ_eq_cells w0
    have hp' := PalPeg.GalilShiftH.periodLength_succ_eq_cells w'
    change periodLength w0 + 1 = PalPeg.GalilShiftH.cellsOf (.watch w0) at hp
    change periodLength w' + 1 = PalPeg.GalilShiftH.cellsOf (.watch w') at hp'
    change PalPeg.GalilShiftH.cellsOf (.watch w') = PalPeg.GalilShiftH.cellsOf (.watch w0)
      at hcells
    omega

/-- A caught-up watch in phase `4` stays caught up and in phase `4` under a chain tick that ends
in a watch: at lag zero the background step is idle and a matched place is consumed at once
(Scala `matched()`), and phase `4` is absorbing. -/
theorem caughtUp_watch_tick {a : Bool} {w0 w' : GalilScaffoldChainWatch.State}
    (htick : ChainTick a (.watch w0) (.watch w')) (hzero : zero w0.lag = true)
    (hphase : w0.machine.control.phase = 4) :
    zero w'.lag = true ∧ w'.machine.control.phase = 4 := by
  obtain ⟨y, hstep, hya⟩ := htick
  generalize hx : ChainVM.watch w0 = x at hstep
  cases hstep with
  | watchStep w w1 hinternal =>
    cases hx
    have hw1 : w1 = w0 := by
      cases hinternal with
      | idle _ => rfl
      | take hp _ =>
        rw [not_zero_of_positive hp] at hzero
        cases hzero
    subst hw1
    cases a with
    | false =>
      rw [if_neg (by simp)] at hya
      cases hya
      exact ⟨hzero, hphase⟩
    | true =>
      rw [if_pos rfl] at hya
      generalize hsourceChain : ChainVM.watch w1 = u at hya
      generalize htargetChain : ChainVM.watch w' = v at hya
      cases hya with
      | watch w2 w3 houter =>
        cases hsourceChain
        cases htargetChain
        cases houter with
        | queued hnonzero =>
          rw [hzero] at hnonzero
          cases hnonzero
        | immediate _ _ =>
          exact ⟨hzero, consume_phase_four _ _ hphase⟩
      | idle => cases hsourceChain
      | copy => cases hsourceChain
      | back => cases hsourceChain
      | breaks => cases htargetChain
      | brokenMatched => cases hsourceChain
  | watchBreak w hb =>
    cases hx
    cases a with
    | false =>
      rw [if_neg (by simp)] at hya
      cases hya
    | true =>
      rw [if_pos rfl] at hya
      cases hya
  | idle => cases hx
  | brokenIdle => cases hx
  | copyBit => cases hx
  | copyEnd => cases hx
  | backStep => cases hx
  | backDone => cases hx

/-- The left end `Lb` of the periodic stretch a shift started from: the text has period `2h` from
`Lb` to `E`, and the period breaks one place further left (what the left head reads there, `none`
on the sentinel, is not the letter two semiperiods to its right). -/
def LeftEnd (raw : List (Fin 2)) (h Lb E : ℕ) : Prop :=
  1 ≤ Lb ∧ Lb ≤ E ∧ PeriodOn (encoded raw) (2 * h) Lb E ∧
    signedRead (encoded raw) ((Lb : ℤ) - 1) ≠ (encoded raw)[Lb - 1 + 2 * h]?

/-- The continuation of a round after a shift (Scala `ScaffoldChain` `beginShift` / `shiftOne` /
`matched` / `checkPair`).  The countdown starts at `0` with `h` unit moves to go, each unit move
adds `2`, each matched place takes `1`; so it is at most two semiperiods, and the place
`Lb = C − R − cycle + 1` does not move during the round.  From `Lb` to the centre (to the landing
centre during the shift) the text has the chain's period: `Lb` is the left end of the scan
palindrome the shift started from. -/
def Continuation (raw : List (Fin 2)) (c : Control) (s : GalilVM) : Prop :=
  ∀ w, s.chain = .watch w →
    (c.mode = .scan → s.periodOnly = true →
      (zero w.lag = true ∧ w.machine.control.phase = 4) ∧
      Canonical s.cycle ∧ value s.cycle ≤ 2 * (periodLength w : ℤ) ∧
      ∃ Lb : ℕ, (Lb : ℤ) + value s.radius + value s.cycle = (position s.center : ℤ) + 1 ∧
        LeftEnd raw (periodLength w) Lb (position s.center)) ∧
    (c.mode = .shift →
      (zero w.lag = true ∧ w.machine.control.phase = 4) ∧
      Canonical s.cycle ∧ value s.cycle + 2 * value s.remaining ≤ 2 * (periodLength w : ℤ) ∧
      ∃ Lb rem : ℕ, s.remaining = ofNat rem ∧
        (Lb : ℤ) + value s.radius + value s.cycle = (position s.center : ℤ) + 1 ∧
        LeftEnd raw (periodLength w) Lb (position s.center + rem))

/-- One tick keeps `Continuation`.  `hstart` supplies the period at the start of a shift: the
scan palindrome the shift leaves has the chain's period. -/
theorem continuation_tick {raw : List (Fin 2)} {x y : State GalilVM}
    (ht : Tick (galilFrameS (PofC centre place entry raw) q first) 2048 x y)
    (hsource : Continuation raw x.ctl x.vm) (hround : TailRound raw x.ctl x.vm)
    (hwinX : WindowRunPack raw x.ctl x.vm)
    (hcopy : x.ctl.mode = .shift → CopyIdle x.vm)
    (hstart : ∀ (c : Control) (s s' : GalilVM) (w : GalilScaffoldChainWatch.State),
      x = ⟨c, s⟩ → c.mode = .scan →
      (galilFrameS (PofC centre place entry raw) q first).compare s s' →
      ¬ (galilFrameS (PofC centre place entry raw) q first).matched s' →
      shiftGuardVM s' → s'.chain = .watch w →
      ∃ Lb : ℕ, (Lb : ℤ) + value s.radius = (position s.center : ℤ) ∧
        LeftEnd raw (periodLength w) Lb (position s.center + periodLength w)) :
    Continuation raw y.ctl y.vm := by
  have hscanTick : ∀ {c : Control} {s t : GalilVM} {a found : Bool}
      {answer : GalilScaffoldTape.Tape} {cc : Fin 3} {walker : GalilScaffoldPlace.Place}
      {ver : PlaceHead} {radius : Counter} {w' : GalilScaffoldChainWatch.State},
      c.mode = .scan → Continuation raw c s → TailRound raw c s → BlockInv s.chain →
      chainAt a found answer cc walker ver radius s.chain (.watch w') →
      t.periodOnly = (if chainBorn found s.chain then false else s.periodOnly) →
      t.periodOnly = true → t.center = s.center →
      (s.chain ≠ .idle → s.periodOnly = true → Canonical s.cycle →
        Canonical t.cycle ∧ value t.cycle ≤ value s.cycle ∧
        value t.radius + value t.cycle = value s.radius + value s.cycle) →
      (zero w'.lag = true ∧ w'.machine.control.phase = 4) ∧
      Canonical t.cycle ∧ value t.cycle ≤ 2 * (periodLength w' : ℤ) ∧
      ∃ Lb : ℕ, (Lb : ℤ) + value t.radius + value t.cycle = (position t.center : ℤ) + 1 ∧
        LeftEnd raw (periodLength w') Lb (position t.center) := by
    intro c s t a found answer cc walker ver radius w' hm hbound htail hblock hch honly htrue
      hcenter hcycle
    rcases hch with ⟨hne, htick⟩ | ⟨-, -, hz⟩ | ⟨hidle, hfound, -⟩
    · have hsourceOnly : s.periodOnly = true := by
        unfold chainBorn at honly
        rw [isIdle_false_of_ne hne] at honly
        rw [honly] at htrue
        simpa using htrue
      obtain ⟨w0, hw0, hlength⟩ :=
        watch_source_of_tailRound (htail hm hsourceOnly) hblock htick
      obtain ⟨⟨hzero, hphase⟩, hcanonical, hsourceBound, Lb, hLb, hperiod⟩ :=
        (hbound w0 hw0).1 hm hsourceOnly
      obtain ⟨hcanonical', hstep, hsum⟩ := hcycle hne hsourceOnly hcanonical
      have hcaught := caughtUp_watch_tick (by rw [hw0] at htick; exact htick) hzero hphase
      rw [hlength, hcenter]
      exact ⟨hcaught, hcanonical', by linarith, Lb, by linarith, hperiod⟩
    · cases hz
    · rw [hidle, hfound] at honly
      rw [honly] at htrue
      simp [chainBorn, ChainVM.isIdle] at htrue
  cases ht with
  | init c s t hm hi =>
    obtain ⟨_,_,_,_,_,_,_,_,_,hch,_⟩ := hi
    intro w hw
    rw [hch] at hw
    cases hw
  | scan_wait c s t hm hav hb =>
    obtain ⟨-, -, hch, hcenter, honly, hradius, -, hcyc, -⟩ :=
      backgroundS_fields (PofC centre place entry raw) q first hb
    intro w' hw
    rw [hw] at hch
    refine ⟨fun _ htrue => ?_, fun hmode => by simp [hm] at hmode⟩
    exact hscanTick hm hsource hround hwinX.coupled.block hch honly htrue hcenter
      (fun hne _ hcanonical => by
        have hkeep : t.cycle = s.cycle := by
          rw [hcyc]
          unfold chainBorn
          rw [isIdle_false_of_ne hne]
          simp
        rw [hkeep, hradius]
        exact ⟨hcanonical, le_rfl, rfl⟩)
  | scan_count c s t hm hav hc hb =>
    obtain ⟨-, -, hch, hcenter, honly, hradius, -, hcyc, -⟩ :=
      backgroundS_fields (PofC centre place entry raw) q first hb
    intro w' hw
    rw [hw] at hch
    refine ⟨fun _ htrue => ?_, fun hmode => by simp [hm] at hmode⟩
    exact hscanTick hm hsource hround hwinX.coupled.block hch honly htrue hcenter
      (fun hne _ hcanonical => by
        have hkeep : t.cycle = s.cycle := by
          rw [hcyc]
          unfold chainBorn
          rw [isIdle_false_of_ne hne]
          simp
        rw [hkeep, hradius]
        exact ⟨hcanonical, le_rfl, rfl⟩)
  | scan_match c s s' t o hm hav hc hcmp hmt hpl ho =>
    obtain ⟨-, -, -, hmatched, -⟩ :=
      PalPeg.CloseoutPackRun40.compare'_inv (onLetterVM raw) leftFirstVM centre place entry
        q first hwinX.coupled hm hcmp
    obtain ⟨hradius', hcyc, -, -⟩ := hmatched hmt
    have hcmp' : compareFound (PofC centre place entry raw) q first s s' := hcmp
    obtain ⟨vs, vq, a, -, -, -, -, hch, heq⟩ := hcmp'
    have hchain' : s'.chain = vs.chain := by
      rw [heq, afterBirth_chain]; cases a <;> rfl
    have hchain : t.chain = s'.chain := by rw [hpl]; split <;> rfl
    have htcycle : t.cycle = s'.cycle := by rw [hpl]; split <;> rfl
    have htradius : t.radius = s'.radius := by rw [hpl]; split <;> rfl
    have htcenter : t.center = s'.center := by rw [hpl]; split <;> rfl
    have hscenter : s'.center = s.center := (PalPeg.WindowTick.compare_target_heads heq).2.2.2.1
    have honly : t.periodOnly
        = if chainBorn (decide (vq.search.mode = .found)) s.chain then false
          else s.periodOnly := by
      have htarget : t.periodOnly = s'.periodOnly := by rw [hpl]; split <;> rfl
      rw [htarget, heq, afterBirth_periodOnly]
      cases a <;> rfl
    intro w' hw
    rw [hchain, hchain'] at hw
    rw [hw] at hch
    refine ⟨fun _ htrue => ?_, fun hmode => by simp [hm] at hmode⟩
    exact hscanTick hm hsource hround hwinX.coupled.block hch honly htrue
      (htcenter.trans hscenter)
      (fun hne hsourceOnly hcanonical => by
        rw [htcycle, htradius, hcyc hne, hradius']
        unfold cycleAfter
        rw [hsourceOnly, if_pos rfl, dec_value, inc_value]
        exact ⟨dec_canonical _ hcanonical, by omega, by ring⟩)
  | scan_shift c s s' t hm hav hc hcmp hmt hr hg hb =>
    obtain ⟨hblock', -, -, -, hmismatched⟩ :=
      PalPeg.CloseoutPackRun40.compare'_inv (onLetterVM raw) leftFirstVM centre place entry
        q first hwinX.coupled hm hcmp
    obtain ⟨hradius', -⟩ := hmismatched hmt
    have hcmp' : compareFound (PofC centre place entry raw) q first s s' := hcmp
    obtain ⟨vs, vq, a, -, -, -, -, -, heq⟩ := hcmp'
    have hscenter : s'.center = s.center := (PalPeg.WindowTick.compare_target_heads heq).2.2.2.1
    obtain ⟨w, hs0, hteq⟩ : beginShiftVM' s' t := hb
    obtain ⟨Lb, hLb, hperiod⟩ := hstart c s s' w rfl hm hcmp hmt hg hs0
    have hguardWatch : zero w.lag = true ∧ w.machine.control.phase = 4 := by
      obtain ⟨wg, hwg, hzeroG, hphaseG, -⟩ := hg
      rw [hs0] at hwg
      cases hwg
      exact ⟨hzeroG, hphaseG⟩
    subst hteq
    rw [hs0] at hblock'
    intro w' hw
    cases hw
    refine ⟨fun hmode => by simp at hmode, fun _ => ?_⟩
    have hlength := PalPeg.GalilChainCoupling.periodLength_consume w.machine w.lag w.margin
      w.lag (inc w.margin) hblock'
    have heta : periodLength ⟨w.machine, w.lag, w.margin⟩ = periodLength w := rfl
    have hreset : value reset = 0 := rfl
    show (zero w.lag = true ∧
        (GalilScaffoldChainVerifier.consume w.machine).control.phase = 4) ∧
      Canonical reset ∧ (value reset + 2 * value (ofNat (periodLength w))
        ≤ 2 * ((periodLength ⟨GalilScaffoldChainVerifier.consume w.machine, w.lag,
          inc w.margin⟩ : ℕ) : ℤ)) ∧
      ∃ Lb rem : ℕ, ofNat (periodLength w) = ofNat rem ∧
        (Lb : ℤ) + value s'.radius + value reset = (position s'.center : ℤ) + 1 ∧
        LeftEnd raw (periodLength ⟨GalilScaffoldChainVerifier.consume w.machine, w.lag,
            inc w.margin⟩) Lb (position s'.center + rem)
    rw [hlength, heta, ofNat_value, hreset, hradius', inc_value, hscenter]
    exact ⟨⟨hguardWatch.1, consume_phase_four _ _ hguardWatch.2⟩, Or.inl rfl, by omega, Lb,
      periodLength w, rfl, by linarith, hperiod⟩
  | scan_fallback c s s' t hm hav hc hcmp hmt hg hr hb =>
    obtain ⟨p, hteq, -⟩ : beginFallbackVM' s' t := hb
    subst hteq
    intro w hw
    cases hw
  | shift_one c s t hm hp hso =>
    have hpos : positive s.remaining = true := by
      rcases hp with hp | hp
      · exact hp
      · exact absurd hp (hcopy hm)
    have hcanC := hso.1.1
    obtain ⟨-, -, -, w, hw, hv⟩ := hso.1
    have hteq := hso.2
    rw [hv] at hteq
    have hcen := hwinX.centreRep (Or.inr hm)
    have hl0 : 0 < s.center.head.left.length :=
      (represented_position _ raw hcen.1 hcen.2).1
    have hcenterPos : position (right s.center) = position s.center + 1 :=
      right_position s.center hcanC hl0
    subst hteq
    obtain ⟨hcaught, hcanonical, hsourceBound, Lb, rem, hrem, hLb, hperiod⟩ :=
      (hsource w hw).2 hm
    intro w' hw'
    cases hw'
    refine ⟨fun hmode => by simp [hm] at hmode, fun _ => ?_⟩
    cases rem with
    | zero => rw [hrem] at hpos; exact absurd hpos (by decide)
    | succ rem =>
      show (zero w.lag = true ∧ w.machine.control.phase = 4) ∧
        Canonical (inc (inc s.cycle)) ∧
        (value (inc (inc s.cycle)) + 2 * value (dec s.remaining)
          ≤ 2 * ((periodLength w : ℕ) : ℤ)) ∧
        ∃ Lb rem' : ℕ, dec s.remaining = ofNat rem' ∧
          (Lb : ℤ) + value (dec s.radius) + value (inc (inc s.cycle))
            = (position (right s.center) : ℤ) + 1 ∧
          LeftEnd raw (periodLength w) Lb (position (right s.center) + rem')
      rw [inc_value, inc_value, dec_value, dec_value, hcenterPos]
      refine ⟨hcaught, inc_canonical _ (inc_canonical _ hcanonical), by linarith, Lb, rem,
        by rw [hrem, dec_ofNat_succ], by push_cast; linarith, ?_⟩
      rw [show position s.center + 1 + rem = position s.center + (rem + 1) from by omega]
      exact hperiod
  | shift_done c s o hm hp ho =>
    intro w hw
    refine ⟨fun _ _ => ?_, fun hmode => by simp at hmode⟩
    obtain ⟨hcaught, hcanonical, hsourceBound, Lb, rem, hrem, hLb, hperiod⟩ :=
      (hsource w hw).2 hm
    have hpos : positive s.remaining = false := by
      cases h1 : positive s.remaining
      · rfl
      · exact absurd (Or.inl h1) hp
    have hzero : rem = 0 := by
      cases rem with
      | zero => rfl
      | succ n => rw [hrem] at hpos; simp [positive, ofNat] at hpos
    subst hzero
    rw [hrem, ofNat_value] at hsourceBound
    have hcast : ((0 : ℕ) : ℤ) = 0 := rfl
    exact ⟨hcaught, hcanonical, by linarith, Lb, hLb, by simpa using hperiod⟩
  | replayStart c s t o hm hr ho ho' =>
    obtain ⟨_,_,_,_,_,_,_,_,_,hch,_,_,_⟩ := hr
    intro w hw
    rw [hch] at hw
    cases hw
  | restart c s t hm hr =>
    obtain ⟨_,_,_,_,_,rfl⟩ := hr
    intro w hw
    cases hw
  | copy_one _ _ _ hm _ _ | copy_done _ _ _ hm _ _
  | home_start _ _ _ hm _ _ | home_step _ _ _ hm _ _
  | fpp_slice _ _ _ hm _ | fpp_done _ _ _ hm _
  | markEnd_found _ _ _ hm _ _ | markEnd_step _ _ _ hm _ _
  | choose_select _ _ _ hm _ _ _ | choose_step _ _ _ hm _ _
  | rewind_done _ _ _ hm _ _ | rewind_one _ _ _ hm _ _ _
  | rewind_pair _ _ _ hm _ _ _ =>
    intro w _
    constructor <;> intro hmode <;> first
      | (simp [hm] at hmode)
      | (simp at hmode)

#print axioms continuation_tick

/-- **The period a shift starts from.**  At a mismatching comparison that passes the shift guard,
the scan palindrome has the chain's period (the verified window, `spanPeriod_of_window`); its
radius is at least two semiperiods, four by a fresh ledger or three by `Other'` with the
countdown bound. -/
theorem continuation_start {raw : List (Fin 2)} {c : Control} {s s' : GalilVM}
    {w : GalilScaffoldChainWatch.State}
    (hwin : WindowRunPack raw c s) (hm : c.mode = .scan)
    {R : ℕ} (hscan : ScanInvariant raw (position s.center) R s.left s.right)
    (hradius : RadiusRep s.radius R)
    (hbound : Continuation raw c s)
    (hcmp : (galilFrameS (PofC centre place entry raw) q first).compare s s')
    (hmt : ¬ (galilFrameS (PofC centre place entry raw) q first).matched s')
    (hguard : shiftGuardVM s') (hchain' : s'.chain = .watch w) :
    ∃ Lb : ℕ, (Lb : ℤ) + value s.radius = (position s.center : ℤ) ∧
      LeftEnd raw (periodLength w) Lb (position s.center + periodLength w) := by
  obtain ⟨w', hw', hzero, hphase, hunbroken, -, hpredictionGuard⟩ := hguard
  have hsame : w' = w := by
    rw [hchain'] at hw'
    exact (ChainVM.watch.inj hw').symm
  subst hsame
  obtain ⟨-, -, -, -, hmismatched⟩ :=
    PalPeg.CloseoutPackRun40.compare'_inv (onLetterVM raw) leftFirstVM centre place entry
      q first hwin.coupled hm hcmp
  obtain ⟨-, -, hsum, hwatchOk⟩ := hmismatched hmt
  rw [hchain'] at hsum
  have hdistance := hsum hunbroken
  rw [PalPeg.GalilChainCoupling.value_zero_of_zero hzero, add_zero, hradius.2] at hdistance
  -- the chain tick of the mismatching comparison is one chain step into the watch
  have hcmp' : compareFound (PofC centre place entry raw) q first s s' := hcmp
  obtain ⟨vs, vq, a, hvl, hvr, hiff, -, hch, heq⟩ := hcmp'
  obtain ⟨hl', hr', -⟩ := PalPeg.WindowTick.compare_target_heads heq
  have hvs : vs.chain = .watch w' := by
    rw [← hchain', heq, afterBirth_chain]; cases a <;> rfl
  have ha : a = false := by
    cases a with
    | false => rfl
    | true =>
      exfalso
      apply hmt
      show read s'.left = read s'.right
      rw [heq, afterBirth_left, afterBirth_right]
      exact hiff.1 rfl
  subst ha
  rw [hvs] at hch
  have hstep : ChainStep s.chain (.watch w') := by
    rcases hch with ⟨-, y, hstep, hzy⟩ | ⟨-, -, hidle⟩ | ⟨-, -, hborn⟩
    · rw [if_neg (by simp)] at hzy
      rw [hzy]
      exact hstep
    · cases hidle
    · rw [if_neg (by simp)] at hborn
      unfold chainStart at hborn
      cases hborn
  obtain ⟨w0, hsource, hinternal⟩ := watch_source_of_step hstep hphase
  -- the window of the watch after its internal step
  obtain ⟨cen₀, cc, hcentre, hinv, hk, -, -⟩ := hwin.window
  rw [hsource] at hinv
  obtain ⟨b, xs, hW0⟩ := hinv
  have hW1 := PalPeg.ShiftPalAlongTrace.watchWindow_step hW0 hinternal
  have hlength0 : periodLength w0 = xs.length + 1 :=
    PalPeg.ShiftPalAlongTrace.periodLength_of_coreP hW0.2.2
  have hlength1 : periodLength w' = xs.length + 1 :=
    PalPeg.ShiftPalAlongTrace.periodLength_of_coreP hW1.2.2
  obtain ⟨m, hk⟩ := (hk w0 hsource).2 (by rw [hm]; decide)
  rw [hlength0] at hk
  have hRC := scan_radius_lt hscan
  have hright : position s.right = position s.center + R := hscan.rightPos
  rw [hright] at hW1
  have htwo : 2 * (xs.length + 1) ≤ R := by
    rcases hwatchOk w' hchain' hunbroken with ⟨-, hfresh⟩ | hother
    · have hfour := PalPeg.WindowPack.four_of_freshC hfresh hphase
      have hlengthDef : periodLength w' = w'.machine.control.period.left.length +
          w'.machine.control.period.right.length := rfl
      rw [← hlengthDef, hdistance, hlength1] at hfour
      have hfourNat : 4 * (xs.length + 1) ≤ R := by exact_mod_cast hfour
      omega
    · obtain ⟨honly, -, -, hscanBound⟩ := hother
      have hfive := hscanBound (by rw [hm]; decide)
      obtain ⟨-, -, hcycle, -⟩ := (hbound w0 hsource).1 hm honly
      rw [hradius.2, hlength1] at hfive
      rw [hlength0] at hcycle
      have hthree : 3 * ((xs.length + 1 : ℕ) : ℤ) ≤ (R : ℤ) := by push_cast at hfive hcycle ⊢; linarith
      omega
  have hperiod := spanPeriod_of_window hW1 hzero hcentre hk hscan.palindrome htwo
  have hpal := hscan.palindrome
  refine ⟨position s.center - R, by rw [hradius.2]; omega, by omega, by omega, ?_, ?_⟩
  · rw [hlength1]
    intro i hi1 hi2
    exact hperiod i hi1 (by omega)
  · -- the left head read a letter that is not the predicted one, and the prediction is the
    -- mirror image of the place two semiperiods right of it
    have hsize : cen₀ + 1 + 2 * (xs.length + 1) ≤ position s.center + R + 1 := by
      rw [hk]; nlinarith
    obtain ⟨-, hpredictionText⟩ := PalPeg.RestartBoundary.prediction_eq_text hW1 hzero hsize
    have hleftRead := left_signed_read s.left raw hscan.leftRep hscan.leftPresent
    rw [hscan.leftPos] at hleftRead
    have hmirror := hpal.2.2 (R + 1 - 2 * (xs.length + 1)) (by omega)
    rw [show position s.center - (R + 1 - 2 * (xs.length + 1))
        = position s.center - R - 1 + 2 * (xs.length + 1) from by omega,
      show position s.center + (R + 1 - 2 * (xs.length + 1))
        = position s.center + R + 1 - 2 * (xs.length + 1) from by omega] at hmirror
    rw [hlength1, ← hleftRead, hmirror, ← hpredictionText, hpredictionGuard, hr', hvr]
    intro hreads
    apply hmt
    show read s'.left = read s'.right
    rw [hl', hr', hvl, hvr]
    exact hreads

#print axioms continuation_start

/-- The run invariant: the minimal-period payload, the excluded lower bound of the running
search, and the excluded `last` of a broken chain at a restart-guard state. -/
structure MinimalAcrossRestart (raw : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  minimal : ModeMinimal (MovePayload raw s) raw c s
  lowerAt : LowerAt raw c s
  broken : BrokenStage (LastExcluded raw) c s
  firstRound : FirstRoundSem raw c s
  clock : ClockAt c s
  blockText : BlockTextAt centre place entry raw c s
  window : FirstRoundWindow raw c s
  guard : FirstRoundGuard c s
  tailRound : TailRound raw c s
  continuation : Continuation raw c s

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
        fun _ _ => by rw [hiChain]; exact ⟨0, trivial⟩,
        fun _ _ hne => absurd hiChain hne,
        (fun _ _ w hw => by rw [hiChain] at hw; cases hw),
        (fun _ _ => by simp [ScanMinimal, hiChain]),
        (fun w hw => by rw [hiChain] at hw; cases hw)⟩
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
      have hsourceAt : ∀ (c : Control) (s : GalilVM), g i = ⟨c, s⟩ →
          MinimalAcrossRestart centre place entry raw c s ∧ WindowRunPack raw c s ∧
            CertAt raw c s ∧ c.clock ≤ 2048 ∧
            (c.mode = .scan → ∃ R, ScanInvariant raw (position s.center) R s.left s.right ∧
              RadiusRep s.radius R) := by
        intro c s hx
        have hrunSource : CloseoutCheckW.StepsIMWC centre place entry q first raw i ⟨c₀,r₀⟩
            ⟨c, s⟩ := hx ▸ hprefix i (by omega)
        have hwin : WindowRunPack raw c s :=
          (PalPeg.CloseoutCheckW.ipackMW_last_of_stepsIMWC centre place entry q first
            hrunSource).win hP
        refine ⟨by rw [hx] at hsource; exact hsource, hwin,
          certAt_packed centre place entry q first hP hI hrunSource,
          by have hle := hfieldSource.clock_le; rw [hx] at hle; exact hle, fun hm => ?_⟩
        obtain ⟨rad, hscan⟩ := scanInvariant_packed centre place entry q first hrunSource hm
        obtain ⟨R, hR, hright⟩ := hwin.radiusScan hm
        have hrad : rad = R := by
          have h1 : position s.right = position s.center + rad := hscan.rightPos
          have h2 : position s.right = position s.center + R := hright
          omega
        subst hrad
        exact ⟨rad, hscan, hR⟩
      refine ⟨?_, lowerAt_tick centre place entry q first htick hsource.lowerAt hsource.broken,
        ?_, firstRoundSem_tick centre place entry q first htick hsource.firstRound
          hsource.broken hbirthSource,
        clockAt_tick centre place entry q first htick hsource.clock
          ⟨hfieldSource.clock_pos, hfieldSource.clock_le⟩ hwinX
          (ledgerAt_packed centre place entry q first hP hI (hprefix i (by omega)))
          hsource.broken hstageSource.scan,
        blockTextAt_tick centre place entry q first hP htick hsource.blockText hwinX
          hsource.broken,
        firstRoundWindow_tick centre place entry q first hP htick hsource.window hwinX
          hsource.broken (haux i (by omega)).front
          (fun hm => (scanInvariant_packed centre place entry q first
            (hprefix i (by omega)) hm).choose_spec.rightRep)
          (fun hm => (scanInvariant_packed centre place entry q first
            (hprefix i (by omega)) hm).choose_spec.rightPresent),
        firstRoundGuard_tick centre place entry q first htick (hcan i (by omega)).canonical
          hsource.guard hsource.broken
          (ledgerAt_packed centre place entry q first hP hI (hprefix i (by omega)))
          hwinX (haux i (by omega)).front
          (fun c s w0 hx hm honly hchain => by
            obtain ⟨hinv, hwin, hcert, hclockLe, hgeom⟩ := hsourceAt c s hx
            obtain ⟨R, hscan, hR⟩ := hgeom hm
            exact no_watchBreak_firstRound centre place entry hP hwin hm honly hinv.window
              hinv.blockText hinv.firstRound hcert hinv.clock hclockLe hscan hR hchain)
          (fun c s s' w1 w' hx hm honly hrightCan hcmp hmt hstep hbreak => by
            obtain ⟨hinv, hwin, hcert, -, hgeom⟩ := hsourceAt c s hx
            obtain ⟨R, hscan, hR⟩ := hgeom hm
            exact lateBreak_firstRound centre place entry q first hP hwin hm honly hinv.window
              hinv.blockText hinv.firstRound hcert hscan hR hrightCan hcmp hmt hstep hbreak
              (hboundary i c s s' (hx ▸ hprefix i (by omega)) hm hcmp hmt w1 w' hstep
                hbreak)),
        tailRound_tick centre place entry q first hP htick hsource.tailRound hsource.minimal
          (hpk i (by omega)) (hpk (i+1) (by omega)) (haux i (by omega)),
        continuation_tick centre place entry q first htick hsource.continuation
          hsource.tailRound hwinX
          (fun hm => (haux i (by omega)).copyP (by rw [hm]; decide))
          (fun c s s' w hx hm hcmp hmt hguard hchain' => by
            obtain ⟨hinv, hwin, -, -, hgeom⟩ := hsourceAt c s hx
            obtain ⟨R, hscan, hR⟩ := hgeom hm
            exact continuation_start centre place entry q first hwin hm hscan hR
              hinv.continuation hcmp hmt hguard hchain')⟩
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
      (periodLength w1) := hpayload.1
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
/-- What a mismatching scan state knows about a watch that comes out of its chain tick caught up
and in phase `4`: it was a watch before, it is unbroken, its distance is the scan radius, and it
has verified four semiperiods or is in a round after a shift (`Other'`). -/
theorem caughtUp_watch {raw : List (Fin 2)} {c : Control} {s : GalilVM} {vq : SearchVM}
    {w1 : GalilScaffoldChainWatch.State}
    (hwin : WindowRunPack raw c s) (hm : c.mode = .scan)
    (hmis : read (left s.left) ≠ read (right s.right))
    (hsearch : searchEffect (PofC centre place entry raw) false s vq)
    (hchainAt : chainAt false (decide (vq.search.mode = .found)) (vq.dp.config.tapes 11)
      ((PofC centre place entry raw).centre s) ((PofC centre place entry raw).place s)
      s.center s.radius s.chain (.watch w1))
    (hzero : zero w1.lag = true) (hphase : w1.machine.control.phase = 4) :
    ChainStep s.chain (.watch w1) ∧ w1.machine.control.broken = false ∧
      (4 * (periodLength w1 : ℤ) ≤ value w1.machine.control.distance ∨
        PalPeg.CloseoutPackRun40.Other' s.periodOnly c.mode (value s.radius) (value s.cycle)
          (value s.remaining) (periodLength w1)) ∧
      value w1.machine.control.distance = value s.radius ∧
      (afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
        (afterMismatch s ⟨left s.left,right s.right,ChainVM.watch w1⟩ vq)).periodOnly
          = s.periodOnly ∧
      (s.chain ≠ .idle →
        (afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
          (afterMismatch s ⟨left s.left,right s.right,ChainVM.watch w1⟩ vq)).cycle
            = s.cycle) := by
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
  obtain ⟨-, hcycleKeep, hsum, hwatchOk⟩ := hmismatchInv hmt
  have htargetChain : (afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
      (afterMismatch s ⟨left s.left,right s.right,ChainVM.watch w1⟩ vq)).chain
        = .watch w1 := by
    rw [afterBirth_chain]
    simp [afterMismatch, searchLens, scanLens]
  rw [htargetChain] at hsum
  have hdistance := hsum hunbroken1
  rw [PalPeg.GalilChainCoupling.value_zero_of_zero hzero, add_zero] at hdistance
  refine ⟨hstep, hunbroken1, ?_, hdistance, hperiodOnly hnotIdle, hcycleKeep⟩
  rcases hwatchOk w1 htargetChain hunbroken1 with ⟨-, hfresh⟩ | hother
  · have h4 := PalPeg.WindowPack.four_of_freshC hfresh hphase
    left
    unfold periodLength
    exact h4
  · exact Or.inr hother

include q first in
/-- `caughtUp_watch` in the first round: the watch has verified four semiperiods. -/
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
  obtain ⟨hstep, hunbroken1, hfourOr, hdistance, htargetOnly, -⟩ :=
    caughtUp_watch centre place entry q first hwin hm hmis hsearch hchainAt hzero hphase
  refine ⟨hstep, hunbroken1, ?_, hdistance, htargetOnly.trans hfirstRound⟩
  rcases hfourOr with hfour | hother
  · exact hfour
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
    hsource hinternal hzero (by omega)
    (fun hlength hperiod => scanMinimal_watch_no_short hminimal hsource hright
      (scan_radius_lt hscan) hscan.palindrome (by rw [hlength]; exact hfour) hperiod)
    hprediction

#print axioms move_of_watch_mispredict

/-- A caught-up watch in phase `4` has at least two semiperiods of radius: four by a fresh
ledger, or three by `Other'` (`5h ≤ R + cycle`) with the countdown bound (`cycle ≤ 2h`). -/
theorem two_semiperiods_le {periodOnly : Bool} {mode : Mode}
    {radius cycle remaining distance : ℤ} {h R : ℕ}
    (hfourOr : 4 * (h : ℤ) ≤ distance ∨
      PalPeg.CloseoutPackRun40.Other' periodOnly mode radius cycle remaining h)
    (hdistance : distance = radius) (hradius : radius = (R : ℤ))
    (hmode : mode ≠ Mode.shift) (hcycle : cycle ≤ 2 * (h : ℤ)) : 2 * h ≤ R := by
  rcases hfourOr with hfour | ⟨-, -, -, hscanBound⟩
  · rw [hdistance, hradius] at hfour
    omega
  · have hfive := hscanBound hmode
    rw [hradius] at hfive
    omega

/-- **The fallback move inequality when a caught-up watch mispredicts in a round after a shift.**
The minimality is the thresholded one (`TailRound`), and the radius is at least two semiperiods:
four by a fresh ledger, or three by `Other'` (`5h ≤ R + cycle`) with `CycleBound`
(`cycle ≤ 2h`). -/
theorem move_of_tail_mispredict {raw : List (Fin 2)} (hraw : raw ≠ []) {c₀ : Control}
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
    (honly : s.periodOnly = true) (hzero : zero w1.lag = true)
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
  have hwin : WindowRunPack (a :: rest) c s :=
    (PalPeg.CloseoutCheckW.ipackMW_last_of_stepsIMWC centre place entry q first hrun).win hP
  obtain ⟨-, -, rad, hscan, hlen⟩ :=
    PalPeg.CanonicalFallbackInput.counters centre place entry q first hI hrun hm hr
  obtain ⟨hstep, -, hfourOr, hdistance, -⟩ :=
    caughtUp_watch centre place entry q first hwin hm hmis hsearch hchainAt hzero hphase
  obtain ⟨R, hR, hright⟩ := hwin.radiusScan hm
  have hrad : rad = R := by
    have h1 : position s.right = position s.center + rad := hscan.rightPos
    have h2 : position s.right = position s.center + R := hright
    omega
  subst hrad
  obtain ⟨w0, hsource, hinternal⟩ := watch_source_of_step hstep hphase
  have htail : ScanMinimal (fun _ _ => False) (a :: rest) s := hinvariant.tailRound hm honly
  obtain ⟨w0', hsource', hlength⟩ :=
    watch_source_of_tailRound (a := false) (w' := w1) htail hwin.coupled.block
      ⟨.watch w1, hstep, by simp⟩
  have hsame : w0' = w0 := by
    rw [hsource] at hsource'
    exact (ChainVM.watch.inj hsource').symm
  subst hsame
  have htwo : 2 * periodLength w1 ≤ rad := by
    obtain ⟨-, -, hcycle, -⟩ := (hinvariant.continuation w0' hsource).1 hm honly
    rw [← hlength] at hcycle
    exact two_semiperiods_le hfourOr hdistance hR.2 (by rw [hm]; decide) hcycle
  exact move_of_prediction_break (vq := vq) (z := ChainVM.watch w1) hwin hm hscan hcan hlen
    hsource hinternal hzero htwo
    (fun _ hperiod => by
      simp only [ScanMinimal, hsource] at htail
      obtain ⟨k', hk', hminimal⟩ := htail
      have hk : k' = rad := by omega
      subst hk
      rcases hminimal with hsem | ⟨base, hbase, htailMinimal⟩
      · exact (watch_moveMinimal hsem).elim
      · exact htailMinimal _ hbase (scan_radius_lt hscan) hscan.palindrome hperiod)
    hprediction

#print axioms move_of_tail_mispredict

/-- **A caught-up watch that predicts the place read passes the shift guard after a shift too.**
The guard asks for the countdown at its last cell.  A larger countdown puts the mismatching left
place inside the periodic stretch `[Lb, C]`, where it equals the prediction (period, mirror
image, verified window); a smaller one puts the break `Lb − 1` inside the scan palindrome, which
has the chain's period (`spanPeriod_of_window`).  (Scala `ScaffoldChain.checkPair`.) -/
theorem shiftGuard_of_tail_caughtUp {raw : List (Fin 2)} (hraw : raw ≠ []) {c₀ : Control}
    {r₀ : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    (hboot : CloseoutCheckW.PackedFromBoot centre place entry q first raw ⟨c₀, r₀⟩)
    {k : ℕ} {c : Control} {s : GalilVM} {vq : SearchVM} {w1 : GalilScaffoldChainWatch.State}
    (hrun : CloseoutCheckW.StepsIMWC centre place entry q first raw k ⟨c₀,r₀⟩ ⟨c, s⟩)
    (hm : c.mode = .scan)
    (hmis : read (left s.left) ≠ read (right s.right))
    (hsearch : searchEffect (PofC centre place entry raw) false s vq)
    (hchainAt : chainAt false (decide (vq.search.mode = .found)) (vq.dp.config.tapes 11)
      ((PofC centre place entry raw).centre s) ((PofC centre place entry raw).place s)
      s.center s.radius s.chain (.watch w1))
    (honly : s.periodOnly = true) (hzero : zero w1.lag = true)
    (hphase : w1.machine.control.phase = 4)
    (hprediction : GalilScaffoldChainConsume.symbol w1.machine.control.period.focus
      = read (right s.right)) :
    shiftGuardVM (afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
      (afterMismatch s ⟨left s.left,right s.right,ChainVM.watch w1⟩ vq)) := by
  obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hraw
  have hinvariant := minimalAcrossRestart_packed centre place entry q first hP hI
    (lowerAt_of_packedFromBoot centre place entry q first hP hI hboot) hrun
  have hwin : WindowRunPack (a :: rest) c s :=
    (PalPeg.CloseoutCheckW.ipackMW_last_of_stepsIMWC centre place entry q first hrun).win hP
  obtain ⟨rad, hscanPacked⟩ := scanInvariant_packed centre place entry q first hrun hm
  have hscan : ScanInvariant (a :: rest) (position s.center) rad s.left s.right := hscanPacked
  clear hscanPacked
  obtain ⟨hstep, hunbroken1, hfourOr, hdistance, htargetOnly, htargetCycle⟩ :=
    caughtUp_watch centre place entry q first hwin hm hmis hsearch hchainAt hzero hphase
  obtain ⟨R, hR, hright⟩ := hwin.radiusScan hm
  have hrad : rad = R := by
    have h1 : position s.right = position s.center + rad := hscan.rightPos
    have h2 : position s.right = position s.center + R := hright
    omega
  subst hrad
  obtain ⟨w0, hsource, hinternal⟩ := watch_source_of_step hstep hphase
  obtain ⟨cen₀, cc, hcentre, hinv, hk, -, -⟩ := hwin.window
  rw [hsource] at hinv
  obtain ⟨b, xs, hW0⟩ := hinv
  have hW1 := PalPeg.ShiftPalAlongTrace.watchWindow_step hW0 hinternal
  have hlength0 : periodLength w0 = xs.length + 1 :=
    PalPeg.ShiftPalAlongTrace.periodLength_of_coreP hW0.2.2
  have hlength1 : periodLength w1 = xs.length + 1 :=
    PalPeg.ShiftPalAlongTrace.periodLength_of_coreP hW1.2.2
  obtain ⟨m, hk⟩ := (hk w0 hsource).2 (by rw [hm]; decide)
  rw [hlength0] at hk
  have hcontinuation : Continuation (a :: rest) c s := hinvariant.continuation
  obtain ⟨-, hcanonical, hcycleLe, Lb, hLbPacked, hLbPos, hLbLePacked, hperiodLeftPacked,
      hbreak⟩ :=
    (hcontinuation w0 hsource).1 hm honly
  have hLb : (Lb : ℤ) + value s.radius + value s.cycle = (position s.center : ℤ) + 1 :=
    hLbPacked
  have hLbLe : Lb ≤ position s.center := hLbLePacked
  have hperiodLeft : PeriodOn (encoded (a :: rest)) (2 * periodLength w0) Lb
      (position s.center) := hperiodLeftPacked
  clear hLbPacked hLbLePacked hperiodLeftPacked
  rw [hlength0] at hcycleLe hperiodLeft hbreak
  rw [hR.2] at hLb
  have htwo : 2 * (xs.length + 1) ≤ rad := by
    have h := two_semiperiods_le hfourOr hdistance hR.2 (by rw [hm]; decide)
      (by rw [hlength1]; exact hcycleLe)
    rwa [hlength1] at h
  have hRC := scan_radius_lt hscan
  have hrightPos : position s.right = position s.center + rad := hscan.rightPos
  rw [hrightPos] at hW1
  have hpal := hscan.palindrome
  have hsize : cen₀ + 1 + 2 * (xs.length + 1) ≤ position s.center + rad + 1 := by
    rw [hk]; nlinarith
  obtain ⟨-, hpredictionText⟩ := PalPeg.RestartBoundary.prediction_eq_text hW1 hzero hsize
  have hleftRead := left_signed_read s.left (a :: rest) hscan.leftRep hscan.leftPresent
  rw [hscan.leftPos] at hleftRead
  have hmirror := hpal.2.2 (rad + 1 - 2 * (xs.length + 1)) (by omega)
  rw [show position s.center - (rad + 1 - 2 * (xs.length + 1))
      = position s.center - rad - 1 + 2 * (xs.length + 1) from by omega,
    show position s.center + (rad + 1 - 2 * (xs.length + 1))
      = position s.center + rad + 1 - 2 * (xs.length + 1) from by omega] at hmirror
  have hcycleOne : value s.cycle = 1 := by
    by_contra hne
    rcases Int.lt_or_gt_of_ne hne with hlow | hhigh
    · have hperiodSpan := spanPeriod_of_window hW1 hzero hcentre hk hpal htwo
      have hinside := hperiodSpan (Lb - 1) (by omega) (by omega)
      apply hbreak
      unfold signedRead
      rw [if_neg (by omega), show ((Lb : ℤ) - 1).toNat = Lb - 1 from by omega]
      exact hinside
    · have hleftPeriod := hperiodLeft (position s.center - rad - 1) (by omega) (by omega)
      apply hmis
      rw [hleftRead, ← hprediction, hpredictionText, ← hmirror, ← hleftPeriod]
      unfold signedRead
      rw [if_neg (by omega),
        show (((position s.center - rad : ℕ) : ℤ) - 1).toNat = position s.center - rad - 1
          from by omega]
  have hsingle : singlePositive s.cycle = true :=
    (singlePositive_iff _ hcanonical).mpr hcycleOne
  have hne : s.chain ≠ .idle := by rw [hsource]; simp
  refine ⟨w1, ?_, hzero, hphase, hunbroken1, ?_, ?_⟩
  · rw [afterBirth_chain]
    simp [afterMismatch, searchLens, scanLens]
  · rw [htargetOnly, honly, htargetCycle hne]
    simpa using hsingle
  · rw [hprediction]
    simp [afterBirth_right, afterMismatch_right]

#print axioms shiftGuard_of_tail_caughtUp
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
  have hmove : MoveAbove (a :: rest) (position s.center) (value s.lower).toNat H := hpayload.1
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

/-- What the chain tick of a mismatching comparison does to a live chain in a round after a
shift: the chain was already broken, or it ends as a caught-up watch in phase `4` (the chain has
no birth payload, and its watch is caught up and in phase `4` throughout the round). -/
theorem tailTick_cases {raw : List (Fin 2)} (hraw : raw ≠ []) {c₀ : Control} {r₀ : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    (hboot : CloseoutCheckW.PackedFromBoot centre place entry q first raw ⟨c₀, r₀⟩)
    {k : ℕ} {c : Control} {s : GalilVM} {vq : SearchVM} {z : ChainVM}
    (hrun : CloseoutCheckW.StepsIMWC centre place entry q first raw k ⟨c₀,r₀⟩ ⟨c, s⟩)
    (hm : c.mode = .scan) (honly : s.periodOnly = true) (hidle : s.chain ≠ .idle)
    (hchainAt : chainAt false (decide (vq.search.mode = .found)) (vq.dp.config.tapes 11)
      ((PofC centre place entry raw).centre s) ((PofC centre place entry raw).place s)
      s.center s.radius s.chain z) :
    (∃ wb, s.chain = .broken wb) ∨
      ∃ w1, z = .watch w1 ∧ zero w1.lag = true ∧ w1.machine.control.phase = 4 := by
  obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hraw
  have hinvariant := minimalAcrossRestart_packed centre place entry q first hP hI
    (lowerAt_of_packedFromBoot centre place entry q first hP hI hboot) hrun
  have htail : ScanMinimal (fun _ _ => False) (a :: rest) s := hinvariant.tailRound hm honly
  have hcontinuation : Continuation (a :: rest) c s := hinvariant.continuation
  cases hs : s.chain with
  | idle => exact absurd hs hidle
  | broken wb => exact Or.inl ⟨wb, rfl⟩
  | copy t h p v lag margin ver =>
    simp only [ScanMinimal, hs] at htail
    obtain ⟨H, n, -, -, -, hfalse⟩ := htail
    exact hfalse.elim
  | back v h lag margin ver =>
    simp only [ScanMinimal, hs] at htail
    obtain ⟨-, H, -, -, -, hfalse⟩ := htail
    exact hfalse.elim
  | watch w0 =>
    right
    obtain ⟨⟨hzero, hphase⟩, -⟩ := (hcontinuation w0 hs).1 hm honly
    rw [hs] at hchainAt
    rcases hchainAt with ⟨-, htick⟩ | ⟨hidle', -, -⟩ | ⟨hidle', -, -⟩
    · obtain ⟨y, hstep, hzy⟩ := htick
      rw [if_neg (by simp)] at hzy
      subst hzy
      generalize hx : ChainVM.watch w0 = x at hstep
      cases hstep with
      | watchStep w w1 hinternal =>
        cases hx
        have htickWatch : ChainTick false (.watch w0) (.watch w1) :=
          ⟨.watch w1, .watchStep w0 w1 hinternal, by simp⟩
        have hcaught := caughtUp_watch_tick htickWatch hzero hphase
        exact ⟨w1, rfl, hcaught⟩
      | watchBreak w hb =>
        cases hx
        rw [not_zero_of_positive hb.1] at hzero
        cases hzero
      | idle => cases hx
      | brokenIdle => cases hx
      | copyBit => cases hx
      | copyEnd => cases hx
      | backStep => cases hx
      | backDone => cases hx
    · cases hidle'
    · cases hidle'

#print axioms tailTick_cases

/-- **A first-round scan state of a packed run from boot has no broken chain off the restart
guard** (Scala: `chain restart violates the confirmed-period invariant` is unreachable). -/
theorem not_broken_firstRound {raw : List (Fin 2)} (hraw : raw ≠ []) {c₀ : Control}
    {r₀ : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    (hboot : CloseoutCheckW.PackedFromBoot centre place entry q first raw ⟨c₀, r₀⟩)
    {k : ℕ} {c : Control} {s : GalilVM}
    (hrun : CloseoutCheckW.StepsIMWC centre place entry q first raw k ⟨c₀,r₀⟩ ⟨c, s⟩)
    (hm : c.mode = .scan) (hfirstRound : s.periodOnly = false)
    (hnoGuard : ¬ restartGuardVM s) (wb : GalilScaffoldChainWatch.State) :
    s.chain ≠ .broken wb := by
  obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hraw
  have hinvariant := minimalAcrossRestart_packed centre place entry q first hP hI
    (lowerAt_of_packedFromBoot centre place entry q first hP hI hboot) hrun
  exact fun hbroken => hnoGuard (hinvariant.guard hm hfirstRound wb hbroken)

#print axioms not_broken_firstRound

end PalPeg.RestartLowerRun
