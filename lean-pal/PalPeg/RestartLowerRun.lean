import PalPeg.RestartLower
import PalPeg.CloseoutStageBoot
import PalPeg.SearchStageRun
import PalPeg.ChainClock

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

/-- The run invariant: the minimal-period payload, the excluded lower bound of the running
search, and the excluded `last` of a broken chain at a restart-guard state. -/
structure MinimalAcrossRestart (raw : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  minimal : ModeMinimal (MovePayload raw s) raw c s
  lowerAt : LowerAt raw c s
  broken : BrokenStage (LastExcluded raw) c s
  firstRound : FirstRoundSem raw c s

/-- `MinimalAcrossRestart` at every point of a packed run out of an `InvLPS` origin whose own
lower bound is excluded. -/
theorem minimalAcrossRestart_packed {raw : List (Fin 2)} {c₀ : Control} {r₀ : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    (horigin : LowerAt raw c₀ r₀)
    {k : ℕ} {y : State GalilVM}
    (hrun : CloseoutCheckW.StepsIMWC centre place entry q first raw k ⟨c₀,r₀⟩ y) :
    MinimalAcrossRestart raw y.ctl y.vm := by
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
  have hall : ∀ i, i ≤ k → MinimalAcrossRestart raw (g i).ctl (g i).vm := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [hg0]
      exact ⟨by simp [ModeMinimal, hiMode, ScanMinimal, hiChain], horigin,
        brokenStage_of_not_broken (by rw [hiMode]; decide)
          (fun w hw => by rw [hiChain] at hw; cases hw),
        firstRoundSem_of_idle hiChain⟩
    | succ i ih =>
      intro hik
      have hsource := ih (by omega)
      have htick := htr.tick i (by omega)
      have hwinX := (hpk i (by omega)).win hP
      have hbirthSource : (g i).ctl.mode = .scan →
          BirthMinimal centre place entry (MovePayload raw (g i).vm) raw (g i).vm :=
        fun hm => birthMinimal_of_lowerAt centre place entry q first hP hI
          (hprefix i (by omega)) hm hsource.lowerAt
      refine ⟨?_, lowerAt_tick centre place entry q first htick hsource.lowerAt hsource.broken,
        ?_, firstRoundSem_tick centre place entry q first htick hsource.firstRound
          hsource.broken hbirthSource⟩
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

end PalPeg.RestartLowerRun
