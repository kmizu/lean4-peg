import PalPeg.RestartLower

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

/-- The lower bound a restart would install from this broken chain is excluded at `C`. -/
def LastExcluded (raw : List (Fin 2)) (C : ℕ) (w : GalilScaffoldChainWatch.State) : Prop :=
  ∀ L : ℕ, value w.machine.control.last = (L : ℤ) → LowerExcluded raw C L

/-- While the search runs with an idle chain, its lower bound is excluded at the centre. -/
def LowerAt (raw : List (Fin 2)) (c : Control) (s : GalilVM) : Prop :=
  c.mode = .scan → s.chain = .idle →
    ∀ L : ℕ, value s.lower = (L : ℤ) → LowerExcluded raw (position s.center) L

theorem lowerAt_of_reset {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    (hlower : s.lower = reset) : LowerAt raw c s := by
  intro _ _ L hL
  rw [hlower] at hL
  have hL0 : L = 0 := by
    have hzero : value reset = 0 := rfl
    rw [hzero] at hL
    exact_mod_cast hL.symm
  rw [hL0]
  exact lowerExcluded_zero _ _

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
  have hkeep : x.ctl.mode = .scan → x.vm.chain = .idle → y.vm.lower = x.vm.lower :=
    fun hm hidle => lower_eq_of_regular_tick centre place entry q first ht
      (by rw [hm]; decide) (by rw [hm]; decide)
      (fun _ hrestart => by
        obtain ⟨w0, hw0, -⟩ := hrestart
        rw [hidle] at hw0
        cases hw0)
  have hbackground : ∀ {c c' : Control} {s t : GalilVM}, x = ⟨c, s⟩ → y = ⟨c', t⟩ →
      c.mode = .scan → (galilFrameS (PofC centre place entry raw) q first).background s t →
      LowerAt raw c' t := by
    intro c c' s t hx hy hm hb
    subst hx
    subst hy
    obtain ⟨-, -, hch, hcenter, -⟩ := backgroundS_fields (PofC centre place entry raw) q first hb
    intro _ hidle L hL
    rw [hidle] at hch
    have hsourceIdle : s.chain = .idle := idle_of_chainAt hch
    have hlowerEq : t.lower = s.lower := hkeep hm hsourceIdle
    rw [hcenter]
    exact hlowerAt hm hsourceIdle L (by rw [← hlowerEq]; exact hL)
  cases ht with
  | init c s t hm hi =>
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hlower,_⟩ := hi
    exact lowerAt_of_reset hlower
  | scan_wait c s t hm hav hb => exact hbackground rfl rfl hm hb
  | scan_count c s t hm hav hc hb => exact hbackground rfl rfl hm hb
  | scan_match c s s' t o hm hav hc hcmp hmt hpl ho =>
    have hcmp' : compareFound (PofC centre place entry raw) q first s s' := hcmp
    obtain ⟨vs, vq, a, -, -, -, -, hch, heq⟩ := hcmp'
    obtain ⟨-, -, hchain', hcenter', -⟩ := PalPeg.WindowTick.compare_target_heads heq
    have hchain : t.chain = s'.chain := by rw [hpl]; split <;> rfl
    have hcenter : t.center = s'.center := by rw [hpl]; split <;> rfl
    intro _ hidle L hL
    have htargetIdle : t.chain = .idle := hidle
    rw [hchain, hchain'] at htargetIdle
    rw [htargetIdle] at hch
    have hsourceIdle : s.chain = .idle := idle_of_chainAt hch
    have hlowerEq : t.lower = s.lower := hkeep hm hsourceIdle
    show LowerExcluded raw (position t.center) L
    rw [hcenter, hcenter']
    exact hlowerAt hm hsourceIdle L (by rw [← hlowerEq]; exact hL)
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
    obtain ⟨w, hw⟩ := hstage.1 hm
    intro _ hidle
    have hsourceIdle : s.chain = .idle := hidle
    rw [hw] at hsourceIdle
    cases hsourceIdle
  | replayStart c s t o hm hr ho ho' =>
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hlower,_⟩ := hr
    exact lowerAt_of_reset hlower
  | restart c s t hm hr =>
    obtain ⟨w, hw, hmargin, hlast, hlag, rfl⟩ := hr
    intro _ _ L hL
    exact ((hstage.2 hm w hw).2 ⟨w, hw, hmargin, hlast, hlag⟩).2 L hL
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

/-- The birth payload without the move inequality, from the excluded lower bound. -/
theorem birthMinimal_of_lowerAt {raw : List (Fin 2)} {c₀ : Control} {r₀ : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    {k : ℕ} {y : State GalilVM}
    (hrun : CloseoutCheckW.StepsIMWC centre place entry q first raw k ⟨c₀,r₀⟩ y)
    (hm : y.ctl.mode = .scan) (hlowerAt : LowerAt raw y.ctl y.vm) :
    BirthMinimal centre place entry (fun _ _ => True) raw y.vm := by
  intro a vq hidle he hf
  obtain ⟨H, hcopy, hfuture, -⟩ :=
    PalPeg.CanonicalSearchHistory.birthMinimals_packed centre place entry q first hP hI hrun hm
      hidle he hf (fun lower hlowerEq => hlowerAt hm hidle lower (by
        rw [← searchEffect_lower_eq he, hlowerEq, ofNat_value]))
  exact ⟨H, hcopy, hfuture, trivial⟩

/-- The run invariant: the minimal-period payload, the excluded lower bound of the running
search, and the excluded `last` of a broken chain at a restart-guard state. -/
structure MinimalAcrossRestart (raw : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  minimal : ModeMinimal (fun _ _ => True) raw c s
  lowerAt : LowerAt raw c s
  broken : BrokenStage (LastExcluded raw) c s

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
          (fun w hw => by rw [hiChain] at hw; cases hw)⟩
    | succ i ih =>
      intro hik
      have hsource := ih (by omega)
      have htick := htr.tick i (by omega)
      have hwinX := (hpk i (by omega)).win hP
      refine ⟨?_, lowerAt_tick centre place entry q first htick hsource.lowerAt hsource.broken, ?_⟩
      · exact modeMinimal_tick_packed centre place entry q first hP htick hsource.minimal
          (hpk i (by omega)) (hpk (i+1) (by omega)) (haux i (by omega))
          (fun hm => birthMinimal_of_lowerAt centre place entry q first hP hI
            (hprefix i (by omega)) hm hsource.lowerAt)
      · refine brokenStage_tick centre place entry q first htick (hcan i (by omega)).canonical
          hsource.broken
          (ledgerAt_packed centre place entry q first hP hI (hprefix i (by omega)))
          hwinX ((hpk (i+1) (by omega)).win hP) (watch_unbroken_of_window hwinX)
          (fun c s s' w1 w' hx hm hcmp hmt hstep hbreak =>
            hboundary i c s s' (hx ▸ hprefix i (by omega)) hm hcmp hmt w1 w' hstep hbreak) ?_
        intro c s s' w1 w' hx hm hcmp hmt hstep hbreak hmargin L hL
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
        have hminimal : ScanMinimal (fun _ _ => True) raw s := by
          have hmode := hsource.minimal
          rw [hx] at hmode
          simpa [ModeMinimal, hm] using hmode
        exact lowerExcluded_at_break hwin hm hscan hR hledger hminimal hstep hbreak hmargin
          (hboundary i c s s' hrunSource hm hcmp hmt w1 w' hstep hbreak) hL
  rw [← hgk]
  exact hall k le_rfl

end PalPeg.RestartLowerRun
