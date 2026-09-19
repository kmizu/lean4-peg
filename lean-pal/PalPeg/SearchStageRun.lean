import PalPeg.SearchStageHistory
import PalPeg.CanonicalSearchHistory
import PalPeg.CanonicalSearchReady

/-!
# The stage history along the ticks of the machine

`SearchStageHistory.StageHistory` with the clock budget at the centre's own place, transported
over the scan ticks of the concrete frame.  A restart or a replay start lands in a fresh search
(`stageHistory_begin`); a background tick and a matched comparison are one search event.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace PalPeg.SearchStageRun

open PalPeg GalilScaffoldTop GalilScaffoldController GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilRunSkeleton GalilInvPlus3 CanonicalSearchProgram
open GalilBranchInvariants2 CanonicalSearchBudget PalPeg.SearchStageHistory PalPeg.ShapedRun

variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- The budget and the stage history of the running search, at the centre's place and against
the scan radius. -/
def StageData (raw : List (Fin 2)) (clock : ℕ) (s : GalilVM) : Prop :=
  ∃ lower, BudgetInv ((PofC centre place entry raw).place s) lower clock (searchLens.get s) ∧
    StageHistory ((PofC centre place entry raw).place s) lower (value s.radius)
      (searchLens.get s) ∧
    (searchLens.get s).search.mode ≠ .found

structure StageAt (raw : List (Fin 2)) (x : State GalilVM) : Prop where
  scan : x.ctl.mode = .scan → x.vm.chain = .idle → StageData centre place entry raw x.ctl.clock x.vm
  shift : x.ctl.mode = .shift → x.vm.chain ≠ .idle

theorem stageAt_restarted {raw : List (Fin 2)} {c : Control} {r : GalilVM} {Rad : ℕ}
    {last : Counter} (hR : Restarted raw r Rad last) (hSE : StageEntry Rad last)
    (hm : c.mode = .scan) (hclock : c.clock = 2048) : StageAt centre place entry raw ⟨c, r⟩ := by
  obtain ⟨lower, hbudget, hsearch⟩ :=
    budgetInv_restarted ((PofC centre place entry raw).place r) hR hSE
  refine ⟨fun _ _ => ⟨lower, ?_, stageHistory_begin _ lower r.radius hsearch,
    by rw [hsearch]; intro hfound; cases hfound⟩, fun h => by simp [hm] at h⟩
  show BudgetInv _ lower c.clock _
  rw [hclock]
  exact hbudget

private theorem idle_source {a found : Bool} {ans : GalilScaffoldTape.Tape} {cc : Fin 3}
    {wk : GalilScaffoldPlace.Place} {ver : GalilScaffoldInputHead.PlaceHead} {rad : Counter}
    {x y : ChainVM} (h : chainAt a found ans cc wk ver rad x y) (hy : y = .idle) : x = .idle := by
  rcases h with ⟨hx,ht⟩ | ⟨hx,_,_⟩ | ⟨hx,_,_⟩
  · exact ((chainTick_ne_idle ht hx) hy).elim
  · exact hx
  · exact hx

/-- An idle chain that stays idle saw no find. -/
private theorem notFound_of_idle {a found : Bool} {ans : GalilScaffoldTape.Tape} {cc : Fin 3}
    {wk : GalilScaffoldPlace.Place} {ver : GalilScaffoldInputHead.PlaceHead} {rad : Counter}
    (h : chainAt a found ans cc wk ver rad .idle .idle) : found = false := by
  rcases h with ⟨hx, _⟩ | ⟨_, hf, _⟩ | ⟨_, _, hz⟩
  · exact absurd rfl hx
  · exact hf
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

/-- A background tick is one search event without a match. -/
theorem stageData_background {raw : List (Fin 2)} {clock clock' : ℕ} {s t : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hsource : s.chain = .idle → StageData centre place entry raw clock s)
    (hevent : ClockEvent false clock clock')
    (hb : (galilFrameS (PofC centre place entry raw) q first).background s t)
    (hidle : t.chain = .idle) : StageData centre place entry raw clock' t := by
  obtain ⟨-, -, hch, hcenter, -, hradius, -, -, -, -, -, hse⟩ :=
    backgroundS_fields (PofC centre place entry raw) q first hb
  rw [hidle] at hch
  have hsourceIdle := idle_source hch rfl
  obtain ⟨lower, hbudget, hhistory, -⟩ := hsource hsourceIdle
  rw [hsourceIdle] at hch
  have hnotFound := of_decide_eq_false (notFound_of_idle hch)
  have hstep : searchStep ((PofC centre place entry raw).place s) false
      (searchLens.get s) (searchLens.get t) := by
    rcases hse with ⟨_, hh⟩ | ⟨hn, _⟩
    · exact hh
    · exact (hn hsourceIdle).elim
  have hnext := stageHistory_step hbudget hhistory hstep
  refine ⟨lower, ?_, ?_, hnotFound⟩
  · rw [hP.2 t s hcenter]
    exact budget_step hbudget hevent hstep
  · rw [hP.2 t s hcenter, hradius]
    simpa using hnext

/-- A matched comparison is one search event with a match: the radius grows by one. -/
theorem stageData_matched {raw : List (Fin 2)} {clock clock' : ℕ} {s t : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hsource : s.chain = .idle → StageData centre place entry raw clock s)
    (hevent : ∀ a, ClockEvent a clock clock')
    (hcmp : (galilFrameS (PofC centre place entry raw) q first).compare s t)
    (hmatched : (galilFrameS (PofC centre place entry raw) q first).matched t)
    (hidle : t.chain = .idle) : StageData centre place entry raw clock' t := by
  obtain ⟨vs, vq, a, -, -, hiff, hse, hch, heq⟩ := hcmp
  have ha : a = true := by
    cases a with
    | true => rfl
    | false =>
      exfalso
      have hm' : GalilScaffoldInputHead.read t.left = GalilScaffoldInputHead.read t.right :=
        hmatched
      rw [heq, afterBirth_left, afterBirth_right] at hm'
      exact absurd (hiff.2 hm') (by simp)
  subst ha
  have hchain : t.chain = vs.chain := by rw [heq, afterBirth_chain]; rfl
  have hcenter : t.center = s.center := by rw [heq, afterBirth_center]; rfl
  have hradius : t.radius = inc s.radius := by rw [heq, afterBirth_radius]; rfl
  have hget : searchLens.get t = vq := by rw [heq, afterBirth_searchGet]; rfl
  rw [hchain.symm.trans hidle] at hch
  have hsourceIdle := idle_source hch rfl
  obtain ⟨lower, hbudget, hhistory, -⟩ := hsource hsourceIdle
  rw [hsourceIdle] at hch
  have hnotFound := of_decide_eq_false (notFound_of_idle hch)
  have hstep : searchStep ((PofC centre place entry raw).place s) true (searchLens.get s) vq := by
    rcases hse with ⟨_, hh⟩ | ⟨hn, _⟩
    · exact hh
    · exact (hn hsourceIdle).elim
  have hnext := stageHistory_step hbudget hhistory hstep
  refine ⟨lower, ?_, ?_, by rw [hget]; exact hnotFound⟩
  · rw [hP.2 t s hcenter, hget]
    exact budget_step hbudget (hevent true) hstep
  · rw [hP.2 t s hcenter, hget, hradius, inc_value]
    simpa using hnext

/-- Every tick of the canonical schedule transports the stage data. -/
theorem stageAt_tick {raw : List (Fin 2)} {x y : State GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hnotInit : x.ctl.mode ≠ .init)
    (hsource : StageAt centre place entry raw x)
    (hfield : PalPeg.CanonicalSearchReady.Field x)
    (ht : Tick (galilFrameS (PofC centre place entry raw) q first) 2048 x y)
    (hrestart : x.ctl.mode = .scan → restartVM entry x.vm y.vm →
      ∃ (Rad : ℕ) (last : Counter), Restarted raw y.vm Rad last ∧ StageEntry Rad last ∧
        y.ctl.mode = .scan ∧ y.ctl.clock = 2048)
    (hreplay : x.ctl.mode = .replayStart →
      Restarted raw y.vm 0 reset ∧ y.ctl.mode = .scan ∧ y.ctl.clock = 2048) :
    StageAt centre place entry raw y := by
  have hclockPos := hfield.clock_pos
  have hclockLe := hfield.clock_le
  cases ht with
  | init c s t hm ht => exact absurd hm hnotInit
  | scan_wait c s t hm _ hb =>
    have hpos : 1 ≤ c.clock := hclockPos
    have hle : c.clock ≤ 2048 := hclockLe
    exact ⟨fun _ => stageData_background centre place entry q first hP (hsource.scan hm)
      (by simp [ClockEvent]; omega) hb, fun h => by simp_all⟩
  | scan_count c s t hm _ hclock hb =>
    have hpos : 1 ≤ c.clock := hclockPos
    have hle : c.clock ≤ 2048 := hclockLe
    exact ⟨fun _ => stageData_background centre place entry q first hP (hsource.scan hm)
      (by simp [ClockEvent]; omega) hb, fun h => by simp_all⟩
  | scan_match c s t u o hm _ hclock hc hmt hp _ =>
    have hpos : 1 ≤ c.clock := hclockPos
    have hle : c.clock ≤ 2048 := hclockLe
    have hchain : u.chain = t.chain := by rw [hp]; split <;> rfl
    have hcenter : u.center = t.center := by rw [hp]; split <;> rfl
    have hradius : u.radius = t.radius := by rw [hp]; split <;> rfl
    have hget : searchLens.get u = searchLens.get t := by rw [hp]; split <;> rfl
    refine ⟨fun _ hidle => ?_, fun h => by simp_all⟩
    obtain ⟨lower, hbudget, hhistory, hnotFound⟩ :=
      stageData_matched centre place entry q first hP (hsource.scan hm)
        (clock' := 2048) (fun a => by cases a <;> simp [ClockEvent] <;> omega) hc hmt
        (hchain.symm.trans hidle)
    refine ⟨lower, ?_, ?_, ?_⟩
    · show BudgetInv ((PofC centre place entry raw).place u) lower 2048 (searchLens.get u)
      rw [hget, hP.2 u t hcenter]
      exact hbudget
    · show StageHistory ((PofC centre place entry raw).place u) lower (value u.radius)
        (searchLens.get u)
      rw [hget, hP.2 u t hcenter, hradius]
      exact hhistory
    · show (searchLens.get u).search.mode ≠ .found
      rw [hget]
      exact hnotFound
  | scan_shift c s t u hm _ _ _ _ _ _ hb =>
    obtain ⟨v, _, rfl⟩ := hb
    exact ⟨(fun hs _ => by simp_all), (fun _ h => by cases h)⟩
  | shift_one c s t hm _ ho =>
    obtain ⟨_, _, _, wv, hw, hget⟩ := ho.1
    have hset := ho.2
    rw [hget] at hset
    rw [hset]
    exact ⟨(fun _ _ => by contradiction), (fun _ h => by cases h)⟩
  | shift_done c s o hm _ _ =>
    exact ⟨fun _ hidle => (hsource.shift hm hidle).elim, fun h => by cases h⟩
  | replayStart c s t o hm hr _ _ =>
    obtain ⟨hR, hmode, hclock⟩ := hreplay hm
    exact stageAt_restarted centre place entry hR (stageEntry_zero _) hmode hclock
  | restart c s t hm hr =>
    obtain ⟨Rad, last, hR, hSE, hmode, hclock⟩ := hrestart hm hr
    exact stageAt_restarted centre place entry hR hSE hmode hclock
  | scan_fallback | copy_one | copy_done | home_start | home_step | fpp_slice | fpp_done
  | markEnd_step | markEnd_found | choose_select | choose_step | rewind_done | rewind_one
  | rewind_pair =>
    constructor
    · intro hs hi
      simp_all
    · intro hs h
      simp_all

open PalPeg.CanonicalSearchReady in
/-- The stage data and the readiness field along a shaped run. -/
theorem stageAt_shaped {raw : List (Fin 2)} {n : ℕ} {x y : State GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hx : StageAt centre place entry raw x) (hfield : Field x) (hnotInit : x.ctl.mode ≠ .init)
    (hr : ShapedSteps centre place entry q first raw n x y) :
    StageAt centre place entry raw y ∧ Field y := by
  induction hr with
  | zero => exact ⟨hx, hfield⟩
  | @succ _ x y z ht hrestart hrs _ ih =>
    have hy := stageAt_tick centre place entry q first hP hnotInit hx hfield ht hrestart hrs
    have hfy : Field y := field_tick centre place entry q first hnotInit hfield ht
      (fun hm hr => by
        obtain ⟨Rad, last, hR, hSE, hmode, hclock⟩ := hrestart hm hr
        exact field_restarted ((PofC centre place entry raw).place y.vm) hR hSE hmode hclock)
      (fun hm => by
        obtain ⟨hR, hmode, hclock⟩ := hrs hm
        exact field_restarted ((PofC centre place entry raw).place y.vm) hR
          (stageEntry_zero _) hmode hclock)
    exact ih hy hfy (PalPeg.BranchSupply.tick_target_mode_ne_init ht)

open PalPeg.CanonicalSearchReady in
/-- The origin records the search segment from its last restart. -/
theorem stageAt_invLPS {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hI : InvLPS (PofC centre place entry raw) q first raw c s) :
    StageAt centre place entry raw ⟨c, s⟩ ∧ Field ⟨c, s⟩ := by
  obtain ⟨r, Rad, last, es, c₀, hR, hSE, hclock, hseg⟩ := hI.2
  have hm : c.mode = .scan := (PalPeg.GalilOracleLocal.invS_mode hI.1.1.1.1.1).1
  have hm₀ := watchSegE_first_mode q first hseg hm
  obtain ⟨n, hshape⟩ := watchSegE_shaped centre place entry q first hseg
  exact stageAt_shaped centre place entry q first hP
    (stageAt_restarted centre place entry hR hSE hm₀ hclock)
    (field_restarted ((PofC centre place entry raw).place r) hR hSE hm₀ hclock)
    (by rw [hm₀]; decide) hshape

open PalPeg.CanonicalSearchReady in
/-- The stage data at every point of a packed run out of an `InvLPS` origin. -/
theorem stageAt_packed {raw : List (Fin 2)} {c₀ : Control} {r₀ : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    {k : ℕ} {y : State GalilVM}
    (hrun : CloseoutCheckW.StepsIMWC centre place entry q first raw k ⟨c₀,r₀⟩ y) :
    StageAt centre place entry raw y := by
  obtain ⟨g, h0, hk, ht, hcan, -⟩ := hrun
  have hm₀ : c₀.mode = .scan := (PalPeg.GalilOracleLocal.invS_mode hI.1.1.1.1.1).1
  have hall : ∀ i, i ≤ k →
      StageAt centre place entry raw (g i) ∧ Field (g i) ∧ (g i).ctl.mode ≠ .init := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [h0]
      obtain ⟨hstage, hfield⟩ := stageAt_invLPS centre place entry q first hP hI
      exact ⟨hstage, hfield, by show c₀.mode ≠ .init; rw [hm₀]; decide⟩
    | succ i ih =>
      intro hn
      obtain ⟨hstage, hfield, hnotInit⟩ := ih (by omega)
      have htick := ht.tick i (by omega)
      have horacle := hcan i (by omega)
      refine ⟨stageAt_tick centre place entry q first hP hnotInit hstage hfield htick
          horacle.restartStage horacle.replayStage,
        field_tick centre place entry q first hnotInit hfield htick
          (fun hm hr => by
            obtain ⟨Rad, last, hR, hSE, hmode, hclock⟩ := horacle.restartStage hm hr
            exact field_restarted ((PofC centre place entry raw).place (g (i+1)).vm) hR hSE
              hmode hclock)
          (fun hm => by
            obtain ⟨hR, hmode, hclock⟩ := horacle.replayStage hm
            exact field_restarted ((PofC centre place entry raw).place (g (i+1)).vm) hR
              (stageEntry_zero _) hmode hclock),
        PalPeg.BranchSupply.tick_target_mode_ne_init htick⟩
  simpa only [hk] using (hall k le_rfl).1

/-- **The search contract in the middle of a stage.**  While the search is active the DP tapes
of the current stage say nothing, but the scan radius is inside a candidate-free window of the
centre's stream, which is all the contract reads. -/
theorem dpPack_of_stage {raw : List (Fin 2)} {clock : ℕ} {s : GalilVM} {Rad : ℕ}
    (hP : Decodes (PofC centre place entry raw))
    (hdata : StageData centre place entry raw clock s)
    (hactive : Active (searchLens.get s).search.mode)
    (hradius : value s.radius = (Rad : ℤ))
    (hcen : PalPeg.GalilInvPlus2.CentreRep raw s)
    (hlow : ∀ δ, 0 < δ → δ ≤ (value s.lower).toNat →
      ¬ HasPeriod (Span raw (position s.center) Rad) (2*δ)) :
    PalPeg.GalilLeafMismatch.DpPack raw s Rad := by
  obtain ⟨lower, hbudget, hhistory, -⟩ := hdata
  obtain ⟨H, hnone, hinside⟩ := radius_le_window hbudget hhistory hactive
  obtain ⟨a₀, ls₀, rs₀, q₀, hdec, hraw⟩ :=
    represents_decompose s.center raw hcen.1 hcen.2
  obtain ⟨-, hplace⟩ := hP.1 s a₀ ls₀ rs₀ q₀ s.center.gap hdec
  have hlower : value s.lower = (lower : ℤ) := by
    have hlowerEq : s.lower = ofNat lower := hbudget.lower_eq
    rw [hlowerEq, ofNat_value]
  refine ⟨a₀, ls₀, rs₀, q₀, s.center.gap, lower, H,
    {GalilScaffoldProgram.denote (searchLens.get s).dp.config with pc := 347},
    hraw, congrArg position hdec, ?_, Or.inr ⟨rfl, fun k _ => ?_⟩, rfl, ?_⟩
  · rw [hradius] at hinside
    exact_mod_cast hinside
  · rw [← hplace]
    exact hnone k
  · intro δ hδ0 hδ
    exact hlow δ hδ0 (by omega)

end PalPeg.SearchStageRun
