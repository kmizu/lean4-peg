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
    StageHistory ((PofC centre place entry raw).place s) lower (value s.radius) (searchLens.get s)

structure StageAt (raw : List (Fin 2)) (x : State GalilVM) : Prop where
  scan : x.ctl.mode = .scan → x.vm.chain = .idle → StageData centre place entry raw x.ctl.clock x.vm
  shift : x.ctl.mode = .shift → x.vm.chain ≠ .idle

theorem stageAt_restarted {raw : List (Fin 2)} {c : Control} {r : GalilVM} {Rad : ℕ}
    {last : Counter} (hR : Restarted raw r Rad last) (hSE : StageEntry Rad last)
    (hm : c.mode = .scan) (hclock : c.clock = 2048) : StageAt centre place entry raw ⟨c, r⟩ := by
  obtain ⟨lower, hbudget, hsearch⟩ :=
    budgetInv_restarted ((PofC centre place entry raw).place r) hR hSE
  refine ⟨fun _ _ => ⟨lower, ?_, stageHistory_begin _ lower r.radius hsearch⟩,
    fun h => by simp [hm] at h⟩
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
  obtain ⟨lower, hbudget, hhistory⟩ := hsource hsourceIdle
  have hstep : searchStep ((PofC centre place entry raw).place s) false
      (searchLens.get s) (searchLens.get t) := by
    rcases hse with ⟨_, hh⟩ | ⟨hn, _⟩
    · exact hh
    · exact (hn hsourceIdle).elim
  have hnext := stageHistory_step hbudget hhistory hstep
  refine ⟨lower, ?_, ?_⟩
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
  obtain ⟨lower, hbudget, hhistory⟩ := hsource hsourceIdle
  have hstep : searchStep ((PofC centre place entry raw).place s) true (searchLens.get s) vq := by
    rcases hse with ⟨_, hh⟩ | ⟨hn, _⟩
    · exact hh
    · exact (hn hsourceIdle).elim
  have hnext := stageHistory_step hbudget hhistory hstep
  refine ⟨lower, ?_, ?_⟩
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
    obtain ⟨lower, hbudget, hhistory⟩ :=
      stageData_matched centre place entry q first hP (hsource.scan hm)
        (clock' := 2048) (fun a => by cases a <;> simp [ClockEvent] <;> omega) hc hmt
        (hchain.symm.trans hidle)
    refine ⟨lower, ?_, ?_⟩
    · show BudgetInv ((PofC centre place entry raw).place u) lower 2048 (searchLens.get u)
      rw [hget, hP.2 u t hcenter]
      exact hbudget
    · show StageHistory ((PofC centre place entry raw).place u) lower (value u.radius)
        (searchLens.get u)
      rw [hget, hP.2 u t hcenter, hradius]
      exact hhistory
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

end PalPeg.SearchStageRun
