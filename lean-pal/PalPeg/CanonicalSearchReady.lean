import PalPeg.CanonicalSearchBudget
import PalPeg.ReadyTransport

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace PalPeg.CanonicalSearchReady

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilRunSkeleton
  PalPeg.GalilBranchInvariants2 PalPeg.CanonicalSearchBudget PalPeg.ShapedRun
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier

/-- Readiness on the only two controller modes where the oracle consumes it.
At an idle scan point the stronger clock-indexed budget is retained. -/
structure Field (x : State GalilVM) : Prop where
  clock_pos : 1 ≤ x.ctl.clock
  clock_le : x.ctl.clock ≤ 2048
  ready : x.ctl.mode=.scan → SearchReady (searchLens.get x.vm)
  readyS : x.ctl.mode=.shift → SearchReady (searchLens.get x.vm)
  funded : x.ctl.mode=.scan → x.vm.chain=.idle →
    ∃ lower, BudgetSome lower x.ctl.clock (searchLens.get x.vm)
  fundedS : x.ctl.mode=.shift → x.vm.chain=.idle →
    ∃ lower, BudgetSome lower x.ctl.clock (searchLens.get x.vm)

private theorem ready_some {lower clock : ℕ} {v : SearchVM}
    (h : BudgetSome lower clock v) : SearchReady v := by
  obtain ⟨p,hp⟩ := h
  exact ready_of_budget hp

private theorem event_false_same {clock : ℕ} (hp : 1≤clock) (hle : clock≤2048) :
    ClockEvent false clock clock := by simp [ClockEvent,hp,hle]

private theorem event_false_dec {clock : ℕ} (hp : 1<clock) (hle : clock≤2048) :
    ClockEvent false clock (clock-1) := by simp [ClockEvent]; omega

private theorem event_reset (a : Bool) : ClockEvent a 1 2048 := by
  cases a <;> simp [ClockEvent]

private theorem background {P : Shared} {q : ℕ} {first : Fin 9}
    {clock' : ℕ} {c : Control} {s t : GalilVM} (hf : Field ⟨c,s⟩)
    (hm : c.mode=.scan) (hc : ClockEvent false c.clock clock')
    (hb : (galilFrameS P q first).background s t) :
    SearchReady (searchLens.get t) ∧
      (t.chain=.idle → ∃ lower, BudgetSome lower clock' (searchLens.get t)) := by
  obtain ⟨-,-,hchain,-,-,-,-,-,-,-,-,hse⟩ := backgroundS_fields P q first hb
  by_cases hi : s.chain=.idle
  · obtain ⟨lower,hbud⟩ := hf.funded hm hi
    rcases hse with ⟨_,hs⟩ | ⟨hne,_⟩
    · have ht := budgetSome_step hbud hc (P.place s) hs
      exact ⟨ready_some ht,fun _ => ⟨lower,ht⟩⟩
    · exact absurd hi hne
  · have he := searchEffect_active P hse hi
    refine ⟨by rw [he]; exact hf.ready hm,fun ht => absurd ht ?_⟩
    rcases hchain with ⟨_,h⟩|⟨h,_⟩|⟨h,_⟩
    · exact chainTick_ne_idle' h hi
    · exact absurd h hi
    · exact absurd h hi

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

theorem field_tick {w : List (Fin 2)} {x y : State GalilVM}
    (hnotInit : x.ctl.mode≠.init) (hf : Field x)
    (ht : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hrestart : x.ctl.mode=.scan → restartVM entry x.vm y.vm → Field y)
    (hreplay : x.ctl.mode=.replayStart → Field y) : Field y := by
  obtain ⟨c,s⟩ := x
  obtain ⟨c',t⟩ := y
  cases ht
  case init => rename_i hm _; exact absurd hm hnotInit
  case scan_wait =>
    rename_i hm _ hb
    have hc := event_false_same hf.clock_pos hf.clock_le
    obtain ⟨hr,hb⟩ := background hf hm hc hb
    exact ⟨hf.clock_pos,hf.clock_le,fun _ => hr,fun h => by simp [hm] at h,fun _ => hb,
      fun h => by simp [hm] at h⟩
  case scan_count =>
    rename_i h1 h2 h3 h4
    have hm : c.mode=.scan := by assumption
    have hclock : 1<c.clock := by assumption
    have hb : (galilFrameS (PofC centre place entry w) q first).background s t := by assumption
    obtain ⟨hr,hb⟩ := background hf hm (event_false_dec hclock hf.clock_le) hb
    exact ⟨by simp; omega,by simpa using (Nat.le_trans (Nat.sub_le c.clock 1) hf.clock_le),
      fun _ => hr,fun h => by simp [hm] at h,fun _ => hb,
      fun h => by simp [hm] at h⟩
  case scan_match =>
    rename_i s' o hmt hm hc0 hcmp _ hpl _
    obtain ⟨vs,vq,a,-,-,-,hse,hchain,hs'⟩ := hcmp
    have hpl' : t = (if c.replaying then {s' with replay := dec s'.replay} else s') := hpl
    have hget : searchLens.get t=vq := by
      subst hpl'; subst hs'
      cases c.replaying <;> cases a <;>
        simp [afterBirth_search,afterBirth_dp,afterBirth_lower,afterBirth_walker,
          afterCompare,afterMismatch,searchLens,scanLens]
    have hchain' : t.chain=vs.chain := by
      subst hpl'; subst hs'
      cases c.replaying <;> cases a <;>
        simp [afterBirth_chain,afterCompare,afterMismatch,searchLens,scanLens]
    by_cases hi : s.chain=.idle
    · obtain ⟨lower,hbud⟩ := hf.funded hm hi
      rcases hse with ⟨_,hs⟩|⟨hne,_⟩
      · have hev : ClockEvent a c.clock 2048 := by simpa [hc0] using event_reset a
        have hnext := budgetSome_step hbud hev ((PofC centre place entry w).place s) hs
        rw [← hget] at hnext
        exact ⟨by simp,by simp,fun _ => ready_some hnext,fun h => by simp [hm] at h,
          fun _ _ => ⟨lower,hnext⟩,fun h => by simp [hm] at h⟩
      · exact absurd hi hne
    · have he := searchEffect_active _ hse hi
      have hnidle : t.chain≠.idle := by
        rw [hchain']
        rcases hchain with ⟨_,h⟩|⟨h,_⟩|⟨h,_⟩
        · exact chainTick_ne_idle' h hi
        · exact absurd h hi
        · exact absurd h hi
      exact ⟨by simp,by simp,fun _ => by rw [hget,he]; exact hf.ready hm,
        fun h => by simp [hm] at h,fun _ h => absurd h hnidle,fun h => by simp [hm] at h⟩
  case scan_shift =>
    rename_i z h1 h2 h3 h4 h5 h6 h7 h8
    have hm : c.mode=.scan := by assumption
    have hc0 : c.clock=1 := by assumption
    have hcmp : (galilFrameS (PofC centre place entry w) q first).compare s z := by assumption
    have hbs : (PofC centre place entry w).beginShift z t := by assumption
    obtain ⟨vs,vq,a,-,-,-,hse,hchain,hs'⟩ := hcmp
    obtain ⟨_,_,ht⟩ := hbs
    have hget : searchLens.get t=vq := by
      subst ht; subst hs'
      cases a <;> simp [afterBirth_search,afterBirth_dp,afterBirth_lower,afterBirth_walker,
        afterCompare,afterMismatch,searchLens,scanLens]
    by_cases hi : s.chain=.idle
    · obtain ⟨lower,hbud⟩ := hf.funded hm hi
      rcases hse with ⟨_,hs⟩|⟨hne,_⟩
      · have hev : ClockEvent a c.clock 2048 := by simpa [hc0] using event_reset a
        have hnext := budgetSome_step hbud hev ((PofC centre place entry w).place s) hs
        rw [← hget] at hnext
        exact ⟨by simp,by simp,fun h => by simp [hm] at h,fun _ => ready_some hnext,
          fun h => by simp [hm] at h,fun _ _ => ⟨lower,hnext⟩⟩
      · exact absurd hi hne
    · have he := searchEffect_active _ hse hi
      exact ⟨by simp,by simp,fun h => by simp [hm] at h,
        fun _ => by rw [hget,he]; exact hf.ready hm,fun h => by simp [hm] at h,
        fun _ htidle => by
          subst ht; subst hs'
          cases a <;> simp [afterBirth_chain,afterCompare,afterMismatch] at htidle⟩
  case shift_one =>
    rename_i hm _ hso
    obtain ⟨hshift,hset⟩ := hso
    have hget : searchLens.get t=searchLens.get s := by rw [hset]; rfl
    exact ⟨hf.clock_pos,hf.clock_le,fun h => by simp [hm] at h,
      fun _ => by rw [hget]; exact hf.readyS hm,fun h => by simp [hm] at h,
      fun _ hi => by
        rw [hset] at hi
        obtain ⟨_,_,_,wg,_,he⟩ := hshift
        rw [he] at hi
        cases hi⟩
  case shift_done =>
    rename_i _ hm _ _
    exact ⟨hf.clock_pos,hf.clock_le,fun _ => hf.readyS hm,fun h => by simp [hm] at h,
      fun _ hi => hf.fundedS hm hi,fun h => by simp [hm] at h⟩
  case replayStart => exact hreplay (by assumption)
  case restart => exact hrestart (by assumption) (by assumption)
  all_goals
    (refine ⟨?_,?_,fun h => ?_,fun h => ?_,fun h _ => ?_,fun h _ => ?_⟩
     · simpa using hf.clock_pos
     · simpa using hf.clock_le
     all_goals exfalso; simp_all)

theorem field_restarted (p : GalilScaffoldPlace.Place)
    {w : List (Fin 2)} {c : Control} {r : GalilVM}
    {Rad : ℕ} {last : Counter} (hR : Restarted w r Rad last)
    (hSE : StageEntry Rad last) (hm : c.mode=.scan) (hc : c.clock=2048) :
    Field ⟨c,r⟩ := by
  obtain ⟨lower,hb⟩ := budgetSome_restarted p hR hSE
  have hr := ready_some hb
  exact ⟨by simpa [hc],by simpa [hc],fun _ => hr,fun h => by simp [hm] at h,
    fun _ _ => ⟨lower,by simpa [hc] using hb⟩,fun h => by simp [hm] at h⟩

theorem field_alongShaped {w : List (Fin 2)} {k : ℕ} {x y : State GalilVM}
    (h : ShapedSteps centre place entry q first w k x y)
    (hni : x.ctl.mode≠.init) (hx : Field x) : Field y := by
  induction h with
  | zero _ => exact hx
  | @succ _ x y z ht hnr hrs _ ih =>
      have hy : Field y := field_tick centre place entry q first
        hni hx ht
        (fun hm hr => absurd hr (hnr hm))
        (fun hm => by
          obtain ⟨hR,hmode,hclock⟩ := hrs hm
          exact field_restarted ((PofC centre place entry w).place y.vm)
            hR (stageEntry_zero _) hmode hclock)
      exact ih (PalPeg.BranchSupply.tick_target_mode_ne_init ht) hy

/-- Search readiness at every scan point of the actual shaped run. -/
theorem ready_of_invLPS_shaped {w : List (Fin 2)}
    {c₀ : Control} {r₀ : GalilVM}
    (hI₀ : PalPeg.GalilInvPlus3.InvLPS (PofC centre place entry w) q first w c₀ r₀)
    {j : ℕ} {x : State GalilVM}
    (hs : ShapedSteps centre place entry q first w j ⟨c₀,r₀⟩ x)
    (hmx : x.ctl.mode=.scan) : SearchReady (searchLens.get x.vm) := by
  obtain ⟨r,Rad,last,es,c,hR,hSE,hclk,hseg⟩ := hI₀.2
  have hm₀ : c₀.mode=.scan := (PalPeg.GalilOracleLocal.invS_mode hI₀.1.1.1.1.1).1
  have hm : c.mode=.scan := watchSegE_first_mode q first hseg hm₀
  obtain ⟨k,hsh⟩ := watchSegE_shaped centre place entry q first hseg
  have hstart := field_restarted ((PofC centre place entry w).place r) hR hSE hm hclk
  have horig := field_alongShaped centre place entry q first hsh (by rw [hm]; decide) hstart
  exact (field_alongShaped centre place entry q first hs (by rw [hm₀]; decide) horig).ready hmx

end

end PalPeg.CanonicalSearchReady
