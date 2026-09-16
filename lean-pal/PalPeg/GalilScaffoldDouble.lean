import PalPeg.GalilScaffoldSearchRun
import PalPeg.GalilScaffoldMatchClock

set_option autoImplicit false
namespace PalPeg.GalilScaffoldDouble
open GalilScaffoldCounter
open GalilScaffoldSearchFinish (State)

def enter (s : State) : State :=
  {s with mode := .double,work := s.span,span := reset,quarter := 0}

theorem finish_enter (s : State) (hf : s.finalStage = false) (hz : zero s.debt = true) :
    GalilScaffoldSearchFinish.finish s true true 347 = enter s := by
  simp [GalilScaffoldSearchFinish.finish,enter,hf,hz]

/-- The wait dispatcher checks debt before invoking double, as in Scala. -/
def waitStep (enabled : Bool) (s : State) : State :=
  if enabled && decide (s.mode = .wait) && zero s.debt then enter s else s

theorem wait_enter (s : State) (hm : s.mode = .wait) (hz : zero s.debt = true) :
    waitStep true s = enter s := by simp [waitStep,hm,hz]

/-- Covers both run-finish and wait dispatch before the outer compare.
An advance on this boundary makes debt -1 and simultaneously resets the clock. -/
theorem enter_boundary (s : State) (available eligible : Bool) (clock : ℕ)
    (hc : Canonical s.debt) (hz : zero s.debt = true)
    (hclock : 1 ≤ clock ∧ clock ≤ 2048) :
    let a := available && decide (clock = 1) && eligible
    let t := GalilScaffoldSearchRun.advance a (enter s)
    let nextClock := (GalilScaffoldMatchClock.run 2048 clock [available]).1
    t.mode = .double ∧ t.work = s.span ∧ t.span = reset ∧ t.quarter = 0 ∧
      Canonical t.debt ∧ (0 ≤ value t.debt ∨ (-1 ≤ value t.debt ∧ nextClock = 2048)) ∧
      (1 ≤ nextClock ∧ nextClock ≤ 2048) := by
  have hv := (zero_iff s.debt hc).mp hz
  have hnext := GalilScaffoldMatchClock.run_invariant 2048 clock [available] (by decide) hclock
  have hdc := dec_canonical s.debt hc
  cases available <;> cases eligible <;> by_cases he : clock = 1 <;>
    simp_all [GalilScaffoldSearchRun.advance,enter,GalilScaffoldMatchClock.run,dec_value]

theorem wait_positive_advance (s : State) (a : Bool) (hm : s.mode = .wait)
    (hc : Canonical s.debt) (hn : 0 ≤ value s.debt) (hz : zero s.debt = false) :
    let t := GalilScaffoldSearchRun.advance a (waitStep true s)
    t.mode = .wait ∧ Canonical t.debt ∧ 0 ≤ value t.debt ∧ negative s.debt ≠ true := by
  have hv : value s.debt ≠ 0 := by
    intro he
    have := (zero_iff s.debt hc).mpr he
    simp_all
  have hsafe := GalilScaffoldSearchFinish.debt_guard s hc hn
  have hdc := dec_canonical s.debt hc
  cases a <;> simp [waitStep,hz,GalilScaffoldSearchRun.advance,hm,hc,hdc,hsafe,dec_value] <;> omega

/-- quarterEnd samples the old quarter, before the modulo-four update. -/
def step (s : State) : State :=
  {s with work := dec s.work,span := inc (inc s.span),quarter := ⟨(s.quarter.val+1)%4, Nat.mod_lt _ (by decide)⟩,debt := if s.quarter.val = 3 then inc s.debt else s.debt}

theorem step_balance (s : State) :
    4*value (step s).debt+(step s).quarter.val = 4*value s.debt+s.quarter.val+1 := by
  have hq := s.quarter.isLt
  by_cases h : s.quarter.val = 3
  · simp [step,h,inc_value]; omega
  · simp [step,h]
    omega

/-- Positive double ticks only; the zero-work dispatch invokes prepare. -/
inductive Run : State → List Bool → State → Prop
  | stop (s : State) (hm : s.mode = .double) (hz : positive s.work = false) : Run s [] s
  | next (s t : State) (a : Bool) (as : List Bool)
      (hm : s.mode = .double) (hp : positive s.work = true)
      (hr : Run (GalilScaffoldSearchRun.advance a (step s)) as t) : Run s (a::as) t

theorem balance {s t : State} {as : List Bool} (hr : Run s as t) :
    4*value t.debt+t.quarter.val =
      4*value s.debt+s.quarter.val+as.length-4*(as.count true : ℤ) := by
  induction hr with
  | stop => simp
  | next s t a as hm hp hr ih =>
    have hb := step_balance s
    cases a <;> simp [GalilScaffoldSearchRun.advance,dec_value] at ih ⊢ <;> omega

theorem canonical {s t : State} {as : List Bool} (hr : Run s as t)
    (hc : Canonical s.debt) : Canonical t.debt := by
  induction hr with
  | stop => exact hc
  | next s t a as hm hp hr ih =>
    have hstep : Canonical (step s).debt := by
      dsimp [step]
      split
      · exact inc_canonical _ hc
      · exact hc
    apply ih
    cases a
    · exact hstep
    · exact dec_canonical _ hstep

theorem completed_credit {s t : State} {as : List Bool} (hr : Run s as t)
    (hq : s.quarter = 0) (hlen : as.length % 4 = 0) :
    t.quarter = 0 ∧ value t.debt = value s.debt+as.length/4-as.count true := by
  have hb := balance hr
  have htq := t.quarter.isLt
  have hz : t.quarter.val = 0 := by simp [hq] at hb; omega
  refine ⟨Fin.ext hz,?_⟩
  simp [hq,hz] at hb
  omega

theorem complete (as : List Bool) (s : State) (span : ℕ)
    (hm : s.mode = .double) (hw : s.work = ofNat as.length) (hs : s.span = ofNat span) :
    ∃ t, Run s as t ∧ t.mode = .double ∧ t.work = ofNat 0 ∧
      t.span = ofNat (span+2*as.length) := by
  induction as generalizing s span with
  | nil => exact ⟨s,.stop s hm (by simp [hw,positive,ofNat]),hm,hw,by simpa using hs⟩
  | cons a as ih =>
    have hmode : (GalilScaffoldSearchRun.advance a (step s)).mode = .double := by
      cases a <;> simpa [GalilScaffoldSearchRun.advance,step] using hm
    have hwork : (GalilScaffoldSearchRun.advance a (step s)).work = ofNat as.length := by
      cases a <;> simp [GalilScaffoldSearchRun.advance,step,hw,dec_ofNat_succ]
    have hspan : (GalilScaffoldSearchRun.advance a (step s)).span = ofNat (span+2) := by
      cases a <;> simp [GalilScaffoldSearchRun.advance,step,hs,inc_ofNat,Nat.add_assoc]
    obtain ⟨t,hr,htm,htw,hts⟩ := ih _ (span+2) hmode hwork hspan
    refine ⟨t,.next s t a as hm (by simp [hw,positive,ofNat,List.replicate_succ]) hr,htm,htw,?_⟩
    convert hts using 1 <;> congr 1 <;> simp <;> omega

theorem span_of_run {s t : State} {as : List Bool} (hr : Run s as t)
    (n : ℕ) (hs : s.span = ofNat n) : t.span = ofNat (n+2*as.length) := by
  induction hr generalizing n with
  | stop => simpa using hs
  | next s t a as hm hp hr ih =>
    have hspan : (GalilScaffoldSearchRun.advance a (step s)).span = ofNat (n+2) := by
      cases a <;> simp [GalilScaffoldSearchRun.advance,step,hs,inc_ofNat,Nat.add_assoc]
    have h := ih (n+2) hspan
    convert h using 1 <;> congr 1 <;> simp <;> omega

#print axioms span_of_run
#print axioms complete
#print axioms enter_boundary
#print axioms wait_positive_advance
#print axioms completed_credit
#print axioms canonical
end PalPeg.GalilScaffoldDouble
