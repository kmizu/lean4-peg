import PalPeg.GalilScaffoldWait

set_option autoImplicit false
namespace PalPeg.GalilScaffoldWaitInterrupt
open GalilScaffoldCounter
open GalilScaffoldSearchFinish (State)

/-- Search projection of a scan/idle-chain, non-replay tick. With chain idle,
canShift is false, hence an unequal comparison triggers fallback after advance. -/
def tick (s : State) (clock : ℕ) (available equal : Bool) : State :=
  let compare := available && decide (clock = 1)
  let t := GalilScaffoldSearchRun.advance compare (GalilScaffoldDouble.waitStep true s)
  if compare && !equal then {t with mode := .idle} else t

theorem fallback_idle (s : State) (clock : ℕ) (available equal : Bool)
    (hf : (available && decide (clock = 1) && !equal) = true) :
    (tick s clock available equal).mode = .idle := by simp [tick,hf]

theorem uninterrupted (s : State) (clock : ℕ) (available equal : Bool)
    (hf : (available && decide (clock = 1) && !equal) = false) :
    tick s clock available equal =
      GalilScaffoldSearchRun.advance (available && decide (clock = 1)) (GalilScaffoldDouble.waitStep true s) := by
  simp [tick,hf]

/-- A fallback terminates the wait segment; it does not resume as a wait tick.
The remaining two branches give precisely the wait or double entry invariants. -/
theorem safe_tick (s : State) (clock : ℕ) (available equal : Bool)
    (hm : s.mode = .wait) (hc : Canonical s.debt) (hn : 0 ≤ value s.debt)
    (hclock : 1 ≤ clock ∧ clock ≤ 2048) :
    let t := tick s clock available equal
    let c := (GalilScaffoldMatchClock.run 2048 clock [available]).1
    negative s.debt ≠ true ∧ Canonical t.debt ∧
      (t.mode = .idle ∨ (t.mode = .wait ∧ 0 ≤ value t.debt) ∨
        (t.mode = .double ∧ (0 ≤ value t.debt ∨ (-1 ≤ value t.debt ∧ c = 2048)))) := by
  have hs := GalilScaffoldSearchFinish.debt_guard s hc hn
  cases hz : zero s.debt with
  | false =>
    obtain ⟨htm,htc,htn,_⟩ := GalilScaffoldDouble.wait_positive_advance s
      (available && decide (clock = 1)) hm hc hn hz
    dsimp [tick]
    split
    · exact ⟨hs,htc,Or.inl rfl⟩
    · exact ⟨hs,htc,Or.inr (Or.inl ⟨htm,htn⟩)⟩
  | true =>
    have h := GalilScaffoldDouble.enter_boundary s available true clock hc hz hclock
    simp only [Bool.and_true] at h
    obtain ⟨htm,_,_,_,htc,htn,_⟩ := h
    dsimp [tick]
    rw [GalilScaffoldDouble.wait_enter s hm hz]
    split
    · exact ⟨hs,htc,Or.inl rfl⟩
    · exact ⟨hs,htc,Or.inr (Or.inr ⟨htm,htn⟩)⟩

def nextClock (clock : ℕ) (available : Bool) : ℕ :=
  (GalilScaffoldMatchClock.run 2048 clock [available]).1

inductive Run : State → ℕ → List (Bool × Bool) → State → ℕ → Prop
  | nil (s : State) (c : ℕ) : Run s c [] s c
  | next (s t : State) (c d : ℕ) (a equal : Bool) (es : List (Bool × Bool))
      (hm : s.mode = .wait) (hs : negative s.debt ≠ true)
      (hr : Run (tick s c a equal) (nextClock c a) es t d) :
      Run s c ((a,equal)::es) t d

def Outcome (s : State) (c : ℕ) : Prop :=
  s.mode = .idle ∨ (s.mode = .wait ∧ 0 ≤ value s.debt) ∨
    (s.mode = .double ∧ (0 ≤ value s.debt ∨ (-1 ≤ value s.debt ∧ c = 2048)))

/-- Consume up to the first exit from wait, never treating fallback as a pause. -/
theorem run_prefix (es : List (Bool × Bool)) (s : State) (c : ℕ)
    (hm : s.mode = .wait) (hc : Canonical s.debt) (hn : 0 ≤ value s.debt)
    (hclock : 1 ≤ c ∧ c ≤ 2048) :
    ∃ used rest t d, es = used++rest ∧ Run s c used t d ∧ Canonical t.debt ∧
      (1 ≤ d ∧ d ≤ 2048) ∧ Outcome t d ∧ (rest = [] ∨ t.mode ≠ .wait) := by
  induction es generalizing s c with
  | nil => exact ⟨[],[],s,c,rfl,.nil _ _,hc,hclock,Or.inr (Or.inl ⟨hm,hn⟩),Or.inl rfl⟩
  | cons e es ih =>
    rcases e with ⟨a,equal⟩
    obtain ⟨hsafe,htc,hout⟩ := safe_tick s c a equal hm hc hn hclock
    have hi := GalilScaffoldMatchClock.run_invariant 2048 c [a] (by decide) hclock
    have hd : 1 ≤ nextClock c a ∧ nextClock c a ≤ 2048 := ⟨hi.1,hi.2.1⟩
    by_cases ht : (tick s c a equal).mode = .wait
    · have hnonneg : 0 ≤ value (tick s c a equal).debt := by
        rcases hout with h | h | h
        · simp_all
        · exact h.2
        · simp_all
      obtain ⟨used,rest,t,d,he,hr,htc',hclock',hout',hend⟩ := ih _ _ ht htc hnonneg hd
      exact ⟨(a,equal)::used,rest,t,d,by simp [he],.next s t c d a equal used hm hsafe hr,
        htc',hclock',hout',hend⟩
    · exact ⟨[(a,equal)],es,tick s c a equal,nextClock c a,rfl,
        .next s _ c _ a equal [] hm hsafe (.nil _ _),htc,hd,hout,Or.inr ht⟩

theorem run_clock {s t : State} {c d : ℕ} {es : List (Bool × Bool)}
    (hr : Run s c es t d) : d = (GalilScaffoldMatchClock.run 2048 c (es.map Prod.fst)).1 := by
  induction hr with
  | nil => rfl
  | next s t c d a equal es hm hs hr ih =>
    cases a <;> by_cases he : c = 1 <;>
      simpa [nextClock,GalilScaffoldMatchClock.run,he] using ih

theorem tick_debt (s : State) (c : ℕ) (a equal : Bool) :
    value (tick s c a equal).debt = value s.debt-(if a && decide (c = 1) then 1 else 0) := by
  cases a <;> cases equal <;> by_cases he : c = 1 <;>
    cases hz : zero s.debt <;> by_cases hm : s.mode = .wait <;>
    simp [tick,GalilScaffoldDouble.waitStep,GalilScaffoldDouble.enter,
      GalilScaffoldSearchRun.advance,he,hz,hm,dec_value]

theorem run_debt {s t : State} {c d : ℕ} {es : List (Bool × Bool)}
    (hr : Run s c es t d) :
    value t.debt = value s.debt-(GalilScaffoldMatchClock.run 2048 c (es.map Prod.fst)).2 := by
  induction hr with
  | nil => simp [GalilScaffoldMatchClock.run]
  | next s t c d a equal es hm hs hr ih =>
    rw [tick_debt] at ih
    cases a <;> by_cases he : c = 1 <;>
      simp [nextClock,GalilScaffoldMatchClock.run,he] at ih ⊢ <;> omega

/-- A conservative available-tick budget forces exit, either by fallback or double. -/
theorem supplied_exit (es : List (Bool × Bool)) (s : State) (c k : ℕ)
    (hm : s.mode = .wait) (hc : Canonical s.debt) (hv : value s.debt = (k : ℤ))
    (hclock : 1 ≤ c ∧ c ≤ 2048) (hb : (k+1)*2048 ≤ (es.map Prod.fst).count true) :
    ∃ used rest t d, es = used++rest ∧ Run s c used t d ∧ Canonical t.debt ∧
      (1 ≤ d ∧ d ≤ 2048) ∧ Outcome t d ∧ t.mode ≠ .wait := by
  obtain ⟨used,rest,t,d,he,hr,htc,hd,hout,hend⟩ := run_prefix es s c hm hc (by omega) hclock
  refine ⟨used,rest,t,d,he,hr,htc,hd,hout,?_⟩
  intro hwait
  have hrest : rest = [] := hend.resolve_right (by simpa using hwait)
  have hused : es = used := by simpa [hrest] using he
  have hnonneg : 0 ≤ value t.debt := by
    rcases hout with h | h | h
    · simp_all
    · exact h.2
    · simp_all
  have hdebt := run_debt hr
  have hsup := GalilScaffoldAdvanceClock.eligible_supply 2048 c (k+1) (es.map Prod.fst) (by decide) hclock hb
  rw [GalilScaffoldAdvanceClock.eligible_compares,hused] at hsup
  omega

theorem run_stopped {s t : State} {c d : ℕ} {es : List (Bool × Bool)}
    (hr : Run s c es t d) (hm : s.mode ≠ .wait) : t = s ∧ d = c ∧ es = [] := by
  cases hr with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | next s t c d a equal es hwait hs hr => exact False.elim (hm hwait)

theorem tick_span (s : State) (c : ℕ) (a equal : Bool) (hm : s.mode = .wait)
    (ht : (tick s c a equal).mode ≠ .idle) :
    GalilScaffoldSearchRun.stageSpan (tick s c a equal) = s.span := by
  cases a <;> cases equal <;> by_cases he : c = 1 <;> cases hz : zero s.debt <;>
    simp_all [tick,GalilScaffoldDouble.waitStep,GalilScaffoldDouble.enter,
      GalilScaffoldSearchRun.advance,GalilScaffoldSearchRun.stageSpan]

theorem run_span {s t : State} {c d : ℕ} {es : List (Bool × Bool)}
    (hr : Run s c es t d) (hm : s.mode = .wait) (ht : t.mode ≠ .idle) :
    GalilScaffoldSearchRun.stageSpan t = s.span := by
  induction hr with
  | nil => simp [GalilScaffoldSearchRun.stageSpan,hm]
  | next s t c d a equal es hwait hs hr ih =>
    by_cases hu : (tick s c a equal).mode = .wait
    · have hframe := tick_span s c a equal hwait (by simp [hu])
      have hspan : (tick s c a equal).span = s.span := by
        simpa [GalilScaffoldSearchRun.stageSpan,hu] using hframe
      exact (ih hu ht).trans hspan
    · obtain ⟨he,_,_⟩ := run_stopped hr hu
      subst t
      exact tick_span s c a equal hwait ht

theorem double_work {s t : State} {c d : ℕ} {es : List (Bool × Bool)}
    (hr : Run s c es t d) (hm : s.mode = .wait) (ht : t.mode = .double) :
    t.work = s.span := by
  simpa [GalilScaffoldSearchRun.stageSpan,ht] using run_span hr hm (by simp [ht])

theorem tick_double_reset (s : State) (c : ℕ) (a equal : Bool) (hm : s.mode = .wait)
    (ht : (tick s c a equal).mode = .double) :
    (tick s c a equal).span = reset ∧ (tick s c a equal).quarter = 0 := by
  cases a <;> cases equal <;> by_cases he : c = 1 <;> cases hz : zero s.debt <;>
    simp_all [tick,GalilScaffoldDouble.waitStep,GalilScaffoldDouble.enter,GalilScaffoldSearchRun.advance]

theorem double_reset {s t : State} {c d : ℕ} {es : List (Bool × Bool)}
    (hr : Run s c es t d) (hm : s.mode = .wait) (ht : t.mode = .double) :
    t.span = reset ∧ t.quarter = 0 := by
  induction hr with
  | nil => simp_all
  | next s t c d a equal es hwait hs hr ih =>
    by_cases hu : (tick s c a equal).mode = .wait
    · exact ih hu ht
    · obtain ⟨he,_,_⟩ := run_stopped hr hu
      subst t
      exact tick_double_reset s c a equal hwait ht

#print axioms double_reset
#print axioms double_work
#print axioms supplied_exit
#print axioms run_debt
#print axioms run_clock
#print axioms run_prefix
#print axioms safe_tick
end PalPeg.GalilScaffoldWaitInterrupt
