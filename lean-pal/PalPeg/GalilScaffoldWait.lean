import PalPeg.GalilScaffoldDouble
import PalPeg.GalilScaffoldAdvanceClock

set_option autoImplicit false
namespace PalPeg.GalilScaffoldWait
open GalilScaffoldCounter
open GalilScaffoldSearchFinish (State)

/-- Enabled wait ticks before the zero-debt dispatch. Each assertion is checked
before the outer advance. The zero dispatch itself belongs to Double.enter. -/
inductive Run : State → List Bool → State → Prop
  | nil (s : State) : Run s [] s
  | next (s t : State) (a : Bool) (as : List Bool)
      (hm : s.mode = .wait) (hz : zero s.debt = false) (hsafe : negative s.debt ≠ true)
      (hr : Run (GalilScaffoldSearchRun.advance a (GalilScaffoldDouble.waitStep true s)) as t) :
      Run s (a::as) t

/-- Sufficient advances reach debt zero using a prefix, not a fictitious wait
after zero. Real availability/eligibility and time to supply advances remain external. -/
theorem reaches_zero (as : List Bool) (s : State) (hm : s.mode = .wait)
    (hc : Canonical s.debt) (hn : 0 ≤ value s.debt)
    (hb : value s.debt ≤ (as.count true : ℤ)) :
    ∃ used rest t, as = used++rest ∧ Run s used t ∧ t.mode = .wait ∧
      Canonical t.debt ∧ zero t.debt = true ∧ t.span = s.span := by
  induction as generalizing s with
  | nil =>
    have hz : zero s.debt = true := (zero_iff s.debt hc).mpr (by simp at hb; omega)
    exact ⟨[],[],s,rfl,.nil _,hm,hc,hz,rfl⟩
  | cons a as ih =>
    cases hz : zero s.debt with
    | true => exact ⟨[],a::as,s,rfl,.nil _,hm,hc,hz,rfl⟩
    | false =>
      let u := GalilScaffoldSearchRun.advance a (GalilScaffoldDouble.waitStep true s)
      obtain ⟨hum,huc,hun,hsafe⟩ := GalilScaffoldDouble.wait_positive_advance s a hm hc hn hz
      have hub : value u.debt ≤ (as.count true : ℤ) := by
        cases a <;> simp [u,GalilScaffoldSearchRun.advance,GalilScaffoldDouble.waitStep,hz,dec_value] at hb ⊢ <;> omega
      have hus : u.span = s.span := by
        cases a <;> simp [u,GalilScaffoldSearchRun.advance,GalilScaffoldDouble.waitStep,hz]
      obtain ⟨used,rest,t,he,hr,htm,htc,htz,hts⟩ := ih u hum huc hun hub
      exact ⟨a::used,rest,t,by simp [he],.next s t a used hm hz hsafe hr,htm,htc,htz,hts.trans hus⟩

theorem clock_reaches_zero (bs : List Bool) (s : State) (clock k : ℕ)
    (hm : s.mode = .wait) (hc : Canonical s.debt) (hv : value s.debt = (k : ℤ))
    (hclock : 1 ≤ clock ∧ clock ≤ 2048) (hb : k*2048 ≤ bs.count true) :
    ∃ used rest t,
      GalilScaffoldAdvanceClock.advances 2048 clock (bs.map (fun b => (b,true))) = used++rest ∧
      Run s used t ∧ t.mode = .wait ∧ Canonical t.debt ∧ zero t.debt = true ∧ t.span = s.span := by
  have h := GalilScaffoldAdvanceClock.eligible_supply 2048 clock k bs (by decide) hclock hb
  apply reaches_zero _ s hm hc
  · omega
  · omega

theorem clock_prefix_zero (bs : List Bool) (s : State) (clock k : ℕ)
    (hm : s.mode = .wait) (hc : Canonical s.debt) (hv : value s.debt = (k : ℤ))
    (hclock : 1 ≤ clock ∧ clock ≤ 2048) (hb : k*2048 ≤ bs.count true) :
    ∃ n t, n ≤ bs.length ∧
      Run s (GalilScaffoldAdvanceClock.advances 2048 clock ((bs.take n).map (fun b => (b,true)))) t ∧
      t.mode = .wait ∧ Canonical t.debt ∧ zero t.debt = true ∧ t.span = s.span ∧
      (1 ≤ (GalilScaffoldMatchClock.run 2048 clock (bs.take n)).1 ∧
        (GalilScaffoldMatchClock.run 2048 clock (bs.take n)).1 ≤ 2048) := by
  obtain ⟨used,rest,t,he,hr,htm,htc,htz,hts⟩ := clock_reaches_zero bs s clock k hm hc hv hclock hb
  have hlen := congrArg List.length he
  simp only [GalilScaffoldAdvanceClock.advances_length,List.length_map,List.length_append] at hlen
  have hprefix : GalilScaffoldAdvanceClock.advances 2048 clock
      ((bs.take used.length).map (fun b => (b,true))) = used := by
    rw [List.map_take,GalilScaffoldAdvanceClock.advances_take,he]
    simp
  have hi := GalilScaffoldMatchClock.run_invariant 2048 clock (bs.take used.length) (by decide) hclock
  refine ⟨used.length,t,by omega,?_,htm,htc,htz,hts,hi.1,hi.2.1⟩
  rw [hprefix]
  exact hr

/-- The next enabled wait dispatch uses the clock returned by the same prefix.
Its outer event is supplied separately, including any advance on double entry. -/
theorem clock_prefix_double (bs : List Bool) (s : State) (clock k : ℕ)
    (available eligible : Bool)
    (hm : s.mode = .wait) (hc : Canonical s.debt) (hv : value s.debt = (k : ℤ))
    (hclock : 1 ≤ clock ∧ clock ≤ 2048) (hb : k*2048 ≤ bs.count true) :
    ∃ n u, n ≤ bs.length ∧
      Run s (GalilScaffoldAdvanceClock.advances 2048 clock ((bs.take n).map (fun b => (b,true)))) u ∧
      u.mode = .wait ∧ zero u.debt = true ∧
      let c := (GalilScaffoldMatchClock.run 2048 clock (bs.take n)).1
      let a := available && decide (c = 1) && eligible
      let t := GalilScaffoldSearchRun.advance a (GalilScaffoldDouble.waitStep true u)
      let c' := (GalilScaffoldMatchClock.run 2048 c [available]).1
      t.mode = .double ∧ t.work = s.span ∧ t.span = reset ∧ t.quarter = 0 ∧
        Canonical t.debt ∧ (0 ≤ value t.debt ∨ (-1 ≤ value t.debt ∧ c' = 2048)) ∧
        (1 ≤ c' ∧ c' ≤ 2048) := by
  obtain ⟨n,u,hn,hu,hum,huc,huz,hus,hcnext⟩ := clock_prefix_zero bs s clock k hm hc hv hclock hb
  refine ⟨n,u,hn,hu,hum,huz,?_⟩
  have h := GalilScaffoldDouble.enter_boundary u available eligible
    (GalilScaffoldMatchClock.run 2048 clock (bs.take n)).1 huc huz hcnext
  simpa only [GalilScaffoldDouble.wait_enter u hum huz,hus] using h

/-- Append one event to guarantee the zero-debt dispatch exists. Its actual
availability is read at the stopping index of this same event stream. -/
theorem clock_sequence_double (bs : List Bool) (extra : Bool) (s : State) (clock k : ℕ)
    (hm : s.mode = .wait) (hc : Canonical s.debt) (hv : value s.debt = (k : ℤ))
    (hclock : 1 ≤ clock ∧ clock ≤ 2048) (hb : k*2048 ≤ bs.count true) :
    let events := bs++[extra]
    ∃ n u, n < events.length ∧
      Run s (GalilScaffoldAdvanceClock.advances 2048 clock ((events.take n).map (fun b => (b,true)))) u ∧
      u.mode = .wait ∧ zero u.debt = true ∧
      let c := (GalilScaffoldMatchClock.run 2048 clock (events.take n)).1
      let available := events[n]!
      let a := available && decide (c = 1) && true
      let t := GalilScaffoldSearchRun.advance a (GalilScaffoldDouble.waitStep true u)
      let c' := (GalilScaffoldMatchClock.run 2048 c [available]).1
      t.mode = .double ∧ t.work = s.span ∧ t.span = reset ∧ t.quarter = 0 ∧
        Canonical t.debt ∧ (0 ≤ value t.debt ∨ (-1 ≤ value t.debt ∧ c' = 2048)) ∧
        (1 ≤ c' ∧ c' ≤ 2048) := by
  obtain ⟨n,u,hn,hu,hum,huc,huz,hus,hcnext⟩ := clock_prefix_zero bs s clock k hm hc hv hclock hb
  have htake : (bs++[extra]).take n = bs.take n := by
    simp [List.take_append,Nat.sub_eq_zero_of_le hn]
  refine ⟨n,u,by simp; omega,?_,hum,huz,?_⟩
  · simpa only [htake] using hu
  · have h := GalilScaffoldDouble.enter_boundary u (bs++[extra])[n]! true
        (GalilScaffoldMatchClock.run 2048 clock (bs.take n)).1 huc huz hcnext
    simpa only [htake,GalilScaffoldDouble.wait_enter u hum huz,hus] using h

/-- Decoded Scala Search.active; this does not include the later fallback reset. -/
def active (s : State) : Bool :=
  !(decide (s.mode = .idle) || decide (s.mode = .found) || decide (s.mode = .missed))

def searchEnabled (scanning chainIdle : Bool) (s : State) : Bool :=
  scanning && chainIdle && active s

def advanceGuard (scanning available : Bool) (clock : ℕ) (chainIdle : Bool) (s : State) : Bool :=
  scanning && available && decide (clock = 1) && active s && chainIdle

/-- On a scan/idle-chain wait segment search ticks even when input is unavailable.
After waitStep (including entry to double), every comparison remains eligible. -/
theorem idle_scan_wait_guards (s : State) (available : Bool) (clock : ℕ)
    (hm : s.mode = .wait) :
    searchEnabled true true s = true ∧
      advanceGuard true available clock true (GalilScaffoldDouble.waitStep (searchEnabled true true s) s) =
        (available && decide (clock = 1) && true) := by
  cases hz : zero s.debt <;>
    simp [searchEnabled,advanceGuard,active,hm,GalilScaffoldDouble.waitStep,GalilScaffoldDouble.enter,hz]

theorem not_scanning_guards (s t : State) (available beforeIdle afterIdle : Bool) (clock : ℕ) :
    searchEnabled false beforeIdle s = false ∧ advanceGuard false available clock afterIdle t = false := by
  simp [searchEnabled,advanceGuard]

#print axioms idle_scan_wait_guards
#print axioms clock_sequence_double
#print axioms clock_prefix_double
#print axioms clock_prefix_zero
#print axioms clock_reaches_zero
#print axioms reaches_zero
end PalPeg.GalilScaffoldWait
