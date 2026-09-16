import PalPeg.GalilScaffoldChainCatch

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainWatch
open GalilScaffoldCounter

structure State where
  machine : GalilScaffoldChainVerifier.State
  lag : Counter
  margin : Counter

/-- Successful consume with the actual moved verifier and its right guard. -/
def Good (s : State) : Prop :=
  GalilScaffoldChainVerifier.canRight s.machine.verifier ∧
  ∃ a, GalilScaffoldChainConsume.symbol s.machine.control.period.focus = some a ∧
    GalilScaffoldInputHead.read (GalilScaffoldChainVerifier.right s.machine.verifier) = some a

def caught (s : State) : State :=
  ⟨GalilScaffoldChainVerifier.consume s.machine,dec s.lag,s.margin⟩
def queued (s : State) : State := ⟨s.machine,inc s.lag,inc s.margin⟩
def immediate (s : State) : State :=
  ⟨GalilScaffoldChainVerifier.consume s.machine,s.lag,inc s.margin⟩

inductive Internal : State → State → Prop
  | idle (s) (hz : positive s.lag = false) : Internal s s
  | take (s) (hp : positive s.lag = true) (hg : Good s) : Internal s (caught s)

/-- The second phase tests lag after Internal, so one tick can consume
twice. This is the successful fresh-watch/only=false, non-shift branch. -/
inductive Outer : State → Bool → State → Prop
  | idle (s) : Outer s false s
  | queued (s) (hz : zero s.lag = false) : Outer s true (queued s)
  | immediate (s) (hz : zero s.lag = true) (hg : Good s) : Outer s true (immediate s)

inductive Tick : State → Bool → State → Prop
  | step {s m t b} (hi : Internal s m) (ho : Outer m b t) : Tick s b t

def balance (s : State) : ℤ :=
  value s.machine.control.distance + value s.lag - value s.margin

theorem good_distance {s : State} (hg : Good s) :
    value (GalilScaffoldChainVerifier.consume s.machine).control.distance =
      value s.machine.control.distance+1 := by
  obtain ⟨_,a,ht,hr⟩ := hg
  exact (GalilScaffoldChainVerifier.consume_agrees s.machine a ht hr).1

theorem internal_balance {s t : State} (hr : Internal s t) : balance t = balance s := by
  cases hr with
  | idle => rfl
  | take hp hg =>
    have hd := good_distance hg
    simp only [balance, caught, dec_value]
    omega

theorem outer_balance {s t : State} {b : Bool} (hr : Outer s b t) : balance t = balance s := by
  cases hr with
  | idle => rfl
  | queued hz => simp [balance,queued,inc_value]; omega
  | immediate hz hg =>
    have hd := good_distance hg
    simp only [balance,immediate,inc_value]
    omega

theorem tick_balance {s t : State} {b : Bool} (hr : Tick s b t) : balance t = balance s := by
  cases hr with
  | step hi ho => exact (outer_balance ho).trans (internal_balance hi)

inductive Run : State → List Bool → State → Prop
  | stop (s) : Run s [] s
  | next {s m t b bs} (ht : Tick s b m) (hr : Run m bs t) : Run s (b :: bs) t

theorem run_balance {s t : State} {bs : List Bool} (hr : Run s bs t) : balance t = balance s := by
  induction hr with
  | stop => rfl
  | next ht hr ih => exact ih.trans (tick_balance ht)

/-- Once caught up past four semiperiods, margin is nonnegative even
with outer matches interleaved, from the same run's conserved balance. -/
theorem caught_margin {s t : State} {bs : List Bool} (hr : Run s bs t) (h : ℕ)
    (hs : balance s = 4*(h : ℤ)) (hl : value t.lag = 0)
    (hd : 4*(h : ℤ) ≤ value t.machine.control.distance) : 0 ≤ value t.margin := by
  have hb := run_balance hr
  unfold balance at hb
  rw [← hs] at hd
  unfold balance at hd
  omega

def CanonicalState (s : State) : Prop := Canonical s.lag ∧ Canonical s.margin

theorem internal_canonical {s t : State} (hr : Internal s t) (hc : CanonicalState s) :
    CanonicalState t := by
  cases hr with
  | idle => exact hc
  | take hp hg => exact ⟨dec_canonical _ hc.1,hc.2⟩

theorem outer_canonical {s t : State} {b : Bool} (hr : Outer s b t) (hc : CanonicalState s) :
    CanonicalState t := by
  cases hr with
  | idle => exact hc
  | queued hz => exact ⟨inc_canonical _ hc.1,inc_canonical _ hc.2⟩
  | immediate hz hg => exact ⟨hc.1,inc_canonical _ hc.2⟩

theorem run_canonical {s t : State} {bs : List Bool} (hr : Run s bs t) (hc : CanonicalState s) :
    CanonicalState t := by
  induction hr with
  | stop => exact hc
  | next ht hr ih =>
    cases ht with
    | step hi ho => exact ih (outer_canonical ho (internal_canonical hi hc))

theorem prepared_balance (machine : GalilScaffoldChainVerifier.State)
    (hd : value machine.control.distance = 0)
    (radius : Counter) (sm dm : Bool) (bs cs : List Bool) :
    let credits := GalilScaffoldChainCredits.run (GalilScaffoldChainCredits.start radius)
      (GalilScaffoldChainCredits.prepEvents sm dm bs cs)
    balance ⟨machine,credits.lag,credits.margin⟩ = 4*(bs.length : ℤ) := by
  have hm := GalilScaffoldChainCatch.prepared_margin radius sm dm bs cs
  dsimp only at hm
  dsimp only [balance]
  rw [hd,hm]
  omega

theorem shift_ready {s t : State} {bs : List Bool} (hr : Run s bs t)
    (hc : CanonicalState s) (h : ℕ) (hb : balance s = 4*(h : ℤ))
    (hz : zero t.lag = true) (hd : 4*(h : ℤ) ≤ value t.machine.control.distance)
    (hp : t.machine.control.phase = 4) (hn : t.machine.control.broken = false) :
    GalilScaffoldChainCatch.freshShiftGuard t.machine t.lag t.margin = true := by
  have hcan := run_canonical hr hc
  have hl := (zero_iff _ hcan.1).mp hz
  have hm := caught_margin hr h hb hl hd
  have hneg : negative t.margin = false := by
    cases he : negative t.margin
    · rfl
    · have hv := (negative_iff _ hcan.2).mp he
      omega
  simp [GalilScaffoldChainCatch.freshShiftGuard,hz,hp,hn,hneg]

#print axioms shift_ready
#print axioms prepared_balance
#print axioms run_balance
#print axioms caught_margin
end PalPeg.GalilScaffoldChainWatch
