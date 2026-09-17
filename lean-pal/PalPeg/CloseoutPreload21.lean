import PalPeg.CloseoutPreload20

/-!
# The bookkeeping identification: a scan leg's event list *is* the clock trace

`CloseoutPreload19` §4 leaves both of its gaps standing on the same unproved
sentence: *the boolean list a leg consumes really is the firing list of
`GalilScaffoldMatchClock` over that leg's ticks, all of which are available.*
`CloseoutPreload20` supplies `LiveL` from `runTrace`, and
`CloseoutPreload19.prefixPhase_of_clock` supplies `PrefixPhase` from
`GalilScaffoldMatchClock.run` — but both still take the identification as an
input.  This file proves it, on the controller ticks themselves.

* §1 `ScanTrace`: a run of `GalilScaffoldTop.Tick`s all taken in `.scan` mode,
  carrying the actual `Tick` in every constructor together with the two boolean
  lists it determines — `ts`, one entry per tick (`true` = the tick was
  available, i.e. `replaying ∨ F.available`), and `as`, the leg's event list
  (`true` exactly on `scan_match`, the ticks on which a comparison fires and the
  search VM is handed a `true`).  The three constructors are exactly the three
  `Tick` branches that stay in `.scan`: `scan_wait`, `scan_count`, `scan_match`
  (`scan_shift`/`scan_fallback` leave the mode, so a leg cannot contain them).
* §2 the identification `scanTrace_eq_runTrace : as = runTrace delay clock ts`,
  by induction on the trace — the three branches line up one-for-one with the
  three cases of `CloseoutPreload20.runTrace`.  With real-time input supply
  (`GalilScaffoldChainInputSupply`: a fresh symbol every tick, so `F.available`
  always holds) `scanTrace_all_avail` shows `ts` is all `true`, which is the
  second half of the identification.
* §3 discharges the hypotheses of `CloseoutPreload20.wait_leg_length_le_of_clock`
  and `CloseoutPreload19.prefixPhase_of_clock` from a `ScanTrace` alone.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload21

open PalPeg
open PalPeg.GalilScaffoldController (Control)
open PalPeg.GalilScaffoldTop (Frame State Tick)
open PalPeg.GalilScaffoldChainInputSupply (SearchVM)
open PalPeg.GalilScaffoldSearchFinish (Mode)
open PalPeg.GalilScaffoldCounter (Canonical value zero)
open PalPeg.CloseoutPreload14 (WaitTrace)
open PalPeg.CloseoutPreload18 (PrefixPhase)
open PalPeg.CloseoutPreload19 (LiveL prefixPhase_of_clock)
open PalPeg.CloseoutPreload20 (runTrace runTrace_length runTrace_count
  liveL_of_clock wait_leg_length_le_of_clock)

variable {σ : Type}

/-! ## 1. A scan leg of controller ticks, with its two boolean lists -/

/-- **NAMED — a scan leg.**  Consecutive `GalilScaffoldTop.Tick`s, each taken in
`.scan` mode, indexed by the availability list `ts` and the event list `as`.
Every constructor carries the `Tick` itself, so a `ScanTrace` is literally a run
of the machine; the booleans are read off the branch taken. -/
inductive ScanTrace (F : Frame σ) (delay : ℕ) :
    List Bool → List Bool → State σ → State σ → Prop
  | nil (p : State σ) : ScanTrace F delay [] [] p p
  | wait (c : Control) (s s' : σ) (ts as : List Bool) (q : State σ)
      (ht : Tick F delay ⟨c, s⟩ ⟨c, s'⟩)
      (hm : c.mode = .scan)
      (hav : c.replaying = false ∧ ¬ F.available s)
      (hr : ScanTrace F delay ts as ⟨c, s'⟩ q) :
      ScanTrace F delay (false :: ts) (false :: as) ⟨c, s⟩ q
  | count (c : Control) (s s' : σ) (ts as : List Bool) (q : State σ)
      (ht : Tick F delay ⟨c, s⟩ ⟨{c with clock := c.clock - 1}, s'⟩)
      (hm : c.mode = .scan)
      (hav : c.replaying = true ∨ F.available s) (hc : 1 < c.clock)
      (hr : ScanTrace F delay ts as ⟨{c with clock := c.clock - 1}, s'⟩ q) :
      ScanTrace F delay (true :: ts) (false :: as) ⟨c, s⟩ q
  | fire (c : Control) (s s'' : σ) (o : Bool) (rp : Bool) (ts as : List Bool)
      (q : State σ)
      (ht : Tick F delay ⟨c, s⟩ ⟨{c with clock := delay, output := o, replaying := rp}, s''⟩)
      (hm : c.mode = .scan)
      (hav : c.replaying = true ∨ F.available s) (hc : c.clock = 1)
      (hr : ScanTrace F delay ts as
        ⟨{c with clock := delay, output := o, replaying := rp}, s''⟩ q) :
      ScanTrace F delay (true :: ts) (true :: as) ⟨c, s⟩ q

/-- The two lists of a scan leg have the same length: one entry per tick. -/
theorem scanTrace_length {F : Frame σ} {delay : ℕ} {ts as : List Bool}
    {p q : State σ} (h : ScanTrace F delay ts as p q) : as.length = ts.length := by
  induction h with
  | nil => rfl
  | wait _ _ _ _ _ _ _ _ _ _ ih => simpa using ih
  | count _ _ _ _ _ _ _ _ _ _ _ ih => simpa using ih
  | fire _ _ _ _ _ _ _ _ _ _ _ _ _ ih => simpa using ih

#print axioms scanTrace_length

/-! ## 2. The identification -/

/-- **NAMED — the bookkeeping identification `CloseoutPreload19` §4 asks for.**
The event list of a scan leg *is* the firing trace of the match clock over the
leg's ticks, started at the clock the leg enters with.  The three `Tick`
branches that stay in `.scan` match the three cases of `runTrace` exactly:
`scan_wait` leaves the clock alone and emits `false` on an unavailable tick,
`scan_count` decrements it (available, clock ≠ 1, `false`), `scan_match` fires
and rewinds it to `delay` (available, clock = 1, `true`). -/
theorem scanTrace_eq_runTrace {F : Frame σ} {delay : ℕ} {ts as : List Bool}
    {p q : State σ} (h : ScanTrace F delay ts as p q) :
    as = runTrace delay p.ctl.clock ts := by
  induction h with
  | nil p => rfl
  | wait c s s' ts as q ht hm hav hr ih =>
      simpa [runTrace] using congrArg (fun l => false :: l) ih
  | count c s s' ts as q ht hm hav hc hr ih =>
      have hne : c.clock ≠ 1 := by omega
      simp only [runTrace, hne, if_false]
      simpa using congrArg (fun l => false :: l) ih
  | fire c s s'' o rp ts as q ht hm hav hc hr ih =>
      simp only [runTrace, hc]
      simpa using congrArg (fun l => true :: l) ih

#print axioms scanTrace_eq_runTrace

/-- **NAMED — real-time input supply makes every tick of a leg available.**
`GalilScaffoldChainInputSupply` delivers one fresh symbol per tick, so
`F.available` holds throughout; the `scan_wait` branch is then unreachable and
the availability list of any scan leg is all `true`.  This is the second half of
the identification, and the hypothesis `CloseoutPreload20.liveL_of_clock` and
`CloseoutPreload19.prefixPhase_of_clock` both take as input. -/
theorem scanTrace_all_avail {F : Frame σ} {delay : ℕ} {ts as : List Bool}
    {p q : State σ} (h : ScanTrace F delay ts as p q)
    (hsupply : ∀ s : σ, F.available s) : ∀ b ∈ ts, b = true := by
  induction h with
  | nil => intro b hb; simp at hb
  | wait c s s' ts as q ht hm hav hr ih => exact absurd (hsupply s) hav.2
  | count c s s' ts as q ht hm hav hc hr ih =>
      intro b hb
      rcases List.mem_cons.mp hb with hb | hb
      · exact hb
      · exact ih b hb
  | fire c s s'' o rp ts as q ht hm hav hc hr ih =>
      intro b hb
      rcases List.mem_cons.mp hb with hb | hb
      · exact hb
      · exact ih b hb

#print axioms scanTrace_all_avail

/-- The packaged form: a scan leg run under real-time supply, entered in phase,
exhibits its event list as an all-available clock trace. -/
theorem scanTrace_is_runTrace {F : Frame σ} {delay : ℕ} {ts as : List Bool}
    {p q : State σ} (h : ScanTrace F delay ts as p q)
    (hsupply : ∀ s : σ, F.available s)
    (h1 : 1 ≤ p.ctl.clock) (h2 : p.ctl.clock ≤ delay) :
    ∃ (ts' : List Bool) (clock : ℕ), (∀ b ∈ ts', b = true) ∧ 1 ≤ clock ∧
      clock ≤ delay ∧ as = runTrace delay clock ts' :=
  ⟨ts, p.ctl.clock, scanTrace_all_avail h hsupply, h1, h2, scanTrace_eq_runTrace h⟩

#print axioms scanTrace_is_runTrace

/-- The liveness clause of `CloseoutPreload19`, straight from a scan leg. -/
theorem liveL_of_scanTrace {F : Frame σ} {delay : ℕ} {ts as : List Bool}
    {p q : State σ} (h : ScanTrace F delay ts as p q)
    (hsupply : ∀ s : σ, F.available s) (hd : 0 < delay)
    (h1 : 1 ≤ p.ctl.clock) (h2 : p.ctl.clock ≤ delay) : LiveL delay as := by
  rw [scanTrace_eq_runTrace h]
  exact liveL_of_clock delay p.ctl.clock hd h1 h2 ts (scanTrace_all_avail h hsupply)

#print axioms liveL_of_scanTrace

/-! ## 3. Both gaps of `CloseoutPreload19` §4, discharged from the machine -/

/-- **NAMED — gap (b), unconditional in the leg.**  A `.wait` leg whose event
list is the event list of a scan leg of the controller (same booleans, which is
what `searchStep` consumes) lasts at most `2048 * (debt + 1)` ticks: no liveness
clause and no clock trace need be assumed, only that the leg is a run of
`GalilScaffoldTop.Tick` under real-time input supply, entered in phase. -/
theorem wait_leg_length_le_of_scan {F : Frame σ} {ts as : List Bool}
    {p q : State σ} {v t : SearchVM} {debt : ℕ}
    (hr : WaitTrace as v t) (hmt : t.search.mode = Mode.wait)
    (hz : zero t.search.debt = true) (hc : Canonical t.search.debt)
    (hdv : value v.search.debt = (debt : ℤ))
    (hsc : ScanTrace F 2048 ts as p q)
    (hsupply : ∀ s : σ, F.available s)
    (h1 : 1 ≤ p.ctl.clock) (h2 : p.ctl.clock ≤ 2048) :
    as.length ≤ 2048 * (debt + 1) :=
  wait_leg_length_le_of_clock hr hmt hz hc hdv h1 h2
    (scanTrace_all_avail hsc hsupply) (scanTrace_eq_runTrace hsc)

#print axioms wait_leg_length_le_of_scan

/-- **NAMED — gap (a), unconditional in the leg.**  The event list of a scan leg
of the controller is phase-bounded: `PrefixPhase` needs no separate
identification with the clock's firing list, because `scanTrace_eq_runTrace`
*is* that identification. -/
theorem prefixPhase_of_scan {F : Frame σ} {ts as : List Bool} {p q : State σ}
    (hsc : ScanTrace F 2048 ts as p q) (hsupply : ∀ s : σ, F.available s)
    (h1 : 1 ≤ p.ctl.clock) (h2 : p.ctl.clock ≤ 2048) : PrefixPhase as := by
  have heq := scanTrace_eq_runTrace hsc
  refine prefixPhase_of_clock (clock := p.ctl.clock) h1 h2
    (scanTrace_all_avail hsc hsupply) ?_ ?_
  · rw [heq]; exact runTrace_length 2048 p.ctl.clock ts
  · rw [heq]; exact runTrace_count 2048 p.ctl.clock ts

#print axioms prefixPhase_of_scan

/-!
## 4. What is left

`ScanTrace` is a run of `GalilScaffoldTop.Tick` and nothing else, so §3 closes
both gaps of `CloseoutPreload19` §4 at the level of the controller.  Two
interface obligations remain, both outside this file:

* that the boolean a `.wait`/`.run` leg's `searchStep` consumes on a tick is the
  same boolean `ScanTrace` records for that tick (here they are *the same list*
  `as` by hypothesis — the coupling itself lives in `GalilScaffoldTopScan`);
* that `∀ s, F.available s` is what `GalilScaffoldChainInputSupply`'s
  `SoundScanNR raw` `StepsAll` delivers for the concrete frame, and that a leg is
  entered with `1 ≤ clock ≤ 2048` (`BoundedControl`).

**無条件 PAL ∈ PEG は未完.**
-/

end PalPeg.CloseoutPreload21
