import PalPeg.CloseoutRadPack2
import PalPeg.GalilFinalAssembly2

/-!
# Closing the four premises of `CloseoutRadPack2.h_trailF_of_parts'`

`CloseoutRadPack2` reduced `H_trailF` to four trace-level facts:
`H_radLedger`, `H_shiftOrd`, `H_leftLive`, `H_verSane`.  This file discharges
the two that are pure transport — the radius ledger and the shift budget — and
exhibits the remaining two, together with the shift *entry* budget, as named
hypotheses with their exact types.

What is proved here, unconditionally except for the named hypotheses:

* `coupledPack_trace` — `GalilChainCoupling.Coupled` and `CopyPack` at every
  state of every pre-loaded trace (boot is chain-idle and copy-idle, and both
  travel along `coupled_steps` / `copyPack_steps`).
* `sanePack_trace'` — `GalilTrailSane.SanePack` along the trace, from
  `GalilTrailRad.centreLive_trace` (free) and `H_leftLive` (named).
* `h_radLedger_of_leftLive` — **`H_radLedger` from `H_leftLive` alone.**  All
  five other premises of `CloseoutRadPack.radLedger_tick` (`Coupled`,
  `CentreLive`, `FrontPack`, `Sane R`, `Sane C`, `CopyIdle`) are supplied.
* `h_shiftOrd_of_entry` — **`H_shiftOrd` from `H_shiftEntry` and `H_leftLive`.**
  The `Canonical remaining` premise of `CloseoutRadPack2.shiftOrd_tick` comes
  from the ledger just proved, `Sane C` from `sanePack_trace'`, and `CopyIdle`
  from `coupledPack_trace`.
* `h_trailF_of_named` / `h_trailF_C` — **`H_trailF` from the three named
  hypotheses only.**

## The named residuals, and why they are named

`H_shiftEntry` (task (1)).  At `scan_shift` the landing sets
`remaining := ofNat (periodLength w)`, and `ShiftBud` asks for
`2 · periodLength w + 1 ≤ C − L` and `periodLength w + 1 ≤ R − C` there.  The
intended route is `ScanInvariant` (`L = C − radius`, `R = C + radius`) at the
shift entry together with the shift guard `4h ≤ distance`
(`GalilCatchUpDistance.places_of_guard`, `periodLength w = h`), which gives
`2h + 1 ≤ C − L` and `h + 1 ≤ R − C`.  What is missing is the *trace-level*
`ScanInvariant` at the comparison source `st i`: the scan invariant is not among
the facts `PreTrace` carries, and reconstructing it needs the chain/scan
coupling in a form (`L = C − radius` as an equality, not `≤`) that
`GalilChainCoupling.Coupled` does not record.  So the entry budget is named at
the exact shape `shiftOrd_tick` consumes.

`H_leftLive` (task (2)).  The `L` analogue of
`GalilCentreLive.centreLive_of_invLP_run`.  Its two branches need different
material: at a scan comparison `1 ≤ position L` is the `ScanInvariant` half
(`live_of_scanInvariant`), and at a rewind tick it is the replay-vs-origin bound
of `minv_after_fallback`.  Neither is available as an `InvLP`-indexed run lemma
today, which is what an induction along `Steps` out of the boot tick would need;
`GalilCentreLive` provides that packaging for `C` only.

`H_verSane` (task (3)).  `GalilFrontMono.Sane` is *not* preserved by
`GalilScaffoldChainVerifier.right` unconditionally: at `gap = true` the moved
place is `⟨headRight head, false⟩`, which is sane only when the head really
consumed a cell, i.e. only under `canRight`.  So the intended route — the chain
verifier is planted at `chainStart` as a copy of `C` (`represents_right`) and
only ever moves right (`GalilTrailChain.trails_move1/2`) with
`pos ver ≤ pos R` (`GalilTrailAssembly.lagLe_traceF`) — has to carry the
`canRight` budget along, and that budget is precisely `ChainBudget`, which in
the present development is derived *from* `RadPack` (`chainBudget_of_radPack`).
Breaking that circle is a separate piece of work, so `H_verSane` is named.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutRadPack3

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilThrottledRun PalPeg.GalilTrailProof PalPeg.GalilFinalAssembly
open PalPeg.GalilTrailScan PalPeg.GalilTrailBudget PalPeg.GalilTrailChain
open PalPeg.GalilTrailAssembly PalPeg.GalilTrailRad PalPeg.CloseoutRadPack
open PalPeg.CloseoutRadPack2
open PalPeg.GalilRunSkeleton

/-! ## 1. `Coupled` and `CopyPack` along every pre-loaded trace -/

section Trace
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **The chain coupling and the copy pack at every state of a pre-loaded
trace.**  The boot state is chain-idle (`coupled_of_idle`) and copy-idle
(`copyPack_boot`); both travel along one tick. -/
theorem coupledPack_trace {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : PreTrace centre place entry q first w st Tc) :
    ∀ i, i ≤ Tc w.length →
      PalPeg.GalilChainCoupling.Coupled (st i).ctl (st i).vm ∧
        PalPeg.GalilChainCoupling.CopyPack (st i).ctl (st i).vm := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [hP.start]
    exact ⟨PalPeg.GalilChainCoupling.coupled_of_idle rfl,
      PalPeg.GalilChainCoupling.copyPack_boot 2048 w⟩
  | succ i ih =>
    intro hi
    have hlt : i < Tc w.length := by omega
    have ht := hP.trace.tick i hlt
    obtain ⟨hC, hK⟩ := ih (by omega)
    exact ⟨PalPeg.GalilChainCoupling.coupled_tick (onLetterVM w) leftFirstVM centre place entry
        q first 2048 hC ht,
      PalPeg.GalilChainCoupling.copyPack_tick (onLetterVM w) leftFirstVM centre place entry
        q first 2048 hK ht⟩

/-- `CopyIdle` off `copy` mode, in the shape `radLedger_tick` and
`shiftOrd_tick` ask for. -/
theorem copyIdle_trace {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : PreTrace centre place entry q first w st Tc) :
    ∀ i, i ≤ Tc w.length → (st i).ctl.mode = Mode.shift → CopyIdle (st i).vm :=
  fun i hi hm => (coupledPack_trace centre place entry q first hP i hi).2
    (by rw [hm]; decide)

end Trace

#print axioms coupledPack_trace
#print axioms copyIdle_trace

/-! ## 2. The named hypotheses -/

section Hyps
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(Named) the shift-entry budget.**  Exactly the `hentry` premise of
`CloseoutRadPack2.shiftOrd_tick`, asserted at every comparison source of every
pre-loaded trace.  See the module docstring for why it is not proved here. -/
def H_shiftEntry : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    ∀ i, i ≤ Tc w.length → ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
      beginShiftVM' s'' t'' → ShiftBud t''

end Hyps

/-! ## 3. `SanePack` along the trace, from `H_leftLive` -/

section Sane
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `SanePack` — in particular `Sane C` and `Sane R` — along every pre-loaded
trace, given only the named `H_leftLive`.  `CentreLive` is free
(`GalilTrailRad.centreLive_trace`). -/
theorem sanePack_trace' (hll : H_leftLive centre place entry q first)
    {w : List (Fin 2)} (hw : 0 < w.length) {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : PreTrace centre place entry q first w st Tc) :
    ∀ i, i ≤ Tc w.length → PalPeg.GalilTrailSane.SanePack (st i).ctl (st i).vm :=
  PalPeg.GalilTrailSane.sanePack_trace centre place entry q first hw hP
    (fun i hi => ⟨centreLive_trace centre place entry q first w hw st Tc hP i (Nat.le_of_lt hi),
      hll w hw st Tc hP i (Nat.le_of_lt hi)⟩)

end Sane

#print axioms sanePack_trace'

/-! ## 4. `H_radLedger`, from `H_leftLive` alone -/

section Ledger
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`H_radLedger` from `H_leftLive`.**  Every other premise of
`CloseoutRadPack.radLedger_tick` is discharged: `Coupled` and `CopyIdle` by
`coupledPack_trace`, `CentreLive` and `FrontPack` by
`GalilTrailRad.live_pack_trace`, `Sane R` / `Sane C` by `sanePack_trace'`. -/
theorem h_radLedger_of_leftLive (hll : H_leftLive centre place entry q first) :
    H_radLedger centre place entry q first := by
  intro w hw st Tc hP i
  have hsane := sanePack_trace' centre place entry q first hll hw hP
  induction i with
  | zero => intro _; rw [hP.start]; exact radLedger_boot w
  | succ i ih =>
    intro hi
    have hlt : i < Tc w.length := by omega
    have hle : i ≤ Tc w.length := by omega
    have hlp := live_pack_trace centre place entry q first w hw st Tc hP i hle
    exact radLedger_tick (onLetterVM w) leftFirstVM centre place entry q first 2048
      (ih hle)
      (coupledPack_trace centre place entry q first hP i hle).1
      hlp.1 hlp.2 (hsane i hle).saneR (hsane i hle).saneC
      (copyIdle_trace centre place entry q first hP i hle)
      (hP.trace.tick i hlt)

end Ledger

#print axioms h_radLedger_of_leftLive

/-! ## 5. `H_shiftOrd`, from `H_shiftEntry` and `H_leftLive` -/

section Shift
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`H_shiftOrd` from the shift-entry budget and `H_leftLive`.** -/
theorem h_shiftOrd_of_entry (hen : H_shiftEntry centre place entry q first)
    (hll : H_leftLive centre place entry q first) :
    H_shiftOrd centre place entry q first := by
  have hL := h_radLedger_of_leftLive centre place entry q first hll
  intro w hw st Tc hP i
  have hsane := sanePack_trace' centre place entry q first hll hw hP
  induction i with
  | zero => intro _; rw [hP.start]; exact shiftOrd_boot w
  | succ i ih =>
    intro hi
    have hlt : i < Tc w.length := by omega
    have hle : i ≤ Tc w.length := by omega
    exact shiftOrd_tick (onLetterVM w) leftFirstVM centre place entry q first 2048
      (ih hle) (hL w hw st Tc hP i hle).canonRem (hsane i hle).saneC
      (copyIdle_trace centre place entry q first hP i hle)
      (fun s'' t'' hcmp hb => hen w hw st Tc hP i hle s'' t'' hcmp hb)
      (hP.trace.tick i hlt)

end Shift

#print axioms h_shiftOrd_of_entry

/-! ## 6. `H_trailF` from the three named hypotheses -/

section Final
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`H_trailF` from `H_shiftEntry`, `H_leftLive` and `H_verSane`.**  The
radius ledger and the shift-order budget of `CloseoutRadPack2` are gone. -/
theorem h_trailF_of_named (hen : H_shiftEntry centre place entry q first)
    (hll : H_leftLive centre place entry q first)
    (hv : H_verSane centre place entry q first) :
    H_trailF centre place entry q first :=
  h_trailF_of_parts' centre place entry q first
    (h_radLedger_of_leftLive centre place entry q first hll)
    (h_shiftOrd_of_entry centre place entry q first hen hll)
    hll hv

end Final

#print axioms h_trailF_of_named

/-- **The concrete instance** at `centreC` / `placeC`, as
`GalilFinalAssembly` consumes it. -/
theorem h_trailF_C (entry q : ℕ) (first : Fin 9)
    (hen : H_shiftEntry PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC
      entry q first)
    (hll : H_leftLive PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC
      entry q first)
    (hv : H_verSane PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC
      entry q first) :
    H_trailF PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC entry q first :=
  h_trailF_of_named _ _ entry q first hen hll hv

#print axioms h_trailF_C

end PalPeg.CloseoutRadPack3
