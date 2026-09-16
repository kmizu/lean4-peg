import PalPeg.CloseoutLPack5

/-!
# `CloseoutLPack6`: the trail bridge, pointwise

`CloseoutLPack5.H_trailI` is the one remaining *bridge* hypothesis of
`pal_in_peg_final5`: from `IPack` at every tick of **one** chosen trace, the
trailing invariant `GalilTrailProof.TrailF` at every tick of that trace.

It was named there for a purely structural reason.  The existing chain

```
CloseoutLPack.h_trailF_final
  ← CloseoutRadPack4.h_trailF_of_named'
  ← CloseoutRadPack3.h_trailF_of_named
  ← CloseoutRadPack2.h_trailF_of_parts'
  ← GalilTrailRad.h_trailF_of_radPack
  ← GalilTrailScan.h_trailF_of_parts
```

is a chain of `∀ w st Tc, PreTrace → …` implications, so none of its links can
be instantiated at a single trace: the hypothesis `CloseoutLPack.H_lpack` that
feeds it is itself universally quantified, while what the construction of
`CloseoutLPack5.checkpoints_costI_upto1` produces is `IPack` on *its* trace only.

This file re-runs that whole chain **pointwise**.  The essential observation is
that every genuinely inductive ingredient is already trace-local: all of

* `CloseoutRadPack.radLedger_tick`, `CloseoutRadPack2.shiftOrd_tick`,
  `CloseoutRadPack4.saneTick`, `GalilTrailBudget.scanT_tick'`
  (one tick, no trace predicate at all);
* `GalilTrailSane.sanePack_trace`, `GalilTrailOrder.order_trace`,
  `GalilTrailRad.live_pack_trace`, `GalilTrailRad.lagLe_traceF`,
  `GalilTrailAssembly.verF_trace`, `GalilTrailBudget.scanT_trace'`,
  `GalilTrailBudget.placeR_of_preTrace`, `CloseoutRadPack3.coupledPack_trace`
  (a fixed `hP`, with pointwise side hypotheses),

take the trace as a parameter.  Only the *wrappers* were `∀`-shaped.  So §1–§5
below rebuild, at one fixed `w`, `st`, `Tc`, `hP`:

1. `LeftLive` / `SanePack` from `IPack` (§1);
2. the shift-entry budget `ShiftBud` from `IPack.shift` — the `2h ≤ rad` the old
   `CloseoutLPack.H_shiftHalf` assumed is *derived* here from the two shift-entry
   fields `ShiftLocal.guard` (`4h ≤ distance`) and `ShiftLocal.coupled`
   (`distance ≤ 2·rad`), which is the point of carrying them in the pack (§2);
3. `RadLedger`, `ShiftOrd`, `SaneVer` by the three tick inductions, hence
   `GalilTrailRad.RadPack` at every tick (§3);
4. `ScanT` and `VerF` at every tick before checkpoint `m+1` (§4);
5. `TrailF`, i.e. `CloseoutLPack5.H_trailI` (§5).

`pal_in_peg_final6` is then `CloseoutLPack5.pal_in_peg_final5` with `H_trailI`
discharged: three hypotheses become two.

## What is still NAMED, and why

* `H_bootI` (`CloseoutLPack5`) is **reduced**, not proved: §6 shows it follows
  from `BootIPack`, which asks for `IPack` at exactly two states — the boot
  state and the single `init` landing of `GalilFinalAssembly4.invLPC_init`.  No
  run-level content is left in it.  `LPack` at the boot state is
  `CloseoutLPack.lpack_boot` (vacuous: `init` mode); what is genuinely not free
  is `ShiftLocal` there (a `compare` out of the boot VM is not excluded by the
  controller being in `init` mode, since `compare` constrains the VM only) and
  `LPack` at the landing (whose `minv` field is the centre invariant).
* `H_oracleI` and `H_realizeLI'` are untouched: they are the run-level and the
  local-realization halves, not the trail bridge.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutLPack6

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilThrottledRun PalPeg.GalilTrailProof PalPeg.GalilFinalAssembly
open PalPeg.CloseoutRadPack PalPeg.CloseoutRadPack2 PalPeg.CloseoutRadPack3
open PalPeg.CloseoutRadPack4 PalPeg.CloseoutLPack
open PalPeg.CloseoutLPack5
open PalPeg.GalilTrailScan PalPeg.GalilTrailBudget PalPeg.GalilTrailChain
open PalPeg.GalilTrailAssembly PalPeg.GalilTrailRad
open PalPeg.GalilRunSkeleton PalPeg.GalilCheckpoints
open PalPeg.GalilFinalAssembly2 PalPeg.GalilFinalAssembly4
open PalPeg.GalilLookRefined PalPeg.GalilFinalBaseNeed

/-! ## 1. `LeftLive` and `SanePack`, pointwise -/

section Pointwise
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `LeftLive` at every tick, read off the pack state by state. -/
theorem leftLive_pt {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hIP : ∀ i, i ≤ Tc w.length → IPack centre place entry q first w (st i)) :
    ∀ i, i ≤ Tc w.length → PalPeg.GalilTrailSane.LeftLive (st i).ctl (st i).vm :=
  fun i hi => leftLive_of_lpack (hIP i hi).pack

/-- **`CloseoutRadPack3.sanePack_trace'`, pointwise.** -/
theorem sanePack_pt {w : List (Fin 2)} (hw : 0 < w.length) {st : ℕ → State GalilVM}
    {Tc : ℕ → ℕ} (hP : PreTrace centre place entry q first w st Tc)
    (hll : ∀ i, i ≤ Tc w.length → PalPeg.GalilTrailSane.LeftLive (st i).ctl (st i).vm) :
    ∀ i, i ≤ Tc w.length → PalPeg.GalilTrailSane.SanePack (st i).ctl (st i).vm :=
  PalPeg.GalilTrailSane.sanePack_trace centre place entry q first hw hP
    (fun i hi => ⟨centreLive_trace centre place entry q first w hw st Tc hP i (Nat.le_of_lt hi),
      hll i (Nat.le_of_lt hi)⟩)

end Pointwise

#print axioms leftLive_pt
#print axioms sanePack_pt

/-! ## 2. The shift-entry budget, from the pack's shift half

This is where carrying `ShiftLocal` in `IPack` pays for itself: the Galil
half-bound `2h ≤ rad`, which `CloseoutLPack.H_shiftHalf` *assumed*, is here an
arithmetic consequence of the guard's `4h ≤ distance` and the chain/scan
coupling's `distance ≤ 2·rad`.
-/

section ShiftEntry
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **The Galil half-bound at one state.**  `4h ≤ distance ≤ 2·rad` gives
`2h ≤ rad`. -/
theorem halfBound_of_ipack {w : List (Fin 2)} {x : State GalilVM}
    (hx : IPack centre place entry q first w x) {s'' t'' : GalilVM}
    (hcmp : (galilFrameS (PofC centre place entry w) q first).compare x.vm s'')
    (hb : beginShiftVM' s'' t'') :
    ∃ rad : ℕ,
      ScanInvariant w (position x.vm.center) rad x.vm.left x.vm.right ∧
      GalilScaffoldChainVerifier.canRight x.vm.right ∧
      ∀ wch : GalilScaffoldChainWatch.State, s''.chain = .watch wch →
        2 * periodLength wch ≤ rad := by
  obtain ⟨hmode, hrep⟩ := hx.shift.mode s'' t'' hcmp hb
  obtain ⟨rad, hscan⟩ := hx.pack.scanInv hmode hrep
  refine ⟨rad, hscan, hx.shift.move s'' t'' hcmp hb, fun wch hch => ?_⟩
  have h4 : 4 * (periodLength wch : ℤ) ≤
      GalilScaffoldCounter.value wch.machine.control.distance :=
    hx.shift.guard s'' t'' hcmp hb wch hch
  have h2 : GalilScaffoldCounter.value wch.machine.control.distance ≤ 2 * (rad : ℤ) :=
    hx.shift.coupled s'' t'' hcmp hb wch hch rad hscan
  omega

/-- **`CloseoutRadPack3.H_shiftEntry`, pointwise.** -/
theorem shiftEntry_pt {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hIP : ∀ i, i ≤ Tc w.length → IPack centre place entry q first w (st i)) :
    ∀ i, i ≤ Tc w.length → ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
      beginShiftVM' s'' t'' → ShiftBud t'' := by
  intro i hi s'' t'' hcmp hb
  obtain ⟨rad, hscan, hcan, hh⟩ :=
    halfBound_of_ipack centre place entry q first (hIP i hi) hcmp hb
  exact shiftBud_of_scanInv (onLetterVM w) leftFirstVM centre place entry q first
    hscan hcan hcmp hb hh

/-- **`CloseoutRadPack4.H_shiftVerSane`, pointwise.** -/
theorem shiftVerSane_pt {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hIP : ∀ i, i ≤ Tc w.length → IPack centre place entry q first w (st i)) :
    ∀ i, i ≤ Tc w.length → ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
      beginShiftVM' s'' t'' → SaneVer t''.chain :=
  fun i hi s'' t'' hcmp hb =>
    saneVer_beginShift hb ((hIP i hi).shift.ver s'' t'' hcmp hb)

end ShiftEntry

#print axioms halfBound_of_ipack
#print axioms shiftEntry_pt
#print axioms shiftVerSane_pt

/-! ## 3. `RadPack` at every tick, pointwise -/

section RadPackPt
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`CloseoutRadPack3.h_radLedger_of_leftLive`, pointwise.** -/
theorem radLedger_pt {w : List (Fin 2)} (hw : 0 < w.length) {st : ℕ → State GalilVM}
    {Tc : ℕ → ℕ} (hP : PreTrace centre place entry q first w st Tc)
    (hll : ∀ i, i ≤ Tc w.length → PalPeg.GalilTrailSane.LeftLive (st i).ctl (st i).vm) :
    ∀ i, i ≤ Tc w.length → RadLedger (st i).ctl (st i).vm := by
  have hsane := sanePack_pt centre place entry q first hw hP hll
  intro i
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

/-- **`CloseoutRadPack3.h_shiftOrd_of_entry`, pointwise.** -/
theorem shiftOrd_pt {w : List (Fin 2)} (hw : 0 < w.length) {st : ℕ → State GalilVM}
    {Tc : ℕ → ℕ} (hP : PreTrace centre place entry q first w st Tc)
    (hll : ∀ i, i ≤ Tc w.length → PalPeg.GalilTrailSane.LeftLive (st i).ctl (st i).vm)
    (hen : ∀ i, i ≤ Tc w.length → ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
      beginShiftVM' s'' t'' → ShiftBud t'') :
    ∀ i, i ≤ Tc w.length → ShiftOrd (st i).ctl (st i).vm := by
  have hsane := sanePack_pt centre place entry q first hw hP hll
  have hL := radLedger_pt centre place entry q first hw hP hll
  intro i
  induction i with
  | zero => intro _; rw [hP.start]; exact shiftOrd_boot w
  | succ i ih =>
    intro hi
    have hlt : i < Tc w.length := by omega
    have hle : i ≤ Tc w.length := by omega
    exact shiftOrd_tick (onLetterVM w) leftFirstVM centre place entry q first 2048
      (ih hle) (hL i hle).canonRem (hsane i hle).saneC
      (copyIdle_trace centre place entry q first hP i hle)
      (fun s'' t'' hcmp hb => hen i hle s'' t'' hcmp hb)
      (hP.trace.tick i hlt)

/-- **`CloseoutRadPack4.h_verSane_of_shift`, pointwise.** -/
theorem verSane_pt {w : List (Fin 2)} (hw : 0 < w.length) {st : ℕ → State GalilVM}
    {Tc : ℕ → ℕ} (hP : PreTrace centre place entry q first w st Tc)
    (hll : ∀ i, i ≤ Tc w.length → PalPeg.GalilTrailSane.LeftLive (st i).ctl (st i).vm)
    (hsv : ∀ i, i ≤ Tc w.length → ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
      beginShiftVM' s'' t'' → SaneVer t''.chain) :
    ∀ i, i ≤ Tc w.length → ∀ p, verOf (st i).vm.chain = some p →
      GalilFrontMono.Sane p := by
  have hsane := sanePack_pt centre place entry q first hw hP hll
  intro i
  induction i with
  | zero => intro _; rw [hP.start]; exact saneVer_idle
  | succ i ih =>
    intro hi
    have hlt : i < Tc w.length := by omega
    have hle : i ≤ Tc w.length := by omega
    exact saneTick (onLetterVM w) leftFirstVM centre place entry q first 2048
      (ih hle) (hsane i hle).saneC
      (fun s'' t'' hcmp hb => hsv i hle s'' t'' hcmp hb)
      (hP.trace.tick i hlt)

/-- **`GalilTrailRad.RadPack` at every tick, from the pack.**  This is the
pointwise counterpart of `CloseoutRadPack2.h_radPack_of_parts` composed with
`CloseoutRadPack3`/`CloseoutRadPack4` and `CloseoutLPack`. -/
theorem radPack_pt {w : List (Fin 2)} (hw : 0 < w.length) {st : ℕ → State GalilVM}
    {Tc : ℕ → ℕ} (hP : PreTrace centre place entry q first w st Tc)
    (hIP : ∀ i, i ≤ Tc w.length → IPack centre place entry q first w (st i)) :
    ∀ i, i ≤ Tc w.length → RadPack (st i).ctl (st i).vm := by
  have hll := leftLive_pt centre place entry q first hIP
  have hen := shiftEntry_pt centre place entry q first hIP
  have hsv := shiftVerSane_pt centre place entry q first hIP
  have hL := radLedger_pt centre place entry q first hw hP hll
  have hS := shiftOrd_pt centre place entry q first hw hP hll hen
  have hV := verSane_pt centre place entry q first hw hP hll hsv
  exact fun i hi => radPack_of_parts (hL i hi) (hS i hi) (hll i hi) (hV i hi)

end RadPackPt

#print axioms radLedger_pt
#print axioms shiftOrd_pt
#print axioms verSane_pt
#print axioms radPack_pt

/-! ## 4. `ScanT` and `VerF`, pointwise -/

section ScanVer
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`GalilTrailBudget.h_trailScan_of_residuals`, pointwise.**  `HeadsOK` from
`SanePack`, the head order (`GalilTrailOrder.order_trace` with the budget read
off `RadPack`) and the proved place bound on `R`. -/
theorem scanT_pt {w : List (Fin 2)} (hw : 0 < w.length) {st : ℕ → State GalilVM}
    {Tc : ℕ → ℕ} (hP : PreTrace centre place entry q first w st Tc)
    (hrad : ∀ i, i ≤ Tc w.length → RadPack (st i).ctl (st i).vm)
    (hsane : ∀ i, i ≤ Tc w.length → PalPeg.GalilTrailSane.SanePack (st i).ctl (st i).vm)
    {m : ℕ} (hm : m < w.length) :
    ∀ i, i ≤ Tc (m+1) → ScanT w m (st i) := by
  have hle : Tc (m+1) ≤ Tc w.length := hP.mono (m+1) w.length (by omega) le_rfl
  have hord : ∀ i, i ≤ Tc w.length →
      position (st i).vm.left ≤ position (st i).vm.right ∧
      position (st i).vm.center ≤ position (st i).vm.right := by
    intro i hi
    exact PalPeg.GalilTrailOrder.order_head_bounds
      (PalPeg.GalilTrailOrder.order_trace centre place entry q first hP
        (fun j hj => orderBudget_of_radPack (hrad j (Nat.le_of_lt hj))
          (frontPack_trace centre place entry q first w hw st Tc hP j (Nat.le_of_lt hj)))
        i hi)
  have hpr := placeR_of_preTrace centre place entry q first
    (PalPeg.GalilTrailFront.h_frontTrace centre place entry q first) hw hP hm
  refine scanT_trace' centre place entry q first hP hm (fun i hi => ?_)
  have hs := hsane i (by omega)
  have ho := hord i (by omega)
  exact ⟨hs.saneL, hs.saneC, hs.saneR, by have := hpr i hi; omega,
    by have := hpr i hi; omega, hpr i hi⟩

/-- **`GalilTrailRad.chainBudget_of_radPack`, pointwise.** -/
theorem chainBudget_pt {w : List (Fin 2)} (hw : 0 < w.length) {st : ℕ → State GalilVM}
    {Tc : ℕ → ℕ} (hP : PreTrace centre place entry q first w st Tc)
    (hrad : ∀ i, i ≤ Tc w.length → RadPack (st i).ctl (st i).vm)
    (hsane : ∀ i, i ≤ Tc w.length → PalPeg.GalilTrailSane.SanePack (st i).ctl (st i).vm)
    {m : ℕ} (hm : m < w.length) :
    ∀ i, i ≤ Tc (m+1) → ChainBudget m (st i).vm.chain := by
  have hle : Tc (m+1) ≤ Tc w.length := hP.mono (m+1) w.length (by omega) le_rfl
  have hplace := placeR_of_preTrace centre place entry q first
    (PalPeg.GalilTrailFront.h_frontTrace centre place entry q first) hw hP hm
  have hstep : ∀ i, i < Tc (m+1) → LagStepF (st i).ctl (st i).vm := fun i hi =>
    lagStepF_of_radPack (hrad i (by omega))
      (frontPack_trace centre place entry q first w hw st Tc hP i (by omega))
      (hsane i (by omega)).saneR
  exact fun i hi =>
    chainBudget_of_lagLe (lagLe_traceF centre place entry q first hP hm hstep i hi)
      (lagAt_of_radPack (hrad i (by omega)) (hplace i hi))

end ScanVer

#print axioms scanT_pt
#print axioms chainBudget_pt

/-! ## 5. `H_trailI` -/

section Trail
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`TrailF` at every tick of a packed trace.**  The pointwise counterpart of
`GalilTrailScan.h_trailF_of_parts` ∘ `GalilTrailRad.h_trailF_of_radPack`. -/
theorem trailF_pt {w : List (Fin 2)} (hw : 0 < w.length) {st : ℕ → State GalilVM}
    {Tc : ℕ → ℕ} (hP : PreTrace centre place entry q first w st Tc)
    (hIP : ∀ i, i ≤ Tc w.length → IPack centre place entry q first w (st i))
    {m : ℕ} (hm : m < w.length) :
    ∀ i, i ≤ Tc (m+1) → TrailF w m (st i) := by
  have hll := leftLive_pt centre place entry q first hIP
  have hsane := sanePack_pt centre place entry q first hw hP hll
  have hrad := radPack_pt centre place entry q first hw hP hIP
  have hscan := scanT_pt centre place entry q first hw hP hrad hsane hm
  have hB := chainBudget_pt centre place entry q first hw hP hrad hsane hm
  have hV := verF_trace centre place entry q first hP hm hscan hB
  exact fun i hi => trailF_of_scanT (hscan i hi) (hV i hi).ver (hV i hi).lagPos

/-- **`CloseoutLPack5.H_trailI` is a theorem.**  The pointwise trail bridge, in
exactly the shape `CloseoutLPack5.needI'_le` consumes. -/
theorem h_trailI : H_trailI centre place entry q first :=
  fun _ hw _ _ hP hIP _ hm i hi =>
    trailF_pt centre place entry q first hw hP hIP hm i hi

end Trail

#print axioms trailF_pt
#print axioms h_trailI

/-! ## 6. `H_bootI`, reduced to two states -/

section Boot
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) the pack at the two boot states.**  All that is left of
`CloseoutLPack5.H_bootI` once `GalilFinalAssembly4.invLPC_init` supplies the run:
`IPack` at the boot state and at the `init` landing.  `CloseoutLPack.lpack_boot`
gives the `LPack` half at the boot state; what is not free is `ShiftLocal` there
(a `compare` out of the boot VM is a condition on the VM, which the `init`
controller does not rule out) and `LPack` at the landing, whose `minv` field is
the centre invariant (`GalilInvPlus3.invLPS_of_inv` / `minv_of_leftmost` on the
state `GalilTrailFront.inv_of_boot_tick` describes). -/
def BootIPack : Prop :=
  ∀ (a : Fin 2) (rest : List (Fin 2)),
    IPack centre place entry q first (a :: rest)
      ⟨GalilScaffoldController.initial 2048, GalilBootVM.initVM0 (a :: rest)⟩ ∧
    ∀ (c1 : Control) (t : GalilVM),
      StepsAll (galilFrameS (PofC centre place entry (a :: rest)) q first) 2048
        (SoundScanNR (a :: rest)) 1
        ⟨GalilScaffoldController.initial 2048, GalilBootVM.initVM0 (a :: rest)⟩ ⟨c1, t⟩ →
      PalPeg.GalilInvPlus2.InvLPC (a :: rest) c1 t →
      IPack centre place entry q first (a :: rest) ⟨c1, t⟩

/-- **`CloseoutLPack5.H_bootI` from `BootIPack`.**  `invLPC_init` gives the one
`init` tick as a `StepsAll`; `GalilCheckpoints.stepsAll_fn` turns it into the
function form `StepsI` wants, and the pack is needed at the two indices `0` and
`1` only. -/
theorem h_bootI_of_bootIPack (hb : BootIPack centre place entry q first) :
    H_bootI centre place entry q first := by
  intro a rest
  obtain ⟨c1, t, hsteps, hI, hpos⟩ := invLPC_init centre place entry q first a rest
  obtain ⟨hp0, hp1⟩ := hb a rest
  obtain ⟨g, hg0, hg1, htr⟩ := stepsAll_fn hsteps
  refine ⟨c1, t, ⟨g, hg0, hg1, htr, ?_⟩, hI, hpos⟩
  intro i hi
  interval_cases i
  · rw [hg0]; exact hp0
  · rw [hg1]; exact hp1 c1 t hsteps hI

end Boot

#print axioms h_bootI_of_bootIPack

/-! ## 7. `PAL ∈ PEG` with the trail bridge gone -/

/-- **`CloseoutLPack5.pal_in_peg_final5` with `H_trailI` discharged.**  Three
hypotheses become two: the packed oracle `H_oracleI` (the run-level routes) and
the local realization `H_realizeLI'`, plus the two-state boot residual. -/
theorem pal_in_peg_final6 (entry q : ℕ) (first : Fin 9)
    (hboot : BootIPack centreC placeC entry q first)
    (hA : H_oracleI centreC placeC entry q first)
    (hC : H_realizeLI' centreC placeC entry q first) :
    RecognizedByTotalPEG PAL :=
  pal_in_peg_final5 entry q first
    (h_bootI_of_bootIPack centreC placeC entry q first hboot) hA
    (h_trailI centreC placeC entry q first) hC

#print axioms pal_in_peg_final6

end PalPeg.CloseoutLPack6
