import PalPeg.GalilTrailSane
import PalPeg.GalilTrailOrder
import PalPeg.GalilTrailAssembly
import PalPeg.GalilTrailFront
import PalPeg.GalilChainCoupling

/-!
# `RadPack`: the counter-to-head bridge, and `H_trailF` from one hypothesis

The `TrailF` induction left three residuals open:

* `GalilTrailSane.H_headLive` — `CentreLive ∧ LeftLive` along the trace;
* `GalilTrailOrder.H_orderBudget` — `canRight R` at a replayed comparison and
  `radius ≥ 1` while shifting;
* `GalilTrailAssembly.H_lagSide` — `canRight R`, `Sane R` at every tick source,
  the `chain.start()` ledger, and `LagAt`.

This file discharges everything in them that is *not* a genuine
counter-to-head bridge, and names what is left as the single hypothesis
`H_radPack`.

**Proved here, unconditionally.**

* `live_pack_trace` — `CentreLive` *and* `GalilFrontMono.FrontPack` at every
  state of every pre-loaded trace, by the route `GalilTrailFront.h_frontTrace`
  already takes for its own `hlive`: `inv_of_boot_tick` → `InvL ∧
  EntryCounters` → `GalilInvPlus2.invLP2_of_boot` → `hfloor_of_invLP2` →
  `GalilCentreLive.centreLive_of_invLP_run` → `front_steps_mono`.  This kills
  the `CentreLive` half of `H_headLive` outright.
* `replayCan_of_pack` — `canRight R` while replaying, from the frontier budget.
  This kills `OrderBudget.replayR`.
* `lagLe_tickF` / `lagLe_traceF` — the lag ledger of `GalilTrailAssembly`, but
  carried against `LagStepF` (the frontier pack) instead of `LagStep` (a blanket
  `canRight R` at *every* tick source).  The blanket form is too strong — at a
  gap cell with an empty stack and an empty FIFO the right head cannot move and
  the machine takes `scan_wait` — and the ledger only ever needs the move at a
  comparison, where the tick's own guard plus the pack settle it.
* `H_frontTrace` is already unconditional (`GalilTrailFront`), so `Sane R` and
  `position R ≤ 2(m+1)-1` come for free once `H_headLive` does.
* `radPack_boot` — the pack holds at `boot w`.

**Left open**, as `H_radPack`: `RadPack` at every state of every pre-loaded
trace, i.e. `LeftLive`, the strict head order during a shift, the
`chain.start()` ledger `position C + radius ≤ position R` when the chain is
idle, and saneness of the chain verifier.  Its transport along a tick of
`galilFrameS` (the 23-constructor split of `GalilTrailBudget.scanT_tick'`,
with `GalilChainCoupling.coupled_tick` for the chain/radius relations) is the
remaining work.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.GalilTrailRad

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilThrottledRun PalPeg.GalilTrailProof PalPeg.GalilFinalAssembly
open PalPeg.GalilRunSkeleton PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilTrailScan PalPeg.GalilTrailBudget
open PalPeg.GalilTrailChain PalPeg.GalilTrailAssembly

/-! ## 1. `CentreLive` at the boot state -/

theorem centreLive_boot (w : List (Fin 2)) :
    CentreLive (boot w).ctl (boot w).vm := by
  intro hm _
  have h : Mode.init = Mode.rewind := hm
  exact Mode.noConfusion h

#print axioms centreLive_boot

/-! ## 2. `CentreLive` along every pre-loaded trace, unconditionally -/

section Trace
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`CentreLive` and the frontier pack at every state of every pre-loaded
trace.**  Exactly the route `GalilTrailFront.h_frontTrace` takes for its own
`hlive`: the boot state is in `init` mode (so `CentreLive` is vacuous and
`FrontPack` is not claimed), the landing of the boot tick is `Inv`
(`GalilTrailFront.inv_of_boot_tick`), hence `InvLP`, hence `InvLP2` from the boot
(`GalilInvPlus2.invLP2_of_boot`), which pays `hfloor`
(`GalilInvPlus2.hfloor_of_invLP2`), hence `CentreLive` along every run out of it
(`GalilCentreLive.centreLive_of_invLP_run`), hence the pack travels
(`GalilFrontMono.front_steps_mono`). -/
theorem live_pack_trace :
    ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
      ∀ i, i ≤ Tc w.length →
        CentreLive (st i).ctl (st i).vm ∧
          ((st i).ctl.mode ≠ Mode.init →
            PalPeg.GalilFrontMono.FrontPack (st i).ctl (st i).vm) := by
  intro w hw st Tc hP
  rcases w with _ | ⟨a, rest⟩
  · exact absurd hw (by simp)
  have hb : st 0 = boot (a :: rest) := hP.start
  have h0 : CentreLive (st 0).ctl (st 0).vm ∧
      ((st 0).ctl.mode ≠ Mode.init →
        PalPeg.GalilFrontMono.FrontPack (st 0).ctl (st 0).vm) := by
    refine ⟨by rw [hb]; exact centreLive_boot _, fun hne => ?_⟩
    exact absurd (show (st 0).ctl.mode = Mode.init by rw [hb]; rfl) hne
  by_cases hN : 1 ≤ Tc (a :: rest).length
  · have hstep0 : Tick (galilFrameS (PofC centre place entry (a :: rest)) q first) 2048
        (boot (a :: rest)) (st 1) := by
      have h := hP.trace.tick 0 (by omega)
      rwa [hb] at h
    obtain ⟨hInv, hSpan, hR1, hrep1⟩ :=
      PalPeg.GalilTrailFront.inv_of_boot_tick centre place entry q first a rest hstep0
    have hOut : OutputRel (a :: rest) (st 1).ctl (st 1).vm :=
      hP.trace.good 1 hN hInv.mode.1 hInv.mode.2.1
    have hInvL : InvL (a :: rest) (st 1).ctl (st 1).vm := ⟨invS_of_inv hInv, hOut⟩
    have hEC : PalPeg.GalilGlueBLeaves.EntryCounters (a :: rest) (st 1).vm :=
      PalPeg.GalilGlueBLeaves.entryCounters_of_inv hInv hSpan
    have hsteps01 : Steps (galilFrameS (PofC centre place entry (a :: rest)) q first) 2048 1
        ⟨GalilScaffoldController.initial 2048, GalilBootVM.initVM0 (a :: rest)⟩
        ⟨(st 1).ctl, (st 1).vm⟩ := .succ hstep0 (.zero _)
    have hInvLP2 :=
      PalPeg.GalilInvPlus2.invLP2_of_boot centre place entry q first 2048 hsteps01 ⟨hInvL, hEC⟩
    have hfloor := PalPeg.GalilInvPlus2.hfloor_of_invLP2 centre place entry q first hInvLP2
    have hlive := PalPeg.GalilCentreLive.centreLive_of_invLP_run centre place entry q first
      ⟨hInvL, hEC⟩ hfloor
    have hFP1 : PalPeg.GalilFrontMono.FrontPack (st 1).ctl (st 1).vm :=
      PalPeg.GalilFrontMono.frontPack_of_invS (invS_of_inv hInv)
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi1
    · exact h0
    · have hs := PalPeg.GalilTrailFront.steps_between hP.trace hi1 hi
      exact ⟨hlive (i - 1) (st i) hs,
        fun _ => (PalPeg.GalilFrontMono.front_steps_mono (onLetterVM (a :: rest)) leftFirstVM
          centre place entry q first 2048 hs (fun m z hz => hlive m z hz) hFP1).1⟩
  · intro i hi
    have hi0 : i = 0 := by omega
    rw [hi0]; exact h0

/-- **`CentreLive` along every pre-loaded trace, unconditionally.** -/
theorem centreLive_trace :
    ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
      ∀ i, i ≤ Tc w.length → CentreLive (st i).ctl (st i).vm :=
  fun w hw st Tc hP i hi => (live_pack_trace centre place entry q first w hw st Tc hP i hi).1

/-- **The frontier pack at every non-`init` state of every pre-loaded trace.** -/
theorem frontPack_trace :
    ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
      ∀ i, i ≤ Tc w.length → (st i).ctl.mode ≠ Mode.init →
        PalPeg.GalilFrontMono.FrontPack (st i).ctl (st i).vm :=
  fun w hw st Tc hP i hi => (live_pack_trace centre place entry q first w hw st Tc hP i hi).2

#print axioms live_pack_trace
#print axioms centreLive_trace
#print axioms frontPack_trace

end Trace

/-! ## 3. The lag ledger with the frontier pack in place of `canRight`

`GalilTrailAssembly.LagStep` asks for `canRight s.right` at *every* tick source.
That is too strong: at a gap cell with an empty stack and an empty FIFO the right
head cannot move, and the machine takes `scan_wait`.  The ledger only ever needs
the move at a *comparison*, where the tick's own guard
(`c.replaying = true ∨ available s`) plus the frontier pack settle it — exactly as
`GalilTrailSane.canRight_compare` does.  `LagStepF` therefore replaces `canRight`
by the pack, which `frontPack_trace` supplies unconditionally. -/

/-- **`canRight R` while replaying**, from the frontier budget: the replay counter
is `ofNat (m+1)`, so `position R + (m+1) ≤ 2 * arrived R`. -/
theorem replayCan_of_pack {c : Control} {s : GalilVM}
    (hP : GalilFrontMono.FrontPack c s) (hr : c.replaying = true) :
    GalilScaffoldChainVerifier.canRight s.right := by
  obtain ⟨m, hm'⟩ := hP.replayPos hr
  exact GalilFrontMono.canRight_of_budget (hP.frontier (m+1) hm')

/-- **`canRight R` at a comparison**, from the tick's guard and the pack. -/
theorem canRight_of_pack_or {c : Control} {s : GalilVM}
    (hP : GalilFrontMono.FrontPack c s)
    (hav : c.replaying = true ∨ GalilScaffoldChainVerifier.canRight s.right) :
    GalilScaffoldChainVerifier.canRight s.right := by
  rcases hav with h | h
  · exact replayCan_of_pack hP h
  · exact h

/-- `GalilTrailAssembly.LagStep` with the frontier pack in place of the blanket
`canRight`. -/
structure LagStepF (c : Control) (s : GalilVM) : Prop where
  pack : c.mode ≠ Mode.init → GalilFrontMono.FrontPack c s
  sane : GalilFrontMono.Sane s.right
  start : s.chain = ChainVM.idle → StartLe s.center s.radius (position s.right)

theorem lagStepF_right {c : Control} {s : GalilVM} (h : LagStepF c s)
    (hm : c.mode = Mode.scan)
    (hav : c.replaying = true ∨ GalilScaffoldChainVerifier.canRight s.right) :
    position (GalilScaffoldChainVerifier.right s.right) = position s.right + 1 :=
  (GalilFrontMono.right_sane
    (canRight_of_pack_or (h.pack (by rw [hm]; decide)) hav) h.sane).1

section TickF
variable (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
  (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)

theorem lagLe_tickF {c c' : Control} {s t : GalilVM}
    (hL : LagLe s.chain (position s.right)) (hS : LagStepF c s)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : LagLe t.chain (position t.right) := by
  cases h
  case init =>
    rename_i hm hi
    obtain ⟨-, -, -, -, -, -, -, -, -, hch, -⟩ : initVM entry s t := hi
    exact lagLe_of_idle hch
  case scan_wait =>
    rename_i hm hav hb
    obtain ⟨-, hr, hch, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    rw [hr]
    exact lagLe_chainAt_false hch hL hS.start
  case scan_count =>
    rename_i hm hc hav hb
    obtain ⟨-, hr, hch, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    rw [hr]
    exact lagLe_chainAt_false hch hL hS.start
  case restart =>
    rename_i hm hb
    obtain ⟨w, -, -, -, -, ht⟩ : restartVM entry s t := hb
    exact lagLe_of_idle (by rw [ht])
  case scan_match =>
    rename_i s' o hmt hm hc hcmp hav hpl ho
    obtain ⟨a, found, ans, cc, wk, hch, -⟩ :=
      compare_chainAt onLetter leftFirst centre place entry q first hcmp
    obtain ⟨-, hr2, -⟩ :=
      compare_heads onLetter leftFirst centre place entry q first hcmp
    have hpl' : t = (if c.replaying then
        {s' with replay := GalilScaffoldCounter.dec s'.replay} else s') := hpl
    have htc : t.chain = s'.chain := by rw [hpl']; cases c.replaying <;> rfl
    have htr : t.right = s'.right := by rw [hpl']; cases c.replaying <;> rfl
    rw [htc, htr, hr2, lagStepF_right hS hm hav]
    exact lagLe_chainAt hch hL hS.start
  case scan_shift =>
    rename_i s' hmt hg hm hc hr hcmp hav hb
    obtain ⟨a, found, ans, cc, wk, hch, ha⟩ :=
      compare_chainAt onLetter leftFirst centre place entry q first hcmp
    obtain rfl : a = false := ha hmt
    obtain ⟨-, hr2, -⟩ :=
      compare_heads onLetter leftFirst centre place entry q first hcmp
    obtain ⟨w, hs0, ht⟩ : beginShiftVM' s' t := hb
    have htc : t.chain = ChainVM.watch (GalilScaffoldChainWatch.immediate w) := by rw [ht]
    have htr : t.right = s'.right := by rw [ht]
    rw [htc, htr, hr2, lagStepF_right hS hm hav]
    refine lagLe_right (x := ChainVM.watch w) rfl rfl ?_
    rw [← hs0]
    exact lagLe_chainAt_false hch hL hS.start
  case scan_fallback =>
    rename_i s' hmt hm hc hg hr hcmp hav hb
    obtain ⟨pl, ht⟩ : beginFallbackVM' s' t := hb
    exact lagLe_of_idle (by rw [ht])
  case shift_one =>
    rename_i hm hp hi
    obtain ⟨-, -, -, w, hw, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    have hws : s.chain = ChainVM.watch w := hw
    have htr : t.right = s.right := by rw [ht]; rfl
    rw [htr]
    exact lagLe_congr hL (by rw [ht, hws]; rfl)
  case shift_done =>
    rename_i o hm hp ho
    exact hL
  case replayStart =>
    rename_i o hm ho ho' hi
    obtain ⟨-, -, -, -, -, -, -, -, -, hch, -⟩ : replayStartVM entry s t := hi
    exact lagLe_of_idle hch
  all_goals
    (rename_i hi
     have hch : t.chain = s.chain := (congrArg GalilVM.chain hi.2).trans rfl
     have htr : t.right = s.right := by
       first
       | exact (congrArg GalilVM.right hi.2).trans rfl
       | exact (congrArg GalilVM.right hi.2).trans (by rw [hi.1.2]; rfl)
       | exact (congrArg GalilVM.right hi.2).trans (by rw [hi.1]; rfl)
     rw [hch, htr]
     exact hL)


#print axioms lagLe_tickF

end TickF

section TraceF
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

theorem lagLe_traceF {raw : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ} {m : ℕ}
    (hP : PreTrace centre place entry q first raw st Tc) (hm : m < raw.length)
    (hstep : ∀ i, i < Tc (m+1) → LagStepF (st i).ctl (st i).vm) :
    ∀ i, i ≤ Tc (m+1) → LagLe (st i).vm.chain (position (st i).vm.right) := by
  have hle : Tc (m+1) ≤ Tc raw.length := hP.mono (m+1) raw.length (by omega) le_rfl
  intro i
  induction i with
  | zero => intro _; rw [hP.start]; exact lagLe_of_idle rfl
  | succ i ih =>
    intro hi
    have hlt : i < Tc (m+1) := by omega
    exact lagLe_tickF (onLetterVM raw) leftFirstVM centre place entry q first 2048
      (ih (by omega)) (hstep i hlt) (hP.trace.tick i (by omega))


#print axioms lagLe_traceF

end TraceF

/-! ## 4. `RadPack`: the counter-to-head bridge -/

/-- **The counter-to-head bridge at one state.**  Everything the `TrailF`
induction still needs and that head arithmetic, the frontier pack and the
centre-liveness run cannot produce on their own:

* `leftLive` — the left head is off the clipped origin whenever a scan
  comparison or a rewind tick is about to move it (`GalilTrailSane.LeftLive`);
* `shiftLC`, `shiftCR` — the three heads are *strictly* ordered while the
  machine shifts, i.e. the radius is at least one during a shift;
* `startLe` — a fresh `chain.start()` copies a centre head trailing `R` by the
  radius (the `≤` half of `ScanInvariant.rightPos`, with the radius counter
  canonical and non-negative);
* `verSane` — the chain verifier is a sane place.

`CentreLive`, `Sane R`, `canRight R` at a comparison, `position R ≤ 2(m+1)-1`
and the whole of `H_frontTrace` are *proved*, here and in
`GalilTrailFront`. -/
structure RadPack (c : Control) (s : GalilVM) : Prop where
  leftLive : PalPeg.GalilTrailSane.LeftLive c s
  shiftLC : c.mode = Mode.shift → position s.left + 1 ≤ position s.center
  shiftCR : c.mode = Mode.shift → position s.center + 1 ≤ position s.right
  startLe : s.chain = ChainVM.idle → StartLe s.center s.radius (position s.right)
  verSane : ∀ p, verOf s.chain = some p → GalilFrontMono.Sane p

/-- `RadPack` plus the frontier pack delivers `GalilTrailOrder.OrderBudget`: the
`canRight` of a replayed comparison is the frontier budget. -/
theorem orderBudget_of_radPack {c : Control} {s : GalilVM} (h : RadPack c s)
    (hp : c.mode ≠ Mode.init → GalilFrontMono.FrontPack c s) :
    PalPeg.GalilTrailOrder.OrderBudget c s :=
  ⟨fun hm _ hr => replayCan_of_pack (hp (by rw [hm]; decide)) hr, h.shiftLC, h.shiftCR⟩

/-- `RadPack` plus the frontier pack and `Sane R` delivers `LagStepF`. -/
theorem lagStepF_of_radPack {c : Control} {s : GalilVM} (h : RadPack c s)
    (hp : c.mode ≠ Mode.init → GalilFrontMono.FrontPack c s)
    (hs : GalilFrontMono.Sane s.right) : LagStepF c s :=
  ⟨hp, hs, h.startLe⟩

/-- `RadPack` plus the place bound on `R` (which `H_frontTrace` supplies)
delivers `GalilTrailAssembly.LagAt`. -/
theorem lagAt_of_radPack {c : Control} {s : GalilVM} {m : ℕ} (h : RadPack c s)
    (hb : position s.right ≤ 2 * (m + 1) - 1) : LagAt m s :=
  ⟨hb, h.verSane⟩

#print axioms orderBudget_of_radPack
#print axioms lagStepF_of_radPack
#print axioms lagAt_of_radPack

/-! ## 5. The boot state -/

theorem radPack_boot (w : List (Fin 2)) : RadPack (boot w).ctl (boot w).vm := by
  have hv : GalilScaffoldCounter.value (boot w).vm.radius = 0 := rfl
  have hc : (boot w).vm.center = (boot w).vm.right := rfl
  have hch : (boot w).vm.chain = ChainVM.idle := rfl
  refine ⟨⟨fun hm _ => ?_, fun hm => ?_⟩, fun hm => ?_, fun hm => ?_, fun _ => ?_,
    fun p hp => ?_⟩
  · exact absurd (show Mode.init = Mode.scan from hm) (by decide)
  · exact absurd (show Mode.init = Mode.rewind from hm) (by decide)
  · exact absurd (show Mode.init = Mode.shift from hm) (by decide)
  · exact absurd (show Mode.init = Mode.shift from hm) (by decide)
  · refine ⟨GalilScaffoldCounter.ofNat_canonical 0, ?_, ?_⟩
    · show (0 : ℤ) ≤ GalilScaffoldCounter.value (boot w).vm.radius
      rw [hv]
    · show (position (boot w).vm.center : ℤ) + GalilScaffoldCounter.value (boot w).vm.radius
        ≤ (position (boot w).vm.right : ℤ)
      rw [hv, hc]; omega
  · rw [hch] at hp
    exact absurd hp (by simp [verOf])

#print axioms radPack_boot

/-! ## 6. The named hypothesis and `H_trailF` -/

section Hyps
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(Named) the counter-to-head bridge along every pre-loaded trace.**  This is
the single residual of the `TrailF` induction after this file: at every state of
every pre-loaded trace, `RadPack` holds.  It is established at the boot state by
`radPack_boot`; what is missing is its transport along a tick of `galilFrameS`. -/
def H_radPack : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    ∀ i, i ≤ Tc w.length → RadPack (st i).ctl (st i).vm

theorem h_headLive_of_radPack (h : H_radPack centre place entry q first) :
    PalPeg.GalilTrailSane.H_headLive centre place entry q first :=
  fun w hw st Tc hP i hi =>
    ⟨centreLive_trace centre place entry q first w hw st Tc hP i (Nat.le_of_lt hi),
      (h w hw st Tc hP i (Nat.le_of_lt hi)).leftLive⟩

theorem h_saneHeads_of_radPack (h : H_radPack centre place entry q first) :
    H_saneHeads centre place entry q first :=
  PalPeg.GalilTrailSane.h_saneHeads_of_headLive centre place entry q first
    (h_headLive_of_radPack centre place entry q first h)

theorem h_headOrder_of_radPack (h : H_radPack centre place entry q first) :
    H_headOrder centre place entry q first :=
  PalPeg.GalilTrailOrder.h_headOrder_of_budget centre place entry q first
    (fun w hw st Tc hP i hi =>
      orderBudget_of_radPack (h w hw st Tc hP i (Nat.le_of_lt hi))
        (frontPack_trace centre place entry q first w hw st Tc hP i (Nat.le_of_lt hi)))

theorem h_trailScan_of_radPack (h : H_radPack centre place entry q first) :
    H_trailScan centre place entry q first :=
  h_trailScan_of_residuals centre place entry q first
    (h_saneHeads_of_radPack centre place entry q first h)
    (h_headOrder_of_radPack centre place entry q first h)
    (PalPeg.GalilTrailFront.h_frontTrace centre place entry q first)

/-- **`ChainBudget` at every state up to the checkpoint**, through the lag ledger
of §3 (so with no blanket `canRight`). -/
theorem chainBudget_of_radPack (h : H_radPack centre place entry q first)
    {w : List (Fin 2)} (hw : 0 < w.length) {st Tc}
    (hP : PreTrace centre place entry q first w st Tc) {m : ℕ} (hm : m < w.length) :
    ∀ i, i ≤ Tc (m+1) → ChainBudget m (st i).vm.chain := by
  have hle : Tc (m+1) ≤ Tc w.length := hP.mono (m+1) w.length (by omega) le_rfl
  have hsane := h_saneHeads_of_radPack centre place entry q first h w hw st Tc hP
  have hplace := placeR_of_preTrace centre place entry q first
    (PalPeg.GalilTrailFront.h_frontTrace centre place entry q first) hw hP hm
  have hstep : ∀ i, i < Tc (m+1) → LagStepF (st i).ctl (st i).vm := fun i hi =>
    lagStepF_of_radPack (h w hw st Tc hP i (by omega))
      (frontPack_trace centre place entry q first w hw st Tc hP i (by omega))
      (hsane i (by omega)).2.2
  exact fun i hi =>
    chainBudget_of_lagLe (lagLe_traceF centre place entry q first hP hm hstep i hi)
      (lagAt_of_radPack (h w hw st Tc hP i (by omega)) (hplace i hi))

theorem h_trailVer_of_radPack (h : H_radPack centre place entry q first) :
    ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc,
      PreTrace centre place entry q first w st Tc → ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) →
        (∀ p, verOf (st i).vm.chain = some p → Trails w m 0 p) ∧
        (∀ v, (st i).vm.chain = .watch v → GalilScaffoldCounter.positive v.lag = true →
          Trails w m 1 v.machine.verifier) := by
  intro w hw st Tc hP m hm i hi
  have hB := chainBudget_of_radPack centre place entry q first h hw hP hm
  have hV := verF_trace centre place entry q first hP hm
    (fun j hj => h_trailScan_of_radPack centre place entry q first h w hw st Tc hP m hm j hj)
    hB i hi
  exact ⟨hV.ver, hV.lagPos⟩

/-- **`H_trailF` from the single named hypothesis `H_radPack`.**  The three
residuals of `GalilTrailSane`/`GalilTrailOrder`/`GalilTrailAssembly` are gone:
`CentreLive` and the frontier pack are proved here, `H_frontTrace` in
`GalilTrailFront`, the blanket `canRight` of `LagStep` is replaced by the
comparison-local one, and the rest is read off `RadPack`. -/
theorem h_trailF_of_radPack (h : H_radPack centre place entry q first) :
    H_trailF centre place entry q first :=
  h_trailF_of_parts centre place entry q first
    (h_trailScan_of_radPack centre place entry q first h)
    (h_trailVer_of_radPack centre place entry q first h)

end Hyps

#print axioms h_headLive_of_radPack
#print axioms h_saneHeads_of_radPack
#print axioms h_headOrder_of_radPack
#print axioms h_trailScan_of_radPack
#print axioms chainBudget_of_radPack
#print axioms h_trailVer_of_radPack
#print axioms h_trailF_of_radPack

end PalPeg.GalilTrailRad
