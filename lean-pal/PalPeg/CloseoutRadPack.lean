import PalPeg.GalilTrailRad

/-!
# The radius ledger, and `RadPack.startLe` discharged

`GalilTrailRad.RadPack` has four fields.  `startLe` — the `chain.start()` ledger
`position C + radius ≤ position R` on a canonical non-negative radius — is the
only one of them that is a pure *counter-to-head* statement, and this file proves
it, in the stronger form that drops the `chain = idle` guard: `RadLedger` asserts
the inequality at **every** state, so `startLe` falls out with the guard unused.

`RadLedger` carries three side clauses that the transport needs and that are not
the conclusion in disguise:

* `canonRem` — the unit countdown is a canonical counter;
* `initZero` — the radius is zero while the controller is still in `init` mode.
  No tick of `galilFrameS` ever *enters* `init` mode, so this clause is carried
  vacuously everywhere; it is what pays the `init` tick, where `C` and `R` are
  both set to `right R` while the radius is kept (`initVM`);
* `shiftBud` — during a shift the unit countdown does not exceed the radius.
  `shiftTick` decrements both, so this is what keeps the radius non-negative
  across `shift_one`; it enters at `scan_shift` from
  `GalilChainCoupling.budget_of_coupled` (`periodLength w ≤ GalilScaffoldCounter.value s'.radius`),
  because `beginShiftVM` sets `remaining := GalilScaffoldCounter.ofNat (periodLength w)`.

The transport hypotheses are four, all of them already proved elsewhere along a
pre-loaded trace:

* `GalilChainCoupling.Coupled c s` (`coupled_tick`; `coupled_of_idle` at boot);
* `CentreLive c s` (`GalilTrailRad.centreLive_trace`), used at `rewind_pair`,
  where `C` moves left and the radius is incremented;
* `GalilFrontMono.FrontPack` off `init` and `Sane s.right`
  (`GalilTrailRad.frontPack_trace`, `GalilTrailSane.h_saneHeads_of_headLive`),
  used at the three comparison branches, where `R` moves right;
* `Sane s.center` (same source), used at `shift_one`.

**Not proved here**, and deliberately not packed away into a fresh hypothesis:
the other three `RadPack` fields.  See §4.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutRadPack

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilThrottledRun PalPeg.GalilTrailProof PalPeg.GalilFinalAssembly
open PalPeg.GalilTrailScan PalPeg.GalilTrailBudget PalPeg.GalilTrailChain
open PalPeg.GalilTrailAssembly PalPeg.GalilTrailRad


/-! ## 1. The ledger -/

/-- **The radius ledger.** -/
structure RadLedger (c : Control) (s : GalilVM) : Prop where
  canon : GalilScaffoldCounter.Canonical s.radius
  canonRem : GalilScaffoldCounter.Canonical s.remaining
  nonneg : 0 ≤ GalilScaffoldCounter.value s.radius
  le : (position s.center : ℤ) + GalilScaffoldCounter.value s.radius ≤ (position s.right : ℤ)
  initZero : c.mode = Mode.init → GalilScaffoldCounter.value s.radius = 0
  shiftBud : c.mode = Mode.shift → GalilScaffoldCounter.value s.remaining ≤ GalilScaffoldCounter.value s.radius

/-- **`RadPack.startLe`, discharged.** -/
theorem startLe_of_radLedger {c : Control} {s : GalilVM} (h : RadLedger c s) :
    s.chain = ChainVM.idle → StartLe s.center s.radius (position s.right) :=
  fun _ => ⟨h.canon, h.nonneg, h.le⟩

#print axioms startLe_of_radLedger

/-! ## 2. The boot state -/

theorem radLedger_boot (w : List (Fin 2)) : RadLedger (boot w).ctl (boot w).vm := by
  have hv : GalilScaffoldCounter.value (boot w).vm.radius = 0 := rfl
  have hrv : GalilScaffoldCounter.value (boot w).vm.remaining = 0 := rfl
  have hc : (boot w).vm.center = (boot w).vm.right := rfl
  exact ⟨Or.inl rfl, Or.inl rfl, by rw [hv], by rw [hv, hc]; omega, fun _ => hv,
    fun _ => by rw [hv, hrv]⟩

#print axioms radLedger_boot

/-! ## 3. Transport along one tick -/

section Tick
variable (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
  (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)

/-- The radius after a comparison is `radius++`, whatever the outcome: both
`afterCompare` and `afterMismatch` set it to `radiusAfter s`. -/
theorem compare_radius {s s' : GalilVM}
    (hcmp : (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).compare s s') :
    s'.radius = GalilScaffoldCounter.inc s.radius := by
  obtain ⟨vs, vq, a, -, -, -, -, -, hteq⟩ :
    compareFound (sharedC onLetter leftFirst centre place entry) q first s s' := hcmp
  rw [hteq, afterBirth_radius]; cases a <;> rfl

/-- The remaining counter is untouched by a comparison. -/
theorem compare_remaining {s s' : GalilVM}
    (hcmp : (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).compare s s') :
    s'.remaining = s.remaining := by
  obtain ⟨vs, vq, a, -, -, -, -, -, hteq⟩ :
    compareFound (sharedC onLetter leftFirst centre place entry) q first s s' := hcmp
  rw [hteq, afterBirth_remaining]; cases a <;> rfl

/-- `R` moves exactly one place right at a comparison tick. -/
theorem rightStep {c : Control} {s : GalilVM} (hm : c.mode = Mode.scan)
    (hP : GalilFrontMono.FrontPack c s) (hs : GalilFrontMono.Sane s.right)
    (hav : c.replaying = true ∨ GalilScaffoldChainVerifier.canRight s.right) :
    position (GalilScaffoldChainVerifier.right s.right) = position s.right + 1 :=
  (GalilFrontMono.right_sane (canRight_of_pack_or hP hav) hs).1

/-- **The radius ledger travels along every tick of `galilFrameS`.** -/
theorem radLedger_tick {c c' : Control} {s t : GalilVM} (hL : RadLedger c s)
    (hC : PalPeg.GalilChainCoupling.Coupled c s)
    (hlive : CentreLive c s)
    (hpack : c.mode ≠ Mode.init → GalilFrontMono.FrontPack c s)
    (hsaneR : GalilFrontMono.Sane s.right) (hsaneC : GalilFrontMono.Sane s.center)
    (hcopy : c.mode = Mode.shift → CopyIdle s)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : RadLedger c' t := by
  obtain ⟨hcan, hcanr, hnn, hle, hiz, hsb⟩ := hL
  cases h
  case init =>
    rename_i hm hi
    obtain ⟨hr, hl, hce, -, hrad, hrem, -⟩ : initVM entry s t := hi
    have hz : GalilScaffoldCounter.value s.radius = 0 := hiz hm
    refine ⟨by rw [hrad]; exact hcan, by rw [hrem]; exact hcanr, by rw [hrad, hz], ?_,
      fun hm' => Mode.noConfusion hm', fun hm' => Mode.noConfusion hm'⟩
    rw [hrad, hce, hr, hz]; omega
  case scan_wait =>
    rename_i hm hav hb
    obtain ⟨-, hr, -, hce, -, hrad, -, -, hrem, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    exact ⟨by rw [hrad]; exact hcan, by rw [hrem]; exact hcanr, by rw [hrad]; exact hnn,
      by rw [hrad, hce, hr]; exact hle,
      fun hm' => Mode.noConfusion (hm.symm.trans hm'),
      fun hm' => Mode.noConfusion (hm.symm.trans hm')⟩
  case scan_count =>
    rename_i hm hc hav hb
    obtain ⟨-, hr, -, hce, -, hrad, -, -, hrem, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    exact ⟨by rw [hrad]; exact hcan, by rw [hrem]; exact hcanr, by rw [hrad]; exact hnn,
      by rw [hrad, hce, hr]; exact hle,
      fun hm' => Mode.noConfusion (hm.symm.trans hm'),
      fun hm' => Mode.noConfusion (hm.symm.trans hm')⟩
  case restart =>
    rename_i hm hb
    obtain ⟨w, -, -, -, -, ht⟩ : restartVM entry s t := hb
    exact ⟨by rw [ht]; exact hcan, by rw [ht]; exact hcanr, by rw [ht]; exact hnn,
      by rw [ht]; exact hle,
      fun hm' => Mode.noConfusion (hm.symm.trans hm'),
      fun hm' => Mode.noConfusion (hm.symm.trans hm')⟩
  case scan_match =>
    rename_i s' o hmt hm hc hcmp hav hpl ho
    obtain ⟨-, hr2, hce⟩ :=
      compare_heads onLetter leftFirst centre place entry q first hcmp
    have hrad' := compare_radius onLetter leftFirst centre place entry q first hcmp
    have hrem' := compare_remaining onLetter leftFirst centre place entry q first hcmp
    have hpl' : t = (if c.replaying then
        {s' with replay := GalilScaffoldCounter.dec s'.replay} else s') := hpl
    have hce2 : t.center = s.center := by rw [hpl']; cases c.replaying <;> exact hce
    have hr3 : t.right = GalilScaffoldChainVerifier.right s.right := by
      rw [hpl']; cases c.replaying <;> exact hr2
    have hrad2 : t.radius = GalilScaffoldCounter.inc s.radius := by rw [hpl']; cases c.replaying <;> exact hrad'
    have hrem2 : t.remaining = s.remaining := by rw [hpl']; cases c.replaying <;> exact hrem'
    have hstep := rightStep hm (hpack (by rw [hm]; decide)) hsaneR hav
    refine ⟨by rw [hrad2]; exact GalilScaffoldCounter.inc_canonical _ hcan, by rw [hrem2]; exact hcanr,
      by rw [hrad2, GalilScaffoldCounter.inc_value]; omega, ?_,
      fun hm' => Mode.noConfusion (hm.symm.trans hm'),
      fun hm' => Mode.noConfusion (hm.symm.trans hm')⟩
    rw [hrad2, hce2, hr3, GalilScaffoldCounter.inc_value, hstep]
    push_cast
    omega
  case scan_shift =>
    rename_i s' hmt hg hm hc hr hcmp hav hb
    obtain ⟨-, hr2, hce⟩ :=
      compare_heads onLetter leftFirst centre place entry q first hcmp
    have hrad' := compare_radius onLetter leftFirst centre place entry q first hcmp
    obtain ⟨w, hs0, ht⟩ : beginShiftVM' s' t := hb
    have hstep := rightStep hm (hpack (by rw [hm]; decide)) hsaneR hav
    have hbud : (periodLength w : ℤ) ≤ GalilScaffoldCounter.value s'.radius :=
      PalPeg.GalilChainCoupling.budget_of_coupled onLetter leftFirst centre place entry q first
        hC hm hr s' w hcmp hmt hg hs0
    have hce2 : t.center = s.center := by rw [ht]; exact hce
    have hr3 : t.right = GalilScaffoldChainVerifier.right s.right := by rw [ht]; exact hr2
    have hrad2 : t.radius = GalilScaffoldCounter.inc s.radius := by rw [ht]; exact hrad'
    have hrem2 : t.remaining = GalilScaffoldCounter.ofNat (periodLength w) := by rw [ht]
    refine ⟨by rw [hrad2]; exact GalilScaffoldCounter.inc_canonical _ hcan, by rw [hrem2]; exact GalilScaffoldCounter.ofNat_canonical _,
      by rw [hrad2, GalilScaffoldCounter.inc_value]; omega, ?_, fun hm' => Mode.noConfusion hm', fun _ => ?_⟩
    · rw [hrad2, hce2, hr3, GalilScaffoldCounter.inc_value, hstep]
      push_cast
      omega
    · rw [hrem2, hrad2, GalilScaffoldCounter.ofNat_value]
      rw [hrad'] at hbud
      exact hbud
  case scan_fallback =>
    rename_i s' hmt hm hc hg hr hcmp hav hb
    obtain ⟨-, hr2, hce⟩ :=
      compare_heads onLetter leftFirst centre place entry q first hcmp
    have hrad' := compare_radius onLetter leftFirst centre place entry q first hcmp
    have hrem' := compare_remaining onLetter leftFirst centre place entry q first hcmp
    obtain ⟨pl, ht, -⟩ : beginFallbackVM' s' t := hb
    have hstep := rightStep hm (hpack (by rw [hm]; decide)) hsaneR hav
    have hce2 : t.center = s.center := by rw [ht]; exact hce
    have hr3 : t.right = GalilScaffoldChainVerifier.right s.right := by rw [ht]; exact hr2
    have hrad2 : t.radius = GalilScaffoldCounter.inc s.radius := by rw [ht]; exact hrad'
    have hrem2 : t.remaining = s.remaining := by rw [ht]; exact hrem'
    refine ⟨by rw [hrad2]; exact GalilScaffoldCounter.inc_canonical _ hcan, by rw [hrem2]; exact hcanr,
      by rw [hrad2, GalilScaffoldCounter.inc_value]; omega, ?_,
      fun hm' => Mode.noConfusion hm', fun hm' => Mode.noConfusion hm'⟩
    rw [hrad2, hce2, hr3, GalilScaffoldCounter.inc_value, hstep]
    push_cast
    omega
  case shift_one =>
    rename_i hm hp hi
    obtain ⟨hcc, hcl, hcl2, w, hw, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    have hce2 : t.center = GalilScaffoldChainVerifier.right s.center := by rw [ht]; rfl
    have hr2 : t.right = s.right := by rw [ht]; rfl
    have hrad2 : t.radius = GalilScaffoldCounter.dec s.radius := by rw [ht]; rfl
    have hrem2 : t.remaining = GalilScaffoldCounter.dec s.remaining := by rw [ht]; rfl
    have hstepC : position (GalilScaffoldChainVerifier.right s.center) = position s.center + 1 :=
      (GalilFrontMono.right_sane hcc hsaneC).1
    have hposR : GalilScaffoldCounter.positive s.remaining = true := by
      rcases hp with h1 | h2
      · exact h1
      · exact absurd h2 (hcopy hm)
    have hpos : 0 < GalilScaffoldCounter.value s.remaining :=
      (GalilScaffoldCounter.positive_iff _ hcanr).1 hposR
    have hb := hsb hm
    refine ⟨by rw [hrad2]; exact GalilScaffoldCounter.dec_canonical _ hcan, by rw [hrem2]; exact GalilScaffoldCounter.dec_canonical _ hcanr,
      by rw [hrad2, GalilScaffoldCounter.dec_value]; omega, ?_,
      fun hm' => Mode.noConfusion (hm.symm.trans hm'), fun _ => ?_⟩
    · rw [hrad2, hce2, hr2, GalilScaffoldCounter.dec_value, hstepC]
      push_cast
      omega
    · rw [hrem2, hrad2, GalilScaffoldCounter.dec_value, GalilScaffoldCounter.dec_value]
      omega
  case shift_done =>
    rename_i o hm hp ho
    exact ⟨hcan, hcanr, hnn, hle, fun hm' => Mode.noConfusion hm',
      fun hm' => Mode.noConfusion hm'⟩
  case replayStart =>
    rename_i o hm ho ho' hi
    obtain ⟨-, hr, hl, hce, hrad, -, hrem, -⟩ : replayStartVM entry s t := hi
    have hz : GalilScaffoldCounter.value t.radius = 0 := by rw [hrad]; rfl
    refine ⟨by rw [hrad]; exact Or.inl rfl, by rw [hrem]; exact hcanr, by rw [hz], ?_,
      fun hm' => Mode.noConfusion hm', fun hm' => Mode.noConfusion hm'⟩
    rw [hz, hce, hr]; omega
  case choose_select =>
    rename_i hm hodd hs hi
    have hrad : t.radius = GalilScaffoldCounter.reset :=
      (congrArg GalilVM.radius hi.2).trans (by rw [hi.1]; rfl)
    have hrem : t.remaining = s.remaining :=
      (congrArg GalilVM.remaining hi.2).trans (by rw [hi.1]; rfl)
    have hce : t.center = s.right := (congrArg GalilVM.center hi.2).trans (by rw [hi.1]; rfl)
    have hr : t.right = s.right := (congrArg GalilVM.right hi.2).trans (by rw [hi.1]; rfl)
    have hz : GalilScaffoldCounter.value t.radius = 0 := by rw [hrad]; rfl
    refine ⟨by rw [hrad]; exact Or.inl rfl, by rw [hrem]; exact hcanr, by rw [hz], ?_,
      fun hm' => Mode.noConfusion hm', fun hm' => Mode.noConfusion hm'⟩
    rw [hz, hce, hr]; omega
  case rewind_pair =>
    rename_i hm hfi hpr hi
    have hce2 : t.center = GalilScaffoldInputHead.left s.center :=
      (congrArg GalilVM.center hi.2).trans (by rw [hi.1.2]; rfl)
    have hr2 : t.right = s.right :=
      (congrArg GalilVM.right hi.2).trans (by rw [hi.1.2]; rfl)
    have hrad2 : t.radius = GalilScaffoldCounter.inc s.radius :=
      (congrArg GalilVM.radius hi.2).trans (by rw [hi.1.2]; rfl)
    have hrem2 : t.remaining = s.remaining :=
      (congrArg GalilVM.remaining hi.2).trans (by rw [hi.1.2]; rfl)
    have hlivepos : 0 < position s.center := hlive hm hfi
    have hdown : position (GalilScaffoldInputHead.left s.center) + 1 = position s.center :=
      left_position_pos hlivepos
    have hdownZ : ((position (GalilScaffoldInputHead.left s.center) : ℤ)) + 1 =
        (position s.center : ℤ) := by exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hdown
    refine ⟨by rw [hrad2]; exact GalilScaffoldCounter.inc_canonical _ hcan,
      by rw [hrem2]; exact hcanr,
      by rw [hrad2, GalilScaffoldCounter.inc_value]; omega, ?_,
      fun hm' => Mode.noConfusion (hm.symm.trans hm'),
      fun hm' => Mode.noConfusion (hm.symm.trans hm')⟩
    rw [hrad2, hce2, hr2, GalilScaffoldCounter.inc_value]
    omega
  case rewind_one =>
    rename_i hm hfi hpr hi
    have hce2 : t.center = s.center :=
      (congrArg GalilVM.center hi.2).trans (by rw [hi.1.2]; rfl)
    have hr2 : t.right = s.right :=
      (congrArg GalilVM.right hi.2).trans (by rw [hi.1.2]; rfl)
    have hrad2 : t.radius = s.radius :=
      (congrArg GalilVM.radius hi.2).trans (by rw [hi.1.2]; rfl)
    have hrem2 : t.remaining = s.remaining :=
      (congrArg GalilVM.remaining hi.2).trans (by rw [hi.1.2]; rfl)
    exact ⟨by rw [hrad2]; exact hcan, by rw [hrem2]; exact hcanr, by rw [hrad2]; exact hnn,
      by rw [hrad2, hce2, hr2]; exact hle,
      fun hm' => Mode.noConfusion (hm.symm.trans hm'),
      fun hm' => Mode.noConfusion (hm.symm.trans hm')⟩
  case copy_one =>
    rename_i hm hp hi
    have hrad : t.radius = s.radius := (congrArg GalilVM.radius hi.2).trans rfl
    have hrem : t.remaining = s.remaining := (congrArg GalilVM.remaining hi.2).trans rfl
    have hce : t.center = s.center := (congrArg GalilVM.center hi.2).trans rfl
    have hr : t.right = s.right := (congrArg GalilVM.right hi.2).trans rfl
    exact ⟨by rw [hrad]; exact hcan, by rw [hrem]; exact hcanr, by rw [hrad]; exact hnn,
      by rw [hrad, hce, hr]; exact hle, fun hm' => Mode.noConfusion (hm.symm.trans hm'), fun hm' => Mode.noConfusion (hm.symm.trans hm')⟩
  case copy_done =>
    rename_i hm hp hi
    have hrad : t.radius = s.radius := (congrArg GalilVM.radius hi.2).trans rfl
    have hrem : t.remaining = s.remaining := (congrArg GalilVM.remaining hi.2).trans rfl
    have hce : t.center = s.center := (congrArg GalilVM.center hi.2).trans rfl
    have hr : t.right = s.right := (congrArg GalilVM.right hi.2).trans rfl
    exact ⟨by rw [hrad]; exact hcan, by rw [hrem]; exact hcanr, by rw [hrad]; exact hnn,
      by rw [hrad, hce, hr]; exact hle, fun hm' => Mode.noConfusion hm', fun hm' => Mode.noConfusion hm'⟩
  case home_start =>
    rename_i hm hl hi
    have hrad : t.radius = s.radius := (congrArg GalilVM.radius hi.2).trans rfl
    have hrem : t.remaining = s.remaining := (congrArg GalilVM.remaining hi.2).trans rfl
    have hce : t.center = s.center := (congrArg GalilVM.center hi.2).trans rfl
    have hr : t.right = s.right := (congrArg GalilVM.right hi.2).trans rfl
    exact ⟨by rw [hrad]; exact hcan, by rw [hrem]; exact hcanr, by rw [hrad]; exact hnn,
      by rw [hrad, hce, hr]; exact hle, fun hm' => Mode.noConfusion hm', fun hm' => Mode.noConfusion hm'⟩
  case home_step =>
    rename_i hm hl hi
    have hrad : t.radius = s.radius := (congrArg GalilVM.radius hi.2).trans rfl
    have hrem : t.remaining = s.remaining := (congrArg GalilVM.remaining hi.2).trans rfl
    have hce : t.center = s.center := (congrArg GalilVM.center hi.2).trans rfl
    have hr : t.right = s.right := (congrArg GalilVM.right hi.2).trans rfl
    exact ⟨by rw [hrad]; exact hcan, by rw [hrem]; exact hcanr, by rw [hrad]; exact hnn,
      by rw [hrad, hce, hr]; exact hle, fun hm' => Mode.noConfusion (hm.symm.trans hm'), fun hm' => Mode.noConfusion (hm.symm.trans hm')⟩
  case fpp_slice =>
    rename_i hm hi
    have hrad : t.radius = s.radius := (congrArg GalilVM.radius hi.2).trans rfl
    have hrem : t.remaining = s.remaining := (congrArg GalilVM.remaining hi.2).trans rfl
    have hce : t.center = s.center := (congrArg GalilVM.center hi.2).trans rfl
    have hr : t.right = s.right := (congrArg GalilVM.right hi.2).trans rfl
    exact ⟨by rw [hrad]; exact hcan, by rw [hrem]; exact hcanr, by rw [hrad]; exact hnn,
      by rw [hrad, hce, hr]; exact hle, fun hm' => Mode.noConfusion (hm.symm.trans hm'), fun hm' => Mode.noConfusion (hm.symm.trans hm')⟩
  case fpp_done =>
    rename_i hm hi
    have hrad : t.radius = s.radius := (congrArg GalilVM.radius hi.2).trans rfl
    have hrem : t.remaining = s.remaining := (congrArg GalilVM.remaining hi.2).trans rfl
    have hce : t.center = s.center := (congrArg GalilVM.center hi.2).trans rfl
    have hr : t.right = s.right := (congrArg GalilVM.right hi.2).trans rfl
    exact ⟨by rw [hrad]; exact hcan, by rw [hrem]; exact hcanr, by rw [hrad]; exact hnn,
      by rw [hrad, hce, hr]; exact hle, fun hm' => Mode.noConfusion hm', fun hm' => Mode.noConfusion hm'⟩
  case markEnd_step =>
    rename_i hm he hi
    have hrad : t.radius = s.radius := (congrArg GalilVM.radius hi.2).trans rfl
    have hrem : t.remaining = s.remaining := (congrArg GalilVM.remaining hi.2).trans rfl
    have hce : t.center = s.center := (congrArg GalilVM.center hi.2).trans rfl
    have hr : t.right = s.right := (congrArg GalilVM.right hi.2).trans rfl
    exact ⟨by rw [hrad]; exact hcan, by rw [hrem]; exact hcanr, by rw [hrad]; exact hnn,
      by rw [hrad, hce, hr]; exact hle, fun hm' => Mode.noConfusion (hm.symm.trans hm'), fun hm' => Mode.noConfusion (hm.symm.trans hm')⟩
  case markEnd_found =>
    rename_i hm he hi
    have hrad : t.radius = s.radius := (congrArg GalilVM.radius hi.2).trans (by rw [hi.1.2]; rfl)
    have hrem : t.remaining = s.remaining := (congrArg GalilVM.remaining hi.2).trans (by rw [hi.1.2]; rfl)
    have hce : t.center = s.center := (congrArg GalilVM.center hi.2).trans (by rw [hi.1.2]; rfl)
    have hr : t.right = s.right := (congrArg GalilVM.right hi.2).trans (by rw [hi.1.2]; rfl)
    exact ⟨by rw [hrad]; exact hcan, by rw [hrem]; exact hcanr, by rw [hrad]; exact hnn,
      by rw [hrad, hce, hr]; exact hle, fun hm' => Mode.noConfusion hm', fun hm' => Mode.noConfusion hm'⟩
  case choose_step =>
    rename_i hm hs hi
    have hrad : t.radius = s.radius := (congrArg GalilVM.radius hi.2).trans (by rw [hi.1.2]; rfl)
    have hrem : t.remaining = s.remaining := (congrArg GalilVM.remaining hi.2).trans (by rw [hi.1.2]; rfl)
    have hce : t.center = s.center := (congrArg GalilVM.center hi.2).trans (by rw [hi.1.2]; rfl)
    have hr : t.right = s.right := (congrArg GalilVM.right hi.2).trans (by rw [hi.1.2]; rfl)
    exact ⟨by rw [hrad]; exact hcan, by rw [hrem]; exact hcanr, by rw [hrad]; exact hnn,
      by rw [hrad, hce, hr]; exact hle, fun hm' => Mode.noConfusion (hm.symm.trans hm'), fun hm' => Mode.noConfusion (hm.symm.trans hm')⟩
  case rewind_done =>
    rename_i hm hfi hi
    have hrad : t.radius = s.radius := (congrArg GalilVM.radius hi.2).trans (by rw [hi.1]; rfl)
    have hrem : t.remaining = s.remaining := (congrArg GalilVM.remaining hi.2).trans (by rw [hi.1]; rfl)
    have hce : t.center = s.center := (congrArg GalilVM.center hi.2).trans (by rw [hi.1]; rfl)
    have hr : t.right = s.right := (congrArg GalilVM.right hi.2).trans (by rw [hi.1]; rfl)
    exact ⟨by rw [hrad]; exact hcan, by rw [hrem]; exact hcanr, by rw [hrad]; exact hnn,
      by rw [hrad, hce, hr]; exact hle, fun hm' => Mode.noConfusion hm', fun hm' => Mode.noConfusion hm'⟩

#print axioms compare_radius
#print axioms compare_remaining
#print axioms radLedger_tick

end Tick

/-! ## 4. The three fields this file does *not* close, and why

`leftLive`.  `LeftLive` is a liveness statement about `L` (`0 < position L` at a
scan comparison and in `rewind` mode).  It is the exact analogue of `CentreLive`,
and `CentreLive` is *not* proved by a tick induction either: it is proved by a
run argument out of an `InvLP` state (`GalilCentreLive.centreLive_of_invLP_run`,
fed by the length floor `hfloor`).  A tick induction on `LeftLive` alone fails
immediately at `scan_match`/`rewind_one`/`rewind_pair`, where `L` moves left and
nothing local says it has not reached the clipped origin.  The route is the
`L`-analogue of `GalilCentreLive`, not this file.

`verSane`.  `Sane` of the chain verifier is preserved by `chainStart`
(`verOf (chainStart .. ver ..) = some ver` with `ver = s.center`, so `Sane C`
does it) and by a verifier right move — but only given `canRight` of the
*verifier*, which is a frontier statement about the chain head, not about `R`.
`GalilFrontMono.FrontPack` budgets `R`, not the verifier.  The missing input is
a verifier-side frontier bound (`position ver + k ≤ 2 * arrived ver`); until it
exists, `verSane` cannot travel across `chainTick`.

`shiftLC` / `shiftCR`.  These are the two clauses whose transport *fails on a
real branch*, and the failure is quantitative, not a missing lemma.

* Entry (`scan_shift`) is fine: `L` moves left, `C` stays, `R` moves right, so
  `position L ≤ position C ≤ position R` (the non-strict order) already gives
  both strict inequalities at the landing state.
* `shift_one` is where it breaks.  `shiftTick` moves `C` one place right and `L`
  *two* places right (`shiftTick = ⟨right center, right (right left), …⟩`), so
  each shift unit eats one unit of `C - L` slack and one unit of `R - C` slack.
  The pre-state's `position L + 1 ≤ position C` and `position C + 1 ≤ position R`
  therefore do **not** reproduce themselves: `shift_one` needs
  `position L + 2 ≤ position C` and `position C + 2 ≤ position R`.

  The honest repair is the same one this file used for the radius: carry the
  budget, not its one-step consequence, i.e. replace the two clauses by

      c.mode = Mode.shift → (position s.left : ℤ) + 2 * value s.remaining + 1
                              ≤ position s.center
      c.mode = Mode.shift → (position s.center : ℤ) + value s.remaining + 1
                              ≤ position s.right

  Both are stable under `shiftTick` (`L` gains 2 and `remaining` loses 1; `C`
  gains 1 and `remaining` loses 1), and both imply the original clauses because
  `0 ≤ value remaining`.

  The second one, however, is *not* available at the shift entry from anything
  proved today.  `GalilChainCoupling.budget_of_coupled` gives exactly
  `periodLength w ≤ value s'.radius`, and `beginShiftVM` sets
  `remaining := ofNat (periodLength w)`, so at the landing state one gets
  `value remaining ≤ value radius` — which is precisely `RadLedger.shiftBud`,
  and which, combined with `RadLedger.le`, yields only

      position C + value remaining ≤ position R

  i.e. the *non-strict* form.  The `+1` is missing.  Consequently `RadPack.shiftCR`
  as written (`c.mode = Mode.shift → position C + 1 ≤ position R`, with no guard
  on `remaining`) is claimed also at the state reached by the last `shift_one`,
  where `remaining = 0` and `position C = position R` is not excluded.  Either
  the clause must be guarded by `positive s.remaining = true` (which is all the
  `GalilTrailOrder` induction ever consumes — `shift_one` fires only under
  `remainingPos`), or the shift-entry budget must be sharpened from
  `periodLength w ≤ radius` to `periodLength w + 1 ≤ radius`.  Neither is done
  here, and neither is assumed.
-/

end PalPeg.CloseoutRadPack
