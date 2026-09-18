import PalPeg.CloseoutRadPack

/-!
# The shift-order budget: `RadPack.shiftLC` / `shiftCR` in stable form

`CloseoutRadPack` §4 diagnosed why the two shift-order clauses of
`GalilTrailRad.RadPack` do not travel along `shift_one`: the tick moves `L` two
places right and `C` one place right, so each shift unit eats one unit of the
`C − L` slack and one unit of the `R − C` slack, and the one-step consequences
`L + 1 ≤ C`, `C + 1 ≤ R` do not reproduce themselves.

This file carries the *budget* instead of its one-step consequence, exactly as
`CloseoutRadPack` did for the radius:

    ShiftBud s := 0 ≤ remaining
               ∧ L + 2 · remaining + 1 ≤ C
               ∧ C +     remaining + 1 ≤ R

`ShiftOrd c s` asserts `ShiftBud s` whenever the controller is in `shift` mode.
Both conjuncts are stable under `shiftTick` (`L` gains at most 2, `C` gains
exactly 1, `remaining` loses exactly 1), and both imply the original unguarded
clauses because `0 ≤ remaining`.  So `ShiftOrd` + `RadLedger` deliver
`GalilTrailOrder.OrderBudget` and the two `RadPack` shift fields with **no**
`positive remaining` guard — the guard discussed in `CloseoutRadPack` §4 is not
needed once the budget, rather than its consequence, is the invariant.

**Proved here, unconditionally**: `shiftBud` at boot, transport along all 23
constructors of one `galilFrameS` tick *except* the shift entry, and the
assembly `RadLedger ∧ ShiftOrd ∧ LeftLive ∧ verSane → RadPack`, hence
`H_trailF` from the corresponding trace-level hypotheses.

**Named residual**: `H_shiftEntry`.  At `scan_shift`, `beginShiftVM` sets
`remaining := ofNat (periodLength w)`, and the strongest entry fact available
today is `GalilChainCoupling.budget_of_coupled`, i.e.
`periodLength w ≤ value s'.radius`, which through `RadLedger.le` yields only the
non-strict `C + remaining ≤ R` and says nothing at all about `C − L`.  What the
budget form needs is `2 · periodLength w + 1 ≤ C − L` and
`periodLength w + 1 ≤ R − C` at the landing state; both are Galil-combinatorial
statements about the chain window, not head arithmetic, so they are named, not
assumed away inside a proof.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutRadPack2

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilThrottledRun PalPeg.GalilTrailProof PalPeg.GalilFinalAssembly
open PalPeg.GalilTrailScan PalPeg.GalilTrailBudget PalPeg.GalilTrailChain
open PalPeg.GalilTrailAssembly PalPeg.GalilTrailRad PalPeg.CloseoutRadPack

/-! ## 1. The budget -/

/-- **The shift budget at one state.** -/
structure ShiftBud (s : GalilVM) : Prop where
  nonneg : 0 ≤ GalilScaffoldCounter.value s.remaining
  lcB : (position s.left : ℤ) + 2 * GalilScaffoldCounter.value s.remaining + 1
          ≤ (position s.center : ℤ)
  crB : (position s.center : ℤ) + GalilScaffoldCounter.value s.remaining + 1
          ≤ (position s.right : ℤ)

/-- The budget, asserted exactly while the controller shifts. -/
def ShiftOrd (c : Control) (s : GalilVM) : Prop := c.mode = Mode.shift → ShiftBud s

/-- The budget implies the unguarded `RadPack.shiftLC`. -/
theorem shiftLC_of_shiftOrd {c : Control} {s : GalilVM} (h : ShiftOrd c s) :
    c.mode = Mode.shift → position s.left + 1 ≤ position s.center := by
  intro hm
  obtain ⟨hn, hl, -⟩ := h hm
  omega

/-- The budget implies the unguarded `RadPack.shiftCR`. -/
theorem shiftCR_of_shiftOrd {c : Control} {s : GalilVM} (h : ShiftOrd c s) :
    c.mode = Mode.shift → position s.center + 1 ≤ position s.right := by
  intro hm
  obtain ⟨hn, -, hr⟩ := h hm
  omega

#print axioms shiftLC_of_shiftOrd
#print axioms shiftCR_of_shiftOrd

/-! ## 2. The boot state -/

theorem shiftOrd_boot (w : List (Fin 2)) : ShiftOrd (boot w).ctl (boot w).vm := by
  intro hm
  exact absurd (show Mode.init = Mode.shift from hm) (by decide)

#print axioms shiftOrd_boot

/-! ## 3. Transport along one tick -/

section Tick
variable (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
  (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)

/-- **The shift budget travels along every tick of `galilFrameS`**, given the
shift-entry budget `hentry` (see the module docstring). -/
theorem shiftOrd_tick {c c' : Control} {s t : GalilVM} (hS : ShiftOrd c s)
    (hcanr : GalilScaffoldCounter.Canonical s.remaining)
    (hsaneC : GalilFrontMono.Sane s.center)
    (hcopy : c.mode = Mode.shift → CopyIdle s)
    (hentry : ∀ s'' t'' : GalilVM,
      (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).compare s s'' →
      beginShiftVM' s'' t'' → ShiftBud t'')
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : ShiftOrd c' t := by
  cases h
  case init => exact fun hm' => Mode.noConfusion hm'
  case scan_wait =>
    rename_i hm hav hb
    exact fun hm' => Mode.noConfusion (hm.symm.trans hm')
  case scan_count =>
    rename_i hm hc hav hb
    exact fun hm' => Mode.noConfusion (hm.symm.trans hm')
  case restart =>
    rename_i hm hb
    exact fun hm' => Mode.noConfusion (hm.symm.trans hm')
  case scan_match =>
    rename_i s' o hmt hm hc hcmp hav hpl ho
    exact fun hm' => Mode.noConfusion (hm.symm.trans hm')
  case scan_shift =>
    rename_i s' hmt hg hm hc hr hcmp hav hb
    exact fun _ => hentry s' t hcmp hb
  case scan_fallback =>
    rename_i s' hmt hm hc hg hr hcmp hav hb
    exact fun hm' => Mode.noConfusion hm'
  case shift_one =>
    rename_i hm hp hi
    obtain ⟨hcC, hcL, hcL2, w, hw, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    obtain ⟨hn, hlc, hcr⟩ := hS hm
    have hposR : GalilScaffoldCounter.positive s.remaining = true := by
      rcases hp with h1 | h2
      · exact h1
      · exact absurd h2 (hcopy hm)
    have hpos : 0 < GalilScaffoldCounter.value s.remaining :=
      (GalilScaffoldCounter.positive_iff _ hcanr).1 hposR
    have hl2 : t.left =
        GalilScaffoldChainVerifier.right (GalilScaffoldChainVerifier.right s.left) := by
      rw [ht]; rfl
    have hce2 : t.center = GalilScaffoldChainVerifier.right s.center := by rw [ht]; rfl
    have hr2 : t.right = s.right := by rw [ht]; rfl
    have hrem2 : t.remaining = GalilScaffoldCounter.dec s.remaining := by rw [ht]; rfl
    have hstepC : position (GalilScaffoldChainVerifier.right s.center) = position s.center + 1 :=
      (GalilFrontMono.right_sane hcC hsaneC).1
    have hL1 := PalPeg.GalilTrailOrder.pos_right_le s.left
    have hL2 := PalPeg.GalilTrailOrder.pos_right_le (GalilScaffoldChainVerifier.right s.left)
    refine fun _ => ⟨?_, ?_, ?_⟩
    · rw [hrem2, GalilScaffoldCounter.dec_value]; omega
    · rw [hrem2, hl2, hce2, GalilScaffoldCounter.dec_value, hstepC]
      have : (position (GalilScaffoldChainVerifier.right
          (GalilScaffoldChainVerifier.right s.left)) : ℤ) ≤ (position s.left : ℤ) + 2 := by
        omega
      omega
    · rw [hrem2, hce2, hr2, GalilScaffoldCounter.dec_value, hstepC]
      omega
  case shift_done =>
    rename_i o hm hp ho
    exact fun hm' => Mode.noConfusion hm'
  case replayStart =>
    rename_i o hm ho ho' hi
    exact fun hm' => Mode.noConfusion hm'
  case choose_select =>
    rename_i hm hodd hs hi
    exact fun hm' => Mode.noConfusion hm'
  case rewind_pair =>
    rename_i hm hfi hpr hi
    exact fun hm' => Mode.noConfusion (hm.symm.trans hm')
  case rewind_one =>
    rename_i hm hfi hpr hi
    exact fun hm' => Mode.noConfusion (hm.symm.trans hm')
  case copy_one =>
    rename_i hm hp hi
    exact fun hm' => Mode.noConfusion (hm.symm.trans hm')
  case copy_done =>
    rename_i hm hp hi
    exact fun hm' => Mode.noConfusion hm'
  case home_start =>
    rename_i hm hl hi
    exact fun hm' => Mode.noConfusion hm'
  case home_step =>
    rename_i hm hl hi
    exact fun hm' => Mode.noConfusion (hm.symm.trans hm')
  case fpp_slice =>
    rename_i hm hi
    exact fun hm' => Mode.noConfusion (hm.symm.trans hm')
  case fpp_done =>
    rename_i hm hi
    exact fun hm' => Mode.noConfusion hm'
  case markEnd_step =>
    rename_i hm he hi
    exact fun hm' => Mode.noConfusion (hm.symm.trans hm')
  case markEnd_found =>
    rename_i hm he hi
    exact fun hm' => Mode.noConfusion hm'
  case choose_step =>
    rename_i hm hs hi
    exact fun hm' => Mode.noConfusion (hm.symm.trans hm')
  case rewind_done =>
    rename_i hm hfi hi
    exact fun hm' => Mode.noConfusion hm'

#print axioms shiftOrd_tick

end Tick

/-! ## 4. Assembly: `RadPack` at one state -/

/-- `RadLedger` (the radius ledger of `CloseoutRadPack`) plus the shift budget
plus the two genuinely non-arithmetic residuals give `GalilTrailRad.RadPack`. -/
theorem radPack_of_parts {c : Control} {s : GalilVM}
    (hL : RadLedger c s) (hS : ShiftOrd c s)
    (hll : PalPeg.GalilTrailSane.LeftLive c s)
    (hv : ∀ p, verOf s.chain = some p → GalilFrontMono.Sane p)
    -- **`M-watchBreak` 修正で現れた義務**（`RadPack.noBgBreak`）。
    (hnb : PalPeg.GalilTrailAssembly.NoBgBreak s.chain) :
    RadPack c s :=
  ⟨hll, shiftLC_of_shiftOrd hS, shiftCR_of_shiftOrd hS, startLe_of_radLedger hL, hv, hnb⟩

#print axioms radPack_of_parts

/-! ## 5. Trace level, and `H_trailF` -/

section Hyps
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- The radius ledger along every pre-loaded trace. -/
def H_radLedger : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    ∀ i, i ≤ Tc w.length → RadLedger (st i).ctl (st i).vm

/-- The shift budget along every pre-loaded trace. -/
def H_shiftOrd : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    ∀ i, i ≤ Tc w.length → ShiftOrd (st i).ctl (st i).vm

/-- `LeftLive` along every pre-loaded trace. -/
def H_leftLive : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    ∀ i, i ≤ Tc w.length → PalPeg.GalilTrailSane.LeftLive (st i).ctl (st i).vm

/-- Saneness of the chain verifier along every pre-loaded trace. -/
def H_verSane : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    ∀ i, i ≤ Tc w.length → ∀ p, verOf (st i).vm.chain = some p → GalilFrontMono.Sane p

/-- **`M-watchBreak` 修正で現れた trace 水準の義務。** 背景 break は verifier を 1 進め
ながら lag を減らさないので lag 台帳が 1 だけ破れる。 -/
def H_noBgBreak : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc,
    PreTrace centre place entry q first w st Tc → ∀ i, i ≤ Tc w.length →
      PalPeg.GalilTrailAssembly.NoBgBreak (st i).vm.chain

theorem h_radPack_of_parts (hL : H_radLedger centre place entry q first)
    (hS : H_shiftOrd centre place entry q first)
    (hll : H_leftLive centre place entry q first)
    (hv : H_verSane centre place entry q first)
    (hnb : H_noBgBreak centre place entry q first) :
    H_radPack centre place entry q first :=
  fun w hw st Tc hP i hi =>
    radPack_of_parts (hL w hw st Tc hP i hi) (hS w hw st Tc hP i hi)
      (hll w hw st Tc hP i hi) (hv w hw st Tc hP i hi) (hnb w hw st Tc hP i hi)

/-- **`H_trailF` from the four trace-level parts.** -/
theorem h_trailF_of_parts' (hL : H_radLedger centre place entry q first)
    (hS : H_shiftOrd centre place entry q first)
    (hll : H_leftLive centre place entry q first)
    (hv : H_verSane centre place entry q first)
    (hnb : H_noBgBreak centre place entry q first) :
    H_trailF centre place entry q first :=
  h_trailF_of_radPack centre place entry q first
    (h_radPack_of_parts centre place entry q first hL hS hll hv hnb)

end Hyps

#print axioms h_radPack_of_parts
#print axioms h_trailF_of_parts'

end PalPeg.CloseoutRadPack2
