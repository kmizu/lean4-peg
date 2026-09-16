import PalPeg.GalilTrailBudget
import PalPeg.GalilInvPlus2
import PalPeg.GalilCentreLive
import PalPeg.GalilFrontMono
import PalPeg.GalilBootVM
import PalPeg.GalilRunInv
import PalPeg.GalilMainLoopMInv
import PalPeg.GalilGlueBLeaves

/-!
# `H_frontTrace`, discharged

`GalilTrailBudget.H_frontTrace` asks, along every pre-loaded trace, for

* monotonicity of the frontier `front = position right + replay`,
* a non-negative replay counter,
* `ReplayRest` (the `replaying` flag and the counter agree at rest).

All three are fields of `GalilFrontMono.FrontPack` (the last two literally, the
first through `GalilFrontMono.front_steps_mono`), so the whole obligation is the
availability of `FrontPack` at every state of the trace, plus `CentreLive` along
every run out of it.

The trace starts at `GalilFinalAssembly.boot w`, which is in `init` mode, so
`FrontPack` does **not** hold there (`notInit`).  The boot state is handled on
its own: its replay counter is empty, its mode is `init` (so `ReplayRest` is
free), and its frontier is `0`, which the `init` tick can only increase.  From
tick `1` on, the landing of the `init` tick is `Inv` (`init_tick_inv` inverts
the tick the trace supplies — `PreTrace` does not record where the trace came
from, so the landing must be recomputed from the tick itself), hence `InvLP`,
hence `InvLP2` from the boot (`GalilInvPlus2.invLP2_of_boot`), which pays
`hfloor` (`hfloor_of_invLP2`), hence `CentreLive` along every run
(`GalilCentreLive.centreLive_of_invLP_run`), hence the pack travels.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.GalilTrailFront

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilFinalAssembly PalPeg.GalilCheckpoints PalPeg.GalilRunSkeleton
open PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open GalilScaffoldCounter GalilScaffoldInputHead

/-! ## 1. Runs inside a trace -/

theorem steps_of_trace {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {st : ℕ → State GalilVM} {e : ℕ}
    (h : Trace (galilFrameS P q first) 2048 (SoundScanNR raw) st e) :
    ∀ i n, i + n ≤ e → Steps (galilFrameS P q first) 2048 n (st i) (st (i + n)) := by
  intro i n
  induction n generalizing i with
  | zero => intro _; exact .zero _
  | succ n ih =>
    intro hi
    have h2 : Steps (galilFrameS P q first) 2048 n (st (i + 1)) (st (i + (n + 1))) := by
      have hh := ih (i + 1) (by omega)
      rwa [show i + 1 + n = i + (n + 1) by omega] at hh
    exact .succ (h.tick i (by omega)) h2

theorem steps_between {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {st : ℕ → State GalilVM} {e i j : ℕ}
    (h : Trace (galilFrameS P q first) 2048 (SoundScanNR raw) st e)
    (hij : i ≤ j) (hj : j ≤ e) :
    Steps (galilFrameS P q first) 2048 (j - i) (st i) (st j) := by
  have hh := steps_of_trace h i (j - i) (by omega)
  rwa [show i + (j - i) = j by omega] at hh

/-! ## 2. Inverting the `init` tick -/

/-- A tick out of `init` mode is *the* `init` tick: the controller enters a
fresh scan and the VM is an `init` landing.  `PreTrace` only records that its
first tick is a tick, so the landing has to be recomputed here. -/
theorem init_tick_inv {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ}
    {c c' : Control} {s t : GalilVM} (hm : c.mode = Mode.init)
    (ht : Tick (galilFrameS P q first) delay ⟨c, s⟩ ⟨c', t⟩) :
    c' = {c with mode := Mode.scan, output := true} ∧ P.init s t := by
  cases ht <;> first
    | exact ⟨rfl, by assumption⟩
    | exact absurd (hm.symm.trans ‹c.mode = Mode.scan›) (by decide)
    | exact absurd (hm.symm.trans ‹c.mode = Mode.shift›) (by decide)
    | exact absurd (hm.symm.trans ‹c.mode = Mode.copy›) (by decide)
    | exact absurd (hm.symm.trans ‹c.mode = Mode.home›) (by decide)
    | exact absurd (hm.symm.trans ‹c.mode = Mode.fpp›) (by decide)
    | exact absurd (hm.symm.trans ‹c.mode = Mode.markEnd›) (by decide)
    | exact absurd (hm.symm.trans ‹c.mode = Mode.choose›) (by decide)
    | exact absurd (hm.symm.trans ‹c.mode = Mode.rewind›) (by decide)
    | exact absurd (hm.symm.trans ‹c.mode = Mode.replayStart›) (by decide)

/-- The landing of the boot tick is a radius-`0` restart with the span
relation, i.e. `Inv` — `GalilCheckpoints.inv_init_pos` for *the given* tick
instead of an existentially produced one. -/
theorem inv_of_boot_tick (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (a : Fin 2) (rest : List (Fin 2)) {y : State GalilVM}
    (ht : Tick (galilFrameS (PofC centre place entry (a :: rest)) q first) 2048
      (boot (a :: rest)) y) :
    Inv (a :: rest) y.ctl y.vm ∧ SpanRep y.vm ∧
      y.vm.right = GalilScaffoldChainVerifier.right (initialHead (a :: rest)) ∧
      y.vm.replay = reset := by
  obtain ⟨hc', hi⟩ :=
    init_tick_inv (P := PofC centre place entry (a :: rest)) (q := q) (first := first)
      (delay := 2048) (c := GalilScaffoldController.initial 2048)
      (s := GalilBootVM.initVM0 (a :: rest)) (c' := y.ctl) (t := y.vm) rfl ht
  have hi' : initVM entry (GalilBootVM.initVM0 (a :: rest)) y.vm := hi
  obtain ⟨hR, hL, hC, hlen, hrad, hrem, hrep, hcyc, hfpp, hchain, hsearch, hlower, hdp⟩ := hi'
  have hR0 : y.vm.right = GalilScaffoldChainVerifier.right (initialHead (a :: rest)) := hR
  have hL0 : y.vm.left = GalilScaffoldChainVerifier.right (initialHead (a :: rest)) := hL
  have hC0 : y.vm.center = GalilScaffoldChainVerifier.right (initialHead (a :: rest)) := hC
  have hrad0 : y.vm.radius = reset := hrad
  have hlen1 : y.vm.length = ofNat 1 := by rw [hlen]; exact inc_ofNat 0
  have hrep0 : y.vm.replay = reset := hrep
  have hsearch0 : y.vm.search = GalilScaffoldSearchFinish.begin reset reset := hsearch
  have hlower0 : y.vm.lower = reset := hlower
  have hRest : Restarted (a :: rest) y.vm 0 reset := by
    refine ⟨hchain, ?_, ?_, ?_, ?_, ?_, ?_, hlower0, ofNat_canonical 0, by decide⟩
    · rw [hC0]; exact initialHead_right_represents a rest
    · rw [hC0]; exact initialHead_right_focus a rest
    · rw [hL0, hR0, hC0]
      exact scan_initial _ _ (initialHead_right_represents a rest)
        (initialHead_right_focus a rest)
    · rw [hrad0]; exact ⟨ofNat_canonical 0, rfl⟩
    · rw [hlen1]; exact ofNat_canonical 1
    · rw [hsearch0, hrad0]
  have hmode : y.ctl.mode = Mode.scan ∧ y.ctl.replaying = false ∧ y.ctl.clock = 2048 := by
    rw [hc']; exact ⟨rfl, rfl, rfl⟩
  have hMt : MInv (a :: rest) y.ctl y.vm := by
    refine minv_of_leftmost ?_ hmode.2.1
    rw [hR0, hC0, initialHead_right_position a rest]
    exact leftmost_one a rest
  have hsi : ShiftIdle y.vm := by
    rw [shiftIdle_iff, hrem]
    exact (shiftIdle_iff (GalilBootVM.initVM0 (a :: rest))).1
      (GalilBootVM.initVM0_shiftIdle (a :: rest))
  exact ⟨inv_of_parts hRest hMt hmode (frontier_of_reset hrep0) (replayRest_of_reset hrep0) hsi,
    spanRep_of_init hlen hrad rfl rfl, hR0, hrep0⟩

/-! ## 3. The replay counter is non-negative inside the pack -/

theorem replay_nonneg {c : Control} {s : GalilVM} (h : PalPeg.GalilFrontMono.FrontPack c s) :
    0 ≤ value s.replay := by
  cases hr : c.replaying with
  | false => rw [h.rest (Or.inl hr)]; decide
  | true =>
    obtain ⟨m, hm⟩ := h.replayPos hr
    rw [hm, ofNat_value]
    omega

/-! ## 4. The obligation -/

theorem h_frontTrace (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) :
    PalPeg.GalilTrailBudget.H_frontTrace centre place entry q first := by
  intro w hw st Tc hP
  rcases w with _ | ⟨a, rest⟩
  · exact absurd hw (by simp)
  have hb : st 0 = boot (a :: rest) := hP.start
  have h0replay : (st 0).vm.replay = reset := by rw [hb]; rfl
  have h0rest : ReplayRest (st 0).ctl (st 0).vm := replayRest_of_reset h0replay
  have h0front : PalPeg.GalilRunTrace.front (st 0).vm = 0 := by rw [hb]; rfl
  by_cases hN : 1 ≤ Tc (a :: rest).length
  · -- the boot tick and its landing
    have hstep0 : Tick (galilFrameS (PofC centre place entry (a :: rest)) q first) 2048
        (boot (a :: rest)) (st 1) := by
      have h := hP.trace.tick 0 (by omega)
      rwa [hb] at h
    obtain ⟨hInv, hSpan, hR1, hrep1⟩ :=
      inv_of_boot_tick centre place entry q first a rest hstep0
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
    -- the pack at every later state
    have packAt : ∀ k, 1 ≤ k → k ≤ Tc (a :: rest).length →
        PalPeg.GalilFrontMono.FrontPack (st k).ctl (st k).vm ∧
          Steps (galilFrameS (PofC centre place entry (a :: rest)) q first) 2048 (k - 1)
            (st 1) (st k) := by
      intro k h1 hk
      have hs := steps_between hP.trace h1 hk
      refine ⟨?_, hs⟩
      exact (PalPeg.GalilFrontMono.front_steps_mono (onLetterVM (a :: rest)) leftFirstVM
        centre place entry q first 2048 hs (fun m z hz => hlive m z hz) hFP1).1
    have monoFrom : ∀ i j, 1 ≤ i → i ≤ j → j ≤ Tc (a :: rest).length →
        PalPeg.GalilRunTrace.front (st i).vm ≤ PalPeg.GalilRunTrace.front (st j).vm := by
      intro i j h1 hij hj
      obtain ⟨hFPi, hs1i⟩ := packAt i h1 (by omega)
      have hsij := steps_between hP.trace hij hj
      refine (PalPeg.GalilFrontMono.front_steps_mono (onLetterVM (a :: rest)) leftFirstVM
        centre place entry q first 2048 hsij ?_ hFPi).2
      intro m z hz
      exact hlive ((i - 1) + m) z (steps_trans hs1i hz)
    have h01 : PalPeg.GalilRunTrace.front (st 0).vm ≤ PalPeg.GalilRunTrace.front (st 1).vm := by
      rw [h0front, PalPeg.GalilRunTrace.front_ofNat (m := 0) hrep1, hR1,
        initialHead_right_position a rest]
      decide
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij hj
      rcases Nat.eq_zero_or_pos i with rfl | hi1
      · rcases Nat.eq_zero_or_pos j with rfl | hj1
        · exact le_rfl
        · exact le_trans h01 (monoFrom 1 j le_rfl hj1 hj)
      · exact monoFrom i j hi1 hij hj
    · intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hi1
      · rw [h0replay]; decide
      · exact replay_nonneg (packAt i hi1 hi).1
    · intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hi1
      · exact h0rest
      · exact ((packAt i hi1 hi).1).rest
  · have hz : Tc (a :: rest).length = 0 := by omega
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij hj
      rw [hz] at hj
      have hi0 : i = 0 := by omega
      have hj0 : j = 0 := by omega
      rw [hi0, hj0]
    · intro i hi
      rw [hz] at hi
      have hi0 : i = 0 := by omega
      rw [hi0, h0replay]; decide
    · intro i hi
      rw [hz] at hi
      have hi0 : i = 0 := by omega
      rw [hi0]; exact h0rest

#print axioms steps_of_trace
#print axioms steps_between
#print axioms init_tick_inv
#print axioms inv_of_boot_tick
#print axioms replay_nonneg
#print axioms h_frontTrace

end PalPeg.GalilTrailFront
