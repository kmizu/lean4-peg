import PalPeg.LocalRealizesPhase
import PalPeg.LocalRealizesScan

/-!
# 局所化計画: the local well-formedness pack of `LocalSysConcrete`

The LOCAL-side residuals of `LocalRealizesPhase` / `LocalRealizesScan` that do
not need abstract-tick determinism.

## Closed here

* **`PhaseNoReplay`** (§1).  "A phase mode never replays" is a *trace*
  invariant: the only ticks entering `shift`/`copy` are `scan_shift` and
  `scan_fallback`, both of which carry `c.replaying = false`, and no tick inside
  the seven phase modes touches `replaying` (`noReplay_tick`).  `Needy` pins the
  whole controller record, so it transports to the local state
  (`phaseNoReplay_of_trace`, `notReplaying_of_trace`).  Residual: the invariant
  at time `0`, which `noReplay_zero_of_init` discharges for a trace starting in
  `init`.
* **`H_fpp` / `H_fpp_mir`** (§2).  `ffpp` is defined concretely (the scaffold
  tick out of `m.vm` that leaves the centre alone), and `exists_fppTick` builds
  one from the trace tick: `tick_fpp_cases` hands over the abstract
  `fppSlice`/`fppDone` block, whose `GalilScaffoldControl.Run` and target tapes
  are mirrored on the double buffer by `exists_fppRun`
  (`LocalBuffers.abs_stepL`).  `H_fpp_mir` is unconditional.
* **The polarity bundle `PolWF`** (§4, §7): no `TickL3` step and no arrival
  touches `pol`, so `PolWF` is preserved by `tickC`/`feedC` once the three open
  steps (`init`/`scan`/`replayStart`) keep it, and holds at `x0C`.
* **Two of the counter side conditions are free** (§3): the shift reading of
  `remainingPos` *is* `positive remaining`, which pins the sign bit **and** the
  tape value (`remaining_of_shiftRemaining`); the copy reading pins
  `0 < val fppWork` (`work_of_copyRemaining`).
* **The pack and its consumers** (§5, §6): `LocalWF` is the polarity bundle `PolWF`.  Together
  with the counter magnitudes read off the trace (`shiftMagnitudes_of_trace`,
  `copyRemaining_of_trace`) and the walker's sentinel carried by `PhysWF`, it yields
  `ShiftCounters`, `CopySide`, `RewindWF`, `ChooseWF`, and `realizes_seven`
  assembles seven of the ten `Realizes` obligations.

## Residuals (§8)

The polarity half of the three modes whose local step is still open.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.dupNamespace false
set_option maxHeartbeats 1000000

namespace PalPeg.LocalWF

variable {lastTick : ℕ}

open PalPeg.GalilScaffoldTop
open PalPeg.GalilScaffoldController (Control Mode)
open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.LocalState
open PalPeg.LocalArrival (abs' absState' absHead')
open PalPeg.LocalReplayParked (abs'' absState'' Mirrored1 MirInv1)
open PalPeg.LocalSysConcrete (PhysWF InvC Needy Tracked Starved Realizes)
open PalPeg.GalilThrottledRun (truncS)

/-! ## 1. "A phase mode never replays" is a trace invariant -/

/-- The seven modes in which the machine is running a fallback phase. -/
def PhaseMode (md : Mode) : Prop :=
  md = .shift ∨ md = .copy ∨ md = .home ∨ md = .fpp ∨ md = .markEnd ∨ md = .choose ∨ md = .rewind

/-- The trace-side invariant: in a phase mode the controller is not replaying. -/
def NoReplay {σ : Type} (t : State σ) : Prop :=
  PhaseMode t.ctl.mode → t.ctl.replaying = false

theorem noReplay_tick {σ : Type} {F : Frame σ} {delay : ℕ} {x y : State σ}
    (h : Tick F delay x y) (hx : NoReplay x) : NoReplay y := by
  unfold NoReplay PhaseMode at hx ⊢
  cases h <;> intro hm <;> simp_all

theorem noReplay_run {σ : Type} {F : Frame σ} {delay : ℕ} {stOf : ℕ → State σ}
    (H_trace : ∀ k, k < lastTick → Tick F delay (stOf k) (stOf (k+1)))
    (H_afterLast : ∀ k, lastTick ≤ k → stOf k = stOf lastTick) (h0 : NoReplay (stOf 0)) :
    ∀ k, NoReplay (stOf k) := by
  have hbelow : ∀ k, k ≤ lastTick → NoReplay (stOf k) := by
    intro k
    induction k with
    | zero => exact fun _ => h0
    | succ k ih => exact fun hk => noReplay_tick (H_trace k (by omega)) (ih (by omega))
  intro k
  rcases Nat.le_total k lastTick with hk | hk
  · exact hbelow k hk
  · rw [H_afterLast k hk]
    exact hbelow lastTick le_rfl

/-- A trace that starts in `init` (as `GalilScaffoldController.initial` does)
satisfies the invariant at `0`. -/
theorem noReplay_zero_of_init {σ : Type} {stOf : ℕ → State σ} (h : (stOf 0).ctl.mode = .init) :
    NoReplay (stOf 0) := by
  intro hm; unfold PhaseMode at hm; rw [h] at hm; simp at hm

variable {P : ℕ}

variable {Good : Mirrored1 P → Prop}

/-- The tracking datum pins the *whole* controller record, so every control-flow
fact of the trace transports to the local state. -/
theorem ctl_of_needy {raw : List (Fin 2)} {stOf : ℕ → State GalilVM} {k j : ℕ}
    {x : GalilVML P} (h : Needy raw stOf k j x) : x.ctl = (stOf k).ctl :=
  congrArg (fun s => s.ctl) h.2

/-- **`PhaseNoReplay` is closed**, from the trace invariant. -/
theorem phaseNoReplay_of_trace {raw : List (Fin 2)} {stOf : ℕ → State GalilVM}
    (h : ∀ k, NoReplay (stOf k)) : PalPeg.LocalRealizesPhase.PhaseNoReplay (P := P) Good raw stOf := by
  intro m hinv hmd
  obtain ⟨k, j, hn⟩ := hinv.track
  have hc : m.vm.ctl = (stOf k).ctl := ctl_of_needy hn
  rw [hc]
  refine h k ?_
  unfold PhaseMode
  rw [← hc]
  rcases hmd with h1 | h1 | h1 | h1 | h1 <;> simp [h1]

/-- The same for the two `rewind`/`choose` modes of `LocalRealizesScan`. -/
theorem notReplaying_of_trace {raw : List (Fin 2)} {stOf : ℕ → State GalilVM}
    (h : ∀ k, NoReplay (stOf k)) {m : Mirrored1 P} (hinv : InvC Good raw stOf m)
    (hmd : PhaseMode m.vm.ctl.mode) : m.vm.ctl.replaying = false := by
  obtain ⟨k, j, hn⟩ := hinv.track
  have hc : m.vm.ctl = (stOf k).ctl := ctl_of_needy hn
  rw [hc]
  exact h k (by rw [← hc]; exact hmd)

/-- **On a tracked `copy` state the guard `remainingPos` is the copy reading.**  The shift
counter of the trace is spent outside `shift`, and truncation does not touch counters. -/
theorem copyRemaining_of_trace {raw : List (Fin 2)} {stOf : ℕ → State GalilVM}
    (hshiftIdleInCopy : ∀ k, (stOf k).ctl.mode = .copy →
      ¬ PalPeg.GalilTickFun3.ShiftRemaining (stOf k).vm)
    {m : Mirrored1 P} (hinv : InvC Good raw stOf m) (hmode : m.vm.ctl.mode = .copy)
    (hremaining : PalPeg.LocalRealizesPhase.RemPosL m.vm) :
    PalPeg.GalilTickFun3.CopyRemaining (abs' m.vm) := by
  obtain ⟨k, j, hneedy⟩ := hinv.track
  have hctl : m.vm.ctl = (stOf k).ctl := ctl_of_needy hneedy
  have hvm : abs'' m.vm = PalPeg.GalilThrottledRun.truncVM (raw.length - j) (stOf k).vm :=
    congrArg State.vm hneedy.2
  have hremainingEq : (abs' m.vm).remaining = (stOf k).vm.remaining :=
    (show (abs' m.vm).remaining = (abs'' m.vm).remaining from rfl).trans
      ((congrArg GalilVM.remaining hvm).trans rfl)
  rcases hremaining with hshift | hcopy
  · exact absurd (show PalPeg.GalilTickFun3.ShiftRemaining (stOf k).vm by
      unfold PalPeg.GalilTickFun3.ShiftRemaining at hshift ⊢
      rw [← hremainingEq]; exact hshift) (hshiftIdleInCopy k (by rw [← hctl]; exact hmode))
  · exact hcopy

/-! ## 2. The `fpp` quantum: `ffpp`, `H_fpp` and `H_fpp_mir` -/

section Fpp

open PalPeg.LocalTick3 (TickL3 fppRunBuf sliceVm doneVm absState''_eq)
open PalPeg.LocalBuffers (Buffered)

/-- With a *constant* pointwise family the fpp double buffer ends on the
prescribed tapes: `LocalBuffers.abs (stepL f b) = f (abs b)`. -/
theorem abs_fppRun_of_abs (T : Fin 9 → GalilScaffoldTape.Tape) :
    ∀ (n : ℕ) (b : Buffered 9), PalPeg.LocalBuffers.abs b = T →
      PalPeg.LocalBuffers.abs (fppRunBuf (fun _ i _ => T i) n b) = T
  | 0, b, h => h
  | n + 1, b, h => abs_fppRun_of_abs T n _ (by rw [PalPeg.LocalBuffers.abs_stepL])

/-- **The pointwise family of a quantum exists.**  For `q = 0` the quantum is
empty, so the target tapes have to be the current ones. -/
theorem exists_fppRun (T : Fin 9 → GalilScaffoldTape.Tape) (q : ℕ) (b : Buffered 9)
    (h0 : q = 0 → PalPeg.LocalBuffers.abs b = T) :
    ∃ g, PalPeg.LocalBuffers.abs (fppRunBuf g q b) = T := by
  cases q with
  | zero => exact ⟨fun _ _ t => t, h0 rfl⟩
  | succ n => exact ⟨fun _ i _ => T i,
      abs_fppRun_of_abs T n _ (by rw [PalPeg.LocalBuffers.abs_stepL])⟩

theorem run_nil {n : ℕ} {code : List (GalilFppWide.Instruction n)}
    {p p' : GalilScaffoldControl.Machine n}
    (h : GalilScaffoldControl.Run code p (List.replicate 0 true) p') : p' = p := by
  cases h with
  | nil => rfl

variable {Pw : Shared} {qq : ℕ} {first : Fin 9} {delay : ℕ}

/-- **The local `fpp` quantum exists.**  Read the abstract `fppSlice`/`fppDone`
block off the trace tick and mirror it on the double buffer. -/
theorem exists_fppTick {x : GalilVML P} {t : State GalilVM}
    (hq : qq ≤ 64) (hmd : x.ctl.mode = .fpp) (hnr : x.ctl.replaying = false)
    (ht : Tick (galilFrameS Pw qq first) delay (absState'' x) t) :
    ∃ y : GalilVML P, TickL3 Pw qq first x y ∧ y.center = x.center := by
  have habs : absState'' x = ⟨x.ctl, abs' x⟩ := absState''_eq hnr
  rw [habs] at ht
  rcases PalPeg.LocalRealizesPhase.tick_fpp_cases hmd ht with ⟨s', hsl, -⟩ | ⟨s', hdn, -⟩
  · obtain ⟨hrun0, hR0, hd0, -⟩ := hsl.1
    have hrun : x.fppMode = .run := hrun0
    have hR : GalilScaffoldControl.Run GalilFppMarkedCode.code (abs' x).fpp.program
        (List.replicate qq true) s'.fpp.program := hR0
    have hd : s'.fpp.program.done = false := hd0
    obtain ⟨g, hg⟩ := exists_fppRun s'.fpp.program.config.tapes qq x.fppBuf (by
      intro hq0
      rw [hq0] at hR
      rw [run_nil hR]
      rfl)
    have hprog0 : s'.fpp.program
        = ⟨⟨s'.fpp.program.config.pc, s'.fpp.program.config.tapes⟩, false⟩ := by
      rw [← hd]
    refine ⟨sliceVm g qq s'.fpp.program.config.pc x,
      TickL3.fpp_slice x g s'.fpp.program.config.pc hmd hnr hq hrun ?_, rfl⟩
    rw [hg, ← hprog0]
    exact hR
  · obtain ⟨hrun0, p, hR0, hd, -⟩ := hdn.1
    have hrun : x.fppMode = .run := hrun0
    have hR : GalilScaffoldControl.Run GalilFppMarkedCode.code (abs' x).fpp.program
        (List.replicate qq true) p := hR0
    obtain ⟨g, hg⟩ := exists_fppRun p.config.tapes qq x.fppBuf (by
      intro hq0
      rw [hq0] at hR
      rw [run_nil hR]
      rfl)
    have hprog0 : p = ⟨⟨p.config.pc, p.config.tapes⟩, true⟩ := by
      rw [← hd]
    refine ⟨doneVm first g qq p.config.pc { x.ctl with mode := .markEnd } x,
      TickL3.fpp_done x g p.config.pc hmd hnr hq hrun ?_, rfl⟩
    rw [hg, ← hprog0]
    exact hR

open Classical in
/-- **The local `fpp` step.**  Any scaffold tick out of `x` that leaves the
centre alone; `exists_fppTick` shows there is one whenever the trace has one. -/
noncomputable def ffpp (Pw : Shared) (qq : ℕ) (first : Fin 9) (m : Mirrored1 P) : Mirrored1 P :=
  if h : ∃ y : GalilVML P, TickL3 Pw qq first m.vm y ∧ y.center = m.vm.center then
    ⟨h.choose, m.mirL⟩
  else m

theorem ffpp_spec {m : Mirrored1 P}
    (h : ∃ y : GalilVML P, TickL3 Pw qq first m.vm y ∧ y.center = m.vm.center) :
    TickL3 Pw qq first m.vm (ffpp Pw qq first m).vm := by
  unfold ffpp
  rw [dif_pos h]
  exact h.choose_spec.1

/-- **`H_fpp_mir` is closed**, unconditionally: the chosen successor never moves
the centre, and off the chosen branch the step is the identity. -/
theorem mirInv1_ffpp {m : Mirrored1 P} (hm : MirInv1 m) : MirInv1 (ffpp Pw qq first m) := by
  unfold ffpp
  by_cases h : ∃ y : GalilVML P, TickL3 Pw qq first m.vm y ∧ y.center = m.vm.center
  · rw [dif_pos h]
    exact PalPeg.LocalRealizesPhase.mirInv1_keep hm h.choose_spec.2
  · rw [dif_neg h]; exact hm

/-- **`H_fpp` is closed**, modulo the quantum budget `qq ≤ 64` and the
control-flow fact that an `fpp` state is not replaying. -/
theorem H_fpp_of_wf {raw : List (Fin 2)} {stOf : ℕ → State GalilVM} (hq : qq ≤ 64)
    (hnr : ∀ m : Mirrored1 P, InvC Good raw stOf m → m.vm.ctl.mode = .fpp →
      m.vm.ctl.replaying = false) :
    ∀ (m : Mirrored1 P) (k j : ℕ), InvC Good raw stOf m → m.vm.ctl.mode = .fpp →
      ¬ Starved m.vm → Needy raw stOf k j m.vm →
      Tick (galilFrameS Pw qq first) delay (absState'' m.vm)
        (truncS (raw.length - j) (stOf (k+1))) →
      TickL3 Pw qq first m.vm (ffpp Pw qq first m).vm := by
  intro m k j hinv hmd hns hn ht
  exact ffpp_spec (exists_fppTick hq hmd (hnr m hinv hmd) ht)

end Fpp

/-! ## 3. Counter facts the abstract guards already contain -/

section Counters

open PalPeg.LocalCounter (val absCtr)
open PalPeg.GalilScaffoldCounter (positive zero)

/-- A positive abstract counter pins **both** the polarity bit and the tape
value: `absCtr t false` is `-val t ≤ 0`. -/
theorem pol_pos_of_positive {t : PalPeg.Program.STape PalPeg.LocalCounter.Seg} {b : Bool}
    (h : positive (absCtr t b) = true) : b = true ∧ 0 < val t := by
  cases b <;> cases hv : val t <;>
    simp_all [absCtr, PalPeg.GalilScaffoldCounter.ofNat, PalPeg.LocalCounter.negOfNat, positive]

/-- **`ShiftCounters.remPol` and `.remPos` are free**: the shift reading of
`remainingPos` already says `remaining` is a positive counter. -/
theorem remaining_of_shiftRemaining {x : GalilVML P}
    (h : PalPeg.GalilTickFun3.ShiftRemaining (abs' x)) :
    x.pol .remaining = true ∧ 0 < val (x.phys (x.roles .remaining)) :=
  pol_pos_of_positive h

/-- **`CopySide.pos` is free** when the guard is the copy one: `copyRemaining`
already says the fpp work counter is not zero. -/
theorem work_of_copyRemaining {x : GalilVML P}
    (h : PalPeg.GalilTickFun3.CopyRemaining (abs' x)) :
    0 < val (x.phys (x.roles .fppWork)) := by
  have h' : zero (absCtr (x.phys (x.roles .fppWork)) (x.pol .fppWork)) ≠ true :=
    fun hz => h (Or.inr hz)
  rw [PalPeg.LocalCounter.zero_iff] at h'
  simp at h'
  omega

end Counters

/-! ## 4. The polarity bundle is a genuine local invariant -/

section Pol

open PalPeg.LocalTick3 (TickL3)
open PalPeg.LocalRealizesPhase (shiftStepL shiftPick copyStepL copyPick homeStepL markEndStepL)
open PalPeg.LocalRealizesScan (chooseStepC rewindStepC)
open PalPeg.LocalSysConcrete (feedC)

/-- The five counters whose sign bit the phase steps rely on. -/
def PolWF (x : GalilVML P) : Prop :=
  x.pol .remaining = true ∧ x.pol .radius = true ∧ x.pol .length = true ∧
    x.pol .cycle = true ∧ x.pol .fppWork = true

/-- **No phase tick touches the polarity bundle.** -/
theorem pol_tickL3 {S : Shared} {q : ℕ} {firstT : Fin 9} {x y : GalilVML P}
    (h : TickL3 S q firstT x y) : y.pol = x.pol := by
  cases h <;> rfl

theorem polWF_of_tickL3 {S : Shared} {q : ℕ} {firstT : Fin 9} {x y : GalilVML P}
    (h : PolWF x) (ht : TickL3 S q firstT x y) : PolWF y := by
  unfold PolWF at h ⊢; rw [pol_tickL3 ht]; exact h

theorem pol_shiftStepL (Pw : Shared) (m : Mirrored1 P) :
    (shiftStepL Pw m).vm.pol = m.vm.pol := by
  classical
  unfold shiftStepL
  split
  · unfold shiftPick; split <;> rfl
  · rfl

theorem pol_copyStepL (m : Mirrored1 P) : (copyStepL m).vm.pol = m.vm.pol := by
  classical
  unfold copyStepL
  split
  · unfold copyPick; split <;> rfl
  · rfl

theorem pol_homeStepL (m : Mirrored1 P) : (homeStepL m).vm.pol = m.vm.pol := by
  classical
  unfold homeStepL; split <;> rfl

theorem pol_markEndStepL (m : Mirrored1 P) : (markEndStepL m).vm.pol = m.vm.pol := by
  classical
  unfold markEndStepL; split <;> rfl

theorem pol_chooseStepC (Pw : Shared) (qq : ℕ) (firstT : Fin 9) (m : Mirrored1 P) :
    (chooseStepC Pw qq firstT m).vm.pol = m.vm.pol := by
  classical
  unfold chooseStepC; split <;> rfl

theorem pol_rewindStepC (Pw : Shared) (qq : ℕ) (firstT : Fin 9) (m : Mirrored1 P) :
    (rewindStepC Pw qq firstT m).vm.pol = m.vm.pol := by
  classical
  unfold rewindStepC
  split
  · rfl
  · split <;> rfl

theorem pol_ffpp (Pw : Shared) (qq : ℕ) (firstT : Fin 9) (m : Mirrored1 P) :
    (ffpp Pw qq firstT m).vm.pol = m.vm.pol := by
  classical
  unfold ffpp
  by_cases h : ∃ y : GalilVML P, TickL3 Pw qq firstT m.vm y ∧ y.center = m.vm.center
  · rw [dif_pos h]; exact pol_tickL3 h.choose_spec.1
  · rw [dif_neg h]

/-- **Arrival does not touch the polarity bundle either.** -/
theorem pol_feedC {m : Mirrored1 P} (hp : m.vm.pending = []) (a : Fin 2) :
    (feedC a m).vm.pol = m.vm.pol := by
  have h1 : (feedC a m).vm
      = PalPeg.LocalArrival.feedL' a [] (PalPeg.LocalSysConcrete.feedV a m.vm) :=
    PalPeg.LocalArrival.feed'_cons (PalPeg.LocalSysConcrete.pending_feedV hp a)
  rw [h1]
  rfl

/-- **`PolWF` holds at the initial latched state** as soon as the blank core has
its counters on the positive side. -/
theorem polWF_x0C {blank : GalilVML P} (h : PolWF blank) (delay : ℕ) :
    PolWF (PalPeg.LocalSysConcrete.x0C blank delay).core.vm := h

end Pol

/-! ## 5. The pack, and the five mode obligations it discharges -/

section Pack

open PalPeg.LocalCounter (val)
open PalPeg.LocalTick3 (ShiftCounters)
open PalPeg.LocalRealizesPhase (RemPosL CopySide)
open PalPeg.LocalRealizesScan (RewindWF ChooseWF)

/-- **The local well-formedness pack**: the polarity bundle (§4, invariant).  The counter
magnitudes a shift or copy unit needs are not part of it: they are read off the trace
(`shiftMagnitudes_of_trace`, `copyRemaining_of_trace`). -/
structure LocalWF (x : GalilVML P) : Prop where
  pol : PolWF x

/-- A tape of positive polarity abstracts to its value. -/
theorem value_absCtr_of_positivePolarity (t : PalPeg.Program.STape PalPeg.LocalCounter.Seg) :
    GalilScaffoldCounter.value (PalPeg.LocalCounter.absCtr t true) = (val t : ℤ) := by
  unfold PalPeg.LocalCounter.absCtr
  rw [if_pos rfl]
  simp [GalilScaffoldCounter.value, GalilScaffoldCounter.ofNat]

open PalPeg.GalilScaffoldCounter (value positive) in
/-- **The counter magnitudes of a shift unit, on a tracked state.**  On the trace the copy side is
idle in `shift`, the shift counter is at most the radius, and the span is `2 · radius + 1`;
truncation does not touch counters, and the three tapes have positive polarity. -/
theorem shiftMagnitudes_of_trace {raw : List (Fin 2)} {stOf : ℕ → State GalilVM}
    (hshiftLedgerOnTrace : ∀ k, (stOf k).ctl.mode = .shift →
      CopyIdle (stOf k).vm ∧ value (stOf k).vm.remaining ≤ value (stOf k).vm.radius ∧
        SpanRep (stOf k).vm)
    {m : Mirrored1 P} (hinv : InvC Good raw stOf m) (hmode : m.vm.ctl.mode = .shift)
    (hremaining : RemPosL m.vm) (hpol : PolWF m.vm) :
    0 < val (m.vm.phys (m.vm.roles .remaining)) ∧ 0 < val (m.vm.phys (m.vm.roles .radius)) ∧
      2 ≤ val (m.vm.phys (m.vm.roles .length)) := by
  obtain ⟨k, j, hneedy⟩ := hinv.track
  have hctl : m.vm.ctl = (stOf k).ctl := ctl_of_needy hneedy
  have hvm : abs'' m.vm = PalPeg.GalilThrottledRun.truncVM (raw.length - j) (stOf k).vm :=
    congrArg State.vm hneedy.2
  obtain ⟨hcopyIdle, hbudget, hspan⟩ := hshiftLedgerOnTrace k (by rw [← hctl]; exact hmode)
  have hfppEq : (abs' m.vm).fpp = (stOf k).vm.fpp :=
    (show (abs' m.vm).fpp = (abs'' m.vm).fpp from rfl).trans ((congrArg GalilVM.fpp hvm).trans rfl)
  have hremainingEq : (abs' m.vm).remaining = (stOf k).vm.remaining :=
    (show (abs' m.vm).remaining = (abs'' m.vm).remaining from rfl).trans
      ((congrArg GalilVM.remaining hvm).trans rfl)
  have hradiusEq : (abs' m.vm).radius = (stOf k).vm.radius :=
    (show (abs' m.vm).radius = (abs'' m.vm).radius from rfl).trans
      ((congrArg GalilVM.radius hvm).trans rfl)
  have hlengthEq : (abs' m.vm).length = (stOf k).vm.length :=
    (show (abs' m.vm).length = (abs'' m.vm).length from rfl).trans
      ((congrArg GalilVM.length hvm).trans rfl)
  have hshiftRemaining : positive (abs' m.vm).remaining = true := by
    rcases hremaining with hshift | hcopy
    · exact hshift
    · exfalso
      rw [copyIdle_iff] at hcopyIdle
      unfold PalPeg.GalilTickFun3.CopyRemaining at hcopy
      rw [hfppEq] at hcopy
      exact hcopy hcopyIdle
  have hremainingVal : (abs' m.vm).remaining
      = PalPeg.LocalCounter.absCtr (m.vm.phys (m.vm.roles .remaining)) true := by
    rw [← hpol.1]; rfl
  have hradiusVal : (abs' m.vm).radius
      = PalPeg.LocalCounter.absCtr (m.vm.phys (m.vm.roles .radius)) true := by
    rw [← hpol.2.1]; rfl
  have hlengthVal : (abs' m.vm).length
      = PalPeg.LocalCounter.absCtr (m.vm.phys (m.vm.roles .length)) true := by
    rw [← hpol.2.2.1]; rfl
  have hremainingValue := value_absCtr_of_positivePolarity (m.vm.phys (m.vm.roles .remaining))
  have hradiusValue := value_absCtr_of_positivePolarity (m.vm.phys (m.vm.roles .radius))
  have hlengthValue := value_absCtr_of_positivePolarity (m.vm.phys (m.vm.roles .length))
  rw [← hremainingVal, hremainingEq] at hremainingValue
  rw [← hradiusVal, hradiusEq] at hradiusValue
  rw [← hlengthVal, hlengthEq] at hlengthValue
  have hremainingPos : 0 < val (m.vm.phys (m.vm.roles .remaining)) := by
    rcases Nat.eq_zero_or_pos (val (m.vm.phys (m.vm.roles .remaining))) with hzero | hpos
    · exfalso
      rw [hremainingVal] at hshiftRemaining
      unfold PalPeg.LocalCounter.absCtr at hshiftRemaining
      rw [if_pos rfl, hzero] at hshiftRemaining
      exact absurd hshiftRemaining (by decide)
    · exact hpos
  unfold SpanRep at hspan
  refine ⟨hremainingPos, ?_, ?_⟩ <;> omega

theorem shiftCounters_of {x : GalilVML P} (h : LocalWF x)
    (hmagnitudes : 0 < val (x.phys (x.roles .remaining)) ∧ 0 < val (x.phys (x.roles .radius)) ∧
      2 ≤ val (x.phys (x.roles .length))) : ShiftCounters x :=
  ⟨h.pol.1, h.pol.2.1, h.pol.2.2.1, h.pol.2.2.2.1, hmagnitudes.1, hmagnitudes.2.1,
    hmagnitudes.2.2⟩

/-- The abstract work counter of the copy reads the local tape: if it is not zero, the tape
holds a positive value, whatever its polarity. -/
theorem val_fppWork_pos_of_copyRemaining {x : GalilVML P}
    (hcopyRemaining : PalPeg.GalilTickFun3.CopyRemaining (abs' x)) :
    0 < val (x.phys (x.roles .fppWork)) := by
  have hworkNotZero : ¬ GalilScaffoldCounter.zero (abs' x).fpp.work = true :=
    fun hzero => hcopyRemaining (Or.inr hzero)
  have hwork : (abs' x).fpp.work
      = PalPeg.LocalCounter.absCtr (x.phys (x.roles .fppWork)) (x.pol .fppWork) := rfl
  rw [hwork] at hworkNotZero
  rcases Nat.eq_zero_or_pos (val (x.phys (x.roles .fppWork))) with hzero | hpos
  · exfalso
    apply hworkNotZero
    unfold PalPeg.LocalCounter.absCtr
    rw [hzero]
    cases x.pol .fppWork <;> rfl
  · exact hpos

theorem copySide_of {x : GalilVML P} (h : LocalWF x)
    (hwalkerProper : PalPeg.LocalChain.ProperView x.fppWalker)
    (hcopyRemaining : PalPeg.GalilTickFun3.CopyRemaining (abs' x)) : CopySide x :=
  ⟨h.pol.2.2.2.2, val_fppWork_pos_of_copyRemaining hcopyRemaining, hwalkerProper⟩

theorem rewindWF_of {x : GalilVML P} (h : LocalWF x) (hnr : x.ctl.replaying = false) :
    RewindWF x :=
  ⟨hnr, h.pol.2.2.1, h.pol.2.1⟩

theorem chooseWF_of {x : GalilVML P} (h : LocalWF x) (hnr : x.ctl.replaying = false) :
    ChooseWF x :=
  ⟨hnr, h.pol.2.2.1⟩

end Pack

/-! ## 6. The capstone: seven of the ten mode obligations -/

section Assembly

open PalPeg.LocalRealizesPhase (shiftStepL copyStepL homeStepL markEndStepL)
open PalPeg.LocalRealizesScan (chooseStepC rewindStepC)

/-- **Seven of the ten `Realizes` obligations of `LocalSysConcrete`**, from the
trace hypotheses, the quantum budget, the trace's own control-flow invariant at
time `0`, and the local pack `LocalWF`.  `init`, `scan` and `replayStart` are
untouched (they are open in `LocalRealizesScan` too). -/
theorem realizes_seven {raw : List (Fin 2)} {stOf : ℕ → State GalilVM}
    {Pw : Shared} {qq : ℕ} {first : Fin 9} {delay : ℕ}
    (H_shared : ∀ j, PalPeg.GalilTruncTick.SharedTrunc raw j Pw)
    (H_trace : ∀ k, k < lastTick → Tick (galilFrameS Pw qq first) delay (stOf k) (stOf (k+1)))
    (H_afterLast : ∀ k, lastTick ≤ k → stOf k = stOf lastTick)
    (H_start : NoReplay (stOf 0)) (hq : qq ≤ 64)
    (H_wf : ∀ m : Mirrored1 P, InvC Good raw stOf m → LocalWF m.vm)
    (H_shiftIdleInCopy : ∀ k, (stOf k).ctl.mode = .copy →
      ¬ PalPeg.GalilTickFun3.ShiftRemaining (stOf k).vm)
    (H_shiftLedgerOnTrace : ∀ k, (stOf k).ctl.mode = .shift →
      CopyIdle (stOf k).vm ∧
        GalilScaffoldCounter.value (stOf k).vm.remaining
          ≤ GalilScaffoldCounter.value (stOf k).vm.radius ∧ SpanRep (stOf k).vm) :
    Realizes Good raw stOf lastTick (shiftStepL (P := P) Pw) .shift ∧
    Realizes Good raw stOf lastTick (copyStepL (P := P)) .copy ∧
    Realizes Good raw stOf lastTick (homeStepL (P := P)) .home ∧
    Realizes Good raw stOf lastTick (ffpp (P := P) Pw qq first) .fpp ∧
    Realizes Good raw stOf lastTick (markEndStepL (P := P)) .markEnd ∧
    Realizes Good raw stOf lastTick (chooseStepC (P := P) Pw qq first) .choose ∧
    Realizes Good raw stOf lastTick (rewindStepC (P := P) Pw qq first) .rewind := by
  have hNR : ∀ k, NoReplay (stOf k) := noReplay_run H_trace H_afterLast H_start
  have hnr : PalPeg.LocalRealizesPhase.PhaseNoReplay (P := P) Good raw stOf :=
    phaseNoReplay_of_trace hNR
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    PalPeg.LocalRealizesPhase.realizes_phases (P := P) (delay := delay)
      (ffpp Pw qq first) H_shared H_trace hnr
      (fun m hinv hmd hns hr => copySide_of (H_wf m hinv) hinv.phys.walkerProper
        (copyRemaining_of_trace H_shiftIdleInCopy hinv hmd hr))
      (fun m hinv hmd hns hr => shiftCounters_of (H_wf m hinv)
        (shiftMagnitudes_of_trace H_shiftLedgerOnTrace hinv hmd hr (H_wf m hinv).pol))
      (H_fpp_of_wf (Pw := Pw) (qq := qq) (first := first) (delay := delay) hq
        (fun m hinv hmd => hnr m hinv (Or.inr (Or.inr (Or.inr (Or.inl hmd))))))
      (fun m hinv hmd hns => mirInv1_ffpp hinv.mir)
  exact ⟨h1, h2, h3, h4, h5,
    PalPeg.LocalRealizesScan.realizes_choose (P := P) (delay := delay) H_shared H_trace
      (fun m hinv hmd => chooseWF_of (H_wf m hinv)
        (notReplaying_of_trace hNR hinv (by unfold PhaseMode; simp [hmd]))),
    PalPeg.LocalRealizesScan.realizes_rewind (P := P) (delay := delay) H_shared H_trace
      (fun m hinv hmd => rewindWF_of (H_wf m hinv)
        (notReplaying_of_trace hNR hinv (by unfold PhaseMode; simp [hmd])))⟩

end Assembly

/-! ## 7. `PolWF` is preserved by a whole local tick -/

section Preservation

open PalPeg.LocalSysConcrete (Steps stepOf tickC tickC_step tickC_starved x0C)
open PalPeg.LocalRealizesPhase (shiftStepL copyStepL homeStepL markEndStepL)
open PalPeg.LocalRealizesScan (chooseStepC rewindStepC)

theorem polWF_congr {x y : GalilVML P} (h : PolWF x) (hp : y.pol = x.pol) : PolWF y := by
  unfold PolWF at h ⊢; rw [hp]; exact h

/-- The `Steps` record of this file: the seven closed modes, with `init`,
`scan` and `replayStart` left as parameters. -/
noncomputable def stepsWF (Pw : Shared) (qq : ℕ) (first : Fin 9)
    (init scan replayStart : Mirrored1 P → Mirrored1 P) : Steps P where
  init := init
  scan := scan
  shift := shiftStepL Pw
  copy := copyStepL
  home := homeStepL
  fpp := ffpp Pw qq first
  markEnd := markEndStepL
  choose := chooseStepC Pw qq first
  rewind := rewindStepC Pw qq first
  replayStart := replayStart

theorem pol_stepOf (Pw : Shared) (qq : ℕ) (first : Fin 9)
    {init scan replayStart : Mirrored1 P → Mirrored1 P}
    (h0 : ∀ m : Mirrored1 P, (init m).vm.pol = m.vm.pol)
    (h1 : ∀ m : Mirrored1 P, (scan m).vm.pol = m.vm.pol)
    (h2 : ∀ m : Mirrored1 P, (replayStart m).vm.pol = m.vm.pol)
    (md : Mode) (m : Mirrored1 P) :
    (stepOf (stepsWF Pw qq first init scan replayStart) md m).vm.pol = m.vm.pol := by
  cases md
  · exact h0 m
  · exact h1 m
  · exact pol_shiftStepL Pw m
  · exact pol_copyStepL m
  · exact pol_homeStepL m
  · exact pol_ffpp Pw qq first m
  · exact pol_markEndStepL m
  · exact pol_chooseStepC Pw qq first m
  · exact pol_rewindStepC Pw qq first m
  · exact h2 m

/-- **`PolWF` is preserved by one local tick**, once the three open steps keep
the polarity bundle (they do: no scan/init/replay action negates a counter of
`PolWF`, but their local realizations are not constructed yet). -/
theorem polWF_tickC (Pw : Shared) (qq : ℕ) (first : Fin 9)
    {init scan replayStart : Mirrored1 P → Mirrored1 P}
    (h0 : ∀ m : Mirrored1 P, (init m).vm.pol = m.vm.pol)
    (h1 : ∀ m : Mirrored1 P, (scan m).vm.pol = m.vm.pol)
    (h2 : ∀ m : Mirrored1 P, (replayStart m).vm.pol = m.vm.pol)
    {m : Mirrored1 P} (h : PolWF m.vm) :
    PolWF (tickC (stepsWF Pw qq first init scan replayStart) m).vm := by
  classical
  by_cases hs : Starved m.vm
  · rw [tickC_starved _ hs]; exact h
  · rw [tickC_step _ hs]
    exact polWF_congr h (pol_stepOf Pw qq first h0 h1 h2 _ m)

/-- **`PolWF` is preserved by an arrival.** -/
theorem polWF_feedC {m : Mirrored1 P} (hp : m.vm.pending = []) (a : Fin 2) (h : PolWF m.vm) :
    PolWF (PalPeg.LocalSysConcrete.feedC a m).vm :=
  polWF_congr h (pol_feedC hp a)

end Preservation

/-! ## 8. The residuals this file does **not** close

* the polarity half for the three modes whose local step is still open
  (`h0`/`h1`/`h2` of `polWF_tickC`).
* `LocalWF` at `x0C` reduces to `PolWF blank` (`polWF_x0C`).

**無条件 PAL ∈ PEG は未完.**
-/

theorem localWF_x0C {blank : GalilVML P} (h : PolWF blank) (delay : ℕ) :
    LocalWF (PalPeg.LocalSysConcrete.x0C blank delay).core.vm :=
  ⟨h⟩

#print axioms noReplay_tick
#print axioms noReplay_run
#print axioms phaseNoReplay_of_trace
#print axioms notReplaying_of_trace
#print axioms exists_fppRun
#print axioms exists_fppTick
#print axioms ffpp_spec
#print axioms mirInv1_ffpp
#print axioms H_fpp_of_wf
#print axioms pol_pos_of_positive
#print axioms remaining_of_shiftRemaining
#print axioms work_of_copyRemaining
#print axioms pol_tickL3
#print axioms pol_feedC
#print axioms shiftCounters_of
#print axioms copySide_of
#print axioms rewindWF_of
#print axioms chooseWF_of
#print axioms realizes_seven
#print axioms pol_stepOf
#print axioms polWF_tickC
#print axioms polWF_feedC
#print axioms localWF_x0C

end PalPeg.LocalWF
