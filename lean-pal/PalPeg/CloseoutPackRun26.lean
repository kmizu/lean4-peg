import PalPeg.CloseoutPackRun24
import PalPeg.CloseoutPackRun18

/-!
# `CloseoutPackRun26`: the shift-mode caveat of `CloseoutPackRun24`, decided

`CloseoutPackRun24` closed `BigResid6.rShiftNext` modulo `WatchShift`, and
recorded a caveat: `compareFound` carries no mode guard and `beginShiftVM'` only
needs `s''.chain = .watch _`, so at a `shift`-mode state — whose chain *is* a
watch, set by `beginShiftVM` — the field `ShiftLocal.mode` (which demands
`x.ctl.mode = Mode.scan`) is false as soon as a chain-internal step is enabled.

**Verdict: refuted.**  §1 shows

* every `scan → shift` tick lands with `t.chain = .watch (immediate w)` and
  `zero w.lag = true` (`shift_landing`), so `GalilScaffoldChainWatch.Internal.idle`
  *is* enabled there (`internal_enabled_at_landing`);
* hence, whenever the two heads read differently at the landing, the mismatch
  comparison `afterMismatch` is a `compareFound` target whose chain is still that
  watch (`compare_watch_target`), and `ShiftLocal.mode` at the landing is false
  (`shiftLocal_false_at_landing`).

So `BigResid6.rShiftNext` (and `rShiftNext_of_pack`'s `WatchShift` premise,
whose first conjunct is the mode) cannot hold at a shift landing with mismatching
heads: the contract must be *guarded* by the controller mode.

§2 re-cuts `ShiftLocal` as `ShiftLocalG` — every field under
`x.ctl.mode = Mode.scan ∧ x.ctl.replaying = false` (the `mode` field becomes the
guard itself and is dropped) — and `WatchShift` as `WatchShiftG`, and proves
`rShiftNextG_of_pack`.  §3 shows the consumers only need the guarded form:
`H_shiftLocalC` is read at `InvLPC` states only, which are scan/non-replaying
(`h_shiftLocalC_of_G`), and the two tick-level consumers of the shift-entry
payload, `CloseoutRadPack2.shiftOrd_tick` and `CloseoutRadPack4.saneTick`, use it
only in their `scan_shift` branch (`shiftOrd_tickG`, `saneTickG`, same proofs
with the guard discharged by the branch's own `hm`/`hr`).

§4 states `pal_in_peg_final16`: `pal_in_peg_final15` with `H_shiftLocalC`
replaced by `H_shiftLocalG`.  **What is not done here:** `BigResid6.rShiftNext`
is still the unguarded contract in `final16`, because `IPackM.shift : ShiftLocal`
is hard-wired into `StepsIM` / `ReachAtIM` / `CycleOracleIM` / `PreTraceIM` /
`pal_in_peg_final5M` (`CloseoutPackRun10`/`12`/`14`/`18`), and re-cutting it to
`ShiftLocalG` is a re-thread of that chain, not a one-file change.  The
pointwise readers `CloseoutPackRun12.shiftEntry_ptM` / `shiftVerSane_ptM` (and
`halfBound_of_ipackM`, which reads `.shift.mode` to feed `scanGeom`) are the
branch that reads the fields at *every* trace state; their guarded counterparts
would go through `shiftOrd_tickG` / `saneTickG`.
-/

set_option autoImplicit false

namespace PalPeg.CloseoutPackRun26

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilFrontMono PalPeg.GalilChainCoupling
open PalPeg.CloseoutLPack PalPeg.CloseoutLPack3 PalPeg.CloseoutLPack4
open PalPeg.CloseoutLPack5 PalPeg.CloseoutPackRun6
open PalPeg.CloseoutPackRun10 PalPeg.CloseoutPackRun11 PalPeg.CloseoutPackRun12
open PalPeg.CloseoutPackRun16 PalPeg.CloseoutPackRun18 PalPeg.CloseoutPackRun24
open PalPeg.CloseoutOracleI PalPeg.CloseoutOracleI2 PalPeg.GalilInvPlus2
open PalPeg.GalilOracleLocal PalPeg.GalilInvPlus3
open PalPeg.CloseoutRadPack PalPeg.CloseoutRadPack2 PalPeg.CloseoutRadPack3
open PalPeg.CloseoutRadPack4 PalPeg.GalilTrailRad PalPeg.GalilTrailChain PalPeg.GalilFinalAssembly2

/-! ## 1. The refutation -/

section Refute
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **The shape of every `scan → shift` landing.**  The only tick from `scan`
into `shift` is `scan_shift`; its `shiftGuard` is `shiftGuardVM` (a watching
chain with `zero lag`) and its `beginShift` is `beginShiftVM'`, which keeps the
same watch (up to `immediate`, which does not touch the lag). -/
theorem shift_landing {w : List (Fin 2)} {c c' : Control} {s t : GalilVM}
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 ⟨c, s⟩ ⟨c', t⟩)
    (hm : c.mode = Mode.scan) (hm' : c'.mode = Mode.shift) :
    ∃ wch : GalilScaffoldChainWatch.State,
      t.chain = .watch (GalilScaffoldChainWatch.immediate wch) ∧ zero wch.lag = true := by
  cases h
  case scan_shift =>
    rename_i s' hmt hg hm0 hc hr hcmp hav hb
    obtain ⟨wg, hwg, hz, -, -, -, -⟩ : shiftGuardVM s' := hg
    obtain ⟨wb, hwb, ht⟩ : beginShiftVM' s' t := hb
    have hww : wg = wb := by
      have := hwg.symm.trans hwb
      exact ChainVM.watch.inj this
    subst hww
    refine ⟨wg, ?_, hz⟩
    rw [ht]
  all_goals exact absurd hm' (by simp_all)

/-- **`Internal` is enabled at every shift landing**: the lag is zero, so the
`idle` internal step applies. -/
theorem internal_enabled_at_landing {w : List (Fin 2)} {c c' : Control} {s t : GalilVM}
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 ⟨c, s⟩ ⟨c', t⟩)
    (hm : c.mode = Mode.scan) (hm' : c'.mode = Mode.shift) :
    ∃ wch : GalilScaffoldChainWatch.State, t.chain = .watch wch ∧
      GalilScaffoldChainWatch.Internal wch wch := by
  obtain ⟨wch, ht, hz⟩ := shift_landing centre place entry q first h hm hm'
  refine ⟨GalilScaffoldChainWatch.immediate wch, ht, ?_⟩
  exact GalilScaffoldChainWatch.Internal.idle _ (positive_of_zero hz)

/-- **A `compareFound` target whose chain is the same watch**, at any state
whose chain watches with a non-positive lag and whose two heads read
differently after their steps: the mismatch comparison (`a = false`) with the
`idle` internal step and no search motion (the chain is not idle). -/
theorem compare_watch_target {w : List (Fin 2)} {s : GalilVM}
    {wch : GalilScaffoldChainWatch.State} (hw : s.chain = .watch wch)
    (hz : positive wch.lag = false)
    (hmm : read (left s.left) ≠ read (right s.right)) :
    ∃ s'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare s s'' ∧
        s''.chain = .watch wch := by
  have hne : s.chain ≠ ChainVM.idle := by rw [hw]; intro h; cases h
  refine ⟨afterMismatch s ⟨left s.left, right s.right, .watch wch⟩ (searchLens.get s),
    ⟨⟨left s.left, right s.right, .watch wch⟩, searchLens.get s, false,
      rfl, rfl, ⟨fun h => Bool.noConfusion h, fun h => absurd h hmm⟩,
      Or.inr ⟨hne, rfl⟩, Or.inl ⟨hne, ?_⟩, ?_⟩, rfl⟩
  · refine ⟨.watch wch, ?_, ?_⟩
    · rw [hw]
      exact ChainStep.watchStep _ _ (GalilScaffoldChainWatch.Internal.idle _ hz)
    · simp
  · rw [afterBirth_of_ne_idle hne]
    simp

/-- **`ShiftLocal` is false at any `shift`-mode state that has a `compareFound`
target with a watching chain**: its `mode` field would say `scan`. -/
theorem shiftLocal_false_of_target {w : List (Fin 2)} {y : State GalilVM}
    (hm : y.ctl.mode = Mode.shift)
    (ht : ∃ (s'' : GalilVM) (wch : GalilScaffoldChainWatch.State),
      (galilFrameS (PofC centre place entry w) q first).compare y.vm s'' ∧
        s''.chain = .watch wch) :
    ¬ ShiftLocal centre place entry q first w y := by
  intro hS
  obtain ⟨s'', wch, hcmp, hch⟩ := ht
  obtain ⟨t'', hb⟩ : ∃ t'' : GalilVM, beginShiftVM' s'' t'' := ⟨_, wch, hch, rfl⟩
  have := (hS.mode s'' t'' hcmp hb).1
  rw [hm] at this
  exact Mode.noConfusion this

/-- **(REFUTATION) `ShiftLocal` fails at every `scan → shift` landing whose two
heads read differently.**  No pack hypothesis at the source is needed: the
landing's chain is a zero-lag watch by `shift_landing`, so `compare_watch_target`
applies.  In particular `BigResid6.rShiftNext` (which demands `ShiftLocal` at
*every* tick target out of a `BigPack2M` state) and `H_shiftLocalC`-style
statements at non-scan states are unprovable as stated. -/
theorem shiftLocal_false_at_landing {w : List (Fin 2)} {x y : State GalilVM}
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hm : x.ctl.mode = Mode.scan) (hm' : y.ctl.mode = Mode.shift)
    (hmm : read (left y.vm.left) ≠ read (right y.vm.right)) :
    ¬ ShiftLocal centre place entry q first w y := by
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  obtain ⟨wch, ht, hz⟩ := shift_landing centre place entry q first h hm hm'
  refine shiftLocal_false_of_target centre place entry q first hm' ?_
  obtain ⟨s'', hcmp, hch⟩ := compare_watch_target centre place entry q first (s := t)
    (wch := GalilScaffoldChainWatch.immediate wch) ht (positive_of_zero hz) hmm
  exact ⟨s'', _, hcmp, hch⟩

/-- The same, phrased against `CloseoutPackRun24.WatchShift`: its first conjunct
is the mode, so it is false at the landing too. -/
theorem watchShift_false_at_landing {w : List (Fin 2)} {x y : State GalilVM}
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hm : x.ctl.mode = Mode.scan) (hm' : y.ctl.mode = Mode.shift)
    (hmm : read (left y.vm.left) ≠ read (right y.vm.right)) :
    ¬ WatchShift centre place entry q first w y := by
  intro hws
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  obtain ⟨wch, ht, hz⟩ := shift_landing centre place entry q first h hm hm'
  have hni : t.chain ≠ ChainVM.idle := by rw [ht]; intro h; cases h
  exact shiftLocal_false_at_landing centre place entry q first h hm hm' hmm
    (shiftLocal_of_watchShift centre place entry q first hni hws)

end Refute

#print axioms shift_landing
#print axioms internal_enabled_at_landing
#print axioms compare_watch_target
#print axioms shiftLocal_false_at_landing
#print axioms watchShift_false_at_landing

/-! ## 2. The guarded re-cut -/

section Guarded
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- The guard every consumer of the shift-entry payload lives under: the
`scan_shift` tick's own `hm`/`hr`. -/
def ScanNR (x : State GalilVM) : Prop :=
  x.ctl.mode = Mode.scan ∧ x.ctl.replaying = false

/-- **`ShiftLocal` guarded by `ScanNR`.**  The `mode` field is the guard itself
and is dropped; the other four are stated only under it. -/
structure ShiftLocalG (w : List (Fin 2)) (x : State GalilVM) : Prop where
  move : ScanNR x → ∀ s'' t'' : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).compare x.vm s'' →
    beginShiftVM' s'' t'' → GalilScaffoldChainVerifier.canRight x.vm.right
  guard : ScanNR x → ∀ s'' t'' : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).compare x.vm s'' →
    beginShiftVM' s'' t'' →
    ∀ wch : GalilScaffoldChainWatch.State, s''.chain = .watch wch →
      4 * (periodLength wch : ℤ) ≤ value wch.machine.control.distance
  coupled : ScanNR x → ∀ s'' t'' : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).compare x.vm s'' →
    beginShiftVM' s'' t'' →
    ∀ wch : GalilScaffoldChainWatch.State, s''.chain = .watch wch →
      ∀ rad : ℕ, ScanInvariant w (position x.vm.center) rad x.vm.left x.vm.right →
        value wch.machine.control.distance ≤ 2 * (rad : ℤ)
  ver : ScanNR x → ∀ s'' t'' : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).compare x.vm s'' →
    beginShiftVM' s'' t'' →
    ∀ wch : GalilScaffoldChainWatch.State, s''.chain = .watch wch →
      GalilScaffoldChainVerifier.canRight wch.machine.verifier ∧
        GalilFrontMono.Sane wch.machine.verifier

/-- The guarded form is weaker. -/
theorem shiftLocalG_of_shiftLocal {w : List (Fin 2)} {x : State GalilVM}
    (h : ShiftLocal centre place entry q first w x) : ShiftLocalG centre place entry q first w x :=
  { move := fun _ => h.move, guard := fun _ => h.guard, coupled := fun _ => h.coupled,
    ver := fun _ => h.ver }

/-- **Under the guard the two forms agree.** -/
theorem shiftLocal_of_shiftLocalG {w : List (Fin 2)} {x : State GalilVM} (hs : ScanNR x)
    (h : ShiftLocalG centre place entry q first w x) : ShiftLocal centre place entry q first w x :=
  { mode := fun _ _ _ _ => hs, move := h.move hs, guard := h.guard hs, coupled := h.coupled hs,
    ver := h.ver hs }

/-- `CloseoutPackRun6.shiftLocal_of_chainIdle`, guarded. -/
theorem shiftLocalG_of_chainIdle {w : List (Fin 2)} {x : State GalilVM}
    (hi : x.vm.chain = ChainVM.idle) : ShiftLocalG centre place entry q first w x :=
  shiftLocalG_of_shiftLocal centre place entry q first (shiftLocal_of_chainIdle centre place entry q first hi)

/-- **`CloseoutPackRun24.WatchShift` guarded**: the same payload minus the mode
conjunct, under `ScanNR`. -/
def WatchShiftG (w : List (Fin 2)) (x : State GalilVM) : Prop :=
  ScanNR x → x.vm.chain ≠ ChainVM.idle →
  ∀ s'' : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).compare x.vm s'' →
    ∀ wch : GalilScaffoldChainWatch.State, s''.chain = .watch wch →
      GalilScaffoldChainVerifier.canRight x.vm.right ∧
      4 * (periodLength wch : ℤ) ≤ value wch.machine.control.distance ∧
      (∀ rad : ℕ, ScanInvariant w (position x.vm.center) rad x.vm.left x.vm.right →
        value wch.machine.control.distance ≤ 2 * (rad : ℤ)) ∧
      GalilScaffoldChainVerifier.canRight wch.machine.verifier ∧
        GalilFrontMono.Sane wch.machine.verifier

theorem watchShiftG_of_watchShift {w : List (Fin 2)} {x : State GalilVM}
    (h : WatchShift centre place entry q first w x) : WatchShiftG centre place entry q first w x :=
  fun _ hni s'' hcmp wch hch => (h hni s'' hcmp wch hch).2

/-- `CloseoutPackRun24.shiftLocal_of_watchShift`, guarded. -/
theorem shiftLocalG_of_watchShiftG {w : List (Fin 2)} {x : State GalilVM}
    (hni : x.vm.chain ≠ ChainVM.idle) (hw : WatchShiftG centre place entry q first w x) :
    ShiftLocalG centre place entry q first w x := by
  have key : ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare x.vm s'' →
      beginShiftVM' s'' t'' →
      ∃ wch : GalilScaffoldChainWatch.State, s''.chain = .watch wch := by
    intro s'' t'' _ hb
    obtain ⟨wch, hwch, -⟩ := hb
    exact ⟨wch, hwch⟩
  exact
    { move := fun hs s'' t'' h1 h2 => by
        obtain ⟨wch, hwch⟩ := key s'' t'' h1 h2
        exact (hw hs hni s'' h1 wch hwch).1
      guard := fun hs s'' _ h1 _ wch hwch => (hw hs hni s'' h1 wch hwch).2.1
      coupled := fun hs s'' _ h1 _ wch hwch => (hw hs hni s'' h1 wch hwch).2.2.1
      ver := fun hs s'' _ h1 _ wch hwch => (hw hs hni s'' h1 wch hwch).2.2.2 }

/-- **`BigResid6.rShiftNext` in guarded form, modulo `WatchShiftG` at the
target.**  As in `CloseoutPackRun24.rShiftNext_of_pack`, the pack, the tick and
`SoundScanNR` are not consumed. -/
theorem rShiftNextG_of_pack {w : List (Fin 2)}
    (hws : ∀ y : State GalilVM, WatchShiftG centre place entry q first w y)
    (x y : State GalilVM) (_hx : BigPack2M centre place entry q first w x)
    (_h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (_hg : SoundScanNR w y) :
    ShiftLocalG centre place entry q first w y := by
  by_cases hi : y.vm.chain = ChainVM.idle
  · exact shiftLocalG_of_chainIdle centre place entry q first hi
  · exact shiftLocalG_of_watchShiftG centre place entry q first hi (hws y)

/-- **The guarded shift-entry contract** (the target shape for
`BigResid6.rShiftNext` once `IPackM.shift` is re-cut to `ShiftLocalG`). -/
def RShiftNextG (w : List (Fin 2)) : Prop :=
  ∀ x y : State GalilVM, BigPack2M centre place entry q first w x →
    Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y →
    SoundScanNR w y → ShiftLocalG centre place entry q first w y

theorem rShiftNextG_of_watchShiftG {w : List (Fin 2)}
    (hws : ∀ y : State GalilVM, WatchShiftG centre place entry q first w y) :
    RShiftNextG centre place entry q first w :=
  rShiftNextG_of_pack centre place entry q first hws

end Guarded

#print axioms shiftLocal_of_shiftLocalG
#print axioms shiftLocalG_of_watchShiftG
#print axioms rShiftNextG_of_pack

/-! ## 3. The consumers only read the payload in scan mode -/

section Consumers
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`H_shiftLocalC` guarded.** -/
def H_shiftLocalG (raw : List (Fin 2)) : Prop :=
  ∀ x : State GalilVM, InvLPC raw x.ctl x.vm → ShiftLocalG centre place entry q first raw x

/-- **`H_shiftLocalC` is read at `InvLPC` states only, and those are
scan/non-replaying** (`GalilOracleLocal.invS_mode`), so the guarded form is
enough there. -/
theorem h_shiftLocalC_of_G {raw : List (Fin 2)} (h : H_shiftLocalG centre place entry q first raw) :
    H_shiftLocalC centre place entry q first raw :=
  fun x hIC => shiftLocal_of_shiftLocalG centre place entry q first (invS_mode hIC.1.1.1.1) (h x hIC)

theorem h_shiftLocalG_of_C {raw : List (Fin 2)} (h : H_shiftLocalC centre place entry q first raw) :
    H_shiftLocalG centre place entry q first raw :=
  fun x hIC => shiftLocalG_of_shiftLocal centre place entry q first (h x hIC)

end Consumers


section TickConsumers
variable (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
  (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)

/-- **`CloseoutRadPack2.shiftOrd_tick` with the entry hypothesis guarded.**  The
proof is that theorem's case split verbatim; the hypothesis is consumed only in
`scan_shift`, where the branch's own `hm : c.mode = .scan` and
`hr : c.replaying = false` discharge the guard. -/
theorem shiftOrd_tickG {c c' : Control} {s t : GalilVM} (hS : ShiftOrd c s)
    (hcanr : GalilScaffoldCounter.Canonical s.remaining)
    (hsaneC : GalilFrontMono.Sane s.center)
    (hcopy : c.mode = Mode.shift → CopyIdle s)
    (hentry : c.mode = Mode.scan → c.replaying = false → ∀ s'' t'' : GalilVM,
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
    exact fun _ => hentry hm hr s' t hcmp hb
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

/-- **`CloseoutRadPack4.saneTick` with the entry hypothesis guarded**, likewise. -/
theorem saneTickG {c c' : Control} {s t : GalilVM}
    (hx : SaneVer s.chain) (hC : GalilFrontMono.Sane s.center)
    (hen : c.mode = Mode.scan → c.replaying = false → ∀ s'' t'' : GalilVM,
      (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).compare s s'' →
      beginShiftVM' s'' t'' → SaneVer t''.chain)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : SaneVer t.chain := by
  cases h
  case init =>
    rename_i hm hi
    obtain ⟨-, -, -, -, -, -, -, -, -, hch, -⟩ : initVM entry s t := hi
    exact saneVer_congr hch saneVer_idle
  case scan_wait =>
    rename_i hm hav hb
    obtain ⟨-, -, hch, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    exact chainAt_sane hch hx hC
  case scan_count =>
    rename_i hm hc hav hb
    obtain ⟨-, -, hch, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    exact chainAt_sane hch hx hC
  case restart =>
    rename_i hm hb
    obtain ⟨w, -, -, -, -, ht⟩ : restartVM entry s t := hb
    subst ht
    exact saneVer_idle
  case scan_match =>
    rename_i s' o hmt hm hc hcmp hav hpl ho
    obtain ⟨a, found, ans, cc, wk, hch, -⟩ :=
      compare_chainAt onLetter leftFirst centre place entry q first hcmp
    have hpl' : t = (if c.replaying then
        {s' with replay := GalilScaffoldCounter.dec s'.replay} else s') := hpl
    have htc : t.chain = s'.chain := by rw [hpl']; cases c.replaying <;> rfl
    exact saneVer_congr htc (chainAt_sane hch hx hC)
  case scan_shift =>
    rename_i s' hmt hg hm hc hr hcmp hav hb
    exact hen hm hr s' t hcmp hb
  case scan_fallback =>
    rename_i s' hmt hm hc hg hr hcmp hav hb
    obtain ⟨pl, ht, -⟩ : beginFallbackVM' s' t := hb
    subst ht
    exact saneVer_idle
  case shift_one =>
    rename_i hm hp hi
    obtain ⟨-, -, -, w, hw, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    subst ht
    have hws : s.chain = .watch w := hw
    exact fun r hr => hx r (by rw [hws]; exact hr)
  case shift_done =>
    rename_i o hm hp ho
    exact hx
  case replayStart =>
    rename_i o hm ho ho' hi
    obtain ⟨-, -, -, -, -, -, -, -, -, hch, -⟩ : replayStartVM entry s t := hi
    exact saneVer_congr hch saneVer_idle
  all_goals
    (rename_i hi
     have hch : t.chain = s.chain := (congrArg GalilVM.chain hi.2).trans rfl
     exact saneVer_congr hch hx)

end TickConsumers

#print axioms h_shiftLocalC_of_G
#print axioms shiftOrd_tickG
#print axioms saneTickG

/-! ## 4. `pal_in_peg_final16` -/

/-- **`CloseoutPackRun18.pal_in_peg_final15` with `H_shiftLocalC` replaced by its
guarded form `H_shiftLocalG`** (free, by `h_shiftLocalC_of_G`: it is only read at
`InvLPC` states, which are scan/non-replaying).  `BigResid6` — and with it the
*unguarded* `rShiftNext`, refuted at shift landings by
`shiftLocal_false_at_landing` — is **unchanged** here: guarding it means
re-cutting `IPackM.shift` to `ShiftLocalG` through `StepsIM` / `CycleOracleIM` /
`PreTraceIM` / `pal_in_peg_final5M`, which this file does not do.  The target
contract is `RShiftNextG`, discharged modulo `WatchShiftG` by
`rShiftNextG_of_pack`. -/
theorem pal_in_peg_final16 (entry q : ℕ) (first : Fin 9)
    (hr : ∀ w : List (Fin 2), BigResid6 centreC placeC entry q first w)
    (hee : ∀ w : List (Fin 2), H_extraEntry3 centreC placeC entry w)
    (het : ∀ w : List (Fin 2), H_extraTick3 centreC placeC entry q first w)
    (hme : ∀ w : List (Fin 2), H_marksEntry' (PofC centreC placeC entry w) q first)
    (hsl : ∀ w : List (Fin 2), H_shiftLocalG centreC placeC entry q first w)
    (hsc : ∀ w : List (Fin 2), H_stageScan centreC placeC entry q first w)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleMC3 (PofC centreC placeC entry w) q first w)
    (hbs : H_bootShift centreC placeC entry q first)
    (hls : H_landShift centreC placeC entry q first)
    (hC : H_realizeLIM' centreC placeC entry q first) :
    RecognizedByTotalPEG PAL :=
  pal_in_peg_final15 entry q first hr hee het hme
    (fun w => h_shiftLocalC_of_G centreC placeC entry q first (hsl w)) hsc hor hbs hls hC

#print axioms pal_in_peg_final16

end PalPeg.CloseoutPackRun26
