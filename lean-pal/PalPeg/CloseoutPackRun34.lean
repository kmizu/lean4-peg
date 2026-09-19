import PalPeg.CloseoutPackRun32
import PalPeg.CloseoutPackRun30

/-!
# `CloseoutPackRun34`: `WatchShiftG` restricted to guarded targets, and a
positional chain invariant that produces it

`CloseoutPackRun32` showed that `CloseoutPackRun26.WatchShiftG` is false at
*unguarded* comparison targets (a watch born at `ChainStep.backDone` has
`distance = reset`).  This file re-cuts the payload to the targets the only
reader — the `scan_shift` tick — actually sees: unmatched (`hmt`) and
`shiftGuardVM`-guarded (`hg`), i.e. phase `4`, lag `0`, unbroken.

* §1 `WatchShiftS`: `WatchShiftG`'s payload under the two extra premises
  `¬ matched s''` and `shiftGuardVM s''`.  `watchShiftS_of_watchShiftG`.
* §2 The consumer check.  `ShiftLocalG`'s fields (Run26:198) are invoked at
  `beginShiftVM'` targets *without* the guard (`halfBound_of_ipackMG`
  Run30:523, `shiftVerSane_ptMG` Run30:558), and `beginShiftVM'` does **not**
  imply `shiftGuardVM` (`beginShiftVM` is `s.chain = .watch w ∧ t = …`,
  GalilScaffoldTopShiftCycle:23).  So `shiftLocalG_of_watchShiftS` is **not
  provable** as stated; what is provable is the guarded re-cut `ShiftLocalS`
  (fields under `¬ matched ∧ shiftGuardVM`), `shiftLocalS_of_watchShiftS`,
  `rShiftNextMS_of_watchShiftS`, and the consumers re-cut to the guard:
  `halfBound_of_shiftLocalS` (the Run30:523 reader) and `shiftOrd_tickS`
  (Run26:334 with a guarded `hentry`: the `scan_shift` branch owns `hmt`/`hg`,
  every other branch is vacuous or has `c.mode ≠ scan`).
* §3 `ChainPositionInvariant`: `Coupled` (whose `sum` is exactly `distance + lag =
  radius`, `GalilChainCoupling.SumRel`) plus, under `ScanNR ∧ chain ≠ idle`,
  the positional payload `ScanPositionPayload`: `canRight right`, the radius ledger
  `value radius ≤ rad` against `ScanInvariant`, the verifier position
  `position verifier + lag = position right`, and `canRight ∧ Sane` of the
  verifier one `ChainTick` away.  `watchShiftS_of_chainPosInv` closes
  `canRight`, `distance ≤ 2·rad` (guard's `lag = 0` + `SumRel` + ledger) and
  the verifier pair; `4·h ≤ distance` is closed in the fresh (`FreshC`) half
  of `WatchOK` (`four_of_freshC`) and named `H_FourSemiperiodsLeDistance` in the post-shift
  (`Other`) half, where `guard_budget` only yields `h ≤ R + 1`.
  `chainPosInv_tick`: `Coupled` by `coupled_tick`, 20/23 shapes closed;
  `H_BackgroundLandingPayload` (`scan_wait`/`scan_count`), `H_MatchLandingPayload` (`scan_match`),
  `H_ShiftExitPayload` (`shift_done`) are the three named branch hypotheses, each
  restricted to `ScanPositionPayload` (the `Coupled` half needs nothing).

Standard axioms only; unconditional `PAL ∈ PEG` remains open.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun34

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilFrontMono PalPeg.GalilChainCoupling
open PalPeg.CloseoutLPack5 PalPeg.CloseoutPackRun6 PalPeg.CloseoutPackRun10
open PalPeg.CloseoutRadPack2 PalPeg.CloseoutRadPack4
open PalPeg.CloseoutPackRun26 PalPeg.CloseoutPackRun30 PalPeg.CloseoutPackRun32

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-! ## 1. `WatchShiftS` -/

/-- **`WatchShiftG` at guarded targets only**: the payload is asserted for
comparison targets that are unmatched and pass `shiftGuardVM` — exactly the
`scan_shift` tick's `hmt` and `hg`. -/
def WatchShiftS (w : List (Fin 2)) (x : State GalilVM) : Prop :=
  ScanNR x → x.vm.chain ≠ ChainVM.idle →
  ∀ s'' : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).compare x.vm s'' →
    ¬ (galilFrameS (PofC centre place entry w) q first).matched s'' →
    shiftGuardVM s'' →
    ∀ wch : GalilScaffoldChainWatch.State, s''.chain = .watch wch →
      GalilScaffoldChainVerifier.canRight x.vm.right ∧
      4 * (periodLength wch : ℤ) ≤ value wch.machine.control.distance ∧
      (∀ rad : ℕ, ScanInvariant w (position x.vm.center) rad x.vm.left x.vm.right →
        value wch.machine.control.distance ≤ 2 * (rad : ℤ)) ∧
      GalilScaffoldChainVerifier.canRight wch.machine.verifier ∧
        GalilFrontMono.Sane wch.machine.verifier

theorem watchShiftS_of_watchShiftG {w : List (Fin 2)} {x : State GalilVM}
    (h : WatchShiftG centre place entry q first w x) : WatchShiftS centre place entry q first w x :=
  fun hs hni s'' hcmp _ _ wch hch => h hs hni s'' hcmp wch hch

/-! ## 2. The consumer check: `ShiftLocalS` -/

/-- **`ShiftLocalG` with every field additionally guarded by `¬ matched s''`
and `shiftGuardVM s''`.** -/
structure ShiftLocalS (w : List (Fin 2)) (x : State GalilVM) : Prop where
  move : ScanNR x → ∀ s'' t'' : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).compare x.vm s'' →
    ¬ (galilFrameS (PofC centre place entry w) q first).matched s'' → shiftGuardVM s'' →
    beginShiftVM' s'' t'' → GalilScaffoldChainVerifier.canRight x.vm.right
  guard : ScanNR x → ∀ s'' t'' : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).compare x.vm s'' →
    ¬ (galilFrameS (PofC centre place entry w) q first).matched s'' → shiftGuardVM s'' →
    beginShiftVM' s'' t'' →
    ∀ wch : GalilScaffoldChainWatch.State, s''.chain = .watch wch →
      4 * (periodLength wch : ℤ) ≤ value wch.machine.control.distance
  coupled : ScanNR x → ∀ s'' t'' : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).compare x.vm s'' →
    ¬ (galilFrameS (PofC centre place entry w) q first).matched s'' → shiftGuardVM s'' →
    beginShiftVM' s'' t'' →
    ∀ wch : GalilScaffoldChainWatch.State, s''.chain = .watch wch →
      ∀ rad : ℕ, ScanInvariant w (position x.vm.center) rad x.vm.left x.vm.right →
        value wch.machine.control.distance ≤ 2 * (rad : ℤ)
  ver : ScanNR x → ∀ s'' t'' : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).compare x.vm s'' →
    ¬ (galilFrameS (PofC centre place entry w) q first).matched s'' → shiftGuardVM s'' →
    beginShiftVM' s'' t'' →
    ∀ wch : GalilScaffoldChainWatch.State, s''.chain = .watch wch →
      GalilScaffoldChainVerifier.canRight wch.machine.verifier ∧
        GalilFrontMono.Sane wch.machine.verifier

theorem shiftLocalS_of_shiftLocalG {w : List (Fin 2)} {x : State GalilVM}
    (h : ShiftLocalG centre place entry q first w x) : ShiftLocalS centre place entry q first w x :=
  { move := fun hs s'' t'' h1 _ _ h2 => h.move hs s'' t'' h1 h2,
    guard := fun hs s'' t'' h1 _ _ h2 => h.guard hs s'' t'' h1 h2,
    coupled := fun hs s'' t'' h1 _ _ h2 => h.coupled hs s'' t'' h1 h2,
    ver := fun hs s'' t'' h1 _ _ h2 => h.ver hs s'' t'' h1 h2 }

theorem shiftLocalS_of_chainIdle {w : List (Fin 2)} {x : State GalilVM}
    (hi : x.vm.chain = ChainVM.idle) : ShiftLocalS centre place entry q first w x :=
  shiftLocalS_of_shiftLocalG centre place entry q first
    (shiftLocalG_of_chainIdle centre place entry q first hi)

/-- `CloseoutPackRun26.shiftLocalG_of_watchShiftG`, guarded. -/
theorem shiftLocalS_of_watchShiftS {w : List (Fin 2)} {x : State GalilVM}
    (hni : x.vm.chain ≠ ChainVM.idle) (hw : WatchShiftS centre place entry q first w x) :
    ShiftLocalS centre place entry q first w x := by
  have key : ∀ s'' t'' : GalilVM, beginShiftVM' s'' t'' →
      ∃ wch : GalilScaffoldChainWatch.State, s''.chain = .watch wch := by
    intro s'' t'' hb
    obtain ⟨wch, hwch, -⟩ := hb
    exact ⟨wch, hwch⟩
  exact
    { move := fun hs s'' t'' h1 hmt hg h2 => by
        obtain ⟨wch, hwch⟩ := key s'' t'' h2
        exact (hw hs hni s'' h1 hmt hg wch hwch).1
      guard := fun hs s'' _ h1 hmt hg _ wch hwch => (hw hs hni s'' h1 hmt hg wch hwch).2.1
      coupled := fun hs s'' _ h1 hmt hg _ wch hwch => (hw hs hni s'' h1 hmt hg wch hwch).2.2.1
      ver := fun hs s'' _ h1 hmt hg _ wch hwch => (hw hs hni s'' h1 hmt hg wch hwch).2.2.2 }

/-- `CloseoutPackRun30.RShiftNextMG` concluding `ShiftLocalS`. -/
def RShiftNextMS (w : List (Fin 2)) : Prop :=
  ∀ x y : State GalilVM, BigPack2MG centre place entry q first w x →
    Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y →
    SoundScanNR w y → ShiftLocalS centre place entry q first w y

theorem rShiftNextMS_of_rShiftNextMG {w : List (Fin 2)}
    (h : RShiftNextMG centre place entry q first w) : RShiftNextMS centre place entry q first w :=
  fun x y hx ht hg => shiftLocalS_of_shiftLocalG centre place entry q first (h x y hx ht hg)

/-- `CloseoutPackRun30.rShiftNextMG_of_watchShiftG`, guarded. -/
theorem rShiftNextMS_of_watchShiftS {w : List (Fin 2)}
    (hws : ∀ y : State GalilVM, WatchShiftS centre place entry q first w y) :
    RShiftNextMS centre place entry q first w := by
  intro x y _ _ _
  by_cases hi : y.vm.chain = ChainVM.idle
  · exact shiftLocalS_of_chainIdle centre place entry q first hi
  · exact shiftLocalS_of_watchShiftS centre place entry q first hi (hws y)

/-- **The Run30:523 reader re-cut to the guard**: `halfBound_of_ipackMG`'s
conclusion from `LPackM` plus `ShiftLocalS`, at an unmatched guarded target. -/
theorem halfBound_of_shiftLocalS {w : List (Fin 2)} {x : State GalilVM}
    (hp : LPackM w x.ctl x.vm) (hsh : ShiftLocalS centre place entry q first w x)
    (hs : ScanNR x) {s'' t'' : GalilVM}
    (hcmp : (galilFrameS (PofC centre place entry w) q first).compare x.vm s'')
    (hmt : ¬ (galilFrameS (PofC centre place entry w) q first).matched s'')
    (hg : shiftGuardVM s'') (hb : beginShiftVM' s'' t'') :
    ∃ rad : ℕ,
      ScanInvariant w (position x.vm.center) rad x.vm.left x.vm.right ∧
      GalilScaffoldChainVerifier.canRight x.vm.right ∧
      ∀ wch : GalilScaffoldChainWatch.State, s''.chain = .watch wch →
        2 * periodLength wch ≤ rad := by
  obtain ⟨rad, hscan⟩ := hp.scanGeom hs.1 hs.2
  refine ⟨rad, hscan, hsh.move hs s'' t'' hcmp hmt hg hb, fun wch hch => ?_⟩
  have h4 := hsh.guard hs s'' t'' hcmp hmt hg hb wch hch
  have h2 := hsh.coupled hs s'' t'' hcmp hmt hg hb wch hch rad hscan
  omega

end

#print axioms watchShiftS_of_watchShiftG
#print axioms shiftLocalS_of_watchShiftS
#print axioms rShiftNextMS_of_watchShiftS
#print axioms halfBound_of_shiftLocalS

section TickConsumer
variable (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
  (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)

/-- **`CloseoutPackRun26.shiftOrd_tickG` with the entry hypothesis guarded by
`¬ matched` and `shiftGuardVM`.**  The `scan_shift` branch owns both; every
scan-mode branch other than `scan_shift` lands in a non-shift mode, and every
branch with `c.mode ≠ scan` is handed `shiftOrd_tickG` with a vacuous entry. -/
theorem shiftOrd_tickS {c c' : Control} {s t : GalilVM} (hS : ShiftOrd c s)
    (hcanr : GalilScaffoldCounter.Canonical s.remaining)
    (hsaneC : GalilFrontMono.Sane s.center)
    (hcopy : c.mode = Mode.shift → CopyIdle s)
    (hentry : c.mode = Mode.scan → c.replaying = false → ∀ s'' t'' : GalilVM,
      (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).compare s s'' →
      ¬ (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).matched s'' →
      shiftGuardVM s'' → beginShiftVM' s'' t'' → ShiftBud t'')
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : ShiftOrd c' t := by
  cases h
  case scan_shift =>
    rename_i s' hmt hg hm hc hr hcmp hav hb
    exact fun _ => hentry hm hr s' t hcmp hmt hg hb
  case scan_wait =>
    rename_i hm hav hb
    exact fun hm' => Mode.noConfusion (hm.symm.trans hm')
  case scan_count =>
    rename_i hm hc hav hb
    exact fun hm' => Mode.noConfusion (hm.symm.trans hm')
  case scan_match =>
    rename_i s' o hmt hm hc hcmp hav hpl ho
    exact fun hm' => Mode.noConfusion (hm.symm.trans hm')
  case scan_fallback =>
    rename_i s' hmt hm hc hg hr hcmp hav hb
    exact fun hm' => Mode.noConfusion hm'
  case shift_one =>
    rename_i hm hp hi
    exact shiftOrd_tickG onLetter leftFirst centre place entry q first delay hS hcanr hsaneC hcopy
      (fun hms => Mode.noConfusion (hm.symm.trans hms)) (Tick.shift_one c s t hm hp hi)
  case init => exact fun hm' => Mode.noConfusion hm'
  case restart =>
    rename_i hm hb
    exact fun hm' => Mode.noConfusion (hm.symm.trans hm')
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

end TickConsumer

#print axioms shiftOrd_tickS

/-! ## 3. The positional invariant -/

/-- Phase `4` of a fresh (`FreshC`) watch control gives `4·h ≤ distance`. -/
theorem four_of_freshC {k : GalilScaffoldChainConsume.State} (hph : k.phase = 4) (hf : FreshC k) :
    4 * ((k.period.left.length + k.period.right.length : ℕ) : ℤ) ≤ value k.distance := by
  have hpv : (k.phase.val : ℤ) = 4 := by rw [hph]; rfl
  cases hfw : k.forward with
  | true =>
    obtain ⟨h1, h2⟩ := hf.1 hfw
    rw [hpv] at h2
    have : (1 : ℤ) ≤ k.period.left.length := by exact_mod_cast h1
    linarith
  | false =>
    obtain ⟨h1, h2⟩ := hf.2 hfw
    rw [hpv] at h2
    have : (k.period.left.length : ℤ) + 1 ≤
        ((k.period.left.length + k.period.right.length : ℕ) : ℤ) := by exact_mod_cast h1
    linarith

section Pos
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **The positional payload** at a scanning state with a live chain. -/
structure ScanPositionPayload (w : List (Fin 2)) (s : GalilVM) : Prop where
  /-- The right head can move. -/
  canR : GalilScaffoldChainVerifier.canRight s.right
  /-- The radius ledger against the scan geometry. -/
  radLe : ∀ rad : ℕ, ScanInvariant w (position s.center) rad s.left s.right →
    value s.radius ≤ (rad : ℤ)
  /-- The verifier sits `lag` cells behind the right head. -/
  pos : ∀ wch : GalilScaffoldChainWatch.State, s.chain = .watch wch →
    (position wch.machine.verifier : ℤ) + value wch.lag = position s.right
  /-- The verifier of every watch one chain tick away can move and is sane. -/
  verNext : ∀ (a : Bool) (z : ChainVM) (wch : GalilScaffoldChainWatch.State),
    ChainTick a s.chain z → z = .watch wch →
      GalilScaffoldChainVerifier.canRight wch.machine.verifier ∧
        GalilFrontMono.Sane wch.machine.verifier

/-- **`ChainPositionInvariant`**: `Coupled` (its `sum` is `distance + lag = radius`) and,
under `ScanNR ∧ chain ≠ idle`, the positional payload. -/
structure ChainPositionInvariant (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  coupled : Coupled c s
  payload : ScanNR ⟨c, s⟩ → s.chain ≠ ChainVM.idle → ScanPositionPayload w s

/-- `distance + lag = radius` read off `ChainPositionInvariant`. -/
theorem chainPosInv_sum {w : List (Fin 2)} {c : Control} {s : GalilVM} (h : ChainPositionInvariant w c s)
    {wch : GalilScaffoldChainWatch.State} (hw : s.chain = .watch wch)
    (hbr : wch.machine.control.broken = false) :
    value wch.machine.control.distance + value wch.lag = value s.radius := by
  have hs := h.coupled.sum
  rw [hw] at hs
  exact hs hbr

theorem chainPosInv_of_idle {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hi : s.chain = ChainVM.idle) : ChainPositionInvariant w c s :=
  ⟨coupled_of_idle hi, fun _ hni => absurd hi hni⟩

/-- **(NAMED) `H_FourSemiperiodsLeDistance`.**  At an unmatched guarded target whose watch is in
the post-shift (`Other`) half of `WatchOK`, `4·h ≤ distance`.  (`guard_budget`
gives only `h ≤ R + 1` there.) -/
def H_FourSemiperiodsLeDistance (w : List (Fin 2)) : Prop :=
  ∀ (x : State GalilVM) (s'' : GalilVM) (wch : GalilScaffoldChainWatch.State),
    ScanNR x → x.vm.chain ≠ ChainVM.idle →
    (galilFrameS (PofC centre place entry w) q first).compare x.vm s'' →
    ¬ (galilFrameS (PofC centre place entry w) q first).matched s'' →
    shiftGuardVM s'' → s''.chain = .watch wch →
    Other x.vm.periodOnly x.ctl.mode (value x.vm.radius) (value x.vm.cycle)
      (value x.vm.remaining) (periodLength wch) →
    4 * (periodLength wch : ℤ) ≤ value wch.machine.control.distance

/-- **`WatchShiftS` from `ChainPositionInvariant`**, modulo `H_FourSemiperiodsLeDistance`. -/
theorem watchShiftS_of_chainPosInv {w : List (Fin 2)}
    (hfour : H_FourSemiperiodsLeDistance centre place entry q first w) {x : State GalilVM}
    (h : ChainPositionInvariant w x.ctl x.vm) : WatchShiftS centre place entry q first w x := by
  intro hs hni s'' hcmp hmt hg wch hch
  have hs' : ScanNR ⟨x.ctl, x.vm⟩ := hs
  have P := h.payload hs' hni
  obtain ⟨a, ht⟩ := compareFound_chainTick q first hcmp hni
  have hver := P.verNext a s''.chain wch ht hch
  obtain ⟨-, -, -, -, hmis⟩ :=
    compare_inv (onLetterVM w) leftFirstVM centre place entry q first h.coupled hs.1 hcmp
  obtain ⟨-, -, hsum, hwk⟩ := hmis hmt
  have hg' := hg
  obtain ⟨w1, hw1, hz, hph, hbr, -, -⟩ := hg'
  have hch' := hch
  rw [hw1] at hch'
  injection hch' with hwe
  rw [hwe] at hw1 hz hph hbr
  rw [hw1] at hsum hwk
  have hd : value wch.machine.control.distance + value wch.lag = value x.vm.radius := hsum hbr
  rw [value_zero_of_zero hz] at hd
  refine ⟨P.canR, ?_, ?_, hver⟩
  · rcases hwk wch rfl hbr with ⟨-, hf⟩ | hO
    · exact four_of_freshC hph hf
    · exact hfour x s'' wch hs hni hcmp hmt hg hch hO
  · intro rad hsc
    have := P.radLe rad hsc
    omega

/-! ### Preservation along ticks -/

/-- **(NAMED) `H_BackgroundLandingPayload`.**  A `backgroundS` step from a scanning source
(`scan_wait` / `scan_count`) preserves the positional payload. -/
def H_BackgroundLandingPayload (w : List (Fin 2)) : Prop :=
  ∀ (c : Control) (s t : GalilVM), c.mode = Mode.scan → ChainPositionInvariant w c s →
    (galilFrameS (PofC centre place entry w) q first).background s t →
    ScanNR ⟨c, t⟩ → t.chain ≠ ChainVM.idle → ScanPositionPayload w t

/-- **(NAMED) `H_MatchLandingPayload`.**  The `scan_match` landing preserves the positional
payload. -/
def H_MatchLandingPayload (w : List (Fin 2)) : Prop :=
  ∀ (c : Control) (s s' t : GalilVM) (o b : Bool), c.mode = Mode.scan → ChainPositionInvariant w c s →
    (galilFrameS (PofC centre place entry w) q first).compare s s' →
    (galilFrameS (PofC centre place entry w) q first).matched s' →
    (galilFrameS (PofC centre place entry w) q first).matchedPlace c.replaying s' t →
    ScanNR ⟨{c with clock := 2048, output := o, replaying := c.replaying && b}, t⟩ →
    t.chain ≠ ChainVM.idle → ScanPositionPayload w t

/-- **(NAMED) `H_ShiftExitPayload`.**  The `shift_done` landing (VM unchanged, the
chain is the post-shift watch) establishes the positional payload. -/
def H_ShiftExitPayload (w : List (Fin 2)) : Prop :=
  ∀ (c : Control) (s : GalilVM) (o : Bool), c.mode = Mode.shift →
    ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos s →
    ChainPositionInvariant w c s →
    ScanNR ⟨{c with mode := Mode.scan, output := o}, s⟩ → s.chain ≠ ChainVM.idle →
    ScanPositionPayload w s

/-- **One tick of `ChainPositionInvariant`**: `Coupled` by `coupled_tick`; the payload
by the three named hypotheses at the scan landings, vacuity elsewhere. -/
theorem chainPosInv_tick {w : List (Fin 2)}
    (hbg : H_BackgroundLandingPayload centre place entry q first w) (hmatch : H_MatchLandingPayload centre place entry q first w)
    (hsd : H_ShiftExitPayload centre place entry q first w)
    {x y : State GalilVM} (hx : ChainPositionInvariant w x.ctl x.vm)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y) :
    ChainPositionInvariant w y.ctl y.vm := by
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  refine ⟨coupled_tick (onLetterVM w) leftFirstVM centre place entry q first 2048 hx.coupled h, ?_⟩
  cases h
  case init =>
    rename_i hm hi
    obtain ⟨-, -, -, -, -, -, -, -, -, hch, -⟩ : initVM entry s t := hi
    exact fun _ hni => absurd hch hni
  case scan_wait =>
    rename_i hm hav hb
    exact fun hs hni => hbg c s t hm hx hb hs hni
  case scan_count =>
    rename_i hm hc hav hb
    exact fun hs hni => hbg c s t hm hx hb ⟨hm, hs.2⟩ hni
  case scan_match =>
    rename_i s' o hmt hm hc hcmp hav hpl ho
    exact fun hs hni => hmatch c s s' t o _ hm hx hcmp hmt hpl hs hni
  case shift_done =>
    rename_i o hm hp ho
    exact fun hs hni => hsd c s o hm hp hx hs hni
  case replayStart =>
    rename_i o hm ho ho' hi
    obtain ⟨-, -, -, -, -, -, -, -, -, hch, -⟩ : replayStartVM entry s t := hi
    exact fun _ hni => absurd hch hni
  case restart =>
    rename_i hm hb
    obtain ⟨w', -, -, -, -, ht⟩ : restartVM entry s t := hb
    subst ht
    exact fun _ hni => absurd rfl hni
  all_goals
    exact fun h1 _ => by
      obtain ⟨h2, -⟩ := h1
      simp_all

end Pos

#print axioms four_of_freshC
#print axioms watchShiftS_of_chainPosInv
#print axioms chainPosInv_tick

end PalPeg.CloseoutPackRun34
