import PalPeg.CloseoutPackRun29
import PalPeg.CloseoutPackRun26

/-!
# `CloseoutPackRun32`: a producer for `WatchShiftG` — the chain–scan invariant

`CloseoutPackRun26.WatchShiftG` speaks about *every* comparison target `s''`
of a `ScanNR` state `x` with a non-idle chain whose chain watches `wch`.  By
`compareFound` (with `x.vm.chain ≠ .idle`) `s''.chain` is exactly a
`ChainTick a x.vm.chain _` successor and the scan heads named by the payload
are the *source* heads `x.vm.left / x.vm.center / x.vm.right`.  So the minimal
datum that produces `WatchShiftG` is a one-`ChainTick`-closed record on the
source: `canRight` of the right head, and for every watch one chain tick away
its `4·period ≤ distance`, `distance ≤ 2·rad` (against the source scan
invariant), and `canRight ∧ Sane` of its verifier.  That record is
`ChainScanInv` (§1); `watchShiftG_of_chainScanInv` (§2) is the producer.

§3 is preservation along `galilFrameS` ticks.  Of the 23 tick shapes, 19 are
closed here: every non-scan landing mode is vacuous under `ScanNR`
(`scan_shift`, `scan_fallback`, `shift_one`, `copy_*`, `home_*`, `fpp_*`,
`markEnd_*`, `choose_*`, `rewind_*`), and `init` / `replayStart` / `restart`
land with an idle chain (`initVM` / `replayStartVM` / `restartVM`).  The
remaining four shapes (three hypotheses) are the ones where a watching chain survives a scan
tick, and each is a named hypothesis (one per branch):

* `H_bg` — `scan_wait` and `scan_count` (the same VM effect, `backgroundS`:
  heads fixed, chain by `chainAt false`);
* `H_match` — `scan_match` (heads moved, chain by `chainAt true`, replay
  countdown);
* `H_shiftDone` — `shift_done` (VM unchanged, the chain is the post-shift
  watch).

**Caveat (design, not proved here).**  `WatchShiftG` is stated at *unguarded*
targets.  A fresh watch born at `ChainStep.backDone` has
`watchControl`'s `distance = reset` (value `0`), so at the first scan
comparison after the birth the target watch violates `4·periodLength ≤
distance` whenever `periodLength ≥ 1`.  Hence `∀ y, WatchShiftG … y` cannot be
produced by any invariant that is true at those states; `H_bg`/`H_match` are
therefore expected to be dischargeable only after `WatchShiftG`'s payload is
restricted to `shiftGuardVM`-guarded targets (the `scan_shift` tick's own
`hg`, phase `4` and lag `0`), which is where `guard_budget` lives.

Standard axioms only; unconditional `PAL ∈ PEG` remains open.
-/

set_option autoImplicit false

namespace PalPeg.CloseoutPackRun32

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilFrontMono PalPeg.GalilChainCoupling
open PalPeg.CloseoutPackRun26

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-! ## 1. The chain–scan invariant -/

/-- The payload `WatchShiftG` demands of one target watch `wch`, against the
source heads `s`. -/
def WatchPayload (w : List (Fin 2)) (s : GalilVM) (wch : GalilScaffoldChainWatch.State) : Prop :=
  4 * (periodLength wch : ℤ) ≤ value wch.machine.control.distance ∧
  (∀ rad : ℕ, ScanInvariant w (position s.center) rad s.left s.right →
    value wch.machine.control.distance ≤ 2 * (rad : ℤ)) ∧
  GalilScaffoldChainVerifier.canRight wch.machine.verifier ∧
    GalilFrontMono.Sane wch.machine.verifier

/-- **The chain–scan invariant.**  Under `ScanNR` with a non-idle chain: the
right head can move, and every watch one `ChainTick` (either event) away from
the current chain carries the payload against the current heads. -/
structure ChainScanInv (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  canR : ScanNR ⟨c, s⟩ → s.chain ≠ ChainVM.idle → GalilScaffoldChainVerifier.canRight s.right
  next : ScanNR ⟨c, s⟩ → s.chain ≠ ChainVM.idle →
    ∀ (a : Bool) (z : ChainVM) (wch : GalilScaffoldChainWatch.State),
      ChainTick a s.chain z → z = .watch wch → WatchPayload w s wch

/-- Vacuous at an idle chain. -/
theorem chainScanInv_of_idle {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hi : s.chain = ChainVM.idle) : ChainScanInv w c s :=
  ⟨fun _ hni => absurd hi hni, fun _ hni => absurd hi hni⟩

/-- Vacuous off `ScanNR`. -/
theorem chainScanInv_of_notScanNR {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hn : ¬ ScanNR ⟨c, s⟩) : ChainScanInv w c s :=
  ⟨fun hs => absurd hs hn, fun hs => absurd hs hn⟩

/-- Only `mode` and `replaying` of the controller matter. -/
theorem chainScanInv_congr {w : List (Fin 2)} {c c' : Control} {s : GalilVM}
    (hm : c'.mode = c.mode) (hr : c'.replaying = c.replaying) (h : ChainScanInv w c s) :
    ChainScanInv w c' s :=
  ⟨fun hs => h.canR ⟨by rw [← hm]; exact hs.1, by rw [← hr]; exact hs.2⟩,
   fun hs => h.next ⟨by rw [← hm]; exact hs.1, by rw [← hr]; exact hs.2⟩⟩

/-! ## 2. The producer -/

/-- The chain of a `compareFound` target of a non-idle-chain source is one
`ChainTick` away from the source chain. -/
theorem compareFound_chainTick {P : Shared} {s s'' : GalilVM}
    (hcmp : (galilFrameS P q first).compare s s'') (hni : s.chain ≠ ChainVM.idle) :
    ∃ a : Bool, ChainTick a s.chain s''.chain := by
  obtain ⟨vs, vq, a, -, -, -, -, hch, hteq⟩ : compareFound P q first s s'' := hcmp
  have hc : s''.chain = vs.chain := by
    rw [hteq, afterBirth_of_ne_idle hni]; cases a <;> rfl
  rw [hc]
  rcases hch with ⟨-, ht⟩ | ⟨hi, -⟩ | ⟨hi, -⟩
  · exact ⟨a, ht⟩
  · exact absurd hi hni
  · exact absurd hi hni

/-- **`WatchShiftG` from `ChainScanInv`.** -/
theorem watchShiftG_of_chainScanInv {w : List (Fin 2)} {x : State GalilVM}
    (h : ChainScanInv w x.ctl x.vm) : WatchShiftG centre place entry q first w x := by
  intro hs hni s'' hcmp wch hch
  have hs' : ScanNR ⟨x.ctl, x.vm⟩ := hs
  obtain ⟨a, ht⟩ := compareFound_chainTick q first hcmp hni
  obtain ⟨h1, h2, h3, h4⟩ := h.next hs' hni a s''.chain wch ht hch
  exact ⟨h.canR hs' hni, h1, h2, h3, h4⟩

/-! ## 3. Preservation along ticks -/

/-- **(NAMED) `H_bg`.**  A `backgroundS` step from a `ScanNR` source (the VM
effect of `scan_wait` and `scan_count`: heads fixed, chain by `chainAt false`)
preserves the invariant. -/
def H_bg (w : List (Fin 2)) : Prop :=
  ∀ (c : Control) (s t : GalilVM), c.mode = Mode.scan → ChainScanInv w c s →
    (galilFrameS (PofC centre place entry w) q first).background s t → ChainScanInv w c t

/-- **(NAMED) `H_match`.**  The `scan_match` landing: a matched comparison
target `s'` (heads moved, chain by `chainAt true`) followed by
`matchedPlace`'s replay countdown. -/
def H_match (w : List (Fin 2)) : Prop :=
  ∀ (c : Control) (s s' t : GalilVM) (o b : Bool), c.mode = Mode.scan → ChainScanInv w c s →
    (galilFrameS (PofC centre place entry w) q first).compare s s' →
    (galilFrameS (PofC centre place entry w) q first).matched s' →
    (galilFrameS (PofC centre place entry w) q first).matchedPlace c.replaying s' t →
    ChainScanInv w {c with clock := 2048, output := o, replaying := c.replaying && b} t

/-- **(NAMED) `H_shiftDone`.**  The `shift_done` landing: the VM is unchanged,
the chain is the post-shift watch, the mode returns to `scan`. -/
def H_shiftDone (w : List (Fin 2)) : Prop :=
  ∀ (c : Control) (s : GalilVM) (o : Bool), c.mode = Mode.shift →
    ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos s →
    ChainScanInv w {c with mode := Mode.scan, output := o} s

/-- **One tick of `ChainScanInv`**, modulo the three named branch hypotheses. -/
theorem chainScanInv_tick {w : List (Fin 2)}
    (hbg : H_bg centre place entry q first w) (hmatch : H_match centre place entry q first w)
    (hsd : H_shiftDone centre place entry q first w)
    {x y : State GalilVM} (hx : ChainScanInv w x.ctl x.vm)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y) :
    ChainScanInv w y.ctl y.vm := by
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  cases h
  case init =>
    rename_i hm hi
    obtain ⟨-, -, -, -, -, -, -, -, -, hch, -⟩ : initVM entry s t := hi
    exact chainScanInv_of_idle hch
  case scan_wait =>
    rename_i hm hav hb
    exact hbg c s t hm hx hb
  case scan_count =>
    rename_i hm hc hav hb
    exact chainScanInv_congr (c := c) rfl rfl (hbg c s t hm hx hb)
  case scan_match =>
    rename_i s' o hmt hm hc hcmp hav hpl ho
    exact hmatch c s s' t o _ hm hx hcmp hmt hpl
  case scan_shift =>
    rename_i s' hmt hg hm hc hr hcmp hav hb
    exact chainScanInv_of_notScanNR (fun h1 => by cases h1.1)
  case scan_fallback =>
    rename_i s' hmt hm hc hg hr hcmp hav hb
    exact chainScanInv_of_notScanNR (fun h1 => by cases h1.1)
  case shift_done =>
    rename_i o hm hp ho
    exact hsd c s o hm hp
  case replayStart =>
    rename_i o hm ho ho' hi
    obtain ⟨-, -, -, -, -, -, -, -, -, hch, -⟩ : replayStartVM entry s t := hi
    exact chainScanInv_of_idle hch
  case restart =>
    rename_i hm hb
    obtain ⟨w', -, -, -, -, ht⟩ : restartVM entry s t := hb
    subst ht
    exact chainScanInv_of_idle rfl
  all_goals
    exact chainScanInv_of_notScanNR (fun h1 => by
      obtain ⟨h2, -⟩ := h1
      simp_all)

end

#print axioms watchShiftG_of_chainScanInv
#print axioms chainScanInv_tick

end PalPeg.CloseoutPackRun32
