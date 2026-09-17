import PalPeg.CloseoutPreload22
import PalPeg.CloseoutPackRun3

/-!
# The input-supply invariant `CloseoutPreload22` §4 names as missing

`CloseoutPreload22` §3 reduces the availability half of `CloseoutPreload21`'s
interface obligations to `canRight s.right`, and observes that the `StepsAll`
invariant carried there (`SoundScanNR raw`, an output relation) does not mention
the right head at all.  Its closing line asks for *an input-supply invariant on
the right head, carried alongside `SoundScanNR`*.

This file supplies exactly that, in two steps.

* §1 **relativisation.**  `CloseoutPreload21`'s three leg lemmas
  (`scanTrace_all_avail`, `wait_leg_length_le_of_scan`, `prefixPhase_of_scan`)
  assume `∀ s : σ, F.available s` — availability at *every* state of the VM,
  which is plainly false for a machine whose input eventually runs out.  What
  their proofs actually use is availability at the states the leg visits *in
  scan mode*.  `ScanSupplyInv F delay I` packages that: a `Tick`-preserved state
  predicate `I` which, in `.scan` mode, implies `F.available`.  §1 re-proves the
  three lemmas from `ScanSupplyInv` + `I p` (`scanTrace_all_avail_inv`,
  `wait_leg_length_le_of_scan_inv`, `prefixPhase_of_scan_inv`).

* §2 **the concrete carrier.**  On `galilFrameS` the predicate is already
  available: `CloseoutPackRun3.BigPack2` carries `Extra.scanAvail` (scan outside
  a replay) and `BigPack.front` (the replay half, via
  `GalilTrailRad.replayCan_of_pack`), and `CloseoutPackRun3.canR_of_bigPack2`
  combines them into `canRight x.vm.right` in `.scan` mode — which
  `CloseoutPreload22.available_iff_canRight` turns into availability
  definitionally.  Preservation is `CloseoutPackRun3.bigPack2_tick`, whose two
  per-tick side conditions (`SoundScanNR w y`, `CentreLive y.ctl y.vm`) are the
  invariants the `StepsAll` run already carries.  `bigPack2_scanSupply` is the
  resulting `ScanSupplyInv`, and `scan_leg_avail_of_bigPack2` is the availability
  list of a scan leg run under it.

**`postRunP_of_machine : CloseoutPreload17.PostRunP` is *not* proved here** — §3.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload23

open PalPeg
open PalPeg.GalilScaffoldController (Control)
open PalPeg.GalilScaffoldTop (Frame State Tick)
open PalPeg.GalilScaffoldChainInputSupply (GalilVM SearchVM galilFrameS)
open PalPeg.GalilScaffoldCounter (Canonical value zero)
open PalPeg.CloseoutPreload14 (WaitTrace)
open PalPeg.CloseoutPreload18 (PrefixPhase)
open PalPeg.CloseoutPreload19 (LiveL prefixPhase_of_clock)
open PalPeg.CloseoutPreload20 (runTrace runTrace_length runTrace_count
  liveL_of_clock wait_leg_length_le_of_clock)
open PalPeg.CloseoutPreload21 (ScanTrace scanTrace_eq_runTrace)

variable {σ : Type}

/-! ## 1. Availability, relativised to a tick-preserved invariant -/

/-- **NAMED — the input-supply invariant `CloseoutPreload22` §4 asks for.**
A state predicate `I` that (a) travels along every `Tick`, and (b) in `.scan`
mode implies that the frame has an input symbol available.  This is the honest
form of `CloseoutPreload21`'s `hsupply : ∀ s, F.available s`: availability is
not a fact about all states of `σ`, only about the reachable ones, and only in
the mode where the machine reads. -/
structure ScanSupplyInv (F : Frame σ) (delay : ℕ) (I : State σ → Prop) : Prop where
  /-- The invariant travels along a tick. -/
  step : ∀ x y : State σ, Tick F delay x y → I x → I y
  /-- In scan mode the invariant supplies the input symbol. -/
  avail : ∀ x : State σ, I x → x.ctl.mode = GalilScaffoldController.Mode.scan →
    F.available x.vm

/-- **NAMED — `CloseoutPreload21.scanTrace_all_avail`, with the invariant in
place of the global supply hypothesis.**  A scan leg entered in a state
satisfying `I` never takes the `scan_wait` branch, so its availability list is
all `true`. -/
theorem scanTrace_all_avail_inv {F : Frame σ} {delay : ℕ} {I : State σ → Prop}
    (hsup : ScanSupplyInv F delay I) {ts as : List Bool} {p q : State σ}
    (h : ScanTrace F delay ts as p q) (hp : I p) : ∀ b ∈ ts, b = true := by
  induction h with
  | nil p => intro b hb; simp at hb
  | wait c s s' ts as q ht hm hav hr ih =>
      exact absurd (hsup.avail ⟨c, s⟩ hp hm) hav.2
  | count c s s' ts as q ht hm hav hc hr ih =>
      intro b hb
      rcases List.mem_cons.mp hb with hb | hb
      · exact hb
      · exact ih (hsup.step _ _ ht hp) b hb
  | fire c s s'' o rp ts as q ht hm hav hc hr ih =>
      intro b hb
      rcases List.mem_cons.mp hb with hb | hb
      · exact hb
      · exact ih (hsup.step _ _ ht hp) b hb

#print axioms scanTrace_all_avail_inv

/-- The liveness clause of `CloseoutPreload19`, from the invariant. -/
theorem liveL_of_scanTrace_inv {F : Frame σ} {delay : ℕ} {I : State σ → Prop}
    (hsup : ScanSupplyInv F delay I) {ts as : List Bool} {p q : State σ}
    (h : ScanTrace F delay ts as p q) (hp : I p) (hd : 0 < delay)
    (h1 : 1 ≤ p.ctl.clock) (h2 : p.ctl.clock ≤ delay) : LiveL delay as := by
  rw [scanTrace_eq_runTrace h]
  exact liveL_of_clock delay p.ctl.clock hd h1 h2 ts (scanTrace_all_avail_inv hsup h hp)

#print axioms liveL_of_scanTrace_inv

/-- **NAMED — gap (b) of `CloseoutPreload19` §4, from the invariant.**
`CloseoutPreload21.wait_leg_length_le_of_scan` with `∀ s, F.available s`
replaced by a supply invariant holding at the leg's entry. -/
theorem wait_leg_length_le_of_scan_inv {F : Frame σ} {I : State σ → Prop}
    (hsup : ScanSupplyInv F 2048 I) {ts as : List Bool} {p q : State σ}
    {v t : SearchVM} {debt : ℕ}
    (hr : WaitTrace as v t) (hmt : t.search.mode = PalPeg.GalilScaffoldSearchFinish.Mode.wait)
    (hz : zero t.search.debt = true) (hc : Canonical t.search.debt)
    (hdv : value v.search.debt = (debt : ℤ))
    (hsc : ScanTrace F 2048 ts as p q) (hp : I p)
    (h1 : 1 ≤ p.ctl.clock) (h2 : p.ctl.clock ≤ 2048) :
    as.length ≤ 2048 * (debt + 1) :=
  wait_leg_length_le_of_clock hr hmt hz hc hdv h1 h2
    (scanTrace_all_avail_inv hsup hsc hp) (scanTrace_eq_runTrace hsc)

#print axioms wait_leg_length_le_of_scan_inv

/-- **NAMED — gap (a) of `CloseoutPreload19` §4, from the invariant.** -/
theorem prefixPhase_of_scan_inv {F : Frame σ} {I : State σ → Prop}
    (hsup : ScanSupplyInv F 2048 I) {ts as : List Bool} {p q : State σ}
    (hsc : ScanTrace F 2048 ts as p q) (hp : I p)
    (h1 : 1 ≤ p.ctl.clock) (h2 : p.ctl.clock ≤ 2048) : PrefixPhase as := by
  have heq := scanTrace_eq_runTrace hsc
  refine prefixPhase_of_clock (clock := p.ctl.clock) h1 h2
    (scanTrace_all_avail_inv hsup hsc hp) ?_ ?_
  · rw [heq]; exact runTrace_length 2048 p.ctl.clock ts
  · rw [heq]; exact runTrace_count 2048 p.ctl.clock ts

#print axioms prefixPhase_of_scan_inv

/-! ## 2. The concrete carrier on `galilFrameS`: `BigPack2` -/

section Concrete

variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

open PalPeg.GalilRunSkeleton (PofC)
open PalPeg.CloseoutPackRun3 (BigPack2 canR_of_bigPack2 bigPack2_tick H_extraTick BigResid5)

/-- **NAMED — the pack supplies availability, pointwise.**  `canR_of_bigPack2`
gives `canRight x.vm.right` in `.scan` mode (the non-replay half from
`Extra.scanAvail`, the replay half from the frontier budget in `BigPack.front`),
and on `galilFrameS` that *is* `available` (`CloseoutPreload22`
§3). -/
theorem avail_of_bigPack2 {w : List (Fin 2)} {x : State GalilVM}
    (hx : BigPack2 centre place entry q first w x)
    (hm : x.ctl.mode = GalilScaffoldController.Mode.scan) :
    (galilFrameS (PofC centre place entry w) q first).available x.vm :=
  (PalPeg.CloseoutPreload22.available_iff_canRight (PofC centre place entry w) q first x.vm).mpr
    (canR_of_bigPack2 centre place entry q first hx.big hx.extra hm)

#print axioms avail_of_bigPack2

/-- **NAMED — the input-supply invariant on the concrete frame.**  `BigPack2` is
a `ScanSupplyInv` for `galilFrameS`, given the residual `BigResid5` /
`H_extraTick` the pack already runs on and the two per-tick side conditions of
`bigPack2_tick` — `SoundScanNR w y`, which is exactly the predicate the
`StepsAll` run carries, and `CentreLive y.ctl y.vm`.  This is the invariant
`CloseoutPreload22` §4 asks for. -/
theorem bigPack2_scanSupply {w : List (Fin 2)}
    (hr : BigResid5 centre place entry q first w)
    (het : H_extraTick centre place entry q first w)
    (hside : ∀ x y : State GalilVM,
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y →
      BigPack2 centre place entry q first w x →
      PalPeg.GalilScaffoldChainInputSupply.SoundScanNR w y ∧
        PalPeg.GalilScaffoldChainInputSupply.CentreLive y.ctl y.vm) :
    ScanSupplyInv (galilFrameS (PofC centre place entry w) q first) 2048
      (BigPack2 centre place entry q first w) where
  step := fun x y ht hx =>
    bigPack2_tick centre place entry q first hr het hx ht
      (hside x y ht hx).1 (hside x y ht hx).2
  avail := fun _x hx hm => avail_of_bigPack2 centre place entry q first hx hm

#print axioms bigPack2_scanSupply

/-- **NAMED — a scan leg of the real machine has an all-`true` availability
list.**  The concrete instance of `scanTrace_all_avail_inv`: no global
`∀ s, F.available s` is assumed anywhere, only the pack at the leg's entry. -/
theorem scan_leg_avail_of_bigPack2 {w : List (Fin 2)} {ts as : List Bool}
    {p q' : State GalilVM}
    (hr : BigResid5 centre place entry q first w)
    (het : H_extraTick centre place entry q first w)
    (hside : ∀ x y : State GalilVM,
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y →
      BigPack2 centre place entry q first w x →
      PalPeg.GalilScaffoldChainInputSupply.SoundScanNR w y ∧
        PalPeg.GalilScaffoldChainInputSupply.CentreLive y.ctl y.vm)
    (hsc : ScanTrace (galilFrameS (PofC centre place entry w) q first) 2048 ts as p q')
    (hp : BigPack2 centre place entry q first w p) : ∀ b ∈ ts, b = true :=
  scanTrace_all_avail_inv (bigPack2_scanSupply centre place entry q first hr het hside) hsc hp

#print axioms scan_leg_avail_of_bigPack2

/-- The two `CloseoutPreload19` §4 gaps on the concrete frame, with the pack in
place of the (false) global supply hypothesis. -/
theorem prefixPhase_of_machine_scan {w : List (Fin 2)} {ts as : List Bool}
    {p q' : State GalilVM}
    (hr : BigResid5 centre place entry q first w)
    (het : H_extraTick centre place entry q first w)
    (hside : ∀ x y : State GalilVM,
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y →
      BigPack2 centre place entry q first w x →
      PalPeg.GalilScaffoldChainInputSupply.SoundScanNR w y ∧
        PalPeg.GalilScaffoldChainInputSupply.CentreLive y.ctl y.vm)
    (hsc : ScanTrace (galilFrameS (PofC centre place entry w) q first) 2048 ts as p q')
    (hp : BigPack2 centre place entry q first w p)
    (h1 : 1 ≤ p.ctl.clock) (h2 : p.ctl.clock ≤ 2048) : PrefixPhase as :=
  prefixPhase_of_scan_inv (bigPack2_scanSupply centre place entry q first hr het hside)
    hsc hp h1 h2

#print axioms prefixPhase_of_machine_scan

end Concrete

/-!
## 3. What is left

Closed here: the missing input of `CloseoutPreload22` §4.  Availability is no
longer assumed globally (`∀ s, F.available s`, which is false); it is carried by
`BigPack2` along the leg and produced in `.scan` mode by `canR_of_bigPack2`
(§2), and `CloseoutPreload21`'s three leg lemmas are re-proved from that form
(§1).  With `bigPack2_scanSupply`, `CloseoutPreload21`'s `hsupply` premise can be
discharged at every application site inside a `StepsAll` run: the pack's own
side conditions are `SoundScanNR` — the run's `Q` — and `CentreLive`.

**NOT closed — `postRunP_of_machine : CloseoutPreload17.PostRunP` is not proved
here, and the obstruction is not the supply.**  With §2 the leg lemmas
`wait_leg_length_le_of_scan` / `prefixPhase_of_scan` are usable on the real
machine, so `CloseoutPreload17` §3's item (2) (the `.wait` leg's length) is now
in reach; but items (1) and (3) are not, and (1) is a statement-level obstruction
rather than a missing lemma.

**Missing (one line):** `PostRunP`'s pacing premise is a list-level
`PacedL 2048 slack as` whose `slack` the consumers instantiate at
`(bs ++ [a]).length`, while `CloseoutPreload16.runP_exit_debt_at_exit_take`
needs `slack ≤ 2047` — and `PacedL` cannot be sharpened after the fact
(`pacedL_mono` goes the wrong way), so `PostRunP` must be restated with the
machine's clock phase (`1 ≤ clock ≤ 2048`, `CloseoutPreload22.ClockInv`, which
§1's `ScanTrace` legs now carry) in place of `PacedL`, and item (3)'s exit-debt
hypothesis `hE` inherits the same normalisation.

**無条件 PAL ∈ PEG は未完.**
-/

end PalPeg.CloseoutPreload23
