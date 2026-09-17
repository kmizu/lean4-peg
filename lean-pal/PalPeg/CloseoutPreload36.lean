import PalPeg.CloseoutPreload35

/-!
# The induction over all later `.run` entries — `postRunC_galil_of_boot`

`CloseoutPreload35.postRunF_step` takes the `PostRunF` datum at one `.run`
entry `p0` (window `mw`) to the next `.run` entry `p8` (window `2mw`) along a
`galilFrameS` run.  This file iterates it.

* §1 `EntryDatum` — the datum at a `.run` entry: mode `.run`, `span = ofNat mw`,
  `lower = ofNat k`, the calibration `8 * max k 1 ≤ mw`, `Canonical` debt, and
  the scan leg `pre` from the phase-in state `p`.  **No DP clause**: the step
  does not read `DpSafeStage` at its input entry, it recomputes it from the
  round trip, so the boot datum needs none.
* §2 `StageLegs` — one stage exactly as `postRunF_step` reads it off the run:
  `.run` leg / exit / `.wait` leg / exit / `.double` leg / dispatch /
  preparation leg / entry tick, with the mode and idle-chain annotations, the
  supply premises (`DepthAt`, `D ≤ prepLen k`, the input-length clause) and
  `bs.length = mw`.  `StageChain` — a sequence of stages, window doubling.
* §3 **`postRunC_galil_of_boot`** — from the datum at the first `.run` entry
  with `32 ≤ mw0`, every later `.run` entry of the chain carries the datum,
  `32 ≤` its window, and `DpSafeStage` over the remaining stream.
  `postRunC_galil_of_initial` reads `ClockInv 2048` off `Control.initial`.

## What this is and is not

It is the induction `CloseoutPreload35` §7 left open, modulo the boot datum.
It is **not** `PostRunPh` / `PostRunC`: those (`CloseoutPreload30` /
`CloseoutPreload24`) quantify over *every* `SearchVM` in mode `.run` with
`DpSafeStage` and over *every* `searchStep` successor at *every* centre place,
and ask for `RunEntriesS`; a run induction reaches only the machine's own states
along its own centres, so it cannot produce them, and `postRunC_of_postRunPh`
is not applicable.  `RunEntriesS` along the chain is not assembled here either
(§4).

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload36

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController
open PalPeg.GalilScaffoldSearchFinish (Mode)
open PalPeg.GalilScaffoldCounter (Canonical value ofNat positive)
open PalPeg.CloseoutReadyStage (DpSafeStage PacedL)
open PalPeg.CloseoutDebtAudit (dpEvents)
open PalPeg.CloseoutPreload6 (prepLen)
open PalPeg.CloseoutPreload8 (DepthAt)
open PalPeg.CloseoutPreload21 (ScanTrace)
open PalPeg.CloseoutPreload22 (ClockInv clockInv_initial)
open PalPeg.CloseoutPreload23 (ScanSupplyInv)
open PalPeg.CloseoutPreload33 (RestartOnBroken IdleLeg scanTrace_single_false_of_clock)
open PalPeg.CloseoutPreload34 (exitNotFire_of_wait)
open PalPeg.CloseoutPreload35 (postRunF_step)

variable (P : Shared) (q : ℕ) (first : Fin 9)

/-! ## 1. The datum at a `.run` entry -/

/-- **The `PostRunF` datum at a `.run` entry `p0`**, with the scan leg `pre`
from the phase-in state `p`.  `I p` and `ClockInv 2048 p.ctl` are carried
separately (they concern `p` only). -/
def EntryDatum (k mw : ℕ) (pre : List Bool) (p p0 : State GalilVM) : Prop :=
  p0.vm.search.mode = Mode.run ∧ p0.vm.search.span = ofNat mw ∧ p0.vm.lower = ofNat k ∧
    8 * max k 1 ≤ mw ∧ Canonical p0.vm.search.debt ∧
    ∃ ts : List Bool, ScanTrace (galilFrameS P q first) 2048 ts pre p p0

/-! ## 2. One stage, and a chain of stages -/

/-- **One stage of the machine, from a `.run` entry to the next**, exactly the
leg data of `CloseoutPreload35.postRunF_step`.  The event list is the one the
`ScanTrace`s record (`a2` at the `.wait` exit; it is `false` by
`exitNotFire_of_wait`, derived in §3, not assumed).  `as` is the stream after
the entry tick; the input-length clause `hlen` is stated against it. -/
inductive StageLegs (k mw : ℕ) : List Bool → List Bool → State GalilVM → State GalilVM → Prop
  | mk {D : ℕ} {rs ws bs ps as : List Bool} {t1 t2 t3 t4 a1 a2 a3 a4 : Bool}
      {p0 p1 p2 p3 p4 p5 p6 p7 p8 : State GalilVM}
      (hrunL : IdleLeg P q first (fun s => s.search.mode = Mode.run) rs p0 p1)
      (ht0 : p1.vm.search.mode = Mode.run) (hidle1 : p1.vm.chain = ChainVM.idle)
      (hex1 : ScanTrace (galilFrameS P q first) 2048 [t1] [a1] p1 p2)
      (hw0 : p2.vm.search.mode = Mode.wait)
      (hwaitL : IdleLeg P q first (fun s => s.search.mode = Mode.wait) ws p2 p3)
      (hw1 : p3.vm.search.mode = Mode.wait) (hidle3 : p3.vm.chain = ChainVM.idle)
      (hex2 : ScanTrace (galilFrameS P q first) 2048 [t2] [a2] p3 p4)
      (hne : p4.vm.search.mode ≠ Mode.wait)
      (hdblL : IdleLeg P q first
        (fun s => s.search.mode = Mode.double ∧ positive s.search.work = true) bs p4 p5)
      (hidle5 : p5.vm.chain = ChainVM.idle)
      (hex3 : ScanTrace (galilFrameS P q first) 2048 [t3] [a3] p5 p6)
      (hdep : DepthAt (searchLens.get p6.vm) D) (hD : D ≤ prepLen k)
      (hprepL : IdleLeg P q first (fun s => s.search.mode ≠ Mode.run) ps p6 p7)
      (hne7 : p7.vm.search.mode ≠ Mode.run) (hidle7 : p7.vm.chain = ChainVM.idle)
      (hex4 : ScanTrace (galilFrameS P q first) 2048 [t4] [a4] p7 p8)
      (hrun8 : p8.vm.search.mode = Mode.run)
      (hblen : bs.length = mw)
      (hlen : D + dpEvents (2 * mw + 1) ≤ ps.length + (as.length + 1)) :
      StageLegs k mw ((rs ++ a1 :: (ws ++ [a2])) ++ (bs ++ a3 :: (ps ++ [a4]))) as p0 p8

/-- **A chain of stages** from a `.run` entry with window `mw` to one with
window `mw'`, consuming the events `evs`, with `tail` the stream left after
the last entry.  The window doubles at every stage. -/
inductive StageChain (k : ℕ) :
    ℕ → ℕ → List Bool → List Bool → State GalilVM → State GalilVM → Prop
  | nil (mw : ℕ) (tail : List Bool) (p : State GalilVM) : StageChain k mw mw [] tail p p
  | cons {mw mw' : ℕ} {ev evs tail : List Bool} {p0 p8 pn : State GalilVM}
      (hst : StageLegs P q first k mw ev (evs ++ tail) p0 p8)
      (hr : StageChain k (2 * mw) mw' evs tail p8 pn) :
      StageChain k mw mw' (ev ++ evs) tail p0 pn

/-! ## 3. The induction -/

/-- **One stage, on the datum.**  `postRunF_step` with `a2 = false` derived. -/
theorem entryDatum_step (hres : RestartOnBroken P) {I : State GalilVM → Prop}
    {k mw : ℕ} {pre ev as : List Bool} {p p0 p8 : State GalilVM}
    (hsup : ScanSupplyInv (galilFrameS P q first) 2048 I)
    (hp : I p) (hclk : ClockInv 2048 p.ctl)
    (hd : EntryDatum P q first k mw pre p p0) (hmw : 32 ≤ mw)
    (hst : StageLegs P q first k mw ev as p0 p8)
    (hpaced : PacedL 2048 0 (pre ++ ev ++ as)) :
    EntryDatum P q first k (2 * mw) (pre ++ ev) p p8 ∧
      DpSafeStage (searchLens.get p8.vm) as := by
  obtain ⟨hm, hsp, hlow, hcal, hcan, ts0, hpre⟩ := hd
  cases hst with
  | @mk D rs ws bs ps as t1 t2 t3 t4 a1 a2 a3 a4 p0 p1 p2 p3 p4 p5 p6 p7 p8
      hrunL ht0 hidle1 hex1 hw0 hwaitL hw1 hidle3 hex2 hne hdblL hidle5 hex3 hdep hD hprepL
      hne7 hidle7 hex4 hrun8 hblen hlen =>
    have hnf := exitNotFire_of_wait P q first hres hcan hrunL ht0 hidle1 hex1 hw0 hwaitL hw1
      hidle3 hex2 hne
    have ha2 : a2 = false := scanTrace_single_false_of_clock hex2 hnf
    subst ha2
    have hpaced' : PacedL 2048 0
        (pre ++ (rs ++ a1 :: (ws ++ [false])) ++ (bs ++ a3 :: (ps ++ a4 :: as))) := by
      have e : pre ++ (rs ++ a1 :: (ws ++ [false])) ++ (bs ++ a3 :: (ps ++ a4 :: as))
          = pre ++ ((rs ++ a1 :: (ws ++ [false])) ++ (bs ++ a3 :: (ps ++ [a4]))) ++ as := by
        simp
      rw [e]; exact hpaced
    obtain ⟨h1, h2, h3, h4, h5, h6, ts8, h7⟩ := postRunF_step P q first hres hsup hm hsp hlow
      hcal hcan hpre hp hclk hrunL ht0 hidle1 hex1 hw0 hwaitL hw1 hidle3 hex2 hne hdblL hidle5
      hex3 hdep hD hprepL hne7 hidle7 hex4 hrun8 hblen hmw hlen hpaced'
    refine ⟨⟨h1, h2, h3, h4, h5, ts8, ?_⟩, h6⟩
    rw [← List.append_assoc]
    exact h7

#print axioms entryDatum_step

/-- **NAMED — the induction over all later `.run` entries.**  From the datum at
the first `.run` entry `p0` (window `mw`, `32 ≤ mw`) and a chain of stages to
`pn`, the datum holds at `pn` with window `mw'`, `32 ≤ mw'`, and — unless the
chain is empty — `DpSafeStage` at `pn` over the remaining stream `tail`.
Hypotheses outside the run and its annotations: `hres`, `hsup`, `I p`,
`ClockInv 2048 p.ctl`, the boot datum, `32 ≤ mw`, and the pacing of the whole
stream from `p`. -/
theorem postRunC_galil_of_boot (hres : RestartOnBroken P) {I : State GalilVM → Prop}
    {k mw mw' : ℕ} {pre evs tail : List Bool} {p p0 pn : State GalilVM}
    (hsup : ScanSupplyInv (galilFrameS P q first) 2048 I)
    (hp : I p) (hclk : ClockInv 2048 p.ctl)
    (hboot : EntryDatum P q first k mw pre p p0) (hmw : 32 ≤ mw)
    (hch : StageChain P q first k mw mw' evs tail p0 pn)
    (hpaced : PacedL 2048 0 (pre ++ evs ++ tail)) :
    EntryDatum P q first k mw' (pre ++ evs) p pn ∧ 32 ≤ mw' ∧
      ((evs = [] ∧ mw = mw' ∧ p0 = pn) ∨ DpSafeStage (searchLens.get pn.vm) tail) := by
  induction hch generalizing pre with
  | nil mw tail p0 =>
      refine ⟨by simpa using hboot, hmw, Or.inl ⟨rfl, rfl, rfl⟩⟩
  | @cons mw mw' ev evs tail p0 p8 pn hst hr ih =>
      have hpaced1 : PacedL 2048 0 (pre ++ ev ++ (evs ++ tail)) := by
        simpa [List.append_assoc] using hpaced
      obtain ⟨hd8, hsafe8⟩ := entryDatum_step P q first hres hsup hp hclk hboot hmw hst hpaced1
      have hpaced2 : PacedL 2048 0 (pre ++ ev ++ evs ++ tail) := by
        simpa [List.append_assoc] using hpaced
      obtain ⟨hdn, hmw', hrest⟩ := ih hd8 (by omega) hpaced2
      refine ⟨by rw [← List.append_assoc]; exact hdn, hmw', Or.inr ?_⟩
      rcases hrest with ⟨he, -, hpn⟩ | h
      · subst he; subst hpn; simpa using hsafe8
      · exact h

#print axioms postRunC_galil_of_boot

/-- The boot form: the phase-in state is the machine's initial control
(`ClockInv 2048` by `clockInv_initial`; `GalilBootVM.initVM0 w` is one such
`s`). -/
theorem postRunC_galil_of_initial (hres : RestartOnBroken P) {I : State GalilVM → Prop}
    {k mw mw' : ℕ} {pre evs tail : List Bool} {s : GalilVM} {p0 pn : State GalilVM}
    (hsup : ScanSupplyInv (galilFrameS P q first) 2048 I)
    (hp : I ⟨initial 2048, s⟩)
    (hboot : EntryDatum P q first k mw pre ⟨initial 2048, s⟩ p0) (hmw : 32 ≤ mw)
    (hch : StageChain P q first k mw mw' evs tail p0 pn)
    (hpaced : PacedL 2048 0 (pre ++ evs ++ tail)) :
    EntryDatum P q first k mw' (pre ++ evs) ⟨initial 2048, s⟩ pn ∧ 32 ≤ mw' ∧
      ((evs = [] ∧ mw = mw' ∧ p0 = pn) ∨ DpSafeStage (searchLens.get pn.vm) tail) :=
  postRunC_galil_of_boot P q first hres hsup hp (clockInv_initial 2048 (by omega)) hboot hmw hch
    hpaced

#print axioms postRunC_galil_of_initial

/-!
## 4. What is left

* **The boot datum** `EntryDatum k mw0 pre ⟨initial 2048, initVM0 w⟩ p0` at the
  first `.run` entry: the search enters through `grow` (Scala
  `ScaffoldSearch.start` / `stepGrow`: `work := max(lower, 1)`, eight span
  cells per unit) then `prepare`, so `mw0 = 8 * max k 1`, `lower = ofNat k`,
  the calibration is an equality, and `Canonical` debt / the scan leg `pre`
  from the initial control are the entry facts (`entry_debt_at_prep` shape).
  Not proved here.
* **`32 ≤ mw0`**, i.e. `k ≥ 4`.  Once true it is preserved (the window
  doubles), so no per-entry hypothesis remains.  For `k ≤ 3` the first one
  (`k = 2, 3`: windows `16`, `24`) or two (`k = 0, 1`: windows `8`, `16`)
  stages have `mw < 32`, and `postRunF_step` does not apply to them
  (`bal_of_paced_slack_S` needs `mw ≥ 32` to absorb the two slack units of
  `dpDemandS`); those stages need the phase of the `.double` leg or a sharper
  demand — a separate argument.
* **`RunEntriesS`** along the chain, and `PostRunPh` / `PostRunC` themselves:
  see the module docstring — not machine-run statements.  The `.found` /
  `.missed` exits (`CloseoutPreload30` §3) and the scan exit
  (`runP_exit_debt_at_exit_scan`) end a chain and are outside `StageChain`.
* **`H_stageScan` / `H_bootShift` / `H_landShift`** (`pal_in_peg_final20`):
  none is a `PostRunC` consumer.  `H_stageScan` asks `ReplayStage` (a
  `Restarted` ancestor with a `WatchSegE` leg) of every `InvScan` state;
  `H_bootShift` / `H_landShift` ask `ShiftLocal` at the boot state and its
  `init` landing.  None mentions `RunEntriesS`, `DpSafeStage` or a `.run`
  entry datum, so nothing here discharges them.

**無条件 PAL ∈ PEG は未完.**
-/

end PalPeg.CloseoutPreload36
