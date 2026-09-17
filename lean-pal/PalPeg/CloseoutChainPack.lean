import PalPeg.CloseoutVerRep
import PalPeg.CloseoutShiftS2
import PalPeg.CloseoutMarksFree

/-!
# `ChainPack`: `ChainPosInv2` with the three supply clauses folded in

Working top-down from `pal_in_peg_final31`, the four branch hypotheses of
`chainPosInv2_tick` all have producers in `CloseoutPackRun48`, and three of
`h_bgP2_of_supply`'s four inputs have the *same shape*:

```
∀ c s, c.mode = Mode.scan → ChainPosInv2 w c s → <local fact about s>
```

with the facts being `RRep` (the right head), `VerRep` (the verifier head) and
`LagCan` (the lag counter).  Folding them into the invariant turns three
hypotheses into three **fields**, which the tick can then be asked to preserve
once instead of three times.

`ChainPack` is that bundle.  `chainPack_supply` reads the three clauses back off
it in exactly the shape `h_bgP2_of_supply` wants.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutChainPack

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilFrontMono
open PalPeg.CloseoutPackRun26 PalPeg.CloseoutPackRun41 PalPeg.CloseoutPackRun47
open PalPeg.CloseoutPackRun44 PalPeg.CloseoutPackRun48 PalPeg.CloseoutVerRep

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`ChainPosInv2` plus the three head/counter supply clauses.** -/
structure ChainPack (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  inv : ChainPosInv2 w c s
  repR : c.mode = Mode.scan →
    GalilScaffoldInputTrace.Represents s.right.head w ∧ s.right.head.focus ≠ none
  repV : c.mode = Mode.scan → VerRep w s.chain
  repVmid : ∀ (y : ChainVM) (wch : GalilScaffoldChainWatch.State),
    ChainStep s.chain y → y = .watch wch →
      GalilScaffoldInputTrace.Represents wch.machine.verifier.head w ∧
        wch.machine.verifier.head.focus ≠ none
  lagCan : c.mode = Mode.scan → LagCan s.chain
  shiftCanR : c.mode = Mode.shift → GalilScaffoldChainVerifier.canRight s.right
  shiftRad : c.mode = Mode.shift → ∀ rad : ℕ,
    ScanInvariant w (position s.center) rad s.left s.right → value s.radius ≤ (rad : ℤ)
  saneR : Sane s.right
  backLag : ∀ (v : GalilScaffoldChainPeriod.Tape) (h lag margin : Counter) (ver : PlaceHead),
    s.chain = .back v h lag margin ver → Canonical lag ∧ 0 ≤ value lag
  replayPay : c.replaying = true → s.chain ≠ ChainVM.idle → PosPayload2 w s
  radNext : ∀ rad : ℕ,
    ScanInvariant w (position s.center) rad (GalilScaffoldInputHead.left s.left) (right s.right) →
      value s.radius + 1 ≤ (rad : ℤ)
  startLedger : s.chain = ChainVM.idle → CentreLedger s
  centreSane : Sane s.center
  centreCanR : GalilScaffoldChainVerifier.canRight s.center
  centreLedgerPos : c.mode = Mode.scan →
    (position s.center : ℤ) + value s.radius = position s.right
  scanRad : c.mode = Mode.scan → ∀ rad : ℕ,
    ScanInvariant w (position s.center) rad s.left s.right → value s.radius ≤ (rad : ℤ)
  scanCentre : c.mode = Mode.scan → CentreLedger s
  scanBound : c.mode = Mode.scan →
    ∃ m : ℕ, 1 ≤ m ∧ m < w.length ∧ position s.right ≤ 2 * m - 1
  /-- The FPP window has not crossed the input origin — the `hwin` input of
  `CloseoutPackRun17.marks_steps`. -/
  winOrigin : c.mode = Mode.copy → PalPeg.CloseoutPackRun17.WindowInOrigin s
  /-- The length counter is non-negative at a `scan` state — the `hfl` input of
  the same, proved from `EntryCounters` by
  `CloseoutLenNonneg.lenNonneg_of_entryCounters`. -/
  lenNonneg : c.mode = Mode.scan → 0 ≤ value s.length

/-- The three clauses, in the shape `h_bgP2_of_supply` asks for. -/
theorem chainPack_supply {w : List (Fin 2)}
    (hp : ∀ (c : Control) (s : GalilVM), ChainPosInv2 w c s → ChainPack w c s) :
    (∀ (c : Control) (s : GalilVM), c.mode = Mode.scan → ChainPosInv2 w c s →
      GalilScaffoldInputTrace.Represents s.right.head w ∧ s.right.head.focus ≠ none) ∧
    (∀ (c : Control) (s : GalilVM), c.mode = Mode.scan → ChainPosInv2 w c s →
      ∀ wch : GalilScaffoldChainWatch.State, s.chain = .watch wch →
        GalilScaffoldInputTrace.Represents wch.machine.verifier.head w ∧
          wch.machine.verifier.head.focus ≠ none) ∧
    (∀ (c : Control) (s : GalilVM), c.mode = Mode.scan → ChainPosInv2 w c s →
      LagCan s.chain) :=
  ⟨fun c s hm hx => (hp c s hx).repR hm,
   fun c s hm hx => (hp c s hx).repV hm,
   fun c s hm hx => (hp c s hx).lagCan hm⟩

/-- **`H_bgP2` from `ChainPack` plus the chain-start clause.**  Three of
`h_bgP2_of_supply`'s four inputs are now fields. -/
theorem h_bgP2_of_chainPack {w : List (Fin 2)}
    (hp : ∀ (c : Control) (s : GalilVM), ChainPosInv2 w c s → ChainPack w c s)
    (hstart : BgStartP2 centre place entry q first w) :
    H_bgP2 centre place entry q first w :=
  let S := chainPack_supply (w := w) hp
  h_bgP2_of_supply centre place entry q first S.1 S.2.1 S.2.2 hstart

/-- **`H_shiftDoneRad2` from `ChainPack`.**  Both of
`h_shiftDoneRad2_of_supply`'s inputs are now fields. -/
theorem h_shiftDoneRad2_of_chainPack {w : List (Fin 2)}
    (hp : ∀ (c : Control) (s : GalilVM), ChainPosInv2 w c s → ChainPack w c s) :
    H_shiftDoneRad2 centre place entry q first w :=
  h_shiftDoneRad2_of_supply centre place entry q first
    (fun c s hm _ hx => (hp c s hx).shiftCanR hm)
    (fun c s hm _ hx => (hp c s hx).shiftRad hm)

/-- **`MatchRes2` from `ChainPack` plus the position budget.**  Of its twelve
fields, eight are `ChainPack` fields or immediate consequences: `repV` is
`VerRep`, `repVmid` is `verRep_of_chainPos` (one `right` on the verifier),
`canR`/`radLe` are `PosPayload2`, and `repNext`/`canRNext` come from the bound
via `right_word`/`right_present`/`canRight_next_of_bound`. -/
theorem matchRes2_of_chainPack {w : List (Fin 2)} {c : Control} {s : GalilVM} {m : ℕ}
    (hp : ChainPack w c s) (hm : c.mode = Mode.scan)
    (hlv : 0 < s.right.head.left.length)
    (hm1 : 1 ≤ m) (hmlt : m < w.length)
    (hpos : position s.right ≤ 2 * m - 1) :
    MatchRes2 w c s := by
  obtain ⟨hrr, hfr⟩ := hp.repR hm
  have hcan : canRight s.right :=
    PalPeg.CloseoutCanRightBound.canRight_of_position_bound hrr hfr hm1 (by omega) hpos
  exact
    { repR := ⟨hrr, hfr⟩
      repV := hp.repV hm
      repVmid := hp.repVmid
      lagCan := hp.lagCan hm
      backLag := hp.backLag
      replayPay := hp.replayPay
      saneR := hp.saneR
      canR := hcan
      repNext := ⟨right_word _ w hrr hcan, PalPeg.CloseoutScanMargin4.right_present hrr hfr hcan⟩
      canRNext := PalPeg.CloseoutCanRightBound.canRight_next_of_bound
        (right_word _ w hrr hcan)
        (PalPeg.CloseoutScanMargin4.right_present hrr hfr hcan) hcan hlv hm1 hmlt hpos
      radNext := hp.radNext
      startLedger := hp.startLedger }

#print axioms matchRes2_of_chainPack
/-! ## All four branch hypotheses from `ChainPack`

`H_matchRes2` and `H_shiftRes2` ask for the **same** `MatchRes2` pack — one at a
matching comparison's source, one at a mismatching guarded one — so
`matchRes2_of_chainPack` discharges both.  With `h_bgP2_of_chainPack` and
`h_shiftDoneRad2_of_chainPack` that is all four of `chainPosInv2_tick`'s
hypotheses, from one bundle plus the run's position budget.
-/

/-- The position-budget side condition the two `MatchRes2` users share. -/
def ScanBudget (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (w : List (Fin 2)) : Prop :=
  ∀ (c : Control) (s : GalilVM), c.mode = Mode.scan → ChainPosInv2 w c s →
    ∃ m : ℕ, 1 ≤ m ∧ m < w.length ∧ position s.right ≤ 2 * m - 1

/-- **`ScanBudget` is a `ChainPack` field.**  The bound lives on the state, and
`ChainPack` is established along the run (where the bound comes from), so it
travels with the bundle rather than as a separate hypothesis. -/
theorem scanBudget_of_chainPack {w : List (Fin 2)}
    (hp : ∀ (c : Control) (s : GalilVM), ChainPosInv2 w c s → ChainPack w c s) :
    ScanBudget centre place entry q first w :=
  fun c s hm hx => (hp c s hx).scanBound hm

/-- The left-length half of the old `ScanBudget` is a consequence of
`ChainPack.repR`: `present_iff_left` turns `focus ≠ none` into
`0 < left.length`. -/
theorem leftLen_of_chainPack {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hp : ChainPack w c s) (hm : c.mode = Mode.scan) : 0 < s.right.head.left.length := by
  obtain ⟨hrr, hfr⟩ := hp.repR hm
  exact (PalPeg.CloseoutLPack3.present_iff_left hrr).1 hfr

/-- `MatchRes2` needs the payload only through `canR`, which `ChainPack.repR`
and the budget already give; so the idle case is not special. -/
theorem matchRes2_of_budget {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hp : ChainPack w c s) (hm : c.mode = Mode.scan)
    (hb : ScanBudget centre place entry q first w) :
    MatchRes2 w c s := by
  obtain ⟨m, hm1, hmlt, hpos⟩ := hb c s hm hp.inv
  exact matchRes2_of_chainPack hp hm (leftLen_of_chainPack hp hm) hm1 hmlt hpos

/-- **`H_matchRes2` from `ChainPack`.** -/
theorem h_matchRes2_of_chainPack {w : List (Fin 2)}
    (hp : ∀ (c : Control) (s : GalilVM), ChainPosInv2 w c s → ChainPack w c s)
    (hb : ScanBudget centre place entry q first w)
    :
    H_matchRes2 centre place entry q first w := fun c s s' t o b hm hx _ _ _ _ _ =>
  matchRes2_of_budget centre place entry q first (hp c s hx) hm hb

/-- **`H_shiftRes2` from the same bundle** — it asks for the identical
`MatchRes2` pack, at a mismatching guarded comparison instead. -/
theorem h_shiftRes2_of_chainPack {w : List (Fin 2)}
    (hp : ∀ (c : Control) (s : GalilVM), ChainPosInv2 w c s → ChainPack w c s)
    (hb : ScanBudget centre place entry q first w)
    :
    H_shiftRes2 centre place entry q first w := fun c s s' t hm hx _ _ _ _ =>
  matchRes2_of_budget centre place entry q first (hp c s hx) hm hb

#print axioms h_matchRes2_of_chainPack


#print axioms h_shiftDoneRad2_of_chainPack

/-! ## `ChainPack` from the run pack

`packRunR_MW` carries `IPackMW = LPackM ∧ LPackM2` and `AuxPack` at every state
of the run, and `LPackM2` already holds the scan and shift geometry:

* `LPackM.scanGeom` / `LPackM2.scanGeomR` give `ScanInvariant` at a `scan`
  state (non-replaying and replaying respectively), whose `rightRep` /
  `rightPresent` are `repR`;
* `LPackM2.shiftGeom` gives `ShiftGeom`, whose `RRep` and position relation are
  `shiftCanR` / `shiftRad`;
* `AuxPack.front.sane` is `saneR`.

So the residue of `ChainPack` is the chain-side data (`repV`, `repVmid`,
`lagCan`, `backLag`, `replayPay`, `startLedger`, the centre pair and the
checkpoint bound), which `ChainSide` names.
-/

/-- **(NAMED) the chain-side residue of `ChainPack`.** -/
structure ChainSide (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  repV : c.mode = Mode.scan → VerRep w s.chain
  repVmid : ∀ (y : ChainVM) (wch : GalilScaffoldChainWatch.State),
    ChainStep s.chain y → y = .watch wch →
      GalilScaffoldInputTrace.Represents wch.machine.verifier.head w ∧
        wch.machine.verifier.head.focus ≠ none
  lagCan : c.mode = Mode.scan → LagCan s.chain
  backLag : ∀ (v : GalilScaffoldChainPeriod.Tape) (h lag margin : Counter) (ver : PlaceHead),
    s.chain = .back v h lag margin ver → Canonical lag ∧ 0 ≤ value lag
  replayPay : c.replaying = true → s.chain ≠ ChainVM.idle → PosPayload2 w s
  radNext : ∀ rad : ℕ,
    ScanInvariant w (position s.center) rad (GalilScaffoldInputHead.left s.left) (right s.right) →
      value s.radius + 1 ≤ (rad : ℤ)
  startLedger : s.chain = ChainVM.idle → CentreLedger s
  centreCanR : GalilScaffoldChainVerifier.canRight s.center
  centreLedgerPos : c.mode = Mode.scan →
    (position s.center : ℤ) + value s.radius = position s.right
  scanCentre : c.mode = Mode.scan → CentreLedger s
  scanBound : c.mode = Mode.scan →
    ∃ m : ℕ, 1 ≤ m ∧ m < w.length ∧ position s.right ≤ 2 * m - 1
  shiftCanR : c.mode = Mode.shift → GalilScaffoldChainVerifier.canRight s.right
  shiftRad : c.mode = Mode.shift → ∀ rad : ℕ,
    ScanInvariant w (position s.center) rad s.left s.right → value s.radius ≤ (rad : ℤ)
  scanRad : c.mode = Mode.scan → ∀ rad : ℕ,
    ScanInvariant w (position s.center) rad s.left s.right → value s.radius ≤ (rad : ℤ)
  /-- The FPP window has not crossed the input origin (needed by the marks
  route, `CloseoutPackRun17.marks_steps`). -/
  winOrigin : c.mode = Mode.copy → PalPeg.CloseoutPackRun17.WindowInOrigin s
  /-- The length counter is non-negative at a `scan` state (the other marks
  input; `CloseoutLenNonneg.lenNonneg_of_entryCounters` proves it from
  `EntryCounters`). -/
  lenNonneg : c.mode = Mode.scan → 0 ≤ value s.length

/-- **`ChainPack` from `LPackM2`, `SanePack` and the chain-side residue.**  `repR` is the
only field the geometry pack supplies; everything else is chain-side. -/
theorem chainPack_of_lpackM2 {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hinv : ChainPosInv2 w c s) (hP : PalPeg.CloseoutPackRun23.LPackM2 w c s)
    (hSP : PalPeg.GalilTrailSane.SanePack c s)
    (hS : ChainSide w c s) : ChainPack w c s where
  inv := hinv
  repR := fun hm => by
    cases hr : c.replaying with
    | false =>
      obtain ⟨rad, hi⟩ := hP.packM.scanGeom hm hr
      exact ⟨hi.rightRep, hi.rightPresent⟩
    | true =>
      obtain ⟨rad, hi⟩ := hP.scanGeomR hm hr
      exact ⟨hi.rightRep, hi.rightPresent⟩
  repV := hS.repV
  repVmid := hS.repVmid
  lagCan := hS.lagCan
  shiftCanR := hS.shiftCanR
  shiftRad := hS.shiftRad
  saneR := hSP.saneR
  backLag := hS.backLag
  replayPay := hS.replayPay
  radNext := hS.radNext
  startLedger := hS.startLedger
  centreSane := hSP.saneC
  centreCanR := hS.centreCanR
  centreLedgerPos := hS.centreLedgerPos
  scanRad := hS.scanRad
  scanCentre := hS.scanCentre
  scanBound := hS.scanBound
  winOrigin := hS.winOrigin
  lenNonneg := hS.lenNonneg

/-! ## The marks route from `ChainPack`

`CloseoutMarksFree.MarksRun` is `WindowInOrigin` at the run's `copy` states plus
`EntryCounters` at its `scan` states, and the second half only feeds `hfl`
(`0 ≤ value length`).  Both are now `ChainPack` fields (`winOrigin`,
`lenNonneg`), so a run all of whose states carry `ChainPack` supplies the marks
route with **no `H_marksEntry'`**.
-/

/-- `hfl` and `hwin` — the two side inputs of
`CloseoutPackRun17.marks_steps` — read off `ChainPack` along a run. -/
theorem marksInputs_of_chainPack {w : List (Fin 2)} {x : State GalilVM}
    (hp : ∀ (z : State GalilVM), ChainPack w z.ctl z.vm) :
    (∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 m x z →
      z.ctl.mode = Mode.scan → 0 ≤ value z.vm.length) ∧
    (∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 m x z →
      z.ctl.mode = Mode.copy → PalPeg.CloseoutPackRun17.WindowInOrigin z.vm) :=
  ⟨fun _ z _ hm => (hp z).lenNonneg hm, fun _ z _ hm => (hp z).winOrigin hm⟩

#print axioms marksInputs_of_chainPack

#print axioms chainPack_of_lpackM2

#print axioms chainPack_supply
/-- **`BgStartP2` from `ChainPack`.**  `background` leaves `right`, `center` and
`radius` alone (`backgroundS_fields`), and a birth installs
`chainStart answer c walker s.center s.radius`, i.e. a `.copy` chain whose
verifier is `s.center` and whose lag is `s.radius`.  So `ChainPos` at the target
is `canRight s.center ∧ Sane s.center ∧ position s.center + radius =
position s.right` — the three `ChainPack` fields added above. -/
theorem bgStartP2_of_chainPack {w : List (Fin 2)}
    (hp : ∀ (c : Control) (s : GalilVM), ChainPosInv2 w c s → ChainPack w c s)
    (hb : ScanBudget centre place entry q first w) :
    BgStartP2 centre place entry q first w :=
  PalPeg.CloseoutPackRun47.bgStartP2_of_centre centre place entry q first
    (fun c s hm hx => by
      obtain ⟨m, hm1, hmlt, hpos⟩ := hb c s hm hx
      obtain ⟨hrr, hfr⟩ := (hp c s hx).repR hm
      exact PalPeg.CloseoutCanRightBound.canRight_of_position_bound hrr hfr hm1 (by omega) hpos)
    (fun c s hm hx => (hp c s hx).scanRad hm)
    (fun c s hm hx => (hp c s hx).scanCentre hm)

#print axioms bgStartP2_of_chainPack

#print axioms h_bgP2_of_chainPack

end

end PalPeg.CloseoutChainPack
