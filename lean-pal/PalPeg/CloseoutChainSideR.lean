import PalPeg.CloseoutBudgetFree

/-!
# `ChainSide` without the contradictory field

`CloseoutPackRefute` demonstrated one outright contradiction in `hpack`:
`ChainPack.scanBound` asks for `∃ m, 1 ≤ m ∧ m < w.length ∧ …`, which is
**unsatisfiable** when `w.length ≤ 1`, while `chainPosInv2_of_idle` makes the
premise free.  The same field sits in the named residue
`CloseoutChainPack.ChainSide`.

`ChainSideR` below is `ChainSide` with that field removed, and
`chainSide_of_chainSideR` puts it back from the run
(`CloseoutBudgetFree.scanBudget_of_front_run`), which is where it always
belonged — `ChainPack`'s own docstring says the bundle "is established along the
run (where the bound comes from)".

**What this fixes and what it does not.**  It removes the one *demonstrated*
contradiction: `∀ w c s, ChainPositionInvariantWithShiftPhase w c s → ChainSideR q first w c s` has no
one-line counterexample, whereas the `ChainSide` version had one for every word
of length ≤ 1.  It does **not** make the hypothesis true: `ChainSideR` still
asserts run facts (`centreCanR`, `marks`, `cpack`, `wpack`, the centre ledger)
under a three-field premise, so the premise still has to become the run-carried
pack — `CloseoutBudgetFree.ChainSideW`.  The difference is that those fields are
*not derivable*, rather than *contradictory*.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutChainSideR

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
open PalPeg.GalilScaffoldChainInputSupply PegSeparation
open PalPeg.GalilFrontMono PalPeg.GalilRunSkeleton
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.CloseoutPackRun41 PalPeg.CloseoutChainPack
open PalPeg.GalilCentreLive
open PalPeg.CloseoutPackRun17
open PalPeg.CloseoutPackRun16
open PalPeg.CloseoutVerRep
open PalPeg.CloseoutPackRun48
open PalPeg.CloseoutPackRun47

variable (q : ℕ) (first : Fin 9)

/-- **(NAMED) `ChainSide` minus the run's position budget.** -/
structure ChainSideR (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  repV : c.mode = Mode.scan → VerRep w s.chain
  repVmid : ∀ (y : ChainVM) (wch : GalilScaffoldChainWatch.State),
    ChainStep s.chain y → y = .watch wch →
      GalilScaffoldInputTrace.Represents wch.machine.verifier.head w ∧
        wch.machine.verifier.head.focus ≠ none
  lagCan : c.mode = Mode.scan → LagCan s.chain
  backLag : ∀ (v : GalilScaffoldChainPeriod.Tape) (h lag margin : Counter) (ver : PlaceHead),
    s.chain = .back v h lag margin ver → Canonical lag ∧ 0 ≤ value lag
  replayPay : c.replaying = true → s.chain ≠ ChainVM.idle → ScanPositionPayloadWithChainLedger w s
  radNext : ∀ rad : ℕ,
    ScanInvariant w (position s.center) rad (GalilScaffoldInputHead.left s.left) (right s.right) →
      value s.radius + 1 ≤ (rad : ℤ)
  startLedger : s.chain = ChainVM.idle → CentreLedger s
  centreCanR : GalilScaffoldChainVerifier.canRight s.center
  centreLedgerPos : c.mode = Mode.scan →
    (position s.center : ℤ) + value s.radius = position s.right
  scanCentre : c.mode = Mode.scan → CentreLedger s
  shiftCanR : c.mode = Mode.shift → GalilScaffoldChainVerifier.canRight s.right
  shiftRad : c.mode = Mode.shift → ∀ rad : ℕ,
    ScanInvariant w (position s.center) rad s.left s.right → value s.radius ≤ (rad : ℤ)
  scanRad : c.mode = Mode.scan → ∀ rad : ℕ,
    ScanInvariant w (position s.center) rad s.left s.right → value s.radius ≤ (rad : ℤ)
  walkerPin : c.mode = Mode.copy → PalPeg.CloseoutWinOrigin.WalkerPin s
  walkerOrigin : c.mode = Mode.copy → PalPeg.CloseoutPackRun25.WalkerInOrigin s
  lenNonneg : c.mode = Mode.scan → 0 ≤ value s.length
  cpack : CPack q c s
  wpack : WPack q first c s
  marks : MarksInv' first c s

/-- **`ChainSide` from `ChainSideR` and the run's budget.** -/
theorem chainSide_of_chainSideR {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hR : ChainSideR q first w c s)
    (hbud : c.mode = Mode.scan →
      ∃ m : ℕ, 1 ≤ m ∧ m < w.length ∧ position s.right ≤ 2 * m - 1) :
    ChainSide q first w c s where
  repV := hR.repV
  repVmid := hR.repVmid
  lagCan := hR.lagCan
  backLag := hR.backLag
  replayPay := hR.replayPay
  radNext := hR.radNext
  startLedger := hR.startLedger
  centreCanR := hR.centreCanR
  centreLedgerPos := hR.centreLedgerPos
  scanCentre := hR.scanCentre
  scanBound := hbud
  shiftCanR := hR.shiftCanR
  shiftRad := hR.shiftRad
  scanRad := hR.scanRad
  walkerPin := hR.walkerPin
  walkerOrigin := hR.walkerOrigin
  lenNonneg := hR.lenNonneg
  cpack := hR.cpack
  wpack := hR.wpack
  marks := hR.marks

/-- **`ChainPack` from the slim residue plus the geometry pack and the run's
budget.**  `CloseoutChainPack.chainPack_of_lpackM2` with `scanBound` no longer
an assertion of the residue. -/
theorem chainPack_of_chainSideR {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hinv : ChainPositionInvariantWithShiftPhase w c s) (hP : PalPeg.CloseoutPackRun23.LPackM2 w c s)
    (hSP : PalPeg.GalilTrailSane.SanePack c s)
    (hR : ChainSideR q first w c s)
    (hbud : c.mode = Mode.scan →
      ∃ m : ℕ, 1 ≤ m ∧ m < w.length ∧ position s.right ≤ 2 * m - 1) :
    ChainPack q first w c s :=
  chainPack_of_lpackM2 q first hinv hP hSP (chainSide_of_chainSideR q first hR hbud)

/-- **The slim residue is what the old one gave.**  So nothing is lost. -/
theorem chainSideR_of_chainSide {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hS : ChainSide q first w c s) : ChainSideR q first w c s where
  repV := hS.repV
  repVmid := hS.repVmid
  lagCan := hS.lagCan
  backLag := hS.backLag
  replayPay := hS.replayPay
  radNext := hS.radNext
  startLedger := hS.startLedger
  centreCanR := hS.centreCanR
  centreLedgerPos := hS.centreLedgerPos
  scanCentre := hS.scanCentre
  shiftCanR := hS.shiftCanR
  shiftRad := hS.shiftRad
  scanRad := hS.scanRad
  walkerPin := hS.walkerPin
  walkerOrigin := hS.walkerOrigin
  lenNonneg := hS.lenNonneg
  cpack := hS.cpack
  wpack := hS.wpack
  marks := hS.marks

#print axioms chainSide_of_chainSideR
#print axioms chainPack_of_chainSideR
#print axioms chainSideR_of_chainSide

end PalPeg.CloseoutChainSideR
