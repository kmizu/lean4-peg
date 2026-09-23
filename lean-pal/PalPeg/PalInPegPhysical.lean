import PalPeg.PhysicalResidualParts
import PalPeg.PhysicalFppAlive

/-!
# 物理機械の経路（`given_physicalObligations`）— 目標からは外した

`PAL ∈ PEG` を、118 本テープの共通機械 `PhysicalDpCleanup.machine` で示す旧経路。報告・出力の契約、
既存 7 ケース、静かなモード（home・markEnd・choose の後半・copy・rewind の1歩/2歩・未停止の fpp）は
証明済み。2026-09-24 に目標 `PalInPeg.unconditional` を SCA 経路（`PalInPegFinal`）へ付け替えたので、
ここに残っていた 6 本の `axiom` は前提に格下げした（`given_physicalObligations`）。

| 前提 | 中身 |
|---|---|
| `hscanRest` | scan の tick のうち既存 7 ケース以外（matched・fallback・restart・探索） |
| `hchooseSelect` | choose の select。head の瞬時コピー（物理規則に行が無い） |
| `hrewindReset` | rewind の reset。退役 FPP bank の reset が要る |
| `hinit` | init。head の瞬時コピー |
| `hreplayStart` | replayStart。head の瞬時コピー |
| `hfreeze` | 報告後の凍結（粘着ビット案） |

fpp の義務は証明済み（`PhysicalFppAlive.ticks_fppDone`）。
-/
set_option autoImplicit false
namespace PalPeg.PalInPeg
open PalPeg.PhysicalResidualParts
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.GalilFinalAssembly2 (centreC placeC)
open PalPeg.CloseoutCheckW (PreTraceIMW CanonTrace)
open PalPeg.LocalSysConcrete (absSC)
open PalPeg.ShadowedLocalFinal (localGood postPhase frozenAt heldAfter)

/-- The view commands of the modes the physical rule does not implement yet: stay. Changing this
when a mode is implemented keeps every obligation's statement. -/
noncomputable def physRest : PalPeg.PhysicalScanCount.RestCommands := fun _ _ _ => stayCommands

/-- **The physical route, given its open obligations.** Superseded as the target by the SCA route
(`PalInPegFinal.unconditional`); kept with its obligations as hypotheses instead of axioms.
The obligations: scan ticks outside the seven dispatcher cases, the select half of `choose`, the
rewind at the first mark, `init`, `replayStart`, and the freeze after the last report (some physical
property entered when the abstract run freezes, kept by the machine without input, and silencing the
report). -/
theorem given_physicalObligations
    (hscanRest : TicksWhere physRest ScanRest) (hchooseSelect : TicksWhere physRest ChooseSelect)
    (hrewindReset : TicksWhere physRest RewindReset) (hinit : TicksWhere physRest InitMode)
    (hreplayStart : TicksWhere physRest ReplayStartMode)
    (hfreeze : ∃ PhysFrozen : List (Fin 2) → PalPeg.PhysicalDpCleanup.Config → Prop,
      (∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
        PreTraceIMW centreC placeC 0 1 0 w st Tc → CanonTrace 0 w st Tc →
        ∀ m p, PalPeg.LocalShadowConcrete.OnRun (localGood (spare := 0)) (postPhase 0 1 0) w
            (heldAfter (Tc w.length) st) m →
          frozenAt w m → PalPeg.PhysicalDpCleanup.Enc w (absSC m) p → PhysFrozen w p) ∧
      (∀ (w : List (Fin 2)) p, PhysFrozen w p →
        PhysFrozen w ((PalPeg.PhysicalDpCleanup.machine physRest).apply blankM p none)) ∧
      (∀ (w : List (Fin 2)) p, PhysFrozen w p →
        PalPeg.PhysicalReportTest.repW p.1
          (fun j => PalPeg.Local.readWin blankM macroRadius (p.2 j)) = false)) :
    PegSeparation.RecognizedByTotalPEG PalPeg.PAL :=
  let ⟨PhysFrozen, henter, hkeep, hquiet⟩ := hfreeze
  given_parts_and_frozen physRest hscanRest
    (PalPeg.PhysicalFppAlive.ticks_fppDone physRest) hchooseSelect
    hrewindReset hinit hreplayStart PhysFrozen henter hkeep hquiet

end PalPeg.PalInPeg
