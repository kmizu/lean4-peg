import PalPeg.PhysicalResidualParts
import PalPeg.PhysicalFppAlive

/-!
# `PalInPeg.unconditional` — 目標そのもの（物理機械の経路）

`PAL ∈ PEG` を、118 本テープの共通機械 `PhysicalDpCleanup.machine` で示す。報告・出力の契約、
既存 7 ケース、静かなモード（home・markEnd・choose の後半・copy・rewind の1歩/2歩・未停止の fpp）は証明済み。
**残りは下の `axiom` で 1 本ずつ明示する。** 1 本証明して外すと `PalPeg/Axioms.lean` の guard が
壊れて更新を強制される。標準 3 公理だけになったら完成。

2026-09-23 に旧 `obligation_localRealization`（抽象 latch との一致を要求する局所実現を 1 本の
存在命題に詰めたもの）から付け替えた。旧経路は `PalInPeg.given_localRealization`。

| 義務 | 中身 | 状況 |
|---|---|---|
| `obligation_scanRest` | scan の tick のうち既存 7 ケース以外（matched・fallback・restart・探索） | 未 |
| ~~`obligation_fpp`~~ | fpp。未停止は処理済み、停止済みはトレース上に無い（`PhysicalFppAlive.ticks_fppDone`） | **済** |
| `obligation_chooseSelect` | choose の select。head の瞬時コピー（物理規則に行が無い） | 未 |
| `obligation_rewindReset` | rewind の reset。退役 FPP bank の reset が要る | 未 |
| `obligation_init` | init。head の瞬時コピー（物理規則に行が無い） | 未 |
| `obligation_replayStart` | replayStart。head の瞬時コピー（物理規則に行が無い） | 未 |
| `obligation_freeze` | 報告後の凍結（粘着ビット案、`CLAUDE.md` (B)） | 未 |
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

/-- **(OBLIGATION)** scan ticks outside the seven dispatcher cases. -/
axiom obligation_scanRest : TicksWhere physRest ScanRest
/-- **(OBLIGATION)** the select half of `choose`. -/
axiom obligation_chooseSelect : TicksWhere physRest ChooseSelect
/-- **(OBLIGATION)** the rewind at the first mark. -/
axiom obligation_rewindReset : TicksWhere physRest RewindReset
/-- **(OBLIGATION)** `init`. -/
axiom obligation_init : TicksWhere physRest InitMode
/-- **(OBLIGATION)** `replayStart`. -/
axiom obligation_replayStart : TicksWhere physRest ReplayStartMode

/-- **(OBLIGATION)** the freeze after the last report: some physical property entered when the
abstract run freezes, kept by the machine without input, and silencing the report. -/
axiom obligation_freeze :
  ∃ PhysFrozen : List (Fin 2) → PalPeg.PhysicalDpCleanup.Config → Prop,
    (∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC 0 1 0 w st Tc → CanonTrace 0 w st Tc →
      ∀ m p, PalPeg.LocalShadowConcrete.OnRun (localGood (spare := 0)) (postPhase 0 1 0) w
          (heldAfter (Tc w.length) st) m →
        frozenAt w m → PalPeg.PhysicalDpCleanup.Enc w (absSC m) p → PhysFrozen w p) ∧
    (∀ (w : List (Fin 2)) p, PhysFrozen w p →
      PhysFrozen w ((PalPeg.PhysicalDpCleanup.machine physRest).apply blankM p none)) ∧
    (∀ (w : List (Fin 2)) p, PhysFrozen w p →
      PalPeg.PhysicalReportTest.repW p.1
        (fun j => PalPeg.Local.readWin blankM macroRadius (p.2 j)) = false)

/-- **目標**: `PAL ∈ PEG`。`#print axioms unconditional` が標準 3 公理だけになったら証明完了。 -/
theorem unconditional : PegSeparation.RecognizedByTotalPEG PalPeg.PAL :=
  let ⟨PhysFrozen, henter, hkeep, hquiet⟩ := obligation_freeze
  given_parts_and_frozen physRest obligation_scanRest
    (PalPeg.PhysicalFppAlive.ticks_fppDone physRest) obligation_chooseSelect
    obligation_rewindReset obligation_init obligation_replayStart PhysFrozen henter hkeep hquiet

end PalPeg.PalInPeg
