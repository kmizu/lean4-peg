import PalPeg.CloseoutPackRun26

/-!
# `H_shiftLocalG` is free

`H_shiftLocalG` (`CloseoutPackRun26:311`) asks for `ShiftLocalG` at every
`InvLPC` state.  Every such state has an **idle chain**, and `ShiftLocalG` is
vacuous there (`shiftLocalG_of_chainIdle`, `CloseoutPackRun26:232`): its fields
all speak about a `beginShiftVM'` out of a comparison target, and that demands a
watching chain.

Why the chain is idle at an `InvLPC` state.  `InvLPC = InvLP2 ∧ CentreRep`
reaches `InvS` (`GalilOracleDischarge:78`), which is `Inv ∨ ∃ k, InvScan`:

* `InvScan` has the field `chainIdle : s.chain = ChainVM.idle`
  (`GalilReplaySegment:319`);
* `Inv` has `rest : ∃ Rad last, Restarted raw r Rad last`
  (`GalilRunInv:31`), and the first conjunct of `Restarted`
  (`GalilScaffoldTopReadyFound:38`) is `r.chain = .idle`.

So both branches give it, exactly as for `H_bootShift` / `H_landShift`.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.CloseoutShiftLocalFree

open PalPeg.CloseoutPackRun26 PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilInvPlus2 PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldController
open PalPeg.GalilScaffoldTop
open PalPeg.GalilReplaySegment

variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **Every `InvS` state has an idle chain.**  Restart branch: the first
conjunct of `Restarted`.  Scan branch: `InvScan.chainIdle`. -/
theorem chainIdle_of_invS {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    (h : InvS raw c s) : s.chain = ChainVM.idle := by
  rcases h with hInv | ⟨_, hScan⟩
  · obtain ⟨_, _, hR⟩ := hInv.rest
    exact hR.1
  · exact hScan.chainIdle

/-- **`H_shiftLocalG` is a theorem.** -/
theorem h_shiftLocalG {raw : List (Fin 2)} :
    H_shiftLocalG centre place entry q first raw :=
  fun _ hIC => shiftLocalG_of_chainIdle centre place entry q first
    (chainIdle_of_invS hIC.1.1.1.1)

#print axioms chainIdle_of_invS
#print axioms h_shiftLocalG

end PalPeg.CloseoutShiftLocalFree
