import PalPeg.CloseoutPackRun46

/-!
# `CloseoutPackRun50`: the two `Extra7` residues are **refuted**

`CloseoutPackRun46` reduced `pal_in_peg_final24`'s `hee`/`het` to two facts
(`extraEntry7_of_end` :284 and `extraTick7_of_scanAvail` :296).  Both say the
same thing: *while the machine is still scanning, the right head has not
consumed the whole input*.  This file shows that this is **false**, by
exhibiting an `InvLPC` state whose right head sits on the final gap cell.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun50

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilOracleGlueB PalPeg.GalilGlueBLeaves
open PalPeg.GalilChainCoupling
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2
open PalPeg.CloseoutPackRun46
open GalilScaffoldInputHead GalilScaffoldCounter GalilScaffoldChainVerifier

/-! ## 1. The witness state -/

/-- The one-letter word; `2 * w0.length = 2` is the last index of `encoded w0`. -/
def w0 : List (Fin 2) := [0]

/-- The final gap cell of `encoded w0`: everything consumed, nothing to the right. -/
def endHead : PlaceHead := ⟨layout [(0 : Fin 2)] [] [], true⟩

theorem endHead_rep : GalilScaffoldInputTrace.Represents endHead.head w0 :=
  ⟨[0], [], [], rfl, rfl⟩

theorem endHead_focus : endHead.head.focus ≠ none := by
  intro h; exact Option.noConfusion h

theorem endHead_pos : position endHead = 2 := by
  simp [position, endHead, layout]

theorem endHead_not_canRight : ¬ canRight endHead := by
  rintro (h | h | h) <;> simp [endHead, layout] at h

/-- The witness VM: the boot VM with all three heads on the final gap cell and
the span counter reading `1`. -/
def endVM : GalilVM :=
  { GalilBootVM.initVM0 w0 with
      left := endHead, center := endHead, right := endHead,
      length := ofNat 1 }

/-- The witness controller: a fresh, non-replaying scan with output off. -/
def endCtl : Control := ⟨Mode.scan, 2048, false, false, false, false⟩

/-! ## 2. `InvLPC w0 endCtl endVM` -/

theorem endScan : ScanInvariant w0 (position endVM.center) 0 endVM.left endVM.right :=
  scan_initial w0 endHead endHead_rep endHead_focus

theorem endLeftmost : Leftmost w0 (position endVM.right) (position endVM.center) := by
  refine ⟨live_of_scanInvariant endScan, fun c hc => ?_⟩
  have h1 := hc.1
  have h2 := hc.2.1
  have h3 : position endVM.right = 2 := endHead_pos
  have h4 : position endVM.center = 2 := endHead_pos
  omega

theorem endMInv : MInv w0 endCtl endVM := minv_of_leftmost endLeftmost rfl

theorem endSearchReady : PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get endVM) :=
  ⟨⟨fun h => Mode.noConfusion h, fun h => Mode.noConfusion h,
    fun h => Mode.noConfusion h, fun h => Mode.noConfusion h⟩,
   fun h => Mode.noConfusion h⟩

theorem endShiftIdle : ShiftIdle endVM := by rw [shiftIdle_iff]; rfl

theorem endInvScan : PalPeg.GalilReplaySegment.InvScan 2048 w0 endCtl endVM 0 :=
  PalPeg.GalilReplaySegment.inv_after_replay 2048 w0 endCtl endVM 0 rfl rfl rfl rfl
    endScan endMInv endSearchReady rfl endShiftIdle

theorem endInvS : InvS w0 endCtl endVM := Or.inr ⟨0, endInvScan⟩

theorem endOutputRel : OutputRel w0 endCtl endVM := fun h => Bool.noConfusion h

theorem endInvL : InvL w0 endCtl endVM := ⟨endInvS, endOutputRel⟩

theorem endEntryCounters : EntryCounters w0 endVM := by
  refine ⟨0, endScan, ⟨Or.inl rfl, ?_⟩, ?_, Or.inr rfl⟩
  · simp [endVM, GalilBootVM.initVM0, value, reset]
  · simp [SpanRep, endVM, GalilBootVM.initVM0, value, reset, ofNat]

theorem endInvLP : InvLP w0 endCtl endVM := ⟨endInvL, endEntryCounters⟩

theorem endCopyPack : CopyPack endCtl endVM := by
  intro _; rw [copyIdle_iff]; exact Or.inl rfl

theorem endInvLP2 : InvLP2 w0 endCtl endVM := ⟨endInvLP, endCopyPack⟩

theorem endCentreRep : CentreRep w0 endVM := ⟨endHead_rep, endHead_focus⟩

theorem endInvLPC : InvLPC w0 endCtl endVM := ⟨endInvLP2, endCentreRep⟩

/-! ## 3. The refutations -/

/-- **`extraEntry7_of_end`'s residue is FALSE.** -/
theorem hend_false :
    ¬ (∀ (c : Control) (r : GalilVM), InvLPC w0 c r → position r.right ≠ 2 * w0.length) := by
  intro h
  exact h endCtl endVM endInvLPC (by rw [endHead_pos]; rfl)

/-- **`H_extraEntry7` itself is FALSE.** -/
theorem h_extraEntry7_false (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ) :
    ¬ H_extraEntry7 centre place entry w0 := by
  intro h
  exact endHead_not_canRight ((h endCtl endVM endInvLPC).scanAvail rfl rfl)

#print axioms hend_false
#print axioms h_extraEntry7_false

end PalPeg.CloseoutPackRun50
