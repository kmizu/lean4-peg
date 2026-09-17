import PalPeg.CloseoutShiftS
import PalPeg.CloseoutExtraFinal

/-!
# The trail bridge off `WatchShiftG`: `pal_in_peg_final5MG2T`

`pal_in_peg_final27`'s `hws : ∀ w y, WatchShiftG … w y` is **false**
(`CloseoutPackRun32`'s caveat: a watch born at `ChainStep.backDone` has
`distance = reset`, so `4·periodLength ≤ distance` fails at the first scan
comparison after the birth).  A theorem resting on it is vacuous, so it has to
go, not be counted.

`CloseoutPackRun34` built the guarded replacements and `CloseoutShiftS` wired
them to a run:

```
ChainPosInv → shiftLocalS_of_run → radPack_ptS → trailF_ptS → needIMG2'_le_S
```

`needIMG2'_le` is the only consumer of `IPackMG.shift` on the main path (through
`h_trailI_MG2` → `trailF_ptMG` → `radPack_ptMG`), so over the `S` chain no
`WatchShiftG` appears.  The boot's `ChainPosInv` is free: `boot w` has an idle
chain and `chainPosInv_of_idle` (`Run34:335`) closes it.

On this route `hws` is replaced by `CloseoutPackRun34`'s four **guarded** branch
hypotheses — `H_fourOther`, `H_bgP`, `H_matchP`, `H_shiftDoneP` — each restricted
to `shiftGuardVM`-guarded, unmatched targets, so none of them meets Run32's
counterexample.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutShiftFinal

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilTickArrive PalPeg.GalilLatchTracking PalPeg.GalilArriveChain
open PalPeg.GalilThrottledRun PalPeg.GalilThrottledRunGen PalPeg.GalilLedgerQ64
open PalPeg.GalilRunSkeleton PalPeg.GalilCheckpoints PalPeg.GalilTraceCost
open PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal PalPeg.GalilLexMeasure
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleMC PalPeg.GalilOracleMC2
open PalPeg.GalilGlueBLeaves PalPeg.GalilBranchInvariants2 PalPeg.GalilSegmentConstruct
open PalPeg.GalilTruncTick PalPeg.GalilFinalAssembly PalPeg.GalilFinalAssembly2
open PalPeg.GalilFinalBaseNeed PalPeg.GalilFinalAssembly3 PalPeg.GalilOracleLeaves2
open PalPeg.GalilFinalAssembly4 PalPeg.GalilInvPlus3 PalPeg.CloseoutOracleI2
open PalPeg.CloseoutPackRun36 PalPeg.CloseoutStageCheck PalPeg.CloseoutStageBoot
open PalPeg.CloseoutPackRun PalPeg.CloseoutPackRun2 PalPeg.CloseoutPackRun3
open PalPeg.CloseoutPackRun5 PalPeg.CloseoutPackRun7 PalPeg.CloseoutPackRun8
open PalPeg.CloseoutPackRun9 PalPeg.CloseoutPackRun10 PalPeg.CloseoutPackRun11
open PalPeg.CloseoutPackRun12 PalPeg.CloseoutPackRun16 PalPeg.CloseoutPackRun18
open PalPeg.CloseoutPackRun19 PalPeg.CloseoutPackRun20 PalPeg.CloseoutPackRun21
open PalPeg.CloseoutPackRun23 PalPeg.CloseoutPackRun24 PalPeg.CloseoutPackRun29
open PalPeg.CloseoutPackRun30 PalPeg.CloseoutPackRun33 PalPeg.CloseoutPackRun35
open PalPeg.CloseoutPackRun26 PalPeg.CloseoutStageSupply
open PalPeg.CloseoutLPack PalPeg.CloseoutLPack2 PalPeg.CloseoutLPack3
open PalPeg.CloseoutLPack4 PalPeg.CloseoutLPack5 PalPeg.CloseoutLPack6
open PalPeg.GalilLookRefined PalPeg.CloseoutOracleI PalPeg.CloseoutLPack5
open PalPeg.CloseoutStageOracle PalPeg.CloseoutPackRun43 PalPeg.CloseoutPackRun45
open PalPeg.CloseoutPackRun46 PalPeg.CloseoutPreload37 PalPeg.CloseoutPackRun22
open PalPeg.CloseoutShiftLocalFree
open PalPeg.CloseoutStageFinal PalPeg.CloseoutExtraOracle PalPeg.CloseoutExtraFree
open PalPeg.CloseoutExtraFinal PalPeg.CloseoutShiftS PalPeg.CloseoutPackRun34
open PalPeg.CloseoutShiftLocalFree

/-- The boot state's chain is idle. -/
theorem boot_chain_idle (w : List (Fin 2)) : (boot w).vm.chain = ChainVM.idle := rfl

theorem pal_in_peg_final5MG2T (entry q : ℕ) (first : Fin 9)
    (hboot : H_bootIMG2S centreC placeC entry q first)
    (hA : H_oracleIMG2S centreC placeC entry q first)
    (hC : H_realizeLIMG2' centreC placeC entry q first)
    (hfour : ∀ w : List (Fin 2), H_fourOther centreC placeC entry q first w)
    (hbgP : ∀ w : List (Fin 2), H_bgP centreC placeC entry q first w)
    (hmatchP : ∀ w : List (Fin 2), H_matchP centreC placeC entry q first w)
    (hsdP : ∀ w : List (Fin 2), H_shiftDoneP centreC placeC entry q first w)
    :
    RecognizedByTotalPEG PAL := by
  classical
  obtain ⟨Q', Γ', iQ, dQ, iΓ, dΓ, t, K, L, blank, initQ, outQ, n, htape, hn, hreal⟩ := hC
  have key : ∀ w : List (Fin 2), ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      0 < w.length → PreTraceIMG2 centreC placeC entry q first w st Tc := by
    intro w
    by_cases hw : 0 < w.length
    · obtain ⟨st, Tc, h⟩ := preTraceIMG2S_exists centreC placeC entry q first hboot hA w hw
      exact ⟨st, Tc, fun _ => h⟩
    · exact ⟨fun _ => boot w, fun _ => 0, fun h => absurd h hw⟩
  choose stP TcP hP using key
  let M := L.realize blank initQ (GalilEmptyWord.accept' initQ outQ) n htape hn
  have hpre : ∀ w : List (Fin 2), 0 < w.length → PreloadL' w (stP w) (TcP w) := by
    intro w hw
    have h := hP w hw
    exact ⟨h.base.pre.tc0, fun m hm => h.base.pre.mono m (m+1) (by omega) hm,
      needL'_boot w (stP w) h.base.pre.start,
      needLe_of_pointwise' w (stP w) (TcP w) (PalPeg.CloseoutShiftS.needIMG2'_le_S centreC placeC entry q first hw h
        (hfour w) (hbgP w) (hmatchP w) (hsdP w) (by rw [h.base.pre.start]; exact chainPosInv_of_idle (boot_chain_idle w)))⟩
  refine pal_in_peg_of_latch' (Nat.mul_pos hn (PalPeg.Local.cnt_pos K)) M
    (PofC centreC placeC entry) (fun _ => q) (fun _ => first) 2048
    (fun w => PofC_onLetter centreC placeC entry w)
    (fun w => PofC_leftFirst centreC placeC entry w)
    (fun w => stLG' τF w (stP w) (TcP w w.length))
    (fun w => arrLG' τF w (stP w) (TcP w w.length))
    (fun w => (w.length + 1) * τF) ?_ ?_ ?_ ?_
  · intro w hw
    have h := hP w hw
    exact abstractRun_throttledL'_2p18 w (stP w) (TcP w w.length)
      (PofC centreC placeC entry w) q first 2048
      (fun j => sharedC_trunc_vm w j centreC placeC entry (fun s => (centrePlaceC w j s).1)
        (fun s => (centrePlaceC w j s).2))
      (sharedC_suf w _ _ centreC placeC entry)
      (by rw [h.base.pre.start]; rfl) (needL'_boot w (stP w) h.base.pre.start)
      (by rw [h.base.pre.start]; exact sufVM_boot w) h.base.pre.trace.tick
  · intro w hw
    exact hreal w hw _ _ (hP w hw)
  · exact ledger_throttledL'_2p18 (PofC centreC placeC entry) (fun _ => q) (fun _ => first)
      stP TcP hpre (fun w hw => (hP w hw).base.pre.report w.length (by omega) le_rfl)
      (fun w hw => base_of_preTraceB (hP w hw).base)
      (fun w hw => (hP w hw).base.pre.cost)
  · exact GalilEmptyWord.realize_accept'_nil L blank initQ outQ n htape hn

#print axioms boot_chain_idle
#print axioms pal_in_peg_final5MG2T


/-! ## What is still missing

`pal_in_peg_final5MG2T` above takes **no** `WatchShiftG`: the whole trail bridge
(`radPack` → `trailF` → `needL'`) now runs on `ChainPosInv`.

The remaining use of `hws` on the main path is the *other* direction — filling
`IPackMG.shift` (`CloseoutPackRun30:83`) inside `packRunR_MG27P`, through
`ipackMG2_tick_pt7`'s `hsh : ShiftLocalG y` (`CloseoutPackRun46:160`).  With the
trail bridge moved off it, that field is read by nobody, so it can be weakened
to the idle case

```
shift : x.vm.chain = ChainVM.idle → ShiftLocalG centre place entry q first w x
```

which `shiftLocalG_of_chainIdle` closes for free.  That edit was attempted and
**rolled back**: `IPackMG` feeds the whole `final17 → … → final27` chain
(`CloseoutPackRun33/35/36/42/43/45/46/50/51`), and weakening the field breaks the
older links.  The non-destructive route is an `S` copy of Run30 §1 and Run36 §2
carrying the weakened field, in the style of `CloseoutStageCheck` — the next
wave.
-/

end PalPeg.CloseoutShiftFinal
