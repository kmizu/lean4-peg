import PalPeg.CloseoutOracleW
import PalPeg.CloseoutChainPack
import PalPeg.CloseoutShiftS2
import PalPeg.CloseoutShiftLocalFree

/-!
# `hme` is inside `hpack`: `MarksInv'` off the `ChainPack` bundle

`given_chainPackAtAnyState_andMore_FALSE_HYP` carries both

```
hme   : ∀ w, H_marksEntry' (PofC centreC placeC entry w) q first
hpack : ∀ w c s, ChainPositionInvariantWithShiftPhase w c s → ChainPack q first w c s
```

and `hme` is used at exactly two places, both inside
`CloseoutOracleW.packRunR_MW`, and both only to produce `MarksInv'`:

| site | use |
|---|---|
| `CloseoutOracleW:170` | `marksInv'_of_run … hme` — `MarksInv'` at the run origin |
| `CloseoutOracleW:205` | `bigPack2MG7W''_tick … hme` — `MarksInv'` one tick on |

But `MarksInv' first c s` is already a **field** of `ChainPack`
(`CloseoutChainPack:281`, `marks`), which `hpack` hands out at every state
satisfying `ChainPositionInvariantWithShiftPhase`.  And `ChainPositionInvariantWithShiftPhase` is available along the whole run:

* at the origin, `InvLPC` forces an idle chain
  (`CloseoutShiftLocalFree.chainIdle_of_invS`) and
  `CloseoutPackRun41.chainPosInv2_of_idle` turns that into `ChainPositionInvariantWithShiftPhase`;
* along the run, `CloseoutShiftS2.chainPosInv2_steps` transports it, on the
  four supplies `H_BackgroundLandingChainLedger` / `H_MatchLandingChainLedger` / `H_ShiftEntryChainLedger` / `H_ShiftExitRadiusLedger`
  which `final36` **already derives from `hpack`** (`h_bgP2_of_chainPack`,
  `h_matchP2_of_target`, `h_shiftEntry2_of_target`,
  `h_shiftDoneRad2_of_chainPack`).

So `hme` is not an independent obligation: it is the same data as `hpack`, and
nothing new appears in its place.

This file carries the two copies with `hme` removed:
`bigPack2MG7W''_tick_M` takes the landing's `MarksInv'` directly, and
`packRunR_MWP` reads every `MarksInv'` it needs off `ChainPack.marks`.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutMarksPack


open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilThrottledRun PalPeg.GalilTrailProof PalPeg.GalilFinalAssembly
open PalPeg.GalilRunSkeleton PalPeg.GalilCheckpoints PalPeg.GalilTraceCost
open PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleMC PalPeg.GalilOracleMC2
open PalPeg.GalilFinalAssembly2 PalPeg.GalilFinalAssembly4
open PalPeg.CloseoutOracleI PalPeg.CloseoutOracleI2 PalPeg.GalilInvPlus3
open PalPeg.CloseoutPackRun PalPeg.CloseoutPackRun2 PalPeg.CloseoutPackRun3
open PalPeg.CloseoutPackRun5 PalPeg.CloseoutPackRun7 PalPeg.CloseoutPackRun8
open PalPeg.CloseoutPackRun9 PalPeg.CloseoutPackRun10 PalPeg.CloseoutPackRun11
open PalPeg.CloseoutPackRun12 PalPeg.CloseoutPackRun16 PalPeg.CloseoutPackRun18
open PalPeg.CloseoutPackRun19 PalPeg.CloseoutPackRun20 PalPeg.CloseoutPackRun21
open PalPeg.CloseoutPackRun23 PalPeg.CloseoutPackRun24 PalPeg.CloseoutPackRun26
open PalPeg.CloseoutPackRun29 PalPeg.CloseoutPackRun30 PalPeg.CloseoutPackRun33
open PalPeg.CloseoutPackRun35 PalPeg.CloseoutPackRun36 PalPeg.CloseoutPackRun43
open PalPeg.CloseoutPreload37 PalPeg.CloseoutPackRun22 PalPeg.CloseoutPackRun45
open PalPeg.CloseoutLPack PalPeg.CloseoutLPack2 PalPeg.CloseoutLPack3
open PalPeg.CloseoutLPack4 PalPeg.CloseoutLPack5 PalPeg.CloseoutLPack6
open GalilScaffoldInputHead GalilScaffoldCounter GalilScaffoldChainVerifier
open PalPeg.CloseoutPackRun46 PalPeg.CloseoutFrontExtra
open PalPeg.CloseoutExtraFree
open PalPeg.CloseoutShiftWeak
open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilThrottledRun PalPeg.GalilTrailProof PalPeg.GalilFinalAssembly
open PalPeg.CloseoutRadPack PalPeg.CloseoutRadPack2 PalPeg.CloseoutRadPack3
open PalPeg.CloseoutRadPack4 PalPeg.CloseoutLPack PalPeg.CloseoutLPack2
open PalPeg.CloseoutLPack3 PalPeg.CloseoutLPack4 PalPeg.CloseoutLPack5
open PalPeg.CloseoutLPack6
open PalPeg.GalilRunSkeleton PalPeg.GalilCheckpoints PalPeg.GalilTraceCost
open PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal PalPeg.GalilLexMeasure
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleMC PalPeg.GalilOracleMC2
open PalPeg.GalilLookRefined PalPeg.GalilFinalBaseNeed PalPeg.GalilFinalAssembly2
open PalPeg.GalilLedgerQ64 PalPeg.GalilLedgerAssembly PalPeg.GalilIntervalCost
open PalPeg.GalilLatchTracking PalPeg.GalilArriveChain PalPeg.GalilTickArrive
open PalPeg.GalilTruncTick PalPeg.GalilFinalAssembly4
open PalPeg.GalilTrailScan PalPeg.GalilTrailBudget PalPeg.GalilTrailChain
open PalPeg.GalilTrailAssembly PalPeg.GalilTrailRad PalPeg.GalilFrontMono
open PalPeg.CloseoutOracleI PalPeg.CloseoutOracleI2 PalPeg.GalilInvPlus3
open PalPeg.CloseoutPackRun PalPeg.CloseoutPackRun2 PalPeg.CloseoutPackRun3
open PalPeg.CloseoutPackRun5 PalPeg.CloseoutPackRun7 PalPeg.CloseoutPackRun8
open PalPeg.CloseoutPackRun9 PalPeg.CloseoutPackRun10 PalPeg.CloseoutPackRun11
open PalPeg.CloseoutPackRun12 PalPeg.CloseoutPackRun16 PalPeg.CloseoutPackRun18
open PalPeg.CloseoutPackRun19 PalPeg.CloseoutPackRun20 PalPeg.CloseoutPackRun21
open PalPeg.CloseoutPackRun23 PalPeg.CloseoutPackRun24 PalPeg.CloseoutPackRun26
open PalPeg.CloseoutPackRun29 PalPeg.CloseoutPackRun30 PalPeg.CloseoutPackRun33
open PalPeg.CloseoutPackRun35
open GalilScaffoldInputHead GalilScaffoldCounter GalilScaffoldChainVerifier
open PalPeg.CloseoutPackRun36 PalPeg.CloseoutPackW PalPeg.CloseoutStageCheck
open PalPeg.CloseoutCheckW PalPeg.CloseoutExtraOracle PalPeg.CloseoutExtraFree
open PalPeg.CloseoutFrontExtra PalPeg.CloseoutStageOracle PalPeg.CloseoutStageBoot
open PalPeg.CloseoutShiftS PalPeg.CloseoutPackRun34 PalPeg.GalilLookRefined

open PalPeg.CloseoutOracleW PalPeg.CloseoutChainPack PalPeg.CloseoutPackRun41
open PalPeg.CloseoutShiftS2 PalPeg.CloseoutShiftLocalFree
open PalPeg.CloseoutPackRun47 PalPeg.CloseoutPackRun48

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`bigPack2MG7W''_tick` with `hme` replaced by the landing's `MarksInv'`.**
The only use of `hme` in the original was `marksInv'_tick` for the `marks`
field; taking that field as an input removes the hypothesis and keeps the
rest of the proof verbatim. -/
theorem bigPack2MG7W''_tick_M {w : List (Fin 2)}
    {x y : State GalilVM} (hx : BigPack2MG7W'' centre place entry q first w x)
    (hmy : MarksInv' first y.ctl y.vm)
    (hey : IPackMW centre place entry q first w y → Extra7 y)
    (hSP : ScanNR x → ShiftPal centre place entry q first w x.vm)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hg : SoundScanNR w y) (hlv : CentreLive y.ctl y.vm) :
    BigPack2MG7W'' centre place entry q first w y := by
  have haux : AuxPack y.ctl y.vm := auxPack_tick centre place entry q first hx.aux hx.live h
  suffices hip : IPackMW centre place entry q first w y by
    exact ⟨hip, haux, hlv, hmy, hey hip⟩
  by_cases hcase : x.ctl.mode = Mode.rewind ∧
      (galilFrameS (PofC centre place entry w) q first).atFirst x.vm
  · obtain ⟨hm, hf⟩ := hcase
    obtain ⟨c, s⟩ := x
    obtain ⟨c', t⟩ := y
    obtain ⟨hc', hfr⟩ := tick_rewind_atFirst hm hf h
    have hM : LPackM w c' t :=
      lpackM_rewind_done centre place entry q first hx.ipackM.pack hm hc' hfr
    refine ⟨hM, ?_, fun hP => PalPeg.WindowPack.windowRunPack_tick centre place entry q first hP
        hx.ipackM.pack hx.ipackM.m2 hx.aux (hx.ipackM.win hP) h⟩
    obtain ⟨heq, hset⟩ := hfr
    have htc : t.center = s.center := by rw [hset, heq]; rfl
    have hCR : CentreRep w t := centreRep_congr htc (hx.ipackM.m2.centreRep (Or.inl hm))
    subst hc'
    refine ⟨hM, ?_, ?_, ?_, fun _ => hCR, ?_⟩
    all_goals vac rfl
  · have hnf : x.ctl.mode = Mode.rewind →
        ¬ (galilFrameS (PofC centre place entry w) q first).atFirst x.vm :=
      fun hm hf => hcase ⟨hm, hf⟩
    exact ipackMW_tick centre place entry q first
      (bigPack2MG7W_of_W'' centre place entry q first hx hnf) hSP h hg




/-- **`PackRunRMW` with no `H_marksEntry'` either.**  Every `MarksInv'` the
proof needs is `ChainPack.marks` at the state in question, and `ChainPositionInvariantWithShiftPhase` —
the premise of `hpk` — travels from the `InvLPC` origin (idle chain) along the
run by `chainPosInv2_steps`. -/
theorem packRunR_MWP {w : List (Fin 2)}
    (hSP : ∀ x : State GalilVM, BigPack2MG7W centre place entry q first w x →
      ScanNR x → ShiftPal centre place entry q first w x.vm)
    (hbg : H_BackgroundLandingChainLedger centre place entry q first w)
    (hmatch : H_MatchLandingChainLedger centre place entry q first w)
    (hentry : H_ShiftEntryChainLedger centre place entry q first w)
    (hsd : H_ShiftExitRadiusLedger centre place entry q first w)
    (hpk : ∀ (c : Control) (s : GalilVM), ChainPositionInvariantWithShiftPhase w c s → ChainPack q first w c s)
    (hCanRightEverywhere : ∀ z : State GalilVM,
      z.ctl.mode = Mode.scan ∨ z.ctl.mode = Mode.shift →
      GalilScaffoldChainVerifier.canRight z.vm.right)
    :
    PackRunRMW centre place entry q first w := by
  intro c r hInvLPS M hm1 hmle j x hjx k y hx h hry hyb
  have hIC : InvLPC w c r := hInvLPS.1
  have hlv0 : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 m ⟨c, r⟩ z →
      CentreLive z.ctl z.vm :=
    PalPeg.GalilOracleLeaves2.hlive_of_invLPC centre place entry q first hIC
  have haux0 : AuxPack c r :=
    ⟨coupled_of_invLPC hIC, front_of_invLPC hIC, copyPack_of_invLPC hIC⟩
  have hauxx : AuxPack x.ctl x.vm :=
    auxPack_steps centre place entry q first (x := ⟨c, r⟩) hlv0 haux0 hjx
  have hpos0 : ChainPositionInvariantWithShiftPhase w c r :=
    chainPosInv2_of_idle (chainIdle_of_invS hIC.1.1.1.1)
  have hpi : ∀ (n' : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 n' ⟨c, r⟩ z →
      ChainPack q first w z.ctl z.vm := fun n' z hz =>
    hpk z.ctl z.vm
      (chainPosInv2_steps centre place entry q first hbg hmatch hentry hsd
        (fun _ z' _ => hCanRightEverywhere z') hpos0 hz)
  have hmx : MarksInv' first x.ctl x.vm := (hpi j x hjx).marks
  obtain ⟨g, hg0, hgk, htr⟩ := stepsAll_fn h
  have hreach : ∀ i, i ≤ k →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 (j + i) ⟨c, r⟩ (g i) := by
    intro i hi
    have := steps_of_trace htr i hi
    rw [hg0] at this
    exact steps_trans hjx this
  have hauxi : ∀ i, i ≤ k → AuxPack (g i).ctl (g i).vm := fun i hi =>
    auxPack_steps centre place entry q first (x := ⟨c, r⟩) hlv0 haux0 (hreach i hi)
  have hmg : ∀ i, i ≤ k → MarksInv' first (g i).ctl (g i).vm := fun i hi =>
    (hpi (j + i) (g i) (hreach i hi)).marks
  have hgy : g k = y := hgk
  subst hgy
  have hextra : ∀ i, i ≤ k → IPackMW centre place entry q first w (g i) → Extra7 (g i) := by
    intro i hi hip
    refine extra7_of_front_steps_pack (m := M) (w := w)
      (steps_to_end_of_trace htr (k - i) i (by omega)) ?_ (hauxi i hi).front ?_ ?_ ?_ hm1 hmle ?_
    · intro d z hz
      exact hlv0 (j + i + d) z (steps_trans (hreach i hi) hz)
    · exact (hauxi k le_rfl).front
    · exact hry
    · exact hip.pack
    · exact hyb
  have hexx : Extra7 x := by
    have := hextra 0 (Nat.zero_le _) (by rw [hg0]; exact hx)
    rw [hg0] at this; exact this
  have hbx : BigPack2MG7W'' centre place entry q first w x :=
    ⟨hx, hauxx, hlv0 j x hjx, hmx, hexx⟩
  have hbig : ∀ i, i ≤ k → BigPack2MG7W'' centre place entry q first w (g i) := by
    intro i
    induction i with
    | zero => intro _; rw [hg0]; exact hbx
    | succ n ih =>
      intro hi
      have hn := ih (by omega)
      exact bigPack2MG7W''_tick_M centre place entry q first hn (hmg (n+1) hi)
        (fun hip => hextra (n+1) hi hip)
        (fun hs => hSP (g n) (bigPack2MG7W_of_W'' centre place entry q first hn
          (fun hm => absurd (hs.1.symm.trans hm) (by decide))) hs)
        (htr.tick n (by omega)) (htr.good (n+1) hi)
        (hlv0 (j + (n+1)) (g (n+1)) (hreach (n+1) hi))
  exact ⟨g, hg0, hgk, htr, fun i hi => (hbig i hi).ipackM⟩



/-- **`PackRunRMW` with no `H_marksEntry'` and no `ChainPack` either.**

`CloseoutPackRun17.marksInv'_of_run'` already produces `MarksInv'` at **every**
state of a run started in `scan`, and all four of its inputs are free at an
`InvLPC` origin:

| 入力 | 出どころ |
|---|---|
| `first ≠ 4` | 側条件（`first = 0` なら `by decide`） |
| `hfl`（scan 状態で `0 ≤ value length`） | `GalilInvPlus2.hfloor_of_invLP2` — `InvLPC.1` がそのまま `InvLP2` |
| `hwin`（copy 状態で `WindowInOrigin`） | `CloseoutPackRun25.windowInOrigin_alongRun`（origin は scan なので origin 側の前提が空虚） |
| `CPack q c r` | `GalilCentreLive.cpack_of_entry` ＋ `CloseoutMarksFree.entryCounters_of_invLPC` |

本体は `packRunR_MWP` と同じで、`hpk`／`hpi`（`ChainPack.marks`）の代わりに
`hmarksAlongRun` を使う。したがって `MarksInv'` は `hme` でも `hpack` でもなく、
**run から無償に出る**。 -/
theorem packRunR_MW_marksFree {w : List (Fin 2)} (h4 : first ≠ 4)
    (hP : Decodes (PofC centre place entry w)) :
    PackRunRMW centre place entry q first w := by
  intro c r hInvLPS M hm1 hmle j x hjx k y hx h hry hyb
  have hIC : InvLPC w c r := hInvLPS.1
  have hlv0 : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 m ⟨c, r⟩ z →
      CentreLive z.ctl z.vm :=
    PalPeg.GalilOracleLeaves2.hlive_of_invLPC centre place entry q first hIC
  have haux0 : AuxPack c r :=
    ⟨coupled_of_invLPC hIC, front_of_invLPC hIC, copyPack_of_invLPC hIC⟩
  have hauxx : AuxPack x.ctl x.vm :=
    auxPack_steps centre place entry q first (x := ⟨c, r⟩) hlv0 haux0 hjx
  have hOriginScan : c.mode = Mode.scan := (invS_mode hIC.1.1.1.1).1
  have hmarksAlongRun : ∀ (n' : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 n' ⟨c, r⟩ z →
      MarksInv' first z.ctl z.vm := by
    intro n' z hz
    exact PalPeg.CloseoutPackRun17.marksInv'_of_run' (onLetterVM w) leftFirstVM centre place
      entry q first 2048 h4 hz
      (PalPeg.GalilInvPlus2.hfloor_of_invLP2 centre place entry q first hIC.1)
      (fun m z' hz' hmz => PalPeg.CloseoutPackRun25.windowInOrigin_alongRun (onLetterVM w)
        leftFirstVM centre place entry q first 2048 hz'
        (fun hc => absurd (hOriginScan.symm.trans hc) (by decide)) hmz)
      (PalPeg.GalilCentreLive.cpack_of_entry q hIC.1.1.1.1
        (PalPeg.CloseoutMarksFree.entryCounters_of_invLPC hIC))
      hOriginScan
  have hmx : MarksInv' first x.ctl x.vm := hmarksAlongRun j x hjx
  obtain ⟨g, hg0, hgk, htr⟩ := stepsAll_fn h
  have hreach : ∀ i, i ≤ k →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 (j + i) ⟨c, r⟩ (g i) := by
    intro i hi
    have := steps_of_trace htr i hi
    rw [hg0] at this
    exact steps_trans hjx this
  have hauxi : ∀ i, i ≤ k → AuxPack (g i).ctl (g i).vm := fun i hi =>
    auxPack_steps centre place entry q first (x := ⟨c, r⟩) hlv0 haux0 (hreach i hi)
  have hmg : ∀ i, i ≤ k → MarksInv' first (g i).ctl (g i).vm := fun i hi =>
    hmarksAlongRun (j + i) (g i) (hreach i hi)
  have hgy : g k = y := hgk
  subst hgy
  have hextra : ∀ i, i ≤ k → IPackMW centre place entry q first w (g i) → Extra7 (g i) := by
    intro i hi hip
    refine extra7_of_front_steps_pack (m := M) (w := w)
      (steps_to_end_of_trace htr (k - i) i (by omega)) ?_ (hauxi i hi).front ?_ ?_ ?_ hm1 hmle ?_
    · intro d z hz
      exact hlv0 (j + i + d) z (steps_trans (hreach i hi) hz)
    · exact (hauxi k le_rfl).front
    · exact hry
    · exact hip.pack
    · exact hyb
  have hexx : Extra7 x := by
    have := hextra 0 (Nat.zero_le _) (by rw [hg0]; exact hx)
    rw [hg0] at this; exact this
  have hbx : BigPack2MG7W'' centre place entry q first w x :=
    ⟨hx, hauxx, hlv0 j x hjx, hmx, hexx⟩
  have hbig : ∀ i, i ≤ k → BigPack2MG7W'' centre place entry q first w (g i) := by
    intro i
    induction i with
    | zero => intro _; rw [hg0]; exact hbx
    | succ n ih =>
      intro hi
      have hn := ih (by omega)
      exact bigPack2MG7W''_tick_M centre place entry q first hn (hmg (n+1) hi)
        (fun hip => hextra (n+1) hi hip)
        (fun hs => PalPeg.WindowPack.shiftPal_of_windowRunPack centre place entry q first
          hn.ipackM.pack (hn.ipackM.win hP) (hn.extra.scanAvail hs.1 hs.2) hs)
        (htr.tick n (by omega)) (htr.good (n+1) hi)
        (hlv0 (j + (n+1)) (g (n+1)) (hreach (n+1) hi))
  exact ⟨g, hg0, hgk, htr, fun i hi => (hbig i hi).ipackM⟩

#print axioms packRunR_MW_marksFree

#print axioms bigPack2MG7W''_tick_M
#print axioms packRunR_MWP

end

end PalPeg.CloseoutMarksPack
