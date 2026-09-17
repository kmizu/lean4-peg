import PalPeg.CloseoutExtraFree

/-!
# `hws` weakened from `WatchShiftG` to `ShiftLocalG`

`packRunR_MG27P` takes `hws : ∀ y, WatchShiftG … y`, but uses it at exactly one
place: `ipackMG2_tick_pt7`'s

```
have hsh : ShiftLocalG … w y := by
  by_cases hi : y.vm.chain = ChainVM.idle
  · exact shiftLocalG_of_chainIdle … hi
  · exact shiftLocalG_of_watchShiftG … hi (hws y)
```

So what the pack actually needs is `ShiftLocalG`, which `WatchShiftG` only
*implies* (`shiftLocalG_of_watchShiftG`, `CloseoutPackRun26:237`).  Taking
`ShiftLocalG` directly is a strictly weaker hypothesis, and it drops
`WatchShiftG`'s fifth conjunct (`Sane wch.machine.verifier` is folded into
`ver`) as well as the idle case-split.

Of `ShiftLocalG`'s four fields, `move` — `ScanNR x → … → canRight x.vm.right` —
is exactly wave 7's `Extra7` payload, so it is already free on a run
(`CloseoutFrontExtra.extra7_of_front_steps_pack`).  `guard` / `coupled` / `ver`
are what remain, and `CloseoutPackRun34`'s `ShiftLocalS` is the guarded form
those can actually take (see `CloseoutShiftS`).

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutShiftWeak

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

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `CloseoutPackRun45.ipackMG2_tick_pt6S` over `BigPack2MG7`. -/
theorem ipackMG2_tick_pt7L {w : List (Fin 2)}
    (hsl : ∀ y : State GalilVM, ShiftLocalG centre place entry q first w y)
    {x y : State GalilVM} (hx : BigPack2MG7 centre place entry q first w x)
    (hSP : ScanNR x → ShiftPal centre place entry q first w x.vm)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hg : SoundScanNR w y) : IPackMG2 centre place entry q first w y := by
  have hL := lticksN_of_lpackM2_pt7 centre place entry q first hx hx.ipackM.m2
  have hsh : ShiftLocalG centre place entry q first w y := hsl y
  refine ⟨⟨?_, hsh⟩,
    lpackM2_tick' centre place entry q first hx.ipackM.m2 hL hx.aux
      (lTickLeaves2_of_shiftPalG centre place entry q first hx.ipackM.m2 hL hSP) h⟩
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  exact lpackN_tick centre place entry q first hx.ipackM.base.pack hL h




theorem bigPack2MG7''_tickL {w : List (Fin 2)}
    (hsl : ∀ y : State GalilVM, ShiftLocalG centre place entry q first w y)
    (hme : H_marksEntry' (PofC centre place entry w) q first)
    {x y : State GalilVM} (hx : BigPack2MG7'' centre place entry q first w x)
    (hey : IPackMG2 centre place entry q first w y → Extra7 y)
    (hSP : ScanNR x → ShiftPal centre place entry q first w x.vm)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hg : SoundScanNR w y) (hlv : CentreLive y.ctl y.vm) :
    BigPack2MG7'' centre place entry q first w y := by
  have haux : AuxPack y.ctl y.vm := auxPack_tick centre place entry q first hx.aux hx.live h
  have hmarks : MarksInv' first y.ctl y.vm := by
    obtain ⟨c, s⟩ := x
    obtain ⟨c', t⟩ := y
    exact marksInv'_tick _ q first 2048 hx.marks (fun hm ho hs => hme c s hm ho hs) h
  suffices hip : IPackMG2 centre place entry q first w y by
    exact ⟨hip, haux, hlv, hmarks, hey hip⟩
  by_cases hcase : x.ctl.mode = Mode.rewind ∧
      (galilFrameS (PofC centre place entry w) q first).atFirst x.vm
  · obtain ⟨hm, hf⟩ := hcase
    obtain ⟨c, s⟩ := x
    obtain ⟨c', t⟩ := y
    obtain ⟨hc', hfr⟩ := tick_rewind_atFirst hm hf h
    have hM : LPackM w c' t :=
      lpackM_rewind_done centre place entry q first hx.ipackM.base.pack hm hc' hfr
    have hG : ShiftLocalG centre place entry q first w ⟨c', t⟩ := by
      apply shiftLocalG_of_chainIdle
      apply haux.coupled.idleOut
      all_goals (show c'.mode ≠ _; rw [hc']; intro h; exact Mode.noConfusion h)
    refine ⟨⟨hM, hG⟩, ?_⟩
    obtain ⟨heq, hset⟩ := hfr
    have htc : t.center = s.center := by rw [hset, heq]; rfl
    have hCR : CentreRep w t := centreRep_congr htc (hx.ipackM.m2.centreRep (Or.inl hm))
    subst hc'
    refine ⟨hM, ?_, ?_, ?_, fun _ => hCR, ?_⟩
    all_goals vac rfl
  · have hnf : x.ctl.mode = Mode.rewind →
        ¬ (galilFrameS (PofC centre place entry w) q first).atFirst x.vm :=
      fun hm hf => hcase ⟨hm, hf⟩
    exact ipackMG2_tick_pt7L centre place entry q first hsl
      (bigPack2MG7_of_bigPack2MG7'' centre place entry q first hx hnf) hSP h hg



theorem packRunR_MG27L {w : List (Fin 2)}
    (hsl : ∀ y : State GalilVM, ShiftLocalG centre place entry q first w y)
    (hSP : ∀ x : State GalilVM, BigPack2MG7 centre place entry q first w x →
      ScanNR x → ShiftPal centre place entry q first w x.vm)
    (hme : H_marksEntry' (PofC centre place entry w) q first)
    :
    PackRunRMG2P centre place entry q first w := by
  intro c r hIC M hm1 hmle j x hjx k y hx h hry hyb
  have hlv0 : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 m ⟨c, r⟩ z →
      CentreLive z.ctl z.vm :=
    PalPeg.GalilOracleLeaves2.hlive_of_invLPC centre place entry q first hIC
  have haux0 : AuxPack c r :=
    ⟨coupled_of_invLPC hIC, front_of_invLPC hIC, copyPack_of_invLPC hIC⟩
  have hauxx : AuxPack x.ctl x.vm :=
    auxPack_steps centre place entry q first (x := ⟨c, r⟩) hlv0 haux0 hjx
  have hmx : MarksInv' first x.ctl x.vm :=
    marksInv'_of_run (PofC centre place entry w) q first 2048 hme (x := ⟨c, r⟩) hjx
      (m := Mode.scan) (by decide) (invS_mode hIC.1.1.1.1).1
  obtain ⟨g, hg0, hgk, htr⟩ := stepsAll_fn h
  have hreach : ∀ i, i ≤ k →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 (j + i) ⟨c, r⟩ (g i) := by
    intro i hi
    have := steps_of_trace htr i hi
    rw [hg0] at this
    exact steps_trans hjx this
  have hauxi : ∀ i, i ≤ k → AuxPack (g i).ctl (g i).vm := fun i hi =>
    auxPack_steps centre place entry q first (x := ⟨c, r⟩) hlv0 haux0 (hreach i hi)
  have hgy : g k = y := hgk
  subst hgy
  have hextra : ∀ i, i ≤ k → IPackMG2 centre place entry q first w (g i) → Extra7 (g i) := by
    intro i hi hip
    refine extra7_of_front_steps_pack (m := M) (w := w)
      (steps_to_end_of_trace htr (k - i) i (by omega)) ?_ (hauxi i hi).front ?_ ?_ ?_ hm1 hmle ?_
    · intro d z hz
      exact hlv0 (j + i + d) z (steps_trans (hreach i hi) hz)
    · exact (hauxi k le_rfl).front
    · exact hry
    · exact hip.base.pack
    · exact hyb
  have hexx : Extra7 x := by
    have := hextra 0 (Nat.zero_le _) (by rw [hg0]; exact hx)
    rw [hg0] at this; exact this
  have hbx : BigPack2MG7'' centre place entry q first w x :=
    ⟨hx, hauxx, hlv0 j x hjx, hmx, hexx⟩
  have hbig : ∀ i, i ≤ k → BigPack2MG7'' centre place entry q first w (g i) := by
    intro i
    induction i with
    | zero => intro _; rw [hg0]; exact hbx
    | succ n ih =>
      intro hi
      have hn := ih (by omega)
      exact bigPack2MG7''_tickL centre place entry q first hsl hme hn
        (fun hip => hextra (n+1) hi hip)
        (fun hs => hSP (g n) (bigPack2MG7_of_bigPack2MG7'' centre place entry q first hn
          (fun hm => absurd (hs.1.symm.trans hm) (by decide))) hs)
        (htr.tick n (by omega)) (htr.good (n+1) hi)
        (hlv0 (j + (n+1)) (g (n+1)) (hreach (n+1) hi))
  exact ⟨g, hg0, hgk, htr, fun i hi => (hbig i hi).ipackM⟩


#print axioms ipackMG2_tick_pt7L
#print axioms bigPack2MG7''_tickL
#print axioms packRunR_MG27L

end

end PalPeg.CloseoutShiftWeak
