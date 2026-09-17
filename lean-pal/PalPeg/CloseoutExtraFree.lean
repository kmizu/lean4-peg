import PalPeg.CloseoutFrontExtra

/-!
# `Extra7` supplied by the run itself: `hee` and `het` are not obligations

`CloseoutPackRun46.packRunR_MG27` (:223) takes two `Extra7` inputs — `hprefix`
(built from `hee` at the origin and `het` at every tick) and `het` again inside
the `hbig` induction.  `CloseoutFrontExtra.extra7_of_front_run_pack` produces
`Extra7` from the run alone, provided the run's **exit** carries the cycle's
position bound — which `CycleOutMC3` always does.

Two obstacles, both resolved here:

* **The head facts.**  `extra7_of_bound` needs `Represents … w` and
  `focus ≠ none` for the right head.  `Extra7` only speaks at `scan` /
  non-replaying states, and `LPack.scanInv` hands over a `ScanInvariant` exactly
  there, whose `rightRep`/`rightPresent` are those two facts
  (`CloseoutFrontExtra.rrep_of_lpack`).
* **Circularity in the induction.**  `Extra7 (g (n+1))` needs the pack at
  `g (n+1)`, which is what the tick lemma is building.  `bigPack2MG7''_tickE`
  below takes the `Extra7` as a *function* of the pack it has just built, so the
  pack is available before the `Extra7` is demanded.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutExtraFree

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

section PackE7
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)


/-! ## The tail of a trace

`CloseoutPackRun2.steps_of_trace` gives the run from the trace's origin to any
index; the `Extra7` supply needs the run from any index to the trace's *end*.
Downward induction on the gap. -/

theorem steps_to_end_of_trace {σ : Type} {F : Frame σ} {delay : ℕ}
    {Q : GalilScaffoldTop.State σ → Prop} {g : ℕ → GalilScaffoldTop.State σ} {e : ℕ}
    (htr : Trace F delay Q g e) :
    ∀ d i, i + d = e → Steps F delay d (g i) (g e) := by
  intro d
  induction d with
  | zero => intro i hi; rw [← hi]; exact .zero _
  | succ n ih =>
    intro i hi
    exact .succ (htr.tick i (by omega)) (ih (i+1) (by omega))

/-- `CloseoutPackRun46.bigPack2MG7''_tick` (:172) with `het` replaced by the
`Extra7` at the landing, taken as a function of the pack the proof builds first.
-/
theorem bigPack2MG7''_tickE {w : List (Fin 2)}
    (hws : ∀ y : State GalilVM, WatchShiftG centre place entry q first w y)
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
    exact ipackMG2_tick_pt7 centre place entry q first hws
      (bigPack2MG7_of_bigPack2MG7'' centre place entry q first hx hnf) hSP h hg


#print axioms bigPack2MG7''_tickE

/-- `CloseoutPackRun36.PackRunRMG2` with the cycle's own exit bound as an extra
input.  Every caller has it: `CycleOutMC3`'s progress exit carries
`position sT.right ≤ 2*m-1` by definition, and its checkpoint exit carries the
next checkpoint's bound. -/
def PackRunRMG2P (w : List (Fin 2)) : Prop :=
  ∀ (c : Control) (r : GalilVM), InvLPC w c r →
    ∀ (M : ℕ), 1 ≤ M → M ≤ w.length →
    ∀ (j : ℕ) (x : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 j ⟨c, r⟩ x →
      ∀ (k : ℕ) (y : State GalilVM), IPackMG2 centre place entry q first w x →
        StepsAll (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) k x y →
        y.ctl.replaying = false → position y.vm.right ≤ 2 * M - 1 →
        StepsIMG2 centre place entry q first w k x y

/-- **`PackRunRMG2P` with no `Extra7` input at all.**  `hee` and `het` existed
only to build `hprefix`; the run supplies it (`extra7_of_front_run_pack`). -/
theorem packRunR_MG27P {w : List (Fin 2)}
    (hws : ∀ y : State GalilVM, WatchShiftG centre place entry q first w y)
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
      exact bigPack2MG7''_tickE centre place entry q first hws hme hn
        (fun hip => hextra (n+1) hi hip)
        (fun hs => hSP (g n) (bigPack2MG7_of_bigPack2MG7'' centre place entry q first hn
          (fun hm => absurd (hs.1.symm.trans hm) (by decide))) hs)
        (htr.tick n (by omega)) (htr.good (n+1) hi)
        (hlv0 (j + (n+1)) (g (n+1)) (hreach (n+1) hi))
  exact ⟨g, hg0, hgk, htr, fun i hi => (hbig i hi).ipackM⟩


#print axioms packRunR_MG27P

end PackE7

end PalPeg.CloseoutExtraFree
