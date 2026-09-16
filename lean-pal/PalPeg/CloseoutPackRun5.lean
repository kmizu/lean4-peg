import PalPeg.CloseoutPackRun4
import PalPeg.CloseoutLPack6

/-!
# `CloseoutPackRun5`: the guarded centre invariant, and the re-cut pack

`CloseoutPackRun4.minv_false_at_mismatch` refutes `CloseoutPackRun3.BigResid5`'s
`rMismatchMinv`, and with it the third field of `CloseoutLPack.LPack`:

```
minv : c.mode ≠ Mode.init → MInv w c s
```

is **false** along a real run.  A mismatching comparison kills the current
centre, and the machine spends the whole fallback phase (`copy`, `home`, `fpp`,
`markEnd`, `choose`, `rewind`) with no live centre at all; the leftmost-live
centre is only re-installed at the `replayStart` landing.

This file performs the re-cut the audit called for.

* **§1** `MInvG w c s := c.mode = Mode.scan → MInv w c s` and `LPackG` /
  `IPackG`.  `MInvG` demands the centre invariant *only in scan mode*; every
  fallback phase satisfies it vacuously, and the landing back into `scan` is
  where it has to be re-established.  `LPack → LPackG` is free
  (`lpackG_of_lpack`), so `LPackG` is a genuine weakening.

* **§2** the trail bridge over the weakened pack.  The point of the re-cut is
  that nothing downstream ever reads `LPack.minv`: `CloseoutRadPack2.LeftLive`
  is `LPack.lrep` (scan comparison and rewind only) and the shift-entry budget
  is `LPack.scanInv` plus `ShiftLocal`.  So the whole of `CloseoutLPack6`'s
  pointwise chain re-runs verbatim, and `h_trailI_G` is `H_trailI` with `IPack`
  replaced by the weaker `IPackG`.  `CloseoutLPack5.H_trailI` follows
  (`h_trailI_of_G`), so the weakening costs nothing at all.

* **§3** `LTickLeavesG` and `lpackG_tick`: `LPackG` along one tick.  Compared
  with `CloseoutLPack3.LTickLeaves`, **four** corners disappear outright,
  because their landing mode is not `scan`:

  | corner | landing mode | status under `MInvG` |
  |---|---|---|
  | `shiftMinv` | `shift` | vacuous |
  | `fallbackMinv` | `copy` | vacuous (this is the **false** one) |
  | `shiftOneMinv` | `shift` | vacuous |
  | `rewindPairMinv` | `rewind` | vacuous |
  | `choosePack`'s `MInv` half | `rewind` | vacuous |

  and exactly one new corner appears, `shiftDoneMinv`, at the `shift → scan`
  exit; `replayPackG` is the `replayStart → scan` landing.  These are the two
  re-establishment points the audit named:
  `GalilLiveCentreShift.leftmost_shift` at the candidate period
  (`CloseoutPackRun3.Extra.cand`) for the first, and
  `GalilLiveCentreFallback.leftmost_after_fallback` +
  `GalilLiveCentreReplay.minv_after_fallback` — fed by the maximality of
  `chosenRadius` (`Extra.failed` / `GalilLeafDp.StageFailed`) and the rewind
  distance — for the second.

* **§4** `BigResid5G`: `CloseoutPackRun3.BigResid5` re-cut over `LPackG`.  Nine
  contracts become **seven**, the refuted `rMismatchMinv` and the two
  fallback-phase `MInv` contracts (`rShiftOneMinv`, `rRewindPairMinv`) are gone,
  `rChoosePack` loses its `MInv` half, and one contract is added
  (`rShiftDoneMinv`).  `lticksG_of_big5G` produces `LTickLeavesG`, so
  `lpackG_tick` is available at every packed state.

## §5 `packRunR_G` and `pal_in_peg_final11`

The payload swap the earlier draft of this file described as "an edit of
`CloseoutLPack5` / `CloseoutPackRun2` rather than a new lemma" has been made:
`CloseoutLPack5.IPack`'s first field is now `LPackG`, so the whole run
vocabulary (`StepsI`, `ReachAtI`, `CycleOutI`, `CycleOracleI`, `PreTraceI`,
`H_bootI`, `H_oracleI`, `H_trailI`) and `CloseoutPackRun2.PackRunR` carry the
guarded pack by definition, and `IPackG` is literally `IPack`.  `H_trailI` is
therefore `H_trailI_G`, which §2 proves outright.  `bigPack2_tickG` and
`packRunR_G` re-run `CloseoutPackRun3`'s tick induction over `BigResid5G`, and
`pal_in_peg_final11` is `pal_in_peg_final10` with the seven re-cut contracts in
place of the nine (plus `H_extraEntry` / `H_extraTick` unchanged).

The legacy residuals `CloseoutPackRun.BigResid`, `CloseoutPackRun2.BigResid'` /
`BigResid4` and `CloseoutPackRun3.BigResid5` each gained the one new corner
`rShiftDoneMinv` so that their `lticks_of_*` lemmas produce `LTickLeavesG`; the
corners the re-cut drops are still fields there, merely unused.

## Honest status

Standard axioms only.  The false field of `LPack` is replaced by a guarded one
that the machine can actually satisfy, and the trail bridge is re-proved over
it.  Unconditional `PAL ∈ PEG` remains open.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun5

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilCheckpoints
open PalPeg.GalilThrottledRun PalPeg.GalilTrailProof
open PalPeg.GalilFinalAssembly PalPeg.GalilFinalAssembly2 PalPeg.GalilFinalAssembly4
open PalPeg.CloseoutRadPack PalPeg.CloseoutRadPack2 PalPeg.CloseoutRadPack3
open PalPeg.CloseoutRadPack4
open PalPeg.CloseoutLPack PalPeg.CloseoutLPack3 PalPeg.CloseoutLPack4 PalPeg.CloseoutLPack5
open PalPeg.CloseoutLPack6
open PalPeg.CloseoutPackRun PalPeg.CloseoutPackRun2 PalPeg.CloseoutPackRun3
open PalPeg.CloseoutOracleI PalPeg.CloseoutOracleI2 PalPeg.GalilInvPlus3
open PalPeg.GalilTrailScan PalPeg.GalilTrailBudget PalPeg.GalilTrailChain
open PalPeg.GalilTrailAssembly PalPeg.GalilTrailRad

/-! ## 1. The guarded centre invariant

`MInvG`, `LPackG` and the guarded tick machinery now live in
`CloseoutLPack5`, because `CloseoutLPack5.IPack` *is* the guarded pack: its
first field was swapped from `LPack` to `LPackG`.  They are re-exported here
under their original `CloseoutPackRun5` names. -/

export PalPeg.CloseoutLPack5 (MInvG minvG_of_minv LPackG lpackG_of_lpack
  leftLive_of_lpackG lpackG_boot lpackG_of_same LTickLeavesG lpackG_tick
  lpackG_tick' lpackG_steps)

section IPackG
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **The re-cut run payload.**  `CloseoutLPack5.IPack` *is* `LPackG` plus
`ShiftLocal`; the payload swap the audit called for is a definition change in
`CloseoutLPack5`, so `IPackG` is now literally `IPack`. -/
abbrev IPackG (w : List (Fin 2)) (x : State GalilVM) : Prop :=
  IPack centre place entry q first w x

theorem ipackG_of_ipack {w : List (Fin 2)} {x : State GalilVM}
    (h : IPack centre place entry q first w x) : IPackG centre place entry q first w x := h

end IPackG

#print axioms ipackG_of_ipack

/-! ## 2. The trail bridge over `IPackG`

Every step of `CloseoutLPack6` is re-run.  The only two places the payload is
read are `leftLive_pt` (which uses `LPack.lrep`) and `halfBound_of_ipack`
(which uses `LPack.scanInv` and `ShiftLocal`); neither touches `minv`, so the
weakened pack carries the whole chain.
-/

section Trail
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `LeftLive` at every tick, from the weakened pack. -/
theorem leftLive_ptG {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hIP : ∀ i, i ≤ Tc w.length → IPackG centre place entry q first w (st i)) :
    ∀ i, i ≤ Tc w.length → PalPeg.GalilTrailSane.LeftLive (st i).ctl (st i).vm :=
  fun i hi => leftLive_of_lpackG (hIP i hi).pack

/-- **`CloseoutLPack6.halfBound_of_ipack` over `IPackG`.**  `4h ≤ distance ≤ 2·rad`. -/
theorem halfBound_of_ipackG {w : List (Fin 2)} {x : State GalilVM}
    (hx : IPackG centre place entry q first w x) {s'' t'' : GalilVM}
    (hcmp : (galilFrameS (PofC centre place entry w) q first).compare x.vm s'')
    (hb : beginShiftVM' s'' t'') :
    ∃ rad : ℕ,
      ScanInvariant w (position x.vm.center) rad x.vm.left x.vm.right ∧
      GalilScaffoldChainVerifier.canRight x.vm.right ∧
      ∀ wch : GalilScaffoldChainWatch.State, s''.chain = .watch wch →
        2 * periodLength wch ≤ rad := by
  obtain ⟨hmode, hrep⟩ := hx.shift.mode s'' t'' hcmp hb
  obtain ⟨rad, hscan⟩ := hx.pack.scanInv hmode hrep
  refine ⟨rad, hscan, hx.shift.move s'' t'' hcmp hb, fun wch hch => ?_⟩
  have h4 : 4 * (periodLength wch : ℤ) ≤
      GalilScaffoldCounter.value wch.machine.control.distance :=
    hx.shift.guard s'' t'' hcmp hb wch hch
  have h2 : GalilScaffoldCounter.value wch.machine.control.distance ≤ 2 * (rad : ℤ) :=
    hx.shift.coupled s'' t'' hcmp hb wch hch rad hscan
  omega

/-- **`CloseoutLPack6.shiftEntry_pt` over `IPackG`.** -/
theorem shiftEntry_ptG {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hIP : ∀ i, i ≤ Tc w.length → IPackG centre place entry q first w (st i)) :
    ∀ i, i ≤ Tc w.length → ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
      beginShiftVM' s'' t'' → ShiftBud t'' := by
  intro i hi s'' t'' hcmp hb
  obtain ⟨rad, hscan, hcan, hh⟩ :=
    halfBound_of_ipackG centre place entry q first (hIP i hi) hcmp hb
  exact shiftBud_of_scanInv (onLetterVM w) leftFirstVM centre place entry q first
    hscan hcan hcmp hb hh

/-- **`CloseoutLPack6.shiftVerSane_pt` over `IPackG`.** -/
theorem shiftVerSane_ptG {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hIP : ∀ i, i ≤ Tc w.length → IPackG centre place entry q first w (st i)) :
    ∀ i, i ≤ Tc w.length → ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
      beginShiftVM' s'' t'' → SaneVer t''.chain :=
  fun i hi s'' t'' hcmp hb =>
    saneVer_beginShift hb ((hIP i hi).shift.ver s'' t'' hcmp hb)

/-- **`CloseoutLPack6.radPack_pt` over `IPackG`.**  The three tick inductions
(`radLedger_pt`, `shiftOrd_pt`, `verSane_pt`) take their side conditions as
arguments, so they are reused verbatim. -/
theorem radPack_ptG {w : List (Fin 2)} (hw : 0 < w.length) {st : ℕ → State GalilVM}
    {Tc : ℕ → ℕ} (hP : PreTrace centre place entry q first w st Tc)
    (hIP : ∀ i, i ≤ Tc w.length → IPackG centre place entry q first w (st i)) :
    ∀ i, i ≤ Tc w.length → RadPack (st i).ctl (st i).vm := by
  have hll := leftLive_ptG centre place entry q first hIP
  have hen := shiftEntry_ptG centre place entry q first hIP
  have hsv := shiftVerSane_ptG centre place entry q first hIP
  have hL := radLedger_pt centre place entry q first hw hP hll
  have hS := shiftOrd_pt centre place entry q first hw hP hll hen
  have hV := verSane_pt centre place entry q first hw hP hll hsv
  exact fun i hi => radPack_of_parts (hL i hi) (hS i hi) (hll i hi) (hV i hi)

/-- **`CloseoutLPack6.trailF_pt` over `IPackG`.** -/
theorem trailF_ptG {w : List (Fin 2)} (hw : 0 < w.length) {st : ℕ → State GalilVM}
    {Tc : ℕ → ℕ} (hP : PreTrace centre place entry q first w st Tc)
    (hIP : ∀ i, i ≤ Tc w.length → IPackG centre place entry q first w (st i))
    {m : ℕ} (hm : m < w.length) :
    ∀ i, i ≤ Tc (m+1) → TrailF w m (st i) := by
  have hll := leftLive_ptG centre place entry q first hIP
  have hsane := sanePack_pt centre place entry q first hw hP hll
  have hrad := radPack_ptG centre place entry q first hw hP hIP
  have hscan := scanT_pt centre place entry q first hw hP hrad hsane hm
  have hB := chainBudget_pt centre place entry q first hw hP hrad hsane hm
  have hV := verF_trace centre place entry q first hP hm hscan hB
  exact fun i hi => trailF_of_scanT (hscan i hi) (hV i hi).ver (hV i hi).lagPos

/-- **(NAMED-FREE) `CloseoutLPack5.H_trailI` with the weakened payload.**  This
is the statement `CloseoutLPack5.needI'_le` consumes, asking only for `IPackG`
at every tick. -/
def H_trailI_G : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    (∀ i, i ≤ Tc w.length → IPackG centre place entry q first w (st i)) →
    ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) → TrailF w m (st i)

/-- **The trail bridge over the weakened pack is a theorem.** -/
theorem h_trailI_G : H_trailI_G centre place entry q first :=
  fun _ hw _ _ hP hIP _ hm i hi =>
    trailF_ptG centre place entry q first hw hP hIP hm i hi

/-- **`CloseoutLPack6.h_trailI` is a corollary**: the weakening costs nothing,
because `IPack → IPackG`. -/
theorem h_trailI_of_G : H_trailI centre place entry q first :=
  fun w hw st Tc hP hIP m hm i hi =>
    h_trailI_G centre place entry q first w hw st Tc hP
      (fun j hj => ipackG_of_ipack centre place entry q first (hIP j hj)) m hm i hi

end Trail

#print axioms leftLive_ptG
#print axioms halfBound_of_ipackG
#print axioms shiftEntry_ptG
#print axioms shiftVerSane_ptG
#print axioms radPack_ptG
#print axioms trailF_ptG
#print axioms h_trailI_G
#print axioms h_trailI_of_G

/-! ## 3. `LPackG` along one tick — see `CloseoutLPack5` -/

/-! ## 4. The re-cut residual over `BigPack2` -/

section Resid
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) `CloseoutPackRun3.BigResid5`, re-cut.**  Seven contracts instead
of nine: the refuted `rMismatchMinv` is gone, and with it `rShiftOneMinv` and
`rRewindPairMinv` (fallback/shift-phase `MInv`, vacuous under `MInvG`);
`rChoosePack` keeps only its head half; `rShiftDoneMinv` is new. -/
structure BigResid5G (w : List (Fin 2)) : Prop where
  rInitPackG : ∀ x : State GalilVM, BigPack2 centre place entry q first w x →
    x.ctl.mode = Mode.init → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).init x.vm t →
    LPackG w {x.ctl with mode := Mode.scan, output := true} t
  rScanInvR : ∀ x : State GalilVM, BigPack2 centre place entry q first w x →
    x.ctl.mode = Mode.scan →
    ∃ r, ScanInvariant w (position x.vm.center) r x.vm.left x.vm.right
  rShiftDoneScan : ∀ x : State GalilVM, BigPack2 centre place entry q first w x →
    x.ctl.mode = Mode.shift →
    ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos x.vm →
    ∃ r, ScanInvariant w (position x.vm.center) r x.vm.left x.vm.right
  rShiftDoneMinv : ∀ x : State GalilVM, BigPack2 centre place entry q first w x →
    x.ctl.mode = Mode.shift →
    ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos x.vm →
    MInv w x.ctl x.vm
  rChoosePackL : ∀ x : State GalilVM, BigPack2 centre place entry q first w x →
    x.ctl.mode = Mode.choose → x.ctl.odd = true → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).choose x.vm t →
    GalilScaffoldInputTrace.Represents t.left.head w ∧ t.left.head.focus ≠ none
  rReplayPackG : ∀ x : State GalilVM, BigPack2 centre place entry q first w x →
    x.ctl.mode = Mode.replayStart → ∀ (t : GalilVM) (o : Bool),
    (galilFrameS (PofC centre place entry w) q first).replayStart x.vm t →
    LPackG w {x.ctl with mode := Mode.scan, clock := 2048, output := o, replaying := (galilFrameS (PofC centre place entry w) q first).replayPos t} t
  rShiftNext : ∀ x y : State GalilVM, BigPack2 centre place entry q first w x →
    Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y →
    SoundScanNR w y → ShiftLocal centre place entry q first w y

/-- **The re-cut leaves from the seven contracts plus `Extra`.**  `scanLeft`
and `rewindLeft` still come from the margins, `scanCanR` from
`CloseoutPackRun3.canR_of_bigPack2`; the two `minv_of_mismatch` entries — the
ones `CloseoutPackRun4` refuted — have no counterpart here. -/
theorem lticksG_of_big5G {w : List (Fin 2)} (hr : BigResid5G centre place entry q first w)
    {x : State GalilVM} (hx : BigPack2 centre place entry q first w x) :
    LTickLeavesG centre place entry q first w x.ctl x.vm where
  initPackG := hr.rInitPackG x hx
  scanLeft := fun hm => by
    obtain ⟨r, hi⟩ := hr.rScanInvR x hx hm
    exact left_pos_of_two (margin_of_scanInv hi (hx.extra.scanMargin hm r hi))
  scanInvR := hr.rScanInvR x hx
  scanCanR := fun hm => canR_of_bigPack2 centre place entry q first hx.big hx.extra hm
  shiftDoneScan := hr.rShiftDoneScan x hx
  shiftDoneMinv := hr.rShiftDoneMinv x hx
  choosePackL := hr.rChoosePackL x hx
  rewindLeft := fun hm => left_pos_of_two (hx.extra.rewindMargin hm)
  replayPackG := hr.rReplayPackG x hx

/-- **The nine contracts of `BigResid5` imply the seven of `BigResid5G`** —
except for `rShiftDoneMinv`, which is genuinely new.  This is the precise sense
in which the re-cut is a weakening plus one obligation. -/
theorem big5G_of_big5 {w : List (Fin 2)} (hr : BigResid5 centre place entry q first w) :
    BigResid5G centre place entry q first w where
  rInitPackG := fun x hx hm t ht => lpackG_of_lpack (hr.rInitPack x hx hm t ht)
  rScanInvR := hr.rScanInvR
  rShiftDoneScan := hr.rShiftDoneScan
  rShiftDoneMinv := hr.rShiftDoneMinv
  rChoosePackL := fun x hx hm ho t ht => (hr.rChoosePack x hx hm ho t ht).1
  rReplayPackG := fun x hx hm t o ht => lpackG_of_lpack (hr.rReplayPack x hx hm t o ht)
  rShiftNext := hr.rShiftNext

end Resid

#print axioms lpackG_steps
#print axioms lticksG_of_big5G
#print axioms big5G_of_big5


/-! ## 5. `packRunR_G` and `pal_in_peg_final11` -/

section RunG
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **One tick of the enlarged pack over the re-cut residual.**
`CloseoutPackRun3.bigPack2_tick` with `lticks_of_big5` / `lpack_tick` replaced by
`lticksG_of_big5G` / `lpackG_tick`. -/
theorem bigPack2_tickG {w : List (Fin 2)} (hr : BigResid5G centre place entry q first w)
    (het : H_extraTick centre place entry q first w)
    {x y : State GalilVM} (hx : BigPack2 centre place entry q first w x)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hg : SoundScanNR w y) (hlv : CentreLive y.ctl y.vm) :
    BigPack2 centre place entry q first w y := by
  refine ⟨?_, het x y hx.extra h⟩
  refine bigPack_mk centre place entry q first
    ⟨?_, hr.rShiftNext x y hx h hg⟩
    (auxPack_tick centre place entry q first
      (auxPack_of_bigPack centre place entry q first hx.big) hx.big.live h) hlv
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  exact lpackG_tick centre place entry q first hx.big.ipack.pack
    (lticksG_of_big5G centre place entry q first hr hx) h

/-- **`CloseoutPackRun2.PackRunR` from the seven re-cut contracts plus the two
`Extra` obligations.**  `CloseoutPackRun3.packRunR_of_big5` verbatim over
`BigResid5G`. -/
theorem packRunR_G {w : List (Fin 2)}
    (hr : BigResid5G centre place entry q first w)
    (hee : H_extraEntry centre place entry w)
    (het : H_extraTick centre place entry q first w) :
    PackRunR centre place entry q first w := by
  intro c r hIC j x hjx k y hx h
  have hlv0 : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 m ⟨c, r⟩ z →
      CentreLive z.ctl z.vm :=
    PalPeg.GalilOracleLeaves2.hlive_of_invLPC centre place entry q first hIC
  have haux0 : AuxPack c r :=
    ⟨coupled_of_invLPC hIC, front_of_invLPC hIC, copyPack_of_invLPC hIC⟩
  have hauxx : AuxPack x.ctl x.vm :=
    auxPack_steps centre place entry q first (x := ⟨c, r⟩) hlv0 haux0 hjx
  have hexx : Extra centre place entry w x :=
    extra_steps centre place entry q first het (x := ⟨c, r⟩) (hee c r hIC) hjx
  have hbx : BigPack2 centre place entry q first w x :=
    ⟨bigPack_mk centre place entry q first hx hauxx (hlv0 j x hjx), hexx⟩
  obtain ⟨g, hg0, hgk, htr⟩ := stepsAll_fn h
  have hreach : ∀ i, i ≤ k →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 (j + i) ⟨c, r⟩ (g i) := by
    intro i hi
    have := steps_of_trace htr i hi
    rw [hg0] at this
    exact steps_trans hjx this
  have hbig : ∀ i, i ≤ k → BigPack2 centre place entry q first w (g i) := by
    intro i
    induction i with
    | zero => intro _; rw [hg0]; exact hbx
    | succ n ih =>
      intro hi
      exact bigPack2_tickG centre place entry q first hr het (ih (by omega))
        (htr.tick n (by omega)) (htr.good (n+1) hi)
        (hlv0 (j + (n+1)) (g (n+1)) (hreach (n+1) hi))
  exact ⟨g, hg0, hgk, htr, fun i hi => (hbig i hi).big.ipack⟩

end RunG

/-- **`CloseoutPackRun3.pal_in_peg_final10` over the re-cut residual.**  Nine
contracts become seven: the refuted `rMismatchMinv` and the two fallback-phase
`MInv` contracts are gone, `rChoosePack` keeps only its head half, and
`rShiftDoneMinv` is added at the `shift → scan` exit. -/
theorem pal_in_peg_final11 (entry q : ℕ) (first : Fin 9)
    (hr : ∀ w : List (Fin 2), BigResid5G centreC placeC entry q first w)
    (hee : ∀ w : List (Fin 2), H_extraEntry centreC placeC entry w)
    (het : ∀ w : List (Fin 2), H_extraTick centreC placeC entry q first w)
    (hsl : ∀ w : List (Fin 2), H_shiftLocalC centreC placeC entry q first w)
    (hsc : ∀ w : List (Fin 2), H_stageScan centreC placeC entry q first w)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleMC3 (PofC centreC placeC entry w) q first w)
    (hbs : H_bootShift centreC placeC entry q first)
    (hls : H_landShift centreC placeC entry q first)
    (hC : H_realizeLI' centreC placeC entry q first) :
    RecognizedByTotalPEG PAL :=
  pal_in_peg_final6' entry q first h_lrepC hbs hls
    (fun w hw => cycleOracleI_of_cycleOracleMC3R centreC placeC entry q first
      (packRunR_G centreC placeC entry q first (hr w) (hee w) (het w)) (hsl w) (hsc w)
      (hor w hw))
    hC

#print axioms bigPack2_tickG
#print axioms packRunR_G
#print axioms pal_in_peg_final11

end PalPeg.CloseoutPackRun5
