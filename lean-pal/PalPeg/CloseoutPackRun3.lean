import PalPeg.CloseoutPackRun2
import PalPeg.GalilTrailRad
import PalPeg.GalilLeafDp
import PalPeg.GalilDpSuffix
import PalPeg.GalilBranchInvariants2

/-!
# `CloseoutPackRun3`: enlarging the pack so the tick-local corners get their data

`CloseoutPackRun2.BigResid4` has twelve contracts.  Several of them are *not*
false and not even deep — they are simply **underdetermined by the source
state's pack**.  `CloseoutLPack4`'s own docstring says so for two of them:
`scanMargin` is "a property of the machine's stopping rule, not of the
invariant", and `shiftDoneScan` is "a statement about the round, not about the
exiting tick".  The cure is not a cleverer tick lemma; it is a **bigger pack**.

This file carries that out.

* §1 `Extra` — the data the tick-local corners lack, as a pack component:
  * `ready` — the search view is `SearchReady` (`GalilBranchInvariants2`), the
    DP-stage invariant that `CloseoutReadyStage.SearchReadyS` refines;
  * `failed` — in `scan`, the DP for the current radius has *failed*
    (`GalilLeafDp.StageFailed`), which is precisely the maximality `hmax` that
    `GalilLiveCentreFallback.leftmost_after_fallback` asks for at a fallback;
  * `cand` — in `shift`, the centre window carries a candidate period
    (`GalilDpSuffix.Candidate`), which is what `GalilPeriodCentre` /
    `reshift_palindrome` consume at the shift exit;
  * `scanMargin` / `rewindMargin` — the origin margins, i.e. the landing-side
    stage data (`Restarted`/`StageEntry`: at a restart `L = C = R` with
    `radius ≥ 0`, and `Live` is strict), which no source tick can see;
  * `scanAvail` — `canRight R` in `scan` **outside a replay**.  Inside a replay
    it is *not* an assumption: `GalilTrailRad.replayCan_of_pack` derives it from
    `FrontPack`, which `BigPack` already carries (`canR_of_bigPack2`).

* §2 `BigPack2 := BigPack ∧ Extra`, with the two NAMED transport obligations
  `H_extraEntry` (`Extra` at an `InvLPC` origin) and `H_extraTick` (`Extra`
  along one tick).  These replace *five* of the twelve contracts by two
  obligations about a single, much smaller predicate.

* §3 `BigResid5` — **nine** contracts, all stated over the enlarged pack
  `BigPack2`.  Compared with `BigResid4`: `rScanMargin`, `rRewindMargin` and
  `rScanCanR` are gone (they became `Extra` fields, the replay half of the last
  one *proved*), and the nine survivors now get `Extra` as extra input.

* §4 `lticks_of_big5`, `bigPack2_tick`, `bigPack2_of_invLPC`, `packRunR_of_big5`
  — the `CloseoutPackRun2` run machinery re-run over `BigPack2`.

* §5 `pal_in_peg_final10`.

## Honest status

Nothing here closes a contract by proving a hard theorem about the Galil
machine.  What it does is **re-cut** the residue: the nine surviving contracts
now have the search/stage/candidate data in hand (so `rMismatchMinv`,
`rShiftDoneScan` and `rShiftOneMinv` can be attacked by
`leftmost_after_fallback` / `GalilPeriodCentre` / `reshift_palindrome` rather
than being unprovable for lack of `hmax` resp. a period), and the three corners
that were *purely* about the landing state have moved into a single pack
component whose entry case is a restart (`Restarted`) and whose tick case is
mode-local.  One genuine closure happens: the replaying half of `rScanCanR`
(§1, `canR_of_bigPack2`).

**(NAMED) still open**, with their exact types below: `H_extraEntry`,
`H_extraTick`, and the nine fields of `BigResid5` (`rInitPack`, `rScanInvR`,
`rMismatchMinv`, `rShiftOneMinv`, `rShiftDoneScan`, `rChoosePack`,
`rRewindPairMinv`, `rReplayPack`, `rShiftNext`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun3

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilCheckpoints
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilInvPlus3
open PalPeg.GalilFinalAssembly PalPeg.GalilFinalAssembly2 PalPeg.GalilFinalAssembly4
open PalPeg.CloseoutLPack PalPeg.CloseoutLPack3 PalPeg.CloseoutLPack4 PalPeg.CloseoutLPack5
open PalPeg.CloseoutOracleI PalPeg.CloseoutOracleI2
open PalPeg.GalilChainCoupling PalPeg.GalilFrontMono
open PalPeg.CloseoutPackRun PalPeg.CloseoutPackRun2

/-! ## 1. `Extra`: the data a tick-local corner cannot see -/

section Extra
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) the enlargement of the pack.**  Six fields, each of them the
information that exactly one `BigResid4` corner was missing. -/
structure Extra (w : List (Fin 2)) (x : State GalilVM) : Prop where
  /-- The search view satisfies the DP-stage invariant. -/
  ready : PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get x.vm)
  /-- **`hmax`.**  In a scan the DP has ruled out every smaller period, i.e. the
  radius currently installed is maximal: exactly `GalilLeafDp.StageFailed`, the
  hypothesis of `GalilLiveCentreFallback.leftmost_after_fallback`. -/
  failed : x.ctl.mode = Mode.scan →
    PalPeg.GalilLeafDp.StageFailed (PofC centre place entry w) w x.vm
      (GalilScaffoldCounter.value x.vm.radius).toNat
  /-- **the shift's candidate period.**  In a shift the centre window carries a
  `GalilDpSuffix.Candidate`, which is what `GalilPeriodCentre` and
  `GalilScaffoldChainReadOrigin.reshift_palindrome` consume. -/
  cand : x.ctl.mode = Mode.shift →
    ∃ lower h, PalPeg.GalilDpSuffix.Candidate
      (GalilScaffoldPlace.stream ((PofC centre place entry w).place x.vm)) lower h
  /-- **the scan origin margin.**  Stage data: the landing of a restart has
  `L = C = R` with `radius ≥ 0`, and `Live` is strict, so the scan is at least
  two places away from the origin. -/
  scanMargin : x.ctl.mode = Mode.scan → ∀ r : ℕ,
    ScanInvariant w (position x.vm.center) r x.vm.left x.vm.right →
    r + 2 ≤ position x.vm.center
  /-- **the rewind origin margin.** -/
  rewindMargin : x.ctl.mode = Mode.rewind → 2 ≤ position x.vm.left
  /-- **`canRight R` in a scan outside a replay.**  The *replaying* half is not
  here: it is proved in `canR_of_bigPack2`. -/
  scanAvail : x.ctl.mode = Mode.scan → x.ctl.replaying = false →
    GalilScaffoldChainVerifier.canRight x.vm.right

/-- **The enlarged pack.** -/
structure BigPack2 (w : List (Fin 2)) (x : State GalilVM) : Prop where
  big : BigPack centre place entry q first w x
  extra : Extra centre place entry w x

/-- **(NAMED) `Extra` holds at an `InvLPC` origin.**  The entry case: the origin
of every cycle is a restart, where `Restarted` / `StageEntry` give the margins
and `readyPacedS_restarted` gives the search invariant. -/
def H_extraEntry (w : List (Fin 2)) : Prop :=
  ∀ (c : Control) (r : GalilVM), InvLPC w c r → Extra centre place entry w ⟨c, r⟩

/-- **(NAMED) `Extra` travels along one tick.**  Mode-local: each field only has
to be re-established in the mode its guard names. -/
def H_extraTick (w : List (Fin 2)) : Prop :=
  ∀ x y : State GalilVM, Extra centre place entry w x →
    Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y →
    Extra centre place entry w y

end Extra

/-! ### The one genuine closure: `canRight R` inside a replay -/

section CanR
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`rScanCanR` is no longer a contract.**  Splitting on `c.replaying`:
* `true` — `GalilTrailRad.replayCan_of_pack` turns the frontier budget already
  carried by `BigPack.front` into `canRight R`;
* `false` — `Extra.scanAvail`.
-/
theorem canR_of_bigPack2 {w : List (Fin 2)} {x : State GalilVM}
    (hb : BigPack centre place entry q first w x) (he : Extra centre place entry w x)
    (hm : x.ctl.mode = Mode.scan) : GalilScaffoldChainVerifier.canRight x.vm.right := by
  cases hrep : x.ctl.replaying with
  | true => exact PalPeg.GalilTrailRad.replayCan_of_pack hb.front hrep
  | false => exact he.scanAvail hm hrep

end CanR

/-! ## 3. `BigResid5`: nine contracts over the enlarged pack -/

section Resid5
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) the residual over the enlarged pack — nine fields.**
`CloseoutPackRun2.BigResid4` minus `rScanMargin`, `rRewindMargin` and
`rScanCanR`, with every survivor handed `Extra` as well. -/
structure BigResid5 (w : List (Fin 2)) : Prop where
  rInitPack : ∀ x : State GalilVM, BigPack2 centre place entry q first w x →
    x.ctl.mode = Mode.init → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).init x.vm t →
    LPack w {x.ctl with mode := Mode.scan, output := true} t
  rScanInvR : ∀ x : State GalilVM, BigPack2 centre place entry q first w x →
    x.ctl.mode = Mode.scan →
    ∃ r, ScanInvariant w (position x.vm.center) r x.vm.left x.vm.right
  rMismatchMinv : ∀ x : State GalilVM, BigPack2 centre place entry q first w x →
    x.ctl.mode = Mode.scan → ∀ s'' : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).compare x.vm s'' →
    MInv w {x.ctl with clock := 2048} s''
  rShiftOneMinv : ∀ x : State GalilVM, BigPack2 centre place entry q first w x →
    x.ctl.mode = Mode.shift → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).shiftOne x.vm t → MInv w x.ctl t
  rShiftDoneScan : ∀ x : State GalilVM, BigPack2 centre place entry q first w x →
    x.ctl.mode = Mode.shift →
    ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos x.vm →
    ∃ r, ScanInvariant w (position x.vm.center) r x.vm.left x.vm.right
  rShiftDoneMinv : ∀ x : State GalilVM, BigPack2 centre place entry q first w x →
    x.ctl.mode = Mode.shift →
    ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos x.vm →
    MInv w x.ctl x.vm
  rChoosePack : ∀ x : State GalilVM, BigPack2 centre place entry q first w x →
    x.ctl.mode = Mode.choose → x.ctl.odd = true → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).choose x.vm t →
    (GalilScaffoldInputTrace.Represents t.left.head w ∧ t.left.head.focus ≠ none) ∧
      MInv w {x.ctl with mode := Mode.rewind, pair := false} t
  rRewindPairMinv : ∀ x : State GalilVM, BigPack2 centre place entry q first w x →
    x.ctl.mode = Mode.rewind → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).rewindPair x.vm t →
    MInv w {x.ctl with pair := false} t
  rReplayPack : ∀ x : State GalilVM, BigPack2 centre place entry q first w x →
    x.ctl.mode = Mode.replayStart → ∀ (t : GalilVM) (o : Bool),
    (galilFrameS (PofC centre place entry w) q first).replayStart x.vm t →
    LPack w {x.ctl with mode := Mode.scan, clock := 2048, output := o, replaying := (galilFrameS (PofC centre place entry w) q first).replayPos t} t
  rShiftNext : ∀ x y : State GalilVM, BigPack2 centre place entry q first w x →
    Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y →
    SoundScanNR w y → ShiftLocal centre place entry q first w y

/-- **The twelve `LTickLeaves` corners from the nine contracts plus `Extra`.**
`scanLeft` and `rewindLeft` come from the margins by `left_pos_of_two`,
`scanCanR` from `canR_of_bigPack2`, and the two mismatch entries from the single
`rMismatchMinv` by `minv_of_mismatch` exactly as in `bigResid'_of_big4`. -/
theorem lticks_of_big5 {w : List (Fin 2)} (hr : BigResid5 centre place entry q first w)
    {x : State GalilVM} (hx : BigPack2 centre place entry q first w x) :
    LTickLeavesG centre place entry q first w x.ctl x.vm where
  initPackG := fun hm t ht => lpackG_of_lpack (hr.rInitPack x hx hm t ht)
  scanLeft := fun hm => by
    obtain ⟨r, hi⟩ := hr.rScanInvR x hx hm
    exact left_pos_of_two (margin_of_scanInv hi (hx.extra.scanMargin hm r hi))
  scanInvR := hr.rScanInvR x hx
  scanCanR := fun hm => canR_of_bigPack2 centre place entry q first hx.big hx.extra hm
  shiftDoneScan := hr.rShiftDoneScan x hx
  shiftDoneMinv := hr.rShiftDoneMinv x hx
  choosePackL := fun hm ho t ht => (hr.rChoosePack x hx hm ho t ht).1
  rewindLeft := fun hm => left_pos_of_two (hx.extra.rewindMargin hm)
  replayPackG := fun hm t o ht => lpackG_of_lpack (hr.rReplayPack x hx hm t o ht)

end Resid5

/-! ## 4. The run machinery over `BigPack2` -/

section Run2
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **One tick of the enlarged pack.**  `CloseoutPackRun2.bigPack_tick'` with the
`Extra` component transported by `H_extraTick`. -/
theorem bigPack2_tick {w : List (Fin 2)} (hr : BigResid5 centre place entry q first w)
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
    (lticks_of_big5 centre place entry q first hr hx) h

/-- **The enlarged pack at an `InvLPC` origin.** -/
theorem bigPack2_of_invLPC {w : List (Fin 2)}
    (hee : H_extraEntry centre place entry w) {c : Control} {r : GalilVM}
    (hIC : InvLPC w c r) (hI : IPack centre place entry q first w ⟨c, r⟩) :
    BigPack2 centre place entry q first w ⟨c, r⟩ :=
  ⟨bigPack_of_invLPC centre place entry q first hIC hI, hee c r hIC⟩

/-- **`Extra` travels along a bare `Steps` run.**  Unlike `BigPack`, the
enlarged component is self-stable, so no reachability bookkeeping is needed. -/
theorem extra_steps {w : List (Fin 2)} (het : H_extraTick centre place entry q first w)
    {n : ℕ} {x y : State GalilVM} (he : Extra centre place entry w x)
    (h : Steps (galilFrameS (PofC centre place entry w) q first) 2048 n x y) :
    Extra centre place entry w y := by
  induction h with
  | zero z => exact he
  | @succ m a b z h hr ih => exact ih (het a b he h)

/-- **`PackRunR` from the nine contracts plus the two `Extra` obligations.**
`CloseoutPackRun2.packRunR_of_bigResid'` re-run with `BigPack2` in place of
`BigPack`: `AuxPack` still travels by `auxPack_steps`, `CentreLive` is still
free from `hlive_of_invLPC`, and `Extra` travels by `extra_steps`. -/
theorem packRunR_of_big5 {w : List (Fin 2)}
    (hr : BigResid5 centre place entry q first w)
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
      exact bigPack2_tick centre place entry q first hr het (ih (by omega))
        (htr.tick n (by omega)) (htr.good (n+1) hi)
        (hlv0 (j + (n+1)) (g (n+1)) (hreach (n+1) hi))
  exact ⟨g, hg0, hgk, htr, fun i hi => (hbig i hi).big.ipack⟩

end Run2

/-! ## 5. `pal_in_peg_final9` over the enlarged pack -/

/-- **`CloseoutPackRun2.pal_in_peg_final9` with `BigResid4` replaced by
`BigResid5` + `H_extraEntry` + `H_extraTick`.**  Twelve contracts over the old
pack become nine over the enlarged one, plus two obligations about `Extra`
alone; one contract (`rScanCanR`) is discharged outright in its replaying half
and reduced to `Extra.scanAvail` otherwise. -/
theorem pal_in_peg_final10 (entry q : ℕ) (first : Fin 9)
    (hr : ∀ w : List (Fin 2), BigResid5 centreC placeC entry q first w)
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
      (packRunR_of_big5 centreC placeC entry q first (hr w) (hee w) (het w)) (hsl w) (hsc w)
      (hor w hw))
    hC

#print axioms canR_of_bigPack2
#print axioms lticks_of_big5
#print axioms bigPack2_tick
#print axioms bigPack2_of_invLPC
#print axioms extra_steps
#print axioms packRunR_of_big5
#print axioms pal_in_peg_final10

end PalPeg.CloseoutPackRun3
