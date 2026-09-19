import PalPeg.WindowTick
import PalPeg.CloseoutPackRun40
import PalPeg.ShiftEntryFromLanding
import PalPeg.CloseoutReplayCanRight
import PalPeg.CloseoutFrontExtra
import PalPeg.CloseoutMarksFree
import PalPeg.CloseoutShiftFinal

set_option maxHeartbeats 1000000

/-!
# `WindowRunPack`: the run-level pack that discharges `ShiftPal`

The residue of `obligation_shiftPalResiduesAlongRun` (the birth-anchored window at a
mismatched comparison whose landing passes `shiftGuardVM`) is read off a pack that is
carried along runs from `InvLPC` origins and along the boot trace:

* `window : ChainWindowRun` — the birth-anchored window (`WindowRun`);
* `coupled : Coupled'` — the chain–scan coupling with the constant-5 round bound
  (`CloseoutPackRun40`), which gives `4h ≤ radius` at a guarded shift entry;
* `centreRep` at scan/shift, `radiusScan`/`radiusShift` — the centre head and the radius
  counter as `RadiusRep` with `position right = position center + R`.

`shiftPal_of_windowRunPack` is the consumer: `ShiftPal` at any `ScanNR` state carrying
`LPackM` (the scan geometry), the pack, and `canRight right`.  It replaces the
`hShiftPalAlongRun` hypothesis of `CloseoutMarksPack.packRunR_MW_marksFree` (the pack rides
inside `IPackMW.win`) and the trace-form `obligation_shiftPalAlongTrace`.
-/

namespace PalPeg.WindowPack

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilReplayGeneral2 PalPeg.GalilBranchInvariants PalPeg.ShiftPalAlongTrace
open PalPeg.WindowInv PalPeg.WindowRun PalPeg.WindowTick PalPeg.GalilRunSkeleton
open PalPeg.GalilChainCoupling PalPeg.CloseoutPackRun40
open PalPeg.GalilInvPlus2 (CentreRep centreRep_congr InvLPC)
open PalPeg.CloseoutPackRun2 (AuxPack)
open PalPeg.CloseoutPackRun10 (LPackM)
open PalPeg.CloseoutPackRun23 (LPackM2)
open PalPeg.CloseoutPackRun26 (ScanNR)
open PalPeg.CloseoutPackRun29 (ShiftPal)
open PalPeg.GalilFrontMono (FrontPack)
open PalPeg.GalilFinalAssembly (boot)

/-! ## 1. The pack -/

/-- **The run-level window pack.** -/
structure WindowRunPack (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  window : ChainWindowRun w c s
  coupled : Coupled' c s
  centreRep : c.mode = Mode.scan ∨ c.mode = Mode.shift → CentreRep w s
  radiusScan : c.mode = Mode.scan →
    ∃ R : ℕ, RadiusRep s.radius R ∧ position s.right = position s.center + R
  radiusShift : c.mode = Mode.shift →
    ∃ (rem R : ℕ), s.remaining = ofNat rem ∧ RadiusRep s.radius R ∧ rem ≤ R ∧
      position s.right = position s.center + R

/-- At the boot state (mode `init`, chain idle) every field is idle or vacuous. -/
theorem windowRunPack_boot (w : List (Fin 2)) : WindowRunPack w (boot w).ctl (boot w).vm where
  window := chainWindowRun_of_idle (PalPeg.CloseoutShiftFinal.boot_chain_idle w)
  coupled := coupled'_of_idle (PalPeg.CloseoutShiftFinal.boot_chain_idle w)
  centreRep := fun h => by rcases h with h | h <;> cases h
  radiusScan := fun h => by cases h
  radiusShift := fun h => by cases h

/-- At an `InvLPC` origin (a restarted scan state): idle chain, centre head from `InvLPC`
itself, radius from `EntryCounters`. -/
theorem windowRunPack_of_invLPC {w : List (Fin 2)} {c : Control} {r : GalilVM}
    (hIC : InvLPC w c r) : WindowRunPack w c r := by
  have hmode : c.mode = Mode.scan := (PalPeg.GalilOracleLocal.invS_mode hIC.1.1.1.1).1
  obtain ⟨Rad, hscan, hRR, -, -⟩ := PalPeg.CloseoutMarksFree.entryCounters_of_invLPC hIC
  have hidle : r.chain = ChainVM.idle := by
    rcases hIC.1.1.1.1 with hI | ⟨k, hI⟩
    · obtain ⟨Rad', last, hR⟩ := hI.rest
      exact hR.1
    · exact hI.chainIdle
  exact
    { window := chainWindowRun_of_idle hidle
      coupled := coupled'_of_idle hidle
      centreRep := fun _ => hIC.2
      radiusScan := fun _ => ⟨Rad, hRR, hscan.rightPos⟩
      radiusShift := fun hs => absurd (hmode.symm.trans hs) (by decide) }

#print axioms windowRunPack_boot
#print axioms windowRunPack_of_invLPC

/-! ## 2. The size bound at a guarded shift entry -/

/-- A fresh watch control at phase `4` has consumed at least four semiperiods. -/
theorem four_of_freshC {k : GalilScaffoldChainConsume.State} (hf : FreshC k) (hph : k.phase = 4) :
    4 * ((k.period.left.length + k.period.right.length : ℕ) : ℤ) ≤ value k.distance := by
  have hv : (k.phase.val : ℤ) = 4 := by rw [hph]; rfl
  cases hfw : k.forward with
  | true =>
    obtain ⟨h1, h2⟩ := hf.1 hfw
    rw [hv] at h2
    push_cast at h2 ⊢
    omega
  | false =>
    obtain ⟨h1, h2⟩ := hf.2 hfw
    rw [hv] at h2
    push_cast at h2 ⊢
    omega

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`4h ≤ radius` at a guarded shift entry**, both halves of `WatchOK`: the fresh half by
phase `4` (`four_of_freshC`), the post-shift half by `four_of_other'`. -/
theorem four_of_guard {w : List (Fin 2)} {x : State GalilVM} {s'' : GalilVM}
    {wch : GalilScaffoldChainWatch.State} (hx : Coupled' x.ctl x.vm) (hs : ScanNR x)
    (hcmp : (galilFrameS (PofC centre place entry w) q first).compare x.vm s'')
    (hmt : ¬ (galilFrameS (PofC centre place entry w) q first).matched s'')
    (hg : shiftGuardVM s'') (hch : s''.chain = ChainVM.watch wch) :
    4 * (periodLength wch : ℤ) ≤ value x.vm.radius := by
  obtain ⟨-, -, -, -, hmis⟩ :=
    compare'_inv (onLetterVM w) leftFirstVM centre place entry q first hx hs.1 hcmp
  obtain ⟨-, -, hsum, hwok⟩ := hmis hmt
  obtain ⟨w1, hw1, hz, hph, hbr, -, -⟩ := id hg
  have hwe : w1 = wch := by rw [hw1] at hch; exact ChainVM.watch.inj hch
  subst hwe
  rw [hw1] at hsum
  have hd : value w1.machine.control.distance + value w1.lag = value x.vm.radius := hsum hbr
  rw [value_zero_of_zero hz] at hd
  rcases hwok w1 hw1 hbr with ⟨-, hf⟩ | hO
  · have h4 := four_of_freshC hf hph
    unfold periodLength
    omega
  · have h4 := four_of_other' centre place entry q first hx hs hcmp hmt hg hw1 hO
    omega

#print axioms four_of_guard

/-! ## 3. `ShiftPal` from the pack -/

/-- At a mismatched comparison whose landing passes the guard, the source chain is a
watch, and the landing's watch is one `Internal` step from it (a fresh watch born by
`backDone` has phase `0`, not `4`). -/
theorem source_watch_of_guard {P : Shared} {q' : ℕ} {first' : Fin 9} {s s' : GalilVM}
    (hcmp : compareFound P q' first' s s')
    (hmt : ¬ (galilFrameS P q' first').matched s') (hg : shiftGuardVM s') :
    ∃ w₀ : GalilScaffoldChainWatch.State, s.chain = ChainVM.watch w₀ ∧
      ∀ wch, s'.chain = ChainVM.watch wch → GalilScaffoldChainWatch.Internal w₀ wch := by
  obtain ⟨vs, vq, a, hvl, hvr, hmatch, -, hchainAt, hs'⟩ := hcmp
  obtain ⟨hl', hr', hch', -, -⟩ := compare_target_heads hs'
  obtain ⟨wch, hw, -, hph, -, -, -⟩ := hg
  have ha : a = false := by
    cases a with
    | false => rfl
    | true =>
      exfalso
      apply hmt
      have hm := hmatch.1 rfl
      show read s'.left = read s'.right
      rw [hl', hr']
      exact hm
  subst ha
  rw [hch'] at hw
  rcases hchainAt with ⟨-, y, hstep, hy⟩ | ⟨-, -, hidle'⟩ | ⟨-, -, hstart⟩
  · simp only [Bool.false_eq_true, ↓reduceIte] at hy
    rw [hy] at hw
    subst hw
    generalize hx' : s.chain = x0 at hstep
    cases hstep with
    | backDone v hh lag margin ver hf =>
      exfalso
      have h0 : (watchControl v).phase = 4 := hph
      simp [watchControl] at h0
    | watchStep w₀ w' ht =>
      refine ⟨w₀, by first | rfl | exact hx' | exact hx'.symm, fun wch' hwch' => ?_⟩
      rw [hch', hy] at hwch'
      have he := ChainVM.watch.inj hwch'
      subst he
      exact ht
  · rw [hidle'] at hw
    cases hw
  · simp only [Bool.false_eq_true, ↓reduceIte] at hstart
    rw [hstart] at hw
    unfold chainStart at hw
    cases hw

/-- **`ShiftPal` at a `ScanNR` state carrying the pack.**  The residue of the former
`obligation_shiftPalResiduesAlongRun`, read off `ChainWindowRun` (window, birth centre,
`k`), `LPackM.scanGeom` (the scan invariant, `R = position right − position center`),
and `four_of_guard` (`2h ≤ R`); then `freshShiftLedger_of_chainW_scan` and
`shiftPal_of_freshShiftLedger`. -/
theorem shiftPal_of_windowRunPack {w : List (Fin 2)} {x : State GalilVM}
    (hpack : LPackM w x.ctl x.vm) (hx : WindowRunPack w x.ctl x.vm)
    (hcan : canRight x.vm.right) (hs : ScanNR x) :
    ShiftPal centre place entry q first w x.vm := by
  obtain ⟨c, s⟩ := x
  refine shiftPal_of_freshShiftLedger centre place entry q first hcan (fun s' hcmp hmis => ?_)
  intro hguard
  obtain ⟨w₀, hw₀, hint⟩ := source_watch_of_guard hcmp hmis hguard
  obtain ⟨cen₀, cc, hcc, hinv, hk, -, -⟩ := hx.window
  rw [hw₀] at hinv
  obtain ⟨b, xs, hW⟩ := hinv
  obtain ⟨k, hk⟩ := (hk w₀ hw₀).2 (by rw [hs.1]; decide)
  have hh : periodLength w₀ = xs.length + 1 := periodLength_of_coreP hW.2.2
  obtain ⟨rad, hscan⟩ := hpack.scanGeom hs.1 hs.2
  have hpos : position s.right = position s.center + rad := hscan.rightPos
  obtain ⟨R', hRR, hR'⟩ := hx.radiusScan hs.1
  obtain ⟨wch, hwch, -, -, -, -, -⟩ := id hguard
  have hW' : WatchWindow w cen₀ (position s.right) cc b xs (ChainVM.watch wch) :=
    watchWindow_step hW (hint wch hwch)
  have hh' : periodLength wch = xs.length + 1 := periodLength_of_coreP hW'.2.2
  have hfour := four_of_guard centre place entry q first (x := ⟨c, s⟩) hx.coupled hs hcmp hmis
    hguard hwch
  have hfour' : 4 * ((xs.length + 1 : ℕ) : ℤ) ≤ (R' : ℤ) := by
    have h1 : value s.radius = (R' : ℤ) := hRR.2
    rw [← hh', ← h1]; exact hfour
  have hR'' : position s.right = position s.center + R' := hR'
  have hsize : 2 * (xs.length + 1) ≤ rad := by omega
  have hW2 : WatchWindow w cen₀ (position s.center + rad) cc b xs s.chain := by
    rw [hw₀, ← hpos]; exact hW
  exact PalPeg.ShiftEntryFromLanding.freshShiftLedger_of_chainW_scan centre place entry q first
    hW2 (by rw [hk, hh]) hscan hcan hcc hsize hcmp hmis hguard

#print axioms shiftPal_of_windowRunPack

/-! ## 4. One tick -/

/-- Both comparison outcomes set `radius := inc radius`. -/
theorem compare_target_radius {s s' : GalilVM} {vs : ScanVM} {vq : SearchVM} {a born : Bool}
    (hs' : s' = afterBirth born (if a then afterCompare s vs vq else afterMismatch s vs vq)) :
    s'.radius = inc s.radius := by
  subst hs'
  cases born <;> cases a <;> rfl

theorem radiusRep_dec {c : Counter} {R : ℕ} (h : RadiusRep c (R + 1)) : RadiusRep (dec c) R := by
  unfold RadiusRep at h ⊢
  refine ⟨dec_canonical c h.1, ?_⟩
  rw [dec_value, h.2]
  push_cast
  ring

theorem centreRep_right {w : List (Fin 2)} {s t : GalilVM} (hc : CentreRep w s)
    (hcan : canRight s.center) (ht : t.center = right s.center) : CentreRep w t := by
  unfold CentreRep at hc ⊢
  rw [ht]
  exact ⟨right_word _ w hc.1 hcan, right_present _ w hc.1 hc.2 hcan⟩

/-- The right head at a scan state, replaying or not, from `LPackM`/`LPackM2`. -/
theorem rightHead_of_packs {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hpack : LPackM w c s) (hm2 : LPackM2 w c s) (hm : c.mode = Mode.scan) :
    GalilScaffoldInputTrace.Represents s.right.head w ∧ s.right.head.focus ≠ none := by
  cases hr : c.replaying with
  | false => exact PalPeg.CloseoutFrontExtra.rrep_of_lpackM hpack hm hr
  | true =>
    obtain ⟨rad, hsi⟩ := hm2.scanGeomR hm hr
    exact ⟨hsi.rightRep, hsi.rightPresent⟩

/-- The three ledger fields at a state that is neither scan nor shift. -/
theorem ledger_vacuous {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hns : c.mode ≠ Mode.scan) (hnsh : c.mode ≠ Mode.shift) :
    (c.mode = Mode.scan ∨ c.mode = Mode.shift → CentreRep w s) ∧
    (c.mode = Mode.scan →
      ∃ R : ℕ, RadiusRep s.radius R ∧ position s.right = position s.center + R) ∧
    (c.mode = Mode.shift →
      ∃ (rem R : ℕ), s.remaining = ofNat rem ∧ RadiusRep s.radius R ∧ rem ≤ R ∧
        position s.right = position s.center + R) :=
  ⟨fun h => by rcases h with h | h; exact absurd h hns; exact absurd h hnsh,
   fun h => absurd h hns, fun h => absurd h hnsh⟩

/-- **The ledger fields (`centreRep`／`radiusScan`／`radiusShift`) in one tick.** -/
theorem ledger_tick {w : List (Fin 2)} {x y : State GalilVM}
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hnotInit : x.ctl.mode ≠ Mode.init)
    (hfront : FrontPack x.ctl x.vm)
    (hcoupled : Coupled' x.ctl x.vm)
    (hcopy : x.ctl.mode = Mode.shift → CopyIdle x.vm)
    (hright : x.ctl.mode = Mode.scan →
      GalilScaffoldInputTrace.Represents x.vm.right.head w ∧ x.vm.right.head.focus ≠ none)
    (hcenRS : x.ctl.mode = Mode.replayStart → CentreRep w x.vm)
    (hcen : x.ctl.mode = Mode.scan ∨ x.ctl.mode = Mode.shift → CentreRep w x.vm)
    (hradS : x.ctl.mode = Mode.scan →
      ∃ R : ℕ, RadiusRep x.vm.radius R ∧ position x.vm.right = position x.vm.center + R)
    (hradSh : x.ctl.mode = Mode.shift →
      ∃ (rem R : ℕ), x.vm.remaining = ofNat rem ∧ RadiusRep x.vm.radius R ∧ rem ≤ R ∧
        position x.vm.right = position x.vm.center + R) :
    (y.ctl.mode = Mode.scan ∨ y.ctl.mode = Mode.shift → CentreRep w y.vm) ∧
    (y.ctl.mode = Mode.scan →
      ∃ R : ℕ, RadiusRep y.vm.radius R ∧ position y.vm.right = position y.vm.center + R) ∧
    (y.ctl.mode = Mode.shift →
      ∃ (rem R : ℕ), y.vm.remaining = ofNat rem ∧ RadiusRep y.vm.radius R ∧ rem ≤ R ∧
        position y.vm.right = position y.vm.center + R) := by
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  cases h with
  | init c s t hm hi => exact absurd hm hnotInit
  | scan_wait c s t hm hav hb =>
    obtain ⟨-, hr, -, hcen', -, hrad, -, -, -, -, -, -⟩ :=
      backgroundS_fields (PofC centre place entry w) q first hb
    refine ⟨fun _ => centreRep_congr hcen' (hcen (Or.inl hm)), fun _ => ?_,
      fun hs => absurd (hm.symm.trans hs) (by decide)⟩
    obtain ⟨R, hRR, hR⟩ := hradS hm
    exact ⟨R, by rw [hrad]; exact hRR, by rw [hr, hcen']; exact hR⟩
  | scan_count c s t hm hav hc hb =>
    obtain ⟨-, hr, -, hcen', -, hrad, -, -, -, -, -, -⟩ :=
      backgroundS_fields (PofC centre place entry w) q first hb
    refine ⟨fun _ => centreRep_congr hcen' (hcen (Or.inl hm)), fun _ => ?_,
      fun hs => absurd (hm.symm.trans hs) (by decide)⟩
    obtain ⟨R, hRR, hR⟩ := hradS hm
    exact ⟨R, by rw [hrad]; exact hRR, by rw [hr, hcen']; exact hR⟩
  | scan_match c s s' t o hm hav hc hcmp hmt hpl ho =>
    have hcmp' : compareFound (PofC centre place entry w) q first s s' := hcmp
    obtain ⟨vs, vq, a, -, hvr, -, -, -, hs'⟩ := hcmp'
    obtain ⟨-, hr', -, hcen', -⟩ := compare_target_heads hs'
    have hrad' : s'.radius = inc s.radius := compare_target_radius hs'
    have hpl' : t = (if c.replaying then {s' with replay := dec s'.replay} else s') := hpl
    have htc : t.center = s'.center := by rw [hpl']; split <;> rfl
    have htr : t.right = s'.right := by rw [hpl']; split <;> rfl
    have htrad : t.radius = s'.radius := by rw [hpl']; split <;> rfl
    obtain ⟨hrep, hpres⟩ := hright hm
    have hcan : canRight s.right := by
      rcases hav with hrp | hav
      · exact PalPeg.CloseoutReplayCanRight.canRight_of_frontPack hfront hrp
      · exact hav
    have hl0 : 0 < s.right.head.left.length := (represented_position _ w hrep hpres).1
    have hposR : position t.right = position s.right + 1 := by
      rw [htr, hr', hvr, right_position _ hcan hl0]
    refine ⟨fun _ => centreRep_congr (htc.trans hcen') (hcen (Or.inl hm)), fun _ => ?_,
      fun hs => absurd (hm.symm.trans hs) (by decide)⟩
    obtain ⟨R, hRR, hR⟩ := hradS hm
    refine ⟨R + 1, ?_, ?_⟩
    · rw [htrad, hrad']; exact radius_rep_inc hRR
    · rw [hposR, htc, hcen', hR]; ring
  | scan_shift c s s' t hm hav hc hcmp hmt hr hg hb =>
    have hcmp' : compareFound (PofC centre place entry w) q first s s' := hcmp
    obtain ⟨vs, vq, a, -, hvr, -, -, -, hs'⟩ := hcmp'
    obtain ⟨-, hr', -, hcen', -⟩ := compare_target_heads hs'
    have hrad' : s'.radius = inc s.radius := compare_target_radius hs'
    have hg' : shiftGuardVM s' := hg
    have hb' : beginShiftVM' s' t := hb
    obtain ⟨wsh, hwsh, ht⟩ := hb'
    have htc : t.center = s'.center := by rw [ht]
    have htr : t.right = s'.right := by rw [ht]
    have htrad : t.radius = s'.radius := by rw [ht]
    have htrem : t.remaining = ofNat (periodLength wsh) := by rw [ht]
    obtain ⟨hrep, hpres⟩ := hright hm
    have hcan : canRight s.right := by
      rcases hav with hrp | hav
      · exact PalPeg.CloseoutReplayCanRight.canRight_of_frontPack hfront hrp
      · exact hav
    have hl0 : 0 < s.right.head.left.length := (represented_position _ w hrep hpres).1
    have hposR : position t.right = position s.right + 1 := by
      rw [htr, hr', hvr, right_position _ hcan hl0]
    have hfour := four_of_guard centre place entry q first (x := ⟨c, s⟩) hcoupled ⟨hm, hr⟩
      hcmp hmt hg' hwsh
    obtain ⟨R, hRR, hR⟩ := hradS hm
    rw [hRR.2] at hfour
    refine ⟨fun _ => centreRep_congr (htc.trans hcen') (hcen (Or.inl hm)), ?_, fun _ => ?_⟩
    · intro hs; cases hs
    refine ⟨periodLength wsh, R + 1, htrem, ?_, by omega, ?_⟩
    · rw [htrad, hrad']; exact radius_rep_inc hRR
    · rw [hposR, htc, hcen', hR]; ring
  | scan_fallback c s s' t hm hav hc hcmp hmt hg hr hb =>
    exact ledger_vacuous (fun h => by first | cases h | (rw [hm] at h; cases h))
      (fun h => by first | cases h | (rw [hm] at h; cases h))
  | shift_one c s t hm hp hso =>
    have hso' : shiftLens.rel (shiftFrame (fun _ => True) (fun _ => True)).shiftOne s t := hso
    obtain ⟨⟨hcanC, -, -, wsh, hwsh, hget⟩, hset⟩ := hso'
    have htcenter : t.center = right s.center :=
      congrArg (fun v : ShiftVM => v.shift.center) hget
    have htrem : t.remaining = dec s.remaining :=
      congrArg (fun v : ShiftVM => v.shift.remaining) hget
    have htrad : t.radius = dec s.radius :=
      congrArg (fun v : ShiftVM => v.shift.radius) hget
    have htright : t.right = s.right := by rw [hset]; rfl
    have hcanC' : canRight s.center := hcanC
    have hc := hcen (Or.inr hm)
    have hl0 : 0 < s.center.head.left.length := (represented_position _ w hc.1 hc.2).1
    have hposC : position t.center = position s.center + 1 := by
      rw [htcenter, right_position s.center hcanC' hl0]
    obtain ⟨rem, R, hremEq, hRR, hle, hR⟩ := hradSh hm
    have hpos : positive s.remaining = true := by
      rcases hp with hp | hp
      · exact hp
      · exact absurd hp (hcopy hm)
    obtain ⟨rem', hrem'⟩ : ∃ rem', rem = rem' + 1 := by
      cases rem with
      | zero => rw [hremEq] at hpos; exact absurd hpos (by decide)
      | succ n => exact ⟨n, rfl⟩
    subst hrem'
    obtain ⟨R', hR'⟩ : ∃ R', R = R' + 1 := ⟨R - 1, by omega⟩
    subst hR'
    refine ⟨fun _ => centreRep_right hc hcanC' htcenter,
      fun hs => absurd (hm.symm.trans hs) (by decide), fun _ => ?_⟩
    refine ⟨rem', R', ?_, ?_, by omega, ?_⟩
    · rw [htrem, hremEq, dec_ofNat_succ]
    · rw [htrad]; exact radiusRep_dec hRR
    · rw [htright, hposC, hR]; ring
  | shift_done c s o hm hp ho =>
    obtain ⟨rem, R, hremEq, hRR, hle, hR⟩ := hradSh hm
    exact ⟨fun _ => hcen (Or.inr hm), fun _ => ⟨R, hRR, hR⟩, fun hs => by cases hs⟩
  | copy_one c s t hm hp hc =>
    exact ledger_vacuous (fun h => by first | cases h | (rw [hm] at h; cases h))
      (fun h => by first | cases h | (rw [hm] at h; cases h))
  | copy_done c s t hm hp hc =>
    exact ledger_vacuous (fun h => by first | cases h | (rw [hm] at h; cases h))
      (fun h => by first | cases h | (rw [hm] at h; cases h))
  | home_start c s t hm hl hc =>
    exact ledger_vacuous (fun h => by first | cases h | (rw [hm] at h; cases h))
      (fun h => by first | cases h | (rw [hm] at h; cases h))
  | home_step c s t hm hl hc =>
    exact ledger_vacuous (fun h => by first | cases h | (rw [hm] at h; cases h))
      (fun h => by first | cases h | (rw [hm] at h; cases h))
  | fpp_slice c s t hm hc =>
    exact ledger_vacuous (fun h => by first | cases h | (rw [hm] at h; cases h))
      (fun h => by first | cases h | (rw [hm] at h; cases h))
  | fpp_done c s t hm hc =>
    exact ledger_vacuous (fun h => by first | cases h | (rw [hm] at h; cases h))
      (fun h => by first | cases h | (rw [hm] at h; cases h))
  | markEnd_found c s t hm he hc =>
    exact ledger_vacuous (fun h => by first | cases h | (rw [hm] at h; cases h))
      (fun h => by first | cases h | (rw [hm] at h; cases h))
  | markEnd_step c s t hm he hc =>
    exact ledger_vacuous (fun h => by first | cases h | (rw [hm] at h; cases h))
      (fun h => by first | cases h | (rw [hm] at h; cases h))
  | choose_select c s t hm ho hs hc =>
    exact ledger_vacuous (fun h => by first | cases h | (rw [hm] at h; cases h))
      (fun h => by first | cases h | (rw [hm] at h; cases h))
  | choose_step c s t hm hs hc =>
    exact ledger_vacuous (fun h => by first | cases h | (rw [hm] at h; cases h))
      (fun h => by first | cases h | (rw [hm] at h; cases h))
  | rewind_done c s t hm hf hc =>
    exact ledger_vacuous (fun h => by first | cases h | (rw [hm] at h; cases h))
      (fun h => by first | cases h | (rw [hm] at h; cases h))
  | rewind_one c s t hm hf hp hc =>
    exact ledger_vacuous (fun h => by first | cases h | (rw [hm] at h; cases h))
      (fun h => by first | cases h | (rw [hm] at h; cases h))
  | rewind_pair c s t hm hf hp hc =>
    exact ledger_vacuous (fun h => by first | cases h | (rw [hm] at h; cases h))
      (fun h => by first | cases h | (rw [hm] at h; cases h))
  | replayStart c s t o hm hrs ho ho' =>
    have hrs' : replayStartVM entry s t := hrs
    obtain ⟨-, hrt, -, hct, hradt, -, -, -, -, -, -, -, -, -, -⟩ := hrs'
    refine ⟨fun _ => centreRep_congr hct (hcenRS hm), fun _ => ?_, ?_⟩
    · refine ⟨0, ⟨?_, ?_⟩, ?_⟩
      · rw [hradt]; exact Or.inl rfl
      · rw [hradt]; rfl
      · rw [hrt, hct, Nat.add_zero]
    · intro hs; cases hs
  | restart c s t hm hrs =>
    have hrs' : restartVM entry s t := hrs
    obtain ⟨wb, -, -, -, -, ht⟩ := hrs'
    refine ⟨fun _ => centreRep_congr (by rw [ht]) (hcen (Or.inl hm)), fun _ => ?_,
      fun hs => absurd (hm.symm.trans hs) (by decide)⟩
    obtain ⟨R, hRR, hR⟩ := hradS hm
    exact ⟨R, by rw [ht]; exact hRR, by rw [ht]; exact hR⟩

#print axioms ledger_tick

/-- **`WindowRunPack` in one tick**, from the source's `LPackM`／`LPackM2`／`AuxPack`. -/
theorem windowRunPack_tick {w : List (Fin 2)} {x y : State GalilVM}
    (hP : Decodes (PofC centre place entry w))
    (hpack : LPackM w x.ctl x.vm) (hm2 : LPackM2 w x.ctl x.vm) (haux : AuxPack x.ctl x.vm)
    (hx : WindowRunPack w x.ctl x.vm)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y) :
    WindowRunPack w y.ctl y.vm := by
  have hright := rightHead_of_packs hpack hm2
  obtain ⟨hcen', hradS', hradSh'⟩ := ledger_tick centre place entry q first h
    haux.front.notInit haux.front hx.coupled (fun hm => haux.copyP (by rw [hm]; decide)) hright
    (fun hm => hm2.centreRep (Or.inr hm)) hx.centreRep hx.radiusScan hx.radiusShift
  have hwin : ChainWindowRun w y.ctl y.vm :=
    chainWindowRun_tick centre place entry q first hP h hx.window haux hx.centreRep
      (fun hm => (hright hm).1) (fun hm => (hright hm).2) haux.front hx.radiusScan
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  exact
    { window := hwin
      coupled := coupled'_tick (onLetterVM w) leftFirstVM centre place entry q first 2048
        hx.coupled h
      centreRep := hcen'
      radiusScan := hradS'
      radiusShift := hradSh' }

#print axioms windowRunPack_tick

end

end PalPeg.WindowPack
