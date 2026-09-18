import PalPeg.CloseoutPackRun19
import PalPeg.CloseoutPackRun20

/-!
# `CloseoutPackRun23`: `LPackM2` — the guarded left pack with four more fields

`CloseoutPackRun19` / `CloseoutPackRun20` / `CloseoutPackRun21` each reduce a
`BigResid6` contract to one fact the pack `CloseoutPackRun10.LPackM` does not
carry.  This file adds those facts as mode-guarded fields of a bigger pack
`LPackM2` and proves that the bigger pack survives one `galilFrameS` tick
(`lpackM2_tick`), reusing `CloseoutPackRun11.lpackN_tick` for the `LPackM`
half and proving only the new conjuncts per branch.

* `scanGeomR` — `ScanInvariant` in `scan` while `replaying = true`
  (`CloseoutPackRun19.H_scanGeomReplay`).  **Closed at every tick.**  The
  replaying scan moves the heads exactly as the non-replaying one
  (`scan_match` is the only mover, and `matched_invariant'` never reads the
  flag); the `replayStart` landing is the radius-`0` invariant at the source
  centre (`scan_initial`), which is what `centreRep` supplies.
* `shiftGeom` — the running geometry of a shift round, `ShiftGeom`: with
  `remaining = ofNat rem`, the heads `L`, `C` and the destination centre
  `position C + rem` satisfy the `ScanInvariant` equations *at the exit*,
  and the palindrome is already known at the destination.  Preserved by
  `shift_one`, and `shiftGeom_exit` turns it into `ScanInvariant` when
  `remaining` is exhausted (`CloseoutPackRun19.H_shiftDoneGeom`).  **Closed
  at every tick except the entry `scan_shift`**, where the single named
  hypothesis `LTickLeaves2.shiftEntry` asks for `ShiftGeom` at the landing;
  its content is the whole-round palindrome
  `GalilScaffoldChainReadOrigin.reshift_palindrome` (§4).
* `rrep` — the right head is represented and present at every mode strictly
  between `scan` and `rewind` (`OffScan`), in particular in `choose`
  (`CloseoutPackRun20.RRepChoose`).  **Closed at every tick**: established at
  `scan_shift` / `scan_fallback` from `ScanInvariant` plus `canRight`, and
  `R` is untouched by shift/copy/home/fpp/markEnd/choose.
* `centreRep` — `CentreRep w s` in `rewind ∨ replayStart`
  (`H_centreReplay` of `CloseoutPackRun21`), together with the order
  `position L ≤ position C` in `rewind` that its `rewind_pair` preservation
  needs.  **Closed at every tick**: `choose_select` copies the (represented,
  present) right head into `C`, `rewind_pair` moves `C` left one place while
  the `rewindLeft` leaf keeps `L` (hence `C`) two places from the origin.

Hypotheses of `lpackM2_tick`: `LTickLeavesN` (as `lpackN_tick`), `AuxPack`
(for `FrontPack.flag` — no replay outside `scan` — and `CopyPack` — no copy
reading of `remainingPos` in `shift`), and the one new leaf `LTickLeaves2`.

## Honest status

Standard axioms only; unconditional `PAL ∈ PEG` remains open.  Three of the
four new fields are unconditional along a tick; `shiftGeom` is conditional on
its entry leaf.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun23

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilFrontMono PalPeg.GalilFinalAssembly
open PalPeg.CloseoutLPack PalPeg.CloseoutLPack3 PalPeg.CloseoutLPack4 PalPeg.CloseoutLPack5
open PalPeg.CloseoutPackRun2 PalPeg.CloseoutPackRun10 PalPeg.CloseoutPackRun11
open PalPeg.CloseoutPackRun19 PalPeg.CloseoutPackRun20
open PalPeg.GalilInvPlus2 (CentreRep centreRep_congr)

/-! ## 1. The new fields -/

/-- The modes strictly between `scan` and `rewind`: the right head is frozen. -/
def OffScan (m : Mode) : Prop :=
  m = Mode.shift ∨ m = Mode.copy ∨ m = Mode.home ∨ m = Mode.fpp ∨
    m = Mode.markEnd ∨ m = Mode.choose

instance (m : Mode) : Decidable (OffScan m) := by unfold OffScan; infer_instance

/-- The right head is represented and present. -/
def RRep (w : List (Fin 2)) (s : GalilVM) : Prop :=
  GalilScaffoldInputTrace.Represents s.right.head w ∧ s.right.head.focus ≠ none

/-- **The running geometry of a shift round.**  `rem` units remain; the
destination centre is `position C + rem`; the left head will arrive at
`position L + 2·rem`, which is `r` left of the destination while `R` is `r`
right of it; the palindrome of radius `r` at the destination is known; both
moving heads are `Sane` (so `right` advances `position` by one). -/
def ShiftGeom (w : List (Fin 2)) (s : GalilVM) : Prop :=
  ∃ rem r : ℕ,
    s.remaining = ofNat rem ∧
    GalilScaffoldInputTrace.Represents s.left.head w ∧
    RRep w s ∧
    Sane s.left ∧ Sane s.center ∧
    position s.left + 2 * rem + r = position s.center + rem ∧
    position s.right = position s.center + rem + r ∧
    0 < position s.left + 2 * rem ∧
    Manacher.PalAt (encoded w) (position s.center + rem) r

/-- **(KEY DEFINITION) `LPackM` plus the four new mode-guarded fields.** -/
structure LPackM2 (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  packM : LPackM w c s
  scanGeomR : c.mode = Mode.scan → c.replaying = true →
    ∃ rad : ℕ, ScanInvariant w (position s.center) rad s.left s.right
  shiftGeom : c.mode = Mode.shift → ShiftGeom w s
  rrep : OffScan c.mode → RRep w s
  centreRep : c.mode = Mode.rewind ∨ c.mode = Mode.replayStart → CentreRep w s
  centreOrder : c.mode = Mode.rewind → position s.left ≤ position s.center

/-! ## 2. Small facts -/

theorem positive_ofNat_succ (n : ℕ) : positive (ofNat (n+1)) = true := by
  simp [positive, ofNat]

theorem positive_ofNat_zero' : positive (ofNat 0) = false := rfl

theorem shiftGeom_congr {w : List (Fin 2)} {s t : GalilVM} (h : ShiftGeom w s)
    (hL : t.left = s.left) (hC : t.center = s.center) (hR : t.right = s.right)
    (hM : t.remaining = s.remaining) : ShiftGeom w t := by
  unfold ShiftGeom RRep at h ⊢
  rw [hL, hC, hR, hM]; exact h

theorem rrep_congr {w : List (Fin 2)} {s t : GalilVM} (h : RRep w s) (hR : t.right = s.right) :
    RRep w t := by
  unfold RRep at h ⊢; rw [hR]; exact h

/-- **The shift exit.**  When `remaining` is exhausted `ShiftGeom` is the
fixed-centre `ScanInvariant` at the current heads. -/
theorem shiftGeom_exit {w : List (Fin 2)} {s : GalilVM} (h : ShiftGeom w s)
    (hz : positive s.remaining = false) :
    ∃ r, ScanInvariant w (position s.center) r s.left s.right := by
  obtain ⟨rem, r, hrem, hlrep, ⟨hrrep, hrpres⟩, -, -, hlpos, hrpos, hl0, hpal⟩ := h
  cases rem with
  | succ n => rw [hrem, positive_ofNat_succ] at hz; exact Bool.noConfusion hz
  | zero =>
    refine ⟨r, hlrep, hrrep, present_of_rep_pos hlrep (by omega), hrpres, by omega, by omega, ?_⟩
    simpa using hpal

/-- A left move never raises `position` (`CloseoutPackRun13.position_left`). -/
theorem position_left_le (p : PlaceHead) : position (GalilScaffoldInputHead.left p) ≤ position p := by
  rw [CloseoutPackRun13.position_left]; omega

/-! ## 3. The new leaf and the tick -/

section Tick
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) the one new leaf: `ShiftGeom` at a shift entry.**  Its content is
the whole-round palindrome `reshift_palindrome` at the destination centre
`position C + periodLength wch`, radius `radius + 1 − periodLength wch`. -/
structure LTickLeaves2 (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  shiftEntry : c.mode = Mode.scan → c.replaying = false → ∀ s' t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).compare s s' →
    ¬ (galilFrameS (PofC centre place entry w) q first).matched s' →
    (galilFrameS (PofC centre place entry w) q first).shiftGuard s' →
    (galilFrameS (PofC centre place entry w) q first).beginShift s' t →
    ShiftGeom w t

/-- Discharge a mode-guarded field whose guard names a different mode. -/
macro "vac" h:term : tactic => `(tactic| (
  intro hx
  first
    | exact Mode.noConfusion hx
    | exact Mode.noConfusion (Eq.trans (Eq.symm $h) hx)
    | (rcases hx with hx | hx <;> first
        | exact Mode.noConfusion hx
        | exact Mode.noConfusion (Eq.trans (Eq.symm $h) hx))
    | (rcases hx with hx | hx | hx | hx | hx | hx <;> first
        | exact Mode.noConfusion hx
        | exact Mode.noConfusion (Eq.trans (Eq.symm $h) hx))))

/-- **(KEY) `LPackM2` survives one tick.**  The `LPackM` half is
`lpackN_tick`; each branch proves the four new conjuncts. -/
theorem lpackM2_tick {w : List (Fin 2)} {c c' : Control} {s t : GalilVM}
    (hP : LPackM2 w c s) (hL : LTickLeavesN centre place entry q first w c s)
    (hA : AuxPack c s) (hL2 : LTickLeaves2 centre place entry q first w c s)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 ⟨c, s⟩ ⟨c', t⟩) :
    LPackM2 w c' t := by
  have hM : LPackM w c' t := lpackN_tick centre place entry q first hP.packM hL h
  cases h
  case init =>
    rename_i hm hi
    have hf : c.replaying = false := hA.front.flag (by rw [hm]; decide)
    refine ⟨hM, fun _ hrep => ?_, ?_, ?_, ?_, ?_⟩
    · rw [hf] at hrep; exact Bool.noConfusion hrep
    all_goals vac hm
  case scan_wait =>
    rename_i hm hav hb
    obtain ⟨hl, hr, -, hC, -⟩ := backgroundS_fields (PofC centre place entry w) q first hb
    refine ⟨hM, fun _ hrep => ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨r, hi⟩ := hP.scanGeomR hm hrep
      exact ⟨r, by rw [hl, hr, hC]; exact hi⟩
    all_goals vac hm
  case scan_count =>
    rename_i hm hc hav hb
    obtain ⟨hl, hr, -, hC, -⟩ := backgroundS_fields (PofC centre place entry w) q first hb
    refine ⟨hM, fun _ hrep => ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨r, hi⟩ := hP.scanGeomR hm hrep
      exact ⟨r, by rw [hl, hr, hC]; exact hi⟩
    all_goals vac hm
  case restart =>
    rename_i hm hb
    obtain ⟨wch, -, -, -, -, ht⟩ : restartVM entry s t := hb
    subst ht
    refine ⟨hM, fun _ hrep => ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨r, hi⟩ := hP.scanGeomR hm hrep
      exact ⟨r, hi⟩
    all_goals vac hm
  case scan_match =>
    rename_i s' o hmt hm hc hcmp hav hpl ho
    obtain ⟨vs, vq, hvl, hvr, hmatch, rfl⟩ :=
      compare_matched_form centre place entry q first hcmp hmt
    have hpl' : t = (if c.replaying then
        {afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq) with
          replay := dec (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq)).replay}
      else afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq)) := hpl
    have htl : t.left = (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq)).left := by
      rw [hpl']; cases c.replaying <;> rfl
    have htr : t.right = (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq)).right := by
      rw [hpl']; cases c.replaying <;> rfl
    have htc : t.center = s.center := by
      rw [hpl']
      cases c.replaying <;> simp [afterBirth_center, afterCompare_center]
    have hcan := hL.scanCanR hm
    obtain ⟨r, hi⟩ : ∃ r, ScanInvariant w (position s.center) r s.left s.right := by
      cases hrep : c.replaying with
      | false => exact hP.packM.scanGeom hm hrep
      | true => exact hP.scanGeomR hm hrep
    have hi' := matched_invariant' w vq hvl hvr hmatch hcan hi
    refine ⟨hM, fun _ _ => ⟨r + 1, ?_⟩, ?_, ?_, ?_, ?_⟩
    · rw [htc, htl, htr, afterBirth_left, afterBirth_right]; exact hi'
    all_goals vac hm
  case scan_shift =>
    rename_i s' hmt hg hm hc hr hcmp hav hb
    have hSG : ShiftGeom w t := hL2.shiftEntry hm hr _ _ hcmp hmt hg hb
    obtain ⟨vs, vq, hvl, hvr, rfl⟩ :=
      compare_mismatch_form centre place entry q first hcmp hmt
    obtain ⟨wch, hchain, ht⟩ :
      beginShiftVM' (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterMismatch s vs vq)) t := hb
    have htr : t.right = GalilScaffoldChainVerifier.right s.right := by
      rw [ht, afterBirth_right, afterMismatch_right]; exact hvr
    obtain ⟨r0, hi⟩ := hP.packM.scanGeom hm hr
    have hcan := hL.scanCanR hm
    refine ⟨hM, ?_, fun _ => hSG, fun _ => ⟨?_, ?_⟩, ?_, ?_⟩
    · vac hm
    · rw [htr]; exact right_word _ w hi.rightRep hcan
    · rw [htr]; exact right_present _ w hi.rightRep hi.rightPresent hcan
    all_goals vac hm
  case scan_fallback =>
    rename_i s' hmt hm hc hg hr hcmp hav hb
    obtain ⟨vs, vq, hvl, hvr, rfl⟩ :=
      compare_mismatch_form centre place entry q first hcmp hmt
    obtain ⟨pl, ht⟩ :
      beginFallbackVM' (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterMismatch s vs vq)) t := hb
    have htr : t.right = GalilScaffoldChainVerifier.right s.right := by
      rw [ht, afterBirth_right, afterMismatch_right]; exact hvr
    obtain ⟨r0, hi⟩ := hP.packM.scanGeom hm hr
    have hcan := hL.scanCanR hm
    refine ⟨hM, ?_, ?_, fun _ => ⟨?_, ?_⟩, ?_, ?_⟩
    · vac hm
    · vac hm
    · rw [htr]; exact right_word _ w hi.rightRep hcan
    · rw [htr]; exact right_present _ w hi.rightRep hi.rightPresent hcan
    all_goals vac hm
  case shift_one =>
    rename_i hm hp hi
    obtain ⟨hcC, hcL, hcL2, wch, hw, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    have htl : t.left = GalilScaffoldChainVerifier.right
        (GalilScaffoldChainVerifier.right s.left) := by rw [ht]; rfl
    have htc : t.center = GalilScaffoldChainVerifier.right s.center := by rw [ht]; rfl
    have htr : t.right = s.right := by rw [ht]; rfl
    have htm : t.remaining = dec s.remaining := by rw [ht]; rfl
    obtain ⟨rem, r, hrem, hlrep, hrr, hsl, hsc, hlpos, hrpos, hl0, hpal⟩ := hP.shiftGeom hm
    have hpos : positive s.remaining = true := by
      rcases hp with h | h
      · exact h
      · exact absurd h (hA.copyP (by rw [hm]; decide))
    obtain ⟨n, rfl⟩ : ∃ n, rem = n + 1 := by
      cases rem with
      | zero => rw [hrem, positive_ofNat_zero'] at hpos; exact Bool.noConfusion hpos
      | succ n => exact ⟨n, rfl⟩
    have hcC' : canRight s.center := hcC
    have hcL' : canRight s.left := hcL
    have hcL2' : canRight (GalilScaffoldChainVerifier.right s.left) := hcL2
    have hCr := right_sane hcC' hsc
    have hLr := right_sane hcL' hsl
    have hLrr := right_sane hcL2' hLr.2
    refine ⟨hM, ?_, fun _ => ⟨n, r, ?_, ?_, rrep_congr hrr htr, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      fun _ => rrep_congr hrr htr, ?_, ?_⟩
    · vac hm
    · rw [htm, hrem]; exact dec_ofNat_succ n
    · rw [htl]; exact right_word _ w (right_word _ w hlrep hcL') hcL2'
    · rw [htl]; exact hLrr.2
    · rw [htc]; exact hCr.2
    · rw [htl, htc, hLrr.1, hLr.1, hCr.1]; omega
    · rw [htr, htc, hCr.1]; omega
    · rw [htl, hLrr.1, hLr.1]; omega
    · rw [htc, hCr.1]
      have he : position s.center + 1 + n = position s.center + (n + 1) := by omega
      rw [he]; exact hpal
    all_goals vac hm
  case shift_done =>
    rename_i o hm hp ho
    have hf : c.replaying = false := hA.front.flag (by rw [hm]; decide)
    refine ⟨hM, fun _ hrep => ?_, ?_, ?_, ?_, ?_⟩
    · rw [hf] at hrep; exact Bool.noConfusion hrep
    all_goals vac hm
  case copy_one =>
    rename_i hm hp hi
    obtain ⟨-, hset⟩ := hi
    have htr : t.right = s.right := by rw [hset]; rfl
    refine ⟨hM, ?_, ?_, fun _ => rrep_congr (hP.rrep (by rw [hm]; decide)) htr, ?_, ?_⟩
    all_goals vac hm
  case copy_done =>
    rename_i hm hp hi
    obtain ⟨-, hset⟩ := hi
    have htr : t.right = s.right := by rw [hset]; rfl
    refine ⟨hM, ?_, ?_, fun _ => rrep_congr (hP.rrep (by rw [hm]; decide)) htr, ?_, ?_⟩
    all_goals vac hm
  case home_start =>
    rename_i hm hl hi
    obtain ⟨-, hset⟩ := hi
    have htr : t.right = s.right := by rw [hset]; rfl
    refine ⟨hM, ?_, ?_, fun _ => rrep_congr (hP.rrep (by rw [hm]; decide)) htr, ?_, ?_⟩
    all_goals vac hm
  case home_step =>
    rename_i hm hl hi
    obtain ⟨-, hset⟩ := hi
    have htr : t.right = s.right := by rw [hset]; rfl
    refine ⟨hM, ?_, ?_, fun _ => rrep_congr (hP.rrep (by rw [hm]; decide)) htr, ?_, ?_⟩
    all_goals vac hm
  case fpp_slice =>
    rename_i hm hi
    obtain ⟨-, hset⟩ := hi
    have htr : t.right = s.right := by rw [hset]; rfl
    refine ⟨hM, ?_, ?_, fun _ => rrep_congr (hP.rrep (by rw [hm]; decide)) htr, ?_, ?_⟩
    all_goals vac hm
  case fpp_done =>
    rename_i hm hi
    obtain ⟨-, hset⟩ := hi
    have htr : t.right = s.right := by rw [hset]; rfl
    refine ⟨hM, ?_, ?_, fun _ => rrep_congr (hP.rrep (by rw [hm]; decide)) htr, ?_, ?_⟩
    all_goals vac hm
  case markEnd_step =>
    rename_i hm he hi
    obtain ⟨-, hset⟩ := hi
    have htr : t.right = s.right := by rw [hset]; rfl
    refine ⟨hM, ?_, ?_, fun _ => rrep_congr (hP.rrep (by rw [hm]; decide)) htr, ?_, ?_⟩
    all_goals vac hm
  case markEnd_found =>
    rename_i hm he hi
    obtain ⟨⟨-, heq⟩, hset⟩ := hi
    have htr : t.right = s.right := by rw [hset, heq]; rfl
    refine ⟨hM, ?_, ?_, fun _ => rrep_congr (hP.rrep (by rw [hm]; decide)) htr, ?_, ?_⟩
    all_goals vac hm
  case choose_step =>
    rename_i hm hs hi
    obtain ⟨⟨-, heq⟩, hset⟩ := hi
    have htr : t.right = s.right := by rw [hset, heq]; rfl
    refine ⟨hM, ?_, ?_, fun _ => rrep_congr (hP.rrep (by rw [hm]; decide)) htr, ?_, ?_⟩
    all_goals vac hm
  case choose_select =>
    rename_i hm hodd hs hi
    obtain ⟨heq, hset⟩ := hi
    have htc : t.center = s.right := by rw [hset, heq]; rfl
    have htl : t.left = s.right := by rw [hset, heq]; rfl
    obtain ⟨hrr, hrp⟩ := hP.rrep (by rw [hm]; decide)
    refine ⟨hM, ?_, ?_, ?_, fun _ => ⟨by rw [htc]; exact hrr, by rw [htc]; exact hrp⟩,
      fun _ => by rw [htl, htc]⟩
    all_goals vac hm
  case rewind_done =>
    rename_i hm hfi hi
    obtain ⟨heq, hset⟩ := hi
    have htc : t.center = s.center := by rw [hset, heq]; rfl
    refine ⟨hM, ?_, ?_, ?_, fun _ => centreRep_congr htc (hP.centreRep (Or.inl hm)), ?_⟩
    all_goals vac hm
  case rewind_one =>
    rename_i hm hfi hpr hi
    obtain ⟨⟨-, heq⟩, hset⟩ := hi
    have htc : t.center = s.center := by rw [hset, heq]; rfl
    have htl : t.left = GalilScaffoldInputHead.left s.left := by rw [hset, heq]; rfl
    refine ⟨hM, ?_, ?_, ?_, fun _ => centreRep_congr htc (hP.centreRep (Or.inl hm)), fun _ => ?_⟩
    · vac hm
    · vac hm
    · vac hm
    · rw [htl, htc]
      exact (position_left_le s.left).trans (hP.centreOrder hm)
  case rewind_pair =>
    rename_i hm hfi hpr hi
    have heq := hi.1.2
    have hset := hi.2
    have htc : t.center = GalilScaffoldInputHead.left s.center := by rw [hset, heq]; rfl
    have htl : t.left = GalilScaffoldInputHead.left s.left := by rw [hset, heq]; rfl
    have hord := hP.centreOrder hm
    have hlpos := hL.rewindLeft hm (by assumption)
    have hcpos : 0 < position (GalilScaffoldInputHead.left s.center) := by
      rw [CloseoutPackRun13.position_left] at hlpos ⊢; omega
    obtain ⟨hcr, hcp⟩ := hP.centreRep (Or.inl hm)
    obtain ⟨hc1, hc2⟩ := lrep_left hcr hcp hcpos
    refine ⟨hM, ?_, ?_, ?_, fun _ => ⟨by rw [htc]; exact hc1, by rw [htc]; exact hc2⟩, fun _ => ?_⟩
    · vac hm
    · vac hm
    · vac hm
    · rw [htl, htc, CloseoutPackRun13.position_left, CloseoutPackRun13.position_left]; omega
  case replayStart =>
    rename_i o hm ho ho' hi
    obtain ⟨-, hr, hl, hc, -⟩ := hi
    obtain ⟨hrep, hpres⟩ := hP.centreRep (Or.inr hm)
    refine ⟨hM, fun _ _ => ⟨0, ?_⟩, ?_, ?_, ?_, ?_⟩
    · rw [hl, hc, hr]; exact scan_initial w s.center hrep hpres
    all_goals vac hm

/-- `lpackM2_tick` in state form. -/
theorem lpackM2_tick' {w : List (Fin 2)} {x y : State GalilVM}
    (hP : LPackM2 w x.ctl x.vm) (hL : LTickLeavesN centre place entry q first w x.ctl x.vm)
    (hA : AuxPack x.ctl x.vm) (hL2 : LTickLeaves2 centre place entry q first w x.ctl x.vm)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y) :
    LPackM2 w y.ctl y.vm := by
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  exact lpackM2_tick centre place entry q first hP hL hA hL2 h

/-! ## 4. Entry, induction, and the three contracts -/

/-- **Entry.**  At the boot state every new field is vacuous (`boot` is in
`Mode.init`), so `LPackM2` is `lpackM_boot`. -/
theorem lpackM2_boot (w : List (Fin 2)) : LPackM2 w (boot w).ctl (boot w).vm := by
  have hm : (boot w).ctl.mode = Mode.init := rfl
  refine ⟨lpackM_boot w, ?_, ?_, ?_, ?_, ?_⟩
  all_goals vac hm

/-- **The tick induction** over a pre-loaded trace with the leaves at every
state. -/
theorem lpackM2_steps {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : PreTrace centre place entry q first w st Tc)
    (hLv : ∀ i, i ≤ Tc w.length →
      LTickLeavesN centre place entry q first w (st i).ctl (st i).vm ∧
      AuxPack (st i).ctl (st i).vm ∧
      LTickLeaves2 centre place entry q first w (st i).ctl (st i).vm) :
    ∀ i, i ≤ Tc w.length → LPackM2 w (st i).ctl (st i).vm := by
  intro i
  induction i with
  | zero => intro _; rw [hP.start]; exact lpackM2_boot w
  | succ n ih =>
    intro hi
    obtain ⟨h1, h2, h3⟩ := hLv n (by omega)
    exact lpackM2_tick' centre place entry q first (ih (by omega)) h1 h2 h3
      (hP.trace.tick n (by omega))

/-- **`H_scanGeomReplay`** (`CloseoutPackRun19`) from `LPackM2` at every pack state. -/
theorem scanGeomReplay_of_lpackM2 {w : List (Fin 2)}
    (hall : ∀ x : State GalilVM, BigPack2M centre place entry q first w x → LPackM2 w x.ctl x.vm) :
    H_scanGeomReplay centre place entry q first w :=
  fun x hx hm hrep => (hall x hx).scanGeomR hm hrep

/-- **`H_shiftDoneGeom`** (`CloseoutPackRun19`) from `LPackM2` at every pack state. -/
theorem shiftDoneGeom_of_lpackM2 {w : List (Fin 2)}
    (hall : ∀ x : State GalilVM, BigPack2M centre place entry q first w x → LPackM2 w x.ctl x.vm) :
    H_shiftDoneGeom centre place entry q first w := by
  intro x hx hm hnp
  have hz : positive x.vm.remaining = false := by
    cases hpos : positive x.vm.remaining with
    | false => rfl
    | true => exact absurd (Or.inl hpos) hnp
  exact shiftGeom_exit ((hall x hx).shiftGeom hm) hz

/-- **`RRepChoose`** (`CloseoutPackRun20`) from `LPackM2` at every pack state. -/
theorem rrepChoose_of_lpackM2 {w : List (Fin 2)}
    (hall : ∀ x : State GalilVM, BigPack2M centre place entry q first w x → LPackM2 w x.ctl x.vm) :
    RRepChoose centre place entry q first w :=
  fun x hx hm _ => (hall x hx).rrep (by rw [hm]; decide)

/-- **`H_centreReplay`** (`CloseoutPackRun21`, stated inline) from `LPackM2`. -/
theorem centreReplay_of_lpackM2 {w : List (Fin 2)}
    (hall : ∀ x : State GalilVM, BigPack2M centre place entry q first w x → LPackM2 w x.ctl x.vm) :
    ∀ x : State GalilVM, BigPack2M centre place entry q first w x →
      x.ctl.mode = Mode.replayStart → CentreRep w x.vm :=
  fun x hx hm => (hall x hx).centreRep (Or.inr hm)

end Tick

#print axioms shiftGeom_exit
#print axioms lpackM2_tick
#print axioms lpackM2_tick'
#print axioms lpackM2_boot
#print axioms lpackM2_steps
#print axioms scanGeomReplay_of_lpackM2
#print axioms shiftDoneGeom_of_lpackM2
#print axioms rrepChoose_of_lpackM2
#print axioms centreReplay_of_lpackM2

end PalPeg.CloseoutPackRun23
