import PalPeg.CloseoutLPack2

/-!
# `CloseoutLPack3`: the head transport of `LPack`, tick by tick

This file attacks `CloseoutLPack2.LPackTick` — **NAMED** there as

    ∀ w, 0 < w.length → ∀ x y : State GalilVM,
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y →
      LPack w x.ctl x.vm → LPack w y.ctl y.vm

with `LPack` (`CloseoutLPack`) the conjunction of

* `lrep`  : off `init`, the left head represents `w` and is present,
* `scanInv`: in a non-replaying `scan`, `∃ rad, ScanInvariant w C rad L R`,
* `minv`  : off `init`, `MInv w c s`.

The strategy is the one of `CloseoutRadPack2.shiftOrd_tick`: split the 23
constructors of one tick and discharge every one whose VM step leaves the three
heads and the replay counter alone.

**Proved here, unconditionally.**

* `present_iff_left`, `moveRight_left_pos`, `lrep_right`, `lrep_left` — the head
  transport.  For a *represented* head, presence of the focus is exactly a
  nonempty left stack; a right step always pushes the focus, so it keeps both;
  a left step keeps both **iff** the landing place is still positive.  That last
  side condition is the origin corner `CloseoutLPack` named, now isolated to a
  single numeric hypothesis `0 < position (left L)`.
* `compare_matched_form` / `compare_mismatch_form` — a comparison whose landing
  `F.matched` holds is the `afterCompare` branch of `compareFound` (the answer
  bit is forced, because `matched` reads only the scan lens, which both branches
  share), and a mismatched one is the `afterMismatch` branch.
* `lpack_of_same` — a VM step that fixes `L`, `C`, `R` and `replay` carries the
  whole pack.
* `lpack_tick` — **`LPack` along one tick**, from `LTickLeaves`.  All 23
  constructors are split.  Discharged outright: `init`-free head transport in
  `scan_wait`, `scan_count`, `restart` (backgrounds and the restart keep every
  head), `copy_one`, `copy_done`, `home_start`, `home_step`, `fpp_slice`,
  `fpp_done`, `markEnd_step` (all `fppLens` steps), `markEnd_found`,
  `choose_step`, `rewind_done` (`rewindLens` steps that touch only `fpp`),
  `shift_done` (the VM is unchanged), the *whole* of `scan_match` (`lrep` by
  `lrep_left`, `scanInv` by `matched_invariant'`, `minv` by `minv_match` off a
  replay and `minv_matchR` during one), and the `lrep` halves of `scan_shift`,
  `scan_fallback`, `shift_one` (two `lrep_right` steps against the `shiftOne`
  guards), `rewind_one` and `rewind_pair`.
* `lpack_tick'`, `h_lpack_of_lticks` — `CloseoutLPack.H_lpack` by induction on
  the tick index, `lpack_boot` as base case.
* `h_trailF_lpack3` / `h_trailF_C3` — `H_trailF` from `H_lticks` together with
  the three shift-entry residuals of `CloseoutLPack2`.

**The named residual** is `LTickLeaves` (and its trace form `H_lticks`), whose
eleven fields are each a statement about *one* state and *one* VM step:
`initPack` (the boot landing), `scanLeft` and `rewindLeft` (the origin corner at
a comparison and at a rewind unit), `scanInvR` and `scanCanR` (the scan
invariant and the right head's mobility in `scan`, including during a replay),
`shiftMinv` / `fallbackMinv` (`MInv` at the two entries, where `R` moves one
place right), `shiftOneMinv` and `rewindPairMinv` (`MInv` where `C` moves),
`shiftDoneScan` (the new centre's palindrome radius after a shift — the one
genuinely non-tick-local corner `CloseoutLPack` predicted), `choosePack` (the
re-centring on the right head) and `replayPack` (all three heads reset onto the
centre).

`H_shiftScan` and `H_shiftPlaces` are **unchanged and still named**.
`H_shiftScan`'s controller-mode conjunct is not recoverable from `compare` and
`beginShiftVM'` (it is the `scan_shift` constructor's own `hm`/`hr`), and its
`canRight R` conjunct is exactly `LTickLeaves.scanCanR`, so the two should be
discharged together; `H_shiftPlaces`' `distance ≤ 2·rad` needs the chain/scan
coupling (`GalilChainCoupling.Coupled.sum`) against the *scan* radius, which is
a chain-window fact, not head arithmetic.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutLPack3

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilThrottledRun PalPeg.GalilTrailProof PalPeg.GalilFinalAssembly
open PalPeg.CloseoutRadPack PalPeg.CloseoutRadPack2 PalPeg.CloseoutRadPack3
open PalPeg.CloseoutRadPack4 PalPeg.CloseoutLPack PalPeg.CloseoutLPack2
open PalPeg.GalilRunSkeleton
open GalilScaffoldInputHead GalilScaffoldCounter

/-! ## 1. Presence is the length of the left stack -/

/-- For a represented head, presence of the focus is exactly a nonempty left
stack.  (`represented_position` is the forward direction only.) -/
theorem present_iff_left {w : List (Fin 2)} {h : GalilScaffoldInputHead.Head}
    (hh : GalilScaffoldInputTrace.Represents h w) :
    h.focus ≠ none ↔ 0 < h.left.length := by
  obtain ⟨xs, rs, q, rfl, -⟩ := hh
  cases xs with
  | nil => simp [GalilScaffoldInputHead.layout]
  | cons a xs => simp [GalilScaffoldInputHead.layout]

#print axioms present_iff_left

/-- A right step always pushes the focus, so the left stack stays nonempty. -/
theorem moveRight_left_pos {h : GalilScaffoldInputHead.Head}
    (hc : GalilScaffoldInputTrace.canRight h) :
    0 < (GalilScaffoldInputTrace.moveRight h).left.length := by
  rcases h with ⟨f, ls, rs, q⟩
  unfold GalilScaffoldInputTrace.moveRight
  cases rs with
  | cons a rs => simp
  | nil =>
    cases q with
    | nil => rcases hc with h | h <;> simp at h
    | cons a q => simp

#print axioms moveRight_left_pos

/-- **A right step keeps the left head represented and present.** -/
theorem lrep_right {w : List (Fin 2)} {p : PlaceHead}
    (hh : GalilScaffoldInputTrace.Represents p.head w) (hp : p.head.focus ≠ none)
    (hc : GalilScaffoldChainVerifier.canRight p) :
    GalilScaffoldInputTrace.Represents (GalilScaffoldChainVerifier.right p).head w ∧
      (GalilScaffoldChainVerifier.right p).head.focus ≠ none := by
  rcases p with ⟨hd, g⟩
  cases g with
  | false => exact ⟨hh, hp⟩
  | true =>
    have hc' : GalilScaffoldInputTrace.canRight hd := by
      rcases hc with h | h | h
      · exact absurd h (by simp)
      · exact Or.inl h
      · exact Or.inr h
    have hr : GalilScaffoldInputTrace.Represents (GalilScaffoldInputTrace.moveRight hd) w :=
      GalilScaffoldInputTrace.right_represents hh hc'
    refine ⟨hr, ?_⟩
    show (GalilScaffoldInputTrace.moveRight hd).focus ≠ none
    rw [present_iff_left hr]
    exact moveRight_left_pos hc'

#print axioms lrep_right

/-- **A left step keeps the left head represented, and present exactly when it
does not fall onto the origin.**  This is the corner named in `CloseoutLPack`:
the landing place has to stay positive. -/
theorem lrep_left {w : List (Fin 2)} {p : PlaceHead}
    (hh : GalilScaffoldInputTrace.Represents p.head w) (hp : p.head.focus ≠ none)
    (hpos : 0 < position (GalilScaffoldInputHead.left p)) :
    GalilScaffoldInputTrace.Represents (GalilScaffoldInputHead.left p).head w ∧
      (GalilScaffoldInputHead.left p).head.focus ≠ none := by
  rcases p with ⟨hd, g⟩
  cases g with
  | true => exact ⟨hh, hp⟩
  | false =>
    have hne : hd.left ≠ [] := (GalilScaffoldInputTrace.left_represents hh hp).1
    have hr : GalilScaffoldInputTrace.Represents (GalilScaffoldInputHead.moveLeft hd) w :=
      (GalilScaffoldInputTrace.left_represents hh hp).2
    refine ⟨hr, ?_⟩
    show (GalilScaffoldInputHead.moveLeft hd).focus ≠ none
    rw [present_iff_left hr]
    have hpos' : 0 < 2 * (GalilScaffoldInputHead.moveLeft hd).left.length := by
      simpa [position, GalilScaffoldInputHead.left] using hpos
    omega

#print axioms lrep_left

/-! ## 2. What a comparison looks like when it matched -/

section Compare
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **A matched comparison is the `afterCompare` branch.**  The answer bit of
`compareFound` is forced to `true` by `F.matched` at the landing, because
`matched` reads only the scan lens and both branches carry the same `vs`. -/
theorem compare_matched_form {w : List (Fin 2)} {s s' : GalilVM}
    (hcmp : (galilFrameS (PofC centre place entry w) q first).compare s s')
    (hmt : (galilFrameS (PofC centre place entry w) q first).matched s') :
    ∃ (vs : ScanVM) (vq : SearchVM),
      vs.left = GalilScaffoldInputHead.left s.left ∧
      vs.right = GalilScaffoldChainVerifier.right s.right ∧
      GalilScaffoldInputHead.read (GalilScaffoldInputHead.left s.left) =
        GalilScaffoldInputHead.read (GalilScaffoldChainVerifier.right s.right) ∧
      s' = afterCompare s vs vq := by
  obtain ⟨vs, vq, a, hvl, hvr, hiff, -, -, hteq⟩ :
    compareFound (PofC centre place entry w) q first s s' := hcmp
  have hread : GalilScaffoldInputHead.read vs.left = GalilScaffoldInputHead.read vs.right := by
    cases a with
    | true => rw [if_pos rfl] at hteq; subst hteq; exact hmt
    | false => rw [if_neg (by simp)] at hteq; subst hteq; exact hmt
  have ha : a = true := hiff.2 hread
  subst ha
  rw [if_pos rfl] at hteq
  exact ⟨vs, vq, hvl, hvr, by rw [← hvl, ← hvr]; exact hread, hteq⟩

/-- **A mismatched comparison is the `afterMismatch` branch.** -/
theorem compare_mismatch_form {w : List (Fin 2)} {s s' : GalilVM}
    (hcmp : (galilFrameS (PofC centre place entry w) q first).compare s s')
    (hmt : ¬ (galilFrameS (PofC centre place entry w) q first).matched s') :
    ∃ (vs : ScanVM) (vq : SearchVM),
      vs.left = GalilScaffoldInputHead.left s.left ∧
      vs.right = GalilScaffoldChainVerifier.right s.right ∧
      s' = afterMismatch s vs vq := by
  obtain ⟨vs, vq, a, hvl, hvr, hiff, -, -, hteq⟩ :
    compareFound (PofC centre place entry w) q first s s' := hcmp
  cases a with
  | true => rw [if_pos rfl] at hteq; exact absurd (hteq ▸ hiff.1 rfl) hmt
  | false => rw [if_neg (by simp)] at hteq; exact ⟨vs, vq, hvl, hvr, hteq⟩

end Compare

#print axioms compare_matched_form
#print axioms compare_mismatch_form

/-! ## 3. The residual leaves of one tick -/

section Leaves
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) everything one tick of `galilFrameS` needs beyond head
transport.**  Every field is a statement about *one* state and *one* VM step;
no trace, no induction.  See `lpack_tick` for how each is used. -/
structure LTickLeaves (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  /-- The `init` landing: the boot step establishes the whole pack. -/
  initPack : c.mode = Mode.init → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).init s t →
    LPack w {c with mode := Mode.scan, output := true} t
  /-- **The origin corner.**  In `scan` the left head is at least two places
  from the origin, so the comparison's left step keeps it present. -/
  scanLeft : c.mode = Mode.scan → 0 < position (GalilScaffoldInputHead.left s.left)
  /-- The scan invariant in `scan` mode *including* a replay (`LPack.scanInv`
  gives it only off a replay; `minv_matchR` needs it during one). -/
  scanInvR : c.mode = Mode.scan →
    ∃ r, ScanInvariant w (position s.center) r s.left s.right
  /-- The right head can move in `scan` mode (free off a replay, where it is
  `F.available`; during one it is `GalilFrontMono` frontier data). -/
  scanCanR : c.mode = Mode.scan → GalilScaffoldChainVerifier.canRight s.right
  /-- The centre invariant at a shift entry: `R` moved one place right. -/
  shiftMinv : c.mode = Mode.scan → ∀ s'' t'' : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).compare s s'' →
    beginShiftVM' s'' t'' → MInv w {c with clock := 2048, mode := Mode.shift} t''
  /-- The centre invariant at a fallback entry: `R` moved one place right. -/
  fallbackMinv : c.mode = Mode.scan → ∀ s'' t'' : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).compare s s'' →
    (galilFrameS (PofC centre place entry w) q first).beginFallback s'' t'' →
    MInv w {c with clock := 2048, mode := Mode.copy} t''
  /-- The centre invariant along a shift unit: `C` moves one place right. -/
  shiftOneMinv : c.mode = Mode.shift → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).shiftOne s t → MInv w c t
  /-- **The shift exit.**  The new centre's palindrome radius is not
  tick-local; this is the leaf `CloseoutLPack` predicted. -/
  shiftDoneScan : c.mode = Mode.shift →
    ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos s →
    ∃ r, ScanInvariant w (position s.center) r s.left s.right
  /-- `choose` re-centres on the right head. -/
  choosePack : c.mode = Mode.choose → c.odd = true → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).choose s t →
    (GalilScaffoldInputTrace.Represents t.left.head w ∧ t.left.head.focus ≠ none) ∧
      MInv w {c with mode := Mode.rewind, pair := false} t
  /-- A rewind unit walks `L` (and, paired, `C`) one place left. -/
  rewindLeft : c.mode = Mode.rewind → 0 < position (GalilScaffoldInputHead.left s.left)
  /-- The centre invariant along a paired rewind unit. -/
  rewindPairMinv : c.mode = Mode.rewind → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).rewindPair s t →
    MInv w {c with pair := false} t
  /-- `replayStart` resets all three heads onto the centre. -/
  replayPack : c.mode = Mode.replayStart → ∀ (t : GalilVM) (o : Bool),
    (galilFrameS (PofC centre place entry w) q first).replayStart s t →
    LPack w {c with mode := Mode.scan, clock := 2048, output := o, replaying := (galilFrameS (PofC centre place entry w) q first).replayPos t} t

end Leaves

/-! ## 4. `LPack` along one tick -/

/-- A VM step that leaves the three heads and the replay counter alone
transports the whole pack. -/
theorem lpack_of_same {w : List (Fin 2)} {c c' : Control} {s t : GalilVM}
    (hP : LPack w c s) (hni : c.mode ≠ Mode.init)
    (hL : t.left = s.left) (hC : t.center = s.center) (hR : t.right = s.right)
    (hrep : t.replay = s.replay) (hr : c'.replaying = c.replaying)
    (hsc : c'.mode = Mode.scan → c'.replaying = false → c.mode = Mode.scan ∧ c.replaying = false) :
    LPack w c' t := by
  refine ⟨fun _ => by rw [hL]; exact hP.lrep hni, ?_,
    fun _ => minv_same hr hR hC hrep (hP.minv hni)⟩
  intro hm hrr
  obtain ⟨hm0, hr0⟩ := hsc hm hrr
  obtain ⟨r, hi⟩ := hP.scanInv hm0 hr0
  exact ⟨r, by rw [hL, hR, hC]; exact hi⟩

#print axioms lpack_of_same

section Tick
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`LPack` survives one tick, given the leaves.**  All 23 constructors are
split; the ones that move no head are discharged outright, the rest consume
exactly one field of `LTickLeaves`. -/
theorem lpack_tick {w : List (Fin 2)} {c c' : Control} {s t : GalilVM}
    (hP : LPack w c s) (hL : LTickLeaves centre place entry q first w c s)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 ⟨c, s⟩ ⟨c', t⟩) :
    LPack w c' t := by
  cases h
  case init =>
    rename_i hm hi
    exact hL.initPack hm _ hi
  case scan_wait =>
    rename_i hm hav hb
    obtain ⟨hl, hr, -, hC, -, -, -, -, -, hrep, -, -⟩ :=
      backgroundS_fields (PofC centre place entry w) q first hb
    exact lpack_of_same hP (by rw [hm]; decide) hl hC hr hrep rfl (fun hm' hr' => ⟨hm', hr'⟩)
  case scan_count =>
    rename_i hm hc hav hb
    obtain ⟨hl, hr, -, hC, -, -, -, -, -, hrep, -, -⟩ :=
      backgroundS_fields (PofC centre place entry w) q first hb
    exact lpack_of_same hP (by rw [hm]; decide) hl hC hr hrep rfl (fun hm' hr' => ⟨hm', hr'⟩)
  case restart =>
    rename_i hm hb
    obtain ⟨wch, -, -, -, -, ht⟩ : restartVM entry s t := hb
    subst ht
    exact lpack_of_same hP (by rw [hm]; decide) rfl rfl rfl rfl rfl (fun hm' hr' => ⟨hm', hr'⟩)
  case scan_match =>
    rename_i s' o hmt hm hc hcmp hav hpl ho
    obtain ⟨vs, vq, hvl, hvr, hmatch, rfl⟩ :=
      compare_matched_form centre place entry q first hcmp hmt
    have hni : c.mode ≠ Mode.init := by rw [hm]; decide
    have hpl' : t = (if c.replaying then
        {afterCompare s vs vq with replay := dec (afterCompare s vs vq).replay}
      else afterCompare s vs vq) := hpl
    have htl : t.left = (afterCompare s vs vq).left := by
      rw [hpl']; cases c.replaying <;> rfl
    have htr : t.right = (afterCompare s vs vq).right := by
      rw [hpl']; cases c.replaying <;> rfl
    have htc : t.center = s.center := by rw [hpl']; cases c.replaying <;> rfl
    have hcan := hL.scanCanR hm
    obtain ⟨r, hi⟩ := hL.scanInvR hm
    have hi' := matched_invariant' w vq hvl hvr hmatch hcan hi
    obtain ⟨hrepr, hpres⟩ := hP.lrep hni
    refine ⟨fun _ => ?_, fun _ _ => ⟨r + 1, ?_⟩, fun _ => ?_⟩
    · rw [htl, afterCompare_left, hvl]
      exact lrep_left hrepr hpres (hL.scanLeft hm)
    · rw [htc, htl, htr]; exact hi'
    · cases hcr : c.replaying with
      | false =>
        have ht : t = afterCompare s vs vq := by rw [hpl', hcr]; rfl
        have hm0 := minv_match (raw := w) (c := c) (vq := vq) o 2048 hcr hvl hvr hcan hmatch hi (hP.minv hni)
        exact minv_same (by simp) (by rw [ht]) (by rw [ht]) (by rw [ht]) hm0
      | true =>
        have ht : t = replayDec true (afterCompare s vs vq) := by rw [hpl', hcr]; rfl
        have hm0 := minv_matchR (raw := w) (c := c) (vs := vs) (vq := vq) (PofC centre place entry w)
          (fun _ => rfl) o 2048 hcr hvr hcan hi (hP.minv hni)
        exact minv_same (by rw [ht]; rfl) (by rw [ht]) (by rw [ht]) (by rw [ht]) hm0
  case scan_shift =>
    rename_i s' hmt hg hm hc hr hcmp hav hb
    obtain ⟨vs, vq, hvl, hvr, rfl⟩ :=
      compare_mismatch_form centre place entry q first hcmp hmt
    have hni : c.mode ≠ Mode.init := by rw [hm]; decide
    obtain ⟨wch, hchain, ht⟩ : beginShiftVM' (afterMismatch s vs vq) t := hb
    obtain ⟨hrepr, hpres⟩ := hP.lrep hni
    refine ⟨fun _ => ?_, fun hm' _ => Mode.noConfusion hm', fun _ => ?_⟩
    · have htl : t.left = GalilScaffoldInputHead.left s.left := by
        rw [ht]; show vs.left = _; exact hvl
      rw [htl]; exact lrep_left hrepr hpres (hL.scanLeft hm)
    · exact hL.shiftMinv hm _ _ hcmp ⟨wch, hchain, ht⟩
  case scan_fallback =>
    rename_i s' hmt hm hc hg hr hcmp hav hb
    obtain ⟨vs, vq, hvl, hvr, rfl⟩ :=
      compare_mismatch_form centre place entry q first hcmp hmt
    have hni : c.mode ≠ Mode.init := by rw [hm]; decide
    obtain ⟨pl, ht⟩ : beginFallbackVM' (afterMismatch s vs vq) t := hb
    obtain ⟨hrepr, hpres⟩ := hP.lrep hni
    refine ⟨fun _ => ?_, fun hm' _ => Mode.noConfusion hm', fun _ => ?_⟩
    · have htl : t.left = GalilScaffoldInputHead.left s.left := by
        rw [ht]; show vs.left = _; exact hvl
      rw [htl]; exact lrep_left hrepr hpres (hL.scanLeft hm)
    · exact hL.fallbackMinv hm _ _ hcmp ⟨pl, ht⟩
  case shift_one =>
    rename_i hm hp hi
    have hni : c.mode ≠ Mode.init := by rw [hm]; decide
    obtain ⟨hcC, hcL, hcL2, wch, hw, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    obtain ⟨hrepr, hpres⟩ := hP.lrep hni
    refine ⟨fun _ => ?_, fun hm' _ => Mode.noConfusion (hm.symm.trans hm'), fun _ => ?_⟩
    · have htl : t.left = GalilScaffoldChainVerifier.right
          (GalilScaffoldChainVerifier.right s.left) := by rw [ht]; rfl
      rw [htl]
      obtain ⟨h1, h2⟩ := lrep_right hrepr hpres hcL
      exact lrep_right h1 h2 hcL2
    · exact hL.shiftOneMinv hm _ hi
  case shift_done =>
    rename_i o hm hp ho
    have hni : c.mode ≠ Mode.init := by rw [hm]; decide
    refine ⟨fun _ => hP.lrep hni, fun _ _ => hL.shiftDoneScan hm hp,
      fun _ => minv_same rfl rfl rfl rfl (hP.minv hni)⟩
  case copy_one =>
    rename_i hm hp hi
    obtain ⟨-, hset⟩ := hi
    exact lpack_of_same hP (by rw [hm]; decide) (by rw [hset]; rfl) (by rw [hset]; rfl) (by rw [hset]; rfl) (by rw [hset]; rfl) rfl
      (fun hm' _ => Mode.noConfusion (hm.symm.trans hm'))
  case copy_done =>
    rename_i hm hp hi
    obtain ⟨-, hset⟩ := hi
    exact lpack_of_same hP (by rw [hm]; decide) (by rw [hset]; rfl) (by rw [hset]; rfl) (by rw [hset]; rfl) (by rw [hset]; rfl) rfl (fun hm' _ => Mode.noConfusion hm')
  case home_start =>
    rename_i hm hl hi
    obtain ⟨-, hset⟩ := hi
    exact lpack_of_same hP (by rw [hm]; decide) (by rw [hset]; rfl) (by rw [hset]; rfl) (by rw [hset]; rfl) (by rw [hset]; rfl) rfl (fun hm' _ => Mode.noConfusion hm')
  case home_step =>
    rename_i hm hl hi
    obtain ⟨-, hset⟩ := hi
    exact lpack_of_same hP (by rw [hm]; decide) (by rw [hset]; rfl) (by rw [hset]; rfl) (by rw [hset]; rfl) (by rw [hset]; rfl) rfl
      (fun hm' _ => Mode.noConfusion (hm.symm.trans hm'))
  case fpp_slice =>
    rename_i hm hi
    obtain ⟨-, hset⟩ := hi
    exact lpack_of_same hP (by rw [hm]; decide) (by rw [hset]; rfl) (by rw [hset]; rfl) (by rw [hset]; rfl) (by rw [hset]; rfl) rfl
      (fun hm' _ => Mode.noConfusion (hm.symm.trans hm'))
  case fpp_done =>
    rename_i hm hi
    obtain ⟨-, hset⟩ := hi
    exact lpack_of_same hP (by rw [hm]; decide) (by rw [hset]; rfl) (by rw [hset]; rfl) (by rw [hset]; rfl) (by rw [hset]; rfl) rfl (fun hm' _ => Mode.noConfusion hm')
  case markEnd_step =>
    rename_i hm he hi
    obtain ⟨-, hset⟩ := hi
    exact lpack_of_same hP (by rw [hm]; decide) (by rw [hset]; rfl) (by rw [hset]; rfl) (by rw [hset]; rfl) (by rw [hset]; rfl) rfl
      (fun hm' _ => Mode.noConfusion (hm.symm.trans hm'))
  case markEnd_found =>
    rename_i hm he hi
    obtain ⟨⟨-, heq⟩, hset⟩ := hi
    exact lpack_of_same hP (by rw [hm]; decide)
      (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl) (by rw [hset]; rfl) rfl (fun hm' _ => Mode.noConfusion hm')
  case choose_step =>
    rename_i hm hs hi
    obtain ⟨⟨-, heq⟩, hset⟩ := hi
    exact lpack_of_same hP (by rw [hm]; decide)
      (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl) (by rw [hset]; rfl) rfl
      (fun hm' _ => Mode.noConfusion (hm.symm.trans hm'))
  case rewind_done =>
    rename_i hm hfi hi
    obtain ⟨heq, hset⟩ := hi
    exact lpack_of_same hP (by rw [hm]; decide)
      (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl) (by rw [hset]; rfl) rfl (fun hm' _ => Mode.noConfusion hm')
  case choose_select =>
    rename_i hm hodd hs hi
    have hni : c.mode ≠ Mode.init := by rw [hm]; decide
    obtain ⟨hrepr, hpres⟩ := hL.choosePack hm hodd _ hi
    exact ⟨fun _ => ⟨hrepr.1, hrepr.2⟩, fun hm' _ => Mode.noConfusion hm', fun _ => hpres⟩
  case rewind_one =>
    rename_i hm hfi hpr hi
    have hni : c.mode ≠ Mode.init := by rw [hm]; decide
    obtain ⟨⟨-, heq⟩, hset⟩ := hi
    have htl : t.left = GalilScaffoldInputHead.left s.left := by rw [hset, heq]; rfl
    have htc : t.center = s.center := by rw [hset, heq]; rfl
    have htr : t.right = s.right := by rw [hset, heq]; rfl
    obtain ⟨hrepr, hpres⟩ := hP.lrep hni
    refine ⟨fun _ => ?_, fun hm' _ => Mode.noConfusion (hm.symm.trans hm'), fun _ => ?_⟩
    · rw [htl]; exact lrep_left hrepr hpres (hL.rewindLeft hm)
    · exact minv_same rfl htr htc (by rw [hset]; rfl) (hP.minv hni)
  case rewind_pair =>
    rename_i hm hfi hpr hi
    have hni : c.mode ≠ Mode.init := by rw [hm]; decide
    have heq := hi.1.2
    have hset := hi.2
    have htl : t.left = GalilScaffoldInputHead.left s.left := by rw [hset, heq]; rfl
    obtain ⟨hrepr, hpres⟩ := hP.lrep hni
    refine ⟨fun _ => ?_, fun hm' _ => Mode.noConfusion (hm.symm.trans hm'), fun _ => ?_⟩
    · rw [htl]; exact lrep_left hrepr hpres (hL.rewindLeft hm)
    · exact hL.rewindPairMinv hm _ hi
  case replayStart =>
    rename_i o hm ho ho' hi
    exact hL.replayPack hm _ o hi

#print axioms lpack_tick

end Tick

/-! ## 5. Trace level: `H_lpack`, and `H_trailF` -/

section Trace
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `lpack_tick` on unpacked states. -/
theorem lpack_tick' {w : List (Fin 2)} {x y : State GalilVM}
    (hP : LPack w x.ctl x.vm) (hL : LTickLeaves centre place entry q first w x.ctl x.vm)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y) :
    LPack w y.ctl y.vm := by
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  exact lpack_tick centre place entry q first hP hL h

/-- **(NAMED) the tick leaves at every state of every pre-loaded trace.**
This is all that is left of `CloseoutLPack.H_lpack` / `CloseoutLPack2.LPackTick`
once head transport is discharged: each field of `LTickLeaves` is a one-state,
one-step statement, and the induction below is done. -/
def H_lticks : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    ∀ i, i ≤ Tc w.length → LTickLeaves centre place entry q first w (st i).ctl (st i).vm

/-- **`H_lpack` from the leaves**, by induction on the tick index: `lpack_boot`
is the base case and `lpack_tick` the step. -/
theorem h_lpack_of_lticks (h : H_lticks centre place entry q first) :
    H_lpack centre place entry q first := by
  intro w hw st Tc hP i
  induction i with
  | zero => intro _; rw [hP.start]; exact lpack_boot w
  | succ i ih =>
    intro hi
    exact lpack_tick' centre place entry q first (ih (by omega))
      (h w hw st Tc hP i (by omega)) (hP.trace.tick i (by omega))

/-- **`H_trailF` from the tick leaves and the three shift-entry residuals.**
`CloseoutLPack2.h_trailF_lpack2` took `LPackTick`; this takes `H_lticks`
instead, i.e. the *corners* of a tick rather than the tick itself. -/
theorem h_trailF_lpack3 (hlt : H_lticks centre place entry q first)
    (hsc : H_shiftScan centre place entry q first)
    (hpl : H_shiftPlaces centre place entry q first)
    (hcan : H_shiftCanRight centre place entry q first) :
    H_trailF centre place entry q first :=
  have hlp := h_lpack_of_lticks centre place entry q first hlt
  h_trailF_final centre place entry q first hlp
    (h_shiftHalf_of_parts centre place entry q first hlp hsc hpl) hcan

end Trace

#print axioms lpack_tick'
#print axioms h_lpack_of_lticks
#print axioms h_trailF_lpack3

/-- **The concrete instance** at `centreC` / `placeC`. -/
theorem h_trailF_C3 (entry q : ℕ) (first : Fin 9)
    (hlt : H_lticks PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC
      entry q first)
    (hsc : H_shiftScan PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC
      entry q first)
    (hpl : H_shiftPlaces PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC
      entry q first)
    (hcan : H_shiftCanRight PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC
      entry q first) :
    H_trailF PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC entry q first :=
  h_trailF_lpack3 _ _ entry q first hlt hsc hpl hcan

#print axioms h_trailF_C3

end PalPeg.CloseoutLPack3
