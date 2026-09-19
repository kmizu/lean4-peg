import PalPeg.CloseoutLPack3

/-!
# `CloseoutLPack4`: the origin corner as arithmetic, and the mismatch landings merged

`CloseoutLPack3` reduced `CloseoutLPack.H_lpack` to `LTickLeaves`, an eleven-field
structure of one-state, one-step statements, and left `H_shiftScan` and
`H_shiftPlaces` untouched.  This file shaves that residual further.

What is **proved** here, unconditionally.

* `left_pos_of_two`, `two_le_of_left_pos`, `left_pos_iff` — **the origin corner is
  a single numeric inequality.**  `GalilFrontier.left_position_pos` says a left
  step off the origin lowers the place by exactly one, so
  `0 < position (left p)` is *equivalent* to `2 ≤ position p`.  The two head-shaped
  fields `LTickLeaves.scanLeft` and `LTickLeaves.rewindLeft` therefore become the
  plain arithmetic statements `scanMargin` / `rewindMargin` below.
* `scanInv_leftPos`, `margin_of_scanInv`, `scanInv_pos` — inside a scan the
  numeric statement is exactly a *margin* on the scan invariant: `position L`
  is `C - rad`, so `2 ≤ position L` is `rad + 2 ≤ C`, i.e. the scan has not
  reached the origin.  `scanInv_pos` records what `Live` alone does give
  (`rad < C`, hence `1 ≤ position L`): the invariant plus liveness get the left
  head to place one, and the *second* place is the genuine leaf.
* `beginShift_heads`, `beginFallback_heads` — **neither entry moves a head.**
  `beginShiftVM` only touches `remaining`, `length`, `chain`, `cycle` and
  `periodOnly`; `beginFallbackVM` only `fpp`, `chain` and `search`.  So `L`, `C`,
  `R` and the replay counter at the landing are literally those of the
  comparison's target.
* `minv_of_mismatch` — consequently `MInv` at *either* entry is `MInv` at the
  comparison's target.  The two fields `LTickLeaves.shiftMinv` and
  `LTickLeaves.fallbackMinv`, which differed only in the entry relation and the
  landing mode, collapse into the single field `mismatchMinv`, which mentions
  neither entry.
* `LTickLeaves4` / `lticks4` / `h_lticks_of_4` — the sharpened leaf structure and
  its bridge to `CloseoutLPack3.LTickLeaves` and `H_lticks`.
* `h_shiftScan_of_parts`, `h_shiftPlaces_of_parts` — `H_shiftScan` and
  `H_shiftPlaces` split into their independent conjuncts, so the controller fact,
  the mobility fact, the guard's place count and the chain/scan coupling can be
  discharged separately and by different layers.
* `h_trailF_lpack4` / `h_trailF_C4` — `H_trailF` from the sharpened residuals.

## What is still NAMED, and why

`H_lticks4` (the trace form of `LTickLeaves4`) keeps ten fields.  Three of them
are, as far as this layer can see, irreducible:

* `scanMargin` / `rewindMargin` — the machine stops a scan before the left head
  falls off the word, but `ScanInvariant` together with
  `GalilLiveCentre.Live` yields only `1 ≤ position L` (`scanInv_pos`): `Live`'s
  `n < 2*C` is `rad < C`, which is `0 < C - rad`, one short of what a left step
  needs.  The missing place is a property of the *machine's* stopping rule (an
  odd-length whole-prefix palindrome reports and restarts rather than compares),
  not of the invariant, so it cannot be recovered here.
* `shiftDoneScan` — the new centre's palindrome radius after a shift.  The
  intended proof is `GalilLiveCentreShift.leftmost_shift` from
  `GalilScaffoldChainReadOrigin.reshift_palindrome` and
  `GalilLiveCentreShift.live_shift_of_palAt`, but all three are statements about
  the *round*, not about the exiting tick.
* `mismatchMinv` — at a mismatched comparison the right head advances to
  `position R + 1`, so `MInv` has to be re-established there.  Off a replay this
  is `Leftmost w (position R + 1) (position C)`, which holds only while the
  centre survives; when it dies the route is the fallback's
  `GalilLiveCentreFallback.leftmost_after_fallback` / `minv_after_fallback`, and
  which of the two applies is decided by the entry guard, i.e. by the round.

The remaining fields (`initPack`, `scanInvR`, `scanCanR`, `shiftOneMinv`,
`choosePack`, `rewindPairMinv`, `replayPack`) are carried over verbatim from
`CloseoutLPack3.LTickLeaves`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutLPack4

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilThrottledRun PalPeg.GalilTrailProof PalPeg.GalilFinalAssembly
open PalPeg.CloseoutRadPack PalPeg.CloseoutRadPack2 PalPeg.CloseoutRadPack3
open PalPeg.CloseoutRadPack4 PalPeg.CloseoutLPack PalPeg.CloseoutLPack2
open PalPeg.CloseoutLPack3
open PalPeg.GalilRunSkeleton
open GalilScaffoldInputHead GalilScaffoldCounter

/-! ## 1. The origin corner is one inequality -/

/-- **A left step stays on the word exactly from place two.**  Forward
direction. -/
theorem left_pos_of_two {p : PlaceHead} (h : 2 ≤ position p) :
    0 < position (GalilScaffoldInputHead.left p) := by
  have hs := left_position_pos (p := p) (by omega)
  omega

/-- **A left step stays on the word exactly from place two.**  Converse. -/
theorem two_le_of_left_pos {p : PlaceHead}
    (h : 0 < position (GalilScaffoldInputHead.left p)) : 2 ≤ position p := by
  by_cases hp : 0 < position p
  · have hs := left_position_pos (p := p) hp
    omega
  · exfalso
    have hz : position p = 0 := by omega
    rcases p with ⟨⟨f, ls, rs, q⟩, g⟩
    cases g with
    | true =>
      have : ls.length = 0 := by
        simp only [position, if_true] at hz; omega
      have hnil : ls = [] := List.eq_nil_of_length_eq_zero this
      subst hnil
      simp [position, GalilScaffoldInputHead.left] at h
    | false =>
      have : ls.length ≤ 1 := by
        simp only [position, Bool.false_eq_true, if_false] at hz; omega
      interval_cases hn : ls.length
      · have hnil : ls = [] := List.eq_nil_of_length_eq_zero hn
        subst hnil
        simp [position, GalilScaffoldInputHead.left, moveLeft] at h
      · match ls, hn with
        | [a], _ => simp [position, GalilScaffoldInputHead.left, moveLeft] at h

/-- `0 < position (left p)` and `2 ≤ position p` are the same statement. -/
theorem left_pos_iff {p : PlaceHead} :
    0 < position (GalilScaffoldInputHead.left p) ↔ 2 ≤ position p :=
  ⟨two_le_of_left_pos, left_pos_of_two⟩

#print axioms left_pos_of_two
#print axioms two_le_of_left_pos

/-! ## 2. Inside a scan the inequality is a margin on the invariant -/

/-- The left head of a scan invariant sits at `C - rad`. -/
theorem scanInv_leftPos {w : List (Fin 2)} {C rad : ℕ} {l r : PlaceHead}
    (hi : ScanInvariant w C rad l r) : position l = C - rad := hi.leftPos

/-- **`2 ≤ position L` is `rad + 2 ≤ C`.**  The scan has not reached the
origin. -/
theorem margin_of_scanInv {w : List (Fin 2)} {C rad : ℕ} {l r : PlaceHead}
    (hi : ScanInvariant w C rad l r) (hm : rad + 2 ≤ C) : 2 ≤ position l := by
  rw [hi.leftPos]; omega

/-- **What liveness alone gives: `1 ≤ position L`.**  `Live w (position R) C`
carries `position R < 2*C`, i.e. `rad < C`, so the left head is on the word —
but one place short of what a further left step needs.  This is why
`scanMargin` below is a genuine leaf. -/
theorem scanInv_pos {w : List (Fin 2)} {C rad : ℕ} {l r : PlaceHead}
    (hi : ScanInvariant w C rad l r) : 1 ≤ position l := by
  have hlive := live_of_scanInvariant hi
  have h1 := hlive.2.1
  have hr := hi.rightPos
  rw [hi.leftPos]
  omega

#print axioms margin_of_scanInv
#print axioms scanInv_pos

/-! ## 3. Neither mismatch entry moves a head -/

/-- `beginShiftVM'` touches only `remaining`, `length`, `chain`, `cycle` and
`periodOnly`. -/
theorem beginShift_heads {s t : GalilVM} (hb : beginShiftVM' s t) :
    t.left = s.left ∧ t.center = s.center ∧ t.right = s.right ∧ t.replay = s.replay := by
  obtain ⟨wch, -, ht⟩ := hb
  refine ⟨by rw [ht], by rw [ht], by rw [ht], by rw [ht]⟩

/-- `beginFallbackVM'` touches only `fpp`, `chain` and `search`. -/
theorem beginFallback_heads {s t : GalilVM} (hb : beginFallbackVM' s t) :
    t.left = s.left ∧ t.center = s.center ∧ t.right = s.right ∧ t.replay = s.replay := by
  obtain ⟨pl, ht, -⟩ := hb
  refine ⟨by rw [ht], by rw [ht], by rw [ht], by rw [ht]⟩

/-- **`MInv` at either entry is `MInv` at the comparison's target.**  The
landing mode is irrelevant: `MInv` reads only `replaying`, and both entries
keep it. -/
theorem minv_of_mismatch {w : List (Fin 2)} {c c' : Control} {s t : GalilVM}
    (hr : c'.replaying = c.replaying)
    (hh : t.left = s.left ∧ t.center = s.center ∧ t.right = s.right ∧ t.replay = s.replay)
    (h : MInv w c s) : MInv w c' t :=
  minv_same hr hh.2.2.1 hh.2.1 hh.2.2.2 h

#print axioms beginShift_heads
#print axioms beginFallback_heads
#print axioms minv_of_mismatch

/-! ## 4. The sharpened leaves -/

section Leaves
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) the sharpened tick leaves.**  Compared with
`CloseoutLPack3.LTickLeaves`: `scanLeft` / `rewindLeft` are now pure arithmetic
(`left_pos_iff`), and `shiftMinv` / `fallbackMinv` have merged into the single
entry-free `mismatchMinv` (`minv_of_mismatch`). -/
structure LTickLeaves4 (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  /-- The `init` landing: the boot step establishes the whole pack. -/
  initPack : c.mode = Mode.init → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).init s t →
    LPack w {c with mode := Mode.scan, output := true} t
  /-- **The origin corner, as arithmetic.**  In `scan` the left head is at least
  two places from the origin, which by `margin_of_scanInv` is exactly
  `rad + 2 ≤ C` for the radius of `scanInvR` — a statement about the chain
  window, with no head shape left in it. -/
  scanMargin : c.mode = Mode.scan → ∀ r : ℕ,
    ScanInvariant w (position s.center) r s.left s.right → r + 2 ≤ position s.center
  /-- The same for a rewind unit. -/
  rewindMargin : c.mode = Mode.rewind → 2 ≤ position s.left
  /-- The scan invariant in `scan` mode, replays included. -/
  scanInvR : c.mode = Mode.scan →
    ∃ r, ScanInvariant w (position s.center) r s.left s.right
  /-- The right head can move in `scan` mode. -/
  scanCanR : c.mode = Mode.scan → GalilScaffoldChainVerifier.canRight s.right
  /-- **The mismatch landing.**  `MInv` at the target of a comparison, with no
  mention of which entry follows: both `beginShiftVM'` and `beginFallbackVM'`
  keep `L`, `C`, `R` and the replay counter. -/
  mismatchMinv : c.mode = Mode.scan → ∀ s'' : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).compare s s'' →
    MInv w {c with clock := 2048} s''
  /-- The centre invariant along a shift unit: `C` moves one place right. -/
  shiftOneMinv : c.mode = Mode.shift → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).shiftOne s t → MInv w c t
  /-- **The shift exit.**  The new centre's palindrome radius. -/
  shiftDoneScan : c.mode = Mode.shift →
    ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos s →
    ∃ r, ScanInvariant w (position s.center) r s.left s.right
  /-- `choose` re-centres on the right head. -/
  choosePack : c.mode = Mode.choose → c.odd = true → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).choose s t →
    (GalilScaffoldInputTrace.Represents t.left.head w ∧ t.left.head.focus ≠ none) ∧
      MInv w {c with mode := Mode.rewind, pair := false} t
  /-- The centre invariant along a paired rewind unit. -/
  rewindPairMinv : c.mode = Mode.rewind → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).rewindPair s t →
    MInv w {c with pair := false} t
  /-- `replayStart` resets all three heads onto the centre. -/
  replayPack : c.mode = Mode.replayStart → ∀ (t : GalilVM) (o : Bool),
    (galilFrameS (PofC centre place entry w) q first).replayStart s t →
    LPack w {c with mode := Mode.scan, clock := 2048, output := o, replaying := (galilFrameS (PofC centre place entry w) q first).replayPos t} t

/-- **The sharpened leaves imply the `CloseoutLPack3` ones.** -/
theorem lticks4 {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (h : LTickLeaves4 centre place entry q first w c s) :
    LTickLeaves centre place entry q first w c s where
  initPack := h.initPack
  scanLeft := fun hm => by
    obtain ⟨r, hi⟩ := h.scanInvR hm
    exact left_pos_of_two (margin_of_scanInv hi (h.scanMargin hm r hi))
  scanInvR := h.scanInvR
  scanCanR := h.scanCanR
  shiftMinv := fun hm s'' _ hcmp hb =>
    minv_of_mismatch (c := {c with clock := 2048}) rfl (beginShift_heads hb)
      (h.mismatchMinv hm s'' hcmp)
  fallbackMinv := fun hm s'' _ hcmp hb =>
    minv_of_mismatch (c := {c with clock := 2048}) rfl (beginFallback_heads hb)
      (h.mismatchMinv hm s'' hcmp)
  shiftOneMinv := h.shiftOneMinv
  shiftDoneScan := h.shiftDoneScan
  choosePack := h.choosePack
  rewindLeft := fun hm _ => left_pos_of_two (h.rewindMargin hm)
  rewindPairMinv := h.rewindPairMinv
  replayPack := h.replayPack

/-- **(NAMED) the sharpened leaves at every state of every pre-loaded trace.** -/
def H_lticks4 : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    ∀ i, i ≤ Tc w.length → LTickLeaves4 centre place entry q first w (st i).ctl (st i).vm

/-- `CloseoutLPack3.H_lticks` from the sharpened leaves. -/
theorem h_lticks_of_4 (h : H_lticks4 centre place entry q first) :
    H_lticks centre place entry q first :=
  fun w hw st Tc hP i hi => lticks4 centre place entry q first (h w hw st Tc hP i hi)

end Leaves

#print axioms lticks4
#print axioms h_lticks_of_4

/-! ## 5. Splitting the two shift-entry residuals -/

section Shift
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) the controller half of `H_shiftScan`**: the `scan_shift`
constructor's own `hm` and the non-replaying guard. -/
def H_shiftMode : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    ∀ i, i ≤ Tc w.length → ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
      beginShiftVM' s'' t'' →
      (st i).ctl.mode = Mode.scan ∧ (st i).ctl.replaying = false

/-- **(NAMED) the mobility half of `H_shiftScan`**: this is exactly
`LTickLeaves4.scanCanR` at a shift entry, i.e. `GalilTrailRad.canRight_of_pack_or`
against the tick's guard. -/
def H_shiftMove : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    ∀ i, i ≤ Tc w.length → ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
      beginShiftVM' s'' t'' →
      GalilScaffoldChainVerifier.canRight (st i).vm.right

/-- `H_shiftScan` is the conjunction of the two. -/
theorem h_shiftScan_of_parts (hm : H_shiftMode centre place entry q first)
    (hv : H_shiftMove centre place entry q first) :
    H_shiftScan centre place entry q first := by
  intro w hw st Tc hP i hi s'' t'' hcmp hb
  obtain ⟨h1, h2⟩ := hm w hw st Tc hP i hi s'' t'' hcmp hb
  exact ⟨h1, h2, hv w hw st Tc hP i hi s'' t'' hcmp hb⟩

/-- **(NAMED) the guard's place count**: `4h ≤ distance`, i.e.
`GalilCatchUpDistance.places_of_guard` applied to the shift guard's
`0 ≤ margin`. -/
def H_shiftGuardPlaces : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    ∀ i, i ≤ Tc w.length → ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
      beginShiftVM' s'' t'' →
      ∀ wch : GalilScaffoldChainWatch.State, s''.chain = .watch wch →
        4 * (periodLength wch : ℤ) ≤ value wch.machine.control.distance

/-- **(NAMED) the chain/scan coupling**: `distance ≤ 2·rad`.  The intended proof
is `GalilChainCoupling.Coupled.sum` together with
`GalilCatchUpDistance.distance_at_terminal`, which identify the chain's distance
with twice the scan radius at a terminal comparison. -/
def H_shiftCoupled : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    ∀ i, i ≤ Tc w.length → ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
      beginShiftVM' s'' t'' →
      ∀ wch : GalilScaffoldChainWatch.State, s''.chain = .watch wch →
        ∀ rad : ℕ,
          ScanInvariant w (position (st i).vm.center) rad (st i).vm.left (st i).vm.right →
          value wch.machine.control.distance ≤ 2 * (rad : ℤ)

/-- `H_shiftPlaces` is the conjunction of the two. -/
theorem h_shiftPlaces_of_parts (hg : H_shiftGuardPlaces centre place entry q first)
    (hc : H_shiftCoupled centre place entry q first) :
    H_shiftPlaces centre place entry q first := by
  intro w hw st Tc hP i hi s'' t'' hcmp hb wch hwch rad hscan
  exact ⟨hg w hw st Tc hP i hi s'' t'' hcmp hb wch hwch,
    hc w hw st Tc hP i hi s'' t'' hcmp hb wch hwch rad hscan⟩

end Shift

#print axioms h_shiftScan_of_parts
#print axioms h_shiftPlaces_of_parts

/-! ## 6. `H_trailF` from the sharpened residuals -/

section Final
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`H_trailF` from `H_lticks4` and the four split shift residuals.** -/
theorem h_trailF_lpack4 (hlt : H_lticks4 centre place entry q first)
    (hmo : H_shiftMode centre place entry q first)
    (hmv : H_shiftMove centre place entry q first)
    (hgp : H_shiftGuardPlaces centre place entry q first)
    (hcp : H_shiftCoupled centre place entry q first)
    (hcan : H_shiftCanRight centre place entry q first) :
    H_trailF centre place entry q first :=
  h_trailF_lpack3 centre place entry q first
    (h_lticks_of_4 centre place entry q first hlt)
    (h_shiftScan_of_parts centre place entry q first hmo hmv)
    (h_shiftPlaces_of_parts centre place entry q first hgp hcp)
    hcan

end Final

#print axioms h_trailF_lpack4

/-- **The concrete instance** at `centreC` / `placeC`. -/
theorem h_trailF_C4 (entry q : ℕ) (first : Fin 9)
    (hlt : H_lticks4 PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC
      entry q first)
    (hmo : H_shiftMode PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC
      entry q first)
    (hmv : H_shiftMove PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC
      entry q first)
    (hgp : H_shiftGuardPlaces PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC
      entry q first)
    (hcp : H_shiftCoupled PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC
      entry q first)
    (hcan : H_shiftCanRight PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC
      entry q first) :
    H_trailF PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC entry q first :=
  h_trailF_lpack4 _ _ entry q first hlt hmo hmv hgp hcp hcan

#print axioms h_trailF_C4

end PalPeg.CloseoutLPack4
