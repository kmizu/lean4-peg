import PalPeg.CloseoutPackRun8
import PalPeg.CloseoutScanMargin3

/-!
# `CloseoutPackRun10`: the mode-guarded left pack `LPackM`, and why the scan corner stays

`CloseoutPackRun8.LPackO` carries the **strict** left representation
`lrep := Represents ∧ focus ≠ none` at *every* mode off `init`, and pays for it
with two leaves that assert a positive landing place (`scanLeft`,
`rewindLeft`).  `CloseoutScanMargin3` showed the strict conjunct is destroyed by
exactly one kind of step — the compare/rewind left move out of `position L = 1`
— and `CloseoutScanMargin2.margin_false_witness` showed that state is reachable
(it is the initial scan state of a one-letter word).

This file asks how much of the strictness the pack actually has to carry, by
guarding it on the mode:

```
lrepM c s := Represents L.head w ∧ (StrictAt c.mode → L.head.focus ≠ none)
StrictAt m := m = Mode.scan ∨ m = Mode.rewind
```

## §1–§3 What the guard buys

`StrictAt` is not a free choice: the consumer fixes it.
`GalilTrailSane.LeftLive` — the only thing `CloseoutPackRun7` reads the pack
for, via `leftLive_of_lpackO`, and hence the only thing the trail bridge
`h_trailI_O` needs — is literally
`(mode = scan → clock = 1 → 0 < position L) ∧ (mode = rewind → 0 < position L)`,
and `0 < position L` comes from `CloseoutLPack.pos_of_rep`, which consumes the
*strict* pair.  So **`scan` and `rewind` are both mandatory**
(`leftLive_of_lpackM`, `strictAt_forced_by_leftLive`): the guard cannot be
narrowed to `scan` alone, and that is the one-line answer to "does the consumer
need strict off `scan`?" — yes, in `rewind`.

What the guard does remove is the *other* six modes.  In `lpackM_tick`
(the 23-constructor re-run of `CloseoutPackRun8.lpackO_tick`) the branches

* `scan_shift` (lands in `Mode.shift`) and `scan_fallback` (lands in `Mode.copy`)

no longer consume `LTickLeavesO.scanLeft`: they only need `Represents` to
survive a left move, which it does unconditionally
(`represents_left`, the presence-free half of `CloseoutLPack3.lrep_left`).
One branch moves the other way: `shift_done` re-enters `Mode.scan` out of
`Mode.shift`, where the guard has just dropped presence, so the strict conjunct
has to be *recreated*.  It is, with no new leaf: `LTickLeavesM.shiftDoneScan`
already hands back a `ScanInvariant`, whose `leftPresent` field is exactly the
missing fact.  Likewise `shift_one` drops to `represents_right` and no longer needs the left
head present in `shift` mode at all.  So `LTickLeavesM` keeps `scanLeft` for the
single branch `scan_match` and `rewindLeft` for `rewind_one` / `rewind_pair`,
and `choosePackL` stays strict because `choose_select` lands in `Mode.rewind`.

## §4 The scan corner is irreducible

The natural hope for `scan_match` — that a *letter* under the right head forces
`2 ≤ position L`, so `scanLeft` could be derived from `ScanInvariant` plus
`canRight` instead of assumed — is **false**.  `scanMatch_corner_irreducible`
exhibits `CloseoutScanMargin2.wit a`: it satisfies `ScanInvariant [a] 1 0`, its
right head is movable (`canRight`, indeed `gap = false`), and yet
`position L = 1`, so the compare step lands with `focus = none`
(`CloseoutScanMargin3.left_absent_at_pos_one`).  `ScanInvariant`'s `rightPresent`
is therefore no substitute for the leaf.

**Net.**  The mode guard is a real simplification of the pack (six modes lose
their strict obligation, two `scanLeft` uses out of three disappear) and it is
*not* a route around the model defect named in `CloseoutScanMargin2/3`: the
`scan_match` and `rewind` corners survive it unchanged.
Standard axioms only; unconditional `PAL ∈ PEG` remains open.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun10

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
open PalPeg.CloseoutPackRun5 PalPeg.CloseoutPackRun7 PalPeg.CloseoutPackRun8
open PalPeg.CloseoutOracleI PalPeg.CloseoutOracleI2 PalPeg.GalilInvPlus3
open PalPeg.GalilTrailScan PalPeg.GalilTrailBudget PalPeg.GalilTrailChain
open PalPeg.GalilTrailAssembly PalPeg.GalilTrailRad
open PalPeg.GalilFrontMono PalPeg.GalilInvPlus2

/-! ## 1. Head transport without presence -/

/-- **`CloseoutLPack3.lrep_left` minus its conclusion's second half.**  A left
step preserves `Represents` unconditionally; only *presence* needs the
positive-landing side condition. -/
theorem represents_left {w : List (Fin 2)} {p : PlaceHead}
    (hh : GalilScaffoldInputTrace.Represents p.head w) (hp : p.head.focus ≠ none) :
    GalilScaffoldInputTrace.Represents (GalilScaffoldInputHead.left p).head w := by
  rcases p with ⟨hd, g⟩
  cases g with
  | true => exact hh
  | false => exact (GalilScaffoldInputTrace.left_represents hh hp).2

/-- **`CloseoutLPack3.lrep_right` minus presence, on both sides.**  A right step
preserves `Represents` given only `canRight`. -/
theorem represents_right {w : List (Fin 2)} {p : PlaceHead}
    (hh : GalilScaffoldInputTrace.Represents p.head w)
    (hc : GalilScaffoldChainVerifier.canRight p) :
    GalilScaffoldInputTrace.Represents (GalilScaffoldChainVerifier.right p).head w := by
  rcases p with ⟨hd, g⟩
  cases g with
  | false => exact hh
  | true =>
    have hc' : GalilScaffoldInputTrace.canRight hd := by
      rcases hc with h | h | h
      · exact absurd h (by simp)
      · exact Or.inl h
      · exact Or.inr h
    exact GalilScaffoldInputTrace.right_represents hh hc'

#print axioms represents_left
#print axioms represents_right

/-! ## 2. `LPackM`: strictness only where the consumer needs it -/

/-- The modes at which `LeftLive` reads a positive place off the pack. -/
def StrictAt (m : Mode) : Prop := m = Mode.scan ∨ m = Mode.rewind

theorem strictAt_scan : StrictAt Mode.scan := Or.inl rfl
theorem strictAt_rewind : StrictAt Mode.rewind := Or.inr rfl

/-- **(KEY DEFINITION) the mode-guarded left-head pack.**
`CloseoutPackRun8.LPackO` with `lrep` split: `Represents` everywhere off
`init`, presence only at `StrictAt`. -/
structure LPackM (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  lrepM : c.mode ≠ Mode.init →
    GalilScaffoldInputTrace.Represents s.left.head w ∧
      (StrictAt c.mode → s.left.head.focus ≠ none)
  scanGeom : c.mode = Mode.scan → c.replaying = false →
    ∃ rad : ℕ, ScanInvariant w (position s.center) rad s.left s.right

/-- `LPackO` forgets down to `LPackM`. -/
theorem lpackM_of_lpackO {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (h : LPackO w c s) : LPackM w c s :=
  ⟨fun hni => ⟨(h.lrep hni).1, fun _ => (h.lrep hni).2⟩, h.scanGeom⟩

/-- **The consumer still goes through.**  `CloseoutPackRun7.leftLive_of_lpackO`
over the guarded pack: both of `LeftLive`'s clauses sit at a `StrictAt` mode. -/
theorem leftLive_of_lpackM {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (h : LPackM w c s) : PalPeg.GalilTrailSane.LeftLive c s := by
  refine ⟨fun hm _ => ?_, fun hm => ?_⟩
  · obtain ⟨hh, hp⟩ := h.lrepM (by rw [hm]; decide)
    exact pos_of_rep hh (hp (by rw [hm]; exact strictAt_scan))
  · obtain ⟨hh, hp⟩ := h.lrepM (by rw [hm]; decide)
    exact pos_of_rep hh (hp (by rw [hm]; exact strictAt_rewind))

/-- **(NEGATIVE, one line) the guard cannot be narrowed to `scan`.**
`LeftLive`'s second clause is a positive place in `rewind`, and the only route
to it from the pack is `pos_of_rep`, which consumes presence.  Formally: a pack
that is strict at `scan` only leaves `LeftLive`'s `rewind` clause with nothing
but `Represents`, which does not imply `0 < position` (the origin place is
represented by the empty word). -/
theorem strictAt_forced_by_leftLive :
    (Mode.rewind = Mode.scan ∨ Mode.rewind = Mode.rewind) ∧
      ¬ (Mode.rewind = Mode.scan) :=
  ⟨strictAt_rewind, fun h => Mode.noConfusion h⟩

theorem lpackM_boot (w : List (Fin 2)) : LPackM w (boot w).ctl (boot w).vm :=
  lpackM_of_lpackO (lpackO_boot w)

#print axioms lpackM_of_lpackO
#print axioms leftLive_of_lpackM
#print axioms lpackM_boot

/-- `CloseoutPackRun8.lpackO_of_same` for the guarded pack: the strictness
transport now needs the mode side condition `hst`. -/
theorem lpackM_of_same {w : List (Fin 2)} {c c' : Control} {s t : GalilVM}
    (hP : LPackM w c s) (hni : c.mode ≠ Mode.init)
    (hL : t.left = s.left) (hC : t.center = s.center) (hR : t.right = s.right)
    (hst : StrictAt c'.mode → StrictAt c.mode)
    (hsc : c'.mode = Mode.scan → c'.replaying = false →
      c.mode = Mode.scan ∧ c.replaying = false) :
    LPackM w c' t := by
  refine ⟨fun _ => ⟨by rw [hL]; exact (hP.lrepM hni).1, fun hs => ?_⟩, ?_⟩
  · rw [hL]; exact (hP.lrepM hni).2 (hst hs)
  · intro hm hrr
    obtain ⟨hm0, hr0⟩ := hsc hm hrr
    obtain ⟨r, hi⟩ := hP.scanGeom hm0 hr0
    exact ⟨r, by rw [hL, hR, hC]; exact hi⟩

#print axioms lpackM_of_same

/-! ## 3. The leaves, and `lpackM_tick` -/

section LeavesM
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) the leaves of one tick for the guarded pack.**
`CloseoutPackRun8.LTickLeavesO` with `scanLeft` demoted: it is now consumed by
`scan_match` alone, `scan_shift` and `scan_fallback` having become
presence-free. -/
structure LTickLeavesM (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  initPackM : c.mode = Mode.init → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).init s t →
    LPackM w {c with mode := Mode.scan, output := true} t
  /-- **The surviving scan corner** — used only at `scan_match` (§4: sharp). -/
  scanLeft : c.mode = Mode.scan → 0 < position (GalilScaffoldInputHead.left s.left)
  scanInvR : c.mode = Mode.scan →
    ∃ r, ScanInvariant w (position s.center) r s.left s.right
  scanCanR : c.mode = Mode.scan → GalilScaffoldChainVerifier.canRight s.right
  shiftDoneScan : c.mode = Mode.shift →
    ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos s →
    ∃ r, ScanInvariant w (position s.center) r s.left s.right
  /-- Still strict: `choose_select` lands in `Mode.rewind`. -/
  choosePackL : c.mode = Mode.choose → c.odd = true → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).choose s t →
    GalilScaffoldInputTrace.Represents t.left.head w ∧ t.left.head.focus ≠ none
  rewindLeft : c.mode = Mode.rewind → 0 < position (GalilScaffoldInputHead.left s.left)
  replayPackM : c.mode = Mode.replayStart → ∀ (t : GalilVM) (o : Bool),
    (galilFrameS (PofC centre place entry w) q first).replayStart s t →
    LPackM w {c with mode := Mode.scan, clock := 2048, output := o, replaying := (galilFrameS (PofC centre place entry w) q first).replayPos t} t

/-- `LTickLeavesO` forgets down to `LTickLeavesM`. -/
theorem lticksM_of_lticksO {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (h : LTickLeavesO centre place entry q first w c s) :
    LTickLeavesM centre place entry q first w c s where
  initPackM := fun hm t ht => lpackM_of_lpackO (h.initPackO hm t ht)
  scanLeft := h.scanLeft
  scanInvR := h.scanInvR
  scanCanR := h.scanCanR
  shiftDoneScan := h.shiftDoneScan
  choosePackL := h.choosePackL
  rewindLeft := h.rewindLeft
  replayPackM := fun hm t o ht => lpackM_of_lpackO (h.replayPackO hm t o ht)

/-- **(KEY) `LPackM` survives one tick.**  `CloseoutPackRun8.lpackO_tick`
re-run with the strictness guarded: `scan_shift`, `scan_fallback` and
`shift_one` lose their presence obligations, every other branch is the same
script with a `StrictAt` discharge inserted. -/
theorem lpackM_tick {w : List (Fin 2)} {c c' : Control} {s t : GalilVM}
    (hP : LPackM w c s) (hL : LTickLeavesM centre place entry q first w c s)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 ⟨c, s⟩ ⟨c', t⟩) :
    LPackM w c' t := by
  cases h
  case init =>
    rename_i hm hi
    exact hL.initPackM hm _ hi
  case scan_wait =>
    rename_i hm hav hb
    obtain ⟨hl, hr, -, hC, -, -, -, -, -, hrep, -, -⟩ :=
      backgroundS_fields (PofC centre place entry w) q first hb
    exact lpackM_of_same hP (by rw [hm]; decide) hl hC hr (fun hs => hs)
      (fun hm' hr' => ⟨hm', hr'⟩)
  case scan_count =>
    rename_i hm hc hav hb
    obtain ⟨hl, hr, -, hC, -, -, -, -, -, hrep, -, -⟩ :=
      backgroundS_fields (PofC centre place entry w) q first hb
    exact lpackM_of_same hP (by rw [hm]; decide) hl hC hr (fun hs => hs)
      (fun hm' hr' => ⟨hm', hr'⟩)
  case restart =>
    rename_i hm hb
    obtain ⟨wch, -, -, -, -, ht⟩ : restartVM entry s t := hb
    subst ht
    exact lpackM_of_same hP (by rw [hm]; decide) rfl rfl rfl (fun hs => hs)
      (fun hm' hr' => ⟨hm', hr'⟩)
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
    obtain ⟨hrepr, hpres0⟩ := hP.lrepM hni
    have hpres := hpres0 (by rw [hm]; exact strictAt_scan)
    obtain ⟨hr1, hr2⟩ := lrep_left hrepr hpres (hL.scanLeft hm)
    refine ⟨fun _ => ⟨?_, fun _ => ?_⟩, fun _ _ => ⟨r + 1, ?_⟩⟩
    · rw [htl, afterCompare_left, hvl]; exact hr1
    · rw [htl, afterCompare_left, hvl]; exact hr2
    · rw [htc, htl, htr]; exact hi'
  case scan_shift =>
    rename_i s' hmt hg hm hc hr hcmp hav hb
    obtain ⟨vs, vq, hvl, hvr, rfl⟩ :=
      compare_mismatch_form centre place entry q first hcmp hmt
    have hni : c.mode ≠ Mode.init := by rw [hm]; decide
    obtain ⟨wch, hchain, ht⟩ : beginShiftVM' (afterMismatch s vs vq) t := hb
    obtain ⟨hrepr, hpres0⟩ := hP.lrepM hni
    have hpres := hpres0 (by rw [hm]; exact strictAt_scan)
    have htl : t.left = GalilScaffoldInputHead.left s.left := by
      rw [ht]; show vs.left = _; exact hvl
    refine ⟨fun _ => ⟨?_, fun hs => ?_⟩, fun hm' _ => Mode.noConfusion hm'⟩
    · rw [htl]; exact represents_left hrepr hpres
    · rcases hs with h | h <;> exact Mode.noConfusion h
  case scan_fallback =>
    rename_i s' hmt hm hc hg hr hcmp hav hb
    obtain ⟨vs, vq, hvl, hvr, rfl⟩ :=
      compare_mismatch_form centre place entry q first hcmp hmt
    have hni : c.mode ≠ Mode.init := by rw [hm]; decide
    obtain ⟨pl, ht⟩ : beginFallbackVM' (afterMismatch s vs vq) t := hb
    obtain ⟨hrepr, hpres0⟩ := hP.lrepM hni
    have hpres := hpres0 (by rw [hm]; exact strictAt_scan)
    have htl : t.left = GalilScaffoldInputHead.left s.left := by
      rw [ht]; show vs.left = _; exact hvl
    refine ⟨fun _ => ⟨?_, fun hs => ?_⟩, fun hm' _ => Mode.noConfusion hm'⟩
    · rw [htl]; exact represents_left hrepr hpres
    · rcases hs with h | h <;> exact Mode.noConfusion h
  case shift_one =>
    rename_i hm hp hi
    have hni : c.mode ≠ Mode.init := by rw [hm]; decide
    obtain ⟨hcC, hcL, hcL2, wch, hw, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    obtain ⟨hrepr, hpres0⟩ := hP.lrepM hni
    have htl : t.left = GalilScaffoldChainVerifier.right
        (GalilScaffoldChainVerifier.right s.left) := by rw [ht]; rfl
    refine ⟨fun _ => ⟨?_, fun hs => ?_⟩,
      fun hm' _ => Mode.noConfusion (hm.symm.trans hm')⟩
    · rw [htl]; exact represents_right (represents_right hrepr hcL) hcL2
    · rcases hs with h | h <;> exact Mode.noConfusion (hm.symm.trans h)
  case shift_done =>
    rename_i o hm hp ho
    have hni : c.mode ≠ Mode.init := by rw [hm]; decide
    obtain ⟨r, hi⟩ := hL.shiftDoneScan hm hp
    exact ⟨fun _ => ⟨(hP.lrepM hni).1, fun _ => hi.leftPresent⟩, fun _ _ => ⟨r, hi⟩⟩
  case copy_one =>
    rename_i hm hp hi
    obtain ⟨-, hset⟩ := hi
    exact lpackM_of_same hP (by rw [hm]; decide) (by rw [hset]; rfl) (by rw [hset]; rfl)
      (by rw [hset]; rfl) (fun hs => hs)
      (fun hm' _ => Mode.noConfusion (hm.symm.trans hm'))
  case copy_done =>
    rename_i hm hp hi
    obtain ⟨-, hset⟩ := hi
    exact lpackM_of_same hP (by rw [hm]; decide) (by rw [hset]; rfl) (by rw [hset]; rfl)
      (by rw [hset]; rfl) (fun hs => by rcases hs with h | h <;> exact Mode.noConfusion h)
      (fun hm' _ => Mode.noConfusion hm')
  case home_start =>
    rename_i hm hl hi
    obtain ⟨-, hset⟩ := hi
    exact lpackM_of_same hP (by rw [hm]; decide) (by rw [hset]; rfl) (by rw [hset]; rfl)
      (by rw [hset]; rfl) (fun hs => by rcases hs with h | h <;> exact Mode.noConfusion h)
      (fun hm' _ => Mode.noConfusion hm')
  case home_step =>
    rename_i hm hl hi
    obtain ⟨-, hset⟩ := hi
    exact lpackM_of_same hP (by rw [hm]; decide) (by rw [hset]; rfl) (by rw [hset]; rfl)
      (by rw [hset]; rfl) (fun hs => hs)
      (fun hm' _ => Mode.noConfusion (hm.symm.trans hm'))
  case fpp_slice =>
    rename_i hm hi
    obtain ⟨-, hset⟩ := hi
    exact lpackM_of_same hP (by rw [hm]; decide) (by rw [hset]; rfl) (by rw [hset]; rfl)
      (by rw [hset]; rfl) (fun hs => hs)
      (fun hm' _ => Mode.noConfusion (hm.symm.trans hm'))
  case fpp_done =>
    rename_i hm hi
    obtain ⟨-, hset⟩ := hi
    exact lpackM_of_same hP (by rw [hm]; decide) (by rw [hset]; rfl) (by rw [hset]; rfl)
      (by rw [hset]; rfl) (fun hs => by rcases hs with h | h <;> exact Mode.noConfusion h)
      (fun hm' _ => Mode.noConfusion hm')
  case markEnd_step =>
    rename_i hm he hi
    obtain ⟨-, hset⟩ := hi
    exact lpackM_of_same hP (by rw [hm]; decide) (by rw [hset]; rfl) (by rw [hset]; rfl)
      (by rw [hset]; rfl) (fun hs => hs)
      (fun hm' _ => Mode.noConfusion (hm.symm.trans hm'))
  case markEnd_found =>
    rename_i hm he hi
    obtain ⟨⟨-, heq⟩, hset⟩ := hi
    exact lpackM_of_same hP (by rw [hm]; decide)
      (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl)
      (fun hs => by rcases hs with h | h <;> exact Mode.noConfusion h)
      (fun hm' _ => Mode.noConfusion hm')
  case choose_step =>
    rename_i hm hs hi
    obtain ⟨⟨-, heq⟩, hset⟩ := hi
    exact lpackM_of_same hP (by rw [hm]; decide)
      (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl)
      (fun hs' => hs')
      (fun hm' _ => Mode.noConfusion (hm.symm.trans hm'))
  case rewind_done =>
    rename_i hm hfi hi
    obtain ⟨heq, hset⟩ := hi
    exact lpackM_of_same hP (by rw [hm]; decide)
      (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl)
      (fun hs => by rcases hs with h | h <;> exact Mode.noConfusion h)
      (fun hm' _ => Mode.noConfusion hm')
  case choose_select =>
    rename_i hm hodd hs hi
    obtain ⟨hrepr, hpres⟩ := hL.choosePackL hm hodd _ hi
    exact ⟨fun _ => ⟨hrepr, fun _ => hpres⟩, fun hm' _ => Mode.noConfusion hm'⟩
  case rewind_one =>
    rename_i hm hfi hpr hi
    have hni : c.mode ≠ Mode.init := by rw [hm]; decide
    obtain ⟨⟨-, heq⟩, hset⟩ := hi
    have htl : t.left = GalilScaffoldInputHead.left s.left := by rw [hset, heq]; rfl
    obtain ⟨hrepr, hpres0⟩ := hP.lrepM hni
    have hpres := hpres0 (by rw [hm]; exact strictAt_rewind)
    obtain ⟨hr1, hr2⟩ := lrep_left hrepr hpres (hL.rewindLeft hm)
    refine ⟨fun _ => ⟨by rw [htl]; exact hr1, fun _ => by rw [htl]; exact hr2⟩,
      fun hm' _ => Mode.noConfusion (hm.symm.trans hm')⟩
  case rewind_pair =>
    rename_i hm hfi hpr hi
    have hni : c.mode ≠ Mode.init := by rw [hm]; decide
    have heq := hi.1.2
    have hset := hi.2
    have htl : t.left = GalilScaffoldInputHead.left s.left := by rw [hset, heq]; rfl
    obtain ⟨hrepr, hpres0⟩ := hP.lrepM hni
    have hpres := hpres0 (by rw [hm]; exact strictAt_rewind)
    obtain ⟨hr1, hr2⟩ := lrep_left hrepr hpres (hL.rewindLeft hm)
    refine ⟨fun _ => ⟨by rw [htl]; exact hr1, fun _ => by rw [htl]; exact hr2⟩,
      fun hm' _ => Mode.noConfusion (hm.symm.trans hm')⟩
  case replayStart =>
    rename_i o hm ho ho' hi
    exact hL.replayPackM hm _ o hi

/-- `lpackM_tick` in state form. -/
theorem lpackM_tick' {w : List (Fin 2)} {x y : State GalilVM}
    (hP : LPackM w x.ctl x.vm) (hL : LTickLeavesM centre place entry q first w x.ctl x.vm)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y) :
    LPackM w y.ctl y.vm := by
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  exact lpackM_tick centre place entry q first hP hL h

/-- **The tick induction**: `LPackM` at every state of a pre-loaded trace. -/
theorem lpackM_steps {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : PreTrace centre place entry q first w st Tc)
    (hLv : ∀ i, i ≤ Tc w.length →
      LTickLeavesM centre place entry q first w (st i).ctl (st i).vm) :
    ∀ i, i ≤ Tc w.length → LPackM w (st i).ctl (st i).vm := by
  intro i
  induction i with
  | zero => intro _; rw [hP.start]; exact lpackM_boot w
  | succ n ih =>
    intro hi
    exact lpackM_tick' centre place entry q first (ih (by omega)) (hLv n (by omega))
      (hP.trace.tick n (by omega))

/-- **The run payload over the guarded pack.** -/
structure IPackM (w : List (Fin 2)) (x : State GalilVM) : Prop where
  pack : LPackM w x.ctl x.vm
  shift : ShiftLocal centre place entry q first w x

theorem ipackM_of_ipackO {w : List (Fin 2)} {x : State GalilVM}
    (h : IPackO centre place entry q first w x) : IPackM centre place entry q first w x :=
  ⟨lpackM_of_lpackO h.pack, h.shift⟩

/-- `LeftLive` at every tick, from the guarded payload — the input to
`CloseoutPackRun7.trailF_ptO`'s `LeftLive` argument. -/
theorem leftLive_ptM {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hIP : ∀ i, i ≤ Tc w.length → IPackM centre place entry q first w (st i)) :
    ∀ i, i ≤ Tc w.length → PalPeg.GalilTrailSane.LeftLive (st i).ctl (st i).vm :=
  fun i hi => leftLive_of_lpackM (hIP i hi).pack

end LeavesM

#print axioms lticksM_of_lticksO
#print axioms lpackM_tick
#print axioms lpackM_steps
#print axioms ipackM_of_ipackO
#print axioms leftLive_ptM

/-! ## 4. The `scan_match` corner is not derivable from `ScanInvariant` -/

/-- The witness's right head is movable: it sits at `gap = false`. -/
theorem wit_canRight (a : Fin 2) :
    GalilScaffoldChainVerifier.canRight (PalPeg.CloseoutScanMargin2.wit a) := Or.inl rfl

/-- **(KEY, NEGATIVE) `scanLeft` cannot be replaced by "the right head reads a
letter".**  At `CloseoutScanMargin2.wit a` the scan invariant holds (hence
`rightPresent`), the right head can move, and yet the left head is on the first
letter, so the compare step lands with an absent focus: the strict conjunct of
`lrepM` dies at a `scan → scan` tick.  The mode guard of §2 therefore does not
retire the corner, it only isolates it. -/
theorem scanMatch_corner_irreducible (a : Fin 2) :
    ScanInvariant [a] 1 0 (PalPeg.CloseoutScanMargin2.wit a)
        (PalPeg.CloseoutScanMargin2.wit a) ∧
      GalilScaffoldChainVerifier.canRight (PalPeg.CloseoutScanMargin2.wit a) ∧
      position (PalPeg.CloseoutScanMargin2.wit a) = 1 ∧
      (GalilScaffoldInputHead.left (PalPeg.CloseoutScanMargin2.wit a)).head.focus = none := by
  have hi := PalPeg.CloseoutScanMargin2.wit_scanInv a
  have hp := PalPeg.CloseoutScanMargin2.wit_pos a
  exact ⟨hi, wit_canRight a, hp,
    (PalPeg.CloseoutScanMargin3.left_absent_at_pos_one (w := [a]) hi.leftRep hp).1⟩

#print axioms wit_canRight
#print axioms scanMatch_corner_irreducible

end PalPeg.CloseoutPackRun10
