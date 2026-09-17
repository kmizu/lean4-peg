import PalPeg.CloseoutPackRun6

/-!
# `CloseoutPackRun7`: the origin relaxation is refuted, and `MInv` leaves the pack

`CloseoutPackRun6` closed two of the thirteen residuals and left a worry on the
table: the origin margins (`CloseoutPackRun3.Extra.scanMargin` /
`rewindMargin`, equivalently `CloseoutLPack5.LTickLeavesG.scanLeft`) demand
`2 ≤ position L`, while a prefix that is *entirely* a palindrome drives the
left head onto the origin gap cell (`position = 0`, `focus = none`), where the
strict `lrep := Represents ∧ focus ≠ none` — and with it
`GalilTrailSane.LeftLive` — is **false**.  The proposed repair was to relax the
field to

```
lrepO := Represents ∧ (focus ≠ none ∨ position = 0)
```

and to carry an origin-permitting `LeftLiveO` through the `TrailF` chain.

This file settles that proposal, and separates the two questions it conflated.

## §1–§2 The relaxation is *vacuous*, and the budget half of the worry is real

`lrepO` is not a weakening at all: under `Represents`, the disjunct
`focus ≠ none ∨ position = 0` is a **theorem** (`focus_or_origin`), because a
represented head is `layout xs rs qs` and `xs = []` forces `focus = none` *and*
`position = 0` in both gap parities.  So `lrepO` is literally `Represents`
(`lrepO_iff_represents`), and `position = 0 ↔ focus = none` under `Represents`
(`origin_iff_absent`).  Relaxing `lrep` to `lrepO` therefore **deletes the
`focus ≠ none` conjunct outright** rather than guarding it.

The half of the worry that *is* sound is the budget half: consumption is blind
to the origin.  `GalilThrottledRun.usedPH n p = n - |p.head.incoming|` depends
only on the FIFO, and `GalilScaffoldInputHead.left` preserves `incoming` in
every one of its four shapes, so `usedPH_left : usedPH n (left p) = usedPH n p`
holds **unconditionally** — at the origin and everywhere else.  The left head's
`usedPH` accounting in `GalilTrailProof.needL'_le_of_trailF` is therefore
untouched by the origin, exactly as the proposal predicted.  But that was never
where `LeftLive` was consumed.

## §3 Where `LeftLive` is really consumed, and why the origin kills it

`GalilTrailSane.LeftLive` is read by `GalilTrailSane.sane3_tick` at the three
comparison ticks (`scan_match`, `scan_shift`, `scan_fallback`) and at `rewind`,
each time through `GalilTrailSane.sane_leftE`, i.e.
`GalilFrontMono.left_sane : 0 < position p → Sane (left p)`.  The sharp form of
that lemma is proved here:

* `sane_left_of_gap_false` — if `p.gap = false` then `Sane (left p)` holds
  **unconditionally**: the left step flips the parity to `gap = true`, and
  `GalilFrontMono.Sane` is `gap = true ∨ 0 < |left|`.  No positivity is needed.
* `sane_left_gap_iff` — if `p.gap = true` then `Sane (left p) ↔ 0 < position p`,
  because the left step keeps the stack and clears the gap bit.
* `not_sane_left_of_origin_gap` — hence at a gap head with an empty stack, i.e.
  **exactly the origin gap cell**, `Sane (left p)` is false.

So the left move out of the origin gap cell is an illegal head move (this is
Scala's `require` on `InputHead.left`), and the origin cell itself is perfectly
`Sane` (`sane_of_origin_gap`): the state is legal, its left successor is not.

**Verdict (`origin_refutes_leftLiveO`).**  An origin-permitting `LeftLiveO`
cannot feed `sane3_tick`.  `CloseoutPackRun6`'s worry is confirmed as a genuine
conflict, but the resolution is the opposite of the one proposed: `lrep` must
*stay* strict, and the machine fact that has to be supplied is that a scan
comparison never fires with the left head on the origin gap cell — which is
precisely `scanMargin`.  `CloseoutLPack4.scanInv_pos` already records that
liveness alone gives only `1 ≤ position L`, one place short; this file shows
that the missing place is not bookkeeping slack but the difference between a
legal and an illegal head move.

## §4 `MInv` leaves the pack for real

The second, independent goal is met without any origin question.  `LPackO` is
`CloseoutLPack5.LPackG` **with `minvG` deleted** — just `lrep` and the scan
geometry `scanGeom` (`L = C - rad`, `R = C + rad`, plus the four
representation fields of `ScanInvariant`; no `Manacher.PalAt`).  `IPackO` is
`LPackO` plus `ShiftLocal`, and the entire `CloseoutPackRun5` §2 trail bridge
re-runs over it verbatim — `leftLive_ptO`, `halfBound_of_ipackO`,
`shiftEntry_ptO`, `shiftVerSane_ptO`, `radPack_ptO`, `trailF_ptO` — ending in
`h_trailI_O : H_trailI_O`, from which `CloseoutLPack5.H_trailI` follows
(`h_trailI_of_O`).  This makes the audit's observation that "nothing downstream
reads `LPack.minv`" into a theorem: the trail chain never mentions the centre
invariant, so `MInvG` is dead weight in the *trail* direction.

## Honest status of goals (2) and (3)

`MInv` is removed from the pack on the trail side only.  The two remaining
pieces are named, not proved:

* **`lpackO_tick`** (23 constructors + boot).  `CloseoutLPack5.lpackG_tick`
  cannot be reused: it consumes `LPackG`, and `LPackO` does not supply
  `minvG`.  The induction has to be re-run with the `minv` corners deleted.
  *Missing fact*: none — this is mechanical, but it is a fresh 23-case `Tick`
  induction over `CloseoutLPack3`'s script, not a corollary.
* **`packRunR_O` / `pal_in_peg_final12`**.  These need `lpackO_tick` first.  The
  contract list would then be `BigResid5G` minus `rShiftDoneMinv` (the one the
  `MInvG` re-cut *added*) and minus the `MInv` half of `rReplayPackG` and
  `rInitPackG`, i.e. **five** contracts: `rInitPackO`, `rScanInvR`,
  `rShiftDoneScan`, `rChoosePackL`, `rReplayPackO`, `rShiftNext`, plus
  `H_extraEntry` / `H_extraTick` / `H_shiftLocalC` / `H_stageScan` /
  `H_oracle` / `H_realizeLI'` unchanged, and `H_bootShift` / `H_landShift`
  already discharged in `CloseoutPackRun6`.  The `scanMargin` leaf refuted
  above survives inside `Extra` in every one of these lists.

Standard axioms only.  Unconditional `PAL ∈ PEG` remains open.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun7

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
open PalPeg.CloseoutOracleI PalPeg.CloseoutOracleI2
open PalPeg.GalilTrailScan PalPeg.GalilTrailBudget PalPeg.GalilTrailChain
open PalPeg.GalilTrailAssembly PalPeg.GalilTrailRad

abbrev PH := GalilScaffoldInputHead.PlaceHead

/-! ## 1. `lrepO` is `Represents`: the origin disjunct is free -/

/-- **A represented head is either present or at the origin.**  `layout xs rs q`
with `xs = []` has `focus = none`, an empty left stack and hence
`position = 0` in *both* gap parities (`2*0` and `2*0-1` are both `0` in `ℕ`);
with `xs = a :: _` it has `focus = some a`. -/
theorem focus_or_origin {p : PH} {w : List (Fin 2)}
    (hr : GalilScaffoldInputTrace.Represents p.head w) :
    p.head.focus ≠ none ∨ position p = 0 := by
  rcases p with ⟨h, g⟩
  obtain ⟨xs, rs, qs, rfl, rfl⟩ := hr
  cases xs with
  | nil => right; cases g <;> simp [position, layout]
  | cons a xs => left; simp [layout]

/-- **The origin-permitting left-head field.**  This is the relaxation
`CloseoutPackRun6` proposed for `CloseoutLPack5.LPackG.lrep`. -/
def lrepO (w : List (Fin 2)) (p : PH) : Prop :=
  GalilScaffoldInputTrace.Represents p.head w ∧ (p.head.focus ≠ none ∨ position p = 0)

/-- **(KEY, negative) `lrepO` is not a weakening of `lrep`: it is
`Represents` alone.**  The added disjunct is a consequence of the first
conjunct, so relaxing `lrep` to `lrepO` deletes `focus ≠ none` rather than
guarding it. -/
theorem lrepO_iff_represents {w : List (Fin 2)} {p : PH} :
    lrepO w p ↔ GalilScaffoldInputTrace.Represents p.head w :=
  ⟨fun h => h.1, fun h => ⟨h, focus_or_origin h⟩⟩

/-- Under `Represents`, sitting at the origin and having no focus are the same
condition. -/
theorem origin_iff_absent {p : PH} {w : List (Fin 2)}
    (hr : GalilScaffoldInputTrace.Represents p.head w) :
    position p = 0 ↔ p.head.focus = none := by
  constructor
  · intro hz
    by_contra hf
    exact absurd hz (by have := pos_of_rep hr hf; omega)
  · intro hf
    rcases focus_or_origin hr with h | h
    · exact absurd hf h
    · exact h

#print axioms focus_or_origin
#print axioms lrepO_iff_represents
#print axioms origin_iff_absent

/-! ## 2. The budget half of the worry: `usedPH` is origin-blind -/

/-- **(KEY) a left step consumes nothing, at the origin or anywhere else.**
`GalilThrottledRun.usedPH n p = n - |p.head.incoming|` reads only the FIFO, and
`GalilScaffoldInputHead.left` preserves `incoming` in all four shapes (gap set:
the head is untouched; gap clear: `moveLeft` either returns the head unchanged
or rebuilds it with the same `incoming`).  This is the whole content of
"the left head does not read at the origin" for the trail budget. -/
theorem usedPH_left (n : ℕ) (p : PH) :
    usedPH n (GalilScaffoldInputHead.left p) = usedPH n p := by
  rcases p with ⟨⟨f, ls, rs, qs⟩, g⟩
  cases g <;> cases ls <;> simp [usedPH, GalilScaffoldInputHead.left, moveLeft]

#print axioms usedPH_left

/-! ## 3. Where the origin really bites: `Sane` of the left successor -/

/-- **A left step out of a letter cell is always legal.**  `left` flips the
parity to `gap = true`, and `GalilFrontMono.Sane` accepts any gap head.  No
positivity hypothesis is involved, so `GalilTrailSane.sane_leftE`'s
`0 < position p` is *only* needed at gap heads. -/
theorem sane_left_of_gap_false {p : PH} (hg : p.gap = false) :
    GalilFrontMono.Sane (GalilScaffoldInputHead.left p) := by
  rcases p with ⟨h, g⟩
  cases g
  · exact Or.inl rfl
  · exact absurd hg (by simp)

/-- **At a gap cell the left step is legal exactly off the origin.**  `left`
keeps the stack and clears the gap bit, so `Sane` degenerates to
`0 < |left| = 0 < position p`. -/
theorem sane_left_gap_iff {p : PH} (hg : p.gap = true) :
    GalilFrontMono.Sane (GalilScaffoldInputHead.left p) ↔ 0 < position p := by
  rcases p with ⟨⟨f, ls, rs, qs⟩, g⟩
  cases g
  · exact absurd hg (by simp)
  · simp only [position, if_true, GalilScaffoldInputHead.left,
      GalilFrontMono.Sane, Bool.not_true, Bool.false_eq_true, false_or]
    omega

/-- **(KEY, negative) the left step out of the origin gap cell is illegal.** -/
theorem not_sane_left_of_origin_gap {p : PH} (hg : p.gap = true) (hz : position p = 0) :
    ¬ GalilFrontMono.Sane (GalilScaffoldInputHead.left p) := by
  rw [sane_left_gap_iff hg, hz]; omega

/-- **The origin gap cell is itself perfectly legal.**  The conflict is not that
the machine reaches an insane state; it is that its *next* left move would
leave the word. -/
theorem sane_of_origin_gap {p : PH} (hg : p.gap = true) : GalilFrontMono.Sane p :=
  Or.inl hg

#print axioms sane_left_of_gap_false
#print axioms sane_left_gap_iff
#print axioms not_sane_left_of_origin_gap
#print axioms sane_of_origin_gap

/-- **The verdict on `CloseoutPackRun6`'s proposal.**  Stated so that it can be
read without unfolding anything: if a state's left head is on the origin gap
cell, then the head-sanity conclusion that `GalilTrailSane.sane3_tick` draws at
every comparison tick and at every `rewind` tick is *false* at that state.
Hence no origin-permitting `LeftLiveO` can replace
`GalilTrailSane.LeftLive` in the `TrailF` chain, and `lrep` must stay strict. -/
theorem origin_refutes_leftLiveO {s : GalilVM} (hg : s.left.gap = true)
    (hz : position s.left = 0) {t : GalilVM}
    (ht : t.left = GalilScaffoldInputHead.left s.left) :
    ¬ GalilFrontMono.Sane t.left := by
  rw [ht]; exact not_sane_left_of_origin_gap hg hz

/-- The same statement in the shape the `Extra` margins use: at the origin gap
cell, `CloseoutLPack5.LTickLeavesG.scanLeft` fails, and by
`CloseoutLPack4.left_pos_iff` so does `CloseoutPackRun3.Extra.scanMargin`. -/
theorem scanLeft_false_of_origin_gap {p : PH} (hg : p.gap = true) (hz : position p = 0) :
    ¬ (0 < position (GalilScaffoldInputHead.left p)) := by
  rcases p with ⟨⟨f, ls, rs, qs⟩, g⟩
  cases g
  · exact absurd hg (by simp)
  · simp only [position, if_true] at hz
    have hnil : ls = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil
    simp [position, GalilScaffoldInputHead.left]

#print axioms origin_refutes_leftLiveO
#print axioms scanLeft_false_of_origin_gap

/-! ## 4. `LPackO`: the pack with `MInv` deleted -/

/-- **The `MInv`-free left-head pack.**  `CloseoutLPack5.LPackG` without
`minvG`: the strict left-head representation off `init`, plus the scan
geometry.  `scanGeom` is `ScanInvariant`, whose content at this point is the
head arithmetic `L = C - rad`, `R = C + rad` and the four representation
fields; it carries no `Manacher.PalAt`, so it is preserved shift-locally. -/
structure LPackO (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  lrep : c.mode ≠ Mode.init →
    GalilScaffoldInputTrace.Represents s.left.head w ∧ s.left.head.focus ≠ none
  scanGeom : c.mode = Mode.scan → c.replaying = false →
    ∃ rad : ℕ, ScanInvariant w (position s.center) rad s.left s.right

/-- `LPackG` forgets down to `LPackO`. -/
theorem lpackO_of_lpackG {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (h : LPackG w c s) : LPackO w c s := ⟨h.lrep, h.scanInv⟩

/-- `LeftLive` is read off the `MInv`-free pack; it only ever used `lrep`. -/
theorem leftLive_of_lpackO {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (h : LPackO w c s) : PalPeg.GalilTrailSane.LeftLive c s := by
  refine ⟨fun hm _ => ?_, fun hm => ?_⟩
  · obtain ⟨hh, hp⟩ := h.lrep (by rw [hm]; decide)
    exact pos_of_rep hh hp
  · obtain ⟨hh, hp⟩ := h.lrep (by rw [hm]; decide)
    exact pos_of_rep hh hp

/-- The boot state, where both fields are vacuous. -/
theorem lpackO_boot (w : List (Fin 2)) : LPackO w (boot w).ctl (boot w).vm :=
  lpackO_of_lpackG (lpackG_boot w)

#print axioms lpackO_of_lpackG
#print axioms leftLive_of_lpackO
#print axioms lpackO_boot

section PackO
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **The `MInv`-free run payload**: `LPackO` plus `CloseoutLPack5.ShiftLocal`. -/
structure IPackO (w : List (Fin 2)) (x : State GalilVM) : Prop where
  pack : LPackO w x.ctl x.vm
  shift : ShiftLocal centre place entry q first w x

theorem ipackO_of_ipack {w : List (Fin 2)} {x : State GalilVM}
    (h : IPack centre place entry q first w x) : IPackO centre place entry q first w x :=
  ⟨lpackO_of_lpackG h.pack, h.shift⟩

end PackO

#print axioms ipackO_of_ipack

/-! ## 5. The trail bridge over `IPackO` -/

section TrailO
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `LeftLive` at every tick, from the `MInv`-free pack. -/
theorem leftLive_ptO {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hIP : ∀ i, i ≤ Tc w.length → IPackO centre place entry q first w (st i)) :
    ∀ i, i ≤ Tc w.length → PalPeg.GalilTrailSane.LeftLive (st i).ctl (st i).vm :=
  fun i hi => leftLive_of_lpackO (hIP i hi).pack

/-- **`CloseoutPackRun5.halfBound_of_ipackG` over `IPackO`.**  `4h ≤ distance ≤ 2·rad`. -/
theorem halfBound_of_ipackO {w : List (Fin 2)} {x : State GalilVM}
    (hx : IPackO centre place entry q first w x) {s'' t'' : GalilVM}
    (hcmp : (galilFrameS (PofC centre place entry w) q first).compare x.vm s'')
    (hb : beginShiftVM' s'' t'') :
    ∃ rad : ℕ,
      ScanInvariant w (position x.vm.center) rad x.vm.left x.vm.right ∧
      GalilScaffoldChainVerifier.canRight x.vm.right ∧
      ∀ wch : GalilScaffoldChainWatch.State, s''.chain = .watch wch →
        2 * periodLength wch ≤ rad := by
  obtain ⟨hmode, hrep⟩ := hx.shift.mode s'' t'' hcmp hb
  obtain ⟨rad, hscan⟩ := hx.pack.scanGeom hmode hrep
  refine ⟨rad, hscan, hx.shift.move s'' t'' hcmp hb, fun wch hch => ?_⟩
  have h4 : 4 * (periodLength wch : ℤ) ≤
      GalilScaffoldCounter.value wch.machine.control.distance :=
    hx.shift.guard s'' t'' hcmp hb wch hch
  have h2 : GalilScaffoldCounter.value wch.machine.control.distance ≤ 2 * (rad : ℤ) :=
    hx.shift.coupled s'' t'' hcmp hb wch hch rad hscan
  omega

/-- **`CloseoutPackRun5.shiftEntry_ptG` over `IPackO`.** -/
theorem shiftEntry_ptO {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hIP : ∀ i, i ≤ Tc w.length → IPackO centre place entry q first w (st i)) :
    ∀ i, i ≤ Tc w.length → ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
      beginShiftVM' s'' t'' → ShiftBud t'' := by
  intro i hi s'' t'' hcmp hb
  obtain ⟨rad, hscan, hcan, hh⟩ :=
    halfBound_of_ipackO centre place entry q first (hIP i hi) hcmp hb
  exact shiftBud_of_scanInv (onLetterVM w) leftFirstVM centre place entry q first
    hscan hcan hcmp hb hh

/-- **`CloseoutPackRun5.shiftVerSane_ptG` over `IPackO`.** -/
theorem shiftVerSane_ptO {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hIP : ∀ i, i ≤ Tc w.length → IPackO centre place entry q first w (st i)) :
    ∀ i, i ≤ Tc w.length → ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
      beginShiftVM' s'' t'' → SaneVer t''.chain :=
  fun i hi s'' t'' hcmp hb =>
    saneVer_beginShift hb ((hIP i hi).shift.ver s'' t'' hcmp hb)

/-- **`CloseoutPackRun5.radPack_ptG` over `IPackO`.** -/
theorem radPack_ptO {w : List (Fin 2)} (hw : 0 < w.length) {st : ℕ → State GalilVM}
    {Tc : ℕ → ℕ} (hP : PreTrace centre place entry q first w st Tc)
    (hIP : ∀ i, i ≤ Tc w.length → IPackO centre place entry q first w (st i)) :
    ∀ i, i ≤ Tc w.length → RadPack (st i).ctl (st i).vm := by
  have hll := leftLive_ptO centre place entry q first hIP
  have hen := shiftEntry_ptO centre place entry q first hIP
  have hsv := shiftVerSane_ptO centre place entry q first hIP
  have hL := radLedger_pt centre place entry q first hw hP hll
  have hS := shiftOrd_pt centre place entry q first hw hP hll hen
  have hV := verSane_pt centre place entry q first hw hP hll hsv
  exact fun i hi => radPack_of_parts (hL i hi) (hS i hi) (hll i hi) (hV i hi)

/-- **`CloseoutPackRun5.trailF_ptG` over `IPackO`.** -/
theorem trailF_ptO {w : List (Fin 2)} (hw : 0 < w.length) {st : ℕ → State GalilVM}
    {Tc : ℕ → ℕ} (hP : PreTrace centre place entry q first w st Tc)
    (hIP : ∀ i, i ≤ Tc w.length → IPackO centre place entry q first w (st i))
    {m : ℕ} (hm : m < w.length) :
    ∀ i, i ≤ Tc (m+1) → TrailF w m (st i) := by
  have hll := leftLive_ptO centre place entry q first hIP
  have hsane := sanePack_pt centre place entry q first hw hP hll
  have hrad := radPack_ptO centre place entry q first hw hP hIP
  have hscan := scanT_pt centre place entry q first hw hP hrad hsane hm
  have hB := chainBudget_pt centre place entry q first hw hP hrad hsane hm
  have hV := verF_trace centre place entry q first hP hm hscan hB
  exact fun i hi => trailF_of_scanT (hscan i hi) (hV i hi).ver (hV i hi).lagPos

/-- **(NAMED-FREE) `CloseoutLPack5.H_trailI` with the `MInv`-free payload.** -/
def H_trailI_O : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    (∀ i, i ≤ Tc w.length → IPackO centre place entry q first w (st i)) →
    ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) → TrailF w m (st i)

/-- **(KEY) the trail bridge never reads the centre invariant.** -/
theorem h_trailI_O : H_trailI_O centre place entry q first :=
  fun _ hw _ _ hP hIP _ hm i hi =>
    trailF_ptO centre place entry q first hw hP hIP hm i hi

/-- **`CloseoutLPack5.H_trailI` is a corollary**: deleting `minvG` from the pack
costs nothing on the trail side. -/
theorem h_trailI_of_O : H_trailI centre place entry q first :=
  fun w hw st Tc hP hIP m hm i hi =>
    h_trailI_O centre place entry q first w hw st Tc hP
      (fun j hj => ipackO_of_ipack centre place entry q first (hIP j hj)) m hm i hi

end TrailO

#print axioms leftLive_ptO
#print axioms halfBound_of_ipackO
#print axioms shiftEntry_ptO
#print axioms shiftVerSane_ptO
#print axioms radPack_ptO
#print axioms trailF_ptO
#print axioms h_trailI_O
#print axioms h_trailI_of_O

end PalPeg.CloseoutPackRun7
