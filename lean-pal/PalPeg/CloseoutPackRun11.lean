import PalPeg.PackedRun
import PalPeg.CloseoutScanMargin4

/-!
# `CloseoutPackRun11`: the `scan_match` origin corner, retired

`CloseoutPackRun10` isolated the strictness of the left-head pack to the two
modes its consumer needs (`LPackM`, `StrictAt = scan ∨ rewind`) and left
`LTickLeavesM.scanLeft` — `0 < position (left L)` at *every* `scan` state — as a
leaf, with §4 (`scanMatch_corner_irreducible`) recording that it does **not**
follow from `ScanInvariant` plus `canRight`: at `CloseoutScanMargin2.wit a` the
invariant holds, the right head moves, and `position L = 1`.

That negative result is about the *unguarded* leaf, and `CloseoutScanMargin4`
(written after it) shows the guarded one is a theorem: the only branch of
`lpackM_tick` that consumes `scanLeft` is `scan_match`, and a matched
comparison at `position L = 1` is impossible, because the post-step left head
is on the origin (`read = none`) while the right head reads a real cell
(`read ≠ none`).  So the corner is not a leaf at all — it is derivable *inside
the branch that uses it*, from data the branch already has.

* §1 `LTickLeavesN` — `LTickLeavesM` with `scanLeft` **deleted** (eight fields
  become seven).
* §2 `lpackN_tick` (KEY) — `CloseoutPackRun10.lpackM_tick` re-run over the
  smaller leaf set.  Twenty-two of the twenty-three branches are the same
  script; `scan_match` replaces `hL.scanLeft hm` by
  `CloseoutScanMargin4.scanLeft_of_scanInv hi hcan hmatch`, where `hi` comes
  from `scanInvR`, `hcan` from `scanCanR` and `hmatch` is the very equality of
  readings that `CloseoutLPack3.compare_matched_form` extracts from the
  constructor's own `matched` hypothesis.
* §3 `lpackN_tick'`, `lpackN_steps` — the state form and the tick induction.
* §4 `Extra'` — `CloseoutPackRun3.Extra` with the **refuted** `scanMargin`
  field removed (`CloseoutScanMargin2.scanMargin_refuted`: `r + 2 ≤ C` fails at
  the initial scan state of a one-letter word, so any pack carrying it is
  unsatisfiable and every theorem hypothesising it is vacuous).  `rewindMargin`
  stays: nothing here refutes it, and `rewind_one` / `rewind_pair` still
  consume it with no matched comparison in sight.
* §5 `BigPack2M` / `BigResid6` / `lticksN_of_big6` / `bigPack2M_tick` — the
  `CloseoutPackRun8.§3` packaging re-cut over the guarded pack and `Extra'`.

## Honest status

Standard axioms only; unconditional `PAL ∈ PEG` remains open, and this file
does **not** reach `pal_in_peg_final13`: `CloseoutPackRun9`'s `StepsIO` family
(`ReachAtIO`, `CycleOutIO`, `CycleOracleIO`, `PreTraceIO`, `pal_in_peg_final5O`)
and `CloseoutPackRun8.packRunR_O` all mention `IPackO` positively, so replacing
the producer by the guarded `IPackM` forces one more transcript of that family
before `final12` can be restated over `BigResid6`.  What is closed here is the
obstruction that made the restatement worth doing: with `scanLeft` gone and
`scanMargin` gone, the residual no longer contains a refuted field.

Residual after this file: the six `BigResid6` contracts (`rInitPackM`,
`rScanInvR`, `rShiftDoneScan`, `rChoosePackL`, `rReplayPackM`, `rShiftNext`),
the rewind corner (`Extra'.rewindMargin`, consumed only by `rewind_one` /
`rewind_pair`), `H_extraEntry'` / `H_extraTick'`, and — unchanged —
`H_shiftLocalC`, `H_stageScan`, `CycleOracleMC3`, `H_bootShift`, `H_landShift`,
`H_realizeLIO'`, plus the `IPackM` re-cut of the `StepsIO` family.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun11

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
open PalPeg.CloseoutPackRun10
open PalPeg.CloseoutOracleI PalPeg.CloseoutOracleI2 PalPeg.GalilInvPlus3
open PalPeg.GalilTrailScan PalPeg.GalilTrailBudget PalPeg.GalilTrailChain
open PalPeg.GalilTrailAssembly PalPeg.GalilTrailRad
open PalPeg.GalilFrontMono PalPeg.GalilInvPlus2

/-! ## 1. `LTickLeavesN`: the leaves without the scan corner -/

section LeavesN
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) the leaves of one tick, scan corner deleted.**
`CloseoutPackRun10.LTickLeavesM` minus `scanLeft`. -/
structure LTickLeavesN (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  initPackN : c.mode = Mode.init → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).init s t →
    LPackM w {c with mode := Mode.scan, output := true} t
  scanInvR : c.mode = Mode.scan →
    ∃ r, ScanInvariant w (position s.center) r s.left s.right
  scanCanR : c.mode = Mode.scan → GalilScaffoldChainVerifier.canRight s.right
  shiftDoneScan : c.mode = Mode.shift →
    ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos s →
    ∃ r, ScanInvariant w (position s.center) r s.left s.right
  choosePackL : c.mode = Mode.choose → c.odd = true → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).choose s t →
    GalilScaffoldInputTrace.Represents t.left.head w ∧ t.left.head.focus ≠ none
  /-- **The surviving corner**: `rewind` has no comparison to lean on. -/
  rewindLeft : c.mode = Mode.rewind →
    ¬ (galilFrameS (PofC centre place entry w) q first).atFirst s →
    0 < position (GalilScaffoldInputHead.left s.left)
  replayPackN : c.mode = Mode.replayStart → ∀ (t : GalilVM) (o : Bool),
    (galilFrameS (PofC centre place entry w) q first).replayStart s t →
    LPackM w {c with mode := Mode.scan, clock := 2048, output := o, replaying := (galilFrameS (PofC centre place entry w) q first).replayPos t} t

/-- `LTickLeavesM` forgets down to `LTickLeavesN`. -/
theorem lticksN_of_lticksM {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (h : LTickLeavesM centre place entry q first w c s) :
    LTickLeavesN centre place entry q first w c s where
  initPackN := h.initPackM
  scanInvR := h.scanInvR
  scanCanR := h.scanCanR
  shiftDoneScan := h.shiftDoneScan
  choosePackL := h.choosePackL
  rewindLeft := fun hm _ => h.rewindLeft hm
  replayPackN := h.replayPackM

/-! ## 2. `lpackN_tick` -/

/-- **(KEY) `LPackM` survives one tick without the scan corner.**
`CloseoutPackRun10.lpackM_tick` re-run over `LTickLeavesN`: only the
`scan_match` branch changes, where the margin is now derived from the matched
reading by `CloseoutScanMargin4.scanLeft_of_scanInv`. -/
theorem lpackN_tick {w : List (Fin 2)} {c c' : Control} {s t : GalilVM}
    (hP : LPackM w c s) (hL : LTickLeavesN centre place entry q first w c s)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 ⟨c, s⟩ ⟨c', t⟩) :
    LPackM w c' t := by
  cases h
  case init =>
    rename_i hm hi
    exact hL.initPackN hm _ hi
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
    obtain ⟨r, hi⟩ := hL.scanInvR hm
    have hi' := matched_invariant' w vq hvl hvr hmatch hcan hi
    obtain ⟨hrepr, hpres0⟩ := hP.lrepM hni
    have hpres := hpres0 (by rw [hm]; exact strictAt_scan)
    obtain ⟨hr1, hr2⟩ := lrep_left hrepr hpres
      (CloseoutScanMargin4.scanLeft_of_scanInv hi hcan hmatch)
    refine ⟨fun _ => ⟨?_, fun _ => ?_⟩, fun _ _ => ⟨r + 1, ?_⟩⟩
    · rw [htl, afterBirth_left, afterCompare_left, hvl]; exact hr1
    · rw [htl, afterBirth_left, afterCompare_left, hvl]; exact hr2
    · rw [htc, htl, htr, afterBirth_left, afterBirth_right]; exact hi'
  case scan_shift =>
    rename_i s' hmt hg hm hc hr hcmp hav hb
    obtain ⟨vs, vq, hvl, hvr, rfl⟩ :=
      compare_mismatch_form centre place entry q first hcmp hmt
    have hni : c.mode ≠ Mode.init := by rw [hm]; decide
    obtain ⟨wch, hchain, ht⟩ :
      beginShiftVM' (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterMismatch s vs vq)) t := hb
    obtain ⟨hrepr, hpres0⟩ := hP.lrepM hni
    have hpres := hpres0 (by rw [hm]; exact strictAt_scan)
    have htl : t.left = GalilScaffoldInputHead.left s.left := by
      rw [ht, afterBirth_left, afterMismatch_left]; exact hvl
    refine ⟨fun _ => ⟨?_, fun hs => ?_⟩, fun hm' _ => Mode.noConfusion hm'⟩
    · rw [htl]; exact represents_left hrepr hpres
    · rcases hs with h | h <;> exact Mode.noConfusion h
  case scan_fallback =>
    rename_i s' hmt hm hc hg hr hcmp hav hb
    obtain ⟨vs, vq, hvl, hvr, rfl⟩ :=
      compare_mismatch_form centre place entry q first hcmp hmt
    have hni : c.mode ≠ Mode.init := by rw [hm]; decide
    obtain ⟨pl, ht⟩ :
      beginFallbackVM' (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterMismatch s vs vq)) t := hb
    obtain ⟨hrepr, hpres0⟩ := hP.lrepM hni
    have hpres := hpres0 (by rw [hm]; exact strictAt_scan)
    have htl : t.left = GalilScaffoldInputHead.left s.left := by
      rw [ht, afterBirth_left, afterMismatch_left]; exact hvl
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
    obtain ⟨hr1, hr2⟩ := lrep_left hrepr hpres (hL.rewindLeft hm (by assumption))
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
    obtain ⟨hr1, hr2⟩ := lrep_left hrepr hpres (hL.rewindLeft hm (by assumption))
    refine ⟨fun _ => ⟨by rw [htl]; exact hr1, fun _ => by rw [htl]; exact hr2⟩,
      fun hm' _ => Mode.noConfusion (hm.symm.trans hm')⟩
  case replayStart =>
    rename_i o hm ho ho' hi
    exact hL.replayPackN hm _ o hi


/-- `lpackN_tick` in state form. -/
theorem lpackN_tick' {w : List (Fin 2)} {x y : State GalilVM}
    (hP : LPackM w x.ctl x.vm) (hL : LTickLeavesN centre place entry q first w x.ctl x.vm)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y) :
    LPackM w y.ctl y.vm := by
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  exact lpackN_tick centre place entry q first hP hL h

/-- **The tick induction over the smaller leaf set.** -/
theorem lpackN_steps {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : PreTrace centre place entry q first w st Tc)
    (hLv : ∀ i, i ≤ Tc w.length →
      LTickLeavesN centre place entry q first w (st i).ctl (st i).vm) :
    ∀ i, i ≤ Tc w.length → LPackM w (st i).ctl (st i).vm :=
  hP.trace.carried (Pk := fun z => LPackM w z.ctl z.vm)
    (by rw [hP.start]; exact lpackM_boot w)
    (fun n hn ht hp => lpackN_tick' centre place entry q first hp (hLv n (by omega)) ht)

end LeavesN

#print axioms lticksN_of_lticksM
#print axioms lpackN_tick
#print axioms lpackN_tick'
#print axioms lpackN_steps

/-! ## 4. `Extra'`: the enlargement minus the refuted field -/

section ExtraP
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) `CloseoutPackRun3.Extra` without `scanMargin`.**  Five fields.
`scanMargin` is not merely unproved but false at a reachable state
(`CloseoutScanMargin2.scanMargin_refuted`), and §2 shows nothing needs it: the
`scan_match` branch that bought it derives its own margin. -/
structure Extra' (w : List (Fin 2)) (x : State GalilVM) : Prop where
  ready : PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get x.vm)
  failed : x.ctl.mode = Mode.scan →
    PalPeg.GalilLeafDp.StageFailed (PofC centre place entry w) w x.vm
      (GalilScaffoldCounter.value x.vm.radius).toNat
  cand : x.ctl.mode = Mode.shift →
    ∃ lower h, PalPeg.GalilDpSuffix.Candidate
      (GalilScaffoldPlace.stream ((PofC centre place entry w).place x.vm)) lower h
  /-- **The surviving margin.**  `rewind_one` / `rewind_pair` walk `L` left with
  no comparison to certify the landing. -/
  rewindMargin : x.ctl.mode = Mode.rewind → 2 ≤ position x.vm.left
  scanAvail : x.ctl.mode = Mode.scan → x.ctl.replaying = false →
    GalilScaffoldChainVerifier.canRight x.vm.right

/-- `Extra` forgets down to `Extra'`. -/
theorem extra'_of_extra {w : List (Fin 2)} {x : State GalilVM}
    (h : Extra centre place entry w x) : Extra' centre place entry w x :=
  ⟨h.ready, h.failed, h.cand, h.rewindMargin, h.scanAvail⟩

/-- **(NAMED) `Extra'` at an `InvLPC` origin.** -/
def H_extraEntry' (w : List (Fin 2)) : Prop :=
  ∀ (c : Control) (r : GalilVM), InvLPC w c r → Extra' centre place entry w ⟨c, r⟩

/-- **(NAMED) `Extra'` travels along one tick.** -/
def H_extraTick' (w : List (Fin 2)) : Prop :=
  ∀ x y : State GalilVM, Extra' centre place entry w x →
    Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y →
    Extra' centre place entry w y

/-- `CloseoutPackRun8.canR_of_partsO` over `Extra'` (it never read
`scanMargin`). -/
theorem canR_of_partsM {w : List (Fin 2)} {x : State GalilVM}
    (hf : FrontPack x.ctl x.vm) (he : Extra' centre place entry w x)
    (hm : x.ctl.mode = Mode.scan) : GalilScaffoldChainVerifier.canRight x.vm.right := by
  cases hrep : x.ctl.replaying with
  | true => exact PalPeg.GalilTrailRad.replayCan_of_pack hf hrep
  | false => exact he.scanAvail hm hrep

end ExtraP

#print axioms extra'_of_extra
#print axioms canR_of_partsM

/-! ## 5. The packaging over the guarded pack -/

section ResidM
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **The guarded enlarged pack.**  `CloseoutPackRun8.BigPack2O` with `IPackO`
replaced by `CloseoutPackRun10.IPackM` and `Extra` by `Extra'`. -/
structure BigPack2M (w : List (Fin 2)) (x : State GalilVM) : Prop where
  ipackM : IPackM centre place entry q first w x
  aux : AuxPack x.ctl x.vm
  live : CentreLive x.ctl x.vm
  extra : Extra' centre place entry w x

/-- `BigPack2O` forgets down to `BigPack2M`. -/
theorem bigPack2M_of_bigPack2O {w : List (Fin 2)} {x : State GalilVM}
    (h : BigPack2O centre place entry q first w x) :
    BigPack2M centre place entry q first w x :=
  ⟨ipackM_of_ipackO centre place entry q first h.ipackO, h.aux, h.live,
    extra'_of_extra centre place entry h.extra⟩

/-- **(NAMED) the residual over the guarded pack — six fields.**
`CloseoutPackRun8.BigResid5O` with `LPackO` weakened to `LPackM` and the
hypothesis weakened to `BigPack2M`. -/
structure BigResid6 (w : List (Fin 2)) : Prop where
  rInitPackM : ∀ x : State GalilVM, BigPack2M centre place entry q first w x →
    x.ctl.mode = Mode.init → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).init x.vm t →
    LPackM w {x.ctl with mode := Mode.scan, output := true} t
  rScanInvR : ∀ x : State GalilVM, BigPack2M centre place entry q first w x →
    x.ctl.mode = Mode.scan →
    ∃ r, ScanInvariant w (position x.vm.center) r x.vm.left x.vm.right
  rShiftDoneScan : ∀ x : State GalilVM, BigPack2M centre place entry q first w x →
    x.ctl.mode = Mode.shift →
    ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos x.vm →
    ∃ r, ScanInvariant w (position x.vm.center) r x.vm.left x.vm.right
  rChoosePackL : ∀ x : State GalilVM, BigPack2M centre place entry q first w x →
    x.ctl.mode = Mode.choose → x.ctl.odd = true → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).choose x.vm t →
    GalilScaffoldInputTrace.Represents t.left.head w ∧ t.left.head.focus ≠ none
  rReplayPackM : ∀ x : State GalilVM, BigPack2M centre place entry q first w x →
    x.ctl.mode = Mode.replayStart → ∀ (t : GalilVM) (o : Bool),
    (galilFrameS (PofC centre place entry w) q first).replayStart x.vm t →
    LPackM w {x.ctl with mode := Mode.scan, clock := 2048, output := o, replaying := (galilFrameS (PofC centre place entry w) q first).replayPos t} t
  rShiftNext : ∀ x y : State GalilVM, BigPack2M centre place entry q first w x →
    Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y →
    SoundScanNR w y → ShiftLocal centre place entry q first w y

/-- **The seven leaves from the six contracts plus `Extra'`.**  Compared with
`CloseoutPackRun8.lticksO_of_big5O`: `scanLeft` has no clause at all (§2), and
`rewindLeft` is the only place a margin is still read. -/
theorem lticksN_of_big6 {w : List (Fin 2)} (hr : BigResid6 centre place entry q first w)
    {x : State GalilVM} (hx : BigPack2M centre place entry q first w x) :
    LTickLeavesN centre place entry q first w x.ctl x.vm where
  initPackN := hr.rInitPackM x hx
  scanInvR := hr.rScanInvR x hx
  scanCanR := fun hm => canR_of_partsM centre place entry hx.aux.front hx.extra hm
  shiftDoneScan := hr.rShiftDoneScan x hx
  choosePackL := hr.rChoosePackL x hx
  rewindLeft := fun hm _ => left_pos_of_two (hx.extra.rewindMargin hm)
  replayPackN := hr.rReplayPackM x hx

/-- **One tick of the guarded enlarged pack.**
`CloseoutPackRun8.bigPack2O_tick` over `BigResid6`. -/
theorem bigPack2M_tick {w : List (Fin 2)} (hr : BigResid6 centre place entry q first w)
    (het : H_extraTick' centre place entry q first w)
    {x y : State GalilVM} (hx : BigPack2M centre place entry q first w x)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hg : SoundScanNR w y) (hlv : CentreLive y.ctl y.vm) :
    BigPack2M centre place entry q first w y := by
  refine ⟨⟨?_, hr.rShiftNext x y hx h hg⟩,
    auxPack_tick centre place entry q first hx.aux hx.live h, hlv,
    het x y hx.extra h⟩
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  exact lpackN_tick centre place entry q first hx.ipackM.pack
    (lticksN_of_big6 centre place entry q first hr hx) h

end ResidM

#print axioms bigPack2M_of_bigPack2O
#print axioms lticksN_of_big6
#print axioms bigPack2M_tick

end PalPeg.CloseoutPackRun11
