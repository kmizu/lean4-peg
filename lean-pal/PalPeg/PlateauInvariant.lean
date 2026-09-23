import PalPeg.PhysicalDpHistory
import PalPeg.OracleReady
import PalPeg.CountersCanonicalTrace
import PalPeg.BranchSupply

/-!
# The ticks after the last report point

After its last letter the local layer keeps ticking until the window of that letter ends.  The
trace stops at the last report point, so the ticks beyond it have to be built: the abstract
successor must *exist*, or the ghost of the proof stalls and loses the physical machine.

The run is the first piece of what the oracle would do for one more letter: count ticks until the
clock is `1`, then the comparison, which moves the right head off the word.  The readiness leaves
of the oracle apply at the last report point as they are: their bounds are
`position right ≤ 2·|w| − 1` and `position right + 1 < |encoded w|`.

`PlateauInv` is closed under one tick (`plateauStep`): a count tick lands in it again
(`backgroundS_exists`, `Tick.scan_count`, `ShapedRun.restartGuard_background`), the comparison
(`plateauCompare`) lands with the right head at `2·|w|`.  It carries what a section of the
abstraction needs (`GhostSection.ghostOf`): canonical counters, `replay = reset` (so the parked
form of the right head is trivial), the span ledger and a nonnegative radius.
-/

set_option autoImplicit false
namespace PalPeg.PlateauInvariant

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilRunSkeleton PalPeg.GalilInvPlus3
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
  PalPeg.GalilStructuredSkeleton PalPeg.GalilTraceCost PalPeg.ShapedRun
open PalPeg.CloseoutPackW PalPeg.CloseoutPackRun2 PalPeg.GalilTickFun
open PalPeg.CountersCanonicalTrace (AllCanonical ChainLastCan allCanonical_tick chainLastCan_vmTick)

/-- One place to the right of the last letter is the place after the word. -/
theorem position_right_of_atLast {p : PlaceHead} {n : ℕ} (hn : 0 < n)
    (h : position p = 2 * n - 1) :
    position (GalilScaffoldChainVerifier.right p) = 2 * n := by
  rcases p with ⟨⟨f, ls, rs, qs⟩, g⟩
  cases g with
  | true => simp only [position, if_true] at h; omega
  | false =>
    simp only [position, Bool.false_eq_true, if_false] at h
    simp only [position, GalilScaffoldChainVerifier.right, Bool.false_eq_true, if_false,
      Bool.not_false, if_true]
    omega


variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- The comparison at clock `1` out of the last report point.  Some canonical tick
exists, and it moves the right head off the word. -/
theorem plateauCompare {w : List (Fin 2)} (hP : Decodes (PofC centre place entry w))
    (hq : 0 < q) (h7 : first ≠ 7) (h8 : first ≠ 8)
    {c₀ : Control} {r₀ : GalilVM} (hI₀ : InvLPS (PofC centre place entry w) q first w c₀ r₀)
    {c : Control} {t : GalilVM} {k kS : ℕ}
    (hrun : PalPeg.CloseoutCheckW.StepsIMWC centre place entry q first w k ⟨c₀, r₀⟩ ⟨c, t⟩)
    (hshaped : ShapedSteps centre place entry q first w kS ⟨c₀, r₀⟩ ⟨c, t⟩)
    (hm : c.mode = .scan) (hr : c.replaying = false) (hclock : c.clock = 1)
    (hnoGuard : ¬ restartGuardVM t) (hav : canRight t.right) (hminv : MInv w c t)
    (hbound : position t.right + 1 < (encoded w).length) :
    ∃ y : State GalilVM,
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 ⟨c, t⟩ y ∧
      PalPeg.GalilTickFair.Canonical entry 2048 ⟨c, t⟩ y ∧
      y.vm.right = right t.right := by
  classical
  have hsearch : ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry w) a t v := by
    intro a
    by_cases hidle : t.chain = .idle
    · exact PalPeg.GalilBranchInvariants2.searchEffect_exists _ a t
        (PalPeg.OracleReady.searchReady_of_invLPS_shaped centre place entry q first hI₀ hshaped hm)
    · exact ⟨searchLens.get t, Or.inr ⟨hidle, rfl⟩⟩
  have hchainT : ChainReady t.chain := by
    have hp := PalPeg.CloseoutCheckW.ipackMW_last_of_stepsIMWC centre place entry q first hrun
    exact PalPeg.CanonicalChainReady.of_window (hp.win hP)
      (PalPeg.CanonicalChainReady.copyReady_packed centre place entry q first hI₀
        (fun j z hz => PalPeg.CanonicalSearchHistory.birthCopy_packed centre place entry q
          first hP hI₀ hz) hrun) hbound
  rcases PalPeg.OracleRun.scanCompare_cases centre place entry q first c t hm hclock hr hav
      hsearch hchainT with ⟨-, vq, z, o, -, -, -, htick⟩ | ⟨hmis, vq, z, u, -, -, hshift | hfallback⟩
  · exact ⟨_, htick, PalPeg.GalilTickFair.canonical_of_scan_nonCopy hm
      (fun h => Mode.noConfusion (hm.symm.trans h)) hnoGuard, by
        show (afterBirth _ (afterCompare t ⟨left t.left, right t.right, z⟩ vq)).right = _
        rw [afterBirth_right, afterCompare_right]⟩
  · obtain ⟨-, hbegin, htick⟩ := hshift
    obtain ⟨watch, -, hu⟩ : beginShiftVM' _ u := hbegin
    exact ⟨_, htick, PalPeg.GalilTickFair.canonical_of_scan_nonCopy hm
      (fun h => Mode.noConfusion h) hnoGuard, by
        show u.right = _
        rw [hu]
        show (afterBirth _ (afterMismatch t ⟨left t.left, right t.right, z⟩ vq)).right = _
        rw [afterBirth_right, afterMismatch_right]⟩
  · obtain ⟨-, hticks⟩ := hfallback
    obtain ⟨hbegin, hwalker, -⟩ :=
      PalPeg.CanonicalFallbackInput.begin_at_mismatch centre place entry q first hI₀ hrun hm hr hav
        hminv hmis hq h7 h8 vq z
    refine ⟨_, hticks _ hbegin, PalPeg.GalilTickFair.canonical_of_scan_copy hm hnoGuard hwalker, ?_⟩
    show (beginFallbackAt _ (afterBirth _ (afterMismatch t ⟨left t.left, right t.right, z⟩ vq))).right
      = _
    show (afterBirth _ (afterMismatch t ⟨left t.left, right t.right, z⟩ vq)).right = _
    rw [afterBirth_right, afterMismatch_right]


/-- **The invariant of the ticks after the last report point.**  A scan state of the
packed run, not replaying, below the restart guard, with its right head on the last letter; and
the facts a section of the abstraction needs. -/
structure PlateauInv (w : List (Fin 2)) (x : State GalilVM) : Prop where
  scan : x.ctl.mode = .scan
  notReplaying : x.ctl.replaying = false
  clockPos : 1 ≤ x.ctl.clock
  noGuard : ¬ restartGuardVM x.vm
  atLast : position x.vm.right = 2 * w.length - 1
  minv : MInv w x.ctl x.vm
  sound : SoundScanNR w x
  onRun : ∃ (c₀ : Control) (r₀ : GalilVM) (k kS : ℕ),
    InvLPS (PofC centre place entry w) q first w c₀ r₀ ∧
    PalPeg.CloseoutCheckW.StepsIMWC centre place entry q first w k ⟨c₀, r₀⟩ x ∧
    ShapedSteps centre place entry q first w kS ⟨c₀, r₀⟩ x
  counters : AllCanonical x.vm
  chainLast : ChainLastCan x.vm.chain
  replayReset : x.vm.replay = reset
  span : SpanRep x.vm
  radiusNonneg : 0 ≤ value x.vm.radius
  /-- The DP bank a reset would retire is dense. -/
  dpDense : PalPeg.PhysicalDpHistory.DpHistory (searchLens.get x.vm)

/-- **One tick on the plateau.**  A canonical tick exists; it lands in the invariant
again (a count tick), or it moves the right head off the word (the comparison). -/
theorem plateauStep {w : List (Fin 2)} (hP : Decodes (PofC centre place entry w))
    (h4 : first ≠ 4) (hq : 0 < q) (h7 : first ≠ 7) (h8 : first ≠ 8) (hw : 0 < w.length)
    {x : State GalilVM} (hinv : PlateauInv centre place entry q first w x) :
    ∃ y : State GalilVM,
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y ∧
      PalPeg.GalilTickFair.Canonical entry 2048 x y ∧
      (PlateauInv centre place entry q first w y ∨ 2 * w.length ≤ position y.vm.right) := by
  classical
  obtain ⟨c, s⟩ := x
  obtain ⟨hm, hr, hclockPos, hnoGuard, hat, hminv, hQ, ⟨c₀, r₀, k, kS, hI₀, hrun, hshaped⟩,
    hcounters, hchainLast, hreplay, hspan, hradius, hdp⟩ := hinv
  have hm' : c.mode = .scan := hm
  have hr' : c.replaying = false := hr
  have hpack : IPackMW centre place entry q first w ⟨c, s⟩ :=
    PalPeg.CloseoutCheckW.ipackMW_last_of_stepsIMWC centre place entry q first hrun
  obtain ⟨hrep, hpres⟩ := PalPeg.WindowPack.rightHead_of_packs hpack.pack hpack.m2 hm'
  have hlength : (encoded w).length = 2 * w.length + 1 := by simp [encoded, pairs_length]
  have hat' : position s.right = 2 * w.length - 1 := hat
  have hav : canRight s.right := canRight_of_bound _ w hrep hpres (by omega)
  have hbound : position s.right + 1 < (encoded w).length := by omega
  by_cases hclock : c.clock = 1
  · -- the comparison
    obtain ⟨y, htick, hcanonical, hright⟩ :=
      plateauCompare centre place entry q first hP hq h7 h8 hI₀ hrun hshaped hm' hr' hclock
        hnoGuard hav hminv hbound
    refine ⟨y, htick, hcanonical, Or.inr ?_⟩
    rw [hright, position_right_of_atLast hw hat']
  · -- a count tick
    have hchainReady : ChainReady s.chain :=
      PalPeg.CanonicalChainReady.of_window (hpack.win hP)
        (PalPeg.CanonicalChainReady.copyReady_packed centre place entry q first hI₀
          (fun j z hz => PalPeg.CanonicalSearchHistory.birthCopy_packed centre place entry q
            first hP hI₀ hz) hrun) hbound
    have hsearch : ∃ v, searchEffect (PofC centre place entry w) false s v := by
      by_cases hidle : s.chain = .idle
      · exact PalPeg.GalilBranchInvariants2.searchEffect_exists _ false s
          (PalPeg.OracleReady.searchReady_of_invLPS_shaped centre place entry q first hI₀
            hshaped hm')
      · exact ⟨searchLens.get s, Or.inr ⟨hidle, rfl⟩⟩
    have hchainAt : ∀ v : SearchVM, ∃ z, chainAt false (decide (v.search.mode = .found))
        (v.dp.config.tapes 11) ((PofC centre place entry w).centre s)
        ((PofC centre place entry w).place s) s.center s.radius s.chain z :=
      fun v => chainAt_exists false _ _ _ _ _ _ s.chain hchainReady
    obtain ⟨s', hb⟩ := backgroundS_exists (PofC centre place entry w) q first s hsearch hchainAt
    have hav' : (galilFrameS (PofC centre place entry w) q first).available s := hav
    have hclockPos' : 1 ≤ c.clock := hclockPos
    have htick : Tick (galilFrameS (PofC centre place entry w) q first) 2048 ⟨c, s⟩
        ⟨{c with clock := c.clock - 1}, s'⟩ :=
      Tick.scan_count c s s' hm' (Or.inr hav') (by omega) hb
    obtain ⟨hleft, hright, -, hcenter, -, hrad, hlen, -, -, hrep', -, -⟩ :=
      backgroundS_fields (PofC centre place entry w) q first hb
    have hcanonical : PalPeg.GalilTickFair.Canonical entry 2048 ⟨c, s⟩
        ⟨{c with clock := c.clock - 1}, s'⟩ :=
      PalPeg.GalilTickFair.canonical_of_scan_nonCopy hm'
        (by show c.mode ≠ Mode.copy; rw [hm']; decide) hnoGuard
    have hQ' : SoundScanNR w ⟨{c with clock := c.clock - 1}, s'⟩ := fun _ hr0 =>
      outputRel_background w (PofC centre place entry w) q first hb rfl (hQ hm' hr0)
    have hnr : ¬ restartVM entry s s' :=
      PalPeg.ShapedRun.not_restartVM_background centre place entry q first hb
    have horacle : OracleTick entry w ⟨c, s⟩ ⟨{c with clock := c.clock - 1}, s'⟩ :=
      oracleTick_of_noGuard hcanonical hm' hnoGuard
    obtain ⟨g, hg0, hgk, htr, -, -⟩ := id hrun
    have hjx : Steps (galilFrameS (PofC centre place entry w) q first) 2048 k ⟨c₀, r₀⟩ ⟨c, s⟩ := by
      have := PalPeg.CloseoutPackRun2.steps_of_trace htr k le_rfl
      rwa [hg0, hgk] at this
    have hone : StepsAllR (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w)
        (OracleTick entry w) 1 ⟨c, s⟩ ⟨{c with clock := c.clock - 1}, s'⟩ :=
      .succ hQ htick horacle (.zero _ hQ')
    have hrun' := PalPeg.CloseoutCheckW.stepsIMWC_trans centre place entry q first hrun
      (PalPeg.CloseoutMarksPack.packRunR_MWR_marksFree centre place entry q first h4 hP
        (OracleTick entry w) c₀ r₀ hI₀ w.length hw le_rfl k ⟨c, s⟩ hjx 1
        ⟨{c with clock := c.clock - 1}, s'⟩ hpack hone hr'
        (by show position s'.right ≤ 2 * w.length - 1; rw [hright]; omega))
    have hshaped' := PalPeg.ShapedRun.shapedSteps_trans centre place entry q first hshaped
      (.succ htick (fun _ hr0 => (hnr hr0).elim)
        (fun h => absurd (hm'.symm.trans h) (by decide)) (.zero _))
    refine ⟨⟨{c with clock := c.clock - 1}, s'⟩, htick, hcanonical, Or.inl ?_⟩
    exact {
      scan := hm'
      notReplaying := hr'
      clockPos := by show 1 ≤ c.clock - 1; omega
      noGuard := PalPeg.ShapedRun.restartGuard_background centre place entry q first hb hnoGuard
      atLast := by show position s'.right = _; rw [hright]; exact hat'
      minv := ⟨fun htrue => absurd (hr'.symm.trans htrue) (by decide), fun _ => by
        show Leftmost w (position s'.right) (position s'.center)
        rw [hright, hcenter]; exact hminv.2 hr'⟩
      sound := hQ'
      onRun := ⟨c₀, r₀, _, _, hI₀, hrun', hshaped'⟩
      counters := allCanonical_tick _ _ centre place entry q first 2048 hcounters hchainLast htick
      chainLast := chainLastCan_vmTick _ _ centre place entry q first 2048 hchainLast htick
      replayReset := by show s'.replay = reset; rw [hrep']; exact hreplay
      span := PalPeg.BranchSupply.spanRep_congr hlen hrad hspan
      radiusNonneg := by show 0 ≤ value s'.radius; rw [hrad]; exact hradius
      dpDense := PalPeg.PhysicalDpHistory.dpHistory_tick centre place entry q first
        (PalPeg.CanonicalSearchHistory.atState_packed centre place entry q first hP hI₀ hrun)
        hdp htick }


variable {centre place entry q first}

/-- A tick out of the plateau keeps `replay` at zero. -/
theorem replayReset_of_plateauTick {w : List (Fin 2)}
    {x y : State GalilVM} (hinv : PlateauInv centre place entry q first w x)
    (htick : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y) :
    y.vm.replay = reset := by
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  have hrest : ReplayRest c s := fun _ => hinv.replayReset
  rcases rightReplayMove_of_tick _ _ centre place entry q first 2048 hrest htick with
    hreplay | ⟨-, hreplay⟩ | ⟨hreplaying, -, -⟩ | ⟨hmode, -, -⟩
  · exact hreplay
  · exact hreplay.trans hinv.replayReset
  · exact absurd (hinv.notReplaying.symm.trans hreplaying) (by decide)
  · exact absurd (hinv.scan.symm.trans hmode) (by decide)

#print axioms plateauStep
#print axioms replayReset_of_plateauTick

end PalPeg.PlateauInvariant
