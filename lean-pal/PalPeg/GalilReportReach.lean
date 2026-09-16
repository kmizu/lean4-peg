import PalPeg.GalilStructuredSkeleton
import PalPeg.GalilFrontier
import PalPeg.GalilEndOfInput
import PalPeg.GalilLiveCentreReplay
import PalPeg.GalilScaffoldTopOutputInit

/-!
# Reaching the report point: the tick that consumes the last letter

`PalPeg.GalilStructuredSkeleton` reduces `PAL ∈ PEG` to the existence, for
every nonempty input `w`, of a *scaffold run* ending in a **report point**
whose output is *refreshed* (`H_run` of `pal_in_peg_of_galil'`).  This module
supplies the last link of that run: the controller tick on which the right
head pops the **final** letter of `w` off the incoming FIFO.

The geometry is settled by `PalPeg.GalilEndOfInput`: a right move that pops
the last queued letter lands on `2 * |w| - 1`, the last letter cell of
`encoded w` (`last_letter_position`).  The replay bookkeeping is settled by
`PalPeg.GalilFrontier`: a move that pops a *new* letter can never happen
during a replay, because the replay counter never points past the material
that has already arrived (`consume_not_replaying`).  Together with `MInv`
(the centre is the leftmost live centre) and the scan invariant, those give
all four fields of `ReportPoint`.

* `report_of_last_consume` — the **matched** comparison on that tick: the
  scan invariant grows by one (`scanInvariant_matched`), the centre invariant
  is carried by `minv_match`, the output is refreshed by the tick's own
  `refresh` witness, and the run is extended by `StepsAll.succ`.  This is a
  complete proof: given the run so far, the tick's data, and the invariants
  at its source state, the target state *is* a refreshed report point.

* `report_of_last_consume_mismatch` — the **mismatched** comparison.  Here
  the tick alone is not enough, and the statement records exactly why; see
  the module note below and the docstring of the theorem.

## What the mismatch case really does

On a mismatch the controller does *not* report.  `Tick.scan_shift` and
`Tick.scan_fallback` carry no `refresh` witness at all: the `output` field is
copied unchanged and the mode leaves `scan`.  So the report point is the next
state in which the controller is back in scan mode, and there are two routes.

* **Shift route.**  `scan_shift → shift_one* → shift_done`.  `shift_done` is
  the tick that refreshes.  The right head does not move anywhere along this
  route (`beginShiftVM'_right`, `tick_shift_right`), so `atLast` survives and
  the report point is the state right after `shift_done`.  What does *not*
  survive is the scan invariant: the comparison mismatched, so the palindrome
  at the *old* centre does not extend, and the chain shift installs a *new*
  centre.  Re-establishing `ScanInvariant` and `MInv` at that new centre is
  the business of the chain-shift layer (`GalilLiveCentre*`,
  `GalilBranchInvariants*`), not of this module, so they appear as explicit
  hypotheses `hi2`/`hM2` of `report_of_last_consume_mismatch`.

* **Fallback route.**  `scan_fallback → copy* → home* → fpp* → markEnd* →
  choose* → rewind* → replayStart`.  `Tick.replayStart` is the tick that can
  refresh, but only in its `replayPos s' = false` branch; in the other branch
  it sets `output := c.output` verbatim **and** raises `replaying`, so both
  `Refreshed` and `ReportPoint.notReplaying` fail there.  Worse, the concrete
  `replayStartVM` moves the right head back onto the centre
  (`replayStart_right_position`), so `ReportPoint.atLast` fails too unless the
  fallback chose radius `0`.  `replayStart_report_point_iff_zero` states both
  facts.  **Conclusion: on the fallback route with a positive chosen radius
  there is no report point right after the mismatching cycle at all** — the
  machine first replays the chosen radius back up to the right head, and the
  report happens on the *matched* comparison that exhausts the replay
  counter, i.e. back in the situation of `report_of_last_consume` (with
  `c.replaying = true` at its source, which is why that theorem derives
  `replaying = false` at the *target* rather than assuming it).  Proving that
  the replay terminates at the right head is `minv_watchSegE` territory and
  is *not* done here.
-/

set_option autoImplicit false

namespace PalPeg.GalilReportReach

open PalPeg GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter
  GalilScaffoldInputHead GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
  GalilStructuredSkeleton GalilEndOfInput

/-! ## Geometry of the tick that pops the last letter -/

/-- The move that pops the **last** queued letter is legal, lands on the last
letter cell `2·|w| - 1` of `encoded w`, and witnesses that `w` is nonempty. -/
theorem last_consume_geometry {s : GalilVM} {w : List (Fin 2)} {a : Fin 2}
    (hrep : GalilScaffoldInputTrace.Represents s.right.head w)
    (hpop : PopsIncoming s.right) (hinc : s.right.head.incoming = [a]) :
    canRight s.right ∧ position (right s.right) = 2 * w.length - 1 ∧ 0 < w.length := by
  have hav : canRight s.right := Or.inr (Or.inr (by rw [hinc]; simp))
  have hr := pops_incoming_right hpop hinc
  refine ⟨hav, last_letter_position s.right w hrep hav ?_, ?_⟩
  · rw [hr]; exact ⟨rfl, rfl, rfl⟩
  · obtain ⟨xs, rs, q, hh, hw⟩ := hrep
    have hq : q = [a] := by
      rw [hh, layout_incoming] at hinc; exact hinc
    rw [hw, hq]; simp

/-- **No replay can be in progress** on a tick that pops a new letter: the
frontier invariant bounds the replay counter by the arrived material. -/
theorem not_replaying_of_pops {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hf : Frontier s) (hpop : PopsIncoming s.right) (hM : MInv w c s) :
    c.replaying = false := by
  cases hrepl : c.replaying with
  | false => rfl
  | true =>
    obtain ⟨m, hm0, hmeq, -⟩ := hM.1 hrepl
    have := consume_not_replaying hf hpop hmeq
    omega

/-! ## Packaging a report point -/

/-- The four fields of `ReportPoint` from the invariants. -/
theorem reportPoint_of_parts {w : List (Fin 2)} {c : Control} {t : GalilVM} {r : ℕ}
    (hnr : c.replaying = false)
    (hi : ScanInvariant w (position t.center) r t.left t.right)
    (hM : MInv w c t) (hlast : position t.right = 2 * w.length - 1)
    (hne : 0 < w.length) : ReportPoint w ⟨c, t⟩ :=
  ⟨hnr, ⟨r, hi⟩, hM, hlast, hne⟩

/-! ## The matched comparison that consumes the last letter -/

/-- **The report point on the last matched comparison.**

`⟨c, s⟩` is the last state of a scaffold run (`hrun`, starting from
`Control.initial delay`), the controller is in scan mode with the clock at
one, and the comparison this tick performs pops the final letter of `w` off
the incoming FIFO (`hpop`, `hinc`).  Then the state the tick lands in is a
refreshed report point of the same run.

The tick is supplied by its `Tick.scan_match` data: the comparison relation
`hcmp` with the two head moves `hl`/`hrr` it exhibits, the match witness
`hmt`, and the refresh witness `ho`. -/
theorem report_of_last_consume
    (w : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM w)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {n : ℕ} {x : State GalilVM} {c : Control} {s : GalilVM}
    (hx : x.ctl = GalilScaffoldController.initial delay)
    (hrun : StepsAll (galilFrameS P q first) delay (SoundScanNR w) n x ⟨c, s⟩)
    (hm : c.mode = Mode.scan) (hclk : c.clock = 1)
    (hpop : PopsIncoming s.right) {a : Fin 2} (hinc : s.right.head.incoming = [a])
    (hfr : Frontier s) (hM : MInv w c s)
    {r : ℕ} (hi : ScanInvariant w (position s.center) r s.left s.right)
    (hrep : GalilScaffoldInputTrace.Represents s.right.head w)
    (vs : ScanVM) (vq : SearchVM) (o : Bool)
    (hl : vs.left = GalilScaffoldInputHead.left s.left)
    (hrr : vs.right = right s.right)
    (hcmp : (galilFrameS P q first).compare s (afterCompare s vs vq))
    (hmt : (galilFrameS P q first).matched (afterCompare s vs vq))
    (ho : refresh (galilFrameS P q first) (afterCompare s vs vq) c.output o) :
    (∃ (k : ℕ) (x' : State GalilVM),
        x'.ctl = GalilScaffoldController.initial delay ∧
        StepsAll (galilFrameS P q first) delay (SoundScanNR w) k x'
          ⟨{c with clock := delay, output := o, replaying := false}, afterCompare s vs vq⟩) ∧
      ReportPoint w
        ⟨{c with clock := delay, output := o, replaying := false}, afterCompare s vs vq⟩ ∧
      Refreshed P q first
        ⟨{c with clock := delay, output := o, replaying := false}, afterCompare s vs vq⟩ := by
  obtain ⟨hav, hlast, hne⟩ := last_consume_geometry hrep hpop hinc
  have hnr : c.replaying = false := not_replaying_of_pops hfr hpop hM
  -- the comparison matched, so the outer symbols agree
  have hmt0 : (galilFrame P q first).matched (scanLens.set s vs) := hmt
  have hmatch : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left s.left) =
      GalilScaffoldInputHead.read (right s.right) := by
    have h0 := matched_parts P q first hmt0
    rw [hl, hrr] at h0; exact h0
  -- the scan invariant grows by one
  have hi' : ScanInvariant w (position s.center) (r + 1)
      (afterCompare s vs vq).left (afterCompare s vs vq).right :=
    matched_invariant' w vq hl hrr hmatch hav hi
  -- the tick itself
  have hpl : (galilFrameS P q first).matchedPlace c.replaying (afterCompare s vs vq)
      (afterCompare s vs vq) := by
    show afterCompare s vs vq = (if c.replaying then _ else afterCompare s vs vq)
    rw [hnr]; simp
  have htick : Tick (galilFrameS P q first) delay ⟨c, s⟩
      ⟨{c with clock := delay, output := o, replaying := false}, afterCompare s vs vq⟩ := by
    have h := Tick.scan_match (F := galilFrameS P q first) (delay := delay) c s
      (afterCompare s vs vq) (afterCompare s vs vq) o hm (Or.inr hav) hclk hcmp hmt hpl ho
    rw [hnr] at h
    simpa using h
  -- the new state is output-sound
  have hsound : SoundScanNR w
      ⟨{c with clock := delay, output := o, replaying := false}, afterCompare s vs vq⟩ := by
    intro _ _
    exact outputRel_of_refreshS' w P hP hP' q first (afterCompare s vs vq) c.output o hi' ho _ rfl
  have hlast' : position (afterCompare s vs vq).right = 2 * w.length - 1 := by
    rw [afterCompare_right, hrr]; exact hlast
  refine ⟨⟨n + 1, x, hx, stepsAll_trans hrun
      (.succ (stepsAll_last hrun) htick (.zero _ hsound))⟩, ?_, ?_⟩
  · exact reportPoint_of_parts rfl hi'
      (minv_match o delay hnr hl hrr hav hmatch hi hM) hlast' hne
  · exact ⟨c.output, (refreshS_iff P q first _ _ _).1 ho⟩

/-- `report_of_last_consume` in the `ScaffoldRun` packaging of
`PalPeg.GalilStructuredSkeleton`, i.e. exactly the shape `H_run` of
`pal_in_peg_of_galil'` consumes. -/
theorem scaffoldRun_report_of_last_consume
    (w : List (Fin 2)) (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ)
    (firstOf : List (Fin 2) → Fin 9) (delay : ℕ)
    (hP : (Pof w).onLetter = onLetterVM w) (hP' : (Pof w).leftFirst = leftFirstVM)
    {n : ℕ} {x : State GalilVM} {c : Control} {s : GalilVM}
    (hx : x.ctl = GalilScaffoldController.initial delay)
    (hrun : StepsAll (galilFrameS (Pof w) (qof w) (firstOf w)) delay (SoundScanNR w) n x ⟨c, s⟩)
    (hm : c.mode = Mode.scan) (hclk : c.clock = 1)
    (hpop : PopsIncoming s.right) {a : Fin 2} (hinc : s.right.head.incoming = [a])
    (hfr : Frontier s) (hM : MInv w c s)
    {r : ℕ} (hi : ScanInvariant w (position s.center) r s.left s.right)
    (hrep : GalilScaffoldInputTrace.Represents s.right.head w)
    (vs : ScanVM) (vq : SearchVM) (o : Bool)
    (hl : vs.left = GalilScaffoldInputHead.left s.left)
    (hrr : vs.right = right s.right)
    (hcmp : (galilFrameS (Pof w) (qof w) (firstOf w)).compare s (afterCompare s vs vq))
    (hmt : (galilFrameS (Pof w) (qof w) (firstOf w)).matched (afterCompare s vs vq))
    (ho : refresh (galilFrameS (Pof w) (qof w) (firstOf w)) (afterCompare s vs vq) c.output o) :
    ∃ y : State GalilVM,
      ScaffoldRun Pof qof firstOf delay w y ∧ ReportPoint w y ∧
        Refreshed (Pof w) (qof w) (firstOf w) y := by
  obtain ⟨⟨k, x', hx', hrun'⟩, hrp, hfrsh⟩ :=
    report_of_last_consume w (Pof w) hP hP' (qof w) (firstOf w) delay hx hrun hm hclk hpop hinc
      hfr hM hi hrep vs vq o hl hrr hcmp hmt ho
  exact ⟨_, ⟨k, x', hx', stepsAll_mono (fun _ _ => trivial) hrun'⟩, hrp, hfrsh⟩

/-! ## The mismatch case -/

/-- The chain shift entry does not move the right head. -/
theorem beginShiftVM'_right {s t : GalilVM} (h : beginShiftVM' s t) : t.right = s.right := by
  obtain ⟨_, _, ht⟩ := h
  rw [ht]

/-- One `stepShift` unit does not move the right head (`shiftLens` does not
contain the right head). -/
theorem shiftOne_right (P : Shared) (q : ℕ) (first : Fin 9) {s t : GalilVM}
    (h : (galilFrameS P q first).shiftOne s t) : t.right = s.right := by
  rw [h.2]; rfl

/-- **No tick out of shift mode moves the right head.** -/
theorem tick_shift_right (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {c c' : Control} {s t : GalilVM} (hm : c.mode = Mode.shift)
    (h : Tick (galilFrameS P q first) delay ⟨c, s⟩ ⟨c', t⟩) : t.right = s.right := by
  have bad : ∀ m : Mode, c.mode = m → m ≠ Mode.shift → t.right = s.right :=
    fun m h0 hne => absurd (h0.symm.trans hm) hne
  cases h
  case init => exact bad Mode.init ‹c.mode = Mode.init› (by simp)
  case scan_wait => exact bad Mode.scan ‹c.mode = Mode.scan› (by simp)
  case scan_count => exact bad Mode.scan ‹c.mode = Mode.scan› (by simp)
  case scan_match => exact bad Mode.scan ‹c.mode = Mode.scan› (by simp)
  case scan_shift => exact bad Mode.scan ‹c.mode = Mode.scan› (by simp)
  case scan_fallback => exact bad Mode.scan ‹c.mode = Mode.scan› (by simp)
  case shift_one => exact shiftOne_right P q first (by assumption)
  case shift_done => rfl
  case copy_one => exact bad Mode.copy ‹c.mode = Mode.copy› (by simp)
  case copy_done => exact bad Mode.copy ‹c.mode = Mode.copy› (by simp)
  case home_start => exact bad Mode.home ‹c.mode = Mode.home› (by simp)
  case home_step => exact bad Mode.home ‹c.mode = Mode.home› (by simp)
  case fpp_slice => exact bad Mode.fpp ‹c.mode = Mode.fpp› (by simp)
  case fpp_done => exact bad Mode.fpp ‹c.mode = Mode.fpp› (by simp)
  case markEnd_found => exact bad Mode.markEnd ‹c.mode = Mode.markEnd› (by simp)
  case markEnd_step => exact bad Mode.markEnd ‹c.mode = Mode.markEnd› (by simp)
  case choose_select => exact bad Mode.choose ‹c.mode = Mode.choose› (by simp)
  case choose_step => exact bad Mode.choose ‹c.mode = Mode.choose› (by simp)
  case rewind_done => exact bad Mode.rewind ‹c.mode = Mode.rewind› (by simp)
  case rewind_one => exact bad Mode.rewind ‹c.mode = Mode.rewind› (by simp)
  case rewind_pair => exact bad Mode.rewind ‹c.mode = Mode.rewind› (by simp)
  case replayStart => exact bad Mode.replayStart ‹c.mode = Mode.replayStart› (by simp)
  case restart => exact bad Mode.scan ‹c.mode = Mode.scan› (by simp)

/-- **The report point on the shift route out of a mismatching last
comparison.**

The comparison mismatches (`hnm`) with the chain-shift guard up (`hg`), so
the controller takes `Tick.scan_shift` into shift mode; `hseg` is the run of
`stepShift` units, and `shift_done` (`hnp`, `ho`) puts it back into scan mode
with the output refreshed.

`hbsr`/`hsegr` — the right head is where the comparison left it — are exactly
what `beginShiftVM'_right` and `tick_shift_right` give for the concrete
scaffold; they are hypotheses here because `Frame.beginShift` and
`Frame.shiftOne` are abstract in `galilFrameS`.

`hi2` and `hM2` are **not** proved here: after a mismatch the scan invariant
at the *old* centre is dead, and the invariants at the centre the chain shift
installs come from the chain-shift layer. -/
theorem report_of_last_consume_mismatch
    (w : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM w)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {n : ℕ} {x : State GalilVM} {c : Control} {s : GalilVM}
    (hx : x.ctl = GalilScaffoldController.initial delay)
    (hrun : StepsAll (galilFrameS P q first) delay (SoundScanNR w) n x ⟨c, s⟩)
    (hm : c.mode = Mode.scan) (hclk : c.clock = 1)
    (hpop : PopsIncoming s.right) {a : Fin 2} (hinc : s.right.head.incoming = [a])
    (hfr : Frontier s) (hM : MInv w c s)
    (hrep : GalilScaffoldInputTrace.Represents s.right.head w)
    -- the mismatching comparison, entering shift mode
    {s1 s1' s2 : GalilVM}
    (hcmp : (galilFrameS P q first).compare s s1)
    (hnm : ¬ (galilFrameS P q first).matched s1)
    (hg : (galilFrameS P q first).shiftGuard s1)
    (hbs : (galilFrameS P q first).beginShift s1 s1')
    (hbsr : s1'.right = right s.right)
    -- the shift segment and its exit
    {msteps : ℕ}
    (hseg : StepsAll (galilFrameS P q first) delay (SoundScanNR w) msteps
      ⟨{c with clock := delay, mode := Mode.shift}, s1'⟩
      ⟨{c with clock := delay, mode := Mode.shift}, s2⟩)
    (hsegr : s2.right = s1'.right)
    (hnp : ¬ (galilFrameS P q first).remainingPos s2)
    (o : Bool) (ho : refresh (galilFrameS P q first) s2 c.output o)
    -- re-established by the chain shift; not proved in this module
    {r2 : ℕ} (hi2 : ScanInvariant w (position s2.center) r2 s2.left s2.right)
    (hM2 : MInv w {c with clock := delay, mode := Mode.scan, output := o} s2) :
    (∃ (k : ℕ) (x' : State GalilVM),
        x'.ctl = GalilScaffoldController.initial delay ∧
        StepsAll (galilFrameS P q first) delay (SoundScanNR w) k x'
          ⟨{c with clock := delay, mode := Mode.scan, output := o}, s2⟩) ∧
      ReportPoint w ⟨{c with clock := delay, mode := Mode.scan, output := o}, s2⟩ ∧
      Refreshed P q first ⟨{c with clock := delay, mode := Mode.scan, output := o}, s2⟩ := by
  obtain ⟨hav, hlast, hne⟩ := last_consume_geometry hrep hpop hinc
  have hnr : c.replaying = false := not_replaying_of_pops hfr hpop hM
  have htick1 : Tick (galilFrameS P q first) delay ⟨c, s⟩
      ⟨{c with clock := delay, mode := Mode.shift}, s1'⟩ :=
    Tick.scan_shift c s s1 s1' hm (Or.inr hav) hclk hcmp hnm hnr hg hbs
  have hshiftSound : SoundScanNR w ⟨{c with clock := delay, mode := Mode.shift}, s1'⟩ :=
    fun hsc _ => Mode.noConfusion hsc
  have htick2 : Tick (galilFrameS P q first) delay
      ⟨{c with clock := delay, mode := Mode.shift}, s2⟩
      ⟨{c with clock := delay, mode := Mode.scan, output := o}, s2⟩ :=
    Tick.shift_done {c with clock := delay, mode := Mode.shift} s2 o rfl hnp ho
  have hsound : SoundScanNR w ⟨{c with clock := delay, mode := Mode.scan, output := o}, s2⟩ := by
    intro _ _
    exact outputRel_of_refreshS' w P hP hP' q first s2 c.output o hi2 ho _ rfl
  have hlast2 : position s2.right = 2 * w.length - 1 := by
    rw [hsegr, hbsr]; exact hlast
  have hrun2 : StepsAll (galilFrameS P q first) delay (SoundScanNR w) (n + 1) x
      ⟨{c with clock := delay, mode := Mode.shift}, s1'⟩ :=
    stepsAll_trans hrun (.succ (stepsAll_last hrun) htick1 (.zero _ hshiftSound))
  have hrun3 := stepsAll_trans (stepsAll_trans hrun2 hseg)
    (StepsAll.succ (stepsAll_last hseg) htick2 (.zero _ hsound))
  refine ⟨⟨_, x, hx, hrun3⟩, ?_, ?_⟩
  · exact reportPoint_of_parts hnr hi2 hM2 hlast2 hne
  · exact ⟨c.output, (refreshS_iff P q first _ _ _).1 ho⟩

/-! ## Why the fallback route has no report point right after the cycle -/

/-- The concrete `stepReplayStart` puts the right head **on the centre**. -/
theorem replayStart_right_position (entry : ℕ) {s t : GalilVM} (h : replayStartVM entry s t) :
    position t.right = position s.center := by
  rw [h.2.1]

/-- **The precise gap on the fallback route.**  After `Tick.replayStart` the
controller's `replaying` flag is the frame's `replayPos`, and the refresh
witness exists only when that flag is down.  So the state right after a
fallback cycle is a candidate report point **iff** the replay counter came
out empty; and even then `ReportPoint.atLast` needs the centre to be back at
the last letter cell, i.e. the fallback must have chosen radius `0`. -/
theorem replayStart_report_point_iff_zero (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (entry : ℕ) (c : Control) (s t : GalilVM) (o : Bool)
    (hm : c.mode = Mode.replayStart)
    (hrs : (galilFrameS P q first).replayStart s t)
    (hrsC : replayStartVM entry s t)
    (ho : (galilFrameS P q first).replayPos t = true → o = c.output)
    (ho' : (galilFrameS P q first).replayPos t = false →
      refresh (galilFrameS P q first) t c.output o)
    (hz : (galilFrameS P q first).replayPos t = false) :
    Tick (galilFrameS P q first) delay ⟨c, s⟩
        ⟨{c with mode := Mode.scan, clock := delay, output := o, replaying := false}, t⟩ ∧
      ({c with mode := Mode.scan, clock := delay, output := o, replaying := false} :
        Control).replaying = false ∧
      Refreshed P q first
        ⟨{c with mode := Mode.scan, clock := delay, output := o, replaying := false}, t⟩ ∧
      position t.right = position s.center := by
  refine ⟨?_, rfl, ⟨c.output, (refreshS_iff P q first _ _ _).1 (ho' hz)⟩,
    replayStart_right_position entry hrsC⟩
  have h := Tick.replayStart (F := galilFrameS P q first) (delay := delay) c s t o hm hrs ho ho'
  rw [hz] at h
  exact h

#print axioms last_consume_geometry
#print axioms not_replaying_of_pops
#print axioms reportPoint_of_parts
#print axioms report_of_last_consume
#print axioms scaffoldRun_report_of_last_consume
#print axioms beginShiftVM'_right
#print axioms shiftOne_right
#print axioms tick_shift_right
#print axioms report_of_last_consume_mismatch
#print axioms replayStart_right_position
#print axioms replayStart_report_point_iff_zero

end PalPeg.GalilReportReach
