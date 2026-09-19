import PalPeg.GalilTrailBudget

/-!
# `H_saneHeads`: the three scan heads never stand on the clipped origin

`GalilTrailBudget.H_saneHeads` asks, along every pre-loaded trace and at every
tick up to the last checkpoint, for `GalilFrontMono.Sane` of `L`, `C` and `R`
(`gap = true ∨ 0 < head.left.length`: the head is not a letter cell at the
clipped origin).  This module discharges it from two purely positional
side conditions.

`Sane` travels along a head move as follows.

* A **right** move keeps it as soon as the move is possible
  (`GalilFrontMono.right_sane`); when it is not possible the head does not
  move at all and the gap flag flips to `false`, which is the one way to
  fall onto the clipped origin.
* A **left** move keeps it exactly when the head stands strictly right of the
  origin (`GalilFrontMono.left_sane`).

The head moves of `galilFrameS` are: `R` right at `init` and at every
comparison; `L` left at a comparison and at every rewind tick; `C` left at a
`rewind_pair` tick; `C` right and `L` right twice per shift unit; and the three
bulk copies (`init`, `choose_select`, `replayStart`).  Of these,

* the shift unit carries its own `canRight` guards (`shiftOne`),
* the comparison's `canRight R` is the frontier bound of
  `GalilFrontMono.FrontPack` when replaying and the `available` guard of the
  tick otherwise,
* `init` moves `R` out of the boot head, whose FIFO is the nonempty input,

so the only facts that are *not* tick-local are the two liveness conditions on
the left-moving heads:

* `CentreLive` (`GalilRewindSafe`), already a named hypothesis of the
  development, for `C` at `rewind_pair`;
* `LeftLive` (below), its exact analogue for `L` at a comparison and at a
  rewind tick.

`h_saneHeads_of_headLive` is therefore `H_saneHeads` from `H_headLive`, the
conjunction of the two along the trace.  Everything else — including the
`FrontPack` needed for the replaying comparison, which is booted here at the
`init` tick — is proved.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.GalilTrailSane

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilThrottledRun PalPeg.GalilLookRefined PalPeg.GalilTrailProof
open PalPeg.GalilFinalAssembly PalPeg.GalilTrailScan PalPeg.GalilTrailBudget

abbrev PH := GalilScaffoldInputHead.PlaceHead

/-! ## 1. Transport of `Sane` along the three head moves -/

theorem sane_rightE {p p' : PH} (he : p' = GalilScaffoldChainVerifier.right p)
    (hc : GalilScaffoldChainVerifier.canRight p) (hs : GalilFrontMono.Sane p) :
    GalilFrontMono.Sane p' := by rw [he]; exact (GalilFrontMono.right_sane hc hs).2

theorem sane_leftE {p p' : PH} (he : p' = GalilScaffoldInputHead.left p) (hp : 0 < position p) :
    GalilFrontMono.Sane p' := by rw [he]; exact GalilFrontMono.left_sane hp

theorem sane_copyE {p p' : PH} (he : p' = p) (hs : GalilFrontMono.Sane p) :
    GalilFrontMono.Sane p' := by rw [he]; exact hs

/-! ## 2. `init` is entered once and never re-entered -/

theorem tick_notInit {σ : Type} {F : Frame σ} {delay : ℕ} {c c' : Control} {s t : σ}
    (h : Tick F delay ⟨c, s⟩ ⟨c', t⟩) : c'.mode ≠ Mode.init := by
  intro hh; cases h <;> simp_all

theorem tick_init {σ : Type} {F : Frame σ} {delay : ℕ} {c c' : Control} {s t : σ}
    (hi : c.mode = Mode.init) (h : Tick F delay ⟨c, s⟩ ⟨c', t⟩) :
    c' = {c with mode := Mode.scan, output := true} ∧ F.init s t := by
  cases h <;> simp_all

/-! ## 3. `LeftLive`, the analogue of `CentreLive` for the left head -/

/-- **The left head is off the origin whenever it is about to move left.**  `L`
moves left at a scan comparison (`clock = 1`) and at every `rewind` tick.  This
is the exact analogue of `GalilRewindSafe.CentreLive` for `L`, and the only
side condition of this module that is not already named elsewhere. -/
def LeftLive (c : Control) (s : GalilVM) : Prop :=
  (c.mode = Mode.scan → c.clock = 1 → 0 < position s.left) ∧
  (c.mode = Mode.rewind → 0 < position s.left)

/-! ## 4. The carrier -/

/-- `Sane` of the three heads, plus what the `init` tick and the replaying
comparison need: at the boot state the right head's FIFO is nonempty and
nothing is replaying; off `init`, the frontier pack of `GalilFrontMono`. -/
structure SanePack (c : Control) (s : GalilVM) : Prop where
  saneL : GalilFrontMono.Sane s.left
  saneC : GalilFrontMono.Sane s.center
  saneR : GalilFrontMono.Sane s.right
  bootCan : c.mode = Mode.init → GalilScaffoldChainVerifier.canRight s.right
  bootRep : c.mode = Mode.init → c.replaying = false ∧ s.replay = GalilScaffoldCounter.reset
  pack : c.mode ≠ Mode.init → GalilFrontMono.FrontPack c s

/-! ## 5. One tick -/

section Tick
variable (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
  (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)

/-- **`canRight R` at a comparison.**  Not replaying, it is the tick's own
`available` guard; replaying, it is the frontier bound, exactly as in
`GalilFrontMono.sane_tick`. -/
theorem canRight_compare {c : Control} {s : GalilVM} (hP : GalilFrontMono.FrontPack c s)
    (hav : c.replaying = true ∨ GalilScaffoldChainVerifier.canRight s.right) :
    GalilScaffoldChainVerifier.canRight s.right := by
  cases hcr : c.replaying with
  | false =>
    rcases hav with h | h
    · rw [hcr] at h; cases h
    · exact h
  | true =>
    obtain ⟨m, hm'⟩ := hP.replayPos hcr
    exact GalilFrontMono.canRight_of_budget (hP.frontier (m+1) hm')

/-- **`Sane` of the three heads travels along one tick.** -/
theorem sane3_tick {c c' : Control} {s t : GalilVM}
    (hS : SanePack c s) (hg : CentreLive c s) (hll : LeftLive c s)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) :
    GalilFrontMono.Sane t.left ∧ GalilFrontMono.Sane t.center ∧ GalilFrontMono.Sane t.right := by
  obtain ⟨bL, bC, bR, hbc, hbr, hpk⟩ := hS
  cases h
  case init =>
    rename_i hm hi
    obtain ⟨hr, hl, hce, -⟩ : initVM entry s t := hi
    have hcan := hbc hm
    exact ⟨sane_rightE hl hcan bR, sane_rightE hce hcan bR, sane_rightE hr hcan bR⟩
  case scan_wait =>
    rename_i hm hav hb
    obtain ⟨hl, hr, -, hce, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    exact ⟨sane_copyE hl bL, sane_copyE hce bC, sane_copyE hr bR⟩
  case scan_count =>
    rename_i hm hc hav hb
    obtain ⟨hl, hr, -, hce, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    exact ⟨sane_copyE hl bL, sane_copyE hce bC, sane_copyE hr bR⟩
  case restart =>
    rename_i hm hb
    obtain ⟨w, -, -, -, -, ht⟩ : restartVM entry s t := hb
    exact ⟨sane_copyE (by rw [ht]) bL, sane_copyE (by rw [ht]) bC, sane_copyE (by rw [ht]) bR⟩
  case scan_match =>
    rename_i s' o hmt hm hc hcmp hav hpl ho
    obtain ⟨hl, hr, hce⟩ :=
      compare_heads onLetter leftFirst centre place entry q first hcmp
    have hpl' : t = (if c.replaying then
        {s' with replay := GalilScaffoldCounter.dec s'.replay} else s') := hpl
    have e1 : t.left = GalilScaffoldInputHead.left s.left := by
      rw [hpl']; cases c.replaying <;> exact hl
    have e2 : t.center = s.center := by rw [hpl']; cases c.replaying <;> exact hce
    have e3 : t.right = GalilScaffoldChainVerifier.right s.right := by
      rw [hpl']; cases c.replaying <;> exact hr
    exact ⟨sane_leftE e1 (hll.1 hm hc), sane_copyE e2 bC,
      sane_rightE e3 (canRight_compare (hpk (by rw [hm]; decide)) hav) bR⟩
  case scan_shift =>
    rename_i s' hmt hg' hm hc hr hcmp hav hb
    obtain ⟨hl, hrr, hce⟩ :=
      compare_heads onLetter leftFirst centre place entry q first hcmp
    obtain ⟨w, -, ht⟩ : beginShiftVM' s' t := hb
    exact ⟨sane_leftE (by rw [ht]; exact hl) (hll.1 hm hc), sane_copyE (by rw [ht]; exact hce) bC,
      sane_rightE (by rw [ht]; exact hrr) (canRight_compare (hpk (by rw [hm]; decide)) hav) bR⟩
  case scan_fallback =>
    rename_i s' hmt hm hc hg' hr hcmp hav hb
    obtain ⟨hl, hrr, hce⟩ :=
      compare_heads onLetter leftFirst centre place entry q first hcmp
    obtain ⟨p, ht, -⟩ : beginFallbackVM' s' t := hb
    exact ⟨sane_leftE (by rw [ht]; exact hl) (hll.1 hm hc), sane_copyE (by rw [ht]; exact hce) bC,
      sane_rightE (by rw [ht]; exact hrr) (canRight_compare (hpk (by rw [hm]; decide)) hav) bR⟩
  case shift_one =>
    rename_i hm hp hi
    obtain ⟨hcc, hcl, hcl2, w, hw, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    have e1 : t.left = GalilScaffoldChainVerifier.right
        (GalilScaffoldChainVerifier.right s.left) := by rw [ht]; rfl
    have e2 : t.center = GalilScaffoldChainVerifier.right s.center := by rw [ht]; rfl
    have e3 : t.right = s.right := by rw [ht]; rfl
    exact ⟨sane_rightE e1 hcl2 (sane_rightE rfl hcl bL), sane_rightE e2 hcc bC,
      sane_copyE e3 bR⟩
  case shift_done => exact ⟨bL, bC, bR⟩
  case copy_one =>
    rename_i hm hp hi
    exact ⟨by rw [(congrArg GalilVM.left hi.2).trans rfl]; exact bL,
      by rw [(congrArg GalilVM.center hi.2).trans rfl]; exact bC,
      by rw [(congrArg GalilVM.right hi.2).trans rfl]; exact bR⟩
  case copy_done =>
    rename_i hm hp hi
    exact ⟨by rw [(congrArg GalilVM.left hi.2).trans rfl]; exact bL,
      by rw [(congrArg GalilVM.center hi.2).trans rfl]; exact bC,
      by rw [(congrArg GalilVM.right hi.2).trans rfl]; exact bR⟩
  case home_start =>
    rename_i hm hl hi
    exact ⟨by rw [(congrArg GalilVM.left hi.2).trans rfl]; exact bL,
      by rw [(congrArg GalilVM.center hi.2).trans rfl]; exact bC,
      by rw [(congrArg GalilVM.right hi.2).trans rfl]; exact bR⟩
  case home_step =>
    rename_i hm hl hi
    exact ⟨by rw [(congrArg GalilVM.left hi.2).trans rfl]; exact bL,
      by rw [(congrArg GalilVM.center hi.2).trans rfl]; exact bC,
      by rw [(congrArg GalilVM.right hi.2).trans rfl]; exact bR⟩
  case fpp_slice =>
    rename_i hm hi
    exact ⟨by rw [(congrArg GalilVM.left hi.2).trans rfl]; exact bL,
      by rw [(congrArg GalilVM.center hi.2).trans rfl]; exact bC,
      by rw [(congrArg GalilVM.right hi.2).trans rfl]; exact bR⟩
  case fpp_done =>
    rename_i hm hi
    exact ⟨by rw [(congrArg GalilVM.left hi.2).trans rfl]; exact bL,
      by rw [(congrArg GalilVM.center hi.2).trans rfl]; exact bC,
      by rw [(congrArg GalilVM.right hi.2).trans rfl]; exact bR⟩
  case markEnd_step =>
    rename_i hm he hi
    exact ⟨by rw [(congrArg GalilVM.left hi.2).trans rfl]; exact bL,
      by rw [(congrArg GalilVM.center hi.2).trans rfl]; exact bC,
      by rw [(congrArg GalilVM.right hi.2).trans rfl]; exact bR⟩
  case markEnd_found =>
    rename_i hm he hi
    exact ⟨by rw [(congrArg GalilVM.left hi.2).trans (by rw [hi.1.2])]; exact bL,
      by rw [(congrArg GalilVM.center hi.2).trans (by rw [hi.1.2])]; exact bC,
      by rw [(congrArg GalilVM.right hi.2).trans (by rw [hi.1.2])]; exact bR⟩
  case choose_step =>
    rename_i hm hs hi
    exact ⟨by rw [(congrArg GalilVM.left hi.2).trans (by rw [hi.1.2])]; exact bL,
      by rw [(congrArg GalilVM.center hi.2).trans (by rw [hi.1.2])]; exact bC,
      by rw [(congrArg GalilVM.right hi.2).trans (by rw [hi.1.2])]; exact bR⟩
  case rewind_done =>
    rename_i hm hfi hi
    exact ⟨by rw [(congrArg GalilVM.left hi.2).trans (by rw [hi.1])]; exact bL,
      by rw [(congrArg GalilVM.center hi.2).trans (by rw [hi.1])]; exact bC,
      by rw [(congrArg GalilVM.right hi.2).trans (by rw [hi.1])]; exact bR⟩
  case choose_select =>
    rename_i hm hodd hs hi
    exact ⟨by rw [(congrArg GalilVM.left hi.2).trans (by rw [hi.1])]; exact bR,
      by rw [(congrArg GalilVM.center hi.2).trans (by rw [hi.1])]; exact bR,
      by rw [(congrArg GalilVM.right hi.2).trans (by rw [hi.1])]; exact bR⟩
  case rewind_one =>
    rename_i hm hpr hfi hi
    have e1 : t.left = GalilScaffoldInputHead.left s.left :=
      (congrArg GalilVM.left hi.2).trans (by rw [hi.1.2]; rfl)
    refine ⟨sane_leftE e1 (hll.2 ‹c.mode = Mode.rewind›), ?_, ?_⟩
    · rw [(congrArg GalilVM.center hi.2).trans (by rw [hi.1.2])]; exact bC
    · rw [(congrArg GalilVM.right hi.2).trans (by rw [hi.1.2])]; exact bR
  case rewind_pair =>
    rename_i hm hpr hfi hi
    have e1 : t.left = GalilScaffoldInputHead.left s.left :=
      (congrArg GalilVM.left hi.2).trans (by rw [hi.1.2]; rfl)
    have e2 : t.center = GalilScaffoldInputHead.left s.center :=
      (congrArg GalilVM.center hi.2).trans (by rw [hi.1.2]; rfl)
    refine ⟨sane_leftE e1 (hll.2 ‹c.mode = Mode.rewind›),
      sane_leftE e2 (hg ‹c.mode = Mode.rewind› ‹c.pair = true›), ?_⟩
    · rw [(congrArg GalilVM.right hi.2).trans (by rw [hi.1.2])]; exact bR
  case replayStart =>
    rename_i o hm ho ho' hi
    obtain ⟨-, hr, hl, hce, -⟩ : replayStartVM entry s t := hi
    exact ⟨sane_copyE hl bC, sane_copyE hce bC, sane_copyE hr bC⟩

/-- **The frontier pack travels along one tick**, booting it at the `init` tick
out of the boot state's data. -/
theorem pack_tick {c c' : Control} {s t : GalilVM}
    (hS : SanePack c s) (hg : CentreLive c s)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : GalilFrontMono.FrontPack c' t := by
  by_cases hi : c.mode = Mode.init
  · obtain ⟨hc', hini⟩ := tick_init hi h
    obtain ⟨hr, -, -, -, -, -, hrp, -⟩ : initVM entry s t := hini
    obtain ⟨hcr, hrs⟩ := hS.bootRep hi
    have hz : t.replay = GalilScaffoldCounter.reset := hrp.trans hrs
    subst hc'
    exact
      { notInit := by intro hh; cases hh
        flag := fun hh => absurd rfl hh
        sane := sane_rightE hr (hS.bootCan hi) hS.saneR
        rewind := GalilFrontMono.rewindEq_of_mode (m := Mode.scan) (by decide) (by decide) rfl
        replayPos := fun hh => by
          exfalso
          have hx : c.replaying = true := hh
          rw [hcr] at hx
          exact Bool.noConfusion hx
        phase := rewindPhase_of_mode (m := Mode.scan) (by decide) (by decide) rfl
        frontier := frontier_of_reset hz
        rest := fun _ => hz }
  · exact GalilFrontMono.frontPack_tick onLetter leftFirst centre place entry q first delay
      (hS.pack hi) hg h

/-- **The whole carrier travels along one tick.** -/
theorem sanePack_tick {c c' : Control} {s t : GalilVM}
    (hS : SanePack c s) (hg : CentreLive c s) (hll : LeftLive c s)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : SanePack c' t := by
  obtain ⟨sL, sC, sR⟩ :=
    sane3_tick onLetter leftFirst centre place entry q first delay hS hg hll h
  exact ⟨sL, sC, sR, fun hh => absurd hh (tick_notInit h), fun hh => absurd hh (tick_notInit h),
    fun _ => pack_tick onLetter leftFirst centre place entry q first delay hS hg h⟩

end Tick

/-! ## 6. The boot state -/

theorem sanePack_boot {w : List (Fin 2)} (hw : 0 < w.length) :
    SanePack (boot w).ctl (boot w).vm := by
  refine ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl, fun _ => ?_, fun _ => ⟨rfl, rfl⟩,
    fun hh => absurd rfl hh⟩
  exact initialHead_canRight w (by intro hh; rw [hh] at hw; simp at hw)

/-! ## 7. Along a pre-loaded trace -/

section Trace
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

theorem sanePack_trace {w : List (Fin 2)} (hw : 0 < w.length) {st : ℕ → State GalilVM}
    {Tc : ℕ → ℕ} (hP : PreTrace centre place entry q first w st Tc)
    (hlive : ∀ i, i < Tc w.length →
      CentreLive (st i).ctl (st i).vm ∧ LeftLive (st i).ctl (st i).vm) :
    ∀ i, i ≤ Tc w.length → SanePack (st i).ctl (st i).vm := by
  intro i
  induction i with
  | zero => intro _; rw [hP.start]; exact sanePack_boot hw
  | succ i ih =>
    intro hi
    have hlt : i < Tc w.length := by omega
    exact sanePack_tick (onLetterVM w) leftFirstVM centre place entry q first 2048
      (ih (by omega)) (hlive i hlt).1 (hlive i hlt).2 (hP.trace.tick i hlt)

/-- **(Named) the two liveness conditions along every pre-loaded trace.**  This
is everything `H_saneHeads` still needs: at every tick up to the last
checkpoint the centre head is off the origin when a `rewind_pair` is about to
move it (`CentreLive`, already named in `GalilRewindSafe` and proved along runs
out of an `InvL` state in `GalilCentreLive`), and the left head is off the
origin when a comparison or a rewind tick is about to move it (`LeftLive`). -/
def H_headLive : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    ∀ i, i < Tc w.length → CentreLive (st i).ctl (st i).vm ∧ LeftLive (st i).ctl (st i).vm

/-- **`H_saneHeads`, reduced to the two liveness conditions.** -/
theorem h_saneHeads_of_headLive (h : H_headLive centre place entry q first) :
    H_saneHeads centre place entry q first := by
  intro w hw st Tc hP i hi
  have hs := sanePack_trace centre place entry q first hw hP
    (fun j hj => h w hw st Tc hP j hj) i hi
  exact ⟨hs.saneL, hs.saneC, hs.saneR⟩

end Trace

#print axioms sane_rightE
#print axioms sane_leftE
#print axioms tick_notInit
#print axioms tick_init
#print axioms canRight_compare
#print axioms sane3_tick
#print axioms pack_tick
#print axioms sanePack_tick
#print axioms sanePack_boot
#print axioms sanePack_trace
#print axioms h_saneHeads_of_headLive

end PalPeg.GalilTrailSane
