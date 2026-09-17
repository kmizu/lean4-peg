import PalPeg.GalilRunTrace
import PalPeg.GalilRewindSafe

/-!
# The frontier is monotone along a cycle

Discharges the `front r ≤ front sT` obligation of `GalilRunTrace.CycleOutL'`.
The carrier `FrontPack` adds to `Frontier`/`ReplayRest`/`RewindPhase` four
mode-guarded facts: no return to `init`; outside `scan` the `replaying` flag is
down; while replaying the counter is `ofNat (m+1)`; the right head is `Sane`
(not a letter at the clipped origin); and in `rewind`/`replayStart` the radius
is `ofNat r` with `position center + r = position right` (`RewindEq`).
The only assumption is `CentreLive`, as in `GalilRewindSafe`.
-/

set_option autoImplicit false
namespace PalPeg.GalilFrontMono
open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainInputSupply
open PalPeg.GalilRunTrace

/-! ## Head arithmetic -/

/-- A head that is not a letter at the clipped origin. -/
def Sane (p : PlaceHead) : Prop := p.gap = true ∨ 0 < p.head.left.length

theorem right_sane {p : PlaceHead} (hc : GalilScaffoldChainVerifier.canRight p) (hs : Sane p) :
    position (GalilScaffoldChainVerifier.right p) = position p + 1 ∧
      Sane (GalilScaffoldChainVerifier.right p) := by
  rcases p with ⟨⟨f, ls, rs, qs⟩, g⟩
  cases g with
  | false =>
    simp only [Sane, Bool.false_eq_true, false_or] at hs
    simp [position, GalilScaffoldChainVerifier.right, Sane]
    omega
  | true =>
    cases rs with
    | cons a rs =>
      simp [position, GalilScaffoldChainVerifier.right, GalilScaffoldChainVerifier.headRight,
        GalilScaffoldInputTrace.moveRight, Sane]
      omega
    | nil =>
      cases qs with
      | nil => simp [GalilScaffoldChainVerifier.canRight] at hc
      | cons a qs =>
        simp [position, GalilScaffoldChainVerifier.right, GalilScaffoldChainVerifier.headRight,
          GalilScaffoldInputTrace.moveRight, Sane]
        omega

theorem canRight_of_budget {p : PlaceHead} {m : ℕ} (h : position p + (m+1) ≤ 2 * arrived p) :
    GalilScaffoldChainVerifier.canRight p := by
  rcases p with ⟨⟨f, ls, rs, qs⟩, g⟩
  cases g with
  | false => exact Or.inl rfl
  | true =>
    cases rs with
    | cons a rs => exact Or.inr (Or.inl (by simp))
    | nil =>
      cases qs with
      | cons a qs => exact Or.inr (Or.inr (by simp))
      | nil => simp [position, arrived] at h

theorem left_sane {p : PlaceHead} (h : 0 < position p) :
    Sane (GalilScaffoldInputHead.left p) := by
  rcases p with ⟨⟨f, ls, rs, qs⟩, g⟩
  cases g with
  | false => exact Or.inl rfl
  | true =>
    right
    simp only [position, if_true] at h
    simp only [GalilScaffoldInputHead.left, if_true]
    omega

theorem sane_of_rep {p : PlaceHead} {raw : List (Fin 2)}
    (hh : GalilScaffoldInputTrace.Represents p.head raw) (hp : p.head.focus ≠ none) : Sane p :=
  Or.inr (represented_position p.head raw hh hp).1

theorem front_congr {s t : GalilVM} (hr : t.right = s.right) (hp : t.replay = s.replay) :
    front t = front s := by
  simp [front, hr, hp]


/-! ## The carrier -/

/-- In `rewind`/`replayStart` mode the radius is a natural number `r` and the
centre stands exactly `r` places left of the right head. -/
def RewindEq (c : Control) (s : GalilVM) : Prop :=
  (c.mode = Mode.rewind ∨ c.mode = Mode.replayStart) →
    ∃ r, s.radius = ofNat r ∧ position s.center + r = position s.right ∧ Sane s.center

/-- The invariant pack carried along a cycle's run. -/
structure FrontPack (c : Control) (s : GalilVM) : Prop where
  notInit : c.mode ≠ Mode.init
  flag : c.mode ≠ Mode.scan → c.replaying = false
  sane : Sane s.right
  rewind : RewindEq c s
  replayPos : c.replaying = true → ∃ m, s.replay = ofNat (m+1)
  phase : RewindPhase c s
  frontier : Frontier s
  rest : ReplayRest c s

theorem rewindEq_of_mode {c : Control} {s : GalilVM} {m : Mode}
    (h1 : m ≠ Mode.rewind) (h2 : m ≠ Mode.replayStart) (h : c.mode = m) : RewindEq c s := by
  intro hm
  rcases hm with hm | hm
  · exact absurd (h.symm.trans hm) h1
  · exact absurd (h.symm.trans hm) h2

macro "vacuous_eq" : tactic =>
  `(tactic| first
    | exact rewindEq_of_mode (m := Mode.init) (by decide) (by decide) (by first | rfl | assumption)
    | exact rewindEq_of_mode (m := Mode.scan) (by decide) (by decide) (by first | rfl | assumption)
    | exact rewindEq_of_mode (m := Mode.shift) (by decide) (by decide) (by first | rfl | assumption)
    | exact rewindEq_of_mode (m := Mode.copy) (by decide) (by decide) (by first | rfl | assumption)
    | exact rewindEq_of_mode (m := Mode.home) (by decide) (by decide) (by first | rfl | assumption)
    | exact rewindEq_of_mode (m := Mode.fpp) (by decide) (by decide) (by first | rfl | assumption)
    | exact rewindEq_of_mode (m := Mode.markEnd) (by decide) (by decide)
        (by first | rfl | assumption)
    | exact rewindEq_of_mode (m := Mode.choose) (by decide) (by decide)
        (by first | rfl | assumption))

theorem ne_of_mode {c : Control} {m m' : Mode} (h : c.mode = m) (hm : m ≠ m') : c.mode ≠ m' :=
  fun h' => hm (h.symm.trans h')

macro "not_scan" : tactic =>
  `(tactic| first
    | exact ne_of_mode (m := Mode.shift) ‹_› (by decide)
    | exact ne_of_mode (m := Mode.copy) ‹_› (by decide)
    | exact ne_of_mode (m := Mode.home) ‹_› (by decide)
    | exact ne_of_mode (m := Mode.fpp) ‹_› (by decide)
    | exact ne_of_mode (m := Mode.markEnd) ‹_› (by decide)
    | exact ne_of_mode (m := Mode.choose) ‹_› (by decide)
    | exact ne_of_mode (m := Mode.rewind) ‹_› (by decide)
    | exact ne_of_mode (m := Mode.replayStart) ‹_› (by decide))

/-- Establishment at a recursion state of the oracle. -/
theorem frontPack_of_invS {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    (h : PalPeg.GalilOracleDischarge.InvS raw c s) : FrontPack c s := by
  obtain ⟨hm, hr⟩ := PalPeg.GalilOracleLocal.invS_mode h
  have hsane : Sane s.right := by
    rcases h with h | ⟨k, h⟩
    · obtain ⟨Rad, last, hR⟩ := h.rest
      exact sane_of_rep hR.2.2.2.1.rightRep hR.2.2.2.1.rightPresent
    · exact sane_of_rep h.scan.rightRep h.scan.rightPresent
  have hfr : Frontier s ∧ ReplayRest c s := by
    rcases h with h | ⟨k, h⟩
    · exact ⟨h.frontier, h.rest_replay⟩
    · exact ⟨h.frontier, h.rest_replay⟩
  exact
    { notInit := by rw [hm]; decide
      flag := fun h' => absurd hm h'
      sane := hsane
      rewind := rewindEq_of_mode (by decide) (by decide) hm
      replayPos := fun h' => by rw [hr] at h'; cases h'
      phase := rewindPhase_of_mode (by decide) (by decide) hm
      frontier := hfr.1
      rest := hfr.2 }

/-! ## (a) One tick -/

section Tick
variable (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
  (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)

/-- The comparison moves the right head one place right and keeps the replay. -/
theorem compare_fields {s s' : GalilVM}
    (hcmp : (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).compare s s') :
    s'.right = GalilScaffoldChainVerifier.right s.right ∧ s'.replay = s.replay := by
  obtain ⟨vs, vq, a, -, hvr, -, -, -, hteq⟩ :
    compareFound (sharedC onLetter leftFirst centre place entry) q first s s' := hcmp
  exact ⟨by rw [hteq, afterBirth_right]; cases a <;> exact hvr,
    by rw [hteq, afterBirth_replay]; cases a <;> rfl⟩

/-- **The frontier moves only on a comparison, and a comparison resets the clock.**
Either the tick leaves the frontier where it was, or it is a comparison: it gains
at most one frontier unit, and it fires at `clock = 1` and leaves `clock = delay`.
(`replayStart` is in the first case by `RewindEq`'s equation
`position center + r = position right`.) -/
theorem front_clock_tick {c c' : Control} {s t : GalilVM} (hP : FrontPack c s)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) :
    front t = front s ∨ (front t ≤ front s + 1 ∧ c.clock = 1 ∧ c'.clock = delay) := by
  cases h
  case init =>
    rename_i hm hi
    exact absurd hm hP.notInit
  case scan_wait =>
    rename_i hm hav hb
    obtain ⟨-, hr, -, -, -, -, -, -, -, hpr, -, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    exact Or.inl (front_congr hr hpr)
  case scan_count =>
    rename_i hm hc hav hb
    obtain ⟨-, hr, -, -, -, -, -, -, -, hpr, -, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    exact Or.inl (front_congr hr hpr)
  case scan_match =>
    rename_i s' o hmt hm hc hcmp hav hpl ho
    obtain ⟨hs'r, hs'p⟩ := compare_fields onLetter leftFirst centre place entry q first hcmp
    have hpl' : t = (if c.replaying then
        {s' with replay := GalilScaffoldCounter.dec s'.replay} else s') := hpl
    cases hcr : c.replaying with
    | false =>
      rw [hcr, if_neg (by simp)] at hpl'
      have hcan : GalilScaffoldChainVerifier.canRight s.right := by
        rcases hav with h | h
        · rw [hcr] at h; cases h
        · exact h
      obtain ⟨hpos, -⟩ := right_sane hcan hP.sane
      have htr : t.right = GalilScaffoldChainVerifier.right s.right := by rw [hpl']; exact hs'r
      have htp : t.replay = s.replay := by rw [hpl']; exact hs'p
      refine Or.inr ⟨?_, hc, rfl⟩
      simp only [front, htr, htp, hpos]; push_cast; omega
    | true =>
      rw [hcr, if_pos rfl] at hpl'
      obtain ⟨m, hm'⟩ := hP.replayPos hcr
      have hb := hP.frontier (m+1) hm'
      obtain ⟨hpos, -⟩ := right_sane (canRight_of_budget hb) hP.sane
      have htr : t.right = GalilScaffoldChainVerifier.right s.right := by rw [hpl', ← hs'r]
      have htp : t.replay = GalilScaffoldCounter.dec s.replay := by rw [hpl', ← hs'p]
      refine Or.inl ?_
      simp only [front, htr, htp, hpos, dec_value]; push_cast; omega
  case scan_shift =>
    rename_i s' hmt hg hm hc hr hcmp hav hb
    obtain ⟨hs'r, hs'p⟩ := compare_fields onLetter leftFirst centre place entry q first hcmp
    obtain ⟨w, -, ht⟩ : beginShiftVM' s' t := hb
    have hcan : GalilScaffoldChainVerifier.canRight s.right := by
      rcases hav with h | h
      · rw [hr] at h; cases h
      · exact h
    obtain ⟨hpos, -⟩ := right_sane hcan hP.sane
    have htr : t.right = GalilScaffoldChainVerifier.right s.right := by rw [ht]; exact hs'r
    have htp : t.replay = s.replay := by rw [ht]; exact hs'p
    refine Or.inr ⟨?_, hc, rfl⟩
    simp only [front, htr, htp, hpos]; push_cast; omega
  case scan_fallback =>
    rename_i s' hmt hm hc hg hr hcmp hav hb
    obtain ⟨hs'r, hs'p⟩ := compare_fields onLetter leftFirst centre place entry q first hcmp
    obtain ⟨pl, ht⟩ : beginFallbackVM' s' t := hb
    have hcan : GalilScaffoldChainVerifier.canRight s.right := by
      rcases hav with h | h
      · rw [hr] at h; cases h
      · exact h
    obtain ⟨hpos, -⟩ := right_sane hcan hP.sane
    have htr : t.right = GalilScaffoldChainVerifier.right s.right := by rw [ht]; exact hs'r
    have htp : t.replay = s.replay := by rw [ht]; exact hs'p
    refine Or.inr ⟨?_, hc, rfl⟩
    simp only [front, htr, htp, hpos]; push_cast; omega
  case shift_one =>
    rename_i hm hp hi
    exact Or.inl (front_congr ((congrArg GalilVM.right hi.2).trans rfl)
      ((congrArg GalilVM.replay hi.2).trans rfl))
  case shift_done => exact Or.inl rfl
  case copy_one =>
    rename_i hm hp hi
    exact Or.inl (front_congr ((congrArg GalilVM.right hi.2).trans rfl)
      ((congrArg GalilVM.replay hi.2).trans rfl))
  case copy_done =>
    rename_i hm hp hi
    exact Or.inl (front_congr ((congrArg GalilVM.right hi.2).trans rfl)
      ((congrArg GalilVM.replay hi.2).trans rfl))
  case home_start =>
    rename_i hm hl hi
    exact Or.inl (front_congr ((congrArg GalilVM.right hi.2).trans rfl)
      ((congrArg GalilVM.replay hi.2).trans rfl))
  case home_step =>
    rename_i hm hl hi
    exact Or.inl (front_congr ((congrArg GalilVM.right hi.2).trans rfl)
      ((congrArg GalilVM.replay hi.2).trans rfl))
  case fpp_slice =>
    rename_i hm hi
    exact Or.inl (front_congr ((congrArg GalilVM.right hi.2).trans rfl)
      ((congrArg GalilVM.replay hi.2).trans rfl))
  case fpp_done =>
    rename_i hm hi
    exact Or.inl (front_congr ((congrArg GalilVM.right hi.2).trans rfl)
      ((congrArg GalilVM.replay hi.2).trans rfl))
  case markEnd_found =>
    rename_i hm he hi
    have htr : t.right = s.right := (congrArg GalilVM.right hi.2).trans (by rw [hi.1.2]; rfl)
    exact Or.inl (front_congr htr ((congrArg GalilVM.replay hi.2).trans rfl))
  case markEnd_step =>
    rename_i hm he hi
    exact Or.inl (front_congr ((congrArg GalilVM.right hi.2).trans rfl)
      ((congrArg GalilVM.replay hi.2).trans rfl))
  case choose_select =>
    rename_i hm hodd hs hi
    have htr : t.right = s.right := (congrArg GalilVM.right hi.2).trans (by rw [hi.1]; rfl)
    exact Or.inl (front_congr htr ((congrArg GalilVM.replay hi.2).trans rfl))
  case choose_step =>
    rename_i hm hs hi
    have htr : t.right = s.right := (congrArg GalilVM.right hi.2).trans (by rw [hi.1.2]; rfl)
    exact Or.inl (front_congr htr ((congrArg GalilVM.replay hi.2).trans rfl))
  case rewind_done =>
    rename_i hm hfi hi
    have htr : t.right = s.right := (congrArg GalilVM.right hi.2).trans (by rw [hi.1]; rfl)
    exact Or.inl (front_congr htr ((congrArg GalilVM.replay hi.2).trans rfl))
  case rewind_one =>
    rename_i hm hpr hfi hi
    have htr : t.right = s.right := (congrArg GalilVM.right hi.2).trans (by rw [hi.1.2]; rfl)
    exact Or.inl (front_congr htr ((congrArg GalilVM.replay hi.2).trans rfl))
  case rewind_pair =>
    rename_i hm hpr hfi hi
    have htr : t.right = s.right := (congrArg GalilVM.right hi.2).trans (by rw [hi.1.2]; rfl)
    exact Or.inl (front_congr htr ((congrArg GalilVM.replay hi.2).trans rfl))
  case replayStart =>
    rename_i o hm ho ho' hi
    have hi' : replayStartVM entry s t := hi
    obtain ⟨r, hrad, heq, -⟩ := hP.rewind (Or.inr hm)
    have hsr : s.replay = GalilScaffoldCounter.reset :=
      hP.rest (Or.inl (hP.flag (by rw [hm]; decide)))
    have htr : t.right = s.center := hi'.2.1
    have htp : t.replay = ofNat r := hi'.1.trans hrad
    refine Or.inl ?_
    simp only [front, htr, htp, hsr, ofNat_value]
    simp [GalilScaffoldCounter.value, GalilScaffoldCounter.reset]
    omega
  case restart =>
    rename_i hm hb
    obtain ⟨w, -, -, -, -, ht⟩ : restartVM entry s t := hb
    exact Or.inl (front_congr (by rw [ht]) (by rw [ht]))

/-- **(a) `front_tick_mono`.** -/
theorem front_tick_mono {c c' : Control} {s t : GalilVM} (hP : FrontPack c s)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : front s ≤ front t := by
  cases h
  case init =>
    rename_i hm hi
    exact absurd hm hP.notInit
  case scan_wait =>
    rename_i hm hav hb
    obtain ⟨-, hr, -, -, -, -, -, -, -, hpr, -, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    exact le_of_eq (front_congr hr hpr).symm
  case scan_count =>
    rename_i hm hc hav hb
    obtain ⟨-, hr, -, -, -, -, -, -, -, hpr, -, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    exact le_of_eq (front_congr hr hpr).symm
  case scan_match =>
    rename_i s' o hmt hm hc hcmp hav hpl ho
    obtain ⟨hs'r, hs'p⟩ := compare_fields onLetter leftFirst centre place entry q first hcmp
    have hpl' : t = (if c.replaying then
        {s' with replay := GalilScaffoldCounter.dec s'.replay} else s') := hpl
    cases hcr : c.replaying with
    | false =>
      rw [hcr, if_neg (by simp)] at hpl'
      have hcan : GalilScaffoldChainVerifier.canRight s.right := by
        rcases hav with h | h
        · rw [hcr] at h; cases h
        · exact h
      obtain ⟨hpos, -⟩ := right_sane hcan hP.sane
      have htr : t.right = GalilScaffoldChainVerifier.right s.right := by rw [hpl']; exact hs'r
      have htp : t.replay = s.replay := by rw [hpl']; exact hs'p
      simp only [front, htr, htp, hpos]; push_cast; omega
    | true =>
      rw [hcr, if_pos rfl] at hpl'
      obtain ⟨m, hm'⟩ := hP.replayPos hcr
      have hb := hP.frontier (m+1) hm'
      obtain ⟨hpos, -⟩ := right_sane (canRight_of_budget hb) hP.sane
      have htr : t.right = GalilScaffoldChainVerifier.right s.right := by rw [hpl', ← hs'r]
      have htp : t.replay = GalilScaffoldCounter.dec s.replay := by rw [hpl', ← hs'p]
      simp only [front, htr, htp, hpos, dec_value]; push_cast; omega
  case scan_shift =>
    rename_i s' hmt hg hm hc hr hcmp hav hb
    obtain ⟨hs'r, hs'p⟩ := compare_fields onLetter leftFirst centre place entry q first hcmp
    obtain ⟨w, -, ht⟩ : beginShiftVM' s' t := hb
    have hcan : GalilScaffoldChainVerifier.canRight s.right := by
      rcases hav with h | h
      · rw [hr] at h; cases h
      · exact h
    obtain ⟨hpos, -⟩ := right_sane hcan hP.sane
    have htr : t.right = GalilScaffoldChainVerifier.right s.right := by rw [ht]; exact hs'r
    have htp : t.replay = s.replay := by rw [ht]; exact hs'p
    simp only [front, htr, htp, hpos]; push_cast; omega
  case scan_fallback =>
    rename_i s' hmt hm hc hg hr hcmp hav hb
    obtain ⟨hs'r, hs'p⟩ := compare_fields onLetter leftFirst centre place entry q first hcmp
    obtain ⟨pl, ht⟩ : beginFallbackVM' s' t := hb
    have hcan : GalilScaffoldChainVerifier.canRight s.right := by
      rcases hav with h | h
      · rw [hr] at h; cases h
      · exact h
    obtain ⟨hpos, -⟩ := right_sane hcan hP.sane
    have htr : t.right = GalilScaffoldChainVerifier.right s.right := by rw [ht]; exact hs'r
    have htp : t.replay = s.replay := by rw [ht]; exact hs'p
    simp only [front, htr, htp, hpos]; push_cast; omega
  case shift_one =>
    rename_i hm hp hi
    exact le_of_eq (front_congr ((congrArg GalilVM.right hi.2).trans rfl)
      ((congrArg GalilVM.replay hi.2).trans rfl)).symm
  case shift_done => exact le_rfl
  case copy_one =>
    rename_i hm hp hi
    exact le_of_eq (front_congr ((congrArg GalilVM.right hi.2).trans rfl)
      ((congrArg GalilVM.replay hi.2).trans rfl)).symm
  case copy_done =>
    rename_i hm hp hi
    exact le_of_eq (front_congr ((congrArg GalilVM.right hi.2).trans rfl)
      ((congrArg GalilVM.replay hi.2).trans rfl)).symm
  case home_start =>
    rename_i hm hl hi
    exact le_of_eq (front_congr ((congrArg GalilVM.right hi.2).trans rfl)
      ((congrArg GalilVM.replay hi.2).trans rfl)).symm
  case home_step =>
    rename_i hm hl hi
    exact le_of_eq (front_congr ((congrArg GalilVM.right hi.2).trans rfl)
      ((congrArg GalilVM.replay hi.2).trans rfl)).symm
  case fpp_slice =>
    rename_i hm hi
    exact le_of_eq (front_congr ((congrArg GalilVM.right hi.2).trans rfl)
      ((congrArg GalilVM.replay hi.2).trans rfl)).symm
  case fpp_done =>
    rename_i hm hi
    exact le_of_eq (front_congr ((congrArg GalilVM.right hi.2).trans rfl)
      ((congrArg GalilVM.replay hi.2).trans rfl)).symm
  case markEnd_found =>
    rename_i hm he hi
    have htr : t.right = s.right := (congrArg GalilVM.right hi.2).trans (by rw [hi.1.2]; rfl)
    exact le_of_eq (front_congr htr ((congrArg GalilVM.replay hi.2).trans rfl)).symm
  case markEnd_step =>
    rename_i hm he hi
    exact le_of_eq (front_congr ((congrArg GalilVM.right hi.2).trans rfl)
      ((congrArg GalilVM.replay hi.2).trans rfl)).symm
  case choose_select =>
    rename_i hm hodd hs hi
    have htr : t.right = s.right := (congrArg GalilVM.right hi.2).trans (by rw [hi.1]; rfl)
    exact le_of_eq (front_congr htr ((congrArg GalilVM.replay hi.2).trans rfl)).symm
  case choose_step =>
    rename_i hm hs hi
    have htr : t.right = s.right := (congrArg GalilVM.right hi.2).trans (by rw [hi.1.2]; rfl)
    exact le_of_eq (front_congr htr ((congrArg GalilVM.replay hi.2).trans rfl)).symm
  case rewind_done =>
    rename_i hm hfi hi
    have htr : t.right = s.right := (congrArg GalilVM.right hi.2).trans (by rw [hi.1]; rfl)
    exact le_of_eq (front_congr htr ((congrArg GalilVM.replay hi.2).trans rfl)).symm
  case rewind_one =>
    rename_i hm hpr hfi hi
    have htr : t.right = s.right := (congrArg GalilVM.right hi.2).trans (by rw [hi.1.2]; rfl)
    exact le_of_eq (front_congr htr ((congrArg GalilVM.replay hi.2).trans rfl)).symm
  case rewind_pair =>
    rename_i hm hpr hfi hi
    have htr : t.right = s.right := (congrArg GalilVM.right hi.2).trans (by rw [hi.1.2]; rfl)
    exact le_of_eq (front_congr htr ((congrArg GalilVM.replay hi.2).trans rfl)).symm
  case replayStart =>
    rename_i o hm ho ho' hi
    have hi' : replayStartVM entry s t := hi
    obtain ⟨r, hrad, heq, -⟩ := hP.rewind (Or.inr hm)
    have hsr : s.replay = GalilScaffoldCounter.reset :=
      hP.rest (Or.inl (hP.flag (by rw [hm]; decide)))
    have htr : t.right = s.center := hi'.2.1
    have htp : t.replay = ofNat r := hi'.1.trans hrad
    simp only [front, htr, htp, hsr, ofNat_value]
    simp [GalilScaffoldCounter.value, GalilScaffoldCounter.reset]
    omega
  case restart =>
    rename_i hm hb
    obtain ⟨w, -, -, -, -, ht⟩ : restartVM entry s t := hb
    exact le_of_eq (front_congr (by rw [ht]) (by rw [ht])).symm

end Tick

/-! ## Pack preservation -/

section Pack
variable (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
  (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)

theorem notInit_tick {c c' : Control} {s t : GalilVM} (hP : FrontPack c s)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : c'.mode ≠ Mode.init := by
  cases h <;> first | exact hP.notInit | (intro hh; cases hh)

theorem flag_tick {c c' : Control} {s t : GalilVM} (hP : FrontPack c s)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : c'.mode ≠ Mode.scan → c'.replaying = false := by
  cases h <;> intro hh <;>
    first
    | exact (hh rfl).elim
    | exact (hh ‹c.mode = Mode.scan›).elim
    | exact ‹c.replaying = false›
    | exact hP.flag (by not_scan)

theorem replayPos_keep {c c' : Control} {s t : GalilVM} (hP : FrontPack c s)
    (hr : c'.replaying = c.replaying) (ht : t.replay = s.replay) :
    c'.replaying = true → ∃ m, t.replay = ofNat (m+1) := by
  intro h
  rw [ht]
  exact hP.replayPos (hr ▸ h)

theorem replayPos_tick {c c' : Control} {s t : GalilVM} (hP : FrontPack c s)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : c'.replaying = true → ∃ m, t.replay = ofNat (m+1) := by
  cases h
  case init =>
    rename_i hm hi
    exact absurd hm hP.notInit
  case scan_wait =>
    rename_i hm hav hb
    intro h; rw [hav.1] at h; cases h
  case scan_count =>
    rename_i hm hc hav hb
    obtain ⟨-, -, -, -, -, -, -, -, -, hpr, -, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    exact replayPos_keep hP rfl hpr
  case scan_match =>
    rename_i s' o hmt hm hc hcmp hav hpl ho
    obtain ⟨-, hs'p⟩ := compare_fields onLetter leftFirst centre place entry q first hcmp
    have hpl' : t = (if c.replaying then
        {s' with replay := GalilScaffoldCounter.dec s'.replay} else s') := hpl
    intro hflag
    have hflag' : (c.replaying &&
        !(galilFrameS (sharedC onLetter leftFirst centre place entry) q first).replayExhausted t)
          = true := hflag
    cases hcr : c.replaying with
    | false => rw [hcr] at hflag'; cases hflag'
    | true =>
      rw [hcr, Bool.true_and] at hflag'
      rw [hcr, if_pos rfl] at hpl'
      obtain ⟨m, hm'⟩ := hP.replayPos hcr
      have htp : t.replay = ofNat m := by
        rw [hpl']; show GalilScaffoldCounter.dec s'.replay = _; rw [hs'p, hm']
        simp [GalilScaffoldCounter.dec, ofNat, List.replicate_succ]
      have hz : GalilScaffoldCounter.zero t.replay = false := by
        have : (!GalilScaffoldCounter.zero t.replay) = true := hflag'
        simpa using this
      rw [htp] at hz ⊢
      cases m with
      | zero => simp [GalilScaffoldCounter.zero, ofNat] at hz
      | succ m => exact ⟨m, rfl⟩
  case scan_shift =>
    rename_i s' hmt hg hm hc hr hcmp hav hb
    intro h; rw [show c.replaying = false from hr] at h; cases h
  case scan_fallback =>
    rename_i s' hmt hm hc hg hr hcmp hav hb
    intro h; rw [show c.replaying = false from hr] at h; cases h
  case shift_one =>
    rename_i hm hp hi
    exact replayPos_keep hP rfl ((congrArg GalilVM.replay hi.2).trans rfl)
  case shift_done => exact replayPos_keep hP rfl rfl
  case copy_one =>
    rename_i hm hp hi
    exact replayPos_keep hP rfl ((congrArg GalilVM.replay hi.2).trans rfl)
  case copy_done =>
    rename_i hm hp hi
    exact replayPos_keep hP rfl ((congrArg GalilVM.replay hi.2).trans rfl)
  case home_start =>
    rename_i hm hl hi
    exact replayPos_keep hP rfl ((congrArg GalilVM.replay hi.2).trans rfl)
  case home_step =>
    rename_i hm hl hi
    exact replayPos_keep hP rfl ((congrArg GalilVM.replay hi.2).trans rfl)
  case fpp_slice =>
    rename_i hm hi
    exact replayPos_keep hP rfl ((congrArg GalilVM.replay hi.2).trans rfl)
  case fpp_done =>
    rename_i hm hi
    exact replayPos_keep hP rfl ((congrArg GalilVM.replay hi.2).trans rfl)
  case markEnd_found =>
    rename_i hm he hi
    exact replayPos_keep hP rfl ((congrArg GalilVM.replay hi.2).trans rfl)
  case markEnd_step =>
    rename_i hm he hi
    exact replayPos_keep hP rfl ((congrArg GalilVM.replay hi.2).trans rfl)
  case choose_select =>
    rename_i hm hodd hs hi
    exact replayPos_keep hP rfl ((congrArg GalilVM.replay hi.2).trans rfl)
  case choose_step =>
    rename_i hm hs hi
    exact replayPos_keep hP rfl ((congrArg GalilVM.replay hi.2).trans rfl)
  case rewind_done =>
    rename_i hm hfi hi
    exact replayPos_keep hP rfl ((congrArg GalilVM.replay hi.2).trans rfl)
  case rewind_one =>
    rename_i hm hpr hfi hi
    exact replayPos_keep hP rfl ((congrArg GalilVM.replay hi.2).trans rfl)
  case rewind_pair =>
    rename_i hm hpr hfi hi
    exact replayPos_keep hP rfl ((congrArg GalilVM.replay hi.2).trans rfl)
  case replayStart =>
    rename_i o hm ho ho' hi
    have hi' : replayStartVM entry s t := hi
    obtain ⟨r, hrad, -, -⟩ := hP.rewind (Or.inr hm)
    have htp : t.replay = ofNat r := hi'.1.trans hrad
    intro hflag
    have hpos : GalilScaffoldCounter.positive t.replay = true := hflag
    rw [htp, positive_ofNat] at hpos
    rw [htp]
    cases r with
    | zero => simp at hpos
    | succ r => exact ⟨r, rfl⟩
  case restart =>
    rename_i hm hb
    obtain ⟨w, -, -, -, -, ht⟩ : restartVM entry s t := hb
    exact replayPos_keep hP rfl (by rw [ht])

theorem sane_tick {c c' : Control} {s t : GalilVM} (hP : FrontPack c s)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : Sane t.right := by
  cases h
  case init =>
    rename_i hm hi
    exact absurd hm hP.notInit
  case scan_wait =>
    rename_i hm hav hb
    obtain ⟨-, hr, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    rw [hr]; exact hP.sane
  case scan_count =>
    rename_i hm hc hav hb
    obtain ⟨-, hr, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    rw [hr]; exact hP.sane
  case scan_match =>
    rename_i s' o hmt hm hc hcmp hav hpl ho
    obtain ⟨hs'r, -⟩ := compare_fields onLetter leftFirst centre place entry q first hcmp
    have hpl' : t = (if c.replaying then
        {s' with replay := GalilScaffoldCounter.dec s'.replay} else s') := hpl
    have htr : t.right = GalilScaffoldChainVerifier.right s.right := by
      rw [← hs'r, hpl']; cases c.replaying <;> rfl
    have hcan : GalilScaffoldChainVerifier.canRight s.right := by
      cases hcr : c.replaying with
      | false =>
        rcases hav with h | h
        · rw [hcr] at h; cases h
        · exact h
      | true =>
        obtain ⟨m, hm'⟩ := hP.replayPos hcr
        exact canRight_of_budget (hP.frontier (m+1) hm')
    rw [htr]; exact (right_sane hcan hP.sane).2
  case scan_shift =>
    rename_i s' hmt hg hm hc hr hcmp hav hb
    obtain ⟨hs'r, -⟩ := compare_fields onLetter leftFirst centre place entry q first hcmp
    obtain ⟨w, -, ht⟩ : beginShiftVM' s' t := hb
    have hcan : GalilScaffoldChainVerifier.canRight s.right := by
      rcases hav with h | h
      · rw [hr] at h; cases h
      · exact h
    have htr : t.right = GalilScaffoldChainVerifier.right s.right := by rw [ht]; exact hs'r
    rw [htr]; exact (right_sane hcan hP.sane).2
  case scan_fallback =>
    rename_i s' hmt hm hc hg hr hcmp hav hb
    obtain ⟨hs'r, -⟩ := compare_fields onLetter leftFirst centre place entry q first hcmp
    obtain ⟨pl, ht⟩ : beginFallbackVM' s' t := hb
    have hcan : GalilScaffoldChainVerifier.canRight s.right := by
      rcases hav with h | h
      · rw [hr] at h; cases h
      · exact h
    have htr : t.right = GalilScaffoldChainVerifier.right s.right := by rw [ht]; exact hs'r
    rw [htr]; exact (right_sane hcan hP.sane).2
  case shift_one =>
    rename_i hm hp hi
    rw [(congrArg GalilVM.right hi.2).trans rfl]; exact hP.sane
  case shift_done => exact hP.sane
  case copy_one =>
    rename_i hm hp hi
    rw [(congrArg GalilVM.right hi.2).trans rfl]; exact hP.sane
  case copy_done =>
    rename_i hm hp hi
    rw [(congrArg GalilVM.right hi.2).trans rfl]; exact hP.sane
  case home_start =>
    rename_i hm hl hi
    rw [(congrArg GalilVM.right hi.2).trans rfl]; exact hP.sane
  case home_step =>
    rename_i hm hl hi
    rw [(congrArg GalilVM.right hi.2).trans rfl]; exact hP.sane
  case fpp_slice =>
    rename_i hm hi
    rw [(congrArg GalilVM.right hi.2).trans rfl]; exact hP.sane
  case fpp_done =>
    rename_i hm hi
    rw [(congrArg GalilVM.right hi.2).trans rfl]; exact hP.sane
  case markEnd_found =>
    rename_i hm he hi
    have htr : t.right = s.right := (congrArg GalilVM.right hi.2).trans (by rw [hi.1.2]; rfl)
    rw [htr]; exact hP.sane
  case markEnd_step =>
    rename_i hm he hi
    rw [(congrArg GalilVM.right hi.2).trans rfl]; exact hP.sane
  case choose_select =>
    rename_i hm hodd hs hi
    have htr : t.right = s.right := (congrArg GalilVM.right hi.2).trans (by rw [hi.1]; rfl)
    rw [htr]; exact hP.sane
  case choose_step =>
    rename_i hm hs hi
    have htr : t.right = s.right := (congrArg GalilVM.right hi.2).trans (by rw [hi.1.2]; rfl)
    rw [htr]; exact hP.sane
  case rewind_done =>
    rename_i hm hfi hi
    have htr : t.right = s.right := (congrArg GalilVM.right hi.2).trans (by rw [hi.1]; rfl)
    rw [htr]; exact hP.sane
  case rewind_one =>
    rename_i hm hpr hfi hi
    have htr : t.right = s.right := (congrArg GalilVM.right hi.2).trans (by rw [hi.1.2]; rfl)
    rw [htr]; exact hP.sane
  case rewind_pair =>
    rename_i hm hpr hfi hi
    have htr : t.right = s.right := (congrArg GalilVM.right hi.2).trans (by rw [hi.1.2]; rfl)
    rw [htr]; exact hP.sane
  case replayStart =>
    rename_i o hm ho ho' hi
    have hi' : replayStartVM entry s t := hi
    obtain ⟨r, -, -, hsc⟩ := hP.rewind (Or.inr hm)
    rw [hi'.2.1]; exact hsc
  case restart =>
    rename_i hm hb
    obtain ⟨w, -, -, -, -, ht⟩ : restartVM entry s t := hb
    rw [ht]; exact hP.sane

theorem rewindEq_tick {c c' : Control} {s t : GalilVM} (hP : FrontPack c s)
    (hg : CentreLive c s)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : RewindEq c' t := by
  cases h
  case choose_select =>
    rename_i hm hodd hs hi
    have hc : t.center = s.right := congrArg RewindVM.center hi.1
    have hr : t.radius = reset := congrArg RewindVM.radius hi.1
    have htr : t.right = s.right := (congrArg GalilVM.right hi.2).trans (by rw [hi.1]; rfl)
    intro _
    exact ⟨0, by rw [hr]; rfl, by rw [hc, htr]; rfl, by rw [hc]; exact hP.sane⟩
  case rewind_one =>
    rename_i hm h1 h2 hi
    have hc : t.center = s.center := congrArg RewindVM.center hi.1.2
    have hr : t.radius = s.radius := congrArg RewindVM.radius hi.1.2
    have htr : t.right = s.right := (congrArg GalilVM.right hi.2).trans (by rw [hi.1.2]; rfl)
    intro _
    obtain ⟨r, hrad, heq, hsc⟩ := hP.rewind (Or.inl hm)
    exact ⟨r, by rw [hr]; exact hrad, by rw [hc, htr]; exact heq, by rw [hc]; exact hsc⟩
  case rewind_pair =>
    rename_i hm h1 h2 hi
    have hc : t.center = GalilScaffoldInputHead.left s.center :=
      congrArg RewindVM.center hi.1.2
    have hr : t.radius = inc s.radius := congrArg RewindVM.radius hi.1.2
    have htr : t.right = s.right := (congrArg GalilVM.right hi.2).trans (by rw [hi.1.2]; rfl)
    intro _
    obtain ⟨r, hrad, heq, -⟩ := hP.rewind (Or.inl hm)
    have hpos : 0 < position s.center := hg hm h1
    have hstep := left_position_pos hpos
    refine ⟨r + 1, by rw [hr, hrad, inc_ofNat], ?_, by rw [hc]; exact left_sane hpos⟩
    rw [hc, htr]; omega
  case rewind_done =>
    rename_i hm h1 hi
    have hc : t.center = s.center := congrArg RewindVM.center hi.1
    have hr : t.radius = s.radius := congrArg RewindVM.radius hi.1
    have htr : t.right = s.right := (congrArg GalilVM.right hi.2).trans (by rw [hi.1]; rfl)
    intro _
    obtain ⟨r, hrad, heq, hsc⟩ := hP.rewind (Or.inl hm)
    exact ⟨r, by rw [hr]; exact hrad, by rw [hc, htr]; exact heq, by rw [hc]; exact hsc⟩
  all_goals vacuous_eq

/-- The whole pack travels along one tick, given `CentreLive` at the source. -/
theorem frontPack_tick {c c' : Control} {s t : GalilVM} (hP : FrontPack c s)
    (hg : CentreLive c s)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : FrontPack c' t :=
  { notInit := notInit_tick onLetter leftFirst centre place entry q first delay hP h
    flag := flag_tick onLetter leftFirst centre place entry q first delay hP h
    sane := sane_tick onLetter leftFirst centre place entry q first delay hP h
    rewind := rewindEq_tick onLetter leftFirst centre place entry q first delay hP hg h
    replayPos := replayPos_tick onLetter leftFirst centre place entry q first delay hP h
    phase := rewindPhase_tick onLetter leftFirst centre place entry q first delay hP.phase hg h
    frontier := frontier_tick onLetter leftFirst centre place entry q first delay hP.rest
      hP.frontier (rewindSafe_of_phase hP.phase).2 h
    rest := replayRest_tick onLetter leftFirst centre place entry q first delay hP.rest
      (rewindSafe_of_phase hP.phase).1 h }

/-! ## (b) Along a run -/

/-- **(b) `front_steps_mono`.**  Along any run whose states are all
`CentreLive`, the pack travels and the frontier does not decrease. -/
theorem front_steps_mono {n : ℕ} {x y : State GalilVM}
    (h : Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay n x y)
    (hg : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay m x z →
      CentreLive z.ctl z.vm)
    (hP : FrontPack x.ctl x.vm) : FrontPack y.ctl y.vm ∧ front x.vm ≤ front y.vm := by
  induction h with
  | zero x => exact ⟨hP, le_rfl⟩
  | @succ n x w y ht _ ih =>
    have h0 := hg 0 x (.zero x)
    have hw := frontPack_tick onLetter leftFirst centre place entry q first delay hP h0 ht
    have hfw := front_tick_mono onLetter leftFirst centre place entry q first delay hP ht
    obtain ⟨h1, h2⟩ := ih (fun m z hz => hg (m+1) z (.succ ht hz)) hw
    exact ⟨h1, le_trans hfw h2⟩

theorem front_stepsAll_mono {Q : State GalilVM → Prop} {n : ℕ} {x y : State GalilVM}
    (h : StepsAll (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay Q
      n x y)
    (hg : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay m x z →
      CentreLive z.ctl z.vm)
    (hP : FrontPack x.ctl x.vm) : front x.vm ≤ front y.vm :=
  (front_steps_mono onLetter leftFirst centre place entry q first delay (stepsAll_steps h) hg hP).2

end Pack

/-! ## (c) The oracle with the frontier obligation -/

section Oracle
open PalPeg.GalilRunSkeleton PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open GalilScaffoldChainVerifier
open PalPeg.GalilBranchInvariants2 (SearchReady)

/-- **(c) `cycleOracleL'_of_pieces`.**  The hypotheses of
`cycleOracleL_of_pieces`, plus `CentreLive` along every run out of an `InvL`
state, give the oracle with the frontier obligation discharged. -/
theorem cycleOracleL'_of_pieces (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry raw) a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) →
      searchEffect (PofC centre place entry raw) a s v → SearchReady v)
    (hquiet : PalPeg.GalilReplaySegment.SearchQuiet (PofC centre place entry raw))
    (houtReplay : ∀ (c' : Control) (t' : GalilVM) (k : ℕ),
      PalPeg.GalilReplaySegment.InvScan 2048 raw c' t' k → SoundScanNR raw ⟨c', t'⟩)
    (hsegment : ∀ (c : Control) (r : GalilVM), InvL raw c r →
      ∃ (c' : Control) (t : GalilVM),
        SegReached centre place entry q first raw c r c' t ∧
        PalPeg.GalilSegmentConstruct.SegEnd (PofC centre place entry raw) c' t)
    (hended : ∀ (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM), InvL raw c r →
      SegReached centre place entry q first raw c r c' t → ¬ canRight t.right →
      LocalReport (PofC centre place entry raw) q first raw c r)
    (hlastMatch : ∀ (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM), InvL raw c r →
      SegReached centre place entry q first raw c r c' t →
      c'.clock = 1 → canRight t.right → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      read (left t.left) = read (right t.right) →
      LocalReport (PofC centre place entry raw) q first raw c r)
    (hlastMismatch : ∀ (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM), InvL raw c r →
      SegReached centre place entry q first raw c r c' t →
      c'.clock = 1 → canRight t.right → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      read (left t.left) ≠ read (right t.right) →
      LocalReport (PofC centre place entry raw) q first raw c r)
    (hmismatch : ∀ (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM), InvL raw c r →
      SegReached centre place entry q first raw c r c' t →
      c'.replaying = false → c'.clock = 1 → canRight t.right →
      read (left t.left) ≠ read (right t.right) →
      FallbackRouteL (PofC centre place entry raw) q first raw c r)
    (hfound : ∀ (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM), InvL raw c r →
      SegReached centre place entry q first raw c r c' t →
      c'.clock = 1 → canRight t.right →
      read (left t.left) = read (right t.right) →
      (∃ vq, searchEffect (PofC centre place entry raw) true t vq ∧ vq.search.mode = .found) →
      FoundRouteL (PofC centre place entry raw) q first raw c r)
    (hfoundBg : ∀ (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM), InvL raw c r →
      SegReached centre place entry q first raw c r c' t → 1 ≤ c'.clock →
      (∃ vq, searchEffect (PofC centre place entry raw) false t vq ∧ vq.search.mode = .found) →
      FoundRouteL (PofC centre place entry raw) q first raw c r)
    (hlive : ∀ (c : Control) (r : GalilVM), InvL raw c r →
      ∀ (m : ℕ) (z : State GalilVM),
        Steps (galilFrameS (PofC centre place entry raw) q first) 2048 m ⟨c, r⟩ z →
        CentreLive z.ctl z.vm) :
    CycleOracleL' (PofC centre place entry raw) q first raw := by
  intro c r hI
  rcases cycleOracleL_of_pieces centre place entry q first raw hex hsearch hpres hquiet houtReplay
      hsegment hended hlastMatch hlastMismatch hmismatch hfound hfoundBg c r hI with
    h | ⟨cT, sT, k, hst, hIT, hlt⟩
  · exact Or.inl h
  · exact Or.inr ⟨cT, sT, k, hst, hIT, hlt,
      front_stepsAll_mono (onLetterVM raw) leftFirstVM centre place entry q first 2048 hst
        (hlive c r hI) (frontPack_of_invS hI.1)⟩

end Oracle

#print axioms right_sane
#print axioms canRight_of_budget
#print axioms left_sane
#print axioms frontPack_of_invS
#print axioms front_tick_mono
#print axioms notInit_tick
#print axioms flag_tick
#print axioms replayPos_tick
#print axioms sane_tick
#print axioms rewindEq_tick
#print axioms frontPack_tick
#print axioms front_steps_mono
#print axioms front_stepsAll_mono
#print axioms cycleOracleL'_of_pieces

end PalPeg.GalilFrontMono
