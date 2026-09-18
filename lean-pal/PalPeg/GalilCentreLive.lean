import PalPeg.GalilFrontMono
import PalPeg.GalilTickFun3
import PalPeg.GalilScaffoldTopFallbackChain
import PalPeg.GalilGlueBLeaves
import PalPeg.GalilOracleLocal

/-!
# `CentreLive` along every run

`CentreLive` (`GalilRewindSafe`) is the last named hypothesis of
`rewindSafe_of_run`, `front_steps_mono` and `cycleOracleL'_of_pieces`.  This
module proves it along every run of the concrete scaffold by carrying `CPack`:

* `rewind`: `mh + [pair] ≤ 2·position center` (`mh` = MARKS head).  Every
  rewind tick moves MARKS one cell left (its `left ≠ []` guard), a pair tick
  also moves the centre, so the bound is kept; with `pair = true` it forces
  `0 < position center`, which is `CentreLive`.
* `choose` sets `center := right`, so it needs `mh ≤ 2·position right`; the
  `choose` walk only lowers `mh`, and `markEnd` lands one cell before an `END`
  that is at most `2·position right + 1`.
* `fpp`/`copy`/`home`: the FPP control is deterministic (`ftick_unique`), so
  the pending run to the prepared program `⟨fppInitial w, false⟩` and then
  `fpp_outcome_program`/`marks_after_fpp` pin the MARKS tape to the layout of
  a window `w` with `|w| ≤ 2·position right`; its only `END` is at `|w|+1`.
* `scan`/`shift`: `value length ≤ 2·position right + 1` (a comparison adds at
  most `2` while moving the right head one place; a shift unit subtracts `2`;
  `replayStart` resets to `1`).  At `scan_fallback` the window is
  `take (value length + 1)`, which gives `|w| ≤ 2·position right`.

**The one gap, `hfloor`.**  `fallback_prepared` needs `0 ≤ value length` at the
fallback: with a negative counter the copy phase never sees `work = 0` and
copies the whole (arbitrary) stream of the existential place `p`, so no bound
on the rewind survives.  Non-negativity is the Galil fact that a chain shift
never exceeds the radius (`h ≤ Rad`), which is not a tick-local property, so it
is taken as the hypothesis `hfloor` on the run's `scan` states.  `InvS` alone
also does not carry the two entry facts (`Canonical length`, the span bound);
`EntryCounters` (i.e. `InvLP`) does.
-/

set_option autoImplicit false
namespace PalPeg.GalilCentreLive
open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainInputSupply PalPeg.GalilFrontMono

/-! ## The FPP control is deterministic -/

theorem ftick_not_run {x y : FppControl.State} (h : FppControl.Tick true x y) :
    x.mode ≠ FppControl.Mode.run := by
  cases h <;> (intro h0; simp_all)

theorem ftick_unique {x y y' : FppControl.State} (h1 : FppControl.Tick true x y)
    (h2 : FppControl.Tick true x y') : y = y' := by
  cases h1 with
  | copyBit _ a hm ha hw =>
    cases h2 with
    | copyBit _ a' _ ha' _ =>
      rw [ha] at ha'; cases ha'; rfl
    | copyEnd _ _ he =>
      rcases he with he | he
      · rw [ha] at he; cases he
      · rw [hw] at he; cases he
    | sourceLeft _ hm' _ _ => rw [hm] at hm'; cases hm'
    | startRun _ hm' _ => rw [hm] at hm'; cases hm'
  | copyEnd _ hm he =>
    cases h2 with
    | copyBit _ a' _ ha' hw' =>
      rcases he with he | he
      · rw [ha'] at he; cases he
      · rw [hw'] at he; cases he
    | copyEnd => rfl
    | sourceLeft _ hm' _ _ => rw [hm] at hm'; cases hm'
    | startRun _ hm' _ => rw [hm] at hm'; cases hm'
  | sourceLeft _ hm hf hl =>
    cases h2 with
    | copyBit _ _ hm' _ _ => rw [hm] at hm'; cases hm'
    | copyEnd _ hm' _ => rw [hm] at hm'; cases hm'
    | sourceLeft => rfl
    | startRun _ _ hf' => exact absurd hf' hf
  | startRun _ hm hf =>
    cases h2 with
    | copyBit _ _ hm' _ _ => rw [hm] at hm'; cases hm'
    | copyEnd _ hm' _ => rw [hm] at hm'; cases hm'
    | sourceLeft _ _ hf' _ => exact absurd hf hf'
    | startRun => rfl

/-- A pending run to a `run`-mode state survives one enabled tick. -/
theorem future_step {x y t0 : FppControl.State} {k : ℕ}
    (hr : FppControl.Run x (List.replicate k true) t0) (h0 : t0.mode = FppControl.Mode.run)
    (ht : FppControl.Tick true x y) : ∃ k', FppControl.Run y (List.replicate k' true) t0 := by
  cases k with
  | zero =>
    cases hr
    exact absurd h0 (ftick_not_run ht)
  | succ k =>
    rw [List.replicate_succ] at hr
    cases hr with
    | cons _ y' _ _ _ ht' hr' =>
      rw [ftick_unique ht ht']
      exact ⟨k, hr'⟩

/-- A pending run from a `run`-mode state is empty. -/
theorem future_run {y t0 : FppControl.State} {k : ℕ}
    (hr : FppControl.Run y (List.replicate k true) t0) (hy : y.mode = FppControl.Mode.run) :
    y = t0 := by
  cases k with
  | zero => cases hr; rfl
  | succ k =>
    rw [List.replicate_succ] at hr
    cases hr with
    | cons _ _ _ _ _ ht _ => exact absurd hy (ftick_not_run ht)

theorem toController_copy {m : FppControl.Mode} (h : m.toController = Mode.copy) :
    m = FppControl.Mode.copy := by
  cases m <;> first | rfl | cases h

theorem toController_home {m : FppControl.Mode} (h : m.toController = Mode.home) :
    m = FppControl.Mode.home := by
  cases m <;> first | rfl | cases h

/-! ## The MARKS layout after the FPP program -/

theorem layout_end (first : Fin 9) (w : List (Fin 3)) (B : ℕ) (hb : w.length ≤ B) :
    ∀ e, 2 ≤ e → Function.update (GalilFppMarkedLayout.marks w) 1 first e = 5 → e ≤ B + 1 := by
  intro e he h5
  rw [Function.update_of_ne (by omega)] at h5
  unfold GalilFppMarkedLayout.marks at h5
  have : e ≠ 0 := by omega
  simp only [this, if_false] at h5
  by_cases h1 : e ≤ w.length
  · simp only [h1, if_true] at h5
    split at h5 <;> cases h5
  · simp only [h1, if_false] at h5
    by_cases h2 : e = w.length + 1
    · omega
    · simp only [h2, if_false] at h5; cases h5


/-! ## The carrier -/

/-- The MARKS head position. -/
def mh (s : GalilVM) : ℕ := GalilScaffoldTape.head (marksTape s.fpp)

/-- The pack carried along a run: `FrontPack`, shift idleness outside `shift`,
the span bound of the length counter against the right head in `scan`/`shift`,
and, for each fallback phase, what bounds the MARKS walk by the right head
(`copy`/`home`/`fpp`: the pending FPP window is at most `2·position right`
long; `markEnd`: every `END` ahead is at most `2·position right + 1`;
`choose`: the MARKS head is at most `2·position right`; `rewind`: the MARKS
head plus the pending half-step is at most `2·position center`). -/
structure CPack (q : ℕ) (c : Control) (s : GalilVM) : Prop where
  front : FrontPack c s
  idle : c.mode ≠ Mode.shift → ShiftIdle s
  canon : Canonical s.length
  span : c.mode = Mode.scan ∨ c.mode = Mode.shift →
    value s.length ≤ 2 * (position s.right : ℤ) + 1
  copy : c.mode = Mode.copy ∨ c.mode = Mode.home →
    ∃ (w : List (Fin 3)) (k : ℕ) (t0 : FppControl.State),
      w.length ≤ 2 * position s.right ∧ s.fpp.mode.toController = c.mode ∧
      FppControl.Run s.fpp (List.replicate k true) t0 ∧ t0.mode = FppControl.Mode.run ∧
      t0.program = ⟨fppInitial w, false⟩
  fpp : c.mode = Mode.fpp → ∃ (w : List (Fin 3)) (n : ℕ), w.length ≤ 2 * position s.right ∧
    GalilScaffoldControl.Run GalilFppMarkedCode.code ⟨fppInitial w, false⟩
      (List.replicate (n*q) true) s.fpp.program
  markEnd : c.mode = Mode.markEnd → ∀ e, mh s ≤ e →
    GalilScaffoldTape.denote (marksTape s.fpp) e = 5 → e ≤ 2 * position s.right + 1
  choose : c.mode = Mode.choose → mh s ≤ 2 * position s.right
  rewind : c.mode = Mode.rewind → mh s + (if c.pair then 1 else 0) ≤ 2 * position s.center

/-- **`CentreLive` is read off the pack.** -/
theorem centreLive_of_pack {q : ℕ} {c : Control} {s : GalilVM} (h : CPack q c s) :
    CentreLive c s := by
  intro hm hp
  have := h.rewind hm
  rw [hp, if_pos rfl] at this
  omega

/-- Discharge a mode-guarded field whose guard the landing mode refutes. -/
macro "vac" : tactic => `(tactic| first
  | (intro hx; exfalso; cases hx; done)
  | (intro hx; exfalso; exact hx rfl)
  | (rw [‹GalilScaffoldController.Control.mode _ = _›]; intro hx; exfalso; exact hx rfl)
  | (rintro (hx | hx) <;> exfalso <;> cases hx; done)
  | (rw [‹GalilScaffoldController.Control.mode _ = _›]; intro hx; exfalso; cases hx; done)
  | (rw [‹GalilScaffoldController.Control.mode _ = _›]; rintro (hx | hx) <;> exfalso <;> cases hx; done))

section Tick
variable (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
  (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)

/-- What a comparison does to the fields the pack reads. -/
theorem compare_len {s s' : GalilVM}
    (hcmp : (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).compare s s') :
    s'.right = GalilScaffoldChainVerifier.right s.right ∧ s'.remaining = s.remaining ∧
      s'.fpp = s.fpp ∧
      (s'.length = s.length ∨ s'.length = inc (inc s.length)) ∧
      (¬ (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).matched s' →
        s'.length = s.length) := by
  obtain ⟨vs, vq, a, hvl, hvr, hiff, -, -, hteq⟩ :
    compareFound (sharedC onLetter leftFirst centre place entry) q first s s' := hcmp
  cases a with
  | true =>
    rw [if_pos rfl] at hteq
    subst hteq
    refine ⟨?_, ?_, ?_, Or.inr ?_, fun hn => absurd ?_ hn⟩
    · rw [afterBirth_right]; exact hvr
    · rw [afterBirth_remaining]; rfl
    · rw [afterBirth_fpp]; rfl
    · rw [afterBirth_length]; rfl
    · have h1 := hiff.1 rfl
      show GalilScaffoldInputHead.read (afterBirth _ (afterCompare s vs vq)).left
        = GalilScaffoldInputHead.read (afterBirth _ (afterCompare s vs vq)).right
      rw [afterBirth_left, afterBirth_right]
      exact h1
  | false =>
    rw [if_neg (by simp)] at hteq
    subst hteq
    refine ⟨?_, ?_, ?_, Or.inl ?_, fun _ => ?_⟩
    · rw [afterBirth_right]; exact hvr
    · rw [afterBirth_remaining]; rfl
    · rw [afterBirth_fpp]; rfl
    · rw [afterBirth_length]; rfl
    · rw [afterBirth_length]; rfl

theorem cpack_tick {c c' : Control} {s t : GalilVM} (hP : CPack q c s)
    (hfl : c.mode = Mode.scan → 0 ≤ value s.length)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : CPack q c' t := by
  have hF := frontPack_tick onLetter leftFirst centre place entry q first delay hP.front
    (centreLive_of_pack hP) h
  cases h
  case init =>
    rename_i hm hi
    exact absurd hm hP.front.notInit
  case scan_wait =>
    rename_i hm hav hb
    obtain ⟨-, hr, -, -, -, -, hlen, -, hrem, -, -, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    refine ⟨hF, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · intro _; rw [shiftIdle_iff, hrem, ← shiftIdle_iff]; exact hP.idle (by rw [hm]; decide)
    · rw [hlen]; exact hP.canon
    · intro _; rw [hlen, hr]; exact hP.span (Or.inl hm)
  case scan_count =>
    rename_i hm hc hav hb
    obtain ⟨-, hr, -, -, -, -, hlen, -, hrem, -, -, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    refine ⟨hF, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · intro _; rw [shiftIdle_iff, hrem, ← shiftIdle_iff]; exact hP.idle (by rw [hm]; decide)
    · rw [hlen]; exact hP.canon
    · intro _; rw [hlen, hr]; exact hP.span (Or.inl hm)
  case restart =>
    rename_i hm hb
    obtain ⟨w, -, -, -, -, ht⟩ : restartVM entry s t := hb
    subst ht
    refine ⟨hF, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · intro _; exact hP.idle (by rw [hm]; decide)
    · exact hP.canon
    · intro _; exact hP.span (Or.inl hm)
  case scan_match =>
    rename_i s' o hmt hm hc hcmp hav hpl ho
    obtain ⟨hs'r, hs'rem, -, hs'len, -⟩ :=
      compare_len onLetter leftFirst centre place entry q first hcmp
    have hpl' : t = (if c.replaying then
        {s' with replay := GalilScaffoldCounter.dec s'.replay} else s') := hpl
    have htr : t.right = s'.right := by rw [hpl']; cases c.replaying <;> rfl
    have htl : t.length = s'.length := by rw [hpl']; cases c.replaying <;> rfl
    have htm : t.remaining = s'.remaining := by rw [hpl']; cases c.replaying <;> rfl
    have hcan : GalilScaffoldChainVerifier.canRight s.right := by
      cases hcr : c.replaying with
      | false =>
        rcases hav with h | h
        · rw [hcr] at h; cases h
        · exact h
      | true =>
        obtain ⟨m, hm'⟩ := hP.front.replayPos hcr
        exact canRight_of_budget (hP.front.frontier (m+1) hm')
    obtain ⟨hpos, -⟩ := right_sane hcan hP.front.sane
    refine ⟨hF, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · intro _; rw [shiftIdle_iff, htm, hs'rem, ← shiftIdle_iff]
      exact hP.idle (by rw [hm]; decide)
    · rw [htl]
      rcases hs'len with h | h <;> rw [h]
      · exact hP.canon
      · exact inc_canonical _ (inc_canonical _ hP.canon)
    · intro _
      have hb := hP.span (Or.inl hm)
      rw [htl, htr, hs'r, hpos]
      rcases hs'len with h | h <;> rw [h]
      · push_cast; omega
      · rw [inc_value, inc_value]; push_cast; omega
  case scan_shift =>
    rename_i s' hmt hg hm hc hr hcmp hav hb
    obtain ⟨hs'r, hs'rem, -, -, hs'len⟩ :=
      compare_len onLetter leftFirst centre place entry q first hcmp
    have hl := hs'len hmt
    obtain ⟨w, -, ht⟩ : beginShiftVM' s' t := hb
    have hcan : GalilScaffoldChainVerifier.canRight s.right := by
      rcases hav with h | h
      · rw [hr] at h; cases h
      · exact h
    obtain ⟨hpos, -⟩ := right_sane hcan hP.front.sane
    subst ht
    refine ⟨hF, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · show Canonical (inc (inc s'.length))
      rw [hl]; exact inc_canonical _ (inc_canonical _ hP.canon)
    · intro _
      have hb := hP.span (Or.inl hm)
      show value (inc (inc s'.length)) ≤ 2 * (position s'.right : ℤ) + 1
      rw [hl, hs'r, hpos, inc_value, inc_value]; push_cast; omega
  case scan_fallback =>
    rename_i s' hmt hm hc hg hr hcmp hav hb
    obtain ⟨hs'r, hs'rem, -, -, hs'len⟩ :=
      compare_len onLetter leftFirst centre place entry q first hcmp
    have hl := hs'len hmt
    obtain ⟨pl, ht, -⟩ : beginFallbackVM' s' t := hb
    have hcan : GalilScaffoldChainVerifier.canRight s.right := by
      rcases hav with h | h
      · rw [hr] at h; cases h
      · exact h
    obtain ⟨hpos, -⟩ := right_sane hcan hP.front.sane
    have hb := hP.span (Or.inl hm)
    have h0 := hfl hm
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℕ, value s.length = ℓ := ⟨(value s.length).toNat, by omega⟩
    subst ht
    refine ⟨hF, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · intro _
      show ShiftIdle {s' with fpp := _, chain := _, search := _}
      rw [shiftIdle_iff]; show positive s'.remaining = false
      rw [hs'rem, ← shiftIdle_iff]; exact hP.idle (by rw [hm]; decide)
    · show Canonical s'.length
      rw [hl]; exact hP.canon
    · intro _
      have hc' : Canonical s'.length := by rw [hl]; exact hP.canon
      have hv' : value s'.length = ℓ := by rw [hl]; exact hℓ
      obtain ⟨t0, hrun, hmode, hprog, -⟩ :=
        FppControl.fallback_prepared s'.fpp.program pl s'.length hc' ℓ hv'
      refine ⟨(GalilScaffoldPlace.stream pl).take (ℓ+1), _, t0, ?_, rfl, hrun, hmode, hprog⟩
      show _ ≤ 2 * position s'.right
      rw [hs'r, hpos, List.length_take]
      rw [hℓ] at hb
      have : ℓ + 1 ≤ 2 * (position s.right + 1) := by omega
      omega
  case shift_one =>
    rename_i hm hp hi
    obtain ⟨-, -, -, w, -, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    subst ht
    refine ⟨hF, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · show Canonical (dec (dec s.length))
      exact dec_canonical _ (dec_canonical _ hP.canon)
    · intro _
      have hb := hP.span (Or.inr hm)
      show value (dec (dec s.length)) ≤ 2 * (position s.right : ℤ) + 1
      rw [dec_value, dec_value]; omega
  case shift_done =>
    rename_i o hm hp ho
    refine ⟨hF, ?_, hP.canon, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · intro _ h; exact hp (Or.inl h)
    · intro _; exact hP.span (Or.inr hm)
  case replayStart =>
    rename_i o hm ho ho' hi
    have hi' : replayStartVM entry s t := hi
    obtain ⟨-, -, -, -, -, hlen, hrem, -⟩ := hi'
    refine ⟨hF, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · intro _; rw [shiftIdle_iff, hrem, ← shiftIdle_iff]; exact hP.idle (by rw [hm]; decide)
    · rw [hlen]; exact ofNat_canonical 1
    · intro _; rw [hlen, ofNat_value]; push_cast; omega
  case copy_one =>
    rename_i hm hp hi
    obtain ⟨a, ha, hv⟩ : ∃ a : Fin 3, GalilScaffoldPlace.read s.fpp.walker = some a ∧
        t.fpp = {s.fpp with program := FppControl.tape s.fpp 7 (fun t => GalilScaffoldTape.moveRight (GalilScaffoldTape.write t (GalilFppPreparation.symbol a))), work := GalilScaffoldCounter.dec s.fpp.work, walker := GalilScaffoldPlace.left s.fpp.walker} := hi.1
    have ht : t = {s with fpp := t.fpp} := hi.2
    have hidle := hP.idle (by rw [hm]; decide)
    have hB : ¬ (GalilScaffoldPlace.read s.fpp.walker = none ∨ zero s.fpp.work = true) :=
      hp.resolve_left hidle
    obtain ⟨w, k, t0, hb, hmode, hrun, h0, hprog⟩ := hP.copy (Or.inl hm)
    have hw : zero s.fpp.work = false := by
      cases hz : zero s.fpp.work
      · rfl
      · exact absurd (Or.inr hz) hB
    have hft : FppControl.Tick true s.fpp t.fpp := by
      rw [hv]; exact .copyBit s.fpp a (toController_copy (hmode.trans hm)) ha hw
    obtain ⟨k', hrun'⟩ := future_step hrun h0 hft
    rw [ht]
    refine ⟨?_, ?_, hP.canon, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · rw [← ht]; exact hF
    · intro _; exact hidle
    · intro _
      refine ⟨w, k', t0, hb, ?_, hrun', h0, hprog⟩
      show t.fpp.mode.toController = c.mode
      rw [hv]; exact hmode
  case copy_done =>
    rename_i hm hp hi
    have hv : t.fpp = {s.fpp with program := FppControl.tape s.fpp 7 (fun t => GalilScaffoldTape.write t 5), mode := .home, finalStage := (GalilScaffoldPlace.read s.fpp.walker).isNone} := hi.1
    have ht : t = {s with fpp := t.fpp} := hi.2
    have hidle := hP.idle (by rw [hm]; decide)
    obtain ⟨w, k, t0, hb, hmode, hrun, h0, hprog⟩ := hP.copy (Or.inl hm)
    have he : GalilScaffoldPlace.read s.fpp.walker = none ∨ zero s.fpp.work = true :=
      Classical.byContradiction (fun hn => hp (Or.inr hn))
    have hft : FppControl.Tick true s.fpp t.fpp := by
      rw [hv]; exact .copyEnd s.fpp (toController_copy (hmode.trans hm)) he
    obtain ⟨k', hrun'⟩ := future_step hrun h0 hft
    rw [ht]
    refine ⟨?_, ?_, hP.canon, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · rw [← ht]; exact hF
    · intro _; exact hidle
    · intro _
      refine ⟨w, k', t0, hb, ?_, hrun', h0, hprog⟩
      show t.fpp.mode.toController = Mode.home
      rw [hv]; rfl
  case home_step =>
    rename_i hm hl hi
    obtain ⟨hleft, hv⟩ : (s.fpp.program.config.tapes 7).left ≠ [] ∧
        t.fpp = {s.fpp with program := FppControl.tape s.fpp 7 GalilScaffoldTape.moveLeft} := hi.1
    have ht : t = {s with fpp := t.fpp} := hi.2
    have hidle := hP.idle (by rw [hm]; decide)
    obtain ⟨w, k, t0, hb, hmode, hrun, h0, hprog⟩ := hP.copy (Or.inr hm)
    have hft : FppControl.Tick true s.fpp t.fpp := by
      rw [hv]; exact .sourceLeft s.fpp (toController_home (hmode.trans hm)) hl hleft
    obtain ⟨k', hrun'⟩ := future_step hrun h0 hft
    rw [ht]
    refine ⟨?_, ?_, hP.canon, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · rw [← ht]; exact hF
    · intro _; exact hidle
    · intro _
      refine ⟨w, k', t0, hb, ?_, hrun', h0, hprog⟩
      show t.fpp.mode.toController = c.mode
      rw [hv]; exact hmode
  case home_start =>
    rename_i hm hl hi
    have hv : t.fpp = {s.fpp with program := GalilScaffoldControl.start 320 s.fpp.program, mode := .run} := hi.1
    have ht : t = {s with fpp := t.fpp} := hi.2
    have hidle := hP.idle (by rw [hm]; decide)
    obtain ⟨w, k, t0, hb, hmode, hrun, h0, hprog⟩ := hP.copy (Or.inr hm)
    have hft : FppControl.Tick true s.fpp t.fpp := by
      rw [hv]; exact .startRun s.fpp (toController_home (hmode.trans hm)) hl
    obtain ⟨k', hrun'⟩ := future_step hrun h0 hft
    have heq : t.fpp = t0 := future_run hrun' (by rw [hv])
    rw [ht]
    refine ⟨?_, ?_, hP.canon, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · rw [← ht]; exact hF
    · intro _; exact hidle
    · intro _
      refine ⟨w, 0, hb, ?_⟩
      show GalilScaffoldControl.Run _ _ _ t.fpp.program
      rw [Nat.zero_mul, List.replicate_zero, heq, hprog]
      exact .nil _
  case fpp_slice =>
    rename_i hm hi
    obtain ⟨-, hq, -, -⟩ : s.fpp.mode = .run ∧
        GalilScaffoldControl.Run GalilFppMarkedCode.code s.fpp.program (List.replicate q true) t.fpp.program ∧
        t.fpp.program.done = false ∧ t.fpp = {s.fpp with program := t.fpp.program} := hi.1
    have ht : t = {s with fpp := t.fpp} := hi.2
    have hidle := hP.idle (by rw [hm]; decide)
    obtain ⟨w, n, hb, hrun⟩ := hP.fpp hm
    have hrun2 : GalilScaffoldControl.Run GalilFppMarkedCode.code ⟨fppInitial w, false⟩
        (List.replicate ((n+1)*q) true) t.fpp.program := by
      rw [Nat.succ_mul, List.replicate_add]; exact GalilScaffoldControl.run_append hrun hq
    rw [ht]
    refine ⟨?_, ?_, hP.canon, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · rw [← ht]; exact hF
    · intro _; exact hidle
    · intro _; exact ⟨w, n+1, hb, hrun2⟩
  case fpp_done =>
    rename_i hm hi
    obtain ⟨-, p, hq, hd, hv⟩ : s.fpp.mode = .run ∧ ∃ p : GalilScaffoldControl.Machine 9,
        GalilScaffoldControl.Run GalilFppMarkedCode.code s.fpp.program (List.replicate q true) p ∧
        p.done = true ∧ t.fpp = {s.fpp with program := markNew p first} := hi.1
    have ht : t = {s with fpp := t.fpp} := hi.2
    have hidle := hP.idle (by rw [hm]; decide)
    obtain ⟨w, n, hb, hrun⟩ := hP.fpp hm
    have hrun2 : GalilScaffoldControl.Run GalilFppMarkedCode.code ⟨fppInitial w, false⟩
        (List.replicate ((n+1)*q) true) p := by
      rw [Nat.succ_mul, List.replicate_add]; exact GalilScaffoldControl.run_append hrun hq
    obtain ⟨v, -, hpos, -, h8, hsched⟩ := fpp_scheduled w
    have hpv : p = ⟨v, true⟩ :=
      fpp_outcome_program q w {s.fpp with program := ⟨fppInitial w, false⟩} rfl v hsched n p hd hrun2
    obtain ⟨hden, hhead⟩ := marks_after_fpp first w v hpos h8
    have hmt : marksTape t.fpp = (markNew ⟨v, true⟩ first).config.tapes 8 := by
      rw [hv, ← hpv]; rfl
    rw [ht]
    refine ⟨?_, ?_, hP.canon, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · rw [← ht]; exact hF
    · intro _; exact hidle
    · intro _ e he h5
      have hmt' : marksTape ({s with fpp := t.fpp} : GalilVM).fpp =
          (markNew ⟨v, true⟩ first).config.tapes 8 := hmt
      have hh : mh ({s with fpp := t.fpp} : GalilVM) = 2 := by
        unfold mh; rw [hmt', hhead]
      rw [hh] at he
      rw [hmt', hden] at h5
      exact layout_end first w (2 * position s.right) hb e he h5
  case markEnd_step =>
    rename_i hm he hi
    have hv : t.fpp = markStep s.fpp GalilScaffoldTape.moveRight := hi.1
    have ht : t = {s with fpp := t.fpp} := hi.2
    have hidle := hP.idle (by rw [hm]; decide)
    have hmt : marksTape t.fpp = GalilScaffoldTape.moveRight (marksTape s.fpp) := by
      rw [hv, markStep_tape]
    have hfocus : (marksTape s.fpp).focus ≠ 5 := he
    rw [ht]
    refine ⟨?_, ?_, hP.canon, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · rw [← ht]; exact hF
    · intro _; exact hidle
    · intro _ e he' h5
      have hmt' : marksTape ({s with fpp := t.fpp} : GalilVM).fpp =
          GalilScaffoldTape.moveRight (marksTape s.fpp) := hmt
      have hh : mh ({s with fpp := t.fpp} : GalilVM) = mh s + 1 := by
        unfold mh; rw [hmt', GalilScaffoldTape.right_head]
      rw [hmt', GalilScaffoldTape.right_denote] at h5
      rw [hh] at he'
      exact hP.markEnd hm e (by omega) h5
  case markEnd_found =>
    rename_i hm he hi
    obtain ⟨hleft, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    subst ht
    have hidle := hP.idle (by rw [hm]; decide)
    have hpos : 0 < GalilScaffoldTape.head (marksTape s.fpp) :=
      (GalilScaffoldTape.left_legal _).1 hleft
    have hfocus : (marksTape s.fpp).focus = 5 := he
    have hle := hP.markEnd hm (mh s) le_rfl (by unfold mh; rw [GalilScaffoldTape.focus_eq]; exact hfocus)
    refine ⟨hF, ?_, hP.canon, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · intro _; exact hidle
    · intro _
      show GalilScaffoldTape.head (marksTape (markStep s.fpp GalilScaffoldTape.moveLeft)) ≤
        2 * position s.right
      rw [markStep_tape, GalilScaffoldTape.left_head _ hpos]
      unfold mh at hle; omega
  case choose_step =>
    rename_i hm hs hi
    obtain ⟨hleft, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    subst ht
    have hidle := hP.idle (by rw [hm]; decide)
    have hpos : 0 < GalilScaffoldTape.head (marksTape s.fpp) :=
      (GalilScaffoldTape.left_legal _).1 hleft
    have hle := hP.choose hm
    refine ⟨hF, ?_, hP.canon, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · intro _; exact hidle
    · intro _
      show GalilScaffoldTape.head (marksTape (markStep s.fpp GalilScaffoldTape.moveLeft)) ≤
        2 * position s.right
      rw [markStep_tape, GalilScaffoldTape.left_head _ hpos]
      unfold mh at hle; omega
  case choose_select =>
    rename_i hm hodd hs hi
    have ht := hi.2
    rw [hi.1] at ht
    subst ht
    have hidle := hP.idle (by rw [hm]; decide)
    have hle := hP.choose hm
    refine ⟨hF, ?_, ofNat_canonical 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · intro _; exact hidle
    · intro _
      show mh s + 0 ≤ 2 * position s.right
      omega
  case rewind_done =>
    rename_i hm hfi hi
    have ht := hi.2
    rw [hi.1] at ht
    subst ht
    have hidle := hP.idle (by rw [hm]; decide)
    refine ⟨hF, ?_, hP.canon, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try vac
    intro _; exact hidle
  case rewind_one =>
    rename_i hm hpr hfi hi
    obtain ⟨hleft, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    subst ht
    have hidle := hP.idle (by rw [hm]; decide)
    have hpos : 0 < GalilScaffoldTape.head (marksTape s.fpp) :=
      (GalilScaffoldTape.left_legal _).1 hleft
    have hle := hP.rewind hm
    rw [hpr] at hle
    simp only [Bool.false_eq_true, if_false] at hle
    refine ⟨hF, ?_, inc_canonical _ hP.canon, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · intro _; exact hidle
    · intro _
      show GalilScaffoldTape.head (marksTape (markStep s.fpp GalilScaffoldTape.moveLeft)) + 1 ≤
        2 * position s.center
      rw [markStep_tape, GalilScaffoldTape.left_head _ hpos]
      unfold mh at hle; omega
  case rewind_pair =>
    rename_i hm hpr hfi hi
    obtain ⟨hleft, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    subst ht
    have hidle := hP.idle (by rw [hm]; decide)
    have hpos : 0 < GalilScaffoldTape.head (marksTape s.fpp) :=
      (GalilScaffoldTape.left_legal _).1 hleft
    have hle := hP.rewind hm
    rw [hpr] at hle
    simp only [if_true] at hle
    have hc : 0 < position s.center := by omega
    have hstep := left_position_pos hc
    refine ⟨hF, ?_, inc_canonical _ hP.canon, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · intro _; exact hidle
    · intro _
      show GalilScaffoldTape.head (marksTape (markStep s.fpp GalilScaffoldTape.moveLeft)) + 0 ≤
        2 * position (GalilScaffoldInputHead.left s.center)
      rw [markStep_tape, GalilScaffoldTape.left_head _ hpos]
      unfold mh at hle; omega

/-! ## Along a run -/

/-- The pack travels along any run whose `scan` states have a non-negative
length counter. -/
theorem cpack_steps {n : ℕ} {x y : State GalilVM}
    (h : Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay n x y)
    (hfl : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay m x z →
      z.ctl.mode = Mode.scan → 0 ≤ value z.vm.length)
    (hP : CPack q x.ctl x.vm) : CPack q y.ctl y.vm := by
  induction h with
  | zero x => exact hP
  | @succ n x w y ht _ ih =>
    refine ih (fun m z hz => hfl (m+1) z (.succ ht hz)) ?_
    exact cpack_tick onLetter leftFirst centre place entry q first delay hP
      (hfl 0 x (.zero x)) ht

end Tick

/-! ## Establishment and the deliverables -/

open PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal PalPeg.GalilGlueBLeaves
  PalPeg.GalilRunSkeleton

/-- At a recursion state of the widened oracle, given the two length facts
`InvS` does not carry. -/
theorem cpack_of_invS {raw : List (Fin 2)} {c : Control} {r : GalilVM} (q : ℕ)
    (hI : InvS raw c r) (hcan : Canonical r.length)
    (hspan : value r.length ≤ 2 * (position r.right : ℤ) + 1) : CPack q c r := by
  obtain ⟨hm, -⟩ := invS_mode hI
  have hidle : ShiftIdle r := by
    rcases hI with h | ⟨k, h⟩
    · exact h.shiftIdle
    · exact h.shiftIdle
  refine ⟨frontPack_of_invS hI, fun _ => hidle, hcan, fun _ => hspan, ?_, ?_, ?_, ?_, ?_⟩
  all_goals vac

/-- `EntryCounters` pays for both length facts. -/
theorem cpack_of_entry {raw : List (Fin 2)} {c : Control} {r : GalilVM} (q : ℕ)
    (hI : InvS raw c r) (hE : EntryCounters raw r) : CPack q c r := by
  obtain ⟨Rad, hi, hRR, hS, hcan⟩ := hE
  refine cpack_of_invS q hI hcan ?_
  have h1 : position r.right = position r.center + Rad := hi.rightPos
  have h2 : value r.radius = Rad := hRR.2
  have h3 : value r.length = 2 * value r.radius + 1 := hS
  rw [h3, h2, h1]; push_cast; omega

/-- **`centreLive_of_invS_run`.**  From an `InvS` state whose length counter is
canonical and spans at most `2·position right + 1`, every state of every run
is `CentreLive`, provided the length counter is non-negative at the run's
`scan` states (`hfloor`). -/
theorem centreLive_of_invS_run (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)
    {raw : List (Fin 2)} {c : Control} {r : GalilVM}
    (hI : InvS raw c r) (hcan : Canonical r.length)
    (hspan : value r.length ≤ 2 * (position r.right : ℤ) + 1)
    (hfloor : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay m ⟨c, r⟩ z →
      z.ctl.mode = Mode.scan → 0 ≤ value z.vm.length) :
    ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay m ⟨c, r⟩ z →
      CentreLive z.ctl z.vm := by
  intro m z hz
  exact centreLive_of_pack (cpack_steps onLetter leftFirst centre place entry q first delay hz
    hfloor (cpack_of_invS q hI hcan hspan))

/-- **`centreLive_of_invLP_run`.**  The same from `InvL ∧ EntryCounters`
(`GalilInvPlus.InvLP`), which supplies the two length facts. -/
theorem centreLive_of_invLP_run (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    {raw : List (Fin 2)} {c : Control} {r : GalilVM}
    (hIP : InvL raw c r ∧ EntryCounters raw r)
    (hfloor : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry raw) q first) 2048 m ⟨c, r⟩ z →
      z.ctl.mode = Mode.scan → 0 ≤ value z.vm.length) :
    ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry raw) q first) 2048 m ⟨c, r⟩ z →
      CentreLive z.ctl z.vm := by
  intro m z hz
  exact centreLive_of_pack (cpack_steps (onLetterVM raw) leftFirstVM centre place entry q first 2048
    hz hfloor (cpack_of_entry q hIP.1.1 hIP.2))

/-- The `hlive` hypothesis of `GalilInvPlus.segment_of_invLP`, from the floor. -/
theorem hlive_of_floor (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hfloor : ∀ (c : Control) (r : GalilVM), InvL raw c r ∧ EntryCounters raw r →
      ∀ (m : ℕ) (z : State GalilVM),
        Steps (galilFrameS (PofC centre place entry raw) q first) 2048 m ⟨c, r⟩ z →
        z.ctl.mode = Mode.scan → 0 ≤ value z.vm.length) :
    ∀ (c : Control) (r : GalilVM), InvL raw c r ∧ EntryCounters raw r →
      ∀ (m : ℕ) (z : State GalilVM),
        Steps (galilFrameS (PofC centre place entry raw) q first) 2048 m ⟨c, r⟩ z →
        CentreLive z.ctl z.vm :=
  fun c r hIP => centreLive_of_invLP_run centre place entry q first hIP (hfloor c r hIP)

#print axioms ftick_not_run

#print axioms ftick_unique
#print axioms future_step
#print axioms future_run
#print axioms layout_end

#print axioms centreLive_of_pack
#print axioms compare_len
#print axioms cpack_tick
#print axioms cpack_steps
#print axioms cpack_of_invS
#print axioms cpack_of_entry
#print axioms centreLive_of_invS_run
#print axioms centreLive_of_invLP_run
#print axioms hlive_of_floor

end PalPeg.GalilCentreLive
