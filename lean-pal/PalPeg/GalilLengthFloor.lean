import PalPeg.GalilCentreLive
import PalPeg.GalilSpanCounter
import PalPeg.GalilCatchUpDistance

/-!
# The length floor `hfloor` of `centreLive_of_invLP_run`

`GalilCentreLive.centreLive_of_invLP_run` takes `hfloor`: at every `scan` state
of a run from an `InvLP` state, `0 ≤ value length`.  This module discharges it
by carrying `FPack` along the run:

* `span`: in `scan`/`shift`, `SpanRep` (`length = 2·radius + 1`);
* `radius`: in `scan`/`shift`, `0 ≤ value radius`;
* `budget`: in `shift`, `remaining` is canonical and `remaining ≤ radius`;
* `copy`: outside `copy`, `CopyIdle` (so a `shift_one` tick is enabled by the
  shift counter, not by the copy reading of `remainingPos`).

The geometry is kept on the counters rather than on head positions: a
comparison adds `1` to the radius and `0`/`2` to the length; a shift unit takes
`1`/`2`; `replayStart` resets to `0`/`1`.  The floor is then `SpanRep` plus
`0 ≤ radius`.

**Named hypotheses.**

* `hbudget`: at a `scan_shift` tick of the run, the semiperiod `periodLength w`
  of the guarded watch is at most the compared radius (Galil's `h ≤ Rad`).
  This is chain-level (watch history), not tick-local.  For the fresh watch
  (`periodOnly = false`) `budget_of_guard` reduces it, through
  `GalilCatchUpDistance.places_of_guard`, to the identification of the chain's
  `distance` with (at most) the VM radius; the `periodOnly = true` round is
  not treated here.
* `hcopy`: `CopyIdle` at the entry state.  `InvL`/`EntryCounters` do not carry
  the FPP copy walker; without it `shift_one` could fire on the copy reading
  of `remainingPos` with an exhausted shift counter.
-/

set_option autoImplicit false
namespace PalPeg.GalilLengthFloor
open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainInputSupply PalPeg.GalilFrontMono PalPeg.GalilCentreLive

/-- The pack carried along a run for the length floor. -/
structure FPack (c : Control) (s : GalilVM) : Prop where
  notInit : c.mode ≠ Mode.init
  copy : c.mode ≠ Mode.copy → CopyIdle s
  span : c.mode = Mode.scan ∨ c.mode = Mode.shift → SpanRep s
  radius : c.mode = Mode.scan ∨ c.mode = Mode.shift → 0 ≤ value s.radius
  budget : c.mode = Mode.shift → Canonical s.remaining ∧ value s.remaining ≤ value s.radius

/-- **The floor is read off the pack.** -/
theorem floor_of_fpack {c : Control} {s : GalilVM} (h : FPack c s) (hm : c.mode = Mode.scan) :
    0 ≤ value s.length := by
  have h1 := h.span (Or.inl hm)
  have h2 := h.radius (Or.inl hm)
  unfold SpanRep at h1
  omega

section Tick
variable (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
  (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)

/-- What a comparison does to the counters the floor pack reads. -/
theorem compare_counters {s s' : GalilVM}
    (hcmp : (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).compare s s') :
    s'.fpp = s.fpp ∧ s'.remaining = s.remaining ∧ s'.radius = inc s.radius ∧
      ((galilFrameS (sharedC onLetter leftFirst centre place entry) q first).matched s' →
        s'.length = inc (inc s.length)) ∧
      (¬ (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).matched s' →
        s'.length = s.length) := by
  obtain ⟨vs, vq, a, -, -, hiff, -, -, hteq⟩ :
    compareFound (sharedC onLetter leftFirst centre place entry) q first s s' := hcmp
  cases a with
  | true =>
    rw [if_pos rfl] at hteq
    subst hteq
    refine ⟨?_, ?_, ?_, fun _ => ?_, fun hn => absurd ?_ hn⟩
    · rw [afterBirth_fpp]; rfl
    · rw [afterBirth_remaining]; rfl
    · rw [afterBirth_radius]; rfl
    · rw [afterBirth_length]; rfl
    · show GalilScaffoldInputHead.read (afterBirth _ (afterCompare s vs vq)).left
        = GalilScaffoldInputHead.read (afterBirth _ (afterCompare s vs vq)).right
      rw [afterBirth_left, afterBirth_right]
      exact hiff.1 rfl
  | false =>
    rw [if_neg (by simp)] at hteq
    subst hteq
    refine ⟨?_, ?_, ?_, fun hm => absurd (hiff.2 ?_) (by simp), fun _ => ?_⟩
    · rw [afterBirth_fpp]; rfl
    · rw [afterBirth_remaining]; rfl
    · rw [afterBirth_radius]; rfl
    · show GalilScaffoldInputHead.read (afterMismatch s vs vq).left
        = GalilScaffoldInputHead.read (afterMismatch s vs vq).right
      have h0 : GalilScaffoldInputHead.read (afterBirth _ (afterMismatch s vs vq)).left
        = GalilScaffoldInputHead.read (afterBirth _ (afterMismatch s vs vq)).right := hm
      rw [afterBirth_left, afterBirth_right] at h0
      exact h0
    · rw [afterBirth_length]; rfl

/-- The budget hypothesis at one state: every guarded shift entry out of a
comparison has its semiperiod within the compared radius. -/
def BudgetAt (c : Control) (s : GalilVM) : Prop :=
  c.mode = Mode.scan → c.replaying = false →
    ∀ (s' : GalilVM) (w : GalilScaffoldChainWatch.State),
      (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).compare s s' →
      ¬ (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).matched s' →
      shiftGuardVM s' → s'.chain = .watch w →
      (periodLength w : ℤ) ≤ value s'.radius

theorem fpack_tick {c c' : Control} {s t : GalilVM} (hP : FPack c s)
    (hbud : BudgetAt onLetter leftFirst centre place entry q first c s)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : FPack c' t := by
  cases h
  case init =>
    rename_i hm hi
    exact absurd hm hP.notInit
  case scan_wait =>
    rename_i hm hav hb
    obtain ⟨-, -, -, -, -, hrad, hlen, -, -, -, hfpp, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    refine ⟨hP.notInit, ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · intro _; rw [copyIdle_iff, hfpp, ← copyIdle_iff]; exact hP.copy (by rw [hm]; decide)
    · intro _; unfold SpanRep; rw [hlen, hrad]; exact hP.span (Or.inl hm)
    · intro _; rw [hrad]; exact hP.radius (Or.inl hm)
  case scan_count =>
    rename_i hm hc hav hb
    obtain ⟨-, -, -, -, -, hrad, hlen, -, -, -, hfpp, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    refine ⟨hP.notInit, ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · intro _; rw [copyIdle_iff, hfpp, ← copyIdle_iff]; exact hP.copy (by rw [hm]; decide)
    · intro _; unfold SpanRep; rw [hlen, hrad]; exact hP.span (Or.inl hm)
    · intro _; rw [hrad]; exact hP.radius (Or.inl hm)
  case restart =>
    rename_i hm hb
    obtain ⟨w, -, -, -, -, ht⟩ : restartVM entry s t := hb
    subst ht
    refine ⟨hP.notInit, ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · intro _; exact hP.copy (by rw [hm]; decide)
    · intro _; exact hP.span (Or.inl hm)
    · intro _; exact hP.radius (Or.inl hm)
  case scan_match =>
    rename_i s' o hmt hm hc hcmp hav hpl ho
    obtain ⟨hf, -, hrad, hlm, -⟩ :=
      compare_counters onLetter leftFirst centre place entry q first hcmp
    have hl := hlm hmt
    have hpl' : t = (if c.replaying then
        {s' with replay := GalilScaffoldCounter.dec s'.replay} else s') := hpl
    have htl : t.length = s'.length := by rw [hpl']; cases c.replaying <;> rfl
    have htr : t.radius = s'.radius := by rw [hpl']; cases c.replaying <;> rfl
    have htf : t.fpp = s'.fpp := by rw [hpl']; cases c.replaying <;> rfl
    refine ⟨hP.notInit, ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · intro _; rw [copyIdle_iff, htf, hf, ← copyIdle_iff]; exact hP.copy (by rw [hm]; decide)
    · intro _
      have hs := hP.span (Or.inl hm)
      unfold SpanRep at hs ⊢
      rw [htl, htr, hl, hrad, inc_value, inc_value, inc_value]; omega
    · intro _
      have hr0 := hP.radius (Or.inl hm)
      rw [htr, hrad, inc_value]; omega
  case scan_shift =>
    rename_i s' hmt hg hm hc hr hcmp hav hb
    obtain ⟨hf, -, hrad, -, hlm⟩ :=
      compare_counters onLetter leftFirst centre place entry q first hcmp
    have hl := hlm hmt
    obtain ⟨w, hw, ht⟩ : beginShiftVM' s' t := hb
    have hbw := hbud hm hr s' w hcmp hmt hg hw
    subst ht
    refine ⟨(by intro hx; cases hx), ?_, ?_, ?_, ?_⟩
    · intro _
      rw [copyIdle_iff]
      show GalilScaffoldPlace.read s'.fpp.walker = none ∨ GalilScaffoldCounter.zero s'.fpp.work = true
      rw [hf, ← copyIdle_iff]; exact hP.copy (by rw [hm]; decide)
    · intro _
      have hs := hP.span (Or.inl hm)
      unfold SpanRep at hs
      show value (inc (inc s'.length)) = 2 * value s'.radius + 1
      rw [hl, hrad, inc_value, inc_value, inc_value]; omega
    · intro _
      have hr0 := hP.radius (Or.inl hm)
      show 0 ≤ value s'.radius
      rw [hrad, inc_value]; omega
    · intro _
      refine ⟨ofNat_canonical _, ?_⟩
      show value (ofNat (periodLength w)) ≤ value s'.radius
      rw [ofNat_value]; exact hbw
  case scan_fallback =>
    refine ⟨(by intro hx; cases hx), ?_, ?_, ?_, ?_⟩
    all_goals vac
  case shift_one =>
    rename_i hm hp hi
    obtain ⟨-, -, -, w, -, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    subst ht
    have hpos : GalilScaffoldCounter.positive s.remaining = true := by
      rcases hp with h | h
      · exact h
      · exact absurd h (hP.copy (by rw [hm]; decide))
    obtain ⟨hcan, hle⟩ := hP.budget hm
    have hv1 := (positive_iff _ hcan).1 hpos
    have hr0 := hP.radius (Or.inr hm)
    have hs := hP.span (Or.inr hm)
    unfold SpanRep at hs
    refine ⟨hP.notInit, ?_, ?_, ?_, ?_⟩
    · intro _; exact hP.copy (by rw [hm]; decide)
    · intro _
      show value (dec (dec s.length)) = 2 * value (dec s.radius) + 1
      rw [dec_value, dec_value, dec_value]; omega
    · intro _
      show 0 ≤ value (dec s.radius)
      rw [dec_value]; omega
    · intro _
      refine ⟨dec_canonical _ hcan, ?_⟩
      show value (dec s.remaining) ≤ value (dec s.radius)
      rw [dec_value, dec_value]; omega
  case shift_done =>
    rename_i o hm hp ho
    refine ⟨(by intro hx; cases hx), ?_, ?_, ?_, ?_⟩
    · intro _; exact hP.copy (by rw [hm]; decide)
    · intro _; exact hP.span (Or.inr hm)
    · intro _; exact hP.radius (Or.inr hm)
    · intro hx; cases hx
  case replayStart =>
    rename_i o hm ho ho' hi
    have hi' : replayStartVM entry s t := hi
    obtain ⟨-, -, -, -, hrad, hlen, -, -, hfpp, -⟩ := hi'
    refine ⟨(by intro hx; cases hx), ?_, ?_, ?_, ?_⟩
    · intro _; rw [copyIdle_iff, hfpp, ← copyIdle_iff]; exact hP.copy (by rw [hm]; decide)
    · intro _; unfold SpanRep; rw [hrad, hlen, ofNat_value]; simp [value, reset]
    · intro _; rw [hrad]; simp [value, reset]
    · intro hx; cases hx
  case copy_one =>
    rename_i hm hp hi
    refine ⟨hP.notInit, ?_, ?_, ?_, ?_⟩
    all_goals vac
  case copy_done =>
    rename_i hm hp hi
    have hv : t.fpp = {s.fpp with program := FppControl.tape s.fpp 7 (fun t => GalilScaffoldTape.write t 5), mode := .home, finalStage := (GalilScaffoldPlace.read s.fpp.walker).isNone} := hi.1
    have he : GalilScaffoldPlace.read s.fpp.walker = none ∨ zero s.fpp.work = true :=
      Classical.byContradiction (fun hn => hp (Or.inr hn))
    refine ⟨(by intro hx; cases hx), ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · intro _; rw [copyIdle_iff, hv]; exact he
  case home_step =>
    rename_i hm hl hi
    obtain ⟨-, hv⟩ : (s.fpp.program.config.tapes 7).left ≠ [] ∧
        t.fpp = {s.fpp with program := FppControl.tape s.fpp 7 GalilScaffoldTape.moveLeft} := hi.1
    refine ⟨hP.notInit, ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · intro _; rw [copyIdle_iff, hv]
      exact (copyIdle_iff s).1 (hP.copy (by rw [hm]; decide))
  case home_start =>
    rename_i hm hl hi
    have hv : t.fpp = {s.fpp with program := GalilScaffoldControl.start 320 s.fpp.program, mode := .run} := hi.1
    refine ⟨(by intro hx; cases hx), ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · intro _; rw [copyIdle_iff, hv]
      exact (copyIdle_iff s).1 (hP.copy (by rw [hm]; decide))
  case fpp_slice =>
    rename_i hm hi
    obtain ⟨-, -, -, hv⟩ : s.fpp.mode = .run ∧
        GalilScaffoldControl.Run GalilFppMarkedCode.code s.fpp.program (List.replicate q true) t.fpp.program ∧
        t.fpp.program.done = false ∧ t.fpp = {s.fpp with program := t.fpp.program} := hi.1
    refine ⟨hP.notInit, ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · intro _; rw [copyIdle_iff, hv]
      exact (copyIdle_iff s).1 (hP.copy (by rw [hm]; decide))
  case fpp_done =>
    rename_i hm hi
    obtain ⟨-, p, -, -, hv⟩ : s.fpp.mode = .run ∧ ∃ p : GalilScaffoldControl.Machine 9,
        GalilScaffoldControl.Run GalilFppMarkedCode.code s.fpp.program (List.replicate q true) p ∧
        p.done = true ∧ t.fpp = {s.fpp with program := markNew p first} := hi.1
    refine ⟨(by intro hx; cases hx), ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · intro _; rw [copyIdle_iff, hv]
      exact (copyIdle_iff s).1 (hP.copy (by rw [hm]; decide))
  case markEnd_step =>
    rename_i hm he hi
    have hv : t.fpp = markStep s.fpp GalilScaffoldTape.moveRight := hi.1
    refine ⟨hP.notInit, ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · intro _; rw [copyIdle_iff, hv]
      exact (copyIdle_iff s).1 (hP.copy (by rw [hm]; decide))
  case markEnd_found =>
    rename_i hm he hi
    obtain ⟨-, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    subst ht
    refine ⟨(by intro hx; cases hx), ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · intro _; exact hP.copy (by rw [hm]; decide)
  case choose_step =>
    rename_i hm hs hi
    obtain ⟨-, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    subst ht
    refine ⟨(by rw [hm]; decide), ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · intro _; exact hP.copy (by rw [hm]; decide)
  case choose_select =>
    rename_i hm hodd hs hi
    have ht := hi.2
    rw [hi.1] at ht
    subst ht
    refine ⟨(by intro hx; cases hx), ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · intro _; exact hP.copy (by rw [hm]; decide)
  case rewind_done =>
    rename_i hm hfi hi
    have ht := hi.2
    rw [hi.1] at ht
    subst ht
    refine ⟨(by intro hx; cases hx), ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · intro _; exact hP.copy (by rw [hm]; decide)
  case rewind_one =>
    rename_i hm hpr hfi hi
    obtain ⟨-, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    subst ht
    refine ⟨(by rw [hm]; decide), ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · intro _; exact hP.copy (by rw [hm]; decide)
  case rewind_pair =>
    rename_i hm hpr hfi hi
    obtain ⟨-, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    subst ht
    refine ⟨(by rw [hm]; decide), ?_, ?_, ?_, ?_⟩
    all_goals try vac
    · intro _; exact hP.copy (by rw [hm]; decide)

/-- The floor pack travels along any run whose scan states satisfy the budget. -/
theorem fpack_steps {n : ℕ} {x y : State GalilVM}
    (h : Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay n x y)
    (hbud : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay m x z →
      BudgetAt onLetter leftFirst centre place entry q first z.ctl z.vm)
    (hP : FPack x.ctl x.vm) : FPack y.ctl y.vm := by
  induction h with
  | zero x => exact hP
  | @succ n x w y ht _ ih =>
    refine ih (fun m z hz => hbud (m+1) z (.succ ht hz)) ?_
    exact fpack_tick onLetter leftFirst centre place entry q first delay hP
      (hbud 0 x (.zero x)) ht

end Tick

open PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal PalPeg.GalilGlueBLeaves
  PalPeg.GalilRunSkeleton

/-- The floor pack at an `InvLP` state whose FPP copy walker is idle. -/
theorem fpack_of_entry {raw : List (Fin 2)} {c : Control} {r : GalilVM}
    (hIP : InvL raw c r ∧ EntryCounters raw r) (hcopy : CopyIdle r) : FPack c r := by
  obtain ⟨hm, -⟩ := invS_mode hIP.1.1
  obtain ⟨Rad, -, hRR, hS, -⟩ := hIP.2
  refine ⟨(by rw [hm]; decide), fun _ => hcopy, fun _ => hS, fun _ => ?_, ?_⟩
  · rw [hRR.2]; exact Int.natCast_nonneg Rad
  · rw [hm]; intro hx; cases hx

/-- **`hfloor_of_invLP`.**  The `hfloor` hypothesis of
`GalilCentreLive.centreLive_of_invLP_run`, from `InvLP`, `CopyIdle` at the entry,
and the shift budget `hbudget` (Galil's `h ≤ Rad`) at the run's shift entries. -/
theorem hfloor_of_invLP (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    {raw : List (Fin 2)} {c : Control} {r : GalilVM}
    (hIP : InvL raw c r ∧ EntryCounters raw r) (hcopy : CopyIdle r)
    (hbudget : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry raw) q first) 2048 m ⟨c, r⟩ z →
      BudgetAt (onLetterVM raw) leftFirstVM centre place entry q first z.ctl z.vm) :
    ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry raw) q first) 2048 m ⟨c, r⟩ z →
      z.ctl.mode = Mode.scan → 0 ≤ value z.vm.length := by
  intro m z hz hm
  exact floor_of_fpack (fpack_steps (onLetterVM raw) leftFirstVM centre place entry q first 2048
    hz (fun m' z' hz' => hbudget m' z' hz') (fpack_of_entry hIP hcopy)) hm

/-- `centreLive_of_invLP_run` with `hfloor` replaced by `hcopy` and `hbudget`. -/
theorem centreLive_of_invLP_budget (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    {raw : List (Fin 2)} {c : Control} {r : GalilVM}
    (hIP : InvL raw c r ∧ EntryCounters raw r) (hcopy : CopyIdle r)
    (hbudget : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry raw) q first) 2048 m ⟨c, r⟩ z →
      BudgetAt (onLetterVM raw) leftFirstVM centre place entry q first z.ctl z.vm) :
    ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry raw) q first) 2048 m ⟨c, r⟩ z →
      CentreLive z.ctl z.vm :=
  centreLive_of_invLP_run centre place entry q first hIP
    (hfloor_of_invLP centre place entry q first hIP hcopy hbudget)

/-! ## The fresh-watch budget from the guard -/

open GalilScaffoldChainVerifier in
/-- **`budget_of_guard`.**  On the shift branch of a fresh (`periodOnly = false`)
watch, the guard's `0 ≤ margin` gives `4·h ≤ distance`
(`GalilCatchUpDistance.places_of_guard`); so the budget `h ≤ radius` follows
once the chain's `distance` is at most the compared VM radius (`hdist`, the
scan-radius identification of `distance_at_terminal`, not derived here). -/
theorem budget_of_guard (P : Shared) (qq : ℕ) (first : Fin 9)
    (cen : PlaceHead) (c : Fin 3) (ys : List (Fin 3)) (b : Fin 3)
    (radius : Counter) (hrc : Canonical radius)
    (sm dm : Bool) (bs cs : List Bool) (hbl : bs.length = ys.length + 1)
    {es : List Bool} {w : GalilScaffoldChainWatch.State}
    (hr : GalilScaffoldChainWatch.Run (watchStart cen c ys b (GalilScaffoldChainCredits.run
      (GalilScaffoldChainCredits.start radius) (GalilScaffoldChainCredits.prepEvents sm dm bs cs)))
      es w)
    (hz : zero w.lag = true)
    {s1 : GalilVM} (hs1 : s1.chain = .watch w) (hpo : s1.periodOnly = false)
    {vs : ScanVM} {vq : SearchVM}
    (hcmp : (galilFrame P qq first).compare s1 (scanLens.set s1 vs))
    (hmis : ¬ (galilFrame P qq first).matched (scanLens.set s1 vs))
    (hg : shiftGuardVM (afterMismatch s1 vs vq))
    (hh : periodLength w = ys.length + 1)
    (hdist : value w.machine.control.distance ≤ value (afterMismatch s1 vs vq).radius) :
    (periodLength w : ℤ) ≤ value (afterMismatch s1 vs vq).radius := by
  have h4 := (GalilCatchUpDistance.places_of_guard P qq first cen c ys b radius hrc sm dm bs cs
    hbl hr hz hs1 hpo hcmp hmis hg).1
  rw [hh]; push_cast
  linarith

#print axioms floor_of_fpack
#print axioms compare_counters
#print axioms fpack_tick
#print axioms fpack_steps
#print axioms fpack_of_entry
#print axioms hfloor_of_invLP
#print axioms centreLive_of_invLP_budget
#print axioms budget_of_guard

end PalPeg.GalilLengthFloor
