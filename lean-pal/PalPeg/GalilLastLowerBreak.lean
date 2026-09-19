import PalPeg.GalilFoundLanding
import PalPeg.GalilRadiusConsumed

/-!
# `3 * h ≤ value last` at the break of a found cycle

`PalPeg/GalilFoundLanding.lean` closes gap 4 of `FoundResidual` only modulo a
threaded hypothesis

```
hlow : (3 * h : ℤ) ≤ value w3'.machine.control.last
```

(`stageEntry_after_found`), and points at `watch_last_lower`
(`PalPeg/GalilScaffoldChainInputSupply.lean`) as its source.  `watch_last_lower`
however only applies to a *fresh* watch: it needs
`s.machine.control = ready center xs b` at the start of a
`GalilScaffoldChainWatch.Run`, and at the break of a found cycle the control is
no longer literally a sweep from `ready` — it is that sweep with all three
counters lowered uniformly by the `shifts` half-period shifts already spent
(`Offset`, `ReadOrigin.offset`).  So the bound has to be re-derived through the
offset.

## What this file proves

* `sweep_last_lower_sharp` — the sharp form of `sweep_last_lower`
  (`PalPeg/GalilScaffoldChainReadOrigin.lean`), for *every* number of
  semiperiods rather than only for even ones: a successful sweep from `ready`
  of at least `(q+1) * h` places has `q * h ≤ value last`.  The witness is
  `GalilLastRadius.aligned_word q+1` (`distance ≤ last + h` after exactly
  `(q+1) * h` places) transported along `successful_prefix` and the monotonicity
  of `last` (`GalilScaffoldChainRestart.run_order`).  This is the `q = 3`
  instance that `watch_last_lower` proves by hand; the extra generality is what
  pays for the shift offset.
* `break_offset` — `break_data` (`PalPeg/GalilRadiusConsumed.lean`) with the
  offset **named**: at the break state of `m` chained rounds followed by `n`
  matched comparisons the control is the reference sweep lowered by exactly
  `(S+1) * h`, where `S = o'.shifts` is the shift count of the origin
  `rounds_origin` produces.  `break_data` hides that `k` behind an existential,
  and the bound below genuinely needs `k` to be a *multiple of `h`*: with only
  `Offset k` and `sweep_gap` one gets `distance + 1 ≤ last + 2*h`, i.e.
  `2*h + 1 ≤ last`, one semiperiod short of the goal.
* `last_lower_at_break` — the theorem gap 4 asks for, at the pre-break control;
  `last_lower_at_break_consume` — the same after the failing break consume
  (which moves neither `distance` nor `last`, `GalilLastRadius.break_gap`);
* `stageEntry_after_found_of_places` — `stageEntry_after_found` with `hlow`
  discharged, i.e. gap 4 reduced from a `last` bound to a *place count*.

## The one named hypothesis

`hplaces : (4 * h : ℤ) ≤ value ….machine.control.distance` — the chain has
consumed at least four semiperiods, i.e. has passed four boundary marks, by the
terminal comparison.  This is exactly

* the `hd` hypothesis of `watch_last_lower`
  (`4*(xs.length+1) ≤ value t.machine.control.distance`), and
* the `hdist` hypothesis of `GalilWatchPhase.phase_at_terminal_of_distance`
  (`4*(h : ℤ) ≤ value w.machine.control.distance`), whose `hcount`/`hdist` pair
  is the registered form of the same fact — so the two gaps are *one* gap, and
  discharging it discharges `phase = 4` as well.

It is not derivable here: it is the catch-up ledger
(`GalilScaffoldChainWatch.balance` / `lag` / `margin`) turning scan places into
chain consumes, exactly as `GalilWatchPhase`'s module docstring records.  The
arithmetic slack is genuine — `radius_le_distance` plus `ReadOrigin.size` only
give `2*h + 1 ≤ distance`, and `3*h ≤ last` is false at that many places.
-/

set_option autoImplicit false

namespace PalPeg.GalilLastLowerBreak

open GalilScaffoldCounter GalilScaffoldChainConsume GalilScaffoldChainSweep
  GalilScaffoldChainInputSupply GalilLastRadius

variable {raw : List (Fin 2)}

/-! ## 1. The sharp sweep bound, for every number of semiperiods -/

/-- **`q` semiperiods of `last` after `q+1` semiperiods of places.**
`sweep_last_lower` only covers even multiples (whole `bounce`s); the odd case is
`GalilLastRadius.half_gap`, packaged by `aligned_word`. -/
theorem sweep_last_lower_sharp (center b : Fin 3) (xs actual : List (Fin 3)) (q : ℕ)
    (ha : (run (ready center xs b) actual).broken = false)
    (hlen : (q + 1) * (xs.length + 1) ≤ actual.length) :
    ((q * (xs.length + 1) : ℕ) : ℤ) ≤ value (run (ready center xs b) actual).last := by
  obtain ⟨word, hwl, hwb, hwg⟩ := aligned_word center b xs (q + 1)
  have hdw : value (run (ready center xs b) word).distance = (word.length : ℤ) := by
    rw [GalilLastRadius.run_distance _ _ rfl hwb, (ready_values center b xs).1]; ring
  have hle : word.length ≤ actual.length := by omega
  have htake :=
    GalilScaffoldChainPrediction.successful_prefix word actual (ready center xs b) hwb ha hle
  have hsplit : actual = word ++ actual.drop word.length := by
    have he := List.take_append_drop word.length actual
    rw [htake] at he
    exact he.symm
  have hmid : run (ready center xs b) actual
      = run (run (ready center xs b) word) (actual.drop word.length) := by
    conv_lhs => rw [hsplit]
    rw [run_append]
  have hordw := GalilScaffoldChainRestart.run_order (ready center xs b) word
    (ordered_ready center b xs)
  have hmono := (GalilScaffoldChainRestart.run_order (run (ready center xs b) word)
    (actual.drop word.length) hordw.1).2
  rw [hdw, hwl] at hwg
  rw [hmid]
  push_cast at hwg hmono ⊢
  linarith

/-! ## 2. The break offset, named -/

/-- **`break_data` with the offset exposed.**  At the break of a found cycle the
control is the reference sweep from `ready` lowered by exactly `(S+1)*h`: `S`
half-period shifts accumulated in `ReadOrigin.offset`, plus the one shift of
`ReadOrigin.shiftRun`. -/
theorem break_offset {h m n : ℕ} {s s' t : OnlyCompareState}
    (o : ReadOrigin raw) (hh : o.interior.length + 1 = h) (he : Entry raw o s)
    (hrounds : CompareRounds h s m s') (hmatched : OnlyMatchedRun s' n t) :
    ∃ (S : ℕ) (tok bnd : Fin 3) (xs word : List (Fin 3)),
      xs.length + 1 = h ∧
      Offset (((S + 1) * h : ℕ) : ℤ) t.watch.machine.control
        (run (ready tok xs bnd) word) ∧
      (run (ready tok xs bnd) word).broken = false ∧
      t.watch.machine.control.broken = false := by
  obtain ⟨o', he', -, hinterior, -, -, -, -, -⟩ := rounds_origin hrounds o hh he
  have hh' : o'.interior.length + 1 = h := by rw [hinterior]; exact hh
  have ht0 : GalilScaffoldChainWatchTrace.Trace o'.shifted.machine [] s'.watch.machine := by
    rw [he'.machine]; exact GalilScaffoldChainWatchTrace.empty _
  have hl0 : LeftMoves o'.resumeLeft 0 s'.left := by rw [he'.left]; exact .stop _
  have checked := o'.matched_checked hmatched [] he'.scan he'.credit he'.radius ht0 hl0
  obtain ⟨-, finalExtra, -, htrace, -⟩ :=
    only_compare_history checked [] he'.scan he'.credit he'.radius ht0 hl0
  have hoff2 := (Offset.shift o'.shiftRun o'.offset).run finalExtra
  have hctl : t.watch.machine.control
      = run o'.shifted.machine.control finalExtra := htrace.control
  have hword : run (run (ready o'.token o'.interior o'.boundary) o'.pre) finalExtra
      = run (ready o'.token o'.interior o'.boundary) (o'.pre ++ finalExtra) :=
    (run_append _ _ _).symm
  rw [hword] at hoff2
  rw [← hctl] at hoff2
  have hpre : t.watch.machine.control.broken = false :=
    htrace.broken.trans ((chain_shift_broken o'.shiftRun).trans o'.unbroken)
  refine ⟨o'.shifts, o'.token, o'.boundary, o'.interior, o'.pre ++ finalExtra, hh', ?_, ?_, hpre⟩
  · have hk : (((o'.shifts + 1) * h : ℕ) : ℤ)
        = ((o'.shifts * (o'.interior.length + 1) : ℕ) : ℤ)
          + ((o'.interior.length + 1 : ℕ) : ℤ) := by
      rw [← hh']; push_cast; ring
    rw [hk]
    exact hoff2
  · rw [← hoff2.broken]; exact hpre

/-! ## 3. The bound gap 4 asks for -/

/-- **`last_lower_at_break`.**  Four semiperiods of consumed places at the break
of a found cycle give the chain's own lower bound `3*h ≤ value last`.

`sweep_last_lower_sharp` is applied at `q = S+4` on the reference sweep, which
`break_offset` says sits `(S+1)*h` above the break control on all three
counters; the place count moves `4*h ≤ distance` up to
`(S+5)*h ≤ word.length`, and `(S+4)*h - (S+1)*h = 3*h`. -/
theorem last_lower_at_break {h m n : ℕ} {s s' t : OnlyCompareState}
    (o : ReadOrigin raw) (hh : o.interior.length + 1 = h) (he : Entry raw o s)
    (hrounds : CompareRounds h s m s') (hmatched : OnlyMatchedRun s' n t)
    (hplaces : (4 * h : ℤ) ≤ value t.watch.machine.control.distance) :
    (3 * h : ℤ) ≤ value t.watch.machine.control.last := by
  obtain ⟨S, tok, bnd, xs, word, hxs, hoff, hsweep, -⟩ := break_offset o hh he hrounds hmatched
  subst hxs
  have hL : value (run (ready tok xs bnd) word).distance = (word.length : ℤ) := by
    rw [GalilLastRadius.run_distance _ _ rfl hsweep, (ready_values tok bnd xs).1]; ring
  have hd := hoff.distance
  rw [hL] at hd
  -- `(S+5) * h ≤ word.length`
  have hlenZ : (((S + 5) * (xs.length + 1) : ℕ) : ℤ) ≤ (word.length : ℤ) := by
    push_cast at hd hplaces ⊢
    linarith
  have hlen : (S + 4 + 1) * (xs.length + 1) ≤ word.length := by
    have : ((S + 5) * (xs.length + 1) : ℕ) ≤ word.length := by exact_mod_cast hlenZ
    omega
  have hlast := sweep_last_lower_sharp tok bnd xs word (S + 4) hsweep hlen
  have hl := hoff.last
  push_cast at hlast hl ⊢
  linarith

/-- The same after the failing break consume, which moves neither `distance`
nor `last` (`GalilLastRadius.break_gap`). -/
theorem last_lower_at_break_consume {h m n : ℕ} {s s' t : OnlyCompareState}
    (o : ReadOrigin raw) (hh : o.interior.length + 1 = h) (he : Entry raw o s)
    (hrounds : CompareRounds h s m s') (hmatched : OnlyMatchedRun s' n t)
    {seen : Option (Fin 3)}
    (hbreak : (consume t.watch.machine.control seen).broken = true)
    (hplaces : (4 * h : ℤ) ≤ value (consume t.watch.machine.control seen).distance) :
    (3 * h : ℤ) ≤ value (consume t.watch.machine.control seen).last := by
  obtain ⟨-, -, -, -, -, -, -, -, hpre⟩ := break_offset o hh he hrounds hmatched
  obtain ⟨hdist, hlast⟩ := break_gap t.watch.machine.control seen hpre hbreak
  rw [hdist] at hplaces
  rw [hlast]
  exact last_lower_at_break o hh he hrounds hmatched hplaces

#print axioms sweep_last_lower_sharp
#print axioms break_offset
#print axioms last_lower_at_break
#print axioms last_lower_at_break_consume

/-! ## 4. Gap 4 of `GalilFoundLanding`, on a place count -/

open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- **`stageEntry_after_found` with `hlow` discharged.**  Same statement as
`GalilScaffoldChainInputSupply.stageEntry_after_found`, with the chain's lower
bound replaced by the place count at the break. -/
theorem stageEntry_after_found_of_places (P : Shared) (qq : ℕ) (first : Fin 9) (delay h : ℕ)
    {raw : List (Fin 2)} (org : ReadOrigin raw) (hint : org.interior.length + 1 = h)
    {s2' : GalilVM} {t' : ShiftState} {v : GalilScaffoldChainWatch.State} {cycle : Counter}
    (hpo : (shiftLens.set s2' ⟨t', .watch v, cycle⟩).periodOnly = true)
    (hzv : zero v.lag = true)
    (hee : Entry raw org (toOnly (shiftLens.set s2' ⟨t', .watch v, cycle⟩) v))
    {m : ℕ} {c1 c' : Control} {o : Bool} {s' : GalilVM}
    (hrounds : Rounds P qq first delay h m {c1 with mode := .scan, clock := delay, output := o}
      (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c' s')
    {n : ℕ} {c3 : Control} {s3 : GalilVM} (hseg3 : ScanSeg P qq first delay n c' s' c3 s3)
    (w3 : GalilScaffoldChainWatch.State) (hs3 : s3.chain = .watch w3)
    (hz3 : GalilScaffoldCounter.zero w3.lag = true)
    (w3' : GalilScaffoldChainWatch.State) (hw3' : w3' = GalilScaffoldChainWatch.immediate w3)
    (ha : PalPeg.GalilRadiusConsumed.Aligned org)
    (hbroken : w3'.machine.control.broken = true)
    (hplaces : (4 * h : ℤ) ≤ value w3'.machine.control.distance) :
    StageEntry (foundRestartRadius org.radius h m n) w3'.machine.control.last := by
  obtain ⟨-, w', hw', hz', hp', hcr⟩ := rounds_lift P qq first delay h hrounds v hpo rfl hzv
  obtain ⟨w'', hw'', -, -, hrun⟩ := scanSeg_only P qq first delay hseg3 w' hp' hw' hz'
  have hww : w'' = w3 := by rw [hs3] at hw''; injection hw'' with e; exact e.symm
  subst hww
  subst hw3'
  exact PalPeg.GalilRadiusConsumed.foundCycleStage_final' org hint hee hcr hrun ha
    (seen := read (right w''.machine.verifier)) hbroken rfl
    (last_lower_at_break_consume org hint hee hcr hrun hbroken hplaces)

#print axioms stageEntry_after_found_of_places

end PalPeg.GalilLastLowerBreak
