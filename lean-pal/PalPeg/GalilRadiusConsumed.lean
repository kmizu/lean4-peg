import PalPeg.GalilLastRadius
import PalPeg.GalilScaffoldChainReadOrigin

/-!
# Closing `RadiusConsumed` at the break of a found cycle

`PalPeg/GalilLastRadius.lean` reduced the stage budget of the found-cycle
restart to one isolated statement, `RadiusConsumed Rad c : Rad ≤ value
c.distance + 1`: the restart radius does not exceed the number of places the
chain has consumed since the watch start, plus the single unconsumed place of
the failing break comparison.

The reason the statement is true is an *alignment* invariant of the read
origins.  A `ReadOrigin` records the verifier position `position start` of the
fresh watch start, the centre `center` of the current scan, and the number
`shifts` of half-period shifts already performed.  The centre advances by one
half period per shift while the verifier start does not move, so

  `position start + shifts * h ≤ center`   (`Aligned`)

with equality at a fresh origin.  The record itself only carries the weaker
`startBefore : position start ≤ center`, which is *not* enough: the difference
`center - position start - shifts * h` is exactly the slack by which the
consumed-place count may fall short of the radius.

Rather than strengthening the `ReadOrigin` field (which changes the signature
of a structure used by 141 downstream modules), the invariant is carried here
as an explicit predicate `Aligned`, together with the two closure lemmas that
make it free at every place the scaffold actually builds origins:

* `aligned_of_only` — an origin produced by `ReadOrigin.ofOnly` /
  `entry_of_only` from an `OnlyOrigin` is aligned, because `OnlyOrigin`
  carries `startPosition : position start = center` and the origin has
  `shifts = 0`;
* `aligned_rounds` — `rounds_origin` preserves it, because it advances
  `shifts` by `m` and `center` by `m * h` and keeps `start`.

From `Aligned` the chain of facts is short:

* `origin_distance` — `distance` at the watched state counts `pre`, lowered by
  the `shifts * h` of the accumulated uniform counter offset (`ReadOrigin.offset`,
  `run_distance`);
* `radius_le_distance` — with `reads_input_cycle` (`position watched =
  position start + pre.length`) and `endPosition` (`position watched =
  center + radius + 1`), alignment gives `radius + 1 ≤ value distance`;
* `distance_at_break` — the `m` rounds move the origin (`rounds_origin`), the
  half-period shift lowers `distance` by `h` (`chain_shift_values`) and the
  final `n` matched comparisons raise it by `n`
  (`matched_checked` + `only_compare_history` + `Trace.distance`);
* `radiusConsumed_at_break` — this is exactly
  `foundRestartRadius orgRadius h m n ≤ value distance + 1`;
* `foundCycleStage_final` — combined with `GalilLastRadius.foundCycleStage`,
  the stage-entry budget of the found-cycle restart.
-/

set_option autoImplicit false

namespace PalPeg.GalilRadiusConsumed

open GalilScaffoldCounter GalilScaffoldChainConsume GalilScaffoldInputHead
  GalilScaffoldChainInputSupply GalilLastRadius

variable {raw : List (Fin 2)}

/-! ## 1. The alignment invariant -/

/-- **Alignment.**  The fresh watch start sits at least `shifts` half periods
below the current centre: the centre advances one half period per shift while
`start` never moves.  Equality holds at a fresh origin. -/
def Aligned (o : ReadOrigin raw) : Prop :=
  position o.start.machine.verifier + o.shifts*(o.interior.length+1) ≤ o.center

/-- **Base case.**  An origin built from an `OnlyOrigin` (that is, by
`ReadOrigin.ofOnly`, hence by `entry_of_only`) is aligned: it has no earlier
shift and `OnlyOrigin.startPosition` puts the watch start exactly at the
centre. -/
theorem aligned_of_only (o : ReadOrigin raw) (p : OnlyOrigin raw)
    (hstart : o.start = p.start) (hshifts : o.shifts = 0) (hcenter : o.center = p.center) :
    Aligned o := by
  unfold Aligned
  rw [hstart, hshifts, hcenter, p.startPosition]
  simp

/-- **Induction step.**  `rounds_origin` advances `shifts` by `m` and `center`
by `m * h` and keeps `start` and `interior`, so it preserves alignment. -/
theorem aligned_rounds {h m : ℕ} (o o' : ReadOrigin raw)
    (hstart : o'.start = o.start) (hinterior : o'.interior = o.interior)
    (hshifts : o'.shifts = o.shifts + m) (hcenter : o'.center = o.center + m*h)
    (hh : o.interior.length+1 = h) (ha : Aligned o) : Aligned o' := by
  unfold Aligned at ha ⊢
  rw [hstart, hinterior, hshifts, hcenter, ← hh]
  calc position o.start.machine.verifier + (o.shifts+m)*(o.interior.length+1)
      = (position o.start.machine.verifier + o.shifts*(o.interior.length+1))
          + m*(o.interior.length+1) := by ring
    _ ≤ o.center + m*(o.interior.length+1) := Nat.add_le_add_right ha _

/-! ## 2. `radius + 1 ≤ distance` at an aligned origin -/

/-- The watched `distance` counts the places read since the fresh start,
lowered by the uniform offset of the `shifts` earlier chain shifts. -/
theorem origin_distance (o : ReadOrigin raw) :
    value o.watched.machine.control.distance
      = (o.pre.length : ℤ) - ((o.shifts*(o.interior.length+1) : ℕ) : ℤ) := by
  have hrun : value (GalilScaffoldChainSweep.run
      (ready o.token o.interior o.boundary) o.pre).distance
      = value (ready o.token o.interior o.boundary).distance + (o.pre.length : ℤ) :=
    run_distance _ _ rfl o.sweep_unbroken
  have hz : value (ready o.token o.interior o.boundary).distance = 0 := rfl
  rw [o.offset.distance, hrun, hz]
  ring

/-- **The origin-side bound.**  At an aligned origin the chain has already
consumed at least `radius + 1` places: the verifier has walked from
`position start` to `center + radius + 1`, and only `shifts * h` of those
places are absorbed by the accumulated shift offset, which alignment bounds
by `center - position start`. -/
theorem radius_le_distance (o : ReadOrigin raw) (ha : Aligned o) :
    (o.radius : ℤ) + 1 ≤ value o.watched.machine.control.distance := by
  have hpos := (reads_input_cycle o.reads raw o.represents o.present
    o.token o.boundary o.interior o.sweep_unbroken).1
  rw [o.endPosition] at hpos
  unfold Aligned at ha
  have hd := origin_distance o
  obtain ⟨S, hS⟩ : ∃ S : ℕ, o.shifts*(o.interior.length+1) = S := ⟨_, rfl⟩
  rw [hS] at ha hd
  omega

/-! ## 3. The break of a found cycle -/

/-- **The consumed places at the break.**  After `m` chained rounds and a final
segment of `n` matched comparisons the chain has consumed at least
`o.radius + 1 + m*h - h + n` places since the fresh start. -/
theorem distance_at_break {h m n : ℕ} {s s' t : OnlyCompareState}
    (o : ReadOrigin raw) (hh : o.interior.length+1 = h) (he : Entry raw o s)
    (hrounds : CompareRounds h s m s') (hmatched : OnlyMatchedRun s' n t)
    (ha : Aligned o) :
    (o.radius : ℤ) + 1 + ((m*h : ℕ) : ℤ) - ((h : ℕ) : ℤ) + ((n : ℕ) : ℤ)
      ≤ value t.watch.machine.control.distance := by
  obtain ⟨o',he',hstart,hinterior,_,_,hshifts,hcenter,hradius⟩ := rounds_origin hrounds o hh he
  have hh' : o'.interior.length+1 = h := by rw [hinterior]; exact hh
  have ha' : Aligned o' := aligned_rounds o o' hstart hinterior hshifts hcenter hh ha
  have ht0 : GalilScaffoldChainWatchTrace.Trace o'.shifted.machine [] s'.watch.machine := by
    rw [he'.machine]; exact GalilScaffoldChainWatchTrace.empty _
  have hl0 : LeftMoves o'.resumeLeft 0 s'.left := by rw [he'.left]; exact .stop _
  have checked := o'.matched_checked hmatched [] he'.scan he'.credit he'.radius ht0 hl0
  obtain ⟨_, finalExtra, hlen, htrace, _⟩ :=
    only_compare_history checked [] he'.scan he'.credit he'.radius ht0 hl0
  have hshift := (chain_shift_values o'.shiftRun).1
  have hbase := radius_le_distance o' ha'
  have hdist := htrace.distance
  rw [hshift, hh'] at hdist
  have hlen' : (finalExtra.length : ℤ) = (n : ℤ) := by simp [hlen]
  rw [hlen'] at hdist
  obtain ⟨M, hM⟩ : ∃ M : ℕ, m*h = M := ⟨_, rfl⟩
  rw [hM] at hradius ⊢
  rw [hradius] at hbase
  omega

/-- **`RadiusConsumed` at the break.**  The restart radius
`foundRestartRadius o.radius h m n = o.radius + 1 + m*h - h + n + 1` is at most
one more than the places consumed. -/
theorem radiusConsumed_at_break {h m n : ℕ} {s s' t : OnlyCompareState}
    (o : ReadOrigin raw) (hh : o.interior.length+1 = h) (he : Entry raw o s)
    (hrounds : CompareRounds h s m s') (hmatched : OnlyMatchedRun s' n t)
    (ha : Aligned o) :
    RadiusConsumed (foundRestartRadius o.radius h m n) t.watch.machine.control := by
  have hsize : 2*h ≤ o.radius := by rw [← hh]; exact o.size
  have hdist := distance_at_break o hh he hrounds hmatched ha
  unfold RadiusConsumed foundRestartRadius
  obtain ⟨M, hM⟩ : ∃ M : ℕ, m*h = M := ⟨_, rfl⟩
  rw [hM] at hdist ⊢
  omega

/-! ## 4. The break state is an offset of a successful sweep -/

/-- All of `foundCycleStage`'s chain-side premises at the break state, from the
rounds data alone: the break control is the `k`-shift offset of a successful
sweep from `ready`, and `RadiusConsumed` holds. -/
theorem break_data {h m n : ℕ} {s s' t : OnlyCompareState}
    (o : ReadOrigin raw) (hh : o.interior.length+1 = h) (he : Entry raw o s)
    (hrounds : CompareRounds h s m s') (hmatched : OnlyMatchedRun s' n t)
    (ha : Aligned o) :
    ∃ (k : ℤ) (tok bnd : Fin 3) (xs word : List (Fin 3)),
      xs.length+1 = h ∧
      Offset k t.watch.machine.control
        (GalilScaffoldChainSweep.run (ready tok xs bnd) word) ∧
      (GalilScaffoldChainSweep.run (ready tok xs bnd) word).broken = false ∧
      t.watch.machine.control.broken = false ∧
      RadiusConsumed (foundRestartRadius o.radius h m n) t.watch.machine.control := by
  obtain ⟨o',he',hstart,hinterior,_,_,hshifts,hcenter,hradius⟩ := rounds_origin hrounds o hh he
  have hh' : o'.interior.length+1 = h := by rw [hinterior]; exact hh
  have ht0 : GalilScaffoldChainWatchTrace.Trace o'.shifted.machine [] s'.watch.machine := by
    rw [he'.machine]; exact GalilScaffoldChainWatchTrace.empty _
  have hl0 : LeftMoves o'.resumeLeft 0 s'.left := by rw [he'.left]; exact .stop _
  have checked := o'.matched_checked hmatched [] he'.scan he'.credit he'.radius ht0 hl0
  obtain ⟨_, finalExtra, _, htrace, _⟩ :=
    only_compare_history checked [] he'.scan he'.credit he'.radius ht0 hl0
  -- the offset of the shifted state, then of the `finalExtra` comparisons
  have hoff1 := Offset.shift o'.shiftRun o'.offset
  have hoff2 := hoff1.run finalExtra
  have hctl : t.watch.machine.control
      = GalilScaffoldChainSweep.run o'.shifted.machine.control finalExtra := htrace.control
  have hword : GalilScaffoldChainSweep.run
      (GalilScaffoldChainSweep.run (ready o'.token o'.interior o'.boundary) o'.pre) finalExtra
      = GalilScaffoldChainSweep.run (ready o'.token o'.interior o'.boundary)
        (o'.pre ++ finalExtra) := (GalilScaffoldChainSweep.run_append _ _ _).symm
  rw [hword] at hoff2
  rw [← hctl] at hoff2
  have hpre : t.watch.machine.control.broken = false :=
    htrace.broken.trans ((chain_shift_broken o'.shiftRun).trans o'.unbroken)
  refine ⟨_, o'.token, o'.boundary, o'.interior, o'.pre ++ finalExtra, hh', hoff2, ?_, hpre, ?_⟩
  · rw [← hoff2.broken]; exact hpre
  · exact radiusConsumed_at_break o hh he hrounds hmatched ha

/-! ## 5. The stage budget of the found-cycle restart -/

/-- **The found-cycle stage entry, with no chain-side hypothesis left.**  Given
the rounds data of `rounds_break` / `life_restarted` (an aligned read origin
`o`, its `Entry`, the `m` chained rounds, the final `n` matched comparisons),
the failing break comparison, and the chain's own lower bound
`3 * h ≤ value last` (`watch_last_lower`), the stage budget
`3 * Rad ≤ 5 * value last` holds at the restart. -/
theorem foundCycleStage_final {h m n : ℕ} {s s' t : OnlyCompareState}
    (o : ReadOrigin raw) (hh : o.interior.length+1 = h) (he : Entry raw o s)
    (hrounds : CompareRounds h s m s') (hmatched : OnlyMatchedRun s' n t)
    (ha : Aligned o) {seen : Option (Fin 3)} {last : Counter}
    (hbreak : (consume t.watch.machine.control seen).broken = true)
    (hlast : last = (consume t.watch.machine.control seen).last)
    (hlow : (3*h : ℤ) ≤ value last) :
    StageEntry (foundRestartRadius o.radius h m n) last := by
  obtain ⟨k, tok, bnd, xs, word, hxs, hoff, hsweep, hpre, hcons⟩ :=
    break_data o hh he hrounds hmatched ha
  exact foundCycleStage o.radius h m n hxs hoff hsweep hpre hbreak hlast hlow hcons

/-- The same conclusion as the `FoundCycleStage` obligation of
`PalPeg/GalilRestartStage.lean`. -/
theorem foundCycleStage_final' {h m n : ℕ} {s s' t : OnlyCompareState}
    (o : ReadOrigin raw) (hh : o.interior.length+1 = h) (he : Entry raw o s)
    (hrounds : CompareRounds h s m s') (hmatched : OnlyMatchedRun s' n t)
    (ha : Aligned o) {seen : Option (Fin 3)} {last : Counter}
    (hbreak : (consume t.watch.machine.control seen).broken = true)
    (hlast : last = (consume t.watch.machine.control seen).last)
    (hlow : (3*h : ℤ) ≤ value last) :
    FoundCycleStage o.radius h m n last :=
  foundCycleStage_final o hh he hrounds hmatched ha hbreak hlast hlow

#print axioms aligned_of_only
#print axioms aligned_rounds
#print axioms origin_distance
#print axioms radius_le_distance
#print axioms distance_at_break
#print axioms radiusConsumed_at_break
#print axioms break_data
#print axioms foundCycleStage_final
#print axioms foundCycleStage_final'

end PalPeg.GalilRadiusConsumed
