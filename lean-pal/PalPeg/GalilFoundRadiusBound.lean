import PalPeg.GalilSearchResult
import PalPeg.GalilRestartStage
import PalPeg.GalilScaffoldTopSegmentHeads

/-!
# The found radius versus the found semiperiod

`GalilPreludeEnds.prelude_done_before_extent'` needs
`hradius : value radius ≤ 4090*h - 2052`, where `radius` is the scan radius at
the found comparison (the counter `chainStart` receives) and `h` the least
candidate the DP returned.  This file derives it from the search.

* `Candidate w k h` carries `k < h` (so `1 ≤ h` and `max k 1 ≤ h`).
* **First stage.**  The stage barrier gives `radius ≤ 2*max k 1 ≤ 2h`
  (`first_radius_arith`).  At the tick (`found_radius_le`) the barrier is
  instantiated with `watchSegE_heads` (the radius counts matched events),
  `watchSegE_clock` and `first_stage_barrier`; the stage-duration premise
  `es1.length ≤ 63*(8*max k 1)` is a hypothesis (see Gaps).
* **Later stages.**  The window is `take (2n+1)`; the previous stage failed
  on `take (n+1)`.  Candidacy is monotone in the prefix, so the least `h` has
  `n < 4h` (`later_stage_n_lt`).  Then any `radius ≤ 512*n` gives the bound
  (`found_radius_le_later`).

## Gaps (stated, not hidden)

* `htime` in `found_radius_le`: the found segment `es1` is inside the first
  stage, `es1.length ≤ 63*(8*max k 1)`.  `idle_segment_found_quantum` proves
  internally that `es1.length + 1 = |as ++ bs ++ usedQ|` but does not export
  `usedQ.length ≤ runBudget (8*max k 1)`.
* `hprev` / `hbar` in `found_radius_le_later`: the failure of the previous
  stage on `take (n+1)` and the later-stage radius barrier `radius ≤ 512*n`.
-/

set_option autoImplicit false

namespace PalPeg.GalilFoundRadiusBound

open PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-! ## 1. Arithmetic -/

theorem candidate_lower_lt {w : List (Fin 3)} {k h : ℕ} (hc : GalilDpCorrect.Candidate w k h) :
    k < h ∧ 1 ≤ h := ⟨hc.1, by have := hc.1; omega⟩

/-- First stage: `radius ≤ 2*max k 1` and `k < h`. -/
theorem first_radius_arith (rad k h : ℕ) (hk : k < h) (hb : rad ≤ 2 * max k 1) :
    (rad : ℤ) ≤ 4090 * (h : ℤ) - 2052 := by
  have hm : max k 1 ≤ h := max_le (by omega) (by omega)
  have : rad ≤ 2 * h := by omega
  have h1 : 1 ≤ h := by omega
  have : (rad : ℤ) ≤ 2 * (h : ℤ) := by exact_mod_cast this
  have : (1 : ℤ) ≤ (h : ℤ) := by exact_mod_cast h1
  omega

/-- Candidacy is monotone along prefixes that still contain `4h+1` symbols. -/
theorem candidate_take_mono (w : List (Fin 3)) {m m' k h : ℕ}
    (hc : GalilDpCorrect.Candidate (w.take m) k h) (h4 : 4 * h + 1 ≤ m') (hm : m' ≤ m) :
    GalilDpCorrect.Candidate (w.take m') k h := by
  obtain ⟨hl, hn, hp2, hp4⟩ := hc
  rw [List.length_take] at hn
  have hwl : 4 * h + 1 ≤ w.length := by omega
  refine ⟨hl, ?_, ?_, ?_⟩
  · rw [List.length_take]; omega
  · rw [List.take_take, Nat.min_eq_left (by omega)]
    rw [List.take_take, Nat.min_eq_left (by omega)] at hp2
    exact hp2
  · rw [List.take_take, Nat.min_eq_left (by omega)]
    rw [List.take_take, Nat.min_eq_left (by omega)] at hp4
    exact hp4

/-- Later stage: a candidate on `take (2n+1)` with none on `take (n+1)` has `n < 4h`. -/
theorem later_stage_n_lt (w : List (Fin 3)) (n k h : ℕ)
    (hc : GalilDpCorrect.Candidate (w.take (2 * n + 1)) k h)
    (hprev : ∀ g, ¬ GalilDpCorrect.Candidate (w.take (n + 1)) k g) : n < 4 * h := by
  by_contra hle
  exact hprev h (candidate_take_mono w hc (by omega) (by omega))

theorem later_radius_arith (r : ℤ) (n h : ℕ) (hn : n < 4 * h) (hb : r ≤ 512 * (n : ℤ)) :
    r ≤ 4090 * (h : ℤ) - 2052 := by
  have : (n : ℤ) + 1 ≤ 4 * (h : ℤ) := by exact_mod_cast hn
  omega

/-! ## 2. First stage, at the found tick -/

/-- **`found_radius_le`.**  `search_result_at_tick` with the radius bound added
to its found disjunct: the scan radius `sF.radius` at the found comparison
(the counter `background_found_chain` hands to `chainStart`) satisfies the
`hradius` premise of `prelude_done_before_extent'` for the least candidate
`h = pos 11`.  The escape disjunct is unchanged. -/
theorem found_radius_le (P : Shared) (qq : ℕ) (first : Fin 9) (hP : Decodes P)
    (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    {raw : List (Fin 2)} {r : GalilVM} {Rad : ℕ} {last : Counter}
    (hR : Restarted raw r Rad last)
    (hcen : r.center = represent ⟨a :: ls,gap⟩ (rs.map some) q)
    {c0 : Control} (hcl : c0.clock = 2048)
    (hstage : StageEntry Rad last)
    {es1 : List Bool} {cF : Control} {sF : GalilVM}
    (hseg : WatchSegE P qq first 2048 es1 c0 r cF sF) (hsF : sF.chain = .idle)
    (hcF : cF.clock = 1) (vq : SearchVM) (hq : searchEffect P true sF vq)
    (hfound : vq.search.mode = .found)
    (htime : ∀ k : ℕ, value last = k → es1.length ≤ 63 * (8 * max k 1)) :
    (∃ k h : ℕ, value last = (k : ℤ) ∧
        GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (8*max k 1+1)) k 0
          (GalilScaffoldProgram.denote vq.dp.config) ∧
        (GalilScaffoldProgram.denote vq.dp.config).pc = 346 ∧
        (GalilScaffoldProgram.denote vq.dp.config).pos 11 = h ∧
        GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (8*max k 1+1)) k h ∧
        (∀ g, g < h →
          ¬ GalilDpCorrect.Candidate
              ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (8*max k 1+1)) k g) ∧
        sF.search.mode = .run ∧
        1 ≤ h ∧ value sF.radius ≤ 2 * ((max k 1 : ℕ) : ℤ) ∧
        value sF.radius ≤ 4090 * (h : ℤ) - 2052) ∨
    (∃ (L : ℕ) (vL : SearchVM), L ≤ es1.length ∧
      SearchRun ⟨a :: ls,gap⟩ (es1.take L) (searchLens.get r) vL ∧
      vL.search.mode ≠ .run ∧ vL.search.mode ≠ .found) := by
  rcases search_result_at_tick P qq first hP a ls rs q gap hR hcen hcl hstage hseg hsF hcF vq hq
      hfound with ⟨k, h, hk, hres, hpc, hpos, hcand, hmin, hrun⟩ | hesc
  · left
    obtain ⟨hkh, h1⟩ := candidate_lower_lt hcand
    -- the radius counts the matched events of the segment
    obtain ⟨_, _, hrad, _, _⟩ := watchSegE_heads P qq first 2048 hseg
    have hrv : value r.radius = (Rad : ℤ) := hR.2.2.2.2.1.2
    obtain ⟨av, hav, hes, _, _⟩ := watchSegE_clock P qq first 2048 hseg
    rw [hcl] at hes
    have ht : (av.map (fun b => (b, true))).length ≤ 63 * (8 * max k 1) := by
      rw [List.length_map, hav]; exact htime k hk
    have hbar := GalilScaffoldAdvanceClock.first_stage_barrier k Rad _ (hstage k hk) ht
    rw [← hes] at hbar
    have hb : Rad + es1.count true ≤ 2 * max k 1 := hbar
    have hle : value sF.radius ≤ 2 * ((max k 1 : ℕ) : ℤ) := by
      rw [hrad, hrv]
      have : ((Rad + es1.count true : ℕ) : ℤ) ≤ ((2 * max k 1 : ℕ) : ℤ) := by exact_mod_cast hb
      push_cast at this
      omega
    have harith := first_radius_arith (Rad + es1.count true) k h hkh hb
    have hbound : value sF.radius ≤ 4090 * (h : ℤ) - 2052 := by
      rw [hrad, hrv]; push_cast at harith; exact harith
    exact ⟨k, h, hk, hres, hpc, hpos, hcand, hmin, hrun, h1, hle, hbound⟩
  · exact Or.inr hesc

/-! ## 3. Later stages -/

/-- **`found_radius_le_later`.**  The found conjunct of
`later_stage_found_result` (window `take (2n+1)`, lower `k`, least candidate
`h`) together with the failure of the previous stage on `take (n+1)` and a
later-stage radius barrier `value radius ≤ 512*n` gives the `hradius` premise. -/
theorem found_radius_le_later (w : List (Fin 3)) (n k h : ℕ) (radius : Counter)
    (hcand : GalilDpCorrect.Candidate (w.take (2 * n + 1)) k h)
    (hprev : ∀ g, ¬ GalilDpCorrect.Candidate (w.take (n + 1)) k g)
    (hbar : value radius ≤ 512 * (n : ℤ)) :
    1 ≤ h ∧ k < h ∧ n < 4 * h ∧ value radius ≤ 4090 * (h : ℤ) - 2052 := by
  obtain ⟨hkh, h1⟩ := candidate_lower_lt hcand
  have hn := later_stage_n_lt w n k h hcand hprev
  exact ⟨h1, hkh, hn, later_radius_arith _ n h hn hbar⟩

/-- The previous-stage failure in the form a stage `Result` with `pc = 347` gives. -/
theorem prev_failure_of_result {w : List (Fin 3)} {k : ℕ} {y : GalilFppWide.Config 12}
    (hr : GalilDpCorrect.Result w k 0 y) (hp : y.pc = 347) :
    ∀ g, ¬ GalilDpCorrect.Candidate w k g := fun g =>
  GalilScaffoldSearchFinish.failed_no_candidate hr hp g (Nat.zero_le g)

#print axioms candidate_lower_lt
#print axioms first_radius_arith
#print axioms candidate_take_mono
#print axioms later_stage_n_lt
#print axioms later_radius_arith
#print axioms found_radius_le
#print axioms found_radius_le_later
#print axioms prev_failure_of_result

end PalPeg.GalilFoundRadiusBound
