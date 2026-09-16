import PalPeg.GalilScaffoldTopReadyFound
import PalPeg.GalilPrepLeast
import PalPeg.GalilSearchContract
import PalPeg.GalilScaffoldTopProgressS

/-!
# Supplying the DP premises of the found cycle from the search co-run

`cycle_found_minv` (`PalPeg/GalilLiveCentreCycle2.lean`) and
`search_contract_of_idle_search` (`PalPeg/GalilSearchContract.lean`) both take
the DP facts of the found tick as *hypotheses*:

* `hres : GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower 0
    (GalilScaffoldProgram.denote vq.dp.config)`,
* `hpc  : (GalilScaffoldProgram.denote vq.dp.config).pc = 346` (found) / `= 347` (idle),
* `hout : (GalilScaffoldProgram.denote vq.dp.config).pos 11 = h`.

This file discharges them from the co-run itself.  The co-run invariant that
ties the DP progress to the segment is `SearchInv`: along a chain-idle
`WatchSegE` the search projection performs exactly the `SearchRun` of the
segment's events (`searchInv_watchSegE`), and the calibrated first stage
(`search_first_stage`) turns that run into a completed DP search.  The window
the DP actually searches is **not** the current scan radius but the calibrated
stage window `(stream ⟨a :: ls,gap⟩).take (8*max k 1 + 1)`, where `k = value last`
is the lower bound installed at the restart; i.e. `span = 8*max k 1` and the
`lower` argument of `Result` is that same `k`.
-/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-! ## The co-run invariant -/

/-- The DP-progress invariant of the co-run: the search projection at `s` is
what the search performs when driven by the events `es` from the search
projection at `r`. -/
def SearchInv (P : Shared) (r : GalilVM) (es : List Bool) (s : GalilVM) : Prop :=
  SearchRun (P.place r) es (searchLens.get r) (searchLens.get s)

/-- `SearchInv` is established by any chain-idle `WatchSegE`. -/
theorem searchInv_watchSegE (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (hplace : ∀ u v : GalilVM, u.center = v.center → P.place u = P.place v)
    {es : List Bool} {c c' : Control} {s t : GalilVM}
    (h : WatchSegE P q first delay es c s c' t) (ht : t.chain = .idle) :
    SearchInv P s es t :=
  watchSegE_searchRun P q first delay hplace h ht

/-- `SearchInv` composes along a segment followed by the search step of one
further tick (the comparison of the found tick). -/
theorem searchInv_step (P : Shared) {r s : GalilVM} {es : List Bool} (a : Bool) (vq : SearchVM)
    (h : SearchInv P r es s) (hcen : s.center = r.center)
    (hplace : ∀ u v : GalilVM, u.center = v.center → P.place u = P.place v)
    (hstep : searchStep (P.place s) a (searchLens.get s) vq) :
    SearchRun (P.place r) (es ++ [a]) (searchLens.get r) vq := by
  rw [hplace s r hcen] at hstep
  exact searchRun_append h (.cons hstep (.nil _))

#print axioms searchInv_watchSegE
#print axioms searchInv_step

/-! ## The found tick with its search quantum exposed -/

/-- `idle_segment_found_first` re-run with the quantum of the first stage
carried out: on the `found` branch the state `v2` just before the run phase
and the event list `usedQ` of the quantum are exhibited, so that the answer
tape of `vq` is the end of an actual `SafeQuanta` entered in `run` mode. -/
theorem idle_segment_found_quantum (P : Shared) (qq : ℕ) (first : Fin 9)
    (hplace : ∀ u v : GalilVM, u.center = v.center → P.place u = P.place v)
    (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    {c0 : Control} {r : GalilVM} (hcl : c0.clock = 2048) (hplr : P.place r = ⟨a :: ls,gap⟩)
    (hcen : r.center = represent ⟨a :: ls,gap⟩ (rs.map some) q)
    (c : Fin 3) (hc : GalilScaffoldPlace.read ⟨a :: ls,gap⟩ = some c)
    (lower radius : Counter) (hlc : Canonical lower) (k : ℕ) (hk : value lower = k)
    (hrc : Canonical radius) (rad : ℕ) (hrad : value radius = rad) (hr : 3*rad ≤ 5*k)
    (hsearch : r.search = GalilScaffoldSearchFinish.begin lower radius) (hlower : r.lower = lower)
    {es1 : List Bool} {c1 : Control} {s1 : GalilVM}
    (hseg : WatchSegE P qq first 2048 es1 c0 r c1 s1) (hs1 : s1.chain = .idle)
    (aF : Bool) (hclock1 : aF = true → c1.clock = 1) (vq : SearchVM)
    (hstep : searchStep (P.place s1) aF (searchLens.get s1) vq)
    (hfound : vq.search.mode = .found) :
    (∃ (v2 : SearchVM) (usedQ : List Bool),
        v2.search.mode = .run ∧
        GalilScaffoldSearchRun.SafeQuanta v2.search v2.dp usedQ vq.search vq.dp ∧
        vq.dp.done = true ∧
        GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (8*max k 1+1)) k 0
          (GalilScaffoldProgram.denote vq.dp.config) ∧
        s1.search.mode = .run) ∨
    (∃ (L : ℕ) (vL : SearchVM), L ≤ es1.length ∧
      SearchRun ⟨a :: ls,gap⟩ (es1.take L) (searchLens.get r) vL ∧
      vL.search.mode ≠ .run ∧ vL.search.mode ≠ .found) := by
  have hrunSeg := watchSegE_searchRun P qq first 2048 hplace hseg hs1
  rw [hplr] at hrunSeg
  have hcen1 : s1.center = r.center := watchSegE_center P qq first 2048 hseg
  rw [hplace s1 r hcen1, hplr] at hstep
  obtain ⟨av1, hav1, hes1, hcl1, _⟩ := watchSegE_clock P qq first 2048 hseg
  rw [hcl] at hes1 hcl1
  obtain ⟨m, hm⟩ : ∃ m, max k 1 + (2*k + 2*((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (8*max k 1+1)).length + 7)
      + GalilScaffoldTimingCost.runBudget (8*max k 1) = m := ⟨_, rfl⟩
  have hpad : SearchRun ⟨a :: ls,gap⟩ (List.replicate m false) vq vq :=
    searchRun_pad _ m vq (Or.inl hfound)
  have hrunF : SearchRun ⟨a :: ls,gap⟩ (es1 ++ [aF]) (searchLens.get r) vq :=
    searchRun_append hrunSeg (.cons hstep (.nil _))
  have hrunAll : SearchRun ⟨a :: ls,gap⟩ ((es1 ++ [aF]) ++ List.replicate m false) (searchLens.get r) vq :=
    searchRun_append hrunF hpad
  have hadv : (es1 ++ [aF]) ++ List.replicate m false =
      GalilScaffoldAdvanceClock.advances 2048 2048
        ((av1 ++ aF :: List.replicate m false).map (fun b => (b, true))) := by
    rw [List.map_append, GalilScaffoldAdvanceClock.advances_append, map_fst_map_pair, ← hcl1, ← hes1,
      List.append_assoc]
    congr 1
    simp only [List.map_cons, GalilScaffoldAdvanceClock.advances, List.singleton_append, List.map_replicate]
    congr 1
    · cases aF
      · rfl
      · rw [hclock1 rfl]; rfl
    · exact (advances_replicate_false 2048 m _).symm
  have hlen : max k 1 + (2*k + 2*((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (8*max k 1+1)).length + 7)
      + GalilScaffoldTimingCost.runBudget (8*max k 1) ≤ ((es1 ++ [aF]) ++ List.replicate m false).length := by
    rw [hm]; simp only [List.length_append, List.length_replicate, List.length_singleton]; omega
  obtain ⟨as, bs, usedQ, rest, v1, v2, v3, hsplit, has, hbs, h1, h2, h3, _, hm0, hw0, hp, hm1, hw1, hl1,
      hm2, hq, hm3, _, ⟨dpv, hdp, hres⟩, hcand⟩ :=
    search_first_stage a ls rs q gap r.center hcen c hc lower radius hlc k hk hrc rad hrad hr hrunAll
      hsearch hlower (by simp [hav1]) hadv hlen
  have hU : SearchRun ⟨a :: ls,gap⟩ (as ++ bs ++ usedQ) (searchLens.get r) v3 :=
    searchRun_append (searchRun_append h1 h2) h3
  obtain ⟨L, hL⟩ : ∃ L, (as ++ bs ++ usedQ).length = L := ⟨_, rfl⟩
  have hUlen : 1 ≤ L := by
    rw [← hL]; simp only [List.length_append]; omega
  have hprefixU : as ++ bs ++ usedQ = ((es1 ++ [aF]) ++ List.replicate m false).take L := by
    rw [hsplit, ← hL, List.take_left]
  have hlenF : (es1 ++ [aF]).length = es1.length + 1 := by simp
  rcases Nat.lt_trichotomy L (es1.length + 1) with hlt | heq | hgt
  · right
    have hL' : L ≤ es1.length := by omega
    have hUes : as ++ bs ++ usedQ = es1.take L := by
      rw [hprefixU, List.append_assoc, List.take_append_of_le_length hL']
    refine ⟨L, v3, hL', by rw [← hUes]; exact hU, hm3, ?_⟩
    have hsplit1 : es1 = (as ++ bs ++ usedQ) ++ es1.drop L := by
      have := List.take_append_drop L es1
      rw [← hUes] at this
      exact this.symm
    exact watchSegE_search_not_found P qq first 2048 hplace hseg hs1 _ _ v3 hsplit1
      (by intro h0; rw [h0] at hL; simp at hL; omega) (by rw [hplr]; exact hU)
  · left
    have hUes : as ++ bs ++ usedQ = es1 ++ [aF] := by
      rw [hprefixU, heq, ← hlenF, List.take_left]
    have hv3 : v3 = vq := by
      rw [hUes] at hU
      exact searchRun_unique hU hrunF
    subst hv3
    refine ⟨v2, usedQ, hm2, hq, by rw [hdp], by rw [hdp]; exact hres, ?_⟩
    have := stage_prefix_mode ⟨a :: ls,gap⟩ k h1 h2 h3 hm0 hw0 hp hm1 hw1 hl1 hm2 hq hm3 es1 [aF]
      (searchLens.get s1) hUes (by simp) hrunSeg
    exact this.2 rfl
  · exfalso
    have hF : es1 ++ [aF] = (as ++ bs ++ usedQ).take (es1.length + 1) := by
      rw [hprefixU, List.take_take, Nat.min_eq_left (by omega), ← hlenF, List.take_left]
    have hsplitU : as ++ bs ++ usedQ = (es1 ++ [aF]) ++ (as ++ bs ++ usedQ).drop (es1.length + 1) := by
      have := List.take_append_drop (es1.length + 1) (as ++ bs ++ usedQ)
      rw [← hF] at this
      exact this.symm
    have hne : (as ++ bs ++ usedQ).drop (es1.length + 1) ≠ [] := by
      intro h0
      have := congrArg List.length h0
      rw [List.length_drop, hL] at this
      simp only [List.length_nil] at this
      omega
    have := stage_prefix_mode ⟨a :: ls,gap⟩ k h1 h2 h3 hm0 hw0 hp hm1 hw1 hl1 hm2 hq hm3 _ _ vq hsplitU hne hrunF
    exact this.1 hfound

#print axioms idle_segment_found_quantum

/-! ## The extraction at the tick -/

/-- **The DP premises of the found cycle.**  From a restarted state along a
chain-idle `WatchSegE` to a tick whose search quantum lands in `found`, the
co-run supplies exactly the three hypotheses `cycle_found_minv` takes: the DP
`Result` on the calibrated stage window `(stream ⟨a :: ls,gap⟩).take (span+1)`
with `span = 8*max k 1` and `lower = k = value last`, the found program counter
`346`, and the OUTPUT cursor `pos 11 = h` — together with the fact that `h` is
then the *least* candidate.  The second disjunct is the escape of
`idle_segment_found_first`: the first stage already halted inside the segment
in a non-`found` exit mode, so this `found` belongs to a later stage. -/
theorem search_result_at_tick (P : Shared) (qq : ℕ) (first : Fin 9) (hP : Decodes P)
    (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    {raw : List (Fin 2)} {r : GalilVM} {Rad : ℕ} {last : Counter}
    (hR : Restarted raw r Rad last)
    (hcen : r.center = represent ⟨a :: ls,gap⟩ (rs.map some) q)
    {c0 : Control} (hcl : c0.clock = 2048)
    (hstage : ∀ k : ℕ, value last = k → 3 * Rad ≤ 5 * k)
    {es1 : List Bool} {cF : Control} {sF : GalilVM}
    (hseg : WatchSegE P qq first 2048 es1 c0 r cF sF) (hsF : sF.chain = .idle)
    (hcF : cF.clock = 1) (vq : SearchVM) (hq : searchEffect P true sF vq)
    (hfound : vq.search.mode = .found) :
    (∃ k h : ℕ, value last = (k : ℤ) ∧
        GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (8*max k 1+1)) k 0
          (GalilScaffoldProgram.denote vq.dp.config) ∧
        (GalilScaffoldProgram.denote vq.dp.config).pc = 346 ∧
        (GalilScaffoldProgram.denote vq.dp.config).pos 11 = h ∧
        GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (8*max k 1+1)) k h ∧
        (∀ g, g < h →
          ¬ GalilDpCorrect.Candidate
              ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (8*max k 1+1)) k g) ∧
        sF.search.mode = .run) ∨
    (∃ (L : ℕ) (vL : SearchVM), L ≤ es1.length ∧
      SearchRun ⟨a :: ls,gap⟩ (es1.take L) (searchLens.get r) vL ∧
      vL.search.mode ≠ .run ∧ vL.search.mode ≠ .found) := by
  obtain ⟨hidle, hrep, hfoc, hscan, ⟨hrc, hrv⟩, hlc, hsearch, hlower, hlast, hlv⟩ := hR
  obtain ⟨hreadr, hplr⟩ := hP.1 r a ls rs q gap hcen
  obtain ⟨k, hk⟩ : ∃ k : ℕ, value last = k := ⟨(value last).toNat, (Int.toNat_of_nonneg hlv).symm⟩
  have hstep : searchStep (P.place sF) true (searchLens.get sF) vq := by
    rcases hq with ⟨_, hstep⟩ | ⟨hne, _⟩
    · exact hstep
    · exact absurd hsF hne
  rcases idle_segment_found_quantum P qq first hP.2 a ls rs q gap hcl hplr hcen (P.centre r) hreadr
      last r.radius hlast k hk hrc Rad hrv (hstage k hk) hsearch hlower hseg hsF true
      (fun _ => hcF) vq hstep hfound with
    ⟨v2, usedQ, hm2, hqq, _, hres, hrun⟩ | ⟨L, vL, hL, hrunL, hnr, hnf⟩
  · left
    obtain ⟨h, u, qp, xs, hcand, _, _, _, _, _, hcur⟩ :=
      found_copy_walk_least (w := (GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (8*max k 1+1))
        (lower := k) (span := 8*max k 1) ⟨a :: ls,gap⟩ rfl hqq hm2 hfound hres
    have hpc := result_pc_of_candidate hres hcand
    exact ⟨k, h, hk, hres, hpc, hcur, hcand, no_candidate_below_of_least hres hpc hcur, hrun⟩
  · exact Or.inr ⟨L, vL, hL, hrunL, hnr, hnf⟩

#print axioms search_result_at_tick

/-- The idle-branch counterpart: a quantum entered in `run` mode that leaves it
without landing in `found` halts at the failure entry `347`.  This is the
`hidle` premise of `search_contract_of_idle_search`; its `hres` is still the
calibrated stage window, not the current scan radius (see the module note). -/
theorem missed_pc_347 {s t : GalilScaffoldSearchFinish.State}
    {x y : GalilScaffoldControl.Machine 12} {as : List Bool}
    {w : List (Fin 3)} {lower : ℕ}
    (hr : GalilScaffoldSearchRun.SafeQuanta s x as t y) (hs : s.mode = .run)
    (ht : t.mode ≠ .run) (hnf : t.mode ≠ .found)
    (hv : GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote y.config)) :
    (GalilScaffoldProgram.denote y.config).pc = 347 := by
  have hl := (GalilScaffoldSearchRun.safe_quanta_terminal_link hr (Or.inl hs)).resolve_left ht
  have hne : y.config.pc ≠ 346 := fun he => hnf (hl.1.mpr he)
  rcases hv with ⟨_, _, _, _, hpc, _, _⟩ | ⟨hpc, _⟩
  · exact absurd (show y.config.pc = 346 from hpc) hne
  · exact hpc

#print axioms missed_pc_347

/-- The calibration of the shift's `h` against the prepared semiperiod.  The
shift entry `beginShiftVM'` uses `h = periodLength w` for the watch state `w`
at the terminal comparison, while the preparation installs
`watchStart ver c ys b final` with `ys.length + 1 = h_dp = pos 11`.  At the
start of the watch the two counts agree: `periodLength` skips the FRONT cell,
so it counts exactly the `ys.length + 1` semiperiod letters. -/
theorem periodLength_watchStart (ver : PlaceHead) (c : Fin 3) (ys : List (Fin 3)) (b : Fin 3)
    (final : GalilScaffoldChainCredits.State) :
    periodLength (watchStart ver c ys b final) = ys.length + 1 := by
  cases ys with
  | nil => rfl
  | cons y ys =>
    simp [periodLength, watchStart, GalilScaffoldChainConsume.ready,
      GalilScaffoldChainPeriod.moveRight]
    omega

#print axioms periodLength_watchStart

/-! ## Towards later stages

The escape disjunct of `search_result_at_tick` is a `found` belonging to a
*later* search stage.  `search_first_stage` only covers the first stage, and
the `Top` layer has so far never analysed the `.double`/`.wait` scheduler
modes.  The two lemmas below are the missing `SearchRun`-level counterparts of
`searchRun_growing` and `searchRun_prepared` for a later stage's entry. -/

/-- `n` doubling ticks from work `n` are the scheduler's `Double.Run`, ending
in `double` with no work.  The DP program, the lower bound and the walker are
untouched by the doubling phase. -/
theorem searchRun_doubling (center : GalilScaffoldPlace.Place) (as : List Bool) :
    ∀ {v v' : SearchVM}, SearchRun center as v v' → v.search.mode = .double →
      v.search.work = ofNat as.length →
      GalilScaffoldDouble.Run v.search as v'.search ∧
        v'.dp = v.dp ∧ v'.lower = v.lower ∧ v'.walker = v.walker ∧
        v'.search.mode = .double ∧ v'.search.work = ofNat 0 := by
  induction as with
  | nil =>
    intro v v' h hm hw
    cases h
    exact ⟨.stop _ hm (by rw [hw]; rfl), rfl, rfl, rfl, hm, hw⟩
  | cons a as ih =>
    intro v v'' h hm hw
    cases h with
    | cons hstep hrest =>
      rename_i v'
      have hpos : positive v.search.work = true := by
        rw [hw, positive_ofNat]; simp
      have hv' : v' = {v with search := GalilScaffoldSearchRun.advance a (GalilScaffoldDouble.step v.search)} := by
        unfold searchStep at hstep
        rw [hm] at hstep
        simp only [hpos, if_true] at hstep
        exact hstep
      have hm' : v'.search.mode = .double := by
        rw [hv']
        show (GalilScaffoldSearchRun.advance a (GalilScaffoldDouble.step v.search)).mode = _
        cases a <;> simpa [GalilScaffoldSearchRun.advance, GalilScaffoldDouble.step] using hm
      have hw' : v'.search.work = ofNat as.length := by
        rw [hv']
        show (GalilScaffoldSearchRun.advance a (GalilScaffoldDouble.step v.search)).work = _
        cases a <;>
          simp [GalilScaffoldSearchRun.advance, GalilScaffoldDouble.step, hw, dec_ofNat_succ]
      obtain ⟨hd, hdp, hl, hwk, hm'', hw''⟩ := ih hrest hm' hw'
      refine ⟨.next _ _ a as hm hpos ?_, ?_, ?_, ?_, hm'', hw''⟩
      · rw [hv'] at hd; exact hd
      · rw [hdp, hv']
      · rw [hl, hv']
      · rw [hwk, hv']

/-- The prepare dispatch and its body from a `double` state without work: the
`.double` counterpart of `searchRun_prepared` (the two `searchStep` branches
have the same body). -/
theorem searchRun_prepared_double (center : GalilScaffoldPlace.Place)
    {x p : GalilScaffoldPrepareControl.State} {a : Bool} {bs : List Bool} {lowerC : Counter}
    (hp : GalilScaffoldPreparePaced.PacedPrepared lowerC center x (a :: bs) p)
    {v v' : SearchVM} (h : SearchRun center (a :: bs) v v') (hx : v.toPrep = x)
    (hm : v.search.mode = .double) (hw : positive v.search.work = false) (hl : v.lower = lowerC) :
    v'.toPrep = p ∧ v'.search.quarter = v.search.quarter ∧ v'.lower = v.lower := by
  cases hp with
  | intro _ _ _ hrun =>
    cases h with
    | cons hstep hrest =>
      rename_i v1
      have hv1 : v1 = SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a
          (GalilScaffoldPrepareControl.prepare v.toPrep v.lower center)) v.search.quarter v.lower := by
        unfold searchStep at hstep
        rw [hm] at hstep
        simp only [hw, Bool.false_eq_true, if_false] at hstep
        exact hstep
      have hx1 : v1.toPrep = GalilScaffoldPreparePaced.afterAdvance a
          (GalilScaffoldPrepareControl.prepare x lowerC center) := by
        rw [hv1, toPrep_ofPrep, hx, hl]
      have hall : ∀ e ∈ (List.replicate bs.length true).zip bs, e.1 = true := by
        intro e he
        have := List.of_mem_zip he
        exact List.eq_of_mem_replicate this.1
      have hrest' : SearchRun center (((List.replicate bs.length true).zip bs).map Prod.snd) v1 v' := by
        rw [map_snd_zip_replicate]; exact hrest
      obtain ⟨hz, hq, hl'⟩ := searchRun_paced center hall hrun hrest' hx1
      refine ⟨hz, ?_, ?_⟩
      · rw [hq, hv1, ofPrep_quarter]
      · rw [hl', hv1, ofPrep_lower]

#print axioms searchRun_doubling
#print axioms searchRun_prepared_double

/-- The doubling phase is deterministic: `positive s.work` decides `stop`
against `next`. -/
theorem double_run_unique {s t t' : GalilScaffoldSearchFinish.State} {as : List Bool}
    (h1 : GalilScaffoldDouble.Run s as t) (h2 : GalilScaffoldDouble.Run s as t') : t = t' := by
  induction h1 generalizing t' with
  | stop s hm hz =>
    cases h2 with
    | stop => rfl
  | next s t a as hm hp _ ih =>
    cases h2 with
    | next _ _ _ _ _ _ hr => exact ih hr

theorem runState_toPrep (w : SearchVM) :
    GalilScaffoldStagePrepare.runState w.toPrep w.search.quarter = w.search := by
  cases w with
  | mk s d l wk => cases s; rfl

theorem toPrep_restoreState {v v' : SearchVM} (hdp : v'.dp = v.dp) (hwk : v'.walker = v.walker) :
    v'.toPrep = GalilScaffoldStagePrepare.restoreState v.toPrep v'.search := by
  cases v with
  | mk s d l wk =>
    cases v' with
    | mk s' d' l' wk' =>
      simp only at hdp hwk
      subst hdp; subst hwk; rfl

#print axioms double_run_unique
#print axioms runState_toPrep
#print axioms toPrep_restoreState

/-- **A later search stage on the actual run.**  The `search_first_stage`
analogue for a stage entered in `double` mode with work `n`: the doubling, the
paced preparation and the DP quantum of `later_stage_chain`, on the window
`(stream ⟨a :: ls,gap⟩).take (2*n+1)` with the unchanged lower bound `k`. -/
theorem search_later_stage (a : Fin 2) (ls rs qq : List (Fin 2)) (gap : Bool) (cen : PlaceHead)
    (hcen : cen = represent ⟨a :: ls,gap⟩ (rs.map some) qq)
    (c : Fin 3) (hc : GalilScaffoldPlace.read ⟨a :: ls,gap⟩ = some c)
    (k n clock : ℕ)
    {v0 v' : SearchVM} {es : List Bool} (hrun : SearchRun ⟨a :: ls,gap⟩ es v0 v')
    (hm0 : v0.search.mode = .double) (hq0 : v0.search.quarter = 0)
    (hw0 : v0.search.work = ofNat n) (hs0 : v0.search.span = ofNat 0)
    (hcanon : Canonical v0.search.debt)
    (hd : 0 ≤ value v0.search.debt ∨ (-1 ≤ value v0.search.debt ∧ clock = 2048))
    (hlow : v0.lower = ofNat k)
    (ha : n % 4 = 0) (hn : 8 ≤ n) (hl : 4*k ≤ n)
    {av : List Bool}
    (hes : es = GalilScaffoldAdvanceClock.advances 2048 clock (av.map (fun b => (b, true))))
    (hclock : 1 ≤ clock ∧ clock ≤ 2048)
    (hlen : n + (2*k + 2*((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (2*n+1)).length + 7)
      + GalilScaffoldTimingCost.runBudget (2*n) ≤ es.length) :
    ∃ (as bs usedQ rest : List Bool) (v1 v2 v3 : SearchVM),
      es = as ++ bs ++ usedQ ++ rest ∧ as.length = n ∧
      SearchRun ⟨a :: ls,gap⟩ as v0 v1 ∧ SearchRun ⟨a :: ls,gap⟩ bs v1 v2 ∧
      SearchRun ⟨a :: ls,gap⟩ usedQ v2 v3 ∧ SearchRun ⟨a :: ls,gap⟩ rest v3 v' ∧
      v2.search.mode = .run ∧
      GalilScaffoldSearchRun.SafeQuanta v2.search v2.dp usedQ v3.search v3.dp ∧
      v3.search.mode ≠ .run ∧
      (∃ dpv, v3.dp = ⟨dpv, true⟩ ∧
        GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (2*n+1)) k 0
          (GalilScaffoldProgram.denote dpv)) := by
  obtain ⟨n2, hn2⟩ : ∃ m, 2*k + 2*((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (2*n+1)).length + 7 = m :=
    ⟨_, rfl⟩
  obtain ⟨n3, hn3⟩ : ∃ m, GalilScaffoldTimingCost.runBudget (2*n) = m := ⟨_, rfl⟩
  rw [hn3, hn2] at hlen
  obtain ⟨as, has⟩ : ∃ l, l = es.take n := ⟨_, rfl⟩
  obtain ⟨bs, hbs⟩ : ∃ l, l = (es.drop n).take n2 := ⟨_, rfl⟩
  obtain ⟨cs, hcs⟩ : ∃ l, l = ((es.drop n).drop n2).take n3 := ⟨_, rfl⟩
  obtain ⟨tail, htail⟩ : ∃ l, l = ((es.drop n).drop n2).drop n3 := ⟨_, rfl⟩
  have hsplit : es = as ++ bs ++ cs ++ tail := by
    rw [has, hbs, hcs, htail]
    simp only [List.append_assoc, List.take_append_drop]
  have hasl : as.length = n := by rw [has, List.length_take]; omega
  have hbsl : bs.length = n2 := by rw [hbs, List.length_take, List.length_drop]; omega
  have hcsl : cs.length = n3 := by
    rw [hcs, List.length_take, List.length_drop, List.length_drop]; omega
  have hprefix : as ++ bs ++ cs = es.take (n + n2 + n3) := by
    rw [hsplit]
    have e1 : (as ++ bs ++ cs).length = n + n2 + n3 := by
      rw [List.length_append, List.length_append, hasl, hbsl, hcsl]
    rw [← e1, List.take_left]
  have he : as ++ bs ++ cs = GalilScaffoldAdvanceClock.advances 2048 clock
      ((av.take (n + n2 + n3)).map (fun b => (b, true))) := by
    rw [hprefix, hes, List.map_take, GalilScaffoldAdvanceClock.advances_take]
  obtain ⟨u, p, used, rest', t, dpv, hdr, hqu, hp, hpm, hcsplit, hq, hnr, hres, _⟩ :=
    later_stage_chain as bs cs _ v0.toPrep k clock a ls rs qq gap cen hcen c hc
      hm0 (by rw [toPrep_work, hw0, hasl]) hs0 hcanon hd (by rw [hasl]; exact ha)
      (by rw [hasl]; exact hn) (by rw [hasl]; exact hl) (by rw [hbsl, hasl, ← hn2])
      (by rw [hcsl, hasl, ← hn3]) hclock he
  rw [hasl] at hres
  -- the actual run through the phases
  rw [hsplit] at hrun
  rw [List.append_assoc, List.append_assoc] at hrun
  obtain ⟨v1, hrun1, hrun'⟩ := searchRun_split _ as hrun
  obtain ⟨v2, hrun2, hrun''⟩ := searchRun_split _ bs hrun'
  rw [hcsplit, List.append_assoc] at hrun''
  -- doubling
  obtain ⟨hdr1, hdp1, hl1, hwk1, hm1, hw1⟩ :=
    searchRun_doubling ⟨a :: ls,gap⟩ as hrun1 hm0 (by rw [hw0, hasl])
  have hrs0 : GalilScaffoldStagePrepare.runState v0.toPrep 0 = v0.search := by
    rw [← hq0]; exact runState_toPrep v0
  rw [hrs0] at hdr
  have hu : u = v1.search := double_run_unique hdr hdr1
  subst hu
  -- preparation
  have hx1 : v1.toPrep = GalilScaffoldStagePrepare.restoreState v0.toPrep v1.search :=
    toPrep_restoreState hdp1 hwk1
  obtain ⟨a', bs', hbs'⟩ : ∃ a' bs', bs = a' :: bs' := by
    cases hbs0 : bs with
    | nil => rw [hbs0] at hbsl; simp at hbsl; omega
    | cons a' bs' => exact ⟨a', bs', rfl⟩
  rw [hbs'] at hp hrun2
  have hw1' : positive v1.search.work = false := by rw [hw1]; rfl
  obtain ⟨hp2, hq2, hl2⟩ :=
    searchRun_prepared_double ⟨a :: ls,gap⟩ hp hrun2 hx1 hm1 hw1' (by rw [hl1, hlow])
  -- the run
  obtain ⟨hsearch2, hdp2⟩ := toPrep_search_eq hp2
  have hsearch2' : v2.search = GalilScaffoldStagePrepare.runState p v1.search.quarter := by
    rw [hsearch2, hq2]
  obtain ⟨v3, hrun3, hs3, hx3, _, _, hrest⟩ := searchRun_quanta _ hq hrun'' hsearch2' hdp2
  have hp2m : v2.search.mode = .run := by rw [← toPrep_mode, hp2]; exact hpm
  have hq' : GalilScaffoldSearchRun.SafeQuanta v2.search v2.dp used v3.search v3.dp := by
    rw [hsearch2', hdp2, hs3, hx3]; exact hq
  refine ⟨as, bs, used, rest' ++ tail, v1, v2, v3, ?_, hasl, hrun1, ?_, hrun3, hrest, hp2m, hq',
    ?_, ⟨dpv, hx3, hres⟩⟩
  · rw [hsplit, hcsplit]; simp [List.append_assoc]
  · rw [hbs']; exact hrun2
  · rw [hs3]; exact hnr

#print axioms search_later_stage

/-- The per-stage counterpart of `search_result_at_tick`: when a later stage
ends in `found`, its DP facts are the same three premises `cycle_found_minv`
takes, now on the window `span = 2*n`.  This is the induction *step* for
`search_result_at_tick'`; the induction itself is not closed (see the gaps). -/
theorem later_stage_found_result (a : Fin 2) (ls rs qq : List (Fin 2)) (gap : Bool) (cen : PlaceHead)
    (hcen : cen = represent ⟨a :: ls,gap⟩ (rs.map some) qq)
    (c : Fin 3) (hc : GalilScaffoldPlace.read ⟨a :: ls,gap⟩ = some c)
    (k n clock : ℕ)
    {v0 v' : SearchVM} {es : List Bool} (hrun : SearchRun ⟨a :: ls,gap⟩ es v0 v')
    (hm0 : v0.search.mode = .double) (hq0 : v0.search.quarter = 0)
    (hw0 : v0.search.work = ofNat n) (hs0 : v0.search.span = ofNat 0)
    (hcanon : Canonical v0.search.debt)
    (hd : 0 ≤ value v0.search.debt ∨ (-1 ≤ value v0.search.debt ∧ clock = 2048))
    (hlow : v0.lower = ofNat k)
    (ha : n % 4 = 0) (hn : 8 ≤ n) (hl : 4*k ≤ n)
    {av : List Bool}
    (hes : es = GalilScaffoldAdvanceClock.advances 2048 clock (av.map (fun b => (b, true))))
    (hclock : 1 ≤ clock ∧ clock ≤ 2048)
    (hlen : n + (2*k + 2*((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (2*n+1)).length + 7)
      + GalilScaffoldTimingCost.runBudget (2*n) ≤ es.length) :
    ∃ (as bs usedQ rest : List Bool) (v1 v2 v3 : SearchVM),
      es = as ++ bs ++ usedQ ++ rest ∧ as.length = n ∧
      SearchRun ⟨a :: ls,gap⟩ as v0 v1 ∧ SearchRun ⟨a :: ls,gap⟩ bs v1 v2 ∧
      SearchRun ⟨a :: ls,gap⟩ usedQ v2 v3 ∧ SearchRun ⟨a :: ls,gap⟩ rest v3 v' ∧
      v3.search.mode ≠ .run ∧
      (v3.search.mode = .found → ∃ h : ℕ,
        GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (2*n+1)) k 0
          (GalilScaffoldProgram.denote v3.dp.config) ∧
        (GalilScaffoldProgram.denote v3.dp.config).pc = 346 ∧
        (GalilScaffoldProgram.denote v3.dp.config).pos 11 = h ∧
        GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (2*n+1)) k h ∧
        (∀ g, g < h →
          ¬ GalilDpCorrect.Candidate
              ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (2*n+1)) k g)) := by
  obtain ⟨as, bs, usedQ, rest, v1, v2, v3, hsplit, hasl, h1, h2, h3, hrest, hm2, hq, hm3,
      ⟨dpv, hx3, hres⟩⟩ :=
    search_later_stage a ls rs qq gap cen hcen c hc k n clock hrun hm0 hq0 hw0 hs0 hcanon hd hlow
      ha hn hl hes hclock hlen
  refine ⟨as, bs, usedQ, rest, v1, v2, v3, hsplit, hasl, h1, h2, h3, hrest, hm3, ?_⟩
  intro hfound
  have hres' : GalilDpCorrect.Result
      ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (2*n+1)) k 0
      (GalilScaffoldProgram.denote v3.dp.config) := by rw [hx3]; exact hres
  obtain ⟨h, u, qp, xs, hcand, _, _, _, _, _, hcur⟩ :=
    found_copy_walk_least (w := (GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (2*n+1))
      (lower := k) (span := 2*n) ⟨a :: ls,gap⟩ rfl hq hm2 hfound hres'
  have hpc := result_pc_of_candidate hres' hcand
  exact ⟨h, hres', hpc, hcur, hcand, no_candidate_below_of_least hres' hpc hcur⟩

#print axioms later_stage_found_result

/-! ## The DP entry datum of a later stage

`runEntries_of_calibrated` (`PalPeg/GalilRunEntries.lean`) needs, at the
`.run` entry of a stage, the four conjuncts of `DpSafeRem`: the preload
identity of the handed-over program, canonical debt, the debt bound on the
events still ahead, and the calibrated DP budget.  `firstStage_dpEntry`
derives them for the first stage; the two theorems below do the same for a
later (doubling) stage. -/

/-- The advance budget of a later stage: at most `n/4` comparisons fall inside
it, and strictly fewer when the stage starts at a full clock. -/
theorem later_stage_count (n clock : ℕ) (ev : List (Bool × Bool))
    (hn : 8 ≤ n) (hclock : 1 ≤ clock ∧ clock ≤ 2048) (ht : ev.length ≤ 63*(2*n)) :
    (GalilScaffoldAdvanceClock.advances 2048 clock ev).count true ≤ n/4 ∧
      (clock = 2048 →
        (GalilScaffoldAdvanceClock.advances 2048 clock ev).count true + 1 ≤ n/4) := by
  have ha := GalilScaffoldAdvanceClock.advances_le_compares 2048 clock ev
  have hl : (ev.map Prod.fst).count true ≤ ev.length := by
    simpa using List.count_le_length (l := ev.map Prod.fst) (a := true)
  refine ⟨?_, ?_⟩
  · have h := GalilScaffoldAdvanceClock.later_stage_advances (2*n) clock ev (by omega) hclock ht
    omega
  · intro h2048
    subst h2048
    have hi := GalilScaffoldMatchClock.run_invariant 2048 2048 (ev.map Prod.fst) (by decide)
      (by omega)
    omega

/-- **The entry datum of a later stage.**  At the handover of a doubling stage
the DP machine is the preload of the stage window `(stream …).take (2*n+1)`
with the unchanged lower bound `k`, the debt is canonical, and the events left
in the stage both pay for the DP run and fit the calibrated budget. -/
theorem laterStage_dpEntry (a : Fin 2) (ls : List (Fin 2)) (gap : Bool)
    (k n clock : ℕ) {v0 v1 v2 : SearchVM} {as bs cs : List Bool}
    (h1 : SearchRun ⟨a :: ls, gap⟩ as v0 v1) (h2 : SearchRun ⟨a :: ls, gap⟩ bs v1 v2)
    (hm0 : v0.search.mode = .double) (hq0 : v0.search.quarter = 0)
    (hw0 : v0.search.work = ofNat n) (hs0 : v0.search.span = ofNat 0)
    (hcanon : Canonical v0.search.debt)
    (hd : 0 ≤ value v0.search.debt ∨ (-1 ≤ value v0.search.debt ∧ clock = 2048))
    (hlow : v0.lower = ofNat k)
    (hmod : n % 4 = 0) (hn : 8 ≤ n) (hl : 4*k ≤ n)
    (ha : as.length = n)
    (hb : bs.length =
      2*k + 2*((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (2*n+1)).length + 7)
    (hcsl : cs.length = GalilScaffoldTimingCost.runBudget (2*n))
    (hclock : 1 ≤ clock ∧ clock ≤ 2048)
    {ev : List (Bool × Bool)}
    (he : as ++ bs ++ cs = GalilScaffoldAdvanceClock.advances 2048 clock ev) :
    v2.dp = ⟨GalilScaffoldPreload.initial
        ((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (2*n+1)) k, false⟩ ∧
      v2.search.mode = .run ∧ Canonical v2.search.debt ∧
      ((cs.count true : ℤ)) ≤ value v2.search.debt ∧
      3186*((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (2*n+1)).length + 1683
        ≤ 64*cs.length := by
  obtain ⟨a'', bs'', hbs⟩ : ∃ a'' bs'', bs = a'' :: bs'' := by
    cases hb0 : bs with
    | nil => rw [hb0] at hb; simp only [List.length_nil] at hb; omega
    | cons a'' bs'' => exact ⟨a'', bs'', rfl⟩
  subst hbs
  -- the doubling phase
  obtain ⟨hdr1, hdp1, hl1, hwk1, hm1, hw1⟩ :=
    searchRun_doubling ⟨a :: ls, gap⟩ as h1 hm0 (by rw [hw0, ha])
  have hspan1 : v1.search.span = ofNat (2*n) := by
    have h := GalilScaffoldDouble.span_of_run hdr1 0 hs0
    rw [h, ha, Nat.zero_add]
  obtain ⟨_, hcred⟩ := GalilScaffoldDouble.completed_credit hdr1 hq0 (by rw [ha]; exact hmod)
  have hcanon1 : Canonical v1.search.debt := GalilScaffoldDouble.canonical hdr1 hcanon
  -- the preparation phase
  have hus' : v1.toPrep.span = ofNat (2*n) := hspan1
  obtain ⟨p, hp, hpm, hpp, hpd, _, _⟩ :=
    GalilScaffoldPrepareControl.prepare_complete v1.toPrep k (2*n) ⟨a :: ls, gap⟩ hus'
  have hprep : GalilScaffoldPreparePaced.PacedPrepared (ofNat k) ⟨a :: ls, gap⟩ v1.toPrep
      (a'' :: bs'') {p with debt := GalilScaffoldPreparePaced.spend (a'' :: bs'') v1.toPrep.debt} :=
    GalilScaffoldPreparePaced.prepared_interleave hp (a'' :: bs'') hb
  have hw1' : positive v1.search.work = false := by rw [hw1]; rfl
  have hv2 : v2.toPrep =
      {p with debt := GalilScaffoldPreparePaced.spend (a'' :: bs'') v1.toPrep.debt} :=
    (searchRun_prepared_double _ hprep h2 rfl hm1 hw1' (by rw [hl1, hlow])).1
  -- the handover datum
  have hdprog : v2.dp =
      ⟨GalilScaffoldPreload.initial
        ((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (2*n+1)) k, false⟩ := by
    show v2.toPrep.program = _
    rw [hv2]
    show p.program = _
    calc p.program = ⟨p.program.config, p.program.done⟩ := rfl
      _ = _ := by rw [hpp, hpd]
  have hmoderun : v2.search.mode = .run := by rw [← toPrep_mode, hv2]; exact hpm
  have hdebt2 : v2.search.debt =
      GalilScaffoldPreparePaced.spend (a'' :: bs'') v1.toPrep.debt := by
    show v2.toPrep.debt = _
    rw [hv2]
  have hcanon2 : Canonical v2.search.debt := by
    rw [hdebt2]
    exact GalilScaffoldPreparePaced.spend_canonical _ _ hcanon1
  have hvalue2 : value v2.search.debt =
      value v0.search.debt + (n/4 : ℕ) - (as ++ a'' :: bs'').count true := by
    rw [hdebt2, GalilScaffoldPreparePaced.spend_value]
    show value v1.search.debt - _ = _
    rw [hcred, ha]
    simp only [List.count_append, Nat.cast_add]
    omega
  -- the calibrated budget and the debt barrier
  have hwl : ((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (2*n+1)).length ≤ 2*n+1 :=
    List.length_take_le _ _
  have hlen_ev : ev.length = as.length + (a'' :: bs'').length + cs.length := by
    have h := congrArg List.length he
    rw [GalilScaffoldAdvanceClock.advances_length] at h
    rw [← h, List.length_append, List.length_append]
  have htime : ev.length ≤ 63*(2*n) := by
    rw [hlen_ev, ha, hb, hcsl]
    have h := GalilScaffoldTimingCost.later_stage_ticks n k
      ((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (2*n+1)).length hn hl hwl
    omega
  obtain ⟨hcnt, hcnt'⟩ := later_stage_count n clock ev hn hclock htime
  have hcount := congrArg (List.count true) he
  simp only [List.count_append] at hcount
  have hbound : ((cs.count true : ℤ)) ≤ value v2.search.debt := by
    rw [hvalue2]
    simp only [List.count_append, Nat.cast_add]
    rcases hd with hd | ⟨hd, h2048⟩
    · omega
    · have := hcnt' h2048
      omega
  have hbud : 3186*((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (2*n+1)).length + 1683
      ≤ 64*cs.length := by
    have h := GalilScaffoldTimingCost.runBudget_sufficient (2*n)
    rw [hcsl]
    omega
  exact ⟨hdprog, hmoderun, hcanon2, hbound, hbud⟩

#print axioms later_stage_count
#print axioms laterStage_dpEntry

/-- **`search_later_stage` with the DP entry datum.**  Same decomposition, for
a stage whose event list is exactly the calibrated stage length, together with
the four conjuncts `DpSafeRem v2 (usedQ ++ rest)` of
`PalPeg/GalilSearchReadyInv.lean` at the `.run` entry `v2`. -/
theorem search_later_stage' (a : Fin 2) (ls rs qq : List (Fin 2)) (gap : Bool) (cen : PlaceHead)
    (hcen : cen = represent ⟨a :: ls,gap⟩ (rs.map some) qq)
    (c : Fin 3) (hc : GalilScaffoldPlace.read ⟨a :: ls,gap⟩ = some c)
    (k n clock : ℕ)
    {v0 v' : SearchVM} {es : List Bool} (hrun : SearchRun ⟨a :: ls,gap⟩ es v0 v')
    (hm0 : v0.search.mode = .double) (hq0 : v0.search.quarter = 0)
    (hw0 : v0.search.work = ofNat n) (hs0 : v0.search.span = ofNat 0)
    (hcanon : Canonical v0.search.debt)
    (hd : 0 ≤ value v0.search.debt ∨ (-1 ≤ value v0.search.debt ∧ clock = 2048))
    (hlow : v0.lower = ofNat k)
    (ha : n % 4 = 0) (hn : 8 ≤ n) (hl : 4*k ≤ n)
    {av : List Bool}
    (hes : es = GalilScaffoldAdvanceClock.advances 2048 clock (av.map (fun b => (b, true))))
    (hclock : 1 ≤ clock ∧ clock ≤ 2048)
    (hlen : es.length = n
      + (2*k + 2*((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (2*n+1)).length + 7)
      + GalilScaffoldTimingCost.runBudget (2*n)) :
    ∃ (as bs usedQ rest : List Bool) (v1 v2 v3 : SearchVM),
      es = as ++ bs ++ usedQ ++ rest ∧ as.length = n ∧
      bs.length = 2*k + 2*((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (2*n+1)).length + 7 ∧
      (usedQ ++ rest).length = GalilScaffoldTimingCost.runBudget (2*n) ∧
      SearchRun ⟨a :: ls,gap⟩ as v0 v1 ∧ SearchRun ⟨a :: ls,gap⟩ bs v1 v2 ∧
      SearchRun ⟨a :: ls,gap⟩ usedQ v2 v3 ∧ SearchRun ⟨a :: ls,gap⟩ rest v3 v' ∧
      v2.search.mode = .run ∧
      GalilScaffoldSearchRun.SafeQuanta v2.search v2.dp usedQ v3.search v3.dp ∧
      v3.search.mode ≠ .run ∧
      (∃ dpv, v3.dp = ⟨dpv, true⟩ ∧
        GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (2*n+1)) k 0
          (GalilScaffoldProgram.denote dpv)) ∧
      v2.dp = ⟨GalilScaffoldPreload.initial
        ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (2*n+1)) k, false⟩ ∧
      Canonical v2.search.debt ∧
      (((usedQ ++ rest).count true : ℤ)) ≤ value v2.search.debt ∧
      3186*((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (2*n+1)).length + 1683
        ≤ 64*(usedQ ++ rest).length := by
  obtain ⟨n2, hn2⟩ : ∃ m, 2*k + 2*((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (2*n+1)).length + 7 = m :=
    ⟨_, rfl⟩
  obtain ⟨n3, hn3⟩ : ∃ m, GalilScaffoldTimingCost.runBudget (2*n) = m := ⟨_, rfl⟩
  rw [hn3, hn2] at hlen
  obtain ⟨as, has⟩ : ∃ l, l = es.take n := ⟨_, rfl⟩
  obtain ⟨bs, hbs⟩ : ∃ l, l = (es.drop n).take n2 := ⟨_, rfl⟩
  obtain ⟨cs, hcs⟩ : ∃ l, l = ((es.drop n).drop n2).take n3 := ⟨_, rfl⟩
  obtain ⟨tail, htail⟩ : ∃ l, l = ((es.drop n).drop n2).drop n3 := ⟨_, rfl⟩
  have hsplit : es = as ++ bs ++ cs ++ tail := by
    rw [has, hbs, hcs, htail]
    simp only [List.append_assoc, List.take_append_drop]
  have hasl : as.length = n := by rw [has, List.length_take]; omega
  have hbsl : bs.length = n2 := by rw [hbs, List.length_take, List.length_drop]; omega
  have hcsl : cs.length = n3 := by
    rw [hcs, List.length_take, List.length_drop, List.length_drop]; omega
  have hprefix : as ++ bs ++ cs = es.take (n + n2 + n3) := by
    rw [hsplit]
    have e1 : (as ++ bs ++ cs).length = n + n2 + n3 := by
      rw [List.length_append, List.length_append, hasl, hbsl, hcsl]
    rw [← e1, List.take_left]
  have he : as ++ bs ++ cs = GalilScaffoldAdvanceClock.advances 2048 clock
      ((av.take (n + n2 + n3)).map (fun b => (b, true))) := by
    rw [hprefix, hes, List.map_take, GalilScaffoldAdvanceClock.advances_take]
  obtain ⟨u, p, used, rest', t, dpv, hdr, hqu, hp, hpm, hcsplit, hq, hnr, hres, _⟩ :=
    later_stage_chain as bs cs _ v0.toPrep k clock a ls rs qq gap cen hcen c hc
      hm0 (by rw [toPrep_work, hw0, hasl]) hs0 hcanon hd (by rw [hasl]; exact ha)
      (by rw [hasl]; exact hn) (by rw [hasl]; exact hl) (by rw [hbsl, hasl, ← hn2])
      (by rw [hcsl, hasl, ← hn3]) hclock he
  rw [hasl] at hres
  -- the actual run through the phases
  rw [hsplit] at hrun
  rw [List.append_assoc, List.append_assoc] at hrun
  obtain ⟨v1, hrun1, hrun'⟩ := searchRun_split _ as hrun
  obtain ⟨v2, hrun2, hrun''⟩ := searchRun_split _ bs hrun'
  rw [hcsplit, List.append_assoc] at hrun''
  -- doubling
  obtain ⟨hdr1, hdp1, hl1, hwk1, hm1, hw1⟩ :=
    searchRun_doubling ⟨a :: ls,gap⟩ as hrun1 hm0 (by rw [hw0, hasl])
  have hrs0 : GalilScaffoldStagePrepare.runState v0.toPrep 0 = v0.search := by
    rw [← hq0]; exact runState_toPrep v0
  rw [hrs0] at hdr
  have hu : u = v1.search := double_run_unique hdr hdr1
  subst hu
  -- preparation
  have hx1 : v1.toPrep = GalilScaffoldStagePrepare.restoreState v0.toPrep v1.search :=
    toPrep_restoreState hdp1 hwk1
  obtain ⟨a', bs', hbs'⟩ : ∃ a' bs', bs = a' :: bs' := by
    cases hbs0 : bs with
    | nil => rw [hbs0] at hbsl; simp at hbsl; omega
    | cons a' bs' => exact ⟨a', bs', rfl⟩
  have hrun20 := hrun2
  rw [hbs'] at hp hrun2
  have hw1' : positive v1.search.work = false := by rw [hw1]; rfl
  obtain ⟨hp2, hq2, hl2⟩ :=
    searchRun_prepared_double ⟨a :: ls,gap⟩ hp hrun2 hx1 hm1 hw1' (by rw [hl1, hlow])
  -- the run
  obtain ⟨hsearch2, hdp2⟩ := toPrep_search_eq hp2
  have hsearch2' : v2.search = GalilScaffoldStagePrepare.runState p v1.search.quarter := by
    rw [hsearch2, hq2]
  obtain ⟨v3, hrun3, hs3, hx3, _, _, hrest⟩ := searchRun_quanta _ hq hrun'' hsearch2' hdp2
  have hp2m : v2.search.mode = .run := by rw [← toPrep_mode, hp2]; exact hpm
  have hq' : GalilScaffoldSearchRun.SafeQuanta v2.search v2.dp used v3.search v3.dp := by
    rw [hsearch2', hdp2, hs3, hx3]; exact hq
  -- the entry datum of the stage
  have htl : tail = [] := by
    have h := congrArg List.length hsplit
    simp only [List.length_append] at h
    exact List.eq_nil_of_length_eq_zero (by omega)
  have hcseq : used ++ (rest' ++ tail) = cs := by
    rw [htl, List.append_nil, ← hcsplit]
  obtain ⟨hdprog, hmoderun, hcanon2, hbound, hbud⟩ :=
    laterStage_dpEntry a ls gap k n clock hrun1 hrun20 hm0 hq0 hw0 hs0 hcanon hd hlow ha hn hl
      hasl (by rw [hbsl, ← hn2]) (by rw [hcsl, ← hn3]) hclock he
  refine ⟨as, bs, used, rest' ++ tail, v1, v2, v3, ?_, hasl, by rw [hbsl, ← hn2], ?_, hrun1, ?_,
    hrun3, hrest, hp2m, hq', ?_, ⟨dpv, hx3, hres⟩, hdprog, hcanon2, ?_, ?_⟩
  · rw [hsplit, hcsplit]; simp [List.append_assoc]
  · rw [hcseq, hcsl, ← hn3]
  · rw [hbs']; exact hrun2
  · rw [hs3]; exact hnr
  · rw [hcseq]; exact hbound
  · rw [hcseq]; exact hbud
#print axioms search_later_stage'

end PalPeg.GalilScaffoldChainInputSupply
