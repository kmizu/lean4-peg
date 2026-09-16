import PalPeg.GalilSearchReadyInv

/-!
# Discharging `RunEntries` for a calibrated stage

`PalPeg/GalilSearchReadyInv.lean` leaves exactly one named hypothesis,
`RunEntries center es v`: at every tick of the stage at which the search
*enters* the DP run (`u.search.mode ≠ .run`, `u'.search.mode = .run`), the
entry datum `DpSafeRem u' ds` of `dpSafeRem_entry` holds for the events `ds`
still ahead — i.e. `u'.dp = ⟨GalilScaffoldPreload.initial w lower, false⟩`
for the stage window `w`, with `3186*w.length+1683 ≤ 64*ds.length` and
`ds.count true ≤ value u'.search.debt`.

This file discharges it for the calibrated **first** stage.  Two things have
to be produced:

* **the entry datum itself** (`firstStage_dpEntry`) — the preload identity of
  the handed-over program comes from `prepare_complete` through
  `prepared_interleave` / `searchRun_prepared`, the budget from
  `GalilScaffoldTimingCost.runBudget_sufficient`, and the debt bound from
  `GalilScaffoldAdvanceClock.first_stage_barrier`;
* **the uniqueness of the entry tick** (`runEntries_of_stage`) — a mode
  classification along the stage (`stage_mode_at`): `grow` on the grow ticks,
  a preparation mode strictly inside the preparation, `run` from the handover
  to the end of the quantum.

The classification stops at the end of the first quantum, so the reduction
needs the stage to halt in an *inert* mode (`Terminal`: `idle`/`found`/
`missed`), in which `searchStep` is the identity and no second entry can
occur.  **The remaining gap** is exactly the `wait`/`double` exit: when the
first quantum ends in `wait` or `double`, the events after it can start a
*second* stage inside the same `es`, and that second entry needs the
`search_later_stage` analogue of `firstStage_dpEntry`, which
`PalPeg/GalilSearchResult.lean` does not expose (`search_later_stage` yields
`SafeQuanta v2.search v2.dp usedQ …` but neither
`v2.dp = ⟨GalilScaffoldPreload.initial w k, false⟩`, nor
`Canonical v2.search.debt`, nor the debt bound on the remaining events).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PalPeg.GalilSearchReadyInv

open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilBranchInvariants2
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-! ## Inert modes are absorbing -/

/-- The three inert modes of `searchStep`. -/
def Terminal (m : GalilScaffoldSearchFinish.Mode) : Prop :=
  m = .idle ∨ m = .found ∨ m = .missed

theorem searchStep_terminal {center : GalilScaffoldPlace.Place} {a : Bool} {v v' : SearchVM}
    (h : searchStep center a v v') (hm : Terminal v.search.mode) : v' = v := by
  unfold searchStep at h
  rcases hm with hm | hm | hm <;> rw [hm] at h <;> exact h

theorem searchRun_terminal {center : GalilScaffoldPlace.Place} {es : List Bool} :
    ∀ {v v' : SearchVM}, SearchRun center es v v' → Terminal v.search.mode → v' = v := by
  induction es with
  | nil => intro v v' h _; cases h; rfl
  | cons a es ih =>
    intro v v'' h hm
    cases h with
    | cons hstep hrest =>
      rename_i w
      have h1 : w = v := searchStep_terminal hstep hm
      subst h1
      exact ih hrest hm

/-! ## The mode classification along a stage -/

/-- Where the search is at every prefix of the first stage: before the
handover (`j < |as|+|bs|`) it is never in `run`; from the handover to the end
of the quantum it always is. -/
theorem stage_mode_at (center : GalilScaffoldPlace.Place) (k : ℕ)
    {as bs usedQ : List Bool} {v0 v1 v2 v3 : SearchVM}
    (h1 : SearchRun center as v0 v1) (h2 : SearchRun center bs v1 v2)
    (hm0 : v0.search.mode = .grow) (hw0 : v0.search.work = ofNat as.length)
    (hp : GalilScaffoldPreparePaced.PacedPrepared (ofNat k) center v1.toPrep bs v2.toPrep)
    (hm1 : v1.search.mode = .grow) (hw1 : positive v1.search.work = false)
    (hl1 : v1.lower = ofNat k)
    (hq : GalilScaffoldSearchRun.SafeQuanta v2.search v2.dp usedQ v3.search v3.dp) :
    ∀ (j : ℕ) (v : SearchVM), SearchRun center ((as ++ bs ++ usedQ).take j) v0 v →
      (j < as.length + bs.length → v.search.mode ≠ .run) ∧
      (as.length + bs.length ≤ j → j < as.length + bs.length + usedQ.length →
        v.search.mode = .run) := by
  intro j v hv
  obtain ⟨a', bs', hbs⟩ : ∃ a' bs', bs = a' :: bs' := by
    cases hb0 : bs with
    | nil => rw [hb0] at hp; cases hp
    | cons a' bs' => exact ⟨a', bs', rfl⟩
  by_cases hj1 : j ≤ as.length
  · -- the grow ticks
    have hes1' : (as ++ bs ++ usedQ).take j = as.take j := by
      rw [List.append_assoc, List.take_append_of_le_length hj1]
    rw [hes1'] at hv
    obtain ⟨hg, _⟩ := searchRun_grow_prefix center (as.take j) as.length hv hm0 hw0
      (by rw [List.length_take]; omega)
    refine ⟨fun _ => by rw [hg]; decide, fun hge _ => ?_⟩
    exfalso
    rw [hbs] at hge
    simp only [List.length_cons] at hge
    omega
  · by_cases hj2 : j < as.length + bs.length
    · -- strictly inside the preparation
      have hj1' := Nat.lt_of_not_le hj1
      have hes1' : (as ++ bs ++ usedQ).take j = as ++ bs.take (j - as.length) := by
        rw [List.take_append_of_le_length (by rw [List.length_append]; omega),
          List.take_append, List.take_of_length_le (by omega)]
      rw [hes1'] at hv
      obtain ⟨vm1, hv1, hv'⟩ := searchRun_split _ as hv
      rw [searchRun_unique hv1 h1] at hv'
      obtain ⟨i, hi⟩ : ∃ i, j - as.length = i + 1 := ⟨j - as.length - 1, by omega⟩
      rw [hi, hbs, List.take_succ_cons] at hv'
      cases hv' with
      | cons hstep hrest =>
        rename_i v1'
        have hv1' : v1' = SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a'
            (GalilScaffoldPrepareControl.prepare v1.toPrep v1.lower center)) v1.search.quarter
            v1.lower := by
          unfold searchStep at hstep
          rw [hm1] at hstep
          simp only [hw1, Bool.false_eq_true, if_false] at hstep
          exact hstep
        have hx1 : v1'.toPrep = GalilScaffoldPreparePaced.afterAdvance a'
            (GalilScaffoldPrepareControl.prepare v1.toPrep (ofNat k) center) := by
          rw [hv1', toPrep_ofPrep, hl1]
        rw [hbs] at hp
        cases hp with
        | intro _ _ _ hrun =>
          have hsplitb : bs' = bs'.take i ++ bs'.drop i := (List.take_append_drop i bs').symm
          rw [hsplitb] at hrun
          obtain ⟨y, hy1, hy2⟩ := pacedPrepared_split _ _ hrun
          have hpref : SearchRun center
              (((List.replicate (bs'.take i).length true).zip (bs'.take i)).map Prod.snd) v1' v := by
            rw [map_snd_zip_replicate]; exact hrest
          obtain ⟨hvy, _, _⟩ := searchRun_paced center (all_enabled_zip _) hy1 hpref hx1
          have hi2 : i < bs'.length := by
            rw [hbs] at hj2
            simp only [List.length_cons] at hj2
            omega
          have hdne : bs'.drop i ≠ [] := by
            intro h0
            have hlen0 := congrArg List.length h0
            rw [List.length_drop] at hlen0
            simp only [List.length_nil] at hlen0
            omega
          obtain ⟨e, es', hd⟩ : ∃ e es', bs'.drop i = e :: es' := by
            cases hd0 : bs'.drop i with
            | nil => exact absurd hd0 hdne
            | cons e es' => exact ⟨e, es', rfl⟩
          rw [hd] at hy2
          simp only [List.length_cons, List.replicate_succ, List.zip_cons_cons] at hy2
          have hpm := pacedRun_cons_prepMode rfl hy2
          rw [← hvy, toPrep_mode] at hpm
          refine ⟨fun _ => ?_, fun hge _ => absurd hge (by omega)⟩
          rcases hpm with hpm | hpm | hpm | hpm <;> rw [hpm] <;> decide
    · -- the run quanta
      have hj2' : as.length + bs.length ≤ j := Nat.le_of_not_lt hj2
      have hes1' : (as ++ bs ++ usedQ).take j =
          as ++ bs ++ usedQ.take (j - (as.length + bs.length)) := by
        rw [List.take_append, List.take_of_length_le (by rw [List.length_append]; omega),
          List.length_append]
      rw [hes1', List.append_assoc] at hv
      obtain ⟨vm1, hv1, hv'⟩ := searchRun_split _ as hv
      rw [searchRun_unique hv1 h1] at hv'
      obtain ⟨vm2, hv2, hv''⟩ := searchRun_split _ bs hv'
      rw [searchRun_unique hv2 h2] at hv''
      refine ⟨fun hlt => absurd hj2' (by omega), fun _ hlt => ?_⟩
      obtain ⟨i, hi⟩ : ∃ i, j - (as.length + bs.length) = i := ⟨_, rfl⟩
      rw [hi] at hv''
      have hdne : usedQ.drop i ≠ [] := by
        intro h0
        have hlen0 := congrArg List.length h0
        rw [List.length_drop] at hlen0
        simp only [List.length_nil] at hlen0
        omega
      have hq' : GalilScaffoldSearchRun.SafeQuanta v2.search v2.dp
          (usedQ.take i ++ usedQ.drop i) v3.search v3.dp := by
        rw [List.take_append_drop]; exact hq
      obtain ⟨m, y', hqm, hmm⟩ := safeQuanta_prefix_run _ _ hdne hq'
      have hv''' : SearchRun center (usedQ.take i ++ []) v2 v := by
        rw [List.append_nil]; exact hv''
      obtain ⟨vq, _, hsq, _, _, _, hnil⟩ := searchRun_quanta center hqm hv''' rfl rfl
      cases hnil
      rw [hsq]
      exact hmm

/-! ## The reduction -/

/-- **The reduction.**  With the entry datum at the handover and an inert exit
mode, the handover is the *only* tick of `es` that enters the DP run, so
`RunEntries` holds. -/
theorem runEntries_of_stage (center : GalilScaffoldPlace.Place) (k : ℕ)
    {as bs usedQ rest es : List Bool} {v0 v1 v2 v3 : SearchVM}
    (hes : es = as ++ bs ++ usedQ ++ rest)
    (h1 : SearchRun center as v0 v1) (h2 : SearchRun center bs v1 v2)
    (h3 : SearchRun center usedQ v2 v3)
    (hm0 : v0.search.mode = .grow) (hw0 : v0.search.work = ofNat as.length)
    (hp : GalilScaffoldPreparePaced.PacedPrepared (ofNat k) center v1.toPrep bs v2.toPrep)
    (hm1 : v1.search.mode = .grow) (hw1 : positive v1.search.work = false)
    (hl1 : v1.lower = ofNat k)
    (hq : GalilScaffoldSearchRun.SafeQuanta v2.search v2.dp usedQ v3.search v3.dp)
    (hm3 : v3.search.mode ≠ .run)
    (hterm : Terminal v3.search.mode)
    (hentry : DpSafeRem v2 (usedQ ++ rest)) :
    RunEntries center es v0 := by
  classical
  have hclass := stage_mode_at center k h1 h2 hm0 hw0 hp hm1 hw1 hl1 hq
  have hstage : as ++ bs ++ usedQ = es.take (as.length + bs.length + usedQ.length) := by
    have e1 : as.length + bs.length + usedQ.length = (as ++ bs ++ usedQ).length := by
      simp only [List.length_append]
    rw [hes, e1, List.take_left]
  intro cs ds b u u' heq hru hstep hnr hrr
  have hsplit2 : es = (cs ++ [b]) ++ ds := by rw [heq]; simp
  have hlb : cs.length + 1 = (cs ++ [b]).length := by simp
  have hcs : cs = es.take cs.length := by rw [heq, List.take_left]
  have hcsb : cs ++ [b] = es.take (cs.length + 1) := by rw [hsplit2, hlb, List.take_left]
  have hdrop : es.drop (cs.length + 1) = ds := by rw [hsplit2, hlb, List.drop_left]
  have hu' : SearchRun center (cs ++ [b]) v0 u' := searchRun_append hru (.cons hstep (.nil _))
  by_cases hjT : cs.length + 1 ≤ as.length + bs.length + usedQ.length
  · -- inside the classified region
    have hpref1 : cs = (as ++ bs ++ usedQ).take cs.length := by
      rw [hstage, List.take_take, Nat.min_eq_left (by omega)]
      exact hcs
    have hpref2 : cs ++ [b] = (as ++ bs ++ usedQ).take (cs.length + 1) := by
      rw [hstage, List.take_take, Nat.min_eq_left (by omega)]
      exact hcsb
    have hA := hclass cs.length u (by rw [← hpref1]; exact hru)
    have hB := hclass (cs.length + 1) u' (by rw [← hpref2]; exact hu')
    have hge : as.length + bs.length ≤ cs.length + 1 := by
      by_contra hcon
      exact hB.1 (by omega) hrr
    have hlt : cs.length < as.length + bs.length := by
      by_contra hcon
      exact hnr (hA.2 (by omega) (by omega))
    have heqj : cs.length + 1 = as.length + bs.length := by omega
    have hab : cs ++ [b] = as ++ bs := by
      rw [hpref2, heqj, show as.length + bs.length = (as ++ bs).length by simp, List.take_left]
    have hrun_ab : SearchRun center (as ++ bs) v0 v2 := searchRun_append h1 h2
    have hv2 : u' = v2 := by
      rw [hab] at hu'
      exact searchRun_unique hu' hrun_ab
    have hds : ds = usedQ ++ rest := by
      have hd2 : es.drop (as.length + bs.length) = usedQ ++ rest := by
        have e1 : as ++ bs ++ usedQ ++ rest = (as ++ bs) ++ (usedQ ++ rest) := by
          simp [List.append_assoc]
        have e2 : as.length + bs.length = (as ++ bs).length := by simp
        rw [hes, e1, e2, List.drop_left]
      rw [← hdrop, heqj, hd2]
    rw [hv2, hds]
    exact hentry
  · -- after the quantum: the inert tail
    exfalso
    have hcs' : cs = (as ++ bs ++ usedQ) ++ rest.take (cs.length - (as ++ bs ++ usedQ).length) := by
      have h0 : es.take cs.length =
          (as ++ bs ++ usedQ) ++ rest.take (cs.length - (as ++ bs ++ usedQ).length) := by
        rw [hes, List.take_append,
          List.take_of_length_le (by simp only [List.length_append]; omega)]
      rw [← h0]
      exact hcs
    rw [hcs'] at hru
    obtain ⟨vm, hvm1, hvm2⟩ := searchRun_split _ (as ++ bs ++ usedQ) hru
    have hvm : vm = v3 := searchRun_unique hvm1 (searchRun_append (searchRun_append h1 h2) h3)
    rw [hvm] at hvm2
    have hu : u = v3 := searchRun_terminal hvm2 hterm
    rw [hu] at hstep
    have hu2 : u' = v3 := searchStep_terminal hstep hterm
    rw [hu2] at hrr
    exact hm3 hrr

/-! ## The entry datum of a calibrated first stage -/

/-- **The entry datum.**  At the handover of a calibrated first stage the DP
machine is the preload of the stage window, the debt is canonical, and the
events left in the stage both pay for the DP run and fit the calibrated
budget — i.e. `DpSafeRem` holds there. -/
theorem firstStage_dpEntry (a : Fin 2) (ls : List (Fin 2)) (gap : Bool)
    (lower radius : Counter) (hlc : Canonical lower) (k : ℕ) (hk : value lower = k)
    (hrc : Canonical radius) (rad : ℕ) (hrad : value radius = rad) (hr : 3*rad ≤ 5*k)
    {v0 v1 v2 : SearchVM} {as bs cs : List Bool}
    (h1 : SearchRun ⟨a :: ls, gap⟩ as v0 v1) (h2 : SearchRun ⟨a :: ls, gap⟩ bs v1 v2)
    (hsearch : v0.search = GalilScaffoldSearchFinish.begin lower radius)
    (hlower : v0.lower = lower)
    (ha : as.length = max k 1)
    (hb : bs.length =
      2*k + 2*((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (8*max k 1+1)).length + 7)
    (hcsl : cs.length = GalilScaffoldTimingCost.runBudget (8*max k 1))
    {ev : List (Bool × Bool)}
    (he : as ++ bs ++ cs = GalilScaffoldAdvanceClock.advances 2048 2048 ev) :
    DpSafeRem v2 cs := by
  obtain ⟨a'', bs'', hbs⟩ : ∃ a'' bs'', bs = a'' :: bs'' := by
    cases hb0 : bs with
    | nil => rw [hb0] at hb; simp only [List.length_nil] at hb; omega
    | cons a'' bs'' => exact ⟨a'', bs'', rfl⟩
  subst hbs
  have hlk : lower = ofNat k := GalilScaffoldChainCatch.canonical_nat lower hlc k hk
  obtain ⟨hm, hw, hs, hd, hcanon⟩ := begin_entry lower radius hlc k hk hrc rad hrad
  have hmode0 : v0.search.mode = .grow := by rw [hsearch]; exact hm
  have hw0 : v0.search.work = ofNat as.length := by rw [hsearch, ha]; exact hw
  have hm0 : v0.toPrep.mode = .grow := by rw [toPrep_mode]; exact hmode0
  have hs0 : v0.toPrep.span = ofNat 0 := by
    show v0.search.span = _
    rw [hsearch]; exact hs
  have hd0 : value v0.toPrep.debt = -(rad : ℤ) := by
    show value v0.search.debt = _
    rw [hsearch]; exact hd
  have hc0 : Canonical v0.toPrep.debt := by
    show Canonical v0.search.debt
    rw [hsearch]; exact hcanon
  -- the grow phase
  obtain ⟨hg1, hq1, hl1, hm1, hw1⟩ := searchRun_growing _ as h1 hmode0 hw0
  obtain ⟨u, hg, hum, huw, hus, hud⟩ :=
    GalilScaffoldStagePrepare.paced_growing_complete as v0.toPrep 0 hm0
      (by rw [toPrep_work]; exact hw0) hs0
  have hu : v1.toPrep = u := pacedGrowing_unique hg1 hg
  have hus' : u.span = ofNat (8*max k 1) := by rw [hus, ha]; simp
  -- the preparation phase
  obtain ⟨p, hp, hpm, hpp, hpd, hpdebt, hpf⟩ :=
    GalilScaffoldPrepareControl.prepare_complete u k (8*max k 1) ⟨a :: ls, gap⟩ hus'
  have hprep : GalilScaffoldPreparePaced.PacedPrepared (ofNat k) ⟨a :: ls, gap⟩ u (a'' :: bs'')
      {p with debt := GalilScaffoldPreparePaced.spend (a'' :: bs'') u.debt} :=
    GalilScaffoldPreparePaced.prepared_interleave hp (a'' :: bs'') hb
  have hw1' : positive v1.search.work = false := by simp [hw1, positive_ofNat]
  have hv2 : v2.toPrep =
      {p with debt := GalilScaffoldPreparePaced.spend (a'' :: bs'') u.debt} :=
    (searchRun_prepared _ hprep h2 hu hm1 hw1' (by rw [hl1, hlower, hlk])).1
  -- the handover datum
  have hdprog : v2.dp =
      ⟨GalilScaffoldPreload.initial
        ((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (8*max k 1+1)) k, false⟩ := by
    show v2.toPrep.program = _
    rw [hv2]
    show p.program = _
    calc p.program = ⟨p.program.config, p.program.done⟩ := rfl
      _ = _ := by rw [hpp, hpd]
  have hmoderun : v2.search.mode = .run := by rw [← toPrep_mode, hv2]; exact hpm
  have hdebt2 : v2.search.debt = GalilScaffoldPreparePaced.spend (a'' :: bs'') u.debt := by
    show v2.toPrep.debt = _
    rw [hv2]
  have hcanon2 : Canonical v2.search.debt := by
    rw [hdebt2]
    exact GalilScaffoldPreparePaced.spend_canonical _ u.debt
      (GalilScaffoldStagePrepare.paced_growing_canonical hg hc0)
  rw [hd0, ha] at hud
  have hvalue2 : value v2.search.debt =
      -(rad : ℤ) + 2*(max k 1 : ℕ) - (as ++ a'' :: bs'').count true := by
    rw [hdebt2, GalilScaffoldPreparePaced.spend_value]
    simp only [List.count_append, Nat.cast_add]
    omega
  -- the calibrated budget and the debt barrier
  have hwl : ((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (8*max k 1+1)).length
      ≤ 8*max k 1+1 := List.length_take_le _ _
  have hlen_ev : ev.length = as.length + (a'' :: bs'').length + cs.length := by
    have h := congrArg List.length he
    rw [GalilScaffoldAdvanceClock.advances_length] at h
    rw [← h, List.length_append, List.length_append]
  have htime : ev.length ≤ 63*(8*max k 1) := by
    rw [hlen_ev, ha, hb, hcsl]
    have h := GalilScaffoldTimingCost.first_stage_ticks k
      ((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (8*max k 1+1)).length hwl
    omega
  have hbar := GalilScaffoldAdvanceClock.first_stage_barrier k rad ev hr htime
  have hcount := congrArg (List.count true) he
  simp only [List.count_append] at hcount
  have hbound : ((cs.count true : ℤ)) ≤ value v2.search.debt := by
    rw [hvalue2]
    simp only [List.count_append, Nat.cast_add]
    omega
  have hbud : 3186*((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (8*max k 1+1)).length + 1683
      ≤ 64*cs.length := by
    have h := GalilScaffoldTimingCost.runBudget_sufficient (8*max k 1)
    rw [hcsl]
    omega
  exact dpSafeRem_entry v2 _ k cs hdprog hmoderun hbud hcanon2 hbound

/-! ## `RunEntries` for the calibrated first stage -/

/-- **The main statement.**  For a `SearchRun` starting at a `Restarted`
state (`v0.search = GalilScaffoldSearchFinish.begin lower radius`) whose event
list is the clocked stream `advances 2048 2048 (av.map (·, true))` of exactly
the calibrated stage length
`max k 1 + (2*k + 2*w.length + 7) + runBudget (8*max k 1)` (`w` the stage
window), the stage decomposes as `as ++ bs ++ usedQ ++ rest`, the entry datum
`DpSafeRem v2 (usedQ ++ rest)` holds at the handover, and — provided the
quantum exits in an inert mode — `RunEntries` holds for the whole of `es`. -/
theorem runEntries_of_calibrated (a : Fin 2) (ls rs qq : List (Fin 2)) (gap : Bool)
    (cen : PlaceHead) (hcen : cen = represent ⟨a :: ls, gap⟩ (rs.map some) qq)
    (c : Fin 3) (hc : GalilScaffoldPlace.read ⟨a :: ls, gap⟩ = some c)
    (lower radius : Counter) (hlc : Canonical lower) (k : ℕ) (hk : value lower = k)
    (hrc : Canonical radius) (rad : ℕ) (hrad : value radius = rad) (hr : 3*rad ≤ 5*k)
    {v0 v' : SearchVM} {es : List Bool} (hrun : SearchRun ⟨a :: ls, gap⟩ es v0 v')
    (hsearch : v0.search = GalilScaffoldSearchFinish.begin lower radius)
    (hlower : v0.lower = lower)
    {av : List Bool} (hav : av.length = es.length)
    (hes : es = GalilScaffoldAdvanceClock.advances 2048 2048 (av.map (fun b => (b, true))))
    (hlen : es.length = max k 1
      + (2*k + 2*((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (8*max k 1+1)).length + 7)
      + GalilScaffoldTimingCost.runBudget (8*max k 1)) :
    ∃ (as bs usedQ rest : List Bool) (v1 v2 v3 : SearchVM),
      es = as ++ bs ++ usedQ ++ rest ∧
      SearchRun ⟨a :: ls, gap⟩ as v0 v1 ∧ SearchRun ⟨a :: ls, gap⟩ bs v1 v2 ∧
      SearchRun ⟨a :: ls, gap⟩ usedQ v2 v3 ∧ SearchRun ⟨a :: ls, gap⟩ rest v3 v' ∧
      v2.search.mode = .run ∧ v3.search.mode ≠ .run ∧
      DpSafeRem v2 (usedQ ++ rest) ∧
      (Terminal v3.search.mode → RunEntries ⟨a :: ls, gap⟩ es v0) := by
  obtain ⟨as, bs, usedQ, rest, v1, v2, v3, hsplit, hal, hbl, h1, h2, h3, hrest, hm0, hw0,
      hp, hm1, hw1, hl1, hm2, hq, hm3, _, _, _⟩ :=
    search_first_stage a ls rs qq gap cen hcen c hc lower radius hlc k hk hrc rad hrad hr
      hrun hsearch hlower hav hes (by omega)
  have hlensum : es.length = as.length + bs.length + (usedQ ++ rest).length := by
    rw [hsplit]; simp only [List.length_append]; omega
  have hcsl : (usedQ ++ rest).length = GalilScaffoldTimingCost.runBudget (8*max k 1) := by
    rw [hal, hbl] at hlensum; omega
  have he : as ++ bs ++ (usedQ ++ rest) =
      GalilScaffoldAdvanceClock.advances 2048 2048 (av.map (fun b => (b, true))) := by
    rw [← hes, hsplit]; simp [List.append_assoc]
  have hentry : DpSafeRem v2 (usedQ ++ rest) :=
    firstStage_dpEntry a ls gap lower radius hlc k hk hrc rad hrad hr h1 h2 hsearch hlower
      hal hbl hcsl he
  exact ⟨as, bs, usedQ, rest, v1, v2, v3, hsplit, h1, h2, h3, hrest, hm2, hm3, hentry,
    fun hterm =>
      runEntries_of_stage _ k hsplit h1 h2 h3 hm0 hw0 hp hm1 hw1 hl1 hq hm3 hterm hentry⟩

#print axioms searchStep_terminal
#print axioms searchRun_terminal
#print axioms stage_mode_at
#print axioms runEntries_of_stage
#print axioms firstStage_dpEntry
#print axioms runEntries_of_calibrated

end PalPeg.GalilSearchReadyInv
