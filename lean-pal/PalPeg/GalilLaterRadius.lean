import PalPeg.GalilSearchWait
import PalPeg.GalilFoundRadiusBound
import PalPeg.GalilRestartStage

/-!
# The found radius at every search stage

Closes the three gaps of `PalPeg/GalilFoundRadiusBound.lean`.

* **Debt balance instead of stage time.**  The stages are re-aligned on the
  actual run through `first_stage_safe` / `later_stage_safe`, whose exit debt
  is exported: `debt = -rad + 2*max k 1 - matches` (first stage),
  `4*debt = 4*d0 + n - 4*matches` (later stage entered with debt `d0`, work
  `n`), and `0 ≤ debt`.  A `wait` exit burns exactly the debt (`wait_split`),
  the boundary tick leaves `-[b]` (`waiting_debt`); a `double` exit hands its
  debt on.  So the matches telescope: from a later entry,
  `4*matches + n ≤ 4*d0 + 2*n'` up to the found tick of window `2n'`
  (`later_found`, induction on the event list); from the restart,
  `rad + matches ≤ 2*max k 1` (found in the first stage) or
  `2*(rad + matches) ≤ n'` (`first_found`).
* **`hprev`.**  Each non-`found` exit gives `pc = 347` on its window
  (`exit_failure`), and the next stage's work is that window (`span` kept by
  the quanta on `wait`, moved to `work` on `double`).
* **`htime`.**  For a `found` in the first stage the tick is inside
  `as ++ bs ++ usedQ`, whose length is `≤ 63*(8*max k 1)` (`first_stage_aligned`).

`found_radius_le_all_stages` assembles this at the tick, with the hypotheses of
`found_radius_le` minus `htime` and without the escape disjunct.
-/

set_option autoImplicit false
namespace PalPeg.GalilLaterRadius

open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilSearchReadyInv
open PalPeg.GalilSearchWait
open GalilScaffoldCounter
open GalilScaffoldTop GalilScaffoldController GalilScaffoldInputHead

/-! ## 1. Splitting a wait at its burn -/

theorem wait_split (center : GalilScaffoldPlace.Place) :
    ∀ (L : List Bool) (v v' : SearchVM), SearchRun center L v v' →
      v.search.mode = .wait → Canonical v.search.debt → v'.search.mode ≠ .wait →
      ∃ (ws : List Bool) (b : Bool) (L' : List Bool), L = ws ++ b :: L' ∧
        value v.search.debt = ws.count true ∧ BurnEvents ws := by
  intro L
  induction L with
  | nil =>
    intro v v' h hm _ hne
    cases h
    exact absurd hm hne
  | cons a L ih =>
    intro v v' h hm hc hne
    cases hz : zero v.search.debt with
    | true =>
      refine ⟨[], a, L, rfl, by simpa using (zero_iff v.search.debt hc).mp hz, ?_⟩
      intro p hp hpne
      exact absurd (List.prefix_nil.mp hp) hpne
    | false =>
      cases h with
      | cons hstep hrest =>
        rename_i v1
        have hv1 : v1 = waitNext a v := wait_searchStep_eq hm hstep
        subst hv1
        have hm1 := waitNext_mode a v hm hz
        have hc1 := waitNext_canonical a v hm hz hc
        have hd1 := waitNext_debt a v hm hz
        obtain ⟨ws, b, L', hL, hv, hb⟩ := ih _ _ hrest hm1 hc1 hne
        have hne0 : value v.search.debt ≠ 0 := by
          intro h0
          have := (zero_iff v.search.debt hc).mpr h0
          rw [hz] at this; exact absurd this (by decide)
        have hval : value v.search.debt = ((a :: ws).count true : ℤ) := by
          rw [hv] at hd1
          cases a <;> simp at hd1 ⊢ <;> omega
        refine ⟨a :: ws, b, L', by rw [hL]; rfl, hval, ?_⟩
        intro p hp hpne
        cases p with
        | nil =>
          have h2 : ((a :: ws).count true : ℤ) ≠ 0 := by rw [← hval]; exact hne0
          have : (a :: ws).count true ≠ 0 := by exact_mod_cast h2
          simp only [List.count_nil]
          omega
        | cons c p' =>
          obtain ⟨hca, hp'⟩ := List.cons_prefix_cons.mp hp
          subst hca
          have hne' : p' ≠ ws := fun he => hpne (by rw [he])
          have := hb p' hp' hne'
          simp only [List.count_cons]
          omega

#print axioms wait_split

/-! ## 2. Splitting clocked event lists -/

theorem advances_split (clock : ℕ) (av L1 L2 : List Bool)
    (h : L1 ++ L2 = GalilScaffoldAdvanceClock.advances 2048 clock (av.map (fun b => (b, true)))) :
    L1 = GalilScaffoldAdvanceClock.advances 2048 clock ((av.take L1.length).map (fun b => (b, true))) ∧
    L2 = GalilScaffoldAdvanceClock.advances 2048
      (GalilScaffoldMatchClock.run 2048 clock (av.take L1.length)).1
      ((av.drop L1.length).map (fun b => (b, true))) := by
  have hlen := congrArg List.length h
  rw [GalilScaffoldAdvanceClock.advances_length, List.length_map, List.length_append] at hlen
  have e : av = av.take L1.length ++ av.drop L1.length := (List.take_append_drop _ _).symm
  rw [e, List.map_append, GalilScaffoldAdvanceClock.advances_append, map_fst_map_pair] at h
  have hl : L1.length = (GalilScaffoldAdvanceClock.advances 2048 clock
      ((av.take L1.length).map (fun b => (b, true)))).length := by
    rw [GalilScaffoldAdvanceClock.advances_length, List.length_map, List.length_take]; omega
  obtain ⟨h1, h2⟩ := List.append_inj h hl
  exact ⟨h1, h2⟩

theorem advances_cons_head (clock : ℕ) (b : Bool) (L av : List Bool)
    (h : b :: L = GalilScaffoldAdvanceClock.advances 2048 clock (av.map (fun b => (b, true)))) :
    ∃ x av', av = x :: av' ∧ b = (x && decide (clock = 1) && true) ∧
      L = GalilScaffoldAdvanceClock.advances 2048 (GalilScaffoldMatchClock.run 2048 clock [x]).1
        (av'.map (fun b => (b, true))) := by
  cases av with
  | nil => simp [GalilScaffoldAdvanceClock.advances] at h
  | cons x av' =>
    simp only [List.map_cons, GalilScaffoldAdvanceClock.advances, List.cons.injEq] at h
    refine ⟨x, av', rfl, h.1, ?_⟩
    rw [h.2]
    congr 1
    cases x <;> by_cases hc : clock = 1 <;> simp [GalilScaffoldMatchClock.run, hc]

#print axioms advances_split
#print axioms advances_cons_head

/-! ## 3. A later stage on the actual run, with its debt balance -/

/-- `search_later_stage` rebuilt on `later_stage_safe`, so that the exit debt
balance, the run-entry span and the lower bound are exported. -/
theorem later_stage_aligned (center : GalilScaffoldPlace.Place) (k n clock : ℕ)
    {v0 v' : SearchVM} {es : List Bool} (hrun : SearchRun center es v0 v')
    (hm0 : v0.search.mode = .double) (hq0 : v0.search.quarter = 0)
    (hw0 : v0.search.work = ofNat n) (hs0 : v0.search.span = ofNat 0)
    (hcanon : Canonical v0.search.debt)
    (hd : 0 ≤ value v0.search.debt ∨ (-1 ≤ value v0.search.debt ∧ clock = 2048))
    (hlow : v0.lower = ofNat k)
    (ha : n % 4 = 0) (hn : 8 ≤ n) (hl : 4*k ≤ n)
    {av : List Bool}
    (hes : es = GalilScaffoldAdvanceClock.advances 2048 clock (av.map (fun b => (b, true))))
    (hclock : 1 ≤ clock ∧ clock ≤ 2048)
    (hlen : es.length = n + (2*k + 2*((GalilScaffoldPlace.stream center).take (2*n+1)).length + 7)
      + GalilScaffoldTimingCost.runBudget (2*n)) :
    ∃ (as bs used rest : List Bool) (v2 v3 : SearchVM),
      es = as ++ bs ++ used ++ rest ∧ as.length = n ∧
      SearchRun center (as ++ bs) v0 v2 ∧ SearchRun center used v2 v3 ∧ SearchRun center rest v3 v' ∧
      v2.search.mode = .run ∧
      GalilScaffoldSearchRun.SafeQuanta v2.search v2.dp used v3.search v3.dp ∧
      v3.search.mode ≠ .run ∧
      (∃ dpv, v3.dp = ⟨dpv, true⟩ ∧
        GalilDpCorrect.Result ((GalilScaffoldPlace.stream center).take (2*n+1)) k 0
          (GalilScaffoldProgram.denote dpv)) ∧
      4 * value v3.search.debt = 4 * value v0.search.debt + n - 4 * ((as ++ bs ++ used).count true) ∧
      Canonical v3.search.debt ∧ 0 ≤ value v3.search.debt ∧
      v2.search.span = ofNat (2*n) ∧ v3.lower = v0.lower := by
  obtain ⟨n2, hn2⟩ : ∃ m, 2*k + 2*((GalilScaffoldPlace.stream center).take (2*n+1)).length + 7 = m :=
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
  obtain ⟨u, p, used, rest', t, dpv, hdr, hqu, hp, hcsplit, hq, hnr, hres, hdebt, htc, htn⟩ :=
    GalilScaffoldStagePrepare.later_stage_safe as bs cs _ v0.toPrep k clock center
      hm0 (by rw [toPrep_work, hw0, hasl]) hs0 hcanon hd (by rw [hasl]; exact ha)
      (by rw [hasl]; exact hn) (by rw [hasl]; exact hl) (by rw [hbsl, hasl, ← hn2])
      (by rw [hcsl, hasl, ← hn3]) hclock he
  rw [hasl] at hres
  have huspan : (GalilScaffoldStagePrepare.restoreState v0.toPrep u).span = ofNat (2*n) := by
    show u.span = _
    have := GalilScaffoldDouble.span_of_run hdr 0
      (by simp [GalilScaffoldStagePrepare.runState]; exact hs0)
    rw [this, hasl, Nat.zero_add]
  have hpm := (Prep.paced_prepared_mode hp huspan (by rw [hbsl, ← hn2])).1
  -- the actual run through the phases
  rw [hsplit] at hrun
  rw [List.append_assoc, List.append_assoc] at hrun
  obtain ⟨v1, hrun1, hrun'⟩ := searchRun_split _ as hrun
  obtain ⟨v2, hrun2, hrun''⟩ := searchRun_split _ bs hrun'
  rw [hcsplit, List.append_assoc] at hrun''
  obtain ⟨hdr1, hdp1, hl1, hwk1, hm1, hw1⟩ :=
    searchRun_doubling center as hrun1 hm0 (by rw [hw0, hasl])
  have hrs0 : GalilScaffoldStagePrepare.runState v0.toPrep 0 = v0.search := by
    rw [← hq0]; exact runState_toPrep v0
  rw [hrs0] at hdr
  have hu : u = v1.search := double_run_unique hdr hdr1
  subst hu
  have hx1 : v1.toPrep = GalilScaffoldStagePrepare.restoreState v0.toPrep v1.search :=
    toPrep_restoreState hdp1 hwk1
  obtain ⟨a', bs', hbs'⟩ : ∃ a' bs', bs = a' :: bs' := by
    cases hbs0 : bs with
    | nil => rw [hbs0] at hbsl; simp at hbsl; omega
    | cons a' bs' => exact ⟨a', bs', rfl⟩
  have hrun20 := hrun2
  have hp0 := hp
  rw [hbs'] at hp hrun2
  have hw1' : positive v1.search.work = false := by rw [hw1]; rfl
  obtain ⟨hp2, hq2, hl2⟩ :=
    searchRun_prepared_double center hp hrun2 hx1 hm1 hw1' (by rw [hl1, hlow])
  obtain ⟨hsearch2, hdp2⟩ := toPrep_search_eq hp2
  have hsearch2' : v2.search = GalilScaffoldStagePrepare.runState p v1.search.quarter := by
    rw [hsearch2, hq2]
  obtain ⟨v3, hrun3, hs3, hx3, hl3, _, hrest⟩ := searchRun_quanta _ hq hrun'' hsearch2' hdp2
  have hp2m : v2.search.mode = .run := by rw [← toPrep_mode, hp2]; exact hpm
  have hq' : GalilScaffoldSearchRun.SafeQuanta v2.search v2.dp used v3.search v3.dp := by
    rw [hsearch2', hdp2, hs3, hx3]; exact hq
  have hspan2 : v2.search.span = ofNat (2*n) := by
    rw [hsearch2']
    show p.span = _
    exact (GalilScaffoldPreparePaced.prepared_span hp0).trans huspan
  refine ⟨as, bs, used, rest' ++ tail, v2, v3, ?_, hasl, searchRun_append hrun1 hrun20, hrun3, hrest,
    hp2m, hq', by rw [hs3]; exact hnr, ⟨dpv, hx3, hres⟩, ?_, by rw [hs3]; exact htc,
    by rw [hs3]; exact htn, hspan2, by rw [hl3, hl2, hl1]⟩
  · rw [hsplit, hcsplit]; simp [List.append_assoc]
  · rw [hs3, hdebt]
    have : v0.toPrep.debt = v0.search.debt := rfl
    rw [this, hasl]
    omega

#print axioms later_stage_aligned

/-! ## 4. The first stage on the actual run, with its debt balance -/

/-- `search_first_stage` rebuilt on `first_stage_safe`: the exit debt balance
`value debt = -rad + 2*max k 1 - count`, the run-entry span `8*max k 1`, the
lower bound, and the length of the used quantum. -/
theorem first_stage_aligned (center : GalilScaffoldPlace.Place)
    (lower radius : Counter) (hlc : Canonical lower) (k : ℕ) (hk : value lower = k)
    (hrc : Canonical radius) (rad : ℕ) (hrad : value radius = rad) (hr : 3*rad ≤ 5*k)
    {v0 v' : SearchVM} {es : List Bool} (hrun : SearchRun center es v0 v')
    (hsearch : v0.search = GalilScaffoldSearchFinish.begin lower radius) (hlower : v0.lower = lower)
    {av : List Bool}
    (hes : es = GalilScaffoldAdvanceClock.advances 2048 2048 (av.map (fun b => (b, true))))
    (hlen : es.length = max k 1 + (2*k + 2*((GalilScaffoldPlace.stream center).take (8*max k 1+1)).length + 7)
      + GalilScaffoldTimingCost.runBudget (8*max k 1)) :
    ∃ (as bs used rest : List Bool) (v2 v3 : SearchVM),
      es = as ++ bs ++ used ++ rest ∧ as.length = max k 1 ∧
      SearchRun center (as ++ bs) v0 v2 ∧ SearchRun center used v2 v3 ∧ SearchRun center rest v3 v' ∧
      v2.search.mode = .run ∧
      GalilScaffoldSearchRun.SafeQuanta v2.search v2.dp used v3.search v3.dp ∧
      v3.search.mode ≠ .run ∧
      (∃ dpv, v3.dp = ⟨dpv, true⟩ ∧
        GalilDpCorrect.Result ((GalilScaffoldPlace.stream center).take (8*max k 1+1)) k 0
          (GalilScaffoldProgram.denote dpv)) ∧
      value v3.search.debt = -(rad : ℤ) + 2*(max k 1 : ℕ) - (as ++ bs ++ used).count true ∧
      Canonical v3.search.debt ∧ 0 ≤ value v3.search.debt ∧
      v2.search.span = ofNat (8*max k 1) ∧ v3.lower = ofNat k ∧
      (as ++ bs ++ used).length ≤ 63 * (8 * max k 1) := by
  obtain ⟨n1, hn1⟩ : ∃ n, max k 1 = n := ⟨_, rfl⟩
  obtain ⟨n2, hn2⟩ : ∃ n, 2*k + 2*((GalilScaffoldPlace.stream center).take (8*max k 1+1)).length + 7 = n :=
    ⟨_, rfl⟩
  obtain ⟨n3, hn3⟩ : ∃ n, GalilScaffoldTimingCost.runBudget (8*max k 1) = n := ⟨_, rfl⟩
  have htick := GalilScaffoldTimingCost.first_stage_ticks k
    ((GalilScaffoldPlace.stream center).take (8*max k 1+1)).length (List.length_take_le _ _)
  rw [hn3, hn2, hn1] at hlen
  obtain ⟨as, has⟩ : ∃ l, l = es.take n1 := ⟨_, rfl⟩
  obtain ⟨bs, hbs⟩ : ∃ l, l = (es.drop n1).take n2 := ⟨_, rfl⟩
  obtain ⟨cs, hcs⟩ : ∃ l, l = ((es.drop n1).drop n2).take n3 := ⟨_, rfl⟩
  obtain ⟨tail, htail⟩ : ∃ l, l = ((es.drop n1).drop n2).drop n3 := ⟨_, rfl⟩
  have hsplit : es = as ++ bs ++ cs ++ tail := by
    rw [has, hbs, hcs, htail]
    simp only [List.append_assoc, List.take_append_drop]
  have ha : as.length = n1 := by rw [has, List.length_take]; omega
  have hb : bs.length = n2 := by
    rw [hbs, List.length_take, List.length_drop]; omega
  have hcsl : cs.length = n3 := by
    rw [hcs, List.length_take, List.length_drop, List.length_drop]; omega
  have hprefix : as ++ bs ++ cs = es.take (n1 + n2 + n3) := by
    rw [hsplit]
    have e1 : (as ++ bs ++ cs).length = n1 + n2 + n3 := by
      rw [List.length_append, List.length_append, ha, hb, hcsl]
    rw [← e1, List.take_left]
  have he : as ++ bs ++ cs = GalilScaffoldAdvanceClock.advances 2048 2048
      ((av.take (n1 + n2 + n3)).map (fun b => (b, true))) := by
    rw [hprefix, hes, List.map_take, GalilScaffoldAdvanceClock.advances_take]
  obtain ⟨hm, hw, hs, hd, hcanon⟩ := begin_entry lower radius hlc k hk hrc rad hrad
  have hm0 : v0.toPrep.mode = .grow := by rw [toPrep_mode, hsearch]; exact hm
  have hw0 : v0.toPrep.work = ofNat (max k 1) := by rw [toPrep_work, hsearch]; exact hw
  have hs0 : v0.toPrep.span = ofNat 0 := by show v0.search.span = _; rw [hsearch]; exact hs
  have hd0 : value v0.toPrep.debt = -(rad : ℤ) := by show value v0.search.debt = _; rw [hsearch]; exact hd
  have hcanon0 : Canonical v0.toPrep.debt := by show Canonical v0.search.debt; rw [hsearch]; exact hcanon
  obtain ⟨u, p, used, rest', t, dpv, hg, hp, hcsplit, hq, hnr, hres, hdebt, htc, htn⟩ :=
    GalilScaffoldStagePrepare.first_stage_safe as bs cs _ v0.toPrep k rad center v0.search.quarter
      hm0 hw0 hs0 hd0 hcanon0 (by rw [ha, hn1]) (by rw [hb, hn2]) (by rw [hcsl, hn3]) he hr
  have huspan : u.span = ofNat (8*max k 1) := by
    have := paced_growing_span hg 0 hs0
    rw [this, ha, ← hn1]; congr 1; omega
  have hpm := (Prep.paced_prepared_mode hp huspan (by rw [hb, hn2])).1
  rw [hsplit] at hrun
  rw [List.append_assoc, List.append_assoc] at hrun
  obtain ⟨v1, hrun1, hrun'⟩ := searchRun_split _ as hrun
  obtain ⟨v2, hrun2, hrun''⟩ := searchRun_split _ bs hrun'
  rw [hcsplit, List.append_assoc] at hrun''
  have hmode0 : v0.search.mode = .grow := by rw [hsearch]; exact hm
  have hwork0 : v0.search.work = ofNat as.length := by rw [hsearch, ha, ← hn1]; exact hw
  obtain ⟨hg1, hq1, hl1, hm1, hw1⟩ := searchRun_growing _ as hrun1 hmode0 hwork0
  have hu : v1.toPrep = u := pacedGrowing_unique hg1 hg
  have hlk : lower = ofNat k := GalilScaffoldChainCatch.canonical_nat lower hlc k hk
  obtain ⟨a', bs', hbs'⟩ : ∃ a' bs', bs = a' :: bs' := by
    cases hbs0 : bs with
    | nil => rw [hbs0] at hb; simp at hb; omega
    | cons a' bs' => exact ⟨a', bs', rfl⟩
  have hrun20 := hrun2
  have hp0 := hp
  rw [hbs'] at hp hrun2
  have hw1' : positive v1.search.work = false := by simp [hw1, positive_ofNat]
  obtain ⟨hp2, hq2, hl2⟩ := searchRun_prepared _ hp hrun2 hu hm1 hw1' (by rw [hl1, hlower, hlk])
  obtain ⟨hsearch2, hdp2⟩ := toPrep_search_eq hp2
  have hq2' : v2.search.quarter = v0.search.quarter := by rw [hq2, hq1]
  rw [hq2'] at hsearch2
  obtain ⟨v3, hrun3, hs3, hx3, hl3, _, hrest⟩ := searchRun_quanta _ hq hrun'' hsearch2 hdp2
  have hp2m : v2.search.mode = .run := by
    rw [← toPrep_mode, hp2]; exact hpm
  have hq' : GalilScaffoldSearchRun.SafeQuanta v2.search v2.dp used v3.search v3.dp := by
    rw [hsearch2, hdp2, hs3, hx3]
    exact hq
  have hspan2 : v2.search.span = ofNat (8*max k 1) := by
    rw [hsearch2]
    show p.span = _
    exact (GalilScaffoldPreparePaced.prepared_span hp0).trans huspan
  have hul : used.length ≤ n3 := by
    rw [← hcsl, hcsplit, List.length_append]; omega
  refine ⟨as, bs, used, rest' ++ tail, v2, v3, ?_, by rw [ha, hn1], searchRun_append hrun1 hrun20,
    hrun3, hrest, hp2m, hq', by rw [hs3]; exact hnr, ⟨dpv, hx3, hres⟩, by rw [hs3]; exact hdebt,
    by rw [hs3]; exact htc, by rw [hs3]; exact htn, hspan2, by rw [hl3, hl2, hl1, hlower, hlk], ?_⟩
  · rw [hsplit, hcsplit]; simp [List.append_assoc]
  · simp only [List.length_append]
    rw [ha, hb]
    rw [← hn1, ← hn2, ← hn3] at *
    omega

#print axioms first_stage_aligned

/-! ## 5. Shared pieces of the stage induction -/

/-- The DP facts of a stage that halts in `found`. -/
theorem found_facts {k S : ℕ} (center : GalilScaffoldPlace.Place) {v2 v3 : SearchVM} {used : List Bool}
    (hq : GalilScaffoldSearchRun.SafeQuanta v2.search v2.dp used v3.search v3.dp)
    (hm2 : v2.search.mode = .run) (hf : v3.search.mode = .found)
    {dpv : GalilScaffoldProgram.Config 12} (hx : v3.dp = ⟨dpv, true⟩)
    (hres : GalilDpCorrect.Result ((GalilScaffoldPlace.stream center).take (S+1)) k 0
      (GalilScaffoldProgram.denote dpv)) :
    ∃ h : ℕ,
      GalilDpCorrect.Result ((GalilScaffoldPlace.stream center).take (S+1)) k 0
        (GalilScaffoldProgram.denote v3.dp.config) ∧
      (GalilScaffoldProgram.denote v3.dp.config).pc = 346 ∧
      (GalilScaffoldProgram.denote v3.dp.config).pos 11 = h ∧
      GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream center).take (S+1)) k h ∧
      (∀ g, g < h → ¬ GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream center).take (S+1)) k g) := by
  have hres' : GalilDpCorrect.Result ((GalilScaffoldPlace.stream center).take (S+1)) k 0
      (GalilScaffoldProgram.denote v3.dp.config) := by rw [hx]; exact hres
  obtain ⟨h, _, _, _, hcand, _, _, _, _, _, hcur⟩ :=
    found_copy_walk_least (w := (GalilScaffoldPlace.stream center).take (S+1))
      (lower := k) (span := S) center rfl hq hm2 hf hres'
  have hpc := result_pc_of_candidate hres' hcand
  exact ⟨h, hres', hpc, hcur, hcand, no_candidate_below_of_least hres' hpc hcur⟩

/-- The previous-stage failure from a non-`found` exit. -/
theorem exit_failure {k S : ℕ} (center : GalilScaffoldPlace.Place) {v2 v3 : SearchVM} {used : List Bool}
    (hq : GalilScaffoldSearchRun.SafeQuanta v2.search v2.dp used v3.search v3.dp)
    (hm2 : v2.search.mode = .run) (hnr : v3.search.mode ≠ .run) (hnf : v3.search.mode ≠ .found)
    {dpv : GalilScaffoldProgram.Config 12} (hx : v3.dp = ⟨dpv, true⟩)
    (hres : GalilDpCorrect.Result ((GalilScaffoldPlace.stream center).take (S+1)) k 0
      (GalilScaffoldProgram.denote dpv)) :
    ∀ g, ¬ GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream center).take (S+1)) k g := by
  have hres' : GalilDpCorrect.Result ((GalilScaffoldPlace.stream center).take (S+1)) k 0
      (GalilScaffoldProgram.denote v3.dp.config) := by rw [hx]; exact hres
  exact GalilFoundRadiusBound.prev_failure_of_result hres' (missed_pc_347 hq hm2 hnr hnf hres')

/-- `searchRun_waiting` with the debt of the new stage entry: `-[b]`. -/
theorem waiting_debt (center : GalilScaffoldPlace.Place) (ws : List Bool) (x : Bool) (clock : ℕ)
    (hclock : 1 ≤ clock ∧ clock ≤ 2048)
    (v3 : SearchVM) (hm : v3.search.mode = .wait) (hc : Canonical v3.search.debt)
    (hdebt : value v3.search.debt = ws.count true) (hb : BurnEvents ws)
    (n : ℕ) (hspan : v3.search.span = ofNat n) :
    ∃ v4 : SearchVM,
      SearchRun center (ws ++ [x && decide (clock = 1) && true]) v3 v4 ∧
      v4.search.mode = .double ∧ v4.search.quarter = 0 ∧
      v4.search.work = ofNat n ∧ v4.search.span = ofNat 0 ∧
      Canonical v4.search.debt ∧
      (0 ≤ value v4.search.debt ∨
        (-1 ≤ value v4.search.debt ∧ (GalilScaffoldMatchClock.run 2048 clock [x]).1 = 2048)) ∧
      (1 ≤ (GalilScaffoldMatchClock.run 2048 clock [x]).1 ∧
        (GalilScaffoldMatchClock.run 2048 clock [x]).1 ≤ 2048) ∧
      v4.lower = v3.lower ∧
      value v4.search.debt = -(([x && decide (clock = 1) && true].count true : ℕ) : ℤ) := by
  obtain ⟨v4, hrun, hm4, hq4, hw4, hs4, hc4, hd4, hcl4, hl4, _, _⟩ :=
    searchRun_waiting center ws x true clock hclock v3 hm hc hdebt hb n hspan
  obtain ⟨vm, hrunm, hmm, hzm, hcm, _⟩ := searchRun_burn center ws v3 hm hc hdebt hb
  set bb : Bool := x && decide (clock = 1) && true with hbb
  have hstep : searchStep center bb vm (waitNext bb vm) := wait_searchStep center bb vm hmm
  have hrun' : SearchRun center (ws ++ [bb]) v3 (waitNext bb vm) :=
    searchRun_append hrunm (.cons hstep (.nil _))
  have he : v4 = waitNext bb vm := searchRun_unique hrun hrun'
  have hv0 : value vm.search.debt = 0 := (zero_iff vm.search.debt hcm).mp hzm
  have hval : value (waitNext bb vm).search.debt = -(([bb].count true : ℕ) : ℤ) := by
    have hw : waitNext bb vm =
        {vm with search := GalilScaffoldSearchRun.advance bb (GalilScaffoldDouble.enter vm.search)} := by
      rw [waitNext, GalilScaffoldDouble.wait_enter vm.search hmm hzm]
    rw [hw]
    cases bb <;>
      simp [GalilScaffoldSearchRun.advance, GalilScaffoldDouble.enter, dec_value, hv0]
  exact ⟨v4, hrun, hm4, hq4, hw4, hs4, hc4, hd4, hcl4, hl4, he ▸ hval⟩

#print axioms found_facts
#print axioms exit_failure
#print axioms waiting_debt

/-! ## 6. The later-stage induction -/

/-- The found tick after a run from `v0`: the run `es` ends in a non-`found`
state `u`, and the tick `e` lands in `found`. -/
def FoundTick (center : GalilScaffoldPlace.Place) (es : List Bool) (v0 u : SearchVM) (e : Bool)
    (vq : SearchVM) : Prop :=
  SearchRun center es v0 u ∧ searchStep center e u vq ∧ u.search.mode ≠ .found ∧
    vq.search.mode = .found

/-- The entry of a later (doubling) stage with work `n`, as `searchRun_waiting`
and a direct `double` exit produce it. -/
def LaterEntry (k n clock : ℕ) (v0 : SearchVM) : Prop :=
  v0.search.mode = .double ∧ v0.search.quarter = 0 ∧ v0.search.work = ofNat n ∧
    v0.search.span = ofNat 0 ∧ Canonical v0.search.debt ∧
    (0 ≤ value v0.search.debt ∨ (-1 ≤ value v0.search.debt ∧ clock = 2048)) ∧
    v0.lower = ofNat k ∧ n % 4 = 0 ∧ 8 ≤ n ∧ 4*k ≤ n ∧ 1 ≤ clock ∧ clock ≤ 2048

/-- What a later stage entered with work `n` and debt `d0` delivers at its
found tick: the stage window `2n'` it is found in (`n ≤ n'`), the DP facts, the
failure of the previous window `n'`, and the match count of the run. -/
def LaterConcl (center : GalilScaffoldPlace.Place) (k n : ℕ) (d0 : ℤ) (es : List Bool)
    (vq : SearchVM) : Prop :=
  ∃ n' h : ℕ, n ≤ n' ∧
    GalilDpCorrect.Result ((GalilScaffoldPlace.stream center).take (2*n'+1)) k 0
      (GalilScaffoldProgram.denote vq.dp.config) ∧
    (GalilScaffoldProgram.denote vq.dp.config).pc = 346 ∧
    (GalilScaffoldProgram.denote vq.dp.config).pos 11 = h ∧
    GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream center).take (2*n'+1)) k h ∧
    (∀ g, g < h → ¬ GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream center).take (2*n'+1)) k g) ∧
    (∀ g, ¬ GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream center).take (n'+1)) k g) ∧
    4 * (es.count true : ℤ) + n ≤ 4 * d0 + 2 * n'

def LaterGoal (center : GalilScaffoldPlace.Place) (k : ℕ) (es : List Bool) : Prop :=
  ∀ (n clock : ℕ) (v0 u vq : SearchVM) (e : Bool) (av : List Bool),
    LaterEntry k n clock v0 → FoundTick center es v0 u e vq →
    (∀ g, ¬ GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream center).take (n+1)) k g) →
    es ++ [e] = GalilScaffoldAdvanceClock.advances 2048 clock (av.map (fun b => (b, true))) →
    LaterConcl center k n (value v0.search.debt) es vq

/-- **Continuing past a `wait`/`double` exit.**  From the exit state of a stage
whose window was `S`, the next stage (entered through the burn or directly)
reaches the found tick, and the whole remainder `R` satisfies the bound. -/
theorem exit_continue (center : GalilScaffoldPlace.Place) (k S : ℕ) (R : List Bool)
    (ih : ∀ es' : List Bool, es'.length ≤ R.length → LaterGoal center k es')
    {v3 u vq : SearchVM} {e : Bool} {clock3 : ℕ} {av3 : List Bool}
    (hmode : v3.search.mode = .wait ∨ v3.search.mode = .double)
    (hspan : v3.search.mode = .wait → v3.search.span = ofNat S)
    (hwork : v3.search.mode = .double →
      v3.search.work = ofNat S ∧ v3.search.span = ofNat 0 ∧ v3.search.quarter = 0)
    (hc : Canonical v3.search.debt) (hnn : 0 ≤ value v3.search.debt) (hlow : v3.lower = ofNat k)
    (hS4 : S % 4 = 0) (hS8 : 8 ≤ S) (hSk : 4*k ≤ S)
    (hprev : ∀ g, ¬ GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream center).take (S+1)) k g)
    (hft : FoundTick center R v3 u e vq)
    (hev : R ++ [e] = GalilScaffoldAdvanceClock.advances 2048 clock3 (av3.map (fun b => (b, true))))
    (hclock3 : 1 ≤ clock3 ∧ clock3 ≤ 2048) :
    LaterConcl center k S (value v3.search.debt) R vq := by
  obtain ⟨hrun, hstep, hu, hfound⟩ := hft
  rcases hmode with hw | hd
  · -- the burn, the boundary tick, then the next stage
    have hrunE : SearchRun center (R ++ [e]) v3 vq := searchRun_append hrun (.cons hstep (.nil _))
    obtain ⟨ws, b, L', hsplit, hval, hburn⟩ :=
      wait_split center (R ++ [e]) v3 vq hrunE hw hc (by rw [hfound]; decide)
    have hev' : ws ++ b :: L' =
        GalilScaffoldAdvanceClock.advances 2048 clock3 (av3.map (fun b => (b, true))) := by
      rw [← hsplit]; exact hev
    obtain ⟨_, hB⟩ := advances_split clock3 av3 ws (b :: L') hev'
    have hclW := GalilScaffoldMatchClock.run_invariant 2048 clock3 (av3.take ws.length) (by decide)
      hclock3
    obtain ⟨x, avW', hxav, hbx, hL'⟩ := advances_cons_head _ b L' _ hB
    obtain ⟨v4, hrun4, hm4, hq4, hw4, hs4, hc4, hd4, hcl4, hl4, hv4⟩ :=
      waiting_debt center ws x _ ⟨hclW.1, hclW.2.1⟩ v3 hw hc hval hburn S (hspan hw)
    rw [← hbx] at hrun4 hv4
    rcases List.eq_nil_or_concat L' with hnil | ⟨L'', e', hcat⟩
    · exfalso
      rw [hnil] at hsplit
      rw [hsplit] at hrunE
      have := searchRun_unique hrunE hrun4
      rw [this, hm4] at hfound
      exact absurd hfound (by decide)
    · rw [List.concat_eq_append] at hcat
      rw [hcat] at hsplit
      have hsplit' : R ++ [e] = (ws ++ b :: L'') ++ [e'] := by rw [hsplit]; simp
      obtain ⟨hR, he⟩ := List.append_inj' hsplit' rfl
      simp only [List.cons.injEq, and_true] at he
      subst he
      rw [hR, show ws ++ b :: L'' = (ws ++ [b]) ++ L'' by simp] at hrun
      obtain ⟨vm, hrm, hrest⟩ := searchRun_split _ (ws ++ [b]) hrun
      have hvm : vm = v4 := searchRun_unique hrm hrun4
      subst hvm
      have hlen : L''.length ≤ R.length := by rw [hR]; simp; omega
      obtain ⟨n', h, hn', hres, hpc, hpos, hcand, hmin, hprev', hbound⟩ :=
        ih L'' hlen S _ vm u vq e avW'
          ⟨hm4, hq4, hw4, hs4, hc4, hd4, by rw [hl4, hlow], hS4, hS8, hSk, hcl4.1, hcl4.2⟩
          ⟨hrest, hstep, hu, hfound⟩ hprev (by rw [← hcat]; exact hL')
      refine ⟨n', h, hn', hres, hpc, hpos, hcand, hmin, hprev', ?_⟩
      rw [hv4] at hbound
      rw [hR, hval]
      simp only [List.count_append, List.count_cons, List.count_nil] at hbound ⊢
      push_cast at hbound ⊢
      omega
  · obtain ⟨hw3, hs3, hq3⟩ := hwork hd
    obtain ⟨n', h, hn', hres, hpc, hpos, hcand, hmin, hprev', hbound⟩ :=
      ih R le_rfl S clock3 v3 u vq e av3
        ⟨hd, hq3, hw3, hs3, hc, Or.inl hnn, hlow, hS4, hS8, hSk, hclock3.1, hclock3.2⟩
        ⟨hrun, hstep, hu, hfound⟩ hprev hev
    exact ⟨n', h, hn', hres, hpc, hpos, hcand, hmin, hprev', hbound⟩

#print axioms exit_continue

/-- **One later stage.**  Given the goal for all strictly shorter runs, the
stage entered at `v0` either halts in `found` at the tick (window `2n`) or
exits in `wait`/`double` and hands on to the next stage. -/
theorem later_found_step (center : GalilScaffoldPlace.Place) (k : ℕ) (es : List Bool)
    (ih : ∀ es' : List Bool, es'.length < es.length → LaterGoal center k es') :
    LaterGoal center k es := by
  intro n clock v0 u vq e av hent hft hprev hev
  obtain ⟨hm0, hq0, hw0, hs0, hcanon, hd, hlow, hn4, hn8, hnk, hcl1, hcl2⟩ := hent
  obtain ⟨hrun, hstep, hu, hfound⟩ := hft
  obtain ⟨N, hN⟩ : ∃ N, n + (2*k + 2*((GalilScaffoldPlace.stream center).take (2*n+1)).length + 7)
      + GalilScaffoldTimingCost.runBudget (2*n) = N := ⟨_, rfl⟩
  have hNn : n ≤ N := by rw [← hN]; omega
  obtain ⟨esAll, hesAll⟩ : ∃ l, l = (es ++ [e]) ++ List.replicate N false := ⟨_, rfl⟩
  have hallEv : esAll = GalilScaffoldAdvanceClock.advances 2048 clock
      ((av ++ List.replicate N false).map (fun b => (b, true))) := by
    rw [hesAll, List.map_append, GalilScaffoldAdvanceClock.advances_append, ← hev, List.map_replicate,
      advances_replicate_false]
  have hrunE : SearchRun center (es ++ [e]) v0 vq := searchRun_append hrun (.cons hstep (.nil _))
  have hrunAll : SearchRun center esAll v0 vq := by
    rw [hesAll]; exact searchRun_append hrunE (searchRun_pad center N vq (Or.inl hfound))
  have hlenAll : N ≤ esAll.length := by rw [hesAll]; simp; omega
  have hrunAll' : SearchRun center (esAll.take N ++ esAll.drop N) v0 vq := by
    rw [List.take_append_drop]; exact hrunAll
  obtain ⟨vN, hrunN, _⟩ := searchRun_split _ _ hrunAll'
  have hesN : esAll.take N = GalilScaffoldAdvanceClock.advances 2048 clock
      (((av ++ List.replicate N false).take N).map (fun b => (b, true))) := by
    rw [List.map_take, GalilScaffoldAdvanceClock.advances_take, ← hallEv]
  have hlenN : (esAll.take N).length = n
      + (2*k + 2*((GalilScaffoldPlace.stream center).take (2*n+1)).length + 7)
      + GalilScaffoldTimingCost.runBudget (2*n) := by
    rw [List.length_take, hN]; omega
  obtain ⟨as, bs, used, rest, v2, v3, hsplit, hasl, hr12, hr3, _, hm2, hq, hnr, ⟨dpv, hx3, hres⟩,
      hdebt, hc3, hn3, hspan2, hl3⟩ :=
    later_stage_aligned center k n clock hrunN hm0 hq0 hw0 hs0 hcanon hd hlow hn4 hn8 hnk hesN
      ⟨hcl1, hcl2⟩ hlenN
  have hrunU : SearchRun center (as ++ bs ++ used) v0 v3 := searchRun_append hr12 hr3
  have hUlen : n ≤ (as ++ bs ++ used).length := by simp only [List.length_append]; omega
  have hUpre : as ++ bs ++ used <+: esAll := by
    refine ⟨rest ++ esAll.drop N, ?_⟩
    conv_rhs => rw [← List.take_append_drop N esAll]
    rw [hsplit]; simp [List.append_assoc]
  have hEpre : es ++ [e] <+: esAll := by rw [hesAll]; exact List.prefix_append _ _
  by_cases hA : es.length + 1 ≤ (as ++ bs ++ used).length
  · -- found inside this stage
    have hp1 : es ++ [e] <+: as ++ bs ++ used :=
      List.prefix_of_prefix_length_le hEpre hUpre
        (by rw [List.length_append, List.length_singleton]; exact hA)
    have hcnt : es.count true ≤ (as ++ bs ++ used).count true :=
      List.Sublist.count_le _ ((List.prefix_append es [e]).trans hp1).sublist
    obtain ⟨D, hD⟩ := hp1
    rw [← hD] at hrunU
    obtain ⟨vm, hvm1, hvm2⟩ := searchRun_split _ (es ++ [e]) hrunU
    have hvm : vm = vq := searchRun_unique hvm1 hrunE
    have h3 : v3 = vq := by
      have := searchRun_terminal hvm2 (by rw [hvm]; exact Or.inr (Or.inl hfound))
      rw [this, hvm]
    have hf3 : v3.search.mode = .found := by rw [h3]; exact hfound
    obtain ⟨h, hres', hpc, hpos, hcand, hmin⟩ := found_facts (S := 2*n) center hq hm2 hf3 hx3 hres
    rw [h3] at hres' hpc hpos hdebt hn3
    refine ⟨n, h, le_rfl, hres', hpc, hpos, hcand, hmin, hprev, ?_⟩
    omega
  · -- the stage exits before the tick
    have hp2 : as ++ bs ++ used <+: es :=
      List.prefix_of_prefix_length_le hUpre ((List.prefix_append es [e]).trans hEpre) (by omega)
    obtain ⟨R, hR⟩ := hp2
    rw [← hR] at hrun
    obtain ⟨vm, hvm1, hvm2⟩ := searchRun_split _ _ hrun
    have hvm : vm = v3 := searchRun_unique hvm1 hrunU
    subst hvm
    have hev' : (as ++ bs ++ used) ++ (R ++ [e]) =
        GalilScaffoldAdvanceClock.advances 2048 clock (av.map (fun b => (b, true))) := by
      rw [← List.append_assoc, hR]; exact hev
    obtain ⟨_, hevR⟩ := advances_split clock av _ _ hev'
    have hcl3 := GalilScaffoldMatchClock.run_invariant 2048 clock
      (av.take (as ++ bs ++ used).length) (by decide) ⟨hcl1, hcl2⟩
    have hwd : vm.search.mode = .wait ∨ vm.search.mode = .double := by
      rcases GalilScaffoldSearchRun.quanta_exit_mode hq hm2 hnr with h | h | h | h
      · exfalso
        have h1 := searchRun_terminal hvm2 (Or.inr (Or.inl h))
        exact hu (by rw [h1]; exact h)
      · exfalso
        have h1 := searchRun_terminal hvm2 (Or.inr (Or.inr h))
        have h2 := searchStep_terminal hstep (by rw [h1]; exact Or.inr (Or.inr h))
        rw [h2, h1, h] at hfound
        exact absurd hfound (by decide)
      · exact Or.inl h
      · exact Or.inr h
    have hnf : vm.search.mode ≠ .found := by
      rcases hwd with h | h <;> rw [h] <;> decide
    have hprev' := exit_failure (S := 2*n) center hq hm2 hnr hnf hx3 hres
    have hspanW : vm.search.mode = .wait → vm.search.span = ofNat (2*n) := by
      intro hw
      have hfr := (GalilScaffoldSearchRun.safe_quanta_frame hq).2
      simp [GalilScaffoldSearchRun.stageSpan, hw, hm2] at hfr
      rw [hfr, hspan2]
    have hworkD : vm.search.mode = .double →
        vm.search.work = ofNat (2*n) ∧ vm.search.span = ofNat 0 ∧ vm.search.quarter = 0 := by
      intro hdb
      have h1 := GalilScaffoldSearchRun.double_work_of_quanta hq hm2 hdb
      have h2 := GalilScaffoldSearchRun.double_reset_of_quanta hq hm2 hdb
      exact ⟨h1.trans hspan2, h2.1, h2.2⟩
    obtain ⟨n', h, hn', hres', hpc, hpos, hcand, hmin, hprev'', hbound⟩ :=
      exit_continue center k (2*n) R
        (fun es' hl => ih es' (by rw [← hR]; simp only [List.length_append]; omega))
        hwd hspanW hworkD hc3 hn3 (by rw [hl3, hlow]) (by omega) (by omega) (by omega) hprev'
        ⟨hvm2, hstep, hu, hfound⟩ hevR ⟨hcl3.1, hcl3.2.1⟩
    refine ⟨n', h, by omega, hres', hpc, hpos, hcand, hmin, hprev'', ?_⟩
    rw [← hR, List.count_append]
    push_cast
    omega

theorem later_found_all (center : GalilScaffoldPlace.Place) (k : ℕ) :
    ∀ (N : ℕ) (es : List Bool), es.length ≤ N → LaterGoal center k es := by
  intro N
  induction N with
  | zero => intro es hl; exact later_found_step center k es (fun es' h => absurd h (by omega))
  | succ N ih => intro es hl; exact later_found_step center k es (fun es' h => ih es' (by omega))

/-- **Every later stage.** -/
theorem later_found (center : GalilScaffoldPlace.Place) (k : ℕ) (es : List Bool) :
    LaterGoal center k es :=
  later_found_all center k es.length es le_rfl

#print axioms later_found_step
#print axioms later_found

/-! ## 7. The whole search from a restart -/

/-- **From `Search.start` to the found tick.**  The first stage either halts
in `found` at the tick (window `8*max k 1`, with `rad + matches ≤ 2*max k 1`
and the tick inside the stage duration) or exits and a later stage of window
`2n'` is found, with the previous window `n'` failed and
`2*(rad + matches) ≤ n'`. -/
theorem first_found (center : GalilScaffoldPlace.Place)
    (lower radius : Counter) (hlc : Canonical lower) (k : ℕ) (hk : value lower = k)
    (hrc : Canonical radius) (rad : ℕ) (hrad : value radius = rad) (hr : 3*rad ≤ 5*k)
    {v0 u vq : SearchVM} {es : List Bool} {e : Bool} {av : List Bool}
    (hsearch : v0.search = GalilScaffoldSearchFinish.begin lower radius) (hlower : v0.lower = lower)
    (hft : FoundTick center es v0 u e vq)
    (hev : es ++ [e] = GalilScaffoldAdvanceClock.advances 2048 2048 (av.map (fun b => (b, true)))) :
    ∃ span h : ℕ,
      GalilDpCorrect.Result ((GalilScaffoldPlace.stream center).take (span+1)) k 0
        (GalilScaffoldProgram.denote vq.dp.config) ∧
      (GalilScaffoldProgram.denote vq.dp.config).pc = 346 ∧
      (GalilScaffoldProgram.denote vq.dp.config).pos 11 = h ∧
      GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream center).take (span+1)) k h ∧
      (∀ g, g < h → ¬ GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream center).take (span+1)) k g) ∧
      ((span = 8 * max k 1 ∧ rad + es.count true ≤ 2 * max k 1 ∧
          es.length + 1 ≤ 63 * (8 * max k 1)) ∨
        (∃ n' : ℕ, span = 2 * n' ∧ 8 * max k 1 ≤ n' ∧
          (∀ g, ¬ GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream center).take (n'+1)) k g) ∧
          2 * (rad + es.count true) ≤ n')) := by
  obtain ⟨hrun, hstep, hu, hfound⟩ := hft
  obtain ⟨N, hN⟩ : ∃ N, max k 1
      + (2*k + 2*((GalilScaffoldPlace.stream center).take (8*max k 1+1)).length + 7)
      + GalilScaffoldTimingCost.runBudget (8*max k 1) = N := ⟨_, rfl⟩
  obtain ⟨esAll, hesAll⟩ : ∃ l, l = (es ++ [e]) ++ List.replicate N false := ⟨_, rfl⟩
  have hallEv : esAll = GalilScaffoldAdvanceClock.advances 2048 2048
      ((av ++ List.replicate N false).map (fun b => (b, true))) := by
    rw [hesAll, List.map_append, GalilScaffoldAdvanceClock.advances_append, ← hev, List.map_replicate,
      advances_replicate_false]
  have hrunE : SearchRun center (es ++ [e]) v0 vq := searchRun_append hrun (.cons hstep (.nil _))
  have hrunAll : SearchRun center esAll v0 vq := by
    rw [hesAll]; exact searchRun_append hrunE (searchRun_pad center N vq (Or.inl hfound))
  have hlenAll : N ≤ esAll.length := by rw [hesAll]; simp; omega
  have hrunAll' : SearchRun center (esAll.take N ++ esAll.drop N) v0 vq := by
    rw [List.take_append_drop]; exact hrunAll
  obtain ⟨vN, hrunN, _⟩ := searchRun_split _ _ hrunAll'
  have hesN : esAll.take N = GalilScaffoldAdvanceClock.advances 2048 2048
      (((av ++ List.replicate N false).take N).map (fun b => (b, true))) := by
    rw [List.map_take, GalilScaffoldAdvanceClock.advances_take, ← hallEv]
  have hlenN : (esAll.take N).length = max k 1
      + (2*k + 2*((GalilScaffoldPlace.stream center).take (8*max k 1+1)).length + 7)
      + GalilScaffoldTimingCost.runBudget (8*max k 1) := by
    rw [List.length_take, hN]; omega
  obtain ⟨as, bs, used, rest, v2, v3, hsplit, hasl, hr12, hr3, _, hm2, hq, hnr, ⟨dpv, hx3, hres⟩,
      hdebt, hc3, hn3, hspan2, hl3, htick⟩ :=
    first_stage_aligned center lower radius hlc k hk hrc rad hrad hr hrunN hsearch hlower hesN hlenN
  have hrunU : SearchRun center (as ++ bs ++ used) v0 v3 := searchRun_append hr12 hr3
  have hm1 : 1 ≤ max k 1 := le_max_right _ _
  have hUlen : 1 ≤ (as ++ bs ++ used).length := by simp only [List.length_append]; omega
  have hUpre : as ++ bs ++ used <+: esAll := by
    refine ⟨rest ++ esAll.drop N, ?_⟩
    conv_rhs => rw [← List.take_append_drop N esAll]
    rw [hsplit]; simp [List.append_assoc]
  have hEpre : es ++ [e] <+: esAll := by rw [hesAll]; exact List.prefix_append _ _
  obtain ⟨m, hm⟩ : ∃ m, max k 1 = m := ⟨_, rfl⟩
  by_cases hA : es.length + 1 ≤ (as ++ bs ++ used).length
  · have hp1 : es ++ [e] <+: as ++ bs ++ used :=
      List.prefix_of_prefix_length_le hEpre hUpre
        (by rw [List.length_append, List.length_singleton]; exact hA)
    have hcnt : es.count true ≤ (as ++ bs ++ used).count true :=
      List.Sublist.count_le _ ((List.prefix_append es [e]).trans hp1).sublist
    obtain ⟨D, hD⟩ := hp1
    rw [← hD] at hrunU
    obtain ⟨vm, hvm1, hvm2⟩ := searchRun_split _ (es ++ [e]) hrunU
    have hvm : vm = vq := searchRun_unique hvm1 hrunE
    have h3 : v3 = vq := by
      have := searchRun_terminal hvm2 (by rw [hvm]; exact Or.inr (Or.inl hfound))
      rw [this, hvm]
    have hf3 : v3.search.mode = .found := by rw [h3]; exact hfound
    obtain ⟨h, hres', hpc, hpos, hcand, hmin⟩ :=
      found_facts (S := 8 * max k 1) center hq hm2 hf3 hx3 hres
    rw [h3] at hres' hpc hpos hdebt hn3
    refine ⟨8 * max k 1, h, hres', hpc, hpos, hcand, hmin, Or.inl ⟨rfl, ?_, by omega⟩⟩
    rw [hm] at hdebt ⊢
    omega
  · have hp2 : as ++ bs ++ used <+: es :=
      List.prefix_of_prefix_length_le hUpre ((List.prefix_append es [e]).trans hEpre) (by omega)
    obtain ⟨R, hR⟩ := hp2
    rw [← hR] at hrun
    obtain ⟨vm, hvm1, hvm2⟩ := searchRun_split _ _ hrun
    have hvm : vm = v3 := searchRun_unique hvm1 hrunU
    subst hvm
    have hev' : (as ++ bs ++ used) ++ (R ++ [e]) =
        GalilScaffoldAdvanceClock.advances 2048 2048 (av.map (fun b => (b, true))) := by
      rw [← List.append_assoc, hR]; exact hev
    obtain ⟨_, hevR⟩ := advances_split 2048 av _ _ hev'
    have hcl3 := GalilScaffoldMatchClock.run_invariant 2048 2048
      (av.take (as ++ bs ++ used).length) (by decide) ⟨by decide, le_rfl⟩
    have hwd : vm.search.mode = .wait ∨ vm.search.mode = .double := by
      rcases GalilScaffoldSearchRun.quanta_exit_mode hq hm2 hnr with h | h | h | h
      · exfalso
        have h1 := searchRun_terminal hvm2 (Or.inr (Or.inl h))
        exact hu (by rw [h1]; exact h)
      · exfalso
        have h1 := searchRun_terminal hvm2 (Or.inr (Or.inr h))
        have h2 := searchStep_terminal hstep (by rw [h1]; exact Or.inr (Or.inr h))
        rw [h2, h1, h] at hfound
        exact absurd hfound (by decide)
      · exact Or.inl h
      · exact Or.inr h
    have hnf : vm.search.mode ≠ .found := by
      rcases hwd with h | h <;> rw [h] <;> decide
    have hprev' := exit_failure (S := 8 * max k 1) center hq hm2 hnr hnf hx3 hres
    have hspanW : vm.search.mode = .wait → vm.search.span = ofNat (8 * max k 1) := by
      intro hw
      have hfr := (GalilScaffoldSearchRun.safe_quanta_frame hq).2
      simp [GalilScaffoldSearchRun.stageSpan, hw, hm2] at hfr
      rw [hfr, hspan2]
    have hworkD : vm.search.mode = .double →
        vm.search.work = ofNat (8 * max k 1) ∧ vm.search.span = ofNat 0 ∧ vm.search.quarter = 0 := by
      intro hdb
      have h1 := GalilScaffoldSearchRun.double_work_of_quanta hq hm2 hdb
      have h2 := GalilScaffoldSearchRun.double_reset_of_quanta hq hm2 hdb
      exact ⟨h1.trans hspan2, h2.1, h2.2⟩
    obtain ⟨n', h, hn', hres', hpc, hpos, hcand, hmin, hprev'', hbound⟩ :=
      exit_continue center k (8 * max k 1) R (fun es' _ => later_found center k es')
        hwd hspanW hworkD hc3 hn3 hl3 (by omega) (by omega) (by omega) hprev'
        ⟨hvm2, hstep, hu, hfound⟩ hevR ⟨hcl3.1, hcl3.2.1⟩
    refine ⟨2 * n', h, hres', hpc, hpos, hcand, hmin, Or.inr ⟨n', rfl, hn', hprev'', ?_⟩⟩
    rw [← hR, List.count_append]
    rw [hm] at hdebt hbound
    push_cast at hdebt hbound
    omega

#print axioms first_found

/-! ## 8. At the found tick -/

/-- **`found_radius_le_all_stages`.**  At any found tick reached along a
chain-idle segment from a restarted state, whatever stage the `found` belongs
to: the DP facts of that stage (window `span`), and the `hradius` premise
`value radius ≤ 4090*h - 2052` of `prelude_done_before_extent'` for the least
candidate `h`.  The hypotheses are exactly those of `found_radius_le` without
its `htime`, and there is no escape disjunct.  The stage disjunct records,
for the first stage, the premise `htime` of `found_radius_le`
(`es1.length ≤ 63*(8*max k 1)`), and for a later stage of window `2n'` the
failed previous window `n'` (`hprev`) and `2*radius ≤ n'` (hence `hbar`). -/
theorem found_radius_le_all_stages (P : Shared) (qq : ℕ) (first : Fin 9) (hP : Decodes P)
    (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    {raw : List (Fin 2)} {r : GalilVM} {Rad : ℕ} {last : Counter}
    (hR : Restarted raw r Rad last)
    (hcen : r.center = represent ⟨a :: ls,gap⟩ (rs.map some) q)
    {c0 : Control} (hcl : c0.clock = 2048)
    (hstage : StageEntry Rad last)
    {es1 : List Bool} {cF : Control} {sF : GalilVM}
    (hseg : WatchSegE P qq first 2048 es1 c0 r cF sF) (hsF : sF.chain = .idle)
    (hcF : cF.clock = 1) (vq : SearchVM) (hq : searchEffect P true sF vq)
    (hfound : vq.search.mode = .found) :
    ∃ k h span : ℕ, value last = (k : ℤ) ∧
      GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) k 0
        (GalilScaffoldProgram.denote vq.dp.config) ∧
      (GalilScaffoldProgram.denote vq.dp.config).pc = 346 ∧
      (GalilScaffoldProgram.denote vq.dp.config).pos 11 = h ∧
      GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) k h ∧
      (∀ g, g < h →
        ¬ GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) k g) ∧
      ((span = 8 * max k 1 ∧ es1.length ≤ 63 * (8 * max k 1) ∧
          value sF.radius ≤ 2 * ((max k 1 : ℕ) : ℤ)) ∨
        (∃ n' : ℕ, span = 2 * n' ∧ 8 * max k 1 ≤ n' ∧
          (∀ g, ¬ GalilDpCorrect.Candidate
            ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (n'+1)) k g) ∧
          2 * value sF.radius ≤ (n' : ℤ) ∧ value sF.radius ≤ 512 * (n' : ℤ))) ∧
      1 ≤ h ∧ value sF.radius ≤ 4090 * (h : ℤ) - 2052 := by
  obtain ⟨_, _, _, _, ⟨hrc, hrv⟩, _, hsearch, hlower, hlast, hlv⟩ := hR
  obtain ⟨_, hplr⟩ := hP.1 r a ls rs q gap hcen
  obtain ⟨k, hk⟩ : ∃ k : ℕ, value last = k := ⟨(value last).toNat, (Int.toNat_of_nonneg hlv).symm⟩
  have hstep : searchStep (P.place sF) true (searchLens.get sF) vq := by
    rcases hq with ⟨_, hstep⟩ | ⟨hne, _⟩
    · exact hstep
    · exact absurd hsF hne
  have hrunSeg0 := watchSegE_searchRun P qq first 2048 hP.2 hseg hsF
  have hrunSeg := hrunSeg0
  rw [hplr] at hrunSeg
  have hcen1 : sF.center = r.center := watchSegE_center P qq first 2048 hseg
  rw [hP.2 sF r hcen1, hplr] at hstep
  obtain ⟨av1, _, hes1, hcl1, _⟩ := watchSegE_clock P qq first 2048 hseg
  rw [hcl] at hes1 hcl1
  have hev : es1 ++ [true] = GalilScaffoldAdvanceClock.advances 2048 2048
      ((av1 ++ [true]).map (fun b => (b, true))) := by
    rw [List.map_append, GalilScaffoldAdvanceClock.advances_append, map_fst_map_pair, ← hcl1, ← hes1,
      hcF]
    rfl
  have hu : (searchLens.get sF).search.mode ≠ .found := by
    cases hes : es1 with
    | nil =>
      rw [hes] at hrunSeg
      have he : searchLens.get sF = searchLens.get r := searchRun_unique hrunSeg (.nil _)
      rw [he]
      show r.search.mode ≠ _
      rw [hsearch]
      simp [GalilScaffoldSearchFinish.begin]
    | cons x xs =>
      exact watchSegE_search_not_found P qq first 2048 hP.2 hseg hsF es1 [] _ (by simp)
        (by rw [hes]; simp) hrunSeg0
  obtain ⟨span, h, hres, hpc, hpos, hcand, hmin, hcase⟩ :=
    first_found ⟨a :: ls,gap⟩ last r.radius hlast k hk hrc Rad hrv (hstage k hk)
      (v0 := searchLens.get r) hsearch hlower ⟨hrunSeg, hstep, hu, hfound⟩ hev
  obtain ⟨hkh, h1⟩ := GalilFoundRadiusBound.candidate_lower_lt hcand
  obtain ⟨_, _, hrad, _, _⟩ := watchSegE_heads P qq first 2048 hseg
  rw [hrv] at hrad
  refine ⟨k, h, span, hk, hres, hpc, hpos, hcand, hmin, ?_, h1, ?_⟩
  · rcases hcase with ⟨hs, hb, ht⟩ | ⟨n', hs, hn', hprev, hb⟩
    · refine Or.inl ⟨hs, by omega, ?_⟩
      rw [hrad]
      have : ((Rad + es1.count true : ℕ) : ℤ) ≤ ((2 * max k 1 : ℕ) : ℤ) := by exact_mod_cast hb
      push_cast at this ⊢
      exact this
    · refine Or.inr ⟨n', hs, hn', hprev, ?_, ?_⟩ <;> rw [hrad] <;>
        · have : ((2 * (Rad + es1.count true) : ℕ) : ℤ) ≤ (n' : ℤ) := by exact_mod_cast hb
          push_cast at this
          omega
  · rcases hcase with ⟨_, hb, _⟩ | ⟨n', hs, _, hprev, hb⟩
    · have := GalilFoundRadiusBound.first_radius_arith (Rad + es1.count true) k h hkh hb
      rw [hrad]; push_cast at this; exact this
    · rw [hs] at hcand
      have hn := GalilFoundRadiusBound.later_stage_n_lt _ n' k h hcand hprev
      have hbar : value sF.radius ≤ 512 * (n' : ℤ) := by
        rw [hrad]
        have : ((2 * (Rad + es1.count true) : ℕ) : ℤ) ≤ (n' : ℤ) := by exact_mod_cast hb
        push_cast at this
        omega
      exact GalilFoundRadiusBound.later_radius_arith _ n' h hn hbar

#print axioms found_radius_le_all_stages

end PalPeg.GalilLaterRadius
