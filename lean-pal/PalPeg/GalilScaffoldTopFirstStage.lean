import PalPeg.GalilScaffoldTopStagePrefix

/-!
# The first search stage on the actual run

After `Search.start(lower)` (the scheduler is `begin lower radius`), the
actual search run over a chain-idle segment — its events being the match
clock's advances from a fresh clock — goes through the grow phase, the
preparation and the DP run of the lower layer's `first_stage_chain_run`,
and halts in an exit mode with the DP result on its program; when it halts
in `found`, the DP candidate and the copied semiperiod are available.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

theorem searchRun_split (center : GalilScaffoldPlace.Place) (l1 : List Bool) :
    ∀ {l2 : List Bool} {v v' : SearchVM}, SearchRun center (l1 ++ l2) v v' →
      ∃ vm, SearchRun center l1 v vm ∧ SearchRun center l2 vm v' := by
  induction l1 with
  | nil => intro l2 v v' h; exact ⟨v, .nil _, h⟩
  | cons a l1 ih =>
    intro l2 v v' h
    cases h with
    | cons hstep hrest =>
      obtain ⟨vm, h1, h2⟩ := ih hrest
      exact ⟨vm, .cons hstep h1, h2⟩

theorem toPrep_search_eq {v : SearchVM} {p : GalilScaffoldPrepareControl.State} (h : v.toPrep = p) :
    v.search = GalilScaffoldStagePrepare.runState p v.search.quarter ∧ v.dp = p.program := by
  subst h
  exact ⟨rfl, rfl⟩

/-- The first stage of the actual search after `Search.start`. -/
theorem search_first_stage (a : Fin 2) (ls rs qq : List (Fin 2)) (gap : Bool) (cen : PlaceHead)
    (hcen : cen = represent ⟨a :: ls,gap⟩ (rs.map some) qq)
    (c : Fin 3) (hc : GalilScaffoldPlace.read ⟨a :: ls,gap⟩ = some c)
    (lower radius : Counter) (hlc : Canonical lower) (k : ℕ) (hk : value lower = k)
    (hrc : Canonical radius) (rad : ℕ) (hrad : value radius = rad) (hr : 3*rad ≤ 5*k)
    {v0 v' : SearchVM} {es : List Bool} (hrun : SearchRun ⟨a :: ls,gap⟩ es v0 v')
    (hsearch : v0.search = GalilScaffoldSearchFinish.begin lower radius) (hlower : v0.lower = lower)
    {av : List Bool} (hav : av.length = es.length)
    (hes : es = GalilScaffoldAdvanceClock.advances 2048 2048 (av.map (fun b => (b, true))))
    (hlen : max k 1 + (2*k + 2*((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (8*max k 1+1)).length + 7)
      + GalilScaffoldTimingCost.runBudget (8*max k 1) ≤ es.length) :
    ∃ (as bs usedQ rest : List Bool) (v1 v2 v3 : SearchVM),
      es = as ++ bs ++ usedQ ++ rest ∧ as.length = max k 1 ∧
      bs.length = 2*k + 2*((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (8*max k 1+1)).length + 7 ∧
      SearchRun ⟨a :: ls,gap⟩ as v0 v1 ∧ SearchRun ⟨a :: ls,gap⟩ bs v1 v2 ∧
      SearchRun ⟨a :: ls,gap⟩ usedQ v2 v3 ∧ SearchRun ⟨a :: ls,gap⟩ rest v3 v' ∧
      v0.search.mode = .grow ∧ v0.search.work = ofNat as.length ∧
      GalilScaffoldPreparePaced.PacedPrepared (ofNat k) ⟨a :: ls,gap⟩ v1.toPrep bs v2.toPrep ∧
      v1.search.mode = .grow ∧ positive v1.search.work = false ∧ v1.lower = ofNat k ∧
      v2.search.mode = .run ∧
      GalilScaffoldSearchRun.SafeQuanta v2.search v2.dp usedQ v3.search v3.dp ∧
      v3.search.mode ≠ .run ∧ v3.lower = lower ∧
      (∃ dpv, v3.dp = ⟨dpv, true⟩ ∧
        GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (8*max k 1+1)) k 0
          (GalilScaffoldProgram.denote dpv)) ∧
      (v3.search.mode = .found →
        ∀ (rad' : Counter), Canonical rad' → ∀ (r0 : ℕ), value rad' = r0 → 0 < r0 → ∀ (sm dm : Bool),
        ∃ (h : ℕ) (ys : List (Fin 3)) (b : Fin 3),
          GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (8*max k 1+1)) k h ∧
          ys.length+1 = h) := by
  -- the phase lengths
  obtain ⟨n1, hn1⟩ : ∃ n, max k 1 = n := ⟨_, rfl⟩
  obtain ⟨n2, hn2⟩ : ∃ n, 2*k + 2*((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (8*max k 1+1)).length + 7 = n :=
    ⟨_, rfl⟩
  obtain ⟨n3, hn3⟩ : ∃ n, GalilScaffoldTimingCost.runBudget (8*max k 1) = n := ⟨_, rfl⟩
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
  -- the events of the three phases
  have hprefix : as ++ bs ++ cs = es.take (n1 + n2 + n3) := by
    rw [hsplit]
    have e1 : (as ++ bs ++ cs).length = n1 + n2 + n3 := by
      rw [List.length_append, List.length_append, ha, hb, hcsl]
    rw [← e1, List.take_left]
  have he : as ++ bs ++ cs = GalilScaffoldAdvanceClock.advances 2048 2048
      ((av.take (n1 + n2 + n3)).map (fun b => (b, true))) := by
    rw [hprefix, hes, List.map_take, GalilScaffoldAdvanceClock.advances_take]
  -- the entry of the stage
  obtain ⟨hm, hw, hs, hd, hcanon⟩ := begin_entry lower radius hlc k hk hrc rad hrad
  have hm0 : v0.toPrep.mode = .grow := by rw [toPrep_mode, hsearch]; exact hm
  have hw0 : v0.toPrep.work = ofNat (max k 1) := by rw [toPrep_work, hsearch]; exact hw
  have hs0 : v0.toPrep.span = ofNat 0 := by show v0.search.span = _; rw [hsearch]; exact hs
  have hd0 : value v0.toPrep.debt = -(rad : ℤ) := by show value v0.search.debt = _; rw [hsearch]; exact hd
  have hcanon0 : Canonical v0.toPrep.debt := by show Canonical v0.search.debt; rw [hsearch]; exact hcanon
  obtain ⟨u, p, used, rest', t, dpv, hg, hp, hpm, hcsplit, hq, hnr, hres, hchain⟩ :=
    first_stage_chain_run as bs cs _ v0.toPrep k rad a ls rs qq gap cen hcen c hc v0.search.quarter
      hm0 hw0 hs0 hd0 hcanon0 (by rw [ha, hn1]) (by rw [hb, hn2]) (by rw [hcsl, hn3]) he hr
  -- the actual run through the phases
  rw [hsplit] at hrun
  rw [List.append_assoc, List.append_assoc] at hrun
  obtain ⟨v1, hrun1, hrun'⟩ := searchRun_split _ as hrun
  obtain ⟨v2, hrun2, hrun''⟩ := searchRun_split _ bs hrun'
  rw [hcsplit, List.append_assoc] at hrun''
  -- grow
  have hmode0 : v0.search.mode = .grow := by rw [hsearch]; exact hm
  have hwork0 : v0.search.work = ofNat as.length := by rw [hsearch, ha, ← hn1]; exact hw
  obtain ⟨hg1, hq1, hl1, hm1, hw1⟩ := searchRun_growing _ as hrun1 hmode0 hwork0
  have hu : v1.toPrep = u := pacedGrowing_unique hg1 hg
  -- preparation
  have hlk : lower = ofNat k := GalilScaffoldChainCatch.canonical_nat lower hlc k hk
  obtain ⟨a', bs', hbs'⟩ : ∃ a' bs', bs = a' :: bs' := by
    cases hbs0 : bs with
    | nil => rw [hbs0] at hb; simp at hb; omega
    | cons a' bs' => exact ⟨a', bs', rfl⟩
  rw [hbs'] at hp hrun2
  have hw1' : positive v1.search.work = false := by simp [hw1, positive_ofNat]
  obtain ⟨hp2, hq2, hl2⟩ := searchRun_prepared _ hp hrun2 hu hm1 hw1' (by rw [hl1, hlower, hlk])
  -- the run
  obtain ⟨hsearch2, hdp2⟩ := toPrep_search_eq hp2
  have hq2' : v2.search.quarter = v0.search.quarter := by rw [hq2, hq1]
  rw [hq2'] at hsearch2
  obtain ⟨v3, hrun3, hs3, hx3, hl3, _, hrest⟩ := searchRun_quanta _ hq hrun'' hsearch2 hdp2
  have hp2m : v2.search.mode = .run := by
    rw [← toPrep_mode, hp2]; exact hpm
  have hq' : GalilScaffoldSearchRun.SafeQuanta v2.search v2.dp used v3.search v3.dp := by
    rw [hsearch2, hdp2]
    rw [hs3, hx3]
    exact hq
  refine ⟨as, bs, used, rest' ++ tail, v1, v2, v3, ?_, ?_, ?_, hrun1, ?_, hrun3, hrest, hmode0, hwork0,
    ?_, hm1, hw1', ?_, hp2m, hq', ?_, ?_, ⟨dpv, hx3, hres⟩, ?_⟩
  · rw [hsplit, hcsplit]; simp [List.append_assoc]
  · rw [ha, hn1]
  · rw [hb, hn2]
  · rw [hbs']; exact hrun2
  · rw [hbs', hu, hp2]; exact hp
  · rw [hl1, hlower, hlk]
  · rw [hs3]; exact hnr
  · rw [hl3, hl2, hl1, hlower]
  · intro hf
    rw [hs3] at hf
    exact hchain hf

#print axioms search_first_stage

end PalPeg.GalilScaffoldChainInputSupply
