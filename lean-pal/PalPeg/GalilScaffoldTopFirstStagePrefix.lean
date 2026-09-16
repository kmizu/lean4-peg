import PalPeg.GalilScaffoldTopFirstStage

/-!
# No exit before the end of the first stage

Along the first stage's grow ticks, preparation and run quanta, the actual
search is never in `found` (or any exit mode) before the last quantum, and
it is in `run` just before it. This pins the tick at which the controller
starts the chain: the last event of the stage.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

theorem zip_replicate_append (l1 l2 : List Bool) :
    (List.replicate (l1 ++ l2).length true).zip (l1 ++ l2) =
      (List.replicate l1.length true).zip l1 ++ (List.replicate l2.length true).zip l2 := by
  rw [List.length_append, List.replicate_add, List.zip_append (by simp)]

theorem pacedPrepared_split {x z : GalilScaffoldPrepareControl.State} (l1 l2 : List Bool)
    (h : GalilScaffoldPreparePaced.PacedRun x ((List.replicate (l1 ++ l2).length true).zip (l1 ++ l2)) z) :
    ∃ y, GalilScaffoldPreparePaced.PacedRun x ((List.replicate l1.length true).zip l1) y ∧
      GalilScaffoldPreparePaced.PacedRun y ((List.replicate l2.length true).zip l2) z := by
  rw [zip_replicate_append] at h
  exact pacedRun_split _ h

theorem all_enabled_zip (l : List Bool) :
    ∀ e ∈ (List.replicate l.length true).zip l, e.1 = true := by
  intro e he
  exact List.eq_of_mem_replicate (List.of_mem_zip he).1

theorem safeQuanta_nil {s t : GalilScaffoldSearchFinish.State} {x y : GalilScaffoldControl.Machine 12}
    (h : GalilScaffoldSearchRun.SafeQuanta s x [] t y) : t = s ∧ y = x := by
  cases h; exact ⟨rfl, rfl⟩

/-- The state after a prefix of a run is determined. -/
theorem searchRun_prefix_eq {center : GalilScaffoldPlace.Place} {l : List Bool} {v0 v' v : SearchVM}
    (h : SearchRun center l v0 v') (j : ℕ) (hj : SearchRun center (l.take j) v0 v) :
    ∃ v'' , SearchRun center (l.drop j) v v'' ∧ v'' = v' := by
  have h' : SearchRun center (l.take j ++ l.drop j) v0 v' := by rw [List.take_append_drop]; exact h
  obtain ⟨vm, h1, h2⟩ := searchRun_split _ _ h'
  have := searchRun_unique h1 hj
  subst this
  exact ⟨v', h2, rfl⟩

/-- Along the first stage the search is never `found` before the last
quantum, and it is in `run` right before it. -/
theorem stage_prefix_mode (center : GalilScaffoldPlace.Place) (k : ℕ)
    {as bs usedQ : List Bool} {v0 v1 v2 v3 : SearchVM}
    (h1 : SearchRun center as v0 v1) (h2 : SearchRun center bs v1 v2)
    (h3 : SearchRun center usedQ v2 v3)
    (hm0 : v0.search.mode = .grow) (hw0 : v0.search.work = ofNat as.length)
    (hp : GalilScaffoldPreparePaced.PacedPrepared (ofNat k) center v1.toPrep bs v2.toPrep)
    (hm1 : v1.search.mode = .grow) (hw1 : positive v1.search.work = false) (hl1 : v1.lower = ofNat k)
    (hm2 : v2.search.mode = .run)
    (hq : GalilScaffoldSearchRun.SafeQuanta v2.search v2.dp usedQ v3.search v3.dp)
    (hm3 : v3.search.mode ≠ .run) :
    ∀ (es1 es2 : List Bool) (v : SearchVM), as ++ bs ++ usedQ = es1 ++ es2 → es2 ≠ [] →
      SearchRun center es1 v0 v →
      v.search.mode ≠ .found ∧ (es2.length = 1 → v.search.mode = .run) := by
  intro es1 es2 v hU hne hv
  -- the shape of the preparation and the run
  obtain ⟨a', bs', hbs⟩ : ∃ a' bs', bs = a' :: bs' := by
    cases hb0 : bs with
    | nil => rw [hb0] at hp; cases hp
    | cons a' bs' => exact ⟨a', bs', rfl⟩
  have husedne : usedQ ≠ [] := by
    intro h0; rw [h0] at hq
    obtain ⟨he, _⟩ := safeQuanta_nil hq
    exact hm3 (by rw [he]; exact hm2)
  obtain ⟨j, hj⟩ : ∃ j, es1.length = j := ⟨_, rfl⟩
  have hes1 : es1 = (as ++ bs ++ usedQ).take j := by rw [← hj, hU, List.take_left]
  have hlenU : (as ++ bs ++ usedQ).length = es1.length + es2.length := by
    rw [hU, List.length_append]
  simp only [List.length_append] at hlenU
  have hes2pos : 0 < es2.length := List.length_pos_iff.mpr hne
  -- three regions
  by_cases hj1 : j ≤ as.length
  · -- inside the grow ticks
    have hes1' : es1 = as.take j := by
      rw [hes1, List.append_assoc, List.take_append_of_le_length hj1]
    rw [hes1'] at hv
    obtain ⟨hg, _⟩ := searchRun_grow_prefix center (as.take j) as.length hv hm0 hw0
      (by rw [List.length_take]; omega)
    refine ⟨by rw [hg]; decide, fun h1len => ?_⟩
    exfalso
    have hbl : 1 ≤ bs.length := by rw [hbs]; simp
    have hul : 1 ≤ usedQ.length := List.length_pos_iff.mpr husedne
    omega
  · by_cases hj2 : j ≤ as.length + bs.length
    · -- inside the preparation
      have hj1' := Nat.lt_of_not_le hj1
      have hes1' : es1 = as ++ bs.take (j - as.length) := by
        rw [hes1, List.take_append_of_le_length (by rw [List.length_append]; omega),
          List.take_append, List.take_of_length_le (by omega)]
      rw [hes1'] at hv
      obtain ⟨vm1, hv1, hv'⟩ := searchRun_split _ as hv
      have hvm1 := searchRun_unique hv1 h1
      subst vm1
      -- the dispatch tick
      obtain ⟨i, hi⟩ : ∃ i, j - as.length = i + 1 := ⟨j - as.length - 1, by omega⟩
      rw [hi, hbs, List.take_succ_cons] at hv'
      cases hv' with
      | cons hstep hrest =>
        rename_i v1'
        have hv1' : v1' = SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a'
            (GalilScaffoldPrepareControl.prepare v1.toPrep v1.lower center)) v1.search.quarter v1.lower := by
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
          -- split the paced body at i
          have hsplitb : bs' = bs'.take i ++ bs'.drop i := (List.take_append_drop i bs').symm
          rw [hsplitb] at hrun
          obtain ⟨y, hy1, hy2⟩ := pacedPrepared_split _ _ hrun
          have hpref : SearchRun center (((List.replicate (bs'.take i).length true).zip (bs'.take i)).map Prod.snd)
              v1' v := by
            rw [map_snd_zip_replicate]; exact hrest
          obtain ⟨hvy, _, _⟩ := searchRun_paced center (all_enabled_zip _) hy1 hpref hx1
          have hil : i ≤ bs'.length := by
            rw [hbs] at hj2; simp only [List.length_cons] at hj2; omega
          by_cases hi2 : i < bs'.length
          · -- a proper prefix of the body
            have hdne : bs'.drop i ≠ [] := by
              intro h0
              have := congrArg List.length h0
              rw [List.length_drop] at this
              simp at this; omega
            obtain ⟨e, es', hd⟩ : ∃ e es', bs'.drop i = e :: es' := by
              cases hd0 : bs'.drop i with
              | nil => exact absurd hd0 hdne
              | cons e es' => exact ⟨e, es', rfl⟩
            rw [hd] at hy2
            simp only [List.length_cons, List.replicate_succ, List.zip_cons_cons] at hy2
            have hpm := pacedRun_cons_prepMode rfl hy2
            rw [← hvy, toPrep_mode] at hpm
            refine ⟨?_, fun h1len => ?_⟩
            · rcases hpm with hpm | hpm | hpm | hpm <;> rw [hpm] <;> decide
            · exfalso
              have hul : 1 ≤ usedQ.length := List.length_pos_iff.mpr husedne
              rw [hbs] at hlenU
              simp only [List.length_cons] at hlenU
              omega
          · -- the whole body: `run`
            have hieq : i = bs'.length := by omega
            have hdnil : bs'.drop i = [] := by rw [hieq, List.drop_length]
            rw [hdnil] at hy2
            simp only [List.length_nil, List.replicate_zero, List.zip_nil_right] at hy2
            cases hy2
            have hvm : v.search.mode = v2.search.mode := by
              rw [← toPrep_mode, hvy, toPrep_mode]
            rw [hvm, hm2]
            exact ⟨by decide, fun _ => rfl⟩
    · -- inside the run quanta
      have hj1' := Nat.lt_of_not_le hj1
      have hj2' := Nat.lt_of_not_le hj2
      have hes1' : es1 = as ++ bs ++ usedQ.take (j - (as.length + bs.length)) := by
        rw [hes1, List.take_append, List.take_of_length_le (by rw [List.length_append]; omega),
          List.length_append]
      rw [hes1', List.append_assoc] at hv
      obtain ⟨vm1, hv1, hv'⟩ := searchRun_split _ as hv
      have hvm1 := searchRun_unique hv1 h1
      subst vm1
      obtain ⟨vm2, hv2, hv''⟩ := searchRun_split _ bs hv'
      have hvm2 := searchRun_unique hv2 h2
      subst vm2
      obtain ⟨i, hi⟩ : ∃ i, j - (as.length + bs.length) = i := ⟨_, rfl⟩
      rw [hi] at hv''
      have hdne : usedQ.drop i ≠ [] := by
        intro h0
        have := congrArg List.length h0
        rw [List.length_drop] at this
        simp at this; omega
      have hq' : GalilScaffoldSearchRun.SafeQuanta v2.search v2.dp (usedQ.take i ++ usedQ.drop i)
          v3.search v3.dp := by rw [List.take_append_drop]; exact hq
      obtain ⟨m, y', hqm, hmm⟩ := safeQuanta_prefix_run _ _ hdne hq'
      have hv''' : SearchRun center (usedQ.take i ++ []) v2 v := by rw [List.append_nil]; exact hv''
      obtain ⟨vq, _, hsq, _, _, _, hnil⟩ := searchRun_quanta center hqm hv''' rfl rfl
      cases hnil
      rw [hsq, hmm]
      exact ⟨by decide, fun _ => rfl⟩

#print axioms stage_prefix_mode

end PalPeg.GalilScaffoldChainInputSupply
