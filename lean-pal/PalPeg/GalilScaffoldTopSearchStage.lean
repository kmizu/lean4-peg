import PalPeg.GalilScaffoldTopSearchRun

/-!
# Identifying the search's run with the staged search

The search driven by a chain-idle segment (`SearchRun`) is deterministic
and its phases are the lower layer's runs: the grow ticks are
`PacedGrowing`, the prepare dispatch and its body are `PacedPrepared`, the
run quanta are `SafeQuanta`. Given the lower layer's existence results
(`first_stage_chain_run`), the actual run passes through the same states,
so its search lands in an exit mode with the DP result on its program.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

theorem toPrep_ofPrep (p : GalilScaffoldPrepareControl.State) (quarter : Fin 4) (lower : Counter) :
    (SearchVM.ofPrep p quarter lower).toPrep = p := rfl

theorem ofPrep_quarter (p : GalilScaffoldPrepareControl.State) (quarter : Fin 4) (lower : Counter) :
    (SearchVM.ofPrep p quarter lower).search.quarter = quarter := rfl

theorem ofPrep_lower (p : GalilScaffoldPrepareControl.State) (quarter : Fin 4) (lower : Counter) :
    (SearchVM.ofPrep p quarter lower).lower = lower := rfl

theorem ofPrep_mode (p : GalilScaffoldPrepareControl.State) (quarter : Fin 4) (lower : Counter) :
    (SearchVM.ofPrep p quarter lower).search.mode = p.mode := rfl

theorem ofPrep_work (p : GalilScaffoldPrepareControl.State) (quarter : Fin 4) (lower : Counter) :
    (SearchVM.ofPrep p quarter lower).search.work = p.work := rfl

theorem toPrep_mode (v : SearchVM) : v.toPrep.mode = v.search.mode := rfl
theorem toPrep_work (v : SearchVM) : v.toPrep.work = v.search.work := rfl

/-! ## The grow phase -/

theorem afterAdvance_mode (a : Bool) (p : GalilScaffoldPrepareControl.State) :
    (GalilScaffoldPreparePaced.afterAdvance a p).mode = p.mode := by
  cases a <;> rfl

theorem afterAdvance_work (a : Bool) (p : GalilScaffoldPrepareControl.State) :
    (GalilScaffoldPreparePaced.afterAdvance a p).work = p.work := by
  cases a <;> rfl

/-- `n` grow ticks from work `n` are the paced growing of the lower layer,
ending in `grow` with no work. -/
theorem searchRun_growing (center : GalilScaffoldPlace.Place) (as : List Bool) :
    ∀ {v v' : SearchVM}, SearchRun center as v v' → v.search.mode = .grow →
      v.search.work = ofNat as.length →
      GalilScaffoldStagePrepare.PacedGrowing v.toPrep as v'.toPrep ∧
        v'.search.quarter = v.search.quarter ∧ v'.lower = v.lower ∧
        v'.search.mode = .grow ∧ v'.search.work = ofNat 0 := by
  induction as with
  | nil =>
    intro v v' h hm hw
    cases h
    refine ⟨.stop _ hm ?_, rfl, rfl, hm, hw⟩
    rw [toPrep_work, hw]; rfl
  | cons a as ih =>
    intro v v'' h hm hw
    cases h with
    | cons hstep hrest =>
      rename_i v'
      have hpos : positive v.search.work = true := by
        rw [hw, positive_ofNat]; simp
      have hv' : v' = SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a
          (GalilScaffoldStagePrepare.growStep v.toPrep)) v.search.quarter v.lower := by
        unfold searchStep at hstep
        rw [hm] at hstep
        simp only [hpos, if_true] at hstep
        exact hstep
      have hm' : v'.search.mode = .grow := by
        rw [hv', ofPrep_mode, afterAdvance_mode]; exact hm
      have hw' : v'.search.work = ofNat as.length := by
        rw [hv', ofPrep_work, afterAdvance_work]
        show dec v.search.work = _
        rw [hw]
        simp only [List.length_cons]
        exact dec_ofNat_succ _
      obtain ⟨hg, hq, hl, hm'', hw''⟩ := ih hrest hm' hw'
      refine ⟨?_, ?_, ?_, hm'', hw''⟩
      · rw [hv', toPrep_ofPrep] at hg
        exact .next _ _ a as hm hpos hg
      · rw [hq, hv', ofPrep_quarter]
      · rw [hl, hv', ofPrep_lower]

/-- Paced growing is deterministic. -/
theorem pacedGrowing_unique {s : GalilScaffoldPrepareControl.State} {as : List Bool}
    {t t' : GalilScaffoldPrepareControl.State}
    (h1 : GalilScaffoldStagePrepare.PacedGrowing s as t)
    (h2 : GalilScaffoldStagePrepare.PacedGrowing s as t') : t = t' := by
  induction h1 with
  | stop s _ _ => cases h2; rfl
  | next s t a as _ _ _ ih =>
    cases h2 with
    | next _ _ _ _ _ _ hr => exact ih hr

/-! ## The preparation phase -/

def PrepMode (m : GalilScaffoldSearchFinish.Mode) : Prop :=
  m = .lower ∨ m = .lowerHome ∨ m = .copy ∨ m = .home

theorem tick_prepMode {x y : GalilScaffoldPrepareControl.State}
    (h : GalilScaffoldPrepareControl.Tick true x y) : PrepMode x.mode := by
  cases h with
  | lowerBit _ hm _ => exact Or.inl hm
  | lowerEnd _ hm _ => exact Or.inl hm
  | lowerLeft _ hm _ _ => exact Or.inr (Or.inl hm)
  | beginCopy _ hm _ => exact Or.inr (Or.inl hm)
  | copyBit _ _ hm _ _ => exact Or.inr (Or.inr (Or.inl hm))
  | copyEnd _ hm _ => exact Or.inr (Or.inr (Or.inl hm))
  | sourceLeft _ hm _ _ => exact Or.inr (Or.inr (Or.inr hm))
  | startRun _ hm _ => exact Or.inr (Or.inr (Or.inr hm))

theorem searchStep_prep {center : GalilScaffoldPlace.Place} {a : Bool} {v v' : SearchVM}
    (h : searchStep center a v v') (hm : PrepMode v.search.mode) :
    ∃ y, GalilScaffoldPrepareControl.Tick true v.toPrep y ∧
      v' = SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a y) v.search.quarter v.lower := by
  unfold searchStep at h
  rcases hm with hm | hm | hm | hm <;> rw [hm] at h <;> exact h

/-- A fully enabled paced run of the lower layer is followed by the actual
search, state by state. -/
theorem searchRun_paced (center : GalilScaffoldPlace.Place) {x z : GalilScaffoldPrepareControl.State}
    {es : List (Bool × Bool)} (hall : ∀ e ∈ es, e.1 = true)
    (hr : GalilScaffoldPreparePaced.PacedRun x es z) :
    ∀ {v v' : SearchVM}, SearchRun center (es.map Prod.snd) v v' → v.toPrep = x →
      v'.toPrep = z ∧ v'.search.quarter = v.search.quarter ∧ v'.lower = v.lower := by
  induction hr with
  | nil x =>
    intro v v' h hx
    cases h
    exact ⟨hx, rfl, rfl⟩
  | cons x y z enabled advance es ht _ ih =>
    intro v v'' h hx
    have he : enabled = true := hall _ (List.mem_cons.2 (Or.inl rfl))
    subst he
    simp only [List.map_cons] at h
    cases h with
    | cons hstep hrest =>
      rename_i v'
      have hpm : PrepMode v.search.mode := by
        rw [← toPrep_mode, hx]; exact tick_prepMode ht
      obtain ⟨y', hy', hv'⟩ := searchStep_prep hstep hpm
      rw [hx] at hy'
      have hyy := Prep.tick_unique hy' ht
      subst hyy
      have hx' : v'.toPrep = GalilScaffoldPreparePaced.afterAdvance advance y' := by
        rw [hv', toPrep_ofPrep]
      obtain ⟨hz, hq, hl⟩ := ih (fun e he => hall e (List.mem_cons_of_mem _ he)) hrest hx'
      refine ⟨hz, ?_, ?_⟩
      · rw [hq, hv', ofPrep_quarter]
      · rw [hl, hv', ofPrep_lower]

theorem map_snd_zip_replicate (bs : List Bool) :
    ((List.replicate bs.length true).zip bs).map Prod.snd = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [List.replicate_succ, List.zip_cons_cons, ih]

/-- The prepare dispatch and its body, from a grow state without work, are
the lower layer's paced preparation. -/
theorem searchRun_prepared (center : GalilScaffoldPlace.Place) {x p : GalilScaffoldPrepareControl.State}
    {a : Bool} {bs : List Bool} {lowerC : Counter}
    (hp : GalilScaffoldPreparePaced.PacedPrepared lowerC center x (a :: bs) p)
    {v v' : SearchVM} (h : SearchRun center (a :: bs) v v') (hx : v.toPrep = x)
    (hm : v.search.mode = .grow) (hw : positive v.search.work = false) (hl : v.lower = lowerC) :
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

/-! ## The run phase -/

/-- A single quantum: 64 safe calls then the advance. -/
theorem safeQuanta_single {s t : GalilScaffoldSearchFinish.State} {x y : GalilScaffoldControl.Machine 12}
    {a : Bool} (h : GalilScaffoldSearchRun.SafeQuanta s x [a] t y) :
    ∃ u y', GalilScaffoldSearchRun.SafeCalls s x (List.replicate 64 true) u y' ∧
      t = GalilScaffoldSearchRun.advance a u ∧ y = y' :=
  match h with
  | .cons _ u _ _ y' _ _ _ _ hcalls hr =>
    match hr with
    | .nil _ _ => ⟨u, y', hcalls, rfl, rfl⟩

/-- The run quanta of the lower layer are followed by the actual search. -/
theorem searchRun_quanta (center : GalilScaffoldPlace.Place)
    {s t : GalilScaffoldSearchFinish.State} {x y : GalilScaffoldControl.Machine 12}
    {used : List Bool} (hq : GalilScaffoldSearchRun.SafeQuanta s x used t y) :
    ∀ {rest : List Bool} {v v' : SearchVM}, SearchRun center (used ++ rest) v v' →
      v.search = s → v.dp = x →
      ∃ v1 : SearchVM, SearchRun center used v v1 ∧ v1.search = t ∧ v1.dp = y ∧
        v1.lower = v.lower ∧ v1.walker = v.walker ∧ SearchRun center rest v1 v' := by
  induction hq with
  | nil s x =>
    intro rest v v' h hs hx
    exact ⟨v, .nil _, hs, hx, rfl, rfl, by simpa using h⟩
  | cons s u t x y z a as hm hcalls _ ih =>
    intro rest v v'' h hs hx
    simp only [List.cons_append] at h
    cases h with
    | cons hstep hrest =>
      rename_i v1
      have hrun : v.search.mode = .run := by rw [hs]; exact hm
      have hsq : GalilScaffoldSearchRun.SafeQuanta v.search v.dp [a] v1.search v1.dp ∧
          v1.lower = v.lower ∧ v1.walker = v.walker := by
        unfold searchStep at hstep
        rw [hrun] at hstep
        exact hstep
      obtain ⟨hsq1, hl1, hw1⟩ := hsq
      rw [hs, hx] at hsq1
      obtain ⟨u', y', hcalls', hs1, hx1⟩ := safeQuanta_single hsq1
      obtain ⟨rfl, rfl⟩ := safe_calls_unique hcalls' hcalls
      obtain ⟨v2, h1, hs2, hx2, hl2, hw2, h2⟩ := ih hrest hs1 hx1
      refine ⟨v2, .cons hstep h1, hs2, hx2, ?_, ?_, h2⟩
      · rw [hl2, hl1]
      · rw [hw2, hw1]

#print axioms searchRun_growing
#print axioms searchRun_prepared
#print axioms searchRun_quanta

end PalPeg.GalilScaffoldChainInputSupply
