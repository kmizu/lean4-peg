import PalPeg.GalilScaffoldTopSearchStage

/-!
# Determinism and prefixes of the search's run

`searchStep` is deterministic (the preparation ticks by `tick_unique`, the
run quanta by `safe_quanta_unique`, the other modes being functions), so
`SearchRun` is. Prefix forms of the phase identifications: a prefix of the
grow ticks stays in `grow`, a proper prefix of a paced preparation stays in
a preparation mode, a proper prefix of the run quanta stays in `run`.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

theorem searchStep_unique {center : GalilScaffoldPlace.Place} {a : Bool} {v v1 v2 : SearchVM}
    (h1 : searchStep center a v v1) (h2 : searchStep center a v v2) : v1 = v2 := by
  unfold searchStep at h1 h2
  cases hm : v.search.mode <;> rw [hm] at h1 h2
  · exact h1.trans h2.symm
  · cases hp : positive v.search.work
    · simp only [hp, Bool.false_eq_true, if_false] at h1 h2; exact h1.trans h2.symm
    · simp only [hp, if_true] at h1 h2; exact h1.trans h2.symm
  · obtain ⟨y1, ht1, hv1⟩ := h1
    obtain ⟨y2, ht2, hv2⟩ := h2
    rw [hv1, hv2, Prep.tick_unique ht1 ht2]
  · obtain ⟨y1, ht1, hv1⟩ := h1
    obtain ⟨y2, ht2, hv2⟩ := h2
    rw [hv1, hv2, Prep.tick_unique ht1 ht2]
  · obtain ⟨y1, ht1, hv1⟩ := h1
    obtain ⟨y2, ht2, hv2⟩ := h2
    rw [hv1, hv2, Prep.tick_unique ht1 ht2]
  · obtain ⟨y1, ht1, hv1⟩ := h1
    obtain ⟨y2, ht2, hv2⟩ := h2
    rw [hv1, hv2, Prep.tick_unique ht1 ht2]
  · obtain ⟨hq1, hl1, hw1⟩ := h1
    obtain ⟨hq2, hl2, hw2⟩ := h2
    obtain ⟨hs, hd⟩ := safe_quanta_unique hq1 hq2
    cases v1; cases v2
    simp only at hs hd hl1 hl2 hw1 hw2
    simp [hs, hd, hl1, hl2, hw1, hw2]
  · exact h1.trans h2.symm
  · exact h1.trans h2.symm
  · exact h1.trans h2.symm
  · cases hp : positive v.search.work
    · simp only [hp, Bool.false_eq_true, if_false] at h1 h2; exact h1.trans h2.symm
    · simp only [hp, if_true] at h1 h2; exact h1.trans h2.symm

theorem searchRun_unique {center : GalilScaffoldPlace.Place} {es : List Bool} :
    ∀ {v v1 v2 : SearchVM}, SearchRun center es v v1 → SearchRun center es v v2 → v1 = v2 := by
  induction es with
  | nil => intro v v1 v2 h1 h2; cases h1; cases h2; rfl
  | cons a es ih =>
    intro v v1 v2 h1 h2
    cases h1 with
    | cons hs1 hr1 =>
      cases h2 with
      | cons hs2 hr2 =>
        have := searchStep_unique hs1 hs2
        subst this
        exact ih hr1 hr2

/-- A prefix of the grow ticks stays in `grow`, with the remaining work. -/
theorem searchRun_grow_prefix (center : GalilScaffoldPlace.Place) (as : List Bool) :
    ∀ {v v' : SearchVM} (n : ℕ), SearchRun center as v v' → v.search.mode = .grow →
      v.search.work = ofNat n → as.length ≤ n →
      v'.search.mode = .grow ∧ v'.search.work = ofNat (n - as.length) := by
  induction as with
  | nil => intro v v' n h hm hw _; cases h; exact ⟨hm, by simpa using hw⟩
  | cons a as ih =>
    intro v v'' n h hm hw hlen
    cases h with
    | cons hstep hrest =>
      rename_i v'
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hlen; omega⟩
      have hpos : positive v.search.work = true := by rw [hw, positive_ofNat]; simp
      have hv' : v' = SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a
          (GalilScaffoldStagePrepare.growStep v.toPrep)) v.search.quarter v.lower := by
        unfold searchStep at hstep
        rw [hm] at hstep
        simp only [hpos, if_true] at hstep
        exact hstep
      have hm' : v'.search.mode = .grow := by
        rw [hv', ofPrep_mode, afterAdvance_mode]; exact hm
      have hw' : v'.search.work = ofNat m := by
        rw [hv', ofPrep_work, afterAdvance_work]
        show dec v.search.work = _
        rw [hw]
        exact dec_ofNat_succ _
      have := ih m hrest hm' hw' (by simp at hlen; omega)
      simpa [Nat.succ_sub_succ] using this

theorem pacedRun_split {x z : GalilScaffoldPrepareControl.State} (l1 : List (Bool × Bool)) :
    ∀ {l2 : List (Bool × Bool)}, GalilScaffoldPreparePaced.PacedRun x (l1 ++ l2) z →
      ∃ y, GalilScaffoldPreparePaced.PacedRun x l1 y ∧ GalilScaffoldPreparePaced.PacedRun y l2 z := by
  induction l1 generalizing x with
  | nil => intro l2 h; exact ⟨x, .nil _, h⟩
  | cons e l1 ih =>
    intro l2 h
    cases h with
    | cons _ y _ enabled advance _ ht hr =>
      obtain ⟨m, h1, h2⟩ := ih hr
      exact ⟨m, .cons _ _ _ enabled advance _ ht h1, h2⟩

theorem pacedRun_cons_prepMode {x z : GalilScaffoldPrepareControl.State} {e : Bool × Bool}
    {es : List (Bool × Bool)} (he : e.1 = true)
    (h : GalilScaffoldPreparePaced.PacedRun x (e :: es) z) : PrepMode x.mode := by
  cases h with
  | cons _ _ _ enabled _ _ ht _ =>
    have : enabled = true := he
    subst this
    exact tick_prepMode ht

/-- A proper prefix of the run quanta ends in `run`. -/
theorem safeQuanta_prefix_run {s t : GalilScaffoldSearchFinish.State} {x y : GalilScaffoldControl.Machine 12}
    (l1 l2 : List Bool) (hne : l2 ≠ [])
    (h : GalilScaffoldSearchRun.SafeQuanta s x (l1 ++ l2) t y) :
    ∃ m y', GalilScaffoldSearchRun.SafeQuanta s x l1 m y' ∧ m.mode = .run := by
  obtain ⟨m, y', h1, h2⟩ := safe_quanta_append l1 l2 h
  refine ⟨m, y', h1, ?_⟩
  cases l2 with
  | nil => exact absurd rfl hne
  | cons b bs => exact safe_quanta_cons_run h2

#print axioms searchRun_unique
#print axioms searchRun_grow_prefix

end PalPeg.GalilScaffoldChainInputSupply
