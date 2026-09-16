import PalPeg.GalilScaffoldTopProgressS
import PalPeg.GalilScaffoldChainFallback

/-!
# Branch-coverage obligations (iii) and (iv)

`ASSEMBLY_PLAN.md`, 「分岐網羅の義務」, items (iii) and (iv).
-/

set_option autoImplicit false
namespace PalPeg.GalilBranchInvariants2

open GalilScaffoldTape (Tape)

/-! ## (iii) The preparation left-end guards -/

/-- The `LEFT` mark (`4`) sits strictly to the left of the head. -/
def Marked (t : Tape) : Prop := (4 : Fin 9) ∈ t.left

/-- The head is on the `LEFT` mark, or the mark is still to its left. -/
def Anchored (t : Tape) : Prop := t.focus = 4 ∨ (4 : Fin 9) ∈ t.left

theorem anchored_of_marked {t : Tape} (h : Marked t) : Anchored t := Or.inr h

/-- Reachability invariant of the preparation controller: in the two writing
modes the `LEFT` mark is strictly left of the head, in the two rewinding
modes it is at or left of the head. -/
def PrepInv (x : GalilScaffoldPrepareControl.State) : Prop :=
  (x.mode = .lower → Marked (x.program.config.tapes 10)) ∧
  (x.mode = .lowerHome → Anchored (x.program.config.tapes 10)) ∧
  (x.mode = .copy → Marked (x.program.config.tapes 7)) ∧
  (x.mode = .home → Anchored (x.program.config.tapes 7))

/-! ### Tape-level facts -/

theorem left_moveRight (t : Tape) :
    (GalilScaffoldTape.moveRight t).left = t.focus :: t.left := by
  rcases t with ⟨l, f, r⟩
  cases r <;> rfl

theorem marked_moveRight {t : Tape} (h : Anchored t) :
    Marked (GalilScaffoldTape.moveRight t) := by
  rw [Marked, left_moveRight]
  rcases h with h | h
  · exact List.mem_cons.mpr (Or.inl h.symm)
  · exact List.mem_cons.mpr (Or.inr h)

theorem marked_write {t : Tape} (s : Fin 9) (h : Marked t) :
    Marked (GalilScaffoldTape.write t s) := h

theorem anchored_moveLeft {t : Tape} (h : Anchored t) (hf : t.focus ≠ 4) :
    Anchored (GalilScaffoldTape.moveLeft t) := by
  rcases h with h | h
  · exact absurd h hf
  · rcases t with ⟨l, f, r⟩
    cases l with
    | nil => exact absurd h (by simp)
    | cons a ls =>
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr h

/-! ### The two tape projections of a preparation tick -/

theorem tape_same (x : GalilScaffoldPrepareControl.State) (i : Fin 12) (f : Tape → Tape) :
    (GalilScaffoldPrepareControl.tape x i f).config.tapes i = f (x.program.config.tapes i) := by
  simp [GalilScaffoldPrepareControl.tape, GalilScaffoldLoading.put]

theorem tape_other (x : GalilScaffoldPrepareControl.State) (i j : Fin 12) (f : Tape → Tape)
    (h : j ≠ i) :
    (GalilScaffoldPrepareControl.tape x i f).config.tapes j = x.program.config.tapes j := by
  simp [GalilScaffoldPrepareControl.tape, GalilScaffoldLoading.put, h]

/-! ### `PrepInv` holds at the entry and is preserved by every tick -/

open GalilScaffoldPrepareControl (State Tick Run prepare)

/-- `PrepareControl.prepare` (the dispatch that enters `.lower`) writes the
`LEFT` mark and steps right, so the invariant holds at the entry. -/
theorem prepInv_prepare (s : State) (lower : GalilScaffoldCounter.Counter)
    (center : GalilScaffoldPlace.Place) : PrepInv (prepare s lower center) := by
  refine ⟨fun _ => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · show Marked _
    have : (prepare s lower center).program.config.tapes 10 =
        GalilScaffoldTape.moveRight (GalilScaffoldTape.write GalilScaffoldTape.reset 4) := by
      simp [prepare, GalilScaffoldLoading.put]
    rw [this, Marked, left_moveRight]
    exact List.mem_cons_self ..
  all_goals exact absurd h (by simp [prepare])

/-- Every preparation tick preserves `PrepInv`, unconditionally. -/
theorem prepInv_tick {x y : State} {b : Bool} (ht : Tick b x y) (h : PrepInv x) : PrepInv y := by
  obtain ⟨hL, hH, hC, hM⟩ := h
  cases ht with
  | idle x => exact ⟨hL, hH, hC, hM⟩
  | lowerBit x hm hp =>
    refine ⟨fun _ => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · show Marked ((GalilScaffoldPrepareControl.tape x 10 _).config.tapes 10)
      rw [tape_same]
      exact marked_moveRight (anchored_of_marked (marked_write 8 (hL hm)))
    all_goals exact absurd (hm ▸ h) (by simp)
  | lowerEnd x hm hp =>
    refine ⟨fun h => ?_, fun _ => ?_, fun h => ?_, fun h => ?_⟩
    · exact absurd h (by simp)
    · show Anchored ((GalilScaffoldPrepareControl.tape x 10 _).config.tapes 10)
      rw [tape_same]
      exact anchored_of_marked (marked_write 5 (hL hm))
    all_goals exact absurd h (by simp)
  | lowerLeft x hm hf hl =>
    refine ⟨fun h => ?_, fun _ => ?_, fun h => ?_, fun h => ?_⟩
    · exact absurd (hm ▸ h) (by simp)
    · show Anchored ((GalilScaffoldPrepareControl.tape x 10 _).config.tapes 10)
      rw [tape_same]
      exact anchored_moveLeft (hH hm) hf
    all_goals exact absurd (hm ▸ h) (by simp)
  | beginCopy x hm hf =>
    refine ⟨fun h => ?_, fun h => ?_, fun _ => ?_, fun h => ?_⟩
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · show Marked ((GalilScaffoldPrepareControl.tape x 7 _).config.tapes 7)
      rw [tape_same]
      exact marked_moveRight (Or.inl rfl)
    · exact absurd h (by simp)
  | copyBit x a hm ha hw =>
    refine ⟨fun h => ?_, fun h => ?_, fun _ => ?_, fun h => ?_⟩
    · exact absurd (hm ▸ h) (by simp)
    · exact absurd (hm ▸ h) (by simp)
    · show Marked ((GalilScaffoldPrepareControl.tape x 7 _).config.tapes 7)
      rw [tape_same]
      exact marked_moveRight (anchored_of_marked (marked_write _ (hC hm)))
    · exact absurd (hm ▸ h) (by simp)
  | copyEnd x hm he =>
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun _ => ?_⟩
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · show Anchored ((GalilScaffoldPrepareControl.tape x 7 _).config.tapes 7)
      rw [tape_same]
      exact anchored_of_marked (marked_write 5 (hC hm))
  | sourceLeft x hm hf hl =>
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun _ => ?_⟩
    · exact absurd (hm ▸ h) (by simp)
    · exact absurd (hm ▸ h) (by simp)
    · exact absurd (hm ▸ h) (by simp)
    · show Anchored ((GalilScaffoldPrepareControl.tape x 7 _).config.tapes 7)
      rw [tape_same]
      exact anchored_moveLeft (hM hm) hf
  | startRun x hm hf =>
    exact ⟨fun h => absurd h (by simp), fun h => absurd h (by simp),
      fun h => absurd h (by simp), fun h => absurd h (by simp)⟩

theorem prepInv_run {x y : State} {bs : List Bool} (hr : Run x bs y) (h : PrepInv x) :
    PrepInv y := by
  induction hr with
  | nil => exact h
  | cons x y z b bs ht _ ih => exact ih (prepInv_tick ht h)

/-! ### Totality of the preparation dispatch (obligation (iii)) -/

/-- Obligation (iii): in every preparation mode a reachable state (one
satisfying `PrepInv`) has an enabled tick.  The only branches that can fail
are `lowerLeft`/`sourceLeft`, whose left-end guard `left ≠ []` is exactly
what `Anchored` supplies once the head is not already on the mark. -/
theorem prep_tick_exists (x : State)
    (hm : x.mode = .lower ∨ x.mode = .lowerHome ∨ x.mode = .copy ∨ x.mode = .home)
    (h : PrepInv x) : ∃ y, Tick true x y := by
  classical
  obtain ⟨hL, hH, hC, hM⟩ := h
  rcases hm with hm | hm | hm | hm
  · by_cases hp : GalilScaffoldCounter.positive x.work = true
    · exact ⟨_, .lowerBit x hm hp⟩
    · exact ⟨_, .lowerEnd x hm (by simpa using hp)⟩
  · by_cases hf : (x.program.config.tapes 10).focus = 4
    · exact ⟨_, .beginCopy x hm hf⟩
    · refine ⟨_, .lowerLeft x hm hf ?_⟩
      rcases hH hm with h4 | h4
      · exact absurd h4 hf
      · intro hnil; rw [hnil] at h4; exact absurd h4 (by simp)
  · by_cases ha : ∃ a, GalilScaffoldPlace.read x.walker = some a
    · obtain ⟨a, ha⟩ := ha
      by_cases hw : GalilScaffoldCounter.zero x.work = false
      · exact ⟨_, .copyBit x a hm ha hw⟩
      · exact ⟨_, .copyEnd x hm (Or.inr (by simpa using hw))⟩
    · refine ⟨_, .copyEnd x hm (Or.inl ?_)⟩
      cases hr : GalilScaffoldPlace.read x.walker with
      | none => rfl
      | some a => exact absurd ⟨a, hr⟩ ha
  · by_cases hf : (x.program.config.tapes 7).focus = 4
    · exact ⟨_, .startRun x hm hf⟩
    · refine ⟨_, .sourceLeft x hm hf ?_⟩
      rcases hM hm with h4 | h4
      · exact absurd h4 hf
      · intro hnil; rw [hnil] at h4; exact absurd h4 (by simp)

/-! ## (iv) Quantum safety of a reachable DP configuration -/

open GalilScaffoldSearchRun (SafeQuanta SafeCalls advance)

/-- A DP configuration is *reachable* when it is what a safe run of the
preloaded DP machine reaches after some prefix `bs` of outer events.  This is
the invariant asked for by obligation (iv): `quantum64_safe`/`dp_quanta_safe`
only speak about `⟨GalilScaffoldPreload.initial w lower, false⟩`, so a
mid-run configuration must be certified as a suffix of such a run. -/
def DpReached (w : List (Fin 3)) (lower : ℕ) (s0 : GalilScaffoldSearchFinish.State)
    (bs : List Bool) (s : GalilScaffoldSearchFinish.State)
    (x : GalilScaffoldControl.Machine 12) : Prop :=
  SafeQuanta s0 ⟨GalilScaffoldPreload.initial w lower, false⟩ bs s x

/-- The preload entry configuration is reachable (empty event prefix). -/
theorem dpReached_start (w : List (Fin 3)) (lower : ℕ)
    (s0 : GalilScaffoldSearchFinish.State) :
    DpReached w lower s0 [] s0 ⟨GalilScaffoldPreload.initial w lower, false⟩ :=
  SafeQuanta.nil _ _

theorem safe_quanta_trans {s m t : GalilScaffoldSearchFinish.State}
    {x y z : GalilScaffoldControl.Machine 12} {as bs : List Bool}
    (h1 : SafeQuanta s x as m y) (h2 : SafeQuanta m y bs t z) :
    SafeQuanta s x (as ++ bs) t z := by
  induction h1 with
  | nil => simpa using h2
  | cons s u t x y z a as hm hq _ ih =>
    exact .cons s u _ x y _ a _ hm hq (ih h2)

/-- Reachability is preserved by every further safe quantum. -/
theorem dpReached_step {w : List (Fin 3)} {lower : ℕ}
    {s0 s t : GalilScaffoldSearchFinish.State} {bs cs : List Bool}
    {x y : GalilScaffoldControl.Machine 12}
    (h : DpReached w lower s0 bs s x) (hq : SafeQuanta s x cs t y) :
    DpReached w lower s0 (bs ++ cs) t y :=
  safe_quanta_trans h hq

theorem safe_quanta_nil {s t : GalilScaffoldSearchFinish.State}
    {x y : GalilScaffoldControl.Machine 12} (h : SafeQuanta s x [] t y) : t = s ∧ y = x := by
  cases h; exact ⟨rfl, rfl⟩

/-- Obligation (iv): from a reachable DP configuration that is still in `run`
mode, the remaining budget carries a safe quantum run to the halt, with the
DP result.  The proof splits the certified whole-run of `dp_quanta_safe` at
the already-consumed prefix, using `safe_quanta_unique` to identify the
midpoint with the given configuration. -/
theorem safeQuanta_exists_of_reached (w : List (Fin 3)) (lower : ℕ) (bs as : List Bool)
    (s0 s : GalilScaffoldSearchFinish.State) (x : GalilScaffoldControl.Machine 12)
    (ha : 3186*w.length+1683 ≤ 64*(bs ++ as).length)
    (hs0 : s0.mode = .run) (hc : GalilScaffoldCounter.Canonical s0.debt)
    (hb : (((bs ++ as).count true : ℤ)) ≤ GalilScaffoldCounter.value s0.debt)
    (hreach : DpReached w lower s0 bs s x) (hrun : s.mode = .run) :
    ∃ used rest t v, as = used ++ rest ∧ SafeQuanta s x used t ⟨v, true⟩ ∧
      t.mode ≠ .run ∧ GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote v) := by
  obtain ⟨used, rest, t, v, hsplit, hq, hmode, hres, _, _, _⟩ :=
    GalilScaffoldSearchRun.dp_quanta_safe w lower (bs ++ as) ha s0 hs0 hc hb
  rcases List.append_eq_append_iff.mp hsplit with ⟨c, hu, hr⟩ | ⟨c, hu, hr⟩
  · -- the certified run goes strictly past the consumed prefix
    subst hu
    obtain ⟨m, y, h1, h2⟩ := GalilScaffoldChainInputSupply.safe_quanta_append bs c hq
    obtain ⟨rfl, rfl⟩ := GalilScaffoldChainInputSupply.safe_quanta_unique h1 hreach
    exact ⟨c, rest, t, v, hr, h2, hmode, hres⟩
  · -- the certified run halted inside the consumed prefix: impossible
    exfalso
    subst hu
    obtain ⟨m, y, h1, h2⟩ := GalilScaffoldChainInputSupply.safe_quanta_append used c hreach
    obtain ⟨rfl, rfl⟩ := GalilScaffoldChainInputSupply.safe_quanta_unique h1 hq
    cases c with
    | nil =>
      obtain ⟨rfl, _⟩ := safe_quanta_nil h2
      exact hmode hrun
    | cons b c => exact hmode (GalilScaffoldChainInputSupply.safe_quanta_cons_run h2)

/-- The single-quantum form used by the scan tick: one 64-call quantum with
any outer event `a` exists at a reachable running DP configuration. -/
theorem quantum_exists_of_reached (w : List (Fin 3)) (lower : ℕ) (bs as : List Bool)
    (s0 s : GalilScaffoldSearchFinish.State) (x : GalilScaffoldControl.Machine 12)
    (ha : 3186*w.length+1683 ≤ 64*(bs ++ as).length)
    (hs0 : s0.mode = .run) (hc : GalilScaffoldCounter.Canonical s0.debt)
    (hb : (((bs ++ as).count true : ℤ)) ≤ GalilScaffoldCounter.value s0.debt)
    (hreach : DpReached w lower s0 bs s x) (hrun : s.mode = .run) (a : Bool) :
    ∃ t y, SafeQuanta s x [a] t y := by
  obtain ⟨used, rest, t, v, _, hq, hmode, _⟩ :=
    safeQuanta_exists_of_reached w lower bs as s0 s x ha hs0 hc hb hreach hrun
  cases used with
  | nil =>
    obtain ⟨rfl, _⟩ := safe_quanta_nil hq
    exact absurd hrun hmode
  | cons b us =>
    cases hq with
    | cons _ u _ _ y _ _ _ hm hcalls _ =>
      exact ⟨advance a u, y, .cons s u _ x y y a [] hm hcalls (.nil _ _)⟩

/-! ## The two obligations discharge the search side of `backgroundS_exists` -/

open GalilScaffoldChainInputSupply (SearchVM searchStep searchEffect searchLens)

/-- The budget side conditions of obligation (iv), packaged at one
configuration. -/
def DpSafeHere (s : GalilScaffoldSearchFinish.State)
    (x : GalilScaffoldControl.Machine 12) : Prop :=
  ∃ (w : List (Fin 3)) (lower : ℕ) (s0 : GalilScaffoldSearchFinish.State) (bs as : List Bool),
    3186*w.length+1683 ≤ 64*(bs ++ as).length ∧ s0.mode = .run ∧
    GalilScaffoldCounter.Canonical s0.debt ∧
    (((bs ++ as).count true : ℤ)) ≤ GalilScaffoldCounter.value s0.debt ∧
    DpReached w lower s0 bs s x

/-- The reachability hypotheses of obligations (iii) and (iv) on the search
projection of the unified VM. -/
def SearchReady (v : SearchVM) : Prop :=
  PrepInv v.toPrep ∧ (v.search.mode = .run → DpSafeHere v.search v.dp)

/-- Obligations (iii)+(iv): a ready search state has a step on every event,
in every mode.  The inactive, `grow`, `wait` and `double` branches are
functional; `lower`/`lowerHome`/`copy`/`home` are `prep_tick_exists`; `run`
is `quantum_exists_of_reached`. -/
theorem searchStep_exists (center : GalilScaffoldPlace.Place) (a : Bool) (v : SearchVM)
    (h : SearchReady v) : ∃ v', searchStep center a v v' := by
  classical
  obtain ⟨hprep, hdp⟩ := h
  cases hm : v.search.mode with
  | idle => exact ⟨v, by unfold searchStep; rw [hm]⟩
  | found => exact ⟨v, by unfold searchStep; rw [hm]⟩
  | missed => exact ⟨v, by unfold searchStep; rw [hm]⟩
  | grow =>
    by_cases hp : GalilScaffoldCounter.positive v.search.work = true
    · exact ⟨_, by unfold searchStep; rw [hm]; simp only [if_pos hp]; rfl⟩
    · exact ⟨_, by unfold searchStep; rw [hm]; simp only [if_neg hp]; rfl⟩
  | wait => exact ⟨_, by unfold searchStep; rw [hm]⟩
  | double =>
    by_cases hp : GalilScaffoldCounter.positive v.search.work = true
    · exact ⟨_, by unfold searchStep; rw [hm]; simp only [if_pos hp]; rfl⟩
    · exact ⟨_, by unfold searchStep; rw [hm]; simp only [if_neg hp]; rfl⟩
  | lower =>
    obtain ⟨y, hy⟩ := prep_tick_exists v.toPrep (Or.inl hm) hprep
    exact ⟨_, by unfold searchStep; rw [hm]; exact ⟨y, hy, rfl⟩⟩
  | lowerHome =>
    obtain ⟨y, hy⟩ := prep_tick_exists v.toPrep (Or.inr (Or.inl hm)) hprep
    exact ⟨_, by unfold searchStep; rw [hm]; exact ⟨y, hy, rfl⟩⟩
  | copy =>
    obtain ⟨y, hy⟩ := prep_tick_exists v.toPrep (Or.inr (Or.inr (Or.inl hm))) hprep
    exact ⟨_, by unfold searchStep; rw [hm]; exact ⟨y, hy, rfl⟩⟩
  | home =>
    obtain ⟨y, hy⟩ := prep_tick_exists v.toPrep (Or.inr (Or.inr (Or.inr hm))) hprep
    exact ⟨_, by unfold searchStep; rw [hm]; exact ⟨y, hy, rfl⟩⟩
  | run =>
    obtain ⟨w, lower, s0, bs, as, ha, hs0, hc, hb, hreach⟩ := hdp hm
    obtain ⟨t, y, hq⟩ :=
      quantum_exists_of_reached w lower bs as s0 v.search v.dp ha hs0 hc hb hreach hm a
    exact ⟨⟨t, y, v.lower, v.walker⟩, by unfold searchStep; rw [hm]; exact ⟨hq, rfl, rfl⟩⟩

/-- The hypothesis `hsearch` of `backgroundS_exists`/`scan_tick_exists`. -/
theorem searchEffect_exists (P : GalilScaffoldChainInputSupply.Shared) (a : Bool)
    (s : GalilScaffoldChainInputSupply.GalilVM)
    (h : SearchReady (searchLens.get s)) : ∃ vq, searchEffect P a s vq := by
  classical
  by_cases hi : s.chain = GalilScaffoldChainInputSupply.ChainVM.idle
  · obtain ⟨vq, hq⟩ := searchStep_exists (P.place s) a (searchLens.get s) h
    exact ⟨vq, Or.inl ⟨hi, hq⟩⟩
  · exact ⟨searchLens.get s, Or.inr ⟨hi, rfl⟩⟩

#print axioms left_moveRight
#print axioms marked_moveRight
#print axioms marked_write
#print axioms anchored_moveLeft
#print axioms anchored_of_marked
#print axioms tape_same
#print axioms tape_other
#print axioms prepInv_prepare
#print axioms prepInv_tick
#print axioms prepInv_run
#print axioms prep_tick_exists
#print axioms dpReached_start
#print axioms safe_quanta_trans
#print axioms dpReached_step
#print axioms safe_quanta_nil
#print axioms safeQuanta_exists_of_reached
#print axioms quantum_exists_of_reached
#print axioms searchStep_exists
#print axioms searchEffect_exists

end PalPeg.GalilBranchInvariants2
