import PalPeg.PhysicalCacheInvariant

/-! # Storage which the broken-chain restart overwrites

The search is suspended while a chain is active. Its four counters can differ
without changing the scan/chain operation, and restart overwrites them all.
These lemmas identify the semantic freedom needed by a physical copy cache;
they do not assume copies of last or a ready DP reset bank.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalRestartStorage
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (Counter reset positive negative zero)
open PalPeg.PhysicalEncoding
open PalPeg.PhysicalContract
open PalPeg.GalilFinalAssembly2 (centreC placeC)

/-- Only suspended search counters are replaced. Heads, chain, program tapes,
search mode, output control and every other counter stay fixed. -/
def replace (s : GalilVM) (lower span work debt : Counter) : GalilVM :=
  {s with lower := lower, search := {s.search with span := span, work := work, debt := debt}}

@[simp] theorem replace_self (s : GalilVM) :
    replace s s.lower s.search.span s.search.work s.search.debt = s := rfl

@[simp] theorem replace_replace (s : GalilVM) (lower span work debt lo sp wk dt : Counter) :
    replace (replace s lower span work debt) lo sp wk dt = replace s lo sp wk dt := rfl

/-- Storage equivalence retains the values of every live scan component. -/
def Same (s t : GalilVM) : Prop :=
  t = replace s t.lower t.search.span t.search.work t.search.debt

theorem same_replace (s : GalilVM) (lower span work debt : Counter) :
    Same s (replace s lower span work debt) := rfl

theorem same_refl (s : GalilVM) : Same s s := rfl

theorem same_symm {s t : GalilVM} (h : Same s t) : Same t s := by
  unfold Same at h ⊢
  rw [h]
  rfl

theorem same_trans {s t u : GalilVM} (h : Same s t) (g : Same t u) : Same s u := by
  unfold Same at h g ⊢
  rw [h] at g
  exact g

/-- Actual background work cannot observe the dormant counter values. -/
theorem background_replace (P : Shared) (s : GalilVM) (lower span work debt : Counter)
    (ha : s.chain ≠ .idle) :
    backgroundFun P (replace s lower span work debt) =
      replace (backgroundFun P s) lower span work debt := by
  rw [backgroundFun_of_active P (replace s lower span work debt) ha,
    backgroundFun_of_active P s ha]
  rfl

/-- The active chain suppresses the search quantum, including its centre and
place queries. The statement holds for an arbitrary Shared parameter. -/
theorem compare_replace (P : Shared) (s : GalilVM) (lower span work debt : Counter)
    (ha : s.chain ≠ .idle) :
    compareFun P (replace s lower span work debt) =
      replace (compareFun P s) lower span work debt := by
  cases hc : s.chain <;> try exact False.elim (ha hc)
  all_goals
    simp only [compareFun, replace, searchEffectFun, hc, chainAtFun, ChainVM.isIdle,
      chainBorn, Bool.false_and, afterBirth, Bool.false_eq_true, if_false]
    split_ifs <;> rfl

/-- Both scan branch predicates use only retained components. -/
theorem guards_replace (s : GalilVM) (lower span work debt : Counter) :
    restartGuardTest (replace s lower span work debt) = restartGuardTest s ∧
      shiftGuardTest (replace s lower span work debt) = shiftGuardTest s := by
  constructor <;> rfl

/-- Input arrival changes the heads and keeps the same storage freedom. -/
theorem arrive_replace (a : Fin 2) (s : GalilVM) (lower span work debt : Counter) :
    PalPeg.GalilArriveChain.arriveVM' a (replace s lower span work debt) =
      replace (PalPeg.GalilArriveChain.arriveVM' a s) lower span work debt := rfl

/-- The outer waiting decision also ignores suspended search counters. -/
theorem starved_replace (x : State GalilVM) (lower span work debt : Counter) :
    PalPeg.FrameFunction.starvedTest ⟨x.ctl, replace x.vm lower span work debt⟩ =
      PalPeg.FrameFunction.starvedTest x := rfl

/-- Full relational restart, with no premise on the old lower/span/work/debt. -/
theorem restart_replace (entry : ℕ) {s t : GalilVM} (hr : restartVM entry s t)
    (lower span work debt : Counter) : restartVM entry (replace s lower span work debt) t := by
  obtain ⟨wm, hw, hm, hl, hz, rfl⟩ := hr
  exact ⟨wm, hw, hm, hl, hz, rfl⟩

/-- The actual functional restart has exactly the same result. -/
theorem restartFun_replace (entry : ℕ) (s : GalilVM) (lower span work debt : Counter)
    (hg : restartGuardVM s) :
    restartFun entry (replace s lower span work debt) = restartFun entry s := by
  exact (restartFun_eq entry (restart_replace entry (restartFun_spec entry s hg)
    lower span work debt)).symm

/-- A fallback also stops search, so it does not make stale counters live. -/
theorem fallback_replace (place : PalPeg.GalilScaffoldPlace.Place) (s : GalilVM)
    (lower span work debt : Counter) :
    beginFallbackAt place (replace s lower span work debt) =
      replace (beginFallbackAt place s) lower span work debt := rfl

/-- Exactly the values restart asks the physical row to establish. -/
theorem restart_counters (entry : ℕ) {s t : GalilVM} (hr : restartVM entry s t) :
    ∃ wm, s.chain = .broken wm ∧ positive wm.machine.control.last = true ∧
      t.chain = .idle ∧ t.lower = wm.machine.control.last ∧
      t.search.work = wm.machine.control.last ∧ t.search.span = reset ∧
      t.search.debt = PalPeg.GalilScaffoldSearchFinish.initialDebt s.radius ∧
      t.search.mode = .grow ∧ t.dp = PalPeg.GalilScaffoldControl.reset entry s.dp := by
  obtain ⟨wm, hw, hm, hl, hz, rfl⟩ := hr
  have hb := PalPeg.GalilScaffoldSearchFinish.begin_positive wm.machine.control.last s.radius hl
  exact ⟨wm, hw, hl, rfl, rfl, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.1, rfl⟩

/-- Finite control observes none of the four replaced counter values. -/
theorem control_replace (w : List (Fin 2)) (x : State GalilVM) (q : CoreControl)
    (he : EncControl w x q) (lower span work debt : Counter) :
    EncControl w ⟨x.ctl, replace x.vm lower span work debt⟩ q := by
  exact ⟨he.ctl, he.chainTag, he.chainPhase, he.chainForward, he.chainBroken,
    he.fppMode, he.fppFinalStage, he.fppPc, he.fppDone, he.dpPc, he.dpDone,
    he.searchMode, he.searchFinalStage, he.searchQuarter, he.periodOnly,
    he.placeGap, he.onLetter, he.leftFirst⟩

/-- The physical representation changes only slots 5--8 and their lower/span
mirrors; all live scan counters remain the same. -/
theorem counterOf_replace (x : State GalilVM) (lower span work debt : Counter) (c : Fin 16) :
    counterOf ⟨x.ctl, replace x.vm lower span work debt⟩ c =
      if c = 5 then some lower else if c = 6 then some span
      else if c = 7 then some work else if c = 8 then some debt else counterOf x c := by
  fin_cases c <;> rfl

/-! ## A storage relation closed under the actual controller

Idle/missed search also leaves the old counters unobserved. Including those
states is essential: fallback drops the chain and stops search before restart
or replay initialization can overwrite the old values.
-/

/-- No search operation may inspect the four counters in this state. -/
def Dormant (s : GalilVM) : Prop :=
  s.chain ≠ .idle ∨ s.search.mode = .idle ∨ s.search.mode = .missed

theorem dormant_replace (s : GalilVM) (lower span work debt : Counter) :
    Dormant (replace s lower span work debt) ↔ Dormant s := Iff.rfl

theorem searchEffect_dormant (P : Shared) (s : GalilVM) (a : Bool)
    (hd : Dormant s) : searchEffectFun P a s = searchLens.get s := by
  cases hc : s.chain with
  | idle =>
    rcases hd with hn | hm | hm
    · exact False.elim (hn hc)
    all_goals simp [searchEffectFun, hc, searchStepFun, searchLens, hm]
  | copy | back | watch | broken => simp only [searchEffectFun, hc]

theorem born_dormant (s : GalilVM) (hd : Dormant s) :
    chainBorn (decide (s.search.mode = .found)) s.chain = false := by
  cases hc : s.chain <;> try rfl
  rcases hd with hn | hm | hm
  · exact False.elim (hn hc)
  all_goals simp [chainBorn, ChainVM.isIdle, hc, hm]

theorem chainAt_dormant (s : GalilVM) (hd : Dormant s) (a : Bool)
    (answer : PalPeg.GalilScaffoldTape.Tape) (c : Fin 3)
    (walker : PalPeg.GalilScaffoldPlace.Place)
    (ver : PalPeg.GalilScaffoldInputHead.PlaceHead) (radius : Counter) :
    chainAtFun a (decide (s.search.mode = .found)) answer c walker ver radius s.chain =
      chainTickFun a s.chain := by
  cases hc : s.chain <;> try rfl
  rcases hd with hn | hm | hm
  · exact False.elim (hn hc)
  all_goals cases a <;> simp [chainAtFun, chainTickFun, chainStepFun, chainMatchedFun, hc, hm]

theorem chainStep_active (chain : ChainVM) (ha : chain ≠ .idle) :
    chainStepFun chain ≠ .idle := by
  cases chain with
  | idle => exact False.elim (ha rfl)
  | broken => simp [chainStepFun]
  | copy t h p v lag margin ver =>
    simp only [chainStepFun]
    split_ifs <;> (try split) <;> simp
  | back => simp only [chainStepFun]; split <;> simp
  | watch =>
    simp only [chainStepFun]
    split <;> try simp
    split <;> simp

theorem chainMatched_active (chain : ChainVM) (ha : chain ≠ .idle) :
    chainMatchedFun chain ≠ .idle := by
  cases chain with
  | idle => exact False.elim (ha rfl)
  | copy | back | broken => simp [chainMatchedFun]
  | watch =>
    simp only [chainMatchedFun]
    split <;> try simp
    split <;> simp

theorem chainTick_active (a : Bool) (chain : ChainVM) (ha : chain ≠ .idle) :
    chainTickFun a chain ≠ .idle := by
  cases a with
  | false => exact chainStep_active chain ha
  | true => exact chainMatched_active _ (chainStep_active chain ha)

/-- Dormant background work has no dependence on the abstract copy oracle. -/
theorem background_dormant (P : Shared) (s : GalilVM) (hd : Dormant s) :
    backgroundFun P s = {s with chain := chainStepFun s.chain} := by
  simp only [backgroundFun, searchEffect_dormant P s false hd,
    searchLens, born_dormant s hd, afterBirth_false]
  rw [chainAt_dormant s hd]
  rfl

theorem background_dormant_replace (P : Shared) (s : GalilVM)
    (lower span work debt : Counter) (hd : Dormant s) :
    backgroundFun P (replace s lower span work debt) =
      replace (backgroundFun P s) lower span work debt := by
  rw [background_dormant P (replace s lower span work debt) hd, background_dormant P s hd]
  rfl

theorem dormant_background (P : Shared) (s : GalilVM) (hd : Dormant s) :
    Dormant (backgroundFun P s) := by
  rw [background_dormant P s hd]
  rcases hd with ha | hm
  · exact Or.inl (chainStep_active _ ha)
  · exact Or.inr hm

/-- Both comparison outcomes retain the same storage freedom. -/
theorem compare_dormant_replace (P : Shared) (s : GalilVM)
    (lower span work debt : Counter) (hd : Dormant s) :
    compareFun P (replace s lower span work debt) =
      replace (compareFun P s) lower span work debt := by
  simp only [compareFun, searchEffect_dormant P s _ hd,
    searchEffect_dormant P (replace s lower span work debt) _ hd, searchLens,
    born_dormant s hd, born_dormant (replace s lower span work debt) hd, afterBirth_false]
  rw [chainAt_dormant s hd, chainAt_dormant (replace s lower span work debt) hd]
  dsimp only [replace]
  split_ifs <;> first | rfl | contradiction

theorem dormant_compare (P : Shared) (s : GalilVM) (hd : Dormant s) :
    Dormant (compareFun P s) := by
  simp only [compareFun, searchEffect_dormant P s _ hd, searchLens,
    born_dormant s hd, afterBirth_false]
  rw [chainAt_dormant s hd]
  split_ifs
  all_goals
    rcases hd with ha | hm
    · exact Or.inl (chainTick_active _ _ ha)
    · exact Or.inr hm

/-- Live search retains literal counter values; suspended search permits
independent storage values while preserving every other VM component. -/
def Related (s t : GalilVM) : Prop := Same s t ∧ (Dormant s ∨ s = t)

theorem related_refl (s : GalilVM) : Related s s := ⟨rfl, Or.inr rfl⟩

theorem related_replace (s : GalilVM) (lower span work debt : Counter) (hd : Dormant s) :
    Related s (replace s lower span work debt) := ⟨rfl, Or.inl hd⟩

theorem related_symm {s t : GalilVM} (h : Related s t) : Related t s := by
  refine ⟨same_symm h.1, ?_⟩
  rcases h.2 with hd | he
  · have hs := h.1
    unfold Same at hs
    rw [hs]
    exact Or.inl hd
  · exact Or.inr he.symm

theorem related_trans {s t u : GalilVM} (h : Related s t) (g : Related t u) :
    Related s u := by
  refine ⟨same_trans h.1 g.1, ?_⟩
  rcases h.2 with hd | he
  · exact Or.inl hd
  · subst t; exact g.2

/-- An equivalent representative has exactly the same externally visible control. -/
def StateRelated (x y : State GalilVM) : Prop := x.ctl = y.ctl ∧ Related x.vm y.vm

theorem stateRelated_refl (x : State GalilVM) : StateRelated x x :=
  ⟨rfl, related_refl _⟩

theorem stateRelated_replace (c : PalPeg.GalilScaffoldController.Control)
    (s : GalilVM) (lower span work debt : Counter) (hd : Dormant s) :
    StateRelated ⟨c, s⟩ ⟨c, replace s lower span work debt⟩ :=
  ⟨rfl, related_replace s lower span work debt hd⟩

theorem dormant_fpp (s : GalilVM) (fpp : FppControl.State) (hd : Dormant s) :
    Dormant (fppLens.set s fpp) := hd

theorem dormant_rewind (s : GalilVM) (v : RewindVM) (hd : Dormant s) :
    Dormant (rewindLens.set s v) := hd

theorem dormant_shift (s : GalilVM) (hd : Dormant s) :
    Dormant (shiftLens.set s (PalPeg.FrameFunction.shiftOneFun (shiftLens.get s))) := by
  cases hc : s.chain with
  | watch wm => exact Or.inl (by simp [shiftLens, PalPeg.FrameFunction.shiftOneFun, hc])
  | idle | copy | back | broken =>
    simpa only [Dormant, shiftLens, PalPeg.FrameFunction.shiftOneFun, hc] using hd

theorem shiftStart_replace (s : GalilVM) (lower span work debt : Counter)
    (hg : shiftGuardVM s) :
    beginShiftFun (replace s lower span work debt) =
      replace (beginShiftFun s) lower span work debt := by
  have hg' : shiftGuardVM (replace s lower span work debt) := hg
  obtain ⟨wm, hw, he⟩ := beginShiftFun_spec s hg
  apply (beginShiftFun_eq hg' _).symm
  refine ⟨wm, hw, ?_⟩
  rw [he]
  rfl

theorem dormant_shiftStart (s : GalilVM) (hg : shiftGuardVM s) :
    Dormant (beginShiftFun s) := by
  obtain ⟨wm, hw, he⟩ := beginShiftFun_spec s hg
  rw [he]
  exact Or.inl (by simp)

/-- The controller's ten modes respect suspended-search storage. Initialization,
replay start and an enabled restart overwrite it; all other steps preserve
its unobservability. No reachability or copy-readiness premise is used. -/
theorem tick_dormant (w : List (Fin 2)) (x : State GalilVM)
    (lower span work debt : Counter) (hd : Dormant x.vm) :
    StateRelated
      (tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
        (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x)
      (tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
        (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048
        ⟨x.ctl, replace x.vm lower span work debt⟩) := by
  cases hm : x.ctl.mode with
  | init | replayStart =>
    simp only [tickFun, hm, PalPeg.FrameFunction.galilFrameFun]
    exact stateRelated_refl _
  | scan =>
    simp only [tickFun, hm, PalPeg.FrameFunction.galilFrameFun]
    have hr : restartGuardTest (replace x.vm lower span work debt) = restartGuardTest x.vm := rfl
    rw [hr]
    by_cases hre : restartGuardTest x.vm = true
    · simp only [hre, if_true]
      rw [restartFun_replace 0 x.vm lower span work debt ((restartGuardTest_iff x.vm).mpr hre)]
      exact stateRelated_refl _
    · simp only [hre, if_false]
      rw [background_dormant_replace _ x.vm lower span work debt hd,
        compare_dormant_replace _ x.vm lower span work debt hd]
      generalize hv : compareFun (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) x.vm = v
      have hdv : Dormant v := hv ▸ dormant_compare _ x.vm hd
      have hb := dormant_background (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) x.vm hd
      have hshift : shiftGuardTest (replace v lower span work debt) = shiftGuardTest v := rfl
      rw [hshift]
      by_cases hs : shiftGuardTest v = true
      · rw [shiftStart_replace v lower span work debt ((shiftGuardTest_iff v).mpr hs)]
        have hds := dormant_shiftStart v ((shiftGuardTest_iff v).mpr hs)
        dsimp only [replace]
        split_ifs <;> first
          | exact ⟨rfl, ⟨rfl, Or.inl hb⟩⟩
          | exact ⟨rfl, ⟨rfl, Or.inl hdv⟩⟩
          | exact ⟨rfl, ⟨rfl, Or.inl hds⟩⟩
          | exact ⟨rfl, ⟨rfl, Or.inl (Or.inr (Or.inl rfl))⟩⟩
          | contradiction
      · dsimp only [replace]
        simp only [hs, if_false]
        split_ifs <;> first
          | exact ⟨rfl, ⟨rfl, Or.inl hb⟩⟩
          | exact ⟨rfl, ⟨rfl, Or.inl hdv⟩⟩
          | exact ⟨rfl, ⟨rfl, Or.inl (Or.inr (Or.inl rfl))⟩⟩
          | contradiction
  | shift =>
    simp only [tickFun, hm, PalPeg.FrameFunction.galilFrameFun]
    dsimp only [replace, shiftLens, fppLens]
    split_ifs <;> first
      | exact ⟨rfl, ⟨rfl, Or.inl (dormant_shift x.vm hd)⟩⟩
      | exact ⟨rfl, ⟨rfl, Or.inl hd⟩⟩
      | contradiction
  | copy | home | fpp | markEnd | choose | rewind =>
    simp only [tickFun, hm, PalPeg.FrameFunction.galilFrameFun]
    dsimp only [replace, shiftLens, fppLens, rewindLens]
    split_ifs <;> first
      | exact ⟨rfl, ⟨rfl, Or.inl hd⟩⟩
      | contradiction

/-- The relation is a congruence of the actual tick function, including guards
and output refresh, rather than just a relation on individual VM operations. -/
theorem related_tick (w : List (Fin 2)) {x y : State GalilVM} (h : StateRelated x y) :
    StateRelated
      (tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
        (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x)
      (tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
        (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 y) := by
  rcases x with ⟨cx, sx⟩
  rcases y with ⟨cy, sy⟩
  change cx = cy ∧ Related sx sy at h
  obtain ⟨rfl, he, hd | rfl⟩ := h
  · change sy = replace sx sy.lower sy.search.span sy.search.work sy.search.debt at he
    rw [he]
    exact tick_dormant w ⟨cx, sx⟩ _ _ _ _ hd
  · exact stateRelated_refl _

theorem dormant_arrive (a : Fin 2) (s : GalilVM) (hd : Dormant s) :
    Dormant (PalPeg.GalilArriveChain.arriveVM' a s) := by
  cases hc : s.chain <;>
    simpa [Dormant, PalPeg.GalilArriveChain.arriveVM', PalPeg.GalilArriveChain.arriveChain,
      PalPeg.LocalTracking.arriveVM, hc] using hd

theorem related_arrive (a : Fin 2) {x y : State GalilVM} (h : StateRelated x y) :
    StateRelated (PalPeg.GalilArriveChain.arriveState' a x)
      (PalPeg.GalilArriveChain.arriveState' a y) := by
  rcases x with ⟨cx, sx⟩
  rcases y with ⟨cy, sy⟩
  change cx = cy ∧ Related sx sy at h
  obtain ⟨rfl, he, hd | rfl⟩ := h
  · change sy = replace sx sy.lower sy.search.span sy.search.work sy.search.debt at he
    rw [he]
    change StateRelated ⟨cx, _⟩ ⟨cx, _⟩
    rw [arrive_replace]
    exact stateRelated_replace cx _ _ _ _ _ (dormant_arrive a sx hd)
  · exact stateRelated_refl _

theorem related_feed (input : Option (Fin 2)) {x y : State GalilVM} (h : StateRelated x y) :
    StateRelated (PalPeg.PhysicalFeed.feedState input x) (PalPeg.PhysicalFeed.feedState input y) := by
  cases input with
  | none => exact h
  | some a => exact related_arrive a h

theorem related_starved {x y : State GalilVM} (h : StateRelated x y) :
    PalPeg.FrameFunction.starvedTest y = PalPeg.FrameFunction.starvedTest x := by
  rcases x with ⟨cx, sx⟩
  rcases y with ⟨cy, sy⟩
  change cx = cy ∧ Related sx sy at h
  obtain ⟨rfl, he, _⟩ := h
  change sy = replace sx sy.lower sy.search.span sy.search.work sy.search.debt at he
  rw [he]
  exact starved_replace ⟨cx, sx⟩ _ _ _ _

/-- Same physical layout and cache, with dormant values supplied by a storage
representative. This is a simulation relation, not a new abstract machine. -/
def Stored (w : List (Fin 2)) (x : State GalilVM) (p : CoreState) : Prop :=
  ∃ y, StateRelated x y ∧ PalPeg.PhysicalCacheInvariant.Running w y p

theorem stored_of_running {w : List (Fin 2)} {x : State GalilVM} {p : CoreState}
    (he : PalPeg.PhysicalCacheInvariant.Running w x p) : Stored w x p :=
  ⟨x, stateRelated_refl x, he⟩

/-- Real input steps preserve the storage relation, including the actual heads,
program banks and boundary cache held in its representative. -/
theorem stored_feed (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (input : Option (Fin 2)) (he : Stored w x p) :
    Stored w (PalPeg.PhysicalFeed.feedState input x)
      (PalPeg.PhysicalBootFeed.feedStep.apply blankM p input) := by
  obtain ⟨y, hr, hy⟩ := he
  exact ⟨_, related_feed input hr, PalPeg.PhysicalCacheInvariant.running_feed w y p input hy⟩

/-- Every strong physical tick proof lifts to the canonical state. The required
source invariant remains a fact about the representative, not an assumed target. -/
theorem stored_tick (w : List (Fin 2)) (x : State GalilVM) (p p' : CoreState)
    (he : Stored w x p)
    (hstep : ∀ y, StateRelated x y → PalPeg.PhysicalCacheInvariant.Running w y p →
      PalPeg.PhysicalCacheInvariant.Running w
        (tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
          (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 y) p') :
    Stored w
      (tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
        (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x) p' := by
  obtain ⟨y, hr, hy⟩ := he
  exact ⟨_, related_tick w hr, hstep y hr hy⟩

/-- The source read which selects restart is already finite and does not depend
on the four dormant counters. -/
theorem restartRead_running (w : List (Fin 2)) (x : State GalilVM)
    (p : CoreState) (he : PalPeg.PhysicalCacheInvariant.Running w x p) :
    restartTest p.1 (fun j => PalPeg.Local.readWin blankM microRadius (p.2 j)) =
      restartGuardTest x.vm := by
  apply PalPeg.PhysicalTickDispatch.read_from_running restartTest
    (fun x => restartGuardTest x.vm) w x p (PalPeg.PhysicalCacheInvariant.running_core he)
  intro T hT
  simpa only [tapesOf, Equiv.apply_symm_apply] using
    restartTest_eq hT.1 (by decide : 1 ≤ microRadius) micro_le_margin

/-- The source-window phase table gives restart priority at any clock. -/
theorem phase_restart (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : PalPeg.PhysicalCacheInvariant.Running w x p) (hg : restartGuardVM x.vm) :
    scanPhase p.1 (fun j => PalPeg.Local.readWin blankM microRadius (p.2 j)) = .restart := by
  rw [scanPhase, restartRead_running w x p he, (restartGuardTest_iff x.vm).mp hg]
  rfl

/-- Existing view commands already keep all four physical cursor banks still
on restart. Only the counter/program part needs a new action row. -/
theorem commands_restart (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : PalPeg.PhysicalCacheInvariant.Running w x p) (hg : restartGuardVM x.vm) :
    scanCommands p.1 (fun j => PalPeg.Local.readWin blankM microRadius (p.2 j)) =
      fun _ => .stay := by
  have hp := phase_restart w x p he hg
  obtain ⟨wm, hw, _, _, _⟩ := hg
  have ht : p.1.chainTag = .broken := by
    obtain ⟨T, hT, _⟩ := PalPeg.PhysicalCacheInvariant.running_core he
    rw [hT.1.1.chainTag, hw]
    rfl
  simp only [scanCommands, hp, reduceCtorEq, if_false, chainConsumesTest, ht,
    decide_false, Bool.false_and, Bool.false_eq_true]
  funext v
  split_ifs <;> rfl

/-- A true restart guard chooses the real tickFun prelude before count or
comparison, for every clock value. -/
theorem tick_restart (w : List (Fin 2)) (x : State GalilVM)
    (hm : x.ctl.mode = .scan) (hg : restartGuardVM x.vm) :
    tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
      (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x =
        ⟨{x.ctl with clock := 2048}, restartFun 0 x.vm⟩ := by
  simp only [tickFun, hm, PalPeg.FrameFunction.galilFrameFun,
    (restartGuardTest_iff x.vm).mp hg, if_true]

/-- Replacing suspended counters changes neither the source guard nor any
component of the actual restart successor. -/
theorem tick_restart_replace (w : List (Fin 2)) (x : State GalilVM)
    (lower span work debt : Counter) (hm : x.ctl.mode = .scan) (hg : restartGuardVM x.vm) :
    tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
      (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048
      ⟨x.ctl, replace x.vm lower span work debt⟩ =
    tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
      (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x := by
  have hr : restartGuardVM (replace x.vm lower span work debt) := by
    obtain ⟨wm, hw, hn, hp, hz⟩ := hg
    exact ⟨wm, hw, hn, hp, hz⟩
  rw [tick_restart w ⟨x.ctl, replace x.vm lower span work debt⟩ hm hr, tick_restart w x hm hg]
  congr 1
  exact restartFun_replace 0 x.vm lower span work debt hg

/-- The finite control part of restart. Copies and the cleared DP bank are
separate tape obligations; no readiness assumption is hidden in this update. -/
def nextControl (q : CoreControl) : CoreControl :=
  {q with ctl := {q.ctl with clock := 2048}, chainTag := .idle, chainPhase := 0, chainForward := false, chainBroken := false, dpPc := some ⟨0, by unfold dpBound; omega⟩, dpDone := true, searchMode := .grow, searchFinalStage := false, searchQuarter := 0, dpLive := !q.dpLive}

theorem control_restart (w : List (Fin 2)) (x : State GalilVM) (q : CoreControl)
    (he : EncControl w x q) (t : GalilVM) (hr : restartVM 0 x.vm t) :
    EncControl w ⟨{x.ctl with clock := 2048}, t⟩ (nextControl q) := by
  obtain ⟨wm, hw, hm, hl, hz, rfl⟩ := hr
  refine {he with ctl := ?_, chainTag := rfl, chainPhase := rfl, chainForward := rfl, chainBroken := rfl, dpPc := rfl, dpDone := rfl, searchMode := rfl, searchFinalStage := rfl, searchQuarter := rfl, placeGap := ?_}
  · rw [← he.ctl]
    rfl
  · intro i place hp
    apply he.placeGap i place
    fin_cases i <;> simpa [placeOf, hw] using hp

theorem boundary_restart (q : CoreControl) (hb : MacroBoundary q) :
    MacroBoundary (nextControl q) := hb

/-- info: 'PalPeg.PhysicalRestartStorage.compare_replace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compare_replace

/-- info: 'PalPeg.PhysicalRestartStorage.tick_restart_replace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tick_restart_replace

/-- info: 'PalPeg.PhysicalRestartStorage.control_restart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms control_restart

/-- info: 'PalPeg.PhysicalRestartStorage.related_tick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms related_tick

/-- info: 'PalPeg.PhysicalRestartStorage.stored_feed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stored_feed

end PalPeg.PhysicalRestartStorage
