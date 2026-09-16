import PalPeg.GalilScaffoldTopProgressS
import PalPeg.GalilScaffoldTopRestart

/-!
# The concrete shared relations of `galilShared` as (partial) functions

`galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs
centre place entry` — the instance used by `cycle_fallback_stepsAll` — carries
three state-to-state relations whose determinism the branch-exhaustiveness
obligation needs (`ASSEMBLY_PLAN.md`, 「分岐網羅の義務」).

* `beginShiftVM'` is existential over the watch state `w`, but `w` is pinned
  by `s.chain = .watch w`, so it is deterministic outright
  (`beginShiftVM'_unique`) and total under `shiftGuardVM` (`beginShift_exists`).
* `beginFallbackVM'` is existential over the right place `p`, and `p` is *not*
  determined by `s`: the relation is genuinely non-functional
  (`beginFallbackVM'_not_unique`). It becomes a function once `p` is supplied,
  e.g. as the shared's own `place` component (`beginFallbackFun`).
* `rs` is an abstract parameter of `galilShared`, not a concrete VM relation;
  the concrete restart used by `restart_tick`/`cycle_found_stepsAll` is
  `restartVM entry`, which is deterministic (pinned by `s.chain = .broken w`)
  and total under the guard `restartGuardVM`.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead

/-! ## `beginShiftVM'` -/

/-- With the period length and the watch state fixed, the shift entry is an
equation, hence deterministic. -/
theorem beginShiftVM_unique (h : ℕ) (w : GalilScaffoldChainWatch.State) {s t₁ t₂ : GalilVM}
    (h₁ : beginShiftVM h w s t₁) (h₂ : beginShiftVM h w s t₂) : t₁ = t₂ := by
  rw [h₁.2, h₂.2]

/-- The watch state existentially quantified in `beginShiftVM'` is pinned by
`s.chain = .watch w`, so the shift entry is deterministic as it stands. -/
theorem beginShiftVM'_unique {s t₁ t₂ : GalilVM}
    (h₁ : beginShiftVM' s t₁) (h₂ : beginShiftVM' s t₂) : t₁ = t₂ := by
  obtain ⟨w₁, hw₁, he₁⟩ := h₁
  obtain ⟨w₂, hw₂, he₂⟩ := h₂
  have hww : ChainVM.watch w₁ = ChainVM.watch w₂ := hw₁.symm.trans hw₂
  injection hww with hw
  subst hw
  rw [he₁, he₂]

/-- Totality of the shift entry under its enabling condition, the concrete
shift guard (restatement of `beginShift_exists`). -/
theorem beginShiftVM'_exists (s : GalilVM) (h : shiftGuardVM s) : ∃ t, beginShiftVM' s t :=
  beginShift_exists s h

/-- The shift entry as a function: the unique successor when the shift guard
holds, the state itself otherwise. -/
noncomputable def beginShiftFun (s : GalilVM) : GalilVM :=
  haveI : Decidable (shiftGuardVM s) := Classical.propDecidable _
  if h : shiftGuardVM s then Classical.choose (beginShiftVM'_exists s h) else s

theorem beginShiftFun_spec (s : GalilVM) (h : shiftGuardVM s) :
    beginShiftVM' s (beginShiftFun s) := by
  have he : beginShiftFun s = Classical.choose (beginShiftVM'_exists s h) := by
    unfold beginShiftFun
    exact dif_pos h
  rw [he]
  exact Classical.choose_spec (beginShiftVM'_exists s h)

/-- `beginShiftFun` computes the shift entry: under the guard, every successor
equals it. -/
theorem beginShiftFun_eq {s t : GalilVM} (hg : shiftGuardVM s) (ht : beginShiftVM' s t) :
    t = beginShiftFun s :=
  beginShiftVM'_unique ht (beginShiftFun_spec s hg)

/-! ## `beginFallbackVM'` -/

/-- The fallback entry with the right place `p` supplied, as a function. -/
def beginFallbackAt (p : GalilScaffoldPlace.Place) (s : GalilVM) : GalilVM :=
  {s with fpp := FppControl.beginFallback s.fpp.program p s.length, chain := .idle, search := {s.search with mode := .idle}}

theorem beginFallbackVM_iff (p : GalilScaffoldPlace.Place) (s t : GalilVM) :
    beginFallbackVM p s t ↔ t = beginFallbackAt p s := Iff.rfl

/-- With the right place fixed, the fallback entry is an equation, hence
deterministic. -/
theorem beginFallbackVM_unique (p : GalilScaffoldPlace.Place) {s t₁ t₂ : GalilVM}
    (h₁ : beginFallbackVM p s t₁) (h₂ : beginFallbackVM p s t₂) : t₁ = t₂ := by
  rw [h₁, h₂]

theorem beginFallbackAt_walker (p : GalilScaffoldPlace.Place) (s : GalilVM) :
    (beginFallbackAt p s).fpp.walker = p := rfl

/-- The place existentially quantified in `beginFallbackVM'` is *not* pinned by
`s`: from any state two different places give two different successors, so
`beginFallbackVM'` is not a function. -/
theorem beginFallbackVM'_not_unique (s : GalilVM) :
    ∃ t₁ t₂ : GalilVM, beginFallbackVM' s t₁ ∧ beginFallbackVM' s t₂ ∧ t₁ ≠ t₂ := by
  refine ⟨beginFallbackAt ⟨[], false⟩ s, beginFallbackAt ⟨[], true⟩ s,
    ⟨⟨[], false⟩, rfl⟩, ⟨⟨[], true⟩, rfl⟩, ?_⟩
  intro hEq
  have h1 : (beginFallbackAt (⟨[], false⟩ : GalilScaffoldPlace.Place) s).fpp.walker
      = (beginFallbackAt (⟨[], true⟩ : GalilScaffoldPlace.Place) s).fpp.walker := by rw [hEq]
  rw [beginFallbackAt_walker, beginFallbackAt_walker] at h1
  exact absurd (congrArg GalilScaffoldPlace.Place.gap h1) (by simp)

/-- Determinism of the fallback entry given the extra hypothesis that pins the
place: any two successors that agree on the copy cursor are equal. -/
theorem beginFallbackVM'_unique_of_walker {s t₁ t₂ : GalilVM}
    (h₁ : beginFallbackVM' s t₁) (h₂ : beginFallbackVM' s t₂)
    (hw : t₁.fpp.walker = t₂.fpp.walker) : t₁ = t₂ := by
  obtain ⟨p₁, he₁⟩ := h₁
  obtain ⟨p₂, he₂⟩ := h₂
  have e₁ : t₁ = beginFallbackAt p₁ s := he₁
  have e₂ : t₂ = beginFallbackAt p₂ s := he₂
  rw [e₁, e₂, beginFallbackAt_walker, beginFallbackAt_walker] at hw
  subst hw
  rw [e₁, e₂]

/-- The determinized fallback entry: the place is read off the state by the
shared's own `place` component. -/
def beginFallbackFun (place : GalilVM → GalilScaffoldPlace.Place) (s : GalilVM) : GalilVM :=
  beginFallbackAt (place s) s

theorem beginFallbackFun_spec (place : GalilVM → GalilScaffoldPlace.Place) (s : GalilVM) :
    beginFallbackVM' s (beginFallbackFun place s) := ⟨place s, rfl⟩

/-- Every successor for the place read off the state equals `beginFallbackFun`;
this is exactly the extra determinism hypothesis needed for
`beginFallbackVM'`. -/
theorem beginFallbackFun_eq (place : GalilVM → GalilScaffoldPlace.Place) {s t : GalilVM}
    (ht : beginFallbackVM (place s) s t) : t = beginFallbackFun place s := by
  unfold beginFallbackFun beginFallbackAt
  exact ht

/-- Under the hypothesis that the fallback entry always uses the state's own
place, `beginFallbackVM'` is deterministic. -/
theorem beginFallbackVM'_unique_of_place (place : GalilVM → GalilScaffoldPlace.Place)
    (hdet : ∀ s t : GalilVM, beginFallbackVM' s t → t.fpp.walker = place s)
    {s t₁ t₂ : GalilVM} (h₁ : beginFallbackVM' s t₁) (h₂ : beginFallbackVM' s t₂) : t₁ = t₂ :=
  beginFallbackVM'_unique_of_walker h₁ h₂ ((hdet s t₁ h₁).trans (hdet s t₂ h₂).symm)

/-! ## `rs` / `restartVM` -/

/-- The enabling condition of the concrete restart: the chain broken with a
non-negative margin, a positive `last` and lag zero. -/
def restartGuardVM (s : GalilVM) : Prop :=
  ∃ w : GalilScaffoldChainWatch.State, s.chain = .broken w ∧
    negative w.margin = false ∧ positive w.machine.control.last = true ∧ zero w.lag = true

/-- The watch state existentially quantified in `restartVM` is pinned by
`s.chain = .broken w`, so the concrete restart is deterministic. -/
theorem restartVM_unique (entry : ℕ) {s t₁ t₂ : GalilVM}
    (h₁ : restartVM entry s t₁) (h₂ : restartVM entry s t₂) : t₁ = t₂ := by
  obtain ⟨w₁, hw₁, _, _, _, he₁⟩ := h₁
  obtain ⟨w₂, hw₂, _, _, _, he₂⟩ := h₂
  have hww : ChainVM.broken w₁ = ChainVM.broken w₂ := hw₁.symm.trans hw₂
  injection hww with hw
  subst hw
  rw [he₁, he₂]

theorem restartVM_exists (entry : ℕ) (s : GalilVM) (h : restartGuardVM s) :
    ∃ t, restartVM entry s t := by
  obtain ⟨w, hw, hm, hl, hz⟩ := h
  exact ⟨_, w, hw, hm, hl, hz, rfl⟩

noncomputable def restartFun (entry : ℕ) (s : GalilVM) : GalilVM :=
  haveI : Decidable (restartGuardVM s) := Classical.propDecidable _
  if h : restartGuardVM s then Classical.choose (restartVM_exists entry s h) else s

theorem restartFun_spec (entry : ℕ) (s : GalilVM) (h : restartGuardVM s) :
    restartVM entry s (restartFun entry s) := by
  have he : restartFun entry s = Classical.choose (restartVM_exists entry s h) := by
    unfold restartFun
    exact dif_pos h
  rw [he]
  exact Classical.choose_spec (restartVM_exists entry s h)

theorem restartFun_eq (entry : ℕ) {s t : GalilVM} (ht : restartVM entry s t) :
    t = restartFun entry s := by
  obtain ⟨w, hw, hm, hl, hz, he⟩ := ht
  exact restartVM_unique entry ⟨w, hw, hm, hl, hz, he⟩
    (restartFun_spec entry s ⟨w, hw, hm, hl, hz⟩)

#print axioms beginShiftVM_unique
#print axioms beginShiftVM'_unique
#print axioms beginShiftVM'_exists
#print axioms beginShiftFun_spec
#print axioms beginShiftFun_eq
#print axioms beginFallbackVM_iff
#print axioms beginFallbackVM_unique
#print axioms beginFallbackAt_walker
#print axioms beginFallbackVM'_not_unique
#print axioms beginFallbackVM'_unique_of_walker
#print axioms beginFallbackFun_spec
#print axioms beginFallbackFun_eq
#print axioms beginFallbackVM'_unique_of_place
#print axioms restartVM_unique
#print axioms restartVM_exists
#print axioms restartFun_spec
#print axioms restartFun_eq

end PalPeg.GalilScaffoldChainInputSupply
