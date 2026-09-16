import PalPeg.GalilLeafQuiet
import PalPeg.GalilWatchOkInst
import PalPeg.GalilOracleMC4
import PalPeg.GalilFinalAssembly2

/-!
# The `hshape` leaf (`GalilWatchOkInst.StartShape`) is **false**

`GalilOracleMC4.h_oracle_of_leaves'''` (and `GalilOracleMC3.h_oracle_of_leaves''`,
`GalilReplaySpan.replay_after_fallback_general''`) ask for

```
∀ w : List (Fin 2), GalilWatchOkInst.StartShape (PofC centreC placeC entry w)
```

with (`PalPeg/GalilWatchOkInst.lean:359`)

```
def StartShape (P : Shared) : Prop :=
  ∀ (s : GalilVM) (a : Bool) (vq : SearchVM), s.chain = .idle →
    SearchReady (searchLens.get s) → searchEffect P a s vq → vq.search.mode = .found →
    ∃ n, 0 < n ∧ AnswerAhead (vq.dp.config.tapes 11) n ∧ PlaceAhead (P.place s) n ∧
      GalilScaffoldChainVerifier.canRight s.center
```

The quantifier `∀ s : GalilVM` is unrestricted and `GalilVM` carries no
well-formedness field, so it ranges over states whose search *already* reads
`.found`.  The offending constructor is again the stutter branch of
`searchStep` (`PalPeg/GalilScaffoldTopSearch.lean:93`),

```
  match v.search.mode with
  | .idle | .found | .missed => v' = v
```

taken through the idle-chain disjunct of `searchEffect`
(`GalilLeafQuiet.searchEffect_found_stutter`).  It delivers `vq = searchLens.get s`
with `vq.dp = s.dp` **completely arbitrary**, while `SearchReady` is vacuous at
`.found` (`GalilLeafQuiet.searchReady_of_found`).  Hence the leaf demands a
`.found`-shaped DP answer tape of *every* VM, which is false.

**Failing conjunct.**  On `GalilLeafQuiet.foundVM` (blank tapes, `zeroPlaceHead`
centre) the conclusion fails in its *second* and *third* conjuncts and holds in
its fourth:

* `AnswerAhead (vq.dp.config.tapes 11) n` — tape 11 is `GalilScaffoldTape.reset
  = ⟨[], 6, []⟩`, and `AnswerAhead` needs `focus = 8` for `n+1` and `focus = 4`
  for `n = 0`; it fails for **every** `n` (`not_answerAhead_reset`), so the
  `0 < n` conjunct is not even the obstruction;
* `PlaceAhead (P.place s) n` — `placeC foundVM = ⟨[], false⟩` (`lettersOf` of a
  `none` focus is `[]`), whose `stream` is `[]`, so `n + 1 ≤ 0` fails for every
  `n` (`not_placeAhead_zeroPlace`);
* `canRight foundVM.center` — **holds**, since `zeroPlaceHead.gap = false` hits
  the first disjunct of `GalilScaffoldChainVerifier.canRight`.  The clause the
  docstring flags as unsupported is therefore *not* what breaks here; the
  breakage is the DP/walker shape, and it is already fatal for `P.place` of any
  shape whatsoever (`not_startShape`, stated for every `Shared`).

As with `hquiet`, the fix is to scope the leaf: the use sites own a *reached*
run-mode search (`found_copy_walk_least`), not an arbitrary `GalilVM`, so the
usable statement must carry the reachability premise that the stutter destroys.
-/

set_option autoImplicit false

namespace PalPeg.GalilLeafStartShape

open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilBranchInvariants
  PalPeg.GalilBranchInvariants2 PalPeg.GalilFinalAssembly2 PalPeg.GalilRunSkeleton
  PalPeg.GalilLeafQuiet
open GalilScaffoldTop
open PalPeg.GalilWatchOkInst (StartShape)

/-! ## The two shape predicates on the witness -/

/-- The blank DP tape carries no `.found` answer, for any `n`. -/
theorem not_answerAhead_reset (n : ℕ) : ¬ AnswerAhead GalilScaffoldTape.reset n := by
  rintro ⟨ls, he⟩
  cases n with
  | zero => exact absurd (List.cons.inj he).1 (by decide)
  | succ m =>
    rw [List.replicate_succ] at he
    exact absurd (List.cons.inj he).1 (by decide)

/-- The centre place read off a `none`-focus head has an empty stream. -/
theorem placeC_foundVM : placeC foundVM = ⟨[], false⟩ := rfl

theorem not_placeAhead_zeroPlace (n : ℕ) :
    ¬ PlaceAhead (⟨[], false⟩ : GalilScaffoldPlace.Place) n := by
  intro h
  have : n + 1 ≤ 0 := h
  omega

/-- The clause the `StartShape` docstring flags as unsupported is the one that
*does* hold on the witness. -/
theorem canRight_foundVM : GalilScaffoldChainVerifier.canRight foundVM.center :=
  Or.inl rfl

/-! ## The refutation -/

/-- **`StartShape` is false for every `P`.**  The DP conjunct alone refutes it,
independently of `P.place`. -/
theorem not_startShape (P : Shared) : ¬ StartShape P := by
  intro h
  obtain ⟨n, -, ha, -, -⟩ :=
    h foundVM false (searchLens.get foundVM) rfl
      (searchReady_of_found (v := searchLens.get foundVM) foundVM_mode)
      (searchEffect_found_stutter P false rfl foundVM_mode) foundVM_mode
  exact not_answerAhead_reset n ha

/-- **The leaf of `h_oracle_of_leaves'''` itself is false.** -/
theorem not_startShape_PofC (entry : ℕ) :
    ¬ (∀ w : List (Fin 2), StartShape (PofC centreC placeC entry w)) :=
  fun h => not_startShape _ (h [])

/-- The walker conjunct fails on the same witness, for the concrete `placeC`. -/
theorem not_startShape_place (P : Shared) (hp : P.place = placeC) : ¬ StartShape P := by
  intro h
  obtain ⟨n, -, -, hw, -⟩ :=
    h foundVM false (searchLens.get foundVM) rfl
      (searchReady_of_found (v := searchLens.get foundVM) foundVM_mode)
      (searchEffect_found_stutter P false rfl foundVM_mode) foundVM_mode
  rw [hp, placeC_foundVM] at hw
  exact not_placeAhead_zeroPlace n hw

end PalPeg.GalilLeafStartShape

#print axioms PalPeg.GalilLeafStartShape.not_answerAhead_reset
#print axioms PalPeg.GalilLeafStartShape.not_placeAhead_zeroPlace
#print axioms PalPeg.GalilLeafStartShape.canRight_foundVM
#print axioms PalPeg.GalilLeafStartShape.not_startShape
#print axioms PalPeg.GalilLeafStartShape.not_startShape_PofC
#print axioms PalPeg.GalilLeafStartShape.not_startShape_place
