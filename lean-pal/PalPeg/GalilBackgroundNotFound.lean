import PalPeg.GalilSegmentConstruct

/-!
# `hbg` is false: a background event can land the search in `found`

`watchSegE_construct` (`PalPeg.GalilSegmentConstruct`) assumes `hbg`: a
background event (`a = false`) never lands the search co-process in
`found`. This module checks that hypothesis against the definitions of
`searchStep`/`searchEffect` (`PalPeg.GalilScaffoldChainInputSupply`,
`PalPeg/GalilScaffoldTopSearch.lean`) and `SafeQuanta`/`advance`
(`PalPeg.GalilScaffoldSearchRun`).

The `.run` mode of `searchStep` runs a fixed schedule of 64 DP calls
(`List.replicate 64 true`, independent of the event `a`) via `SafeCalls`,
landing in some intermediate state `u`, and only then applies
`advance a u`. `advance` only ever touches the `debt` field:

```
def advance (a : Bool) (s : State) : State :=
  if a then {s with debt := GalilScaffoldCounter.dec s.debt} else s
```

so `(advance a u).mode = u.mode` for *every* `a`. The DP quantum that can
land `u.mode = .found` (via `finish`'s `pc = 346` branch, reached inside the
64 calls) never inspects `a`, so if a comparison event (`a = true`) can
drive the search into `found`, the *same* underlying quantum run with
`a = false` (a background tick) lands in `found` too. `hbg` is therefore
false: found is not exclusive to comparisons.

This is not a contradiction in the model — `chainAt`'s third disjunct
(`x = .idle ∧ found = true ∧ (if a then ChainMatched … else z = chainStart …)`)
already handles `a = false` explicitly, and it is exactly what
`backgroundS` wires into its own chain effect. So the design already
anticipated a background-triggered chain start; only the segment
construction's exit set (`SegEnd`) does not yet have a matching
constructor. The fix in `GalilSegmentConstruct` is to add a fourth
`SegEnd` case — say `foundBackground` — for the situation "chain idle,
search effect of the background event `false` is `found`", mirroring the
existing `found` case (which is stated for the comparison event) but
without the `c.clock = 1`/`canRight`/`read … = read …` comparison
hypotheses, since a background tick carries no comparison. Concretely:

```
| foundBackground
    (hq : ∃ vq, searchEffect P false t vq ∧ vq.search.mode = .found)
```

and `idle_background_exists`'s caller (both branches of `watchSegE_construct`
that use `hbg s v hv` to keep discharging `idle_background_exists`) would
instead case on `v.search.mode = .found ∨ v.search.mode ≠ .found`: on
`≠ .found` proceed exactly as today, and on `= .found` stop the recursion
and return `SegEnd.foundBackground ⟨v, hv, hf⟩` together with the state
produced by `backgroundS` itself (whose own `chainAt` clause already starts
the chain there, so the resulting state genuinely has `t.chain ≠ .idle`,
matching the other two `SegEnd` exits which also leave the segment at a
state outside the idle-chain scan loop).
-/

set_option autoImplicit false
namespace PalPeg.GalilBackgroundNotFound

open PalPeg.GalilScaffoldChainInputSupply GalilScaffoldTop GalilScaffoldController
open GalilScaffoldSearchRun

/-- `hbg` is false in general: from a chain-idle, run-mode state whose
comparison event (`a = true`) search effect lands in `found`, the very same
underlying DP quantum reached via the background event (`a = false`) lands
in `found` too. So `searchEffect P false s' v' → v'.search.mode ≠ .found`
cannot hold unconditionally. -/
theorem background_found_starts_chain (P : Shared) {s : GalilVM} {v : SearchVM}
    (hidle : s.chain = ChainVM.idle) (hrun : (searchLens.get s).search.mode = .run)
    (h : searchEffect P true s v) (hf : v.search.mode = .found) :
    ∃ v', searchEffect P false s v' ∧ v'.search.mode = .found := by
  have hstep : searchStep (P.place s) true (searchLens.get s) v := by
    rcases h with ⟨_, hs⟩ | ⟨hne, _⟩
    · exact hs
    · exact absurd hidle hne
  unfold searchStep at hstep
  rw [hrun] at hstep
  obtain ⟨hsq, hlower, hwalker⟩ := hstep
  obtain ⟨u, y', hcalls, hveq, hyeq⟩ := safeQuanta_single hsq
  refine ⟨⟨u, y', v.lower, v.walker⟩, Or.inl ⟨hidle, ?_⟩, ?_⟩
  · show searchStep (P.place s) false (searchLens.get s) ⟨u, y', v.lower, v.walker⟩
    unfold searchStep
    rw [hrun]
    have hadv : advance false u = u := by unfold advance; rfl
    refine ⟨?_, hlower, hwalker⟩
    show SafeQuanta (searchLens.get s).search (searchLens.get s).dp [false] u y'
    rw [← hadv]
    exact SafeQuanta.cons _ u _ (searchLens.get s).dp y' y' false [] hrun hcalls (SafeQuanta.nil _ _)
  · show u.mode = .found
    have hadv : advance true u = v.search := hveq.symm
    have : (advance true u).mode = u.mode := by unfold advance; rfl
    rw [hadv] at this
    exact this ▸ hf

/-- `chainAt`'s background clause: a background event (`a = false`) whose
search effect is `found` on an idle chain starts the chain directly (no
`ChainMatched`, since a background event carries no comparison result to
fold into the answer tape at this tick — Scala's `chain.start()` fires
plainly and the very next comparison drives the fresh chain). This is the
clause `backgroundS` already relies on; `GalilSegmentConstruct.SegEnd`
should gain a matching exit for exactly this case (see the module
docstring above). -/
theorem chainAt_background_found (answer : GalilScaffoldTape.Tape) (c : Fin 3)
    (walker : GalilScaffoldPlace.Place) (ver : GalilScaffoldInputHead.PlaceHead)
    (radius : GalilScaffoldCounter.Counter) (z : ChainVM) :
    chainAt false true answer c walker ver radius ChainVM.idle z ↔
      z = chainStart answer c walker ver radius := by
  unfold chainAt
  simp

end PalPeg.GalilBackgroundNotFound

#print axioms PalPeg.GalilBackgroundNotFound.background_found_starts_chain
#print axioms PalPeg.GalilBackgroundNotFound.chainAt_background_found
